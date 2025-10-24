// policy = l.l_orderkey = o.o_orderkey and o.o_orderstatus = 'O' and l.l_quantity < 3

#include <iostream>
#include <filesystem>
#include <fstream>
#include <string>
#include <vector>
#include <stdexcept>
#include <cstdint>
#include <chrono>
#include <charconv>
#include <cctype>
#include <algorithm>
#include <limits>
#include <unordered_map>
#include <cvc5/cvc5.h>

namespace api = cvc5;
namespace fs  = std::filesystem;

// ============================== schema + npy helpers ==============================

static std::string load_schema(const fs::path& dirpath) {
    const fs::path filepath = dirpath / "schema.json";
    std::ifstream in(filepath, std::ios::in | std::ios::binary);
    if (!in) throw std::runtime_error("Failed to open schema.json at: " + filepath.string());
    in.seekg(0, std::ios::end);
    std::streamoff n = in.tellg();
    if (n < 0) throw std::runtime_error("Failed to stat schema.json");
    in.seekg(0, std::ios::beg);
    std::string s; s.resize(static_cast<size_t>(n));
    if (n > 0) in.read(&s[0], static_cast<std::streamsize>(n));
    return s;
}

static int col_index(const std::string& schema_json, const std::string& name) {
    const std::string key = "\"name\"";
    size_t pos = 0;
    int idx = 0;
    while (true) {
        size_t k = schema_json.find(key, pos);
        if (k == std::string::npos) break;
        size_t colon = schema_json.find(':', k + key.size());
        if (colon == std::string::npos) break;
        size_t q1 = schema_json.find('"', colon + 1);
        if (q1 == std::string::npos) break;
        size_t q2 = schema_json.find('"', q1 + 1);
        if (q2 == std::string::npos) break;
        std::string val = schema_json.substr(q1 + 1, q2 - q1 - 1);
        if (val == name) return idx;
        ++idx;
        pos = q2 + 1;
    }
    throw std::out_of_range("Column name not found in schema: " + name);
}

struct Npy2DInt32 { size_t rows{0}, cols{0}; size_t data_offset{0}; };

static std::string trim(const std::string& s) {
    size_t i = 0, j = s.size();
    while (i < j && std::isspace(static_cast<unsigned char>(s[i]))) ++i;
    while (j > i && std::isspace(static_cast<unsigned char>(s[j-1]))) --j;
    return s.substr(i, j - i);
}

static Npy2DInt32 load_npy_meta_2d_i32(const fs::path& p) {
    std::ifstream in(p, std::ios::in | std::ios::binary);
    if (!in) throw std::runtime_error("Failed to open npy file: " + p.string());
    char magic[6];
    if (!in.read(magic, 6)) throw std::runtime_error("npy: short read (magic)");
    if (!(magic[0] == char(0x93) && magic[1] == 'N' && magic[2] == 'U' && magic[3] == 'M' && magic[4] == 'P' && magic[5] == 'Y'))
        throw std::runtime_error("npy: bad magic header");
    unsigned char ver[2];
    if (!in.read(reinterpret_cast<char*>(ver), 2)) throw std::runtime_error("npy: short read (version)");
    if (!(ver[0] == 1 && ver[1] == 0)) throw std::runtime_error("npy: only v1.0 supported");
    uint16_t header_len = 0;
    if (!in.read(reinterpret_cast<char*>(&header_len), 2)) throw std::runtime_error("npy: short read (hlen)");
    std::string header; header.resize(header_len);
    if (!in.read(&header[0], header_len)) throw std::runtime_error("npy: short read (header)");
    auto find_str = [&](const char* k)->std::string {
        size_t pos = header.find(k);
        if (pos == std::string::npos) throw std::runtime_error(std::string("npy: missing key ") + k);
        size_t colon = header.find(':', pos);
        size_t q1 = header.find('\'', colon + 1);
        size_t q2 = (q1 == std::string::npos) ? q1 : header.find('\'', q1 + 1);
        if (q1 == std::string::npos || q2 == std::string::npos) throw std::runtime_error("npy: bad string");
        return header.substr(q1 + 1, q2 - q1 - 1);
    };
    const std::string descr = find_str("'descr'");
    if (descr != "<i4") throw std::runtime_error("npy: codes must be <i4 (int32)");
    size_t shp = header.find("'shape'");
    if (shp == std::string::npos) throw std::runtime_error("npy: missing shape");
    size_t lp = header.find('(', shp);
    size_t rp = header.find(')', lp);
    if (lp == std::string::npos || rp == std::string::npos || rp <= lp + 1) throw std::runtime_error("npy: bad shape tuple");
    std::string inside = header.substr(lp + 1, rp - lp - 1);
    size_t comma = inside.find(',');
    if (comma == std::string::npos) throw std::runtime_error("npy: shape must be 2D");
    std::string s_rows = trim(inside.substr(0, comma));
    std::string s_cols = trim(inside.substr(comma + 1));
    if (!s_cols.empty() && s_cols.back() == ',') s_cols.pop_back();
    Npy2DInt32 meta;
    meta.rows = static_cast<size_t>(std::stoull(s_rows));
    meta.cols = static_cast<size_t>(std::stoull(s_cols));
    meta.data_offset = 6 + 2 + 2 + header_len;
    return meta;
}

// ----- 1D dict header with numeric + bytes + unicode support -----

struct NpyHeader1D {
    size_t data_offset{0};
    size_t count{0};
    enum class DType { I32, I64, F32, F64, BYTES, UNICODE } dtype{DType::F64};
    size_t itemsize{0}; // for BYTES (|Sx) and UNICODE (<Ux => itemsize = x*4)
};

static NpyHeader1D parse_npy_header_1d(const std::vector<uint8_t>& npy) {
    if (npy.size() < 14) throw std::runtime_error("npy: buffer too small");
    const uint8_t* p = npy.data();
    const char magic[] = {'\x93','N','U','M','P','Y'};
    for (int i = 0; i < 6; ++i) if (p[i] != static_cast<uint8_t>(magic[i])) throw std::runtime_error("npy: bad magic");
    if (!(p[6] == 1 && p[7] == 0)) throw std::runtime_error("npy: only v1.0 supported");
    uint16_t hlen = static_cast<uint16_t>(p[8]) | (static_cast<uint16_t>(p[9]) << 8);
    if (10u + hlen > npy.size()) throw std::runtime_error("npy: bad header length");
    std::string header(reinterpret_cast<const char*>(p + 10), reinterpret_cast<const char*>(p + 10 + hlen));
    auto find_str = [&](const char* k)->std::string {
        size_t pos = header.find(k);
        if (pos == std::string::npos) throw std::runtime_error(std::string("npy: missing key ") + k);
        size_t colon = header.find(':', pos);
        size_t q1 = header.find('\'', colon + 1);
        size_t q2 = (q1 == std::string::npos) ? q1 : header.find('\'', q1 + 1);
        if (q1 == std::string::npos || q2 == std::string::npos) throw std::runtime_error("npy: bad string");
        return header.substr(q1 + 1, q2 - q1 - 1);
    };
    NpyHeader1D h;
    const std::string descr = find_str("'descr'");
    if      (descr == "<i4") { h.dtype = NpyHeader1D::DType::I32; h.itemsize = 4; }
    else if (descr == "<i8") { h.dtype = NpyHeader1D::DType::I64; h.itemsize = 8; }
    else if (descr == "<f4") { h.dtype = NpyHeader1D::DType::F32; h.itemsize = 4; }
    else if (descr == "<f8") { h.dtype = NpyHeader1D::DType::F64; h.itemsize = 8; }
    else if (descr.size() >= 3 && descr[0] == '|' && descr[1] == 'S') {
        h.dtype = NpyHeader1D::DType::BYTES;
        h.itemsize = std::stoull(descr.substr(2));
    }
    else if (descr.size() >= 3 && descr[0] == '<' && descr[1] == 'U') {
        h.dtype = NpyHeader1D::DType::UNICODE;
        h.itemsize = std::stoull(descr.substr(2)) * 4;
    }
    else if (descr.rfind("<M8[", 0) == 0) { h.dtype = NpyHeader1D::DType::I64; h.itemsize = 8; }
    else throw std::runtime_error("npy: unsupported dictionary dtype descr: " + descr);
    size_t shp = header.find("'shape'");
    if (shp == std::string::npos) throw std::runtime_error("npy: missing shape");
    size_t lp = header.find('(', shp);
    size_t rp = header.find(')', lp);
    if (lp == std::string::npos || rp == std::string::npos) throw std::runtime_error("npy: bad shape");
    auto t = [](const std::string& s)->std::string {
        size_t i = 0, j = s.size();
        while (i < j && std::isspace(static_cast<unsigned char>(s[i]))) ++i;
        while (j > i && std::isspace(static_cast<unsigned char>(s[j-1]))) --j;
        return s.substr(i, j - i);
    };
    std::string inside = t(header.substr(lp + 1, rp - lp - 1));
    if (inside.empty()) throw std::runtime_error("npy: bad 1D shape");
    if (inside.back() == ',') inside.pop_back();
    h.count = static_cast<size_t>(std::stoull(inside));
    h.data_offset = 6 + 2 + 2 + hlen;
    return h;
}

// ---------- dict decode for OK/LN (numeric) ----------
static bool dict_decode_i64(const NpyHeader1D& meta,
                            const std::vector<uint8_t>& buf,
                            int32_t code,
                            int64_t& out) {
    if (code < 0) return false;
    const uint32_t idx = static_cast<uint32_t>(code);
    if (idx >= meta.count) return false;
    const uint8_t* p = buf.data() + meta.data_offset;
    switch (meta.dtype) {
        case NpyHeader1D::DType::I32: out = static_cast<int64_t>(reinterpret_cast<const int32_t*>(p)[idx]); return true;
        case NpyHeader1D::DType::I64: out = reinterpret_cast<const int64_t*>(p)[idx]; return true;
        default: return false;
    }
}

static inline bool bytes_eq_char_with_pad(const uint8_t* s, size_t n, char ch) {
    if (n == 0) return false;
    if (s[0] != static_cast<uint8_t>(ch)) return false;
    for (size_t i=1;i<n;++i) if (!(s[i]==0 || s[i]==' ')) return false;
    return true;
}
static inline bool utf32le_eq_char_with_pad(const uint8_t* s, size_t nBytes, char ch) {
    if (nBytes < 4) return false;
    auto cp = [&](int i)->uint32_t {
        return static_cast<uint32_t>(s[i*4+0]) | (static_cast<uint32_t>(s[i*4+1])<<8)
             | (static_cast<uint32_t>(s[i*4+2])<<16) | (static_cast<uint32_t>(s[i*4+3])<<24);
    };
    const size_t N = nBytes/4;
    if (cp(0) != static_cast<uint32_t>(static_cast<unsigned char>(ch))) return false;
    for (size_t i=1;i<N;++i) { uint32_t c = cp(static_cast<int>(i)); if (!(c==0 || c==' ')) return false; }
    return true;
}


int main() {
    const auto t0 = std::chrono::steady_clock::now();

    // --- paths & column names
    const fs::path tables("tables0_1");
    const fs::path lineitem = tables / "lineitem";
    const fs::path orders   = tables / "orders";

    const std::string l_ok = "l_orderkey";
    const std::string l_ln = "l_linenumber";
    const std::string l_qty= "l_quantity";

    const std::string o_ok = "o_orderkey";
    const std::string o_os = "o_orderstatus";

    // --- load schemas / locate columns
    const std::string l_schema = load_schema(lineitem);
    const std::string o_schema = load_schema(orders);

    const int i_l_ok  = col_index(l_schema, l_ok);
    const int i_l_ln  = col_index(l_schema, l_ln);
    const int i_l_qty = col_index(l_schema, l_qty);

    const int i_o_ok = col_index(o_schema, o_ok);
    const int i_o_os = col_index(o_schema, o_os);

    auto load_vals = [](const fs::path& dir, const std::string& col)->std::vector<uint8_t>{
        const fs::path filepath = dir / (col + ".npy");
        std::ifstream in(filepath, std::ios::in | std::ios::binary);
        if (!in) throw std::runtime_error("Failed to open dictionary: " + filepath.string());
        in.seekg(0, std::ios::end);
        std::streamoff n = in.tellg();
        if (n < 0) throw std::runtime_error("Failed to stat dictionary npy: " + filepath.string());
        in.seekg(0, std::ios::beg);
        std::vector<uint8_t> buf; buf.resize(static_cast<size_t>(n));
        if (n > 0) in.read(reinterpret_cast<char*>(buf.data()), n);
        return buf;
    };

    // --- load dictionaries
    const std::vector<uint8_t> l_ok_buf  = load_vals(lineitem, l_ok);
    const std::vector<uint8_t> l_ln_buf  = load_vals(lineitem, l_ln);
    const std::vector<uint8_t> l_qty_buf = load_vals(lineitem, l_qty);

    const std::vector<uint8_t> o_ok_buf  = load_vals(orders, o_ok);
    const std::vector<uint8_t> o_os_buf  = load_vals(orders, o_os);

    const NpyHeader1D l_okDict  = parse_npy_header_1d(l_ok_buf);
    const NpyHeader1D l_lnDict  = parse_npy_header_1d(l_ln_buf);
    const NpyHeader1D l_qtyDict = parse_npy_header_1d(l_qty_buf);

    const NpyHeader1D o_okDict  = parse_npy_header_1d(o_ok_buf);
    const NpyHeader1D o_osDict  = parse_npy_header_1d(o_os_buf);

    // --- build value->code map for orders.o_orderkey
    std::unordered_map<long long, uint32_t> map_o_ok_val_to_code;
    map_o_ok_val_to_code.reserve(o_okDict.count * 2 + 1);
    {
        const uint8_t* p = o_ok_buf.data() + o_okDict.data_offset;
        if (o_okDict.dtype == NpyHeader1D::DType::I32) {
            const int32_t* v = reinterpret_cast<const int32_t*>(p);
            for (uint32_t i = 0; i < o_okDict.count; ++i) map_o_ok_val_to_code[(long long)v[i]] = i;
        } else if (o_okDict.dtype == NpyHeader1D::DType::I64) {
            const int64_t* v = reinterpret_cast<const int64_t*>(p);
            for (uint32_t i = 0; i < o_okDict.count; ++i) map_o_ok_val_to_code[(long long)v[i]] = i;
        } else {
            throw std::runtime_error("o_orderkey must be numeric (<i4 or <i8)");
        }
    }

    // --- load codes, presence, per-row info (lineitem)
    const fs::path l_codes_path = lineitem / "codes.npy";
    const Npy2DInt32 l_codesMeta = load_npy_meta_2d_i32(l_codes_path);
    const size_t LR = l_codesMeta.rows;
    const size_t LC = l_codesMeta.cols;
    const size_t K_L_OK  = (size_t)i_l_ok;
    const size_t K_L_LN  = (size_t)i_l_ln;
    const size_t K_L_QTY = (size_t)i_l_qty;

    std::vector<uint64_t> row_ids;           row_ids.reserve(LR);
    std::vector<int32_t>  l_ok_code;         l_ok_code.reserve(LR);
    std::vector<int32_t>  l_qty_code;        l_qty_code.reserve(LR);
    std::vector<int32_t>  l_ok_pos_in_o;     l_ok_pos_in_o.reserve(LR); // mapped into orders.o_orderkey code idx
    std::vector<uint8_t>  present_l_ok(l_okDict.count, 0);
    std::vector<uint8_t>  present_l_qty(l_qtyDict.count, 0);

    {
        std::ifstream in(l_codes_path, std::ios::in | std::ios::binary);
        if (!in) throw std::runtime_error("Failed to open lineitem codes npy");
        in.seekg((std::streamoff)l_codesMeta.data_offset, std::ios::beg);
        const size_t row_bytes = LC * sizeof(int32_t);
        const size_t blk_rows = std::max<size_t>(1, (size_t)(4 * 1024 * 1024) / row_bytes);
        std::vector<int32_t> blk; blk.resize(blk_rows * LC);

        size_t r = 0;
        while (r < LR) {
            const size_t n = std::min(blk_rows, LR - r);
            const size_t nbytes = n * row_bytes;
            if (!in.read(reinterpret_cast<char*>(blk.data()), (std::streamsize)nbytes))
                throw std::runtime_error("npy: short read (lineitem codes)");
            for (size_t i = 0; i < n; ++i) {
                const size_t base = i * LC;
                const int32_t okc  = blk[base + K_L_OK];
                const int32_t lnc  = blk[base + K_L_LN];
                const int32_t qtyc = blk[base + K_L_QTY];

                int32_t okc_fix = okc;
                if (okc_fix < 0 || (uint32_t)okc_fix >= l_okDict.count) okc_fix = -1;
                int32_t qtyc_fix = qtyc;
                if (qtyc_fix < 0 || (uint32_t)qtyc_fix >= l_qtyDict.count) qtyc_fix = -1;

                const uint64_t rid = (uint64_t)(uint32_t)okc << 32 | (uint64_t)(uint32_t)lnc;
                row_ids.push_back(rid);
                l_ok_code.push_back(okc_fix);
                l_qty_code.push_back(qtyc_fix);
                if (okc_fix >= 0) present_l_ok[(size_t)okc_fix]   = 1;
                if (qtyc_fix >= 0) present_l_qty[(size_t)qtyc_fix] = 1;

                // map l_ok value to orders key code j
                int32_t mapped = -1;
                if (okc_fix >= 0) {
                    int64_t tmp=0;
                    if (dict_decode_i64(l_okDict, l_ok_buf, okc_fix, tmp)) {
                        auto it = map_o_ok_val_to_code.find((long long)tmp);
                        if (it != map_o_ok_val_to_code.end()) mapped = (int32_t)it->second;
                    }
                }
                l_ok_pos_in_o.push_back(mapped);
            }
            r += n;
        }
    }

    //S_status_O and S_ok_has_O
    const fs::path o_codes_path = orders / "codes.npy";
    const Npy2DInt32 o_codesMeta = load_npy_meta_2d_i32(o_codes_path);
    const size_t ORows = o_codesMeta.rows;
    const size_t OC    = o_codesMeta.cols;
    const size_t K_O_OK = (size_t)i_o_ok;
    const size_t K_O_OS = (size_t)i_o_os;

    std::vector<uint8_t> present_o_ok(o_okDict.count, 0);
    std::vector<uint8_t> present_o_os(o_osDict.count, 0);

    // orderstatus == 'O'
    std::vector<uint8_t> S_os_isO(o_osDict.count, 0);
    {
        const uint8_t* p = o_os_buf.data() + o_osDict.data_offset;
        auto ensure = [&](size_t elem) {
            if (o_osDict.data_offset + o_osDict.count * elem > o_os_buf.size())
                throw std::runtime_error("npy: truncated o_orderstatus dictionary payload");
        };
        switch (o_osDict.dtype) {
            case NpyHeader1D::DType::BYTES: {
                ensure(o_osDict.itemsize);
                for (size_t i=0;i<o_osDict.count;++i) {
                    const uint8_t* s = p + i*o_osDict.itemsize;
                    S_os_isO[i] = bytes_eq_char_with_pad(s, o_osDict.itemsize, 'O') ? 1 : 0;
                } break; }
            case NpyHeader1D::DType::UNICODE: {
                ensure(o_osDict.itemsize);
                for (size_t i=0;i<o_osDict.count;++i) {
                    const uint8_t* s = p + i*o_osDict.itemsize;
                    S_os_isO[i] = utf32le_eq_char_with_pad(s, o_osDict.itemsize, 'O') ? 1 : 0;
                } break; }
            case NpyHeader1D::DType::I32: {
                ensure(4); const int32_t* v = reinterpret_cast<const int32_t*>(p);
                for (size_t i=0;i<o_osDict.count;++i) S_os_isO[i] = (v[i] == (int32_t)'O') ? 1 : 0; break; }
            case NpyHeader1D::DType::I64: {
                ensure(8); const int64_t* v = reinterpret_cast<const int64_t*>(p);
                for (size_t i=0;i<o_osDict.count;++i) S_os_isO[i] = (v[i] == (int64_t)'O') ? 1 : 0; break; }
            default: throw std::runtime_error("Unsupported dtype for o_orderstatus");
        }
    }

    // For each orders.o_orderkey code j, tell whether there's an orders row with status 'O'
    std::vector<uint8_t> S_ok_has_O(o_okDict.count, 0);
    {
        std::ifstream in(o_codes_path, std::ios::in | std::ios::binary);
        if (!in) throw std::runtime_error("Failed to open orders codes npy");
        in.seekg((std::streamoff)o_codesMeta.data_offset, std::ios::beg);
        const size_t row_bytes = OC * sizeof(int32_t);
        const size_t blk_rows = std::max<size_t>(1, (size_t)(4 * 1024 * 1024) / row_bytes);
        std::vector<int32_t> blk; blk.resize(blk_rows * OC);

        size_t r = 0;
        while (r < ORows) {
            const size_t n = std::min(blk_rows, ORows - r);
            const size_t nbytes = n * row_bytes;
            if (!in.read(reinterpret_cast<char*>(blk.data()), (std::streamsize)nbytes))
                throw std::runtime_error("npy: short read (orders codes)");
            for (size_t i = 0; i < n; ++i) {
                const size_t base = i * OC;
                int32_t okc = blk[base + K_O_OK];
                int32_t osc = blk[base + K_O_OS];
                if (okc >= 0 && (uint32_t)okc < o_okDict.count) present_o_ok[(size_t)okc] = 1; else okc = -1;
                if (osc >= 0 && (uint32_t)osc < o_osDict.count) present_o_os[(size_t)osc] = 1; else osc = -1;
                if (okc >= 0 && osc >= 0 && S_os_isO[(size_t)osc]) {
                    S_ok_has_O[(size_t)okc] = 1;
                }
            }
            r += n;
        }
    }

    // l_quantity < 3 
    std::vector<uint8_t> S_qty(l_qtyDict.count, 0);
    {
        const uint8_t* p = l_qty_buf.data() + l_qtyDict.data_offset;
        auto ensure = [&](size_t elem) {
            if (l_qtyDict.data_offset + l_qtyDict.count * elem > l_qty_buf.size())
                throw std::runtime_error("npy: truncated l_quantity dictionary payload");
        };
        switch (l_qtyDict.dtype) {
            case NpyHeader1D::DType::I32: { ensure(4); const int32_t* v = reinterpret_cast<const int32_t*>(p);
                for (size_t i=0;i<l_qtyDict.count;++i) S_qty[i] = (v[i] < 3) ? 1 : 0; break; }
            case NpyHeader1D::DType::I64: { ensure(8); const int64_t* v = reinterpret_cast<const int64_t*>(p);
                for (size_t i=0;i<l_qtyDict.count;++i) S_qty[i] = (v[i] < 3) ? 1 : 0; break; }
            case NpyHeader1D::DType::F32: { ensure(4); const float* v = reinterpret_cast<const float*>(p);
                for (size_t i=0;i<l_qtyDict.count;++i) S_qty[i] = (v[i] < 3.0f) ? 1 : 0; break; }
            case NpyHeader1D::DType::F64: { ensure(8); const double* v = reinterpret_cast<const double*>(p);
                for (size_t i=0;i<l_qtyDict.count;++i) S_qty[i] = (v[i] < 3.0) ? 1 : 0; break; }
            default: throw std::runtime_error("Unsupported dtype for l_quantity");
        }
    }


    const auto t_assert_start = std::chrono::steady_clock::now();

    api::TermManager tm;
    api::Solver solver(tm);
    solver.setLogic("QF_UF");
    solver.setOption("incremental", "false");
    solver.setOption("produce-models", "true");
    const api::Sort BOOL = tm.getBooleanSort();

    // presence flags on value domains
    std::vector<api::Term> x_va_l_ok(l_okDict.count), x_va_o_ok(o_okDict.count), x_va_l_qty(l_qtyDict.count);
    for (size_t v = 0; v < l_okDict.count; ++v) {
        x_va_l_ok[v] = tm.mkConst(BOOL, "x_va_l_orderkey_" + std::to_string(v));
        solver.assertFormula((v < present_l_ok.size() && present_l_ok[v]) ? x_va_l_ok[v]
                         : tm.mkTerm(api::Kind::NOT, {x_va_l_ok[v]}));
    }
    for (size_t v = 0; v < o_okDict.count; ++v) {
        x_va_o_ok[v] = tm.mkConst(BOOL, "x_va_o_orderkey_" + std::to_string(v));
        solver.assertFormula((v < present_o_ok.size() && present_o_ok[v]) ? x_va_o_ok[v]
                         : tm.mkTerm(api::Kind::NOT, {x_va_o_ok[v]}));
    }
    for (size_t v = 0; v < l_qtyDict.count; ++v) {
        x_va_l_qty[v] = tm.mkConst(BOOL, "x_va_l_quantity_" + std::to_string(v));
        solver.assertFormula((v < present_l_qty.size() && present_l_qty[v]) ? x_va_l_qty[v]
                         : tm.mkTerm(api::Kind::NOT, {x_va_l_qty[v]}));
    }

    std::vector<api::Term> Q_ok_has_O_term(o_okDict.count);
    for (size_t j = 0; j < o_okDict.count; ++j) {
        Q_ok_has_O_term[j] = tm.mkConst(BOOL, "Q_o_ok_has_status_O_" + std::to_string(j));
        const bool v = S_ok_has_O[j] != 0;
        solver.assertFormula(v ? Q_ok_has_O_term[j]
                               : tm.mkTerm(api::Kind::NOT, {Q_ok_has_O_term[j]}));
    }

    // literal truth over l_quantity values
    std::vector<api::Term> Q_qty(l_qtyDict.count);
    for (size_t v = 0; v < l_qtyDict.count; ++v) {
        Q_qty[v] = tm.mkConst(BOOL, "Q_l_quantity_lt3_" + std::to_string(v));
        solver.assertFormula(S_qty[v] ? Q_qty[v] : tm.mkTerm(api::Kind::NOT, {Q_qty[v]}));
    }

    const size_t R = row_ids.size();
    std::vector<api::Term> X_r(R), pass_rows(R);
    for (size_t r = 0; r < R; ++r) {
        X_r[r] = tm.mkConst(BOOL, "X_row_" + std::to_string(r));
        solver.assertFormula(X_r[r]); // active

        const int32_t lok = l_ok_code[r];
        const int32_t j   = l_ok_pos_in_o[r];
        const int32_t q   = l_qty_code[r];

        api::Term clause = tm.mkBoolean(false);
        if (lok >= 0 && j >= 0 && q >= 0) {
            clause = tm.mkTerm(api::Kind::AND, std::vector<api::Term>{
                X_r[r],
                x_va_l_ok[(size_t)lok], x_va_o_ok[(size_t)j], Q_ok_has_O_term[(size_t)j],
                x_va_l_qty[(size_t)q],  Q_qty[(size_t)q]
            });
        }
        pass_rows[r] = tm.mkConst(BOOL, "pass_row_" + std::to_string(r));
        solver.assertFormula(tm.mkTerm(api::Kind::EQUAL, {pass_rows[r], clause}));
    }

    const auto t_solve_start = std::chrono::steady_clock::now();

    // solve once
    api::Result res = solver.checkSat();

    const auto t_collect_start = std::chrono::steady_clock::now();

    if (!res.isSat()) {
        std::cerr << "UNSAT: writing empty result.\n";
        std::ofstream out("result.txt", std::ios::binary | std::ios::trunc);
        const auto t1 = std::chrono::steady_clock::now();
        std::cout << "Elapsed: " << std::chrono::duration_cast<std::chrono::milliseconds>(t1 - t0).count() << " ms\n";
        return 0;
    }

    // collect passing rows
    std::vector<uint64_t> passed_ids; passed_ids.reserve(R);
    for (size_t r = 0; r < R; ++r) {
        api::Term tv = solver.getValue(pass_rows[r]);
        bool is_true = false;
        if (tv.getKind() == api::Kind::CONST_BOOLEAN) {
            try { is_true = tv.getBooleanValue(); } catch (...) { is_true = false; }
        }
        if (is_true) passed_ids.push_back(row_ids[r]);
    }

    const auto t_write_start = std::chrono::steady_clock::now();

    // write result.txt
    std::ofstream results_out("result.txt", std::ios::binary | std::ios::trunc);
    if (!results_out) throw std::runtime_error("Failed to open result.txt for writing");
    std::string buffer; buffer.reserve(passed_ids.size() * 32);

    for (uint64_t rid : passed_ids) {
        const int32_t ok_code = (int32_t)(rid >> 32);
        const int32_t ln_code = (int32_t)(rid & 0xffffffffu);
        int64_t ok_val = 0, ln_val = 0;
        if (!dict_decode_i64(l_okDict, l_ok_buf, ok_code, ok_val)) continue;
        if (!dict_decode_i64(l_lnDict, l_ln_buf, ln_code, ln_val)) continue;

        char out[64]; char* p = out;
        auto r1 = std::to_chars(p, out + sizeof(out), ok_val);
        if (r1.ec != std::errc()) throw std::runtime_error("serialize ok_val failed");
        p = r1.ptr; *p++ = ',';
        auto r2 = std::to_chars(p, out + sizeof(out), ln_val);
        if (r2.ec != std::errc()) throw std::runtime_error("serialize ln_val failed");
        p = r2.ptr; *p++ = '\n';
        buffer.append(out, (size_t)(p - out));
    }
    results_out.write(buffer.data(), (std::streamsize)buffer.size());
    if (!results_out) throw std::runtime_error("Failed to write result.txt");

    const auto t1 = std::chrono::steady_clock::now();
    std::cout << "Elapsed: " << std::chrono::duration_cast<std::chrono::milliseconds>(t1 - t0).count() << " ms\n";
    std::cout << "Phase(assert): "  << std::chrono::duration_cast<std::chrono::milliseconds>(t_solve_start   - t_assert_start).count()  << " ms\n";
    std::cout << "Phase(solve): "   << std::chrono::duration_cast<std::chrono::milliseconds>(t_collect_start - t_solve_start).count()   << " ms\n";
    std::cout << "Phase(collect): " << std::chrono::duration_cast<std::chrono::milliseconds>(t_write_start   - t_collect_start).count() << " ms\n";
    std::cout << "Phase(write): "   << std::chrono::duration_cast<std::chrono::milliseconds>(t1              - t_write_start).count()   << " ms\n";
}
