// policy = l.l_orderkey = o.o_orderkey and o.o_custkey = c.c_custkey and c.c_mktsegment = 'AUTOMOBILE' and o.o_orderstatus = 'O'


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
    std::string s; s.resize((size_t)n);
    if (n > 0) in.read(&s[0], (std::streamsize)n);
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
    while (i < j && std::isspace((unsigned char)s[i])) ++i;
    while (j > i && std::isspace((unsigned char)s[j-1])) --j;
    return s.substr(i, j - i);
}

static Npy2DInt32 load_npy_meta_2d_i32(const fs::path& p) {
    std::ifstream in(p, std::ios::in | std::ios::binary);
    if (!in) throw std::runtime_error("Failed to open npy file: " + p.string());
    char magic[6];
    if (!in.read(magic, 6)) throw std::runtime_error("npy: short read (magic)");
    if (!(magic[0]==char(0x93)&&magic[1]=='N'&&magic[2]=='U'&&magic[3]=='M'&&magic[4]=='P'&&magic[5]=='Y'))
        throw std::runtime_error("npy: bad magic header");
    unsigned char ver[2];
    if (!in.read(reinterpret_cast<char*>(ver), 2)) throw std::runtime_error("npy: short read (version)");
    if (!(ver[0]==1 && ver[1]==0)) throw std::runtime_error("npy: only v1.0 supported");
    uint16_t header_len = 0;
    if (!in.read(reinterpret_cast<char*>(&header_len), 2)) throw std::runtime_error("npy: short read (hlen)");
    std::string header; header.resize(header_len);
    if (!in.read(&header[0], header_len)) throw std::runtime_error("npy: short read (header)");
    auto find_str = [&](const char* k)->std::string {
        size_t pos = header.find(k);
        if (pos == std::string::npos) throw std::runtime_error(std::string("npy: missing key ")+k);
        size_t colon = header.find(':', pos);
        size_t q1 = header.find('\'', colon + 1);
        size_t q2 = (q1==std::string::npos) ? q1 : header.find('\'', q1+1);
        if (q1==std::string::npos || q2==std::string::npos) throw std::runtime_error("npy: bad string");
        return header.substr(q1+1, q2-q1-1);
    };
    const std::string descr = find_str("'descr'");
    if (descr != "<i4") throw std::runtime_error("npy: codes must be <i4 (int32)");
    size_t shp = header.find("'shape'");
    if (shp == std::string::npos) throw std::runtime_error("npy: missing shape");
    size_t lp = header.find('(', shp);
    size_t rp = header.find(')', lp);
    if (lp==std::string::npos || rp==std::string::npos || rp<=lp+1) throw std::runtime_error("npy: bad shape tuple");
    std::string inside = header.substr(lp+1, rp-lp-1);
    size_t comma = inside.find(',');
    if (comma == std::string::npos) throw std::runtime_error("npy: shape must be 2D");
    std::string s_rows = trim(inside.substr(0, comma));
    std::string s_cols = trim(inside.substr(comma+1));
    if (!s_cols.empty() && s_cols.back() == ',') s_cols.pop_back();
    Npy2DInt32 meta;
    meta.rows = (size_t)std::stoull(s_rows);
    meta.cols = (size_t)std::stoull(s_cols);
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
    for (int i=0;i<6;++i) if (p[i] != (uint8_t)magic[i]) throw std::runtime_error("npy: bad magic");
    if (!(p[6]==1 && p[7]==0)) throw std::runtime_error("npy: only v1.0 supported");
    uint16_t hlen = (uint16_t)p[8] | ((uint16_t)p[9] << 8);
    if (10u + hlen > npy.size()) throw std::runtime_error("npy: bad header length");
    std::string header(reinterpret_cast<const char*>(p + 10), reinterpret_cast<const char*>(p + 10 + hlen));
    auto find_str = [&](const char* k)->std::string {
        size_t pos = header.find(k);
        if (pos == std::string::npos) throw std::runtime_error(std::string("npy: missing key ")+k);
        size_t colon = header.find(':', pos);
        size_t q1 = header.find('\'', colon + 1);
        size_t q2 = (q1==std::string::npos) ? q1 : header.find('\'', q1+1);
        if (q1==std::string::npos || q2==std::string::npos) throw std::runtime_error("npy: bad string");
        return header.substr(q1+1, q2-q1-1);
    };
    NpyHeader1D h;
    const std::string descr = find_str("'descr'");
    if      (descr == "<i4") { h.dtype = NpyHeader1D::DType::I32; h.itemsize = 4; }
    else if (descr == "<i8") { h.dtype = NpyHeader1D::DType::I64; h.itemsize = 8; }
    else if (descr == "<f4") { h.dtype = NpyHeader1D::DType::F32; h.itemsize = 4; }
    else if (descr == "<f8") { h.dtype = NpyHeader1D::DType::F64; h.itemsize = 8; }
    else if (descr.size()>=3 && descr[0]=='|' && descr[1]=='S') { h.dtype = NpyHeader1D::DType::BYTES; h.itemsize = std::stoull(descr.substr(2)); }
    else if (descr.size()>=3 && descr[0]=='<' && descr[1]=='U') { h.dtype = NpyHeader1D::DType::UNICODE; h.itemsize = std::stoull(descr.substr(2))*4; }
    else if (descr.rfind("<M8[", 0) == 0) { h.dtype = NpyHeader1D::DType::I64; h.itemsize = 8; }
    else throw std::runtime_error("npy: unsupported dictionary dtype descr: " + descr);
    size_t shp = header.find("'shape'");
    if (shp == std::string::npos) throw std::runtime_error("npy: missing shape");
    size_t lp = header.find('(', shp);
    size_t rp = header.find(')', lp);
    if (lp==std::string::npos || rp==std::string::npos) throw std::runtime_error("npy: bad shape");
    auto t = [](const std::string& s)->std::string{
        size_t i=0,j=s.size();
        while (i<j && std::isspace((unsigned char)s[i])) ++i;
        while (j>i && std::isspace((unsigned char)s[j-1])) --j;
        return s.substr(i, j-i);
    };
    std::string inside = t(header.substr(lp+1, rp-lp-1));
    if (inside.empty()) throw std::runtime_error("npy: bad 1D shape");
    if (inside.back()==',') inside.pop_back();
    h.count = (size_t)std::stoull(inside);
    h.data_offset = 6 + 2 + 2 + hlen;
    return h;
}

// ---------- dict decode for numeric (OK/LN/keys) ----------
static bool dict_decode_i64(const NpyHeader1D& meta,
                            const std::vector<uint8_t>& buf,
                            int32_t code,
                            int64_t& out) {
    if (code < 0) return false;
    const uint32_t idx = (uint32_t)code;
    if (idx >= meta.count) return false;
    const uint8_t* p = buf.data() + meta.data_offset;
    switch (meta.dtype) {
        case NpyHeader1D::DType::I32: out = (int64_t)reinterpret_cast<const int32_t*>(p)[idx]; return true;
        case NpyHeader1D::DType::I64: out = reinterpret_cast<const int64_t*>(p)[idx]; return true;
        default: return false;
    }
}

static inline bool bytes_eq_str_with_pad(const uint8_t* s, size_t n, const char* target, size_t tlen) {
    if (n < tlen) return false;
    for (size_t i=0;i<tlen;++i) if (s[i] != (uint8_t)target[i]) return false;
    for (size_t i=tlen;i<n;++i) if (!(s[i]==0 || s[i]==' ')) return false;
    return true;
}
static inline bool utf32le_eq_str_with_pad(const uint8_t* s, size_t nBytes, const char* target, size_t tlen) {
    if (nBytes < tlen*4) return false;
    auto cp = [&](int i)->uint32_t {
        return (uint32_t)s[i*4+0] | ((uint32_t)s[i*4+1]<<8)
             | ((uint32_t)s[i*4+2]<<16) | ((uint32_t)s[i*4+3]<<24);
    };
    for (size_t i=0;i<tlen;++i) if (cp((int)i) != (uint32_t)(unsigned char)target[i]) return false;
    const size_t N = nBytes/4;
    for (size_t i=tlen;i<N;++i) { uint32_t c = cp((int)i); if (!(c==0 || c==' ')) return false; }
    return true;
}


int main() {
    const auto t0 = std::chrono::steady_clock::now();

    // tables & columns
    const fs::path tables("tables0_1");
    const fs::path lineitem = tables / "lineitem";
    const fs::path orders   = tables / "orders";
    const fs::path customer = tables / "customer";

    const std::string l_ok  = "l_orderkey";
    const std::string l_ln  = "l_linenumber";
    const std::string o_ok  = "o_orderkey";
    const std::string o_ck  = "o_custkey";
    const std::string o_os  = "o_orderstatus";
    const std::string c_ck  = "c_custkey";
    const std::string c_ms  = "c_mktsegment";

    const std::string l_schema = load_schema(lineitem);
    const std::string o_schema = load_schema(orders);
    const std::string c_schema = load_schema(customer);
    const int i_l_ok  = col_index(l_schema, l_ok);
    const int i_l_ln  = col_index(l_schema, l_ln);
    const int i_o_ok  = col_index(o_schema, o_ok);
    const int i_o_ck  = col_index(o_schema, o_ck);
    const int i_o_os  = col_index(o_schema, o_os);
    const int i_c_ck  = col_index(c_schema, c_ck);
    const int i_c_ms  = col_index(c_schema, c_ms);

    auto load_vals = [](const fs::path& dir, const std::string& col)->std::vector<uint8_t>{
        const fs::path filepath = dir / (col + ".npy");
        std::ifstream in(filepath, std::ios::in | std::ios::binary);
        if (!in) throw std::runtime_error("Failed to open dictionary: " + filepath.string());
        in.seekg(0, std::ios::end);
        std::streamoff n = in.tellg();
        if (n < 0) throw std::runtime_error("Failed to stat dictionary npy: " + filepath.string());
        in.seekg(0, std::ios::beg);
        std::vector<uint8_t> buf; buf.resize((size_t)n);
        if (n > 0) in.read(reinterpret_cast<char*>(buf.data()), n);
        return buf;
    };

    // dicts
    const std::vector<uint8_t> l_ok_buf  = load_vals(lineitem, l_ok);
    const std::vector<uint8_t> l_ln_buf  = load_vals(lineitem, l_ln);
    const std::vector<uint8_t> o_ok_buf  = load_vals(orders, o_ok);
    const std::vector<uint8_t> o_ck_buf  = load_vals(orders, o_ck);
    const std::vector<uint8_t> o_os_buf  = load_vals(orders, o_os);
    const std::vector<uint8_t> c_ck_buf  = load_vals(customer, c_ck);
    const std::vector<uint8_t> c_ms_buf  = load_vals(customer, c_ms);

    const NpyHeader1D l_okDict  = parse_npy_header_1d(l_ok_buf);
    const NpyHeader1D l_lnDict  = parse_npy_header_1d(l_ln_buf);
    const NpyHeader1D o_okDict  = parse_npy_header_1d(o_ok_buf);
    const NpyHeader1D o_ckDict  = parse_npy_header_1d(o_ck_buf);
    const NpyHeader1D o_osDict  = parse_npy_header_1d(o_os_buf);
    const NpyHeader1D c_ckDict  = parse_npy_header_1d(c_ck_buf);
    const NpyHeader1D c_msDict  = parse_npy_header_1d(c_ms_buf);

    // Build value->code maps (orders.ok and customer.ck)
    std::unordered_map<long long, uint32_t> map_o_ok_val_to_code;
    std::unordered_map<long long, uint32_t> map_c_ck_val_to_code;
    {
        const uint8_t* p = o_ok_buf.data() + o_okDict.data_offset;
        if (o_okDict.dtype == NpyHeader1D::DType::I32) {
            const int32_t* v = reinterpret_cast<const int32_t*>(p);
            for (uint32_t i=0;i<o_okDict.count;++i) map_o_ok_val_to_code[(long long)v[i]] = i;
        } else if (o_okDict.dtype == NpyHeader1D::DType::I64) {
            const int64_t* v = reinterpret_cast<const int64_t*>(p);
            for (uint32_t i=0;i<o_okDict.count;++i) map_o_ok_val_to_code[(long long)v[i]] = i;
        } else { throw std::runtime_error("o_orderkey must be numeric"); }
    }
    {
        const uint8_t* p = c_ck_buf.data() + c_ckDict.data_offset;
        if (c_ckDict.dtype == NpyHeader1D::DType::I32) {
            const int32_t* v = reinterpret_cast<const int32_t*>(p);
            for (uint32_t i=0;i<c_ckDict.count;++i) map_c_ck_val_to_code[(long long)v[i]] = i;
        } else if (c_ckDict.dtype == NpyHeader1D::DType::I64) {
            const int64_t* v = reinterpret_cast<const int64_t*>(p);
            for (uint32_t i=0;i<c_ckDict.count;++i) map_c_ck_val_to_code[(long long)v[i]] = i;
        } else { throw std::runtime_error("c_custkey must be numeric"); }
    }

    // Load lineitem codes
    const fs::path l_codes_path = lineitem / "codes.npy";
    const Npy2DInt32 l_codesMeta = load_npy_meta_2d_i32(l_codes_path);
    const size_t LR = l_codesMeta.rows, LC = l_codesMeta.cols;
    const size_t K_L_OK = (size_t)i_l_ok, K_L_LN = (size_t)i_l_ln;

    std::vector<uint64_t> row_ids; row_ids.reserve(LR);
    std::vector<int32_t>  l_ok_code; l_ok_code.reserve(LR);
    std::vector<uint8_t>  present_l_ok(l_okDict.count, 0);

    {
        std::ifstream in(l_codes_path, std::ios::in | std::ios::binary);
        if (!in) throw std::runtime_error("Failed to open lineitem codes npy");
        in.seekg((std::streamoff)l_codesMeta.data_offset, std::ios::beg);
        const size_t row_bytes = LC * sizeof(int32_t);
        const size_t blk_rows = std::max<size_t>(1, (size_t)(4*1024*1024)/row_bytes);
        std::vector<int32_t> blk; blk.resize(blk_rows * LC);
        size_t r=0;
        while (r < LR) {
            const size_t n = std::min(blk_rows, LR - r);
            const size_t nbytes = n * row_bytes;
            if (!in.read(reinterpret_cast<char*>(blk.data()), (std::streamsize)nbytes))
                throw std::runtime_error("npy: short read (lineitem codes)");
            for (size_t i=0;i<n;++i) {
                const size_t base = i * LC;
                const int32_t okc = blk[base + K_L_OK];
                const int32_t lnc = blk[base + K_L_LN];
                int32_t okc_fix = (okc >= 0 && (uint32_t)okc < l_okDict.count) ? okc : -1;
                const uint64_t rid = (uint64_t)(uint32_t)okc << 32 | (uint64_t)(uint32_t)lnc;
                row_ids.push_back(rid);
                l_ok_code.push_back(okc_fix);
                if (okc_fix >= 0) present_l_ok[(size_t)okc_fix] = 1;
            }
            r += n;
        }
    }

    // Build S_seg_isAuto over c_mktsegment values
    std::vector<uint8_t> S_seg_isAuto(c_msDict.count, 0);
    {
        const char* AUTO = "AUTOMOBILE"; const size_t AL = 10;
        const uint8_t* p = c_ms_buf.data() + c_msDict.data_offset;
        auto ensure = [&](size_t elem) {
            if (c_msDict.data_offset + c_msDict.count * elem > c_ms_buf.size())
                throw std::runtime_error("npy: truncated c_mktsegment dictionary payload");
        };
        switch (c_msDict.dtype) {
            case NpyHeader1D::DType::BYTES: {
                ensure(c_msDict.itemsize);
                for (size_t i=0;i<c_msDict.count;++i) {
                    const uint8_t* s = p + i*c_msDict.itemsize;
                    S_seg_isAuto[i] = bytes_eq_str_with_pad(s, c_msDict.itemsize, AUTO, AL) ? 1 : 0;
                } break; }
            case NpyHeader1D::DType::UNICODE: {
                ensure(c_msDict.itemsize);
                for (size_t i=0;i<c_msDict.count;++i) {
                    const uint8_t* s = p + i*c_msDict.itemsize;
                    S_seg_isAuto[i] = utf32le_eq_str_with_pad(s, c_msDict.itemsize, AUTO, AL) ? 1 : 0;
                } break; }
            default: { for (size_t i=0;i<c_msDict.count;++i) S_seg_isAuto[i] = 0; break; }
        }
    }

    // For each c_custkey code k: does that customer have segment 'AUTOMOBILE'?
    std::vector<uint8_t> S_ck_isAuto(c_ckDict.count, 0);
    {
        const fs::path c_codes_path = customer / "codes.npy";
        const Npy2DInt32 c_codesMeta = load_npy_meta_2d_i32(c_codes_path);
        const size_t C = c_codesMeta.cols;
        const size_t K_C_CK = (size_t)i_c_ck;
        const size_t K_C_MS = (size_t)i_c_ms;

        std::ifstream in(c_codes_path, std::ios::in | std::ios::binary);
        if (!in) throw std::runtime_error("Failed to open customer codes npy");
        in.seekg((std::streamoff)c_codesMeta.data_offset, std::ios::beg);
        const size_t row_bytes = C * sizeof(int32_t);
        const size_t blk_rows = std::max<size_t>(1, (size_t)(4*1024*1024)/row_bytes);
        std::vector<int32_t> blk; blk.resize(blk_rows * C);

        size_t r=0;
        while (r < c_codesMeta.rows) {
            const size_t n = std::min(blk_rows, c_codesMeta.rows - r);
            const size_t nbytes = n * row_bytes;
            if (!in.read(reinterpret_cast<char*>(blk.data()), (std::streamsize)nbytes))
                throw std::runtime_error("npy: short read (customer codes)");
            for (size_t i=0;i<n;++i) {
                const size_t base = i * C;
                int32_t ck = blk[base + K_C_CK];
                int32_t ms = blk[base + K_C_MS];
                if (ck >= 0 && (uint32_t)ck < c_ckDict.count) {
                    bool isAuto = (ms >= 0 && (uint32_t)ms < c_msDict.count && S_seg_isAuto[(size_t)ms]);
                    if (isAuto) S_ck_isAuto[(size_t)ck] = 1;
                }
            }
            r += n;
        }
    }

    // Build S_os_isO over orderstatus values
    std::vector<uint8_t> S_os_isO(o_osDict.count, 0);
    {
        const char* OSTR = "O"; const size_t OL = 1;
        const uint8_t* p = o_os_buf.data() + o_osDict.data_offset;
        auto ensure = [&](size_t elem){
            if (o_osDict.data_offset + o_osDict.count * elem > o_os_buf.size())
                throw std::runtime_error("npy: truncated o_orderstatus dictionary payload");
        };
        switch (o_osDict.dtype) {
            case NpyHeader1D::DType::BYTES: {
                ensure(o_osDict.itemsize);
                for (size_t i=0;i<o_osDict.count;++i) {
                    const uint8_t* s = p + i*o_osDict.itemsize;
                    S_os_isO[i] = bytes_eq_str_with_pad(s, o_osDict.itemsize, OSTR, OL) ? 1 : 0;
                } break; }
            case NpyHeader1D::DType::UNICODE: {
                ensure(o_osDict.itemsize);
                for (size_t i=0;i<o_osDict.count;++i) {
                    const uint8_t* s = p + i*o_osDict.itemsize;
                    S_os_isO[i] = utf32le_eq_str_with_pad(s, o_osDict.itemsize, OSTR, OL) ? 1 : 0;
                } break; }
            default: { for (size_t i=0;i<o_osDict.count;++i) S_os_isO[i] = 0; break; }
        }
    }

    // For each o_orderkey value code j: exists orders row with (ck Auto) AND (status 'O') ?
    std::vector<uint8_t> S_ok_pass(o_okDict.count, 0);
    std::vector<uint8_t> present_o_ok(o_okDict.count, 0);
    {
        const fs::path o_codes_path = orders / "codes.npy";
        const Npy2DInt32 o_codesMeta = load_npy_meta_2d_i32(o_codes_path);
        const size_t C = o_codesMeta.cols;
        const size_t K_O_OK = (size_t)i_o_ok;
        const size_t K_O_CK = (size_t)i_o_ck;
        const size_t K_O_OS = (size_t)i_o_os;

        const uint8_t* ockData = o_ck_buf.data() + o_ckDict.data_offset;

        std::ifstream in(o_codes_path, std::ios::in | std::ios::binary);
        if (!in) throw std::runtime_error("Failed to open orders codes npy");
        in.seekg((std::streamoff)o_codesMeta.data_offset, std::ios::beg);
        const size_t row_bytes = C * sizeof(int32_t);
        const size_t blk_rows = std::max<size_t>(1, (size_t)(4*1024*1024)/row_bytes);
        std::vector<int32_t> blk; blk.resize(blk_rows * C);

        size_t r=0;
        while (r < o_codesMeta.rows) {
            const size_t n = std::min(blk_rows, o_codesMeta.rows - r);
            const size_t nbytes = n * row_bytes;
            if (!in.read(reinterpret_cast<char*>(blk.data()), (std::streamsize)nbytes))
                throw std::runtime_error("npy: short read (orders codes)");
            for (size_t i=0;i<n;++i) {
                const size_t base = i * C;
                int32_t okc = blk[base + K_O_OK];
                int32_t ock = blk[base + K_O_CK];
                int32_t oosc= blk[base + K_O_OS];

                if (okc >= 0 && (uint32_t)okc < o_okDict.count) {
                    present_o_ok[(size_t)okc] = 1;

                    bool statusO = (oosc >= 0 && (uint32_t)oosc < o_osDict.count && S_os_isO[(size_t)oosc]);

                    long long ck_val = 0; bool have_val=false;
                    if (ock >= 0 && (uint32_t)ock < o_ckDict.count) {
                        if (o_ckDict.dtype == NpyHeader1D::DType::I32) { ck_val = reinterpret_cast<const int32_t*>(ockData)[(uint32_t)ock]; have_val=true; }
                        else if (o_ckDict.dtype == NpyHeader1D::DType::I64) { ck_val = reinterpret_cast<const int64_t*>(ockData)[(uint32_t)ock]; have_val=true; }
                    }
                    bool custAuto = false;
                    if (have_val) {
                        auto it = map_c_ck_val_to_code.find(ck_val);
                        if (it != map_c_ck_val_to_code.end()) {
                            uint32_t ccode = it->second;
                            if (ccode < S_ck_isAuto.size() && S_ck_isAuto[ccode]) custAuto = true;
                        }
                    }
                    if (statusO && custAuto) S_ok_pass[(size_t)okc] = 1;
                }
            }
            r += n;
        }
    }

    // Map lineitem l_ok value to orders o_ok code j
    std::vector<uint32_t> l_ok_to_o_ok_code; l_ok_to_o_ok_code.reserve(row_ids.size());
    {
        l_ok_to_o_ok_code.resize(l_ok_code.size(), (uint32_t)-1);
        const uint8_t* lokData = l_ok_buf.data() + l_okDict.data_offset;
        for (size_t r=0;r<l_ok_code.size();++r) {
            int32_t lok = l_ok_code[r];
            uint32_t mapped = (uint32_t)-1;
            if (lok >= 0 && (uint32_t)lok < l_okDict.count) {
                long long val = 0; bool have=false;
                if (l_okDict.dtype == NpyHeader1D::DType::I32) { val = reinterpret_cast<const int32_t*>(lokData)[(uint32_t)lok]; have=true; }
                else if (l_okDict.dtype == NpyHeader1D::DType::I64) { val = reinterpret_cast<const int64_t*>(lokData)[(uint32_t)lok]; have=true; }
                if (have) {
                    auto it = map_o_ok_val_to_code.find(val);
                    if (it != map_o_ok_val_to_code.end()) mapped = it->second;
                }
            }
            l_ok_to_o_ok_code[r] = mapped;
        }
    }

    api::TermManager tm;
    api::Solver solver(tm);
    solver.setLogic("QF_UF");
    solver.setOption("incremental", "false");
    solver.setOption("produce-models", "true");
    const api::Sort BOOL = tm.getBooleanSort();

    // presence flags on value domains
    std::vector<api::Term> x_va_l_ok(l_okDict.count), x_va_o_ok(o_okDict.count);
    for (size_t v=0; v<l_okDict.count; ++v) {
        x_va_l_ok[v] = tm.mkConst(BOOL, "x_va_l_orderkey_" + std::to_string(v));
        solver.assertFormula((v < present_l_ok.size() && present_l_ok[v]) ? x_va_l_ok[v]
                         : tm.mkTerm(api::Kind::NOT, {x_va_l_ok[v]}));
    }
    for (size_t v=0; v<o_okDict.count; ++v) {
        x_va_o_ok[v] = tm.mkConst(BOOL, "x_va_o_orderkey_" + std::to_string(v));
        solver.assertFormula((v < present_o_ok.size() && present_o_ok[v]) ? x_va_o_ok[v]
                         : tm.mkTerm(api::Kind::NOT, {x_va_o_ok[v]}));
    }

    // truth table over o_orderkey values: ok_pass[j] = exists orders row with (ck Auto) AND (status O)
    std::vector<api::Term> Q_ok_pass(o_okDict.count);
    for (size_t j=0;j<o_okDict.count;++j) {
        Q_ok_pass[j] = tm.mkConst(BOOL, "Q_ok_pass_" + std::to_string(j));
        solver.assertFormula(S_ok_pass[j] ? Q_ok_pass[j] : tm.mkTerm(api::Kind::NOT, {Q_ok_pass[j]}));
    }

    const size_t R = row_ids.size();
    std::vector<api::Term> X_r(R), pass_rows(R);
    for (size_t r=0;r<R;++r) {
        X_r[r] = tm.mkConst(BOOL, "X_row_" + std::to_string(r));
        solver.assertFormula(X_r[r]);

        const int32_t lok = l_ok_code[r];
        const uint32_t j  = l_ok_to_o_ok_code[r];

        api::Term clause = tm.mkBoolean(false);
        if (lok >= 0 && j != (uint32_t)-1) {
            clause = tm.mkTerm(api::Kind::AND, std::vector<api::Term>{
                X_r[r], x_va_l_ok[(size_t)lok], x_va_o_ok[(size_t)j], Q_ok_pass[(size_t)j]
            });
        }
        pass_rows[r] = tm.mkConst(BOOL, "pass_row_" + std::to_string(r));
        solver.assertFormula(tm.mkTerm(api::Kind::EQUAL, {pass_rows[r], clause}));
    }

    api::Result res = solver.checkSat();
    if (!res.isSat()) {
        std::cerr << "UNSAT: writing empty result.\n";
        std::ofstream out("result.txt", std::ios::binary | std::ios::trunc);
        const auto t1 = std::chrono::steady_clock::now();
        std::cout << "Elapsed: " << std::chrono::duration_cast<std::chrono::milliseconds>(t1 - t0).count() << " ms\n";
        return 0;
    }

    // collect passing rows
    std::vector<uint64_t> passed_ids; passed_ids.reserve(R);
    for (size_t r=0;r<R;++r) {
        api::Term tv = solver.getValue(pass_rows[r]);
        bool is_true=false;
        if (tv.getKind() == api::Kind::CONST_BOOLEAN) {
            try { is_true = tv.getBooleanValue(); } catch (...) { is_true=false; }
        }
        if (is_true) passed_ids.push_back(row_ids[r]);
    }

    // write result.txt
    std::ofstream results_out("result.txt", std::ios::binary | std::ios::trunc);
    if (!results_out) throw std::runtime_error("Failed to open result.txt for writing");
    std::string buffer; buffer.reserve(passed_ids.size() * 32);

    for (uint64_t rid : passed_ids) {
        const int32_t ok_code = (int32_t)(rid >> 32);
        const int32_t ln_code = (int32_t)(rid & 0xffffffffu);
        int64_t ok_val=0, ln_val=0;
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
}


