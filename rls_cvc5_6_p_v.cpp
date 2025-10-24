// policy = l.l_orderkey = o.o_orderkey and o.o_orderstatus = 'O' and (l.l_quantity < 3 or o.o_orderdate between [2021-01-01 to 2024-12-31])

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
    size_t itemsize{0};
};

static NpyHeader1D parse_npy_header_1d(const std::vector<uint8_t>& npy) {
    if (npy.size() < 14) throw std::runtime_error("npy: buffer too small");
    const uint8_t* p = npy.data();
    const char magic[] = {'\x93','N','U','M','P','Y'};
    for (int i=0;i<6;++i) if (p[i] != (uint8_t)magic[i]) throw std::runtime_error("npy: bad magic");
    if (!(p[6] == 1 && p[7] == 0)) throw std::runtime_error("npy: only v1.0 supported");
    uint16_t hlen = (uint16_t)p[8] | ((uint16_t)p[9] << 8);
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
        h.dtype = NpyHeader1D::DType::BYTES; h.itemsize = std::stoull(descr.substr(2));
    }
    else if (descr.size() >= 3 && descr[0] == '<' && descr[1] == 'U') {
        h.dtype = NpyHeader1D::DType::UNICODE; h.itemsize = std::stoull(descr.substr(2)) * 4;
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
        while (i < j && std::isspace((unsigned char)s[i])) ++i;
        while (j > i && std::isspace((unsigned char)s[j-1])) --j;
        return s.substr(i, j - i);
    };
    std::string inside = t(header.substr(lp + 1, rp - lp - 1));
    if (inside.empty()) throw std::runtime_error("npy: bad 1D shape");
    if (inside.back() == ',') inside.pop_back();
    h.count = (size_t)std::stoull(inside);
    h.data_offset = 6 + 2 + 2 + hlen;
    return h;
}

// ---------- dict decode for OK/LN (numeric) ----------
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

static inline bool bytes_eq_char_with_pad(const uint8_t* s, size_t n, char ch) {
    if (n == 0) return false;
    if (s[0] != (uint8_t)ch) return false;
    for (size_t i=1;i<n;++i) if (!(s[i]==0 || s[i]==' ')) return false;
    return true;
}
static inline bool utf32le_eq_char_with_pad(const uint8_t* s, size_t nBytes, char ch) {
    if (nBytes < 4) return false;
    auto cp = [&](int i)->uint32_t {
        return (uint32_t)s[i*4+0] | ((uint32_t)s[i*4+1]<<8)
             | ((uint32_t)s[i*4+2]<<16) | ((uint32_t)s[i*4+3]<<24);
    };
    const size_t N = nBytes/4;
    if (cp(0) != (uint32_t)(unsigned char)ch) return false;
    for (size_t i=1;i<N;++i) { uint32_t c = cp((int)i); if (!(c==0 || c==' ')) return false; }
    return true;
}

// ============================== date helpers ==============================

static inline int64_t days_from_civil(int y, unsigned m, unsigned d) {
    y -= m <= 2;
    const int era = (y >= 0 ? y : y - 399) / 400;
    const unsigned yoe = (unsigned)(y - era * 400);
    const unsigned doy = (153 * (m + (m > 2 ? -3 : 9)) + 2) / 5 + d - 1;
    const unsigned doe = yoe * 365 + yoe / 4 - yoe / 100 + yoe / 400 + doy;
    return era * 146097 + (int64_t)doe - 719468;
}

struct YMD { int y; int m; int d; };

static inline bool ymd_valid(int y, int m, int d) {
    if (m < 1 || m > 12 || d < 1 || d > 31) return false;
    static const int mdays[] = {31,28,31,30,31,30,31,31,30,31,30,31};
    int maxd = mdays[m-1];
    bool leap = ( (y%4==0 && y%100!=0) || (y%400==0) );
    if (m == 2 && leap) maxd = 29;
    return d <= maxd;
}

static inline bool parse_ymd_ascii(const uint8_t* s, size_t n, YMD& out) {
    auto digit = [](uint8_t c)->bool { return c >= '0' && c <= '9'; };
    if (n >= 10 && digit(s[0])&&digit(s[1])&&digit(s[2])&&digit(s[3]) &&
        ((s[4]=='-' && digit(s[5])&&digit(s[6]) && s[7]=='-' && digit(s[8])&&digit(s[9])) ||
         (digit(s[4])&&digit(s[5])&&digit(s[6])&&digit(s[7])&&digit(s[8])&&digit(s[9])))) {
        int Y,M,D;
        if (s[4]=='-') {
            Y = (s[0]-'0')*1000 + (s[1]-'0')*100 + (s[2]-'0')*10 + (s[3]-'0');
            M = (s[5]-'0')*10 + (s[6]-'0');
            D = (s[8]-'0')*10 + (s[9]-'0');
        } else {
            Y = (s[0]-'0')*1000 + (s[1]-'0')*100 + (s[2]-'0')*10 + (s[3]-'0');
            M = (s[4]-'0')*10 + (s[5]-'0');
            D = (s[6]-'0')*10 + (s[7]-'0');
        }
        if (!ymd_valid(Y,M,D)) return false;
        out = {Y,M,D}; return true;
    }
    return false;
}

static inline bool parse_ymd_utf32le(const uint8_t* s, size_t nBytes, YMD& out) {
    if (nBytes < 8*4) return false;
    auto cp = [&](int i)->uint32_t {
        return (uint32_t)s[i*4+0] | ((uint32_t)s[i*4+1]<<8)
             | ((uint32_t)s[i*4+2]<<16) | ((uint32_t)s[i*4+3]<<24);
    };
    auto isd = [&](uint32_t c)->bool { return c >= '0' && c <= '9'; };
    if (isd(cp(0))&&isd(cp(1))&&isd(cp(2))&&isd(cp(3))) {
        if (cp(4)=='-' && isd(cp(5))&&isd(cp(6)) && cp(7)=='-' && isd(cp(8))&&cp(9)) {
            int Y = (cp(0)-'0')*1000 + (cp(1)-'0')*100 + (cp(2)-'0')*10 + (cp(3)-'0');
            int M = (cp(5)-'0')*10 + (cp(6)-'0');
            int D = (cp(8)-'0')*10 + (cp(9)-'0');
            if (!ymd_valid(Y,M,D)) return false; out={Y,M,D}; return true;
        }
        if (isd(cp(4))&&isd(cp(5))&&isd(cp(6))&&isd(cp(7))&&isd(cp(8))&&isd(cp(9))) {
            int Y = (cp(0)-'0')*1000 + (cp(1)-'0')*100 + (cp(2)-'0')*10 + (cp(3)-'0');
            int M = (cp(4)-'0')*10 + (cp(5)-'0');
            int D = (cp(6)-'0')*10 + (cp(7)-'0');
            if (!ymd_valid(Y,M,D)) return false; out={Y,M,D}; return true;
        }
    }
    return false;
}

enum class DateNumMode { INT_YYYYMMDD, EPOCH_DAYS, EPOCH_SECONDS, EPOCH_MILLIS, EPOCH_MICROS, EPOCH_NANOS, UNKNOWN };

template <typename T>
static DateNumMode detect_date_numeric_mode(const T* v, size_t n) {
    if (n == 0) return DateNumMode::UNKNOWN;
    T mn = std::numeric_limits<T>::max(), mx = std::numeric_limits<T>::min();
    for (size_t i=0;i<n;++i) { if (v[i] < mn) mn = v[i]; if (v[i] > mx) mx = v[i]; }
    if (mn >= 10000101 && mx <= 99991231) return DateNumMode::INT_YYYYMMDD;
    if (mn >= 0 && mx < 400000) return DateNumMode::EPOCH_DAYS;
    if (mn > 100000000 && mx < 10000000000LL) return DateNumMode::EPOCH_SECONDS;
    if (mn > 10000000000LL && mx < 10000000000000LL) return DateNumMode::EPOCH_MILLIS;
    if (mn >= 10000000000000LL && mx < 10000000000000000LL) return DateNumMode::EPOCH_MICROS;
    if (mn >= 10000000000000000LL) return DateNumMode::EPOCH_NANOS;
    return DateNumMode::UNKNOWN;
}


int main() {
    const auto t0 = std::chrono::steady_clock::now();

    // paths & columns
    const fs::path tables("tables0_1");
    const fs::path lineitem = tables / "lineitem";
    const fs::path orders   = tables / "orders";

    const std::string l_ok  = "l_orderkey";
    const std::string l_ln  = "l_linenumber";
    const std::string l_qty = "l_quantity";
    const std::string o_ok  = "o_orderkey";
    const std::string o_os  = "o_orderstatus";
    const std::string o_od  = "o_orderdate";

    const std::string l_schema = load_schema(lineitem);
    const std::string o_schema = load_schema(orders);
    const int i_l_ok  = col_index(l_schema, l_ok);
    const int i_l_ln  = col_index(l_schema, l_ln);
    const int i_l_qty = col_index(l_schema, l_qty);
    const int i_o_ok  = col_index(o_schema, o_ok);
    const int i_o_os  = col_index(o_schema, o_os);
    const int i_o_od  = col_index(o_schema, o_od);

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
    const std::vector<uint8_t> l_qty_buf = load_vals(lineitem, l_qty);
    const std::vector<uint8_t> o_ok_buf  = load_vals(orders, o_ok);
    const std::vector<uint8_t> o_os_buf  = load_vals(orders, o_os);
    const std::vector<uint8_t> o_od_buf  = load_vals(orders, o_od);

    const NpyHeader1D l_okDict  = parse_npy_header_1d(l_ok_buf);
    const NpyHeader1D l_lnDict  = parse_npy_header_1d(l_ln_buf);
    const NpyHeader1D l_qtyDict = parse_npy_header_1d(l_qty_buf);
    const NpyHeader1D o_okDict  = parse_npy_header_1d(o_ok_buf);
    const NpyHeader1D o_osDict  = parse_npy_header_1d(o_os_buf);
    const NpyHeader1D o_odDict  = parse_npy_header_1d(o_od_buf);

    // positional universe I = |orders.o_orderkey|
    const size_t I = o_okDict.count;

    // orders ok value -> position in I
    std::unordered_map<long long, uint32_t> map_o_ok_val_to_code;
    map_o_ok_val_to_code.reserve(o_okDict.count * 2 + 1);
    {
        const uint8_t* p = o_ok_buf.data() + o_okDict.data_offset;
        if (o_okDict.dtype == NpyHeader1D::DType::I32) {
            const int32_t* v = reinterpret_cast<const int32_t*>(p);
            for (uint32_t i=0;i<o_okDict.count;++i) map_o_ok_val_to_code[(long long)v[i]] = i;
        } else if (o_okDict.dtype == NpyHeader1D::DType::I64) {
            const int64_t* v = reinterpret_cast<const int64_t*>(p);
            for (uint32_t i=0;i<o_okDict.count;++i) map_o_ok_val_to_code[(long long)v[i]] = i;
        } else {
            throw std::runtime_error("o_orderkey must be numeric (<i4 or <i8)");
        }
    }

    // Load lineitem codes: row->posI (by l_ok), qty code; presence
    const fs::path l_codes_path = lineitem / "codes.npy";
    const Npy2DInt32 l_codesMeta = load_npy_meta_2d_i32(l_codes_path);
    const size_t LR = l_codesMeta.rows;
    const size_t LC = l_codesMeta.cols;
    const size_t K_L_OK  = (size_t)i_l_ok;
    const size_t K_L_LN  = (size_t)i_l_ln;
    const size_t K_L_QTY = (size_t)i_l_qty;

    std::vector<uint64_t> row_ids;       row_ids.reserve(LR);
    std::vector<int32_t>  posI_for_row;  posI_for_row.reserve(LR);
    std::vector<int32_t>  qty_code;      qty_code.reserve(LR);
    std::vector<uint8_t>  present_pos_l(I, 0);
    std::vector<uint8_t>  present_qty(l_qtyDict.count, 0);

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
            for (size_t i=0;i<n;++i) {
                const size_t base = i * LC;
                const int32_t okc  = blk[base + K_L_OK];
                const int32_t lnc  = blk[base + K_L_LN];
                const int32_t qtyc = blk[base + K_L_QTY];

                int32_t mapped = -1;
                if (okc >= 0 && (uint32_t)okc < l_okDict.count) {
                    int64_t okv = 0;
                    if (dict_decode_i64(l_okDict, l_ok_buf, okc, okv)) {
                        auto it = map_o_ok_val_to_code.find((long long)okv);
                        if (it != map_o_ok_val_to_code.end()) mapped = (int32_t)it->second;
                    }
                }
                const uint64_t rid = (uint64_t)(uint32_t)okc << 32 | (uint64_t)(uint32_t)lnc;
                row_ids.push_back(rid);
                posI_for_row.push_back(mapped);

                int32_t qcode = (qtyc>=0 && (uint32_t)qtyc<l_qtyDict.count)? qtyc : -1;
                qty_code.push_back(qcode);
                if (mapped >= 0 && (size_t)mapped < I) present_pos_l[(size_t)mapped] = 1;
                if (qcode >= 0) present_qty[(size_t)qcode] = 1;
            }
            r += n;
        }
    }

    // Load orders codes: presence over I and positional truths
    const fs::path o_codes_path = orders / "codes.npy";
    const Npy2DInt32 o_codesMeta = load_npy_meta_2d_i32(o_codes_path);
    const size_t ORows = o_codesMeta.rows;
    const size_t OC    = o_codesMeta.cols;
    const size_t K_O_OK = (size_t)i_o_ok;
    const size_t K_O_OS = (size_t)i_o_os;
    const size_t K_O_OD = (size_t)i_o_od;

    std::vector<uint8_t> present_pos_o(I, 0);
    std::vector<uint8_t> Qpos_O(I, 0);            
    std::vector<uint8_t> Qpos_O_and_Date(I, 0);  

    // Precompute per-value truths for status and date
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

    const int YL=2021, ML=1, DL=1;
    const int YU=2024, MU=12, DU=31;
    const int64_t lo_days = days_from_civil(YL,ML,DL);
    const int64_t hi_days = days_from_civil(YU,MU,DU);
    const int lo_yyyymmdd = YL*10000 + ML*100 + DL;
    const int hi_yyyymmdd = YU*10000 + MU*100 + DU;

    std::vector<uint8_t> S_od_inrange(o_odDict.count, 0);
    {
        const uint8_t* p = o_od_buf.data() + o_odDict.data_offset;
        auto ensure = [&](size_t elem) {
            if (o_odDict.data_offset + o_odDict.count * elem > o_od_buf.size())
                throw std::runtime_error("npy: truncated o_orderdate dictionary payload");
        };
        if (o_odDict.dtype == NpyHeader1D::DType::BYTES) {
            ensure(o_odDict.itemsize);
            for (size_t i=0;i<o_odDict.count;++i) {
                const uint8_t* s = p + i*o_odDict.itemsize;
                YMD ymd; bool ok = parse_ymd_ascii(s, o_odDict.itemsize, ymd);
                if (ok) {
                    int64_t d = days_from_civil(ymd.y,ymd.m,ymd.d);
                    S_od_inrange[i] = (d >= lo_days && d <= hi_days) ? 1 : 0;
                } else S_od_inrange[i] = 0;
            }
        } else if (o_odDict.dtype == NpyHeader1D::DType::UNICODE) {
            ensure(o_odDict.itemsize);
            for (size_t i=0;i<o_odDict.count;++i) {
                const uint8_t* s = p + i*o_odDict.itemsize;
                YMD ymd; bool ok = parse_ymd_utf32le(s, o_odDict.itemsize, ymd);
                if (ok) {
                    int64_t d = days_from_civil(ymd.y,ymd.m,ymd.d);
                    S_od_inrange[i] = (d >= lo_days && d <= hi_days) ? 1 : 0;
                } else S_od_inrange[i] = 0;
            }
        } else if (o_odDict.dtype == NpyHeader1D::DType::I32) {
            ensure(4);
            const int32_t* v = reinterpret_cast<const int32_t*>(p);
            DateNumMode mode = detect_date_numeric_mode(v, o_odDict.count);
            for (size_t i=0;i<o_odDict.count;++i) {
                int64_t val = v[i]; bool pass=false;
                switch (mode) {
                    case DateNumMode::INT_YYYYMMDD: pass = (val >= lo_yyyymmdd && val <= hi_yyyymmdd); break;
                    case DateNumMode::EPOCH_DAYS:   pass = (val >= lo_days && val <= hi_days); break;
                    case DateNumMode::EPOCH_SECONDS:pass = (val >= lo_days*86400 && val <= hi_days*86400 + 86399); break;
                    case DateNumMode::EPOCH_MILLIS: pass = (val >= lo_days*86400LL*1000 && val <= (hi_days+1)*86400LL*1000 - 1); break;
                    case DateNumMode::EPOCH_MICROS: pass = (val >= lo_days*86400LL*1000000 && val <= (hi_days+1)*86400LL*1000000 - 1); break;
                    case DateNumMode::EPOCH_NANOS:  pass = (val >= lo_days*86400LL*1000000000 && val <= (hi_days+1)*86400LL*1000000000 - 1); break;
                    default: pass=false;
                }
                S_od_inrange[i] = pass ? 1 : 0;
            }
        } else if (o_odDict.dtype == NpyHeader1D::DType::I64) {
            ensure(8);
            const int64_t* v = reinterpret_cast<const int64_t*>(p);
            DateNumMode mode = detect_date_numeric_mode(v, o_odDict.count);
            for (size_t i=0;i<o_odDict.count;++i) {
                long double val = (long double)v[i]; bool pass=false;
                switch (mode) {
                    case DateNumMode::INT_YYYYMMDD: pass = (v[i] >= lo_yyyymmdd && v[i] <= hi_yyyymmdd); break;
                    case DateNumMode::EPOCH_DAYS:   pass = (v[i] >= lo_days && v[i] <= hi_days); break;
                    case DateNumMode::EPOCH_SECONDS:pass = (val >= (long double)lo_days*86400.0L && val <= ((long double)(hi_days+1)*86400.0L - 1.0L)); break;
                    case DateNumMode::EPOCH_MILLIS: pass = (val >= (long double)lo_days*86400.0L*1000.0L && val <  (long double)(hi_days+1)*86400.0L*1000.0L); break;
                    case DateNumMode::EPOCH_MICROS: pass = (val >= (long double)lo_days*86400.0L*1e6L      && val <  (long double)(hi_days+1)*86400.0L*1e6L); break;
                    case DateNumMode::EPOCH_NANOS:  pass = (val >= (long double)lo_days*86400.0L*1e9L      && val <  (long double)(hi_days+1)*86400.0L*1e9L); break;
                    default: pass=false;
                }
                S_od_inrange[i] = pass ? 1 : 0;
            }
        } else {
            throw std::runtime_error("o_orderdate unsupported dtype");
        }
    }

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
            for (size_t i=0;i<n;++i) {
                const size_t base = i * OC;
                int32_t okc = blk[base + K_O_OK];
                int32_t osc = blk[base + K_O_OS];
                int32_t odc = blk[base + K_O_OD];

                if (okc >= 0 && (uint32_t)okc < o_okDict.count) {
                    present_pos_o[(size_t)okc] = 1;
                    bool isO   = (osc >= 0 && (uint32_t)osc < o_osDict.count && S_os_isO[(size_t)osc]);
                    bool inrng = (odc >= 0 && (uint32_t)odc < o_odDict.count && S_od_inrange[(size_t)odc]);
                    if (isO) Qpos_O[(size_t)okc] = 1;
                    if (isO && inrng) Qpos_O_and_Date[(size_t)okc] = 1;
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

    // Presence over shared positional universe I
    std::vector<api::Term> x_pos_l(I), x_pos_o(I);
    for (size_t i=0;i<I;++i) {
        x_pos_l[i] = tm.mkConst(BOOL, "x_pos_l_orderkey_" + std::to_string(i));
        x_pos_o[i] = tm.mkConst(BOOL, "x_pos_o_orderkey_" + std::to_string(i));
        solver.assertFormula(present_pos_l[i] ? x_pos_l[i] : tm.mkTerm(api::Kind::NOT, {x_pos_l[i]}));
        solver.assertFormula(present_pos_o[i] ? x_pos_o[i] : tm.mkTerm(api::Kind::NOT, {x_pos_o[i]}));
    }

    // Positional truths
    std::vector<api::Term> Qpos_O_term(I), Qpos_O_and_Date_term(I);
    for (size_t i=0;i<I;++i) {
        Qpos_O_term[i] = tm.mkConst(BOOL, "Qpos_status_O_" + std::to_string(i));
        solver.assertFormula(Qpos_O[i] ? Qpos_O_term[i] : tm.mkTerm(api::Kind::NOT, {Qpos_O_term[i]}));
        Qpos_O_and_Date_term[i] = tm.mkConst(BOOL, "Qpos_status_O_and_dateInRange_" + std::to_string(i));
        solver.assertFormula(Qpos_O_and_Date[i] ? Qpos_O_and_Date_term[i]
                                                : tm.mkTerm(api::Kind::NOT, {Qpos_O_and_Date_term[i]}));
    }

    // Value-literals for l_quantity
    std::vector<api::Term> x_va_qty(l_qtyDict.count), Q_qty(l_qtyDict.count);
    for (size_t v=0; v<l_qtyDict.count; ++v) {
        x_va_qty[v] = tm.mkConst(BOOL, "x_va_l_quantity_" + std::to_string(v));
        Q_qty[v]    = tm.mkConst(BOOL, "Q_l_quantity_lt3_" + std::to_string(v));
        solver.assertFormula((v < present_qty.size() && present_qty[v]) ? x_va_qty[v]
                         : tm.mkTerm(api::Kind::NOT, {x_va_qty[v]}));
        solver.assertFormula(S_qty[v] ? Q_qty[v] : tm.mkTerm(api::Kind::NOT, {Q_qty[v]}));
    }

   
    const size_t R = row_ids.size();
    std::vector<api::Term> X_r(R), pass_rows(R);
    for (size_t r=0;r<R;++r) {
        X_r[r] = tm.mkConst(BOOL, "X_row_" + std::to_string(r));
        solver.assertFormula(X_r[r]);

        const int32_t i = posI_for_row[r];
        const int32_t q = qty_code[r];

        api::Term clause = tm.mkBoolean(false);
        if (i >= 0 && (size_t)i < I) {
            api::Term left  = tm.mkBoolean(false);
            if (q >= 0) {
                left = tm.mkTerm(api::Kind::AND, std::vector<api::Term>{
                    Qpos_O_term[(size_t)i],
                    x_va_qty[(size_t)q], Q_qty[(size_t)q]
                });
            }
            api::Term right = Qpos_O_and_Date_term[(size_t)i];
            api::Term disj = tm.mkTerm(api::Kind::OR, std::vector<api::Term>{ left, right });

            clause = tm.mkTerm(api::Kind::AND, std::vector<api::Term>{
                X_r[r], x_pos_l[(size_t)i], x_pos_o[(size_t)i], disj
            });
        }
        pass_rows[r] = tm.mkConst(BOOL, "pass_row_" + std::to_string(r));
        solver.assertFormula(tm.mkTerm(api::Kind::EQUAL, {pass_rows[r], clause}));
    }

    const auto t_solve_start = std::chrono::steady_clock::now();

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
    for (size_t r=0;r<R;++r) {
        api::Term tv = solver.getValue(pass_rows[r]);
        bool is_true=false;
        if (tv.getKind() == api::Kind::CONST_BOOLEAN) {
            try { is_true = tv.getBooleanValue(); } catch (...) { is_true=false; }
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
    std::cout << "Phase(assert): "  << std::chrono::duration_cast<std::chrono::milliseconds>(t_solve_start   - t_assert_start).count()  << " ms\n";
    std::cout << "Phase(solve): "   << std::chrono::duration_cast<std::chrono::milliseconds>(t_collect_start - t_solve_start).count()   << " ms\n";
    std::cout << "Phase(collect): " << std::chrono::duration_cast<std::chrono::milliseconds>(t_write_start   - t_collect_start).count() << " ms\n";
    std::cout << "Phase(write): "   << std::chrono::duration_cast<std::chrono::milliseconds>(t1              - t_write_start).count()   << " ms\n";
}
