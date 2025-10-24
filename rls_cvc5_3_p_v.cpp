// policy = l_quantity < 3 and (l_returnflag = 'R' or l_shipdate >= current_date - 3y)


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
#include <ctime>
#include <limits>
#include <cvc5/cvc5.h>

namespace fs  = std::filesystem;
namespace api = cvc5;

// ======= (All helpers identical to value-based file; kept inline for single-file buildability) =======
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
static std::string trim(const std::string& s) {
    size_t i = 0, j = s.size();
    while (i < j && std::isspace(static_cast<unsigned char>(s[i]))) ++i;
    while (j > i && std::isspace(static_cast<unsigned char>(s[j-1]))) --j;
    return s.substr(i, j - i);
}
static int col_index(const std::string& schema_json, const std::string& name) {
    const std::string key = "\"name\"";
    size_t pos = 0; int idx = 0;
    while (true) {
        size_t k = schema_json.find(key, pos);
        if (k == std::string::npos) break;
        size_t colon = schema_json.find(':', k + key.size()); if (colon == std::string::npos) break;
        size_t q1 = schema_json.find('"', colon + 1); if (q1 == std::string::npos) break;
        size_t q2 = schema_json.find('"', q1 + 1); if (q2 == std::string::npos) break;
        std::string val = schema_json.substr(q1 + 1, q2 - q1 - 1);
        if (val == name) return idx;
        ++idx; pos = q2 + 1;
    }
    throw std::out_of_range("Column name not found in schema: " + name);
}
struct Npy2DInt32 { size_t rows{0}, cols{0}; size_t data_offset{0}; };
static Npy2DInt32 load_npy_meta_2d_i32(const fs::path& p) {
    std::ifstream in(p, std::ios::in | std::ios::binary);
    if (!in) throw std::runtime_error("Failed to open npy file: " + p.string());
    char magic[6];
    if (!in.read(magic, 6)) throw std::runtime_error("npy: short read (magic)");
    if (!(magic[0] == char(0x93) && magic[1]=='N' && magic[2]=='U' && magic[3]=='M' && magic[4]=='P' && magic[5]=='Y'))
        throw std::runtime_error("npy: bad magic header");
    unsigned char ver[2];
    if (!in.read(reinterpret_cast<char*>(ver), 2)) throw std::runtime_error("npy: short read (version)");
    if (!(ver[0] == 1 && ver[1] == 0)) throw std::runtime_error("npy: only v1.0 supported");
    uint16_t header_len = 0;
    if (!in.read(reinterpret_cast<char*>(&header_len), 2)) throw std::runtime_error("npy: short read (hlen)");
    std::string header; header.resize(header_len);
    if (!in.read(&header[0], header_len)) throw std::runtime_error("npy: short read (header)");

    auto find_str = [&](const char* k)->std::string {
        size_t pos = header.find(k); if (pos == std::string::npos) throw std::runtime_error(std::string("npy: missing key ")+k);
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
    size_t lp = header.find('(', shp), rp = header.find(')', lp);
    if (lp == std::string::npos || rp == std::string::npos || rp <= lp + 1) throw std::runtime_error("npy: bad shape tuple");

    auto t = [](const std::string& s)->std::string {
        size_t i=0,j=s.size(); while(i<j && std::isspace(static_cast<unsigned char>(s[i]))) ++i;
        while(j>i && std::isspace(static_cast<unsigned char>(s[j-1]))) --j; return s.substr(i, j-i);
    };
    std::string inside = t(header.substr(lp + 1, rp - lp - 1));
    size_t comma = inside.find(','); if (comma == std::string::npos) throw std::runtime_error("npy: shape must be 2D");
    std::string s_rows = trim(inside.substr(0, comma));
    std::string s_cols = trim(inside.substr(comma + 1)); if (!s_cols.empty() && s_cols.back() == ',') s_cols.pop_back();

    Npy2DInt32 meta;
    meta.rows = static_cast<size_t>(std::stoull(s_rows));
    meta.cols = static_cast<size_t>(std::stoull(s_cols));
    meta.data_offset = 6 + 2 + 2 + header_len;
    return meta;
}
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
    for (int i = 0; i < 6; ++i) if (p[i] != static_cast<uint8_t>(magic[i])) throw std::runtime_error("npy: bad magic");
    if (!(p[6] == 1 && p[7] == 0)) throw std::runtime_error("npy: only v1.0 supported");
    uint16_t hlen = static_cast<uint16_t>(p[8]) | (static_cast<uint16_t>(p[9]) << 8);
    if (10u + hlen > npy.size()) throw std::runtime_error("npy: bad header length");
    std::string header(reinterpret_cast<const char*>(p + 10), reinterpret_cast<const char*>(p + 10 + hlen));
    auto find_str = [&](const char* k)->std::string {
        size_t pos = header.find(k); if (pos == std::string::npos) throw std::runtime_error(std::string("npy: missing key ")+k);
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
    else if (descr.rfind("<M8[", 0) == 0) {
        h.dtype = NpyHeader1D::DType::I64;
        h.itemsize = 8;
    }
    else throw std::runtime_error("npy: unsupported dictionary dtype descr: " + descr);
    size_t shp = header.find("'shape'"); if (shp == std::string::npos) throw std::runtime_error("npy: missing shape");
    size_t lp = header.find('(', shp), rp = header.find(')', lp); if (lp == std::string::npos || rp == std::string::npos) throw std::runtime_error("npy: bad shape");
    auto t = [](const std::string& s)->std::string { size_t i=0,j=s.size(); while(i<j&&std::isspace((unsigned char)s[i]))++i; while(j>i&&std::isspace((unsigned char)s[j-1]))--j; return s.substr(i,j-i); };
    std::string inside = t(header.substr(lp + 1, rp - lp - 1)); if (inside.empty()) throw std::runtime_error("npy: bad 1D shape");
    if (inside.back() == ',') inside.pop_back();
    h.count = static_cast<size_t>(std::stoull(inside));
    h.data_offset = 6 + 2 + 2 + hlen;
    return h;
}
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
static inline int64_t days_from_civil(int y, unsigned m, unsigned d) {
    y -= m <= 2;
    const int era = (y >= 0 ? y : y - 399) / 400;
    const unsigned yoe = static_cast<unsigned>(y - era * 400);
    const unsigned doy = (153 * (m + (m > 2 ? -3 : 9)) + 2) / 5 + d - 1;
    const unsigned doe = yoe * 365 + yoe / 4 + yoe / 400 - yoe / 100 + doy;
    return era * 146097 + static_cast<int64_t>(doe) - 719468;
}
struct YMD { int y; int m; int d; };
static inline bool ymd_valid(int y, int m, int d) {
    if (m < 1 || m > 12 || d < 1 || d > 31) return false;
    static const int mdays[] = {31,28,31,30,31,30,31,31,30,31,30,31};
    int maxd = mdays[m-1];
    bool leap = ((y%4==0 && y%100!=0) || (y%400==0));
    if (m == 2 && leap) maxd = 29;
    return d <= maxd;
}
static inline bool parse_ymd_ascii(const uint8_t* s, size_t n, YMD& out) {
    auto digit = [](uint8_t c)->bool { return c >= '0' && c <= '9'; };
    if (n >= 10 && digit(s[0])&&digit(s[1])&&digit(s[2])&&digit(s[3]) &&
        ((s[4]=='-' && digit(s[5])&&digit(s[6]) && s[7]=='-' && digit(s[8])&&digit(s[9])) ||
         (digit(s[4])&&digit(s[5])&&digit(s[6])&&digit(s[7])&&digit(s[8])&&digit(s[9])))) {
        int Y,M,D;
        if (s[4]=='-') { Y=(s[0]-'0')*1000+(s[1]-'0')*100+(s[2]-'0')*10+(s[3]-'0'); M=(s[5]-'0')*10+(s[6]-'0'); D=(s[8]-'0')*10+(s[9]-'0'); }
        else           { Y=(s[0]-'0')*1000+(s[1]-'0')*100+(s[2]-'0')*10+(s[3]-'0'); M=(s[4]-'0')*10+(s[5]-'0'); D=(s[6]-'0')*10+(s[7]-'0'); }
        if (!ymd_valid(Y,M,D)) return false; out={Y,M,D}; return true;
    }
    return false;
}
static inline bool parse_ymd_utf32le(const uint8_t* s, size_t nBytes, YMD& out) {
    if (nBytes < 8*4) return false;
    auto cp = [&](int i)->uint32_t {
        return static_cast<uint32_t>(s[i*4+0]) | (static_cast<uint32_t>(s[i*4+1])<<8)
             | (static_cast<uint32_t>(s[i*4+2])<<16) | (static_cast<uint32_t>(s[i*4+3])<<24);
    };
    auto isd = [&](uint32_t c)->bool { return c >= '0' && c <= '9'; };
    if (isd(cp(0))&&isd(cp(1))&&isd(cp(2))&&isd(cp(3))) {
        if (cp(4)=='-' && isd(cp(5))&&isd(cp(6)) && cp(7)=='-' && isd(cp(8))&&isd(cp(9))) {
            int Y=(cp(0)-'0')*1000+(cp(1)-'0')*100+(cp(2)-'0')*10+(cp(3)-'0');
            int M=(cp(5)-'0')*10+(cp(6)-'0'); int D=(cp(8)-'0')*10+(cp(9)-'0');
            if (!ymd_valid(Y,M,D)) return false; out={Y,M,D}; return true;
        }
        if (isd(cp(4))&&isd(cp(5))&&isd(cp(6))&&isd(cp(7))&&isd(cp(8))&&isd(cp(9))) {
            int Y=(cp(0)-'0')*1000+(cp(1)-'0')*100+(cp(2)-'0')*10+(cp(3)-'0');
            int M=(cp(4)-'0')*10+(cp(5)-'0'); int D=(cp(6)-'0')*10+(cp(7)-'0');
            if (!ymd_valid(Y,M,D)) return false; out={Y,M,D}; return true;
        }
    }
    return false;
}
enum class SdNumMode { INT_YYYYMMDD, EPOCH_DAYS, EPOCH_SECONDS, EPOCH_MILLIS, EPOCH_MICROS, EPOCH_NANOS, UNKNOWN };
template <typename T>
static SdNumMode detect_sd_numeric_mode(const T* v, size_t n) {
    if (n == 0) return SdNumMode::UNKNOWN;
    T mn = std::numeric_limits<T>::max(), mx = std::numeric_limits<T>::min();
    for (size_t i=0;i<n;++i) { if (v[i] < mn) mn = v[i]; if (v[i] > mx) mx = v[i]; }
    if (mn >= 10000101 && mx <= 99991231) return SdNumMode::INT_YYYYMMDD;
    if (mn >= 0 && mx < 400000) return SdNumMode::EPOCH_DAYS;
    if (mn > 100000000 && mx < 10000000000LL) return SdNumMode::EPOCH_SECONDS;
    if (mn > 10000000000LL && mx < 10000000000000LL) return SdNumMode::EPOCH_MILLIS;
    if (mn >= 10000000000000LL && mx < 10000000000000000LL) return SdNumMode::EPOCH_MICROS;
    if (mn >= 10000000000000000LL) return SdNumMode::EPOCH_NANOS;
    return SdNumMode::UNKNOWN;
}
static bool dict_decode_i64_ok(const NpyHeader1D& meta,
                               const std::vector<uint8_t>& buf,
                               int32_t code,
                               int64_t& out) { return dict_decode_i64(meta, buf, code, out); }
static bool dict_decode_i64_ln(const NpyHeader1D& meta,
                               const std::vector<uint8_t>& buf,
                               int32_t code,
                               int64_t& out) { return dict_decode_i64(meta, buf, code, out); }


int main() {
    const auto T0 = std::chrono::steady_clock::now();

    std::time_t now_t = std::time(nullptr) + 19800; // IST
    std::tm gm = *std::gmtime(&now_t);
    int cutoffY = gm.tm_year + 1900 - 3;
    int cutoffM = gm.tm_mon + 1;
    int cutoffD = gm.tm_mday;
    if (!ymd_valid(cutoffY, cutoffM, cutoffD)) {
        if (cutoffM == 2 && cutoffD == 29) cutoffD = 28;
        else { while (!ymd_valid(cutoffY,cutoffM,cutoffD)) --cutoffD; }
    }
    const int64_t cutoff_days     = days_from_civil(cutoffY, cutoffM, cutoffD);
    const int     cutoff_yyyymmdd = cutoffY*10000 + cutoffM*100 + cutoffD;

    const fs::path tables   = fs::path("tables0_1");
    const fs::path lineitem = tables / "lineitem";

    const std::string l_ok  = "l_orderkey";
    const std::string l_ln  = "l_linenumber";
    const std::string l_qty = "l_quantity";
    const std::string l_rf  = "l_returnflag";
    const std::string l_sd  = "l_shipdate";

    const std::string schema = load_schema(lineitem);
    const int i_l_ok  = col_index(schema, l_ok);
    const int i_l_ln  = col_index(schema, l_ln);
    const int i_l_qty = col_index(schema, l_qty);
    const int i_l_rf  = col_index(schema, l_rf);
    const int i_l_sd  = col_index(schema, l_sd);

    auto load_vals = [&](const std::string& col)->std::vector<uint8_t>{
        const fs::path filepath = lineitem / (col + ".npy");
        std::ifstream in(filepath, std::ios::in | std::ios::binary);
        if (!in) throw std::runtime_error("Failed to open dictionary: " + filepath.string());
        in.seekg(0, std::ios::end); std::streamoff n = in.tellg(); in.seekg(0, std::ios::beg);
        std::vector<uint8_t> buf; buf.resize(static_cast<size_t>(n));
        if (n > 0) in.read(reinterpret_cast<char*>(buf.data()), n);
        return buf;
    };

    const std::vector<uint8_t> ok_buf  = load_vals(l_ok);
    const std::vector<uint8_t> ln_buf  = load_vals(l_ln);
    const std::vector<uint8_t> qty_buf = load_vals(l_qty);
    const std::vector<uint8_t> rf_buf  = load_vals(l_rf);
    const std::vector<uint8_t> sd_buf  = load_vals(l_sd);

    const NpyHeader1D okDict  = parse_npy_header_1d(ok_buf);
    const NpyHeader1D lnDict  = parse_npy_header_1d(ln_buf);
    const NpyHeader1D qtyDict = parse_npy_header_1d(qty_buf);
    const NpyHeader1D rfDict  = parse_npy_header_1d(rf_buf);
    const NpyHeader1D sdDict  = parse_npy_header_1d(sd_buf);

    // Load codes into memory (global)
    const fs::path codes_path = lineitem / "codes.npy";
    const Npy2DInt32 codesMeta = load_npy_meta_2d_i32(codes_path);
    const size_t R = codesMeta.rows, C = codesMeta.cols;
    const size_t K_OK  = static_cast<size_t>(i_l_ok);
    const size_t K_LN  = static_cast<size_t>(i_l_ln);
    const size_t K_QTY = static_cast<size_t>(i_l_qty);
    const size_t K_RF  = static_cast<size_t>(i_l_rf);
    const size_t K_SD  = static_cast<size_t>(i_l_sd);

    std::vector<uint64_t> row_ids; row_ids.reserve(R);
    std::vector<int32_t>  code_qty; code_qty.reserve(R);
    std::vector<int32_t>  code_rf;  code_rf.reserve(R);
    std::vector<int32_t>  code_sd;  code_sd.reserve(R);

    {
        std::ifstream in(codes_path, std::ios::in | std::ios::binary);
        if (!in) throw std::runtime_error("Failed to open codes npy");
        in.seekg(static_cast<std::streamoff>(codesMeta.data_offset), std::ios::beg);
        const size_t row_bytes = C * sizeof(int32_t);
        const size_t blk_rows = std::max<size_t>(1, (size_t)(4 * 1024 * 1024) / row_bytes);
        std::vector<int32_t> blk; blk.resize(blk_rows * C);

        size_t r = 0;
        while (r < R) {
            const size_t n = std::min(blk_rows, R - r);
            const size_t nbytes = n * row_bytes;
            if (!in.read(reinterpret_cast<char*>(blk.data()), static_cast<std::streamsize>(nbytes)))
                throw std::runtime_error("npy: short read");
            for (size_t i = 0; i < n; ++i) {
                const size_t base = i * C;
                const int32_t okc  = blk[base + K_OK];
                const int32_t lnc  = blk[base + K_LN];
                int32_t qcode = blk[base + K_QTY];
                int32_t rcode = blk[base + K_RF];
                int32_t scode = blk[base + K_SD];

                const uint64_t rid = (static_cast<uint64_t>(static_cast<uint32_t>(okc)) << 32)
                                   | static_cast<uint64_t>(static_cast<uint32_t>(lnc));
                row_ids.push_back(rid);

                if (qcode < 0 || static_cast<uint32_t>(qcode) >= qtyDict.count) qcode = -1;
                if (rcode < 0 || static_cast<uint32_t>(rcode) >= rfDict.count)  rcode = -1;
                if (scode < 0 || static_cast<uint32_t>(scode) >= sdDict.count)  scode = -1;
                code_qty.push_back(qcode);
                code_rf .push_back(rcode);
                code_sd .push_back(scode);
            }
            r += n;
        }
    }

    const auto T1 = std::chrono::steady_clock::now(); // end load

    // Build positional truth tables Qpos_*[pos] (per-attribute positions; symmetrical to value tables)
    std::vector<uint8_t> Qpos_qty(qtyDict.count, 0);
    {
        const uint8_t* p = qty_buf.data() + qtyDict.data_offset;
        auto ensure = [&](size_t s){ if (qtyDict.data_offset + qtyDict.count*s > qty_buf.size()) throw std::runtime_error("npy: truncated l_quantity"); };
        switch (qtyDict.dtype) {
            case NpyHeader1D::DType::I32: { ensure(4); const int32_t* v = reinterpret_cast<const int32_t*>(p);
                for (size_t i=0;i<qtyDict.count;++i) Qpos_qty[i] = (v[i] < 3) ? 1 : 0; break; }
            case NpyHeader1D::DType::I64: { ensure(8); const int64_t* v = reinterpret_cast<const int64_t*>(p);
                for (size_t i=0;i<qtyDict.count;++i) Qpos_qty[i] = (v[i] < 3) ? 1 : 0; break; }
            case NpyHeader1D::DType::F32: { ensure(4); const float*   v = reinterpret_cast<const float*>(p);
                for (size_t i=0;i<qtyDict.count;++i) Qpos_qty[i] = (v[i] < 3.0f) ? 1 : 0; break; }
            case NpyHeader1D::DType::F64: { ensure(8); const double*  v = reinterpret_cast<const double*>(p);
                for (size_t i=0;i<qtyDict.count;++i) Qpos_qty[i] = (v[i] < 3.0) ? 1 : 0; break; }
            default: throw std::runtime_error("Unsupported dtype for l_quantity");
        }
    }

    auto bytes_eq_char_with_pad = [](const uint8_t* s, size_t n, char ch)->bool {
        if (n == 0) return false;
        if (s[0] != static_cast<uint8_t>(ch)) return false;
        for (size_t i=1;i<n;++i) if (!(s[i]==0 || s[i]==' ')) return false;
        return true;
    };
    auto utf32le_eq_char_with_pad = [](const uint8_t* s, size_t nBytes, char ch)->bool {
        if (nBytes < 4) return false;
        auto cp = [&](int i)->uint32_t {
            return static_cast<uint32_t>(s[i*4+0]) | (static_cast<uint32_t>(s[i*4+1])<<8)
                 | (static_cast<uint32_t>(s[i*4+2])<<16) | (static_cast<uint32_t>(s[i*4+3])<<24);
        };
        const size_t N = nBytes/4;
        if (cp(0) != static_cast<uint32_t>(static_cast<unsigned char>(ch))) return false;
        for (size_t i=1;i<N;++i) { uint32_t c = cp(static_cast<int>(i)); if (!(c==0 || c==' ')) return false; }
        return true;
    };

    std::vector<uint8_t> Qpos_rf(rfDict.count, 0);
    {
        const uint8_t* p = rf_buf.data() + rfDict.data_offset;
        auto ensure = [&](size_t elem) {
            if (rfDict.data_offset + rfDict.count * elem > rf_buf.size())
                throw std::runtime_error("npy: truncated l_returnflag dictionary payload");
        };
        switch (rfDict.dtype) {
            case NpyHeader1D::DType::BYTES: {
                ensure(rfDict.itemsize);
                for (size_t i=0;i<rfDict.count;++i) {
                    const uint8_t* s = p + i*rfDict.itemsize;
                    Qpos_rf[i] = bytes_eq_char_with_pad(s, rfDict.itemsize, 'R') ? 1 : 0;
                } break; }
            case NpyHeader1D::DType::UNICODE: {
                ensure(rfDict.itemsize);
                for (size_t i=0;i<rfDict.count;++i) {
                    const uint8_t* s = p + i*rfDict.itemsize;
                    Qpos_rf[i] = utf32le_eq_char_with_pad(s, rfDict.itemsize, 'R') ? 1 : 0;
                } break; }
            case NpyHeader1D::DType::I32: {
                ensure(4); const int32_t* v = reinterpret_cast<const int32_t*>(p);
                for (size_t i=0;i<rfDict.count;++i) Qpos_rf[i] = (v[i] == static_cast<int32_t>('R')) ? 1 : 0; break; }
            case NpyHeader1D::DType::I64: {
                ensure(8); const int64_t* v = reinterpret_cast<const int64_t*>(p);
                for (size_t i=0;i<rfDict.count;++i) Qpos_rf[i] = (v[i] == static_cast<int64_t>('R')) ? 1 : 0; break; }
            default: throw std::runtime_error("Unsupported dtype for l_returnflag");
        }
    }

    std::vector<uint8_t> Qpos_sd(sdDict.count, 0);
    {
        const uint8_t* p = sd_buf.data() + sdDict.data_offset;
        auto ensure = [&](size_t elem) {
            if (sdDict.data_offset + sdDict.count * elem > sd_buf.size())
                throw std::runtime_error("npy: truncated l_shipdate dictionary payload");
        };
        if (sdDict.dtype == NpyHeader1D::DType::BYTES) {
            ensure(sdDict.itemsize);
            for (size_t i=0;i<sdDict.count;++i) {
                const uint8_t* s = p + i*sdDict.itemsize;
                YMD ymd; bool ok = parse_ymd_ascii(s, sdDict.itemsize, ymd);
                Qpos_sd[i] = (ok && days_from_civil(ymd.y, ymd.m, ymd.d) >= cutoff_days) ? 1 : 0;
            }
        } else if (sdDict.dtype == NpyHeader1D::DType::UNICODE) {
            ensure(sdDict.itemsize);
            for (size_t i=0;i<sdDict.count;++i) {
                const uint8_t* s = p + i*sdDict.itemsize;
                YMD ymd; bool ok = parse_ymd_utf32le(s, sdDict.itemsize, ymd);
                Qpos_sd[i] = (ok && days_from_civil(ymd.y, ymd.m, ymd.d) >= cutoff_days) ? 1 : 0;
            }
        } else if (sdDict.dtype == NpyHeader1D::DType::I32) {
            ensure(4); const int32_t* v = reinterpret_cast<const int32_t*>(p);
            SdNumMode mode = detect_sd_numeric_mode(v, sdDict.count);
            for (size_t i=0;i<sdDict.count;++i) {
                int64_t val = v[i]; bool pass=false;
                switch (mode) {
                    case SdNumMode::INT_YYYYMMDD: pass = (val >= cutoff_yyyymmdd); break;
                    case SdNumMode::EPOCH_DAYS:   pass = (val >= cutoff_days);    break;
                    case SdNumMode::EPOCH_SECONDS:pass = (val >= cutoff_days * 86400); break;
                    case SdNumMode::EPOCH_MILLIS: pass = (val >= cutoff_days * 86400LL * 1000); break;
                    case SdNumMode::EPOCH_MICROS: pass = (val >= cutoff_days * 86400LL * 1000000); break;
                    case SdNumMode::EPOCH_NANOS:  pass = (val >= cutoff_days * 86400LL * 1000000000); break;
                    default: pass=false;
                }
                Qpos_sd[i] = pass ? 1 : 0;
            }
        } else if (sdDict.dtype == NpyHeader1D::DType::I64) {
            ensure(8); const int64_t* v = reinterpret_cast<const int64_t*>(p);
            SdNumMode mode = detect_sd_numeric_mode(v, sdDict.count);
            for (size_t i=0;i<sdDict.count;++i) {
                long double val = static_cast<long double>(v[i]); bool pass=false;
                switch (mode) {
                    case SdNumMode::INT_YYYYMMDD: pass = (v[i] >= cutoff_yyyymmdd); break;
                    case SdNumMode::EPOCH_DAYS:   pass = (v[i] >= cutoff_days);     break;
                    case SdNumMode::EPOCH_SECONDS:pass = (val >= (long double)cutoff_days*86400.0L); break;
                    case SdNumMode::EPOCH_MILLIS: pass = (val >= (long double)cutoff_days*86400.0L*1000.0L); break;
                    case SdNumMode::EPOCH_MICROS: pass = (val >= (long double)cutoff_days*86400.0L*1000000.0L); break;
                    case SdNumMode::EPOCH_NANOS:  pass = (val >= (long double)cutoff_days*86400.0L*1000000000.0L); break;
                    default: pass=false;
                }
                Qpos_sd[i] = pass ? 1 : 0;
            }
        } else {
            throw std::runtime_error("l_shipdate unsupported dtype");
        }
    }

    const auto T2 = std::chrono::steady_clock::now(); // end truth tables

    api::TermManager tm;
    api::Solver solver(tm);
    solver.setLogic("QF_UF");
    solver.setOption("incremental", "false");
    solver.setOption("produce-models", "true");
    const api::Sort BOOL = tm.getBooleanSort();

    // positional truth tables asserted as constants
    std::vector<api::Term> Qp_qty(qtyDict.count), Qp_rf(rfDict.count), Qp_sd(sdDict.count);
    for (size_t v = 0; v < qtyDict.count; ++v) {
        Qp_qty[v] = tm.mkConst(BOOL, "Qp_qty_" + std::to_string(v));
        solver.assertFormula(Qpos_qty[v] ? Qp_qty[v] : tm.mkTerm(api::Kind::NOT, {Qp_qty[v]}));
    }
    for (size_t v = 0; v < rfDict.count; ++v) {
        Qp_rf[v] = tm.mkConst(BOOL, "Qp_rf_" + std::to_string(v));
        solver.assertFormula(Qpos_rf[v] ? Qp_rf[v] : tm.mkTerm(api::Kind::NOT, {Qp_rf[v]}));
    }
    for (size_t v = 0; v < sdDict.count; ++v) {
        Qp_sd[v] = tm.mkConst(BOOL, "Qp_sd_" + std::to_string(v));
        solver.assertFormula(Qpos_sd[v] ? Qp_sd[v] : tm.mkTerm(api::Kind::NOT, {Qp_sd[v]}));
    }

    std::vector<api::Term> pass_rows(row_ids.size());
    for (size_t r = 0; r < row_ids.size(); ++r) {
        const int32_t vq = code_qty[r];
        const int32_t vr = code_rf[r];
        const int32_t vs = code_sd[r];

        api::Term qty_lit = tm.mkBoolean(false);
        if (vq >= 0) qty_lit = Qp_qty[static_cast<size_t>(vq)];

        std::vector<api::Term> disjuncts;
        if (vr >= 0) disjuncts.push_back(Qp_rf[static_cast<size_t>(vr)]);
        if (vs >= 0) disjuncts.push_back(Qp_sd[static_cast<size_t>(vs)]);

        api::Term right = tm.mkBoolean(false);
        if (disjuncts.empty()) right = tm.mkBoolean(false);
        else if (disjuncts.size() == 1) right = disjuncts[0];
        else right = tm.mkTerm(api::Kind::OR, disjuncts);

        api::Term clause = tm.mkTerm(api::Kind::AND, std::vector<api::Term>{ qty_lit, right });

        pass_rows[r] = tm.mkConst(BOOL, "pass_row_" + std::to_string(r));
        solver.assertFormula(tm.mkTerm(api::Kind::EQUAL, {pass_rows[r], clause}));
    }

    const auto T3a = std::chrono::steady_clock::now(); // end asserts

    // solve once
    api::Result res = solver.checkSat();
    if (!res.isSat()) {
        std::cerr << "UNSAT: writing empty result.\n";
        std::ofstream out("result.txt", std::ios::binary | std::ios::trunc);
        const auto Tend = std::chrono::steady_clock::now();
        std::cout << "Elapsed: " << std::chrono::duration_cast<std::chrono::milliseconds>(Tend - T0).count() << " ms\n";
        std::cout << "Phase(load): "   << std::chrono::duration_cast<std::chrono::milliseconds>(T1 - T0).count()  << " ms\n";
        std::cout << "Phase(truth): "  << std::chrono::duration_cast<std::chrono::milliseconds>(T2 - T1).count()  << " ms\n";
        std::cout << "Phase(assert): " << std::chrono::duration_cast<std::chrono::milliseconds>(T3a- T2).count()  << " ms\n";
        std::cout << "Phase(solve): "  << 0 << " ms\n";
        std::cout << "Phase(collect+write): " << 0 << " ms\n";
        return 0;
    }

    const auto T3b = std::chrono::steady_clock::now(); // after solve

    // collect passing rows
    std::vector<uint64_t> passed_ids; passed_ids.reserve(row_ids.size());
    for (size_t r = 0; r < row_ids.size(); ++r) {
        api::Term tv = solver.getValue(pass_rows[r]);
        bool is_true = false;
        if (tv.getKind() == api::Kind::CONST_BOOLEAN) {
            try { is_true = tv.getBooleanValue(); }
            catch (...) { is_true = (tv == tm.mkBoolean(true)); }
        }
        if (is_true) passed_ids.push_back(row_ids[r]);
    }

    const auto T4 = std::chrono::steady_clock::now(); // end collect

    // write result.txt
    std::ofstream results_out("result.txt", std::ios::binary | std::ios::trunc);
    if (!results_out) throw std::runtime_error("Failed to open result.txt for writing");
    std::string buffer; buffer.reserve(passed_ids.size() * 32);

    for (uint64_t rid : passed_ids) {
        const int32_t ok_code = static_cast<int32_t>(rid >> 32);
        const int32_t ln_code = static_cast<int32_t>(rid & 0xffffffffu);
        int64_t ok_val = 0, ln_val = 0;
        if (!dict_decode_i64_ok(okDict, ok_buf, ok_code, ok_val)) continue;
        if (!dict_decode_i64_ln(lnDict, ln_buf, ln_code, ln_val)) continue;

        char out[64]; char* p = out;
        auto r1 = std::to_chars(p, out + sizeof(out), ok_val);
        if (r1.ec != std::errc()) throw std::runtime_error("serialize ok_val failed");
        p = r1.ptr; *p++ = ',';
        auto r2 = std::to_chars(p, out + sizeof(out), ln_val);
        if (r2.ec != std::errc()) throw std::runtime_error("serialize ln_val failed");
        p = r2.ptr; *p++ = '\n';
        buffer.append(out, static_cast<size_t>(p - out));
    }

    results_out.write(buffer.data(), static_cast<std::streamsize>(buffer.size()));
    if (!results_out) throw std::runtime_error("Failed to write result.txt");

    const auto Tend = std::chrono::steady_clock::now();
    std::cout << "Elapsed: " << std::chrono::duration_cast<std::chrono::milliseconds>(Tend - T0).count() << " ms\n";
    std::cout << "Phase(load): "   << std::chrono::duration_cast<std::chrono::milliseconds>(T1 - T0).count()  << " ms\n";
    std::cout << "Phase(truth): "  << std::chrono::duration_cast<std::chrono::milliseconds>(T2 - T1).count()  << " ms\n";
    std::cout << "Phase(assert): " << std::chrono::duration_cast<std::chrono::milliseconds>(T3a- T2).count()  << " ms\n";
    std::cout << "Phase(solve): "  << std::chrono::duration_cast<std::chrono::milliseconds>(T3b- T3a).count() << " ms\n";
    std::cout << "Phase(collect): "<< std::chrono::duration_cast<std::chrono::milliseconds>(T4 - T3b).count() << " ms\n";
    std::cout << "Phase(write): "  << std::chrono::duration_cast<std::chrono::milliseconds>(Tend- T4).count()  << " ms\n";
}
