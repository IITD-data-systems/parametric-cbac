// policy = l_quantity < 3


#include <algorithm>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>
#include <cvc5/cvc5.h>

namespace fs  = std::filesystem;
namespace api = cvc5;

// ============================== schema + npy helpers (subset of your originals) ==============================
static std::string load_schema(const fs::path& dirpath) {
    const fs::path filepath = dirpath / "schema.json";
    std::ifstream in(filepath, std::ios::in | std::ios::binary);
    if (!in) throw std::runtime_error("Failed to open schema.json at: " + filepath.string());
    in.seekg(0, std::ios::end); std::streamoff n = in.tellg(); if (n < 0) throw std::runtime_error("Failed to stat schema.json");
    in.seekg(0, std::ios::beg); std::string s; s.resize(static_cast<size_t>(n)); if (n > 0) in.read(&s[0], static_cast<std::streamsize>(n));
    return s;
}

static int col_index(const std::string& schema_json, const std::string& name) {
    const std::string key = "\"name\""; size_t pos = 0; int idx = 0;
    while (true) {
        size_t k = schema_json.find(key, pos); if (k == std::string::npos) break;
        size_t colon = schema_json.find(':', k + key.size()); if (colon == std::string::npos) break;
        size_t q1 = schema_json.find('"', colon + 1); if (q1 == std::string::npos) break;
        size_t q2 = schema_json.find('"', q1 + 1); if (q2 == std::string::npos) break;
        std::string val = schema_json.substr(q1 + 1, q2 - q1 - 1);
        if (val == name) return idx; ++idx; pos = q2 + 1;
    }
    throw std::out_of_range("Column name not found in schema: " + name);
}

struct Npy2DInt32 { size_t rows{0}, cols{0}, data_offset{0}; };
static Npy2DInt32 load_npy_meta_2d_i32(const fs::path& p) {
    std::ifstream in(p, std::ios::in | std::ios::binary);
    if (!in) throw std::runtime_error("Failed to open npy file: " + p.string());
    char magic[6]; if (!in.read(magic, 6)) throw std::runtime_error("npy: short read (magic)");
    if (!(magic[0] == char(0x93) && magic[1]=='N' && magic[2]=='U' && magic[3]=='M' && magic[4]=='P' && magic[5]=='Y'))
        throw std::runtime_error("npy: bad magic header");
    unsigned char ver[2]; if (!in.read(reinterpret_cast<char*>(ver), 2)) throw std::runtime_error("npy: short read (version)");
    if (!(ver[0] == 1 && ver[1] == 0)) throw std::runtime_error("npy: only v1.0 supported");
    uint16_t hlen; if (!in.read(reinterpret_cast<char*>(&hlen), 2)) throw std::runtime_error("npy: short read (hlen)");
    std::string header(hlen, '\0'); if (!in.read(header.data(), hlen)) throw std::runtime_error("npy: short read (header)");
    // dtype check
    if (header.find("'descr': '<i4'") == std::string::npos) throw std::runtime_error("npy: codes.npy must be <i4");
    // fortran order must be False
    if (header.find("'fortran_order': False") == std::string::npos) throw std::runtime_error("npy: need C-order");
    // shape parsing: (rows, cols)
    size_t shp = header.find("'shape':"); if (shp == std::string::npos) throw std::runtime_error("npy: missing shape");
    size_t lp = header.find('(', shp); size_t rp = header.find(')', lp);
    if (lp == std::string::npos || rp == std::string::npos) throw std::runtime_error("npy: bad shape");
    auto trim = [](const std::string& s){ size_t i=0,j=s.size(); while(i<j && isspace((unsigned char)s[i])) ++i; while(j>i && isspace((unsigned char)s[j-1])) --j; return s.substr(i,j-i); };
    std::string inside = trim(header.substr(lp+1, rp-lp-1)); size_t comma = inside.find(',');
    if (comma == std::string::npos) throw std::runtime_error("npy: shape must be 2D");
    Npy2DInt32 m; m.rows = static_cast<size_t>(std::stoull(trim(inside.substr(0, comma))));
    std::string s2 = trim(inside.substr(comma+1)); if (!s2.empty() && s2.back()==',') s2.pop_back();
    m.cols = static_cast<size_t>(std::stoull(s2)); m.data_offset = 6 + 2 + 2 + hlen; return m;
}

// 1D dictionary header with numeric types (I32/I64/F32/F64) and minimal BYTES/UNICODE for completeness
struct NpyHeader1D { size_t data_offset{0}, count{0}; enum class DType { I32, I64, F32, F64, BYTES, UNICODE } dtype{DType::F64}; size_t itemsize{0}; };
static NpyHeader1D parse_npy_header_1d(const std::vector<uint8_t>& npy) {
    if (npy.size() < 14) throw std::runtime_error("npy: buffer too small");
    const uint8_t* p = npy.data(); const char magic[] = {'\x93','N','U','M','P','Y'}; for (int i=0;i<6;++i) if (p[i]!=static_cast<uint8_t>(magic[i])) throw std::runtime_error("npy: bad magic");
    if (!(p[6]==1 && p[7]==0)) throw std::runtime_error("npy: only v1.0 supported");
    uint16_t hlen = static_cast<uint16_t>(p[8]) | (static_cast<uint16_t>(p[9])<<8);
    std::string header(reinterpret_cast<const char*>(p+10), hlen);
    auto has = [&](const char* s){ return header.find(s) != std::string::npos; };
    NpyHeader1D h; h.data_offset = 6 + 2 + 2 + hlen;
    if (has("'descr': '<i4'")) h.dtype = NpyHeader1D::DType::I32;
    else if (has("'descr': '<i8'")) h.dtype = NpyHeader1D::DType::I64;
    else if (has("'descr': '<f4'")) h.dtype = NpyHeader1D::DType::F32;
    else if (has("'descr': '<f8'")) h.dtype = NpyHeader1D::DType::F64;
    else if (has("'descr': '|S")) { h.dtype = NpyHeader1D::DType::BYTES; size_t a = header.find("'descr': '|S"); size_t q = header.find('\'', a+12); h.itemsize = static_cast<size_t>(std::stoull(header.substr(a+12, q-(a+12)))); }
    else if (has("'descr': '<U")) { h.dtype = NpyHeader1D::DType::UNICODE; size_t a = header.find("'descr': '<U"); size_t q = header.find('\'', a+12); h.itemsize = static_cast<size_t>(std::stoull(header.substr(a+12, q-(a+12)))) * 4; }
    else throw std::runtime_error("npy: unsupported dtype");
    size_t shp = header.find("'shape':"); if (shp == std::string::npos) throw std::runtime_error("npy: missing shape");
    size_t lp = header.find('(', shp); size_t rp = header.find(')', lp); if (lp == std::string::npos || rp == std::string::npos) throw std::runtime_error("npy: bad 1D shape");
    auto trim2 = [](const std::string& s){ size_t i=0,j=s.size(); while(i<j && isspace((unsigned char)s[i])) ++i; while(j>i && isspace((unsigned char)s[j-1])) --j; return s.substr(i,j-i); };
    std::string inside = trim2(header.substr(lp+1, rp-lp-1)); if (inside.empty()) throw std::runtime_error("npy: bad 1D shape"); if (inside.back()==',') inside.pop_back();
    h.count = static_cast<size_t>(std::stoull(inside)); return h;
}

static bool dict_decode_i64(const NpyHeader1D& meta, const std::vector<uint8_t>& buf, int32_t code, int64_t& out) {
    if (code < 0) return false; const uint32_t idx = static_cast<uint32_t>(code); if (idx >= meta.count) return false;
    const uint8_t* p = buf.data() + meta.data_offset;
    switch (meta.dtype) {
        case NpyHeader1D::DType::I32: out = static_cast<int64_t>(reinterpret_cast<const int32_t*>(p)[idx]); return true;
        case NpyHeader1D::DType::I64: out = reinterpret_cast<const int64_t*>(p)[idx]; return true;
        default: return false; // ok/ln should be numeric
    }
}



int main() {
    const auto T0 = std::chrono::steady_clock::now();

    // --- Paths & schema ---
    const fs::path lineitem = fs::path("tables10") / "lineitem";
    const std::string l_ok  = "l_orderkey";
    const std::string l_ln  = "l_linenumber";
    const std::string l_qty = "l_quantity";

    const std::string schema = load_schema(lineitem);
    const int i_l_ok  = col_index(schema, l_ok);
    const int i_l_ln  = col_index(schema, l_ln);
    const int i_l_qty = col_index(schema, l_qty);

    auto load_vals = [&](const std::string& col)->std::vector<uint8_t>{
        const fs::path filepath = lineitem / (col + ".npy");
        std::ifstream in(filepath, std::ios::in | std::ios::binary);
        if (!in) throw std::runtime_error("Failed to open dictionary: " + filepath.string());
        in.seekg(0, std::ios::end); std::streamoff n = in.tellg(); in.seekg(0, std::ios::beg);
        std::vector<uint8_t> buf; buf.resize(static_cast<size_t>(n)); if (n > 0) in.read(reinterpret_cast<char*>(buf.data()), n);
        return buf;
    };

    const std::vector<uint8_t> ok_buf  = load_vals(l_ok);
    const std::vector<uint8_t> ln_buf  = load_vals(l_ln);
    const std::vector<uint8_t> qty_buf = load_vals(l_qty);

    const NpyHeader1D okDict  = parse_npy_header_1d(ok_buf);
    const NpyHeader1D lnDict  = parse_npy_header_1d(ln_buf);
    const NpyHeader1D qtyDict = parse_npy_header_1d(qty_buf);

    const fs::path codes_path = lineitem / "codes.npy";
    const Npy2DInt32 codesMeta = load_npy_meta_2d_i32(codes_path);
    const size_t R = codesMeta.rows, C = codesMeta.cols;
    const size_t K_OK  = static_cast<size_t>(i_l_ok);
    const size_t K_LN  = static_cast<size_t>(i_l_ln);
    const size_t K_QTY = static_cast<size_t>(i_l_qty);

    std::vector<uint64_t> row_ids; row_ids.reserve(R);
    std::vector<int32_t>  qty_code; qty_code.reserve(R);
    std::vector<int32_t>  ok_code;  ok_code.reserve(R);
    std::vector<int32_t>  ln_code;  ln_code.reserve(R);

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
                int32_t okc  = blk[base + K_OK];
                int32_t lnc  = blk[base + K_LN];
                int32_t qcode = blk[base + K_QTY];
                if (okc < 0 || static_cast<uint32_t>(okc) >= okDict.count) okc = -1;
                if (lnc < 0 || static_cast<uint32_t>(lnc) >= lnDict.count) lnc = -1;
                if (qcode < 0 || static_cast<uint32_t>(qcode) >= qtyDict.count) qcode = -1;
                ok_code.push_back(okc);
                ln_code.push_back(lnc);
                qty_code.push_back(qcode);
                const uint64_t rid = (static_cast<uint64_t>(static_cast<uint32_t>(okc)) << 32)
                                   | static_cast<uint64_t>(static_cast<uint32_t>(lnc));
                row_ids.push_back(rid);
            }
            r += n;
        }
    }

    const auto T1 = std::chrono::steady_clock::now(); // end load

    // --- Build value truth table Sv_qty[v] ---
    std::vector<uint8_t> Sv_qty(qtyDict.count, 0);
    {
        const uint8_t* p = qty_buf.data() + qtyDict.data_offset;
        auto ensure = [&](size_t elem_size) {
            if (qtyDict.data_offset + qtyDict.count * elem_size > qty_buf.size())
                throw std::runtime_error("npy: truncated l_quantity dictionary payload");
        };
        switch (qtyDict.dtype) {
            case NpyHeader1D::DType::I32: { ensure(4); const int32_t* v = reinterpret_cast<const int32_t*>(p);
                for (size_t i=0;i<qtyDict.count;++i) Sv_qty[i] = (v[i] < 3) ? 1 : 0; break; }
            case NpyHeader1D::DType::I64: { ensure(8); const int64_t* v = reinterpret_cast<const int64_t*>(p);
                for (size_t i=0;i<qtyDict.count;++i) Sv_qty[i] = (v[i] < 3) ? 1 : 0; break; }
            case NpyHeader1D::DType::F32: { ensure(4); const float* v = reinterpret_cast<const float*>(p);
                for (size_t i=0;i<qtyDict.count;++i) Sv_qty[i] = (v[i] < 3.0f) ? 1 : 0; break; }
            case NpyHeader1D::DType::F64: { ensure(8); const double* v = reinterpret_cast<const double*>(p);
                for (size_t i=0;i<qtyDict.count;++i) Sv_qty[i] = (v[i] < 3.0) ? 1 : 0; break; }
            default: throw std::runtime_error("Unsupported dtype for l_quantity");
        }
    }

    const auto T2 = std::chrono::steady_clock::now(); // end stamps (truth)

    // --- Signatures over I_ok ---
    std::unordered_map<int32_t, uint8_t> sig_by_ok; // ok token -> 2-bit signature (Y1|Y2<<1)
    sig_by_ok.reserve(1024);
    std::vector<uint8_t> TL; TL.resize(qty_code.size(), 0);
    for (size_t r = 0; r < qty_code.size(); ++r) {
        int32_t qc = qty_code[r]; bool lt3 = (qc >= 0) ? (Sv_qty[static_cast<size_t>(qc)] != 0) : false;
        TL[r] = lt3 ? 1 : 0;
        int32_t okc = ok_code[r]; if (okc < 0) continue;
        uint8_t& sig = sig_by_ok[okc]; sig |= 0b01; if (lt3) sig |= 0b10;
    }

    const auto T3 = std::chrono::steady_clock::now(); // end signatures

    // --- Binning: signature -> anchors (ok tokens) ---
    std::unordered_map<uint8_t, std::vector<int32_t>> bins;
    bins.reserve(4);
    for (const auto& kv : sig_by_ok) bins[kv.second].push_back(kv.first);

    const auto T4 = std::chrono::steady_clock::now(); // end binning

    // --- SAT: one var per class; X_sig <-> (bit1 of signature) ---
    api::TermManager tm; api::Solver solver(tm);
    solver.setLogic("QF_UF"); solver.setOption("produce-models", "true");
    const api::Sort BOOL = tm.getBooleanSort();

    std::unordered_map<uint8_t, api::Term> X_of_sig;
    for (const auto& kv : bins) {
        uint8_t sig = kv.first; api::Term X = tm.mkConst(BOOL, std::string("X_sig_") + std::to_string((int)sig));
        X_of_sig[sig] = X; bool y2 = (sig & 0b10) != 0; api::Term Y2 = tm.mkBoolean(y2);
        solver.assertFormula(tm.mkTerm(api::Kind::EQUAL, {X, Y2}));
    }

    const auto T5a = std::chrono::steady_clock::now();
    api::Result sat = solver.checkSat();
    const auto T5b = std::chrono::steady_clock::now();

    std::unordered_set<int32_t> S_ok; // authorized anchors
    if (sat.isSat()) {
        for (const auto& kv : bins) {
            uint8_t sig = kv.first; bool truth = solver.getValue(X_of_sig[sig]).getBooleanValue();
            if (truth) for (int32_t okc : kv.second) S_ok.insert(okc);
        }
    } else {
        std::cerr << "[WARN] UNSAT in class solve; authorizing no classes.\n";
    }

    const auto T6 = std::chrono::steady_clock::now(); // end SAT/collect

    // --- Projection & write ---
    std::ofstream results_out("result.txt", std::ios::out | std::ios::binary);
    if (!results_out) throw std::runtime_error("Failed to open result.txt for writing");

    const size_t MAXBUF = 1 << 20; std::string buffer; buffer.reserve(MAXBUF);
    auto flush_buf = [&](){ if (!buffer.empty()) { results_out.write(buffer.data(), static_cast<std::streamsize>(buffer.size())); buffer.clear(); } };

    size_t emitted = 0;
    for (size_t r = 0; r < row_ids.size(); ++r) {
        if (!TL[r]) continue; // enforce qty<3
        int32_t okc = ok_code[r]; if (okc < 0) continue; if (!S_ok.count(okc)) continue; // authorized anchor
        int32_t lnc = ln_code[r];
        int64_t okv = 0, lnv = 0; if (!dict_decode_i64(okDict, ok_buf, okc, okv)) continue; if (!dict_decode_i64(lnDict, ln_buf, lnc, lnv)) continue;
        buffer.append(std::to_string(okv)); buffer.push_back(','); buffer.append(std::to_string(lnv)); buffer.push_back('\n');
        if (buffer.size() > MAXBUF/2) flush_buf(); ++emitted;
    }
    flush_buf(); if (!results_out) throw std::runtime_error("Failed to write result.txt");

    const auto Tend = std::chrono::steady_clock::now();
    std::cout << "Elapsed: " << std::chrono::duration_cast<std::chrono::milliseconds>(Tend - T0).count() << " ms\n";
    std::cout << "Phase(load):   " << std::chrono::duration_cast<std::chrono::milliseconds>(T1 - T0).count()  << " ms\n";
    std::cout << "Phase(truth):  " << std::chrono::duration_cast<std::chrono::milliseconds>(T2 - T1).count()  << " ms\n";
    std::cout << "Phase(sign):   " << std::chrono::duration_cast<std::chrono::milliseconds>(T3 - T2).count()  << " ms\n";
    std::cout << "Phase(bin):    " << std::chrono::duration_cast<std::chrono::milliseconds>(T4 - T3).count()  << " ms\n";
    std::cout << "Phase(assert): " << std::chrono::duration_cast<std::chrono::milliseconds>(T5a- T4).count()  << " ms\n";
    std::cout << "Phase(solve):  " << std::chrono::duration_cast<std::chrono::milliseconds>(T5b- T5a).count() << " ms\n";
    std::cout << "Phase(collect):" << std::chrono::duration_cast<std::chrono::milliseconds>(T6 - T5b).count() << " ms\n";
    std::cout << "Phase(write):  " << std::chrono::duration_cast<std::chrono::milliseconds>(Tend- T6).count()  << " ms\n";
}
