// policy = l_qty < 3  
#include <iostream>
#include <filesystem>
#include <fstream>
#include <string>
#include <vector>
#include <stdexcept>
#include <cstdint>
#include <chrono>
#include <charconv>
#include <cvc5/cvc5.h>

namespace api = cvc5;

// ---------- schema + npy helpers ----------

static std::string load_schema(const std::filesystem::path& dirpath) {
    const std::filesystem::path filepath = dirpath / "schema.json";
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

static std::vector<uint8_t> load_vals(const std::filesystem::path& dirpath, const std::string& col) {
    const std::filesystem::path filepath = dirpath / (col + ".npy");
    std::ifstream in(filepath, std::ios::in | std::ios::binary);
    if (!in) throw std::runtime_error("Failed to open dictionary: " + filepath.string());
    in.seekg(0, std::ios::end);
    std::streamoff n = in.tellg();
    if (n < 0) throw std::runtime_error("Failed to stat dictionary npy: " + filepath.string());
    in.seekg(0, std::ios::beg);
    std::vector<uint8_t> buf; buf.resize(static_cast<size_t>(n));
    if (n > 0) in.read(reinterpret_cast<char*>(buf.data()), n);
    return buf;
}

struct Npy2DInt32 { size_t rows{0}, cols{0}; size_t data_offset{0}; };

static std::string trim(const std::string& s) {
    size_t i = 0, j = s.size();
    while (i < j && std::isspace(static_cast<unsigned char>(s[i]))) ++i;
    while (j > i && std::isspace(static_cast<unsigned char>(s[j-1]))) --j;
    return s.substr(i, j - i);
}

static Npy2DInt32 load_npy_meta_2d_i32(const std::filesystem::path& p) {
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

    auto find_kw = [&](const char* k) { return header.find(k); };
    auto find_bool = [&](const char* k)->bool {
        size_t pos = find_kw(k);
        if (pos == std::string::npos) throw std::runtime_error(std::string("npy: missing key ") + k);
        size_t colon = header.find(':', pos);
        size_t start = colon + 1;
        while (start < header.size() && std::isspace(static_cast<unsigned char>(header[start]))) ++start;
        if (header.compare(start, 4, "True") == 0) return true;
        if (header.compare(start, 5, "False") == 0) return false;
        throw std::runtime_error(std::string("npy: bad bool for ") + k);
    };
    auto find_str = [&](const char* k)->std::string {
        size_t pos = header.find(k);
        if (pos == std::string::npos) throw std::runtime_error(std::string("npy: missing key ") + k);
        size_t colon = header.find(':', pos);
        size_t q1 = header.find('\'', colon + 1);
        size_t q2 = (q1 == std::string::npos) ? q1 : header.find('\'', q1 + 1);
        if (q1 == std::string::npos || q2 == std::string::npos) throw std::runtime_error("npy: bad string");
        return header.substr(q1 + 1, q2 - q1 - 1);
    };

    const bool fortran_order = find_bool("'fortran_order'");
    if (fortran_order) throw std::runtime_error("npy: fortran order not supported");
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

struct NpyHeader1D {
    size_t data_offset{0};
    size_t count{0};
    enum class DType { I32, I64, F32, F64 } dtype{DType::F64};
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

    const std::string descr = find_str("'descr'");
    NpyHeader1D h;
    if (descr == "<i4") h.dtype = NpyHeader1D::DType::I32;
    else if (descr == "<i8") h.dtype = NpyHeader1D::DType::I64;
    else if (descr == "<f4") h.dtype = NpyHeader1D::DType::F32;
    else if (descr == "<f8") h.dtype = NpyHeader1D::DType::F64;
    else throw std::runtime_error("npy: unsupported dictionary dtype: " + descr);

    size_t shp = header.find("'shape'");
    if (shp == std::string::npos) throw std::runtime_error("npy: missing shape");
    size_t lp = header.find('(', shp);
    size_t rp = header.find(')', lp);
    if (lp == std::string::npos || rp == std::string::npos) throw std::runtime_error("npy: bad shape");
    std::string inside = header.substr(lp + 1, rp - lp - 1);
    inside = trim(inside);
    if (inside.size() < 1) throw std::runtime_error("npy: bad 1D shape");
    if (inside.back() == ',') inside.pop_back();
    h.count = static_cast<size_t>(std::stoull(inside));
    h.data_offset = 6 + 2 + 2 + hlen;
    return h;
}

// ---------- dict decode for OK/LN ----------

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


int main() {
    const auto t0 = std::chrono::steady_clock::now();

    const std::filesystem::path tables("tables0_1");
    const std::filesystem::path lineitem = tables / "lineitem";

    const std::string l_ok  = "l_orderkey";
    const std::string l_ln  = "l_linenumber";
    const std::string l_qty = "l_quantity";

    const std::string schema = load_schema(lineitem);
    const int i_l_ok  = col_index(schema, l_ok);
    const int i_l_ln  = col_index(schema, l_ln);
    const int i_l_qty = col_index(schema, l_qty);

    const std::vector<uint8_t> ok_buf  = load_vals(lineitem, l_ok);
    const std::vector<uint8_t> ln_buf  = load_vals(lineitem, l_ln);
    const std::vector<uint8_t> qty_buf = load_vals(lineitem, l_qty);

    const NpyHeader1D okDict  = parse_npy_header_1d(ok_buf);
    const NpyHeader1D lnDict  = parse_npy_header_1d(ln_buf);
    const NpyHeader1D qtyDict = parse_npy_header_1d(qty_buf);

    // Read codes once into arrays and compute "present" values for l_quantity
    const std::filesystem::path codes_path = lineitem / "codes.npy";
    const Npy2DInt32 codesMeta = load_npy_meta_2d_i32(codes_path);
    const size_t R = codesMeta.rows;
    const size_t C = codesMeta.cols;
    const size_t K_OK  = static_cast<size_t>(i_l_ok);
    const size_t K_LN  = static_cast<size_t>(i_l_ln);
    const size_t K_QTY = static_cast<size_t>(i_l_qty);

    std::vector<uint64_t> row_ids; row_ids.reserve(R);
    std::vector<int32_t>  qty_code; qty_code.reserve(R);
    std::vector<uint8_t>  present(qtyDict.count, 0);

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
                if (qcode < 0 || static_cast<uint32_t>(qcode) >= qtyDict.count) qcode = -1;

                const uint64_t rid = (static_cast<uint64_t>(static_cast<uint32_t>(okc)) << 32)
                                   | static_cast<uint64_t>(static_cast<uint32_t>(lnc));
                row_ids.push_back(rid);
                qty_code.push_back(qcode);

                if (qcode >= 0) present[static_cast<size_t>(qcode)] = 1;
            }
            r += n;
        }
    }

    // S_qty[v] = (dictionary value at v) < 3
    std::vector<uint8_t> S_qty(qtyDict.count, 0);
    {
        const uint8_t* p = qty_buf.data() + qtyDict.data_offset;
        auto ensure = [&](size_t elem_size) {
            const size_t need = qtyDict.count * elem_size;
            if (qtyDict.data_offset + need > qty_buf.size())
                throw std::runtime_error("npy: truncated l_quantity dictionary payload");
        };
        switch (qtyDict.dtype) {
            case NpyHeader1D::DType::I32: {
                ensure(sizeof(int32_t));
                const int32_t* v = reinterpret_cast<const int32_t*>(p);
                for (size_t i = 0; i < qtyDict.count; ++i) S_qty[i] = (v[i] < 3) ? 1 : 0;
                break;
            }
            case NpyHeader1D::DType::I64: {
                ensure(sizeof(int64_t));
                const int64_t* v = reinterpret_cast<const int64_t*>(p);
                for (size_t i = 0; i < qtyDict.count; ++i) S_qty[i] = (v[i] < 3) ? 1 : 0;
                break;
            }
            case NpyHeader1D::DType::F32: {
                ensure(sizeof(float));
                const float* v = reinterpret_cast<const float*>(p);
                for (size_t i = 0; i < qtyDict.count; ++i) S_qty[i] = (v[i] < 3.0f) ? 1 : 0;
                break;
            }
            case NpyHeader1D::DType::F64: {
                ensure(sizeof(double));
                const double* v = reinterpret_cast<const double*>(p);
                for (size_t i = 0; i < qtyDict.count; ++i) S_qty[i] = (v[i] < 3.0) ? 1 : 0;
                break;
            }
            default:
                throw std::runtime_error("Unsupported dtype for l_quantity");
        }
    }


    api::TermManager tm;
    api::Solver solver(tm);
    solver.setLogic("QF_UF");
    solver.setOption("incremental", "false");   // single solve
    solver.setOption("produce-models", "true"); // to read pass_rows
    const api::Sort BOOL = tm.getBooleanSort();

    // x_va[v]: define for ALL values; asserted true if present, false otherwise
    std::vector<api::Term> x_va(qtyDict.count);
    for (size_t v = 0; v < qtyDict.count; ++v) {
        x_va[v] = tm.mkConst(BOOL, "x_va_l_quantity_" + std::to_string(v));
        if (present[v]) {
            solver.assertFormula(x_va[v]);
        } else {
            solver.assertFormula(tm.mkTerm(api::Kind::NOT, {x_va[v]}));
        }
    }

    // Q_qty[v]: literal membership at that value
    std::vector<api::Term> Q_qty(qtyDict.count);
    for (size_t v = 0; v < qtyDict.count; ++v) {
        Q_qty[v] = tm.mkConst(BOOL, "Q_l_quantity_lt3_" + std::to_string(v));
        if (S_qty[v]) {
            solver.assertFormula(Q_qty[v]);
        } else {
            solver.assertFormula(tm.mkTerm(api::Kind::NOT, {Q_qty[v]}));
        }
    }

    // Rows: X_rv[r] asserted true (so pass_rows can be forced true when value satisfies)
    std::vector<api::Term> X_rv(row_ids.size());
    std::vector<api::Term> pass_rows(row_ids.size());
    for (size_t r = 0; r < row_ids.size(); ++r) {
        X_rv[r] = tm.mkConst(BOOL, "X_rv_l_quantity_row_" + std::to_string(r));
        solver.assertFormula(X_rv[r]); // assert row indicator true

        const int32_t qc = qty_code[r];
        api::Term clause;
        if (qc < 0) {
            clause = tm.mkBoolean(false);
        } else {
            const size_t v = static_cast<size_t>(qc);
            clause = tm.mkTerm(api::Kind::AND, std::vector<api::Term>{
                X_rv[r], x_va[v], Q_qty[v]
            });
        }
        pass_rows[r] = tm.mkConst(BOOL, "pass_row_" + std::to_string(r));
        solver.assertFormula(tm.mkTerm(api::Kind::EQUAL, {pass_rows[r], clause}));
    }

    // Solve once
    api::Result res = solver.checkSat();
    if (!res.isSat()) {
        std::cerr << "UNSAT: global constraints inconsistent; writing empty result.\n";
        std::ofstream out("result.txt", std::ios::binary | std::ios::trunc);
        const auto t1 = std::chrono::steady_clock::now();
        std::cout << "Elapsed: " << std::chrono::duration_cast<std::chrono::milliseconds>(t1 - t0).count() << " ms\n";
        std::cout << "Elapsed: 0 ms\n";
        return 0;
    }

    // Collect and write results
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

    const auto t1 = std::chrono::steady_clock::now();
    std::cout << "Elapsed: " << std::chrono::duration_cast<std::chrono::milliseconds>(t1 - t0).count() << " ms\n";

    std::ofstream results_out("result.txt", std::ios::binary | std::ios::trunc);
    if (!results_out) throw std::runtime_error("Failed to open result.txt for writing");
    std::string buffer; buffer.reserve(passed_ids.size() * 32);

    for (uint64_t rid : passed_ids) {
        const int32_t ok_code = static_cast<int32_t>(rid >> 32);
        const int32_t ln_code = static_cast<int32_t>(rid & 0xffffffffu);

        int64_t ok_val = 0, ln_val = 0;
        if (!dict_decode_i64(okDict, ok_buf, ok_code, ok_val)) continue;
        if (!dict_decode_i64(lnDict, ln_buf, ln_code, ln_val)) continue;

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

    const auto t2 = std::chrono::steady_clock::now();
    std::cout << "Elapsed: " << std::chrono::duration_cast<std::chrono::milliseconds>(t2 - t1).count() << " ms\n";
}
