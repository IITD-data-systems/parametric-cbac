#include <algorithm>
#include <cctype>
#include <cstdint>
#include <cstring>
#include <map>
#include <set>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

extern "C" {
typedef bool (*emit_invidx_read_fn)(
    void*, const char*, const std::uint8_t**, std::size_t*);
typedef void (*emit_invidx_write_fn)(
    void*, const char*, const std::uint8_t*, std::size_t);
}

namespace {

thread_local std::string last_error;

[[noreturn]] void fail(const std::string& message) {
    throw std::runtime_error(message);
}

class ArtifactIO {
public:
    ArtifactIO(void* context,
               emit_invidx_read_fn read,
               emit_invidx_write_fn write)
        : context_(context), read_(read), write_(write) {
        if (!read_ || !write_) fail("null artifact callback");
    }

    bool try_read(const std::string& name,
                  std::vector<std::uint8_t>& output) const {
        const std::uint8_t* data = nullptr;
        std::size_t size = 0;
        if (!read_(context_, name.c_str(), &data, &size)) {
            output.clear();
            return false;
        }
        if (size != 0 && data == nullptr) {
            fail("null data for artifact " + name);
        }
        if (size == 0) {
            output.clear();
            return true;
        }
        output.assign(data, data + size);
        return true;
    }

    std::vector<std::uint8_t> read(const std::string& name) const {
        std::vector<std::uint8_t> output;
        if (!try_read(name, output)) {
            fail("missing artifact " + name);
        }
        return output;
    }

    void write(const std::string& name,
               const std::vector<std::uint8_t>& bytes) const {
        write_(context_, name.c_str(), bytes.data(), bytes.size());
    }

private:
    void* context_;
    emit_invidx_read_fn read_;
    emit_invidx_write_fn write_;
};

std::uint16_t u16le(const std::uint8_t* bytes) {
    return static_cast<std::uint16_t>(bytes[0]) |
        static_cast<std::uint16_t>(
            static_cast<std::uint16_t>(bytes[1]) << 8U);
}

std::uint32_t u32le(const std::uint8_t* bytes) {
    return static_cast<std::uint32_t>(bytes[0]) |
        (static_cast<std::uint32_t>(bytes[1]) << 8U) |
        (static_cast<std::uint32_t>(bytes[2]) << 16U) |
        (static_cast<std::uint32_t>(bytes[3]) << 24U);
}

void append_u32(std::vector<std::uint8_t>& bytes,
                std::uint32_t value) {
    bytes.push_back(static_cast<std::uint8_t>(value));
    bytes.push_back(static_cast<std::uint8_t>(value >> 8U));
    bytes.push_back(static_cast<std::uint8_t>(value >> 16U));
    bytes.push_back(static_cast<std::uint8_t>(value >> 24U));
}

void append_u32s(std::vector<std::uint8_t>& bytes,
                 const std::vector<std::uint32_t>& values) {
    for (const std::uint32_t value : values) append_u32(bytes, value);
}

std::vector<std::string> read_lines(const ArtifactIO& io,
                                    const std::string& name) {
    const std::vector<std::uint8_t> bytes = io.read(name);
    const std::string text(bytes.begin(), bytes.end());
    std::vector<std::string> lines;
    std::size_t begin = 0;
    while (begin < text.size()) {
        const std::size_t newline = text.find('\n', begin);
        const std::size_t end =
            newline == std::string::npos ? text.size() : newline;
        std::string line = text.substr(begin, end - begin);
        if (!line.empty() && line.back() == '\r') line.pop_back();
        if (!line.empty()) lines.push_back(std::move(line));
        if (newline == std::string::npos) break;
        begin = newline + 1U;
    }
    return lines;
}

std::map<std::string, std::string>
load_col_domains(const ArtifactIO& io) {
    std::map<std::string, std::string> result;
    for (const std::string& line :
         read_lines(io, "meta/col_domain")) {
        const std::size_t equals = line.find('=');
        if (equals == std::string::npos) {
            fail("bad col_domain row: " + line);
        }
        result.emplace(
            line.substr(0, equals), line.substr(equals + 1U));
    }
    return result;
}

struct CodeBase {
    std::uint32_t total_rows = 0;
    std::uint32_t chunk_count = 0;
};

CodeBase load_code_base(const ArtifactIO& io,
                        const std::string& table) {
    const std::vector<std::uint8_t> bytes =
        io.read(table + "_code_base");
    if (bytes.size() < 20U ||
        std::memcmp(bytes.data(), "CB04", 4U) != 0) {
        fail("bad code base for " + table);
    }
    return CodeBase{u32le(bytes.data() + 4U),
                    u32le(bytes.data() + 16U)};
}

class PackedDecoder {
public:
    PackedDecoder(const std::vector<std::uint8_t>& chunk,
                  std::string name)
        : name_(std::move(name)) {
        if (chunk.size() < 16U ||
            std::memcmp(chunk.data(), "CC04", 4U) != 0) {
            fail("bad code chunk " + name_);
        }
        rows_ = u32le(chunk.data() + 4U);
        width_ = u16le(chunk.data() + 8U);
        if (width_ == 0 || width_ > 32U) {
            fail("bad bit width in " + name_);
        }
        payload_ = chunk.data() + 16U;
        payload_size_ = chunk.size() - 16U;
        mask_ = width_ == 32U ? UINT64_C(0xffffffff) :
            ((UINT64_C(1) << width_) - 1U);
    }

    std::uint32_t rows() const { return rows_; }

    std::uint32_t next() {
        while (available_bits_ < width_) {
            if (payload_offset_ >= payload_size_) {
                fail("packed payload ended early in " + name_);
            }
            accumulator_ |=
                static_cast<std::uint64_t>(
                    payload_[payload_offset_++])
                << available_bits_;
            available_bits_ += 8U;
        }
        const std::uint32_t encoded =
            static_cast<std::uint32_t>(accumulator_ & mask_);
        accumulator_ >>= width_;
        available_bits_ -= width_;
        return encoded;
    }

private:
    std::string name_;
    const std::uint8_t* payload_ = nullptr;
    std::size_t payload_size_ = 0;
    std::size_t payload_offset_ = 0;
    std::uint32_t rows_ = 0;
    std::uint16_t width_ = 0;
    std::uint64_t mask_ = 0;
    std::uint64_t accumulator_ = 0;
    std::uint16_t available_bits_ = 0;
};

template <typename Visitor>
void scan_column(const ArtifactIO& io,
                 const std::string& table,
                 std::size_t column_index,
                 const CodeBase& base,
                 Visitor&& visitor) {
    std::uint64_t row_base = 0;
    for (std::uint32_t chunk_index = 0;
         chunk_index < base.chunk_count; ++chunk_index) {
        const std::string name =
            table + "_code_col_" + std::to_string(column_index) +
            "_chunk_" + std::to_string(chunk_index);
        const std::vector<std::uint8_t> chunk = io.read(name);
        PackedDecoder decoder(chunk, name);
        for (std::uint32_t row = 0; row < decoder.rows(); ++row) {
            visitor(static_cast<std::uint32_t>(row_base + row),
                    decoder.next());
        }
        row_base += decoder.rows();
    }
    if (row_base != base.total_rows) {
        fail("code chunks do not sum to total rows for " + table);
    }
}

std::pair<std::string, std::string>
split_qualified(const std::string& qualified) {
    const std::size_t dot = qualified.find('.');
    if (dot == std::string::npos) {
        fail("unqualified column " + qualified);
    }
    return {qualified.substr(0, dot), qualified.substr(dot + 1U)};
}

std::size_t resolve_column_index(const ArtifactIO& io,
                                 const std::string& table,
                                 const std::string& qualified) {
    const std::vector<std::string> columns =
        read_lines(io, "meta/cols/" + table);
    const auto found =
        std::find(columns.begin(), columns.end(), qualified);
    if (found == columns.end()) {
        fail("column absent from meta/cols: " + qualified);
    }
    return static_cast<std::size_t>(found - columns.begin());
}

std::vector<std::uint32_t>
collect_present_tokens(const ArtifactIO& io,
                       const std::string& qualified,
                       const std::string& domain_text) {
    const auto [table, column] = split_qualified(qualified);
    (void)column;
    const std::vector<std::uint8_t> ranks =
        io.read("rank/domain/" + domain_text);
    if (ranks.size() % sizeof(std::uint32_t) != 0) {
        fail("bad rank map for domain " + domain_text);
    }
    const std::size_t token_count = ranks.size() / 4U;
    std::vector<std::uint8_t> present(token_count, 0);
    const std::size_t column_index =
        resolve_column_index(io, table, qualified);
    const CodeBase base = load_code_base(io, table);
    scan_column(io, table, column_index, base,
        [&](std::uint32_t, std::uint32_t encoded) {
            if (encoded == 0) return;
            const std::uint32_t token = encoded - 1U;
            if (token >= token_count) {
                fail("token exceeds source domain for " + qualified);
            }
            present[token] = 1;
        });
    std::vector<std::uint32_t> tokens;
    for (std::size_t token = 0; token < token_count; ++token) {
        if (present[token]) {
            tokens.push_back(static_cast<std::uint32_t>(token));
        }
    }
    std::sort(tokens.begin(), tokens.end(),
        [&](std::uint32_t left, std::uint32_t right) {
            return u32le(ranks.data() +
                         static_cast<std::size_t>(left) * 4U) <
                   u32le(ranks.data() +
                         static_cast<std::size_t>(right) * 4U);
        });
    return tokens;
}

const std::map<std::string, std::string>& schema_key_columns() {
    static const std::map<std::string, std::string> columns{
        {"customer.c_custkey", "custkey"},
        {"orders.o_custkey", "custkey"},
        {"orders.o_orderkey", "orderkey"},
        {"lineitem.l_orderkey", "orderkey"},
        {"part.p_partkey", "partkey"},
        {"partsupp.ps_partkey", "partkey"},
        {"lineitem.l_partkey", "partkey"},
        {"supplier.s_suppkey", "suppkey"},
        {"partsupp.ps_suppkey", "suppkey"},
        {"lineitem.l_suppkey", "suppkey"},
        {"nation.n_nationkey", "nationkey"},
        {"customer.c_nationkey", "nationkey"},
        {"supplier.s_nationkey", "nationkey"},
        {"region.r_regionkey", "regionkey"},
        {"nation.n_regionkey", "regionkey"}};
    return columns;
}

struct EmitStats {
    std::uint64_t indexes_built = 0;
    std::uint64_t indexes_reused = 0;
    std::uint64_t indexed_rows = 0;
    std::uint64_t bytes_written = 0;
};

void ensure_forward_index(const ArtifactIO& io,
                          const std::string& qualified,
                          const std::vector<std::uint8_t>& cix,
                          EmitStats& stats) {
    const auto [table, column] = split_qualified(qualified);
    if (cix.size() < 16U || std::memcmp(cix.data(), "CIX1", 4U) != 0) {
        fail("bad CIX1 while building forward index for " + qualified);
    }
    const std::uint32_t rank_count = u32le(cix.data() + 4U);
    const std::uint32_t nonnull_rows = u32le(cix.data() + 8U);
    const std::size_t offsets_bytes =
        (static_cast<std::size_t>(rank_count) + 1U) * 4U;
    const std::size_t rows_offset = 12U + offsets_bytes;
    const std::size_t rows_bytes = static_cast<std::size_t>(nonnull_rows) * 4U;
    if (rows_offset > cix.size() || rows_bytes > cix.size() - rows_offset) {
        fail("truncated CIX1 while building forward index for " + qualified);
    }
    const std::string output =
        "canon_fwdidx/" + table + "/" + column;
    const CodeBase base = load_code_base(io, table);
    std::vector<std::uint8_t> existing;
    if (io.try_read(output, existing)) {
        const std::size_t expected =
            16U + static_cast<std::size_t>(base.total_rows) * 4U;
        if (existing.size() != expected ||
            std::memcmp(existing.data(), "CFI1", 4U) != 0 ||
            u32le(existing.data() + 4U) != base.total_rows ||
            u32le(existing.data() + 8U) != rank_count) {
            fail("refusing to replace incompatible " + output);
        }
        return;
    }

    std::vector<std::uint8_t> bytes(
        16U + static_cast<std::size_t>(base.total_rows) * 4U, 0xffU);
    bytes[0] = 'C'; bytes[1] = 'F'; bytes[2] = 'I'; bytes[3] = '1';
    auto write_u32 = [&](std::size_t offset, std::uint32_t value) {
        bytes[offset] = static_cast<std::uint8_t>(value);
        bytes[offset + 1U] = static_cast<std::uint8_t>(value >> 8U);
        bytes[offset + 2U] = static_cast<std::uint8_t>(value >> 16U);
        bytes[offset + 3U] = static_cast<std::uint8_t>(value >> 24U);
    };
    write_u32(4U, base.total_rows);
    write_u32(8U, rank_count);
    write_u32(12U, 0U);
    const std::uint8_t* offsets = cix.data() + 12U;
    const std::uint8_t* child_rows = cix.data() + rows_offset;
    std::uint64_t assigned = 0;
    for (std::uint32_t rank = 0; rank < rank_count; ++rank) {
        const std::uint32_t begin =
            u32le(offsets + static_cast<std::size_t>(rank) * 4U);
        const std::uint32_t end =
            u32le(offsets + (static_cast<std::size_t>(rank) + 1U) * 4U);
        if (begin > end || end > nonnull_rows)
            fail("invalid CIX1 offsets for " + qualified);
        for (std::uint32_t cursor = begin; cursor < end; ++cursor) {
            const std::uint32_t row =
                u32le(child_rows + static_cast<std::size_t>(cursor) * 4U);
            if (row >= base.total_rows)
                fail("CIX1 row exceeds table for " + qualified);
            const std::size_t destination =
                16U + static_cast<std::size_t>(row) * 4U;
            if (u32le(bytes.data() + destination) != UINT32_MAX)
                fail("duplicate CIX1 row for " + qualified);
            write_u32(destination, rank);
            ++assigned;
        }
    }
    if (assigned != nonnull_rows)
        fail("forward-index scatter count mismatch for " + qualified);
    io.write(output, bytes);
    ++stats.indexes_built;
    stats.bytes_written += bytes.size();
}

void emit_one(const ArtifactIO& io,
              const std::string& qualified,
              const std::string& domain_text,
              const std::vector<std::uint32_t>& canonical_tokens,
              EmitStats& stats) {
    const auto [table, column] = split_qualified(qualified);
    const std::vector<std::uint8_t> ranks =
        io.read("rank/domain/" + domain_text);
    if (ranks.size() % sizeof(std::uint32_t) != 0) {
        fail("bad rank map for domain " + domain_text);
    }
    const std::size_t source_token_count = ranks.size() / 4U;
    const std::size_t rank_count = canonical_tokens.size();
    if (rank_count > UINT32_MAX) {
        fail("rank universe exceeds CIX1");
    }
    const std::string output =
        "canon_invidx/" + table + "/" + column;
    std::vector<std::uint8_t> existing;
    if (io.try_read(output, existing)) {
        if (existing.size() < 16U ||
            std::memcmp(existing.data(), "CIX1", 4U) != 0 ||
            u32le(existing.data() + 4U) != rank_count) {
            fail("refusing to replace incompatible " + output);
        }
        ensure_forward_index(io, qualified, existing, stats);
        ++stats.indexes_reused;
        return;
    }

    const std::size_t column_index =
        resolve_column_index(io, table, qualified);
    const CodeBase base = load_code_base(io, table);
    std::vector<std::uint32_t> canonical_by_token(
        source_token_count, UINT32_MAX);
    for (std::size_t canonical_rank = 0;
         canonical_rank < canonical_tokens.size(); ++canonical_rank) {
        const std::uint32_t token = canonical_tokens[canonical_rank];
        if (token >= source_token_count) {
            fail("canonical token exceeds source domain for " +
                 qualified);
        }
        canonical_by_token[token] =
            static_cast<std::uint32_t>(canonical_rank);
    }

    std::vector<std::uint32_t> counts(rank_count, 0);
    std::uint64_t nonnull = 0;
    scan_column(io, table, column_index, base,
        [&](std::uint32_t, std::uint32_t encoded) {
            if (encoded == 0) return;
            const std::uint32_t token = encoded - 1U;
            if (token >= source_token_count) {
                fail("token exceeds rank map for " + qualified);
            }
            const std::uint32_t rank = canonical_by_token[token];
            if (rank >= rank_count) {
                fail("column token absent from canonical universe for " +
                     qualified);
            }
            ++counts[rank];
            ++nonnull;
        });
    if (nonnull > UINT32_MAX) {
        fail("nonnull rows exceed CIX1 for " + qualified);
    }

    std::vector<std::uint32_t> offsets(rank_count + 1U, 0);
    std::vector<std::uint32_t> cursor(rank_count, 0);
    std::vector<std::uint32_t> present;
    std::uint32_t running = 0;
    for (std::size_t rank = 0; rank < rank_count; ++rank) {
        offsets[rank] = running;
        cursor[rank] = running;
        if (counts[rank] != 0) {
            present.push_back(static_cast<std::uint32_t>(rank));
        }
        running += counts[rank];
    }
    offsets[rank_count] = running;
    std::vector<std::uint32_t> child_rows(running);
    scan_column(io, table, column_index, base,
        [&](std::uint32_t row, std::uint32_t encoded) {
            if (encoded == 0) return;
            const std::uint32_t token = encoded - 1U;
            const std::uint32_t rank = canonical_by_token[token];
            child_rows[cursor[rank]++] = row;
        });

    std::vector<std::uint8_t> bytes;
    bytes.reserve(12U + offsets.size() * 4U +
                  child_rows.size() * 4U + 4U +
                  present.size() * 4U +
                  canonical_tokens.size() * 4U);
    bytes.insert(bytes.end(), {'C', 'I', 'X', '1'});
    append_u32(bytes, static_cast<std::uint32_t>(rank_count));
    append_u32(bytes, running);
    append_u32s(bytes, offsets);
    append_u32s(bytes, child_rows);
    append_u32(bytes, static_cast<std::uint32_t>(present.size()));
    append_u32s(bytes, present);
    append_u32s(bytes, canonical_tokens);
    io.write(output, bytes);
    ensure_forward_index(io, qualified, bytes, stats);

    ++stats.indexes_built;
    stats.indexed_rows += running;
    stats.bytes_written += bytes.size();
}

std::string manifest_body(
        const std::vector<std::pair<std::string, std::string>>& coverage) {
    std::string body =
        "format=CIX1\n"
        "coverage=column_inventory\n"
        "ranking=schema_keys_or_column_order\n";
    for (const auto& entry : coverage) {
        const auto key_found = schema_key_columns().find(entry.first);
        body += entry.first + "=" +
            (key_found == schema_key_columns().end() ?
                "column-order" :
                "schema-key:" + key_found->second) + "\n";
    }
    return body;
}

int run(ArtifactIO& io) {
    const auto domains = load_col_domains(io);
    std::vector<std::pair<std::string, std::string>> coverage(
        domains.begin(), domains.end());
    if (coverage.empty()) fail("column inventory is empty");

    std::map<std::string, std::vector<std::uint32_t>> key_tokens;
    for (const auto& entry : coverage) {
        const auto key_found = schema_key_columns().find(entry.first);
        if (key_found == schema_key_columns().end()) continue;
        const std::string key =
            key_found->second + ":" + entry.second;
        std::vector<std::uint32_t> tokens =
            collect_present_tokens(io, entry.first, entry.second);
        std::vector<std::uint32_t>& combined = key_tokens[key];
        combined.insert(combined.end(), tokens.begin(), tokens.end());
    }
    for (auto& entry : key_tokens) {
        std::vector<std::uint32_t>& tokens = entry.second;
        std::sort(tokens.begin(), tokens.end());
        tokens.erase(std::unique(tokens.begin(), tokens.end()),
                     tokens.end());
        const std::size_t colon = entry.first.rfind(':');
        const std::string domain = entry.first.substr(colon + 1U);
        const std::vector<std::uint8_t> ranks =
            io.read("rank/domain/" + domain);
        std::sort(tokens.begin(), tokens.end(),
            [&](std::uint32_t left, std::uint32_t right) {
                return u32le(ranks.data() +
                             static_cast<std::size_t>(left) * 4U) <
                       u32le(ranks.data() +
                             static_cast<std::size_t>(right) * 4U);
            });
    }

    EmitStats stats;
    for (const auto& entry : coverage) {
        const auto key_found = schema_key_columns().find(entry.first);
        if (key_found != schema_key_columns().end()) {
            const std::string key =
                key_found->second + ":" + entry.second;
            emit_one(io, entry.first, entry.second,
                     key_tokens.at(key), stats);
        } else {
            emit_one(io, entry.first, entry.second,
                     collect_present_tokens(
                         io, entry.first, entry.second), stats);
        }
    }

    std::vector<std::uint8_t> existing;
    if (!io.try_read("meta/canon_invidx", existing)) {
        const std::string body = manifest_body(coverage);
        io.write("meta/canon_invidx",
                 std::vector<std::uint8_t>(body.begin(), body.end()));
    }
    return static_cast<int>(stats.indexes_built);
}

}  // namespace

extern "C" int emit_invidx_run(
        void* context,
        emit_invidx_read_fn read,
        emit_invidx_write_fn write) {
    try {
        last_error.clear();
        ArtifactIO io(context, read, write);
        return run(io);
    } catch (const std::exception& error) {
        last_error = error.what();
        return -1;
    }
}

extern "C" const char* emit_invidx_last_error() {
    return last_error.c_str();
}
