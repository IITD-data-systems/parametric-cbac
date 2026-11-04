#include "policy_runtime_new.h"
#include "our_pg_uniform.h"
#include "exec_metrics.h"
#include "artifact_allowlist.h"

extern "C" {
#include "postgres.h"
#include "utils/builtins.h"
#include "utils/memutils.h"
}

#include <algorithm>
#include <array>
#include <cerrno>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <limits>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

struct PolicyRunHandleNew {
    PolicyAllowListCNew allow_list;
    PolicyRunProfileCNew profile;
};

namespace {

constexpr int kPolicyModeFilter = 0;
constexpr int kPolicyModeTid = 1;
constexpr int kPolicyModeEmpty = 2;
constexpr int kPolicyModeAll = 3;


constexpr std::uint64_t kTidDensityNumerator = 1;
constexpr std::uint64_t kTidDensityDenominator = 5;

constexpr std::size_t kWordsPerBlock = 8U;
constexpr std::uint32_t kMaxOffset = 512U;

[[noreturn]] void fail(const std::string &message) {
    ereport(ERROR, (errmsg("our_pg: %s", message.c_str())));
    std::abort();
}

std::uint32_t u32le(const unsigned char *p) {
    return static_cast<std::uint32_t>(p[0]) |
           (static_cast<std::uint32_t>(p[1]) << 8U) |
           (static_cast<std::uint32_t>(p[2]) << 16U) |
           (static_cast<std::uint32_t>(p[3]) << 24U);
}

struct ArtifactView {
    const unsigned char *data = nullptr;
    std::size_t len = 0;
};

ArtifactView lookup_required(const PolicyArtifactCNew *arts,
                             int art_count,
                             const PolicyEngineInputC *in,
                             const std::string &name) {
    if (!pac_artifact_name_allowed(name.c_str())) fail("Forbidden artifact: "+name);
    for (int i = 0; i < art_count; ++i) {
        if (arts != nullptr && arts[i].name != nullptr &&
            std::strcmp(arts[i].name, name.c_str()) == 0) {
            if (arts[i].data == nullptr && arts[i].len != 0U)
                fail("null artifact data for " + name);
            return {static_cast<const unsigned char *>(arts[i].data), arts[i].len};
        }
    }
    const void *data = nullptr;
    std::size_t len = 0;
    if (in == nullptr || in->artifact_lookup_fn == nullptr ||
        !in->artifact_lookup_fn(in->artifact_lookup_ctx, name.c_str(), &data, &len)) {
        fail("missing required artifact " + name);
    }
    if (data == nullptr && len != 0U)
        fail("artifact callback returned null data for " + name);
    return {static_cast<const unsigned char *>(data), len};
}

std::uint32_t total_rows_for_table(const PolicyArtifactCNew *arts,int art_count,
                                   const PolicyEngineInputC *in,const std::string &table) {
    const auto names=lookup_required(arts,art_count,in,"meta/cols/"+table);
    std::string first(reinterpret_cast<const char *>(names.data),names.len);
    first=first.substr(0,first.find_first_of("\r\n"));
    const auto dot=first.find('.');
    if (dot==std::string::npos || first.substr(0,dot)!=table)
        fail("Invalid column catalog for "+table);
    const auto forward=lookup_required(arts,art_count,in,"canon_fwdidx/"+table+"/"+first.substr(dot+1));
    if (forward.len<16U || std::memcmp(forward.data,"CFI2",4U)!=0)
        fail("Invalid rank-encoded column for "+table);
    const auto rows=u32le(forward.data+4U);
    if (forward.len!=16ULL+4ULL*rows) fail("CFI2 length mismatch for "+table);
    return rows;
}

using RowBits = std::vector<std::uint64_t>;

struct CtidPair {
    std::uint32_t block;
    std::uint32_t offset;
};

struct ConversionTimer {
    std::chrono::steady_clock::time_point started=std::chrono::steady_clock::now();
    ~ConversionTimer() {
        cf_perf_metric_set("conversion_ms",std::chrono::duration<double,std::milli>(
            std::chrono::steady_clock::now()-started).count());
    }
};

// Converts the walk result into the CTID bitmap used by PostgreSQL.
void build_allow_item(const PolicyArtifactCNew *arts,
                      int art_count,
                      const PolicyEngineInputC *in,
                      int target_index,
                      PolicyTableAllowCNew *item) {
    if (in->target_tables == nullptr || in->target_tables[target_index] == nullptr)
        fail("missing target table name");
    const std::string target(in->target_tables[target_index]);
    const std::uint32_t total_rows =
        total_rows_for_table(arts, art_count, in, target);
    const RowBits allowed = our_pg_evaluate_target(
        arts, art_count, in, target_index, target, total_rows);
    // Declared before conversion buffers, so their release is included too.
    const ConversionTimer conversion_timer;
    const std::string ctid_name = target + "_ctid";
    const ArtifactView ctid_view =
        lookup_required(arts, art_count, in, ctid_name);
    if (ctid_view.len != static_cast<std::size_t>(total_rows) * 8U)
        fail("CTID artifact length mismatch for " + ctid_name);
    std::vector<std::uint32_t> block_ids;
    std::vector<std::uint64_t> block_words;
    std::uint32_t total_blocks = 0;
    std::uint64_t allowed_rows = 0;
    std::uint32_t previous_block = 0;
    bool have_previous = false;
    if (total_rows != 0U) {
        const unsigned char *last = ctid_view.data +
            static_cast<std::size_t>(total_rows - 1U) * 8U;
        const CtidPair final_ctid{u32le(last), u32le(last + 4U)};
        if (final_ctid.offset == 0U || final_ctid.offset > kMaxOffset)
            fail("final CTID offset out of range for " + ctid_name);
        total_blocks = final_ctid.block + 1U;
    }
    
    for (std::size_t word_index = 0; word_index < allowed.size(); ++word_index) {
        std::uint64_t word = allowed[word_index];
        while (word != 0U) {
            const unsigned bit = static_cast<unsigned>(__builtin_ctzll(word));
            const std::uint64_t row64 = word_index * 64U + bit;
            word &= word - 1U;
            if (row64 >= total_rows) continue;
            const std::uint32_t row = static_cast<std::uint32_t>(row64);
            const unsigned char *encoded =
                ctid_view.data + static_cast<std::size_t>(row) * 8U;
            const CtidPair ctid{u32le(encoded), u32le(encoded + 4U)};
            if (ctid.offset == 0U || ctid.offset > kMaxOffset)
                fail("CTID offset out of range for " + ctid_name);
            if (have_previous && ctid.block < previous_block)
                fail("CTID artifact is not block ordered for " + ctid_name);
            previous_block = ctid.block;
            have_previous = true;
            if (block_ids.empty() || block_ids.back() != ctid.block) {
                block_ids.push_back(ctid.block);
                block_words.insert(block_words.end(), kWordsPerBlock, 0U);
            }
            const std::uint32_t off0 = ctid.offset - 1U;
            const std::uint64_t mask = std::uint64_t{1} << (off0 & 63U);
            std::uint64_t &output_word =
                block_words[(block_ids.size() - 1U) * kWordsPerBlock + (off0 >> 6U)];
            if ((output_word & mask) == 0U) {
                output_word |= mask;
                ++allowed_rows;
            }
        }
    }
    item->table = pstrdup(target.c_str());
    item->blocks = static_cast<std::uint32_t>(block_ids.size());
    item->total_blocks = total_blocks;
    item->n_rows = total_rows;
    item->allowed_rows = allowed_rows;
    // This is the complete bundle result, independent of the local heap CTIDs.
    cf_perf_metric_set("allowed_rows",static_cast<double>(allowed_rows));
    item->allowed_sids = static_cast<std::uint32_t>(
        std::min<std::uint64_t>(allowed_rows, std::numeric_limits<std::uint32_t>::max()));
    item->total_sids = total_rows;
    if (allowed_rows == 0U) {
        item->mode_hint = kPolicyModeEmpty;
        item->mode_reason = pstrdup("our_pg_empty");
    } else if (allowed_rows == total_rows) {
        item->mode_hint = kPolicyModeAll;
        item->mode_reason = pstrdup("our_pg_all");
    } else if (allowed_rows <=
               (static_cast<std::uint64_t>(total_rows) * kTidDensityNumerator) /
                   kTidDensityDenominator) {
        item->mode_hint = kPolicyModeTid;
        item->mode_reason = pstrdup("our_pg_sparse_tid");
    } else {
        item->mode_hint = kPolicyModeFilter;
        item->mode_reason = pstrdup("our_pg_dense_filter");
    }
    if (!block_ids.empty()) {
        item->block_ids = static_cast<std::uint32_t *>(
            MemoryContextAllocExtended(CurrentMemoryContext,block_ids.size() * sizeof(std::uint32_t),MCXT_ALLOC_HUGE));
        std::memcpy(item->block_ids, block_ids.data(),
                    block_ids.size() * sizeof(std::uint32_t));
        item->block_words = static_cast<std::uint64_t *>(
            MemoryContextAllocExtended(CurrentMemoryContext,block_words.size() * sizeof(std::uint64_t),MCXT_ALLOC_HUGE));
        std::memcpy(item->block_words, block_words.data(),
                    block_words.size() * sizeof(std::uint64_t));
    }
}

}

// Runs the PAC walk for each target requested by PostgreSQL.
extern "C" PolicyRunHandleNew *our_pg_run(const PolicyArtifactCNew *arts,
                                           int art_count,
                                           const PolicyEngineInputC *in) {
    if (in == nullptr) fail("NULL PolicyEngineInputC");
    const auto start = std::chrono::steady_clock::now();
    PolicyRunHandleNew *handle = static_cast<PolicyRunHandleNew *>(
        palloc0(sizeof(PolicyRunHandleNew)));
    handle->allow_list.count = in->target_count;
    handle->allow_list.items = in->target_count > 0
        ? static_cast<PolicyTableAllowCNew *>(
              palloc0(sizeof(PolicyTableAllowCNew) * static_cast<std::size_t>(in->target_count)))
        : nullptr;
    for (int i = 0; i < in->target_count; ++i)
        build_allow_item(arts, art_count, in, i, &handle->allow_list.items[i]);
    handle->profile.policy_total_ms =
        std::chrono::duration<double, std::milli>(
            std::chrono::steady_clock::now() - start).count();
    handle->profile.project_allowset_ms = handle->profile.policy_total_ms;
    return handle;
}

extern "C" PolicyRunHandleNew *policy_run_new(
    const PolicyArtifactCNew *arts,
    int art_count,
    const PolicyEngineInputC *in) {
    return our_pg_run(arts, art_count, in);
}

extern "C" const PolicyAllowListCNew *policy_run_allow_list_new(
    const PolicyRunHandleNew *handle) {
    return handle ? &handle->allow_list : nullptr;
}

extern "C" const PolicyRunProfileCNew *policy_run_profile_new(
    const PolicyRunHandleNew *handle) {
    return handle ? &handle->profile : nullptr;
}
