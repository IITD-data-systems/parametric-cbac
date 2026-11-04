#ifndef _GNU_SOURCE
#define _GNU_SOURCE 1
#endif

#include "postgres.h"
#include "fmgr.h"

#include <float.h>     
#include <ctype.h>
#include <stdint.h>
#include <stddef.h>
#include <string.h>
#include "artifact_allowlist.h"
#include <stdio.h>
#include <sys/stat.h>
#include <sys/resource.h>
#include <unistd.h>
#include <sys/mman.h>
#include <fcntl.h>
#include <errno.h>
#ifdef __linux__
#include <sched.h>
#endif

#include "optimizer/paths.h"      
#include "optimizer/planner.h"
#include "optimizer/restrictinfo.h"
#include "nodes/extensible.h"      
#include "nodes/pathnodes.h"       
#include "nodes/plannodes.h"       
#include "nodes/makefuncs.h"
#include "executor/executor.h"     
#include "executor/tuptable.h"     
#include "commands/explain.h"      
#include "portability/instr_time.h"
#include "utils/guc.h"            
#include "nodes/bitmapset.h"
#include "parser/parsetree.h"
#include "executor/spi.h"
#include "utils/builtins.h"
#include "miscadmin.h"
#include "catalog/pg_type.h"
#include "catalog/namespace.h"
#include "access/htup_details.h"   
#include "access/htup.h"
#include "access/table.h"
#include "access/tableam.h"
#include "storage/itemptr.h"      
#include "utils/memutils.h"       
#include "utils/rel.h"
#include "utils/lsyscache.h"
#include "lib/stringinfo.h"
#include "nodes/nodeFuncs.h"
#include "nodes/pg_list.h"
#include "nodes/primnodes.h"
#include "utils/hsearch.h"
#include "utils/array.h"
#include "storage/fd.h"
#include "utils/wait_event.h"
#include "common/md5.h"
#include "parser/parse_oper.h"

#include "policy_evaluator.h"
extern double our_pg_release_runtime(void);
#include "policy_runtime_new.h"
#include "policy_spec.h"
#include "tcop/utility.h"
#include "exec_metrics.h"
extern void our_pg_preload_artifacts(const PolicyEngineInputC *in);
PG_MODULE_MAGIC;


struct CfExec;
typedef struct TableFilterState TableFilterState;
typedef struct PolicyQueryState PolicyQueryState;

typedef enum CfScanMode
{
    CF_SCAN_MODE_FILTER = 0,
    CF_SCAN_MODE_TID = 1,
    CF_SCAN_MODE_EMPTY = 2,
    CF_SCAN_MODE_ALL = 3
} CfScanMode;

typedef enum PolicyModeHint
{
    POLICY_MODE_HINT_FILTER = 0,
    POLICY_MODE_HINT_TID = 1,
    POLICY_MODE_HINT_EMPTY = 2,
    POLICY_MODE_HINT_ALL = 3
} PolicyModeHint;

typedef struct TableFilterState TableFilterState;


#define CF_MAX_OFF 512u
#define CF_WORDS_PER_BLOCK ((CF_MAX_OFF + 63u) / 64u)

static inline bool
cf_allowed_ctid_words(const uint64 *words, const uint32 *block_ids, uint32 blocks, uint32 total_blocks, BlockNumber blk, OffsetNumber off)
{
    uint32 blk_u;
    uint32 off_u;
    uint32 off0;
    size_t word_idx;
    size_t flat;
    uint64 mask;

    if (!words || blocks == 0)
        return false;
    blk_u = (uint32) blk;
    if (block_ids) {
        uint32 lo = 0, hi = blocks;
        while (lo < hi) {
            uint32 mid = lo + (hi - lo) / 2u;
            uint32 v = block_ids[mid];
            if (v < blk_u)
                lo = mid + 1u;
            else
                hi = mid;
        }
        if (lo >= blocks || block_ids[lo] != blk_u)
            return false;
        blk_u = lo;
    } else {
        if (blk_u >= blocks)
            return false;
    }
    if (total_blocks > 0 && blk_u >= total_blocks && !block_ids)
        return false;
    if (off < 1)
        return false;
    off_u = (uint32) off;
    if (off_u > CF_MAX_OFF)
        return false;

    off0 = off_u - 1u;
    word_idx = (size_t) (off0 >> 6);
    flat = (size_t) blk_u * (size_t) CF_WORDS_PER_BLOCK + word_idx;
    mask = 1ULL << (off0 & 63u);
    return (words[flat] & mask) != 0;
}

static inline const uint64 *
cf_lookup_block_words(const uint64 *words,
                      const uint32 *block_ids,
                      uint32 blocks,
                      uint32 total_blocks,
                      BlockNumber blk)
{
    if (!words || blocks == 0)
        return NULL;
    uint32 blk_u = (uint32) blk;
    if (block_ids)
    {
        uint32 lo = 0, hi = blocks;
        while (lo < hi)
        {
            uint32 mid = lo + (hi - lo) / 2u;
            uint32 v = block_ids[mid];
            if (v < blk_u)
                lo = mid + 1u;
            else
                hi = mid;
        }
        if (lo >= blocks || block_ids[lo] != blk_u)
            return NULL;
        return words + (size_t) lo * (size_t) CF_WORDS_PER_BLOCK;
    }
    if (blk_u >= blocks)
        return NULL;
    if (total_blocks > 0 && blk_u >= total_blocks)
        return NULL;
    return words + (size_t) blk_u * (size_t) CF_WORDS_PER_BLOCK;
}

#define CF_TRACE_LOG(fmt, ...) \
    do { \
        if (cf_trace_enabled()) \
            CF_METRICS_LOG(NOTICE, fmt, ##__VA_ARGS__); \
    } while (0)

#define CF_RESCAN_LOG(fmt, ...) \
    do { \
        if (cf_profile_rescan) \
            CF_METRICS_LOG(NOTICE, "rescan_profile: " fmt, ##__VA_ARGS__); \
    } while (0)

#define CF_DEBUG_IDS_LOG(fmt, ...) \
    do { \
        if (cf_debug_ids) \
            CF_METRICS_LOG(NOTICE, "CF_ID " fmt, ##__VA_ARGS__); \
    } while (0)

#define CF_DEBUG_QS_LOG(fmt, ...) \
    do { \
        if (cf_debug_ids) \
            CF_METRICS_LOG(NOTICE, "CF_QS " fmt, ##__VA_ARGS__); \
    } while (0)

#define CF_DEBUG_SUBPLAN_LOG(fmt, ...) \
    do { \
        if (cf_debug_ids) \
            CF_METRICS_LOG(NOTICE, "CF_SUBPLAN " fmt, ##__VA_ARGS__); \
    } while (0)

static uint64
cf_popcount_block_words(const uint64 *words, uint32 blocks)
{
    uint64 cnt = 0;
    if (!words || blocks == 0)
        return 0;
    size_t nwords = (size_t) blocks * (size_t) CF_WORDS_PER_BLOCK;
    for (size_t i = 0; i < nwords; i++)
        cnt += (uint64) __builtin_popcountll((unsigned long long) words[i]);
    return cnt;
}

static inline void
cf_periodic_interrupt_check(uint64 *counter)
{
    if (counter == NULL)
    {
        CHECK_FOR_INTERRUPTS();
        return;
    }
    (*counter)++;
    if (((*counter) & 0x3FFFULL) == 0ULL)
        CHECK_FOR_INTERRUPTS();
}

static long
cf_rss_kb_now(void)
{
    FILE *f = fopen("/proc/self/status", "r");
    if (!f)
        return -1;
    char line[256];
    long kb = -1;
    while (fgets(line, sizeof(line), f))
    {
        if (strncmp(line, "VmRSS:", 6) == 0)
        {
            char *p = line + 6;
            while (*p && (*p < '0' || *p > '9'))
                p++;
            kb = atol(p);
            break;
        }
    }
    fclose(f);
    return kb;
}

static long
cf_peak_rss_kb(void)
{
    struct rusage ru;
    if (getrusage(RUSAGE_SELF, &ru) != 0)
        return -1;
    return (long) ru.ru_maxrss;
}

static bool
cf_memory_context_contains(MemoryContext parent, MemoryContext child)
{
    for (MemoryContext cur = child; cur != NULL; cur = cur->parent)
    {
        if (cur == parent)
            return true;
    }
    return false;
}

static void
cf_contract_assert_chunk(const char *label, const char *relname, void *ptr, MemoryContext qctx)
{
    if (!ptr || !qctx)
        return;
    MemoryContext mctx = GetMemoryChunkContext(ptr);
    bool ok = cf_memory_context_contains(qctx, mctx);
    CF_TRACE_LOG(
         "custom_filter_new: memctx label=%s rel=%s ptr=%p mctx=%p qctx=%p ok=%s",
         label ? label : "<null>",
         relname ? relname : "<global>",
         ptr,
         (void *) mctx,
         (void *) qctx,
         ok ? "true" : "false");
    if (!ok)
        ereport(ERROR,
                (errmsg("custom_filter_new[memctx_violation]: allocation escaped query context (label=%s rel=%s)",
                        label ? label : "<null>",
                        relname ? relname : "<global>")));
}

bool cf_enabled = false;
bool cf_diagnostic_logging = false;
bool cf_cost_single_visit = true;
bool cf_cost_branch_order = true;
bool cf_cost_present_caps = true;
bool cf_cost_dense_budget = true;
bool cf_cost_hop_elision = true;
bool cf_cost_target_fraction = true;
bool cf_cost_group_maps = true;
bool cf_block_target_loop = true;
bool cf_composed_reuse = true;
bool cf_run_reuse = true;
bool cf_decision_sharing = true;
bool cf_posting_position_store = true;
bool cf_composed_bounds = true;
int cf_block_target_rows = 1024;
static bool cf_chunked_artifacts=false;
static char *cf_artifact_directory=NULL;
int cf_cost_dense_budget_mb = 2048;

/* Read after the query; no diagnostic output is needed inside its timer. */
#define CF_TIGHT_BRANCH_METRICS(n) \
    {"tight_branch_order_" #n, -1}, {"tight_branch_cost_" #n, -1}, \
    {"tight_branch_single_visit_" #n, -1}, {"tight_branch_probes_" #n, -1}, \
    {"tight_branch_writes_" #n, -1}, {"tight_branch_block_" #n, -1}, \
    {"tight_branch_cache_cells_" #n, -1}, {"tight_branch_cache_bytes_" #n, -1}, \
    {"tight_branch_run_sampled_" #n, -1}, {"tight_branch_run_repeats_" #n, -1}, \
    {"tight_branch_run_disabled_" #n, -1}
static struct {
    const char *name;
    double value;
} cf_perf_metrics[] = {
    {"posting_position_plans", -1}, {"posting_position_calls", -1},
    {"posting_position_scan_rows", -1}, {"posting_position_unique", -1},
    {"posting_position_multiple_fallbacks", -1}, {"posting_position_empty", -1},
    {"posting_position_hits", -1}, {"posting_position_writes", -1},
    {"posting_position_unsafe_context", -1}, {"posting_position_tail_evals", -1},
    {"posting_position_bytes", -1}, {"posting_position_profile_samples", -1},
    {"posting_position_sample_scan_ms", -1}, {"posting_position_sample_cell_ms", -1},
    {"posting_position_sample_tail_ms", -1},
    {"composed_bounds_used", -1}, {"bound_probes", -1}, {"bound_hits", -1},
    {"bound_fills", -1}, {"bound_first_rows", -1}, {"bound_position_scans", -1},
    {"bound_slot_checks", -1}, {"collective_record_probes", -1},
    {"collective_slot_checks", -1}, {"collective_input_reads", -1},
    {"bound_position_rows", -1}, {"bound_connection_hits", -1}, {"bound_fallbacks", -1},
    {"bound_target_rows", -1}, {"bound_build_inclusive_ms", -1}, {"bound_bytes", -1},
    {"shared_bound_graph_used", -1}, {"shared_bound_root_target_filter_decisions", -1},
    {"shared_bound_should_nodes", -1}, {"shared_bound_private_or_drivers", -1},
    {"functional_composed_program_used", -1}, {"shared_request_frame_visits", -1},
    {"shared_live_checks", -1}, {"shared_formula_visits", -1}, {"shared_child_route_checks", -1},
    {"composed_probes", -1}, {"composed_misses", -1}, {"composed_bytes", -1},
    {"composed_decisions", -1}, {"composed_decision_hits", -1},
    {"run_count", -1}, {"run_reused_rows", -1}, {"run_entering_columns", -1},
    {"run_rows_saved", -1},
    {"nested_quantifier_calls", -1}, {"nested_maximum_depth", -1},
    {"nested_unique_hops", -1}, {"nested_kept_hits", -1},
    {"nested_first_witness_stops", -1}, {"nested_exhaustions", -1},
    {"nested_tight_slice_rows", -1}, {"nested_formula_instructions", -1},
    {"nested_block_words", -1},
    {"nested_dense_decisions", -1},
    {"nested_envelope_should_apply", -1}, {"nested_envelope_probes", -1},
    {"nested_envelope_hits", -1}, {"nested_envelope_fills", -1},
    {"nested_envelope_declined", -1}, {"nested_envelope_invalidated", -1},
    {"kept_miss_path_probes", -1}, {"outside_kept_path_probes", -1},
    {"kept_hit_path_probes", -1}, {"kept_hit_checked_rows", -1},
    {"block_loop_used", -1}, {"block_target_rows", -1},
    {"nested_formula_path_used", -1},
    {"block_branch_arrivals", -1}, {"block_cell_arrivals", -1}, {"block_scalar_arrivals", -1},
    {"block_rows_scalar", -1}, {"block_rows_cells", -1}, {"block_rows_filter_only", -1},
    {"exec_ms", -1}, {"exec_start_us", -1}, {"exec_stop_us", -1},
    {"artifact_mapping_ms", -1}, {"policy_input_ms", -1}, {"artifact_discovery_input_ms", -1},
    {"engine_setup_ms", -1}, {"dag_ms", -1}, {"terminals_ms", -1},
    {"runtime_cleanup_ms", -1}, {"engine_target_wall_ms", -1},
    {"conversion_ms", -1}, {"teardown_ms", -1},
    {"universe_decode_ms", -1}, {"rank_remap_ms", -1}, {"theta_transfer_bytes", -1},
    {"target_driver_ms", -1}, {"policy_run_wall_ms", -1}, {"allow_build_ms", -1},
    {"store_bytes", -1}, {"decisions_stored", -1}, {"hits_good", -1},
    {"hits_nogood", -1}, {"witness_tuples_read", -1},
    {"composite_build_ms", -1}, {"interval_build_ms", -1},
    {"composite_connections", -1}, {"composite_lookups", -1},
    {"interval_lookups", -1}, {"online_build_tuples", -1},
    {"direction_mode", -1}, {"direction_candidates", -1},
    {"rows_read_before_first_target", -1},
    {"projection_build_ms", -1}, {"projection_branches", -1},
    {"projection_null_entries", -1}, {"tight_loop_null_slow_arrivals", -1}, {"tight_loop_null_hits", -1},
    {"projection_full_branches", -1}, {"projection_partial_branches", -1},
    {"functional_tuple_hops", -1}, {"direct_residual_arrivals", -1},
    {"projected_hash_arrivals", -1}, {"projected_hash_misses", -1},
    {"projection_hits_good", -1}, {"projection_hits_nogood", -1},
    {"bound_record_skips", -1},
    {"bound_record_refusals", -1},
    {"chain_boundary_build_ms", -1}, {"chain_boundary_hits", -1},
    {"chain_boundary_misses", -1}, {"composite_decision_hits", -1},
    {"composite_decision_misses", -1}, {"composite_connections_rejected", -1},
    {"walk_ms", -1}, {"walk_exclusive_ms", -1}, {"bitmap_mark_ms", -1}, {"decision_lookup_ms", -1},
    {"profiled", -1}, {"target_evals", -1}, {"allowed_rows", -1}, {"composite_probe_ns_per_target", -1},
    {"composite_probe_ms", -1}, {"rank_order_build_ms", -1}, {"rank_order_used", -1},
    {"setup_exclusive_ms", -1}, {"online_build_ms", -1},
    {"tight_loop_used", -1}, {"tight_loop_build_ms", -1}, {"tight_loop_ms", -1},
    {"global_window_complete_blocks", 0},
    {"tight_loop_ns_per_row", -1}, {"tight_loop_slow_arrivals", -1},
    {"tight_loop_inline_misses", -1}, {"tight_loop_tuple_hits", -1},
    {"tight_loop_tuple_misses", -1},
    {"boundary_component_splits", -1}, {"formula_rank_cache_used", -1},
    {"formula_rank_hits_good", -1}, {"formula_rank_hits_nogood", -1},
    {"formula_rank_misses", -1}, {"formula_rank_entries", -1},
    {"branch_rank_entries", -1}, {"branch_rank_hits_good", -1},
    {"branch_rank_hits_nogood", -1}, {"branch_rank_empty_stops", -1},
    {"tight_single_visit_arrivals", -1},
    {"dense_budget_bytes", -1}, {"dense_budget_reserved_bytes", -1},
    {"dense_budget_rejections", -1},
    CF_TIGHT_BRANCH_METRICS(0), CF_TIGHT_BRANCH_METRICS(1),
    CF_TIGHT_BRANCH_METRICS(2), CF_TIGHT_BRANCH_METRICS(3),
    CF_TIGHT_BRANCH_METRICS(4), CF_TIGHT_BRANCH_METRICS(5),
    CF_TIGHT_BRANCH_METRICS(6), CF_TIGHT_BRANCH_METRICS(7),
    CF_TIGHT_BRANCH_METRICS(8), CF_TIGHT_BRANCH_METRICS(9),
    CF_TIGHT_BRANCH_METRICS(10), CF_TIGHT_BRANCH_METRICS(11),
    {"grouped_request_calls", -1}, {"grouped_shared_postings", -1},
    {"grouped_shared_rows", -1}, {"grouped_boundary_fills", -1},
    {"grouped_per_leaf_rows", -1},
    {"scoped_quantifier_path_used", -1},
    {"nested_scope_splits", -1}, {"nested_split_components", -1},
    {"nested_exact_probes", -1}, {"nested_exact_fills", -1}, {"nested_exact_hits", -1},
    {"nested_outer_dependency_declines", -1},
    {"nested_coequal_checks", -1}, {"nested_coequal_rejections", -1},
    {"nested_prefix_context_elisions", -1}, {"nested_functional_context_elisions", -1},
    {"nested_formula_updates", -1}, {"nested_request_arrivals", -1}, {"nested_request_decisions", -1},
    {"nested_compiled_target_used", -1}, {"nested_compiled_rows", -1}, {"nested_compiled_parts", -1},
    {"nested_compiled_fallbacks", -1}, {"nested_compiled_table_probes", -1}, {"nested_hash_decisions", -1},
    {"nested_dense_probes", -1}, {"nested_dense_hits", -1}, {"nested_dense_fills", -1},
    {"nested_packed_probes", -1}, {"nested_packed_hits", -1}, {"nested_packed_fills", -1},
    {"nested_word_hop_probes", -1},
    {"nested_word_hop_hits", -1},
    {"nested_word_hop_fills", -1},
    {"nested_partial_nogood_probes", -1},
    {"nested_partial_nogood_hits", -1},
    {"nested_partial_nogood_fills", -1},
    {"nested_bits_settled_without_read", -1},
    {"nested_rows_skipped", -1},
    {"nested_word_budget_declines", -1},
    {"nested_word_envelope_probes", -1},
    {"nested_word_envelope_hits", -1},
    {"nested_word_envelope_fills", -1},
    {"nested_word_envelope_pieces", -1},
    {"nested_word_envelope_bytes", -1},
    {"nested_gate_bypasses", -1}, {"nested_no_repeat_gates_off", -1}
};
#undef CF_TIGHT_BRANCH_METRICS

void
cf_perf_metric_set(const char *name, double value)
{
    for (size_t i = 0; i < lengthof(cf_perf_metrics); ++i)
        if (strcmp(name, cf_perf_metrics[i].name) == 0) {
            cf_perf_metrics[i].value = value;
            return;
        }
    ereport(ERROR, (errmsg("unknown PAC timing metric: %s", name)));
}

/* GUC's default six-digit display would round the absolute timestamps. */
static const char *cf_perf_show_exec(void) {
    static char text[64]; snprintf(text, sizeof(text), "%.17g", cf_perf_metrics[0].value); return text;
}
static const char *cf_perf_show_start(void) {
    static char text[64]; snprintf(text, sizeof(text), "%.17g", cf_perf_metrics[1].value); return text;
}
static const char *cf_perf_show_stop(void) {
    static char text[64]; snprintf(text, sizeof(text), "%.17g", cf_perf_metrics[2].value); return text;
}
static char *cf_perf_json_setting = NULL;
static char *cf_cost_plan_setting = NULL;
void cf_perf_cost_plan_set(const char *json) {
    SetConfigOption("custom_filter_new.last_cost_plan",json,PGC_INTERNAL,PGC_S_SESSION);
}
static const char *cf_perf_show_json(void) {
    StringInfoData text;
    initStringInfo(&text);
    appendStringInfoChar(&text, '{');
    for (size_t i = 0; i < lengthof(cf_perf_metrics); ++i)
        appendStringInfo(&text, "%s\"%s\":%.17g", i ? "," : "", cf_perf_metrics[i].name, cf_perf_metrics[i].value);
    appendStringInfoChar(&text, '}');
    return text.data;
}

int cf_decision_store = 1;
bool cf_composite_edges = true;
bool cf_interval_edges = true;
bool cf_chain_projection = true;
bool cf_chain_boundaries = true;
bool cf_composite_cost = true;
bool cf_engine_profile = false;
bool cf_tight_loop = true;
bool cf_component_boundaries = true;
bool cf_nested_theta_transfer = true;
bool cf_nested_equality_ranges = true;
bool cf_formula_rank_cache = true;
int cf_direction = 0;
bool cf_rankstore_dump = false;
static int cf_debug_mode = 0;

static int cf_cpu = -1;
static bool cf_debug_ids = false;
static char *cf_policy_path = NULL;
static char *cf_policy_template_path = NULL;
static char *cf_policy_binding_path = NULL;
static char *cf_query_path = NULL;
static char *cf_query_id = NULL;
static int cf_profile_k = 0;
static char *cf_profile_query = NULL;
static int cf_class_phase_limit = 0;
static int cf_class_phase_timeout_ms = 20000;
static int cf_runtime_path = POLICY_RUNTIME_PATH_WALK;
static bool cf_profile_rescan = false;
static bool cf_tidscan_seqscan = true;
static double cf_tidscan_density_threshold = 0.20;

bool
cf_trace_enabled(void)
{
    return cf_diagnostic_logging && cf_debug_mode == 2;
}

bool
cf_debug_enabled(void)
{
    return cf_diagnostic_logging && cf_debug_mode != 0;
}

bool
cf_contract_enabled(void)
{
    return cf_debug_mode == 1;
}

static void
cf_pin_backend_to_single_cpu(void)
{
#ifdef __linux__
    static bool attempted = false;
    cpu_set_t allowed_mask;
    cpu_set_t pin_mask;
    int chosen_cpu = -1;

    if (attempted)
        return;
    attempted = true;

    CPU_ZERO(&allowed_mask);
    if (sched_getaffinity(0, sizeof(allowed_mask), &allowed_mask) != 0)
    {
        int saved_errno = errno;
        if (cf_contract_enabled())
            elog(WARNING,
                 "custom_filter_new: failed to read backend CPU affinity: %s",
                 strerror(saved_errno));
        return;
    }

    if (cf_cpu >= 0 && cf_cpu < CPU_SETSIZE &&
        CPU_ISSET(cf_cpu, &allowed_mask))
        chosen_cpu = cf_cpu;

    for (int cpu = 0; chosen_cpu < 0 && cpu < CPU_SETSIZE; cpu++)
    {
        if (CPU_ISSET(cpu, &allowed_mask))
        {
            chosen_cpu = cpu;
            break;
        }
    }
    if (chosen_cpu < 0)
    {
        if (cf_contract_enabled())
            elog(WARNING,
                 "custom_filter_new: backend CPU affinity mask is empty; cannot pin single core");
        return;
    }

    CPU_ZERO(&pin_mask);
    CPU_SET(chosen_cpu, &pin_mask);
    if (sched_setaffinity(0, sizeof(pin_mask), &pin_mask) != 0)
    {
        int saved_errno = errno;
        if (cf_contract_enabled())
            elog(WARNING,
                 "custom_filter_new: failed to pin backend to CPU %d: %s",
                 chosen_cpu,
                 strerror(saved_errno));
        return;
    }

    CF_TRACE_LOG("custom_filter_new: pinned backend pid=%d to cpu=%d",
                 (int) getpid(),
                 chosen_cpu);
#else
    return;
#endif
}

static const char *
cf_template_policy_path(void)
{
    if (cf_policy_template_path && cf_policy_template_path[0] != '\0')
        return cf_policy_template_path;
    return cf_policy_path;
}

typedef struct CfBoundPolicyCache
{
    char *template_path;
    char *binding_path;
    char *query_path;
    char *query_id;
    char *query_sql;
    char *bound_text;
} CfBoundPolicyCache;

static CfBoundPolicyCache cf_bound_policy_cache = {0};
static const char *cf_planner_query_string = NULL;

static bool
cf_binding_contract_enabled(void)
{
    return cf_template_policy_path() && cf_template_policy_path()[0] != '\0' &&
           cf_policy_binding_path && cf_policy_binding_path[0] != '\0' &&
           cf_query_path && cf_query_path[0] != '\0';
}

static void
cf_bound_policy_cache_reset(void)
{
    if (cf_bound_policy_cache.template_path)
        pfree(cf_bound_policy_cache.template_path);
    if (cf_bound_policy_cache.binding_path)
        pfree(cf_bound_policy_cache.binding_path);
    if (cf_bound_policy_cache.query_path)
        pfree(cf_bound_policy_cache.query_path);
    if (cf_bound_policy_cache.query_id)
        pfree(cf_bound_policy_cache.query_id);
    if (cf_bound_policy_cache.query_sql)
        pfree(cf_bound_policy_cache.query_sql);
    if (cf_bound_policy_cache.bound_text)
        pfree(cf_bound_policy_cache.bound_text);
    memset(&cf_bound_policy_cache, 0, sizeof(cf_bound_policy_cache));
}

static const char *
cf_get_bound_policy_text(const char *query_sql)
{
    const char *template_path = cf_template_policy_path();
    const char *binding_path = cf_policy_binding_path;
    const char *query_path = cf_query_path;
    const char *query_id = (cf_query_id && cf_query_id[0]) ? cf_query_id : "";

    if (!template_path || !template_path[0] ||
        !binding_path || !binding_path[0] ||
        !query_path || !query_path[0] ||
        !query_sql || !query_sql[0])
        return NULL;

    if (cf_bound_policy_cache.bound_text &&
        cf_bound_policy_cache.template_path &&
        cf_bound_policy_cache.binding_path &&
        cf_bound_policy_cache.query_path &&
        cf_bound_policy_cache.query_id &&
        cf_bound_policy_cache.query_sql &&
        strcmp(cf_bound_policy_cache.template_path, template_path) == 0 &&
        strcmp(cf_bound_policy_cache.binding_path, binding_path) == 0 &&
        strcmp(cf_bound_policy_cache.query_path, query_path) == 0 &&
        strcmp(cf_bound_policy_cache.query_id, query_id) == 0 &&
        strcmp(cf_bound_policy_cache.query_sql, query_sql) == 0)
        return cf_bound_policy_cache.bound_text;

    /* The cache survives SQL statements, so its allocations must too. */
    MemoryContext cache_oldctx = MemoryContextSwitchTo(TopMemoryContext);
    char *bound_text = bind_policy_template_for_query(template_path,
                                                      binding_path,
                                                      query_path,
                                                      query_id,
                                                      query_sql);
    if (!bound_text || !bound_text[0])
    {
        MemoryContextSwitchTo(cache_oldctx);
        return NULL;
    }

    cf_bound_policy_cache_reset();
    cf_bound_policy_cache.template_path = pstrdup(template_path);
    cf_bound_policy_cache.binding_path = pstrdup(binding_path);
    cf_bound_policy_cache.query_path = pstrdup(query_path);
    cf_bound_policy_cache.query_id = pstrdup(query_id);
    cf_bound_policy_cache.query_sql = pstrdup(query_sql);
    cf_bound_policy_cache.bound_text = bound_text;
    MemoryContextSwitchTo(cache_oldctx);
    return cf_bound_policy_cache.bound_text;
}

static const char *
cf_current_policy_query_sql(void)
{
    if (cf_planner_query_string && cf_planner_query_string[0] != '\0')
        return cf_planner_query_string;
    return debug_query_string;
}

static char *
cf_read_policy_text_file(const char *path, MemoryContext mcxt)
{
    if (!path || !path[0] || !mcxt)
        return NULL;
    FILE *fp = fopen(path, "rb");
    if (!fp)
        return NULL;
    if (fseek(fp, 0, SEEK_END) != 0)
    {
        fclose(fp);
        return NULL;
    }
    long len = ftell(fp);
    if (len < 0)
    {
        fclose(fp);
        return NULL;
    }
    if (fseek(fp, 0, SEEK_SET) != 0)
    {
        fclose(fp);
        return NULL;
    }
    char *buf = (char *) MemoryContextAllocZero(mcxt, (Size) len + 1);
    size_t got = fread(buf, 1, (size_t) len, fp);
    fclose(fp);
    if (got != (size_t) len)
        return NULL;
    buf[len] = '\0';
    return buf;
}

static PolicyEvalResultC *
// Parses the active policy for the tables used by this query.
cf_eval_policies_for_tables(const char *query_sql, char **scanned_tables, int n_scanned)
{
    if (cf_binding_contract_enabled())
    {
        if (!query_sql || query_sql[0] == '\0')
            ereport(ERROR,
                    (errmsg("custom_filter_new: binding contract requires query SQL"),
                     errdetail("policy_template_path, policy_binding_path, and query_path are set, but query SQL is empty.")));
        const char *bound_text = cf_get_bound_policy_text(query_sql);
        if (bound_text && bound_text[0] != '\0')
        {
            return evaluate_policies_text_scanned(bound_text, scanned_tables, n_scanned);
        }
        ereport(ERROR,
                (errmsg("custom_filter_new: policy binding returned no resolved policy"),
                 errdetail("template=%s binding=%s query=%s query_id=%s",
                           cf_template_policy_path(),
                           cf_policy_binding_path,
                           cf_query_path,
                           (cf_query_id && cf_query_id[0]) ? cf_query_id : "<empty>")));
    }
    if (!cf_template_policy_path() || cf_template_policy_path()[0] == '\0')
        return NULL;
    return evaluate_policies_scanned(cf_template_policy_path(), scanned_tables, n_scanned);
}


bool cf_in_internal_query = false;

static bool cf_in_executor_start_init = false;


set_rel_pathlist_hook_type prev_set_rel_pathlist_hook = NULL;
planner_hook_type prev_planner_hook = NULL;
ExecutorStart_hook_type prev_ExecutorStart_hook = NULL;
ExecutorRun_hook_type prev_ExecutorRun_hook = NULL;

typedef struct CfPlannerPolicyEvalCacheEntry
{
    const Query *parse;
    bool has_targets;
    char **target_tables;
    int target_count;
    char **fallback_relnames;
    bool *fallback_results;
    int fallback_count;
    int fallback_cap;
    struct CfPlannerPolicyEvalCacheEntry *next;
} CfPlannerPolicyEvalCacheEntry;

typedef struct CfPlannerGucSnapshot
{
    bool active;
    bool contract_mode;
    char *enable_indexonlyscan;
    char *enable_indexscan;
    char *enable_bitmapscan;
    char *enable_tidscan;
    char *enable_seqscan;
} CfPlannerGucSnapshot;

static CfPlannerPolicyEvalCacheEntry *cf_planner_policy_cache = NULL;
static int cf_planner_scope_depth = 0;


void cf_rel_pathlist_hook(PlannerInfo *root, RelOptInfo *rel, Index rti, RangeTblEntry *rte);
static PlannedStmt *cf_planner_hook(Query *parse, const char *query_string,
                                    int cursorOptions, ParamListInfo boundParams);
static void cf_executor_start(QueryDesc *queryDesc, int eflags);
static void cf_executor_run(QueryDesc *queryDesc, ScanDirection direction, uint64 count, bool execute_once);

Plan *cf_plan_path(PlannerInfo *root, RelOptInfo *rel,struct CustomPath *best_path,List *tlist, List *clauses, List *custom_plans);

Node *cf_create_state(CustomScan *cscan);
void cf_begin(CustomScanState *node, EState *estate, int eflags);
TupleTableSlot *cf_exec(CustomScanState *node);
void cf_end(CustomScanState *node);
void cf_explain(CustomScanState *node, List *ancestors, ExplainState *es);
void cf_rescan(CustomScanState *node);
bool cf_child_is_scan(PlanState *node);
TupleTableSlot *cf_return_tuple(CustomScanState *node);
static TupleTableSlot *cf_store_slot(CustomScanState *node, TupleTableSlot *slot);
void cf_accum_validation_time(struct CfExec *st, instr_time *start_time);

static const char *cf_debug_mode_name(int mode);

static void
cf_log_policy_identity(const char *path)
{
    if (!path || !path[0])
        return;

    struct stat st;
    if (stat(path, &st) != 0)
    {
        CF_TRACE_LOG( "policy_contract: policy_path=%s (stat failed)", path);
        return;
    }

    CF_TRACE_LOG( "policy_contract: policy_path=%s size=%lld",
         path, (long long) st.st_size);

    size_t sz = (size_t) st.st_size;
    char *buf = (char *) palloc(sz > 0 ? sz : 1);

    File fd = PathNameOpenFile(path, O_RDONLY | PG_BINARY);
    if (fd < 0)
    {
        CF_TRACE_LOG( "policy_contract: policy_path=%s md5=ERROR(open)", path);
        pfree(buf);
        return;
    }

    int nread = FileRead(fd, buf, sz, 0, WAIT_EVENT_DATA_FILE_READ);
    FileClose(fd);
    if (nread < 0 || (size_t)nread != sz)
    {
        CF_TRACE_LOG( "policy_contract: policy_path=%s md5=ERROR(read)", path);
        pfree(buf);
        return;
    }

    char md5buf[MD5_DIGEST_LENGTH * 2 + 1];
    const char *err = NULL;
    if (pg_md5_hash(buf, sz, md5buf, &err))
    {
        md5buf[MD5_DIGEST_LENGTH * 2] = '\0';
        CF_TRACE_LOG( "policy_contract: policy_path=%s md5=%s", path, md5buf);
    }
    else
    {
        CF_TRACE_LOG( "policy_contract: policy_path=%s md5=ERROR(hash)", path);
    }
    pfree(buf);
}
static PolicyQueryState *cf_build_query_state(EState *estate, const char *query_str);
static TableFilterState *cf_find_filter(PolicyQueryState *qs, Oid relid, bool log_on_miss);
static bool cf_table_wrapped(PolicyQueryState *qs, const char *name);
static const char *cf_plan_find_scan_type(Plan *plan, PlannedStmt *pstmt, Oid relid);
static bool cf_plan_scan_relid(Plan *plan, Index *out_relid);
static bool cf_relid_is_relation(PlannedStmt *pstmt, Index scanrelid, Oid *out_relid);
static void cf_count_rel_occurrences(PlannedStmt *pstmt, Oid relid, int *out_scanned, int *out_wrapped);
static void cf_log_wrapper_audit(PlannedStmt *pstmt);
typedef enum CfTidSource
{
    CF_TID_NONE = 0,
    CF_TID_TTS = 1,
    CF_TID_SYSATTR = 2,
    CF_TID_MAT_TTS = 3,
    CF_TID_HEAPTUPLE = 4
} CfTidSource;

static const char *cf_tid_source_name(CfTidSource src);
static bool cf_slot_get_ctid(TupleTableSlot *slot, ItemPointerData *out, CfTidSource *src);
static TupleTableSlot *cf_scan_slot(PlanState *child, TupleTableSlot *fallback);
static void cf_collect_scanned_tables(EState *estate, MemoryContext mcxt,
                                      char ***out_names, int *out_count,
                                      char ***out_wrapped, int *out_wrapped_count,
                                      int *out_main_rel_count, int *out_total_rel_count);
static bool cf_table_in_list(const char *name, char **list, int count);
static int cf_eval_target_index(const PolicyEvalResultC *res, const char *name);
static void cf_parse_query_targets(const char *query_str, MemoryContext mcxt, char ***out_tables, int *out_count);
static void cf_free_cstring_list(char **items, int count);
static bool cf_collect_policy_targets_for_parse(Query *parse, MemoryContext mcxt,
                                                char ***out_targets, int *out_target_count);
static bool cf_is_policy_target_single_table(const char *relname);
static const CfPlannerPolicyEvalCacheEntry *cf_planner_policy_eval(Query *parse);
static void cf_planner_policy_cache_reset(void);
static void cf_planner_scope_enter(void);
static void cf_planner_scope_exit(void);
static void cf_planner_guc_snapshot_init(CfPlannerGucSnapshot *snap);
static void cf_planner_guc_apply(CfPlannerGucSnapshot *snap, bool contract_mode);
static void cf_planner_guc_restore(CfPlannerGucSnapshot *snap);
static bool cf_table_should_filter(PolicyQueryState *qs, const char *name);
static bool cf_table_scanned(PolicyQueryState *qs, const char *name);
static bool cf_needed_file_used_by_policy_new(const char *name);
static void cf_prune_needed_files_for_policy_new(PolicyQueryState *qs);
static void cf_augment_needed_files_for_walk(PolicyQueryState *qs,
                                             const PolicyEvalResultC *eval_res);
static bool cf_rel_is_policy_target(PlannerInfo *root, Oid relid);
static bool cf_plan_inner_only_safe(Plan *plan, const char **reason_out);
static bool cf_query_has_empty_allow_set(const PolicyQueryState *qs, const char **table_out);
static void cf_reset_query_exec_metrics(PolicyQueryState *qs);
static void cf_update_scan_mode(struct CfExec *st, CustomScanState *node, TableFilterState *tf);
static bool cf_tid_iter_next(struct CfExec *st, TableFilterState *tf, ItemPointerData *out_tid);
static TupleTableSlot *cf_exec_seqscan_tid_mode(CustomScanState *node, struct CfExec *st, TableFilterState *tf);
static void cf_collect_seqscan_qual_atoms(EState *estate,
                                          const PolicyEvalResultC *eval_res,
                                          MemoryContext mcxt,
                                          PolicyScanQualAtomC **out_atoms,
                                          int *out_count);

static bool cf_table_name_from_schema_key(const char *schema_key, char *out, size_t out_sz);
static bool cf_target_has_nonlocal_atoms(const PolicyEvalResultC *eval_res, const char *target_table);
static int cf_eval_effective_target_count(const PolicyEvalResultC *eval_res);
static char **cf_eval_effective_target_tables(const PolicyEvalResultC *eval_res);
static const char *cf_template_policy_path(void);
static bool cf_binding_contract_enabled(void);
static void cf_bound_policy_cache_reset(void);
static const char *cf_get_bound_policy_text(const char *query_sql);
static const char *cf_current_policy_query_sql(void);
static PolicyEvalResultC *cf_eval_policies_for_tables(const char *query_sql,
                                                      char **scanned_tables,
                                                      int n_scanned);


CustomPathMethods CFPathMethods = {
    .CustomName     = "custom_filter_new",
    .PlanCustomPath = cf_plan_path,
};

CustomScanMethods CFPlanMethods = {
    .CustomName            = "custom_filter_new",
    .CreateCustomScanState = cf_create_state,
};

CustomExecMethods CFExecMethods = {
    .BeginCustomScan   = cf_begin,
    .ExecCustomScan    = cf_exec,
    .EndCustomScan     = cf_end,
    .ReScanCustomScan  = cf_rescan,
    .ExplainCustomScan = cf_explain,
};


void _PG_init(void);
void _PG_fini(void);

// Registers the PAC planner and executor hooks.
void
_PG_init(void)
{
    DefineCustomBoolVariable("custom_filter_new.chunked_artifacts", "Read physical blob chunks without changing logical rank structures.",
        NULL,&cf_chunked_artifacts,false,PGC_SUSET,0,NULL,NULL,NULL);
    DefineCustomStringVariable("custom_filter_new.artifact_directory", "Read-only bundle directory for offline count checks.",
        NULL,&cf_artifact_directory,"",PGC_SUSET,0,NULL,NULL,NULL);
    DefineCustomBoolVariable("custom_filter_new.block_target_loop", "Batch target ranks and send only unresolved instances to the scalar path.",
                             NULL,&cf_block_target_loop,true,PGC_SUSET,0,NULL,NULL,NULL);
    DefineCustomBoolVariable("custom_filter_new.composed_reuse", "Keep reached functional chain endpoints by first entering rank.",
                             NULL,&cf_composed_reuse,true,PGC_SUSET,0,NULL,NULL,NULL);
    DefineCustomBoolVariable("custom_filter_new.run_reuse", "Evaluate equal consecutive complete target input tuples once.",
                             NULL,&cf_run_reuse,true,PGC_SUSET,0,NULL,NULL,NULL);
    DefineCustomBoolVariable("custom_filter_new.decision_sharing", "Merge connection requests across operators; operators remain per request.",
                             NULL,&cf_decision_sharing,true,PGC_SUSET,0,NULL,NULL,NULL);
    DefineCustomBoolVariable("custom_filter_new.posting_position_store", "Keep unique multi-equality witness verdicts in online posting-position cells.",
                             NULL,&cf_posting_position_store,true,PGC_SUSET,0,NULL,NULL,NULL);
    DefineCustomBoolVariable("custom_filter_new.composed_bounds", "Compose complete-witness windows along equality subwalks, filled on arrival.",
                             NULL,&cf_composed_bounds,true,PGC_SUSET,0,NULL,NULL,NULL);
    DefineCustomIntVariable("custom_filter_new.block_target_rows", "Target rows per sequential block; multiple of 64.",
                            NULL,&cf_block_target_rows,1024,64,65536,PGC_SUSET,0,NULL,NULL,NULL);
    DefineCustomBoolVariable("custom_filter_new.cost_single_visit", "Plan no-store and repeat admission from headers.",
                             NULL,&cf_cost_single_visit,true,PGC_SUSET,0,NULL,NULL,NULL);
    DefineCustomBoolVariable("custom_filter_new.cost_branch_order", "Move a branch only for a twofold predicted cost advantage.",
                             NULL,&cf_cost_branch_order,true,PGC_SUSET,0,NULL,NULL,NULL);
    DefineCustomBoolVariable("custom_filter_new.cost_present_caps", "Use present count for dense plan eligibility.",
                             NULL,&cf_cost_present_caps,true,PGC_SUSET,0,NULL,NULL,NULL);
    DefineCustomBoolVariable("custom_filter_new.cost_dense_budget", "Use reached-key sparse caches when dense storage exceeds its budget.",
                             NULL,&cf_cost_dense_budget,true,PGC_SUSET,0,NULL,NULL,NULL);
    DefineCustomIntVariable("custom_filter_new.cost_dense_budget_mb", "Dense-cache budget; small values exercise sparse fallback in tests.",
                            NULL,&cf_cost_dense_budget_mb,2048,1,32768,PGC_SUSET,0,NULL,NULL,NULL);
    DefineCustomBoolVariable("custom_filter_new.cost_hop_elision", "Remove hop caches protected by the same-key guard or slot.",
                             NULL,&cf_cost_hop_elision,true,PGC_SUSET,0,NULL,NULL,NULL);
    DefineCustomBoolVariable("custom_filter_new.cost_target_fraction", "Include target constant-filter posting counts in arrival estimates.",
                             NULL,&cf_cost_target_fraction,true,PGC_SUSET,0,NULL,NULL,NULL);
    DefineCustomBoolVariable("custom_filter_new.cost_group_maps", "Index only reached composite posting groups.",
                             NULL,&cf_cost_group_maps,true,PGC_SUSET,0,NULL,NULL,NULL);
    static const struct config_enum_entry direction_options[] = {
        {"target", 0, false}, {NULL, 0, false}
    };
    DefineCustomBoolVariable("custom_filter_new.composite_edges",
                            "Use unary postings for complete equality connections.",
                            NULL, &cf_composite_edges, true, PGC_SUSET, 0, NULL, NULL, NULL);
    DefineCustomBoolVariable("custom_filter_new.interval_edges",
                            "Use online monotone interval coverage indexes.",
                            NULL, &cf_interval_edges, true, PGC_SUSET, 0, NULL, NULL, NULL);
    DefineCustomBoolVariable("custom_filter_new.chain_projection", "Project functional chains online.",
                            NULL, &cf_chain_projection, true, PGC_SUSET, 0, NULL, NULL, NULL);
    DefineCustomBoolVariable("custom_filter_new.chain_boundaries", "Summarize complete chain witnesses.",
                            NULL, &cf_chain_boundaries, true, PGC_SUSET, 0, NULL, NULL, NULL);
    DefineCustomBoolVariable("custom_filter_new.composite_cost", "Avoid unprofitable composite postings.",
                            NULL, &cf_composite_cost, true, PGC_SUSET, 0, NULL, NULL, NULL);
    DefineCustomBoolVariable("custom_filter_new.engine_profile", "Measure engine phases in diagnostic runs.",
                            NULL, &cf_engine_profile, false, PGC_SUSET, 0, NULL, NULL, NULL);
    DefineCustomBoolVariable("custom_filter_new.tight_loop", "Use a compiled loop for fully decided policies.",
                            NULL, &cf_tight_loop, true, PGC_SUSET, 0, NULL, NULL, NULL);
    DefineCustomBoolVariable("custom_filter_new.component_boundaries", "Factor disjoint witness components for ordered boundaries.",
                            NULL, &cf_component_boundaries, true, PGC_SUSET, 0, NULL, NULL, NULL);
    DefineCustomBoolVariable("custom_filter_new.nested_theta_transfer", "Store complete one-row scoped decisions in filled-value boundary universes.",
                            NULL, &cf_nested_theta_transfer, true, PGC_SUSET, 0, NULL, NULL, NULL);
    DefineCustomBoolVariable("custom_filter_new.nested_equality_ranges", "Probe entered-rank equality ranges without unpacking row facts.",
                            NULL, &cf_nested_equality_ranges, true, PGC_SUSET, 0, NULL, NULL, NULL);
    DefineCustomBoolVariable("custom_filter_new.formula_rank_cache", "Cache a complete formula determined by one target rank.",
                            NULL, &cf_formula_rank_cache, true, PGC_SUSET, 0, NULL, NULL, NULL);
    DefineCustomEnumVariable("custom_filter_new.direction",
                            "Visit every target row.",
                            NULL, &cf_direction, 0, direction_options, PGC_SUSET, 0, NULL, NULL, NULL);
    static const struct config_enum_entry store_options[] = {
        {"old", 0, false}, {"rank", 1, false}, {NULL, 0, false}
    };
    DefineCustomEnumVariable("custom_filter_new.decision_store",
                             "Choose the old store or the rank decision store.",
                             NULL, &cf_decision_store, 1, store_options,
                             PGC_SUSET, 0, NULL, NULL, NULL);
    DefineCustomBoolVariable("custom_filter_new.rankstore_dump",
                             "Print the rank store after evaluation.",
                             NULL, &cf_rankstore_dump, false,
                             PGC_SUSET, 0, NULL, NULL, NULL);
    DefineCustomBoolVariable("custom_filter_new.enabled",
                             "",
                             NULL,
                             &cf_enabled,
                             false,
                             PGC_SUSET,
                             0,
                             NULL, NULL, NULL);

    DefineCustomIntVariable("custom_filter_new.cpu",
                            "CPU to pin this backend to (-1 chooses the first allowed CPU).",
                            NULL,
                            &cf_cpu,
                            -1,
                            -1,
                            CPU_SETSIZE - 1,
                            PGC_SUSET,
                            0,
                            NULL, NULL, NULL);

    static const struct config_enum_entry debug_mode_options[] = {
        {"off", 0, false},
        {"contract", 1, false},
        {"trace", 2, false},
        {NULL, 0, false}
    };

    DefineCustomEnumVariable("custom_filter_new.debug_mode",
                             "",
                             NULL,
                             &cf_debug_mode,
                             0,
                             debug_mode_options,
                             PGC_SUSET,
                             0,
                             NULL, NULL, NULL);

    static const struct config_enum_entry runtime_path_options[] = {
        {"walk", POLICY_RUNTIME_PATH_WALK, false},
        {NULL, 0, false}
    };

    DefineCustomEnumVariable("custom_filter_new.runtime_path",
                             "Select the PAC walk runtime.",
                             NULL,
                             &cf_runtime_path,
                             POLICY_RUNTIME_PATH_WALK,
                             runtime_path_options,
                             PGC_SUSET,
                             0,
                             NULL, NULL, NULL);

    DefineCustomBoolVariable("custom_filter_new.debug_ids",
                             "Emit executor identity / binding debug NOTICE lines (temporary; off by default).",
                             NULL,
                             &cf_debug_ids,
                             false,
                             PGC_SUSET,
                             0,
                             NULL, NULL, NULL);

    DefineCustomBoolVariable("custom_filter_new.diagnostic_logging",
                             "Enable diagnostic logging; off for measured runs.",
                             NULL, &cf_diagnostic_logging, false, PGC_SUSET, 0,
                             NULL, NULL, NULL);
    DefineCustomStringVariable("custom_filter_new.last_metrics", "Last query timing and counters, without logging.",
                               NULL, &cf_perf_json_setting, "", PGC_INTERNAL, 0, NULL, NULL, cf_perf_show_json);
    DefineCustomStringVariable("custom_filter_new.last_cost_plan", "Header admission and diagnostic cache outcomes.",
                               NULL,&cf_cost_plan_setting,"",PGC_INTERNAL,0,NULL,NULL,NULL);
    for (size_t i = 0; i < lengthof(cf_perf_metrics); ++i) {
        char *name = psprintf("custom_filter_new.last_%s", cf_perf_metrics[i].name);
        DefineCustomRealVariable(name, "Last query metric, read after timing.", NULL,
                                 &cf_perf_metrics[i].value, -1, -1, DBL_MAX,
                                 PGC_INTERNAL, 0, NULL, NULL,
                                 i == 0 ? cf_perf_show_exec : i == 1 ? cf_perf_show_start : i == 2 ? cf_perf_show_stop : NULL);
    }

    DefineCustomIntVariable("custom_filter_new.profile_k",
                            "",
                            NULL,
                            &cf_profile_k,
                            0,
                            0,
                            1000000,
                            PGC_SUSET,
                            0,
                            NULL, NULL, NULL);

    DefineCustomIntVariable("custom_filter_new.class_phase_limit",
                            "Stop the class-based engine after this many paper-order phases for profiling.",
                            NULL,
                            &cf_class_phase_limit,
                            0,
                            0,
                            100,
                            PGC_SUSET,
                            0,
                            NULL, NULL, NULL);

    DefineCustomIntVariable("custom_filter_new.class_phase_timeout_ms",
                            "Abort a single class-based paper phase if it runs longer than this many milliseconds.",
                            NULL,
                            &cf_class_phase_timeout_ms,
                            20000,
                            1,
                            3600000,
                            PGC_SUSET,
                            0,
                            NULL, NULL, NULL);

    DefineCustomStringVariable("custom_filter_new.profile_query",
                               "",
                               NULL,
                               &cf_profile_query,
                               "",
                               PGC_SUSET,
                               0,
                               NULL, NULL, NULL);

    DefineCustomStringVariable("custom_filter_new.policy_path",
                               "",
                               NULL,
                               &cf_policy_path,
                               NULL,
                               PGC_SUSET,
                               0,
                               NULL, NULL, NULL);

    DefineCustomStringVariable("custom_filter_new.policy_template_path",
                               "",
                               NULL,
                               &cf_policy_template_path,
                               NULL,
                               PGC_SUSET,
                               0,
                               NULL, NULL, NULL);

    DefineCustomStringVariable("custom_filter_new.policy_binding_path",
                               "",
                               NULL,
                               &cf_policy_binding_path,
                               NULL,
                               PGC_SUSET,
                               0,
                               NULL, NULL, NULL);

    DefineCustomStringVariable("custom_filter_new.query_path",
                               "",
                               NULL,
                               &cf_query_path,
                               NULL,
                               PGC_SUSET,
                               0,
                               NULL, NULL, NULL);

    DefineCustomStringVariable("custom_filter_new.query_id",
                               "",
                               NULL,
                               &cf_query_id,
                               "",
                               PGC_SUSET,
                               0,
                               NULL, NULL, NULL);

    DefineCustomBoolVariable("custom_filter_new.profile_rescan",
                             "",
                             NULL,
                             &cf_profile_rescan,
                             false,
                             PGC_SUSET,
                             0,
                             NULL, NULL, NULL);

    DefineCustomBoolVariable("custom_filter_new.tidscan_seqscan",
                             "Enable adaptive CTID-driven fetch mode for selective SeqScan targets.",
                             NULL,
                             &cf_tidscan_seqscan,
                             true,
                             PGC_SUSET,
                             0,
                             NULL, NULL, NULL);

    DefineCustomRealVariable("custom_filter_new.tidscan_density_threshold",
                             "Switch SeqScan to CTID-driven mode when allowed-block density is below this threshold.",
                             NULL,
                             &cf_tidscan_density_threshold,
                             0.20,
                             0.0,
                             1.0,
                             PGC_SUSET,
                             0,
                             NULL, NULL, NULL);

    prev_planner_hook = planner_hook;
    planner_hook = cf_planner_hook;

    prev_set_rel_pathlist_hook = set_rel_pathlist_hook;
    set_rel_pathlist_hook = cf_rel_pathlist_hook;

    prev_ExecutorStart_hook = ExecutorStart_hook;
    ExecutorStart_hook = cf_executor_start;
    prev_ExecutorRun_hook = ExecutorRun_hook;
    ExecutorRun_hook = cf_executor_run;

    RegisterCustomScanMethods(&CFPlanMethods);
}

void
_PG_fini(void)
{
    planner_hook = prev_planner_hook;
    set_rel_pathlist_hook = prev_set_rel_pathlist_hook;
    ExecutorStart_hook = prev_ExecutorStart_hook;
    ExecutorRun_hook = prev_ExecutorRun_hook;
    cf_planner_policy_cache_reset();
    cf_planner_scope_depth = 0;
}

static void
cf_collect_parse_tables_recurse(Query *parse, List **out_names)
{
    if (!parse || !parse->rtable || !out_names)
        return;
    ListCell *lc;
    foreach (lc, parse->rtable)
    {
        RangeTblEntry *rte = (RangeTblEntry *) lfirst(lc);
        if (!rte)
            continue;
        if (rte->rtekind == RTE_RELATION)
        {
            const char *rn = get_rel_name(rte->relid);
            if (!rn)
                continue;
            bool seen = false;
            ListCell *ln;
            foreach (ln, *out_names)
            {
                const char *cur = (const char *) lfirst(ln);
                if (cur && strcmp(cur, rn) == 0)
                {
                    seen = true;
                    break;
                }
            }
            if (!seen)
                *out_names = lappend(*out_names, pstrdup(rn));
            continue;
        }
        if (rte->rtekind == RTE_SUBQUERY && rte->subquery)
            cf_collect_parse_tables_recurse(rte->subquery, out_names);
    }
}

static void
cf_collect_parse_tables(Query *parse, MemoryContext mcxt, char ***out_tables, int *out_count)
{
    *out_tables = NULL;
    *out_count = 0;
    if (!parse)
        return;

    List *names = NIL;
    cf_collect_parse_tables_recurse(parse, &names);
    int count = list_length(names);
    if (count <= 0 || names == NIL)
        return;

    MemoryContext oldctx = MemoryContextSwitchTo(mcxt);
    char **tables = (char **) palloc0(sizeof(char *) * count);
    MemoryContextSwitchTo(oldctx);

    int idx = 0;
    ListCell *lc;
    foreach (lc, names)
    {
        const char *rn = (const char *) lfirst(lc);
        if (!rn || !rn[0])
            continue;
        oldctx = MemoryContextSwitchTo(mcxt);
        tables[idx++] = pstrdup(rn);
        MemoryContextSwitchTo(oldctx);
    }

    *out_tables = tables;
    *out_count = idx;
}

static void
cf_free_cstring_list(char **items, int count)
{
    if (!items || count <= 0)
        return;
    for (int i = 0; i < count; i++)
    {
        if (items[i])
            pfree(items[i]);
    }
    pfree(items);
}

static bool
cf_table_name_from_schema_key(const char *schema_key, char *out, size_t out_sz)
{
    if (!schema_key || !out || out_sz == 0)
        return false;
    const char *p = schema_key;
    if (strncmp(p, "join:", 5) == 0)
        p += 5;
    else if (strncmp(p, "const:", 6) == 0)
        p += 6;
    while (*p == ' ')
        p++;
    const char *dot = strchr(p, '.');
    if (!dot || dot == p)
        return false;
    size_t n = (size_t) (dot - p);
    if (n >= out_sz)
        n = out_sz - 1;
    memcpy(out, p, n);
    out[n] = '\0';
    return true;
}

static int
cf_eval_effective_target_count(const PolicyEvalResultC *eval_res)
{
    if (!eval_res)
        return 0;
    if (eval_res->exec_target_count > 0 && eval_res->exec_target_tables)
        return eval_res->exec_target_count;
    return eval_res->target_count;
}

static char **
cf_eval_effective_target_tables(const PolicyEvalResultC *eval_res)
{
    if (!eval_res)
        return NULL;
    if (eval_res->exec_target_count > 0 && eval_res->exec_target_tables)
        return eval_res->exec_target_tables;
    return eval_res->target_tables;
}





static bool
cf_target_has_nonlocal_atoms(const PolicyEvalResultC *eval_res, const char *target_table)
{
    if (!eval_res || !eval_res->atoms || eval_res->atom_count <= 0 || !target_table || !target_table[0])
        return true;

    for (int i = 0; i < eval_res->atom_count; i++)
    {
        const PolicyAtomC *a = &eval_res->atoms[i];
        if (!a)
            continue;

        char lhs_tbl[NAMEDATALEN] = {0};
        char rhs_tbl[NAMEDATALEN] = {0};
        bool lhs_ok = cf_table_name_from_schema_key(a->lhs_schema_key, lhs_tbl, sizeof(lhs_tbl));
        bool rhs_ok = cf_table_name_from_schema_key(a->rhs_schema_key, rhs_tbl, sizeof(rhs_tbl));
        bool lhs_touch = lhs_ok && strcmp(lhs_tbl, target_table) == 0;
        bool rhs_touch = rhs_ok && strcmp(rhs_tbl, target_table) == 0;
        if (!lhs_touch && !rhs_touch)
            continue;

        if (a->kind == POLICY_ATOM_COL_CONST)
            continue;

        if (a->kind == POLICY_ATOM_COL_COL && lhs_touch && rhs_touch)
            continue;

        return true;
    }

    return false;
}

static bool
cf_collect_policy_targets_for_parse(Query *parse, MemoryContext mcxt,
                                    char ***out_targets, int *out_target_count)
{
    char **scanned_tables = NULL;
    int n_scanned_tables = 0;
    PolicyEvalResultC *eval_res = NULL;
    bool has_targets = false;
    char **targets = NULL;
    int target_cap = 0;
    int target_count = 0;
    MemoryContext alloc_ctx = mcxt ? mcxt : CurrentMemoryContext;

    if (out_targets)
        *out_targets = NULL;
    if (out_target_count)
        *out_target_count = 0;
    if (!parse || !cf_template_policy_path() || cf_template_policy_path()[0] == '\0')
        return false;

    cf_collect_parse_tables(parse, CurrentMemoryContext, &scanned_tables, &n_scanned_tables);
    if (n_scanned_tables <= 0 || !scanned_tables)
        return false;

    



    eval_res = cf_eval_policies_for_tables(cf_current_policy_query_sql(), scanned_tables, n_scanned_tables);
    int effective_target_count = cf_eval_effective_target_count(eval_res);
    char **effective_target_tables = cf_eval_effective_target_tables(eval_res);
    if (!eval_res || effective_target_count <= 0 || !effective_target_tables)
        goto cleanup;

    for (int i = 0; i < effective_target_count; i++)
    {
        const char *tbl = effective_target_tables[i];
        if (!tbl || tbl[0] == '\0')
            continue;

        bool seen = false;
        for (int j = 0; j < target_count; j++)
        {
            if (targets[j] && strcmp(targets[j], tbl) == 0)
            {
                seen = true;
                break;
            }
        }
        if (seen)
            continue;

        if (target_count >= target_cap)
        {
            int new_cap = (target_cap == 0) ? 8 : target_cap * 2;
            MemoryContext oldctx = MemoryContextSwitchTo(alloc_ctx);
            char **new_targets = (char **) palloc0(sizeof(char *) * new_cap);
            if (targets && target_count > 0)
                memcpy(new_targets, targets, sizeof(char *) * target_count);
            MemoryContextSwitchTo(oldctx);
            if (targets)
                pfree(targets);
            targets = new_targets;
            target_cap = new_cap;
        }

        {
            MemoryContext oldctx = MemoryContextSwitchTo(alloc_ctx);
            targets[target_count++] = pstrdup(tbl);
            MemoryContextSwitchTo(oldctx);
        }
    }

    if (target_count > 0)
    {
        has_targets = true;
        if (out_targets)
            *out_targets = targets;
        else
            cf_free_cstring_list(targets, target_count);
        if (out_target_count)
            *out_target_count = target_count;
    }
    else
    {
        if (targets)
            pfree(targets);
    }

cleanup:
    if (eval_res)
        free_policy_eval_result(eval_res);
    cf_free_cstring_list(scanned_tables, n_scanned_tables);
    return has_targets;
}








static bool
cf_is_policy_target_single_table(const char *relname)
{
    bool found = false;
    char *scanned[1];
    PolicyEvalResultC *eval_res = NULL;

    if (!relname || !relname[0] || !cf_template_policy_path() || cf_template_policy_path()[0] == '\0')
        return false;
    scanned[0] = (char *) relname;
    eval_res = cf_eval_policies_for_tables(cf_current_policy_query_sql(), scanned, 1);
    int effective_target_count = cf_eval_effective_target_count(eval_res);
    char **effective_target_tables = cf_eval_effective_target_tables(eval_res);
    if (eval_res && effective_target_tables && effective_target_count > 0)
    {
        for (int i = 0; i < effective_target_count; i++)
        {
            if (effective_target_tables[i] && strcmp(effective_target_tables[i], relname) == 0)
            {
                found = true;
                break;
            }
        }
    }
    if (eval_res)
        free_policy_eval_result(eval_res);
    return found;
}

static const CfPlannerPolicyEvalCacheEntry *
cf_planner_policy_eval(Query *parse)
{
    CfPlannerPolicyEvalCacheEntry *it = NULL;
    CfPlannerPolicyEvalCacheEntry *entry = NULL;
    char **targets = NULL;
    int target_count = 0;
    bool has_targets = false;

    if (!parse || !cf_template_policy_path() || cf_template_policy_path()[0] == '\0')
        return NULL;

    for (it = cf_planner_policy_cache; it; it = it->next)
    {
        if (it->parse == parse)
            return it;
    }

    has_targets = cf_collect_policy_targets_for_parse(parse,
                                                      CurrentMemoryContext,
                                                      &targets,
                                                      &target_count);
    entry = (CfPlannerPolicyEvalCacheEntry *) palloc0(sizeof(CfPlannerPolicyEvalCacheEntry));
    entry->parse = parse;
    entry->has_targets = has_targets;
    entry->target_tables = targets;
    entry->target_count = target_count;
    entry->next = cf_planner_policy_cache;
    cf_planner_policy_cache = entry;
    return entry;
}

static bool
cf_planner_policy_eval_fallback_lookup(CfPlannerPolicyEvalCacheEntry *entry,
                                       const char *relname,
                                       bool *out_found)
{
    if (out_found)
        *out_found = false;
    if (!entry || !relname || !relname[0])
        return false;
    for (int i = 0; i < entry->fallback_count; i++)
    {
        if (entry->fallback_relnames[i] && strcmp(entry->fallback_relnames[i], relname) == 0)
        {
            if (out_found)
                *out_found = true;
            return entry->fallback_results[i];
        }
    }
    return false;
}

static void
cf_planner_policy_eval_fallback_store(CfPlannerPolicyEvalCacheEntry *entry,
                                      const char *relname,
                                      bool result)
{
    if (!entry || !relname || !relname[0])
        return;
    for (int i = 0; i < entry->fallback_count; i++)
    {
        if (entry->fallback_relnames[i] && strcmp(entry->fallback_relnames[i], relname) == 0)
        {
            entry->fallback_results[i] = result;
            return;
        }
    }
    if (entry->fallback_count >= entry->fallback_cap)
    {
        int new_cap = (entry->fallback_cap == 0) ? 4 : (entry->fallback_cap * 2);
        char **new_names = (char **) palloc0(sizeof(char *) * new_cap);
        bool *new_results = (bool *) palloc0(sizeof(bool) * new_cap);
        if (entry->fallback_relnames && entry->fallback_count > 0)
            memcpy(new_names, entry->fallback_relnames, sizeof(char *) * entry->fallback_count);
        if (entry->fallback_results && entry->fallback_count > 0)
            memcpy(new_results, entry->fallback_results, sizeof(bool) * entry->fallback_count);
        if (entry->fallback_relnames)
            pfree(entry->fallback_relnames);
        if (entry->fallback_results)
            pfree(entry->fallback_results);
        entry->fallback_relnames = new_names;
        entry->fallback_results = new_results;
        entry->fallback_cap = new_cap;
    }
    entry->fallback_relnames[entry->fallback_count] = pstrdup(relname);
    entry->fallback_results[entry->fallback_count] = result;
    entry->fallback_count++;
}

static void
cf_planner_policy_cache_reset(void)
{
    while (cf_planner_policy_cache)
    {
        CfPlannerPolicyEvalCacheEntry *next = cf_planner_policy_cache->next;
        cf_free_cstring_list(cf_planner_policy_cache->target_tables,
                             cf_planner_policy_cache->target_count);
        cf_free_cstring_list(cf_planner_policy_cache->fallback_relnames,
                             cf_planner_policy_cache->fallback_count);
        if (cf_planner_policy_cache->fallback_results)
            pfree(cf_planner_policy_cache->fallback_results);
        pfree(cf_planner_policy_cache);
        cf_planner_policy_cache = next;
    }
}

static void
cf_planner_scope_enter(void)
{
    if (cf_planner_scope_depth == 0)
    {
        cf_planner_policy_cache_reset();
        cf_bound_policy_cache_reset();
    }
    cf_planner_scope_depth++;
}

static void
cf_planner_scope_exit(void)
{
    if (cf_planner_scope_depth > 0)
        cf_planner_scope_depth--;
    if (cf_planner_scope_depth == 0)
        cf_planner_policy_cache_reset();
}

static void
cf_planner_guc_snapshot_init(CfPlannerGucSnapshot *snap)
{
    if (!snap)
        return;
    memset(snap, 0, sizeof(*snap));
}

static void
cf_planner_guc_apply(CfPlannerGucSnapshot *snap, bool contract_mode)
{
    if (!snap)
        return;

    cf_planner_guc_snapshot_init(snap);
    snap->contract_mode = contract_mode;

    {
        const char *v = GetConfigOption("enable_indexonlyscan", true, false);
        snap->enable_indexonlyscan = v ? pstrdup(v) : pstrdup("on");
    }
    {
        const char *v_index = GetConfigOption("enable_indexscan", true, false);
        const char *v_bitmap = GetConfigOption("enable_bitmapscan", true, false);
        const char *v_tid = GetConfigOption("enable_tidscan", true, false);
        const char *v_seq = GetConfigOption("enable_seqscan", true, false);
        snap->enable_indexscan = pstrdup(v_index ? v_index : "on");
        snap->enable_bitmapscan = pstrdup(v_bitmap ? v_bitmap : "on");
        snap->enable_tidscan = pstrdup(v_tid ? v_tid : "on");
        snap->enable_seqscan = pstrdup(v_seq ? v_seq : "on");
    }

    (void) contract_mode;
    SetConfigOption("enable_indexonlyscan", "off", PGC_USERSET, PGC_S_SESSION);
    snap->active = true;
}

static void
cf_planner_guc_restore(CfPlannerGucSnapshot *snap)
{
    if (!snap || !snap->active)
        return;

    if (snap->enable_indexonlyscan)
        SetConfigOption("enable_indexonlyscan", snap->enable_indexonlyscan, PGC_USERSET, PGC_S_SESSION);
    if (snap->enable_indexscan)
        SetConfigOption("enable_indexscan", snap->enable_indexscan, PGC_USERSET, PGC_S_SESSION);
    if (snap->enable_bitmapscan)
        SetConfigOption("enable_bitmapscan", snap->enable_bitmapscan, PGC_USERSET, PGC_S_SESSION);
    if (snap->enable_tidscan)
        SetConfigOption("enable_tidscan", snap->enable_tidscan, PGC_USERSET, PGC_S_SESSION);
    if (snap->enable_seqscan)
        SetConfigOption("enable_seqscan", snap->enable_seqscan, PGC_USERSET, PGC_S_SESSION);

    if (snap->enable_indexonlyscan)
        pfree(snap->enable_indexonlyscan);
    if (snap->enable_indexscan)
        pfree(snap->enable_indexscan);
    if (snap->enable_bitmapscan)
        pfree(snap->enable_bitmapscan);
    if (snap->enable_tidscan)
        pfree(snap->enable_tidscan);
    if (snap->enable_seqscan)
        pfree(snap->enable_seqscan);

    cf_planner_guc_snapshot_init(snap);
}

static bool
cf_query_has_policy_targets(Query *parse)
{
    const CfPlannerPolicyEvalCacheEntry *entry = NULL;
    char **targets = NULL;
    int target_count = 0;
    bool has_targets = false;

    if (!parse || !cf_template_policy_path() || cf_template_policy_path()[0] == '\0')
        return false;

    if (cf_planner_scope_depth > 0)
    {
        entry = cf_planner_policy_eval(parse);
        return (entry && entry->has_targets);
    }

    has_targets = cf_collect_policy_targets_for_parse(parse,
                                                      CurrentMemoryContext,
                                                      &targets,
                                                      &target_count);
    cf_free_cstring_list(targets, target_count);
    return has_targets;
}

static PlannedStmt *
cf_planner_hook(Query *parse, const char *query_string,
                int cursorOptions, ParamListInfo boundParams)
{
    PlannedStmt *res = NULL;
    volatile bool apply_planner_gucs = false;
    CfPlannerGucSnapshot guc_snapshot;
    const char *saved_planner_query_string = cf_planner_query_string;

    cf_planner_guc_snapshot_init(&guc_snapshot);
    cf_planner_scope_enter();
    cf_planner_query_string = query_string;

    PG_TRY();
    {
        if (cf_enabled && !cf_in_internal_query && cf_query_has_policy_targets(parse))
        {
            apply_planner_gucs = true;
            cf_planner_guc_apply(&guc_snapshot, cf_contract_enabled());
        }

        if (prev_planner_hook)
            res = prev_planner_hook(parse, query_string, cursorOptions, boundParams);
        else
            res = standard_planner(parse, query_string, cursorOptions, boundParams);
        if (apply_planner_gucs)
            cf_planner_guc_restore(&guc_snapshot);
        cf_planner_query_string = saved_planner_query_string;
        cf_planner_scope_exit();
    }
    PG_CATCH();
    {
        if (apply_planner_gucs)
            cf_planner_guc_restore(&guc_snapshot);
        cf_planner_query_string = saved_planner_query_string;
        cf_planner_scope_exit();
        PG_RE_THROW();
    }
    PG_END_TRY();
    return res;
}

void
cf_rel_pathlist_hook(PlannerInfo *root, RelOptInfo *rel,
                     Index rti, RangeTblEntry *rte)
{
    if (prev_set_rel_pathlist_hook)
        prev_set_rel_pathlist_hook(root, rel, rti, rte);

    
    if (!cf_enabled || cf_in_internal_query)
        return;

    if (rel->reloptkind != RELOPT_BASEREL || rte == NULL || rte->rtekind != RTE_RELATION)
        return;

    Relation relobj = table_open(rte->relid, NoLock);
    if (relobj->rd_rel->relkind != RELKIND_RELATION)
    {
        table_close(relobj, NoLock);
        return;
    }
    table_close(relobj, NoLock);

    const char *relname = rte ? get_rel_name(rte->relid) : NULL;
    bool rel_is_target = cf_rel_is_policy_target(root, rte->relid);
    if (cf_contract_enabled())
        CF_TRACE_LOG("custom_filter_new: pathlist_rel rel=%s oid=%u target=%d",
                     relname ? relname : "<unknown>",
                     rte ? rte->relid : InvalidOid,
                     rel_is_target ? 1 : 0);

    




    if (!rel_is_target)
        return;

    

    List *orig_paths = rel->pathlist;
    List *wrapped_paths = NIL;
    Path *best_total = NULL;
    Path *best_startup = NULL;
    ListCell *lc;

    foreach (lc, orig_paths)
    {
        Path *child = (Path *) lfirst(lc);
        if (!child || (child->pathtype != T_SeqScan &&
                       child->pathtype != T_IndexScan &&
                       child->pathtype != T_BitmapHeapScan))
            continue;
        CustomPath *cp = makeNode(CustomPath);
        cp->methods = &CFPathMethods;
        cp->path.pathtype = T_CustomScan;
        cp->path.parent = rel;
        cp->path.pathtarget = rel->reltarget;
        cp->path.param_info = child->param_info;
        cp->path.rows = child->rows;
        cp->path.startup_cost = child->startup_cost;
        cp->path.total_cost = child->total_cost;
        cp->flags = 0;
        cp->custom_paths = list_make1(child);
        cp->custom_private = NIL;

        wrapped_paths = lappend(wrapped_paths, &cp->path);
        if (!best_total || cp->path.total_cost < best_total->total_cost)
            best_total = &cp->path;
        if (!best_startup || cp->path.startup_cost < best_startup->startup_cost)
            best_startup = &cp->path;
    }

    if (wrapped_paths == NIL)
        return;

    CF_TRACE_LOG( "custom_filter_new: wrap rel=%s oid=%u paths=%d",
         relname ? relname : "<unknown>",
         rte ? rte->relid : InvalidOid,
         list_length(wrapped_paths));

    rel->pathlist = wrapped_paths;
    rel->cheapest_total_path = best_total;
    rel->cheapest_startup_path = best_startup;
}

static const char *
cf_debug_mode_name(int mode)
{
    switch (mode)
    {
        case 0:
            return "off";
        case 1:
            return "contract";
        case 2:
            return "trace";
        default:
            return "off";
    }
}

static bool
cf_rel_is_policy_target(PlannerInfo *root, Oid relid)
{
    const CfPlannerPolicyEvalCacheEntry *entry = NULL;
    CfPlannerPolicyEvalCacheEntry *mutable_entry = NULL;
    char **targets = NULL;
    int target_count = 0;
    if (!root || relid == InvalidOid)
        return false;
    if (!cf_template_policy_path() || cf_template_policy_path()[0] == '\0')
        return false;

    const char *relname = get_rel_name(relid);
    if (!relname)
        return false;

    if (cf_planner_scope_depth > 0)
    {
        bool fallback = false;
        bool fallback_found = false;
        entry = cf_planner_policy_eval(root->parse);
        mutable_entry = (CfPlannerPolicyEvalCacheEntry *) entry;
        if (entry && entry->has_targets && entry->target_count > 0)
        {
            for (int i = 0; i < entry->target_count; i++)
            {
                if (entry->target_tables[i] && strcmp(entry->target_tables[i], relname) == 0)
                {
                    if (cf_trace_enabled())
                        CF_METRICS_LOG(NOTICE, "custom_filter_new: rel_target_check rel=%s mode=cache matched=1 fallback=0",
                             relname);
                    return true;
                }
            }
        }
        fallback = cf_planner_policy_eval_fallback_lookup(mutable_entry, relname, &fallback_found);
        if (!fallback_found)
        {
            fallback = cf_is_policy_target_single_table(relname);
            cf_planner_policy_eval_fallback_store(mutable_entry, relname, fallback);
        }
        if (cf_trace_enabled())
            CF_METRICS_LOG(NOTICE, "custom_filter_new: rel_target_check rel=%s mode=cache matched=0 fallback=%d",
                 relname, fallback ? 1 : 0);
        return fallback;
    }

    if (!cf_collect_policy_targets_for_parse(root->parse,
                                             CurrentMemoryContext,
                                             &targets,
                                             &target_count))
        return false;

    for (int i = 0; i < target_count; i++)
    {
        if (targets[i] && strcmp(targets[i], relname) == 0)
        {
            cf_free_cstring_list(targets, target_count);
            if (cf_trace_enabled())
                CF_METRICS_LOG(NOTICE, "custom_filter_new: rel_target_check rel=%s mode=direct matched=1 fallback=0",
                     relname);
            return true;
        }
    }
    cf_free_cstring_list(targets, target_count);
    {
        bool fallback = cf_is_policy_target_single_table(relname);
        if (cf_trace_enabled())
            CF_METRICS_LOG(NOTICE, "custom_filter_new: rel_target_check rel=%s mode=direct matched=0 fallback=%d",
                 relname, fallback ? 1 : 0);
        return fallback;
    }
}

static const char *
cf_scan_state_name(PlanState *node)
{
    if (!node)
        return "<null>";
    switch (nodeTag(node))
    {
        case T_SeqScanState:
            return "SeqScan";
        case T_SampleScanState:
            return "SampleScan";
        case T_IndexScanState:
            return "IndexScan";
        case T_IndexOnlyScanState:
            return "IndexOnlyScan";
        case T_BitmapHeapScanState:
            return "BitmapHeapScan";
        case T_TidScanState:
            return "TidScan";
        case T_TidRangeScanState:
            return "TidRangeScan";
        case T_ForeignScanState:
            return "ForeignScan";
        case T_FunctionScanState:
            return "FunctionScan";
        case T_TableFuncScanState:
            return "TableFuncScan";
        case T_ValuesScanState:
            return "ValuesScan";
        case T_CteScanState:
            return "CteScan";
        case T_WorkTableScanState:
            return "WorkTableScan";
        default:
            return "OtherScan";
    }
}


Plan *
cf_plan_path(PlannerInfo *root, RelOptInfo *rel,
             CustomPath *best_path,
             List *tlist, List *clauses, List *custom_plans)
{
    CustomScan *cscan = makeNode(CustomScan);
    cscan->methods = &CFPlanMethods;

    
    cscan->scan.scanrelid       = rel->relid;
    Plan *child_plan = (custom_plans && custom_plans != NIL)
                           ? (Plan *) linitial(custom_plans)
                           : NULL;
    if (child_plan && child_plan->targetlist)
        cscan->scan.plan.targetlist = child_plan->targetlist;
    else
        cscan->scan.plan.targetlist = tlist;
    cscan->scan.plan.qual       = NIL;   

    cscan->custom_scan_tlist = cscan->scan.plan.targetlist;
    cscan->custom_exprs      = NIL;

    cscan->custom_plans = custom_plans;

    cscan->custom_relids = bms_copy(rel->relids);

    return &cscan->scan.plan;
}


typedef struct CfExec
{
    CustomScanState css;

    PlanState *child_plan;
    double data_transfer_ms;
    double policy_build_ms;
    double row_validation_ms;
    double child_exec_ms;
    double ctid_extract_ms;
    double ctid_to_rid_ms;
    double allow_check_ms;
    double projection_ms;
    uint64 child_next_calls;
    double tid_heap_fetch_ms;
    double tid_slot_store_ms;
    double tid_visibility_ms;

    uint64 tuples_seen;
    uint64 tuples_passed;
    uint64 misses;
    Oid relid;
    char relname[NAMEDATALEN];
    uint32 seq_rid;
    const char *scan_type;
    bool tid_logged;

    struct TableFilterState *filter;
    struct TableFilterState *validated_filter;
    uint64 validated_build_seq;
    bool need_filter_rebind;
    uint64 bound_build_seq;
    bool attempted_filter_rebuild;
    uint64 rescan_calls;
    bool exec_logged;
    bool debug_exec_logged;
    bool blk_cache_valid;
    BlockNumber blk_cache_blkno;
    bool blk_cache_present;
    const uint64 *blk_cache_words;
    uint64 blocks_seen;
    uint64 blocks_skipped;
    CfScanMode scan_mode;
    bool scan_mode_set;
    double scan_mode_density;
    bool scan_mode_logged;
    bool tid_iter_initialized;
    uint32 tid_iter_block_ord;
    uint32 tid_iter_word_idx;
    uint32 tid_iter_bit_min;
    TableScanDesc tidrange_scan;
    bool tidrange_active;
    bool tupleless_eligible;
    bool tupleless_fastpath;
    bool tupleless_range_active;
    bool tupleless_slot_ready;
    BlockNumber tupleless_blk;
    OffsetNumber tupleless_next_off;
    OffsetNumber tupleless_end_off;
    uint64 tid_blocks_visited;
    uint64 tid_tuples_fetched;
    uint64 tid_offsets_checked;
    uint64 tid_offsets_passed;
    double tid_fetch_ms;
    double tid_qual_ms;
    bool empty_short_circuit_recorded;
    uint64 empty_short_circuit_calls;
    double empty_short_circuit_ms;
    uint64 interrupt_counter;
} CfExec;

typedef struct TableFilterState
{
    Oid relid;
    char relname[NAMEDATALEN];
    uint32 n_rows;
    uint64 *block_words;
    uint32 *block_ids;
    uint32 blocks;
    uint32 total_blocks;
    size_t block_words_nbytes;
    size_t block_ids_nbytes;
    uint64 allowed_rows;
    uint32 allowed_sids;
    uint32 total_sids;
    double policy_hub_prop_ms;
    double policy_sat_ms;
    double policy_sid_build_ms;
    double allowed_density;
    int mode_hint;
    char mode_reason[64];
    bool allow_is_empty;
    bool allow_is_all;
    uint64 seen;
    uint64 passed;
    uint64 misses;
} TableFilterState;

typedef struct PolicyQueryState
{
    bool ready;
    bool metrics_logged;
    int n_filters;
    TableFilterState *filters;
    
    uint64 filters_guard_hash;
    bool filters_guard_set;
    bool filters_guard_reported;
    const char *filters_guard_last_ok_phase;
    
    MemoryContext filters_alloc_mctx;
    MemoryContext qctx;
    char **needed_files;
    int n_needed_files;
    char **policy_targets;
    int n_policy_targets;
    char **closure_tables;
    int n_closure_tables;
    char **query_targets;
    int n_query_targets;
    char **scanned_tables;
    int n_scanned_tables;
    char **wrapped_tables;
    int n_wrapped_tables;
    size_t bytes_allow;
    size_t bytes_ctid;
    size_t bytes_blk_index;
    size_t bytes_artifacts_loaded;
    double eval_ms;
    double scanned_collect_ms;
    double seqqual_collect_ms;
    double policy_run_wall_ms;
    double artifact_load_ms;
    double artifact_parse_ms;
    double atoms_ms;
    double propagate_ms;
    double project_ms;
    double project_mask_ms;
    double project_row_ms;
    size_t project_mask_bytes;
    int project_n_join_evals_max;
    int project_clause_words_max;
    int clause_plan_count_max;
    uint64 prop_join_scans_total;
    int unique_join_struct_sigs_max;
    char *prop_table_scans;
    uint64 signature_cache_hits;
    uint64 signature_cache_misses;
    uint64 term_code_scans;
    uint64 target_full_row_scans;
    size_t target_rid_bitmap_bytes;
    size_t signature_cache_bytes;
    uint64 active_sig_dense_count;
    uint64 active_sig_sparse_count;
    double active_sig_density_sum;
    uint64 domain_set_dense_count;
    uint64 domain_set_sparse_count;
    double domain_set_density_sum;
    uint64 block_words_blocks_allocated;
    uint64 block_words_total_blocks;
    size_t block_words_dense_bytes;
    uint64 block_words_nblocks;
    uint64 block_words_nwords_per_block;
    uint64 proj_sig_count;
    uint64 proj_sig_total;
    uint64 proj_sig_new;
    uint64 proj_sig_skipped;
    uint64 proj_mask_or_ops;
    uint64 proj_rid_iters;
    uint64 proj_rid_iters_scan_enforcement;
    uint64 proj_rid_iters_dependency;
    uint64 canon_term_map_cache_hits;
    uint64 canon_term_map_cache_misses;
    double canon_term_map_build_ms;
    size_t canon_term_map_bytes;
    double restrict_key_index_build_ms;
    uint64 restrict_key_index_entries;
    size_t restrict_key_index_bytes;
    double restrict_key_prune_ms;
    uint64 sigmask_cache_hits;
    uint64 sigmask_cache_misses;
    double sigmask_build_ms;
    size_t sigmask_bytes;
    size_t bytes_sig_ctid_masks;
    size_t bytes_block_words;
    size_t bytes_artifact_buffers_retained;
    size_t bytes_decoded_buffers_retained;
    uint64 qual_atoms_total;
    uint64 qual_atoms_applied;
    uint64 qual_pruned_sigs;
    double qual_prune_ms;
    uint64 restrict_sig_tables;
    uint64 restrict_sig_schema_cols_total;
    size_t restrict_sig_bytes_total;
    double restrict_sig_apply_ms;
    double restrict_term_apply_ms;
    uint64 restrict_term_sigs_kept;
    uint64 restrict_term_sigs_dropped;
    double stamp_ms;
    double bin_ms;
    double local_sat_ms;
    double fill_ms;
    double prop_ms;
    int prop_iters;
    double decode_ms;
    double policy_total_ms;
    uint64 bin_build_rows_scanned;
    uint64 bin_count_final;
    uint64 bin_build_hub_count;
    double ctid_map_ms;
    double allow_build_ms;
    double executor_init_ms_ours;
    double filter_ms;
    double child_exec_ms;
    double ctid_extract_ms;
    double ctid_to_rid_ms;
    double allow_check_ms;
    double projection_ms;
    double custom_scan_total_ms;
    double custom_scan_overhead_ms;
    uint64 child_next_calls_total;
    uint64 total_filter_rows;
    uint64 total_allow_rows;
    uint64 rows_seen;
    uint64 rows_passed;
    uint64 ctid_misses;
    uint64 blocks_seen;
    uint64 blocks_skipped;
    uint64 scan_mode_tid_tables;
    uint64 scan_mode_filter_tables;
    uint64 scan_mode_empty_tables;
    uint64 scan_mode_all_tables;
    uint64 tid_blocks_visited;
    uint64 tid_tuples_fetched;
    uint64 tid_offsets_checked;
    uint64 tid_offsets_passed;
    double tid_fetch_ms;
    double tid_qual_ms;
    double tid_heap_fetch_ms;
    double tid_slot_store_ms;
    double tid_visibility_ms;
    uint64 empty_short_circuit_tables;
    double empty_short_circuit_ms;
    bool query_short_circuit_empty;
    bool query_short_circuit_decided;
    char query_short_circuit_reason[64];
    double query_short_circuit_ms;
    uint64 query_short_circuit_hits;
    uint64 scan_reuse_hits;
    uint64 scan_reuse_misses;
    double scan_reuse_ms_saved;
    Oid *scan_reuse_relids;
    int scan_reuse_relids_count;
    int scan_reuse_relids_cap;
    uint64 empty_short_circuit_hits;
    double policy_hub_prop_ms_total;
    double policy_sat_ms_total;
    double policy_sid_build_ms_total;
    uint64 policy_allowed_sids_total;
    uint64 policy_total_sids_total;
    long rss_kb_before_eval;
    long rss_kb_after_eval;
    long rss_kb_after_load;
    long rss_kb_after_engine;
    long rss_kb_after_ctid;
    long rss_kb_end;
    long peak_rss_kb_end;

    
    uint64 build_seq;
    uint64 policy_eval_calls;
    uint64 artifact_load_calls;
    uint64 policy_run_calls;
    uint64 allow_build_calls;
    uint64 blk_index_build_calls;
} PolicyQueryState;








static inline uint64
cf_fnv1a64_update(uint64 h, const void *data, size_t len)
{
    const unsigned char *p = (const unsigned char *) data;
    while (len--)
    {
        h ^= (uint64) (*p++);
        h *= 1099511628211ULL;
    }
    return h;
}

static uint64
cf_filters_guard_compute_hash(const PolicyQueryState *qs)
{
    
    uint64 h = 1469598103934665603ULL;
    if (!qs)
        return h;

    h = cf_fnv1a64_update(h, &qs->n_filters, sizeof(qs->n_filters));
    if (!qs->filters || qs->n_filters <= 0)
        return h;

    for (int i = 0; i < qs->n_filters; i++)
    {
        const TableFilterState *tf = &qs->filters[i];
        h = cf_fnv1a64_update(h, &tf->relid, sizeof(tf->relid));
        size_t rn = strnlen(tf->relname, NAMEDATALEN);
        h = cf_fnv1a64_update(h, &rn, sizeof(rn));
        if (rn > 0)
            h = cf_fnv1a64_update(h, tf->relname, rn);
        h = cf_fnv1a64_update(h, &tf->n_rows, sizeof(tf->n_rows));
        h = cf_fnv1a64_update(h, &tf->block_words, sizeof(tf->block_words));
        h = cf_fnv1a64_update(h, &tf->block_ids, sizeof(tf->block_ids));
        h = cf_fnv1a64_update(h, &tf->blocks, sizeof(tf->blocks));
        h = cf_fnv1a64_update(h, &tf->total_blocks, sizeof(tf->total_blocks));
        h = cf_fnv1a64_update(h, &tf->block_words_nbytes, sizeof(tf->block_words_nbytes));
        h = cf_fnv1a64_update(h, &tf->block_ids_nbytes, sizeof(tf->block_ids_nbytes));
        h = cf_fnv1a64_update(h, &tf->allowed_rows, sizeof(tf->allowed_rows));
        h = cf_fnv1a64_update(h, &tf->allow_is_empty, sizeof(tf->allow_is_empty));
    }

    return h;
}

static const char *
cf_mctx_safe_name(MemoryContext mctx)
{
    if (!mctx)
        return "<null>";
    if (mctx->ident)
        return mctx->ident;
    if (mctx->name)
        return mctx->name;
    return "<unnamed>";
}

static void
cf_filters_guard_set(PolicyQueryState *qs, const char *phase)
{
    if (!qs)
        return;
    qs->filters_guard_hash = cf_filters_guard_compute_hash(qs);
    qs->filters_guard_set = true;
    qs->filters_guard_reported = false;
    qs->filters_guard_last_ok_phase = phase;
}

static void
cf_filters_guard_check(PolicyQueryState *qs, const char *phase)
{
    if (!cf_debug_ids || !qs || !qs->filters_guard_set)
        return;

    uint64 h = cf_filters_guard_compute_hash(qs);
    if (h == qs->filters_guard_hash)
    {
        qs->filters_guard_last_ok_phase = phase;
        return;
    }

    if (qs->filters_guard_reported)
        return;

    
    qs->filters_guard_reported = true;

    uintptr_t start = (uintptr_t) qs->filters;
    uintptr_t end = start + (uintptr_t) qs->n_filters * (uintptr_t) sizeof(TableFilterState);

    StringInfoData msg;
    initStringInfo(&msg);
    appendStringInfo(&msg,
                     "CF_GUARD_CHANGED pid=%d qs=%p build_seq=%llu phase=%s last_ok=%s "
                     "filters_ptr=%p range=[0x%lx,0x%lx) n_filters=%d old_hash=%llu new_hash=%llu",
                     (int) getpid(),
                     (void *) qs,
                     (unsigned long long) qs->build_seq,
                     phase ? phase : "<null>",
                     qs->filters_guard_last_ok_phase ? qs->filters_guard_last_ok_phase : "<unset>",
                     (void *) qs->filters,
                     (unsigned long) start,
                     (unsigned long) end,
                     qs->n_filters,
                     (unsigned long long) qs->filters_guard_hash,
                     (unsigned long long) h);

    
    int lim = qs->n_filters;
    if (lim > 32)
        lim = 32;
    for (int i = 0; i < lim; i++)
    {
        const TableFilterState *tf = &qs->filters[i];
        appendStringInfo(&msg,
                         " f%d(tf=%p relid=%u rel=%s block_words=%p blocks=%u bytes=%zu rows=%u)",
                         i,
                         (void *) tf,
                         (unsigned int) tf->relid,
                         tf->relname[0] ? tf->relname : "<unknown>",
                         (void *) tf->block_words,
                         (unsigned int) tf->blocks,
                         tf->block_words_nbytes,
                         tf->n_rows);
    }
    if (qs->n_filters > lim)
        appendStringInfoString(&msg, " ...");

    CF_METRICS_LOG(NOTICE, "%s", msg.data);
}

typedef struct LoadedArtifact
{
    char *name;
    bytea *data;
    void *raw_data;
    size_t len;
    bool owned;
} LoadedArtifact;

#include "sf100_chunks.inc"

typedef struct PolicyArtifactLookupContext
{
    MemoryContext mcxt;
    LoadedArtifact *loaded;
    int loaded_count;
    int loaded_cap;
    double load_ms;
    uint64 bytes_loaded;
    bool sealed;
    char **absent;
    int absent_count;
} PolicyArtifactLookupContext;

typedef struct ArtifactNameIndexEntry
{
    char key[MAXPGPATH];
    int idx;
} ArtifactNameIndexEntry;

static MemoryContext cf_query_cxt = NULL;
static PolicyQueryState *cf_query_state = NULL;
static PlannedStmt *cf_query_plannedstmt = NULL;
static uint64 cf_query_build_seq = 0;

static const char *
cf_rtekind_name(int k)
{
    switch (k)
    {
        case RTE_RELATION: return "RELATION";
        case RTE_SUBQUERY: return "SUBQUERY";
        case RTE_JOIN: return "JOIN";
        case RTE_FUNCTION: return "FUNCTION";
        case RTE_TABLEFUNC: return "TABLEFUNC";
        case RTE_VALUES: return "VALUES";
        case RTE_CTE: return "CTE";
        case RTE_NAMEDTUPLESTORE: return "NAMEDTUPLESTORE";
        case RTE_RESULT: return "RESULT";
        default: break;
    }
    return "OTHER";
}

static void
cf_debug_log_scan_ids(const char *event, CfExec *st, CustomScanState *node)
{
    if (!cf_debug_ids || !event || !st || !node)
        return;

    CustomScan *cscan = (CustomScan *) node->ss.ps.plan;
    EState *estate = node->ss.ps.state;

    Index scanrelid = 0;
    const char *rtekind = "<none>";
    Oid rte_relid_oid = InvalidOid;
    const char *rte_relname = "<none>";
    if (cscan)
        scanrelid = cscan->scan.scanrelid;
    if (estate && scanrelid > 0)
    {
        RangeTblEntry *rte = rt_fetch(scanrelid, estate->es_range_table);
        if (rte)
        {
            rtekind = cf_rtekind_name((int) rte->rtekind);
            rte_relid_oid = rte->relid;
            if (rte_relid_oid != InvalidOid)
            {
                const char *rn = get_rel_name(rte_relid_oid);
                if (rn)
                    rte_relname = rn;
            }
        }
    }

    PolicyQueryState *qs = cf_query_state;
    bool should_filter = false;
    bool in_targets = false;
    bool scanned = false;
    bool wrapped = false;
    if (qs && st->relname[0])
    {
        in_targets = cf_table_in_list(st->relname, qs->policy_targets, qs->n_policy_targets);
        scanned = cf_table_scanned(qs, st->relname);
        should_filter = cf_table_should_filter(qs, st->relname);
        wrapped = cf_table_wrapped(qs, st->relname);
    }

    CF_DEBUG_IDS_LOG("pid=%d build_seq=%llu qs=%p node=%p plan=%p event=%s "
                     "scanrelid=%d rtekind=%s rte_relid_oid=%u rte_relname=%s "
                     "st_relid=%u st_relname=%s st_scan=%s "
                     "need_rebind=%d bound_build_seq=%llu "
                     "should_filter=%d in_policy_targets=%d scanned=%d wrapped=%d "
                     "filter_ptr=%p filter_block_words=%p filter_found=%d",
                     (int) getpid(),
                     (unsigned long long) (qs ? qs->build_seq : 0),
                     (void *) qs,
                     (void *) st,
                     (void *) node->ss.ps.plan,
                     event,
                     (int) scanrelid,
                     rtekind,
                     rte_relid_oid,
                     rte_relname,
                     st->relid,
                     st->relname[0] ? st->relname : "<unknown>",
                     st->scan_type ? st->scan_type : "<unknown>",
                     st->need_filter_rebind ? 1 : 0,
                     (unsigned long long) st->bound_build_seq,
                     should_filter ? 1 : 0,
                     in_targets ? 1 : 0,
                     scanned ? 1 : 0,
                     wrapped ? 1 : 0,
                     (void *) st->filter,
                     (void *) (st->filter ? st->filter->block_words : NULL),
                     st->filter ? 1 : 0);
}

static PolicyQueryState *
cf_ensure_query_state(EState *estate, const char *query_str, PlannedStmt *pstmt)
{
    if (!estate || !estate->es_query_cxt)
        return cf_query_state;

    MemoryContext qctx = estate->es_query_cxt;
    












    if (cf_query_state && cf_query_cxt &&
        (cf_query_cxt == qctx || cf_memory_context_contains(cf_query_cxt, qctx)))
        return cf_query_state;

    cf_query_state = cf_build_query_state(estate, query_str);
    cf_query_cxt = qctx;
    cf_query_plannedstmt = pstmt ? pstmt : estate->es_plannedstmt;
    return cf_query_state;
}

static PolicyQueryState *
cf_force_rebuild_query_state(EState *estate, const char *query_str, PlannedStmt *pstmt)
{
    if (!estate || !estate->es_query_cxt)
        return cf_query_state;
    if (cf_in_internal_query)
        return cf_query_state;
    cf_query_state = cf_build_query_state(estate, query_str);
    cf_query_cxt = estate->es_query_cxt;
    cf_query_plannedstmt = pstmt ? pstmt : estate->es_plannedstmt;
    return cf_query_state;
}

static void
cf_executor_start(QueryDesc *queryDesc, int eflags)
{
    PlannedStmt *pstmt = NULL;

    









    cf_in_executor_start_init = true;
    PG_TRY();
    {
        if (prev_ExecutorStart_hook)
            prev_ExecutorStart_hook(queryDesc, eflags);
        else
            standard_ExecutorStart(queryDesc, eflags);
    }
    PG_FINALLY();
    {
        cf_in_executor_start_init = false;
    }
    PG_END_TRY();

    if (!cf_enabled || cf_in_internal_query || !queryDesc || !queryDesc->estate)
        return;

    pstmt = queryDesc->plannedstmt;
    if (!pstmt || pstmt->commandType != CMD_SELECT)
        return;

    if (cf_query_state)
        cf_reset_query_exec_metrics(cf_query_state);

    instr_time init_start, init_end;
    INSTR_TIME_SET_CURRENT(init_start);
    PolicyQueryState *qs = cf_ensure_query_state(queryDesc->estate,
                                                 cf_current_policy_query_sql(),
                                                 pstmt);
    INSTR_TIME_SET_CURRENT(init_end);
    cf_log_wrapper_audit(pstmt);
    if (qs)
    {
        qs->executor_init_ms_ours += INSTR_TIME_GET_MILLISEC(init_end) - INSTR_TIME_GET_MILLISEC(init_start);
        const char *reason = "none";
        const char *empty_rel = NULL;
        bool any_empty = cf_query_has_empty_allow_set(qs, &empty_rel);
        bool safe_plan = false;

        qs->query_short_circuit_empty = false;
        qs->query_short_circuit_decided = true;
        qs->query_short_circuit_reason[0] = '\0';

        if (!any_empty)
            reason = "no_empty_allow";
        else
        {
            safe_plan = cf_plan_inner_only_safe(pstmt->planTree, &reason);
            if (safe_plan)
            {
                qs->query_short_circuit_empty = true;
                reason = "inner_only_empty";
            }
        }

        strlcpy(qs->query_short_circuit_reason, reason, sizeof(qs->query_short_circuit_reason));
        if (cf_profile_query && cf_profile_query[0])
        {
            CF_METRICS_LOG(NOTICE,
                 "query_short_circuit_decision: enabled=%d reason=%s empty_rel=%s",
                 qs->query_short_circuit_empty ? 1 : 0,
                 qs->query_short_circuit_reason[0] ? qs->query_short_circuit_reason : "none",
                 empty_rel ? empty_rel : "none");
        }
    }
}

static void
cf_reset_query_exec_metrics(PolicyQueryState *qs)
{
    if (!qs)
        return;

    qs->scanned_collect_ms = 0.0;
    qs->seqqual_collect_ms = 0.0;
    qs->policy_run_wall_ms = 0.0;
    qs->artifact_load_ms = 0.0;
    qs->artifact_parse_ms = 0.0;
    qs->atoms_ms = 0.0;
    qs->propagate_ms = 0.0;
    qs->project_ms = 0.0;
    qs->project_mask_ms = 0.0;
    qs->project_row_ms = 0.0;
    qs->project_mask_bytes = 0;
    qs->project_n_join_evals_max = 0;
    qs->project_clause_words_max = 0;
    qs->decode_ms = 0.0;
    qs->policy_total_ms = 0.0;
    qs->ctid_map_ms = 0.0;
    qs->allow_build_ms = 0.0;
    qs->executor_init_ms_ours = 0.0;
    qs->filter_ms = 0.0;
    qs->child_exec_ms = 0.0;
    qs->ctid_extract_ms = 0.0;
    qs->ctid_to_rid_ms = 0.0;
    qs->allow_check_ms = 0.0;
    qs->projection_ms = 0.0;
    qs->child_next_calls_total = 0;
    qs->total_filter_rows = 0;
    qs->total_allow_rows = 0;
    qs->rows_seen = 0;
    qs->rows_passed = 0;
    qs->ctid_misses = 0;
    qs->scan_mode_tid_tables = 0;
    qs->scan_mode_filter_tables = 0;
    qs->scan_mode_empty_tables = 0;
    qs->scan_mode_all_tables = 0;
    qs->tid_blocks_visited = 0;
    qs->tid_tuples_fetched = 0;
    qs->tid_offsets_checked = 0;
    qs->tid_offsets_passed = 0;
    qs->tid_fetch_ms = 0.0;
    qs->tid_qual_ms = 0.0;
    qs->tid_heap_fetch_ms = 0.0;
    qs->tid_slot_store_ms = 0.0;
    qs->tid_visibility_ms = 0.0;
    qs->scan_reuse_hits = 0;
    qs->scan_reuse_misses = 0;
    qs->scan_reuse_ms_saved = 0.0;
    qs->scan_reuse_relids_count = 0;
    qs->empty_short_circuit_hits = 0;
    qs->policy_hub_prop_ms_total = 0.0;
    qs->policy_sat_ms_total = 0.0;
    qs->policy_sid_build_ms_total = 0.0;
    qs->policy_allowed_sids_total = 0;
    qs->policy_total_sids_total = 0;
    qs->prop_join_scans_total = 0;
    qs->proj_sig_total = 0;
    qs->proj_sig_count = 0;
    qs->proj_sig_new = 0;
    qs->proj_sig_skipped = 0;
    qs->bin_build_hub_count = 0;
    qs->bin_count_final = 0;
    qs->bin_build_rows_scanned = 0;
    qs->bytes_artifact_buffers_retained = 0;
    qs->bytes_decoded_buffers_retained = 0;
    qs->restrict_sig_bytes_total = 0;
    qs->bytes_sig_ctid_masks = 0;
    qs->bytes_block_words = 0;
    qs->prop_table_scans = NULL;
    qs->custom_scan_total_ms = 0.0;
    qs->custom_scan_overhead_ms = 0.0;
    qs->rss_kb_after_ctid = -1;
    qs->rss_kb_end = -1;
    qs->peak_rss_kb_end = 0;
}

static void
cf_executor_run(QueryDesc *queryDesc, ScanDirection direction, uint64 count, bool execute_once)
{
    












    if (prev_ExecutorRun_hook)
        prev_ExecutorRun_hook(queryDesc, direction, count, execute_once);
    else
        standard_ExecutorRun(queryDesc, direction, count, execute_once);
}

static void
cf_log_query_metrics(PolicyQueryState *qs)
{
    if (!qs)
        return;
    if (!cf_profile_query || !cf_profile_query[0])
        return;
    CF_METRICS_LOG(NOTICE,
         "policy_profile: scan_filter_ms=%.3f filter_ms=%.3f total_rows=%llu allow_rows=%llu fetched_rows=%llu rows_passed=%llu "
         "policy_eval_ms_total=%.3f allow_build_ms=%.3f artifact_load_ms=%.3f decode_ms=%.3f "
         "rows_scanned=%llu hubs=%llu edges=%llu classes_total=%llu classes_per_hub=%s "
         "target_classes_support=%llu target_classes_demand=%llu sat_profiles=%llu sat_allowed_profiles=%llu "
         "bytes_artifact_buffers_retained=%zu bytes_decoded_buffers_retained=%zu bytes_transfer_summaries=%zu bytes_target_row_to_class=%zu bytes_block_words=%zu",
         qs->filter_ms,
         qs->filter_ms,
         (unsigned long long)qs->total_filter_rows,
         (unsigned long long)qs->total_allow_rows,
         (unsigned long long)qs->rows_seen,
         (unsigned long long)qs->rows_passed,
         qs->policy_total_ms,
         qs->allow_build_ms,
         qs->artifact_load_ms,
         qs->decode_ms,
         (unsigned long long) qs->bin_build_rows_scanned,
         (unsigned long long) qs->bin_build_hub_count,
         (unsigned long long) qs->prop_join_scans_total,
         (unsigned long long) qs->bin_count_final,
         (qs->prop_table_scans && qs->prop_table_scans[0]) ? qs->prop_table_scans : "none",
         (unsigned long long) (qs->proj_sig_new + qs->proj_sig_skipped),
         (unsigned long long) qs->proj_sig_new,
         (unsigned long long) qs->proj_sig_total,
         (unsigned long long) qs->proj_sig_count,
         qs->bytes_artifact_buffers_retained,
         qs->bytes_decoded_buffers_retained,
         qs->restrict_sig_bytes_total,
         qs->bytes_sig_ctid_masks,
         qs->bytes_block_words);
    CF_METRICS_LOG(NOTICE,
         "policy_profile_exec_stage03: scan_filter_ms=%.3f filter_ms=%.3f total_rows=%llu allow_rows=%llu fetched_rows=%llu rows_passed=%llu "
         "policy_eval_ms_total=%.3f allow_build_ms=%.3f artifact_load_ms=%.3f decode_ms=%.3f "
         "executor_init_ms=%.3f scanned_collect_ms=%.3f eval_ms=%.3f seqqual_collect_ms=%.3f policy_run_wall_ms=%.3f "
         "custom_scan_overhead_ms=%.3f projection_ms=%.3f tid_fetch_ms=%.3f tid_heap_fetch_ms=%.3f tid_qual_ms=%.3f tid_slot_store_ms=%.3f",
         qs->filter_ms,
         qs->filter_ms,
         (unsigned long long)qs->total_filter_rows,
         (unsigned long long)qs->total_allow_rows,
         (unsigned long long)qs->rows_seen,
         (unsigned long long)qs->rows_passed,
         qs->policy_total_ms,
         qs->allow_build_ms,
         qs->artifact_load_ms,
         qs->decode_ms,
         qs->executor_init_ms_ours,
         qs->scanned_collect_ms,
         qs->eval_ms,
         qs->seqqual_collect_ms,
         qs->policy_run_wall_ms,
         qs->custom_scan_overhead_ms,
         qs->projection_ms,
         qs->tid_fetch_ms,
         qs->tid_heap_fetch_ms,
         qs->tid_qual_ms,
         qs->tid_slot_store_ms);
}

static void
cf_query_state_reset_callback(void *arg)
{
    PolicyQueryState *qs = (PolicyQueryState *) arg;
    if (qs && !qs->metrics_logged)
    {
        if (cf_trace_enabled())
        {
            qs->rss_kb_end = cf_rss_kb_now();
            qs->peak_rss_kb_end = cf_peak_rss_kb();
        }
        cf_log_query_metrics(qs);
        qs->metrics_logged = true;
    }
    if (cf_query_state == qs)
    {
        cf_query_state = NULL;
        cf_query_cxt = NULL;
        cf_query_plannedstmt = NULL;
        cf_bound_policy_cache_reset();
    }
}

static bool
cf_has_suffix(const char *name, const char *suffix)
{
    if (!name || !suffix)
        return false;
    size_t nlen = strlen(name);
    size_t slen = strlen(suffix);
    if (nlen < slen)
        return false;
    return strcmp(name + (nlen - slen), suffix) == 0;
}

static char *
cf_files_table_sql_ident(void)
{
    const char *cfg = GetConfigOption("custom_filter_new.files_table", true, false);
    const char *raw = (cfg && cfg[0]) ? cfg : "public.files";
    const char *dot = strchr(raw, '.');
    if (dot && strchr(dot + 1, '.') == NULL)
    {
        char *schema = pnstrdup(raw, dot - raw);
        char *table = pstrdup(dot + 1);
        char *q = quote_qualified_identifier(schema, table);
        pfree(schema);
        pfree(table);
        return q;
    }
    return pstrdup(quote_identifier(raw));
}

static bool
cf_load_artifacts_batch(char **needed_files, int needed_count,
                        MemoryContext mcxt, LoadedArtifact *arts,
                        StringInfo missing)
{
    if (!needed_files || needed_count <= 0 || !arts)
        return true;
    for (int i=0;i<needed_count;++i)
        if (!pac_artifact_name_allowed(needed_files[i]))
            ereport(ERROR,(errmsg("Forbidden artifact: %s",needed_files[i])));
    if ((cf_artifact_directory && cf_artifact_directory[0]) || cf_chunked_artifacts)
        return cf_load_large_artifacts(needed_files,needed_count,mcxt,arts,missing);

    HASHCTL ctl;
    memset(&ctl, 0, sizeof(ctl));
    ctl.keysize = MAXPGPATH;
    ctl.entrysize = sizeof(ArtifactNameIndexEntry);
    ctl.hcxt = mcxt;
    HTAB *name_to_idx = hash_create("custom_filter_new artifact index",
                                    needed_count,
                                    &ctl,
                                    HASH_ELEM | HASH_STRINGS | HASH_CONTEXT);

    for (int i = 0; i < needed_count; i++)
    {
        bool found = false;
        ArtifactNameIndexEntry *ent =
            (ArtifactNameIndexEntry *) hash_search(name_to_idx, needed_files[i], HASH_ENTER, &found);
        if (ent)
            ent->idx = i;
    }

    Datum *arr_elems = (Datum *) palloc0(sizeof(Datum) * needed_count);
    for (int i = 0; i < needed_count; i++)
        arr_elems[i] = CStringGetTextDatum(needed_files[i]);

    ArrayType *name_arr = construct_array(arr_elems,
                                          needed_count,
                                          TEXTOID,
                                          -1,
                                          false,
                                          TYPALIGN_INT);

    char *files_table_sql = cf_files_table_sql_ident();
    char *sql = psprintf(
        "SELECT name, file "
        "FROM %s "
        "WHERE COALESCE(run_id,'') = COALESCE(current_setting('custom_filter_new.run_id', true), '') "
        "AND name = ANY($1::text[])",
        files_table_sql);
    Oid argtypes[1];
    Datum values[1];
    char nulls[1] = { ' ' };
    argtypes[0] = get_array_type(TEXTOID);
    if (!OidIsValid(argtypes[0]))
        ereport(ERROR, (errmsg("custom_filter_new: could not resolve text[] type oid")));

    values[0] = PointerGetDatum(name_arr);
    int spi_rc = SPI_execute_with_args(sql, 1, argtypes, values, nulls, true, 0);
    pfree(sql);
    pfree(files_table_sql);
    if (spi_rc != SPI_OK_SELECT)
        ereport(ERROR,
                (errmsg("custom_filter_new: batch artifact load failed (spi_rc=%d)", spi_rc)));

    TupleDesc tupdesc = SPI_tuptable->tupdesc;
    for (uint64 row = 0; row < SPI_processed; row++)
    {
        HeapTuple tup = SPI_tuptable->vals[row];
        bool isnull_name = false;
        Datum name_d = SPI_getbinval(tup, tupdesc, 1, &isnull_name);
        if (isnull_name)
            continue;
        char *name = TextDatumGetCString(name_d);

        bool found = false;
        ArtifactNameIndexEntry *ent =
            (ArtifactNameIndexEntry *) hash_search(name_to_idx, name, HASH_FIND, &found);
        if (!found || !ent)
        {
            pfree(name);
            continue;
        }

        bool isnull_file = false;
        Datum file_d = SPI_getbinval(tup, tupdesc, 2, &isnull_file);
        if (isnull_file)
        {
            pfree(name);
            continue;
        }

        bytea *payload = NULL;
        bool owned = false;
        



        MemoryContext oldctx = MemoryContextSwitchTo(mcxt);
        payload = (bytea *) PG_DETOAST_DATUM_COPY(file_d);
        MemoryContextSwitchTo(oldctx);
        owned = true;

        arts[ent->idx].data = payload;
        arts[ent->idx].len = (size_t) VARSIZE_ANY_EXHDR(payload);
        arts[ent->idx].owned = owned;
        pfree(name);
    }

    bool ok = true;
    for (int i = 0; i < needed_count; i++)
    {
        if (arts[i].data)
            continue;
        if (missing && missing->len > 0)
            appendStringInfoString(missing, ", ");
        if (missing)
            appendStringInfoString(missing, needed_files[i]);
        ok = false;
    }
    return ok;
}

static bool
cf_policy_lookup_artifact(void *ctx_ptr,
                          const char *artifact_name,
                          const void **data_out,
                          size_t *len_out)
{
    PolicyArtifactLookupContext *ctx = (PolicyArtifactLookupContext *) ctx_ptr;
    if (!ctx || !artifact_name || !artifact_name[0] || !data_out || !len_out)
        return false;
    if (!pac_artifact_name_allowed(artifact_name))
        ereport(ERROR,(errmsg("Forbidden artifact: %s",artifact_name)));

    for (int i = 0; i < ctx->loaded_count; i++)
    {
        if (ctx->loaded[i].name && strcmp(ctx->loaded[i].name, artifact_name) == 0)
        {
            *data_out = ctx->loaded[i].raw_data ? ctx->loaded[i].raw_data : (const void *) VARDATA_ANY(ctx->loaded[i].data);
            *len_out = ctx->loaded[i].raw_data ? ctx->loaded[i].len : (size_t) VARSIZE_ANY_EXHDR(ctx->loaded[i].data);
            return true;
        }
    }

    for (int i = 0; i < ctx->absent_count; ++i)
        if (strcmp(ctx->absent[i], artifact_name) == 0) return false;
    if (ctx->sealed)
        ereport(ERROR, (errmsg("artifact read attempted inside exec_ms: %s", artifact_name)));

    MemoryContext oldctx = MemoryContextSwitchTo(ctx->mcxt);
    if (ctx->loaded_count >= ctx->loaded_cap)
    {
        int new_cap = ctx->loaded_cap > 0 ? ctx->loaded_cap * 2 : 8;
        LoadedArtifact *new_loaded =
            (LoadedArtifact *) palloc0(sizeof(LoadedArtifact) * new_cap);
        if (ctx->loaded && ctx->loaded_count > 0)
            memcpy(new_loaded, ctx->loaded, sizeof(LoadedArtifact) * ctx->loaded_count);
        ctx->loaded = new_loaded;
        ctx->loaded_cap = new_cap;
    }

    LoadedArtifact *slot = &ctx->loaded[ctx->loaded_count];
    memset(slot, 0, sizeof(*slot));
    slot->name = pstrdup(artifact_name);

    char *needed_name = slot->name;
    StringInfoData missing;
    initStringInfo(&missing);
    instr_time load_start;
    instr_time load_end;
    INSTR_TIME_SET_CURRENT(load_start);
    bool ok = cf_load_artifacts_batch(&needed_name, 1, ctx->mcxt, slot, &missing);
    INSTR_TIME_SET_CURRENT(load_end);
    ctx->load_ms += INSTR_TIME_GET_MILLISEC(load_end) - INSTR_TIME_GET_MILLISEC(load_start);
    if (!ok || !slot->data)
    {
        ctx->absent = ctx->absent ? repalloc(ctx->absent, sizeof(char *) * (ctx->absent_count + 1))
                                 : palloc(sizeof(char *));
        ctx->absent[ctx->absent_count++] = pstrdup(artifact_name);
        MemoryContextSwitchTo(oldctx);
        return false;
    }

    if (!slot->raw_data) slot->len = (size_t) VARSIZE_ANY_EXHDR(slot->data);
    slot->owned = true;
    ctx->bytes_loaded += slot->len;
    ctx->loaded_count++;
    *data_out = slot->raw_data ? slot->raw_data : (const void *) VARDATA_ANY(slot->data);
    *len_out = slot->len;
    MemoryContextSwitchTo(oldctx);
    return true;
}



static TableFilterState *
cf_find_filter(PolicyQueryState *qs, Oid relid, bool log_on_miss)
{
    if (!qs || !qs->filters)
        return NULL;
    for (int i = 0; i < qs->n_filters; i++)
    {
        if (qs->filters[i].relid == relid)
            return &qs->filters[i];
    }
    if (cf_debug_ids && log_on_miss)
    {
        int n = qs->n_filters;
        if (n < 0) n = 0;
        int lim = n < 8 ? n : 8;
        StringInfoData buf;
        initStringInfo(&buf);
        appendStringInfo(&buf,
                         "CF_FIND_NULL qs=%p qs_build_seq=%llu needle_relid=%u n_filters=%d filters_ptr=%p",
                         (void *) qs,
                         (unsigned long long) qs->build_seq,
                         (unsigned int) relid,
                         qs->n_filters,
                         (void *) qs->filters);
        for (int i = 0; i < lim; i++)
        {
            TableFilterState *f = &qs->filters[i];
            appendStringInfo(&buf,
                             " f%d(relid=%u,name=%s,block_words=%p,rows=%u)",
                             i,
                             (unsigned int) f->relid,
                             f->relname[0] ? f->relname : "<unknown>",
                             (void *) f->block_words,
                             f->n_rows);
        }
        CF_METRICS_LOG(NOTICE, "%s", buf.data);
    }
    return NULL;
}

static void
cf_record_scan_reuse(PolicyQueryState *qs, Oid relid)
{
    if (!qs || !OidIsValid(relid))
        return;
    for (int i = 0; i < qs->scan_reuse_relids_count; i++)
    {
        if (qs->scan_reuse_relids[i] == relid)
        {
            qs->scan_reuse_hits++;
            if (qs->n_filters > 0 && qs->allow_build_ms > 0.0)
                qs->scan_reuse_ms_saved += (qs->allow_build_ms / (double) qs->n_filters);
            return;
        }
    }
    qs->scan_reuse_misses++;
    if (qs->scan_reuse_relids_count >= qs->scan_reuse_relids_cap)
    {
        int new_cap = (qs->scan_reuse_relids_cap > 0) ? (qs->scan_reuse_relids_cap * 2) : 8;
        size_t new_bytes = sizeof(Oid) * (size_t)new_cap;
        if (qs->scan_reuse_relids)
            qs->scan_reuse_relids = (Oid *) repalloc(qs->scan_reuse_relids, new_bytes);
        else
            qs->scan_reuse_relids = (Oid *) palloc(new_bytes);
        qs->scan_reuse_relids_cap = new_cap;
    }
    qs->scan_reuse_relids[qs->scan_reuse_relids_count++] = relid;
}

static PolicyQueryState *
cf_build_query_state(EState *estate, const char *query_str)
{
    for (size_t i = 0; i < lengthof(cf_perf_metrics); ++i)
        cf_perf_metrics[i].value = -1;
    /* These are accumulators, including when this query never uses windows. */
    cf_perf_metric_set("bound_record_skips", 0);
    cf_perf_metric_set("bound_record_refusals", 0);
    cf_perf_metric_set("global_window_complete_blocks", 0);
    MemoryContext qctx = estate && estate->es_query_cxt ? estate->es_query_cxt : CurrentMemoryContext;
    MemoryContext oldctx = MemoryContextSwitchTo(qctx);
    if (CurrentMemoryContext != qctx)
        ereport(ERROR,
                (errmsg("custom_filter_new: query state allocated outside query context"),
                 errdetail("qctx=%p(%s) current=%p(%s)",
                           (void *) qctx, cf_mctx_safe_name(qctx),
                           (void *) CurrentMemoryContext, cf_mctx_safe_name(CurrentMemoryContext))));

    PolicyQueryState *qs = (PolicyQueryState *) palloc0(sizeof(PolicyQueryState));
    qs->build_seq = ++cf_query_build_seq;
    qs->qctx = qctx;
    CF_RESCAN_LOG("event=query_state_begin pid=%d build_seq=%llu qs=%p qctx=%p",
                  (int) getpid(),
                  (unsigned long long) qs->build_seq,
                  (void *) qs,
                  (void *) qctx);
    bool profile_trace = (cf_trace_enabled());
    qs->rss_kb_before_eval = -1;
    qs->rss_kb_after_eval = -1;
    qs->rss_kb_after_load = -1;
    qs->rss_kb_after_engine = -1;
    qs->rss_kb_after_ctid = -1;
    qs->rss_kb_end = -1;
    qs->peak_rss_kb_end = -1;

    const char *policy_path = cf_template_policy_path() && cf_template_policy_path()[0] ? cf_template_policy_path() : NULL;
    if (!policy_path)
        ereport(ERROR, (errmsg("custom_filter_new.policy_template_path/custom_filter_new.policy_path is not set")));
    if (cf_contract_enabled())
        cf_log_policy_identity(policy_path);

    if (cf_debug_ids && estate && estate->es_plannedstmt)
    {
        int spcnt = estate->es_plannedstmt->subplans ? list_length(estate->es_plannedstmt->subplans) : 0;
        CF_DEBUG_SUBPLAN_LOG("pid=%d build_seq=%llu pstmt=%p subplans_count=%d walk_subplans=1",
                             (int) getpid(),
                             (unsigned long long) qs->build_seq,
                             (void *) estate->es_plannedstmt,
                             spcnt);
        if (estate->es_plannedstmt->subplans)
        {
            int idx = 0;
            ListCell *lc;
            foreach (lc, estate->es_plannedstmt->subplans)
            {
                Plan *sp = (Plan *) lfirst(lc);
                CF_DEBUG_SUBPLAN_LOG("pid=%d build_seq=%llu subplan_idx=%d walk=1 tag=%d ptr=%p",
                                     (int) getpid(),
                                     (unsigned long long) qs->build_seq,
                                     idx++,
                                     sp ? (int) nodeTag(sp) : -1,
                                     (void *) sp);
            }
        }
    }

    int main_rel_count = 0;
    int total_rel_count = 0;
    instr_time scanned_start, scanned_end;
    INSTR_TIME_SET_CURRENT(scanned_start);
    cf_collect_scanned_tables(estate, qctx,
                              &qs->scanned_tables, &qs->n_scanned_tables,
                              &qs->wrapped_tables, &qs->n_wrapped_tables,
                              &main_rel_count, &total_rel_count);
    INSTR_TIME_SET_CURRENT(scanned_end);
    qs->scanned_collect_ms = INSTR_TIME_GET_MILLISEC(scanned_end) - INSTR_TIME_GET_MILLISEC(scanned_start);
    if (cf_debug_ids)
    {
        CF_DEBUG_SUBPLAN_LOG("pid=%d build_seq=%llu scans_main=%d scans_total=%d scans_subplans_added=%d",
                             (int) getpid(),
                             (unsigned long long) qs->build_seq,
                             main_rel_count,
                             total_rel_count,
                             (total_rel_count >= main_rel_count) ? (total_rel_count - main_rel_count) : 0);
    }

    instr_time eval_start, eval_end;
    if (profile_trace)
        qs->rss_kb_before_eval = cf_rss_kb_now();
    INSTR_TIME_SET_CURRENT(eval_start);
    qs->policy_eval_calls++;
    PolicyEvalResultC *eval_res = cf_eval_policies_for_tables(query_str,
                                                              qs->scanned_tables,
                                                              qs->n_scanned_tables);
    INSTR_TIME_SET_CURRENT(eval_end);
    qs->eval_ms = INSTR_TIME_GET_MILLISEC(eval_end) - INSTR_TIME_GET_MILLISEC(eval_start);
    if (profile_trace)
        qs->rss_kb_after_eval = cf_rss_kb_now();
    if (!eval_res)
    {
        MemoryContextSwitchTo(oldctx);
        return qs;
    }
    qs->n_needed_files = eval_res->needed_count;
    if (qs->n_needed_files > 0)
    {
        qs->needed_files = (char **) palloc0(sizeof(char *) * qs->n_needed_files);
        for (int i = 0; i < qs->n_needed_files; i++)
            qs->needed_files[i] = pstrdup(eval_res->needed_files[i]);
        cf_prune_needed_files_for_policy_new(qs);
    }
    cf_augment_needed_files_for_walk(qs, eval_res);
    if (cf_diagnostic_logging && qs->n_needed_files > 0)
    {
        StringInfoData nf;
        initStringInfo(&nf);
        appendStringInfoChar(&nf, '[');
        for (int i = 0; i < qs->n_needed_files; i++)
        {
            if (i > 0)
                appendStringInfoString(&nf, ", ");
            appendStringInfoString(&nf, qs->needed_files[i]);
        }
        appendStringInfoChar(&nf, ']');
        CF_TRACE_LOG( "custom_filter_new: needed_files = %s", nf.data);
    }
    qs->n_policy_targets = cf_eval_effective_target_count(eval_res);
    if (qs->n_policy_targets > 0)
    {
        char **effective_target_tables = cf_eval_effective_target_tables(eval_res);
        qs->policy_targets = (char **) palloc0(sizeof(char *) * qs->n_policy_targets);
        for (int i = 0; i < qs->n_policy_targets; i++)
            qs->policy_targets[i] = pstrdup(effective_target_tables[i]);
        StringInfoData st;
        initStringInfo(&st);
        appendStringInfoChar(&st, '[');
        for (int i = 0; i < qs->n_policy_targets; i++)
        {
            if (i > 0)
                appendStringInfoString(&st, ", ");
            appendStringInfoString(&st, qs->policy_targets[i]);
        }
        appendStringInfoChar(&st, ']');
        CF_TRACE_LOG( "custom_filter_new: policy_targets = %s", st.data);
    }
    if (qs->n_policy_targets > 0)
    {
        StringInfoData st;
        initStringInfo(&st);
        appendStringInfoChar(&st, '[');
        for (int i = 0; i < qs->n_policy_targets; i++)
        {
            if (i > 0)
                appendStringInfoString(&st, ", ");
            appendStringInfoString(&st, qs->policy_targets[i] ? qs->policy_targets[i] : "<null>");
        }
        appendStringInfoChar(&st, ']');
        CF_TRACE_LOG( "policy_eval: target_tables=%s", st.data);
        for (int i = 0; i < eval_res->target_count; i++)
        {
            CF_TRACE_LOG( "policy_eval: combined_ast target=%s ast=%s",
                 eval_res->target_tables[i] ? eval_res->target_tables[i] : "<null>",
                 (eval_res->target_asts && eval_res->target_asts[i]) ? eval_res->target_asts[i] : "");
        }
    }
    qs->n_closure_tables = eval_res->closure_count;
    if (qs->n_closure_tables > 0)
    {
        qs->closure_tables = (char **) palloc0(sizeof(char *) * qs->n_closure_tables);
        for (int i = 0; i < qs->n_closure_tables; i++)
            qs->closure_tables[i] = pstrdup(eval_res->closure_tables[i]);
    }
    if (cf_contract_enabled() && qs->n_closure_tables > 0)
    {
        StringInfoData st;
        initStringInfo(&st);
        appendStringInfoChar(&st, '[');
        for (int i = 0; i < qs->n_closure_tables; i++)
        {
            if (i > 0)
                appendStringInfoString(&st, ", ");
            appendStringInfoString(&st, qs->closure_tables[i]);
        }
        appendStringInfoChar(&st, ']');
        CF_TRACE_LOG( "custom_filter_new: closure_tables = %s", st.data);
    }
    



    if (cf_trace_enabled())
    {
        cf_parse_query_targets(query_str ? query_str : "", qctx,
                               &qs->query_targets, &qs->n_query_targets);
        if (qs->n_query_targets > 0)
        {
            StringInfoData st;
            initStringInfo(&st);
            appendStringInfoChar(&st, '[');
            for (int i = 0; i < qs->n_query_targets; i++)
            {
                if (i > 0)
                    appendStringInfoString(&st, ", ");
                appendStringInfoString(&st, qs->query_targets[i]);
            }
            appendStringInfoChar(&st, ']');
            CF_TRACE_LOG( "custom_filter_new: query_targets = %s", st.data);
        }
    }
    if (qs->n_scanned_tables > 0)
    {
        StringInfoData st;
        initStringInfo(&st);
        appendStringInfoChar(&st, '[');
        for (int i = 0; i < qs->n_scanned_tables; i++)
        {
            if (i > 0)
                appendStringInfoString(&st, ", ");
            appendStringInfoString(&st, qs->scanned_tables[i]);
        }
        appendStringInfoChar(&st, ']');
        CF_TRACE_LOG( "custom_filter_new: scanned_tables = %s", st.data);
        for (int i = 0; i < qs->n_scanned_tables; i++)
        {
            const char *tbl = qs->scanned_tables[i];
            bool filtered = cf_table_should_filter(qs, tbl);
            CF_TRACE_LOG( "custom_filter_new: table=%s filter=%s",
                 tbl ? tbl : "<null>", filtered ? "on" : "off");
            if (cf_contract_enabled() && !filtered)
                CF_TRACE_LOG( "custom_filter_new: not_wrapping scan table=%s reason=no_policy_target",
                     tbl ? tbl : "<null>");
        }
    }

    if (eval_res && eval_res->target_joinclass_counts &&
        eval_res->target_joinclass_offsets && eval_res->target_joinclass_ids)
    {
        if (cf_contract_enabled())
        {
            for (int i = 0; i < eval_res->target_count; i++)
            {
                int cnt = eval_res->target_joinclass_counts[i];
                int off = eval_res->target_joinclass_offsets[i];
                StringInfoData list;
                initStringInfo(&list);
                for (int j = 0; j < cnt; j++)
                {
                    if (j > 0)
                        appendStringInfoString(&list, ", ");
                    appendStringInfo(&list, "%d", eval_res->target_joinclass_ids[off + j]);
                }
                CF_TRACE_LOG( "custom_filter_new: target=%s joinclass_count=%d joinclasses=[%s]",
                     (eval_res->target_tables && eval_res->target_tables[i]) ? eval_res->target_tables[i] : "<null>",
                     cnt, list.data);
            }
        }
        for (int i = 0; i < qs->n_scanned_tables; i++)
        {
            const char *tbl = qs->scanned_tables[i];
            if (!tbl || !cf_table_should_filter(qs, tbl))
                continue;
            int idx = cf_eval_target_index(eval_res, tbl);
            if (idx < 0)
                continue;
            int cnt = eval_res->target_joinclass_counts[idx];
            if (cnt > 1)
            {
                int off = eval_res->target_joinclass_offsets[idx];
                StringInfoData list;
                initStringInfo(&list);
                for (int j = 0; j < cnt; j++)
                {
                    if (j > 0)
                        appendStringInfoString(&list, ", ");
                    appendStringInfo(&list, "%d", eval_res->target_joinclass_ids[off + j]);
                }
                if (cf_contract_enabled()) {
                    CF_TRACE_LOG(
                         "custom_filter_new: multi-join-class policy detected (table=%s join_classes=[%s])",
                         tbl, list.data);
                }
            }
        }
    }

    





    if (qs->n_policy_targets > 0)
        cf_pin_backend_to_single_cpu();

    if (qs->n_policy_targets > 0 &&
        estate &&
        estate->es_plannedstmt &&
        estate->es_plannedstmt->parallelModeNeeded)
    {
        ereport(ERROR,
                (errmsg("custom_filter_new: parallel plans are forbidden for policy enforcement"),
                 errhint("ensure max_parallel_workers_per_gather=0, max_parallel_workers=0, and force_parallel_mode=off before planning the query")));
    }

    if (qs->n_wrapped_tables > 0 && cf_contract_enabled())
    {
        StringInfoData st;
        initStringInfo(&st);
        appendStringInfoChar(&st, '[');
        for (int i = 0; i < qs->n_wrapped_tables; i++)
        {
            if (i > 0)
                appendStringInfoString(&st, ", ");
            appendStringInfoString(&st, qs->wrapped_tables[i]);
        }
        appendStringInfoChar(&st, ']');
        CF_TRACE_LOG( "custom_filter_new: wrapped_tables = %s", st.data);
    }

    if (qs->n_policy_targets > 0 && qs->n_scanned_tables > 0)
    {
        for (int i = 0; i < qs->n_policy_targets; i++)
        {
            const char *tbl = qs->policy_targets[i];
            if (!tbl)
                continue;
            if (!cf_table_scanned(qs, tbl))
                continue;
            Oid nsp = get_namespace_oid("public", true);
            Oid relid = InvalidOid;
            if (OidIsValid(nsp))
                relid = get_relname_relid(tbl, nsp);
            if (!OidIsValid(relid))
                relid = get_relname_relid(tbl, InvalidOid);
            const char *stype = cf_plan_find_scan_type(estate->es_plannedstmt->planTree,
                                                       estate->es_plannedstmt,
                                                       relid);
            int scanned_occ = 0;
            int wrapped_occ = 0;
            if (OidIsValid(relid))
                cf_count_rel_occurrences(estate->es_plannedstmt, relid, &scanned_occ, &wrapped_occ);
            int target_occ_declared = 0;
            if (eval_res && eval_res->target_tables && eval_res->target_count > 0) {
                for (int ti = 0; ti < eval_res->target_count; ti++) {
                    if (eval_res->target_tables[ti] && strcmp(eval_res->target_tables[ti], tbl) == 0)
                        target_occ_declared++;
                }
            }
            if (cf_contract_enabled())
                CF_TRACE_LOG( "custom_filter_new: wrapper_coverage table=%s relid=%u scanned_occ=%d wrapped_occ=%d scan=%s",
                     tbl,
                     relid,
                     scanned_occ,
                     wrapped_occ,
                     stype ? stype : "<unknown>");
            if (scanned_occ > target_occ_declared && target_occ_declared > 0) {
                bool has_nonlocal_atoms = cf_target_has_nonlocal_atoms(eval_res, tbl);
                if (has_nonlocal_atoms) {
                    if (cf_contract_enabled()) {
                        CF_TRACE_LOG(
                             "custom_filter_new: repeated protected occurrences continuing with table-level enforcement "
                             "(table=%s scanned_occ=%d declared_target_occ=%d has_nonlocal_atoms=1)",
                             tbl,
                             scanned_occ,
                             target_occ_declared);
                    }
                } else if (cf_contract_enabled()) {
                    CF_TRACE_LOG(
                         "custom_filter_new: repeated occurrences allowed for local-only target table=%s scanned_occ=%d declared_target_occ=%d",
                         tbl,
                         scanned_occ,
                         target_occ_declared);
                }
            }
            if (stype && strcmp(stype, "IndexOnlyScan") == 0)
            {
                ereport(ERROR,
                        (errmsg("custom_filter_new: IndexOnlyScan unsupported for policy-required table (table=%s scan=%s)",
                                tbl, stype),
                         errhint("disable indexonlyscan or force heap scan")));
            }
            if (scanned_occ > 0 && wrapped_occ >= scanned_occ)
                continue;
            if (scanned_occ <= 0 && cf_table_wrapped(qs, tbl))
                continue;
            ereport(ERROR,
                    (errmsg("custom_filter_new: policy enforcement required but some occurrences are not wrapped "
                            "(table=%s scan=%s scanned_occ=%d wrapped_occ=%d)",
                            tbl,
                            stype ? stype : "<unknown>",
                            scanned_occ,
                            wrapped_occ),
                     errhint("ensure every protected scan occurrence is wrapped; disable unsupported scan kinds if needed")));
        }
    }

    if (qs->n_policy_targets == 0)
    {
        free_policy_eval_result(eval_res);
        eval_res = NULL;
        goto finalize;
    }

    bool spi_connected = false;
    LoadedArtifact *arts = NULL;
    const bool load_artifacts_on_demand = true;
    if (qs->n_needed_files > 0 && !load_artifacts_on_demand)
    {
        cf_in_internal_query = true;
        if (SPI_connect() != SPI_OK_CONNECT)
        {
            cf_in_internal_query = false;
            free_policy_eval_result(eval_res);
            MemoryContextSwitchTo(oldctx);
            return qs;
        }
        spi_connected = true;

        




        MemoryContextSwitchTo(qctx);
        if (cf_debug_ids)
        {
            CF_DEBUG_QS_LOG("pid=%d build_seq=%llu post_SPI_connect cur_mctx=%p(%s) qctx=%p(%s)",
                            (int) getpid(),
                            (unsigned long long) qs->build_seq,
                            (void *) CurrentMemoryContext,
                            cf_mctx_safe_name(CurrentMemoryContext),
                            (void *) qctx,
                            cf_mctx_safe_name(qctx));
        }

        arts = (LoadedArtifact *) palloc0(sizeof(LoadedArtifact) * qs->n_needed_files);
        StringInfoData missing;
        initStringInfo(&missing);
        instr_time load_start;
        INSTR_TIME_SET_CURRENT(load_start);

        for (int i = 0; i < qs->n_needed_files; i++)
        {
            arts[i].name = pstrdup(qs->needed_files[i]);
        }

        qs->artifact_load_calls++;
        if (!cf_load_artifacts_batch(qs->needed_files, qs->n_needed_files, qctx, arts, &missing))
        {
            
            MemoryContextSwitchTo(qctx);
            SPI_finish();
            cf_in_internal_query = false;
            free_policy_eval_result(eval_res);
            MemoryContextSwitchTo(oldctx);
            ereport(ERROR,
                    (errmsg("custom_filter_new: missing artifacts: %s", missing.data)));
        }
        
        MemoryContextSwitchTo(qctx);

        for (int i = 0; i < qs->n_needed_files; i++)
        {
            if (!arts[i].data)
                continue;
            qs->bytes_artifacts_loaded += arts[i].len;
            if (cf_contract_enabled())
                cf_contract_assert_chunk("artifact_blob", NULL, arts[i].data, qctx);
        }
        instr_time load_end;
        INSTR_TIME_SET_CURRENT(load_end);
        double load_ms = INSTR_TIME_GET_MILLISEC(load_end) - INSTR_TIME_GET_MILLISEC(load_start);
        CF_TRACE_LOG( "custom_filter_new: artifact_load_ms=%.3f", load_ms);
        qs->artifact_load_ms = load_ms;
        if (profile_trace)
            qs->rss_kb_after_load = cf_rss_kb_now();
        if (cf_contract_enabled()) {
            for (int i = 0; i < qs->n_needed_files; i++) {
                if (arts[i].name && arts[i].data) {
                    CF_TRACE_LOG( "custom_filter_new: artifact %s bytes=%zu",
                         arts[i].name, arts[i].len);
                }
            }
        }
    }

    PolicyArtifactCNew *policy_arts = (arts && qs->n_needed_files > 0)
                                       ? (PolicyArtifactCNew *) palloc0(sizeof(PolicyArtifactCNew) * qs->n_needed_files)
                                       : NULL;
    int policy_art_count = 0;
    for (int i = 0; arts && i < qs->n_needed_files; i++)
    {
        if (!arts[i].name || !arts[i].data)
            continue;
        policy_arts[policy_art_count].name = arts[i].name;
        policy_arts[policy_art_count].data = arts[i].raw_data ? arts[i].raw_data : (const void *) VARDATA_ANY(arts[i].data);
        policy_arts[policy_art_count].len = arts[i].raw_data ? arts[i].len : (size_t) VARSIZE_ANY_EXHDR(arts[i].data);
        policy_art_count++;
    }

    PolicyArtifactLookupContext lookup_ctx;
    memset(&lookup_ctx, 0, sizeof(lookup_ctx));
    lookup_ctx.mcxt = qctx;
    if (arts)
    {
        



        lookup_ctx.loaded = arts;
        lookup_ctx.loaded_count = qs->n_needed_files;
        lookup_ctx.loaded_cap = qs->n_needed_files;
        lookup_ctx.bytes_loaded = qs->bytes_artifacts_loaded;
    }

    bool policy_lookup_spi_connected = false;
    if (!spi_connected)
    {
        cf_in_internal_query = true;
        if (SPI_connect() == SPI_OK_CONNECT)
        {
            spi_connected = true;
            policy_lookup_spi_connected = true;
            MemoryContextSwitchTo(qctx);
        }
        else
        {
            cf_in_internal_query = false;
        }
    }

    PolicyRunHandleNew *run_handle = NULL;
    const PolicyAllowListCNew *allow_list = NULL;
    instr_time exec_start, exec_stop, teardown_start, teardown_stop;
    bool exec_started = false;
    bool teardown_started = false;
    if (eval_res->target_count > 0)
    {
        






        PolicyScanQualAtomC *scan_qual_atoms = NULL;
        int scan_qual_atom_count = 0;
        instr_time seqqual_start, seqqual_end;
        instr_time policy_run_start, policy_run_end;
        INSTR_TIME_SET_CURRENT(seqqual_start);
        cf_collect_seqscan_qual_atoms(estate, eval_res, qctx, &scan_qual_atoms, &scan_qual_atom_count);
        INSTR_TIME_SET_CURRENT(seqqual_end);
        qs->seqqual_collect_ms += INSTR_TIME_GET_MILLISEC(seqqual_end) - INSTR_TIME_GET_MILLISEC(seqqual_start);
        PolicyEngineInputC in;
        memset(&in, 0, sizeof(in));
        in.target_count = eval_res->target_count;
        in.target_tables = eval_res->target_tables;
        in.target_node_ids = eval_res->target_node_ids;
        in.target_asts = eval_res->target_asts;
        in.target_ast_tok_len = eval_res->target_ast_tok_len;
        in.target_ast_toks = eval_res->target_ast_toks;
        in.target_ast_tok_offsets = eval_res->target_ast_tok_offsets;
        in.target_ast_tok_counts = eval_res->target_ast_tok_counts;
        in.atoms = eval_res->atoms;
        in.atom_count = eval_res->atom_count;
        in.scan_qual_atoms = scan_qual_atoms;
        in.scan_qual_atom_count = scan_qual_atom_count;
        in.artifact_lookup_fn = cf_policy_lookup_artifact;
        in.artifact_lookup_ctx = &lookup_ctx;
        our_pg_preload_artifacts(&in);
        lookup_ctx.sealed = true;
        cf_perf_metric_set("artifact_discovery_input_ms", qs->eval_ms);
        /* Exact start: every artifact blob is now in backend memory. */
        INSTR_TIME_SET_CURRENT(exec_start);
        exec_started = true;
        INSTR_TIME_SET_CURRENT(eval_start);
        cf_bound_policy_cache_reset();
        PolicyEvalResultC *loaded_eval = cf_eval_policies_for_tables(query_str, qs->scanned_tables, qs->n_scanned_tables);
        INSTR_TIME_SET_CURRENT(eval_end);
        if (!loaded_eval) ereport(ERROR, (errmsg("post-load policy parsing failed")));
        free_policy_eval_result(eval_res);
        eval_res = loaded_eval;
        qs->eval_ms = INSTR_TIME_GET_MILLISEC(eval_end) - INSTR_TIME_GET_MILLISEC(eval_start);
        cf_collect_seqscan_qual_atoms(estate, eval_res, qctx, &scan_qual_atoms, &scan_qual_atom_count);
        memset(&in, 0, sizeof(in));
        in.target_count = eval_res->target_count;
        in.target_tables = eval_res->target_tables;
        in.target_table_ids = eval_res->target_table_ids;
        in.target_node_ids = eval_res->target_node_ids;
        in.target_asts = eval_res->target_asts;
        in.target_perm_asts = eval_res->target_perm_asts;
        in.target_rest_asts = eval_res->target_rest_asts;
        in.target_ast_tok_len = eval_res->target_ast_tok_len;
        in.target_ast_toks = eval_res->target_ast_toks;
        in.target_ast_tok_offsets = eval_res->target_ast_tok_offsets;
        in.target_ast_tok_counts = eval_res->target_ast_tok_counts;
        in.atom_count = eval_res->atom_count;
        in.atoms = eval_res->atoms;
        in.scan_qual_atom_count = scan_qual_atom_count;
        in.scan_qual_atoms = scan_qual_atoms;
        in.runtime_path = cf_runtime_path;
        in.class_phase_limit = cf_class_phase_limit;
        in.class_phase_timeout_ms = cf_class_phase_timeout_ms;
        in.artifact_lookup_fn = cf_policy_lookup_artifact;
        in.artifact_lookup_ctx = &lookup_ctx;
        in.scanned_count = eval_res->scanned_count;
        in.scanned_tables = eval_res->scanned_tables;
        in.policy_text = cf_read_policy_text_file(cf_policy_path, qctx);
        CF_TRACE_LOG( "custom_filter_new: calling policy_run once target_count=%d atom_count=%d",
             in.target_count, in.atom_count);
        MemoryContext old_policy_ctx = MemoryContextSwitchTo(qctx);
        qs->policy_run_calls++;
        INSTR_TIME_SET_CURRENT(policy_run_start);
        run_handle = policy_run_new(policy_arts, policy_art_count, &in);
        INSTR_TIME_SET_CURRENT(policy_run_end);
        MemoryContextSwitchTo(old_policy_ctx);
        qs->policy_run_wall_ms += INSTR_TIME_GET_MILLISEC(policy_run_end) - INSTR_TIME_GET_MILLISEC(policy_run_start);
        if (!run_handle)
            ereport(ERROR,
                    (errmsg("custom_filter_new: policy_run failed (target_count=%d atom_count=%d)",
                            in.target_count, in.atom_count)));
        const PolicyRunProfileCNew *pp = policy_run_profile_new(run_handle);
        if (pp) {
            qs->artifact_parse_ms += pp->artifact_parse_ms;
            qs->atoms_ms += pp->atoms_ms;
            qs->stamp_ms += pp->composite_stamp_ms;
            qs->propagate_ms += pp->propagate_ms;
            qs->project_ms += pp->project_allowset_ms;
            qs->bin_ms += pp->prop_bin_catalog_ms;
            qs->local_sat_ms += pp->sat_ms;
            qs->decode_ms += pp->decode_ms;
            qs->policy_total_ms += pp->policy_total_ms;
            qs->prop_join_scans_total += pp->prop_join_scans_total;
            qs->proj_sig_total += pp->proj_sig_total;
            qs->proj_sig_count += pp->proj_sig_count;
            qs->proj_sig_new += pp->proj_sig_new;
            qs->proj_sig_skipped += pp->proj_sig_skipped;
            qs->bin_build_hub_count += pp->bin_build_hub_count;
            qs->bin_count_final += pp->bin_count_final;
            qs->bin_build_rows_scanned += pp->bin_build_rows_scanned;
            qs->bytes_artifact_buffers_retained += pp->bytes_artifact_buffers_retained;
            qs->bytes_decoded_buffers_retained += pp->bytes_decoded_buffers_retained;
            qs->restrict_sig_bytes_total += pp->restrict_sig_bytes_total;
            qs->bytes_sig_ctid_masks += pp->bytes_sig_ctid_masks;
            qs->bytes_block_words += pp->bytes_block_words;
            if (pp->prop_table_scans && pp->prop_table_scans[0]) {
                qs->prop_table_scans = pstrdup(pp->prop_table_scans);
            }
        }
        qs->artifact_load_ms += lookup_ctx.load_ms;
        qs->bytes_artifacts_loaded += lookup_ctx.bytes_loaded;
        allow_list = policy_run_allow_list_new(run_handle);
        if (!allow_list)
            ereport(ERROR,
                    (errmsg("custom_filter_new: policy_run returned NULL allow list")));
        if (profile_trace)
            qs->rss_kb_after_engine = cf_rss_kb_now();
        for (int i = 0; cf_diagnostic_logging && i < allow_list->count; i++)
        {
            const PolicyTableAllowCNew *it = &allow_list->items[i];
            const char *tname = (it && it->table) ? it->table : "<null>";
            uint32 rows = it ? it->n_rows : 0;
            uint64 cnt = 0;
            if (it && it->block_words)
                cnt = cf_popcount_block_words(it->block_words, it->blocks);
            CF_TRACE_LOG( "custom_filter_new: allow_%s count=%llu/%u", tname, (unsigned long long) cnt, rows);
        }
    }

    if (policy_lookup_spi_connected && spi_connected)
    {
        MemoryContextSwitchTo(qctx);
        SPI_finish();
        cf_in_internal_query = false;
        spi_connected = false;
    }

    
    int n_filters = 0;
    if (allow_list && allow_list->count > 0)
    {
        for (int i = 0; i < allow_list->count; i++)
        {
            const PolicyTableAllowCNew *it = &allow_list->items[i];
            const char *tname = (it && it->table) ? it->table : NULL;
            if (!tname)
                continue;
            if (cf_table_should_filter(qs, tname))
                n_filters++;
        }
    }

    



    MemoryContextSwitchTo(qctx);

    qs->n_filters = n_filters;
    if (n_filters > 0)
    {
        



        if (CurrentMemoryContext != qctx)
            ereport(ERROR,
                    (errmsg("custom_filter_new: qs->filters allocated outside query context"),
                     errdetail("qctx=%p(%s) current=%p(%s)",
                               (void *) qctx, cf_mctx_safe_name(qctx),
                               (void *) CurrentMemoryContext, cf_mctx_safe_name(CurrentMemoryContext))));
        qs->filters_alloc_mctx = CurrentMemoryContext;
        if (cf_debug_ids)
        {
            CF_DEBUG_QS_LOG("pid=%d build_seq=%llu filters_alloc_site cur_mctx=%p(%s) qctx=%p(%s)",
                            (int) getpid(),
                            (unsigned long long) qs->build_seq,
                            (void *) CurrentMemoryContext,
                            cf_mctx_safe_name(CurrentMemoryContext),
                            (void *) qctx,
                            cf_mctx_safe_name(qctx));
        }
        qs->filters = (TableFilterState *) palloc0(sizeof(TableFilterState) * n_filters);
    }

    int fidx = 0;
    instr_time allow_build_start, allow_build_end;
    INSTR_TIME_SET_CURRENT(allow_build_start);
    if (allow_list && allow_list->count > 0)
    {
        for (int i = 0; i < allow_list->count; i++)
        {
            const PolicyTableAllowCNew *it = &allow_list->items[i];
            const char *tname = (it && it->table) ? it->table : NULL;
            if (!tname)
                continue;
            if (!cf_table_should_filter(qs, tname))
                continue;
            if (!it->block_words && it->blocks > 0)
                ereport(ERROR,
                        (errmsg("custom_filter_new[engine_error]: missing block_words for %s", tname)));

            TableFilterState *tf = &qs->filters[fidx++];
            qs->allow_build_calls++;
            memset(tf, 0, sizeof(TableFilterState));
            strlcpy(tf->relname, tname, sizeof(tf->relname));
            Oid nsp = get_namespace_oid("public", true);
            if (OidIsValid(nsp))
                tf->relid = get_relname_relid(tname, nsp);
            if (!OidIsValid(tf->relid))
                tf->relid = get_relname_relid(tname, InvalidOid);

            tf->n_rows = it->n_rows;
            tf->blocks = it->blocks;
            tf->total_blocks = it->total_blocks;
            tf->block_words_nbytes = (size_t)tf->blocks * (size_t)CF_WORDS_PER_BLOCK * sizeof(uint64);
            tf->block_ids_nbytes = (size_t)tf->blocks * sizeof(uint32);

            tf->block_words = NULL;
            tf->block_ids = NULL;
            if (it->block_words && tf->blocks > 0)
            {
                tf->block_words = (uint64 *) palloc(tf->block_words_nbytes);
                memcpy(tf->block_words, it->block_words, tf->block_words_nbytes);
            }
            if (it->block_ids && tf->blocks > 0)
            {
                tf->block_ids = (uint32 *) palloc(tf->block_ids_nbytes);
                memcpy(tf->block_ids, it->block_ids, tf->block_ids_nbytes);
            }
            tf->allowed_rows = it->allowed_rows;
            if (tf->allowed_rows == 0 && tf->block_words && tf->blocks > 0)
                tf->allowed_rows = cf_popcount_block_words(tf->block_words, tf->blocks);
            tf->allowed_sids = it->allowed_sids;
            tf->total_sids = it->total_sids;
            tf->policy_hub_prop_ms = it->hub_prop_ms;
            tf->policy_sat_ms = it->sat_ms;
            tf->policy_sid_build_ms = it->sid_build_ms;
            tf->mode_hint = it->mode_hint;
            tf->mode_reason[0] = '\0';
            if (it->mode_reason && it->mode_reason[0])
                strlcpy(tf->mode_reason, it->mode_reason, sizeof(tf->mode_reason));
            tf->allowed_density = (tf->n_rows > 0) ? ((double) tf->allowed_rows / (double) tf->n_rows) : 0.0;
            tf->allow_is_empty = (tf->allowed_rows == 0);
            tf->allow_is_all = (tf->n_rows > 0 && tf->allowed_rows >= tf->n_rows) ||
                               (tf->mode_hint == POLICY_MODE_HINT_ALL);
            qs->total_filter_rows += tf->n_rows;
            qs->total_allow_rows += tf->allowed_rows;
            qs->policy_hub_prop_ms_total += tf->policy_hub_prop_ms;
            qs->policy_sat_ms_total += tf->policy_sat_ms;
            qs->policy_sid_build_ms_total += tf->policy_sid_build_ms;
            qs->policy_allowed_sids_total += tf->allowed_sids;
            qs->policy_total_sids_total += tf->total_sids;

            qs->bytes_allow += tf->block_words_nbytes + tf->block_ids_nbytes;

            CF_TRACE_LOG("custom_filter_new: allow_%s blocks_alloc=%u total_blocks=%u words_bytes=%zu ids_bytes=%zu",
                         tname, tf->blocks, tf->total_blocks, tf->block_words_nbytes, tf->block_ids_nbytes);
            if (cf_profile_query && cf_profile_query[0])
                CF_METRICS_LOG(NOTICE,
                     "policy_target_phase: rel=%s hub_prop_ms=%.3f sat_ms=%.3f sid_access_build_ms=%.3f allowed_sids=%u total_sids=%u allowed_rows=%llu total_rows=%u density=%.6f",
                     tname,
                     tf->policy_hub_prop_ms,
                     tf->policy_sat_ms,
                     tf->policy_sid_build_ms,
                     tf->allowed_sids,
                     tf->total_sids,
                     (unsigned long long) tf->allowed_rows,
                     tf->n_rows,
                     tf->allowed_density);
        }
    }
    INSTR_TIME_SET_CURRENT(allow_build_end);
    qs->allow_build_ms += INSTR_TIME_GET_MILLISEC(allow_build_end) - INSTR_TIME_GET_MILLISEC(allow_build_start);

    qs->n_filters = fidx;
    /* Exact stop: custom-filter states now own the completed allow bitmaps. */
    if (exec_started) {
        INSTR_TIME_SET_CURRENT(exec_stop);
        cf_perf_metric_set("exec_start_us", INSTR_TIME_GET_MICROSEC(exec_start));
        cf_perf_metric_set("exec_stop_us", INSTR_TIME_GET_MICROSEC(exec_stop));
        cf_perf_metric_set("exec_ms", (INSTR_TIME_GET_MICROSEC(exec_stop) - INSTR_TIME_GET_MICROSEC(exec_start)) / 1000.0);
        INSTR_TIME_SET_CURRENT(teardown_start);
        teardown_started = true;
    }
    cf_perf_metric_set("artifact_mapping_ms", qs->artifact_load_ms);
    cf_perf_metric_set("policy_input_ms", qs->eval_ms);
    cf_perf_metric_set("policy_run_wall_ms", qs->policy_run_wall_ms);
    cf_perf_metric_set("allow_build_ms", qs->allow_build_ms);
    /* Bitmap handoff is complete; this teardown is outside exec_ms. */
    if (run_handle)
        (void) our_pg_release_runtime();
    if (profile_trace)
        qs->rss_kb_after_ctid = cf_rss_kb_now();

    for (int i = 0; arts && i < qs->n_needed_files; i++)
    {
        if (!arts[i].name || !arts[i].data)
            continue;
        if (!arts[i].owned)
            continue;
        size_t nlen = strlen(arts[i].name);
        if (nlen > 5 && cf_has_suffix(arts[i].name, "_ctid"))
            continue;
        pfree(arts[i].data);
        arts[i].data = NULL;
        arts[i].len = 0;
        arts[i].owned = false;
    }

    CF_TRACE_LOG( "custom_filter_new: retain total allow=%zuB ctid=%zuB blk_index=%zuB",
         qs->bytes_allow, qs->bytes_ctid, qs->bytes_blk_index);
    if (cf_contract_enabled() && qs->n_filters > 0)
    {
        for (int i = 0; i < qs->n_filters; i++)
        {
            TableFilterState *tf = &qs->filters[i];
            if (tf->block_words)
            {
                MemoryContext mctx = GetMemoryChunkContext(tf->block_words);
                CF_TRACE_LOG(
                     "custom_filter_new: block_words pre_exec rel=%s count=%llu rows=%u ptr=%p blocks=%u bytes=%zu mctx=%p qctx=%p qs=%p",
                     tf->relname,
                     (unsigned long long) tf->allowed_rows,
                     tf->n_rows,
                     (void *) tf->block_words,
                     (unsigned int) tf->blocks,
                     tf->block_words_nbytes,
                     (void *) mctx,
                     (void *) qctx,
                     (void *) qs);
            }
        }
    }

    




    if (spi_connected)
    {
        if (cf_debug_ids)
            cf_filters_guard_set(qs, "pre_SPI_finish");

        SPI_finish();
        if (cf_debug_ids)
            cf_filters_guard_check(qs, "post_SPI_finish");
        cf_in_internal_query = false;
    }
    free_policy_eval_result(eval_res);

    if (teardown_started)
    {
        INSTR_TIME_SET_CURRENT(teardown_stop);
        cf_perf_metric_set("teardown_ms", (INSTR_TIME_GET_MICROSEC(teardown_stop) - INSTR_TIME_GET_MICROSEC(teardown_start)) / 1000.0);
    }

finalize:
    qs->ready = true;
    if (qctx)
    {
        MemoryContextCallback *cb = (MemoryContextCallback *) MemoryContextAlloc(qctx, sizeof(MemoryContextCallback));
        cb->func = cf_query_state_reset_callback;
        cb->arg = qs;
        MemoryContextRegisterResetCallback(qctx, cb);
    }
    MemoryContextSwitchTo(oldctx);
    if (cf_debug_ids)
    {
        CF_DEBUG_QS_LOG("pid=%d build_seq=%llu qs=%p ready=%d n_filters=%d n_policy_targets=%d n_scanned_tables=%d n_wrapped_tables=%d",
                        (int) getpid(),
                        (unsigned long long) qs->build_seq,
                        (void *) qs,
                        qs->ready ? 1 : 0,
                        qs->n_filters,
                        qs->n_policy_targets,
                        qs->n_scanned_tables,
                        qs->n_wrapped_tables);
        for (int i = 0; i < qs->n_policy_targets; i++)
        {
            CF_DEBUG_QS_LOG("pid=%d build_seq=%llu target[%d]=%s",
                            (int) getpid(),
                            (unsigned long long) qs->build_seq,
                            i,
                            (qs->policy_targets && qs->policy_targets[i]) ? qs->policy_targets[i] : "<null>");
        }
        for (int i = 0; i < qs->n_scanned_tables; i++)
        {
            CF_DEBUG_QS_LOG("pid=%d build_seq=%llu scanned[%d]=%s",
                            (int) getpid(),
                            (unsigned long long) qs->build_seq,
                            i,
                            (qs->scanned_tables && qs->scanned_tables[i]) ? qs->scanned_tables[i] : "<null>");
        }
        for (int i = 0; i < qs->n_filters; i++)
        {
            TableFilterState *tf = &qs->filters[i];
            CF_DEBUG_QS_LOG("pid=%d build_seq=%llu filter[%d] key_relid=%u rel=%s block_words=%p blocks=%u bytes=%zu n_rows=%u",
                            (int) getpid(),
                            (unsigned long long) qs->build_seq,
                            i,
                            tf->relid,
                            tf->relname[0] ? tf->relname : "<unknown>",
                            (void *) tf->block_words,
                            (unsigned int) tf->blocks,
                            tf->block_words_nbytes,
                            tf->n_rows);
        }

        
        MemoryContext qs_mctx = GetMemoryChunkContext(qs);
        CF_DEBUG_QS_LOG("pid=%d build_seq=%llu memctx qctx=%p(%s) qs=%p qs_mctx=%p(%s) filters_ptr=%p filters_alloc_mctx=%p(%s) cur_mctx=%p(%s)",
                        (int) getpid(),
                        (unsigned long long) qs->build_seq,
                        (void *) qctx,
                        cf_mctx_safe_name(qctx),
                        (void *) qs,
                        (void *) qs_mctx,
                        cf_mctx_safe_name(qs_mctx),
                        (void *) qs->filters,
                        (void *) qs->filters_alloc_mctx,
                        cf_mctx_safe_name(qs->filters_alloc_mctx),
                        (void *) CurrentMemoryContext,
                        cf_mctx_safe_name(CurrentMemoryContext));
        for (int i = 0; i < qs->n_filters; i++)
        {
            TableFilterState *tf = &qs->filters[i];
            MemoryContext allow_mctx = tf->block_words ? GetMemoryChunkContext(tf->block_words) : NULL;
            CF_DEBUG_QS_LOG("pid=%d build_seq=%llu memctx rel=%s relid=%u block_words=%p mctx=%p(%s)",
                            (int) getpid(),
                            (unsigned long long) qs->build_seq,
                            tf->relname[0] ? tf->relname : "<unknown>",
                            (unsigned int) tf->relid,
                            (void *) tf->block_words,
                            (void *) allow_mctx,
                            cf_mctx_safe_name(allow_mctx));
        }
    }
    CF_RESCAN_LOG("event=query_state_ready pid=%d build_seq=%llu scanned_collect_ms=%.3f eval_calls=%llu eval_ms=%.3f seqqual_collect_ms=%.3f load_calls=%llu load_ms=%.3f policy_run_calls=%llu policy_run_wall_ms=%.3f policy_total_ms=%.3f allow_build_calls=%llu allow_build_ms=%.3f blk_index_build_calls=%llu n_filters=%d",
                  (int) getpid(),
                  (unsigned long long) qs->build_seq,
                  qs->scanned_collect_ms,
                  (unsigned long long) qs->policy_eval_calls,
                  qs->eval_ms,
                  qs->seqqual_collect_ms,
                  (unsigned long long) qs->artifact_load_calls,
                  qs->artifact_load_ms,
                  (unsigned long long) qs->policy_run_calls,
                  qs->policy_run_wall_ms,
                  qs->policy_total_ms,
                  (unsigned long long) qs->allow_build_calls,
                  qs->allow_build_ms,
                  (unsigned long long) qs->blk_index_build_calls,
                  qs->n_filters);
    return qs;
}

static bool
cf_slot_get_ctid(TupleTableSlot *slot, ItemPointerData *out, CfTidSource *src)
{
    if (src)
        *src = CF_TID_NONE;
    if (ItemPointerIsValid(&slot->tts_tid))
    {
        *out = slot->tts_tid;
        if (src) *src = CF_TID_TTS;
        return true;
    }

    bool should_free = false;
    HeapTuple htup = ExecFetchSlotHeapTuple(slot, false, &should_free);
    if (htup)
    {
        *out = htup->t_self;
        if (should_free)
            heap_freetuple(htup);
        if (src) *src = CF_TID_HEAPTUPLE;
        return ItemPointerIsValid(out);
    }

    



    if (slot->tts_ops && slot->tts_ops->getsysattr)
    {
        bool isnull = false;
        Datum d = slot_getsysattr(slot, SelfItemPointerAttributeNumber, &isnull);
        if (!isnull)
        {
            ItemPointer ip = DatumGetItemPointer(d);
            if (ItemPointerIsValid(ip))
            {
                *out = *ip;
                if (src) *src = CF_TID_SYSATTR;
                return true;
            }
        }
    }

    return false;
}

static TupleTableSlot *
cf_store_slot(CustomScanState *node, TupleTableSlot *slot)
{
    if (!node || !node->ss.ss_ScanTupleSlot || slot == node->ss.ss_ScanTupleSlot)
        return slot;
    return ExecCopySlot(node->ss.ss_ScanTupleSlot, slot);
}

static TupleTableSlot *
cf_scan_slot(PlanState *child, TupleTableSlot *fallback)
{
    if (!child)
        return fallback;

    switch (nodeTag(child))
    {
        case T_SeqScanState:
        case T_SampleScanState:
        case T_IndexScanState:
        case T_IndexOnlyScanState:
        case T_BitmapHeapScanState:
        case T_TidScanState:
        case T_TidRangeScanState:
        case T_ForeignScanState:
        case T_FunctionScanState:
        case T_TableFuncScanState:
        case T_ValuesScanState:
        case T_CteScanState:
        case T_WorkTableScanState:
            {
                ScanState *ss = (ScanState *) child;
                if (ss->ss_ScanTupleSlot)
                    return ss->ss_ScanTupleSlot;
            }
            break;
        default:
            break;
    }

    return fallback;
}

static bool
cf_query_has_empty_allow_set(const PolicyQueryState *qs, const char **table_out)
{
    if (table_out)
        *table_out = NULL;
    if (!qs || !qs->filters || qs->n_filters <= 0)
        return false;
    for (int i = 0; i < qs->n_filters; i++)
    {
        const TableFilterState *tf = &qs->filters[i];
        if (tf->allow_is_empty || tf->allowed_rows == 0 || tf->blocks == 0 || !tf->block_words)
        {
            if (table_out)
                *table_out = tf->relname[0] ? tf->relname : NULL;
            return true;
        }
    }
    return false;
}

static bool
cf_plan_inner_only_safe(Plan *plan, const char **reason_out)
{
    const char *reason = "ok";
    if (!plan)
    {
        if (reason_out)
            *reason_out = reason;
        return true;
    }

    switch (nodeTag(plan))
    {
        case T_NestLoop:
            if (((NestLoop *) plan)->join.jointype != JOIN_INNER)
            {
                reason = "not_safe_join";
                goto not_safe;
            }
            break;
        case T_MergeJoin:
            if (((MergeJoin *) plan)->join.jointype != JOIN_INNER)
            {
                reason = "not_safe_join";
                goto not_safe;
            }
            break;
        case T_HashJoin:
            if (((HashJoin *) plan)->join.jointype != JOIN_INNER)
            {
                reason = "not_safe_join";
                goto not_safe;
            }
            break;
        case T_Append:
            reason = "not_safe_append";
            goto not_safe;
        case T_MergeAppend:
            reason = "not_safe_append";
            goto not_safe;
        case T_RecursiveUnion:
            reason = "not_safe_setop";
            goto not_safe;
        case T_SetOp:
            reason = "not_safe_setop";
            goto not_safe;
        case T_SubqueryScan:
            reason = "not_safe_subquery";
            goto not_safe;
        case T_FunctionScan:
        case T_TableFuncScan:
        case T_WorkTableScan:
        case T_CteScan:
            reason = "not_safe_scan_type";
            goto not_safe;
        default:
            break;
    }

    if (!cf_plan_inner_only_safe(outerPlan(plan), reason_out))
        return false;
    if (!cf_plan_inner_only_safe(innerPlan(plan), reason_out))
        return false;

    switch (nodeTag(plan))
    {
        case T_Append:
            {
                Append *ap = (Append *) plan;
                ListCell *lc;
                foreach (lc, ap->appendplans)
                {
                    if (!cf_plan_inner_only_safe((Plan *) lfirst(lc), reason_out))
                        return false;
                }
            }
            break;
        case T_MergeAppend:
            {
                MergeAppend *ap = (MergeAppend *) plan;
                ListCell *lc;
                foreach (lc, ap->mergeplans)
                {
                    if (!cf_plan_inner_only_safe((Plan *) lfirst(lc), reason_out))
                        return false;
                }
            }
            break;
        case T_BitmapAnd:
            {
                BitmapAnd *ba = (BitmapAnd *) plan;
                ListCell *lc;
                foreach (lc, ba->bitmapplans)
                {
                    if (!cf_plan_inner_only_safe((Plan *) lfirst(lc), reason_out))
                        return false;
                }
            }
            break;
        case T_BitmapOr:
            {
                BitmapOr *bo = (BitmapOr *) plan;
                ListCell *lc;
                foreach (lc, bo->bitmapplans)
                {
                    if (!cf_plan_inner_only_safe((Plan *) lfirst(lc), reason_out))
                        return false;
                }
            }
            break;
        case T_CustomScan:
            {
                CustomScan *cs = (CustomScan *) plan;
                ListCell *lc;
                foreach (lc, cs->custom_plans)
                {
                    if (!cf_plan_inner_only_safe((Plan *) lfirst(lc), reason_out))
                        return false;
                }
            }
            break;
        default:
            break;
    }

    if (reason_out)
        *reason_out = reason;
    return true;

not_safe:
    if (reason_out)
        *reason_out = reason;
    return false;
}

static const char *
cf_scan_mode_name(CfScanMode m)
{
    switch (m)
    {
        case CF_SCAN_MODE_EMPTY:
            return "EMPTY";
        case CF_SCAN_MODE_ALL:
            return "ALL";
        case CF_SCAN_MODE_TID:
            return "TID";
        case CF_SCAN_MODE_FILTER:
        default:
            return "FILTER";
    }
}

static void
cf_update_scan_mode(CfExec *st, CustomScanState *node, TableFilterState *tf)
{
    CfScanMode new_mode = CF_SCAN_MODE_FILTER;
    double density = 0.0;
    double page_density = 0.0;
    const char *reason = "no_filter";
    PlanState *child = st ? st->child_plan : NULL;

    if (tf)
    {
        if (tf->n_rows > 0)
        {
            



            density = (double) tf->allowed_rows / (double) tf->n_rows;
        }
        else if (tf->total_blocks > 0)
        {
            density = (double) tf->blocks / (double) tf->total_blocks;
        }
        else
        {
            density = 0.0;
        }
        if (tf->total_blocks > 0)
            page_density = (double) tf->blocks / (double) tf->total_blocks;
        else
            page_density = 0.0;

        if (tf->allow_is_all || tf->mode_hint == POLICY_MODE_HINT_ALL)
        {
            new_mode = CF_SCAN_MODE_ALL;
            density = 1.0;
            reason = (tf->mode_reason[0] ? tf->mode_reason : "all_allow_set");
        }
        else if (tf->allow_is_empty || tf->mode_hint == POLICY_MODE_HINT_EMPTY || tf->allowed_rows == 0)
        {
            new_mode = CF_SCAN_MODE_EMPTY;
            density = 0.0;
            reason = (tf->mode_reason[0] ? tf->mode_reason : "empty_allow_set");
        }
        else if (tf->blocks == 0 || !tf->block_words || tf->block_words_nbytes == 0)
        {
            new_mode = CF_SCAN_MODE_EMPTY;
            density = 0.0;
            reason = "missing_allow_bitmap";
        }
        else if (tf->mode_hint == POLICY_MODE_HINT_FILTER)
        {
            new_mode = CF_SCAN_MODE_FILTER;
            reason = (tf->mode_reason[0] ? tf->mode_reason : "mode_hint_filter");
        }
        else if (tf->mode_hint == POLICY_MODE_HINT_TID)
        {
            




            if (!cf_tidscan_seqscan)
                reason = "tidscan_disabled";
            else if (!child)
                reason = "no_child_plan";
            else if (nodeTag(child) != T_SeqScanState)
                reason = "child_not_seqscan";
            else if (child->plan && child->plan->parallel_aware)
                reason = "parallel_aware";
            else
            {
                new_mode = CF_SCAN_MODE_TID;
                reason = (tf->mode_reason[0] ? tf->mode_reason : "mode_hint_tid");
            }
        }
        else
        {
            new_mode = CF_SCAN_MODE_FILTER;
            reason = (tf->mode_reason[0] ? tf->mode_reason : "allow_set_filter");
        }
    }

    if (!st)
        return;

    if (!st->scan_mode_set || st->scan_mode != new_mode)
    {
        st->scan_mode = new_mode;
        st->scan_mode_set = true;
        st->tid_iter_initialized = false;
        st->tid_iter_block_ord = 0;
        st->tid_iter_word_idx = 0;
        st->tid_iter_bit_min = 0;
    }
    st->scan_mode_density = density;

    if (!st->scan_mode_logged && tf && cf_trace_enabled())
    {
        CF_METRICS_LOG(NOTICE,
             "scan_mode_decision: rel=%s mode=%s allow_rows=%llu allow_blocks=%u relpages=%u density=%.6f page_density=%.6f reason=%s scan=%s",
             st->relname[0] ? st->relname : "<unknown>",
             cf_scan_mode_name(st->scan_mode),
             (unsigned long long) tf->allowed_rows,
             (unsigned int) tf->blocks,
             (unsigned int) tf->total_blocks,
             st->scan_mode_density,
             page_density,
             reason,
             st->scan_type ? st->scan_type : "<unknown>");
        st->scan_mode_logged = true;
    }
    (void) node;
}

static bool
cf_tid_iter_next(CfExec *st, TableFilterState *tf, ItemPointerData *out_tid)
{
    if (!st || !tf || !tf->block_words || !out_tid)
        return false;
    if (!st->tid_iter_initialized)
    {
        st->tid_iter_initialized = true;
        st->tid_iter_block_ord = 0;
        st->tid_iter_word_idx = 0;
        st->tid_iter_bit_min = 0;
    }

    while (st->tid_iter_block_ord < tf->blocks)
    {
        cf_periodic_interrupt_check(&st->interrupt_counter);
        const uint64 *bw = tf->block_words + (size_t) st->tid_iter_block_ord * (size_t) CF_WORDS_PER_BLOCK;
        BlockNumber blk = (BlockNumber) (tf->block_ids ? tf->block_ids[st->tid_iter_block_ord] : st->tid_iter_block_ord);

        if (st->tid_iter_word_idx == 0 && st->tid_iter_bit_min == 0)
            st->tid_blocks_visited++;

        while (st->tid_iter_word_idx < CF_WORDS_PER_BLOCK)
        {
            cf_periodic_interrupt_check(&st->interrupt_counter);
            uint64 w = bw[st->tid_iter_word_idx];
            if (st->tid_iter_bit_min > 0 && st->tid_iter_bit_min < 64)
                w &= ~((1ULL << st->tid_iter_bit_min) - 1ULL);
            else if (st->tid_iter_bit_min >= 64)
                w = 0;

            if (w != 0)
            {
                uint32 bit = (uint32) __builtin_ctzll(w);
                uint32 off0 = st->tid_iter_word_idx * 64u + bit;
                OffsetNumber off = (OffsetNumber) (off0 + 1u);
                ItemPointerSet(out_tid, blk, off);
                st->tid_iter_bit_min = bit + 1u;
                if (st->tid_iter_bit_min >= 64u)
                {
                    st->tid_iter_word_idx++;
                    st->tid_iter_bit_min = 0;
                }
                return true;
            }
            st->tid_iter_word_idx++;
            st->tid_iter_bit_min = 0;
        }

        st->tid_iter_block_ord++;
        st->tid_iter_word_idx = 0;
        st->tid_iter_bit_min = 0;
    }
    return false;
}

static inline bool
cf_block_offset_is_set(const uint64 *bw, uint32 off0)
{
    uint32 word_idx = off0 >> 6;
    uint32 bit = off0 & 63u;
    if (word_idx >= CF_WORDS_PER_BLOCK)
        return false;
    return (bw[word_idx] & (1ULL << bit)) != 0;
}

static bool
cf_tid_iter_next_range(CfExec *st, TableFilterState *tf,
                       ItemPointerData *out_min_tid,
                       ItemPointerData *out_max_tid)
{
    ItemPointerData first_tid;
    if (!cf_tid_iter_next(st, tf, &first_tid))
        return false;

    BlockNumber blk = ItemPointerGetBlockNumber(&first_tid);
    OffsetNumber off = ItemPointerGetOffsetNumber(&first_tid);
    if (off <= 0)
        return false;

    uint32 block_ord = st->tid_iter_block_ord;
    if (st->tid_iter_bit_min == 0 && st->tid_iter_word_idx == 0 && block_ord > 0)
        block_ord--;
    if (block_ord >= tf->blocks)
        return false;

    const uint64 *bw = tf->block_words + (size_t) block_ord * (size_t) CF_WORDS_PER_BLOCK;
    uint32 start_off0 = (uint32) off - 1u;
    uint32 end_off0 = start_off0;
    while (end_off0 + 1u < CF_MAX_OFF && cf_block_offset_is_set(bw, end_off0 + 1u))
        end_off0++;

    uint32 next_off0 = end_off0 + 1u;
    st->tid_iter_block_ord = block_ord;
    st->tid_iter_word_idx = next_off0 >> 6;
    st->tid_iter_bit_min = next_off0 & 63u;
    if (st->tid_iter_word_idx >= CF_WORDS_PER_BLOCK) {
        st->tid_iter_block_ord++;
        st->tid_iter_word_idx = 0;
        st->tid_iter_bit_min = 0;
    }

    ItemPointerSet(out_min_tid, blk, (OffsetNumber) (start_off0 + 1u));
    ItemPointerSet(out_max_tid, blk, (OffsetNumber) (end_off0 + 1u));
    return true;
}

static TupleTableSlot *
cf_exec_seqscan_tid_mode(CustomScanState *node, CfExec *st, TableFilterState *tf)
{
    if (!node || !st || !tf)
        ereport(ERROR,
                (errmsg("custom_filter_new: invalid TID mode state (node/st/filter is null)")));

    PlanState *child = st->child_plan;
    if (!child || nodeTag(child) != T_SeqScanState)
        ereport(ERROR,
                (errmsg("custom_filter_new: TID mode requires SeqScan child (rel=%s child_tag=%d)",
                        st->relname[0] ? st->relname : "<unknown>",
                        child ? (int) nodeTag(child) : -1)));
    Assert(nodeTag(child) == T_SeqScanState);

    ScanState *ss = (ScanState *) child;
    TupleTableSlot *scan_slot = ss->ss_ScanTupleSlot;
    EState *estate = node->ss.ps.state;
    Snapshot snap = estate ? estate->es_snapshot : InvalidSnapshot;
    ExprContext *econtext = child->ps_ExprContext;
    const bool need_qual = (child->qual != NULL);
    const bool need_proj = (child->ps_ProjInfo != NULL);
    const bool tupleless_fastpath =
        (st->tupleless_eligible &&
         !need_qual &&
         !need_proj);

    if (!ss->ss_currentRelation || !scan_slot || !snap)
        ereport(ERROR,
                (errmsg("custom_filter_new: SeqScan TID mode missing relation/slot/snapshot (rel=%s)",
                        st->relname[0] ? st->relname : "<unknown>")));

    if ((need_qual || need_proj) && !econtext)
    {
        econtext = CreateExprContext(child->state);
        child->ps_ExprContext = econtext;
    }

    if (cf_trace_enabled() && !st->tid_logged)
    {
        CF_TRACE_LOG("custom_filter_new: tid_mode rel=%s tupleless_eligible=%d need_qual=%d need_proj=%d tupleless_fastpath=%d",
                     st->relname[0] ? st->relname : "<unknown>",
                     st->tupleless_eligible ? 1 : 0,
                     need_qual ? 1 : 0,
                     need_proj ? 1 : 0,
                     tupleless_fastpath ? 1 : 0);
        st->tid_logged = true;
    }

    const bool profile_detail = cf_profile_rescan;

    if (tupleless_fastpath)
    {
        st->tupleless_fastpath = true;
        if (need_proj && !econtext)
        {
            econtext = CreateExprContext(child->state);
            child->ps_ExprContext = econtext;
        }
        for (;;)
        {
            cf_periodic_interrupt_check(&st->interrupt_counter);
            if (!st->tupleless_range_active)
            {
                ItemPointerData min_tid, max_tid;
                if (!cf_tid_iter_next_range(st, tf, &min_tid, &max_tid))
                    return ExecClearTuple(node->ss.ss_ScanTupleSlot);
                st->tid_offsets_checked++;
                st->tupleless_blk = ItemPointerGetBlockNumber(&min_tid);
                st->tupleless_next_off = ItemPointerGetOffsetNumber(&min_tid);
                st->tupleless_end_off = ItemPointerGetOffsetNumber(&max_tid);
                st->tupleless_range_active = true;
            }

            st->tuples_seen++;
            st->tuples_passed++;
            st->tid_offsets_passed++;
            if (tf)
            {
                tf->seen++;
                tf->passed++;
            }
            if (!st->tupleless_slot_ready)
            {
                ExecClearTuple(node->ss.ss_ScanTupleSlot);
                ExecStoreVirtualTuple(node->ss.ss_ScanTupleSlot);
                st->tupleless_slot_ready = true;
            }

            if (st->tupleless_next_off >= st->tupleless_end_off)
            {
                st->tupleless_range_active = false;
                st->tupleless_blk = InvalidBlockNumber;
                st->tupleless_next_off = InvalidOffsetNumber;
                st->tupleless_end_off = InvalidOffsetNumber;
            }
            else
            {
                st->tupleless_next_off++;
            }
            return cf_return_tuple(node);
        }
    }

    if (need_qual || need_proj)
    {
        for (;;)
        {
            cf_periodic_interrupt_check(&st->interrupt_counter);
            TupleTableSlot *slot;
            bool qual_ok = true;
            instr_time fetch_start, fetch_end;
            for (;;)
            {
                if (st->tidrange_active)
                {
                    if (profile_detail)
                        INSTR_TIME_SET_CURRENT(fetch_start);
                    ExecClearTuple(scan_slot);
                    if (table_scan_getnextslot_tidrange(st->tidrange_scan,
                                                        ForwardScanDirection,
                                                        scan_slot))
                    {
                        if (profile_detail)
                        {
                            double fetch_ms = 0.0;
                            INSTR_TIME_SET_CURRENT(fetch_end);
                            fetch_ms = INSTR_TIME_GET_MILLISEC(fetch_end) - INSTR_TIME_GET_MILLISEC(fetch_start);
                            st->tid_fetch_ms += fetch_ms;
                            st->tid_heap_fetch_ms += fetch_ms;
                            st->tid_visibility_ms += fetch_ms;
                        }
                        st->tid_tuples_fetched++;
                        st->tuples_seen++;
                        if (tf)
                            tf->seen++;
                        break;
                    }
                    table_endscan(st->tidrange_scan);
                    st->tidrange_scan = NULL;
                    st->tidrange_active = false;
                }

                ItemPointerData min_tid, max_tid;
                if (!cf_tid_iter_next_range(st, tf, &min_tid, &max_tid))
                    return ExecClearTuple(node->ss.ss_ScanTupleSlot);
                st->tid_offsets_checked++;
                if (!st->tidrange_scan)
                    st->tidrange_scan = table_beginscan_tidrange(ss->ss_currentRelation,
                                                                 snap,
                                                                 &min_tid,
                                                                 &max_tid);
                else
                    table_rescan_tidrange(st->tidrange_scan, &min_tid, &max_tid);
                st->tidrange_active = true;
            }

            instr_time qual_start, qual_end;
            if (profile_detail)
                INSTR_TIME_SET_CURRENT(qual_start);
            if (econtext)
                ResetExprContext(econtext);
            econtext->ecxt_scantuple = scan_slot;
            if (profile_detail)
            {
                if (need_qual)
                    qual_ok = ExecQual(child->qual, econtext);
                INSTR_TIME_SET_CURRENT(qual_end);
                st->tid_qual_ms += INSTR_TIME_GET_MILLISEC(qual_end) - INSTR_TIME_GET_MILLISEC(qual_start);
            }
            else if (need_qual)
            {
                qual_ok = ExecQual(child->qual, econtext);
            }
            if (!qual_ok)
                continue;

            slot = scan_slot;
            if (need_proj)
            {
                instr_time store_start, store_end;
                econtext->ecxt_scantuple = scan_slot;
                if (profile_detail)
                    INSTR_TIME_SET_CURRENT(store_start);
                slot = ExecProject(child->ps_ProjInfo);
                if (profile_detail)
                {
                    INSTR_TIME_SET_CURRENT(store_end);
                    st->tid_slot_store_ms += INSTR_TIME_GET_MILLISEC(store_end) - INSTR_TIME_GET_MILLISEC(store_start);
                }
            }
            if (cf_trace_enabled() &&
                (st->tid_tuples_fetched <= 3 ||
                 (st->tid_tuples_fetched % 50000ULL) == 0ULL))
            {
                CF_TRACE_LOG("custom_filter_new: tid_return_progress rel=%s fetched=%llu returned_slot=%p isnull=%d",
                             st->relname[0] ? st->relname : "<unknown>",
                             (unsigned long long) st->tid_tuples_fetched,
                             (void *) slot,
                             TupIsNull(slot) ? 1 : 0);
            }

            st->tuples_passed++;
            st->tid_offsets_passed++;
            if (tf)
                tf->passed++;
            return slot;
        }
    }

    for (;;)
    {
        cf_periodic_interrupt_check(&st->interrupt_counter);
        instr_time fetch_start, fetch_end;

        for (;;)
        {
            if (st->tidrange_active)
            {
                if (profile_detail)
                    INSTR_TIME_SET_CURRENT(fetch_start);
                ExecClearTuple(scan_slot);
                if (table_scan_getnextslot_tidrange(st->tidrange_scan, ForwardScanDirection, scan_slot))
                {
                    if (profile_detail)
                    {
                        INSTR_TIME_SET_CURRENT(fetch_end);
                        {
                            double fetch_ms = INSTR_TIME_GET_MILLISEC(fetch_end) - INSTR_TIME_GET_MILLISEC(fetch_start);
                            st->tid_fetch_ms += fetch_ms;
                            st->tid_heap_fetch_ms += fetch_ms;
                            st->tid_visibility_ms += fetch_ms;
                        }
                    }
                    st->tid_tuples_fetched++;
                    st->tuples_seen++;
                    if (tf)
                        tf->seen++;
                    break;
                }
                table_endscan(st->tidrange_scan);
                st->tidrange_scan = NULL;
                st->tidrange_active = false;
            }

            ItemPointerData min_tid, max_tid;
            if (!cf_tid_iter_next_range(st, tf, &min_tid, &max_tid))
                return ExecClearTuple(node->ss.ss_ScanTupleSlot);
            st->tid_offsets_checked++;
            if (!st->tidrange_scan)
                st->tidrange_scan = table_beginscan_tidrange(ss->ss_currentRelation, snap, &min_tid, &max_tid);
            else
                table_rescan_tidrange(st->tidrange_scan, &min_tid, &max_tid);
            st->tidrange_active = true;
        }

        st->tuples_passed++;
        st->tid_offsets_passed++;
        if (tf)
            tf->passed++;
        return scan_slot;
    }
}

static const char *
cf_tid_source_name(CfTidSource src)
{
    switch (src)
    {
        case CF_TID_TTS: return "tts_tid";
        case CF_TID_SYSATTR: return "sysattr";
        case CF_TID_MAT_TTS: return "materialized_tts_tid";
        case CF_TID_HEAPTUPLE: return "heaptuple";
        default: return "none";
    }
}

typedef struct ScannedCtx
{
    PlannedStmt *pstmt;
    List *relids;
    List *wrapped_relids;
} ScannedCtx;

typedef struct WrapperAuditCtx
{
    PlannedStmt *pstmt;
    int total_wrappers;
    int main_wrappers;
    int subplan_wrappers;
    int detail_count;
    StringInfo details;
} WrapperAuditCtx;

static void
cf_wrapper_audit_append(WrapperAuditCtx *ctx, CustomScan *cs, bool in_subplan, int subplan_idx)
{
    if (!ctx || !cs || !ctx->pstmt)
        return;

    int scanrelid = (int) cs->scan.scanrelid;
    Oid relid = InvalidOid;
    const char *relname = "<none>";
    const char *alias = "<none>";

    if (scanrelid > 0)
    {
        RangeTblEntry *rte = rt_fetch((Index) scanrelid, ctx->pstmt->rtable);
        if (rte)
        {
            relid = rte->relid;
            if (relid != InvalidOid)
            {
                const char *rn = get_rel_name(relid);
                if (rn)
                    relname = rn;
            }
            if (rte->eref && rte->eref->aliasname)
                alias = rte->eref->aliasname;
        }
    }

    ctx->total_wrappers++;
    if (in_subplan)
        ctx->subplan_wrappers++;
    else
        ctx->main_wrappers++;

    if (ctx->detail_count < 128)
    {
        appendStringInfo(ctx->details,
                         "%s{scanrelid=%d relid=%u rel=%s alias=%s subplan=%d subplan_idx=%d}",
                         (ctx->detail_count == 0 ? "" : ";"),
                         scanrelid,
                         relid,
                         relname,
                         alias,
                         in_subplan ? 1 : 0,
                         subplan_idx);
        ctx->detail_count++;
    }
}

static void
cf_wrapper_audit_walk(Plan *plan, WrapperAuditCtx *ctx, bool in_subplan, int subplan_idx)
{
    if (!plan || !ctx)
        return;

    if (IsA(plan, CustomScan))
    {
        CustomScan *cs = (CustomScan *) plan;
        if (cs->methods && cs->methods->CustomName &&
            strcmp(cs->methods->CustomName, "custom_filter_new") == 0)
        {
            cf_wrapper_audit_append(ctx, cs, in_subplan, subplan_idx);
        }
        if (cs->custom_plans)
        {
            ListCell *lc;
            foreach (lc, cs->custom_plans)
                cf_wrapper_audit_walk((Plan *) lfirst(lc), ctx, in_subplan, subplan_idx);
        }
    }

    if (plan->lefttree)
        cf_wrapper_audit_walk(plan->lefttree, ctx, in_subplan, subplan_idx);
    if (plan->righttree)
        cf_wrapper_audit_walk(plan->righttree, ctx, in_subplan, subplan_idx);

    switch (nodeTag(plan))
    {
        case T_Append:
            {
                Append *a = (Append *) plan;
                ListCell *lc;
                foreach (lc, a->appendplans)
                    cf_wrapper_audit_walk((Plan *) lfirst(lc), ctx, in_subplan, subplan_idx);
            }
            break;
        case T_MergeAppend:
            {
                MergeAppend *ma = (MergeAppend *) plan;
                ListCell *lc;
                foreach (lc, ma->mergeplans)
                    cf_wrapper_audit_walk((Plan *) lfirst(lc), ctx, in_subplan, subplan_idx);
            }
            break;
        case T_BitmapAnd:
            {
                BitmapAnd *ba = (BitmapAnd *) plan;
                ListCell *lc;
                foreach (lc, ba->bitmapplans)
                    cf_wrapper_audit_walk((Plan *) lfirst(lc), ctx, in_subplan, subplan_idx);
            }
            break;
        case T_BitmapOr:
            {
                BitmapOr *bo = (BitmapOr *) plan;
                ListCell *lc;
                foreach (lc, bo->bitmapplans)
                    cf_wrapper_audit_walk((Plan *) lfirst(lc), ctx, in_subplan, subplan_idx);
            }
            break;
        case T_SubqueryScan:
            {
                SubqueryScan *sq = (SubqueryScan *) plan;
                cf_wrapper_audit_walk(sq->subplan, ctx, in_subplan, subplan_idx);
            }
            break;
        case T_ModifyTable:
            break;
        default:
            break;
    }
}

static void
cf_log_wrapper_audit(PlannedStmt *pstmt)
{
    if (!cf_debug_ids || !pstmt || !pstmt->planTree)
        return;

    StringInfoData details;
    initStringInfo(&details);
    WrapperAuditCtx ctx;
    ctx.pstmt = pstmt;
    ctx.total_wrappers = 0;
    ctx.main_wrappers = 0;
    ctx.subplan_wrappers = 0;
    ctx.detail_count = 0;
    ctx.details = &details;

    cf_wrapper_audit_walk(pstmt->planTree, &ctx, false, -1);
    if (pstmt->subplans)
    {
        int spidx = 0;
        ListCell *lc;
        foreach (lc, pstmt->subplans)
        {
            cf_wrapper_audit_walk((Plan *) lfirst(lc), &ctx, true, spidx);
            spidx++;
        }
    }

    CF_DEBUG_SUBPLAN_LOG("wrapper_audit custom_scans=%d main=%d subplan=%d details=%s",
                         ctx.total_wrappers,
                         ctx.main_wrappers,
                         ctx.subplan_wrappers,
                         details.len > 0 ? details.data : "<none>");
    pfree(details.data);
}

static bool
cf_plan_scan_relid(Plan *plan, Index *out_relid)
{
    if (!plan || !out_relid)
        return false;
    switch (nodeTag(plan))
    {
        case T_SeqScan:
        case T_SampleScan:
        case T_IndexScan:
        case T_IndexOnlyScan:
        case T_BitmapHeapScan:
        case T_TidScan:
        case T_TidRangeScan:
        case T_ForeignScan:
        case T_FunctionScan:
        case T_TableFuncScan:
        case T_ValuesScan:
        case T_CteScan:
        case T_WorkTableScan:
            *out_relid = ((Scan *) plan)->scanrelid;
            return true;
        default:
            break;
    }
    return false;
}

static bool
cf_relid_is_relation(PlannedStmt *pstmt, Index scanrelid, Oid *out_relid)
{
    if (!pstmt || scanrelid <= 0)
        return false;
    RangeTblEntry *rte = rt_fetch(scanrelid, pstmt->rtable);
    if (!rte || rte->rtekind != RTE_RELATION)
        return false;
    if (out_relid)
        *out_relid = rte->relid;
    return true;
}

static void
cf_plan_walk(Plan *plan, ScannedCtx *ctx)
{
    if (!plan)
        return;

    if (IsA(plan, CustomScan))
    {
        CustomScan *cs = (CustomScan *) plan;
        if (cs->scan.scanrelid > 0 && ctx->pstmt)
        {
            Oid relid = InvalidOid;
            if (cf_relid_is_relation(ctx->pstmt, cs->scan.scanrelid, &relid))
            {
                if (!list_member_oid(ctx->relids, relid))
                    ctx->relids = lappend_oid(ctx->relids, relid);
                if (!list_member_oid(ctx->wrapped_relids, relid))
                    ctx->wrapped_relids = lappend_oid(ctx->wrapped_relids, relid);
            }
        }
        if (cs->custom_plans)
        {
            ListCell *lc;
            foreach (lc, cs->custom_plans)
                cf_plan_walk((Plan *) lfirst(lc), ctx);
        }
    }

    {
        Index scanrelid = 0;
        if (cf_plan_scan_relid(plan, &scanrelid) && ctx->pstmt)
        {
            Oid relid = InvalidOid;
            if (cf_relid_is_relation(ctx->pstmt, scanrelid, &relid))
            {
                if (!list_member_oid(ctx->relids, relid))
                    ctx->relids = lappend_oid(ctx->relids, relid);
            }
        }
    }

    if (plan->lefttree)
        cf_plan_walk(plan->lefttree, ctx);
    if (plan->righttree)
        cf_plan_walk(plan->righttree, ctx);

    switch (nodeTag(plan))
    {
        case T_Append:
            {
                Append *a = (Append *) plan;
                ListCell *lc;
                foreach (lc, a->appendplans)
                    cf_plan_walk((Plan *) lfirst(lc), ctx);
            }
            break;
        case T_MergeAppend:
            {
                MergeAppend *ma = (MergeAppend *) plan;
                ListCell *lc;
                foreach (lc, ma->mergeplans)
                    cf_plan_walk((Plan *) lfirst(lc), ctx);
            }
            break;
        case T_BitmapAnd:
            {
                BitmapAnd *ba = (BitmapAnd *) plan;
                ListCell *lc;
                foreach (lc, ba->bitmapplans)
                    cf_plan_walk((Plan *) lfirst(lc), ctx);
            }
            break;
        case T_BitmapOr:
            {
                BitmapOr *bo = (BitmapOr *) plan;
                ListCell *lc;
                foreach (lc, bo->bitmapplans)
                    cf_plan_walk((Plan *) lfirst(lc), ctx);
            }
            break;
        case T_SubqueryScan:
            {
                SubqueryScan *sq = (SubqueryScan *) plan;
                cf_plan_walk(sq->subplan, ctx);
            }
            break;
        case T_ModifyTable:
            break;
        default:
            break;
    }
}

static void
cf_collect_scanned_tables(EState *estate, MemoryContext mcxt,
                          char ***out_names, int *out_count,
                          char ***out_wrapped, int *out_wrapped_count,
                          int *out_main_rel_count, int *out_total_rel_count)
{
    if (!estate || !estate->es_plannedstmt)
    {
        *out_names = NULL;
        *out_count = 0;
        if (out_wrapped)
            *out_wrapped = NULL;
        if (out_wrapped_count)
            *out_wrapped_count = 0;
        if (out_main_rel_count)
            *out_main_rel_count = 0;
        if (out_total_rel_count)
            *out_total_rel_count = 0;
        return;
    }
    ScannedCtx ctx;
    ctx.pstmt = estate->es_plannedstmt;
    ctx.relids = NIL;
    ctx.wrapped_relids = NIL;
    cf_plan_walk(estate->es_plannedstmt->planTree, &ctx);
    int main_rel_count = list_length(ctx.relids);
    







    if (estate->es_plannedstmt->subplans)
    {
        ListCell *lc;
        foreach (lc, estate->es_plannedstmt->subplans)
            cf_plan_walk((Plan *) lfirst(lc), &ctx);
    }

    int count = list_length(ctx.relids);
    if (out_main_rel_count)
        *out_main_rel_count = main_rel_count;
    if (out_total_rel_count)
        *out_total_rel_count = count;
    if (count == 0)
    {
        *out_names = NULL;
        *out_count = 0;
        if (out_wrapped)
            *out_wrapped = NULL;
        if (out_wrapped_count)
            *out_wrapped_count = 0;
        if (out_main_rel_count)
            *out_main_rel_count = main_rel_count;
        if (out_total_rel_count)
            *out_total_rel_count = 0;
        return;
    }

    MemoryContext oldctx = MemoryContextSwitchTo(mcxt);
    char **names = (char **) palloc0(sizeof(char *) * count);
    int idx = 0;
    ListCell *lc;
    foreach (lc, ctx.relids)
    {
        Oid relid = lfirst_oid(lc);
        const char *rn = get_rel_name(relid);
        if (rn)
            names[idx++] = pstrdup(rn);
    }
    MemoryContextSwitchTo(oldctx);

    *out_names = names;
    *out_count = idx;

    if (out_wrapped && out_wrapped_count)
    {
        int wcount = list_length(ctx.wrapped_relids);
        if (wcount > 0)
        {
            MemoryContext oldctx2 = MemoryContextSwitchTo(mcxt);
            char **wnames = (char **) palloc0(sizeof(char *) * wcount);
            int widx = 0;
            ListCell *wc;
            foreach (wc, ctx.wrapped_relids)
            {
                Oid relid = lfirst_oid(wc);
                const char *rn = get_rel_name(relid);
                if (rn)
                    wnames[widx++] = pstrdup(rn);
            }
            MemoryContextSwitchTo(oldctx2);
            *out_wrapped = wnames;
            *out_wrapped_count = widx;
        }
        else
        {
            *out_wrapped = NULL;
            *out_wrapped_count = 0;
        }
    }
}

typedef struct CfScanQualTmpAtom
{
    Oid relid;
    char *target_table;
    int kind;                
    char *lhs_schema_key;
    int op;                  
    char *rhs_schema_key;    
    char *const_value;       
} CfScanQualTmpAtom;

typedef struct CfSeqQualEntry
{
    Oid relid;
    char *relname;
    int seqscan_count;
    List *atoms; 
} CfSeqQualEntry;

typedef struct CfSeqQualCtx
{
    PlannedStmt *pstmt;
    MemoryContext mcxt;
    List *entries; 
} CfSeqQualCtx;

static Node *
cf_strip_relabel_node(Node *n)
{
    for (;;)
    {
        if (n == NULL)
            return NULL;
        if (IsA(n, RelabelType))
        {
            n = (Node *) ((RelabelType *) n)->arg;
            continue;
        }
        return n;
    }
}

static int
cf_map_policy_op_from_name(const char *opname)
{
    if (!opname)
        return 0;
    if (strcmp(opname, "=") == 0)
        return POLICY_OP_EQ;
    if (strcmp(opname, "<>") == 0 || strcmp(opname, "!=") == 0)
        return POLICY_OP_NE;
    if (strcmp(opname, "<") == 0)
        return POLICY_OP_LT;
    if (strcmp(opname, "<=") == 0)
        return POLICY_OP_LE;
    if (strcmp(opname, ">") == 0)
        return POLICY_OP_GT;
    if (strcmp(opname, ">=") == 0)
        return POLICY_OP_GE;
    return 0;
}

static int
cf_flip_policy_op(int op)
{
    switch (op)
    {
        case POLICY_OP_LT: return POLICY_OP_GT;
        case POLICY_OP_LE: return POLICY_OP_GE;
        case POLICY_OP_GT: return POLICY_OP_LT;
        case POLICY_OP_GE: return POLICY_OP_LE;
        default: return op;
    }
}

static char *
cf_const_text_value(Const *c, MemoryContext mcxt)
{
    if (!c || c->constisnull)
        return NULL;
    Oid typoutput = InvalidOid;
    bool typisvarlena = false;
    getTypeOutputInfo(c->consttype, &typoutput, &typisvarlena);
    char *out = OidOutputFunctionCall(typoutput, c->constvalue);
    if (!out)
        return NULL;
    MemoryContext oldctx = MemoryContextSwitchTo(mcxt);
    char *copy = pstrdup(out);
    MemoryContextSwitchTo(oldctx);
    return copy;
}

static bool
cf_var_schema_key(Var *v,
                  Index expected_scanrelid,
                  Oid expected_relid,
                  PlannedStmt *pstmt,
                  MemoryContext mcxt,
                  char **out_schema_key,
                  char **out_relname)
{
    Index vscan = 0;
    AttrNumber vatt = InvalidAttrNumber;
    if (!v || !pstmt || !out_schema_key)
        return false;
    if (v->varlevelsup != 0)
        return false;
    vscan = (Index) v->varno;
    if (vscan != expected_scanrelid)
    {
        if (v->varnosyn > 0 && (Index) v->varnosyn == expected_scanrelid)
            vscan = (Index) v->varnosyn;
        else
            return false;
    }
    vatt = v->varattno;
    if (vatt <= 0 && v->varattnosyn > 0)
        vatt = v->varattnosyn;
    if (vatt <= 0)
        return false;
    Oid relid = InvalidOid;
    if (!cf_relid_is_relation(pstmt, vscan, &relid))
        return false;
    if (expected_relid != InvalidOid && relid != expected_relid)
        return false;
    const char *rn = get_rel_name(relid);
    const char *att = get_attname(relid, vatt, false);
    if (!rn || !att)
        return false;
    MemoryContext oldctx = MemoryContextSwitchTo(mcxt);
    *out_schema_key = psprintf("%s.%s", rn, att);
    if (out_relname)
        *out_relname = pstrdup(rn);
    MemoryContextSwitchTo(oldctx);
    return true;
}

static CfSeqQualEntry *
cf_seqqual_entry_get(CfSeqQualCtx *ctx, Oid relid, const char *relname)
{
    ListCell *lc;
    foreach (lc, ctx->entries)
    {
        CfSeqQualEntry *e = (CfSeqQualEntry *) lfirst(lc);
        if (e && e->relid == relid)
            return e;
    }
    MemoryContext oldctx = MemoryContextSwitchTo(ctx->mcxt);
    CfSeqQualEntry *e = (CfSeqQualEntry *) palloc0(sizeof(CfSeqQualEntry));
    e->relid = relid;
    e->relname = relname ? pstrdup(relname) : NULL;
    e->seqscan_count = 0;
    e->atoms = NIL;
    ctx->entries = lappend(ctx->entries, e);
    MemoryContextSwitchTo(oldctx);
    return e;
}

static void
cf_seqqual_append_atom(CfSeqQualEntry *entry, CfScanQualTmpAtom *atom)
{
    if (!entry || !atom)
        return;
    entry->atoms = lappend(entry->atoms, atom);
}

static void
cf_collect_seqscan_qual_expr(Node *expr,
                             CfSeqQualEntry *entry,
                             Index scanrelid,
                             Oid relid,
                             PlannedStmt *pstmt,
                             MemoryContext mcxt)
{
    if (!expr || !entry || !pstmt)
        return;

    expr = cf_strip_relabel_node(expr);
    if (!expr)
        return;

    if (IsA(expr, BoolExpr))
    {
        BoolExpr *b = (BoolExpr *) expr;
        if (b->boolop == AND_EXPR)
        {
            ListCell *lc;
            foreach (lc, b->args)
                cf_collect_seqscan_qual_expr((Node *) lfirst(lc), entry, scanrelid, relid, pstmt, mcxt);
        }
        return;
    }

    if (!IsA(expr, OpExpr))
        return;

    OpExpr *op = (OpExpr *) expr;
    if (list_length(op->args) != 2)
        return;
    const char *opname = get_opname(op->opno);
    int pop = cf_map_policy_op_from_name(opname);
    if (pop == 0)
        return;

    Node *a0 = cf_strip_relabel_node((Node *) linitial(op->args));
    Node *a1 = cf_strip_relabel_node((Node *) lsecond(op->args));
    if (!a0 || !a1)
        return;

    Var *v_lhs = NULL;
    Var *v_rhs = NULL;
    Const *c_lhs = NULL;
    Const *c_rhs = NULL;
    if (IsA(a0, Var)) v_lhs = (Var *) a0;
    if (IsA(a1, Var)) v_rhs = (Var *) a1;
    if (IsA(a0, Const)) c_lhs = (Const *) a0;
    if (IsA(a1, Const)) c_rhs = (Const *) a1;

    if (v_lhs && c_rhs)
    {
        char *lhs_key = NULL;
        if (!cf_var_schema_key(v_lhs, scanrelid, relid, pstmt, mcxt, &lhs_key, NULL))
            return;
        char *cval = cf_const_text_value(c_rhs, mcxt);
        if (!cval)
            return;
        MemoryContext oldctx = MemoryContextSwitchTo(mcxt);
        CfScanQualTmpAtom *a = (CfScanQualTmpAtom *) palloc0(sizeof(CfScanQualTmpAtom));
        a->relid = relid;
        a->target_table = pstrdup(entry->relname);
        a->kind = POLICY_SCAN_QUAL_COL_CONST;
        a->lhs_schema_key = lhs_key;
        a->op = pop;
        a->const_value = cval;
        MemoryContextSwitchTo(oldctx);
        cf_seqqual_append_atom(entry, a);
        return;
    }
    if (c_lhs && v_rhs)
    {
        char *lhs_key = NULL;
        if (!cf_var_schema_key(v_rhs, scanrelid, relid, pstmt, mcxt, &lhs_key, NULL))
            return;
        char *cval = cf_const_text_value(c_lhs, mcxt);
        if (!cval)
            return;
        MemoryContext oldctx = MemoryContextSwitchTo(mcxt);
        CfScanQualTmpAtom *a = (CfScanQualTmpAtom *) palloc0(sizeof(CfScanQualTmpAtom));
        a->relid = relid;
        a->target_table = pstrdup(entry->relname);
        a->kind = POLICY_SCAN_QUAL_COL_CONST;
        a->lhs_schema_key = lhs_key;
        a->op = cf_flip_policy_op(pop);
        a->const_value = cval;
        MemoryContextSwitchTo(oldctx);
        cf_seqqual_append_atom(entry, a);
        return;
    }
    if (v_lhs && v_rhs)
    {
        char *lhs_key = NULL;
        char *rhs_key = NULL;
        if (!cf_var_schema_key(v_lhs, scanrelid, relid, pstmt, mcxt, &lhs_key, NULL))
            return;
        if (!cf_var_schema_key(v_rhs, scanrelid, relid, pstmt, mcxt, &rhs_key, NULL))
            return;
        MemoryContext oldctx = MemoryContextSwitchTo(mcxt);
        CfScanQualTmpAtom *a = (CfScanQualTmpAtom *) palloc0(sizeof(CfScanQualTmpAtom));
        a->relid = relid;
        a->target_table = pstrdup(entry->relname);
        a->kind = POLICY_SCAN_QUAL_COL_COL;
        a->lhs_schema_key = lhs_key;
        a->op = pop;
        a->rhs_schema_key = rhs_key;
        MemoryContextSwitchTo(oldctx);
        cf_seqqual_append_atom(entry, a);
        return;
    }
}

static void
cf_plan_collect_seqscan_quals(Plan *plan, CfSeqQualCtx *ctx)
{
    if (!plan || !ctx)
        return;

    if (IsA(plan, CustomScan))
    {
        CustomScan *cs = (CustomScan *) plan;
        if (cs->custom_plans)
        {
            ListCell *lc;
            foreach (lc, cs->custom_plans)
                cf_plan_collect_seqscan_quals((Plan *) lfirst(lc), ctx);
        }
    }

    





    if (nodeTag(plan) == T_SeqScan ||
        nodeTag(plan) == T_IndexScan ||
        nodeTag(plan) == T_IndexOnlyScan ||
        nodeTag(plan) == T_BitmapHeapScan ||
        nodeTag(plan) == T_TidScan ||
        nodeTag(plan) == T_TidRangeScan)
    {
        Index scanrelid = ((Scan *) plan)->scanrelid;
        Oid relid = InvalidOid;
        if (cf_relid_is_relation(ctx->pstmt, scanrelid, &relid))
        {
            const char *rn = get_rel_name(relid);
            CfSeqQualEntry *entry = cf_seqqual_entry_get(ctx, relid, rn);
            entry->seqscan_count++;
            if (plan->qual)
            {
                ListCell *lc;
                foreach (lc, plan->qual)
                    cf_collect_seqscan_qual_expr((Node *) lfirst(lc),
                                                entry,
                                                scanrelid,
                                                relid,
                                                ctx->pstmt,
                                                ctx->mcxt);
            }

            
            List *index_quals = NIL;
            if (nodeTag(plan) == T_IndexScan)
                index_quals = ((IndexScan *) plan)->indexqualorig;
            else if (nodeTag(plan) == T_IndexOnlyScan)
                index_quals = ((IndexOnlyScan *) plan)->indexqual;
            else if (nodeTag(plan) == T_BitmapHeapScan)
                index_quals = ((BitmapHeapScan *) plan)->bitmapqualorig;
            else if (nodeTag(plan) == T_TidScan)
                index_quals = ((TidScan *) plan)->tidquals;
            else if (nodeTag(plan) == T_TidRangeScan)
                index_quals = ((TidRangeScan *) plan)->tidrangequals;
            if (index_quals)
            {
                ListCell *lc;
                foreach (lc, index_quals)
                    cf_collect_seqscan_qual_expr((Node *) lfirst(lc),
                                                entry,
                                                scanrelid,
                                                relid,
                                                ctx->pstmt,
                                                ctx->mcxt);
            }
        }
    }

    if (plan->lefttree)
        cf_plan_collect_seqscan_quals(plan->lefttree, ctx);
    if (plan->righttree)
        cf_plan_collect_seqscan_quals(plan->righttree, ctx);

    switch (nodeTag(plan))
    {
        case T_Append:
            {
                Append *a = (Append *) plan;
                ListCell *lc;
                foreach (lc, a->appendplans)
                    cf_plan_collect_seqscan_quals((Plan *) lfirst(lc), ctx);
            }
            break;
        case T_MergeAppend:
            {
                MergeAppend *ma = (MergeAppend *) plan;
                ListCell *lc;
                foreach (lc, ma->mergeplans)
                    cf_plan_collect_seqscan_quals((Plan *) lfirst(lc), ctx);
            }
            break;
        case T_BitmapAnd:
            {
                BitmapAnd *ba = (BitmapAnd *) plan;
                ListCell *lc;
                foreach (lc, ba->bitmapplans)
                    cf_plan_collect_seqscan_quals((Plan *) lfirst(lc), ctx);
            }
            break;
        case T_BitmapOr:
            {
                BitmapOr *bo = (BitmapOr *) plan;
                ListCell *lc;
                foreach (lc, bo->bitmapplans)
                    cf_plan_collect_seqscan_quals((Plan *) lfirst(lc), ctx);
            }
            break;
        case T_SubqueryScan:
            {
                SubqueryScan *sq = (SubqueryScan *) plan;
                cf_plan_collect_seqscan_quals(sq->subplan, ctx);
            }
            break;
        default:
            break;
    }
}

static void
cf_collect_seqscan_qual_atoms(EState *estate,
                              const PolicyEvalResultC *eval_res,
                              MemoryContext mcxt,
                              PolicyScanQualAtomC **out_atoms,
                              int *out_count)
{
    int effective_target_count = 0;
    char **effective_target_tables = NULL;

    if (out_atoms) *out_atoms = NULL;
    if (out_count) *out_count = 0;
    if (!estate || !estate->es_plannedstmt || !eval_res || !out_atoms || !out_count)
        return;

    effective_target_count = cf_eval_effective_target_count(eval_res);
    effective_target_tables = cf_eval_effective_target_tables(eval_res);
    if (effective_target_count <= 0 || !effective_target_tables)
        return;

    CfSeqQualCtx ctx;
    ctx.pstmt = estate->es_plannedstmt;
    ctx.mcxt = mcxt;
    ctx.entries = NIL;
    cf_plan_collect_seqscan_quals(estate->es_plannedstmt->planTree, &ctx);
    if (estate->es_plannedstmt->subplans)
    {
        ListCell *lc;
        foreach (lc, estate->es_plannedstmt->subplans)
            cf_plan_collect_seqscan_quals((Plan *) lfirst(lc), &ctx);
    }

    int total = 0;
    ListCell *lc;
    foreach (lc, ctx.entries)
    {
        CfSeqQualEntry *e = (CfSeqQualEntry *) lfirst(lc);
        if (!e || !e->relname || e->seqscan_count != 1)
            continue;
        if (!cf_table_in_list(e->relname, effective_target_tables, effective_target_count))
            continue;
        total += list_length(e->atoms);
    }
    if (total <= 0)
        return;

    MemoryContext oldctx = MemoryContextSwitchTo(mcxt);
    PolicyScanQualAtomC *atoms = (PolicyScanQualAtomC *) palloc0(sizeof(PolicyScanQualAtomC) * total);
    MemoryContextSwitchTo(oldctx);

    int idx = 0;
    foreach (lc, ctx.entries)
    {
        CfSeqQualEntry *e = (CfSeqQualEntry *) lfirst(lc);
        if (!e || !e->relname || e->seqscan_count != 1)
            continue;
        if (!cf_table_in_list(e->relname, effective_target_tables, effective_target_count))
            continue;
        ListCell *la;
        foreach (la, e->atoms)
        {
            CfScanQualTmpAtom *a = (CfScanQualTmpAtom *) lfirst(la);
            if (!a || !a->target_table || !a->lhs_schema_key || a->op == 0)
                continue;
            atoms[idx].target_table = a->target_table;
            atoms[idx].kind = a->kind;
            atoms[idx].lhs_schema_key = a->lhs_schema_key;
            atoms[idx].op = a->op;
            atoms[idx].rhs_schema_key = a->rhs_schema_key;
            atoms[idx].const_value = a->const_value;
            idx++;
        }
    }
    *out_atoms = atoms;
    *out_count = idx;
}

static bool
cf_table_in_list(const char *name, char **list, int count)
{
    if (!name || !list || count <= 0)
        return false;
    for (int i = 0; i < count; i++)
    {
        if (list[i] && strcmp(list[i], name) == 0)
            return true;
    }
    return false;
}

static int
cf_eval_target_index(const PolicyEvalResultC *res, const char *name)
{
    if (!res || !name || !res->target_tables || res->target_count <= 0)
        return -1;
    for (int i = 0; i < res->target_count; i++) {
        if (res->target_tables[i] && strcmp(res->target_tables[i], name) == 0)
            return i;
    }
    return -1;
}

static void
cf_parse_query_targets(const char *query_str, MemoryContext mcxt,
                       char ***out_tables, int *out_count)
{
    *out_tables = NULL;
    *out_count = 0;
    if (!query_str)
        return;

    const char *s = query_str;
    size_t len = strlen(s);
    size_t i = 0;
    while (i + 3 < len)
    {
        if ((i == 0 || !isalnum((unsigned char)s[i - 1])) &&
            tolower((unsigned char)s[i]) == 'f' &&
            tolower((unsigned char)s[i + 1]) == 'r' &&
            tolower((unsigned char)s[i + 2]) == 'o' &&
            tolower((unsigned char)s[i + 3]) == 'm' &&
            (i + 4 == len || !isalnum((unsigned char)s[i + 4])))
        {
            i += 4;
            break;
        }
        i++;
    }
    if (i >= len)
        return;

    while (i < len && isspace((unsigned char)s[i]))
        i++;
    if (i >= len)
        return;

    size_t start = i;
    while (i < len && (isalnum((unsigned char)s[i]) || s[i] == '_' || s[i] == '.'))
        i++;
    if (i <= start)
        return;

    size_t toklen = i - start;
    char *tok = (char *) palloc(toklen + 1);
    for (size_t j = 0; j < toklen; j++)
        tok[j] = (char) tolower((unsigned char) s[start + j]);
    tok[toklen] = '\0';
    char *dot = strrchr(tok, '.');
    const char *tbl = dot ? dot + 1 : tok;

    MemoryContext oldctx = MemoryContextSwitchTo(mcxt);
    char **tables = (char **) palloc0(sizeof(char *));
    tables[0] = pstrdup(tbl);
    MemoryContextSwitchTo(oldctx);

    *out_tables = tables;
    *out_count = 1;
}

static const char *
cf_plan_find_scan_type(Plan *plan, PlannedStmt *pstmt, Oid relid)
{
    if (!plan || !pstmt || relid == InvalidOid)
        return NULL;

    if (IsA(plan, CustomScan))
    {
        CustomScan *cs = (CustomScan *) plan;
        if (cs->custom_plans)
        {
            ListCell *lc;
            foreach (lc, cs->custom_plans)
            {
                const char *t = cf_plan_find_scan_type((Plan *) lfirst(lc), pstmt, relid);
                if (t)
                    return t;
            }
        }
    }

    {
        Index scanrelid = 0;
        if (cf_plan_scan_relid(plan, &scanrelid))
        {
            Oid plan_relid = InvalidOid;
            if (cf_relid_is_relation(pstmt, scanrelid, &plan_relid) && plan_relid == relid)
            {
                switch (nodeTag(plan))
                {
                    case T_SeqScan: return "SeqScan";
                    case T_SampleScan: return "SampleScan";
                    case T_IndexScan: return "IndexScan";
                    case T_IndexOnlyScan: return "IndexOnlyScan";
                    case T_BitmapHeapScan: return "BitmapHeapScan";
                    case T_TidScan: return "TidScan";
                    case T_TidRangeScan: return "TidRangeScan";
                    case T_ForeignScan: return "ForeignScan";
                    case T_FunctionScan: return "FunctionScan";
                    case T_TableFuncScan: return "TableFuncScan";
                    case T_ValuesScan: return "ValuesScan";
                    case T_CteScan: return "CteScan";
                    case T_WorkTableScan: return "WorkTableScan";
                    default: break;
                }
                return "OtherScan";
            }
        }
    }

    if (plan->lefttree)
    {
        const char *t = cf_plan_find_scan_type(plan->lefttree, pstmt, relid);
        if (t)
            return t;
    }
    if (plan->righttree)
    {
        const char *t = cf_plan_find_scan_type(plan->righttree, pstmt, relid);
        if (t)
            return t;
    }

    switch (nodeTag(plan))
    {
        case T_Append:
            {
                Append *a = (Append *) plan;
                ListCell *lc;
                foreach (lc, a->appendplans)
                {
                    const char *t = cf_plan_find_scan_type((Plan *) lfirst(lc), pstmt, relid);
                    if (t)
                        return t;
                }
            }
            break;
        case T_MergeAppend:
            {
                MergeAppend *ma = (MergeAppend *) plan;
                ListCell *lc;
                foreach (lc, ma->mergeplans)
                {
                    const char *t = cf_plan_find_scan_type((Plan *) lfirst(lc), pstmt, relid);
                    if (t)
                        return t;
                }
            }
            break;
        case T_BitmapAnd:
            {
                BitmapAnd *ba = (BitmapAnd *) plan;
                ListCell *lc;
                foreach (lc, ba->bitmapplans)
                {
                    const char *t = cf_plan_find_scan_type((Plan *) lfirst(lc), pstmt, relid);
                    if (t)
                        return t;
                }
            }
            break;
        case T_BitmapOr:
            {
                BitmapOr *bo = (BitmapOr *) plan;
                ListCell *lc;
                foreach (lc, bo->bitmapplans)
                {
                    const char *t = cf_plan_find_scan_type((Plan *) lfirst(lc), pstmt, relid);
                    if (t)
                        return t;
                }
            }
            break;
        case T_SubqueryScan:
            {
                SubqueryScan *sq = (SubqueryScan *) plan;
                const char *t = cf_plan_find_scan_type(sq->subplan, pstmt, relid);
                if (t)
                    return t;
            }
            break;
        default:
            break;
    }

    return NULL;
}

typedef struct CfRelOccCountCtx
{
    PlannedStmt *pstmt;
    Oid relid;
    int scanned;
    int wrapped;
} CfRelOccCountCtx;

static void
cf_count_rel_occurrences_walk(Plan *plan, CfRelOccCountCtx *ctx)
{
    if (!plan || !ctx || !ctx->pstmt || ctx->relid == InvalidOid)
        return;

    if (IsA(plan, CustomScan))
    {
        CustomScan *cs = (CustomScan *) plan;
        if (cs->scan.scanrelid > 0)
        {
            Oid wrapped_relid = InvalidOid;
            if (cf_relid_is_relation(ctx->pstmt, cs->scan.scanrelid, &wrapped_relid) &&
                wrapped_relid == ctx->relid)
                ctx->wrapped++;
        }
        if (cs->custom_plans)
        {
            ListCell *lc;
            foreach (lc, cs->custom_plans)
                cf_count_rel_occurrences_walk((Plan *) lfirst(lc), ctx);
        }
    }

    {
        Index scanrelid = 0;
        if (cf_plan_scan_relid(plan, &scanrelid))
        {
            Oid plan_relid = InvalidOid;
            if (cf_relid_is_relation(ctx->pstmt, scanrelid, &plan_relid) && plan_relid == ctx->relid)
                ctx->scanned++;
        }
    }

    if (plan->lefttree)
        cf_count_rel_occurrences_walk(plan->lefttree, ctx);
    if (plan->righttree)
        cf_count_rel_occurrences_walk(plan->righttree, ctx);

    switch (nodeTag(plan))
    {
        case T_Append:
            {
                Append *a = (Append *) plan;
                ListCell *lc;
                foreach (lc, a->appendplans)
                    cf_count_rel_occurrences_walk((Plan *) lfirst(lc), ctx);
            }
            break;
        case T_MergeAppend:
            {
                MergeAppend *ma = (MergeAppend *) plan;
                ListCell *lc;
                foreach (lc, ma->mergeplans)
                    cf_count_rel_occurrences_walk((Plan *) lfirst(lc), ctx);
            }
            break;
        case T_BitmapAnd:
            {
                BitmapAnd *ba = (BitmapAnd *) plan;
                ListCell *lc;
                foreach (lc, ba->bitmapplans)
                    cf_count_rel_occurrences_walk((Plan *) lfirst(lc), ctx);
            }
            break;
        case T_BitmapOr:
            {
                BitmapOr *bo = (BitmapOr *) plan;
                ListCell *lc;
                foreach (lc, bo->bitmapplans)
                    cf_count_rel_occurrences_walk((Plan *) lfirst(lc), ctx);
            }
            break;
        case T_SubqueryScan:
            {
                SubqueryScan *sq = (SubqueryScan *) plan;
                cf_count_rel_occurrences_walk(sq->subplan, ctx);
            }
            break;
        default:
            break;
    }
}

static void
cf_count_rel_occurrences(PlannedStmt *pstmt, Oid relid, int *out_scanned, int *out_wrapped)
{
    if (out_scanned)
        *out_scanned = 0;
    if (out_wrapped)
        *out_wrapped = 0;
    if (!pstmt || relid == InvalidOid)
        return;

    CfRelOccCountCtx ctx;
    memset(&ctx, 0, sizeof(ctx));
    ctx.pstmt = pstmt;
    ctx.relid = relid;

    cf_count_rel_occurrences_walk(pstmt->planTree, &ctx);
    if (pstmt->subplans)
    {
        ListCell *lc;
        foreach (lc, pstmt->subplans)
            cf_count_rel_occurrences_walk((Plan *) lfirst(lc), &ctx);
    }

    if (out_scanned)
        *out_scanned = ctx.scanned;
    if (out_wrapped)
        *out_wrapped = ctx.wrapped;
}

static bool
cf_table_should_filter(PolicyQueryState *qs, const char *name)
{
    if (!qs || !name)
        return false;
    if (!cf_table_in_list(name, qs->policy_targets, qs->n_policy_targets))
        return false;
    if (!cf_table_scanned(qs, name))
        return false;
    return true;
}

static bool
cf_table_scanned(PolicyQueryState *qs, const char *name)
{
    if (!qs || !name || qs->n_scanned_tables == 0 || !qs->scanned_tables)
        return true;
    for (int i = 0; i < qs->n_scanned_tables; i++)
    {
        if (qs->scanned_tables[i] && strcmp(qs->scanned_tables[i], name) == 0)
            return true;
    }
    return false;
}

static bool
cf_table_wrapped(PolicyQueryState *qs, const char *name)
{
    if (!qs || !name || qs->n_wrapped_tables == 0 || !qs->wrapped_tables)
        return false;
    for (int i = 0; i < qs->n_wrapped_tables; i++)
    {
        if (qs->wrapped_tables[i] && strcmp(qs->wrapped_tables[i], name) == 0)
            return true;
    }
    return false;
}

static bool
cf_needed_file_used_by_policy_new(const char *name)
{
    return pac_artifact_name_allowed(name);
}

static void
cf_prune_needed_files_for_policy_new(PolicyQueryState *qs)
{
    if (!qs || qs->n_needed_files <= 0 || !qs->needed_files)
        return;
    int out = 0;
    for (int i = 0; i < qs->n_needed_files; i++)
    {
        char *name = qs->needed_files[i];
        if (!cf_needed_file_used_by_policy_new(name))
        {
            if (name)
                pfree(name);
            continue;
        }
        qs->needed_files[out++] = name;
    }
    qs->n_needed_files = out;
}

static void
cf_walk_add_needed_file(PolicyQueryState *qs, const char *name)
{
    char **grown;

    if (!qs || !name || !name[0])
        return;
    for (int i = 0; i < qs->n_needed_files; i++)
    {
        if (qs->needed_files[i] && strcmp(qs->needed_files[i], name) == 0)
            return;
    }
    if (qs->needed_files)
        grown = (char **) repalloc(qs->needed_files,
                                  sizeof(char *) * (size_t) (qs->n_needed_files + 1));
    else
        grown = (char **) palloc(sizeof(char *));
    qs->needed_files = grown;
    qs->needed_files[qs->n_needed_files++] = pstrdup(name);
}

static void
cf_walk_add_table_files(PolicyQueryState *qs, const char *table)
{
    char *name;

    if (!table || !table[0])
        return;
    name = psprintf("meta/cols/%s", table);
    cf_walk_add_needed_file(qs, name);
    pfree(name);
    name = psprintf("%s_ctid", table);
    cf_walk_add_needed_file(qs, name);
    pfree(name);
}

static void
cf_walk_add_column_files(PolicyQueryState *qs, const char *schema_key)
{
    const char *body;
    const char *dot;
    const char *end;
    char *table;
    char *column;
    char *name;

    if (!schema_key || !schema_key[0])
        return;
    body = schema_key;
    if (strncmp(body, "const:", 6) == 0)
        body += 6;
    else if (strncmp(body, "join:", 5) == 0)
        body += 5;
    dot = strchr(body, '.');
    if (!dot || dot == body)
        ereport(ERROR,
                (errmsg("custom_filter_new: invalid walk schema key: %s", schema_key)));
    end = strchr(dot + 1, ' ');
    if (!end)
        end = body + strlen(body);
    if (end <= dot + 1)
        ereport(ERROR,
                (errmsg("custom_filter_new: invalid walk schema key: %s", schema_key)));
    table = pnstrdup(body, (int) (dot - body));
    column = pnstrdup(dot + 1, (int) (end - (dot + 1)));
    cf_walk_add_table_files(qs, table);
    name = psprintf("canon_invidx/%s/%s", table, column);
    cf_walk_add_needed_file(qs, name);
    pfree(name);
    name = psprintf("canon_fwdidx/%s/%s", table, column);
    cf_walk_add_needed_file(qs, name);
    pfree(name);
    pfree(column);
    pfree(table);
}


static void
// Adds every prebuilt artifact required by the PAC walk.
cf_augment_needed_files_for_walk(PolicyQueryState *qs,
                                 const PolicyEvalResultC *eval_res)
{
    if (!qs || !eval_res)
        return;
    cf_walk_add_needed_file(qs, "meta/col_domain");
    for (int i = 0; i < eval_res->target_count; i++)
    {
        if (eval_res->target_tables && eval_res->target_tables[i])
            cf_walk_add_table_files(qs, eval_res->target_tables[i]);
    }
    for (int i = 0; i < eval_res->atom_count; i++)
    {
        const PolicyAtomC *atom = &eval_res->atoms[i];
        cf_walk_add_column_files(qs, atom->lhs_schema_key);
        cf_walk_add_column_files(qs, atom->rhs_schema_key);
    }
}

Node *
cf_create_state(CustomScan *cscan)
{
    CfExec *st = (CfExec *) palloc0(sizeof(CfExec));

    NodeSetTag(&st->css, T_CustomScanState);
    st->css.methods = &CFExecMethods;
    st->css.slotOps = &TTSOpsBufferHeapTuple;

    st->child_plan    = NULL;
    st->data_transfer_ms = 0.0;
    st->policy_build_ms = 0.0;
    st->row_validation_ms = 0.0;
    st->child_exec_ms = 0.0;
    st->ctid_extract_ms = 0.0;
    st->ctid_to_rid_ms = 0.0;
    st->allow_check_ms = 0.0;
    st->projection_ms = 0.0;
    st->child_next_calls = 0;
    st->tid_heap_fetch_ms = 0.0;
    st->tid_slot_store_ms = 0.0;
    st->tid_visibility_ms = 0.0;
    st->tuples_seen = 0;
    st->tuples_passed = 0;
    st->misses = 0;
    st->relid = InvalidOid;
    st->relname[0] = '\0';
    st->seq_rid = 0;
    st->scan_type = NULL;
    st->tid_logged = false;
    st->filter = NULL;
    st->validated_filter = NULL;
    st->validated_build_seq = 0;
    st->need_filter_rebind = true;
    st->bound_build_seq = 0;
    st->attempted_filter_rebuild = false;
    st->rescan_calls = 0;
    st->exec_logged = false;
    st->debug_exec_logged = false;
    st->blk_cache_valid = false;
    st->blk_cache_blkno = InvalidBlockNumber;
    st->blk_cache_present = false;
    st->blk_cache_words = NULL;
    st->blocks_seen = 0;
    st->blocks_skipped = 0;
    st->scan_mode = CF_SCAN_MODE_FILTER;
    st->scan_mode_set = false;
    st->scan_mode_density = 1.0;
    st->scan_mode_logged = false;
    st->tid_iter_initialized = false;
    st->tid_iter_block_ord = 0;
    st->tid_iter_word_idx = 0;
    st->tid_iter_bit_min = 0;
    st->tidrange_scan = NULL;
    st->tidrange_active = false;
    st->tupleless_eligible = false;
    st->tupleless_fastpath = false;
    st->tupleless_range_active = false;
    st->tupleless_slot_ready = false;
    st->tupleless_blk = InvalidBlockNumber;
    st->tupleless_next_off = InvalidOffsetNumber;
    st->tupleless_end_off = InvalidOffsetNumber;
    st->tid_blocks_visited = 0;
    st->tid_tuples_fetched = 0;
    st->tid_offsets_checked = 0;
    st->tid_offsets_passed = 0;
    st->tid_fetch_ms = 0.0;
    st->tid_qual_ms = 0.0;
    st->empty_short_circuit_recorded = false;
    st->empty_short_circuit_calls = 0;
    st->empty_short_circuit_ms = 0.0;

    return (Node *) st;
}


void
cf_begin(CustomScanState *node, EState *estate, int eflags)
{
    CfExec *st = (CfExec *) node;
    CustomScan *cscan = (CustomScan *) node->ss.ps.plan;
    if (estate && cscan->scan.scanrelid > 0)
    {
        RangeTblEntry *rte = rt_fetch(cscan->scan.scanrelid, estate->es_range_table);
        st->relid = rte ? rte->relid : InvalidOid;
        if (st->relid != InvalidOid)
        {
            const char *rn = get_rel_name(st->relid);
            if (rn)
                strlcpy(st->relname, rn, sizeof(st->relname));
        }
    }
    




    



    st->filter = cf_in_executor_start_init ? NULL : cf_find_filter(cf_query_state, st->relid, false);
    st->need_filter_rebind = true;
    st->validated_filter = NULL;
    st->validated_build_seq = 0;
    st->bound_build_seq = cf_query_state ? cf_query_state->build_seq : 0;
    st->attempted_filter_rebuild = false;

    st->child_plan = ExecInitNode((Plan *) linitial(cscan->custom_plans),
                                  estate,
                                  eflags);
    st->scan_type = cf_scan_state_name(st->child_plan);
    {
        int custom_tlist_len = (node->ss.ps.plan && ((Plan *) node->ss.ps.plan)->targetlist)
                                   ? list_length(((Plan *) node->ss.ps.plan)->targetlist)
                                   : 0;
        int child_tlist_len = (st->child_plan && st->child_plan->plan && st->child_plan->plan->targetlist)
                                  ? list_length(st->child_plan->plan->targetlist)
                                  : 0;
        int result_natts = (node->ss.ps.ps_ResultTupleDesc != NULL)
                               ? node->ss.ps.ps_ResultTupleDesc->natts
                               : -1;
        st->tupleless_eligible = (custom_tlist_len == 0 &&
                                  child_tlist_len == 0 &&
                                  result_natts == 0);
        if (cf_trace_enabled())
        {
        CF_METRICS_LOG(NOTICE,
             "custom_filter_new: begin_shape rel=%s custom_tlist=%d child_tlist=%d result_natts=%d",
             st->relname[0] ? st->relname : "<unknown>",
             custom_tlist_len,
             child_tlist_len,
             result_natts);
        }
    }
    cf_debug_log_scan_ids("BeginCustomScan", st, node);
    if (cf_profile_rescan && st->relid != InvalidOid)
    {
        CF_RESCAN_LOG("event=BeginCustomScan pid=%d build_seq=%llu node=%p plan=%p rel=%s relid=%u scan=%s filter=%s",
                      (int) getpid(),
                      (unsigned long long) (cf_query_state ? cf_query_state->build_seq : 0),
                      (void *) st,
                      (void *) node->ss.ps.plan,
                      st->relname[0] ? st->relname : "<unknown>",
                      st->relid,
                      st->scan_type ? st->scan_type : "<unknown>",
                      st->filter ? "on" : "off");
    }
    if (!cf_child_is_scan(st->child_plan))
    {
        if (st->filter)
            ereport(ERROR,
                    (errmsg("custom_filter_new: unsupported scan node for policy-required table (rel=%s node=%s)",
                            st->relname[0] ? st->relname : "<unknown>",
                            st->scan_type ? st->scan_type : "<unknown>")));
        else
            elog(WARNING, "custom_filter_new: child plan is not a scan node");
    }
    if (cf_contract_enabled())
    {
        CF_TRACE_LOG( "custom_filter_new: scan rel=%s type=%s filter=%s",
             st->relname[0] ? st->relname : "<unknown>",
             st->scan_type ? st->scan_type : "<unknown>",
             st->filter ? "on" : "off");
    }
    node->custom_ps = list_make1(st->child_plan);
}

TupleTableSlot *
// Returns only tuples whose CTIDs are present in the PAC allow set.
cf_exec(CustomScanState *node)
{
    CfExec    *st    = (CfExec *) node;
    PlanState *child = st->child_plan;
    instr_time validation_start;

    INSTR_TIME_SET_CURRENT(validation_start);

    if (cf_query_state && st->bound_build_seq != cf_query_state->build_seq)
    {
        st->need_filter_rebind = true;
        st->validated_filter = NULL;
        st->validated_build_seq = 0;
    }

    if (st->need_filter_rebind)
    {
        if (cf_query_state)
        {
            bool should_filter = false;
            bool in_policy_targets = false;
            if (st->relname[0])
            {
                should_filter = cf_table_should_filter(cf_query_state, st->relname);
                in_policy_targets = cf_table_in_list(st->relname,
                                                     cf_query_state->policy_targets,
                                                     cf_query_state->n_policy_targets);
            }
            bool expect_filter = should_filter || in_policy_targets;
            cf_filters_guard_check(cf_query_state, "BindFilter");
            





            st->filter = cf_find_filter(cf_query_state, st->relid, expect_filter);
            if (expect_filter && st->filter && st->rescan_calls == 0)
                cf_record_scan_reuse(cf_query_state, st->relid);
            if (cf_debug_ids && cf_query_state && !st->filter)
            {
                if (expect_filter)
                {
                    CustomScan *cscan = (CustomScan *) node->ss.ps.plan;
                    EState *estate = node->ss.ps.state;
                    Index scanrelid = cscan ? cscan->scan.scanrelid : 0;
                    Oid rte_oid = InvalidOid;
                    if (estate && scanrelid > 0)
                    {
                        RangeTblEntry *rte = rt_fetch(scanrelid, estate->es_range_table);
                        if (rte)
                            rte_oid = rte->relid;
                    }
                    CF_METRICS_LOG(NOTICE,
                         "CF_BIND_NULL pid=%d scanrelid=%d st_relid=%u st_relname=%s rte_oid=%u should_filter=%d in_policy_targets=%d qs_ptr=%p build_seq=%llu",
                         (int) getpid(),
                         (int) scanrelid,
                         (unsigned int) st->relid,
                         st->relname[0] ? st->relname : "<unknown>",
                         (unsigned int) rte_oid,
                         should_filter ? 1 : 0,
                         in_policy_targets ? 1 : 0,
                         (void *) cf_query_state,
                         (unsigned long long) cf_query_state->build_seq);
                }
            }

            st->bound_build_seq = cf_query_state ? cf_query_state->build_seq : 0;
            st->need_filter_rebind = false;
            st->blk_cache_valid = false;
            st->blk_cache_blkno = InvalidBlockNumber;
            st->blk_cache_present = false;
            st->blk_cache_words = NULL;
            st->scan_mode_set = false;
            st->scan_mode_density = 1.0;
            st->scan_mode_logged = false;
            st->interrupt_counter = 0;
            st->tid_iter_initialized = false;
            st->tid_iter_block_ord = 0;
            st->tid_iter_word_idx = 0;
            st->tid_iter_bit_min = 0;
            st->tupleless_fastpath = false;
            st->tupleless_range_active = false;
            st->tupleless_slot_ready = false;
            st->tupleless_blk = InvalidBlockNumber;
            st->tupleless_next_off = InvalidOffsetNumber;
            st->tupleless_end_off = InvalidOffsetNumber;

            cf_debug_log_scan_ids("BindFilter", st, node);
            if (!st->debug_exec_logged)
            {
                cf_debug_log_scan_ids("ExecCustomScan(first)", st, node);
                if (cf_query_state)
                    cf_filters_guard_check(cf_query_state, "ExecCustomScan(first)");
                st->debug_exec_logged = true;
            }

            if (cf_profile_rescan && !st->exec_logged && st->relid != InvalidOid)
            {
                CF_RESCAN_LOG("event=ExecCustomScan(first) pid=%d build_seq=%llu node=%p rel=%s relid=%u scan=%s filter=%s",
                              (int) getpid(),
                              (unsigned long long) cf_query_state->build_seq,
                              (void *) st,
                              st->relname[0] ? st->relname : "<unknown>",
                              st->relid,
                              st->scan_type ? st->scan_type : "<unknown>",
                              st->filter ? "on" : "off");
                st->exec_logged = true;
            }
        }
    }

    TableFilterState *tf = st->filter;
    if (tf)
        cf_update_scan_mode(st, node, tf);
    if (tf && st->scan_mode == CF_SCAN_MODE_EMPTY)
    {
        



        instr_time e0, e1;
        INSTR_TIME_SET_CURRENT(e0);
        st->empty_short_circuit_recorded = true;
        st->empty_short_circuit_calls++;
        INSTR_TIME_SET_CURRENT(e1);
        st->empty_short_circuit_ms += INSTR_TIME_GET_MILLISEC(e1) - INSTR_TIME_GET_MILLISEC(e0);
        cf_accum_validation_time(st, &validation_start);
        return ExecClearTuple(node->ss.ss_ScanTupleSlot);
    }

    if (tf && st->scan_mode == CF_SCAN_MODE_TID)
    {
        for (;;)
        {
            cf_periodic_interrupt_check(&st->interrupt_counter);
            TupleTableSlot *slot = cf_exec_seqscan_tid_mode(node, st, tf);
            if (TupIsNull(slot))
            {
                cf_accum_validation_time(st, &validation_start);
                return ExecClearTuple(node->ss.ss_ScanTupleSlot);
            }
            slot = cf_store_slot(node, slot);
            cf_accum_validation_time(st, &validation_start);
            return slot;
        }
    }

    if (tf && st->scan_mode == CF_SCAN_MODE_ALL)
    {
        for (;;)
        {
            cf_periodic_interrupt_check(&st->interrupt_counter);
            instr_time child_start, child_end;
            INSTR_TIME_SET_CURRENT(child_start);
            st->child_next_calls++;
            TupleTableSlot *slot = ExecProcNode(child);
            INSTR_TIME_SET_CURRENT(child_end);
            st->child_exec_ms += INSTR_TIME_GET_MILLISEC(child_end) - INSTR_TIME_GET_MILLISEC(child_start);

            if (TupIsNull(slot))
            {
                cf_accum_validation_time(st, &validation_start);
                return ExecClearTuple(node->ss.ss_ScanTupleSlot);
            }

            st->tuples_seen++;
            if (tf)
                tf->seen++;
            st->tuples_passed++;
            if (tf)
                tf->passed++;
            slot = cf_store_slot(node, slot);
            cf_accum_validation_time(st, &validation_start);
            return slot;
        }
    }

    for (;;)
    {
        cf_periodic_interrupt_check(&st->interrupt_counter);
        instr_time child_start, child_end;
        INSTR_TIME_SET_CURRENT(child_start);
        st->child_next_calls++;
        TupleTableSlot *slot = ExecProcNode(child);
        INSTR_TIME_SET_CURRENT(child_end);
        st->child_exec_ms += INSTR_TIME_GET_MILLISEC(child_end) - INSTR_TIME_GET_MILLISEC(child_start);

        if (TupIsNull(slot))
        {
            cf_accum_validation_time(st, &validation_start);
            return ExecClearTuple(node->ss.ss_ScanTupleSlot);
        }
        st->tuples_seen++;

        bool allow = true;
        if (tf)
            tf->seen++;
	allow_check:
        if (tf && tf->block_words)
        {
            TupleTableSlot *ctid_slot = slot;
            ItemPointerData tid_buf;
            CfTidSource tid_src = CF_TID_NONE;
            bool has_tid = false;
            instr_time ctid_extract_start, ctid_extract_end;
            INSTR_TIME_SET_CURRENT(ctid_extract_start);
            if (ItemPointerIsValid(&slot->tts_tid))
            {
                tid_buf = slot->tts_tid;
                tid_src = CF_TID_TTS;
                has_tid = true;
            }
            else if (nodeTag(child) == T_BitmapHeapScanState)
            {
                if (ItemPointerIsValid(&ctid_slot->tts_tid))
                {
                    tid_buf = ctid_slot->tts_tid;
                    tid_src = CF_TID_TTS;
                    has_tid = true;
                }
            }
            else
            {
                has_tid = cf_slot_get_ctid(ctid_slot, &tid_buf, &tid_src);
            }
            if (!has_tid)
            {
                ctid_slot = cf_scan_slot(child, slot);
                if (ctid_slot && ItemPointerIsValid(&ctid_slot->tts_tid))
                {
                    tid_buf = ctid_slot->tts_tid;
                    tid_src = CF_TID_TTS;
                    has_tid = true;
                }
                else
                {
                    has_tid = cf_slot_get_ctid(ctid_slot, &tid_buf, &tid_src);
                }
            }
            INSTR_TIME_SET_CURRENT(ctid_extract_end);
            st->ctid_extract_ms += INSTR_TIME_GET_MILLISEC(ctid_extract_end) -
                                   INSTR_TIME_GET_MILLISEC(ctid_extract_start);
            if (!has_tid)
            {
                ereport(ERROR,
                        (errmsg("custom_filter_new: missing CTID/TID for policy-required table (rel=%s scan=%s)",
                                st->relname[0] ? st->relname : "<unknown>",
                                st->scan_type ? st->scan_type : "<unknown>")));
            }
            if (cf_contract_enabled() && !st->tid_logged)
            {
                CF_TRACE_LOG( "custom_filter_new: tid_source rel=%s scan=%s source=%s",
                     st->relname[0] ? st->relname : "<unknown>",
                     st->scan_type ? st->scan_type : "<unknown>",
                     cf_tid_source_name(tid_src));
                st->tid_logged = true;
            }
            BlockNumber blk = 0;
            OffsetNumber off = 0;
            blk  = ItemPointerGetBlockNumber(&tid_buf);
            off = ItemPointerGetOffsetNumber(&tid_buf);
            instr_time allow_start, allow_end;
            INSTR_TIME_SET_CURRENT(allow_start);
            if (!st->blk_cache_valid || st->blk_cache_blkno != blk)
            {
                st->blk_cache_valid = true;
                st->blk_cache_blkno = blk;
                st->blk_cache_words = cf_lookup_block_words(tf->block_words,
                                                            tf->block_ids,
                                                            tf->blocks,
                                                            tf->total_blocks,
                                                            blk);
                st->blk_cache_present = (st->blk_cache_words != NULL);
                st->blocks_seen++;
                if (!st->blk_cache_present)
                    st->blocks_skipped++;
            }
            if (!st->blk_cache_present)
            {
                allow = false;
            }
            else if (off < 1 || off > CF_MAX_OFF)
            {
                allow = false;
            }
            else
            {
                uint32 off0 = (uint32) off - 1u;
                size_t word_idx = (size_t) (off0 >> 6);
                uint64 mask = 1ULL << (off0 & 63u);
                allow = (st->blk_cache_words[word_idx] & mask) != 0;
            }
            INSTR_TIME_SET_CURRENT(allow_end);
            st->allow_check_ms += INSTR_TIME_GET_MILLISEC(allow_end) -
                                  INSTR_TIME_GET_MILLISEC(allow_start);
        }
        else if (tf && !tf->block_words && tf->blocks > 0)
        {
            




            TableFilterState *reb = cf_query_state ? cf_find_filter(cf_query_state, st->relid, true) : NULL;
            if (reb && reb->block_words)
            {
                st->filter = reb;
                st->bound_build_seq = cf_query_state ? cf_query_state->build_seq : 0;
                tf = reb;
                st->blk_cache_valid = false;
                goto allow_check;
            }

            EState *estate = node->ss.ps.state;
            if (!st->attempted_filter_rebuild && estate)
            {
                st->attempted_filter_rebuild = true;
                (void) cf_force_rebuild_query_state(estate,
                                                    cf_current_policy_query_sql(),
                                                    estate->es_plannedstmt);
                reb = cf_query_state ? cf_find_filter(cf_query_state, st->relid, true) : NULL;
                if (reb && reb->block_words)
                {
                    st->filter = reb;
                    st->bound_build_seq = cf_query_state ? cf_query_state->build_seq : 0;
                    tf = reb;
                    st->blk_cache_valid = false;
                    goto allow_check;
                }
            }

            if (cf_trace_enabled())
            {
                PolicyQueryState *qs = cf_query_state;
                const char *rn = st->relname[0] ? st->relname : "<unknown>";
                bool in_targets = false;
                bool scanned = false;
                bool should_filter = false;
                bool wrapped = false;
                if (qs && st->relname[0])
                {
                    in_targets = cf_table_in_list(st->relname, qs->policy_targets, qs->n_policy_targets);
                    scanned = cf_table_scanned(qs, st->relname);
                    should_filter = cf_table_should_filter(qs, st->relname);
                    wrapped = cf_table_wrapped(qs, st->relname);
                }
                CF_METRICS_LOG(NOTICE,
                     "custom_filter_new: missing_block_words_debug qs=%p build_seq=%llu st=%p rel=%s relid=%u tf=%p "
                     "in_policy_targets=%d scanned=%d should_filter=%d wrapped=%d n_filters=%d n_policy_targets=%d n_scanned_tables=%d",
                     (void *) qs,
                     (unsigned long long) (qs ? qs->build_seq : 0),
                     (void *) st,
                     rn,
                     st->relid,
                     (void *) tf,
                     in_targets ? 1 : 0,
                     scanned ? 1 : 0,
                     should_filter ? 1 : 0,
                     wrapped ? 1 : 0,
                     qs ? qs->n_filters : 0,
                     qs ? qs->n_policy_targets : 0,
                     qs ? qs->n_scanned_tables : 0);
                if (qs && qs->filters)
                {
                    for (int i = 0; i < qs->n_filters; i++)
                    {
                        TableFilterState *k = &qs->filters[i];
                        CF_METRICS_LOG(NOTICE,
                             "custom_filter_new: missing_block_words_debug key[%d] rel=%s relid=%u block_words=%p blocks=%u bytes=%zu rows=%u",
                             i,
                             k->relname[0] ? k->relname : "<unknown>",
                             k->relid,
                             (void *) k->block_words,
                             (unsigned int) k->blocks,
                             k->block_words_nbytes,
                             k->n_rows);
                    }
                }
            }

            if (cf_debug_ids)
            {
                cf_debug_log_scan_ids("MissingBlockWords", st, node);
                PolicyQueryState *qs = cf_query_state;
                if (qs)
                {
                    CF_DEBUG_IDS_LOG("pid=%d build_seq=%llu missing_block_words_state qs=%p n_filters=%d n_policy_targets=%d",
                                     (int) getpid(),
                                     (unsigned long long) qs->build_seq,
                                     (void *) qs,
                                     qs->n_filters,
                                     qs->n_policy_targets);
                    if (qs->filters)
                    {
                        for (int i = 0; i < qs->n_filters; i++)
                        {
                            TableFilterState *k = &qs->filters[i];
                            CF_DEBUG_IDS_LOG("pid=%d build_seq=%llu key[%d] rel=%s relid=%u block_words=%p blocks=%u bytes=%zu n_rows=%u",
                                             (int) getpid(),
                                             (unsigned long long) qs->build_seq,
                                             i,
                                             k->relname[0] ? k->relname : "<unknown>",
                                             k->relid,
                                             (void *) k->block_words,
                                             (unsigned int) k->blocks,
                                             k->block_words_nbytes,
                                             k->n_rows);
                        }
                    }
                }
            }

            ereport(ERROR,
                    (errmsg("custom_filter_new[engine_error]: missing block_words for policy-required table rel=%s",
                            st->relname[0] ? st->relname : "<unknown>")));
        }

        if (allow)
        {
            st->tuples_passed++;
            if (tf)
                tf->passed++;
            slot = cf_store_slot(node, slot);
            cf_accum_validation_time(st, &validation_start);
            return slot;
        }

    }
}

void
cf_end(CustomScanState *node)
{
    CfExec *st = (CfExec *) node;

    if (st->tidrange_scan)
    {
        table_endscan(st->tidrange_scan);
        st->tidrange_scan = NULL;
        st->tidrange_active = false;
    }

    if (st->child_plan)
    {
        ExecEndNode(st->child_plan);
        st->child_plan = NULL;
    }

    

    CF_TRACE_LOG( "custom_filter_new exec: rel=%s oid=%u seen=%llu passed=%llu misses=%llu mode=%s",
         st->relname[0] ? st->relname : "<unknown>",
         st->relid,
         (unsigned long long) st->tuples_seen,
         (unsigned long long) st->tuples_passed,
         (unsigned long long) st->misses,
         cf_debug_mode_name(cf_debug_mode));

    CF_TRACE_LOG( "custom_filter_new: row validation time = %.3f ms", st->row_validation_ms);

    if (cf_profile_rescan && st->relid != InvalidOid)
    {
        CF_RESCAN_LOG("event=EndCustomScan pid=%d build_seq=%llu node=%p rel=%s relid=%u scan=%s filter=%s rescans=%llu tuples_seen=%llu tuples_passed=%llu",
                      (int) getpid(),
                      (unsigned long long) (cf_query_state ? cf_query_state->build_seq : 0),
                      (void *) st,
                      st->relname[0] ? st->relname : "<unknown>",
                      st->relid,
                      st->scan_type ? st->scan_type : "<unknown>",
                      st->filter ? "on" : "off",
                      (unsigned long long) st->rescan_calls,
                      (unsigned long long) st->tuples_seen,
                      (unsigned long long) st->tuples_passed);
    }

    if (cf_query_state) {
        double accounted_ms = 0.0;
        double overhead_ms = 0.0;
        cf_query_state->filter_ms += st->row_validation_ms;
        cf_query_state->custom_scan_total_ms += st->row_validation_ms;
        cf_query_state->child_exec_ms += st->child_exec_ms;
        cf_query_state->child_next_calls_total += st->child_next_calls;
        cf_query_state->ctid_extract_ms += st->ctid_extract_ms;
        cf_query_state->ctid_to_rid_ms += st->ctid_to_rid_ms;
        cf_query_state->allow_check_ms += st->allow_check_ms;
        cf_query_state->projection_ms += st->projection_ms;
        cf_query_state->rows_seen += st->tuples_seen;
        cf_query_state->rows_passed += st->tuples_passed;
        cf_query_state->ctid_misses += st->misses;
        cf_query_state->blocks_seen += st->blocks_seen;
        cf_query_state->blocks_skipped += st->blocks_skipped;
        if (st->filter)
        {
            if (st->scan_mode == CF_SCAN_MODE_EMPTY)
                cf_query_state->scan_mode_empty_tables++;
            else if (st->scan_mode == CF_SCAN_MODE_ALL)
                cf_query_state->scan_mode_all_tables++;
            else if (st->scan_mode == CF_SCAN_MODE_TID)
                cf_query_state->scan_mode_tid_tables++;
            else
                cf_query_state->scan_mode_filter_tables++;
        }
        cf_query_state->tid_blocks_visited += st->tid_blocks_visited;
        cf_query_state->tid_tuples_fetched += st->tid_tuples_fetched;
        cf_query_state->tid_offsets_checked += st->tid_offsets_checked;
        cf_query_state->tid_offsets_passed += st->tid_offsets_passed;
        cf_query_state->tid_fetch_ms += st->tid_fetch_ms;
        cf_query_state->tid_qual_ms += st->tid_qual_ms;
        cf_query_state->tid_heap_fetch_ms += st->tid_heap_fetch_ms;
        cf_query_state->tid_slot_store_ms += st->tid_slot_store_ms;
        cf_query_state->tid_visibility_ms += st->tid_visibility_ms;
        if (st->empty_short_circuit_recorded)
            cf_query_state->empty_short_circuit_tables++;
        cf_query_state->empty_short_circuit_hits += st->empty_short_circuit_calls;
        cf_query_state->empty_short_circuit_ms += st->empty_short_circuit_ms;

        accounted_ms = st->child_exec_ms +
                       st->ctid_extract_ms +
                       st->ctid_to_rid_ms +
                       st->allow_check_ms +
                       st->projection_ms +
                       st->tid_fetch_ms +
                       st->tid_qual_ms +
                       st->empty_short_circuit_ms;
        if (st->row_validation_ms > accounted_ms)
            overhead_ms = st->row_validation_ms - accounted_ms;
        else
            overhead_ms = 0.0;
        cf_query_state->custom_scan_overhead_ms += overhead_ms;
    }

    



    st->filter = NULL;
    st->validated_filter = NULL;
    st->validated_build_seq = 0;
    st->need_filter_rebind = true;
    st->bound_build_seq = 0;
    st->attempted_filter_rebuild = false;
    st->blk_cache_valid = false;
    st->blk_cache_blkno = InvalidBlockNumber;
    st->blk_cache_present = false;
    st->blk_cache_words = NULL;
    st->scan_mode_set = false;
    st->tid_iter_initialized = false;
    st->tidrange_active = false;
}

void
cf_rescan(CustomScanState *node)
{
    CfExec *st = (CfExec *) node;

    if (cf_query_state)
        cf_filters_guard_check(cf_query_state, "ReScanCustomScan");

    if (st->child_plan)
    {
        



        if (!(st->filter && st->filter->allow_is_empty))
            ExecReScan(st->child_plan);
    }

    st->seq_rid = 0;
    if (st->tidrange_scan)
    {
        table_endscan(st->tidrange_scan);
        st->tidrange_scan = NULL;
        st->tidrange_active = false;
    }
    



    if (st->filter && st->filter->allow_is_empty &&
        cf_query_state && st->bound_build_seq == cf_query_state->build_seq)
    {
        st->scan_mode = CF_SCAN_MODE_EMPTY;
        st->scan_mode_set = true;
        st->scan_mode_density = 0.0;
        st->tid_iter_initialized = false;
        st->tid_iter_block_ord = 0;
        st->tid_iter_word_idx = 0;
        st->tid_iter_bit_min = 0;
        st->blk_cache_valid = false;
        st->blk_cache_blkno = InvalidBlockNumber;
        st->blk_cache_present = false;
        st->blk_cache_words = NULL;
        st->need_filter_rebind = false;
    }
    else
    {
        st->blk_cache_valid = false;
        st->blk_cache_blkno = InvalidBlockNumber;
        st->blk_cache_present = false;
        st->blk_cache_words = NULL;
        st->scan_mode_set = false;
        st->scan_mode_density = 1.0;
        st->scan_mode_logged = false;
        st->tid_iter_initialized = false;
        st->tid_iter_block_ord = 0;
        st->tid_iter_word_idx = 0;
        st->tid_iter_bit_min = 0;
        st->need_filter_rebind = true;
        st->validated_filter = NULL;
        st->validated_build_seq = 0;
    }
    st->rescan_calls++;
    if (cf_profile_rescan && st->relid != InvalidOid)
    {
        uint64 n = st->rescan_calls;
        bool log_now = (n <= 4) || ((n & (n - 1)) == 0) || ((n % 1024) == 0);
        if (log_now)
        {
            CF_RESCAN_LOG("event=ReScanCustomScan pid=%d build_seq=%llu node=%p rel=%s relid=%u scan=%s filter=%s rescan_count=%llu",
                          (int) getpid(),
                          (unsigned long long) (cf_query_state ? cf_query_state->build_seq : 0),
                          (void *) st,
                          st->relname[0] ? st->relname : "<unknown>",
                          st->relid,
                          st->scan_type ? st->scan_type : "<unknown>",
                          st->filter ? "on" : "off",
                          (unsigned long long) n);
        }
    }
    if (cf_debug_ids && st->relid != InvalidOid)
    {
        uint64 n = st->rescan_calls;
        bool log_now = (n <= 4) || ((n & (n - 1)) == 0) || ((n % 1024) == 0);
        if (log_now)
            cf_debug_log_scan_ids("ReScanCustomScan", st, node);
    }
}



void
cf_explain(CustomScanState *node, List *ancestors, ExplainState *es)
{
    (void) node;
    (void) ancestors;
    ExplainPropertyText("custom_filter_new", "", es);
}

bool
cf_child_is_scan(PlanState *node)
{
    if (node == NULL)
        return false;

    switch (nodeTag(node))
    {
        case T_SeqScanState:
        case T_SampleScanState:
        case T_IndexScanState:
        case T_IndexOnlyScanState:
        case T_BitmapHeapScanState:
        case T_TidScanState:
        case T_TidRangeScanState:
        case T_ForeignScanState:
        case T_FunctionScanState:
        case T_TableFuncScanState:
        case T_ValuesScanState:
        case T_CteScanState:
        case T_WorkTableScanState:
            return true;
        default:
            break;
    }

    return false;
}

TupleTableSlot *
cf_return_tuple(CustomScanState *node)
{
    ProjectionInfo *projInfo = node->ss.ps.ps_ProjInfo;

    if (projInfo)
    {
        ExprContext *econtext = node->ss.ps.ps_ExprContext;
        econtext->ecxt_scantuple = node->ss.ss_ScanTupleSlot;
        return ExecProject(projInfo);
    }

    return node->ss.ss_ScanTupleSlot;
}

void
cf_accum_validation_time(CfExec *st, instr_time *start_time)
{
    instr_time stop;
    instr_time diff;

    INSTR_TIME_SET_CURRENT(stop);
    diff = stop;
    INSTR_TIME_SUBTRACT(diff, *start_time);
    st->row_validation_ms += INSTR_TIME_GET_MILLISEC(diff);
}
