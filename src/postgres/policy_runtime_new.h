#pragma once

#include <stddef.h>
#include <stdint.h>

#include "policy_evaluator.h"

#ifdef __cplusplus
extern "C" {
#endif

// Immutable artifact view passed from PostgreSQL to PAC.
typedef struct PolicyArtifactCNew {
    const char *name;
    const void *data;
    size_t len;
} PolicyArtifactCNew;

// Allowed CTIDs and execution mode for one protected table.
typedef struct PolicyTableAllowCNew {
    const char *table;
    uint64_t *block_words;
    uint32_t *block_ids;
    uint32_t blocks;
    uint32_t total_blocks;
    uint32_t n_rows;
    uint64_t allowed_rows;
    uint32_t allowed_sids;
    uint32_t total_sids;
    double hub_prop_ms;
    double sat_ms;
    double sid_build_ms;
    int mode_hint;
    const char *mode_reason;
} PolicyTableAllowCNew;

typedef struct PolicyAllowListCNew {
    int count;
    PolicyTableAllowCNew *items;
} PolicyAllowListCNew;

typedef struct PolicyRunProfileCNew {
    double artifact_parse_ms;
    double atoms_ms;
    double propagate_ms;
    double project_ms;
    double project_mask_ms;
    double project_row_ms;
    size_t project_mask_bytes;
    int project_n_join_evals_max;
    int project_clause_words_max;
    double stamp_ms;
    double bin_ms;
    double local_sat_ms;
    double fill_ms;
    double prop_ms;
    int prop_iters;
    double decode_ms;
    double policy_total_ms;
    int clause_plan_count_max;
    uint64_t prop_join_scans_total;
    int unique_join_struct_sigs_max;
    const char *prop_table_scans;
    uint64_t signature_cache_hits;
    uint64_t signature_cache_misses;
    uint64_t term_code_scans;
    uint64_t target_full_row_scans;
    size_t target_rid_bitmap_bytes;
    size_t signature_cache_bytes;
    uint64_t active_sig_dense_count;
    uint64_t active_sig_sparse_count;
    double active_sig_density_sum;
    uint64_t domain_set_dense_count;
    uint64_t domain_set_sparse_count;
    double domain_set_density_sum;
    uint64_t block_words_blocks_allocated;
    uint64_t block_words_total_blocks;
    size_t block_words_dense_bytes;
    uint64_t block_words_nblocks;
    uint64_t block_words_nwords_per_block;
    uint64_t proj_sig_count;
    uint64_t proj_sig_total;
    uint64_t proj_sig_new;
    uint64_t proj_sig_skipped;
    uint64_t proj_mask_or_ops;
    uint64_t proj_rid_iters;
    uint64_t proj_rid_iters_scan_enforcement;
    uint64_t proj_rid_iters_dependency;
    uint64_t canon_term_map_cache_hits;
    uint64_t canon_term_map_cache_misses;
    double canon_term_map_build_ms;
    size_t canon_term_map_bytes;
    double restrict_key_index_build_ms;
    uint64_t restrict_key_index_entries;
    size_t restrict_key_index_bytes;
    double restrict_key_prune_ms;
    uint64_t sigmask_cache_hits;
    uint64_t sigmask_cache_misses;
    double sigmask_build_ms;
    size_t sigmask_bytes;
    size_t bytes_sig_ctid_masks;
    size_t bytes_block_words;
    size_t bytes_artifact_buffers_retained;
    size_t bytes_decoded_buffers_retained;
    uint64_t qual_atoms_total;
    uint64_t qual_atoms_applied;
    uint64_t qual_pruned_sigs;
    double qual_prune_ms;
    uint64_t restrict_sig_tables;
    uint64_t restrict_sig_schema_cols_total;
    size_t restrict_sig_bytes_total;
    double restrict_sig_apply_ms;
    double restrict_term_apply_ms;
    uint64_t restrict_term_sigs_kept;
    uint64_t restrict_term_sigs_dropped;
    uint64_t scan_mode_tid_tables;
    uint64_t scan_mode_filter_tables;
    uint64_t tid_blocks_visited;
    uint64_t tid_tuples_fetched;
    double tid_fetch_ms;
    double tid_qual_ms;
    double build_hubs_ms;
    double composite_stamp_ms;
    double build_context_ms;
    double signature_build_ms;
    double sat_ms;
    double project_allowset_ms;
    double prop_build_arcs_ms;
    double prop_ac_ms;
    double prop_scc_ms;
    double prop_bin_catalog_ms;
    double prop_witness_ms;
    double prop_cmp_ms;
    double semantic_dedup_ms;
    double candidate_prune_ms;
    double sig_const_fold_ms;
    uint64_t allow_cache_hit;
    uint64_t allow_cache_miss;
    double allow_cache_build_ms;
    uint64_t bin_build_rows_scanned;
    uint64_t bin_count_final;
    double bin_build_avg_probe_len;
    uint64_t bin_build_max_probe_len;
    uint64_t bin_build_rehash_count;
    uint64_t bin_build_hub_count;
    uint64_t bin_build_local_atom_count;
    uint64_t bin_build_extra_count;
} PolicyRunProfileCNew;

typedef struct PolicyRunHandleNew PolicyRunHandleNew;

PolicyRunHandleNew *policy_run_new(const PolicyArtifactCNew *arts, int art_count,
                                   const PolicyEngineInputC *in);
const PolicyAllowListCNew *policy_run_allow_list_new(const PolicyRunHandleNew *h);
const PolicyRunProfileCNew *policy_run_profile_new(const PolicyRunHandleNew *h);

#ifdef __cplusplus
}
#endif
