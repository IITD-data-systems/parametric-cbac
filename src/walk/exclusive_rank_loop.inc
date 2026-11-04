// Separate cold specialization: the unrestricted V4 function remains untouched.
MEMENTO_ITERATOR_COLD
std::uint64_t MEMENTO_METHOD(solve_rank_node_exclusive)(std::size_t node, std::uint64_t requested,
                                  std::uint64_t settle_on_success, const LookupResult &lookup)
#ifdef MEMENTO_DECLARE_COLD
;
#else
{
        requested &= dag_[node].leaves;
        if (requested == 0U || aborted_) return 0U;
        CF_COUNT(++node_calls_[node]);
        std::uint64_t remaining = requested, result = 0U;
        apply_terminal_groups(node, requested, &result, &remaining, settle_on_success);
        if (!remaining || aborted_) return result;
        std::uint32_t proof_key = kNullRank;
        std::uint64_t proof_decided = 0, proof_truth = 0;
        lookup_rank_proof(node, remaining, &proof_key, &proof_decided, &proof_truth);
        remaining &= ~proof_decided;
        result |= proof_truth & proof_decided;
        CF_COUNT(rank_proof_hits_ += __builtin_popcountll(proof_decided));
        CF_COUNT(rank_proof_good_hits_ += __builtin_popcountll(proof_truth & proof_decided));
        CF_COUNT(rank_proof_no_good_hits_ += __builtin_popcountll(proof_decided & ~proof_truth));
        if (!remaining) return result;
        RankProofCell *active_proof = rank_active_proof(node, proof_key);
        bool visited_partner = false;
        const std::uint64_t checks_before = rank_store_.probes;
        const std::size_t representative = __builtin_ctzll(remaining);
        const NormalizedAtom &edge = *dag_[node].edge_by_leaf[representative];
        const bool candidate_left = dag_[node].candidate_is_left_by_leaf[representative];
        const ColumnRef &candidate = candidate_left ? edge.left : edge.right;
        ColumnIndex &index = column(candidate);
        tuple_index::Rows tuple_rows{};
        bool tuple_used=false;
        // DAG nodes are acyclic; each active recursive frame has its own scratch slots.
        auto &full = rank_full_instances_[node];
        auto &local = rank_local_instances_[node];
        std::uint64_t full_enabled = 0U, local_enabled = 0U;
        for (std::uint64_t bits = rank_single_visit_[node] ? 0U : remaining; bits; bits &= bits - 1U) {
            const std::size_t leaf = __builtin_ctzll(bits);
            const std::uint64_t bit = std::uint64_t{1} << leaf;
            const auto &full_plan = rank_full_plans_[node][leaf];
            const auto &local_plan = rank_local_plans_[node][leaf];
            if (rank_store_.enabled(full_plan.id)) {
                full_enabled |= bit;
                full[leaf] = rank_fill_predicate(full_plan);
            }
            if (local_plan.id != full_plan.id && rank_store_.enabled(local_plan.id)) {
                local_enabled |= bit;
                local[leaf] = rank_fill_predicate(local_plan);
            }
            if (lookup.count == 0 && edge.op == POLICY_OP_EQ) {
                const ColumnRef &parent = candidate_left ? edge.right : edge.left;
                const auto parent_row = bindings_[parent.node_id];
                const std::uint32_t empty_rank = parent_row < 0 ? kNullRank :
                    row_universe_rank(parent, parent_row);
                if (empty_rank != kNullRank) {
                    bool truth = false;
                    if ((full_enabled & bit) && rank_lookup(node, empty_rank, full[leaf], &truth, 0U, 0U) && truth)
                        fail("empty rank was learned good");
                    if (((full_enabled & bit) && !rank_insert(node, empty_rank, full[leaf], false)) ||
                        ((local_enabled & bit) && !rank_insert(node, empty_rank, local[leaf], false)))
                        fail("empty rank verdict flipped");
                }
            }
            if (!(full_enabled & bit) || edge.op == POLICY_OP_EQ) continue;
            const auto found = rank_envelopes_.find(full[leaf]);
            if (edge.op == POLICY_OP_EQ || lookup.count != 1 ||
                found == rank_envelopes_.end()) {
                rank_observe_range(node, full[leaf].id, false, 0U);
                continue;
            }
            const auto [begin, end] = lookup.ranges[0];
            const RankEnvelope &envelope = found->second;
            bool known = false, truth = false;
            if (begin == 0U) {
                if (envelope.smallest_good < end) { known = true; truth = true; }
                else if (end <= envelope.false_prefix_end) known = true;
            }
            if (!known && end == index.cix.rank_count) {
                if (envelope.smallest_good != UINT32_MAX && envelope.largest_good >= begin) {
                    known = true; truth = true;
                } else if (begin >= envelope.false_suffix_begin) known = true;
            }
            if (known) {
                // Good skips at least one witness; nogood skips every row in this range.
                rank_observe_range(node, full[leaf].id, true,
                    truth ? 1U : posting_rows(index, lookup));
                CF_COUNT(++rank_range_hits_);
                remaining &= ~bit;
                if (truth) result |= bit;
            } else {
                rank_observe_range(node, full[leaf].id, false, 0U);
            }
        }
        for (int interval = 0; interval < lookup.count && remaining && !aborted_; ++interval) {
            for (std::uint32_t rank = lookup.ranges[interval].first;
                 rank < lookup.ranges[interval].second && remaining && !aborted_; ++rank) {
                if ((rank & 4095U) == 0U) CHECK_FOR_INTERRUPTS();
                std::uint32_t begin = index.cix.begin(rank);
                std::uint32_t end = index.cix.end(rank);
                const bool multirow = end - begin > 1U;
                if (multirow) {
                    CF_COUNT(++rank_multirow_arrivals_);
                    CF_COUNT(++rank_multirow_by_node_[node].arrivals);
                }
                std::uint64_t scan = remaining, rank_good = 0U, local_good = 0U;
                for (std::uint64_t bits = scan & (full_enabled | local_enabled); bits; bits &= bits - 1U) {
                    const std::size_t leaf = __builtin_ctzll(bits);
                    const std::uint64_t bit = std::uint64_t{1} << leaf;
                    bool truth = false;
                    if ((full_enabled & bit) &&
                        rank_lookup(node, rank, full[leaf], &truth,
                                           end - begin)) {
                        scan &= ~bit;
                        if (composite_indexes_[node]) CF_COUNT(++composite_decision_hits_);
                        if (truth) rank_good |= bit;
                        if (multirow) {
                            CF_COUNT(++rank_multirow_stops_);
                            auto &stats = rank_multirow_by_node_[node];
                            if (truth) CF_COUNT(++stats.good_stops);
                            else CF_COUNT(++stats.nogood_stops);
                        }
                    } else if ((local_enabled & bit) &&
                               rank_lookup(node, rank, local[leaf], &truth,
                                                  end - begin)) {
                        if (!truth) scan &= ~bit;
                        else fail("partial good must not be stored");
                    }
                }
                if (scan && composite_indexes_[node]) {
                    CF_COUNT(composite_decision_misses_ += __builtin_popcountll(scan));
                    tuple_rows = composite_rows(node, representative);
                    tuple_used=true;
                    begin = 0U;
                    end = tuple_rows.size();
                }
                if (scan && multirow) {
                    CF_COUNT(++rank_multirow_descents_);
                    CF_COUNT(++rank_multirow_by_node_[node].scans);
                }
                const std::uint64_t unresolved = scan;
                for (std::uint32_t cursor = begin; cursor < end && scan && !aborted_; ++cursor) {
                    const std::uint32_t row = tuple_used ? tuple_rows[cursor] :
                        u32le(index.cix.child_rows + cursor * 4ULL);
                    ++partner_touches_; CF_COUNT(++node_partner_touches_[node]);
                    visited_partner = true;
                    for (int occurrence : dag_[node].bound_occurrences) bindings_[occurrence] = row;
                    rank_record_row(node, proof_key, active_proof);
                    std::uint64_t passing = evaluate_filters_with_rank_proof(node, scan, active_proof);
                    local_good |= passing;
                    passing = rank_solve_children(node, passing, active_proof);
                    for (int occurrence : dag_[node].bound_occurrences) bindings_[occurrence] = -1;
                    rank_good |= passing;
                    scan &= ~passing;
                }
                const std::uint64_t completed = rank_good | (aborted_ ? 0U : unresolved);
                for (std::uint64_t bits = completed & unresolved & (full_enabled | local_enabled); bits; bits &= bits - 1U) {
                    const std::size_t leaf = __builtin_ctzll(bits);
                    const std::uint64_t bit = std::uint64_t{1} << leaf;
                    if (full_enabled & bit)
                        rank_learn(node, rank, candidate, full[leaf], (rank_good & bit) != 0U,
                                   edge.op != POLICY_OP_EQ);
                    // Only store local nogood after every row failed locally.
                    // A full good has a single joint witness by construction.
                    if ((local_enabled & bit) && !(local_good & bit) && !aborted_)
                        rank_learn(node, rank, candidate, local[leaf], false);
                }
                if (aborted_) CF_COUNT(++rank_interrupted_);
                result |= rank_good;
                remaining &= ~rank_good;
                const std::uint64_t complete_root = rank_good & settle_on_success;
                if (complete_root) settle(complete_root, complete_root);
            }
        }
        if (active_proof) {
            if (!aborted_ && !visited_partner && posting_rows(index, lookup) == 0U) {
                active_proof->decided |= dag_[node].edge_proof_bit;
                active_proof->truth &= ~dag_[node].edge_proof_bit;
                CF_COUNT(++rank_proof_atom_strengthens_);
            }
            for (auto bits = result; bits; bits &= bits - 1U) {
                const auto leaf = __builtin_ctzll(bits);
                if (!proof_key_safe_[node][leaf]) continue;
                const auto mask = subtree_proof_masks_[node][leaf];
                if (active_proof->decided & ~active_proof->truth & mask)
                    fail("our_pg rank-proof good attempted to overwrite nogood");
                CF_COUNT(rank_proof_backtrack_strengthens_ += __builtin_popcountll(mask & ~active_proof->decided));
                active_proof->decided |= mask;
                active_proof->truth |= mask;
            }
        }
        if (cf_rankstore_dump)
            CF_COUNT(++rank_checks_per_arrival_[rank_store_.probes - checks_before]);
        return result;
    }
#endif
