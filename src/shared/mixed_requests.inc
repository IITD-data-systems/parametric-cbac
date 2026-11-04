// Only cross-operator nodes call this routine. V4's other iterators and loops
// remain separate and unchanged. No per-rank reached-row/shared-record cache.
// The separate cold rank loop takes a segment instead of looking up the whole
// request again. The existing V4 solver and rank-loop function stay unchanged.
MEMENTO_ITERATOR_COLD
std::uint64_t MEMENTO_METHOD(solve_exclusive_segment)(std::size_t node,std::uint64_t bit,
                                     std::uint32_t begin,std::uint32_t end)
#ifdef MEMENTO_DECLARE_COLD
;
#else
{
    LookupResult range{};range.count=1;range.ranges[0]={begin,end};
    if(rank_store_mode_)return solve_rank_node_exclusive(node,bit,0U,range);
    const auto leaf=unsigned(__builtin_ctzll(bit));
    const auto &edge=*dag_[node].edge_by_leaf[leaf];
    const auto &candidate=dag_[node].candidate_is_left_by_leaf[leaf] ? edge.left : edge.right;
    auto &index=column(candidate);
    for(auto rank=begin;rank<end && !aborted_;++rank) {
        if(!(rank&4095U))CHECK_FOR_INTERRUPTS();
        for(auto cursor=index.cix.begin(rank);cursor<index.cix.end(rank) && !aborted_;++cursor) {
            const auto row=u32le(index.cix.child_rows+std::size_t(cursor)*4U);
            ++partner_touches_;CF_COUNT(++node_partner_touches_[node]);
            for(int occurrence:dag_[node].bound_occurrences)bindings_[occurrence]=row;
            auto passing=atom_holds(edge) ? evaluate_filters(node,bit) : 0U;
            for(auto child:dag_[node].children) {
                const auto needed=passing & dag_[child].leaves;
                if(needed)passing&=~needed|solve_node(child,needed,0U);
                if(!passing || aborted_)break;
            }
            for(int occurrence:dag_[node].bound_occurrences)bindings_[occurrence]=-1;
            if(passing)return bit;
        }
    }
    return 0U;
}
#endif

MEMENTO_ITERATOR_COLD
std::uint64_t MEMENTO_METHOD(solve_mixed_requests)(std::size_t node,std::uint64_t requested,
                                   std::uint64_t settle_on_success)
#ifdef MEMENTO_DECLARE_COLD
;
#else
{
    if(!(requested&(requested-1U)))return solve_node_v4(node,requested,settle_on_success);
    auto &connection=dag_[node];requested&=connection.leaves;
    if(!requested || aborted_)return 0U;
    // Per-request shortcuts run BEFORE admission to any shared iterator.
    // Chain projections/boundaries have already had their normal V4 chance in
    // evaluate_target; intervals and terminal lookups belong at this node.
    std::uint64_t live=requested,result=0,enabled=0;
    for(auto bits=live;bits && !aborted_;bits&=bits-1U) {
        const auto leaf=unsigned(__builtin_ctzll(bits));const auto bit=std::uint64_t{1}<<leaf;
        bool truth=false;
        if(interval_truth(node,leaf,&truth)) {
            live&=~bit;if(truth)result|=bit;
            if(bit & settle_on_success)settle(bit,truth ? bit : 0U);
        }
    }
    if(!live || aborted_)return result;
    apply_terminal_groups(node,live,&result,&live,settle_on_success);
    if(const auto done=(requested & ~live) & settle_on_success)settle(done,result & done);
    if(!live || aborted_)return result;
    const auto first=unsigned(__builtin_ctzll(requested));
    const auto &edge=*connection.edge_by_leaf[first];
    const auto &candidate=connection.candidate_is_left_by_leaf[first] ? edge.left : edge.right;
    auto &index=column(candidate);
    std::array<RankPredicateInstance,64> instances{};
    full_reuse::MixedRequests requests;
    for(auto bits=live;bits;bits&=bits-1U) {
        const auto leaf=unsigned(__builtin_ctzll(bits));const auto bit=std::uint64_t{1}<<leaf;
        const auto &own=*connection.edge_by_leaf[leaf];
        const auto lookup=edge_lookup(own,connection.candidate_is_left_by_leaf[leaf]);
        for(int i=0;i<lookup.count;++i)requests.add(leaf,lookup.ranges[i].first,lookup.ranges[i].second);
        if(rank_store_mode_ && rank_store_.enabled(rank_full_plans_[node][leaf].id)) {
            enabled|=bit;instances[leaf]=rank_fill_predicate(rank_full_plans_[node][leaf]);
            // Read V4's own range envelope as well as cross-operator summaries.
            // It can have been filled by an independent/exclusive V4 path.
            const auto own_envelope=rank_envelopes_.find(instances[leaf]);
            if(lookup.count==1 && own_envelope!=rank_envelopes_.end()) {
                const auto &e=own_envelope->second;const auto r=lookup.ranges[0];
                bool known=false,good=false;
                if(r.first==0U) {
                    if(e.smallest_good<r.second){known=true;good=true;}
                    else known=r.second<=e.false_prefix_end;
                }
                if(!known && r.second==index.cix.rank_count) {
                    if(e.smallest_good!=UINT32_MAX && e.largest_good>=r.first){known=true;good=true;}
                    else known=r.first>=e.false_suffix_begin;
                }
                if(known){live&=~bit;if(good)result|=bit;CF_COUNT(++rank_range_hits_);continue;}
            }
            const auto found=mixed_envelopes_.find(instances[leaf]);
            if(found!=mixed_envelopes_.end()) {
                bool known=true,good=false;
                for(const auto &range:requests.requests[leaf]) {
                    bool part=false;
                    if(found->second.range(range.first,range.second,index.cix.rank_count,&part)) {
                        if(part){good=true;break;}
                    } else known=false;
                }
                if(good || known) {
                    live&=~bit;if(good)result|=bit;
                    CF_COUNT(++rank_range_hits_);
                }
            }
        }
        if(requests.requests[leaf].empty())live&=~bit; // NULL/empty range: EXISTS false
    }
    // An empty/exhaustively cached-false request is decided too. Raw truth is
    // passed to the existing formula, which alone applies outer polarity.
    if(const auto done=(requested & ~live) & settle_on_success)settle(done,result & done);
    if(!live || aborted_)return result;
    // Disjoint requests never join a shared iterator. In particular =/!=,
    // =/>, <=/> and >=/< retain the complete V4 request path and shortcuts.
    if(!requests.overlaps(live)) {
        for(auto bits=live;bits && !aborted_;bits&=bits-1U) {
            const auto bit=bits & -bits;
            const auto good=solve_node_v4(node,bit,settle_on_success);
            result|=good;
            if(!aborted_ && (bit & settle_on_success))settle(bit,good);
        }
        return result;
    }
    CF_COUNT(++node_calls_[node]);
    requests.unite(live);
    for(const auto &range:requests.united) {
        for(auto rank=range.first;rank<range.second && live && !aborted_;++rank) {
            // Requests can settle inside a posting. Seek past intervals that
            // belonged only to them; do not walk a now-dead rank domain.
            rank=requests.next(rank,live,range.second);
            if(rank>=range.second)break;
            if(!(rank&4095U))CHECK_FOR_INTERRUPTS();
            const auto admitted=requests.admitted(rank,live);
            if(!admitted)continue; // settled requests cannot cause more row reads
            // Only the intersection of at least two LIVE requests is shared.
            // Exclusive spans use V4's loop over that span, not the union loop.
            if(!(admitted & (admitted-1U))) {
                const auto stop=requests.segment_end(rank,live,range.second);
                const auto good=solve_exclusive_segment(node,admitted,rank,stop);
                result|=good;live&=~good;
                if(const auto settled=good & settle_on_success)settle(settled,settled);
                rank=stop-1U;
                if(!aborted_) {
                    const auto exhausted=live & ~requests.future(stop,live);
                    live&=~exhausted;
                    if(const auto settled=exhausted & settle_on_success)settle(settled,0U);
                }
                continue;
            }
            const auto begin=index.cix.begin(rank),end=index.cix.end(rank);
            auto scan=admitted;std::uint64_t good=0;
            for(auto bits=scan&enabled;bits;bits&=bits-1U) {
                const auto leaf=unsigned(__builtin_ctzll(bits));const auto bit=std::uint64_t{1}<<leaf;
                bool truth=false;
                if(rank_lookup(node,rank,instances[leaf],&truth,end-begin)) {
                    scan&=~bit;if(truth)good|=bit;
                }
            }
            if(const auto settled=good & settle_on_success)settle(settled,settled);
            // One posting walk for the union of live requests. Each complete
            // witness is checked with its own incoming operator and its own Rest.
            for(auto cursor=begin;cursor<end && scan && !aborted_;++cursor) {
                if(!(cursor&4095U))CHECK_FOR_INTERRUPTS();
                const auto row=u32le(index.cix.child_rows+std::size_t(cursor)*4U);
                ++partner_touches_;CF_COUNT(++node_partner_touches_[node]);
                for(int occurrence:connection.bound_occurrences)bindings_[occurrence]=row;
                std::uint64_t connected=0;
                for(auto bits=scan;bits;bits&=bits-1U) {
                    const auto leaf=unsigned(__builtin_ctzll(bits));
                    if(atom_holds(*connection.edge_by_leaf[leaf]))connected|=std::uint64_t{1}<<leaf;
                }
                auto passing=evaluate_filters(node,connected);
                // Children recurse for a complete joint witness, never combine
                // successes from different rows. No operator-specific proof cell.
                for(auto child:connection.children) {
                    const auto needed=passing & dag_[child].leaves;
                    if(needed)passing&=~needed|solve_node(child,needed,0U);
                    if(!passing || aborted_)break;
                }
                for(int occurrence:connection.bound_occurrences)bindings_[occurrence]=-1;
                good|=passing;scan&=~passing;
                const auto settled=passing & settle_on_success;
                if(settled)settle(settled,settled);
            }
            for(auto bits=(aborted_ ? good : admitted)&enabled;bits;bits&=bits-1U) {
                const auto leaf=unsigned(__builtin_ctzll(bits));const auto bit=std::uint64_t{1}<<leaf;
                const bool truth=(good&bit)!=0;
                if(!rank_insert(node,rank,instances[leaf],truth))fail("mixed request decision flipped");
                mixed_envelopes_[instances[leaf]].observe(rank,truth,index.cix.rank_count,
                    [&](auto r){return rank_store_.known_false(r,instances[leaf]);});
            }
            result|=good;live&=~good;
            if(const auto settled=good&settle_on_success)settle(settled,settled);
            if(!aborted_) {
                const auto exhausted=live & ~requests.future(rank+1U,live);
                live&=~exhausted;
                if(const auto settled=exhausted & settle_on_success)settle(settled,0U);
            }
        }
        if(!live || aborted_)break;
    }
    return result;
}
#endif
