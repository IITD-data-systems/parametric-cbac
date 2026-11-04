// The normal V4 compiler/loops are untouched. Only genuine overlapping DAG
// groups enter this cold compiler/scheduler. Its warm tail uses V4 leaf loops.


MEMENTO_ITERATOR_COLD
bool MEMENTO_METHOD(mixed_subtree)(std::size_t node) const
#ifdef MEMENTO_DECLARE_COLD
;
#else
{
    if((node_solvers_[node]==&FusedWalkRuntime::solve_mixed_requests))return true;
    for(auto child:dag_[node].children)if(mixed_subtree(child))return true;
    return false;
}
#endif

MEMENTO_ITERATOR_COLD
bool MEMENTO_METHOD(has_compiled_request_groups)() const
#ifdef MEMENTO_DECLARE_COLD
;
#else
{
    if(!cf_decision_sharing || !cf_tight_loop || !rank_store_mode_)return false;
    for(auto node:dag_[0].children)if(mixed_subtree(node))return true;
    return false;
}
#endif

MEMENTO_ITERATOR_COLD
std::size_t MEMENTO_METHOD(grouped_boundary_cell)(const TightBranch &branch,std::uint32_t row) const
#ifdef MEMENTO_DECLARE_COLD
;
#else
{
    if(branch.global)return 0U;
    const auto rank=branch.context.local(row);
    return rank==kNullRank ? branch.window->count()-1U : rank;
}
#endif

MEMENTO_ITERATOR_COLD
void MEMENTO_METHOD(grouped_publish_boundary)(TightBranch &branch,std::uint32_t row,std::uint32_t value)
#ifdef MEMENTO_DECLARE_COLD
;
#else
{
    auto &plan=window_requests_[branch.leaf];
    if(!plan.enabled || plan.key_single_visit)return;
    composed_windows::Coverage coverage;
    coverage.add(composed_windows::ordered_window(plan.cells.shape(),value,
        plan.op==POLICY_OP_GT || plan.op==POLICY_OP_LE,column(plan.time).cix.rank_count));
    const auto before=plan.cells.bytes();record_window(plan,row,coverage);
    CF_COUNT(if(plan.cells.bytes()!=before)++branch.decision_writes;);
}
#endif

MEMENTO_ITERATOR_COLD
bool MEMENTO_METHOD(grouped_boundary_hit)(TightBranch &branch,std::uint32_t row,bool *truth)
#ifdef MEMENTO_DECLARE_COLD
;
#else
{
    if(!branch.boundary)return false;
    const auto time=branch.time.local(row);
    if(time==kNullRank){*truth=false;return true;}
    if(!branch.window)return false;
    const auto cell=grouped_boundary_cell(branch,row);
    const auto answer=branch.above ? branch.window->probe_window<composed_windows::Shape::lower>(cell,time) :
                                    branch.window->probe_window<composed_windows::Shape::upper>(cell,time);
    if(answer<0)return false;
    CF_COUNT(++branch.decision_probes;++branch.boundary_hits);
    *truth=answer==1;return true;
}
#endif

MEMENTO_ITERATOR_COLD
void MEMENTO_METHOD(grouped_independent_boundary)(TightBranch &branch,std::uint32_t row)
#ifdef MEMENTO_DECLARE_COLD
;
#else
{
    bool truth=false;
    // One request remains; Record writes the same cells the word loop probes.
    if(!window_truth(branch.leaf,row,&truth))fail("missing independent boundary");
    const auto bit=std::uint64_t{1}<<branch.leaf;settle(bit,truth ? bit : 0U);
}
#endif

// Balance/date upper tails seek from the greatest present rank; lower tails
// seek from the least. The first complete witness is therefore the exact
// extreme, not a speculative bound. Empty postings are skipped by offset
// binary search in the EXISTING inverted index, never by a domain/row pass.
MEMENTO_ITERATOR_COLD
void MEMENTO_METHOD(grouped_joint_boundary)(const CompiledRequestGroup &group,std::uint64_t requested,
        std::uint32_t row,const std::array<TightBranch*,64> &by_leaf)
#ifdef MEMENTO_DECLARE_COLD
;
#else
{
    CF_COUNT(++grouped_request_calls_);
    const auto node=group.node;const auto &connection=dag_[node];
    auto live=requested;
    full_reuse::MixedRequests requests;
    const auto first=unsigned(__builtin_ctzll(live));
    const auto &edge=*connection.edge_by_leaf[first];
    const auto &candidate=connection.candidate_is_left_by_leaf[first] ? edge.left : edge.right;
    auto &index=column(candidate);const auto count=index.cix.rank_count;
    const auto total=count ? index.cix.end(count-1U) : 0U;
    std::array<RankPredicateInstance,64> instances{};std::uint64_t enabled=0;
    for(auto bits=live;bits && !aborted_;bits&=bits-1U) {
        const auto leaf=unsigned(__builtin_ctzll(bits));const auto bit=std::uint64_t{1}<<leaf;
        const auto lookup=edge_lookup(*connection.edge_by_leaf[leaf],connection.candidate_is_left_by_leaf[leaf]);
        for(int i=0;i<lookup.count;++i)requests.add(leaf,lookup.ranges[i].first,lookup.ranges[i].second);
        if(!posting_rows(index,lookup)) {
            live&=~bit;
            if(!total)grouped_publish_boundary(*by_leaf[leaf],row,kNullRank);
            settle(bit,0U);continue;
        }
        if(rank_store_.enabled(rank_full_plans_[node][leaf].id)) {
            enabled|=bit;instances[leaf]=rank_fill_predicate(rank_full_plans_[node][leaf]);
        }
    }
    if(!live || aborted_)return;
    if(!(live&(live-1U))) {grouped_independent_boundary(*by_leaf[__builtin_ctzll(live)],row);return;}
    std::uint64_t position=group.upper ? total : 0U;
    while(live && !aborted_) {
        if(!(live&(live-1U))) {grouped_independent_boundary(*by_leaf[__builtin_ctzll(live)],row);break;}
        if((group.upper && !position) || (!group.upper && position>=total)) {
            for(auto bits=live;bits && !aborted_;bits&=bits-1U) {
                const auto leaf=unsigned(__builtin_ctzll(bits));const auto bit=std::uint64_t{1}<<leaf;
                // Entire candidate column was exhausted for this Rest.
                grouped_publish_boundary(*by_leaf[leaf],row,kNullRank);settle(bit,0U);
            }
            break;
        }
        const auto cursor=static_cast<std::uint32_t>(group.upper ? position-1U : position);
        std::uint32_t lo=0,hi=count;
        while(lo<hi){const auto mid=lo+(hi-lo)/2U;if(index.cix.end(mid)<=cursor)lo=mid+1U;else hi=mid;}
        if(lo>=count)fail("joint iterator offset outside index");
        const auto rank=lo,begin=index.cix.begin(rank),end=index.cix.end(rank);
        const auto admitted=requests.admitted(rank,live),exhausted=live&~admitted;
        // For these one-sided requests, a range ending at this frontier has
        // been fully searched. It must settle before any exclusive reads.
        for(auto bits=exhausted;bits && !aborted_;bits&=bits-1U) {
            const auto bit=bits&-bits;live&=~bit;settle(bit,0U);
        }
        if(!live || aborted_)break;
        if(!(live&(live-1U)))continue;
        auto scan=live;std::uint64_t good=0;
        for(auto bits=scan&enabled;bits;bits&=bits-1U) {
            const auto leaf=unsigned(__builtin_ctzll(bits));const auto bit=std::uint64_t{1}<<leaf;bool truth=false;
            if(rank_lookup(node,rank,instances[leaf],&truth,end-begin)){scan&=~bit;if(truth)good|=bit;}
        }
        if(scan&(scan-1U)){CF_COUNT(++grouped_shared_postings_);}
        const auto unresolved=scan;
        for(auto at=begin;at<end && scan && !aborted_;++at) {
            if(!(at&4095U))CHECK_FOR_INTERRUPTS();
            if(scan&(scan-1U)){CF_COUNT(++grouped_shared_rows_);}
            const auto witness=u32le(index.cix.child_rows+std::size_t(at)*4U);
            ++partner_touches_;CF_COUNT(++node_partner_touches_[node]);
            for(int occurrence:connection.bound_occurrences)bindings_[occurrence]=witness;
            std::uint64_t connected=0;
            for(auto bits=scan;bits;bits&=bits-1U) {
                const auto leaf=unsigned(__builtin_ctzll(bits));
                if(atom_holds(*connection.edge_by_leaf[leaf]))connected|=std::uint64_t{1}<<leaf;
            }
            auto passing=evaluate_filters(node,connected);
            for(auto child:connection.children) {
                const auto needed=passing&dag_[child].leaves;
                if(needed)passing&=~needed|solve_node(child,needed,0U);
                if(!passing || aborted_)break;
            }
            for(int occurrence:connection.bound_occurrences)bindings_[occurrence]=-1;
            good|=passing;scan&=~passing;
        }
        for(auto bits=(aborted_ ? good : unresolved)&enabled;bits;bits&=bits-1U) {
            const auto leaf=unsigned(__builtin_ctzll(bits));const auto bit=std::uint64_t{1}<<leaf;
            if(!rank_insert(node,rank,instances[leaf],bool(good&bit)))fail("joint request decision flipped");
        }
        // Every earlier posting in the chosen direction failed for each live
        // request. A complete witness now certifies its global/context extreme.
        for(auto bits=good;bits && !aborted_;bits&=bits-1U) {
            const auto leaf=unsigned(__builtin_ctzll(bits));const auto bit=std::uint64_t{1}<<leaf;
            grouped_publish_boundary(*by_leaf[leaf],row,rank);CF_COUNT(++grouped_boundary_fills_);
            live&=~bit;settle(bit,bit);
        }
        position=group.upper ? begin : end;
    }
}
#endif

MEMENTO_ITERATOR_COLD
void MEMENTO_METHOD(grouped_row)(const CompiledRequestGroup &group,std::uint32_t row,
        std::uint64_t &done,std::uint64_t &raw,std::uint64_t &ternary,
        const std::array<TightBranch*,64> &by_leaf)
#ifdef MEMENTO_DECLARE_COLD
;
#else
{
    target_walk_started_=true;bindings_[target_node_]=row;
    settled_=done;truth_=raw;formula_ternary_state_=ternary;aborted_=false;
    auto live=group.leaves&~settled_;
    const auto passing=evaluate_filters(0,live);
    if(live&~passing)settle(live&~passing,0U);
    live=passing&~settled_;
    for(auto bits=live;bits && !aborted_;bits&=bits-1U) {
        const auto leaf=unsigned(__builtin_ctzll(bits));const auto bit=std::uint64_t{1}<<leaf;bool truth=false;
        if(grouped_boundary_hit(*by_leaf[leaf],row,&truth))settle(bit,truth ? bit : 0U);
    }
    live&=~settled_;
    if(live && !aborted_) {
        if(group.boundary)grouped_joint_boundary(group,live,row,by_leaf);
        else {
            // Full V4 shortcuts still get first refusal on non-boundary groups.
            for(auto bits=live;bits && !aborted_;bits&=bits-1U) {
                const auto leaf=unsigned(__builtin_ctzll(bits));const auto bit=std::uint64_t{1}<<leaf;bool truth=false;
                if(window_truth(leaf,row,&truth) || chain_projected_truth(leaf,row,&truth))settle(bit,truth ? bit : 0U);
            }
            live&=~settled_;
            if(live && !aborted_) {
                CF_COUNT(++grouped_request_calls_);
                const auto good=solve_node(group.node,live,live);
                if(!aborted_)settle(live,good);
            }
        }
    }
    done=settled_;raw=truth_;ternary=formula_ternary_state_;
    bindings_[target_node_]=-1;aborted_=false;
}
#endif

MEMENTO_ITERATOR_COLD
bool MEMENTO_METHOD(grouped_warm)(const CompiledRequestGroup &group,const std::array<TightBranch*,64> &by_leaf)
#ifdef MEMENTO_DECLARE_COLD
;
#else
{
    unsigned cold=0;
    for(auto bits=group.leaves;bits;bits&=bits-1U) {
        auto &branch=*by_leaf[__builtin_ctzll(bits)];
        const bool ready=branch.global && branch.window && branch.window->complete(0);
        if(!ready)++cold;
    }
    return cold<=1U;
}
#endif


// Cold arrival hooks: the only compiler and outer drivers are V4's.
MEMENTO_ITERATOR_COLD
void MEMENTO_METHOD(restore_group_loops)(const CompiledRequestGroup &group)
#ifdef MEMENTO_DECLARE_COLD
;
#else
{
    for(auto bits=group.leaves;bits;bits&=bits-1U) {
        const auto leaf=unsigned(__builtin_ctzll(bits));auto &branch=*grouped_by_leaf_[leaf];
        branch.loop=grouped_v4_words_[leaf];branch.block_loop=grouped_v4_blocks_[leaf];
    }
}
#endif
MEMENTO_ITERATOR_COLD
void MEMENTO_METHOD(grouped_prepare_arrivals)(TightBranch &branch,std::uint32_t base,std::uint32_t size,const std::uint64_t *live)
#ifdef MEMENTO_DECLARE_COLD
;
#else
{
    const auto owner=grouped_owner_[branch.leaf];
    if(owner<0)return;
    auto &group=compiled_groups_[owner];
    for(std::uint32_t word=0;word<(size+63U)/64U && !grouped_warm(group,grouped_by_leaf_);++word)
        for(auto bits=live[word];bits && !grouped_warm(group,grouped_by_leaf_);bits&=bits-1U) {
            const auto offset=unsigned(__builtin_ctzll(bits));
            std::uint64_t done=0,raw=0,ternary=0;
            grouped_row(group,base+word*64U+offset,done,raw,ternary,grouped_by_leaf_);
        }
    if(grouped_warm(group,grouped_by_leaf_))restore_group_loops(group);
}
#endif
MEMENTO_ITERATOR_COLD
std::uint64_t MEMENTO_METHOD(grouped_word_hook)(TightBranch &branch,std::uint32_t base,std::uint64_t live,std::uint64_t *slow)
#ifdef MEMENTO_DECLARE_COLD
;
#else
{
    grouped_prepare_arrivals(branch,base,64U,&live);
    const auto leaf=branch.leaf;branch.loop=grouped_v4_words_[leaf];
    const auto answer=(this->*branch.loop)(branch,base,live,slow);
    grouped_v4_words_[leaf]=branch.loop;
    if(!grouped_warm(compiled_groups_[grouped_owner_[leaf]],grouped_by_leaf_))branch.loop=&FusedWalkRuntime::grouped_word_hook;
    return answer;
}
#endif
MEMENTO_ITERATOR_COLD
void MEMENTO_METHOD(grouped_block_hook)(TightBranch &branch,std::uint32_t base,std::uint32_t size,
        const std::uint64_t *live,std::uint64_t *good,std::uint64_t *scalar,std::uint64_t *cells,std::uint64_t *slow)
#ifdef MEMENTO_DECLARE_COLD
;
#else
{
    grouped_prepare_arrivals(branch,base,size,live);
    const auto leaf=branch.leaf;branch.block_loop=grouped_v4_blocks_[leaf];
    (this->*branch.block_loop)(branch,base,size,live,good,scalar,cells,slow);
    grouped_v4_blocks_[leaf]=branch.block_loop;
    if(!grouped_warm(compiled_groups_[grouped_owner_[leaf]],grouped_by_leaf_))branch.block_loop=&FusedWalkRuntime::grouped_block_hook;
}
#endif
MEMENTO_ITERATOR_COLD
void MEMENTO_METHOD(install_grouped_hooks)(std::vector<TightBranch> &branches)
#ifdef MEMENTO_DECLARE_COLD
;
#else
{
    if(!has_compiled_request_groups())return;
    grouped_owner_.fill(-1);
    for(auto &branch:branches){grouped_by_leaf_[branch.leaf]=&branch;grouped_v4_words_[branch.leaf]=branch.loop;grouped_v4_blocks_[branch.leaf]=branch.block_loop;}
    for(auto node:dag_[0].children) {
        if(!mixed_subtree(node))continue;
        const auto leaves=dag_[node].leaves;bool complete=true;
        for(auto bits=leaves;bits;bits&=bits-1U) {
            const auto leaf=unsigned(__builtin_ctzll(bits));unsigned roots=0;
            for(auto child:dag_[0].children)roots+=bool(dag_[child].leaves&(std::uint64_t{1}<<leaf));
            complete &= roots==1U;
        }
        if(!complete)continue;
        CompiledRequestGroup group;group.node=node;group.leaves=leaves;
        bool upper=true,lower=true,boundary=node_solvers_[node]==&FusedWalkRuntime::solve_mixed_requests;
        for(auto bits=leaves;bits;bits&=bits-1U) {
            const auto leaf=unsigned(__builtin_ctzll(bits));const auto &branch=*grouped_by_leaf_[leaf];
            const auto op=normalized_edge_op(*dag_[node].edge_by_leaf[leaf],dag_[node].candidate_is_left_by_leaf[leaf]);
            upper &= op==POLICY_OP_GE || op==POLICY_OP_GT;lower &= op==POLICY_OP_LE || op==POLICY_OP_LT;
            const auto &edge=*dag_[node].edge_by_leaf[leaf];
            const auto &candidate=dag_[node].candidate_is_left_by_leaf[leaf] ? edge.left : edge.right;
            boundary &= branch.boundary && !branch.key_single_visit && same_ref(window_requests_[leaf].endpoint,candidate);
        }
        group.boundary=boundary&&(upper||lower);group.upper=upper;
        for(auto bits=leaves;bits;bits&=bits-1U) {
            const auto leaf=unsigned(__builtin_ctzll(bits));grouped_owner_[leaf]=compiled_groups_.size();
            auto &branch=*grouped_by_leaf_[leaf];branch.loop=&FusedWalkRuntime::grouped_word_hook;
            if(branch.block_loop)branch.block_loop=&FusedWalkRuntime::grouped_block_hook;
        }
        compiled_groups_.push_back(group);
    }
}
#endif

