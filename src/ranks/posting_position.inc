struct PostingPositionPlan {
    bool enabled=false,verdict_safe=false,store_admitted=false;
    ColumnRef primary,source;
    std::vector<ColumnRef> secondary,outside;
    std::vector<const std::uint32_t*> forward_columns;
    std::size_t rows=0;
    posting_position::Cells cells;
};
std::vector<std::vector<PostingPositionPlan>> posting_position_plans_;
std::uint64_t posting_position_calls_=0,posting_position_scan_rows_=0,posting_position_unique_=0;
std::uint64_t posting_position_multiple_=0,posting_position_empty_=0,posting_position_hits_=0;
std::uint64_t posting_position_writes_=0,posting_position_good_hits_=0,posting_position_bad_hits_=0;
std::uint64_t posting_position_tail_evals_=0,posting_position_unsafe_context_=0;
std::size_t posting_position_bytes_=0,posting_position_plan_count_=0;
double posting_position_scan_ms_=0,posting_position_cell_ms_=0,posting_position_tail_ms_=0;
std::uint64_t posting_position_profile_samples_=0;

void configure_posting_positions() {
    posting_position_plans_.resize(dag_.size());
    if(composed_bound_program_)return; // the position now holds a boundary, not a point verdict
    for(std::size_t node=1;node<dag_.size();++node) {
        posting_position_plans_[node].resize(leaves_.size());
        if(fused_node_is_mixed(dag_[node]))continue;
        bool any=false;
        for(auto bits=dag_[node].leaves;bits;bits&=bits-1U) {
            const auto leaf=std::size_t(__builtin_ctzll(bits));
            const auto *edge=dag_[node].edge_by_leaf[leaf];
            if(!edge || edge->op!=POLICY_OP_EQ)continue;
            auto &plan=posting_position_plans_[node][leaf];
            const auto occurrence=dag_[node].occurrence_by_leaf[leaf];
            plan.primary=dag_[node].candidate_is_left_by_leaf[leaf] ? edge->left : edge->right;
            plan.source=dag_[node].candidate_is_left_by_leaf[leaf] ? edge->right : edge->left;
            for(const auto *atom:dag_[node].filters_by_leaf[leaf]) {
                if(atom->right_is_const || atom->op!=POLICY_OP_EQ)continue;
                const bool left=atom->left.node_id==occurrence,right=atom->right.node_id==occurrence;
                if(left==right)continue;
                const auto &inside=left ? atom->left : atom->right;
                const auto &outside=left ? atom->right : atom->left;
                if(column(inside).domain!=column(outside).domain)continue;
                plan.secondary.push_back(inside);plan.outside.push_back(outside);
                plan.forward_columns.push_back(column(inside).forward_ranks);
            }
            if(plan.secondary.empty())continue;
            plan.verdict_safe=true;
            for(const auto &dependency:dependencies_[node][leaf]) {
                bool fixed=same_ref(dependency,plan.source);
                for(const auto &outside:plan.outside)fixed=fixed || same_ref(dependency,outside);
                if(!fixed){plan.verdict_safe=false;break;}
            }
            // Proving a unique posting requires scanning the complete slice.
            // If an additional outside operand prevents keeping its verdict,
            // that proof buys no reuse and can defeat the ordinary early exit.
            // Complete-window programs have a separate boundary cache above;
            // the point-verdict solver must not intercept these unsafe rests.
            if(!plan.verdict_safe)continue;
            plan.rows=column(plan.primary).forward_rows;
            // Reservation is metadata only; allocate/fill the cells on arrival.
            plan.store_admitted=cf_posting_position_store && plan.verdict_safe &&
                reserve_dense_cache((plan.rows+3U)/4U);
            plan.enabled=true;any=true;++posting_position_plan_count_;
        }
        if(any)node_solvers_[node]=&FusedWalkRuntime::solve_node_posting_position;
    }
}

bool posting_position_truth(std::size_t node,std::size_t leaf,bool *truth) {
    auto &plan=posting_position_plans_[node][leaf];
    if(!plan.enabled)return false;
    if(!target_walk_started_)fail("posting scan before first arrival");
    const auto parent_row=bindings_[plan.source.node_id];
    if(parent_row<0)return false;
    const auto rank=row_local_rank(plan.source,parent_row);
    if(rank==kNullRank){*truth=false;return true;}
    // Fill only the asking request's remaining equality operands.
    std::array<std::uint32_t,16> values{};
    if(plan.outside.size()>values.size())return false;
    for(std::size_t i=0;i<plan.outside.size();++i) {
        const auto bound=bindings_[plan.outside[i].node_id];if(bound<0)return false;
        values[i]=row_local_rank(plan.outside[i],bound);
        if(values[i]==kNullRank){*truth=false;return true;}
    }
    auto &index=column(plan.primary);
    CF_COUNT(++posting_position_calls_);
    const bool profile=cf_engine_profile && ((posting_position_calls_&1023U)==0U);
    std::chrono::steady_clock::time_point start;
    if(profile)start=std::chrono::steady_clock::now();
    const auto row_at=[&](std::uint32_t p){return u32le(index.cix.child_rows+4ULL*p);};
    const auto begin=index.cix.begin(rank),end=index.cix.end(rank);
    posting_position::Match match;
    if(plan.forward_columns.size()==1U) {
        const auto *forward=plan.forward_columns.front();const auto filled=values[0];
        match=posting_position::scan(begin,end,row_at,[&](std::uint32_t row){return forward[row]==filled;});
    } else match=posting_position::scan(begin,end,row_at,[&](std::uint32_t row) {
        for(std::size_t i=0;i<plan.forward_columns.size();++i)
            if(plan.forward_columns[i][row]!=values[i])return false;
        return true;
    });
    // These are real witness row/forward-rank reads, even on verdict hits.
    partner_touches_+=match.scanned;CF_COUNT(node_partner_touches_[node]+=match.scanned;
        posting_position_scan_rows_+=match.scanned;);
    if(profile){posting_position_scan_ms_+=elapsed_ms(start,std::chrono::steady_clock::now());++posting_position_profile_samples_;}
    if(!match.count){CF_COUNT(++posting_position_empty_);*truth=false;return true;}
    if(match.count!=1U){CF_COUNT(++posting_position_multiple_);return false;}
    CF_COUNT(++posting_position_unique_);
    if(profile)start=std::chrono::steady_clock::now();
    if(plan.store_admitted) {
        const auto state=plan.cells.get(match.position);
        if(state) {
            *truth=state==1U;
            CF_COUNT(++posting_position_hits_;if(*truth)++posting_position_good_hits_;else ++posting_position_bad_hits_;);
            if(profile)posting_position_cell_ms_+=elapsed_ms(start,std::chrono::steady_clock::now());
            return true;
        }
    } else if(!plan.verdict_safe)CF_COUNT(++posting_position_unsafe_context_);
    if(profile){posting_position_cell_ms_+=elapsed_ms(start,std::chrono::steady_clock::now());start=std::chrono::steady_clock::now();}
    CF_COUNT(++posting_position_tail_evals_);
    for(const auto occurrence:dag_[node].bound_occurrences)bindings_[occurrence]=match.row;
    const auto bit=std::uint64_t{1}<<leaf;
    auto passing=evaluate_filters_with_rank_proof(node,bit,nullptr);
    passing=rank_solve_children(node,passing,nullptr);
    for(const auto occurrence:dag_[node].bound_occurrences)bindings_[occurrence]=-1;
    *truth=(passing&bit)!=0;
    if(!aborted_ && plan.store_admitted) {
        const auto before=plan.cells.bytes();plan.cells.arrive(plan.rows);
        posting_position_bytes_+=plan.cells.bytes()-before;
        if(plan.cells.get(match.position) && (plan.cells.get(match.position)==1U)!=*truth)
            fail("posting-position decision flipped");
        plan.cells.put(match.position,*truth);CF_COUNT(++posting_position_writes_);
    }
    if(profile)posting_position_tail_ms_+=elapsed_ms(start,std::chrono::steady_clock::now());
    return !aborted_;
}

std::uint64_t solve_node_posting_position(std::size_t node,std::uint64_t requested,std::uint64_t settle_on_success) {
    std::uint64_t done=0,good=0;
    for(auto bits=requested & dag_[node].leaves;bits && !aborted_;bits&=bits-1U) {
        const auto leaf=std::size_t(__builtin_ctzll(bits));bool truth=false;
        // Preserve existing boundary/envelope shortcuts before scanning again.
        if(interval_truth(node,leaf,&truth) || posting_position_truth(node,leaf,&truth)) {
            const auto bit=std::uint64_t{1}<<leaf;done|=bit;if(truth)good|=bit;
        }
    }
    if(good&settle_on_success)settle(good&settle_on_success,good&settle_on_success);
    const auto rest=requested & ~done;
    return good | (rest && !aborted_ ? solve_node_v4(node,rest,settle_on_success) : 0U);
}

void report_posting_positions() {
    cf_perf_metric_set("posting_position_plans",posting_position_plan_count_);
    cf_perf_metric_set("posting_position_calls",posting_position_calls_);
    cf_perf_metric_set("posting_position_scan_rows",posting_position_scan_rows_);
    cf_perf_metric_set("posting_position_unique",posting_position_unique_);
    cf_perf_metric_set("posting_position_multiple_fallbacks",posting_position_multiple_);
    cf_perf_metric_set("posting_position_empty",posting_position_empty_);
    cf_perf_metric_set("posting_position_hits",posting_position_hits_);
    cf_perf_metric_set("posting_position_writes",posting_position_writes_);
    cf_perf_metric_set("posting_position_unsafe_context",posting_position_unsafe_context_);
    cf_perf_metric_set("posting_position_tail_evals",posting_position_tail_evals_);
    cf_perf_metric_set("posting_position_bytes",posting_position_bytes_);
    cf_perf_metric_set("posting_position_profile_samples",posting_position_profile_samples_);
    cf_perf_metric_set("posting_position_sample_scan_ms",posting_position_scan_ms_);
    cf_perf_metric_set("posting_position_sample_cell_ms",posting_position_cell_ms_);
    cf_perf_metric_set("posting_position_sample_tail_ms",posting_position_tail_ms_);
}
