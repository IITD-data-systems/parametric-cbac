// Composed bounds are a decision strategy of the existing tight/block/run
// executors. There is no second target walker and no target-row decision map.
// One quantified part, one unary entry and one one-sided window: the compiled
// loop probes the SAME cells the arrival Walk fills. Depth below that entry
// does not affect the specialization. No formula/frame replay occurs on hits.
template<composed_windows::Shape Form,bool Major,bool Ready>
std::uint64_t composed_window_rows_view(TightBranch &branch,std::uint32_t base,std::uint64_t live,
        std::uint64_t *slow,composed_windows::Cells::ReadView<Major> view) {
    auto &leaf=composed_bound_leaves_.front();
    const auto at=leaf.nodes[0].children.front();auto &node=leaf.nodes[at];
    auto &cells=*node.cells.data;
    const auto *keys=node.connection->source[0];
    const auto *probes=column(node.probe).forward_ranks;
    std::uint64_t good=0;
    for(auto bits=live;bits;bits&=bits-1U) {
        const auto offset=unsigned(__builtin_ctzll(bits)),row=base+offset;
        if(!(row&4095U))CHECK_FOR_INTERRUPTS();
        target_walk_started_=true;
        const auto key=keys[row],probe=probes[row];
        bool truth=false;
        if(key!=kNullRank && probe!=kNullRank) {
            CF_COUNT(++bound_probes_;++bound_slot_checks_;);
            int answer=-1;
            if constexpr(Ready)answer=view.template probe_window<Form>(key,probe);
            if(answer>=0) {
                truth=answer==1;
                CF_COUNT(++node.arrivals;++node.point_requests;++node.probes;++bound_hits_;++node.hits;);
            } else {
                bindings_[target_node_]=row;
                // A hit bypasses the formula; a miss is still an asking point
                // of the SAME demand walk. Do not exhaust a multi-row slice
                // after its first complete witness already decides the root.
                // Partial one-sided windows prove yes only; Probe resumes the
                // walk for an uncovered arrival, never inventing a nogood.
                const auto result=composed_node_bound(leaf,at,true,probe,true);
                view=cells.template read_view<Major>();
                if(!result.supported)fail("compiled window lost its planned dependency proof");
                truth=result.covers(probe);CF_COUNT(++*slow;);
            }
        }
        if(truth!=composed_window_negated_)good|=std::uint64_t{1}<<offset;
        CF_COUNT(++bound_target_rows_;
            composed_run_causes_[row%composed_run_causes_.size()]=node.shared_group;
            if(functional_composed_program_)++shared_bound_groups_[node.shared_group].root_decisions;);
        if constexpr(!Ready)if(view.allocated())
            return good|composed_window_rows_view<Form,Major,true>(branch,base,bits&(bits-1U),slow,view);
    }
    return good;
}

template<composed_windows::Shape Form,bool Major>
std::uint64_t composed_window_rows_layout(TightBranch &branch,std::uint32_t base,std::uint64_t live,std::uint64_t *slow) {
    auto &leaf=composed_bound_leaves_.front();
    const auto view=leaf.nodes[leaf.nodes[0].children.front()].cells.data->template read_view<Major>();
    if(view.allocated())return composed_window_rows_view<Form,Major,true>(branch,base,live,slow,view);
    return composed_window_rows_view<Form,Major,false>(branch,base,live,slow,view);
}

template<composed_windows::Shape Form>
std::uint64_t composed_window_rows(TightBranch &branch,std::uint32_t base,std::uint64_t live,std::uint64_t *slow) {
    const auto &leaf=composed_bound_leaves_.front();
    if(leaf.nodes[leaf.nodes[0].children.front()].cells.data->rank_major())
        return composed_window_rows_layout<Form,true>(branch,base,live,slow);
    return composed_window_rows_layout<Form,false>(branch,base,live,slow);
}

bool compile_composed_window_loop(TightBranch &branch) {
    using K=FormulaNode;
    if(composed_bound_leaves_.size()!=1U)return false;
    const auto *formula=bound_formula_.get();composed_window_negated_=false;
    if(formula->kind==K::Not){composed_window_negated_=true;formula=formula->left.get();}
    if(formula->kind!=K::Branch || formula->leaf_id!=0)return false;
    auto &leaf=composed_bound_leaves_.front();
    if(!leaf.target_atoms.empty() || !leaf.target_groups.empty() || leaf.nodes[0].children.size()!=1U)return false;
    const auto &node=leaf.nodes[leaf.nodes[0].children.front()];
    if(!node.has_probe || node.probe.node_id!=target_node_ || node.connection->entries.size()!=1U ||
       !column(node.probe).forward_ranks)return false;
    const auto shape=node.cells.data->shape();
    if(shape==composed_windows::Shape::lower)
        branch.loop=&FusedWalkRuntime::composed_window_rows<composed_windows::Shape::lower>;
    else if(shape==composed_windows::Shape::upper)
        branch.loop=&FusedWalkRuntime::composed_window_rows<composed_windows::Shape::upper>;
    else return false;
    return true;
}

std::uint64_t composed_tight_rows(TightBranch &,std::uint32_t base,std::uint64_t live,std::uint64_t *slow) {
    std::uint64_t good=0;
    for(auto bits=live;bits;bits&=bits-1U) {
        const auto offset=unsigned(__builtin_ctzll(bits));const auto row=base+offset;
        if(!(row&4095U))CHECK_FOR_INTERRUPTS();
        if(composed_target_truth(row))good|=std::uint64_t{1}<<offset;
        CF_COUNT(++*slow;composed_run_causes_[row%composed_run_causes_.size()]=composed_last_cause_;);
    }
    return good;
}

void composed_credit_runs(TightBranch &branch,std::uint32_t base,std::uint32_t size,
                          std::uint64_t live,std::uint64_t selected) {
    for(unsigned offset=0;offset<size;++offset) {
        const auto bit=std::uint64_t{1}<<offset;
        if(selected&bit)branch.composed_carry_cause=composed_run_causes_[(base+offset)%composed_run_causes_.size()];
        else if(live&bit) {
            if(branch.composed_carry_cause==SIZE_MAX)++shared_target_filter_decisions_;
            else ++shared_bound_groups_[branch.composed_carry_cause].root_decisions;
        }
    }
}

bool run_composed_tight_policy(std::uint32_t rows,std::vector<std::uint64_t> &allowed) {
    if(!cf_tight_loop)return run_composed_bounds(rows,allowed);
    std::vector<TightBranch> branches(1);auto &branch=branches.front();
    branch.composed_policy=true;branch.loop=&FusedWalkRuntime::composed_tight_rows;
    compile_composed_window_loop(branch);
    branch.block_loop=&FusedWalkRuntime::block_scalar_words;
    branch.block_batched=cf_block_target_loop;
    CF_COUNT(composed_run_causes_.resize(std::max(64,cf_block_target_rows)););
    if(cf_run_reuse && !run_columns_.empty()) {
        // Whole-policy runs use EVERY target operand, not only its entering
        // key: distinct probe values/target filters must never share a verdict.
        branch.run_columns=run_columns_;branch.run_rows=rows;
        branch.row_loop=branch.loop;branch.loop=&FusedWalkRuntime::run_lean_branch;
        branch.base_block_loop=branch.block_loop;branch.block_loop=&FusedWalkRuntime::run_block_branch;
    }
    const auto started=std::chrono::steady_clock::now();std::uint64_t slow=0;
    if(cf_block_target_loop)run_block_words(branches,rows,allowed,&slow);
    else {cf_perf_metric_set("block_loop_used",0);run_lean_words(branches,rows,allowed,&slow);}
    cf_perf_metric_set("tight_loop_used",1);
    cf_perf_metric_set("tight_loop_build_ms",0);
    cf_perf_metric_set("tight_loop_ms",elapsed_ms(started,std::chrono::steady_clock::now()));
    cf_perf_metric_set("tight_loop_slow_arrivals",slow);
    cf_perf_metric_set("formula_rank_cache_used",0);
    return true;
}
