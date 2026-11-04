// Formula hits keep V4's rank-cell/bitmap path. Only a complete formula miss
// invokes the compiled per-leaf loops, whose first-arrival hooks share reads.
// In particular, enabling sharing must not disable whole-formula reuse.
MEMENTO_ITERATOR_COLD
bool MEMENTO_METHOD(grouped_formula_miss)(std::uint32_t row,std::vector<TightBranch> &branches,std::uint64_t *slow)
#ifdef MEMENTO_DECLARE_COLD
;
#else
{
    target_walk_started_=true;++target_evals_;
    const auto required=flat_positive_|flat_negative_;
    int verdict=-1;std::uint64_t ternary=0;
    if(flat_mode_!=FlatFormulaMode::none && flat_constant_>=0)verdict=flat_constant_;
    else for(auto &branch:branches) {
        const auto bit=std::uint64_t{1}<<branch.leaf;
        if(flat_mode_!=FlatFormulaMode::none && !(required&bit))continue;
        const bool good=((this->*branch.loop)(branch,row,1U,slow)&1U)!=0;
        if(flat_mode_!=FlatFormulaMode::none) {
            const bool pass=(flat_negative_&bit) ? !good : good;
            if(flat_mode_==FlatFormulaMode::conjunction && !pass){verdict=0;break;}
            if(flat_mode_==FlatFormulaMode::disjunction && pass){verdict=1;break;}
        } else {
            ternary+=formula_ternary_powers_[branch.leaf]*(good ? 2U : 1U);
            verdict=formula_truth_table_[ternary];if(verdict>=0)break;
        }
    }
    if(flat_mode_==FlatFormulaMode::conjunction && verdict<0)verdict=1;
    if(flat_mode_==FlatFormulaMode::disjunction && verdict<0)verdict=0;
    if(verdict<0)fail("grouped formula remained unresolved");
    return verdict==1;
}
#endif

MEMENTO_ITERATOR_COLD
bool MEMENTO_METHOD(run_grouped_formula_loop)(std::uint32_t rows,std::vector<std::uint64_t> &allowed,
                                             std::vector<TightBranch> &branches)
#ifdef MEMENTO_DECLARE_COLD
;
#else
{
    if(!cf_formula_rank_cache)return false;
    bool all_projected=true;
    for(const auto &plan:chain_plans_)all_projected &= plan.enabled && plan.full;
    if(all_projected)return false;
    ColumnRef operand;bool first=true;
    for(auto leaf:leaves_) {
        ColumnRef ref;
        if(!single_target_operand(*leaf,&ref))return false;
        if(!first && ref.runtime_column!=operand.runtime_column)return false;
        operand=ref;first=false;
    }
    TightStream stream;
    if(first || column_is_unique(operand) || !tight_stream(operand,rows,&stream))return false;
    const auto count=column(operand).cix.rank_count;
    if(count>200000000U || !reserve_dense_cache((std::size_t(count)+4U)/4U))return false;
    std::vector<std::uint8_t> cells((std::size_t(count)+4U)/4U,0U);
    projection_front_bytes_+=cells.capacity();
    const auto started=std::chrono::steady_clock::now();
    std::uint64_t scalar=0,hit_good=0,hit_bad=0,slow=0;
    if(cf_block_target_loop) {
        if(cf_block_target_rows%64)fail("formula block size must be a multiple of 64");
        const auto block=static_cast<std::uint32_t>(cf_block_target_rows);
        std::vector<std::uint32_t> misses;misses.reserve(block);
        for(std::uint32_t base=0;base<rows;base+=std::min(block,rows-base)) {
            CHECK_FOR_INTERRUPTS();target_walk_started_=true;misses.clear();
            const auto end=base+std::min(block,rows-base);
            for(auto row=base;row<end;++row) {
                const auto rank=stream.local(row),key=rank==kNullRank ? count : rank;
                const auto cell=(cells[key/4U]>>((key&3U)*2U))&3U;
                if(!cell){misses.push_back(row);continue;}
                if(cell==1U){allowed[row/64U]|=std::uint64_t{1}<<(row&63U);CF_COUNT(++hit_good);}
                else CF_COUNT(++hit_bad);
            }
            for(auto row:misses) {
                const auto rank=stream.local(row),key=rank==kNullRank ? count : rank;
                const auto shift=(key&3U)*2U;auto &packed=cells[key/4U];auto cell=(packed>>shift)&3U;
                if(!cell) {
                    const bool truth=grouped_formula_miss(row,branches,&slow);cell=truth ? 1U : 2U;
                    packed|=cell<<shift;++scalar;CF_COUNT(++formula_rank_entries_);
                } else {CF_COUNT(if(cell==1U)++hit_good;else ++hit_bad);}
                if(cell==1U)allowed[row/64U]|=std::uint64_t{1}<<(row&63U);
            }
        }
    } else for(std::uint32_t row=0;row<rows;++row) {
        if(!(row&4095U))CHECK_FOR_INTERRUPTS();target_walk_started_=true;
        const auto rank=stream.local(row),key=rank==kNullRank ? count : rank;
        const auto shift=(key&3U)*2U;auto &packed=cells[key/4U];auto cell=(packed>>shift)&3U;
        if(!cell) {
            const bool truth=grouped_formula_miss(row,branches,&slow);cell=truth ? 1U : 2U;
            packed|=cell<<shift;++scalar;CF_COUNT(++formula_rank_entries_);
        } else {CF_COUNT(if(cell==1U)++hit_good;else ++hit_bad);}
        if(cell==1U)allowed[row/64U]|=std::uint64_t{1}<<(row&63U);
    }
    target_evals_+=rows-scalar;
    CF_COUNT(formula_good_+=hit_good;formula_nogood_+=hit_bad;);
    cf_perf_metric_set("formula_rank_cache_used",1);
    cf_perf_metric_set("formula_rank_hits_good",formula_good_);
    cf_perf_metric_set("formula_rank_hits_nogood",formula_nogood_);
    cf_perf_metric_set("formula_rank_misses",formula_rank_entries_);
    cf_perf_metric_set("formula_rank_entries",formula_rank_entries_);
    cf_perf_metric_set("tight_loop_used",1);
    cf_perf_metric_set("tight_loop_ms",elapsed_ms(started,std::chrono::steady_clock::now()));
    cf_perf_metric_set("tight_loop_slow_arrivals",scalar);
    cf_perf_metric_set("block_loop_used",cf_block_target_loop ? 1 : 0);
    cf_perf_metric_set("block_target_rows",cf_block_target_rows);
    CF_COUNT(cf_perf_metric_set("block_branch_arrivals",rows);cf_perf_metric_set("block_cell_arrivals",hit_good+hit_bad);
        cf_perf_metric_set("block_scalar_arrivals",scalar);cf_perf_metric_set("block_rows_scalar",scalar);
        cf_perf_metric_set("block_rows_cells",hit_good+hit_bad);cf_perf_metric_set("block_rows_filter_only",0));
    return true;
}
#endif

// Cold-only compiler copy. Ordinary policies retain the original V4 compiler.
MEMENTO_ITERATOR_COLD
bool MEMENTO_METHOD(run_grouped_tight_policy)(std::uint32_t rows,std::vector<std::uint64_t> &allowed)
#ifdef MEMENTO_DECLARE_COLD
;
#else
{
    cf_perf_metric_set("block_loop_used",0);
    cf_perf_metric_set("tight_loop_used",0);
    cf_perf_metric_set("formula_rank_cache_used",0);
    if (!cf_tight_loop || !rank_store_mode_ || leaves_.empty() || leaves_.size()>12U) return false;
    // This entry is selected only for a plan with genuine mixed-node groups.
    // Compile the first-arrival hooks BEFORE entering whole-formula reuse.
    // A formula miss asks its compiled leaves, preserving the shared iterator;
    // hits never re-enter the grouped scheduler.
    const auto build_started=std::chrono::steady_clock::now();
    const auto boundaries_before=chain_boundary_build_ms_;
    std::vector<TightBranch> branches;
    branches.reserve(leaves_.size());
    for (std::size_t leaf=0;leaf<leaves_.size();++leaf) {
        TightBranch branch;branch.leaf=leaf;
        auto &boundary=window_requests_[leaf];auto &projection=chain_plans_[leaf];
        if (boundary.enabled && boundary.indexed) {
            branch.boundary=true;branch.global=boundary.global;
            branch.above=boundary.op==POLICY_OP_GT || boundary.op==POLICY_OP_GE;
            branch.key_single_visit=boundary.key_single_visit;
            if (!tight_stream(boundary.time,rows,&branch.time)) return false;
            if (!branch.global && !tight_stream(boundary.context[0],rows,&branch.context)) return false;
            branch.window=&boundary.cells;
            branch.window_view=boundary.cells.read_view<false>();
        } else if (projection.enabled && projection.full) {
            branch.projected=true;
            branch.composed=cf_composed_reuse && kept_leaves_[leaf].enabled;
            branch.key_single_visit=projection.key_single_visit;
            branch.sparse=projection.sparse;
            for (auto &step:projection.required_steps) if (!compile_tight_hop(step)) return false;
            for (auto &step:projection.compound_steps) if (!compile_tight_hop(step)) return false;
            for (auto &slot:projection.slots) {
                TightBranch::Value value;value.slot=&slot;
                if (!tight_stream(slot.direct ? slot.ref : slot.root,rows,&value.input)) return false;
                if (!slot.direct && !tight_stream(slot.ref,column(slot.ref).cix.row_count,&value.endpoint)) return false;
                branch.values.push_back(value);
                if(slot.direct)branch.direct_values.push_back(branch.values.size()-1U);
                else if(slot.cache_slot)branch.indirect_values.push_back(branch.values.size()-1U);
                else branch.uncached_values.push_back(branch.values.size()-1U);
            }
            branch.resolved.resize(projection.slots.size());
            std::size_t stack=1;
            for (const auto &group:projection.groups) stack=std::max(stack,group.size());
            branch.boolean_stack.resize(stack);
            for (auto &guard:projection.guards) {
                TightBranch::ProjectedGuard entry;entry.guard=&guard;
                if (!tight_stream(guard.root,rows,&entry.input)) return false;
                if(guard.key_single_visit)branch.direct_guards.push_back(entry);
                else branch.guards.push_back(entry);
            }
            for (auto key:projection.key_slots) {
                auto &slot=projection.slots[key];TightBranch::ProjectedKey entry;
                if (!tight_stream(slot.direct ? slot.ref : slot.root,rows,&entry.input)) return false;
                entry.slot=slot.direct ? nullptr : &slot;
                entry.null_cell=domain(column(slot.ref).domain).count;
                branch.keys.push_back(entry);
            }
        } else {
            std::map<std::size_t,ColumnRef> refs;
            const auto collect=[&](const NormalizedAtom *atom) {
                if (atom->left.node_id==target_node_) refs.emplace(atom->left.runtime_column,atom->left);
                if (!atom->right_is_const && atom->right.node_id==target_node_)
                    refs.emplace(atom->right.runtime_column,atom->right);
            };
            for (auto atom:leaves_[leaf]->atoms) collect(atom);
            for (const auto &group:leaves_[leaf]->boolean_groups) for (auto atom:group.atoms) collect(atom);
            if (refs.size()>1U && refs.size()<=16U) {
                // An outside unique key makes every complete instance a first visit.
                for (const auto &ref:refs) if (cf_cost_single_visit && column_is_unique(ref.second)) branch.key_single_visit=true;
                branch.packed_ranked=true;
                ChainPlan identity;
                for (const auto &ref:refs) {
                    TightStream stream;if (!tight_stream(ref.second,rows,&stream)) return false;
                    branch.operands.push_back(stream);
                    ChainSlot slot;slot.ref=slot.root=ref.second;slot.direct=true;
                    identity.key_slots.push_back(identity.slots.size());identity.slots.push_back(slot);
                }
                branch.instance_predicate=intern_chain_predicate(leaf,identity);
                if(cf_cost_single_visit) {
                    std::vector<ColumnRef> keys;for(const auto &ref:refs)keys.push_back(ref.second);
                    branch.key_single_visit|=decision_repeat_ratio(planned_leaf_arrivals_[leaf],keys)<=1.0;
                }
                branch.expected_cost=tight_expected_cost(branch,rows);
                choose_lean_loop(branch);branches.push_back(std::move(branch));continue;
            }
            ColumnRef operand;
            if (!single_target_operand(*leaves_[leaf],&operand) ||
                !tight_stream(operand,rows,&branch.context)) return false;
            const auto count=column(operand).cix.rank_count;
            if (count>200000000U) return false;
            branch.ranked=true;branch.null_cell=count;
            branch.key_single_visit=cf_cost_single_visit &&
                (column_is_unique(operand) || decision_repeat_ratio(planned_leaf_arrivals_[leaf],{operand})<=1.0);
            if (!branch.key_single_visit) {
                if (!reserve_dense_cache((std::size_t(count)+4U)/4U)) {
                    branch.sparse=true;branch.rank_cells.select_sparse();
                }
                branch.rank_cells.assign((std::size_t(count)+4U)/4U,0U);
            }
            projection_front_bytes_+=branch.rank_cells.capacity();
            for (auto child:dag_[0].children) {
                if (!(dag_[child].leaves&(std::uint64_t{1}<<leaf))) continue;
                const auto &edge=*dag_[child].edge_by_leaf[leaf];
                if (edge.op!=POLICY_OP_EQ) continue;
                const auto &bound=dag_[child].candidate_is_left_by_leaf[leaf] ? edge.right : edge.left;
                const auto &candidate=dag_[child].candidate_is_left_by_leaf[leaf] ? edge.left : edge.right;
                if (bound.node_id==target_node_ && bound.runtime_column==operand.runtime_column)
                    branch.entering_indexes.push_back(&column(candidate));
            }
        }
        branch.expected_cost=tight_expected_cost(branch,rows);
        choose_lean_loop(branch);
        branches.push_back(std::move(branch));
    }
    // Preserve Boolean short circuiting; summaries are built only for live arrivals.
    // Metadata-only expected work, not a fixed branch-kind priority. Single-
    // visit keys go last; a repeating boundary can precede a general rank walk.
    if(cf_cost_branch_order) {
        // Start in policy order. A local move requires a clear twofold advantage.
        for(std::size_t i=1;i<branches.size();++i) {
            auto j=i;
            while(j && branches[j].expected_cost*2.0<=branches[j-1U].expected_cost) {
                std::swap(branches[j],branches[j-1U]);--j;
            }
        }
    } else std::stable_sort(branches.begin(),branches.end(),[](const TightBranch &a,const TightBranch &b) {
        return (a.boundary ? 2 : a.ranked ? 1 : 0)<(b.boundary ? 2 : b.ranked ? 1 : 0);
    });
    for (std::size_t order=0;order<branches.size();++order) {
        auto &branch=branches[order];
        if(cf_block_target_loop)compile_block_branch(branch);
        if(cf_run_reuse)compile_branch_runs(branch);
        record_compiled_loop(branch,order);
        cf_perf_metric_set(("tight_branch_order_"+std::to_string(order)).c_str(),branch.leaf);
        cf_perf_metric_set(("tight_branch_cost_"+std::to_string(branch.leaf)).c_str(),branch.expected_cost);
        cf_perf_metric_set(("tight_branch_single_visit_"+std::to_string(branch.leaf)).c_str(),branch.key_single_visit ? 1 : 0);
        cf_perf_metric_set(("tight_branch_block_"+std::to_string(branch.leaf)).c_str(),branch.block_batched ? 1 : 0);
        cf_perf_metric_set(("tight_branch_cache_cells_"+std::to_string(branch.leaf)).c_str(),branch.block_planned_cells);
        cf_perf_metric_set(("tight_branch_cache_bytes_"+std::to_string(branch.leaf)).c_str(),branch.block_planned_bytes);
    }
    install_grouped_hooks(branches);
    if(run_grouped_formula_loop(rows,allowed,branches)) {
        // Formula reuse returns before the ordinary compiler's epilogue.
        // Publish its actual shared-walk evidence on this exit as well.
        for(auto &branch:branches) {
            chain_boundary_hits_+=branch.boundary_hits;
            cf_perf_metric_set(("tight_branch_probes_"+std::to_string(branch.leaf)).c_str(),branch.decision_probes);
            cf_perf_metric_set(("tight_branch_writes_"+std::to_string(branch.leaf)).c_str(),branch.decision_writes);
        }
        CF_COUNT(
            cf_perf_metric_set("grouped_request_calls",grouped_request_calls_);
            cf_perf_metric_set("grouped_shared_postings",grouped_shared_postings_);
            cf_perf_metric_set("grouped_shared_rows",grouped_shared_rows_);
            cf_perf_metric_set("grouped_boundary_fills",grouped_boundary_fills_);
        );
        return true;
    }
    tight_loop_build_ms_=elapsed_ms(build_started,std::chrono::steady_clock::now())-
                         (chain_boundary_build_ms_-boundaries_before);
    const auto started=std::chrono::steady_clock::now();
    std::uint64_t slow=0;
    const bool lean=cf_cost_single_visit || cf_cost_branch_order || cf_cost_present_caps ||
        cf_cost_dense_budget || cf_cost_hop_elision || cf_cost_target_fraction || cf_cost_group_maps;
    if(lean) {
        // If every branch chooses scalar, keep the lean outer loop as well.
        const bool batched=cf_block_target_loop && std::any_of(branches.begin(),branches.end(),
            [](const TightBranch &branch){return branch.block_batched;});
        if(batched)run_block_words(branches,rows,allowed,&slow);
        else {
            cf_perf_metric_set("block_loop_used",0);
            run_lean_words(branches,rows,allowed,&slow);
        }
    } else {
    for (std::size_t word=0;word<allowed.size();++word) {
        if ((word&63U)==0U) CHECK_FOR_INTERRUPTS();
        std::uint64_t result=0;
        const auto begin=static_cast<std::uint32_t>(word*64U),end=std::min(rows,begin+64U);
        for (auto row=begin;row<end;++row) {
            target_walk_started_=true;
            const auto bit=std::uint64_t{1}<<(row-begin);
            ++target_evals_;
            std::uint64_t decided=0,truth=0,ternary=0;
            int verdict=-1;
            for (auto &branch:branches) {
                const auto leafbit=std::uint64_t{1}<<branch.leaf;
                const bool good=tight_branch_truth(branch,row,&slow);
                decided|=leafbit;if (good) truth|=leafbit;
                if (flat_mode_!=FlatFormulaMode::none) {
                    const auto required=flat_positive_|flat_negative_;
                    if (flat_constant_>=0) verdict=flat_constant_;
                    else if (flat_mode_==FlatFormulaMode::conjunction)
                        verdict=((decided&flat_positive_&~truth) || (decided&flat_negative_&truth)) ? 0 :
                            ((decided&required)==required ? 1 : -1);
                    else verdict=((decided&flat_positive_&truth) || (decided&flat_negative_&~truth)) ? 1 :
                            ((decided&required)==required ? 0 : -1);
                } else {
                    ternary+=formula_ternary_powers_[branch.leaf]*(good ? 2U : 1U);
                    verdict=formula_truth_table_[ternary];
                }
                if (verdict>=0) break;
            }
            if (verdict<0) fail("compiled formula remained unresolved");
            if (verdict==1) result|=bit;
        }
        allowed[word]=result;
    }
    }
    for (auto &branch:branches) {
        CF_COUNT(
            cf_perf_metric_set(("tight_branch_run_sampled_"+std::to_string(branch.leaf)).c_str(),branch.runs.sampled);
            cf_perf_metric_set(("tight_branch_run_repeats_"+std::to_string(branch.leaf)).c_str(),branch.runs.repeats);
            cf_perf_metric_set(("tight_branch_run_disabled_"+std::to_string(branch.leaf)).c_str(),branch.runs.disabled);
        );
        cf_perf_metric_set(("tight_branch_probes_"+std::to_string(branch.leaf)).c_str(),branch.decision_probes);
        cf_perf_metric_set(("tight_branch_writes_"+std::to_string(branch.leaf)).c_str(),branch.decision_writes);
        chain_boundary_hits_+=branch.boundary_hits;
        if (branch.projected && (branch.good || branch.nogood)) {
            auto &plan=chain_plans_[branch.leaf];
            const auto ordinal=plan.predicate & ((1U<<RankPredicateInstance::arity_shift)-1U);
            auto &state=rank_store_.predicates[ordinal];
            const auto hits=branch.good+branch.nogood;
            if (state.enabled) {
                rank_store_.probes+=hits;state.total_probes+=hits;state.total_hits+=hits;
                state.saved_reads+=hits;state.window_probes+=hits;state.window_hits+=hits;
                if (state.window_probes>=1024U) state.window_probes=state.window_hits=0;
            }
            rank_store_.good_hits+=branch.good;rank_store_.no_good_hits+=branch.nogood;
            CF_COUNT(projection_hits_good_+=branch.good);CF_COUNT(projection_hits_nogood_+=branch.nogood);
        }
    }
    const auto duration=elapsed_ms(started,std::chrono::steady_clock::now());
    cf_perf_metric_set("tight_loop_used",1);
    cf_perf_metric_set("global_window_complete_blocks",global_window_complete_blocks_);
    cf_perf_metric_set("tight_loop_build_ms",tight_loop_build_ms_);
    cf_perf_metric_set("tight_loop_ms",duration);
    cf_perf_metric_set("tight_loop_ns_per_row",target_evals_ ? duration*1000000.0/target_evals_ : 0);
    cf_perf_metric_set("tight_loop_slow_arrivals",slow);
    cf_perf_metric_set("tight_loop_inline_misses",tight_inline_misses_);
    cf_perf_metric_set("tight_loop_tuple_hits",tight_tuple_hits_);
    cf_perf_metric_set("tight_loop_tuple_misses",tight_tuple_misses_);
    cf_perf_metric_set("tight_loop_null_slow_arrivals",tight_null_slow_);
    cf_perf_metric_set("tight_loop_null_hits",tight_null_hits_);
    cf_perf_metric_set("branch_rank_entries",branch_rank_entries_);
    cf_perf_metric_set("branch_rank_hits_good",branch_good_);
    cf_perf_metric_set("branch_rank_hits_nogood",branch_nogood_);
    cf_perf_metric_set("branch_rank_empty_stops",branch_empty_);
    cf_perf_metric_set("tight_single_visit_arrivals",tight_single_visit_arrivals_);
    cf_perf_metric_set("direct_residual_arrivals",direct_residual_arrivals_);
    cf_perf_metric_set("projected_hash_arrivals",projected_hash_arrivals_);
    cf_perf_metric_set("projected_hash_misses",projected_hash_misses_);
    CF_COUNT(
        cf_perf_metric_set("grouped_request_calls",grouped_request_calls_);
        cf_perf_metric_set("grouped_shared_postings",grouped_shared_postings_);
        cf_perf_metric_set("grouped_shared_rows",grouped_shared_rows_);
        cf_perf_metric_set("grouped_boundary_fills",grouped_boundary_fills_);
    );
    return true;
}
#endif

