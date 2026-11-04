// A compiled rank-stream recipe. No row decisions or target-row key sets.
struct TightStream {
    const std::uint32_t *rows=nullptr, *logical=nullptr, *values=nullptr;
    std::uint32_t local(std::uint32_t row) const {
        // The strict bundle already uses universe ranks; no remap is possible.
        return rows[row];
    }
    std::uint32_t value(std::uint32_t row) const {
        const auto rank=local(row);
        return rank==kNullRank || !values ? rank : values[rank];
    }
};
struct TightBranch {
    struct ProjectedKey { TightStream input; ChainSlot *slot=nullptr; std::uint32_t null_cell=0; };
    struct ProjectedGuard { TightStream input; ChainPlan::Guard *guard=nullptr; };
    bool boundary=false, above=false, ranked=false, projected=false;
    bool composed=false;
    bool composed_policy=false;
    std::size_t composed_carry_cause=SIZE_MAX;
    bool key_single_visit=false;
    double expected_cost=0;
    std::size_t leaf=0;
    TightStream time, context;
    bool global=false;
    composed_windows::Cells *window=nullptr;
    composed_windows::Cells::ReadView<false> window_view;
    std::uint64_t good=0,nogood=0,boundary_hits=0;
    std::uint64_t decision_probes=0,decision_writes=0;
    ReachedCells<std::uint8_t> rank_cells;
    std::uint32_t null_cell=0;
    std::uint8_t null_time=0;
    std::vector<const ColumnIndex *> entering_indexes;
    std::vector<ProjectedKey> keys;
    std::vector<ProjectedGuard> guards;
    std::vector<ProjectedGuard> direct_guards;
    struct Value { TightStream input, endpoint; ChainSlot *slot=nullptr; };
    std::vector<Value> values;
    std::vector<std::size_t> direct_values,indirect_values,uncached_values;
    std::vector<std::uint32_t> resolved;
    std::vector<std::uint8_t> boolean_stack;
    bool packed_ranked=false;
    std::uint32_t instance_predicate=0;
    std::vector<TightStream> operands;
    PackedMemoMap packed_cells;
    std::unordered_map<FusedMemoKey,FusedMemoEntry,FusedMemoKeyHash> wide_cells;
    using Loop=std::uint64_t(FusedWalkRuntime::*)(TightBranch &,std::uint32_t,std::uint64_t,std::uint64_t *);
    Loop loop=nullptr;
    Loop row_loop=nullptr;
    std::vector<const std::uint32_t*> run_columns;
    full_reuse::RunBlock runs;
    std::uint32_t run_rows=0;
    TightStream kept_input;
    struct KeptValue {std::size_t slot=0,field=0;std::uint32_t domain=0;const void *ranks=nullptr;};
    struct KeptGroup {
        KeptUse *use=nullptr;TightStream input;
        const std::uint8_t *states=nullptr;std::uint32_t null_key=0;
        std::vector<KeptValue> values;
        std::vector<KeptValue> u8,u16,u32;
    };
    std::vector<KeptGroup> kept_groups;
    bool kept_initialized=false;
    bool sparse=false;
    struct BlockAtom {
        const std::uint32_t *left=nullptr,*right=nullptr;
        int op=0;std::uint32_t lower=0,upper=0;
    };
    std::vector<BlockAtom> block_atoms;
    std::vector<std::size_t> block_conjuncts;
    std::vector<std::vector<std::pair<int,std::size_t>>> block_groups;
    std::vector<std::uint64_t> block_atom_masks,block_stack;
    std::vector<std::vector<std::uint32_t>> block_resolved;
    using BlockLoop=void(FusedWalkRuntime::*)(TightBranch &,std::uint32_t,std::uint32_t,
        const std::uint64_t *,std::uint64_t *,std::uint64_t *,std::uint64_t *,std::uint64_t *);
    BlockLoop block_loop=nullptr;
    BlockLoop base_block_loop=nullptr;
    bool block_batched=false,block_target_only=false;
    std::size_t block_planned_cells=0,block_planned_bytes=0;
};
double tight_loop_build_ms_=0;
std::uint64_t formula_rank_entries_=0,formula_good_=0,formula_nogood_=0;
std::uint64_t branch_rank_entries_=0,branch_good_=0,branch_nogood_=0,branch_empty_=0;
std::uint64_t tight_null_slow_=0,tight_null_hits_=0;
std::uint64_t tight_inline_misses_=0,tight_tuple_hits_=0,tight_tuple_misses_=0;
std::uint64_t tight_single_visit_arrivals_=0;
std::uint64_t global_window_complete_blocks_=0;

// Equality of this one target value must determine every outside operand.
bool single_target_operand(const FormulaNode &leaf,ColumnRef *operand) {
    std::map<std::size_t,ColumnRef> refs;
    const auto add=[&](const NormalizedAtom *atom) {
        if (atom->left.node_id==target_node_) refs.emplace(atom->left.runtime_column,atom->left);
        if (!atom->right_is_const && atom->right.node_id==target_node_)
            refs.emplace(atom->right.runtime_column,atom->right);
    };
    for (auto atom:leaf.atoms) add(atom);
    for (const auto &group:leaf.boolean_groups) for (auto atom:group.atoms) add(atom);
    if (refs.size()!=1U) return false;
    *operand=refs.begin()->second;return true;
}

bool run_formula_rank_loop(std::uint32_t rows,std::vector<std::uint64_t> &allowed) {
    if (!cf_formula_rank_cache) return false;
    // Complete projections already decide at endpoint values, never at a source FK.
    bool all_projected=true;
    for (const auto &plan:chain_plans_) all_projected &= plan.enabled && plan.full;
    if (all_projected) return false;
    ColumnRef operand;bool first=true;
    for (auto leaf:leaves_) {
        ColumnRef ref;
        if (!single_target_operand(*leaf,&ref)) return false;
        if (!first && ref.runtime_column!=operand.runtime_column) return false;
        operand=ref;first=false;
    }
    TightStream stream;
    if (first || column_is_unique(operand) || !tight_stream(operand,rows,&stream)) return false;
    const auto count=column(operand).cix.rank_count;
    if (count>200000000U) return false;
    if (!reserve_dense_cache((std::size_t(count)+4U)/4U)) return false;
    const auto build_started=std::chrono::steady_clock::now();
    // One extra cell represents a NULL operand, whose formula instance is fixed too.
    std::vector<std::uint8_t> cells((std::size_t(count)+4U)/4U,0U);
    projection_front_bytes_+=cells.capacity();
    tight_loop_build_ms_=elapsed_ms(build_started,std::chrono::steady_clock::now());
    const auto started=std::chrono::steady_clock::now();
    if(cf_block_target_loop)run_block_formula(rows,allowed,cells,stream,count);
    else for (std::size_t word=0;word<allowed.size();++word) {
        if ((word&63U)==0U) CHECK_FOR_INTERRUPTS();
        std::uint64_t result=0;
        const auto begin=static_cast<std::uint32_t>(word*64U),end=std::min(rows,begin+64U);
        for (auto row=begin;row<end;++row) {
            target_walk_started_=true;
            const auto bit=std::uint64_t{1}<<(row-begin);
            bindings_[target_node_]=row;
            // Recheck own predicates per row; all their operands are this same value.
            (void)evaluate_filters(0,leaves_.size()==64U ? UINT64_MAX : ((std::uint64_t{1}<<leaves_.size())-1U));
            const auto rank=stream.local(row),key=rank==kNullRank ? count : rank;
            const auto shift=(key&3U)*2U;
            auto &packed=cells[key/4U];
            unsigned cell=(packed>>shift)&3U;
            if (!cell) {
                const bool good=evaluate_target(row);
                cell=good ? 1U : 2U;packed|=cell<<shift;CF_COUNT(++formula_rank_entries_);
            } else {
                ++target_evals_;
                if (cell==1U) CF_COUNT(++formula_good_);else CF_COUNT(++formula_nogood_);
            }
            if (cell==1U) result|=bit;
        }
        allowed[word]=result;
    }
    const auto duration=elapsed_ms(started,std::chrono::steady_clock::now());
    cf_perf_metric_set("formula_rank_cache_used",1);
    cf_perf_metric_set("formula_rank_hits_good",formula_good_);
    cf_perf_metric_set("formula_rank_hits_nogood",formula_nogood_);
    cf_perf_metric_set("formula_rank_misses",formula_rank_entries_);
    cf_perf_metric_set("formula_rank_entries",formula_rank_entries_);
    cf_perf_metric_set("tight_loop_used",1);
    cf_perf_metric_set("global_window_complete_blocks",global_window_complete_blocks_);
    cf_perf_metric_set("tight_loop_build_ms",tight_loop_build_ms_);
    cf_perf_metric_set("tight_loop_ms",duration);
    cf_perf_metric_set("tight_loop_ns_per_row",target_evals_ ? duration*1000000.0/target_evals_ : 0);
    cf_perf_metric_set("tight_loop_slow_arrivals",formula_rank_entries_);
    return true;
}

bool tight_ranked_truth(TightBranch &branch,std::uint32_t row,std::uint64_t *slow) {
    const auto rank=branch.context.local(row),key=rank==kNullRank ? branch.null_cell : rank;
    const auto shift=(key&3U)*2U;
    auto *packed=branch.key_single_visit ? nullptr : &branch.rank_cells[key/4U];
    if (packed) CF_COUNT(++branch.decision_probes);
    unsigned cell=packed ? (*packed>>shift)&3U : 0U;
    if (cell) {
        if (cell==1U) CF_COUNT(++branch_good_);else CF_COUNT(++branch_nogood_);
        return cell==1U;
    }
    ++*slow;
    bool good=true;
    // Empty mandatory equality postings decide the branch without walk dispatch.
    for (auto index:branch.entering_indexes)
        if (rank==kNullRank || index->cix.begin(rank)==index->cix.end(rank)) {
            good=false;CF_COUNT(++branch_empty_);break;
        }
    if (good) {
        const auto old_settled=settled_,old_truth=truth_,old_ternary=formula_ternary_state_;
        const auto old_aborted=aborted_;
        settled_=truth_=formula_ternary_state_=0;aborted_=false;
        bindings_[target_node_]=row;
        const auto bit=std::uint64_t{1}<<branch.leaf;
        good=(evaluate_filters(0,bit)&bit)!=0U;
        bool decided=false;
        if (good) decided=window_truth(branch.leaf,row,&good) || chain_projected_truth(branch.leaf,row,&good);
        if (good && !decided)
            for (auto child:dag_[0].children)
                if ((dag_[child].leaves&bit) && !(solve_node(child,bit,0U)&bit)) { good=false;break; }
        if (aborted_) fail("interrupted branch cannot become a rank decision");
        settled_=old_settled;truth_=old_truth;formula_ternary_state_=old_ternary;aborted_=old_aborted;
    }
    if (packed) {cell=good ? 1U : 2U;*packed|=cell<<shift;CF_COUNT(++branch_rank_entries_);CF_COUNT(++branch.decision_writes);}
    return good;
}

// Multiple outside operands identify a complete instance, including each NULL.
bool tight_packed_truth(TightBranch &branch,std::uint32_t row,std::uint64_t *slow) {
    FusedMemoKey key{};key.width=branch.operands.size();
    for (std::size_t i=0;i<key.width;++i) key.ranks[i]=branch.operands[i].local(row);
    const auto packed=std::uint64_t{key.ranks[0]} | (std::uint64_t{key.ranks[1]}<<32U);
    const bool cache=!branch.key_single_visit && rank_store_.enabled(branch.instance_predicate);
    if (cache) CF_COUNT(++branch.decision_probes);
    if (cache && key.width==2U) {
        if (auto cell=branch.packed_cells.find(packed)) {
            rank_store_.observe_range(branch.instance_predicate,true,cell->touch_cost);
            if (cell->truth) CF_COUNT(++branch_good_);else CF_COUNT(++branch_nogood_);
            return cell->truth;
        }
    } else if (cache) {
        const auto found=branch.wide_cells.find(key);
        if (found!=branch.wide_cells.end()) {
            rank_store_.observe_range(branch.instance_predicate,true,found->second.touch_cost);
            if (found->second.truth) CF_COUNT(++branch_good_);else CF_COUNT(++branch_nogood_);
            return found->second.truth;
        }
    }
    if (cache) rank_store_.observe_range(branch.instance_predicate,false,0U);
    ++*slow;
    const auto touches=partner_touches_+online_build_tuples_;
    const auto old_settled=settled_,old_truth=truth_,old_ternary=formula_ternary_state_;
    const auto old_aborted=aborted_;
    settled_=truth_=formula_ternary_state_=0;aborted_=false;
    bindings_[target_node_]=row;
    const auto bit=std::uint64_t{1}<<branch.leaf;
    bool good=(evaluate_filters(0,bit)&bit)!=0U,decided=false;
    if (good) decided=window_truth(branch.leaf,row,&good) || chain_projected_truth(branch.leaf,row,&good);
    if (good && !decided) for (auto child:dag_[0].children)
        if ((dag_[child].leaves&bit) && !(solve_node(child,bit,0U)&bit)) {good=false;break;}
    if (aborted_) fail("interrupted composite instance cannot become a decision");
    settled_=old_settled;truth_=old_truth;formula_ternary_state_=old_ternary;aborted_=old_aborted;
    if (branch.key_single_visit || !rank_store_.enabled(branch.instance_predicate)) return good;
    const auto reads=static_cast<std::uint32_t>(std::min<std::uint64_t>(UINT32_MAX,partner_touches_+online_build_tuples_-touches));
    if (key.width==2U) {
        const auto before=branch.packed_cells.bytes();
        branch.packed_cells.insert(packed,FusedMemoEntry{good,reads});
        projection_front_bytes_+=branch.packed_cells.bytes()-before;
    } else {
        branch.wide_cells.emplace(key,FusedMemoEntry{good,reads});
        projection_front_bytes_+=sizeof(FusedMemoKey)+sizeof(FusedMemoEntry)+3U*sizeof(void*);
    }
    CF_COUNT(++branch_rank_entries_);CF_COUNT(++branch.decision_writes);return good;
}

// Compile only pointers and headers. No posting or witness row is read here.
bool compile_tight_hop(const std::shared_ptr<ChainStep> &step) {
    if (step->source_forward && step->root_forward && step->destination &&
        step->tuple_forward.size()==step->tuple_sources.size()) return true;
    if (step->parent && !compile_tight_hop(step->parent)) return false;
    step->source_forward=column(step->source).forward_ranks;
    step->root_forward=column(step->root).forward_ranks;
    step->destination=&column(step->unique);
    if (!step->source_forward || !step->root_forward) return false;
    step->tuple_forward.clear();
    for (const auto &source:step->tuple_sources) {
        const auto data=column(source).forward_ranks;
        if (!data) return false;
        step->tuple_forward.push_back(data);
    }
    if(step->cache_hop)
        step->resolve=step->reached.sparse() ? &FusedWalkRuntime::lean_hop<true,true> : &FusedWalkRuntime::lean_hop<false,true>;
    else step->resolve=&FusedWalkRuntime::lean_hop<false,false>;
    return true;
}

// A missed hop stays inside the compiled loop and reads mapped arrays directly.
std::uint32_t tight_hop(ChainStep *step,std::uint32_t target,std::uint32_t root_rank) {
    if (step->current_target==target) return step->current_row;
    const auto parent=step->parent ? tight_hop(step->parent.get(),target,root_rank) : target;
    if (parent==kNullRank) {
        step->current_target=target;step->current_row=kNullRank;return kNullRank;
    }
    std::uint32_t result=kNullRank;
    const auto entering=step->parent ? step->source_forward[parent] : root_rank;
    if (entering!=kNullRank) {
        if (step->reached.empty()) initialize_chain_cells(step->reached,step->cardinality);
        if (entering>=step->reached.size()) fail("compiled hop rank outside universe");
        result=step->reached[entering];
        if (result==kChainUnknown) {
            CF_COUNT(++tight_inline_misses_);
            const auto &index=step->destination->cix;
            const auto begin=index.begin(entering),end=index.end(entering);
            if (end-begin>1U) fail("compiled hop encountered nonunique rank");
            result=end==begin ? kNullRank : u32le(index.child_rows+begin*4ULL);
            if (end>begin) ++partner_touches_;
            step->reached[entering]=result;
        }
    }
    step->current_target=target;step->current_row=result;
    return result;
}

std::uint32_t tight_value(TightBranch::Value &value,std::uint32_t row) {
    auto *slot=value.slot;
    const auto source=value.input.local(row);
    if (slot->direct) return source;
    if (slot->step->compound) {
        const auto endpoint=tight_hop(slot->step.get(),row,source);
        return endpoint==kNullRank ? kNullRank : value.endpoint.local(endpoint);
    }
    if (source==kNullRank) return kNullRank;
    if (slot->reached.empty()) initialize_chain_cells(slot->reached,slot->cardinality);
    auto &cached=slot->reached[source];
    if (cached==kChainUnknown) {
        const auto endpoint=tight_hop(slot->step.get(),row,source);
        cached=endpoint==kNullRank ? kNullRank : value.endpoint.local(endpoint);
    }
    return cached;
}

bool tight_test(const ChainAtom &test,const TightBranch &branch) {
    const auto value=branch.resolved[test.left];
    if (value==kNullRank) return false;
    const auto &atom=*test.atom;
    if (!atom.right_is_const) {
        const auto right=branch.resolved[test.right];
        return right!=kNullRank && compare_rank(value,atom.op,right);
    }
    switch (atom.op) {
        case POLICY_OP_EQ:return value>=atom.constant_lower && value<atom.constant_upper;
        case POLICY_OP_NE:return value<atom.constant_lower || value>=atom.constant_upper;
        case POLICY_OP_LT:return value<atom.constant_lower;
        case POLICY_OP_LE:return value<atom.constant_upper;
        case POLICY_OP_GT:return value>=atom.constant_upper;
        case POLICY_OP_GE:return value>=atom.constant_lower;
        default:fail("invalid compiled residual operator");
    }
}

bool tight_tests(TightBranch &branch,const ChainPlan &plan) {
    for (const auto &atom:plan.atoms) if (!tight_test(atom,branch)) return false;
    for (const auto &group:plan.groups) {
        std::size_t top=0;
        for (const auto &token:group) {
            if (token.first==static_cast<int>(LocalBooleanTokenKind::atom))
                branch.boolean_stack[top++]=tight_test(token.second,branch);
            else {
                const bool right=branch.boolean_stack[--top],left=branch.boolean_stack[--top];
                branch.boolean_stack[top++]=token.first==static_cast<int>(LocalBooleanTokenKind::conjunction) ? left&&right : left||right;
            }
        }
        if (top!=1U || !branch.boolean_stack[0]) return false;
    }
    return true;
}

bool tight_inline_truth(TightBranch &branch,std::uint32_t row) {
    auto &plan=chain_plans_[branch.leaf];
    for (auto &entry:branch.guards) {
        auto &guard=*entry.guard;
        const auto rank=entry.input.local(row),key=rank==kNullRank ? guard.cardinality : rank;
        if (guard.key_single_visit) {
            if (rank==kNullRank) return false;
            for (auto &end:guard.ends)
                if (tight_hop(end.get(),row,rank)==kNullRank) return false;
            continue;
        }
        if (guard.state.empty()) {
            guard.state.assign(std::size_t(guard.cardinality)+1U,0U);
            projection_front_bytes_+=guard.state.capacity();
        }
        auto &cell=guard.state[key];
        if (!cell) {
            bool good=rank!=kNullRank;
            if (good) for (auto &end:guard.ends)
                if (tight_hop(end.get(),row,rank)==kNullRank) {good=false;break;}
            cell=good ? 1U : 2U;
        }
        if (cell==2U) return false;
    }
    for (auto &step:plan.compound_steps)
        if (tight_hop(step.get(),row,step->root_forward[row])==kNullRank) return false;
    for (std::size_t i=0;i<branch.values.size();++i) branch.resolved[i]=tight_value(branch.values[i],row);
    if (plan.direct_residual) {CF_COUNT(++direct_residual_arrivals_);return tight_tests(branch,plan);}
    if (branch.key_single_visit) {
        CF_COUNT(++tight_inline_misses_);
        return tight_tests(branch,plan);
    }
    if (plan.dense_front.empty()) CF_COUNT(++projected_hash_arrivals_);
    std::size_t dense=0;std::uint32_t primary=0;
    RankPredicateInstance instance;
    if(!RankDecisionStore::Key(plan.predicate,plan.key_slots.empty()?0:plan.key_slots.size()-1,[&](unsigned i,unsigned &value){
        value=branch.resolved[plan.key_slots[i+1]];return true;},instance))fail("projected Rest exceeds parameter capacity");
    for (std::size_t i=0;i<plan.key_slots.size();++i) {
        const auto value=branch.resolved[plan.key_slots[i]];
        if (!i) primary=value;
        if (!plan.dense_front.empty()) dense+=plan.dense_strides[i]*(value==kNullRank ? branch.keys[i].null_cell : value);
    }
    const bool enabled=rank_store_.enabled(instance.id);
    if (enabled) CF_COUNT(++branch.decision_probes);
    if (enabled && !plan.dense_front.empty()) {
        const auto cell=(plan.dense_front[dense/4U]>>((dense&3U)*2U))&3U;
        if (cell) {if (cell==1U) CF_COUNT(++branch.good);else CF_COUNT(++branch.nogood);return cell==1U;}
    }
    const bool single_null=plan.key_slots.size()==1U && primary==kNullRank;
    if (enabled && single_null && plan.null_decision) {
        if (plan.null_decision==1U) CF_COUNT(++branch.good);else CF_COUNT(++branch.nogood);
        return plan.null_decision==1U;
    }
    const bool cache=enabled && (primary!=kNullRank || plan.key_slots.size()>1U);
    bool truth=false;
    std::chrono::steady_clock::time_point started;
    if (cf_engine_profile) started=std::chrono::steady_clock::now();
    const bool hit=cache && rank_store_.lookup(primary,instance,&truth);
    if (cf_engine_profile) decision_lookup_ms_+=elapsed_ms(started,std::chrono::steady_clock::now());
    if (hit) {
        if (truth) CF_COUNT(++projection_hits_good_);else CF_COUNT(++projection_hits_nogood_);return truth;
    }
    CF_COUNT(++tight_inline_misses_);
    if (plan.dense_front.empty()) CF_COUNT(++projected_hash_misses_);
    truth=tight_tests(branch,plan);
    if (cache && rank_store_.enabled(instance.id) && !rank_store_.insert(primary,instance,truth)) fail("compiled endpoint decision flipped");
    if (enabled && rank_store_.enabled(instance.id)) {
        CF_COUNT(++branch.decision_writes);
        const unsigned cell=truth ? 1U : 2U;
        if (single_null) {
            if (plan.dense_front.empty() && !plan.null_decision) CF_COUNT(++projection_null_entries_);
            plan.null_decision=cell;
        }
        if (!plan.dense_front.empty() && primary==kNullRank) CF_COUNT(++projection_null_entries_);
        if (!plan.dense_front.empty()) plan.dense_front[dense/4U] |= cell<<((dense&3U)*2U);
    }
    return truth;
}

bool tight_stream(const ColumnRef &ref,std::uint32_t rows,TightStream *out) {
    auto &idx=column(ref);
    // The existing forward artifact is optional. Keep the normal path if absent.
    if (!idx.forward_ranks || idx.forward_rows<rows) return false;
    out->rows=idx.forward_ranks;
    out->logical=nullptr;
    return true;
}

bool tight_branch_truth(TightBranch &branch,std::uint32_t row,std::uint64_t *slow) {
    bindings_[target_node_]=row;
    const auto leafbit=std::uint64_t{1}<<branch.leaf;
    if (!(evaluate_filters(0,leafbit)&leafbit)) return false;
    if (branch.key_single_visit) CF_COUNT(++tight_single_visit_arrivals_);
    if (branch.packed_ranked) return tight_packed_truth(branch,row,slow);
    if (branch.ranked) return tight_ranked_truth(branch,row,slow);
    if (branch.boundary) {
        const auto time=branch.time.local(row);
        if(time==kNullRank){CF_COUNT(++tight_null_hits_);return false;}
        CF_COUNT(++branch.decision_probes);
        if(!branch.key_single_visit) {
            const auto context=branch.global ? 0U : branch.context.local(row);
            const auto cell=context==kNullRank ? branch.window->count()-1U : std::size_t(context);
            const auto answer=!branch.window_view.allocated() ? -1 : branch.above ?
                branch.window_view.probe_window<composed_windows::Shape::lower>(cell,time) :
                branch.window_view.probe_window<composed_windows::Shape::upper>(cell,time);
            if(answer>=0){CF_COUNT(++branch.boundary_hits);return answer==1;}
        }
        ++*slow;bool truth=false;
        if(!window_truth(branch.leaf,row,&truth))fail("window request unresolved");
        branch.window_view=branch.window->read_view<false>();
        CF_COUNT(++branch.decision_writes);return truth;
    }
    return tight_inline_truth(branch,row);
}

// Expected array/posting work per arrival from index headers only. A miss pays
// the branch's traversal work; a hit reads its decision/summary. No data scan,
// sampling or policy evaluation is allowed while estimating these costs.
double tight_expected_cost(const TightBranch &branch,std::uint32_t rows) {
    double decisions=1.0;
    const auto &leaf=*leaves_[branch.leaf];
    double miss_work=leaf.atoms.size();
    for (const auto &group:leaf.boolean_groups) miss_work+=group.postfix.size();
    for (std::size_t node=1;node<dag_.size();++node) {
        if (!(dag_[node].leaves&(std::uint64_t{1}<<branch.leaf))) continue;
        const auto &edge=*dag_[node].edge_by_leaf[branch.leaf];
        const auto &candidate=dag_[node].candidate_is_left_by_leaf[branch.leaf] ? edge.left : edge.right;
        const auto &index=column(candidate).cix;
        miss_work+=double(index.row_count)/std::max(1U,index.present_count);
    }
    if (branch.boundary) {
        const auto &plan=window_requests_[branch.leaf];
        if (!plan.global) for (const auto &ref:plan.context)
            decisions*=std::max(1U,column(ref).cix.present_count);
    } else if (branch.projected) {
        const auto &plan=chain_plans_[branch.leaf];
        for (auto key:plan.key_slots)
            decisions*=std::max(1U,column(plan.slots[key].ref).cix.present_count);
        // Projection reads still happen on hits; residual-only branches have
        // no decision probe and pay their small integer tests each time.
        if (plan.direct_residual) return double(branch.values.size()+plan.atoms.size());
    } else if (branch.packed_ranked) {
        std::map<std::size_t,ColumnRef> operands;
        const auto add=[&](const NormalizedAtom *atom) {
            if (atom->left.node_id==target_node_) operands.emplace(atom->left.runtime_column,atom->left);
            if (!atom->right_is_const && atom->right.node_id==target_node_)
                operands.emplace(atom->right.runtime_column,atom->right);
        };
        for (auto atom:leaf.atoms) add(atom);
        for (const auto &group:leaf.boolean_groups) for (auto atom:group.atoms) add(atom);
        for (const auto &ref:operands) decisions*=std::max(1U,column(ref.second).cix.present_count);
    } else {
        ColumnRef ref;
        if (single_target_operand(leaf,&ref)) decisions=column(ref).cix.present_count;
    }
    const auto arrivals=planned_leaf_arrivals_.empty() ? double(rows) : planned_leaf_arrivals_[branch.leaf];
    const auto miss_fraction=branch.key_single_visit ? 1.0 :
        std::min(1.0,decisions/std::max(1.0,arrivals));
    const auto hit_work=double(1U+branch.values.size()+branch.guards.size()+branch.operands.size());
    double projection_misses=0;
    if(branch.projected)for(const auto &guard:chain_plans_[branch.leaf].guards) {
        std::size_t hops=0;
        for(auto end:guard.ends)for(auto step=end;step;step=step->parent)++hops;
        // First source arrival resolves the entire path, even with few endpoints.
        // Five primitive operations: two offsets, row id, forward rank, dispatch.
        projection_misses+=std::min(1.0,double(column(guard.root).cix.present_count)/std::max(1.0,arrivals))*hops*5.0;
    }
    const auto fraction=rows ? std::min(1.0,arrivals/double(rows)) : 0.0;
    const auto own=double(dag_[0].filters_by_leaf[branch.leaf].size());
    return own+fraction*(hit_work+projection_misses+miss_fraction*miss_work);
}

#include "lean_branch_loops.inc"
#include "block_target_loop.inc"
#include "composed_executor.inc"

bool run_tight_policy(std::uint32_t rows,std::vector<std::uint64_t> &allowed) {
    if(composed_bound_program_)return run_composed_tight_policy(rows,allowed);
    cf_perf_metric_set("block_loop_used",0);
    cf_perf_metric_set("tight_loop_used",0);
    cf_perf_metric_set("formula_rank_cache_used",0);
    if (!cf_tight_loop || !rank_store_mode_ || leaves_.empty() || leaves_.size()>12U) return false;
    if (run_formula_rank_loop(rows,allowed)) return true;
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
