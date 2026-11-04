// Kept paths are query-local, filled only when their root rank arrives. A root
// array is shared by all branches entering through the same target column.
struct KeptRoot {
    ColumnRef root;
    std::map<std::string,std::size_t> fields;
    std::vector<std::uint32_t> domains;
    full_reuse::KeptRanks ranks;
    std::uint64_t probes=0,misses=0;
    std::uint32_t current_row=kNullRank;
    std::uint32_t missed_row=kNullRank;
    full_reuse::KeptRanks::Cell current_cell;
    std::vector<std::pair<const ChainStep *,std::uint32_t>> resolved;
    std::size_t field(const std::string &name,std::uint32_t domain=0) {
        auto inserted=fields.emplace(name,fields.size());
        if(inserted.second)domains.push_back(domain);
        return inserted.first->second;
    }
};
struct KeptUse {
    KeptRoot *root=nullptr;
    std::size_t valid=SIZE_MAX,decision=SIZE_MAX;
    std::vector<std::shared_ptr<ChainStep>> ends;
    std::vector<std::pair<std::size_t,std::size_t>> slots; // plan slot -> record field
};
struct KeptLeaf {
    bool enabled=false,single_root=false;
    std::vector<KeptUse> uses;
    std::vector<std::uint32_t> scratch;
};
std::map<std::size_t,KeptRoot> kept_roots_;
std::vector<KeptLeaf> kept_leaves_;
std::vector<const std::uint32_t *> run_columns_;
std::uint64_t run_count_=0,run_reused_rows_=0,kept_decision_hits_=0,kept_decisions_=0;
std::uint64_t run_rows_saved_=0;
std::uint64_t physical_path_probes_=0,kept_miss_path_probes_=0,uncovered_path_probes_=0;
std::uint64_t kept_hit_path_probes_=0,kept_hit_checked_rows_=0,kept_fill_events_=0;
unsigned kept_build_depth_=0;
void note_path_probe() {
    CF_COUNT(++physical_path_probes_;
        if(kept_build_depth_)++kept_miss_path_probes_;else ++uncovered_path_probes_);
}

// The target's guards have already passed before this quantifier is entered.
// They do not belong to its Rest, even if the projection compiler assigned
// them direct slots. Mixed target/local comparisons are not closed at a rank.
bool kept_rest_closed(const ChainPlan &plan,std::size_t leaf)const {
    if(plan.guards.size()!=1U || !plan.full)return false;
    std::set<const NormalizedAtom *> guards;
    for(auto atom:dag_[0].filters_by_leaf[leaf])guards.insert(atom);
    for(auto group:dag_[0].boolean_groups_by_leaf[leaf])for(auto atom:group->atoms)guards.insert(atom);
    const auto direct=[&](const ChainAtom &test){return plan.slots[test.left].direct ||
        (!test.atom->right_is_const && plan.slots[test.right].direct);};
    for(const auto &test:plan.atoms)if(direct(test)&&!guards.count(test.atom))return false;
    for(const auto &group:plan.groups){bool own=false;
        for(const auto &token:group)if(token.first==static_cast<int>(LocalBooleanTokenKind::atom))own|=direct(token.second);
        if(own)for(const auto &token:group)if(token.first==static_cast<int>(LocalBooleanTokenKind::atom)&&!guards.count(token.second.atom))return false;
    }
    return true;
}

void configure_full_reuse() {
    kept_leaves_.resize(chain_plans_.size());
    // No path to keep, and no witness work for runs to remove. Preserve the
    // target-column loops without even collecting run-column pointers.
    if(dag_[0].children.empty())return;
    if(cf_composed_reuse)for(std::size_t leaf=0;leaf<chain_plans_.size();++leaf) {
        auto &plan=chain_plans_[leaf];auto &kept=kept_leaves_[leaf];
        if(!plan.enabled || !plan.compound_steps.empty())continue;
        if(std::all_of(plan.guards.begin(),plan.guards.end(),[&](const auto &guard){return column_is_unique(guard.root);}))continue;
        kept.single_root=kept_rest_closed(plan,leaf);
        if(kept.single_root){
            // The entering-rank verdict is authoritative. Projected endpoint
            // tuples and their front table would retain the same answer twice.
            if(cf_cost_dense_budget)dense_bytes_planned_-=plan.dense_front.size();
            projection_front_bytes_-=plan.dense_front.capacity();
            std::vector<std::uint8_t>().swap(plan.dense_front);plan.dense_strides.clear();
            plan.key_slots.clear();plan.predicate=0;
            plan.key_single_visit=column_is_unique(plan.guards.front().root);
        }
        for(auto &guard:plan.guards) {
            auto &root=kept_roots_[guard.root.runtime_column];root.root=guard.root;
            KeptUse use;use.root=&root;use.ends=guard.ends;
            for(const auto &end:use.ends)
                if(!compile_tight_hop(end))fail("cannot compile kept functional path");
            // Markers are branch-specific: no result can leak between different
            // predicates/polarities. Shared endpoint fields are predicate-free.
            if(kept.single_root)use.decision=root.field("decision:"+std::to_string(leaf));
            else {
                std::string path="valid";
                for(const auto &end:use.ends)path+=":"+std::to_string(reinterpret_cast<std::uintptr_t>(end.get()));
                use.valid=root.field(path);
            }
            for(std::size_t i=0;i<plan.slots.size();++i) {
                auto &slot=plan.slots[i];
                if(slot.direct || slot.root.runtime_column!=guard.root.runtime_column)continue;
                if(!compile_tight_hop(slot.step))fail("cannot compile kept endpoint path");
                const auto name=std::to_string(reinterpret_cast<std::uintptr_t>(slot.step.get()))+":"+slot.ref.key();
                // A complete one-root branch needs only its two-bit verdict.
                // Endpoint values for its first arrival remain transient.
                use.slots.emplace_back(i,kept.single_root ? SIZE_MAX :
                    root.field(name,std::max(1U,domain(column(slot.ref).domain).count)));
            }
            kept.uses.push_back(std::move(use));
        }
        kept.enabled=!kept.uses.empty();
        if(kept.enabled)kept.scratch.resize(plan.slots.size());
    }
    for(auto &entry:kept_roots_) {
        auto &root=entry.second;
        const auto count=column(root.root).cix.rank_count;
        root.ranks.plan(count,root.domains);
        const auto bytes=root.ranks.planned_bytes();
        if(!reserve_dense_cache(bytes))fail("dense budget cannot fit kept-chain array");
    }
    // Include every target operand, including own filters, constants' columns,
    // NULL-sensitive operands and nested local Boolean groups.
    std::map<std::size_t,ColumnRef> refs;
    const auto collect=[&](const NormalizedAtom *atom) {
        if(atom->left.node_id==target_node_)refs.emplace(atom->left.runtime_column,atom->left);
        if(!atom->right_is_const && atom->right.node_id==target_node_)
            refs.emplace(atom->right.runtime_column,atom->right);
    };
    for(auto leaf:leaves_) {
        for(auto atom:leaf->atoms)collect(atom);
        for(const auto &group:leaf->boolean_groups)for(auto atom:group.atoms)collect(atom);
    }
    for(const auto &entry:refs) {
        auto *forward=column(entry.second).forward_ranks;
        if(!forward)fail("run reuse requires a rank forward column");
        run_columns_.push_back(forward);
    }
}

std::uint32_t kept_resolve(const std::shared_ptr<ChainStep> &step,std::uint32_t rank,std::uint32_t target,
                           std::vector<std::pair<const ChainStep *,std::uint32_t>> &resolved) {
    for(const auto &old:resolved)if(old.first==step.get())return old.second;
    // The compiled hop also remembers this target arrival, so two endpoints
    // sharing a prefix do not re-read that prefix on their first arrival.
    // Suffix hop cells still share work between different arriving roots.
    CF_COUNT(++kept_build_depth_);
    const auto row=(this->*step->resolve)(step.get(),target,rank);
    CF_COUNT(--kept_build_depth_);
    resolved.emplace_back(step.get(),row);return row;
}

template<bool Decision=false>
bool prepare_kept_leaf(std::size_t leaf,std::uint32_t row,std::vector<std::uint32_t> *values,
                       bool *cached_decision=nullptr,bool *decision_hit=nullptr) {
    if(!target_walk_started_)fail("kept chain before first target row");
    auto &plan=chain_plans_[leaf];auto &kept=kept_leaves_[leaf];
    if(decision_hit)*decision_hit=false;
    for(std::size_t i=0;i<plan.slots.size();++i)if(plan.slots[i].direct)
        (*values)[i]=row_universe_rank(plan.slots[i].ref,row);
    for(auto &use:kept.uses) {
        auto &root=*use.root;
        const auto rank=row_universe_rank(root.root,row);
        if(root.current_row!=row) {
            CF_COUNT(++root.probes);
            const auto before=root.ranks.bytes();root.current_cell=root.ranks.arrive(rank);
            projection_front_bytes_+=root.ranks.bytes()-before;root.current_row=row;
        }
        auto cell=root.current_cell;
        if constexpr(Decision)if(cell[use.decision]!=kChainUnknown) {
            *cached_decision=cell[use.decision]==1U;
            if(decision_hit)*decision_hit=true;
            CF_COUNT(++kept_decision_hits_);return true;
        }
        if constexpr(Decision) {
            CF_COUNT(if(root.missed_row!=row){++root.misses;root.missed_row=row;});
            bool valid=rank!=kNullRank;
            auto &resolved=root.resolved;resolved.clear();
            if(valid)for(const auto &end:use.ends)
                if(kept_resolve(end,rank,row,resolved)==kNullRank){valid=false;break;}
            if(!valid){cell[use.decision]=2U;CF_COUNT(++kept_decisions_);return false;}
            for(const auto &binding:use.slots) {
                const auto &slot=plan.slots[binding.first];
                const auto end=kept_resolve(slot.step,rank,row,resolved);
                (*values)[binding.first]=end==kNullRank ? kNullRank : row_universe_rank(slot.ref,end);
            }
            continue;
        }
        // General projected paths use endpoints, not a complete branch verdict.
        // They can also be reached from the scalar walk rather than a tight loop.
        if(use.valid==SIZE_MAX) {
            // No recursive Decision call: that would cache a branch decision
            // without the caller evaluating the remaining predicate tests.
            auto &resolved=root.resolved;resolved.clear();
            if(rank==kNullRank)return false;
            for(const auto &end:use.ends)if(kept_resolve(end,rank,row,resolved)==kNullRank)return false;
            for(const auto &binding:use.slots) {
                const auto &slot=plan.slots[binding.first];
                const auto end=kept_resolve(slot.step,rank,row,resolved);
                (*values)[binding.first]=end==kNullRank ? kNullRank : row_universe_rank(slot.ref,end);
            }
            continue;
        }
        if(cell[use.valid]==kChainUnknown) {
            CF_COUNT(if(root.missed_row!=row){++root.misses;root.missed_row=row;});
            bool valid=rank!=kNullRank;
            auto &resolved=root.resolved;resolved.clear();
            if(valid)for(std::size_t i=0;i<use.ends.size();++i) {
                const auto end=kept_resolve(use.ends[i],rank,row,resolved);
                if(end==kNullRank){valid=false;break;}
            }
            if(valid)for(const auto &binding:use.slots) {
                auto &slot=plan.slots[binding.first];
                if(cell[binding.second]==kChainUnknown) {
                    const auto end=kept_resolve(slot.step,rank,row,resolved);
                    cell[binding.second]=end==kNullRank ? kNullRank : row_universe_rank(slot.ref,end);
                }
            }
            cell[use.valid]=valid ? 1U : 2U;
        }
        if(cell[use.valid]==2U)return false;
        // Another branch may already have validated the same path, while
        // asking for a different endpoint column. Fill only that newly reached
        // endpoint; never expose its unset code as a rank.
        for(const auto &binding:use.slots)if(cell[binding.second]==kChainUnknown) {
            auto &resolved=root.resolved;resolved.clear();
            const auto &slot=plan.slots[binding.first];
            const auto end=kept_resolve(slot.step,rank,row,resolved);
            cell[binding.second]=end==kNullRank ? kNullRank : row_universe_rank(slot.ref,end);
        }
        for(const auto &binding:use.slots)(*values)[binding.first]=cell[binding.second];
    }
    for(std::size_t i=0;i<plan.slots.size();++i) {
        plan.slots[i].kept_current_row=row;plan.slots[i].kept_current_value=(*values)[i];
    }
    return true;
}

void store_kept_decision(std::size_t leaf,std::uint32_t row,bool good) {
    auto &use=kept_leaves_[leaf].uses.front();
    const auto rank=row_universe_rank(use.root->root,row);
    use.root->ranks.arrive(rank)[use.decision]=good ? 1U : 2U;
    CF_COUNT(++kept_decisions_);
}

void report_full_reuse(std::uint32_t rows) {
    // Diagnostics only: report the complete input-tuple run count even after a
    // branch disables run detection. This scan is absent from clean libraries.
    CF_COUNT(
        run_count_=run_columns_.empty() ? rows : (rows ? 1U : 0U);
        std::vector<std::uint8_t> equal;
        constexpr std::uint32_t block=65536U;
        for(std::uint32_t base=1;!run_columns_.empty() && base<rows;base+=std::min(block,rows-base)) {
            const auto size=std::min(block,rows-base);equal.assign(size,1U);
            for(const auto *column:run_columns_)
                for(std::uint32_t i=0;i<size;++i)equal[i]&=column[base+i]==column[base+i-1U];
            for(auto same:equal)run_count_+=!same;
        }
        run_reused_rows_=rows-run_count_;
    );
    std::uint64_t probes=0,misses=0;std::size_t bytes=0;
    for(const auto &entry:kept_roots_){probes+=entry.second.probes;misses+=entry.second.misses;bytes+=entry.second.ranks.bytes();}
    cf_perf_metric_set("composed_probes",probes);cf_perf_metric_set("composed_misses",misses);
    cf_perf_metric_set("composed_bytes",bytes);cf_perf_metric_set("composed_decisions",kept_decisions_);
    cf_perf_metric_set("composed_decision_hits",kept_decision_hits_);
    cf_perf_metric_set("run_count",run_count_);cf_perf_metric_set("run_reused_rows",run_reused_rows_);
    cf_perf_metric_set("run_entering_columns",run_columns_.size());
    cf_perf_metric_set("run_rows_saved",run_rows_saved_);
    cf_perf_metric_set("kept_miss_path_probes",kept_miss_path_probes_);
    cf_perf_metric_set("outside_kept_path_probes",uncovered_path_probes_);
    cf_perf_metric_set("kept_hit_path_probes",kept_hit_path_probes_);
    cf_perf_metric_set("kept_hit_checked_rows",kept_hit_checked_rows_);
}
