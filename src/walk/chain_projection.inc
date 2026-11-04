// Entries are filled only after the first target row reaches a source rank.
static constexpr std::uint32_t kChainUnknown = UINT32_MAX - 1U;
struct ChainStep {
    ColumnRef source, unique, root;
    std::shared_ptr<ChainStep> parent;
    std::uint32_t cardinality = 0;
    ReachedCells<std::uint32_t> reached;
    bool cache_hop=true;
    std::uint64_t cache_probes=0,cache_hits=0,cache_entries=0;
    using Resolve=std::uint32_t(FusedWalkRuntime::*)(ChainStep *,std::uint32_t,std::uint32_t);
    Resolve resolve=nullptr;
    using RankResolve=std::uint32_t(FusedWalkRuntime::*)(const std::shared_ptr<ChainStep> &,std::uint32_t);
    RankResolve rank_resolve=nullptr;
    bool compound = false;
    std::uint32_t tuple_arity = 0;             // > 0: a declared key of the relation entered by several equalities
    std::vector<ColumnRef> tuple_columns;      // the key's columns in the entered relation, sorted by name
    std::vector<std::uint32_t> tuple_scratch;
    std::vector<ColumnRef> tuple_sources;
    std::vector<const NormalizedAtom *> tuple_atoms;
    std::unordered_map<FusedMemoKey, std::uint32_t, FusedMemoKeyHash> tuple_reached;
    PackedMemoMap tuple_packed;
    const std::uint32_t *source_forward=nullptr, *root_forward=nullptr;
    const ColumnIndex *destination=nullptr;
    std::vector<const std::uint32_t *> tuple_forward;
    std::uint32_t current_target = kNullRank, current_row = kNullRank;
};
struct ChainSlot {
    ColumnRef ref, root;
    std::shared_ptr<ChainStep> step;
    std::uint32_t cardinality = 0;
    mutable ReachedCells<std::uint32_t> reached;
    bool direct = false;
    bool cache_slot=true;
    mutable std::uint32_t kept_current_row=kNullRank,kept_current_value=kNullRank;
    mutable std::uint64_t cache_probes=0,cache_hits=0,cache_entries=0;
    using Value=std::uint32_t(FusedWalkRuntime::*)(const ChainSlot &,std::uint32_t);
    Value value=nullptr;
};
struct ChainAtom {
    const NormalizedAtom *atom = nullptr;
    std::size_t left = 0, right = 0;
};
struct ChainPlan {
    struct Guard {
        ColumnRef root;
        bool key_single_visit = false;
        std::uint32_t cardinality = 0;
        std::vector<std::shared_ptr<ChainStep>> ends;
        ReachedCells<std::uint8_t> state;
        std::uint64_t cache_probes=0,cache_hits=0,cache_entries=0;
        using Evaluate=bool(FusedWalkRuntime::*)(Guard &,std::uint32_t);
        Evaluate evaluate=nullptr;
    };
    bool enabled = false, full = false, key_single_visit = false, sparse=false;
    std::vector<ColumnRef> roots;
    std::vector<std::shared_ptr<ChainStep>> required_steps;
    std::vector<std::shared_ptr<ChainStep>> compound_steps;
    std::vector<Guard> guards;
    std::vector<ChainSlot> slots;
    std::vector<ChainAtom> atoms;
    std::vector<std::vector<std::pair<int, ChainAtom>>> groups;
    std::vector<std::size_t> key_slots;
    std::uint32_t predicate = 0;
    std::vector<std::size_t> dense_strides;
    std::vector<std::uint8_t> dense_front;
    bool direct_residual = false;
    std::uint8_t null_decision = 0;
};
// Metadata for a one-window Rest compiled from the current graph. Its cells
// and interval algebra are the same ones used by deeper composed windows.
struct WindowRequest {
    bool enabled=false, minimum=true, global=false, key_single_visit=false;
    bool indexed=false, recording=true;
    ColumnRef time,endpoint;
    const NormalizedAtom *removed=nullptr;
    int op=0;
    std::vector<ColumnRef> context;
    composed_windows::Cells cells;
    // Exact residual contexts of the existing graph compiler. These contain
    // windows, never endpoints copied to a second tight-loop decision cache.
    unsigned region_summary=UINT32_MAX;
};
std::vector<ChainPlan> chain_plans_;
std::vector<WindowRequest> window_requests_;
std::map<std::string, std::shared_ptr<ChainStep>> chain_steps_;
double projection_build_ms_ = 0, chain_boundary_build_ms_ = 0;
double decision_lookup_ms_ = 0, bitmap_mark_ms_ = 0;
double composite_probe_ms_ = 0, rank_order_build_ms_ = 0;
std::size_t projection_front_bytes_ = 0;
std::uint64_t projection_hits_good_ = 0, projection_hits_nogood_ = 0;
std::uint64_t projection_null_entries_ = 0;
std::uint64_t chain_boundary_hits_ = 0, chain_boundary_misses_ = 0;
std::uint64_t composite_decision_hits_ = 0, composite_decision_misses_ = 0;
std::uint64_t composite_connections_rejected_ = 0;
std::uint64_t functional_tuple_hops_ = 0, direct_residual_arrivals_ = 0;
std::uint64_t projected_hash_arrivals_ = 0;
std::uint64_t projected_hash_misses_ = 0;

void mark_allowed(std::vector<std::uint64_t> &allowed,std::uint32_t row) {
    std::chrono::steady_clock::time_point started;
    if (cf_engine_profile) started=std::chrono::steady_clock::now();
    allowed[row>>6U] |= std::uint64_t{1} << (row&63U);
    if (cf_engine_profile) bitmap_mark_ms_+=elapsed_ms(started,std::chrono::steady_clock::now());
}

bool composite_postings_pay(std::size_t node, std::size_t leaf) {
    const auto &edge = *dag_[node].edge_by_leaf[leaf];
    const auto &candidate = dag_[node].candidate_is_left_by_leaf[leaf] ? edge.left : edge.right;
    const auto &index = column(candidate);
    const auto distinct = column_distinct_ranks(candidate);
    double expected = distinct ? double(index.cix.row_count)/distinct : 0;
    // Local filters run after the posting is read; they do not reduce scan cost.
    return expected >= 8.0;
}

bool branch_composite_postings_pay(const FusedBranchPlan &branch,std::size_t node,std::size_t leaf) {
    const auto &entry=branch.nodes[node];
    const auto &candidate=entry.candidate_is_left ? entry.edge->left : entry.edge->right;
    const auto &index=column(candidate);
    const auto distinct=column_distinct_ranks(candidate);
    double expected=distinct ? double(index.cix.row_count)/distinct : 0;
    // Estimate rows read before residual filters, not rows surviving those filters.
    return expected>=8.0;
}

// Follow this path only when a source rank is reached.
template<class Cells> void initialize_chain_cells(Cells &cells, std::uint32_t cardinality) {
    if (!target_walk_started_) fail("chain cache allocation before first target row");
    if (cells.empty()) {
        if (cardinality >= kChainUnknown) fail("chain cardinality conflicts with unknown sentinel");
        cells.assign(cardinality, kChainUnknown);
        projection_front_bytes_ += cells.capacity() * sizeof(std::uint32_t);
    }
}

template<bool Cache,bool Sparse>
std::uint32_t resolve_chain_cells(const std::shared_ptr<ChainStep> &step, std::uint32_t rank) {
    if (!target_walk_started_) fail("chain projection before first target row");
    if (rank==kNullRank) return kNullRank;
    auto entering=rank;
    if (step->parent) {
        const auto parent_row=resolve_chain(step->parent,rank);
        entering=parent_row==kNullRank ? kNullRank : row_universe_rank(step->source,parent_row);
    }
    if (entering==kNullRank) return kNullRank;
    // Each hop reuses its own entering rank, not the upstream order/customer key.
    if constexpr(Cache) {
        initialize_chain_cells(step->reached, step->cardinality);
        if (entering >= step->reached.size()) fail("chain entering rank outside universe");
        const auto cached=step->reached.template at<Sparse>(entering);
        if (cached!=kChainUnknown) return cached;
    }
    auto &dst=column(step->unique);
    std::uint32_t row=kNullRank;
    if (entering!=kNullRank) {
        if (entering>=dst.cix.rank_count) fail("functional entering rank outside universe");
        const auto begin=dst.cix.begin(entering),end=dst.cix.end(entering);
        if (end-begin>1U) fail("functional projection encountered a nonunique key");
        if (end>begin) {row=u32le(dst.cix.child_rows+begin*4ULL);++partner_touches_;}
    }
    if constexpr(Cache)step->reached.template at<Sparse>(entering)=row;
    return row;
}
std::uint32_t resolve_chain(const std::shared_ptr<ChainStep> &step,std::uint32_t rank) {
    return (this->*step->rank_resolve)(step,rank);
}

std::shared_ptr<ChainStep> chain_step(const ColumnRef &source,const ColumnRef &unique,
                                     std::shared_ptr<ChainStep> parent) {
    const std::string identity=(parent ? parent->root.key()+":"+std::to_string(reinterpret_cast<std::uintptr_t>(parent.get())) : "ROOT")+
        ":"+source.key()+"="+unique.key();
    auto &step=chain_steps_[identity];
    if (step) return step;
    if (column(source).domain!=column(unique).domain) fail("functional chain crosses canonical universes");
    step=std::make_shared<ChainStep>();
    step->source=source;step->unique=unique;step->parent=parent;
    step->root=parent ? parent->root : source;
    step->compound=parent && parent->compound;
    step->cardinality=column(source).cix.rank_count;
    return step;
}

// Compound chains cache the full entering tuple, never one of its columns alone.
std::uint32_t resolve_compound_chain(const std::shared_ptr<ChainStep> &step,std::uint32_t row) {
    if (!target_walk_started_) fail("composite projection before first target row");
    if (!step->compound) return resolve_chain(step,row_local_rank(step->root,row));
    if (step->current_target==row) return step->current_row;
    const auto parent_row=step->parent ? resolve_compound_chain(step->parent,row) : row;
    std::uint32_t result=kNullRank;
    if (parent_row!=kNullRank) {
        const auto entering=row_universe_rank(step->source,parent_row);
        if (entering!=kNullRank) {
            initialize_chain_cells(step->reached,step->cardinality);
            result=step->reached[entering];
            if (result==kChainUnknown) {
                auto &idx=column(step->unique);
                const auto begin=idx.cix.begin(entering),end=idx.cix.end(entering);
                if (end-begin>1U) fail("functional compound continuation is not unique");
                result=end==begin ? kNullRank : u32le(idx.cix.child_rows+begin*4ULL);
                if (end>begin) ++partner_touches_;
                step->reached[entering]=result;
            }
        }
    }
    step->current_target=row;step->current_row=result;
    return result;
}


std::uint32_t intern_chain_predicate(std::size_t leaf, ChainPlan &plan) {
    // The branch identity includes every predicate and the Boolean grouping, not polarity.
    std::string text="PROJECTED_REMAINDER[";
    for (const auto *atom:leaves_[leaf]->atoms) text+=atom_proof_identity(*atom)+";";
    for (const auto &group:leaves_[leaf]->boolean_groups)
        for (const auto &token:group.postfix)
            text+=token.kind==LocalBooleanTokenKind::atom ? atom_proof_identity(*token.atom) :
                  token.kind==LocalBooleanTokenKind::conjunction ? "AND" : "OR";
    for (auto slot:plan.key_slots) text+="SLOT:"+plan.slots[slot].ref.key()+";";
    text+="]";
    auto inserted=rank_predicate_ids_.emplace(text,0U);
    if (inserted.second) {
        const auto ordinal=static_cast<std::uint32_t>(rank_predicate_ids_.size());
        if (ordinal >= (1U<<RankPredicateInstance::arity_shift)) fail("projection predicate capacity exceeded");
        const auto filled=plan.key_slots.empty() ? 0U : plan.key_slots.size()-1U;
        inserted.first->second=ordinal | (static_cast<std::uint32_t>(filled)<<RankPredicateInstance::arity_shift);
        rank_predicate_text_.push_back(&inserted.first->first);
        rank_gate_columns_.push_back(plan.key_slots.empty() ? "projection" : plan.slots[plan.key_slots.front()].ref.key());
    }
    const auto cardinality=plan.key_slots.empty() ? 1U :
        domain(column(plan.slots[plan.key_slots.front()].ref).domain).count;
    rank_store_.register_predicate(inserted.first->second,cardinality,cardinality);
    std::vector<ColumnRef> keys;
    for(auto slot:plan.key_slots)keys.push_back(plan.slots[slot].ref);
    const auto arrivals=planned_leaf_arrivals_.empty() ? target_rows_estimate_ : planned_leaf_arrivals_[leaf];
    if(cf_cost_single_visit && decision_repeat_ratio(arrivals,keys)>=4.0)
        rank_store_.open_without_probation(inserted.first->second);
    if((inserted.first->second>>RankPredicateInstance::arity_shift)==0U &&
       !reserve_dense_cache((std::size_t(cardinality)+3U)/4U))rank_store_.use_sparse(inserted.first->second);
    return inserted.first->second;
}

void configure_chain_projections() {
    chain_plans_.resize(leaves_.size());
    const auto started=std::chrono::steady_clock::now();
    std::size_t count=0;
    for (std::size_t leaf=0; cf_chain_projection && leaf<leaves_.size(); ++leaf) {
        if(composed_bound_program_)break; // no duplicate endpoint arrays for a summarized subwalk
        auto &plan=chain_plans_[leaf];
        std::map<int,std::shared_ptr<ChainStep>> resolved{{target_node_,nullptr}};
        std::set<int> occurrences{target_node_};
        std::set<const NormalizedAtom *> tree;
        const auto collect=[&](const NormalizedAtom *atom) {
            occurrences.insert(atom->left.node_id);
            if (!atom->right_is_const) occurrences.insert(atom->right.node_id);
        };
        for (auto atom:leaves_[leaf]->atoms) collect(atom);
        for (const auto &group:leaves_[leaf]->boolean_groups) for (auto atom:group.atoms) collect(atom);
        bool changed=true;
        while (changed) {
            changed=false;
            for (auto atom:leaves_[leaf]->atoms) {
                if (atom->right_is_const || atom->op!=POLICY_OP_EQ) continue;
                const bool left=resolved.count(atom->left.node_id), right=resolved.count(atom->right.node_id);
                if (left==right) continue;
                const auto &unique=left ? atom->right : atom->left;
                const auto &source=left ? atom->left : atom->right;
                if (!column_is_unique(unique)) continue;
                auto parent=resolved.at(source.node_id);
                // Root cardinality is not an admission cap. The complete
                // chain's actual arrays are charged by reserve_dense_cache
                // below; an exhausted budget selects reached-key storage.
                resolved[unique.node_id]=chain_step(source,unique,parent);
                tree.insert(atom); changed=true;
            }
        }
        if (resolved.size()==1U) continue;
        plan.full=resolved.size()==occurrences.size();
        plan.enabled=true; ++count;
        std::set<std::size_t> root_ids;
        for (const auto &item:resolved) {
            if (!item.second) continue;
            if (item.second->compound) {plan.compound_steps.push_back(item.second);continue;}
            plan.required_steps.push_back(item.second);
            if (root_ids.insert(item.second->root.runtime_column).second)
                plan.roots.push_back(item.second->root);
        }
        // A cached guard proves every required functional hop for this root.
        // Resolve only maximal paths; their prefixes are checked by resolve_chain.
        std::set<const ChainStep *> prefixes;
        for (const auto &step:plan.required_steps)
            for (auto parent=step->parent;parent;parent=parent->parent) prefixes.insert(parent.get());
        for (const auto &root:plan.roots) {
            ChainPlan::Guard guard;guard.root=root;
            guard.key_single_visit=cf_cost_single_visit &&
                ((root.node_id==target_node_ && column_is_unique(root)) ||
                 decision_repeat_ratio(planned_leaf_arrivals_[leaf],{root})<=1.0);
            guard.cardinality=column(root).cix.rank_count;
            for (const auto &step:plan.required_steps)
                if (step->root.runtime_column==root.runtime_column && !prefixes.count(step.get()))
                    guard.ends.push_back(step);
            plan.guards.push_back(std::move(guard));
        }
        std::map<std::pair<int,std::size_t>,std::size_t> slot_ids;
        const auto slot=[&](const ColumnRef &ref) {
            auto inserted=slot_ids.emplace(std::make_pair(ref.node_id,ref.runtime_column),plan.slots.size());
            if (!inserted.second) return inserted.first->second;
            ChainSlot value; value.ref=ref;
            if (ref.node_id==target_node_) { value.direct=true; value.root=ref; }
            else {
                value.step=resolved.at(ref.node_id);value.root=value.step->root;
            }
            value.cardinality=column(value.root).cix.rank_count;
            value.cache_slot=!cf_cost_single_visit || decision_repeat_ratio(planned_leaf_arrivals_[leaf],{value.root})>1.0;
            plan.slots.push_back(std::move(value));
            return inserted.first->second;
        };
        const auto known=[&](const NormalizedAtom *atom) {
            return resolved.count(atom->left.node_id) && (atom->right_is_const || resolved.count(atom->right.node_id));
        };
        const auto compiled=[&](const NormalizedAtom *atom) {
            return ChainAtom{atom,slot(atom->left),atom->right_is_const ? 0U : slot(atom->right)};
        };
        std::set<std::size_t> keys;
        for (auto atom:leaves_[leaf]->atoms) {
            if (tree.count(atom)) continue;
            if (known(atom)) {
                plan.atoms.push_back(compiled(atom));
                if (plan.full) {
                    keys.insert(slot(atom->left));
                    if (!atom->right_is_const) keys.insert(slot(atom->right));
                }
            } else {
                if (resolved.count(atom->left.node_id)) keys.insert(slot(atom->left));
                if (!atom->right_is_const && resolved.count(atom->right.node_id)) keys.insert(slot(atom->right));
            }
        }
        for (const auto &group:leaves_[leaf]->boolean_groups) {
            bool all=true;
            for (auto atom:group.atoms) all &= known(atom);
            if (all) {
                plan.groups.emplace_back();
                for (const auto &token:group.postfix) {
                    const auto kind=static_cast<int>(token.kind);
                    plan.groups.back().push_back({kind,token.kind==LocalBooleanTokenKind::atom ? compiled(token.atom) : ChainAtom{}});
                    if (plan.full && token.kind==LocalBooleanTokenKind::atom) {
                        keys.insert(slot(token.atom->left));
                        if (!token.atom->right_is_const) keys.insert(slot(token.atom->right));
                    }
                }
            } else for (auto atom:group.atoms) {
                if (resolved.count(atom->left.node_id)) keys.insert(slot(atom->left));
                if (!atom->right_is_const && resolved.count(atom->right.node_id)) keys.insert(slot(atom->right));
            }
        }
        if (keys.size()>16U) { plan.enabled=false; continue; }
        plan.key_slots.assign(keys.begin(),keys.end());
        if(cf_cost_single_visit) {
            std::vector<ColumnRef> key_columns;
            for(auto key:plan.key_slots)key_columns.push_back(plan.slots[key].ref);
            if(decision_repeat_ratio(planned_leaf_arrivals_[leaf],key_columns)<=1.0)plan.key_single_visit=true;
        }
        // Only an actual decision-key operand proves a single visit. A unique
        // source FK does not: its projected endpoint may repeat (nation, etc.).
        for (auto key:plan.key_slots) {
            const auto &value=plan.slots[key];
            if (cf_cost_single_visit && value.direct && value.ref.node_id==target_node_ && column_is_unique(value.ref))
                plan.key_single_visit=true;
        }
        if(cf_cost_hop_elision) {
            for(const auto &guard:plan.guards)if(!guard.key_single_visit)
                for(auto step:guard.ends) {
                    while(step->parent)step=step->parent;
                    step->cache_hop=false;
                }
            for(const auto &value:plan.slots)if(!value.direct && value.cache_slot && !value.step->compound) {
                auto step=value.step;while(step->parent)step=step->parent;
                step->cache_hop=false;
            }
        }
        // Only admitted dense arrays are reserved; rejected arrays use reached keys.
        std::size_t dense_bytes=0;
        for (const auto &step:plan.required_steps)
            if(step->cache_hop)dense_bytes+=std::size_t(step->cardinality)*sizeof(std::uint32_t);
        for (const auto &step:plan.compound_steps)
            if (!step->tuple_arity) dense_bytes+=std::size_t(step->cardinality)*sizeof(std::uint32_t);
        for (const auto &value:plan.slots)
            if (!value.direct && value.cache_slot && !value.step->compound)
                dense_bytes+=std::size_t(value.cardinality)*sizeof(std::uint32_t);
        for (const auto &guard:plan.guards)
            if (!guard.key_single_visit) dense_bytes+=std::size_t(guard.cardinality)+1U;
        if (!reserve_dense_cache(dense_bytes)) {
            plan.sparse=true;
            for(auto &step:plan.required_steps)step->reached.select_sparse();
            for(auto &step:plan.compound_steps)step->reached.select_sparse();
            for(auto &slot:plan.slots)slot.reached.select_sparse();
            for(auto &guard:plan.guards)guard.state.select_sparse();
        }
        // One plain rank comparison costs less than packing and probing its two-value key.
        plan.direct_residual=plan.full && plan.groups.empty() && plan.atoms.size()==1U &&
                             !plan.atoms[0].atom->right_is_const;
        if (rank_store_mode_) plan.predicate=intern_chain_predicate(leaf,plan);
        // A bounded front cache mirrors complete endpoint decisions only.
        // The authoritative store still uses (rank, predicate, filled ranks).
        if (rank_store_mode_ && plan.full && !plan.key_single_visit && !plan.key_slots.empty()) {
            std::size_t cells=1,present=1;
            for (auto slot:plan.key_slots) {
                const auto cardinality=domain(column(plan.slots[slot].ref).domain).count;
                // NULL is a separate cache slot, not an equal SQL value.
                const auto slots=std::size_t(cardinality)+1U;
                const auto occupied=std::size_t(column(plan.slots[slot].ref).cix.present_count)+1U;
                if (!cardinality || cells>SIZE_MAX/slots || present>262144U/occupied ||
                    (!cf_cost_present_caps && cells>262144U/slots)) { cells=0; break; }
                present*=occupied;
                plan.dense_strides.push_back(cells); cells*=slots;
            }
            if (cells && reserve_dense_cache((cells+3U)/4U)) {
                plan.dense_front.assign((cells+3U)/4U,0U);
                projection_front_bytes_+=plan.dense_front.capacity();
            } else plan.dense_strides.clear();
        }
    }
    if(cf_cost_single_visit)for(auto &entry:chain_steps_) {
        auto &step=*entry.second;double arrivals=0;
        for(std::size_t leaf=0;leaf<chain_plans_.size();++leaf) {
            const auto &plan=chain_plans_[leaf];if(!plan.enabled)continue;
            for(const auto &end:plan.required_steps)for(auto current=end;current;current=current->parent)
                if(current.get()==&step)arrivals=std::max(arrivals,planned_leaf_arrivals_[leaf]);
        }
        if(decision_repeat_ratio(arrivals,{step.source})<=1.0)step.cache_hop=false;
    }
    // Shared hops must agree on storage. Propagate sparse admission through
    // their connected plan component before compiling any target loop.
    bool storage_changed=true;
    while(storage_changed) {
        storage_changed=false;
        for(auto &plan:chain_plans_)if(plan.enabled) {
            for(const auto &step:plan.required_steps)if(step->reached.sparse() && !plan.sparse) {
                plan.sparse=true;storage_changed=true;
            }
            if(plan.sparse) {
                for(auto &step:plan.required_steps) {
                    for(auto p=step;p;p=p->parent)if(!p->reached.sparse()) {p->reached.select_sparse();storage_changed=true;}
                }
                for(auto &slot:plan.slots)slot.reached.select_sparse();
                for(auto &guard:plan.guards)guard.state.select_sparse();
            }
        }
    }
    for(auto &entry:chain_steps_) {
        auto &step=*entry.second;
        if(step.cache_hop)step.rank_resolve=step.reached.sparse() ?
            &FusedWalkRuntime::resolve_chain_cells<true,true> : &FusedWalkRuntime::resolve_chain_cells<true,false>;
        else step.rank_resolve=&FusedWalkRuntime::resolve_chain_cells<false,false>;
    }
    for(auto &plan:chain_plans_) {
        for(auto &slot:plan.slots) {
            if(slot.direct)slot.value=&FusedWalkRuntime::chain_value_mode<0>;
            else if(slot.step->compound)slot.value=&FusedWalkRuntime::chain_value_mode<4>;
            else if(!slot.cache_slot)slot.value=&FusedWalkRuntime::chain_value_mode<3>;
            else slot.value=slot.reached.sparse() ? &FusedWalkRuntime::chain_value_mode<2> : &FusedWalkRuntime::chain_value_mode<1>;
        }
        for(auto &guard:plan.guards)
            guard.evaluate=guard.key_single_visit ? &FusedWalkRuntime::chain_guard_mode<0> :
                guard.state.sparse() ? &FusedWalkRuntime::chain_guard_mode<2> : &FusedWalkRuntime::chain_guard_mode<1>;
    }
    projection_build_ms_=elapsed_ms(started,std::chrono::steady_clock::now());
    cf_perf_metric_set("projection_build_ms",projection_build_ms_);
    cf_perf_metric_set("projection_branches",count);
    std::size_t full=0,partial=0;
    for (const auto &plan:chain_plans_)
        if (plan.enabled) {if (plan.full) ++full;else ++partial;}
    cf_perf_metric_set("projection_full_branches",full);
    cf_perf_metric_set("projection_partial_branches",partial);
    cf_perf_metric_set("functional_tuple_hops",functional_tuple_hops_);
}

std::uint32_t chain_value(const ChainSlot &slot,std::uint32_t row) {
    if(cf_composed_reuse && slot.kept_current_row==row)return slot.kept_current_value;
    return (this->*slot.value)(slot,row);
}
template<int Mode> std::uint32_t chain_value_mode(const ChainSlot &slot,std::uint32_t row) {
    if constexpr(Mode==0)return row_universe_rank(slot.ref,row);
    else if constexpr(Mode==4) {
        const auto endpoint=resolve_compound_chain(slot.step,row);
        return endpoint==kNullRank ? kNullRank : row_universe_rank(slot.ref,endpoint);
    } else {
    const auto rank=row_local_rank(slot.root,row);
    if (rank==kNullRank) return kNullRank;
    if constexpr(Mode==3) {
        const auto endpoint=resolve_chain(slot.step,rank);
        return endpoint==kNullRank ? kNullRank : row_universe_rank(slot.ref,endpoint);
    }
    else {
    initialize_chain_cells(slot.reached, slot.cardinality);
    if (rank>=slot.reached.size()) fail("chain slot rank outside universe");
    const auto cached=slot.reached.template at<Mode==2>(rank);
    if (cached!=kChainUnknown) return cached;
    const auto endpoint=resolve_chain(slot.step,rank);
    const auto value=endpoint==kNullRank ? kNullRank : row_universe_rank(slot.ref,endpoint);
    slot.reached.template at<Mode==2>(rank)=value;
    return value;
    }
    }
}
bool chain_atom(const ChainAtom &test,const ChainPlan &plan,std::uint32_t row) {
    const auto value=chain_value(plan.slots[test.left],row);
    if (value==kNullRank) return false;
    const auto &atom=*test.atom;
    if (!atom.right_is_const) {
        const auto right=chain_value(plan.slots[test.right],row);
        return right!=kNullRank && compare_rank(value,atom.op,right);
    }
    switch (atom.op) {
        case POLICY_OP_EQ:return value>=atom.constant_lower && value<atom.constant_upper;
        case POLICY_OP_NE:return value<atom.constant_lower || value>=atom.constant_upper;
        case POLICY_OP_LT:return value<atom.constant_lower;
        case POLICY_OP_LE:return value<atom.constant_upper;
        case POLICY_OP_GT:return value>=atom.constant_upper;
        case POLICY_OP_GE:return value>=atom.constant_lower;
        default:fail("invalid projected operator");
    }
}
bool chain_tests(const ChainPlan &plan,std::uint32_t row) {
    for (const auto &atom:plan.atoms) if (!chain_atom(atom,plan,row)) return false;
    for (const auto &group:plan.groups) {
        std::vector<bool> stack;
        for (const auto &token:group) {
            if (token.first==static_cast<int>(LocalBooleanTokenKind::atom)) stack.push_back(chain_atom(token.second,plan,row));
            else {
                const bool right=stack.back(); stack.pop_back();
                const bool left=stack.back(); stack.pop_back();
                stack.push_back(token.first==static_cast<int>(LocalBooleanTokenKind::conjunction) ? left&&right : left||right);
            }
        }
        if (stack.size()!=1U || !stack.back()) return false;
    }
    return true;
}

bool chain_guard(ChainPlan::Guard &guard,std::uint32_t rank) {
    return (this->*guard.evaluate)(guard,rank);
}
template<int Mode> bool chain_guard_mode(ChainPlan::Guard &guard,std::uint32_t rank) {
    if (!target_walk_started_) fail("chain guard before first target row");
    if constexpr(Mode==0) {
        if (rank==kNullRank) return false;
        for (const auto &step:guard.ends) if (resolve_chain(step,rank)==kNullRank) return false;
        return true;
    }
    else {
    if (guard.state.empty()) {
        guard.state.assign(std::size_t(guard.cardinality)+1U,0U);
        projection_front_bytes_+=guard.state.capacity();
    }
    const auto cell=rank==kNullRank ? guard.cardinality : rank;
    if (cell>=guard.state.size()) fail("chain guard rank outside universe");
    auto &state=guard.state.template at<Mode==2>(cell);
    if (state) return state==1U;
    bool good=rank!=kNullRank;
    if (good) for (const auto &step:guard.ends)
        if (resolve_chain(step,rank)==kNullRank) {good=false;break;}
    state=good ? 1U : 2U;
    return good;
    }
}

bool chain_projected_truth(std::size_t leaf,std::uint32_t row,bool *truth) {
    auto &plan=chain_plans_[leaf];
    if (!plan.enabled) return false;
    const bool composed=cf_composed_reuse && kept_leaves_[leaf].enabled;
    const bool kept_verdict=composed && kept_leaves_[leaf].single_root;
    const auto finish=[&](){if(kept_verdict)store_kept_decision(leaf,row,*truth);return true;};
    if(composed) {
        auto &values=kept_leaves_[leaf].scratch;
        if(kept_verdict) {
            bool hit=false;
            if(!prepare_kept_leaf<true>(leaf,row,&values,truth,&hit)){*truth=false;return true;}
            if(hit)return true;
        } else if(!prepare_kept_leaf(leaf,row,&values)){*truth=false;return true;}
    }
    if(!composed) {
    for (const auto &step:plan.compound_steps)
        if (resolve_compound_chain(step,row)==kNullRank) {*truth=false;return true;}
    for (auto &guard:plan.guards) {
        const auto rank=row_universe_rank(guard.root,row);
        if (!chain_guard(guard,rank)) { *truth=false; return true; }
    }
    // Known predicates are checked before reusing a residual decision.
    }
    if (!plan.full && !chain_tests(plan,row)) { *truth=false; return true; }
    if (plan.direct_residual) {CF_COUNT(++direct_residual_arrivals_);*truth=chain_tests(plan,row);return finish();}
    std::array<std::uint32_t,16> key_values;
    std::uint32_t primary=0;
    std::size_t dense_key=0;
    bool dense_valid=!plan.dense_front.empty();
    for (std::size_t i=0;i<plan.key_slots.size();++i) {
        const auto value=chain_value(plan.slots[plan.key_slots[i]],row);
        key_values[i]=value;
        if (i==0U) primary=value;
        if (dense_valid) {
            const auto cell=value==kNullRank ? domain(column(plan.slots[plan.key_slots[i]].ref).domain).count : value;
            dense_key+=plan.dense_strides[i]*cell;
        }
    }
    const bool dense_cache=rank_store_mode_ && !plan.key_single_visit && rank_store_.enabled(plan.predicate);
    // Filled-operand hash keys include NULL explicitly; a one-rank NULL gets its own cell.
    const bool single_null=dense_cache && plan.full && plan.key_slots.size()==1U && primary==kNullRank;
    if (single_null && plan.null_decision) {
        *truth=plan.null_decision==1U;
        if (*truth) {CF_COUNT(++projection_hits_good_);++rank_store_.good_hits;}
        else {CF_COUNT(++projection_hits_nogood_);++rank_store_.no_good_hits;}
        return finish();
    }
    const bool cache=dense_cache && (primary!=kNullRank || plan.key_slots.size()>1U);
    if (dense_cache && dense_valid) {
        std::chrono::steady_clock::time_point started;
        if (cf_engine_profile) started=std::chrono::steady_clock::now();
        const auto cell=(plan.dense_front[dense_key/4U]>>((dense_key&3U)*2U))&3U;
        if (cell) {
            *truth=cell==1U;
            rank_store_.observe_range(plan.predicate,true,1U);
            if (*truth) { CF_COUNT(++projection_hits_good_); ++rank_store_.good_hits; }
            else { CF_COUNT(++projection_hits_nogood_); ++rank_store_.no_good_hits; }
        }
        if (cf_engine_profile) decision_lookup_ms_+=elapsed_ms(started,std::chrono::steady_clock::now());
        if (cell) return finish();
    }
    RankPredicateInstance instance;
    if(!RankDecisionStore::Key(plan.predicate,plan.key_slots.empty()?0:plan.key_slots.size()-1,
        [&](unsigned i,unsigned &rank){rank=key_values[i+1];return true;},instance))fail("projected Rest exceeds parameter capacity");
    std::chrono::steady_clock::time_point lookup_started;
    if (cache && cf_engine_profile) lookup_started=std::chrono::steady_clock::now();
    const bool hit=cache && rank_store_.lookup(primary,instance,truth);
    if (cache && cf_engine_profile) decision_lookup_ms_+=elapsed_ms(lookup_started,std::chrono::steady_clock::now());
    if (hit) {
        if (*truth) CF_COUNT(++projection_hits_good_); else CF_COUNT(++projection_hits_nogood_);
        return finish();
    }
    if (plan.full && !dense_valid) CF_COUNT(++projected_hash_misses_);
    if (plan.full) *truth=chain_tests(plan,row);
    else {
        const auto bit=std::uint64_t{1}<<leaf;
        *truth=true;
        for (auto child:dag_[0].children)
            if ((dag_[child].leaves&bit) && !(solve_node(child,bit,0U)&bit)) { *truth=false; break; }
        if (aborted_) return false;
    }
    // These decisions live at projected endpoints, not the single-visit target node.
    if (cache && rank_store_.enabled(instance.id) && !rank_store_.insert(primary,instance,*truth))
        fail("projected decision flipped");
    if (single_null) {
        plan.null_decision=*truth ? 1U : 2U;
        if (!dense_valid) CF_COUNT(++projection_null_entries_);
    }
    if (dense_cache && dense_valid && rank_store_.enabled(instance.id)) {
        const auto shift=(dense_key&3U)*2U;
        const unsigned old=(plan.dense_front[dense_key/4U]>>shift)&3U,value=*truth ? 1U : 2U;
        if (old && old!=value) fail("projection front cache flipped");
        if (!old && primary==kNullRank) CF_COUNT(++projection_null_entries_);
        plan.dense_front[dense_key/4U] |= value<<shift;
    }
    return finish();
}

void configure_window_requests() {
    window_requests_.resize(leaves_.size());
    if(composed_bound_program_)return;
    if (!cf_chain_boundaries) return;
    for (std::size_t leaf=0;leaf<leaves_.size();++leaf) {
        auto &plan=window_requests_[leaf];
        for (auto atom:leaves_[leaf]->atoms) {
            if (atom->right_is_const || atom->left.node_id==atom->right.node_id) continue;
            const bool left=atom->left.node_id==target_node_,right=atom->right.node_id==target_node_;
            if (left==right) continue;
            const int op=left ? atom->op : invert_op(atom->op);
            if (op!=POLICY_OP_LT && op!=POLICY_OP_LE && op!=POLICY_OP_GT && op!=POLICY_OP_GE) continue;
            plan.time=left ? atom->left : atom->right;
            plan.endpoint=left ? atom->right : atom->left;
            plan.op=op; plan.minimum=op==POLICY_OP_GT || op==POLICY_OP_GE;
            plan.removed=atom; break;
        }
        if (!plan.removed) continue;
        bool safe=true;
        std::map<std::size_t,ColumnRef> context;
        const auto check=[&](const NormalizedAtom *atom) {
            if (atom==plan.removed) return;
            for (auto ref:{&atom->left,atom->right_is_const ? nullptr : &atom->right})
                if (ref && ref->node_id==target_node_) {
                    if (ref->runtime_column==plan.time.runtime_column) safe=false;
                    else context.emplace(ref->runtime_column,*ref);
                }
        };
        for (auto atom:leaves_[leaf]->atoms) check(atom);
        for (const auto &group:leaves_[leaf]->boolean_groups) for (auto atom:group.atoms) check(atom);
        // The remaining witness graph must still connect to the target.
        std::set<int> connected{target_node_},all{target_node_};
        for (auto atom:leaves_[leaf]->atoms) {
            all.insert(atom->left.node_id);
            if (!atom->right_is_const) all.insert(atom->right.node_id);
        }
        for (const auto &group:leaves_[leaf]->boolean_groups) for (auto atom:group.atoms) {
            all.insert(atom->left.node_id); if (!atom->right_is_const) all.insert(atom->right.node_id);
        }
        bool changed=true;
        while (changed) {
            changed=false;
            for (auto atom:leaves_[leaf]->atoms) if (atom!=plan.removed && !atom->right_is_const) {
                if (connected.count(atom->left.node_id) && connected.insert(atom->right.node_id).second) changed=true;
                if (connected.count(atom->right.node_id) && connected.insert(atom->left.node_id).second) changed=true;
            }
        }
        // A target-independent witness graph has a single global boundary.
        // This is enabled only with the compiled-loop feature for ablation.
        if (cf_tight_loop && context.empty() && connected!=all) {
            std::set<int> witness_connected;
            for (int occurrence:all) if (occurrence!=target_node_) { witness_connected.insert(occurrence); break; }
            changed=true;
            while (changed) {
                changed=false;
                for (auto atom:leaves_[leaf]->atoms) if (atom!=plan.removed && !atom->right_is_const) {
                    if (witness_connected.count(atom->left.node_id) && witness_connected.insert(atom->right.node_id).second) changed=true;
                    if (witness_connected.count(atom->right.node_id) && witness_connected.insert(atom->left.node_id).second) changed=true;
                }
            }
            auto witnesses=all; witnesses.erase(target_node_);
            plan.global=witness_connected==witnesses && !witnesses.empty();
        }
        safe &= (connected==all || plan.global) && context.size()<=16U;
        for (const auto &item:context) plan.context.push_back(item.second);
        for (const auto &ref:plan.context)
            if (cf_cost_single_visit && ref.node_id==target_node_ && column_is_unique(ref)) plan.key_single_visit=true;
        plan.enabled=safe;
        if(safe) {
            const auto shape=plan.minimum ? composed_windows::Shape::lower : composed_windows::Shape::upper;
            plan.indexed=plan.global || plan.context.size()==1U;
            const auto count=plan.global ? 1U : plan.indexed ?
                std::size_t(column(plan.context[0]).cix.rank_count)+1U : 0U;
            plan.cells.plan(count,shape,column(plan.time).cix.rank_count);
            if(!plan.indexed){
                // A mandatory graph connection supplies the canonical rank;
                // every other outside value remains in this Rest's region.
                bool canonical=false;
                for(auto atom:leaves_[leaf]->atoms)if(atom!=plan.removed&&!atom->right_is_const){
                    const bool left=atom->left.node_id==target_node_,right=atom->right.node_id==target_node_;
                    if(left==right)continue;const auto &parent=left?atom->left:atom->right;
                    auto at=std::find_if(plan.context.begin(),plan.context.end(),[&](const ColumnRef&r){return same_ref(r,parent);});
                    if(at!=plan.context.end()){std::rotate(plan.context.begin(),at,at+1);canonical=true;break;}
                }
                if(!canonical)fail("contextual window has no mandatory entering connection");
                plan.region_summary=rank_store_.add_window_region(std::size_t(domain(column(plan.context.front()).domain).count)+1,
                    plan.context.size()-1);
            }
            if(plan.indexed && !plan.key_single_visit) {
                plan.recording=reserve_dense_cache(plan.cells.planned_bytes());
                if(!plan.recording)++bound_record_refusals_;
            }
        }
    }
}

// Enumerate complete witnesses, never independent pieces from different rows.
void enumerate_window_witnesses(std::size_t leaf,WindowRequest &plan,composed_windows::Coverage *coverage) {
    std::set<int> occurrences{target_node_};
    for (auto atom:leaves_[leaf]->atoms) {
        occurrences.insert(atom->left.node_id); if (!atom->right_is_const) occurrences.insert(atom->right.node_id);
        if (atom==plan.removed) continue;
        if (bindings_[atom->left.node_id]>=0 && (atom->right_is_const || bindings_[atom->right.node_id]>=0) && !atom_holds(*atom)) return;
    }
    for (const auto &group:leaves_[leaf]->boolean_groups) {
        bool bound=true;
        for (auto atom:group.atoms) {
            occurrences.insert(atom->left.node_id); if (!atom->right_is_const) occurrences.insert(atom->right.node_id);
            bound &= bindings_[atom->left.node_id]>=0 && (atom->right_is_const || bindings_[atom->right.node_id]>=0);
        }
        if (bound && !boolean_group_holds(group)) return;
    }
    bool complete=true;
    for (int occurrence:occurrences) complete &= bindings_[occurrence]>=0;
    if (complete) {
        const auto value=row_universe_rank(plan.endpoint,bindings_[plan.endpoint.node_id]);
        if(value!=kNullRank) {
            composed_windows::Coverage witness;
            witness.add(composed_windows::ordered_window(plan.cells.shape(),value,
                plan.op==POLICY_OP_GT || plan.op==POLICY_OP_LE,column(plan.time).cix.rank_count));
            coverage->unite(witness);
        }
        return;
    }
    const NormalizedAtom *chosen=nullptr;
    bool chosen_left=false;
    LookupResult chosen_lookup;
    std::uint64_t best=UINT64_MAX;
    for (auto atom:leaves_[leaf]->atoms) {
        if (atom==plan.removed || atom->right_is_const) continue;
        const bool left=bindings_[atom->left.node_id]>=0,right=bindings_[atom->right.node_id]>=0;
        if (left==right) continue;
        const auto lookup=edge_lookup(*atom,!left);
        const auto cost=posting_rows(column(left ? atom->right : atom->left),lookup);
        if (cost<best) { chosen=atom; chosen_left=!left; chosen_lookup=lookup; best=cost; }
    }
    if (!chosen && plan.global) {
        // Start with a selective mandatory constant, then enumerate joint witnesses.
        ColumnRef seed; bool found=false;
        for (auto atom:leaves_[leaf]->atoms) {
            if (atom==plan.removed || atom->left.node_id==target_node_ || bindings_[atom->left.node_id]>=0) continue;
            LookupResult lookup;
            if (atom->right_is_const) lookup=constant_lookup(*atom,column(atom->left));
            else { lookup.count=1; lookup.ranges[0]={0U,column(atom->left).cix.rank_count}; }
            const auto cost=posting_rows(column(atom->left),lookup);
            if (cost<best) { seed=atom->left;chosen_lookup=lookup;best=cost;found=true; }
        }
        if (!found) {
            // Rest may be TRUE: the removed ordered edge was its only atom.
            // On this first arrival use its endpoint as the witness seed.
            // Existing seeded summaries and their hot loops are unchanged.
            seed=plan.endpoint;
            chosen_lookup.count=1;
            chosen_lookup.ranges[0]={0U,column(seed).cix.rank_count};
        }
        auto &index=column(seed);
        for (int interval=0;interval<chosen_lookup.count;++interval)
            for (auto rank=chosen_lookup.ranges[interval].first;rank<chosen_lookup.ranges[interval].second;++rank)
                for (auto cursor=index.cix.begin(rank);cursor<index.cix.end(rank);++cursor) {
                    if ((online_build_tuples_&4095U)==0U) CHECK_FOR_INTERRUPTS();
                    ++online_build_tuples_;
                    bindings_[seed.node_id]=u32le(index.cix.child_rows+cursor*4ULL);
                    enumerate_window_witnesses(leaf,plan,coverage);
                    bindings_[seed.node_id]=-1;
                }
        return;
    }
    if (!chosen) fail("boundary summary has an unbound disconnected occurrence");
    const auto &candidate=chosen_left ? chosen->left : chosen->right;
    auto &index=column(candidate);
    for (int interval=0;interval<chosen_lookup.count;++interval)
        for (auto rank=chosen_lookup.ranges[interval].first;rank<chosen_lookup.ranges[interval].second;++rank)
            for (auto cursor=index.cix.begin(rank);cursor<index.cix.end(rank);++cursor) {
                if ((online_build_tuples_&4095U)==0U) CHECK_FOR_INTERRUPTS();
                ++online_build_tuples_;
                bindings_[candidate.node_id]=u32le(index.cix.child_rows+cursor*4ULL);
                enumerate_window_witnesses(leaf,plan,coverage);
                bindings_[candidate.node_id]=-1;
            }
}


std::size_t window_cell(const WindowRequest &plan,std::uint32_t row) {
    if(plan.global)return 0;
    const auto rank=row_local_rank(plan.context[0],row);
    return rank==kNullRank ? plan.cells.count()-1U : rank;
}
RankPredicateInstance window_context(const WindowRequest &plan,std::uint32_t row) {
    RankPredicateInstance key;const auto &summary=rank_store_.summaries[plan.region_summary];
    if(!RankDecisionStore::Key(summary.region_predicate,plan.context.size()-1,[&](unsigned i,unsigned &rank){
        rank=row_universe_rank(plan.context[i+1],row);return true;},key))fail("window Rest exceeds parameter capacity");
    return key;
}
void record_window(WindowRequest &plan,std::uint32_t row,const composed_windows::Coverage &coverage) {
    if(plan.key_single_visit)return;
    if(!plan.recording){++bound_record_skips_;return;}
    if(plan.indexed) {
        const auto before=plan.cells.bytes();plan.cells.put(window_cell(plan,row),coverage);
        projection_front_bytes_+=plan.cells.bytes()-before;
    } else {
        auto &summary=rank_store_.summaries[plan.region_summary];
        const auto value=row_universe_rank(plan.context.front(),row);
        const auto rank=value==kNullRank?summary.cells.count()-1:value;
        if(!rank_store_.Record(summary,rank,window_context(plan,row),coverage)){
            ++bound_record_refusals_;++bound_record_skips_;plan.recording=false;return;}
    }
}
int probe_window(WindowRequest &plan,std::uint32_t row,std::uint32_t value) {
    if(value==kNullRank)return 0;
    if(plan.key_single_visit)return -1;
    if(plan.indexed) {
        const auto cell=window_cell(plan,row);
        return plan.minimum ? plan.cells.probe_window<composed_windows::Shape::lower>(cell,value) :
                              plan.cells.probe_window<composed_windows::Shape::upper>(cell,value);
    }
    const auto &summary=rank_store_.summaries[plan.region_summary];
    const auto context=row_universe_rank(plan.context.front(),row);
    return rank_store_.Probe(summary,context==kNullRank?summary.cells.count()-1:context,window_context(plan,row),value);
}
bool window_truth(std::size_t leaf,std::uint32_t row,bool *truth) {
    auto &plan=window_requests_[leaf];if(!plan.enabled)return false;
    const auto value=row_universe_rank(plan.time,row);
    const auto answer=probe_window(plan,row,value);
    if(answer>=0) {
        if(value!=kNullRank)++chain_boundary_hits_;
        *truth=answer==1;return true;
    }
    ++chain_boundary_misses_;composed_windows::Coverage coverage;
    const auto started=std::chrono::steady_clock::now();
    enumerate_window_witnesses(leaf,plan,&coverage);
    record_window(plan,row,coverage);
    chain_boundary_build_ms_+=elapsed_ms(started,std::chrono::steady_clock::now());
    *truth=coverage.covers(value);return true;
}

void apply_chain_frontier(std::uint64_t candidates) {
    const auto row=static_cast<std::uint32_t>(bindings_[target_node_]);
    for (auto bits=candidates&~settled_;bits && !aborted_;bits&=bits-1U) {
        const auto leaf=static_cast<std::size_t>(__builtin_ctzll(bits));
        bool truth=false;
        if (window_truth(leaf,row,&truth) || chain_projected_truth(leaf,row,&truth)) {
            const auto bit=std::uint64_t{1}<<leaf;
            settle(bit,truth ? bit : 0U);
        }
    }
}
