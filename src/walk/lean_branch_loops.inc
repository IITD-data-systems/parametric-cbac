// Every branch chooses one structural loop at compile time, not at each row.
#ifndef CF_DIAGNOSTIC_COUNTERS
#define CF_DIAGNOSTIC_COUNTERS 1
#endif
#ifndef CF_COUNT
#if CF_DIAGNOSTIC_COUNTERS
#define CF_COUNT(expr) do {expr;} while(false)
#else
#define CF_COUNT(expr) do {} while(false)
#endif
#endif

template<bool Sparse,bool Cache>
std::uint32_t lean_hop(ChainStep *step,std::uint32_t target,std::uint32_t root_rank) {
    if(step->current_target==target)return step->current_row;
    const auto parent=step->parent ? (this->*step->parent->resolve)(step->parent.get(),target,root_rank) : target;
    std::uint32_t result=kNullRank;
    if(parent!=kNullRank) {
        const auto rank=step->parent ? step->source_forward[parent] : root_rank;
        if(rank!=kNullRank) {
            if constexpr(Cache) {
                note_path_probe();
                CF_COUNT(++step->cache_probes);
                if(step->reached.empty())initialize_chain_cells(step->reached,step->cardinality);
                auto &cell=step->reached.template at<Sparse>(rank);
                if(cell!=kChainUnknown){result=cell;CF_COUNT(++step->cache_hits);}
                else {result=lean_hop_row(step,rank);cell=result;CF_COUNT(++step->cache_entries);}
            } else result=lean_hop_row(step,rank);
        }
    }
    step->current_target=target;step->current_row=result;return result;
}
std::uint32_t lean_hop_row(ChainStep *step,std::uint32_t rank) {
    const auto &index=step->destination->cix;
    if(rank>=index.rank_count)fail("functional entering rank outside universe");
    const auto begin=index.begin(rank),end=index.end(rank);
    if(end-begin>1U)fail("functional hop encountered nonunique rank");
    CF_COUNT(++tight_inline_misses_);
    if(end==begin)return kNullRank;
    ++partner_touches_;
    return u32le(index.child_rows+begin*4ULL);
}

template<bool Sparse> std::uint32_t lean_slot(TightBranch::Value &value,std::uint32_t row) {
    auto *slot=value.slot;const auto rank=value.input.local(row);
    if(rank==kNullRank)return kNullRank;
    if(slot->reached.empty())initialize_chain_cells(slot->reached,slot->cardinality);
    CF_COUNT(++slot->cache_probes);
    note_path_probe();
    auto &cell=slot->reached.template at<Sparse>(rank);
    if(cell==kChainUnknown) {
        const auto endpoint=(this->*slot->step->resolve)(slot->step.get(),row,rank);
        cell=endpoint==kNullRank ? kNullRank : value.endpoint.local(endpoint);
        CF_COUNT(++slot->cache_entries);
    } else CF_COUNT(++slot->cache_hits);
    return cell;
}

template<bool Store,bool Front>
bool lean_projected_decide(TightBranch &branch,ChainPlan &plan) {
    if constexpr(!Store)return tight_tests(branch,plan);
    else if constexpr(Front) {
        std::size_t key=0;
        for(std::size_t i=0;i<plan.key_slots.size();++i) {
            const auto value=branch.resolved[plan.key_slots[i]];
            key+=plan.dense_strides[i]*(value==kNullRank ? branch.keys[i].null_cell : value);
        }
        auto &packed=plan.dense_front[key/4U];const auto shift=(key&3U)*2U;
        const auto cell=(packed>>shift)&3U;
        CF_COUNT(++branch.decision_probes);
        if(cell){CF_COUNT(if(cell==1U)++branch.good;else ++branch.nogood);return cell==1U;}
        const bool good=tight_tests(branch,plan);
        packed|=(good ? 1U : 2U)<<shift;
        CF_COUNT(++branch.decision_writes; ++branch_rank_entries_);
        return good;
    } else {
        // A closed entering-rank verdict owns this Rest. Its first arrival
        // still evaluates the tests, but has no second, private key to probe.
        if(plan.key_slots.empty())return tight_tests(branch,plan);
        RankPredicateInstance instance;const auto rank=branch.resolved[plan.key_slots.front()];
        if(!RankDecisionStore::Key(plan.predicate,plan.key_slots.size()-1,[&](unsigned i,unsigned &value){
            value=branch.resolved[plan.key_slots[i+1]];return true;},instance))fail("projected Rest exceeds parameter capacity");
        if(plan.key_slots.size()==1U && rank==kNullRank) {
            if(plan.null_decision)return plan.null_decision==1U;
            const bool good=tight_tests(branch,plan);plan.null_decision=good ? 1U : 2U;return good;
        }
        bool good=false;
        if(rank_store_.enabled(instance.id) && rank_store_.lookup(rank,instance,&good))return good;
        good=tight_tests(branch,plan);
        if(rank_store_.enabled(instance.id) && !rank_store_.insert(rank,instance,good))fail("endpoint decision flipped");
        return good;
    }
}

template<bool Store,bool Sparse,bool Front,bool Composed=false,bool RootDecision=false>
bool lean_projected(TightBranch &branch,std::uint32_t row) {
    auto &plan=chain_plans_[branch.leaf];
    if constexpr(Composed) {
        bool cached=false,hit=false;
        if(!prepare_kept_leaf<RootDecision>(branch.leaf,row,&branch.resolved,&cached,&hit))return false;
        if(hit)return cached;
    } else {
    for(auto &entry:branch.direct_guards) {
        const auto rank=entry.input.local(row);
        if(rank==kNullRank)return false;
        for(auto &end:entry.guard->ends)
            if((this->*end->resolve)(end.get(),row,rank)==kNullRank)return false;
    }
    for(auto &entry:branch.guards) {
        auto &guard=*entry.guard;const auto rank=entry.input.local(row);
        const auto key=rank==kNullRank ? guard.cardinality : rank;
        if(guard.state.empty()) {
            guard.state.assign(std::size_t(guard.cardinality)+1U,0U);
            projection_front_bytes_+=guard.state.capacity();
        }
        auto &cell=guard.state.template at<Sparse>(key);
        CF_COUNT(++guard.cache_probes);
        note_path_probe();
        if(!cell) {
            bool good=rank!=kNullRank;
            if(good)for(auto &end:guard.ends)
                if((this->*end->resolve)(end.get(),row,rank)==kNullRank){good=false;break;}
            cell=good ? 1U : 2U;
            CF_COUNT(++guard.cache_entries);
        } else CF_COUNT(++guard.cache_hits);
        if(cell==2U)return false;
    }
    for(auto i:branch.direct_values)branch.resolved[i]=branch.values[i].input.local(row);
    for(auto i:branch.uncached_values) {
        auto &value=branch.values[i];const auto rank=value.input.local(row);
        const auto endpoint=rank==kNullRank ? kNullRank : (this->*value.slot->step->resolve)(value.slot->step.get(),row,rank);
        branch.resolved[i]=endpoint==kNullRank ? kNullRank : value.endpoint.local(endpoint);
    }
    for(auto i:branch.indirect_values)branch.resolved[i]=lean_slot<Sparse>(branch.values[i],row);
    }
    const bool good=lean_projected_decide<Store,Front>(branch,plan);
    if constexpr(RootDecision)
        store_kept_decision(branch.leaf,row,good);
    return good;
}

template<bool Front>
bool lean_kept_first(TightBranch &branch,std::uint32_t row,std::uint32_t rank) {
    CF_COUNT(++kept_build_depth_;++kept_fill_events_);
    auto &use=kept_leaves_[branch.leaf].uses.front();auto &root=*use.root;
    CF_COUNT(++root.probes;++root.misses);
    bool valid=rank!=kNullRank;
    if(valid)for(const auto &end:use.ends)
        if((this->*end->resolve)(end.get(),row,rank)==kNullRank){valid=false;break;}
    bool good=false;
    if(valid) {
        for(std::size_t i=0;i<branch.values.size();++i) {
            const auto &value=branch.values[i];
            if(value.slot->direct){branch.resolved[i]=value.input.rows[row];continue;}
            const auto endpoint=(this->*value.slot->step->resolve)(value.slot->step.get(),row,rank);
            branch.resolved[i]=endpoint==kNullRank ? kNullRank : value.endpoint.rows[endpoint];
        }
        good=lean_projected_decide<true,Front>(branch,chain_plans_[branch.leaf]);
    }
    root.ranks.arrive(rank)[use.decision]=good ? 1U : 2U;
    CF_COUNT(++kept_decisions_;--kept_build_depth_);return good;
}

void lean_kept_group_first(TightBranch &branch,TightBranch::KeptGroup &group,
                           std::uint32_t row,std::uint32_t rank) {
    CF_COUNT(++kept_build_depth_;++kept_fill_events_);
    auto &use=*group.use;auto &root=*use.root;auto cell=root.ranks.arrive(rank);
    CF_COUNT(++root.misses);
    bool valid=rank!=kNullRank;
    if(valid)for(const auto &end:use.ends)
        if((this->*end->resolve)(end.get(),row,rank)==kNullRank){valid=false;break;}
    if(valid)for(const auto &field:group.values) {
        if(cell[field.field]!=kChainUnknown)continue;
        const auto &value=branch.values[field.slot];
        const auto endpoint=(this->*value.slot->step->resolve)(value.slot->step.get(),row,rank);
        cell[field.field]=endpoint==kNullRank ? kNullRank : value.endpoint.rows[endpoint];
    }
    cell[use.valid]=valid ? 1U : 2U;
    CF_COUNT(--kept_build_depth_);
}

template<unsigned Width>
std::uint32_t lean_kept_field(TightBranch &branch,TightBranch::KeptGroup &group,
                             const TightBranch::KeptValue &value,std::uint32_t key,std::uint32_t rank,std::uint32_t row) {
    std::uint32_t endpoint;
    if constexpr(Width==1)endpoint=static_cast<const std::uint8_t*>(value.ranks)[key];
    else if constexpr(Width==2)endpoint=static_cast<const std::uint16_t*>(value.ranks)[key];
    else endpoint=static_cast<const std::uint32_t*>(value.ranks)[key];
    const bool unknown=Width==4 ? endpoint==kChainUnknown : endpoint==value.domain+1U;
    if(unknown) {
        lean_kept_group_first(branch,group,row,rank);
        return group.use->root->ranks.peek(rank,value.field);
    }
    if constexpr(Width!=4)if(endpoint==value.domain)return kNullRank;
    return endpoint;
}

template<bool Front,bool Own,unsigned Width,bool Store=true>
std::uint64_t lean_compact_endpoints(TightBranch &branch,std::uint32_t base,std::uint64_t live,std::uint64_t *) {
    if(!live)return 0;
    if(!target_walk_started_)fail("kept endpoint before first target row");
    if(!branch.kept_initialized) {
        const auto first=base+__builtin_ctzll(live);
        for(auto &group:branch.kept_groups) {
            auto &root=*group.use->root;const auto before=root.ranks.bytes();
            root.ranks.arrive(group.input.rows[first]);projection_front_bytes_+=root.ranks.bytes()-before;
            group.states=root.ranks.states(group.use->valid);
            if constexpr(Width)for(auto &value:group.values)value.ranks=root.ranks.template ranks<Width>(value.field);
            else {
                for(auto &value:group.u8)value.ranks=root.ranks.template ranks<1>(value.field);
                for(auto &value:group.u16)value.ranks=root.ranks.template ranks<2>(value.field);
                for(auto &value:group.u32)value.ranks=root.ranks.template ranks<4>(value.field);
            }
        }
        branch.kept_initialized=true;
    }
    std::uint64_t passing=0;auto &plan=chain_plans_[branch.leaf];
    for(auto bits=live;bits;bits&=bits-1U) {
        const auto offset=static_cast<std::uint32_t>(__builtin_ctzll(bits)),row=base+offset;
        [[maybe_unused]] const auto before_fills=kept_fill_events_,before_probes=physical_path_probes_;
        if constexpr(Own) {
            bindings_[target_node_]=row;
            if(!(evaluate_filters(0,std::uint64_t{1}<<branch.leaf)&(std::uint64_t{1}<<branch.leaf)))continue;
        }
        bool valid=true;
        for(auto &group:branch.kept_groups) {
            const auto rank=group.input.rows[row],key=rank==kNullRank ? group.null_key : rank;
            CF_COUNT(++group.use->root->probes);
            auto state=(group.states[key/4U]>>((key&3U)*2U))&3U;
            if(!state){lean_kept_group_first(branch,group,row,rank);state=(group.states[key/4U]>>((key&3U)*2U))&3U;}
            if(state==2U){valid=false;break;}
            if constexpr(Width)for(const auto &value:group.values)
                branch.resolved[value.slot]=lean_kept_field<Width>(branch,group,value,key,rank,row);
            else {
                for(const auto &value:group.u8)branch.resolved[value.slot]=lean_kept_field<1>(branch,group,value,key,rank,row);
                for(const auto &value:group.u16)branch.resolved[value.slot]=lean_kept_field<2>(branch,group,value,key,rank,row);
                for(const auto &value:group.u32)branch.resolved[value.slot]=lean_kept_field<4>(branch,group,value,key,rank,row);
            }
        }
        if(!valid) {
            CF_COUNT(if(before_fills==kept_fill_events_){++kept_hit_checked_rows_;kept_hit_path_probes_+=physical_path_probes_-before_probes;});
            continue;
        }
        for(auto index:branch.direct_values)branch.resolved[index]=branch.values[index].input.rows[row];
        if(lean_projected_decide<Store,Front>(branch,plan))passing|=std::uint64_t{1}<<offset;
        CF_COUNT(if(before_fills==kept_fill_events_){++kept_hit_checked_rows_;kept_hit_path_probes_+=physical_path_probes_-before_probes;});
    }
    return passing;
}

template<unsigned Width>
void choose_compact_endpoints(TightBranch &branch,bool front,bool own) {
    // A comparison of two kept endpoint ranks does not need a second store.
    if(branch.key_single_visit || chain_plans_[branch.leaf].direct_residual) {
        branch.loop=own ? &FusedWalkRuntime::lean_compact_endpoints<false,true,Width,false> :
                          &FusedWalkRuntime::lean_compact_endpoints<false,false,Width,false>;
        return;
    }
    if(front)branch.loop=own ? &FusedWalkRuntime::lean_compact_endpoints<true,true,Width> : &FusedWalkRuntime::lean_compact_endpoints<true,false,Width>;
    else branch.loop=own ? &FusedWalkRuntime::lean_compact_endpoints<false,true,Width> : &FusedWalkRuntime::lean_compact_endpoints<false,false,Width>;
}

bool compile_compact_endpoints(TightBranch &branch) {
    const auto &plan=chain_plans_[branch.leaf];
    unsigned width=0;bool mixed=false;
    for(auto &use:kept_leaves_[branch.leaf].uses) {
        TightBranch::KeptGroup group;group.use=&use;
        group.input.rows=column(use.root->root).forward_ranks;group.null_key=column(use.root->root).cix.rank_count;
        for(const auto &binding:use.slots) {
            const auto next=use.root->ranks.width(binding.second);
            if(width && next!=width)mixed=true;
            width=next;
            group.values.push_back({binding.first,binding.second,use.root->ranks.domain(binding.second),nullptr});
            auto &typed=next==1 ? group.u8 : next==2 ? group.u16 : group.u32;
            typed.push_back(group.values.back());
        }
        branch.kept_groups.push_back(std::move(group));
    }
    if(!width)return false;
    const bool front=!plan.dense_front.empty();
    const bool own=!dag_[0].filters_by_leaf[branch.leaf].empty() || !dag_[0].boolean_groups_by_leaf[branch.leaf].empty();
    if(mixed)choose_compact_endpoints<0>(branch,front,own);
    else if(width==1)choose_compact_endpoints<1>(branch,front,own);
    else if(width==2)choose_compact_endpoints<2>(branch,front,own);
    else choose_compact_endpoints<4>(branch,front,own);
    return true;
}

template<bool Store,bool Sparse> bool lean_ranked(TightBranch &branch,std::uint32_t row,std::uint64_t *slow) {
    const auto rank=branch.context.local(row),key=rank==kNullRank ? branch.null_cell : rank;
    unsigned shift=0;std::uint8_t *packed=nullptr;
    if constexpr(Store) {
        shift=(key&3U)*2U;packed=&branch.rank_cells.template at<Sparse>(key/4U);
        const auto cell=(*packed>>shift)&3U;
        CF_COUNT(++branch.decision_probes);
        if(cell){CF_COUNT(if(cell==1U)++branch_good_;else ++branch_nogood_);return cell==1U;}
    }
    CF_COUNT(++*slow);
    bool good=true;
    for(auto index:branch.entering_indexes)
        if(rank==kNullRank || index->cix.begin(rank)==index->cix.end(rank)){good=false;break;}
    if(good) {
        const auto old_settled=settled_,old_truth=truth_,old_ternary=formula_ternary_state_;const auto old_aborted=aborted_;
        settled_=truth_=formula_ternary_state_=0;aborted_=false;bindings_[target_node_]=row;
        const auto bit=std::uint64_t{1}<<branch.leaf;
        good=(evaluate_filters(0,bit)&bit)!=0U;bool decided=false;
        if(good)decided=window_truth(branch.leaf,row,&good) || chain_projected_truth(branch.leaf,row,&good);
        if(good && !decided)for(auto child:dag_[0].children)
            if((dag_[child].leaves&bit) && !(solve_node(child,bit,0U)&bit)){good=false;break;}
        if(aborted_)fail("interrupted rank decision");
        settled_=old_settled;truth_=old_truth;formula_ternary_state_=old_ternary;aborted_=old_aborted;
    }
    if constexpr(Store){*packed|=(good ? 1U : 2U)<<shift;CF_COUNT(++branch.decision_writes; ++branch_rank_entries_);}
    return good;
}

bool lean_branch_miss(TightBranch &branch,std::uint32_t row) {
    const auto old_settled=settled_,old_truth=truth_,old_ternary=formula_ternary_state_;const auto old_aborted=aborted_;
    settled_=truth_=formula_ternary_state_=0;aborted_=false;bindings_[target_node_]=row;
    const auto bit=std::uint64_t{1}<<branch.leaf;
    bool good=(evaluate_filters(0,bit)&bit)!=0U,decided=false;
    if(good)decided=window_truth(branch.leaf,row,&good) || chain_projected_truth(branch.leaf,row,&good);
    if(good && !decided)for(auto child:dag_[0].children)
        if((dag_[child].leaves&bit) && !(solve_node(child,bit,0U)&bit)){good=false;break;}
    if(aborted_)fail("interrupted complete-instance decision");
    settled_=old_settled;truth_=old_truth;formula_ternary_state_=old_ternary;aborted_=old_aborted;
    return good;
}
template<bool Store,bool Two> bool lean_packed(TightBranch &branch,std::uint32_t row,std::uint64_t *slow) {
    if constexpr(!Store){CF_COUNT(++*slow);return lean_branch_miss(branch,row);}
    else {
        FusedMemoKey key{};key.width=branch.operands.size();
        for(std::size_t i=0;i<key.width;++i)key.ranks[i]=branch.operands[i].local(row);
        const auto packed=std::uint64_t{key.ranks[0]}|(std::uint64_t{key.ranks[1]}<<32U);
        if(rank_store_.enabled(branch.instance_predicate)) {
            CF_COUNT(++branch.decision_probes);
            if constexpr(Two) {
                if(auto cell=branch.packed_cells.find(packed)) {
                    rank_store_.observe_range(branch.instance_predicate,true,cell->touch_cost);
                    CF_COUNT(if(cell->truth)++branch_good_;else ++branch_nogood_);return cell->truth;
                }
            } else {
                auto found=branch.wide_cells.find(key);
                if(found!=branch.wide_cells.end()) {
                    rank_store_.observe_range(branch.instance_predicate,true,found->second.touch_cost);
                    CF_COUNT(if(found->second.truth)++branch_good_;else ++branch_nogood_);return found->second.truth;
                }
            }
            rank_store_.observe_range(branch.instance_predicate,false,0U);
        }
        CF_COUNT(++*slow);const auto touches=partner_touches_+online_build_tuples_;
        const bool good=lean_branch_miss(branch,row);
        if(rank_store_.enabled(branch.instance_predicate)) {
            const auto reads=static_cast<std::uint32_t>(std::min<std::uint64_t>(UINT32_MAX,partner_touches_+online_build_tuples_-touches));
            if constexpr(Two)branch.packed_cells.insert(packed,FusedMemoEntry{good,reads});
            else branch.wide_cells.emplace(key,FusedMemoEntry{good,reads});
            CF_COUNT(++branch_rank_entries_;++branch.decision_writes);
        }
        return good;
    }
}
template<bool Store,bool Sparse,bool Global,bool Probe=true>
bool lean_window(TightBranch &branch,std::uint32_t row,std::uint64_t *slow) {
    const auto time=branch.time.local(row);if(time==kNullRank)return false;
    std::size_t cell=0;
    if constexpr(Store && Probe) {
        if constexpr(!Global) {
            const auto rank=branch.context.local(row);cell=rank==kNullRank ? branch.window->count()-1U : rank;
        }
        CF_COUNT(++branch.decision_probes);
        const auto answer=branch.above ?
            branch.window_view.probe_window<composed_windows::Shape::lower>(cell,time) :
            branch.window_view.probe_window<composed_windows::Shape::upper>(cell,time);
        if(answer>=0) {
            CF_COUNT(++branch.boundary_hits);
            return answer==1;
        }
    }
    CF_COUNT(++*slow);bool truth=false;
    if(!window_truth(branch.leaf,row,&truth))fail("compiled window unresolved");
    branch.window_view=branch.window->read_view<false>();
    CF_COUNT(if constexpr(Store)++branch.decision_writes;);
    return truth;
}

template<int Kind,bool Store,bool Sparse,bool Own>
std::uint64_t lean_loop(TightBranch &branch,std::uint32_t base,std::uint64_t live,std::uint64_t *slow) {
    std::uint64_t passing=0;
    if constexpr(Store && (Kind==3 || Kind==5)) {
        // No allocation test in the normal gather. Until first Record (or
        // throughout a zero-budget walk), expand only the actually live rows.
        if(!branch.window_view.allocated()) {
            while(live) {
                const auto offset=std::uint32_t(__builtin_ctzll(live)),row=base+offset;
                live&=live-1U;bindings_[target_node_]=row;
                if constexpr(Own)if(!(evaluate_filters(0,std::uint64_t{1}<<branch.leaf)&(std::uint64_t{1}<<branch.leaf)))continue;
                if(lean_window<Store,Sparse,Kind==5,false>(branch,row,slow))passing|=std::uint64_t{1}<<offset;
                if(branch.window_view.allocated())
                    return passing|lean_loop<Kind,Store,Sparse,Own>(branch,base,live,slow);
            }
            return passing;
        }
    }
    for(auto bits=live;bits;bits&=bits-1U) {
        const auto offset=static_cast<std::uint32_t>(__builtin_ctzll(bits)),row=base+offset;
        const auto leafbit=std::uint64_t{1}<<branch.leaf;
        if constexpr(Own || (Kind!=0 && Kind!=4))bindings_[target_node_]=row;
        if constexpr(Own)if(!(evaluate_filters(0,leafbit)&leafbit))continue;
        bool good=false;
        if constexpr(Kind==0)good=lean_projected<Store,Sparse,false>(branch,row);
        else if constexpr(Kind==4)good=lean_projected<Store,Sparse,true>(branch,row);
        else if constexpr(Kind==1)good=lean_ranked<Store,Sparse>(branch,row,slow);
        else if constexpr(Kind==2)good=lean_packed<Store,true>(branch,row,slow);
        else if constexpr(Kind==6)good=lean_packed<Store,false>(branch,row,slow);
        else if constexpr(Kind==7)good=lean_projected<Store,Sparse,false,true>(branch,row);
        else if constexpr(Kind==8)good=lean_projected<Store,Sparse,true,true>(branch,row);
        else if constexpr(Kind==9)good=lean_projected<Store,Sparse,false,true,true>(branch,row);
        else if constexpr(Kind==10)good=lean_projected<Store,Sparse,true,true,true>(branch,row);
        else if constexpr(Kind==3)good=lean_window<Store,Sparse,false>(branch,row,slow);
        else if constexpr(Kind==5)good=lean_window<Store,Sparse,true>(branch,row,slow);
        if(good)passing|=std::uint64_t{1}<<offset;
    }
    return passing;
}
template<int Kind,bool Own> void choose_lean_cells(TightBranch &branch,bool store) {
    if(store)branch.loop=branch.sparse ? &FusedWalkRuntime::lean_loop<Kind,true,true,Own> : &FusedWalkRuntime::lean_loop<Kind,true,false,Own>;
    else branch.loop=branch.sparse ? &FusedWalkRuntime::lean_loop<Kind,false,true,Own> : &FusedWalkRuntime::lean_loop<Kind,false,false,Own>;
}

// Complete one-root predicates need only a two-bit verdict gather. All dynamic
// chain/slot/metadata work remains on the first-arrival miss path.
template<bool Front,bool Own>
std::uint64_t lean_kept_verdict(TightBranch &branch,std::uint32_t base,std::uint64_t live,std::uint64_t *) {
    if(!live)return 0;
    if(!target_walk_started_)fail("kept verdict before first target row");
    auto &use=kept_leaves_[branch.leaf].uses.front();auto &root=*use.root;
    if(root.ranks.empty()) {
        const auto before=root.ranks.bytes();
        root.ranks.arrive(branch.kept_input.rows[base+__builtin_ctzll(live)]);
        projection_front_bytes_+=root.ranks.bytes()-before;
    }
    const auto *states=root.ranks.states(use.decision);
    const auto *inputs=branch.kept_input.rows+base;
    const auto null_key=column(root.root).cix.rank_count;
    std::uint64_t passing=0,hits=0;
    for(auto bits=live;bits;bits&=bits-1U) {
        const auto offset=static_cast<std::uint32_t>(__builtin_ctzll(bits)),row=base+offset;
        if constexpr(Own) {
            bindings_[target_node_]=row;
            if(!(evaluate_filters(0,std::uint64_t{1}<<branch.leaf)&(std::uint64_t{1}<<branch.leaf)))continue;
        }
        const auto rank=inputs[offset],key=rank==kNullRank ? null_key : rank;
        const auto cell=(states[key/4U]>>((key&3U)*2U))&3U;
        bool good;
        if(cell){good=cell==1U;CF_COUNT(++hits;++kept_hit_checked_rows_);}
        else good=lean_kept_first<Front>(branch,row,rank);
        if(good)passing|=std::uint64_t{1}<<offset;
    }
    CF_COUNT(root.probes+=hits;kept_decision_hits_+=hits);
    return passing;
}
template<int Kind> void choose_lean_storage(TightBranch &branch,bool store) {
    if(dag_[0].filters_by_leaf[branch.leaf].empty() && dag_[0].boolean_groups_by_leaf[branch.leaf].empty())
        choose_lean_cells<Kind,false>(branch,store);
    else choose_lean_cells<Kind,true>(branch,store);
}
void choose_lean_loop(TightBranch &branch) {
    const bool store=!branch.key_single_visit;
    if(branch.projected) {
        const auto &plan=chain_plans_[branch.leaf];
        if(branch.composed) {
            if(kept_leaves_[branch.leaf].single_root) {
                branch.kept_input.rows=column(kept_leaves_[branch.leaf].uses.front().root->root).forward_ranks;
                const bool own=!dag_[0].filters_by_leaf[branch.leaf].empty() || !dag_[0].boolean_groups_by_leaf[branch.leaf].empty();
                if(plan.dense_front.empty())branch.loop=own ? &FusedWalkRuntime::lean_kept_verdict<false,true> : &FusedWalkRuntime::lean_kept_verdict<false,false>;
                else branch.loop=own ? &FusedWalkRuntime::lean_kept_verdict<true,true> : &FusedWalkRuntime::lean_kept_verdict<true,false>;
            }
            else if(compile_compact_endpoints(branch))return;
            else if(plan.dense_front.empty())choose_lean_storage<7>(branch,store && !plan.direct_residual);
            else choose_lean_storage<8>(branch,store && !plan.direct_residual);
        }
        else if(plan.dense_front.empty())choose_lean_storage<0>(branch,store && !plan.direct_residual);
        else choose_lean_storage<4>(branch,store && !plan.direct_residual);
    } else if(branch.ranked)choose_lean_storage<1>(branch,store);
    else if(branch.packed_ranked) {
        // Several target operands do not define an entering rank. Delegate
        // to the walk's rank/predicate cells instead of caching a tuple verdict.
        if(branch.operands.size()==2U)choose_lean_storage<2>(branch,false);
        else choose_lean_storage<6>(branch,false);
    } else if(branch.global)choose_lean_storage<5>(branch,store);
    else choose_lean_storage<3>(branch,store);
}

void run_kept_runs(std::vector<TightBranch> &branches,std::uint32_t rows,
                    std::vector<std::uint64_t> &allowed,std::uint64_t *slow) {
    const auto required=flat_positive_|flat_negative_;
    for(std::uint32_t row=0;row<rows;) {
        CHECK_FOR_INTERRUPTS();target_walk_started_=true;
        const auto end=full_reuse::run_end(run_columns_,row,rows);
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
        if(verdict<0)fail("kept-run formula remained unresolved");
        if(verdict==1)full_reuse::allow_range(allowed,row,end);
        target_evals_+=end-row;CF_COUNT(++run_count_;run_reused_rows_+=end-row-1U);row=end;
    }
}

void run_lean_words(std::vector<TightBranch> &branches,std::uint32_t rows,
                    std::vector<std::uint64_t> &allowed,std::uint64_t *slow) {
    std::array<std::uint64_t,64> ternary{};
    const auto required=flat_positive_|flat_negative_;
    for(std::size_t word=0;word<allowed.size();++word) {
        if((word&63U)==0U)CHECK_FOR_INTERRUPTS();
        target_walk_started_=true;
        const auto base=static_cast<std::uint32_t>(word*64U),size=std::min(64U,rows-base);
        const auto all=size==64U ? UINT64_MAX : (std::uint64_t{1}<<size)-1U;
        std::uint64_t live=all,accepted=0;
        if(branches.size()==1U && branches.front().composed_policy) {
            auto &branch=branches.front();allowed[word]=(this->*branch.loop)(branch,base,all,slow);
            target_evals_+=size;continue;
        }
        if(flat_constant_>=0 && flat_mode_!=FlatFormulaMode::none) {
            allowed[word]=flat_constant_ ? all : 0;target_evals_+=size;continue;
        }
        ternary.fill(0);
        for(auto &branch:branches) {
            const auto leafbit=std::uint64_t{1}<<branch.leaf;
            if(flat_mode_!=FlatFormulaMode::none && !(required&leafbit))continue;
            const auto good=(this->*branch.loop)(branch,base,live,slow);
            if(flat_mode_!=FlatFormulaMode::none) {
                const auto pass=flat_negative_&leafbit ? live&~good : good;
                if(flat_mode_==FlatFormulaMode::conjunction)live&=pass;
                else {accepted|=pass;live&=~pass;}
            } else for(auto bits=live;bits;bits&=bits-1U) {
                const auto offset=__builtin_ctzll(bits);
                const auto bit=std::uint64_t{1}<<offset;
                ternary[offset]+=formula_ternary_powers_[branch.leaf]*((good&bit) ? 2U : 1U);
                const auto verdict=formula_truth_table_[ternary[offset]];
                if(verdict>=0){if(verdict)accepted|=bit;live&=~bit;}
            }
            if(!live)break;
        }
        if(flat_mode_==FlatFormulaMode::conjunction)accepted=live;
        else if(flat_mode_==FlatFormulaMode::none && live)fail("lean formula unresolved");
        allowed[word]=accepted;target_evals_+=size;
    }
}
