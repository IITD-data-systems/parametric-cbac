// Transient block masks and row selections are not decision keys or persistent caches.
std::uint64_t block_branch_arrivals_=0,block_cell_arrivals_=0,block_scalar_arrivals_=0;
std::vector<std::uint32_t> block_misses_;

// Header-only admission: no cache cells or witness rows are read here.
struct BlockCacheFootprint {
    static constexpr std::size_t cell_cap=1U<<20U, byte_cap=4U<<20U;
    std::size_t largest=0,bytes=0;
    bool has_cache=false;
    bool only_packed=true;
    void add(std::size_t cells,std::size_t width,bool packed=false) {
        has_cache|=cells!=0;
        if(cells)only_packed&=packed;
        largest=std::max(largest,cells);
        const auto cost=packed ? cells/4U+unsigned(cells%4U!=0) :
            (cells>SIZE_MAX/width ? SIZE_MAX : cells*width);
        bytes=cost>SIZE_MAX-bytes ? SIZE_MAX : bytes+cost;
    }
    bool block(bool target_only) const {
        return target_only || (has_cache && (largest<=cell_cap || only_packed) && bytes<=byte_cap);
    }
};

BlockCacheFootprint block_cache_footprint(const TightBranch &branch) {
    BlockCacheFootprint out;
    if(branch.composed) {
        for(const auto &use:kept_leaves_[branch.leaf].uses)
            out.add(std::size_t(column(use.root->root).cix.rank_count)+1U,1U,
                    kept_leaves_[branch.leaf].single_root);
        if(!kept_leaves_[branch.leaf].single_root) {
            out.bytes=0;
            for(const auto &use:kept_leaves_[branch.leaf].uses)out.bytes+=use.root->ranks.planned_bytes();
            const auto &plan=chain_plans_[branch.leaf];
            out.bytes+=plan.dense_front.size();
        }
        return out;
    }
    if(branch.projected) {
        const auto &plan=chain_plans_[branch.leaf];
        std::set<const ChainStep *> seen;
        for(const auto &entry:branch.guards) {
            const auto &guard=*entry.guard;
            out.add(std::size_t(guard.cardinality)+1U,guard.state.sparse() ? 32U : 1U);
        }
        for(auto index:branch.indirect_values) {
            const auto &slot=*branch.values[index].slot;
            out.add(std::size_t(slot.cardinality),slot.reached.sparse() ? 32U : 4U);
        }
        for(const auto &end:plan.required_steps)for(auto step=end;step;step=step->parent) {
            if(seen.insert(step.get()).second && step->cache_hop)
                out.add(std::size_t(step->cardinality),step->reached.sparse() ? 32U : 4U);
        }
        if(!plan.dense_front.empty())out.add(plan.dense_front.size()*4U,1U,true);
        else if(!branch.key_single_visit && !plan.direct_residual) {
            std::size_t keys=1;
            for(auto index:plan.key_slots) {
                const auto count=std::size_t(column(plan.slots[index].ref).cix.present_count)+1U;
                keys=keys>BlockCacheFootprint::cell_cap/count ? BlockCacheFootprint::cell_cap+1U : keys*count;
            }
            out.add(keys,32U);
        }
    } else if(!branch.key_single_visit) {
        if(branch.ranked)out.add(std::size_t(branch.null_cell)+1U,branch.sparse ? 32U : 1U,!branch.sparse);
        else if(branch.packed_ranked) {
            std::size_t keys=1;
            for(const auto &stream:branch.operands) {
                // Each stream is a mapped forward column. Only its header is needed.
                std::size_t count=0;
                for(const auto &entry:columns_)if(entry.forward_ranks==stream.rows) {
                    count=std::size_t(entry.cix.present_count)+1U;break;
                }
                if(!count){keys=BlockCacheFootprint::cell_cap+1U;break;}
                keys=keys>BlockCacheFootprint::cell_cap/count ? BlockCacheFootprint::cell_cap+1U : keys*count;
            }
            out.add(keys,32U);
        } else if(branch.global)out.add(1U,5U);
        else if(branch.window)out.add(branch.window->count(),5U);
    }
    return out;
}

// A scalar branch keeps its compiled lean loop, even inside a mixed block plan.
void block_scalar_words(TightBranch &branch,std::uint32_t base,std::uint32_t size,const std::uint64_t *live,
                        std::uint64_t *good,std::uint64_t *scalar,std::uint64_t *,std::uint64_t *slow) {
    for(std::size_t word=0;word<(size+63U)/64U;++word) {
        good[word]=(this->*branch.loop)(branch,base+word*64U,live[word],slow);
        CF_COUNT(scalar[word]|=live[word];block_branch_arrivals_+=__builtin_popcountll(live[word]);
            block_scalar_arrivals_+=__builtin_popcountll(live[word]));
    }
}

std::uint64_t block_atom_mask(const TightBranch::BlockAtom &atom,std::uint32_t base,std::uint64_t live) {
    std::uint64_t result=0;
    const auto *left=atom.left+base;
    const auto *right=atom.right ? atom.right+base : nullptr;
    for(auto bits=live;bits;bits&=bits-1U) {
        const auto offset=static_cast<unsigned>(__builtin_ctzll(bits));
        const auto a=left[offset];if(a==kNullRank)continue;
        bool good=false;
        if(right) {
            const auto b=right[offset];good=b!=kNullRank && compare_rank(a,atom.op,b);
        } else switch(atom.op) {
            case POLICY_OP_EQ:good=a>=atom.lower && a<atom.upper;break;
            case POLICY_OP_NE:good=a<atom.lower || a>=atom.upper;break;
            case POLICY_OP_LT:good=a<atom.lower;break;
            case POLICY_OP_LE:good=a<atom.upper;break;
            case POLICY_OP_GT:good=a>=atom.upper;break;
            case POLICY_OP_GE:good=a>=atom.lower;break;
            default:fail("invalid block target comparison");
        }
        if(good)result|=std::uint64_t{1}<<offset;
    }
    return result;
}

std::uint64_t block_target_filter(TightBranch &branch,std::uint32_t base,std::uint64_t live) {
    if(branch.block_atoms.empty())return live;
    for(std::size_t i=0;i<branch.block_atoms.size();++i)
        branch.block_atom_masks[i]=block_atom_mask(branch.block_atoms[i],base,live);
    auto selected=live;
    for(auto atom:branch.block_conjuncts)selected&=branch.block_atom_masks[atom];
    for(const auto &group:branch.block_groups) {
        std::size_t top=0;
        for(const auto &token:group) {
            if(!token.first)branch.block_stack[top++]=branch.block_atom_masks[token.second];
            else {
                if(top<2U)fail("invalid block target Boolean group");
                const auto right=branch.block_stack[--top];
                if(token.first==1)branch.block_stack[top-1U]&=right;
                else branch.block_stack[top-1U]|=right;
            }
        }
        if(top!=1U)fail("unresolved block target Boolean group");
        selected&=branch.block_stack[0];
    }
    return selected;
}

// A complete local predicate is already decided by the column masks. Do not
// send its passing rows through boundary/projection/general-walk dispatch.
void block_target_only_words(TightBranch &branch,std::uint32_t base,std::uint32_t size,const std::uint64_t *live,
                             std::uint64_t *good,std::uint64_t *,std::uint64_t *,std::uint64_t *) {
    for(std::size_t w=0;w<(size+63U)/64U;++w) {
        good[w]=block_target_filter(branch,base+w*64U,live[w]);
        CF_COUNT(block_branch_arrivals_+=__builtin_popcountll(good[w]));
    }
}

// A speculative probe has no observations, allocations, writes or walk side effects.
// Commit observations only after a complete cached outcome is known.
template<bool Sparse,bool Front>
bool block_projected_probe(TightBranch &branch,std::uint32_t row,bool *truth) {
    auto &plan=chain_plans_[branch.leaf];
    std::size_t guards=0;
    for(auto &entry:branch.guards) {
        auto &guard=*entry.guard;const auto rank=entry.input.local(row);
        const auto key=rank==kNullRank ? guard.cardinality : rank;
        const auto *cell=guard.state.template peek<Sparse>(key);
        if(!cell || !*cell)return false;
        ++guards;
        if(*cell==2U) {
            CF_COUNT(for(std::size_t i=0;i<guards;++i){++branch.guards[i].guard->cache_probes;++branch.guards[i].guard->cache_hits;});
            *truth=false;return true;
        }
    }
    for(auto i:branch.direct_values)branch.resolved[i]=branch.values[i].input.local(row);
    for(auto i:branch.indirect_values) {
        auto &value=branch.values[i];const auto rank=value.input.local(row);
        if(rank==kNullRank){branch.resolved[i]=kNullRank;continue;}
        const auto *cell=value.slot->reached.template peek<Sparse>(rank);
        if(!cell || *cell==kChainUnknown)return false;
        branch.resolved[i]=*cell;
    }
    if constexpr(Front) {
        std::size_t key=0;
        for(std::size_t i=0;i<plan.key_slots.size();++i) {
            const auto rank=branch.resolved[plan.key_slots[i]];
            key+=plan.dense_strides[i]*(rank==kNullRank ? branch.keys[i].null_cell : rank);
        }
        const auto cell=(plan.dense_front[key/4U]>>((key&3U)*2U))&3U;
        if(!cell)return false;
        *truth=cell==1U;
        CF_COUNT(++branch.decision_probes;if(*truth)++branch.good;else ++branch.nogood;);
    } else {
        // The canonical entering-rank verdict is filled by the same walk;
        // there is no speculative private-key decision for a closed Rest.
        if(plan.key_slots.empty())return false;
        RankPredicateInstance instance;const auto rank=branch.resolved[plan.key_slots.front()];
        if(!RankDecisionStore::Key(plan.predicate,plan.key_slots.size()-1,[&](unsigned i,unsigned &value){
            value=branch.resolved[plan.key_slots[i+1]];return true;},instance))return false;
        if(plan.key_slots.size()==1U && rank==kNullRank) {
            if(!plan.null_decision)return false;
            *truth=plan.null_decision==1U;
        } else {
            if(!rank_store_.enabled(instance.id) || !rank_store_.peek(rank,instance,truth))return false;
            if(!rank_store_.lookup(rank,instance,truth))fail("block cached decision disappeared");
        }
    }
    CF_COUNT(for(auto &entry:branch.guards){++entry.guard->cache_probes;++entry.guard->cache_hits;});
    CF_COUNT(for(auto i:branch.indirect_values)if(branch.values[i].input.local(row)!=kNullRank){++branch.values[i].slot->cache_probes;++branch.values[i].slot->cache_hits;});
    return true;
}

template<int Kind,bool Sparse>
bool block_cached(TightBranch &branch,std::uint32_t row,bool *truth) {
    if constexpr(Kind==0 || Kind==4)return block_projected_probe<Sparse,Kind==4>(branch,row,truth);
    else if constexpr(Kind==1) {
        const auto rank=branch.context.local(row),key=rank==kNullRank ? branch.null_cell : rank;
        const auto *packed=branch.rank_cells.template peek<Sparse>(key/4U);
        const auto cell=packed ? (*packed>>((key&3U)*2U))&3U : 0U;
        if(!cell)return false;
        *truth=cell==1U;CF_COUNT(++branch.decision_probes;if(*truth)++branch_good_;else ++branch_nogood_;);
        return true;
    } else if constexpr(Kind==2 || Kind==6) {
        if(!rank_store_.enabled(branch.instance_predicate))return false;
        FusedMemoKey key{};key.width=branch.operands.size();
        for(std::size_t i=0;i<key.width;++i)key.ranks[i]=branch.operands[i].local(row);
        const FusedMemoEntry *cell=nullptr;
        if constexpr(Kind==2)cell=branch.packed_cells.find(std::uint64_t{key.ranks[0]}|(std::uint64_t{key.ranks[1]}<<32U));
        else {
            const auto found=branch.wide_cells.find(key);
            if(found!=branch.wide_cells.end())cell=&found->second;
        }
        if(!cell)return false;
        *truth=cell->truth;rank_store_.observe_range(branch.instance_predicate,true,cell->touch_cost);
        CF_COUNT(++branch.decision_probes;if(*truth)++branch_good_;else ++branch_nogood_;);
        return true;
    } else {
        const auto time=branch.time.local(row);
        if(time==kNullRank){*truth=false;return true;}
        std::size_t key=0;
        if constexpr(Kind!=5) {
            const auto rank=branch.context.local(row);key=rank==kNullRank ? branch.window->count()-1U : rank;
        }
        const auto answer=branch.above ? branch.window_view.probe_window<composed_windows::Shape::lower>(key,time) :
                                        branch.window_view.probe_window<composed_windows::Shape::upper>(key,time);
        if(answer<0)return false;
        *truth=answer==1;
        CF_COUNT(++branch.decision_probes;++branch.boundary_hits;);return true;
    }
}

template<int Kind,bool Store,bool Sparse>
bool block_resolve(TightBranch &branch,std::uint32_t row,std::uint64_t *slow) {
    bindings_[target_node_]=row;
    if constexpr(Kind==0)return lean_projected<Store,Sparse,false>(branch,row);
    else if constexpr(Kind==4)return lean_projected<Store,Sparse,true>(branch,row);
    else if constexpr(Kind==1)return lean_ranked<Store,Sparse>(branch,row,slow);
    else if constexpr(Kind==2)return lean_packed<Store,true>(branch,row,slow);
    else if constexpr(Kind==6)return lean_packed<Store,false>(branch,row,slow);
    else if constexpr(Kind==5)return lean_window<Store,Sparse,true,false>(branch,row,slow);
    else return lean_window<Store,Sparse,false,false>(branch,row,slow);
}

template<int Kind,bool Store,bool Sparse,bool Probe=true>
void block_branch(TightBranch &branch,std::uint32_t base,std::uint32_t size,const std::uint64_t *live,
                  std::uint64_t *good,std::uint64_t *scalar,std::uint64_t *cells,std::uint64_t *slow) {
    const auto words=(size+63U)/64U;block_misses_.clear();
    if constexpr(!Store || !Probe) {
        // Noncacheable arrivals cannot benefit from a worklist or speculative probe.
        for(std::size_t w=0;w<words;++w) {
            const auto selected=block_target_filter(branch,base+w*64U,live[w]);
            CF_COUNT(const auto count=__builtin_popcountll(selected);
                block_branch_arrivals_+=count;block_scalar_arrivals_+=count;scalar[w]|=selected;);
            good[w]=lean_loop<Kind,Store,Sparse,false>(branch,base+w*64U,selected,slow);
        }
        return;
    }
    if constexpr(Kind==5) {
        // One complete global cell is one target-column comparison. Read its
        // state/bound once for this block, never once per target. Empty and
        // partial cells still take the demand walk below.
        if(branch.window_view.allocated()) {
            const auto state=branch.window_view.state(0);
            if(state==1U || state==2U) {
                const auto boundary=state==2U ? (branch.above ?
                    branch.window_view.template bound<composed_windows::Shape::lower>(0) :
                    branch.window_view.template bound<composed_windows::Shape::upper>(0)) : 0U;
                const typename TightBranch::BlockAtom atom{branch.time.rows,nullptr,
                    branch.above ? POLICY_OP_GE : POLICY_OP_LT,boundary,boundary};
                for(std::size_t w=0;w<words;++w) {
                    const auto selected=block_target_filter(branch,base+w*64U,live[w]);
                    good[w]=state==1U ? 0U : block_atom_mask(atom,base+w*64U,selected);
                    CF_COUNT(const auto count=__builtin_popcountll(selected);
                        block_branch_arrivals_+=count;block_cell_arrivals_+=count;cells[w]|=selected;
                        auto valid=atom;valid.op=POLICY_OP_GE;valid.lower=0;valid.upper=0;
                        const auto probes=__builtin_popcountll(block_atom_mask(valid,base+w*64U,selected));
                        branch.decision_probes+=probes;branch.boundary_hits+=probes;);
                }
                ++global_window_complete_blocks_;
                return;
            }
        }
    }
    if constexpr(Kind==3 || Kind==5) {
        // Before the first Record there is no state buffer to gather from.
        // This choice is per block, not a states_.empty() test on every row.
        if(!branch.window_view.allocated()) {
            for(std::size_t w=0;w<words;++w) {
                const auto selected=block_target_filter(branch,base+w*64U,live[w]);good[w]=0;
                CF_COUNT(block_branch_arrivals_+=__builtin_popcountll(selected));
                for(auto bits=selected;bits;bits&=bits-1U)
                    block_misses_.push_back(base+w*64U+unsigned(__builtin_ctzll(bits)));
            }
        }
    }
    const bool gather=!(Kind==3 || Kind==5) || branch.window_view.allocated();
    if(gather)
    for(std::size_t word=0;word<words;++word) {
        const auto selected=block_target_filter(branch,base+word*64U,live[word]);good[word]=0;
        CF_COUNT(block_branch_arrivals_+=__builtin_popcountll(selected));
        for(auto bits=selected;bits;bits&=bits-1U) {
            const auto offset=static_cast<unsigned>(__builtin_ctzll(bits));
            const auto row=base+static_cast<std::uint32_t>(word*64U)+offset;
            const auto bit=std::uint64_t{1}<<offset;
            bool truth=false;
            if constexpr(Store && Probe) {
                if(block_cached<Kind,Sparse>(branch,row,&truth)) {
                    CF_COUNT(cells[word]|=bit;++block_cell_arrivals_);
                    if(truth)good[word]|=bit;
                    continue;
                }
            }
            block_misses_.push_back(row);
        }
    }
    // Reprobe unresolved instances: an earlier miss may have filled the same key.
    // No row id is stored in any decision table; this vector is only this block's worklist.
    for(auto row:block_misses_) {
        const auto local=row-base,word=local/64U;const auto bit=std::uint64_t{1}<<(local&63U);
        bool truth=false;
        if constexpr(Store && Probe) {
            if((!(Kind==3 || Kind==5) || branch.window_view.allocated()) && block_cached<Kind,Sparse>(branch,row,&truth)) {
                CF_COUNT(cells[word]|=bit;++block_cell_arrivals_);
                if(truth)good[word]|=bit;
                continue;
            }
        }
        truth=block_resolve<Kind,Store,Sparse>(branch,row,slow);
        CF_COUNT(scalar[word]|=bit;++block_scalar_arrivals_);
        if(truth)good[word]|=bit;
    }
}

// Column-at-a-time gathers for projected dense decisions. Hops are resolved only
// by the scalar miss path, preserving its shared-step reuse and endpoint keys.
template<bool Sparse>
void block_projected_front(TightBranch &branch,std::uint32_t base,std::uint32_t size,const std::uint64_t *live,
                           std::uint64_t *good,std::uint64_t *scalar,std::uint64_t *cells,std::uint64_t *slow) {
    const auto words=(size+63U)/64U;auto &plan=chain_plans_[branch.leaf];
    std::vector<std::uint64_t> selected(words),ready(words),answered(words,0U);
    for(std::size_t w=0;w<words;++w) {
        selected[w]=ready[w]=block_target_filter(branch,base+w*64U,live[w]);good[w]=0;
        CF_COUNT(block_branch_arrivals_+=__builtin_popcountll(selected[w]));
    }
    for(std::size_t g=0;g<branch.guards.size();++g) {
        auto &entry=branch.guards[g];auto &guard=*entry.guard;
        for(std::size_t w=0;w<words;++w) {
            std::uint64_t passed=0,failed=0;const auto *ranks=entry.input.rows+base+w*64U;
            for(auto bits=ready[w];bits;bits&=bits-1U) {
                const auto i=static_cast<unsigned>(__builtin_ctzll(bits));const auto rank=ranks[i];
                const auto *cell=guard.state.template peek<Sparse>(rank==kNullRank ? guard.cardinality : rank);
                if(cell && *cell==1U)passed|=std::uint64_t{1}<<i;
                else if(cell && *cell==2U)failed|=std::uint64_t{1}<<i;
            }
            ready[w]=passed;answered[w]|=failed;
            CF_COUNT(cells[w]|=failed;const auto count=__builtin_popcountll(failed);block_cell_arrivals_+=count;
                for(std::size_t j=0;j<=g;++j){branch.guards[j].guard->cache_probes+=count;branch.guards[j].guard->cache_hits+=count;});
        }
    }
    if(branch.block_resolved.empty())branch.block_resolved.resize(branch.values.size());
    for(auto slot_index:branch.indirect_values) {
        auto &value=branch.values[slot_index];auto &endpoints=branch.block_resolved[slot_index];
        if(endpoints.size()<size)endpoints.resize(size);
        for(std::size_t w=0;w<words;++w) {
            std::uint64_t known=0;const auto *ranks=value.input.rows+base+w*64U;
            for(auto bits=ready[w];bits;bits&=bits-1U) {
                const auto i=static_cast<unsigned>(__builtin_ctzll(bits));const auto rank=ranks[i];
                if(rank==kNullRank){endpoints[w*64U+i]=kNullRank;known|=std::uint64_t{1}<<i;continue;}
                const auto *cell=value.slot->reached.template peek<Sparse>(rank);
                if(cell && *cell!=kChainUnknown){endpoints[w*64U+i]=*cell;known|=std::uint64_t{1}<<i;}
            }
            ready[w]=known;
        }
    }
    for(std::size_t w=0;w<words;++w) {
        std::uint64_t hit=0;std::uint64_t yes=0;
        for(auto bits=ready[w];bits;bits&=bits-1U) {
            const auto i=static_cast<unsigned>(__builtin_ctzll(bits));const auto row=w*64U+i;
            std::size_t key=0;
            for(std::size_t k=0;k<plan.key_slots.size();++k) {
                const auto slot=plan.key_slots[k];const auto &value=branch.values[slot];
                const auto rank=value.slot->direct ? value.input.rows[base+row] : branch.block_resolved[slot][row];
                key+=plan.dense_strides[k]*(rank==kNullRank ? branch.keys[k].null_cell : rank);
            }
            const auto cell=(plan.dense_front[key/4U]>>((key&3U)*2U))&3U;
            if(cell){hit|=std::uint64_t{1}<<i;if(cell==1U)yes|=std::uint64_t{1}<<i;}
        }
        answered[w]|=hit;good[w]|=yes;
        CF_COUNT(cells[w]|=hit;const auto count=__builtin_popcountll(hit);block_cell_arrivals_+=count;
            branch.decision_probes+=count;branch.good+=__builtin_popcountll(yes);branch.nogood+=count-__builtin_popcountll(yes);
            for(auto &entry:branch.guards){entry.guard->cache_probes+=count;entry.guard->cache_hits+=count;});
        CF_COUNT(for(auto slot:branch.indirect_values)for(auto bits=hit;bits;bits&=bits-1U) {
            const auto i=static_cast<unsigned>(__builtin_ctzll(bits));
            if(branch.values[slot].input.rows[base+w*64U+i]!=kNullRank){++branch.values[slot].slot->cache_probes;++branch.values[slot].slot->cache_hits;}
        });
    }
    // Build only the selected, unresolved arrivals, preserving target row order.
    block_misses_.clear();
    for(std::size_t w=0;w<words;++w)for(auto bits=selected[w]&~answered[w];bits;bits&=bits-1U)
        block_misses_.push_back(base+static_cast<std::uint32_t>(w*64U)+__builtin_ctzll(bits));
    for(auto row:block_misses_) {
        const auto offset=row-base,w=offset/64U;const auto bit=std::uint64_t{1}<<(offset&63U);bool truth=false;
        if(block_projected_probe<Sparse,true>(branch,row,&truth)) {
            CF_COUNT(cells[w]|=bit;++block_cell_arrivals_);if(truth)good[w]|=bit;continue;
        }
        bindings_[target_node_]=row;truth=lean_projected<true,Sparse,true>(branch,row);
        CF_COUNT(scalar[w]|=bit;++block_scalar_arrivals_);if(truth)good[w]|=bit;
    }
}

template<int Kind> void choose_block_storage(TightBranch &branch,bool store,bool probe=true) {
    if constexpr(Kind==4)if(store && probe) {
        branch.block_loop=branch.sparse ? &FusedWalkRuntime::block_projected_front<true> : &FusedWalkRuntime::block_projected_front<false>;
        return;
    }
    if(store && !probe)branch.block_loop=branch.sparse ? &FusedWalkRuntime::block_branch<Kind,true,true,false> : &FusedWalkRuntime::block_branch<Kind,true,false,false>;
    else if(store)branch.block_loop=branch.sparse ? &FusedWalkRuntime::block_branch<Kind,true,true> : &FusedWalkRuntime::block_branch<Kind,true,false>;
    else branch.block_loop=branch.sparse ? &FusedWalkRuntime::block_branch<Kind,false,true> : &FusedWalkRuntime::block_branch<Kind,false,false>;
}

void compile_block_branch(TightBranch &branch) {
    std::map<const NormalizedAtom *,std::size_t> atoms;
    const auto add=[&](const NormalizedAtom *atom) {
        auto found=atoms.find(atom);if(found!=atoms.end())return found->second;
        if(atom->left.node_id!=target_node_ || (!atom->right_is_const && atom->right.node_id!=target_node_))
            fail("block target filter depends on a witness binding");
        TightBranch::BlockAtom compiled;
        compiled.left=column(atom->left).forward_ranks;compiled.op=atom->op;
        if(!compiled.left)fail("block target forward column missing");
        if(atom->right_is_const) {
            if(!atom->constant_compiled)fail("block target constant was not placed in its universe");
            compiled.lower=atom->constant_lower;compiled.upper=atom->constant_upper;
        } else {
            if(column(atom->left).domain!=column(atom->right).domain)fail("block filter crosses universes");
            compiled.right=column(atom->right).forward_ranks;
            if(!compiled.right)fail("block target right forward column missing");
        }
        const auto index=branch.block_atoms.size();atoms.emplace(atom,index);branch.block_atoms.push_back(compiled);return index;
    };
    for(auto atom:dag_[0].filters_by_leaf[branch.leaf])branch.block_conjuncts.push_back(add(atom));
    std::size_t stack=1;
    for(const auto *group:dag_[0].boolean_groups_by_leaf[branch.leaf]) {
        std::vector<std::pair<int,std::size_t>> tokens;
        for(const auto &token:group->postfix) {
            if(token.kind==LocalBooleanTokenKind::atom)tokens.emplace_back(0,add(token.atom));
            else tokens.emplace_back(token.kind==LocalBooleanTokenKind::conjunction ? 1 : 2,0U);
        }
        stack=std::max(stack,tokens.size());branch.block_groups.push_back(std::move(tokens));
    }
    branch.block_stack.resize(stack);branch.block_atom_masks.resize(branch.block_atoms.size());
    branch.block_target_only=true;
    for(auto child:dag_[0].children)
        if(dag_[child].leaves&(std::uint64_t{1}<<branch.leaf))branch.block_target_only=false;
    const auto outside=[&](const NormalizedAtom *atom) {
        return atom->left.node_id!=target_node_ || (!atom->right_is_const && atom->right.node_id!=target_node_);
    };
    for(auto atom:leaves_[branch.leaf]->atoms)if(outside(atom))branch.block_target_only=false;
    for(const auto &group:leaves_[branch.leaf]->boolean_groups)
        for(auto atom:group.atoms)if(outside(atom))branch.block_target_only=false;
    const auto footprint=block_cache_footprint(branch);
    branch.block_planned_cells=footprint.largest;branch.block_planned_bytes=footprint.bytes;
    branch.block_batched=footprint.block(branch.block_target_only);
    if(branch.block_target_only) {
        branch.block_loop=&FusedWalkRuntime::block_target_only_words;
        return;
    }
    if(branch.composed) {
        // The compiled kept-verdict/endpoint loop is already a compact gather.
        // Keep it inside the original block driver, including target masking,
        // branch order and row-wise short circuiting; do not scalarize targets.
        branch.block_loop=&FusedWalkRuntime::block_scalar_words;
        return;
    }
    if(!branch.block_batched) {
        branch.block_loop=&FusedWalkRuntime::block_scalar_words;
        return;
    }
    const bool store=!branch.key_single_visit;
    if(branch.projected) {
        const auto &plan=chain_plans_[branch.leaf];
        const bool cache=store && !plan.direct_residual && branch.direct_guards.empty() && branch.uncached_values.empty();
        if(plan.dense_front.empty())choose_block_storage<0>(branch,store && !plan.direct_residual,cache);
        else choose_block_storage<4>(branch,store && !plan.direct_residual,cache);
    } else if(branch.ranked)choose_block_storage<1>(branch,store);
    else if(branch.packed_ranked) {
        if(branch.operands.size()==2U)choose_block_storage<2>(branch,store);
        else choose_block_storage<6>(branch,store);
    } else if(branch.global)choose_block_storage<5>(branch,store);
    else choose_block_storage<3>(branch,store);
}

std::uint64_t run_lean_branch(TightBranch &branch,std::uint32_t base,std::uint64_t live,std::uint64_t *slow) {
    const auto size=std::min(64U,branch.run_rows-base);
    auto &runs=branch.runs;const bool linked=runs.next_base==base;
    const auto same=full_reuse::RunBlock::equal_word(branch.run_columns,base,size,linked);
    bool seen=false;
    const auto selected=full_reuse::RunBlock::heads(live,same,linked && runs.seen_carry,&seen);
    const auto saved=__builtin_popcountll(live)-__builtin_popcountll(selected);
    const auto answers=(this->*branch.row_loop)(branch,base,selected,slow);
    const auto good=full_reuse::RunBlock::spread(answers,same,linked && runs.good_carry);
    runs.seen_carry=seen;runs.good_carry=(good>>63U)!=0;runs.next_base=base+size;
    runs.observe(size,saved);if(runs.disabled)branch.loop=branch.row_loop;
    CF_COUNT(if(branch.composed_policy)composed_credit_runs(branch,base,size,live,selected););
    CF_COUNT(run_rows_saved_+=saved);return good&live;
}

void run_block_branch(TightBranch &branch,std::uint32_t base,std::uint32_t size,const std::uint64_t *live,
                      std::uint64_t *good,std::uint64_t *scalar,std::uint64_t *cells,std::uint64_t *slow) {
    auto &runs=branch.runs;const auto words=(size+63U)/64U;
    const bool linked=runs.next_base==base;
    bool seen=linked && runs.seen_carry;std::uint32_t saved=0;
    runs.equal_masks.resize(words);runs.selected.resize(words);runs.answers.assign(words,0);
    for(std::uint32_t w=0;w<words;++w) {
        const auto count=std::min(64U,size-w*64U);
        const auto same=full_reuse::RunBlock::equal_word(branch.run_columns,base+w*64U,count,linked || w);
        runs.equal_masks[w]=same;
        runs.selected[w]=full_reuse::RunBlock::heads(live[w],same,seen,&seen);
        saved+=__builtin_popcountll(live[w])-__builtin_popcountll(runs.selected[w]);
    }
    const auto wrapper=branch.loop;branch.loop=branch.row_loop;
    (this->*branch.base_block_loop)(branch,base,size,runs.selected.data(),runs.answers.data(),scalar,cells,slow);
    bool carry=linked && runs.good_carry;
    for(std::uint32_t w=0;w<words;++w) {
        const auto answer=full_reuse::RunBlock::spread(runs.answers[w],runs.equal_masks[w],carry);
        good[w]=answer&live[w];carry=(answer>>63U)!=0;
        CF_COUNT(if(branch.composed_policy)composed_credit_runs(branch,base+w*64U,std::min(64U,size-w*64U),live[w],runs.selected[w]););
    }
    runs.next_base=base+size;runs.seen_carry=seen;runs.good_carry=carry;
    runs.observe(size,saved);
    if(runs.disabled)branch.block_loop=branch.base_block_loop;
    if(!branch.runs.disabled)branch.loop=wrapper;
    CF_COUNT(run_rows_saved_+=saved);
}

void compile_branch_runs(TightBranch &branch) {
    bool witness=false;
    for(auto child:dag_[0].children)witness|=(dag_[child].leaves&(std::uint64_t{1}<<branch.leaf))!=0;
    // Target-only scans already have zero-probe vector/word loops. Run detection
    // cannot save any walk or chain work for these branches.
    if(!witness)return;
    std::map<std::size_t,ColumnRef> refs;
    const auto collect=[&](const NormalizedAtom *atom) {
        if(atom->left.node_id==target_node_)refs.emplace(atom->left.runtime_column,atom->left);
        if(!atom->right_is_const && atom->right.node_id==target_node_)refs.emplace(atom->right.runtime_column,atom->right);
    };
    for(auto atom:leaves_[branch.leaf]->atoms)collect(atom);
    for(const auto &group:leaves_[branch.leaf]->boolean_groups)for(auto atom:group.atoms)collect(atom);
    if(refs.empty())return;
    for(const auto &ref:refs)branch.run_columns.push_back(column(ref.second).forward_ranks);
    branch.run_rows=column(refs.begin()->second).cix.row_count;
    branch.row_loop=branch.loop;branch.loop=&FusedWalkRuntime::run_lean_branch;
    if(branch.block_loop){branch.base_block_loop=branch.block_loop;branch.block_loop=&FusedWalkRuntime::run_block_branch;}
}

void run_block_words(std::vector<TightBranch> &branches,std::uint32_t rows,
                     std::vector<std::uint64_t> &allowed,std::uint64_t *slow) {
    if(cf_block_target_rows%64)fail("block size must be a multiple of 64");
    const auto block=static_cast<std::uint32_t>(cf_block_target_rows),capacity=block/64U;
    std::vector<std::uint64_t> live(capacity),accepted(capacity),good(capacity),scalar,cells,ternary(block);
    CF_COUNT(scalar.resize(capacity);cells.resize(capacity));
    block_misses_.reserve(block);
    std::uint64_t scalar_rows=0,cell_rows=0,filter_only_rows=0;
    const auto required=flat_positive_|flat_negative_;
    for(std::uint32_t base=0;base<rows;base+=std::min(block,rows-base)) {
        CHECK_FOR_INTERRUPTS();target_walk_started_=true;
        const auto size=std::min(block,rows-base),words=(size+63U)/64U;
        std::fill(live.begin(),live.end(),UINT64_MAX);
        if(size%64U)live[words-1U]=(std::uint64_t{1}<<(size%64U))-1U;
        std::fill(accepted.begin(),accepted.end(),0U);
        CF_COUNT(std::fill(scalar.begin(),scalar.end(),0U);std::fill(cells.begin(),cells.end(),0U));
        std::fill(ternary.begin(),ternary.end(),0U);
        if(branches.size()==1U && branches.front().composed_policy) {
            auto &branch=branches.front();
            (this->*branch.block_loop)(branch,base,size,live.data(),good.data(),scalar.data(),cells.data(),slow);
            for(std::size_t word=0;word<words;++word) {
                allowed[base/64U+word]=good[word];
                CF_COUNT(scalar_rows+=__builtin_popcountll(scalar[word]);cell_rows+=__builtin_popcountll(cells[word]&~scalar[word]));
            }
            target_evals_+=size;continue;
        }
        if(flat_constant_>=0 && flat_mode_!=FlatFormulaMode::none) {
            for(std::size_t word=0;word<words;++word)allowed[base/64U+word]=flat_constant_ ? live[word] : 0;
            target_evals_+=size;CF_COUNT(filter_only_rows+=size);continue;
        }
        for(auto &branch:branches) {
            const auto leafbit=std::uint64_t{1}<<branch.leaf;
            if(flat_mode_!=FlatFormulaMode::none && !(required&leafbit))continue;
            (this->*branch.block_loop)(branch,base,size,live.data(),good.data(),scalar.data(),cells.data(),slow);
            bool remaining=false;
            for(std::size_t word=0;word<words;++word) {
                if(flat_mode_!=FlatFormulaMode::none) {
                    const auto pass=flat_negative_&leafbit ? live[word]&~good[word] : good[word];
                    if(flat_mode_==FlatFormulaMode::conjunction)live[word]&=pass;
                    else {accepted[word]|=pass;live[word]&=~pass;}
                } else for(auto bits=live[word];bits;bits&=bits-1U) {
                    const auto offset=static_cast<unsigned>(__builtin_ctzll(bits));
                    const auto bit=std::uint64_t{1}<<offset;auto &state=ternary[word*64U+offset];
                    state+=formula_ternary_powers_[branch.leaf]*((good[word]&bit) ? 2U : 1U);
                    const auto verdict=formula_truth_table_[state];
                    if(verdict>=0){if(verdict)accepted[word]|=bit;live[word]&=~bit;}
                }
                remaining|=live[word]!=0U;
            }
            if(!remaining)break;
        }
        for(std::size_t word=0;word<words;++word) {
            if(flat_mode_==FlatFormulaMode::conjunction)accepted[word]=live[word];
            else if(flat_mode_==FlatFormulaMode::none && live[word])fail("block formula unresolved");
            allowed[base/64U+word]=accepted[word];
            CF_COUNT(scalar_rows+=__builtin_popcountll(scalar[word]);
                cell_rows+=__builtin_popcountll(cells[word]&~scalar[word]));
        }
        target_evals_+=size;
    }
    cf_perf_metric_set("block_loop_used",1);cf_perf_metric_set("block_target_rows",block);
    CF_COUNT(filter_only_rows=rows-scalar_rows-cell_rows;
        cf_perf_metric_set("block_branch_arrivals",block_branch_arrivals_);
        cf_perf_metric_set("block_cell_arrivals",block_cell_arrivals_);cf_perf_metric_set("block_scalar_arrivals",block_scalar_arrivals_);
        cf_perf_metric_set("block_rows_scalar",scalar_rows);cf_perf_metric_set("block_rows_cells",cell_rows);
        cf_perf_metric_set("block_rows_filter_only",filter_only_rows));
}

// When every leaf reads the same target rank, keep the original full-formula
// two-bit cells and batch their probes. This does not create a row-keyed cache.
void run_block_formula(std::uint32_t rows,std::vector<std::uint64_t> &allowed,
                       std::vector<std::uint8_t> &cells,const TightStream &stream,std::uint32_t null_key) {
    if(cf_block_target_rows%64)fail("formula block size must be a multiple of 64");
    const auto block=static_cast<std::uint32_t>(cf_block_target_rows);
    std::vector<std::uint32_t> misses;misses.reserve(block);
    std::uint64_t scalar=0,hit_good=0,hit_bad=0;
    for(std::uint32_t base=0;base<rows;base+=std::min(block,rows-base)) {
        CHECK_FOR_INTERRUPTS();target_walk_started_=true;misses.clear();
        const auto end=base+std::min(block,rows-base);
        for(auto row=base;row<end;++row) {
            const auto rank=stream.local(row),key=rank==kNullRank ? null_key : rank;
            const auto cell=(cells[key/4U]>>((key&3U)*2U))&3U;
            if(!cell){misses.push_back(row);continue;}
            if(cell==1U){allowed[row/64U]|=std::uint64_t{1}<<(row&63U);CF_COUNT(++hit_good);}
            else CF_COUNT(++hit_bad);
        }
        for(auto row:misses) {
            const auto rank=stream.local(row),key=rank==kNullRank ? null_key : rank;
            const auto shift=(key&3U)*2U;auto &packed=cells[key/4U];auto cell=(packed>>shift)&3U;
            if(!cell) {
                const bool truth=evaluate_target(row);cell=truth ? 1U : 2U;
                packed|=cell<<shift;++scalar;CF_COUNT(++formula_rank_entries_);
            } else {CF_COUNT(if(cell==1U)++hit_good;else ++hit_bad);}
            if(cell==1U)allowed[row/64U]|=std::uint64_t{1}<<(row&63U);
        }
    }
    // evaluate_target already counted the misses; count the remaining rows once.
    target_evals_+=rows-scalar;
    CF_COUNT(formula_good_+=hit_good;formula_nogood_+=hit_bad;);
    cf_perf_metric_set("block_loop_used",1);cf_perf_metric_set("block_target_rows",block);
    CF_COUNT(cf_perf_metric_set("block_branch_arrivals",rows);cf_perf_metric_set("block_cell_arrivals",hit_good+hit_bad);
        cf_perf_metric_set("block_scalar_arrivals",scalar);cf_perf_metric_set("block_rows_scalar",scalar);
        cf_perf_metric_set("block_rows_cells",hit_good+hit_bad);cf_perf_metric_set("block_rows_filter_only",0));
}
