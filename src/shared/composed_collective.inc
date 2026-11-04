// The all-functional strategy batches requests at a shared ROOT connection.
// Misses still extend only the asking request through the demand bound walk.
// No rank, row, predicate result or qualifying set is prepared ahead of arrival.
void configure_collective_roots() {
    if(!cf_decision_sharing || !composed_bound_program_)return;
    for(const auto &leaf:composed_bound_leaves_)for(auto root:leaf.nodes[0].children)
        if(!leaf.nodes[root].functional_tail)return;
    std::map<std::size_t,std::size_t> inputs;
    const auto input=[&](const ColumnRef &ref) {
        auto [it,inserted]=inputs.emplace(ref.runtime_column,inputs.size());
        if(inserted)collective_inputs_.push_back(column(ref).forward_ranks);
        return it->second;
    };
    const auto count=composed_bound_leaves_.size();
    collective_target_atoms_.resize(count);collective_target_groups_.resize(count);collective_conjuncts_.resize(count);
    std::map<const BoundConnection*,std::size_t> groups;
    for(std::size_t l=0;l<count;++l) {
        const auto &leaf=composed_bound_leaves_[l];
        const auto atom=[&](const NormalizedAtom *a) {
            const auto id=collective_target_atoms_[l].size();
            collective_target_atoms_[l].push_back({a,input(a->left),a->right_is_const ? SIZE_MAX : input(a->right)});
            return id;
        };
        for(auto a:leaf.target_atoms)collective_conjuncts_[l].push_back(atom(a));
        for(auto group:leaf.target_groups) {
            std::vector<std::pair<int,std::size_t>> program;
            for(const auto &tok:group->postfix) {
                if(tok.kind==LocalBooleanTokenKind::atom)program.push_back({0,atom(tok.atom)});
                else program.push_back({tok.kind==LocalBooleanTokenKind::conjunction ? 1 : 2,0});
            }
            if(group->postfix.empty())for(auto a:group->atoms) {
                program.push_back({0,atom(a)});if(program.size()>1U)program.push_back({2,0});
            }
            collective_target_stack_.resize(std::max(collective_target_stack_.size(),program.size()));
            collective_target_groups_[l].push_back(std::move(program));
        }
        for(auto root:leaf.nodes[0].children) {
            const auto &node=leaf.nodes[root];auto [it,inserted]=groups.emplace(node.connection.get(),groups.size());
            if(inserted) {
                collective_roots_.emplace_back();auto &g=collective_roots_.back();g.connection=node.connection;
                for(const auto &e:node.connection->entries)g.sources.push_back(input(e.source));
            }
            auto &g=collective_roots_[it->second];const auto bit=std::uint64_t{1}<<l;
            if(g.branches&bit){collective_roots_.clear();return;} // private activations, unchanged strategy
            g.branches|=bit;g.requests.push_back({l,root,node.has_probe ? input(node.probe) : SIZE_MAX});
        }
    }
    for(auto &g:collective_roots_) {
        std::map<std::pair<const composed_windows::Cells*,std::size_t>,std::size_t> slots;
        for(std::size_t i=0;i<g.requests.size();++i) {
            auto &entry=g.requests[i];const auto &node=composed_bound_leaves_[entry.leaf].nodes[entry.node];
            auto [it,inserted]=slots.emplace(std::make_pair(node.cells.data.get(),entry.probe),slots.size());
            if(inserted){g.comparisons.push_back(i);g.comparison_requests.push_back(0);}
            entry.comparison=it->second;g.comparison_requests[entry.comparison]|=std::uint64_t{1}<<entry.leaf;
        }
    }
    collective_values_.resize(collective_inputs_.size());collective_composed_program_=true;
}

bool collective_target_atom(const CollectiveAtom &entry)const {
    const auto &a=*entry.atom;const auto left=collective_values_[entry.left];if(left==kNullRank)return false;
    if(entry.right!=SIZE_MAX) {
        const auto right=collective_values_[entry.right];if(right==kNullRank)return false;
        switch(a.op) {
            case POLICY_OP_EQ:return left==right;case POLICY_OP_NE:return left!=right;
            case POLICY_OP_LT:return left<right;case POLICY_OP_LE:return left<=right;
            case POLICY_OP_GT:return left>right;case POLICY_OP_GE:return left>=right;
        }
    } else switch(a.op) {
        case POLICY_OP_EQ:return left>=a.constant_lower && left<a.constant_upper;
        case POLICY_OP_NE:return left<a.constant_lower || left>=a.constant_upper;
        case POLICY_OP_LT:return left<a.constant_lower;case POLICY_OP_LE:return left<a.constant_upper;
        case POLICY_OP_GT:return left>=a.constant_upper;case POLICY_OP_GE:return left>=a.constant_lower;
    }
    fail("invalid collective target operator");
}

bool collective_target_filter(std::size_t leaf) {
    const auto &atoms=collective_target_atoms_[leaf];
    for(auto a:collective_conjuncts_[leaf])if(!collective_target_atom(atoms[a]))return false;
    for(const auto &group:collective_target_groups_[leaf]) {
        std::size_t top=0;
        for(const auto &tok:group) {
            if(!tok.first)collective_target_stack_[top++]=collective_target_atom(atoms[tok.second]);
            else {
                if(top<2U)fail("invalid collective target Boolean group");
                const auto right=collective_target_stack_[--top];
                collective_target_stack_[top-1U]=tok.first==1 ? collective_target_stack_[top-1U]&&right : collective_target_stack_[top-1U]||right;
            }
        }
        if(top!=1U || !collective_target_stack_[0])return false;
    }
    return true;
}

bool composed_collective_truth(std::uint32_t row,bool *supported) {
    bindings_[target_node_]=row;composed_formula_.begin();
    for(std::size_t i=0;i<collective_inputs_.size();++i)collective_values_[i]=collective_inputs_[i][row];
    CF_COUNT(collective_input_reads_+=collective_inputs_.size(););
    std::array<unsigned,64> pending{};
    for(unsigned l=0;l<composed_bound_leaves_.size();++l) {
        if(!(composed_formula_.needed()&(std::uint64_t{1}<<l)))continue;
        auto &leaf=composed_bound_leaves_[l];CF_COUNT(++leaf.arrivals);
        pending[l]=leaf.nodes[0].children.size();
        if(!collective_target_filter(l)){CF_COUNT(++leaf.target_filtered);composed_last_cause_=SIZE_MAX;composed_formula_.settle(l,false);}
        else if(!pending[l]){CF_COUNT(++leaf.body_passes);composed_last_cause_=SIZE_MAX;composed_formula_.settle(l,true);}
    }
    const auto deliver=[&](unsigned leaf,bool good,std::size_t cause) {
        if(!(composed_formula_.needed()&(std::uint64_t{1}<<leaf)))return;
        if(!good || !--pending[leaf]) {
            if(good)CF_COUNT(++composed_bound_leaves_[leaf].body_passes);
            composed_last_cause_=cause;composed_formula_.settle(leaf,good);
        }
    };
    for(auto &group:collective_roots_) {
        auto requests=group.branches&composed_formula_.needed();if(!requests)continue;
        auto &conn=*group.connection;
        CF_COUNT(for(const auto &entry:group.requests)if(requests&(std::uint64_t{1}<<entry.leaf))
            ++composed_bound_leaves_[entry.leaf].root_reads;);
        for(const auto &entry:group.requests)if((requests&(std::uint64_t{1}<<entry.leaf)) &&
            entry.probe!=SIZE_MAX && collective_values_[entry.probe]==kNullRank) {
            deliver(entry.leaf,false,composed_bound_leaves_[entry.leaf].nodes[entry.node].shared_group);
        }
        requests&=composed_formula_.needed();if(!requests)continue;
        if(conn.parent_row!=row) {
            conn.parent_row=row;conn.resolved_parent=kNullRank;conn.resolved_row=kNullRank;
            conn.rank=collective_values_[group.sources[0]];conn.begin=conn.end=0;conn.match={};CF_COUNT(++conn.rank_reads);
        }
        if(conn.rank!=kNullRank && conn.entries.size()>1U)bound_resolve(conn,row);
        if(conn.rank==kNullRank || (conn.entries.size()>1U && !conn.match.count)) {
            for(const auto &entry:group.requests)if(requests&(std::uint64_t{1}<<entry.leaf))
                deliver(entry.leaf,false,composed_bound_leaves_[entry.leaf].nodes[entry.node].shared_group);
            continue;
        }
        if(conn.entries.size()>1U && conn.match.count!=1U){*supported=false;return false;}
        const auto key=conn.entries.size()>1U ? conn.match.position : conn.rank;
        const auto bank=composed_bound_leaves_[group.requests.front().leaf].nodes[group.requests.front().node].cells.data->rank_major();
        const auto record=bank ? bank->record(key) : nullptr;
        std::array<int,64> answers{};bool all_hit=true;
        CF_COUNT(++bound_probes_;++collective_record_probes_;);
        // One rank/record access, with an independent comparison per live Rest.
        for(std::size_t comparison=0;comparison<group.comparisons.size();++comparison)if(requests&group.comparison_requests[comparison]) {
            const auto &entry=group.requests[group.comparisons[comparison]];
            auto &node=composed_bound_leaves_[entry.leaf].nodes[entry.node];
            const auto value=entry.probe==SIZE_MAX ? 0U : collective_values_[entry.probe];
            answers[comparison]=node.cells.data->probe_record(key,value,record);all_hit &= answers[comparison]>=0;
            CF_COUNT(++collective_slot_checks_;++bound_slot_checks_;);
        }
        CF_COUNT(if(all_hit)++bound_hits_;);
        for(const auto &entry:group.requests) {
            const auto bit=std::uint64_t{1}<<entry.leaf;if(!(requests&composed_formula_.needed()&bit))continue;
            auto &leaf=composed_bound_leaves_[entry.leaf];auto &node=leaf.nodes[entry.node];
            bool good;auto cause=node.shared_group;
            if(answers[entry.comparison]>=0) {
                good=answers[entry.comparison]==1;
                CF_COUNT(++node.probes;++node.hits;++node.arrivals;++node.functional_requests;++node.dense_gathers;
                    if(node.has_probe)++node.point_requests;else ++node.full_requests;
                    if(node.counter_target!=row){node.counter_target=row;++node.undecided_target_rows;});
            } else {
                const auto value=entry.probe==SIZE_MAX ? 0U : collective_values_[entry.probe];
                auto answer=composed_node_bound(leaf,entry.node,node.has_probe,value,true);
                if(!answer.supported){*supported=false;return false;}
                good=answer.covers(value);cause=composed_last_cause_;
                answers[entry.comparison]=good; // same Rest AND same probe, before polarity
            }
            deliver(entry.leaf,good,cause);
        }
        if(composed_formula_.value()>=0)break;
    }
    if(composed_formula_.value()<0)fail("collective formula remained unresolved");
    CF_COUNT(composed_formula_updates_+=composed_formula_.updates(););
    return composed_formula_.value()==1;
}
