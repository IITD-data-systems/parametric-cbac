// One connection node, a set of asking requests, and one slice iterator.
// Frames and routing are allocated at planning time; ranks/windows are filled
// only by target arrivals. The unsplit formula owns all stopping decisions.
std::string shared_bound_atom_identity(const NormalizedAtom &atom,const ComposedNode &node)const {
    const auto ref=[&](const ColumnRef &r) {
        return node.has_probe && same_ref(r,node.probe) ? std::string("$probe") : r.key();
    };
    return ref(atom.left)+":"+std::to_string(atom.op)+":"+
        (atom.right_is_const ? "#"+std::to_string(atom.constant_lower)+":"+std::to_string(atom.constant_upper) : ref(atom.right));
}

std::string shared_bound_rest_identity(const ComposedLeaf &leaf,std::size_t at)const {
    const auto &node=leaf.nodes[at];std::vector<std::string> terms;
    for(auto atom:node.local)terms.push_back(shared_bound_atom_identity(*atom,node));
    for(auto group:node.groups) {
        std::string text="boolean{";
        for(const auto &tok:group->postfix) {
            text+=std::to_string(static_cast<int>(tok.kind))+":";
            if(tok.atom)text+=shared_bound_atom_identity(*tok.atom,node);
            text+=';';
        }
        // Empty postfix is used only by the standalone OR-group test fixture.
        if(group->postfix.empty())for(auto atom:group->atoms)text+=shared_bound_atom_identity(*atom,node)+"|";
        terms.push_back(text+"}");
    }
    for(auto child:node.children) {
        std::string edge;
        const auto &sub=leaf.nodes[child];
        for(const auto &e:sub.connection->entries)edge+=e.candidate.key()+"="+e.source.key()+";";
        // The child's external value may be this node's probe or a value
        // bound inside its witness. Those are distinct composed rests.
        if(sub.has_probe)edge+="probe:"+(node.has_probe && same_ref(sub.probe,node.probe) ? std::string("$probe") : sub.probe.key())+";";
        terms.push_back("child{"+edge+shared_bound_rest_identity(leaf,child)+"}");
    }
    std::sort(terms.begin(),terms.end());
    std::string result=std::to_string(node.universe)+":"+std::to_string(node.lower)+":"+std::to_string(node.upper)+"{";
    for(const auto &term:terms)result+=std::to_string(term.size())+":"+term;
    return result+"}";
}

bool shared_bound_acyclic(std::size_t group,std::vector<unsigned> &color)const {
    if(color[group]==1U)return false;
    if(color[group]==2U)return true;
    color[group]=1U;
    for(auto f:shared_bound_groups_[group].frames)for(auto child:shared_bound_frames_[f].children)
        if(!shared_bound_acyclic(shared_bound_frames_[child].group,color))return false;
    color[group]=2U;return true;
}

void shared_bound_polarities(const FormulaNode *node,bool negative=false) {
    if(!node)return;
    if(node->kind==FormulaNode::Branch) {
        (negative ? shared_negative_leaves_ : shared_positive_leaves_)|=std::uint64_t{1}<<node->leaf_id;return;
    }
    if(node->kind==FormulaNode::Not){shared_bound_polarities(node->left.get(),!negative);return;}
    shared_bound_polarities(node->left.get(),negative);shared_bound_polarities(node->right.get(),negative);
}

void configure_shared_bound_graph() {
    const auto count=composed_bound_leaves_.size();
    if(!cf_decision_sharing || count<2U || count>64U)return;
    shared_bound_polarities(bound_formula_.get());
    std::map<const BoundConnection*,std::size_t> groups;
    std::map<std::pair<const BoundConnection*,std::string>,std::shared_ptr<composed_windows::Cells>> decisions;
    shared_bound_roots_.resize(count);shared_body_state_.resize(count);shared_root_pending_.resize(count);
    std::vector<std::vector<std::size_t>> ids(count);
    bool eligible=true;
    for(std::size_t leaf=0;leaf<count;++leaf) {
        auto &plan=composed_bound_leaves_[leaf];ids[leaf].resize(plan.nodes.size(),SIZE_MAX);
        for(std::size_t n=1;n<plan.nodes.size();++n) {
            auto &node=plan.nodes[n];auto conn=node.connection.get();
            auto found=groups.find(conn);
            if(found==groups.end()) {
                const auto id=shared_bound_groups_.size();groups.emplace(conn,id);
                shared_bound_groups_.emplace_back();shared_bound_groups_.back().connection=node.connection;
                found=groups.find(conn);
            }
            auto &g=shared_bound_groups_[found->second];const auto bit=std::uint64_t{1}<<leaf;
            if(g.leaves&bit)eligible=false; // recursive reuse needs distinct activation frames
            g.leaves|=bit;const auto id=shared_bound_frames_.size();ids[leaf][n]=id;g.frames.push_back(id);
            shared_bound_frames_.emplace_back();auto &frame=shared_bound_frames_.back();
            frame.leaf=leaf;frame.slot=n;frame.group=found->second;frame.plan=&node;
            node.shared_group=frame.group;
            auto key=std::make_pair(conn,shared_bound_rest_identity(plan,n));
            auto [rest,inserted]=decisions.emplace(std::move(key),node.cells.data);
            if(!inserted)node.cells.data=rest->second;
        }
    }
    for(std::size_t id=0;id<shared_bound_frames_.size();++id) {
        auto &frame=shared_bound_frames_[id];
        const auto &node=composed_bound_leaves_[frame.leaf].nodes[frame.slot];
        if(node.parent>0)frame.parent=ids[frame.leaf][node.parent];
        else shared_bound_roots_[frame.leaf].push_back(ids[frame.leaf][frame.slot]);
        for(auto child:node.children)frame.children.push_back(ids[frame.leaf][child]);
        frame.child_state.resize(frame.children.size());
    }
    for(auto &frame:shared_bound_frames_)for(std::size_t i=0;i<frame.children.size();++i)
        shared_bound_frames_[frame.children[i]].parent_slot=i;
    std::vector<unsigned> color(shared_bound_groups_.size());
    for(std::size_t g=0;g<color.size() && eligible;++g)eligible=shared_bound_acyclic(g,color);
    // Do not replace the demand schedule for a program with no shared join.
    bool shared=false;
    for(const auto &g:shared_bound_groups_)if((g.leaves&(g.leaves-1U))!=0) {
        shared=true;++shared_bound_should_nodes_;
    }
    eligible&=shared;
    if(!eligible){shared_bound_frames_.clear();shared_bound_groups_.clear();shared_bound_roots_.clear();return;}
    // The plan, not the policy's name/target, chooses the executor. Fully
    // functional roots retain the demand formula and per-branch dense gathers.
    functional_composed_program_=true;
    for(const auto &leaf:composed_bound_leaves_)for(auto root:leaf.nodes[0].children)
        functional_composed_program_ &= leaf.nodes[root].functional_tail;
    shared_bound_program_=!functional_composed_program_;
    // Every routing edge, point/full request shape and parent slot is fixed
    // now. Runtime routing intersects live branch masks; it does not search
    // the graph or walk ancestor frames.
    for(auto &g:shared_bound_groups_) {
        std::map<std::size_t,std::size_t> routes;
        for(auto id:g.frames) {
            const auto &f=shared_bound_frames_[id];
            if(f.plan->functional_tail){g.functional_frames.push_back(id);g.functional_leaves|=std::uint64_t{1}<<f.leaf;}
            for(std::size_t slot=0;slot<f.children.size();++slot) {
                const auto child=f.children[slot];const auto &sub=shared_bound_frames_[child];
                auto [it,inserted]=routes.emplace(sub.group,routes.size());
                if(inserted)g.routes.push_back({sub.group,{}});
                const bool point=sub.plan->has_probe && !(f.plan->has_probe && same_ref(sub.plan->probe,f.plan->probe));
                g.routes[it->second].edges.push_back({id,child,slot,point,point ? sub.plan->probe.node_id : -1});
            }
        }
    }
    std::map<std::size_t,std::size_t> root_routes;
    for(const auto &roots:shared_bound_roots_)for(auto id:roots) {
        const auto group=shared_bound_frames_[id].group;
        auto [it,inserted]=root_routes.emplace(group,root_routes.size());
        if(inserted)shared_root_routes_.push_back({group,{}});
        shared_root_routes_[it->second].frames.push_back(id);
    }
}

void shared_bound_functional(std::size_t group,std::uint64_t requests,std::uint32_t parent_row) {
    auto &g=shared_bound_groups_[group];auto &conn=*g.connection;
    requests&=g.functional_leaves&shared_needed_;if(!requests)return;
    std::uint64_t asking=0;
    for(auto id:g.functional_frames) {
        auto &f=shared_bound_frames_[id];const auto bit=std::uint64_t{1}<<f.leaf;
        if(!(requests&bit) || !shared_bound_live(id))continue;
        f.asked=true;f.done=false;f.row_live=false;
        if(f.point && f.plan->has_probe && f.probe==kNullRank)shared_bound_deliver(id,{});
        else asking|=bit;
    }
    asking&=shared_needed_;if(!asking || shared_root_state_>=0)return;
    std::uint64_t before=0;CF_COUNT(before=partner_touches_;);
    bound_input(conn,parent_row);if(conn.entries.size()>1U)bound_resolve(conn,parent_row);
    CF_COUNT(shared_bound_negative_reads(group,asking,partner_touches_-before););
    const bool empty=conn.rank==kNullRank || (conn.entries.size()>1U && !conn.match.count);
    if(!empty && conn.entries.size()>1U && conn.match.count!=1U) {
        shared_supported_=false;CF_COUNT(++bound_fallbacks_);return;
    }
    const auto key=conn.entries.size()>1U ? conn.match.position : conn.rank;
    if(!empty)CF_COUNT(++bound_probes_;++collective_record_probes_;);
    bool all_hit=true;
    for(auto id:g.functional_frames) {
        auto &f=shared_bound_frames_[id];const auto bit=std::uint64_t{1}<<f.leaf;
        if(!(asking&shared_needed_&bit) || !shared_bound_live(id))continue;
        if(empty){shared_bound_deliver(id,{});continue;}
        auto &node=*f.plan;CF_COUNT(++shared_request_frame_visits_;++bound_slot_checks_;++collective_slot_checks_;);
        const auto state=node.cells.state(key);f.key=key;
        if(state && (node.cells.complete(key) || (f.point && node.cells.covers(key,f.probe)))) {
            CF_COUNT(++node.probes;++node.hits;++node.arrivals;++node.functional_requests;++node.dense_gathers;
                if(f.point)++node.point_requests;else ++node.full_requests;
                const auto target=static_cast<std::uint32_t>(bindings_[target_node_]);
                if(node.counter_target!=target){node.counter_target=target;++node.undecided_target_rows;});
            shared_bound_deliver(id,{true,node.cells.data.get(),key,{}});
        } else {
            all_hit=false;std::uint64_t before_reads=0;CF_COUNT(before_reads=partner_touches_;);
            auto answer=composed_node_bound(composed_bound_leaves_[f.leaf],f.slot,f.point,f.probe,true);
            const auto cause=composed_last_cause_;
            CF_COUNT(shared_bound_negative_reads(group,bit,partner_touches_-before_reads););
            shared_bound_deliver(id,std::move(answer),cause);
        }
    }
    if(!empty && all_hit)CF_COUNT(++bound_hits_;);
}

// Diagnostic attribution, not a change of schedule. A physical read is
// negative-only iff every currently asking request at this node is negative.
// Participations may overlap across branches; exclusive reads do not.
void shared_bound_negative_reads(std::size_t group,std::uint64_t requests,std::uint64_t rows) {
    if(!rows || (requests&shared_positive_leaves_))return;
    const auto negative=requests&shared_negative_leaves_;if(!negative)return;
    negative_only_physical_reads_+=rows;
    for(auto id:shared_bound_groups_[group].frames) {
        auto &f=shared_bound_frames_[id];if(!(negative&(std::uint64_t{1}<<f.leaf)))continue;
        auto &node=composed_bound_leaves_[f.leaf].nodes[f.slot];node.negative_only_reads+=rows;
        if(!(negative&(negative-1U)))node.negative_exclusive_reads+=rows;
    }
}

void shared_bound_propagate(std::size_t group=SIZE_MAX,std::size_t leaf=SIZE_MAX) {
    const auto before=shared_root_state_;const auto visits=composed_formula_.updates();
    if(leaf!=SIZE_MAX)composed_formula_.settle(leaf,shared_body_state_[leaf]!=0);
    shared_root_state_=composed_formula_.value();shared_needed_=composed_formula_.needed();
    CF_COUNT(shared_formula_visits_+=composed_formula_.updates()-visits;);
    if(before<0 && shared_root_state_>=0) {
        composed_last_cause_=group;
        if(group==SIZE_MAX)CF_COUNT(++shared_target_filter_decisions_);
        else CF_COUNT(++shared_bound_groups_[group].root_decisions);
    }
}

bool shared_bound_live(std::size_t id)const {
    CF_COUNT(++shared_live_checks_);
    const auto &frame=shared_bound_frames_[id];
    return frame.active && shared_supported_ && shared_root_state_<0 &&
        (shared_needed_&(std::uint64_t{1}<<frame.leaf));
}

ComposedNode &shared_bound_node(std::size_t id) {
    CF_COUNT(++shared_request_frame_visits_);
    return *shared_bound_frames_[id].plan;
}

void shared_bound_cancel(std::size_t id) {
    auto &f=shared_bound_frames_[id];if(!f.active)return;
    f.active=false;f.row_live=false;
    for(auto child:f.children)if(shared_bound_frames_[child].active)shared_bound_cancel(child);
}

void shared_bound_deliver(std::size_t id,BoundAnswer answer,std::size_t cause=SIZE_MAX) {
    auto &f=shared_bound_frames_[id];if(f.done || !f.active)return;
    if(cause==SIZE_MAX)cause=f.group;
    f.answer=std::move(answer);f.done=true;f.row_live=false;f.active=false;
    if(!f.answer.supported){shared_supported_=false;return;}
    if(f.parent==SIZE_MAX) {
        const auto pass=f.answer.covers(shared_bound_node(id).has_probe ? f.probe : 0U);
        if(!pass)shared_body_state_[f.leaf]=0;
        else if(!--shared_root_pending_[f.leaf]) {
            shared_body_state_[f.leaf]=1;CF_COUNT(++composed_bound_leaves_[f.leaf].body_passes);
        }
        if(shared_body_state_[f.leaf]>=0)shared_bound_propagate(cause,f.leaf);return;
    }
    auto &parent=shared_bound_frames_[f.parent];if(!parent.row_live)return;
    const auto &node=shared_bound_node(id),&above=shared_bound_node(f.parent);
    bool pass=true;
    if(!node.has_probe)pass=f.answer.covers(0U);
    else if(above.has_probe && same_ref(node.probe,above.probe))parent.witness.intersect(f.answer.coverage());
    else pass=f.answer.covers(f.probe);
    if(!pass)parent.witness.windows.clear();
    if(parent.child_state[f.parent_slot]!=2U) {
        parent.child_state[f.parent_slot]=2U;
        if(!parent.open_children)fail("shared child count underflow");--parent.open_children;
    }
    if(parent.witness.empty() || !parent.open_children)
        shared_bound_row_done(f.parent,cause);
}

void shared_bound_store(std::size_t id,std::size_t cause=SIZE_MAX) {
    auto &f=shared_bound_frames_[id];auto &node=shared_bound_node(id);
    // An equal rest in this same batch may already have published its answer.
    // Share that fact; never overwrite a complete envelope with a fragment.
    if(node.cells.complete(f.key)) {
        shared_bound_deliver(id,{true,node.cells.data.get(),f.key,{}},cause);return;
    }
    if(node.cells.state(f.key))f.coverage.unite(node.cells.get(f.key));
    if(!f.complete && f.coverage.empty()){shared_bound_deliver(id,{true,nullptr,0,{}},cause);return;}
    if(!node.cells.recording()) {
        ++bound_record_skips_;
        shared_bound_deliver(id,{true,nullptr,0,std::move(f.coverage)},cause);return;
    }
    const auto extra=node.cells.extra_bytes(f.coverage);
    if(extra && !reserve_dense_cache(extra)) {
        ++bound_record_refusals_;++bound_record_skips_;
        shared_bound_deliver(id,{true,nullptr,0,std::move(f.coverage)},cause);return;
    }
    const auto was=node.cells.state(f.key);node.cells.put(f.key,f.coverage,f.complete);
    CF_COUNT(++bound_fills_;++node.fills;if(!was)++node.unique_records;
        if(f.complete)++node.complete_fills;else ++node.partial_fills;);
    shared_bound_deliver(id,{true,node.cells.data.get(),f.key,{}},cause);
}

void shared_bound_row_done(std::size_t id,std::size_t cause=SIZE_MAX) {
    auto &f=shared_bound_frames_[id];if(!f.row_live)return;
    f.row_live=false;f.coverage.unite(f.witness);
    for(auto child:f.children)if(shared_bound_frames_[child].active)shared_bound_cancel(child);
    const auto &node=shared_bound_node(id);const auto &conn=*node.connection;
    if(conn.unique || conn.entries.size()>1U || (!node.has_probe && !f.coverage.empty())) {
        shared_bound_store(id,cause);return;
    }
    if(f.point && f.coverage.covers(f.probe)) {
        // Even if this happens to be the final row, partial is safe. A later
        // full request can complete it; an uncovered point can never reject.
        f.complete=false;CF_COUNT(++shared_bound_node(id).first_stops);shared_bound_store(id,cause);
    }
}

bool shared_bound_local_row(std::size_t id,std::uint32_t row) {
    auto &f=shared_bound_frames_[id];auto &node=shared_bound_node(id);
    // A programming error here is a real stage failure, never a timing censor.
    if(f.done || !shared_bound_live(id))fail("shared bound read after decided request");
    bindings_[node.occurrence]=row;f.witness=composed_windows::Coverage::all(node.universe);
    for(const auto *atom:node.local) {
        if(std::find(node.probe_atoms.begin(),node.probe_atoms.end(),atom)!=node.probe_atoms.end()) {
            const bool left=same_ref(atom->left,node.probe);const auto &end=left ? atom->right : atom->left;
            if(bindings_[end.node_id]<0){shared_supported_=false;return false;}
            const auto rank=row_local_rank(end,bindings_[end.node_id]);
            if(rank==kNullRank){f.witness.windows.clear();break;}
            const auto op=left ? atom->op : invert_op(atom->op);
            composed_windows::Coverage atom_window;composed_windows::Window w{0,node.universe};
            if(op==POLICY_OP_LT)w.hi=rank;else if(op==POLICY_OP_LE)w.hi=rank+1U;
            else if(op==POLICY_OP_GT)w.lo=rank+1U;else if(op==POLICY_OP_GE)w.lo=rank;
            else {shared_supported_=false;return false;}
            atom_window.add(w);f.witness.intersect(atom_window);
        } else if(!atom_holds(*atom)){f.witness.windows.clear();break;}
    }
    if(!f.witness.empty())for(auto *group:node.groups)
        if(!boolean_group_holds(*group)){f.witness.windows.clear();break;}
    const auto &conn=*node.connection;
    if(f.point && !f.children.empty() && !conn.unique && conn.entries.size()==1U && node.has_probe &&
       !f.witness.empty() && !f.witness.covers(f.probe)) {
        f.complete=false;f.witness.windows.clear();CF_COUNT(++node.point_pruned);
    }
    std::fill(f.child_state.begin(),f.child_state.end(),0U);f.open_children=f.children.size();f.row_live=true;
    if(f.witness.empty() || f.children.empty())shared_bound_row_done(id);
    return shared_supported_;
}

void shared_bound_solve(std::size_t group,std::uint64_t requests,std::uint32_t parent_row) {
    auto &g=shared_bound_groups_[group];auto &conn=*g.connection;
    requests&=shared_needed_;if(!requests || shared_root_state_>=0)return;
    // A functional suffix has no shared slice to schedule. Retain each
    // request's old composed summary; share only the connection lookup scratch.
    shared_bound_functional(group,requests,parent_row);requests&=~g.functional_leaves;
    requests&=shared_needed_;if(!requests || shared_root_state_>=0 || !shared_supported_)return;
    // NULL-ordered requests settle before they join a shared connection read.
    for(auto id:g.frames) {
        auto &f=shared_bound_frames_[id];const auto bit=std::uint64_t{1}<<f.leaf;
        if(!(requests&bit) || !shared_bound_live(id))continue;
        f.asked=true;f.done=false;f.row_live=false;f.complete=true;f.coverage.windows.clear();
        if(f.point && shared_bound_node(id).has_probe && f.probe==kNullRank) {
            CF_COUNT(++shared_bound_node(id).arrivals;++shared_bound_node(id).point_requests;);
            shared_bound_deliver(id,{});requests&=~bit;
        }
    }
    requests&=shared_needed_;if(!requests || shared_root_state_>=0)return;
    CF_COUNT(++g.entries;++conn.shared_entries);
    // The entering rank is read once for the whole live request set.
    bound_input(conn,parent_row);
    std::uint64_t before_resolve=0;CF_COUNT(before_resolve=partner_touches_;);
    if(conn.entries.size()>1U)bound_resolve(conn,parent_row);
    CF_COUNT(shared_bound_negative_reads(group,requests,partner_touches_-before_resolve););
    std::uint64_t misses=0;
    bool probed=false,all_cached=true;
    for(auto id:g.frames) {
        auto &f=shared_bound_frames_[id];if(!(requests&(std::uint64_t{1}<<f.leaf)))continue;
        if(!shared_bound_live(id))continue;
        auto &node=shared_bound_node(id);
        CF_COUNT(++node.arrivals;if(f.point)++node.point_requests;else ++node.full_requests;);
        CF_COUNT(const auto target=static_cast<std::uint32_t>(bindings_[target_node_]);
            if(node.counter_target!=target){node.counter_target=target;++node.undecided_target_rows;});
        if((f.point && node.has_probe && f.probe==kNullRank) || conn.rank==kNullRank ||
           (conn.entries.size()>1U && !conn.match.count)) {shared_bound_deliver(id,{});continue;}
        if(conn.entries.size()>1U && conn.match.count!=1U) {
            CF_COUNT(++bound_fallbacks_);shared_bound_deliver(id,{false,nullptr,0,{}});continue;
        }
        f.key=conn.entries.size()>1U ? conn.match.position : conn.rank;
        CF_COUNT(++node.probes;++bound_slot_checks_;++collective_slot_checks_;
            if(!probed){++bound_probes_;++collective_record_probes_;});probed=true;
        const auto state=node.cells.state(f.key);
        if(state && (node.cells.complete(f.key) || (f.point && node.cells.covers(f.key,f.probe)))) {
            CF_COUNT(++node.hits);shared_bound_deliver(id,{true,node.cells.data.get(),f.key,{}});continue;
        }
        CF_COUNT(++node.misses;if(state)++node.reopens;);
        CF_COUNT(const auto target=static_cast<std::uint32_t>(bindings_[target_node_]);
            if(node.counter_miss_target!=target){node.counter_miss_target=target;++node.cache_miss_target_rows;});
        if(state)f.coverage=node.cells.get(f.key);
        misses|=std::uint64_t{1}<<f.leaf;all_cached=false;
    }
    if(probed && all_cached)CF_COUNT(++bound_hits_;);
    if(!misses || shared_root_state_>=0 || !shared_supported_)return;
    bound_resolve(conn,parent_row);
    const auto begin=conn.begin,end=conn.end;
    const auto count=conn.entries.size()>1U ? (conn.match.count==1U ? 1U : 0U) : end-begin;
    for(std::uint32_t p=0;p<count && shared_root_state_<0 && shared_supported_;++p) {
        if(!(p&4095U))CHECK_FOR_INTERRUPTS();bool any=false;
        for(auto id:g.frames)if((misses&(std::uint64_t{1}<<shared_bound_frames_[id].leaf)) &&
            !shared_bound_frames_[id].done && shared_bound_live(id)){any=true;break;}
        if(!any)break;
        const auto row=conn.entries.size()>1U ? conn.match.row : u32le(conn.index->cix.child_rows+4ULL*(begin+p));
        if(conn.entries.size()==1U){++partner_touches_;CF_COUNT(++bound_first_rows_;
            std::uint64_t live=0;for(auto id:g.frames) {
                const auto &f=shared_bound_frames_[id];const auto bit=std::uint64_t{1}<<f.leaf;
                if((misses&bit) && !f.done && shared_bound_live(id))live|=bit;
            }
            shared_bound_negative_reads(group,live,1U););}
        CF_COUNT(++g.rows;++conn.shared_rows);
        // Bind every alias before any request's local test/descendants.
        for(auto id:g.frames)if(misses&(std::uint64_t{1}<<shared_bound_frames_[id].leaf))
            bindings_[shared_bound_node(id).occurrence]=row;
        for(auto id:g.frames)if((misses&(std::uint64_t{1}<<shared_bound_frames_[id].leaf)) &&
            !shared_bound_frames_[id].done && shared_bound_live(id))shared_bound_local_row(id,row);
        // Child routing is fixed at plan time. Share an iterator among all
        // currently asking branches, never extend a path for an unasked rest.
        for(const auto &route:g.routes) {
            if(shared_root_state_>=0 || !shared_supported_)break;
            std::uint64_t asking=0;
            for(const auto &edge:route.edges) {
                auto &f=shared_bound_frames_[edge.parent];const auto bit=std::uint64_t{1}<<f.leaf;
                CF_COUNT(++shared_child_route_checks_);
                if(!(misses&shared_needed_&bit) || !f.active || !f.row_live || f.child_state[edge.slot])continue;
                auto &child=shared_bound_frames_[edge.child];f.child_state[edge.slot]=1U;
                child.active=true;child.point=edge.point;asking|=bit;
                const auto source=edge.point ? bindings_[edge.probe_node] : -1;
                child.probe=source<0 ? kNullRank : row_local_rank(child.plan->probe,source);
            }
            if(asking)shared_bound_solve(route.group,asking,row);
        }
        for(auto id:g.frames)if(misses&(std::uint64_t{1}<<shared_bound_frames_[id].leaf))
            bindings_[shared_bound_node(id).occurrence]=-1;
    }
    for(auto id:g.frames)if((misses&(std::uint64_t{1}<<shared_bound_frames_[id].leaf)) &&
        !shared_bound_frames_[id].done && shared_bound_live(id))shared_bound_store(id);
}

bool shared_bound_row(std::uint32_t row) {
        target_walk_started_=true;bindings_[target_node_]=row;composed_formula_.begin();
        shared_supported_=true;shared_root_state_=-1;
        std::fill(shared_body_state_.begin(),shared_body_state_.end(),-1);
        for(auto &frame:shared_bound_frames_){frame.asked=false;frame.done=false;frame.row_live=false;frame.active=false;}
        for(std::size_t leaf=0;leaf<shared_bound_roots_.size();++leaf)shared_root_pending_[leaf]=shared_bound_roots_[leaf].size();
        shared_bound_propagate();
        for(std::size_t leaf=0;leaf<composed_bound_leaves_.size() && shared_root_state_<0;++leaf) {
            if(!(shared_needed_&(std::uint64_t{1}<<leaf)))continue;
            auto &plan=composed_bound_leaves_[leaf];CF_COUNT(++plan.arrivals);bool pass=true;
            for(auto atom:plan.target_atoms)if(!atom_holds(*atom)){pass=false;break;}
            if(pass)for(auto *group:plan.target_groups)if(!boolean_group_holds(*group)){pass=false;break;}
            if(!pass){CF_COUNT(++plan.target_filtered);shared_body_state_[leaf]=0;shared_bound_propagate(SIZE_MAX,leaf);}
            else if(!shared_root_pending_[leaf]){shared_body_state_[leaf]=1;shared_bound_propagate(SIZE_MAX,leaf);}
        }
        for(const auto &route:shared_root_routes_) {
            if(shared_root_state_>=0 || !shared_supported_)break;
            std::uint64_t asking=0;
            for(auto id:route.frames) {
                auto &f=shared_bound_frames_[id];const auto bit=std::uint64_t{1}<<f.leaf;
                if(!(shared_needed_&bit) || f.asked)continue;
                const auto &node=*f.plan;f.point=node.has_probe;f.active=true;
                f.probe=node.has_probe ? row_local_rank(node.probe,row) : 0U;
                asking|=bit;CF_COUNT(++composed_bound_leaves_[f.leaf].root_reads);
            }
            if(asking)shared_bound_solve(route.group,asking,row);
        }
        if(shared_root_state_<0)shared_supported_=false;
        return shared_root_state_==1;
}

std::size_t shared_bound_group_for_node(const ComposedNode &node)const {
    for(const auto &frame:shared_bound_frames_)
        if(&composed_bound_leaves_[frame.leaf].nodes[frame.slot]==&node)return frame.group;
    return SIZE_MAX;
}

std::size_t shared_bound_cell_identity(const ComposedNode &node)const {
    std::size_t id=0;
    for(const auto &leaf:composed_bound_leaves_)for(const auto &other:leaf.nodes) {
        if(other.cells.data.get()==node.cells.data.get())return id;
        ++id;
    }
    return SIZE_MAX;
}
