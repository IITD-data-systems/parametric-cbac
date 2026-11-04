// Composed subwalk summaries. Metadata only at planning time; all witness
// reads and every summary fill occur after a target arrival. Eligibility is
// a structural equality tree with one outside ordered probe per subwalk.
// Ineligible graphs retain the existing walk without a new per-node dispatch.
struct BoundEntry {ColumnRef candidate,source;};
struct BoundConnection {
    std::vector<BoundEntry> entries;
    const ColumnIndex *index=nullptr;
    std::vector<const std::uint32_t*> source,secondary;
    bool unique=false;
    std::uint32_t parent_row=kNullRank,rank=kNullRank,begin=0,end=0;
    std::uint32_t resolved_parent=kNullRank;
    posting_position::Match match;
    std::uint32_t resolved_row=kNullRank;
    std::uint64_t rank_reads=0,slice_reads=0,shared_entries=0,shared_rows=0;
};
// Requests with identical filled rests share the same entering-rank cells.
// The connection and the polarity are not part of the rest identity.
struct BoundCells {
    std::shared_ptr<composed_windows::Cells> data=std::make_shared<composed_windows::Cells>();
    void plan(std::size_t n,composed_windows::Shape s,std::uint32_t u){data->plan(n,s,u);}
    std::size_t planned_bytes()const{return data->planned_bytes();}
    std::size_t bytes()const{return data->bytes();}
    std::size_t extra_bytes(const composed_windows::Coverage &c)const{return data->extra_bytes(c);}
    unsigned state(std::uint32_t k)const{return data->state(k);}
    bool complete(std::uint32_t k)const{return data->complete(k);}
    bool covers(std::uint32_t k,std::uint32_t r)const{return data->covers(k,r);}
    bool recording()const{return data->recording();}
    int probe(std::uint32_t k,std::uint32_t r)const{return data->probe(k,r);}
    composed_windows::Coverage get(std::uint32_t k)const{return data->get(k);}
    void put(std::uint32_t k,composed_windows::Coverage c,bool complete=true){data->put(k,std::move(c),complete);}
};
struct ComposedNode {
    int occurrence=-1,parent=-1;
    std::vector<std::size_t> children;
    std::vector<const NormalizedAtom*> local,probe_atoms;
    std::vector<const LocalBooleanGroup*> groups;
    std::set<int> subtree;
    std::shared_ptr<BoundConnection> connection;
    bool has_probe=false,lower=false,upper=false;
    ColumnRef probe;
    std::uint32_t universe=1;
    // A composite position is proved unique by the arrival scan; never by
    // a newly built pair index. Ambiguity still declines the dense path.
    bool functional_tail=false;
    std::size_t shared_group=SIZE_MAX;
    std::uint64_t functional_requests=0,dense_gathers=0;
    std::uint64_t negative_only_reads=0,negative_exclusive_reads=0;
    BoundCells cells;
    std::uint64_t probes=0,hits=0,fills=0;
    std::uint64_t arrivals=0,misses=0,point_requests=0,full_requests=0;
    std::uint64_t first_stops=0,point_pruned=0,partial_fills=0,complete_fills=0,reopens=0,unique_records=0;
    std::uint32_t counter_target=kNullRank,counter_miss_target=kNullRank;
    std::uint64_t undecided_target_rows=0,cache_miss_target_rows=0;
};
struct ComposedLeaf {
    std::vector<ComposedNode> nodes; // slot zero is the target, never cached
    std::vector<const NormalizedAtom*> target_atoms;
    std::vector<const LocalBooleanGroup*> target_groups;
    std::uint64_t arrivals=0,target_filtered=0,root_reads=0,body_passes=0;
};
struct CollectiveAtom {const NormalizedAtom *atom=nullptr;std::size_t left=0,right=SIZE_MAX;};
struct CollectiveRoot {
    struct Request {std::size_t leaf=0,node=0,probe=SIZE_MAX,comparison=0;};
    std::shared_ptr<BoundConnection> connection;
    std::vector<Request> requests;
    std::vector<std::size_t> sources;
    std::vector<std::size_t> comparisons;
    std::vector<std::uint64_t> comparison_requests;
    std::uint64_t branches=0;
};
bool collective_composed_program_=false;
std::vector<CollectiveRoot> collective_roots_;
std::vector<const std::uint32_t*> collective_inputs_;
std::vector<std::uint32_t> collective_values_;
std::vector<std::vector<CollectiveAtom>> collective_target_atoms_;
std::vector<std::vector<std::vector<std::pair<int,std::size_t>>>> collective_target_groups_;
std::vector<std::vector<std::size_t>> collective_conjuncts_;
std::vector<std::uint8_t> collective_target_stack_;
std::uint64_t collective_record_probes_=0,collective_slot_checks_=0,collective_input_reads_=0,bound_slot_checks_=0;
struct BoundAnswer {
    bool supported=true;
    const composed_windows::Cells *cells=nullptr;
    std::uint32_t key=0;
    composed_windows::Coverage temporary;
    bool covers(std::uint32_t rank)const {
        return cells ? cells->covers(key,rank) : temporary.covers(rank);
    }
    composed_windows::Coverage coverage()const{return cells ? cells->get(key) : temporary;}
};
// Definitions are below the sequential compiler/walker. Only multi-request
// equality trees use this schedule; a single request keeps the demand walker.
struct SharedBoundFrame {
    std::size_t leaf=0,slot=0,group=0,parent=SIZE_MAX;
    std::vector<std::size_t> children;
    std::vector<std::uint8_t> child_state;
    ComposedNode *plan=nullptr;
    std::size_t parent_slot=SIZE_MAX,open_children=0;
    bool active=false;
    bool asked=false,done=false,row_live=false,point=false,complete=true;
    std::uint32_t probe=kNullRank,key=kNullRank;
    composed_windows::Coverage coverage,witness;
    BoundAnswer answer;
};
struct SharedBoundGroup {
    struct Edge {std::size_t parent=0,child=0,slot=0;bool point=false;int probe_node=-1;};
    struct Route {std::size_t group=0;std::vector<Edge> edges;};
    std::shared_ptr<BoundConnection> connection;
    std::vector<std::size_t> frames;
    std::uint64_t leaves=0,entries=0,rows=0,root_decisions=0;
    std::vector<Route> routes;
    std::vector<std::size_t> functional_frames;
    std::uint64_t functional_leaves=0;
};
struct SharedRootRoute {std::size_t group=0;std::vector<std::size_t> frames;};
std::vector<SharedRootRoute> shared_root_routes_;
std::vector<SharedBoundFrame> shared_bound_frames_;
std::vector<SharedBoundGroup> shared_bound_groups_;
std::vector<std::vector<std::size_t>> shared_bound_roots_;
std::vector<std::int8_t> shared_body_state_;
std::vector<std::size_t> shared_root_pending_;
std::uint64_t shared_needed_=0,shared_target_filter_decisions_=0;
int shared_root_state_=-1;
bool shared_bound_program_=false,shared_supported_=true;
bool functional_composed_program_=false;
std::size_t composed_last_cause_=SIZE_MAX;
std::uint64_t shared_request_frame_visits_=0,shared_child_route_checks_=0;
mutable std::uint64_t shared_live_checks_=0,shared_formula_visits_=0;
std::uint64_t shared_bound_should_nodes_=0,shared_bound_private_or_drivers_=0;
std::uint64_t shared_negative_leaves_=0,shared_positive_leaves_=0;
std::uint64_t negative_only_physical_reads_=0;
std::vector<ComposedLeaf> composed_bound_leaves_;
std::map<std::string,std::shared_ptr<BoundConnection>> bound_connections_;
bool composed_bound_program_=false;
bool composed_window_negated_=false;
composed_requests::Formula composed_formula_;
std::uint64_t composed_formula_updates_=0;
std::vector<std::size_t> composed_run_causes_;
std::uint64_t bound_probes_=0,bound_hits_=0,bound_fills_=0,bound_first_rows_=0;
std::uint64_t bound_position_scans_=0,bound_position_rows_=0,bound_connection_hits_=0;
std::uint64_t bound_fallbacks_=0,bound_target_rows_=0;
std::uint64_t bound_record_skips_=0;
// Store failures are observable in clean builds. These are updated only at
// reservation/Record refusal sites, never by a successful row-loop probe.
std::uint64_t bound_record_refusals_=0;
double bound_build_ms_=0;

std::size_t compile_composed_formula(const FormulaNode *node) {
    using F=composed_requests::Formula;
    if(node->kind==FormulaNode::Branch)return composed_formula_.add(F::leaf,node->leaf_id);
    if(node->kind==FormulaNode::True || node->kind==FormulaNode::False)
        return composed_formula_.add(F::constant,0,0,node->kind==FormulaNode::True);
    const auto a=compile_composed_formula(node->left.get());
    if(node->kind==FormulaNode::Not)return composed_formula_.add(F::negation,a);
    const auto b=compile_composed_formula(node->right.get());
    return composed_formula_.add(node->kind==FormulaNode::And ? F::conjunction : F::disjunction,a,b);
}

bool compile_composed_leaf(std::size_t leaf,ComposedLeaf &out,std::size_t *bytes,bool *ordered) {
    const auto *body=bound_leaves_[leaf];
    std::map<int,ColumnRef> occurrences;
    const auto collect=[&](const ColumnRef &r){occurrences.emplace(r.node_id,r);};
    for(auto atom:body->atoms){collect(atom->left);if(!atom->right_is_const)collect(atom->right);}
    for(const auto &group:body->boolean_groups)for(auto atom:group.atoms) {
        collect(atom->left);if(!atom->right_is_const)collect(atom->right);
    }
    if(!occurrences.count(target_node_) || occurrences.size()<2U)return false;
    out.nodes.emplace_back();out.nodes[0].occurrence=target_node_;
    std::map<int,std::size_t> slot{{target_node_,0U}};
    // Only mandatory equalities determine the tree. An OR comparison never
    // supplies an entry edge. No data or policy-side key set is inspected.
    for(std::size_t i=0;i<out.nodes.size();++i) {
        const auto parent=out.nodes[i].occurrence;
        for(auto atom:body->atoms) {
            if(atom->right_is_const || atom->op!=POLICY_OP_EQ)continue;
            const bool left=atom->left.node_id==parent,right=atom->right.node_id==parent;
            if(left==right)continue;
            const auto other=left ? atom->right.node_id : atom->left.node_id;
            if(slot.count(other))continue;
            const auto child=out.nodes.size();slot.emplace(other,child);
            out.nodes.emplace_back();out.nodes.back().occurrence=other;
            out.nodes.back().parent=static_cast<int>(i);out.nodes[i].children.push_back(child);
        }
    }
    if(slot.size()!=occurrences.size())return false; // theta/cyclic/disconnected: old path
    std::vector<std::vector<BoundEntry>> entries(out.nodes.size());
    for(auto atom:body->atoms) {
        const auto a=slot.at(atom->left.node_id);
        if(atom->right_is_const){out.nodes[a].local.push_back(atom);continue;}
        const auto b=slot.at(atom->right.node_id);
        if(a==b){out.nodes[a].local.push_back(atom);continue;}
        if(atom->op==POLICY_OP_EQ) {
            std::size_t child,parent;
            if(out.nodes[a].parent==static_cast<int>(b)){child=a;parent=b;}
            else if(out.nodes[b].parent==static_cast<int>(a)){child=b;parent=a;}
            else return false; // a cycle needs the existing general walk
            entries[child].push_back({a==child ? atom->left : atom->right,
                                      a==parent ? atom->left : atom->right});
        } else {
            if(atom->op!=POLICY_OP_LT && atom->op!=POLICY_OP_LE &&
               atom->op!=POLICY_OP_GT && atom->op!=POLICY_OP_GE)return false;
            const auto ancestor=[&](std::size_t x,std::size_t y) {
                for(int p=static_cast<int>(y);p>=0;p=out.nodes[p].parent)if(p==static_cast<int>(x))return true;
                return false;
            };
            if(ancestor(a,b))out.nodes[b].local.push_back(atom);
            else if(ancestor(b,a))out.nodes[a].local.push_back(atom);
            else return false; // sibling comparison is not independent subwalks
        }
    }
    for(const auto &group:body->boolean_groups) {
        int occurrence=-1;
        for(auto atom:group.atoms) {
            if(occurrence<0)occurrence=atom->left.node_id;
            if(atom->left.node_id!=occurrence ||
               (!atom->right_is_const && atom->right.node_id!=occurrence))return false;
        }
        if(occurrence<0)return false;
        out.nodes[slot.at(occurrence)].groups.push_back(&group);
    }
    for(std::size_t i=out.nodes.size();i-->0;) {
        auto &node=out.nodes[i];node.subtree.insert(node.occurrence);
        for(auto child:node.children)node.subtree.insert(out.nodes[child].subtree.begin(),out.nodes[child].subtree.end());
        if(!i)continue;
        // All outside values except the equality entry must be this ONE probe.
        // Constants and operator values remain part of the asking rest.
        for(auto atom:body->atoms) {
            if(atom->right_is_const)continue;
            const bool left=node.subtree.count(atom->left.node_id),right=node.subtree.count(atom->right.node_id);
            if(left==right)continue;
            if(atom->op==POLICY_OP_EQ) {
                bool entry=false;
                for(const auto &e:entries[i])entry|=(same_ref(e.candidate,atom->left)&&same_ref(e.source,atom->right)) ||
                    (same_ref(e.candidate,atom->right)&&same_ref(e.source,atom->left));
                if(!entry)return false;
                continue;
            }
            const auto &probe=left ? atom->right : atom->left;
            if(node.has_probe && !same_ref(node.probe,probe))return false;
            node.has_probe=true;node.probe=probe;
            const auto op=left ? invert_op(atom->op) : atom->op; // probe op endpoint
            node.lower|=op==POLICY_OP_GT || op==POLICY_OP_GE;
            node.upper|=op==POLICY_OP_LT || op==POLICY_OP_LE;
        }
        if(node.has_probe) {
            *ordered=true;node.universe=column(node.probe).cix.rank_count;
            for(auto atom:node.local)if(!atom->right_is_const &&
                (same_ref(atom->left,node.probe)||same_ref(atom->right,node.probe))) {
                const auto &endpoint=same_ref(atom->left,node.probe) ? atom->right : atom->left;
                if(column(endpoint).domain!=column(node.probe).domain)return false;
                node.probe_atoms.push_back(atom);
            }
        }
        if(entries[i].empty() || entries[i].size()>16U)return false;
        // The primary is an existing unary posting, chosen by header fanout.
        auto &ent=entries[i];
        std::stable_sort(ent.begin(),ent.end(),[&](const BoundEntry &a,const BoundEntry &b) {
            const auto &x=column(a.candidate).cix,&y=column(b.candidate).cix;
            const auto cx=double(x.row_count)/std::max(1U,x.present_count);
            const auto cy=double(y.row_count)/std::max(1U,y.present_count);
            return cx!=cy ? cx<cy : a.candidate.key()<b.candidate.key();
        });
        std::string identity;
        for(const auto &e:ent) {
            if(column(e.candidate).domain!=column(e.source).domain)return false;
            identity+=e.candidate.key()+"="+e.source.key()+";";
        }
        auto &conn=bound_connections_[identity];
        if(!conn) {
            conn=std::make_shared<BoundConnection>();conn->entries=ent;
            conn->index=&column(ent[0].candidate);
            conn->unique=ent.size()==1U && column_is_unique(ent[0].candidate);
            for(const auto &e:ent)conn->source.push_back(column(e.source).forward_ranks);
            for(std::size_t e=1;e<ent.size();++e)conn->secondary.push_back(column(ent[e].candidate).forward_ranks);
        }
        node.connection=conn;
        node.functional_tail=conn->unique || ent.size()>1U;
        for(auto child:node.children)node.functional_tail &= out.nodes[child].functional_tail;
        const auto count=ent.size()>1U ? conn->index->forward_rows : conn->index->cix.rank_count;
        const auto shape=!node.has_probe ? composed_windows::Shape::truth :
            node.lower && node.upper ? composed_windows::Shape::window :
            node.lower ? composed_windows::Shape::lower : composed_windows::Shape::upper;
        node.cells.plan(count,shape,node.universe);
        const auto next=node.cells.planned_bytes();
        if(next>SIZE_MAX-*bytes)return false;
        *bytes+=next;
    }
    out.target_atoms=out.nodes[0].local;out.target_groups=out.nodes[0].groups;
    return true;
}

void configure_composed_bounds() {
    if(!cf_composed_bounds || !cf_interval_edges || !cf_chain_boundaries)return;
    std::size_t bytes=0;bool ordered=false;
    if(!bound_formula_ || bound_leaves_.empty() || bound_leaves_.size()>64U)return;
    // OR-local equalities cannot be mandatory drivers for a shared tree.
    // They keep their private entry in the established general walk.
    for(const auto *body:bound_leaves_)for(const auto &group:body->boolean_groups)
        for(const auto *atom:group.atoms)
            if(!atom->right_is_const && atom->op==POLICY_OP_EQ && atom->left.node_id!=atom->right.node_id)
                ++shared_bound_private_or_drivers_;
    std::vector<ComposedLeaf> plans(bound_leaves_.size());
    for(std::size_t leaf=0;leaf<bound_leaves_.size();++leaf)
        if(!compile_composed_leaf(leaf,plans[leaf],&bytes,&ordered)) {
            bound_connections_.clear();return;
        }
    if(!ordered){bound_connections_.clear();return;}
    composed_formula_.finish(compile_composed_formula(bound_formula_.get()));
    composed_bound_leaves_=std::move(plans);
    // Sharing identities is planning-only; no rank or witness is read here.
    configure_shared_bound_graph();
    bytes=0;std::set<const composed_windows::Cells*> counted;
    for(const auto &leaf:composed_bound_leaves_)for(const auto &node:leaf.nodes)if(node.connection)
        if(counted.insert(node.cells.data.get()).second) {
            if(node.cells.planned_bytes()>SIZE_MAX-bytes){composed_bound_leaves_.clear();bound_connections_.clear();return;}
            bytes+=node.cells.planned_bytes();
        }
    // Lack of storage never changes the plan or fails the query. Missing
    // records expand through this same walk, never an alternate executor.
    if(!reserve_dense_cache(bytes)) {
        ++bound_record_refusals_;
        for(auto &leaf:composed_bound_leaves_)for(auto &node:leaf.nodes)if(node.connection)
            node.cells.data->stop_recording();
    }
    // Only the fully functional strategy changes layout this round. The
    // customer grouped schedule and its functional suffixes stay unchanged.
    if(functional_composed_program_) {
        std::map<const BoundConnection*,std::vector<std::shared_ptr<composed_windows::Cells>>> layouts;
        for(auto &leaf:composed_bound_leaves_)for(auto &node:leaf.nodes)if(node.connection) {
            auto &slots=layouts[node.connection.get()];
            if(std::find(slots.begin(),slots.end(),node.cells.data)==slots.end())slots.push_back(node.cells.data);
        }
        for(auto &entry:layouts) {
            auto &slots=entry.second;if(slots.size()<2U || !slots.front()->recording())continue;
            const auto count=slots.front()->count();std::vector<composed_windows::Shape> shapes;
            std::size_t old_bytes=0;bool compatible=true;
            for(const auto &slot:slots){compatible &= slot->count()==count;shapes.push_back(slot->shape());old_bytes+=slot->planned_bytes();}
            if(!compatible)continue;
            auto bank=std::make_shared<composed_windows::RankMajor>(count,shapes);
            const auto extra=bank->planned_bytes()>old_bytes ? bank->planned_bytes()-old_bytes : 0U;
            if(extra && !reserve_dense_cache(extra))continue; // per-branch fallback
            for(std::size_t s=0;s<slots.size();++s)slots[s]->attach(bank,s);
        }
    }
    composed_bound_program_=true;
    configure_collective_roots();
}

// Share only the connection read. Each request has its own boundary cells.
// The scratch holds one current parent's lookup, not a tuple decision store.
void bound_input(BoundConnection &c,std::uint32_t parent) {
    if(c.parent_row==parent){CF_COUNT(++bound_connection_hits_);return;}
    c.parent_row=parent;c.resolved_parent=kNullRank;c.resolved_row=kNullRank;c.rank=c.source[0][parent];CF_COUNT(++c.rank_reads);
    c.begin=c.end=0;c.match={};
}
void bound_resolve(BoundConnection &c,std::uint32_t parent) {
    bound_input(c,parent);if(c.resolved_parent==parent)return;
    c.resolved_parent=parent;
    if(c.rank==kNullRank)return;
    const auto &index=c.index->cix;c.begin=index.begin(c.rank);c.end=index.end(c.rank);CF_COUNT(++c.slice_reads);
    if(c.unique && c.begin<c.end)c.resolved_row=u32le(index.child_rows+4ULL*c.begin);
    if(c.entries.size()>1U) {
        std::array<std::uint32_t,16> values{};
        for(std::size_t i=1;i<c.entries.size();++i) {
            values[i-1]=c.source[i][parent];if(values[i-1]==kNullRank){c.begin=c.end=0;return;}
        }
        CF_COUNT(++bound_position_scans_);
        c.match=posting_position::scan(c.begin,c.end,
            [&](std::uint32_t p){return u32le(index.child_rows+4ULL*p);},
            [&](std::uint32_t row){
                for(std::size_t i=0;i<c.secondary.size();++i)if(c.secondary[i][row]!=values[i])return false;
                return true;
            });
        partner_touches_+=c.match.scanned;CF_COUNT(bound_position_rows_+=c.match.scanned);
    }
}

BoundAnswer composed_node_bound(ComposedLeaf &leaf,std::size_t at,
                              bool point_request=false,std::uint32_t probe_value=kNullRank,bool record_probed=false) {
    auto &node=leaf.nodes[at];auto &conn=*node.connection;
    composed_last_cause_=node.shared_group;
    CF_COUNT(if(node.functional_tail)++node.functional_requests;);
    CF_COUNT(++node.arrivals;if(point_request)++node.point_requests;else ++node.full_requests;);
    CF_COUNT(if(bindings_[target_node_]>=0) {
        const auto target=static_cast<std::uint32_t>(bindings_[target_node_]);
        if(node.counter_target!=target){node.counter_target=target;++node.undecided_target_rows;}
    });
    if(point_request && node.has_probe && probe_value==kNullRank)return {};
    const auto parent=bindings_[leaf.nodes[node.parent].occurrence];
    if(parent<0)return {false,nullptr,0,{}};
    bound_input(conn,static_cast<std::uint32_t>(parent));
    if(conn.rank==kNullRank)return {};
    std::uint32_t key=conn.rank;
    if(conn.entries.size()>1U) {
        bound_resolve(conn,static_cast<std::uint32_t>(parent));
        if(!conn.match.count)return {};
        // A posting position stands for exactly one row. Ambiguity must use
        // the existing general node store, not a point verdict or tuple cache.
        if(conn.match.count!=1U){CF_COUNT(++bound_fallbacks_);return {false,nullptr,0,{}};}
        key=conn.match.position;
    }
    CF_COUNT(if(!record_probed){++bound_probes_;++bound_slot_checks_;});
    CF_COUNT(++node.probes);
    const auto state=node.cells.state(key);
    const bool point_enumeration=point_request && !conn.unique && conn.entries.size()==1U;
    if(state && (node.cells.complete(key) ||
                 (point_request && node.cells.covers(key,probe_value)))) {
        CF_COUNT(if(!record_probed)++bound_hits_;++node.hits;if(node.functional_tail)++node.dense_gathers;);return {true,node.cells.data.get(),key,{}};
    }
    CF_COUNT(++node.misses;if(state)++node.reopens;);
    CF_COUNT(if(bindings_[target_node_]>=0) {
        const auto target=static_cast<std::uint32_t>(bindings_[target_node_]);
        if(node.counter_miss_target!=target){node.counter_miss_target=target;++node.cache_miss_target_rows;}
    });
    const auto started=std::chrono::steady_clock::now();
    bound_resolve(conn,static_cast<std::uint32_t>(parent));
    auto coverage=state ? node.cells.get(key) : composed_windows::Coverage{};
    bool supported=true,complete=true;
    const auto visit=[&](std::uint32_t row) {
        bindings_[node.occurrence]=row;
        composed_windows::Witness witness(node.universe);
        for(const auto *atom:node.local) {
            if(std::find(node.probe_atoms.begin(),node.probe_atoms.end(),atom)!=node.probe_atoms.end()) {
                const bool left=same_ref(atom->left,node.probe);
                const auto &endpoint=left ? atom->right : atom->left;
                const auto bound=bindings_[endpoint.node_id];
                if(bound<0){supported=false;break;}
                const auto rank=row_local_rank(endpoint,bound);
                if(rank==kNullRank){witness.reject();break;}
                const auto op=left ? atom->op : invert_op(atom->op);
                if(op!=POLICY_OP_LT && op!=POLICY_OP_LE && op!=POLICY_OP_GT && op!=POLICY_OP_GE)
                    {supported=false;break;}
                const auto shape=op==POLICY_OP_GT || op==POLICY_OP_GE ?
                    composed_windows::Shape::lower : composed_windows::Shape::upper;
                const auto window=composed_windows::ordered_window(shape,rank,
                    op==POLICY_OP_GT || op==POLICY_OP_LE,node.universe);
                witness.require(window);
            } else if(!atom_holds(*atom)){witness.reject();break;}
        }
        if(supported && !witness.coverage().empty())for(auto *group:node.groups)
            if(!boolean_group_holds(*group)){witness.reject();break;}
        // A concrete asking value can reject this row before its expensive
        // descendants. Omitted windows might serve another value, so this is
        // NOT a complete envelope or a global nogood.
        if(point_enumeration && !node.children.empty() && node.has_probe && !witness.coverage().empty() &&
           !witness.coverage().covers(probe_value)) {
            complete=false;CF_COUNT(++node.point_pruned);
            bindings_[node.occurrence]=-1;return;
        }
        if(supported && !witness.coverage().empty())for(auto child:node.children) {
            auto &sub=leaf.nodes[child];
            const bool shared_probe=sub.has_probe && node.has_probe && same_ref(sub.probe,node.probe);
            const auto source=sub.has_probe && !shared_probe ? bindings_[sub.probe.node_id] : -1;
            const auto value=source>=0 ? row_local_rank(sub.probe,source) : kNullRank;
            // Composition on the same outside probe needs the child's COMPLETE
            // window. A bound value internal to this witness needs only that
            // request's truth, and may stop at its first complete witness.
            auto result=composed_node_bound(leaf,child,sub.has_probe && !shared_probe,value);
            if(!result.supported){supported=false;break;}
            if(!sub.has_probe) {if(!result.covers(0U)){witness.reject();break;}}
            else if(shared_probe)witness.require(result.coverage());
            else {
                const auto source=bindings_[sub.probe.node_id];
                if(source<0){supported=false;break;}
                if(!result.covers(row_local_rank(sub.probe,source))){witness.reject();break;}
            }
            if(witness.coverage().empty())break;
        }
        if(supported)coverage.unite(witness.coverage());
        bindings_[node.occurrence]=-1;
    };
    if(conn.entries.size()>1U)visit(conn.match.row);
    else {
        const auto &index=conn.index->cix;
        // Recursive self-joins may reuse the same physical connection scratch.
        // The asking request owns these immutable cursor bounds, not scratch.
        const auto begin=conn.begin,end=conn.end;
        for(auto p=begin;p<end && supported;++p) {
            if(!(p&4095U))CHECK_FOR_INTERRUPTS();
            ++partner_touches_;CF_COUNT(++bound_first_rows_);
            visit(conn.unique ? conn.resolved_row : u32le(index.child_rows+4ULL*p));
            if(!node.has_probe && !coverage.empty()){if(p+1U<end)CF_COUNT(++node.first_stops);break;}
            if(point_enumeration && coverage.covers(probe_value)) {
                if(p+1U<end)complete=false;
                if(p+1U<end)CF_COUNT(++node.first_stops);break;
            }
        }
    }
    // This elapsed scope nests child builds; it is explicitly inclusive.
    bound_build_ms_+=elapsed_ms(started,std::chrono::steady_clock::now());
    if(!supported)return {false,nullptr,0,{}};
    if(!node.cells.recording()){++bound_record_skips_;return {true,nullptr,0,std::move(coverage)};}
    const auto extra=node.cells.extra_bytes(coverage);
    if(extra && !reserve_dense_cache(extra)) {
        ++bound_record_refusals_;++bound_record_skips_;
        return {true,nullptr,0,std::move(coverage)};
    }
    if(!complete && coverage.empty())return {true,nullptr,0,{}};
    node.cells.put(key,std::move(coverage),complete);
    CF_COUNT(++bound_fills_;++node.fills;if(!state)++node.unique_records;
        if(complete)++node.complete_fills;else ++node.partial_fills;);
    return {true,node.cells.data.get(),key,{}};
}

bool composed_functional_truth(ComposedLeaf &leaf,std::size_t at,std::uint32_t value,bool *supported) {
    auto &node=leaf.nodes[at];auto &conn=*node.connection;
    composed_last_cause_=node.shared_group;
    const auto parent=bindings_[leaf.nodes[node.parent].occurrence];
    if(parent<0){*supported=false;return false;}
    if(node.has_probe && value==kNullRank) {
        CF_COUNT(++node.arrivals;++node.functional_requests;++node.point_requests;);
        return false;
    }
    bound_input(conn,static_cast<std::uint32_t>(parent));
    if(conn.rank==kNullRank) {
        CF_COUNT(++node.arrivals;++node.functional_requests;
            if(node.has_probe)++node.point_requests;else ++node.full_requests;);
        return false;
    }
    auto key=conn.rank;
    if(conn.entries.size()>1U) {
        bound_resolve(conn,static_cast<std::uint32_t>(parent));
        if(!conn.match.count)return false;
        if(conn.match.count!=1U){*supported=false;return false;}
        key=conn.match.position;
    }
    const auto answer=node.cells.probe(key,value);
    if(answer>=0) {
        CF_COUNT(++node.arrivals;++node.functional_requests;++node.dense_gathers;
            if(node.has_probe)++node.point_requests;else ++node.full_requests;
            ++node.probes;++bound_probes_;++node.hits;++bound_hits_;
            const auto target=static_cast<std::uint32_t>(bindings_[target_node_]);
            if(node.counter_target!=target){node.counter_target=target;++node.undecided_target_rows;});
        return answer==1;
    }
    const auto result=composed_node_bound(leaf,at,node.has_probe,value);
    if(!result.supported){*supported=false;return false;}
    return result.covers(value);
}

bool composed_leaf_truth(std::size_t leaf_id,std::uint32_t row,bool *supported) {
    auto &leaf=composed_bound_leaves_[leaf_id];bindings_[target_node_]=row;
    CF_COUNT(++leaf.arrivals);
    for(auto atom:leaf.target_atoms)if(!atom_holds(*atom)){composed_last_cause_=SIZE_MAX;CF_COUNT(++leaf.target_filtered);return false;}
    for(auto *group:leaf.target_groups)if(!boolean_group_holds(*group)){composed_last_cause_=SIZE_MAX;CF_COUNT(++leaf.target_filtered);return false;}
    for(auto root:leaf.nodes[0].children) {
        CF_COUNT(++leaf.root_reads);
        const auto &node=leaf.nodes[root];
        const auto value=node.has_probe ? row_local_rank(node.probe,row) : 0U;
        if(node.functional_tail && cf_decision_sharing) {
            if(!composed_functional_truth(leaf,root,value,supported))return false;
            continue;
        }
        const auto answer=composed_node_bound(leaf,root,node.has_probe,value);
        if(!answer.supported){*supported=false;return false;}
        if(!answer.covers(value))return false;
    }
    CF_COUNT(++leaf.body_passes);
    return true;
}

bool composed_formula_truth(const FormulaNode *node,std::uint32_t row,bool *supported) {
    if(collective_composed_program_)return composed_collective_truth(row,supported);
    (void)node;composed_formula_.begin();
    while(composed_formula_.value()<0) {
        const auto needed=composed_formula_.needed();if(!needed)fail("compiled composed formula has no request");
        const auto leaf=unsigned(__builtin_ctzll(needed));
        const bool truth=composed_leaf_truth(leaf,row,supported);if(!*supported)return false;
        composed_formula_.settle(leaf,truth);
    }
    CF_COUNT(composed_formula_updates_+=composed_formula_.updates());
    return composed_formula_.value()==1;
}

bool composed_target_truth(std::uint32_t row) {
    target_walk_started_=true;bool supported=true;composed_last_cause_=SIZE_MAX;
    const auto verdict=shared_bound_program_ ? shared_bound_row(row) :
        composed_formula_truth(bound_formula_.get(),row,&supported);
    if(!supported || (shared_bound_program_ && !shared_supported_)) {
        // evaluate_target owns its count; the compiled outer loop owns all
        // target counts, including copied runs, so do not count twice.
        const auto before=target_evals_;const bool v=evaluate_target(row);target_evals_=before;return v;
    }
    CF_COUNT(++bound_target_rows_;
        if(functional_composed_program_) {
            if(composed_last_cause_==SIZE_MAX)++shared_target_filter_decisions_;
            else ++shared_bound_groups_[composed_last_cause_].root_decisions;
        });
    return verdict;
}

bool run_composed_bounds(std::uint32_t rows,std::vector<std::uint64_t> &allowed) {
    if(!composed_bound_program_)return false;
    for(std::uint32_t row=0;row<rows;++row) {
        if(!(row&4095U))CHECK_FOR_INTERRUPTS();
        if(composed_target_truth(row))allowed[row/64U]|=std::uint64_t{1}<<(row&63U);
        ++target_evals_;
    }
    return true;
}

void report_composed_bounds() {
    cf_perf_metric_set("composed_bounds_used",composed_bound_program_ ? 1 : 0);
    cf_perf_metric_set("bound_probes",bound_probes_);cf_perf_metric_set("bound_hits",bound_hits_);
    cf_perf_metric_set("bound_fills",bound_fills_);cf_perf_metric_set("bound_first_rows",bound_first_rows_);
    cf_perf_metric_set("bound_record_skips",bound_record_skips_);
    cf_perf_metric_set("bound_record_refusals",bound_record_refusals_);
    cf_perf_metric_set("bound_position_scans",bound_position_scans_);
    cf_perf_metric_set("bound_position_rows",bound_position_rows_);
    cf_perf_metric_set("bound_connection_hits",bound_connection_hits_);
    cf_perf_metric_set("bound_fallbacks",bound_fallbacks_);
    cf_perf_metric_set("bound_target_rows",bound_target_rows_);
    cf_perf_metric_set("bound_build_inclusive_ms",bound_build_ms_);
    cf_perf_metric_set("bound_bytes",composed_bound_bytes());
    cf_perf_metric_set("shared_bound_graph_used",shared_bound_program_ ? 1 : 0);
    cf_perf_metric_set("shared_bound_root_target_filter_decisions",shared_target_filter_decisions_);
    cf_perf_metric_set("shared_bound_should_nodes",shared_bound_should_nodes_);
    cf_perf_metric_set("shared_bound_private_or_drivers",shared_bound_private_or_drivers_);
    cf_perf_metric_set("functional_composed_program_used",functional_composed_program_ ? 1 : 0);
    cf_perf_metric_set("shared_request_frame_visits",shared_request_frame_visits_);
    cf_perf_metric_set("shared_live_checks",shared_live_checks_);
    cf_perf_metric_set("shared_formula_visits",shared_formula_visits_);
    cf_perf_metric_set("shared_child_route_checks",shared_child_route_checks_);
    cf_perf_metric_set("bound_slot_checks",bound_slot_checks_);
    cf_perf_metric_set("collective_record_probes",collective_record_probes_);
    cf_perf_metric_set("collective_slot_checks",collective_slot_checks_);
    cf_perf_metric_set("collective_input_reads",collective_input_reads_);
}

std::size_t composed_bound_bytes()const {
    std::size_t bytes=0;
    std::set<const composed_windows::Cells*> counted;
    std::set<const composed_windows::RankMajor*> banks;
    for(const auto &leaf:composed_bound_leaves_)for(const auto &node:leaf.nodes)
        if(counted.insert(node.cells.data.get()).second) {
            bytes+=node.cells.bytes();const auto bank=node.cells.data->rank_major();
            if(bank && banks.insert(bank).second)bytes+=bank->bytes();
        }
    return bytes;
}

#include "composed_shared_walk.inc"
#include "composed_collective.inc"

std::string composed_bound_plan_dump()const {
    std::string out="[";
#if CF_DIAGNOSTIC_COUNTERS
    bool first=true;
    for(std::size_t leaf=0;leaf<composed_bound_leaves_.size();++leaf)
        for(const auto &node:composed_bound_leaves_[leaf].nodes) {
            if(!node.connection)continue;
            const auto shared_group=shared_bound_group_for_node(node);
            const auto *g=shared_group<shared_bound_groups_.size() ? &shared_bound_groups_[shared_group] : nullptr;
            if(!first)out+=",";first=false;
            out+="{\"leaf\":"+std::to_string(leaf)+",\"occurrence\":"+std::to_string(node.occurrence)+
                ",\"entered_column\":"+json_quote(node.connection->entries[0].candidate.key())+
                ",\"cache_index\":"+json_quote(node.connection->entries.size()>1U ? "existing_posting_position" : "entering_rank")+
                ",\"probe\":"+json_quote(node.has_probe ? node.probe.key() : "")+
                ",\"lower\":"+std::to_string(node.lower)+",\"upper\":"+std::to_string(node.upper)+
                ",\"probes\":"+std::to_string(node.probes)+",\"hits\":"+std::to_string(node.hits)+
                ",\"fills\":"+std::to_string(node.fills)+",\"bytes\":"+std::to_string(node.cells.bytes())+
                ",\"arrivals\":"+std::to_string(node.arrivals)+",\"undecided_arrivals\":"+std::to_string(node.misses)+
                ",\"undecided_target_rows\":"+std::to_string(node.undecided_target_rows)+
                ",\"cache_miss_target_rows\":"+std::to_string(node.cache_miss_target_rows)+
                ",\"point_requests\":"+std::to_string(node.point_requests)+",\"full_window_requests\":"+std::to_string(node.full_requests)+
                ",\"first_witness_stops\":"+std::to_string(node.first_stops)+",\"point_pruned_rows\":"+std::to_string(node.point_pruned)+
                ",\"partial_fills\":"+std::to_string(node.partial_fills)+",\"complete_fills\":"+std::to_string(node.complete_fills)+
                ",\"partial_reopens\":"+std::to_string(node.reopens)+",\"unique_records_stored\":"+std::to_string(node.unique_records)+
                ",\"shared_connection_node\":"+(g ? std::to_string(shared_group) : "-1")+
                ",\"branch_mask\":"+std::to_string(g ? g->leaves : std::uint64_t{1}<<leaf)+
                ",\"execution_strategy\":"+json_quote(node.functional_tail ? "functional_dense_bounds_shared_lookup" : node.connection->unique || node.connection->entries.size()>1U ? "functional_row_shared_children" : "grouped_shared_slice")+
                ",\"functional_requests\":"+std::to_string(node.functional_requests)+
                ",\"dense_truth_gathers\":"+std::to_string(node.dense_gathers)+
                ",\"rank_major_record_bytes\":"+std::to_string(node.cells.data->rank_major() ? node.cells.data->rank_major()->stride() : 0U)+
                ",\"negative_only_read_participations\":"+std::to_string(node.negative_only_reads)+
                ",\"negative_exclusive_reads\":"+std::to_string(node.negative_exclusive_reads)+
                ",\"shared_decision_cells\":"+std::to_string(shared_bound_cell_identity(node))+
                ",\"connection_entries\":"+std::to_string(g ? node.functional_tail ? node.connection->rank_reads : g->entries : 0U)+
                ",\"connection_rank_reads\":"+std::to_string(node.connection->rank_reads)+
                ",\"connection_slice_reads\":"+std::to_string(node.connection->slice_reads)+
                ",\"shared_witness_rows\":"+std::to_string(g ? g->rows : 0U)+
                ",\"targets_decided_after_node\":"+std::to_string(g ? g->root_decisions : 0U)+"}";
        }
#endif
    return out+"]";
}

std::string composed_bound_requests_dump()const {
    std::string out="[";
#if CF_DIAGNOSTIC_COUNTERS
    for(std::size_t i=0;i<composed_bound_leaves_.size();++i) {
        const auto &leaf=composed_bound_leaves_[i];if(i)out+=",";
        out+="{\"request\":"+std::to_string(i)+",\"undecided_rows\":"+std::to_string(leaf.arrivals)+
            ",\"target_filtered\":"+std::to_string(leaf.target_filtered)+
            ",\"root_bound_reads\":"+std::to_string(leaf.root_reads)+
            ",\"body_passes\":"+std::to_string(leaf.body_passes)+
            ",\"negative_polarity\":"+std::to_string((shared_negative_leaves_>>i)&1U)+
            ",\"positive_polarity\":"+std::to_string((shared_positive_leaves_>>i)&1U)+
            ",\"negative_only_physical_reads_all_requests\":"+std::to_string(negative_only_physical_reads_)+"}";
    }
#endif
    return out+"]";
}
