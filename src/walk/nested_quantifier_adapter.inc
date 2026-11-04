inline bool shared_flat_quantifiers(const PolicyEngineInputC*in,int target){
    if(!cf_decision_sharing)return false;
    std::vector<nested_walk::Atom>a;std::map<int,int> ids;std::map<std::string,unsigned> columns;
    auto ref=[&](const ColumnRef&r){auto item=columns.emplace(r.key(),columns.size());return nested_walk::Ref{r.node_id,item.first->second};};
    for(int i=0;i<in->atom_count;++i){auto x=normalize_atom(in->atoms[i]);nested_walk::Atom y;y.left=ref(x.left);y.constant=x.right_is_const;y.op=x.op;if(!y.constant)y.right=ref(x.right);ids[x.atom_id]=a.size();a.push_back(y);}
    struct Item{int id;std::vector<int> locals;};std::vector<Item> stack;std::vector<nested_walk::Expr>e;
    const int begin=in->target_ast_tok_offsets[target],count=in->target_ast_tok_counts[target];
    for(int i=0;i<count;++i){const auto t=in->target_ast_toks[begin+i];nested_walk::Expr x;using K=nested_walk::Kind;
        if(t.kind==8){if(stack.empty())return false;stack.back().locals.push_back(t.value);continue;}
        if(t.kind==POLICY_AST_TOK_VAR){x.kind=K::atom;x.value=ids.at(t.value);}
        else if(t.kind==POLICY_AST_TOK_TRUE)x.kind=K::yes;else if(t.kind==POLICY_AST_TOK_FALSE)x.kind=K::no;
        else if(t.kind==POLICY_AST_TOK_NOT||t.kind==POLICY_AST_TOK_EXISTS){if(stack.empty())return false;auto v=stack.back();stack.pop_back();x.left=v.id;x.locals=v.locals;x.kind=t.kind==POLICY_AST_TOK_NOT?K::negation:K::exists;}
        else if(t.kind==POLICY_AST_TOK_AND||t.kind==POLICY_AST_TOK_OR){if(stack.size()<2)return false;x.right=stack.back().id;stack.pop_back();x.left=stack.back().id;stack.pop_back();x.kind=t.kind==POLICY_AST_TOK_AND?K::conjunction:K::disjunction;}else return false;
        e.push_back(x);stack.push_back({int(e.size()-1),{}});
    }
    if(stack.size()!=1)return false;return nested_walk::flat_scope::lower(a,e,stack.back().id,in->target_node_ids?in->target_node_ids[target]:0,false).routed;
}

// Scoped requests use the SAME immutable CFI2/CIX2 universes as the fused walk.
// This adapter supplies the block, tight-slice, unique-hop and kept strategies
// of nested_walk::Executor. No PG query or new artifact is issued here.
inline bool needs_scoped_quantifiers(const PolicyEngineInputC *in,int target) {
    if(!in->target_ast_toks || !in->target_ast_tok_offsets || !in->target_ast_tok_counts)return false;
    const int begin=in->target_ast_tok_offsets[target],count=in->target_ast_tok_counts[target];
    if(begin<0 || count<=0 || begin>in->target_ast_tok_len-count)fail("invalid scoped AST range");
    struct Item {bool quantified=false,negated=false;std::set<int> refs,binders;};std::vector<Item> stack;
    const int target_node=in->target_node_ids?in->target_node_ids[target]:0;
    for(int i=0;i<count;++i){auto tok=in->target_ast_toks[begin+i];
        // A lexical binder labels an EXISTS; it does not make it nested.
        // Flat quantified policies must retain the existing fused strategies.
        if(tok.kind==8){if(stack.empty() || tok.value<0)fail("invalid lexical binder");
            if(!stack.back().binders.insert(tok.value).second)return true;continue;}
        if(tok.kind==POLICY_AST_TOK_VAR || tok.kind==POLICY_AST_TOK_TRUE || tok.kind==POLICY_AST_TOK_FALSE){
            Item item;
            if(tok.kind==POLICY_AST_TOK_VAR){bool found=false;
                for(int j=0;j<in->atom_count;++j)if(in->atoms[j].atom_id==tok.value){
                    const auto &a=in->atoms[j];item.refs.insert(a.lhs_node_id);
                    if(a.rhs_schema_key && a.rhs_schema_key[0])item.refs.insert(a.rhs_node_id);
                    found=true;break;}
                if(!found)fail("scoped AST references absent atom");}
            stack.push_back(std::move(item));}
        else if(tok.kind==POLICY_AST_TOK_NOT){if(stack.empty())fail("malformed scoped NOT");stack.back().negated=true;}
        else if(tok.kind==POLICY_AST_TOK_EXISTS){if(stack.empty())fail("malformed scoped EXISTS");
            if(stack.back().quantified || stack.back().negated)return true;
            auto &item=stack.back();
            if(!item.binders.empty()){
                // Do not flatten malformed, unused or cross-scope binders:
                // retain the scoped validator instead of dropping ownership.
                for(int ref:item.refs)if(ref!=target_node && !item.binders.count(ref))return true;
                for(int local:item.binders)if(local==target_node || !item.refs.count(local))return true;
                for(int local:item.binders)item.refs.erase(local);
                item.binders.clear();
            }
            item.quantified=true;}
        else if(tok.kind==POLICY_AST_TOK_AND || tok.kind==POLICY_AST_TOK_OR){if(stack.size()<2)fail("malformed scoped Boolean AST");
            auto b=stack.back();stack.pop_back();stack.back().quantified|=b.quantified;stack.back().negated|=b.negated;
            stack.back().refs.insert(b.refs.begin(),b.refs.end());stack.back().binders.insert(b.binders.begin(),b.binders.end());}
        else fail("unsupported scoped AST token");
    }
    return shared_flat_quantifiers(in,target);
}

class NestedQuantifierRuntime {
    const PolicyArtifactCNew *arts_;int art_count_;const PolicyEngineInputC *in_;
    std::vector<ColumnIndex> columns_;
    std::map<std::string,unsigned> column_ids_;
    std::map<std::string,DomainIndex> domains_;
    std::vector<nested_walk::Atom> atoms_;
    std::vector<nested_walk::Expr> expressions_;
    std::unique_ptr<nested_walk::Executor<NestedQuantifierRuntime>> executor_;
    std::uint64_t envelope_reserved_bytes_=0;
    bool started_=false;
    std::string diagnostic_snapshot_;
    std::chrono::steady_clock::time_point diagnostic_next_;
    std::vector<unsigned> diagnostic_branches_;

    nested_walk::flat_scope::Result flat_scope_route_;
    unsigned compile(const ColumnRef &ref){
        auto old=column_ids_.find(ref.key());if(old!=column_ids_.end())return old->second;
        ColumnIndex out;out.domain=domain_for_column(arts_,art_count_,in_,ref.key());
        auto dom=domains_.find(out.domain);
        if(dom==domains_.end()){
            const auto view=lookup_required(arts_,art_count_,in_,"universe/domain/"+out.domain);
            DomainIndex d;d.values=universe_format::Dictionary::decode(view.data,view.len);
            d.count=d.values.count;d.numeric_kind=d.values.numeric_kind;domains_.emplace(out.domain,d);
        }
        const auto inv="canon_invidx/"+ref.table+"/"+ref.column;
        out.cix=decode_cix(lookup_required(arts_,art_count_,in_,inv),inv);
        const auto name="canon_fwdidx/"+ref.table+"/"+ref.column;
        const auto fwd=lookup_required(arts_,art_count_,in_,name);
        if(fwd.len<16 || std::memcmp(fwd.data,"CFI2",4)!=0 || u32le(fwd.data+12)!=0 ||
            u32le(fwd.data+8)!=out.cix.rank_count || fwd.len!=16ULL+4ULL*u32le(fwd.data+4))fail("invalid scoped CFI2 "+name);
        out.forward_rows=u32le(fwd.data+4);out.forward_ranks=reinterpret_cast<const std::uint32_t*>(fwd.data+16);
        if(domains_.at(out.domain).count!=out.cix.rank_count || out.forward_rows!=out.cix.row_count)
            fail("scoped column rank/row count mismatch "+name);
        const auto id=columns_.size();columns_.push_back(out);column_ids_[ref.key()]=id;return id;
    }
    std::pair<std::uint32_t,std::uint32_t> bounds(unsigned column,std::string_view literal){
        auto &dom=domains_.at(columns_[column].domain);
        const auto compare=[&](unsigned rank){auto value=dom.values.value(rank);
            return dom.numeric_kind?rankfix_numeric_compare(value,literal,dom.numeric_kind):value.compare(literal);};
        unsigned lo=0,hi=dom.count;while(lo<hi){auto mid=lo+(hi-lo)/2;if(compare(mid)<0)lo=mid+1;else hi=mid;}
        return {lo,lo+(lo<dom.count && compare(lo)==0)};
    }
public:
    NestedQuantifierRuntime(const PolicyArtifactCNew *arts,int art_count,const PolicyEngineInputC *in,
        int target_index,int target_node):arts_(arts),art_count_(art_count),in_(in){
        std::map<int,int> atom_ids;
        for(int i=0;i<in->atom_count;++i){auto a=normalize_atom(in->atoms[i]);
            nested_walk::Atom out;out.left={a.left.node_id,compile(a.left)};out.op=a.op;out.constant=a.right_is_const;
            if(a.right_is_const)std::tie(out.lower,out.upper)=bounds(out.left.column,a.literal);
            else{out.right={a.right.node_id,compile(a.right)};
                if(columns_[out.left.column].domain!=columns_[out.right.column].domain)
                    fail("nested comparison crosses canonical universes");}
            atom_ids[a.atom_id]=atoms_.size();atoms_.push_back(out);
        }
        struct Item {int expression;std::vector<int> binders;};std::vector<Item> stack;
        const int begin=in->target_ast_tok_offsets[target_index],count=in->target_ast_tok_counts[target_index];
        for(int i=0;i<count;++i){auto token=in->target_ast_toks[begin+i];nested_walk::Expr e;
            using K=nested_walk::Kind;
            if(token.kind==8){if(stack.empty() || token.value<0)fail("invalid lexical quantifier binder");
                stack.back().binders.push_back(token.value);continue;}
            if(token.kind==POLICY_AST_TOK_VAR){e.kind=K::atom;e.value=atom_ids.at(token.value);}
            else if(token.kind==POLICY_AST_TOK_TRUE)e.kind=K::yes;
            else if(token.kind==POLICY_AST_TOK_FALSE)e.kind=K::no;
            else if(token.kind==POLICY_AST_TOK_NOT || token.kind==POLICY_AST_TOK_EXISTS){
                if(stack.empty())fail("malformed scoped unary expression");auto child=stack.back();stack.pop_back();
                e.left=child.expression;e.kind=token.kind==POLICY_AST_TOK_NOT?K::negation:K::exists;
                e.locals=std::move(child.binders);
            }else if(token.kind==POLICY_AST_TOK_AND || token.kind==POLICY_AST_TOK_OR){
                if(stack.size()<2)fail("malformed scoped binary expression");
                e.right=stack.back().expression;stack.pop_back();e.left=stack.back().expression;stack.pop_back();
                e.kind=token.kind==POLICY_AST_TOK_AND?K::conjunction:K::disjunction;
            }else fail("unsupported scoped expression token");
            expressions_.push_back(std::move(e));stack.push_back({int(expressions_.size()-1),{}});
        }
        if(stack.size()!=1)fail("scoped postfix AST did not reduce");
        // Flat sibling EXISTS have no outer lexical locals beyond the target.
        // Infer and alpha-rename only that unambiguous case. Nested scopes keep
        // the existing explicit-binder validation and execution unchanged.
        flat_scope_route_=nested_walk::flat_scope::lower(atoms_,expressions_,stack.back().expression,target_node);
        // Explicit binders are required: references alone cannot distinguish
        // an inner local from a correlated outer value used only in the inner.
        for(auto &e:expressions_)if(e.kind==nested_walk::Kind::exists && e.locals.empty())
            fail("nested EXISTS requires explicit lexical occurrence binders");
        diagnostic_branches_.resize(atoms_.size());unsigned diagnostic_branch=0;
        std::function<void(int,unsigned)> mark_branch=[&](int id,unsigned branch){const auto&e=expressions_[id];
            if(e.kind==nested_walk::Kind::exists&&!branch)branch=++diagnostic_branch;
            if(e.kind==nested_walk::Kind::atom)diagnostic_branches_[e.value]=branch;
            if(e.left>=0)mark_branch(e.left,branch);if(e.right>=0)mark_branch(e.right,branch);};
        if(flat_scope_route_.routed)diagnostic_branches_=flat_scope_route_.atom_branch;
        else mark_branch(stack.back().expression,0);
        executor_=std::make_unique<nested_walk::Executor<NestedQuantifierRuntime>>(*this,atoms_,expressions_,
            stack.back().expression,target_node,cf_decision_store!=0 && cf_composed_reuse,cf_run_reuse,
            cf_interval_edges && cf_component_boundaries,79 | (cf_decision_sharing?128:0) | (cf_nested_theta_transfer?16:0) | (cf_nested_equality_ranges?32:0),
            std::uint64_t(std::max(cf_cost_dense_budget_mb,0))*1024*1024,
            !GetConfigOptionByName("memento_diagnostic.frontier_cost_guard",nullptr,true)||std::string(GetConfigOptionByName("memento_diagnostic.frontier_cost_guard",nullptr,true))!="off");
    }
    void interrupt(){
#if CF_DIAGNOSTIC_COUNTERS
        if(!diagnostic_snapshot_.empty()&&(QueryCancelPending||ProcDiePending||std::chrono::steady_clock::now()>=diagnostic_next_)){
            diagnostic_next_=std::chrono::steady_clock::now()+std::chrono::seconds(5);publish_diagnostics();}
#endif
        CHECK_FOR_INTERRUPTS();
    }
    std::uint32_t rank(unsigned column,std::uint32_t row){
        if(!started_)fail("nested witness read before target arrival");
        const auto &c=columns_.at(column);if(row>=c.forward_rows)fail("nested row out of bounds");return c.forward_ranks[row];
    }
    unsigned ranks(unsigned column){return columns_.at(column).cix.rank_count;}
    unsigned present_ranks(unsigned column){return columns_.at(column).cix.present_count;}
    unsigned rows(unsigned column){return columns_.at(column).forward_rows;}
    bool unique(unsigned column){return columns_.at(column).cix.unique;}
    std::uint64_t slice_rows(unsigned column,unsigned rank){
        const auto &c=columns_.at(column).cix;
        return rank<c.rank_count?std::uint64_t(c.end(rank)-c.begin(rank)):0;
    }
    bool allow_dense(unsigned column){return (std::uint64_t(ranks(column))+3)/4<=std::uint64_t(std::max(cf_cost_dense_budget_mb,0))*1024*1024;}
    bool allow_envelope(unsigned column,unsigned){
        // Two partial window banks (good and nogood), not just two-bit cells.
        const auto count=std::uint64_t(ranks(column));
        const auto bytes=2*((count+3)/4+8*count);
        const auto budget=std::uint64_t(std::max(cf_cost_dense_budget_mb,0))*1024*1024;
        if(bytes>budget || envelope_reserved_bytes_>budget-bytes)return false;
        envelope_reserved_bytes_+=bytes;return true;
    }
    template<class Visitor>void visit(unsigned column,int op,unsigned pivot,Visitor visitor){
        const auto &c=columns_.at(column).cix;
        if(op==1){if(pivot>=c.rank_count)return;
            for(auto pos=c.begin(pivot);pos<c.end(pivot);++pos)if(visitor(u32le(c.child_rows+4ULL*pos)))return;
            return;
        }
        // Read only the admitted existing rank slices. The per-row tight loop
        // checks the compiled scope formula and stops at its first witness.
        for(unsigned i=0;i<c.present_count;++i){const auto rank=u32le(c.present+4ULL*i);
            if(!nested_walk::compare(rank,op,pivot))continue;
            for(auto pos=c.begin(rank);pos<c.end(rank);++pos)if(visitor(u32le(c.child_rows+4ULL*pos)))return;
        }
    }
    std::vector<std::uint64_t> run(unsigned rows){
        const unsigned bitmap_rows=rows;
#if CF_DIAGNOSTIC_COUNTERS
        // Planning-only observation: zero target arrivals, the same compiled
        // plan/budgets, and a full-length all-zero bitmap. Never a timed mode.
        const char *plan_only=GetConfigOption("memento_diagnostic.plan_only",true,false);
        if(plan_only && std::strcmp(plan_only,"on")==0)rows=0;
#endif
#if CF_DIAGNOSTIC_COUNTERS
        const auto snapshot=GetConfigOption("memento_diagnostic.snapshot",true,false);
        if(snapshot&&snapshot[0]=='/')
            diagnostic_snapshot_=snapshot;
        diagnostic_next_=std::chrono::steady_clock::now()+std::chrono::seconds(5);
        if(!diagnostic_snapshot_.empty())publish_diagnostics();
#endif
        started_=true;auto result=executor_->run(rows);result.resize((std::uint64_t(bitmap_rows)+63)/64,0);        publish_diagnostics();return result;
    }
    void publish_diagnostics(){
        const auto &c=executor_->counters;
        cf_perf_metric_set("target_evals",c.target_evals);cf_perf_metric_set("allowed_rows",c.allowed_rows);
        cf_perf_metric_set("witness_tuples_read",c.witness_rows);
        cf_perf_metric_set("decisions_stored",executor_->store().size()+executor_->store().summary_size());
        cf_perf_metric_set("hits_good",executor_->store().good_hits);cf_perf_metric_set("hits_nogood",executor_->store().no_good_hits);
        cf_perf_metric_set("rows_read_before_first_target",0);
        cf_perf_metric_set("nested_formula_path_used",1);
        cf_perf_metric_set("scoped_quantifier_path_used",1);
        cf_perf_metric_set("block_loop_used",c.block_words>0);
        cf_perf_metric_set("tight_loop_used",c.tight_slice_rows>0);
        cf_perf_metric_set("run_rows_saved",c.run_rows_saved);
        cf_perf_metric_set("nested_quantifier_calls",c.quantifier_calls);
        cf_perf_metric_set("nested_maximum_depth",c.maximum_depth);
        cf_perf_metric_set("nested_unique_hops",c.unique_hops);
        cf_perf_metric_set("nested_kept_hits",c.kept_hits);
        cf_perf_metric_set("nested_scope_splits",c.scope_splits);
        cf_perf_metric_set("nested_split_components",c.split_components);
        cf_perf_metric_set("nested_exact_probes",c.exact_probes);
        cf_perf_metric_set("nested_exact_fills",c.exact_fills);
        cf_perf_metric_set("nested_exact_hits",c.exact_hits);
        cf_perf_metric_set("nested_outer_dependency_declines",c.outer_dependency_declines);
        cf_perf_metric_set("nested_coequal_checks",c.coequal_checks);
        cf_perf_metric_set("nested_coequal_rejections",c.coequal_rejections);
        cf_perf_metric_set("nested_prefix_context_elisions",c.prefix_context_elisions);
        cf_perf_metric_set("nested_functional_context_elisions",c.functional_context_elisions);
        cf_perf_metric_set("nested_formula_updates",c.formula_updates);
        cf_perf_metric_set("nested_request_arrivals",c.request_arrivals);
        cf_perf_metric_set("nested_request_decisions",c.request_decisions);
        cf_perf_metric_set("nested_compiled_target_used",executor_->compiled_target());
        cf_perf_metric_set("nested_compiled_rows",c.compiled_rows);
        cf_perf_metric_set("nested_compiled_parts",c.compiled_parts);
        cf_perf_metric_set("nested_compiled_fallbacks",c.compiled_fallbacks);
        cf_perf_metric_set("nested_compiled_table_probes",c.compiled_table_probes);
        cf_perf_metric_set("nested_hash_decisions",executor_->store().entries.size());
        cf_perf_metric_set("nested_dense_probes",c.dense_probes);
        cf_perf_metric_set("nested_dense_hits",c.dense_hits);
        cf_perf_metric_set("nested_dense_fills",c.dense_fills);
        cf_perf_metric_set("nested_packed_probes",c.packed_probes);
        cf_perf_metric_set("nested_packed_hits",c.packed_hits);
        cf_perf_metric_set("nested_packed_fills",c.packed_fills);
        cf_perf_metric_set("nested_gate_bypasses",c.gate_bypasses);
        cf_perf_metric_set("nested_word_hop_probes",c.word_hop_probes);
        cf_perf_metric_set("nested_word_hop_hits",c.word_hop_hits);
        cf_perf_metric_set("nested_word_hop_fills",c.word_hop_fills);
        cf_perf_metric_set("nested_partial_nogood_probes",c.partial_nogood_probes);
        cf_perf_metric_set("nested_partial_nogood_hits",c.partial_nogood_hits);
        cf_perf_metric_set("nested_partial_nogood_fills",c.partial_nogood_fills);
        cf_perf_metric_set("nested_bits_settled_without_read",c.bits_settled_without_read);
        cf_perf_metric_set("nested_rows_skipped",c.rows_skipped);
        cf_perf_metric_set("nested_word_budget_declines",executor_->store().word_budget_declines);
        cf_perf_metric_set("nested_word_envelope_probes",c.word_envelope_probes);
        cf_perf_metric_set("nested_word_envelope_hits",c.word_envelope_hits);
        cf_perf_metric_set("nested_word_envelope_fills",c.word_envelope_fills);
        cf_perf_metric_set("nested_word_envelope_pieces",executor_->store().word_envelopes.pieces);
        cf_perf_metric_set("nested_word_envelope_bytes",executor_->store().word_envelopes.bytes);
        cf_perf_metric_set("nested_no_repeat_gates_off",executor_->store().gates_off);
        cf_perf_metric_set("nested_first_witness_stops",c.first_witness_stops);
        cf_perf_metric_set("nested_exhaustions",c.exhaustions);
        cf_perf_metric_set("nested_tight_slice_rows",c.tight_slice_rows);
        cf_perf_metric_set("nested_formula_instructions",c.formula_instructions);
        cf_perf_metric_set("nested_block_words",c.block_words);
        cf_perf_metric_set("nested_dense_decisions",executor_->store().dense_entries);
        cf_perf_metric_set("nested_envelope_should_apply",c.envelope_should_apply);
        cf_perf_metric_set("nested_envelope_probes",c.envelope_probes);
        cf_perf_metric_set("nested_envelope_hits",c.envelope_hits);
        cf_perf_metric_set("nested_envelope_fills",c.envelope_fills);
        cf_perf_metric_set("nested_envelope_declined",c.envelope_declined);
        cf_perf_metric_set("nested_envelope_invalidated",c.envelope_invalidated);
        auto plan=std::string("{\"executor\":\"scoped_quantifier_program\",\"nested_quantifiers\":true,\"maximum_depth\":")+
            std::to_string(c.maximum_depth)+",\"compiled_boolean_formula\":true,\"tight_slice_rows\":"+
            std::to_string(c.tight_slice_rows)+",\"shared_scope_graph\":"+(executor_->shared_scope_graph()?"true":"false")+
            ",\"shared_scope_nodes\":"+std::to_string(executor_->shared_scope_nodes())+",\"unique_hops\":"+std::to_string(c.unique_hops)+
            ",\"kept_hits\":"+std::to_string(c.kept_hits)+",\"target_blocks\":"+std::to_string(c.block_words)+
            ",\"run_rows_saved\":"+std::to_string(c.run_rows_saved)+
            ",\"envelope_should_apply\":"+std::to_string(c.envelope_should_apply)+
            ",\"envelope_hits\":"+std::to_string(c.envelope_hits)+
            ",\"envelope_fills\":"+std::to_string(c.envelope_fills)+",\"node_attribution\":[";
        const auto quoted=[](const std::string &value){
            std::string out="\"";const char *hex="0123456789abcdef";
            for(unsigned char ch:value){if(ch=='\"' || ch=='\\')out+='\\';
                if(ch<32){out+="\\u00";out+=hex[ch>>4];out+=hex[ch&15];}else out+=char(ch);}
            return out+'\"';
        };
        const auto name=[&](unsigned id){for(const auto &item:column_ids_)if(item.second==id)return item.first;
            return std::string("unknown_column_")+std::to_string(id);};
        bool node_comma=false;
        executor_->visit_node_work([&](auto scope,auto stage,auto occurrence,auto predicate,const auto &w){
            if(node_comma)plan+=',';node_comma=true;
            plan+="{\"scope\":"+std::to_string(scope)+",\"stage\":"+std::to_string(stage)+
                ",\"occurrence\":"+std::to_string(occurrence)+",\"predicate_id\":"+std::to_string(predicate)+
                ",\"request_plan\":"+quoted(w.positional?"positional_union":"whole_scope")+
                ",\"union_rest\":"+(w.union_rest?"true":"false")+
                ",\"request_width\":"+std::to_string(w.request_width)+
                ",\"entering_column\":"+quoted(w.column==UINT32_MAX?"not_reached":name(w.column))+
                ",\"arrivals\":"+std::to_string(w.arrivals)+",\"distinct_entering_ranks\":"+std::to_string(w.distinct)+
                ",\"witness_rows\":"+std::to_string(w.witness_rows)+
                ",\"dense_probes\":"+std::to_string(w.dense_probes)+",\"dense_hits\":"+std::to_string(w.dense_hits)+
                ",\"dense_fills\":"+std::to_string(w.dense_fills)+
                ",\"packed_probes\":"+std::to_string(w.packed_probes)+",\"packed_hits\":"+std::to_string(w.packed_hits)+
                ",\"packed_fills\":"+std::to_string(w.packed_fills)+
                ",\"boundary_probes\":"+std::to_string(w.boundary_probes)+",\"boundary_hits\":"+std::to_string(w.boundary_hits)+
                ",\"boundary_fills\":"+std::to_string(w.boundary_fills)+
                ",\"word_hop_probes\":"+std::to_string(w.word_hop_probes)+
                ",\"word_hop_hits\":"+std::to_string(w.word_hop_hits)+
                ",\"word_hop_fills\":"+std::to_string(w.word_hop_fills)+
                ",\"partial_nogood_probes\":"+std::to_string(w.partial_nogood_probes)+
                ",\"partial_nogood_hits\":"+std::to_string(w.partial_nogood_hits)+
                ",\"partial_nogood_fills\":"+std::to_string(w.partial_nogood_fills)+
                ",\"bits_settled_without_read\":"+std::to_string(w.bits_settled_without_read)+
                ",\"rows_skipped\":"+std::to_string(w.rows_skipped)+
                ",\"summary_arrivals\":"+std::to_string(w.summary_arrivals)+",\"summary_hits\":"+std::to_string(w.summary_hits)+
                ",\"summary_fills\":"+std::to_string(w.summary_fills)+",\"frontier_points\":"+std::to_string(w.frontier_points)+
                "}";
        });
        plan+="],\"flat_scope_routing\":{\"used\":"+std::string(flat_scope_route_.routed?"true":"false")+
            ",\"branches\":"+std::to_string(flat_scope_route_.flat_branches)+",\"shared_skeletons\":"+std::to_string(flat_scope_route_.shared_skeletons)+"},\"request_groups\":[";
        bool group_comma=false;
        executor_->visit_compiled_groups([&](auto group,auto bit,auto scope,const auto&locals,const auto&used,const auto&drivers,const auto&mandatory){
            if(group_comma)plan+=',';group_comma=true;std::set<unsigned> branches;
            for(auto index:used)if(index<int(diagnostic_branches_.size())&&diagnostic_branches_[index])branches.insert(diagnostic_branches_[index]);
            plan+="{\"group\":"+std::to_string(group)+",\"request_bit\":"+std::to_string(bit)+",\"scope\":"+std::to_string(scope)+",\"branches\":[";
            bool comma=false;for(auto b:branches){if(comma)plan+=',';comma=true;plan+=std::to_string(b);}plan+="],\"stages\":[";
            for(unsigned k=0;k<drivers.size();++k){if(k)plan+=',';const auto&d=drivers[k];unsigned equalities=0;
                for(auto a:mandatory){const auto&x=atoms_[a];if(!x.constant&&x.op==1&&(x.left.occurrence==locals[k]||x.right.occurrence==locals[k]))++equalities;}
                plan+="{\"stage\":"+std::to_string(k)+",\"entering_column\":"+quoted(name(d.column))+",\"source_column\":"+quoted(name(d.source.column))+
                    ",\"mandatory_equalities_touching_local\":"+std::to_string(equalities)+"}";
            }
            plan+="]}";
        });
        plan+="],\"summary_stage_attribution\":[";bool summary_stage_comma=false;
        executor_->visit_summary_work([&](auto id,auto step,auto scope,auto stage,auto occurrence,auto column,const auto&users,const auto&w){
            if(summary_stage_comma)plan+=',';summary_stage_comma=true;
            plan+="{\"plan\":"+std::to_string(id)+",\"step\":"+std::to_string(step)+",\"scope\":"+std::to_string(scope)+",\"stage\":"+std::to_string(stage)+
                ",\"occurrence\":"+std::to_string(occurrence)+",\"entering_column\":"+quoted(name(column))+",\"arrivals\":"+std::to_string(w.arrivals)+
                ",\"summary_arrivals\":"+std::to_string(w.summary_arrivals)+",\"summary_hits\":"+std::to_string(w.summary_hits)+",\"summary_fills\":"+std::to_string(w.summary_fills)+
                ",\"witness_rows\":"+std::to_string(w.witness_rows)+",\"frontier_points\":"+std::to_string(w.frontier_points)+",\"rows_skipped\":"+std::to_string(w.rows_skipped)+",\"request_scopes\":[";
            bool comma=false;for(auto user:users){if(comma)plan+=',';comma=true;plan+=std::to_string(user);}plan+="]}";
        });
        plan+="],\"summary_eligibility\":[";bool eligibility_comma=false;
        executor_->visit_summary_eligibility([&](auto scope,const auto&locals,const auto&used,auto bank,auto column,auto tests,const auto&reason){
            if(eligibility_comma)plan+=',';eligibility_comma=true;
            plan+="{\"scope\":"+std::to_string(scope)+",\"plan\":"+std::to_string(bank)+",\"eligible\":"+(bank>=0?"true":"false")+
                ",\"entering_column\":"+quoted(column==UINT32_MAX?"not_planned":name(column))+",\"tests\":"+std::to_string(tests)+",\"reason\":"+quoted(reason)+",\"locals\":[";
            bool comma=false;for(auto local:locals){if(comma)plan+=',';comma=true;plan+=std::to_string(local);}plan+="],\"atoms\":[";
            comma=false;for(auto atom:used){if(comma)plan+=',';comma=true;plan+=std::to_string(atom);}plan+="],\"branches\":[";
            std::set<unsigned> branches;for(auto atom:used)if(atom<int(diagnostic_branches_.size())&&diagnostic_branches_[atom])branches.insert(diagnostic_branches_[atom]);
            comma=false;for(auto branch:branches){if(comma)plan+=',';comma=true;plan+=std::to_string(branch);}plan+="]}";
        });
        plan+="],\"sorted_rank_summaries\":[";bool sorted_comma=false;
        executor_->visit_sorted_summaries([&](auto id,const auto&bank){
            if(sorted_comma)plan+=',';sorted_comma=true;
            plan+="{\"id\":"+std::to_string(id)+",\"form\":\"sorted_nonnull_ranks\",\"entering_column\":"+quoted(name(bank.column))+
                ",\"storage\":\"common_rank_cells\""+
                ",\"value_column\":"+quoted(bank.value_column==UINT32_MAX?"none":name(bank.value_column))+",\"probes\":"+std::to_string(bank.probes)+",\"hits\":"+std::to_string(bank.hits)+
                ",\"fills\":"+std::to_string(bank.fills)+",\"witness_rows\":"+std::to_string(bank.rows)+",\"empty_range_rejections\":"+std::to_string(bank.empty_rejections)+
                ",\"rows_skipped\":"+std::to_string(bank.rows_skipped)+",\"reserved_bytes\":"+std::to_string(bank.reserved_bytes)+",\"stored_bytes\":"+std::to_string(bank.stored_bytes())+
                ",\"temporary_fill_bytes\":"+std::to_string(bank.temporary_bytes)+",\"sort_comparisons\":"+std::to_string(bank.sort_comparisons)+",\"binary_steps\":"+std::to_string(bank.binary_steps)+
                ",\"fill_active\":"+(bank.fill_active?"true":"false")+",\"active_rank\":"+std::to_string(bank.active_rank)+",\"request_scopes\":[";
            bool sep=false;for(auto scope:bank.requests){if(sep)plan+=',';sep=true;plan+=std::to_string(scope);}plan+="],\"equality_prefix\":[";
            sep=false;for(auto column:bank.equality_columns){if(sep)plan+=',';sep=true;plan+=quoted(name(column));}plan+="]}";
        });
        plan+="],\"rank_summaries\":[";

        bool summary_comma=false;
        executor_->visit_summaries([&](auto id,auto scope,auto column,const auto &users,const auto &bank){
            if(summary_comma)plan+=',';summary_comma=true;
            plan+="{\"id\":"+std::to_string(id)+",\"scope\":"+std::to_string(scope)+
                ",\"storage\":\"common_rank_cells\",\"common_witness_bytes\":"+std::to_string(bank.cells.bytes())+
                ",\"shared_group\":"+std::to_string(executor_->shared_scope_group(scope))+
                ",\"entering_column\":"+quoted(name(column))+",\"request_scopes\":[";
            bool sep=false;for(auto user:users){if(sep)plan+=',';sep=true;plan+=std::to_string(user);}
            plan+="],\"form\":"+quoted(bank.merged_mode?"merged_conjunctive_frontier":bank.theta_mode?"theta_transferred_decision":bank.decision_mode?(bank.decisions.filled_operand?"request_boundary_masks":"request_verdict_mask"):
                unique(column)?"functional_point":"complete_witness_frontier")+",\"dimensions\":"+std::to_string(bank.merged_mode?bank.merged.dimensions:bank.dimensions)+
                ",\"merged_request_count\":"+std::to_string(bank.merged_request_count)+
                ",\"stored_vectors\":"+std::to_string(bank.merged_mode?bank.payload().masks.size():bank.payload().points.size())+
                ",\"merged_rows_read\":"+std::to_string(bank.merged_rows_read)+
                ",\"merged_equality_dimensions\":"+std::to_string(bank.merged.equalities.size())+
                ",\"raw_tests_before_folding\":"+std::to_string(bank.raw_tests)+
                ",\"common_constants_folded\":"+std::to_string(bank.folded_constant_tests)+
                ",\"frontier_arrivals\":"+std::to_string(bank.frontier_arrivals)+
                ",\"equality_dimension_mask\":"+std::to_string(bank.equality_dimensions())+
                ",\"equality_searches\":"+std::to_string(bank.equality_searches)+
                ",\"equality_key_comparisons\":"+std::to_string(bank.equality_key_comparisons)+
                ",\"equality_group_hits\":"+std::to_string(bank.equality_group_hits)+
                ",\"equality_group_misses\":"+std::to_string(bank.equality_group_misses)+
                ",\"equality_points_excluded\":"+std::to_string(bank.equality_points_excluded)+
                ",\"ungrouped_points_checked\":"+std::to_string(bank.ungrouped_points_checked)+
                ",\"probes\":"+std::to_string(bank.probes)+",\"hits\":"+std::to_string(bank.hits)+
                ",\"fills\":"+std::to_string(bank.fills)+",\"points\":"+std::to_string(bank.merged_mode?bank.payload().masks.size():bank.payload().points.size())+
                ",\"reserved_bytes\":"+std::to_string(bank.reserved_bytes)+
                ",\"stored_bytes\":"+std::to_string(bank.stored_bytes())+
                ",\"temporary_fill_bytes\":"+std::to_string(bank.fill_input_bytes+bank.reduction_temporary_bytes)+
                ",\"fill_rows_visited\":"+std::to_string(bank.fill_rows_visited)+
                ",\"measured_frontier_admission\":"+(bank.measured_admission?"true":"false")+
                ",\"frontier_bank_dropped\":"+(bank.frontier_dropped?"true":"false")+
                ",\"frontier_admission_decision\":"+quoted(!bank.measured_admission?"not_applicable":bank.frontier_dropped?"drop_entries_exceed_quarter_of_entry_rows_read":bank.admission_judged?"keep_entries_at_most_quarter_of_entry_rows_read":bank.frontier_fill_attempts?"probation_awaiting_evidence":"not_reached")+
                ",\"frontier_minimum_evidence_rows\":"+std::to_string(bank.frontier_minimum_rows)+
                ",\"frontier_admission_judged\":"+(bank.admission_judged?"true":"false")+
                ",\"frontier_admission_basis\":"+quoted(bank.admission_basis==1?"100000_rows":bank.admission_basis==2?"all_present_rank_slices_collected":bank.admission_basis==3?"target_walk_finished":"awaiting_evidence")+
                ",\"frontier_present_ranks_filled\":"+std::to_string(bank.present_ranks_filled)+
                ",\"frontier_present_rank_slices_at_decision\":"+std::to_string(bank.judgment_present_rank_slices)+
                ",\"frontier_present_rank_upper_bound\":"+std::to_string(bank.present_ranks)+
                ",\"frontier_walk_finished\":"+(bank.frontier_walk_finished?"true":"false")+
                ",\"frontier_first_judgment_rows\":"+std::to_string(bank.first_judgment_rows)+
                ",\"frontier_first_judgment_entries\":"+std::to_string(bank.first_judgment_entries)+
                ",\"frontier_first_judgment_basis\":"+std::to_string(bank.first_judgment_basis)+
                ",\"frontier_admission_rows\":"+std::to_string(bank.measured_rows)+
                ",\"frontier_admission_entries_at_decision\":"+std::to_string(bank.decision_entries)+
                ",\"frontier_fill_attempts\":"+std::to_string(bank.frontier_fill_attempts)+
                ",\"frontier_suppressed_probes\":"+std::to_string(bank.suppressed_probes)+
                ",\"dominance_flag_tables\":"+std::to_string(bank.flag_tables.size())+
                ",\"dominance_flag_table_builds\":"+std::to_string(bank.flag_tables_built)+
                ",\"neq_operator_dimensions\":"+std::to_string(bank.any_neq_dimensions())+
                ",\"neq_collective_dimensions\":"+std::to_string(bank.neq_dimensions())+
                ",\"neq_pure_dimensions\":"+std::to_string(bank.pure_neq_dimensions())+
                ",\"neq_dimensions_seen\":"+std::to_string(bank.neq_dimensions_seen)+
                ",\"neq_certificate_attempts\":"+std::to_string(bank.neq_certificate_attempts)+
                ",\"neq_eligibility_checks\":"+std::to_string(bank.neq_eligibility_checks)+
                ",\"neq_certificates\":"+std::to_string(bank.neq_certificates)+
                ",\"neq_points_removed\":"+std::to_string(bank.neq_points_removed)+
                ",\"neq_search_steps\":"+std::to_string(bank.neq_search_steps)+
                ",\"reduction_points_visited\":"+std::to_string(bank.reduction_points_visited)+
                ",\"dominance_comparisons\":"+std::to_string(bank.dominance_comparisons)+
                ",\"collection_ns\":"+std::to_string(bank.collection_ns)+",\"reduction_ns\":"+std::to_string(bank.reduction_ns)+",\"probe_ns\":"+std::to_string(bank.probe_ns)+
                ",\"estimated_rows_per_rank\":"+std::to_string(bank.estimated_rows_per_rank)+",\"estimated_points_per_rank\":"+std::to_string(bank.estimated_points_per_rank)+
                ",\"estimated_repeats\":"+std::to_string(bank.estimated_repeats)+",\"estimated_summary_work\":"+std::to_string(bank.estimated_summary_work)+",\"estimated_walk_work\":"+std::to_string(bank.estimated_walk_work)+
                ",\"fill_active\":"+(bank.fill_active?"true":"false")+
                ",\"active_rank\":"+std::to_string(bank.active_rank)+
                ",\"complete_candidates\":"+std::to_string(bank.candidates)+",\"dominated\":"+std::to_string(bank.dominated)+
                ",\"point_checks\":"+std::to_string(bank.checks)+
                ",\"request_width\":"+std::to_string(bank.merged_mode?bank.merged_request_count:bank.theta_mode?bank.theta.width:bank.decisions.width)+
                ",\"frontier_points_per_filled_rank\":"+std::to_string(bank.fills&&!bank.decision_mode?double(bank.merged_mode?bank.payload().masks.size():bank.payload().points.size())/bank.fills:0.0)+
                ",\"maximum_frontier_points_per_rank\":"+std::to_string(bank.maximum_frontier)+
                ",\"frontier_payload_bytes\":"+std::to_string(bank.merged_mode?bank.merged.bytes():bank.payload().points.size()*sizeof(rank_summaries::Point))+
                ",\"collective_mask_reads\":"+std::to_string(bank.decisions.mask_checks+bank.theta.evaluations)+
                ",\"collective_fills\":"+std::to_string(bank.collective_fills)+
                ",\"collective_rows\":"+std::to_string(bank.collective_rows)+
                ",\"collective_formula_steps\":"+std::to_string(bank.collective_formula_steps)+
                ",\"collective_constant_comparisons\":"+std::to_string(bank.collective_comparisons)+
                ",\"collective_child_projections\":"+std::to_string(bank.collective_child_projections)+
                ",\"per_request_formula_evaluations\":"+std::to_string(bank.per_request_formula_evaluations)+
                ",\"theta_boundary_projections\":"+std::to_string(bank.theta.projections)+
                ",\"theta_dimensions\":"+std::to_string(bank.theta.dimensions)+
                ",\"boundary_fallbacks\":"+std::to_string(bank.decisions.fallbacks)+
                ",\"decision_payload_bytes\":"+std::to_string(bank.payload().answers.bytes()+bank.payload().theta.bytes())+
                ",\"rank_metadata_bytes\":"+std::to_string(bank.payload().slots.size()*sizeof(rank_summaries::Slot)+bank.reached_bits.size()*8)+
                ",\"bytes_per_allocated_rank\":"+std::to_string(bank.cells.count()?double(bank.payload().answers.bytes()+bank.payload().theta.bytes())/bank.cells.count():0.0)+
                ",\"retained_witness_rows\":0,\"retained_row_values\":0"+
                ",\"gate_basis\":\"total_targets_vs_distinct_entering_ranks_reached\",\"target_rows\":"+std::to_string(bank.target_rows)+
                ",\"distinct_entering_ranks_reached\":"+std::to_string((bank.decision_mode||bank.measured_admission)?bank.distinct_reached:bank.fills)+
                ",\"tablewide_gate\":"+(bank.tablewide?"true":"false")+
                ",\"gate_declines\":"+std::to_string(bank.gate_declines)+"}";
        });
        plan+="],\"equality_rank_decisions\":[";
        bool equality_comma=false;
        for(const auto &b:executor_->store().summaries)if(b.equality_mode){
            if(equality_comma)plan+=',';equality_comma=true;
            plan+="{\"entering_column\":"+quoted(name(b.column))+",\"parameter_column\":"+quoted(name(b.parameter_column))+
                ",\"form\":\"equality_range_decision\",\"probes\":"+std::to_string(b.probes)+",\"hits\":"+std::to_string(b.hits)+
                ",\"fills\":"+std::to_string(b.fills)+",\"range_comparisons\":"+std::to_string(b.range_comparisons)+
                ",\"decision_payload_bytes\":"+std::to_string(b.stored_bytes())+",\"retained_row_values\":0}";
        }
        plan+="],\"functional_rank_facts\":[";
        bool facts_comma=false;
        for(const auto &facts:executor_->store().summaries)if(facts.fact_mode){
            if(facts_comma)plan+=',';facts_comma=true;
            plan+="{\"entering_column\":"+quoted(name(facts.column))+",\"columns\":[";
            bool sep=false;for(auto col:facts.fact_columns){if(sep)plan+=',';sep=true;plan+=quoted(name(col));}
            plan+="],\"probes\":"+std::to_string(facts.probes)+",\"hits\":"+std::to_string(facts.hits)+
                ",\"fills\":"+std::to_string(facts.fills)+",\"request_arrivals\":"+std::to_string(facts.fact_requests)+"}";
        }
        plan+="],\"word_gate_populations\":[";bool population_comma=false;
        for(const auto&s:executor_->store().predicates)if(s.word&&s.word_tablewide){
            if(population_comma)plan+=',';population_comma=true;
            plan+="{\"predicate_id\":"+std::to_string(s.predicate_id)+",\"basis\":\"cumulative_saved_reads_after_table_coverage_or_planned_arrivals\",\"present_entering_ranks\":"+std::to_string(s.table_present)+
                ",\"distinct_entering_ranks_reached\":"+std::to_string(s.table_distinct)+",\"planned_arrivals\":"+std::to_string(s.table_horizon)+",\"probes\":"+std::to_string(s.total_probes)+",\"hits\":"+std::to_string(s.total_hits)+
                ",\"saved_reads\":"+std::to_string(s.saved_reads)+",\"enabled\":"+(s.enabled?"true":"false")+"}";
        }
        plan+="],\"predicate_gates\":[";
        bool comma=false;
        executor_->visit_predicates([&](auto id,auto column,const auto &filled,auto cardinality,
            auto probes,auto hits,auto window_probes,auto window_hits,auto last_probes,auto last_hits,
            auto saved_reads,bool enabled,auto threshold,bool tablewide,const char *form){
            if(comma)plan+=',';comma=true;
            plan+="{\"predicate_id\":"+std::to_string(id)+",\"store_type\":"+quoted(form)+",\"entering_column\":"+quoted(name(column))+
                ",\"entering_rank_universe_count\":"+std::to_string(cardinality)+",\"filled_operands\":[";
            bool sep=false;for(auto ref:filled){if(sep)plan+=',';sep=true;
                plan+="{\"occurrence\":"+std::to_string(ref.occurrence)+",\"column\":"+quoted(name(ref.column))+"}";}
            plan+="],\"probes\":"+std::to_string(probes)+",\"hits\":"+std::to_string(hits)+
                ",\"repeat_fraction\":"+std::to_string(probes?double(hits)/probes:0.0)+
                ",\"window_probes\":"+std::to_string(window_probes)+",\"window_hits\":"+std::to_string(window_hits)+
                ",\"last_window_probes\":"+std::to_string(last_probes)+",\"last_window_hits\":"+std::to_string(last_hits)+
                ",\"saved_reads\":"+std::to_string(saved_reads)+",\"threshold\":"+std::to_string(threshold)+
                ",\"gate\":"+quoted(!enabled?"off_no_repeat":probes==0?"unused":tablewide?"on_tablewide":probes<threshold?"probation":"on")+"}";
        });
        plan+="]}";
        cf_perf_cost_plan_set(plan.c_str());
#if CF_DIAGNOSTIC_COUNTERS
        if(!diagnostic_snapshot_.empty()){
            const auto temporary=diagnostic_snapshot_+".tmp";
            {std::ofstream output(temporary);output<<"{\"targets_done\":"<<c.target_evals<<",\"allowed_rows\":"<<c.allowed_rows<<",\"witness_rows\":"<<c.witness_rows<<",\"plan\":"<<plan<<"}";}
            if(::chmod(temporary.c_str(),0644)!=0)throw std::runtime_error("cannot make diagnostic snapshot readable");
            std::rename(temporary.c_str(),diagnostic_snapshot_.c_str());
        }
#endif
    }
};
