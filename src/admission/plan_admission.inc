// Structural traffic estimates from headers, before the first target row.
std::vector<double> planned_arrivals_;
std::vector<double> planned_leaf_arrivals_;
double target_rows_estimate_=0;
struct CostAdmission {
    std::size_t node,leaf;bool tail;double ratio;std::uint32_t id;
    double independent_ratio=0,arrivals=0;
    std::vector<ColumnRef> columns;
};
std::vector<CostAdmission> cost_admissions_;
void configure_arrival_estimates() {
    for(const auto &entry:column_id_by_key_)
        if(entry.first.rfind(target_+".",0)==0)
            target_rows_estimate_=std::max(target_rows_estimate_,double(columns_[entry.second].forward_rows));
    planned_leaf_arrivals_.assign(leaves_.size(),target_rows_estimate_);
    for(std::size_t leaf=0;leaf<leaves_.size();++leaf) {
        std::map<std::size_t,double> fractions;
        for(const auto *atom:dag_[0].filters_by_leaf[leaf]) {
            if(!cf_cost_target_fraction)break;
            if(!atom->right_is_const || atom->left.node_id!=target_node_)continue;
            auto &idx=column(atom->left);
            const auto lookup=constant_lookup(*atom,idx);
            // Offset reads count matches; no posting or witness row is read.
            const double fraction=target_rows_estimate_ ?
                double(posting_rows(idx,lookup))/target_rows_estimate_ : 0;
            auto inserted=fractions.emplace(atom->left.runtime_column,fraction);
            if(!inserted.second)inserted.first->second=std::min(inserted.first->second,fraction);
        }
        // Different columns give marginal estimates, not an exact joint count.
        for(const auto &entry:fractions)planned_leaf_arrivals_[leaf]*=entry.second;
    }
    planned_arrivals_.assign(dag_.size(),0);planned_arrivals_[0]=target_rows_estimate_;
    const auto visit=[&](auto &&self,std::size_t parent)->void {
        for(auto child:dag_[parent].children) {
            const auto leaf=static_cast<std::size_t>(__builtin_ctzll(dag_[child].leaves));
            const auto &edge=*dag_[child].edge_by_leaf[leaf];
            const auto &source=dag_[child].candidate_is_left_by_leaf[leaf] ? edge.right : edge.left;
            const auto &h=column(source).cix;
            const auto fanout=h.present_count ? double(h.row_count)/h.present_count : 0;
            const auto arrivals=parent==0 ? planned_leaf_arrivals_[leaf] : planned_arrivals_[parent];
            planned_arrivals_[child]=std::min(1e100,arrivals*fanout);
            self(self,child);
        }
    };
    visit(visit,0U);
}
void report_cost_admissions() {
#if CF_DIAGNOSTIC_COUNTERS
    std::string text="{\"target_rows\":"+std::to_string(target_rows_estimate_)+",\"leaf_arrivals\":[";
    for(std::size_t i=0;i<planned_leaf_arrivals_.size();++i) {
        if(i)text+=",";text+=std::to_string(planned_leaf_arrivals_[i]);
    }
    text+="],\"columns\":[";bool first_column=true;
    for(const auto &entry:column_id_by_key_) {
        if(!first_column)text+=",";first_column=false;
        std::ostringstream name;name<<std::quoted(entry.first);
        text+="{\"id\":"+std::to_string(entry.second)+",\"column\":"+name.str()+"}";
    }
    text+="],\"nodes\":[";
    for(std::size_t i=0;i<cost_admissions_.size();++i) {
        const auto &a=cost_admissions_[i];if(i)text+=",";
        const auto ordinal=a.id&((1U<<RankPredicateInstance::arity_shift)-1U);
        const auto hits=a.id && ordinal<rank_store_.predicates.size() ? rank_store_.predicates[ordinal].total_hits : 0U;
        text+="{\"node\":"+std::to_string(a.node)+",\"leaf\":"+std::to_string(a.leaf)+
            ",\"tail\":"+std::to_string(a.tail)+",\"predicted_repeats\":"+std::to_string(a.ratio)+
            ",\"probes\":"+std::to_string(rank_node_probes_[a.node])+
            ",\"writes\":"+std::to_string(rank_node_writes_[a.node])+",\"hits\":"+std::to_string(hits)+
            ",\"gate\":\""+(!a.id ? "off_predicted" : cf_cost_single_visit && a.ratio>=4 ? "immediate" : "probation")+"\""+
            ",\"independent_predicted_repeats\":"+std::to_string(a.independent_ratio)+
            ",\"predicted_arrivals\":"+std::to_string(a.arrivals)+",\"rank_and_filled_predicate\":[";
        for(std::size_t operand=0;operand<a.columns.size();++operand) {
            if(operand)text+=",";
            const auto &ref=a.columns[operand];std::ostringstream name;name<<std::quoted(ref.key());
            auto without=a.columns;without.erase(without.begin()+operand);
            text+="{\"role\":\""+std::string(operand ? "filled_predicate_operand" : "entering_rank")+
                "\",\"column\":"+name.str()+",\"occurrence\":"+std::to_string(ref.node_id)+
                ",\"present_ranks\":"+std::to_string(column(ref).cix.present_count)+
                ",\"predicted_repeats_without_operand\":"+
                std::to_string(rank_predicate_repeat_ratio(a.leaf,a.arrivals,without))+"}";
        }
        text+="]}";
    }
    text+="],\"caches\":[";bool first=true;
    const auto cache=[&](const char *kind,std::size_t column,bool enabled,double ratio,
                         std::uint64_t probes,std::uint64_t hits,std::uint64_t entries) {
        if(!first)text+=",";first=false;
        text+="{\"kind\":\""+std::string(kind)+"\",\"column\":"+std::to_string(column)+
            ",\"enabled\":"+std::to_string(enabled)+",\"predicted_repeats\":"+std::to_string(ratio)+
            ",\"probes\":"+std::to_string(probes)+",\"hits\":"+std::to_string(hits)+
            ",\"entries\":"+std::to_string(entries)+"}";
    };
    for(const auto &entry:chain_steps_) {
        const auto &s=*entry.second;
        cache("hop",s.source.runtime_column,s.cache_hop,decision_repeat_ratio(target_rows_estimate_,{s.source}),
              s.cache_probes,s.cache_hits,s.cache_entries);
    }
    for(std::size_t leaf=0;leaf<chain_plans_.size();++leaf) {
        const auto &plan=chain_plans_[leaf];
        for(const auto &s:plan.slots)if(!s.direct)
            cache("slot",s.root.runtime_column,s.cache_slot,decision_repeat_ratio(planned_leaf_arrivals_[leaf],{s.root}),
                  s.cache_probes,s.cache_hits,s.cache_entries);
        for(const auto &g:plan.guards)
            cache("guard",g.root.runtime_column,!g.key_single_visit,decision_repeat_ratio(planned_leaf_arrivals_[leaf],{g.root}),
                  g.cache_probes,g.cache_hits,g.cache_entries);
    }
    for(const auto &entry:kept_roots_) {
        const auto &root=entry.second;
        cache("composed",root.root.runtime_column,true,
              decision_repeat_ratio(target_rows_estimate_,{root.root}),root.probes,root.probes-root.misses,root.misses);
    }
    text+="],\"entering_columns\":[";
    bool first_input=true;
    for(const auto &entry:column_id_by_key_)if(entry.first.rfind(target_+".",0)==0) {
        if(!first_input)text+=",";first_input=false;
        std::ostringstream name;name<<std::quoted(entry.first);text+=name.str();
    }
    text+="],\"terminal_cache_costs\":[";bool first_terminal=true;
    for(const auto &group:terminal_groups_)if(group.child_columns.size()>1U) {
        if(!first_terminal)text+=",";first_terminal=false;
        const auto &cost=group.cost;
        text+="{\"node\":"+std::to_string(group.node)+",\"mode\":"+std::to_string(group.cache_mode)+
            ",\"arrivals\":"+std::to_string(cost.arrivals)+",\"distinct\":"+std::to_string(cost.distinct)+
            ",\"shortest_expected_posting\":"+std::to_string(cost.reads)+
            ",\"scan_units\":"+std::to_string(cost.scan)+",\"lookup_units\":"+std::to_string(cost.lookup)+
            ",\"build_units\":"+std::to_string(cost.build)+
            ",\"first_touch_units\":"+std::to_string(cost.cold)+
            ",\"without_cache_units\":"+std::to_string(cost.without_cache)+
            ",\"with_cache_units\":"+std::to_string(cost.with_cache)+
            ",\"probes\":"+std::to_string(group.probes)+",\"hits\":"+std::to_string(group.hits)+
            ",\"writes\":"+std::to_string(group.writes)+",\"scan_reads\":"+std::to_string(group.scan_reads)+"}";
    }
    text+="],\"walk_dag\":"+walk_dag_dump()+",\"compiled_loops\":[";
    for(std::size_t i=0;i<compiled_loop_recipes_.size();++i){if(i)text+=",";text+=compiled_loop_recipes_[i];}
    text+="],\"composed_bound_nodes\":"+composed_bound_plan_dump()+
        ",\"composed_bound_requests\":"+composed_bound_requests_dump()+"}";cf_perf_cost_plan_set(text.c_str());
#endif
}
double decision_repeat_ratio(double arrivals,const std::vector<ColumnRef> &keys) {
    std::set<std::pair<int,std::size_t>> seen;
    double distinct=1;
    for(const auto &key:keys)if(seen.emplace(key.node_id,key.runtime_column).second)
        distinct=std::min(1e100,distinct*std::max(1U,column(key).cix.present_count));
    return arrivals/distinct;
}
double rank_predicate_repeat_ratio(std::size_t leaf,double arrivals,const std::vector<ColumnRef> &keys) {
    using Key=filled_predicate_reuse::Key;
    std::vector<Key> input;
    for(const auto &key:keys)input.emplace_back(key.node_id,key.runtime_column);
    std::vector<std::pair<Key,Key>> equalities;
    for(const auto *atom:leaves_[leaf]->atoms)
        if(!atom->right_is_const && atom->op==POLICY_OP_EQ)
            equalities.push_back({{atom->left.node_id,atom->left.runtime_column},{atom->right.node_id,atom->right.runtime_column}});
    const auto distinct=filled_predicate_reuse::distinct_estimate(input,equalities,[&](Key key) {
        const auto &c=columns_.at(key.second);
        return filled_predicate_reuse::Header{double(c.forward_rows),double(c.cix.present_count)};
    });
    return arrivals/distinct;
}
