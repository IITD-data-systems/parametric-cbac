// Diagnostic-only structural dump; no addresses, data cells, elapsed times,
// private merge-key spelling or policy-dependent artifact selection.
static std::string json_quote(const std::string &value) {
    std::ostringstream stream;stream<<std::quoted(value);return stream.str();
}
void record_compiled_loop(const TightBranch &branch,std::size_t order) {
#if CF_DIAGNOSTIC_COUNTERS
    const auto &plan=chain_plans_[branch.leaf];
    std::string recipe=branch.composed && kept_leaves_[branch.leaf].single_root ? "lean_kept_verdict" :
        branch.composed && !branch.kept_groups.empty() ? "lean_compact_endpoints" :
        branch.composed ? "lean_composed" : branch.projected ? "lean_projected" :
        branch.ranked ? "lean_ranked" : branch.packed_ranked ? "lean_packed" : "lean_window";
    std::string text="{\"order\":"+std::to_string(order)+",\"leaf\":"+std::to_string(branch.leaf)+
        ",\"loop\":"+json_quote(recipe)+",\"store\":"+std::to_string(!branch.key_single_visit)+
        ",\"sparse\":"+std::to_string(branch.sparse)+",\"own\":"+
        std::to_string(!dag_[0].filters_by_leaf[branch.leaf].empty() || !dag_[0].boolean_groups_by_leaf[branch.leaf].empty())+
        ",\"front\":"+std::to_string(!plan.dense_front.empty())+",\"direct_residual\":"+std::to_string(plan.direct_residual)+
        ",\"global\":"+std::to_string(branch.global)+",\"above\":"+std::to_string(branch.above)+
        ",\"packed_operands\":"+std::to_string(branch.operands.size())+
        ",\"block\":"+std::to_string(branch.block_batched)+",\"target_only\":"+std::to_string(branch.block_target_only)+
        ",\"block_cells\":"+std::to_string(branch.block_planned_cells)+",\"block_bytes\":"+std::to_string(branch.block_planned_bytes)+
        ",\"run_columns\":"+std::to_string(branch.run_columns.size())+",\"kept_groups\":[";
    for(std::size_t g=0;g<branch.kept_groups.size();++g) {
        if(g)text+=",";const auto &group=branch.kept_groups[g];
        text+="{\"root\":"+json_quote(group.use->root->root.key())+",\"widths\":[";
        for(std::size_t i=0;i<group.values.size();++i) {
            if(i)text+=",";text+=std::to_string(group.use->root->ranks.width(group.values[i].field));
        }
        text+="]}";
    }
    text+="]}";compiled_loop_recipes_.push_back(std::move(text));
#endif
}
std::string walk_dag_dump()const {
    std::string text="[";
    for(std::size_t n=0;n<dag_.size();++n) {
        if(n)text+=",";const auto &node=dag_[n];
        text+="{\"node\":"+std::to_string(n)+",\"table\":"+json_quote(node.table)+
            ",\"leaves\":"+std::to_string(node.leaves)+",\"children\":[";
        for(std::size_t i=0;i<node.children.size();++i){if(i)text+=",";text+=std::to_string(node.children[i]);}
        text+="],\"requests\":[";bool first=true;
        for(auto bits=node.leaves;bits;bits&=bits-1U) {
            if(!first)text+=",";first=false;const auto leaf=unsigned(__builtin_ctzll(bits));
            text+="{\"leaf\":"+std::to_string(leaf)+",\"occurrence\":"+std::to_string(node.occurrence_by_leaf[leaf]);
            if(n) {
                const auto &edge=*node.edge_by_leaf[leaf];const bool left=node.candidate_is_left_by_leaf[leaf];
                text+=",\"parent_column\":"+json_quote((left ? edge.right : edge.left).key())+
                    ",\"candidate_column\":"+json_quote((left ? edge.left : edge.right).key())+
                    ",\"operator\":"+json_quote(op_name(normalized_edge_op(edge,left)));
            }
            text+=",\"equalities\":[";
            for(std::size_t i=0;i<node.equalities_by_leaf[leaf].size();++i){if(i)text+=",";text+=json_quote(atom_proof_identity(*node.equalities_by_leaf[leaf][i]));}
            text+="],\"filters\":[";
            for(std::size_t i=0;i<node.filters_by_leaf[leaf].size();++i){if(i)text+=",";text+=json_quote(atom_proof_identity(*node.filters_by_leaf[leaf][i]));}
            text+="],\"boolean\":[";bool group_first=true;
            for(const auto *group:node.boolean_groups_by_leaf[leaf]) {
                if(!group_first)text+=",";group_first=false;text+="[";
                for(std::size_t i=0;i<group->postfix.size();++i) {
                    if(i)text+=",";const auto &token=group->postfix[i];
                    text+=json_quote(token.kind==LocalBooleanTokenKind::atom ? atom_proof_identity(*token.atom) :
                        token.kind==LocalBooleanTokenKind::conjunction ? "AND" : "OR");
                }
                text+="]";
            }
            text+="]}";
        }
        text+="]}";
    }
    return text+"]";
}
