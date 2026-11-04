#include "our_pg_uniform.h"
#include "rank_decision_store.h"
#include "rankfix_values.h"
#include "exec_metrics.h"
#include "interval_coverage.h"
#include "universe_format.h"
#include "identity_ranks.h"
#include "reached_cells.h"
#include "lazy_group_map.h"
#include "artifact_allowlist.h"
#include "tuple_index.h"
#include "iterator_isolation.h"
#include "node_solver_binding.h"
#include "mixed_requests.h"
#include "shared_envelope.h"
#include "filled_predicate_repeats.h"
#include "posting_position.h"
#include "composed_windows.h"
#include "nested_quantifier_walk.h"
#include "flat_scope_routing.h"
#include <fstream>

extern "C" {
#include "postgres.h"
#include "miscadmin.h"
#include "utils/lsyscache.h"
#include "utils/guc.h"
#include "utils/memutils.h"
#include "catalog/namespace.h"
#include "catalog/pg_type_d.h"
extern int cf_decision_store;
extern bool cf_composite_edges;
extern bool cf_interval_edges;
extern bool cf_chain_projection;
extern bool cf_chain_boundaries;
extern bool cf_composite_cost;
extern bool cf_engine_profile;
extern bool cf_cost_single_visit;
extern bool cf_cost_branch_order;
extern bool cf_cost_present_caps;
extern bool cf_cost_dense_budget;
extern int cf_cost_dense_budget_mb;
extern bool cf_cost_hop_elision;
extern bool cf_cost_target_fraction;
extern bool cf_cost_group_maps;
extern bool cf_block_target_loop;
extern bool cf_composed_reuse;
extern bool cf_run_reuse;
extern bool cf_decision_sharing;
extern bool cf_posting_position_store;
extern bool cf_composed_bounds;
extern int cf_block_target_rows;
extern bool cf_tight_loop;
extern bool cf_component_boundaries;
extern bool cf_nested_theta_transfer;
extern bool cf_nested_equality_ranges;
extern bool cf_formula_rank_cache;
extern bool cf_rankstore_dump;
}
#if !CF_DIAGNOSTIC_COUNTERS
#define cf_engine_profile false
#endif

#include <algorithm>
#include <iomanip>
#include <array>
#include <cerrno>
#include <charconv>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <limits>
#include <map>
#include <memory>
#include <set>
#include <string>
#include <string_view>
#include <tuple>
#include <unordered_map>
#include <utility>
#include <vector>
#include "kept_chains.h"
#include "composite_cache_cost.h"

namespace memento_runtime __attribute__((visibility("hidden"))) {





[[noreturn]] inline void fail(const std::string &message) {
    ereport(ERROR, (errmsg("our_pg: %s", message.c_str())));
    std::abort();
}

inline std::uint32_t u32le(const unsigned char *p) {
    return static_cast<std::uint32_t>(p[0]) |
           (static_cast<std::uint32_t>(p[1]) << 8U) |
           (static_cast<std::uint32_t>(p[2]) << 16U) |
           (static_cast<std::uint32_t>(p[3]) << 24U);
}

struct ArtifactView {
    const unsigned char *data = nullptr;
    std::size_t len = 0;
};

inline ArtifactView lookup_required(const PolicyArtifactCNew *arts,
                             int art_count,
                             const PolicyEngineInputC *in,
                             const std::string &name) {
    if (!pac_artifact_name_allowed(name.c_str())) fail("Forbidden artifact: "+name);
    for (int i = 0; i < art_count; ++i) {
        if (arts != nullptr && arts[i].name != nullptr &&
            std::strcmp(arts[i].name, name.c_str()) == 0) {
            if (arts[i].data == nullptr && arts[i].len != 0U)
                fail("null artifact data for " + name);
            return {static_cast<const unsigned char *>(arts[i].data), arts[i].len};
        }
    }
    const void *data = nullptr;
    std::size_t len = 0;
    if (in == nullptr || in->artifact_lookup_fn == nullptr ||
        !in->artifact_lookup_fn(in->artifact_lookup_ctx, name.c_str(), &data, &len))
        fail("missing required artifact " + name);
    if (data == nullptr && len != 0U)
        fail("artifact callback returned null data for " + name);
    return {static_cast<const unsigned char *>(data), len};
}

inline ArtifactView lookup_optional(const PolicyArtifactCNew *arts, int art_count,
                             const PolicyEngineInputC *in, const std::string &name) {
    if (!pac_artifact_name_allowed(name.c_str())) fail("Forbidden artifact: "+name);
    for (int i = 0; i < art_count; ++i)
        if (arts && arts[i].name && name == arts[i].name)
            return {static_cast<const unsigned char *>(arts[i].data), arts[i].len};
    const void *data = nullptr;
    std::size_t len = 0;
    if (!in || !in->artifact_lookup_fn ||
        !in->artifact_lookup_fn(in->artifact_lookup_ctx, name.c_str(), &data, &len))
        return {};
    return {static_cast<const unsigned char *>(data), len};
}

inline std::vector<std::string> text_lines(ArtifactView view) {
    std::vector<std::string> out;
    std::size_t begin = 0;
    while (begin < view.len) {
        std::size_t end = begin;
        while (end < view.len && view.data[end] != '\n') ++end;
        std::string line(reinterpret_cast<const char *>(view.data + begin), end - begin);
        if (!line.empty() && line.back() == '\r') line.pop_back();
        if (!line.empty()) out.push_back(std::move(line));
        begin = end < view.len ? end + 1U : end;
    }
    return out;
}

inline std::pair<std::string, std::string> split_schema_key(const char *raw) {
    if (raw == nullptr) fail("null schema key");
    std::string key(raw);
    if (key.rfind("const:", 0U) == 0U) key.erase(0U, 6U);
    else if (key.rfind("join:", 0U) == 0U) key.erase(0U, 5U);
    const std::size_t metadata = key.find(' ');
    if (metadata != std::string::npos) key.resize(metadata);
    const std::size_t dot = key.find('.');
    if (dot == std::string::npos || dot == 0U || dot + 1U >= key.size())
        fail("invalid schema key " + key);
    return {key.substr(0U, dot), key.substr(dot + 1U)};
}

inline std::string domain_for_column(const PolicyArtifactCNew *arts,
                              int art_count,
                              const PolicyEngineInputC *in,
                              const std::string &qualified) {
    const ArtifactView meta = lookup_required(arts, art_count, in, "meta/col_domain");
    for (const std::string &line : text_lines(meta)) {
        const std::size_t eq = line.find('=');
        if (eq != std::string::npos && line.substr(0U, eq) == qualified)
            return line.substr(eq + 1U);
    }
    fail("column absent from meta/col_domain: " + qualified);
}

struct CixView {
    std::uint32_t rank_count=0, row_count=0, present_count=0;
    bool unique=false;
    const unsigned char *offsets=nullptr,*child_rows=nullptr,*present=nullptr;
    std::uint32_t begin(std::uint32_t rank) const { return u32le(offsets+4ULL*rank); }
    std::uint32_t end(std::uint32_t rank) const { return u32le(offsets+4ULL*(rank+1)); }
    std::uint32_t logical_offset(std::uint32_t rank) const { return begin(rank); }
    std::uint32_t forward_rank(std::uint32_t rank) const { return rank; }
};

inline CixView decode_cix(ArtifactView view,const std::string &name) {
    try {
        const auto inv=universe_format::Inverted::decode(view.data,view.len);
        CixView out;out.rank_count=inv.ranks;out.row_count=inv.rows;out.present_count=inv.present_count;
        out.unique=inv.unique;out.offsets=inv.offsets;out.child_rows=inv.children;out.present=inv.present;
        return out;
    } catch(const std::exception &error) { fail(name+": "+error.what()); }
}

inline bool parse_number(std::string_view value, double *out) {
    std::string text(value);
    char *end = nullptr;
    errno = 0;
    const double parsed = std::strtod(text.c_str(), &end);
    if (errno != 0 || end == text.c_str() || *end != '\0' || !std::isfinite(parsed))
        return false;
    *out = parsed;
    return true;
}

inline int compare_values(std::string_view lhs, std::string_view rhs) {
    double a = 0.0;
    double b = 0.0;
    if (parse_number(lhs, &a) && parse_number(rhs, &b)) {
        if (a < b) return -1;
        if (a > b) return 1;
        return 0;
    }
    const int cmp = lhs.compare(rhs);
    return cmp < 0 ? -1 : cmp > 0 ? 1 : 0;
}

struct ColumnRef {
    std::string table;
    std::string column;
    int node_id = -1;
    
    
    
    
    std::size_t runtime_column = SIZE_MAX;
    std::string key() const { return table + "." + column; }
};

struct NormalizedAtom {
    int atom_id = 0;
    ColumnRef left;
    ColumnRef right;
    bool right_is_const = false;
    std::string literal;
    int universe = -1;
    int op = POLICY_OP_EQ;
    std::uint32_t constant_lower = 0;
    std::uint32_t constant_upper = 0;
    bool constant_compiled = false;
    
    
    std::uint64_t proof_bit = 0;
};

inline const char *op_name(int op) {
    switch (op) {
        case POLICY_OP_EQ: return "=";
        case POLICY_OP_LT: return "<";
        case POLICY_OP_LE: return "<=";
        case POLICY_OP_GT: return ">";
        case POLICY_OP_GE: return ">=";
        case POLICY_OP_NE: return "!=";
        default: return "?";
    }
}

inline std::string atom_proof_identity(const NormalizedAtom &atom) {
    std::string out = atom.left.key() + "|" + std::to_string(atom.op) + "|";
    if (atom.right_is_const)
        out += "const:" + atom.literal;
    else
        out += atom.right.key();
    return out;
}

inline int invert_op(int op) {
    switch (op) {
        case POLICY_OP_LT: return POLICY_OP_GT;
        case POLICY_OP_LE: return POLICY_OP_GE;
        case POLICY_OP_GT: return POLICY_OP_LT;
        case POLICY_OP_GE: return POLICY_OP_LE;
        case POLICY_OP_EQ:
        case POLICY_OP_NE: return op;
        default: fail("invalid comparison operator " + std::to_string(op));
    }
}

inline NormalizedAtom normalize_atom(const PolicyAtomC &atom) {
    NormalizedAtom out;
    out.atom_id = atom.atom_id;
    std::tie(out.left.table, out.left.column) = split_schema_key(atom.lhs_schema_key);
    out.left.node_id = atom.lhs_node_id;
    out.right_is_const = atom.rhs_schema_key == nullptr || atom.rhs_schema_key[0] == '\0';
    if (out.right_is_const) {
        if (atom.const_count != 1 || atom.const_values == nullptr ||
            atom.const_values[0] == nullptr)
            fail("atom y" + std::to_string(atom.atom_id) + " has invalid constant payload");
        out.literal = atom.const_values[0];
    } else {
        std::tie(out.right.table, out.right.column) = split_schema_key(atom.rhs_schema_key);
        out.right.node_id = atom.rhs_node_id;
    }
    out.universe = atom.domain_id >= 0 ? atom.domain_id : atom.join_class_id;
    out.op = atom.op == 0 ? POLICY_OP_EQ : atom.op;
    if (out.op < POLICY_OP_EQ || out.op > POLICY_OP_NE)
        fail("atom y" + std::to_string(atom.atom_id) + " has invalid operator");
    CF_METRICS_LOG(DEBUG1,
         "our_pg uniform_atom atom=y%d universe=%d op=%s rhs=%s lookup=lookup_rank_ranges",
         out.atom_id, out.universe, op_name(out.op),
         out.right_is_const ? "const" : "column");
    return out;
}

struct DomainIndex {
    universe_format::Dictionary values;
    std::uint32_t count=0;
    int numeric_kind=0;
};

struct ColumnIndex {
    std::string domain;
    CixView cix;
    const std::uint32_t *forward_ranks=nullptr;
    std::uint32_t forward_rows=0;
};

using RankRange = std::pair<std::uint32_t, std::uint32_t>;

struct LookupResult {
    std::array<RankRange, 2> ranges{{{0U, 0U}, {0U, 0U}}};
    int count = 0;
};

struct RawExpr {
    int kind = POLICY_AST_TOK_FALSE;
    int atom_id = 0;
    RawExpr *left = nullptr;
    RawExpr *right = nullptr;
};

enum class LocalBooleanTokenKind : std::uint8_t {
    atom,
    conjunction,
    disjunction
};

struct LocalBooleanToken {
    LocalBooleanTokenKind kind = LocalBooleanTokenKind::atom;
    const NormalizedAtom *atom = nullptr;
};

struct LocalBooleanGroup {
    std::vector<LocalBooleanToken> postfix;
    std::vector<const NormalizedAtom *> atoms;
    std::uint64_t proof_bit = 0;
};

struct FormulaNode {
    enum Kind { Branch, And, Or, Not, True, False } kind = False;
    std::size_t leaf_id = std::numeric_limits<std::size_t>::max();
    
    
    std::vector<const NormalizedAtom *> atoms;
    std::vector<LocalBooleanGroup> boolean_groups;
    std::unique_ptr<FormulaNode> left;
    std::unique_ptr<FormulaNode> right;
};

inline bool pure_conjunction(const RawExpr *node) {
    if (node == nullptr) return false;
    if (node->kind == POLICY_AST_TOK_VAR || node->kind == POLICY_AST_TOK_TRUE)
        return true;
    return node->kind == POLICY_AST_TOK_AND &&
           pure_conjunction(node->left) && pure_conjunction(node->right);
}

inline void collect_conjunction_atoms(const RawExpr *node, std::vector<int> *out) {
    if (node == nullptr || out == nullptr) return;
    if (node->kind == POLICY_AST_TOK_VAR) {
        out->push_back(node->atom_id);
    } else if (node->kind == POLICY_AST_TOK_AND) {
        collect_conjunction_atoms(node->left, out);
        collect_conjunction_atoms(node->right, out);
    }
}

inline bool contains_not(const RawExpr *node) {
    if (node == nullptr) return false;
    // A quantifier is a scope boundary even when its body is entirely positive.
    if (node->kind == POLICY_AST_TOK_NOT || node->kind == POLICY_AST_TOK_EXISTS) return true;
    return contains_not(node->left) || contains_not(node->right);
}

inline const NormalizedAtom *require_atom(
    int id,
    const std::unordered_map<int, const NormalizedAtom *> &atoms) {
    const auto found = atoms.find(id);
    if (found == atoms.end())
        fail("target AST references absent atom y" + std::to_string(id));
    return found->second;
}

inline void compile_local_boolean_group(
    const RawExpr *node,
    const std::unordered_map<int, const NormalizedAtom *> &atoms,
    LocalBooleanGroup *group) {
    if (node == nullptr || group == nullptr)
        fail("null factored Boolean group");
    if (node->kind == POLICY_AST_TOK_VAR) {
        const NormalizedAtom *atom = require_atom(node->atom_id, atoms);
        group->postfix.push_back(
            LocalBooleanToken{LocalBooleanTokenKind::atom, atom});
        if (std::find(group->atoms.begin(), group->atoms.end(), atom) ==
            group->atoms.end()) group->atoms.push_back(atom);
        return;
    }
    if (node->kind != POLICY_AST_TOK_AND && node->kind != POLICY_AST_TOK_OR)
        fail("unsupported token inside a positive Boolean group");
    compile_local_boolean_group(node->left, atoms, group);
    compile_local_boolean_group(node->right, atoms, group);
    group->postfix.push_back(LocalBooleanToken{
        node->kind == POLICY_AST_TOK_AND ?
            LocalBooleanTokenKind::conjunction :
            LocalBooleanTokenKind::disjunction,
        nullptr});
}

inline void compile_factored_positive_branch(
    const RawExpr *node,
    const std::unordered_map<int, const NormalizedAtom *> &atoms,
    FormulaNode *branch,
    std::set<int> *mandatory_seen) {
    if (node == nullptr || branch == nullptr || mandatory_seen == nullptr)
        fail("null factored positive branch");
    if (node->kind == POLICY_AST_TOK_AND) {
        compile_factored_positive_branch(
            node->left, atoms, branch, mandatory_seen);
        compile_factored_positive_branch(
            node->right, atoms, branch, mandatory_seen);
        return;
    }
    if (node->kind == POLICY_AST_TOK_VAR) {
        if (mandatory_seen->insert(node->atom_id).second)
            branch->atoms.push_back(require_atom(node->atom_id, atoms));
        return;
    }
    if (node->kind == POLICY_AST_TOK_TRUE) return;
    if (node->kind == POLICY_AST_TOK_FALSE)
        fail("FALSE inside a connected positive branch is unsupported");
    if (node->kind != POLICY_AST_TOK_OR)
        fail("NOT reached factored positive branch compiler");
    branch->boolean_groups.emplace_back();
    compile_local_boolean_group(
        node, atoms, &branch->boolean_groups.back());
}

inline std::unique_ptr<FormulaNode> compile_formula(
    const RawExpr *raw,
    const std::unordered_map<int, const NormalizedAtom *> &atoms) {
    if (raw == nullptr) fail("null formula node");
    if (raw->kind == POLICY_AST_TOK_EXISTS) {
        if (contains_not(raw->left))
            fail("nested quantifiers or NOT inside an EXISTS body are unsupported");
        auto branch = std::make_unique<FormulaNode>();
        branch->kind = FormulaNode::Branch;
        std::set<int> seen;
        compile_factored_positive_branch(raw->left, atoms, branch.get(), &seen);
        if (branch->atoms.empty() && branch->boolean_groups.empty())
            branch->kind = FormulaNode::True;
        return branch;
    }
    
    
    
    
    
    if (raw->kind == POLICY_AST_TOK_OR) {
        auto out = std::make_unique<FormulaNode>();
        out->kind = FormulaNode::Or;
        out->left = compile_formula(raw->left, atoms);
        out->right = compile_formula(raw->right, atoms);
        return out;
    }
    
    
    
    if (!contains_not(raw)) {
        auto branch = std::make_unique<FormulaNode>();
        branch->kind = FormulaNode::Branch;
        std::set<int> seen;
        compile_factored_positive_branch(raw, atoms, branch.get(), &seen);
        if (branch->atoms.empty() && branch->boolean_groups.empty()) {
            branch->kind = FormulaNode::True;
        }
        return branch;
    }
    auto out = std::make_unique<FormulaNode>();
    if (pure_conjunction(raw)) {
        std::vector<int> ids;
        collect_conjunction_atoms(raw, &ids);
        if (ids.empty()) {
            out->kind = FormulaNode::True;
            return out;
        }
        out->kind = FormulaNode::Branch;
        std::set<int> seen;
        for (int id : ids) {
            const auto found = atoms.find(id);
            if (found == atoms.end())
                fail("target AST references absent atom y" + std::to_string(id));
            if (seen.insert(id).second) out->atoms.push_back(found->second);
        }
        return out;
    }
    switch (raw->kind) {
        case POLICY_AST_TOK_TRUE: out->kind = FormulaNode::True; return out;
        case POLICY_AST_TOK_FALSE: out->kind = FormulaNode::False; return out;
        case POLICY_AST_TOK_NOT:
            out->kind = FormulaNode::Not;
            out->left = compile_formula(raw->left, atoms);
            return out;
        case POLICY_AST_TOK_AND: out->kind = FormulaNode::And; break;
        case POLICY_AST_TOK_OR: out->kind = FormulaNode::Or; break;
        default: fail("invalid boolean formula node");
    }
    out->left = compile_formula(raw->left, atoms);
    out->right = compile_formula(raw->right, atoms);
    return out;
}

// Existential conjunctions factor only across disjoint witness occurrences.
// The surrounding NOT is kept: NOT EXISTS(A AND B) becomes NOT(EA AND EB).
inline std::size_t split_boundary_components(std::unique_ptr<FormulaNode> &node,int target) {
    if (!node) return 0;
    if (node->kind!=FormulaNode::Branch)
        return split_boundary_components(node->left,target)+split_boundary_components(node->right,target);
    if (!cf_component_boundaries) return 0;
    std::map<int,int> parent;
    const auto include=[&](const NormalizedAtom *atom) {
        if (atom->left.node_id!=target) parent.emplace(atom->left.node_id,atom->left.node_id);
        if (!atom->right_is_const && atom->right.node_id!=target)
            parent.emplace(atom->right.node_id,atom->right.node_id);
    };
    for (auto atom:node->atoms) include(atom);
    for (const auto &group:node->boolean_groups) for (auto atom:group.atoms) include(atom);
    if (parent.size()<2U) return 0;
    const auto root=[&](int value) { while(parent.at(value)!=value) value=parent.at(value);return value; };
    const auto merge=[&](int a,int b) { parent[root(a)]=root(b); };
    for (auto atom:node->atoms)
        if (!atom->right_is_const && atom->left.node_id!=target && atom->right.node_id!=target)
            merge(atom->left.node_id,atom->right.node_id);
    // An OR group is indivisible, even when its alternatives use different relations.
    for (const auto &group:node->boolean_groups) {
        int first=-1;
        for (auto atom:group.atoms) for (auto ref:{&atom->left,atom->right_is_const ? nullptr : &atom->right})
            if (ref && ref->node_id!=target) {
                if (first<0) first=ref->node_id;else merge(first,ref->node_id);
            }
    }
    std::map<int,std::unique_ptr<FormulaNode>> parts;
    for (const auto &item:parent) parts.emplace(root(item.first),nullptr);
    if (parts.size()<2U) return 0;
    for (auto &item:parts) { item.second=std::make_unique<FormulaNode>();item.second->kind=FormulaNode::Branch; }
    const auto component=[&](const NormalizedAtom *atom) {
        if (atom->left.node_id!=target) return root(atom->left.node_id);
        if (!atom->right_is_const && atom->right.node_id!=target) return root(atom->right.node_id);
        return parts.begin()->first;
    };
    for (auto atom:node->atoms) parts.at(component(atom))->atoms.push_back(atom);
    for (const auto &group:node->boolean_groups) {
        int key=parts.begin()->first;
        for (auto atom:group.atoms)
            if (atom->left.node_id!=target || (!atom->right_is_const && atom->right.node_id!=target)) {
                key=component(atom);break;
            }
        parts.at(key)->boolean_groups.push_back(group);
    }
    const auto splits=parts.size()-1U;
    std::unique_ptr<FormulaNode> result;
    for (auto &item:parts) {
        if (!result) result=std::move(item.second);
        else {
            auto conjunction=std::make_unique<FormulaNode>();conjunction->kind=FormulaNode::And;
            conjunction->left=std::move(result);conjunction->right=std::move(item.second);result=std::move(conjunction);
        }
    }
    node=std::move(result);
    return splits;
}

inline std::unique_ptr<FormulaNode> parse_formula(
    const PolicyEngineInputC *in,
    int target_index,
    const std::unordered_map<int, const NormalizedAtom *> &atoms) {
    if (in->target_ast_toks == nullptr || in->target_ast_tok_offsets == nullptr ||
        in->target_ast_tok_counts == nullptr)
        fail("missing postfix target AST payload");
    const int offset = in->target_ast_tok_offsets[target_index];
    const int count = in->target_ast_tok_counts[target_index];
    if (offset < 0 || count <= 0 || offset > in->target_ast_tok_len - count)
        fail("invalid postfix target AST range");
    std::vector<std::unique_ptr<RawExpr>> arena;
    std::vector<RawExpr *> stack;
    auto make = [&](int kind) {
        arena.push_back(std::make_unique<RawExpr>());
        arena.back()->kind = kind;
        return arena.back().get();
    };
    for (int i = 0; i < count; ++i) {
        const PolicyAstTokC &tok = in->target_ast_toks[offset + i];
        // Lexical occurrence IDs are already present on normalized atoms.
        // The routing check admits only flat scopes to this parser.
        if (tok.kind == 8) {
            if (stack.empty() || tok.value < 0) fail("invalid flat lexical binder");
            continue;
        }
        if (tok.kind == POLICY_AST_TOK_VAR || tok.kind == POLICY_AST_TOK_TRUE ||
            tok.kind == POLICY_AST_TOK_FALSE) {
            RawExpr *node = make(tok.kind);
            node->atom_id = tok.value;
            stack.push_back(node);
        } else if (tok.kind == POLICY_AST_TOK_NOT || tok.kind == POLICY_AST_TOK_EXISTS) {
            if (stack.empty()) fail("malformed postfix NOT");
            RawExpr *node = make(tok.kind);
            node->left = stack.back();
            stack.back() = node;
        } else if (tok.kind == POLICY_AST_TOK_AND || tok.kind == POLICY_AST_TOK_OR) {
            if (stack.size() < 2U) fail("malformed postfix binary operator");
            RawExpr *rhs = stack.back(); stack.pop_back();
            RawExpr *lhs = stack.back(); stack.pop_back();
            RawExpr *node = make(tok.kind);
            node->left = lhs;
            node->right = rhs;
            stack.push_back(node);
        } else {
            fail("unsupported postfix token");
        }
    }
    if (stack.size() != 1U) fail("postfix AST did not reduce to one root");
    return compile_formula(stack.back(), atoms);
}

struct FusedBranchNode {
    int occurrence = -1;
    std::string table;
    int parent = -1;
    const NormalizedAtom *edge = nullptr;
    std::vector<const NormalizedAtom *> equalities;
    bool candidate_is_left = false;
    std::vector<int> children;
    std::vector<const NormalizedAtom *> filters;
    std::vector<const LocalBooleanGroup *> boolean_groups;
};

struct FusedBranchPlan {
    std::vector<FusedBranchNode> nodes;
};

struct FusedDagNode {
    struct CompiledFilter {
        const NormalizedAtom *atom = nullptr;
        std::uint64_t leaves = 0;
    };
    struct CompiledBooleanGroup {
        const LocalBooleanGroup *group = nullptr;
        std::uint64_t leaves = 0;
    };
    std::string table;
    std::string edge_key;
    std::uint64_t leaves = 0;
    std::vector<std::size_t> children;
    std::array<int, 64> occurrence_by_leaf{};
    std::array<const NormalizedAtom *, 64> edge_by_leaf{};
    std::array<bool, 64> candidate_is_left_by_leaf{};
    std::array<std::vector<const NormalizedAtom *>, 64> equalities_by_leaf;
    std::array<std::vector<const NormalizedAtom *>, 64> filters_by_leaf;
    std::array<std::vector<const LocalBooleanGroup *>, 64>
        boolean_groups_by_leaf;
    std::vector<CompiledFilter> compiled_filters;
    std::vector<CompiledBooleanGroup> compiled_boolean_groups;
    std::vector<int> bound_occurrences;
    std::uint64_t edge_proof_bit = 0;

    FusedDagNode() { occurrence_by_leaf.fill(-1); }
};

using RankProofCell=rank_summaries::Proof;
struct NodeRankProofPlan {
    bool sparse=false;
    std::size_t cardinality = 0;
    unsigned summary=UINT32_MAX;
    std::vector<ColumnRef> filled_columns;
};

struct FunctionalRankProjection {
    static constexpr std::uint32_t unknown = UINT32_MAX;
    static constexpr std::uint32_t null_rank = UINT32_MAX - 1U;
    ColumnRef child_column;
    ColumnRef bound_column;
    int op = POLICY_OP_EQ;  
    std::uint64_t proof_bit = 0;
    ReachedCells<std::uint32_t> child_rank_by_entering_rank;
};

struct BoundPairSlot {
    std::uint32_t secondary_universe_rank = UINT32_MAX;
    std::uint32_t row = UINT32_MAX;
};

struct BoundPairCache {
    bool eligible = false;
    ColumnRef primary_child_column;
    ColumnRef secondary_child_column;
    ColumnRef secondary_bound_column;
    std::size_t primary_count = 0;
    std::size_t ways = 0;
    ReachedCells<std::uint8_t> ready;
    ReachedCells<std::uint8_t> ambiguous;
    ReachedCells<BoundPairSlot> slots;
};

struct FrontierGate {
    std::uint32_t probes = 0;
    std::uint32_t switches = 0;
    bool disabled = false;
};

inline void assign_formula_leaves(FormulaNode *node,
                                  std::vector<FormulaNode *> *leaves) {
    if (node == nullptr) return;
    if (node->kind == FormulaNode::Branch) {
        if (leaves->size() >= 64U) fail("our_pg fused walk supports at most 64 leaves");
        node->leaf_id = leaves->size();
        leaves->push_back(node);
        return;
    }
    assign_formula_leaves(node->left.get(), leaves);
    assign_formula_leaves(node->right.get(), leaves);
}

inline FusedBranchPlan build_fused_branch_plan(
    const FormulaNode *leaf,
    int target_node,
    const std::string &target,
    bool retain_prior_bindings = false,
    const std::set<std::string> *overlapping_connections = nullptr) {
    FusedBranchPlan out;
    out.nodes.push_back(FusedBranchNode{});
    out.nodes[0].occurrence = target_node;
    out.nodes[0].table = target;

    std::map<int, std::string> table_by_occurrence;
    table_by_occurrence[target_node] = target;
    std::set<int> all_occurrences{target_node};
    for (const NormalizedAtom *atom : leaf->atoms) {
        all_occurrences.insert(atom->left.node_id);
        table_by_occurrence[atom->left.node_id] = atom->left.table;
        if (!atom->right_is_const) {
            all_occurrences.insert(atom->right.node_id);
            table_by_occurrence[atom->right.node_id] = atom->right.table;
        }
    }
    for (const LocalBooleanGroup &group : leaf->boolean_groups) {
        for (const NormalizedAtom *atom : group.atoms) {
            all_occurrences.insert(atom->left.node_id);
            table_by_occurrence[atom->left.node_id] = atom->left.table;
            if (!atom->right_is_const) {
                all_occurrences.insert(atom->right.node_id);
                table_by_occurrence[atom->right.node_id] = atom->right.table;
            }
        }
    }

    std::map<int, int> plan_node_by_occurrence{{target_node, 0}};
    std::set<const NormalizedAtom *> tree_edges;
    while (plan_node_by_occurrence.size() < all_occurrences.size()) {
        const NormalizedAtom *chosen = nullptr;
        bool candidate_left = false;
        int candidate_occurrence = -1;
        int parent_occurrence = -1;
        int best_priority = 2;
        for (const NormalizedAtom *atom : leaf->atoms) {
            if (atom->right_is_const) continue;
            const bool left_bound = plan_node_by_occurrence.count(atom->left.node_id) != 0;
            const bool right_bound = plan_node_by_occurrence.count(atom->right.node_id) != 0;
            if (left_bound == right_bound) continue;
            const auto &candidate = left_bound ? atom->right : atom->left;
            const auto &parent = left_bound ? atom->left : atom->right;
            const std::string connection=parent.key()+"|"+candidate.key()+"|"+candidate.table;
            const int priority = overlapping_connections && overlapping_connections->count(connection) ? -1 :
                                 atom->op == POLICY_OP_EQ ? 0 : 1;
            if (chosen != nullptr && priority >= best_priority) continue;
            chosen = atom;
            best_priority = priority;
            candidate_left = !left_bound;
            candidate_occurrence = candidate_left ? atom->left.node_id : atom->right.node_id;
            parent_occurrence = candidate_left ? atom->right.node_id : atom->left.node_id;
        }
        if (chosen == nullptr) {
            fail("our_pg fused plan contains a disconnected policy occurrence");
        }
        FusedBranchNode node;
        node.occurrence = candidate_occurrence;
        node.table = table_by_occurrence.at(candidate_occurrence);
        node.parent = plan_node_by_occurrence.at(parent_occurrence);
        node.edge = chosen;
        node.candidate_is_left = candidate_left;
        // Only mandatory equalities form a connection; OR alternatives do not.
        for (const auto *atom : leaf->atoms) {
            if (atom->right_is_const || atom->op != POLICY_OP_EQ) continue;
            if ((atom->left.node_id == candidate_occurrence &&
                 plan_node_by_occurrence.count(atom->right.node_id)) ||
                (atom->right.node_id == candidate_occurrence &&
                 plan_node_by_occurrence.count(atom->left.node_id)))
                node.equalities.push_back(atom);
        }
        const int index = static_cast<int>(out.nodes.size());
        out.nodes.push_back(std::move(node));
        out.nodes[static_cast<std::size_t>(out.nodes[index].parent)].children.push_back(index);
        plan_node_by_occurrence[candidate_occurrence] = index;
        tree_edges.insert(chosen);
    }

    for (const NormalizedAtom *atom : leaf->atoms) {
        if (tree_edges.count(atom) != 0) continue;
        int attach = plan_node_by_occurrence.at(atom->left.node_id);
        if (!atom->right_is_const) {
            attach = std::max(attach, plan_node_by_occurrence.at(atom->right.node_id));
        }
        out.nodes[static_cast<std::size_t>(attach)].filters.push_back(atom);
    }
    for (const LocalBooleanGroup &group : leaf->boolean_groups) {
        int attach = 0;
        for (const NormalizedAtom *atom : group.atoms) {
            attach = std::max(attach,
                plan_node_by_occurrence.at(atom->left.node_id));
            if (!atom->right_is_const) {
                attach = std::max(attach,
                    plan_node_by_occurrence.at(atom->right.node_id));
            }
        }
        out.nodes[static_cast<std::size_t>(attach)].boolean_groups.push_back(
            &group);
    }
    const auto is_ancestor = [&](int ancestor, int descendant) {
        while (descendant >= 0) {
            if (ancestor == descendant) return true;
            descendant = out.nodes[descendant].parent;
        }
        return false;
    };
    for (std::size_t i = 0; i < out.nodes.size(); ++i) {
        const auto needs_prior_binding = [&](const NormalizedAtom &atom) {
            return !is_ancestor(plan_node_by_occurrence.at(atom.left.node_id), i) ||
                (!atom.right_is_const &&
                 !is_ancestor(plan_node_by_occurrence.at(atom.right.node_id), i));
        };
        for (const NormalizedAtom *atom : out.nodes[i].filters)
            retain_prior_bindings |= needs_prior_binding(*atom);
        for (const LocalBooleanGroup *group : out.nodes[i].boolean_groups)
            for (const NormalizedAtom *atom : group->atoms)
                retain_prior_bindings |= needs_prior_binding(*atom);
    }
    // Keep prior witnesses bound when a residual predicate links siblings.
    // A complete branch must use one jointly qualifying binding, not a
    // different row for each partial test.
    if (retain_prior_bindings) {
        for (std::size_t i = 0; i < out.nodes.size(); ++i) {
            out.nodes[i].children.clear();
            if (i != 0U) out.nodes[i].parent = static_cast<int>(i - 1U);
            if (i + 1U < out.nodes.size())
                out.nodes[i].children.push_back(static_cast<int>(i + 1U));
        }
    }
    return out;
}

inline int normalized_edge_op(const NormalizedAtom &edge, bool candidate_is_left) {
    return candidate_is_left ? edge.op : invert_op(edge.op);
}

// Relative to the common bound rank: lower values, the pivot, upper values.
// This is plan metadata, not an operator in the connection identity. Requests
// with disjoint masks can NEVER share a posting and retain separate V4 nodes.
inline bool fused_node_is_mixed(const FusedDagNode &node) {
    if(!node.leaves)return false;
    const auto first=unsigned(__builtin_ctzll(node.leaves));
    const auto op=normalized_edge_op(*node.edge_by_leaf[first],node.candidate_is_left_by_leaf[first]);
    for(auto bits=node.leaves&(node.leaves-1U);bits;bits&=bits-1U) {
        const auto leaf=unsigned(__builtin_ctzll(bits));
        if(normalized_edge_op(*node.edge_by_leaf[leaf],node.candidate_is_left_by_leaf[leaf])!=op)return true;
    }
    return false;
}

inline unsigned edge_rank_regions(int op) {
    switch(op) {
        case POLICY_OP_EQ:return 2U;
        case POLICY_OP_NE:return 5U;
        case POLICY_OP_LT:return 1U;
        case POLICY_OP_LE:return 3U;
        case POLICY_OP_GT:return 4U;
        case POLICY_OP_GE:return 6U;
        default:return 0U;
    }
}

// Prefer a shared request connection only when different leaves use genuinely
// overlapping operators on that same target/candidate pair. All-equality and
// disjoint groups retain V4's access order. Residual filled operands stay keys.
inline std::set<std::string> overlapping_target_connections(
        const std::vector<FormulaNode *> &leaves,int target) {
    std::map<std::string,std::vector<std::pair<std::size_t,int>>> requests;
    std::set<std::string> result;
    if(!cf_decision_sharing)return result;
    for(std::size_t leaf=0;leaf<leaves.size();++leaf)for(auto atom:leaves[leaf]->atoms) {
        if(atom->right_is_const)continue;
        const bool left=atom->left.node_id==target,right=atom->right.node_id==target;
        if(left==right)continue;
        const auto &parent=left ? atom->left : atom->right;
        const auto &candidate=left ? atom->right : atom->left;
        requests[parent.key()+"|"+candidate.key()+"|"+candidate.table].emplace_back(
            leaf,normalized_edge_op(*atom,!left));
    }
    for(const auto &entry:requests)for(const auto &a:entry.second)for(const auto &b:entry.second)
        if(a.first!=b.first && a.second!=b.second && (edge_rank_regions(a.second)&edge_rank_regions(b.second)))
            result.insert(entry.first);
    return result;
}

inline std::string fused_edge_key(const FusedBranchNode &node) {
    const ColumnRef &candidate = node.candidate_is_left ? node.edge->left : node.edge->right;
    const ColumnRef &parent = node.candidate_is_left ? node.edge->right : node.edge->left;
    std::string key = parent.key() + "|" + candidate.key() + "|" + node.table;
    // A connection owns an iterator; its requests own their operators.
    // The off switch restores V4's separate nodes for a controlled comparison.
    if (!cf_decision_sharing)
        key += "|OP:" + std::to_string(normalized_edge_op(*node.edge, node.candidate_is_left));
    if (cf_composite_edges && node.equalities.size() > 1U)
        for (const auto *atom : node.equalities) {
            const auto &child = atom->left.node_id == node.occurrence ? atom->left : atom->right;
            const auto &bound = atom->left.node_id == node.occurrence ? atom->right : atom->left;
            key += "|EQ:" + child.key() + "=" + bound.key();
        }
    return key;
}

inline std::size_t merge_fused_branch_node(
    const FusedBranchPlan &branch,
    int branch_node,
    std::size_t fused_parent,
    std::size_t leaf,
    std::vector<FusedDagNode> *dag,
    std::map<std::pair<std::size_t, std::string>, std::size_t> *by_edge) {
    const FusedBranchNode &source = branch.nodes[static_cast<std::size_t>(branch_node)];
    const std::string edge_key = fused_edge_key(source);
    const auto key = std::make_pair(fused_parent, edge_key);
    auto found = by_edge->find(key);
    const std::uint64_t bit = std::uint64_t{1} << leaf;
    std::size_t fused_index=SIZE_MAX;
    if(found!=by_edge->end() && !((*dag)[found->second].leaves&bit)) {
        const auto regions=edge_rank_regions(normalized_edge_op(*source.edge,source.candidate_is_left));
        for(auto child:(*dag)[fused_parent].children) {
            const auto &existing=(*dag)[child];
            if(existing.edge_key!=edge_key || (existing.leaves&bit))continue;
            bool overlaps=false;
            for(auto bits=existing.leaves;bits;bits&=bits-1U) {
                const auto other=unsigned(__builtin_ctzll(bits));
                overlaps |= (regions & edge_rank_regions(normalized_edge_op(
                    *existing.edge_by_leaf[other],existing.candidate_is_left_by_leaf[other])))!=0U;
            }
            if(overlaps){fused_index=child;break;}
        }
    }
    if (fused_index == SIZE_MAX) {
        fused_index = dag->size();
        FusedDagNode node;
        node.table = source.table;
        node.edge_key = edge_key;
        dag->push_back(std::move(node));
        if (by_edge->count(key) == 0) (*by_edge)[key] = fused_index;
        (*dag)[fused_parent].children.push_back(fused_index);
    }
    FusedDagNode &target = (*dag)[fused_index];
    target.leaves |= bit;
    target.occurrence_by_leaf[leaf] = source.occurrence;
    target.edge_by_leaf[leaf] = source.edge;
    target.candidate_is_left_by_leaf[leaf] = source.candidate_is_left;
    target.equalities_by_leaf[leaf] = source.equalities;
    target.filters_by_leaf[leaf] = source.filters;
    target.boolean_groups_by_leaf[leaf] = source.boolean_groups;
    for (int child : source.children) {
        merge_fused_branch_node(branch, child, fused_index, leaf, dag, by_edge);
    }
    return fused_index;
}

struct FusedMemoKey {
    
    
    
    std::array<std::uint32_t, 16> ranks;
    std::uint8_t width;
    bool operator==(const FusedMemoKey &other) const {
        if (width != other.width) return false;
        for (std::size_t i = 0; i < width; ++i)
            if (ranks[i] != other.ranks[i]) return false;
        return true;
    }
};

struct FusedMemoKeyHash {
    std::size_t operator()(const FusedMemoKey &key) const {
        std::uint64_t value = UINT64_C(0x9e3779b97f4a7c15) ^ key.width;
        for (std::size_t i = 0; i < key.width; ++i) {
            std::uint64_t x = key.ranks[i] + UINT64_C(0x9e3779b97f4a7c15);
            x = (x ^ (x >> 30U)) * UINT64_C(0xbf58476d1ce4e5b9);
            x = (x ^ (x >> 27U)) * UINT64_C(0x94d049bb133111eb);
            value ^= x ^ (x >> 31U);
            value = (value << 13U) | (value >> 51U);
        }
        return static_cast<std::size_t>(value);
    }
};

struct FusedMemoEntry {
    bool truth = false;
    std::uint32_t touch_cost = 0;
};

inline std::uint64_t splitmix64(std::uint64_t value) {
    value += UINT64_C(0x9e3779b97f4a7c15);
    value = (value ^ (value >> 30U)) * UINT64_C(0xbf58476d1ce4e5b9);
    value = (value ^ (value >> 27U)) * UINT64_C(0x94d049bb133111eb);
    return value ^ (value >> 31U);
}

inline bool pack_memo_key(const FusedMemoKey &key, std::uint64_t *packed) {
    if (key.width == 0U) {
        *packed = 0U;
        return true;
    }
    if (key.width == 1U) {
        *packed = key.ranks[0];
        return true;
    }
    if (key.width == 2U) {
        *packed = (static_cast<std::uint64_t>(key.ranks[0]) << 32U) |
                  key.ranks[1];
        return true;
    }
    return false;
}





// Several equalities entering one relation occurrence. Nothing is persisted for it: the rows of an entering rank
// tuple are found at query time from the unary inverted and forward indexes (see unary_tuple_rows).
struct CompositeConnection {
    std::vector<ColumnRef> columns;
    std::vector<std::uint32_t> rows;      // scratch for the current lookup; DAG nodes are acyclic, one frame per node
    std::size_t driver=0;
    bool groups_enabled=false;
    std::unordered_map<std::uint32_t,LazyGroupMap> groups;
};

class PackedMemoMap {
public:
    explicit PackedMemoMap(std::pmr::memory_resource *resource = std::pmr::get_default_resource())
        : occupied_(resource), keys_(resource), values_(resource) {}
    std::size_t size() const { return size_; }
    std::size_t bytes() const {
        return occupied_.capacity()+keys_.capacity()*sizeof(std::uint64_t)+values_.capacity()*sizeof(FusedMemoEntry);
    }
    FusedMemoEntry *find(std::uint64_t key) {
        if (occupied_.empty()) return nullptr;
        const std::size_t mask = occupied_.size() - 1U;
        std::size_t slot = static_cast<std::size_t>(splitmix64(key)) & mask;
        while (occupied_[slot] != 0U) {
            if (keys_[slot] == key) return &values_[slot];
            slot = (slot + 1U) & mask;
        }
        return nullptr;
    }

    std::pair<FusedMemoEntry *, bool> insert(std::uint64_t key,
                                              FusedMemoEntry value) {
        if (occupied_.empty()) rehash(1024U);
        if ((size_ + 1U) * 10U >= occupied_.size() * 7U)
            rehash(occupied_.size() * 2U);
        const std::size_t mask = occupied_.size() - 1U;
        std::size_t slot = static_cast<std::size_t>(splitmix64(key)) & mask;
        while (occupied_[slot] != 0U) {
            if (keys_[slot] == key) return {&values_[slot], false};
            slot = (slot + 1U) & mask;
        }
        occupied_[slot] = 1U;
        keys_[slot] = key;
        values_[slot] = value;
        ++size_;
        return {&values_[slot], true};
    }

    void clear_release() {
        std::pmr::vector<std::uint8_t>(occupied_.get_allocator()).swap(occupied_);
        std::pmr::vector<std::uint64_t>(keys_.get_allocator()).swap(keys_);
        std::pmr::vector<FusedMemoEntry>(values_.get_allocator()).swap(values_);
        size_ = 0;
    }

private:
    void rehash(std::size_t capacity) {
        auto old_occupied = std::move(occupied_);
        auto old_keys = std::move(keys_);
        auto old_values = std::move(values_);
        occupied_.assign(capacity, 0U);
        keys_.resize(capacity);
        values_.resize(capacity);
        size_ = 0;
        for (std::size_t i = 0; i < old_occupied.size(); ++i) {
            if (old_occupied[i] == 0U) continue;
            insert(old_keys[i], old_values[i]);
        }
    }

    std::pmr::vector<std::uint8_t> occupied_;
    std::pmr::vector<std::uint64_t> keys_;
    std::pmr::vector<FusedMemoEntry> values_;
    std::size_t size_ = 0;
};

struct FusedMemoStore {
    explicit FusedMemoStore(std::pmr::memory_resource *resource = std::pmr::get_default_resource())
        : packed_entries(resource), wide_entries(resource) {}
    bool enabled = true;
    bool probationary = true;
    bool recurrence_observed = false;
    std::uint64_t probes = 0;
    std::uint64_t hits = 0;
    PackedMemoMap packed_entries;
    std::pmr::unordered_map<FusedMemoKey, FusedMemoEntry, FusedMemoKeyHash> wide_entries;
};

class FusedWalkRuntime;
struct TerminalVerdictGroup {
    std::size_t node=0;
    std::uint64_t leaves=0;
    std::vector<ColumnRef> bound_columns,child_columns;
    std::unordered_map<FusedMemoKey,std::uint64_t,FusedMemoKeyHash> truth;
    int cache_mode=1;
    std::uint32_t gate_id=0;
    full_reuse::CompositeCacheCost cost;
    std::uint64_t probes=0,hits=0,writes=0,scan_reads=0;
    using Lookup=bool(FusedWalkRuntime::*)(TerminalVerdictGroup &,std::uint64_t *);
    Lookup lookup=nullptr;
};

struct RootTerminalProbe {
    std::size_t group = SIZE_MAX;
    std::size_t leaf = SIZE_MAX;
    std::vector<ColumnRef> target_columns;
};

// Compiles and evaluates one target with the shared rank-driven walk.
class FusedWalkRuntime {
    static constexpr std::size_t kDenseCacheBudget = std::size_t{2} << 30U;
    std::size_t dense_bytes_planned_ = 0;
    std::uint64_t dense_budget_rejections_ = 0;
    bool reserve_dense_cache(std::size_t bytes) {
        if(!cf_cost_dense_budget)return true;
        const auto limit=std::size_t(cf_cost_dense_budget_mb)<<20U;
        if (bytes > limit - dense_bytes_planned_) {
            ++dense_budget_rejections_;
            return false;
        }
        dense_bytes_planned_ += bytes;
        return true;
    }
public:
    FusedWalkRuntime(const PolicyArtifactCNew *arts,
                     int art_count,
                     const PolicyEngineInputC *in,
                     std::string target,
                     int target_node,
                     int target_index)
        : arts_(arts), art_count_(art_count), in_(in), target_(std::move(target)),
          target_node_(target_node) {
        rank_store_mode_ = cf_decision_store == 1;
        rank_store_.region_budget_bytes=cf_cost_dense_budget?(std::size_t(cf_cost_dense_budget_mb)<<20U):SIZE_MAX;
        const auto setup_started = std::chrono::steady_clock::now();
        normalized_.reserve(static_cast<std::size_t>(in_->atom_count));
        for (int i = 0; i < in_->atom_count; ++i)
            normalized_.push_back(normalize_atom(in_->atoms[i]));
        for (NormalizedAtom &atom : normalized_) {
            if (atom.left.node_id < 0 && atom.left.table == target_)
                atom.left.node_id = target_node_;
            if (!atom.right_is_const && atom.right.node_id < 0 && atom.right.table == target_)
                atom.right.node_id = target_node_;
            if (atom.left.node_id < 0 || (!atom.right_is_const && atom.right.node_id < 0))
                fail("atom y" + std::to_string(atom.atom_id) + " has no occurrence node");
            atom_by_id_[atom.atom_id] = &atom;
            max_node_ = std::max(max_node_, atom.left.node_id);
            if (!atom.right_is_const) max_node_ = std::max(max_node_, atom.right.node_id);
        }
        max_node_ = std::max(max_node_, target_node_);
        bindings_.assign(static_cast<std::size_t>(max_node_ + 1), -1);
        formula_ = parse_formula(in_, target_index, atom_by_id_);
        // Bounds retain the original branch bodies: splitting a body's two
        // independent root components must not make an OR visit components of
        // a branch whose first component has already failed.
        if(cf_composed_bounds) {
            bound_formula_=parse_formula(in_,target_index,atom_by_id_);
            assign_formula_leaves(bound_formula_.get(),&bound_leaves_);
        }
        const auto component_splits=split_boundary_components(formula_,target_node_);
        cf_perf_metric_set("boundary_component_splits",component_splits);
        assign_formula_leaves(formula_.get(), &leaves_);
        compile_flat_formula();
        configure_formula_truth_table();

        
        
        
        
        std::set<int> used_atom_ids;
        for (const FormulaNode *leaf : leaves_) {
            for (const NormalizedAtom *atom : leaf->atoms)
                used_atom_ids.insert(atom->atom_id);
            for (const LocalBooleanGroup &group : leaf->boolean_groups)
                for (const NormalizedAtom *atom : group.atoms)
                    used_atom_ids.insert(atom->atom_id);
        }
        {
            std::map<std::string, std::size_t> proof_by_identity;
            for (const FormulaNode *leaf : leaves_) {
                for (const NormalizedAtom *atom : leaf->atoms)
                    proof_by_identity.emplace(
                        atom_proof_identity(*atom), 0U);
                for (const LocalBooleanGroup &group : leaf->boolean_groups) {
                    std::string identity = "BOOL:";
                    for (const LocalBooleanToken &token : group.postfix) {
                        if (token.kind == LocalBooleanTokenKind::atom) {
                            identity += "A" + atom_proof_identity(*token.atom) + ";";
                        } else {
                            identity += token.kind ==
                                LocalBooleanTokenKind::conjunction ?
                                "AND;" : "OR;";
                        }
                    }
                    proof_by_identity.emplace(identity, 0U);
                }
            }
            rank_proofs_enabled_ = proof_by_identity.size() <= 64U;
#ifdef SETU_DIAG_DISABLE_RANK_PROOFS
            rank_proofs_enabled_ = false;
#endif
            if (rank_proofs_enabled_) {
                std::size_t next = 0;
                for (auto &item : proof_by_identity) item.second = next++;
                for (FormulaNode *leaf : leaves_) {
                    for (const NormalizedAtom *atom_const : leaf->atoms) {
                        NormalizedAtom *atom = const_cast<NormalizedAtom *>(atom_const);
                        atom->proof_bit = std::uint64_t{1} <<
                            proof_by_identity.at(atom_proof_identity(*atom));
                    }
                    for (LocalBooleanGroup &group : leaf->boolean_groups) {
                        std::string identity = "BOOL:";
                        for (const LocalBooleanToken &token : group.postfix) {
                            if (token.kind == LocalBooleanTokenKind::atom) {
                                identity += "A" +
                                    atom_proof_identity(*token.atom) + ";";
                            } else {
                                identity += token.kind ==
                                    LocalBooleanTokenKind::conjunction ?
                                    "AND;" : "OR;";
                            }
                        }
                        group.proof_bit = std::uint64_t{1} <<
                            proof_by_identity.at(identity);
                    }
                }
            }
        }
        
        
        for (NormalizedAtom &atom : normalized_) {
            if (used_atom_ids.count(atom.atom_id) == 0U) continue;
            compile_column(atom.left);
            if (!atom.right_is_const) compile_column(atom.right);
        }
        






        for (NormalizedAtom &atom : normalized_) {
            if (used_atom_ids.count(atom.atom_id) == 0U ||
                !atom.right_is_const) continue;
            ColumnIndex &left = column(atom.left);
            const auto bounds = literal_bounds(left.domain, atom.literal);
            atom.constant_lower = bounds.first;
            atom.constant_upper = bounds.second;
            atom.constant_compiled = true;
        }
        const auto columns_compiled = std::chrono::steady_clock::now();
        if (leaves_.empty()) return;
        dag_.push_back(FusedDagNode{});
        dag_[0].table = target_;
        const auto overlapping_connections=overlapping_target_connections(leaves_,target_node_);
        std::map<std::pair<std::size_t, std::string>, std::size_t> by_edge;
        for (std::size_t leaf = 0; leaf < leaves_.size(); ++leaf) {
            const std::uint64_t bit = std::uint64_t{1} << leaf;
            FusedBranchPlan branch =
                build_fused_branch_plan(leaves_[leaf], target_node_, target_,false,&overlapping_connections);
            if (cf_composite_edges && cf_composite_cost)
                for (std::size_t node=1;node<branch.nodes.size();++node)
                    if (branch.nodes[node].equalities.size()>1U && !branch_composite_postings_pay(branch,node,leaf)) {
                        branch.nodes[node].equalities.assign(1U,branch.nodes[node].edge);
                        ++composite_connections_rejected_;
                    }
            dag_[0].leaves |= bit;
            dag_[0].occurrence_by_leaf[leaf] = target_node_;
            dag_[0].filters_by_leaf[leaf] = branch.nodes[0].filters;
            dag_[0].boolean_groups_by_leaf[leaf] =
                branch.nodes[0].boolean_groups;
            for (int child : branch.nodes[0].children)
                merge_fused_branch_node(branch, child, 0, leaf, &dag_, &by_edge);
        }
        // Immutable solver binding: no mixed-node test on recursive arrivals.
        node_solvers_=full_reuse::bind_node_solvers(dag_,&FusedWalkRuntime::solve_node_v4,
            &FusedWalkRuntime::solve_mixed_requests,fused_node_is_mixed);
        for(std::size_t node=0;node<dag_.size();++node)
            if(node_solvers_[node]==&FusedWalkRuntime::solve_mixed_requests)mixed_request_leaves_ |= dag_[node].leaves;
        dependencies_.resize(dag_.size());
        memo_.resize(dag_.size());
        node_calls_.assign(dag_.size(), 0U);
        node_partner_touches_.assign(dag_.size(), 0U);
        node_memo_hits_.assign(dag_.size(), 0U);
        node_terminal_hits_.assign(dag_.size(), 0U);
        rank_multirow_by_node_.resize(dag_.size());
        frontier_gates_.assign(dag_.size(), FrontierGate{});
        for (std::size_t node = 0; node < dag_.size(); ++node) {
            dependencies_[node].resize(leaves_.size());
            memo_[node].reserve(leaves_.size());
            for (std::size_t leaf = 0; leaf < leaves_.size(); ++leaf)
                memo_[node].emplace_back(&old_memo_memory_);
            std::set<int> occurrences;
            for (std::uint64_t bits = dag_[node].leaves;
                 bits != 0U; bits &= bits - 1U) {
                const std::size_t leaf = static_cast<std::size_t>(
                    __builtin_ctzll(bits));
                const int occurrence = dag_[node].occurrence_by_leaf[leaf];
                if (occurrence >= 0) occurrences.insert(occurrence);
            }
            dag_[node].bound_occurrences.assign(
                occurrences.begin(), occurrences.end());
        }
        compile_filter_masks();
        compile_dependencies();
        // Composite group admission uses these header-only arrival estimates.
        // Initialize them in both store modes before compiling connections.
        configure_arrival_estimates();
        configure_composite_connections();
        if (rank_store_mode_) {
            configure_single_visits();
            compile_rank_predicates();
        }
        configure_rank_proofs();
        configure_functional_rank_projections();
        configure_bound_pair_caches();
        configure_composed_bounds();
        configure_chain_projections();
        configure_full_reuse();
        configure_window_requests();
        const auto dag_compiled = std::chrono::steady_clock::now();
        compile_terminal_verdicts();
        compile_root_terminal_probes();
        const auto terminals_compiled = std::chrono::steady_clock::now();
        configure_interval_connections();
        configure_posting_positions();
        const auto driver_compiled = std::chrono::steady_clock::now();
        cf_perf_metric_set("universe_decode_ms",0);
        cf_perf_metric_set("rank_remap_ms",0);
        cf_perf_metric_set("theta_transfer_bytes",0);
        cf_perf_metric_set("engine_setup_ms", elapsed_ms(setup_started, driver_compiled));
        cf_perf_metric_set("setup_exclusive_ms", std::max(0.0,elapsed_ms(setup_started,driver_compiled)-
            projection_build_ms_-composite_build_ms_-interval_build_ms_-chain_boundary_build_ms_-decision_lookup_ms_));
        cf_perf_metric_set("dag_ms", elapsed_ms(columns_compiled, dag_compiled));
        cf_perf_metric_set("terminals_ms", elapsed_ms(dag_compiled, terminals_compiled));
        const auto setup_reads=partner_touches_+terminal_build_tuples_+online_build_tuples_+bound_pair_build_rows_;
        cf_perf_metric_set("rows_read_before_first_target",setup_reads);
        if (setup_reads) fail("setup accessed witness rows before the first target row");
        CF_METRICS_LOG(DEBUG1,
             "our_pg_setup: columns_ms=%.3f dag_ms=%.3f terminals_ms=%.3f driver_ms=%.3f total_ms=%.3f columns=%zu nodes=%zu leaves=%zu",
             elapsed_ms(setup_started, columns_compiled),
             elapsed_ms(columns_compiled, dag_compiled),
             elapsed_ms(dag_compiled, terminals_compiled),
             elapsed_ms(terminals_compiled, driver_compiled),
             elapsed_ms(setup_started, driver_compiled),
             columns_.size(), dag_.size(), leaves_.size());
    }

    std::vector<std::uint64_t> run(std::uint32_t total_rows) {
        const auto run_started = std::chrono::steady_clock::now();
        const double builds_before = composite_build_ms_ + interval_build_ms_ + chain_boundary_build_ms_;
        const double lookups_before = decision_lookup_ms_;
        cf_perf_metric_set("direction_mode", 0);
        cf_perf_metric_set("direction_candidates", total_rows);
        std::vector<std::uint64_t> allowed(
            (static_cast<std::size_t>(total_rows) + 63U) / 64U, 0U);
        const bool single_projection=leaves_.size()==1U && chain_plans_[0].enabled && chain_plans_[0].full;
        bool single_false=false,single_true=false;
        if (single_projection) {
            settled_=1U;truth_=0U;single_false=partial(formula_.get())==1;
            truth_=1U;single_true=partial(formula_.get())==1;
            settled_=truth_=0U;
        }
        const auto evaluate=[&](std::uint32_t row) {
            target_walk_started_=true;
            if (!single_projection) return evaluate_target(row);
            ++target_evals_;
            bindings_[target_node_]=row;
            bool truth=false;
            if (evaluate_filters(0,1U)&1U) {
                if (!chain_projected_truth(0U,row,&truth)) fail("complete projection did not decide its branch");
            }
            return truth ? single_true : single_false;
        };
        const bool compiled=composed_bound_program_ ? run_tight_policy(total_rows,allowed) :
            (mixed_request_leaves_ ? run_grouped_tight_policy(total_rows,allowed) :
                                    run_tight_policy(total_rows,allowed));
        if (!compiled) {
            full_reuse::RunBlock runs;
            for(std::uint32_t base=0;base<total_rows;base+=std::min(1024U,total_rows-base)) {
                CHECK_FOR_INTERRUPTS();const auto size=std::min(1024U,total_rows-base);
                if(cf_run_reuse && !run_columns_.empty() && !runs.disabled && runs.detect(run_columns_,base,size)) {
                    for(std::uint32_t offset=0;offset<size;) {
                        const auto end=runs.ends[offset];
                        if(evaluate(base+offset))full_reuse::allow_range(allowed,base+offset,base+end);
                        target_evals_+=end-offset-1U;CF_COUNT(run_rows_saved_+=end-offset-1U);offset=end;
                    }
                } else for(auto row=base;row<base+size;++row)
                    if(evaluate(row))allowed[row/64U]|=std::uint64_t{1}<<(row&63U);
            }
        }
        if (target_evals_!=total_rows) fail("target-only path did not visit every target row");
        CF_COUNT(cf_perf_metric_set("nested_formula_path_used",
            target_evals_ && flat_mode_==FlatFormulaMode::none ? 1 : 0));
        report_cost_admissions();
        report_full_reuse(total_rows);
        report_composed_bounds();
        const double run_ms = elapsed_ms(run_started, std::chrono::steady_clock::now());
        cf_perf_metric_set("walk_exclusive_ms", std::max(0.0, run_ms -
            (composite_build_ms_ + interval_build_ms_ + chain_boundary_build_ms_ - builds_before) - rank_order_build_ms_ -
            (decision_lookup_ms_-lookups_before) - bitmap_mark_ms_ - tight_loop_build_ms_));
        // Lazy indexes and summaries are work performed during the walk.
        cf_perf_metric_set("walk_ms",std::max(0.0,run_ms-tight_loop_build_ms_));
        cf_perf_metric_set("bitmap_mark_ms", cf_engine_profile ? bitmap_mark_ms_ : -1);
        cf_perf_metric_set("decision_lookup_ms", cf_engine_profile ? decision_lookup_ms_ : -1);
        cf_perf_metric_set("profiled", cf_engine_profile ? 1 : 0);
        cf_perf_metric_set("target_evals", target_evals_);
        cf_perf_metric_set("projection_hits_good", projection_hits_good_);
        cf_perf_metric_set("projection_hits_nogood", projection_hits_nogood_);
        cf_perf_metric_set("chain_boundary_build_ms", chain_boundary_build_ms_);
        cf_perf_metric_set("chain_boundary_hits", chain_boundary_hits_);
        cf_perf_metric_set("chain_boundary_misses", chain_boundary_misses_);
        cf_perf_metric_set("composite_decision_hits", composite_decision_hits_);
        cf_perf_metric_set("composite_decision_misses", composite_decision_misses_);
        cf_perf_metric_set("composite_probe_ms", cf_engine_profile ? composite_probe_ms_ : -1);
        cf_perf_metric_set("composite_probe_ns_per_target", cf_engine_profile && target_evals_ ? composite_probe_ms_*1000000.0/target_evals_ : -1);
        cf_perf_metric_set("rank_order_build_ms",rank_order_build_ms_);
        cf_perf_metric_set("rank_order_used",0);
        cf_perf_metric_set("online_build_ms",projection_build_ms_+composite_build_ms_+interval_build_ms_+
            chain_boundary_build_ms_+rank_order_build_ms_+tight_loop_build_ms_);
        CF_METRICS_LOG(DEBUG1,
             "our_pg_walk: target_rows=%u target_evals=%llu partner_touches=%llu root_terminal_hits=%llu prefork_rank_proof_skips=%llu rank_proof_hits=%llu rank_proof_good_hits=%llu rank_proof_no_good_hits=%llu rank_proof_atom_hits=%llu rank_proof_atom_strengthens=%llu rank_proof_backtrack_strengthens=%llu functional_projection_hits=%llu functional_projection_strengthens=%llu bound_pair_builds=%llu bound_pair_build_rows=%llu bound_pair_hits=%llu bound_pair_misses=%llu bound_pair_fallbacks=%llu frontier_choices=%llu frontier_switches=%llu frontier_gated_choices=%llu frontier_gates_disabled=%llu",
             total_rows,
             static_cast<unsigned long long>(target_evals_),
             static_cast<unsigned long long>(partner_touches_),
             static_cast<unsigned long long>(root_terminal_hits_),
             static_cast<unsigned long long>(prefork_rank_proof_skips_),
             static_cast<unsigned long long>(rank_proof_hits_),
             static_cast<unsigned long long>(rank_proof_good_hits_),
             static_cast<unsigned long long>(rank_proof_no_good_hits_),
             static_cast<unsigned long long>(rank_proof_atom_hits_),
             static_cast<unsigned long long>(rank_proof_atom_strengthens_),
             static_cast<unsigned long long>(rank_proof_backtrack_strengthens_),
             static_cast<unsigned long long>(functional_projection_hits_),
             static_cast<unsigned long long>(functional_projection_strengthens_),
             static_cast<unsigned long long>(bound_pair_builds_),
             static_cast<unsigned long long>(bound_pair_build_rows_),
             static_cast<unsigned long long>(bound_pair_hits_),
             static_cast<unsigned long long>(bound_pair_misses_),
             static_cast<unsigned long long>(bound_pair_fallbacks_),
             static_cast<unsigned long long>(frontier_choices_),
             static_cast<unsigned long long>(frontier_switches_),
             static_cast<unsigned long long>(frontier_gated_choices_),
             static_cast<unsigned long long>(frontier_gates_disabled_));
        for (std::size_t node = 1; cf_diagnostic_logging && node < dag_.size(); ++node) {
            CF_METRICS_LOG(DEBUG1,
                 "our_pg_node: node=%zu table=%s calls=%llu partner_touches=%llu memo_hits=%llu terminal_hits=%llu leaves=%llu",
                 node, dag_[node].table.c_str(),
                 static_cast<unsigned long long>(node_calls_[node]),
                 static_cast<unsigned long long>(node_partner_touches_[node]),
                 static_cast<unsigned long long>(node_memo_hits_[node]),
                 static_cast<unsigned long long>(node_terminal_hits_[node]),
                 static_cast<unsigned long long>(dag_[node].leaves));
        }
        if (cf_diagnostic_logging && !rank_store_mode_) {
            std::uint64_t probes = 0, hits = 0;
            std::size_t entries = 0;
            for (const auto &node : memo_)
                for (const auto &store : node) {
                    probes += store.probes; hits += store.hits;
                    entries += store.packed_entries.size() + store.wide_entries.size();
                }
            CF_METRICS_LOG(NOTICE,
                 "oldstore: tuples_read=%llu walk_tuples=%llu terminal_build_tuples=%llu memo_probes=%llu memo_hits=%llu memo_entries=%zu peak_memo_bytes=%zu packed_forward_columns=%llu",
                 static_cast<unsigned long long>(partner_touches_ + terminal_build_tuples_),
                 static_cast<unsigned long long>(partner_touches_),
                 static_cast<unsigned long long>(terminal_build_tuples_),
                 static_cast<unsigned long long>(probes),
                 static_cast<unsigned long long>(hits), entries, old_memo_memory_.peak,
                 static_cast<unsigned long long>(packed_forward_columns_));
        }
        if (rank_store_mode_) {
            cf_perf_metric_set("dense_budget_bytes",std::size_t(cf_cost_dense_budget_mb)<<20U);
            cf_perf_metric_set("dense_budget_reserved_bytes",dense_bytes_planned_);
            cf_perf_metric_set("dense_budget_rejections",dense_budget_rejections_);
            std::size_t sparse_bytes=0;
            for(const auto &entry:chain_steps_)sparse_bytes+=entry.second->reached.sparse_peak_bytes();
            for(const auto &plan:chain_plans_) {
                for(const auto &slot:plan.slots)sparse_bytes+=slot.reached.sparse_peak_bytes();
                for(const auto &guard:plan.guards)sparse_bytes+=guard.state.sparse_peak_bytes();
            }
            for(const auto &projections:functional_rank_projections_)
                for(const auto &projection:projections)sparse_bytes+=projection.child_rank_by_entering_rank.sparse_peak_bytes();
            for(const auto &cache:bound_pair_caches_)
                sparse_bytes+=cache.ready.sparse_peak_bytes()+cache.ambiguous.sparse_peak_bytes()+cache.slots.sparse_peak_bytes();
            report_posting_positions();
            cf_perf_metric_set("store_bytes", rank_store_.memory.peak + projection_front_bytes_+sparse_bytes+posting_position_bytes_+composed_bound_bytes());
            cf_perf_metric_set("decisions_stored", rank_store_.size()+formula_rank_entries_+branch_rank_entries_+projection_null_entries_+posting_position_writes_+bound_fills_);
            cf_perf_metric_set("projection_null_entries",projection_null_entries_);
            cf_perf_metric_set("hits_good", rank_store_.good_hits+formula_good_+branch_good_+posting_position_good_hits_);
            cf_perf_metric_set("hits_nogood", rank_store_.no_good_hits+formula_nogood_+branch_nogood_+posting_position_bad_hits_);
            cf_perf_metric_set("witness_tuples_read", partner_touches_ + terminal_build_tuples_ + online_build_tuples_);
            cf_perf_metric_set("online_build_tuples", online_build_tuples_);
            cf_perf_metric_set("composite_lookups", composite_lookups_);
            cf_perf_metric_set("interval_lookups", interval_lookups_);
            CF_METRICS_LOG(NOTICE,
                 "rankstore: tuples_read=%llu rank_checks=%llu good_hits=%llu no_good_hits=%llu entries=%zu peak_store_bytes=%zu multirow_arrivals=%llu multirow_descents=%llu strengthened_multirow_stops=%llu interrupted=%llu range_hits=%llu gates_off=%llu dense_entries=%zu hash_entries=%zu walk_tuples=%llu terminal_build_tuples=%llu pair_cache_uses=%llu",
                 static_cast<unsigned long long>(partner_touches_ + terminal_build_tuples_),
                 static_cast<unsigned long long>(rank_store_.probes),
                 static_cast<unsigned long long>(rank_store_.good_hits),
                 static_cast<unsigned long long>(rank_store_.no_good_hits),
                 rank_store_.size(), rank_store_.memory.peak,
                 static_cast<unsigned long long>(rank_multirow_arrivals_),
                 static_cast<unsigned long long>(rank_multirow_descents_),
                 static_cast<unsigned long long>(rank_multirow_stops_),
                 static_cast<unsigned long long>(rank_interrupted_),
                 static_cast<unsigned long long>(rank_range_hits_),
                 static_cast<unsigned long long>(rank_store_.gates_off),
                 rank_store_.dense_entries, rank_store_.entries.size(),
                 static_cast<unsigned long long>(partner_touches_),
                 static_cast<unsigned long long>(terminal_build_tuples_),
                 static_cast<unsigned long long>(bound_pair_hits_ + bound_pair_misses_ + bound_pair_fallbacks_));
            for (std::size_t node = 0; node < dag_.size(); ++node) {
                if (rank_single_visit_[node] &&
                    (rank_node_probes_[node] || rank_node_writes_[node]))
                    fail("single-visit node performed a decision-store probe/write");
                if (!cf_diagnostic_logging) continue;
                if (node == 0U) {
                    CF_METRICS_LOG(NOTICE, "rankstore_node: node=0 table=%s parent=-1 source=none entry=none op=target parent_unique=1 single_visit=1 store_probes=0 store_writes=0",
                         dag_[node].table.c_str());
                    continue;
                }
                const auto leaf = __builtin_ctzll(dag_[node].leaves);
                const auto &edge = *dag_[node].edge_by_leaf[leaf];
                const auto &entry = dag_[node].candidate_is_left_by_leaf[leaf] ? edge.left : edge.right;
                const auto &source = dag_[node].candidate_is_left_by_leaf[leaf] ? edge.right : edge.left;
                CF_METRICS_LOG(NOTICE,
                     "rankstore_node: node=%zu table=%s parent=%zu source=%s entry=%s op=%s parent_unique=%u single_visit=%u store_probes=%llu store_writes=%llu",
                     node, dag_[node].table.c_str(), rank_parent_nodes_[node],
                     source.key().c_str(), entry.key().c_str(), op_name(edge.op),
                     unsigned(rank_parent_unique_[node]), unsigned(rank_single_visit_[node]),
                     static_cast<unsigned long long>(rank_node_probes_[node]),
                     static_cast<unsigned long long>(rank_node_writes_[node]));
            }
            if (cf_diagnostic_logging) rank_store_.visit_gates([&](std::uint32_t id, std::uint32_t ranks,
                std::uint64_t threshold, std::uint64_t probes, std::uint64_t hits,
                std::uint64_t saved, const char *decision) {
                CF_METRICS_LOG(NOTICE,
                     "rankstore_gate: predicate_id=%u entry_column=%s distinct_ranks=%u threshold=%llu probes=%llu hits=%llu saved_reads=%llu decision=%s",
                     id, rank_gate_columns_[id & ((1U << RankPredicateInstance::arity_shift) - 1U)].c_str(), ranks,
                     static_cast<unsigned long long>(threshold), static_cast<unsigned long long>(probes),
                     static_cast<unsigned long long>(hits), static_cast<unsigned long long>(saved), decision);
            });
            for (std::size_t node = 1; cf_diagnostic_logging && node < dag_.size(); ++node) {
                const auto &stats = rank_multirow_by_node_[node];
                if (stats.arrivals == 0U) continue;
                const std::size_t leaf = __builtin_ctzll(dag_[node].leaves);
                const NormalizedAtom &edge = *dag_[node].edge_by_leaf[leaf];
                const ColumnRef &entry = dag_[node].candidate_is_left_by_leaf[leaf] ?
                    edge.left : edge.right;
                CF_METRICS_LOG(NOTICE,
                     "rankstore_connection: table=%s entry_column=%s multirow_arrivals=%llu row_scans=%llu strengthened_stops=%llu good_stops=%llu nogood_stops=%llu row_decisions=0 composite_ranks=0",
                     dag_[node].table.c_str(), entry.key().c_str(),
                     static_cast<unsigned long long>(stats.arrivals),
                     static_cast<unsigned long long>(stats.scans),
                     static_cast<unsigned long long>(stats.good_stops + stats.nogood_stops),
                     static_cast<unsigned long long>(stats.good_stops),
                     static_cast<unsigned long long>(stats.nogood_stops));
            }
            if (cf_diagnostic_logging && cf_rankstore_dump) {
                rank_store_.visit_entries([&](const RankDecisionKey &key, bool truth) {
                    const std::uint32_t id = key.predicate_id();
                    std::string filled;
                    for (unsigned i = 0; i < (id >> RankPredicateInstance::arity_shift); ++i) {
                        if (i) filled += ',';
                        filled += std::to_string(static_cast<std::uint32_t>(
                            key.operands[i / 2U] >> ((i & 1U) * 32U)));
                    }
                    CF_METRICS_LOG(NOTICE, "rankstore_entry: rank=%u predicate_id=%u instance=%s filled_ranks=[%s] verdict=%s",
                         key.rank(), id,
                         rank_predicate_text_[id & ((1U << RankPredicateInstance::arity_shift) - 1U)]->c_str(),
                         filled.c_str(), truth ? "good" : "nogood");
                });
                for (const auto &item : rank_checks_per_arrival_)
                    CF_METRICS_LOG(NOTICE, "rankstore_arrivals: checks=%llu arrivals=%llu",
                         static_cast<unsigned long long>(item.first),
                         static_cast<unsigned long long>(item.second));
            }
        }
        return allowed;
    }



private:
    static constexpr std::uint32_t kNullRank =
        std::numeric_limits<std::uint32_t>::max();
#include "plan_admission.inc"
    static constexpr std::uint64_t kProbation = 8192U;

    static double elapsed_ms(std::chrono::steady_clock::time_point begin,
                             std::chrono::steady_clock::time_point end) {
        return std::chrono::duration<double, std::milli>(end - begin).count();
    }

    enum class FlatFormulaMode { none, conjunction, disjunction };

    bool collect_flat_literals(const FormulaNode *node,
                               FormulaNode::Kind connective,
                               bool negated) {
        if (node == nullptr) return false;
        if (node->kind == FormulaNode::And || node->kind == FormulaNode::Or) {
            // Negation reverses the connective; never flatten NOT(A AND B) as !A AND !B.
            const auto effective = negated ?
                (node->kind == FormulaNode::And ? FormulaNode::Or : FormulaNode::And) : node->kind;
            if (effective != connective) return false;
            return collect_flat_literals(node->left.get(), connective, negated) &&
                   collect_flat_literals(node->right.get(), connective, negated);
        }
        if (node->kind == FormulaNode::Not)
            return collect_flat_literals(node->left.get(), connective, !negated);
        if (node->kind == FormulaNode::Branch) {
            const std::uint64_t bit = std::uint64_t{1} << node->leaf_id;
            (negated ? flat_negative_ : flat_positive_) |= bit;
            return true;
        }
        const bool value = node->kind == FormulaNode::True;
        if (node->kind != FormulaNode::True && node->kind != FormulaNode::False)
            return false;
        const bool effective = negated ? !value : value;
        if ((connective == FormulaNode::And && !effective) ||
            (connective == FormulaNode::Or && effective)) {
            flat_constant_ = effective ? 1 : 0;
        }
        return true;
    }

    void compile_flat_formula() {
        flat_mode_ = FlatFormulaMode::none;
        flat_positive_ = 0;
        flat_negative_ = 0;
        flat_constant_ = -1;
        FormulaNode::Kind connective = FormulaNode::And;
        if (formula_->kind == FormulaNode::Or) connective = FormulaNode::Or;
        else if (formula_->kind != FormulaNode::And &&
                 formula_->kind != FormulaNode::Branch &&
                 formula_->kind != FormulaNode::Not &&
                 formula_->kind != FormulaNode::True &&
                 formula_->kind != FormulaNode::False) return;
        if (!collect_flat_literals(formula_.get(), connective, false)) return;
        flat_mode_ = connective == FormulaNode::And ?
            FlatFormulaMode::conjunction : FlatFormulaMode::disjunction;
        const std::uint64_t contradictory = flat_positive_ & flat_negative_;
        if (contradictory != 0U) {
            flat_constant_ = flat_mode_ == FlatFormulaMode::conjunction ? 0 : 1;
        }
    }

    






    void configure_formula_truth_table() {
        if (flat_mode_ != FlatFormulaMode::none || leaves_.empty() ||
            leaves_.size() > 12U) {
            return;
        }
        formula_ternary_powers_.resize(leaves_.size());
        std::uint64_t states = 1U;
        for (std::size_t leaf = 0; leaf < leaves_.size(); ++leaf) {
            formula_ternary_powers_[leaf] = states;
            states *= 3U;
        }
        formula_truth_table_.resize(static_cast<std::size_t>(states), -1);
        const auto evaluate =
            [&](auto &&self, const FormulaNode *node,
                std::uint64_t state) -> std::int8_t {
                switch (node->kind) {
                    case FormulaNode::Branch: {
                        const std::uint64_t digit =
                            (state / formula_ternary_powers_[node->leaf_id]) % 3U;
                        return digit == 0U ? -1 : (digit == 2U ? 1 : 0);
                    }
                    case FormulaNode::And: {
                        const std::int8_t left = self(self, node->left.get(), state);
                        if (left == 0) return 0;
                        const std::int8_t right = self(self, node->right.get(), state);
                        if (right == 0) return 0;
                        return left == 1 && right == 1 ? 1 : -1;
                    }
                    case FormulaNode::Or: {
                        const std::int8_t left = self(self, node->left.get(), state);
                        if (left == 1) return 1;
                        const std::int8_t right = self(self, node->right.get(), state);
                        if (right == 1) return 1;
                        return left == 0 && right == 0 ? 0 : -1;
                    }
                    case FormulaNode::Not: {
                        const std::int8_t value = self(self, node->left.get(), state);
                        return value < 0 ? -1 : static_cast<std::int8_t>(1 - value);
                    }
                    case FormulaNode::True: return 1;
                    case FormulaNode::False: return 0;
                }
                return -1;
            };
        for (std::uint64_t state = 0; state < states; ++state) {
            formula_truth_table_[static_cast<std::size_t>(state)] =
                evaluate(evaluate, formula_.get(), state);
        }
    }

    int partial_current() const {
        if (flat_mode_ == FlatFormulaMode::none &&
            !formula_truth_table_.empty()) {
            return formula_truth_table_[
                static_cast<std::size_t>(formula_ternary_state_)];
        }
        if (flat_mode_ == FlatFormulaMode::none) return partial(formula_.get());
        if (flat_constant_ >= 0) return flat_constant_;
        const std::uint64_t required = flat_positive_ | flat_negative_;
        if (flat_mode_ == FlatFormulaMode::conjunction) {
            if (((settled_ & flat_positive_) & ~truth_) != 0U ||
                ((settled_ & flat_negative_) & truth_) != 0U) return 0;
            return (settled_ & required) == required ? 1 : -1;
        }
        if (((settled_ & flat_positive_) & truth_) != 0U ||
            ((settled_ & flat_negative_) & ~truth_) != 0U) return 1;
        return (settled_ & required) == required ? 0 : -1;
    }

    DomainIndex &domain(const std::string &id) {
        auto found=domains_.find(id);
        if(found!=domains_.end())return found->second;
        const auto view=lookup_required(arts_,art_count_,in_,"universe/domain/"+id);
        DomainIndex out;
        try { out.values=universe_format::Dictionary::decode(view.data,view.len); }
        catch(const std::exception &error) { fail("domain "+id+": "+error.what()); }
        out.count=out.values.count;out.numeric_kind=out.values.numeric_kind;
        return domains_.emplace(id,std::move(out)).first->second;
    }

    void compile_column(ColumnRef &ref) {
        const auto key=ref.key();const auto found=column_id_by_key_.find(key);
        if(found!=column_id_by_key_.end()) { ref.runtime_column=found->second;return; }
        ColumnIndex out;out.domain=domain_for_column(arts_,art_count_,in_,key);
        const auto inv_name="canon_invidx/"+ref.table+"/"+ref.column;
        out.cix=decode_cix(lookup_required(arts_,art_count_,in_,inv_name),inv_name);
        const auto fwd_name="canon_fwdidx/"+ref.table+"/"+ref.column;
        const auto forward=lookup_required(arts_,art_count_,in_,fwd_name);
        if(forward.len<16U || std::memcmp(forward.data,"CFI2",4U)!=0)
            fail("expected universe-ranked CFI2: "+fwd_name);
        out.forward_rows=u32le(forward.data+4U);
        if(u32le(forward.data+8U)!=out.cix.rank_count || u32le(forward.data+12U)!=0U ||
           forward.len!=16ULL+4ULL*out.forward_rows)
            fail("CFI2 metadata mismatch: "+key);
        out.forward_ranks=reinterpret_cast<const std::uint32_t *>(forward.data+16U);
        if(domain(out.domain).count!=out.cix.rank_count)fail("column universe size mismatch: "+key);
        ref.runtime_column=columns_.size();columns_.push_back(std::move(out));
        column_id_by_key_.emplace(key,ref.runtime_column);
    }

    ColumnIndex &column(const ColumnRef &ref) {
        if (ref.runtime_column >= columns_.size())
            fail("uncompiled column reference " + ref.key());
        return columns_[ref.runtime_column];
    }

    std::uint32_t row_local_rank(const ColumnRef &ref,std::uint32_t row) {
        if (!target_walk_started_ && ref.node_id!=target_node_)
            fail("witness forward read before the first target row");
        const auto &idx=column(ref);
        return row<idx.forward_rows ? idx.forward_ranks[row] : kNullRank;
    }

    std::uint32_t row_universe_rank(const ColumnRef &ref,std::uint32_t row) {
        return row_local_rank(ref,row);
    }

    std::pair<std::uint32_t,std::uint32_t> literal_bounds(const std::string &id,std::string_view literal) {
        const std::pair<std::string,std::string> key{id,std::string(literal)};
        const auto cached=literal_bounds_cache_.find(key);
        if(cached!=literal_bounds_cache_.end())return cached->second;
        auto &dom=domain(id);
        const auto compare=[&](std::uint32_t rank) {
            const auto value=dom.values.value(rank);
            return dom.numeric_kind ? rankfix_numeric_compare(value,literal,dom.numeric_kind) : value.compare(literal);
        };
        // The offline dictionary is unique in comparison semantics. One lower_bound gives L;
        // U is L+1 exactly when L contains the constant, otherwise U=L.
        std::uint32_t lower=0,upper=dom.count;
        while(lower<upper) {
            const auto middle=lower+(upper-lower)/2;
            if(compare(middle)<0)lower=middle+1;else upper=middle;
        }
        upper=lower+(lower<dom.count && compare(lower)==0);
        const auto result=std::make_pair(lower,upper);
        literal_bounds_cache_.emplace(key,result);return result;
    }

    static bool compare_rank(std::uint32_t left, int op, std::uint32_t right) {
        switch (op) {
            case POLICY_OP_EQ: return left == right;
            case POLICY_OP_LT: return left < right;
            case POLICY_OP_LE: return left <= right;
            case POLICY_OP_GT: return left > right;
            case POLICY_OP_GE: return left >= right;
            case POLICY_OP_NE: return left != right;
            default: fail("invalid rank comparison operator");
        }
    }

    bool atom_holds(const NormalizedAtom &atom) {
        const std::int64_t left_row = bindings_[atom.left.node_id];
        if (left_row < 0) return true;
        const std::uint32_t left =
            row_universe_rank(atom.left, static_cast<std::uint32_t>(left_row));
        if (left == kNullRank) return false;
        if (!atom.right_is_const) {
            const std::int64_t right_row = bindings_[atom.right.node_id];
            if (right_row < 0) return true;
            ColumnIndex &left_column = column(atom.left);
            ColumnIndex &right_column = column(atom.right);
            if (left_column.domain != right_column.domain)
                fail("atom y" + std::to_string(atom.atom_id) + " crosses canonical universes");
            const std::uint32_t right =
                row_universe_rank(atom.right, static_cast<std::uint32_t>(right_row));
            return right != kNullRank && compare_rank(left, atom.op, right);
        }
        if (!atom.constant_compiled)
            fail("constant atom was not compiled before evaluation");
        const std::uint32_t lower = atom.constant_lower;
        const std::uint32_t upper = atom.constant_upper;
        switch (atom.op) {
            case POLICY_OP_EQ: return left >= lower && left < upper;
            case POLICY_OP_LT: return left < lower;
            case POLICY_OP_LE: return left < upper;
            case POLICY_OP_GT: return left >= upper;
            case POLICY_OP_GE: return left >= lower;
            case POLICY_OP_NE: return left < lower || left >= upper;
            default: fail("invalid constant comparison operator");
        }
    }

    LookupResult edge_lookup(const NormalizedAtom &edge,
                             bool candidate_is_left) {
        const ColumnRef &candidate = candidate_is_left ? edge.left : edge.right;
        const ColumnRef &pivot = candidate_is_left ? edge.right : edge.left;
        const std::int64_t pivot_row = bindings_[pivot.node_id];
        if (pivot_row < 0) fail("fused edge pivot is unbound");
        ColumnIndex &candidate_index = column(candidate);
        ColumnIndex &pivot_index = column(pivot);
        if (candidate_index.domain != pivot_index.domain)
            fail("fused edge crosses canonical universes");
        const int op = normalized_edge_op(edge, candidate_is_left);
        const std::uint32_t pivot_local =
            row_local_rank(pivot, static_cast<std::uint32_t>(pivot_row));
        LookupResult out;
        if (pivot_local == kNullRank) return out;
        // Both columns already use the same universe numbering, including empty postings.
        const std::uint32_t lower=pivot_local,upper=pivot_local+1U;
        if(pivot_local>=candidate_index.cix.rank_count)fail("entering rank exceeds universe");
        const std::uint32_t n = candidate_index.cix.rank_count;
        switch (op) {
            case POLICY_OP_EQ:
                if (lower < upper) {
                    out.ranges[0] = {lower, upper};
                    out.count = 1;
                }
                break;
            case POLICY_OP_LT: out.ranges[0] = {0U, lower}; out.count = 1; break;
            case POLICY_OP_LE: out.ranges[0] = {0U, upper}; out.count = 1; break;
            case POLICY_OP_GT: out.ranges[0] = {upper, n}; out.count = 1; break;
            case POLICY_OP_GE: out.ranges[0] = {lower, n}; out.count = 1; break;
            case POLICY_OP_NE:
                out.ranges[0] = {0U, lower};
                out.ranges[1] = {upper, n};
                out.count = 2;
                break;
            default: fail("invalid fused edge operator");
        }
        return out;
    }

    void collect_subtree_occurrences(std::size_t node,
                                     std::size_t leaf,
                                     std::set<int> *out) const {
        const std::uint64_t bit = std::uint64_t{1} << leaf;
        if ((dag_[node].leaves & bit) == 0) return;
        const int occurrence = dag_[node].occurrence_by_leaf[leaf];
        if (occurrence >= 0) out->insert(occurrence);
        for (std::size_t child : dag_[node].children)
            collect_subtree_occurrences(child, leaf, out);
    }

    void compile_dependencies() {
        for (std::size_t node = 1; node < dag_.size(); ++node) {
            for (std::size_t leaf = 0; leaf < leaves_.size(); ++leaf) {
                const std::uint64_t bit = std::uint64_t{1} << leaf;
                if ((dag_[node].leaves & bit) == 0) continue;
                std::set<int> subtree;
                collect_subtree_occurrences(node, leaf, &subtree);
                std::set<std::pair<int, std::string>> seen;
                auto add = [&](const ColumnRef &ref) {
                    const auto key = std::make_pair(ref.node_id, ref.key());
                    if (seen.insert(key).second)
                        dependencies_[node][leaf].push_back(ref);
                };
                const NormalizedAtom *edge = dag_[node].edge_by_leaf[leaf];
                const bool candidate_left = dag_[node].candidate_is_left_by_leaf[leaf];
                add(candidate_left ? edge->right : edge->left);
                for (const NormalizedAtom *atom : leaves_[leaf]->atoms) {
                    if (atom->right_is_const) continue;
                    const bool left_inside = subtree.count(atom->left.node_id) != 0;
                    const bool right_inside = subtree.count(atom->right.node_id) != 0;
                    if (left_inside == right_inside) continue;
                    add(left_inside ? atom->right : atom->left);
                }
                for (const LocalBooleanGroup &group :
                     leaves_[leaf]->boolean_groups) {
                    for (const NormalizedAtom *atom : group.atoms) {
                        if (atom->right_is_const) continue;
                        const bool left_inside =
                            subtree.count(atom->left.node_id) != 0;
                        const bool right_inside =
                            subtree.count(atom->right.node_id) != 0;
                        if (left_inside == right_inside) continue;
                        add(left_inside ? atom->right : atom->left);
                    }
                }
                if (dependencies_[node][leaf].size() > 16U)
                    memo_[node][leaf].enabled = false;
            }
        }
    }

    bool column_is_unique(const ColumnRef &ref) { return column(ref).cix.unique; }
    std::uint32_t column_distinct_ranks(const ColumnRef &ref) { return column(ref).cix.present_count; }

    void configure_single_visits() {
        rank_single_visit_.assign(dag_.size(), 0U);
        rank_parent_unique_.assign(dag_.size(), 0U);
        rank_parent_nodes_.assign(dag_.size(), 0U);
        rank_node_probes_.assign(dag_.size(), 0U);
        rank_node_writes_.assign(dag_.size(), 0U);
        rank_single_visit_[0] = 1U;
        const auto visit = [&](auto &&self, std::size_t parent) -> void {
            for (const auto child : dag_[parent].children) {
                bool unique = true, exact = true, direct = true;
                for (auto bits = dag_[child].leaves; bits; bits &= bits - 1U) {
                    const auto leaf = __builtin_ctzll(bits);
                    const auto &edge = *dag_[child].edge_by_leaf[leaf];
                    const auto &source = dag_[child].candidate_is_left_by_leaf[leaf] ? edge.right : edge.left;
                    unique = column_is_unique(source) && unique;
                    exact = edge.op == POLICY_OP_EQ && exact;
                    direct = std::find(dag_[parent].bound_occurrences.begin(),
                        dag_[parent].bound_occurrences.end(), source.node_id) !=
                        dag_[parent].bound_occurrences.end() && direct;
                }
                rank_parent_nodes_[child] = parent;
                rank_parent_unique_[child] = unique;
                // Unique pivots do not make overlapping theta ranges single-visit.
                rank_single_visit_[child] = rank_single_visit_[parent] && unique && exact && direct;
                self(self, child);
            }
        };
        visit(visit, 0U);
    }

    std::uint32_t entering_rank(std::size_t node_index) {
        const FusedDagNode &node = dag_[node_index];
        if (node.leaves == 0U) return kNullRank;
        const std::size_t leaf = static_cast<std::size_t>(
            __builtin_ctzll(node.leaves));
        const NormalizedAtom &edge = *node.edge_by_leaf[leaf];
        const bool candidate_left = node.candidate_is_left_by_leaf[leaf];
        const ColumnRef &parent = candidate_left ? edge.right : edge.left;
        const std::int64_t row = bindings_[parent.node_id];
        return row < 0 ? kNullRank :
            row_local_rank(parent, static_cast<std::uint32_t>(row));
    }

    bool proof_atom_is_local_to_entry(std::size_t node_index,
                                      const NormalizedAtom &atom) const {
        const FusedDagNode &node = dag_[node_index];
        const std::size_t representative = static_cast<std::size_t>(
            __builtin_ctzll(node.leaves));
        const NormalizedAtom &edge = *node.edge_by_leaf[representative];
        const bool candidate_left =
            node.candidate_is_left_by_leaf[representative];
        const ColumnRef &parent = candidate_left ? edge.right : edge.left;
        const auto determined = [&](const ColumnRef &ref) {
            if (ref.node_id == parent.node_id &&
                ref.runtime_column == parent.runtime_column) return true;
            return std::find(node.bound_occurrences.begin(),
                             node.bound_occurrences.end(),
                             ref.node_id) != node.bound_occurrences.end();
        };
        return determined(atom.left) &&
            (atom.right_is_const || determined(atom.right));
    }

    bool proof_group_is_local_to_entry(
            std::size_t node_index,
            const LocalBooleanGroup &group) const {
        return std::all_of(
            group.atoms.begin(), group.atoms.end(),
            [&](const NormalizedAtom *atom) {
                return proof_atom_is_local_to_entry(node_index, *atom);
            });
    }

    void configure_rank_proofs() {
        if (!rank_proofs_enabled_) return;
        node_rank_proofs_.resize(dag_.size());
        subtree_proof_masks_.resize(dag_.size());
        proof_key_safe_.resize(dag_.size());
        local_stable_proof_masks_.assign(dag_.size(), 0U);
        for (std::size_t node_index = 1;
             node_index < dag_.size(); ++node_index) {
            FusedDagNode &node = dag_[node_index];
            const std::size_t representative = static_cast<std::size_t>(
                __builtin_ctzll(node.leaves));
            const NormalizedAtom &edge =
                *node.edge_by_leaf[representative];
            const bool candidate_left =
                node.candidate_is_left_by_leaf[representative];
            const ColumnRef &parent = candidate_left ? edge.right : edge.left;
            // A representative's connection proof cannot prove another operator.
            if(fused_node_is_mixed(node))continue;
            node.edge_proof_bit = edge.proof_bit;
            node_rank_proofs_[node_index].cardinality =
                column(parent).cix.rank_count;
            // The entering rank determines this row, not unrelated earlier bindings.
            // Keep every outside operand used anywhere in this node's remaining tail.
            std::map<std::pair<int, std::string>, ColumnRef> filled;
            for (const auto &dependencies : dependencies_[node_index]) {
                for (const ColumnRef &ref : dependencies) {
                    if (ref.node_id == parent.node_id &&
                        ref.runtime_column == parent.runtime_column) continue;
                    filled.emplace(std::make_pair(ref.node_id, ref.key()), ref);
                }
            }
            for (const auto &item : filled)
                node_rank_proofs_[node_index].filled_columns.push_back(item.second);
            if(rank_store_mode_ && rank_single_visit_[node_index])
                node_rank_proofs_[node_index].cardinality=0;
            else if(filled.empty() && !reserve_dense_cache(node_rank_proofs_[node_index].cardinality*sizeof(RankProofCell)))
                node_rank_proofs_[node_index].sparse=true;
            if (filled.size() > RankPredicateInstance::max_operands)
                fail("rank proof exceeds fixed-width filled operand capacity (16)");
            auto &proof_plan=node_rank_proofs_[node_index];
            if(proof_plan.cardinality)proof_plan.summary=rank_store_.add_proof_region(proof_plan.cardinality,
                proof_plan.filled_columns.size(),proof_plan.sparse);
            for (const FusedDagNode::CompiledFilter &filter :
                 node.compiled_filters) {
                if (proof_atom_is_local_to_entry(node_index, *filter.atom))
                    local_stable_proof_masks_[node_index] |=
                        filter.atom->proof_bit;
            }
            for (const FusedDagNode::CompiledBooleanGroup &group :
                 node.compiled_boolean_groups) {
                if (proof_group_is_local_to_entry(node_index, *group.group))
                    local_stable_proof_masks_[node_index] |=
                        group.group->proof_bit;
            }
            subtree_proof_masks_[node_index].fill(0U);
            proof_key_safe_[node_index].fill(0U);
        }

        std::vector<std::array<std::int8_t, 64>> state(dag_.size());
        for (auto &values : state) values.fill(0);
        const auto build = [&](auto &&self, std::size_t node_index,
                               std::size_t leaf) -> bool {
            std::int8_t &cached = state[node_index][leaf];
            if (cached != 0) return cached > 0;
            FusedDagNode &node = dag_[node_index];
            const std::uint64_t leaf_bit = std::uint64_t{1} << leaf;
            if ((node.leaves & leaf_bit) == 0U) {
                cached = -1;
                return false;
            }
            const NormalizedAtom &edge = *node.edge_by_leaf[leaf];
            const bool candidate_left = node.candidate_is_left_by_leaf[leaf];
            const ColumnRef &candidate = candidate_left ? edge.left : edge.right;
            std::uint64_t mask = edge.proof_bit;
            bool safe = !fused_node_is_mixed(node) && edge.op == POLICY_OP_EQ && column_is_unique(candidate);
            for (const NormalizedAtom *atom : node.filters_by_leaf[leaf]) {
                mask |= atom->proof_bit;
                safe = safe && proof_atom_is_local_to_entry(node_index, *atom);
            }
            for (const LocalBooleanGroup *group :
                 node.boolean_groups_by_leaf[leaf]) {
                mask |= group->proof_bit;
                safe = safe && proof_group_is_local_to_entry(
                    node_index, *group);
            }
            for (std::size_t child : node.children) {
                if ((dag_[child].leaves & leaf_bit) == 0U) continue;
                safe = self(self, child, leaf) && safe;
                mask |= subtree_proof_masks_[child][leaf];
            }
            subtree_proof_masks_[node_index][leaf] = mask;
            proof_key_safe_[node_index][leaf] = safe ? 1U : 0U;
            cached = safe ? 1 : -1;
            return safe;
        };
        for (std::size_t node_index = 1;
             node_index < dag_.size(); ++node_index) {
            for (std::uint64_t bits = dag_[node_index].leaves;
                 bits != 0U; bits &= bits - 1U) {
                const std::size_t leaf = static_cast<std::size_t>(
                    __builtin_ctzll(bits));
                (void)build(build, node_index, leaf);
            }
        }
    }

    void configure_functional_rank_projections() {
        functional_rank_projections_.resize(dag_.size());
#ifdef SETU_DIAG_DISABLE_PROJECTIONS
        return;
#endif
        if (!rank_proofs_enabled_) return;
        for (std::size_t node_index = 1;
             node_index < dag_.size(); ++node_index) {
            const FusedDagNode &node = dag_[node_index];
            const std::size_t representative = static_cast<std::size_t>(
                __builtin_ctzll(node.leaves));
            const NormalizedAtom &edge = *node.edge_by_leaf[representative];
            const bool candidate_left =
                node.candidate_is_left_by_leaf[representative];
            const ColumnRef &candidate_entry =
                candidate_left ? edge.left : edge.right;
            const ColumnRef &parent_entry =
                candidate_left ? edge.right : edge.left;
            if (edge.op != POLICY_OP_EQ ||
                !column_is_unique(candidate_entry)) continue;
            const std::size_t cardinality = column(parent_entry).cix.rank_count;
            if(cf_cost_single_visit && decision_repeat_ratio(planned_arrivals_[node_index],{parent_entry})<=1.0)continue;
            const int occurrence = node.occurrence_by_leaf[representative];
            std::set<std::uint64_t> seen;
            for (const FusedDagNode::CompiledFilter &compiled :
                 node.compiled_filters) {
                const NormalizedAtom &atom = *compiled.atom;
                if (atom.right_is_const || atom.proof_bit == 0U ||
                    !seen.insert(atom.proof_bit).second) continue;
                const bool left_child = atom.left.node_id == occurrence;
                const bool right_child = atom.right.node_id == occurrence;
                if (left_child == right_child) continue;
                const ColumnRef &child = left_child ? atom.left : atom.right;
                const ColumnRef &bound = left_child ? atom.right : atom.left;
                if (bound.node_id == parent_entry.node_id &&
                    bound.runtime_column == parent_entry.runtime_column) {
                    continue;
                }
                FunctionalRankProjection projection;
                projection.child_column = child;
                projection.bound_column = bound;
                projection.op = left_child ? atom.op : invert_op(atom.op);
                projection.proof_bit = atom.proof_bit;
                if (!reserve_dense_cache(cardinality*sizeof(std::uint32_t))) projection.child_rank_by_entering_rank.select_sparse();
                projection.child_rank_by_entering_rank.assign(
                    cardinality, FunctionalRankProjection::unknown);
                functional_rank_projections_[node_index].push_back(
                    std::move(projection));
            }
        }
    }

    bool projected_theta_passes(FunctionalRankProjection &projection,
                                std::uint32_t child_rank,std::uint32_t bound_rank) {
        if(child_rank==FunctionalRankProjection::null_rank || bound_rank==kNullRank)return false;
        if(column(projection.child_column).domain!=column(projection.bound_column).domain)
            fail("functional comparison crosses universes");
        return compare_rank(child_rank,projection.op,bound_rank);
    }

    void configure_bound_pair_caches() {
        constexpr std::size_t max_ways = 16U;
        bound_pair_caches_.resize(dag_.size());
        for (std::size_t node_index = 1;
             node_index < dag_.size(); ++node_index) {
            const FusedDagNode &node = dag_[node_index];
            const std::size_t representative = static_cast<std::size_t>(
                __builtin_ctzll(node.leaves));
            const NormalizedAtom &edge = *node.edge_by_leaf[representative];
            const bool entry_left =
                node.candidate_is_left_by_leaf[representative];
            const ColumnRef &primary_child =
                entry_left ? edge.left : edge.right;
            if (edge.op != POLICY_OP_EQ) continue;

            const NormalizedAtom *selected = nullptr;
            for (const FusedDagNode::CompiledFilter &compiled :
                 node.compiled_filters) {
                const NormalizedAtom &atom = *compiled.atom;
                if (compiled.leaves != node.leaves ||
                    atom.right_is_const || atom.op != POLICY_OP_EQ) continue;
                const int occurrence =
                    node.occurrence_by_leaf[representative];
                const bool left_child = atom.left.node_id == occurrence;
                const bool right_child = atom.right.node_id == occurrence;
                if (left_child == right_child) continue;
                const ColumnRef &child = left_child ? atom.left : atom.right;
                if (child.runtime_column == primary_child.runtime_column) continue;
                if (selected != nullptr) {
                    selected = nullptr;
                    break;
                }
                selected = &atom;
            }
            if (selected == nullptr) continue;
            const int occurrence = node.occurrence_by_leaf[representative];
            const bool secondary_left = selected->left.node_id == occurrence;
            const ColumnRef &secondary_child =
                secondary_left ? selected->left : selected->right;
            const ColumnRef &secondary_bound =
                secondary_left ? selected->right : selected->left;
            ColumnIndex &primary_index = column(primary_child);
            std::size_t ways = 0;
            if(cf_cost_present_caps)ways=(std::uint64_t(primary_index.cix.row_count)+
                std::max(1U,primary_index.cix.present_count)-1U)/std::max(1U,primary_index.cix.present_count);
            else for (std::uint32_t rank = 0;
                 rank < primary_index.cix.rank_count; ++rank) {
                const std::uint32_t begin = primary_index.cix.begin(rank);
                const std::uint32_t end = primary_index.cix.end(rank);
                ways = std::max<std::size_t>(ways, end - begin);
            }
            const std::size_t primary_count = primary_index.cix.rank_count;
            if (ways == 0U || ways > max_ways) continue;
            BoundPairCache &cache = bound_pair_caches_[node_index];
            if (!reserve_dense_cache(primary_count*(2U+ways*sizeof(BoundPairSlot)))) {
                cache.ready.select_sparse();cache.ambiguous.select_sparse();cache.slots.select_sparse();
            }
            cache.eligible = true;
            cache.primary_child_column = primary_child;
            cache.secondary_child_column = secondary_child;
            cache.secondary_bound_column = secondary_bound;
            cache.primary_count = primary_count;
            cache.ways = ways;
            cache.ready.assign(primary_count, 0U);
            cache.ambiguous.assign(primary_count, 0U);
            cache.slots.resize(primary_count * ways);
        }
    }

    bool proof_instance(std::size_t node, RankPredicateInstance *instance) {
        const auto &columns = node_rank_proofs_[node].filled_columns;
        const auto &summary=rank_store_.summaries[node_rank_proofs_[node].summary];
        return RankDecisionStore::Key(summary.region_predicate,columns.size(),[&](unsigned i,unsigned &value){
            const auto &ref = columns[i];
            const auto row = bindings_[ref.node_id];
            if (row < 0) return false;
            value = row_universe_rank(ref, static_cast<std::uint32_t>(row));return true;
        },*instance);
    }

    RankProofCell *ensure_rank_proof(std::size_t node, std::uint32_t rank) {
        if(!node_rank_proofs_[node].cardinality)return nullptr;
        RankPredicateInstance instance;
        if (!proof_instance(node, &instance)) return nullptr;
        return rank_store_.Record(rank_store_.summaries[node_rank_proofs_[node].summary],rank,instance,&bound_record_refusals_);
    }

    void lookup_rank_proof(std::size_t node_index,
                           std::uint64_t requested,
                           std::uint32_t *key_rank,
                           std::uint64_t *decided,
                           std::uint64_t *truth) {
        *key_rank = kNullRank;
        *decided = 0U;
        *truth = 0U;
        if (!rank_proofs_enabled_) return;
        if(!node_rank_proofs_[node_index].cardinality)return;
        *key_rank = entering_rank(node_index);
        if (*key_rank == kNullRank) return;
        RankPredicateInstance instance;
        const RankProofCell *proof = proof_instance(node_index, &instance) ?
            rank_store_.Probe(rank_store_.summaries[node_rank_proofs_[node_index].summary],*key_rank,instance) : nullptr;
        std::uint64_t available_decided = 0U;
        std::uint64_t available_truth = 0U;
        if (proof != nullptr) {
            available_decided = proof->decided;
            available_truth = proof->truth;
        }
        for (FunctionalRankProjection &projection :
             functional_rank_projections_[node_index]) {
            if (*key_rank >= projection.child_rank_by_entering_rank.size())
                continue;
            const std::uint32_t child_rank =
                projection.child_rank_by_entering_rank[*key_rank];
            if (child_rank == FunctionalRankProjection::unknown) continue;
            const std::int64_t bound_row =
                bindings_[projection.bound_column.node_id];
            if (bound_row < 0) continue; // Unbound is not a failed comparison.
            available_decided |= projection.proof_bit;
            available_truth &= ~projection.proof_bit;
            const std::uint32_t bound_rank =
                row_local_rank(projection.bound_column,
                    static_cast<std::uint32_t>(bound_row));
            if (projected_theta_passes(
                    projection, child_rank, bound_rank)) {
                available_truth |= projection.proof_bit;
            }
            CF_COUNT(++functional_projection_hits_);
        }
        for (std::uint64_t bits = requested;
             bits != 0U; bits &= bits - 1U) {
            const std::size_t leaf = static_cast<std::size_t>(
                __builtin_ctzll(bits));
            const std::uint64_t leaf_bit = std::uint64_t{1} << leaf;
            const std::uint64_t required =
                subtree_proof_masks_[node_index][leaf];
            const std::uint64_t known = available_decided & required;
            if ((known & ~available_truth) != 0U) {
                *decided |= leaf_bit;
            } else if (required != 0U && known == required) {
                *decided |= leaf_bit;
                *truth |= leaf_bit;
            }
        }
    }

    static std::string filter_signature(const NormalizedAtom &atom) {
        std::string result = atom.left.table + "." + atom.left.column + "|" +
            std::to_string(atom.op) + "|";
        if (atom.right_is_const) {
            result += "const|" + atom.literal;
        } else {
            result += atom.right.table + "." + atom.right.column;
        }
        return result;
    }

    static std::string boolean_group_signature(
            const LocalBooleanGroup &group) {
        std::string result;
        for (const LocalBooleanToken &token : group.postfix) {
            if (token.kind == LocalBooleanTokenKind::atom) {
                result += "A{" + filter_signature(*token.atom) + "};";
            } else {
                result += token.kind == LocalBooleanTokenKind::conjunction ?
                    "AND;" : "OR;";
            }
        }
        return result;
    }

    void compile_filter_masks() {
        for (FusedDagNode &node : dag_) {
            std::map<std::string, std::size_t> by_signature;
            std::map<std::string, std::size_t> groups_by_signature;
            for (std::size_t leaf = 0; leaf < leaves_.size(); ++leaf) {
                const std::uint64_t bit = std::uint64_t{1} << leaf;
                if ((node.leaves & bit) == 0U) continue;
                for (const NormalizedAtom *atom : node.filters_by_leaf[leaf]) {
                    const std::string signature = filter_signature(*atom);
                    auto found = by_signature.find(signature);
                    if (found == by_signature.end()) {
                        const std::size_t index = node.compiled_filters.size();
                        node.compiled_filters.push_back(
                            FusedDagNode::CompiledFilter{atom, bit});
                        by_signature.emplace(signature, index);
                    } else {
                        node.compiled_filters[found->second].leaves |= bit;
                    }
                }
                for (const LocalBooleanGroup *group :
                     node.boolean_groups_by_leaf[leaf]) {
                    const std::string signature =
                        boolean_group_signature(*group);
                    auto found = groups_by_signature.find(signature);
                    if (found == groups_by_signature.end()) {
                        const std::size_t index =
                            node.compiled_boolean_groups.size();
                        node.compiled_boolean_groups.push_back(
                            FusedDagNode::CompiledBooleanGroup{group, bit});
                        groups_by_signature.emplace(signature, index);
                    } else {
                        node.compiled_boolean_groups[found->second].leaves |= bit;
                    }
                }
            }
        }
    }

    bool leaf_occurs_below(std::size_t node, std::uint64_t bit) const {
        for (std::size_t child : dag_[node].children)
            if ((dag_[child].leaves & bit) != 0U) return true;
        return false;
    }

    static bool same_ref(const ColumnRef &left, const ColumnRef &right) {
        return left.node_id == right.node_id && left.table == right.table &&
               left.column == right.column;
    }

    bool terminal_key_for_leaf(std::size_t node_index,
                               std::size_t leaf,
                               std::vector<ColumnRef> *bound,
                               std::vector<ColumnRef> *child,
                               bool *lazy_bound_filters) {
        const FusedDagNode &node = dag_[node_index];
        
        
        
        if (!node.boolean_groups_by_leaf[leaf].empty()) return false;
        const int occurrence = node.occurrence_by_leaf[leaf];
        const NormalizedAtom *edge = node.edge_by_leaf[leaf];
        if (occurrence < 0 || edge == nullptr || edge->right_is_const ||
            edge->op != POLICY_OP_EQ) return false;
        auto add_pair = [&](const ColumnRef &candidate,
                            const ColumnRef &outside) {
            for (std::size_t i = 0; i < bound->size(); ++i) {
                if (same_ref((*bound)[i], outside))
                    return same_ref((*child)[i], candidate);
            }
            bound->push_back(outside);
            child->push_back(candidate);
            return true;
        };
        const bool edge_left = edge->left.node_id == occurrence;
        const bool edge_right = edge->right.node_id == occurrence;
        if (edge_left == edge_right) return false;
        const ColumnRef &primary_child = edge_left ? edge->left : edge->right;
        const ColumnRef &primary_bound = edge_left ? edge->right : edge->left;
        if (!add_pair(primary_child, primary_bound)) return false;

        
        
        
        
        ColumnIndex &primary_bound_index = column(primary_bound);
        const bool primary_unique = primary_bound_index.cix.unique;
        *lazy_bound_filters = false;

        for (const NormalizedAtom *atom : node.filters_by_leaf[leaf]) {
            if (atom->right_is_const) {
                if (atom->left.node_id != occurrence) return false;
                continue;
            }
            const bool left_child = atom->left.node_id == occurrence;
            const bool right_child = atom->right.node_id == occurrence;
            if (left_child && right_child) continue;
            if (left_child == right_child) return false;
            const ColumnRef &candidate = left_child ? atom->left : atom->right;
            const ColumnRef &outside = left_child ? atom->right : atom->left;
            if (atom->op == POLICY_OP_EQ) {
                if (!add_pair(candidate, outside)) return false;
                continue;
            }
            if (!primary_unique || outside.node_id != primary_bound.node_id)
                return false;
            *lazy_bound_filters = true;
        }
        return !bound->empty() && bound->size() <= 16U;
    }

    // Describe terminal lookups without touching any witness row.
    void compile_terminal_verdicts() {
        terminal_groups_by_node_.resize(dag_.size());
        for (std::size_t node=1;node<dag_.size();++node) {
            for (auto bits=dag_[node].leaves;bits;bits&=bits-1U) {
                const auto leaf=static_cast<std::size_t>(__builtin_ctzll(bits));
                const auto bit=std::uint64_t{1}<<leaf;
                if (leaf_occurs_below(node,bit) || (chain_plans_[leaf].enabled && chain_plans_[leaf].full)) continue;
                TerminalVerdictGroup group;group.node=node;group.leaves=bit;
                bool has_bound_filters=false;
                if (!terminal_key_for_leaf(node,leaf,&group.bound_columns,&group.child_columns,&has_bound_filters)) continue;
                // A multi-equality hop has ONE entering rank. The other
                // equalities belong to its filled predicate. Do not bypass
                // that node store with a tuple-keyed terminal verdict cache.
                // solve_rank_node uses the existing per-column postings and
                // rank_full_plans_ / rank_local_plans_ for these requests.
                if(group.child_columns.size()>1U) continue;
                const auto occurrence=dag_[node].occurrence_by_leaf[leaf];
                // Include every outside operand; the equality tuple alone is not enough.
                for (auto atom:dag_[node].filters_by_leaf[leaf]) {
                    for (auto ref:{&atom->left,atom->right_is_const ? nullptr : &atom->right}) {
                        if (!ref || ref->node_id==occurrence) continue;
                        if (std::none_of(group.bound_columns.begin(),group.bound_columns.end(),
                            [&](const ColumnRef &known){return same_ref(*ref,known);})) group.bound_columns.push_back(*ref);
                    }
                }
                if (group.bound_columns.size()>16U) continue;
                if(cf_cost_single_visit) {
                    group.gate_id=rank_full_plans_[node][leaf].id;
                    group.cache_mode=group.gate_id ? 2 : 0;
                    for(const auto &a:cost_admissions_)if(a.node==node && a.leaf==leaf && a.tail && a.ratio>=4.0 && a.id)
                        group.cache_mode=3;
                }
                // Joint supported equality tuples in one relation are bounded
                // by its row count, not the product of marginal distinct ranks.
                // Additional outside operands remain part of the full key.
                if(group.child_columns.size()>1U) {
                    double distinct=1,shortest=1e100;
                    for(const auto &ref:group.child_columns)
                    {
                        const auto &header=column(ref).cix;
                        distinct=std::min(1e100,distinct*std::max(1U,header.present_count));
                        shortest=std::min(shortest,double(header.row_count)/std::max(1U,header.present_count));
                    }
                    distinct=std::min(distinct,double(column(group.child_columns.front()).cix.row_count));
                    for(std::size_t i=group.child_columns.size();i<group.bound_columns.size();++i)
                        distinct=std::min(1e100,distinct*std::max(1U,column(group.bound_columns[i]).cix.present_count));
                    const bool target_bound=std::all_of(group.bound_columns.begin(),group.bound_columns.end(),
                        [&](const ColumnRef &ref){return ref.node_id==target_node_;});
                    const auto arrivals=target_bound ? planned_leaf_arrivals_[leaf] : planned_arrivals_[node];
                    group.cost=full_reuse::composite_cache_cost(arrivals,distinct,shortest,
                        group.child_columns.size(),group.bound_columns.size(),
                        sizeof(FusedMemoKey)+sizeof(std::uint64_t)+2U*sizeof(void*));
                    if(!group.cost.admitted)group.cache_mode=0;
                    else if(group.cache_mode==0)group.cache_mode=1;
                }
                switch(group.cache_mode) {
                    case 0:group.lookup=&FusedWalkRuntime::terminal_group_lookup_mode<0>;break;
                    case 1:group.lookup=&FusedWalkRuntime::terminal_group_lookup_mode<1>;break;
                    case 2:group.lookup=&FusedWalkRuntime::terminal_group_lookup_mode<2>;break;
                    case 3:group.lookup=&FusedWalkRuntime::terminal_group_lookup_mode<3>;break;
                }
                terminal_groups_by_node_[node].push_back(terminal_groups_.size());
                terminal_groups_.push_back(std::move(group));
            }
        }
    }

    bool target_equivalent_column(std::size_t leaf,
                                  const ColumnRef &source,
                                  ColumnRef *target_ref) const {
        std::vector<ColumnRef> connected{source};
        auto contains = [&](const ColumnRef &ref) {
            return std::any_of(
                connected.begin(), connected.end(),
                [&](const ColumnRef &item) { return same_ref(item, ref); });
        };
        bool changed = true;
        while (changed) {
            changed = false;
            for (const NormalizedAtom *atom : leaves_[leaf]->atoms) {
                if (atom->right_is_const || atom->op != POLICY_OP_EQ) continue;
                const bool left = contains(atom->left);
                const bool right = contains(atom->right);
                if (left == right) continue;
                connected.push_back(left ? atom->right : atom->left);
                changed = true;
            }
        }
        for (const ColumnRef &ref : connected) {
            if (ref.node_id == target_node_) {
                *target_ref = ref;
                return true;
            }
        }
        return false;
    }

    std::size_t dag_parent(std::size_t child) const {
        for (std::size_t parent = 0; parent < dag_.size(); ++parent) {
            if (std::find(dag_[parent].children.begin(),
                          dag_[parent].children.end(), child) !=
                dag_[parent].children.end()) {
                return parent;
            }
        }
        return SIZE_MAX;
    }

    void compile_root_terminal_probes() {
        for (std::size_t group_index = 0;
             group_index < terminal_groups_.size(); ++group_index) {
            const TerminalVerdictGroup &group = terminal_groups_[group_index];
            if(group.cache_mode==0)continue;
            for (std::uint64_t bits = group.leaves;
                 bits != 0U; bits &= bits - 1U) {
                const std::size_t leaf = static_cast<std::size_t>(
                    __builtin_ctzll(bits));
                bool transparent = true;
                std::size_t ancestor = dag_parent(group.node);
                while (ancestor != SIZE_MAX && ancestor != 0U) {
                    if (!dag_[ancestor].filters_by_leaf[leaf].empty() ||
                        !dag_[ancestor].boolean_groups_by_leaf[leaf].empty()) {
                        transparent = false;
                        break;
                    }
                    std::size_t matching_children = 0;
                    for (std::size_t child : dag_[ancestor].children)
                        matching_children +=
                            (dag_[child].leaves &
                             (std::uint64_t{1} << leaf)) != 0U;
                    if (matching_children != 1U) {
                        transparent = false;
                        break;
                    }
                    ancestor = dag_parent(ancestor);
                }
                if (!transparent || ancestor != 0U) continue;
                RootTerminalProbe probe;
                probe.group = group_index;
                probe.leaf = leaf;
                for (const ColumnRef &bound : group.bound_columns) {
                    ColumnRef target_ref;
                    if (!target_equivalent_column(leaf, bound, &target_ref)) {
                        transparent = false;
                        break;
                    }
                    probe.target_columns.push_back(target_ref);
                }
                if (transparent)
                    root_terminal_probes_.push_back(std::move(probe));
            }
        }
    }

    static bool terminal_group_truth_for_key(const TerminalVerdictGroup &group,
            const FusedMemoKey &key,std::uint64_t *truth) {
        const auto found=group.truth.find(key);
        if (found==group.truth.end()) return false;
        *truth=found->second;return true;
    }

    bool terminal_group_lookup(TerminalVerdictGroup &group,std::uint64_t *truth) {
        return (this->*group.lookup)(group,truth);
    }
    template<int Mode> bool terminal_group_lookup_mode(TerminalVerdictGroup &group,std::uint64_t *truth) {
        FusedMemoKey key;key.width=group.bound_columns.size();
        for (std::size_t i=0;i<group.bound_columns.size();++i) {
            const auto &ref=group.bound_columns[i];const auto bound=bindings_[ref.node_id];
            if (bound<0) return false;
            key.ranks[i]=row_universe_rank(ref,bound);
            // An equality operand cannot have a witness when it is NULL.
            if (i<group.child_columns.size() && key.ranks[i]==kNullRank) {*truth=0;return true;}
        }
        bool cache=true;
        if constexpr(Mode==0)cache=false;
        else if constexpr(Mode==2)cache=rank_store_.enabled(group.gate_id);
        if constexpr(Mode!=0)if(cache) {
            CF_COUNT(++group.probes);
            const bool hit=terminal_group_truth_for_key(group,key,truth);
            if constexpr(Mode==2)rank_observe_range(group.node,group.gate_id,hit,hit && *truth ? 1U : 0U);
            if(hit){CF_COUNT(++group.hits);return true;}
        }
        std::size_t primary=0;
        for (std::size_t i=1;i<group.child_columns.size();++i) {
            auto &candidate=column(group.child_columns[i]);auto &current=column(group.child_columns[primary]);
            if (candidate.cix.end(key.ranks[i])-candidate.cix.begin(key.ranks[i]) <
                current.cix.end(key.ranks[primary])-current.cix.begin(key.ranks[primary])) primary=i;
        }
        auto &driver=column(group.child_columns[primary]);
        const auto begin=driver.cix.begin(key.ranks[primary]),end=driver.cix.end(key.ranks[primary]);
        const auto leaf=static_cast<std::size_t>(__builtin_ctzll(group.leaves));
        const auto &node=dag_[group.node];
        const auto occurrence=node.occurrence_by_leaf[leaf];
        const auto old_binding=bindings_[occurrence];
        std::uint64_t learned=0;
        for (auto cursor=begin;cursor<end;++cursor) {
            if ((cursor&4095U)==0U) CHECK_FOR_INTERRUPTS();
            const auto row=u32le(driver.cix.child_rows+cursor*4ULL);
            ++partner_touches_;CF_COUNT(++node_partner_touches_[group.node]);
            CF_COUNT(++group.scan_reads);
            bool same=true;
            for (std::size_t i=0;i<group.child_columns.size();++i)
                if (row_universe_rank(group.child_columns[i],row)!=key.ranks[i]) {same=false;break;}
            if (!same) continue;
            bindings_[occurrence]=row;
            bool good=true;
            for (auto atom:node.filters_by_leaf[leaf]) if (!atom_holds(*atom)) {good=false;break;}
            if (good) {learned=group.leaves;break;}
        }
        bindings_[occurrence]=old_binding;
        // A complete posting scan proves nogood; a joint witness proves good.
        if constexpr(Mode!=0)if(cache){group.truth.emplace(key,learned);CF_COUNT(++group.writes);}
        *truth=learned;return true;
    }

    void apply_terminal_groups(std::size_t node,
                               std::uint64_t requested,
                               std::uint64_t *result,
                               std::uint64_t *remaining,
                               std::uint64_t settle_on_success) {
        for (std::size_t group_index : terminal_groups_by_node_[node]) {
            TerminalVerdictGroup &group = terminal_groups_[group_index];
            const std::uint64_t active = requested & group.leaves & *remaining;
            if (active == 0U) continue;
            std::uint64_t learned = 0;
            if (!terminal_group_lookup(group, &learned)) continue;
            CF_COUNT(++node_terminal_hits_[node]);
            const std::uint64_t true_bits = active & learned;
            *result |= true_bits;
            *remaining &= ~active;
            const std::uint64_t completed = true_bits & settle_on_success;
            if (completed != 0U) settle(completed, completed);
            if (aborted_) return;
        }
    }

    void apply_root_terminal_frontier(std::uint64_t candidates) {
        for (const RootTerminalProbe &probe : root_terminal_probes_) {
            const std::uint64_t bit = std::uint64_t{1} << probe.leaf;
            if ((candidates & bit & ~settled_) == 0U) continue;
            TerminalVerdictGroup &group = terminal_groups_[probe.group];
            FusedMemoKey key;
            key.width = static_cast<std::uint8_t>(probe.target_columns.size());
            bool valid = true;
            for (std::size_t i = 0; i < probe.target_columns.size(); ++i) {
                const std::uint32_t rank = row_universe_rank(
                    probe.target_columns[i],
                    static_cast<std::uint32_t>(bindings_[target_node_]));
                if (rank == kNullRank) { valid = false; break; }
                key.ranks[i] = rank;
            }
            if (!valid) {
                settle(bit, 0U);
                if (aborted_) return;
                continue;
            }
            std::uint64_t learned=0;
            if (!terminal_group_truth_for_key(group,key,&learned)) continue;
            settle(bit, learned & bit);
            CF_COUNT(++root_terminal_hits_);
            if (aborted_) return;
        }
    }

    bool make_memo_key(std::size_t node, std::size_t leaf, FusedMemoKey *key) {
        const std::vector<ColumnRef> &dependencies = dependencies_[node][leaf];
        if (dependencies.size() > key->ranks.size()) return false;
        key->width = static_cast<std::uint8_t>(dependencies.size());
        for (std::size_t i = 0; i < dependencies.size(); ++i) {
            const ColumnRef &ref = dependencies[i];
            const std::int64_t row = bindings_[ref.node_id];
            if (row < 0) return false;
            const std::uint32_t rank =
                row_universe_rank(ref, static_cast<std::uint32_t>(row));
            if (rank == kNullRank) return false;
            key->ranks[i] = rank;
        }
        return true;
    }

    bool memo_lookup(FusedMemoStore &store,
                     const FusedMemoKey &key,
                     bool *truth) {
        if (!store.enabled) return false;
        ++store.probes;
        FusedMemoEntry *entry = nullptr;
        std::uint64_t packed = 0;
        if (pack_memo_key(key, &packed)) {
            entry = store.packed_entries.find(packed);
        } else {
            const auto found = store.wide_entries.find(key);
            if (found != store.wide_entries.end()) entry = &found->second;
        }
        if (entry != nullptr) {
            ++store.hits;
            store.recurrence_observed = true;
            *truth = entry->truth;
        }
        if (store.probationary && store.probes >= kProbation) {
            store.probationary = false;
            if (!store.recurrence_observed) {
                store.enabled = false;
                store.packed_entries.clear_release();
                store.wide_entries.clear();
                store.wide_entries.rehash(0);
            }
        }
        return entry != nullptr;
    }

    static void memo_insert(FusedMemoStore &store,
                            const FusedMemoKey &key,
                            bool truth,
                            std::uint64_t touches) {
        if (!store.enabled) return;
        const std::uint32_t cost = static_cast<std::uint32_t>(
            std::min<std::uint64_t>(touches, std::numeric_limits<std::uint32_t>::max()));
        FusedMemoEntry *entry = nullptr;
        bool inserted = false;
        std::uint64_t packed = 0;
        if (pack_memo_key(key, &packed)) {
            std::tie(entry, inserted) = store.packed_entries.insert(
                packed, FusedMemoEntry{truth, cost});
        } else {
            auto result = store.wide_entries.emplace(
                key, FusedMemoEntry{truth, cost});
            entry = &result.first->second;
            inserted = result.second;
        }
        if (!inserted) {
            if (entry->truth != truth)
                fail("our_pg fused memo attempted to flip a verdict");
            entry->touch_cost = std::max(entry->touch_cost, cost);
        }
    }

    bool boolean_group_holds(const LocalBooleanGroup &group) {
        std::array<bool, 64> stack{};
        std::size_t size = 0;
        for (const LocalBooleanToken &token : group.postfix) {
            if (token.kind == LocalBooleanTokenKind::atom) {
                if (size >= stack.size())
                    fail("our_pg Boolean group stack overflow");
                stack[size++] = atom_holds(*token.atom);
                continue;
            }
            if (size < 2U) fail("invalid our_pg Boolean group postfix");
            const bool right = stack[--size];
            const bool left = stack[--size];
            stack[size++] = token.kind ==
                LocalBooleanTokenKind::conjunction ?
                left && right : left || right;
        }
        if (size != 1U) fail("invalid our_pg Boolean group result");
        return stack[0];
    }

    std::uint64_t evaluate_filters(std::size_t node, std::uint64_t requested) {
        std::uint64_t passing = requested;
        for (const FusedDagNode::CompiledFilter &filter :
             dag_[node].compiled_filters) {
            const std::uint64_t affected = passing & filter.leaves;
            if (affected != 0U && !atom_holds(*filter.atom))
                passing &= ~affected;
        }
        for (const FusedDagNode::CompiledBooleanGroup &compiled :
             dag_[node].compiled_boolean_groups) {
            const std::uint64_t affected = passing & compiled.leaves;
            if (affected != 0U && !boolean_group_holds(*compiled.group))
                passing &= ~affected;
        }
        return passing;
    }

    std::uint64_t evaluate_filters_with_rank_proof(
            std::size_t node, std::uint64_t requested,
            RankProofCell *proof) {
        if (proof == nullptr) return evaluate_filters(node, requested);
        std::uint64_t passing = requested;
        const std::uint64_t stable = local_stable_proof_masks_[node];
        for (const FusedDagNode::CompiledFilter &filter :
             dag_[node].compiled_filters) {
            const std::uint64_t affected = passing & filter.leaves;
            if (affected == 0U) continue;
            const std::uint64_t atom_bit = filter.atom->proof_bit;
            bool holds = false;
            if ((stable & atom_bit) != 0U &&
                (proof->decided & atom_bit) != 0U) {
                holds = (proof->truth & atom_bit) != 0U;
                CF_COUNT(++rank_proof_atom_hits_);
            } else {
                holds = atom_holds(*filter.atom);
                if ((stable & atom_bit) != 0U) {
                    proof->decided |= atom_bit;
                    if (holds) proof->truth |= atom_bit;
                    else proof->truth &= ~atom_bit;
                    CF_COUNT(++rank_proof_atom_strengthens_);
                }
            }
            if (!holds) passing &= ~affected;
        }
        for (const FusedDagNode::CompiledBooleanGroup &compiled :
             dag_[node].compiled_boolean_groups) {
            const std::uint64_t affected = passing & compiled.leaves;
            if (affected == 0U) continue;
            const std::uint64_t group_bit = compiled.group->proof_bit;
            bool holds = false;
            if ((stable & group_bit) != 0U &&
                (proof->decided & group_bit) != 0U) {
                holds = (proof->truth & group_bit) != 0U;
                CF_COUNT(++rank_proof_atom_hits_);
            } else {
                holds = boolean_group_holds(*compiled.group);
                if ((stable & group_bit) != 0U) {
                    proof->decided |= group_bit;
                    if (holds) proof->truth |= group_bit;
                    else proof->truth &= ~group_bit;
                    CF_COUNT(++rank_proof_atom_strengthens_);
                }
            }
            if (!holds) passing &= ~affected;
        }
        return passing;
    }

    static bool same_lookup(const LookupResult &left,
                            const LookupResult &right) {
        if (left.count != right.count) return false;
        for (int i = 0; i < left.count; ++i)
            if (left.ranges[i] != right.ranges[i]) return false;
        return true;
    }

    std::uint64_t posting_rows(const ColumnIndex &column,
                               const LookupResult &lookup) const {
        std::uint64_t rows = 0;
        for (int i = 0; i < lookup.count; ++i) {
            const std::uint32_t begin = column.cix.logical_offset(lookup.ranges[i].first);
            const std::uint32_t end = column.cix.logical_offset(lookup.ranges[i].second);
            rows += end - begin;
        }
        return rows;
    }

    std::uint64_t estimate_partner_rows(std::size_t node_index,
                                        std::uint64_t requested) {
        const FusedDagNode &node = dag_[node_index];
        requested &= node.leaves;
        if (requested == 0U) return 0U;
        const std::size_t representative = static_cast<std::size_t>(
            __builtin_ctzll(requested));
        const NormalizedAtom &edge = *node.edge_by_leaf[representative];
        const bool candidate_left =
            node.candidate_is_left_by_leaf[representative];
        const ColumnRef &candidate = candidate_left ? edge.left : edge.right;
        return posting_rows(column(candidate), edge_lookup(edge, candidate_left));
    }

    bool frontier_gate_enabled(std::size_t node,
                               std::size_t pending_count) const {
        return pending_count > 1U && !frontier_gates_[node].disabled;
    }

    void observe_frontier_choice(std::size_t node, bool switched) {
        FrontierGate &gate = frontier_gates_[node];
        if (gate.disabled) {
            CF_COUNT(++frontier_gated_choices_);
            return;
        }
        if (gate.probes != std::numeric_limits<std::uint32_t>::max())
            ++gate.probes;
        if (switched && gate.switches != std::numeric_limits<std::uint32_t>::max())
            ++gate.switches;
        if (gate.probes >= kFrontierProbation && gate.switches == 0U) {
            gate.disabled = true;
            CF_COUNT(++frontier_gates_disabled_);
        }
    }

    LookupResult literal_lookup(ColumnIndex &candidate,
                                int op,
                                const std::string &literal) {
        const auto universe_bounds = literal_bounds(candidate.domain, literal);
        const std::uint32_t lower=universe_bounds.first,upper=universe_bounds.second;
        const std::uint32_t count=candidate.cix.rank_count;
        LookupResult result;
        switch (op) {
            case POLICY_OP_EQ:
                if (lower < upper) {
                    result.ranges[0] = {lower, upper};
                    result.count = 1;
                }
                break;
            case POLICY_OP_LT:
                result.ranges[0] = {0U, lower}; result.count = 1; break;
            case POLICY_OP_LE:
                result.ranges[0] = {0U, upper}; result.count = 1; break;
            case POLICY_OP_GT:
                result.ranges[0] = {upper, count}; result.count = 1; break;
            case POLICY_OP_GE:
                result.ranges[0] = {lower, count}; result.count = 1; break;
            case POLICY_OP_NE:
                result.ranges[0] = {0U, lower};
                result.ranges[1] = {upper, count};
                result.count = 2;
                break;
            default:
                fail("invalid target-driver operator");
        }
        return result;
    }

    LookupResult constant_lookup(const NormalizedAtom &atom,
                                 ColumnIndex &candidate) {
        if (!atom.right_is_const)
            fail("target driver requires a constant atom");
        return literal_lookup(candidate, atom.op, atom.literal);
    }

    #include "chain_projection.inc"
    #include "full_reuse.inc"
    #include "tight_policy_loop.inc"
    #include "grouped_plan.h"
    #define MEMENTO_DECLARE_COLD
    #define MEMENTO_METHOD(name) name
    #include "grouped_target_loop.inc"
    #include "mixed_requests.inc"
    #include "exclusive_rank_loop.inc"
    #include "node_dispatch.inc"
    #include "grouped_compiler.inc"
    #undef MEMENTO_METHOD
    #undef MEMENTO_DECLARE_COLD
    #include "walk_plan_dump.inc"

    void configure_composite_connections() {
        if (planned_arrivals_.size() != dag_.size())
            fail("composite connection requires compiled arrival estimates");
        const auto started = std::chrono::steady_clock::now();
        composite_indexes_.resize(dag_.size());
                std::size_t connections = 0;
        for (std::size_t node = 1; cf_composite_edges && node < dag_.size(); ++node) {
            const auto leaf = __builtin_ctzll(dag_[node].leaves);
            const auto &atoms = dag_[node].equalities_by_leaf[leaf];
            if (atoms.size() <= 1U) continue;
            if (cf_composite_cost && !composite_postings_pay(node, leaf)) {
                ++composite_connections_rejected_;
                continue;
            }
            if (atoms.size() > 16U) fail("composite connection exceeds 16 rank columns");
            const auto occurrence = dag_[node].occurrence_by_leaf[leaf];
            std::vector<ColumnRef> refs;
            for (const auto *atom : atoms) {
                const auto &ref = atom->left.node_id == occurrence ? atom->left : atom->right;
                const auto &bound = atom->left.node_id == occurrence ? atom->right : atom->left;
                if (column(ref).domain != column(bound).domain)
                    fail("composite edge crosses canonical universes");
                refs.push_back(ref);
            }
            std::sort(refs.begin(),refs.end(),[](const ColumnRef &a,const ColumnRef &b){return a.column<b.column;});
            refs.erase(std::unique(refs.begin(),refs.end(),[](const ColumnRef &a,const ColumnRef &b){return a.column==b.column;}),refs.end());
            if (refs.size()<2U) continue;
            auto index=std::make_shared<CompositeConnection>();index->columns=refs;
            double shortest=std::numeric_limits<double>::max();
            for(std::size_t i=0;i<refs.size();++i) {
                const auto &h=column(refs[i]).cix;
                const auto expected=double(h.row_count)/std::max(1U,h.present_count);
                if(expected<shortest){shortest=expected;index->driver=i;}
            }
            const auto groups=std::max(1U,column(refs[index->driver]).cix.present_count);
            index->groups_enabled=cf_cost_group_maps && shortest>16.0 && planned_arrivals_[node]/groups>1.0;
            composite_indexes_[node] = index;
            ++connections;
        }
        cf_perf_metric_set("composite_connections", connections);
        cf_perf_metric_set("composite_connections_rejected", composite_connections_rejected_);
        composite_build_ms_ = elapsed_ms(started, std::chrono::steady_clock::now());
        cf_perf_metric_set("composite_build_ms", composite_build_ms_);
    }

    tuple_index::Rows composite_rows(std::size_t node,std::size_t leaf) {
        const auto &atoms=dag_[node].equalities_by_leaf[leaf];
        const auto occurrence=dag_[node].occurrence_by_leaf[leaf];
        auto &index=*composite_indexes_[node];
        std::array<std::uint32_t,16> key{};
        index.rows.clear();
        for (std::size_t i=0;i<index.columns.size();++i) {
            bool found=false;
            for (auto atom:atoms) {
                const auto &candidate=atom->left.node_id==occurrence ? atom->left : atom->right;
                if (candidate.key()!=index.columns[i].key()) continue;
                const auto &bound=atom->left.node_id==occurrence ? atom->right : atom->left;
                if (bindings_[bound.node_id]<0) fail("unbound composite entering operand");
                key[i]=row_universe_rank(bound,bindings_[bound.node_id]);found=true;break;
            }
            if (!found) fail("composite edge column mismatch");
        }
        CF_COUNT(++composite_lookups_);
        if(index.groups_enabled) {
            for(std::size_t i=0;i<index.columns.size();++i)if(key[i]==kNullRank)return {};
            const auto rank=key[index.driver];
            auto found=index.groups.find(rank);
            if(found==index.groups.end()) {
                auto &driver=column(index.columns[index.driver]);
                const auto begin=driver.cix.begin(rank),end=driver.cix.end(rank);
                const auto bytes=std::size_t(end-begin)*sizeof(LazyGroupMap::Entry)+128U;
                if(reserve_dense_cache(bytes)) {
                    if(!target_walk_started_)fail("composite group built before first target row");
                    auto &group=index.groups.try_emplace(rank).first->second;
                    group.build(begin,end,[&](std::uint32_t cursor) {
                        if((cursor&4095U)==0U)CHECK_FOR_INTERRUPTS();
                        LazyGroupMap::Entry entry;entry.row=u32le(driver.cix.child_rows+cursor*4ULL);
                        ++partner_touches_;
                        for(std::size_t i=0;i<index.columns.size();++i)
                            entry.key[i]=i==index.driver ? rank : row_universe_rank(index.columns[i],entry.row);
                        return entry;
                    });
                    found=index.groups.find(rank);
                }
            }
            if(found!=index.groups.end()) {
                found->second.lookup(key,index.rows);
                return {reinterpret_cast<const unsigned char *>(index.rows.data()),
                        static_cast<std::uint32_t>(index.rows.size())};
            }
        }
        unary_tuple_rows(index.columns,key.data(),index.rows,UINT32_MAX);
        return {reinterpret_cast<const unsigned char *>(index.rows.data()),
                static_cast<std::uint32_t>(index.rows.size())};
    }

    // Rows whose columns hold exactly the given universe ranks, from unary indexes only: scan the shortest inverted
    // posting among the columns (its length is one offset subtraction) and check the others by forward rank. A NULL
    // rank has no match. Stops after limit rows. Every posting row read is a witness touch.
    std::uint32_t unary_tuple_rows(const std::vector<ColumnRef> &columns,const std::uint32_t *ranks,
                                   std::vector<std::uint32_t> &out,std::uint32_t limit) {
        out.clear();
        for (std::size_t i=0;i<columns.size();++i) if (ranks[i]==kNullRank) return 0U;
        std::size_t primary=0;
        for (std::size_t i=1;i<columns.size();++i) {
            auto &candidate=column(columns[i]);auto &current=column(columns[primary]);
            if (candidate.cix.end(ranks[i])-candidate.cix.begin(ranks[i]) <
                current.cix.end(ranks[primary])-current.cix.begin(ranks[primary])) primary=i;
        }
        auto &driver=column(columns[primary]);
        const auto begin=driver.cix.begin(ranks[primary]),end=driver.cix.end(ranks[primary]);
        for (auto cursor=begin;cursor<end && out.size()<limit;++cursor) {
            if ((cursor&4095U)==0U) CHECK_FOR_INTERRUPTS();
            const auto row=u32le(driver.cix.child_rows+cursor*4ULL);
            ++partner_touches_;
            bool same=true;
            for (std::size_t i=0;i<columns.size() && same;++i)
                if (i!=primary && row_universe_rank(columns[i],row)!=ranks[i]) same=false;
            if (same) out.push_back(row);
        }
        return static_cast<std::uint32_t>(out.size());
    }


    struct IntervalPlan {
        bool enabled=false;
        const NormalizedAtom *start_atom=nullptr,*end_atom=nullptr;
        ColumnRef start,end,time;
        bool start_closed=true,end_closed=true;
        std::vector<ColumnRef> context;
        std::unordered_map<FusedMemoKey,OnlineIntervalCoverage,FusedMemoKeyHash> cache;
        using Evaluate=bool(FusedWalkRuntime::*)(std::size_t,std::size_t,bool *);
        Evaluate evaluate=nullptr;
    };

    void configure_interval_connections() {
        interval_plans_.resize(dag_.size());
        cf_perf_metric_set("interval_build_ms", 0);
        if(composed_bound_program_)return; // replaced by complete-subwalk windows
        if (!cf_interval_edges) return;
        for (std::size_t node = 1; node < dag_.size(); ++node) {
            for (auto bits = dag_[node].leaves; bits; bits &= bits - 1U) {
                const auto leaf = __builtin_ctzll(bits);
                auto &plan = interval_plans_[node][leaf];
                const auto occurrence = dag_[node].occurrence_by_leaf[leaf];
                const auto &edge = *dag_[node].edge_by_leaf[leaf];
                if (edge.op != POLICY_OP_EQ) continue;
                for (const auto *atom : dag_[node].filters_by_leaf[leaf]) {
                    if (atom->right_is_const) continue;
                    const bool left = atom->left.node_id == occurrence;
                    if (left == (atom->right.node_id == occurrence)) continue;
                    const auto &candidate = left ? atom->left : atom->right;
                    const auto &bound = left ? atom->right : atom->left;
                    const auto op = left ? atom->op : invert_op(atom->op);
                    if (op != POLICY_OP_LT && op != POLICY_OP_LE &&
                        op != POLICY_OP_GT && op != POLICY_OP_GE) continue;
                    if ((plan.start_atom || plan.end_atom) &&
                        (bound.node_id != plan.time.node_id || bound.runtime_column != plan.time.runtime_column)) continue;
                    plan.time = bound;
                    if ((op == POLICY_OP_LT || op == POLICY_OP_LE) && !plan.start_atom) {
                        plan.start_atom = atom; plan.start = candidate;
                        plan.start_closed = op == POLICY_OP_LE;
                    } else if ((op == POLICY_OP_GT || op == POLICY_OP_GE) && !plan.end_atom) {
                        plan.end_atom = atom; plan.end = candidate;
                        plan.end_closed = op == POLICY_OP_GE;
                    }
                }
                if (!plan.start_atom && !plan.end_atom) continue;
                if ((plan.start_atom && column(plan.start).domain != column(plan.time).domain) ||
                    (plan.end_atom && column(plan.end).domain != column(plan.time).domain)) continue;
                std::set<int> subtree;
                collect_subtree_occurrences(node, leaf, &subtree);
                bool safe = true;
                // Removing the probe time must leave a complete, time-independent tail.
                const auto check = [&](const NormalizedAtom *atom) {
                    if (atom == plan.start_atom || atom == plan.end_atom) return;
                    if (subtree.count(atom->left.node_id) == 0 &&
                        (atom->right_is_const || subtree.count(atom->right.node_id) == 0)) return;
                    for (const auto *ref : {&atom->left, atom->right_is_const ? nullptr : &atom->right})
                        if (ref && ref->node_id == plan.time.node_id && ref->runtime_column == plan.time.runtime_column)
                            safe = false;
                };
                for (auto atom : leaves_[leaf]->atoms) check(atom);
                for (const auto &group : leaves_[leaf]->boolean_groups)
                    for (auto atom : group.atoms) check(atom);
                for (const auto &ref : dependencies_[node][leaf])
                    if (ref.node_id != plan.time.node_id || ref.runtime_column != plan.time.runtime_column)
                        plan.context.push_back(ref);
                plan.enabled = safe && plan.context.size() <= 16U;
                if(plan.enabled)plan.evaluate=cf_cost_single_visit &&
                    decision_repeat_ratio(planned_arrivals_[node],plan.context)<=1.0 ?
                    &FusedWalkRuntime::interval_truth_mode<false> : &FusedWalkRuntime::interval_truth_mode<true>;
            }
        }
    }

    bool interval_truth(std::size_t node, std::size_t leaf, bool *truth) {
        auto &plan = interval_plans_[node][leaf];
        if (!plan.enabled) return false;
        return (this->*plan.evaluate)(node,leaf,truth);
    }
    template<bool Cache> bool interval_truth_mode(std::size_t node,std::size_t leaf,bool *truth) {
        auto &plan=interval_plans_[node][leaf];
        if (bindings_[plan.time.node_id] < 0) fail("unbound interval probe time");
        const auto time = row_universe_rank(plan.time, bindings_[plan.time.node_id]);
        if (time == kNullRank) { *truth = false; return true; }
        FusedMemoKey key{}; key.width = plan.context.size();
        for (std::size_t i = 0; i < plan.context.size(); ++i) {
            const auto &ref = plan.context[i];
            if (bindings_[ref.node_id] < 0) return false;
            key.ranks[i] = row_universe_rank(ref, bindings_[ref.node_id]);
        }
        CF_COUNT(++interval_lookups_);
        auto found = plan.cache.end();
        if constexpr(Cache)found=plan.cache.find(key);
        OnlineIntervalCoverage fresh;
        if (found == plan.cache.end()) {
            const auto started = std::chrono::steady_clock::now();
            const double lookup_before = decision_lookup_ms_;
            OnlineIntervalCoverage coverage;
            const auto &edge = *dag_[node].edge_by_leaf[leaf];
            const auto left = dag_[node].candidate_is_left_by_leaf[leaf];
            const auto &candidate = left ? edge.left : edge.right;
            auto &index = column(candidate);
            const auto lookup = edge_lookup(edge, left);
            const bool tuple_used=bool(composite_indexes_[node]);
            const auto tuple=tuple_used ? composite_rows(node,leaf) : tuple_index::Rows{};
            const auto visit = [&](std::uint32_t row) {
                ++online_build_tuples_;
                for (int occurrence : dag_[node].bound_occurrences) bindings_[occurrence] = row;
                bool passing = true;
                for (auto atom : dag_[node].filters_by_leaf[leaf]) {
                    if (atom == plan.start_atom || atom == plan.end_atom) continue;
                    if (bindings_[atom->left.node_id] < 0 ||
                        (!atom->right_is_const && bindings_[atom->right.node_id] < 0))
                        fail("interval build encountered an unbound predicate");
                    if (!atom_holds(*atom)) { passing = false; break; }
                }
                if (passing) for (auto group : dag_[node].boolean_groups_by_leaf[leaf])
                    if (!boolean_group_holds(*group)) { passing = false; break; }
                const auto start = plan.start_atom ? row_universe_rank(plan.start, row) : 0U;
                const auto end = plan.end_atom ? row_universe_rank(plan.end, row) : kNullRank - 1U;
                if (passing && start != kNullRank && end != kNullRank &&
                    (rank_solve_children(node, std::uint64_t{1} << leaf, nullptr) & (std::uint64_t{1} << leaf)))
                    coverage.add({start, end, plan.start_closed, plan.end_closed});
                for (int occurrence : dag_[node].bound_occurrences) bindings_[occurrence] = -1;
            };
            if (tuple_used) for (std::size_t i=0;i<tuple.size();++i) visit(tuple[i]);
            else for (int interval = 0; interval < lookup.count; ++interval)
                for (auto rank = lookup.ranges[interval].first; rank < lookup.ranges[interval].second; ++rank)
                    for (auto cursor = index.cix.begin(rank); cursor < index.cix.end(rank); ++cursor) {
                        if ((cursor & 4095U) == 0U) CHECK_FOR_INTERRUPTS();
                        visit(u32le(index.cix.child_rows + cursor * 4ULL));
                    }
            coverage.finish();
            if constexpr(Cache)found=plan.cache.emplace(key,std::move(coverage)).first;
            else fresh=std::move(coverage);
            interval_build_ms_ += elapsed_ms(started, std::chrono::steady_clock::now());
            decision_lookup_ms_ = lookup_before; // Child probes belong to this build phase.
            cf_perf_metric_set("interval_build_ms", interval_build_ms_);
        }
        if constexpr(Cache)*truth=found->second.covers(time);
        else *truth=fresh.covers(time);
        return true;
    }



    bool equality_driver_for_leaf(std::size_t node_index,
                                  std::size_t leaf,
                                  std::size_t candidate_column,
                                  LookupResult *lookup) {
        const FusedDagNode &node = dag_[node_index];
        const int occurrence = node.occurrence_by_leaf[leaf];
        if (occurrence < 0) return false;
        for (const NormalizedAtom *atom : node.filters_by_leaf[leaf]) {
            if (atom->right_is_const || atom->op != POLICY_OP_EQ) continue;
            bool candidate_left = false;
            if (atom->left.node_id == occurrence &&
                bindings_[atom->right.node_id] >= 0) {
                candidate_left = true;
            } else if (atom->right.node_id == occurrence &&
                       bindings_[atom->left.node_id] >= 0) {
                candidate_left = false;
            } else {
                continue;
            }
            const ColumnRef &candidate = candidate_left ? atom->left : atom->right;
            if (candidate.runtime_column != candidate_column) continue;
            *lookup = edge_lookup(*atom, candidate_left);
            return true;
        }
        return false;
    }

    template <typename Visitor>
    void visit_partners(std::size_t node_index,
                        std::uint64_t requested,
                        Visitor &&visitor) {
        const std::size_t representative =
            static_cast<std::size_t>(__builtin_ctzll(requested));
        const FusedDagNode &node = dag_[node_index];
        const NormalizedAtom &edge = *node.edge_by_leaf[representative];
        const bool candidate_left = node.candidate_is_left_by_leaf[representative];
        const ColumnRef &entering_candidate =
            candidate_left ? edge.left : edge.right;
        const ColumnRef *driver_candidate = &entering_candidate;
        LookupResult lookup = edge_lookup(edge, candidate_left);
        ColumnIndex *candidate_index = &column(entering_candidate);

        BoundPairCache &pair_cache = bound_pair_caches_[node_index];
        if (pair_cache.eligible && lookup.count == 1 &&
            lookup.ranges[0].second == lookup.ranges[0].first + 1U) {
            const std::uint32_t primary_rank = lookup.ranges[0].first;
            const std::int64_t secondary_bound_row =
                bindings_[pair_cache.secondary_bound_column.node_id];
            const std::uint32_t secondary_universe_rank =
                secondary_bound_row < 0 ? kNullRank : row_universe_rank(
                    pair_cache.secondary_bound_column,
                    static_cast<std::uint32_t>(secondary_bound_row));
            if (primary_rank < pair_cache.primary_count &&
                secondary_universe_rank != kNullRank) {
                const std::size_t slot_begin =
                    static_cast<std::size_t>(primary_rank) * pair_cache.ways;
                if (pair_cache.ready[primary_rank] == 0U) {
                    const std::uint32_t begin = candidate_index->cix.begin(primary_rank);
                    const std::uint32_t end = candidate_index->cix.end(primary_rank);
                    std::size_t inserted = 0;
                    for (std::uint32_t cursor = begin;
                         cursor < end; ++cursor) {
                        const std::uint32_t row = u32le(
                            candidate_index->cix.child_rows +
                            static_cast<std::size_t>(cursor) * 4U);
                        ++partner_touches_;
                        CF_COUNT(++node_partner_touches_[node_index]);
                        ++bound_pair_build_rows_;
                        const std::uint32_t row_secondary =
                            row_universe_rank(
                                pair_cache.secondary_child_column, row);
                        if (row_secondary == kNullRank) continue;
                        bool duplicate = false;
                        for (std::size_t way = 0; way < inserted; ++way) {
                            if (pair_cache.slots[slot_begin + way].
                                    secondary_universe_rank == row_secondary) {
                                duplicate = true;
                                break;
                            }
                        }
                        if (duplicate || inserted >= pair_cache.ways) {
                            pair_cache.ambiguous[primary_rank] = 1U;
                            break;
                        }
                        pair_cache.slots[slot_begin + inserted] =
                            BoundPairSlot{row_secondary, row};
                        ++inserted;
                    }
                    pair_cache.ready[primary_rank] = 1U;
                    CF_COUNT(++bound_pair_builds_);
                }
                if (pair_cache.ambiguous[primary_rank] == 0U) {
                    for (std::size_t way = 0;
                         way < pair_cache.ways; ++way) {
                        const BoundPairSlot &slot =
                            pair_cache.slots[slot_begin + way];
                        if (slot.secondary_universe_rank == UINT32_MAX) break;
                        if (slot.secondary_universe_rank !=
                            secondary_universe_rank) continue;
                        CF_COUNT(++bound_pair_hits_);
                        ++partner_touches_;
                        CF_COUNT(++node_partner_touches_[node_index]);
                        for (int bound_occurrence : node.bound_occurrences)
                            bindings_[bound_occurrence] = slot.row;
                        (void)visitor(requested);
                        for (int bound_occurrence : node.bound_occurrences)
                            bindings_[bound_occurrence] = -1;
                        return;
                    }
                    CF_COUNT(++bound_pair_misses_);
                    return;
                }
                CF_COUNT(++bound_pair_fallbacks_);
            }
        }
        std::uint64_t best_rows = posting_rows(*candidate_index, lookup);
        bool switched_driver = false;

        
        
        
        
        
        const int occurrence = node.occurrence_by_leaf[representative];
        for (const NormalizedAtom *atom : node.filters_by_leaf[representative]) {
            if (atom->right_is_const || atom->op != POLICY_OP_EQ) continue;
            bool atom_candidate_left = false;
            if (atom->left.node_id == occurrence &&
                bindings_[atom->right.node_id] >= 0) {
                atom_candidate_left = true;
            } else if (atom->right.node_id == occurrence &&
                       bindings_[atom->left.node_id] >= 0) {
                atom_candidate_left = false;
            } else {
                continue;
            }
            const ColumnRef &alternative =
                atom_candidate_left ? atom->left : atom->right;
            const LookupResult alternative_lookup =
                edge_lookup(*atom, atom_candidate_left);
            bool common = true;
            for (std::uint64_t bits = requested; bits != 0; bits &= bits - 1U) {
                const std::size_t leaf =
                    static_cast<std::size_t>(__builtin_ctzll(bits));
                LookupResult leaf_lookup;
                if (!equality_driver_for_leaf(
                        node_index, leaf, alternative.runtime_column, &leaf_lookup) ||
                    !same_lookup(alternative_lookup, leaf_lookup)) {
                    common = false;
                    break;
                }
            }
            if (!common) continue;
            ColumnIndex &alternative_index = column(alternative);
            const std::uint64_t rows =
                posting_rows(alternative_index, alternative_lookup);
            if (rows < best_rows) {
                best_rows = rows;
                lookup = alternative_lookup;
                candidate_index = &alternative_index;
                driver_candidate = &alternative;
                switched_driver = true;
            }
        }
        (void)driver_candidate;
        bool stop = false;
        for (int interval = 0; interval < lookup.count && !stop; ++interval) {
                // Offsets delimit the whole ordered range, including its empty ranks.
                const std::uint32_t begin = candidate_index->cix.begin(lookup.ranges[interval].first);
                const std::uint32_t end = candidate_index->cix.begin(lookup.ranges[interval].second);
                for (std::uint32_t p = begin; p < end; ++p) {
                    const std::uint32_t row = u32le(
                        candidate_index->cix.child_rows + static_cast<std::size_t>(p) * 4U);
                    ++partner_touches_;
                    CF_COUNT(++node_partner_touches_[node_index]);
                    for (int bound_occurrence : node.bound_occurrences)
                        bindings_[bound_occurrence] = row;
                    std::uint64_t connected = requested;
                    if (switched_driver) {
                        connected = 0;
                        for (std::uint64_t bits = requested;
                             bits != 0; bits &= bits - 1U) {
                            const std::size_t leaf = static_cast<std::size_t>(
                                __builtin_ctzll(bits));
                            const NormalizedAtom *entering =
                                node.edge_by_leaf[leaf];
                            if (entering != nullptr && atom_holds(*entering))
                                connected |= std::uint64_t{1} << leaf;
                        }
                    }
                    if (connected != 0) stop = visitor(connected);
                    for (int bound_occurrence : node.bound_occurrences)
                        bindings_[bound_occurrence] = -1;
                    if (stop) break;
                }
        }
    }

    #include "posting_position.inc"
    #include "composed_bound_walk.inc"

    struct RankPredicatePlan {
        std::uint32_t id = 0;
        std::vector<ColumnRef> filled_columns;
    };

    // Build and intern templates once. Slots are filled with ranks during walking.
    RankPredicatePlan rank_compile_predicate(std::size_t node, std::size_t leaf,
                                             bool whole_tail) {
        std::map<int, unsigned> roles;
        std::vector<std::size_t> nodes;
        const auto collect = [&](auto &&self, std::size_t current) -> void {
            roles.emplace(dag_[current].occurrence_by_leaf[leaf], roles.size());
            nodes.push_back(current);
            if (whole_tail)
                for (std::size_t child : dag_[current].children)
                    if ((dag_[child].leaves & (std::uint64_t{1} << leaf)) != 0U)
                        self(self, child);
        };
        collect(collect, node);
        RankPredicatePlan plan;
        std::map<std::pair<std::string, int>, ColumnRef> external;
        const auto add_operand = [&](const ColumnRef &ref) {
            if (roles.count(ref.node_id) == 0U)
                external.emplace(std::make_pair(ref.key(), ref.node_id), ref);
        };
        const auto add_atom = [&](const NormalizedAtom &atom) {
            add_operand(atom.left);
            if (!atom.right_is_const) add_operand(atom.right);
        };
        for (std::size_t current : nodes) {
            if (current != node) add_atom(*dag_[current].edge_by_leaf[leaf]);
            for (const NormalizedAtom *atom : dag_[current].filters_by_leaf[leaf])
                add_atom(*atom);
            for (const LocalBooleanGroup *group : dag_[current].boolean_groups_by_leaf[leaf])
                for (const NormalizedAtom *atom : group->atoms) add_atom(*atom);
        }
        // The first component is the rank key. All other entering components
        // are packed filled ranks, even if a future planner removes the redundant filters.
        if (composite_indexes_[node]) {
            const auto &edge = *dag_[node].edge_by_leaf[leaf];
            const auto &primary = dag_[node].candidate_is_left_by_leaf[leaf] ? edge.right : edge.left;
            for (auto atom : dag_[node].equalities_by_leaf[leaf]) {
                const auto &bound = atom->left.node_id == dag_[node].occurrence_by_leaf[leaf] ? atom->right : atom->left;
                if (bound.node_id != primary.node_id || bound.runtime_column != primary.runtime_column)
                    add_operand(bound);
            }
        }
        if (external.size() > RankPredicateInstance::max_operands)
            fail("rank predicate exceeds fixed-width filled operand capacity (16)");
        std::map<std::pair<std::string, int>, unsigned> slot;
        for (const auto &item : external) {
            slot.emplace(item.first, plan.filled_columns.size());
            plan.filled_columns.push_back(item.second);
        }
        const auto operand = [&](const ColumnRef &ref) {
            const auto role = roles.find(ref.node_id);
            if (role != roles.end())
                return ref.key() + "#" + std::to_string(role->second);
            return std::string("SLOT[") + column(ref).domain + ":" +
                std::to_string(slot.at(std::make_pair(ref.key(), ref.node_id))) + "]";
        };
        const auto atom_text = [&](const NormalizedAtom &atom) {
            std::string left = operand(atom.left);
            std::string right = atom.right_is_const ?
                "CONST[" + std::to_string(atom.literal.size()) + ":" + atom.literal + "]" :
                operand(atom.right);
            int op = atom.op;
            if (!atom.right_is_const && right < left) {
                std::swap(left, right);
                op = invert_op(op);
            }
            return "(" + left + op_name(op) + right + ")";
        };
        std::vector<std::string> terms;
        for (std::size_t current : nodes) {
            if (current != node)
                terms.push_back(atom_text(*dag_[current].edge_by_leaf[leaf]));
            for (const NormalizedAtom *atom : dag_[current].filters_by_leaf[leaf])
                terms.push_back(atom_text(*atom));
            for (const LocalBooleanGroup *group : dag_[current].boolean_groups_by_leaf[leaf]) {
                std::vector<std::string> stack;
                for (const LocalBooleanToken &token : group->postfix) {
                    if (token.kind == LocalBooleanTokenKind::atom) {
                        stack.push_back(atom_text(*token.atom));
                    } else {
                        std::string right = std::move(stack.back()); stack.pop_back();
                        std::string left = std::move(stack.back()); stack.pop_back();
                        if (right < left) std::swap(left, right);
                        stack.push_back("(" + left +
                            (token.kind == LocalBooleanTokenKind::conjunction ? " AND " : " OR ") +
                            right + ")");
                    }
                }
                terms.push_back(stack.back());
            }
        }
        std::sort(terms.begin(), terms.end());
        terms.erase(std::unique(terms.begin(), terms.end()), terms.end());
        const NormalizedAtom &edge = *dag_[node].edge_by_leaf[leaf];
        const ColumnRef &candidate = dag_[node].candidate_is_left_by_leaf[leaf] ?
            edge.left : edge.right;
        std::string instance = "UNIVERSE[" + column(candidate).domain +
            "] RELATION[" + candidate.key() + "] AND[";
        for (const std::string &term : terms)
            instance += std::to_string(term.size()) + ":" + term;
        instance += ']';
        auto inserted = rank_predicate_ids_.emplace(std::move(instance), 0U);
        if (inserted.second) {
            const std::uint32_t ordinal = rank_predicate_ids_.size();
            if (ordinal >= (1U << RankPredicateInstance::arity_shift))
                fail("rank predicate id capacity exceeded");
            inserted.first->second = ordinal |
                (static_cast<std::uint32_t>(plan.filled_columns.size()) << RankPredicateInstance::arity_shift);
            rank_predicate_text_.push_back(&inserted.first->first);
            rank_gate_columns_.push_back(candidate.key());
        }
        plan.id = inserted.first->second;
        std::vector<ColumnRef> key{candidate};
        key.insert(key.end(),plan.filled_columns.begin(),plan.filled_columns.end());
        double arrivals=planned_arrivals_[node];
        if(fused_node_is_mixed(dag_[node])) {
            // Requests over overlapping ranges are not single visits merely
            // because the pivot is unique. Estimate admitted distinct ranks
            // from headers and each request's operator, never from a policy id.
            double ranks=1.0;
            for(auto bits=dag_[node].leaves;bits;bits&=bits-1U) {
                const auto request=unsigned(__builtin_ctzll(bits));
                const auto op=dag_[node].edge_by_leaf[request]->op;
                const double present=column(candidate).cix.present_count;
                ranks=std::max(ranks,op==POLICY_OP_EQ ? 1.0 : op==POLICY_OP_NE ? std::max(0.0,present-1.0) : present*0.5);
            }
            arrivals=std::min(1e100,arrivals*ranks);
        }
        const double repeats=rank_predicate_repeat_ratio(leaf,arrivals,key);
        if(cf_cost_single_visit && repeats<=1.0) {
            cost_admissions_.push_back({node,leaf,whole_tail,repeats,0U,
                decision_repeat_ratio(arrivals,key),arrivals,key});plan.id=0;return plan;
        }
        cost_admissions_.push_back({node,leaf,whole_tail,repeats,plan.id,
            decision_repeat_ratio(arrivals,key),arrivals,key});
        rank_store_.register_predicate(plan.id,
            domain(column(candidate).domain).count,
            column_distinct_ranks(candidate));
        if((plan.id>>RankPredicateInstance::arity_shift)==0U &&
           !reserve_dense_cache((std::size_t(domain(column(candidate).domain).count)+3U)/4U))
            rank_store_.use_sparse(plan.id);
        if(cf_cost_single_visit && repeats>=4.0)rank_store_.open_without_probation(plan.id);
        return plan;
    }

    void compile_rank_predicates() {
        rank_full_plans_.resize(dag_.size());
        rank_local_plans_.resize(dag_.size());
        rank_full_instances_.resize(dag_.size());
        rank_local_instances_.resize(dag_.size());
        rank_predicate_text_.push_back(nullptr);
        rank_gate_columns_.push_back("");
        for (std::size_t node = 1; node < dag_.size(); ++node) {
            if (rank_single_visit_[node]) continue;
            for (std::uint64_t bits = dag_[node].leaves; bits; bits &= bits - 1U) {
                const std::size_t leaf = __builtin_ctzll(bits);
                rank_full_plans_[node][leaf] = rank_compile_predicate(node, leaf, true);
                rank_local_plans_[node][leaf] = rank_compile_predicate(node, leaf, false);
            }
        }
    }

    RankPredicateInstance rank_fill_predicate(const RankPredicatePlan &plan) {
        RankPredicateInstance instance;
        const bool bound=RankDecisionStore::Key(plan.id,plan.filled_columns.size(),[&](unsigned i,unsigned &rank){
            const ColumnRef &ref = plan.filled_columns[i];
            const std::int64_t row = bindings_[ref.node_id];
            if (row < 0) fail("rank predicate has an unbound external operand " + ref.key());
            rank = row_universe_rank(ref, row);return true;
        },instance);
        if(!bound)fail("rank predicate exceeds parameter capacity");
        return instance;
    }

    bool rank_boolean_holds(const LocalBooleanGroup &group) {
        // Subtree lengths let a short-circuited operand be skipped entirely.
        auto found = rank_boolean_spans_.find(&group);
        if (found == rank_boolean_spans_.end()) {
            std::vector<std::size_t> spans(group.postfix.size(), 1U), stack;
            for (std::size_t i = 0; i < group.postfix.size(); ++i) {
                if (group.postfix[i].kind != LocalBooleanTokenKind::atom) {
                    const std::size_t right = stack.back(); stack.pop_back();
                    const std::size_t left = stack.back(); stack.pop_back();
                    spans[i] += spans[left] + spans[right];
                }
                stack.push_back(i);
            }
            found = rank_boolean_spans_.emplace(&group, std::move(spans)).first;
        }
        const auto eval = [&](auto &&self, std::size_t position) -> bool {
            const LocalBooleanToken &token = group.postfix[position];
            if (token.kind == LocalBooleanTokenKind::atom)
                return atom_holds(*token.atom);
            const std::size_t right = position - 1U;
            const std::size_t left = right - found->second[right];
            const bool lhs = self(self, left);
            if (token.kind == LocalBooleanTokenKind::conjunction)
                return lhs && self(self, right);
            return lhs || self(self, right);
        };
        return eval(eval, group.postfix.size() - 1U);
    }

    bool rank_local_holds(std::size_t node, std::size_t leaf) {
        for (const NormalizedAtom *atom : dag_[node].filters_by_leaf[leaf])
            if (!atom_holds(*atom)) return false;
        for (const LocalBooleanGroup *group : dag_[node].boolean_groups_by_leaf[leaf])
            if (!rank_boolean_holds(*group)) return false;
        return true;
    }

    struct RankEnvelope {
        std::uint32_t smallest_good = UINT32_MAX;
        std::uint32_t largest_good = 0;
        std::uint32_t false_prefix_end = 0;
        std::uint32_t false_suffix_begin = UINT32_MAX;
    };

    bool rank_insert(std::size_t node, std::uint32_t rank,
                     const RankPredicateInstance &instance, bool truth) {
        if (!rank_store_.enabled(instance.id)) return true;
        CF_COUNT(++rank_node_writes_[node]);
        return rank_store_.insert(rank, instance, truth);
    }

    bool rank_lookup(std::size_t node, std::uint32_t rank,
                     const RankPredicateInstance &instance, bool *truth,
                     std::uint64_t nogood_reads = 0U, std::uint64_t good_reads = 1U) {
        const auto before = rank_store_.probes;
        std::chrono::steady_clock::time_point started;
        if (cf_engine_profile) started = std::chrono::steady_clock::now();
        const bool hit = rank_store_.lookup(rank, instance, truth, nogood_reads, good_reads);
        if (cf_engine_profile) decision_lookup_ms_ += elapsed_ms(started, std::chrono::steady_clock::now());
        CF_COUNT(rank_node_probes_[node] += rank_store_.probes - before);
        return hit;
    }

    void rank_observe_range(std::size_t node, std::uint32_t id,
                            bool hit, std::uint64_t saved) {
        const auto before = rank_store_.probes;
        rank_store_.observe_range(id, hit, saved);
        CF_COUNT(rank_node_probes_[node] += rank_store_.probes - before);
    }

    void rank_learn(std::size_t node, std::uint32_t local_rank, const ColumnRef &candidate,
                    const RankPredicateInstance &instance, bool truth,
                    bool track_range = false) {
        if (!rank_store_.enabled(instance.id)) return;
        const auto rank_count = column(candidate).cix.rank_count;
        if (!rank_insert(node, local_rank, instance, truth))
            fail("rank decision attempted to flip good/nogood");
        if (!track_range) return;
        RankEnvelope &envelope = rank_envelopes_[instance];
        if (envelope.false_suffix_begin == UINT32_MAX)
            envelope.false_suffix_begin = rank_count;
        if (truth) {
            envelope.smallest_good = std::min(envelope.smallest_good, local_rank);
            envelope.largest_good = std::max(envelope.largest_good, local_rank);
        } else {
            while (envelope.false_prefix_end < rank_count &&
                   rank_store_.known_false(envelope.false_prefix_end, instance))
                ++envelope.false_prefix_end;
            while (envelope.false_suffix_begin > 0U &&
                   rank_store_.known_false(envelope.false_suffix_begin - 1U, instance))
                --envelope.false_suffix_begin;
        }
    }

    bool rank_learning_enabled(std::size_t node, std::uint64_t requested) const {
        if (rank_single_visit_[node]) return false;
        for (std::uint64_t bits = requested & dag_[node].leaves; bits; bits &= bits - 1U) {
            const auto leaf = __builtin_ctzll(bits);
            if (rank_store_.enabled(rank_full_plans_[node][leaf].id) ||
                rank_store_.enabled(rank_local_plans_[node][leaf].id)) return true;
        }
        return false;
    }

    RankProofCell *rank_active_proof(std::size_t node, std::uint32_t key) {
        if (!rank_proofs_enabled_ || key == kNullRank) return nullptr;
        const auto leaf = __builtin_ctzll(dag_[node].leaves);
        const auto &edge = *dag_[node].edge_by_leaf[leaf];
        const auto &candidate = dag_[node].candidate_is_left_by_leaf[leaf] ? edge.left : edge.right;
        if (edge.op != POLICY_OP_EQ || !column_is_unique(candidate)) return nullptr;
        return ensure_rank_proof(node, key);
    }

    void rank_record_row(std::size_t node, std::uint32_t key, RankProofCell *proof) {
        if (proof) {
            proof->decided |= dag_[node].edge_proof_bit;
            proof->truth |= dag_[node].edge_proof_bit;
        }
        if (key == kNullRank || !rank_proofs_enabled_) return;
        for (auto &projection : functional_rank_projections_[node]) {
            if (key >= projection.child_rank_by_entering_rank.size()) continue;
            auto &stored = projection.child_rank_by_entering_rank[key];
            const auto row = bindings_[projection.child_column.node_id];
            const auto value = row < 0 ? kNullRank : row_local_rank(projection.child_column, row);
            const auto encoded = value == kNullRank ? FunctionalRankProjection::null_rank : value;
            if (stored == FunctionalRankProjection::unknown) {
                stored = encoded;
                CF_COUNT(++functional_projection_strengthens_);
            } else if (stored != encoded) {
                fail("our_pg functional rank projection attempted to flip");
            }
        }
    }

    std::uint64_t rank_solve_children(std::size_t node, std::uint64_t passing,
                                     RankProofCell *proof) {
        std::uint64_t pending = dag_[node].children.size() >= 64U ? UINT64_MAX :
            ((std::uint64_t{1} << dag_[node].children.size()) - 1U);
        while (pending && passing && !aborted_) {
            const unsigned first = __builtin_ctzll(pending);
            unsigned chosen = first;
            if (frontier_gate_enabled(node, __builtin_popcountll(pending))) {
                std::uint64_t best = UINT64_MAX;
                for (auto choices = pending; choices; choices &= choices - 1U) {
                    const unsigned position = __builtin_ctzll(choices);
                    const auto child = dag_[node].children[position];
                    const auto live = passing & dag_[child].leaves;
                    if (!live) continue;
                    const auto cost = estimate_partner_rows(child, live);
                    if (cost < best) { best = cost; chosen = position; }
                }
            }
            pending &= ~(std::uint64_t{1} << chosen);
            CF_COUNT(++frontier_choices_);
            if (chosen != first) CF_COUNT(++frontier_switches_);
            observe_frontier_choice(node, chosen != first);
            const auto child = dag_[node].children[chosen];
            const auto required = passing & dag_[child].leaves;
            if (!required) continue;
            const auto child_key = entering_rank(child);
            std::uint32_t prefork_key = kNullRank;
            std::uint64_t decided = 0, truth = 0;
            lookup_rank_proof(child, required, &prefork_key, &decided, &truth);
            std::uint64_t success;
            if ((decided & required) == required) {
                success = truth & required;
                CF_COUNT(++prefork_rank_proof_skips_);
                CF_COUNT(rank_proof_hits_ += __builtin_popcountll(required));
                CF_COUNT(rank_proof_good_hits_ += __builtin_popcountll(success));
                CF_COUNT(rank_proof_no_good_hits_ += __builtin_popcountll(required & ~success));
            } else {
                success = solve_node(child, required, 0U);
            }
            RankProofCell *child_cell = proof && child_key != kNullRank ?
                ensure_rank_proof(child, child_key) : nullptr;
            if (child_cell != nullptr) {
                auto &child_proof = *child_cell;
                std::uint64_t relevant = 0;
                for (auto bits = required; bits; bits &= bits - 1U) {
                    const auto leaf = __builtin_ctzll(bits);
                    if (!proof_key_safe_[child][leaf]) continue;
                    const auto mask = subtree_proof_masks_[child][leaf];
                    relevant |= mask;
                    if (success & (std::uint64_t{1} << leaf)) {
                        child_proof.decided |= mask;
                        child_proof.truth |= mask;
                    }
                }
                const auto learned = child_proof.decided & relevant;
                const auto overlap = proof->decided & learned;
                if ((proof->truth ^ child_proof.truth) & overlap)
                    fail("our_pg rank-proof strengthening attempted to flip truth");
                proof->decided |= learned;
                proof->truth = (proof->truth & ~learned) | (child_proof.truth & learned);
                CF_COUNT(rank_proof_backtrack_strengthens_ += __builtin_popcountll(learned & ~overlap));
            }
            passing &= ~required | success;
        }
        return passing;
    }


    // Each range is an OR over complete, per-rank outcomes. Local good
    // results are never combined across different rows of a multi-row rank.
    std::uint64_t solve_rank_node(std::size_t node, std::uint64_t requested,
                                  std::uint64_t settle_on_success) {
        requested &= dag_[node].leaves;
        if (requested == 0U || aborted_) return 0U;
        CF_COUNT(++node_calls_[node]);
        std::uint64_t remaining = requested, result = 0U;
        apply_terminal_groups(node, requested, &result, &remaining, settle_on_success);
        if (!remaining || aborted_) return result;
        std::uint32_t proof_key = kNullRank;
        std::uint64_t proof_decided = 0, proof_truth = 0;
        lookup_rank_proof(node, remaining, &proof_key, &proof_decided, &proof_truth);
        remaining &= ~proof_decided;
        result |= proof_truth & proof_decided;
        CF_COUNT(rank_proof_hits_ += __builtin_popcountll(proof_decided));
        CF_COUNT(rank_proof_good_hits_ += __builtin_popcountll(proof_truth & proof_decided));
        CF_COUNT(rank_proof_no_good_hits_ += __builtin_popcountll(proof_decided & ~proof_truth));
        if (!remaining) return result;
        RankProofCell *active_proof = rank_active_proof(node, proof_key);
        bool visited_partner = false;
        const std::uint64_t checks_before = rank_store_.probes;
        const std::size_t representative = __builtin_ctzll(remaining);
        const NormalizedAtom &edge = *dag_[node].edge_by_leaf[representative];
        const bool candidate_left = dag_[node].candidate_is_left_by_leaf[representative];
        const ColumnRef &candidate = candidate_left ? edge.left : edge.right;
        ColumnIndex &index = column(candidate);
        const LookupResult lookup = edge_lookup(edge, candidate_left);
        tuple_index::Rows tuple_rows{};
        bool tuple_used=false;
        // DAG nodes are acyclic; each active recursive frame has its own scratch slots.
        auto &full = rank_full_instances_[node];
        auto &local = rank_local_instances_[node];
        std::uint64_t full_enabled = 0U, local_enabled = 0U;
        for (std::uint64_t bits = rank_single_visit_[node] ? 0U : remaining; bits; bits &= bits - 1U) {
            const std::size_t leaf = __builtin_ctzll(bits);
            const std::uint64_t bit = std::uint64_t{1} << leaf;
            const auto &full_plan = rank_full_plans_[node][leaf];
            const auto &local_plan = rank_local_plans_[node][leaf];
            if (rank_store_.enabled(full_plan.id)) {
                full_enabled |= bit;
                full[leaf] = rank_fill_predicate(full_plan);
            }
            if (local_plan.id != full_plan.id && rank_store_.enabled(local_plan.id)) {
                local_enabled |= bit;
                local[leaf] = rank_fill_predicate(local_plan);
            }
            if (lookup.count == 0 && edge.op == POLICY_OP_EQ) {
                const ColumnRef &parent = candidate_left ? edge.right : edge.left;
                const auto parent_row = bindings_[parent.node_id];
                const std::uint32_t empty_rank = parent_row < 0 ? kNullRank :
                    row_universe_rank(parent, parent_row);
                if (empty_rank != kNullRank) {
                    bool truth = false;
                    if ((full_enabled & bit) && rank_lookup(node, empty_rank, full[leaf], &truth, 0U, 0U) && truth)
                        fail("empty rank was learned good");
                    if (((full_enabled & bit) && !rank_insert(node, empty_rank, full[leaf], false)) ||
                        ((local_enabled & bit) && !rank_insert(node, empty_rank, local[leaf], false)))
                        fail("empty rank verdict flipped");
                }
            }
            if (!(full_enabled & bit) || edge.op == POLICY_OP_EQ) continue;
            const auto found = rank_envelopes_.find(full[leaf]);
            if (edge.op == POLICY_OP_EQ || lookup.count != 1 ||
                found == rank_envelopes_.end()) {
                rank_observe_range(node, full[leaf].id, false, 0U);
                continue;
            }
            const auto [begin, end] = lookup.ranges[0];
            const RankEnvelope &envelope = found->second;
            bool known = false, truth = false;
            if (begin == 0U) {
                if (envelope.smallest_good < end) { known = true; truth = true; }
                else if (end <= envelope.false_prefix_end) known = true;
            }
            if (!known && end == index.cix.rank_count) {
                if (envelope.smallest_good != UINT32_MAX && envelope.largest_good >= begin) {
                    known = true; truth = true;
                } else if (begin >= envelope.false_suffix_begin) known = true;
            }
            if (known) {
                // Good skips at least one witness; nogood skips every row in this range.
                rank_observe_range(node, full[leaf].id, true,
                    truth ? 1U : posting_rows(index, lookup));
                CF_COUNT(++rank_range_hits_);
                remaining &= ~bit;
                if (truth) result |= bit;
            } else {
                rank_observe_range(node, full[leaf].id, false, 0U);
            }
        }
        for (int interval = 0; interval < lookup.count && remaining && !aborted_; ++interval) {
            for (std::uint32_t rank = lookup.ranges[interval].first;
                 rank < lookup.ranges[interval].second && remaining && !aborted_; ++rank) {
                if ((rank & 4095U) == 0U) CHECK_FOR_INTERRUPTS();
                std::uint32_t begin = index.cix.begin(rank);
                std::uint32_t end = index.cix.end(rank);
                const bool multirow = end - begin > 1U;
                if (multirow) {
                    CF_COUNT(++rank_multirow_arrivals_);
                    CF_COUNT(++rank_multirow_by_node_[node].arrivals);
                }
                std::uint64_t scan = remaining, rank_good = 0U, local_good = 0U;
                for (std::uint64_t bits = scan & (full_enabled | local_enabled); bits; bits &= bits - 1U) {
                    const std::size_t leaf = __builtin_ctzll(bits);
                    const std::uint64_t bit = std::uint64_t{1} << leaf;
                    bool truth = false;
                    if ((full_enabled & bit) &&
                        rank_lookup(node, rank, full[leaf], &truth,
                                           end - begin)) {
                        scan &= ~bit;
                        if (composite_indexes_[node]) CF_COUNT(++composite_decision_hits_);
                        if (truth) rank_good |= bit;
                        if (multirow) {
                            CF_COUNT(++rank_multirow_stops_);
                            auto &stats = rank_multirow_by_node_[node];
                            if (truth) CF_COUNT(++stats.good_stops);
                            else CF_COUNT(++stats.nogood_stops);
                        }
                    } else if ((local_enabled & bit) &&
                               rank_lookup(node, rank, local[leaf], &truth,
                                                  end - begin)) {
                        if (!truth) scan &= ~bit;
                        else fail("partial good must not be stored");
                    }
                }
                if (scan && composite_indexes_[node]) {
                    CF_COUNT(composite_decision_misses_ += __builtin_popcountll(scan));
                    tuple_rows = composite_rows(node, representative);
                    tuple_used=true;
                    begin = 0U;
                    end = tuple_rows.size();
                }
                if (scan && multirow) {
                    CF_COUNT(++rank_multirow_descents_);
                    CF_COUNT(++rank_multirow_by_node_[node].scans);
                }
                const std::uint64_t unresolved = scan;
                for (std::uint32_t cursor = begin; cursor < end && scan && !aborted_; ++cursor) {
                    const std::uint32_t row = tuple_used ? tuple_rows[cursor] :
                        u32le(index.cix.child_rows + cursor * 4ULL);
                    ++partner_touches_; CF_COUNT(++node_partner_touches_[node]);
                    visited_partner = true;
                    for (int occurrence : dag_[node].bound_occurrences) bindings_[occurrence] = row;
                    rank_record_row(node, proof_key, active_proof);
                    std::uint64_t passing = evaluate_filters_with_rank_proof(node, scan, active_proof);
                    local_good |= passing;
                    passing = rank_solve_children(node, passing, active_proof);
                    for (int occurrence : dag_[node].bound_occurrences) bindings_[occurrence] = -1;
                    rank_good |= passing;
                    scan &= ~passing;
                }
                const std::uint64_t completed = rank_good | (aborted_ ? 0U : unresolved);
                for (std::uint64_t bits = completed & unresolved & (full_enabled | local_enabled); bits; bits &= bits - 1U) {
                    const std::size_t leaf = __builtin_ctzll(bits);
                    const std::uint64_t bit = std::uint64_t{1} << leaf;
                    if (full_enabled & bit)
                        rank_learn(node, rank, candidate, full[leaf], (rank_good & bit) != 0U,
                                   edge.op != POLICY_OP_EQ);
                    // Only store local nogood after every row failed locally.
                    // A full good has a single joint witness by construction.
                    if ((local_enabled & bit) && !(local_good & bit) && !aborted_)
                        rank_learn(node, rank, candidate, local[leaf], false);
                }
                if (aborted_) CF_COUNT(++rank_interrupted_);
                result |= rank_good;
                remaining &= ~rank_good;
                const std::uint64_t complete_root = rank_good & settle_on_success;
                if (complete_root) settle(complete_root, complete_root);
            }
        }
        if (active_proof) {
            if (!aborted_ && !visited_partner && posting_rows(index, lookup) == 0U) {
                active_proof->decided |= dag_[node].edge_proof_bit;
                active_proof->truth &= ~dag_[node].edge_proof_bit;
                CF_COUNT(++rank_proof_atom_strengthens_);
            }
            for (auto bits = result; bits; bits &= bits - 1U) {
                const auto leaf = __builtin_ctzll(bits);
                if (!proof_key_safe_[node][leaf]) continue;
                const auto mask = subtree_proof_masks_[node][leaf];
                if (active_proof->decided & ~active_proof->truth & mask)
                    fail("our_pg rank-proof good attempted to overwrite nogood");
                CF_COUNT(rank_proof_backtrack_strengthens_ += __builtin_popcountll(mask & ~active_proof->decided));
                active_proof->decided |= mask;
                active_proof->truth |= mask;
            }
        }
        if (cf_rankstore_dump)
            CF_COUNT(++rank_checks_per_arrival_[rank_store_.probes - checks_before]);
        return result;
    }

    std::uint64_t solve_node_v4(std::size_t node,
                             std::uint64_t requested,
                             std::uint64_t settle_on_success) {
        std::uint64_t interval_good = 0, interval_done = 0;
        for (auto bits = requested & dag_[node].leaves; !aborted_ && bits; bits &= bits - 1U) {
            const auto leaf = __builtin_ctzll(bits);
            bool truth = false;
            if (interval_truth(node, leaf, &truth)) {
                const auto bit = std::uint64_t{1} << leaf;
                interval_done |= bit;
                if (truth) interval_good |= bit;
            }
        }
        if (interval_done) {
            const auto complete = interval_good & settle_on_success;
            if (complete) settle(complete, complete);
            const auto rest = requested & ~interval_done;
            return interval_good | (rest && !aborted_ ? solve_node(node, rest, settle_on_success) : 0U);
        }
        if (rank_store_mode_ && (composite_indexes_[node] || rank_single_visit_[node] || rank_learning_enabled(node, requested)))
            return solve_rank_node(node, requested, settle_on_success);
        if (requested == 0 || aborted_) return 0;
        CF_COUNT(++node_calls_[node]);
        requested &= dag_[node].leaves;
        if (requested == 0) return 0;
        std::uint64_t result = 0;
        std::uint64_t remaining = requested;
        apply_terminal_groups(
            node, requested, &result, &remaining, settle_on_success);
        if (remaining == 0U || aborted_) return result;

        std::uint32_t rank_proof_key = kNullRank;
        std::uint64_t proof_decided = 0U;
        std::uint64_t proof_truth = 0U;
        lookup_rank_proof(node, remaining, &rank_proof_key,
                          &proof_decided, &proof_truth);
        if (proof_decided != 0U) {
            remaining &= ~proof_decided;
            result |= proof_truth & proof_decided;
            CF_COUNT(rank_proof_hits_ += static_cast<std::uint64_t>(
                __builtin_popcountll(proof_decided)));
            CF_COUNT(rank_proof_good_hits_ += static_cast<std::uint64_t>(
                __builtin_popcountll(proof_truth & proof_decided)));
            CF_COUNT(rank_proof_no_good_hits_ += static_cast<std::uint64_t>(
                __builtin_popcountll(proof_decided & ~proof_truth)));
        }
        if (remaining == 0U) return result;

        std::array<FusedMemoKey, 64> keys;
        std::uint64_t keyed = 0;
        for (std::uint64_t bits = rank_store_mode_ ? 0U : requested; bits != 0; bits &= bits - 1U) {
            const std::size_t leaf = static_cast<std::size_t>(__builtin_ctzll(bits));
            FusedMemoStore &store = memo_[node][leaf];
            if (!store.enabled || !make_memo_key(node, leaf, &keys[leaf])) continue;
            keyed |= std::uint64_t{1} << leaf;
            bool truth = false;
            if (memo_lookup(store, keys[leaf], &truth)) {
                CF_COUNT(++node_memo_hits_[node]);
                remaining &= ~(std::uint64_t{1} << leaf);
                if (truth) result |= std::uint64_t{1} << leaf;
            }
        }
        if (remaining == 0) return result;

        const std::uint64_t unresolved = remaining;
        const std::uint64_t touches_before = partner_touches_;
        const std::size_t representative = static_cast<std::size_t>(
            __builtin_ctzll(dag_[node].leaves));
        const NormalizedAtom &entry_edge =
            *dag_[node].edge_by_leaf[representative];
        const bool entry_candidate_left =
            dag_[node].candidate_is_left_by_leaf[representative];
        const ColumnRef &entry_candidate = entry_candidate_left ?
            entry_edge.left : entry_edge.right;
        const bool functional_entry = rank_proofs_enabled_ &&
            entry_edge.op == POLICY_OP_EQ &&
            column_is_unique(entry_candidate);
        RankProofCell *active_rank_proof = nullptr;
        if (functional_entry && rank_proof_key != kNullRank)
            active_rank_proof = ensure_rank_proof(node, rank_proof_key);
        bool visited_partner = false;
        visit_partners(node, remaining, [&](std::uint64_t connected) {
            visited_partner = true;
            if (active_rank_proof != nullptr) {
                active_rank_proof->decided |= dag_[node].edge_proof_bit;
                active_rank_proof->truth |= dag_[node].edge_proof_bit;
            }
            if (rank_proof_key != kNullRank) {
                for (FunctionalRankProjection &projection :
                     functional_rank_projections_[node]) {
                    if (rank_proof_key >=
                        projection.child_rank_by_entering_rank.size()) {
                        continue;
                    }
                    std::uint32_t &stored =
                        projection.child_rank_by_entering_rank[rank_proof_key];
                    const std::int64_t child_row =
                        bindings_[projection.child_column.node_id];
                    const std::uint32_t value = child_row < 0 ? kNullRank :
                        row_local_rank(projection.child_column,
                            static_cast<std::uint32_t>(child_row));
                    const std::uint32_t encoded = value == kNullRank ?
                        FunctionalRankProjection::null_rank : value;
                    if (stored == FunctionalRankProjection::unknown) {
                        stored = encoded;
                        CF_COUNT(++functional_projection_strengthens_);
                    } else if (stored != encoded) {
                        fail("our_pg functional rank projection attempted to flip");
                    }
                }
            }
            std::uint64_t partner_success = evaluate_filters_with_rank_proof(
                node, connected, active_rank_proof);
            std::uint64_t pending = dag_[node].children.size() >= 64U ?
                std::numeric_limits<std::uint64_t>::max() :
                ((std::uint64_t{1} << dag_[node].children.size()) - 1U);
            while (pending != 0U && partner_success != 0U && !aborted_) {
                const unsigned first = static_cast<unsigned>(__builtin_ctzll(pending));
                unsigned chosen = first;
                if (frontier_gate_enabled(node, __builtin_popcountll(pending))) {
                    std::uint64_t best = std::numeric_limits<std::uint64_t>::max();
                    for (std::uint64_t choices = pending;
                         choices != 0U; choices &= choices - 1U) {
                        const unsigned position = static_cast<unsigned>(
                            __builtin_ctzll(choices));
                        const std::size_t candidate = dag_[node].children[position];
                        const std::uint64_t live =
                            partner_success & dag_[candidate].leaves;
                        if (live == 0U) continue;
                        const std::uint64_t cost =
                            estimate_partner_rows(candidate, live);
                        if (cost < best) {
                            best = cost;
                            chosen = position;
                        }
                    }
                }
                pending &= ~(std::uint64_t{1} << chosen);
                CF_COUNT(++frontier_choices_);
                if (chosen != first) CF_COUNT(++frontier_switches_);
                observe_frontier_choice(node, chosen != first);
                const std::size_t child = dag_[node].children[chosen];
                const std::uint64_t required = partner_success & dag_[child].leaves;
                if (required == 0) continue;
                const std::uint32_t child_proof_key = entering_rank(child);
                std::uint32_t prefork_key = kNullRank;
                std::uint64_t prefork_decided = 0U;
                std::uint64_t prefork_truth = 0U;
                lookup_rank_proof(child, required, &prefork_key,
                                  &prefork_decided, &prefork_truth);
                std::uint64_t success = 0U;
                if ((prefork_decided & required) == required) {
                    success = prefork_truth & required;
                    CF_COUNT(++prefork_rank_proof_skips_);
                    CF_COUNT(rank_proof_hits_ += static_cast<std::uint64_t>(
                        __builtin_popcountll(required)));
                    CF_COUNT(rank_proof_good_hits_ += static_cast<std::uint64_t>(
                        __builtin_popcountll(success)));
                    CF_COUNT(rank_proof_no_good_hits_ += static_cast<std::uint64_t>(
                        __builtin_popcountll(required & ~success)));
                } else {
                    success = solve_node(child, required, 0);
                }
                RankProofCell *child_cell = active_rank_proof != nullptr &&
                    child_proof_key != kNullRank ? ensure_rank_proof(child, child_proof_key) : nullptr;
                if (child_cell != nullptr) {
                    RankProofCell &child_proof = *child_cell;
                    std::uint64_t relevant = 0U;
                    for (std::uint64_t bits = required;
                         bits != 0U; bits &= bits - 1U) {
                        const std::size_t leaf = static_cast<std::size_t>(
                            __builtin_ctzll(bits));
                        const std::uint64_t leaf_bit =
                            std::uint64_t{1} << leaf;
                        if (proof_key_safe_[child][leaf] == 0U) continue;
                        const std::uint64_t child_mask =
                            subtree_proof_masks_[child][leaf];
                        relevant |= child_mask;
                        if ((success & leaf_bit) != 0U) {
                            child_proof.decided |= child_mask;
                            child_proof.truth |= child_mask;
                        }
                    }
                    const std::uint64_t learned =
                        child_proof.decided & relevant;
                    const std::uint64_t overlap =
                        active_rank_proof->decided & learned;
                    if (((active_rank_proof->truth ^ child_proof.truth) &
                         overlap) != 0U) {
                        fail("our_pg rank-proof strengthening attempted to flip truth");
                    }
                    active_rank_proof->decided |= learned;
                    active_rank_proof->truth =
                        (active_rank_proof->truth & ~learned) |
                        (child_proof.truth & learned);
                    CF_COUNT(rank_proof_backtrack_strengthens_ +=
                        static_cast<std::uint64_t>(
                            __builtin_popcountll(learned & ~overlap)));
                }
                partner_success &= ~required | success;
            }
            const std::uint64_t newly_satisfied = partner_success & ~result;
            result |= newly_satisfied;
            remaining &= ~partner_success;
            const std::uint64_t completed = newly_satisfied & settle_on_success;
            if (completed != 0) settle(completed, completed);
            return remaining == 0 || aborted_;
        });

        const bool exhausted = !aborted_;
        const std::uint64_t decided =
            (result & unresolved) | (exhausted ? remaining : 0);
        if (active_rank_proof != nullptr) {
            if (exhausted && !visited_partner) {
                active_rank_proof->decided |= dag_[node].edge_proof_bit;
                active_rank_proof->truth &= ~dag_[node].edge_proof_bit;
                CF_COUNT(++rank_proof_atom_strengthens_);
            }
            for (std::uint64_t bits = result & decided;
                 bits != 0U; bits &= bits - 1U) {
                const std::size_t leaf = static_cast<std::size_t>(
                    __builtin_ctzll(bits));
                if (proof_key_safe_[node][leaf] == 0U) continue;
                const std::uint64_t mask =
                    subtree_proof_masks_[node][leaf];
                const std::uint64_t fresh =
                    mask & ~active_rank_proof->decided;
                active_rank_proof->decided |= mask;
                active_rank_proof->truth |= mask;
                CF_COUNT(rank_proof_backtrack_strengthens_ +=
                    static_cast<std::uint64_t>(__builtin_popcountll(fresh)));
            }
        }
        const std::uint64_t touch_cost = partner_touches_ - touches_before;
        for (std::uint64_t bits = rank_store_mode_ ? 0U : (decided & keyed); bits != 0; bits &= bits - 1U) {
            const std::size_t leaf = static_cast<std::size_t>(__builtin_ctzll(bits));
            memo_insert(memo_[node][leaf], keys[leaf],
                        (result & (std::uint64_t{1} << leaf)) != 0, touch_cost);
        }
        return result;
    }

    int partial(const FormulaNode *node) const {
        switch (node->kind) {
            case FormulaNode::Branch: {
                const std::uint64_t bit = std::uint64_t{1} << node->leaf_id;
                if ((settled_ & bit) == 0) return -1;
                return (truth_ & bit) != 0 ? 1 : 0;
            }
            case FormulaNode::And: {
                const int left = partial(node->left.get());
                if (left == 0) return 0;
                const int right = partial(node->right.get());
                if (right == 0) return 0;
                return left == 1 && right == 1 ? 1 : -1;
            }
            case FormulaNode::Or: {
                const int left = partial(node->left.get());
                if (left == 1) return 1;
                const int right = partial(node->right.get());
                if (right == 1) return 1;
                return left == 0 && right == 0 ? 0 : -1;
            }
            case FormulaNode::Not: {
                const int value = partial(node->left.get());
                return value < 0 ? -1 : 1 - value;
            }
            case FormulaNode::True: return 1;
            case FormulaNode::False: return 0;
        }
        return -1;
    }

    void settle(std::uint64_t bits, std::uint64_t truths) {
        const std::uint64_t overlap = settled_ & bits;
        if ((((truth_ ^ truths) & overlap) != 0U))
            fail("our_pg formula leaf attempted to flip raw truth");
        if (!formula_truth_table_.empty()) {
            for (std::uint64_t fresh = bits & ~settled_;
                 fresh != 0U; fresh &= fresh - 1U) {
                const std::size_t leaf = static_cast<std::size_t>(
                    __builtin_ctzll(fresh));
                const std::uint64_t bit = std::uint64_t{1} << leaf;
                formula_ternary_state_ += formula_ternary_powers_[leaf] *
                    ((truths & bit) != 0U ? 2U : 1U);
            }
        }
        truth_ = (truth_ & ~bits) | (truths & bits);
        settled_ |= bits;
        aborted_ = partial_current() >= 0;
    }

    void apply_root_memo_frontier(std::uint64_t candidates) {
        for (std::size_t child : dag_[0].children) {
            std::uint64_t requested =
                candidates & dag_[child].leaves & ~settled_;
            
            
            
            
            
            
            
            
            
            
            if (__builtin_popcountll(dag_[child].leaves) > 1) continue;

            
            
            std::uint64_t shared_managed = 0;
            for (std::size_t group_index :
                 terminal_groups_by_node_[child]) {
                shared_managed |= terminal_groups_[group_index].leaves;
            }
            requested &= ~shared_managed;
            for (std::uint64_t bits = requested;
                 bits != 0U && !aborted_; bits &= bits - 1U) {
                const std::size_t leaf = static_cast<std::size_t>(
                    __builtin_ctzll(bits));
                FusedMemoStore &store = memo_[child][leaf];
                FusedMemoKey key;
                if (!store.enabled || !make_memo_key(child, leaf, &key))
                    continue;
                bool learned = false;
                if (!memo_lookup(store, key, &learned)) continue;
                const std::uint64_t bit = std::uint64_t{1} << leaf;
                settle(bit, learned ? bit : 0U);
            }
            if (aborted_) return;
        }
    }

    bool evaluate_target(std::uint32_t row) {
        target_walk_started_=true;
        ++target_evals_;
        settled_ = 0;
        truth_ = 0;
        formula_ternary_state_ = 0;
        aborted_ = false;
        bindings_[target_node_] = row;
        if (leaves_.empty()) {
            const bool result = partial_current() == 1;
            bindings_[target_node_] = -1;
            return result;
        }
        const std::uint64_t all = dag_[0].leaves;
        std::uint64_t candidates = evaluate_filters(0, all);
        const std::uint64_t denied = all & ~candidates;
        if (denied != 0) settle(denied, 0);
        if (!aborted_) apply_chain_frontier(candidates);
        candidates &= ~settled_;

        if (!aborted_) apply_root_terminal_frontier(candidates);
        if (!rank_store_mode_ && !aborted_) apply_root_memo_frontier(candidates);

        std::uint64_t child_leaves = 0;
        for (std::size_t child : dag_[0].children) child_leaves |= dag_[child].leaves;
        const std::uint64_t local = all & ~child_leaves;
        if (!aborted_ && (local & candidates) != 0)
            settle(local & candidates, local & candidates);

        std::uint64_t pending = dag_[0].children.size() >= 64U ?
            std::numeric_limits<std::uint64_t>::max() :
            ((std::uint64_t{1} << dag_[0].children.size()) - 1U);
        while (pending != 0U && !aborted_) {
            candidates &= ~settled_;
            const unsigned first = static_cast<unsigned>(__builtin_ctzll(pending));
            unsigned chosen = first;
            if (frontier_gate_enabled(0, __builtin_popcountll(pending))) {
                std::uint64_t best = std::numeric_limits<std::uint64_t>::max();
                for (std::uint64_t choices = pending;
                     choices != 0U; choices &= choices - 1U) {
                    const unsigned position = static_cast<unsigned>(
                        __builtin_ctzll(choices));
                    const std::size_t candidate = dag_[0].children[position];
                    const std::uint64_t live =
                        candidates & dag_[candidate].leaves;
                    if (live == 0U) continue;
                    const std::uint64_t cost =
                        estimate_partner_rows(candidate, live);
                    if (cost < best) {
                        best = cost;
                        chosen = position;
                    }
                }
            }
            pending &= ~(std::uint64_t{1} << chosen);
            CF_COUNT(++frontier_choices_);
            if (chosen != first) CF_COUNT(++frontier_switches_);
            observe_frontier_choice(0, chosen != first);
            const std::size_t child = dag_[0].children[chosen];
            std::uint64_t future = 0;
            for (std::uint64_t choices = pending;
                 choices != 0U; choices &= choices - 1U) {
                const unsigned position = static_cast<unsigned>(
                    __builtin_ctzll(choices));
                future |= dag_[dag_[0].children[position]].leaves;
            }
            const std::uint64_t required = candidates & dag_[child].leaves;
            if (required != 0) {
                const std::uint64_t success = solve_node(child, required,
                    rank_store_mode_ ? required & ~future : 0U);
                if (aborted_) break;
                const std::uint64_t failed = required & ~success;
                candidates &= ~failed;
                if (failed != 0) settle(failed, 0);
            }
            if (aborted_) break;
            const std::uint64_t complete = candidates & dag_[child].leaves & ~future;
            if (complete != 0) settle(complete, complete);
        }
        if (!aborted_) {
            const std::uint64_t unresolved = all & ~settled_;
            if (unresolved != 0) settle(unresolved, candidates & unresolved);
        }
        const int verdict = partial_current();
        bindings_[target_node_] = -1;
        if (verdict < 0) fail("our_pg fused formula remained unresolved");
        return verdict == 1;
    }

    const PolicyArtifactCNew *arts_;
    int art_count_;
    const PolicyEngineInputC *in_;
    std::string target_;
    int target_node_;
    int max_node_ = 0;
    std::vector<NormalizedAtom> normalized_;
    std::unordered_map<int, const NormalizedAtom *> atom_by_id_;
    std::unique_ptr<FormulaNode> formula_;
    std::vector<FormulaNode *> leaves_;
    std::unique_ptr<FormulaNode> bound_formula_;
    std::vector<FormulaNode *> bound_leaves_;
    FlatFormulaMode flat_mode_ = FlatFormulaMode::none;
    std::uint64_t flat_positive_ = 0;
    std::uint64_t flat_negative_ = 0;
    int flat_constant_ = -1;
    std::vector<std::uint64_t> formula_ternary_powers_;
    std::vector<std::int8_t> formula_truth_table_;
    std::uint64_t formula_ternary_state_ = 0;
    std::vector<FusedDagNode> dag_;
    std::vector<std::vector<std::vector<ColumnRef>>> dependencies_;
    RankStoreMemory old_memo_memory_;
    std::vector<std::vector<FusedMemoStore>> memo_;
    bool rank_store_mode_ = false;
    std::vector<std::shared_ptr<CompositeConnection>> composite_indexes_;
    std::vector<std::array<IntervalPlan, 64>> interval_plans_;
    double interval_build_ms_ = 0;
    double composite_build_ms_ = 0;
    std::uint64_t online_build_tuples_ = 0, composite_lookups_ = 0, interval_lookups_ = 0;
    RankDecisionStore rank_store_;
    std::pmr::unordered_map<RankPredicateInstance, RankEnvelope, RankPredicateHash>
        rank_envelopes_{&rank_store_.memory};
    std::map<std::string, std::uint32_t> rank_predicate_ids_;
    std::vector<const std::string *> rank_predicate_text_;
    std::vector<std::string> rank_gate_columns_;
    std::vector<std::array<RankPredicatePlan, 64>> rank_full_plans_;
    std::vector<std::array<RankPredicatePlan, 64>> rank_local_plans_;
    std::vector<std::array<RankPredicateInstance, 64>> rank_full_instances_;
    std::vector<std::array<RankPredicateInstance, 64>> rank_local_instances_;
    std::vector<std::uint8_t> rank_single_visit_, rank_parent_unique_;
    std::vector<std::size_t> rank_parent_nodes_;
    std::vector<std::uint64_t> rank_node_probes_, rank_node_writes_;
    std::map<const LocalBooleanGroup *, std::vector<std::size_t>> rank_boolean_spans_;
    std::uint64_t rank_range_hits_ = 0;
    std::uint64_t packed_forward_columns_ = 0;
    std::uint64_t terminal_build_tuples_ = 0;
    std::uint64_t rank_multirow_arrivals_ = 0;
    std::uint64_t rank_multirow_descents_ = 0;
    std::uint64_t rank_multirow_stops_ = 0;
    struct RankMultirowStats {
        std::uint64_t arrivals = 0;
        std::uint64_t scans = 0;
        std::uint64_t good_stops = 0;
        std::uint64_t nogood_stops = 0;
    };
    std::vector<RankMultirowStats> rank_multirow_by_node_;
    std::uint64_t rank_interrupted_ = 0;
    std::map<std::uint64_t, std::uint64_t> rank_checks_per_arrival_;
    bool rank_proofs_enabled_ = false;
    std::vector<NodeRankProofPlan> node_rank_proofs_;
    std::vector<std::array<std::uint64_t, 64>> subtree_proof_masks_;
    std::vector<std::array<std::uint8_t, 64>> proof_key_safe_;
    std::vector<std::uint64_t> local_stable_proof_masks_;
    std::vector<std::vector<FunctionalRankProjection>>
        functional_rank_projections_;
    std::vector<BoundPairCache> bound_pair_caches_;
    std::vector<std::int8_t> column_unique_;
    std::vector<std::uint32_t> column_distinct_ranks_;
    std::map<std::string, DomainIndex> domains_;
    std::unordered_map<std::string, std::size_t> column_id_by_key_;
    std::vector<ColumnIndex> columns_;
    std::map<std::pair<std::string, std::string>,
             std::pair<std::uint32_t, std::uint32_t>> literal_bounds_cache_;
    std::vector<TerminalVerdictGroup> terminal_groups_;
    std::vector<std::vector<std::size_t>> terminal_groups_by_node_;
    std::vector<std::int64_t> bindings_;
    std::uint64_t settled_ = 0;
    std::uint64_t truth_ = 0;
    std::uint64_t partner_touches_ = 0;
    std::uint64_t target_evals_ = 0;
    std::vector<std::uint64_t> node_calls_;
    std::vector<std::uint64_t> node_partner_touches_;
    std::vector<std::uint64_t> node_memo_hits_;
    std::vector<std::uint64_t> node_terminal_hits_;
    std::vector<FrontierGate> frontier_gates_;
    std::vector<RootTerminalProbe> root_terminal_probes_;
    std::uint64_t root_terminal_hits_ = 0;
    std::uint64_t frontier_choices_ = 0;
    std::uint64_t frontier_switches_ = 0;
    std::uint64_t frontier_gated_choices_ = 0;
    std::uint64_t frontier_gates_disabled_ = 0;
    std::uint64_t prefork_rank_proof_skips_ = 0;
    std::uint64_t rank_proof_hits_ = 0;
    std::uint64_t rank_proof_good_hits_ = 0;
    std::uint64_t rank_proof_no_good_hits_ = 0;
    std::uint64_t rank_proof_atom_hits_ = 0;
    std::uint64_t rank_proof_atom_strengthens_ = 0;
    std::uint64_t rank_proof_backtrack_strengthens_ = 0;
    std::uint64_t functional_projection_hits_ = 0;
    std::uint64_t functional_projection_strengthens_ = 0;
    std::uint64_t bound_pair_builds_ = 0;
    std::uint64_t bound_pair_build_rows_ = 0;
    std::uint64_t bound_pair_hits_ = 0;
    std::uint64_t bound_pair_misses_ = 0;
    std::uint64_t bound_pair_fallbacks_ = 0;
    static constexpr std::uint32_t kFrontierProbation = 8192U;
    bool aborted_ = false;
    bool target_walk_started_=false;
    // Keep V4's complete member prefix byte-for-byte: even diagnostic storage
    // changes the offsets encoded into clean hot functions if inserted above.
    std::vector<std::string> compiled_loop_recipes_;
    std::uint64_t mixed_request_leaves_=0;
    std::pmr::unordered_map<RankPredicateInstance,full_reuse::SharedEnvelope,RankPredicateHash>
        mixed_envelopes_{&rank_store_.memory};
    using NodeSolver=std::uint64_t(FusedWalkRuntime::*)(std::size_t,std::uint64_t,std::uint64_t);
    std::vector<NodeSolver> node_solvers_;
    std::vector<CompiledRequestGroup> compiled_groups_;
    std::array<int,64> grouped_owner_{};
    std::array<TightBranch*,64> grouped_by_leaf_{};
    std::array<TightBranch::Loop,64> grouped_v4_words_{};
    std::array<TightBranch::BlockLoop,64> grouped_v4_blocks_{};
    std::uint64_t grouped_request_calls_=0,grouped_shared_postings_=0,grouped_shared_rows_=0;
    std::uint64_t grouped_boundary_fills_=0,grouped_per_leaf_rows_=0;
};

#ifndef MEMENTO_COLD_TRANSLATION_UNIT
#include "nested_quantifier_adapter.inc"
// Query-context callbacks also release a runtime if a query errors or is cancelled.
struct DeferredRuntime {
    MemoryContextCallback callback;
    FusedWalkRuntime *runtime;
    DeferredRuntime *next;
};
DeferredRuntime *pending_runtimes=nullptr;

struct DeferredNestedRuntime {
    MemoryContextCallback callback;
    NestedQuantifierRuntime *runtime;
    DeferredNestedRuntime *next;
};
DeferredNestedRuntime *pending_nested_runtimes=nullptr;
void destroy_nested_runtime(void *arg){
    auto *owner=static_cast<DeferredNestedRuntime*>(arg);
    if(!owner->runtime)return;
    auto **link=&pending_nested_runtimes;
    while(*link && *link!=owner)link=&(*link)->next;
    if(*link)*link=owner->next;
    auto *runtime=owner->runtime;owner->runtime=nullptr;delete runtime;
}
NestedQuantifierRuntime *retain_nested_runtime(const PolicyArtifactCNew *arts,int count,
    const PolicyEngineInputC *in,int target_index,int target_node){
    auto *owner=static_cast<DeferredNestedRuntime*>(palloc0(sizeof(DeferredNestedRuntime)));
    owner->callback.func=destroy_nested_runtime;owner->callback.arg=owner;
    MemoryContextRegisterResetCallback(CurrentMemoryContext,&owner->callback);
    try{owner->runtime=new NestedQuantifierRuntime(arts,count,in,target_index,target_node);}
    catch(const std::exception &error){fail(std::string("nested plan: ")+error.what());}
    owner->next=pending_nested_runtimes;pending_nested_runtimes=owner;return owner->runtime;
}

void destroy_deferred_runtime(void *arg) {
    auto *owner=static_cast<DeferredRuntime *>(arg);
    if (!owner->runtime) return;
    auto **link=&pending_runtimes;
    while (*link && *link!=owner) link=&(*link)->next;
    if (*link) *link=owner->next;
    auto *runtime=owner->runtime;
    owner->runtime=nullptr;
    delete runtime;
}

FusedWalkRuntime *retain_runtime(const PolicyArtifactCNew *arts,int art_count,
    const PolicyEngineInputC *in,const std::string &target,int target_node,int target_index) {
    auto *owner=static_cast<DeferredRuntime *>(palloc0(sizeof(DeferredRuntime)));
    owner->callback.func=destroy_deferred_runtime;
    owner->callback.arg=owner;
    MemoryContextRegisterResetCallback(CurrentMemoryContext,&owner->callback);
    owner->runtime=new FusedWalkRuntime(arts,art_count,in,target,target_node,target_index);
    owner->next=pending_runtimes;
    pending_runtimes=owner;
    return owner->runtime;
}

} // namespace memento_runtime

using namespace memento_runtime;

// Called only after the custom filter owns the completed tuple-location bitmap.
extern "C" double our_pg_release_runtime(void) {
    const auto started=std::chrono::steady_clock::now();
    while (pending_runtimes) destroy_deferred_runtime(pending_runtimes);
    while (pending_nested_runtimes) destroy_nested_runtime(pending_nested_runtimes);
    const double duration=std::chrono::duration<double,std::milli>(std::chrono::steady_clock::now()-started).count();
    cf_perf_metric_set("runtime_cleanup_ms",duration);
    return duration;
}


/* Load only the blobs the unchanged walk can request, before exec_ms starts. */
extern "C" void our_pg_preload_artifacts(const PolicyEngineInputC *in) {
    PolicyEvalResultC res{};
    res.target_count=in->target_count;res.target_tables=in->target_tables;
    res.target_node_ids=in->target_node_ids;res.target_asts=in->target_asts;
    res.target_ast_tok_len=in->target_ast_tok_len;res.target_ast_toks=in->target_ast_toks;
    res.target_ast_tok_offsets=in->target_ast_tok_offsets;res.target_ast_tok_counts=in->target_ast_tok_counts;
    res.atom_count=in->atom_count;res.atoms=in->atoms;
    std::set<std::string> columns;
    for (int target_index = 0; target_index < in->target_count; ++target_index) {
        const std::string target(in->target_tables[target_index]);
        const int target_node = in->target_node_ids ? in->target_node_ids[target_index] : 0;
        const auto names=text_lines(lookup_required(nullptr,0,in,"meta/cols/"+target));
        if (names.empty()) fail("No rank-encoded column for target "+target);
        const auto first=split_schema_key(names.front().c_str());
        lookup_required(nullptr,0,in,"canon_fwdidx/"+first.first+"/"+first.second);
        lookup_required(nullptr, 0, in, target + "_ctid");
        std::vector<NormalizedAtom> atoms;
        atoms.reserve(in->atom_count);
        std::unordered_map<int, const NormalizedAtom *> by_id;
        for (int i = 0; i < in->atom_count; ++i) {
            atoms.push_back(normalize_atom(in->atoms[i]));
            auto &atom = atoms.back();
            if (atom.left.node_id < 0 && atom.left.table == target) atom.left.node_id = target_node;
            if (!atom.right_is_const && atom.right.node_id < 0 && atom.right.table == target)
                atom.right.node_id = target_node;
            by_id[atom.atom_id] = &atom;
        }
        if(needs_scoped_quantifiers(in,target_index)){
            for(const auto &atom:atoms){columns.insert(atom.left.key());if(!atom.right_is_const)columns.insert(atom.right.key());}
            continue;
        }
        auto formula = parse_formula(in, target_index, by_id);
        std::vector<FormulaNode *> leaves;
        assign_formula_leaves(formula.get(), &leaves);
        auto use = [&](const NormalizedAtom *atom) {
            columns.insert(atom->left.key());
            if (!atom->right_is_const) columns.insert(atom->right.key());
        };
        for (const auto *leaf : leaves) {
            for (const auto *atom : leaf->atoms) use(atom);
            for (const auto &group : leaf->boolean_groups)
                for (const auto *atom : group.atoms) use(atom);
        }
    }
    for (const auto &key : columns) {
        const auto ref = split_schema_key(key.c_str());
        const std::string domain_id = domain_for_column(nullptr, 0, in, key);
        lookup_required(nullptr,0,in,"universe/domain/"+domain_id);
        lookup_required(nullptr,0,in,"canon_invidx/"+ref.first+"/"+ref.second);
        lookup_required(nullptr,0,in,"canon_fwdidx/"+ref.first+"/"+ref.second);
    }
}

// Returns one bit per target row allowed by the policy.
std::vector<std::uint64_t> our_pg_evaluate_target(
    const PolicyArtifactCNew *arts,
    int art_count,
    const PolicyEngineInputC *in,
    int target_index,
    const std::string &target,
    std::uint32_t total_rows) {
    const int target_node = in->target_node_ids != nullptr
        ? in->target_node_ids[target_index] : 0;
    if (target_node < 0) fail("target occurrence has no node id");
    const auto started=std::chrono::steady_clock::now();
    cf_perf_metric_set("nested_formula_path_used",0);
    cf_perf_metric_set("scoped_quantifier_path_used",0);
    if(needs_scoped_quantifiers(in,target_index)){
        auto *runtime=retain_nested_runtime(arts,art_count,in,target_index,target_node);
        std::vector<std::uint64_t> allowed;
        try{allowed=runtime->run(total_rows);}
        catch(const std::exception &error){fail(std::string("nested execution: ")+error.what());}
        cf_perf_metric_set("engine_target_wall_ms",std::chrono::duration<double,std::milli>(std::chrono::steady_clock::now()-started).count());
        return allowed;
    }
    auto *runtime=retain_runtime(arts,art_count,in,target,target_node,target_index);
    auto allowed=runtime->run(total_rows);
    cf_perf_metric_set("engine_target_wall_ms",std::chrono::duration<double,std::milli>(std::chrono::steady_clock::now()-started).count());
    return allowed;
}

#else
} // namespace memento_runtime
#endif
