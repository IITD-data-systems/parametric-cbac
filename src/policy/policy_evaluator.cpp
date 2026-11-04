#include "policy_evaluator.h"

extern "C" {
#include "postgres.h"
#include "utils/palloc.h"
#include "utils/guc.h"
}

#include <algorithm>
#include <cctype>
#include <cstdlib>
#include <deque>
#include <fstream>
#include <functional>
#include <map>
#include <set>
#include <unordered_set>
#include <sstream>
#include <string>
#include <utility>
#include <vector>
#include <limits>

namespace {

struct AstNode {
    enum Type { VAR, AND, OR, NOT, EXISTS } type;
    std::string key;
    int var_id = -1;
    std::vector<AstNode *> children;
    std::vector<std::string> binders;
};

struct NodeStore {
    std::vector<AstNode *> nodes;
};

static thread_local NodeStore *g_node_store = nullptr;
static thread_local std::map<int,std::map<std::string,int>> g_quantifier_binders;
static bool g_eval_debug = false;

struct Policy {
    int policy_id = -1;
    std::string target;
    std::string expr;
    AstNode *ast = nullptr;
    int line_no = 0;
    std::set<std::string> referenced_tables;
    std::set<std::pair<std::string, std::string>> const_cols;
    std::set<std::string> atom_keys;
    struct AtomDef {
        enum Kind { JOIN_EQ, COL_CONST, COL_COL } kind = COL_CONST;
        std::string key;
        std::string left_table;
        std::string left_col;
        std::string right_table;
        std::string right_col;
        std::string op;
        std::vector<std::string> values;
        int join_class_id = -1;
        int atom_id = -1;
    };
    std::vector<AtomDef> atoms;
};

struct Token {
    enum Type { IDENT, STRING, NUMBER, OP, SLOT, LPAREN, RPAREN, COMMA, AND, OR, NOT, EXISTS } type;
    std::string text;
};

static std::string to_lower(const std::string &s) {
    std::string out = s;
    std::transform(out.begin(), out.end(), out.begin(), [](unsigned char c) { return std::tolower(c); });
    return out;
}

static bool eval_debug_enabled() {
    const char *v = GetConfigOption("custom_filter.debug_mode", true, false);
    if (!v) return false;
    std::string s = to_lower(v);
    return s != "off";
}

static const char *token_type_name(Token::Type t) {
    switch (t) {
        case Token::IDENT: return "IDENT";
        case Token::STRING: return "STRING";
        case Token::NUMBER: return "NUMBER";
        case Token::OP: return "OP";
        case Token::SLOT: return "SLOT";
        case Token::LPAREN: return "LPAREN";
        case Token::RPAREN: return "RPAREN";
        case Token::COMMA: return "COMMA";
        case Token::AND: return "AND";
        case Token::OR: return "OR";
        case Token::NOT: return "NOT";
        case Token::EXISTS: return "EXISTS";
    }
    return "UNKNOWN";
}

static std::string trim(const std::string &s) {
    size_t start = 0;
    while (start < s.size() && std::isspace(static_cast<unsigned char>(s[start]))) start++;
    size_t end = s.size();
    while (end > start && std::isspace(static_cast<unsigned char>(s[end - 1]))) end--;
    return s.substr(start, end - start);
}

static bool env_flag_enabled(const char *name) {
    const char *v = std::getenv(name);
    if (!v) return false;
    std::string s = to_lower(trim(v));
    return !(s.empty() || s == "0" || s == "off" || s == "false" || s == "no");
}

static std::string unquote(const std::string &s) {
    if (s.size() >= 2 && s.front() == '\'' && s.back() == '\'')
        return s.substr(1, s.size() - 2);
    return s;
}

static std::string normalize_number_string(const std::string &s) {
    std::string t = trim(s);
    if (t.empty()) return t;

    std::string sign;
    if (t[0] == '+' || t[0] == '-') {
        if (t[0] == '-') sign = "-";
        t = t.substr(1);
    }

    std::string mant = t;
    std::string exp;
    size_t epos = t.find_first_of("eE");
    if (epos != std::string::npos) {
        mant = t.substr(0, epos);
        exp = t.substr(epos + 1);
    }

    std::string intpart = mant;
    std::string frac;
    size_t dpos = mant.find('.');
    if (dpos != std::string::npos) {
        intpart = mant.substr(0, dpos);
        frac = mant.substr(dpos + 1);
    }

    size_t nz = 0;
    while (nz < intpart.size() && intpart[nz] == '0') nz++;
    intpart = intpart.substr(nz);
    if (intpart.empty()) intpart = "0";

    while (!frac.empty() && frac.back() == '0') frac.pop_back();

    std::string norm = intpart;
    if (!frac.empty())
        norm += "." + frac;

    if (!exp.empty()) {
        exp = trim(exp);
        std::string exp_sign;
        if (!exp.empty() && (exp[0] == '+' || exp[0] == '-')) {
            if (exp[0] == '-') exp_sign = "-";
            exp = exp.substr(1);
        }
        size_t enz = 0;
        while (enz < exp.size() && exp[enz] == '0') enz++;
        exp = exp.substr(enz);
        if (exp.empty()) exp = "0";
        norm += "e" + exp_sign + exp;
    }

    if (norm == "0") sign.clear();
    return sign + norm;
}

static std::string normalize_literal(const Token &tok) {
    std::string val = tok.text;
    if (tok.type == Token::SLOT) {
        ereport(ERROR,
                (errmsg("policy_eval: unresolved value slot in runtime policy"),
                 errdetail("slot %s reached evaluation without query binding", tok.text.c_str())));
    }
    if (tok.type == Token::STRING) {
        val = unquote(val);
        val = trim(val);
        return val;
    }
    if (tok.type == Token::NUMBER) {
        return normalize_number_string(val);
    }
    return trim(val);
}

static bool is_ident_char(char c) {
    return std::isalnum(static_cast<unsigned char>(c)) || c == '_' || c == '.';
}

static bool is_slot_char(char c) {
    return std::isalnum(static_cast<unsigned char>(c)) || c == '_';
}

static std::vector<Token> tokenize_expr(const std::string &expr) {
    std::vector<Token> tokens;
    size_t i = 0;
    while (i < expr.size()) {
        char c = expr[i];
        if (std::isspace(static_cast<unsigned char>(c))) {
            i++;
            continue;
        }
        if (c == '(') {
            tokens.push_back({Token::LPAREN, "("});
            i++;
            continue;
        }
        if (c == ')') {
            tokens.push_back({Token::RPAREN, ")"});
            i++;
            continue;
        }
        if (c == ',') {
            tokens.push_back({Token::COMMA, ","});
            i++;
            continue;
        }
        if (c == '\'') {
            size_t j = i + 1;
            while (j < expr.size()) {
                if (expr[j] == '\'' && (j + 1 >= expr.size() || expr[j + 1] != '\'')) {
                    break;
                }
                if (expr[j] == '\'' && j + 1 < expr.size() && expr[j + 1] == '\'') {
                    j += 2;
                    continue;
                }
                j++;
            }
            if (j < expr.size()) j++;
            tokens.push_back({Token::STRING, expr.substr(i, j - i)});
            i = j;
            continue;
        }
        if (c == '!') {
            if (i + 1 < expr.size() && expr[i + 1] == '=') {
                tokens.push_back({Token::OP, "!="});
                i += 2;
                continue;
            }
            ereport(ERROR, (errmsg("unsupported operator: !")));
        }
        if (c == '<' || c == '>' || c == '=') {
            std::string op;
            op.push_back(c);
            if (i + 1 < expr.size()) {
                char n = expr[i + 1];
                if ((c == '<' || c == '>') && n == '=') {
                    op.push_back(n);
                    i++;
                } else if (c == '<' && n == '>') {
                    op.push_back(n);
                    i++;
                }
            }
            tokens.push_back({Token::OP, op});
            i++;
            continue;
        }
        const bool signed_number =
            (c == '+' || c == '-') && i + 1 < expr.size() &&
            (std::isdigit(static_cast<unsigned char>(expr[i + 1])) ||
             (expr[i + 1] == '.' && i + 2 < expr.size() &&
              std::isdigit(static_cast<unsigned char>(expr[i + 2]))));
        if (signed_number || std::isdigit(static_cast<unsigned char>(c)) ||
            (c == '.' && i + 1 < expr.size() && std::isdigit(static_cast<unsigned char>(expr[i + 1])))) {
            size_t j = i + 1;
            while (j < expr.size() &&
                   (std::isdigit(static_cast<unsigned char>(expr[j])) || expr[j] == '.')) {
                j++;
            }
            tokens.push_back({Token::NUMBER, expr.substr(i, j - i)});
            i = j;
            continue;
        }
        if (std::isalpha(static_cast<unsigned char>(c)) || c == '_') {
            size_t j = i + 1;
            while (j < expr.size() && is_ident_char(expr[j])) j++;
            std::string word = expr.substr(i, j - i);
            std::string lower = to_lower(word);
            if (lower == "date") {
                size_t k = j;
                while (k < expr.size() && std::isspace(static_cast<unsigned char>(expr[k]))) k++;
                if (k < expr.size() && expr[k] == '\'') {
                    ereport(ERROR, (errmsg("unsupported literal form: DATE '...'")));
                }
            }
            if (lower == "and") {
                tokens.push_back({Token::AND, lower});
            } else if (lower == "or") {
                tokens.push_back({Token::OR, lower});
            } else if (lower == "not") {
                tokens.push_back({Token::NOT, lower});
            } else if (lower == "exists") {
                tokens.push_back({Token::EXISTS, lower});
            } else {
                tokens.push_back({Token::IDENT, lower});
            }
            i = j;
            continue;
        }
        if (c == '@' || c == '$') {
            size_t j = i + 1;
            while (j < expr.size() && is_slot_char(expr[j])) j++;
            std::string slot = to_lower(expr.substr(i, j - i));
            tokens.push_back({Token::SLOT, slot});
            i = j;
            continue;
        }
        i++;
    }
    return tokens;
}

static AstNode *make_var_node(const std::string &key) {
    AstNode *node = new AstNode();
    node->type = AstNode::VAR;
    node->key = key;
    if (g_node_store) g_node_store->nodes.push_back(node);
    return node;
}

static AstNode *make_false_node() {
    AstNode *node = new AstNode();
    node->type = AstNode::VAR;
    node->key = "";
    node->var_id = 0; 
    if (g_node_store) g_node_store->nodes.push_back(node);
    return node;
}

static bool ast_is_false_node(const AstNode *node) {
    return node && node->type == AstNode::VAR && node->key.empty() && node->var_id == 0;
}

static AstNode *make_node(AstNode::Type type, AstNode *left, AstNode *right) {
    AstNode *node = new AstNode();
    node->type = type;
    node->children.push_back(left);
    node->children.push_back(right);
    if (g_node_store) g_node_store->nodes.push_back(node);
    return node;
}

static AstNode *make_unary_node(AstNode::Type type, AstNode *child) {
    AstNode *node = new AstNode();
    node->type = type;
    node->children.push_back(child);
    if (g_node_store) g_node_store->nodes.push_back(node);
    return node;
}

static AstNode *clone_ast(const AstNode *node) {
    if (!node) return nullptr;
    if (node->type == AstNode::VAR) {
        AstNode *n = make_var_node(node->key);
        n->var_id = node->var_id;
        return n;
    }
    if (node->type == AstNode::NOT) {
        AstNode *n = new AstNode();
        n->type = node->type;
        if (g_node_store) g_node_store->nodes.push_back(n);
        if (!node->children.empty())
            n->children.push_back(clone_ast(node->children[0]));
        return n;
    }
    AstNode *n = new AstNode();
    n->type = node->type;
    n->binders = node->binders;
    if (g_node_store) g_node_store->nodes.push_back(n);
    for (auto *child : node->children) {
        n->children.push_back(clone_ast(child));
    }
    return n;
}

static std::string join_tokens(const std::vector<Token> &tokens) {
    std::string out;
    for (size_t i = 0; i < tokens.size(); i++) {
        if (i > 0) out.push_back(' ');
        out += tokens[i].text;
    }
    return out;
}

static std::pair<std::string, std::string> split_table_col(const std::string &ident,
                                                           const std::string &target_table) {
    auto pos = ident.find('.');
    if (pos != std::string::npos) {
        return {ident.substr(0, pos), ident.substr(pos + 1)};
    }
    return {target_table, ident};
}

static bool is_op_slot_token(const Token &tok) {
    return tok.type == Token::SLOT && tok.text.rfind("@op", 0) == 0;
}

static bool is_value_slot_token(const Token &tok) {
    return tok.type == Token::SLOT &&
           (tok.text.rfind("@value", 0) == 0 || tok.text.rfind("$value", 0) == 0);
}

static std::string canonicalize_atom(const std::vector<Token> &tokens,
                                     const std::string &target_table,
                                     Policy &policy,
                                     Policy::AtomDef *out_def) {
    if (!out_def) return "";
    *out_def = Policy::AtomDef();

    for (const auto &t : tokens) {
        if (t.type == Token::IDENT && t.text == "between") {
            ereport(ERROR, (errmsg("unsupported operator: between")));
        }
    }

    std::string left_ident;
    std::string op;
    std::string right_ident;
    bool op_from_slot = false;

    for (size_t i = 0; i < tokens.size(); i++) {
        if (tokens[i].type == Token::IDENT) {
            left_ident = tokens[i].text;
            break;
        }
    }
    for (size_t i = 0; i < tokens.size(); i++) {
        if (tokens[i].type == Token::OP || is_op_slot_token(tokens[i])) {
            op = to_lower(tokens[i].text);
            op_from_slot = is_op_slot_token(tokens[i]);
            for (size_t j = i + 1; j < tokens.size(); j++) {
                if (tokens[j].type == Token::IDENT) {
                    right_ident = tokens[j].text;
                    break;
                }
                if (tokens[j].type == Token::STRING || tokens[j].type == Token::NUMBER ||
                    is_value_slot_token(tokens[j])) {
                    break;
                }
            }
            break;
        }
    }

    if (left_ident.empty() || op.empty())
        return "";
    if (op == "<>") op = "!=";
    auto left = split_table_col(left_ident, target_table);
    std::string left_full = left.first + "." + left.second;
    policy.referenced_tables.insert(left.first);

    if (!right_ident.empty()) {
        auto right = split_table_col(right_ident, target_table);
        std::string right_full = right.first + "." + right.second;
        policy.referenced_tables.insert(right.first);

        if (op == "=") {
            out_def->kind = Policy::AtomDef::JOIN_EQ;
            out_def->left_table = left.first;
            out_def->left_col = left.second;
            out_def->right_table = right.first;
            out_def->right_col = right.second;
            if (left_full <= right_full) {
                out_def->key = "join:" + left_full + "=" + right_full;
            } else {
                std::swap(out_def->left_table, out_def->right_table);
                std::swap(out_def->left_col, out_def->right_col);
                out_def->key = "join:" + right_full + "=" + left_full;
            }
            out_def->op = "=";
            return out_def->key;
        }

        if (op == "!=" || op == "<" || op == "<=" || op == ">" || op == ">=" || op_from_slot) {
            out_def->kind = Policy::AtomDef::COL_COL;
            out_def->left_table = left.first;
            out_def->left_col = left.second;
            out_def->right_table = right.first;
            out_def->right_col = right.second;

            auto flip_dir = [](const std::string &o) -> std::string {
                if (o == "<") return ">";
                if (o == "<=") return ">=";
                if (o == ">") return "<";
                if (o == ">=") return "<=";
                return o;
            };

            std::string cop = op;
            
            if (cop == "!=") {
                if (right_full < left_full) {
                    std::swap(out_def->left_table, out_def->right_table);
                    std::swap(out_def->left_col, out_def->right_col);
                    std::swap(left_full, right_full);
                }
            } else if (!op_from_slot && right_full < left_full) {
                std::swap(out_def->left_table, out_def->right_table);
                std::swap(out_def->left_col, out_def->right_col);
                std::swap(left_full, right_full);
                cop = flip_dir(cop);
            }

            out_def->op = cop;
            out_def->key = "colcmp:" + left_full + cop + right_full;
            return out_def->key;
        }

        ereport(ERROR, (errmsg("unsupported column comparison: %s %s %s",
                               left_ident.c_str(), op.c_str(), right_ident.c_str())));
    }

    out_def->kind = Policy::AtomDef::COL_CONST;
    out_def->left_table = left.first;
    out_def->left_col = left.second;
    out_def->op = op;
    policy.const_cols.insert({left.first, left.second});

    bool supported_const_op =
        (op == "=" || op == "!=" ||
         op == "<" || op == "<=" ||
         op == ">" || op == ">=");
    if (!supported_const_op && !op_from_slot) {
        ereport(ERROR, (errmsg("unsupported col-const operator: %s", op.c_str())));
    }

    std::vector<std::string> values;
    for (size_t i = 0; i < tokens.size(); i++) {
        if (tokens[i].type == Token::STRING || tokens[i].type == Token::NUMBER || is_value_slot_token(tokens[i])) {
            values.push_back(normalize_literal(tokens[i]));
            break;
        }
    }
    out_def->values = values;

    std::string key = "const:" + left_full + "|" + op;
    if (!values.empty()) {
        key += "|" + values[0];
    } else {
        key += "|" + join_tokens(tokens);
    }
    out_def->key = key;
    return key;
}

static AstNode *parse_or(const std::vector<Token> &tokens, size_t &idx,
                         const std::string &target_table, Policy &policy);

static AstNode *parse_not(const std::vector<Token> &tokens, size_t &idx,
                          const std::string &target_table, Policy &policy);

static AstNode *parse_atom(const std::vector<Token> &tokens, size_t &idx,
                           const std::string &target_table, Policy &policy) {
    if (idx >= tokens.size()) return nullptr;
    if (tokens[idx].type == Token::LPAREN) {
        idx++;
        AstNode *node = parse_or(tokens, idx, target_table, policy);
        if (idx < tokens.size() && tokens[idx].type == Token::RPAREN) idx++;
        return node;
    }

    std::vector<Token> atom_tokens;
    int depth = 0;
    while (idx < tokens.size()) {
        if (tokens[idx].type == Token::LPAREN) {
            depth++;
        } else if (tokens[idx].type == Token::RPAREN) {
            if (depth == 0) break;
            depth--;
        } else if ((tokens[idx].type == Token::AND || tokens[idx].type == Token::OR) && depth == 0) {
            break;
        }
        atom_tokens.push_back(tokens[idx]);
        idx++;
    }

    if (atom_tokens.size() == 1 && atom_tokens[0].type == Token::IDENT &&
        atom_tokens[0].text == "false")
        return make_false_node();

    Policy::AtomDef def;
    std::string key = canonicalize_atom(atom_tokens, target_table, policy, &def);
    if (!key.empty()) {
        
        
        std::string scoped_key = key + "@p" + std::to_string(policy.line_no);
        def.key = scoped_key;
        policy.atom_keys.insert(scoped_key);
        policy.atoms.push_back(def);
        key = std::move(scoped_key);
    }
    return make_var_node(key);
}

static AstNode *parse_not(const std::vector<Token> &tokens, size_t &idx,
                          const std::string &target_table, Policy &policy) {
    if (idx < tokens.size() && tokens[idx].type == Token::NOT) {
        idx++;
        AstNode *child = parse_not(tokens, idx, target_table, policy);
        return make_unary_node(AstNode::NOT, child);
    }
    if (idx < tokens.size() && tokens[idx].type == Token::EXISTS) {
        ++idx;
        std::vector<std::string> binders;
        while (idx < tokens.size() && tokens[idx].type == Token::IDENT) {
            binders.push_back(tokens[idx++].text);
            if (idx < tokens.size() && tokens[idx].type == Token::COMMA) ++idx;
            else break;
        }
        if (idx >= tokens.size() || tokens[idx].type != Token::LPAREN)
            ereport(ERROR, (errmsg("EXISTS group requires a parenthesized predicate body")));
        ++idx;
        AstNode *body = parse_or(tokens, idx, target_table, policy);
        if (!body || idx >= tokens.size() || tokens[idx].type != Token::RPAREN)
            ereport(ERROR, (errmsg("unterminated EXISTS group")));
        ++idx;
        AstNode *node=make_unary_node(AstNode::EXISTS, body);
        node->binders=std::move(binders);
        return node;
    }
    return parse_atom(tokens, idx, target_table, policy);
}

static AstNode *parse_and(const std::vector<Token> &tokens, size_t &idx,
                          const std::string &target_table, Policy &policy) {
    AstNode *left = parse_not(tokens, idx, target_table, policy);
    while (idx < tokens.size() && tokens[idx].type == Token::AND) {
        idx++;
        AstNode *right = parse_not(tokens, idx, target_table, policy);
        left = make_node(AstNode::AND, left, right);
    }
    return left;
}

static AstNode *parse_or(const std::vector<Token> &tokens, size_t &idx,
                         const std::string &target_table, Policy &policy) {
    AstNode *left = parse_and(tokens, idx, target_table, policy);
    while (idx < tokens.size() && tokens[idx].type == Token::OR) {
        idx++;
        AstNode *right = parse_and(tokens, idx, target_table, policy);
        left = make_node(AstNode::OR, left, right);
    }
    return left;
}

static int precedence(const AstNode *node) {
    if (!node) return 0;
    if (node->type == AstNode::OR) return 1;
    if (node->type == AstNode::AND) return 2;
    if (node->type == AstNode::NOT) return 3;
    return 4;
}

static std::string ast_to_string(const AstNode *node) {
    if (!node) return "";
    if (node->type == AstNode::VAR) {
        return "y" + std::to_string(node->var_id);
    }
    if (node->type == AstNode::EXISTS) {
        std::string scope;
        for (auto binder:node->binders) {if(!scope.empty())scope+=",";scope+=binder;}
        return "exists " + scope + " (" + ast_to_string(node->children.at(0)) + ")";
    }
    if (node->type == AstNode::NOT) {
        const AstNode *child = node->children.empty() ? nullptr : node->children[0];
        std::string part = ast_to_string(child);
        if (child && precedence(child) < precedence(node))
            return "not (" + part + ")";
        return "not " + part;
    }
    std::string op = (node->type == AstNode::AND) ? " and " : " or ";
    std::string out;
    for (size_t i = 0; i < node->children.size(); i++) {
        if (i > 0) out += op;
        const AstNode *child = node->children[i];
        std::string part = ast_to_string(child);
        if (precedence(child) < precedence(node)) {
            out += "(" + part + ")";
        } else {
            out += part;
        }
    }
    return out;
}

static std::string ast_to_key_string(const AstNode *node) {
    if (!node) return "";
    if (node->type == AstNode::VAR) {
        if (node->key.empty())
            return "false";
        return node->key;
    }
    if (node->type == AstNode::EXISTS) {
        std::string scope;
        for (auto binder:node->binders) {if(!scope.empty())scope+=",";scope+=binder;}
        return "exists " + scope + " (" + ast_to_key_string(node->children.at(0)) + ")";
    }
    if (node->type == AstNode::NOT) {
        const AstNode *child = node->children.empty() ? nullptr : node->children[0];
        std::string part = ast_to_key_string(child);
        if (child && precedence(child) < precedence(node))
            return "not (" + part + ")";
        return "not " + part;
    }
    std::string op = (node->type == AstNode::AND) ? " and " : " or ";
    std::string out;
    for (size_t i = 0; i < node->children.size(); i++) {
        if (i > 0) out += op;
        const AstNode *child = node->children[i];
        std::string part = ast_to_key_string(child);
        if (precedence(child) < precedence(node))
            out += "(" + part + ")";
        else
            out += part;
    }
    return out;
}

static AstNode *simplify_ast_idempotent(const AstNode *node) {
    if (!node)
        return nullptr;
    if (node->type == AstNode::VAR) {
        if (ast_is_false_node(node))
            return make_false_node();
        AstNode *out = make_var_node(node->key);
        out->var_id = node->var_id;
        return out;
    }
    if (node->type == AstNode::NOT || node->type == AstNode::EXISTS) {
        AstNode *child = node->children.empty() ? nullptr : simplify_ast_idempotent(node->children[0]);
        auto *out=make_unary_node(node->type, child);
        out->binders=node->binders;
        return out;
    }

    auto flatten_same_type = [&](auto &&self, AstNode *cur, AstNode::Type ty,
                                 std::vector<AstNode *> *out) -> void {
        if (!cur || !out)
            return;
        if (cur->type != ty) {
            out->push_back(cur);
            return;
        }
        for (AstNode *ch : cur->children)
            self(self, ch, ty, out);
    };

    std::vector<AstNode *> flat;
    flat.reserve(node->children.size());
    for (const AstNode *child : node->children) {
        AstNode *s = simplify_ast_idempotent(child);
        if (!s)
            continue;
        if (ast_is_false_node(s)) {
            if (node->type == AstNode::AND)
                return make_false_node();
            continue;
        }
        flatten_same_type(flatten_same_type, s, node->type, &flat);
    }
    if (flat.empty())
        return make_false_node();

    std::unordered_set<std::string> seen;
    seen.reserve(flat.size() * 2u + 1u);
    std::vector<AstNode *> uniq;
    uniq.reserve(flat.size());
    for (AstNode *t : flat) {
        std::string k = ast_to_key_string(t);
        if (seen.insert(k).second)
            uniq.push_back(t);
    }
    if (uniq.empty())
        return nullptr;
    if (uniq.size() == 1u)
        return uniq[0];

    AstNode *acc = uniq[0];
    for (size_t i = 1; i < uniq.size(); i++)
        acc = make_node(node->type, acc, uniq[i]);
    return acc;
}

static void ast_to_postfix_tokens(const AstNode *node, std::vector<PolicyAstTokC> &out) {
    if (!node)
        return;
    if (node->type == AstNode::VAR) {
        PolicyAstTokC tok;
        if (ast_is_false_node(node)) {
            tok.kind = POLICY_AST_TOK_FALSE;
            tok.value = 0;
        } else {
            tok.kind = POLICY_AST_TOK_VAR;
            tok.value = node->var_id;
        }
        out.push_back(tok);
        return;
    }
    if (node->type == AstNode::NOT || node->type == AstNode::EXISTS) {
        const auto body_begin=out.size();
        if (node->children.empty()) {
            PolicyAstTokC tok;
            tok.kind = POLICY_AST_TOK_FALSE;
            tok.value = 0;
            out.push_back(tok);
        } else {
            ast_to_postfix_tokens(node->children[0], out);
        }
        PolicyAstTokC op_tok;
        op_tok.kind = node->type == AstNode::NOT ? POLICY_AST_TOK_NOT : POLICY_AST_TOK_EXISTS;
        op_tok.value = 0;
        if(node->type==AstNode::EXISTS)for(auto binder:node->binders){
            std::set<int> ids;
            for(auto i=body_begin;i<out.size();++i)if(out[i].kind==POLICY_AST_TOK_VAR){
                auto atom=g_quantifier_binders.find(out[i].value);
                if(atom!=g_quantifier_binders.end()){
                    auto found=atom->second.find(binder);
                    if(found!=atom->second.end())ids.insert(found->second);
                }
            }
            if(ids.size()!=1)
                ereport(ERROR,(errmsg("unknown quantifier occurrence %s",binder.c_str())));
            PolicyAstTokC bind_tok;bind_tok.kind=8;bind_tok.value=*ids.begin();
            out.push_back(bind_tok);
        }
        out.push_back(op_tok);
        return;
    }
    if (node->children.empty()) {
        return;
    }
    ast_to_postfix_tokens(node->children[0], out);
    for (size_t i = 1; i < node->children.size(); i++) {
        ast_to_postfix_tokens(node->children[i], out);
        PolicyAstTokC op_tok;
        op_tok.kind = (node->type == AstNode::AND) ? POLICY_AST_TOK_AND : POLICY_AST_TOK_OR;
        op_tok.value = 0;
        out.push_back(op_tok);
    }
}

static void assign_var_ids(AstNode *node, const std::map<std::string, int> &mapping) {
    if (!node) return;
    if (node->type == AstNode::VAR) {
        auto it = mapping.find(node->key);
        if (it != mapping.end()) node->var_id = it->second;
        return;
    }
    for (auto *child : node->children) {
        assign_var_ids(child, mapping);
    }
}

static std::vector<Policy> load_policies_from_stream(std::istream &in) {
    std::vector<Policy> policies;
    std::string line;
    int line_no = 0;
    while (std::getline(in, line)) {
        line_no++;
        line = trim(line);
        if (line.empty()) continue;
        auto colon = line.find(':');
        if (colon == std::string::npos) continue;
        std::string left = trim(line.substr(0, colon));
        std::string right = trim(line.substr(colon + 1));
        int policy_id = -1;
        size_t pos = 0;
        while (pos < left.size() && std::isspace(static_cast<unsigned char>(left[pos])))
            pos++;
        size_t id_start = pos;
        while (pos < left.size() && std::isdigit(static_cast<unsigned char>(left[pos])))
            pos++;
        if (pos > id_start) {
            try {
                policy_id = std::stoi(left.substr(id_start, pos - id_start));
            } catch (...) {
                policy_id = -1;
            }
            while (pos < left.size() &&
                   (left[pos] == '.' || std::isspace(static_cast<unsigned char>(left[pos]))))
                pos++;
            left = left.substr(pos);
        } else {
            left = left.substr(id_start);
        }
        left = to_lower(trim(left));
        if (left.empty() || right.empty()) continue;

        Policy pol;
        pol.policy_id = policy_id;
        pol.target = left;
        pol.expr = right;
        pol.line_no = line_no;
        pol.referenced_tables.insert(left);
        auto tokens = tokenize_expr(right);
        if (g_eval_debug) {
            std::string out;
            for (size_t ti = 0; ti < tokens.size(); ti++) {
                if (ti > 0) out += " ";
                out += std::string(token_type_name(tokens[ti].type)) + ":" + tokens[ti].text;
            }
            elog(NOTICE, "policy_eval: target=%s tokens=%s", pol.target.c_str(), out.c_str());
        }
        size_t idx = 0;
        pol.ast = parse_or(tokens, idx, pol.target, pol);
        policies.push_back(pol);
    }
    return policies;
}

static std::vector<Policy> load_policies(const std::string &path) {
    std::vector<Policy> policies;
    std::ifstream in(path);
    if (!in.is_open()) {
        return policies;
    }
    return load_policies_from_stream(in);
}

static std::vector<Policy> load_policies_from_text(const std::string &text) {
    std::istringstream in(text);
    return load_policies_from_stream(in);
}

static void collect_ast_keys(const AstNode *node, std::set<std::string> &keys) {
    if (!node) return;
    if (node->type == AstNode::VAR) {
        if (!node->key.empty())
            keys.insert(node->key);
        return;
    }
    for (const auto *child : node->children)
        collect_ast_keys(child, keys);
}

static std::string collapse_sql_for_match(const std::string &sql) {
    std::string out;
    out.reserve(sql.size());
    bool in_space = false;
    for (char ch : sql) {
        if (std::isspace((unsigned char)ch)) {
            in_space = true;
            continue;
        }
        if (in_space && !out.empty())
            out.push_back(' ');
        in_space = false;
        out.push_back((char)std::tolower((unsigned char)ch));
    }
    while (!out.empty() && std::isspace((unsigned char)out.back()))
        out.pop_back();
    while (!out.empty() && out.back() == ';')
        out.pop_back();
    while (!out.empty() && std::isspace((unsigned char)out.back()))
        out.pop_back();
    return out;
}

static std::string normalize_query_id_key(const std::string &raw) {
    std::string q = trim(raw);
    if (q.empty())
        return q;
    if ((q[0] == 'q' || q[0] == 'Q') && q.size() > 1u) {
        bool digits = true;
        for (size_t i = 1; i < q.size(); i++) {
            if (!std::isdigit((unsigned char)q[i])) {
                digits = false;
                break;
            }
        }
        if (digits)
            q.erase(0, 1);
    }
    return q;
}

static std::map<std::string, std::string> load_query_map(const std::string &path) {
    std::map<std::string, std::string> out;
    std::map<std::string, std::string> first_qid_by_sql;
    std::ifstream in(path);
    if (!in.is_open())
        return out;
    std::string line;
    int ordinal = 0;
    while (std::getline(in, line)) {
        line = trim(line);
        if (line.empty() || line[0] == '#')
            continue;
        ordinal++;
        std::string qid;
        std::string sql;
        size_t colon = line.find(':');
        if (colon == std::string::npos) {
            qid = std::to_string(ordinal);
            sql = line;
        } else {
            qid = trim(line.substr(0, colon));
            sql = trim(line.substr(colon + 1));
        }
        if (qid.empty() || sql.empty())
            continue;
        std::string norm_qid = normalize_query_id_key(qid);
        if (norm_qid.empty())
            norm_qid = qid;
        std::string norm_sql = collapse_sql_for_match(sql);
        auto dup_qid = out.find(norm_qid);
        if (dup_qid != out.end()) {
            ereport(ERROR,
                    (errmsg("policy_eval: duplicate query id in query file"),
                     errdetail("query id %s appears more than once in %s", norm_qid.c_str(), path.c_str())));
        }
        auto dup_sql = first_qid_by_sql.find(norm_sql);
        if (dup_sql != first_qid_by_sql.end()) {
            ereport(ERROR,
                    (errmsg("policy_eval: duplicate SQL text in query file"),
                     errdetail("query ids %s and %s normalize to the same SQL in %s",
                               dup_sql->second.c_str(), norm_qid.c_str(), path.c_str())));
        }
        first_qid_by_sql[norm_sql] = norm_qid;
        out[norm_qid] = norm_sql;
    }
    return out;
}

static std::map<std::string, std::map<std::string, std::string>>
load_binding_map(const std::string &path) {
    std::map<std::string, std::map<std::string, std::string>> out;
    std::ifstream in(path);
    if (!in.is_open())
        return out;
    std::string line;
    std::string current_query;
    while (std::getline(in, line)) {
        line = trim(line);
        if (line.empty() || line[0] == '#')
            continue;
        if (line.rfind("query:", 0) == 0) {
            current_query = normalize_query_id_key(trim(line.substr(6)));
            continue;
        }
        if (line.front() == '[' && line.back() == ']') {
            current_query = normalize_query_id_key(trim(line.substr(1, line.size() - 2)));
            continue;
        }
        size_t eq = line.find('=');
        if (eq == std::string::npos || current_query.empty())
            continue;
        std::string key = to_lower(trim(line.substr(0, eq)));
        std::string value = trim(line.substr(eq + 1));
        if (key.empty() || value.empty())
            continue;
        if (out[current_query].find(key) != out[current_query].end()) {
            ereport(ERROR,
                    (errmsg("policy_eval: duplicate binding key"),
                     errdetail("query %s has duplicate binding for %s in %s",
                               current_query.c_str(), key.c_str(), path.c_str())));
        }
        out[current_query][key] = value;
    }
    return out;
}

static std::string normalize_binding_op(const std::string &raw) {
    std::string op = to_lower(trim(raw));
    if (op == "eq" || op == "=") return "=";
    if (op == "ne" || op == "!=" || op == "<>") return "!=";
    if (op == "lt" || op == "<") return "<";
    if (op == "le" || op == "<=") return "<=";
    if (op == "gt" || op == ">") return ">";
    if (op == "ge" || op == ">=") return ">=";
    ereport(ERROR, (errmsg("policy_eval: unsupported binding operator: %s", raw.c_str())));
}

static std::string bind_expr_for_policy(const std::string &expr,
                                        int policy_id,
                                        const std::map<std::string, std::string> &bindings) {
    std::string out;
    out.reserve(expr.size() + 64u);
    for (size_t i = 0; i < expr.size();) {
        char c = expr[i];
        if (c == '@' || c == '$') {
            size_t j = i + 1;
            while (j < expr.size() && is_slot_char(expr[j])) j++;
            std::string slot = to_lower(expr.substr(i + 1, j - (i + 1)));
            std::string key = std::to_string(policy_id) + "." + slot;
            auto it = bindings.find(key);
            if (it == bindings.end()) {
                ereport(ERROR,
                        (errmsg("policy_eval: missing binding for slot %s in policy %d",
                                slot.c_str(), policy_id)));
            }
            if (slot.rfind("op", 0) == 0)
                out += normalize_binding_op(it->second);
            else
                out += it->second;
            i = j;
            continue;
        }
        out.push_back(c);
        i++;
    }
    return out;
}

struct StructuredTemplatePolicy {
    int policy_id = 0;
    std::string target;
    std::map<std::string, std::string> occurrences;
    std::map<std::string, std::string> atoms;
    std::map<std::string, std::string> scoped_atoms;
};

static bool is_template_ident_start(char c) {
    return std::isalpha((unsigned char)c) || c == '_';
}

static bool is_template_ident_char(char c) {
    return std::isalnum((unsigned char)c) || c == '_';
}

static bool starts_with_ci(const std::string &s, const char *prefix) {
    std::string lhs = to_lower(trim(s));
    std::string rhs = to_lower(prefix ? prefix : "");
    return lhs.rfind(rhs, 0) == 0;
}

static std::vector<std::string> split_template_csv(const std::string &s) {
    std::vector<std::string> out;
    std::string cur;
    cur.reserve(s.size());
    int paren_depth = 0;
    for (char ch : s) {
        if (ch == '(') paren_depth++;
        if (ch == ')' && paren_depth > 0) paren_depth--;
        if (ch == ',' && paren_depth == 0) {
            std::string part = trim(cur);
            if (!part.empty())
                out.push_back(part);
            cur.clear();
            continue;
        }
        cur.push_back(ch);
    }
    std::string tail = trim(cur);
    if (!tail.empty())
        out.push_back(tail);
    return out;
}

static std::string expand_occurrence_aliases(const std::string &expr,
                                             const std::map<std::string, std::string> &occurrences) {
    std::string out;
    out.reserve(expr.size() + 32u);
    for (size_t i = 0; i < expr.size();) {
        char c = expr[i];
        if (!is_template_ident_start(c)) {
            out.push_back(c);
            i++;
            continue;
        }
        size_t j = i + 1;
        while (j < expr.size() && is_template_ident_char(expr[j])) j++;
        std::string ident = expr.substr(i, j - i);
        if (j < expr.size() && expr[j] == '.') {
            size_t k = j + 1;
            while (k < expr.size() && is_template_ident_char(expr[k])) k++;
            std::string alias = to_lower(ident);
            auto it = occurrences.find(alias);
            if (it != occurrences.end()) {
                out += it->second;
                out += expr.substr(j, k - j);
                i = k;
                continue;
            }
        }
        out += ident;
        i = j;
    }
    return out;
}

static std::string render_structured_ast_expr(const std::string &ast,
                                              const std::map<std::string, std::string> &bound_atoms) {
    std::string out;
    out.reserve(ast.size() + 64u);
    for (size_t i = 0; i < ast.size();) {
        char c = ast[i];
        if (!is_template_ident_start(c)) {
            out.push_back(c);
            i++;
            continue;
        }
        size_t j = i + 1;
        while (j < ast.size() && is_template_ident_char(ast[j])) j++;
        std::string ident = ast.substr(i, j - i);
        auto it = bound_atoms.find(to_lower(ident));
        if (it != bound_atoms.end()) {
            out.push_back('(');
            out += it->second;
            out.push_back(')');
        } else {
            out += ident;
        }
        i = j;
    }
    return out;
}

static bool parse_structured_template_text(const std::string &text,
                                           std::vector<StructuredTemplatePolicy> *out) {
    if (!out) return false;
    out->clear();
    std::istringstream in(text);
    std::string line;
    StructuredTemplatePolicy current;
    bool in_policy = false;
    bool saw_structured = false;

    auto finish_current = [&]() {
        if (!in_policy) return;
        if (current.policy_id <= 0 || current.target.empty() || current.atoms.empty()) {
            ereport(ERROR,
                    (errmsg("policy_eval: malformed structured policy template"),
                     errdetail("Each policy block must define policy id, target, and atoms.")));
        }
        out->push_back(current);
        current = StructuredTemplatePolicy{};
        in_policy = false;
    };

    while (std::getline(in, line)) {
        std::string trimmed = trim(line);
        if (trimmed.empty() || trimmed[0] == '#')
            continue;
        size_t leading_colon = trimmed.find(':');
        if (!in_policy &&
            leading_colon != std::string::npos &&
            leading_colon > 0 &&
            std::all_of(trimmed.begin(), trimmed.begin() + (std::ptrdiff_t)leading_colon,
                        [](char c) { return std::isdigit((unsigned char)c) || std::isspace((unsigned char)c); })) {
            std::string lhs = trim(trimmed.substr(0, leading_colon));
            int pid = std::atoi(lhs.c_str());
            if (pid > 0) {
                std::vector<std::string> items = split_template_csv(trimmed.substr(leading_colon + 1));
                if (!items.empty()) {
                    saw_structured = true;
                    StructuredTemplatePolicy pol;
                    pol.policy_id = pid;
                    pol.target = to_lower(trim(items.front()));
                    if (pol.target.empty()) {
                        ereport(ERROR,
                                (errmsg("policy_eval: malformed structured policy target"),
                                 errdetail("Line: %s", trimmed.c_str())));
                    }
                    for (size_t i = 1; i < items.size(); i++) {
                        const std::string &item = items[i];
                        if (starts_with_ci(item, "occ ")) {
                            size_t colon = item.find(':');
                            if (colon == std::string::npos) {
                                ereport(ERROR,
                                        (errmsg("policy_eval: malformed occurrence declaration"),
                                         errdetail("Line: %s", item.c_str())));
                            }
                            std::string alias = to_lower(trim(item.substr(4, colon - 4)));
                            std::string table = to_lower(trim(item.substr(colon + 1)));
                            if (alias.empty() || table.empty()) {
                                ereport(ERROR,
                                        (errmsg("policy_eval: malformed occurrence declaration"),
                                         errdetail("Line: %s", item.c_str())));
                            }
                            pol.occurrences[alias] = table;
                            continue;
                        }
                        if (starts_with_ci(item, "atom ")) {
                            size_t colon = item.find(':');
                            if (colon == std::string::npos) {
                                ereport(ERROR,
                                        (errmsg("policy_eval: malformed atom declaration"),
                                         errdetail("Line: %s", item.c_str())));
                            }
                            std::string atom_id = to_lower(trim(item.substr(5, colon - 5)));
                            std::string expr = trim(item.substr(colon + 1));
                            if (atom_id.empty() || expr.empty()) {
                                ereport(ERROR,
                                        (errmsg("policy_eval: malformed atom declaration"),
                                         errdetail("Line: %s", item.c_str())));
                            }
                            pol.atoms[atom_id] = expand_occurrence_aliases(expr, pol.occurrences);
                            continue;
                        }
                        ereport(ERROR,
                                (errmsg("policy_eval: unsupported structured template item"),
                                 errdetail("Item: %s", item.c_str())));
                    }
                    if (pol.atoms.empty()) {
                        ereport(ERROR,
                                (errmsg("policy_eval: malformed structured policy template"),
                                 errdetail("Structured template line must define at least one atom: %s",
                                           trimmed.c_str())));
                    }
                    out->push_back(pol);
                    continue;
                }
            }
        }
        if (starts_with_ci(trimmed, "policy ")) {
            saw_structured = true;
            finish_current();
            std::string rhs = trim(trimmed.substr(7));
            int pid = std::atoi(rhs.c_str());
            if (pid <= 0) {
                ereport(ERROR,
                        (errmsg("policy_eval: invalid structured policy id"),
                         errdetail("Line: %s", trimmed.c_str())));
            }
            in_policy = true;
            current.policy_id = pid;
            continue;
        }
        if (!in_policy)
            return false;
        if (starts_with_ci(trimmed, "target:")) {
            current.target = to_lower(trim(trimmed.substr(7)));
            continue;
        }
        if (starts_with_ci(trimmed, "occ ")) {
            size_t colon = trimmed.find(':');
            if (colon == std::string::npos)
                ereport(ERROR,
                        (errmsg("policy_eval: malformed occurrence declaration"),
                         errdetail("Line: %s", trimmed.c_str())));
            std::string alias = to_lower(trim(trimmed.substr(4, colon - 4)));
            std::string table = to_lower(trim(trimmed.substr(colon + 1)));
            if (alias.empty() || table.empty())
                ereport(ERROR,
                        (errmsg("policy_eval: malformed occurrence declaration"),
                         errdetail("Line: %s", trimmed.c_str())));
            current.occurrences[alias] = table;
            continue;
        }
        if (starts_with_ci(trimmed, "atom ")) {
            size_t colon = trimmed.find(':');
            if (colon == std::string::npos)
                ereport(ERROR,
                        (errmsg("policy_eval: malformed atom declaration"),
                         errdetail("Line: %s", trimmed.c_str())));
            std::string atom_id = to_lower(trim(trimmed.substr(5, colon - 5)));
            std::string expr = trim(trimmed.substr(colon + 1));
            if (atom_id.empty() || expr.empty())
                ereport(ERROR,
                        (errmsg("policy_eval: malformed atom declaration"),
                         errdetail("Line: %s", trimmed.c_str())));
            current.atoms[atom_id] = expand_occurrence_aliases(expr, current.occurrences);
            current.scoped_atoms[atom_id] = expr;
            continue;
        }
        if (to_lower(trimmed) == "end") {
            finish_current();
            continue;
        }
        ereport(ERROR,
                (errmsg("policy_eval: unsupported structured template line"),
                 errdetail("Line: %s", trimmed.c_str())));
    }
    finish_current();
    return saw_structured;
}

static std::string bind_policy_template_text(const std::string &template_text,
                                             const std::map<std::string, std::string> &bindings) {
    std::vector<StructuredTemplatePolicy> structured;
    if (parse_structured_template_text(template_text, &structured)) {
        std::ostringstream out;
        for (const StructuredTemplatePolicy &pol : structured) {
            std::string ast_key = std::to_string(pol.policy_id) + ".ast";
            auto it_ast = bindings.find(ast_key);
            if (it_ast == bindings.end())
                continue;
            if (to_lower(trim(it_ast->second)) == "false")
                continue;
            const auto ast_tokens=tokenize_expr(it_ast->second);
            const bool scoped=std::any_of(ast_tokens.begin(),ast_tokens.end(),
                [](const Token &t){return t.type==Token::EXISTS;});
            if(scoped)for(const auto &occ:pol.occurrences)
                out << "# scoped_occ " << occ.first << " " << occ.second << "\n";
            std::map<std::string, std::string> bound_atoms;
            for (const auto &kv : (scoped?pol.scoped_atoms:pol.atoms)) {
                bound_atoms[kv.first] = bind_expr_for_policy(kv.second, pol.policy_id, bindings);
            }
            std::string expr = render_structured_ast_expr(it_ast->second, bound_atoms);
            out << pol.policy_id << ". " << pol.target << ": " << expr << "\n";
        }
        return out.str();
    }

    std::istringstream in(template_text);
    std::ostringstream out;
    std::string line;
    while (std::getline(in, line)) {
        std::string raw = line;
        std::string trimmed = trim(raw);
        if (trimmed.empty() || trimmed[0] == '#') {
            out << raw << "\n";
            continue;
        }
        size_t colon = raw.find(':');
        if (colon == std::string::npos) {
            out << raw << "\n";
            continue;
        }
        std::string left = trim(raw.substr(0, colon));
        std::string right = trim(raw.substr(colon + 1));
        size_t pos = 0;
        while (pos < left.size() && std::isdigit((unsigned char)left[pos])) pos++;
        if (pos == 0) {
            out << raw << "\n";
            continue;
        }
        int policy_id = std::atoi(left.substr(0, pos).c_str());
        if (policy_id <= 0) {
            out << raw << "\n";
            continue;
        }
        out << left << ": " << bind_expr_for_policy(right, policy_id, bindings) << "\n";
    }
    return out.str();
}

struct DirectPolicyAstSet {
    AstNode *perm = nullptr;
    AstNode *rest = nullptr;
    AstNode *final = nullptr;
    int perm_count = 0;
    int rest_count = 0;
};

struct DirectAtomInfo {
    Policy::AtomDef atom;
    int line_no = -1;
    std::string policy_target;
};

struct ExpandedAtomDef {
    Policy::AtomDef atom;
    std::string key;
    std::string lhs_node_key;
    std::string rhs_node_key;
    std::string target_node_key;
    std::string enforcement_target;
    std::string occurrence_path;
    int source_line = -1;
};

static std::string canonical_expanded_atom_key(const Policy::AtomDef &atom,
                                               const std::string &lhs_node_key,
                                               const std::string &rhs_node_key,
                                               const std::string &target_node_key) {
    std::ostringstream oss;
    oss << "kind=" << (int)atom.kind
        << "|lhs=" << atom.left_table << "." << atom.left_col
        << "@ln=" << lhs_node_key
        << "|op=" << atom.op
        << "|target=" << target_node_key;
    if (atom.kind == Policy::AtomDef::JOIN_EQ || atom.kind == Policy::AtomDef::COL_COL) {
        oss << "|rhs=" << atom.right_table << "." << atom.right_col
            << "@rn=" << rhs_node_key;
    } else {
        oss << "|vals=";
        for (std::size_t i = 0; i < atom.values.size(); ++i) {
            if (i) oss << ",";
            oss << atom.values[i];
        }
    }
    return oss.str();
}

struct TableOccurrenceCtx {
    std::string current_table;
    std::string root_node_key;
    std::string enforcement_target;
    std::string occurrence_path;
    std::map<std::string, std::string> *shared_witness_node_key_by_occurrence = nullptr;
    std::map<std::string, AstNode *> *shared_witness_effective_ast_by_occurrence = nullptr;
    std::map<std::string, std::string> used_witness_tables_by_occurrence;
};

class PolicyAstExpander {
public:
    PolicyAstExpander(const std::map<std::string, DirectPolicyAstSet> *direct_asts,
                      const std::map<std::string, std::vector<const Policy *>> *direct_policies_by_target,
                      const std::map<std::string, std::set<std::string>> *direct_policy_deps,
                      const std::map<std::string, DirectAtomInfo> *direct_atom_info,
                      const std::set<std::string> *policy_tables,
                      std::map<std::string, ExpandedAtomDef> *expanded_atoms,
                      uint64 *atom_instance_seq)
        : direct_asts_(direct_asts),
          direct_policies_by_target_(direct_policies_by_target),
          direct_policy_deps_(direct_policy_deps),
          direct_atom_info_(direct_atom_info),
          policy_tables_(policy_tables),
          expanded_atoms_(expanded_atoms),
          atom_instance_seq_(atom_instance_seq)
    {}

    enum class ExpandMode {
        kPermOnly,
        kRestOnly,
        kFinal,
    };

    AstNode *expand_table_effective(const std::string &table,
                                    const std::string &root_node_key,
                                    const std::string &occurrence_path,
                                    const std::string &enforcement_target,
                                    std::vector<std::string> *stack,
                                    std::map<std::string, std::string> *shared_node_keys,
                                    std::map<std::string, AstNode *> *shared_effective_asts)
    {
        return expand_table_mode(table,
                                 root_node_key,
                                 occurrence_path,
                                 enforcement_target,
                                 ExpandMode::kFinal,
                                 stack,
                                 shared_node_keys,
                                 shared_effective_asts);
    }

    AstNode *expand_table_mode(const std::string &table,
                               const std::string &root_node_key,
                               const std::string &occurrence_path,
                               const std::string &enforcement_target,
                               ExpandMode mode,
                               std::vector<std::string> *stack,
                               std::map<std::string, std::string> *shared_node_keys,
                               std::map<std::string, AstNode *> *shared_effective_asts)
    {
        if (!stack)
            return nullptr;
        auto pit = direct_policies_by_target_ ? direct_policies_by_target_->find(table)
                                              : direct_policies_by_target_->end();
        if (!direct_policies_by_target_ || pit == direct_policies_by_target_->end())
            return nullptr;

        AstNode *perm = nullptr;
        AstNode *rest = nullptr;
        int perm_count = 0;

        for (const Policy *pol : pit->second) {
            if (!pol || !pol->ast)
                continue;
            




            bool permissive = true;
            if (mode == ExpandMode::kPermOnly && !permissive)
                continue;
            if (mode == ExpandMode::kRestOnly && permissive)
                continue;

            std::map<std::string, std::string> local_clause_node_keys;
            std::map<std::string, AstNode *> local_clause_witness_asts;
            std::map<std::string, std::string> *node_keys =
                shared_node_keys ? shared_node_keys : &local_clause_node_keys;
            std::map<std::string, AstNode *> *witness_asts =
                shared_effective_asts ? shared_effective_asts : &local_clause_witness_asts;
            AstNode *clause = expand_clause_occurrence(pol->ast,
                                                       table,
                                                       root_node_key,
                                                       occurrence_path,
                                                       enforcement_target,
                                                       stack,
                                                       node_keys,
                                                       witness_asts);
            if (!clause)
                continue;

            if (permissive) {
                perm_count++;
                perm = perm ? make_node(AstNode::OR, perm, clause) : clause;
            } else {
                rest = rest ? make_node(AstNode::AND, rest, clause) : clause;
            }
        }

        if (mode == ExpandMode::kPermOnly)
            return simplify_ast_idempotent(perm);
        if (mode == ExpandMode::kRestOnly)
            return simplify_ast_idempotent(rest);

        if (perm_count == 0)
            return make_false_node();
        AstNode *out = perm;
        if (rest)
            out = make_node(AstNode::AND, out, rest);
        return simplify_ast_idempotent(out);
    }

    AstNode *expand_clause_occurrence(const AstNode *root,
                                      const std::string &current_table,
                                      const std::string &root_node_key,
                                      const std::string &occurrence_path,
                                      const std::string &enforcement_target,
                                      std::vector<std::string> *stack,
                                      std::map<std::string, std::string> *shared_node_keys,
                                      std::map<std::string, AstNode *> *shared_effective_asts)
    {
        if (!root || !stack)
            return nullptr;
        for (const std::string &s : *stack) {
            if (s == current_table) {
                ereport(ERROR,
                        (errmsg("policy_eval: cycle detected during recursive policy expansion at table=%s",
                                current_table.c_str())));
            }
        }
        stack->push_back(current_table);
        TableOccurrenceCtx ctx;
        ctx.current_table = current_table;
        ctx.root_node_key = root_node_key;
        ctx.enforcement_target = enforcement_target;
        ctx.occurrence_path = occurrence_path;
        ctx.shared_witness_node_key_by_occurrence = shared_node_keys;
        ctx.shared_witness_effective_ast_by_occurrence = shared_effective_asts;
        AstNode *out = expand_node(root, &ctx, stack);
        stack->pop_back();
        return simplify_ast_idempotent(out);
    }

private:
    bool table_has_direct_policies(const std::string &table_name) const
    {
        if (!direct_policies_by_target_ || table_name.empty())
            return false;
        auto it = direct_policies_by_target_->find(table_name);
        return it != direct_policies_by_target_->end() && !it->second.empty();
    }

    std::string witness_occurrence_path(const TableOccurrenceCtx *ctx,
                                        const std::string &table_name) const
    {
        if (!ctx || table_name.empty())
            return std::string();
        if (table_name == ctx->current_table)
            return ctx->occurrence_path;
        if (table_has_direct_policies(table_name))
            return "target:" + table_name;
        return ctx->occurrence_path + "|w:" + ctx->current_table + "->" + table_name;
    }

    std::string witness_node_key(TableOccurrenceCtx *ctx, const std::string &table_name)
    {
        if (!ctx || table_name.empty())
            return std::string();
        if (table_name == ctx->current_table)
            return ctx->root_node_key;
        if (table_has_direct_policies(table_name))
            return "target:" + table_name;
        std::string occ_path = witness_occurrence_path(ctx, table_name);
        if (ctx->shared_witness_node_key_by_occurrence) {
            auto it = ctx->shared_witness_node_key_by_occurrence->find(occ_path);
            if (it != ctx->shared_witness_node_key_by_occurrence->end())
                return it->second;
        }
        std::string key = "occ:" + occ_path;
        if (ctx->shared_witness_node_key_by_occurrence)
            (*ctx->shared_witness_node_key_by_occurrence)[occ_path] = key;
        return key;
    }

    AstNode *expand_node(const AstNode *node,
                         TableOccurrenceCtx *ctx,
                         std::vector<std::string> *stack)
    {
        if (!node || !ctx || !stack)
            return nullptr;

        if (node->type == AstNode::VAR) {
            if (node->key.empty())
                return make_false_node();
            auto ait = direct_atom_info_ ? direct_atom_info_->find(node->key) : direct_atom_info_->end();
            if (!direct_atom_info_ || ait == direct_atom_info_->end()) {
                AstNode *fallback = make_var_node(node->key);
                fallback->var_id = node->var_id;
                return fallback;
            }

            const DirectAtomInfo &src = ait->second;
            const Policy::AtomDef &base = src.atom;
            std::vector<std::pair<std::string, std::string>> witness_refs;
            auto record_witness_table = [&](const std::string &table_name) {
                if (!ctx || table_name.empty() || table_name == ctx->current_table)
                    return;
                auto pit = direct_policies_by_target_ ? direct_policies_by_target_->find(table_name)
                                                      : direct_policies_by_target_->end();
                if (!direct_policies_by_target_ || pit == direct_policies_by_target_->end())
                    return;
                std::string occ = witness_occurrence_path(ctx, table_name);
                for (const auto &existing : witness_refs) {
                    if (existing.first == occ && existing.second == table_name)
                        return;
                }
                witness_refs.push_back({occ, table_name});
            };
            record_witness_table(base.left_table);
            if (base.kind == Policy::AtomDef::JOIN_EQ || base.kind == Policy::AtomDef::COL_COL)
                record_witness_table(base.right_table);

            ExpandedAtomDef ex;
            ex.atom = base;
            ex.enforcement_target = ctx->enforcement_target;
            ex.occurrence_path = ctx->occurrence_path;
            ex.source_line = src.line_no;
            ex.target_node_key = "target:" + ctx->enforcement_target;
            ex.lhs_node_key = witness_node_key(ctx, base.left_table);
            if (base.kind == Policy::AtomDef::JOIN_EQ || base.kind == Policy::AtomDef::COL_COL)
                ex.rhs_node_key = witness_node_key(ctx, base.right_table);
            std::string inst_key = canonical_expanded_atom_key(base,
                                                               ex.lhs_node_key,
                                                               ex.rhs_node_key,
                                                               ex.target_node_key);
            ex.atom.key = inst_key;
            ex.key = inst_key;
            if (expanded_atoms_) {
                auto it_existing = expanded_atoms_->find(inst_key);
                if (it_existing == expanded_atoms_->end())
                    (*expanded_atoms_)[inst_key] = ex;
            }

            if (g_eval_debug) {
                elog(NOTICE,
                     "policy_eval: rebind atom=%s src=%s line=%d current=%s occ=%s lhs_node=%s rhs_node=%s target_node=%s",
                     inst_key.c_str(),
                     base.key.c_str(),
                     src.line_no,
                     ctx->current_table.c_str(),
                     ctx->occurrence_path.c_str(),
                     ex.lhs_node_key.empty() ? "<none>" : ex.lhs_node_key.c_str(),
                     ex.rhs_node_key.empty() ? "<none>" : ex.rhs_node_key.c_str(),
                     ex.target_node_key.c_str());
            }

            AstNode *out = make_var_node(inst_key);
            for (const auto &ref : witness_refs) {
                const std::string &w_occ = ref.first;
                const std::string &wtable = ref.second;
                AstNode *witness_ast = nullptr;
                if (ctx->shared_witness_effective_ast_by_occurrence) {
                    auto it = ctx->shared_witness_effective_ast_by_occurrence->find(w_occ);
                    if (it != ctx->shared_witness_effective_ast_by_occurrence->end())
                        witness_ast = it->second;
                }
                if (!witness_ast) {
                    std::string w_root = witness_node_key(ctx, wtable);
                    witness_ast = expand_table_effective(wtable,
                                                         w_root,
                                                         w_occ,
                                                         ctx->enforcement_target,
                                                         stack,
                                                         ctx->shared_witness_node_key_by_occurrence,
                                                         ctx->shared_witness_effective_ast_by_occurrence);
                    if (ctx->shared_witness_effective_ast_by_occurrence)
                        (*ctx->shared_witness_effective_ast_by_occurrence)[w_occ] = witness_ast;
                }
                if (witness_ast)
                    out = make_node(AstNode::AND, out, witness_ast);
            }
            return simplify_ast_idempotent(out);
        }

        if (node->children.empty())
            return nullptr;
        if (node->type == AstNode::NOT || node->type == AstNode::EXISTS) {
            AstNode *child = expand_node(node->children[0], ctx, stack);
            auto *out=make_unary_node(node->type, child);
            out->binders=node->binders;
            return simplify_ast_idempotent(out);
        }
        AstNode *acc = expand_node(node->children[0], ctx, stack);
        for (size_t i = 1; i < node->children.size(); i++) {
            AstNode *rhs = expand_node(node->children[i], ctx, stack);
            acc = make_node(node->type, acc, rhs);
        }
        return acc;
    }

    const std::map<std::string, DirectPolicyAstSet> *direct_asts_ = nullptr;
    const std::map<std::string, std::vector<const Policy *>> *direct_policies_by_target_ = nullptr;
    const std::map<std::string, std::set<std::string>> *direct_policy_deps_ = nullptr;
    const std::map<std::string, DirectAtomInfo> *direct_atom_info_ = nullptr;
    const std::set<std::string> *policy_tables_ = nullptr;
    std::map<std::string, ExpandedAtomDef> *expanded_atoms_ = nullptr;
    uint64 *atom_instance_seq_ = nullptr;
};

} 

static PolicyEvalResultC *evaluate_policies_internal(const char *policy_source,
                                                     bool source_is_text,
                                                     char **scanned_tables,
                                                     int n_scanned,
                                                     bool default_all_targets) {
    std::string source = policy_source ? policy_source : "";
    g_quantifier_binders.clear();
    std::map<std::string,std::string> scoped_occurrences;
    if(source_is_text){
        std::istringstream lines(source);std::string line;
        while(std::getline(lines,line))if(line.rfind("# scoped_occ ",0)==0){
            std::istringstream fields(line.substr(13));std::string alias,physical,extra;
            if(!(fields>>alias>>physical) || fields>>extra)
                ereport(ERROR,(errmsg("malformed scoped occurrence metadata")));
            auto inserted=scoped_occurrences.emplace(alias,physical);
            if(!inserted.second && inserted.first->second!=physical)
                ereport(ERROR,(errmsg("conflicting scoped occurrence metadata")));
        }
    }
    g_eval_debug = eval_debug_enabled();
    bool dump_policy_ast = env_flag_enabled("CF_DUMP_POLICY_AST") || g_eval_debug;
    NodeStore store;
    g_node_store = &store;
    auto policies = source_is_text ? load_policies_from_text(source) : load_policies(source);

    auto join_set = [](const std::set<std::string> &s) {
        std::string out;
        for (const auto &v : s) {
            if (!out.empty()) out += ", ";
            out += v;
        }
        return out;
    };
    auto join_vec = [](const std::vector<std::string> &v) {
        std::string out;
        for (const auto &item : v) {
            if (!out.empty()) out += ", ";
            out += item;
        }
        return out;
    };

    std::map<std::string, std::vector<size_t>> policies_by_target;
    std::set<std::string> policy_tables;
    std::set<std::string> known_tables;
    for (size_t i = 0; i < policies.size(); i++) {
        if (policies[i].target.empty())
            continue;
        policies_by_target[policies[i].target].push_back(i);
        policy_tables.insert(policies[i].target);
        known_tables.insert(policies[i].target);
        known_tables.insert(policies[i].referenced_tables.begin(),
                            policies[i].referenced_tables.end());
    }

    std::vector<std::string> scanned_list;
    std::set<std::string> scanned_set;
    for (int i = 0; i < n_scanned; i++) {
        if (!scanned_tables || !scanned_tables[i]) continue;
        std::string t = to_lower(scanned_tables[i]);
        if (t.empty()) continue;
        if (scanned_set.insert(t).second)
            scanned_list.push_back(t);
    }
    if (scanned_set.empty() && default_all_targets) {
        scanned_set = policy_tables;
        scanned_list.assign(policy_tables.begin(), policy_tables.end());
    }

    std::set<std::string> enforcement_targets;
    for (const auto &t : scanned_set) {
        if (policy_tables.find(t) != policy_tables.end())
            enforcement_targets.insert(t);
    }

    std::map<std::string, DirectPolicyAstSet> direct_asts;
    int total_perm_policies = 0;
    int total_rest_policies = 0;
    for (const auto &tbl : policy_tables) {
        DirectPolicyAstSet ds;
        auto pit = policies_by_target.find(tbl);
        if (pit == policies_by_target.end()) {
            direct_asts[tbl] = ds;
            continue;
        }
        for (size_t idx : pit->second) {
            const Policy &pol = policies[idx];
            if (!pol.ast)
                continue;
            








            bool permissive = true;
            if (permissive) {
                ds.perm_count++;
                total_perm_policies++;
                if (!ds.perm)
                    ds.perm = pol.ast;
                else
                    ds.perm = make_node(AstNode::OR, ds.perm, pol.ast);
            } else {
                ds.rest_count++;
                total_rest_policies++;
                if (!ds.rest)
                    ds.rest = pol.ast;
                else
                    ds.rest = make_node(AstNode::AND, ds.rest, pol.ast);
            }
        }
        if (ds.perm_count == 0)
            ds.final = make_false_node();
        else if (!ds.rest)
            ds.final = ds.perm;
        else
            ds.final = make_node(AstNode::AND, ds.perm, ds.rest);
        direct_asts[tbl] = ds;
    }

    if (g_eval_debug) {
        elog(NOTICE, "policy_eval: query_tables=[%s]", join_set(scanned_set).c_str());
        elog(NOTICE, "policy_eval: policy_tables=[%s]", join_set(policy_tables).c_str());
        elog(NOTICE, "policy_eval: direct_targets=[%s]", join_set(enforcement_targets).c_str());
        elog(NOTICE, "policy_eval: enforcement_targets=[%s]", join_set(enforcement_targets).c_str());
        for (const auto &kv : direct_asts) {
            std::string perm_str = kv.second.perm ? ast_to_key_string(kv.second.perm) : "";
            std::string rest_str = kv.second.rest ? ast_to_key_string(kv.second.rest) : "";
            std::string final_str = kv.second.final ? ast_to_key_string(kv.second.final) : "";
            elog(NOTICE, "policy_eval: direct_ast table=%s perm=%s rest=%s final=%s",
                 kv.first.c_str(), perm_str.c_str(), rest_str.c_str(), final_str.c_str());
        }
    }

    std::map<std::string, int> domain_col_index;
    std::vector<std::string> domain_cols;
    auto add_domain_col = [&](const std::string &key) {
        if (key.empty())
            return;
        if (domain_col_index.emplace(key, (int)domain_cols.size()).second)
            domain_cols.push_back(key);
    };
    for (const auto &pol : policies) {
        for (const auto &atom : pol.atoms) {
            add_domain_col(atom.left_table + "." + atom.left_col);
            if (atom.kind == Policy::AtomDef::JOIN_EQ || atom.kind == Policy::AtomDef::COL_COL)
                add_domain_col(atom.right_table + "." + atom.right_col);
        }
    }

    std::vector<int> parent(domain_cols.size(), 0);
    for (size_t i = 0; i < domain_cols.size(); i++)
        parent[i] = (int)i;
    std::function<int(int)> uf_find = [&](int x) -> int {
        while (parent[x] != x) {
            parent[x] = parent[parent[x]];
            x = parent[x];
        }
        return x;
    };
    auto uf_union = [&](int a, int b) {
        int ra = uf_find(a);
        int rb = uf_find(b);
        if (ra != rb)
            parent[rb] = ra;
    };

    for (const auto &pol : policies) {
        for (const auto &atom : pol.atoms) {
            if (atom.kind != Policy::AtomDef::JOIN_EQ && atom.kind != Policy::AtomDef::COL_COL)
                continue;
            int ia = domain_col_index[atom.left_table + "." + atom.left_col];
            int ib = domain_col_index[atom.right_table + "." + atom.right_col];
            uf_union(ia, ib);
        }
    }

    std::map<int, std::vector<std::string>> class_members;
    for (size_t i = 0; i < domain_cols.size(); i++) {
        int root = uf_find((int)i);
        class_members[root].push_back(domain_cols[i]);
    }
    struct ClassKey {
        int root = -1;
        std::string key;
    };
    std::vector<ClassKey> classes;
    classes.reserve(class_members.size());
    for (auto &kv : class_members) {
        auto &members = kv.second;
        std::sort(members.begin(), members.end());
        std::string key;
        for (size_t i = 0; i < members.size(); i++) {
            if (i > 0) key.push_back(',');
            key += members[i];
        }
        classes.push_back(ClassKey{kv.first, key});
    }
    std::sort(classes.begin(), classes.end(), [](const ClassKey &a, const ClassKey &b) {
        return a.key < b.key;
    });

    std::map<int, int> root_to_class;
    for (size_t i = 0; i < classes.size(); i++)
        root_to_class[classes[i].root] = (int)i;

    std::map<std::string, int> join_class_by_col;
    for (size_t i = 0; i < domain_cols.size(); i++) {
        int cid = root_to_class[uf_find((int)i)];
        join_class_by_col[domain_cols[i]] = cid;
    }

    for (auto &pol : policies) {
        for (auto &atom : pol.atoms) {
            if (atom.kind == Policy::AtomDef::JOIN_EQ) {
                std::string lkey = atom.left_table + "." + atom.left_col;
                std::string rkey = atom.right_table + "." + atom.right_col;
                auto itl = join_class_by_col.find(lkey);
                auto itr = join_class_by_col.find(rkey);
                if (itl == join_class_by_col.end() || itr == join_class_by_col.end()) {
                    ereport(ERROR,
                            (errmsg("missing domain mapping for join atom: %s = %s",
                                    lkey.c_str(), rkey.c_str())));
                }
                if (itl->second != itr->second) {
                    ereport(ERROR,
                            (errmsg("join atom resolved to different domains: %s class=%d, %s class=%d",
                                    lkey.c_str(), itl->second, rkey.c_str(), itr->second)));
                }
                atom.join_class_id = itl->second;
            } else if (atom.kind == Policy::AtomDef::COL_CONST) {
                std::string lkey = atom.left_table + "." + atom.left_col;
                auto it = join_class_by_col.find(lkey);
                if (it != join_class_by_col.end())
                    atom.join_class_id = it->second;
            } else if (atom.kind == Policy::AtomDef::COL_COL) {
                std::string lkey = atom.left_table + "." + atom.left_col;
                std::string rkey = atom.right_table + "." + atom.right_col;
                auto itl = join_class_by_col.find(lkey);
                auto itr = join_class_by_col.find(rkey);
                if (itl == join_class_by_col.end() || itr == join_class_by_col.end()) {
                    ereport(ERROR,
                            (errmsg("unsupported col-col atom (missing comparable domain): %s %s %s",
                                    lkey.c_str(), atom.op.c_str(), rkey.c_str())));
                }
                if (itl->second != itr->second) {
                    ereport(ERROR,
                            (errmsg("unsupported col-col atom (cross-domain): %s class=%d %s %s class=%d",
                                    lkey.c_str(), itl->second, atom.op.c_str(), rkey.c_str(), itr->second)));
                }
                atom.join_class_id = itl->second;
            }
        }
    }

    std::map<std::string, DirectAtomInfo> direct_atom_info;
    for (const auto &pol : policies) {
        for (const auto &atom : pol.atoms) {
            if (atom.key.empty())
                continue;
            DirectAtomInfo dai;
            dai.atom = atom;
            dai.line_no = pol.line_no;
            dai.policy_target = pol.target;
            direct_atom_info[atom.key] = std::move(dai);
        }
    }

    std::map<std::string, std::vector<const Policy *>> direct_policies_by_target;
    for (const auto &pol : policies) {
        if (pol.target.empty())
            continue;
        direct_policies_by_target[pol.target].push_back(&pol);
    }
    std::map<std::string, std::set<std::string>> direct_policy_deps;
    for (const auto &pol : policies) {
        if (pol.target.empty())
            continue;
        auto &deps = direct_policy_deps[pol.target];
        for (const auto &ref_table : pol.referenced_tables) {
            if (ref_table.empty() || ref_table == pol.target)
                continue;
            if (direct_policies_by_target.find(ref_table) == direct_policies_by_target.end())
                continue;
            deps.insert(ref_table);
        }
    }

    std::vector<std::string> execution_targets;
    {
        std::map<std::string, uint8_t> visit_state;
        std::function<void(const std::string&)> visit = [&](const std::string& table) {
            if (table.empty())
                return;
            auto dit = direct_policies_by_target.find(table);
            if (dit == direct_policies_by_target.end())
                return;
            uint8_t &state = visit_state[table];
            if (state == 2u)
                return;
            if (state == 1u) {
                ereport(ERROR,
                        (errmsg("policy_eval: cycle detected in direct target dependency graph at table=%s",
                                table.c_str())));
            }
            state = 1u;
            auto dep_it = direct_policy_deps.find(table);
            if (dep_it != direct_policy_deps.end()) {
                for (const std::string &dep : dep_it->second)
                    visit(dep);
            }
            state = 2u;
            execution_targets.push_back(table);
        };
        for (const auto &target : enforcement_targets)
            visit(target);
    }

    std::map<std::string, ExpandedAtomDef> expanded_atoms;
    uint64 atom_instance_seq = 0;
    PolicyAstExpander expander(&direct_asts,
                               &direct_policies_by_target,
                               &direct_policy_deps,
                               &direct_atom_info,
                               &policy_tables,
                               &expanded_atoms,
                               &atom_instance_seq);

    std::map<std::string, AstNode *> effective_perm_ast;
    std::map<std::string, AstNode *> effective_rest_ast;
    std::map<std::string, AstNode *> effective_final_ast;
    const bool expand_debug_subtrees = g_eval_debug || dump_policy_ast;
    for (const auto &target : execution_targets) {
        auto dit = direct_asts.find(target);
        if (dit == direct_asts.end())
            continue;
        std::vector<std::string> stack;
        std::map<std::string, std::string> perm_node_keys;
        std::map<std::string, AstNode *> perm_witness_asts;
        std::map<std::string, std::string> rest_node_keys;
        std::map<std::string, AstNode *> rest_witness_asts;
        std::map<std::string, std::string> final_node_keys;
        std::map<std::string, AstNode *> final_witness_asts;
        AstNode *perm_expanded = nullptr;
        AstNode *rest_expanded = nullptr;
        if (expand_debug_subtrees) {
            perm_expanded = expander.expand_table_mode(target,
                                                       "target:" + target,
                                                       "target:" + target + ":perm",
                                                       target,
                                                       PolicyAstExpander::ExpandMode::kPermOnly,
                                                       &stack,
                                                       &perm_node_keys,
                                                       &perm_witness_asts);
            stack.clear();
            rest_expanded = expander.expand_table_mode(target,
                                                       "target:" + target,
                                                       "target:" + target + ":rest",
                                                       target,
                                                       PolicyAstExpander::ExpandMode::kRestOnly,
                                                       &stack,
                                                       &rest_node_keys,
                                                       &rest_witness_asts);
        }

        AstNode *final_expanded = nullptr;
        stack.clear();
        final_expanded = expander.expand_table_mode(target,
                                                    "target:" + target,
                                                    "target:" + target,
                                                    target,
                                                    PolicyAstExpander::ExpandMode::kFinal,
                                                    &stack,
                                                    &final_node_keys,
                                                    &final_witness_asts);

        effective_perm_ast[target] = perm_expanded;
        effective_rest_ast[target] = rest_expanded;
        effective_final_ast[target] = final_expanded;
    }

    auto compute_target_closure = [&](const std::string &target) {
        std::set<std::string> deps;
        deps.insert(target);  

        auto fit = effective_final_ast.find(target);
        if (fit != effective_final_ast.end() && fit->second) {
            std::set<std::string> keys;
            collect_ast_keys(fit->second, keys);
            for (const auto &k : keys) {
                auto eit = expanded_atoms.find(k);
                if (eit == expanded_atoms.end())
                    continue;
                const Policy::AtomDef &a = eit->second.atom;
                if (!a.left_table.empty())
                    deps.insert(a.left_table);
                if (!a.right_table.empty())
                    deps.insert(a.right_table);
            }
        }
        return deps;
    };

    std::map<std::string, std::set<std::string>> effective_exec_closure_by_target;
    std::set<std::string> exec_closure_tables;
    for (const auto &target : execution_targets) {
        std::set<std::string> deps = compute_target_closure(target);
        effective_exec_closure_by_target[target] = deps;
        exec_closure_tables.insert(deps.begin(), deps.end());
    }

    
    
    std::map<std::string, std::set<std::string>> effective_closure_by_target;
    std::set<std::string> closure_tables;
    for (const auto &target : enforcement_targets) {
        auto it = effective_exec_closure_by_target.find(target);
        if (it == effective_exec_closure_by_target.end())
            continue;
        effective_closure_by_target[target] = it->second;
        closure_tables.insert(it->second.begin(), it->second.end());
    }

    if (g_eval_debug) {
        elog(NOTICE, "policy_eval: execution_targets=[%s]", join_vec(execution_targets).c_str());
        for (const auto &kv : effective_final_ast) {
            std::string perm_dbg = effective_perm_ast[kv.first] ? ast_to_key_string(effective_perm_ast[kv.first]) : "";
            std::string rest_dbg = effective_rest_ast[kv.first] ? ast_to_key_string(effective_rest_ast[kv.first]) : "";
            std::string final_dbg = kv.second ? ast_to_key_string(kv.second) : "";
            elog(NOTICE,
                 "policy_eval: effective_ast target=%s perm=%s rest=%s final=%s",
                 kv.first.c_str(), perm_dbg.c_str(), rest_dbg.c_str(), final_dbg.c_str());
        }
        elog(NOTICE, "policy_eval: closure_tables=[%s]", join_set(closure_tables).c_str());
        for (const auto &kv : effective_closure_by_target) {
            elog(NOTICE,
                 "policy_eval: target_closure target=%s tables=[%s]",
                 kv.first.c_str(),
                 join_set(kv.second).c_str());
        }
    }

    std::set<std::string> used_atom_keys;
    for (const auto &kv : effective_final_ast) {
        collect_ast_keys(kv.second, used_atom_keys);
    }
    for (const auto &kv : direct_asts) {
        collect_ast_keys(kv.second.final, used_atom_keys);
    }

    std::map<std::string, ExpandedAtomDef> atom_defs;
    for (const auto &k : used_atom_keys) {
        auto it = expanded_atoms.find(k);
        if (it != expanded_atoms.end())
            atom_defs[k] = it->second;
        else {
            auto dit = direct_atom_info.find(k);
            if (dit != direct_atom_info.end()) {
                ExpandedAtomDef ex;
                ex.atom = dit->second.atom;
                ex.atom.key = k;
                ex.key = k;
                ex.enforcement_target = dit->second.policy_target;
                ex.occurrence_path = "target:" + dit->second.policy_target;
                ex.source_line = dit->second.line_no;
                ex.target_node_key = "target:" + dit->second.policy_target;
                ex.lhs_node_key = ex.atom.left_table == dit->second.policy_target
                                      ? ex.target_node_key
                                      : "target:" + ex.atom.left_table;
                if (ex.atom.kind == Policy::AtomDef::JOIN_EQ || ex.atom.kind == Policy::AtomDef::COL_COL) {
                    ex.rhs_node_key = ex.atom.right_table == dit->second.policy_target
                                          ? ex.target_node_key
                                          : "target:" + ex.atom.right_table;
                }
                atom_defs[k] = ex;
            }
        }
    }

    std::vector<std::string> atom_list;
    atom_list.reserve(atom_defs.size());
    for (const auto &kv : atom_defs)
        atom_list.push_back(kv.first);

    std::map<std::string, int> atom_map;
    for (size_t i = 0; i < atom_list.size(); i++)
        atom_map[atom_list[i]] = static_cast<int>(i + 1);

    for (auto &kv : effective_final_ast)
        assign_var_ids(kv.second, atom_map);
    for (auto &kv : effective_perm_ast)
        assign_var_ids(kv.second, atom_map);
    for (auto &kv : effective_rest_ast)
        assign_var_ids(kv.second, atom_map);
    for (auto &kv : direct_asts) {
        assign_var_ids(kv.second.final, atom_map);
        assign_var_ids(kv.second.perm, atom_map);
        assign_var_ids(kv.second.rest, atom_map);
    }

    if (dump_policy_ast) {
        int targets_perm0 = 0;
        for (const auto &kv : effective_final_ast) {
            auto dit = direct_asts.find(kv.first);
            int perm_n = (dit == direct_asts.end()) ? 0 : dit->second.perm_count;
            int rest_n = (dit == direct_asts.end()) ? 0 : dit->second.rest_count;
            bool used_y0 = (kv.second && kv.second->type == AstNode::VAR && kv.second->var_id == 0);
            if (perm_n == 0 || used_y0)
                targets_perm0++;
            std::string ast_str = kv.second ? ast_to_string(kv.second) : "";
            elog(NOTICE, "CF_POLICY_AST target=%s perm=%d rest=%d y0=%d ast=%s",
                 kv.first.c_str(), perm_n, rest_n, used_y0 ? 1 : 0, ast_str.c_str());
        }
        elog(NOTICE,
             "CF_POLICY_AST_SUMMARY permissive_total=%d restrictive_total=%d targets=%d targets_perm0=%d",
             total_perm_policies, total_rest_policies, (int)effective_final_ast.size(), targets_perm0);
    }

    std::map<std::string, std::vector<int>> target_joinclasses;
    for (const auto &kv : effective_final_ast) {
        std::set<int> jc;
        std::set<std::string> keys;
        collect_ast_keys(kv.second, keys);
        for (const auto &k : keys) {
            auto it = atom_defs.find(k);
            if (it == atom_defs.end())
                continue;
            const auto &atom = it->second.atom;
            if ((atom.kind == Policy::AtomDef::JOIN_EQ || atom.kind == Policy::AtomDef::COL_COL) &&
                atom.join_class_id >= 0)
                jc.insert(atom.join_class_id);
        }
        target_joinclasses[kv.first].assign(jc.begin(), jc.end());
        if (g_eval_debug) {
            std::string list;
            for (int cid : jc) {
                if (!list.empty()) list += ", ";
                list += std::to_string(cid);
            }
            elog(NOTICE, "policy_eval: target=%s join_classes=[%s]",
                 kv.first.c_str(), list.c_str());
        }
    }

    // Scope identities remain distinct even for two aliases of the SAME base
    // relation. Only artifact/schema names are mapped back to the base table.
    std::map<int,std::map<std::string,std::string>> scoped_node_keys;
    for(auto &item:atom_defs){auto &ea=item.second;auto &atom=ea.atom;
        auto left=scoped_occurrences.find(atom.left_table);
        if(left!=scoped_occurrences.end()){
            scoped_node_keys[atom_map.at(item.first)][atom.left_table]=ea.lhs_node_key;
            atom.left_table=left->second;
        }
        auto right=scoped_occurrences.find(atom.right_table);
        if(right!=scoped_occurrences.end()){
            scoped_node_keys[atom_map.at(item.first)][atom.right_table]=ea.rhs_node_key;
            atom.right_table=right->second;
        }
    }
    const auto physical_set=[&](std::set<std::string> &names){
        std::set<std::string> mapped;
        for(auto name:names){auto it=scoped_occurrences.find(name);mapped.insert(it==scoped_occurrences.end()?name:it->second);}
        names=std::move(mapped);
    };
    physical_set(exec_closure_tables);physical_set(closure_tables);physical_set(known_tables);
    bool has_join_eq = false;
    bool has_cross_atoms = false;
    std::set<std::pair<std::string, std::string>> needed_col_consts;
    std::map<std::string, std::set<std::string>> needed_cols_by_table;
    for (const auto &kv : atom_defs) {
        const auto &atom = kv.second.atom;
        if (!atom.left_table.empty() && !atom.left_col.empty())
            needed_cols_by_table[atom.left_table].insert(atom.left_col);
        if (!atom.right_table.empty() && !atom.right_col.empty())
            needed_cols_by_table[atom.right_table].insert(atom.right_col);
        if (atom.kind == Policy::AtomDef::JOIN_EQ) {
            has_join_eq = true;
        } else {
            if (atom.kind == Policy::AtomDef::COL_COL && atom.left_table != atom.right_table)
                has_cross_atoms = true;
            if (atom.join_class_id < 0)
                needed_col_consts.insert({atom.left_table, atom.left_col});
        }
    }

    std::vector<std::string> needed_files;
    if (has_join_eq || has_cross_atoms) {
        needed_files.push_back("meta/join_classes");
        needed_files.push_back("meta/col_domain");
    }
    for (const auto &tbl : exec_closure_tables) {
        if (known_tables.find(tbl) == known_tables.end())
            continue;
        needed_files.push_back(tbl + "_ctid");
        needed_files.push_back(tbl + "_code_base");
        needed_files.push_back("meta/cols/" + tbl);
    }
    for (const auto &col : needed_col_consts) {
        needed_files.push_back("dict/" + col.first + "/" + col.second);
        needed_files.push_back("meta/dict_type/" + col.first + "/" + col.second);
        needed_files.push_back("meta/dict_sorted/" + col.first + "/" + col.second);
    }
    std::sort(needed_files.begin(), needed_files.end());
    needed_files.erase(std::unique(needed_files.begin(), needed_files.end()), needed_files.end());
    std::vector<std::string> direct_targets(enforcement_targets.begin(), enforcement_targets.end());

    std::set<std::string> table_name_set;
    std::set<std::string> col_name_set;
    std::set<std::string> node_key_set;
    for (const auto &kv : atom_defs) {
        const auto &atom = kv.second.atom;
        if (!atom.left_table.empty()) {
            table_name_set.insert(atom.left_table);
            col_name_set.insert(atom.left_table + "." + atom.left_col);
        }
        if (!atom.right_table.empty()) {
            table_name_set.insert(atom.right_table);
            col_name_set.insert(atom.right_table + "." + atom.right_col);
        }
        if (!kv.second.lhs_node_key.empty())
            node_key_set.insert(kv.second.lhs_node_key);
        if (!kv.second.rhs_node_key.empty())
            node_key_set.insert(kv.second.rhs_node_key);
        if (!kv.second.target_node_key.empty())
            node_key_set.insert(kv.second.target_node_key);
    }

    std::map<std::string, int> table_id_by_name;
    {
        int next = 1;
        for (const auto &tname : table_name_set)
            table_id_by_name[tname] = next++;
    }
    std::map<std::string, int> col_id_by_name;
    {
        int next = 1;
        for (const auto &cname : col_name_set)
            col_id_by_name[cname] = next++;
    }
    std::map<std::string, int> node_id_by_key;
    {
        int next = 1;
        for (const auto &nkey : node_key_set)
            node_id_by_key[nkey] = next++;
    }

    for(const auto &atom:scoped_node_keys)for(const auto &alias:atom.second)
        g_quantifier_binders[atom.first][alias.first]=node_id_by_key.at(alias.second);

    auto map_const_op = [](const std::string &op) {
        if (!op.empty() && op[0] == '@') {
            ereport(ERROR,
                    (errmsg("policy_eval: unresolved operator slot in runtime policy"),
                     errdetail("slot %s reached evaluation without query binding", op.c_str())));
        }
        if (op == "=") return POLICY_OP_EQ;
        if (op == "<") return POLICY_OP_LT;
        if (op == "<=") return POLICY_OP_LE;
        if (op == ">") return POLICY_OP_GT;
        if (op == ">=") return POLICY_OP_GE;
        if (op == "!=") return POLICY_OP_NE;
        ereport(ERROR, (errmsg("unsupported policy operator: %s", op.c_str())));
        return POLICY_OP_EQ;
    };

    PolicyEvalResultC *res = (PolicyEvalResultC *)palloc0(sizeof(PolicyEvalResultC));
    res->needed_count = static_cast<int>(needed_files.size());
    res->needed_files = res->needed_count ? (char **)palloc0(sizeof(char *) * res->needed_count) : nullptr;
    for (int i = 0; i < res->needed_count; i++)
        res->needed_files[i] = pstrdup(needed_files[i].c_str());

    res->atom_count = static_cast<int>(atom_list.size());
    res->atoms = res->atom_count ? (PolicyAtomC *)palloc0(sizeof(PolicyAtomC) * res->atom_count) : nullptr;
    for (int i = 0; i < res->atom_count; i++) {
        const auto &key = atom_list[(size_t)i];
        auto it = atom_defs.find(key);
        if (it == atom_defs.end())
            continue;
        const ExpandedAtomDef &ea = it->second;
        const Policy::AtomDef &atom = ea.atom;

        PolicyAtomC *out = &res->atoms[i];
        out->atom_id = atom_map[key];
        if (atom.kind == Policy::AtomDef::JOIN_EQ)
            out->kind = POLICY_ATOM_JOIN_EQ;
        else if (atom.kind == Policy::AtomDef::COL_COL)
            out->kind = POLICY_ATOM_COL_COL;
        else
            out->kind = POLICY_ATOM_COL_CONST;
        out->join_class_id = atom.join_class_id;
        out->domain_id = atom.join_class_id;
        out->lhs_node_id = -1;
        out->rhs_node_id = -1;
        out->lhs_table_id = -1;
        out->rhs_table_id = -1;
        out->lhs_col_id = -1;
        out->rhs_col_id = -1;
        out->target_node_id = -1;

        auto ltid = table_id_by_name.find(atom.left_table);
        if (ltid != table_id_by_name.end())
            out->lhs_table_id = ltid->second;
        auto rtid = table_id_by_name.find(atom.right_table);
        if (rtid != table_id_by_name.end())
            out->rhs_table_id = rtid->second;
        auto lcid = col_id_by_name.find(atom.left_table + "." + atom.left_col);
        if (lcid != col_id_by_name.end())
            out->lhs_col_id = lcid->second;
        auto rcid = col_id_by_name.find(atom.right_table + "." + atom.right_col);
        if (rcid != col_id_by_name.end())
            out->rhs_col_id = rcid->second;
        auto lnid = node_id_by_key.find(ea.lhs_node_key);
        if (lnid != node_id_by_key.end())
            out->lhs_node_id = lnid->second;
        auto rnid = node_id_by_key.find(ea.rhs_node_key);
        if (rnid != node_id_by_key.end())
            out->rhs_node_id = rnid->second;
        auto tnit = node_id_by_key.find(ea.target_node_key);
        if (tnit != node_id_by_key.end())
            out->target_node_id = tnit->second;

        out->canon_key = pstrdup(atom.key.c_str());
        if (atom.kind == Policy::AtomDef::JOIN_EQ) {
            std::string lkey = "join:" + atom.left_table + "." + atom.left_col +
                               " class=" + std::to_string(atom.join_class_id);
            std::string rkey = "join:" + atom.right_table + "." + atom.right_col +
                               " class=" + std::to_string(atom.join_class_id);
            out->lhs_schema_key = pstrdup(lkey.c_str());
            out->rhs_schema_key = pstrdup(rkey.c_str());
            out->op = 0;
            out->const_count = 0;
            out->const_values = nullptr;
        } else if (atom.kind == Policy::AtomDef::COL_CONST) {
            std::string skey = "const:" + atom.left_table + "." + atom.left_col;
            out->lhs_schema_key = pstrdup(skey.c_str());
            out->rhs_schema_key = nullptr;
            out->op = map_const_op(atom.op);
            out->const_count = static_cast<int>(atom.values.size());
            out->const_values = out->const_count ? (char **)palloc0(sizeof(char *) * out->const_count) : nullptr;
            for (int v = 0; v < out->const_count; v++)
                out->const_values[v] = pstrdup(atom.values[(size_t)v].c_str());
        } else {
            std::string lkey = "join:" + atom.left_table + "." + atom.left_col +
                               " class=" + std::to_string(atom.join_class_id);
            std::string rkey = "join:" + atom.right_table + "." + atom.right_col +
                               " class=" + std::to_string(atom.join_class_id);
            out->lhs_schema_key = pstrdup(lkey.c_str());
            out->rhs_schema_key = pstrdup(rkey.c_str());
            out->op = map_const_op(atom.op);
            out->const_count = 0;
            out->const_values = nullptr;
        }
    }

    auto resolve_target_node_id = [&](const std::string &target_name) {
        int resolved_node = -1;
        auto tnid = node_id_by_key.find("target:" + target_name);
        if (tnid != node_id_by_key.end())
            return tnid->second;

        std::set<int> candidate_nodes;
        for (const auto &akv : atom_defs) {
            const ExpandedAtomDef &ea = akv.second;
            const Policy::AtomDef &atom = ea.atom;
            if (atom.left_table == target_name && !ea.lhs_node_key.empty()) {
                auto itn = node_id_by_key.find(ea.lhs_node_key);
                if (itn != node_id_by_key.end())
                    candidate_nodes.insert(itn->second);
            }
            if (atom.right_table == target_name && !ea.rhs_node_key.empty()) {
                auto itn = node_id_by_key.find(ea.rhs_node_key);
                if (itn != node_id_by_key.end())
                    candidate_nodes.insert(itn->second);
            }
            if (!ea.target_node_key.empty() &&
                ea.target_node_key.rfind("target:" + target_name, 0) == 0) {
                auto itn = node_id_by_key.find(ea.target_node_key);
                if (itn != node_id_by_key.end())
                    candidate_nodes.insert(itn->second);
            }
        }
        if (candidate_nodes.size() == 1)
            resolved_node = *candidate_nodes.begin();
        return resolved_node;
    };

    auto fill_target_payload = [&](const std::vector<std::string> &targets,
                                   bool use_direct_ast,
                                   char ***out_tables,
                                   int **out_table_ids,
                                   int **out_node_ids,
                                   char ***out_asts,
                                   char ***out_perm_asts,
                                   char ***out_rest_asts,
                                   int *out_tok_len,
                                   PolicyAstTokC **out_toks,
                                   int **out_tok_offsets,
                                   int **out_tok_counts,
                                   int **out_joinclass_counts,
                                   int **out_joinclass_offsets,
                                   int **out_joinclass_ids,
                                   int *out_joinclass_ids_len) {
        int count = static_cast<int>(targets.size());
        if (out_tables)
            *out_tables = count ? (char **)palloc0(sizeof(char *) * count) : nullptr;
        if (out_table_ids)
            *out_table_ids = count ? (int *)palloc0(sizeof(int) * count) : nullptr;
        if (out_node_ids)
            *out_node_ids = count ? (int *)palloc0(sizeof(int) * count) : nullptr;
        if (out_asts)
            *out_asts = count ? (char **)palloc0(sizeof(char *) * count) : nullptr;
        if (out_perm_asts)
            *out_perm_asts = count ? (char **)palloc0(sizeof(char *) * count) : nullptr;
        if (out_rest_asts)
            *out_rest_asts = count ? (char **)palloc0(sizeof(char *) * count) : nullptr;
        if (out_tok_offsets)
            *out_tok_offsets = count ? (int *)palloc0(sizeof(int) * count) : nullptr;
        if (out_tok_counts)
            *out_tok_counts = count ? (int *)palloc0(sizeof(int) * count) : nullptr;
        if (out_joinclass_counts)
            *out_joinclass_counts = count ? (int *)palloc0(sizeof(int) * count) : nullptr;
        if (out_joinclass_offsets)
            *out_joinclass_offsets = count ? (int *)palloc0(sizeof(int) * count) : nullptr;
        if (out_tok_len)
            *out_tok_len = 0;
        if (out_toks)
            *out_toks = nullptr;
        if (out_joinclass_ids_len)
            *out_joinclass_ids_len = 0;
        if (out_joinclass_ids)
            *out_joinclass_ids = nullptr;

        std::vector<PolicyAstTokC> tok_flat;
        tok_flat.reserve((size_t)count * 16u);
        std::vector<int> joinclass_ids;
        if (out_joinclass_ids)
            joinclass_ids.reserve((size_t)count * 4u);

        for (int i = 0; i < count; i++) {
            const std::string &target_name = targets[(size_t)i];
            AstNode *f = nullptr;
            if (use_direct_ast) {
                auto dit = direct_asts.find(target_name);
                if (dit != direct_asts.end())
                    f = dit->second.final;
            } else {
                auto fit = effective_final_ast.find(target_name);
                if (fit != effective_final_ast.end())
                    f = fit->second;
            }
            AstNode *p = nullptr;
            if (use_direct_ast) {
                auto dit = direct_asts.find(target_name);
                if (dit != direct_asts.end())
                    p = dit->second.perm;
            } else {
                auto pit = effective_perm_ast.find(target_name);
                if (pit != effective_perm_ast.end())
                    p = pit->second;
            }
            AstNode *r = nullptr;
            if (use_direct_ast) {
                auto dit = direct_asts.find(target_name);
                if (dit != direct_asts.end())
                    r = dit->second.rest;
            } else {
                auto rit = effective_rest_ast.find(target_name);
                if (rit != effective_rest_ast.end())
                    r = rit->second;
            }

            std::string ast_str = f ? ast_to_string(f) : "";
            std::string perm_str = p ? ast_to_string(p) : "";
            std::string rest_str = r ? ast_to_string(r) : "";

            if (out_tables && *out_tables)
                (*out_tables)[i] = pstrdup(target_name.c_str());
            if (out_table_ids && *out_table_ids) {
                auto ttid = table_id_by_name.find(target_name);
                (*out_table_ids)[i] = (ttid != table_id_by_name.end()) ? ttid->second : -1;
            }
            if (out_node_ids && *out_node_ids)
                (*out_node_ids)[i] = resolve_target_node_id(target_name);
            if (out_asts && *out_asts)
                (*out_asts)[i] = ast_str.empty() ? pstrdup("") : pstrdup(ast_str.c_str());
            if (out_perm_asts && *out_perm_asts)
                (*out_perm_asts)[i] = perm_str.empty() ? pstrdup("") : pstrdup(perm_str.c_str());
            if (out_rest_asts && *out_rest_asts)
                (*out_rest_asts)[i] = rest_str.empty() ? pstrdup("") : pstrdup(rest_str.c_str());

            if (out_tok_offsets && *out_tok_offsets)
                (*out_tok_offsets)[i] = static_cast<int>(tok_flat.size());
            std::vector<PolicyAstTokC> ast_toks;
            if (f)
                ast_to_postfix_tokens(f, ast_toks);
            if (out_tok_counts && *out_tok_counts)
                (*out_tok_counts)[i] = static_cast<int>(ast_toks.size());
            tok_flat.insert(tok_flat.end(), ast_toks.begin(), ast_toks.end());

            if (out_joinclass_offsets && *out_joinclass_offsets)
                (*out_joinclass_offsets)[i] = static_cast<int>(joinclass_ids.size());
            if (out_joinclass_counts && *out_joinclass_counts) {
                auto jcit = target_joinclasses.find(target_name);
                int jc_count = 0;
                if (jcit != target_joinclasses.end()) {
                    jc_count = static_cast<int>(jcit->second.size());
                    joinclass_ids.insert(joinclass_ids.end(), jcit->second.begin(), jcit->second.end());
                }
                (*out_joinclass_counts)[i] = jc_count;
            }

            if (g_eval_debug) {
                elog(NOTICE,
                     "policy_eval: target_ast_tokens target=%s count=%zu",
                     target_name.c_str(),
                     ast_toks.size());
                elog(NOTICE,
                     "policy_eval: combined_ast target=%s ast=%s perm_ast=%s rest_ast=%s",
                     target_name.c_str(),
                     ast_str.c_str(),
                     perm_str.c_str(),
                     rest_str.c_str());
            }
        }

        if (out_tok_len)
            *out_tok_len = static_cast<int>(tok_flat.size());
        if (out_toks && out_tok_len && *out_tok_len > 0) {
            *out_toks = (PolicyAstTokC *)palloc0(sizeof(PolicyAstTokC) * (*out_tok_len));
            for (int i = 0; i < *out_tok_len; i++)
                (*out_toks)[i] = tok_flat[(size_t)i];
        }
        if (out_joinclass_ids_len)
            *out_joinclass_ids_len = static_cast<int>(joinclass_ids.size());
        if (out_joinclass_ids && out_joinclass_ids_len && *out_joinclass_ids_len > 0) {
            *out_joinclass_ids = (int *)palloc0(sizeof(int) * (*out_joinclass_ids_len));
            for (int i = 0; i < *out_joinclass_ids_len; i++)
                (*out_joinclass_ids)[i] = joinclass_ids[(size_t)i];
        }
    };

    res->target_count = static_cast<int>(direct_targets.size());
    fill_target_payload(direct_targets,
                        true,
                        &res->target_tables,
                        &res->target_table_ids,
                        &res->target_node_ids,
                        &res->target_asts,
                        &res->target_perm_asts,
                        &res->target_rest_asts,
                        &res->target_ast_tok_len,
                        &res->target_ast_toks,
                        &res->target_ast_tok_offsets,
                        &res->target_ast_tok_counts,
                        &res->target_joinclass_counts,
                        &res->target_joinclass_offsets,
                        &res->target_joinclass_ids,
                        &res->target_joinclass_ids_len);

    res->exec_target_count = static_cast<int>(execution_targets.size());
    fill_target_payload(execution_targets,
                        false,
                        &res->exec_target_tables,
                        &res->exec_target_table_ids,
                        &res->exec_target_node_ids,
                        &res->exec_target_asts,
                        &res->exec_target_perm_asts,
                        &res->exec_target_rest_asts,
                        &res->exec_target_ast_tok_len,
                        &res->exec_target_ast_toks,
                        &res->exec_target_ast_tok_offsets,
                        &res->exec_target_ast_tok_counts,
                        nullptr,
                        nullptr,
                        nullptr,
                        nullptr);

    if (g_eval_debug) {
        for (size_t i = 0; i < atom_list.size(); i++) {
            int id = (int)(i + 1);
            elog(NOTICE, "policy_eval: atom y%d = %s", id, atom_list[i].c_str());
        }
    }

    res->ast_node_count = static_cast<int>(store.nodes.size());
    res->ast_nodes = res->ast_node_count ? (void **)palloc0(sizeof(void *) * res->ast_node_count) : nullptr;
    for (int i = 0; i < res->ast_node_count; i++)
        res->ast_nodes[i] = store.nodes[i];

    res->closure_count = static_cast<int>(closure_tables.size());
    res->closure_tables = res->closure_count ? (char **)palloc0(sizeof(char *) * res->closure_count) : nullptr;
    int c = 0;
    for (const auto &tbl : closure_tables)
        res->closure_tables[c++] = pstrdup(tbl.c_str());
    if (g_eval_debug)
        elog(NOTICE, "policy_eval: closure_count=%d", res->closure_count);

    res->scanned_count = static_cast<int>(scanned_list.size());
    res->scanned_tables = res->scanned_count ? (char **)palloc0(sizeof(char *) * res->scanned_count) : nullptr;
    for (int i = 0; i < res->scanned_count; i++)
        res->scanned_tables[i] = pstrdup(scanned_list[(size_t)i].c_str());

    g_node_store = nullptr;
    return res;
}

// Converts a policy file into atoms, occurrences, and Boolean roots.
PolicyEvalResultC *evaluate_policies_scanned(const char *policy_path,
                                             char **scanned_tables,
                                             int n_scanned) {
    return evaluate_policies_internal(policy_path, false, scanned_tables, n_scanned, false);
}

PolicyEvalResultC *evaluate_policies_text_scanned(const char *policy_text,
                                                  char **scanned_tables,
                                                  int n_scanned) {
    return evaluate_policies_internal(policy_text, true, scanned_tables, n_scanned, false);
}

PolicyEvalResultC *evaluate_policies_c(const char *query_sql, const char *policy_path) {
    (void) query_sql;
    return evaluate_policies_internal(policy_path, false, nullptr, 0, true);
}

char *bind_policy_template_for_query(const char *template_path,
                                     const char *binding_path,
                                     const char *query_path,
                                     const char *query_id,
                                     const char *query_sql) {
    std::string template_file = template_path ? template_path : "";
    std::string binding_file = binding_path ? binding_path : "";
    std::string query_file = query_path ? query_path : "";
    std::string qid = query_id ? query_id : "";
    std::string sql = query_sql ? query_sql : "";
    if (template_file.empty() || binding_file.empty() || query_file.empty())
        return nullptr;

    std::ifstream tin(template_file);
    if (!tin.is_open()) {
        ereport(ERROR, (errmsg("policy_eval: unable to open policy template: %s", template_file.c_str())));
    }
    std::ostringstream tbuf;
    tbuf << tin.rdbuf();
    std::string template_text = tbuf.str();

    std::map<std::string, std::map<std::string, std::string>> binding_map = load_binding_map(binding_file);

    std::map<std::string, std::string> query_map = load_query_map(query_file);

    std::string resolved_query_id = normalize_query_id_key(qid);
    if (!resolved_query_id.empty()) {
        std::string keys;
        for (const auto &kv : binding_map) {
            if (!keys.empty())
                keys += ",";
            keys += kv.first;
        }
        auto it = binding_map.find(resolved_query_id);
        if (it != binding_map.end()) {
            std::string bound = bind_policy_template_text(template_text, it->second);
            return pstrdup(bound.c_str());
        }
        ereport(ERROR,
                (errmsg("policy_eval: missing binding block for query id %s", resolved_query_id.c_str()),
                 errdetail("No binding section was found in %s (available query ids: [%s])",
                           binding_file.c_str(),
                           keys.c_str())));
    }

    if (sql.empty())
        ereport(ERROR,
                (errmsg("policy_eval: query binding requires query id or SQL text"),
                 errdetail("No query id was provided and SQL text is empty.")));

    std::string norm_sql = collapse_sql_for_match(sql);
    std::vector<std::string> matched_query_ids;
    for (const auto &kv : query_map) {
        if (kv.second == norm_sql)
            matched_query_ids.push_back(kv.first);
    }
    if (matched_query_ids.empty()) {
        ereport(ERROR,
                (errmsg("policy_eval: query SQL not found in query file"),
                 errdetail("No entry in %s matches the current SQL text.", query_file.c_str())));
    }
    if (matched_query_ids.size() > 1u) {
        std::string joined;
        for (size_t i = 0; i < matched_query_ids.size(); i++) {
            if (i) joined += ", ";
            joined += matched_query_ids[i];
        }
        ereport(ERROR,
                (errmsg("policy_eval: ambiguous query binding lookup"),
                 errdetail("Multiple query ids match the same SQL text: %s", joined.c_str())));
    }
    auto it = binding_map.find(matched_query_ids[0]);
    if (it == binding_map.end()) {
        ereport(ERROR,
                (errmsg("policy_eval: missing binding block for query id %s", matched_query_ids[0].c_str()),
                 errdetail("No binding section was found in %s", binding_file.c_str())));
    }
    std::string bound = bind_policy_template_text(template_text, it->second);
    return pstrdup(bound.c_str());
}

void free_policy_eval_result(PolicyEvalResultC *res) {
    if (!res) return;
    if (res->needed_files) {
        for (int i = 0; i < res->needed_count; i++) {
            if (res->needed_files[i]) pfree(res->needed_files[i]);
        }
        pfree(res->needed_files);
    }
    if (res->atoms) {
        for (int i = 0; i < res->atom_count; i++) {
            PolicyAtomC *a = &res->atoms[i];
            if (a->canon_key) pfree(a->canon_key);
            if (a->lhs_schema_key) pfree(a->lhs_schema_key);
            if (a->rhs_schema_key) pfree(a->rhs_schema_key);
            if (a->const_values) {
                for (int j = 0; j < a->const_count; j++) {
                    if (a->const_values[j]) pfree(a->const_values[j]);
                }
                pfree(a->const_values);
            }
        }
        pfree(res->atoms);
    }
    if (res->target_tables) {
        for (int i = 0; i < res->target_count; i++) {
            if (res->target_tables[i]) pfree(res->target_tables[i]);
        }
        pfree(res->target_tables);
    }
    if (res->target_table_ids)
        pfree(res->target_table_ids);
    if (res->target_node_ids)
        pfree(res->target_node_ids);
    if (res->target_asts) {
        for (int i = 0; i < res->target_count; i++) {
            if (res->target_asts[i]) pfree(res->target_asts[i]);
        }
        pfree(res->target_asts);
    }
    if (res->target_perm_asts) {
        for (int i = 0; i < res->target_count; i++) {
            if (res->target_perm_asts[i]) pfree(res->target_perm_asts[i]);
        }
        pfree(res->target_perm_asts);
    }
    if (res->target_rest_asts) {
        for (int i = 0; i < res->target_count; i++) {
            if (res->target_rest_asts[i]) pfree(res->target_rest_asts[i]);
        }
        pfree(res->target_rest_asts);
    }
    if (res->target_ast_toks)
        pfree(res->target_ast_toks);
    if (res->target_ast_tok_offsets)
        pfree(res->target_ast_tok_offsets);
    if (res->target_ast_tok_counts)
        pfree(res->target_ast_tok_counts);
    if (res->target_joinclass_counts)
        pfree(res->target_joinclass_counts);
    if (res->target_joinclass_offsets)
        pfree(res->target_joinclass_offsets);
    if (res->target_joinclass_ids)
        pfree(res->target_joinclass_ids);
    if (res->exec_target_tables) {
        for (int i = 0; i < res->exec_target_count; i++) {
            if (res->exec_target_tables[i]) pfree(res->exec_target_tables[i]);
        }
        pfree(res->exec_target_tables);
    }
    if (res->exec_target_table_ids)
        pfree(res->exec_target_table_ids);
    if (res->exec_target_node_ids)
        pfree(res->exec_target_node_ids);
    if (res->exec_target_asts) {
        for (int i = 0; i < res->exec_target_count; i++) {
            if (res->exec_target_asts[i]) pfree(res->exec_target_asts[i]);
        }
        pfree(res->exec_target_asts);
    }
    if (res->exec_target_perm_asts) {
        for (int i = 0; i < res->exec_target_count; i++) {
            if (res->exec_target_perm_asts[i]) pfree(res->exec_target_perm_asts[i]);
        }
        pfree(res->exec_target_perm_asts);
    }
    if (res->exec_target_rest_asts) {
        for (int i = 0; i < res->exec_target_count; i++) {
            if (res->exec_target_rest_asts[i]) pfree(res->exec_target_rest_asts[i]);
        }
        pfree(res->exec_target_rest_asts);
    }
    if (res->exec_target_ast_toks)
        pfree(res->exec_target_ast_toks);
    if (res->exec_target_ast_tok_offsets)
        pfree(res->exec_target_ast_tok_offsets);
    if (res->exec_target_ast_tok_counts)
        pfree(res->exec_target_ast_tok_counts);
    if (res->ast_nodes) {
        for (int i = 0; i < res->ast_node_count; i++) {
            AstNode *n = static_cast<AstNode *>(res->ast_nodes[i]);
            delete n;
        }
        pfree(res->ast_nodes);
    }
    if (res->closure_tables) {
        for (int i = 0; i < res->closure_count; i++) {
            if (res->closure_tables[i]) pfree(res->closure_tables[i]);
        }
        pfree(res->closure_tables);
    }
    if (res->scanned_tables) {
        for (int i = 0; i < res->scanned_count; i++) {
            if (res->scanned_tables[i]) pfree(res->scanned_tables[i]);
        }
        pfree(res->scanned_tables);
    }
    pfree(res);
}
