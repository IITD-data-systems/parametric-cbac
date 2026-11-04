#include "policy_spec.h"

#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef enum {
    TOK_IDENT = 1,
    TOK_STRING,
    TOK_NUMBER,
    TOK_OP,
    TOK_SLOT,
    TOK_LPAREN,
    TOK_RPAREN,
    TOK_COMMA
} TokenType;

typedef struct {
    TokenType type;
    char *text;
} Token;

typedef struct {
    PolicyAtom *items;
    int count;
    int cap;
} AtomList;

typedef struct {
    char alias[POLICY_SPEC_MAX_NAME];
    char table[POLICY_SPEC_MAX_NAME];
} OccAlias;

typedef struct {
    OccAlias *items;
    int count;
    int cap;
} OccAliasList;

static int copy_str(char *dst, size_t dstsz, const char *src);

static char *str_dup_range(const char *s, size_t n) {
    char *out = (char *)malloc(n + 1);
    if (!out) return NULL;
    memcpy(out, s, n);
    out[n] = '\0';
    return out;
}

static void to_lower_inplace(char *s) {
    for (; s && *s; s++) *s = (char)tolower((unsigned char)*s);
}

static char *trim_inplace(char *s) {
    if (!s) return s;
    while (*s && isspace((unsigned char)*s)) s++;
    size_t len = strlen(s);
    while (len > 0 && isspace((unsigned char)s[len - 1])) {
        s[len - 1] = '\0';
        len--;
    }
    return s;
}

static int token_push(Token **arr, int *count, int *cap, Token tok) {
    if (*count >= *cap) {
        int ncap = (*cap == 0) ? 32 : (*cap * 2);
        Token *narr = (Token *)realloc(*arr, sizeof(Token) * ncap);
        if (!narr) return -1;
        *arr = narr;
        *cap = ncap;
    }
    (*arr)[(*count)++] = tok;
    return 0;
}

static int tokenize(const char *s, Token **out_tokens, int *out_count) {
    *out_tokens = NULL;
    *out_count = 0;
    int cap = 0;
    const char *p = s;
    while (*p) {
        if (isspace((unsigned char)*p)) {
            p++;
            continue;
        }
        if (isalpha((unsigned char)*p) || *p == '_') {
            const char *start = p;
            while (isalnum((unsigned char)*p) || *p == '_' || *p == '.') p++;
            char *txt = str_dup_range(start, (size_t)(p - start));
            if (!txt) return -1;
            to_lower_inplace(txt);
            Token t = {TOK_IDENT, txt};
            if (token_push(out_tokens, out_count, &cap, t) != 0) return -1;
            continue;
        }
        if (*p == '@' || *p == '$') {
            const char *start = p;
            p++;
            while (isalnum((unsigned char)*p) || *p == '_') p++;
            char *txt = str_dup_range(start, (size_t)(p - start));
            if (!txt) return -1;
            to_lower_inplace(txt);
            Token t = {TOK_SLOT, txt};
            if (token_push(out_tokens, out_count, &cap, t) != 0) return -1;
            continue;
        }
        if (isdigit((unsigned char)*p) || (*p == '-' && isdigit((unsigned char)p[1]))) {
            const char *start = p;
            p++;
            while (isdigit((unsigned char)*p) || *p == '.') p++;
            char *txt = str_dup_range(start, (size_t)(p - start));
            if (!txt) return -1;
            Token t = {TOK_NUMBER, txt};
            if (token_push(out_tokens, out_count, &cap, t) != 0) return -1;
            continue;
        }
        if (*p == '\'') {
            p++;
            size_t len = 0;
            char *buf = (char *)malloc(strlen(p) + 1);
            if (!buf) return -1;
            while (*p) {
                if (*p == '\'' && p[1] == '\'') {
                    buf[len++] = '\'';
                    p += 2;
                    continue;
                }
                if (*p == '\'') break;
                buf[len++] = *p++;
            }
            if (*p == '\'') p++;
            buf[len] = '\0';
            Token t = {TOK_STRING, buf};
            if (token_push(out_tokens, out_count, &cap, t) != 0) return -1;
            continue;
        }
        if (*p == '(') { Token t = {TOK_LPAREN, str_dup_range("(", 1)}; if (token_push(out_tokens, out_count, &cap, t) != 0) return -1; p++; continue; }
        if (*p == ')') { Token t = {TOK_RPAREN, str_dup_range(")", 1)}; if (token_push(out_tokens, out_count, &cap, t) != 0) return -1; p++; continue; }
        if (*p == ',') { Token t = {TOK_COMMA, str_dup_range(",", 1)}; if (token_push(out_tokens, out_count, &cap, t) != 0) return -1; p++; continue; }
        if (strchr("=<>!", *p)) {
            const char *start = p;
            p++;
            if ((*start == '<' || *start == '>' || *start == '!') && *p == '=') p++;
            else if (*start == '<' && *p == '>') p++;
            char *txt = str_dup_range(start, (size_t)(p - start));
            if (!txt) return -1;
            Token t = {TOK_OP, txt};
            if (token_push(out_tokens, out_count, &cap, t) != 0) return -1;
            continue;
        }
        p++;
    }
    return 0;
}

static void free_tokens(Token *toks, int ntok) {
    if (!toks) return;
    for (int i = 0; i < ntok; i++) {
        free(toks[i].text);
    }
    free(toks);
}

static int atom_push(AtomList *list, const PolicyAtom *atom) {
    if (list->count >= list->cap) {
        int ncap = (list->cap == 0) ? 16 : (list->cap * 2);
        PolicyAtom *nitems = (PolicyAtom *)realloc(list->items, sizeof(PolicyAtom) * ncap);
        if (!nitems) return -1;
        list->items = nitems;
        list->cap = ncap;
    }
    list->items[list->count++] = *atom;
    return 0;
}

static int occ_alias_push(OccAliasList *list, const char *alias, const char *table) {
    if (list->count >= list->cap) {
        int ncap = (list->cap == 0) ? 8 : (list->cap * 2);
        OccAlias *nitems = (OccAlias *)realloc(list->items, sizeof(OccAlias) * ncap);
        if (!nitems) return -1;
        list->items = nitems;
        list->cap = ncap;
    }
    memset(&list->items[list->count], 0, sizeof(OccAlias));
    copy_str(list->items[list->count].alias, sizeof(list->items[list->count].alias), alias);
    copy_str(list->items[list->count].table, sizeof(list->items[list->count].table), table);
    list->count++;
    return 0;
}

static const char *occ_alias_lookup(const OccAliasList *list, const char *alias) {
    if (!list || !alias) return NULL;
    for (int i = 0; i < list->count; i++) {
        if (strcmp(list->items[i].alias, alias) == 0)
            return list->items[i].table;
    }
    return NULL;
}

static void occ_alias_free(OccAliasList *list) {
    if (!list) return;
    free(list->items);
    list->items = NULL;
    list->count = 0;
    list->cap = 0;
}

static int copy_str(char *dst, size_t dstsz, const char *src) {
    if (!dst || dstsz == 0) return -1;
    if (!src) { dst[0] = '\0'; return 0; }
    size_t n = strlen(src);
    if (n >= dstsz) n = dstsz - 1;
    memcpy(dst, src, n);
    dst[n] = '\0';
    return 0;
}

static int is_ident_start_ch(char c) {
    return isalpha((unsigned char)c) || c == '_';
}

static int is_ident_char_ch(char c) {
    return isalnum((unsigned char)c) || c == '_';
}

static int append_text(char **buf, size_t *len, size_t *cap, const char *src, size_t n) {
    if (!buf || !len || !cap) return -1;
    if (*len + n + 1 > *cap) {
        size_t ncap = (*cap == 0) ? 128 : *cap;
        while (*len + n + 1 > ncap) ncap *= 2;
        char *nbuf = (char *)realloc(*buf, ncap);
        if (!nbuf) return -1;
        *buf = nbuf;
        *cap = ncap;
    }
    memcpy(*buf + *len, src, n);
    *len += n;
    (*buf)[*len] = '\0';
    return 0;
}

static char *expand_occ_aliases_expr(const char *expr, const OccAliasList *aliases) {
    size_t len = 0, cap = 0;
    char *out = NULL;
    const char *p = expr;
    while (p && *p) {
        if (!is_ident_start_ch(*p)) {
            if (append_text(&out, &len, &cap, p, 1) != 0) {
                free(out);
                return NULL;
            }
            p++;
            continue;
        }
        const char *start = p;
        p++;
        while (is_ident_char_ch(*p)) p++;
        if (*p == '.') {
            char *alias = str_dup_range(start, (size_t)(p - start));
            const char *table = NULL;
            if (!alias) {
                free(out);
                return NULL;
            }
            to_lower_inplace(alias);
            table = occ_alias_lookup(aliases, alias);
            free(alias);
            if (table) {
                if (append_text(&out, &len, &cap, table, strlen(table)) != 0) {
                    free(out);
                    return NULL;
                }
                const char *dot = p;
                p++;
                while (is_ident_char_ch(*p)) p++;
                if (append_text(&out, &len, &cap, dot, (size_t)(p - dot)) != 0) {
                    free(out);
                    return NULL;
                }
                continue;
            }
        }
        if (append_text(&out, &len, &cap, start, (size_t)(p - start)) != 0) {
            free(out);
            return NULL;
        }
    }
    if (!out) {
        out = (char *)malloc(1);
        if (!out) return NULL;
        out[0] = '\0';
    }
    return out;
}

static char **split_template_csv_items(const char *s, int *count_out) {
    char **items = NULL;
    int count = 0;
    int cap = 0;
    const char *p = s;
    const char *start = s;
    int paren_depth = 0;
    if (count_out) *count_out = 0;
    while (1) {
        char ch = *p;
        if (ch == '(') paren_depth++;
        else if (ch == ')' && paren_depth > 0) paren_depth--;
        if ((ch == ',' && paren_depth == 0) || ch == '\0') {
            size_t len = (size_t)(p - start);
            char *part = (char *)malloc(len + 1);
            if (!part) goto fail;
            memcpy(part, start, len);
            part[len] = '\0';
            {
                char *trimmed = trim_inplace(part);
                if (*trimmed != '\0') {
                    if (count == cap) {
                        int ncap = cap ? cap * 2 : 8;
                        char **ni = (char **)realloc(items, sizeof(char *) * (size_t)ncap);
                        if (!ni) { free(part); goto fail; }
                        items = ni;
                        cap = ncap;
                    }
                    if (trimmed != part)
                        memmove(part, trimmed, strlen(trimmed) + 1);
                    items[count++] = part;
                } else {
                    free(part);
                }
            }
            if (ch == '\0') break;
            start = p + 1;
        }
        p++;
    }
    if (count_out) *count_out = count;
    return items;
fail:
    if (items) {
        int i;
        for (i = 0; i < count; i++) free(items[i]);
        free(items);
    }
    return NULL;
}

static void free_split_items(char **items, int count) {
    int i;
    for (i = 0; i < count; i++) free(items[i]);
    free(items);
}

static int parse_column(const char *ident, const char *target,
                        char *out_table, size_t out_table_sz,
                        char *out_col, size_t out_col_sz) {
    const char *dot = strrchr(ident, '.');
    if (dot) {
        size_t tlen = (size_t)(dot - ident);
        char *tmp = str_dup_range(ident, tlen);
        if (!tmp) return -1;
        to_lower_inplace(tmp);
        copy_str(out_table, out_table_sz, tmp);
        free(tmp);
        copy_str(out_col, out_col_sz, dot + 1);
        return 0;
    }
    copy_str(out_table, out_table_sz, target);
    copy_str(out_col, out_col_sz, ident);
    return 0;
}

static int is_keyword(const Token *t, const char *kw) {
    return t && t->type == TOK_IDENT && t->text && strcmp(t->text, kw) == 0;
}

static int is_column_ident(const Token *t) {
    if (!t || t->type != TOK_IDENT || !t->text) return 0;
    if (strcmp(t->text, "and") == 0) return 0;
    if (strcmp(t->text, "or") == 0) return 0;
    if (strcmp(t->text, "in") == 0) return 0;
    if (strcmp(t->text, "like") == 0) return 0;
    return 1;
}

static int is_value_slot(const Token *t) {
    return t && t->type == TOK_SLOT && t->text &&
           (strncmp(t->text, "@value", 6) == 0 || strncmp(t->text, "$value", 6) == 0);
}

static int is_op_token(const Token *t) {
    if (!t || !t->text) return 0;
    if (t->type == TOK_OP) return 1;
    if (t->type == TOK_SLOT && strncmp(t->text, "@op", 3) == 0) return 1;
    return 0;
}

static int parse_policy_atoms(const char *target, Token *toks, int ntok, AtomList *out) {
    for (int i = 0; i < ntok; i++) {
        if (toks[i].type != TOK_IDENT) continue;
        if (!is_column_ident(&toks[i])) continue;

        if (i + 1 < ntok && is_op_token(&toks[i + 1])) {
            const char *op = toks[i + 1].text;
            if (strcmp(op, "<>") == 0)
                op = "!=";
            if (i + 2 < ntok && toks[i + 2].type == TOK_IDENT) {
                if (!is_column_ident(&toks[i + 2])) continue;
                if (strcmp(op, "=") == 0) {
                    PolicyAtom a;
                    memset(&a, 0, sizeof(a));
                    a.type = ATOM_JOIN_EQ;
                    if (parse_column(toks[i].text, target,
                                     a.lhs_table, sizeof(a.lhs_table),
                                     a.lhs_col, sizeof(a.lhs_col)) != 0)
                        return -1;
                    if (parse_column(toks[i + 2].text, target,
                                     a.rhs_table, sizeof(a.rhs_table),
                                     a.rhs_col, sizeof(a.rhs_col)) != 0)
                        return -1;
                    copy_str(a.op, sizeof(a.op), "=");
                    if (atom_push(out, &a) != 0) return -1;
                    continue;
                }
                if (strcmp(op, "!=") == 0 ||
                    strcmp(op, "<") == 0 ||
                    strcmp(op, "<=") == 0 ||
                    strcmp(op, ">") == 0 ||
                    strcmp(op, ">=") == 0 ||
                    toks[i + 1].type == TOK_SLOT) {
                    PolicyAtom a;
                    memset(&a, 0, sizeof(a));
                    a.type = ATOM_COL_COL;
                    if (parse_column(toks[i].text, target,
                                     a.lhs_table, sizeof(a.lhs_table),
                                     a.lhs_col, sizeof(a.lhs_col)) != 0)
                        return -1;
                    if (parse_column(toks[i + 2].text, target,
                                     a.rhs_table, sizeof(a.rhs_table),
                                     a.rhs_col, sizeof(a.rhs_col)) != 0)
                        return -1;
                    copy_str(a.op, sizeof(a.op), op);
                    if (atom_push(out, &a) != 0) return -1;
                    continue;
                }
            } else if (i + 2 < ntok &&
                       (toks[i + 2].type == TOK_STRING || toks[i + 2].type == TOK_NUMBER)) {
                PolicyAtom a;
                memset(&a, 0, sizeof(a));
                a.type = ATOM_COL_CONST;
                if (parse_column(toks[i].text, target,
                                 a.lhs_table, sizeof(a.lhs_table),
                                 a.lhs_col, sizeof(a.lhs_col)) != 0)
                    return -1;
                copy_str(a.op, sizeof(a.op), op);
                copy_str(a.literal, sizeof(a.literal), toks[i + 2].text);
                if (atom_push(out, &a) != 0) return -1;
                continue;
            } else if (i + 2 < ntok && is_value_slot(&toks[i + 2])) {
                PolicyAtom a;
                memset(&a, 0, sizeof(a));
                a.type = ATOM_COL_CONST;
                if (parse_column(toks[i].text, target,
                                 a.lhs_table, sizeof(a.lhs_table),
                                 a.lhs_col, sizeof(a.lhs_col)) != 0)
                    return -1;
                copy_str(a.op, sizeof(a.op), op);
                copy_str(a.literal, sizeof(a.literal), toks[i + 2].text);
                if (atom_push(out, &a) != 0) return -1;
                continue;
            }
        }

        if (i + 1 < ntok && is_keyword(&toks[i + 1], "in"))
            return -1;

        if (i + 1 < ntok && is_keyword(&toks[i + 1], "like"))
            return -1;
    }
    return 0;
}

int parse_policy_file(const char *policy_path, PolicySet *out) {
    if (!out) return -1;
    memset(out, 0, sizeof(*out));

    FILE *fp = fopen(policy_path, "r");
    if (!fp) return -1;

    /* A single policy line can legitimately contain many full-depth Boolean
     * branches.  Keep it intact; splitting at 4 KiB turns the continuation
     * into bogus atoms (for example, lineitem.lineit). */
    char linebuf[65536];
    int mode = 0; /* 0 unknown, 1 old, 2 structured */
    int in_structured = 0;
    int current_policy_id = 0;
    char current_target[POLICY_SPEC_MAX_NAME];
    AtomList current_atoms = {0};
    OccAliasList current_aliases = {0};
    current_target[0] = '\0';

    #define FINISH_STRUCTURED_POLICY() \
        do { \
            if (in_structured) { \
                if (current_policy_id <= 0 || current_target[0] == '\0') { fclose(fp); free_policy_set(out); occ_alias_free(&current_aliases); free(current_atoms.items); return -1; } \
                Policy pol; \
                memset(&pol, 0, sizeof(pol)); \
                copy_str(pol.target_table, sizeof(pol.target_table), current_target); \
                pol.atom_count = current_atoms.count; \
                pol.atoms = current_atoms.items; \
                if (out->policy_count == 0) { \
                    out->policies = (Policy *)malloc(sizeof(Policy)); \
                    if (!out->policies) { fclose(fp); free_policy_set(out); occ_alias_free(&current_aliases); return -1; } \
                    out->policy_count = 1; \
                    out->policies[0] = pol; \
                } else { \
                    int n = out->policy_count + 1; \
                    Policy *np = (Policy *)realloc(out->policies, sizeof(Policy) * n); \
                    if (!np) { fclose(fp); free_policy_set(out); occ_alias_free(&current_aliases); return -1; } \
                    out->policies = np; \
                    out->policies[out->policy_count] = pol; \
                    out->policy_count = n; \
                } \
                current_policy_id = 0; \
                current_target[0] = '\0'; \
                current_atoms.items = NULL; current_atoms.count = 0; current_atoms.cap = 0; \
                occ_alias_free(&current_aliases); \
                in_structured = 0; \
            } \
        } while (0)

    while (fgets(linebuf, sizeof(linebuf), fp) != NULL) {
        char *line = trim_inplace(linebuf);
        if (*line == '\0') continue;
        if (*line == '#') continue;

        {
            char *colon0 = strchr(line, ':');
            if (colon0) {
                int all_digits = 1;
                char *q = line;
                while (q < colon0) {
                    if (!isdigit((unsigned char)*q) && !isspace((unsigned char)*q)) {
                        all_digits = 0;
                        break;
                    }
                    q++;
                }
                if (all_digits && strchr(colon0 + 1, ',') != NULL) {
                    char target[POLICY_SPEC_MAX_NAME];
                    char **items = NULL;
                    int item_count = 0;
                    AtomList atoms = {0};
                    OccAliasList aliases = {0};
                    int ok = 0;
                    char *rhs = trim_inplace(colon0 + 1);
                    items = split_template_csv_items(rhs, &item_count);
                    if (!items || item_count <= 0) { fclose(fp); free_policy_set(out); return -1; }
                    copy_str(target, sizeof(target), items[0]);
                    to_lower_inplace(target);
                    if (target[0] == '\0') { free_split_items(items, item_count); fclose(fp); free_policy_set(out); return -1; }
                    {
                        int i;
                        for (i = 1; i < item_count; i++) {
                            char *item = items[i];
                            if (strncmp(item, "occ ", 4) == 0) {
                                char *rest = trim_inplace(item + 4);
                                char *colon = strchr(rest, ':');
                                if (!colon) goto one_line_fail;
                                *colon = '\0';
                                rest = trim_inplace(rest);
                                colon = trim_inplace(colon + 1);
                                to_lower_inplace(rest);
                                to_lower_inplace(colon);
                                if (occ_alias_push(&aliases, rest, colon) != 0) goto one_line_fail;
                            }
                        }
                        for (i = 1; i < item_count; i++) {
                            char *item = items[i];
                            if (strncmp(item, "atom ", 5) == 0) {
                                char *rest = trim_inplace(item + 5);
                                char *colon = strchr(rest, ':');
                                Token *toks = NULL;
                                int ntok = 0;
                                char *expanded = NULL;
                                if (!colon) goto one_line_fail;
                                *colon = '\0';
                                rest = trim_inplace(colon + 1);
                                expanded = expand_occ_aliases_expr(rest, &aliases);
                                if (!expanded) goto one_line_fail;
                                if (tokenize(expanded, &toks, &ntok) != 0) { free(expanded); goto one_line_fail; }
                                if (parse_policy_atoms(target, toks, ntok, &atoms) != 0) {
                                    free_tokens(toks, ntok);
                                    free(expanded);
                                    goto one_line_fail;
                                }
                                free_tokens(toks, ntok);
                                free(expanded);
                            }
                        }
                    }
                    if (atoms.count <= 0) goto one_line_fail;
                    {
                        Policy pol;
                        memset(&pol, 0, sizeof(pol));
                        copy_str(pol.target_table, sizeof(pol.target_table), target);
                        pol.atom_count = atoms.count;
                        pol.atoms = atoms.items;
                        if (out->policy_count == 0) {
                            out->policies = (Policy *)malloc(sizeof(Policy));
                            if (!out->policies) goto one_line_fail;
                            out->policy_count = 1;
                            out->policies[0] = pol;
                        } else {
                            int n = out->policy_count + 1;
                            Policy *np = (Policy *)realloc(out->policies, sizeof(Policy) * (size_t)n);
                            if (!np) goto one_line_fail;
                            out->policies = np;
                            out->policies[out->policy_count] = pol;
                            out->policy_count = n;
                        }
                    }
                    ok = 1;
one_line_fail:
                    occ_alias_free(&aliases);
                    free_split_items(items, item_count);
                    if (!ok) {
                        free(atoms.items);
                        fclose(fp);
                        free_policy_set(out);
                        return -1;
                    }
                    continue;
                }
            }
        }

        if (mode == 0) {
            if (strncmp(line, "policy ", 7) == 0)
                mode = 2;
            else
                mode = 1;
        }

        if (mode == 2) {
            if (strncmp(line, "policy ", 7) == 0) {
                FINISH_STRUCTURED_POLICY();
                current_policy_id = atoi(trim_inplace(line + 7));
                if (current_policy_id <= 0) { fclose(fp); free_policy_set(out); return -1; }
                in_structured = 1;
                continue;
            }
            if (!in_structured) { fclose(fp); free_policy_set(out); return -1; }
            if (strncmp(line, "target:", 7) == 0) {
                copy_str(current_target, sizeof(current_target), trim_inplace(line + 7));
                to_lower_inplace(current_target);
                continue;
            }
            if (strncmp(line, "occ ", 4) == 0) {
                char *rest = trim_inplace(line + 4);
                char *colon = strchr(rest, ':');
                if (!colon) { fclose(fp); free_policy_set(out); occ_alias_free(&current_aliases); free(current_atoms.items); return -1; }
                *colon = '\0';
                char *alias = trim_inplace(rest);
                char *table = trim_inplace(colon + 1);
                to_lower_inplace(alias);
                to_lower_inplace(table);
                if (occ_alias_push(&current_aliases, alias, table) != 0) { fclose(fp); free_policy_set(out); occ_alias_free(&current_aliases); free(current_atoms.items); return -1; }
                continue;
            }
            if (strncmp(line, "atom ", 5) == 0) {
                char *rest = trim_inplace(line + 5);
                char *colon = strchr(rest, ':');
                Token *toks = NULL;
                int ntok = 0;
                char *expanded = NULL;
                if (!colon) { fclose(fp); free_policy_set(out); occ_alias_free(&current_aliases); free(current_atoms.items); return -1; }
                *colon = '\0';
                rest = trim_inplace(colon + 1);
                expanded = expand_occ_aliases_expr(rest, &current_aliases);
                if (!expanded) { fclose(fp); free_policy_set(out); occ_alias_free(&current_aliases); free(current_atoms.items); return -1; }
                if (tokenize(expanded, &toks, &ntok) != 0) { free(expanded); fclose(fp); free_policy_set(out); occ_alias_free(&current_aliases); free(current_atoms.items); return -1; }
                if (parse_policy_atoms(current_target, toks, ntok, &current_atoms) != 0) { free_tokens(toks, ntok); free(expanded); fclose(fp); free_policy_set(out); occ_alias_free(&current_aliases); free(current_atoms.items); return -1; }
                free_tokens(toks, ntok);
                free(expanded);
                continue;
            }
            if (strncmp(line, "ast:", 4) == 0) {
                continue;
            }
            if (strcmp(line, "end") == 0) {
                FINISH_STRUCTURED_POLICY();
                continue;
            }
            fclose(fp);
            free_policy_set(out);
            occ_alias_free(&current_aliases);
            free(current_atoms.items);
            return -1;
        }

        char *colon = strchr(line, ':');
        if (!colon) continue;
        *colon = '\0';
        char *left = trim_inplace(line);
        char *right = trim_inplace(colon + 1);

        size_t pos = 0;
        while (left[pos] &&
               (isdigit((unsigned char)left[pos]) || left[pos] == '.' || isspace((unsigned char)left[pos])))
            pos++;
        left += pos;
        if (*left == '\0' || *right == '\0') continue;

        char target[POLICY_SPEC_MAX_NAME];
        copy_str(target, sizeof(target), left);
        to_lower_inplace(target);

        Token *toks = NULL;
        int ntok = 0;
        if (tokenize(right, &toks, &ntok) != 0) {
            free_tokens(toks, ntok);
            fclose(fp);
            free_policy_set(out);
            return -1;
        }

        AtomList atoms = {0};
        if (parse_policy_atoms(target, toks, ntok, &atoms) != 0) {
            free_tokens(toks, ntok);
            fclose(fp);
            free_policy_set(out);
            return -1;
        }
        free_tokens(toks, ntok);

        Policy pol;
        memset(&pol, 0, sizeof(pol));
        copy_str(pol.target_table, sizeof(pol.target_table), target);
        pol.atom_count = atoms.count;
        pol.atoms = atoms.items;

        if (out->policy_count == 0) {
            out->policies = (Policy *)malloc(sizeof(Policy));
            if (!out->policies) { fclose(fp); free_policy_set(out); return -1; }
            out->policy_count = 1;
            out->policies[0] = pol;
        } else {
            int n = out->policy_count + 1;
            Policy *np = (Policy *)realloc(out->policies, sizeof(Policy) * n);
            if (!np) { fclose(fp); free_policy_set(out); return -1; }
            out->policies = np;
            out->policies[out->policy_count] = pol;
            out->policy_count = n;
        }
    }
    if (mode == 2)
        FINISH_STRUCTURED_POLICY();
    fclose(fp);
    #undef FINISH_STRUCTURED_POLICY
    return 0;
}

void free_policy_set(PolicySet *ps) {
    if (!ps) return;
    if (ps->policies) {
        for (int i = 0; i < ps->policy_count; i++) {
            if (ps->policies[i].atoms)
                free(ps->policies[i].atoms);
        }
        free(ps->policies);
    }
    ps->policies = NULL;
    ps->policy_count = 0;
}
