#pragma once

#ifdef __cplusplus
extern "C" {
#endif

#define POLICY_SPEC_MAX_NAME 64
#define POLICY_SPEC_MAX_OP 8
#define POLICY_SPEC_MAX_LITERAL 128

typedef enum {
    ATOM_JOIN_EQ = 1,
    ATOM_COL_CONST = 2,
    ATOM_COL_COL = 3
} PolicyAtomType;

typedef struct {
    PolicyAtomType type;
    char lhs_table[POLICY_SPEC_MAX_NAME];
    char lhs_col[POLICY_SPEC_MAX_NAME];
    char rhs_table[POLICY_SPEC_MAX_NAME];
    char rhs_col[POLICY_SPEC_MAX_NAME];
    char op[POLICY_SPEC_MAX_OP];
    char literal[POLICY_SPEC_MAX_LITERAL];
} PolicyAtom;

typedef struct {
    char target_table[POLICY_SPEC_MAX_NAME];
    int atom_count;
    PolicyAtom *atoms;
} Policy;

typedef struct {
    int policy_count;
    Policy *policies;
} PolicySet;

int parse_policy_file(const char *policy_path, PolicySet *out);
void free_policy_set(PolicySet *ps);

#ifdef __cplusplus
}
#endif
