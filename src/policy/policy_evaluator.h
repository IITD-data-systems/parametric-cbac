#pragma once

#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef enum {
    POLICY_ATOM_JOIN_EQ = 1,
    POLICY_ATOM_COL_CONST = 2,
    POLICY_ATOM_COL_COL = 3
} PolicyAtomKindC;

typedef enum {
    POLICY_OP_EQ = 1,
    POLICY_OP_LT = 2,
    POLICY_OP_LE = 3,
    POLICY_OP_GT = 4,
    POLICY_OP_GE = 5,
    POLICY_OP_NE = 6
} PolicyConstOpC;

typedef enum {
    POLICY_AST_TOK_VAR = 1,
    POLICY_AST_TOK_AND = 2,
    POLICY_AST_TOK_OR = 3,
    POLICY_AST_TOK_TRUE = 4,
    POLICY_AST_TOK_FALSE = 5,
    POLICY_AST_TOK_NOT = 6,
    POLICY_AST_TOK_EXISTS = 7
} PolicyAstTokKindC;

typedef enum {
    POLICY_RUNTIME_PATH_CLASS = 1,
    POLICY_RUNTIME_PATH_SMT = 2,
    POLICY_RUNTIME_PATH_HYBRID = 3,
    POLICY_RUNTIME_PATH_WALK = 4
} PolicyRuntimePathC;

typedef struct PolicyAstTokC {
    int kind;   
    int value;  
} PolicyAstTokC;

typedef struct PolicyAtomC {
    int atom_id;                 
    int kind;                    
    int join_class_id;           
    int domain_id;               
    int lhs_node_id;             
    int rhs_node_id;             
    int lhs_table_id;            
    int rhs_table_id;            
    int lhs_col_id;              
    int rhs_col_id;              
    int target_node_id;          
    char *canon_key;             
    char *lhs_schema_key;        
    char *rhs_schema_key;        
    int op;                      
    int const_count;
    char **const_values;         
} PolicyAtomC;

typedef enum {
    POLICY_SCAN_QUAL_COL_CONST = 1,
    POLICY_SCAN_QUAL_COL_COL = 2
} PolicyScanQualKindC;

typedef struct PolicyScanQualAtomC {
    char *target_table;           
    int kind;                     
    char *lhs_schema_key;         
    int op;                       
    char *rhs_schema_key;         
    char *const_value;            
} PolicyScanQualAtomC;

typedef bool (*PolicyArtifactLookupFnC)(void *ctx,
                                        const char *artifact_name,
                                        const void **data_out,
                                        size_t *len_out);

// Normalized policy input consumed by the PAC walk.
typedef struct PolicyEngineInputC {
    int target_count;
    char **target_tables;
    int *target_table_ids;
    int *target_node_ids; 
    char **target_asts;
    char **target_perm_asts;
    char **target_rest_asts;
    int target_ast_tok_len;
    PolicyAstTokC *target_ast_toks;
    int *target_ast_tok_offsets;
    int *target_ast_tok_counts;
    int atom_count;
    PolicyAtomC *atoms;
    int scan_qual_atom_count;
    PolicyScanQualAtomC *scan_qual_atoms;
    int runtime_path; 
    int class_phase_limit;
    int class_phase_timeout_ms;
    PolicyArtifactLookupFnC artifact_lookup_fn;
    void *artifact_lookup_ctx;
    int scanned_count;
    char **scanned_tables;
    const char *policy_text;
} PolicyEngineInputC;

typedef struct PolicyEvalResultC {
    int needed_count;
    char **needed_files;
    int target_count;
    char **target_tables;
    int *target_table_ids;
    int *target_node_ids; 
    char **target_asts;
    char **target_perm_asts;
    char **target_rest_asts;
    int target_ast_tok_len;
    PolicyAstTokC *target_ast_toks;
    int *target_ast_tok_offsets;
    int *target_ast_tok_counts;
    int *target_joinclass_counts;
    int *target_joinclass_offsets;
    int *target_joinclass_ids;
    int target_joinclass_ids_len;
    int exec_target_count;
    char **exec_target_tables;
    int *exec_target_table_ids;
    int *exec_target_node_ids;
    char **exec_target_asts;
    char **exec_target_perm_asts;
    char **exec_target_rest_asts;
    int exec_target_ast_tok_len;
    PolicyAstTokC *exec_target_ast_toks;
    int *exec_target_ast_tok_offsets;
    int *exec_target_ast_tok_counts;
    int atom_count;
    PolicyAtomC *atoms;
    int ast_node_count;
    void **ast_nodes;
    int closure_count;
    char **closure_tables;
    int scanned_count;
    char **scanned_tables;
} PolicyEvalResultC;

PolicyEvalResultC *evaluate_policies_scanned(const char *policy_path,
                                             char **scanned_tables,
                                             int n_scanned);
PolicyEvalResultC *evaluate_policies_text_scanned(const char *policy_text,
                                                  char **scanned_tables,
                                                  int n_scanned);
PolicyEvalResultC *evaluate_policies_c(const char *query_sql, const char *policy_path);
char *bind_policy_template_for_query(const char *template_path,
                                     const char *binding_path,
                                     const char *query_path,
                                     const char *query_id,
                                     const char *query_sql);
void free_policy_eval_result(PolicyEvalResultC *res);

#ifdef __cplusplus
}
#endif
