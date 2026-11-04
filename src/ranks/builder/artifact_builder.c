#include "postgres.h"
#include "fmgr.h"
#include "executor/spi.h"
#include "executor/tuptable.h"
#include "utils/builtins.h"
#include "utils/guc.h"
#include "utils/hsearch.h"
#include "utils/lsyscache.h"
#include "utils/memutils.h"
#include "utils/numeric.h"
#include "utils/snapmgr.h"
#include "utils/timestamp.h"
#include "utils/date.h"
#include "utils/varlena.h"
#include "lib/stringinfo.h"
#include "access/htup_details.h"
#include "access/table.h"
#include "access/tableam.h"
#include "access/xact.h"
#include "catalog/pg_type.h"
#include "catalog/pg_type_d.h"
#include "catalog/namespace.h"
#include "common/hashfn.h"
#include "miscadmin.h"

#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <limits.h>
#include <errno.h>

#include "artifact_builder.hpp"
#include "policy_spec.h"

PG_MODULE_MAGIC;

typedef bool (*emit_invidx_read_fn)(
    void *, const char *, const uint8 **, size_t *);
typedef void (*emit_invidx_write_fn)(
    void *, const char *, const uint8 *, size_t);
extern int emit_invidx_run(
    void *, emit_invidx_read_fn, emit_invidx_write_fn);
extern const char *emit_invidx_last_error(void);

#define FETCH_BATCH 10000

typedef struct {
    char *table;
    char *column;
} ABColumnRef;

typedef struct {
    ABColumnRef *items;
    int count;
    int cap;
} ColumnList;

typedef struct {
    char **items;
    int count;
    int cap;
} StringList;

typedef struct {
    int a;
    int b;
} HubPair;

typedef struct {
    int *items;
    int count;
    int cap;
} IntList;

typedef struct {
    int id;
    IntList cols;
    HTAB *tok_map;
    int32 next_tok;
    int type_class;
} HubClass;

typedef struct {
    int col_idx;
    int is_hub;
    int hub_class_id;
    int const_col_idx;
    HTAB *tok_map;
    AttrNumber attnum;
    Oid typid;
    Oid typoutput;
    bool typisvarlena;
} TokenColumn;

typedef struct {
    int col_idx;
    int hub_class_id;
    AttrNumber attnum;
    Oid typid;
    Oid typoutput;
    bool typisvarlena;
} HubTokCol;

typedef struct {
    ABColumnRef col;
    HTAB *tok_map;
    int32 next_tok;
    Oid typid;
    bool uses_hub_map;
    int hub_class_id;
} ConstColumn;

typedef enum {
    DICT_KEY_TEXT = 0,
    DICT_KEY_INT64 = 1,
    DICT_KEY_BYTES = 2
} DictKeyKind;

typedef struct DictTokEntry DictTokEntry;
struct DictTokEntry {
    uint64 hkey;
    int32 tok;
    int32 blen;
    DictKeyKind key_kind;
    int64 ival;
    char *val;
    DictTokEntry *next;
};

typedef enum {
    HUB_TYPE_UNSUPPORTED = 0,
    HUB_TYPE_NUMERIC = 1,
    HUB_TYPE_DATE = 2,
    HUB_TYPE_TEXT = 3
} HubTypeClass;

static void str_list_add_unique(StringList *list, const char *value) {
    for (int i = 0; i < list->count; i++) {
        if (strcmp(list->items[i], value) == 0) {
            return;
        }
    }
    if (list->count == list->cap) {
        int newcap = list->cap == 0 ? 8 : list->cap * 2;
        if (list->items) {
            list->items = (char **)repalloc(list->items, newcap * sizeof(char *));
        } else {
            list->items = (char **)palloc(newcap * sizeof(char *));
        }
        list->cap = newcap;
    }
    list->items[list->count++] = pstrdup(value);
}

static int column_index(const ColumnList *cols, const char *table, const char *col) {
    for (int i = 0; i < cols->count; i++) {
        if (strcmp(cols->items[i].table, table) == 0 && strcmp(cols->items[i].column, col) == 0) {
            return i;
        }
    }
    return -1;
}

static int column_add_unique(ColumnList *cols, const char *table, const char *col) {
    int idx = column_index(cols, table, col);
    if (idx >= 0) return idx;
    if (cols->count == cols->cap) {
        int newcap = cols->cap == 0 ? 16 : cols->cap * 2;
        if (cols->items) {
            cols->items = (ABColumnRef *)repalloc(cols->items, newcap * sizeof(ABColumnRef));
        } else {
            cols->items = (ABColumnRef *)palloc(newcap * sizeof(ABColumnRef));
        }
        cols->cap = newcap;
    }
    cols->items[cols->count].table = pstrdup(table);
    cols->items[cols->count].column = pstrdup(col);
    return cols->count++;
}

static void int_list_add(IntList *list, int value) {
    if (list->count == list->cap) {
        int newcap = list->cap == 0 ? 8 : list->cap * 2;
        if (list->items) {
            list->items = (int *)repalloc(list->items, newcap * sizeof(int));
        } else {
            list->items = (int *)palloc(newcap * sizeof(int));
        }
        list->cap = newcap;
    }
    list->items[list->count++] = value;
}


static void sort_string_list(StringList *list) {
    if (!list || list->count <= 1) return;
    for (int i = 0; i < list->count; i++) {
        for (int j = i + 1; j < list->count; j++) {
            if (strcmp(list->items[i], list->items[j]) > 0) {
                char *tmp = list->items[i];
                list->items[i] = list->items[j];
                list->items[j] = tmp;
            }
        }
    }
}

static void sort_columns_by_name(const ColumnList *cols, IntList *idxs) {
    if (!cols || !idxs || idxs->count <= 1) return;
    for (int i = 0; i < idxs->count; i++) {
        for (int j = i + 1; j < idxs->count; j++) {
            int ai = idxs->items[i];
            int bi = idxs->items[j];
            int cmp = strcmp(cols->items[ai].table, cols->items[bi].table);
            if (cmp == 0) cmp = strcmp(cols->items[ai].column, cols->items[bi].column);
            if (cmp > 0) {
                int tmp = idxs->items[i];
                idxs->items[i] = idxs->items[j];
                idxs->items[j] = tmp;
            }
        }
    }
}

static bytea *cstring_to_bytea(const char *s) {
    if (!s) s = "";
    int len = (int)strlen(s);
    bytea *ba = (bytea *)palloc(VARHDRSZ + len);
    SET_VARSIZE(ba, VARHDRSZ + len);
    if (len > 0) memcpy(VARDATA(ba), s, len);
    return ba;
}

static inline double elapsed_ms(TimestampTz t0)
{
    return ((double) (GetCurrentTimestamp() - t0)) / 1000.0;
}

static SPIPlanPtr g_insert_file_plan = NULL;
static SPIPlanPtr g_read_artifact_plan = NULL;

static char *
files_table_sql_ident(bool *is_default_out)
{
    const char *cfg = GetConfigOption("custom_filter_new.files_table", true, false);
    const char *raw = (cfg && cfg[0]) ? cfg : "public.files";
    const char *dot = strchr(raw, '.');
    bool is_default = (strcmp(raw, "public.files") == 0);
    char *out = NULL;

    if (dot && strchr(dot + 1, '.') == NULL)
    {
        char *schema = pnstrdup(raw, dot - raw);
        char *table = pstrdup(dot + 1);
        out = quote_qualified_identifier(schema, table);
        pfree(schema);
        pfree(table);
    }
    else
    {
        out = pstrdup(quote_identifier(raw));
    }

    if (is_default_out)
        *is_default_out = is_default;
    return out;
}

static void prepare_insert_file_plan(void)
{
    Oid argtypes[2] = {TEXTOID, BYTEAOID};
    char *table_sql = files_table_sql_ident(NULL);
    char *sql = psprintf(
        "INSERT INTO %s (run_id, name, file) "
        "VALUES (COALESCE(current_setting('custom_filter_new.run_id', true), ''), $1, $2)",
        table_sql);
    SPIPlanPtr plan = SPI_prepare(sql, 2, argtypes);
    pfree(sql);
    pfree(table_sql);
    if (!plan)
        ereport(ERROR, (errmsg("artifact_builder: SPI_prepare insert plan failed")));
    g_insert_file_plan = SPI_saveplan(plan);
    SPI_freeplan(plan);
    if (!g_insert_file_plan)
        ereport(ERROR, (errmsg("artifact_builder: SPI_saveplan insert plan failed")));
}

static void insert_file(const char *name, bytea *data) {
    Datum values[2];
    char nulls[2] = {' ', ' '};
    if (!g_insert_file_plan)
        ereport(ERROR, (errmsg("artifact_builder: insert plan not initialized")));
    values[0] = CStringGetTextDatum(name);
    values[1] = PointerGetDatum(data);
    int ret = SPI_execute_plan(g_insert_file_plan, values, nulls, false, 0);
    if (ret != SPI_OK_INSERT)
        ereport(ERROR, (errmsg("failed to insert file %s", name)));
}

static void insert_file_text(const char *name, const char *text) {
    bytea *ba = cstring_to_bytea(text);
    insert_file(name, ba);
}

typedef struct {
    MemoryContext memory_context;
    uint8 *read_buffer;
} EmitInvidxContext;

static void
prepare_read_artifact_plan(void)
{
    Oid argtypes[1] = {TEXTOID};
    char *table_sql = files_table_sql_ident(NULL);
    char *sql = psprintf(
        "SELECT file FROM %s "
        "WHERE COALESCE(run_id,'') = "
        "COALESCE(current_setting('custom_filter_new.run_id', true), '') "
        "AND name = $1 ORDER BY ctid DESC LIMIT 2",
        table_sql);
    SPIPlanPtr plan = SPI_prepare(sql, 1, argtypes);
    pfree(sql);
    pfree(table_sql);
    if (!plan)
        ereport(ERROR,
                (errmsg("artifact_builder: SPI_prepare read plan failed")));
    g_read_artifact_plan = SPI_saveplan(plan);
    SPI_freeplan(plan);
    if (!g_read_artifact_plan)
        ereport(ERROR,
                (errmsg("artifact_builder: SPI_saveplan read plan failed")));
}

static bool
pg_read_artifact(void *opaque, const char *name,
                 const uint8 **data, size_t *len)
{
    EmitInvidxContext *context = (EmitInvidxContext *) opaque;
    Datum values[1];
    char nulls[1] = {' '};
    int result;

    if (!g_read_artifact_plan)
        ereport(ERROR,
                (errmsg("artifact_builder: read plan not initialized")));
    values[0] = CStringGetTextDatum(name);
    result = SPI_execute_plan(
        g_read_artifact_plan, values, nulls, true, 2);
    if (result != SPI_OK_SELECT)
        ereport(ERROR,
                (errmsg("artifact_builder: failed to read artifact %s",
                        name)));
    if (SPI_processed == 0) {
        *data = NULL;
        *len = 0;
        return false;
    }
    if (SPI_processed != 1)
        ereport(ERROR,
                (errmsg("artifact_builder: duplicate artifact %s", name)));

    bool is_null = false;
    Datum datum = SPI_getbinval(
        SPI_tuptable->vals[0], SPI_tuptable->tupdesc, 1, &is_null);
    if (is_null)
        ereport(ERROR,
                (errmsg("artifact_builder: null artifact %s", name)));
    bytea *value = DatumGetByteaPP(datum);
    const size_t value_len = (size_t) VARSIZE_ANY_EXHDR(value);

    MemoryContext old_context =
        MemoryContextSwitchTo(context->memory_context);
    if (context->read_buffer)
        pfree(context->read_buffer);
    context->read_buffer = value_len ? (uint8 *) palloc(value_len) : NULL;
    if (value_len)
        memcpy(context->read_buffer, VARDATA_ANY(value), value_len);
    MemoryContextSwitchTo(old_context);

    *data = context->read_buffer;
    *len = value_len;
    return true;
}

static void
pg_write_artifact(void *opaque, const char *name,
                  const uint8 *data, size_t len)
{
    (void) opaque;
    if (len > (size_t) (MaxAllocSize - VARHDRSZ))
        ereport(ERROR,
                (errmsg("artifact_builder: artifact too large %s", name)));
    bytea *value = (bytea *) palloc(VARHDRSZ + len);
    SET_VARSIZE(value, VARHDRSZ + len);
    if (len)
        memcpy(VARDATA(value), data, len);
    insert_file(name, value);
    pfree(value);
}

static uint16
bit_width_u32(uint32 v)
{
    uint16 bw = 1;
    while ((v >> bw) != 0 && bw < 32)
        bw++;
    return bw;
}

static void
flush_code_col_chunks(const char *table,
                      int chunk_idx,
                      uint32 chunk_rows,
                      const int32 *chunk_tokens,
                      int token_count)
{
    if (!table || chunk_rows == 0 || token_count <= 0 || !chunk_tokens)
        return;

    for (int col = 0; col < token_count; col++) {
        uint32 max_enc = 0;
        for (uint32 r = 0; r < chunk_rows; r++) {
            int32 tok = chunk_tokens[(size_t)r * (size_t)token_count + (size_t)col];
            uint32 enc = (tok < 0) ? 0u : (uint32)tok + 1u;
            if (enc > max_enc)
                max_enc = enc;
        }
        uint16 bw = bit_width_u32(max_enc);
        size_t payload_bits = (size_t)chunk_rows * (size_t)bw;
        size_t payload_len = (payload_bits + 7u) / 8u;
        if (payload_len > (size_t)INT32_MAX)
            ereport(ERROR, (errmsg("code column payload too large table=%s col=%d chunk=%d bytes=%zu",
                                   table, col, chunk_idx, payload_len)));

        uint8 *payload = payload_len > 0 ? (uint8 *)palloc0(payload_len) : NULL;
        size_t out_pos = 0;
        uint64 acc = 0;
        int acc_bits = 0;
        for (uint32 r = 0; r < chunk_rows; r++) {
            int32 tok = chunk_tokens[(size_t)r * (size_t)token_count + (size_t)col];
            uint32 enc = (tok < 0) ? 0u : (uint32)tok + 1u;
            acc |= ((uint64)enc) << acc_bits;
            acc_bits += (int)bw;
            while (acc_bits >= 8) {
                if (out_pos >= payload_len)
                    ereport(ERROR, (errmsg("code column pack overflow table=%s col=%d chunk=%d",
                                           table, col, chunk_idx)));
                payload[out_pos++] = (uint8)(acc & 0xFFu);
                acc >>= 8;
                acc_bits -= 8;
            }
        }
        if (acc_bits > 0) {
            if (out_pos >= payload_len)
                ereport(ERROR, (errmsg("code column tail overflow table=%s col=%d chunk=%d",
                                       table, col, chunk_idx)));
            payload[out_pos++] = (uint8)(acc & 0xFFu);
        }
        if (out_pos != payload_len)
            ereport(ERROR, (errmsg("code column pack size mismatch table=%s col=%d chunk=%d out=%zu payload=%zu",
                                   table, col, chunk_idx, out_pos, payload_len)));

        ByteaBuilder *bb = bb_create();
        const char magic[4] = {'C', 'C', '0', '4'};
        bb_append_bytes(bb, magic, sizeof(magic));
        bb_append_int32(bb, (int32)chunk_rows);
        bb_append_bytes(bb, &bw, sizeof(uint16));
        {
            uint16 reserved = 0;
            bb_append_bytes(bb, &reserved, sizeof(uint16));
        }
        bb_append_int32(bb, (int32)payload_len);
        if (payload_len > 0)
            bb_append_bytes(bb, payload, payload_len);

        char chunk_name[NAMEDATALEN * 3];
        snprintf(chunk_name, sizeof(chunk_name), "%s_code_col_%d_chunk_%d", table, col, chunk_idx);
        bytea *chunk_ba = bb_to_bytea(bb);
        insert_file(chunk_name, chunk_ba);
        if (chunk_ba)
            pfree(chunk_ba);
        bb_free(bb);
        if (payload)
            pfree(payload);
    }
}

static size_t estimate_table_rows(const char *table) {
    Oid argtypes[1] = {TEXTOID};
    Datum values[1];
    char nulls[1] = {' '};
    values[0] = CStringGetTextDatum(table);
    int ret = SPI_execute_with_args(
        "SELECT GREATEST(COALESCE(c.reltuples, 0), 0)::bigint "
        "FROM pg_class c "
        "JOIN pg_namespace n ON n.oid = c.relnamespace "
        "WHERE n.nspname = 'public' AND c.relname = $1",
        1, argtypes, values, nulls, true, 1);
    if (ret != SPI_OK_SELECT || SPI_processed == 0)
        return 0;
    bool isnull = false;
    Datum d = SPI_getbinval(SPI_tuptable->vals[0], SPI_tuptable->tupdesc, 1, &isnull);
    if (isnull)
        return 0;
    int64 est = DatumGetInt64(d);
    if (est <= 0)
        return 0;
    return (size_t) est;
}

static Oid column_type_oid(const char *table, const char *col) {
    if (!table || !col) return InvalidOid;
    Oid argtypes[2] = {TEXTOID, TEXTOID};
    Datum values[2];
    char nulls[2] = {' ', ' '};
    values[0] = CStringGetTextDatum(table);
    values[1] = CStringGetTextDatum(col);
    int ret = SPI_execute_with_args(
        "SELECT a.atttypid "
        "FROM pg_attribute a "
        "JOIN pg_class c ON c.oid = a.attrelid "
        "JOIN pg_namespace n ON n.oid = c.relnamespace "
        "WHERE c.relname = $1 AND a.attname = $2 "
        "AND a.attnum > 0 AND NOT a.attisdropped "
        "AND n.nspname = 'public'",
        2, argtypes, values, nulls, true, 0);
    if (ret != SPI_OK_SELECT || SPI_processed == 0)
        return InvalidOid;
    bool isnull = false;
    Datum d = SPI_getbinval(SPI_tuptable->vals[0], SPI_tuptable->tupdesc, 1, &isnull);
    if (isnull)
        return InvalidOid;
    return DatumGetObjectId(d);
}

static HubTypeClass hub_type_class_for_oid(Oid typid)
{
    if (typid == INT2OID || typid == INT4OID || typid == INT8OID || typid == NUMERICOID)
        return HUB_TYPE_NUMERIC;
    if (typid == DATEOID)
        return HUB_TYPE_DATE;
    if (typid == TEXTOID || typid == VARCHAROID || typid == BPCHAROID)
        return HUB_TYPE_TEXT;
    return HUB_TYPE_UNSUPPORTED;
}

static const char *hub_type_class_name(HubTypeClass tc)
{
    switch (tc) {
        case HUB_TYPE_NUMERIC: return "numeric";
        case HUB_TYPE_DATE: return "date";
        case HUB_TYPE_TEXT: return "text";
        default: break;
    }
    return "unsupported";
}

static Oid dict_typid_for_hub_type_class(HubTypeClass tc)
{
    switch (tc) {
        case HUB_TYPE_NUMERIC: return NUMERICOID;
        case HUB_TYPE_DATE: return DATEOID;
        case HUB_TYPE_TEXT: return TEXTOID;
        default: break;
    }
    return TEXTOID;
}

static char *normalize_numeric_string(const char *src)
{
    if (!src)
        return pstrdup("0");
    const char *p = src;
    while (*p && isspace((unsigned char)*p))
        p++;

    bool neg = false;
    if (*p == '+' || *p == '-') {
        neg = (*p == '-');
        p++;
    }

    const char *mant_start = p;
    const char *exp_pos = NULL;
    for (const char *q = p; *q; q++) {
        if (*q == 'e' || *q == 'E') {
            exp_pos = q;
            break;
        }
    }
    const char *mant_end = exp_pos ? exp_pos : (p + strlen(p));
    while (mant_end > mant_start && isspace((unsigned char)mant_end[-1]))
        mant_end--;

    const char *dot = NULL;
    for (const char *q = mant_start; q < mant_end; q++) {
        if (*q == '.') {
            dot = q;
            break;
        }
    }

    const char *int_start = mant_start;
    const char *int_end = dot ? dot : mant_end;
    while (int_start < int_end && *int_start == '0')
        int_start++;
    bool int_is_zero = (int_start == int_end);

    const char *frac_start = dot ? (dot + 1) : mant_end;
    const char *frac_end = mant_end;
    while (frac_end > frac_start && frac_end[-1] == '0')
        frac_end--;

    StringInfoData out;
    initStringInfo(&out);
    if (neg)
        appendStringInfoChar(&out, '-');
    if (!int_is_zero)
        appendBinaryStringInfo(&out, int_start, int_end - int_start);
    else
        appendStringInfoChar(&out, '0');
    if (frac_end > frac_start) {
        appendStringInfoChar(&out, '.');
        appendBinaryStringInfo(&out, frac_start, frac_end - frac_start);
    }

    if (exp_pos) {
        const char *e = exp_pos + 1;
        while (*e && isspace((unsigned char)*e))
            e++;
        bool e_neg = false;
        if (*e == '+' || *e == '-') {
            e_neg = (*e == '-');
            e++;
        }
        while (*e == '0')
            e++;
        if (*e) {
            appendStringInfoChar(&out, 'e');
            if (e_neg)
                appendStringInfoChar(&out, '-');
            appendStringInfoString(&out, e);
        }
    }

    /* Canonicalize signed zero -> zero. */
    if (strcmp(out.data, "-0") == 0)
        out.data[0] = '0', out.data[1] = '\0';
    return out.data;
}

static const char *dict_type_label_for_oid(Oid typid) {
    if (typid == INT2OID || typid == INT4OID || typid == INT8OID)
        return "int";
    if (typid == DATEOID)
        return "date";
    if (typid == NUMERICOID)
        return "numeric";
    if (typid == FLOAT4OID || typid == FLOAT8OID)
        return "float";
    if (typid == BPCHAROID)
        return "bpchar";
    return "text";
}

static uint64 dict_hash_key_text(const char *val) {
    if (!val) return 0;
    return hash_bytes_extended((const unsigned char *)val, strlen(val), 0);
}

static uint64 dict_hash_key_bytes(const char *data, int32 len)
{
    if (!data || len <= 0)
        return 0;
    return hash_bytes_extended((const unsigned char *) data, (size_t) len, 0);
}

static uint64 dict_hash_key_int64(int64 ival)
{
    return hash_bytes_extended((const unsigned char *) &ival, sizeof(int64), 0);
}

static inline bool dict_typid_uses_intkey(Oid typid)
{
    return typid == INT2OID || typid == INT4OID || typid == INT8OID ||
           typid == OIDOID || typid == DATEOID;
}

static inline int64 dict_datum_to_intkey(Oid typid, Datum v)
{
    switch (typid) {
        case INT2OID:
            return (int64) DatumGetInt16(v);
        case INT4OID:
            return (int64) DatumGetInt32(v);
        case INT8OID:
            return (int64) DatumGetInt64(v);
        case OIDOID:
            return (int64) DatumGetObjectId(v);
        case DATEOID:
            return (int64) DatumGetDateADT(v);
        default:
            ereport(ERROR, (errmsg("artifact_builder: unsupported int-key typid=%u", typid)));
    }
    return 0;
}

static inline bool dict_typid_uses_bytekey(Oid typid)
{
    return typid == TEXTOID || typid == VARCHAROID ||
           typid == BPCHAROID || typid == NUMERICOID;
}

static HTAB *dict_map_create(const char *name, long est_rows, MemoryContext mcxt) {
    HASHCTL ctl;
    memset(&ctl, 0, sizeof(ctl));
    ctl.keysize = sizeof(uint64);
    ctl.entrysize = sizeof(DictTokEntry);
    ctl.hcxt = mcxt;
    if (est_rows < 128) est_rows = 128;
    return hash_create(name, est_rows, &ctl, HASH_ELEM | HASH_BLOBS | HASH_CONTEXT);
}

static int32 dict_map_get_or_insert_text(HTAB *map,
                                         MemoryContext mcxt,
                                         const char *val,
                                         int32 *next_tok,
                                         bool *out_inserted)
{
    bool found = false;
    uint64 hkey = dict_hash_key_text(val);
    DictTokEntry *head = (DictTokEntry *) hash_search(map, &hkey, HASH_ENTER, &found);
    if (!head)
        ereport(ERROR, (errmsg("artifact_builder: hash insert failed")));

    if (!found) {
        int32 tok = *next_tok;
        (*next_tok)++;
        head->hkey = hkey;
        head->tok = tok;
        head->blen = val ? (int32) strlen(val) : 0;
        head->key_kind = DICT_KEY_TEXT;
        head->ival = 0;
        head->val = MemoryContextStrdup(mcxt, val);
        head->next = NULL;
        if (out_inserted) *out_inserted = true;
        return tok;
    }

    for (DictTokEntry *cur = head; cur; cur = cur->next) {
        if (cur->key_kind == DICT_KEY_TEXT && cur->val && strcmp(cur->val, val) == 0) {
            if (out_inserted) *out_inserted = false;
            return cur->tok;
        }
        if (!cur->next) {
            int32 tok = *next_tok;
            (*next_tok)++;
            DictTokEntry *extra = (DictTokEntry *) MemoryContextAlloc(mcxt, sizeof(DictTokEntry));
            extra->hkey = hkey;
            extra->tok = tok;
            extra->blen = val ? (int32) strlen(val) : 0;
            extra->key_kind = DICT_KEY_TEXT;
            extra->ival = 0;
            extra->val = MemoryContextStrdup(mcxt, val);
            extra->next = NULL;
            cur->next = extra;
            if (out_inserted) *out_inserted = true;
            return tok;
        }
    }

    ereport(ERROR, (errmsg("artifact_builder: unreachable in dict_map_get_or_insert_text")));
    return -1;
}

static int32 dict_map_get_or_insert_int64(HTAB *map,
                                          MemoryContext mcxt,
                                          int64 ival,
                                          int32 *next_tok,
                                          bool *out_inserted)
{
    bool found = false;
    uint64 hkey = dict_hash_key_int64(ival);
    DictTokEntry *head = (DictTokEntry *) hash_search(map, &hkey, HASH_ENTER, &found);
    if (!head)
        ereport(ERROR, (errmsg("artifact_builder: hash insert failed")));

    if (!found) {
        int32 tok = *next_tok;
        (*next_tok)++;
        head->hkey = hkey;
        head->tok = tok;
        head->blen = 0;
        head->key_kind = DICT_KEY_INT64;
        head->ival = ival;
        head->val = NULL;
        head->next = NULL;
        if (out_inserted) *out_inserted = true;
        return tok;
    }

    for (DictTokEntry *cur = head; cur; cur = cur->next) {
        if (cur->key_kind == DICT_KEY_INT64 && cur->ival == ival) {
            if (out_inserted) *out_inserted = false;
            return cur->tok;
        }
        if (!cur->next) {
            int32 tok = *next_tok;
            (*next_tok)++;
            DictTokEntry *extra = (DictTokEntry *) MemoryContextAlloc(mcxt, sizeof(DictTokEntry));
            extra->hkey = hkey;
            extra->tok = tok;
            extra->blen = 0;
            extra->key_kind = DICT_KEY_INT64;
            extra->ival = ival;
            extra->val = NULL;
            extra->next = NULL;
            cur->next = extra;
            if (out_inserted) *out_inserted = true;
            return tok;
        }
    }

    ereport(ERROR, (errmsg("artifact_builder: unreachable in dict_map_get_or_insert_int64")));
    return -1;
}

static int32 dict_map_get_or_insert_bytes(HTAB *map,
                                          MemoryContext mcxt,
                                          const char *data,
                                          int32 len,
                                          int32 *next_tok,
                                          bool *out_inserted)
{
    bool found = false;
    uint64 hkey = dict_hash_key_bytes(data, len);
    DictTokEntry *head = (DictTokEntry *) hash_search(map, &hkey, HASH_ENTER, &found);
    if (!head)
        ereport(ERROR, (errmsg("artifact_builder: hash insert failed")));

    if (!found) {
        int32 tok = *next_tok;
        (*next_tok)++;
        head->hkey = hkey;
        head->tok = tok;
        head->blen = len;
        head->key_kind = DICT_KEY_BYTES;
        head->ival = 0;
        if (len > 0) {
            head->val = (char *) MemoryContextAlloc(mcxt, (size_t) len + 1);
            memcpy(head->val, data, (size_t) len);
            head->val[len] = '\0';
        } else {
            head->val = NULL;
        }
        head->next = NULL;
        if (out_inserted) *out_inserted = true;
        return tok;
    }

    for (DictTokEntry *cur = head; cur; cur = cur->next) {
        if (cur->key_kind == DICT_KEY_BYTES && cur->blen == len) {
            if (len == 0 || (cur->val && data && memcmp(cur->val, data, (size_t) len) == 0)) {
                if (out_inserted) *out_inserted = false;
                return cur->tok;
            }
        }
        if (!cur->next) {
            int32 tok = *next_tok;
            (*next_tok)++;
            DictTokEntry *extra = (DictTokEntry *) MemoryContextAlloc(mcxt, sizeof(DictTokEntry));
            extra->hkey = hkey;
            extra->tok = tok;
            extra->blen = len;
            extra->key_kind = DICT_KEY_BYTES;
            extra->ival = 0;
            if (len > 0) {
                extra->val = (char *) MemoryContextAlloc(mcxt, (size_t) len + 1);
                memcpy(extra->val, data, (size_t) len);
                extra->val[len] = '\0';
            } else {
                extra->val = NULL;
            }
            extra->next = NULL;
            cur->next = extra;
            if (out_inserted) *out_inserted = true;
            return tok;
        }
    }

    ereport(ERROR, (errmsg("artifact_builder: unreachable in dict_map_get_or_insert_bytes")));
    return -1;
}

static void write_dict_from_map(const char *name, HTAB *map, int32 n_tokens, Oid dict_typid)
{
    if (!name || !map || n_tokens < 0)
        ereport(ERROR, (errmsg("artifact_builder: invalid write_dict_from_map args")));

    DictTokEntry **vals = NULL;
    if (n_tokens > 0)
        vals = (DictTokEntry **) palloc0(sizeof(DictTokEntry *) * (size_t) n_tokens);

    HASH_SEQ_STATUS seq;
    hash_seq_init(&seq, map);
    DictTokEntry *head = NULL;
    while ((head = (DictTokEntry *) hash_seq_search(&seq)) != NULL) {
        for (DictTokEntry *cur = head; cur; cur = cur->next) {
            if (cur->tok < 0 || cur->tok >= n_tokens)
                ereport(ERROR, (errmsg("artifact_builder: dict token out of range tok=%d n=%d", cur->tok, n_tokens)));
            vals[cur->tok] = cur;
        }
    }

    Oid typed_out_func = InvalidOid;
    bool typed_out_varlena = false;
    if (dict_typid == DATEOID || dict_typid == NUMERICOID)
        getTypeOutputInfo(dict_typid, &typed_out_func, &typed_out_varlena);
    (void) typed_out_varlena;

    ByteaBuilder *bb = bb_create();
    for (int32 tok = 0; tok < n_tokens; tok++) {
        DictTokEntry *ent = vals ? vals[tok] : NULL;
        const char *val = NULL;
        char intbuf[64];
        int32 len = 0;
        char *tmp_out = NULL;
        struct varlena *tmp_num = NULL;

        if (ent) {
            if (ent->key_kind == DICT_KEY_TEXT) {
                val = ent->val ? ent->val : "";
                len = (int32) strlen(val);
            } else if (ent->key_kind == DICT_KEY_INT64) {
                if (dict_typid == DATEOID) {
                    tmp_out = OidOutputFunctionCall(typed_out_func, DateADTGetDatum((DateADT) ent->ival));
                    val = tmp_out ? tmp_out : "";
                    len = (int32) strlen(val);
                } else {
                    len = (int32) snprintf(intbuf, sizeof(intbuf), "%lld", (long long) ent->ival);
                    if (len < 0)
                        len = 0;
                    val = intbuf;
                }
            } else if (ent->key_kind == DICT_KEY_BYTES) {
                if (dict_typid == NUMERICOID) {
                    tmp_num = (struct varlena *) palloc((size_t) ent->blen + VARHDRSZ);
                    SET_VARSIZE(tmp_num, (size_t) ent->blen + VARHDRSZ);
                    if (ent->blen > 0)
                        memcpy(VARDATA(tmp_num), ent->val, (size_t) ent->blen);
                    tmp_out = OidOutputFunctionCall(typed_out_func, PointerGetDatum(tmp_num));
                    val = tmp_out ? tmp_out : "";
                    len = (int32) strlen(val);
                } else {
                    val = ent->val ? ent->val : "";
                    len = ent->blen > 0 ? ent->blen : 0;
                }
            }
        }

        bb_append_int32(bb, len);
        if (len > 0)
            bb_append_bytes(bb, val, (size_t) len);
        if (tmp_out)
            pfree(tmp_out);
        if (tmp_num)
            pfree(tmp_num);
    }
    insert_file(name, bb_to_bytea(bb));
    bb_free(bb);
    if (vals)
        pfree(vals);
}

typedef struct {
    int32 tok;
    int64 ival;
    bool has_ival;
    double num;
    bool has_num;
    Numeric numv;
    char *txt;
} RankTok;

static int cmp_ranktok(const void *ap, const void *bp, void *arg)
{
    Oid typid = *((Oid *)arg);
    const RankTok *a = (const RankTok *)ap;
    const RankTok *b = (const RankTok *)bp;

    if (dict_typid_uses_intkey(typid) && a->has_ival && b->has_ival) {
        if (a->ival < b->ival) return -1;
        if (a->ival > b->ival) return 1;
    } else if (typid == NUMERICOID && a->numv && b->numv) {
        int32 cmp = DatumGetInt32(DirectFunctionCall2(numeric_cmp,
                                                      NumericGetDatum(a->numv),
                                                      NumericGetDatum(b->numv)));
        if (cmp < 0) return -1;
        if (cmp > 0) return 1;
    } else if ((typid == FLOAT4OID || typid == FLOAT8OID || typid == NUMERICOID) &&
               a->has_num && b->has_num) {
        if (a->num < b->num) return -1;
        if (a->num > b->num) return 1;
    } else {
        const char *at = a->txt ? a->txt : "";
        const char *bt = b->txt ? b->txt : "";
        int c = strcmp(at, bt);
        if (c != 0) return c;
    }
    if (a->tok < b->tok) return -1;
    if (a->tok > b->tok) return 1;
    return 0;
}

static void write_rank_from_map(const char *name, HTAB *map, int32 n_tokens, Oid dict_typid)
{
    if (!name || !map || n_tokens < 0)
        ereport(ERROR, (errmsg("artifact_builder: invalid write_rank_from_map args")));

    RankTok *rows = NULL;
    DictTokEntry **vals = NULL;
    if (n_tokens > 0) {
        rows = (RankTok *)palloc0(sizeof(RankTok) * (size_t)n_tokens);
        vals = (DictTokEntry **)palloc0(sizeof(DictTokEntry *) * (size_t)n_tokens);
    }

    HASH_SEQ_STATUS seq;
    hash_seq_init(&seq, map);
    DictTokEntry *head = NULL;
    while ((head = (DictTokEntry *) hash_seq_search(&seq)) != NULL) {
        for (DictTokEntry *cur = head; cur; cur = cur->next) {
            if (cur->tok < 0 || cur->tok >= n_tokens)
                ereport(ERROR, (errmsg("artifact_builder: rank token out of range tok=%d n=%d", cur->tok, n_tokens)));
            vals[cur->tok] = cur;
        }
    }

    Oid typed_out_func = InvalidOid;
    bool typed_out_varlena = false;
    if (dict_typid == DATEOID || dict_typid == NUMERICOID)
        getTypeOutputInfo(dict_typid, &typed_out_func, &typed_out_varlena);
    (void)typed_out_varlena;

    for (int32 tok = 0; tok < n_tokens; tok++) {
        RankTok *rt = &rows[tok];
        rt->tok = tok;
        rt->ival = 0;
        rt->has_ival = false;
        rt->num = 0.0;
        rt->has_num = false;
        rt->numv = NULL;
        rt->txt = NULL;

        DictTokEntry *ent = vals ? vals[tok] : NULL;
        if (!ent)
            continue;

        char intbuf[64];
        const char *val = "";
        int32 vlen = 0;
        char *tmp_out = NULL;
        struct varlena *tmp_num = NULL;

        if (ent->key_kind == DICT_KEY_TEXT) {
            val = ent->val ? ent->val : "";
            vlen = (int32)strlen(val);
        } else if (ent->key_kind == DICT_KEY_INT64) {
            rt->ival = ent->ival;
            rt->has_ival = true;
            if (dict_typid == DATEOID) {
                tmp_out = OidOutputFunctionCall(typed_out_func, DateADTGetDatum((DateADT)ent->ival));
                val = tmp_out ? tmp_out : "";
                vlen = (int32)strlen(val);
            } else {
                vlen = (int32)snprintf(intbuf, sizeof(intbuf), "%lld", (long long)ent->ival);
                if (vlen < 0) vlen = 0;
                val = intbuf;
            }
        } else if (ent->key_kind == DICT_KEY_BYTES) {
            if (dict_typid == NUMERICOID) {
                tmp_num = (struct varlena *)palloc((size_t)ent->blen + VARHDRSZ);
                SET_VARSIZE(tmp_num, (size_t)ent->blen + VARHDRSZ);
                if (ent->blen > 0)
                    memcpy(VARDATA(tmp_num), ent->val, (size_t)ent->blen);
                rt->numv = (Numeric)palloc(VARSIZE_ANY(tmp_num));
                memcpy(rt->numv, tmp_num, VARSIZE_ANY(tmp_num));
                tmp_out = OidOutputFunctionCall(typed_out_func, PointerGetDatum(tmp_num));
                val = tmp_out ? tmp_out : "";
                vlen = (int32)strlen(val);
            } else {
                val = ent->val ? ent->val : "";
                vlen = ent->blen > 0 ? ent->blen : 0;
            }
        }

        rt->txt = (char *)palloc((size_t)vlen + 1u);
        if (vlen > 0)
            memcpy(rt->txt, val, (size_t)vlen);
        rt->txt[vlen] = '\0';

        if (dict_typid == NUMERICOID) {
            rt->numv = DatumGetNumeric(DirectFunctionCall3(numeric_in,
                                                           CStringGetDatum(rt->txt),
                                                           ObjectIdGetDatum(InvalidOid),
                                                           Int32GetDatum(-1)));
        } else if (dict_typid == FLOAT4OID || dict_typid == FLOAT8OID) {
            char *endp = NULL;
            errno = 0;
            double d = strtod(rt->txt, &endp);
            if (errno == 0 && endp && *endp == '\0') {
                rt->num = d;
                rt->has_num = true;
            }
        }

        if (tmp_out)
            pfree(tmp_out);
        if (tmp_num)
            pfree(tmp_num);
    }

    if (n_tokens > 1)
        qsort_arg(rows, (size_t)n_tokens, sizeof(RankTok), cmp_ranktok, &dict_typid);

    int32 *rank_by_tok = NULL;
    if (n_tokens > 0)
        rank_by_tok = (int32 *)palloc0(sizeof(int32) * (size_t)n_tokens);
    for (int32 i = 0; i < n_tokens; i++) {
        int32 tok = rows[i].tok;
        if (tok < 0 || tok >= n_tokens)
            ereport(ERROR, (errmsg("artifact_builder: invalid tok in rank sort tok=%d n=%d", tok, n_tokens)));
        rank_by_tok[tok] = i;
    }

    ByteaBuilder *bb = bb_create();
    for (int32 tok = 0; tok < n_tokens; tok++)
        bb_append_int32(bb, rank_by_tok[tok]);
    insert_file(name, bb_to_bytea(bb));
    bb_free(bb);

    if (rank_by_tok)
        pfree(rank_by_tok);
    if (rows) {
        for (int32 i = 0; i < n_tokens; i++) {
            if (rows[i].txt)
                pfree(rows[i].txt);
            if (rows[i].numv)
                pfree(rows[i].numv);
        }
        pfree(rows);
    }
    if (vals)
        pfree(vals);
}

Datum emit_invidx(PG_FUNCTION_ARGS);
PG_FUNCTION_INFO_V1(emit_invidx);

Datum
emit_invidx(PG_FUNCTION_ARGS)
{
    TimestampTz started = GetCurrentTimestamp();
    MemoryContext emit_context = NULL;
    EmitInvidxContext context;
    int indexes_built = -1;
    bool spi_connected = false;

    memset(&context, 0, sizeof(context));
    PG_TRY();
    {
        if (SPI_connect() != SPI_OK_CONNECT)
            ereport(ERROR, (errmsg("emit_invidx: SPI_connect failed")));
        spi_connected = true;
        SPI_execute("SET LOCAL search_path TO public, pg_catalog", false, 0);
        SPI_execute("SET LOCAL synchronous_commit TO off", false, 0);

        g_insert_file_plan = NULL;
        g_read_artifact_plan = NULL;
        prepare_insert_file_plan();
        prepare_read_artifact_plan();
        emit_context = AllocSetContextCreate(
            TopTransactionContext,
            "artifact_builder_emit_invidx_ctx",
            ALLOCSET_DEFAULT_SIZES);
        context.memory_context = emit_context;

        indexes_built = emit_invidx_run(
            &context, pg_read_artifact, pg_write_artifact);
        if (indexes_built < 0)
            ereport(ERROR,
                    (errmsg("emit_invidx: %s",
                            emit_invidx_last_error())));

        if (g_read_artifact_plan) {
            SPI_freeplan(g_read_artifact_plan);
            g_read_artifact_plan = NULL;
        }
        if (g_insert_file_plan) {
            SPI_freeplan(g_insert_file_plan);
            g_insert_file_plan = NULL;
        }
        MemoryContextDelete(emit_context);
        emit_context = NULL;
        SPI_finish();
        spi_connected = false;
    }
    PG_CATCH();
    {
        if (g_read_artifact_plan) {
            SPI_freeplan(g_read_artifact_plan);
            g_read_artifact_plan = NULL;
        }
        if (g_insert_file_plan) {
            SPI_freeplan(g_insert_file_plan);
            g_insert_file_plan = NULL;
        }
        if (emit_context)
            MemoryContextDelete(emit_context);
        if (spi_connected)
            SPI_finish();
        PG_RE_THROW();
    }
    PG_END_TRY();

    elog(NOTICE,
         "artifact_builder: emit_invidx indexes_built=%d ms=%.3f",
         indexes_built, elapsed_ms(started));
    PG_RETURN_VOID();
}

Datum build_base(PG_FUNCTION_ARGS);
PG_FUNCTION_INFO_V1(build_base);

Datum build_base(PG_FUNCTION_ARGS) {
    if (PG_NARGS() < 1 || PG_ARGISNULL(0)) {
        ereport(ERROR, (errmsg("build_base requires policy path")));
    }
    const char *path = text_to_cstring(PG_GETARG_TEXT_PP(0));
    TimestampTz build_t0 = GetCurrentTimestamp();

    ColumnList cols = {0};
    ColumnList const_cols_list = {0};
    StringList tables = {0};

    PolicySet ps;
    memset(&ps, 0, sizeof(ps));
    if (parse_policy_file(path, &ps) != 0) {
        ereport(ERROR, (errmsg("failed to parse policies at %s", path)));
    }

    if (SPI_connect() != SPI_OK_CONNECT) {
        ereport(ERROR, (errmsg("SPI_connect failed")));
    }
    SetConfigOption("max_parallel_workers", "0", PGC_USERSET, PGC_S_SESSION);
    SetConfigOption("max_parallel_workers_per_gather", "0", PGC_USERSET, PGC_S_SESSION);
    SetConfigOption("max_parallel_maintenance_workers", "0", PGC_USERSET, PGC_S_SESSION);
    SetConfigOption("parallel_leader_participation", "off", PGC_USERSET, PGC_S_SESSION);
    SPI_execute("SET LOCAL search_path TO public, pg_catalog", false, 0);
    SPI_execute("SET LOCAL synchronous_commit TO off", false, 0);
    {
        bool files_table_default = false;
        char *table_sql = files_table_sql_ident(&files_table_default);
        char *sql = psprintf("CREATE TABLE IF NOT EXISTS %s (run_id text, name text, file bytea)", table_sql);
        SPI_execute(sql, false, 0);
        pfree(sql);
        sql = psprintf("ALTER TABLE %s ADD COLUMN IF NOT EXISTS run_id text", table_sql);
        SPI_execute(sql, false, 0);
        pfree(sql);
        sql = psprintf("UPDATE %s SET run_id='' WHERE run_id IS NULL", table_sql);
        SPI_execute(sql, false, 0);
        pfree(sql);
        sql = psprintf(
            "DELETE FROM %s "
            "WHERE COALESCE(run_id,'') = COALESCE(current_setting('custom_filter_new.run_id', true), '')",
            table_sql);
        SPI_execute(sql, false, 0);
        pfree(sql);
        if (files_table_default)
        {
            SPI_execute("DROP INDEX IF EXISTS files_name_uidx", false, 0);
            SPI_execute("DROP INDEX IF EXISTS files_runid_name_uidx", false, 0);
            SPI_execute("DROP INDEX IF EXISTS files_runid_name_idx", false, 0);
        }
        pfree(table_sql);
    }
    g_insert_file_plan = NULL;
    prepare_insert_file_plan();

    int colcmp_atom_count = 0;
    int *col_hub_class = NULL;
    int col_hub_class_cap = 0;
    int *edge_left = NULL;
    int *edge_right = NULL;
    int edge_cap = 0;
    int edge_count = 0;
    /*
     * Keep token dictionaries in a context that survives SPI statement memory
     * resets for the whole build.
     */
    MemoryContext build_mcxt = AllocSetContextCreate(TopTransactionContext,
                                                     "artifact_builder_build_ctx",
                                                     ALLOCSET_DEFAULT_SIZES);

    for (int p = 0; p < ps.policy_count; p++) {
        Policy *pol = &ps.policies[p];
        if (pol->target_table[0] != '\0')
            str_list_add_unique(&tables, pol->target_table);
        for (int i = 0; i < pol->atom_count; i++) {
            PolicyAtom *a = &pol->atoms[i];
            if (a->lhs_table[0] == '\0' || a->lhs_col[0] == '\0')
                continue;
            int lidx = column_add_unique(&cols, a->lhs_table, a->lhs_col);
            str_list_add_unique(&tables, a->lhs_table);
            if (a->type == ATOM_COL_CONST) {
                column_add_unique(&const_cols_list, a->lhs_table, a->lhs_col);
            }
            if (a->type == ATOM_JOIN_EQ || a->type == ATOM_COL_COL) {
                if (a->rhs_table[0] == '\0' || a->rhs_col[0] == '\0')
                    ereport(ERROR, (errmsg("col-col atom missing rhs table/col")));
                int ridx = column_add_unique(&cols, a->rhs_table, a->rhs_col);
                str_list_add_unique(&tables, a->rhs_table);
                colcmp_atom_count++;
                if (edge_count >= edge_cap) {
                    int newcap = edge_cap == 0 ? 32 : edge_cap * 2;
                    edge_left = edge_left ? (int *)repalloc(edge_left, sizeof(int) * newcap)
                                          : (int *)palloc(sizeof(int) * newcap);
                    edge_right = edge_right ? (int *)repalloc(edge_right, sizeof(int) * newcap)
                                            : (int *)palloc(sizeof(int) * newcap);
                    edge_cap = newcap;
                }
                edge_left[edge_count] = lidx;
                edge_right[edge_count] = ridx;
                edge_count++;
            }
            if (a->type == ATOM_COL_COL) {
                column_add_unique(&const_cols_list, a->lhs_table, a->lhs_col);
                column_add_unique(&const_cols_list, a->rhs_table, a->rhs_col);
            }
        }
    }

    // Ensure const dicts are created for any const atom column, regardless of target.
    for (int p = 0; p < ps.policy_count; p++) {
        Policy *pol = &ps.policies[p];
        for (int i = 0; i < pol->atom_count; i++) {
            PolicyAtom *a = &pol->atoms[i];
            if (a->type != ATOM_COL_CONST) continue;
            if (a->lhs_table[0] == '\0' || a->lhs_col[0] == '\0')
                continue;
            column_add_unique(&const_cols_list, a->lhs_table, a->lhs_col);
            str_list_add_unique(&tables, a->lhs_table);
        }
    }

    sort_string_list(&tables);

    int ncols = cols.count;
    bool *is_hub_col = (bool *)palloc0(sizeof(bool) * ncols);
    int nhub_classes = 0;
    HubClass *hub_classes = NULL;
    Oid *hub_class_typid = NULL;
    Oid *col_typid = NULL;
    HubTypeClass *col_type_class = NULL;

    if (ncols > 0) {
        col_typid = (Oid *) palloc0(sizeof(Oid) * ncols);
        col_type_class = (HubTypeClass *) palloc0(sizeof(HubTypeClass) * ncols);
        for (int i = 0; i < ncols; i++) {
            Oid typid = column_type_oid(cols.items[i].table, cols.items[i].column);
            if (!OidIsValid(typid)) {
                ereport(ERROR,
                        (errmsg("unable to resolve type OID for %s.%s",
                                cols.items[i].table, cols.items[i].column)));
            }
            col_typid[i] = typid;
            col_type_class[i] = hub_type_class_for_oid(typid);
        }
    }

    if (ncols > 0) {
        int *parent = (int *)palloc(sizeof(int) * ncols);
        uint8 *rankv = (uint8 *)palloc0(sizeof(uint8) * ncols);
        for (int i = 0; i < ncols; i++) parent[i] = i;

        for (int i = 0; i < edge_count; i++) {
            int li = edge_left[i];
            int ri = edge_right[i];
            if (li < 0 || ri < 0 || li >= ncols || ri >= ncols)
                continue;
            is_hub_col[li] = true;
            is_hub_col[ri] = true;

            HubTypeClass ltc = col_type_class[li];
            HubTypeClass rtc = col_type_class[ri];
            if (ltc == HUB_TYPE_UNSUPPORTED || rtc == HUB_TYPE_UNSUPPORTED) {
                ereport(ERROR,
                        (errmsg("unsupported type class for col-col atom: %s.%s (%s) %s.%s (%s)",
                                cols.items[li].table, cols.items[li].column, format_type_be(col_typid[li]),
                                cols.items[ri].table, cols.items[ri].column, format_type_be(col_typid[ri]))));
            }
            if (ltc != rtc) {
                ereport(ERROR,
                        (errmsg("type-class mismatch for col-col atom: %s.%s (%s) vs %s.%s (%s)",
                                cols.items[li].table, cols.items[li].column, hub_type_class_name(ltc),
                                cols.items[ri].table, cols.items[ri].column, hub_type_class_name(rtc))));
            }

            int a = li;
            int b = ri;
            while (parent[a] != a) {
                parent[a] = parent[parent[a]];
                a = parent[a];
            }
            while (parent[b] != b) {
                parent[b] = parent[parent[b]];
                b = parent[b];
            }
            if (a != b) {
                if (rankv[a] < rankv[b]) {
                    int t = a; a = b; b = t;
                }
                parent[b] = a;
                if (rankv[a] == rankv[b])
                    rankv[a]++;
            }
        }

        int *root_map = (int *)palloc(sizeof(int) * ncols);
        for (int i = 0; i < ncols; i++) root_map[i] = -1;

        typedef struct {
            int root;
            IntList cols;
            char *key;
        } JoinClassTmp;

        JoinClassTmp *tmp = (JoinClassTmp *)palloc0(sizeof(JoinClassTmp) * ncols);
        int tmp_count = 0;
        for (int i = 0; i < ncols; i++) {
            int r = i;
            while (parent[r] != r) {
                parent[r] = parent[parent[r]];
                r = parent[r];
            }
            int idx = root_map[r];
            if (idx < 0) {
                idx = tmp_count++;
                root_map[r] = idx;
                tmp[idx].root = r;
            }
            int_list_add(&tmp[idx].cols, i);
        }

        ColumnList *g_cols = &cols;
        for (int i = 0; i < tmp_count; i++) {
            int n = tmp[i].cols.count;
            if (n > 1) {
                for (int a = 0; a < n; a++) {
                    for (int b = a + 1; b < n; b++) {
                        int ia = tmp[i].cols.items[a];
                        int ib = tmp[i].cols.items[b];
                        ABColumnRef *ca = &g_cols->items[ia];
                        ABColumnRef *cb = &g_cols->items[ib];
                        int cmp = strcmp(ca->table, cb->table);
                        if (cmp == 0) cmp = strcmp(ca->column, cb->column);
                        if (cmp > 0) {
                            int t = tmp[i].cols.items[a];
                            tmp[i].cols.items[a] = tmp[i].cols.items[b];
                            tmp[i].cols.items[b] = t;
                        }
                    }
                }
            }
            if (tmp[i].cols.count > 0) {
                ABColumnRef *c = &g_cols->items[tmp[i].cols.items[0]];
                StringInfoData key;
                initStringInfo(&key);
                appendStringInfo(&key, "%s.%s", c->table, c->column);
                tmp[i].key = pstrdup(key.data);
            } else {
                tmp[i].key = pstrdup("");
            }
        }

        for (int i = 0; i < tmp_count; i++) {
            for (int j = i + 1; j < tmp_count; j++) {
                if (strcmp(tmp[i].key, tmp[j].key) > 0) {
                    JoinClassTmp t = tmp[i];
                    tmp[i] = tmp[j];
                    tmp[j] = t;
                }
            }
        }

        nhub_classes = tmp_count;
        if (nhub_classes > 0) {
            hub_classes = (HubClass *)palloc0(sizeof(HubClass) * nhub_classes);
            for (int i = 0; i < nhub_classes; i++) {
                hub_classes[i].id = i;
                hub_classes[i].type_class = HUB_TYPE_TEXT;
                HubTypeClass tc = HUB_TYPE_UNSUPPORTED;
                for (int j = 0; j < tmp[i].cols.count; j++) {
                    int col_idx = tmp[i].cols.items[j];
                    int_list_add(&hub_classes[i].cols, col_idx);
                    if (col_idx >= 0 && col_idx < ncols) {
                        HubTypeClass cur = col_type_class[col_idx];
                        if (tc == HUB_TYPE_UNSUPPORTED)
                            tc = cur;
                        else if (tc != cur) {
                            ereport(ERROR,
                                    (errmsg("internal hub type-class mismatch for component id=%d", i)));
                        }
                    }
                }
                if (tc == HUB_TYPE_UNSUPPORTED)
                    tc = HUB_TYPE_TEXT;
                hub_classes[i].type_class = tc;
            }
        }
    }

    if (ncols > 0) {
        col_hub_class_cap = ncols;
        col_hub_class = (int *)palloc0(sizeof(int) * col_hub_class_cap);
        for (int i = 0; i < col_hub_class_cap; i++) col_hub_class[i] = -1;
        for (int i = 0; i < nhub_classes; i++) {
            for (int j = 0; j < hub_classes[i].cols.count; j++) {
                int col_idx = hub_classes[i].cols.items[j];
                if (col_idx >= 0 && col_idx < col_hub_class_cap)
                    col_hub_class[col_idx] = i;
            }
        }
        for (int i = 0; i < ncols; i++) {
            if (col_hub_class[i] >= 0)
                is_hub_col[i] = true;
        }
    }

    if (colcmp_atom_count > 0 && nhub_classes <= 0)
        ereport(ERROR, (errmsg("col-col atoms present but no hub classes built")));

    if (nhub_classes > 0) {
        hub_class_typid = (Oid *) palloc0(sizeof(Oid) * nhub_classes);
        for (int i = 0; i < nhub_classes; i++) {
            hub_class_typid[i] = dict_typid_for_hub_type_class((HubTypeClass)hub_classes[i].type_class);
        }
    }
    bool *hub_class_need_rank = NULL;
    if (nhub_classes > 0) {
        hub_class_need_rank = (bool *)palloc0(sizeof(bool) * nhub_classes);
        for (int i = 0; i < nhub_classes; i++)
            hub_class_need_rank[i] = true;
    }

    // meta/tables
    {
        StringInfoData buf;
        initStringInfo(&buf);
        for (int i = 0; i < tables.count; i++) {
            appendStringInfoString(&buf, tables.items[i]);
            appendStringInfoChar(&buf, '\n');
        }
        insert_file_text("meta/tables", buf.data);
    }

    // meta/join_classes (compat filename; content is hub-class membership)
    {
        StringInfoData buf;
        initStringInfo(&buf);
        for (int i = 0; i < nhub_classes; i++) {
            appendStringInfo(&buf, "class=%d cols=", i);
            // sort members by table.col
            for (int j = 0; j < hub_classes[i].cols.count; j++) {
                for (int k = j + 1; k < hub_classes[i].cols.count; k++) {
                    int ai = hub_classes[i].cols.items[j];
                    int bi = hub_classes[i].cols.items[k];
                    int cmp = strcmp(cols.items[ai].table, cols.items[bi].table);
                    if (cmp == 0) cmp = strcmp(cols.items[ai].column, cols.items[bi].column);
                    if (cmp > 0) {
                        int tmp = hub_classes[i].cols.items[j];
                        hub_classes[i].cols.items[j] = hub_classes[i].cols.items[k];
                        hub_classes[i].cols.items[k] = tmp;
                    }
                }
            }
            for (int j = 0; j < hub_classes[i].cols.count; j++) {
                int col_idx = hub_classes[i].cols.items[j];
                if (j > 0) appendStringInfoString(&buf, ",");
                appendStringInfo(&buf, "%s.%s", cols.items[col_idx].table, cols.items[col_idx].column);
            }
            appendStringInfoChar(&buf, '\n');
        }
        insert_file_text("meta/join_classes", buf.data);
    }

    /*
     * Hub/composite-hub structures are query-time semantics derived from
     * active policy atoms in the evaluator/engine. They must not be persisted
     * as build-time artifacts.
     */

    // meta/col_domain (compat filename; values are hub-class ids)
    {
        StringInfoData buf;
        initStringInfo(&buf);
        for (int i = 0; i < nhub_classes; i++) {
            for (int j = 0; j < hub_classes[i].cols.count; j++) {
                int col_idx = hub_classes[i].cols.items[j];
                appendStringInfo(&buf, "%s.%s=%d\n",
                                 cols.items[col_idx].table,
                                 cols.items[col_idx].column,
                                 i);
            }
        }
        insert_file_text("meta/col_domain", buf.data);
    }

    free_policy_set(&ps);

    /*
     * Build hub-class token maps on-the-fly during table tokenization to avoid
     * extra DISTINCT/ORDER BY passes over large tables.
     */
    for (int i = 0; i < nhub_classes; i++) {
        size_t est_rows = 0;
        StringList hub_class_tables = {0};
        for (int j = 0; j < hub_classes[i].cols.count; j++) {
            int col_idx = hub_classes[i].cols.items[j];
            str_list_add_unique(&hub_class_tables, cols.items[col_idx].table);
        }
        for (int t = 0; t < hub_class_tables.count; t++)
            est_rows += estimate_table_rows(hub_class_tables.items[t]);
        if (est_rows > (size_t) LONG_MAX)
            est_rows = (size_t) LONG_MAX;
        char map_name[NAMEDATALEN * 2];
        snprintf(map_name, sizeof(map_name), "hc_tok_map_%d", i);
        hub_classes[i].tok_map = dict_map_create(map_name, (long) est_rows, build_mcxt);
        hub_classes[i].next_tok = 0;
    }
    elog(NOTICE, "artifact_builder: hub_class_map_init hub_classes=%d ms=%.3f",
         nhub_classes, elapsed_ms(build_t0));

    // Const-column maps: also built on-the-fly while scanning the owning table.
    ConstColumn *const_cols = (ConstColumn *)palloc0(sizeof(ConstColumn) * const_cols_list.count);
    int n_const = 0;
    for (int i = 0; i < const_cols_list.count; i++) {
        const_cols[n_const].col = const_cols_list.items[i];
        const_cols[n_const].typid = column_type_oid(const_cols[n_const].col.table,
                                                    const_cols[n_const].col.column);
        const_cols[n_const].uses_hub_map = false;
        const_cols[n_const].hub_class_id = -1;

        int col_idx = column_index(&cols,
                                   const_cols[n_const].col.table,
                                   const_cols[n_const].col.column);
        int cid = (col_idx >= 0 && col_hub_class && col_idx < col_hub_class_cap) ? col_hub_class[col_idx] : -1;
        if (col_idx >= 0 && is_hub_col[col_idx] && cid >= 0) {
            const_cols[n_const].uses_hub_map = true;
            const_cols[n_const].hub_class_id = cid;
            const_cols[n_const].tok_map = hub_classes[cid].tok_map;
            const_cols[n_const].next_tok = 0;
        } else {
            size_t est_rows = estimate_table_rows(const_cols[n_const].col.table);
            if (est_rows > (size_t) LONG_MAX)
                est_rows = (size_t) LONG_MAX;
            char map_name[NAMEDATALEN * 2];
            snprintf(map_name, sizeof(map_name), "const_tok_map_%d", n_const);
            const_cols[n_const].tok_map = dict_map_create(map_name, (long) est_rows, build_mcxt);
            const_cols[n_const].next_tok = 0;
        }
        n_const++;
    }

// meta/cols/<table> and table artifacts
    for (int ti = 0; ti < tables.count; ti++) {
        TimestampTz table_t0 = GetCurrentTimestamp();
        char *table = tables.items[ti];
        IntList hub_cols = {0};
        IntList const_cols_idx = {0};
        for (int i = 0; i < ncols; i++) {
            if (strcmp(cols.items[i].table, table) != 0) continue;
            if (is_hub_col[i]) int_list_add(&hub_cols, i);
            else int_list_add(&const_cols_idx, i);
        }
        sort_columns_by_name(&cols, &hub_cols);
        sort_columns_by_name(&cols, &const_cols_idx);

        // write meta/cols/<table>
        {
            StringInfoData buf;
            initStringInfo(&buf);
            for (int i = 0; i < hub_cols.count; i++) {
                int col_idx = hub_cols.items[i];
                appendStringInfo(&buf, "%s.%s\n", cols.items[col_idx].table, cols.items[col_idx].column);
            }
            for (int i = 0; i < const_cols_idx.count; i++) {
                int col_idx = const_cols_idx.items[i];
                appendStringInfo(&buf, "%s.%s\n", cols.items[col_idx].table, cols.items[col_idx].column);
            }
            char name[NAMEDATALEN * 2];
            snprintf(name, sizeof(name), "meta/cols/%s", table);
            insert_file_text(name, buf.data);
        }

        int token_count = hub_cols.count + const_cols_idx.count;
        TokenColumn *tokcols = (TokenColumn *)palloc0(sizeof(TokenColumn) * token_count);
        int tpos = 0;
        for (int i = 0; i < hub_cols.count; i++) {
            int col_idx = hub_cols.items[i];
            int cid = (col_hub_class && col_idx < col_hub_class_cap) ? col_hub_class[col_idx] : -1;
            if (cid < 0)
                ereport(ERROR, (errmsg("missing hub class id for %s.%s",
                                       cols.items[col_idx].table, cols.items[col_idx].column)));
            tokcols[tpos].col_idx = col_idx;
            tokcols[tpos].is_hub = 1;
            tokcols[tpos].hub_class_id = cid;
            tokcols[tpos].const_col_idx = -1;
            tokcols[tpos].tok_map = hub_classes[cid].tok_map;
            tpos++;
        }
        for (int i = 0; i < const_cols_idx.count; i++) {
            int col_idx = const_cols_idx.items[i];
            tokcols[tpos].col_idx = col_idx;
            tokcols[tpos].is_hub = 0;
            tokcols[tpos].hub_class_id = -1;
            tokcols[tpos].const_col_idx = -1;
            for (int j = 0; j < const_cols_list.count; j++) {
                if (strcmp(const_cols[j].col.table, cols.items[col_idx].table) == 0 &&
                    strcmp(const_cols[j].col.column, cols.items[col_idx].column) == 0) {
                    tokcols[tpos].tok_map = const_cols[j].tok_map;
                    tokcols[tpos].const_col_idx = j;
                    break;
                }
            }
            if (!tokcols[tpos].tok_map)
                ereport(ERROR, (errmsg("missing const token map for %s.%s",
                                       cols.items[col_idx].table, cols.items[col_idx].column)));
            tpos++;
        }

        ByteaBuilder *ctid_bb = bb_create();
        /* Columnar code chunks for compactness. */
        const uint32 code_chunk_max_rows = 1000000;
        size_t est_rows = estimate_table_rows(table);
        if (est_rows == 0)
            est_rows = 1024;
        if (est_rows > (SIZE_MAX / (sizeof(int32) * 2)))
            est_rows = SIZE_MAX / (sizeof(int32) * 2);
        bb_reserve(ctid_bb, est_rows * sizeof(int32) * 2);
        int32 *row_tokens = NULL;
        if (token_count > 0)
            row_tokens = (int32 *) palloc(sizeof(int32) * token_count);
        int32 *chunk_tokens = NULL;
        if (token_count > 0) {
            size_t chunk_cap = (size_t) code_chunk_max_rows * (size_t) token_count;
            if (chunk_cap > 0 && chunk_cap > SIZE_MAX / sizeof(int32))
                ereport(ERROR, (errmsg("token chunk allocation overflow for %s", table)));
            chunk_tokens = (int32 *) palloc(sizeof(int32) * chunk_cap);
        }

        Oid relid = RelnameGetRelid(table);
        if (!OidIsValid(relid))
            ereport(ERROR, (errmsg("relation not found: %s", table)));
        Relation rel = table_open(relid, AccessShareLock);
        TupleDesc rel_desc = RelationGetDescr(rel);
        for (int i = 0; i < token_count; i++) {
            int col_idx = tokcols[i].col_idx;
            AttrNumber attnum = get_attnum(relid, cols.items[col_idx].column);
            if (attnum == InvalidAttrNumber)
                ereport(ERROR, (errmsg("missing attribute %s.%s",
                                       table, cols.items[col_idx].column)));
            tokcols[i].attnum = attnum;
            tokcols[i].typid = TupleDescAttr(rel_desc, attnum - 1)->atttypid;
            getTypeOutputInfo(tokcols[i].typid, &tokcols[i].typoutput, &tokcols[i].typisvarlena);
        }

        PushActiveSnapshot(GetTransactionSnapshot());
        TableScanDesc scan = table_beginscan(rel, GetActiveSnapshot(), 0, NULL);
        TupleTableSlot *slot = MakeSingleTupleTableSlot(rel_desc, table_slot_callbacks(rel));
        int64 total_rows = 0;
        int chunk_idx = 0;
        uint32 chunk_rows = 0;

        while (table_scan_getnextslot(scan, ForwardScanDirection, slot)) {
            if (!ItemPointerIsValid(&slot->tts_tid))
                continue;
            int32 blk = (int32) ItemPointerGetBlockNumber(&slot->tts_tid);
            int32 off = (int32) ItemPointerGetOffsetNumber(&slot->tts_tid);
            bb_append_int32(ctid_bb, blk);
            bb_append_int32(ctid_bb, off);
            for (int i = 0; i < token_count; i++) {
                bool isnull = false;
                Datum v = slot_getattr(slot, tokcols[i].attnum, &isnull);
                int32 tval = -1;
                if (!isnull) {
                    int32 *next_tok_ptr = NULL;
                    if (tokcols[i].is_hub) {
                        int jc = tokcols[i].hub_class_id;
                        if (jc < 0 || jc >= nhub_classes)
                            ereport(ERROR, (errmsg("invalid hub class index %d", jc)));
                        next_tok_ptr = &hub_classes[jc].next_tok;
                    } else {
                        int ci = tokcols[i].const_col_idx;
                        if (ci < 0 || ci >= n_const)
                            ereport(ERROR, (errmsg("invalid const column index %d", ci)));
                        next_tok_ptr = &const_cols[ci].next_tok;
                    }
                    if (tokcols[i].is_hub) {
                        int jc = tokcols[i].hub_class_id;
                        HubTypeClass tc = (HubTypeClass)hub_classes[jc].type_class;
                        if (tc == HUB_TYPE_DATE) {
                            int64 ikey = dict_datum_to_intkey(tokcols[i].typid, v);
                            tval = dict_map_get_or_insert_int64(tokcols[i].tok_map,
                                                                build_mcxt,
                                                                ikey,
                                                                next_tok_ptr,
                                                                NULL);
                        } else if (tc == HUB_TYPE_TEXT && dict_typid_uses_bytekey(tokcols[i].typid)) {
                            struct varlena *vl_orig = (struct varlena *) DatumGetPointer(v);
                            struct varlena *vl = PG_DETOAST_DATUM_PACKED(v);
                            const char *bytes = VARDATA_ANY(vl);
                            int32 blen = (int32) VARSIZE_ANY_EXHDR(vl);
                            if (tokcols[i].typid == BPCHAROID) {
                                while (blen > 0 && bytes[blen - 1] == ' ')
                                    blen--;
                            }
                            tval = dict_map_get_or_insert_bytes(tokcols[i].tok_map,
                                                                build_mcxt,
                                                                bytes,
                                                                blen,
                                                                next_tok_ptr,
                                                                NULL);
                            if (vl != vl_orig)
                                pfree(vl);
                        } else {
                            char *txt = OidOutputFunctionCall(tokcols[i].typoutput, v);
                            if (txt) {
                                char *canon = txt;
                                if (tc == HUB_TYPE_NUMERIC && tokcols[i].typid == NUMERICOID) {
                                    struct varlena *num_orig = (struct varlena *) DatumGetPointer(v);
                                    Numeric num = DatumGetNumeric(v);
                                    canon = numeric_normalize(num);
                                    if ((struct varlena *) num != num_orig)
                                        pfree(num);
                                } else if (tc == HUB_TYPE_NUMERIC) {
                                    canon = normalize_numeric_string(txt);
                                } else if (tokcols[i].typid == BPCHAROID) {
                                    size_t n = strlen(canon);
                                    while (n > 0 && canon[n - 1] == ' ') {
                                        canon[n - 1] = '\0';
                                        n--;
                                    }
                                }
                                tval = dict_map_get_or_insert_text(tokcols[i].tok_map,
                                                                   build_mcxt,
                                                                   canon,
                                                                   next_tok_ptr,
                                                                   NULL);
                                if (canon != txt)
                                    pfree(canon);
                                pfree(txt);
                            }
                        }
                    } else if (dict_typid_uses_intkey(tokcols[i].typid)) {
                        int64 ikey = dict_datum_to_intkey(tokcols[i].typid, v);
                        tval = dict_map_get_or_insert_int64(tokcols[i].tok_map,
                                                            build_mcxt,
                                                            ikey,
                                                            next_tok_ptr,
                                                            NULL);
                    } else if (dict_typid_uses_bytekey(tokcols[i].typid)) {
                        struct varlena *vl_orig = (struct varlena *) DatumGetPointer(v);
                        struct varlena *vl = PG_DETOAST_DATUM_PACKED(v);
                        const char *bytes = VARDATA_ANY(vl);
                        int32 blen = (int32) VARSIZE_ANY_EXHDR(vl);
                        if (tokcols[i].typid == BPCHAROID) {
                            while (blen > 0 && bytes[blen - 1] == ' ')
                                blen--;
                        }
                        tval = dict_map_get_or_insert_bytes(tokcols[i].tok_map,
                                                            build_mcxt,
                                                            bytes,
                                                            blen,
                                                            next_tok_ptr,
                                                            NULL);
                        if (vl != vl_orig)
                            pfree(vl);
                    } else {
                        char *txt = OidOutputFunctionCall(tokcols[i].typoutput, v);
                        if (txt) {
                            if (tokcols[i].typid == BPCHAROID) {
                                size_t n = strlen(txt);
                                while (n > 0 && txt[n - 1] == ' ') {
                                    txt[n - 1] = '\0';
                                    n--;
                                }
                            }
                            tval = dict_map_get_or_insert_text(tokcols[i].tok_map,
                                                               build_mcxt,
                                                               txt,
                                                               next_tok_ptr,
                                                               NULL);
                            pfree(txt);
                        }
                    }
                }
                row_tokens[i] = tval;
            }
            if (token_count > 0) {
                size_t base = (size_t) chunk_rows * (size_t) token_count;
                memcpy(chunk_tokens + base, row_tokens, sizeof(int32) * (size_t) token_count);
            }
            total_rows++;
            chunk_rows++;
            if (chunk_rows >= code_chunk_max_rows) {
                flush_code_col_chunks(table, chunk_idx, chunk_rows, chunk_tokens, token_count);
                chunk_rows = 0;
                chunk_idx++;
            }
        }
        table_endscan(scan);
        ExecDropSingleTupleTableSlot(slot);
        PopActiveSnapshot();
        table_close(rel, AccessShareLock);

        char name_ctid[NAMEDATALEN];
        char name_code[NAMEDATALEN * 2];
        snprintf(name_ctid, sizeof(name_ctid), "%s_ctid", table);
        snprintf(name_code, sizeof(name_code), "%s_code_base", table);

        /* Flush final partial chunk and then write a compact CB04 manifest at <table>_code_base. */
        flush_code_col_chunks(table, chunk_idx, chunk_rows, chunk_tokens, token_count);
        if (chunk_rows > 0)
            chunk_idx++;
        if (total_rows > (int64) INT32_MAX)
            ereport(ERROR, (errmsg("row count too large for %s: " INT64_FORMAT, table, total_rows)));

        ByteaBuilder *manifest_bb = bb_create();
        const char magic3[4] = {'C', 'B', '0', '4'};
        bb_append_bytes(manifest_bb, magic3, sizeof(magic3));
        bb_append_int32(manifest_bb, (int32) total_rows);
        bb_append_int32(manifest_bb, (int32) code_chunk_max_rows);
        bb_append_int32(manifest_bb, (int32) token_count);
        bb_append_int32(manifest_bb, (int32) chunk_idx);

        bytea *ctid_ba = bb_to_bytea(ctid_bb);
        insert_file(name_ctid, ctid_ba);
        if (ctid_ba) pfree(ctid_ba);

        bytea *manifest_ba = bb_to_bytea(manifest_bb);
        insert_file(name_code, manifest_ba);
        if (manifest_ba) pfree(manifest_ba);

        if (row_tokens)
            pfree(row_tokens);
        if (chunk_tokens)
            pfree(chunk_tokens);
        bb_free(ctid_bb);
        bb_free(manifest_bb);
        elog(NOTICE, "artifact_builder: table_tokenize table=%s rows=%lld token_cols=%d ms=%.3f",
             table, (long long) total_rows, token_count, elapsed_ms(table_t0));
    }

    /*
     * Persist one shared dictionary per hub class. Token assignment is
     * insertion-order based (unsorted), so dict_sorted remains 0.
     * Compatibility note: filenames keep legacy dict/domain and rank/domain paths.
     * For hub classes used by ordered col-col predicates, also persist token->rank.
     */
    for (int i = 0; i < nhub_classes; i++) {
        TimestampTz dict_t0 = GetCurrentTimestamp();
        char dict_name[NAMEDATALEN * 3];
        snprintf(dict_name, sizeof(dict_name), "dict/domain/%d", i);
        write_dict_from_map(dict_name, hub_classes[i].tok_map, hub_classes[i].next_tok, hub_class_typid ? hub_class_typid[i] : TEXTOID);

        char dtype_name[NAMEDATALEN * 3];
        snprintf(dtype_name, sizeof(dtype_name), "meta/dict_type/domain/%d", i);
        insert_file_text(dtype_name, dict_type_label_for_oid(hub_class_typid ? hub_class_typid[i] : TEXTOID));

        char sorted_name[NAMEDATALEN * 3];
        snprintf(sorted_name, sizeof(sorted_name), "meta/dict_sorted/domain/%d", i);
        insert_file_text(sorted_name, "0");

        char rank_meta_name[NAMEDATALEN * 3];
        snprintf(rank_meta_name, sizeof(rank_meta_name), "meta/dict_rank/domain/%d", i);
        if (hub_class_need_rank && hub_class_need_rank[i]) {
            char rank_name[NAMEDATALEN * 3];
            snprintf(rank_name, sizeof(rank_name), "rank/domain/%d", i);
            write_rank_from_map(rank_name,
                                hub_classes[i].tok_map,
                                hub_classes[i].next_tok,
                                hub_class_typid ? hub_class_typid[i] : TEXTOID);
            insert_file_text(rank_meta_name, "1");
        } else {
            insert_file_text(rank_meta_name, "0");
        }

        elog(NOTICE,
             "artifact_builder: dict hub_class=%d tokens=%d sorted=0 rank=%d ms=%.3f",
             i, hub_classes[i].next_tok,
             (hub_class_need_rank && hub_class_need_rank[i]) ? 1 : 0,
             elapsed_ms(dict_t0));
    }

    /*
     * Persist non-hub const-column dictionaries after tokenization.
     * Hub-class columns are served by dict/domain/<hub_class_id> (compat path).
     */
    for (int i = 0; i < n_const; i++) {
        if (const_cols[i].uses_hub_map)
            continue;
        TimestampTz dict_t0 = GetCurrentTimestamp();
        char dict_name[NAMEDATALEN * 3];
        snprintf(dict_name, sizeof(dict_name), "dict/%s/%s",
                 const_cols[i].col.table, const_cols[i].col.column);
        int32 ntoks = const_cols[i].next_tok;
        write_dict_from_map(dict_name, const_cols[i].tok_map, ntoks, const_cols[i].typid);

        char dtype_name[NAMEDATALEN * 3];
        snprintf(dtype_name, sizeof(dtype_name), "meta/dict_type/%s/%s",
                 const_cols[i].col.table, const_cols[i].col.column);
        insert_file_text(dtype_name, dict_type_label_for_oid(const_cols[i].typid));

        char sorted_name[NAMEDATALEN * 3];
        snprintf(sorted_name, sizeof(sorted_name), "meta/dict_sorted/%s/%s",
                 const_cols[i].col.table, const_cols[i].col.column);
        insert_file_text(sorted_name, "0");

        elog(NOTICE,
             "artifact_builder: const_dict table=%s col=%s tokens=%d sorted=0 ms=%.3f",
             const_cols[i].col.table, const_cols[i].col.column,
             ntoks, elapsed_ms(dict_t0));
    }

    elog(NOTICE, "artifact_builder: total_ms=%.3f tables=%d hub_classes=%d const_cols=%d",
         elapsed_ms(build_t0), tables.count, nhub_classes, n_const);

    if (g_insert_file_plan) {
        SPI_freeplan(g_insert_file_plan);
        g_insert_file_plan = NULL;
    }
    {
        bool files_table_default = false;
        char *table_sql = files_table_sql_ident(&files_table_default);
        if (files_table_default)
        {
            SPI_execute("CREATE INDEX IF NOT EXISTS files_runid_name_idx ON public.files(run_id, name)", false, 0);
        }
        pfree(table_sql);
    }

    MemoryContextDelete(build_mcxt);
    SPI_finish();
    PG_RETURN_VOID();
}
