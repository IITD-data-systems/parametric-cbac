#pragma once

#ifdef __cplusplus
extern "C" {
#endif
#include "postgres.h"
#ifdef __cplusplus
}
#endif

#ifdef __cplusplus
extern "C" {
#endif

typedef struct ByteaBuilder ByteaBuilder;

ByteaBuilder *bb_create(void);
void bb_reserve(ByteaBuilder *bb, size_t nbytes);
void bb_append_int32(ByteaBuilder *bb, int32 value);
void bb_append_bytes(ByteaBuilder *bb, const void *data, size_t len);
bytea *bb_to_bytea(ByteaBuilder *bb);
size_t bb_size(ByteaBuilder *bb);
void bb_free(ByteaBuilder *bb);

#ifdef __cplusplus
}
#endif
