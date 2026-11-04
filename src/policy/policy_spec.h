#pragma once

#include <stdbool.h>

#ifdef __cplusplus
extern "C" {
#endif

bool cf_trace_enabled(void);
bool cf_debug_enabled(void);
bool cf_contract_enabled(void);

#ifdef __cplusplus
}
#endif
