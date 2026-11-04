#ifndef PAC_EXEC_METRICS_H
#define PAC_EXEC_METRICS_H
#include "diagnostic_counter.h"
#ifdef __cplusplus
extern "C" {
#endif
extern bool cf_diagnostic_logging;
void cf_perf_metric_set(const char *name, double value);
void cf_perf_cost_plan_set(const char *json);
#ifdef __cplusplus
}
#endif
/* Do not format arguments or emit diagnostics when logging is off. */
#define CF_METRICS_LOG(level, ...) do { \
    if (cf_diagnostic_logging) elog(level, __VA_ARGS__); \
} while (0)
#endif

