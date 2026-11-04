#pragma once
#ifndef CF_DIAGNOSTIC_COUNTERS
#define CF_DIAGNOSTIC_COUNTERS 1
#endif
#if CF_DIAGNOSTIC_COUNTERS
#define CF_COUNT(expr) do {expr;} while(0)
#else
#define CF_COUNT(expr) do {} while(0)
#endif
