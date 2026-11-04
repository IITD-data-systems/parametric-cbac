// Native translation unit: NEVER compile this file with LTO.
#define MEMENTO_COLD_TRANSLATION_UNIT
#include "our_pg_uniform.online.cpp"
namespace memento_runtime {
#define MEMENTO_METHOD(name) FusedWalkRuntime::name
#include "grouped_target_loop.inc"
#include "mixed_requests.inc"
#include "exclusive_rank_loop.inc"
#include "node_dispatch.inc"
#include "grouped_compiler.inc"
#undef MEMENTO_METHOD
}
