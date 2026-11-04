#pragma once

#include "policy_runtime_new.h"

#include <cstdint>
#include <string>
#include <vector>

std::vector<std::uint64_t> our_pg_evaluate_target(
    const PolicyArtifactCNew *arts,
    int art_count,
    const PolicyEngineInputC *in,
    int target_index,
    const std::string &target,
    std::uint32_t total_rows);
