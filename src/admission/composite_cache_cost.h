#pragma once
#include <algorithm>
#include <cstddef>

namespace full_reuse {
// Relative work units, not predicted nanoseconds. A wide-key hash probe needs
// hashing plus bucket/key access. Separate the repeated hot probe from the
// first-touch cache-line and allocation costs: charging a cold probe on EVERY
// arrival would reject short postings even after their keys are heavily reused.
struct CompositeCacheCost {
    double arrivals=0,distinct=0,reads=0,scan=0,lookup=0,build=0,cold=0;
    double without_cache=0,with_cache=0;
    bool admitted=false;
};
inline CompositeCacheCost composite_cache_cost(double arrivals,double distinct,
                                               double shortest,std::size_t equalities,std::size_t operands,
                                               std::size_t entry_bytes=96U) {
    CompositeCacheCost cost;
    cost.arrivals=std::max(0.0,arrivals);cost.distinct=std::max(1.0,distinct);
    cost.reads=std::max(0.0,shortest);
    cost.scan=cost.reads*(1.0+equalities); // posting + rank checks, before local filters
    cost.lookup=4.0+2.0*operands;
    cost.build=24.0+2.0*operands;
    // Conservative relative first-touch work per 64-byte entry cache line.
    // This is a structural estimate, not hardware cycles or a policy constant.
    cost.cold=48.0*double(entry_bytes/64U+unsigned(entry_bytes%64U!=0));
    const auto first=std::min(cost.arrivals,cost.distinct);
    cost.without_cache=cost.arrivals*cost.scan;
    cost.with_cache=cost.arrivals*cost.lookup+first*(cost.scan+cost.build+cost.cold);
    // Demand a margin: the model is structural, not a measured joint count.
    cost.admitted=cost.arrivals>first && cost.with_cache*1.1<cost.without_cache;
    return cost;
}
}
