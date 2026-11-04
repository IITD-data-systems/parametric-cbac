#pragma once
#include <algorithm>
namespace rank_frontier_admission {
struct Estimate {double rows=0,points=0,repeats=0,walk=0,summary=0;bool pays=false;};
inline Estimate estimate(double rows,double points,unsigned steps,double repeats){
    Estimate e;e.rows=rows;e.points=std::min(rows,std::max(0.,points));e.repeats=std::max(1.,repeats);
    // Shared predicates cost the same in a scan and a point check. A point
    // replaces a complete functional witness, not just one of its hops.
    e.walk=e.repeats*rows*steps;
    e.summary=rows*steps+e.points*std::max(0.,e.points-1.)+e.repeats*e.points;
    e.pays=e.summary<e.walk;return e;
}
} // namespace rank_frontier_admission
