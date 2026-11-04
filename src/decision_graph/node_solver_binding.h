#ifndef MEMENTO_NODE_SOLVER_BINDING_H
#define MEMENTO_NODE_SOLVER_BINDING_H
#include <vector>
namespace full_reuse {
template<class Nodes,class Solver,class IsMixed>
std::vector<Solver> bind_node_solvers(const Nodes &nodes,Solver ordinary,Solver mixed,IsMixed is_mixed) {
    std::vector<Solver> result;result.reserve(nodes.size());
    for(std::size_t i=0;i<nodes.size();++i)
        result.push_back(i && is_mixed(nodes[i]) ? mixed : ordinary);
    return result;
}
}
#endif
