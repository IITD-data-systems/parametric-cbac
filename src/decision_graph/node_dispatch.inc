MEMENTO_DISPATCH_ISLAND
std::uint64_t MEMENTO_METHOD(solve_node)(std::size_t node,
                             std::uint64_t requested,
                             std::uint64_t settle_on_success)
#ifdef MEMENTO_DECLARE_COLD
;
#else
{
        return (this->*node_solvers_[node])(node,requested,settle_on_success);
    }
#endif
