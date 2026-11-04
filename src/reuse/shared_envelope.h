#pragma once
#include <algorithm>
#include <cstdint>

namespace full_reuse {
// Exact complete-Rest cells are authoritative; no invented nogood gaps.
struct SharedEnvelope {
    std::uint32_t smallest_good=UINT32_MAX,largest_good=0;
    std::uint32_t false_prefix_end=0,false_suffix_begin=UINT32_MAX;
    template<class KnownFalse>
    void observe(std::uint32_t rank,bool good,std::uint32_t count,KnownFalse known_false) {
        if(false_suffix_begin==UINT32_MAX)false_suffix_begin=count;
        if(good) {
            smallest_good=std::min(smallest_good,rank);
            largest_good=std::max(largest_good,rank);
        } else {
            while(false_prefix_end<count && known_false(false_prefix_end))++false_prefix_end;
            while(false_suffix_begin && known_false(false_suffix_begin-1U))--false_suffix_begin;
        }
    }
    bool range(std::uint32_t begin,std::uint32_t end,std::uint32_t count,bool *truth)const {
        if(begin>=end){*truth=false;return true;}
        if(smallest_good!=UINT32_MAX &&
           ((begin<=smallest_good && smallest_good<end) || (begin<=largest_good && largest_good<end))) {
            *truth=true;return true;
        }
        if(end<=false_prefix_end || (false_suffix_begin<=count && begin>=false_suffix_begin)) {
            *truth=false;return true;
        }
        return false;
    }
};
}
