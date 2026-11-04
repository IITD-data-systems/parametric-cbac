#pragma once
#include <algorithm>
#include <array>
#include <cstdint>
#include <utility>
#include <vector>

namespace full_reuse {
// Request ranges are planning/arrival metadata, never materialized row/key sets.
// A request has at most two intervals (NE). Merging removes overlaps, not gaps.
struct MixedRequests {
    using Range=std::pair<std::uint32_t,std::uint32_t>;
    std::array<std::vector<Range>,64> requests;
    std::vector<Range> united;
    void add(unsigned leaf,std::uint32_t begin,std::uint32_t end) {
        if(begin<end)requests[leaf].emplace_back(begin,end);
    }
    void unite(std::uint64_t live) {
        united.clear();
        for(auto bits=live;bits;bits&=bits-1U) {
            const auto leaf=unsigned(__builtin_ctzll(bits));
            united.insert(united.end(),requests[leaf].begin(),requests[leaf].end());
        }
        std::sort(united.begin(),united.end());std::size_t n=0;
        for(const auto &range:united) {
            if(n && range.first<=united[n-1U].second)united[n-1U].second=std::max(united[n-1U].second,range.second);
            else united[n++]=range;
        }
        united.resize(n);
    }
    std::uint64_t admitted(std::uint32_t rank,std::uint64_t live)const {
        std::uint64_t result=0;
        for(auto bits=live;bits;bits&=bits-1U) {
            const auto leaf=unsigned(__builtin_ctzll(bits));
            for(const auto &range:requests[leaf])if(range.first<=rank && rank<range.second) {
                result|=std::uint64_t{1}<<leaf;break;
            }
        }
        return result;
    }
    std::uint32_t next(std::uint32_t rank,std::uint64_t live,std::uint32_t limit)const {
        auto result=limit;
        for(auto bits=live;bits;bits&=bits-1U) {
            const auto leaf=unsigned(__builtin_ctzll(bits));
            for(const auto &range:requests[leaf])if(rank<range.second)
                result=std::min(result,std::max(rank,range.first));
        }
        return result;
    }
    std::uint64_t future(std::uint32_t rank,std::uint64_t live)const {
        std::uint64_t result=0;
        for(auto bits=live;bits;bits&=bits-1U) {
            const auto leaf=unsigned(__builtin_ctzll(bits));
            for(const auto &range:requests[leaf])if(rank<range.second) {
                result|=std::uint64_t{1}<<leaf;break;
            }
        }
        return result;
    }
    // Event boundaries, not a rank-domain pass. A segment has one fixed set of
    // admitted requests. Recompute after settlement: a formerly shared range
    // immediately becomes an independent V4 range when only one request lives.
    std::uint32_t segment_end(std::uint32_t rank,std::uint64_t live,std::uint32_t limit)const {
        auto end=limit;
        for(auto bits=live;bits;bits&=bits-1U) {
            const auto leaf=unsigned(__builtin_ctzll(bits));
            for(const auto &range:requests[leaf]) {
                if(range.first>rank)end=std::min(end,range.first);
                if(range.second>rank)end=std::min(end,range.second);
            }
        }
        return end;
    }
    bool overlaps(std::uint64_t live,std::uint32_t after=0)const {
        for(auto bits=live;bits;bits&=bits-1U) {
            const auto a=unsigned(__builtin_ctzll(bits));
            for(auto others=bits&(bits-1U);others;others&=others-1U) {
                const auto b=unsigned(__builtin_ctzll(others));
                for(const auto &x:requests[a])for(const auto &y:requests[b])
                    if(std::max({after,x.first,y.first})<std::min(x.second,y.second))return true;
            }
        }
        return false;
    }
};
}
