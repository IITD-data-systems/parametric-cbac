#pragma once
#include <algorithm>
#include <cstdint>
#include <vector>

// Equal ranks compare equal values. Strictness belongs to each boundary.
struct OnlineIntervalCoverage {
    struct Interval { std::uint32_t start, end; bool start_closed, end_closed; };
    struct End { std::uint32_t rank; bool closed; };
    std::vector<Interval> intervals;
    std::vector<End> prefix;
    void add(Interval value) {
        if (value.start < value.end ||
            (value.start == value.end && value.start_closed && value.end_closed))
            intervals.push_back(value);
    }
    void finish() {
        std::sort(intervals.begin(), intervals.end(), [](auto a, auto b) {
            return a.start != b.start ? a.start < b.start : a.start_closed > b.start_closed;
        });
        prefix.clear();
        for (auto value : intervals) {
            End end{value.end, value.end_closed};
            if (!prefix.empty() && (prefix.back().rank > end.rank ||
                (prefix.back().rank == end.rank && prefix.back().closed))) end = prefix.back();
            prefix.push_back(end);
        }
    }
    bool covers(std::uint32_t t) const {
        std::size_t lo = 0, hi = intervals.size();
        while (lo < hi) {
            const auto mid = lo + (hi - lo) / 2;
            const auto value = intervals[mid];
            if (value.start < t || (value.start == t && value.start_closed)) lo = mid + 1;
            else hi = mid;
        }
        return lo && (prefix[lo - 1].rank > t ||
                     (prefix[lo - 1].rank == t && prefix[lo - 1].closed));
    }
};
