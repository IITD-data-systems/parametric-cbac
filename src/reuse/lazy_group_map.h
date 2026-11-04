#pragma once
#include <algorithm>
#include <array>
#include <cstdint>
#include <vector>

// One reached unary posting, indexed by its other equality ranks. Duplicates stay.
class LazyGroupMap {
public:
    using Key=std::array<std::uint32_t,16>;
    struct Entry {Key key{};std::uint32_t row=0;};
    std::vector<Entry> entries;
    template<class Read> void build(std::uint32_t begin,std::uint32_t end,Read read) {
        entries.reserve(end-begin);
        for(auto i=begin;i<end;++i)entries.push_back(read(i));
        std::sort(entries.begin(),entries.end(),[](const Entry &a,const Entry &b){return a.key<b.key;});
    }
    void lookup(const Key &key,std::vector<std::uint32_t> &out) const {
        out.clear();
        for(auto rank:key)if(rank==UINT32_MAX)return;
        auto it=std::lower_bound(entries.begin(),entries.end(),key,
                                [](const Entry &a,const Key &b){return a.key<b;});
        for(;it!=entries.end() && it->key==key;++it)out.push_back(it->row);
    }
};
