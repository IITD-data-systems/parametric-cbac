#pragma once
#include "rank_theta_decisions.h"
#include "composed_windows.h"
#include <algorithm>
#include <vector>

// Search/reduction kernels only. The query store owns the rank entry,
// directory and buffers and alone publishes its completed proof.
namespace rank_sorted {
    template<class Entry,class Interrupt>rank_summaries::Slot prepare(Entry&b,unsigned rank,std::vector<unsigned>&input,bool has_null,Interrupt interrupt){
        interrupt();std::uint64_t comparisons=0;
        std::sort(input.begin(),input.end(),[&](unsigned x,unsigned y){
            ++b.sort_comparisons;if(!(++comparisons%4096))interrupt();return x<y;});
        input.erase(std::unique(input.begin(),input.end()),input.end());interrupt();
        if(b.payload().slots.empty())b.payload().ranks.reserve(b.max_rows);
        if(b.view.probe(rank))throw std::logic_error("sorted rank summary filled twice");
        if(b.payload().ranks.size()+input.size()>b.max_rows)throw std::logic_error("sorted summary exceeded relation rank budget");
        rank_summaries::Slot slot;slot.offset=b.payload().ranks.size();slot.count=input.size();slot.ungrouped=has_null;
        b.payload().ranks.insert(b.payload().ranks.end(),input.begin(),input.end());
        interrupt();return slot;
    }

    template<class Entry,class Interrupt>rank_summaries::Slot prepare_prefix(Entry&b,unsigned rank,std::vector<unsigned>&input,Interrupt interrupt){
        const unsigned width=b.stride(),prefix=unsigned(b.equality_columns.size());
        if(!width||input.size()%width)throw std::logic_error("malformed sorted equality-prefix ranks");
        interrupt();std::vector<std::size_t>order(input.size()/width);
        for(std::size_t i=0;i<order.size();++i)order[i]=i;
        b.temporary_bytes=input.capacity()*sizeof(unsigned)+order.capacity()*sizeof(std::size_t);
        std::sort(order.begin(),order.end(),[&](std::size_t x_index,std::size_t y_index){
            if(!(++b.sort_comparisons%4096))interrupt();
            for(unsigned d=0;d<width;++d){auto x=input[x_index*width+d],y=input[y_index*width+d];if(x!=y)return x<y;}return false;});
        if(b.payload().slots.empty())b.payload().ranks.reserve(b.max_rows*width);
        if(b.view.probe(rank))throw std::logic_error("equality-prefix rank filled twice");
        rank_summaries::Slot slot;slot.offset=b.payload().ranks.size()/width;std::size_t previous=SIZE_MAX;
        const auto null_start=b.payload().null_prefixes.size();
        for(auto index:order){if(!(index%1024))interrupt();
            bool same=previous!=SIZE_MAX;
            if(same)for(unsigned d=0;d<width;++d)if(input[index*width+d]!=input[previous*width+d]){same=false;break;}
            if(same)continue;previous=index;
            const bool null_value=b.value_column!=UINT32_MAX&&input[index*width+prefix]==UINT32_MAX;
            if(null_value){b.payload().null_prefixes.insert(b.payload().null_prefixes.end(),input.begin()+index*width,input.begin()+index*width+prefix);continue;}
            b.payload().ranks.insert(b.payload().ranks.end(),input.begin()+index*width,input.begin()+(index+1)*width);++slot.count;
        }
        // One small descriptor per entered rank locates the NULL-presence
        // equality prefixes. No NULL or row data is stored in b.payload().ranks.
        if(b.payload().null_slots.empty())b.payload().null_slots.resize(b.cells.count());
        b.payload().null_slots[rank]={std::uint32_t(null_start/prefix),std::uint32_t((b.payload().null_prefixes.size()-null_start)/prefix)};
        interrupt();return slot;
    }
    template<class Entry>bool contains_prefix(Entry&b,unsigned rank,const std::vector<unsigned>&prefix,const rank_requests::Set&accepted){
        const auto&s=b.view.slot(rank);const auto width=b.stride(),n=unsigned(b.equality_columns.size());
        if(prefix.size()!=n||!b.view.probe(rank))throw std::logic_error("invalid equality-prefix lookup");
        const auto &storage=*b.view.payload;
        auto cmp=[&](std::uint64_t point){for(unsigned d=0;d<n;++d){auto v=storage.ranks[point*width+d];if(v!=prefix[d])return v<prefix[d]?-1:1;}return 0;};
        auto lower=[&](std::uint64_t lo,std::uint64_t hi,bool after){while(lo<hi){++b.binary_steps;auto mid=lo+(hi-lo)/2;auto c=cmp(mid);if(c<0||(after&&!c))lo=mid+1;else hi=mid;}return lo;};
        auto first=lower(s.offset,s.offset+s.count,false),last=lower(first,s.offset+s.count,true);
        if(b.value_column==UINT32_MAX)return first!=last&&accepted.has(0);
        for(auto range:accepted.ranges){auto lo=first,hi=last;while(lo<hi){++b.binary_steps;auto mid=lo+(hi-lo)/2;if(storage.ranks[mid*width+n]<range.lo)lo=mid+1;else hi=mid;}
            if(lo<last&&storage.ranks[lo*width+n]<range.hi)return true;}
        if(accepted.null_good&&!storage.null_slots.empty()){
            const auto&s=storage.null_slots[rank];auto lo=std::uint64_t(s.offset),hi=lo+s.count;
            while(lo<hi){++b.binary_steps;auto mid=lo+(hi-lo)/2;int c=0;for(unsigned d=0;d<n;++d){auto v=storage.null_prefixes[mid*n+d];if(v!=prefix[d]){c=v<prefix[d]?-1:1;break;}}
                if(c<0)lo=mid+1;else hi=mid;}
            if(lo<std::uint64_t(s.offset)+s.count){bool equal=true;for(unsigned d=0;d<n;++d)equal&=storage.null_prefixes[lo*n+d]==prefix[d];if(equal)return true;}
        }
        return false;
    }
    template<class Entry>bool contains(const Entry&b,unsigned rank,const rank_requests::Set&accepted){
        const auto &slot=b.view.slot(rank);if(!b.view.probe(rank))throw std::logic_error("unknown sorted summary probed");
        if(accepted.null_good&&slot.ungrouped)return true;
        const auto first=b.view.payload->ranks.begin()+slot.offset,last=first+slot.count;
        for(auto range:accepted.ranges){auto at=std::lower_bound(first,last,range.lo);
            if(at!=last&&*at<range.hi)return true;}
        return false;
    }
} // namespace rank_sorted
