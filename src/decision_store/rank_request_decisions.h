#pragma once
#include <algorithm>
#include <cstdint>
#include <memory_resource>
#include <stdexcept>
#include <vector>

// Query-bound decisions only. Endpoints are boundary ranks, never witness
// coordinates. A temporary RangeSet is the union of COMPLETE witnesses for
// one request; no pieces of different witnesses are conjoined.
namespace rank_requests {
struct Range {std::uint32_t lo,hi;}; // [lo,hi), excluding SQL NULL
struct Set {
    std::vector<Range> ranges;
    bool null_good=false;
    void add(std::uint32_t lo,std::uint32_t hi){
        if(lo>=hi)return;
        Range value{lo,hi};auto at=ranges.begin();
        while(at!=ranges.end() && at->hi<value.lo)++at;
        while(at!=ranges.end() && at->lo<=value.hi){
            value.lo=std::min(value.lo,at->lo);value.hi=std::max(value.hi,at->hi);
            at=ranges.erase(at);
        }
        ranges.insert(at,value);
    }
    bool has(std::uint32_t rank)const{
        if(rank==UINT32_MAX)return null_good;
        for(auto range:ranges){if(rank<range.lo)return false;if(rank<range.hi)return true;}
        return false;
    }
};
struct Cell {
    std::uint64_t G=0,X=0,N=0; // N is the decision for a filled SQL NULL
    std::uint32_t nu=UINT32_MAX,fallback=UINT32_MAX;
};
struct MaskedRange {std::uint32_t lo,hi;std::uint64_t mask;};
struct MaskedSlot {std::uint32_t offset,count;};
inline std::uint64_t width_mask(unsigned width){
    if(width<1 || width>64)throw std::logic_error("request-mask width outside 1..64");
    return width==64?~std::uint64_t{0}:(std::uint64_t{1}<<width)-1;
}
// Plan/counter metadata has no owning answer array. Cells owns Payload.
struct MaskLayout {
    unsigned width=0,domain=0;bool filled_operand=false;
    std::uint64_t fallbacks=0,mask_checks=0,epoch=UINT64_MAX,answer=0;
    unsigned rank=UINT32_MAX,value=UINT32_MAX;const void *indirect=nullptr;
    void configure(unsigned w,unsigned d,bool filled){width_mask(w);width=w;domain=d;filled_operand=filled;}
};
struct MaskPayload {
    std::pmr::vector<std::uint64_t> A;
    std::pmr::vector<Cell> cells;
    std::pmr::vector<MaskedRange> boundaries;
    std::pmr::vector<MaskedSlot> slots;
    explicit MaskPayload(std::pmr::memory_resource*m):A(m),cells(m),boundaries(m),slots(m){}
    std::uint64_t bytes()const{return A.size()*8+cells.size()*sizeof(Cell)+boundaries.size()*sizeof(MaskedRange)+slots.size()*sizeof(MaskedSlot);}
};
// One collective proof partition, including the compact all/except-one form.
inline void record_masks(MaskLayout&p,MaskPayload&data,unsigned rank,unsigned cardinality,
    const std::vector<MaskedRange>&partition,std::uint64_t null_good){
    if(!p.filled_operand){if(data.A.empty())data.A.resize(cardinality);
        data.A[rank]=partition.empty()?0:partition.front().mask;return;}
    if(data.cells.empty())data.cells.resize(cardinality);
    Cell c;c.N=null_good;const auto live=width_mask(p.width);
    std::uint64_t common=live,any=0,seen=0,multiple=0;
    for(auto r:partition){common&=r.mask;any|=r.mask;const auto bad=live&~r.mask;
        if(r.hi-r.lo==1){multiple|=seen&bad;seen|=bad;}else multiple|=bad;}
    c.G=common;const auto partial=any&~common;c.X=partial&~multiple;
    bool fallback=partial!=c.X;
    for(auto r:partition)if(r.hi-r.lo==1&&(c.X&~r.mask)){
        if(c.nu!=UINT32_MAX&&c.nu!=r.lo)fallback=true;c.nu=r.lo;}
    if(fallback){++p.fallbacks;c.fallback=data.slots.size();
        data.slots.push_back({std::uint32_t(data.boundaries.size()),std::uint32_t(partition.size())});
        data.boundaries.insert(data.boundaries.end(),partition.begin(),partition.end());}
    data.cells[rank]=c;
}
// Direct filled ranks and transferred equality ranges share this lookup.
// Matches/Except operate on boundaries, never on retained row attributes.
template<class Matches,class Except>
std::uint64_t read_masks(MaskLayout&p,const MaskPayload&data,unsigned rank,unsigned value,
    std::uint64_t epoch,const void*indirect,bool null_value,Matches matches,Except except){
    if(p.indirect==indirect&&p.epoch==epoch&&p.rank==rank&&p.value==value)return p.answer;
    ++p.mask_checks;p.indirect=indirect;p.epoch=epoch;p.rank=rank;p.value=value;
    if(!p.filled_operand)return p.answer=data.A[rank];
    const auto &c=data.cells[rank];if(null_value)return p.answer=c.N;
    if(c.fallback==UINT32_MAX)return p.answer=c.G|(except(c.nu)?c.X:0);
    const auto&s=data.slots[c.fallback];
    for(unsigned i=0;i<s.count;++i){const auto&r=data.boundaries[s.offset+i];
        if(matches(Range{r.lo,r.hi}))return p.answer=r.mask;}
    return p.answer=0;
}
} // namespace rank_requests
