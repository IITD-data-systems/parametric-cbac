#pragma once
#include <cstdint>
#include <stdexcept>
#include <vector>

namespace posting_position {
struct Match {std::uint32_t position=UINT32_MAX,row=UINT32_MAX,count=0,scanned=0;};
// Only existing posting row IDs and forward ranks are read. No key set, hash,
// or tuple rank is constructed. Scan the entire slice to prove uniqueness.
template<class Row,class Admits>
Match scan(std::uint32_t begin,std::uint32_t end,Row row_at,Admits admits) {
    Match result;
    for(auto p=begin;p<end;++p) {
        const auto row=row_at(p);++result.scanned;
        if(admits(row)){++result.count;result.position=p;result.row=row;}
    }
    return result;
}
class Cells {
    std::vector<std::uint8_t> cells_;
public:
    void arrive(std::size_t rows){if(cells_.empty())cells_.assign((rows+3U)/4U,0U);}
    std::size_t bytes()const{return cells_.size();}
    unsigned get(std::uint32_t p)const{return cells_.empty() ? 0U : (cells_.at(p/4U)>>((p&3U)*2U))&3U;}
    void put(std::uint32_t p,bool good) {
        const auto old=get(p),value=good ? 1U : 2U;
        if(old && old!=value)throw std::logic_error("posting-position decision flipped");
        cells_.at(p/4U)|=value<<((p&3U)*2U);
    }
};
}
