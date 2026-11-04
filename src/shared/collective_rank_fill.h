#pragma once
#include "rank_request_decisions.h"
#include <array>

namespace collective_fill {
using Mask=std::uint64_t;
struct Truth {Mask yes=0,no=0;}; // other live bits are SQL UNKNOWN
inline unsigned outcomes(int op){
    switch(op){case 1:return 2;case 2:return 1;case 3:return 3;
        case 4:return 4;case 5:return 6;case 6:return 5;}
    throw std::logic_error("invalid request operator");
}
struct Constants {
    unsigned width=0;
    std::array<int,64> operators{};
    std::array<std::uint32_t,64> lower{},upper{};
    std::array<std::vector<std::array<unsigned,3>>,64> extra;
    std::vector<unsigned> cuts;
    std::vector<Mask> masks;
    static bool accepts(unsigned value,int op,unsigned lo,unsigned hi){
        switch(op){case 1:return value>=lo && value<hi;
        case 2:return value<lo;case 3:return value<hi;
        case 4:return value>=hi;case 5:return value>=lo;
        case 6:return value<lo || value>=hi;}
        throw std::logic_error("uncompiled collective constant operator");
    }
    void compile(){
        rank_requests::width_mask(width);cuts={0};masks.clear();
        for(unsigned j=0;j<width;++j){cuts.push_back(lower[j]);cuts.push_back(upper[j]);for(auto c:extra[j]){cuts.push_back(c[1]);cuts.push_back(c[2]);}}
        std::sort(cuts.begin(),cuts.end());cuts.erase(std::unique(cuts.begin(),cuts.end()),cuts.end());
        for(unsigned value:cuts){Mask yes=0;
            for(unsigned j=0;j<width;++j){bool good=accepts(value,operators[j],lower[j],upper[j]);for(auto c:extra[j])good&=accepts(value,c[0],c[1],c[2]);if(good)yes|=Mask{1}<<j;}
            masks.push_back(yes);
        }
    }
    Truth compare(unsigned value)const{
        if(value==UINT32_MAX)return {};
        if(cuts.empty())throw std::logic_error("collective constants not compiled");
        const auto pos=std::upper_bound(cuts.begin(),cuts.end(),value)-cuts.begin()-1;
        const Mask yes=masks[pos];return {yes,rank_requests::width_mask(width)&~yes};
    }
};
struct Remap {
    bool identity=true;unsigned chunks=0;Mask live=0;
    std::vector<std::array<Mask,256>> tables;
    void configure(const std::vector<unsigned>& source,unsigned source_width){
        live=rank_requests::width_mask(source.size());
        for(unsigned j=0;j<source.size();++j)identity&=source[j]==j;
        if(identity)return;
        chunks=(source_width+7)/8;tables.resize(chunks);
        std::array<Mask,64> target{};for(unsigned j=0;j<source.size();++j)target[source[j]]|=Mask{1}<<j;
        for(unsigned k=0;k<chunks;++k)for(unsigned byte=0;byte<256;++byte){Mask result=0;
            for(unsigned b=0;b<8;++b)if(byte&(1U<<b))result|=target[k*8+b];tables[k][byte]=result;}
    }
    Mask operator()(Mask source)const{
        if(identity)return source&live;Mask result=0;
        for(unsigned k=0;k<chunks;++k)result|=tables[k][(source>>(8*k))&255];return result;
    }
};
// General plan-time routing between two request words. Each pair names an
// input and output bit; no per-request loop remains at runtime.
struct Scatter {
    bool identity=false;Mask mask=0;unsigned chunks=0;
    std::vector<std::array<Mask,256>> tables;
    void configure(const std::vector<std::pair<unsigned,unsigned>>& pairs){
        identity=true;std::array<Mask,64> destinations{};unsigned last=0;
        for(auto pair:pairs){if(pair.first>=64 || pair.second>=64)throw std::logic_error("invalid word route");
            destinations[pair.first]|=Mask{1}<<pair.second;mask|=Mask{1}<<pair.first;
            last=std::max(last,pair.first+1);identity&=pair.first==pair.second;}
        if(identity)return;chunks=(last+7)/8;tables.resize(chunks);
        for(unsigned k=0;k<chunks;++k)for(unsigned byte=0;byte<256;++byte){Mask result=0;
            for(unsigned b=0;b<8;++b)if(byte&(1U<<b))result|=destinations[k*8+b];tables[k][byte]=result;}
    }
    Mask operator()(Mask value)const{
        if(identity)return value&mask;Mask result=0;
        for(unsigned k=0;k<chunks;++k)result|=tables[k][(value>>(8*k))&255];return result;
    }
};
// Reusable rank-local union of COMPLETE witness decisions. Each interval
// carries a whole request mask. There is no per-branch container.
struct Union {
    std::vector<rank_requests::MaskedRange> pieces,temporary;
    Mask null_good=0;
    static void append(std::vector<rank_requests::MaskedRange>& out,unsigned lo,unsigned hi,Mask mask){
        if(lo>=hi)return;
        if(!out.empty() && out.back().hi==lo && out.back().mask==mask)out.back().hi=hi;
        else out.push_back({lo,hi,mask});
    }
    void reset(unsigned domain){pieces.clear();temporary.clear();null_good=0;append(pieces,0,domain,0);}
    void add(const std::vector<rank_requests::MaskedRange>& row,Mask nulls){
        temporary.clear();std::size_t a=0,b=0;
        while(a<pieces.size() && b<row.size()){
            auto x=pieces[a],y=row[b];append(temporary,std::max(x.lo,y.lo),std::min(x.hi,y.hi),x.mask|y.mask);
            if(x.hi<=y.hi)++a;if(y.hi<=x.hi)++b;
        }
        pieces.swap(temporary);null_good|=nulls;
    }
};
} // namespace collective_fill
