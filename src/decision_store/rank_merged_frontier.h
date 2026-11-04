#pragma once
#include <algorithm>
#include <cstdint>
#include <limits>
#include <memory_resource>
#include <stdexcept>
#include <utility>
#include <vector>
#include "rank_witness_types.h"

// A vector always comes from ONE complete witness. Its mask says which
// conjunctive requests may use that witness. No row identifier is retained.
namespace rank_merged {
using Mask=std::uint64_t;
constexpr auto null_rank=UINT32_MAX;
struct Test {unsigned dimension=0;int op=1;};
struct Vector {std::vector<std::uint32_t> ranks;Mask mask=0;};
struct Input {
    unsigned dimension=0,value=null_rank;
    Mask present=0;
    Mask accept[3]{}; // local < filled, local == filled, local > filled
};
struct GroupKey {Mask mask=0;std::vector<unsigned> ranks;};

struct Frontier {
    unsigned dimensions=0,width=0;
    std::vector<std::vector<Test>> tests;
    std::vector<unsigned> equalities;
    rank_summaries::WitnessPayload &storage;
    std::uint64_t dominance_checks=0,points_checked=0,equality_searches=0;
    struct Range {std::uint64_t begin,end;Mask mask;};
    std::vector<Range> ranges_,visits_;
    explicit Frontier(rank_summaries::WitnessPayload &payload):storage(payload){}
    std::uint64_t bytes()const{return storage.ranks.size()*sizeof(std::uint32_t)+storage.masks.size()*sizeof(Mask);}
    // Each request has its OWN operator directions. Unioning operator sets
    // here would incorrectly prevent dominance for heterogeneous requests.
    bool dominates(const Vector &a,const Vector &b,unsigned request)const{
        for(auto t:tests.at(request)){
            const auto x=a.ranks[t.dimension],y=b.ranks[t.dimension];
            if(x==y)continue;
            if(x==null_rank||y==null_rank)return false;
            switch(t.op){
                case 1:case 6:return false;
                case 2:case 3:if(x>y)return false;break;
                case 4:case 5:if(x<y)return false;break;
                default:throw std::logic_error("invalid merged frontier operator");
            }
        }
        return true;
    }
    template<class Interrupt>
    void reduce(std::vector<Vector>&complete,Interrupt interrupt){
        // Sorting only changes the order of reduction. Different requests
        // may prefer different directions; reverse dominance is checked too.
        std::uint64_t work=0;
        std::sort(complete.begin(),complete.end(),[&](const Vector&a,const Vector&b){
            if(!(++work%4096))interrupt();return a.ranks<b.ranks;});
        std::vector<Vector> kept;kept.reserve(complete.size());
        for(auto &point:complete){interrupt();
            if(point.ranks.size()!=dimensions)throw std::logic_error("merged vector shape changed");
            for(auto &old:kept){
                if(!(++work%1024))interrupt();
                if(old.ranks==point.ranks){point.mask|=old.mask;old.mask=0;continue;}
                auto common=point.mask&old.mask;
                while(common){const auto bit=unsigned(__builtin_ctzll(common));common&=common-1;
                    if(!(++dominance_checks%1024))interrupt();
                    if(dominates(old,point,bit))point.mask&=~(Mask{1}<<bit);
                    else if(dominates(point,old,bit))old.mask&=~(Mask{1}<<bit);
                }
                if(!point.mask)break;
            }
            kept.erase(std::remove_if(kept.begin(),kept.end(),[](const Vector&p){return !p.mask;}),kept.end());
            if(point.mask)kept.push_back(std::move(point));
        }
        if(!equalities.empty())std::sort(kept.begin(),kept.end(),[&](const Vector&a,const Vector&b){
            if(!(++work%4096))interrupt();
            for(auto d:equalities)if(a.ranks[d]!=b.ranks[d])return a.ranks[d]<b.ranks[d];
            return a.ranks<b.ranks;
        });
        complete.swap(kept);
    }
    std::uint64_t append(const std::vector<Vector>&complete){
        const auto offset=storage.masks.size();
        for(const auto&p:complete){storage.masks.push_back(p.mask);storage.ranks.insert(storage.ranks.end(),p.ranks.begin(),p.ranks.end());}
        return offset;
    }
    std::pair<std::uint64_t,std::uint64_t> equality_slice(std::uint64_t offset,unsigned count,
        const std::vector<unsigned>&key){
        if(key.size()!=equalities.size())throw std::logic_error("merged equality key shape changed");
        ++equality_searches;
        for(auto rank:key)if(rank==null_rank)return {offset,offset};
        auto compare=[&](std::uint64_t i){
            for(unsigned k=0;k<equalities.size();++k){auto value=storage.ranks[i*dimensions+equalities[k]];
                if(value<key[k])return -1;if(value>key[k])return 1;}return 0;
        };
        auto lo=offset,hi=offset+count;
        while(lo<hi){const auto mid=lo+(hi-lo)/2;if(compare(mid)<0)lo=mid+1;else hi=mid;}
        const auto begin=lo;hi=offset+count;
        while(lo<hi){const auto mid=lo+(hi-lo)/2;if(compare(mid)<=0)lo=mid+1;else hi=mid;}
        return {begin,lo};
    }
    template<class Interrupt>
    Mask lookup(std::uint64_t offset,unsigned count,Mask live,const std::vector<Input>&inputs,
                const std::vector<GroupKey>&keys,Interrupt interrupt){
        visits_.clear();
        if(equalities.empty())visits_.push_back({offset,offset+count,live});
        else {ranges_.clear();
            for(const auto&key:keys){auto span=equality_slice(offset,count,key.ranks);
                if(span.first<span.second)ranges_.push_back({span.first,span.second,key.mask&live});}
            std::sort(ranges_.begin(),ranges_.end(),[](const Range&a,const Range&b){return a.begin<b.begin;});
            // Equal keys have equal ranges; unequal keys have disjoint ranges.
            // Coalesce them so each stored vector is inspected at most once.
            for(auto r:ranges_){if(!r.mask)continue;
                if(!visits_.empty()&&r.begin==visits_.back().begin&&r.end==visits_.back().end)visits_.back().mask|=r.mask;
                else visits_.push_back(r);}
        }
        Mask yes=0;
        for(const auto&span:visits_)for(auto i=span.begin;i<span.end&&(live&~yes);++i){
            if(!(++points_checked%1024))interrupt();
            Mask answer=storage.masks[i]&span.mask&live&~yes;
            for(const auto&test:inputs){const auto needed=answer&test.present;if(!needed)continue;
                const auto value=storage.ranks[i*dimensions+test.dimension];
                if(value==null_rank||test.value==null_rank)answer&=~test.present; // UNKNOWN is not a witness
                else {const auto outcome=value<test.value?0:value==test.value?1:2;
                    answer&=~test.present|test.accept[outcome];}
                if(!answer)break;
            }
            yes|=answer;
        }
        return yes;
    }
};
} // namespace rank_merged
