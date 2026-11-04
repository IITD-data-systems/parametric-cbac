#pragma once
#include "collective_rank_fill.h"
#include <map>
#include <memory>

// Proofs at one entered rank. Payloads are boundary ranges and request masks,
// never rows, witness points or tuples of entering ranks.
struct WordEnvelopeStore {
    using Mask=std::uint64_t;using Range=rank_requests::MaskedRange;
    struct Piece {unsigned lo,hi;Mask good,nogood;};
    struct Cell {collective_fill::Union good,nogood;std::vector<Piece> joined;};
    struct Bank {unsigned domain=0,cardinality=0;std::vector<std::unique_ptr<Cell>> cells;};
    std::map<unsigned,Bank> banks;
    std::uint64_t bytes=0,entries=0,pieces=0,declines=0;
    struct Answer {Mask good=0,nogood=0;};
    static std::uint64_t payload(const Cell&c){return sizeof(Cell)+(c.good.pieces.capacity()+c.good.temporary.capacity()+c.nogood.pieces.capacity()+c.nogood.temporary.capacity())*sizeof(Range)+c.joined.capacity()*sizeof(Piece);}
    static void join(Cell &c){
        c.joined.clear();unsigned a=0,b=0;
        while(a<c.good.pieces.size()&&b<c.nogood.pieces.size()){
            auto g=c.good.pieces[a],n=c.nogood.pieces[b];auto lo=std::max(g.lo,n.lo),hi=std::min(g.hi,n.hi);
            if(g.mask&n.mask)throw std::logic_error("nested word envelope decision flipped");
            if(lo<hi){if(!c.joined.empty()&&c.joined.back().hi==lo&&c.joined.back().good==g.mask&&c.joined.back().nogood==n.mask)c.joined.back().hi=hi;
                else c.joined.push_back({lo,hi,g.mask,n.mask});}
            if(g.hi<=n.hi)++a;if(n.hi<=g.hi)++b;
        }
    }
    Answer probe(unsigned id,unsigned rank,unsigned value)const{
        if(value==UINT32_MAX)return {};
        auto found=banks.find(id);if(found==banks.end()||rank>=found->second.cells.size()||!found->second.cells[rank])return {};
        const auto &v=found->second.cells[rank]->joined;
        auto p=std::upper_bound(v.begin(),v.end(),value,[](unsigned x,const Piece&p){return x<p.lo;});
        if(p==v.begin())return {};--p;return value<p->hi?Answer{p->good,p->nogood}:Answer{};
    }
    bool put(unsigned id,unsigned rank,unsigned cardinality,unsigned domain,const collective_fill::Union &proof,Mask good,Mask nogood,std::uint64_t budget){
        if(!(good|nogood))return false;
        auto old=banks.find(id);const bool fresh=old==banks.end()||old->second.cells.empty();
        if(rank>=cardinality)throw std::logic_error("word envelope rank outside entered universe");
        Cell cell;const Cell *previous=nullptr;
        if(!fresh&&old->second.cells[rank])previous=old->second.cells[rank].get();
        if(previous)cell=*previous;else{cell.good.reset(domain);cell.nogood.reset(domain);}
        std::vector<Range> yes,no;for(auto p:proof.pieces){collective_fill::Union::append(yes,p.lo,p.hi,p.mask&good);collective_fill::Union::append(no,p.lo,p.hi,p.mask&nogood);}
        cell.good.add(yes,0);cell.nogood.add(no,0);join(cell);
        const auto before=previous?payload(*previous):0;
        const auto after=payload(cell);const auto wanted=bytes-before+after+(fresh?std::uint64_t(cardinality)*sizeof(std::unique_ptr<Cell>):0);
        if(wanted>budget){++declines;return false;}
        auto &bank=banks[id];if(fresh){bank.domain=domain;bank.cardinality=cardinality;bank.cells.resize(cardinality);}
        if(bank.domain!=domain||bank.cardinality!=cardinality)throw std::logic_error("word envelope domain changed");
        pieces+=cell.joined.size()-(previous?previous->joined.size():0);bytes=wanted;
        if(!previous)++entries;bank.cells[rank]=std::make_unique<Cell>(std::move(cell));return true;
    }
};
