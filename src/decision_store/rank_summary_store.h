#pragma once
#include <array>
#include <chrono>
#include <map>
#include <algorithm>
#include "diagnostic_counter.h"
#include <cstdint>
#include <memory_resource>
#include <stdexcept>
#include <vector>
#include "rank_request_decisions.h"
#include "rank_theta_decisions.h"
#include "rank_merged_frontier.h"
#include "composed_windows.h"

// The decision store's on-arrival form for a complete functional witness.
// Six tests use729 SQL FALSE/TRUE/UNKNOWN states in a96-byte mask.
// Larger forms retain the ordinary dense/packed decision path.
namespace rank_summaries {
struct Summary {
    unsigned dimensions,states=1;
    std::array<unsigned,max_tests> operators{}; // set of normalized request operators
    composed_windows::Cells cells;
    composed_windows::Cells::WitnessReadView view;
    rank_requests::MaskLayout decisions;
    rank_theta::Layout theta;
    rank_merged::Frontier merged;
    // Sorted/prefix ranks are another layout of this common entry, not an
    // executor-owned bank or a second completion directory.
    bool sorted_mode=false;
    unsigned column=0,value_column=0;
    bool fact_mode=false;
    std::vector<unsigned> fact_columns;
    std::uint64_t fact_requests=0;
    bool equality_mode=false,proof_mode=false,proof_sparse=false,region_window_mode=false;
    unsigned parameter_column=0,parameter_domain=0,region_predicate=0;
    std::uint64_t range_comparisons=0,region_count=0;
    std::vector<unsigned> requests,equality_columns;
    std::uint64_t max_rows=0,rows=0,empty_rejections=0,rows_skipped=0;
    std::uint64_t temporary_bytes=0,sort_comparisons=0,binary_steps=0;
    unsigned stride()const{return equality_columns.size()+(value_column!=UINT32_MAX);}
    bool merged_mode=false;
    unsigned merged_request_count=0;
    std::uint64_t merged_rows_read=0;
    bool measured_admission=false,frontier_dropped=false;
    std::uint64_t measured_rows=0,frontier_fill_attempts=0,decision_entries=0,decision_rows=0,suppressed_probes=0;
    std::uint64_t neq_certificate_attempts=0,neq_eligibility_checks=0,neq_certificates=0,neq_points_removed=0,neq_search_steps=0;
    unsigned neq_dimensions_seen=0;
    unsigned raw_tests=0,folded_constant_tests=0;
    std::uint64_t frontier_arrivals=0,equality_searches=0,equality_key_comparisons=0;
    std::uint64_t equality_group_hits=0,equality_group_misses=0,equality_points_excluded=0;
    std::uint64_t ungrouped_points_checked=0;
    bool decision_mode=false;
    bool theta_mode=false;
    std::pmr::vector<std::uint64_t> reached_bits;
    std::uint64_t distinct_reached=0,present_ranks=0;
    std::uint64_t probes=0,hits=0,fills=0,candidates=0,dominated=0,checks=0;
    std::uint64_t target_rows=0,gate_declines=0;unsigned maximum_frontier=0;
    std::uint64_t collective_fills=0,collective_rows=0,collective_formula_steps=0,collective_comparisons=0;
    std::uint64_t collective_child_projections=0,per_request_formula_evaluations=0;
    bool tablewide=false;
    std::uint64_t reserved_bytes=0,fill_rows_visited=0,reduction_points_visited=0,dominance_comparisons=0;
    std::uint64_t fill_input_bytes=0,reduction_temporary_bytes=0;
    double estimated_rows_per_rank=0,estimated_points_per_rank=0,estimated_repeats=0,estimated_summary_work=0,estimated_walk_work=0;
    std::uint64_t collection_ns=0,reduction_ns=0,probe_ns=0;
    struct Phase {
        std::uint64_t &total;std::chrono::steady_clock::time_point start;
        explicit Phase(std::uint64_t&t):total(t){CF_COUNT(start=std::chrono::steady_clock::now(););}
        ~Phase(){CF_COUNT(total+=std::chrono::duration_cast<std::chrono::nanoseconds>(std::chrono::steady_clock::now()-start).count(););}
    };
    unsigned active_rank=UINT32_MAX;bool fill_active=false;
    std::uint64_t stored_bytes()const{
        return cells.bytes()+reached_bits.size()*8;
    }
    std::uint64_t last_epoch=UINT64_MAX;unsigned last_rank=UINT32_MAX;
    const Slot *last_slot=nullptr;
    Summary(unsigned count,const std::vector<int> &ops,std::pmr::memory_resource *memory)
        :dimensions(ops.size()),merged(prepare_cells(cells,count,memory)),reached_bits(memory),flag_tables(memory){
        if(dimensions>max_tests)throw std::logic_error("summary does not fit the compact decision form");
        for(unsigned i=0;i<dimensions;++i){operators[i]=1U<<ops[i];states*=3;}
        view=cells.witness_read_view();
    }
    rank_summaries::WitnessPayload &payload(){return cells.witness_payload();}
    const rank_summaries::WitnessPayload &payload()const{return cells.witness_payload();}
    static WitnessPayload &prepare_cells(composed_windows::Cells &cells,unsigned count,std::pmr::memory_resource *memory){
        cells.plan_witness(count,memory);return cells.witness_payload();
    }
    // Whole-query opportunity, not a short prefix's repeat rate. A node may
    // suppress new writes once it has reached at least as many distinct ranks
    // as there are targets and has seen no reuse. Existing summaries remain
    // readable; observing a repeat opens admission again. No decision changes.
    bool admit_new()const{
        if(frontier_dropped || !cells.recording())return false;
        if(decision_mode && tablewide){
            // The whole table supplies an opportunity estimate even when its
            // physical-order prefix has no repeats. For low-opportunity
            // targets wait for actual table-wide reuse, not a 1024-probe window.
            return target_rows>=2*present_ranks || probes>=2*distinct_reached+64;
        }
        return !tablewide || fills<target_rows || hits>0;
    }
    // Sufficient, operator-parametric dominance. A's result table includes B's;
    // each differing rank moves A's input only in a direction in which A's
    // formula is monotone. Equality/exclusion values may differ only when that
    // input is irrelevant. Thus different witnesses' pieces are never mixed.
    struct Flags {unsigned positive=0,negative=0,independent=0,population=0,required_true=0;};
    mutable std::pmr::map<std::array<std::uint64_t,state_words>,Flags> flag_tables;
    mutable std::uint64_t flag_tables_built=0;
    const Flags &flags(const Bits &good)const{
        auto old=flag_tables.find(good.words);if(old!=flag_tables.end())return old->second;
        Flags f;for(auto word:good.words)f.population+=__builtin_popcountll(word);
        unsigned stride=1;
        for(unsigned d=0;d<dimensions;++d,stride*=3){bool positive=true,negative=true,independent=true,required=true;
            for(unsigned k=0;k<states;++k)if((k/stride)%3==0){const bool no=good.get(k),yes=good.get(k+stride),unknown=good.get(k+2*stride);
                positive&=!no||yes;negative&=!yes||no;independent&=no==yes&&yes==unknown;required&=!no&&!unknown;}
            f.positive|=unsigned(positive)<<d;f.negative|=unsigned(negative)<<d;f.independent|=unsigned(independent)<<d;f.required_true|=unsigned(required)<<d;
        }
        ++flag_tables_built;return flag_tables.emplace(good.words,f).first->second;
    }
    bool dominates(const Point&a,const Point&b,const Flags&f)const{
        for(unsigned d=0;d<dimensions;++d){if(a.ranks[d]==b.ranks[d]||(f.independent&(1U<<d)))continue;
            if(a.ranks[d]==null_rank||b.ranks[d]==null_rank)return false;
            const unsigned less=(1U<<2)|(1U<<3),greater=(1U<<4)|(1U<<5),ops=operators[d];
            const bool low=ops&&!(ops&~less),high=ops&&!(ops&~greater);
            if(!low&&!high)return false;const bool more=low?a.ranks[d]<b.ranks[d]:a.ranks[d]>b.ranks[d];
            if(!((more?f.positive:f.negative)&(1U<<d)))return false;
        }
        return includes(a.good,b.good);
    }
    bool dominates(const Point&a,const Point&b)const{return dominates(a,b,flags(a.good));}
    struct Prepared {const Point *point;const Flags *traits;};
    bool before(const Prepared&a,const Prepared&b)const{
        if(a.traits->population!=b.traits->population)return a.traits->population>b.traits->population;
        if(a.point->good.words!=b.point->good.words)return a.point->good.words<b.point->good.words;
        const auto&f=*a.traits;
        for(unsigned d=0;d<dimensions;++d){if(f.independent&(1U<<d))continue;
            const auto x=a.point->ranks[d],y=b.point->ranks[d];if(x==y)continue;
            if(x==null_rank||y==null_rank)return x<y;
            const unsigned less=(1U<<2)|(1U<<3),greater=(1U<<4)|(1U<<5),ops=operators[d];
            const bool low=ops&&!(ops&~less),high=ops&&!(ops&~greater);
            if(!low&&!high)return x<y;
            if(f.positive&(1U<<d))return low?x<y:x>y;
            if(f.negative&(1U<<d))return low?x>y:x<y;
            return x<y;
        }return false;
    }

    static constexpr std::uint64_t frontier_minimum_rows=100000;
    // Hard storage bound, not a no-dominance benefit estimate. During
    // probation a bank can retain every collected row below the threshold.
    static std::uint64_t frontier_point_capacity(std::uint64_t rows){
        return rows;
    }
    bool admission_judged=false,frontier_walk_finished=false,present_ranks_known=false;
    unsigned admission_basis=0; // 1: rows; 2: all present ranks; 3: walk ended
    std::uint64_t present_ranks_filled=0;
    std::uint64_t first_judgment_rows=0,first_judgment_entries=0;unsigned first_judgment_basis=0;
    std::uint64_t judgment_present_rank_slices=0;
    bool judge_frontier(std::uint64_t entries,bool completing_present_rank=false,bool finished_walk=false,bool only_if_drop=false){
        if(!measured_admission||frontier_dropped)return !frontier_dropped;
        unsigned basis=0;
        if(measured_rows>=frontier_minimum_rows)basis=1;
        else if(present_ranks_known&&present_ranks_filled+unsigned(completing_present_rank)>=present_ranks)basis=2;
        else if(finished_walk)basis=3;
        if(!basis)return true;
        if(only_if_drop&&entries<=measured_rows)return true;
        if(!admission_judged){first_judgment_rows=measured_rows;first_judgment_entries=entries;first_judgment_basis=basis;}
        admission_judged=true;admission_basis=basis;
        judgment_present_rank_slices=present_ranks_filled+unsigned(completing_present_rank);
        decision_entries=entries;decision_rows=measured_rows;
        if(entries<=measured_rows)return true;
        frontier_dropped=true;
        cells.discard_witnesses();
        view=cells.witness_read_view();
        std::pmr::vector<std::uint64_t>(reached_bits.get_allocator().resource()).swap(reached_bits);
        flag_tables.clear();last_slot=nullptr;last_epoch=UINT64_MAX;last_rank=UINT32_MAX;
        fill_active=false;reduction_temporary_bytes=0;return false;
    }
    void finish_walk(){
        frontier_walk_finished=true;
        // Only a completed target walk proves there are no more arrivals
        // when the reached ranks are a strict subset of present ranks.
        if(measured_admission&&!frontier_dropped&&frontier_fill_attempts)
            (void)judge_frontier(payload().points.size(),false,true);
    }


    unsigned neq_dimensions()const{
        unsigned result=0;for(unsigned d=0;d<dimensions;++d)
            if(operators[d]&(1U<<6))result|=1U<<d;
        return result;
    }
    unsigned pure_neq_dimensions()const{
        unsigned result=0;for(unsigned d=0;d<dimensions;++d)
            if(operators[d]==(1U<<6))result|=1U<<d;
        return result;
    }
    unsigned any_neq_dimensions()const{return neq_dimensions();}
    // Outside its excluded ranks, this point must cover q's full good table.
    // A syntactic != under NOT need not be an exclusion: require the cached
    // truth-table direction as well. NULL differences and equality groups
    // retain the ordinary dominance safety checks.
    bool covers_except_neq(const Prepared&a,const Prepared&q,unsigned neq)const{
        if(!includes(a.point->good,q.point->good))return false;
        const auto&f=*a.traits;
        for(unsigned d=0;d<dimensions;++d){
            const unsigned bit=1U<<d;
            if((neq&bit)&&(q.traits->independent&bit))continue;
            if(a.point->ranks[d]==q.point->ranks[d]||(f.independent&bit))continue;
            if(a.point->ranks[d]==null_rank||q.point->ranks[d]==null_rank)return false;
            if(neq&bit){
                if(!(f.positive&bit))return false;
                const unsigned ops=operators[d];
                if(ops&(1U<<1))return false; // equality groups stay unchanged
                const bool lower=a.point->ranks[d]<q.point->ranks[d];
                if((ops&((1U<<2)|(1U<<3)))&&!((lower?f.positive:f.negative)&bit))return false;
                if((ops&((1U<<4)|(1U<<5)))&&!((lower?f.negative:f.positive)&bit))return false;
                continue;
            }
            const unsigned less=(1U<<2)|(1U<<3),greater=(1U<<4)|(1U<<5),ops=operators[d];
            const bool low=ops&&!(ops&~less),high=ops&&!(ops&~greater);
            if(!low&&!high)return false;
            const bool more=low?a.point->ranks[d]<q.point->ranks[d]:a.point->ranks[d]>q.point->ranks[d];
            if(!((more?f.positive:f.negative)&bit))return false;
        }
        return true;
    }
    template<class Interrupt>
    bool neq_certificate(const Prepared&q,const std::vector<Prepared>&kept,
                         unsigned neq,Interrupt&interrupt){
        ++neq_certificate_attempts;
        const unsigned active=neq&~q.traits->independent;
        neq_dimensions_seen|=active;
        const unsigned needed=unsigned(__builtin_popcount(active))+1;
        std::vector<const Prepared*> eligible;eligible.reserve(kept.size());
        for(const auto&point:kept){
            if(!(++neq_eligibility_checks%1024))interrupt();
            if(covers_except_neq(point,q,neq))eligible.push_back(&point);
        }
        if(eligible.size()<needed)return false;
        std::array<const Prepared*,max_tests+1> chosen{};
        const auto compatible=[&](const Prepared*p,unsigned count){
            for(unsigned k=0;k<count;++k)for(unsigned d=0;d<dimensions;++d)
                if((active&(1U<<d))&&p->point->ranks[d]==chosen[k]->point->ranks[d])return false;
            return true;
        };
        // Exact bounded-depth matching, not greedy distinct counts. Separate
        // coordinates having enough values is necessary but not sufficient.
        const auto search=[&](auto&&self,std::size_t begin,unsigned count)->bool{
            const unsigned remaining=needed-count;
            if(!remaining)return true;
            if(eligible.size()-begin<remaining)return false;
            std::array<std::array<unsigned,max_tests+1>,max_tests> values{};
            std::array<unsigned,max_tests> distinct{};unsigned available=0;
            for(std::size_t i=begin;i<eligible.size();++i){
                if(!(++neq_search_steps%1024))interrupt();
                const auto*p=eligible[i];if(!compatible(p,count))continue;++available;
                for(unsigned d=0;d<dimensions;++d)if((active&(1U<<d))&&distinct[d]<remaining){
                    bool seen=false;for(unsigned k=0;k<distinct[d];++k)seen|=values[d][k]==p->point->ranks[d];
                    if(!seen)values[d][distinct[d]++]=p->point->ranks[d];
                }
            }
            if(available<remaining)return false;
            for(unsigned d=0;d<dimensions;++d)if((active&(1U<<d))&&distinct[d]<remaining)return false;
            for(std::size_t i=begin;i<eligible.size();++i){
                if(!(++neq_search_steps%1024))interrupt();
                if(!compatible(eligible[i],count))continue;
                chosen[count]=eligible[i];if(self(self,i+1,count+1))return true;
            }
            return false;
        };
        const bool proved=search(search,0,0);
        if(proved){++neq_certificates;++neq_points_removed;}
        return proved;
    }


    unsigned equality_dimensions()const{
        unsigned mask=0;for(unsigned d=0;d<dimensions;++d)if(operators[d]==(1U<<1))mask|=1U<<d;return mask;
    }
    bool equality_required(const Prepared&p,unsigned mask)const{return (p.traits->required_true&mask)==mask;}
    template<class Interrupt>
    unsigned order_equality_groups(std::vector<Prepared>&kept,Interrupt&interrupt){
        const unsigned mask=equality_dimensions();if(!mask)return kept.size();
        std::uint64_t steps=0;
        std::sort(kept.begin(),kept.end(),[&](const Prepared&a,const Prepared&b){
            if(!(++steps%4096))interrupt();
            const bool ga=equality_required(a,mask),gb=equality_required(b,mask);
            if(ga!=gb)return !ga; // exact residuals for OR/NOT before the indexed tail
            for(unsigned d=0;d<dimensions;++d)if(mask&(1U<<d))
                if(a.point->ranks[d]!=b.point->ranks[d])return a.point->ranks[d]<b.point->ranks[d];
            return false;
        });
        unsigned fallback=0;while(fallback<kept.size()&&!equality_required(kept[fallback],mask))++fallback;
        return fallback;
    }
    std::pair<std::uint64_t,std::uint64_t> equality_slice(unsigned rank,
        const std::array<std::uint32_t,max_tests>&key,bool usable=true){
        const auto&s=view.slot(rank);const auto begin=s.offset+s.ungrouped,end=s.offset+s.count;
        const auto mask=equality_dimensions();
        if(!mask||!usable)return {begin,end};
        ++equality_searches;
        for(unsigned d=0;d<dimensions;++d)if((mask&(1U<<d))&&key[d]==null_rank){
            equality_points_excluded+=end-begin;++equality_group_misses;return {begin,begin};}
        const auto compare_key=[&](const Point&p){
            ++equality_key_comparisons;
            for(unsigned d=0;d<dimensions;++d)if(mask&(1U<<d)){
                if(p.ranks[d]<key[d])return -1;if(p.ranks[d]>key[d])return 1;}
            return 0;
        };
        auto lo=begin,hi=end;
        while(lo<hi){const auto mid=lo+(hi-lo)/2;if(compare_key(view.point(mid))<0)lo=mid+1;else hi=mid;}
        const auto first=lo;hi=end;
        while(lo<hi){const auto mid=lo+(hi-lo)/2;if(compare_key(view.point(mid))<=0)lo=mid+1;else hi=mid;}
        equality_points_excluded+=(end-begin)-(lo-first);
        if(first<lo)++equality_group_hits;else ++equality_group_misses;
        return {first,lo};
    }

    struct NoInterrupt {void operator()()const{}};
    template<class Publish,class Interrupt>
    bool reduce_points(unsigned rank,const std::vector<Point>&complete,Publish publish,Interrupt interrupt){
        if(frontier_dropped || !cells.recording())return false;
        Phase phase(reduction_ns);active_rank=rank;fill_active=true;++frontier_fill_attempts;
        measured_rows+=complete.size();std::vector<Prepared> ordered;ordered.reserve(complete.size());
        for(const auto &p:complete){++candidates;if(!p.good.empty())ordered.push_back({&p,&flags(p.good)});}
        std::uint64_t comparisons=0;
        std::sort(ordered.begin(),ordered.end(),[&](const Prepared&a,const Prepared&b){if(!(++comparisons%4096))interrupt();return before(a,b);});
        const unsigned neq=neq_dimensions();
        std::vector<Prepared> kept;interrupt();
        for(const auto &p:ordered){++reduction_points_visited;if(!(reduction_points_visited%64))interrupt();bool beaten=false;
            for(const auto &old:kept){++dominance_comparisons;if(!(dominance_comparisons%1024))interrupt();
                if(dominates(*old.point,*p.point,*old.traits)){beaten=true;break;}}
            if(!beaten&&neq)beaten=neq_certificate(p,kept,neq,interrupt);
            if(beaten){++dominated;continue;}kept.push_back(p);
            reduction_temporary_bytes=ordered.capacity()*sizeof(Prepared)+kept.capacity()*sizeof(Prepared);
            // Judge the observed kept set against the same quarter rule.
            // Dropping a bank only suppresses storage; the walk answers it.
            if(!judge_frontier(payload().points.size()+kept.size(),!complete.empty(),false,true))return false;
        }
        interrupt();const unsigned ungrouped=order_equality_groups(kept,interrupt);
        const Slot slot{payload().points.size(),unsigned(kept.size()),ungrouped};
        for(const auto&p:kept)payload().points.push_back(*p.point);
        if(!publish(slot)){payload().points.resize(slot.offset);return false;}
        if(!complete.empty())++present_ranks_filled;maximum_frontier=std::max(maximum_frontier,slot.count);
        decision_entries=payload().points.size();decision_rows=measured_rows;
        fill_active=false;reduction_temporary_bytes=0;
        return judge_frontier(payload().points.size());
    }
    template<class Publish,class Interrupt>
    void reduce_merged(unsigned rank,std::vector<rank_merged::Vector>&complete,Publish publish,Interrupt interrupt){
        if(!cells.recording())return;
        Phase phase(reduction_ns);++frontier_fill_attempts;
        merged.reduce(complete,interrupt);
        if(complete.size()>UINT32_MAX)throw std::overflow_error("merged rank slice too large");
        const Slot slot{merged.append(complete),unsigned(complete.size()),0};
        publish(slot);++collective_fills;maximum_frontier=std::max(maximum_frontier,slot.count);
        decision_entries=payload().masks.size();decision_rows=measured_rows;
        dominance_comparisons=merged.dominance_checks;
    }

};
} // namespace rank_summaries
