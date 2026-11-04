#pragma once
#include "diagnostic_counter.h"

#include <cstdint>
#include <algorithm>
#include <array>
#include <memory_resource>
#include <string>
#include <stdexcept>
#include <unordered_map>
#include <vector>

// Counts allocations made by the decision store, not artifact buffers.
class RankStoreMemory : public std::pmr::memory_resource {
public:
    std::size_t live = 0;
    std::size_t peak = 0;
private:
    void *do_allocate(std::size_t bytes, std::size_t alignment) override {
        void *p = std::pmr::new_delete_resource()->allocate(bytes, alignment);
        live += bytes;
        if (live > peak) peak = live;
        return p;
    }
    void do_deallocate(void *p, std::size_t bytes, std::size_t alignment) override {
        live -= bytes;
        std::pmr::new_delete_resource()->deallocate(p, bytes, alignment);
    }
    bool do_is_equal(const std::pmr::memory_resource &other) const noexcept override {
        return this == &other;
    }
};

// The high five id bits encode arity. Operand pairs occupy integer words.
struct RankPredicateInstance {
    static constexpr unsigned max_operands = 16;
    static constexpr unsigned arity_shift = 27;
    std::uint32_t id = 0;
    std::array<std::uint64_t, max_operands / 2> operands{};
    bool operator==(const RankPredicateInstance &other) const noexcept {
        return id == other.id && operands == other.operands;
    }
};

struct RankDecisionKey {
    std::uint64_t rank_and_predicate;
    std::array<std::uint64_t, RankPredicateInstance::max_operands / 2> operands;
    RankDecisionKey(std::uint32_t rank, const RankPredicateInstance &instance)
        : rank_and_predicate(std::uint64_t{instance.id} << 32U | rank),
          operands(instance.operands) {}
    std::uint32_t rank() const noexcept { return rank_and_predicate; }
    std::uint32_t predicate_id() const noexcept { return rank_and_predicate >> 32U; }
    bool operator==(const RankDecisionKey &other) const noexcept {
        return rank_and_predicate == other.rank_and_predicate && operands == other.operands;
    }
};

struct RankDecisionHash {
    static std::uint64_t mix(std::uint64_t x) noexcept {
        x = (x ^ (x >> 30U)) * 0xbf58476d1ce4e5b9ULL;
        x = (x ^ (x >> 27U)) * 0x94d049bb133111ebULL;
        return x ^ (x >> 31U);
    }
    std::size_t operator()(const RankDecisionKey &key) const noexcept {
        std::uint64_t h = mix(key.rank_and_predicate);
        const unsigned words = ((key.predicate_id() >> RankPredicateInstance::arity_shift) + 1U) / 2U;
        for (unsigned i = 0; i < words; ++i) h = mix(h ^ mix(key.operands[i]));
        return h;
    }
};

struct RankPredicateHash {
    std::size_t operator()(const RankPredicateInstance &instance) const noexcept {
        return RankDecisionHash{}(RankDecisionKey(0U, instance));
    }
};

#include "packed_rank_decisions.h"
#include "rank_summary_store.h"
#include "rank_sorted_summary.h"
#include "word_envelope_store.h"

template<class SparseTable>class BasicRankDecisionStore {
    static constexpr std::uint32_t ordinal_mask = (1U << RankPredicateInstance::arity_shift) - 1U;
    static constexpr unsigned probation_window = 1024;
    struct PredicateState {
        struct Word {std::uint64_t good=0,nogood=0;};
        explicit PredicateState(std::pmr::memory_resource *resource) : word_cells(resource),cells(resource),gate_rank_bits(resource) {}
        std::pmr::vector<Word> word_cells;
        bool word=false,word_tablewide=false;
        std::pmr::vector<std::uint64_t> gate_rank_bits;
        std::uint64_t table_present=0,table_distinct=0,table_horizon=0,next_table_check=0;

        std::pmr::vector<std::uint8_t> cells;
        std::uint32_t cardinality = 0;
        std::uint32_t distinct_ranks = 0;
        std::uint32_t predicate_id = 0;
        std::uint64_t threshold = probation_window;
        std::uint64_t total_probes = 0;
        std::uint64_t total_hits = 0;
        std::uint64_t saved_reads = 0;
        std::uint64_t window_probes = 0;
        std::uint64_t window_hits = 0;
        std::uint64_t window_saved_reads=0,last_window_saved_reads=0;
        std::uint64_t word_miss_reads=0,word_miss_samples=0;
        std::uint64_t last_window_probes = 0;
        std::uint64_t last_window_hits = 0;
        bool enabled = true;
        bool immediate = false;
        bool sparse = false;
    };
public:
    RankStoreMemory memory;
    WordEnvelopeStore word_envelopes;
    std::vector<rank_summaries::Summary> summaries;
    SparseTable entries{&memory};
    std::pmr::vector<PredicateState> predicates{&memory};
    std::uint64_t probes = 0;
    std::uint64_t good_hits = 0;
    std::uint64_t no_good_hits = 0;
    std::uint64_t gates_off = 0;
    std::size_t dense_entries = 0;
    std::size_t word_bytes=0,word_budget_bytes=0;
    std::uint64_t word_budget_declines=0;
    std::size_t region_budget_bytes=SIZE_MAX;
    std::uint64_t region_record_refusals=0;

    // Every caller supplies the same filled-rank view; NULL remains a rank
    // sentinel and an unbound operand returns false rather than a short key.
    template<class Read>static bool Key(unsigned id,unsigned count,Read read,RankPredicateInstance &out){
        out={};if(count>RankPredicateInstance::max_operands)return false;out.id=id;
        for(unsigned i=0;i<count;++i){unsigned rank;if(!read(i,rank)){out={};return false;}
            out.operands[i/2]|=std::uint64_t(rank)<<((i&1U)*32U);}
        return true;
    }

    unsigned add_summary(unsigned count,const std::vector<int> &ops={}){
        summaries.emplace_back(count,ops,&memory);return summaries.size()-1;
    }
    using Summary=rank_summaries::Summary;
    using Slot=rank_summaries::Slot;
    // One rank address and completion path for every request-summary layout.
    static const Slot *Probe(Summary&b,unsigned rank,std::uint64_t epoch){
        if(b.last_epoch==epoch&&b.last_rank==rank)return b.last_slot;
        ++b.probes;b.last_epoch=epoch;b.last_rank=rank;
        if(b.decision_mode||b.measured_admission){
            if(b.reached_bits.empty())b.reached_bits.resize((std::uint64_t(b.cells.count())+63)/64);
            auto &word=b.reached_bits[rank/64];auto bit=std::uint64_t{1}<<(rank%64);
            if(!(word&bit)){word|=bit;++b.distinct_reached;}
        }
        b.last_slot=b.view.probe(rank);if(b.last_slot)++b.hits;return b.last_slot;
    }
    static bool Record(Summary&b,unsigned rank,Slot slot){
        if(!b.cells.put(rank,slot))return false;
        b.view=b.cells.witness_read_view();
        b.last_slot=b.last_rank<b.cells.count()?b.view.probe(b.last_rank):nullptr;
        ++b.fills;return true;
    }
    static bool recordable(Summary&b,unsigned rank){
        if(rank>=b.cells.count()||b.view.probe(rank))throw std::logic_error("rank summary filled twice or out of range");
        return !b.frontier_dropped&&b.cells.recording();
    }
    template<class Interrupt=Summary::NoInterrupt>
    static bool Record(Summary&b,unsigned rank,const std::vector<rank_summaries::Point>&points,Interrupt interrupt={}){
        return recordable(b,rank)&&b.reduce_points(rank,points,[&](Slot s){return Record(b,rank,s);},interrupt);
    }
    template<class Interrupt>
    static bool Record(Summary&b,unsigned rank,std::vector<rank_merged::Vector>&points,Interrupt interrupt){
        if(!recordable(b,rank))return false;
        b.reduce_merged(rank,points,[&](Slot s){return Record(b,rank,s);},interrupt);return true;
    }
    template<class Interrupt>
    static bool Record(Summary&b,unsigned rank,std::vector<unsigned>&values,bool nulls,Interrupt interrupt){
        if(!recordable(b,rank))return false;
        auto slot=b.equality_columns.empty()?rank_sorted::prepare(b,rank,values,nulls,interrupt):rank_sorted::prepare_prefix(b,rank,values,interrupt);
        const bool stored=Record(b,rank,slot);b.fill_active=false;b.temporary_bytes=0;interrupt();return stored;
    }
    static bool Record(Summary&b,unsigned rank,const std::vector<rank_requests::MaskedRange>&partition,std::uint64_t nulls){
        if(!recordable(b,rank))return false;
        rank_requests::record_masks(b.decisions,b.payload().answers,rank,b.cells.count(),partition,nulls);
        if(!Record(b,rank,Slot{rank,b.decisions.width,0}))return false;
        ++b.collective_fills;return true;
    }
    static bool Record(Summary&b,unsigned rank,const std::array<rank_theta::Boundary,2>&axes,const std::array<std::uint64_t,9>&truth){
        if(!recordable(b,rank))return false;
        rank_theta::record_theta(b.theta,b.payload().theta,rank,b.cells.count(),axes,truth);
        return Record(b,rank,Slot{rank,b.theta.width,0});
    }
    static std::uint64_t Probe(Summary&b,unsigned rank,unsigned value,std::uint64_t epoch){
        return rank_requests::read_masks(b.decisions,b.payload().answers,rank,value,epoch,nullptr,value==UINT32_MAX,
            [&](rank_requests::Range r){return value>=r.lo&&value<r.hi;},[&](unsigned n){return value!=n;});
    }
    static std::uint64_t Probe(Summary&b,unsigned rank,Summary&eq,unsigned entered,std::uint64_t epoch,const rank_theta::Boundary *transient=nullptr){
        const auto &range=transient?*transient:eq.payload().equalities[entered];
        return rank_requests::read_masks(b.decisions,b.payload().answers,rank,entered,epoch,&eq,range.null_local,
            [&](rank_requests::Range r){++eq.range_comparisons;return range.accepts_interval(r);},
            [&](unsigned n){++eq.range_comparisons;return range.truth(n)==0;});
    }
    static std::uint64_t Probe(Summary&b,unsigned rank,const std::array<unsigned,2>&filled){
        return rank_theta::read_theta(b.theta,b.payload().theta,rank,filled);
    }
    unsigned add_rank_facts(unsigned entered,unsigned count,std::vector<unsigned> columns){
        const auto id=add_summary(count);auto &entry=summaries[id];
        entry.fact_mode=true;entry.column=entered;entry.fact_columns=std::move(columns);return id;
    }
    // A unique-rank fact is another completed slice of this same Cells owner.
    // Only columns demanded by the remaining graph are retained, never row IDs.
    static bool Record(Summary&b,unsigned rank,const std::vector<unsigned>&values,bool present){
        if(!recordable(b,rank))return false;
        if(present&&values.size()!=b.fact_columns.size())throw std::logic_error("one-row fact shape mismatch");
        auto &data=b.payload().fact_ranks;const auto width=b.fact_columns.size();
        if(present&&data.empty())data.resize(std::uint64_t(b.cells.count())*width);
        if(present)std::copy(values.begin(),values.end(),data.begin()+std::uint64_t(rank)*width);
        return Record(b,rank,Slot{std::uint64_t(rank)*width,unsigned(present),0});
    }
    unsigned add_rank_equality(unsigned column,unsigned parameter,unsigned count,unsigned domain){
        auto id=add_summary(count);auto &b=summaries[id];b.equality_mode=true;b.column=column;
        b.parameter_column=parameter;b.parameter_domain=domain;return id;
    }
    static bool Record(Summary&b,unsigned rank,const rank_theta::Boundary&range,bool present){
        if(!recordable(b,rank))return false;
        auto &data=b.payload().equalities;if(data.empty())data.resize(b.cells.count());data[rank]=range;
        return Record(b,rank,Slot{rank,unsigned(present),0});
    }
    unsigned add_proof_region(unsigned count,unsigned arity,bool sparse){
        const auto id=add_summary(count);auto &b=summaries[id];b.proof_mode=true;b.proof_sparse=sparse||arity;
        b.region_predicate=(id+1)|(arity<<RankPredicateInstance::arity_shift);return id;
    }
    unsigned add_window_region(unsigned count,unsigned arity){
        const auto id=add_proof_region(count,arity,true);auto &b=summaries[id];
        b.proof_mode=false;b.region_window_mode=true;return id;
    }
    int Probe(const Summary&b,unsigned rank,const RankPredicateInstance&instance,unsigned value)const{
        const auto found=entries.find_region(RankDecisionKey(rank,instance));if(!found)return -1;
        const auto &data=b.payload();const auto &slot=data.region_windows[*found];
        if(value==UINT32_MAX)return 0;
        for(auto i=slot.offset;i<slot.offset+slot.count;++i){const auto &r=data.region_ranges[i];
            if(value<r.lo)return 0;if(value<r.hi)return 1;}
        return 0;
    }
    bool Record(Summary&b,unsigned rank,const RankPredicateInstance&instance,const composed_windows::Coverage&window){
        const RankDecisionKey key(rank,instance);auto &data=b.payload();const auto found=entries.find_region(key);
        if(found){const auto &slot=data.region_windows[*found];bool equal=slot.count==window.windows.size();
            for(unsigned i=0;equal&&i<slot.count;++i){const auto &r=data.region_ranges[slot.offset+i];
                equal=r.lo==window.windows[i].lo&&r.hi==window.windows[i].hi;}
            if(!equal)throw std::logic_error("residual window decision flipped");return true;}
        if(!b.cells.recording())return false;
        const auto allocation=entries.region_allocation_cost(key)+(data.region_windows.size()+1)*2*sizeof(Slot)+
            (data.region_ranges.size()+window.windows.size())*2*sizeof(rank_requests::Range);
        if(allocation>region_budget_bytes||memory.live>region_budget_bytes-allocation){++region_record_refusals;b.cells.stop_recording();return false;}
        const auto offset=data.region_windows.size();
        data.region_windows.push_back(Slot{data.region_ranges.size(),std::uint32_t(window.windows.size()),0});
        for(auto r:window.windows)data.region_ranges.push_back({r.lo,r.hi});
        entries.record_region(key,offset);++b.fills;return true;
    }
    using Proof=rank_summaries::Proof;
    static constexpr std::size_t proof_page_size=4096;
    const Proof *Probe(const Summary&b,unsigned rank,const RankPredicateInstance&instance)const{
        if(rank>=b.cells.count())return nullptr;
        std::uint64_t offset=rank;
        if(b.proof_sparse){const auto found=entries.find_region(RankDecisionKey(rank,instance));if(!found)return nullptr;offset=*found;}
        const auto &pages=b.payload().proof_pages;const auto page=offset/proof_page_size;
        return page<pages.size()&&!pages[page].empty()?&pages[page][offset%proof_page_size]:nullptr;
    }
    Proof *Record(Summary&b,unsigned rank,const RankPredicateInstance&instance,std::uint64_t *refusals=nullptr){
        if(rank>=b.cells.count())throw std::out_of_range("proof entering rank");
        if(auto previous=Probe(b,rank,instance))return const_cast<Proof*>(previous);
        if(!b.cells.recording())return nullptr;
        auto &pages=b.payload().proof_pages;const auto offset=b.proof_sparse?b.region_count:rank;
        const auto page=offset/proof_page_size;
        const auto allocation=(page>=pages.size()||pages[page].empty()?proof_page_size*sizeof(Proof):0)+
            (b.proof_sparse?entries.region_allocation_cost(RankDecisionKey(rank,instance)):0)+
            (page>=pages.capacity()?(page+1)*2*sizeof(std::pmr::vector<Proof>):0);
        if(allocation>region_budget_bytes||memory.live>region_budget_bytes-allocation){
            ++region_record_refusals;if(refusals)++*refusals;b.cells.stop_recording();return nullptr;}
        if(page>=pages.size())pages.resize(page+1);if(pages[page].empty())pages[page].resize(proof_page_size);
        if(b.proof_sparse)entries.record_region(RankDecisionKey(rank,instance),offset);
        ++b.region_count;++b.fills;return &pages[page][offset%proof_page_size];
    }
    std::size_t summary_size()const{
        std::size_t n=0;for(const auto &b:summaries)n+=b.fills;return n;
    }

    void register_predicate(std::uint32_t id, std::uint32_t cardinality,
                            std::uint32_t distinct_ranks) {
        const auto ordinal = id & ordinal_mask;
        while (predicates.size() <= ordinal) predicates.emplace_back(&memory);
        predicates[ordinal].cardinality = cardinality;
        predicates[ordinal].distinct_ranks = distinct_ranks;
        predicates[ordinal].predicate_id = id;
        predicates[ordinal].threshold = probation_window;
    }

    bool enabled(std::uint32_t id) const noexcept {
        return id!=0 && (id&ordinal_mask)<predicates.size() && predicates[id & ordinal_mask].enabled;
    }
    void open_without_probation(std::uint32_t id) {predicates[id&ordinal_mask].immediate=true;}
    void use_sparse(std::uint32_t id) {predicates[id&ordinal_mask].sparse=true;}
    bool dense_instance(std::uint32_t id)const {
        return (id>>RankPredicateInstance::arity_shift)==0U && !predicates[id&ordinal_mask].sparse;
    }

    std::size_t size() const noexcept { return entries.size() + dense_entries + word_envelopes.entries; }

    void observe(PredicateState &state, bool hit, std::uint64_t saved_reads) {
        if(state.immediate) {
            CF_COUNT(++state.total_probes;state.total_hits+=hit;state.saved_reads+=saved_reads);
            return;
        }
        ++state.total_probes;
        state.total_hits += hit;
        state.saved_reads += saved_reads;
        ++state.window_probes;
        state.window_hits += hit;
        state.window_saved_reads+=saved_reads;
        if(state.word&&state.word_tablewide){
            // Physical order may put a long unique prefix before reuse. The
            // assessment is cumulative over the entered table's rank coverage
            // (or a complete planned arrival horizon), never a1024-row slice.
            const bool covered=state.table_distinct>=state.table_present;
            if((covered||state.total_probes>=state.table_horizon)&&state.total_probes>=state.next_table_check){
                state.last_window_probes=state.total_probes;state.last_window_hits=state.total_hits;
                state.last_window_saved_reads=state.saved_reads;
                if(state.saved_reads<state.total_probes){state.enabled=false;++gates_off;}
                state.next_table_check=state.total_probes+std::max(state.table_horizon,state.table_present);
            }
            return;
        }
        if (state.total_probes >= state.threshold && state.window_probes >= probation_window) {
            state.last_window_probes=state.window_probes;
            state.last_window_hits=state.window_hits;
            state.last_window_saved_reads=state.window_saved_reads;
            const bool unprofitable_word=state.word&&state.window_saved_reads<state.window_probes;
            const bool unprofitable_scalar=!state.word&&state.window_hits==0&&state.saved_reads<(state.total_probes+3U)/4U;
            if (unprofitable_word||unprofitable_scalar) {
                state.enabled = false;
                ++gates_off;
            }
            state.window_probes = state.window_hits = state.window_saved_reads = 0;
        }
    }

    bool peek(std::uint32_t rank, const RankPredicateInstance &instance, bool *truth) const {
        const auto &state=predicates[instance.id & ordinal_mask];
        if(!state.enabled)return false;
        if((instance.id>>RankPredicateInstance::arity_shift)==0U && !state.sparse) {
            const auto cell=rank<state.cardinality && !state.cells.empty() ?
                (state.cells[rank/4U]>>((rank&3U)*2U))&3U : 0U;
            *truth=cell==1U;return cell!=0U;
        }
        const auto found=entries.find(RankDecisionKey(rank,instance));
        if(found==entries.end())return false;
        *truth=found->second;return true;
    }

    bool lookup(std::uint32_t rank, const RankPredicateInstance &instance, bool *truth,
                std::uint64_t nogood_saved_reads = 0, std::uint64_t good_saved_reads = 1) {
        auto &state = predicates[instance.id & ordinal_mask];
        if (!state.enabled) return false;
        CF_COUNT(++probes);
        bool hit = false;
        if ((instance.id >> RankPredicateInstance::arity_shift) == 0U && !state.sparse) {
            const unsigned cell = rank < state.cardinality && !state.cells.empty() ?
                (state.cells[rank / 4U] >> ((rank & 3U) * 2U)) & 3U : 0U;
            hit = cell != 0U;
            *truth = cell == 1U;
        } else {
            const auto found = entries.find(RankDecisionKey(rank, instance));
            hit = found != entries.end();
            if (hit) *truth = found->second;
        }
        observe(state, hit, hit ? (*truth ? good_saved_reads : nogood_saved_reads) : 0U);
        if (!hit) return false;
        if (*truth) CF_COUNT(++good_hits);
        else CF_COUNT(++no_good_hits);
        return true;
    }

    // Range reuse is a gate observation too, not an invisible source of savings.
    void observe_range(std::uint32_t id, bool hit, std::uint64_t saved_reads) {
        auto &state = predicates[id & ordinal_mask];
        if (!state.enabled) return;
        CF_COUNT(++probes);
        const auto avoided=state.word&&state.word_miss_samples?std::max<std::uint64_t>(1,state.word_miss_reads/state.word_miss_samples):saved_reads;
        observe(state,hit,hit?avoided:0);
    }

    template<class Visitor> void visit_gates(Visitor visitor) const {
        for (std::size_t id = 1U; id < predicates.size(); ++id) {
            const auto &state = predicates[id];
            visitor(state.predicate_id, state.distinct_ranks, state.threshold,
                    state.total_probes, state.total_hits, state.saved_reads,
                    !state.enabled ? "off" : state.total_probes == 0 ? "unused" :
                    state.total_probes < state.threshold ? "probation" : "on");
        }
    }

    // Returns false on a conflicting verdict; the caller reports ERROR.
    bool insert(std::uint32_t rank, const RankPredicateInstance &instance, bool truth) {
        auto &state = predicates[instance.id & ordinal_mask];
        if (!state.enabled) return true;
        if ((instance.id >> RankPredicateInstance::arity_shift) == 0U && !state.sparse) {
            if (rank >= state.cardinality) return false;
            if (state.cells.empty()) state.cells.resize((std::size_t{state.cardinality} + 3U) / 4U, 0U);
            const unsigned shift = (rank & 3U) * 2U;
            const unsigned old = (state.cells[rank / 4U] >> shift) & 3U;
            const unsigned value = truth ? 1U : 2U;
            if (old) return old == value;
            state.cells[rank / 4U] |= value << shift;
            ++dense_entries;
            return true;
        }
        const auto inserted = entries.emplace(RankDecisionKey(rank, instance), truth);
        return inserted.second || inserted.first->second == truth;
    }

    using Word=PackedRankDecisions::Word;
    void register_word(std::uint32_t id,std::uint32_t cardinality,bool sparse) {
        register_predicate(id,cardinality,cardinality);auto &s=predicates[id&ordinal_mask];s.word=true;s.sparse=sparse;
    }
    void configure_word_tablewide(std::uint32_t id,std::uint64_t present,std::uint64_t arrivals){
        auto &s=predicates[id&ordinal_mask];s.word_tablewide=true;
        s.table_present=std::max<std::uint64_t>(1,present);s.table_horizon=std::max<std::uint64_t>(1,arrivals);
        s.threshold=s.table_horizon; // diagnostic: no fixed prefix horizon
    }
    bool word_dense(std::uint32_t id)const {
        const auto &s=predicates[id&ordinal_mask];return !(id>>RankPredicateInstance::arity_shift) && !s.sparse;
    }
    void record_word_miss(std::uint32_t id,std::uint64_t reads){
        if(!id)return;auto &state=predicates[id&ordinal_mask];
        state.word_miss_reads+=reads;++state.word_miss_samples;
    }
    Word lookup_word(std::uint32_t rank,const RankPredicateInstance &instance,std::uint64_t live,std::uint64_t fallback_reads=1) {
        auto &s=predicates[instance.id&ordinal_mask];if(!s.enabled)return {};
        if(s.word_tablewide&&rank<s.cardinality){
            if(s.gate_rank_bits.empty()){
                const auto bytes=((std::uint64_t(s.cardinality)+63)/64)*8;
                if(bytes<=word_budget_bytes&&word_bytes<=word_budget_bytes-bytes){
                    const auto before=memory.live;s.gate_rank_bits.resize((std::uint64_t(s.cardinality)+63)/64);word_bytes+=memory.live-before;
                }
            }
            if(!s.gate_rank_bits.empty()){auto &word=s.gate_rank_bits[rank/64];const auto bit=1ULL<<(rank%64);
                if(!(word&bit)){word|=bit;++s.table_distinct;}}
        }
        Word result;
        if(word_dense(instance.id)){
            if(rank<s.cardinality && !s.word_cells.empty())result={s.word_cells[rank].good,s.word_cells[rank].nogood};
        }else result=entries.find_word(RankDecisionKey(rank,instance));
        result.good&=live;result.nogood&=live;
        const bool hit=(result.good|result.nogood)!=0;
        CF_COUNT(++probes;good_hits+=result.good!=0;no_good_hits+=result.nogood!=0);
        const auto saved=s.word_miss_samples?std::max<std::uint64_t>(1,s.word_miss_reads/s.word_miss_samples):fallback_reads;
        observe(s,hit,hit?saved:0);return result;
    }
    bool insert_word(std::uint32_t rank,const RankPredicateInstance &instance,
                     std::uint64_t good,std::uint64_t nogood,bool &written) {
        written=false;auto &s=predicates[instance.id&ordinal_mask];
        if(!s.enabled || !(good|nogood))return true;
        if(good&nogood)return false;
        const auto cost=word_dense(instance.id)?(s.word_cells.empty()?std::uint64_t(s.cardinality)*sizeof(typename PredicateState::Word):0):
            entries.word_allocation_cost(RankDecisionKey(rank,instance));
        if(cost>word_budget_bytes || word_bytes+word_envelopes.bytes>word_budget_bytes-cost){++word_budget_declines;return true;}
        const auto before=memory.live;
        if(word_dense(instance.id)){
            if(rank>=s.cardinality)return false;
            if(s.word_cells.empty())s.word_cells.resize(s.cardinality);
            auto &cell=s.word_cells[rank];
            if((cell.good&nogood) || (cell.nogood&good))return false;
            if(!(cell.good|cell.nogood))++dense_entries;
            cell.good|=good;cell.nogood|=nogood;
        }else if(!entries.insert_word(RankDecisionKey(rank,instance),good,nogood))return false;
        word_bytes+=memory.live-before;written=true;return true;
    }

    bool known_false(std::uint32_t rank, const RankPredicateInstance &instance) {
        const auto &state = predicates[instance.id & ordinal_mask];
        if ((instance.id >> RankPredicateInstance::arity_shift) == 0U)
            return rank < state.cardinality && !state.cells.empty() &&
                ((state.cells[rank / 4U] >> ((rank & 3U) * 2U)) & 3U) == 2U;
        const RankDecisionKey key(rank, instance);
        const auto found = entries.find(key);
        return found != entries.end() && !found->second;
    }

    template<class Visitor> void visit_entries(Visitor visitor) const {
        for (const auto &item : entries) visitor(item.first, item.second);
        for (std::uint32_t id = 1U; id < predicates.size(); ++id) {
            const auto &state = predicates[id];
            if (state.cells.empty()) continue;
            RankPredicateInstance instance;
            instance.id = id;
            for (std::uint32_t rank = 0; rank < state.cardinality; ++rank) {
                const unsigned value = (state.cells[rank / 4U] >> ((rank & 3U) * 2U)) & 3U;
                if (value) visitor(RankDecisionKey(rank, instance), value == 1U);
            }
        }
    }
};

// Existing non-nested strategies retain their store implementation. The
// nested path selects packed open addressing at compile time, without a
// per-probe dispatch or a node-allocated fallback.
using RankDecisionStore=BasicRankDecisionStore<PackedRankDecisions>;
using PackedRankDecisionStore=RankDecisionStore;
