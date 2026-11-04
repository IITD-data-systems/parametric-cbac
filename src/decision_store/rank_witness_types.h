#pragma once
#include <array>
#include <cstdint>
#include <memory_resource>
#include <stdexcept>
#include <vector>
#include "rank_request_decisions.h"
#include "rank_theta_decisions.h"

// Physical complete-witness form of the common rank summary. Every point is
// one complete witness. No row identifier or independently mixed coordinates.
namespace rank_summaries {
constexpr unsigned null_rank=UINT32_MAX;
constexpr unsigned max_tests=6;
constexpr unsigned max_states=729;
constexpr unsigned state_words=(max_states+63)/64;
struct Bits {
    std::array<std::uint64_t,state_words> words{};
    bool get(unsigned i)const{if(i>=max_states)throw std::out_of_range("summary state");return (words[i/64]>>(i%64))&1;}
    void set(unsigned i){if(i>=max_states)throw std::out_of_range("summary state");words[i/64]|=std::uint64_t{1}<<(i%64);}
    bool empty()const{for(auto word:words)if(word)return false;return true;}
};
inline Bits operator&(const Bits&a,const Bits&b){Bits out;for(unsigned i=0;i<state_words;++i)out.words[i]=a.words[i]&b.words[i];return out;}
inline Bits operator|(const Bits&a,const Bits&b){Bits out;for(unsigned i=0;i<state_words;++i)out.words[i]=a.words[i]|b.words[i];return out;}
inline Bits operator~(const Bits&a){Bits out;for(unsigned i=0;i<state_words;++i)out.words[i]=~a.words[i];return out;}
inline bool includes(const Bits&a,const Bits&b){for(unsigned i=0;i<state_words;++i)if(b.words[i]&~a.words[i])return false;return true;}
struct Point {std::array<std::uint32_t,max_tests> ranks{};Bits good;};
struct Slot {std::uint64_t offset=UINT64_MAX;std::uint32_t count=0,ungrouped=0;};
struct Proof {std::uint64_t decided=0,truth=0;};
// Buffers belong to Cells, not to a separate summary bank. The arrays are
// empty until the first arrival; a fixed truth-table point form and a compact
// rank-vector/request-mask form are structural layouts of the same payload.
struct WitnessPayload {
    rank_requests::MaskPayload answers;
    rank_theta::Payload theta;
    std::pmr::vector<Slot> slots;
    std::pmr::vector<Point> points;
    std::pmr::vector<std::uint32_t> ranks;
    std::pmr::vector<std::uint64_t> masks;
    std::pmr::vector<std::uint32_t> fact_ranks;
    std::pmr::vector<rank_theta::Boundary> equalities;
    std::pmr::vector<std::pmr::vector<Proof>> proof_pages;
    std::pmr::vector<Slot> region_windows;
    std::pmr::vector<rank_requests::Range> region_ranges;
    struct Prefix {std::uint32_t offset=0,count=0;};
    std::pmr::vector<std::uint32_t> null_prefixes;
    std::pmr::vector<Prefix> null_slots;
    explicit WitnessPayload(std::pmr::memory_resource *memory):answers(memory),theta(memory),slots(memory),points(memory),ranks(memory),masks(memory),fact_ranks(memory),equalities(memory),proof_pages(memory),region_windows(memory),region_ranges(memory),null_prefixes(memory),null_slots(memory){}
    std::size_t proof_bytes()const{std::size_t n=proof_pages.capacity()*sizeof(decltype(proof_pages)::value_type);for(const auto&p:proof_pages)n+=p.capacity()*sizeof(Proof);return n;}
    std::size_t bytes()const{return slots.size()*sizeof(Slot)+points.size()*sizeof(Point)+ranks.size()*4U+masks.size()*8U+
        null_prefixes.size()*4U+null_slots.size()*sizeof(Prefix)+answers.bytes()+theta.bytes()+fact_ranks.size()*4U+equalities.size()*sizeof(rank_theta::Boundary)+proof_bytes()+region_windows.size()*sizeof(Slot)+region_ranges.size()*sizeof(rank_requests::Range);}
    void clear(){
        answers=rank_requests::MaskPayload(slots.get_allocator().resource());
        theta=rank_theta::Payload(slots.get_allocator().resource());
        std::pmr::vector<Slot>(slots.get_allocator().resource()).swap(slots);
        std::pmr::vector<Point>(points.get_allocator().resource()).swap(points);
        std::pmr::vector<std::uint32_t>(ranks.get_allocator().resource()).swap(ranks);
        std::pmr::vector<std::uint64_t>(masks.get_allocator().resource()).swap(masks);
        std::pmr::vector<std::uint32_t>(fact_ranks.get_allocator().resource()).swap(fact_ranks);
        std::pmr::vector<rank_theta::Boundary>(equalities.get_allocator().resource()).swap(equalities);
        std::pmr::vector<std::pmr::vector<Proof>>(proof_pages.get_allocator().resource()).swap(proof_pages);
        std::pmr::vector<Slot>(region_windows.get_allocator().resource()).swap(region_windows);
        std::pmr::vector<rank_requests::Range>(region_ranges.get_allocator().resource()).swap(region_ranges);
        std::pmr::vector<std::uint32_t>(null_prefixes.get_allocator().resource()).swap(null_prefixes);
        std::pmr::vector<Prefix>(null_slots.get_allocator().resource()).swap(null_slots);
    }
};
} // namespace rank_summaries
