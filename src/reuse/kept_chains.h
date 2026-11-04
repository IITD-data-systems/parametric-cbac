#pragma once
#include <algorithm>
#include <cstdint>
#include <limits>
#include <stdexcept>
#include <vector>
#if defined(__AVX2__)
#include <immintrin.h>
#endif

namespace full_reuse {
constexpr std::uint32_t unset = UINT32_MAX - 1U;
constexpr std::uint32_t null_rank = UINT32_MAX;

// Columnar kept records: endpoint ranks use their universe width and predicate
// states use two bits (0=unset, 1=good, 2=nogood). No physical endpoint row IDs
// are retained. Allocation is on first arrival, not at plan construction.
class KeptRanks {
    struct Field {
        std::uint32_t domain=0;
        unsigned width=0;
        std::vector<std::uint8_t> u8;
        std::vector<std::uint16_t> u16;
        std::vector<std::uint32_t> u32;
        void allocate(std::size_t n) {
            if(!width)u8.assign((n+3U)/4U,0);
            else if(width==1)u8.assign(n,static_cast<std::uint8_t>(domain+1U));
            else if(width==2)u16.assign(n,static_cast<std::uint16_t>(domain+1U));
            else u32.assign(n,unset);
        }
        std::uint32_t get(std::size_t key) const {
            if(!width) {
                const auto state=(u8[key/4U]>>((key&3U)*2U))&3U;
                return state ? state : unset;
            }
            const auto value=width==1 ? std::uint32_t(u8[key]) : width==2 ? std::uint32_t(u16[key]) : u32[key];
            return width==4 ? value : value==domain+1U ? unset : value==domain ? null_rank : value;
        }
        void put(std::size_t key,std::uint32_t value) {
            if(!width) {
                if(value!=unset && value!=1U && value!=2U)throw std::runtime_error("invalid kept state");
                const auto shift=(key&3U)*2U;
                u8[key/4U]=(u8[key/4U]&~(3U<<shift))|((value==unset ? 0U : value)<<shift);
            } else if(width==4)u32[key]=value;
            else {
                if(value!=unset && value!=null_rank && value>=domain)throw std::runtime_error("kept endpoint outside universe");
                const auto encoded=value==unset ? domain+1U : value==null_rank ? domain : value;
                if(width==1)u8[key]=static_cast<std::uint8_t>(encoded);
                else u16[key]=static_cast<std::uint16_t>(encoded);
            }
        }
    };
    std::uint32_t ranks_ = 0;
    std::vector<Field> fields_;
    bool allocated_=false;
    std::size_t key(std::uint32_t rank) const {
        const auto result=rank==null_rank ? ranks_ : rank;
        if(result>ranks_)throw std::runtime_error("kept-chain rank outside universe");
        return result;
    }
public:
    struct Value {
        KeptRanks *owner;std::size_t key,field;
        operator std::uint32_t() const { return owner->fields_[field].get(key); }
        Value &operator=(std::uint32_t value){owner->fields_[field].put(key,value);return *this;}
    };
    struct Cell {
        KeptRanks *owner=nullptr;std::size_t key=0;
        Value operator[](std::size_t field){return {owner,key,field};}
    };
    void plan(std::uint32_t ranks,const std::vector<std::uint32_t> &domains) {
        if (ranks >= unset || domains.empty() || allocated_) throw std::runtime_error("invalid kept-chain shape");
        ranks_=ranks;fields_.resize(domains.size());
        for(std::size_t i=0;i<domains.size();++i) {
            auto &field=fields_[i];field.domain=domains[i];
            field.width=!domains[i] ? 0U : domains[i]<=254U ? 1U : domains[i]<=65534U ? 2U : 4U;
        }
    }
    Cell arrive(std::uint32_t rank) {
        const auto index=key(rank);
        if(!allocated_){for(auto &field:fields_)field.allocate(std::size_t(ranks_)+1U);allocated_=true;}
        return {this,index};
    }
    std::uint32_t peek(std::uint32_t rank,std::size_t field) const {return allocated_ ? fields_[field].get(key(rank)) : unset;}
    const std::uint8_t *states(std::size_t field) const {return allocated_ && !fields_[field].width ? fields_[field].u8.data() : nullptr;}
    unsigned width(std::size_t field) const {return fields_[field].width;}
    std::uint32_t domain(std::size_t field) const {return fields_[field].domain;}
    template<unsigned Width> const void *ranks(std::size_t field) const {
        if(fields_[field].width!=Width)throw std::runtime_error("kept rank width differs from compiled loop");
        if constexpr(Width==1)return fields_[field].u8.data();
        else if constexpr(Width==2)return fields_[field].u16.data();
        else return fields_[field].u32.data();
    }
    std::size_t planned_bytes() const {
        std::size_t size=0;const auto n=std::size_t(ranks_)+1U;
        for(const auto &field:fields_)size+=field.width ? n*field.width : (n+3U)/4U;
        return size;
    }
    std::size_t bytes() const {
        std::size_t size=0;for(const auto &field:fields_)size+=field.u8.capacity()+2U*field.u16.capacity()+4U*field.u32.capacity();return size;
    }
    bool empty() const { return !allocated_; }
};

// Compare adjacent entering ranks column-at-a-time. Failed probation removes
// the wrapper itself, so unique-arrival branches pay nothing after 4K rows.
struct RunBlock {
    std::vector<std::uint8_t> same;
    std::vector<std::uint32_t> ends;
    std::uint64_t sampled=0,repeats=0;
    bool disabled=false;
    std::vector<std::uint64_t> selected,answers;
    struct Span {std::uint32_t begin,end,representative;};
    std::vector<Span> spans;
    std::vector<std::uint64_t> equal_masks;
    std::uint32_t next_base=UINT32_MAX;
    bool seen_carry=false,good_carry=false;
    static std::uint64_t equal_word(const std::vector<const std::uint32_t*> &columns,
                                    std::uint32_t base,std::uint32_t size,bool linked) {
        std::uint64_t same=size==64U ? UINT64_MAX : (std::uint64_t{1}<<size)-1U;
        for(const auto *column:columns) {
            std::uint64_t mask=0;std::uint32_t i=0;
            if(!base){i=1;}
#if defined(__AVX2__)
            for(;i+8U<=size;i+=8U) {
                const auto a=_mm256_loadu_si256(reinterpret_cast<const __m256i*>(column+base+i));
                const auto b=_mm256_loadu_si256(reinterpret_cast<const __m256i*>(column+base+i-1U));
                mask|=std::uint64_t(static_cast<unsigned>(_mm256_movemask_ps(_mm256_castsi256_ps(_mm256_cmpeq_epi32(a,b)))))<<i;
            }
#endif
            for(;i<size;++i)if(column[base+i]==column[base+i-1U])mask|=std::uint64_t{1}<<i;
            same&=mask;
        }
        return linked ? same : same&~std::uint64_t{1};
    }
    static std::uint64_t spread(std::uint64_t seed,std::uint64_t same,bool carry) {
        seed|=std::uint64_t(carry)&same;
        for(unsigned shift=1;shift<64U;shift*=2U) {
            seed|=(seed<<shift)&same;
            same&=same<<shift;
        }
        return seed;
    }
    static std::uint64_t heads(std::uint64_t live,std::uint64_t same,bool carry,bool *next_seen) {
        const auto seen=spread(live,same,carry);
        *next_seen=(seen>>63U)!=0;
        return live&~(((seen<<1U)|std::uint64_t(carry))&same);
    }
    void observe(std::uint32_t size,std::uint32_t saved) {
        sampled+=size;repeats+=saved;
        if(sampled>=4096U && repeats*8U<sampled)disabled=true;
    }
    std::uint32_t detect(const std::vector<const std::uint32_t*> &columns,std::uint32_t base,std::uint32_t size) {
        if(!size || disabled || columns.empty())return 0;
        same.assign(size,1U);same[0]=0;
        for(const auto *column:columns) {
            const auto *values=column+base;
            for(std::uint32_t i=1;i<size;++i)same[i]&=values[i]==values[i-1U];
        }
        std::uint32_t repeated=0;for(auto value:same)repeated+=value;
        sampled+=size;repeats+=repeated;
        // At least 1/8 of rows must be saved to pay for detection and expansion.
        if(sampled>=4096U && repeats*8U<sampled)disabled=true;
        if(!repeated)return 0;
        ends.resize(size);
        auto end=size;
        for(auto i=size;i--;){if(i+1U==size || !same[i+1U])end=i+1U;ends[i]=end;}
        return repeated;
    }
    static std::uint64_t range_word(std::uint32_t begin,std::uint32_t end,std::uint32_t word) {
        const auto lo=std::max(begin,word*64U),hi=std::min(end,word*64U+64U);
        if(hi<=lo)return 0;
        return (UINT64_MAX<<(lo&63U))&(UINT64_MAX>>(63U-((hi-1U)&63U)));
    }
    std::uint32_t select(const std::uint64_t *live,std::uint32_t size) {
        const auto words=(size+63U)/64U;
        selected.assign(words,0U);answers.assign(words,0U);spans.clear();
        std::uint32_t saved=0;
        for(std::uint32_t begin=0;begin<size;) {
            const auto end=ends[begin];std::uint32_t representative=size,count=0;
            for(auto word=begin/64U;word<=(end-1U)/64U;++word) {
                const auto bits=live[word]&range_word(begin,end,word);
                if(bits && representative==size)representative=word*64U+__builtin_ctzll(bits);
                count+=__builtin_popcountll(bits);
            }
            if(count) {
                selected[representative/64U]|=std::uint64_t{1}<<(representative&63U);
                spans.push_back({begin,end,representative});saved+=count-1U;
            }
            begin=end;
        }
        return saved;
    }
    void expand(const std::uint64_t *live,std::uint64_t *good,std::uint32_t size) const {
        std::fill(good,good+(size+63U)/64U,0U);
        for(const auto &span:spans)if(answers[span.representative/64U]&(std::uint64_t{1}<<(span.representative&63U)))
            for(auto word=span.begin/64U;word<=(span.end-1U)/64U;++word)
                good[word]|=live[word]&range_word(span.begin,span.end,word);
    }
};

// OR exactly [begin,end), including unaligned edges and a short final word.
inline void allow_range(std::vector<std::uint64_t> &bits, std::uint32_t begin, std::uint32_t end) {
    if (end <= begin) return;
    const auto first = begin / 64U, last = (end - 1U) / 64U;
    const auto left = UINT64_MAX << (begin & 63U);
    const auto right = UINT64_MAX >> (63U - ((end - 1U) & 63U));
    if (first == last) { bits[first] |= left & right; return; }
    bits[first] |= left;
    std::fill(bits.begin() + first + 1U, bits.begin() + last, UINT64_MAX);
    bits[last] |= right;
}

// No policy-dependent artifact or index: compare the bound target's complete
// input tuple in physical row order. NULL is an instance value here, not SQL =.
inline std::uint32_t run_end(const std::vector<const std::uint32_t *> &columns,
                             std::uint32_t begin, std::uint32_t rows) {
    auto end = begin + 1U;
    while (end < rows) {
        bool equal = true;
        for (auto column : columns) if (column[end] != column[begin]) { equal = false; break; }
        if (!equal) break;
        ++end;
    }
    return end;
}
}
