#pragma once
#include "universe_format.h"
#include <array>
#include <limits>

// Operator-blind, lexicographically sorted tuples of universe ranks.
namespace tuple_index {
using universe_format::read32;
using universe_format::require;
struct Rows {
    const unsigned char *data=nullptr;
    std::uint32_t count=0;
    std::size_t size() const {return count;}
    std::uint32_t operator[](std::size_t i) const {
        require(i<count,"tuple posting out of bounds");return read32(data+4ULL*i);
    }
};
struct View {
    std::uint32_t arity=0,keys=0,rows=0;
    const unsigned char *tuples=nullptr,*offsets=nullptr,*postings=nullptr;
    static View decode(const unsigned char *data,std::size_t size) {
        require(size>=24 && std::memcmp(data,"CXI1",4)==0,"invalid tuple index");
        View out;out.arity=read32(data+4);out.keys=read32(data+8);out.rows=read32(data+12);
        require(out.arity>=2 && out.arity<=16 && read32(data+16)==0,"unsupported tuple index");
        const std::uint64_t key_bytes=4ULL*out.arity*out.keys;
        const std::uint64_t offset_bytes=4ULL*(std::uint64_t(out.keys)+1);
        require(20ULL+key_bytes+offset_bytes+4ULL*out.rows==size,"tuple index size mismatch");
        out.tuples=data+20;out.offsets=out.tuples+key_bytes;out.postings=out.offsets+offset_bytes;
        require(read32(out.offsets)==0 && read32(out.offsets+4ULL*out.keys)==out.rows,"tuple posting endpoints mismatch");
        return out;
    }
    Rows lookup(const std::array<std::uint32_t,16> &key) const {
        for (std::uint32_t i=0;i<arity;++i) if (key[i]==UINT32_MAX) return {};
        const auto compare=[&](std::uint32_t row) {
            for (std::uint32_t i=0;i<arity;++i) {
                const auto value=read32(tuples+4ULL*(std::uint64_t(row)*arity+i));
                if (value!=key[i]) return value<key[i] ? -1 : 1;
            }
            return 0;
        };
        std::uint32_t lo=0,hi=keys;
        while (lo<hi) {const auto mid=lo+(hi-lo)/2;if (compare(mid)<0) lo=mid+1;else hi=mid;}
        if (lo==keys || compare(lo)!=0) return {};
        const auto begin=read32(offsets+4ULL*lo),end=read32(offsets+4ULL*(lo+1));
        require(begin<=end && end<=rows,"tuple posting bounds invalid");
        return {postings+4ULL*begin,end-begin};
    }
};
}
