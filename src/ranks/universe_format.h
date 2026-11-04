#pragma once
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <stdexcept>
#include <string_view>

namespace universe_format {
inline std::uint32_t read32(const unsigned char *p) {
    return std::uint32_t(p[0]) | std::uint32_t(p[1])<<8 |
           std::uint32_t(p[2])<<16 | std::uint32_t(p[3])<<24;
}
inline void require(bool condition, const char *message) {
    if (!condition) throw std::runtime_error(message);
}
struct Dictionary {
    std::uint32_t count=0, numeric_kind=0;
    const unsigned char *offsets=nullptr, *payload=nullptr;
    std::string_view value(std::uint32_t rank) const {
        require(rank<count,"universe dictionary rank out of bounds");
        const auto lo=read32(offsets+4ULL*rank), hi=read32(offsets+4ULL*(rank+1));
        require(lo<=hi,"universe dictionary offsets reversed");
        return {reinterpret_cast<const char *>(payload+lo),hi-lo};
    }
    static Dictionary decode(const unsigned char *data,std::size_t size) {
        require(size>=20 && std::memcmp(data,"UDX1",4)==0,"invalid UDX1 dictionary");
        Dictionary out;out.count=read32(data+4);out.numeric_kind=read32(data+8);
        require(out.numeric_kind<=2 && read32(data+12)==0,"unsupported UDX1 type/flags");
        const auto header=16ULL+4ULL*(out.count+1ULL);
        require(header<=size,"truncated UDX1 offsets");
        out.offsets=data+16;out.payload=data+header;
        require(read32(out.offsets)==0 && read32(out.offsets+4ULL*out.count)==size-header,
                "UDX1 terminal offset mismatch");
        return out;
    }
};
struct Inverted {
    std::uint32_t ranks=0, rows=0, present_count=0;
    bool unique=false;
    const unsigned char *offsets=nullptr,*children=nullptr,*present=nullptr;
    static Inverted decode(const unsigned char *data,std::size_t size) {
        require(size>=24 && std::memcmp(data,"CIX2",4)==0,"expected universe-ranked CIX2");
        Inverted out;out.ranks=read32(data+4);out.rows=read32(data+8);out.present_count=read32(data+12);
        const auto flags=read32(data+16);require(flags<=1,"unsupported CIX2 flags");out.unique=flags;
        require(out.present_count<=out.ranks,"CIX2 present count exceeds universe");
        const auto header=20ULL+4ULL*(out.ranks+1ULL);
        require(header+4ULL*out.rows+4ULL*out.present_count==size,"CIX2 length mismatch");
        out.offsets=data+20;out.children=data+header;out.present=out.children+4ULL*out.rows;
        require(read32(out.offsets)==0 && read32(out.offsets+4ULL*out.ranks)==out.rows,
                "CIX2 terminal offset mismatch");
        return out;
    }
};
}
