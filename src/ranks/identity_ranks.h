#pragma once
#include <cstdint>
#include <iterator>

// A zero-allocation view of 0..m. Ranks need no identity remap array.
struct IdentityRanks {
    struct Iterator {
        using iterator_category=std::random_access_iterator_tag;
        using value_type=std::uint32_t;using difference_type=std::int64_t;
        using pointer=void;using reference=std::uint32_t;
        difference_type pos=0;
        value_type operator*() const{return pos;}
        value_type operator[](difference_type n)const{return pos+n;}
        Iterator &operator++(){++pos;return *this;}Iterator operator++(int){auto old=*this;++pos;return old;}
        Iterator &operator--(){--pos;return *this;}Iterator operator--(int){auto old=*this;--pos;return old;}
        Iterator &operator+=(difference_type n){pos+=n;return *this;}
        Iterator &operator-=(difference_type n){pos-=n;return *this;}
        friend Iterator operator+(Iterator a,difference_type n){a+=n;return a;}
        friend Iterator operator+(difference_type n,Iterator a){a+=n;return a;}
        friend Iterator operator-(Iterator a,difference_type n){a-=n;return a;}
        friend difference_type operator-(Iterator a,Iterator b){return a.pos-b.pos;}
        friend bool operator==(Iterator a,Iterator b){return a.pos==b.pos;}
        friend bool operator!=(Iterator a,Iterator b){return !(a==b);}
        friend bool operator<(Iterator a,Iterator b){return a.pos<b.pos;}
        friend bool operator>(Iterator a,Iterator b){return b<a;}
        friend bool operator<=(Iterator a,Iterator b){return !(b<a);}
        friend bool operator>=(Iterator a,Iterator b){return !(a<b);}
    };
    std::uint32_t count=0;
    IdentityRanks()=default;explicit IdentityRanks(std::uint32_t n):count(n){}
    std::uint32_t size()const{return count;}
    std::uint32_t operator[](std::uint32_t rank)const{return rank;}
    Iterator begin()const{return {0};}Iterator end()const{return {count};}
    const std::uint32_t *data()const{return nullptr;}
};
