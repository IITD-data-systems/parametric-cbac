#pragma once
#include <cstdint>
#include <vector>
#include <unordered_map>
#include <memory>
#include <memory_resource>
#include <new>
#include "rank_decision_store.h"

// The storage strategy is selected once while compiling the plan.
template<class T> class ReachedCells {
    std::shared_ptr<RankStoreMemory> allocation_=std::make_shared<RankStoreMemory>();
    std::vector<T> dense_;
    std::pmr::unordered_map<std::size_t,T> sparse_{allocation_.get()};
    std::size_t size_=0;
    T initial_{};
    using Get=T&(*)(ReachedCells *,std::size_t);
    static T &dense_get(ReachedCells *p,std::size_t key){return p->dense_[key];}
    static T &sparse_get(ReachedCells *p,std::size_t key){return p->sparse_.try_emplace(key,p->initial_).first->second;}
    Get get_=dense_get;
public:
    using value_type=T;
    ReachedCells()=default;
    ReachedCells(const ReachedCells &other):dense_(other.dense_),size_(other.size_),initial_(other.initial_),get_(other.get_) {
        for(const auto &entry:other.sparse_)sparse_.emplace(entry);
    }
    ReachedCells(ReachedCells &&other) noexcept:allocation_(other.allocation_),dense_(std::move(other.dense_)),
        sparse_(std::move(other.sparse_)),size_(other.size_),initial_(other.initial_),get_(other.get_) {}
    ReachedCells &operator=(const ReachedCells &other) {
        if(this!=&other){this->~ReachedCells();new(this)ReachedCells(other);}return *this;
    }
    ReachedCells &operator=(ReachedCells &&other) noexcept {
        if(this!=&other){this->~ReachedCells();new(this)ReachedCells(std::move(other));}return *this;
    }
    void select_sparse(){get_=sparse_get;}
    bool sparse() const{return get_==sparse_get;}
    bool empty() const{return size_==0;}
    std::size_t size() const{return size_;}
    std::size_t capacity() const{return dense_.capacity();}
    std::size_t sparse_peak_bytes() const{return allocation_->peak;}
    void assign(std::size_t n,T initial){size_=n;initial_=initial;if(!sparse())dense_.assign(n,initial);}
    void resize(std::size_t n){assign(n,T{});}
    T &operator[](std::size_t key){return get_(this,key);}
    template<bool Sparse> T &at(std::size_t key) {
        if constexpr(Sparse)return sparse_get(this,key);
        else return dense_[key];
    }
    template<bool Sparse> const T *peek(std::size_t key) const {
        if constexpr(Sparse) {
            const auto found=sparse_.find(key);
            return found==sparse_.end() ? nullptr : &found->second;
        } else return key<dense_.size() ? dense_.data()+key : nullptr;
    }
};
