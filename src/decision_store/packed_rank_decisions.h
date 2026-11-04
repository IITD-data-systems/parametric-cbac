#pragma once
#include <algorithm>
#include <cstdint>
#include <memory_resource>
#include <optional>
#include <utility>
#include <vector>

// Open addressing over integer words. The first word is predicate-id/rank;
// the remaining words pack two filled-value ranks each. Banks are separated
// by key width, NOT by data values. No composite entering index is built.
// Include after RankDecisionKey and RankDecisionHash have been declared.
class PackedRankDecisions {
    struct Bank {
        unsigned words;
        std::size_t used=0;
        std::pmr::vector<std::uint64_t> keys;
        std::pmr::vector<std::uint8_t> cells; // 0 unset; bool verdict or word occupancy
        bool word_mode=false;
        std::pmr::vector<std::uint64_t> good,nogood;
        Bank(unsigned width,std::pmr::memory_resource *r,bool word=false):words(width),keys(r),cells(r),word_mode(word),good(r),nogood(r){}
        std::size_t hash(const std::uint64_t *p)const {
            auto h=RankDecisionHash::mix(p[0]);
            for(unsigned w=1;w<words;++w)h=RankDecisionHash::mix(h^RankDecisionHash::mix(p[w]));
            return h;
        }
        std::size_t locate(const RankDecisionKey &key)const {
            auto slot=RankDecisionHash{}(key)&(cells.size()-1);
            while(cells[slot]) {
                const auto *p=keys.data()+slot*words;
                if(p[0]==key.rank_and_predicate && std::equal(key.operands.begin(),key.operands.begin()+words-1,p+1))break;
                slot=(slot+1)&(cells.size()-1);
            }
            return slot;
        }
        void grow(std::size_t capacity) {
            auto old_keys=std::move(keys);auto old_cells=std::move(cells);
            auto old_good=std::move(good),old_nogood=std::move(nogood);
            keys=std::pmr::vector<std::uint64_t>(old_keys.get_allocator().resource());
            cells=std::pmr::vector<std::uint8_t>(old_cells.get_allocator().resource());
            keys.resize(capacity*words);cells.resize(capacity,0);
            good=std::pmr::vector<std::uint64_t>(old_good.get_allocator().resource());
            nogood=std::pmr::vector<std::uint64_t>(old_nogood.get_allocator().resource());
            if(word_mode){good.resize(capacity,0);nogood.resize(capacity,0);}
            for(std::size_t i=0;i<old_cells.size();++i)if(old_cells[i]){
                const auto *p=old_keys.data()+i*words;auto slot=hash(p)&(capacity-1);
                while(cells[slot])slot=(slot+1)&(capacity-1);
                std::copy_n(p,words,keys.data()+slot*words);cells[slot]=old_cells[i];
                if(word_mode){good[slot]=old_good[i];nogood[slot]=old_nogood[i];}
            }
        }
    };
    std::pmr::memory_resource *resource_;
    std::pmr::vector<Bank> banks_,word_banks_,region_banks_;
    std::size_t size_=0;
    static unsigned arity(const RankDecisionKey &key){return key.predicate_id()>>RankPredicateInstance::arity_shift;}
public:
    struct Item {RankDecisionKey first;bool second;};
    class const_iterator {
        friend class PackedRankDecisions;
        const PackedRankDecisions *owner_=nullptr;
        unsigned bank_=RankPredicateInstance::max_operands+1;
        std::size_t slot_=0;
        mutable std::optional<Item> cache_;
        const_iterator(const PackedRankDecisions *owner,unsigned bank,std::size_t slot):owner_(owner),bank_(bank),slot_(slot){}
        void skip() {
            while(bank_<owner_->banks_.size()){
                const auto &b=owner_->banks_[bank_];
                while(slot_<b.cells.size() && !b.cells[slot_])++slot_;
                if(slot_<b.cells.size())return;++bank_;slot_=0;
            }
            bank_=RankPredicateInstance::max_operands+1;slot_=0;
        }
    public:
        const_iterator()=default;
        const Item &operator*()const {
            const auto &b=owner_->banks_[bank_];const auto *p=b.keys.data()+slot_*b.words;
            RankPredicateInstance instance;instance.id=p[0]>>32U;
            std::copy_n(p+1,b.words-1,instance.operands.begin());
            cache_.emplace(Item{RankDecisionKey(std::uint32_t(p[0]),instance),b.cells[slot_]==1});return *cache_;
        }
        const Item *operator->()const{return &**this;}
        const_iterator &operator++(){++slot_;cache_.reset();skip();return *this;}
        bool operator==(const const_iterator &b)const{return owner_==b.owner_ && bank_==b.bank_ && slot_==b.slot_;}
        bool operator!=(const const_iterator &b)const{return !(*this==b);}
    };
    explicit PackedRankDecisions(std::pmr::memory_resource *resource):resource_(resource),banks_(resource),word_banks_(resource),region_banks_(resource){}
    std::size_t size()const{return size_;}
    bool empty()const{return size_==0;}
    void clear(){banks_.clear();word_banks_.clear();region_banks_.clear();size_=0;}
    // Exact parameter regions use this same integer-key layout to address
    // the common Cells payload. No row locator or independent proof owner.
    std::optional<std::uint64_t> find_region(const RankDecisionKey &key)const {
        const auto a=arity(key);if(a>=region_banks_.size()||region_banks_[a].cells.empty())return {};
        const auto &b=region_banks_[a];const auto slot=b.locate(key);
        return b.cells[slot]?std::optional<std::uint64_t>(b.good[slot]):std::nullopt;
    }
    std::size_t region_allocation_cost(const RankDecisionKey &key)const {
        const auto a=arity(key),words=1+(a+1)/2;
        if(region_banks_.empty())return (RankPredicateInstance::max_operands+1)*sizeof(Bank)+16*(words*8+17);
        const auto &b=region_banks_.at(a);if(b.cells.empty())return 16*(words*8+17);
        if(b.cells[b.locate(key)])return 0;
        return (b.used+1)*10>b.cells.size()*7?b.cells.size()*2*(words*8+17):0;
    }
    void record_region(const RankDecisionKey &key,std::uint64_t offset){
        const auto a=arity(key);if(a>RankPredicateInstance::max_operands)throw std::logic_error("proof region arity");
        if(region_banks_.empty()){
            region_banks_.reserve(RankPredicateInstance::max_operands+1);
            for(unsigned i=0;i<=RankPredicateInstance::max_operands;++i)region_banks_.emplace_back(1+(i+1)/2,resource_,true);
        }
        auto &b=region_banks_[a];if(b.cells.empty())b.grow(16);auto slot=b.locate(key);
        if(b.cells[slot]){if(b.good[slot]!=offset)throw std::logic_error("proof region moved");return;}
        if((b.used+1)*10>b.cells.size()*7){b.grow(b.cells.size()*2);slot=b.locate(key);}
        auto *p=b.keys.data()+slot*b.words;p[0]=key.rank_and_predicate;std::copy_n(key.operands.begin(),b.words-1,p+1);
        b.cells[slot]=1;b.good[slot]=offset;++b.used;
    }
    struct Word {std::uint64_t good=0,nogood=0;};
    Word find_word(const RankDecisionKey &key)const {
        const auto a=arity(key);if(a>=word_banks_.size() || word_banks_[a].cells.empty())return {};
        const auto &b=word_banks_[a];const auto slot=b.locate(key);
        return b.cells[slot]?Word{b.good[slot],b.nogood[slot]}:Word{};
    }
    std::size_t word_allocation_cost(const RankDecisionKey &key)const {
        const auto a=arity(key);const auto words=1+(a+1)/2;
        if(word_banks_.empty())return (RankPredicateInstance::max_operands+1)*sizeof(Bank)+16*(words*8+17);
        const auto &b=word_banks_.at(a);
        if(b.cells.empty())return 16*(words*8+17);
        const auto slot=b.locate(key);if(b.cells[slot])return 0;
        return (b.used+1)*10>b.cells.size()*7 ? b.cells.size()*2*(words*8+17):0;
    }
    bool insert_word(const RankDecisionKey &key,std::uint64_t good,std::uint64_t nogood) {
        if(good&nogood)return false;
        if(!(good|nogood))return true;
        const auto a=arity(key);if(a>RankPredicateInstance::max_operands)throw std::logic_error("word decision arity exceeds integer key");
        if(word_banks_.empty()){
            word_banks_.reserve(RankPredicateInstance::max_operands+1);
            for(unsigned i=0;i<=RankPredicateInstance::max_operands;++i)word_banks_.emplace_back(1+(i+1)/2,resource_,true);
        }
        auto &b=word_banks_[a];if(b.cells.empty())b.grow(16);
        auto slot=b.locate(key);
        if(b.cells[slot]){
            if((b.good[slot]&nogood) || (b.nogood[slot]&good))return false;
            b.good[slot]|=good;b.nogood[slot]|=nogood;return true;
        }
        if((b.used+1)*10>b.cells.size()*7){b.grow(b.cells.size()*2);slot=b.locate(key);}
        auto *p=b.keys.data()+slot*b.words;p[0]=key.rank_and_predicate;
        std::copy_n(key.operands.begin(),b.words-1,p+1);b.cells[slot]=1;
        b.good[slot]=good;b.nogood[slot]=nogood;++b.used;++size_;return true;
    }
    const_iterator end()const{return const_iterator(this,RankPredicateInstance::max_operands+1,0);}
    const_iterator begin()const{const_iterator result(this,0,0);result.skip();return result;}
    const_iterator find(const RankDecisionKey &key)const {
        const auto a=arity(key);if(a>=banks_.size() || banks_[a].cells.empty())return end();
        const auto &b=banks_[a];const auto slot=b.locate(key);
        return b.cells[slot]?const_iterator(this,a,slot):end();
    }
    std::pair<const_iterator,bool> emplace(const RankDecisionKey &key,bool truth) {
        const auto a=arity(key);if(a>RankPredicateInstance::max_operands)throw std::logic_error("packed decision arity exceeds integer key");
        if(banks_.empty()){
            banks_.reserve(RankPredicateInstance::max_operands+1);
            for(unsigned i=0;i<=RankPredicateInstance::max_operands;++i)banks_.emplace_back(1+(i+1)/2,resource_);
        }
        auto &b=banks_[a];
        if(b.cells.empty())b.grow(16);
        auto slot=b.locate(key);
        if(b.cells[slot])return {const_iterator(this,a,slot),false};
        if((b.used+1)*10>b.cells.size()*7){b.grow(b.cells.size()*2);slot=b.locate(key);}
        auto *p=b.keys.data()+slot*b.words;p[0]=key.rank_and_predicate;
        std::copy_n(key.operands.begin(),b.words-1,p+1);b.cells[slot]=truth?1:2;
        ++b.used;++size_;return {const_iterator(this,a,slot),true};
    }
};
