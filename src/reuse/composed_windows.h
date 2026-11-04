#pragma once
#include <algorithm>
#include <cstdint>
#include <limits>
#include <map>
#include <memory>
#include <cstring>
#include "request_formula.h"
#include "rank_witness_types.h"
#include <stdexcept>
#include <vector>

// Query-local summaries of COMPLETE witnesses, not an artifact or a key set.
// A window is half-open in the existing probe universe: [lo, hi). Endpoints
// may equal the universe size; SQL NULL is never a valid probe rank.
namespace composed_windows {
constexpr std::uint32_t null_rank=UINT32_MAX;
struct Window {
    std::uint32_t lo=0,hi=0;
    bool operator==(const Window &b)const{return lo==b.lo && hi==b.hi;}
};
// Functional chains have zero or one window. Keep that case scalar during
// composition too, not only after storing it in the dense boundary arrays.
// Heap storage is needed only for a genuine multi-window witness union.
class WindowList {
    Window one_{};
    std::vector<Window> many_;
    std::size_t size_=0;
public:
    std::size_t size()const{return size_;}
    bool empty()const{return size_==0;}
    std::size_t capacity()const{return size_<=1U ? 1U : many_.capacity();}
    std::size_t heap_bytes()const{return many_.capacity()*sizeof(Window);}
    Window *begin(){return size_<=1U ? &one_ : many_.data();}
    const Window *begin()const{return size_<=1U ? &one_ : many_.data();}
    Window *end(){return begin()+size_;}
    const Window *end()const{return begin()+size_;}
    Window &operator[](std::size_t i){return begin()[i];}
    const Window &operator[](std::size_t i)const{return begin()[i];}
    Window &front(){return *begin();}
    const Window &front()const{return *begin();}
    void clear(){size_=0;many_.clear();}
    void push_back(Window w) {
        if(!size_){one_=w;size_=1;return;}
        if(size_==1U){many_.clear();many_.push_back(one_);}
        many_.push_back(w);++size_;
    }
    void resize(std::size_t n) {
        if(n>size_)throw std::logic_error("window list only shrinks");
        if(n<=1U && size_>1U){if(n)one_=many_.front();many_.clear();}
        else if(n>1U)many_.resize(n);
        size_=n;
    }
    template<class It>void insert(Window *position,It first,It last) {
        if(position!=end())throw std::logic_error("window insertion is append-only");
        for(;first!=last;++first)push_back(*first);
    }
    void swap(WindowList &other) {
        std::swap(one_,other.one_);many_.swap(other.many_);std::swap(size_,other.size_);
    }
    bool operator==(const WindowList &b)const {
        return size_==b.size_ && std::equal(begin(),end(),b.begin());
    }
};
struct Coverage {
    WindowList windows;
    static Coverage all(std::uint32_t count) {
        Coverage c;if(count)c.windows.push_back({0,count});return c;
    }
    bool empty()const{return windows.empty();}
    bool covers(std::uint32_t rank)const {
        if(rank==null_rank)return false;
        auto it=std::upper_bound(windows.begin(),windows.end(),rank,
            [](std::uint32_t r,const Window &w){return r<w.lo;});
        return it!=windows.begin() && rank<(--it)->hi;
    }
    void add(Window w) {if(w.lo<w.hi)windows.push_back(w);}
    void finish() {
        std::sort(windows.begin(),windows.end(),[](Window a,Window b){return a.lo<b.lo;});
        std::size_t out=0;
        for(auto w:windows) {
            if(w.lo>=w.hi)continue;
            if(out && w.lo<=windows[out-1].hi)
                windows[out-1].hi=std::max(windows[out-1].hi,w.hi);
            else windows[out++]=w;
        }
        windows.resize(out);
    }
    void unite(const Coverage &other) {
        if(this==&other)return;
        if(other.empty())return;
        if(empty()){*this=other;return;}
        if(windows.size()==1U && other.windows.size()==1U) {
            const auto a=windows.front(),b=other.windows.front();
            if(a.lo<=b.hi && b.lo<=a.hi) {
                windows.front()={std::min(a.lo,b.lo),std::max(a.hi,b.hi)};return;
            }
        }
        windows.insert(windows.end(),other.windows.begin(),other.windows.end());finish();
    }
    void intersect(const Coverage &other) {
        WindowList result;std::size_t a=0,b=0;
        while(a<windows.size() && b<other.windows.size()) {
            const auto lo=std::max(windows[a].lo,other.windows[b].lo);
            const auto hi=std::min(windows[a].hi,other.windows[b].hi);
            if(lo<hi)result.push_back({lo,hi});
            if(windows[a].hi<other.windows[b].hi)++a;else ++b;
        }
        windows.swap(result);
    }
    bool operator==(const Coverage &b)const{return windows==b.windows;}
};

// Rows contribute independently: intersect every atom/child requirement of
// ONE complete witness, then union the resulting windows across witnesses.
// Never take the independent extrema of unrelated witness fragments.
class Witness {
    Coverage coverage_;
public:
    explicit Witness(std::uint32_t count):coverage_(Coverage::all(count)){}
    void require(Window w) {Coverage c;c.add(w);coverage_.intersect(c);}
    void require(const Coverage &c){coverage_.intersect(c);}
    void reject(){coverage_.windows.clear();}
    const Coverage &coverage()const{return coverage_;}
};

enum class Shape {truth,lower,upper,window,witness};
inline Window ordered_window(Shape shape,std::uint32_t endpoint,bool shifted,std::uint32_t universe) {
    if(endpoint==null_rank)return {};
    const auto boundary=endpoint+unsigned(shifted);
    return shape==Shape::lower ? Window{boundary,universe} : Window{0,boundary};
}
// Query-local rank-major records. Layout is metadata; the buffer is allocated
// only by the first arriving Store. A slot still denotes exactly one Rest.
class RankMajor {
public:
    struct Slot {unsigned state_byte=0,shift=0;std::size_t lower=SIZE_MAX,upper=SIZE_MAX;};
private:
    std::size_t count_,stride_=0;
    std::vector<Slot> slots_;
    std::vector<std::uint8_t> records_;
    mutable std::uint32_t current_=null_rank;
    mutable const std::uint8_t *record_=nullptr;
public:
    RankMajor(std::size_t count,const std::vector<Shape> &shapes):count_(count) {
        stride_=(shapes.size()+3U)/4U;
        for(std::size_t i=0;i<shapes.size();++i) {
            Slot s;s.state_byte=i/4U;s.shift=(i&3U)*2U;
            if(shapes[i]==Shape::lower || shapes[i]==Shape::window){s.lower=stride_;stride_+=4U;}
            if(shapes[i]==Shape::upper || shapes[i]==Shape::window){s.upper=stride_;stride_+=4U;}
            slots_.push_back(s);
        }
        if(stride_ && count_>SIZE_MAX/stride_)throw std::overflow_error("rank-major budget overflow");
    }
    std::size_t count()const{return count_;}
    std::size_t stride()const{return stride_;}
    std::size_t planned_bytes()const{return count_*stride_;}
    std::size_t bytes()const{return records_.size();}
    const std::uint8_t *data()const{return records_.empty() ? nullptr : records_.data();}
    const Slot &slot(std::size_t i)const{return slots_.at(i);}
    const std::uint8_t *record(std::uint32_t key)const {
        if(key>=count_)throw std::out_of_range("rank-major entering rank");
        if(records_.empty())return nullptr;
        // All branches arriving at this rank use the same contiguous record.
        if(current_!=key){current_=key;record_=records_.data()+key*stride_;}
        return record_;
    }
    void allocate(){if(records_.empty()){records_.resize(planned_bytes());current_=null_rank;record_=nullptr;}}
    unsigned state(std::uint32_t key,const Slot &s)const {
        const auto p=record(key);return p ? (p[s.state_byte]>>s.shift)&3U : 0U;
    }
    std::uint32_t value(std::uint32_t key,std::size_t offset)const {
        std::uint32_t v;std::memcpy(&v,record(key)+offset,sizeof(v));return v;
    }
    void value(std::uint32_t key,std::size_t offset,std::uint32_t v) {
        auto p=const_cast<std::uint8_t*>(record(key));std::memcpy(p+offset,&v,sizeof(v));
    }
    void state(std::uint32_t key,const Slot &s,unsigned v) {
        auto p=const_cast<std::uint8_t*>(record(key));
        p[s.state_byte]=(p[s.state_byte]&~(3U<<s.shift))|(v<<s.shift);
    }
};
// Dense cells indexed by ONE entering rank or by the unique existing posting
// position. No tuple ranks, hashed predicates, or row IDs computed offline.
// Unset/nogood/good are separate two-bit states. Storage allocates on arrival.
class Cells {
    std::size_t count_=0;
    Shape shape_=Shape::truth;
    std::uint32_t universe_=1;
    bool recording_=true;
    std::vector<std::uint8_t> states_;
    std::vector<std::uint32_t> lower_,upper_;
    std::shared_ptr<RankMajor> rank_major_;
    RankMajor::Slot rank_slot_;
    std::unique_ptr<rank_summaries::WitnessPayload> witnesses_;
    bool has_lower()const{return shape_==Shape::lower || shape_==Shape::window;}
    bool has_upper()const{return shape_==Shape::upper || shape_==Shape::window;}
    std::uint32_t lower(std::uint32_t key)const{return rank_major_ ? rank_major_->value(key,rank_slot_.lower) : lower_[key];}
    std::uint32_t upper(std::uint32_t key)const{return rank_major_ ? rank_major_->value(key,rank_slot_.upper) : upper_[key];}
    // Genuine unions with holes need their full shape, not a convex hull.
    // This is a single-rank map, populated only for exceptional multi-windows.
    std::map<std::uint32_t,Coverage> unions_;
public:
    // Non-owning witness access. Before the first Record every valid key
    // addresses the same constant UNSET slot; it is not a decision array.
    // After allocation all keys address the existing rank directory directly.
    // The caller proves a valid non-NULL entering rank outside the hot loop.
    struct WitnessReadView {
        static inline constexpr rank_summaries::Slot unset{};
        const rank_summaries::Slot *directory=&unset;
        const rank_summaries::WitnessPayload *payload=nullptr;
        std::uint32_t key_mask=0;
        const rank_summaries::Slot &slot(std::uint32_t key)const noexcept{return directory[key&key_mask];}
        const rank_summaries::Slot *probe(std::uint32_t key)const noexcept{
            const auto &s=slot(key);return s.offset==UINT64_MAX ? nullptr : &s;
        }
        const rank_summaries::Point &point(std::uint64_t position)const noexcept{return payload->points[position];}
    };
    WitnessReadView witness_read_view()const{
        if(!witnesses_)throw std::logic_error("witness view requested for a window");
        WitnessReadView view;view.payload=witnesses_.get();
        if(!witnesses_->slots.empty()){view.directory=witnesses_->slots.data();view.key_mask=UINT32_MAX;}
        return view;
    }
    void plan_witness(std::size_t count,std::pmr::memory_resource *memory){
        if(count_ || witnesses_ || !states_.empty() || rank_major_)throw std::logic_error("replanning a rank summary");
        if(count>SIZE_MAX/sizeof(rank_summaries::Slot))throw std::overflow_error("witness rank directory overflow");
        count_=count;shape_=Shape::witness;
        witnesses_=std::make_unique<rank_summaries::WitnessPayload>(memory);
    }
    rank_summaries::WitnessPayload &witness_payload(){return *witnesses_;}
    const rank_summaries::WitnessPayload &witness_payload()const{return *witnesses_;}
    const rank_summaries::Slot *probe(std::uint32_t key)const{
        if(!witnesses_ || key>=count_)throw std::out_of_range("witness entering rank");
        const auto &slots=witnesses_->slots;
        return key<slots.size() && slots[key].offset!=UINT64_MAX ? &slots[key] : nullptr;
    }
    // Publish only a completed witness/proof region. A cancelled fill is not
    // an exhaustive absence proof, and cannot make a later request nogood.
    bool put(std::uint32_t key,rank_summaries::Slot value,bool complete=true){
        if(probe(key))throw std::logic_error("witness rank filled twice");
        if(!complete || !recording_)return false;
        if(value.offset==UINT64_MAX)throw std::logic_error("invalid witness slice");
        if(witnesses_->slots.empty())witnesses_->slots.resize(count_);
        witnesses_->slots[key]=value;return true;
    }
    void discard_witnesses(){
        if(!witnesses_)throw std::logic_error("discarding a window as witnesses");
        witnesses_->clear();
        recording_=false;
    }
    // A non-owning read specialization of this very store, not a second set
    // of boundaries. Layout is selected outside the row loop. First Record
    // allocates the buffers, so callers must refresh after every fill.
    template<bool Major> struct ReadView {
        const std::uint8_t *states=nullptr,*lower=nullptr,*upper=nullptr;
        std::size_t stride=0;
        unsigned shift=0;
        bool allocated()const{return states!=nullptr;}
        unsigned state(std::uint32_t key)const {
            if constexpr(Major)return (states[std::size_t(key)*stride]>>shift)&3U;
            else return (states[key/4U]>>((key&3U)*2U))&3U;
        }
        template<Shape Form> std::uint32_t bound(std::uint32_t key)const {
            static_assert(Form==Shape::lower || Form==Shape::upper);
            const auto *p=Form==Shape::lower ? lower : upper;
            std::uint32_t value;
            std::memcpy(&value,p+std::size_t(key)*(Major ? stride : sizeof(value)),sizeof(value));
            return value;
        }
        // Preconditions: allocated, valid entering key, non-NULL universe
        // rank. Checked access remains in Cells::probe_window and the walk.
        template<Shape Form> int probe_window(std::uint32_t key,std::uint32_t rank)const {
            const auto s=state(key);if(!s)return -1;if(s==1U)return 0;
            const auto boundary=bound<Form>(key);
            const bool good=Form==Shape::lower ? rank>=boundary : rank<boundary;
            return good ? 1 : s==3U ? -1 : 0;
        }
    };
    template<bool Major> ReadView<Major> read_view()const {
        if(witnesses_)throw std::logic_error("window view requested for witness form");
        if(bool(rank_major_)!=Major)throw std::logic_error("wrong bound read layout");
        ReadView<Major> view;
        if constexpr(Major) {
            const auto *p=rank_major_->data();if(!p)return view;
            view.states=p+rank_slot_.state_byte;view.stride=rank_major_->stride();view.shift=rank_slot_.shift;
            if(has_lower())view.lower=p+rank_slot_.lower;
            if(has_upper())view.upper=p+rank_slot_.upper;
        } else {
            view.states=states_.empty() ? nullptr : states_.data();
            view.lower=reinterpret_cast<const std::uint8_t*>(lower_.data());
            view.upper=reinterpret_cast<const std::uint8_t*>(upper_.data());
        }
        return view;
    }
    std::size_t count()const{return count_;}
    Shape shape()const{return shape_;}
    bool recording()const{return recording_;}
    void stop_recording(){recording_=false;}
    // A one-sided witness union is itself one interval. This is the direct
    // instance of Probe, not a second cache or a copied chain boundary.
    // Partial cells prove yes only; an uncovered point must resume the Walk.
    template<Shape Form> int probe_window(std::uint32_t key,std::uint32_t rank)const {
        static_assert(Form==Shape::lower || Form==Shape::upper);
        if(rank==null_rank || rank>=universe_)return 0;
        const auto s=state(key);if(!s)return -1;if(s==1U)return 0;
        const bool good=Form==Shape::lower ? rank>=lower(key) : rank<upper(key);
        return good ? 1 : s==3U ? -1 : 0;
    }
    const RankMajor *rank_major()const{return rank_major_.get();}
    const RankMajor::Slot &rank_slot()const{return rank_slot_;}
    // A collective node obtains its record address ONCE, then each request
    // checks its own exact Rest slot and probe value in that same record.
    int probe_record(std::uint32_t key,std::uint32_t rank,const std::uint8_t *record)const {
        if(!rank_major_)return probe(key,rank);
        if(rank==null_rank || rank>=universe_)return 0;
        if(!record)return -1;
        const auto s=(record[rank_slot_.state_byte]>>rank_slot_.shift)&3U;
        if(!s)return -1;if(s==1U)return 0;
        auto multi=unions_.find(key);bool good;
        if(multi!=unions_.end())good=multi->second.covers(rank);
        else {
            std::uint32_t lo=0,hi=universe_;
            if(has_lower())std::memcpy(&lo,record+rank_slot_.lower,4);
            if(has_upper())std::memcpy(&hi,record+rank_slot_.upper,4);
            good=lo<=rank && rank<hi;
        }
        return good ? 1 : s==3U ? -1 : 0;
    }
    void attach(std::shared_ptr<RankMajor> bank,std::size_t slot) {
        if(!states_.empty() || rank_major_ || witnesses_ || bank->bytes() || bank->count()!=count_)
            throw std::logic_error("rank-major layout must precede every arrival");
        rank_slot_=bank->slot(slot);rank_major_=std::move(bank);
    }
    void plan(std::size_t count,Shape shape,std::uint32_t universe) {
        if(!states_.empty() || rank_major_ || witnesses_)throw std::logic_error("replanning filled bound cells");
        if(shape==Shape::witness)throw std::logic_error("witness plans require a payload allocator");
        count_=count;shape_=shape;universe_=universe;
    }
    std::size_t planned_bytes()const {
        if(shape_==Shape::witness)return count_*sizeof(rank_summaries::Slot);
        const auto arrays=shape_==Shape::truth ? 0U : shape_==Shape::window ? 2U : 1U;
        if(count_>(std::numeric_limits<std::size_t>::max()-3U)/(4U*arrays+1U))
            throw std::overflow_error("bound cell budget overflow");
        return (count_+3U)/4U+count_*4U*arrays;
    }
    std::size_t bytes()const {
        if(witnesses_)return witnesses_->bytes();
        std::size_t bytes=states_.size()+4U*(lower_.size()+upper_.size());
        for(const auto &entry:unions_)bytes+=sizeof(entry)+4U*sizeof(void*)+
            entry.second.windows.capacity()*sizeof(Window);
        return bytes;
    }
    std::size_t extra_bytes(const Coverage &c)const {
        return c.windows.size()>1U ? sizeof(std::pair<const std::uint32_t,Coverage>)+
            4U*sizeof(void*)+c.windows.size()*sizeof(Window) : 0U;
    }
    unsigned state(std::uint32_t key)const {
        if(key>=count_)throw std::out_of_range("bound entering rank");
        if(witnesses_){const auto *slot=probe(key);return !slot ? 0U : slot->count ? 2U : 1U;}
        if(rank_major_)return rank_major_->state(key,rank_slot_);
        return states_.empty() ? 0U : (states_[key/4U]>>((key&3U)*2U))&3U;
    }
    // State 3 contains sound good windows but does not establish nogood outside
    // them. A later uncovered request must resume/recompute, never answer false
    // merely from this partial envelope.
    bool complete(std::uint32_t key)const{const auto s=state(key);return s==1U || s==2U;}
    // Dense decision gather: -1 means the requesting point still needs the
    // arrival walk. Partial windows may prove good, never an outside nogood.
    int probe(std::uint32_t key,std::uint32_t rank)const {
        if(witnesses_)throw std::logic_error("window probe requested for witness form");
        if(rank==null_rank || rank>=universe_)return 0;
        const auto s=state(key);if(!s)return -1;
        if(s==1U)return 0;
        auto multi=unions_.find(key);
        const bool good=multi!=unions_.end() ? multi->second.covers(rank) :
            (!has_lower() || lower(key)<=rank) && (!has_upper() || rank<upper(key));
        return good ? 1 : s==3U ? -1 : 0;
    }
    Coverage get(std::uint32_t key)const {
        if(witnesses_)throw std::logic_error("window requested from witness form");
        const auto s=state(key);if(!s)throw std::logic_error("reading unset bound");
        Coverage c;if(s==1U)return c;
        auto multi=unions_.find(key);if(multi!=unions_.end())return multi->second;
        c.add({has_lower() ? lower(key) : 0U,has_upper() ? upper(key) : universe_});
        return c;
    }
    bool covers(std::uint32_t key,std::uint32_t rank)const {
        if(witnesses_)throw std::logic_error("window requested from witness form");
        if(rank==null_rank || rank>=universe_)return false;
        const auto s=state(key);if(!s)throw std::logic_error("reading unset bound");
        if(s==1U)return false;
        auto multi=unions_.find(key);if(multi!=unions_.end())return multi->second.covers(rank);
        return (!has_lower() || lower(key)<=rank) && (!has_upper() || rank<upper(key));
    }
    void put(std::uint32_t key,Coverage c,bool complete=true) {
        if(witnesses_)throw std::logic_error("window recorded in witness form");
        const auto s=state(key);c.finish();
        if(s) {
            if(s!=3U) {
                if(!(get(key)==c))throw std::logic_error("kept bound flipped");
                return;
            }
            auto preserved=get(key);preserved.intersect(c);
            if(!(preserved==get(key)))throw std::logic_error("partial bound lost a good witness");
        }
        if(!complete && c.empty())return; // no proof of a globally empty envelope
        for(auto w:c.windows)if(w.hi>universe_)throw std::logic_error("bound outside probe universe");
        if(rank_major_)rank_major_->allocate();
        else if(states_.empty()) {
            states_.assign((count_+3U)/4U,0);
            if(shape_==Shape::lower || shape_==Shape::window)lower_.resize(count_);
            if(shape_==Shape::upper || shape_==Shape::window)upper_.resize(count_);
        }
        if(!c.empty()) {
            if(c.windows.size()>1U)unions_[key]=c;
            else {
                unions_.erase(key);
                const auto w=c.windows.front();
                if((shape_==Shape::truth && (w.lo!=0U || w.hi!=universe_)) ||
                   (shape_==Shape::lower && w.hi!=universe_) ||
                   (shape_==Shape::upper && w.lo!=0U))
                    throw std::logic_error("bound shape disagrees with plan");
                if(has_lower()){if(rank_major_)rank_major_->value(key,rank_slot_.lower,w.lo);else lower_[key]=w.lo;}
                if(has_upper()){if(rank_major_)rank_major_->value(key,rank_slot_.upper,w.hi);else upper_[key]=w.hi;}
            }
        }
        const auto next=c.empty() ? 1U : complete ? 2U : 3U;
        if(rank_major_)rank_major_->state(key,rank_slot_,next);
        else {const auto shift=(key&3U)*2U;
            states_[key/4U]=(states_[key/4U]&~(3U<<shift))|(next<<shift);}
    }
};
}
