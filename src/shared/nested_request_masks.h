#pragma once
#include <algorithm>
#include <array>
#include <cstdint>
#include <stdexcept>
#include <vector>

// Plan-time Boolean circuit and (when small) formula table. Runtime inputs
// are request masks D/H/U, not a stream of Boolean bytecode instructions.
// SQL UNKNOWN is separate from an open request; quantifiers coerce it only
// after their complete witness has been tested.
namespace nested_masks {
enum class Value : unsigned char {open=0,no=1,yes=2,unknown=3};
class Formula {
public:
    enum Kind {input,literal,not_,and_,or_};
    struct Node {Kind kind;unsigned a=0,b=0,parent=UINT32_MAX;Value constant=Value::open;};
    struct State {Value value=Value::open;unsigned open=0,good=0,unknown=0;std::uint64_t needed=0;};
    struct Frame {std::vector<State> states;std::uint64_t D=0,H=0,U=0;std::uint32_t table_key=0;};
private:
    std::vector<Node> nodes_;
    std::array<std::vector<unsigned>,64> uses_;
    std::vector<State> initial_;
    std::vector<unsigned char> table_;
    unsigned root_=UINT32_MAX,inputs_=0;
    std::uint64_t all_=0;
    static Value negate(Value v){return v==Value::no?Value::yes:v==Value::yes?Value::no:v;}
    static Value binary(Value a,Value b,bool conjunction) {
        if(conjunction && (a==Value::no || b==Value::no))return Value::no;
        if(!conjunction && (a==Value::yes || b==Value::yes))return Value::yes;
        if(a==Value::open || b==Value::open)return Value::open;
        return a==Value::unknown || b==Value::unknown?Value::unknown:conjunction?Value::yes:Value::no;
    }
    void derive(unsigned id,std::vector<State> &states)const {
        const auto &n=nodes_[id];auto &s=states[id];
        if(n.kind==input || n.kind==literal)return;
        if(n.kind==not_)s.value=negate(states[n.a].value);
        else {
            const auto count=2U;
            const auto bad=count-s.open-s.good-s.unknown;
            if(n.kind==and_)s.value=bad?Value::no:s.open?Value::open:s.unknown?Value::unknown:Value::yes;
            else s.value=s.good?Value::yes:s.open?Value::open:s.unknown?Value::unknown:Value::no;
        }
        s.needed=s.value!=Value::open?0:states[n.a].needed|(n.kind==not_?0:states[n.b].needed);
    }
public:
    unsigned add(Kind kind,unsigned a=0,unsigned b=0,Value value=Value::open) {
        const auto id=unsigned(nodes_.size());Node n{kind,a,b,UINT32_MAX,value};
        if(kind==input){if(a>=64)throw std::logic_error("more than 64 request slots at one node");
            uses_[a].push_back(id);inputs_=std::max(inputs_,a+1);all_|=std::uint64_t{1}<<a;}
        else if(kind!=literal){
            if(a>=id || (kind!=not_ && b>=id))throw std::logic_error("formula is not postorder");
            if(nodes_[a].parent!=UINT32_MAX || (kind!=not_ && nodes_[b].parent!=UINT32_MAX))
                throw std::logic_error("formula activation nodes must have one parent");
            nodes_[a].parent=id;if(kind!=not_)nodes_[b].parent=id;
        }
        nodes_.push_back(n);return id;
    }
    void finish(unsigned root) {
        if(root>=nodes_.size())throw std::logic_error("missing mask formula root");root_=root;
        initial_.resize(nodes_.size());
        for(unsigned i=0;i<nodes_.size();++i){const auto &n=nodes_[i];auto &s=initial_[i];
            if(n.kind==input)s.needed=std::uint64_t{1}<<n.a;
            else if(n.kind==literal)s.value=n.constant;
            else {for(unsigned j=0;j<(n.kind==not_?1U:2U);++j){const auto &c=initial_[j?n.b:n.a];
                    s.open+=c.value==Value::open;s.good+=c.value==Value::yes;s.unknown+=c.value==Value::unknown;}
                derive(i,initial_);}}
        // The paper's Boolean table is constructed from the FORMULA only.
        // Never read a rank, tuple, artifact row or a bound policy result here.
        if(inputs_<=8){
            table_.resize(std::size_t{1}<<(2*inputs_));std::vector<Value> values(nodes_.size());
            for(std::size_t key=0;key<table_.size();++key){
                for(unsigned i=0;i<nodes_.size();++i){const auto &n=nodes_[i];
                    values[i]=n.kind==input?Value((key>>(2*n.a))&3):n.kind==literal?n.constant:
                        n.kind==not_?negate(values[n.a]):binary(values[n.a],values[n.b],n.kind==and_);}
                table_[key]=static_cast<unsigned char>(values[root_]);
            }
        }
    }
    void begin(Frame &frame)const {frame.states=initial_;frame.D=frame.H=frame.U=0;frame.table_key=0;}
    void inherit(Frame &frame,const Frame &parent)const {frame=parent;}
    Value value(const Frame &frame)const{return table_.empty()?frame.states[root_].value:Value(table_[frame.table_key]);}
    std::uint64_t needed(const Frame &frame)const{return frame.states[root_].needed;}
    std::uint64_t all()const{return all_;}
    std::size_t table_entries()const{return table_.size();}
    Value input_value(const Frame &f,unsigned bit)const {
        const auto mask=std::uint64_t{1}<<bit;
        return !(f.D&mask)?Value::open:f.U&mask?Value::unknown:f.H&mask?Value::yes:Value::no;
    }
    void settle(Frame &frame,unsigned bit,Value value,std::uint64_t *updates=nullptr)const {
        if(value==Value::open)return;
        const auto mask=std::uint64_t{1}<<bit;
        if(frame.D&mask){if(input_value(frame,bit)!=value)throw std::logic_error("request answer flipped");return;}
        frame.D|=mask;if(value==Value::yes)frame.H|=mask;if(value==Value::unknown)frame.U|=mask;
        if(!table_.empty())frame.table_key|=std::uint32_t(value)<<(2*bit);
        for(auto child:uses_[bit]){
            auto &c=frame.states[child];const auto before=c.value;c.value=value;c.needed=0;
            auto old=before;
            for(auto parent=nodes_[child].parent;parent!=UINT32_MAX;child=parent,parent=nodes_[parent].parent){
                auto &s=frame.states[parent];const auto prior=s.value;const auto needed=s.needed;
                const auto now=frame.states[child].value;
                if(old!=now){s.open-=old==Value::open;s.good-=old==Value::yes;s.unknown-=old==Value::unknown;
                    s.open+=now==Value::open;s.good+=now==Value::yes;s.unknown+=now==Value::unknown;}
                derive(parent,frame.states);if(updates)++*updates;
                if(prior==s.value && needed==s.needed)break;old=prior;
            }
        }
    }
};
struct Outcome {std::uint64_t D=0,H=0;};
} // namespace nested_masks
