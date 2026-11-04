#pragma once
#include <cstdint>
#include <cstddef>
#include <vector>
#include <stdexcept>

// A plan-compiled Boolean circuit. Masks name requests, never stored row
// decisions. Runtime state is reset for each arriving target assignment.
namespace composed_requests {
class Formula {
public:
    enum Kind {leaf,constant,negation,conjunction,disjunction};
    struct Node {
        Kind kind;std::size_t a=0,b=0,parent=SIZE_MAX;
        std::uint64_t branches=0;int literal=-1;
    };
private:
    struct State {int value=-1;unsigned open=0,good=0;std::uint64_t needed=0;};
    std::vector<Node> nodes_;
    std::vector<State> initial_,state_;
    std::vector<std::vector<std::size_t>> uses_=std::vector<std::vector<std::size_t>>(64);
    std::size_t root_=SIZE_MAX;
    std::uint64_t known_=0,truth_=0,updates_=0;
    unsigned arity(const Node &n)const{return n.kind==negation ? 1U : 2U;}
    void derive(std::size_t id) {
        const auto &n=nodes_[id];auto &s=state_[id];
        if(n.kind==leaf || n.kind==constant)return;
        if(n.kind==negation)s.value=s.open ? -1 : !state_[n.a].value;
        else if(n.kind==conjunction)s.value=(arity(n)-s.open-s.good) ? 0 : !s.open ? 1 : -1;
        else s.value=s.good ? 1 : !s.open ? 0 : -1;
        s.needed=s.value>=0 ? 0U : state_[n.a].needed|
            (n.kind==negation ? 0U : state_[n.b].needed);
    }
public:
    std::size_t add(Kind kind,std::size_t a=0,std::size_t b=0,int literal=-1) {
        const auto id=nodes_.size();Node n{kind,a,b,SIZE_MAX,0,literal};
        if(kind==leaf){if(a>=64U)throw std::logic_error("request mask exceeds 64 branches");n.branches=std::uint64_t{1}<<a;uses_[a].push_back(id);}
        else if(kind!=constant){
            if(a>=id || (kind!=negation && b>=id))throw std::logic_error("formula is not postorder");
            if(nodes_[a].parent!=SIZE_MAX || (kind!=negation && nodes_[b].parent!=SIZE_MAX))
                throw std::logic_error("formula uses need distinct activation nodes");
            nodes_[a].parent=id;n.branches=nodes_[a].branches;
            if(kind!=negation){nodes_[b].parent=id;n.branches|=nodes_[b].branches;}
        }
        nodes_.push_back(n);return id;
    }
    void finish(std::size_t root) {
        if(root>=nodes_.size())throw std::logic_error("missing formula root");root_=root;
        state_.assign(nodes_.size(),{});
        for(std::size_t i=0;i<nodes_.size();++i) {
            const auto &n=nodes_[i];auto &s=state_[i];
            if(n.kind==leaf)s.needed=n.branches;
            else if(n.kind==constant)s.value=n.literal;
            else {
                const auto count=arity(n);
                for(unsigned j=0;j<count;++j){const auto &c=state_[j ? n.b : n.a];s.open+=c.value<0;s.good+=c.value==1;}
                derive(i);
            }
        }
        initial_=state_;begin();
    }
    void begin(){state_=initial_;known_=truth_=updates_=0;}
    int value()const{return state_.at(root_).value;}
    std::uint64_t needed()const{return state_.at(root_).needed;}
    std::uint64_t known()const{return known_;}
    std::uint64_t truth()const{return truth_;}
    std::uint64_t updates()const{return updates_;}
    const std::vector<Node> &nodes()const{return nodes_;}
    void settle(unsigned request,bool good) {
        const auto bit=std::uint64_t{1}<<request;
        if(known_&bit){if(bool(truth_&bit)!=good)throw std::logic_error("request decision flipped");return;}
        known_|=bit;if(good)truth_|=bit;
        for(auto child:uses_.at(request)) {
            state_[child].value=good;state_[child].needed=0;
            bool changed_value=true;
            for(auto p=nodes_[child].parent;p!=SIZE_MAX;child=p,p=nodes_[p].parent) {
                auto &s=state_[p];if(s.value>=0)break;
                const auto old=s.value;const auto needed=s.needed;
                if(changed_value){if(!s.open)throw std::logic_error("formula open count underflow");--s.open;s.good+=state_[child].value==1;}
                derive(p);changed_value=old!=s.value;
#if CF_DIAGNOSTIC_COUNTERS
                ++updates_;
#endif
                if(!changed_value && needed==s.needed)break;
            }
        }
    }
};
}
