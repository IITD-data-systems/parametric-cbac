#pragma once
// Scoped execution strategies for quantified predicates. No policy-side rows
// are materialized: every slice, cell and inner request is reached on arrival.
#include "rank_decision_store.h"
#include "composed_windows.h"
#include "nested_request_masks.h"
#include "collective_rank_fill.h"
#include "rank_sorted_summary.h"
#include "rank_frontier_admission.h"
#include <sys/stat.h>
#include <algorithm>
#include <cstdint>
#include <functional>
#include <fstream>
#include <cstdio>
#include <iterator>
#include <map>
#include <set>
#include <stdexcept>
#include <vector>

namespace nested_walk {
constexpr auto null_rank=UINT32_MAX;
enum class Truth : unsigned char { no, yes, unknown, pending };
inline Truth negate(Truth x) {
    return x==Truth::yes?Truth::no:x==Truth::no?Truth::yes:x;
}
inline Truth combine(Truth a,Truth b,bool conjunction) {
    if(conjunction && (a==Truth::no || b==Truth::no))return Truth::no;
    if(!conjunction && (a==Truth::yes || b==Truth::yes))return Truth::yes;
    if(a==Truth::pending || b==Truth::pending)return Truth::pending;
    if(a==Truth::unknown || b==Truth::unknown)return Truth::unknown;
    return conjunction?Truth::yes:Truth::no;
}
struct Ref {
    int occurrence=-1;
    unsigned column=0;
    bool operator<(const Ref &b)const {
        return occurrence<b.occurrence || (occurrence==b.occurrence && column<b.column);
    }
    bool operator==(const Ref &b)const{return occurrence==b.occurrence && column==b.column;}
};
struct Atom {
    Ref left,right;
    bool constant=false;
    int op=1; // PolicyConstOpC: =,<,<=,>,>=,!=
    std::uint32_t lower=0,upper=0;
};
enum class Kind { atom, conjunction, disjunction, negation, exists, yes, no };
struct Expr {
    Kind kind=Kind::no;
    int value=-1,left=-1,right=-1;
    // Explicit lexical binders. Empty is a zero-variable quantifier, not an
    // invitation to pull variables out of an inner scope.
    std::vector<int> locals;
};
struct Counters {
    std::uint64_t target_evals=0,allowed_rows=0,witness_rows=0;
    std::uint64_t quantifier_calls=0,first_witness_stops=0,exhaustions=0;
    std::uint64_t tight_slice_rows=0,unique_hops=0,kept_hits=0;
    std::uint64_t block_words=0,run_rows_saved=0,formula_instructions=0;
    std::uint64_t envelope_should_apply=0,envelope_probes=0,envelope_hits=0;
    std::uint64_t envelope_fills=0,envelope_declined=0,envelope_invalidated=0;
    std::uint64_t scope_splits=0,split_components=0;
    std::uint64_t exact_probes=0,exact_fills=0,exact_hits=0,outer_dependency_declines=0;
    std::uint64_t coequal_checks=0,coequal_rejections=0;
    std::uint64_t prefix_context_elisions=0,functional_context_elisions=0;
    std::uint64_t formula_updates=0,request_arrivals=0,request_decisions=0;
    std::uint64_t compiled_rows=0,compiled_parts=0,compiled_fallbacks=0,compiled_table_probes=0;
    std::uint64_t dense_probes=0,dense_hits=0,dense_fills=0;
    std::uint64_t packed_probes=0,packed_hits=0,packed_fills=0,gate_bypasses=0;
    std::uint64_t word_hop_probes=0,word_hop_hits=0,word_hop_fills=0;
    std::uint64_t partial_nogood_probes=0,partial_nogood_hits=0,partial_nogood_fills=0;
    std::uint64_t bits_settled_without_read=0,rows_skipped=0;
    std::uint64_t word_envelope_probes=0,word_envelope_hits=0,word_envelope_fills=0;
    unsigned maximum_depth=0;
};
inline bool compare(std::uint32_t a,int op,std::uint32_t b) {
    switch(op){case 1:return a==b;case 2:return a<b;case 3:return a<=b;
        case 4:return a>b;case 5:return a>=b;case 6:return a!=b;}
    throw std::runtime_error("invalid nested comparison");
}
inline int inverse(int op){return op==2?4:op==3?5:op==4?2:op==5?3:op;}

// Host supplies existing per-column forward/inverted arrays, never new
// indexes. visit(column,op,rank,callback) stops when callback returns true.
template<class Host> class Executor {
    using MaskFrame=nested_masks::Formula::Frame;
    using MaskValue=nested_masks::Value;
    using Outcome=nested_masks::Outcome;
    struct Request {bool quantifier=false;int value=-1;unsigned ready=0;};
    struct NodeWork {
        std::uint64_t summary_arrivals=0,summary_hits=0,summary_fills=0,frontier_points=0;
        unsigned column=UINT32_MAX;
        unsigned request_width=1;bool positional=false,union_rest=false;
        std::uint64_t arrivals=0,distinct=0,witness_rows=0;
        std::uint64_t dense_probes=0,dense_hits=0,dense_fills=0;
        std::uint64_t packed_probes=0,packed_hits=0,packed_fills=0;
        std::uint64_t boundary_probes=0,boundary_hits=0,boundary_fills=0,bypasses=0;
    std::uint64_t word_hop_probes=0,word_hop_hits=0,word_hop_fills=0;
    std::uint64_t partial_nogood_probes=0,partial_nogood_hits=0,partial_nogood_fills=0;
    std::uint64_t bits_settled_without_read=0,rows_skipped=0;
        std::vector<std::uint64_t> reached;
    };
    struct Scope {
        int expression=-1;
        std::vector<int> locals;
        std::vector<Ref> refs;
        std::vector<int> mandatory;
        mutable std::map<std::pair<int,int>,std::vector<int>> equality_orders;
        std::set<int> used_atoms;
        std::vector<std::uint32_t> predicates;
        nested_masks::Formula formula;
        std::vector<Request> requests;
        std::map<int,unsigned> atom_slots;
        std::vector<std::uint64_t> ready;
        std::vector<MaskFrame> frames;
        std::vector<NodeWork> work;
        std::vector<int> fact_banks;
        std::vector<int> boundary_banks;
    };
    Host &host_;
    const std::vector<int>& ranked_equalities(const Scope&s,int occurrence,int required=-1){
        const auto key=std::make_pair(occurrence,required);auto found=s.equality_orders.find(key);
        if(found!=s.equality_orders.end())return found->second;
        auto result=s.mandatory;auto count=[&](int id){const auto&a=atoms_[id];if(a.constant||a.op!=1)return std::uint64_t{0};
            if(a.left.occurrence==occurrence)return std::uint64_t(host_.ranks(a.left.column));
            if(a.right.occurrence==occurrence)return std::uint64_t(host_.ranks(a.right.column));return std::uint64_t{0};};
        std::stable_sort(result.begin(),result.end(),[&](int a,int b){if((a==required)!=(b==required))return a==required;return count(a)>count(b);});return s.equality_orders.emplace(key,std::move(result)).first->second;
    }

    std::vector<Atom> atoms_;
    std::vector<Expr> expressions_;
    std::vector<Scope> scopes_;
    std::map<int,int> scope_by_expr_;
    std::vector<std::int64_t> bindings_;
    struct FactBinding {const std::uint32_t *values=nullptr;const std::vector<unsigned> *columns=nullptr;};
    std::vector<FactBinding> fact_bindings_;
    struct BoundaryBinding {int bank=-1;unsigned rank=0,column=0,parameter=0;const rank_theta::Boundary *transient=nullptr;};
    std::vector<BoundaryBinding> boundary_bindings_;
    struct RankBinding {unsigned column=0,rank=0;bool active=false;};
    std::vector<RankBinding> rank_bindings_;
    std::uint32_t bound_rank(Ref ref){
        const auto &rank=rank_bindings_[ref.occurrence];
        if(rank.active){if(ref.column==rank.column)return rank.rank;
            throw std::logic_error("an existence decision cannot supply other row columns");}
        const auto &boundary=boundary_bindings_[ref.occurrence];
        if(boundary.bank>=0){
            if(ref.column==boundary.column)return boundary.rank; // entering assignment, not a row value
            throw std::logic_error("a stored boundary cannot be unpacked for row re-evaluation");
        }
        const auto &point=fact_bindings_[ref.occurrence];
        if(point.values){const auto it=std::lower_bound(point.columns->begin(),point.columns->end(),ref.column);
            if(it==point.columns->end() || *it!=ref.column)throw std::logic_error("uncompiled one-row fact column");
            return point.values[it-point.columns->begin()];}
        return host_.rank(ref.column,bindings_[ref.occurrence]);
    }
    std::map<int,unsigned> occurrence_columns_;
    std::vector<Ref> target_inputs_;
    PackedRankDecisionStore store_;
    std::set<std::uint32_t> registered_;
    std::uint32_t next_predicate_=1;
    struct PredicateInfo {unsigned column=0;std::vector<Ref> filled;};
    std::map<std::uint32_t,PredicateInfo> predicate_info_;
    struct DirectPart {bool enabled=false;unsigned scope=0,column=0,source=0;};
    std::vector<DirectPart> direct_parts_;
    bool compiled_target_=false;
    bool decisions_,runs_;
    bool envelopes_;
    int target_;
    struct Certificate {
        Ref probe;
        composed_windows::Coverage region;
        bool valid=true;
    };
    struct Envelopes {
        Ref probe;
        unsigned column;
        composed_windows::Cells good,nogood;
    };
    // One bank per scoped Rest/stage, indexed by ONE equality-entered rank.
    // Other filled operands decline this dense form rather than inventing a
    // tuple rank. Both banks contain partial proofs, never a convex hull.
    std::map<std::uint32_t,Envelopes> envelopes_by_predicate_;
    std::vector<Certificate*> certificates_;

    void reached(NodeWork &work,unsigned column,unsigned rank) {
        CF_COUNT(
            if(work.column!=UINT32_MAX && work.column!=column)
                throw std::logic_error("diagnostic attribution driver changed within a compiled stage");
            work.column=column;++work.arrivals;
            if(rank!=null_rank && rank<host_.ranks(column)){
                if(work.reached.empty())work.reached.resize((std::uint64_t(host_.ranks(column))+63)/64);
                auto &word=work.reached[rank/64];const auto bit=std::uint64_t{1}<<(rank%64);
                if(!(word&bit)){word|=bit;++work.distinct;}
            }
        );
    }

#include "nested_rank_summaries.inc"
#include "nested_sorted_summaries.inc"
#include "nested_shared_nodes.inc"
#include "nested_merged_frontiers.inc"

    void invalidate_certificates() {
        for(auto certificate:certificates_)if(certificate->valid){
            certificate->valid=false;++counters.envelope_invalidated;}
    }
    void observe(const Atom &a,std::uint32_t left,std::uint32_t right) {
        for(auto certificate:certificates_)if(certificate->valid){
            const bool l=a.left==certificate->probe;
            const bool r=!a.constant && a.right==certificate->probe;
            if(!l && !r)continue;
            if(l && r)continue; // same non-NULL value on both sides
            if(a.constant || a.op==1 || a.op==6){certificate->valid=false;continue;}
            // A NULL on the other side stays UNKNOWN for every non-NULL
            // probe. It imposes no boundary; SQL three-valued logic remains
            // in the compiled formula, including underneath NOT EXISTS.
            const auto other=l?right:left;
            if(other==null_rank)continue;
            const int op=l?a.op:inverse(a.op);
            const auto count=host_.ranks(certificate->probe.column);
            composed_windows::Coverage admitted;
            if(op==2)admitted.add({0,other});
            if(op==3)admitted.add({0,other+1});
            if(op==4)admitted.add({other+1,count});
            if(op==5)admitted.add({other,count});
            if(!compare(l?left:right,op,other)){
                composed_windows::Coverage complement;
                std::uint32_t begin=0;
                for(auto w:admitted.windows){complement.add({begin,w.lo});begin=w.hi;}
                complement.add({begin,count});admitted=std::move(complement);
            }
            certificate->region.intersect(admitted);
        }
    }

    void validate(int expression,std::set<int> bound)const {
        const auto &e=expressions_.at(expression);
        if(e.kind==Kind::atom){auto a=atoms_.at(e.value);
            if(!bound.count(a.left.occurrence) || (!a.constant && !bound.count(a.right.occurrence)))
                throw std::runtime_error("column reference outside its lexical quantifier scope");
            return;
        }
        if(e.kind==Kind::exists)for(auto local:e.locals){
            if(!occurrence_columns_.count(local) || !bound.insert(local).second)
                throw std::runtime_error("duplicate, shadowed or unused quantifier occurrence id");
        }
        if(e.left>=0)validate(e.left,bound);
        if(e.right>=0)validate(e.right,bound);
    }

    void refs(int expression,std::set<Ref> &out)const {
        const auto &e=expressions_.at(expression);
        if(e.kind==Kind::atom){const auto &a=atoms_.at(e.value);out.insert(a.left);
            if(!a.constant)out.insert(a.right);return;}
        if(e.left>=0)refs(e.left,out);
        if(e.right>=0)refs(e.right,out);
    }
    void conjunction_parts(int expression,std::vector<int> &out)const {
        const auto &e=expressions_.at(expression);
        if(e.kind==Kind::conjunction){conjunction_parts(e.left,out);conjunction_parts(e.right,out);}
        else out.push_back(expression);
    }
    int append_conjunction(const std::vector<int> &parts) {
        if(parts.empty())throw std::logic_error("empty scoped component");
        int result=parts.front();
        for(std::size_t i=1;i<parts.size();++i){
            Expr e;e.kind=Kind::conjunction;e.left=result;e.right=parts[i];
            expressions_.push_back(std::move(e));result=expressions_.size()-1;
        }
        return result;
    }
    void split_independent_scopes() {
        // EXISTS over independent connected parts distributes over AND,
        // never over OR. NOT remains outside the resulting Boolean formula.
        // Shared outer values are filled inputs, not materialized key sets.
        const auto original=expressions_.size();
        for(std::size_t id=0;id<original;++id){
            const auto e=expressions_[id];
            if(e.kind!=Kind::exists || e.locals.empty())continue;
            std::vector<int> parts;conjunction_parts(e.left,parts);
            if(parts.size()<2)continue;
            std::map<int,int> parent;
            for(int local:e.locals)parent[local]=local;
            auto find=[&](int x){while(parent[x]!=x)x=parent[x];return x;};
            std::vector<std::vector<int>> dependencies;
            std::set<int> used;
            for(int part:parts){
                std::set<Ref> values;refs(part,values);std::vector<int> locals;
                for(auto value:values)if(parent.count(value.occurrence) &&
                    std::find(locals.begin(),locals.end(),value.occurrence)==locals.end())
                    locals.push_back(value.occurrence);
                for(int local:locals)used.insert(local);
                for(std::size_t j=1;j<locals.size();++j)parent[find(locals[j])]=find(locals[0]);
                dependencies.push_back(std::move(locals));
            }
            // Do not erase the existence requirement of an unused binder.
            if(used.size()!=e.locals.size())continue;
            std::map<int,std::vector<int>> groups;
            for(std::size_t j=0;j<parts.size();++j)
                groups[dependencies[j].empty()?-1:find(dependencies[j][0])].push_back(parts[j]);
            if(groups.size()<2)continue;
            std::vector<int> components;
            for(const auto &group:groups){
                Expr child;child.kind=Kind::exists;child.left=append_conjunction(group.second);
                if(group.first!=-1)for(int local:e.locals)if(find(local)==group.first)child.locals.push_back(local);
                // An outer-only factor is a zero-variable existential: SQL
                // UNKNOWN must become false BEFORE an enclosing NOT applies.
                expressions_.push_back(std::move(child));components.push_back(expressions_.size()-1);
            }
            const int combined=append_conjunction(components);
            expressions_[id]=expressions_[combined];
            ++counters.scope_splits;counters.split_components+=components.size();
        }
    }
    std::set<int> mandatory(int expression)const {
        const auto &e=expressions_.at(expression);
        if(e.kind==Kind::atom)return {e.value};
        if(e.kind!=Kind::conjunction && e.kind!=Kind::disjunction)return {};
        auto a=mandatory(e.left),b=mandatory(e.right);std::set<int> out;
        if(e.kind==Kind::conjunction){a.insert(b.begin(),b.end());return a;}
        std::set_intersection(a.begin(),a.end(),b.begin(),b.end(),std::inserter(out,out.end()));
        return out;
    }
    void used_atoms(int expression,std::set<int> &out)const {
        const auto &e=expressions_.at(expression);
        if(e.kind==Kind::atom){out.insert(e.value);return;}
        if(e.left>=0)used_atoms(e.left,out);
        if(e.right>=0)used_atoms(e.right,out);
    }
    unsigned compile_formula(int expression,Scope &scope,std::map<std::pair<bool,int>,unsigned> &slots) {
        const auto &e=expressions_.at(expression);
        using F=nested_masks::Formula;
        if(e.kind==Kind::atom || e.kind==Kind::exists){
            const bool quantifier=e.kind==Kind::exists;
            const int value=quantifier?scope_by_expr_.at(expression):e.value;
            const auto key=std::make_pair(quantifier,value);
            auto old=slots.find(key);unsigned slot;
            if(old!=slots.end())slot=old->second;
            else {
                slot=scope.requests.size();if(slot>=64)throw std::runtime_error("more than 64 requests at one plan node");
                slots.emplace(key,slot);Request request{quantifier,value,0};
                std::set<Ref> dependencies;
                if(!quantifier){const auto &a=atoms_[value];dependencies.insert(a.left);if(!a.constant)dependencies.insert(a.right);}
                else {const auto &child=scopes_[value];for(auto ref:child.refs)
                    if(std::find(child.locals.begin(),child.locals.end(),ref.occurrence)==child.locals.end() &&
                        !owned_inside(child.expression,ref.occurrence))dependencies.insert(ref);}
                for(auto ref:dependencies){auto position=std::find(scope.locals.begin(),scope.locals.end(),ref.occurrence);
                    if(position!=scope.locals.end())request.ready=std::max(request.ready,unsigned(position-scope.locals.begin()+1));}
                scope.requests.push_back(request);
                if(!quantifier)scope.atom_slots[value]=slot;
            }
            return scope.formula.add(F::input,slot);
        }
        if(e.kind==Kind::yes || e.kind==Kind::no)return scope.formula.add(F::literal,0,0,e.kind==Kind::yes?MaskValue::yes:MaskValue::no);
        const auto left=compile_formula(e.left,scope,slots);
        if(e.kind==Kind::negation)return scope.formula.add(F::not_,left);
        const auto right=compile_formula(e.right,scope,slots);
        return scope.formula.add(e.kind==Kind::conjunction?F::and_:F::or_,left,right);
    }
    Truth atom(int id) {
        const auto &a=atoms_.at(id);
        if(bindings_.at(a.left.occurrence)<0 || (!a.constant && bindings_.at(a.right.occurrence)<0))
            return Truth::pending;
        const auto left=bound_rank(a.left);
        if(left==null_rank)return Truth::unknown;
        bool answer=false;
        if(a.constant){switch(a.op){
            case 1:answer=left>=a.lower && left<a.upper;break;
            case 2:answer=left<a.lower;break;case 3:answer=left<a.upper;break;
            case 4:answer=left>=a.upper;break;case 5:answer=left>=a.lower;break;
            case 6:answer=left<a.lower || left>=a.upper;break;
            default:throw std::runtime_error("invalid nested constant comparison");}}
        else {const auto right=bound_rank(a.right);
            observe(a,left,right);
            if(right==null_rank)return Truth::unknown;
            answer=compare(left,a.op,right);}
        return answer?Truth::yes:Truth::no;
    }
    static MaskValue mask_value(Truth value) {
        return value==Truth::yes?MaskValue::yes:value==Truth::no?MaskValue::no:
            value==Truth::unknown?MaskValue::unknown:MaskValue::open;
    }
    void settle_ready(Scope &scope,MaskFrame &frame,unsigned stage,unsigned depth,bool compiled=false) {
        auto M=scope.ready[stage];
        while(M){
            auto L=M&scope.formula.needed(frame)&~frame.D;
            if(!L)break;
            const auto slot=unsigned(__builtin_ctzll(L));const auto bit=std::uint64_t{1}<<slot;
            const auto request=scope.requests[slot];MaskValue value;
            ++counters.request_arrivals;
            if(request.quantifier){
                const auto result=compiled?compiled_part(slot,depth+1):quantify(request.value,depth+1);
                value=result.H&1U?MaskValue::yes:MaskValue::no;
            }else value=mask_value(atom(request.value));
            if(value==MaskValue::open)throw std::logic_error("request scheduled before its outer operands were bound");
            scope.formula.settle(frame,slot,value,&counters.formula_updates);
            ++counters.request_decisions;M&=~bit;
            if(compiled)++counters.compiled_table_probes;
        }
    }
    DirectPart direct_part(unsigned scope_id)const {
        const auto &scope=scopes_[scope_id];
        if(scope.locals.empty()){
            const auto &e=expressions_[scope.expression];
            if(e.kind==Kind::exists)return direct_part(scope_by_expr_.at(scope.expression));
            return {};
        }
        const int occurrence=scope.locals.front();
        for(auto id:scope.mandatory){const auto &a=atoms_[id];if(a.constant || a.op!=1)continue;
            Ref candidate,bound;
            if(a.left.occurrence==occurrence && a.right.occurrence==target_){candidate=a.left;bound=a.right;}
            else if(a.right.occurrence==occurrence && a.left.occurrence==target_){candidate=a.right;bound=a.left;}
            else continue;
            bool independent=true;
            for(auto ref:scope.refs)if(ref.occurrence==target_ && !(ref==bound))independent=false;
            // The branch may reference the target ONLY through this entering
            // equality; a target-only guard stays a separate Boolean input.
            for(auto atom_id:scope.used_atoms){const auto &test=atoms_[atom_id];
                if(test.left==bound || (!test.constant && test.right==bound)){
                    if(test.constant || test.op!=1)independent=false;
                    const auto other=test.left==bound?test.right:test.left;
                    if(!(other==candidate))independent=false;
                }}
            if(independent)return {true,scope_id,candidate.column,bound.column};
        }
        return {};
    }
    void register_exact(unsigned id,unsigned column,const std::vector<Ref> &filled={}) {
        if(registered_.insert(id).second){
            store_.register_predicate(id,host_.ranks(column),host_.ranks(column));
            if((summary_mode_&4) && filled.empty() &&
                host_.rows(occurrence_columns_.at(target_))>present_count(host_,column,0))
                store_.open_without_probation(id);
            if(!host_.allow_dense(column))store_.use_sparse(id);
            predicate_info_[id&((1U<<RankPredicateInstance::arity_shift)-1)]={column,filled};
        }
    }
    Outcome compiled_part(unsigned slot,unsigned depth) {
        const auto part=direct_parts_.at(slot);
        const auto rank=host_.rank(part.source,bindings_[target_]);
        if(rank==null_rank)return {1,0};
        auto &work=scopes_[part.scope].work.front();reached(work,part.column,rank);
        if(sorted_requests_[part.scope]>=0||summary_requests_[part.scope].plan>=0){const auto answer=answer_request(part.scope,rank);
            if(answer.D)return answer;}
        const auto base=scopes_[part.scope].predicates.front();
        register_exact(base,part.column);RankPredicateInstance instance;instance.id=base;
        bool answer=false;
        if(store_.enabled(base)){
            ++counters.exact_probes;
            if(store_.dense_instance(base))++counters.dense_probes;else ++counters.packed_probes;
            CF_COUNT(if(store_.dense_instance(base))++work.dense_probes;else ++work.packed_probes);
            if(store_.lookup(rank,instance,&answer)){++counters.exact_hits;++counters.kept_hits;
                CF_COUNT(if(store_.dense_instance(base))++work.dense_hits;else ++work.packed_hits);
                if(store_.dense_instance(base))++counters.dense_hits;else ++counters.packed_hits;return {1,answer?1U:0U};}
        }else {++counters.gate_bypasses;CF_COUNT(++work.bypasses);}
        ++counters.compiled_fallbacks;
        return quantify(part.scope,depth,true);
    }
    bool owned_inside(int expression,int occurrence)const {
        const auto &e=expressions_.at(expression);
        if(e.kind==Kind::exists && std::find(e.locals.begin(),e.locals.end(),occurrence)!=e.locals.end())return true;
        return (e.left>=0 && owned_inside(e.left,occurrence)) || (e.right>=0 && owned_inside(e.right,occurrence));
    }
    Outcome quantify(unsigned scope_id,unsigned depth,bool already_probed=false) {
        host_.interrupt();++counters.quantifier_calls;
        counters.maximum_depth=std::max(counters.maximum_depth,depth);
        auto &s=scopes_.at(scope_id);
        for(int occurrence:s.locals)if(bindings_[occurrence]>=0)
            throw std::runtime_error("quantifier binder shadows an occurrence id; use a distinct lexical occurrence");
        auto &frame=s.frames[0];s.formula.begin(frame);
        settle_ready(s,frame,0,depth);
        return walk(scope_id,0,depth,frame,already_probed);
    }
    Outcome walk(unsigned scope_id,unsigned stage,unsigned depth,MaskFrame &frame,bool already_probed=false) {
        host_.interrupt();auto &s=scopes_.at(scope_id);
        const auto value=s.formula.value(frame);
        const std::uint64_t M=1U;std::uint64_t D=0,H=0,L=M;
        if(value==MaskValue::no || value==MaskValue::unknown)return {M,0};
        if(stage==s.locals.size()){
            if(value==MaskValue::open)throw std::runtime_error("unbound operand in quantified body");
            return {M,value==MaskValue::yes?M:0};
        }
        const int occurrence=s.locals[stage];
        unsigned column=occurrence_columns_.at(occurrence);int op=0;std::uint32_t pivot=0;
        Ref driver_bound;
        // Mandatory drivers only. An atom inside just one OR alternative may
        // not discard candidates of the other alternative.
        for(int id:ranked_equalities(s,occurrence)){const auto &a=atoms_[id];
            if(a.constant)continue;
            Ref candidate,bound;
            if(a.left.occurrence==occurrence && bindings_[a.right.occurrence]>=0){candidate=a.left;bound=a.right;}
            else if(a.right.occurrence==occurrence && bindings_[a.left.occurrence]>=0){candidate=a.right;bound=a.left;}
            else continue;
            if(op==1 && a.op!=1)continue;
            column=candidate.column;op=candidate==a.left?a.op:inverse(a.op);
            driver_bound=bound;
            pivot=bound_rank(bound);
            if(op==1)break;
        }
        if(op && pivot==null_rank){++counters.exhaustions;return {M,0};}
        auto &work=s.work[stage];if(!already_probed)reached(work,column,op?pivot:null_rank);
        if(stage==0 && op==1 && (sorted_requests_[scope_id]>=0||summary_requests_[scope_id].plan>=0)){
            const auto answer=answer_request(scope_id,pivot);if(answer.D)return answer;
        }
        // Equalities to the SAME entered column can be verified outside its
        // Rest. A mismatching filled operand rejects THIS request only, with
        // no nogood stored at the entering rank. Only after all agree may
        // their tautological connection atoms be omitted from a cached Rest.
        std::set<Ref> checked_equal_operands;
        if(op==1)for(int id:s.mandatory){const auto &a=atoms_[id];
            if(a.constant || a.op!=1)continue;
            Ref bound;
            if(a.left.occurrence==occurrence && a.left.column==column && bindings_[a.right.occurrence]>=0)bound=a.right;
            else if(a.right.occurrence==occurrence && a.right.column==column && bindings_[a.left.occurrence]>=0)bound=a.left;
            else continue;
            ++counters.coequal_checks;
            for(auto certificate:certificates_)if(certificate->valid && certificate->probe==bound){
                certificate->valid=false;++counters.envelope_invalidated;}
            if(bound_rank(bound)!=pivot){
                ++counters.coequal_rejections;return {M,0};
            }
            checked_equal_operands.insert(bound);
        }
        // A probe-dependent iterator can change the set of unvisited rows.
        // Its answer cannot certify a window from just the visited witnesses.
        // Keep the ordinary tight iterator, but decline that enclosing proof.
        for(auto certificate:certificates_)if(op && driver_bound==certificate->probe && certificate->valid){
            certificate->valid=false;++counters.envelope_invalidated;}
        if(op==1 && s.fact_banks[stage]>=0)
            return walk_with_facts(scope_id,stage,depth,frame,pivot);
        if(op==1 && s.boundary_banks[stage]>=0)
            return walk_with_equality_range(scope_id,stage,depth,frame,pivot);
        // The entering rank is ONE column rank. All other bound ranks belong
        // to the filled predicate instance, not a tuple entering index.
        // An equality slice is exactly the entered rank's row set. A whole
        // ordered/!= iterator result is NOT a decision at its pivot rank.
        // Until a valid per-candidate envelope is available, those requests
        // retain the tight range scan, but must not store that shortcut.
        const bool equality_request=decisions_ && op==1;
        RankPredicateInstance instance;bool memo=equality_request;
        std::vector<std::uint32_t> filled;std::vector<Ref> filled_refs;
        for(auto ref:s.refs)if(bindings_[ref.occurrence]>=0){
            // Only operands proved equal by the mandatory arrival checks
            // are fixed by the entering rank. Other filled operands remain
            // dependencies of Rest and decline exact rank-only storage.
            if(op==1 && host_.unique(driver_bound.column) && ref.occurrence==driver_bound.occurrence){
                // The equality entering rank determines this entire outer
                // row when the bound column is data-unique. Its other columns
                // are kept-chain facts, not independent filled key operands.
                ++counters.functional_context_elisions;continue;
            }
            bool only_driver=op==1 && checked_equal_operands.count(ref);
            bool remaining_use=false;
            for(auto id:s.used_atoms){const auto &a=atoms_[id];
                if(!(a.left==ref) && (a.constant || !(a.right==ref)))continue;
                // A satisfied mandatory prefix has already guarded this
                // arrival. Keep it out of the remaining connected part's
                // decision identity, not in every later node's Rest.
                const bool bound=bindings_[a.left.occurrence]>=0 &&
                    (a.constant || bindings_[a.right.occurrence]>=0);
                if(bound && std::binary_search(s.mandatory.begin(),s.mandatory.end(),id) && atom(id)==Truth::yes){
                    ++counters.prefix_context_elisions;continue;
                }
                remaining_use=true;
                const auto other=a.left==ref?a.right:a.left;
                if(a.constant || a.op!=1 || other.occurrence!=occurrence || other.column!=column){only_driver=false;break;}
            }
            if(!remaining_use)continue;
            if(!only_driver){filled.push_back(bound_rank(ref));filled_refs.push_back(ref);}
        }
        // The entering value is still ONE rank. Filled values belong to
        // Rest's parameter slots, packed as integer ranks in the paper's
        // open-addressing decision table, never a composite entering index.
        memo=memo && filled.size()<=RankPredicateInstance::max_operands;
        if(equality_request && !memo)++counters.outer_dependency_declines;
        const auto base=s.predicates[stage];
        Envelopes *envelope=nullptr;
        Certificate certificate;
        if(envelopes_ && equality_request && filled.size()==1 && filled[0]!=null_rank){
            const auto probe=filled_refs[0];bool eligible=true,used=false;
            for(auto id:s.used_atoms){const auto &a=atoms_[id];
                if(a.left==probe || (!a.constant && a.right==probe)){
                    used=true;if(a.constant || a.op==1 || a.op==6)eligible=false;}}
            if(eligible && used){++counters.envelope_should_apply;
                register_exact(base,column,filled_refs);
                if(store_.enabled(base)){
                auto it=envelopes_by_predicate_.find(base);
                if(it==envelopes_by_predicate_.end() &&
                    host_.allow_envelope(column,host_.ranks(probe.column))){
                    Envelopes bank;bank.probe=probe;bank.column=column;
                    bank.good.plan(host_.ranks(column),composed_windows::Shape::window,host_.ranks(probe.column));
                    bank.nogood.plan(host_.ranks(column),composed_windows::Shape::window,host_.ranks(probe.column));
                    it=envelopes_by_predicate_.emplace(base,std::move(bank)).first;
                }
                if(it!=envelopes_by_predicate_.end()){
                    envelope=&it->second;
                    if(!(envelope->probe==probe) || envelope->column!=column)
                        throw std::logic_error("nested envelope Rest identity changed");
                    ++counters.envelope_probes;
                    CF_COUNT(++work.boundary_probes);
                    int known=-1;composed_windows::Coverage proof;
                    if(envelope->good.probe(pivot,filled[0])==1){known=1;proof=envelope->good.get(pivot);}
                    else if(envelope->nogood.probe(pivot,filled[0])==1){known=0;proof=envelope->nogood.get(pivot);}
                    store_.observe_range(base,known>=0,known>=0?1:0);
                    if(known>=0){++counters.envelope_hits;
                        CF_COUNT(++work.boundary_hits);
                        for(auto active:certificates_)if(active->valid){
                            if(active->probe==probe)active->region.intersect(proof);
                            else {active->valid=false;++counters.envelope_invalidated;}}
                        return {M,known==1?M:0};
                    }
                    certificate.probe=probe;
                    certificate.region=composed_windows::Coverage::all(host_.ranks(probe.column));
                    if(!store_.enabled(base))envelope=nullptr;
                }else ++counters.envelope_declined;
                }else ++counters.gate_bypasses;
            }
        }
        if(!PackedRankDecisionStore::Key(base | (std::uint32_t(filled.size())<<RankPredicateInstance::arity_shift),filled.size(),
            [&](unsigned i,unsigned &value){value=filled[i];return true;},instance))memo=false;
        // A boundary is already a decision form for this Rest: no redundant
        // point-table probe/write when its complete-witness window is used.
        if(envelope)memo=false;
        if(memo){
            register_exact(instance.id,column,filled_refs);
            if(!store_.enabled(instance.id)){memo=false;if(!already_probed)++counters.gate_bypasses;}
        }
        if(memo){
            bool answer=false;
            // An exact memo cell proves only its filled point. Do not use it
            // as evidence for an enclosing varying-probe window.
            if(!already_probed){++counters.exact_probes;
                if(store_.dense_instance(instance.id))++counters.dense_probes;else ++counters.packed_probes;
                CF_COUNT(if(store_.dense_instance(instance.id))++work.dense_probes;else ++work.packed_probes);
                if(store_.lookup(pivot,instance,&answer)){++counters.kept_hits;++counters.exact_hits;
                    CF_COUNT(if(store_.dense_instance(instance.id))++work.dense_hits;else ++work.packed_hits);
                    if(store_.dense_instance(instance.id))++counters.dense_hits;else ++counters.packed_hits;
                    invalidate_certificates();return {M,answer?M:0};}}
        }
        if(envelope)certificates_.push_back(&certificate);
        bool answer=false;std::uint64_t rows=0;
        // The host executes a tight existing-inverted-slice scan or a unique
        // hop. No recursive expression traversal is in this row loop.
        auto visit=[&](std::uint32_t row){
            ++rows;++counters.witness_rows;++counters.tight_slice_rows;
            CF_COUNT(++work.witness_rows);
            bindings_[occurrence]=row;
            auto &child=s.frames[stage+1];s.formula.inherit(child,frame);
            settle_ready(s,child,stage+1,depth);
            const auto result=walk(scope_id,stage+1,depth,child);
            answer=(result.H&M)!=0;
            bindings_[occurrence]=-1;
            return answer;
        };
        if(op)host_.visit(column,op,pivot,visit);
        else for(std::uint32_t row=0;row<host_.rows(column);++row)if(visit(row))break;
        if(op==1 && host_.unique(column))++counters.unique_hops;
        if(answer)++counters.first_witness_stops;else ++counters.exhaustions;
        if(envelope){
            certificates_.pop_back();
            if(certificate.valid && !certificate.region.empty()){
                if(!certificate.region.covers(filled[0]))throw std::logic_error("nested window lost arriving probe");
                auto &cells=answer?envelope->good:envelope->nogood;
                auto &opposite=answer?envelope->nogood:envelope->good;
                if(opposite.state(pivot)){
                    auto overlap=opposite.get(pivot);overlap.intersect(certificate.region);
                    if(!overlap.empty())throw std::logic_error("nested envelope decision flipped");}
                if(cells.state(pivot)){auto previous=cells.get(pivot);certificate.region.unite(previous);}
                cells.put(pivot,std::move(certificate.region),false);++counters.envelope_fills;
                CF_COUNT(++work.boundary_fills);
            }
        }
        if(memo && store_.enabled(instance.id)){
            if(!store_.insert(pivot,instance,answer))throw std::runtime_error("nested decision flipped");
            ++counters.exact_fills;if(store_.dense_instance(instance.id))++counters.dense_fills;else ++counters.packed_fills;}
        CF_COUNT(if(memo && store_.enabled(instance.id)){
            if(store_.dense_instance(instance.id))++work.dense_fills;else ++work.packed_fills;});
        D|=L;if(answer)H|=L;L&=~D;
        return {D,H};
    }
public:
    Counters counters;
    template<class H>static auto skipped_slice(H &host,unsigned column,unsigned rank,int)->decltype(host.slice_rows(column,rank)){
        return host.slice_rows(column,rank);
    }
    template<class H>static std::uint64_t skipped_slice(H &,unsigned,unsigned,long){return 0;}
    template<class H>static auto present_count(H &host,unsigned column,int)->decltype(host.present_ranks(column)) {
        return host.present_ranks(column);
    }
    template<class H>static unsigned present_count(H &host,unsigned column,long){return host.ranks(column);}
    Executor(Host &host,std::vector<Atom> atoms,std::vector<Expr> expressions,int root,int target,
             bool decisions=true,bool runs=true,bool envelopes=true,unsigned summary_mode=0,
             std::uint64_t summary_budget=0,bool summary_cost_guard=true):host_(host),atoms_(std::move(atoms)),
             expressions_(std::move(expressions)),decisions_(decisions),runs_(runs),envelopes_(envelopes),target_(target) {
        summary_mode_=summary_mode;summary_budget_=summary_budget;summary_cost_guard_=summary_cost_guard;
        int max_occurrence=target;
        for(auto a:atoms_){occurrence_columns_.emplace(a.left.occurrence,a.left.column);
            max_occurrence=std::max(max_occurrence,a.left.occurrence);
            if(!a.constant){occurrence_columns_.emplace(a.right.occurrence,a.right.column);
                max_occurrence=std::max(max_occurrence,a.right.occurrence);}}
        bindings_.resize(max_occurrence+1,-1);
        fact_bindings_.resize(max_occurrence+1);
        boundary_bindings_.resize(max_occurrence+1);
        rank_bindings_.resize(max_occurrence+1);
        validate(root,{target});
        split_independent_scopes();
        validate(root,{target});
        for(std::size_t i=0;i<expressions_.size();++i)if(expressions_[i].kind==Kind::exists){
            const auto &e=expressions_[i];Scope s;s.expression=e.left;s.locals=e.locals;
            auto m=mandatory(e.left);s.mandatory.assign(m.begin(),m.end());
            used_atoms(e.left,s.used_atoms);
            std::set<Ref> r;refs(e.left,r);s.refs.assign(r.begin(),r.end());
            for(auto unused:s.locals){(void)unused;s.predicates.push_back(next_predicate_++);}
            scope_by_expr_[i]=scopes_.size();scopes_.push_back(std::move(s));
        }
        Scope s;s.expression=root;std::set<Ref> r;refs(root,r);s.refs.assign(r.begin(),r.end());
        for(auto ref:r)if(ref.occurrence==target)target_inputs_.push_back(ref);
        scopes_.push_back(std::move(s));
        for(auto &scope:scopes_){std::map<std::pair<bool,int>,unsigned> slots;
            const auto root_formula=compile_formula(scope.expression,scope,slots);scope.formula.finish(root_formula);
            scope.ready.assign(scope.locals.size()+1,0);scope.frames.resize(scope.locals.size()+1);
            scope.work.resize(scope.locals.size());
            scope.fact_banks.assign(scope.locals.size(),-1);
            scope.boundary_banks.assign(scope.locals.size(),-1);
            for(unsigned i=0;i<scope.requests.size();++i)scope.ready[scope.requests[i].ready]|=std::uint64_t{1}<<i;
            for(auto &frame:scope.frames)scope.formula.begin(frame);
        }
        // The scalar fallback uses this same fixed entry priority.
        // No allocation or rank-cardinality sort on row arrivals.
        for(const auto&scope:scopes_)for(auto occurrence:scope.locals)
            (void)ranked_equalities(scope,occurrence);
        configure_word_graph();
        configure_summaries();
        configure_rank_facts();
        configure_equality_ranges();
        configure_word_summary_routes();
        auto &root_scope=scopes_.back();compiled_target_=decisions_ && root_scope.formula.table_entries()!=0;
        direct_parts_.resize(root_scope.requests.size());
        for(unsigned i=0;i<root_scope.requests.size();++i){const auto &request=root_scope.requests[i];
            if(request.quantifier){direct_parts_[i]=direct_part(request.value);compiled_target_&=direct_parts_[i].enabled;
                if(direct_parts_[i].enabled)++counters.compiled_parts;}
            else {const auto &a=atoms_[request.value];compiled_target_&=a.left.occurrence==target_ && (a.constant || a.right.occurrence==target_);}}
    }
    bool evaluate(std::uint32_t row) {
        ++summary_epoch_;
        bindings_[target_]=row;
        if(word_graph_ready_){const auto answer=word_evaluate();bindings_[target_]=-1;++counters.compiled_rows;return answer;}
        auto &scope=scopes_.back();auto &frame=scope.frames.front();scope.formula.begin(frame);
        settle_ready(scope,frame,0,0,compiled_target_);
        const auto result=scope.formula.value(frame);
        bindings_[target_]=-1;
        if(result==MaskValue::open)throw std::runtime_error("unbound operand outside quantified scope");
        if(compiled_target_)++counters.compiled_rows;
        return result==MaskValue::yes;
    }
    std::vector<std::uint64_t> run(std::uint32_t rows) {
        std::vector<std::uint64_t> allowed((std::uint64_t(rows)+63)/64,0);
        std::vector<std::uint32_t> previous,target_values;
        bool old_answer=false;
        // Block bitmap executor, with input-tuple run reuse inside the block.
        for(std::uint64_t begin=0;begin<rows;begin+=64){++counters.block_words;
            std::uint64_t word=0;
            for(auto row=begin;row<std::min<std::uint64_t>(rows,begin+64);++row){
                host_.interrupt();target_values.clear();
                for(auto ref:target_inputs_)target_values.push_back(host_.rank(ref.column,row));
                bool answer;
                if(runs_ && row && target_values==previous){answer=old_answer;++counters.run_rows_saved;}
                else answer=evaluate(row);
                previous=target_values;old_answer=answer;++counters.target_evals;
                if(answer){word|=1ULL<<(row-begin);++counters.allowed_rows;}
            }
            allowed[begin/64]=word;
        }
        for(auto &bank:store_.summaries)bank.finish_walk();
        return allowed;
    }
    const PackedRankDecisionStore &store()const{return store_;}
    bool compiled_target()const{return compiled_target_;}
    template<class Visitor>void visit_summaries(Visitor visitor)const {
        for(unsigned id=0;id<summary_plans_.size();++id){const auto &plan=summary_plans_[id];
            std::vector<unsigned> users;
            for(unsigned scope=0;scope<summary_requests_.size();++scope)if(summary_requests_[scope].plan==int(id))users.push_back(scope);
            visitor(id,plan.scope,plan.column,users,store_.summaries[plan.bank]);
        }
    }
    template<class Visitor>void visit_node_work(Visitor visitor)const {
        if(word_graph_ready_){
            for(unsigned group=0;group<word_groups_.size();++group){const auto &g=word_groups_[group];const auto &s=scopes_[g.scope];
                for(unsigned stage=0;stage<g.work.size();++stage)visitor(group,stage,s.locals[stage],g.memos[stage].full.predicate?g.memos[stage].full.predicate:s.predicates[stage],g.work[stage]);}
            return;
        }
        for(unsigned scope=0;scope<scopes_.size();++scope){const auto &s=scopes_[scope];
            for(unsigned stage=0;stage<s.work.size();++stage)
                visitor(scope,stage,s.locals[stage],s.predicates[stage],s.work[stage]);
        }
    }
    template<class Visitor>void visit_compiled_groups(Visitor visitor)const{
        if(!word_graph_ready_)return;
        for(unsigned id=0;id<word_groups_.size();++id){const auto &g=word_groups_[id];
            for(unsigned bit=0;bit<g.members.size();++bit){const auto &m=g.members[bit];const auto &scope=scopes_[m.scope];
                visitor(id,bit,m.scope,scope.locals,scope.used_atoms,g.drivers,scope.mandatory);}}
    }
    template<class Visitor>void visit_summary_work(Visitor visitor)const{
        for(unsigned id=0;id<sorted_plans_.size();++id){const auto&p=sorted_plans_[id];visitor(summary_plans_.size()+id,0,p.scope,0,p.local,p.column,store_.summaries[p.bank].requests,p.work);}
        for(unsigned id=0;id<summary_plans_.size();++id){const auto &plan=summary_plans_[id];
            for(unsigned i=0;i<plan.work.size();++i){const auto&step=plan.steps[i];
                visitor(id,i,step.scope,step.stage,step.occurrence,step.column,plan.requests,plan.work[i]);}}
    }
    template<class Visitor>void visit_sorted_summaries(Visitor visitor)const{
        for(unsigned id=0;id<store_.summaries.size();++id)if(store_.summaries[id].sorted_mode)visitor(id,store_.summaries[id]);
    }
    template<class Visitor>void visit_summary_eligibility(Visitor visitor)const{
        for(unsigned scope=0;scope<scopes_.size();++scope){const auto&s=scopes_[scope];
            const auto sorted=sorted_requests_[scope];
            const auto reason=sorted>=0?std::string{}:summary_ineligible_[scope]+"; sorted: "+sorted_reasons_[scope];
            visitor(scope,s.locals,s.used_atoms,sorted>=0?int(summary_plans_.size())+sorted:summary_requests_[scope].plan,summary_entered_[scope],summary_test_counts_[scope],reason);}
    }
    bool shared_scope_graph()const{return word_graph_ready_;}
    int shared_scope_group(unsigned scope)const{return word_graph_ready_?word_scope_group_.at(scope):-1;}
    unsigned shared_scope_nodes()const{unsigned result=0;for(const auto &g:word_groups_)result+=g.work.size();return result;}
    template<class Visitor>void visit_predicates(Visitor visit)const {
        for(const auto &state:store_.predicates){
            const auto ordinal=state.predicate_id&((1U<<RankPredicateInstance::arity_shift)-1);
            auto info=predicate_info_.find(ordinal);if(info==predicate_info_.end())continue;
            const char *form=state.word?(store_.word_dense(state.predicate_id)?"dense_word":"packed_word"):
                (state.predicate_id>>RankPredicateInstance::arity_shift)>0?"packed":
                !info->second.filled.empty()?"boundary":state.sparse?"packed_sparse":"dense_2bit";
            visit(state.predicate_id,info->second.column,info->second.filled,state.cardinality,
                state.total_probes,state.total_hits,state.window_probes,state.window_hits,
                state.last_window_probes,state.last_window_hits,state.saved_reads,
                state.enabled,state.threshold,state.immediate||state.word_tablewide,form);
        }
    }
};
} // namespace nested_walk
