#pragma once
#include "nested_quantifier_walk.h"
#include <sstream>
#include <tuple>
// Lower only sibling flat quantifiers. Their implicit locals are exactly the
// referenced non-target occurrences; rename those locals separately per scope.
// No atom, polarity, connective, literal, operator or driving slice changes.
namespace nested_walk { namespace flat_scope {
struct Result {
    bool routed=false;unsigned flat_branches=0,shared_skeletons=0;
    std::vector<unsigned> atom_branch,atom_source;
    std::map<int,unsigned> occurrence_branch;
};
inline std::set<unsigned> mandatory(const std::vector<Expr>&es,int id){
    const auto e=es.at(id);if(e.kind==Kind::atom)return {unsigned(e.value)};
    if(e.kind!=Kind::conjunction&&e.kind!=Kind::disjunction)return {};
    auto a=mandatory(es,e.left),b=mandatory(es,e.right);
    if(e.kind==Kind::conjunction){a.insert(b.begin(),b.end());return a;}
    std::set<unsigned> both;std::set_intersection(a.begin(),a.end(),b.begin(),b.end(),std::inserter(both,both.end()));return both;
}
inline Result lower(std::vector<Atom>&atoms,std::vector<Expr>&expressions,int root,int target,bool apply=true){
    Result out;std::vector<int> quantifiers;bool nested=false;
    std::function<void(int,bool)> find=[&](int id,bool inside){const auto e=expressions.at(id);
        if(e.kind==Kind::exists){nested|=inside;quantifiers.push_back(id);inside=true;}
        if(e.left>=0)find(e.left,inside);if(e.right>=0)find(e.right,inside);};find(root,false);
    out.flat_branches=quantifiers.size();if(nested||quantifiers.size()<2)return out;
    struct Plan {int expression;std::vector<int> locals;std::string skeleton;std::set<std::string> work;};std::vector<Plan> plans;
    std::map<std::string,unsigned> counts;std::map<std::string,std::map<std::string,unsigned>> shared_work;
    int next=target+1;for(const auto&a:atoms)next=std::max(next,std::max(a.left.occurrence,a.constant?-1:a.right.occurrence)+1);
    for(int id:quantifiers){const auto e=expressions[id];std::set<int> refs;
        std::function<void(int)> collect=[&](int n){auto x=expressions[n];if(x.kind==Kind::atom){const auto&a=atoms.at(x.value);refs.insert(a.left.occurrence);if(!a.constant)refs.insert(a.right.occurrence);}
            if(x.left>=0)collect(x.left);if(x.right>=0)collect(x.right);};collect(e.left);refs.erase(target);
        if(!e.locals.empty()&&std::set<int>(e.locals.begin(),e.locals.end())!=refs)return out;
        auto required=mandatory(expressions,e.left);std::map<int,int> bound{{target,-1}};Plan p;p.expression=id;
        while(!refs.empty()){
            bool found=false;std::tuple<unsigned,int,unsigned,int> best{};
            for(auto index:required){const auto&a=atoms[index];if(a.constant||a.op!=1)continue;
                for(bool reverse:{false,true}){const auto local=reverse?a.right:a.left,outer=reverse?a.left:a.right;
                    if(!refs.count(local.occurrence)||!bound.count(outer.occurrence))continue;
                    auto candidate=std::make_tuple(local.column,bound[outer.occurrence],outer.column,local.occurrence);
                    if(!found||candidate<best){best=candidate;found=true;}}}
            if(!found)return out;auto [column,parent,source,occurrence]=best;
            p.skeleton+=std::to_string(column)+"<-"+std::to_string(parent)+":"+std::to_string(source)+";";
            bound[occurrence]=p.locals.size();p.locals.push_back(occurrence);refs.erase(occurrence);
        }
        // Matching joins alone are not shared parametric work. Require a
        // common non-driver predicate position reading a local relation.
        std::set<std::string> drivers;std::map<int,int> roles{{target,-1}};
        for(unsigned i=0;i<p.locals.size();++i)roles[p.locals[i]]=i;
        auto ref=[&](Ref x){return std::to_string(roles.at(x.occurrence))+":"+std::to_string(x.column);};
        for(auto index:required){const auto &a=atoms[index];
            if(a.left.occurrence==target&&(a.constant||a.right.occurrence==target))continue;
            const auto position=ref(a.left)+":"+(a.constant?"literal":ref(a.right));
            bool driver=false;
            if(!a.constant&&a.op==1){
                for(bool reverse:{false,true}){auto l=reverse?a.right:a.left,r=reverse?a.left:a.right;
                    if(roles[l.occurrence]>=0 && roles[r.occurrence]<roles[l.occurrence]){
                        const auto edge=std::to_string(l.column)+"<-"+std::to_string(roles[r.occurrence])+":"+std::to_string(r.column)+";";
                        driver|=p.skeleton.find(edge)!=std::string::npos;
                    }
                }
            }
            if(!driver)p.work.insert(position);
        }
        if(!p.locals.empty()){++counts[p.skeleton];for(const auto &position:p.work)++shared_work[p.skeleton][position];}
        plans.push_back(std::move(p));
    }
    for(const auto &item:counts)if(item.second>=2){bool useful=false;
        for(const auto &position:shared_work[item.first])useful|=position.second>=2;
        out.shared_skeletons+=useful;
    }
    if(!out.shared_skeletons)return out;out.routed=true;if(!apply)return out;
    for(unsigned i=0;i<atoms.size();++i){out.atom_branch.push_back(0);out.atom_source.push_back(i);}
    for(unsigned branch=0;branch<plans.size();++branch){const auto p=plans[branch];std::map<int,int> aliases;
        for(int old:p.locals){aliases[old]=next;out.occurrence_branch[next++]=branch+1;}
        auto rename=[&](Ref ref){if(ref.occurrence!=target)ref.occurrence=aliases.at(ref.occurrence);return ref;};
        std::function<int(int)> clone=[&](int id){auto e=expressions.at(id);
            if(e.kind==Kind::atom){auto a=atoms.at(e.value);const auto source=unsigned(e.value);a.left=rename(a.left);if(!a.constant)a.right=rename(a.right);
                e.value=atoms.size();atoms.push_back(a);out.atom_branch.push_back(branch+1);out.atom_source.push_back(source);}
            if(e.left>=0)e.left=clone(e.left);if(e.right>=0)e.right=clone(e.right);
            expressions.push_back(e);return int(expressions.size()-1);};
        const int body=clone(expressions[p.expression].left);expressions[p.expression].left=body;expressions[p.expression].locals.clear();
        for(int old:p.locals)expressions[p.expression].locals.push_back(aliases.at(old));
    }
    return out;
}
}}
