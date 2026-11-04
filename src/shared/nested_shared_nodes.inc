// Execution strategy of the scoped Walk: a lexical family has ONE iterator
// per template position and a word of requests. Rows are never retained here.
struct WordValue {std::uint64_t yes=0,no=0,unknown=0;};
struct WordInstruction {Kind kind=Kind::no;unsigned a=0,b=0;int input=-1;};
struct WordMember {unsigned scope=0;std::map<int,int> aliases;};
struct WordInput {
    bool child=false,constant=false;unsigned ready=0,child_group=0;
    std::uint64_t present=0;collective_fill::Scatter negative_up;
    Ref left,right;std::array<std::uint64_t,3> accept{};collective_fill::Constants constants;
    collective_fill::Scatter down,up;
    std::vector<std::pair<unsigned,unsigned>> routes;
};
struct WordDriver {unsigned column=0;Ref source;unsigned presence_predicate=0;int atom=-1;};
struct WordMemoKey {unsigned predicate=0;std::vector<Ref> filled;bool never_repeats=false;mutable std::uint64_t probes=0,hits=0;};
struct WordStageMemo {WordMemoKey full,partial;std::vector<unsigned> prefix,partial_inputs;};
struct WordFrame {std::vector<WordValue> inputs,values;std::uint64_t failed=0,unknown_inputs=0,pending=0;};
struct WordSummaryRoute {unsigned member=0,scope=0;int plan=-1;};
struct WordGroup {
    unsigned scope=0;std::string key,whole_key;bool positional=false,heterogeneous=false;int shared_summary=-1;
    std::vector<WordMember> members;
    std::vector<WordInput> inputs;
    std::vector<WordInstruction> program;
    std::vector<WordDriver> drivers;
    std::vector<WordStageMemo> memos;
    std::vector<NodeWork> work;
    std::vector<WordFrame> frames;
    std::vector<WordValue> input_values;
    std::vector<std::uint64_t> input_epochs,stage_epochs,pending_after;
    std::vector<std::vector<unsigned>> ready_inputs;
    std::vector<int> boundary_choices;
    std::uint64_t initial_pending=0;
    collective_fill::Scatter summary_up;
    std::vector<WordSummaryRoute> summary_routes,sorted_routes;
};
struct WordTerm {std::uint64_t positive=0,negative=0;};
struct WordRootUse {int group=-1,atom=-1;std::uint64_t slots=0;collective_fill::Scatter down,up;
    std::vector<std::pair<unsigned,unsigned>> routes;};
std::vector<WordGroup> word_groups_;
std::vector<int> word_scope_group_,word_scope_bit_;
std::vector<WordTerm> word_root_terms_;
std::vector<WordRootUse> word_root_uses_;
bool word_graph_ready_=false;
// Connection roles are resolved once, before collecting any branch. An
// equality that varies by request is a test, never part of a driver key.
std::map<std::pair<unsigned,unsigned>,unsigned> word_connection_ops_,word_connection_uses_;
void prepare_word_connections(){
    for(const auto &s:scopes_)for(unsigned stage=0;stage<s.locals.size();++stage){
        const int occurrence=s.locals[stage];std::set<std::pair<unsigned,unsigned>> seen;
        for(auto id:s.mandatory){const auto &a=atoms_[id];if(a.constant)continue;Ref local,source;
            if(a.left.occurrence==occurrence){local=a.left;source=a.right;}
            else if(a.right.occurrence==occurrence){local=a.right;source=a.left;}else continue;
            const auto it=std::find(s.locals.begin(),s.locals.end(),source.occurrence);
            if(it!=s.locals.end() && unsigned(it-s.locals.begin())>=stage)continue;
            const auto key=std::make_pair(local.column,source.column);
            word_connection_ops_[key]|=1U<<a.op;
            if(seen.insert(key).second)++word_connection_uses_[key];
        }
    }
}
int word_observer_group_=-1;
const WordRootUse *word_observer_use_=nullptr;
std::uint64_t word_observer_D_=0,word_observer_H_=0,word_observer_U_=0,word_observer_good_=0;
bool word_root_finished_=false,word_root_answer_=false;

struct WordCertificate {
    Ref probe;unsigned domain=0;collective_fill::Union region;
    std::array<std::uint64_t,64> mapping{};
};
std::vector<WordCertificate*> word_certificates_;
static void word_intersect(collective_fill::Union &a,const std::vector<rank_requests::MaskedRange>&b){
    a.temporary.clear();unsigned i=0,j=0;
    while(i<a.pieces.size()&&j<b.size()){
        auto x=a.pieces[i],y=b[j];collective_fill::Union::append(a.temporary,std::max(x.lo,y.lo),std::min(x.hi,y.hi),x.mask&y.mask);
        if(x.hi<=y.hi)++i;if(y.hi<=x.hi)++j;
    }
    a.pieces.swap(a.temporary);
}
static std::uint64_t word_mapped(const WordCertificate &c,std::uint64_t mask){
    std::uint64_t result=0;while(mask){auto bit=unsigned(__builtin_ctzll(mask));mask&=mask-1;result|=c.mapping[bit];}return result;
}
void word_point(Ref ref,std::uint64_t live){
    for(auto c:word_certificates_)if(c->probe==ref){
        const auto touched=word_mapped(*c,live);const auto at=bound_rank(ref);std::vector<rank_requests::MaskedRange> p;
        if(at==null_rank)continue;
        collective_fill::Union::append(p,0,at,~touched);collective_fill::Union::append(p,at,at+1,~0ULL);collective_fill::Union::append(p,at+1,c->domain,~touched);word_intersect(c->region,p);
    }
}
void word_observe(const WordInput &input,std::uint64_t live,const WordValue &observed){
    for(auto c:word_certificates_){
        const bool left=input.left==c->probe,right=!input.constant&&input.right==c->probe;
        if(!left&&!right)continue;
        auto other=input.constant?0:bound_rank(left?input.right:input.left);
        if(!input.constant&&other==null_rank)continue; // UNKNOWN stays UNKNOWN
        std::vector<unsigned> cuts{0,c->domain};
        if(input.constant)for(auto x:input.constants.cuts)cuts.push_back(std::min(x,c->domain));
        else{cuts.push_back(std::min(other,c->domain));cuts.push_back(other>=c->domain?c->domain:other+1);}
        std::sort(cuts.begin(),cuts.end());cuts.erase(std::unique(cuts.begin(),cuts.end()),cuts.end());
        std::vector<rank_requests::MaskedRange> proof;
        for(unsigned i=0;i+1<cuts.size();++i){auto x=cuts[i];std::uint64_t yes;
            if(input.constant)yes=input.constants.compare(x).yes;
            else{const auto l=left?x:other,r=right?x:other;yes=input.accept[l<r?0:l==r?1:2];}
            const auto same=(observed.yes&yes)|(observed.no&~yes)|observed.unknown;
            const auto bad=word_mapped(*c,live&~same);
            collective_fill::Union::append(proof,x,cuts[i+1],~bad);
        }
        word_intersect(c->region,proof);
    }
}
std::uint64_t word_child(const WordInput &input,std::uint64_t live,unsigned depth){
    std::vector<std::array<std::uint64_t,64>> saved;
    for(auto c:word_certificates_){saved.push_back(c->mapping);std::array<std::uint64_t,64> next{};
        for(auto route:input.routes)if(live&(1ULL<<route.first))next[route.second]|=c->mapping[route.first];c->mapping=next;}
    const auto answer=word_quantify(input.child_group,input.down(live),depth);
    for(unsigned i=0;i<saved.size();++i)word_certificates_[i]->mapping=saved[i];return answer;
}
std::string word_shape(int expression,std::map<int,std::string> names,unsigned &serial)const{
    const auto &e=expressions_[expression];
    if(e.kind==Kind::atom){const auto &a=atoms_[e.value];
        auto ref=[&](Ref r){auto found=names.find(r.occurrence);
            if(found==names.end())throw std::logic_error("shared graph lost a filled outer operand");
            return found->second+":"+std::to_string(r.column);};
        return "a("+ref(a.left)+","+(a.constant?"constant":ref(a.right))+")";
    }
    std::string key=std::to_string(int(e.kind))+"(";
    if(e.kind==Kind::exists){const auto binder=serial++;
        for(unsigned j=0;j<e.locals.size();++j)names[e.locals[j]]="b"+std::to_string(binder)+"."+std::to_string(j);
        key+=std::to_string(e.locals.size())+":";
    }
    if(e.left>=0)key+=word_shape(e.left,names,serial);
    if(e.right>=0)key+=","+word_shape(e.right,names,serial);
    return key+")";
}

bool word_conjuncts(int expression,std::vector<std::pair<int,bool>>&out)const{
    const auto &e=expressions_[expression];
    if(e.kind==Kind::conjunction)return word_conjuncts(e.left,out)&&word_conjuncts(e.right,out);
    if(e.kind==Kind::atom||e.kind==Kind::exists){out.push_back({expression,false});return true;}
    if(e.kind==Kind::negation&&expressions_[e.left].kind==Kind::exists){out.push_back({e.left,true});return true;}
    return e.kind==Kind::yes;
}
std::string word_skeleton(unsigned scope,const std::map<int,std::string>&outer)const{
    const auto &s=scopes_[scope];std::map<int,std::string> names=outer;
    std::string key="join:"+std::to_string(s.locals.size())+":";
    for(unsigned stage=0;stage<s.locals.size();++stage){const int occurrence=s.locals[stage];
        unsigned best_uses=0;std::string best;
        for(auto id:s.mandatory){const auto &a=atoms_[id];if(a.constant||a.op!=1)continue;Ref local,source;
            if(a.left.occurrence==occurrence){local=a.left;source=a.right;}
            else if(a.right.occurrence==occurrence){local=a.right;source=a.left;}else continue;
            const auto old=names.find(source.occurrence);if(old==names.end())continue;
            const auto pair=std::make_pair(local.column,source.column);
            if(word_connection_ops_.at(pair)!=(1U<<1))continue;
            const auto uses=word_connection_uses_.at(pair);
            const auto candidate=std::to_string(local.column)+"="+old->second+":"+std::to_string(source.column)+";";
            if(uses>best_uses || (uses==best_uses && candidate<best)){best=candidate;best_uses=uses;}
        }
        if(best.empty())return {};key+=best;names[occurrence]="self"+std::to_string(stage);
    }
    return key;
}
unsigned collect_word_scope(unsigned scope,const std::map<int,std::string>& outer_names,
    const std::map<int,int>& outer_aliases,std::map<std::string,unsigned>& shared){
    if(word_scope_group_[scope]>=0)return word_scope_group_[scope];
    const auto &s=scopes_[scope];auto names=outer_names;
    for(unsigned j=0;j<s.locals.size();++j)names[s.locals[j]]="self"+std::to_string(j);
    unsigned serial=0;const auto whole=std::to_string(s.locals.size())+":"+word_shape(s.expression,names,serial);
    std::vector<std::pair<int,bool>> terms;const auto skeleton=word_skeleton(scope,outer_names);
    // A zero-local result of the independent split is a formula wrapper,
    // not an equality-entered iterator. Grouping all such wrappers on the
    // empty skeleton can merge a wrapper with its descendant and overwrite
    // its active frame. Preserve the whole-scope key for these wrappers.
    const bool positional=!s.locals.empty()&&!skeleton.empty()&&word_conjuncts(s.expression,terms);
    const auto key=positional?skeleton:"whole:"+whole;
    auto found=shared.find(key);unsigned id;
    if(found==shared.end()){id=word_groups_.size();shared.emplace(key,id);WordGroup group;
        group.scope=scope;group.key=key;group.whole_key=whole;group.positional=positional;word_groups_.push_back(std::move(group));}
    else id=found->second;
    if(word_groups_[id].whole_key!=whole)word_groups_[id].heterogeneous=true;
    const auto &canonical=scopes_[word_groups_[id].scope];
    if(word_groups_[id].members.size()==64)throw std::runtime_error("shared scope exceeds one request word");
    WordMember member;member.scope=scope;member.aliases=outer_aliases;
    auto child_names=outer_names;
    for(unsigned j=0;j<s.locals.size();++j){
        member.aliases[s.locals[j]]=canonical.locals[j];
        child_names[s.locals[j]]="node"+std::to_string(id)+".stage"+std::to_string(j);
    }
    const auto aliases=member.aliases;
    word_scope_group_[scope]=id;word_scope_bit_[scope]=word_groups_[id].members.size();
    word_groups_[id].members.push_back(std::move(member));
    for(const auto &request:s.requests)if(request.quantifier)
        collect_word_scope(request.value,child_names,aliases,shared);
    return id;
}

Ref word_alias(const WordMember& member,Ref ref)const{
    const auto found=member.aliases.find(ref.occurrence);
    if(found==member.aliases.end())throw std::logic_error("shared node has no outer assignment");
    return {found->second,ref.column};
}

unsigned word_program(int expression,WordGroup& group,const std::map<std::pair<bool,int>,unsigned>& slots){
    const auto &e=expressions_[expression];WordInstruction ins;ins.kind=e.kind;
    if(e.kind==Kind::atom || e.kind==Kind::exists)
        ins.input=slots.at({e.kind==Kind::exists,e.kind==Kind::exists?scope_by_expr_.at(expression):e.value});
    else {
        if(e.left>=0)ins.a=word_program(e.left,group,slots);
        if(e.right>=0)ins.b=word_program(e.right,group,slots);
    }
    const auto result=group.program.size();group.program.push_back(ins);return result;
}

std::vector<WordTerm> word_dnf(int expression,bool negative,const std::map<std::pair<bool,int>,unsigned>& slots)const{
    const auto &e=expressions_[expression];
    if(e.kind==Kind::atom || e.kind==Kind::exists){auto bit=std::uint64_t{1}<<slots.at(
        {e.kind==Kind::exists,e.kind==Kind::exists?scope_by_expr_.at(expression):e.value});
        return {{negative?0:bit,negative?bit:0}};}
    if(e.kind==Kind::yes || e.kind==Kind::no)return (e.kind==Kind::yes)!=negative?std::vector<WordTerm>{{0,0}}:std::vector<WordTerm>{};
    if(e.kind==Kind::negation)return word_dnf(e.left,!negative,slots);
    auto left=word_dnf(e.left,negative,slots),right=word_dnf(e.right,negative,slots);
    if((e.kind==Kind::conjunction)!=negative){std::vector<WordTerm> terms;
        for(auto a:left)for(auto b:right){WordTerm t{a.positive|b.positive,a.negative|b.negative};
            if(!(t.positive&t.negative))terms.push_back(t);
            if(terms.size()>4096)throw std::runtime_error("root formula exceeds compiled request table");}
        return terms;
    }
    left.insert(left.end(),right.begin(),right.end());
    if(left.size()>4096)throw std::runtime_error("root formula exceeds compiled request table");return left;
}

bool word_all_equal(const WordGroup &group,int atom_id)const{
    if(group.positional){
        const auto &canonical=group.members.front();const auto &atom=atoms_[atom_id];
        if(atom.constant || atom.op!=1)return false;
        const auto left=word_alias(canonical,atom.left),right=word_alias(canonical,atom.right);
        for(const auto &member:group.members){bool found=false;
            for(auto id:scopes_[member.scope].mandatory){const auto &a=atoms_[id];if(a.constant||a.op!=1)continue;
                const auto l=word_alias(member,a.left),r=word_alias(member,a.right);
                if((l==left&&r==right)||(l==right&&r==left)){found=true;break;}}
            if(!found)return false;
        }
        return true;
    }
    const auto &canonical=scopes_[group.scope];unsigned position=0;
    for(;position<canonical.requests.size();++position)
        if(!canonical.requests[position].quantifier && canonical.requests[position].value==unsigned(atom_id))break;
    if(position==canonical.requests.size())return false;
    for(const auto &member:group.members){const auto &actual=scopes_[member.scope];
        if(position>=actual.requests.size() || actual.requests[position].quantifier ||
           atoms_[actual.requests[position].value].op!=1)return false;
    }
    return true;
}

int word_preferred_atom(unsigned scope,unsigned stage)const{
    if(!word_graph_ready_ || scope>=word_scope_group_.size() || word_scope_group_[scope]<0)return -1;
    const auto &group=word_groups_[word_scope_group_[scope]];
    if(group.members.size()<2||stage>=group.drivers.size())return -1;
    const auto &driver=group.drivers[stage];
    for(const auto &member:group.members)if(member.scope==scope){
        for(auto id:scopes_[scope].mandatory){const auto &a=atoms_[id];if(a.constant||a.op!=1)continue;
            for(bool reverse:{false,true}){const auto local=reverse?a.right:a.left,source=reverse?a.left:a.right;
                if(local.occurrence==scopes_[scope].locals[stage] && local.column==driver.column && word_alias(member,source)==driver.source)return id;
            }
        }
    }
    return -1;
}
void configure_word_union(WordGroup &group){
    const auto width=group.members.size();const auto all=rank_requests::width_mask(width);
    std::map<std::string,unsigned> positions;std::vector<std::vector<std::pair<unsigned,unsigned>>> down,positive,negative;
    for(unsigned bit=0;bit<width;++bit){const auto &member=group.members[bit];const auto &scope=scopes_[member.scope];
        std::vector<std::pair<int,bool>> terms;if(!word_conjuncts(scope.expression,terms))throw std::logic_error("non-conjunctive body entered positional group");
        for(auto term:terms){const auto &expr=expressions_[term.first];const bool child=expr.kind==Kind::exists;
            const int value=child?scope_by_expr_.at(term.first):expr.value;
            unsigned ready=0;bool found=false;for(const auto &r:scope.requests)if(r.quantifier==child&&r.value==value){ready=r.ready;found=true;break;}
            if(!found)throw std::logic_error("union request missing from scoped compiler");
            Ref left,right;bool constant=false;unsigned child_group=0;std::string key;
            if(child){child_group=word_scope_group_[value];key="child:"+std::to_string(child_group);}
            else{const auto &atom=atoms_[value];left=word_alias(member,atom.left);constant=atom.constant;if(!constant)right=word_alias(member,atom.right);
                key="atom:"+std::to_string(left.occurrence)+":"+std::to_string(left.column)+":"+(constant?"literal":std::to_string(right.occurrence)+":"+std::to_string(right.column));}
            auto old=positions.find(key);unsigned slot;
            if(old==positions.end()){slot=group.inputs.size();positions[key]=slot;WordInput input;input.child=child;input.constant=constant;input.ready=ready;input.child_group=child_group;input.left=left;input.right=right;input.constants.width=width;
                group.inputs.push_back(std::move(input));down.emplace_back();positive.emplace_back();negative.emplace_back();}
            else{slot=old->second;if(group.inputs[slot].ready!=ready)throw std::logic_error("same union position has different readiness");}
            auto &input=group.inputs[slot];const auto mask=1ULL<<bit;
            const bool repeated=(input.present&mask)!=0;input.present|=mask;
            if(child){const unsigned child_bit=word_scope_bit_[value];down[slot].push_back({bit,child_bit});(term.second?negative[slot]:positive[slot]).push_back({child_bit,bit});}
            else{const auto &atom=atoms_[value];if(constant){if(repeated)input.constants.extra[bit].push_back({unsigned(atom.op),atom.lower,atom.upper});
                    else{input.constants.operators[bit]=atom.op;input.constants.lower[bit]=atom.lower;input.constants.upper[bit]=atom.upper;}}
                else for(unsigned o=0;o<3;++o){const bool accepts=collective_fill::outcomes(atom.op)&(1U<<o);
                    if(repeated){if(!accepts)input.accept[o]&=~mask;}else if(accepts)input.accept[o]|=mask;}}
        }
    }
    for(unsigned slot=0;slot<group.inputs.size();++slot){auto &input=group.inputs[slot];const auto absent=all&~input.present;
        if(input.present!=all)group.heterogeneous=true;
        if(!input.child&&!input.constant){const auto &locals=scopes_[group.scope].locals;
            const bool l=std::find(locals.begin(),locals.end(),input.left.occurrence)!=locals.end(),r=std::find(locals.begin(),locals.end(),input.right.occurrence)!=locals.end();
            if(l&&r)for(auto mask:input.accept)if(mask&&mask!=all)group.heterogeneous=true;
        }
        if(input.child){input.routes=down[slot];input.down.configure(down[slot]);input.up.configure(positive[slot]);input.negative_up.configure(negative[slot]);}
        else if(input.constant){for(unsigned bit=0;bit<width;++bit)if(absent&(1ULL<<bit)){input.constants.operators[bit]=5;input.constants.lower[bit]=0;input.constants.upper[bit]=0;}input.constants.compile();}
        else for(auto &mask:input.accept)mask|=absent;
    }
    // Atom positions first at each readiness, then children. This preserves
    // demand: a failed local filter never asks a private child for rows.
    std::vector<unsigned> order;for(unsigned i=0;i<group.inputs.size();++i)order.push_back(i);
    std::stable_sort(order.begin(),order.end(),[&](unsigned a,unsigned b){const auto &x=group.inputs[a],&y=group.inputs[b];return x.ready<y.ready||(x.ready==y.ready&&x.child<y.child);});
    std::vector<WordInput> sorted;for(auto slot:order)sorted.push_back(std::move(group.inputs[slot]));group.inputs=std::move(sorted);
    for(unsigned slot=0;slot<group.inputs.size();++slot){WordInstruction input;input.kind=Kind::atom;input.input=slot;group.program.push_back(input);
        if(group.program.size()>1){WordInstruction both;both.kind=Kind::conjunction;both.a=group.program.size()-2;both.b=group.program.size()-1;group.program.push_back(both);}}
    if(group.program.empty()){WordInstruction yes;yes.kind=Kind::yes;group.program.push_back(yes);}
}
void configure_word_graph(){
    if(!(summary_mode_&128) || !decisions_)return;
    prepare_word_connections();
    word_scope_group_.assign(scopes_.size(),-1);word_scope_bit_.assign(scopes_.size(),-1);
    std::map<std::string,unsigned> shared;
    std::map<int,std::string> names{{target_,"target"}};std::map<int,int> aliases{{target_,target_}};
    const auto &root=scopes_.back();
    for(const auto &request:root.requests)if(request.quantifier)collect_word_scope(request.value,names,aliases,shared);
    // Safe drivers are fixed from mandatory conjuncts, never an OR alternative.
    // An unsupported family retains the previous scoped execution strategy.
    bool eligible=true;
    for(auto &group:word_groups_){const auto &s=scopes_[group.scope];const auto &member=group.members.front();
        std::set<int> bound;for(auto item:member.aliases)if(std::find(s.locals.begin(),s.locals.end(),item.first)==s.locals.end())bound.insert(item.first);
        for(unsigned stage=0;stage<s.locals.size();++stage){const int occurrence=s.locals[stage];bool found=false;WordDriver driver;unsigned best_uses=0;std::uint64_t best_ranks=0;std::pair<unsigned,unsigned> best_pair{UINT32_MAX,UINT32_MAX};
            for(auto atom_id:s.mandatory){const auto &a=atoms_[atom_id];if(a.constant || a.op!=1 || !word_all_equal(group,atom_id))continue;Ref candidate,source;
                if(a.left.occurrence==occurrence){candidate=a.left;source=a.right;}
                else if(a.right.occurrence==occurrence){candidate=a.right;source=a.left;}else continue;
                if(!bound.count(source.occurrence))continue;
                const auto pair=std::make_pair(candidate.column,source.column);
                if(group.members.size()>1&&word_connection_ops_[pair]!=(1U<<1))continue;
                const auto uses=word_connection_uses_[pair];
                const auto ranks=std::uint64_t(host_.ranks(candidate.column));
                if(!found || ranks>best_ranks || (ranks==best_ranks&&(uses>best_uses||(uses==best_uses&&pair<best_pair)))){
                    driver={candidate.column,word_alias(member,source)};driver.atom=atom_id;found=true;best_ranks=ranks;best_uses=uses;best_pair=pair;
                }
            }
            if(!found){eligible=false;break;}
            group.drivers.push_back(driver);bound.insert(occurrence);
        }
        if(!eligible)break;
        std::map<std::pair<bool,int>,unsigned> slots;
        if(group.positional)configure_word_union(group);else for(unsigned i=0;i<s.requests.size();++i){const auto request=s.requests[i];WordInput input;
            input.child=request.quantifier;input.ready=request.ready;input.present=rank_requests::width_mask(group.members.size());slots[{request.quantifier,request.value}]=i;
            if(request.quantifier){input.child_group=word_scope_group_[request.value];
                std::vector<std::pair<unsigned,unsigned>> down,up;
                for(unsigned bit=0;bit<group.members.size();++bit){const auto &actual=scopes_[group.members[bit].scope];
                    if(actual.requests.size()!=s.requests.size() || !actual.requests[i].quantifier)throw std::logic_error("shared request topology changed");
                    const unsigned child=actual.requests[i].value;
                    if(word_scope_group_[child]!=int(input.child_group))throw std::logic_error("shared child route differs between requests");
                    down.push_back({bit,unsigned(word_scope_bit_[child])});up.push_back({unsigned(word_scope_bit_[child]),bit});
                }
                input.routes=down;input.down.configure(down);input.up.configure(up);
            }else {const auto &a=atoms_[request.value];input.constant=a.constant;
                input.left=word_alias(member,a.left);if(!a.constant)input.right=word_alias(member,a.right);
                input.constants.width=group.members.size();
                for(unsigned bit=0;bit<group.members.size();++bit){
                    const auto &actual=atoms_[scopes_[group.members[bit].scope].requests[i].value];
                    if(actual.constant!=a.constant)throw std::logic_error("shared atom kind changed");
                    if(a.constant){input.constants.operators[bit]=actual.op;
                        input.constants.lower[bit]=actual.lower;input.constants.upper[bit]=actual.upper;
                    }else for(unsigned outcome=0;outcome<3;++outcome)
                        if(collective_fill::outcomes(actual.op)&(1U<<outcome))input.accept[outcome]|=std::uint64_t{1}<<bit;
                }
                if(a.constant)input.constants.compile();
            }
            group.inputs.push_back(std::move(input));
        }
        if(!group.positional)word_program(s.expression,group,slots);group.work.resize(s.locals.size());
        for(unsigned stage=0;stage<group.work.size();++stage){group.work[stage].column=group.drivers[stage].column;
            group.work[stage].request_width=group.members.size();group.work[stage].positional=group.positional;group.work[stage].union_rest=group.heterogeneous;}
        group.frames.resize(s.locals.size()+1);
        group.ready_inputs.resize(s.locals.size()+1);group.stage_epochs.resize(s.locals.size()+1);
        group.input_values.resize(group.inputs.size());group.input_epochs.resize(group.inputs.size());
        group.pending_after.resize(group.inputs.size());
        for(unsigned i=0;i<group.inputs.size();++i)group.ready_inputs.at(group.inputs[i].ready).push_back(i);
        std::uint64_t pending=0;
        for(unsigned i=group.inputs.size();i-- >0;){group.pending_after[i]=pending;pending|=group.inputs[i].present;}
        group.initial_pending=pending;
        for(auto &frame:group.frames)if(!group.positional){frame.inputs.resize(group.inputs.size());frame.values.resize(group.program.size());}
    }
    if(!eligible){word_groups_.clear();word_scope_group_.clear();word_scope_bit_.clear();return;}
    std::map<std::pair<bool,int>,unsigned> slots;std::map<unsigned,unsigned> uses;
    std::vector<std::vector<std::pair<unsigned,unsigned>>> down,up;
    for(unsigned slot=0;slot<root.requests.size();++slot){const auto request=root.requests[slot];slots[{request.quantifier,request.value}]=slot;
        if(!request.quantifier){WordRootUse use;use.atom=request.value;use.slots=std::uint64_t{1}<<slot;word_root_uses_.push_back(use);
            down.emplace_back();up.emplace_back();continue;}
        const unsigned group=word_scope_group_[request.value],bit=word_scope_bit_[request.value];
        auto old=uses.find(group);unsigned index;
        if(old==uses.end()){index=word_root_uses_.size();uses[group]=index;WordRootUse use;use.group=group;
            word_root_uses_.push_back(use);down.emplace_back();up.emplace_back();}
        else index=old->second;
        word_root_uses_[index].slots|=std::uint64_t{1}<<slot;
        down[index].push_back({slot,bit});up[index].push_back({bit,slot});
    }
    word_root_terms_=word_dnf(root.expression,false,slots);
    for(unsigned i=0;i<word_root_uses_.size();++i)if(word_root_uses_[i].group>=0){
        word_root_uses_[i].down.configure(down[i]);word_root_uses_[i].up.configure(up[i]);}
    word_graph_ready_=true;
}

void configure_word_summary_routes(){
    if(!word_graph_ready_)return;
    for(auto &group:word_groups_){
        group.summary_routes.clear();group.sorted_routes.clear();
        for(unsigned bit=0;bit<group.members.size();++bit){const auto scope=group.members[bit].scope;
            if(sorted_requests_[scope]>=0)group.sorted_routes.push_back({bit,scope,sorted_requests_[scope]});
            const auto &request=summary_requests_[scope];
            if(request.plan>=0)group.summary_routes.push_back({bit,scope,request.plan});
        }
        const auto &canonical=scopes_[group.scope];group.boundary_choices=canonical.boundary_banks;
        for(unsigned stage=0;stage<group.boundary_choices.size();++stage){auto &choice=group.boundary_choices[stage];
            if(choice<0)continue;const auto &bank=store_.summaries[choice];
            for(const auto &member:group.members)for(auto ref:scopes_[member.scope].refs){const auto alias=member.aliases.find(ref.occurrence);
                if(alias!=member.aliases.end()&&alias->second==canonical.locals[stage]&&ref.column!=bank.column&&ref.column!=bank.parameter_column)choice=-1;}
        }
        // Legacy marker remains diagnostic only. Routes are per request,
        // and distinct Rest signatures are never forced into a union bank.
        group.shared_summary=group.summary_routes.empty()?-1:group.summary_routes.front().plan;
    }
    // This strategy consumes rank-word decision forms. Predicates that fit
    // none retain A+B's packed/envelope path (including its certificate
    // rules), rather than silently dropping those existing mechanisms.
    // 3A: no eligible summary is not a reason to discard the shared graph.
    // Whole-rest word cells at every equality hop are its fallback.
    if(word_graph_ready_)for(auto &group:word_groups_){const auto &scope=scopes_[group.scope];
        for(unsigned stage=0;stage<group.drivers.size();++stage){auto &driver=group.drivers[stage];
            if(scope.boundary_banks[stage]>=0 || (stage==0 && group.shared_summary>=0) || !host_.unique(driver.column))continue;
            bool only_rank=true;for(const auto &m:group.members)for(auto ref:scopes_[m.scope].refs){
                auto alias=m.aliases.find(ref.occurrence);if(alias!=m.aliases.end()&&alias->second==scope.locals[stage]&&ref.column!=driver.column)only_rank=false;}
            if(only_rank){driver.presence_predicate=next_predicate_++;register_exact(driver.presence_predicate,driver.column);}
        }
    }
    configure_word_memos();
}

NodeWork &node_work(unsigned scope,unsigned stage){
    if(word_graph_ready_ && word_scope_group_[scope]>=0)return word_groups_[word_scope_group_[scope]].work[stage];
    return scopes_[scope].work[stage];
}

static WordValue word_positional_value(const WordFrame&frame,std::uint64_t live){
    const auto no=frame.failed&live;
    return {live&~(frame.pending|frame.failed|frame.unknown_inputs),no,live&~(frame.pending|frame.failed)&frame.unknown_inputs};
}
WordValue word_input(const WordGroup&group,const WordFrame&frame,unsigned slot)const{
    if(!group.positional)return frame.inputs[slot];
    return group.input_epochs[slot]==group.stage_epochs[group.inputs[slot].ready]?group.input_values[slot]:WordValue{};
}
void word_set_input(WordGroup&group,WordFrame&frame,unsigned slot,WordValue value){
    if(!group.positional){frame.inputs[slot]=value;return;}
    group.input_values[slot]=value;group.input_epochs[slot]=group.stage_epochs[group.inputs[slot].ready];
    frame.failed|=value.no;frame.unknown_inputs|=value.unknown;frame.pending=group.pending_after[slot];
}
void word_inherit(const WordGroup&group,WordFrame&child,const WordFrame&parent){
    if(group.positional){child.failed=parent.failed;child.unknown_inputs=parent.unknown_inputs;child.pending=parent.pending;}
    else child.inputs=parent.inputs;
}
WordValue word_formula(WordGroup &group,WordFrame &frame,std::uint64_t live){
    if(group.positional)return word_positional_value(frame,live);
    for(unsigned i=0;i<group.program.size();++i){const auto &ins=group.program[i];WordValue value;
        if(ins.input>=0)value=frame.inputs[ins.input];
        else if(ins.kind==Kind::yes)value.yes=live;
        else if(ins.kind==Kind::no)value.no=live;
        else {const auto a=frame.values[ins.a],b=frame.values[ins.b];
            if(ins.kind==Kind::negation)value={a.no,a.yes,a.unknown};
            else if(ins.kind==Kind::conjunction)value={a.yes&b.yes,a.no|b.no,(a.unknown&(b.yes|b.unknown))|(b.unknown&a.yes)};
            else if(ins.kind==Kind::disjunction)value={a.yes|b.yes,a.no&b.no,(a.unknown&(b.no|b.unknown))|(b.unknown&a.no)};
        }
        value.yes&=live;value.no&=live;value.unknown&=live;frame.values[i]=value;
    }
    ++counters.formula_updates;return frame.values.back();
}

void word_ready(unsigned id,unsigned stage,WordFrame &frame,std::uint64_t live,unsigned depth){
    auto &group=word_groups_[id];
    ++group.stage_epochs.at(stage);
    for(auto i:group.ready_inputs.at(stage)){const auto &input=group.inputs[i];
        auto value=group.positional?word_positional_value(frame,live):word_formula(group,frame,live);const auto active=live&~(value.yes|value.no|value.unknown);
        // A true body still needs the quantified locals to exist, but no
        // already-decided request may ask another child to read rows.
        if(!active)break;
        ++counters.request_arrivals;WordValue result;
        if(!(active&input.present)){word_set_input(group,frame,i,{active,0,0});++counters.request_decisions;continue;}
        if(input.child){auto yes=word_child(input,active&input.present,depth+1);
            if(group.positional){const auto child_live=input.down(active&input.present);result.no=(input.up(child_live&~yes)|input.negative_up(yes))&active;result.yes=active&~result.no;}
            else{result.yes=input.up(yes)&active;result.no=active&~result.yes;}
        }else {const auto left=bound_rank(input.left);
            if(input.constant){const auto bits=input.constants.compare(left);result={bits.yes&active,bits.no&active,left==null_rank?active:0};}
            else {const auto right=bound_rank(input.right);
                if(left==null_rank || right==null_rank)result.unknown=active;
                else {const unsigned outcome=left<right?0:left==right?1:2;result.yes=active&input.accept[outcome];result.no=active&~input.accept[outcome];}}
        }
        if(!input.child){const auto absent=active&~input.present;result.yes|=absent;result.no&=input.present;result.unknown&=input.present;word_observe(input,active&input.present,result);}
        word_set_input(group,frame,i,result);++counters.request_decisions;
    }
}

Outcome word_summary(unsigned id,unsigned,unsigned long long live_value){
    const std::uint64_t live=live_value;auto &group=word_groups_[id];Outcome result;
    for(const auto &route:group.sorted_routes){const auto bit=std::uint64_t{1}<<route.member;if(!(live&bit))continue;
        const auto &member=group.members[route.member];const auto &p=sorted_plans_[route.plan];
        const auto rank=bound_rank(word_alias(member,p.source));if(rank==null_rank){result.D|=bit;continue;}
        const auto answer=answer_request(route.scope,rank,&member.aliases);if(!answer.D)continue;
        for(auto ref:scopes_[route.scope].refs)if(ref.occurrence!=p.local)word_point(word_alias(member,ref),bit);
        result.D|=bit;if(answer.H)result.H|=bit;
    }
    merged_seen_.clear();
    for(const auto &route:group.summary_routes){const auto bit=std::uint64_t{1}<<route.member;
        if(!(live&bit))continue;
        const auto &member=group.members[route.member];const auto &request=summary_requests_[route.scope];
        const auto &plan=summary_plans_[route.plan];
        if(plan.merged_index>=0){
            if(std::find(merged_seen_.begin(),merged_seen_.end(),route.plan)!=merged_seen_.end())continue;
            merged_seen_.push_back(route.plan);
            // One probe, fill, and vector pass for all live requests at
            // this entering rank. Different filled driver values are
            // separate arrivals, never silently combined into one slice.
            merged_pending_.clear();
            for(const auto&other:group.summary_routes)if(other.plan==route.plan&&(live&(std::uint64_t{1}<<other.member))){
                const auto &m=group.members[other.member];const auto &r=summary_requests_[other.scope];
                const auto source=word_alias(m,r.source);const auto rank=bound_rank(source);
                if(rank==null_rank){result.D|=std::uint64_t{1}<<other.member;continue;}
                merged_pending_.push_back({rank,other.scope,other.member,&m.aliases});
            }
            std::stable_sort(merged_pending_.begin(),merged_pending_.end(),[](const MergedPending&x,const MergedPending&y){return x.rank<y.rank;});
            for(std::size_t first=0;first<merged_pending_.size();){
                const auto rank=merged_pending_[first].rank;auto last=first;merged_members_.clear();
                while(last<merged_pending_.size()&&merged_pending_[last].rank==rank){merged_members_.push_back({merged_pending_[last].scope,merged_pending_[last].aliases});++last;}
                if(ensure_summary(merged_members_.front().scope,rank)){
                    invalidate_certificates();
                    const auto yes=answer_merged_frontier(plan,rank,merged_members_);
                    for(auto i=first;i<last;++i){const auto&e=merged_pending_[i];
                        const auto output=std::uint64_t{1}<<e.member;const auto&r=summary_requests_[e.scope];
                        const auto&m=group.members[e.member];
                        // Exact summaries cannot certify an enclosing varying
                        // window. Preserve the existing dependency observation.
                        for(auto ref:merged_outer_refs(e.scope))word_point(word_alias(m,ref),output);
                        result.D|=output;if(yes&(std::uint64_t{1}<<r.bit))result.H|=output;
                        ++counters.kept_hits;
                    }
                }
                first=last;
            }
            continue;
        }
        const auto source=word_alias(member,request.source);
        const auto rank=bound_rank(source);if(rank==null_rank)continue;
        const auto answer=answer_request(route.scope,rank,&member.aliases);if(!answer.D)continue;
        for(const auto &test:request.tests)if(!test.constant)word_point(word_alias(member,test.outer),bit);
        result.D|=bit;if(answer.H)result.H|=bit;
        ++counters.kept_hits;
    }
    return result;
}

// Compile remaining filled operands once. Prefix conjuncts which have already
// passed are guards, not part of Rest at this hop. No relation is read here.
std::vector<Ref> word_memo_refs(unsigned id,unsigned stage,const std::vector<int> &atoms)const{
    const auto &g=word_groups_[id];const auto &scope=scopes_[g.scope];
    const auto &member=g.members.front();const auto &driver=g.drivers[stage];
    std::set<Ref> result;
    if(g.positional){
        auto add=[&](Ref ref){auto pos=std::find(scope.locals.begin(),scope.locals.end(),ref.occurrence);
            if(pos!=scope.locals.end()&&unsigned(pos-scope.locals.begin())>=stage)return;
            if(ref.occurrence==driver.source.occurrence&&host_.unique(driver.source.column))return;result.insert(ref);};
        if(atoms.empty()){
            for(const auto &m:g.members){const auto &actual=scopes_[m.scope];
                for(auto atom_id:actual.used_atoms){const auto &a=atoms_[atom_id];auto old=actual.atom_slots.find(atom_id);
                    if(old!=actual.atom_slots.end()&&actual.requests[old->second].ready<=stage&&std::binary_search(actual.mandatory.begin(),actual.mandatory.end(),atom_id))continue;
                    auto ref=[&](Ref r){if(owned_inside(actual.expression,r.occurrence))return;auto alias=m.aliases.find(r.occurrence);if(alias==m.aliases.end())return;add({alias->second,r.column});};
                    if(!a.constant&&a.op==1){auto l=m.aliases.find(a.left.occurrence),r=m.aliases.find(a.right.occurrence);
                        if(l!=m.aliases.end()&&r!=m.aliases.end()){
                            Ref left{l->second,a.left.column},right{r->second,a.right.column};
                            if((left==Ref{scope.locals[stage],driver.column}&&right==driver.source)||(right==Ref{scope.locals[stage],driver.column}&&left==driver.source))continue;}}
                    ref(a.left);if(!a.constant)ref(a.right);
                }
            }
        }else for(int slot:atoms){const auto &input=g.inputs.at(slot);add(input.left);if(!input.constant)add(input.right);}
        return {result.begin(),result.end()};
    }

    auto before=[&](Ref ref){
        const auto pos=std::find(scope.locals.begin(),scope.locals.end(),ref.occurrence);
        if(pos!=scope.locals.end())return unsigned(pos-scope.locals.begin())<stage;
        return !owned_inside(scope.expression,ref.occurrence);
    };
    for(int atom_id:atoms){
        if(atom_id==driver.atom)continue;
        const auto slot=scope.atom_slots.find(atom_id);
        if(slot!=scope.atom_slots.end() && scope.requests[slot->second].ready<=stage &&
            std::binary_search(scope.mandatory.begin(),scope.mandatory.end(),atom_id))continue;
        const auto &a=atoms_[atom_id];
        auto add=[&](Ref ref){
            if(!before(ref))return;
            const auto mapped=word_alias(member,ref);
            // The pivot determines an equality-entered unique source row.
            if(mapped.occurrence==driver.source.occurrence && host_.unique(driver.source.column))return;
            result.insert(mapped);
        };
        add(a.left);if(!a.constant)add(a.right);
    }
    return {result.begin(),result.end()};
}
void configure_word_memos(){
    store_.word_budget_bytes=summary_budget_>summary_reserved_?summary_budget_-summary_reserved_:0;
    std::uint64_t reserved=0;
    for(unsigned id=0;id<word_groups_.size();++id){auto &g=word_groups_[id];const auto &scope=scopes_[g.scope];
        bool once_per_target=false;
        for(const auto &use:word_root_uses_)if(use.group==int(id))once_per_target=true;
        for(const auto &parent:word_groups_)for(const auto &input:parent.inputs)
            if(input.child&&input.child_group==id)once_per_target=false;
        g.memos.resize(scope.locals.size());
        for(unsigned stage=0;stage<scope.locals.size();++stage){auto &plan=g.memos[stage];const auto &driver=g.drivers[stage];
            std::vector<int> partial;
            if(g.positional){for(unsigned slot=0;slot<g.inputs.size();++slot){const auto &input=g.inputs[slot];
                if(input.ready<=stage)plan.prefix.push_back(slot);
                if(!input.child&&input.ready==stage+1){partial.push_back(slot);plan.partial_inputs.push_back(slot);}}}
            else for(auto atom_id:scope.mandatory){auto slot=scope.atom_slots.find(atom_id);if(slot==scope.atom_slots.end())continue;
                const auto ready=scope.requests[slot->second].ready;
                if(ready<=stage)plan.prefix.push_back(slot->second);
                if(ready==stage+1 && atom_id!=driver.atom){partial.push_back(atom_id);plan.partial_inputs.push_back(slot->second);}
            }
            auto register_cell=[&](WordMemoKey &key,std::vector<Ref> refs,bool boundary=false){
                // One entry per target, plus a target-unique filled rank,
                // proves that the union key cannot recur in this query.
                if(once_per_target)for(auto ref:refs)if(ref.occurrence==target_&&host_.unique(ref.column)){
                    key.never_repeats=true;
                    // A boundary drops this filled value from the lookup key.
                    // Its certificate can repeat even when exact cells cannot.
                    if(!boundary || refs.size()!=1)return;
                }
                if(refs.size()>RankPredicateInstance::max_operands){++counters.outer_dependency_declines;return;}
                const auto base=next_predicate_++;key.predicate=base|(unsigned(refs.size())<<RankPredicateInstance::arity_shift);key.filled=std::move(refs);
                const auto bytes=std::uint64_t(host_.ranks(driver.column))*16;
                bool dense=key.filled.empty() && host_.allow_dense(driver.column) && bytes<=store_.word_budget_bytes && reserved<=store_.word_budget_bytes-bytes;
                if(dense)reserved+=bytes;
                store_.register_word(key.predicate,host_.ranks(driver.column),!dense);
                const auto expected=summary_arrival_estimate(g.scope);
                store_.configure_word_tablewide(key.predicate,present_count(host_,driver.column,0),std::uint64_t(std::min(expected,1e18)));
                registered_.insert(key.predicate);predicate_info_[base]={driver.column,key.filled};
            };
            // The pre-existing one-row existence cell already IS the whole
            // Rest for this degenerate one-input scope; do not duplicate it.
            if(!(driver.presence_predicate && scope.locals.size()==1 && g.inputs.size()==1))
                register_cell(plan.full,word_memo_refs(id,stage,g.positional?std::vector<int>{}:std::vector<int>{scope.used_atoms.begin(),scope.used_atoms.end()}),envelopes_);
            if(!partial.empty()){
                auto refs=word_memo_refs(id,stage,partial);
                if(!plan.full.predicate || refs!=plan.full.filled)register_cell(plan.partial,std::move(refs));
            }
            once_per_target=once_per_target&&host_.unique(driver.column);
        }
    }
}
bool word_instance(const WordMemoKey &key,RankPredicateInstance &instance,bool boundary=false){
    if((key.never_repeats&&!boundary) || !key.predicate || !store_.enabled(key.predicate))return false;
    if(key.probes>=65536&&key.hits*64<key.probes)return false; // measured: this key does not repeat
    return PackedRankDecisionStore::Key(key.predicate,key.filled.size(),[&](unsigned i,unsigned &value){const auto ref=key.filled[i];
        const auto &boundary=boundary_bindings_[ref.occurrence];
        if(boundary.bank>=0 && ref.column!=boundary.column){++counters.outer_dependency_declines;return false;}
        value=bound_rank(ref);return true;
    },instance);
}
void word_partial_row(unsigned id,const WordStageMemo &plan,const WordFrame &frame,std::uint64_t live,std::uint64_t &all_failed){
    if(!plan.partial.predicate)return;
    std::uint64_t failed=0;for(auto input:plan.partial_inputs){const auto value=word_input(word_groups_[id],frame,input);failed|=value.no|value.unknown;}
    all_failed&=failed|~live;
}
PackedRankDecisionStore::Word word_probe(unsigned id,unsigned stage,unsigned pivot,const RankPredicateInstance &key,
    std::uint64_t live,bool partial){
    const auto &key_plan=partial?word_groups_[id].memos[stage].partial:word_groups_[id].memos[stage].full;
    auto &work=word_groups_[id].work[stage];++counters.exact_probes;
    const bool dense=store_.word_dense(key.id);
    if(dense){++counters.dense_probes;CF_COUNT(++work.dense_probes);}else{++counters.packed_probes;CF_COUNT(++work.packed_probes);}
    ++counters.word_hop_probes;CF_COUNT(++work.word_hop_probes);
    if(partial){++counters.partial_nogood_probes;CF_COUNT(++work.partial_nogood_probes);}
    auto value=store_.lookup_word(pivot,key,live,std::max<std::uint64_t>(1,skipped_slice(host_,word_groups_[id].drivers[stage].column,pivot,0)));
    ++key_plan.probes;if(value.good|value.nogood)++key_plan.hits;
    if(value.good|value.nogood)for(auto ref:key_plan.filled)word_point(ref,value.good|value.nogood);
    if(value.good|value.nogood){++counters.exact_hits;++counters.kept_hits;++counters.word_hop_hits;
        CF_COUNT(++work.word_hop_hits);
        if(dense){++counters.dense_hits;CF_COUNT(++work.dense_hits);}else{++counters.packed_hits;CF_COUNT(++work.packed_hits);}
        if(partial){++counters.partial_nogood_hits;CF_COUNT(++work.partial_nogood_hits);}
        const auto bits=__builtin_popcountll(value.good|value.nogood);counters.bits_settled_without_read+=bits;
        CF_COUNT(work.bits_settled_without_read+=bits);
    }
    return value;
}
void word_store(unsigned id,unsigned stage,unsigned pivot,const RankPredicateInstance &key,std::uint64_t good,std::uint64_t nogood,bool partial){
    bool written=false;
    if(!store_.insert_word(pivot,key,good,nogood,written))throw std::logic_error("nested word decision flipped");
    if(!written)return;auto &work=word_groups_[id].work[stage];++counters.exact_fills;++counters.word_hop_fills;
    CF_COUNT(++work.word_hop_fills);
    if(store_.word_dense(key.id)){++counters.dense_fills;CF_COUNT(++work.dense_fills);}else{++counters.packed_fills;CF_COUNT(++work.packed_fills);}
    if(partial){++counters.partial_nogood_fills;CF_COUNT(++work.partial_nogood_fills);}
}
std::uint64_t word_walk(unsigned id,unsigned stage,WordFrame &frame,std::uint64_t live,unsigned depth){
    auto &group=word_groups_[id];const auto &scope=scopes_[group.scope];
    const auto value=word_formula(group,frame,live);live&=~(value.no|value.unknown);
    if(!live)return 0;
    if(stage==scope.locals.size()){
        if(live&~value.yes){std::string detail="shared request reached end with an unbound operand: group="+std::to_string(id)+" scope="+std::to_string(group.scope)+" live="+std::to_string(live)+" yes="+std::to_string(value.yes)+" inputs=";
            for(unsigned i=0;i<group.inputs.size();++i)if((live&~value.yes)&~(word_input(group,frame,i).yes|word_input(group,frame,i).no|word_input(group,frame,i).unknown))detail+=std::to_string(i)+"@"+std::to_string(group.inputs[i].ready)+":"+std::to_string(group.inputs[i].present)+",";throw std::logic_error(detail);}return value.yes&live;}
    const auto &plan=group.memos[stage];
    for(auto slot:plan.prefix){const auto prefix=word_input(group,frame,slot);
        if(live&~(prefix.yes|prefix.no|prefix.unknown))throw std::logic_error("shared mandatory prefix was not settled");
        live&=prefix.yes;
    }
    if(!live)return 0;
    const auto &driver=group.drivers[stage];const auto pivot=bound_rank(driver.source);
    auto &work=group.work[stage];reached(work,driver.column,pivot);if(pivot==null_rank)return 0;
    word_point(driver.source,live);
    std::uint64_t summary_good=0;
    if(!stage){const auto cached=word_summary(id,pivot,live);summary_good=cached.H;live&=~cached.D;
        if(summary_good)word_found(id,summary_good);
        if(!live||word_root_finished_)return summary_good;}
    RankPredicateInstance exact,partial;
    const bool boundary_candidate=envelopes_&&plan.full.filled.size()==1&&bound_rank(plan.full.filled.front())!=null_rank;
    const bool memo=word_instance(plan.full,exact,boundary_candidate),small=word_instance(plan.partial,partial);
    std::uint64_t good=0;
    const bool range=boundary_candidate&&memo;
    if(range){
        ++counters.word_envelope_probes;CF_COUNT(++work.boundary_probes);
        auto known=store_.word_envelopes.probe(exact.id,pivot,bound_rank(plan.full.filled.front()));
        known.good&=live;known.nogood&=live;
        store_.observe_range(exact.id,(known.good|known.nogood)!=0,1);
        if(known.good|known.nogood){++counters.word_envelope_hits;CF_COUNT(++work.boundary_hits);counters.bits_settled_without_read+=__builtin_popcountll(known.good|known.nogood);CF_COUNT(work.bits_settled_without_read+=__builtin_popcountll(known.good|known.nogood));}
        // Do not widen an enclosing proof from an unprojected child proof.
        if(known.good|known.nogood)word_point(plan.full.filled.front(),known.good|known.nogood);
        good=known.good;live&=~(known.good|known.nogood);
    }
    if(memo&&!range){const auto known=word_probe(id,stage,pivot,exact,live,false);good=known.good;live&=~(known.good|known.nogood);}
    if(small && live){const auto known=word_probe(id,stage,pivot,partial,live,true);
        if(known.good)throw std::logic_error("partial cell contained a good decision");live&=~known.nogood;}
    if(good)word_found(id,good);
    if(!live || word_root_finished_){
        CF_COUNT(const auto skipped=skipped_slice(host_,driver.column,pivot,0);counters.rows_skipped+=skipped;work.rows_skipped+=skipped;);
        return summary_good|good;
    }
    WordCertificate certificate;
    if(range){certificate.probe=plan.full.filled.front();certificate.domain=host_.ranks(certificate.probe.column);certificate.region.reset(certificate.domain);
        certificate.region.pieces.front().mask=live;for(unsigned b=0;b<64;++b)certificate.mapping[b]=1ULL<<b;word_certificates_.push_back(&certificate);
        if(certificate.probe==driver.source)word_point(driver.source,live);}
    const auto reads_before=counters.witness_rows;
    auto failed=live;const auto walked=word_walk_uncached(id,stage,frame,live,depth,pivot,failed);
    if(memo)store_.record_word_miss(exact.id,counters.witness_rows-reads_before);
    if(range)word_certificates_.pop_back();
    // A root-decided early stop is NOT exhaustion for other request bits.
    // Keep proven witnesses, but never turn their unvisited tails into nogoods.
    const auto nogood=word_root_finished_?0:live&~walked;
    if(range&&store_.enabled(exact.id)){
        const auto budget=store_.word_budget_bytes>store_.word_bytes?store_.word_budget_bytes-store_.word_bytes:0;
        if(store_.word_envelopes.put(exact.id,pivot,host_.ranks(driver.column),certificate.domain,certificate.region,walked,nogood,budget)){
            ++counters.word_envelope_fills;CF_COUNT(++work.boundary_fills);}
    }else if(memo&&!range)word_store(id,stage,pivot,exact,walked,nogood,false);
    if(small && nogood)word_store(id,stage,pivot,partial,0,nogood&failed,true);
    return summary_good|good|walked;
}

std::uint64_t word_walk_uncached(unsigned id,unsigned stage,WordFrame &frame,std::uint64_t live,unsigned depth,
    unsigned pivot,std::uint64_t &partial_failed){
    auto &group=word_groups_[id];const auto &scope=scopes_[group.scope];
    const auto driver=group.drivers[stage];auto &work=group.work[stage];
    const int occurrence=scope.locals[stage];const int boundary=group.boundary_choices[stage];

    if(driver.presence_predicate){
        RankPredicateInstance instance;instance.id=driver.presence_predicate;bool present=false;
        ++counters.exact_probes;++counters.dense_probes;CF_COUNT(++work.dense_probes);
        if(store_.lookup(pivot,instance,&present)){++counters.exact_hits;++counters.dense_hits;CF_COUNT(++work.dense_hits);}
        else {
            host_.visit(driver.column,1,pivot,[&](unsigned){present=true;++counters.witness_rows;++counters.tight_slice_rows;CF_COUNT(++work.witness_rows);return true;});
            if(store_.enabled(instance.id)){store_.insert(pivot,instance,present);++counters.exact_fills;++counters.dense_fills;CF_COUNT(++work.dense_fills);}
        }
        if(!present)return 0;
        // This is the current equality assignment, not a cached row value.
        // Planning proved that the rest reads no other column of this row.
        bindings_[occurrence]=0;rank_bindings_[occurrence]={driver.column,pivot,true};
        auto &child=group.frames[stage+1];word_inherit(group,child,frame);
        word_ready(id,stage+1,child,live,depth);
        word_partial_row(id,group.memos[stage],child,live,partial_failed);const auto answer=word_walk(id,stage+1,child,live,depth);
        bindings_[occurrence]=-1;rank_bindings_[occurrence]={};return answer;
    }
    if(boundary>=0){auto &bank=store_.summaries[boundary];auto slot=PackedRankDecisionStore::Probe(bank,pivot,summary_epoch_);
        const bool known=slot;bool present=slot&&slot->count;rank_theta::Boundary transient;
        CF_COUNT(++work.boundary_probes;if(known)++work.boundary_hits);
        if(!known){unsigned parameter=null_rank;
            host_.visit(bank.column,1,pivot,[&](unsigned row){++counters.witness_rows;++counters.tight_slice_rows;CF_COUNT(++work.witness_rows);
                present=true;parameter=host_.rank(bank.parameter_column,row);return true;});
            transient=rank_theta::transfer(parameter,1,bank.parameter_domain);
            if(PackedRankDecisionStore::Record(bank,pivot,transient,present))CF_COUNT(++work.boundary_fills);
            slot=bank.view.probe(pivot);}
        if(!present)return 0;
        bindings_[occurrence]=0;boundary_bindings_[occurrence]={boundary,pivot,bank.column,bank.parameter_column,slot?nullptr:&transient};
        auto &child=group.frames[stage+1];word_inherit(group,child,frame);
        word_ready(id,stage+1,child,live,depth);
        word_partial_row(id,group.memos[stage],child,live,partial_failed);const auto answer=word_walk(id,stage+1,child,live,depth);
        bindings_[occurrence]=-1;boundary_bindings_[occurrence]={};return answer;
    }
    std::uint64_t good=0;
    host_.visit(driver.column,1,pivot,[&](unsigned row){
        const auto active=live&~good;if(!active)throw std::logic_error("shared iterator read after all requests decided");
        ++counters.witness_rows;++counters.tight_slice_rows;CF_COUNT(++work.witness_rows);
        bindings_[occurrence]=row;auto &child=group.frames[stage+1];word_inherit(group,child,frame);
        word_ready(id,stage+1,child,active,depth);
        word_partial_row(id,group.memos[stage],child,active,partial_failed);good|=word_walk(id,stage+1,child,active,depth);
        bindings_[occurrence]=-1;word_found(id,good);return word_root_finished_ || (good&live)==live;
    });
    if(host_.unique(driver.column))++counters.unique_hops;
    if(good)++counters.first_witness_stops;if(good!=live)++counters.exhaustions;return good;
}

void word_found(unsigned id,std::uint64_t good){
    if(int(id)!=word_observer_group_ || !good)return;
    // Only complete witnesses from the root use's OWN scope are reported.
    // An inner EXISTS result is not an outer witness until its parent's
    // remaining conjuncts and quantified locals have passed.
    word_observer_good_|=good;const auto proven=word_observer_use_->up(word_observer_good_);
    const auto root=word_root_state(word_observer_D_|proven,word_observer_H_|proven,word_observer_U_);
    if(root.first || !root.second){word_root_finished_=true;word_root_answer_=root.first;}
}

std::uint64_t word_quantify(unsigned id,std::uint64_t live,unsigned depth){
    if(!live)return 0;host_.interrupt();++counters.quantifier_calls;counters.maximum_depth=std::max(counters.maximum_depth,depth);
    auto &group=word_groups_[id];auto &frame=group.frames.front();
    if(group.positional){frame.failed=0;frame.unknown_inputs=0;frame.pending=group.initial_pending;}
    else std::fill(frame.inputs.begin(),frame.inputs.end(),WordValue{});
    word_ready(id,0,frame,live,depth);return word_walk(id,0,frame,live,depth);
}

std::pair<bool,std::uint64_t> word_root_state(std::uint64_t D,std::uint64_t H,std::uint64_t U)const{
    std::uint64_t needed=0;
    for(const auto term:word_root_terms_){
        if(((D&~H)|U)&term.positive || (H|U)&term.negative)continue;
        const auto wants=term.positive|term.negative;
        if((D&wants)==wants)return {true,0};needed|=wants&~D;
    }
    return {false,needed};
}

bool word_evaluate(){
    std::uint64_t D=0,H=0,U=0;word_root_finished_=false;word_observer_group_=-1;
    for(const auto &use:word_root_uses_){const auto state=word_root_state(D,H,U);
        if(state.first || !state.second)return state.first;
        const auto slots=state.second&use.slots;if(!slots)continue;
        if(use.group>=0){word_observer_group_=use.group;word_observer_use_=&use;
            word_observer_D_=D;word_observer_H_=H;word_observer_U_=U;word_observer_good_=0;
            const auto result=word_quantify(use.group,use.down(slots),1);word_observer_group_=-1;
            if(word_root_finished_)return word_root_answer_;
            H|=use.up(result)&slots;D|=slots;
        }else {const auto value=atom(use.atom);D|=slots;
            if(value==Truth::yes)H|=slots;else if(value==Truth::unknown)U|=slots;
            else if(value==Truth::pending)throw std::logic_error("root request has unbound target operand");}
    }
    const auto result=word_root_state(D,H,U);if(result.second)throw std::logic_error("root request word left undecided");
    return result.first;
}
