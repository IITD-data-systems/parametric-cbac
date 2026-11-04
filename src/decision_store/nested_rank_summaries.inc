// Included in Executor's private section. Scope-preserving summaries, not an
// alternative policy walker: only the complete functional witness below one
// equality-entered rank is collected. Everything else keeps A+B's executor.
struct SummaryTest {int atom=-1;Ref local,outer;bool constant=false;int op=1;};
struct SummaryStep {
    int occurrence=-1;unsigned column=0;Ref source;bool root=false;
    unsigned scope=0,stage=0;std::vector<int> guards;
};
struct SummaryInstruction {Kind kind=Kind::no;int atom=-1;unsigned a=0,b=0,scope=UINT32_MAX;std::uint64_t locals=0;};
struct SummarySymbol {rank_summaries::Bits yes,no;};
struct CollectiveChild {
    unsigned scope=0,plan=0;collective_fill::Remap remap;
    std::array<Ref,2> operands{};unsigned variable_mask=0;
    std::array<int,2> inputs{-1,-1};
};
struct CollectiveInstruction {int left=-1,right=-1,test=-1,child=-1,literal=-1;};
struct CollectiveScratch {
    std::vector<unsigned> ranks,cuts;
    std::vector<collective_fill::Truth> values,tests;
    std::vector<rank_requests::MaskedRange> row;
    collective_fill::Union result;
};
struct SummaryPlan {
    unsigned scope=0,column=0,bank=0;int driver=-1;
    int merged_index=-1;
    std::map<int,unsigned> locals;
    std::vector<SummaryStep> steps;
    std::vector<SummaryTest> tests;
    unsigned raw_tests=0,folded_constants=0;
    std::vector<unsigned> planned_operators;
    std::map<int,unsigned> test_by_atom;
    std::vector<SummaryInstruction> program;
    std::vector<SummarySymbol> symbols;
    rank_summaries::Bits all;
    std::string signature;
    std::vector<unsigned> requests;
    int filled_test=-1;
    std::vector<unsigned> filled_tests;
    bool theta=false;
    bool point_mode=false;
    std::string decline;
    bool range_program=false;
    std::vector<Ref> rank_inputs;
    std::vector<int> test_inputs;
    std::vector<collective_fill::Constants> constants;
    std::vector<std::array<std::uint64_t,3>> filled_accept;
    std::vector<CollectiveInstruction> collective_program;
    std::vector<CollectiveChild> collective_children;
    std::vector<unsigned> folded_literals;
    mutable std::map<std::pair<std::array<std::uint64_t,rank_summaries::state_words>,unsigned>,rank_summaries::Bits> bound_literal_tables;
    mutable CollectiveScratch scratch;
    mutable std::vector<NodeWork> work;
};
struct SummaryRequest {int plan=-1;std::vector<SummaryTest> tests;unsigned bit=0;
    std::map<unsigned,unsigned> child_scopes;std::map<int,int> aliases;Ref source;unsigned column=UINT32_MAX;};
std::vector<SummaryPlan> summary_plans_;
std::vector<SummaryRequest> summary_requests_;
std::vector<std::string> summary_ineligible_;
std::vector<unsigned> summary_entered_,summary_test_counts_;
unsigned summary_mode_=0;bool summary_cost_guard_=true;
std::uint64_t summary_budget_=0,summary_reserved_=0,summary_epoch_=0;

bool summary_steps(unsigned scope,SummaryPlan &plan,std::set<int> &bound,
                   std::vector<int> ancestors,bool root_scope){
    const auto &s=scopes_[scope];
    auto guards=ancestors;guards.insert(guards.end(),s.mandatory.begin(),s.mandatory.end());
    for(unsigned stage=0;stage<s.locals.size();++stage){
        const int occurrence=s.locals[stage];SummaryStep step;
        step.occurrence=occurrence;step.scope=scope;step.stage=stage;step.guards=guards;
        const bool first=root_scope && stage==0;
        bool driver=false;
        auto drivers=ranked_equalities(s,occurrence);
        // The common join is also the summary's entry. A per-request '='
        // remains a test, so summaries cannot silently change their rank.
        const int preferred=word_preferred_atom(scope,stage);
        if(preferred>=0)std::stable_sort(drivers.begin(),drivers.end(),[&](int a,int b){return (a==preferred)>(b==preferred);});
        for(int id:drivers){const auto &a=atoms_[id];if(a.constant || a.op!=1)continue;
            Ref candidate,source;
            if(a.left.occurrence==occurrence){candidate=a.left;source=a.right;}
            else if(a.right.occurrence==occurrence){candidate=a.right;source=a.left;}
            else continue;
            if(first && (std::find(s.locals.begin(),s.locals.end(),source.occurrence)!=s.locals.end() ||
                         owned_inside(s.expression,source.occurrence)))continue;
            if(first?bound.count(source.occurrence)!=0:bound.count(source.occurrence)==0)continue;
            if(!first && !host_.unique(candidate.column))continue;
            step.column=candidate.column;step.source=source;step.root=first;driver=true;
            if(first){plan.driver=id;plan.column=candidate.column;}
            break;
        }
        if(!driver || plan.locals.size()>=63 || plan.locals.count(occurrence)){
            plan.decline=!driver?(first?"no mandatory equality from the bound outer scope":"non-functional or unavailable descendant equality"):
                plan.locals.size()>=63?"more than63 local occurrences":"repeated local occurrence";
            plan.decline+=" at occurrence "+std::to_string(occurrence);return false;
        }
        plan.locals[occurrence]=plan.locals.size();bound.insert(occurrence);plan.steps.push_back(std::move(step));
    }
    std::function<bool(int)> descend=[&](int expression){
        const auto &e=expressions_[expression];
        if(e.kind==Kind::exists){auto child_bound=bound;
            return summary_steps(scope_by_expr_.at(expression),plan,child_bound,guards,false);}
        return (e.left<0 || descend(e.left)) && (e.right<0 || descend(e.right));
    };
    return descend(s.expression);
}

std::string summary_ref(const SummaryPlan &p,Ref r)const{
    const auto it=p.locals.find(r.occurrence);
    return (it==p.locals.end()?"outside:":"local:"+std::to_string(it->second)+":")+std::to_string(r.column);
}
bool summary_program(int expression,SummaryPlan &p,unsigned &output){
    const auto &e=expressions_[expression];SummaryInstruction instruction;instruction.kind=e.kind;
    if(e.kind==Kind::atom){
        instruction.atom=e.value;const auto &a=atoms_[e.value];
        if(e.value==p.driver){p.signature+="driver;";}
        else {
            const bool l=p.locals.count(a.left.occurrence),r=!a.constant && p.locals.count(a.right.occurrence);
            if(!l && !r){p.decline="outside-only atom "+std::to_string(e.value)+" is not a witness test";return false;}
            if(a.constant || !l || !r){
                SummaryTest test;test.atom=e.value;test.constant=a.constant;
                test.local=l?a.left:a.right;test.outer=l?a.right:a.left;test.op=l?a.op:inverse(a.op);
                // Once filled, an outside column is a parameter slot, not
                // the path/outer column that happened to supply its value.
                p.signature+="test("+summary_ref(p,test.local)+","+
                    (test.constant?"literal-slot":"filled-rank-slot")+");";
                p.test_by_atom[e.value]=p.tests.size();p.tests.push_back(test);
            }else p.signature+="atom("+summary_ref(p,a.left)+","+std::to_string(a.op)+","+summary_ref(p,a.right)+");";
        }
    }else {
        if(e.left>=0 && !summary_program(e.left,p,instruction.a))return false;
        if(e.right>=0 && !summary_program(e.right,p,instruction.b))return false;
        if(e.kind==Kind::exists)for(int local:e.locals){
            instruction.scope=scope_by_expr_.at(expression);
            auto found=p.locals.find(local);if(found==p.locals.end())return false;
            instruction.locals|=std::uint64_t{1}<<found->second;
        }
        p.signature+="kind"+std::to_string(int(e.kind))+"["+std::to_string(instruction.locals)+"];";
    }
    output=p.program.size();p.program.push_back(instruction);return true;
}

// Only a write-admission proof: do not infer that any other column of a
// unique row is unique. A shared foreign-key output remains reusable.
bool summary_driver_is_target_unique(unsigned scope,Ref source)const{
    std::vector<unsigned> ancestors,path;
    std::function<bool(int)> find=[&](int id){
        const auto&e=expressions_[id];
        if(e.kind==Kind::exists){const auto child=unsigned(scope_by_expr_.at(id));
            if(child==scope){ancestors=path;return true;}
            path.push_back(child);const bool found=find(e.left);path.pop_back();return found;
        }
        return (e.left>=0&&find(e.left))||(e.right>=0&&find(e.right));
    };
    if(!find(scopes_.back().expression))return false;
    std::set<int> bound{target_};std::set<Ref> refs,unique_values;
    for(auto parent:ancestors)for(auto occurrence:scopes_[parent].locals)bound.insert(occurrence);
    for(const auto&a:atoms_){if(bound.count(a.left.occurrence))refs.insert(a.left);
        if(!a.constant&&bound.count(a.right.occurrence))refs.insert(a.right);}
    for(auto ref:refs)if(ref.occurrence==target_&&host_.unique(ref.column))unique_values.insert(ref);
    bool changed=true;
    while(changed){changed=false;
        for(auto parent:ancestors)for(auto id:scopes_[parent].mandatory){const auto&a=atoms_[id];
            if(a.constant||a.op!=1||!bound.count(a.left.occurrence)||!bound.count(a.right.occurrence))continue;
            if(unique_values.count(a.left))changed|=unique_values.insert(a.right).second;
            if(unique_values.count(a.right))changed|=unique_values.insert(a.left).second;
        }
        std::vector<Ref> known(unique_values.begin(),unique_values.end());
        for(auto key:known)if(host_.unique(key.column))for(auto ref:refs)
            if(ref.occurrence==key.occurrence&&host_.unique(ref.column))changed|=unique_values.insert(ref).second;
    }
    return unique_values.count(source)!=0;
}

// Metadata estimates, never policy-side rows or extra artifacts.
double summary_arrival_estimate(unsigned wanted)const{
    std::vector<unsigned>path,ancestors;std::function<bool(int)>find=[&](int id){const auto&e=expressions_[id];
        if(e.kind==Kind::exists){auto scope=unsigned(scope_by_expr_.at(id));if(scope==wanted){ancestors=path;return true;}
            path.push_back(scope);bool found=find(e.left);path.pop_back();return found;}
        return(e.left>=0&&find(e.left))||(e.right>=0&&find(e.right));};find(scopes_.back().expression);
    double arrivals=host_.rows(occurrence_columns_.at(target_));std::set<int>bound{target_};
    for(auto parent:ancestors)for(auto local:scopes_[parent].locals){
        for(auto id:scopes_[parent].mandatory){const auto&a=atoms_[id];if(a.constant||a.op!=1)continue;Ref entry,source;
            if(a.left.occurrence==local){entry=a.left;source=a.right;}else if(a.right.occurrence==local){entry=a.right;source=a.left;}else continue;
            if(!bound.count(source.occurrence))continue;
            arrivals*=std::max(1.,double(host_.rows(entry.column))/std::max<std::uint64_t>(1,present_count(host_,entry.column,0)));break;
        }bound.insert(local);
    }return std::min(arrivals,1e18);
}
rank_frontier_admission::Estimate frontier_estimate(unsigned scope,const SummaryPlan&p)const{
    const auto present=std::max<std::uint64_t>(1,present_count(host_,p.column,0));
    const double rows=double(host_.rows(p.column))/present;double product=1;std::set<unsigned>columns;
    for(const auto&t:p.tests)columns.insert(t.local.column);
    for(auto c:columns){product*=std::max<std::uint64_t>(1,present_count(host_,c,0));if(product>=rows){product=rows;break;}}
    return rank_frontier_admission::estimate(rows,std::min(rows,product),p.steps.size(),summary_arrival_estimate(scope)/present);
}

void configure_summaries(){
    sorted_requests_.assign(scopes_.size(),-1);sorted_reasons_.assign(scopes_.size(),"not considered");
    summary_requests_.resize(scopes_.size());summary_ineligible_.assign(scopes_.size(),"target/root scope without an entering rank");
    summary_entered_.assign(scopes_.size(),UINT32_MAX);summary_test_counts_.resize(scopes_.size());
    if(!decisions_||!summary_mode_){std::fill(summary_ineligible_.begin(),summary_ineligible_.end(),"summary setting disabled");return;}
    configure_merged_frontiers();
    std::vector<SummaryPlan> drafts;
    std::map<std::string,std::vector<unsigned>> groups;
    for(unsigned scope=0;scope+1<scopes_.size();++scope){
        if(summary_requests_[scope].plan>=0)continue; // conjunctive merged bank
        if(word_graph_ready_ && word_scope_group_[scope]<0){summary_ineligible_[scope]="scope not routed through shared word graph";continue;}
        if(scopes_[scope].locals.empty()){summary_ineligible_[scope]="zero-local formula wrapper";continue;}
        // A heterogeneous positional group has ONE union Rest, not several
        // member banks. Its stage plan uses the3A dense/packed words and3B
        // complete-Rest boundary bank. Do not allocate/reserve old per-member
        // summaries which cannot represent missing inputs/private children.
        // Each request compiles its own exact Rest, including private children.
        if(configure_sorted(scope))continue;
        SummaryPlan plan;plan.scope=scope;std::set<int> bound;
        if(!summary_steps(scope,plan,bound,{},true)){summary_ineligible_[scope]=plan.decline;continue;}
        summary_entered_[scope]=plan.column;
        const bool unique=host_.unique(plan.column);
        if(summary_driver_is_target_unique(scope,plan.steps.front().source)){
            summary_ineligible_[scope]="target-unique driver through mandatory key equalities/unique hops: no cross-target rank reuse";continue;
        }
        if(unique?!(summary_mode_&2):!(summary_mode_&1)){summary_ineligible_[scope]="summary mode excludes this entry kind";continue;}
        plan.signature="entered:"+std::to_string(plan.column)+";";
        unsigned unused=0;if(!summary_program(scopes_[scope].expression,plan,unused)){summary_ineligible_[scope]=plan.decline;summary_test_counts_[scope]=plan.tests.size();continue;}
        summary_test_counts_[scope]=plan.tests.size();
        // With no variable test this is already a two-bit predicate. Do not
        // replace A+B's compact verdict with a larger zero-dimensional point.
        if(plan.tests.empty()){summary_ineligible_[scope]="no parametric tests; ordinary two-bit decision";continue;}
        if(summary_mode_&8){
            unsigned filled=0;
            for(unsigned d=0;d<plan.tests.size();++d)if(!plan.tests[d].constant){
                plan.filled_test=d;plan.filled_tests.push_back(d);++filled;}
            // One varying filled operand is the paper's boundary form. More
            // operands retain A+B's dense/packed exact decisions; no points.
            plan.theta=(summary_mode_&16) && unique && filled>0 && filled<=2;
            bool same_value=true;
            for(auto d:plan.filled_tests)if(!(plan.tests[d].outer==plan.tests[plan.filled_tests.front()].outer))same_value=false;
            plan.range_program=!plan.theta && filled>1 && same_value;
            plan.point_mode=!unique && filled>=2 && !plan.range_program;
            if(filled>1 && !plan.theta && !plan.range_program && !plan.point_mode){summary_ineligible_[scope]="unsupported multiple filled operands at a unique rank";continue;}
        }
        plan.raw_tests=plan.tests.size();
        plan.signature+="form:"+std::to_string(plan.theta)+":"+std::to_string(plan.point_mode)+":"+std::to_string(plan.range_program)+";";
        // Implicit outer EXISTS: all its locals must stand for actual rows.
        SummaryInstruction outer;outer.kind=Kind::exists;outer.a=unused;
        for(int local:scopes_[scope].locals)outer.locals|=std::uint64_t{1}<<plan.locals.at(local);
        plan.program.push_back(outer);
        const unsigned id=drafts.size();groups[plan.signature].push_back(id);drafts.push_back(std::move(plan));
    }
    // Operators and bound constants are known at planning. A literal folds
    // only if every request in this <=64-request bank binds it identically.
    for(const auto&group:groups)for(unsigned begin=0;begin<group.second.size();begin+=64){
        const unsigned end=std::min<unsigned>(group.second.size(),begin+64);
        const auto&base=drafts[group.second[begin]];std::vector<bool> fold(base.tests.size());
        std::vector<unsigned> ops(base.tests.size());
        for(unsigned d=0;d<base.tests.size();++d){fold[d]=base.tests[d].constant;const auto&a=atoms_[base.tests[d].atom];
            for(unsigned i=begin;i<end;++i){const auto&p=drafts[group.second[i]];
                if(p.tests.size()!=base.tests.size())throw std::logic_error("summary template test positions changed");
                const auto&test=p.tests[d];const auto&b=atoms_[test.atom];ops[d]|=1U<<test.op;
                fold[d]=fold[d]&&test.constant&&a.op==b.op&&a.lower==b.lower&&a.upper==b.upper;
            }
        }
        for(unsigned i=begin;i<end;++i){auto&p=drafts[group.second[i]];auto raw=std::move(p.tests);p.tests.clear();p.test_by_atom.clear();
            p.filled_test=-1;p.filled_tests.clear();
            for(unsigned d=0;d<raw.size();++d)if(!fold[d]){
                p.test_by_atom[raw[d].atom]=p.tests.size();
                if(!raw[d].constant){p.filled_test=p.tests.size();p.filled_tests.push_back(p.tests.size());}
                p.tests.push_back(raw[d]);p.planned_operators.push_back(ops[d]);
            }
            p.folded_constants=p.raw_tests-p.tests.size();p.signature+="bank:"+std::to_string(begin)+";";
        }
    }
    std::map<std::string,unsigned> shared;
    for(auto &draft:drafts){SummaryPlan plan=std::move(draft);const unsigned scope=plan.scope;const bool unique=host_.unique(plan.column);
        summary_test_counts_[scope]=plan.tests.size();
        if(plan.tests.size()>rank_summaries::max_tests){summary_ineligible_[scope]="more than6 parametric tests after folding "+std::to_string(plan.folded_constants)+" common literals from "+std::to_string(plan.raw_tests)+" raw tests";continue;}
        // Retain the existing A word when all raw tests fold away.
        const bool frontier=!(summary_mode_&8)||plan.point_mode;
        const auto present=std::uint64_t(present_count(host_,plan.column,0));
        const auto rows=std::uint64_t(host_.rows(plan.column));
        rank_frontier_admission::Estimate estimate; // no plan-time no-dominance estimate
        estimate.rows=double(rows)/std::max<std::uint64_t>(1,present);
        auto found=shared.find(plan.signature);
        if(found!=shared.end()){
            auto &canonical=summary_plans_[found->second];
            std::uint64_t extra_bytes=0;
            if(canonical.theta){const auto &operators=store_.summaries[canonical.bank].operators;
                for(auto d:canonical.filled_tests)if(!(operators[d]&(1U<<plan.tests[d].op)))
                    extra_bytes+=std::uint64_t(host_.ranks(plan.column))*sizeof(rank_theta::Boundary);
            }
            if(canonical.requests.size()<64 && extra_bytes<=summary_budget_ &&
               summary_reserved_<=summary_budget_-extra_bytes){
                summary_reserved_+=extra_bytes;store_.summaries[canonical.bank].reserved_bytes+=extra_bytes;
                summary_requests_[scope]={int(found->second),plan.tests,unsigned(canonical.requests.size())};
                for(unsigned d=0;d<plan.tests.size();++d)
                    store_.summaries[canonical.bank].operators[d]|=1U<<plan.tests[d].op;
                summary_requests_[scope].source=plan.steps.front().source;summary_requests_[scope].column=plan.column;
                summary_ineligible_[scope].clear();canonical.requests.push_back(scope);continue;
            }
        }
        // Only reserve a plan's byte budget here. Rank arrays and witnesses
        // are NOT allocated/filled until an actual target reaches the rank.
        std::uint64_t bytes=std::uint64_t(host_.ranks(plan.column))*(sizeof(rank_summaries::Slot)+
            ((summary_mode_&8)&&!plan.point_mode?(plan.theta?sizeof(rank_theta::Cell):plan.filled_test<0?8:sizeof(rank_requests::Cell)):0))+
            ((summary_mode_&8)&&!plan.point_mode?0:((frontier&&!unique&&summary_cost_guard_)?rank_summaries::Summary::frontier_point_capacity(host_.rows(plan.column)):std::uint64_t(host_.rows(plan.column)))*sizeof(rank_summaries::Point));
        if(plan.theta)for(auto d:plan.filled_tests){const unsigned n=__builtin_popcount(plan.planned_operators[d]);
            if(n>1)bytes+=std::uint64_t(host_.ranks(plan.column))*sizeof(rank_theta::Boundary)*(n-1);}
        if(bytes>summary_budget_ || summary_reserved_>summary_budget_-bytes){summary_ineligible_[scope]="summary memory budget: needs "+std::to_string(bytes)+" bytes";continue;}
        summary_reserved_+=bytes;
        std::vector<int> operators;for(const auto &t:plan.tests)operators.push_back(t.op);
        plan.bank=store_.add_summary(host_.ranks(plan.column),operators);
        auto &bank=store_.summaries[plan.bank];
        bank.raw_tests=plan.raw_tests;bank.folded_constant_tests=plan.folded_constants;
        for(unsigned d=0;d<plan.tests.size();++d)bank.operators[d]=plan.planned_operators[d];
        bank.estimated_rows_per_rank=estimate.rows;bank.estimated_points_per_rank=estimate.points;bank.estimated_repeats=estimate.repeats;bank.estimated_summary_work=estimate.summary;bank.estimated_walk_work=estimate.walk;
        bank.measured_admission=frontier&&!unique&&summary_cost_guard_;
        bank.reserved_bytes=bytes;bank.tablewide=(summary_mode_&4)!=0;
        bank.target_rows=host_.rows(occurrence_columns_.at(target_));
        bank.present_ranks=present_count(host_,plan.column,0);bank.present_ranks_known=true;
        bank.decision_mode=(summary_mode_&8)!=0&&!plan.point_mode;
        bank.theta_mode=plan.theta;
        const auto states=store_.summaries[plan.bank].states;
        for(unsigned k=0;k<states;++k)plan.all.set(k);
        unsigned stride=1;
        for(unsigned i=0;i<plan.tests.size();++i,stride*=3){SummarySymbol symbol;
            for(unsigned k=0;k<states;++k){const auto value=(k/stride)%3;
                if(value==0)symbol.no.set(k);else if(value==1)symbol.yes.set(k);}
            plan.symbols.push_back(symbol);
        }
        plan.work.resize(plan.steps.size());
        for(unsigned stage=0;stage<plan.steps.size();++stage)plan.work[stage].column=plan.steps[stage].column;
        const unsigned id=summary_plans_.size();shared[plan.signature]=id;
        plan.requests.push_back(scope);
        summary_ineligible_[scope].clear();summary_requests_[scope]={int(id),plan.tests};summary_requests_[scope].source=plan.steps.front().source;summary_requests_[scope].column=plan.column;summary_plans_.push_back(std::move(plan));
    }
    if(summary_mode_&8)for(auto &plan:summary_plans_){
        if(plan.merged_index>=0)continue;
        auto &bank=store_.summaries[plan.bank];
        if(plan.theta){std::vector<unsigned> domains;
            for(auto d:plan.filled_tests)domains.push_back(host_.ranks(plan.tests[d].local.column));
            bank.theta.configure(plan.requests.size(),domains);
            std::vector<std::vector<int>> operators;
            for(auto scope:plan.requests){std::vector<int> ops;
                for(auto d:plan.filled_tests)ops.push_back(summary_requests_[scope].tests[d].op);operators.push_back(ops);}
            bank.theta.configure_operators(operators);
        }else if(bank.decision_mode)bank.decisions.configure(plan.requests.size(),plan.filled_test<0?1:host_.ranks(plan.tests[plan.filled_test].local.column),
            plan.filled_test>=0);
        for(auto scope:plan.requests){auto &request=summary_requests_[scope];
            const auto &canonical=scopes_[plan.scope],&actual=scopes_[scope];
            for(unsigned i=0;i<canonical.locals.size();++i)request.aliases[actual.locals[i]]=canonical.locals[i];
            summary_aliases(canonical.expression,actual.expression,request);
        }
    }
    for(auto &plan:summary_plans_)if(store_.summaries[plan.bank].decision_mode)configure_collective(plan);
}

// Plan-time routing and constant binding only. No relation is read here.
void configure_collective(SummaryPlan &p){
    auto input=[&](Ref ref){
        auto found=std::find(p.rank_inputs.begin(),p.rank_inputs.end(),ref);
        if(found!=p.rank_inputs.end())return int(found-p.rank_inputs.begin());
        p.rank_inputs.push_back(ref);return int(p.rank_inputs.size()-1);
    };
    p.filled_accept.resize(p.tests.size());
    for(unsigned d=0;d<p.tests.size();++d){
        for(unsigned bit=0;bit<p.requests.size();++bit)for(unsigned outcome=0;outcome<3;++outcome)
            if(collective_fill::outcomes(summary_requests_[p.requests[bit]].tests[d].op)&(1U<<outcome))
                p.filled_accept[d][outcome]|=std::uint64_t{1}<<bit;
        p.test_inputs.push_back(input(p.tests[d].local));
        collective_fill::Constants constants;constants.width=p.requests.size();
        if(p.tests[d].constant)for(unsigned bit=0;bit<p.requests.size();++bit){
            const auto &test=summary_requests_[p.requests[bit]].tests[d];const auto &atom=atoms_[test.atom];
            constants.operators[bit]=test.op;
            constants.lower[bit]=atom.lower;constants.upper[bit]=atom.upper;
        }
        if(p.tests[d].constant)constants.compile();
        p.constants.push_back(constants);
    }
    for(const auto &ins:p.program){CollectiveInstruction compiled;
        if(ins.kind==Kind::atom && ins.atom!=p.driver){
            auto test=p.test_by_atom.find(ins.atom);
            if(test!=p.test_by_atom.end())compiled.test=test->second;
            else if(atoms_[ins.atom].constant){compiled.literal=ins.atom;compiled.left=input(atoms_[ins.atom].left);}
            else {compiled.left=input(atoms_[ins.atom].left);compiled.right=input(atoms_[ins.atom].right);}
        }
        if(ins.kind==Kind::exists && ins.scope!=UINT32_MAX){
            const auto &request=summary_requests_[ins.scope];
            if(request.plan>=0 && summary_plans_[request.plan].theta && !p.theta){
                const auto &child_plan=summary_plans_[request.plan];CollectiveChild child;
                child.scope=ins.scope;child.plan=request.plan;
                std::vector<unsigned> bits;
                for(unsigned bit=0;bit<p.requests.size();++bit){
                    const auto &parent_request=summary_requests_[p.requests[bit]];
                    const auto &actual=summary_requests_[parent_request.child_scopes.at(ins.scope)];
                    if(actual.plan!=request.plan)throw std::logic_error("collective child plan topology changed");
                    bits.push_back(actual.bit);
                    for(unsigned k=0;k<child_plan.filled_tests.size();++k){
                        auto ref=actual.tests[child_plan.filled_tests[k]].outer;
                        const bool variable=p.filled_test>=0 && ref==parent_request.tests[p.filled_test].outer;
                        auto alias=parent_request.aliases.find(ref.occurrence);
                        if(!variable && alias!=parent_request.aliases.end())ref.occurrence=alias->second;
                        if(!bit){child.operands[k]=ref;if(variable)child.variable_mask|=1U<<k;}
                        else if(variable!=bool(child.variable_mask&(1U<<k)) || (!variable && !(ref==child.operands[k])))
                            throw std::logic_error("collective child filled inputs differ between requests");
                    }
                }
                child.remap.configure(bits,child_plan.requests.size());
                for(unsigned k=0;k<child_plan.filled_tests.size();++k)if(!(child.variable_mask&(1U<<k)))child.inputs[k]=input(child.operands[k]);
                compiled.child=p.collective_children.size();p.collective_children.push_back(std::move(child));
            }
        }
        p.collective_program.push_back(compiled);
    }
    auto &s=p.scratch;s.ranks.resize(p.rank_inputs.size());s.values.resize(p.program.size());s.tests.resize(p.tests.size());
    s.cuts.reserve(32);s.row.reserve(32);s.result.pieces.reserve(32);s.result.temporary.reserve(32);
}

void summary_aliases(int canonical,int actual,SummaryRequest &request){
    const auto &a=expressions_[canonical],&b=expressions_[actual];
    if(a.kind!=b.kind)throw std::logic_error("canonical request topology changed");
    if(a.kind==Kind::exists){
        request.child_scopes[scope_by_expr_.at(canonical)]=scope_by_expr_.at(actual);
        if(a.locals.size()!=b.locals.size())throw std::logic_error("canonical binder count changed");
        for(unsigned i=0;i<a.locals.size();++i)request.aliases[b.locals[i]]=a.locals[i];
    }
    if(a.left>=0)summary_aliases(a.left,b.left,request);
    if(a.right>=0)summary_aliases(a.right,b.right,request);
}

std::uint32_t summary_value(const SummaryPlan &p,const std::vector<std::int64_t> &rows,Ref ref){
    const auto it=p.locals.find(ref.occurrence);
    if(it==p.locals.end() || rows[it->second]<0)return null_rank;
    return host_.rank(ref.column,rows[it->second]);
}
Truth summary_literal(unsigned value,const Atom&a)const{
    if(value==null_rank)return Truth::unknown;bool yes=false;
    switch(a.op){case 1:yes=value>=a.lower&&value<a.upper;break;
        case 2:yes=value<a.lower;break;case 3:yes=value<a.upper;break;
        case 4:yes=value>=a.upper;break;case 5:yes=value>=a.lower;break;
        case 6:yes=value<a.lower||value>=a.upper;break;default:throw std::logic_error("unknown summary literal operator");}
    return yes?Truth::yes:Truth::no;
}
Truth summary_static(const SummaryPlan&p,const std::vector<std::int64_t>&rows,int id){
    if(id==p.driver)return Truth::yes;const auto&a=atoms_[id];const auto left=summary_value(p,rows,a.left);
    if(a.constant)return summary_literal(left,a);const auto right=summary_value(p,rows,a.right);
    if(left==null_rank||right==null_rank)return Truth::unknown;
    return compare(left,a.op,right)?Truth::yes:Truth::no;
}
rank_summaries::Point summary_point(const SummaryPlan &p,const std::vector<std::int64_t> &rows,
                                   std::vector<SummarySymbol> &values){
    std::uint64_t valid=0;for(unsigned i=0;i<rows.size();++i)if(rows[i]>=0)valid|=std::uint64_t{1}<<i;
    rank_summaries::Point point;
    for(unsigned i=0;i<p.tests.size();++i)point.ranks[i]=summary_value(p,rows,p.tests[i].local);
    values.clear();
    for(const auto &instruction:p.program){SummarySymbol value;
        if(instruction.kind==Kind::atom){
            if(instruction.atom==p.driver)value.yes=p.all;
            else {auto dynamic=p.test_by_atom.find(instruction.atom);
                if(dynamic!=p.test_by_atom.end()){
                    // A NULL local operand remains UNKNOWN for ALL parameters.
                    if(point.ranks[dynamic->second]!=null_rank)value=p.symbols[dynamic->second];
                }else {const auto t=summary_static(p,rows,instruction.atom);
                    if(t==Truth::yes)value.yes=p.all;else if(t==Truth::no)value.no=p.all;}
            }
        }else if(instruction.kind==Kind::yes)value.yes=p.all;
        else if(instruction.kind==Kind::no)value.no=p.all;
        else if(instruction.kind==Kind::negation){value.yes=values[instruction.a].no;value.no=values[instruction.a].yes;}
        else if(instruction.kind==Kind::conjunction){value.yes=values[instruction.a].yes&values[instruction.b].yes;
            value.no=values[instruction.a].no|values[instruction.b].no;}
        else if(instruction.kind==Kind::disjunction){value.yes=values[instruction.a].yes|values[instruction.b].yes;
            value.no=values[instruction.a].no&values[instruction.b].no;}
        else if(instruction.kind==Kind::exists){
            if((valid&instruction.locals)==instruction.locals)value.yes=values[instruction.a].yes;
            value.no=p.all&~value.yes; // SQL EXISTS coerces UNKNOWN only here
        }
        values.push_back(value);
    }
    point.good=values.back().yes;return point;
}

bool summary_constant(unsigned value,const SummaryTest &test)const{
    const auto &a=atoms_[test.atom];
    switch(test.op){case 1:return value>=a.lower && value<a.upper;
        case 2:return value<a.lower;case 3:return value<a.upper;
        case 4:return value>=a.upper;case 5:return value>=a.lower;
        case 6:return value<a.lower || value>=a.upper;}
    throw std::logic_error("unknown request comparison");
}
// A child decision remains a proof region for this complete witness.
struct ChildBoundary {unsigned bank,rank;};

// One word circuit over a complete witness. Constants are bound as contiguous
// arrays at planning, and each atom produces all request bits in one operation.
// This is deliberately NOT called once per branch.
collective_fill::Truth collective_formula(const SummaryPlan &p,std::uint64_t valid,
    const std::map<unsigned,ChildBoundary> &children,unsigned parameter,unsigned theta_state){
    auto &s=p.scratch;auto &bank=store_.summaries[p.bank];
    const auto live=rank_requests::width_mask(p.requests.size());
    if(p.theta){unsigned state=theta_state;
        for(auto d:p.filled_tests){auto truth=state%3;state/=3;
            if(s.ranks[p.test_inputs[d]]==null_rank)truth=2;
            s.tests[d]={truth==1?live:0,truth==0?live:0};}
    }else for(auto d:p.filled_tests){const auto local=s.ranks[p.test_inputs[d]];
        if(local==null_rank || parameter==null_rank)s.tests[d]={};
        else {const auto outcome=local<parameter?0:local==parameter?1:2;
            const auto yes=p.filled_accept[d][outcome]&live;s.tests[d]={yes,live&~yes};}
    }
    for(unsigned i=0;i<p.program.size();++i){
        const auto &ins=p.program[i];const auto &compiled=p.collective_program[i];
        collective_fill::Truth value;
        auto child=compiled.child<0?children.end():children.find(ins.scope);
        if(ins.kind==Kind::exists && child!=children.end()){
            const auto &route=p.collective_children[compiled.child];
            const auto &cp=summary_plans_[route.plan];auto &cb=store_.summaries[child->second.bank];
            std::array<unsigned,2> filled{};
            for(unsigned k=0;k<cp.filled_tests.size();++k){
                if(route.variable_mask&(1U<<k))filled[k]=parameter;
                else filled[k]=s.ranks[route.inputs[k]];
            }
            value.yes=route.remap(PackedRankDecisionStore::Probe(cb,child->second.rank,filled));value.no=live&~value.yes;
            ++bank.collective_child_projections;
        }else if(ins.kind==Kind::atom){
            if(ins.atom==p.driver)value.yes=live;
            else if(compiled.test>=0)value=s.tests[compiled.test];
            else if(compiled.literal>=0){const auto truth=summary_literal(s.ranks[compiled.left],atoms_[compiled.literal]);
                value={truth==Truth::yes?live:0,truth==Truth::no?live:0};}
            else {const auto left=s.ranks[compiled.left],right=s.ranks[compiled.right];
                if(left!=null_rank && right!=null_rank){bool yes=compare(left,atoms_[ins.atom].op,right);
                    value={yes?live:0,yes?0:live};}}
        }else if(ins.kind==Kind::yes)value.yes=live;
        else if(ins.kind==Kind::no)value.no=live;
        else if(ins.kind==Kind::negation)value={s.values[ins.a].no,s.values[ins.a].yes};
        else if(ins.kind==Kind::conjunction)value={s.values[ins.a].yes&s.values[ins.b].yes,s.values[ins.a].no|s.values[ins.b].no};
        else if(ins.kind==Kind::disjunction)value={s.values[ins.a].yes|s.values[ins.b].yes,s.values[ins.a].no&s.values[ins.b].no};
        else if(ins.kind==Kind::exists){if((valid&ins.locals)==ins.locals)value.yes=s.values[ins.a].yes;
            value.no=live&~value.yes;}
        s.values[i]=value;
    }
    bank.collective_formula_steps+=p.program.size();return s.values.back();
}

void collective_witness(const SummaryPlan &p,const std::vector<std::int64_t>& rows,
    const std::map<unsigned,ChildBoundary>& children,std::array<rank_theta::Boundary,2>& axes,
    std::array<std::uint64_t,9>& masks){
    auto &s=p.scratch;auto &bank=store_.summaries[p.bank];++bank.collective_rows;
    std::uint64_t valid=0;for(unsigned i=0;i<rows.size();++i)if(rows[i]>=0)valid|=std::uint64_t{1}<<i;
    // Each distinct local column is loaded only once for this complete row.
    for(unsigned i=0;i<p.rank_inputs.size();++i){auto ref=p.rank_inputs[i];
        if(p.locals.count(ref.occurrence))s.ranks[i]=summary_value(p,rows,ref);
        else s.ranks[i]=bindings_[ref.occurrence]<0?null_rank:bound_rank(ref);
    }
    for(unsigned d=0;d<p.tests.size();++d)if(p.tests[d].constant){
        s.tests[d]=p.constants[d].compare(s.ranks[p.test_inputs[d]]);
        bank.collective_comparisons+=p.requests.size();
    }
    if(p.theta){
        std::array<unsigned,2> local{};
        for(unsigned k=0;k<p.filled_tests.size();++k)local[k]=s.ranks[p.test_inputs[p.filled_tests[k]]];
        axes=bank.theta.prepare_axes(local);
        for(unsigned state=0;state<bank.theta.states;++state)masks[state]|=collective_formula(p,valid,children,0,state).yes;
        return;
    }
    const unsigned domain=bank.decisions.domain;s.cuts.clear();s.cuts.push_back(0);s.cuts.push_back(domain);
    for(auto d:p.filled_tests){auto v=s.ranks[p.test_inputs[d]];
        if(v!=null_rank){s.cuts.push_back(std::min(v,domain));s.cuts.push_back(v>=domain?domain:v+1);}}
    for(const auto &route:p.collective_children){auto found=children.find(route.scope);
        if(found==children.end())continue;
        const auto &theta=store_.summaries[found->second.bank].theta;
        for(unsigned k=0;k<theta.dimensions;++k)if(route.variable_mask&(1U<<k))rank_theta::append_cuts(theta,store_.summaries[found->second.bank].payload().theta,found->second.rank,k,s.cuts);
    }
    std::sort(s.cuts.begin(),s.cuts.end());s.cuts.erase(std::unique(s.cuts.begin(),s.cuts.end()),s.cuts.end());
    s.row.clear();for(unsigned i=0;i+1<s.cuts.size();++i)if(s.cuts[i]<s.cuts[i+1])
        collective_fill::Union::append(s.row,s.cuts[i],s.cuts[i+1],collective_formula(p,valid,children,s.cuts[i],0).yes);
    const auto nulls=p.filled_test<0?0:collective_formula(p,valid,children,null_rank,0).yes;
    s.result.add(s.row,nulls);
}

unsigned request_bank(unsigned scope)const{
    return sorted_requests_[scope]>=0?sorted_plans_[sorted_requests_[scope]].bank:summary_plans_[summary_requests_[scope].plan].bank;
}
bool ensure_summary(unsigned scope,unsigned rank){
    const bool sorted=sorted_requests_[scope]>=0;
    auto &bank=store_.summaries[request_bank(scope)];
    auto &work=sorted?sorted_plans_[sorted_requests_[scope]].work:summary_plans_[summary_requests_[scope].plan].work.front();
    const auto column=sorted?sorted_plans_[sorted_requests_[scope]].column:summary_plans_[summary_requests_[scope].plan].column;
    reached(work,column,rank);CF_COUNT(++work.summary_arrivals);
    if(bank.frontier_dropped){++bank.suppressed_probes;++bank.gate_declines;return false;}
    if(PackedRankDecisionStore::Probe(bank,rank,summary_epoch_)){
        const auto skipped=skipped_slice(host_,column,rank,0);if(sorted){++counters.kept_hits;bank.rows_skipped+=skipped;}
        CF_COUNT(++work.summary_hits;work.rows_skipped+=skipped;counters.rows_skipped+=skipped;);
        return true;
    }
    if(!bank.admit_new()){++bank.gate_declines;return false;}
    fill_summary(scope,rank);return !bank.frontier_dropped&&bank.view.probe(rank);
}
template<class Visitor>void summary_slice(unsigned column,unsigned rank,NodeWork&work,Visitor visit){
    host_.visit(column,1,rank,[&](unsigned row){
        ++counters.witness_rows;++counters.tight_slice_rows;CF_COUNT(++work.witness_rows);
        return visit(row);
    });
}


rank_summaries::Point bind_frontier_literals(const SummaryPlan&p,rank_summaries::Point point){
    if(p.folded_literals.empty())return point;unsigned fixed=0,stride=1;
    const auto &tests=summary_requests_[p.requests.front()].tests;
    for(unsigned d=0;d<p.tests.size();++d,stride*=3)if(std::find(p.folded_literals.begin(),p.folded_literals.end(),d)!=p.folded_literals.end())
        fixed+=stride*(point.ranks[d]==null_rank?2:unsigned(summary_constant(point.ranks[d],tests[d])));
    auto key=std::make_pair(point.good.words,fixed);auto old=p.bound_literal_tables.find(key);
    if(old==p.bound_literal_tables.end()){
        rank_summaries::Bits bound;const auto states=store_.summaries[p.bank].states;
        for(unsigned state=0;state<states;++state){unsigned index=state,mul=1;
            for(unsigned d=0;d<p.tests.size();++d,mul*=3)if(std::find(p.folded_literals.begin(),p.folded_literals.end(),d)!=p.folded_literals.end())index-=((state/mul)%3)*mul;
            if(point.good.get(index+fixed))bound.set(state);
        }
        old=p.bound_literal_tables.emplace(key,bound).first;
    }
    point.good=old->second;return point;
}

void fill_summary(unsigned scope,unsigned rank){
    auto &bank=store_.summaries[request_bank(scope)];
    if(sorted_requests_[scope]>=0){auto &plan=sorted_plans_[sorted_requests_[scope]];
        bank.fill_active=true;bank.active_rank=rank;host_.interrupt();std::vector<unsigned>values;
        values.reserve(std::min<std::uint64_t>(bank.max_rows,skipped_slice(host_,plan.column,rank,0))*std::max(1U,bank.stride()));bool has_null=false;
        summary_slice(plan.column,rank,plan.work,[&](unsigned row){++bank.rows;
            if(!(bank.rows%256))host_.interrupt();
            if(!plan.equality_columns.empty()){
                const auto start=values.size();bool nonnull=true;for(auto column:plan.equality_columns){auto v=host_.rank(column,row);nonnull&=v!=null_rank;values.push_back(v);}
                if(!nonnull)values.resize(start);else if(plan.value_column!=UINT32_MAX)values.push_back(host_.rank(plan.value_column,row));
            }else{auto value=host_.rank(plan.value_column,row);if(value==null_rank)has_null=true;else values.push_back(value);}
            bank.temporary_bytes=values.capacity()*sizeof(unsigned);return false;});
        if(PackedRankDecisionStore::Record(bank,rank,values,has_null,[&](){host_.interrupt();}))CF_COUNT(++plan.work.summary_fills);
        return;
    }
    const auto &plan=summary_plans_[summary_requests_[scope].plan];
    if(plan.merged_index>=0){fill_merged_frontier(plan,rank);return;}
    std::vector<std::int64_t> rows(plan.locals.size(),-1);
    std::vector<rank_summaries::Point> points;
    const bool collective=bank.decision_mode;
    std::array<rank_theta::Boundary,2> axes{};std::array<std::uint64_t,9> masks{};
    std::vector<SummarySymbol> values;values.reserve(plan.program.size());
    if(collective && !plan.theta)plan.scratch.result.reset(bank.decisions.domain);
    const auto &root=plan.steps.front();
    bank.active_rank=rank;bank.fill_active=true;bank.fill_input_bytes=0;bank.reduction_temporary_bytes=0;
    host_.interrupt();
    {rank_summaries::Summary::Phase read_phase(bank.collection_ns);
    summary_slice(root.column,rank,plan.work.front(),[&](std::uint32_t row){
        ++bank.fill_rows_visited;
        if((bank.fill_rows_visited&255U)==0)host_.interrupt();
        std::fill(rows.begin(),rows.end(),-1);rows[0]=row;
        std::map<unsigned,ChildBoundary> children;std::set<int> replaced;
        for(unsigned i=1;i<plan.steps.size();++i){const auto &step=plan.steps[i];
            if(replaced.count(step.occurrence))continue;
            bool needed=true;
            for(int id:step.guards){const auto &a=atoms_[id];
                if(id==plan.driver || a.constant || plan.test_by_atom.count(id))continue;
                auto l=plan.locals.find(a.left.occurrence),r=plan.locals.find(a.right.occurrence);
                if(l!=plan.locals.end() && r!=plan.locals.end() && rows[l->second]>=0 && rows[r->second]>=0 &&
                    summary_static(plan,rows,id)!=Truth::yes){needed=false;break;}
            }
            if(!needed)continue;
            const auto pivot=summary_value(plan,rows,step.source);if(pivot==null_rank)continue;
            reached(plan.work[i],step.column,pivot);
            const auto &child=summary_requests_[step.scope];
            if(bank.decision_mode && !plan.theta && step.stage==0 && child.plan>=0 &&
               summary_plans_[child.plan].theta && ensure_summary(step.scope,pivot)){
                const auto &child_plan=summary_plans_[child.plan];
                children.emplace(step.scope,ChildBoundary{child_plan.bank,pivot});
                for(const auto &local:child_plan.locals)replaced.insert(local.first);
                continue;
            }
            host_.visit(step.column,1,pivot,[&](std::uint32_t found){
                rows[plan.locals.at(step.occurrence)]=found;
                ++counters.witness_rows;++counters.tight_slice_rows;
                CF_COUNT(++plan.work[i].witness_rows);
                return true; // data-unique key: exactly one complete row
            });
            ++counters.unique_hops;
        }
        if(bank.decision_mode)++bank.candidates;
        if(collective)collective_witness(plan,rows,children,axes,masks);
        else {points.push_back(bind_frontier_literals(plan,summary_point(plan,rows,values)));
            bank.fill_input_bytes=points.capacity()*sizeof(rank_summaries::Point);}
        return false;
    });
    }
    if(plan.theta){PackedRankDecisionStore::Record(bank,rank,axes,masks);if(collective)++bank.collective_fills;}
    else if(collective)PackedRankDecisionStore::Record(bank,rank,plan.scratch.result.pieces,plan.scratch.result.null_good);
    else PackedRankDecisionStore::Record(bank,rank,points,[&](){host_.interrupt();});
    bank.fill_active=false;bank.fill_input_bytes=0;bank.reduction_temporary_bytes=0;host_.interrupt();
    CF_COUNT(auto &work=plan.work.front();if(!bank.frontier_dropped){++work.summary_fills;if(!bank.decision_mode)work.frontier_points+=bank.payload().slots[rank].count;});
    if(collective){std::fill(plan.scratch.ranks.begin(),plan.scratch.ranks.end(),null_rank);
        std::fill(plan.scratch.tests.begin(),plan.scratch.tests.end(),collective_fill::Truth{});}
}

// One request activation for scalar, compiled and shared-mask callers.
// The caller's bit mapping changes only the binding view, never the stored
// decision form, completion rule or the fill that establishes it.
Outcome answer_request(unsigned scope,unsigned rank,const std::map<int,int>*aliases=nullptr){
    if(sorted_requests_[scope]>=0){auto &plan=sorted_plans_[sorted_requests_[scope]];auto &bank=store_.summaries[plan.bank];
    std::vector<unsigned>prefix(plan.equality_columns.size(),UINT32_MAX);
    bool prefix_ready=true,prefix_possible=true;for(auto id:plan.equality_atoms){const auto&a=atoms_[id];const bool left=a.left.occurrence==plan.local;
        const auto local=left?a.left:a.right,outer=request_alias(left?a.right:a.left,aliases);
        if(bindings_[outer.occurrence]<0){prefix_ready=false;break;}const auto value=bound_rank(outer);
        if(value==null_rank){prefix_possible=false;break;}auto position=std::find(plan.equality_columns.begin(),plan.equality_columns.end(),local.column)-plan.equality_columns.begin();
        if(prefix[position]!=UINT32_MAX&&prefix[position]!=value){prefix_possible=false;break;}prefix[position]=value;
    }
    if(!prefix_ready)return{0,0};if(!prefix_possible){++bank.empty_rejections;invalidate_certificates();return{1,0};}
    auto accepted=sorted_formula(scopes_[scope].expression,plan,aliases);
    if(!accepted.ready)return {0,0};
    invalidate_certificates();
    // Evaluate outer guards and an empty interval before accessing the bank.
    if(accepted.yes.ranges.empty()&&!accepted.yes.null_good){++bank.empty_rejections;return {1,0};}
    if(!ensure_summary(scope,rank))return {0,0};
    const bool good=plan.equality_columns.empty()?rank_sorted::contains(bank,rank,accepted.yes):rank_sorted::contains_prefix(bank,rank,prefix,accepted.yes);if(good)++counters.first_witness_stops;else ++counters.exhaustions;
    return {1,good?1U:0U};
    }
    const auto &request=summary_requests_[scope];const auto &plan=summary_plans_[request.plan];
    auto &bank=store_.summaries[plan.bank];
    if(!ensure_summary(scope,rank))return {0,0};
    // An exact parametric summary is not a proof over an enclosing varying
    // probe window. Keep the existing certificate safety rule.
    invalidate_certificates();
    if(plan.merged_index>=0){
        const auto bit=std::uint64_t{1}<<request.bit;
        const auto yes=answer_merged_frontier(plan,rank,{{scope,aliases}});
        return {1,(yes&bit)?1U:0U};
    }
    if(plan.theta){
        std::array<unsigned,2> filled{};
        for(unsigned i=0;i<plan.filled_tests.size();++i)filled[i]=bound_rank(request_alias(request.tests[plan.filled_tests[i]].outer,aliases));
        auto mask=PackedRankDecisionStore::Probe(bank,rank,filled);return {1,(mask&(std::uint64_t{1}<<request.bit))?1U:0U};
    }
    if(bank.decision_mode){
        unsigned value=0;
        const BoundaryBinding *indirect=nullptr;
        if(plan.filled_test>=0){const auto ref=request_alias(request.tests[plan.filled_test].outer,aliases);
            if(bindings_[ref.occurrence]<0)throw std::logic_error("request filled operand unbound");
            const auto &binding=boundary_bindings_[ref.occurrence];
            if(binding.bank>=0 && binding.parameter==ref.column)indirect=&binding;
            else value=bound_rank(ref);}
        const auto mask=indirect?PackedRankDecisionStore::Probe(bank,rank,store_.summaries[indirect->bank],indirect->rank,summary_epoch_,indirect->transient):
            PackedRankDecisionStore::Probe(bank,rank,value,summary_epoch_);
        const bool answer=(mask&(std::uint64_t{1}<<request.bit))!=0;
        if(answer)++counters.first_witness_stops;else ++counters.exhaustions;
        return {1,answer?1U:0U};
    }
    std::array<std::uint32_t,rank_summaries::max_tests> parameters{};
    for(unsigned d=0;d<request.tests.size();++d)if(!request.tests[d].constant){
        const auto ref=request_alias(request.tests[d].outer,aliases);
        if(bindings_[ref.occurrence]<0)throw std::logic_error("summary filled operand unbound");
        parameters[d]=bound_rank(ref);
    }
    return {1,summary_points(request,bank,rank,parameters)?1U:0U};
}

bool summary_points(const SummaryRequest &request,rank_summaries::Summary &bank,unsigned rank,
    const std::array<std::uint32_t,rank_summaries::max_tests> &parameters){
    rank_summaries::Summary::Phase probe_phase(bank.probe_ns);
    ++bank.frontier_arrivals;const auto *slot=&bank.view.slot(rank);
    auto key=parameters;bool usable=true;
    const auto equality=bank.equality_dimensions();
    for(unsigned d=0;d<request.tests.size();++d)if(equality&(1U<<d)){
        const auto&test=request.tests[d];
        if(test.constant){const auto&a=atoms_[test.atom];
            if(a.upper!=std::uint64_t(a.lower)+1)usable=false;else key[d]=a.lower;}
        else if(test.op!=1)usable=false;
    }
    const auto group=bank.equality_slice(rank,key,usable);
    const auto inspect=[&](std::uint64_t position,bool fallback){
        const auto&point=bank.view.point(position);++bank.checks;if(fallback)++bank.ungrouped_points_checked;
        unsigned index=0,stride=1;
        for(unsigned d=0;d<request.tests.size();++d,stride*=3){
            const auto &test=request.tests[d];const auto value=point.ranks[d];unsigned truth=2;
            if(value!=null_rank){
                if(!test.constant){if(parameters[d]!=null_rank)truth=compare(value,test.op,parameters[d]);}
                else {const auto &a=atoms_[test.atom];bool result=false;
                    switch(test.op){case 1:result=value>=a.lower && value<a.upper;break;
                        case 2:result=value<a.lower;break;case 3:result=value<a.upper;break;
                        case 4:result=value>=a.upper;break;case 5:result=value>=a.lower;break;
                        case 6:result=value<a.lower || value>=a.upper;break;}
                    truth=result;
                }
            }
            index+=truth*stride;
        }
        return point.good.get(index);
    };
    for(std::uint64_t i=slot->offset;i<slot->offset+slot->ungrouped;++i)if(inspect(i,true)){++counters.first_witness_stops;return true;}
    for(auto i=group.first;i<group.second;++i)if(inspect(i,false)){++counters.first_witness_stops;return true;}
    ++counters.exhaustions;return false;
}

void configure_equality_ranges(){
    if(!decisions_ || !(summary_mode_&32))return;
    std::map<std::pair<unsigned,unsigned>,unsigned> shared;
    for(auto &scope:scopes_)for(unsigned stage=0;stage<scope.locals.size();++stage){
        const int occurrence=scope.locals[stage];unsigned entered=UINT32_MAX,parameter=UINT32_MAX;
        for(auto id:ranked_equalities(scope,occurrence,word_preferred_atom(unsigned(&scope-scopes_.data()),stage))){const auto &a=atoms_[id];if(a.constant || a.op!=1)continue;
            Ref candidate,source;
            if(a.left.occurrence==occurrence){candidate=a.left;source=a.right;}
            else if(a.right.occurrence==occurrence){candidate=a.right;source=a.left;}else continue;
            auto position=std::find(scope.locals.begin(),scope.locals.end(),source.occurrence);
            if(position!=scope.locals.end() && unsigned(position-scope.locals.begin())>=stage)continue;
            if(owned_inside(scope.expression,source.occurrence) || !host_.unique(candidate.column))continue;
            entered=candidate.column;break;
        }
        if(entered==UINT32_MAX)continue;
        bool eligible=true,used=false;
        for(const auto &r:scope.requests){
            if(!r.quantifier){const auto &a=atoms_[r.value];
                if((a.left.occurrence==occurrence && a.left.column!=entered) ||
                   (!a.constant && a.right.occurrence==occurrence && a.right.column!=entered))eligible=false;
                continue;
            }
            const auto &child=scopes_[r.value];bool reads=false;
            for(auto ref:child.refs)if(ref.occurrence==occurrence && ref.column!=entered)reads=true;
            if(!reads)continue;
            const auto &request=summary_requests_[r.value];
            if(request.plan<0){eligible=false;continue;}
            const auto &plan=summary_plans_[request.plan];const auto &bank=store_.summaries[plan.bank];
            if(plan.theta || plan.filled_tests.size()!=1 || r.ready!=stage+1 ||
                bank.target_rows<2*bank.present_ranks){eligible=false;continue;}
            auto ref=request.tests[plan.filled_tests[0]].outer;
            if(ref.occurrence!=occurrence || (parameter!=UINT32_MAX && parameter!=ref.column)){eligible=false;continue;}
            parameter=ref.column;used=true;
        }
        for(auto ref:scope.refs)if(ref.occurrence==occurrence && ref.column!=entered && ref.column!=parameter)eligible=false;
        if(!eligible || !used)continue;
        auto key=std::make_pair(entered,parameter);auto found=shared.find(key);
        if(found==shared.end()){
            const auto bytes=std::uint64_t(host_.ranks(entered))*(sizeof(rank_theta::Boundary)+sizeof(rank_summaries::Slot));
            if(bytes>summary_budget_ || summary_reserved_>summary_budget_-bytes)continue;
            summary_reserved_+=bytes;
            found=shared.emplace(key,store_.add_rank_equality(entered,parameter,host_.ranks(entered),host_.ranks(parameter))).first;
        }
        scope.boundary_banks[stage]=found->second;
    }
}

Outcome walk_with_equality_range(unsigned scope_id,unsigned stage,unsigned depth,MaskFrame &frame,unsigned rank){
    auto &scope=scopes_[scope_id];const int occurrence=scope.locals[stage];
    const unsigned id=scope.boundary_banks[stage];auto &bank=store_.summaries[id];
    auto slot=PackedRankDecisionStore::Probe(bank,rank,summary_epoch_);const bool known=slot;
    bool present=slot&&slot->count;rank_theta::Boundary transient;
    CF_COUNT(++scope.work[stage].boundary_probes;if(known)++scope.work[stage].boundary_hits);
    if(!known){unsigned boundary=null_rank;
        host_.visit(bank.column,1,rank,[&](unsigned row){
            ++counters.witness_rows;++counters.tight_slice_rows;CF_COUNT(++scope.work[stage].witness_rows);
            present=true;boundary=host_.rank(bank.parameter_column,row);return true;
        });
        transient=rank_theta::transfer(boundary,1,bank.parameter_domain);
        if(PackedRankDecisionStore::Record(bank,rank,transient,present))CF_COUNT(++scope.work[stage].boundary_fills);
        slot=bank.view.probe(rank);
    }
    if(!present){++counters.exhaustions;return {1,0};}
    bindings_[occurrence]=0;boundary_bindings_[occurrence]={int(id),rank,bank.column,bank.parameter_column,slot?nullptr:&transient};
    auto &child=scope.frames[stage+1];scope.formula.inherit(child,frame);
    settle_ready(scope,child,stage+1,depth);
    const auto answer=walk(scope_id,stage+1,depth,child);
    bindings_[occurrence]=-1;boundary_bindings_[occurrence]={};
    return answer;
}

void configure_rank_facts(){
    if(summary_mode_&8)return; // no retained row values in the decision build
    if(!decisions_ || !(summary_mode_&2))return;
    struct Use {unsigned scope,stage,column;};std::vector<Use> uses;
    std::map<unsigned,std::set<unsigned>> layouts;
    for(unsigned id=0;id+1<scopes_.size();++id){auto &scope=scopes_[id];
        if(summary_requests_[id].plan>=0)continue; // complete point is already stronger
        for(unsigned stage=0;stage<scope.locals.size();++stage){
            bool frontier_child=false;
            for(const auto &request:scope.requests)if(request.quantifier && request.ready==stage+1 &&
                summary_requests_[request.value].plan>=0)frontier_child=true;
            if(!frontier_child)continue;
            const auto occurrence=scope.locals[stage];unsigned column=UINT32_MAX;
            for(int atom_id:ranked_equalities(scope,occurrence,word_preferred_atom(id,stage))){const auto &a=atoms_[atom_id];if(a.constant || a.op!=1)continue;
                Ref candidate,source;
                if(a.left.occurrence==occurrence){candidate=a.left;source=a.right;}
                else if(a.right.occurrence==occurrence){candidate=a.right;source=a.left;}
                else continue;
                const auto position=std::find(scope.locals.begin(),scope.locals.end(),source.occurrence);
                if(position!=scope.locals.end() && unsigned(position-scope.locals.begin())>=stage)continue;
                if(owned_inside(scope.expression,source.occurrence))continue;
                column=candidate.column;break;
            }
            if(column==UINT32_MAX || !host_.unique(column))continue;
            auto &cols=layouts[column];cols.insert(column);
            for(auto ref:scope.refs)if(ref.occurrence==occurrence)cols.insert(ref.column);
            uses.push_back({id,stage,column});
        }
    }
    std::map<unsigned,int> banks;
    for(const auto &layout:layouts){
        const std::uint64_t bytes=std::uint64_t(host_.ranks(layout.first))*(sizeof(rank_summaries::Slot)+4*layout.second.size());
        if(bytes>summary_budget_ || summary_reserved_>summary_budget_-bytes)continue;
        summary_reserved_+=bytes;
        banks[layout.first]=store_.add_rank_facts(layout.first,host_.ranks(layout.first),
            std::vector<unsigned>(layout.second.begin(),layout.second.end()));
    }
    for(auto use:uses){auto found=banks.find(use.column);if(found!=banks.end())
        scopes_[use.scope].fact_banks[use.stage]=found->second;}
}

Outcome walk_with_facts(unsigned scope_id,unsigned stage,unsigned depth,MaskFrame &frame,unsigned rank){
    auto &scope=scopes_[scope_id];const int occurrence=scope.locals[stage];
    auto &bank=store_.summaries[scope.fact_banks[stage]];++bank.fact_requests;
    auto slot=PackedRankDecisionStore::Probe(bank,rank,summary_epoch_);
    bool present=slot&&slot->count;std::vector<std::uint32_t> values;
    if(!slot){
        // A data-unique inverted slice has zero or one row. Read it only on
        // this rank's first arrival, then keep the read ranks inside V.
        host_.visit(bank.column,1,rank,[&](std::uint32_t row){
            present=true;++counters.witness_rows;++counters.tight_slice_rows;
            CF_COUNT(++scope.work[stage].witness_rows);
            for(auto column:bank.fact_columns)values.push_back(host_.rank(column,row));
            return true;
        });
        PackedRankDecisionStore::Record(bank,rank,values,present);++counters.unique_hops;
        slot=bank.view.probe(rank);
    }
    if(!present){++counters.exhaustions;return {1,0};}
    bindings_[occurrence]=0;fact_bindings_[occurrence]={slot?bank.payload().fact_ranks.data()+slot->offset:values.data(),&bank.fact_columns};
    auto &child=scope.frames[stage+1];scope.formula.inherit(child,frame);
    settle_ready(scope,child,stage+1,depth);
    const auto result=walk(scope_id,stage+1,depth,child);
    bindings_[occurrence]=-1;fact_bindings_[occurrence]={};
    if(result.H&1)++counters.first_witness_stops;else ++counters.exhaustions;
    return result;
}
