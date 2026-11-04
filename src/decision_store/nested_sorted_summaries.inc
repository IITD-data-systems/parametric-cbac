// One-table range summaries are a decision strategy of the same scoped Walk.
struct SortedPlan {unsigned scope=0,column=0,value_column=0,bank=0;int local=-1,driver=-1;Ref source;NodeWork work;std::vector<unsigned>equality_columns;std::set<int>equality_atoms;};
struct SortedTruth {rank_requests::Set yes,no;bool ready=true;};
std::vector<SortedPlan> sorted_plans_;
std::vector<int> sorted_requests_;
std::vector<std::string> sorted_reasons_;

bool configure_sorted(unsigned scope){
    const auto&s=scopes_[scope];auto decline=[&](const std::string&why){sorted_reasons_[scope]=why;return false;};
    if(s.locals.size()!=1)return decline("requires exactly one local table");
    SortedPlan plan;plan.scope=scope;plan.local=s.locals.front();
    for(auto id:ranked_equalities(s,plan.local,word_preferred_atom(scope,0))){const auto&a=atoms_[id];if(a.constant||a.op!=1)continue;Ref entry,source;
        if(a.left.occurrence==plan.local){entry=a.left;source=a.right;}else if(a.right.occurrence==plan.local){entry=a.right;source=a.left;}else continue;
        if(source.occurrence==plan.local||owned_inside(s.expression,source.occurrence))continue;
        plan.driver=id;plan.column=entry.column;plan.source=source;break;
    }
    if(plan.driver<0)return decline("no mandatory equality from an outer row");
    if(summary_driver_is_target_unique(scope,plan.source))return decline("target-unique driver: no rank reuse");
    std::map<unsigned,std::vector<int>>tests;bool valid=true;
    std::function<void(int)>check=[&](int id){const auto&e=expressions_[id];
        if(e.kind==Kind::exists){valid=false;sorted_reasons_[scope]="child quantifier requires another local table";return;}
        if(e.kind==Kind::atom&&e.value!=plan.driver){const auto&a=atoms_[e.value];bool l=a.left.occurrence==plan.local,r=!a.constant&&a.right.occurrence==plan.local;
            if(l&&r){valid=false;sorted_reasons_[scope]="comparison reads two local columns";return;}
            if(l||r)tests[l?a.left.column:a.right.column].push_back(e.value);
        }
        if(e.left>=0)check(e.left);if(e.right>=0)check(e.right);
    };check(s.expression);if(!valid)return false;
    if(tests.empty())return decline("no local value test; use ordinary decision");
    // Prefix equalities must be mandatory; an OR-only equality may never
    // select the slice for another alternative.
    std::vector<unsigned>range_columns;
    for(const auto&column:tests){bool equality=true;
        for(auto id:column.second){const auto&a=atoms_[id];equality&=!a.constant&&a.op==1&&std::binary_search(s.mandatory.begin(),s.mandatory.end(),id);}
        if(equality){plan.equality_columns.push_back(column.first);for(auto id:column.second)plan.equality_atoms.insert(id);}
        else range_columns.push_back(column.first);
    }
    if(range_columns.size()>1)return decline("more than one non-equality local range column");
    plan.value_column=range_columns.empty()?UINT32_MAX:range_columns.front();
    // Keep the original one-column form when all tests happen to be =.
    if(tests.size()==1&&range_columns.empty()){plan.value_column=tests.begin()->first;plan.equality_columns.clear();plan.equality_atoms.clear();}
    if(host_.unique(plan.column))return decline("unique rank retains its existing compact decision form");
    if(!(summary_mode_&1))return decline("summary mode excludes multi-row entries");
    unsigned bank=0;for(;bank<store_.summaries.size();++bank){const auto&b=store_.summaries[bank];if(b.sorted_mode&&b.column==plan.column&&b.value_column==plan.value_column&&b.equality_columns==plan.equality_columns)break;}
    if(bank==store_.summaries.size()){
        const auto rows=std::uint64_t(host_.rows(plan.column));const auto prefix=plan.equality_columns.size(),width=prefix+(plan.value_column!=UINT32_MAX);
        const auto bytes=std::uint64_t(host_.ranks(plan.column))*(sizeof(rank_summaries::Slot)+(prefix?sizeof(rank_requests::MaskedSlot):0))+
            rows*(prefix?sizeof(unsigned)*(2*width+2*prefix)+sizeof(std::size_t):2*sizeof(unsigned));
        if(bytes>summary_budget_||summary_reserved_>summary_budget_-bytes)return decline("sorted-rank summary memory budget: needs "+std::to_string(bytes)+" bytes");
        summary_reserved_+=bytes;bank=store_.add_summary(host_.ranks(plan.column));auto &b=store_.summaries[bank];
        b.sorted_mode=true;b.column=plan.column;b.value_column=plan.value_column;b.equality_columns=plan.equality_columns;
        b.max_rows=rows;b.reserved_bytes=bytes;
    }
    plan.bank=bank;plan.work.column=plan.column;store_.summaries[bank].requests.push_back(scope);
    sorted_requests_[scope]=sorted_plans_.size();sorted_plans_.push_back(std::move(plan));summary_entered_[scope]=sorted_plans_.back().column;
    summary_ineligible_[scope].clear();sorted_reasons_[scope].clear();return true;
}
Ref request_alias(Ref ref,const std::map<int,int>*aliases)const{
    if(aliases){auto found=aliases->find(ref.occurrence);if(found==aliases->end())throw std::logic_error("request lost an outer operand");ref.occurrence=found->second;}return ref;
}
SortedTruth sorted_formula(int id,const SortedPlan&p,const std::map<int,int>*aliases){
    const auto&e=expressions_[id];const auto domain=p.value_column==UINT32_MAX?1:host_.ranks(p.value_column);SortedTruth result;
    if(e.kind==Kind::yes||e.kind==Kind::no||(e.kind==Kind::atom&&(e.value==p.driver||p.equality_atoms.count(e.value)))){
        (e.kind==Kind::no?result.no:result.yes)=rank_theta::whole(domain);return result;}
    if(e.kind==Kind::atom){const auto&a=atoms_[e.value];const bool l=a.left.occurrence==p.local,r=!a.constant&&a.right.occurrence==p.local;
        if(!l&&!r){auto left=request_alias(a.left,aliases);auto right=a.constant?Ref{}:request_alias(a.right,aliases);
            if(bindings_[left.occurrence]<0||(!a.constant&&bindings_[right.occurrence]<0)){result.ready=false;return result;}
            const auto x=bound_rank(left),y=a.constant?0:bound_rank(right);
            if(x==null_rank||(!a.constant&&y==null_rank))return result;
            bool good;
            if(a.constant)good=a.op==1?x>=a.lower&&x<a.upper:a.op==2?x<a.lower:a.op==3?x<a.upper:a.op==4?x>=a.upper:a.op==5?x>=a.lower:x<a.lower||x>=a.upper;
            else good=compare(x,a.op,y);
            (good?result.yes:result.no)=rank_theta::whole(domain);return result;
        }
        if(a.constant){switch(a.op){case 1:result.yes.add(a.lower,a.upper);break;case 2:result.yes.add(0,a.lower);break;
            case 3:result.yes.add(0,a.upper);break;case 4:result.yes.add(a.upper,domain);break;case 5:result.yes.add(a.lower,domain);break;
            case 6:result.yes.add(0,a.lower);result.yes.add(a.upper,domain);break;}}
        else {auto outer=request_alias(l?a.right:a.left,aliases);if(bindings_[outer.occurrence]<0){result.ready=false;return result;}
            auto value=bound_rank(outer);if(value==null_rank)return result;
            // transfer describes fixed OP variable; invert local OP filled.
            auto boundary=rank_theta::transfer(value,inverse(l?a.op:inverse(a.op)),domain);
            for(unsigned i=0;i<boundary.count;++i)result.yes.add(boundary.yes[i].lo,boundary.yes[i].hi);
        }
        result.no=rank_theta::negate(result.yes,domain);result.no.null_good=false;return result;
    }
    auto a=sorted_formula(e.left,p,aliases);if(e.kind==Kind::negation){std::swap(a.yes,a.no);return a;}
    auto b=sorted_formula(e.right,p,aliases);result.ready=a.ready&&b.ready;
    if(e.kind==Kind::conjunction){result.yes=rank_theta::meet(a.yes,b.yes);result.no=rank_theta::unite(a.no,b.no);}
    else {result.yes=rank_theta::unite(a.yes,b.yes);result.no=rank_theta::meet(a.no,b.no);}return result;
}
