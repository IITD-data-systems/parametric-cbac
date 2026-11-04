// Conjunctive, equality-entered requests share one on-arrival frontier.
// Outside polarity is deliberately absent from both the bank and its bits.
struct MergedColumn {unsigned row=0,column=0;};
struct MergedStep {
    unsigned column=0,source_row=0,source_column=0;
    int occurrence=-1;unsigned scope=0,stage=0;
};
struct MergedFixed {unsigned left=0,right=0;int atom=-1;bool constant=false;};
struct MergedTest {unsigned dimension=0;Ref outer;int op=1;int atom=-1;};
struct MergedRequest {
    unsigned scope=0;
    std::vector<unsigned> required;
    std::vector<MergedFixed> fixed;
    std::vector<MergedTest> tests;
    std::vector<int> guards;
    bool impossible=false;
};
struct MergedFrontierPlan {
    std::vector<MergedStep> steps;
    std::vector<MergedColumn> columns;
    std::vector<MergedRequest> requests;
};
struct MergedArrival {unsigned scope=0;const std::map<int,int>*aliases=nullptr;};
std::vector<MergedFrontierPlan> merged_frontiers_;
struct MergedPending {unsigned rank=0,scope=0,member=0;const std::map<int,int>*aliases=nullptr;};
std::vector<int> merged_seen_;std::vector<MergedPending> merged_pending_;std::vector<MergedArrival> merged_members_;
std::vector<rank_merged::Input> merged_inputs_;std::vector<rank_merged::GroupKey> merged_keys_;
std::vector<std::vector<Ref>> merged_refs_;std::vector<char> merged_refs_ready_;
const std::vector<Ref>& merged_outer_refs(unsigned scope){
    if(merged_refs_ready_.size()<scopes_.size()){merged_refs_ready_.assign(scopes_.size(),0);merged_refs_.assign(scopes_.size(),{});}
    if(!merged_refs_ready_[scope]){const auto&s=scopes_[scope];
        for(auto ref:s.refs)if(!owned_inside(s.expression,ref.occurrence)&&std::find(s.locals.begin(),s.locals.end(),ref.occurrence)==s.locals.end())merged_refs_[scope].push_back(ref);
        merged_refs_ready_[scope]=1;}
    return merged_refs_[scope];
}

// Positive EXISTS over a functional descendant is a conjunction over its
// one possible row, including row existence. Internal NOT/OR is NOT such a
// conjunction and retains its existing truth-table/per-request bank.
bool merged_conjuncts(int expression,std::vector<int>&atoms,bool &impossible)const{
    const auto &e=expressions_[expression];
    if(e.kind==Kind::atom){atoms.push_back(e.value);return true;}
    if(e.kind==Kind::yes)return true;
    if(e.kind==Kind::no){impossible=true;return true;}
    if(e.kind==Kind::exists)return merged_conjuncts(e.left,atoms,impossible);
    if(e.kind==Kind::conjunction)return merged_conjuncts(e.left,atoms,impossible)&&merged_conjuncts(e.right,atoms,impossible);
    return false;
}

void configure_merged_frontiers(){
    // Only a shared-read strategy: decision_sharing=off preserves precisely
    // the old per-request path. The word graph is configured before this.
    if(!word_graph_ready_)return;
    struct Draft {SummaryPlan plan;std::vector<int> atoms;bool impossible=false;};
    std::vector<Draft> drafts;
    std::map<std::pair<unsigned,unsigned>,std::vector<unsigned>> groups;
    for(unsigned scope=0;scope+1<scopes_.size();++scope){
        if(scopes_[scope].locals.empty()||word_scope_group_[scope]<0)continue;
        Draft d;d.plan.scope=scope;std::set<int> bound;
        if(!merged_conjuncts(scopes_[scope].expression,d.atoms,d.impossible))continue;
        // Keep the existing complete-functional-witness eligibility. A
        // searching child is another node, never an invented join of rows.
        if(!summary_steps(scope,d.plan,bound,{},true))continue;
        const bool unique=host_.unique(d.plan.column);
        if(unique?!(summary_mode_&2):!(summary_mode_&1))continue;
        const auto key=std::make_pair(d.plan.column,d.plan.steps.front().source.column);
        groups[key].push_back(drafts.size());drafts.push_back(std::move(d));
    }
    for(const auto &group:groups)for(unsigned begin=0;begin<group.second.size();begin+=64){
        const unsigned end=std::min<unsigned>(group.second.size(),begin+64);
        if(end-begin<2)continue; // today's single-request bank is unchanged
        MergedFrontierPlan merged;
        std::map<std::string,unsigned> paths;
        auto dimension=[&](unsigned row,unsigned column){
            for(unsigned i=0;i<merged.columns.size();++i)
                if(merged.columns[i].row==row&&merged.columns[i].column==column)return i;
            merged.columns.push_back({row,column});return unsigned(merged.columns.size()-1);
        };
        for(unsigned i=begin;i<end;++i){const auto &d=drafts[group.second[i]];const auto&p=d.plan;
            MergedRequest request;request.scope=p.scope;request.impossible=d.impossible;
            std::map<int,unsigned> local_rows;
            std::map<int,std::string> local_paths;
            for(unsigned stage=0;stage<p.steps.size();++stage){const auto &step=p.steps[stage];
                std::string path="root";unsigned source_row=0;
                if(stage){source_row=local_rows.at(step.source.occurrence);
                    path=local_paths.at(step.source.occurrence)+"/"+std::to_string(step.source.column)+"="+std::to_string(step.column);}
                auto old=paths.find(path);unsigned row;
                if(old==paths.end()){row=merged.steps.size();paths.emplace(path,row);
                    merged.steps.push_back({step.column,source_row,step.source.column,step.occurrence,step.scope,step.stage});}
                else row=old->second;
                local_rows[step.occurrence]=row;local_paths[step.occurrence]=path;request.required.push_back(row);
            }
            for(int id:d.atoms){if(id==p.driver)continue;const auto&a=atoms_[id];
                const auto l=local_rows.find(a.left.occurrence),r=local_rows.find(a.right.occurrence);
                const bool left=l!=local_rows.end(),right=!a.constant&&r!=local_rows.end();
                if(!left&&!right){request.guards.push_back(id);continue;}
                if(a.constant){request.fixed.push_back({dimension(l->second,a.left.column),0,id,true});continue;}
                if(left&&right){request.fixed.push_back({dimension(l->second,a.left.column),dimension(r->second,a.right.column),id,false});continue;}
                const auto local=left?a.left:a.right,outer=left?a.right:a.left;
                request.tests.push_back({dimension((left?l:r)->second,local.column),outer,left?a.op:inverse(a.op),id});
            }
            merged.requests.push_back(std::move(request));
        }
        const auto column=group.first.first;
        const std::uint64_t bytes=std::uint64_t(host_.ranks(column))*sizeof(rank_summaries::Slot)+
            std::uint64_t(host_.rows(column))*(sizeof(std::uint64_t)+merged.columns.size()*sizeof(std::uint32_t));
        if(bytes>summary_budget_||summary_reserved_>summary_budget_-bytes)continue;
        // Reserve once, not once per request. No arrays or rows are filled
        // here; the first actual target arrival performs the sole fill.
        SummaryPlan plan;plan.scope=merged.requests.front().scope;plan.column=column;
        plan.driver=drafts[group.second[begin]].plan.driver;
        plan.merged_index=merged_frontiers_.size();plan.signature="merged-driver:"+std::to_string(column)+":"+std::to_string(group.first.second);
        plan.bank=store_.add_summary(host_.ranks(column),{});
        auto &bank=store_.summaries[plan.bank];bank.merged_mode=true;
        bank.merged_request_count=merged.requests.size();bank.reserved_bytes=bytes;
        bank.merged.width=merged.requests.size();bank.merged.dimensions=merged.columns.size();
        bank.merged.tests.resize(merged.requests.size());
        bank.present_ranks=present_count(host_,column,0);bank.present_ranks_known=true;
        // src_keep deliberately has no frontier density admission rule.
        bank.measured_admission=false;bank.tablewide=false;
        summary_reserved_+=bytes;
        const unsigned id=summary_plans_.size();
        for(unsigned bit=0;bit<merged.requests.size();++bit){const auto&r=merged.requests[bit];
            std::vector<SummaryTest> tests;
            for(const auto&t:r.tests){bank.merged.tests[bit].push_back({t.dimension,t.op});
                SummaryTest test;test.atom=t.atom;test.outer=t.outer;test.op=t.op;
                const auto &a=atoms_[t.atom];test.local=atoms_[t.atom].left==t.outer?a.right:a.left;tests.push_back(test);}
            summary_requests_[r.scope]={int(id),std::move(tests),bit};
            const auto&draft=drafts[group.second[begin+bit]].plan;
            summary_requests_[r.scope].source=draft.steps.front().source;summary_requests_[r.scope].column=column;
            summary_entered_[r.scope]=column;summary_test_counts_[r.scope]=r.tests.size();summary_ineligible_[r.scope].clear();
            plan.requests.push_back(r.scope);
        }
        // Index only equality dimensions REQUIRED by every request. A
        // missing/private test accepts everything, so it cannot restrict
        // a shared index. Other requests/operators retain the full scan.
        for(unsigned dim=0;dim<merged.columns.size();++dim){bool common=true;
            for(const auto&r:merged.requests){bool found=false;
                for(const auto&t:r.tests)if(t.dimension==dim&&t.op==1)found=true;
                common&=found;}
            if(common)bank.merged.equalities.push_back(dim);
        }
        for(const auto&s:merged.steps){SummaryStep step;step.column=s.column;step.occurrence=s.occurrence;step.scope=s.scope;step.stage=s.stage;
            plan.steps.push_back(step);NodeWork work;work.column=s.column;work.request_width=merged.requests.size();plan.work.push_back(work);}
        merged_frontiers_.push_back(std::move(merged));summary_plans_.push_back(std::move(plan));
    }
}

void fill_merged_frontier(const SummaryPlan &plan,unsigned rank){
    auto &bank=store_.summaries[plan.bank];const auto&p=merged_frontiers_[plan.merged_index];
    std::vector<std::int64_t> rows(p.steps.size(),-1);
    std::vector<rank_merged::Vector> complete;
    bank.active_rank=rank;bank.fill_active=true;
    {rank_summaries::Summary::Phase phase(bank.collection_ns);
    summary_slice(plan.column,rank,plan.work[0],[&](unsigned root_row){
        host_.interrupt();std::fill(rows.begin(),rows.end(),-1);rows[0]=root_row;
        ++bank.fill_rows_visited;++bank.measured_rows;++bank.candidates;
        ++bank.merged_rows_read;
        // Resolve each shared/private functional path once. A missing row
        // clears only the bits that require that particular path.
        for(unsigned i=1;i<p.steps.size();++i){const auto&s=p.steps[i];
            if(rows[s.source_row]<0)continue;
            const auto pivot=host_.rank(s.source_column,rows[s.source_row]);if(pivot==null_rank)continue;
            reached(plan.work[i],s.column,pivot);
            host_.visit(s.column,1,pivot,[&](unsigned row){rows[i]=row;
                ++bank.merged_rows_read;++counters.witness_rows;++counters.tight_slice_rows;CF_COUNT(++plan.work[i].witness_rows);
                return true;});++counters.unique_hops;
        }
        rank_merged::Vector point;point.ranks.resize(p.columns.size(),null_rank);
        for(unsigned d=0;d<p.columns.size();++d){const auto&c=p.columns[d];
            if(rows[c.row]>=0)point.ranks[d]=host_.rank(c.column,rows[c.row]);}
        for(unsigned bit=0;bit<p.requests.size();++bit){const auto&r=p.requests[bit];bool good=!r.impossible;
            for(auto row:r.required)good&=rows[row]>=0;
            if(!good)continue;
            for(auto test:r.fixed){const auto left=point.ranks[test.left];
                if(left==null_rank){good=false;break;}
                if(test.constant)good=summary_literal(left,atoms_[test.atom])==Truth::yes;
                else {const auto right=point.ranks[test.right];good=right!=null_rank&&compare(left,atoms_[test.atom].op,right);}
                if(!good)break;
            }
            for(auto test:r.tests)if(point.ranks[test.dimension]==null_rank){good=false;break;}
            if(good)point.mask|=std::uint64_t{1}<<bit;
        }
        // All requests' fixed tests were evaluated against this SAME row
        // vector. No filled value, row id, or precomputed key set is stored.
        if(point.mask)complete.push_back(std::move(point));
        bank.fill_input_bytes=complete.capacity()*sizeof(rank_merged::Vector);
        return false;
    });}
    PackedRankDecisionStore::Record(bank,rank,complete,[&](){host_.interrupt();});
    bank.fill_active=false;bank.fill_input_bytes=0;
    CF_COUNT(++plan.work.front().summary_fills;plan.work.front().frontier_points+=bank.payload().slots[rank].count;);
}

Ref merged_alias(Ref ref,const std::map<int,int>*aliases)const{
    if(aliases){auto found=aliases->find(ref.occurrence);if(found!=aliases->end())ref.occurrence=found->second;}
    return ref;
}

std::uint64_t answer_merged_frontier(const SummaryPlan &plan,unsigned rank,const std::vector<MergedArrival>&arrivals){
    auto &bank=store_.summaries[plan.bank];const auto&p=merged_frontiers_[plan.merged_index];
    rank_summaries::Summary::Phase phase(bank.probe_ns);++bank.frontier_arrivals;
    std::uint64_t live=0,requested=0;auto &inputs=merged_inputs_;auto &keys=merged_keys_;inputs.clear();
    std::size_t used_keys=0;const bool grouped=!bank.merged.equalities.empty();
    auto value=[&](Ref ref){return bound_rank(ref);};
    for(const auto&arrival:arrivals){const auto bit=summary_requests_[arrival.scope].bit;
        const auto mask=std::uint64_t{1}<<bit;const auto&r=p.requests[bit];bool guard=true;
        requested|=mask;
        for(int id:r.guards){const auto&a=atoms_[id];const auto left=value(merged_alias(a.left,arrival.aliases));
            if(a.constant)guard=summary_literal(left,a)==Truth::yes;
            else {const auto right=value(merged_alias(a.right,arrival.aliases));guard=left!=null_rank&&right!=null_rank&&compare(left,a.op,right);}
            if(!guard)break;
        }
        if(!guard)continue;live|=mask;
        if(grouped){if(used_keys==keys.size())keys.emplace_back();auto &key=keys[used_keys++];key.mask=mask;key.ranks.clear();
            for(auto d:bank.merged.equalities){
                auto test=std::find_if(r.tests.begin(),r.tests.end(),[&](const MergedTest&t){return t.dimension==d&&t.op==1;});
                key.ranks.push_back(value(merged_alias(test->outer,arrival.aliases)));
            }
        }
        for(const auto&t:r.tests){const auto filled=value(merged_alias(t.outer,arrival.aliases));
            unsigned index=0;for(;index<inputs.size();++index)if(inputs[index].dimension==t.dimension&&inputs[index].value==filled)break;
            if(index==inputs.size()){rank_merged::Input in;in.dimension=t.dimension;in.value=filled;inputs.push_back(in);}
            auto&input=inputs[index];const auto accept=collective_fill::outcomes(t.op);
            // Repeated tests on one local column and filled value are AND,
            // not OR: this also handles two-sided/equality combinations.
            const bool seen=(input.present&mask)!=0;
            for(unsigned o=0;o<3;++o){if(!(accept&(1U<<o)))input.accept[o]&=~mask;
                else if(!seen)input.accept[o]|=mask;}
            input.present|=mask;
        }
    }
    keys.resize(used_keys);
    if(!live){counters.exhaustions+=__builtin_popcountll(requested);return 0;}
    const auto &slot=bank.view.slot(rank);const auto previous=bank.merged.points_checked;
    const auto searches=bank.merged.equality_searches;
    const auto answer=bank.merged.lookup(slot.offset,slot.count,live,inputs,keys,[&](){host_.interrupt();});
    bank.checks+=bank.merged.points_checked-previous;bank.equality_searches+=bank.merged.equality_searches-searches;
    counters.first_witness_stops+=__builtin_popcountll(answer);
    counters.exhaustions+=__builtin_popcountll(requested&~answer);
    return answer;
}
