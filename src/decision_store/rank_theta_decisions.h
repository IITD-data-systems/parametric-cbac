#pragma once
#include "rank_request_decisions.h"
#include <array>

// Lemma-6 theta transfer. These objects answer predicates in the filled
// operands' universes. They have no API returning a row attribute or row id.
namespace rank_theta {
struct Boundary {
    std::array<rank_requests::Range,2> yes{};
    unsigned char count=0,null_local=1;
    unsigned truth(unsigned value)const{
        if(null_local || value==UINT32_MAX)return 2;
        for(unsigned i=0;i<count;++i)if(value>=yes[i].lo && value<yes[i].hi)return 1;
        return 0;
    }
    bool accepts_interval(rank_requests::Range interval)const{
        if(null_local)return false;
        for(unsigned i=0;i<count;++i)if(yes[i].lo>=interval.lo && yes[i].hi<=interval.hi)return true;
        return false;
    }
};
inline Boundary transfer(unsigned local,int op,unsigned domain){
    Boundary result;if(local==UINT32_MAX)return result;result.null_local=0;
    auto add=[&](unsigned lo,unsigned hi){if(lo<hi)result.yes[result.count++]={lo,hi};};
    auto successor=local>=domain?domain:local+1;auto at=std::min(local,domain);
    // local OP filled: predicates are stored as ranges of the FILLED value.
    switch(op){case 1:add(at,successor);break;case 2:add(successor,domain);break;
        case 3:add(at,domain);break;case 4:add(0,at);break;
        case 5:add(0,successor);break;case 6:add(0,at);add(successor,domain);break;
        default:throw std::logic_error("unknown theta operator");}
    return result;
}
inline rank_requests::Set whole(unsigned domain){rank_requests::Set s;s.add(0,domain);s.null_good=true;return s;}
inline rank_requests::Set negate(const rank_requests::Set &s,unsigned domain){
    rank_requests::Set result;unsigned at=0;
    for(auto r:s.ranges){result.add(at,r.lo);at=r.hi;}result.add(at,domain);result.null_good=!s.null_good;return result;
}
inline rank_requests::Set unite(rank_requests::Set a,const rank_requests::Set &b){
    for(auto r:b.ranges)a.add(r.lo,r.hi);a.null_good|=b.null_good;return a;
}
inline rank_requests::Set meet(const rank_requests::Set &a,const rank_requests::Set &b){
    rank_requests::Set result;result.null_good=a.null_good&&b.null_good;
    for(auto x:a.ranges)for(auto y:b.ranges)result.add(std::max(x.lo,y.lo),std::min(x.hi,y.hi));return result;
}
struct Cell {
    std::array<Boundary,2> axes;
    std::uint64_t R=0;
    std::uint32_t expanded=UINT32_MAX;
    std::uint32_t extra_axes=UINT32_MAX;
};
struct Layout {
    unsigned width=0,dimensions=0,states=1;
    std::array<unsigned,2> domains{};
    std::array<std::vector<int>,2> axis_operators;
    std::array<std::array<unsigned char,64>,2> bit_axes{};
    struct OperatorGroup {unsigned a=0,b=0;std::uint64_t mask=0;};
    std::vector<OperatorGroup> operator_groups;
    std::vector<Boundary> pending_axes;
    unsigned extra_count=0;
    std::uint64_t evaluations=0,projections=0;
    void configure(unsigned w,const std::vector<unsigned>& ds){
        rank_requests::width_mask(w);if(ds.empty() || ds.size()>2)throw std::logic_error("theta dimensions outside 1..2");
        width=w;dimensions=ds.size();for(unsigned i=0;i<dimensions;++i){domains[i]=ds[i];states*=3;}
    }
    void configure_operators(const std::vector<std::vector<int>>& per_bit){
        if(per_bit.size()!=width)throw std::logic_error("theta request operator width mismatch");
        for(unsigned d=0;d<dimensions;++d){
            auto &ops=axis_operators[d];
            for(unsigned bit=0;bit<width;++bit){int op=per_bit[bit].at(d);
                if(op<1 || op>6)throw std::logic_error("invalid theta request operator");
                auto found=std::find(ops.begin(),ops.end(),op);
                if(found==ops.end()){bit_axes[d][bit]=ops.size();ops.push_back(op);}
                else bit_axes[d][bit]=found-ops.begin();
            }
            extra_count+=ops.size()-1;
        }
        for(unsigned bit=0;bit<width;++bit){unsigned a=bit_axes[0][bit],b=dimensions==2?bit_axes[1][bit]:0;
            auto found=std::find_if(operator_groups.begin(),operator_groups.end(),[&](const OperatorGroup& g){return g.a==a && g.b==b;});
            if(found==operator_groups.end())operator_groups.push_back({a,b,std::uint64_t{1}<<bit});
            else found->mask|=std::uint64_t{1}<<bit;
        }
        pending_axes.resize(extra_count);
    }
    std::array<Boundary,2> prepare_axes(const std::array<unsigned,2>& local){
        std::array<Boundary,2> result{};unsigned offset=0;
        for(unsigned d=0;d<dimensions;++d){const auto &ops=axis_operators[d];
            if(ops.empty())throw std::logic_error("theta operators not configured");
            result[d]=transfer(local[d],ops[0],domains[d]);
            for(unsigned i=1;i<ops.size();++i)pending_axes[offset++]=transfer(local[d],ops[i],domains[d]);
        }
        return result;
    }
};
struct Payload {
    std::pmr::vector<Cell> cells;
    std::pmr::vector<std::uint64_t> masks;
    std::pmr::vector<Boundary> extra_axes;
    explicit Payload(std::pmr::memory_resource*m):cells(m),masks(m),extra_axes(m){}
    std::uint64_t bytes()const{return cells.size()*sizeof(Cell)+masks.size()*8+extra_axes.size()*sizeof(Boundary);}
};
inline const Boundary& axis(const Layout&p,const Payload&data,const Cell& cell,unsigned d,unsigned index){
        if(index==0)return cell.axes[d];
        unsigned offset=index-1;
        if(d)offset+=p.axis_operators[0].empty()?0:p.axis_operators[0].size()-1;
        return data.extra_axes[cell.extra_axes+offset];
    }
inline void append_cuts(const Layout&p,const Payload&data,unsigned rank,unsigned d,std::vector<unsigned>& cuts){
        const auto &cell=data.cells[rank];unsigned n=std::max<std::size_t>(1,p.axis_operators[d].size());
        for(unsigned i=0;i<n;++i){const auto &boundary=axis(p,data,cell,d,i);
            for(unsigned j=0;j<boundary.count;++j){cuts.push_back(boundary.yes[j].lo);cuts.push_back(boundary.yes[j].hi);}}
    }
inline void record_theta(const Layout&p,Payload&data,unsigned rank,unsigned cardinality,const std::array<Boundary,2> &axes,const std::array<std::uint64_t,9>& truth){
        if(data.cells.empty())data.cells.resize(cardinality);Cell cell;cell.axes=axes;
        if(p.extra_count){
            if(data.extra_axes.size()>UINT32_MAX-p.extra_count)throw std::overflow_error("theta boundary offset exceeds representation");
            cell.extra_axes=static_cast<std::uint32_t>(data.extra_axes.size());
            data.extra_axes.insert(data.extra_axes.end(),p.pending_axes.begin(),p.pending_axes.end());
        }
        unsigned all_true=p.dimensions==1?1:4;bool conjunction=true;
        for(unsigned i=0;i<p.states;++i)if(i!=all_true && truth[i])conjunction=false;
        cell.R=truth[all_true];
        if(!conjunction){cell.expanded=data.masks.size();data.masks.insert(data.masks.end(),truth.begin(),truth.begin()+p.states);}
        data.cells[rank]=cell;
    }
inline std::uint64_t at(const Layout&p,const Payload&data,const Cell &c,unsigned state){
        return c.expanded==UINT32_MAX?(state==(p.dimensions==1?1U:4U)?c.R:0):data.masks[c.expanded+state];
    }
inline std::uint64_t read_theta(Layout&p,const Payload&data,unsigned rank,const std::array<unsigned,2> &values){
        ++p.evaluations;const auto &c=data.cells[rank];
        if(p.operator_groups.empty()){unsigned state=c.axes[0].truth(values[0]);
            if(p.dimensions==2)state+=3*c.axes[1].truth(values[1]);return at(p,data,c,state);}
        std::array<std::array<unsigned,6>,2> outcomes{};
        for(unsigned d=0;d<p.dimensions;++d)for(unsigned i=0;i<p.axis_operators[d].size();++i)outcomes[d][i]=axis(p,data,c,d,i).truth(values[d]);
        std::uint64_t result=0;
        for(const auto &group:p.operator_groups){unsigned state=outcomes[0][group.a];
            if(p.dimensions==2)state+=3*outcomes[1][group.b];result|=at(p,data,c,state)&group.mask;}
        return result;
    }
inline rank_requests::Set project(Layout&p,const Payload&data,unsigned rank,unsigned bit,const std::array<unsigned,2> &values,int variable,unsigned domain){
        ++p.projections;const auto &c=data.cells[rank];const auto b=std::uint64_t{1}<<bit;
        if(variable<0)return read_theta(p,data,rank,values)&b?whole(domain):rank_requests::Set{};
        unsigned fixed=0;for(unsigned i=0;i<p.dimensions;++i)if(int(i)!=variable)fixed+=(i?3:1)*axis(p,data,c,i,p.bit_axes[i][bit]).truth(values[i]);
        const unsigned stride=variable?3:1;rank_requests::Set result;
        const auto &axis=rank_theta::axis(p,data,c,variable,p.bit_axes[variable][bit]);
        if(axis.null_local){if(at(p,data,c,fixed+2*stride)&b)result=whole(domain);return result;}
        rank_requests::Set positive;for(unsigned i=0;i<axis.count;++i)positive.add(axis.yes[i].lo,axis.yes[i].hi);
        if(at(p,data,c,fixed+stride)&b)result=positive;
        if(at(p,data,c,fixed)&b){auto negative=negate(positive,domain);negative.null_good=false;result=unite(result,negative);}
        result.null_good=(at(p,data,c,fixed+2*stride)&b)!=0;return result;
    }
inline rank_requests::Set project_mask(Layout&p,const Payload&data,unsigned rank,unsigned bit,const std::array<unsigned,2> &values,unsigned variable_mask,unsigned domain){
        if(variable_mask!=3)return project(p,data,rank,bit,values,variable_mask==0?-1:variable_mask==1?0:1,domain);
        // Both comparisons can read the SAME value from above (a window).
        // Partition its universe at their decision boundaries, not at row
        // values, then read the existing truth decision on each interval.
        ++p.projections;const auto &cell=data.cells[rank];std::vector<unsigned> cuts{0,domain};
        for(unsigned i=0;i<p.dimensions;++i){const auto &a=axis(p,data,cell,i,p.bit_axes[i][bit]);
            for(unsigned j=0;j<a.count;++j){cuts.push_back(a.yes[j].lo);cuts.push_back(a.yes[j].hi);}}
        std::sort(cuts.begin(),cuts.end());cuts.erase(std::unique(cuts.begin(),cuts.end()),cuts.end());
        const auto mask=std::uint64_t{1}<<bit;rank_requests::Set result;
        for(unsigned i=0;i+1<cuts.size();++i)if(cuts[i]<cuts[i+1] && (read_theta(p,data,rank,{cuts[i],cuts[i]})&mask))
            result.add(cuts[i],cuts[i+1]);
        result.null_good=(read_theta(p,data,rank,{UINT32_MAX,UINT32_MAX})&mask)!=0;return result;
    }
} // namespace rank_theta
