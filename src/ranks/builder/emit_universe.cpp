// Offline, operator-blind conversion. Existing bundles are read-only.
#include "universe_format.h"
#include "rankfix_values.h"
#include <algorithm>
#include <cerrno>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <map>
#include <numeric>
#include <string>
#include <vector>
#include <fcntl.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

namespace fs=std::filesystem;
using universe_format::read32;
using universe_format::require;
struct Mapping {
    const unsigned char *data=nullptr;std::size_t size=0;int fd=-1;
    explicit Mapping(const fs::path &path) {
        fd=open(path.c_str(),O_RDONLY|O_CLOEXEC);require(fd>=0,"cannot open source artifact");
        struct stat s{};require(fstat(fd,&s)==0 && s.st_size>=0,"cannot stat source artifact");size=s.st_size;
        if(size) { const auto p=mmap(nullptr,size,PROT_READ,MAP_PRIVATE,fd,0);
            require(p!=MAP_FAILED,"cannot map source artifact");data=static_cast<const unsigned char *>(p); }
    }
    ~Mapping(){if(data)munmap(const_cast<unsigned char *>(data),size);if(fd>=0)close(fd);}
    Mapping(const Mapping&)=delete;Mapping&operator=(const Mapping&)=delete;
};
struct Output {
    fs::path path;int fd=-1;
    explicit Output(const fs::path &p):path(p) {
        fs::create_directories(p.parent_path());fd=open(p.c_str(),O_WRONLY|O_CREAT|O_EXCL|O_CLOEXEC,0644);
        require(fd>=0,"destination exists or cannot be created; never overwriting");
    }
    ~Output(){if(fd>=0)close(fd);}
    void bytes(const void *p,std::size_t n) {
        auto s=static_cast<const unsigned char *>(p);
        while(n) { const auto got=write(fd,s,n);if(got<0 && errno==EINTR)continue;
            require(got>0,"artifact write failed");s+=got;n-=got; }
    }
    void word(std::uint32_t n) { unsigned char b[]={static_cast<unsigned char>(n),static_cast<unsigned char>(n>>8),
        static_cast<unsigned char>(n>>16),static_cast<unsigned char>(n>>24)};bytes(b,4); }
    void finish(){require(fsync(fd)==0,"artifact fsync failed");require(close(fd)==0,"artifact close failed");fd=-1;}
};
std::map<std::string,std::string> metadata(const fs::path &p) {
    std::ifstream in(p);require(bool(in),"missing metadata file");std::map<std::string,std::string> out;
    for(std::string line;std::getline(in,line);) { if(line.empty())continue;
        const auto pos=line.find('=');require(pos!=std::string::npos,"bad metadata row");
        require(out.emplace(line.substr(0,pos),line.substr(pos+1)).second,"duplicate metadata entry"); }
    return out;
}
struct Universe {
    std::vector<std::uint32_t> by_token,representatives;int kind=0;
};
Universe build_domain(const fs::path &src,const fs::path &dst,const std::string &id,int kind) {
    Mapping raw(src/"dict/domain"/id),old_rank(src/"rank/domain"/id);
    std::vector<std::string_view> values;
    for(std::size_t pos=0;pos<raw.size;) {
        require(raw.size-pos>=4,"truncated source dictionary");const auto n=read32(raw.data+pos);pos+=4;
        require(n<=raw.size-pos,"truncated source dictionary value");
        values.emplace_back(reinterpret_cast<const char *>(raw.data+pos),n);pos+=n;
    }
    require(values.size()<UINT32_MAX && old_rank.size==values.size()*4ULL,"source domain length mismatch");
    Universe u;u.kind=kind;std::vector<std::uint32_t> ordered(values.size(),UINT32_MAX);
    for(std::uint32_t tok=0;tok<values.size();++tok) {
        const auto rank=read32(old_rank.data+4ULL*tok);
        require(rank<values.size() && ordered[rank]==UINT32_MAX,"source rank map is not a permutation");ordered[rank]=tok;
    }
    const auto compare=[&](std::uint32_t a,std::uint32_t b) {
        return kind ? rankfix_numeric_compare(values[a],values[b],kind) : values[a].compare(values[b]);
    };
    if(!std::is_sorted(ordered.begin(),ordered.end(),[&](auto a,auto b){return compare(a,b)<0;}))
        std::stable_sort(ordered.begin(),ordered.end(),[&](auto a,auto b){return compare(a,b)<0;});
    u.by_token.resize(values.size());
    for(auto tok:ordered) {
        if(u.representatives.empty() || compare(u.representatives.back(),tok)!=0)u.representatives.push_back(tok);
        u.by_token[tok]=u.representatives.size()-1;
    }
    // Random-access values in universe order: one logarithmic constant placement, no online decode.
    std::vector<std::uint32_t> offsets;offsets.reserve(u.representatives.size()+1);std::uint64_t size=0;
    for(auto tok:u.representatives) { offsets.push_back(size);size+=values[tok].size();require(size<=UINT32_MAX,"UDX1 payload too large"); }
    offsets.push_back(size);
    require(16ULL+4ULL*offsets.size()+size<1073741800ULL,"universe dictionary exceeds PostgreSQL bytea limit");
    Output dict(dst/"universe/domain"/id);dict.bytes("UDX1",4);dict.word(u.representatives.size());dict.word(kind);dict.word(0);
    for(auto n:offsets)dict.word(n);for(auto tok:u.representatives)dict.bytes(values[tok].data(),values[tok].size());dict.finish();
    // Packed code tokens remain unchanged. Only their offline rank map changes in this new bundle.
    Output ranks(dst/"rank/domain"/id);for(auto n:u.by_token)ranks.word(n);ranks.finish();
    std::cout<<"DOMAIN,"<<id<<",ranks="<<u.representatives.size()<<",tokens="<<values.size()<<",kind="<<kind<<"\n";
    return u;
}
void build_column(const fs::path &src,const fs::path &dst,const std::string &key,const Universe &u) {
    const auto dot=key.find('.');require(dot!=std::string::npos,"unqualified column");
    const auto table=key.substr(0,dot), col=key.substr(dot+1);
    Mapping cix(src/"canon_invidx"/table/col),base(src/(table+"_code_base"));
    require(cix.size>=16 && std::memcmp(cix.data,"CIX1",4)==0,"source index is not CIX1");
    require(base.size>=20 && std::memcmp(base.data,"CB04",4)==0,"source base is not CB04");
    const auto old_count=read32(cix.data+4),nonnull=read32(cix.data+8),rows=read32(base.data+4);
    const auto child_at=12ULL+4ULL*(old_count+1ULL),present_at=child_at+4ULL*nonnull;
    require(present_at+4<=cix.size,"truncated source index");
    const auto old_present=read32(cix.data+present_at);
    const auto token_at=present_at+4ULL+4ULL*old_present;
    require(token_at+4ULL*old_count==cix.size,"CIX1 token array mismatch");
    require(nonnull<=rows && read32(cix.data+12+4ULL*old_count)==nonnull,"source index row mismatch");
    const auto count=static_cast<std::uint32_t>(u.representatives.size());
    std::vector<std::uint32_t> counts(count,0),offsets(count+1,0),local_to_universe(old_count),present;
    for(std::uint32_t local=0;local<old_count;++local) {
        const auto tok=read32(cix.data+token_at+4ULL*local);require(tok<u.by_token.size(),"source canonical token invalid");
        const auto rank=u.by_token[tok];local_to_universe[local]=rank;
        const auto lo=read32(cix.data+12+4ULL*local),hi=read32(cix.data+12+4ULL*(local+1));
        require(lo<=hi && hi<=nonnull,"source offsets invalid");counts[rank]+=hi-lo;
    }
    bool unique=true;
    for(std::uint32_t rank=0;rank<count;++rank) {
        offsets[rank+1]=offsets[rank]+counts[rank];if(counts[rank])present.push_back(rank);unique=unique && counts[rank]<=1;
    }
    require(offsets.back()==nonnull,"converted index count mismatch");
    std::vector<std::uint32_t> children(nonnull),forward(rows,UINT32_MAX),cursor(offsets.begin(),offsets.end()-1);
    for(std::uint32_t local=0;local<old_count;++local) {
        const auto rank=local_to_universe[local],lo=read32(cix.data+12+4ULL*local),hi=read32(cix.data+12+4ULL*(local+1));
        for(auto i=lo;i<hi;++i) {
            const auto row=read32(cix.data+child_at+4ULL*i);require(row<rows && forward[row]==UINT32_MAX,"invalid/duplicate witness row");
            forward[row]=rank;children[cursor[rank]++]=row;
        }
    }
    // Aliased numeric representations may have merged. Preserve sorted postings after merging.
    for(auto rank:present)std::sort(children.begin()+offsets[rank],children.begin()+offsets[rank+1]);
    const auto bytes=20ULL+4ULL*offsets.size()+4ULL*children.size()+4ULL*present.size();
    require(bytes<1073741800ULL && 16ULL+4ULL*rows<1073741800ULL,"column index exceeds PostgreSQL bytea limit");
    Output inv(dst/"canon_invidx"/table/col);inv.bytes("CIX2",4);inv.word(count);inv.word(nonnull);inv.word(present.size());inv.word(unique);
    for(auto n:offsets)inv.word(n);for(auto n:children)inv.word(n);for(auto n:present)inv.word(n);inv.finish();
    Output fwd(dst/"canon_fwdidx"/table/col);fwd.bytes("CFI2",4);fwd.word(rows);fwd.word(count);fwd.word(0);
    for(auto n:forward)fwd.word(n);fwd.finish();
    std::cout<<"COLUMN,"<<key<<",universe_ranks="<<count<<",local_ranks_before="<<old_count<<",present="<<present.size()
             <<",rows="<<rows<<",nonnull="<<nonnull<<",unique="<<unique<<",bytes="<<bytes+16ULL+4ULL*rows<<"\n";
}
int main(int argc,char **argv) {
    try {
        require(argc==4,"usage: emit_universe <read-only-source-bundle> <new-output-directory> <domain-kinds-file>");
        const fs::path src=fs::canonical(argv[1]),dst=fs::absolute(argv[2]);require(!fs::exists(dst),"output directory already exists");
        auto cols=metadata(src/"meta/col_domain"),kinds=metadata(argv[3]);
        std::map<std::string,std::vector<std::string>> groups;for(const auto &[col,id]:cols)groups[id].push_back(col);
        fs::create_directories(dst);
        for(const auto &[id,columns]:groups) {
            require(kinds.count(id),"missing declared datatype for universe");const auto kind=std::stoi(kinds.at(id));
            require(kind>=0 && kind<=2,"unsupported universe type");auto u=build_domain(src,dst,id,kind);
            for(const auto &col:columns)build_column(src,dst,col,u);
        }
        Output manifest(dst/"meta/canon_invidx");const std::string text="format=CIX2\nforward=CFI2\nranking=full_universe\nconstants=UDX1\n";
        manifest.bytes(text.data(),text.size());manifest.finish();return 0;
    }catch(const std::exception &e){std::cerr<<"UNIVERSE_BUILD_FAILED: "<<e.what()<<"\n";return 1;}
}
