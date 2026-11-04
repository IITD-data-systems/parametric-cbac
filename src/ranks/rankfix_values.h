#pragma once
#include <string>
#include <string_view>
#include <cmath>
#include <cstdlib>
#include <stdexcept>
#include <algorithm>

// Compare decimal values exactly, including scientific notation and SQL NaN ordering.
struct RankFixDecimal {
    int sign=0, special=0;
    long long power=0;
    std::string digits;
};
inline RankFixDecimal rankfix_decimal(std::string_view raw) {
    RankFixDecimal out;
    std::string value(raw);
    if(value=="NaN" || value=="nan") {out.special=2;return out;}
    std::size_t pos=0;int sign=1;
    if(pos<value.size() && (value[pos]=='+' || value[pos]=='-')) {if(value[pos]=='-')sign=-1;++pos;}
    if(value.substr(pos)=="Infinity" || value.substr(pos)=="inf") {out.special=sign;return out;}
    long long fractional=0,exponent=0;bool dot=false,any=false;
    while(pos<value.size() && value[pos]!='e' && value[pos]!='E') {
        const char c=value[pos++];
        if(c=='.' && !dot) {dot=true;continue;}
        if(c<'0' || c>'9') throw std::runtime_error("invalid numeric dictionary value: "+value);
        any=true;out.digits+=c;if(dot)++fractional;
    }
    if(!any)throw std::runtime_error("empty numeric dictionary value");
    if(pos<value.size()) {char *end=nullptr;exponent=std::strtoll(value.c_str()+pos+1,&end,10);
        if(!end || end!=value.c_str()+value.size())throw std::runtime_error("invalid numeric exponent");}
    auto first=out.digits.find_first_not_of('0');
    if(first==std::string::npos) {out.digits="0";return out;}
    out.digits.erase(0,first);out.sign=sign;
    out.power=exponent-fractional+static_cast<long long>(out.digits.size());
    while(out.digits.size()>1 && out.digits.back()=='0')out.digits.pop_back();
    return out;
}
inline int rankfix_numeric_compare(std::string_view left,std::string_view right,int kind) {
    if(kind==2) {
        char *aend=nullptr,*bend=nullptr;std::string a(left),b(right);
        double x=std::strtod(a.c_str(),&aend),y=std::strtod(b.c_str(),&bend);
        if(aend!=a.c_str()+a.size() || bend!=b.c_str()+b.size())throw std::runtime_error("invalid float value");
        if(std::isnan(x))return std::isnan(y)?0:1;
        if(std::isnan(y))return -1;
        return x<y?-1:x>y?1:0;
    }
    const auto a=rankfix_decimal(left),b=rankfix_decimal(right);
    if(a.special || b.special) {
        auto order=[](const RankFixDecimal &v){return v.special==2?3:v.special==1?2:v.special==-1?0:1;};
        return order(a)<order(b)?-1:order(a)>order(b)?1:0;
    }
    if(a.sign!=b.sign)return a.sign<b.sign?-1:1;
    if(!a.sign)return 0;
    if(a.power!=b.power)return (a.power<b.power?-1:1)*a.sign;
    const auto length=std::max(a.digits.size(),b.digits.size());
    for(std::size_t i=0;i<length;++i) {
        char x=i<a.digits.size()?a.digits[i]:'0',y=i<b.digits.size()?b.digits[i]:'0';
        if(x!=y)return (x<y?-1:1)*a.sign;
    }
    return 0;
}
