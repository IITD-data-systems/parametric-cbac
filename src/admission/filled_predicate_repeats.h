#pragma once
#include <algorithm>
#include <map>
#include <set>
#include <utility>
#include <vector>

namespace filled_predicate_reuse {
// Metadata-only estimate for an entered rank with its outside values filled
// into the predicate. This defines NO tuple-keyed decision store.
// This is an admission estimate, not a decision or a precomputed key set.
// Key identifies (occurrence, runtime column). Equalities come only from the
// asking branch's mandatory conjunction, never a local OR alternative.
using Key=std::pair<int,std::size_t>;
struct Header {double rows,present;};
template<class Headers>
double distinct_estimate(const std::vector<Key> &keys,
        const std::vector<std::pair<Key,Key>> &equalities,Headers header) {
    std::map<Key,Key> parent;
    for(const auto &key:keys)parent.emplace(key,key);
    for(const auto &e:equalities){parent.emplace(e.first,e.first);parent.emplace(e.second,e.second);}
    const auto root=[&](Key key){while(parent.at(key)!=key)key=parent.at(key);return key;};
    for(const auto &e:equalities)parent[root(e.first)]=root(e.second);
    double product=1;
    std::set<Key> unique;
    for(const auto &key:keys)if(unique.insert(key).second)
        product=std::min(1e100,product*std::max(1.0,header(key).present));
    std::set<int> occurrences;
    for(const auto &entry:parent)occurrences.insert(entry.first.first);
    for(int occurrence:occurrences) {
        bool complete=true;double rows=0;
        for(const auto &key:keys) {
            bool matched=false;
            for(const auto &entry:parent)if(entry.first.first==occurrence && root(entry.first)==root(key)) {
                matched=true;rows=std::max(rows,header(entry.first).rows);break;
            }
            if(!matched){complete=false;break;}
        }
        // Only if the entering value AND every filled operand can be read
        // from one occurrence. This bounds supported predicate instances;
        // it neither constructs those instances nor changes their identity.
        // An outside operand not mapped there prevents this cap. Absent
        // combinations can still occur, so this remains an admission heuristic.
        if(complete)product=std::min(product,std::max(1.0,rows));
    }
    return product;
}
}
