// Independent integer replay. Build with a C++20 compiler and pass prices.txt.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <numeric>
#include <stdexcept>
#include <string>
#include <vector>

namespace {
using Mask = unsigned;
using Matching = std::array<int, 18>;
using Lengths = std::vector<int>;
constexpr int root = 17;
constexpr Mask rootBit = 1u << root, ordinary = rootBit - 1, full = 2 * rootBit - 1;
constexpr int numTypes = 15;
int edgeId(int a, int b) { return std::max(a,b)*(std::max(a,b)-1)/2 + std::min(a,b); }
int low(Mask s) { return std::countr_zero(s); }
struct Record {
    Lengths lengths;
    int both;
    std::array<int,153> price;
    std::array<std::array<int,numTypes>,numTypes> transfer;
};
using Records = std::array<Record,numTypes>;
void require(bool condition, const char* message) {
    if (!condition) throw std::runtime_error(message);
}
Records read(std::istream& in) {
    Records rows{};
    for (auto& r : rows) {
        int n = 0;
        in >> n;
        require(1 <= n && n <= 4, "malformed cycle list");
        r.lengths.resize(n);
        for (int& l : r.lengths) in >> l;
        in >> r.both;
        for (int& f : r.price) in >> f;
        for (auto& a : r.transfer) for (int& f : a) in >> f;
        require(bool(in), "incomplete table");
    }
    std::string extra;
    require(!(in >> extra), "trailing input");
    return rows;
}
void typeLists(int rest, int smallest, Lengths& list, std::map<Lengths,int>& types) {
    if (!rest) { types.emplace(list,0); return; }
    for (int k=smallest; k<=rest; k+=2) {
        list.push_back(k);
        typeLists(rest-k,k,list,types);
        list.pop_back();
    }
}
std::map<Lengths,int> typeIndex(const Records& rows) {
    std::map<Lengths,int> expected, index;
    for (int r=4; r<=18; r+=2) {
        Lengths l{r};
        typeLists(18-r,4,l,expected);
    }
    for (int i=0; i<numTypes; ++i) {
        require(expected.contains(rows[i].lengths), "invalid pair type");
        index.emplace(rows[i].lengths,i);
    }
    require(index.size()==expected.size() && index.size()==numTypes, "missing pair type");
    return index;
}
std::pair<Matching,Matching> representative(const Lengths& lengths) {
    Matching a{}, b{};
    auto point=[](int k){return k==0 ? root : k==root ? 0 : k;};
    int start=0;
    for (int n : lengths) {
        for (int i=0; i<n; i+=2) {
            int u=point(start+i), v=point(start+i+1), w=point(start+(i+2)%n);
            a[u]=v; a[v]=u; b[v]=w; b[w]=v;
        }
        start+=n;
    }
    return {a,b};
}
Lengths cycleType(const Matching& a, const Matching& b) {
    Mask todo=full;
    Lengths cycles;
    while (todo) {
        int start=cycles.empty() ? root : low(todo), v=start, n=0;
        do { todo &= ~(1u<<v); v=n%2==0 ? a[v] : b[v]; ++n; } while (v!=start);
        cycles.push_back(n);
    }
    std::sort(cycles.begin()+1,cycles.end());
    return cycles;
}
struct Counts {
    std::vector<int> freq = std::vector<int>(full+1);
    int all=0, one=0, both=0;
};
std::vector<unsigned char> closed(const Matching& m) {
    std::vector<Mask> sides{0};
    for (int i=0;i<18;++i) if (i<m[i]) {
        Mask e=(1u<<i)|(1u<<m[i]); int size=sides.size();
        for (int j=0;j<size;++j) sides.push_back(sides[j]|e);
    }
    std::vector<unsigned char> table(full+1);
    for (Mask s : sides) table[s]=1;
    return table;
}
Counts countGroupings(const Matching& a,const Matching& b) {
    auto ca=closed(a), cb=closed(b);
    std::vector<unsigned char> hit(full+1);
    for (Mask s=0;s<=full;++s) hit[s]=ca[s]+2*cb[s];
    Counts result;
    std::array<Mask,6> blocks{};
    blocks[0]=rootBit;
    for (Mask big=1;big<=ordinary;++big) if (std::popcount(big)==5) {
        blocks[1]=big;
        auto visit=[&](auto& self,Mask left,int i,int known)->void {
            if (i==6) {
                ++result.all;
                result.one+=known&1;
                if (known!=3) return;
                ++result.both;
                for (int j=0;j<6;++j) for (int k=0;k<j;++k)
                    ++result.freq[blocks[j]|blocks[k]];
                return;
            }
            Mask first=left&-left;
            for (Mask x=left^first;x;x&=x-1)
                for (Mask y=x&(x-1);y;y&=y-1) {
                    Mask t=first|(x&-x)|(y&-y);
                    int h=known;
                    for (int j=0;j<i;++j) h|=hit[t|blocks[j]];
                    blocks[i]=t;
                    self(self,left^t,i+1,h);
                }
        };
        visit(visit,ordinary^big,2,hit[rootBit|big]);
    }
    return result;
}
struct TripleCheck {
    const Record& row;
    const std::map<Lengths,int>& types;
    const Matching& a;
    const Matching& b;
    const std::vector<int>& freq;
    Matching third{};
    std::array<Mask,9> edges{};
    std::array<Mask,36> pairs{};
    std::array<Mask,84> triples{};
    int minimumTransfer = 0;
    std::uint64_t checked=0;
    void visit(Mask left,int depth,int nPairs,int nTriples,int cost,std::int64_t fee) {
        if (!left) {
            ++checked;
            if (2*cost <= fee+minimumTransfer) return;
            int s=types.at(cycleType(a,third)), t=types.at(cycleType(b,third));
            require(2*cost<=fee+row.transfer[s][t],"a third matching exceeds its budget");
            return;
        }
        int u=low(left);
        Mask rest=left^(1u<<u), partners=rest&~((1u<<a[u])|(1u<<b[u]));
        for (;partners;partners&=partners-1) {
            int v=low(partners);
            Mask e=(1u<<u)|(1u<<v);
            third[u]=v; third[v]=u;
            int next=cost;
            for (int j=0;j<depth;++j) next+=freq[e|edges[j]];
            for (int j=0;j<nPairs;++j) next+=freq[e|pairs[j]];
            for (int j=0;j<nTriples;++j) next+=freq[e|triples[j]];
            edges[depth]=e;
            for (int j=0;j<depth;++j) pairs[nPairs+j]=e|edges[j];
            for (int j=0;j<nPairs;++j) triples[nTriples+j]=e|pairs[j];
            visit(rest^(1u<<v),depth+1,nPairs+depth,nTriples+nPairs,next,fee+row.price[edgeId(u,v)]);
        }
    }
};
}
int main(int argc,char** argv) {
    try {
        if (argc!=2) throw std::runtime_error("usage: check prices.txt");
        std::ifstream input(argv[1]);
        auto rows=read(input);
        auto types=typeIndex(rows);
        std::int64_t gain=100000000, transferUpper=0;
        std::uint64_t checked=0;
        for (int i=0;i<numTypes;++i) {
            auto& row=rows[i];
            auto [a,b]=representative(row.lengths);
            auto counts=countGroupings(a,b);
            require(counts.all==95295200 && counts.one==8230880 && counts.both==row.both,"grouping count mismatch");
            int minTransfer=100000000;
            std::int64_t priceTotal=0;
            for (int u=0;u<18;++u) for (int v=0;v<u;++v)
                if (a[u]!=v && b[u]!=v) priceTotal+=row.price[edgeId(u,v)];
            for (int j=0;j<numTypes;++j) for (int k=0;k<numTypes;++k) {
                require(row.transfer[j][k]==row.transfer[k][j],"transfer is asymmetric");
                minTransfer=std::min(minTransfer,row.transfer[j][k]);
                transferUpper=std::max(transferUpper,std::int64_t(row.transfer[j][k])+rows[j].transfer[k][i]+rows[k].transfer[i][j]);
            }
            TripleCheck tc{row,types,a,b,counts.freq};
            tc.minimumTransfer=minTransfer;
            tc.visit(full,0,0,0,0,0);
            checked+=tc.checked;
            gain=std::min(gain,10*std::int64_t(counts.both)-priceTotal);
            std::cout<<"Type "<<i+1<<": "<<counts.both<<" double failures, "<<tc.checked<<" third colors checked.\n"<<std::flush;
        }
        std::int64_t lower=12LL*(95295200-17*8230880)+136LL*gain-680LL*transferUpper;
        require(gain>=3973540 && transferUpper<=1 && lower>=4843640,"insufficient lower bound");
        std::cout<<checked<<" rooted third-color checks. At least "<<(lower+11)/12<<" successful groupings.\n";
    } catch(const std::exception& e) {
        std::cerr<<e.what()<<"\n";return 1;
    }
}
