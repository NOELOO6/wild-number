// c++ -std=c++20 -O3 check.cpp -o check && ./check ../P1F16catalogue 5
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <numeric>
#include <random>
#include <stdexcept>
#include <string>
#include <vector>

using Mask = unsigned;
using Word = std::uint64_t;
using Matching = std::array<Mask, 8>;   // Each edge has two set bits.
using Layout = std::array<Mask, 15>;   // Five root-fours and ten ordinary six-sets.
constexpr Mask full = 65535;

void require(bool value, const char* what) {
    if (!value) throw std::runtime_error(what);
}
Mask low(Mask s) { return s & -s; }

std::vector<Mask> closed_sides(const Matching& m) {
    std::vector<Mask> result;
    for (unsigned i=0; i<8; ++i) for (unsigned j=0; j<i; ++j) {
        result.push_back(m[i]|m[j]);
        for (unsigned k=0; k<j; ++k) result.push_back(m[i]|m[j]|m[k]);
    }
    return result;
}

struct Factorization {
    std::array<Matching,15> matchings{};
    std::array<std::array<unsigned,16>,16> color{};
    std::array<bool,65536> closed{};

    explicit Factorization(std::istream& input) {
        for (auto& row : color) row.fill(15);
        for (unsigned c=0; c<15; ++c) {
            std::string item;
            require(bool(input>>item) && item.size()==16, "invalid catalogue entry");
            Mask used=0;
            for (unsigned i=0; i<8; ++i) {
                unsigned x=item[2*i]-'a', y=item[2*i+1]-'a';
                require(x<16 && y<16 && x!=y && color[x][y]==15, "invalid catalogue edge");
                Mask e=(1u<<x)|(1u<<y);
                require(!(used&e), "edges of a color intersect");
                used|=e;
                matchings[c][i]=e;
                color[x][y]=color[y][x]=c;
            }
            require(used==full,"color misses a vertex");
            for (Mask s : closed_sides(matchings[c])) closed[s]=true;
        }
    }
};

struct Palettes {
    std::vector<Mask> sets;
    unsigned words;
    std::vector<Word> all, contains;

    explicit Palettes(int count) {
        for (Mask p=0; p<32768; ++p) if (std::popcount(p)==count) sets.push_back(p);
        words=(sets.size()+63)/64;
        all.assign(words,~Word(0));
        if (sets.size()%64) all.back()=(Word(1)<<(sets.size()%64))-1;
        contains.assign(15*words,0);
        for (unsigned j=0; j<sets.size(); ++j)
            for (unsigned c=0; c<15; ++c) if (sets[j]&(1u<<c))
                contains[c*words+j/64]|=Word(1)<<(j%64);
    }
};

// For each side, record every palette whose edges can match all of its vertices internally.
// Pair the least vertex to each possible partner, then use the entry for the remaining side.
struct MatchingTable {
    const Palettes& palettes;
    const Factorization& f;
    std::vector<Word> possible;

    MatchingTable(const Palettes& p, const Factorization& factors)
        : palettes(p), f(factors), possible(65536*p.words) {
        unsigned w=p.words;
        std::copy(p.all.begin(),p.all.end(),possible.begin());
        for (Mask s=1; s<full; ++s) {
            int size=std::popcount(s);
            if (size%2 || size>12) continue;
            unsigned x=std::countr_zero(s);
            Mask rest=s^low(s);
            Word* out=&possible[s*w];
            for (Mask ys=rest; ys; ys^=low(ys)) {
                unsigned c=f.color[x][std::countr_zero(ys)];
                const Word* sub=&possible[(rest^low(ys))*w];
                const Word* eligible=&p.contains[c*w];
                for (unsigned j=0; j<w; ++j) out[j]|=sub[j]&eligible[j];
            }
        }
    }

    Word closed(Mask s, unsigned column) const {
        unsigned w=palettes.words;
        return possible[s*w+column]&possible[(full^s)*w+column];
    }
};

template<class Safe>
bool find_layout(Mask root, Mask left, std::array<Mask,5>& blocks, unsigned used, const Safe& safe) {
    if (!left) return true;
    // At this depth the two as yet unchosen triples must have this union.
    if (used==3 && !safe(left)) return false;
    Mask x=low(left);
    for (Mask ys=left^x; ys; ys^=low(ys)) for (Mask zs=ys^low(ys); zs; zs^=low(zs)) {
        Mask t=x|low(ys)|low(zs);
        if (!safe(root|t)) continue;
        bool compatible=true;
        for (unsigned i=0; i<used; ++i) if (!safe(t|blocks[i])) {compatible=false; break;}
        if (compatible) {
            blocks[used]=t;
            if (find_layout(root,left^t,blocks,used+1,safe)) return true;
        }
    }
    return false;
}

template<class Safe>
bool find_layout(Mask root, const Safe& safe) {
    std::array<Mask,5> blocks{};
    return find_layout(root,full^root,blocks,0,safe);
}

// The initial batch accelerates the proof. The exhaustive fallback makes the result independent
// of which layouts were tried in this batch.
std::array<std::vector<Layout>,16> starting_layouts(unsigned trials) {
    std::array<std::vector<Layout>,16> result;
    std::mt19937 random(170021);
    for (unsigned r=0; r<16; ++r) {
        std::array<unsigned,15> vertices{};
        unsigned next=0;
        for (unsigned x=0; x<16; ++x) if (x!=r) vertices[next++]=x;
        for (unsigned trial=0; trial<trials; ++trial) {
            for (unsigned m=15; m>1; --m) std::swap(vertices[m-1],vertices[random()%m]);
            Layout l{};
            std::array<Mask,5> blocks{};
            unsigned entry=0;
            for (unsigned i=0; i<5; ++i) {
                blocks[i]=(1u<<vertices[3*i])|(1u<<vertices[3*i+1])|(1u<<vertices[3*i+2]);
                l[entry++]=(1u<<r)|blocks[i];
                for (unsigned j=0; j<i; ++j) l[entry++]=blocks[i]|blocks[j];
            }
            result[r].push_back(l);
        }
    }
    return result;
}

std::vector<Word> uncovered(const MatchingTable& table,const std::vector<Layout>& layouts) {
    const auto& p=table.palettes;
    auto need=p.all;
    for (const auto& l:layouts) {
        if (std::any_of(l.begin(),l.end(),[&](Mask s){return table.f.closed[s];})) continue;
        bool open=false;
        for (unsigned j=0; j<p.words; ++j) {
            if (!need[j]) continue;
            Word blocked=0;
            for (Mask s:l) blocked|=table.closed(s,j);
            need[j]&=blocked;
            open|=need[j]!=0;
        }
        if (!open) break;
    }
    return need;
}

struct Refinement {
    using Forbidden = std::array<bool,65536>;
    std::array<Mask,16> neighbors{};
    std::vector<Matching> matchings;
    std::vector<std::vector<Mask>> sides;
    Forbidden original{};
    unsigned max_depth=0;
    std::uint64_t nodes=0;

    Refinement(const Factorization& f,Mask palette) {
        for (unsigned c=0; c<15; ++c) {
            if (palette&(1u<<c)) {
                for (Mask e:f.matchings[c]) {
                    unsigned x=std::countr_zero(e), y=std::countr_zero(e^low(e));
                    neighbors[x]|=1u<<y; neighbors[y]|=1u<<x;
                }
            } else for (Mask s:closed_sides(f.matchings[c])) original[s]=true;
        }
        Matching current{};
        enumerate(full,0,current);
        for (const auto& m:matchings) sides.push_back(closed_sides(m));
    }

    void enumerate(Mask left,unsigned depth,Matching& current) {
        if (!left) {matchings.push_back(current); return;}
        unsigned x=std::countr_zero(left);
        Mask rest=left^low(left);
        for (Mask ys=rest&neighbors[x]; ys; ys^=low(ys)) {
            current[depth]=low(left)|low(ys);
            enumerate(rest^low(ys),depth+1,current);
        }
    }

    bool disjoint(unsigned i,unsigned j) const {
        for (Mask e:matchings[i]) for (Mask f:matchings[j]) if (e==f) return false;
        return true;
    }

    bool verify(Mask roots,const std::vector<unsigned>& available,const Forbidden& fixed,unsigned depth) {
        ++nodes;
        max_depth=std::max(max_depth,depth);
        auto blocked=fixed;
        std::array<unsigned,16> partner_count{};
        for (unsigned i:available) {
            for (Mask s:sides[i]) blocked[s]=true;
            for (Mask e:matchings[i]) if (e&1) ++partner_count[std::countr_zero(e^1u)];
        }
        Mask unresolved=0;
        for (Mask rs=roots; rs; rs^=low(rs))
            if (!find_layout(low(rs),[&](Mask s){return !blocked[s];})) unresolved|=low(rs);
        if (!unresolved) return true;

        // Every actual redraw covers this edge exactly once. Branch over its possible colors'
        // matchings, retaining for the other colors only edge-disjoint perfect matchings.
        unsigned partner=0;
        for (unsigned v=1; v<16; ++v) if (partner_count[v] &&
            (!partner || partner_count[v]<partner_count[partner])) partner=v;
        if (!partner) return false;
        Mask selected=1|(1u<<partner);
        for (unsigned i:available) {
            const auto& m=matchings[i];
            if (std::find(m.begin(),m.end(),selected)==m.end()) continue;
            auto next_fixed=fixed;
            for (Mask s:sides[i]) next_fixed[s]=true;
            std::vector<unsigned> next;
            for (unsigned j:available) if (disjoint(i,j)) next.push_back(j);
            if (!verify(unresolved,next,next_fixed,depth+1)) return false;
        }
        return true;
    }

    bool run(Mask roots) {
        std::vector<unsigned> available(matchings.size());
        std::iota(available.begin(),available.end(),0);
        return verify(roots,available,original,0);
    }
};

int main(int argc,char** argv) {
    try {
        require(argc==3 || argc==5,"usage: check CATALOGUE {4|5} [FIRST COUNT]");
        int k=std::stoi(argv[2]);
        require(k==4 || k==5,"supported palette sizes are four and five");
        unsigned first=argc==5 ? std::stoul(argv[3]) : 0;
        unsigned length=argc==5 ? std::stoul(argv[4]) : 3155;
        require(first<3155 && length>0 && length<=3155-first,"invalid catalogue range");
        std::ifstream catalogue(argv[1]);
        require(bool(catalogue),"could not open catalogue");
        Palettes palettes(k);
        auto starts=starting_layouts(k==4 ? 6000 : 1000);
        std::uint64_t checks=0, branch_cases=0, branch_nodes=0;
        unsigned max_depth=0;
        for (unsigned entry=0; entry<first+length; ++entry) {
            Factorization f(catalogue);
            if (entry<first) continue;
            MatchingTable table(palettes,f);
            std::map<Mask,Mask> refine;
            for (unsigned r=0; r<16; ++r) {
                auto need=uncovered(table,starts[r]);
                for (unsigned j=0; j<need.size(); ++j) for (Word s=need[j]; s; s&=s-1) {
                    Word bit=s&-s;
                    auto safe=[&](Mask side){return !f.closed[side] && !(table.closed(side,j)&bit);};
                    if (!find_layout(1u<<r,safe))
                        refine[palettes.sets[j*64+std::countr_zero(bit)]]|=1u<<r;
                }
                checks+=palettes.sets.size();
            }
            for (auto [palette,roots]:refine) {
                require(k>4,"four-color palette has no common layout");
                Refinement proof(f,palette);
                require(proof.run(roots),"uncovered recoloring branch");
                branch_cases+=std::popcount(roots);
                branch_nodes+=proof.nodes;
                max_depth=std::max(max_depth,proof.max_depth);
            }
        }
        if (first+length==3155) {
            std::string extra;
            require(!(catalogue>>extra),"unexpected additional catalogue input");
        }
        std::cout<<length<<" representatives, "<<checks<<" rooted palettes, "<<branch_cases
                 <<" refined, "<<branch_nodes<<" branch nodes, maximum depth "<<max_depth<<"\n";
    } catch (const std::exception& e) {
        std::cerr<<e.what()<<'\n';
        return 1;
    }
}
