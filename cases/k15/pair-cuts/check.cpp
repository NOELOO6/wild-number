// c++ -std=c++20 -O3 check.cpp -o check && ./check one-root-prices.txt
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

using Integer = std::int64_t;
using Mask = unsigned;
using Matching = std::array<unsigned, 16>;
using Lengths = std::vector<unsigned>;
constexpr Mask root = 1u << 15, full = 2 * root - 1;
constexpr unsigned shapes = 11, sixes = 5005;
constexpr Integer layouts = 1401400;

void require(bool condition, const std::string& reason) {
    if (!condition) throw std::runtime_error(reason);
}

template <class Range>
void read_numbers(std::istream& input, Range& target, Integer limit) {
    for (auto& x : target) {
        require(bool(input >> x) && x >= -limit && x <= limit, "invalid certificate integer");
    }
}

struct Row {
    Lengths cycles;
    Integer matchings, correction, gain;
    std::array<Integer, 3> pair_counts;
    std::array<Integer, 120> edge;
    std::array<Integer, shapes * shapes> transfer;
};

void append_tails(std::vector<Lengths>& result, Lengths& row, unsigned left, unsigned least) {
    if (left == 0) result.push_back(row);
    for (unsigned part = least; part <= left; part += 2) {
        row.push_back(part);
        append_tails(result, row, left - part, part);
        row.pop_back();
    }
}

std::vector<Lengths> rooted_types() {
    std::vector<Lengths> result;
    for (unsigned first = 4; first <= 16; first += 2) {
        Lengths row{first};
        append_tails(result, row, 16 - first, 4);
    }
    require(result.size() == shapes, "rooted cycle types");
    return result;
}

struct Certificate {
    Integer scale, root_max, pair_max, minimum_pairs, template_id, bound;
    std::array<Integer, 14> a;
    std::array<Row, shapes> rows;

    explicit Certificate(const char* path) {
        std::ifstream in(path);
        require(bool(in >> scale >> root_max >> pair_max >> minimum_pairs >> template_id >> bound),
                "missing certificate header");
        require(scale > 0 && scale <= 10000000 && root_max >= 0 && root_max <= 15 &&
                pair_max >= 0 && pair_max <= 15 && minimum_pairs >= 0 && minimum_pairs <= 105 &&
                template_id >= 0 && template_id < shapes && bound >= 0 && bound <= layouts,
                "invalid certificate header");
        read_numbers(in, a, 20000000);
        auto types = rooted_types();
        for (unsigned i = 0; i < shapes; ++i) {
            auto& row = rows[i];
            for (auto n : types[i]) {
                unsigned actual = 0;
                require(bool(in >> actual) && actual == n, "wrong matching cycle lengths");
            }
            row.cycles = types[i];
            require(bool(in >> row.matchings), "missing matching count");
            read_numbers(in, row.pair_counts, layouts);
            require(bool(in >> row.correction >> row.gain) && std::abs(row.correction) < 1000000000000LL &&
                    std::abs(row.gain) < 10000000000000000LL, "invalid claimed row");
            read_numbers(in, row.edge, 2000000000);
            read_numbers(in, row.transfer, 2000000000);
        }
        std::string extra;
        require(!(in >> extra), "trailing data");
    }
};

Integer choose(int n, int k) {
    if (n < k) return 0;
    Integer c = 1;
    for (int j = 1; j <= k; ++j) c = c * (n + 1 - j) / j;
    return c;
}

void check_score(const Certificate& c) {
    for (int p = 0; p <= 15; ++p) for (int r = 0; r <= 15-p; ++r) {
        Integer score = c.a[0] + c.a[1] * p + c.a[2] * r;
        for (int k = 0; k <= 2; ++k) score += c.a[3+k] * choose(p,2-k) * choose(r,k);
        score *= 3; // The cubic coefficients are averaged over all six orders of a triple.
        for (unsigned mask = 0; mask < 8; ++mask) {
            int k = std::popcount(mask);
            score += (3 / choose(3,k)) * c.a[6+mask] * choose(p,3-k) * choose(r,k);
        }
        require(score <= 3*c.scale*(p <= c.pair_max && r <= c.root_max), "pointwise score");
    }
    for (unsigned i=0; i<shapes; ++i) for (unsigned j=0; j<shapes; ++j)
        for (unsigned k=0; k<shapes; ++k) {
            auto fee = [&](unsigned x,unsigned y,unsigned z){return c.rows[x].transfer[y*shapes+z];};
            require(fee(i,j,k) == fee(i,k,j), "asymmetric transfer");
            require(fee(i,j,k)+fee(j,i,k)+fee(k,i,j) >= 0, "negative total transfer");
        }
    require(c.a[7]==c.a[8] && c.a[11]==c.a[12], "asymmetric anchor coefficients");
}

Mask low(Mask s) { return s & -s; }
unsigned edge_id(unsigned x, unsigned y) {
    if (x > y) std::swap(x,y);
    return y*(y-1)/2+x;
}

std::pair<Matching,Matching> canonical(const Lengths& cycles) {
    Matching a{}, b{};
    auto label = [](unsigned x){return x == 0 ? 15u : x == 15 ? 0u : x;};
    unsigned start = 0;
    for (unsigned n : cycles) {
        for (unsigned k = 0; k < n; k += 2) {
            unsigned x=label(start+k), y=label(start+k+1), z=label(start+(k+2)%n);
            a[x]=y; a[y]=x; b[y]=z; b[z]=y;
        }
        start += n;
    }
    return {a,b};
}

unsigned cycle_key(const Lengths& cycles) {
    unsigned key=0;
    for (auto n : cycles) key=9*key+n/2;
    return key;
}

unsigned type_key(const Matching& a, const Matching& b) {
    Mask unseen=full;
    std::array<unsigned,4> lens{};
    unsigned n=0;
    while (unseen) {
        unsigned x = n==0 ? 15 : std::countr_zero(unseen), start=x;
        do {
            unsigned y=a[x];
            unseen ^= (1u<<x)|(1u<<y);
            x=b[y];
            lens[n]+=2;
        } while (x!=start);
        ++n;
    }
    for (unsigned i=2;i<n;++i)
        for (unsigned j=i;j>1 && lens[j]<lens[j-1];--j) std::swap(lens[j],lens[j-1]);
    unsigned key=0;
    for (unsigned j=0;j<n;++j) key=9*key+lens[j]/2;
    return key;
}

struct Counts {
    const Certificate& cert;
    const Row& row;
    Matching a, b, third{};
    std::array<unsigned,6561> index{};
    std::array<bool,65536> closed_a{},closed_b{};
    std::array<unsigned,65536> four_rank{},six_rank{};
    std::array<Integer,65536> singles{};
    std::vector<Integer> decompositions = std::vector<Integer>(455*sixes);
    std::array<Mask,5> blocks{};
    std::array<Mask,8> edges{};
    std::array<Integer,3> pairs{},one{};
    Integer layouts_seen=0, thirds_seen=0;
    Integer max_error=INT64_MIN;

    Counts(const Certificate& c, unsigned i) : cert(c), row(c.rows[i]) {
        auto matchings=canonical(row.cycles);
        a=matchings.first; b=matchings.second;
        index.fill(shapes);
        for (unsigned j=0;j<shapes;++j) index[cycle_key(c.rows[j].cycles)]=j;
        unsigned qs=0,ss=0;
        for (Mask s=0;s<=full;++s) {
            if (std::popcount(s)==4 && (s&root)) four_rank[s]=qs++;
            if (std::popcount(s)==6 && !(s&root)) six_rank[s]=ss++;
            if (!s) {closed_a[0]=closed_b[0]=true; continue;}
            unsigned x=std::countr_zero(s);
            auto closed = [&](const Matching& m, const auto& table) {
                Mask mate=1u<<m[x];
                return (s&mate) && table[s^low(s)^mate];
            };
            closed_a[s]=closed(a,closed_a);
            closed_b[s]=closed(b,closed_b);
        }
        require(qs==455 && ss==sixes && index[type_key(a,b)]==i, "canonical matching pair");
    }

    unsigned split_id(Mask q,Mask s) const {
        return four_rank[q]*sixes+six_rank[std::min(s,full^q^s)];
    }

    // Modes: 0 = connected, 1 = root-only, 2 = at least one ordinary two-triple cut.
    unsigned mode(const std::array<bool,65536>& closed) const {
        unsigned result=0;
        for (unsigned i=0;i<5;++i) {
            if (closed[root|blocks[i]]) result=1;
            for (unsigned j=0;j<i;++j) if (closed[blocks[i]|blocks[j]]) return 2;
        }
        return result;
    }

    void record_layout() {
        ++layouts_seen;
        unsigned ma=mode(closed_a),mb=mode(closed_b);
        ++one[ma];
        if (!ma || !mb) return;
        ++pairs[(ma==1)+(mb==1)];
        unsigned h=(ma==1)+2*(mb==1);
        Integer p=cert.a[6+h], r=cert.a[10+h];
        for (unsigned i=0;i<5;++i) {
            Mask q=root|blocks[i];
            singles[q]+=r;
            for (unsigned j=0;j<i;++j) singles[blocks[i]|blocks[j]]+=p;
            std::array<Mask,4> other{};
            unsigned pos=0;
            for (unsigned j=0;j<5;++j) if (j!=i) other[pos++]=blocks[j];
            for (unsigned j=1;j<4;++j) decompositions[split_id(q,other[0]|other[j])]-=p+r;
        }
    }

    void each_layout(unsigned depth, Mask left) {
        if (depth==blocks.size()) {
            require(left==0,"layout coverage");
            record_layout(); return;
        }
        Mask x=low(left);
        for (Mask ys=left^x;ys;ys^=low(ys))
            for (Mask zs=ys^low(ys);zs;zs^=low(zs)) {
                Mask triple=x|low(ys)|low(zs);
                blocks[depth]=triple;
                each_layout(depth+1,left^triple);
            }
    }

    void record_matching(Integer edge_sum) {
        ++thirds_seen;
        std::array<Mask,7> ordinary{};
        unsigned pos=0; Mask rooted=0;
        for (Mask e:edges) {
            if (e&root) rooted=e;
            else ordinary[pos++]=e;
        }
        Integer charge=0;
        for (unsigned i=0;i<7;++i) {
            Mask q=rooted|ordinary[i];
            charge+=singles[q];
            for (unsigned j=0;j<i;++j) for (unsigned k=0;k<j;++k)
                charge+=singles[ordinary[i]|ordinary[j]|ordinary[k]];
            std::array<Mask,6> other{};
            unsigned z=0;
            for (unsigned j=0;j<7;++j) if (i!=j) other[z++]=ordinary[j];
            for (unsigned j=1;j<6;++j) for (unsigned k=j+1;k<6;++k)
                charge+=decompositions[split_id(q,other[0]|other[j]|other[k])];
        }
        unsigned j=index[type_key(a,third)],k=index[type_key(b,third)];
        require(j<shapes && k<shapes,"unclassified matching pair");
        Integer error=edge_sum+row.transfer[j*shapes+k]-charge;
        max_error=std::max(max_error,error);
    }

    void each_matching(unsigned depth, Mask left, Integer edge_sum) {
        if (!left) {record_matching(edge_sum); return;}
        unsigned x=std::countr_zero(left);
        Mask rest=left^low(left),allowed=rest&~((1u<<a[x])|(1u<<b[x]));
        for (Mask ys=allowed;ys;ys^=low(ys)) {
            unsigned y=std::countr_zero(ys);
            edges[depth]=(1u<<x)|(1u<<y);
            third[x]=y; third[y]=x;
            each_matching(depth+1,rest^(1u<<y),edge_sum+row.edge[edge_id(x,y)]);
        }
    }

    void verify() {
        each_layout(0,root-1);
        require(layouts_seen==layouts && one[1]==100800 && one[2]==91000,"single counts");
        require(pairs==row.pair_counts,"pair counts");
        each_matching(0,full,0);
        require(thirds_seen==row.matchings && max_error==row.correction,"third-matching bound");
        Integer price=0, quadratic=0;
        for (unsigned y=0;y<16;++y) for (unsigned x=0;x<y;++x)
            if (a[x]!=y && b[x]!=y) price+=row.edge[edge_id(x,y)];
        for (unsigned k=0;k<3;++k) quadratic+=cert.a[3+k]*pairs[k];
        require(105*quadratic+35*(price-13*max_error)==row.gain,"row gain");
    }
};

int main(int argc,char** argv) {
    try {
        require(argc >= 2, "supply a price file");
        for (int file=1;file<argc;++file) {
            Certificate c(argv[file]);
            check_score(c);
            Integer least=INT64_MAX, evaluated=0;
            for (unsigned i=0;i<shapes;++i) {
                Counts count(c,i);
                count.verify();
                evaluated+=count.thirds_seen;
                least=std::min(least,c.rows[i].gain);
            }
            Integer base=layouts*c.a[0]+15*(91000*c.a[1]+100800*c.a[2]);
            Integer total=105*(base+least)+c.minimum_pairs*(c.rows[c.template_id].gain-least);
            require(total>(c.bound-1)*105*c.scale && total<=c.bound*105*c.scale,"rounded guarantee");
            std::cout<<argv[file]<<": "<<c.bound<<" layouts; "<<evaluated<<" third matchings checked\n";
        }
    } catch (const std::exception& e) {
        std::cerr<<e.what()<<'\n';
        return 1;
    }
}
