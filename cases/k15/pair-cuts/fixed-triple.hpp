// Included by check.cpp after its rooted matching representatives and mask helpers.
struct FixedTriplePrices {
    Integer scale, constant, bound;
    std::array<Integer,4> linear;
    std::array<std::array<Integer,4>,4> quadratic, transfer;
    std::array<std::array<Integer,45>,4> edge;
    explicit FixedTriplePrices(const char* path) {
        std::ifstream in(path);
        require(bool(in>>scale>>constant>>bound) && scale==1000000 && std::abs(constant)<=5000000 &&
                bound>=0 && bound<=15400,"fixed-triple header");
        read_numbers(in,linear,5000000);
        for (auto& row:quadratic) read_numbers(in,row,5000000);
        for (auto& row:transfer) read_numbers(in,row,100000000000LL);
        for (auto& row:edge) read_numbers(in,row,100000000000LL);
        std::string extra;
        require(!(in>>extra),"unexpected fixed-triple prices");
    }
};

struct FixedTripleChart {
    struct Counts {Integer all=0, first=0, second=0, both=0;};
    Matching a,b;
    std::array<bool,65536> ca{},cb{};
    std::vector<Counts> counts=std::vector<Counts>(32768);
    std::array<Mask,5> groups{};

    static bool closed(const Matching& m,Mask s) {
        for (Mask z=s;z;z^=low(z)) if (!(s&(1u<<m[std::countr_zero(z)]))) return false;
        return true;
    }
    explicit FixedTripleChart(const Lengths& chart) {
        auto pair=canonical(chart); a=pair.first; b=pair.second;
        for (Mask s=0;s<=full;++s) {ca[s]=closed(a,s); cb[s]=closed(b,s);}
        draw(0,root-1);
    }
    // A six-cut always spoils this fixed triple. A root cut spoils it only at another triple.
    std::pair<bool,Mask> failures(const std::array<bool,65536>& cl) const {
        Mask rooted=0;
        for (unsigned i=0;i<5;++i) {
            if (cl[root|groups[i]]) rooted=groups[i];
            for (unsigned j=0;j<i;++j) if (cl[groups[i]|groups[j]]) return {true,0};
        }
        return {false,rooted};
    }
    void draw(unsigned depth,Mask left) {
        if (!left) {
            auto [pa,ra]=failures(ca);
            auto [pb,rb]=failures(cb);
            for (Mask t:groups) {
                bool first=pa || (ra && ra!=t), second=pb || (rb && rb!=t);
                auto& n=counts[t]; ++n.all; n.first+=first; n.second+=second; n.both+=first && second;
            }
            return;
        }
        Mask x=low(left);
        for (Mask ys=left^x;ys;ys^=low(ys)) for (Mask zs=ys^low(ys);zs;zs^=low(zs)) {
            groups[depth]=x|low(ys)|low(zs);
            draw(depth+1,left^groups[depth]);
        }
    }
    static unsigned type(const Matching& m,Mask t) {
        const Mask q=t|root;
        if (closed(m,q)) return 3;
        if (t&(1u<<m[15])) return 1;
        for (Mask s=t;s;s^=low(s)) if (t&(1u<<m[std::countr_zero(s)])) return 2;
        return 0;
    }
    static unsigned edge_class(const Matching& m,Mask t,unsigned x,unsigned y) {
        auto region=[&](unsigned v){return v==15 ? 0u : (t&(1u<<v)) ? 1u : 2u;};
        unsigned i=3*region(x)+region(m[x]),j=3*region(y)+region(m[y]);
        if (i>j) std::swap(i,j);
        return j*(j+1)/2+i;
    }
};

void verify_fixed_triple(const char* path) {
    FixedTriplePrices p(path);
    constexpr std::array<int,4> mult{10,2,2,1};
    for (int a=0;a<=10;++a) for (int b=0;b<=2;++b) for (int c=0;c<=2;++c) for (int d=0;d<=1;++d) {
        std::array<int,4> x{a,b,c,d};
        Integer score=p.constant;
        for (unsigned i=0;i<4;++i) {
            score+=p.linear[i]*x[i];
            for (unsigned j=0;j<4;++j) score+=p.quadratic[i][j]*x[i]*(x[j]-(i==j));
        }
        require(score>=(a+b+c+d==0 ? p.scale : 0),"fixed-triple pointwise score");
    }
    std::array<Integer,4> single{},edge_sum{};
    std::array<bool,4> seen{};
    unsigned total=0;
    for (const auto& cycles:rooted_types()) {
        FixedTripleChart chart(cycles);
        for (Mask t=1;t<root;++t) if (std::popcount(t)==3) {
            const auto& count=chart.counts[t];
            require(count.all==15400,"fixed-triple layout count");
            for (unsigned reverse=0;reverse<2;++reverse) {
                const auto& a=reverse?chart.b:chart.a;
                const auto& b=reverse?chart.a:chart.b;
                unsigned i=chart.type(a,t),j=chart.type(b,t);
                Integer available=0,used=0,first=reverse?count.second:count.first;
                for (unsigned y=1;y<16;++y) for (unsigned x=0;x<y;++x) {
                    Integer price=p.edge[i][chart.edge_class(a,t,x,y)];
                    if (a[x]!=y) available+=price;
                    if (b[x]==y) used+=price;
                }
                if (seen[i]) require(single[i]==first && edge_sum[i]==available,"inconsistent matching type");
                single[i]=first; edge_sum[i]=available; seen[i]=true;
                if (i!=3 || j!=3)
                    require(p.quadratic[i][j]*count.both<=used+p.transfer[i][j],"fixed-triple pair bill");
                ++total;
            }
        }
    }
    Integer score=15400*p.constant;
    for (unsigned i=0;i<4;++i) {
        require(seen[i],"missing matching type");
        score+=mult[i]*(p.linear[i]*single[i]+edge_sum[i]);
        for (unsigned j=0;j<4;++j) score+=mult[i]*(mult[j]-(i==j))*p.transfer[i][j];
    }
    require(score/p.scale==p.bound && score>=0 && total==10010,"fixed-triple rounded bound");
    std::cout<<path<<": at most "<<p.bound<<" layouts per singly closed triple; "<<total<<" ordered charts checked\n";
}
