// C++20. Supply the original catalogue and the path for the output witnesses.
#include <algorithm>
#include <array>
#include <fstream>
#include <iostream>
#include <numeric>
#include <random>
#include <sstream>
#include <stdexcept>
#include <string>
using Factors = std::array<std::array<int,16>,15>;
using Order = std::array<int,15>;
Factors read_row(const std::string& line){
    Factors f{}; std::array<std::array<int,16>,16> occurrences{};
    std::istringstream input(line); std::string word;
    for(auto& row:f){
        if(!(input>>word) || word.size()!=16)throw std::runtime_error("Invalid catalogue row");
        row.fill(-1);
        for(int i=0;i<16;i+=2){
            int a=word[i]-'a',b=word[i+1]-'a';
            if(a<0||a>=16||b<0||b>=16||a==b||row[a]!=-1||row[b]!=-1)
                throw std::runtime_error("Invalid matching");
            row[a]=b;row[b]=a;
            if(++occurrences[std::min(a,b)][std::max(a,b)]!=1)throw std::runtime_error("Repeated edge");
        }
    }
    if(input>>word)throw std::runtime_error("Extra column");
    for(int i=0;i<15;i++)for(int j=0;j<i;j++){
        int v=0,count=0;
        do{v=f[j][f[i][v]];count+=2;}while(v!=0);
        if(count!=16)throw std::runtime_error("Pair does not make one cycle");
    }
    return f;
}
bool connects(const Factors& f,int root,const Order& seq){
    int group[16];group[root]=-1;
    for(int i=0;i<15;i++)group[seq[i]]=i/3;
    for(const auto& m:f){
        int parent[5]={0,1,2,3,4}, parts=5;
        auto rep=[&](int x){while(parent[x]!=x)x=parent[x];return x;};
        for(int a:seq){
            int b=m[a];if(a>b || b==root)continue;
            int i=rep(group[a]),j=rep(group[b]);
            if(i!=j){parent[i]=j;parts--;if(parts==1)break;}
        }
        if(parts!=1)return false;
    }
    return true;
}
int main(int argc,char**argv){
    if(argc!=3)return 1;
    std::ifstream in(argv[1]);std::ofstream out(argv[2]);if(!in||!out)return 2;
    std::mt19937 rng(81739);
    std::string line;int n=0,max_attempts=0;
    while(std::getline(in,line)){
        auto f=read_row(line);n++;
        for(int root=0;root<16;root++){
            Order seq{};int k=0;for(int v=0;v<16;v++)if(v!=root)seq[k++]=v;
            int trial=0;
            do{
                if(++trial>10000)throw std::runtime_error("No witness");
                std::shuffle(seq.begin(),seq.end(),rng);
            }while(!connects(f,root,seq));
            max_attempts=std::max(max_attempts,trial);
            if(root)out<<' ';
            for(int v:seq)out<<char('a'+v);
        }
        out<<'\n';
    }
    if(n!=3155)return 3;
    std::cout<<n<<" representatives, "<<n*16<<" rooted witnesses, maximum trials "<<max_attempts<<"\n";
}
