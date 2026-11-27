// Exact search for Fonollosa's unique multiset sums, for modulus below 256.
// clang++ -std=c++17 -O3 -I/opt/homebrew/include cyclic_min_modulus.cpp -o cyclic-min
// cyclic-min 8 128 247  (last modulus included); a found tuple is printed.
#include <algorithm>
#include <array>
#include <cassert>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <vector>
#include <atomic>
#include <mutex>
#include <thread>
#include <memory>
#include <boost/multiprecision/cpp_int.hpp>
#ifdef WIDE_CYCLIC
using Bits = boost::multiprecision::uint512_t;
constexpr int MAX_N=512;
#else
using Bits = boost::multiprecision::uint256_t;
constexpr int MAX_N=256;
#endif
using Balls = std::array<Bits,14>;
struct Search {
    int n,N,anchor=0;
    Bits mask;
    int pts[14]{};
    unsigned short mult[MAX_N][MAX_N]{}, gcd[MAX_N]{};
    std::vector<int> normalizers[MAX_N];
    int needed[14][14]{};
    std::uint64_t nodes=0,solutions=0;
    bool enumerate;
    Search(int k,int modulus,bool all) : n(k),N(modulus),mask((Bits(1)<<N)-1),enumerate(all) {
        for(int a=0;a<N;++a) {
            gcd[a]=std::gcd(a,N);
            for(int b=0;b<N;++b) mult[a][b]=(a*b)%N;
        }
        for (int r=2;r<n;++r) for(unsigned s=1;s<(1u<<(n-1));++s) {
            if(!(s>>(r-1))) continue;
            const int size=__builtin_popcount(s)+1; // always include the zero pivot
            for(int j=1;j<=size;++j) ++needed[r][j];
        }
    }
    Bits rotate(Bits w,int v) const { return ((w<<v)|(w>>(N-v)))&mask; }
    static bool hit(const Bits& w,int v) { return boost::multiprecision::bit_test(w,v); }
    static int count(const Bits& w) {
        int total=0;
        const auto& raw=w.backend();
        for(unsigned i=0;i<raw.size();++i) total+=__builtin_popcountll(raw.limbs()[i]);
        return total;
    }
    // Only keep a prefix if none of its affine normalizations precedes it.
    // Future (larger) points cannot undo an already smaller sorted prefix.
    bool canonical(int r) const {
        if (r<3) return true;
        int best=pts[2];
        for(int a=0;a<r;++a) for(int b=0;b<r;++b) {
            if(a==b) continue;
            int diff=pts[b]-pts[a]; if(diff<0) diff+=N;
            for(int u:normalizers[diff]) {
                if(u==1 && a==0) continue;
                int vals[14],len=0,third=N;
                for(int j=0;j<r;++j) if(j!=a && j!=b) {
                    int d=pts[j]-pts[a]; if(d<0) d+=N;
                    int v=mult[u][d];
                    if(v<best) return false;
                    third=std::min(third,v);
                    vals[len++]=v;
                }
                if(third!=best || r<=3) continue;
                std::sort(vals,vals+len);
                if(std::lexicographical_compare(vals,vals+len,pts+2,pts+r)) return false;
            }
        }
        return true;
    }
    // Target of the old r-point prefix is V. If the added t occurs j times
    // in a competing multiset, the old labels must sum to V+(1-j)t, in
    // exactly r+1-j slots. j=1 is impossible by validity of the prefix.
    bool dfs(int r,int V,const Balls& reach) {
        ++nodes;
        if(r==n) { ++solutions; return !enumerate; }
        if(reach[n]==mask) return false;
        // All subset sums of the nonpivot labels of a valid full set are
        // distinct. A subset containing a future label cannot have its sum
        // representable by the same number of old labels, or by one extra
        // old label: include the zero pivot among the labels being replaced.
        for(int j=n-1;j>=3;--j)
            if(count(reach[j])+needed[r][j]>N) return false;
        for(int t=pts[r-1]+1;t<=N-(n-r);++t) {
            int v=(V+t)%N;
            if(hit(reach[r+1],v)) continue;
            bool good=true;
            for(int i=0;i<r;++i) if(gcd[t-pts[i]]<anchor) {good=false;break;}
            if(!good) continue;
            int residual=V;
            for(int j=2;j<=r+1;++j) {
                residual-=t; if(residual<0) residual+=N;
                if(hit(reach[r+1-j],residual)) {good=false;break;}
            }
            if(!good) continue;
            pts[r]=t;
            if(!canonical(r+1)) continue;
            if(r+1==n) {
                ++solutions;
                if(!enumerate) return true;
                continue;
            }
            Balls next=reach;
            for(int j=1;j<=n;++j) next[j]|=rotate(next[j-1],t);
            if(dfs(r+1,v,next)) return true;
        }
        return false;
    }
    bool run() {
        // An affine normalization sends a pair realizing the minimum gcd of
        // all pairwise differences to (0,g). No other point can lie in (0,g).
        for(anchor=1;anchor<N;++anchor) if(N%anchor==0) {
            for(int d=0;d<N;++d) normalizers[d].clear();
            for(int d=1;d<N;++d) if(gcd[d]==anchor)
                for(int u=1;u<N;++u) if(gcd[u]==1 && mult[u][d]==anchor)
                    normalizers[d].push_back(u);
            pts[0]=0; pts[1]=anchor;
            Balls start{}; start[0]=1;
            for(int j=1;j<=n;++j) start[j]=1|rotate(start[j-1],anchor);
            if(dfs(2,anchor,start)) return true;
        }
        return false;
    }
};

int main(int argc,char**argv) {
    if(argc<4 || argc>6) return 2;
    int n=std::stoi(argv[1]),lo=std::stoi(argv[2]),hi=std::stoi(argv[3]);
    if(n<2 || n>12 || lo<n || lo>hi || hi>=MAX_N) return 2;
    const bool all = argc>=5 && std::string(argv[4])=="--orbits";
    if(argc>=5 && !all && std::string(argv[4])!="--first") return 2;
    const int threads=argc==6?std::stoi(argv[5]):1;
    if(threads<1 || threads>16) return 2;
    std::atomic<int> next{lo};
    std::mutex output;
    auto worker=[&] {
      int N;
      while((N=next.fetch_add(1))<=hi) {
        auto storage=std::make_unique<Search>(n,N,all);
        Search& s=*storage;
        auto st=std::chrono::steady_clock::now();
        bool found=s.run();
        double dt=std::chrono::duration<double>(std::chrono::steady_clock::now()-st).count();
        std::lock_guard<std::mutex> guard(output);
        std::cout<<"n="<<n<<" N="<<N<<" nodes="<<s.nodes<<" seconds="<<dt;
        if(all) {
            std::cout<<" ORBITS "<<s.solutions;
        } else if(found) {
            std::cout<<" VALID";
            for(int i=0;i<n;i++) std::cout<<" "<<s.pts[i];
        } else std::cout<<" NONE";
        std::cout<<std::endl;
      }
    };
    std::vector<std::thread> jobs;
    for(int j=1;j<threads;++j) jobs.emplace_back(worker);
    worker();
    for(auto& t:jobs) t.join();
}
