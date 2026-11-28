// Read the Hart-Harvey-Ong indices file in increasing prime order.
// Output conjecture number and all prime factors of each surviving product.
// Run via hho_product_join.py, which checks the source digest.
#include <algorithm>
#include <charconv>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

using UInt = std::uint64_t;

struct SmallPrime {
    unsigned p;
    std::vector<unsigned> indices, inverses;

    SmallPrime(unsigned prime, const std::vector<unsigned>& rows) : p(prime), indices(rows), inverses(prime) {
        if (p > 1) {
            inverses[1] = 1;
            for (unsigned i = 2; i < p; ++i)
                inverses[i] = p - (UInt(p/i) * inverses[p%i]) % p;
        }
    }
};

// Only store irregular pairs (eight bytes each). Two 16-bit prime buckets
// bound every membership search to a small contiguous segment of the table.
class IndexTable {
    std::vector<UInt> pairs;
    std::vector<std::size_t> starts;
public:
    void insert(unsigned p, const std::vector<unsigned>& rows) {
        while (starts.size() <= (p >> 16)) starts.push_back(pairs.size());
        for (unsigned k : rows) pairs.push_back((UInt(p) << 32) | k);
    }
    bool contains(unsigned p, unsigned k) const {
        auto b = p >> 16;
        auto stop = b+1 < starts.size() ? starts[b+1] : pairs.size();
        return std::binary_search(pairs.begin()+starts[b], pairs.begin()+stop, (UInt(p)<<32)|k);
    }
};

// For n=v*cofactor with odd v and cofactor, compute its required index
// modulo v-1 without needing to form n, which need not fit in 64 bits.
unsigned local_index(unsigned c, unsigned v, UInt cofactor) {
    UInt mod = (c==12 ? 1 : 2)*UInt(v-1);
    if (c==12) return (cofactor+mod-3)%mod;
    return ((cofactor+v-1+mod-(c==15 ? 3 : 1))%mod)/2;
}

void check(unsigned c, const SmallPrime& small, UInt q, unsigned r, const IndexTable& table) {
    unsigned p = small.p;
    if (q < std::max(p,37U) || q > r || !(q%2)) return;
    if (p != 1 && !std::binary_search(small.indices.begin(),small.indices.end(),
                                      local_index(c,p,q*r))) return;
    if (table.contains(q,local_index(c,q,UInt(p)*r)))
        std::cout << c << ' ' << p << ' ' << q << ' ' << r << std::endl;
}

void probe(unsigned c, unsigned r, unsigned k, const std::vector<SmallPrime>& smalls, const IndexTable& table) {
    UInt step = (c==12 ? 1 : 2)*UInt(r-1);
    UInt residue = (c==12 ? k+3 : 2*UInt(k)+(c==15 ? 4 : 2)+step-r) % step;
    for (const auto& small : smalls) {
        unsigned p = small.p;
        if (p==1) {
            for (UInt q=residue; q<=r; q+=step) check(c,small,q,r,table);
            continue;
        }
        unsigned rem = step%p;
        if (!rem) {
            if (residue%p) continue;
            for (UInt q=residue/p; q<=r; q+=step/p) check(c,small,q,r,table);
        } else {
            UInt j = ((p-residue%p)*UInt(small.inverses[rem]))%p;
            for (UInt q=(residue+j*step)/p; q<=r; q+=step) check(c,small,q,r,table);
        }
    }
}

int main(int argc, char** argv) {
    if (argc<3) throw std::invalid_argument("usage: irregular_product_join smallest conjecture...");
    unsigned smallest = std::stoul(argv[1]), first = 1;
    std::vector<unsigned> cases;
    for (int i=2;i<argc;++i) {
        if (std::string(argv[i])=="--from" && i+1<argc) {
            first=std::stoul(argv[++i]); continue;
        }
        auto c=std::stoul(argv[i]);
        if (c!=12 && c!=15 && c!=16) throw std::invalid_argument("unknown conjecture");
        cases.push_back(c);
    }
    std::ios::sync_with_stdio(false); std::cin.tie(nullptr);
    if (cases.empty() || first>smallest) throw std::invalid_argument("empty selected range");
    std::vector<SmallPrime> smalls;
    if (first<=1) smalls.emplace_back(1,std::vector<unsigned>{});
    IndexTable table;
    unsigned previous=0;
    std::string line;
    std::vector<unsigned> numbers,rows;
    while (std::getline(std::cin,line)) {
        numbers.clear();
        const char* ptr=line.data(); const char* end=ptr+line.size();
        while (ptr!=end) {
            if (*ptr==' ' || *ptr=='\t' || *ptr=='\r') {++ptr; continue;}
            unsigned value;
            auto result=std::from_chars(ptr,end,value);
            if (result.ec!=std::errc{}) throw std::runtime_error("bad prime table record");
            numbers.push_back(value); ptr=result.ptr;
        }
        if (numbers.empty()) continue;
        unsigned r=numbers.front();
        if (r<=previous || r>2147483647) throw std::runtime_error("out-of-order or oversized prime");
        previous=r;
        if (numbers.size()==1) continue;
        rows.assign(numbers.begin()+1,numbers.end());
        if (!std::is_sorted(rows.begin(),rows.end())) throw std::runtime_error("unsorted indices");
        table.insert(r,rows);
        if (first<=r && r<=smallest) smalls.emplace_back(r,rows);
        for (unsigned k : rows) for (unsigned c : cases) probe(c,r,k,smalls,table);
    }
    if (!std::cin.eof()) throw std::runtime_error("unexpected read failure");
    std::cerr << "Largest prime read: " << previous << '\n';
}
