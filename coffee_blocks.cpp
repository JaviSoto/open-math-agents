// Generate A280864 and test the prime-debut and squarefree-divisor conjectures.
// Usage: coffee_blocks number-of-terms [official-two-column-bfile]
#include <algorithm>
#include <bit>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <vector>

using U = std::uint32_t;
using W = std::uint64_t;

class Table {
public:
    // A zero entry is either 0, 1, or a prime. A composite U has a prime
    // factor no larger than 65535, so two bytes suffice.
    std::vector<std::uint16_t> factor;
    std::vector<bool> used;
    std::vector<U> first;
    explicit Table(U bound) { extend(bound); }
    void extend(U bound) {
        factor.assign(W(bound)+1, 0);
        for (W p=2; p*p<=bound; ++p)
            if (!factor[p])
                for (W j=p*p; j<=bound; j+=p)
                    if (!factor[j]) factor[j]=p;
        used.resize(W(bound)+1);
        first.resize(W(bound)+1, 1);
    }
    void fit(W value) {
        if (value < used.size()) return;
        W bound = std::max<W>(value, W(used.size())*2);
        if (bound >= UINT32_MAX) throw std::runtime_error("table limit exceeded");
        extend(static_cast<U>(bound));
    }
    U radical(U value, std::vector<U>& primes) const {
        U result=1;
        primes.clear();
        while(value>1) {
            U p=factor[value] ? factor[value] : value;
            primes.push_back(p);
            result*=p;
            do { value/=p; } while (value%p==0);
        }
        return result;
    }
};

int main(int argc, char** argv) {
    if (argc<2 || argc>3) return 2;
    W count=std::stoull(argv[1]);
    if (count<2 || count>200000000) return 2;
    Table tab(static_cast<U>(std::max<W>(1000,count*3)));
    std::ifstream reference;
    if (argc==3) {
        reference.open(argv[2]);
        if (!reference) throw std::runtime_error("missing b-file");
    }
    U ref_index=0, ref_value=0, checked=0;
    if (argc==3) reference >> ref_index >> ref_value;
    U need=1, forbid=1, previous=0, max_term=0, next_prime=2;
    W type_two=0, unusual_debut=0, squarefree_issues=0, order_issues=0, prime_index_issues=0;
    std::vector<U> prime_factors;
    for (U n=1; n<=count; ++n) {
        U first=tab.first[need];
        W val=W(need)*first;
        tab.fit(val);
        while(tab.used[val]) {
            ++first; val+=need; tab.fit(val);
        }
        tab.first[need]=first;
        U mult=first;
        while(tab.used[val] || std::gcd(mult,forbid)!=1) {
            ++mult; val+=need; tab.fit(val);
        }
        U a=static_cast<U>(val);
        if (n==ref_index) {
            if (a!=ref_value) throw std::runtime_error("b-file mismatch");
            ++checked;
            if (!(reference >> ref_index >> ref_value)) ref_index=0;
        }
        U rad=tab.radical(a,prime_factors);
        bool exceptional=false;
        if (!prime_factors.empty() && prime_factors.back()>=next_prime) {
            U fresh=prime_factors.back();
            if (fresh!=next_prime || mult!=fresh)
                throw std::runtime_error("prime debut out of order");
            prime_index_issues += (fresh>n);
            if (need>1) {
                ++type_two; exceptional=(need==2);
                if (!exceptional && unusual_debut++<5)
                    std::cout<<"new prime starts at another multiple: "<<n<<" "<<a<<" "<<fresh<<"\n";
            }
            do { ++next_prime; tab.fit(next_prime); } while(tab.factor[next_prime]);
        }
        if (a==rad && a>1) {
            for (U p : prime_factors) {
                // It is enough inductively to check the maximal proper divisors.
                if (!tab.used[a/p] && !(exceptional && p==2)) {
                    if (squarefree_issues++<5)
                        std::cout<<"missing maximal divisor: "<<n<<" "<<a<<" "<<a/p<<"\n";
                }
            }
        }
        if (n>1 && need>1 && rad==need && a==rad && prime_factors.size()>1) {
            if (order_issues++<5) std::cout<<"squarefree composite terminal: "<<n<<" "<<a<<"\n";
        }
        if (std::gcd(rad,forbid)!=1 || (rad%need)!=0 || tab.used[a])
            throw std::runtime_error("run-rule inconsistency");
        previous=a; max_term=std::max(max_term,a); tab.used[a]=true;
        forbid=need; need=rad/forbid;
    }
    std::cout<<"terms="<<count<<" last="<<previous<<" max="<<max_term<<" next_prime="<<next_prime
             <<" type_II="<<type_two<<" non_double_debuts="<<unusual_debut
             <<" squarefree_divisor_violations="<<squarefree_issues
             <<" squarefree_composite_ends="<<order_issues<<" prime_index_violations="<<prime_index_issues
             <<" reference_terms="<<checked<<"\n";
}
