// Independent finite sieve for the rank-five A245212 branches described in the paper.
// c++ -std=c++17 -O2 five_prime_replay_245212.cpp -o /tmp/five-prime-replay
#include <array>
#include <cstdint>
#include <iostream>
#include <map>
#include <string>
#include <utility>
#include <vector>

using Word = std::uint64_t;
using Wide = unsigned __int128;
using Pair = std::pair<Word, Word>;
int ceiling = 7072, strip = 4, w3 = 7, sigma3 = 4;
std::array<int, 4> primes{5, 7, 11, 13}, floors{18, 12, 7, 6};

Word modulus_for(int i) {
    Word m = 1;
    for (int e = 0; e < floors[i] && m <= (Word(1)<<42)/primes[i]; ++e) m *= primes[i];
    return m;
}

Word mul(Word a, Word b, Word m) { return Wide(a) * b % m; }

// Compute W and sigma from their defining sums, without division or inverses.
std::vector<Pair> moments(int q, Word m) {
    std::vector<Pair> terms{{1, 1}};
    Word power = 1, w = 1, sum = 1;
    for (int e = 1; e <= ceiling; ++e) {
        power = mul(q, power, m);
        w = (w + (e+1)*power) % m;
        sum = (sum + power) % m;
        terms.emplace_back(w, sum);
    }
    return terms;
}

struct Test {
    Word modulus = 1, small;
    int floor, p;
    std::vector<Pair> fixed, scanned, unknown;
    std::map<Pair, std::vector<int>> buckets;

    Test(int excluded, int searched, int slice, int other)
        : small(primes[excluded]*primes[excluded]), floor(floors[searched]), p(primes[excluded]) {
        modulus = modulus_for(excluded);
        fixed = moments(primes[slice], modulus);
        scanned = moments(primes[other], modulus);
        unknown = moments(primes[searched], modulus);
    }

    bool possible(int a, int b, std::vector<int>* matches = nullptr) {
        Word left = mul(w3, mul(fixed[a].first, scanned[b].first, modulus), modulus);
        Word right = mul(sigma3*(p-1), mul(fixed[a].second, scanned[b].second, modulus), modulus);
        Pair key{left % small, right % small};
        auto [it, fresh] = buckets.try_emplace(key);
        if (fresh) {
            for (int c = floor; c <= ceiling; ++c) {
                auto [w,s] = unknown[c];
                if ((key.first*(w%small))%small == (key.second*(s%small))%small)
                    it->second.push_back(c);
            }
        }
        for (auto c : it->second) {
            auto [w,s] = unknown[c];
            if (mul(left,w,modulus) == mul(right,s,modulus)) {
                if (!matches) return true;
                matches->push_back(c);
            }
        }
        return matches && !matches->empty();
    }
};

bool cofactor_matches(int i, const std::array<int, 4>& exponents) {
    Word m = modulus_for(i), a = w3, b = sigma3*(primes[i]-1);
    for (int j=0; j<4; ++j) if (j!=i) {
        auto [w,s] = moments(primes[j],m)[exponents[j]];
        a = mul(a,w,m);
        b = mul(b,s,m);
    }
    return a==b;
}

int main(int argc, char** argv) {
    if (argc==2) {
        const std::string last = argv[1];
        strip=5; w3=34; sigma3=13; primes[2]=19;
        if (last=="23") { primes[3]=23; floors={19,12,4,3}; ceiling=11616; }
        else if (last=="29") { primes[3]=29; floors={65,43,14,9}; ceiling=13536; }
        else if (last=="31") { primes[3]=31; floors={163,109,36,21}; ceiling=14176; }
        else return 2;
    } else if (argc!=1) return 2;
    for (int i = 0; i < 4; ++i) {
        std::vector<int> rest;
        for (int k = 0; k < 4; ++k) if (k != i) rest.push_back(k);
        int r = rest[0], s = rest[1], j = rest[2];
        Test first(r,s,i,j), second(s,r,i,j);
        int boxes = 0, passed_first = 0, passed_both = 0, passed_all = 0;
        for (int a = floors[i]; a < strip*floors[i]; ++a)
            for (int b = floors[j]; b <= ceiling; ++b) {
                ++boxes;
                if (first.possible(a,b)) {
                    ++passed_first;
                    std::vector<int> roots_r, roots_s;
                    if (second.possible(a,b,&roots_r)) {
                        ++passed_both;
                        first.possible(a,b,&roots_s);
                        std::array<int,4> e;
                        e[i]=a; e[j]=b;
                        for (int er : roots_r) for (int es : roots_s) {
                            e[r]=er; e[s]=es;
                            if (cofactor_matches(i,e) && cofactor_matches(j,e)) ++passed_all;
                        }
                    }
                }
            }
        std::cout << primes[i] << ": " << boxes << " boxes, " << passed_first
                  << " pass first, " << passed_both << " pass both, " << passed_all << " pass all" << std::endl;
        if (passed_all) return 1;
    }
}
