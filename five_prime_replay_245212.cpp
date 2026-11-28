// Independent finite sieve for the rank-five, v3 = 1 branch of A245212.
// c++ -std=c++17 -O2 five_prime_replay_245212.cpp -o /tmp/five-prime-replay
#include <array>
#include <cstdint>
#include <iostream>
#include <map>
#include <utility>
#include <vector>

using Word = std::uint64_t;
using Wide = unsigned __int128;
using Pair = std::pair<Word, Word>;
constexpr int ceiling = 7072;
constexpr std::array<int, 4> primes{5, 7, 11, 13};
constexpr std::array<int, 4> floors{18, 12, 7, 6};

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
        for (int e = 0; e < floors[excluded]; ++e) modulus *= p;
        fixed = moments(primes[slice], modulus);
        scanned = moments(primes[other], modulus);
        unknown = moments(primes[searched], modulus);
    }

    bool possible(int a, int b) {
        Word left = mul(7, mul(fixed[a].first, scanned[b].first, modulus), modulus);
        Word right = mul(4*(p-1), mul(fixed[a].second, scanned[b].second, modulus), modulus);
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
            if (mul(left,w,modulus) == mul(right,s,modulus)) return true;
        }
        return false;
    }
};

int main() {
    for (int i = 0; i < 4; ++i) {
        std::vector<int> rest;
        for (int k = 0; k < 4; ++k) if (k != i) rest.push_back(k);
        int r = rest[0], s = rest[1], j = rest[2];
        Test first(r,s,i,j), second(s,r,i,j);
        int boxes = 0, passed_first = 0, passed_both = 0;
        for (int a = floors[i]; a < 4*floors[i]; ++a)
            for (int b = floors[j]; b <= ceiling; ++b) {
                ++boxes;
                if (first.possible(a,b)) {
                    ++passed_first;
                    if (second.possible(a,b)) ++passed_both;
                }
            }
        std::cout << primes[i] << ": " << boxes << " boxes, " << passed_first
                  << " pass first, " << passed_both << " pass both\n";
        if (passed_both) return 1;
    }
}
