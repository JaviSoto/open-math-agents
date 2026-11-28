// Independent full rectangle checker for A245212; uses GMP and C++17.
// c++ -O3 -std=c++17 two_odd_rectangle_245212.cpp -lgmpxx -lgmp -o replay
// ./replay [workers [maximum K [maximum M [maximum m]]]]
// Both exponent lengths range from 6 through M; their minimum is <=m.
#include <algorithm>
#include <atomic>
#include <cstdint>
#include <cstdlib>
#include <exception>
#include <iostream>
#include <stdexcept>
#include <string>
#include <thread>
#include <vector>
#include <gmpxx.h>

using Big = mpz_class;
struct Moment { Big weighted = 1, sigma = 1, top = 1; };
struct Counts {
    uint64_t positions = 0, square = 0, powers = 0;
    Counts& operator+=(const Counts& rhs) {
        positions += rhs.positions; square += rhs.square; powers += rhs.powers;
        return *this;
    }
};

static bool prime(int n) {
    for (int d = 2; d*d <= n; ++d) if (n % d == 0) return false;
    return n >= 2;
}

// The weighted/ordinary sums are built term by term, with no closed form.
static std::vector<Moment> moments(int base, int limit) {
    std::vector<Moment> result(limit+1);
    Big power = 1;
    for (int length = 2; length <= limit; ++length) {
        power *= base;
        auto& cur = result[length];
        cur.top = power*length;
        cur.sigma = result[length-1].sigma + power;
        cur.weighted = result[length-1].weighted + cur.top;
    }
    return result;
}

struct LastPrime {
    int K, p, B;
    Big w, s, h; // h = 2*t-w, the leading coefficient of the digit denominator
    Counts& stats;

    Big candidate(int C) const {
        Big num = (C-1)*w+s, den = h*C-s, q;
        mpz_cdiv_q(q.get_mpz_t(), num.get_mpz_t(), den.get_mpz_t());
        return q;
    }

    void check(const Big& q, int lo, int hi) {
        if (q <= p) return;
        Big diff = w-(q-1)*s;
        Big square = q*q;
        if (!mpz_divisible_p(diff.get_mpz_t(), square.get_mpz_t())) return;
        stats.square += hi-lo+1;
        Big power;
        mpz_pow_ui(power.get_mpz_t(), q.get_mpz_t(), lo-1);
        for (int C = lo; C <= hi; ++C, power *= q) {
            if (!mpz_divisible_p(diff.get_mpz_t(), power.get_mpz_t())) continue;
            ++stats.powers;
            // D q^f = sum_{j=0}^{f-1} ((j+1)w+s) q^j is the full balance.
            Big total = 0;
            for (int j = C-2; j >= 0; --j) total = total*q+(j+1)*w+s;
            if (total == (h*C-s)*power)
                throw std::runtime_error("exact equality at K="+std::to_string(K)
                    +" p="+std::to_string(p)+" B="+std::to_string(B)
                    +" q="+q.get_str()+" C="+std::to_string(C));
        }
    }

    // A ratio of affine functions with a positive denominator is monotone.
    // Equal rounded endpoints therefore determine the whole interval.
    void interval(int lo, int hi, const Big& first, const Big& last) {
        if (first == last) { check(first, lo, hi); return; }
        if (first <= p && last <= p) return;
        if (hi-lo <= 8) {
            check(first, lo, lo);
            for (int c = lo+1; c < hi; ++c) check(candidate(c), c, c);
            check(last, hi, hi);
            return;
        }
        int mid = (lo+hi)/2;
        interval(lo, mid, first, candidate(mid));
        interval(mid+1, hi, candidate(mid+1), last);
    }

    void run(int end) {
        stats.positions += end-5;
        if (h <= 0 || h*end <= s) return;
        int start = 6;
        if (h*start <= s) {
            Big floor = s/h;
            start = static_cast<int>(floor.get_ui())+1; // s/h < end above
        }
        interval(start, end, candidate(start), candidate(end));
    }
};

int main(int argc, char** argv) {
    const int workers = argc > 1 ? std::stoi(argv[1]) : 8;
    const int maxK = argc > 2 ? std::stoi(argv[2]) : 1250;
    const int maxM = argc > 3 ? std::stoi(argv[3]) : 225;
    const int maxMin = argc > 4 ? std::stoi(argv[4]) : 32;
    if (workers < 1 || workers > 64 || maxK < 6 || maxK > 1250 ||
        maxMin < 6 || maxMin > maxM || maxM > 225) return 2;
    auto dyadic = moments(2, maxK);
    std::vector<int> primes;
    for (int p = 13; p <= 3*maxK; p += 2) if (prime(p)) primes.push_back(p);
    std::atomic<size_t> next{0};
    std::vector<Counts> counts(workers);
    std::vector<std::thread> threads;
    for (int i = 0; i < workers; ++i) threads.emplace_back([&, i]() {
        for (size_t ix; (ix = next.fetch_add(1)) < primes.size();) {
            int p = primes[ix];
            auto odd = moments(p, maxM);
            for (int K = std::max(6,(p+2)/3); K <= maxK; ++K) {
                const auto& d = dyadic[K];
                for (int B = 6; B <= maxM; ++B) {
                    if (p*B <= (K-1)*(B-1)) break;
                    const auto& o = odd[B];
                    Big w = d.weighted*o.weighted;
                    LastPrime last{K,p,B,w,d.sigma*o.sigma,2*d.top*o.top-w,counts[i]};
                    last.run(B <= maxMin ? maxM : maxMin);
                }
            }
        }
    });
    for (auto& thread : threads) thread.join();
    Counts total;
    for (const auto& c : counts) total += c;
    std::cout << "K<=" << maxK << " M<=" << maxM << " m<=" << maxMin
              << " positions=" << total.positions << " square=" << total.square
              << " fullPower=" << total.powers << " equalities=0\n";
}
