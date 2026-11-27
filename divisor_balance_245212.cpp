// Search for counterexamples to OEIS A245212 by solving for an extra prime.
// Every m <= limit is examined. No upper bound on the appended prime or
// power of two is imposed; this is not an exhaustive search over all n.
#include <algorithm>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <vector>
#include <boost/multiprecision/cpp_int.hpp>

using Integer = std::uint64_t;
struct Factors {
    Integer remainder, weighted = 1, sigma = 1, tau = 1;
    void absorb(Integer p) {
        Integer power = 1, s = 1, w = 1, exponent = 0;
        while (remainder % p == 0) {
            remainder /= p;
            power *= p;
            ++exponent;
            s += power;
            w += (exponent + 1) * power;
        }
        sigma *= s;
        weighted *= w;
        tau *= exponent + 1;
    }
};

bool prime(Integer p) {
    if (p < 2 || p % 2 == 0) return p == 2;
    for (Integer d = 3; d <= p / d; d += 2)
        if (p % d == 0) return false;
    return true;
}

int main(int argc, char** argv) {
    const Integer limit = argc > 1 ? std::stoull(argv[1]) : 5000000;
    const bool allPowers = argc > 2 && std::string(argv[2]) == "--all-powers";
    if (limit == 0 || limit > 2000000000ULL) return 2;
    std::vector<Integer> primes;
    for (Integer d = 2; d <= limit / d; ++d)
        if (prime(d)) primes.push_back(d);
    Integer eligible = 0, mixed = 0, matches = 0, powerCandidates = 0;
    for (Integer start = 1; start <= limit; start += 65536) {
        const Integer end = std::min<Integer>(limit + 1, start + 65536);
        std::vector<Factors> block;
        block.reserve(end - start);
        for (Integer m = start; m < end; ++m) block.push_back({m});
        for (Integer p : primes) {
            if (p*p >= end) break;
            for (Integer m = ((start+p-1)/p)*p; m < end; m += p)
                block[m-start].absorb(p);
        }
        for (Integer m = start; m < end; ++m) {
            auto& f = block[m-start];
            if (f.remainder > 1) f.absorb(f.remainder);
            const Integer t = m*f.tau, a = f.weighted, s = f.sigma;
            // For n = m*p, p not dividing m, the balance equation is
            // p(4T-2A-S)=A+S. T=m*tau(m), A=sum d*tau(d), S=sigma(m).
            if (4*t > 2*a+s) {
                const Integer den = 4*t-2*a-s;
                if ((a+s)%den == 0) {
                    const Integer p = (a+s)/den;
                    if (p > 1 && m%p && prime(p)) {
                        ++eligible;
                        if (p != 2 || (m & (m-1))) {
                            ++matches;
                            std::cout << "witness m=" << m << " p=" << p << std::endl;
                        }
                    }
                }
            }
            // For odd m>1, n=2^k*m gives
            // 2^(k+1)*(T-S-k*(A-T))=A-S. Enumerate only divisors of A-S.
            if (m>1 && (m & 1)) {
                Integer v=a-s;
                for (Integer k=1; k<63 && v%(Integer(1)<<(k+1))==0; ++k) {
                    ++mixed;
                    if (t == s + k*(a-t) + (v>>(k+1))) {
                        ++matches;
                        std::cout << "witness odd m=" << m << " k=" << k << std::endl;
                    }
                }
            }
            if (!allPowers || m==1 || 2*t<=a) continue;
            // At exponent e>=2 the root in p lies STRICTLY between
            // (e*A+S)/D and (e*A+S)/D+1, with D=(e+1)(2T-A)-S.
            // Also p^e divides A-S(p-1), so e is bounded independently
            // of p unless this right side vanishes. In that exceptional
            // case m was already a solution and p=1+A/S; test it here.
            if (a%s==0 && 2*t==a+s) {
                const Integer p=1+a/s;
                if (m%p && prime(p)) {
                    ++matches;
                    std::cout << "infinite extensions m=" << m << " p=" << p << std::endl;
                }
            }
            const unsigned maxE = 64-__builtin_clzll(a+s);
            for (Integer e=2; e<=maxE; ++e) {
                const Integer leading=(e+1)*(2*t-a);
                if (leading<=s) continue;
                const Integer d=leading-s, b=e*a+s;
                const Integer p=b/d+1;
                if (p<2 || m%p==0 || (a+s)%p!=0 || b%d==0) continue;
                using boost::multiprecision::cpp_int;
                cpp_int constant=cpp_int(a)-cpp_int(s)*(p-1);
                if (!constant) continue;
                Integer j=0;
                while (j<e && constant%p==0) { constant/=p; ++j; }
                if (j!=e || !prime(p)) continue;
                ++powerCandidates;
                const cpp_int slope=cpp_int(2*t)*(p-1)-cpp_int(a)*p;
                const cpp_int bracket=cpp_int(e+1)*(p-1)*slope+
                    cpp_int(a)*p-cpp_int(s)*p*(p-1);
                if (bracket==constant) {
                    ++matches;
                    std::cout << "witness m=" << m << " p=" << p << " e=" << e << std::endl;
                }
            }
        }
    }
    std::cout << "cofactor_limit=" << limit << " prime_extensions=" << eligible
              << " mixed_tests=" << mixed << " power_candidates=" << powerCandidates
              << " nontrivial_matches=" << matches << '\n';
}
