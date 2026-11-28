"""Exclude solutions to A245212 with a bounded number of odd divisors.

Run python3 odd_divisor_count_245212.py --through 35 --audit.
All bounds, endpoint comparisons and final equality checks use integers.
"""
import argparse
from bisect import bisect_right
from collections import Counter
from functools import lru_cache
from math import isqrt, prod
from time import monotonic


def ordered_exponents(t):
    """Each ordered list of positive exponents with ∏(e+1)=t, once."""
    if t == 1:
        yield ()
    else:
        for factor in range(2, t+1):
            if t % factor == 0:
                for tail in ordered_exponents(t//factor):
                    yield (factor-1, *tail)


def first_impossible_k(t):
    """The inequality fails at K and every larger k. See the monotonicity proof."""
    k = 2*t
    while (1 << k) <= (4*(k+2)*t*t)**t:
        k += 1
    return k


@lru_cache(100000)
def local(p, e):
    """Return p^e, Σ(j+1)p^j, Σp^j; p need not be prime for this evaluation."""
    if e == 1:
        return p, 1+2*p, 1+p
    if e == 2:
        power = p*p
        return power, 1+2*p+3*power, 1+p+power
    power = p**e
    sigma = (p*power-1)//(p-1)
    return power, (p*(e+1)*power-sigma)//(p-1), sigma


class PrimeTable:
    def __init__(self):
        self.limit = 2
        self.values = [2]

    def interval(self, lo, hi):
        if hi <= lo:
            return ()
        if self.limit < hi:
            limit = max(hi, 2*self.limit)
            bits = bytearray([1])*(limit+1)
            bits[:2] = bytes(2)
            for d in range(2, isqrt(limit)+1):
                if bits[d]:
                    bits[d*d::d] = bytes((limit-d*d)//d+1)
            self.values = [p for p in range(2,limit+1) if bits[p]]
            self.limit = limit
        return self.values[bisect_right(self.values,lo):bisect_right(self.values,hi)]


def last_prime(e, T, A, S):
    """Only integer candidate. e=1 requires equality; e>1 both bounds are strict."""
    D = (e+1)*(2*T-A)-S
    if D <= 0:
        return 0
    whole, rem = divmod(e*A+S,D)
    if e == 1:
        return 0 if rem else whole
    return whole+1 if rem else 0


def original_difference(k, factors):
    """Evaluate a(n)−σ(n) from the divisors of the odd part, grouped by v₂."""
    divisors = [(1,1)]
    for p,e in factors:
        divisors = [(d*p**j,tau*(j+1)) for d,tau in divisors for j in range(e+1)]
    m = max(d for d,_ in divisors)
    odd_sigma = sum(d for d,_ in divisors)
    odd_weight = sum(d*tau for d,tau in divisors)
    n = m << k
    tau = (k+1)*len(divisors)
    sigma = sum(odd_sigma << h for h in range(k+1))
    proper_weight = sum(((h+1)*odd_weight) << h for h in range(k+1))-n*tau
    return n*tau-proper_weight-sigma


def check_pattern(t, exps, limit_k, primes, audit=False):
    c = Counter()
    factors = tuple(prod(e+1 for e in exps[i:]) for i in range(len(exps)+1))
    for k in range(limit_k):
        power = 1 << k
        gh = 2*power-1
        gl = k*gh+k+1   # γ=gl/gh, including γ=1 at k=0
        target = (gl+gh)*t
        k0, a0, s0 = power*(k+1), 1+2*k*power, gh

        def descend(i, prev, m, a, s, bases):
            remaining = exps[i:]
            if len(remaining) == 1:
                c["last_tests"] += 1
                e = remaining[0]
                T, A, S = k0*m*(t//(e+1)), a0*a, s0*s
                p = last_prime(e,T,A,S)
                if p <= prev:
                    return
                c["ordered_digits"] += 1
                if (A+S) % p:
                    return
                c["divisible"] += 1
                c["max_digit"] = max(c["max_digit"],p)
                z,w,h = local(p,e)
                # Test the original W+σ=2nτ, even when the candidate p is
                # composite: if the equality holds we must not certify the row.
                if A*w+S*h == 2*T*z*(e+1):
                    raise ArithmeticError(f"candidate equality: t={t} k={k} prefix={m} last={p}^{e}")
                if audit and all(p % d for d in range(2,isqrt(p)+1)):
                    c["prime_audits"] += 1
                    direct = original_difference(k,zip((*bases,p),exps))
                    if direct != 2*T*z*(e+1)-A*w-S*h or direct == 0:
                        raise ArithmeticError(f"original divisor-sum audit failed: {k}, {bases}, {p}")
                return

            # If the limiting expression with *all* remaining bases at ∞ is
            # already at the target, finite positive bases strictly exceed it.
            if gl*a*factors[i]+gh*s >= target*m:
                return

            def possible(x):
                den, num_w, num_s = m, a, s
                for e in remaining:
                    z,w,h = local(x,e)
                    den *= z
                    num_w *= w
                    num_s *= h
                return gl*num_w+gh*num_s >= target*den

            # With all tail bases replaced by x, this is a decreasing upper
            # bound for any tail starting at x. The strict limit test above
            # guarantees a finite first failing x.
            if not possible(prev+1):
                return
            lo, hi = prev+1, 2*(prev+1)
            while possible(hi):
                lo, hi = hi, 2*hi
            while lo+1 < hi:
                mid = (lo+hi)//2
                if possible(mid):
                    lo = mid
                else:
                    hi = mid
            key = "max_q" if i == 0 else "max_later"
            c[key] = max(c[key],lo)
            for p in primes.interval(prev,lo):
                z,w,h = local(p,exps[i])
                descend(i+1,p,m*z,a*w,s*h,(*bases,p) if audit else ())

        descend(0,2,1,1,1,())
    return c


def run(start, stop, audit=False):
    primes = PrimeTable()
    total = Counter()
    for t in range(start,stop+1):
        cap = first_impossible_k(t)
        row = Counter()
        for exps in ordered_exponents(t):
            if len(exps) < 2:
                continue  # odd part equal to 1 or a prime power: separate exact argument
            if prod(e+2 for e in exps) % (1 << len(exps)):
                continue  # necessary 2-adic condition
            if all(e%2 == 0 for e in exps) and any(e%4 != 0 for e in exps):
                continue  # a square odd part of a solution must be a fourth power
            result = check_pattern(t, exps, cap, primes, audit)
            row["patterns"] += 1
            for name,n in result.items():
                if name.startswith("max_"):
                    row[name] = max(row[name],n)
                else:
                    row[name] += n
        for name,n in row.items():
            if name.startswith("max_"):
                total[name] = max(total[name],n)
            else:
                total[name] += n
        print(t,cap,row["patterns"],row["max_q"],row["max_later"],row["last_tests"],
              row["ordered_digits"],row["divisible"],row["prime_audits"],flush=True)
    return total


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--from", type=int, dest="start", default=2)
    parser.add_argument("--through", type=int, default=35)
    parser.add_argument("--audit", action="store_true", help="also re-evaluate the original divisor sums on each surviving prime")
    args = parser.parse_args()
    if not (2 <= args.start <= args.through):
        parser.error("expected 2 ≤ starting t ≤ final t")
    begin = monotonic()
    print("t first_impossible_k patterns max_q max_later last_tests ordered_digits divisible prime_audits",flush=True)
    counts = run(args.start,args.through,args.audit)
    print("complete",dict(sorted(counts.items())),"seconds",round(monotonic()-begin,3),flush=True)


if __name__ == "__main__":
    main()
