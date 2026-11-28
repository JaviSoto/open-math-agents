"""Fixed k=1, odd bases 3<q<r, q>=17: exact three-prime reverse-digit check.

Run python3 rank_three_large_middle_245212.py, or add --q 17 --r 19 for
one support. Counts cover overlapping choices of two small prime powers.
The small-power bounds use simultaneous Euler rounding, at global height
ceiling(4,r); see GuardedHeight245212 and RankThreeCap245212.
"""
import argparse
from collections import Counter
from functools import cache
from itertools import permutations
from math import isqrt, prod


def prime(n):
    return n >= 2 and all(n % j for j in range(2, isqrt(n) + 1))


def ceiling(bound):
    slope = 64
    offset = 16 * (7 + (9 + 2 * bound) * bound.bit_length())
    t = max(256 * slope**2, 2 * offset + 1)
    while (next_t := offset + slope * t.bit_length()) < t:
        t = next_t
    return t


def ilog(p, n):
    e, u = 0, 1
    while u*p <= n:
        u *= p
        e += 1
    return e


@cache
def moments(p, e):
    v = p**e
    s = (v*p-1)//(p-1)
    t = (e+1)*v
    w = (p*t-s)//(p-1)
    return w, s, t


def support(q, r):
    bases = (3, q, r)
    den = 5 * prod(bases)
    diff = den - 8 * 2 * (q-1) * (r-1)
    assert diff > 0
    E = ceiling(r)
    M = 2 * 64 * r**9 * (E+1)**4
    # The multiplier 2 accounts for the unrounded dyadic prime.
    lo = {p: max(1, (den+p*diff-1)//(p*diff)-1) for p in bases}
    first = {p: ilog(p, M) for p in bases}
    for p,j,l in permutations(bases):
        # Complementary finite Euler factors, including the dyadic one, are <=1.
        assert 4*(p-1) < (first[j]+2)*(first[l]+2)
    out = Counter()
    for p,j,l in permutations(bases):
        for e in range(lo[p], first[p]+1):
            W, S, T = moments(p,e)
            if 5*W*j*l < 8*T*(j-1)*(l-1):
                continue
            out["prefix"] += 1
            limit = max(ilog(j, M*p**e), 4*(l-1)//(e+1))
            assert 4*(l-1) < (e+1)*(limit+2)
            for f in range(lo[j],limit+1):
                w,s,t = moments(j,f)
                A,B,H = 5*W*w,3*S*s,4*T*t
                if A*l < 2*H*(l-1):
                    continue
                out["pairs"] += 1
                h = (l-1)*B-A
                if h % l:
                    continue
                out["mod_prime"] += 1
                C, D = l*h, (l-1)*(2*H*(l-1)-l*A)
                if not D or not C:
                    # A genuine solution has nonzero latter cofactor difference.
                    continue
                length = C//D
                if length-1 < lo[l] or length > abs(C).bit_length():
                    continue
                if C == (C-D*length)*l**length:
                    raise ArithmeticError((p,e,j,f,l,length-1))
    return out


def main():
    args = argparse.ArgumentParser(description=__doc__)
    args.add_argument("--q", type=int)
    args.add_argument("--r", type=int)
    arg = args.parse_args()
    count, all_results = 0, Counter()
    for q in range(17,32):
        if not prime(q) or arg.q not in (None,q):
            continue
        for r in range(q+1,16*(q-1)//(q-16)+1):
            if not prime(r) or arg.r not in (None,r):
                continue
            out = support(q,r)
            count += 1
            all_results.update(out)
    print(f"{count} supports; {dict(all_results)}; no equalities")


if __name__ == "__main__":
    main()
