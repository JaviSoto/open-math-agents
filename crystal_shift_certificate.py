"""Exact finite certificate for two collisions in the same (q-4) squareclass.

Run with python3 crystal_shift_certificate.py (standard library only).
The three enumerations and their explicit upper limits are proved in
crystal-shift-exclusion.md. Same-*parameter*-squareclass is a separately
Lean-proved exclusion; the certificate can skip that case.
"""
from functools import cache
from math import isqrt
from sys import argv


def parameters(d):
    """Return squarefree s and A > 0 such that d = s*A^2."""
    s, a, k = d, 1, 2
    while k*k <= s:
        while s % (k*k) == 0:
            s //= k*k
            a *= k
        k += 1
    return s, a


def value(q, r):
    x, y = 0, 1
    for _ in range(r):
        x, y = y, (q-2)*y - x + 2
    return (2*x-1)*(2*y-1)


@cache
def images(p):
    result = []
    for q in range(p):
        x, y = 0, 1
        attained = set()
        while True:
            attained.add(((2*x-1)*(2*y-1)) % p)
            x, y = y, ((q-2)*y - x + 2) % p
            if (x, y) == (0, 1):
                break
        result.append(attained)
    return result


@cache
def sieve(p, r):
    """Rows q mod p, columns Q mod p; True only means equality possible."""
    vals = [value(Q, r) % p for Q in range(p)]
    return [tuple(v in image for v in vals) for image in images(p)]


@cache
def divisors(n):
    return tuple(k for i in range(1, isqrt(n)+1) if n % i == 0
                 for k in ((i,) if i*i == n else (i, n//i)))


def finite_small():
    for q in range(5, 26):
        s, a = parameters(q-4)
        for r in range(2, 28):
            for b in range(a+1, 16*(8*r+9)*a):
                yield q, s*b*b+4, r


def finite_cubic():
    for q in range(26, 17000):
        s, a = parameters(q-4)
        for b in range(a+1, 23*a):
            Q = s*b*b+4
            # Distinct parameters in the same cubic row cannot collide.
            if value(q, 3) <= value(Q, 2):
                yield q, Q, 2


def finite_sparse():
    for r in range(3, 16):
        for s in range(1, 176*r):
            if parameters(s)[1] != 1:
                continue
            for a in range(1, (176*r-1)//s+1):
                d = s*a*a
                if d < 22:
                    continue
                for h in range(1, (176*r-1)//(s*a)+1):
                    for b in divisors(a*(8*r-2)+h):
                        if a < b < 16*a*r and h*d < 11*b and 2*h < b:
                            yield d+4, s*b*b+4, r


def check(rows, use_sieve):
    count = exact = 0
    collisions = []
    for q, Q, r in rows:
        count += 1
        if isqrt(q*Q)**2 == q*Q:
            continue
        if use_sieve and any(not sieve(p, r)[q % p][Q % p] for p in (5,7,11,13,17,19,23)):
            continue
        exact += 1
        n = value(Q, r)
        x, y = q, (q-1)**2
        while (2*x-1)*(2*y-1) < n:
            x, y = y, (q-2)*y-x+2
        if (2*x-1)*(2*y-1) == n:
            collisions.append((q, Q, r, n))
    return count, exact, collisions


if __name__ == "__main__":
    # Dist(q*sqrt(q/(q-4)), Z) > 1/16 for these small q. All closest
    # integers h lie in [0,100] since 0<q*sqrt(q/(q-4))<100.
    for q in range(5, 26):
        assert q**3 < 100**2*(q-4)
        for h in range(101):
            assert not ((q-4)*max(0,16*h-1)**2 <= 256*q**3 <= (q-4)*(16*h+1)**2)
    for name, rows in (("q≤25", finite_small()), ("large cubic", finite_cubic()),
                       ("large sparse", finite_sparse())):
        num, tested, hits = check(rows, "--no-sieve" not in argv)
        print(name, "candidate triples", num, "exact tests", tested, "collisions", hits,
              flush=True)
        assert not hits
