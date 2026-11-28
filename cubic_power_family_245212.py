"""Decide both orientations of the A245212 family 2^k p^a q^3.

The proof in cubic-power-family-245212.md shows K=k+1<320, a≤700,
and min(p,q)≤5K in the cases left after the 71-divisor exclusion.
The last base is inferred by exact division, not bounded in advance.
"""
from argparse import ArgumentParser
from collections import Counter
from math import isqrt


def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def moments(p, e):
    power = p**e
    ordinary = (p*power - 1)//(p - 1)
    top = (e + 1)*power
    return (p*top - ordinary)//(p - 1), ordinary, top


def last(cofactor, exponent, first_prime, counts):
    w, s, t = cofactor
    counts["inputs"] += 1
    den = (2*t - w)*(exponent + 1) - s
    if den <= 0:
        return
    counts["positive_denominator"] += 1
    q = (w*exponent + s - 1)//den + 1
    if q <= first_prime or (w + s) % q:
        return
    counts["divisible"] += 1
    v, ordinary, top = moments(q, exponent)
    if w*v + s*ordinary == 2*t*top:
        raise ArithmeticError(f"Exact candidate: {first_prime=}, {q=}, {exponent=}")


def run(start, stop):
    primes = [p for p in range(11, 5*stop + 1, 2) if prime(p)]
    counts = Counter()
    for K in range(start, stop + 1):
        F, G, T = moments(2, K - 1)
        for p in primes:
            if p > 5*K:
                break
            if 2*p <= K - 1:
                continue
            v, s, t = moments(p, 3)
            cube = F*v, G*s, T*t
            # A nonsquare odd core has an exponent 2 modulo 4. The other
            # exponent here equals 3. Counts through 71 settle a<18.
            for a in range(18, 701, 4):
                last(cube, a, p, counts)
                v, s, t = moments(p, a)
                last((F*v, G*s, T*t), 3, p, counts)
    return counts


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--from-k-plus-one", type=int, default=1)
    parser.add_argument("--through-k-plus-one", type=int, default=319)
    args = parser.parse_args()
    if not 1 <= args.from_k_plus_one <= args.through_k_plus_one <= 319:
        parser.error("use a subinterval of 1 through 319")
    print(dict(run(args.from_k_plus_one, args.through_k_plus_one)), flush=True)
