"""Decide both orientations of the A245212 families with a cube or fourth power.

The proof in cubic-power-family-245212.md shows K=k+1<320, a≤700,
and min(p,q)≤5K in the cases left after the 71-divisor exclusion.
Use --degree 4 for the fourth-power-family-245212.md cutoff. The last
base is inferred by exact division, not bounded in advance.
"""
from argparse import ArgumentParser
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
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


def check_base(job):
    p, degree, start, stop, first, last_exponent = job
    counts = Counter()
    fixed = moments(p, degree)
    # These moments do not depend on the dyadic exponent. Keep them local
    # to one prime so the largest integers are released after that job.
    variable = [(a, *moments(p, a)) for a in range(first, last_exponent + 1, 4)]
    for K in range(max(start, (p+4)//5), min(stop, 2*p) + 1):
        F, G, T = moments(2, K - 1)
        small = F*fixed[0], G*fixed[1], T*fixed[2]
        for a, v, s, t in variable:
            last(small, a, p, counts)
            last((F*v, G*s, T*t), degree, p, counts)
    return counts


def run(start, stop, degree=3, workers=1):
    first, last_exponent = (18, 700) if degree == 3 else (16, 1200)
    jobs = [(p, degree, start, stop, first, last_exponent) for p in range(11, 5*stop+1, 2)
            if prime(p) and 2*p >= start]
    if workers == 1:
        return sum(map(check_base, jobs), Counter())
    with ProcessPoolExecutor(max_workers=workers) as pool:
        return sum(pool.map(check_base, jobs, chunksize=1), Counter())


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--degree", type=int, choices=(3, 4), default=3)
    parser.add_argument("--jobs", type=int, default=6)
    parser.add_argument("--from-k-plus-one", type=int, default=1)
    parser.add_argument("--through-k-plus-one", type=int)
    args = parser.parse_args()
    maximum = 319 if args.degree == 3 else 447
    stop = maximum if args.through_k_plus_one is None else args.through_k_plus_one
    if not 1 <= args.from_k_plus_one <= stop <= maximum or args.jobs < 1:
        parser.error(f"use a subinterval of 1 through {maximum} and at least one worker")
    print(dict(run(args.from_k_plus_one, stop, args.degree, args.jobs)), flush=True)
