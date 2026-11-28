"""Exhaust the A245212 rank-two boxes left by the integer enclosures.

Run python3 two_odd_replay_245212.py --jobs 6. Exact integer arithmetic
throughout. No congruence classes of exponents are assumed or skipped.
"""
from argparse import ArgumentParser
from bisect import bisect_left, bisect_right
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
from functools import lru_cache
from math import isqrt

from two_odd_boxes_245212 import reduce


def prime_bases(limit):
    return [p for p in range(13, limit+1, 2)
            if all(p % d for d in range(3, isqrt(p)+1, 2))]


@lru_cache(maxsize=32768)
def moments(base, length):
    """Weighted sum W, ordinary sum S, and n*τ(n) at n=base^(length-1)."""
    power = base**(length-1)
    ordinary = (base*power-1)//(base-1)
    top = length*power
    weighted = (base*top-ordinary)//(base-1)
    return weighted, ordinary, top


def sweep(m):
    _, boxes = reduce(m, 512*m**4, precision=12)
    primes = prime_bases(3*max((box[1] for box in boxes), default=0))
    counts = Counter()
    for first, last, lo, hi, swapped in boxes:
        for K in range(first, last+1):
            F, G, T = moments(2, K)
            for M in range(lo, hi+1):
                B, C = (m, M) if swapped else (M, m)
                counts["cells"] += 1
                lower = max(13, 1+(K-1)*(B-1)//B)
                for i in range(bisect_left(primes, lower), bisect_right(primes, 3*K)):
                    p = primes[i]
                    W, S, U = moments(p, B)
                    a, s, t = F*W, G*S, T*U
                    counts["prime_cases"] += 1
                    denominator = (2*t-a)*C-s
                    if denominator <= 0:
                        continue
                    q = (a*(C-1)+s-1)//denominator+1
                    if q <= p or (a+s) % q:
                        continue
                    counts["divisible"] += 1
                    V, ordinary, top = moments(q, C)
                    if a*V+s*ordinary == 2*t*top:
                        raise ArithmeticError(f"Exact balance at {K=}, {B=}, {C=}, {p=}, {q=}")
    return m, counts


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--minimum", type=int, default=6)
    parser.add_argument("--maximum", type=int, default=32)
    parser.add_argument("--jobs", type=int, default=6)
    args = parser.parse_args()
    if not (6 <= args.minimum <= args.maximum <= 32) or args.jobs < 1:
        parser.error("use 6<=minimum<=maximum<=32 and at least one worker")
    total = Counter()
    with ProcessPoolExecutor(max_workers=args.jobs) as pool:
        for m, counts in pool.map(sweep, range(args.minimum, args.maximum+1)):
            print(m, dict(counts), flush=True)
            total.update(counts)
    print("Total:", dict(total))
