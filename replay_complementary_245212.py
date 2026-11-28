"""Independent divisor-recurrence replay for the d=3 and d=4 finite boxes.

Use --degree 3 or 4. This checks a different necessary congruence (mod q²)
and uses the strict leading-digit inequalities, ahead of the full balance.
"""
from argparse import ArgumentParser
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
from math import isqrt


def verify(w, s, t, f, p, counts):
    den = 2*t*(f+1) - w*(f+1) - s
    if den <= 0:
        return
    floor, rem = divmod(w*f+s, den)
    if not rem:  # For f>1 both ends of the interval are strict.
        return
    q = floor+1
    difference = w-(q-1)*s
    if q <= p or difference % (q*q):
        return
    counts["square_congruence"] += 1
    power = q**f
    if not difference or difference % power:
        return
    counts["full_congruence"] += 1
    digit_sum = 0
    for j in reversed(range(f)):
        digit_sum = digit_sum*q + (j+1)*w + s
    if digit_sum == den*power:
        raise ArithmeticError(f"Exact balance at {p=}, {q=}, {f=}")


def check(job):
    p, d, maximum, exponents = job
    counts = Counter()
    power = w = s = 1
    values = {}
    for j in range(1, exponents[-1]+1):
        power *= p
        s += power
        w += (j+1)*power
        if j == d or j in exponents:
            values[j] = w, s, (j+1)*power
    for a in exponents:
        wa, sa, ta = values[a]
        wc, sc, tc = values[d]
        for K in range((p+4)//5, min(maximum,2*p)+1):
            z = 1 << K
            f2, g2, t2 = 1+(K-1)*z, z-1, K*(z//2)
            verify(f2*wa, g2*sa, t2*ta, d, p, counts)
            verify(f2*wc, g2*sc, t2*tc, a, p, counts)
            counts["triples"] += 1
    return counts


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--degree", type=int, choices=(3,4), required=True)
    parser.add_argument("--jobs", type=int, default=5)
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("use at least one worker")
    K, exps = (319,range(18,701,4)) if args.degree==3 else (447,range(16,1201,4))
    jobs = [(p,args.degree,K,exps) for p in range(11,5*K+1,2)
            if all(p%i for i in range(3,isqrt(p)+1,2))]
    with ProcessPoolExecutor(max_workers=args.jobs) as pool:
        print(dict(sum(pool.map(check,jobs,chunksize=1),Counter())))
