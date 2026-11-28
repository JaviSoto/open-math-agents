"""Census for the original cubic conjecture beyond the first missing table row.

python3 cubic_census_284759.py To163.gz --bound 80000000000 --workers 5
Only the independently checked contiguous prime prefix is used. Above it,
the cofactor bound tests exact Bernoulli numerators instead of table rows.
"""
from argparse import ArgumentParser
from concurrent.futures import ProcessPoolExecutor
from fractions import Fraction
from math import comb, gcd, isqrt
from mestrovic_composite_survey import admissible, direct_index_control, tables
from mestrovic_power_witness import cubic_test, prime_powers


def even_bernoulli(max_index):
    """Exact B_2j from the tangent-number triangle; entry 0 is B_0."""
    count = max_index // 2
    tangent = [1] * (count + 1)
    for j in range(2, count + 1):
        tangent[j] = (j-1) * tangent[j-1]
    for k in range(2, count + 1):
        for j in range(k, count + 1):
            tangent[j] = (j-k) * tangent[j-1] + (j-k+2) * tangent[j]
    values = [Fraction(1)]
    for j in range(1, count + 1):
        power = 1 << (2*j)
        values.append(Fraction((-1)**(j-1) * 2*j * tangent[j], power*(power-1)))
    # Independently check the defining recurrence at low and large indices.
    for j in sorted({*range(1, min(12, count)+1), count} - {0}):
        order = 2*j+1
        assert sum(comb(order, 2*i)*values[i] for i in range(j+1)) == Fraction(order, 2)
    return values


def smooth_factors(primes, limit, end):
    """Unique nonincreasing factor lists for all nontrivial smooth integers."""
    def visit(prefix, factors, end):
        for index in range(end):
            p = primes[index]
            product = prefix * p
            if product > limit:
                break
            new = factors + (p,)
            yield product, new
            yield from visit(product, new, index+1)
    yield from visit(1, (), end)


def lower_range(bound, cap, indices, divisors):
    small = max(37, (bound+cap-1)//cap)
    primes = sorted(p for p in indices if p <= small)
    for idx, p in enumerate(primes):
        for m, factors in smooth_factors(primes, bound//p, idx+1):
            e = p*m-3
            if e % (p-1) in indices[p] and all(e % (q-1) in indices[q] for q in factors):
                yield p*m
    for p, rows in indices.items():
        if p <= small:
            continue
        for k in rows:
            first = 37 + (k+3-37) % (p-1)
            for m in range(first, bound//p+1, p-1):
                if admissible(m, p, p*m-3, indices, divisors):
                    yield p*m


def upper_job(job):
    m, bottom, top, numerator, rows = job
    # Solve the strongest individual modulus for P, then check the others.
    bands = []
    for q, indices in rows:
        d = gcd(m, q-1)
        period = (q-1)//d
        inverse = pow(m//d, -1, period)
        residues = {((k+3)//d)*inverse % period for k in indices if (k+3)%d == 0}
        if not residues:
            return []
        bands.append((Fraction(len(residues),period), period, residues))
    _, period, residues = min(bands, key=lambda band:band[0])
    results = []
    for residue in residues:
        for p in range(bottom+(residue-bottom)%period, min(top,numerator)+1, period):
            if numerator % p:
                continue
            if any((p*m-3) % (q-1) not in indices for q, indices in rows):
                continue
            if all(p%d for d in range(2, isqrt(p)+1)):
                results.append(p*m)
    return results


def census(bound, cap, indices, divisors, workers):
    hits = set(lower_range(bound, cap, indices, divisors))
    max_m = bound//(cap+1)
    if max_m < 37:
        return hits
    # This split puts P above sqrt(bound), hence m<P and the bound applies.
    if cap < isqrt(bound):
        raise ValueError("table prefix must cover the square root of the bound")
    values = even_bernoulli(max_m-3)
    jobs = []
    for m in range(37, max_m+1, 2):
        factors = [p for p, _ in prime_powers(m)]
        if all(p in indices for p in factors):
            jobs.append((m, cap+1, bound//m, abs(values[(m-3)//2].numerator),
                         [(p, indices[p]) for p in factors]))
    with ProcessPoolExecutor(max_workers=workers) as pool:
        for outer_hits in pool.map(upper_job, jobs):
            hits.update(outer_hits)
    return hits


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("table")
    parser.add_argument("--bound", type=int, required=True)
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--cap", type=int, default=63917460)
    args = parser.parse_args()
    cap = min(args.cap, max(37, args.bound//37))
    indices, divisors = tables(args.table, cap*37)
    control = min(50000, args.bound)
    assert set(lower_range(control,cap,indices,divisors)) == {
        n for c,n in direct_index_control(control,indices) if c==12}
    print(f"Complete prime prefix: {cap:,}; upper n: {args.bound:,}", flush=True)
    for n in sorted(census(args.bound,cap,indices,divisors,args.workers)):
        result = cubic_test(n, False)
        print(n, "passes" if all(r==0 for _,_,r in result) else "fails", result, flush=True)
