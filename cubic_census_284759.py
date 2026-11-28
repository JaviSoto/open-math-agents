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


def cofactor_class(p, k, case):
    if case==12:
        return p-1, k+3
    return 2*(p-1), 2*k+(4 if case==15 else 2)-p


def reduced_exponent(n,case):
    return n-3 if case==12 else (n-(3 if case==15 else 1))//2


def smooth_hits(p, primes, limit, indices, case):
    """Generate the smaller factors in order; solve for the last one modulo p−1."""
    def visit(prefix, factors, start):
        low = primes[start]
        top = min(p, limit//prefix)
        modulus = (p-1)*(1 if case==12 else 2)
        d = gcd(prefix,modulus)
        step = modulus//d
        inverse = pow(prefix//d, -1, step)
        for k in indices[p]:
            _,target=cofactor_class(p,k,case)
            if target%d:
                continue
            residue = target//d*inverse % step
            for q in range(low+(residue-low)%step, top+1, step):
                if q not in indices:
                    continue
                n = p*prefix*q
                e=reduced_exponent(n,case)
                if e%(q-1) in indices[q] and all(e%(r-1) in indices[r] for r in factors):
                    yield n
        for index in range(start,len(primes)):
            r = primes[index]
            if r>p or prefix*r*r>limit:
                break
            yield from visit(prefix*r, factors+(r,), index)
    yield from visit(1, (), 0)


def lower_range(bound, cap, indices, divisors, case=12):
    small = max(37, (bound+cap-1)//cap)
    primes = sorted(p for p in indices if p <= small)
    for p in primes:
        yield from smooth_hits(p, primes, bound//p, indices, case)
    for p, rows in indices.items():
        if p <= small:
            continue
        for k in rows:
            step, residue = cofactor_class(p,k,case)
            first = 37 + (residue-37)%step
            for m in range(first, bound//p+1, step):
                if admissible(m,p,reduced_exponent(p*m,case),indices,divisors):
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
    parser.add_argument("--prefix-case",type=int,choices=[12,15,16],
                        help="only test products with largest prime in the audited prefix, for the selected test")
    args = parser.parse_args()
    cap = min(args.cap, max(37, args.bound//37))
    indices, divisors = tables(args.table, cap*37)
    control = min(50000, args.bound)
    case=args.prefix_case or 12
    assert set(lower_range(control,cap,indices,divisors,case)) == {
        n for c,n in direct_index_control(control,indices) if c==case}
    print(f"Complete prime prefix: {cap:,}; upper n: {args.bound:,}", flush=True)
    if args.prefix_case:
        print(f"Conjecture {case}: largest prime factor at most {cap:,}",flush=True)
        hits=set(lower_range(args.bound,cap,indices,divisors,case))
    else:
        hits=census(args.bound,cap,indices,divisors,args.workers)
    for n in sorted(hits):
        result = cubic_test(n, case!=12)
        print(n, "passes" if all(r==0 for _,_,r in result) else "fails", result, flush=True)
    print(f"{len(hits)} index candidates",flush=True)
