"""Probe Meštrović's three power-sum tests outside the complete n-range.

Usage: python3 three_factor_power_search.py To163.gz --largest 5000000 --smallest 257
For each largest prime r with irregular index k, invert one linear
congruence for q. Includes semiprimes and triples p*q*r, p<=q<=r.
All numerical hits still need a direct modular check at the exact powers.
"""
from argparse import ArgumentParser
from array import array
from bisect import bisect_left
import gzip
from math import gcd

BITS = 28


def rows(path, limit):
    with gzip.open(path, "rb") as data:
        for line in data:
            fields = line.partition(b";")[0].split()
            if len(fields) > 1:
                r = int(fields[0])
                if r <= limit:
                    for pair in fields[1:]:
                        yield r, int(pair.partition(b":")[0])


def indexed(path, limit):
    # Store packed exponent/prime pairs, not millions of Python tuples or
    # Bernoulli numerators. Sort only when a new run is out of order.
    runs = [array("Q")]
    for r, k in rows(path, limit):
        key = (r << BITS) | k
        if runs[-1] and runs[-1][-1] > key:
            runs.append(array("Q"))
        runs[-1].append(key)
    return runs


def contains(runs, p, k):
    key = (p << BITS) | k
    for run in runs:
        if run and run[0] <= key <= run[-1]:
            i = bisect_left(run, key)
            if i < len(run) and run[i] == key:
                return True
    return False


def probe(path, largest, smallest, cases):
    runs = indexed(path, largest)
    small = {}
    for run in runs:
        for i in range(bisect_left(run, (smallest+1) << BITS)):
            key = run[i]
            small.setdefault(key >> BITS, set()).add(key % (1 << BITS))
    seen = set()
    small_keys = (1, *sorted(small))
    for r, k in rows(path, largest):
        for c in cases:
            step = r-1 if c == 12 else 2*(r-1)
            offset = 1 if c == 16 else 3
            t = k+3 if c == 12 else 2*k+offset+1-r
            for p in small_keys:
                if p > r:
                    break
                d = gcd(p, step)
                if t % d:
                    continue
                period = step//d
                residue = (t//d) * pow(p//d, -1, period) % period
                low = max(p, 37)
                for q in range(low+(residue-low)%period, r+1, period):
                    n = p*q*r
                    if n % 2 == 0:
                        continue
                    e = n-offset if c == 12 else (n-offset)//2
                    if (p == 1 or e % (p-1) in small[p]) and contains(runs, q, e % (q-1)):
                        result = (c,n,p,q,r)
                        if result not in seen:
                            seen.add(result)
                            yield result


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("table")
    parser.add_argument("--largest", type=int, required=True)
    parser.add_argument("--smallest", type=int, default=157)
    parser.add_argument("--cases", nargs="+", type=int, choices=[12,15,16], default=[12,15,16])
    args = parser.parse_args()
    for result in probe(args.table,args.largest,args.smallest,args.cases):
        print(*result, flush=True)
