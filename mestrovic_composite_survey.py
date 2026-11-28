"""Find candidate composites for Meštrović, Conjectures 12, 15 and 16.

python3 mestrovic_composite_survey.py /path/to/To163.gz --bound 564458189

For largest prime P and n=P*m, each irregular index fixes m modulo
P-1 (ordinary exponent) or 2(P-1) (half exponent). The bounds are on n,
include prime powers and do not require n to be squarefree. Candidates
still need direct prime-power verification.
"""
from argparse import ArgumentParser
from array import array
import gzip
import hashlib
from math import isqrt
from mestrovic_power_witness import cubic_test


def tables(path, bound):
    # For odd composites every prime factor must be irregular; 37 is the first.
    limit = max(37, bound // 37)
    sieve = bytearray([1]) * (limit + 1)
    sieve[:2] = bytes(2)
    for p in range(2, isqrt(limit) + 1):
        if sieve[p]:
            sieve[p*p::p] = bytes(1 + (limit-p*p)//p)
    irregular = {}
    checksum = hashlib.md5(usedforsecurity=False)
    with gzip.open(path, "rb") as rows:
        for line in rows:
            checksum.update(line)
            fields = line.partition(b";")[0].split()
            p = int(fields[0])
            if p > limit:
                continue
            if not sieve[p]:
                raise ValueError(f"nonprime or duplicate prime in required data: {p}")
            sieve[p] = 0
            if len(fields) > 1:
                irregular[p] = tuple(int(f.partition(b":")[0]) for f in fields[1:])
    if checksum.hexdigest() != "a9b0eb7c97a5e9d2163936ea145d70a6":
        raise ValueError("the file does not match the published To163.gz uncompressed digest")
    missing = sieve.find(1)
    if missing >= 0:
        raise ValueError(f"missing prime row: {missing}")
    if min(irregular) != 37:
        raise ValueError("unexpected first irregular prime")
    # For odd composites store a small prime divisor; unset means prime or 1.
    divisor = array("H", [0]) * (limit//2 + 1)
    for p in range(3, isqrt(limit) + 1, 2):
        if not divisor[p//2]:
            start = p*p//2
            divisor[start::p] = array("H", [p]) * (1 + (len(divisor)-1-start)//p)
    return irregular, divisor


def admissible(m, largest, e, irregular, divisor):
    while m > 1:
        p = divisor[m//2] or m
        if p > largest or e % (p-1) not in irregular.get(p, ()):
            return False
        while m % p == 0:
            m //= p
    return True


def possible(bound, irregular, divisor):
    for p, indices in irregular.items():
        for k in indices:
            for conjecture, decrement, stride, residue in (
                (12, 3, p-1, k+3),
                (15, 3, 2*(p-1), 2*k+4-p),
                (16, 1, 2*(p-1), 2*k+2-p),
            ):
                first = 37 + (residue-37) % stride
                for m in range(first, bound//p + 1, stride):
                    n = p*m
                    assert n % 2 == 1
                    e = n-decrement if conjecture == 12 else (n-decrement)//2
                    if admissible(m, p, e, irregular, divisor):
                        yield conjecture, n


def direct_index_control(bound, irregular):
    """Slow loop over n for testing the optimized largest-factor enumeration."""
    hits = set()
    for n in range(3, bound+1, 2):
        m, p, primes = n, 3, set()
        while p*p <= m:
            if not m % p:
                primes.add(p)
                while not m % p:
                    m //= p
            p += 2
        if m != 1:
            primes.add(m)
        if n in primes:
            continue
        for c, e in [(12, n-3), (15 if n%4 == 3 else 16, (n-(3 if n%4 == 3 else 1))//2)]:
            if all(e % (r-1) in irregular.get(r, ()) for r in primes):
                hits.add((c, n))
    return hits


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("table")
    parser.add_argument("--bound", type=int, required=True)
    parser.add_argument("--verify", action="store_true",
                        help="evaluate the defining power sum modulo each exact prime-power factor of n³")
    args = parser.parse_args()
    indices, divisors = tables(args.table, args.bound)
    control = min(50000, args.bound)
    assert set(possible(control, indices, divisors)) == direct_index_control(control, indices)
    print(f"Verified prime-row coverage to {max(37, args.bound//37):,}; bound on n: {args.bound:,}", flush=True)
    for c, n in sorted(possible(args.bound, indices, divisors)):
        if args.verify:
            residues = cubic_test(n, c != 12)
            result = "passes" if all(s == 0 for _, _, s in residues) else "fails"
            print(f"Conjecture {c}: {n} {result}: {residues}", flush=True)
        else:
            print(f"Conjecture {c}: {n}", flush=True)
