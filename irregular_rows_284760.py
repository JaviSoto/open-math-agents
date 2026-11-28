"""Filter every documented Buhler–Harvey irregular row for the A284760 digit.

Run with python3 irregular_rows_284760.py. The source gzips 113,549,054 bytes;
records are streamed, including their published uncompressed MD5 check. Output
contains the surviving (p,k,s,t) rows, not a proof that one is a counterexample.
See https://people.reed.edu/~jpb/bernoulli/ for the definitions of s and t.
"""
import gzip
import hashlib
import json
import re
import argparse
from pathlib import Path
from math import isqrt
from urllib.request import Request, urlopen

SOURCE = "https://people.reed.edu/~jpb/bernoulli/To163.gz"
REFERENCE_MD5 = "a9b0eb7c97a5e9d2163936ea145d70a6"


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--gzip",type=Path,help="Use an existing compressed copy of the published table.")
    args=parser.parse_args()
    checksum = hashlib.md5(usedforsecurity=False)
    pair_count = prime_count = largest = 0
    seen = bytearray(1 + 163_577_856 // 8)
    survivors, repeated = [], []
    source=(args.gzip.open("rb") if args.gzip else
            urlopen(Request(SOURCE, headers={"User-Agent": "A284760 research check"}), timeout=90))
    with source as stream:
        with gzip.GzipFile(fileobj=stream) as rows:
            for line in rows:
                checksum.update(line)
                fields = line.split(b";", 1)[0].split()
                if not fields:
                    continue
                p = int(fields[0])
                byte, bit = divmod(p, 8)
                if seen[byte] & (1 << bit):
                    repeated.append(p)
                else:
                    seen[byte] |= 1 << bit
                    prime_count += 1
                largest = max(largest, p)
                for field in fields[1:]:
                    match = re.fullmatch(rb"(\d+):(\d+),(\d+),(\d+)", field)
                    if not match:
                        raise ValueError(f"Unrecognized record at {p}: {field!r}")
                    k, _, s, t = map(int, match.groups())
                    pair_count += 1
                    if (s + (k + 3) * (t - s)) % p == 0:
                        survivors.append((p, k, s, t))
    if checksum.hexdigest() != REFERENCE_MD5:
        raise ValueError("Data digest differs from the published reference")
    odd_prime = bytearray(b"\1") * (1 + largest // 2)
    odd_prime[0] = 0
    for p in range(3, isqrt(largest) + 1, 2):
        if odd_prime[p // 2]:
            first = p*p//2
            odd_prime[first::p] = bytes(1+(len(odd_prime)-1-first)//p)
    missing_count, first_missing = 0, None
    for i, is_prime in enumerate(odd_prime):
        if is_prime:
            p=2*i+1
            if not seen[p//8] & (1 << (p%8)):
                missing_count += 1
                if first_missing is None:
                    first_missing = p
    print(json.dumps(dict(source=SOURCE, md5=checksum.hexdigest(), largestPrime=largest,
                          primeCount=prime_count, duplicateRowCount=len(repeated),
                          missingPrimeCount=missing_count, firstMissingPrime=first_missing,
                          pairCount=pair_count, survivors=survivors), indent=2))


if __name__ == "__main__":
    main()
