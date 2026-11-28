"""Intersect Hart–Harvey–Ong's complete prime table with the surviving small cofactors.

Use --archive twobillion.tar.bz2 to work offline; with no argument the authors'
archive is streamed without retaining it. The program checks their uncompressed
MD5, strict prime ordering, total records, and the published irregularity census.
"""
import argparse
import hashlib
import json
from pathlib import Path
import tarfile
from urllib.request import Request, urlopen


SOURCE = "https://web.maths.unsw.edu.au/~davidharvey/research/twobillion.tar.bz2"
DIGEST = "1058f8add5f70c71d578c7cd87e00a7e"
EXPECTED = [63751120,31873681,7963496,1326171,165211,16410,1384,86,4,1]
START = 63_917_461


def inspect(rows):
    digest = hashlib.md5(usedforsecurity=False)
    counts = [0]*10
    previous = 1
    quarter, half, prime_half = [], [], []
    candidates = []
    for line in rows:
        digest.update(line)
        fields = line.split()
        if not fields:
            continue
        q = int(fields[0])
        if q <= previous or q >= 2**31:
            raise ValueError(f"Prime out of order or outside range: {q}, after {previous}")
        previous = q
        counts[len(fields)-1] += 1
        for term in fields[1:]:
            k = int(term)
            if 2*k == q-1:
                prime_half.append(q)
            if q < START:
                continue
            if k == 6260:
                candidates.append(("quartic",6263,q))
                if (6263*q-3) % 6262 == 3286:
                    quarter.append(6263*q)
            m = 2*k-q+2
            if m in (59,379,59*379):
                candidates.append(("half",m,q))
                n = m*q
                e = (n-1)//2
                if (n%4 == 1 and (m%59 or e%58==44)
                        and (m%379 or e%378==174)):
                    half.append(n)
    if digest.hexdigest() != DIGEST or counts != EXPECTED:
        raise ValueError(f"File does not match HHO: {digest.hexdigest()}, {counts}")
    return dict(source=SOURCE,md5=DIGEST,records=sum(counts),largest=previous,
                candidates=candidates,quartic=quarter,half=half,primeHalf=prime_half)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive",type=Path)
    args = parser.parse_args()
    stream = (args.archive.open("rb") if args.archive else
              urlopen(Request(SOURCE,headers={"User-Agent":"Mestrovic prime cofactor research"}),timeout=90))
    with stream, tarfile.open(fileobj=stream,mode="r|bz2") as archive:
        for member in archive:
            if member.name == "twobillion/indices.txt" and member.isfile():
                with archive.extractfile(member) as rows:
                    result = inspect(rows)
                print(json.dumps(result,indent=2))
                return
    raise ValueError("The published irregular-index file is missing")


if __name__ == "__main__":
    main()
