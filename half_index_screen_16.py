"""Screen Buhler–Harvey's two half-rows for Meštrović Conjecture 16.

Supply the original To163.gz as the sole argument. The checksum and the first
gap of the reference table are documented in quartic-bernoulli-284760.md.
For each p the condition is 2s+(2k+1)(t−s) = 0 (mod p), since
2e+1=n for e=(n−1)/2.
"""
import argparse
import gzip
import hashlib
import re

REFERENCE_MD5 = "a9b0eb7c97a5e9d2163936ea145d70a6"


def screen(path):
    digest = hashlib.md5(usedforsecurity=False)
    hits = []
    total = 0
    fields = re.compile(rb"(\d+):(\d+),(\d+),(\d+)")
    with gzip.open(path, "rb") as table:
        for line in table:
            digest.update(line)
            entries = line.partition(b";")[0].split()
            if not entries:
                continue
            p = int(entries[0])
            for item in entries[1:]:
                match = fields.fullmatch(item)
                if not match:
                    raise ValueError(f"Malformed entry for {p}")
                k, _, s, t = map(int, match.groups())
                if (2*s+(2*k+1)*(t-s)) % p == 0:
                    hits.append((p,k,s,t))
                total += 1
    if digest.hexdigest() != REFERENCE_MD5:
        raise ValueError("Published MD5 differs")
    return total, hits


def complete(p, k):
    """The first digit is forced by 2e+1=0 mod p and the second by p²|n."""
    lift=(2*k+1)*pow(2,-1,p)%p
    a=k+(p-1)*lift
    square, cube = p**2, p**3
    first=delta=0
    for i in range(1,p):
        value=pow(i,a,cube)
        first+=value
        delta+=(value%p)*((pow(i,p-1,square)-1)//p)
    return a,first%cube,(first+square*delta)%cube


def repeated(p,k):
    e=k+(p-1)*((2*k+1)*pow(2,-1,p*p)*(1+p)%(p*p))
    high=sum(pow(i,e,p**4) for i in range(1,p))%p**4
    low=sum(pow(i,e-2,p*p) for i in range(1,p))%(p*p)
    return e,(6*high-e*(e-1)*p*p*low)%p**4


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("table")
    total, hits = screen(parser.parse_args().table)
    print(total, "irregular pairs checked")
    for row in hits:
        print(*row)
    for p,k,_,_ in hits:
        print("complete",p,k,*complete(p,k),flush=True)
        if p in (59,379):
            print("repeat",p,k,*repeated(p,k),flush=True)
