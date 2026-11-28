"""Reproduce the dyadic refinement of Nilsson's pinned 524,288-bin C1a witness.

Pass the original witness.json; its SHA-256 is checked. gmpy2 accelerates the
integer multiplication if available. No network access is needed by the checker.
"""
import argparse
from decimal import Decimal, localcontext
from fractions import Fraction
import hashlib
import json
from pathlib import Path


PARENT_SHA = "e413bfe3ca5248ebcb83474c19d432e265738c16c698d1054d4300b0eb294112"
PREVIOUS = Fraction(16124353801444301117880474240400261526455525552208409537172579155968,
                    10730507431658250947299700927335358497863186863726223329858730545929)


def parent(path):
    raw = path.read_bytes()
    if hashlib.sha256(raw).hexdigest() != PARENT_SHA:
        raise ValueError("expected the pinned Nilsson 524288-cell witness")
    a = json.loads(raw)["weights"]
    if len(a)!=524288 or any(type(x) is not int or x<0 for x in a):
        raise ValueError("invalid parent weights")
    return a


def refine(a):
    n = len(a)
    D = 10*n*n
    return [x*(D+v) for i,x in enumerate(a) for v in (2*n-i,i-2*n)]


def coefficients(a):
    try:
        from gmpy2 import mpz as integer
    except ImportError:
        integer = int
    n = len(a)
    # By Cauchy-Schwarz no coefficient exceeds sum a_i^2.
    width = (sum(x*x for x in a).bit_length()+7)//8
    poly = integer.from_bytes(b"".join(x.to_bytes(width,"little") for x in a),"little")
    digits = (poly*poly).to_bytes((2*n-1)*width,"little")
    return [int.from_bytes(digits[i:i+width],"little") for i in range(0,len(digits),width)]


def bound(a):
    c = coefficients(a)
    total = sum(a)
    assert sum(c)==total*total
    M=max(c)
    k=c.index(M)
    assert sum(a[i]*a[k-i] for i in range(max(0,k-len(a)+1),min(k,len(a)-1)+1))==M
    return k,Fraction(2*len(a)*M,total**2)


if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("source",type=Path)
    p.add_argument("--ntt",action="store_true",help="use independent modular transforms (NumPy)")
    args=p.parse_args()
    a=refine(parent(args.source))
    if args.ntt:
        from certify_autoconvolution_ntt import exact_score
        k,q=exact_score(a)
    else:
        k,q=bound(a)
    assert q < PREVIOUS
    print(f"bins={len(a)} peak_index={k}\n{q}")
    with localcontext() as ctx:
        ctx.prec=55
        print(Decimal(q.numerator)/Decimal(q.denominator))
