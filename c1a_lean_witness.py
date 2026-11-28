"""Generate a compact integer witness and exact peak proposal for the pinned Lean checker."""
import argparse
import hashlib
import json
from pathlib import Path

from nilsson_refinement import coefficients, parent


def optimized(a):
    n=len(a)
    D=100*n*n
    S=sum(a)
    scale=n*10**14
    # Rational affine skew fitted on the integer peak gaps, then rounded to
    # a smaller integer grid for a substantially smaller kernel certificate.
    return [(2*scale*h*(D+u)+D*S)//(2*D*S)
            for i,h in enumerate(a) for u in (87*n-73*i,73*i-87*n)]


def write_proposal(a,witness,proposal):
    raw=json.dumps({"weights":a},separators=(",",":")).encode("ascii")
    c=coefficients(a)
    S=sum(a)
    M=max(c)
    assert sum(c)==S*S
    witness.write_bytes(raw)
    receipt={"sha256":hashlib.sha256(raw).hexdigest(),"N":len(a),"sum_a":str(S),"max_conv":str(M)}
    proposal.write_text(json.dumps(receipt,indent=2)+"\n")
    from fractions import Fraction
    from decimal import Decimal, localcontext
    q=Fraction(2*len(a)*M,S*S)
    print(c.index(M),q)
    with localcontext() as ctx:
        ctx.prec=52
        print(Decimal(q.numerator)/Decimal(q.denominator))


if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("parent",type=Path)
    p.add_argument("certificate",type=Path)
    p.add_argument("receipt",type=Path)
    args=p.parse_args()
    write_proposal(optimized(parent(args.parent)),args.certificate,args.receipt)
