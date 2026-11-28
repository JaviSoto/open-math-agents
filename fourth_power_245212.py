"""Replay the exclusion of odd squares with at most four distinct prime factors.

The mod-two argument reduces squares to fourth powers. The prime envelope leaves
three three-prime supports and the four-prime boxes enumerated below. Arbitrary
multiples of four are included using the proved mathematical height estimate.
An exceeded work limit is reported as an unfinished case, never a certificate.
"""
from argparse import ArgumentParser
from collections import Counter
from fractions import Fraction as F
from math import prod

from odd_four_245212 import cover, factors, moment, prime, val
from rounding_245212 import exponent_ceiling, rounded


def three(q,stride=4):
    bases=(3,5,q)
    counter=Counter()
    def visit(box):
        counter["nodes"]+=1
        if rounded(bases,box):
            return
        bounds=[factors((b,(p,p))) for p,b in zip(bases,box)]
        xl,xh,yl,yh=zip(*bounds)
        if prod(xh)+prod(yh)<2 or prod(xl)+prod(yl)>2:
            return
        varying=[i for i,(l,h) in enumerate(box) if l<h]
        if len(varying)<=1:
            i=varying[0] if varying else 0
            T,A,S=map(prod,zip(*(moment(p,l) for j,(p,(l,h)) in enumerate(zip(bases,box)) if i!=j)))
            p=bases[i]
            difference=A-(p-1)*S
            if not difference:
                assert p*S!=2*T
                return
            l,h=box[i]
            for e in range(l,min(h,val(p,difference))+1,stride):
                t,w,s=moment(p,e)
                if A*w+S*s==2*T*t:
                    raise ValueError("solution",bases,box,i,e)
            return
        i=max(varying,key=lambda j:(xh[j]-xl[j])*prod(xh[:j]+xh[j+1:])+
                                   (yh[j]-yl[j])*prod(yh[:j]+yh[j+1:]))
        l,h=box[i]
        m=max(l,min(h-stride,2*(l+1)*(h+1)//(l+h+2)-1))
        m-=m%stride
        visit(box[:i]+((l,m),)+box[i+1:])
        visit(box[:i]+((m+stride,h),)+box[i+1:])
    h=exponent_ceiling(3,q)
    visit(((stride,h-h%stride),)*3)
    return counter["nodes"]


def four_supports():
    for p in (5,7):
        for q in range(p+1,32):
            if not prime(q):
                continue
            v=F(3,2)*F(p,p-1)*F(q,q-1)
            R=10**18-1 if v>=2 else min(10**18-1,(2/(2-v)).__floor__())
            if R>q:
                yield p,q,R


def audit(budget,unrestricted=False):
    assert F(5,4)*F(7,6)*F(11,10)*F(13,12)<2
    assert F(3,2)*F(5,4)<2 and F(3,2)*F(7,6)*F(11,10)<2
    assert F(3,2)*F(5,4)*F(17,16)<2
    # Verify the worst rank-four score when the exponent of three is one.
    one=F(7,6)*prod(F(p,p-1) for p in (5,7,11))+F(2,3)*prod(F(p+1,2*p) for p in (5,7,11))
    assert one==F(221339,110880)<2
    if unrestricted:
        print("Ranks 1 and 2 excluded by cap; rank four with first exponent 1:",one,"< 2",flush=True)
    for q in (7,11,13):
        print((3,5,q),three(q,1 if unrestricted else 4),"nodes",flush=True)
    for p,q,R in four_supports():
        result=cover(p,q,q+1,R,budget,1 if unrestricted else 4)
        if result[0]!="certified":
            raise RuntimeError((3,p,q),result)
        print((3,p,q,"r"),f"r≤{R}",result[1]["nodes"],"nodes",flush=True)


if __name__=="__main__":
    parser=ArgumentParser(description=__doc__)
    parser.add_argument("--budget",type=int,default=2000000)
    parser.add_argument("--unrestricted",action="store_true",help="Test the four-prime k≥2 branch without assuming a square.")
    args=parser.parse_args()
    audit(args.budget,args.unrestricted)
