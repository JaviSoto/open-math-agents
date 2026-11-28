"""Certified integer enclosures for the remaining two-odd-prime exponent boxes.

Here p<q, K=k+1, B and C are the exponents of p and q plus one.
Each True exit is a strict contradiction of a positive integer bound.
Unresolved boxes remain explicit; no floating-point inequalities are used.
"""
from argparse import ArgumentParser
from collections import Counter


def ceiling_log(n):
    """An integer e such that n <= 2^e for positive n."""
    return (n-1).bit_length()


def ceiling_div(n, d):
    return -(-n//d)


def obstruction(k0,k1,b0,b1,c0,c1,prime_min=13,prime_max=None):
    """All parameters range over the closed intervals, including endpoints."""
    if k0 < 6 or min(b0,c0) < 4:
        raise ValueError("The positive-alpha proof requires K>=6 and exponents at least three")
    # Strict reciprocal inequality at the smaller prime.
    low=max(prime_min,(k0-1)*(b0-1)//b0+1)
    # Local weighted factors <= 1+1/(p-1), and 1-s_p*s_q/(BC)
    # >= 1-(11/10)^2/16. In particular p<=3K and C*(K-1)-u>0.
    high=3*k1 if prime_max is None else min(prime_max,3*k1)
    if low>high:
        return "least prime"
    l=low.bit_length()-1
    pbits=(b0-1)*l
    qbits=(c0-1)*l
    # All log bounds are outward-rounded integer exponents of powers of two.
    # q^(C-2) <= 3*2^K*K*B*P from the prime-power cofactor inequality.
    cofactor=k1+ceiling_log(3*k1*b1)
    qlog=ceiling_div(cofactor+(b1-1)*ceiling_log(high),c0-2)
    q2_over_p=ceiling_div(2*cofactor-(c0-4)*pbits,c0-2)
    # L(γ)=u²D+(Cγ-u)/P is strictly positive and has denominator
    # dividing G. Thus P>=2GCK gives D>=1/(2Gu²), even at small K
    # where replacing γ by k would lose the integer separation.
    if pbits >= k1+ceiling_log(2*c1*k1):
        limit=k1+ceiling_log(6*c1*b1*k1*high**2)
        qlog=min(qlog,limit)
        q2_over_p=min(q2_over_p,2*limit-pbits)
    # Positive L-u²D is at most CKB*u/G + CK/P. If at most 1/2,
    # q <= 6CBKu²; this estimate is independent of C's size in the denominator.
    if ceiling_log(c1*k1*b1*high)-(k0-1)<=-2 and ceiling_log(c1*k1)-pbits<=-2:
        y=6*c1*b1*k1*high**2
        qlog=min(qlog,ceiling_log(y))
        q2_over_p=min(q2_over_p,ceiling_log(y*y)-pbits)
    hlog=ceiling_log(high)
    if (c0-2)*l > cofactor+(b1-1)*hlog:
        return "largest prime power"
    if (c0-b1-1)*l > cofactor:
        return "ordered prime powers"
    if (b0-2)*l > k1+ceiling_log(3*k1*c1)+(c1-1)*qlog:
        return "smaller prime power"
    # For a>=2d+4, the integral resonance A=kH is impossible. Apply in
    # either orientation. H<=2hb*x²*y^d, |C|<=2h(K+x)y^d and
    # 2^K/P<3hb*y^d; bound the terms of 2^K<=1+K*H+(2^K/P)*|C|.
    for large,outer,inner,xlog,ylog in ((b0,b1,c1,hlog,qlog),(c0,c1,b1,qlog,hlog)):
        if large>=2*inner+3:
            d=inner-1
            first=ceiling_log(2*inner*outer*k1)+2*xlog+d*ylog
            second=ceiling_log(6*inner*inner*outer)+max(ceiling_log(k1),xlog)+1+2*d*ylog
            if max(first,second)+2<k0:
                return "complementary integer"
    # 2^K divides the positive W(P)W(Q)-sigma(P)sigma(Q).
    # W(P)W(Q) <= (11/10)^2 BC P Q < 2 BC P Q.
    if k0>ceiling_log(2*b1*c1)+(b1-1)*ceiling_log(high)+(c1-1)*qlog:
        return "dyadic divisor"
    x=ceiling_log(k1*c1+high)+q2_over_p
    y=ceiling_log(high*high*(k1*b1+low))-qbits
    z=ceiling_log(k1+high*low)-pbits-qbits
    if max(x,y,z)+k1<=-2:
        return "exact dyadic"
    drift=ceiling_log(9*k1*high*high*b1*c1)-2+2*qlog-(k0-1)
    if max(x,y,z,drift)<=-3:
        return "integer dyadic"
    return None


def blocks(first, last):
    """Factor-of-two blocks include every integer exactly once."""
    while first<=last:
        end=min(last,2*first-1)
        yield first,end
        first=end+1


def reduce(m, cutoff, precision=32):
    counts=Counter()
    pending=[]
    def visit(k0,k1,m0,m1,swapped):
        # Uniform complementary-exponent theorem, using the larger exponent.
        m1=min(m1,64*m*m*k1,32768*m**6)
        if m1<m0:
            return
        b0,b1,c0,c1=(m,m,m0,m1) if swapped else (m0,m1,m,m)
        reason=obstruction(k0,k1,b0,b1,c0,c1)
        if reason:
            counts[reason]+=1
            return
        wk=k1-k0
        wm=m1-m0
        if wk<=max(1,k0//precision) and wm<=max(1,m0//precision):
            pending.append((k0,k1,m0,m1,swapped))
            return
        if wk and (not wm or wk*m0>=wm*k0):
            half=(k0+k1)//2
            visit(k0,half,m0,m1,swapped)
            visit(half+1,k1,m0,m1,swapped)
        else:
            half=(m0+m1)//2
            visit(k0,k1,m0,half,swapped)
            visit(k0,k1,half+1,m1,swapped)
    for k0,k1 in blocks(6,min(cutoff,512*m**4)):
        for m0,m1 in blocks(m,min(64*m*m*k1,32768*m**6)):
            visit(k0,k1,m0,m1,False)
            # Equal exponents have no second orientation.
            visit(k0,k1,max(m+1,m0),m1,True)
    return counts,pending


if __name__ == "__main__":
    parser=ArgumentParser(description=__doc__)
    parser.add_argument("--minimum",type=int,default=6)
    parser.add_argument("--maximum",type=int,default=32)
    parser.add_argument("--through",type=int,default=512*32**4)
    parser.add_argument("--precision",type=int,default=16)
    args=parser.parse_args()
    for m in range(args.minimum,args.maximum+1):
        counts,pending=reduce(m,args.through,args.precision)
        cells=sum((b-a+1)*(d-c+1) for a,b,c,d,_ in pending)
        print(m,len(pending),cells,max((r[1] for r in pending),default=0),
              max((r[3] for r in pending),default=0),dict(counts),flush=True)
