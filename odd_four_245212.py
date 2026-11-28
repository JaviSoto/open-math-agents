"""Cover all four-prime odd A245212 candidates by exact rational interval comparisons.

The prime bases are 3,p,q,r in increasing order. The last prime r and
all exponents are unrestricted unless upper bounds follow from the totient
hypothesis or are given on the command line. A run reaching its node budget
is inconclusive. This program does not use floating point.
"""
from argparse import ArgumentParser
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import isqrt, prod
from time import monotonic
from odd_modular_245212 import impossible, tighten, variable_base_impossible
from rounding_245212 import exponent_ceiling, rounded_ranges, singleton_caps


@lru_cache(50000)
def y(p,e):
    if e is None:
        return F(0),F(0)
    if p is None:
        return F(1,e+1),F(1,e+1)
    v=F(p,(p-1)*(e+1))
    if e<32:
        u=v*(1-F(1,p**(e+1)))
        return u,u
    return v*(1-F(1,p**32)),v


@lru_cache(20000)
def prime(p):
    return p>=2 and all(p%d for d in range(2,isqrt(p)+1))


@lru_cache(50000)
def known_composite(r):
    if r<1000000:
        return not prime(r)
    # A failed Fermat congruence is itself an exact compositeness witness.
    return any(r%a==0 or pow(a,r-1,r)!=1 for a in (2,3,5,7))


def factors(bounds):
    exp,base=bounds
    e,E=exp;p,P=base
    lo=y(P,E)[0]; hi=y(p,e)[1]
    xl=1+(1-hi)/(P-1) if P is not None else F(1)
    return xl,1+(1-lo)/(p-1),lo,hi


@lru_cache(256)
def moment(p,e):
    power=p**e
    t=(e+1)*power
    s=(power*p-1)//(p-1)
    return t,(p*t-s)//(p-1),s


def val(p,n):
    k=0
    while n%p==0:
        k+=1;n//=p
    return k


@lru_cache(20000)
def eligible_ends(r,R):
    surviving=[s for s in range(r,R+1) if prime(s)]
    return (surviving[0],surviving[-1]) if surviving else None


def exact_prefix(bases,exps,rr,ds,stride):
    """Eliminate r and d together using the top base-r digit and r-adic divisibility."""
    T,A,S=map(prod,zip(*(moment(p,e) for p,e in zip(bases,exps))))
    r,R=rr
    lo,hi=ds
    # Cut the d range again, now with the exact A/T,S/T of this prefix.
    # These are the same leading-digit inequalities as digit_tighten.
    for upper,u in ((True,R),(False,r-1)):
        v=(u+1)*A-2*u*T
        w=A-(u+1)*S
        if upper:
            if v>0: hi=min(hi,w//v-1)
            if v<0: lo=max(lo,-((-w)//v)-1)
            if v==0 and w<0: return True
        else:
            if v>0: lo=max(lo,w//v)
            if v<0: hi=min(hi,-((-w)//v)-2)
            if v==0 and w>=0: return True
    lo+=(-lo)%stride
    # A-(r-1)S cannot vanish at a nontrivial prime extension by no_resonance.
    # Thus r^d divides a nonzero integer whose absolute value is at most A+R*S.
    hi=min(hi,(A+R*S).bit_length()//(r.bit_length()-1))
    for d in range(lo,hi+1,stride):
        den=(d+1)*(2*T-A)-S
        if den<=0:
            continue
        q,rem=divmod(d*A+S,den)
        if (d==1)!=(rem==0):
            continue
        if rem:
            q+=1
        if not r<=q<=R or (A+S)%q:
            continue
        t,w,s=moment(q,d)
        if A*w+S*s==2*T*t:
            return False
    return True


def digit_tighten(bs,exps,xl,xh,yl,yh,stride):
    """Apply both top-digit inequalities to every prime, without fixing its cofactor."""
    work=[]
    for i,(p,P) in enumerate(bs):
        X=prod(xl[:i]+xl[i+1:]); U=prod(xh[:i]+xh[i+1:])
        Y=prod(yl[:i]+yl[i+1:]); V=prod(yh[:i]+yh[i+1:])
        if X>=2:
            return None
        l,h=exps[i]
        l=max(l+1,(Y/(2-X)).__floor__()+1)
        h+=1
        # t = e+1. Upper digit: t*((P+1)*X-2P) ≤ X-(P+1)*Y.
        v=(P+1)*X-2*P
        w=X-(P+1)*Y
        if v>0:
            h=min(h,(w/v).__floor__())
        elif v<0:
            l=max(l,(w/v).__ceil__())
        elif w<0:
            return None
        # Lower digit: t*(p*U-2*(p-1)) > U-p*V.
        v=p*U-2*(p-1)
        w=U-p*V
        if v>0:
            l=max(l,(w/v).__floor__()+1)
        elif v<0:
            h=min(h,(w/v).__ceil__()-1)
        elif w>=0:
            return None
        l-=1;h-=1
        l+=(-l)%stride;h-=h%stride
        if h<l:
            return None
        work.append((l,h))
    return tuple(work)


def prime_window(rr,ds,xl,xh,yl,yh):
    """The final prime is the ceiling of a fractional linear function of its exponent."""
    lo,hi=rr
    for lower,X,Y in ((True,prod(xl[:3]),prod(yl[:3])),(False,prod(xh[:3]),prod(yh[:3]))):
        d,D=ds
        w=(d+1)*(2-X)-Y
        z=(D+1)*(2-X)-Y
        if lower and max(w,z)<=0:
            return None
        if min(w,z)<=0:
            continue
        # Positive denominators throughout: the extrema in d are at the two ends,
        # and the quotient increases with either of X and Y.
        ends=((d*X+Y)/w,(D*X+Y)/z)
        if lower:
            lo=max(lo,min(ends).__ceil__())
        else:
            hi=min(hi,max(ends).__ceil__())
    return (lo,hi) if lo<=hi else None


def cover(p,q,rlo,rhi,budget,stride=1,least=(2,None)):
    c=Counter()
    biggest=[0]*5
    clock=monotonic()
    def rec(box):
        c["nodes"]+=1
        if c["nodes"]>budget:
            raise TimeoutError(box)
        a,b,g,d,rr=box
        r,R=rr
        if R is not None and R<=1000000 and R-r<=128:
            ends=eligible_ends(r,R)
            if ends is None:
                c["no-primes"]+=1;return
            if ends!=rr:
                c["prime-endpoints"]+=1
                rec(box[:4]+(ends,));return
        bs=((3,3),(p,p),(q,q),rr)
        if R is not None:
            tightened=singleton_caps(bs,box[:4],stride)
            if tightened is None:
                c["singleton-cap"]+=1;return
            box=tightened+(rr,)
            a,b,g,d=box[:4]
        if R is not None and rounded_ranges(bs,box[:4]):
            c["integer-rounding"]+=1;return
        f=[factors(z) for z in zip((a,b,g,d),bs)]
        xl,xh,yl,yh=zip(*f)
        if prod(xh)+prod(yh)<2 or prod(xl)+prod(yl)>2:
            c["interval"]+=1;return
        if R is not None:
            cut=digit_tighten(bs,box[:4],xl,xh,yl,yh,stride)
            if cut is None:
                c["top-digits"]+=1;return
            box=cut+(rr,)
            a,b,g,d=cut
            if stride==1:
                pr=prime_window(rr,d,xl,xh,yl,yh)
                if pr is None:
                    c["prime-window"]+=1;return
                if pr!=rr:
                    r,R=rr=pr
                    bs=((3,3),(p,p),(q,q),rr)
                    box=cut+(rr,)
                    c["tightened-prime"]+=1
        if stride==1 and R is not None and variable_base_impossible((3,p,q),box[:4],rr):
            c["base-lift"]+=1;return
        if r==R and known_composite(r):
            c["composite"]+=1;return
        if R is not None and all(l==h for l,h in (a,b,g)) and max(a[0],b[0],g[0])<4096:
            if exact_prefix((3,p,q),(a[0],b[0],g[0]),rr,d,stride):
                c["recovered-prime"]+=1;return
        if stride==1 and R is not None and max(b[1] for b in (a,b,g))<5000:
            if prod(h-l+1 for l,h in (a,b,g))<=100:
                if all(exact_prefix((3,p,q),ex,rr,d,1) for ex in product(
                        *(range(l,h+1) for l,h in (a,b,g)))):
                    c["prefix-block"]+=1;return
        if r==R and impossible((3,p,q,r),box[:4],stride):
            c["residue-box"]+=1;return
        if r==R:
            reduced=tighten((3,p,q,r),box[:4],stride)
            if reduced is None:
                c["lifted"]+=1;return
            if stride>1:
                reduced=tuple((l+(-l)%stride,None if h is None else h-h%stride) for l,h in reduced)
                if any(h is not None and h<l for l,h in reduced):
                    c["residue-stride"]+=1;return
            if reduced!=box[:4]:
                c["jump"]+=1
                rec(reduced+(rr,));return
        # Once three of the other coordinates are fixed, the entire last
        # exponent can be handled by a congruence and the valuation of a
        # nonzero integer; a single successful root would be a true equality.
        var=[i for i,(l,h) in enumerate(box[:4]) if l!=h]
        if r==R and len(var)<=1:
            k=var[0] if var else 0
            terms=[moment(bs[i][0],box[i][0]) for i in range(4) if i!=k]
            t,w,s=map(prod,zip(*terms))
            base=bs[k][0]
            rem=w-(base-1)*s
            if not rem:
                assert base*s!=2*t,(box,t,w,s)
            else:
                lo,hi=box[k];maxe=val(base,rem)
                for e in range(lo,min(maxe,hi if hi is not None else maxe)+1,stride):
                    u,v,z=moment(base,e)
                    assert w*v+s*z!=2*t*u,("equality",box,k,e)
            c["valuation"]+=1;return
        # W(other)+sigma(other) must be divisible by the last prime. In a
        # bounded interval this is useful even before specializing d.
        if all(l==h for l,h in (a,b,g)) and max(a[0],b[0],g[0])<4096:
            terms=[moment(t,u[0]) for t,u in ((3,a),(p,b),(q,g))]
            _,w,s=map(prod,zip(*terms))
            if R is not None and R-r<=1024 and not any((w+s)%v==0 and prime(v) for v in range(r,R+1)):
                c["modular"]+=1;return
        variants=[]
        for k,(lo,hi) in enumerate(box):
            if lo==hi:continue
            if k<4:
                pp=bs[k][0]
                dy=y(pp,lo)[1]-y(pp,hi)[0]
                dx=dy/(pp-1)
                xx=prod(xh[i] for i in range(4) if i!=k)
                yy=prod(yh[i] for i in range(4) if i!=k)
                variation=xx*dx+yy*dy
            else:
                dl=y(r,d[0])[1]-y(R,d[0])[0]
                dr=F(1,r-1)-(F(1,R-1) if R is not None else 0)
                variation=prod(xh[:3])*dr+prod(yh[:3])*dl
            variants.append((variation,k))
        assert variants,("unresolved singleton",box)
        _,i=max(variants)
        l,h=box[i]
        m=2*l+1 if h is None else max(l,min(h-1,2*(l+1)*(h+1)//(l+h+2)-1))
        step=stride if i<4 else 1
        m-=m%step
        biggest[i]=max(biggest[i],m+step)
        rec(box[:i]+((l,m),)+box[i+1:])
        rec(box[:i]+((m+step,h),)+box[i+1:])
    cap=None if rhi is None else exponent_ceiling(4,rhi)
    if cap is not None:
        cap-=cap%stride
    lo=max(least[0],2,stride);lo+=(-lo)%stride
    hi=cap if least[1] is None else min(cap,least[1])
    if hi is not None:
        hi-=hi%stride
    if hi is not None and hi<lo:
        return "certified",c,biggest,0
    box=((lo,hi),(stride,cap),(stride,cap),(stride,cap),(rlo,rhi))
    try:
        rec(box)
    except TimeoutError as ex:
        return "unfinished",str(ex),c,biggest,monotonic()-clock
    return "certified",c,biggest,monotonic()-clock


if __name__=="__main__":
    ap=ArgumentParser(description=__doc__)
    ap.add_argument("p",type=int);ap.add_argument("q",type=int)
    ap.add_argument("--r",type=int);ap.add_argument("--budget",type=int,default=50000)
    ap.add_argument("--stride",type=int,default=1,help="positive common divisor of all four exponents")
    ap.add_argument("--least-exp-min",type=int,default=2)
    ap.add_argument("--least-exp-max",type=int)
    args=ap.parse_args()
    assert args.p>3 and args.q>args.p and prime(args.p) and prime(args.q)
    cap=F(3,2)*F(args.p,args.p-1)*F(args.q,args.q-1)
    last=10**18-1 if cap>=2 else min(10**18-1,(2/(2-cap)).__ceil__()-1)
    if args.r is not None:
        assert args.r>args.q and prime(args.r)
        low=last=args.r
    else:
        low=args.q+1
    assert args.stride>=1
    print(cover(args.p,args.q,low,last,args.budget,args.stride,
                (args.least_exp_min,args.least_exp_max)),flush=True)
