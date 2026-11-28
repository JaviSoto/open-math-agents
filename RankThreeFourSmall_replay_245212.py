"""Exact two-free-prime search for n=4*3^e*p^b*q^d, 5<=p<q.

Run with --exponents 1 2 3 4 5 6 7, or --prime 257 --exponents 7 for
the near-pole comparison. --literal disables the first-order digit filter.
Arithmetic uses Python integers only. Any putative solution interrupts the
run with its four parameters. The search never relies on probable primality.
"""
from argparse import ArgumentParser
from collections import Counter
from time import perf_counter
from RankThreeFourSmall_profile_245212 import bounds, ilog, prime
from rank_three_middle_blocks_245212 import moments


def check_solution(A,S,H,p,b,q,d):
    w,s,t=moments(p,b); v,z,u=moments(q,d)
    if A*w*v+S*s*z==H*t*u:
        raise ArithmeticError(f"exact equality at cofactor {(A,S,H)}, p,b,q,d={(p,b,q,d)}")


def known(A,S,H,p,b,q,stats):
    """One exponent fixed, reverse digit gives at most one other exponent."""
    w,s,t=moments(p,b); V,Y,J=A*w,S*s,H*t
    if (V+Y)%q:return
    D=(q-1)*(J*(q-1)-q*V)
    if D==0:return
    d=q*((q-1)*Y-V)//D-1
    if d<1 or d>(V+q*Y).bit_length():return
    check_solution(A,S,H,p,b,q,d)
    stats["known exact checks"]+=1


def mod_possible(A,S,p,b,q,d):
    """p^b divides W(h*q^d) - (p-1)*sigma(h*q^d); clear (q-1)^2."""
    mod=p**min(4,b); v=q-1; power=pow(q,d,mod)
    test=A*(q*((d+1)*v-1)*power+1)-(p-1)*S*v*(q*power-1)
    return test%mod==0


def moving(A,S,H,p,b,R,L,literal,stats):
    """R<=q, 1<=d<=L. Test leading digit q=ceil(N/D) exactly or bound it first."""
    u=p-1; B=b+1
    base=u*B*(H*u-A*p)
    def exact(d):
        w,s,t=moments(p,b); V,Y,J=A*w,S*s,H*t
        z=(d+1)*(J-V)-Y
        if z<=0:return
        q=(d*V+Y-1)//z+1
        if q>=R and (V+Y)%q==0:
            check_solution(A,S,H,p,b,q,d)
            stats["moving exact checks"]+=1
    for d in range(1,L+1):
        if literal:
            exact(d)
            continue
        C=d+1
        D0=C*base+p*(C*A-S*u)
        D1=S*u-C*A
        N0=p*(d*A*(B*u-1)+S*u)
        N1=d*A-S*u
        # u^2 D = D0*p^b+D1 and u^2 N=N0*p^b+N1.
        # If D0 is negative and p^b>|D1|, D is negative.
        low_power=1<<min(200,b)
        if D0<0 and low_power>abs(D1):continue
        # |N/D-N0/D0|=|N1*D0-N0*D1|/(D0*(D0*p^b+D1)).
        # Our integer bound makes this <1 without constructing p^b.
        if D0>0 and low_power>abs(D1)+abs(N1*D0-N0*D1):
            floor=N0//D0
            if not any(q>=R and mod_possible(A,S,p,b,q,d) for q in range(floor,floor+3)):continue
        exact(d)


def exact_band(A,S,H,p,d,R,BB):
    """Return b intervals validated by the sign of both affine coefficients."""
    u=p-1; C=d+1; G=H*u-A*p
    ds=C*u*G
    dc=p*(C*A-S*u)
    tailD=S*u-C*A
    ns=p*d*A*u
    nc=p*(S*u-d*A)
    tailF=d*A-S*u-(R-1)*tailD
    J=ilog(p,max(abs(tailD),abs(tailF)))+1
    margin=(R-1)*ds-ns
    if ds<=0 or margin<=0:raise ArithmeticError("nonincreasing affine cut")
    # D0=(b+1)*ds+dc >= 0; N0-(R-1)D0 >= 0.
    lo=max(J,(-dc+ds-1)//ds-1)
    hi=min(BB,(nc-(R-1)*dc)//margin-1)
    return range(1,min(J-1,BB)+1),range(lo,hi+1)


def run(e,only_p=None,literal=False,band_literal=False):
    h=4*3**e;w,s,t=moments(3,e)
    return run_cofactor(h,17*w,7*s,24*t,only_p,literal,band_literal,label=e)


def run_cofactor(h,A,S,H,only_p=None,literal=False,band_literal=False,*,first=5,label=None):
    """Enumerate p<q odd primes, p>=first, coprime to h; H=2hτ(h), A=W(h), S=σ(h)."""
    from math import gcd
    if not (0<A<H and h>0 and S>0 and first>=3 and first%2):
        raise ValueError("require h,S positive, 0<A<H, and first an odd integer >=3")
    then=perf_counter();stats=Counter()
    gap=H-A;L=max(4,S//gap+1);P=2*H*L//(gap*L-S)
    for p in range(first,P+1,2):
        if only_p and only_p!=p:continue
        if not prime(p) or gcd(h,p)!=1:continue
        stats["first primes"]+=1
        u=p-1; G=H*u-A*p
        if G==0:raise ArithmeticError(f"unresolved first Euler pole at h={h}, p={p}")
        if G<0:
            B=2*A//(-G)
            for b in range(1,B+1):
                w,s,t=moments(p,b);V,Y,J=A*w,S*s,H*t
                # PairExtension245212.lowerBase_le + last_log_base.
                R=max(2,p+1,V//(2*(J-V)) if J>V else 0)
                D=ilog(R,V+Y)+1
                moving(A,S,H,p,b,R,D,literal,stats)
                stats["above-pole prefixes"]+=1
            continue
        Q=1+2*A*p//G
        for q in range(p+2,Q+1,2):
            if not prime(q) or gcd(h,q)!=1:continue
            E=bounds(h,A,S,H,p,q)
            # For nonpositive pair excess, E bounds d; otherwise it bounds min(b,d).
            if A*p*q>H*u*(q-1):
                for b in range(1,E+1):known(A,S,H,p,b,q,stats)
            for d in range(1,E+1):known(A,S,H,q,d,p,stats)
            stats["finite prime pairs"]+=1
        BB=4*S*u//G
        R=max(p,Q)+1
        D=2*(A+S*u)//A
        # p*((H-A)*tau-S)<=2H*tau, by the same count-sensitive
        # reciprocal estimate as RankThreeFourSmallHarmonic.first_prime.
        den=p*(H-A)-2*H
        tau=p*S//den if den>0 else None
        if tau is not None:BB=min(BB,tau//2-1)
        if band_literal:
            for d in range(1,D+1):
                width=min(BB,tau//(d+1)-1) if tau is not None else BB
                for band in exact_band(A,S,H,p,d,R,width):
                    for b in band:
                        w,s,t=moments(p,b); V,Y,J=A*w,S*s,H*t
                        den=(d+1)*(J-V)-Y
                        if den>0:
                            q=(d*V+Y-1)//den+1
                            if q>=R and (V+Y)%q==0:
                                check_solution(A,S,H,p,b,q,d)
                                stats["moving exact checks"]+=1
                        stats["band exponent pairs"]+=1
        else:
            for b in range(1,BB+1):
                last=min(D,tau//(b+1)-1) if tau is not None else D
                moving(A,S,H,p,b,R,last,literal,stats)
                stats["far exponent pairs"]+=last
    result=dict(exponent=label,cofactor=h,first_bound=P,elapsed=round(perf_counter()-then,3),**stats)
    print(result,flush=True)
    return result


if __name__=="__main__":
    parser=ArgumentParser(description=__doc__)
    parser.add_argument("--exponents",nargs="+",type=int,choices=range(1,8),default=list(range(1,8)))
    parser.add_argument("--prime",type=int)
    parser.add_argument("--literal",action="store_true")
    parser.add_argument("--band-literal",action="store_true",help="cut affine b intervals, then compute each remaining large power exactly")
    args=parser.parse_args()
    for exponent in args.exponents:run(exponent,args.prime,args.literal or args.band_literal,args.band_literal)
