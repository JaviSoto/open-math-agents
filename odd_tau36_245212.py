"""Exact prime-box search for bounded odd divisor counts in A245212.

Extends the published odd_divisor_count_245212.py.  --plan counts an upper
bound on the terminal integers instead of running the terminal checks.
"""
import argparse
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
from functools import cache
from math import comb, gcd, isqrt, lcm, prod
from time import monotonic

from odd_divisor_count_245212 import (
    first_impossible_k, last_prime, local, ordered_exponents, original_difference,
)


@cache
def small_primes(n):
    bits=bytearray([1])*(n+1)
    bits[:2]=bytes(2)
    for d in range(2,isqrt(n)+1):
        if bits[d]:
            bits[d*d::d]=bytes((n-d*d)//d+1)
    return [p for p in range(3,n+1,2) if bits[p]]


def prime_interval(lo,hi):
    """Segmented sieve including both ends, with a fixed-size marking buffer."""
    lo=max(3,lo)|1
    if hi<lo:
        return
    root=isqrt(hi)
    primes=small_primes(1 << root.bit_length())
    for low in range(lo,hi+1,32768*2):
        end=min(hi,low+65534)
        bits=bytearray([1])*((end-low)//2+1)
        for p in primes:
            if p*p>end: break
            first=max(p*p,((low+p-1)//p)*p)
            if first%2==0: first+=p
            if first<=end:
                bits[(first-low)//2::p]=bytes((end-first)//(2*p)+1)
        yield from (low+2*i for i,b in enumerate(bits) if b)


def first_true(lo,hi,predicate):
    while lo<hi:
        mid=(lo+hi)//2
        if predicate(mid): hi=mid
        else: lo=mid+1
    return lo


def integer_roots(coefs,lo,hi):
    """Isolate all integer roots on the bounded interval using Descartes signs."""
    d=len(coefs)-1
    if not coefs[-1]: raise ArithmeticError("expected nonzero leading coefficient")
    def at(x):
        v=0
        for a in reversed(coefs): v=v*x+a
        return v
    stack=[(lo,hi)]
    while stack:
        l,h=stack.pop()
        if l>h: continue
        if h-l<=2:
            for p in range(l,h+1):
                if not at(p): yield p
            continue
        # Coefficients of (1+z)^d f(l+(h-l)z/(1+z)).
        shifted=[sum(coefs[j]*comb(j,i)*l**(j-i) for j in range(i,d+1))*(h-l)**i
                 for i in range(d+1)]
        signs=[sum(shifted[i]*comb(d-i,j-i) for i in range(j+1)) for j in range(d+1)]
        if min(signs)>=0 or max(signs)<=0:
            if signs[0]==0: yield l
            if signs[-1]==0: yield h
            continue
        mid=(l+h)//2
        stack.extend(((l,mid),(mid+1,h)))


def surplus_polynomials(A,S,J,Q,H,e):
    """Return L,R so a true last pair x¹yᵉ satisfies h*L(y)+R(y)=0."""
    weighted=[A*(j+1) for j in range(e+1)]
    L=[-Q*S-2*H*w for w in weighted]
    L[e]+=(Q+H)*J
    R=[0]*(2*e+1)
    for j,w in enumerate(weighted):
        R[e+j]+=J*(S-w)
        for z in range(e+1): R[z+j]-=w*S
    return L,R


def solve(t,k,exps,plan=False,window=None,audit=False,odd_residue=None,terminal_primes=None):
    c=Counter()
    power=1<<k
    gh=2*power-1
    gl=k*gh+k+1
    target=(gl+gh)*t
    tails=[prod(e+1 for e in exps[i:]) for i in range(len(exps)+1)]
    triangles=[prod((e+1)*(e+2)//2 for e in exps[i:]) for i in range(len(exps)+1)]
    rank=len(exps)
    saturated=prod(e+2 for e in exps)%(2<<rank)!=0
    # Optional stronger congruence from the exact exponent-order theorem,
    # supplied by other callers only when proved for this complete profile.
    odd_modulus,odd_remainder = odd_residue or ((4,1) if saturated else (1,0))
    g0=gcd(k+1,gh)
    Q=gh//g0
    H=k*Q+(k+1)//g0

    def append(prefix,x,e):
        m,a,s=prefix
        z,w,h=local(x,e)
        return m*z,a*w,s*h

    def deficit(prefix,i):
        m,a,s=prefix
        return target*m-gl*a*tails[i]-gh*s

    def threshold(prefix,i,base):
        # max next prime: put every remaining unknown at x for an upper bound.
        if deficit(prefix,i)<=0:
            return None  # no finite lower-limit gap
        def below(x):
            value=prefix
            for e in exps[i:]:
                value=append(value,x,e)
            return deficit(value,rank)>0
        hi=base
        while not below(hi):
            hi*=2
        return first_true(base,hi,below)-1

    def dyadic_box(prefix,i,lo,hi):
        """True if every prospective W(m) is at most 2^(k+1)."""
        if k<6:
            return False
        upper=append(prefix,hi,exps[i])
        j=i+1
        if j<rank:
            # Monotonicity allows a sharper cap for one following prime at lo.
            lower=append(prefix,lo,exps[i])
            # For the final prime the leading digit itself gives the bound
            # without a binary search or trial primality of the endpoint.
            M,A,S=lower
            if j==rank-1 and (d:=deficit(lower,j))>0:
                e=exps[j]
                cap=(e*gl*A+gh*S+d-1)//d
            else:
                cap=threshold(lower,j,lo+1)
            if cap is not None:
                if cap<=lo: return True
                upper=append(upper,cap,exps[j])
                j+=1
        for h in range(j,rank):
            M,A,S=upper
            # At a true prefix 0<Dγ≤Dk, where Dk is an integer. Bounding
            # Dk−Dγ by 1/2 gives Dγ≥1/2 uniformly on this box.
            if 2*(k+1)*A*tails[h]>gh:
                return False
            cap=2*((k+1)*A*(triangles[h]-tails[h])+S*(tails[h]-1))
            upper=append(upper,cap,exps[h])
        # 2^(k+1) | W(m)−σ(m), which is positive and strictly below W(m).
        return upper[1]<=2*power

    def descend(prefix,i,prev,bases):
        m,a,s=prefix
        common=gcd((1+2*k*power)*a,gh*s)
        forced=common//gcd(common,2*power*(k+1)*t*m)
        if forced>1 and (forced<=prev or gcd(forced,m)>1):
            c["forced"]+=1
            return
        if i==rank-1:
            c["last"]+=1
            if plan: return
            m,a,s=prefix; e=exps[i]
            T=(k+1)*power*m*(t//(e+1)); A=(1+2*k*power)*a; S=gh*s
            p=last_prime(e,T,A,S)
            if p<=prev or (e%2 and p%odd_modulus!=odd_remainder): return
            if (A+S)%p: return
            c["divisible"]+=1
            z,w,h=local(p,e)
            difference=2*T*z*(e+1)-A*w-S*h
            if audit:
                # Even if the final p is composite, this is the same finite
                # expansion as a formal product. No primality oracle is used.
                independent=original_difference(k,zip((*bases,p),exps))
                if independent!=difference:
                    raise ArithmeticError(f"direct sums disagree: {k=}, {bases=}, {p=}")
                c["divisor_audits"]+=1
            if not difference:
                raise ArithmeticError(f"integer candidate: k={k}, prefix={m}, p={p}, e={e}")
            return
        hi=threshold(prefix,i,prev+1)
        if hi is None or hi<=prev: return
        if forced>1: hi=min(hi,forced)
        # Even with all later bases at infinity the target must be exceeded
        # by the target-minus-score difference. A zero endpoint is impossible.
        def low_ok(x):
            return deficit(append(prefix,x,exps[i]),i+1)>0
        if not low_ok(hi): return
        lo=first_true(prev+1,hi,low_ok)
        boxes=[(lo,hi)]
        intervals=[]
        pair=i==rank-2 and 1 in exps[i:]
        if pair:
            e1,e2=exps[i:]
            e=e2 if e1==1 else e1
            # For a linear prime x and another y^e, eliminate x from
            # hQ=W(m)-tm and hH=tm-σ(m). The resulting polynomial is hL+R.
            tu=t*m
            L,R=surplus_polynomials(a,s,tu,Q,H,e)
            g1=gcd(a,tu);g2=gcd(s,tu)
            stride=lcm(g1//gcd(g1,Q),g2//gcd(g2,H))
            residues=None
            def h_masks():
                allowed=[]
                for modulus in (3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71):
                    ok=set()
                    for y in range(modulus):
                        v=stride*sum(a*pow(y,j,modulus) for j,a in enumerate(L))%modulus
                        w=sum(a*pow(y,j,modulus) for j,a in enumerate(R))%modulus
                        if v:
                            ok.add((-w*pow(v,-1,modulus))%modulus)
                        elif not w:
                            ok=set(range(modulus)); break
                    bad=set(range(modulus))-ok
                    if bad: allowed.append((modulus,bad))
                return allowed
        while boxes:
            low,high=boxes.pop()
            if dyadic_box(prefix,i,low,high):
                c["dyadic"]+=1
                continue
            # If even the smallest possible tail makes W(m)>2^(k+1),
            # subdivision cannot possibly establish this upper-bound veto.
            smallest=prefix[1]*prod(local(low,e)[1] for e in exps[i:])
            if i==rank-2:
                hpre=append(prefix,high,exps[i])
                d=deficit(hpre,i+1)
                if d>0:
                    B=exps[-1]*gl*hpre[1]+gh*hpre[2]
                    bottom=max(low,(B+d-1)//d)
                    smallest=prefix[1]*local(low,exps[i])[1]*local(bottom,exps[-1])[1]
                    if pair:
                        lpre=append(prefix,low,e1)
                        capd=deficit(lpre,i+1)
                        if capd<=0: raise ArithmeticError("ordered lower endpoint")
                        top=(e2*gl*lpre[1]+gh*lpre[2]+capd-1)//capd
                        def surplus(x,y):
                            z,w,_=local(x,e1); zz,ww,_=local(y,e2)
                            return a*w*ww-tu*z*zz
                        hlow=(surplus(low,bottom)+Q*stride-1)//(Q*stride)
                        hhi=surplus(high,top)//(Q*stride)
                        nh=max(0,hhi-hlow+1)
                        if not nh:
                            c["surplus_empty"]+=1
                            continue
                        if nh<=min(250000, (high-low)//250):
                            c["surplus_h"]+=nh
                            if not plan:
                                yl,yh=(bottom,top) if e1==1 else (low,high)
                                ok=bytearray([1])*nh
                                if nh>=128 and residues is None: residues=h_masks()
                                for modulus,bad in residues or ():
                                    for rem in bad:
                                        first=(rem-hlow)%modulus
                                        if first<nh:
                                            ok[first::modulus]=bytes((nh-1-first)//modulus+1)
                                for offset,passing in enumerate(ok):
                                    if not passing: continue
                                    c["root_tests"]+=1
                                    n=hlow+offset
                                    h=n*stride
                                    coefs=R.copy()
                                    for j,v in enumerate(L): coefs[j]+=h*v
                                    for y in integer_roots(coefs,yl,yh):
                                        Y,wy,sy=local(y,e)
                                        dx=tu*Y-s*sy
                                        if dx<=0: continue
                                        x,rem=divmod(h*H+s*sy,dx)
                                        if rem or x<2: continue
                                        x0,y0=(x,y) if e1==1 else (y,x)
                                        if low<=x0<=high and y0>x0:
                                            raise ArithmeticError(f"integer pair: k={k}, prefix={m}, {x=}, {y=}")
                            continue
                        near_end=surplus(high,bottom)//(Q*stride)
                        if k>=30 and high-low>100000 and near_end<(high-low)*16:
                            mid=(low+high)//2
                            boxes.extend(((mid+1,high),(low,mid)))
                            continue
            if high-low>=512 and k>=18 and smallest<=2*power:
                mid=(low+high)//2
                boxes.extend(((mid+1,high),(low,mid)))
                continue
            if plan and i==rank-2:
                c["terminal_span"]+=high-low+1
                c["max_terminal"]=max(high,c["max_terminal"])
                if window is not None:
                    if intervals and intervals[-1][1]+1==low:
                        intervals[-1]=(intervals[-1][0],high)
                    else:
                        intervals.append((low,high))
                continue
            candidates=(terminal_primes(prefix,exps[i:],low,high)
                        if terminal_primes is not None and i==rank-2 else prime_interval(low,high))
            for p in candidates:
                if exps[i]%2 and p%odd_modulus!=odd_remainder: continue
                descend(append(prefix,p,exps[i]),i+1,p,(*bases,p) if audit else ())
        if window is not None:
            for low,high in intervals:
                window(k,t,exps,prefix,low,high,saturated)
    descend((1,1,1),0,2,())
    return c


def patterns(t):
    """Ordered prime exponents after the published parity and square tests."""
    for exps in ordered_exponents(t):
        if len(exps)<2 or prod(e+2 for e in exps)%(1<<len(exps)): continue
        if all(e%2==0 for e in exps) and any(e%4!=0 for e in exps): continue
        yield exps


def run_job(job):
    t,exps,lo,hi,plan,audit,solver=job
    start=monotonic(); result=Counter()
    for k in range(lo,hi+1):
        for key,value in solver(t,k,exps,plan,audit=audit).items():
            if key.startswith("max_"): result[key]=max(result[key],value)
            else: result[key]+=value
    return t,exps,lo,hi,dict(result),round(monotonic()-start,3)


def self_test():
    """Compare the polynomial and sieve with exhaustive integer calculations."""
    from random import Random
    rng=Random(245212)
    for lo,hi in [(3,7),(10,11),(65500,131200),(10**7,10**7+257)]:
        trial=[p for p in range(lo,hi+1)
               if p%2 and all(p%d for d in range(3,isqrt(p)+1,2))]
        if list(prime_interval(lo,hi))!=trial: raise AssertionError("segmented sieve")
    for _ in range(500):
        degree=rng.randrange(1,9)
        poly=[rng.randrange(-100,101) for _ in range(degree)]+[rng.randrange(1,40)]
        forced=rng.randrange(-10,31)
        poly=[-forced*poly[0]]+[u-forced*v for u,v in zip(poly,poly[1:])]+[poly[-1]]
        expected=[x for x in range(-10,31) if sum(c*x**i for i,c in enumerate(poly))==0]
        if sorted(integer_roots(poly,-10,30))!=expected: raise AssertionError("integer roots")
    # Manufacture positive surplus identities rather than expecting a genuine
    # counterexample. Both eliminant and reconstructed x must recover the pair.
    for x in (3,7,11,19):
        for y in (5,13,17):
            for d in range(1,7):
                P,A,S=local(23,2)
                yp,wy,sy=local(y,d)
                J=3*2*(d+1)*P
                Q=A*(1+2*x)*wy-J*x*yp
                H=J*x*yp-S*(1+x)*sy
                h=gcd(Q,H); Q//=h; H//=h
                L,R=surplus_polynomials(A,S,J,Q,H,d)
                f=R.copy()
                for j,v in enumerate(L): f[j]+=h*v
                if y not in integer_roots(f,2,30): raise AssertionError("surplus eliminant")
                if divmod(h*H+S*sy,J*yp-S*sy)!=(x,0): raise AssertionError("recovered prime")
    print("self-test passed: segmented primes; 500 signed integer-root intervals; 72 planted surplus pairs")


def main(solver=solve,default_t=36,self_check=self_test,description=__doc__):
    parser=argparse.ArgumentParser(description=description)
    parser.add_argument("--t",type=int,default=default_t)
    parser.add_argument("--through",type=int,help="include every divisor count from --t to this value")
    parser.add_argument("--jobs",type=int,default=1,help="number of independent pattern workers (default: 1)")
    parser.add_argument("--self-test",action="store_true",help="run deterministic arithmetic regression tests and exit")
    parser.add_argument("--k",nargs=2,type=int,metavar=("LO","HI"))
    parser.add_argument("--exps",nargs="+",type=int)
    parser.add_argument("--plan",action="store_true")
    parser.add_argument("--audit",action="store_true",
                        help="expand all divisors independently for each final divisibility survivor")
    args=parser.parse_args()
    if args.self_test:
        self_check()
        return
    if args.audit and args.plan: parser.error("--plan does not perform equality checks")
    if args.t<2: parser.error("the odd divisor count must be at least 2")
    if args.jobs<1: parser.error("--jobs must be positive")
    through=args.t if args.through is None else args.through
    if through<args.t or (through!=args.t and args.exps):
        parser.error("--through must be at least --t and is incompatible with selecting a single pattern")
    if args.exps and (any(e<1 for e in args.exps) or prod(e+1 for e in args.exps)!=args.t):
        parser.error("bad exponent pattern")
    jobs=[]
    for t in range(args.t,through+1):
        cap=first_impossible_k(t)
        lo,hi=(0,cap-1) if args.k is None else args.k
        if not 0<=lo<=hi<cap: parser.error(f"k must belong to [0,{cap-1}] at t={t}")
        for exps in patterns(t):
            if not args.exps or tuple(args.exps)==exps:
                jobs.append((t,exps,lo,hi,args.plan,args.audit,solver))
    def report(rows):
        totals=Counter()
        for t,exps,lo,hi,counts,elapsed in rows:
            print(t,exps,lo,hi,counts,elapsed,flush=True)
            for name,n in counts.items():
                if name.startswith("max_"): totals[name]=max(totals[name],n)
                else: totals[name]+=n
        print("plan" if args.plan else "complete",len(jobs),"patterns",dict(sorted(totals.items())),flush=True)
    if args.jobs==1 or len(jobs)<2:
        report(map(run_job,jobs))
    else:
        with ProcessPoolExecutor(max_workers=min(len(jobs),args.jobs)) as pool:
            report(pool.map(run_job,jobs))


if __name__=="__main__":
    main()
