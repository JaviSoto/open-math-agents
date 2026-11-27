"""Exhaust prime-power extensions of specified smooth cofactors for OEIS A245212."""
from itertools import combinations
from math import gcd
import argparse
import gmpy2


def extensions(m, t, a, s):
    """Return every prime power coprime to m extending it to a balance.

    t=m*tau(m), a=sum(d*tau(d) for d|m), s=sum(d for d|m).
    For the sole infinite-family case we output exponent None.
    """
    g = a+s
    u = 2*t-a
    if u <= 0:
        return
    if 2*t == g and a % s == 0:
        p = 1 + a//s
        if m%p and gmpy2.is_prime(p):
            yield p, None
    leading = 2*u-s
    if leading > 0:
        p, r = divmod(g, leading)
        if not r and p>1 and m%p and gmpy2.is_prime(p):
            yield p, 1
    # For e>=2 the positive root lies strictly in (B/D, B/D+1).
    # B/D is monotone in e, so skip whole runs of identical candidates.
    last = g.bit_length()
    e = max(2, s//u)
    while e<=last:
        den = (e+1)*u-s
        if den <= 0:
            e += 1
            continue
        p = (e*a+s)//den+1
        if e==last or (last*a+s)//((last+1)*u-s)+1==p:
            end = last
        else:
            lo, hi = e, last
            while hi-lo>1:
                mid=(lo+hi)//2
                if (mid*a+s)//((mid+1)*u-s)+1==p:
                    lo=mid
                else:
                    hi=mid
            end=lo
        if p>1 and g%p==0 and m%p and gmpy2.is_prime(p):
            c = a-s*(p-1)
            slope = (p-1)*(2*t*(p-1)-a*p)
            rest = a*p-s*p*(p-1)
            if c:
                power=p**e
                for exponent in range(e,end+1):
                    if c%power:
                        break
                    if c//power==(exponent+1)*slope+rest:
                        yield p, exponent
                    power *= p
        e=end+1


def growth(primes, bound, root=(1,1,1,1)):
    if not primes:
        yield root
        return
    p=primes[0]
    m,t,a,s=root
    power,sa,ss=1,1,1
    exponent=0
    while m*power*p<=bound:
        exponent+=1
        power*=p
        ss+=power
        sa+=(exponent+1)*power
        yield from growth(primes[1:],bound,(m*power,t*(exponent+1)*power,a*sa,s*ss))


def verify(m):
    ds=[d for d in range(1,m+1) if m%d==0]
    return m*len(ds),sum(d*sum(d%j==0 for j in range(1,d+1)) for d in ds),sum(ds)


def self_test():
    for m in range(1,120):
        t,a,s=verify(m)
        predicted=set(extensions(m,t,a,s))
        for p in (2,3,5,7,11,13,17,19,23,29):
            if not m%p:
                continue
            for e in range(1,12):
                ok=2*t*(e+1)*p**e==a*sum((j+1)*p**j for j in range(e+1))+s*sum(p**j for j in range(e+1))
                assert ok==((p,e) in predicted or (p,None) in predicted), (m,p,e)
    assert list(growth((3,5),30))==[(15,60,77,24)]


if __name__=="__main__":
    ap=argparse.ArgumentParser()
    ap.add_argument("--prime-limit",type=int,default=17)
    ap.add_argument("--support",type=int,default=3)
    ap.add_argument("--digits",type=int,default=35)
    ap.add_argument("--test",action="store_true")
    args=ap.parse_args()
    if args.test:
        self_test()
        print("Small divisor enumeration agrees with every tested extension.",flush=True)
    primes=[p for p in range(2,args.prime_limit+1) if gmpy2.is_prime(p)]
    count=0
    for r in range(1,args.support+1):
        for bases in combinations(primes,r):
            for m,t,a,s in growth(bases,10**args.digits):
                count+=1
                for p,e in extensions(m,t,a,s):
                    if p!=2 or m & (m-1):
                        print("candidate",m,p,e,"cofactor bases",bases,flush=True)
        print("distinct cofactor primes through",r,"total cofactors",count,flush=True)
