"""Integer-rounding obstruction for unrestricted exponents at fixed prime bases.

The derivation of exponent_ceiling and the integer gap is given in
prime-power-height-245212.md. Only integers and exact rational numbers are
used in the certificate comparisons.
"""
from fractions import Fraction
from functools import lru_cache
from math import prod


@lru_cache
def exponent_ceiling(k,B):
    assert k>=1 and B>=3
    d=k*2**k
    a=2**k*(k+k.bit_length()+(2*k+1+2*B)*B.bit_length())
    t=max(256*d*d,2*a+1)
    while (better:=a+d*t.bit_length())<t:
        t=better
    return t


def rounded(bases,boxes):
    return rounded_ranges(tuple((p,p) for p in bases),boxes)


@lru_cache(100000)
def log_bounds(p):
    # 1/128-bit outward rounding, exactly, using 2^a ≤ p^128 < 2^(a+1).
    b=(p**128).bit_length()
    return b-1,b


def singleton_caps(primes,boxes,stride):
    """At an actual solution, each individual prime power is bounded by all the others."""
    k=len(primes)
    global_cap=exponent_ceiling(k,max(p for _,p in primes))
    highs=[global_cap if h is None else min(h,global_cap) for _,h in boxes]
    for _ in range(2):
        for i,(p,P) in enumerate(primes):
            z=log_bounds(2**(k-1)+P-1)[1]+sum(log_bounds(highs[j]+1)[1]+
                highs[j]*log_bounds(primes[j][1])[1] for j in range(k) if i!=j)
            h=min(highs[i],z//log_bounds(p)[0])
            highs[i]=h-h%stride
            if highs[i]<boxes[i][0]:
                return None
    lows=[l for l,_ in boxes]
    if stride==1:
        for i,(p,P) in enumerate(primes):
            fixed=log_bounds(2**(k-1)+P-1)[1]+sum(log_bounds(highs[j]+1)[1] for j in range(k) if j!=i)
            needed=lows[i]*log_bounds(p)[0]-fixed
            for j in range(k):
                if i==j:
                    continue
                other=sum(highs[t]*log_bounds(primes[t][1])[1] for t in range(k) if t not in (i,j))
                lows[j]=max(lows[j],-((other-needed)//log_bounds(primes[j][1])[1]))
                if lows[j]>highs[j]:
                    return None
    return tuple(zip(lows,highs))


def rounded_ranges(primes,boxes):
    """Veto a whole prime/exponent box; each prime may lie anywhere between its bounds."""
    k=len(primes)
    B=max(p for _,p in primes)
    cap=exponent_ceiling(k,B)
    lows=tuple(lo for lo,_ in boxes)
    if any(lo>cap for lo in lows):
        return True
    highs=tuple(min(cap,h) if h is not None else cap for _,h in boxes)
    # Overapproximate log2(D) by integral bit lengths, with D selected
    # separately at each prime: exact at low factors, asymptotic at high ones.
    upper_bits=tuple(log_bounds(p)[1] for _,p in primes)
    lower_bits=tuple(log_bounds(p)[0] for p,_ in primes)
    exp_bits=tuple(log_bounds(h+1)[1] for h in highs)
    error_bits=log_bounds(k*(2**(k-1)+B-1))[1]
    ys=tuple(Fraction(p,(p-1)*(lo+1)) for (p,_),lo in zip(primes,lows))
    strict=[(P-1)*prod(ys[:i]+ys[i+1:])<1 for i,(_,P) in enumerate(primes)]
    # The best subset can be sought among the terminal segments sorted
    # by lower prime-power height; each trial is an independent valid veto.
    order=sorted(range(k),key=lambda i: lows[i]*lower_bits[i],reverse=True)
    for n in range(1,k+1):
        top=order[:n]
        ds=[exp_bits[j]+(2*upper_bits[j] if j in top else highs[j]*upper_bits[j]) for j in range(k)]
        whole=sum(ds)
        if not all(lows[i]*lower_bits[i]>error_bits+whole-ds[i] for i in top):
            continue
        if n==1 or all(strict[i] for i in top):
            return True
        # If the true score were 2 the rounded numerator would now be 2D.
        # But both rounded local numerators at the largest selected prime p
        # contain p. D is coprime to p apart from the exponent-plus-one factors.
        t=max(top,key=lambda j:primes[j][0])
        p,P=primes[t]
        if not all(primes[j][1]<=p for j in top if j!=t):
            continue
        if all(h+1<p or (p==P and l+1+(-(l+1))%p>h+1) for l,h in zip(lows,highs)):
            return True
    return False
