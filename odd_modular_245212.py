"""Exact modular pruning for exponent boxes in the four-prime divisor equality.

For each term p^e dividing n, write n=p^e*m.  The equality implies
p^e | W(m)-(p-1)*sigma(m).  This module tests that divisibility on whole
progressions of exponents of another prime q; periods are verified locally.
"""
from functools import lru_cache
from itertools import product
from math import gcd, prod


@lru_cache(250000)
def residues(q, e, mod):
    if q==1:
        return ((e+1)*(e+2)//2)%mod,(e+1)%mod
    v = q - 1
    power = pow(q, e+1, mod*v*v)
    return ((power*((e+1)*v-1)+1)//(v*v)) % mod, ((power-1)//v) % mod


@lru_cache(10000)
def period(p, q, h):
    mod = p**h
    length = (p-1)*mod
    # The block of length T contributes 0 in both the unweighted and
    # weighted sums. T=0 mod mod kills translation of the weights.
    assert pow(q,length,mod)==1 and residues(q,length-1,mod)==(0,0)
    return length


@lru_cache(50000)
def lifted(p, q, A, S, h):
    mod=p**h
    if A%p==0 and S%p==0:
        if h==1:
            return 1,(0,)
        return lifted(p,q,A//p,S//p,h-1)
    M=period(p,q,h)
    if h==1:
        candidates=range(M)
    else:
        modulus,roots=lifted(p,q,A%(mod//p),S%(mod//p),h-1)
        if roots is None or len(roots)*(M//modulus)>10000:
            return M,None
        candidates=(d for r in roots for d in range(r,M,modulus))
    hits=[]
    for d in candidates:
        w,s=residues(q,d,mod)
        if (A*w-S*s)%mod==0:
            hits.append(d)
    return M,tuple(hits)


def stride_residue(r,M,stride):
    """Intersection of d=r mod M with the positive multiple-of-stride constraint."""
    g=gcd(M,stride)
    if r%g:
        return None
    s=stride//g
    j=(-r//g*pow(M//g,-1,s))%s if s>1 else 0
    return r+M*j,M*s


def impossible(bases, exps,stride=1):
    """Return true only if one p-adic condition excludes the entire box."""
    for i,p in enumerate(bases):
        if p>47:
            continue
        h=min(exps[i][0],15 if p<=7 else 8)
        if h==0:
            continue
        mod=p**h
        others=[j for j in range(4) if j!=i]
        def width(j):
            l,r=exps[j]
            return (r is None,0 if r is None else r-l)
        others.sort(key=width)
        j,k,z=others
        if exps[k][1] is None:
            continue
        trials=(1+(exps[j][1]-exps[j][0])//stride)*(1+(exps[k][1]-exps[k][0])//stride)
        if trials>4 or (trials>1 and exps[z][1] is None):
            continue
        possible=False
        low,high=exps[z]
        for u,v in product(range(exps[j][0],exps[j][1]+1,stride),range(exps[k][0],exps[k][1]+1,stride)):
            a,b=residues(bases[j],u,mod)
            c,d=residues(bases[k],v,mod)
            A=a*c%mod
            S=(p-1)*b*d%mod
            if high is not None and high-low<=40*stride:
                for w in range(low,high+1,stride):
                    x,y=residues(bases[z],w,mod)
                    if (A*x-S*y)%mod==0:
                        possible=True;break
            else:
                M,R=lifted(p,bases[z],A,S,h)
                if R is None or any(hit is not None and (high is None or low+(hit[0]-low)%hit[1]<=high)
                                    for hit in (stride_residue(r,M,stride) for r in R)):
                    possible=True
            if possible:
                break
        if not possible:
            return True
    return False


def tighten(bases, exps,stride=1):
    """Intersect the exponent intervals with consequences of all useful prime moduli."""
    work=list(exps)
    for i,p in enumerate(bases):
        if p>43:
            continue
        h=min(work[i][0],24 if p<=7 else 12)
        if h<2:
            continue
        mod=p**h
        for z,(lo,hi) in enumerate(work):
            if z==i or lo==hi:
                continue
            j,k=[j for j in range(4) if j not in (i,z)]
            if work[j][1] is None or work[k][1] is None:
                continue
            if (1+(work[j][1]-work[j][0])//stride)*(1+(work[k][1]-work[k][0])//stride)>6:
                continue
            lows=[];highs=[]
            for u,v in product(range(work[j][0],work[j][1]+1,stride),range(work[k][0],work[k][1]+1,stride)):
                a,b=residues(bases[j],u,mod)
                c,d=residues(bases[k],v,mod)
                A=a*c%mod;S=(p-1)*b*d%mod
                M,R=lifted(p,bases[z],A,S,h)
                if R is None:
                    lows=[lo];highs=[hi];break
                for r in R:
                    hit=stride_residue(r,M,stride)
                    if hit is None:
                        continue
                    rr,mm=hit
                    first=lo+(rr-lo)%mm
                    if hi is None or first<=hi:
                        lows.append(first)
                        highs.append(None if hi is None else hi-(hi-rr)%mm)
            if not lows:
                return None
            work[z]=min(lows),None if hi is None else max(highs)
    return tuple(work)


@lru_cache(50000)
def base_roots(p,h,d,A,S):
    """Roots u (units modulo p^h) of A*W(u^d)-S*sigma(u^d), or None if too numerous."""
    if h==0:
        return 1,(0,)
    Q=p**h
    if A%p==0 and S%p==0:
        return base_roots(p,h-1,d,A//p,S//p)
    if h==1:
        candidates=range(1,p)
    else:
        m,rr=base_roots(p,h-1,d,A%(Q//p),S%(Q//p))
        if rr is None or len(rr)*(Q//m)>150:
            return Q,None
        candidates=(v for r in rr for v in range(r,Q,m))
    roots=[]
    for r in candidates:
        w,s=residues(r,d,Q)
        if (A*w-S*s)%Q==0:
            roots.append(r)
    return Q,tuple(roots)


def variable_base_impossible(bases,exps,rr):
    """All possible final primes fail a p-adic divisor condition imposed at an earlier base."""
    lo,hi=rr
    if lo==hi:
        return False
    for i,p in enumerate(bases):
        h=min(exps[i][0],16 if p<=5 else 10)
        if h<2:
            continue
        j,k=[t for t in range(3) if t!=i]
        B=[exps[z] for z in (j,k,3)]
        if prod(b-a+1 for a,b in B)>10:
            continue
        Q=p**h
        for e,f,d in product(*(range(a,b+1) for a,b in B)):
            u,v=residues(bases[j],e,Q)
            w,s=residues(bases[k],f,Q)
            m,roots=base_roots(p,h,d,(u*w)%Q,((p-1)*v*s)%Q)
            if roots is None or any(lo+(z-lo)%m<=hi for z in roots):
                break
        else:
            return True
    return False
