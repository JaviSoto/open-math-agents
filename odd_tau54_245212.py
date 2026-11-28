"""Measure and check fixed odd-divisor profiles with one odd exponent.

The exact two-adic order theorem in OrdersResearch245212.lean supplies the
stronger residue; profiles with multiple odd exponents keep the baseline.
"""
from functools import cache,lru_cache
from math import prod

from odd_tau36_245212 import local,prime_interval,solve as base_solve


def v2(n):
    return (n & -n).bit_length()-1


def odd_residue(k, exponents):
    if sum(e%2 for e in exponents)!=1:
        return None
    difference=v2(prod(e+2 for e in exponents))-len(exponents)
    if difference<0:
        raise ValueError("the exponent obstruction already excludes this profile")
    height=1+k+v2(k+1)
    if difference==height:
        # The only possible U is larger than height.
        modulus=1<<(height+2)
        return modulus,modulus-1
    # U is exactly the smaller of height and difference.
    order=min(height,difference)+1
    return 1<<(order+1),(1<<order)-1


def quadratic_residues(modulus,A,S,T,e,last=2):
    """First residues for which the last linear or quadratic has a nonzero root."""
    squares={y*y%modulus for y in range(modulus)}
    ok=set()
    for x in range(1,modulus):
        z,w,s=local(x,e) if x>1 else (1,(e+1)*(e+2)//2,e+1)
        a=A*w; b=S*s
        if last==1:
            d=(T*z-2*a-b)%modulus
            num=(a+b)%modulus
            if bool(d)==bool(num): ok.add(x)
            continue
        d=(T*z-3*a-b)%modulus
        top=(2*a+b)%modulus; constant=(a+b)%modulus
        if not d:
            has_root=bool(top and constant) or top==constant==0
        elif not constant:
            has_root=top!=0
        else:
            has_root=(top*top+4*d*constant)%modulus in squares
        if has_root: ok.add(x)
    return ok


def residue_tile(ok,p):
    """p bytes encode the complete 8*p-bit repeat, with bit i representing 2*i."""
    return bytes(sum(((16*j+2*i)%p in ok)<<i for i in range(8)) for j in range(p))


@cache
def local_mod(p,e):
    """(power, W, σ) modulo p; indexed by the candidate residue, including 1."""
    return [(pow(x,e,p),
             sum((i+1)*pow(x,i,p) for i in range(e+1))%p,
             sum(pow(x,i,p) for i in range(e+1))%p) for x in range(p)]


@cache
def last_images(p,e):
    """Possible values of u*W(yᵉ)/yᵉ + σ(yᵉ)/yᵉ for each u in F_p."""
    pairs=[(w*pow(z,-1,p)%p,s*pow(z,-1,p)%p) for z,w,s in local_mod(p,e)[1:]]
    rows=[{(u*w+s)%p for w,s in pairs} for u in range(p)]
    return rows,{w for w,_ in pairs}


def general_residues(p,A,S,T,a,b):
    rows,w_only=last_images(p,b)
    ok=set()
    for x,(z,w,s) in enumerate(local_mod(p,a)[1:],1):
        aw=A*w%p; ss=S*s%p; tz=T*z%p
        if ss:
            inv=pow(ss,-1,p)
            allowed=tz*inv%p in rows[aw*inv%p]
        elif aw:
            allowed=tz*pow(aw,-1,p)%p in w_only
        else:
            allowed=not tz
        if allowed: ok.add(x)
    return ok


def tail_sieve(t,k):
    gh=(1<<(k+1))-1
    gl=k*gh+k+1
    moduli=(3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97)
    @lru_cache(maxsize=12)
    def tiles(prefix,exps):
        m,a,s=prefix
        out=[]
        for p in moduli:
            ok=general_residues(p,gl*a%p,gh*s%p,(gl+gh)*t*m%p,*exps)
            if not ok: return None
            out.append((p,pow(16,-1,p),residue_tile(ok,p),len(ok)/p))
        return sorted(out,key=lambda entry:entry[3])
    def sieve(prefix,exps,lo,hi):
        if lo<=moduli[-1] or hi-lo<4096:
            yield from prime_interval(lo,hi)
            return
        patterns=tiles(prefix,exps)
        if patterns is None: return
        lo|=1
        for start in range(lo,hi+1,1<<19):
            n=min((hi-start)//2+1,1<<18)
            passing=(1<<n)-1
            nbytes=(n+7)//8
            for p,inv,tile,_ in patterns:
                shift=start*inv%p
                adjusted=tile[shift:]+tile[:shift]
                packed=(adjusted*(nbytes//p+1))[:nbytes]
                passing&=int.from_bytes(packed,'little')
                if not passing: break
            # All primes survive a Fermat test. The remaining bases may
            # include pseudoprimes, which can only add conservative checks.
            if passing.bit_count()>=nbytes//64:
                for byte_index,byte in enumerate(passing.to_bytes(nbytes,'little')):
                    while byte:
                        bit=byte & -byte
                        x=start+16*byte_index+2*(bit.bit_length()-1)
                        if pow(2,x-1,x)==1: yield x
                        byte^=bit
            else:
                while passing:
                    bit=passing & -passing
                    x=start+2*(bit.bit_length()-1)
                    if pow(2,x-1,x)==1: yield x
                    passing^=bit
    return sieve


def solve(t,k,exps,plan=False,window=None,audit=False):
    return base_solve(t,k,exps,plan,window,audit,odd_residue(k,exps),tail_sieve(t,k))


def self_test():
    from random import Random
    from odd_tau36_245212 import self_test as common_tests
    common_tests()
    rng=Random(54)
    for p in (3,5,7,11,13,17,19,23):
        for _ in range(60):
            A,S,T=(rng.randrange(p) for _ in range(3))
            a,b=rng.randrange(1,8),rng.randrange(1,12)
            xs,ys=local_mod(p,a),local_mod(p,b)
            brute={x for x,(z,w,s) in enumerate(xs[1:],1)
                   if any((T*z*Z-A*w*W-S*s*U)%p==0 for Z,W,U in ys[1:])}
            ok=general_residues(p,A,S,T,a,b)
            if brute!=ok: raise AssertionError("projected residue set")
            tile=residue_tile(ok,p)
            for start in range(p):
                shift=start*pow(16,-1,p)%p
                rotated=tile[shift:]+tile[:shift]
                if any(bool(rotated[j//8]&(1<<(j%8)))!=((start+2*j)%p in ok)
                       for j in range(8*p)): raise AssertionError("packed residue offset")
            for d in (1,2):
                if quadratic_residues(p,A,S,T,a,d)!=general_residues(p,A,S,T,a,d):
                    raise AssertionError("discriminant comparison")
    print("480 finite-field and packed-table tests; 960 independent linear/quadratic tests passed")


if __name__=="__main__":
    from odd_tau36_245212 import main
    main(solve,54,self_test,__doc__)
