"""Decide the two-odd-prime A245212 family at a fixed dyadic exponent.

Run python3 fixed_dyadic_pairs_245212.py --through 9, or add --prime 5.
The limits are derived from the input, never imposed on the prime powers.
"""
import argparse
from fractions import Fraction as F
from functools import lru_cache
from math import isqrt


def prime(q):
    return q>=2 and all(q%d for d in range(2,isqrt(q)+1))


@lru_cache(maxsize=8192)
def moments(p,e):
    power=p**e
    t=(e+1)*power
    s=(p*power-1)//(p-1)
    return (p*t-s)//(p-1),s,t


def times(m,n):
    return tuple(x*y for x,y in zip(m,n))


def ceil(x):
    return -(-x.numerator//x.denominator)


def exact(k,p,e,q,f,a,s,t):
    # The prime-power formulas are valid at primes. Do not attempt primality
    # of a huge recovered base until the far cheaper congruences have passed.
    if q<3 or f<1 or q==p or (a+s)%q:
        return False
    diff=a-(q-1)*s
    if not diff or diff%q**min(8,f) or f>(abs(diff).bit_length()-1)//max(1,q.bit_length()-1):
        return False
    aq,sq,tq=moments(q,f)
    if a*aq+s*sq!=2*t*tq or not prime(q):
        return False
    raise ArithmeticError(f"A245212 equality at 2^{k} * {p}^{e} * {q}^{f}")


def quotient_runs(a,s,t,limit):
    """Maximal exponent intervals on which the only possible last base is constant."""
    h=2*t-a
    if h<=0:
        return
    b=h-s
    f=max(1,(-b)//h+1)
    while f<=limit:
        floor=(a*f+s-1)//(h*f+b)
        end=limit
        if floor*h>a:
            end=min(end,(s-1-floor*b)//(floor*h-a))
        if a>(floor+1)*h:
            end=min(end,((floor+1)*b-s)//(a-(floor+1)*h))
        if end<f:
            raise ArithmeticError("Invalid quotient interval")
        yield f,end,floor+1
        f=end+1


def free_last(k,p,e,m,stats):
    a,s,t=m
    gap=2*t-a
    if gap<=0:
        return
    # A*f + S <= q*((2*T-A)*(f+1)-S) <= 2*q*(2*T-A)*f.
    # q^(f-1) <= A+S, so this lower bound for q cuts the exponent
    # range before any large integer quotient is computed.
    base=max(p+1,a//(2*gap))
    bits=base.bit_length()-1
    limit=(a+s).bit_length()-1
    for lo,hi,q in quotient_runs(a,s,t,limit//bits+1):
        stats["unknown_base_tests"]+=hi-lo+1
        stats["quotient_runs"]+=1
        if q>p:
            fixed_last(k,p,e,q,m,stats)


def fixed_last(k,p,e,q,m,stats):
    a,s,t=m
    stats["known_base_tests"]+=1
    if (a+s)%q:
        return
    den=(q-1)*(2*t*(q-1)-q*a)
    if den:
        f=(q*((q-1)*s-a))//den-1
        exact(k,p,e,q,f,a,s,t)


def sweep(k,only_prime=None):
    dyadic=moments(2,k)
    c=F(dyadic[0],dyadic[2])
    stats=dict(k=k,unbounded_pairs=0,bounded_pairs=0,unknown_base_tests=0,quotient_runs=0,known_base_tests=0)
    if only_prime is not None and (only_prime<3 or not prime(only_prime)):
        raise ValueError("--prime must be an odd prime")
    p=only_prime or 3
    while c*F(p,p-1)**2>=2:
        if prime(p):
            u=c*F(p,p-1)
            if u==2:
                raise ArithmeticError("Odd numerator of the dyadic factor and of the odd Euler factors precludes equality")
            if u>2:
                stats["unbounded_pairs"]+=1
                bound=ceil(u/((p-1)*(u-2)))
                for e in range(1,bound+1):
                    free_last(k,p,e,times(dyadic,moments(p,e)),stats)
            else:
                qmax=int(2/(2-u))
                for q in range(p+2,qmax+1,2):
                    if not prime(q):
                        continue
                    cap=u*F(q,q-1)
                    if cap<=2:
                        if cap==2:
                            raise ArithmeticError("Impossible exact Euler resonance")
                        continue
                    stats["bounded_pairs"]+=1
                    bound=ceil(cap*(F(1,p-1)+F(1,q-1))/(cap-2))
                    for e in range(1,bound+1):
                        fixed_last(k,p,e,q,times(dyadic,moments(p,e)),stats)
                        fixed_last(k,q,e,p,times(dyadic,moments(q,e)),stats)
        if only_prime:
            break
        p+=2
    return stats


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--through",type=int,required=True)
    parser.add_argument("--from-k",type=int,default=0)
    parser.add_argument("--prime",type=int)
    args=parser.parse_args()
    for k in range(args.from_k,args.through+1):
        print(sweep(k,args.prime),flush=True)
