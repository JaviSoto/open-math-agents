"""Test all even A245212 candidates 2^k*u*p on an inclusive range of odd cores.

p is a fresh odd prime of exponent one; neither p nor k has a search cutoff.
The Lean logarithmic bound and resultant supply the finite list. No primality
oracle: report *every* surviving odd coprime quotient, even a composite one.
"""
from argparse import ArgumentParser
from collections import Counter
from math import gcd, isqrt


def primes_upto(n):
    sieve = bytearray([1])*(n+1)
    for p in range(2,isqrt(n)+1):
        if sieve[p]:
            sieve[p*p::p] = bytes(len(sieve[p*p::p]))
    return [p for p in range(2,n+1) if sieve[p]]


def cores(start, stop, primes):
    """Factor one bounded segment; all moment arithmetic uses Python integers."""
    first = start | 1
    values = list(range(first,stop+1,2))
    residual = values.copy()
    moments = [[1,1,1] for _ in values]
    for p in primes:
        if p==2:
            continue
        if p*p>stop:
            break
        hit = first + (-first)%p
        if hit%2==0:
            hit += p
        for i in range((hit-first)//2,len(values),p):
            e, power = 0, 1
            while residual[i]%p==0:
                residual[i] //= p
                e += 1
                power *= p
            t = (e+1)*power
            s = (p*power-1)//(p-1)
            w = (p*t-s)//(p-1)
            row = moments[i]
            row[0] *= t
            row[1] *= w
            row[2] *= s
    for u, (t,w,s), p in zip(values,moments,residual):
        if p>1:
            t,w,s = t*2*p,w*(2*p+1),s*(p+1)
        yield u,t,w,s


def check(start,stop):
    primes = primes_upto(isqrt(stop))
    counts = Counter()
    for lo in range(start,stop+1,32768):
        for u,t,w,s in cores(lo,min(lo+32767,stop),primes):
            counts["odd cores"] += 1
            c = 2*w-s
            factor = w*s+2*t*(w-s)
            cap = 2*((c+factor).bit_length()-1)
            for k in range(1,cap+1):
                linear = 2*(k+1)*t-2*k*w-s
                if linear<=0:
                    # w>=t: the term d=u in W contributes exactly t.
                    break
                z = 1<<(k+1)
                d = z*linear-c
                if d<=0:
                    continue
                counts["positive denominators"] += 1
                if (k+1)*factor%d:
                    continue
                counts["resultant divides"] += 1
                numerator = z*(k*w+s)+w-s
                p, remainder = divmod(numerator,d)
                if remainder:
                    continue
                counts["integer quotients"] += 1
                if p>=3 and p%2 and gcd(p,u)==1:
                    print(f"unresolved u={u} k={k} p={p}",flush=True)
                    counts["unresolved"] += 1
    return counts


if __name__=="__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("start",type=int)
    parser.add_argument("stop",type=int)
    args = parser.parse_args()
    if not 1<=args.start<=args.stop:
        parser.error("Use a positive inclusive range")
    result = check(args.start,args.stop)
    print(dict(result))
    raise SystemExit(bool(result["unresolved"]))
