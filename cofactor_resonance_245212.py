"""Recover the unique odd Euler support, if any, of a fixed A245212 cofactor.

python3 cofactor_resonance_245212.py --limit 100000
For a unitary prefix h of a solution, seek W(h)*prod(q) = 2h*tau(h)*prod(q-1)
with distinct odd q coprime to h and a nonempty product. The largest q can
never cancel against a smaller q-1, so the reduced numerator of H/W(h)
determines q. This is exhaustive for each tested h, independent of rank.
"""
from argparse import ArgumentParser
from functools import lru_cache
from math import gcd


@lru_cache(maxsize=16384)
def largest_prime(n):
    largest = 1
    divisor = 2
    while divisor * divisor <= n:
        if n % divisor == 0:
            largest = divisor
            while n % divisor == 0:
                n //= divisor
        divisor = 3 if divisor == 2 else divisor + 2
    return max(n,largest)


def support(h,weighted,target):
    if weighted >= target or weighted % h:
        return None
    common = gcd(target,weighted)
    n,d = target//common,weighted//common
    primes = []
    while n != d:
        if n <= d or n % 2 == 0 or d % 2 == 1:
            return None
        q = largest_prime(n)
        if h % q == 0 or (primes and q >= primes[-1]):
            return None
        primes.append(q)
        n = n//q*(q-1)
        common = gcd(n,d)
        n,d = n//common,d//common
    return tuple(reversed(primes))


def moments_up_to(limit):
    tau = [0]*(limit+1)
    for d in range(1,limit+1):
        for n in range(d,limit+1,d):
            tau[n] += 1
    weighted = [0]*(limit+1)
    for d in range(1,limit+1):
        w = d*tau[d]
        for n in range(d,limit+1,d):
            weighted[n] += w
    return tau,weighted


if __name__=='__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--limit',type=int,required=True)
    opts = parser.parse_args()
    tau,W = moments_up_to(opts.limit)
    divisible = 0
    found = 0
    for h in range(1,opts.limit+1):
        H = 2*h*tau[h]
        if W[h]<H and W[h]%h==0:
            divisible += 1
            primes = support(h,W[h],H)
            if primes is not None:
                found += 1
                print(f'h={h} support={primes} W={W[h]} H={H}')
    print(f'Tested h=1..{opts.limit}; {divisible} meet the divisibility and size conditions; {found} have a resonance.')
