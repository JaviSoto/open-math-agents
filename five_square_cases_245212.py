"""Exact finite replay for the 3^2, 5, 7, 19, r branch of A245212."""
from fractions import Fraction as F
from math import ceil, prod
from sys import argv
from five_prime_sieve_245212 import scan
from rounding_245212 import exponent_ceiling


def exponent_floors(primes):
    full = F(34,27)*prod(F(p,p-1) for p in primes)
    bounds = {}
    for p in primes:
        # The first endpoint is affine in y and below 2 at both y=0 and 1.
        assert max(F(34,27)*F(p,p-1),F(47,27))<2
        coefficient = full/F(p,p-1)
        gap = coefficient*p-2*(p-1)
        assert gap>0
        e = 1
        for _ in range(3):
            terms = min(e,8)+1
            partial = (1-F(1,p**terms))/(1-F(1,p))
            e = max(e,ceil(coefficient*partial/gap)-1)
        bounds[p] = e
    return bounds


def run(r):
    assert r in (23,29,31)
    primes = (5,7,19,r)
    bounds = exponent_floors(primes)
    ceiling = exponent_ceiling(5,r)
    # Lower bound on X at exponent 5*floor using the infinite geometric sum.
    xlower = [1+(1-F(p,(p-1)*(5*bounds[p]+1)))/(p-1) for p in primes]
    assert F(34,27)*prod(xlower)>2
    for p in primes:
        result = scan(p,bounds[p],5*bounds[p]-1,ceiling,primes=primes,
                      floors=bounds,three_exponent=2,verbose=False)
        print(r,p,bounds[p],ceiling,*result,flush=True)


if __name__ == "__main__":
    for r in map(int,argv[1:] or (23,29,31)):
        run(r)
