"""Validate the cyclic modulus search against definition-level enumeration.

Pass the compiled cyclic_min_modulus binary as the sole argument.
"""
from collections import Counter
from itertools import combinations, combinations_with_replacement
from math import gcd
from subprocess import check_output
from sys import argv


def valid(points, modulus):
    target = sum(points) % modulus
    for selection in combinations_with_replacement(points, len(points)):
        if selection != points and sum(selection) % modulus == target:
            return False
    return True


def direct_orbits(n, modulus):
    # Every orbit contains a set passing through zero. For each valid set,
    # directly enumerate every translate-through-zero and every unit scale.
    reps = set()
    units = [u for u in range(1, modulus) if gcd(u,modulus)==1]
    for tail in combinations(range(1,modulus),n-1):
        points=(0,*tail)
        if valid(points,modulus):
            reps.add(min(tuple(sorted((u*(x-y)) % modulus for x in points))
                         for u in units for y in points))
    return len(reps)


def main(binary):
    for n in range(2,7):
        largest=17
        lines=check_output([binary,str(n),str(n),str(largest),"--orbits"],text=True).splitlines()
        for modulus,line in zip(range(n,largest+1),lines,strict=True):
            got=int(line.rsplit(" ",1)[1])
            expected=direct_orbits(n,modulus)
            assert got==expected,(n,modulus,got,expected)
    print("All affine orbit counts agree for n=2..6, n<=N<=17.")
    # Independent positive check, including every rival multiset.
    for n in range(2,10):
        result=2**n-2**(n.bit_length()-1)
        points=tuple(2**i-1 for i in range(n))
        assert valid(points,result)
    print("Directly enumerated competing multisets of the extremal examples for n=2..9.")


if __name__=="__main__":
    main(argv[1])
