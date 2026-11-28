"""Certify a rational interval missed by all distinct odd-prime Euler products.

python3 euler_gap_245212.py --dyadic 1 --rank 3
python3 euler_gap_245212.py --A 35 --H 48 --rank 3 --exclude-divisors

Every prefix (including the empty one) is considered. At a prefix below
target, prove its entire large-next-prime tail stays at least halfway from
the target. A prefix above target can only increase. Return zero with a
witness when any subproduct is exactly at the target. The routine is
effective for every finite rank, but running time can grow very quickly.
"""
import argparse
from fractions import Fraction
from math import isqrt


def prime(n):
    return n >= 2 and all(n % i for i in range(2,isqrt(n)+1))


def cutoff(prefix, target, remaining):
    """First integer p≥2 for which prefix*(p/(p−1))^remaining≤midpoint."""
    numer = 2*prefix.numerator
    denom = (prefix+target)*prefix.denominator
    def tail_fits(p):
        return numer*p**remaining <= denom*(p-1)**remaining
    lo,hi = 1,2
    while not tail_fits(hi):
        lo,hi = hi,2*hi
    while hi>lo+1:
        mid = (lo+hi)//2
        if tail_fits(mid):
            hi = mid
        else:
            lo = mid
    return hi


def certify(A,H,rank,exclude=False):
    if min(A,H)<=0 or rank<0:
        raise ValueError('positive moments and nonnegative rank required')
    nodes = 0
    witness = None
    def visit(value, path, left):
        nonlocal nodes,witness
        nodes += 1
        gap = abs(H-value)
        if not gap:
            witness = path
        if not left or value>=H:
            return gap
        limit = cutoff(value,H,left)
        lower = gap/2
        minimum = path[-1]+2 if path else 3
        for p in range(minimum,limit,2):
            if prime(p) and not (exclude and H%p==0):
                lower = min(lower,visit(value*Fraction(p,p-1),path+(p,),left-1))
                if not lower:
                    break
        return lower
    distance = visit(Fraction(A),(),rank)
    return distance,nodes,witness


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--dyadic',type=int,help='use A=W(2^k), H=2*(k+1)*2^k')
    parser.add_argument('--A',type=int)
    parser.add_argument('--H',type=int)
    parser.add_argument('--rank',type=int,required=True)
    parser.add_argument('--exclude-divisors',action='store_true',help='omit primes dividing H')
    args = parser.parse_args()
    if args.dyadic is not None:
        if args.dyadic<0 or args.A is not None or args.H is not None:
            parser.error('use one nonnegative dyadic exponent, or A and H')
        k = args.dyadic
        A, H = k*(2**(k+1))+1, (k+1)*2**(k+1)
    elif args.A and args.H:
        A, H = args.A,args.H
    else:
        parser.error('supply --dyadic or both --A and --H')
    gap,nodes,witness = certify(A,H,args.rank,args.exclude_divisors)
    print(f'A={A}, H={H}, rank≤{args.rank}: gap≥{gap}; {nodes} prefixes examined')
    if witness is not None:
        print('Exact resonance at:',witness)


if __name__=='__main__':
    main()
