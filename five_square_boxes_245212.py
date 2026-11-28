"""Cover a fixed rank-five support by disjoint exponent boxes.

The score bounds below are outward rounded on a fixed dyadic grid. The
remaining boxes are screened with the integer-rounding lemma before any
enumeration. Run with two ordered primes q,r for the support (3,5,7,q,r).
"""
from argparse import ArgumentParser
from functools import cache
from itertools import product
from math import ceil, floor, prod
from odd_four_245212 import factors, moment, prime
from odd_modular_245212 import residues
from five_prime_sieve_245212 import ResidueTable
from five_square_cases_245212 import exponent_floors
from rounding_245212 import exponent_ceiling, rounded_ranges

GRID = 1 << 42


def intervals(p,lo,hi):
    while lo<=hi:
        end = min(hi, 2*lo-1)
        a,b,c,d = factors(((lo,end),(p,p)))
        yield (lo,end,floor(GRID*a),ceil(GRID*b),floor(GRID*c),ceil(GRID*d))
        lo=end+1


def remaining(q,r):
    primes = (5,7,q,r)
    assert 7<q<r and prime(q) and prime(r)
    cap = exponent_ceiling(5,r)
    lows = exponent_floors(primes)
    domains = [list(intervals(p,lows[p],cap)) for p in primes]
    fixed = tuple((p,p) for p in (3,*primes))
    target = 54*GRID**4
    for box in product(*domains):
        if (34*prod(a[2] for a in box)+13*prod(a[4] for a in box)>target or
            34*prod(a[3] for a in box)+13*prod(a[5] for a in box)<target):
            continue
        bounds = tuple((row[0],row[1]) for row in box)
        if not rounded_ranges(fixed, ((2,2),*bounds)):
            yield bounds


def verify(q,r):
    primes = (5,7,q,r)
    @cache
    def table(p,other,h,lo,hi):
        return ResidueTable(p,other,hi,{other:lo},{p:p**h})

    counts = [0,0,0,0]
    for box in remaining(q,r):
        counts[0] += 1
        bounds = dict(zip(primes,box))
        i,j,a,b = sorted(primes,key=lambda p:bounds[p][1]-bounds[p][0])
        if a**min(20,bounds[a][0]) < b**min(20,bounds[b][0]):
            a,b = b,a
        tab_b = table(a,b,min(20,bounds[a][0]),*bounds[b])
        tab_a = table(b,a,min(20,bounds[b][0]),*bounds[a])
        def fixed(p,e):
            return residues(p,e,tab_b.modulus),residues(p,e,tab_a.modulus)
        js = [(v,*fixed(j,v)) for v in range(bounds[j][0],bounds[j][1]+1)]
        for u in range(bounds[i][0],bounds[i][1]+1):
            (w1,s1),(w2,s2) = fixed(i,u)
            for v,(w3,s3),(w4,s4) in js:
                counts[1] += 1
                bs = tab_b.hits(34*w1*w3,13*(a-1)*s1*s3)
                if not bs:
                    continue
                aa = tab_a.hits(34*w2*w4,13*(b-1)*s2*s4)
                for ea,eb in product(aa,bs):
                    counts[2] += 1
                    es = {i:u,j:v,a:ea,b:eb}
                    for p in (i,j):
                        mod = p**min(20,es[p])
                        vals = [residues(z,e,mod) for z,e in es.items() if z!=p]
                        if (34*prod(w for w,_ in vals)-13*(p-1)*prod(s for _,s in vals))%mod:
                            break
                    else:
                        counts[3] += 1
                        t,w,s = map(prod,zip(*(moment(p,e) for p,e in es.items())))
                        if 34*w+13*s==54*t:
                            raise ArithmeticError(f"solution: {es}")
    ResidueTable.index.cache_clear()
    table.cache_clear()
    print(q,r,*counts,flush=True)


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("q",type=int)
    parser.add_argument("r",type=int,nargs="+")
    parser.add_argument("--sizes",action="store_true")
    args = parser.parse_args()
    for r in args.r:
        if args.sizes:
            boxes = list(remaining(args.q,r))
            sizes = [prod(sorted(hi-lo+1 for lo,hi in b)[:2]) for b in boxes]
            print(args.q,r,len(boxes),sum(sizes),max(sizes,default=0))
        else:
            verify(args.q,r)
