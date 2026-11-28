"""Exact cross-prime check for 3*5^a*7^b*11^c*13^d (A245212).

Each prime power p^e dividing a solution forces W(n/p^e)=(p-1)*sigma(n/p^e)
modulo p^e. With two of the four variable exponents fixed, the condition
at either unfixed prime depends only on the exponent of the other one.
"""
from argparse import ArgumentParser
from collections import defaultdict
from functools import cache
from itertools import product
from math import gcd, prod
from odd_four_245212 import moment
from odd_modular_245212 import residues
from rounding_245212 import exponent_ceiling

PRIMES = (5, 7, 11, 13)
FLOORS = dict(zip(PRIMES, (18, 12, 7, 6)))
CEILING = exponent_ceiling(5, 13)


def direction(w, s, p, modulus):
    if w % p:
        return 0, s * pow(w, -1, modulus) % modulus
    return 1, w * pow(s, -1, modulus) % modulus


class ResidueTable:
    def __init__(self, p, q, ceiling, floors=FLOORS, moduli=None):
        self.p = p
        self.modulus = moduli[p] if moduli is not None else p**floors[p]
        self.groups = defaultdict(list)
        for e in range(floors[q], ceiling + 1):
            w, s = residues(q, e, self.modulus)
            common = gcd(gcd(w, s), self.modulus)
            self.groups[common].append((e, w // common, s // common))

    @cache
    def index(self, common, modulus):
        result = defaultdict(list)
        for e, w, s in self.groups[common]:
            result[direction(w, s, self.p, modulus)].append(e)
        return result

    def hits(self, a, b):
        """All exponents with a*W = b*sigma modulo the table modulus."""
        p, m = self.p, self.modulus
        common = gcd(gcd(a, b), m)
        a, b = a//common, b//common
        result = []
        for divisor, rows in self.groups.items():
            mod = (m//common)//divisor
            if mod <= 1:
                result.extend(e for e, _, _ in rows)
            else:
                result.extend(self.index(divisor, mod).get(direction(b, a, p, mod), ()))
        return result


def scan(i, start, stop, ceiling, *, primes=PRIMES, floors=FLOORS, three_exponent=1, verbose=True):
    r, s, j = (p for p in primes if p != i)
    # A smaller power remains a necessary test. Limiting its size speeds up
    # the case where the proved minimum exponent is in the hundreds.
    moduli = {p:p**min(floors[p],20) for p in primes}
    t0, w0, z0 = moment(3,three_exponent)
    ts = ResidueTable(r, s, ceiling, floors, moduli)
    tr = ResidueTable(s, r, ceiling, floors, moduli)
    def factors(p, q, e):
        return residues(q, e, moduli[p])
    jrows = [(v, factors(r, j, v), factors(s, j, v)) for v in range(floors[j], ceiling+1)]
    tested = 0
    survivors = 0
    for u in range(start, stop+1):
        w1, z1 = factors(r, i, u)
        w2, z2 = factors(s, i, u)
        for v, (w3, z3), (w4, z4) in jrows:
            tests = ts.hits(w0*w1*w3, z0*(r-1)*z1*z3)
            if not tests:
                continue
            testr = tr.hits(w0*w2*w4, z0*(s-1)*z2*z4)
            for er, es in product(testr, tests):
                exps = {i:u,j:v,r:er,s:es}
                tested += 1
                for p in (i,j):
                    m = p**min(exps[p],20)
                    pairs = [residues(q,e,m) for q,e in exps.items() if q != p]
                    if (w0*prod(w for w,_ in pairs)-z0*(p-1)*prod(z for _,z in pairs))%m:
                        break
                else:
                    survivors += 1
                    t,w,z = map(prod, zip(*(moment(q,e) for q,e in exps.items())))
                    if w0*w+z0*z == 2*t0*t:
                        raise ArithmeticError(f"solution: {exps}")
        if verbose:
            print(f"p={i} e={u}: tested {tested} pairs; {survivors} reached exact equality test",flush=True)
    ts.index.cache_clear()
    return (stop-start+1)*len(jrows), tested, survivors


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("prime", type=int, choices=PRIMES)
    parser.add_argument("--start", type=int)
    parser.add_argument("--stop", type=int)
    parser.add_argument("--ceiling", type=int, default=CEILING)
    args = parser.parse_args()
    scan(args.prime, args.start or FLOORS[args.prime],
         args.stop or 4*FLOORS[args.prime]-1, args.ceiling)
