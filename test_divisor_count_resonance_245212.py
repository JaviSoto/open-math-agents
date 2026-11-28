"""Reproduce positive controls and exactness checks for the cofactor search."""
from collections import Counter
from itertools import combinations, product
from math import prod
from unittest import TestCase, main

import divisor_count_resonance_245212 as solver


class DivisorCountSearch(TestCase):
    def test_recovers_planted_solutions(self):
        n=0
        for rank in range(1,5):
            for primes in combinations((3,5,7,11,17),rank):
                for exponents in product((1,2,3),repeat=rank):
                    want=tuple(zip(primes,exponents))
                    ratio=prod(solver.weighted(p,e) for p,e in want)
                    out=list(solver.prefix_search(tuple(sorted(exponents)),(),ratio,3,(),Counter()))
                    self.assertIn(want,out)
                    self.assertEqual(len(out),len(set(out)))
                    n+=1
        self.assertEqual(n,780)

    def test_independent_target_generators(self):
        for d in range(2,1025):
            self.assertEqual(set(solver.targets(d,"closure")),set(solver.targets(d,"quotient")),d)

    def test_prime_ranges_and_terminal_inverse(self):
        for start in (3,5,99,583,81001):
            brute=[p for p in range(start,start+1000,2) if solver.factors(p)==(p,)]
            self.assertEqual(list(solver.prime_bases(start,start+1000)),brute)
        for e in range(2,45):
            for p in (2,3,17,211):
                self.assertEqual(solver.terminal_base(solver.weighted(p,e),e),p)

    def test_nonprimes_are_not_certified(self):
        for n in (1,4,25,561,3215031751,3317044064679887385961981):
            self.assertFalse(solver.certified_prime(n))

    def test_denominator_support_bound(self):
        # A real three-slot branch at D=12,420. Two coprime nonsquare
        # composite factors require at least four bases of exponent ≤2.
        prefix=((47,14),(490999941736485923704801,2),(31013,22))
        left=120540471392616285857593713991045225260003126401
        right=1248886946256413820756169877062158015532163352406699697344271763862834462710605033977094426471940367
        self.assertTrue(solver.excess_support(left*right,prefix,(1,1,2)))
        for prime,exp in ((47,14),(31013,22)):
            for bound in (1,2,3,6):
                data=solver.weighted(prime,exp).numerator
                parts=solver.factors(data) if data<1000000 else (3,5,11,17)
                forced=prod(p**bound for p in parts)
                self.assertFalse(solver.excess_support(forced,((prime,exp),),(bound,)*len(parts)))

    def test_two_prime_windows_preserve_both_exponent_orders(self):
        for p,q in ((3,5),(13,71),(101,3001),(257,65537)):
            for e,f in ((1,1),(2,5),(5,2),(4,2)):
                ratio=solver.weighted(p,e)*solver.weighted(q,f)
                den=ratio.denominator
                F=den//solver.gcd(den,(e+1)*(f+1))
                upper=solver.first_false(3,lambda n: solver.weighted(n,e)*solver.weighted(n,f)>=ratio)
                windows=solver.two_prime_windows(tuple(sorted((e,f))),ratio,3,upper,F)
                self.assertTrue(any((a,b)==(e,f) and lo<=p<hi for a,b,lo,hi in windows))

    def test_optional_factor_acceleration_preserves_results(self):
        plain=solver.FACTOR
        try:
            solver.FACTOR=None
            solver.proposed_factors.cache_clear()
            solver.certified_prime.cache_clear()
            reference=solver.search(256)
        finally:
            solver.FACTOR=plain
            solver.proposed_factors.cache_clear()
            solver.certified_prime.cache_clear()
        result=solver.search(256)
        self.assertEqual(reference["resonances"],result["resonances"])
        self.assertEqual(reference["Euler product and exponent patterns"],result["Euler product and exponent patterns"])


if __name__=="__main__":
    main()
