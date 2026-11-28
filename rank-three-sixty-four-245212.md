# A three-odd-prime counterexample must be divisible by 64

For a positive integer \(n\) with exactly three distinct odd prime factors, the OEIS A245212 equality implies:

* \(64\mid n\), and neither 3 nor 5 divides \(n\).
* If \(7\mid n\), then \(\nu_2(n)=6\) and \(49\le\nu_7(n)\le127\). In particular \(64\cdot7^{49}\mid n\) in this case. No bound on either of the remaining primes or their exponents is assumed.

The [previous location theorem](rank-three-location-245212.md) left open \(\nu_2(n)=5\). At this dyadic order there are eight prime pairs with an unrestricted last prime and 665 further triples. The [order-five proof](rank-three-thirty-two-large-245212.md) excludes them all. It has also been assembled as a [single original-import source](RankThreeThirtyTwoLargeResearch245212.lean).

If seven occurs, write \(n=64\cdot7^a p^b q^c\) with \(7<p<q\). The normalized weight of \(64\cdot7^{128}\) already exceeds the allowed prefix weight, giving \(a\le127\). At each of the first 48 values of \(a\) the prefix moments bound \(p\). The remaining last prime and both variable exponents are treated by the prime and exponent certificates; simply searching to a numerical bound on \(n\) would not suffice.

The [full source archive](rank-three-seven-range-245212.tar.gz) contains 1,838 Lean modules, their hashes and the replay script. Extract it and run `lake env python3 /path/to/RankThreeSevenRange245212/lean_source_bundle_245212.py --workers 4` from the Formal Conjectures checkout at `9097e2f90e66d2f6244209cb1c07f7120d17ec53`. The final theorem on the original input is `OMA.RankThreeSevenRange245212.original`. This is a necessary condition, not an assertion that an input in the remaining interval actually works.
