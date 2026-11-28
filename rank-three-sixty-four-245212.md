# A three-odd-prime counterexample must be divisible by 64

For a positive integer \(n\) with exactly three distinct odd prime factors, the OEIS A245212 equality implies:

* \(64\mid n\), and neither 3 nor 5 divides \(n\).
* Seven divides \(n\) **if and only if** \(\nu_2(n)=6\). When this happens, \(65\le\nu_7(n)\le127\). In particular \(64\cdot7^{65}\mid n\). No bound on either of the remaining primes or their exponents is assumed.

The [previous location theorem](rank-three-location-245212.md) left open \(\nu_2(n)=5\). At this dyadic order there are eight prime pairs with an unrestricted last prime and 665 further triples. The [order-five proof](rank-three-thirty-two-large-245212.md) excludes them all. It has also been assembled as a [single original-import source](RankThreeThirtyTwoLargeResearch245212.lean).

If seven occurs, write \(n=64\cdot7^a p^b q^c\) with \(7<p<q\). The normalized weight of \(64\cdot7^{128}\) already exceeds the allowed prefix weight, giving \(a\le127\). At each of the first 64 values of \(a\) the prefix moments bound \(p\). The remaining last prime and both variable exponents are treated by the prime and exponent certificates; searching to a numerical bound on \(n\) would not suffice. Conversely, at exact dyadic order six the [least-prime-at-least-eleven theorem](rank-three-sixty-four-large-245212.md) eliminates both unrestricted last-prime families and all 96 remaining supports, so seven must occur.

The [full source archive](rank-three-seven-iff-245212.tar.gz) contains 2,165 Lean modules, their hashes and the replay script. Extract it and run `lake env python3 /path/to/RankThreeSevenIff245212/lean_source_bundle_245212.py --workers 4` from the Formal Conjectures checkout at `9097e2f90e66d2f6244209cb1c07f7120d17ec53`. The final theorem on the original input is `OMA.RankThreeSevenIff245212.original`. The [order-six least-eleven proof](RankThreeSixtyFourLargeResearch245212.lean) was independently replayed as a single source against the original import. The full conjecture remains open.
