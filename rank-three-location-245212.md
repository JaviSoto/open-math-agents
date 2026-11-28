# What remains of the three-odd-prime case of A245212

Let \(n\) be a positive integer with exactly three **distinct odd prime divisors**. If it satisfies \(W(n)+\sigma(n)=2n\tau(n)\), then:

* \(32\mid n\), and neither 3 nor 5 divides \(n\).
* If \(7\mid n\), the power of two in \(n\) is exactly **32 or 64**. In particular no multiple of 896 with exactly three distinct odd prime divisors can solve the equation.

The prime bases and exponents are otherwise unrestricted. These conditions narrow the [finite but impractically large rank-three search](three-odd-absolute-245212.md). They do not exclude every rank-three integer.

For the first assertion, the [multiple-of-five theorem](rank-three-five-complete-245212.md) and the multiple-of-three theorem leave three primes at least seven. At dyadic exponent four, the Euler bound reduces the possible first two primes to seven pairs. Two pairs allow the last prime to be arbitrarily large; the others have 298 possible triples in total. Each of those cases was eliminated with the exponents unrestricted. The [dyadic-exponent-four proof](rank-three-sixteen-large-245212.md) documents the finite and infinite families separately. Results at dyadic exponents zero through three finish the argument.

For the second assertion, if \(k=\nu_2(n)\ge7\) and \(7^a\parallel n\), the normalized weight of \(2^k7^a\) gives only fifteen candidate pairs: at \(k=7\) the exponent \(a\) is at most 6; at 8 it is at most 3; at 9 it is at most 2; at 10 through 13 it is 1. All larger \(k\) are impossible. For each candidate the middle prime has an explicit upper bound; the last prime and both remaining exponents are covered without assuming upper limits on the input.

The [original-input theorem](RankThreeLocation245212.lean) is `OMA.RankThreeLocation245212.original`. The [entire source archive](rank-three-location-245212.tar.gz) includes all 1,325 modules, hashes, and a from-source replay command for the pinned Formal Conjectures revision `9097e2f90e66d2f6244209cb1c07f7120d17ec53`. Compile the standalone [dyadic order four proof](RankThreeSixteenLargeResearch245212.lean) separately with `lake env lean /path/to/RankThreeSixteenLargeResearch245212.lean`.
