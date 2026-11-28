# No equality when the smaller of two odd primes is seven

For every prime \(q>7\), all \(k\ge0\), and all positive \(e,f\), the
[A245212 equality](https://oeis.org/A245212) fails at \(2^k7^e q^f\).
The [standalone proof](Least7PairResearch245212.lean) imports the original
OEIS declaration; its final theorem is `OMA.Least7Pair245212.no_pair`.
Run it with the pinned project's `lake env lean`. Its axiom audit lists only
`propext`, `Classical.choice` and `Quot.sound`.

The [dyadic exponent bound](two-odd-finiteness-245212.md) gives \(k<14\).
For \(k=0,1,2,3\) the Euler bound leaves no prime larger than seven.
For \(k=4\) only 11 and 13 are possible and one exponent is at most 6 and
12, respectively. For \(k=5\) the possibilities in order are
11, 13, 17, 19, 23, 29, 31 and 37; the corresponding smaller exponent is
at most 2, 3, 5, 6, 10, 19, 24 and 81. The reverse digit determines the
other exponent. For the remaining \(k=6,\ldots,13\), seven's own weighted
factor gives \(e\le127,6,3,2,1,1,1,1\), respectively. The last exponent
is then bounded by the cofactor moments, and the leading digit determines
the last prime. The kernel checks the cutoff inequalities and the exact
divisor balance in every case.

Together with the prior results for [three and five](five-moving-pair-245212.md),
a two-odd-prime counterexample must have smaller prime at least 11.
