# No equality when the smaller odd prime is eleven

For every prime \(q>11\) and all \(k\ge0\), \(e,f\ge1\), the [A245212](https://oeis.org/A245212) divisor equality fails at \(2^k11^e q^f\). Together with [the cases through seven](seven-moving-pair-245212.md), a solution with precisely two distinct odd primes must therefore have both at least 13.

The [standalone Lean proof](Least11PairResearch245212.lean) starts from the original OEIS declaration. With the project's pinned toolchain, run `lake env lean Least11PairResearch245212.lean`; the theorem is `OMA.Least11Pair245212.no_pair`. Its audit lists only `propext`, `Classical.choice` and `Quot.sound`.

The reciprocal bound gives \(k<22\). For each remaining dyadic exponent the weighted divisor sum gives either a finite list of possible larger primes and a bound on the smaller exponent, or a bound on eleven's exponent. For example, at \(k=9,q=101\) at least one exponent is at most 12,946. At \(k=10\) eleven's exponent is at most 2,047 while the larger prime remains unrestricted. In that case the cofactor gives a lower bound on the last base, hence an upper bound on its exponent; the leading digit then determines its base. Lean checks the cutoffs and the residual exact arithmetic. The [threshold generator](generate_least_pair_245212.py) and [independent integer sweep](fixed_dyadic_pairs_245212.py) are included for reproduction.
