# Four composite cubic counterexamples through 100 billion

For $S_e(n)=\sum_{a=1}^{n-1}a^e$, the only composite integers $2\le n\le 100{,}000{,}000{,}000$ for which $n^3\mid S_{n-2}(n)$ are:

| $n$ | Prime factors |
|---:|---|
| 246,407,261 | 157 × 1,569,473 |
| 409,407,431 | 59 × 1,559 × 4,451 |
| 564,458,189 | 5,309 × 106,321 |
| 7,708,886,483 | 75,079 × 102,677 |

This is a computational census. The [formal disproof of Conjecture 12](https://github.com/lefttosolve2/open-math-agents/pull/30424) and the [formal check of the least example](least-cubic-power-sum.md) do not require trusting the census or the irregular-prime table.

## Three general theorems

Write $\operatorname{num}B_j$ for the reduced numerator of a Bernoulli number. The [kernel-checked source archive](cubic-bernoulli-284759.tar.gz) proves:

1. For **all positive integers**, $n^3\mid S_{n-2}(n)$ if and only if $n$ is odd and $n\mid\operatorname{num}B_{n-3}$. At $n=1$ the empty sum is zero; truncated natural indices are used there and at $n=2$.
2. For **every** $n\equiv3\pmod4$, $n^3\mid S_{(n-1)/2}(n)$ if and only if $n\mid\operatorname{num}B_{(n-3)/2}$. This characterizes the test in [Meštrović's Conjecture 15](https://cs.uwaterloo.ca/journals/JIS/VOL17/Mestrovic/mes4.pdf); whether a composite can satisfy it remains open.
3. If $n=Pm$, $P$ is prime, and $7\le m<P$ is odd, passing the ordinary cubic test implies $P\mid\operatorname{num}B_{m-3}$. In particular, for each such fixed cofactor the possible large primes divide one fixed nonzero integer. No squarefreeness assumption is needed.

For the first two statements, reflecting $a$ to $n-a$ modulo $n^3$ reduces the odd-power test to a square-divisibility test at the preceding even exponent $e$. For every odd prime $p\mid n$, Faulhaber's identity makes $S_e(n)/n^2-B_e/n$ an integer at $p$: the lower terms have an extra factor $n$ to cancel any Bernoulli denominator. The factor $e+1$ is invertible at $p$. Combining the local tests gives ordinary numerator divisibility. For the third result, restrict the even power sum to one complete residue block modulo $P^2$. Multiplication by a nonzero residue permutes the block; its first-order carry transfers the vanishing test from $Pm-3$ back to $m-3$. A second application of the square-divisibility criterion gives the result.

The even-exponent square-divisibility step above is a specialization of Bernd Kellner’s [Proposition 8.5 (2007)](https://arxiv.org/pdf/math/0409223#page=36), which covers every positive even exponent and both the square and cube tests. Our proof checks this step independently in Lean; the reflection, cofactor restriction, and composite search use it to address the stated conjectures.

## How the census handles missing data

The [Buhler–Harvey table](https://people.reed.edu/~jpb/bernoulli/) has its first missing prime at 63,917,461. Below that cutoff, the program verifies the table's full uncompressed digest, checks coverage against its own prime sieve, and verifies that repeated rows agree on their irregular indices. For each largest prime $P$, the admissible cofactors run through explicit residue classes; small smooth cofactors are generated in factored form. Prime powers and nonsquarefree composites are included. The earlier [census](least-cubic-power-sum.md) explains the local index condition.

Above the cutoff the cofactor is at most 1,564. The program computes the exact $B_{m-3}$ by the integer tangent-number recurrence, checks it against the Bernoulli recurrence at selected indices, and tests every admissible candidate $P$ for divisibility and primality. It does **not** infer the missing table rows. Finally, it evaluates the original sum modulo each exact prime power dividing $n^3$. The extra index candidate $16{,}843^2$ fails this check.

Run `python3 cubic_census_284759.py To163.gz --bound 100000000000 --workers 5`. An independent split at **1,000,000** for the earlier two-billion range exercised the upper branch on the positive example with $P=1{,}569{,}473$ and reproduced all three composite hits. To replay the 14-module Lean proof from [the pinned Formal Conjectures checkout](https://github.com/google-deepmind/formal-conjectures/tree/9097e2f90e66d2f6244209cb1c07f7120d17ec53), run `lake env python3 /path/to/lean_source_bundle_245212.py --archive /path/to/cubic-bernoulli-284759.tar.gz --workers 3`. Its final theorem is `OMA.CubicTests284759.tests`.
