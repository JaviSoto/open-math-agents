# A sharp small-factor classification of cubic semiprimes

For primes $p\le q$ with $p\le157$, the product $n=pq$ satisfies
$n^3\mid\sum_{i=1}^{n-1} i^{n-2}$ **if and only if**
$p=157$ and $q=1{,}569{,}473$. There is no upper bound on $q$. This
proves, in particular, that 157 is the smallest prime occurring in a
*semiprime* counterexample to Meštrović's Conjecture 12. A product of
three primes [can have prime factor 37](power-product-census.md).

Any possible $p<101$ is excluded by the [earlier semiprime proof](power-product-census.md).
For $101\le p\le157$, a finite power-sum test at $p$ leaves five primes:

| $p$ | Permitted $(n-3)\bmod (p-1)$ | Bernoulli number restricting $q$ |
|---:|---|---|
| 101 | 68 | $B_{98}$ |
| 103 | 24 | $B_{100}$ |
| 131 | 22 | $B_{128}$ |
| 149 | 130 | $B_{146}$ |
| 157 | 62 or 110 | $B_{154}$ |

None of these rows allows $p=q$. For $q>p$, our [cofactor theorem](cubic-tests-284759.md)
forces $q$ to divide the reduced numerator of the indicated Bernoulli number.
Lean computes these five numerators by the Bernoulli recurrence and checks
their complete prime factorizations, including the 85-digit factor of
$\operatorname{num} B_{154}$, by recursive Lucas certificates. Substituting
the prime divisors into the middle column leaves only $q=1{,}569{,}473$
at $p=157$, with index 110. The [proof of the positive example](least-cubic-power-sum.md)
checks the original sum.

[Complete 25-file Lean archive](cubic-sharp-semiprimes-284759.tar.gz):
from the pinned [Formal Conjectures checkout](https://github.com/google-deepmind/formal-conjectures/tree/9097e2f90e66d2f6244209cb1c07f7120d17ec53),
run `lake env python3 /path/to/lean_source_bundle_245212.py --archive /path/to/cubic-sharp-semiprimes-284759.tar.gz --workers 4`.
The final theorem is `OMA.CubicSharpSemiprimes284759.classify`. The archive contains
the numerical certificates; replay does not contact a factor database or require
factoring software.
