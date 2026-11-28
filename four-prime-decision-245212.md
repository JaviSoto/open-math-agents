# An effective decision for the four-odd-prime branch of OEIS A245212

For a positive integer $n$, set $W(n)=\sum_{d\mid n}d\,\tau(d)$, where $\tau$ counts positive divisors. The [OEIS A245212](https://oeis.org/A245212) equality is $W(n)+\sigma(n)=2n\tau(n)$.

**Prime bound.** If an odd solution has at most four distinct prime factors, each is smaller than $10^{18}$. In the remaining four-prime case, write the support in order as $3,p,q,r$; then $p=5$ or $7$, $q\le31$, and $r<10^{18}$. These estimates hold for all positive exponents: they do not arise from checking numbers up to a cutoff. The formal prime bound is `OMA.Decision245212.prime_bound` in **DecisionResearch245212.lean**.

The proof first bounds the product of the factors $p/(p-1)$ from below by 2. If the largest prime is at least $10^{18}$, the first three primes must then be $3,5,q$, with $q=7,11,13$. At each of these three prefixes, consider intervals of positive exponents. For a putative large fourth prime, exact rational comparisons bound its exponent above and below, after which integer divisibility tests eliminate the possible completions. Lean checks the exhaustive splits and the arithmetic at their leaves. The verifier does not rely on primality testing of a large candidate.

**Exponents.** For any given set of odd primes, `OMA.Effective245212.search_correct` proves that a terminating Boolean test detects the existence of positive exponents satisfying the normalized equality. One exponent at a time can be restricted to an effective finite interval. After selecting its value the recursion deletes that prime and incorporates its two normalized factors into two rational coefficients. In the exceptional case where the limiting coefficient equals 2, a separate argument controls the error; with a single remaining prime the equation is affine in its normalized divisor sum.

Combining the search with the prime bound yields a *particular* Boolean, `OMA.Decision245212.verdict`. The theorem `OMA.Decision245212.conditional` proves that `verdict = true` would settle the four-odd-prime branch with exponent of 3 at least two. The full Boolean has not been evaluated. The remaining problem is distinct from the already proved prime bound and the soundness and completeness of the exponent search.

## Verification

**DecisionResearch245212.lean** contains both proofs and all arithmetic certificates. It imports only `FormalConjectures.OEIS.«245212»`. From the project's pinned `formal-conjectures` checkout, ensure the imported module is built (`lake build FormalConjectures.OEIS.«245212»`), then run `lake env lean -j2 /absolute/path/to/DecisionResearch245212.lean`. The source does not require the current nested reduction or a third-party theorem about these prime supports.

For an independent arithmetic replay put **large_last_245212.py** and **equal_power_245212.py** together; the latter supplies rational interval bounds. Run `python3 large_last_245212.py 1000000000000000000 q --exact` with `q` replaced by 7, 11, and 13. Use `--lean --block 384` for 7 and 11 and `--lean --block 1200` for 13 to emit the three Lean certificate sections. The Python replay is optional; Lean checks the certificates without it. The separate prime-power-height manuscript gives a quantitative height estimate and is not a dependency of either proved result here.
