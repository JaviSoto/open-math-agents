# A Bernoulli criterion for Meštrović’s quartic power-sum conjecture

Write $S_e(m)=\sum_{a=1}^{m-1}a^e$, and write $\operatorname{num} B_j$ for the numerator of the Bernoulli number in lowest terms. For **every positive integer** $n$,

$$
n^4\mid S_{n-2}(n)
\quad\Longleftrightarrow\quad n\text{ is odd and }n^2\mid\operatorname{num} B_{n-3}.
$$

The indices at $n=1$ use natural subtraction, as in the formal statement. The conjecture concerns $n>1$. For prime $n$, the criterion follows from [Meštrović, equation (19)](https://cs.uwaterloo.ca/journals/JIS/VOL17/Mestrovic/mes4.pdf). Here the criterion includes arbitrary composites and repeated factors.

For the even-power step in the argument, [Kellner, Proposition 8.5](https://arxiv.org/pdf/math/0409223#page=36), had already proved that $m^{r+1}\mid S_e(m)$ if and only if $m^r\mid\operatorname{num}B_e$ for positive even $e$, positive $m$, and $r=1,2$. The original exponent $n-2$ here is odd when $n$ is odd. Our verification includes that odd-power step, the corresponding higher-order tests at prime divisors, and an independent formal derivation of the Bernoulli criterion used below.

An explicit computation using published irregular-index data gives two consequences for [OEIS A284760](https://oeis.org/A284760): **there is no counterexample for $1<n\le10^{11}$**, and **a composite counterexample must be at least $400,315,058,243$**. More generally, no integer whose prime divisors are all below $63,917,461$ is a counterexample. The computation and its coverage are described below. The full conjecture remains open. The neighbouring [cubic conjecture A284759](https://github.com/lefttosolve2/open-math-agents/pull/30424) has a different answer.

## Why the numerator is decisive

For even $n$ and a positive even exponent, the sum already fails divisibility by $n$. When $4\mid n$, expand the terms $a$ and $a+n/2$ modulo $n$: the square of the increment and the linear term both vanish, so halving $n$ preserves the obstruction. When $n=2m$ with $m$ odd, exactly $m$ terms are odd. The case $n=2$ is immediate.

Now let $n$ be odd, $e=n-3$, and $p\mid n$ prime. For a counterexample, reflection of the original odd-power sum modulo $n^3$, followed by expansion in complete residue blocks, gives $p^2\mid S_e(p)$. This works for repeated prime factors as well. The case $e\equiv0\pmod{p-1}$ is excluded by summing $1$ over the nonzero residues.

For $p\ge5$, the case $e\equiv2\pmod{p-1}$ is also impossible. Double the representatives $i=0,\ldots,p-1$, writing $2i=r_i+p t_i$, $0\le r_i<p$. Comparing the two permuted sums modulo $p^2$ gives $\sum t_i r_i^{e-1}\equiv0\pmod p$, since $p\nmid e$. If $e\equiv2$, this sum reduces to $1+3+\cdots+(p-2)=((p-1)/2)^2\not\equiv0\pmod p$.

Apply Faulhaber’s identity for $S_{n-2}(n)$ after division by $n^4$. Up to the denominator $n-1$, which is a unit at $p$, the only potentially nonintegral term at $p$ is

$$\binom{n-1}{2}\,\frac{B_{n-3}}{n^2}.$$

The term at $B_{n-5}$ is integral because $p-1\nmid n-5$; earlier terms carry enough powers of $n$ by von Staudt–Clausen, and odd Bernoulli numbers above index one vanish. The displayed binomial coefficient is a unit for odd $p\mid n$. Thus $p^{2v_p(n)}$ divides the numerator at every such $p$. The small cases $3,5$ are excluded as well.

Conversely, suppose $n^2\mid\operatorname{num} B_e$. An index divisible by $p-1$ is excluded by von Staudt–Clausen. Applying Faulhaber to $S_e(p)/p^2$ gives an integer at $p$: even the $B_{e-2}$ term still carries one power of $p$ to clear its denominator. The same doubling argument now excludes $e\equiv2$. The preceding expansion of the original sum has all its terms integral at every prime of $n$, giving divisibility by $n^4$. This proves the reverse implication without assuming a general Kummer congruence.

## Two short rows per irregular index

Assume an odd counterexample and $p\ge7$ dividing it. The same Faulhaber calculation one order further at $p$ gives $p^3\mid S_e(p)$: $B_e/p^2$ is integral and so is $B_{e-2}$. Let $h=(p-1)/2$ and $H_j=\sum_{a=1}^h a^j$. Expand $S_e(p)$ two ways modulo $p^3$, first by pairing $a,p-a$ and then by pairing $2a,p-2a$. The quadratic terms vanish because $H_{e-2}\equiv0\pmod p$ (its doubled complete sum vanishes and $p-1\nmid e-2$). Eliminating $H_e$ gives

$$H_{e-1}\equiv0\pmod{p^2}.$$

Put $k=e\bmod(p-1)$. It is a positive even irregular index: $p\mid\operatorname{num} B_e$, $p\nmid e$, and the first [Kummer congruence](https://arxiv.org/abs/math/0409223) transfers divisibility to $B_k/k$. Write $e=k+(p-1)y$. Since $e\equiv-3\pmod p$, one has $y\equiv k+3\pmod p$. For each unit $a$, $a^{p-1}-1$ is a multiple of $p$, so powers of $a^{p-1}$ are affine in $y$ modulo $p^2$. It follows that the two auxiliary values recorded in the published tables,

$$s=(H_{k-1}\bmod p^2)/p,\qquad t=(H_{p+k-2}\bmod p^2)/p,$$

must satisfy $s+(k+3)(t-s)\equiv0\pmod p$. This uses the same data as the authors’ cyclotomic-invariant test with a different coefficient, forced by $p\mid n$.

## The computation and its coverage

We scanned the [Buhler–Harvey table and its published field definitions](https://people.reed.edu/~jpb/bernoulli/), companion to [*Irregular primes to 163 million*](https://arxiv.org/abs/0912.2121). All 4,578,239 recorded irregular pairs were tested. The uncompressed file matches the authors’ MD5. It contains 9,163,831 prime records but only 9,099,631 distinct primes. Comparing against an independent sieve, the first missing prime is $63,917,461$. The uninterrupted coverage used here ends immediately before that prime.

Only four recorded pairs pass the half-row test. For a final check take $a=k+(p-1)(k+3)$ and $d=p(p-1)$:

| $p$ | $k$ | $s$ | $t$ | $S_a(p)/p^2\bmod p$ | $S_{a+d}(p)/p^2\bmod p$ |
|---:|---:|---:|---:|---:|---:|
| 6,263 | 3,286 | 4,830 | 624 | 0 | 0 |
| 130,811 | 52,324 | 0 | 0 | 62,424 | 62,424 |
| 599,479 | 359,568 | 0 | 0 | 435,791 | 435,791 |
| 2,010,401 | 1,234,960 | 0 | 0 | 889,857 | 889,857 |

For units $i$, $i^d-1$ is divisible by $p^2$, so $S_{a+jd}(p)$ is affine in $j$ modulo $p^3$. Equal entries in a row cover every exponent in that class, including smaller nonnegative exponents by periodicity. The last three rows therefore contradict the necessary complete-sum test. In the remaining row $p=6263$, a pure power of $p$ would have $n\equiv1\pmod{p-1}$ and $e\equiv6260$, not $3286$. Therefore every counterexample has a prime factor at least $63,917,461$. Its smallest factor is at least $6263$, so a composite counterexample is at least their product.

For prime inputs up to $10^{11}$, [Booker, Hathi, Mossinghoff and Trudgian](https://arxiv.org/abs/2101.11157) established that only $16843$ and $2124679$ divide $\operatorname{num} B_{p-3}$. Both are inside the uninterrupted table range and both fail the quartic test. This supplies the prime part of the stated $10^{11}$ bound.

At $6263$ one can also rule out repeated factors. If $p^2\mid n$, the exponent $e$ equals $129011580838$ modulo $p^2(p-1)$. Write $u=129011580838$. Faulhaber expansion gives $6pB_u\equiv 6S_u(p)-u(u-1)p^2S_{u-2}(p)\pmod{p^4}$. The right side is $4847p^3\pmod{p^4}$, so $p^3\nmid\operatorname{num} B_u$. Order-three Kummer congruence transfers this obstruction from $u$ to $e$; both indices are prime to $p$. Hence $6263$ can occur only once in a counterexample.

## Reproduction

[ThirdOrderOriginal284760.lean](ThirdOrderOriginal284760.lean) contains the general equivalence, complete-row test and two-half-row relation. It imports Mathlib only and reports the axioms of each result. Those general implications do not depend on a database. The numerical bounds also use the published regular/irregular classification and the external computations explicitly identified above; the database is not encoded in the Lean kernel.

Run [irregular_rows_284760.py](irregular_rows_284760.py) to download, checksum and scan the published table; pass `--gzip /path/to/To163.gz` to reuse a copy. [third_order_rows_284760.py](third_order_rows_284760.py) recomputes both complete residues in each of the four rows and the repeated-factor digit with integer arithmetic, without the table.
