# A245212 with few odd divisors

Let $n=2^k m>0$ with $m$ odd. If the odd part has **at most 53 divisors**, the A245212 equality holds exactly when $m=1$. There is no bound here on $n$, on an odd prime divisor, or on the power of two supplied as input. The original search through 35 is described below; [the extension through 53](odd-tau36-245212.md) uses an additional integer-polynomial sieve. The final exclusions use exact computation; they are not a Lean proof of the full conjecture.

Write $W(s)=\sum_{d\mid s}d\tau(d)$. The sequence's definition says that the equality holds precisely when $W(n)+\sigma(n)=2n\tau(n)$. It holds at every power of two, including 1. For $m=p^e>1$, the [odd-divisor envelope](divisor-envelope-245212.md) gives $p-1=k+\delta$ with $\delta=(k+1)/(2^{k+1}-1)$. If $k=0$, this forces $p=2$; otherwise $0<\delta<1$ and the right side is not an integer. It remains to check at least two odd primes.

There is also a sieve involving the prime factors of the divisor count $t$ alone.
If every prime dividing $t$ is $1\bmod 2^j$ for some $j\ge1$, every local count
$e_i+1$ has the same congruence. Thus $m$ is a $2^j$-th power and equality
forces $t\equiv1\bmod 2^{j+1}$. In particular, an odd prime power $t=p^s$
requires **even** $s$, for every odd prime $p$. Both statements are
[formally proved from the original equality](CountPrimeLayer245212.lean).

**All divisor counts, not just those through 35.** If $\tau(m)$ is odd at any solution, then $\tau(m)\equiv1\pmod8$. The [Lean theorem](OddCountResidue245212.lean) starts with the original equality and does not call the finite search below. Odd divisor count makes $m$ a square, so the [dyadic power theorem](DyadicResearch245212.lean) gives $m=v^4$ and the number $\Omega(v)$ of prime factors counted with multiplicity is even. Multiplying the factors $1+4e$ of $\tau(v^4)$ then gives $1+4\Omega(v)\equiv1\pmod8$. Thus every odd divisor count congruent to 3, 5 or 7 modulo 8 is impossible, with no size bound.

More generally the same Lean file proves `power_count`: whenever the odd part of a solution is a $2^j$-th power with $j\ge1$, its divisor count is $1\bmod 2^{j+1}$. Write $m=v^{2^j}$. The dyadic theorem gives even $\Omega(v)$, and the local divisor counts have product $1+2^j\Omega(v)\pmod{2^{j+1}}$. The modulo-eight result above uses the additional fact that odd divisor count forces a fourth power at a solution.

If $\tau(m)$ is **even**, then some prime $\ell\equiv3\pmod4$ divides $\tau(m)$. In particular it cannot be a positive power of two. For the [Lean proof](EvenCountResidue245212.lean), some prime of $m$ must have odd exponent, since $\tau(m)=\prod(e+1)$ is even. The [exponent obstruction](ParityResearch245212.lean) then gives a (different) exponent $e\equiv2\pmod4$. Its factor $e+1\equiv3\pmod4$ must have at least one prime factor congruent to 3 modulo 4. Both the odd and even conclusions apply to arbitrary positive $n$, independent of the finite search.

## A finite list for each exponent pattern

Set $t=\tau(m)$. Enumerate all **ordered** exponent lists $e_1,\ldots,e_s\ge1$ satisfying $\prod(e_i+1)=t$. Bases will be primes in strictly increasing order. We discard lists failing the [known divisibility](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1376) $2^s\mid\prod(e_i+2)$. If all exponents are even, the [square-to-fourth-power condition](dyadic-power-245212.md) also requires all of them to be divisible by four; the precise Lean theorem is `OMA.DyadicPower245212.square_root_is_square` in [DyadicResearch245212.lean](DyadicResearch245212.lean). The first three-base case left by these tests is $t=18$, with exponents $1,2,2$ in any order.

The [effective envelope](divisor-envelope-245212.md) bounds $2^k\le[4(k+2)t^2]^t$. Find the first $K\ge2t$ where this fails; test every $0\le k<K$. To see that no larger $k$ can work, put $z=1/(k+2)$. The binomial bound $(1+z)^t\le\sum_{j=0}^t(tz)^j<2$ applies since $tz<1/2$. Thus each increment doubles the left side and multiplies the right by less than two.

For fixed $k$, let $\gamma=k+\delta$. Anmol Sahu’s [dyadic inversion](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5390) gives the exact equation

$$
 (1+\gamma)t =
 \gamma \prod_i \frac{W(p_i^{e_i})}{p_i^{e_i}}+
        \prod_i \frac{\sigma(p_i^{e_i})}{p_i^{e_i}}.
$$

Both local ratios have positive coefficients as polynomials in $1/p$. Their constant terms are $e+1$ and 1. In particular the right side is strictly decreasing in each base for $e\ge1$, since $\gamma>0$.

After fixing any prefix of the primes, set all remaining bases to infinity (use the constant terms). If this value **equals or exceeds** the left side, discard the prefix: finite remaining primes make the expression strictly larger. Otherwise set all remaining bases to the same integer $x$. The expression decreases to the strict lower limit, so doubling then binary search finds the last integer where it **equals or exceeds** the target. The true next prime cannot exceed this integer: all later bases are at least this prime. Enumerate each prime up to that endpoint and greater than the previous prime. Including equality in the search is intentional. Every comparison is between products of positive integers after clearing denominators. This argument also gives a finite recursive algorithm at any fixed $t$; the running time is not uniform in $t$.

## Last prime and direct checks

Let $b$ be the cofactor including $2^k$ and the chosen odd prime powers. For the final prime $p$ with exponent $e$, set $T=b\tau(b)$, $A=W(b)$, $S=\sigma(b)$, $D=(e+1)(2T-A)-S$, and $B=eA+S$. The [leading-digit calculation](divisor-balance-245212.md) gives

$$
 Dp^e = \sum_{j=0}^{e-1}((j+1)A+S)p^j.
$$

Thus $D>0$; zero and negative values are excluded. For $e=1$, $p=B/D$ must be integral. For $e>1$, dividing by $p^{e-1}$ gives $B<pD<B+B/(p-1)$. Consequently $B/D<p<B/D+1$; an integral quotient leaves no candidate, and otherwise only $1+\lfloor B/D\rfloor$ can work. Finally $p\mid A+S$. For every candidate left, the program tests the **original equality** by multiplication of local moments, without relying on primality to discard an integer solution.

Run:

    python3 odd_divisor_count_245212.py --through 35 --audit

There are **31 ordered exponent profiles** after the exact reductions. The columns below distinguish generated candidates from prime bases:

| Odd-divisor count $t$ | Last-prime tests | Ordered integer candidates | Pass $p\mid A+S$ | Prime candidates | Equalities |
|---|---:|---:|---:|---:|---:|
| 2–26 | 6,873,189 | 2,646,221 | 3,407 | 198 | 0 |
| 27–35 | 132,090,693 | 45,095,205 | 16,553 | 1,138 | 0 |
| **All** | **138,963,882** | **47,741,426** | **19,960** | **1,336** | **0** |

The largest endpoint for a nonfinal prime was 45,663,435, and the largest final digit to pass divisibility was 13,641,069. In audit mode the program proves primality by trial division and independently evaluates every one of the 1,336 original integers: it lists the divisors of the odd part, groups the full divisor sum by the exponent of two and compares $a(n)-\sigma(n)$ with the multiplicative calculation. The two rows can also be reproduced separately with `--through 26 --audit` and `--from 27 --through 35 --audit`.

For $t\le11$, only the two ordered exponents $(1,2),(2,1)$ at $t=6$ survive the stated elementary exclusions. The first impossible $k$ is 82. There are 2,496 final digit tests, 638 ordered digits, four divisible digits and one prime digit. Its input is $2^{42}\cdot31\cdot191^2=4{,}973{,}799{,}177{,}919{,}135{,}744$; the original difference $a(n)-\sigma(n)$ is $16{,}765{,}353{,}294{,}582{,}946$.

For context, [formal-conjectures issue #8382](https://github.com/google-deepmind/formal-conjectures/issues/8382) records earlier density-zero and totient results for A245212, and [#5390](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5390) gives the fixed-odd-cofactor inversion. These results concern the same original problem but do not assert the finite divisor-count conclusion above.
