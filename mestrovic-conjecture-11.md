# One composite counterexample to both parts of Meštrović's Conjecture 11

Let $S_e(n)=\sum_{a=1}^{n-1}a^e$ and let $B_j$ denote the Bernoulli numbers with $B_1=-1/2$. [Conjecture 11, p. 7, in Meštrović's 2014 paper](https://cs.uwaterloo.ca/journals/JIS/VOL17/Mestrovic/mes4.pdf#page=7) asserts that neither of the following congruences holds for any integer $n\ge2$:

$$S_n(n)\equiv\tfrac12 n^3 B_{n-1}\pmod{n^5},
\qquad S_{n-1}(n)\equiv nB_{n-1}\pmod{n^4}.$$

**Both hold for $n=409407431=59\cdot1559\cdot4451$.** The first also holds for every prime $p\ge5$. In particular, there is a short counterexample to the first assertion: $S_5(5)=1300$, $5^3 B_4/2=-25/12$, and the difference is $5^6/12$. For rational summands, congruence modulo $m$ means $m$ divides the numerator of the reduced difference.

## Why the same composite works twice

Suppose that $n\ge7$ is odd and every prime $p\mid n$ is at least $5$. Write $e=n-3$. We use two sufficient conditions:

1. If $p-1\nmid e$ for every $p\mid n$, the first congruence holds.
2. If $n\mid\operatorname{num}B_e$ and $p-1\nmid e-2$ for every $p\mid n$, the second congruence holds.

Here is the local calculation. Normalize each difference by its claimed modulus and fix a prime $p\mid n$. In Faulhaber's formula for $S_n(n)$ the highest nonzero Bernoulli term is exactly $n^3 B_{n-1}/2$. After subtracting it and dividing by $n^5$, the next even-indexed Bernoulli term is

$$\frac{(n-1)(n-2)}{24}\,B_e.$$

All earlier terms are $p$-integral. In fact, every $pB_i$ is $p$-integral by von Staudt–Clausen, those terms retain at least one factor of $n$ after division by $n^5$, and the denominator $n+1$ is prime to $p$. Odd-indexed Bernoulli numbers above $B_1$ vanish. Finally $B_e$ is $p$-integral when $p-1\nmid e$. This proves the first test and applies immediately to $n=p\ge7$.

For $S_{n-1}(n)$ the leading term is $nB_{n-1}$. After subtracting and dividing by $n^4$, the two next even-indexed terms are

$$\frac{(n-1)(n-2)}{6}\,\frac{B_e}{n}
\quad\text{and}\quad \binom{n}{5}B_{e-2}.$$

The first is $p$-integral because $n$ divides the reduced numerator of $B_e$; the second is $p$-integral when $p-1\nmid e-2$. Again all earlier terms retain at least one factor of $n$. Integrality at every $p\mid n$ proves divisibility of the reduced numerator by the entire modulus, including all prime multiplicities.

For the stated composite, the local indices are small:

| $p$ | $e\bmod(p-1)$ | $(e-2)\bmod(p-1)$ |
|---:|---:|---:|
| 59 | 44 | 42 |
| 1559 | 862 | 860 |
| 4451 | 2978 | 2976 |

The Bernoulli-numerator divisibility follows from the [certified cubic counterexample](https://github.com/lefttosolve2/open-math-agents/pull/30424): $n^3\mid S_{n-2}(n)$ at this same $n$. For odd $n\ge7$ the cubic condition is equivalent to $n\mid\operatorname{num}B_{n-3}$. The file below includes that equivalence and the explicit certificate for the three finite rows modulo $p^2$, so neither the proof nor its reproduction needs a Bernoulli table.

## Reproduce the result

[ConjectureElevenOriginal.lean](ConjectureElevenOriginal.lean) imports only Mathlib. In the LeftToSolve pinned Lean environment, run `lake env lean /absolute/path/to/ConjectureElevenOriginal.lean`. The final declarations `OMA.ConjectureElevenMestrovic.first_prime` and `OMA.ConjectureElevenMestrovic.composite` are the universal prime assertion and the simultaneous composite counterexample. The artifact includes the checked example $n=5$.

The result concerns the published paper's Conjecture **11**. The independently submitted [Meštrović Conjecture 12 disproof](https://github.com/lefttosolve2/open-math-agents/pull/30424) concerns $n^3\mid S_{n-2}(n)$; [Conjecture 13](https://github.com/JaviSoto/open-math-agents/blob/b90d02b716198c7703a21a6e539e5bc3f4f931d8/quartic-bernoulli-284760.md), with modulus $n^4$ and the same exponent $n-2$, remains open.
