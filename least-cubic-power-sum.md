# The first composite counterexamples to Meštrović's cubic conjecture

The least composite found is **246,407,261 = 157 × 1,569,473**. Writing
$S_e(n)=\sum_{1\le x<n}x^e$, the [Lean proof](LeastCubicWitness284759.lean)
establishes both its compositeness and $n^3\mid S_{n-2}(n)$. It needs no
Bernoulli table or search assumption. The [LeftToSolve disproof](https://github.com/lefttosolve2/open-math-agents/pull/30424)
uses the distinct, three-prime example below.

We also ran an exhaustive **computational** census using the published
irregular-index data of Buhler and Harvey. Among composite $n$ from 2
through **2,000,000,000**, the only successes are:

| $n$ | Factorization |
|---:|---|
| 246,407,261 | 157 × 1,569,473 |
| 409,407,431 | 59 × 1,559 × 4,451 |
| 564,458,189 | 5,309 × 106,321 |

The fourth candidate surviving the index sieve, $16843^2=283686649$,
fails modulo $16843^6$. In particular the search includes repeated prime
factors. In the same range we find no composite counterexamples to
Conjecture 15 or 16 (the half-exponent questions). These bounded negative
results and the minimality claim rely on the index table and the search;
they are separate from the Lean certificate of the counterexample.

## Why the search is exhaustive

The numbering is from [Meštrović, JIS 17 (2014), article 14.8.4](https://cs.uwaterloo.ca/journals/JIS/VOL17/Mestrovic/mes4.pdf).
For Conjecture 12 on odd $n$, use $t=n-3$; for Conjecture 15 ($n=3\bmod4$)
use $t=(n-3)/2$; for Conjecture 16 ($n=1\bmod4$) use $t=(n-1)/2$.
In each case $t$ is even. The input 3 fails the original tests directly.
For the first two tests the original exponent is $t+1$, coprime to $n$.
The reflection congruence $2S_{t+1}(n)\equiv (t+1)n S_t(n)\pmod{n^3}$
shows $n^3\mid S_{t+1}(n)$ iff $n^2\mid S_t(n)$. For the last test
$n^3\mid S_t(n)$ already implies $n^2\mid S_t(n)$. Even $n$ cannot pass
Conjecture 12: for even positive exponent the Carlitz–von Staudt power-sum
congruence (Theorem 20 of the paper) has valuation $\nu_2(n)-1$ at 2.
The sum for $n=2$ is 1.

Let $p^a\parallel n$ be odd. In the three cases $p\nmid t+1$. Faulhaber's
formula, multiplied by $t+1$, shows
$S_t(n)\equiv nB_t\pmod{p^{2a}}$ in the $p$-adic numbers. Indeed the term
in $n^2$ has $B_{t-1}=0$ unless $t=2$, when its denominator is 2.
Every term in $n^j$ with $j\ge3$ has valuation at least $ja-1\ge2a$:
von Staudt–Clausen gives $v_p(B_i)\ge-1$. Thus a success forces
$v_p(B_t)\ge a$. In particular $p-1$ cannot divide $t$ (so $p=3$ is
impossible). For $p\ge5$, also $p\nmid t$ in all three tests. The
[Kummer congruence](https://arxiv.org/abs/math/0409223) now requires the
nonzero even index $k=t\bmod(p-1)$ to be irregular at $p$. Every prime
factor of a surviving composite is therefore at least 37.

Write $n=P m$ with $P$ the **largest** prime factor. Each irregular index
at $P$ determines one residue for $m$:

| Conjecture | Required cofactor residue |
|---|---|
| 12 | $m\equiv k+3\pmod{P-1}$ |
| 15 | $m\equiv 2k+4-P\pmod{2(P-1)}$ |
| 16 | $m\equiv 2k+2-P\pmod{2(P-1)}$ |

The half-exponent formulas use $P m\equiv m+(P-1)\pmod{2(P-1)}$ for odd
$m$. Enumerate that progression for $37\le m\le 2000000000/P$, factor
$m$, and check its prime indices too. The program checks that the table
has each prime through $54,054,054$ exactly once against its own sieve.
It then evaluates the **original** power sum modulo every $p^{3a}$ for
every survivor. For Conjecture 16 the only index candidate, $3737=37\cdot101$,
fails modulo both prime cubes; it is known to pass the square test.

## Certifying the small witness without summing millions of terms

At $p=157$ and $p=1569473$, the even exponent 246407258 reduces modulo
$p-1$ to 110 and 154, respectively. [The transfer proof](PowerSumIndexTransfer284759.lean)
permutes residues by multiplication by 2. If $r=(2x)\bmod p$ and
$c=\lfloor2x/p\rfloor$, expanding $(r+pc)^e$ modulo $p^2$ gives

$$ (2^e-1)S_e(p)\equiv ep\sum_{0\le x<p} c\,r^{e-1}\pmod{p^2}. $$

The sum on the right, modulo $p$, depends only on $e\bmod(p-1)$ for
$e>1$. Here the small exponents are units at their primes and $2^k-1$ is
also a unit. It suffices to prove that the rows at **110 and 154** vanish.
For each $k$, Lean checks an integer polynomial identity
$F(X+1)-F(X)=D X^k$, $\gcd(D,p)=1$, and $F(p)-F(0)\equiv0\bmod p^2$.
The sum telescopes. All coefficients and endpoints are kernel-checked;
the row length does not enter the calculation. Lifting these two rows
and reflecting the odd power sum gives the original cubic divisibility.

To reproduce the census, download [To163.gz from the authors](https://people.reed.edu/~jpb/bernoulli/)
and run `python3 mestrovic_composite_survey.py To163.gz --bound 2000000000 --verify`.
For the independent Lean replay, extract [the six-module archive](least-cubic-witness-284759.tar.gz).
From a Formal Conjectures checkout at `9097e2f90e66d2f6244209cb1c07f7120d17ec53`,
run `lake env python3 /path/to/LeastCubicWitness284759/lean_source_bundle_245212.py --workers 3`.
An independent run compiled all six sources and audited the original witness theorem.
