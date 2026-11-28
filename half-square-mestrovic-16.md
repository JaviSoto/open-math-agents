# Meštrović's half-exponent conjecture and the second Bernoulli numerator

Write $S_e(n)=\sum_{a=1}^{n-1}a^e$. [Meštrović's Conjecture 16](https://cs.uwaterloo.ca/journals/JIS/VOL17/Mestrovic/mes4.pdf#page=9) says that $n^3\nmid S_{(n-1)/2}(n)$ whenever $n\ge5$ and $n\equiv1\pmod4$. We prove the following exact reformulation:

$$\boxed{\quad n^3\mid S_{(n-1)/2}(n)\quad\Longleftrightarrow\quad
n^2\mid\operatorname{num} B_{(n-1)/2}.\quad}$$

Here $\operatorname{num}$ is the reduced numerator. This holds without assuming that $n$ is prime or squarefree. With the published irregular-pair tables, the reformulation excludes every $n<126,701,535,232$. The conjecture for all $n$ remains open.

The equivalence itself is a specialization of [Kellner, Proposition 8.5](https://arxiv.org/pdf/math/0409223#page=36): for every positive even $e$ and positive $m$, one has $m^{r+1}\mid S_e(m)$ exactly when $m^r\mid\operatorname{num}B_e$, for $r=1,2$. Take $e=(n-1)/2$, $m=n$, $r=2$. We give an independent Lean proof and use it, together with the additional local half-sum test below, to obtain the numerical exclusion.

## The equivalence

Set $e=(n-1)/2$, so $e$ is even and $2e+1=n$. The input $n=5$ is immediate. Otherwise $e\ge4$. For each prime $p\mid n$, both $e$ and $e+1$ are units modulo $p$. Through the first two powers of $n$, Faulhaber's formula and von Staudt–Clausen give

$$n^2\mid S_e(n)\quad\Longleftrightarrow\quad n\mid\operatorname{num}B_e.$$

Thus either side of the boxed claim implies $n\mid\operatorname{num}B_e$. Fix $p\mid n$. Von Staudt–Clausen shows $p-1\nmid e$; in particular $p\ne3$. We also have $p-1\nmid e-2$. Indeed the preceding square test at $n=p$ (with the same exponent $e$) gives $p^2\mid S_e(p)$. Alternatively, the first Kummer congruence would transfer $p\mid B_e/e$ at index $2\bmod(p-1)$ to $p\mid B_2/2=1/12$, which is impossible. The Lean proof uses a direct permutation by doubling modulo $p^2$.

Consequently $B_{e-2}$ is $p$-integral. In the expansion of $S_e(n)/n^3$, the final even Bernoulli term is $B_e/n^2$. The preceding even term is $e(e-1)B_{e-2}/6$ and hence is $p$-integral. All earlier terms retain a factor of $n$ to clear the possible denominator $p$ of their Bernoulli number. Comparing integrality at all $p\mid n$ proves the boxed statement.

## Which small primes could occur?

Put $k=e\bmod(p-1)$. For a counterexample, $k$ is an irregular index by the first Kummer congruence, since $p\nmid e$. No irregular index occurs at $p=5$. At $p\ge7$, applying the same expansion at the upper limit $p$ shows $p^3\mid S_e(p)$. Let $H_j=\sum_{a=1}^{(p-1)/2}a^j$. Expanding $S_e(p)$ through quadratic order by pairing $a,p-a$ and $2a,p-2a$, and eliminating $H_e$, yields $p^2\mid H_{e-1}$. The quadratic terms vanish because $p-1\nmid e-2$. This is the same pair of identities used in the [quartic problem](https://github.com/JaviSoto/open-math-agents/blob/b90d02b716198c7703a21a6e539e5bc3f4f931d8/quartic-bernoulli-284760.md), but the exponent imposes a different next digit.

Write $e=k+(p-1)y$. Then $2e+1\equiv0\pmod p$ gives $y\equiv k+1/2\pmod p$. The [Buhler–Harvey table](https://people.reed.edu/~jpb/bernoulli/) records $s=(H_{k-1}\bmod p^2)/p$ and $t=(H_{k+p-2}\bmod p^2)/p$. Since $(a^{p-1}-1)^2\equiv0\pmod{p^2}$ for units $a$, $H_{e-1}$ is affine in $y$ modulo $p^2$. The required relation is

$$2s+(2k+1)(t-s)\equiv0\pmod p.$$

Of 4,578,239 irregular-index records, five pass. In this table $a=k+(p-1)y_0$ with $0\le y_0<p$ the compatible residue, and $d=p(p-1)$.

| $p$ | $k$ | $s$ | $t$ | $S_a(p)/p^2\bmod p$ | $S_{a+d}(p)/p^2\bmod p$ |
|---:|---:|---:|---:|---:|---:|
| 59 | 44 | 11 | 26 | 0 | 0 |
| 379 | 174 | 44 | 148 | 0 | 0 |
| 130811 | 52324 | 0 | 0 | 8789 | 8789 |
| 599479 | 359568 | 0 | 0 | 180601 | 180601 |
| 2010401 | 1234960 | 0 | 0 | 1365626 | 1365626 |

The map $j\mapsto S_{a+jd}(p)$ is affine modulo $p^3$ because $x^d\equiv1\pmod{p^2}$ for each unit $x$. Thus the last three rows cannot occur. As in the quartic audit, the historical table contains repeated prime records (first duplicate $62,855,957$) and is first missing a prime at $M=63,917,461$. We use its complete range **only for $p<M$**.

Neither surviving prime can occur with multiplicity two. If $p^2\mid n$, then $2e+1\equiv0\pmod{p^2}$ fixes $e$ modulo $p^2(p-1)$. Choose the representative $u=k+(p-1)y$ with $y\equiv(2k+1)(p+1)/2\pmod{p^2}$. The representatives are $154904$ and $25065354$, respectively. Faulhaber at $p$ gives

$$6pB_u\equiv6 S_u(p)-u(u-1)p^2S_{u-2}(p)\pmod{p^4}.$$

Here $B_{u-2}$ is $p$-integral, and $S_{u-2}(p)\equiv pB_{u-2}\pmod{p^2}$; the exponents $u\equiv-1/2\pmod p$ avoid the exceptional small indices. The right-hand side is $33p^3$ modulo $p^4$ at $59$, and $99p^3$ at $379$. [Order-three Kummer congruence](https://arxiv.org/abs/math/0409223) transfers the nonzero valuation digit of $B_u/u$ to $B_e/e$, so $p^3\nmid\operatorname{num}B_e$. This contradicts $n^2\mid\operatorname{num}B_e$ when $p^2\mid n$.

The only possible prime factors below $M$ are therefore $59$ and $379$, each at most once. Neither alone is $1\bmod4$, and their product has $e\equiv218\pmod{378}$, not the required $174$. At least one prime factor is $\ge M$.

## Beyond the first table

If a composite counterexample satisfies $n<59\cdot2^{31}$, it has exactly one prime factor $q\ge M$, counted with multiplicity, since $M^2>59\cdot2^{31}$. Thus $n=mq$ with $m\in\{59,379,22361\}$ and $M\le q<2^{31}$. Its irregular index at $q$ would have to equal

$$\frac{q+m-2}{2}=\frac{mq-1}{2}\bmod(q-1).$$

The [Hart–Harvey–Ong table](https://arxiv.org/abs/1605.02398) has **no row of any of those three shapes** in this range. Our scan checked the uncompressed MD5 supplied in the authors' archive, strict ordering of all 105,097,564 odd-prime rows, final prime $2147483647$, and the full index-of-irregularity histogram printed in their Table 2.

For prime $n=p$, the boxed condition implies $p\mid\operatorname{num}B_{(p-1)/2}$, the classical Bernoulli form of an Ankeny–Artin–Chowla exception. [Van der Poorten, te Riele and Williams](https://doi.org/10.1090/S0025-5718-02-01527-2) excluded such primes through $2\cdot10^{11}$; see also the [verification history](https://arxiv.org/abs/2410.21864). Their range includes $59\cdot2^{31}=126,701,535,232$. Reinhart's later prime $331914313984493$ is an exception to the ordinary AAC conjecture; one factor of $p$ in the Bernoulli numerator is insufficient to settle Conjecture 16 at that prime.

## Reproduction

[ConjectureSixteenOriginal.lean](ConjectureSixteenOriginal.lean) imports only Mathlib. Run `lake env lean /absolute/path/to/ConjectureSixteenOriginal.lean` in the LeftToSolve pinned checkout. Its final theorems are the equivalence (`OMA.ConjectureSixteen.original`) and the two-half-row congruence at every eligible prime (`OMA.ConjectureSixteen.half_row`).

For the historical table, run `python3 half_index_screen_16.py To163.gz` using the [published gzip](https://people.reed.edu/~jpb/bernoulli/To163.gz). For the large-cofactor computation, run `python3 cofactor_indices_mestrovic.py`; it streams [the authors' archive](https://web.maths.unsw.edu.au/~davidharvey/research/twobillion.tar.bz2), or accepts a local copy via `--archive`. [First scan](half_index_screen_16.py) · [Second scan](cofactor_indices_mestrovic.py). The numerical bound uses these separately reproducible computations and the cited published results; the two general Lean statements do not depend on the tables.
