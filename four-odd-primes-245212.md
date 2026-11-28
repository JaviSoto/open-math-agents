# An odd solution to OEIS A245212 needs at least five distinct primes

**Theorem (verified in Lean).** The only positive odd integer $n$ with at most four distinct prime divisors that satisfies
$$W(n)+\sigma(n)=2n\tau(n),\qquad W(n)=\sum_{d\mid n}d\tau(d),$$
is $n=1$. The prime multiplicities, the primes themselves, and $n$ are unrestricted in this statement. This settles the four-odd-prime branch of [Křížek's A245212 conjecture](https://oeis.org/A245212); it does not settle the full conjecture.

**[Download the complete Lean source](odd-four-lean-source.zip).** The theorem is `OMA.OddSupportClass245212.odd_four` in `src/OddFourComplete245212.lean`. It starts from the original OEIS definition in Formal Conjectures. The source archive includes every prime-support certificate and a replay script; it contains no precompiled proofs. The final axiom audit lists only `propext`, `Classical.choice`, and `Quot.sound`. The exact-arithmetic search below gives a separate check.

Extract the archive and, from the [pinned Formal Conjectures checkout](https://github.com/google-deepmind/formal-conjectures/tree/9097e2f90e66d2f6244209cb1c07f7120d17ec53), run:

```sh
lake build FormalConjectures.OEIS.245212
lake env python3 /path/to/extracted/verify.py
```

The first replay builds 499 Lean modules and can take hours; subsequent runs reuse unchanged results. Use `--jobs 1` to check one module at a time.

**Five or six primes.** Any odd solution greater than one with at most six distinct prime factors must be divisible by three. Otherwise its Euler product is at most the product for 5, 7, 11, 13, 17, 19, which is $323323/165888<2$. With exactly five primes and just one factor of three, the only possible prime support is **3, 5, 7, 11, 13**. If the largest prime were at least 17, the four remaining Euler factors would have product at most $1309/768<12/7$; the interval bound below with $x(3,1)=7/6$ and $y(3,1)=2/3$ then gives a strict contradiction. These [additional Lean corollaries](OddSixWithoutThree245212.lean) import the standalone three-prime file. The unrestricted five- and six-prime cases remain open.

On that last five-prime support, write $n=3\cdot 5^a7^b11^c13^d$. The [Lean theorem on exponents](FiveExponentBounds245212.lean) gives $a\ge18,\ b\ge12,\ c\ge7,\ d\ge6$. Consequently $n$ is divisible by $3\cdot5^{18}7^{12}11^7 13^6$, about $1.49\times10^{37}$. To see where the bounds come from, fix one of the four larger primes $p$, and write $C=\prod_{q\ne p,\,q>3} q/(q-1)$. The normalized sum is at most a weighted average of $(7/6)x(p,e)+(2/3)y(p,e)\le11/6$ and $(7/6)x(p,e)C$. The second endpoint therefore has to reach 2. Checking it at each indicated lower bound minus one, and using monotonicity in the exponent, excludes every smaller exponent. The Lean theorem takes the original OEIS equality as its hypothesis.

The same [Lean file](FiveExponentBounds245212.lean) shows that at least one exponent belongs to one of these short ranges: $18\le a\le71$, $12\le b\le47$, $7\le c\le27$, or $6\le d\le23$. In fact, already at $(72,48,28,24)$ the first product $(7/6)\prod x$ exceeds 2. Every $x$ increases with its exponent, and the second product is nonnegative. These ranges form 129 one-exponent cases.

### Five primes: the exponent of three cannot be one

Here the proof combines the above Lean results with a written bound and an exhaustive computation. **Any odd solution with exactly five distinct prime divisors must be divisible by nine.** The remaining case with $9\mid n$ is open.

Use the [general integer-rounding height bound](prime-power-height-245212.md) with $k=5$, $B=13$: the largest exponent is at most 7072. To reproduce the number, the offset is 4992 and the slope is 160. Starting from 6,553,600, the successive bounds are 8672, 7232 and 7072; a further iteration leaves 7072. The general-rank height argument is a written proof, not part of the rank-four Lean certificate.

If $p^e\parallel n$ and $m=n/p^e$, the original equality requires $W(m)\equiv(p-1)\sigma(m)\pmod {p^e}$. Indeed, modulo $p^e$, the geometric sum gives $(p-1)\sigma(p^e)\equiv-1$, and the weighted sum gives $(p-1)^2W(p^e)\equiv1$. For $n=3\cdot5^a7^b11^c13^d$ we can use the four constant moduli $5^{18},7^{12},11^7,13^6$, by the lower bounds proved above.

For each of the 129 cases, fix a second exponent anywhere in its allowed range up to 7072. Denote the two unfixed primes by $r,s$. The congruence at $r$ is independent of its own exponent: with our two fixed exponents, it is a condition only on the exponent of $s$. The congruence at $s$ similarly constrains only the exponent of $r$. If either congruence has no permitted exponent, the entire box is impossible. The four overlapping families account for 911,625 boxes. Only 13 pass the first congruence and none passes both.

| Prime assigned the short range | Boxes | Pass first congruence | Pass both |
|---|---:|---:|---:|
| 5 | 381,618 | 13 | 0 |
| 7 | 254,412 | 0 | 0 |
| 11 | 148,407 | 0 | 0 |
| 13 | 127,188 | 0 | 0 |

Two implementations independently rule out every box. The [standalone C++ replay](five_prime_replay_245212.cpp) uses the defining divisor sums by recurrence; it filters by a small modulus and then tests the full congruence directly, including zeros and noninvertible coefficients. Compile with a C++17 compiler supporting 128-bit integer multiplication: `c++ -std=c++17 -O2 five_prime_replay_245212.cpp -o /tmp/five-prime-replay && /tmp/five-prime-replay`. The [Python replay](five_prime_sieve_245212.py) instead uses a closed geometric formula and matches normalized residue pairs after removing common prime factors. Run it with each of the arguments 5, 7, 11, 13. This finite sieve has not been formalized in Lean.

### If the exponent at three is two

The [Lean support theorem](FiveSquareThree245212.lean) starts from the original equality. With exactly five odd primes and $3^2\parallel n$, the support must be $3,5,7,q,r$. There are just four possibilities for $q$:

| $q$ | Restriction on the last prime $r>q$ |
|---:|---|
| 11 | The cap argument gives no upper bound. |
| 13 | $r<190$, hence $r\le181$. |
| 17 | $r<41$, hence $r\le37$. |
| 19 | $r<33$, hence $r\le31$. |

Here $x(3,2)=34/27$ and $y(3,2)=13/27$. If the product of the four remaining prime caps is less than $27/17$, both endpoints of the interval bound are below 2. Applying this to the smallest possible primes beyond each proposed threshold gives the table; no upper bound on the exponents is used. These supports have not been excluded by this theorem.

**The $q=19$ row is impossible by an additional finite computation.** Its only possible last primes are $23,29,31$. As a result, if $3^2\parallel n$, the fourth prime of a five-prime solution can only be 11, 13, or 17.

For each of the three supports let $A=34/27$ and, for each tail prime $p$, let $C$ be the product of the other three tail caps. The interval bound used above forces $ACx(p,e)\ge2$: the competing endpoint $Ax(p,e)+(13/27)y(p,e)$ is affine in $y$ and is below 2 at both endpoints 0 and 1. If we already know $e\ge h$, then $y(p,e)\ge(1+p^{-1}+\cdots+p^{-h})/(e+1)$. Thus

$$e+1\ \ge\ \frac{AC(1+p^{-1}+\cdots+p^{-h})}{ACp-2(p-1)}.$$

All denominators here are positive. Starting at $h=1$, apply this three times, using at most the terms through $p^{-8}$. This gives the lower bounds below. Five times these bounds makes the first product exceed 2 even when each $x$ is replaced by its lower bound obtained from $y\le p/((p-1)(e+1))$. At least one exponent therefore lies below five times its indicated floor.

| $r$ | Floors on exponents of $5,7,19,r$ | Height bound | Two-exponent boxes |
|---:|---|---:|---:|
| 23 | 19, 12, 4, 3 | 11,616 | 1,765,316 |
| 29 | 65, 43, 14, 9 | 13,536 | 7,088,492 |
| 31 | 163, 109, 36, 21 | 14,176 | 18,628,036 |

The [Python replay](five_square_cases_245212.py) computes those bounds as exact fractions and checks all three supports, using $W(3^2)=34$ and $\sigma(3^2)=13$ in the cofactor congruences. Only two tuples pass the first pair of prime tests, both for $r=23$; neither passes the remaining tests. Run `python3 five_square_cases_245212.py` to reproduce the calculation. The [C++ replay](five_prime_replay_245212.cpp) accepts 23, 29, or 31 as an argument for these same supports. The table of possible supports above is Lean-verified; this further elimination uses the written height argument and exact computation.

**The $q=17$ row is also excluded.** The same inequalities and the same Python cross-prime sieve apply to every permitted $r=19,23,29,31,37$. With $q=17$, the inputs and box counts are:

| $r$ | Floors on exponents of $5,7,17,r$ | Height bound | Two-exponent boxes |
|---:|---|---:|---:|
| 19 | 8, 5, 2, 1 | 10,336 | 661,500 |
| 23 | 12, 8, 3, 2 | 11,616 | 1,161,492 |
| 29 | 24, 16, 6, 3 | 13,536 | 2,652,628 |
| 31 | 31, 20, 7, 4 | 14,176 | 3,514,856 |
| 37 | 92, 61, 23, 10 | 18,976 | 14,110,928 |

For this family use `python3 five_square_cases_245212.py --fourth 17`. After recovering the candidate exponents of the two unfixed primes, the replay tests the remaining two prime congruences at the *actual* candidate exponents (capped at 20, which only weakens the rejection). No tuple passed all four. Thus with five odd primes and exactly two factors of three, **$3,5,7$ must all divide the number, and its fourth prime is 11 or 13**. The complete conjecture and these last two families remain open. The $q=17$ exclusions are computational, not Lean certificates.

**The $q=13$ row is excluded as well.** All 36 choices of the last prime $13<r<190$ are covered by the [finite-box replay](five_square_boxes_245212.py). For each $r$, start with the same written height bound and computed lower bounds. Partition every exponent interval into consecutive disjoint boxes $[l,\min(2l-1,E)]$. Bound each normalized moment from above and below, rounding outward to a grid of width $2^{-42}$. Reject a box if its score excludes 2 or if the integer-rounding test in the height argument rules it out. On the remaining boxes fix the two shortest intervals in turn and test the cofactor congruences at the other two primes, using each box's lower exponent as the modulus exponent (capped at 20). No four-exponent tuple passed even that first pair of congruences. In particular **the only remaining five-prime support when $3^2\parallel n$ is $3,5,7,11,r$**, with $r>11$. This elimination is by exact computation. Run `python3 five_square_boxes_245212.py 13 17 19 23 29 31 37 41 43 47 53 59 61 67 71 73 79 83 89 97 101 103 107 109 113 127 131 137 139 149 151 157 163 167 173 179 181` from the research branch.

## Reduction to ten boxes

For $p^e\parallel n$ write $T(p^e)=(e+1)p^e$, $x(p,e)=W(p^e)/T(p^e)$ and $y(p,e)=\sigma(p^e)/T(p^e)$. All three divisor functions are multiplicative, so at a solution $\prod x+\prod y=2$. We have
$$y(p,e)=\frac{1+p^{-1}+\cdots+p^{-e}}{e+1},\qquad x(p,e)=1+\frac{1-y(p,e)}{p-1}.$$
The product of the caps $p/(p-1)$ is at least two for any $n>1$ satisfying the equality. Indeed $x=y+(1-y)p/(p-1)$; in expanding $\prod x$, every product of one or more caps is at most the product of all caps, and $\prod y<1$.

With at most four odd primes the least must therefore be three: $\prod_{p=5,7,11,13}p/(p-1)<2$. With one or two odd primes the maximum cap is $15/8<2$. With three primes the only possible supports are $3,5,q$ for $q=7,11,13$: the caps at $3,7,11$ and $3,5,17$ are both below two. For four primes with exact exponent one at three, use $x(3,1)=7/6$, $y(3,1)=2/3$, $x(p,e)\le p/(p-1)$ and $y(p,e)\le(p+1)/(2p)$. The worst upper bound over the other three primes $p\ge5,q\ge7,r\ge11$ is $221339/110880<2$.

For four primes with the exponent of three at least two, the [kernel-checked prime bound](four-prime-decision-245212.md) restricts the ordered support $3,p,q,r$ to $p\in\{5,7\}$, $q\le31$, $r<10^{18}$. When $v=3pq/[2(p-1)(q-1)]<2$, the cap condition improves this to $r\le\lfloor2/(2-v)\rfloor$. These are the ten nonempty integer intervals in the table below. Some endpoints are composite and are deliberately included.

The [integer-rounding height bound](prime-power-height-245212.md) gives $\max e_i\le1\,920\,000\,000\,000\,000\,011\,376$ for rank four and $\max p_i<10^{18}$. Its proof covers odd and even supports other than powers of two; here only the odd case is needed. The program uses its smaller bound when the box has a smaller largest prime.

## How to reject a complete box

A box gives integer intervals for four exponents and for the last prime. We either prove there is no solution in it, tighten necessary conditions, or bisect an integer interval. A split at $m$ is always into $[l,m]$ and $[m+1,h]$; its location affects running time only. All arithmetical comparisons use integers or exact rational numbers.

**Moment bounds and integer rounding.** The average $y(p,e)$ decreases in each variable; in particular an interval not evaluated exactly can use $p(1-p^{-32})/[(p-1)(e+1)]\le y\le p/[(p-1)(e+1)]$ when $e\ge32$. Positive product bounds on each term reject scores wholly above or below two. The stronger tests in **rounding_245212.py** replace selected $x,y$ by the rational main terms in the height lemma. If both sums differ by less than the reciprocal of the rounded denominator, equality would imply that the rounded score is exactly two. With one factor rounded this is impossible: its correction cannot vanish at a solution by the no-resonance lemma. With several rounded factors, it is also impossible if all correction terms have the same strict sign, or if the largest selected prime divides no exponent-plus-one, since it divides the rounded numerator but not twice its denominator. Unrounded bases are coprime to this prime and every smaller rounded base minus one is smaller than the prime.

The singleton inequality is particularly useful in both directions:
$$p_i^{e_i}\le(2^{k-1}+p_i-1)\prod_{j\ne i}(e_j+1)p_j^{e_j}.$$
It bounds any one exponent above in terms of the others. It bounds another exponent below if the left side is already large and the remaining factors have small upper bounds. Equivalently use the kernel-checked cofactor bound below with $x_j\le2$ and $y_j\le1$. The implementation compares outward intervals for logarithms by finding the bit length of integer 128th powers.

**Leading-digit bounds.** Single out any prime $P$ and put $n=mP^e$, $t=e+1$, $A=W(m)$, $S=\sigma(m)$, and $T=m\tau(m)$. The equality gives
$$\sum_{j=0}^{e}P^j[A(j+1)+S]=2TtP^e.$$
Subtract the leading term and divide the remaining positive sum by $P^e$. Its last term, and a geometric upper bound for the whole sum, give $D=t(2T-A)-S>0$ and
$$(P-1)D< eA+S\le PD.$$
The upper inequality is equality just when $e=1$. Thus $P=\lceil(eA+S)/D\rceil$.

Write $X\le A/T\le U$, $Y\le S/T\le V$, and $p\le P\le P'$ on a box. Necessary constraints on $t$ are
$$t(2-X)>Y,\quad t[(P'+1)X-2P']\le X-(P'+1)Y,\quad t[pU-2(p-1)]>U-pV.$$
Indeed $eA+S-PD$ decreases as $P$ increases at a possible solution; after dividing by $T$ it increases with either cofactor moment. For the inverse bound on the last prime, the quotient $(eX+Y)/[(e+1)(2-X)-Y]$ increases with $X,Y$ on a positive denominator. For fixed moments it is monotone or constant as a function of $e$, so its extremes lie at the two endpoints. A bound that encounters a pole is omitted unless the entire range has nonpositive denominator.

**Nonzero cofactor divisibility.** For a solution and an odd $P\nmid m$,
$$ P^e\mid W(m)-(P-1)\sigma(m),\qquad W(m)-(P-1)\sigma(m)\ne0.$$
Both assertions and the absolute-value bound are in **PrimePowerDivResearch245212.lean**, theorem `OMA.PrimePowerDiv245212.cofactor_bound` with its companion lemmas. Modulo $P^e$, the prime-power identities give $(P-1)\sigma(P^e)=-1$ and $(P-1)W(P^e)+\sigma(P^e)=0$. Multiplying the divisor equality by $(P-1)^2$ gives the divisibility. If the difference vanishes, the equality implies $P\sigma(m)=2m\tau(m)$ and $W(m)+\sigma(m)=2m\tau(m)$; the no-resonance result forces $P=2,m=1$. Reducing modulo $P$ also gives $P\mid A+S$. Exact-prefix leaves use these bounds, recover the candidate prime from its top digit, and test the integer equality. When three other exponents are fixed, the valuation of the nonzero difference bounds the remaining exponent directly.

**Two modular tests.** Fix an earlier prime $P$ and work modulo $P^h$ for $h\le e$. For another fixed unit prime $u$ with variable exponent $j$, the pair $(W(u^j),\sigma(u^j))$ has period dividing $(P-1)P^h$ modulo $P^h$. The program checks that raising $u$ to the period gives one and that the whole repeated block contributes zero to both sums; translation of weights contributes a multiple of $P^h$. It lifts surviving exponent residues from the preceding modulus, tests the congruence, and intersects the survivors with the box. Alternatively keep the last prime as a variable $z$. For a fixed exponent $j$, both local sums are integer polynomials in $z$. Every solution modulo $P^h$ lies over a root modulo $P^{h-1}$, and all $P$ possible lifts of every surviving residue are checked. If the two coefficients share a power of $P$, the common factor is cancelled before lifting. If there are too many lifts the test declines to exclude anything. Composite endpoints are discarded only by trial division or a failed Fermat congruence.

## Reproduce

Keep **fourth_power_245212.py**, **odd_four_245212.py**, **odd_modular_245212.py**, and **rounding_245212.py** together. Run:

    python3 fourth_power_245212.py --unrestricted

No packages or machine-specific data are required. Run without Python's `-O` (which disables assertions). A found equality or unfinished family stops the run. The Python arithmetic and the combined conclusion are not kernel-certified. The prime-support bound, nonzero cofactor divisibility and [explicit rank-four exponent ceiling](HeightResearch245212.lean) have separate Lean proofs. Work limits are per support; they are not number-theoretic cutoffs.

| Ordered first three primes | Largest allowed fourth prime | Boxes |
|---|---:|---:|
|3,5,7|$10^{18}-1$|9,884|
|3,5,11|$10^{18}-1$|46,428|
|3,5,13|$10^{18}-1$|169,325|
|3,5,17|256|28,468|
|3,5,19|96|13,236|
|3,5,23|50|1,514|
|3,5,29|34|38|
|3,5,31|32|1|
|3,7,11|26|5,093|
|3,7,13|19|48|

The exact three-prime checks at $3,5,7$, $3,5,11$, and $3,5,13$ visit 635, 171, and 57 boxes. Across ranks three and four the computation visits 274,898 boxes. The divisors of 1 give the claimed equality at 1.

The result for **at most three distinct prime divisors** now also has a [self-contained Lean proof](OddThreeResearch245212.lean). It starts with the original Formal Conjectures definition and proves `OMA.OddSupportClass245212.odd_three` for arbitrary odd $n$. Its three finite certificates independently discard exponent boxes by interval bounds or a prime-power divisibility test on the other two factors. No numerical size bound on the input appears in the theorem. To replay it, use `lake env lean /path/to/OddThreeResearch245212.lean` in the [pinned Formal Conjectures checkout](https://github.com/google-deepmind/formal-conjectures/tree/9097e2f90e66d2f6244209cb1c07f7120d17ec53). The file prints the axioms the result uses: propositional extensionality, classical choice, and quotient soundness.

For related earlier results see Anmol Sahu's [inversion of the exponent of two](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5390) and [DomTheDeveloper's density-zero and totient inequalities](https://github.com/google-deepmind/formal-conjectures/issues/8382). Neither replaces the four-prime computation here.
