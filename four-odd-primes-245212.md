# An odd solution to OEIS A245212 needs at least five distinct primes

**Theorem (computer-assisted).** The only positive odd integer $n$ with at most four distinct prime divisors that satisfies
$$W(n)+\sigma(n)=2n\tau(n),\qquad W(n)=\sum_{d\mid n}d\tau(d),$$
is $n=1$. The prime multiplicities, the primes themselves, and $n$ are unrestricted in this statement. This settles the four-odd-prime branch of [Křížek's A245212 conjecture](https://oeis.org/A245212); it does not settle the full conjecture.

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

For related earlier results see Anmol Sahu's [inversion of the exponent of two](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5390) and [DomTheDeveloper's density-zero and totient inequalities](https://github.com/google-deepmind/formal-conjectures/issues/8382). Neither replaces the four-prime computation here.
