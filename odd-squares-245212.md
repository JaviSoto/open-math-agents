# Divisor balance fails for odd squares on at most four primes

Let $n>1$ be odd, a square, and divisible by at most four different primes. The exact arithmetic computation below excludes $W(n)+\sigma(n)=2n\tau(n)$, where $W(n)=\sum_{d\mid n}d\tau(d)$. There is no upper bound on $n$ in this conclusion.

The previously kernel-checked theorem `OMA.DyadicPower245212.square_root_is_square` forces every exponent of an odd square solution to be divisible by four. Also the products of $p/(p-1)$ on the support must be at least two. This excludes one or two odd primes, forces the least prime to be three, and at rank three permits only $3,5,q$ with $q=7,11,13$. At rank four, the verified prime bounds give ordered support $3,p,q,r$ with $p\in\{5,7\}$, $q\le31$, $r<10^{18}$. If $v=3p q/[2(p-1)(q-1)]<2$, the same envelope gives $r\le\lfloor2/(2-v)\rfloor$. Each of these bounds is conservative at an endpoint.

The numerical verification is independent of the formal prime-support result's certificate: it starts from the allowed supports and rejects them. The [prime-power height proof](prime-power-height-245212.md) gives an explicit upper bound on *every* exponent in each resulting box. Its rounding argument can be used much more locally:

- Write $a_i=p_i^{e_i}$ and $D_i=(e_i+1)(p_i-1)^2$. Round any chosen group of normalized factors as in the height proof; let $D$ be the denominator of the rounded sum. When the change multiplied by $D$ has absolute value less than one, an actual solution would make the rounded numerator exactly $2D$.
- For the largest prime $r$ among the rounded factors, both of its rounded numerators are divisible by $r$. No rounded base minus one is divisible by $r$, and no unrounded prime power is divisible by $r$. Consequently $r$ must divide an exponent-plus-one. If the intervals preclude this, the *whole* box is impossible. This test does not require the errors to have the same sign.
- With only factor $i$ rounded, cancellation at an equality is impossible by the no-resonance lemma, so $a_i\le(2^{k-1}+p_i-1)\prod_{j\ne i}((e_j+1)a_j)$. This gives additional upper bounds depending on the actual box, not just the global largest prime. All logarithmic comparisons use integer bit lengths of 128th powers and outward rounding.
- For $m=n/p^e$ abbreviate $T=m\tau(m)$, $A=W(m)$, $S=\sigma(m)$, and $t=e+1$. From the leading base-$p$ digit of the equality, $D'=t(2T-A)-S>0$, and $(p-1)D'<eA+S\le pD'$. At $e=1$ the upper inequality is equality; for $e>1$ it is strict. These linear inequalities restrict $e$, or determine the unique possible prime when the other three prime powers and $e$ are fixed. In that last case the script additionally tests $p\mid A+S$, $p^e\mid A-(p-1)S$, and the equality itself.
- For a fixed prime support another check uses the divisibility $p_i^{e_i}\mid W(m)-(p_i-1)\sigma(m)$. As each other exponent varies, both local sums are periodic modulo $p_i^h$ for $h\le e_i$: the code directly verifies that an entire period contributes zero to both sums and that its power of the base is one. Lifting compatible exponent residues and intersecting their progressions with multiples of four cannot delete an actual equality. Exact rational interval comparisons, exclusion of composite endpoints, and exhaustive interval splits give the remaining leaves.

## Reproduce

Keep **fourth_power_245212.py**, **odd_four_245212.py**, **odd_modular_245212.py**, and **rounding_245212.py** together and run `python3 fourth_power_245212.py`. They use only the Python standard library. An exceeded work limit or a detected solution interrupts the run; neither is counted as an exclusion. The three-prime cases took 61, 95, and 25 visited boxes. At four primes the counts were:

| $p$ | $q$ | Largest allowed $r$ | Visited boxes |
|---:|---:|---:|---:|
|5|7|$10^{18}-1$|1,328|
|5|11|$10^{18}-1$|56,573|
|5|13|$10^{18}-1$|226,210|
|5|17|256|5,290|
|5|19|96|2,227|
|5|23|50|591|
|5|29|34|24|
|5|31|32|1|
|7|11|26|652|
|7|13|19|58|

In total 293,135 boxes were visited. The prime bound, square-to-fourth-power implication and no-resonance lemma have independent Lean proofs. The new box computation and uniform height estimate described here have not been formally verified in Lean.
