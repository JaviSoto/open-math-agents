# Where an exact Euler product can occur

Let $W(h)=\sum_{d\mid h}d\tau(d)$. **For every prescribed divisor count $D$, only finitely many positive integers $h$ divide $W(h)$.** An explicit upper bound for all of them is $L_D$, where

    L₀ = 1,    Lᵢ₊₁ = Lᵢ (D³ Lᵢ + 1)^D.

Put $j=W(h)/h$. For a coprime factorization $h=uv$ with $v>1$, write $p$ for the least prime of $v$. The positive integer $g=ju-W(u)\tau(v)$ satisfies $pg\le\omega(v)ju$. Indeed $W(v)>v\tau(v)$, while $W(v)\le\tau(v)\sigma(v)$ and $\varphi(v)\sigma(v)\le v^2$. Then $gv\le ju(v-\varphi(v))$; the proportion of integers sharing a prime with $v$ is at most the sum of reciprocals of its prime factors. Thus $p\le\omega(v)ju$. Every exponent is at most $D$, the rank is at most $D$, and $j\le D^2$ by termwise comparison in $W(h)$. Iterating the bound on a whole prime power gives the stated recurrence.

In the A245212 reduction, an exact Euler product at $h$ has a nonempty set $T$ of unused odd primes, all coprime to $h$, with

$$W(h)\prod_{q\in T}q=2h\tau(h)\prod_{q\in T}(q-1).$$

The cofactor must divide $W(h)$. Every $p\in T$ either divides $D=\tau(h)$ or divides $q-1$ for a strictly larger $q\in T$: reduce the equation modulo $p$ and use coprimality. Repeating this gives a way to construct the allowable pool of primes starting from the prime divisors of $D$.

Both results are in the [standalone Lean proof](CofactorEulerAncestryResearch245212.lean): `OMA.WeightedMultipleHeight245212.divisor_count` and `OMA.CofactorEulerAncestry245212.ancestry`. Replay with `lake env lean /absolute/path/to/CofactorEulerAncestryResearch245212.lean` in the project's pinned Formal Conjectures checkout.

**Exact computational test, separate from the Lean results.** In every divisor count from 1 through 1,024 there is no such cofactor, odd or even. There is no cutoff on $h$, its prime factors, or their exponents. For $h=1$ the Euler numerator would be odd and the right side even. For $h>1$, enumerate all multiplicative partitions of $D$, giving the exponents. Either enumerate possible Euler supports from the descending-prime pool or reconstruct them from the only possible integral quotients $D<j<2D$. The two independent methods gave identical target sets at every count tested through 1,024. For each target enforce the exact power of 2 on each side, then solve $\prod W(p^e)/[(e+1)p^e]=j/D$ in the remaining bases (with any dyadic power already fixed).

The reduced denominator of a residual target divides the remaining product $\prod[(e+1)p^e]$. Removing its gcd with $\prod(e+1)$ can therefore force a specific prime base. In the last position the denominator has the exact form $t p^e$, with $t\mid e+1$, since $W(p^e)\equiv1\pmod p$. When no divisor is found, monotone comparison still gives a finite interval for the smallest remaining prime. Only integer and rational arithmetic determine which branches are discarded. For divisor counts through 512, forcing primes this way reduced 7,719,216 candidate prime prefixes to 1,622.

Run `python3 divisor_count_resonance_245212.py --max-divisors 1024`; add `--strategy quotient` for the independent target generator, or `--parity even` to isolate the dyadic cases. The script also recovered all 780 planted positive weighted products in a separate test covering one to four distinct primes and exponents from 1 to 3. The exhaustive calculation is not yet a Lean proof of the 1,024 cutoff.
