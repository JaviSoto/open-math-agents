# A computable height for three odd primes, and two tests that work at every rank

For each $k\ge0$, there is an **explicit computable upper bound** for every
solution of the [A245212 equation](https://oeis.org/A245212) of the form
$2^k m$ with $m$ odd and supported on exactly three primes. No prime or
exponent of $m$ is prescribed. The previous [finiteness theorem](three-odd-finiteness-245212.md)
did not give such a bound. The universal bound here is large.

**A cofactor that cannot resonate.** Write $W(h)=\sum_{d\mid h}d\tau(d)$.
For every odd prime $p$ and $a>0$, the number $h=2^k p^a$ does **not**
divide $W(h)$. To see why, suppose it did. The congruence $W(p^a)\equiv1\bmod p$
and multiplicativity force $p^a\mid W(2^k)=k2^{k+1}+1$.
On the other hand $2^k\mid W(p^a)$, since $W(2^k)$ is odd.
The exact local formula

$$
v_2(W(p^a))+1=v_2(a+1)+v_2(a+2)
$$

and the fact that exactly one of these consecutive numbers is even show that
$2^{k+1}\le a+2$. This makes $p^a>k2^{k+1}+1$: check $k=0,1$ separately,
and for $k\ge2$ use $a\ge2(k+1)$. This contradicts the first divisibility.

If a cofactor has an exact Euler resonance on unused primes $T$, it satisfies
$W(h)\prod_{q\in T}q=2h\tau(h)\prod_{q\in T}(q-1)$. As $\gcd(h,\prod q)=1$,
this forces $h\mid W(h)$. Thus the [whole-prime-power bound](effective-prime-power-245212.md)
applies **twice in succession** to a dyadic input, regardless of its odd rank:
first before any odd prime has been chosen, and again after any one odd
prime power has been absorbed into the prefix.

**The height formula.** Let $M(h,r),P(h,r)$ be the explicit exponent and prime
bounds in the linked note. Define

$$
J(h,r)=h(P(h,r)+1)^{M(h,r)},\quad
L=J(2^k,3),\quad D=\max_{0\le h\le L}J(h,2).
$$

Use the natural-number formulas also at the unused endpoint $h=0$
(natural division by zero is zero). After two steps the prefix is at most $D$.
The last odd prime-power completion gives $n\le4D^7$. The [standalone Lean
proof](RankThreeEffectiveResearch245212.lean) checks the complete bound from
the original definition: `OMA.RankThreeEffective245212.original`.

**All ranks.** Starting from any positive cofactor $h$ and $r$ remaining
distinct odd primes, define $C(0,h)=h$ and

$$
C(r,h)=\max_{0\le p\le P(h,r),\,0\le a\le M(h,r)}
                 C(r-1,hp^a)\quad(r>0).
$$

Each of the following is sufficient to conclude $n\le C(r,h)$:

* No remaining odd prime divides $\tau(h)$ or the exponent-plus-one of a
  *different* remaining prime. This makes the earlier
  [divisor-count finiteness result](cofactor-cross-count-245212.md) effective.
* Write $m=n/h$ and
  $E(m)=\sum_{p\mid m}\max(0,v_2(v_p(m)+2)-1)$, summing over primes.
  Then $v_2(W(h))+E(m)\le v_2(2h\tau(h))$ suffices. In particular at
  $h=2^k$ this says $E(m)\le1+k+v_2(k+1)$; divisibilities between primes
  and divisor counts are unrestricted.

For the second test, a nonempty Euler denominator has an extra factor of two,
while its numerator is odd. Absorbing $p^a$ increases the order difference
$v_2(W(h))-v_2(2h\tau(h))$ by exactly $v_2(a+2)-1$ and removes its contribution
from the remaining budget. The nonresonance condition therefore persists until
no primes remain. This [standalone Lean proof](CofactorValuationResearch245212.lean)
includes both sufficient conditions.

**Checking a resonance.** A reduced product $\prod p/(p-1)$ identifies its
prime support: the largest prime cannot cancel against any denominator and
must be the largest prime divisor of the reduced numerator. Remove it and
repeat. The [Lean proof](EulerSupportUnique245212.lean) establishes uniqueness
without a bound on the number of primes. The [integer decoder](cofactor_resonance_245212.py)
tested every $h\le2{,}000{,}000$: only 17 passed $h\mid W(h)$ and $W(h)<2h\tau(h)$,
and none had a nonempty resonance on coprime odd primes. This numerical
observation does not rule out resonance at larger cofactors.

Both standalone files run with `lake env lean /path/to/FILE.lean` from the
formal-conjectures checkout at `9097e2f90e66d2f6244209cb1c07f7120d17ec53`.
