# An explicit bound on one whole odd prime power in every fixed-rank solution

Fix the exponent $k$ of two and the number $r>0$ of distinct odd primes in a
putative [A245212 solution](https://oeis.org/A245212). There is a computable
pair of bounds $P,M$, depending only on $k,r$, such that **the same odd prime**
$p$ satisfies $p\le P$ and $v_p(n)\le M$. This applies even when some odd
prime divides $k+1$ or divides another exponent plus one. The formulas grow
quickly; their point is to reduce one unbounded choice to a provably finite one.

For the formulas, put $h=2^k$, $A=W(h)=\sum_{b\mid h}b\tau(b)$,
$S=\sigma(h)$, and $H=2h\tau(h)$. Set

$$
B_0=1,\qquad B_{j+1}=\max\{2B_j,(2+2A2^j B_j)^{j+1}\}.
$$

Then one may take

$$
M=B_r(2Ar2^r+2S),\qquad
P=\max\{M+1,\lfloor rH(S+1)/(H-A)\rfloor\}.
$$

The same bounds work for any fixed positive cofactor $h$ coprime to the
remaining part, provided no subset of its remaining primes satisfies
$A\prod p=H\prod(p-1)$. This hypothesis is automatic for $h=2^k$ and
odd remaining primes: the left side is odd and the right side even.

**Why a prime power is bounded.** For any eligible set of at most $j$ primes,
the distance between $H$ and $A\prod p/(p-1)$ is at least $1/B_j$. Remove
the largest prime $q$. If $q$ is sufficiently large, restoring it changes
the previous product by at most half its distance from $H$. Otherwise every
prime is bounded, giving a bound on the denominator of a nonzero rational.
This proves the estimate by induction, including the empty product.

If every exponent is at most $M$, the harmonic bound for the least prime
gives $P$ (at a solution with odd part greater than one, $H>A$). Otherwise
suppose each prime at most $M+1$ has exponent greater than $M$. Approximate
its normalized weighted divisor factor by $p/(p-1)$, and the factor for
each larger prime by one. The error per factor is at most $2/(M+1)$; the
ordinary normalized divisor product is also at most $2/(M+1)$ because one
exponent exceeds $M$. Substituting these estimates in the original equation
puts the limiting Euler product strictly closer to $H$ than $1/B_r$,
contradicting the previous estimate.

**Reproduce.** Check the [standalone Lean source](CofactorEffectiveResearch245212.lean)
with `lake env lean /path/to/CofactorEffectiveResearch245212.lean` in the
project's formal-conjectures checkout at `9097e2f90e66d2f6244209cb1c07f7120d17ec53`.
The original cofactor statement and dyadic corollary are
`OMA.CofactorEffectiveOriginal245212.original` and `.dyadic`.
The [rational interval search](euler_gap_245212.py) independently gives more
useful distances in small cases: at rank at most three it certifies $1/8192$
for $h=2$ and $7/288$ for $h=4$. These sharper numerical estimates are from
the Python search; the Lean theorem uses the universal recurrence above.
