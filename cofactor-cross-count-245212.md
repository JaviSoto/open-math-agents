# In an infinite fixed-rank family, an odd prime must divide a divisor count elsewhere

Fix a positive cofactor $h$ and the number $r$ of additional, distinct odd primes. Let
$n=h\prod_{i=1}^r p_i^{a_i}$, where $a_i>0$ and $p_i\nmid h$. Among solutions of
the [A245212 divisor equation](https://oeis.org/A245212), only finitely many satisfy **both**:

* No $p_i$ divides $\tau(h)$, the number of divisors of $h$.
* No $p_i$ divides $a_j+1$ for a **different** index $j$.

There is no restriction on $p_i\mid a_i+1$ for its own index, and no bound on the
primes or exponents. The result holds for each fixed rank, however large. It does
not give the numerical bound or rule out isolated solutions.

In particular, at each fixed power $2^k$ and rank $r$, all but finitely many
solutions must have an odd prime dividing either $k+1$ or the exponent-plus-one
of a *different* odd prime. For odd inputs ($h=1$), only the second alternative
is possible. This is an obstruction to an infinite family, not a divisibility
claim about every individual solution.

## Why this holds

Write $W(t)=\sum_{b\mid t}b\tau(b)$, $A=W(h)$ and $T=h\tau(h)$. The normalized
weighted divisor average of $p^a$ is $X=W(p^a)/[(a+1)p^a]$, and its ordinary
divisor average is $Y=\sigma(p^a)/[(a+1)p^a]$. At a solution,

$$
\frac A T\prod_i X_i + \frac{\sigma(h)}T\prod_i Y_i=2 .
$$

Every $X_i\ge1$ and the second summand is positive, so $A<2T$.
Suppose no remaining prime power has both base and exponent bounded.
Fixed exponent vectors already allow only finitely many bases, by strict
monotonicity of the normalized divisor sums and Dickson's lemma. Thus in an
escaping sequence some exponent tends to infinity. Pass to a simultaneous
subsequence: each increasing base gives $X_i\to1$, and each fixed base $p$
with increasing exponent gives $X_i\to p/(p-1)$. The ordinary product tends
to zero. For the set $F$ of the latter bases this would give

$$
A\prod_{p\in F}p=2T\prod_{p\in F}(p-1).
$$

The empty set is impossible since $A<2T$. For a nonempty set, its **largest**
prime divides the right side but is larger than every factor $p-1$. It must
therefore divide $2T=2h\tau(h)$. The prime is odd, coprime to $h$, and was
assumed not to divide $\tau(h)$. This proves that some whole prime power is
bounded. There are finitely many choices for it. Absorb it into the cofactor.
The new divisor count is $\tau(h)(a_i+1)$, and the second hypothesis ensures
that none of the remaining primes divides it. Induction on the number of
remaining primes proves the assertion.

The [standalone Lean source](CofactorCrossResearch245212.lean) proves
`OMA.CofactorCrossOriginal245212.original` from the project's pinned
`FormalConjectures.OEIS.«245212»` statement. To replay, run
`lake env lean /path/to/CofactorCrossResearch245212.lean` from the formal-conjectures checkout.
