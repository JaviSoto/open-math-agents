# Two odd primes with freely varying exponents

For every fixed $k\ge0$, only finitely many odd $m$ with at most two distinct prime factors can satisfy the A245212 equality at $2^k m$. Both odd primes and both of their exponents are unrestricted. Conversely one can fix an odd prime $r$ dividing $m$ and let **everything else**, including $k$, vary: there are still only finitely many solutions with at most two distinct odd primes. These are finiteness statements; they do not say that there are no exceptions. For $k=1,2$ there are in fact **no** solutions with two distinct odd primes.

**Why two primes suffice.** The [earlier square-core result](uniform-exponents-245212.md) covers square $m$. For a nonsquare, the [bounded-power theorem](bounded-atom-245212.md) fixes one exactly dividing $r^e$ to a finite list. With $a=2^k r^e$, there is now at most one prime power $q^f$ left. Such an odd prime must divide $W(a)+\sigma(a)>0$, a fixed integer. Moreover $q^f\le |W(a)-(q-1)\sigma(a)|$. The right-hand side does not vanish at a solution. Both the last prime and its exponent are therefore bounded.

**How the power of two is controlled.** If $m=\prod p^e$ is an odd part at equality, then

$$ k\sum_{p^e\parallel m}\frac{e}{(e+1)p}<1. $$

The bound holds for any number of odd primes. Keeping just the two leading terms of $W(p^e)/((e+1)p^e)$ gives a lower bound $1+e/((e+1)p)$. Multiply the factors, retaining the constant and the linear terms; all other terms are nonnegative. The dyadic factors $c=X(2,k)$ and $d=Y(2,k)$ satisfy $c+d=2$ and $kd<c$. At equality $c(\prod X-1)=d(1-\prod Y)<d$, giving the inequality. Thus $k<2p$ for **every** odd prime dividing $m$; for one fixed prime the first finiteness result need only be applied at finitely many $k$.

**The explicit exclusions at $k=1,2$.** The dyadic Euler bound says that $2\le X(2,k)\prod_{p\mid m}p/(p-1)$ for $m>1$. Keep $X(2,k)$ exact and enclose the remaining product by its value when all odd exponents are zero or its product of Euler bounds. At $k=1,2$ every odd pair is excluded by this inequality, the previously checked $3,q$ family, or the previously checked $5,7$ family.

[Unrestricted finiteness, the reciprocal bound, and the fixed-odd-prime theorem](DyadicLeastResearch245212.lean) and [the exact dyadic Euler bound and the $k=1,2$ exclusions](DyadicEulerResearch245212.lean) are standalone Lean files. Run `lake env lean /path/to/file.lean` for each from the project's pinned formal-conjectures checkout. No enumeration of candidate natural numbers is needed for the finiteness results.
