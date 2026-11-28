# Odd prime powers that must stay bounded in A245212

Fix a nonnegative integer $k$ and an upper bound $K$ on the number of distinct prime factors of an odd integer $m$. For each prime power $p^e$ exactly dividing $m$, put $h(e)=\max(0,v_2(e+2)-1)$. There is a number $B=B(k,K)$ with the following property. Apart from finitely many $m$, the original A245212 equality for $2^k m$ requires

$$\sum_{p^e\parallel m,\;p\le B,\;e\le B} h(e) \;>\; k+v_2(k+1).$$

In particular there are only finitely many solutions when the sum over **all** the odd prime powers is at most this threshold. For example, at any fixed $k\ge1$, there are only finitely many odd parts $p^2q^{2j+1}$ at equality, allowing both primes and $j$ to vary: the square contributes one, and the odd exponent contributes zero. The result does not compute $B$ or rule out every member of that finite set.

**Proof.** Write $X(p,e)=W(p^e)/((e+1)p^e)$, where $W(n)=\sum_{d\mid n}d\tau(d)$, and $Y(p,e)=\sigma(p^e)/((e+1)p^e)$. At equality the product of the $X$ factors plus the product of the $Y$ factors is two. The dyadic factor $X(2,k)$ has odd numerator and denominator with exactly $H=k+v_2(k+1)$ factors of two. For odd $p$, $X(p,e)/2^{h(e)}$ admits a representation with odd numerator.

The weighted product $X(2,k)\prod X(p,e)$ stays a positive distance from two whenever the displayed sum is at most $H$, for a sufficiently large common cutoff $B$. Otherwise choose near-equalities with cutoff tending to infinity. Pass to a subsequence on which every prime and exponent coordinate is monotone. A diverging prime gives limiting factor one, and a fixed prime with diverging exponent gives $p/(p-1)$: both have odd numerator. Only coordinates where both entries stabilize need powers of two removed. Eventually all those coordinates are visible at the same index, so their total cost is at most $H$. The dyadic denominator absorbs it, making the limiting product a rational with odd numerator; it cannot be two.

At equality the gap bounds the product of the $Y$ factors below. Since every $Y$ is at most one and $Y(p,e)<2/(e+1)$, this bounds every exponent. For any fixed exponent tuple, the earlier fixed-exponents theorem gives only finitely many prime tuples. Taking the finite union proves the claim.

The [standalone Lean proof](ParityBudgetResearch245212.lean) imports just the original OEIS module and Mathlib dependencies. Check it with the project's pinned toolchain using `lake env lean /path/to/ParityBudgetResearch245212.lean`. The final declarations are `OMA.ParityBudget245212.finite_visible_budget` and `OMA.ParityBudget245212.finite_budget`.
