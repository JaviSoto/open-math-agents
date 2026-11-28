# Uniform restrictions for OEIS A245212 at fixed rank

For each integer $K\ge0$, there is an explicit constant $M_K$ such that every odd solution $n>1$ with at most $K$ distinct prime divisors has a prime factor occurring to an exponent smaller than $M_K$. No primes or exponents are prescribed. Two related finiteness results hold:

- For each fixed $a,K\ge0$, only finitely many **odd squares** $u$ with at most $K$ distinct prime factors give a solution $2^a u$. There is no bound on the ratios of exponents in this assertion.
- For each fixed $K,C$, only finitely many odd solutions have at most $K$ distinct prime factors and every exponent at most $C$ times the least. In particular this applies to all powers of squarefree bases with at most $K$ prime factors.

None of these statements excludes nontrivial solutions among the finitely many possibilities.

## The explicit bound for the least exponent

For prime powers define
$
 y(p,e)=\frac{1+p^{-1}+\cdots+p^{-e}}{e+1},\quad
 x(p,e)=1+\frac{1-y(p,e)}{p-1},\quad c(p)=\frac p{p-1}.
$
A solution satisfies $\prod x+\prod y=2$ by multiplicativity of the two divisor sums. For an odd prime, $1\le x\le c\le2$ and $0<y<2/(e+1)$.

Define $D_0=1$ and, in the step from $j$ to $j+1$,
$
 L=1+2^{j+1}D_j,\qquad D_{j+1}=2D_j L^{j+1}.
$
For any set $S$ of at most $j$ odd primes, $D_j|\prod_{p\in S}c(p)-2|\ge1$. To see this, write the product as $A/B$ with $A=\prod p$ odd and $B=\prod(p-1)$. Then $A\ne2B$ and $B|\prod c-2|\ge1$. If every prime is at most $L$ in the induction step, $B\le L^{j+1}\le D_{j+1}$. Otherwise remove any $r>L$. The product of the remaining factors is at most $2^j$, and restoring $r$ changes the product by at most $2^j/(r-1)\le1/(2D_j)$. The inductive gap therefore leaves at least $1/(2D_j)$.

If all $e_i\ge m$, then $0\le c_i-x_i\le2/(m+1)$. Replacing the factors one by one gives $\prod c-\prod x\le K2^K\,2/(m+1)$. The product of the $y_i$ is at most $2/(m+1)$ on a nonempty support. Consequently
$
 M_K=2D_K(K2^K+1)
$
is a strict upper bound on the least exponent.

## Odd squares, including a fixed power of two

Write $W(v)=\sum_{d\mid v}d\tau(d)$. The dyadic restriction proved in the companion source says that if $u$ is an odd square at a solution $2^a u$, then $u$ is actually a fourth power. Hence every exponent of $u$ is a multiple of four. For odd $p$ the integer $W(p^{4b})$ is odd: its parity is that of $\sum_{j=0}^{4b}(j+1)$. Thus $x(p,4b)=W(p^{4b})/((4b+1)p^{4b})$ can be written with odd numerator. So can $c(p)=p/(p-1)$ and the fixed coefficient $x(2,a)$, whose numerator $W(2^a)$ is odd.

For fixed $K$, these observations give a uniform positive gap between 2 and
$
 x(2,a)\prod_{i=1}^{K}x(p_i,4b_i).
$
Indeed a sequence of products approaching 2 admits a common subsequence on which every prime and exponent coordinate is nondecreasing (Dickson’s lemma). Each coordinate then either stabilizes or tends to infinity. When $p_i$ tends to infinity the corresponding factor tends to 1 uniformly in $b_i$. When $p_i$ stabilizes and $b_i$ grows, it tends to $c(p_i)$. Otherwise it has a constant value $x(p_i,4b_i)$. The limiting product consequently has an odd numerator and cannot equal 2. This proves the gap.

At a solution the distance to 2 equals $y(2,a)\prod_i y(p_i,4b_i)$, at most $2/(4b_j+1)$ for *every* $j$. The gap bounds every exponent in this family.

## Closing the finiteness argument

For fixed positive exponents, the score strictly decreases as any prime base increases. The weighted factor is a nonnegative polynomial in $p^{-1}$,
$
 x(p,e)=\frac{1}{e+1}\sum_{j=0}^e (e-j+1)p^{-j},
$
and $y(p,e)$ is strictly decreasing for $e>0$. Products of these positive factors preserve the comparison. Thus distinct solutions with one fixed exponent vector form an antichain in $\mathbb N^K$ under coordinatewise comparison. Dickson’s lemma makes that antichain finite. Taking the union over the finitely many permitted exponent vectors proves both assertions.

Standalone pinned Lean file: `UniformResearch245212.lean`. The statements are `OMA.Uniform245212.least_exponent`, `OMA.SquareFinite245212.square_finite`, and `OMA.Uniform245212.comparable_finite`. The formal proofs use only the standard axioms.
