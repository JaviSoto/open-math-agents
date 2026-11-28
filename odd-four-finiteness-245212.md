# Finiteness with four unrestricted odd prime factors

There are finitely many odd integers satisfying the [OEIS A245212](https://oeis.org/A245212) equality that have at most four distinct prime factors. Both the primes and their exponents vary. The proof does not enumerate this finite set; in particular it does not show that its only member is 1.

Write $T(n)=n\tau(n)$, $S(n)=\sigma(n)$, and $W(n)=\sum_{d\mid n}d\tau(d)$. The equality is $W+S=2T$. On each prime power put

$$
 y(p,e)=\frac{1+p^{-1}+\cdots+p^{-e}}{e+1},\qquad
 x(p,e)=1+\frac{1-y(p,e)}{p-1},\qquad c(p)=\frac p{p-1}.
$$

The prime-power sum formulas give $S/T=y$ and $W/T=x$. Hence the equality becomes $\prod x+\prod y=2$. If there is a positive exponent, $\prod y<1$. Since $x=y+(1-y)c$, expanding shows

$$
 \prod x\le \prod y+(1-\prod y)\prod c.
$$

Each term in the expansion except the all-$y$ term has a product of a subset of the $c$'s, bounded by their full product. It follows that $\prod c\ge2$.

Suppose that a prime $r\ge257$ occurs. For at most three odd primes the full product is at most $(3/2)(5/4)(257/256)<2$. With four odd primes, their increasing list must be $3,5,q,r$, where $q\in\{7,11,13\}$. Otherwise compare, coordinate by coordinate, against $(5,6,7,257)$, $(3,7,9,257)$, or $(3,5,17,257)$. Each comparison has product $<2$; in the last case the product is $65535/32768$.

The finite calculation needed is the following separation statement. For each of these three triples $(3,5,q)$, replace **one** of its three $x(p,e)$'s by the limit $c(p)$. For every choice of the remaining positive exponents, the resulting product $F$ satisfies

$$
 |F-2|>10^{-8}.
$$

The checker splits integer intervals of exponents; it never assumes an upper limit on them. For $e<32$ it uses exact geometric sums. At $e\ge32$ it uses

$$
 \frac{p(1-p^{-32})}{(p-1)(e+1)}\le y(p,e)\le
 \frac p{(p-1)(e+1)}.
$$

Monotonicity of $x(p,e)$ supplies both endpoints of a product on each interval box; $e=\infty$ gives $y=0$. The nine trees have 1,985 nodes in total. The Python script generates proposed splits. The Lean kernel checks the interval enclosures, the rational comparisons and the coverage of all the exponents.

Set $H=10^{10}$. If $r>H$ and a prefix exponent $e\ge H$, choose its corresponding face. All prefix $x$'s are between 1 and $3/2$; $y(p,e)<2/(e+1)$; and $1\le x(r,d)\le1+1/H$. Replacing $x(p,e)$ by $c(p)$ changes the prefix product by at most $3y(p,e)$. Adding the fourth $x$ changes the product by at most $5/H$, and the full product of the four $y$'s is at most $y(p,e)$. More precisely both one-sided deviations of the score from the face are bounded by $\max(5/H+y(p,e),3y(p,e))<10^{-8}$. This contradicts the separation statement at an equality. Therefore either every prime is at most $H$, or all three prefix exponents are less than $H$.

In the latter case put $m=3^a5^bq^c\le195^H$. Reducing the equality for $m r^d$ modulo $r$ shows $r\mid W(m)+S(m)$: both local divisor sums at $r^d$ are 1 modulo $r$, while $T(mr^d)$ is 0. Thus all prime bases lie in a single explicit finite interval. For example

$$
 B=H+\sum_{1\le m\le195^H}(W(m)+S(m))
$$

works. The [fixed-prime-support finiteness theorem](https://github.com/JaviSoto/open-math-agents/blob/ba691fea37a641775967023dd99c87b7413d3488/divisor-balance-245212.md) applies to all primes up to $B$. It excludes powers of two from its conclusion, so the odd integer 1 is included separately.

The standalone Lean source is `OddResearch245212.lean`: `OMA.OddFaces245212.odd_support` gives the uniform prime bound and `OMA.OddFaces245212.odd_finite` gives the finiteness statement.
