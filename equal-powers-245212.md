# No odd power of a squarefree base on at most four primes

Let $u>1$ be odd and squarefree with at most four distinct prime divisors. For every positive exponent $e$ the integer $u^e$ fails the OEIS A245212 equality. This includes every choice of prime bases and every common exponent. The proof does not bound the input before searching it.

Write $u=p_1\cdots p_k$ with increasing primes. The companion modulo-three result shows that every nontrivial odd solution with at most six prime factors has $p_1=3$, independently of the exponents. The strict ordering and primality then give lower bounds $5,7,11$ for any further coordinates. The normalized equality is

$$
 \prod_{i=1}^k x(p_i,e)+\prod_{i=1}^k y(p_i,e)=2,\qquad
 y(p,e)=\frac{1+p^{-1}+\cdots+p^{-e}}{e+1},\quad x(p,e)=1+\frac{1-y(p,e)}{p-1}.
$$

For each $k=1,2,3,4$, the certificate covers integer intervals in the common exponent and in the remaining prime bases. Each split $[L,H]=[L,c]\cup[c+1,H]$ covers the whole interval, including when $H$ is infinite. On a box, $y$ decreases as either coordinate increases; at infinite exponent its limit is zero, and at infinite prime base its limit is $1/(e+1)$. For finite $e<32$ the evaluator uses the exact geometric sum; for $e\ge32$ it uses

$$
 \frac{p(1-p^{-32})}{(p-1)(e+1)}
 \le y(p,e)\le\frac{p}{(p-1)(e+1)}.
$$

Nonnegative bounds on $x$ follow directly from its formula. A leaf is accepted if the upper score bound is below two, the lower score bound is above two, a prime coordinate is a singleton composite, or two interval bounds contradict the strict ordering. There are respectively 3, 3, 157 and 6,247 nodes for ranks one through four. The largest split on the exponent occurs at 98,301; the part above that value is covered by the same proof.

The standalone Lean source is **EqualResearch245212.lean**, with declaration **OMA.Equal245212.no_squarefree_power**. The reproducible generator **equal_power_245212.py --lean** emits the finite certificate; the Lean proofs check its rational inequalities and completeness independently.
