# A modulo-three obstruction for OEIS A245212

If $n=3^a u^3$, where $a>0$, $u>0$ and $3\nmid u$, then $n$ does not satisfy the divisor equality in [OEIS A245212](https://oeis.org/A245212). Both even and odd cofactors are allowed. In particular **no positive cube divisible by three is a solution**. Also, **no nontrivial odd cube with at most six distinct prime factors is a solution**.

Write $W(n)=\sum_{d\mid n}d\,\tau(d)$ and $S(n)=\sigma(n)$. The equality is $W(n)+S(n)=2n\tau(n)$. Both $W$ and $S$ are multiplicative. For a prime $q$,

$$
 W(q^e)=\sum_{j=0}^e(j+1)q^j,\qquad S(q^e)=\sum_{j=0}^e q^j.
$$

In $\mathbb F_3$ one has $W(q^{3e})=1$ for every $e\ge0$: increasing $e$ by one adds $q^{3e}(2q+q^3)=0$. The unweighted sum $S(q^{3e})$ is always zero or one. For $q=0,1$ modulo three it equals one; for $q=-1$ it is the alternating sum of $3e+1$ terms. Products preserve these two assertions. Both sums at $3^a$ are one modulo three for every $a$. Consequently $W(3^a u^3)+S(3^a u^3)$ is either one or two modulo three, whereas $2n\tau(n)$ is zero.

For the second assertion use the necessary condition $\prod_{p\mid n}p/(p-1)\ge2$ for any nontrivial solution. One proof: put $y(p,e)=S(p^e)/((e+1)p^e)$, $c(p)=p/(p-1)$ and $x(p,e)=W(p^e)/((e+1)p^e)=y+(1-y)c$. The equality gives $\prod x+\prod y=2$; expanding the first product and bounding each nonempty product of $c$'s by the full product gives $\prod x\le\prod y+(1-\prod y)\prod c$. Since $\prod y<1$, the condition follows.

If $n$ is odd, $3\nmid n$, and $n$ has at most six prime factors counted without multiplicity, its product of $c(p)$ is at most that for $5,7,11,13,17,19$:

$$
 \frac54\frac76\frac{11}{10}\frac{13}{12}\frac{17}{16}\frac{19}{18}
 =\frac{323323}{165888}<2.
$$

Hence every nontrivial odd solution with at most six different primes is divisible by three. Applying the cubic congruence proves the claim.

The standalone Lean file is **CubeResearch245212.lean**. The declarations in namespace **OMA.Cube245212** are **no_three_times_cube**, **no_cube_of_three**, **three_dvd_odd_of_six**, and **no_odd_cube_six**.
