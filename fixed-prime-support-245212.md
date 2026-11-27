# Only finitely many exceptions can use a fixed set of primes

Let $W(n)=\sum_{d\mid n}d\tau(d)$, and write $\sigma(n)=\sum_{d\mid n}d$.
The [A245212 conjecture](https://oeis.org/A245212) asks whether the positive
solutions of $W(n)+\sigma(n)=2n\tau(n)$ are exactly the powers of two.
For every finite set of primes $P$, only finitely many positive solutions
supported on $P$ are not powers of two. The argument allows arbitrary
exponents on every prime in $P$. It does not exclude an isolated exception.

## An abundancy bound

For every positive $n$,

$$W(n)^2\ \ge\ n\sigma(n)\tau(n)^2.$$

All factors are multiplicative, so consider $n=p^e$. Write
$S_e=\sum_{i=0}^e p^i$, $W_e=\sum_{i=0}^e(i+1)p^i$. Then
$2W_e\ge(e+1)(p^e+S_e)$. For $e=0$ there is equality. For the induction
step, subtract the desired right side at $e+1$ from $2W_{e+1}$. This
gives $2W_e-(e+2)S_e\ge(e+1)p^e-S_e\ge0$. The square inequality follows
by $(p^e+S_e)^2\ge4p^eS_e$. At a solution, $W(n)<2n\tau(n)$, hence

$$\sigma(n)<4n. \tag{1}$$

## No family with one freely varying exponent

Set $X(n)=W(n)/(n\tau(n))$ and $Y(n)=\sigma(n)/(n\tau(n))$;
these too are multiplicative. On a prime power,

$$Y(p^e)=\frac{1+p^{-1}+\cdots+p^{-e}}{e+1},\qquad
  X(p^e)=\frac{p}{p-1}-\frac{Y(p^e)}{p-1}.$$

The former strictly decreases to zero: appending the next term, strictly
smaller than the preceding average, reduces the average.
For fixed $m$ and prime $p\nmid m$, the equality for $mp^e$ is

$$X(m)\frac{p}{p-1}
 +\left(Y(m)-\frac{X(m)}{p-1}\right)Y(p^e)=2.$$

If it holds for two distinct exponents, both the coefficient of $Y(p^e)$
and the constant minus two vanish. Evaluating at $e=0$ gives the equality
for $m$; also $p\sigma(m)=2m\tau(m)$. If $p=2$, then
$\sigma(m)=m\tau(m)$; summing $d\le m$ over all divisors, with the
divisor $1<m$ when $m>1$, shows $m=1$. If $p$ is odd then
$p\mid\tau(m)$, since $p\nmid2m$. Now $\sigma(m)/m=2\tau(m)/p$
is a positive even integer strictly less than four by (1). Thus it equals
two and $\tau(m)=p$ is prime. The formula
$\tau(m)=\prod_{q\mid m}(v_q(m)+1)$ makes $m$ a prime power, for which
$\sigma(m)/m<2$. This is a contradiction. In particular, except for the
powers of two themselves, **at most one exponent works** once the cofactor
and the prime to be appended are fixed.

## The finite antichain argument

Let $P$ be nonempty, and set $H=2\sum_{p\in P}p$. This threshold is
convenient rather than sharp. Record the vector of truncated exponents
$(\min(e_p,H))_{p\in P}$. There are only finitely many such vectors.

Consider increasing the $p$-exponent in $n=m p^e$ with $p\nmid m$.
If another prime $q$ divides $m$ to exponent $f\ge2p$, then
$Y(m)\le Y(q^f)<2/(f+1)$, because the other local $Y$ factors are
at most one and $\sum_{j=0}^f q^{-j}<2$. Also $X(m)\ge1$.
It follows that $(p-1)Y(m)<X(m)$. The affine formula above now shows
that $X(n)+Y(n)$ strictly increases with $e$.

Within a fixed truncated pattern, suppose that two distinct solutions
have exponent vectors $u\le v$ coordinate by coordinate. If just one
coordinate changes, the one-exponent result says that both numbers
are powers of two. If at least two coordinates change, every changed
coordinate was already at least $H$ in $u$. Increase the changed
coordinates one at a time. At each step another changed coordinate
still has exponent at least $H\ge2p$, so the score strictly increases.
It cannot equal two at both ends.

Thus the non-dyadic solutions in each pattern form an antichain: no two
are comparable coordinate by coordinate. Every antichain in
$\mathbb N^{|P|}$ is finite (Dickson's lemma). One short proof is that
each sequence of natural numbers has an infinite nondecreasing
subsequence: either some value recurs infinitely often, or the sequence
eventually exceeds each bound. Applying this successively to each of
the finitely many coordinates finds two comparable vectors in any
infinite sequence. The finite union over truncated patterns proves the theorem.
The case $P=\varnothing$ contains only $1$.

Together with [the odd-divisor bound](divisor-envelope-245212.md), the result
forces both the largest prime factor and the odd-divisor count to escape
every fixed bound along any sequence of distinct non-dyadic solutions.
