# An effective bound using only the number of odd divisors

Write $n=2^a m$ with $m>1$ odd, $t=\tau(m)$, and suppose $n$ satisfies
the equality in [OEIS A245212](https://oeis.org/A245212). Then

$$
 2^a \le [4(a+2)t^2]^t,\qquad
 m\le[(2^{a+1}-1)(a+2)t^2]^{t-1}.                         \tag{1}
$$

In particular $a=O(t\log(2t))$ and $\log n=O(t^2\log(2t))$. When
$a=0$ the second bound alone gives $\log n=O(t\log(2t))$.
Thus bounding the number of **odd divisors** suffices for effective
finiteness, even if the power of two and all the prime bases are allowed
to vary. This does not bound $t$ absolutely.

## An Egyptian-fraction identity

Use $T=m\tau(m)$, $A=\sum_{d\mid m}d\tau(d)$, $S=\sigma(m)$ and put
$\delta=(a+1)/(2^{a+1}-1)$. The local factors at two are respectively
$(a+1)2^a$, $1+a2^{a+1}$ and $2^{a+1}-1$. Thus the equality at $n$ gives

$$ T-S=(a+\delta)(A-T).                                    \tag{2} $$

This holds also at $a=0$, where $\delta=1$. It is the inversion used in
[reduction #5390](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5390).
Dividing (2) by $m$ and replacing each divisor by its complement gives

$$ t-1=\sum_{\substack{d\mid m\\d>1}}
               \frac{(a+\delta)\tau(m/d)+1}{d}.               \tag{3} $$

All terms are positive. For example, if $m=p^e$ then
$(p-1)(A-T)=T-S$, by telescoping the prime-power sums. An odd prime
would therefore have to satisfy $p-1=a+\delta$. For $a\ge1$ this is
not an integer, while for $a=0$ it would give $p=2$. This excludes
all $2^a p^e$ with $p$ odd and $e>0$.

## Truncating at the smallest prime factors

Write $m=\prod_{i=1}^r p_i^{e_i}$ with the primes in strictly increasing
order, and $m_j=\prod_{i=1}^j p_i^{e_i}$, so $m_0=1$. Omitting terms of
(3) whose denominators do not divide $m_j$ leaves a tail of at most
$t$ terms. Each omitted denominator is at least $p_{j+1}$. Also
$0<\delta\le1$, and $\tau(m/d)\le t$.

First subtract from $t-1$ the sum over $1<d\mid m_j$ using the integer
coefficient $a$ in place of $a+\delta$. The result $E_j$ is strictly
positive, for every $0\le j\le r$: at $j=r$ the $\delta$-part is
still positive since $m>1$, and at $j<r$ there is a positive tail.
Its denominator divides $m_j$. Splitting $E_j$ into a $\delta$-part
and a tail, and using $\delta\le(a+1)2^{-a}$, gives

$$
 1/m_j\le E_j\le (a+2)t^2(2^{-a}+1/p_{j+1}),                 \tag{4}
$$

where the last summand is omitted at $j=r$. Put $H=4(a+2)t^2$.
For each $j<r$, either $2^a\le H m_j$ or $p_{j+1}\le Hm_j$;
otherwise (4) would give $1/m_j<1/(2m_j)$. At $j=r$ only the first
alternative remains. Until that alternative occurs we have

$$ Hm_{j+1}=(Hm_j)p_{j+1}^{e_{j+1}}
                  \le (Hm_j)^{e_{j+1}+1}. $$

Induction therefore bounds $2^a$ by
$H^{\prod_i(e_i+1)}=H^t$, proving the first assertion.

For the second bound subtract the *exact* terms $1<d\mid m_j$ from (3).
For $j<r$ the remainder is strictly positive, with denominator dividing
$(2^{a+1}-1)m_j$. The tail estimate now gives

$$
 \frac1{(2^{a+1}-1)m_j}\le \frac{(a+2)t^2}{p_{j+1}} .
$$

Writing $K=(2^{a+1}-1)(a+2)t^2$, induction as above yields
$K m\le K^t$. This proves (1).

To see the asserted asymptotic for $a$, put $s=a/t$ and take base-two
logarithms in the first inequality of (1). Since $a+2\le t(s+2)$,
$s\le 2+3\log_2 t+\log_2(s+2)$. For $s\ge8$ the last logarithm is
at most $s/2$. Substitute this bound for $a$ into $\log K$ in the
second inequality. Both conclusions have absolute implied constants.

These are uniform bounds rather than an efficient enumeration: at
large $t$ the bound on $m$ is far beyond a direct search.
