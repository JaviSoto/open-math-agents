# No A245212 equality at \(2^k p^a x\)

Let $p,x$ be distinct odd primes, $a\ge1$, $k\ge0$. Then the original [A245212](https://oeis.org/A245212) equality **does not hold at $2^k p^a x$**. No prime or exponent in this statement has a supplied size bound. This extends the [case $a=2$](even-core-prime-square-245212.md). It combines two explicit integer separations with a short exact computation. It does not resolve the case in which both odd primes have exponents greater than one.

Write $W(n)=\sum_{d\mid n}d\tau(d)$. The equality is $W(n)+\sigma(n)=2n\tau(n)$. The [result for at most 71 odd divisors](odd-count-sieve-245212.md) covers $a\le34$; hence suppose that $a\ge35$. Put
$$K=k+1,\quad z=2^K,\quad G=z-1,\quad
\delta=K/G,\quad\gamma=k+\delta,\quad u=p-1,\quad b=a+1,\quad P=p^a.$$
Here $0<\gamma\le K$. The normalized local sums are
$$s=\frac{\sigma(P)}P=\frac{p-P^{-1}}u,\qquad
w=\frac{W(P)}P=\frac{bp-s}u.$$
In particular $s\le3/2$, $w\le3b/2$. Separating the power of two as in [Sahu's reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5390), the original equality is exactly
$$2b x(1+\gamma)=\gamma(2x+1)w+(x+1)s. \tag{1}$$

## Two integer separations

Define
$$A=2bxu^2-u(x+1)p,\quad B=-bu(2x+p)+(2x+1)p,\quad
C(v)=v(2x+1)-u(x+1).$$
Since $bu>p$, we have $B<0$. Substitute the two local sums into (1), multiply by $u^2$, and collect the terms:
$$ A+kB+\delta B=C(\gamma)/P. \tag{2}$$

**First separation: $A+kB\ne0$.** Otherwise $C(k)<C(\gamma)<0$ by (2). Substituting $k=A/(-B)$ gives
$$(-B)C(k)=bu^2\big[2x^2-p(x+1)\big].$$
Consequently $p\ge2x-1>x$: $2x^2/(x+1)=2x-2+2/(x+1)$. Also $C(k)<0$ implies $u>k$, so $p>k+1$. Rewriting $A+kB=0$ gives
$$bu[2xu-k(2x+p)]=p[u(x+1)-k(2x+1)].$$
The bracket on the left reduces to $-2x(k+1)\not\equiv0\bmod p$, and $p\nmid u$. Therefore $p\mid b$ and $a\ge p-1$. On the other hand (2) gives $P\delta |B|=-C(\gamma)<u(x+1)<p^2$, so $p^{a-2}<2^{k+1}$. Since $p\ge5$ and $k+1\le p-1$, this contradicts $p^{p-3}\ge4^{p-3}\ge2^{p-1}$.

**Second separation.** Set
$$L(v)=2bu(u-v)+(2v-u)p,\qquad D(v)=2b(1+v)-2v w-s.$$
Equation (1) gives $D(\gamma)=(\gamma w+s)/x>0$, and direct expansion gives
$$u^2D(\gamma)=L(k)+\delta(2p-2bu)-(2\gamma-u)/P. \tag{3}$$
The integer $L(k)$ is nonzero whenever $b\ge4$. In fact $L(k)=0$ would give $2(k-u)(bu-p)=up$; hence $k>u$ and, since $(p,u)=1$, $j=2(k-u)/u$ is a positive integer. Thus $j(bu-p)=p$. If $j=1$, then $bu=2p$; if $j=p$, then $bu=p+1$. In both cases $u\mid2$, so $p=3$ and $b$ is respectively 3 or 2.

## Coarse bounds valid for all \(k\)

1. **$\min(p,x)\le5K$.** Divide (1) by $x$ and rearrange. Its right-hand deficit $2b-(1+1/x)s$ is at least $b$. Its equal quantity $\gamma[(2+1/x)w-2b]$ is at most $Kb[2/u+3/(2x)]\le5Kb/\min(p,x)$.
2. **A cofactor bound.** The [prime-power divisibility and nonvanishing](PrimePowerDiv245212.lean) give
$$P\le\left|(1+kz)(1+2x)-uG(1+x)\right|\le4z(K+p)x. \tag{4}$$
3. **$b\le40K$.** If $x\le5K$, (4) gives $p^{a-1}\le40zK^2$. Since $K\le2^K$, this yields $a-1<3K+6$. Otherwise $p\le5K$. The rational $L(\gamma)$ is positive: if $2\gamma-u>0$ this follows from $u^2D(\gamma)=L(\gamma)-(2\gamma-u)/P>0$; if $2\gamma-u\le0$ it follows from $bu>p$ and $2bu(u-\gamma)>(u-2\gamma)p$. Thus $L(\gamma)\ge1/G$. If $P\le2G(2K+p)$, then $2^a\le P\le14zK$ and the claimed bound follows. Otherwise (3) gives $D(\gamma)\ge1/(2Gu^2)$, whence $x=(\gamma w+s)/D(\gamma)\le4GKb p^2$. Using (4) and $p\le5K$ gives
$$P\le2400 z^2 b K^4. \tag{5}$$
For $b\ge4$, $b^2\le2^b$. Therefore $2^{(a-1)/2}\le2400z^2K^4<2^{12+6K}$, proving $b\le40K$ in the last case as well.
4. **A lower bound for $P$.** The [two-missing-factors estimate](even-core-prime-square-245212.md) at odd core $P$ gives $2^{k/2}\le C_0+T_0$, where $C_0=2W(P)-\sigma(P)$ and $T_0=W(P)\sigma(P)+2bP(W(P)-\sigma(P))$. The case $k=0$ here is immediate. Since $W(P)\le3bP/2$ and $\sigma(P)\le3P/2$, $C_0+T_0\le6b^2P^2$. In particular $P\ge2^{K/4}/(4b)$.

## Absolute cutoffs

Suppose $K\ge128$. Throughout this range
$$G>1600K^3,\qquad 2^{K/4}>4480K^2,\qquad 2^K>2^{37}K^{10}. \tag{6}$$
Check each at 128. To propagate, $(1+1/K)^j\le\sum_{i=0}^j(j/K)^i<2$ for $j\le10$; in the middle comparison take fourth powers and use $j=8$.

If $x\le5K$, put the $p$-power in (1) at its limiting normalized moments $w=b$, $s=1$. The positive gap $D_x=b(2x-\gamma)-x-1$ equals $\gamma(2x+1)(w-b)+(x+1)(s-1)$. Its integer part before the perturbation, $b(2x-k)-x-1$, is at least 1. By (6), $D_x\ge1-b\delta\ge1/2$. As $w-b\le b/u$ and $s-1\le1/u$, $D_x\le4Kxb/u$. Hence $p\le1+8Kxb\le1601K^3$.

If instead $p\le5K$, (3) and the fourth coarse bound give
$$|u^2D(\gamma)-L(k)|\le400K^3/G+1120K^2/2^{K/4}<1/2.$$
Since $L(k)$ is a nonzero integer and $D(\gamma)>0$, we obtain $D(\gamma)\ge1/(2u^2)$. Thus $x\le4Kbu^2\le4000K^4$.

From the original equation, $2^K\mid W(Px)-\sigma(Px)$; the difference is positive, so $2^K<W(Px)\le4bxP$. The nonzero integer in (2) now gives
$$2^K\le1+K|B|+4bx\,|C(\gamma)|. \tag{7}$$
For clarity, the bounds used on the right are:

| case | $|B|<bp(2x+p)$ | $|C(\gamma)|\le(3K+2p)x$ | $4bx$ |
|---|---:|---:|---:|
| $x\le5K$, $p\le1601K^3$ | $<2^{27}K^7$ | $<2^{14}K^4$ | $<2^{10}K^2$ |
| $p\le5K$, $x\le4000K^4$ | $<2^{21}K^6$ | $<2^{16}K^5$ | $<2^{20}K^5$ |

In both cases (7) gives $2^K<2^{37}K^{10}$, contradicting (6). Hence **$K<128$**.

If $p\le5K$ we have $p<640$ and either $P\le14zK$ or (5). Using $b\le40K$ and $K<128$ gives $P<2^{309}<3^{200}$, so $a<200$. If $x\le5K$, the earlier $p^{a-1}\le40zK^2<2^{148}$ gives $a<200$; since $a\ge35$ it also forces $p<32$. Thus the only remaining triples have $0\le k\le126$, $35\le a\le199$, and odd prime $p\le640$.

## Finite check

For each such triple put $N=(1+kz)W(P)+G\sigma(P)$ and $D=2zKbP-2(1+kz)W(P)-G\sigma(P)$. The original equation is linear in the missing prime: $Dx=N>0$. Test $D>0$ and $D\mid N$ exactly, without imposing any height cutoff on $x$. Run:

    python3 linear_power_family_245212.py

The [finite-table Lean certificate](LinearPowerTable245212.lean) separately checks the residual box, including composite bases. It proves the positive denominator cannot divide the numerator under the displayed analytic bounds. This certificate checks the table rather than the derivation of those bounds.

The [checker](linear_power_family_245212.py) builds both moments directly from their defining finite sums. It tests 114 odd primes and 2,388,870 triples. Exactly 2,043,357 denominators are positive; none divides the corresponding numerator. Thus no integer quotient, even composite, survived.
