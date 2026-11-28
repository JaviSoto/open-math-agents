# What survives after an exact first Euler resonance

Fix $h>0$, and write $A=W(h)=\sum_{d\mid h}d\tau(d)$, $S=\sigma(h)$ and $H=2h\tau(h)$. A solution of [OEIS A245212](https://oeis.org/A245212) satisfies $W(n)+\sigma(n)=2n\tau(n)$. Suppose an odd prime $p\nmid h$ satisfies the exact Euler equality $Ap=H(p-1)$. Put $u=p-1$, $B=a+1$, $P=p^a$, $g=hP$, $A'=W(g)$ and $H'=2g\tau(g)$.

**No second exact Euler equality is possible after adjoining this prime power.** For every finite set $I$ of new primes disjoint from $p$, even of unbounded cardinality,
$$
 A'\prod_{s\in I}s\ne H'\prod_{s\in I}(s-1).
$$
The conclusion includes $I=\varnothing$. For a bounded number of fresh odd primes we also give a uniform lower bound for the difference divided by $\prod(s-1)$. In an actual solution this forces both the size and the exponent of at least one new prime to be bounded by polynomials in $a$.

## The integer identity

For arbitrary nonnegative $N,D$, set $\Delta=H'D-A'N$ and $L=N-uB(N-D)$. The geometric sums for $U=\sigma(p^a)$ and $V=W(p^a)$ satisfy $uU=pP-1$ and $u^2 V=p(Bu-1)P+1$. Substitution and $Ap=Hu$ give
$$
 u^2\Delta=A[pP L-N].
$$
If $p\nmid N$, the bracket is nonzero modulo $p$. This proves the first assertion for $N=\prod s$, $D=\prod(s-1)$ and every subset thereof. If $N$ is odd then so is $L$, so the same identity immediately gives $2u^2|\Delta|\ge ApP$ whenever $2N\le pP$.

## A gap uniform in the fresh primes

For $t=uB$, let $C=\operatorname{budget}(t-1,r)$, with
$$
 C_0(A)=1,\qquad C_{j+1}(A)=\max\{2C_j(A),[2+2A\,2^j C_j(A)]^{j+1}\}.
$$
Here $r$ bounds $|I|$, and $\operatorname{budget}(A,j)=C_j(A)$. For any subset of odd bases, $L=tD-(t-1)N$ cannot vanish: its two terms have opposite parity. The finite Euler-product separation lemma therefore gives $D\le C|L|$. Also $N\le2^rD$. Hence when $2^{r+1}C\le pP$, the triangle inequality gives $pP D\le 2C|pPL-N|$. No upper bound on the largest new prime is needed. We have proved
$$
        2C u^2 |\Delta| \ge ApP D .
$$

This applies from an explicit exponent onwards. Put $d_0=1$ and $d_{j+1}=(1+j+d_j)(j+1)$. Induction gives $C_j(A)\le [4(A+1)]^{d_j}$. For
$$
a\ge \max\{16(d_r+1)^2,\;2^{r+1}(8p)^{d_r}\},
$$
the elementary bound $a^{2d_r}\le2^a$ implies $2^{r+1}C\le pP$.

## What an actual extension must contain

Suppose $gm$ is a solution, where $m>1$ is odd and coprime to $g$, and put $r=\omega(m)$, $T=\tau(m)$. For the smallest prime $q\mid m$, the integer mass inequality and the absorbed identity $u(H'-A')=AU$ give
$$
  AT>Su,\qquad q(AT-Su)\le rApBT,\qquad
  q\le rAp(Su+1)B.
$$
For clarity, the mass inequality before cancellation is $q[(H'-A')T-SU]\le rH'T$. Multiply by $u$, use $uH'=ApBP$ and $U\ge P$. Finally $T\le(Su+1)(AT-Su)$ because $AT-Su$ is a positive integer and $A\ge1$.

There is also a lower bound on **every** $q\mid m$, not just the smallest. Let $b=v_q(m)\ge1$, and $Q=q^b$. Omitting the other factors from the normalized weighted moment gives $uV W(q^b)<pBP(b+1)Q$. Indeed any coprime factor $z$ has $W(z)\ge z\tau(z)$, and the omitted ordinary divisor sum is positive. The top two divisors of $q^b$ give $bQ\le q[W(q^b)-(b+1)Q]$. Together with $uV+U=pBP$ and $uU=pP-1$ this proves
$$
                     uBb<q(b+1)+b.
$$
In particular $uB\le2q$. The smallest fresh base is thus comparable to $a+1$, with constants depending only on $h,p,r$. We do not assert an upper bound of this order on all fresh primes.

More importantly, define
$$
       M=6 C u^2\bigl(B r 2^r+S\bigr).
$$
Above the displayed onset, **some $q\mid m$ simultaneously satisfies**
$$
 v_q(m)\le M,\qquad q\le\max\{M+1,\,rAp(Su+1)B\}.
$$
Both bounds are polynomials in $a$ up to a constant depending on $h,p,r$, since $C\le (4uB)^{d_r}$.

Here is why the same prime meets both bounds. If all exponents are at most $M$, choose the least prime. Otherwise suppose every base at most $M+1$ has exponent greater than $M$. In the normalized weighted product replace the factors of these smaller bases by their Euler limits $q/(q-1)$, and all other factors by $1$. Each change has magnitude at most $2/(M+1)$; the product of the ordinary normalized factors is at most $2/(M+1)$ because at least one exponent exceeds $M$. Telescoping the product of the weighted factors (each is at most $2$) gives
$$
       (M+1)|A'N/D-H'|\le 2A'r2^r+2\sigma(g).
$$
The preceding uniform gap bounds the left side below by $(M+1)ApP/(2Cu^2)$. But $2W(p^a)\le3BP$ and $2\sigma(p^a)\le3P$ give $2Cu^2(2A'r2^r+2\sigma(g))\le MApP$, a contradiction. This improves the exponential dependence on $a$ that results from treating $hp^a$ as an arbitrary cofactor.

## A separate obstruction to a zero leading coefficient

Take any finite set of remaining odd bases $s>1$, with positive integer lengths $\ell_s$ (exponent plus one). Write $R=\prod s$, $D=\prod(s-1)$, $J=(Bu-1)\prod_s(\ell_s(s-1)-1)$. Its factors, as well as $R$, are odd. The vanishing of the full leading coefficient after clearing squares of the Euler denominators would give
$$
 HK(uD)^2=pR(AJ+SuD),\qquad K=B\prod_s\ell_s.
$$
Since $Ap=Hu$ and $\gcd(p,u)=1$, we have $H=pc$ and $A=uc$. Cancelling $pu$ yields
$$c(KuD^2-RJ)=RSD.$$
The bracket is positive and odd. Consequently
$$
                v_2(H)=v_2(S)+\sum_s v_2(s-1).
$$
Violation precludes a zero leading coefficient for *all* exponent choices on that support. This is a necessary condition on the leading term, not on every exact solution: lower terms are present at finite exponents.

## Replay and scope

[FreePoleHereditaryResearch245212.lean](FreePoleHereditaryResearch245212.lean) includes the proofs and axiom audits for `inherited`, `polynomial`, the explicit onset, the least/every-prime inequalities, the leading-coefficient condition and the polynomial atom bound. It imports only the pinned Formal Conjectures OEIS module; run `lake env lean -j 1 -DElab.async=false /absolute/path/to/FreePoleHereditaryResearch245212.lean` in that checkout. The proof reuses the [two-free-prime height](two-free-effective-245212.md) project's geometric-sum identities, harmonic inequality and separated Euler products.

This controls a singleton resonance with **any** fixed number of additional prime factors. In particular it applies when two follow the resonant prime in a three-free-prime problem. The bounds depend on $a$. They do not give an absolute height for three free prime powers at arbitrary $h$; they also do not treat a first resonance supported on two primes.
