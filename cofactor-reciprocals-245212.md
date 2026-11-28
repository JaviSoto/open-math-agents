# Which primes can extend a fixed factor in A245212?

Suppose the positive integer $n=hm$ satisfies the [A245212 divisor equality](https://oeis.org/A245212), with $m>1$ and $\gcd(h,m)=1$. Fixing $h$ puts a positive lower bound on the sum of reciprocals of the **distinct primes** in $m$, even when their number and all their exponents can vary.

Write $T=h\tau(h)$, $A=\sum_{d\mid h}d\tau(d)$, $S=\sigma(h)$, and $L=\tau(m)$. Then $D=2T-A>0$ and

$$
\sum_{p\mid m}\frac1p\;\ge\;\frac{D L-S}{2T L}\;\ge\;\frac{D}{2T(S+1)} >0.
$$

In particular if precisely $r$ primes remain, the next, smallest prime is at most $2rT(S+1)/D$. When the remaining exponents are known, replace this by $2rTL/(DL-S)$. Once a prime and its exponent have been chosen, absorb that prime power into $h$ and apply the same bound again. This gives a finite, explicit search for *every* ordered prime tuple with prescribed positive exponents; no conjectural size cutoff is needed.

For example, fixing $h=6$ gives $T=24,A=35,S=12$. With two distinct new primes, $L\ge4$. Their smaller prime is at most $96L/(13L-12)\le9.6$, so it must be **5 or 7**. This first test uses no information about the two exponents. It alone does not rule out the two remaining cases.

**Proof.** Write $W(t)=\sum_{d\mid t}d\tau(d)$. Multiplicativity gives
$A W(m)+S\sigma(m)=2TLm$. In $W(m)$ the largest divisor alone contributes $mL$; also $\sigma(m)>m$. Thus $DL-S$ is a positive integer. In the other direction $W(m)\le L\sigma(m)$, since each divisor of $m$ has at most $L$ divisors. The elementary inequality $\varphi(m)\sigma(m)\le m^2$ follows on prime powers from the geometric sum and then by multiplicativity. Combining these inequalities gives

$$
(DL-S)m\le 2TL(m-\varphi(m)).
$$

Euler’s product and the union bound give $1-\varphi(m)/m\le\sum_{p\mid m}1/p$. Putting $E=DL-S\ge1$, we have $DL=E+S\le(S+1)E$, giving the exponent-independent lower bound. Summing $p_{\min}/p\le1$ proves the least-prime estimate.

The [standalone Lean proof](CofactorHarmonicResearch245212.lean) starts with the original OEIS equation. Check it in the pinned Formal Conjectures checkout with `lake env lean /path/to/CofactorHarmonicResearch245212.lean`. The final declarations are `OMA.CofactorHarmonic245212.count_sensitive` and `.least_prime`.
