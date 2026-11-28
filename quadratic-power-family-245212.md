# No A245212 equality at \(2^k p^a q^2\)

Let \(p,q\) be distinct odd primes and \(a\ge1,\ k\ge0\). Then \(2^k p^a q^2\) does not satisfy the [A245212](https://oeis.org/A245212) equality. Together with the [linear-factor theorem](linear-power-family-245212.md), this shows that a solution with two different odd prime factors must have **both odd-prime exponents at least three**. Neither prime nor exponent is bounded in the hypothesis.

Write \(W(n)=\sum_{d\mid n}d\tau(d)\). The equation is \(W(n)+\sigma(n)=2n\tau(n)\). The odd part has \(3(a+1)\) divisors, so the [published exclusion up to 71](odd-count-sieve-245212.md) covers \(a\le22\). Henceforth \(a\ge23\). Put
\[
 K=k+1,\quad z=2^K,\quad G=z-1,\quad F=1+kz,\quad
 \delta=K/G,\quad \gamma=F/G=k+\delta,\quad P=p^a,\quad u=p-1,\quad b=a+1.
\]
Thus \(0<\gamma\le K\) and \(b\ge24\). Define
\[
 J=3q^2,\quad V=3q^2+2q+1,\quad S=q^2+q+1,\qquad
 s=\frac{\sigma(P)}P=\frac{p-P^{-1}}u,\quad w=\frac{W(P)}P=\frac{bp-s}u .
\]
Here \(1<s\le3/2\), \(b<w\le3b/2\), \(w-b\le b/u\) and \(s-1\le1/u\). By [Sahu's separation of the dyadic factor](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5390), equivalently by direct multiplication of the three local divisor sums, equality means
\[
 (1+\gamma)bJ=\gamma Vw+Ss. \tag{1}
\]

## Two integer separations

Set \(A=bu^2J-upS,\ H=bu(pV-uJ)-pV,\ C(v)=vV-uS\). Since \(pV-uJ\ge V\) and \(bu>p\), \(H>0\). Substitution of the finite sums in (1) gives
\[
 A-kH-\delta H=C(\gamma)/P. \tag{2}
\]
Suppose \(A=kH\). Then \(C(k)<C(\gamma)<0\), and multiplying \(C(k)\) by \(H\) gives
\[
 H C(k)=bu^2[J(V-S)-pS(V-J)].
\]
Since \(V-S\ge 2q^2,\ S\le3q^2/2,\ V-J=2q+1\le3q\), this forces \(p>(4/3)q\), hence \(p\ge5\) and \(q<p\). From \(C(k)<0\) and \(V>S\) we get \(k<u\). Reducing \(A-kH=0\) modulo \(p\) gives \(p\mid bJ(k+1)\). Since \(J=3q^2,\ p>q\ge3,\ 0<k+1<p\), we get \(p\mid b\) and \(a\ge p-1\). But \(P\delta H=-C(\gamma)<uS<p^3\), so \(p^{a-3}<2^{k+1}\le2^{p-1}\). For \(p\ge7\), \(p^{a-3}\ge4^{p-4}\ge2^{p-1}\); for \(p=5\) use \(a\ge23\). Thus **\(A-kH\ne0\)**.

For the other separation put
\[
 L(v)=3bu(u-v)+(3v-u)p,\qquad D(v)=3b(1+v)-3vw-s.
\]
Equation (1) gives \(0<D(\gamma)=(2\gamma w+s)/q+(\gamma w+s)/q^2\le4Kb/q\), and expansion gives
\[
 u^2 D(\gamma)=L(k)+3\delta(p-bu)-(3\gamma-u)/P. \tag{3}
\]
If \(L(k)=0\), then \(3(k-u)(bu-p)=2up\). As \(\gcd(bu-p,u)=1\), \(bu-p\) divides \(2p\). But \(bu-p>2p\) for \(b\ge5,\ p\ge3\). Thus **\(L(k)\ne0\)**.

## Uniform estimates

1. **\(\min(p,q)\le5K\).** Dividing (1) by \(bJ\), the deficit \(1-Ss/(bJ)\) is at least \(31/32\). On the other side it equals \(\gamma[Vw/(bJ)-1]\). Since \(w/b\le1+1/u\) and \(V/J\le1+1/(q-1)\), the latter is at most \(15K/[4\min(p,q)]\) (use \(1/(r-1)\le3/(2r)\), and \(r-1\ge2\)).
2. The [prime-power divisor bound](PrimePowerDiv245212.lean) applied with cofactor \(2^k q^2\) gives
   \[
   P\le |F V-uGS|\le4z(K+p)q^2. \tag{4}
   \]
   If \(q\le5K\), this gives \(p^{a-1}\le200zK^3\), hence \(b\le64K\).
3. If \(p\le5K\), we also have \(b\le64K\). Indeed \(L(\gamma)>0\): for \(3\gamma-u>0\) use (3) at \(\gamma\) and \(D(\gamma)>0\); for \(3\gamma-u\le0\) use \(3bu(u-\gamma)>(u-3\gamma)p\). The denominator of \(L(\gamma)\) divides \(G\). If \(P\le2G(3K+p)\le16zK\), the bound on \(b\) follows. Otherwise (3) gives \(D(\gamma)\ge1/(2Gu^2)\). Thus \(q\le8GKb p^2\le200zbK^3\), and by (4)
   \[
   P\le 2^{20}z^3 b^2K^7. \tag{5}
   \]
   This also holds in the short case \(P\le16zK\). Since \(b^2\le 2^{a/2}\) for \(b=a+1\ge24\) (induction), \(2^{a/2}\le2^{20+10K}\), proving \(b\le64K\).
4. **\(P\ge2^{K/3}/(12Kb)\).** The positive \(D(k)=D(\gamma)+3\delta(w-b)\) is an integer divided by \(P\). If \(6KbP\le G\), then \(D(\gamma)\ge1/P-3Kb/G\ge1/(2P)\), so \(q\le8KbP\). From the original equation, \(z\mid W(P)V-\sigma(P)S\) (reduce modulo \(z\)); the difference is positive. Consequently
   \[
   z<W(P)V<6bPq^2\le384K^2b^3P^3 .
   \]
   Otherwise \(P>G/(6Kb)\ge z/(12Kb)\), also sufficient.

## Absolute cutoff

Suppose \(K\ge224\). At 224 and hence throughout this range
\[
 G>3840K^3,\qquad 2^{K/3}>24576K^3,\qquad 2^K>2^{71}K^{18}. \tag{6}
\]
For propagation, \((1+1/K)^j\le\sum_{i=0}^j(j/K)^i<2\) for \(j\le18\); take cubes in the middle comparison.

If \(q\le5K\), the strictly positive quantity \(D_q=bJ(1+\gamma)-\gamma bV-S\) equals \(\gamma V(w-b)+S(s-1)\). Replacing \(\gamma\) by \(k\) increases it to a positive integer, and changes it by at most \(\delta b(V-J)\le704K^3/G<1/2\). Hence \(1/2\le D_q\le5Kb q^2/u\); this gives \(p\le 1+16000K^4<2^{14}K^4\).

If \(p\le5K\) then (3), with estimate 4, gives
\[
 |u^2D(\gamma)-L(k)|\le960K^3/G+6144K^3/2^{K/3}<1/2 .
\]
Since \(L(k)\) is a nonzero integer and \(D(\gamma)>0\), this yields \(D(\gamma)\ge1/(2u^2)\), hence \(q\le8Kb p^2<2^{14}K^4\).

Now \(A-kH\) is a nonzero integer by (2). Multiplying (2) by \(G\) and using \(z/P<6bq^2\) yields
\[
 z\le1+KH+6bq^2|C(\gamma)|.
\]
In either case \(H\le bp[3q^2+3pq]<2^{39}K^{10}\), because \(pV-uJ=3q^2+p(2q+1)\). Use \(|C(\gamma)|\le(4K+2p)q^2\). When \(q\le5K,\ p<2^{14}K^4\), this gives \(|C|<2^{20}K^6,\ 6bq^2<2^{14}K^3\). When \(p\le5K,\ q<2^{14}K^4\), it gives \(|C|<2^{32}K^9,\ 6bq^2<2^{37}K^9\). In both cases \(z<2^{71}K^{18}\), contradicting (6).

We have now proved \(K<224\). If \(p\le5K\) then \(p<1120\) and (5) gives \(P<2^{776}<3^{500}\). Otherwise \(q\le5K\), hence \(p^{a-1}\le200zK^3<2^{256}\). Since \(a\ge23\), this implies \(p<4096,\ a<500\). The other prime \(q\) requires no bound for the finite replay.

## Exact finite calculation

For \(1\le K<224,\ 23\le a<500\) and every odd prime \(p<4096\), set \(A_0=F W(P),\ U=G\sigma(P),\ D_0=3zKbP-3A_0-U,\ N=2A_0+U,\ M=A_0+U\). The original equation is
\[
 D_0q^2=Nq+M.
\]
Thus \(D_0>0\) and \(0<q-N/D_0=M/(D_0q)<1\) since \(M\le N<D_0q\). The only possible integer is \(\lfloor N/D_0\rfloor+1\). Its substitution tests equality exactly, including possible composite candidates.

    python3 quadratic_power_family_245212.py

The [program](quadratic_power_family_245212.py) generates 563 odd primes by trial division and visits all 59,886,873 triples. The necessary cofactor bounds (4) and (5) leave 1,104,936. Exactly 627,889 have positive denominator; zero produce an integer root. All sums and comparisons are integer operations.
