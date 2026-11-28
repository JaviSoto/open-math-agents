# A bound from either odd-prime exponent

Suppose \(n=2^k p^a q^d\), where \(p,q\) are distinct odd primes, \(a\ge1\), and \(d\ge2\). If \(n\) satisfies the [A245212](https://oeis.org/A245212) equality, then
\[
 k+1\le512(d+1)^4,\qquad a+1\le32768(d+1)^6.
\]
In particular **a bound on either odd exponent alone gives effective finiteness**, with both primes, the other odd exponent and the power of two initially unrestricted. The [standalone Lean proof](ComplementaryResearch245212.lean) proves the intermediate inequality \(a+1\le64(d+1)^2(k+1)\) directly from the original equality for every \(d\ge1\). The final bound on \(k\) below is a written argument. The explicit [\(d=1\)](linear-power-family-245212.md) and [\(d=2\)](quadratic-power-family-245212.md) analyses exclude those two cases entirely. This argument does not exclude every \(d\).

Let \(h=d+1\ge3,\ b=a+1,\ K=k+1,\ z=2^K,\ G=z-1,\ \delta=K/G,\ \gamma=k+\delta,\ P=p^a,\ u=p-1\). Write
\[
 J=hq^d,\quad V=W(q^d),\quad S=\sigma(q^d),\qquad
 s=\sigma(P)/P=(p-P^{-1})/u,\quad w=W(P)/P=(bp-s)/u ,
\]
where \(W(n)=\sum_{r\mid n}r\tau(r)\). [Sahu's dyadic identity](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5390) is \((1+\gamma)bJ=\gamma Vw+Ss\). Because \(p,q\ge3\),
\[
 1<s\le3/2,\quad b<w\le3b/2,\quad w-b\le b/u,\quad s-1\le1/u,\qquad
 S\le(3/2)q^d,\quad V\le(3/2)h q^d,\quad 0<V-J\le(3/2)d q^{d-1}.
\]
The last inequality follows by bounding each lower coefficient of \(V-J\) by \(d\) and summing a geometric series. Likewise \(S-q^d\le(3/2)q^{d-1}\).

**Small \(b\).** If \(b<16h^2\), the odd divisor count \(t=bh\le16h^3\). The published [divisor envelope](divisor-envelope-245212.md) gives \(K\le t(2\lfloor\log_2(8t^3)\rfloor+2)\le16h^3(32+18h)\le512h^4\), since \(\log_2 h\le h\). The asserted bound on \(b\) is immediate. We may now assume \(b\ge16h^2\).

## Removing the two possible resonances

Set \(A=bu^2 J-upS,\ H=bu(pV-uJ)-pV,\ C(v)=vV-uS\). Then \(H>0\), as \(pV-uJ\ge V\) and \(bu>p\). Clearing the dyadic identity gives
\[
 A-kH-\delta H=C(\gamma)/P. \tag{1}
\]
Suppose \(A=kH\). Then \(C(k)<C(\gamma)<0\), so \(k<u\), and
\[
 H C(k)=bu^2[J(V-S)-pS(V-J)].
\]
Since \(V-S\ge d q^d\), it follows that \(p>(4h/9)q>q\). Reduction of \(A-kH=0\) modulo \(p\) gives \(p\mid bhq^d(k+1)\), hence \(p\mid bh\). Also \(P\delta H=-C(\gamma)<uS<p^{d+2}\), so
\[
 p^{a-d-2}<2^K\le2^{p-1}. \tag{2}
\]
If \(p\le2d+4\), then \(a\ge2d+4,\ p\ge5\) imply \(p^{a-d-2}\ge4^{d+2}>2^{p-1}\). Otherwise \(p>h\) so \(p\mid b\) and \(a\ge p-1\). Now \(2(a-d-2)\ge p-1\) since \(p\ge2d+5\), again contradicting (2). Thus \(A-kH\ne0\).

The other limit uses
\[
 D(v)=hb(1+v)-hv w-s,\qquad L(v)=hbu(u-v)+(hv-u)p .
\]
Direct expansion gives
\[
 u^2D(\gamma)=L(k)+h\delta(p-bu)-(h\gamma-u)/P. \tag{3}
\]
If \(L(k)=0\), then \(h(k-u)(bu-p)=dup\). But \(\gcd(bu-p,u)=1\), so \(bu-p\mid dp\), impossible because \(bu-p>dp\). Thus \(L(k)\ne0\). The general cleared identity, resonance consequences and integer pole obstruction are [kernel-checked](QuadraticPowerGap245212.lean).

## Estimates before the cutoff

* **\(\min(p,q)\le5K\).** In \(1-Ss/(bJ)=\gamma[Vw/(bJ)-1]\) the left side is at least \(1-9/(4bh)\ge31/32\); the right is at most \(15K/(4\min(p,q))\) by \(V/J\le1+1/(q-1)\) and \(w/b\le1+1/(p-1)\).
* **The two cofactor bounds** are
  \[
  P\le2hz(K+p)q^d,\qquad 0<D(\gamma)\le3hKb/q. \tag{4}
  \]
  The first is the [prime-power divisor bound](PrimePowerDiv245212.lean) applied with cofactor \(2^kq^d\). For the second, \(q^dD(\gamma)=\gamma w(V-J)+s(S-q^d)\); apply the local estimates above.
* **\(b\le64h^2K\).** Set \(E=2^{16h^2}\). If \(q\le5K\), (4) gives \(p^{a-1}\le4h5^d zK^{d+1}\), which suffices since \(K\le2^K\). If \(p\le5K\), then \(L(\gamma)>0\): for \(h\gamma-u>0\) use (3) and \(D(\gamma)>0\); otherwise use \(hbu(u-\gamma)>(u-h\gamma)p\). The denominator of \(L(\gamma)\) divides \(G\). Either \(P\le2(h+5)zK\), or (3) gives \(D(\gamma)\ge1/(2Gu^2)\), so \(q\le6hKbGu^2\le150hzbK^3\). In both cases
  \[
  P\le E z^h b^d K^{3d+1},
  \]
  since \(12h(150h)^d\le E\). For \(b\ge16h^2\), \(d\log_2 b\le d\sqrt b\le b/4\le a/2\). Thus \(a/2\le 16h^2+(4d+2)K\), giving the claimed bound.
* **\(P\ge z^{1/h}/(6hKb)\).** The rational \(D(k)=D(\gamma)+h\delta(w-b)>0\) has denominator dividing \(P\). If \(2hKbP\le G\), then \(D(\gamma)\ge1/(2P)\) and \(q\le6hKbP\). The original equality modulo \(z\) gives \(z\mid W(P)V-\sigma(P)S\), a positive number. Thus \(z<W(P)V\le3h b P q^d\le(6hKbP)^h\). In the other case \(P>G/(2hKb)\ge z/(4hKb)\).

## Bounding \(K\)

If \(z^{1/h}\le E K^{h+2}\), we already have a fixed-degree polynomial upper bound for \(2^K\). Otherwise write \(B=E K^{h+1}\). We show \(p,q\le B\).

* If \(q\le5K\), the positive \(D_q=bJ(1+\gamma)-\gamma bV-S=\gamma V(w-b)+S(s-1)\) increases to an integer when \(\gamma\) is replaced by \(k\). The increase is \(\delta b(V-J)\le2h(64h^2)5^{d-1}K^{d+1}/G<1/2\). Here \(G\ge z^{1/h}\) for \(z\ge4,\ h\ge3\) and \(E\ge4h(64h^2)5^{d-1}\). Consequently \(1/2\le D_q\le(2h Kb q^d)/u\), giving \(p\le 1+4h(64h^2)5^d K^{d+2}\le B\).
* If \(p\le5K\), the difference between \(u^2D(\gamma)\) and \(L(k)\) is at most
  \[
  \frac{5h(64h^2)K^3}{G}+
  \frac{6h(h+5)(64h^2)K^3}{z^{1/h}}<\tfrac12
  \]
  by the fourth estimate and \(E\ge8192h^4\). Positivity of \(D(\gamma)\) and nonvanishing of integer \(L(k)\) now give \(D(\gamma)\ge1/(2u^2)\), so \(q\le6hKb p^2\le150h(64h^2)K^4\le B\).

Since \(b,p,q,K\le B\), we have \(H\le bp^2 V\le 2hB^{d+3}\), \(|C(\gamma)|\le4hB^{d+1}\) and \(z/P<3h b q^d\le3hB^{d+1}\). The nonzero integer in (1) implies
\[
 z\le1+KH+(z/P)|C(\gamma)|\le16h^2 B^{2d+3}.
\]
Combining the two cases, put \(s_0=(h+1)(2h+1)\) and \(T=16h^2(2h+2)\). We have \(2^K\le2^T K^{s_0}\). If \(K>\max(16,2T,4s_0^2)\), then \(T+s_0\log_2 K\le T+s_0\sqrt K<K\), a contradiction. The maximum is at most \(512h^4\) for \(h\ge3\). This gives \(K\le512h^4\) and \(b\le64h^2K\le32768h^6\).

**Effective finite test.** Once \(K,b\) are bounded, the smaller prime is at most \(5K\) in the large-\(b\) case; the small-\(b\) case already has the explicit [whole-input bound](divisor-envelope-245212.md). Alternatively, since all real exponents are positive, the same minimum-prime estimate with \(1-9/(4bh)\ge5/8\) gives \(\min(p,q)\le6K\) for all \(b\ge2,\ h\ge3\). Having chosen which prime is smaller, select it and its exponent. With \(m_0\) the product of its power and \(2^k\), the remaining prime divides the strictly positive integer \(W(m_0)+\sigma(m_0)\): reduce the original equality modulo this prime. The known exponent also permits the [exact leading digit](odd-divisor-count-245212.md), so factoring that integer is unnecessary.
