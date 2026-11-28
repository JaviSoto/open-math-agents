# Finiteness with at most two odd prime factors

There are only finitely many integers **other than powers of two** satisfying the [A245212](https://oeis.org/A245212) equality and having at most two distinct odd prime factors. Both odd primes, both odd exponents and the power of two can vary. This proof does not enumerate the exceptional finite set or establish that it is empty. Pure powers of two are genuine solutions, and are excluded from the finiteness assertion.

The prior [fixed-\(k\) theorem](dyadic-rank-two-height-245212.md) handles each individual power of two, and the [complementary-exponent theorem](complementary-exponent-245212.md) bounds every other parameter once either odd exponent is fixed. Neither finiteness statement alone covers all five parameters simultaneously. The [standalone Lean certificate](TwoOddGlobalGap245212.lean) proves the cleared four-moment identity and the integer separation used below. The bounds and two limiting arguments completing the theorem are given in this paper, not yet formalized end to end.

## Two exact integer separations

Suppose \(n=2^k p^{B-1}q^{C-1}\) satisfies the equality, with distinct odd primes \(p<q\) and integers \(B,C\ge2\). Write
\[
 K=k+1,\quad z=2^K,\quad G=z-1,\quad F=1+kz,\quad
 \delta=K/G,\quad \gamma=F/G=k+\delta,\quad
 u=p-1,\quad v=q-1,\quad P=p^{B-1},\quad Q=q^{C-1}.
\]
Put \(w_p=W(P)/P,\ s_p=\sigma(P)/P\), and similarly for \(q\), with \(W(m)=\sum_{d\mid m}d\tau(d)\). The [original dyadic balance](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5390) is \(\gamma w_p w_q+s_p s_q=(1+\gamma)BC\). Hence, for \(t=\gamma\) or \(t=k\), the real number
\[
 R_t=t w_p w_q+s_p s_q-(1+t)BC
\]
is respectively zero or \(-\delta(w_p w_q-BC)<0\).

The local moments have exact expansions
\[
 w_p=\frac{p(Bu-1)}{u^2}+\frac1{u^2P},\qquad
 s_p=\frac p u-\frac1{uP},
\]
and similarly with \(q,C,v,Q\). Define
\[
 E_t=(1+t)BCu^2v^2-pq\{t(Bu-1)(Cv-1)+uv\},
\quad
 \alpha_t=q[t(Cv-1)-uv],\quad \beta_t=p[t(Bu-1)-uv].
\]
Multiplication of the four local factors gives
\[
 u^2v^2 R_t=-E_t+\frac{\alpha_t}{P}+\frac{\beta_t}{Q}+\frac{t+uv}{PQ}. \tag{1}
\]

**Separation.** If \(k\ge2,\ C\ge16,\ p\le5K\), then neither \(E_k\) nor \(E_\gamma\) is zero. Indeed, if \(E_k=0\), reduce modulo the larger prime \(q\). Since \(u<q\) and \(q\nmid v\), it follows that \(q\mid KBC\). The identical conclusion holds if \(E_\gamma=0\): multiply by \(G\), use \(G(1+\gamma)=zK\), and note \(q\nmid z\). Also \(t(C-1/v)>u\) by \(t\ge k,\ p\le5(k+1),\ C\ge16\), so \(\alpha_t>0\). Equation (1) and \(R_t\le0\) force \(\beta_t<0\), equivalently
\[
 q>t(B-1/u)+1>\max(K,B).
\]
The final strict bound follows from \(t\ge k\ge2,\ B\ge2,\ u\ge2\). Thus \(q\mid C\), \(C\ge q>B\), and \(Q>P\). Now \(t(C-1/v)>2u\), because \(C\ge q>p\) and \(t\ge2\). Hence
\[
 \alpha_t>q u v>p u v>|\beta_t|.
\]
This gives \(\alpha_t Q+\beta_t P+t+uv>0\), contradicting (1). In particular
\[
 |E_k|\ge1,\qquad |G E_\gamma|\ge1, \tag{2}
\]
since the two quantities inside the absolute values are integers.

## Error bounds

For both \(t=k,\gamma\), \(0<t\le K\), and
\[
 |\alpha_t|\le q^2(KC+p),\quad |\beta_t|\le p^2(KB+q),\quad t+uv\le K+pq .
\]
Thus, with
\[
 T=\frac{q^2(KC+p)}P+\frac{p^2(KB+q)}Q+\frac{K+pq}{PQ},
\]
equation (1) and \(w_p\le3B/2,\ w_q\le3C/2\) give
\[
 |E_\gamma|\le T,\qquad |E_k|\le T+\tfrac94\delta p^2q^2 B C. \tag{3}
\]
These estimates retain the contribution of each finite prime power separately.

## Excluding every escaping sequence

The [one-odd-prime case](divisor-envelope-245212.md) has no solutions. If there were infinitely many with two odd primes, take a sequence of different solutions escaping every finite set. Since each fixed \(k\) and each fixed odd exponent have only finitely many solutions, after discarding a finite initial segment for any prescribed bound we have \(k,B,C\to\infty\). The [reciprocal prime bound](two-odd-finiteness-245212.md) gives \(p>k/2\). The minimum-prime estimate in the [complementary-exponent proof](complementary-exponent-245212.md) gives \(p\le5K\) for sufficiently large \(B,C\) (it uses only \(BC\ge72\)). That theorem, in both orientations, gives
\[
 B\le32768 C^6,\qquad C\le32768 B^6. \tag{4}
\]
All hypotheses of (2) now hold. Let \(M=\max(B,C)\), \(m=\min(B,C)\). Either there is a subsequence with \(\log M=o(K)\), or a subsequence with \(\log M\ge cK\) for a fixed \(c>0\). We rule out both.

**When \(\log M=o(K)\).** To bound the larger prime, use the exact positive deficit at the infinite \(q\)-limit:
\[
 D=C B(1+\gamma)-C\gamma w_p-s_p,\qquad
 0<D\le 3C K B/q.
\]
Indeed \(q^{C-1}D=\gamma w_p[W(Q)-C Q]+s_p[\sigma(Q)-Q]\), and geometric sums bound the two brackets by \((3/2)(C-1)Q/q\) and \((3/2)Q/q\). For the integer \(L=C B u(u-k)+(Ck-u)p\), direct expansion gives
\[
 0<L-u^2D=C\delta(Bu-p)+(C\gamma-u)/P
 \le 5CBK^2/G+CK/P. \tag{5}
\]
The lower strict inequality holds eventually because \(p\le5K\) and \(C\to\infty\). The right tends to zero: the first summand uses \(\log M=o(K)\); the second uses \(p>k/2,\ B\to\infty,\ C\le32768B^6\). Hence integer \(L\ge1\) gives \(D\ge1/(2u^2)\) eventually. Thus \(q\le6CKBu^2\le150CBK^3\).

Consequently every fixed polynomial in \(K,p,q,B,C\) has logarithm \(O(\log K+\log m)\), using (4); for positive polynomials here the bound applies directly. Meanwhile \(\log P,\log Q\ge(m-1)\log p\), and \(\log p=\log K+O(1)\). Both powers therefore dominate every such polynomial. This gives \(T\to0\). Also \(\delta p^2q^2 BC\to0\), since the polynomial numerator has logarithm \(o(K)\) and \(G=2^K-1\). Thus (3) contradicts \(|E_k|\ge1\).

**When \(\log M\ge cK\).** From (4), \(m\ge(M/32768)^{1/6}\), so both exponents grow at least exponentially in \(K\). The [prime-power divisor bound](PrimePowerDiv245212.lean) with cofactor \(2^kP\) gives
\[
 Q\le|F W(P)-vG\sigma(P)|\le 3 z K B q P,\qquad
 q^{C-2}\le3zKBP. \tag{6}
\]
Each of \(\log z,\log K,\log p,\log B,\log C\) is \(o(\log P)\): use \(p>k/2\), (4), and \(\log P=(B-1)\log p\). By (6), \(\log q\le[(1+o(1))\log P]/(C-2)=o(\log P)\) as well. All six logarithms are also \(o(\log Q)\): \(\log q=\log Q/(C-1)\), \(p<q\), \(C\) grows exponentially in \(K\), and \(B\le32768C^6\). Therefore every numerator in \(GT\) has logarithm \(o(\log P)\) and \(o(\log Q)\), and \(GT\to0\). The first part of (3) now contradicts \(|G E_\gamma|\ge1\).

Both subsequences lead to contradictions. This establishes finiteness without claiming a completed search for the remaining finite set.
