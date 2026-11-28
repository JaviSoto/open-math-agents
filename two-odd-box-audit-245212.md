# Independent enclosure of the two-odd-prime search

For an A245212 solution \(2^{K-1}p^{B-1}q^{C-1}\) with \(p<q\), write \(m=\min(B,C)\), \(M=\max(B,C)\). The [independent integer verifier](two_odd_box_audit_245212.py) proves that in the remaining range \(6\le m\le32\) one must have **\(K\le1250,\ M\le225\)**. On testing every cell of this rectangle, it leaves 85,481 possible triples, all with \(K\le1119,\ M\le135\). The [comparison](two_odd_box_overlap_245212.py) verifies that every such triple enters the [final-prime replay](two_odd_replay_245212.py). This enclosure by itself makes no assertion about equality at a surviving triple.

## Inputs and elementary bounds

Use \(u=p-1,\ v=q-1,\ P=p^{B-1},\ Q=q^{C-1},\ z=2^K,\ G=z-1,\ k=K-1,\ \gamma=k+K/G\). With \(w_p=W(P)/P,\ s_p=\sigma(P)/P\) and analogous \(q\)-terms, the balance is
\[
 1-\frac{s_ps_q}{BC}=\gamma\left(\frac{w_pw_q}{BC}-1\right).
\]
The [least-prime exclusions](eleven-moving-pair-245212.md) give \(p,q\ge13\). Both \(s_p\) and \(w_p/B\) are at most \(1+1/u\), and likewise at \(q\). For \(B,C\ge4\) the left side is at least \(2135/2304=1-(13/12)^2/16\). For \(K\le5\) the right side is at most \(5((13/12)^2-1)=125/144\), so there is no solution. For \(K\ge6\) the right side is at most \(K(2+1/12)/u\). In particular
\[
 u\le \frac{960}{427}K < \frac94 K,\qquad
 p>\frac{(K-1)(B-1)}{B}
\]
where the last inequality follows from the [strict reciprocal bound](two-odd-finiteness-245212.md). Rounding up to the next odd integer in the latter inequality preserves all possible \(p\); for \(q\) add two. The [fixed-exponent bounds](ComplementaryBoundedResearch245212.lean) give \(K\le512m^4,\ M\le64m^2K,\ M\le32768m^6\). The separate [smaller-exponent theorem](two-odd-effective-245212.md) gives \(m\le32\).

**Prime-power bounds.** The [cofactor divisibility bound](PrimePowerDiv245212.lean) implies \(q^{C-2}\le3zKBP\) and \(p^{B-2}\le3zKCQ\). For the first inequality, divide the bound \(Q\le|F W(P)-(q-1)G\sigma(P)|\) by \(q\); \(F\le KG,\ W(P)\le3BP/2,\ \sigma(P)\le3P/2,\ G<z\). The second is symmetric. Also \(q^{C-B-1}\le3zKB\) since \(p<q\). A negative exponent cannot trigger this last exclusion.

The \(q\)-cofactor bound also controls the quotient \(q^2/P\). With \(C\ge c_0\ge4\) raise it to the positive power \(c_0-2\):
\[
 (q^2/P)^{c_0-2}\le(3zKB)^2P^{-(c_0-4)}.
\]
Thus one may use the lower endpoint for \(P\) even if the resulting upper logarithm is negative.

**Both poles.** In the [complementary-exponent notation](complementary-exponent-245212.md), \(D>0,\ qD\le3CKB\), and
\[
 L(\gamma)=u^2D+(C\gamma-u)/P,\qquad
 L(k)-u^2D=C(K/G)(Bu-p)+(C\gamma-u)/P .
\]
Here \(C\ge4,\ K\ge6\) imply \(C\gamma>u\) from the bound on \(u\). Consequently \(GL(\gamma)\) and \(L(k)\) are positive integers. If \(P\ge2GCK\), then \(u^2D\ge1/(2G)\). If \(CKBu/G\le1/4\) and \(CK/P\le1/4\), then \(u^2D\ge1/2\). These give the respective bounds \(q\le6CKBGu^2\) and \(q\le6CKBu^2\). In the first sufficient condition, replacing \(G\) by \(z\) is conservative.

**Integral defects.** The [two-prime expansion](two-odd-global-245212.md) writes
\[
 T=\frac{q^2(KC+p)}P+\frac{p^2(KB+q)}Q+\frac{K+pq}{PQ},
 \qquad
 |E_\gamma|\le T,\quad |E_k|\le T+2(K/G)p^2q^2BC .
\]
The constant 2 is valid since \((13/12)^2<2\). Both \(GE_\gamma\) and \(E_k\) are nonzero integers: \(u<k(C-1)\) follows from \(u<9K/4,\ K\ge6,\ C\ge4\), so the positive-\(\alpha\) separation applies. For the second and third terms of \(T\), first replace the \(p\) factors in the numerators with their upper endpoints. The functions \((a+q)/q^{C-1}\) and \((a+bq)/q^{C-1}\) are decreasing in \(q>0\) for nonnegative \(a,b\), \(C\ge2\). Therefore the **lower** bound on \(q\) is valid simultaneously in the remaining numerator and denominator. Finally \(z\mid W(P)W(Q)-\sigma(P)\sigma(Q)>0\), so \(z<2BCPQ\).

**Unequal exponents.** Let \(x^a,y^d\) denote the two prime powers, in either order. For \(a\ge2d+4,\ d\ge2\) the [integer nonresonance](ComplementaryBoundedResearch245212.lean) gives \(A-kH\ne0\). Clearing the balance as in the fixed-exponent proof yields
\[
 z\le1+KH+(z/x^a)|C(\gamma)|,\quad
 H\le2(d+1)(a+1)x^2y^d,\quad |C(\gamma)|\le2(d+1)(K+x)y^d.
\]
Use \(z/x^a\le3(d+1)(a+1)y^d\). With interval endpoints, \(\min(a+1)\ge2\max(d+1)+3\) is sufficient to use this test throughout the box.

## Integer replay and coverage

Run \(\texttt{python3 two_odd_box_overlap_245212.py}\) in the research directory; the [exterior verifier](two_odd_box_audit_245212.py) also runs independently without either primary script. It bounds \(16\log_2 n\) between \(\operatorname{bitlength}(n^{16})-1\) and \(\operatorname{bitlength}(n^{16}-1)\), so powers of two and signed upper exponents require no numerical tolerance. The logarithm of a sum of \(j\) nonnegative terms is at most the largest upper logarithm plus \(\log_2 j\). Every veto is an impossible strict inequality (or a sufficient non-strict bound for a positive integer).

For each \(m=6,\ldots,32\), test both disjoint exterior regions \(K\ge1251\), and \(6\le K\le1250,\ M\ge226\). Use both orientations, including \(B=C\) only once. Unresolved intervals split at \(\lfloor\sqrt{ab}\rfloor\) between endpoints \(a<b\), covering \([a,\lfloor\sqrt{ab}\rfloor]\) and its complement. Intersect only with the proved bound \(M\le64m^2K_{\max}\) and the initial global bounds. All 720 terminal exterior boxes were vetoed. Repeating the same independent test inside the rectangle down to singleton triples gives the 85,481 survivors above; all are contained in the 170,873 cells produced by the primary verifier at precision 12. The two programs share the proven inequalities but use distinct interval arithmetic, subdivisions and data structures.
