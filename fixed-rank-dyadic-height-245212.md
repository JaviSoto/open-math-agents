# The power of two in a solution with any prescribed number of odd primes

Consider the [A245212 equation](https://oeis.org/A245212)
\[
 W(n)+\sigma(n)=2n\tau(n),\qquad W(n)=\sum_{d\mid n}d\,\tau(d).
\]
Let \(n=2^k\prod_{i=1}^r p_i^{e_i}\), where the \(p_i\) are distinct odd
primes, \(r\ge1\), and all \(e_i\ge1\). Put \(L=1+\max_i e_i\). Every
solution satisfies
\[
 2^k\le C(E_r)(L+1)^{2E_r},\qquad
 E_r=(r+2)(3r+4)^{2r+1}+r,\qquad
 C(d)=2^{16(d+2)^2+8}+(16\cdot128^d)^2 .
\]
Both the formula and the proof are uniform in \(r\). In particular, at any
fixed positive rank \(k=O_r(\log(L+1))\), even when all the odd primes
vary. At rank four \(2E_4=824\,633\,720\,840\). These constants are for
separation, not practical enumeration. The estimate alone does not bound
the largest exponent or prove finiteness at rank four. For \(r=0\) every
power of two is a solution, so that case must be omitted.

## Only a longest coordinate can decrease the rounded score

Use \(B_i=e_i+1\), \(X_i=W(p_i^{e_i})/(B_i p_i^{e_i})\), and
\(Y_i=\sigma(p_i^{e_i})/(B_i p_i^{e_i})\). For \(G=2^{k+1}-1\),
multiplicativity and the exact moments at \(2^k\) give
\[
 \Delta=k+1-k\prod_iX_i-\prod_iY_i
       =\frac{(k+1)(\prod_iX_i-1)}G.
\]
The terms of \(W(p^e)\) at \(p^e,p^{e-1}\) show
\(X_i\ge1+e_i/(B_ip_i)\); hence \(2p_iG\Delta\ge1\).

At each coordinate one may take the exact moments, drop the base (use
\(1,1/B_i\)), or retain the base while dropping the reciprocal power (use
\(p_i(B_i u_i-1)/(B_i u_i^2),p_i/(B_i u_i)\), where \(u_i=p_i-1\)).
All three choices have \(X\ge1,\ 0\le Y\le\min(1,2/B_i)\). Write the
score as \(k\prod X+\prod Y\), and suppose a rounded score equals \(k+1\),
where \(k\ge8\).

If there are retained bases, take the largest, \(P\). It divides both
numerator products and thus \((k+1)\) times the product of the local
denominators. Those denominators are \(B_i p_i^{e_i}\), \(B_i\), or
\(B_i(p_i-1)^2\), according to the choice of moments. Distinctness of the
bases and maximality of \(P\) show that \(P\le\max(k+1,L)\).

Fix **one** longest coordinate \(v\), with \(B_v=L\). Restore the exact
moments one coordinate at a time. A dropped base cannot decrease the
score. Restoring a retained base \(p_i\) adds \((\delta,-u_i\delta)\)
with \(\delta=1/(B_iu_i^2p_i^{e_i})\). A loss can occur only if
\[
 k<u_i\prod_{j\ne i}Y_j .
\]
Here the other moments may be exact or rounded. This implies \(p_i>k+1\),
so \(p_i\le L\). If \(i\ne v\), the product includes \(Y_v\le2/L\), and
the right side is at most \(2(p_i-1)/L<2\), a contradiction. Thus only
\(v\) can lose anything, regardless of the rank. Its loss is at most
\(p_v^{-e_v}\le\Delta/4\): indeed \(e_v\ge p_v-1\), \(p_v>k+1\), and
\(k\ge8\) give \(p_v^{e_v}\ge 8p_v G\). Restoring every coordinate would
have to lose exactly \(\Delta>0\). This proves that **no** rounded score
equals \(k+1\).

## The finite denominator bound

Let \(x=[128(k+2)(L+1)]^{r+2}\) and \(A=3r+4\). Among the \(2r+1\)
disjoint intervals \((x^{A^j},x^{A^{j+1}}]\), \(0\le j\le2r\), one
contains none of the \(2r\) numbers \(p_i,p_i^{e_i}\). Write it
\((Q,Q^A]\). Keep a moment exact if \(p_i^{e_i}\le Q\); otherwise keep
only its base if \(p_i\le Q\), and drop the base if \(p_i>Q\). Each local
denominator is at most \(Q^3\). Since the rounded score differs from
\(k+1\), its distance from that integer is at least \(Q^{-3r}\).

The local moment errors are at most \(2/Q^A\). Telescoping a product of
\(r\) nonnegative factors at most \(2\) bounds the score error by
\(2r\,2^r(k+1)/Q^A\). If \(G\ge2^r(k+1)x^{A^{2r+1}}\), the deficit
formula gives \(\Delta\le1/Q^A\), since \(\prod X_i\le2^r\). The two
errors together are smaller than \(Q^{-3r}\): \(Q\ge128\) and both
\(2r2^r\) and \(k+1\) are at most \(Q\). This contradiction gives
\[
 2^k\le G<2^r(k+1)[128(k+2)(L+1)]^{(r+2)(3r+4)^{2r+1}} .
\]
Absorb \(2^r\) into the last base to obtain exponent \(E_r\). For
\(k+2\ge16(E_r+2)^2\), the elementary estimate
\((k+2)^{2(E_r+1)}\le2^{k+2}\) absorbs the remaining factor in \(k\)
after squaring; the stated constant also covers all smaller \(k\).

## Checking the result

[FixedRankHeightResearch245212.lean](FixedRankHeightResearch245212.lean)
imports only the original Formal Conjectures OEIS statement. In its pinned
Lake checkout, run `lake env lean -j 1 -DElab.async=false /path/to/FixedRankHeightResearch245212.lean`.
The final four axiom reports cover the sign theorem, the factored theorem,
the original-integer theorem, and the rank-four specialization. For
arbitrary \(n\), the formal rank is the cardinality of
\(\operatorname{primeFactors}(n)\setminus\{2\}\), and \(k=v_2(n)\).
