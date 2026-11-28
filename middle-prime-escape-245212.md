# The two remaining exponent patterns for a hypothetical infinite rank-three family

This is a mathematical proof using the linked, separately kernel-checked bounds. Its subsequence and size arguments are given below. They are not part of the Lean theorem for the [smallest prime](least-prime-longest-245212.md).

Write \(n=2^k p^a q^b r^d\) with odd primes \(p<q<r\) and positive exponents, and impose the original A245212 equality. **Only finitely many such \(n\) have \(d\ge3\)**. A stronger conclusion describes any unbounded sequence of distinct solutions after passing to a subsequence. Put \(L=b+1,\ B=L,\ C=d+1,\ u=q-1,\ Q=q^b,\ h=2^k p^a,\ A=W(h),\ S=\sigma(h),\ H=2h\tau(h)\). Then eventually:

1. \(a,d=o(b)\), \(k,p,q,h=O(L^M)\) for some fixed \(M\), and \(p<q\le L\);
2. \(d=1\) or \(d=2\), and \(r\ge kQ/2\);
3. the following **exact integers** satisfy
\[
 HBCu^2=q[AC(Bu-1)+Su],\qquad Su>AC,\qquad C B u[Hu-Aq]=q[Su-AC].
\]

In particular \(q\mid B\) eventually. Indeed the first equation gives \(q\mid HBC\). The prime \(q>k+1\) does not divide \(2h\), while \(\tau(h)=(k+1)(a+1)\). The strict slope bound below gives \(q>k(a+1)C/4\), hence \(q>a+1,C\) for large \(k\). The conclusion follows. The theorem does not assert the existence of an escaping sequence in either remaining pattern.

## Taking a subsequence and clearing the target

Each bounded range of \(k\) has an effective whole-integer bound by fixed-dyadic rank-three finiteness. Thus \(k\to\infty\). The [smallest-prime theorem](least-prime-longest-245212.md), the [largest-prime sector and exponent separation](two-long-exponents-245212.md), and finiteness at bounded divisor count yield \(b\to\infty\) and \(a,d=o(b)\). The [logarithmic dyadic bound](rank-three-dyadic-log-245212.md) gives \(k=O(\log L)\). In particular the exact dyadic coefficients \(f=1+k2^{k+1}\) and \(g=2^{k+1}-1\) are polynomially bounded in \(L\), and \(f\ge kg>0\).

Consider the six positive integral scales \(p,p^a,q,q^b,r,r^d\). Passing to a common subsequence, each \(\log(\text{scale})/\log L\) has a finite or infinite limit in the extended nonnegative reals. Thus a given scale is either bounded by a fixed power of \(L\), or exceeds every fixed power of \(L\) eventually. At each prime \(s\) keep both moments exact if its power is polynomially bounded. Otherwise retain its base and drop reciprocal powers if the base is polynomially bounded; discard the base if it too exceeds every polynomial. In the last case the rounded moments are \(1,1/(e+1)\).

All rounded denominators are polynomially bounded: they are \((e+1)s^e\), \((e+1)(s-1)^2\), or \(e+1\), respectively. Each coordinate error decays faster than every reciprocal power of \(L\): this follows directly from the reciprocal-power formulas in the retained case and the \(O(1/s)\) estimates in the discarded case. All moments are bounded. Multiplication by \(f,g\) still leaves errors smaller than every reciprocal polynomial. The difference of the rounded score and the integer \(f+g\) therefore vanishes eventually; its denominator was only polynomial. The true score also equals \(f+g\).

## The sign and size of a restoration

A discarded base \(s\) gains at least \(f/(2s)\) on restoration. Indeed the weighted factor increases from 1 to at least \(1+1/(2s)\), the other weighted factors are at least 1, and the ordinary term does not decrease. A retained base \(s\) changes the score by
\[
  \frac{f X_j'X_\ell'-g(s-1)Y_j'Y_\ell'}{(e+1)(s-1)^2s^e}.
\]
Here the primes on the other factors mean their *current* values during a restoration in any order. In particular \(0\le Y_j'\le\min(1,2/(e_j+1))\). At the exact rounded target, every retained prime is at most \(\max(k+1,L)=L\) eventually, by the integer divisibility argument in the smallest-prime theorem. If \(s\ne q\) is retained, one other length is \(L\), so \((s-1)Y'_jY'_\ell\le2\). Its gain is at least
\[
     \frac{(k-2)g}{L^3 s^e}.
\]

The coordinate \(q\) cannot be exact because \(q^b\) exceeds every polynomial in \(L\). Nor can it be discarded: it would contribute a strictly positive gain, while both others give nonnegative gains. Hence \(q\) is retained, \(q\le L\), and \(p<q\) cannot be discarded. A restoration of \(q\) must actually lose unless both others are exact and its change vanishes. That latter case is impossible: with both others exact the slope vanishes precisely when \(W(2^k p^a r^d)=(q-1)\sigma(2^k p^a r^d)\), contradicted by the [nonzero cofactor discrepancy](PrimePowerDiv245212.lean). In every case with another changed coordinate we therefore have
\[
  q-1>k(a+1)(d+1)/4,\qquad
  \text{loss at }q \le g/q^b .
\]
The first inequality uses \(Y'_jY'_\ell\le4/[(a+1)(d+1)]\); the second bounds the negative part of the displayed change using \(Y'_j,Y'_\ell\le1\).

No other base can be retained. For \(p\), we have \(p^a\le q^a=q^{o(b)}\), so \(L^3 p^a=o(q^b)\) and its gain alone exceeds the entire possible loss. For retained \(r\), we have \(r\le L\). When \(q\ge\sqrt L\), \(r^d\le q^{2d}=q^{o(b)}\). When \(q<\sqrt L\), the negative slope at \(q\) gives \(d<4q/k\le4\sqrt L\). Then \(\log(r^d)\le4\sqrt L\log L=o(b)\), again \(r^d=q^{o(b)}\). Either estimate makes the displayed gain larger than \(g/q^b\). This excludes retention.

Consequently \(p\) is exact, \(q\) retained, and \(r\) discarded; the possibility of exact \(r\) was excluded by the nonzero discrepancy. Comparing the gain at \(r\) with the loss at \(q\) gives \(r\ge f q^b/(2g)\ge k q^b/2\). Since \(p^a\) is exact, it is polynomially bounded; so is \(h\). Substituting these three choices of moments into the score gives the asserted exact integer equality. Restoring \(q\) *first*, while \(r\)'s factors are \(1,1/C\), has negative slope exactly when \(Su>AC\).

## The exponent of the largest prime

Put \(m=hq^b\). The last-prime bound, from the same [divisibility and nonzero discrepancy](PrimePowerDiv245212.lean), gives
\[
 r^{d-1}\le W(m)+\sigma(m).
\]
Indeed \(r^d\le|W(m)-(r-1)\sigma(m)|\le r[W(m)+\sigma(m)]\). Multiplicativity and the elementary bounds \(W(q^b)\le2(b+1)q^b,\ \sigma(q^b)\le2q^b\) show the right hand side is polynomial in \(L\) times \(q^b\), because \(h\) is polynomially bounded. If \(d\ge3\), the left hand side is at least \(r^2\ge k^2q^{2b}/4\), a contradiction. Starting with an infinite sequence with \(d\ge3\) and passing to the subsequence above would therefore be impossible. This proves the finiteness assertion.
