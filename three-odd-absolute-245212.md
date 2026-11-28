# A uniform finite search for A245212 with three distinct odd prime factors

**Theorem.** There is a computable integer \(K_3\) such that every positive integer \(n\) with exactly three distinct odd prime factors satisfying \(a(n)=\sigma(n)\) is at most \(K_3\). Nothing is fixed in advance: the prime factors, their exponents, and the power of two in \(n\) may all vary. Here \(a(n)\) is the original [OEIS A245212](https://oeis.org/A245212) function. Equivalently, writing \(W(n)=\sum_{d\mid n}d\tau(d)\), the equation is \(W(n)+\sigma(n)=2n\tau(n)\).

The bound is much too large to exhaust by running through the integers. This proof neither finds an exception nor proves that none exist. Together with the [classification for at most two odd prime factors](two-odd-nonexistence-245212.md), it shows that powers of two are the only solutions with at most three distinct odd prime factors apart from a finite set.

The [standalone Lean file](ThreeOddAbsoluteResearch245212.lean) uses the original Formal Conjectures definition. The bound itself is `OMA.ThreeOddAbsolute245212.cutoff`; `original` proves the inequality directly for \(n\), and `finite` proves the corresponding set is finite. The [source archive](three-odd-absolute-245212.tar.gz) separates the proof into small modules and includes a parallel replay script. Use the Formal Conjectures checkout at commit `9097e2f90e66d2f6244209cb1c07f7120d17ec53`.

## Which exponent can still grow?

Write \(n=2^k p^a q^b r^d\), with \(3\le p<q<r\) prime and \(a,b,d>0\). [Fixed \(k\)](rank-three-effective-height-245212.md), a [longest exponent at \(p\)](least-prime-longest-245212.md), and [two long exponents](two-long-exponents-245212.md) each give a whole-integer bound in their respective cases. Combining them, for any prescribed \(N\), either \(n\) is below a computable bound depending only on \(N\), or
\[
k\ge256,\quad p\ge33,\quad B=b+1\ge N,\quad
16(a+1)<B,\quad16(d+1)<B.
\]
It remains to bound \(B\) in this last case.

For \(s^e\) put \(X=W(s^e)/[(e+1)s^e]\) and \(Y=\sigma(s^e)/[(e+1)s^e]\). The original equation has the form \(f\prod X+g\prod Y=f+g\), where \(f=1+k2^{k+1}\) and \(g=2^{k+1}-1\). Both coefficients are [polynomially bounded in \(B+1\)](rank-three-dyadic-log-245212.md). Among seven disjoint intervals with successive endpoints \(Q,Q^{16}\), one misses all six numbers \(p,q,r,p^a,q^b,r^d\). Keep the prime-power moments exact below this interval. Above it, omit the reciprocal-power terms if the base was retained; if the base was also above the interval, use \(X=1,Y=1/(e+1)\). The new score has denominator at most \(Q^9\); its error is strictly below \(Q^{-9}\). Thus it still equals the exact integer target.

The signs and sizes of the three corrections determine the rounded configuration: the \(p\) moments must be exact, \(q\) must be retained with its reciprocal power omitted, and \(r\) must be discarded. Restoring \(q\) first strictly *decreases* the score. The [intermediate argument](middle-prime-escape-245212.md) gives the arithmetic behind these signs; `MiddleModes245212.force` and `MiddleBridge245212.original` prove the finite-threshold version without a subsequence. For fixed computable \(D\) this gives
\[
p\le4(k+1),\qquad h=2^kp^a\le(B+1)^D.
\]
Put \(A=W(h),S=\sigma(h),H=2h\tau(h),u=q-1,C=d+1\). The score and the strict sign become
\[
 HBCu^2=q[AC(Bu-1)+Su],\qquad AC<Su.
\]

## Why even this configuration runs out

Define \(E=uH-qA\) and \(\Delta=H-A\). Rearranging the displayed equality gives \(BCuE=q(Su-AC)>0\); hence \(E,\Delta>0\) and \(BE\le qH\). The obstacle to bounding \(B\) would be an \(E\) tiny compared with \(H\). The special cofactor \(h=2^kp^a\) rules this out quantitatively.

Here is the integer estimate used twice. If \(cZP=G+iZ+jP+t\), with nonnegative integer entries and \(G>0\), then
\[
 ZP\le m(i,j,t)G,\qquad m(i,j,t)=[4(i+j+t+1)+1]^3 .
\]
When both variables exceed \(4(i+j+t+1)\), each error term is at most \(ZP/4\). Otherwise one variable is small, say \(Z\); the coefficient \(cZ-j\) of \(P\) is a positive integer and bounds \(P\) by \(G+iZ+t\). The other case is symmetric. Neither \(c\) nor the sizes of the two variables appear in the multiplier.

In our cofactor set \(Z=2^{k+1}\), \(P=p^a\), \(L=(p-1)^2\), \(M=(k+1)(a+1)\), \(v=p[(a+1)(p-1)-1]\). Exactly,
\[
 H=MZP,\qquad LA=(kZ+1)(vP+1).
\]
Set \(K=M L\,m(k,v,1)\). Apply the integer estimate to \(H-A=\Delta\) and to \(uH-qA=E\) after clearing \(L\). This gives \(H\le K\Delta\) and \(H\le q^3 K E\). Now \(q\Delta=E+H\). For \(q\ge2K\) this gives \(q\Delta\le2E\), hence \(B\le2K\). For \(q<2K\), substitute the second bound into \(BE\le qH\), giving \(B\le q^4K\le16K^5\). **The resulting bound \(B\le16K^5\) does not depend on \(q,r,b,d\).**

Finally put \(X=8(k+a+34)\). From \(p\le4(k+1)\) we have \(K\le X^{16}\), \(B\le X^{81}\). But \(2^{k+a}\le h\le(B+1)^D\le X^{82D}\). Exponential growth therefore bounds \(k+a\), and so bounds \(B\). One cutoff used in Lean is
\[
 B\le[8(16(j+1)^2+68+6j)]^{81},\qquad j=82D .
\]
Choose \(N\) above this number and the finite approximation threshold. The long-middle alternative is then impossible. The computable bound in the first alternative is \(K_3\).
