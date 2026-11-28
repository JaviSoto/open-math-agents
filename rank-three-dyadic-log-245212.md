# The dyadic exponent grows at most logarithmically in the largest odd exponent

Let \(n=2^k\prod_{i=1}^3p_i^{e_i}\) satisfy the [A245212 equality](https://oeis.org/A245212), with distinct odd primes and positive exponents. Put \(L=\max_i(e_i+1)\). Then
all such \(n\) satisfy
\[
  2^k\le C(L+1)^{2D},\qquad
  D=16^7,\qquad C=2^{16(D+2)^2+8}+(16\cdot128^D)^2 .
\]
All three bases and all three exponents are free. The constants give a uniform asymptotic estimate; they are too large for a practical numerical search.

## The dyadic deficit

Write \(X_i=W(p_i^{e_i})/[(e_i+1)p_i^{e_i}]\) and \(Y_i=\sigma(p_i^{e_i})/[(e_i+1)p_i^{e_i}]\), where \(W(n)=\sum_{d\mid n}d\,\tau(d)\). For \(G=2^{k+1}-1\), the original equality gives
\[
 \Delta=(k+1)-(k\prod X_i+\prod Y_i)
        =\frac{(k+1)(\prod X_i-1)}{G}.
\]
The first two terms of \(X_i\) give \(X_i\ge1+e_i/[(e_i+1)p_i]\); hence \(2p_iG\Delta\ge1\) for every \(i\).

At each coordinate choose one of three rational pairs: keep the exact pair; discard the base, using \((1,1/(e_i+1))\); or retain the base and drop the reciprocal-power terms. For \(p=p_i,\ B=e_i+1,\ u=p-1\), the last pair is \((p(Bu-1)/(Bu^2),p/(Bu))\). Restoring it to the exact pair changes its two entries by \((\delta,-u\delta)\), with \(\delta=1/(Bu^2p^{e_i})\). All versions have \(X\ge1\) and \(0\le Y\le\min(1,2/B)\).

Suppose the rounded score \(k\prod X'_i+\prod Y'_i\) equals \(k+1\), with \(k\ge8\). In the cleared equation the largest retained prime divides both numerators, and therefore divides \((k+1)\) times the product of the three local denominators. It cannot divide a smaller retained prime minus one or an exact power of a different prime. Thus every retained prime satisfies \(p\le\max(k+1,L)\).

Restore the three coordinates one at a time. An exact or discarded-base coordinate cannot decrease the score. A retained coordinate can lose only when \(uY'_jY'_\ell>k\), where the other factors have their current, possibly restored values. This implies \(p>k+1\), hence \(p\le L\). Neither other length can equal \(L\): otherwise \(uY'_jY'_\ell\le2\). Thus \(e_i=L-1\ge p-1\). The loss is at most \(p^{-e_i}\), and \(p^{e_i}\ge8pG\) for \(k\ge8,\ p>k+1,\ e_i\ge p-1\). Consequently each loss is at most \(\Delta/4\). Three restorations can lose at most \(3\Delta/4\), whereas ending at the true score would require losing exactly \(\Delta>0\). The rounded score therefore differs from \(k+1\) for **every** selection of replacements, even if no lengths are comparable.

## Clearing the denominators

Take \(x=128(k+2)(L+1)\). Among seven disjoint intervals \((x^{16^j},x^{16^{j+1}}]\), \(0\le j<7\), one contains none of the six numbers \(p_i,p_i^{e_i}\). Call it \((Q,Q^{16}]\). Keep a coordinate exact if \(p_i^{e_i}\le Q\); otherwise retain the base if \(p_i\le Q\) and discard it if \(p_i>Q\). The common denominator of each pair is at most \(Q^3\). The strict separation just proved forces the score to differ from \(k+1\) by at least \(Q^{-9}\).

The coordinate errors are at most \(2/Q^{16}\); the three-factor product estimate bounds the score error by \(48(k+1)/Q^{16}\). If \(G\ge8(k+1)x^D\) then the displayed deficit formula and \(X_i\le2\) give \(\Delta\le x^{-D}\le Q^{-16}\). This contradicts the integer gap, since \(48(k+1)+1<Q^2\). Thus \(2^k\le G<8(k+1)x^D\). Finally, when \(k+2\ge16(D+2)^2\), the elementary estimate \((k+2)^{2(D+1)}\le2^{k+2}\) absorbs the polynomial in \(k\) after squaring. All smaller \(k\) are covered by the first term of \(C\).

The standalone Lean file [SingleMovingResearch245212.lean](SingleMovingResearch245212.lean) checks the statement from the original equality as **OMA.SingleMovingHeight245212.original**. The theorem controls \(k\) in terms of \(L\); it does not by itself bound \(L\).
