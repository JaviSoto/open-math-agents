# Distinct crystal parameters cannot share a shifted squareclass

Let \(q=(a+b)^2/((a+1)(b+1))\) be the parameter of an admissible sorted
crystal pair of product \(n=ab\). If a second pair of the same product
has parameter \(Q\), with \(q,Q>4\) and \((q-4)(Q-4)\) a square, then the
two pairs coincide.

This proof combines an algebraic norm, an integer spacing estimate, and
a finite exact-integer computation. It is **not** formalized in Lean.
It uses the recurrence classification of
[Abrate, Barbero, Cerruti and Murru](https://arxiv.org/abs/1601.03081)
and the same-parameter-squareclass exclusion proved in the accompanying
CrystalComplementComplete.lean. No distribution conjecture, elliptic-curve
table, or general integral-point theorem is needed.

## Setup and the limiting constant

Suppose the pairs differ. The same-squareclass theorem lets us assume
\(q<Q\) and \(qQ\) nonsquare. Write \(d=q-4=sA^2,\ e=Q-4=sB^2\) with \(s\)
squarefree and \(0<A<B\). Set \(N=n+1,\ \Delta=b-a\), and
\[
 R_q=2\Delta-q-2,\qquad \kappa(q)=q\sqrt{q/d}-q-2.
\]
Define \(R_Q\) by the other pair. The exact identity in the parameter
supplement gives
\[
 R_q=\sqrt{d(4N+q)}+\kappa(q)-E_q,\quad
 0<E_q\le 32/(d^{3/2}\sqrt n).
\]
Indeed, the sum of the positive square roots when rationalizing its
difference of squares is at least \(2d^{3/2}\sqrt n\).
We have \(0<\kappa(q)<6/d\): the lower inequality follows from
\(q^3-d(q+2)^2=12q+16>0\), and the upper one from
\((q^2-2q-2)^2-q^3d=8q+4>0\).

The integer \(H=B R_q-A R_Q\) approximates
\(H_\infty=B\kappa(q)-A\kappa(Q)\). Since \(B\sqrt d=A\sqrt e\),
rationalizing the difference of the two leading square roots shows
\[
 |H-H_\infty|\le
 \bigl(B\sqrt d(Q-q)/4+32(A+B)\bigr)/\sqrt n
 <7Q^2/\sqrt n .
\]
Here \(A,B\le\sqrt Q\) and \(Q\ge6\).

Put \(M=sAB=\sqrt{de}<Q\), \(U=B^2q\sqrt{sq}\), \(V=A^2Q\sqrt{sQ}\).
Then \(M(H-H_\infty)\) equals an integer minus \(U\) plus \(V\).
The two radicals \(\sqrt{sq},\sqrt{sQ}\) represent independent nontrivial
quadratic classes: \(sq\) has the class of \(q(q-4)\), strictly between
\((q-3)^2\) and \((q-2)^2\), and likewise for \(sQ\); their classes are
different because \(qQ\) is nonsquare. The two radicals and 1 are linearly
independent over \(\mathbb Q\). Our algebraic integer is nonzero, so the
product of its four sign conjugates is a nonzero integer. The two
quantities \(U,V\) are individually at most \(Q^3\). Each of the other
three conjugates has modulus below \(11Q^3\), since it differs from this
one by at most \(2U+2V\) and \(|M(H-H_\infty)|<7Q^3\). Therefore
\[
 1/(11^3Q^{10})< |H-H_\infty|<7Q^2/\sqrt n,
 \qquad n<10^8Q^{24}.
\]
At index \(r\ge2\) for the *larger* parameter \(Q\), the geometric-sum
formula of the parameter supplement gives \(n>4(Q-3)^{2r-1}\). It also
gives \(n>Q^3\), either from strict growth and the explicit cubic at \(r=2\)
or directly. Thus \(r\le27\) for \(Q\ge6\), and \(r\le15\) for \(Q\ge26\).
For these numerical cutoffs check \(4\cdot3^{55}>10^8 6^{24}\) and
\(4\cdot23^{31}>10^8 26^{24}\); \((Q-3)^k/Q^{24}\) increases for \(k>24\).

The recurrence modulo \(e\) gives \(u_r\equiv r^2\) and consequently
\[
 R_Q\equiv 8r-2\pmod e,\qquad B\mid H+A(8r-2).
\]

## Bounding both parameters

The following three ranges exhaust the possibilities.

**1. \(5\le q\le25\).** For \(Q>q\) and \(r\ge2\), bound
\[
 |H/B-\kappa(q)| < 11 A/B.
\]
Indeed the contributions are at most \((A/B)\kappa(Q)<3A/B\),
\(\sqrt d Q/(4\sqrt n)<(A/B)/4\),
\(E_q<(A/B)\,32/(d^2Q)<6A/B\), and \((A/B)E_Q<A/B\)
(use \(e\ge2,\ Q\ge6,\ n>Q^3\)). By the congruence above, an integer
is therefore within \((8r+9)A/B\) of \(\kappa(q)\).
For these 21 \(q\), its distance from the integers exceeds \(1/16\).
The script checks this by squaring the endpoints of the intervals
\([h-1/16,h+1/16]\), \(0\le h\le100\), for \(q\sqrt{q/d}\);
the check is independent of floating point. It follows that
\(A<B<16(8r+9)A\), giving 1,662,622 candidate triples.

**2. \(q\ge26,\ r=2\).** Write \(k=(H+14A)/B\in\mathbb Z\). The same
four-term estimate now gives
\[
 -(\kappa(Q)+1/4+1)A/B < H/B < \kappa(q)+A/B .
\]
For the lower bound use \(32/(d^2Q)<1\); for the upper bound the dominant
square-root difference and \(-E_q\) are negative. Since \(\kappa(q)<1/3\),
it follows that \(0<k<1/3+15A/B\), so \(B<23A,\ Q<529q\).
The smaller parameter cannot also have index two, as the cubic product is
strictly increasing; thus \(4(q-3)^5<n<4Q^3\). From \(q-3\ge23q/26\)
we get \(q<17000\). The script also removes candidates with the first
noncubic \(q\)-product already greater than the cubic \(Q\)-product.
216,805 triples remain.

**3. \(q\ge26,\ r\ge3\).** Use the exact identity
\[
 R_q^2/d=4N+K_q,\qquad K_q=q+(24a+16z+12)/d,
\]
where \(z\) is the previous half-component in the \(q\)-recurrence.
It follows by expanding the square, using the component equation and
\(b=(q-2)a+q+1-2z\). Also
\(z=(a-1)^2/(2(b+1))\). For the same product a larger parameter has
a larger sum and hence a strictly smaller small component: the function
\(S^2/(N+S)\) is strictly increasing for \(S>0\), while \(x+n/x\)
decreases strictly for \(x\le\sqrt n\).
Consequently the numerator \(F_q=24a+16z+12\) exceeds its analogue \(F_Q\).
Since \(r\ge3\), the smaller component of the \(Q\)-pair is at least
\(2(Q-1)^2-1\), so \(F_Q>de\). Thus
\[
 K_q-K_Q>q-Q+F_Q(1/d-1/e)>0.
\]
On the other hand \(F_q\le44a\) since \(z\le a,\ a\ge3\), and
\(a\le\sqrt{n/d}\) since \(b\ge(q-3)a\). Hence \(K_q-K_Q<44\sqrt n/d^{3/2}\).
Both \(R\)'s are positive because \(b\ge(q-3)a,\ a\ge2q-1\); each is
greater than \(2\sqrt{dn}\) or \(2\sqrt{en}\) by the displayed identity.
Multiplying \(H\) by \(BR_q+AR_Q\) and using \(B^2d=A^2e\) gives
\[
 0<H<11B/d\le B/2.
\]
The positive integer divisible by \(B\) above is now at most
\(H+A(8r-2)\), so \(B<16Ar\), and \(sA<176r\).
The script enumerates squarefree \(s\), positive \(A,H\) with
\(sA<176r,\ HsA<176r\); it takes \(B\) from the divisors of
\(A(8r-2)+H\) and imposes the proved inequalities. 240,837 triples remain.

## Exact computation and consequence

    python3 crystal_shift_certificate.py
    python3 crystal_shift_certificate.py --no-sieve

For each retained triple the script calculates the \(Q\)-product at \(r\)
and compares against the strictly increasing \(q\)-products until it
matches or passes. No equality occurs. The default run filters modulo
seven small primes using *complete* recurrence orbits (the state update
is invertible); the second command disables these filters. Both use integer
arithmetic and skip same-squareclass \(q,Q\), which are already excluded
by the separately kernel-checked theorem. Thus the shifted-squareclass
exclusion holds at all sizes, unlike a finite search by product cutoff.

Together with the three earlier exclusions, this characterizes the remaining
nonparabolic case: if \(q,Q>4\) give a collision, the three squareclasses
\[
 [q(q-4)],\quad[Q(Q-4)],\quad[qQ]
\]
are linearly independent in \(\mathbb Q^\times/\mathbb Q^{\times2}\).
Indeed the first two are each nontrivial; equality of them is precisely
the common-real-quadratic-field case. The other four possible nontrivial
relations are squareclasses \(qQ,(q-4)Q,q(Q-4),(q-4)(Q-4)\) vanishing,
all excluded. The corresponding three square roots must generate a field
of degree eight. We do not resolve this remaining independent-class case.
