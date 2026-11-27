# Further exclusions for the biharmonic crystal uniqueness problem

Download [the Lean sources, finite certificates and search programs](crystal-parameter-supplement.zip). The companion [density result](crystal-density.md) counts how many exceptions could remain.

This is a supplement to the density argument, not a proof of uniqueness.
The two results below exclude infinite families of *possible second
decompositions*. Write \(n=ab,\ 1<a\le b\), \(q=(a+b)^2/((a+1)(b+1))\),
and use \(Q\) for the parameter of the other decomposition. The original
classification is that of [Abrate, Barbero, Cerruti and Murru](https://arxiv.org/abs/1601.03081).
The separation arguments below are independent of their classification
except where the recurrence or finite search is explicitly invoked.

## Equal parameter squareclasses

If \(q=sA^2,\ Q=sB^2\) with \(s,A,B>0\), then the component pairs
coincide. This entire statement is formally checked.

Write \(S=a+b\). The Vieta estimate \(q\le (a+1)/2\) proved below
implies \(q^2\le S\): multiply \(2q\le a+1\) and \(S\le2(b+1)\),
then use \(S^2=q(a+1)(b+1)\). As \(A^2\mid S^2\), let \(S=At\).
The integer \(u=2t-sA\) satisfies
\[
 u^2=4s(n+1)+(sA)^2,\qquad u\ge(sA)^2.
\]
For the inequality use \(t\ge(sA)^2 A\), then \(t\ge sA\).
It follows that \((u-1)^2<4s(n+1)\le u^2\): even \(u=1\) is harmless
since \(4s(n+1)>0\). Hence \(u\) depends only on \(n,s\).
The analogous equation for \(Q\) forces \(A=B\). The positive sum of
components is the unique positive root of \(S^2=q(n+1+S)\); equality
of sums and products gives equality of the two sorted pairs.

## Complementary squareclasses

**There are no collisions with \(q>4\) and \((q-4)Q\) a square.**
We first prove that any such collision, with \(d=q-4\), must satisfy

\[
 n<64q^{21};\qquad \text{if }q\ge11,\quad 4096n<q^{15}.
\]

For \(q\ge11\) this leaves only recurrence indices \(2\le r\le7\).
A divisibility argument then reduces the entire theorem to 228 rows,
irrespective of the size of \(Q\). The \(10^{38}\) full-problem search
is independent and is not needed for this theorem.

**Proof.** Write \(S=a+b,\ \Delta=b-a\).
The component identity reads \(S^2=q(n+1+S)\), so
\((2S-q)^2=q(4(n+1)+q)\), with \(2S>q\) since
\((a+1)(b+1)>S\). Direct expansion also gives
\((dS+2q)^2-qd\Delta^2=16q\). Consequently for
\(U=d\sqrt{d(4(n+1)+q)}\) one has the *exact* identity

\[
 (U+q\sqrt{qd})^2-(2d\Delta)^2=64d.
\]

For the second decomposition, with \(T=c+e\),
\((2T-Q)^2=Q(4(n+1)+Q)\). Thus
\(V=d\sqrt{d(4(n+1)+Q)}\) is an integer: the radical equals
\(\sqrt{dQ}(2T-Q)/Q\), a rational number with integral square.

For any sorted decomposition its parameter obeys \(q^3\le4n\).
Indeed, with \(x=(a+1)/2,y=(b+1)/2\), the positive integer
\((q-2)x+2-y=(x-1)^2/y\) gives \(y\le(x-1)^2\). The identity
\(x^2y-(x+y-1)^2=(y-1)((x-1)^2-y)\) yields \(q\le x\le a\).
Also \(q\le(2b)^2/(ab)=4b/a\). Together these give the assertion,
and the same estimate applies to \(Q\).

Rationalizing both differences of radicals and using
\(U\ge2d^{3/2}\sqrt n\) now gives

\[
\begin{split}
0 < U+q\sqrt{qd}-2d\Delta &\le 32/(\sqrt d\sqrt n),\\
|V-U| &\le d^{3/2}|Q-q|/(4\sqrt n)
       < d^{3/2}/(2n^{1/6}).
\end{split}
\]

As \(2d\Delta-V\) is an integer, the sum on the right bounds the
distance of \(q\sqrt{qd}\) from the integers. Since
\((q-3)^2<qd=(q-2)^2-4<(q-2)^2\), this distance is
greater than \(1/(2q^2)\): rationalize the difference with the nearest
integer, which is below \(q^2\), and use its nonzero integral numerator.
If \(n\ge64q^{21}\), the second term is at most \(1/(4q^2)\);
the first is at most \(4/q^{21/2}<1/(4q^2)\) for \(q\ge5\),
a contradiction.

For \(q\ge11\), set \(D=q^2-2q-2\). As
\(D^2-q^3d=8q+4\) and \((D-\frac12)^2<q^3d\) (equivalently
\(q^2-10q-25/4>0\)), the nearest integer is \(D\).
The distance is \((8q+4)/(D+q\sqrt{qd})>4/q\).
If \(4096n\ge q^{15}\), the second error is at most \(2/q\)
and the first at most \(2048/q^{15/2}<1/q\). This proves the second bound.

Finally at index \(r\ge2\) let
\(\alpha=(q-2+\sqrt{q(q-4)})/2>q-3\). The geometric sums in the next
section show \(n>4\alpha^{2r-1}\). For \(q\ge11,\ r\ge8\) this implies
\(4096n>16384(8q/11)^{15}>q^{15}\), the desired exclusion.

**The integer lattice and finite certificate.** For \(q\ge32\), use
the stronger fact that \(V\) is a multiple of \(d\). The previously defined
\(D=d(q+2)+6\) is within \(1/2\) of \(q\sqrt{qd}\), with \(D>q\sqrt{qd}\).
Hence \(0<q\sqrt{qd}-d(q+2)<6\). Independently,
\[
 |V-U|< d^{3/2}/(2n^{1/6})
 \le (4^{1/6}/2)\sqrt{d/q}\,d<2d/3.
\]
The other error \(32/(\sqrt d\sqrt n)\) is less than 1 for \(q\ge32\),
using \(4n\ge q^3\). Consequently \(V\) lies within
\(7+2d/3<d\) of the multiple \(d(2\Delta-q-2)\). These two multiples
of \(d\) must be equal. Squaring and using
\(\Delta^2=dn+q(S+1)\) gives exactly
\[
 dQ=8(q+1)a-8b+(q+2)^2+16.
\]
Modulo \(d\), the recurrence has parameter \(q\equiv4\) and its solution is
\(u_r\equiv r^2\pmod d\). Thus \(a\equiv2r^2-1,\ b\equiv2(r+1)^2-1\);
reducing the right side yields \(d\mid4(4r-1)^2\).
There are only 44 such pairs of \(q\ge32,\ 2\le r\le7\), the largest
parameter being 2920. For \(5\le q\le31\), the previous size estimates
bound \(n\); the strictly increasing sequence leaves 184 possible rows
(largest index 18).

For each of these 228 rows the program checks the *whole* range of \(Q\)
by one integer square root. The integer \(t=V/d\) must satisfy
\(t^2=4d(n+1)+dQ\). As \(Q\le(4n)^{1/3}\) and \(4n\ge q^3\), the possible
positive square roots lie in an interval above \(\sqrt{4d(n+1)}\) of
length at most
\(\sqrt d(4n)^{1/3}/(4\sqrt n)<1\).
Therefore \(t=\lfloor\sqrt{4d(n+1)}\rfloor+1\). Recover \(dQ\) by
subtraction. It must be divisible by \(d\), be a square, and satisfy
\(Q^3\le4n\); then \(Q(4(n+1)+Q)\) must be the square of \(2T-Q\),
and the extracted \(T\) must make \(T^2-4n\) a square with the right
parity. No row passes all these necessary conditions.

    python3 crystal_complement_certificate.py

This gives a reproducible finite proof of the exact complementary-squareclass
exclusion. For example, a parameter 5 decomposition cannot collide with any
square parameter, however large; this does not presume that 5 is the smaller
of the two candidate parameters. The general uniqueness problem, for
unrelated squareclasses and different quadratic fields, remains open.

## Equal real quadratic fields

No two distinct integral parameters \(q,Q>4\) with
\(\mathbb Q(\sqrt{q(q-4)})=\mathbb Q(\sqrt{Q(Q-4)})\) can produce the
same admissible crystal product, at any indices.

In a common real quadratic field, the totally positive norm-one units
larger than one are positive integral powers of their least element
\(\lambda>1\): all traces are positive integers \(\ge3\), so such a
minimum exists; dividing by an appropriate power of the minimum leaves
an element in \([1,\lambda)\). The units attached to \(q,Q\),
whose characteristic polynomials are \(X^2-(q-2)X+1\) and its analogue,
are therefore \(\lambda^m,\lambda^\ell\) for positive integers \(m,\ell\).

Let \(\alpha=\lambda^m\), \(H_r=1+\alpha^{-1}+\dots+\alpha^{1-r}\).
The half-components at index \(r\ge2\) are
\(u_r=\alpha^{r-1}H_r^2\) and \(u_{r+1}\) (the geometric formula gives
the prescribed recurrence and \(u_0=0,u_1=1\)). Therefore
\[
  (1+3/(2\alpha))^2
  <\frac{(2u_r-1)(2u_{r+1}-1)}{4\lambda^{m(2r-1)}}
  <(1-1/\alpha)^{-4}.
\]
For the lower bound each factor, normalized by \(2\alpha^{r-1}\) or
\(2\alpha^r\), is at least \((1+1/\alpha)^2-1/(2\alpha)\).
Each normalized factor strictly increases with \(r\).

When \(\operatorname{Tr}(\lambda)\ge4\), \(\lambda>37/10\) and
\((1-1/\lambda)^{-4}<(37/27)^4<37/10\).
Thus the integer exponent \(m(2r-1)\) is determined by the value
(as the floor of \(\log_\lambda(n/4)\)). This also holds for all
\(m\ge2\) when the trace is three: \(\lambda>5/2\),
\(\alpha>(5/2)^2\), and \((25/21)^4<5/2\).

At a common exponent the intervals of normalized values for distinct
indices \(m\) are disjoint. For \(\beta\ge\lambda\alpha\), \(x=1/\alpha\),
we have \(0<x<2/5,\ \lambda>5/2\) and
\[
 (1+3x/2)(1-x/\lambda)^2
 \ge 1+x(3/2-2/\lambda-3x/\lambda)>1.
\]
Hence the upper endpoint for \(\beta\) is below the lower endpoint for
\(\alpha\). If \(m\) is equal then the common exponent fixes \(r\) too.

It remains to compare trace three, \(m=1\), with \(m\ge2\).
Here \(q=5,\ \lambda=(3+\sqrt5)/2\), and the upper endpoint of the
normalized interval is exactly \(\lambda^2\). At \(r=3\) the product is
\(2759\) and
\[
 2759>4(21/8)^6(169/144)^4
      >4\lambda^6(1-1/\lambda^2)^{-4},
\]
using \(13/5<\lambda<21/8\). The normalized product increases with
\(r\), so for every \(r\ge3\) the product is between
\(4\lambda^{2r}(1-1/\lambda^2)^{-4}\) and \(4\lambda^{2r+1}\).
This interval lies strictly between all the \(m\ge2\) windows. At
\(r=2\) the product is \(279\); \(m\ge2\) requires \(Q\ge9\), whose
smallest product is \(17\cdot127=2159\). This exhausts the exceptional case.

## Reproduce the exhaustive check

Compile and run the adjacent crystal_wide_search.cpp:

    clang++ -O3 -std=c++17 crystal_wide_search.cpp -o /tmp/crystal-wide
    python3 crystal_search_crosscheck.py /tmp/crystal-wide
    /tmp/crystal-wide 38

The recurrence classification is the only input. All \(n\le10^{38}\)
are covered; no elliptic-curve list is used. The program checks 2,236,067,975
parabolic indices, 30,170,878 quintic and 238,443 higher-row occurrences,
and recognizes the cubic family by integer inverse bounds. Sixteen small
prime residue masks discard only impossible matches. Every inverse-root
candidate is corrected and tested in integer arithmetic. The result is
zero distinct pairs. The parabolic and quintic residue masks admit
2,439,590 parabolic/cubic, 64,505 quintic/cubic and 88 quintic/parabolic
exact tests. At \(10^{28}\), the population agrees with the separate Python
search without the residue filters: 7,071,066 parabolic and 311,658
quintic-or-higher occurrences. The cross-check above also verifies seven
small bounds independently through \(10^{20}\), and direct divisor
enumeration matches every actual pair at \(10^2,10^3,10^4,10^5,10^6\)
(respectively 1, 6, 18, 43 and 93). Neither the 228-row certificate nor
the wide search assumes completeness of a table of elliptic or
hyperelliptic points.

For the moduli and exponents in this search all recurrence coordinates and
root candidates fit in unsigned 128-bit arithmetic. The search tests the
next product against the limit *before* multiplying. A candidate cubic
root \(w=1+\lfloor\sqrt[3]{\lfloor n/4\rfloor}\rfloor\) follows from
\(4(w-1)^3<C(w)<4w^3\) for \(w\ge3\); square and cube roots seeded by
floating point are adjusted both ways by exact inequalities. Quintic
inversion uses monotone integer binary search. The code is deterministic.

## Fixed parameter pairs without a field condition

There are at most finitely many rational collisions for *each* fixed pair
\(q,Q\ge4,\ q\ne Q\). This statement does not give a uniform bound or
exclude any specific rational point. To see it write \(t=(a+b)/q\), so
the conic \(y^2=q(q-4)t^2+4qt+4,\ y=b-a\) has degree-four map
\(n=q t(t-1)-1\). For \(q>4\), its finite branch values are
\(-1-q/4,\ q/(\sqrt q+2)^2,\ q/(\sqrt q-2)^2\): the first comes from
the derivative in \(t\), and the other two from \(y=0\), i.e. \(a=b\).
The three belong respectively to the negative ray, \((0,1)\), and \((1,\infty)\),
and are strictly monotone in \(q\) within those ranges. Thus distinct
parameters have disjoint finite branch sets. This is also true at \(q=4\),
where the upper positive value disappears and the remaining two are
\(-2,1/4\).

The degree-16 fiber product over the \(n\)-line is geometrically irreducible:
the two covers' Galois closures could only share a subextension ramified at
most at infinity, necessarily trivial over \(\mathbb C\). For \(q,Q>4\)
the joint finite ramification is \(4\cdot4+4\cdot4=32\); above infinity
each cover has cycle type \((2,2)\), whose joint permutation has 8 cycles,
contributing 8. If one parameter equals 4, the contributions change to 28
and 12 (cycle types \((4)\) and \((2,2)\)). The smooth projective model
therefore has genus \(1+(-32+40)/2=5\) in either case.
[Faltings' theorem](https://doi.org/10.1007/BF01388432) yields rational
finiteness. This is complementary to the separate fixed-*index* finiteness
in our earlier paper, which used Siegel.

## Verification boundary

The following are checked in pinned Lean 4.33.1 with Formal Conjectures at
9097e2f90e66d2f6244209cb1c07f7120d17ec53:

* CrystalSquareClass.lean: two genuine sorted decompositions with parameters
  in the same squareclass must be the identical pair (full theorem).
* CrystalComplement.lean: integer_companion produces the integer \(V\);
  pell proves the exact difference-of-squares identity above.
* CrystalComplementFinite.lean: the small-parameter bound is exceeded by
  row 19 in all cases; the two candidate lists have lengths 184 and 44;
  the displayed necessary test rejects every row in their union. This
  calculation uses the Lean kernel, independently of the Python certificate.

From a checkout with the original UniqueCrystalComponents module built, run
lake env lean on each attached Lean file. The complementary-squareclass
**bounds and lattice reduction**, rank-one unit **interval separation**,
and **genus-five analysis** are the mathematical arguments given here.
The separate \(10^{38}\) search is a reproducible exhaustive program, not
a theorem verified in Lean.
