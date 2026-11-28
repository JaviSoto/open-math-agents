# Three unequal exponents in A245212: a quadratic separation

Write an integer with three distinct odd prime factors as
\(n=2^k\prod_{i=1}^3 p_i^{e_i}\), with \(k\ge0\) and all \(e_i\ge1\).
Let \(B_i=e_i+1,\ m=\min_i B_i,\ L=\max_i B_i\). The equation is
\(W(n)+\sigma(n)=2n\tau(n)\), with \(W(n)=\sum_{d\mid n}d\tau(d)\).

**Theorem.** For every fixed positive integer \(c\), there is an explicit
computable bound on **the whole integer \(n\)** for every solution satisfying
\(L\le c m^2\). The three primes, their individual exponents, and \(k\) are
all unrestricted apart from the stated inequality. For example this proves
finiteness for \(2^kp^{4a}q^{8a}r^{12a}\) with \(a,k,p,q,r\) all varying.
Along any infinite sequence of distinct three-odd-prime solutions,
\(L/m^2\) would therefore tend to infinity. This does not rule out such
solutions with an isolated much larger exponent. The bounds prove finiteness;
their sizes do not suggest enumerating up to them.

The simultaneous estimate underlying the theorem is independent of \(c\).
Put \(K=\max(1,k)\), \(b=16^4\), \(F=(b+4)b\). Then
\[
      4\max(K,L)<Km^2 \quad\Longrightarrow\quad
      m<64(F+1)^2=1\,180\,735\,740\,853\,323\,038\,784 .
\]

## Integer separation at three primes

For \(p=p_i,\ e=e_i,\ B=e+1,\ u=p-1\), normalize the weighted and
ordinary divisor sums to \(X=W(p^e)/(Bp^e)\) and \(Y=\sigma(p^e)/(Bp^e)\).
Writing \(z=2^{k+1}\), the exact equation is
\[
 (1+kz)\prod X_i+(z-1)\prod Y_i=(k+1)z.
\]
We use a pair \((f,g)\), with target \(f+g\), either from this exact
equation or, when \(k>0\), its approximation \((k,1)\).
In either case \(g>0,\ f\ge Kg,\ f+g=(K+1)l\), where \(l\) is coprime
to each odd prime. At \(k=0\) the exact pair is \((1,1)\) and we take
\(K=1,l=1\). The true score \(f\prod X_i+g\prod Y_i\) is at most \(f+g\):
for the approximate pair its deficit is
\((k+1)(\prod X_i-1)/(z-1)\).

At each prime choose one of two replacements for \((X,Y)\):

| Replacement | \(\widetilde X\) | \(\widetilde Y\) | Common denominator |
|---|---:|---:|---:|
| Keep the base, discard the reciprocal power | \(p(Bu-1)/(Bu^2)\) | \(pu/(Bu^2)\) | \(Bu^2\) |
| Discard the base | \(1\) | \(1/B\) | \(B\) |

For **each of the eight choices** the replaced score differs from \(f+g\).
For if equality held after clearing denominators, the largest retained prime
\(q\) would divide both product numerators. No \(p_i-1\) at a retained
prime is divisible by \(q\). Therefore \(q\) divides
\((K+1)\prod B_i\), and every retained prime is at most \(\max(K+1,L)\).
If none is retained this last assertion is vacuous.

Return one coordinate at a time to its true value. For a discarded base,
\(X>1,\ Y\ge1/B\). For a retained base the changes are \((d,-u d)\)
with \(d=1/(Bu^2p^e)>0\). At the other two coordinates, the weighted
factors are at least 1 and the ordinary factors are at most \(2/m\),
both before and after replacement. Thus the score increases strictly:
\(4u\le4\max(K,L)<Km^2\). This contradicts the upper bound on the
true score. If \(D\) is the product of the three displayed denominators,
the nonzero difference has absolute value at least \(1/D\).

## Choosing the replacements

Let \(x\ge128\) be at least \(L\) and \(f+g\). Among the four disjoint
intervals \((x^{16^j},x^{16^{j+1}}]\), \(0\le j<4\), one contains no
prime base. Put \(Q=x^{16^j}\) for that interval. Keep the bases at most
\(Q\) and discard the others, which exceed \(Q^{16}\). Then \(D\le Q^9\).
If every \(p_i^{e_i}\ge x^b\), both errors at each factor are at most
\(2/Q^{16}\): for a kept base they decay as \(1/p_i^{e_i}\); otherwise
they decay as \(1/p_i\). Telescoping the two products costs at most
\(48(f+g)/Q^{16}\). If the original score is within \(1/x^b\) of its
target, this contradicts the integer gap, since \(48(f+g)+1<Q^2\).

Start with \(x=128(K+2)(L+1)\). If \(k>0\) and
\(z-1\ge8(k+1)x^b\), use the approximate pair, whose deficit is at most
\(1/x^b\) since \(\prod X_i\le8\). Otherwise use the exact pair, with
scale \(x^{b+4}\) instead when \(k>0\): its coefficient sum fits within
that larger scale. Thus \(p_i^{e_i}\ge x^F\) for every \(i\) suffices.
The dyadic reciprocal-sum bound \(k<2p_i\) and \(L\le Km^2\) give
\(x\le p_i^{14}m^2\). If \(m\ge64(F+1)^2\) the elementary inequality
\(m^{4F}\le2^m\) now yields \(x^F\le p_i^{e_i}\); details, including
the endpoints, are in **ThreeMovingScalar245212.scale**. This proves the
simultaneous estimate.

## Bounding all parameters

If \(k>4c\) and \(m>3\), then \(L\le cm^2\) gives the strict inequality
in the simultaneous estimate. For the remaining finitely many \(k\le4c\)
the [fixed-cofactor prime-power estimate](effective-prime-power-245212.md)
bounds at least one exponent by a computable function \(H(2^k,3)\).
Thus in all cases \(m\le M(c)\), where one can take
\[
 M(c)=64(F+1)^2+9+\sum_{k=0}^{4c} H(2^k,3).
\]
The odd part then has at most \(T(c)=(cM(c)^2)^3\) divisors. The
[divisor-envelope bounds](divisor-envelope-245212.md) give computable
\(E(t),U(t)\) with \(k<E(t)\) and \(\prod p_i^{e_i}\le U(t)\) for
an odd part with \(t\) divisors. The explicit whole-integer cutoff used
in Lean is \(\sum_{t=0}^{T(c)}2^{E(t)}U(t)\).

## Replaying the proof

[ThreeMovingResearch245212.lean](ThreeMovingResearch245212.lean) contains
the full proof starting from the original Formal Conjectures OEIS definition.
From the pinned Formal Conjectures checkout, with its OEIS module built,
run `lake env lean /absolute/path/to/ThreeMovingResearch245212.lean`.
The three audited declarations are **OMA.ThreeMovingGap245212.nonzero**,
**OMA.ThreeMovingOriginal245212.shortest**, and **OMA.ThreeMovingFinite245212.bounded**.

There is a separate, shorter congruence argument for *equal* exponents.
The [dyadic multiplicity result](dyadic-power-245212.md) already excludes
a common even exponent at every odd rank. The [exponent-product
divisibility](exponent-parity-245212.md) excludes all-odd exponents at
every positive rank. [OddRankCommonResearch245212.lean](OddRankCommonResearch245212.lean)
combines them: no \(2^k(p_1\cdots p_{2s+1})^e\) with distinct odd
primes and \(e>0\) solves the equation. More generally, if all exponents
are divisible by \(2^j\), \(j\ge1\), then \(\sum_i e_i/2^j\) is even:
the root has even total prime multiplicity. This is a corollary of
the previously established parity results and is not needed for the
quadratic-sector estimate.
