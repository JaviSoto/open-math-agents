# An arbitrary fixed cofactor has only finitely many extensions by two odd prime powers

Fix **any positive integer** \(h\). There are only finitely many \(n=h p^{B-1}q^{C-1}\) that satisfy the [A245212](https://oeis.org/A245212) equality, where \(p,q\) are distinct odd primes coprime to \(h\) and \(B,C\ge2\). Neither of the two primes or exponents is prescribed. This includes cofactors whose weighted divisor sum has an exact Euler resonance; it does not require \(h\) to be a power of two.

Consequently, for every fixed \(k\) there are only finitely many solutions on **at most four distinct odd primes** at \(2^k m\) with \(m\) odd. One may instead fix a bound on any one odd prime divisor, leaving \(k\) unrestricted. These are finiteness assertions, not exclusions of all four-prime exceptions.

## The exceptional slope

Write \(A=W(h),\ S=\sigma(h),\ T=h\tau(h)\); all are positive. At a prime power \(P=p^{B-1}\), put \(U=\sigma(P), W=W(P), X_p=W/(BP), Y_p=U/(BP)\). Use \(Q=q^{C-1}, Z,V,X_q,Y_q\) analogously. The balance is
\[
       A X_p X_q+S Y_p Y_q=2T.\tag{1}
\]
Both \(X\)'s exceed 1, so \(A<2T\). At any prime power, \(1<X_p\le p/(p-1)\), \(0<Y_p\le p/((p-1)B)\). When \(p\) is fixed and \(B\to\infty\), \(X_p\to p/(p-1)\).

Suppose there are infinitely many distinct solutions and order \(p<q\). Pass to a subsequence on which each integral coordinate is constant or tends to infinity. Bounded primes give finite [fixed-support solutions](fixed-prime-support-245212.md). Bounded exponents give only finitely many prime pairs, since for fixed exponents the normalized expression in (1) strictly decreases as either base increases: both prime-power averages are positive sums of negative powers of the base. If both bases and at least one exponent tend to infinity, (1) would give \(A=2T\). We are therefore left with fixed \(p\) and \(q\to\infty\). If \(B\) remains bounded there is only one prime power to append to a fixed cofactor, so the [cofactor divisibility bound](PrimePowerDiv245212.lean) bounds it. Otherwise \(B\to\infty\) and (1) gives the **exact resonance** \(Ap=2T(p-1)\). Put \(u=p-1\).

The [Lean certificate](CofactorPairPoleResearch245212.lean) proves the following identities and slope bounds starting from the original equality. Use \(uW+U=pBP\) and \(uU=pP-1\). Substituting the resonance into (1) gives
\[
 Q(CA-Su)U = u\{A W(V-CQ)+S U(Z-Q)\},\qquad
 uW=(Bu-1)U+B.\tag{2}
\]
Here \(CA-Su>0\) since the right side is positive. The first omitted divisor and the geometric-series bound give
\[
 (C-1)Q\le q(V-CQ)\le2C Q,\qquad 0\le q(Z-Q)\le2Q .
\]
Since \(W\le BU\), we obtain \(q(CA-Su)\le 2u(ABC+S)\). Also \(C\le(Su+1)(CA-Su)\), because \(A\ge1\) and the last factor is a positive integer. Thus
\[
               q\le 2u(A+S)(Su+1)B.\tag{3}
\]
When \(C\ge3\), the lower bound in (2) gives \(qC>(Bu-1)(C-1)\ge BC\), since \(u\ge2,B\ge2\). In particular **\(B<q\)**.

## The integral contradiction

If \(C\) stays bounded, apply the [cofactor bound](PrimePowerDiv245212.lean) in the other direction:
\[
 p^{B-1}\le |A V-(p-1)S Z|\le (A C+uS)\,\tfrac32 q^{C-1}.
\]
By (3) the right side is bounded by a fixed polynomial in \(B\), impossible. Hence \(C\to\infty\) and \(B<q=O(B)\). In the forward direction the same bound gives
\[
 q^{C-2}\le A W+S U\le\tfrac32(AB+S) p^{B-1}.
\]
Taking logarithms shows \(C=o(B)\), since \(p\) is fixed and \(q\to\infty\). Thus \(q>\max(2T,p,B,C)\) eventually.

Set \(v=q-1\). The integer
\[
 E=2TBCu^2v^2-pq\{A(Bu-1)(Cv-1)+Suv\}
\]
is **nonzero**, since modulo \(q\) it is \(2TBCu^2v^2\), and none of those factors is divisible by the prime \(q\). But expanding (1) with the exact finite geometric moments gives
\[
 E=\frac{q[A(Cv-1)-Suv]}{P}
   +\frac{p[A(Bu-1)-Suv]}{Q}
   +\frac{A+Suv}{PQ}.
\]
All numerators grow at most polynomially in \(B\), whereas \(P=p^{B-1}\) and \(Q=q^{C-1}\) dominate every fixed polynomial in \(B\) (use \(q>B\) and \(C\to\infty\)). Hence \(E\to0\), impossible for nonzero integers. This proves the fixed-cofactor assertion. The cleared expansion and modular nonvanishing are also in the linked Lean certificate; the subsequence argument is written mathematics.

## Consequence for four freely moving odd primes

At fixed \(k\), ranks through three are [already finite in Lean](three-odd-finiteness-245212.md). Consider an escaping sequence with exactly four odd primes. By [the bounded dyadic excess theorem](parity-budget-245212.md), after omitting a finite set there are bounded prime powers whose total visible excess exceeds \(k+v_2(k+1)\). Pass to a subsequence with the same bounded powers. If there are two such factors, absorb them in \(h\) with \(2^k\) and apply the theorem just proved. If there is just one, \(r^a\), its excess alone exceeds the threshold. As in the [three-prime proof](three-odd-finiteness-245212.md), \(r^a>W(2^k)\) prevents resonance at \(2^k r^a\). The bounded-factor lemma there applies to **any** prescribed number of remaining primes: apply it to the three here. It supplies a second bounded prime power, which can again be fixed on a subsequence. Both alternatives contradict escape. Finally the reciprocal bound \(k<2p\) for every odd prime factor \(p\) gives the variant with one bounded odd prime and free \(k\).
