# An absolute bound on the smaller odd exponent

In any A245212 counterexample with exactly two odd primes, **the smaller odd-prime exponent is at most 31**. This makes the [rank-two finiteness argument](two-odd-global-245212.md) effective. In fact, writing \(B,C\) for both exponents plus one and \(K=k+1\) for the dyadic exponent plus one, every such solution satisfies
\[
 \min(B,C)\le32,\quad K\le512\cdot32^4=536870912,\quad
 \max(B,C)\le32768\cdot32^6=35184372088832.
\]
The [standalone Lean proof](TwoOddEffectiveResearch245212.lean) derives \(\min(B,C)\le32\) from the original equation for both prime orderings and every \(k\). The last two bounds follow from the [complementary-exponent estimates](complementary-exponent-245212.md) after the previously excluded exponent-one case. After choosing \(p\le6K\) and the exponents, the bigger prime is the unique possible [last digit](odd-divisor-count-245212.md).

Use the notation of the [global finiteness paper](two-odd-global-245212.md): \(p<q,\ u=p-1,\ v=q-1,\ P=p^{B-1},\ Q=q^{C-1},\ z=2^K,\ G=z-1,\ \delta=K/G\). Set \(m=\min(B,C)\), \(M=\max(B,C)\). Suppose \(m\ge33\); we derive a contradiction. We have \(p\le5K\). The [reciprocal bound](two-odd-finiteness-245212.md) gives \(p> (K-1)(m-1)/m\), in particular \(p\ge K/3\) for \(K\ge3\). The cases \(K=1,2\) have previously been excluded ([odd case](four-odd-primes-245212.md), [\(k=1\)](two-odd-finiteness-245212.md)).

From the complementary-exponent proof **\(M\le64m^2 K\)**: use its large-\(b\) estimate with \(b=M,h=m\), and for \(M<16m^2\) the bound is automatic. We use the two nonzero integer estimates \(|GE_\gamma|\ge1,\ |E_k|\ge1\) and the error \(T\) from (2)–(3) of the global paper.

## Rough bound using the exact dyadic parameter

By (6) there, \(q^{C-2}\le3zKBP\). Since \(C-2\ge4\), this gives \(q^2\le\sqrt{3zKBP}\). Hence
\[
 T\le 80\sqrt z K^3 M^2/p^{(m-1)/2}.
\]
In detail, the first term \(q^2(KC+p)/P\) is at most \(4\sqrt z K^2M^2/\sqrt P\). The second term \(p^2(KB+q)/Q\) is at most \(p^2(KM+1)/p^{C-2}\); the third is at most \((K+p^2)/(P p^{C-2})\). These give the displayed bound using \(p\le5K\). Since \(1\le GT\), it follows that
\[
 p^{m-1}\le6400z^3K^6M^4\le2^{37+3K}K^{10}m^8. \tag{1}
\]

## Large dyadic exponent: \(K\ge256\)

First \(m\le5K\). This is immediate for \(m<256\); otherwise \(8\log_2 m\le m/4\) and \(\log_2 K\le K/32\), both by the decreasing ratio \(\log x/x\) on \(x\ge256\). Taking base-two logarithms in (1) gives \(m-1\le37+(3+10/32)K+m/4\), which is sufficient. Therefore
\[
 M<2^{11}K^3,\qquad BC=mM<2^{13}K^4.
\]
In (5) of the global paper the positive quantity \(L-u^2D\) is at most
\[
 5CBK^2/G+CK/P\le 2^{17}K^6/2^K
                  +2^{11}K^4/(K/3)^{m-1}<1/2.
\]
The first summand is less than \(1/4\) at 256 and decreases; the second is less than \(1/4\) even at \(m=16\), because \(4\cdot2^{11}3^{15}<256^{11}\). Thus \(D\ge1/(2u^2)\) and \(q\le 6CBKu^2<2^{21}K^7\). In (3) of the global paper this implies
\[
 T\le \frac{2^{56}K^{18}}{(K/3)^{m-1}},\qquad
 \tfrac94\delta p^2q^2BC\le \frac{2^{63}K^{21}}{2^K}.
\]
For the first inequality insert \(q<2^{21}K^7,\ p\le5K,\ M<2^{11}K^3,\ P,Q\ge(K/3)^{m-1}\) separately into the three summands of \(T\). In the second use \(G\ge z/2\). Since \(K/3\ge K^{4/5}\) and \(2^{56}\le K^7\), the first bound is at most \(K^{25-(4/5)32}<1/2\). The second is below \(1/2\) at 256 and decreases. Hence \(|E_k|<1\), contradiction.

## Smaller dyadic exponents: \(3\le K\le255\)

This part uses only the two positive integer parameters \(K,m\); neither primes nor original OEIS inputs are scanned. Set \(\ell=\max(3,1+\lfloor(K-1)(m-1)/m\rfloor)\), \(h=5K\), \(R=\ell^{m-1}\), and \(U=64m^2K\). Thus \(\ell\le p\le h,\ P,Q\ge R,\ B,C\le U,\ BC\le mU\).

First (1) fails at \(m=119\) for all 253 choices of \(K\). It continues to fail above 119 because \(\ell\) is nondecreasing and \((120/119)^8<3\le\ell\). Check \(33\le m\le118\) by either of these two tests.

1. The bound \(q^{C-2}\le3zKBP\) gives \(q^2/P\le(3zKU)^{2/(m-2)}R^{-(m-4)/(m-2)}\). Also \(q/Q\le p/R\), since \(q^{2-C}\le p^{2-m}\le h/R\) (and in fact it is at most \(p/R\)). The following sufficient conditions give \(GT<1\), by retaining less than one third for each of its three terms:
   \[
   [3G(KU+h)]^{m-2}(3zKU)^2<R^{m-4},\quad
   3Gh^2(KU+h)<R,\quad 3G(K+h^2)<R^2 .
   \]
2. If \(2(KmUh R+GUK)\le GR\), the error in the integer \(L\) is at most \(1/2\), so \(q\le y=6mUK h^2\). Put \(A=y^2(KU+h)+h^2(KU+y)\) and \(B'=K+hy\). Formula (3) then gives \(|E_k|<1\) whenever
   \[
   4G(AR+B')+9K h^2y^2mU R^2<4G R^2 .
   \]

Run the [exact integer replay](two_odd_effective_245212.py):

    python3 two_odd_effective_245212.py

Every one of the \(253\cdot86=21758\) boxes passes at least one test. There is no remaining case with \(m\ge33\). The standalone proof combines the table with the [simultaneous separations](TwoOddGlobalGap245212.lean); its theorem \(\texttt{OMA.TwoOddEffectiveAll245212.smaller_exponent}\) depends only on \(\texttt{propext}\), \(\texttt{Classical.choice}\), and \(\texttt{Quot.sound}\).

The same [finite scalar tests are also checked in Lean](TwoOddEffectiveTable245212.lean);
the theorem `OMA.TwoOddEffectiveTable245212.ranges` covers every displayed
index and depends only on `propext` and `Quot.sound`. An independent rational
interval calculation gave the same exclusion in every cell, allowing the
three error terms to share their remaining margin.

The Lean proof uses integer comparisons throughout. For instance, for \(n\ge256\), \(2^{65}n^{21}\le2^n\): it holds at 256, and \((257/256)^{21}<2\) propagates it by induction. Likewise \(K^{20}\le2^K\) and \(m^{16}\le2^m\) above 256. Squaring (1) and using \(p^2\ge8\) gives \(3(m-1)\le74+7K+m\), enough for \(m\le5K\). Also \(K\le3p\) implies \(K^4\le p^5\) for \(K\ge256\); thus \(p^{m-1}\ge K^{24}p^2\) when \(m\ge33\). These inequalities replace square roots and real logarithms in the large-\(K\) comparison. They lead to the same threshold.
