# No A245212 solution with a complementary odd prime cube

For all distinct odd primes \(p,q\) and all \(k\ge0,a\ge1\), the
[A245212 equality](https://oeis.org/A245212) fails at \(2^k p^a q^3\).
The argument combines the two integer separations below with a finite
calculation. It does not impose a cutoff on the larger prime.

Use the notation and identities (1)–(4) of the
[complementary-exponent proof](complementary-exponent-245212.md), specialized
to \(d=3,h=4\): \(K=k+1,\ z=2^K,\ G=z-1,\ \gamma=k+K/G,\ b=a+1,\ P=p^a,\ u=p-1\).
Here \(p\) is the prime carrying the arbitrary exponent; either prime may be
smaller. The [least-prime exclusions](seven-moving-pair-245212.md) give
\(p,q\ge11\). The [71-divisor result](odd-count-sieve-245212.md) handles
\(4b\le71\). The odd part is not square, so one exponent is 2 modulo 4
by the [exponent parity theorem](ParityBudgetResearch245212.lean). Hence
\(a\equiv2\pmod4\) and we need only \(a\ge18\).

### Bounds valid beyond the original small-exponent split

The identities in the complementary-exponent proof hold for every \(b\).
We record why its two nonzero integers still apply here at \(b\ge19\),
without assuming \(b\ge16h^2\). If \(A-kH=0\), the resonance identity gives
\(p>(4h/9)q>q\), \(k<p-1\), and \(p\mid bh\). As \(p\ge11>4\),
we have \(p\mid b\), so \(a\ge p-1\). It also gives
\(p^{a-5}<2^K\le2^{p-1}\). But \(2(a-5)\ge p-1\) for \(p\ge11\),
contradicting \(p>4\). The other possible zero, \(L(k)=0\), would imply
\(bu-p\mid3p\); here \(bu-p>3p\).

Since \(4b\ge72\), the same minimum-prime estimate gives \(\min(p,q)\le5K\).
The two cofactor inequalities, using \(h=4\), are
\[
 P\le8z(K+p)q^3,\qquad 0<D(\gamma)\le12Kb/q.
\]
The lower cofactor estimate there likewise gives
\(P\ge z^{1/4}/(24Kb)\): its proof uses \(D(k)>0\) with denominator dividing
\(P\), and \(z\mid W(P)W(q^3)-\sigma(P)\sigma(q^3)>0\).

If \(q\le5K\), the first cofactor bound gives \(p^{a-1}\le2000zK^4\).
If \(p\le5K\), positivity of \(L(\gamma)\), whose denominator divides \(G\),
gives either \(P\le18zK\) or \(q\le600zbK^3\), as in the linked proof.
Substitution gives \(P\le2^{34}z^4b^3K^{10}\) in the latter case,
because \(48\cdot600^3<2^{34}\); it holds in the short case too.
As \(p\ge11\) and \(3\log_2 b\le a\) for \(b=a+1\ge19\), both branches imply
\[
                    2a\le34+4K+10\log_2 K.                 \tag{1}
\]

### An absolute cutoff

Suppose \(K\ge320\); (1) then implies \(b\le4K\). If \(p\le5K\),
the absolute difference between \(u^2D(\gamma)\) and the nonzero integer
\(L(k)\) is at most
\[
 4Kb u/G+(4K+p)/P\le80K^3/G+864K^3/2^{K/4}<1/2 .
\]
Thus \(D(\gamma)\ge1/(2u^2)\) and \(q\le24Kb u^2\le2400K^4\).
If \(q\le5K\), the positive deficit
\(D_q=bJ(1+\gamma)-\gamma bV-S\) increases to an integer on replacing
\(\gamma\) by \(k\). The increase is at most \(450K^4/G<1/2\), since
\(V-J\le(9/2)q^2\). Therefore \(1/2\le D_q\le8Kbq^3/u\), giving
\(p\le1+8000K^5\). The numerical inequalities hold at 320 and propagate:
\((321/320)^{12}<2\).

With \(V=W(q^3)\le6q^3\), the nonzero integer \(A-kH\) and identity (1)
of the linked proof give
\[
 z\le1+KH+(z/P)|C(\gamma)|
 \le1+24K^2p^2q^3+48K(6K+3p/2)q^6 .
\]
The latter uses \(H\le bp^2V\), \(|C(\gamma)|\le(6K+3p/2)q^3\), and
\(z/P<12bq^3\) by the same positive divisibility above. Inserting either
\((p,q)\le(5K,2^{12}K^4)\) or \((p,q)\le(2^{14}K^5,5K)\) bounds the
right side by \(2^{83}K^{26}\). This contradicts \(2^{320}>2^{83}320^{26}\)
and \((321/320)^{26}<2\). Hence **\(K\le319, a\le700\)** by (1).

### Finite calculation

Choose the smaller prime \(s\) with \(11\le s\le5K\) and \(k<2s\).
Its exponent is either 3 or \(a\). For its cofactor \(c=2^ks^j\), write
\(w=W(c),s_0=\sigma(c),t=c\tau(c)\). If the remaining prime has
exponent \(f\), the [last-digit identity](odd-divisor-count-245212.md)
requires \(D=(2t-w)(f+1)-s_0>0\) and forces its base to be
\(1+\lfloor(wf+s_0-1)/D\rfloor\). It must divide \(w+s_0\).
The [replay](cubic_power_family_245212.py) checked both orientations:
12,580,812 cases, 11,318,977 positive denominators, 6,013 candidates
passing the divisibility and size tests, and **no exact divisor balance**.
An independent run built every local moment by recurrence, reversed the
loop order, and used the stronger prime-power congruence modulo the
candidate base squared: only 14 cases passed that filter and none
satisfied the original equality.
