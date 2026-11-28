# No A245212 equality with a complementary fourth power

For all distinct odd primes \(p,q\), \(k\ge0\), and \(a\ge1\),
\(2^k p^a q^4\) does not satisfy the original A245212 equality.
Here are the constants and finite replay for the fourth-power version of
the [cube argument](cubic-power-family-245212.md).

Keep its notation, now with \(d=4,h=5\). Both odd primes are at least
11 by the [least-prime exclusions](seven-moving-pair-245212.md). The
[71-divisor search](odd-count-sieve-245212.md) handles \(5(a+1)\le71\).
If \(a\) were odd, neither exponent would be 2 modulo 4, contrary to the
exponent parity theorem. Thus the odd part is square; it must be
[a fourth power](odd-squares-245212.md), whence \(4\mid a\) and \(a\ge16\).

The [separation at \(A-kH\)](complementary-exponent-245212.md) remains
valid down to this lower bound on \(a\): resonance would force
\(p>(20/9)q>q\), \(p\mid5b\), and \(p^{a-6}<2^K\le2^{p-1}\).
Now \(p\ge13\), \(p\mid b\), and \(a\ge p-1\), so
\(2(a-6)\ge p-1\), a contradiction. The other integer \(L(k)\) cannot
vanish since \(bu-p>4p\). With \(5b\ge72\), the smaller prime is at most \(5K\).

The cofactor estimates are \(P\le10z(K+p)q^4\),
\(D(\gamma)\le15Kb/q\), and \(P\ge z^{1/5}/(30Kb)\). If \(q\le5K\),
then \(p^{a-1}\le12500zK^5\). Otherwise \(p\le5K\); positivity of
\(L(\gamma)\) as in the cube proof gives either \(P\le20zK\) or
\(q\le750zbK^3\). Hence \(P\le2^{45}z^5 b^4 K^{13}\) in this branch,
using \(60\cdot750^4<2^{45}\). Because \(11^3>2^{10}\) and
\(3\log_2 b\le a\) for \(a\ge16\), both branches give
\[
                   2a\le45+5K+13\log_2 K.                 \tag{1}
\]

If \(K\ge448\), (1) implies \(b\le4K\). When \(p\le5K\), the error
in the integer \(L(k)\) is at most
\(100K^3/G+1200K^3/2^{K/5}<1/2\), so
\(q\le30Kb u^2\le3000K^4\).
When \(q\le5K\), replacing \(\gamma\) by \(k\) in the positive \(D_q\)
changes it by at most \(3000K^5/G<1/2\) since \(V-J\le6q^3\).
Then \(1/2\le D_q\le10Kbq^4/u\) gives \(p\le1+50000K^6\).
The errors are below the stated thresholds at 448 and decrease thereafter:
\((449/448)^{15}<2\).

Finally the nonzero \(A-kH\) bounds \(z\) by
\[
  1+30K^2p^2q^4+60K(15K/2+3p/2)q^8.
\]
Indeed \(H\le bp^2V\), \(V\le(15/2)q^4\), and \(z/P<15bq^4\) by
the positive divisibility in the cube proof. Inserting either
\((p,q)\le(5K,2^{12}K^4)\) or \((p,q)\le(2^{16}K^6,5K)\) bounds this
by \(2^{117}K^{34}\). But \(2^{448}>2^{117}448^{34}\) and
\((449/448)^{34}<2\). Thus \(K\le447\), \(a\le1200\) from (1).

The [leading-digit replay](cubic_power_family_245212.py) tested both
orientations of each smaller prime, with \(4\mid a\): 40,836,312 cases,
36,511,592 positive denominators, 26,236 size-and-divisibility survivors,
and no exact balance. The [independent recurrence replay](replay_complementary_245212.py)
used divisibility by the candidate base squared and then its whole power.
123 cases passed the square test, one passed the full prime-power congruence,
and it failed the original equality. Run both with `--degree 4`.
