# A short exponent on a fixed odd support in OEIS A245212

Suppose a positive integer \(n=2^k p^a q^b r^c\) satisfies the
divisor balance \(W(n)+\sigma(n)=2n\tau(n)\), where
\(W(n)=\sum_{d\mid n}d\tau(d)\). Assume \(7\le p<q<r\le B\)
are primes, \(a,b,c>0\), and \(2\le k\le 2B\).
Let \(E\) be the explicit four-factor height
\(\mathrm{ceiling}(4,B)\) of `HeightLog245212.lean`, and set
\[
 M=4(B+8)(k+1)2^k(E+1)^2(q-1)^2(B-1)^2.
\]
Then
\[
 \min(a,b,c)\le\max\left(
 \left\lfloor\sqrt{\left\lfloor3B/(k+1)\right\rfloor}\right\rfloor,
 \left\lfloor\log_p M\right\rfloor\right).
\]
This is a bound on at least one exponent, not on each independently.

To see this, replace all three odd normalized factors by their rounded
rational expressions, leaving the dyadic factor exact. The rounding
error at \(u^e\) is
\(1/\big((e+1)(u-1)^2u^e\big)\). Its local denominator
\((e+1)(u-1)^2\) cancels when multiplying by the common denominator
of the rounded expression. The factors outside that coordinate are at
most \((k+1)2^k(E+1)^2(q-1)^2(B-1)^2\): among the two remaining odd
bases at least one is at most \(q\). Hence, if the three powers all
exceed \(M\), the integer separation estimate forces the rounded
expression to equal exactly two.

On the other hand, the rounded \(Y\)-factor satisfies
\(Y_{\rm rounded}(2,k)(k+1)=2\), and every odd factor satisfies
\(Y_{\rm rounded}(u,e)(e+1)\le 7/6\). If all three exponents exceed
the displayed square-root bound, the product of the other two lengths
times \(k+1\) exceeds \(3B\). Consequently
\((u-1)\prod_{j\ne i}Y_{{\rm rounded},j}<1\) when restoring each
one of the three odd coordinates. Restoring them strictly increases
the expression. This contradicts equality to two both before and
after restoration. Finally, each odd power exceeds \(M\) whenever all
three exponents exceed \(\lfloor\log_p M\rfloor\).

| \(k\) | \(p,q,B\) | Previous threshold | Pointwise threshold |
|---:|:---|---:|---:|
| 8 | 11, 47, 1381 | 65 | 26 |
| 9 | 17, 23, 5693 | 75 | 41 |
| 10 | 13, 67, 5521 | 75 | 38 |
| 11 | 19, 31, 7561 | 86 | 43 |

The checked statement is
`OMA.RankThreePointHeight245212.shortest` in
`RankThreePointHeight245212.lean`. The verifier
`RankThreePointSlots245212.lean` uses this threshold directly and
tests the three possible choices of a shortest exponent.
Rebuild the one-import source with
`python3 rank_three_point_height_245212.py RankThreePointHeightResearch245212.lean`.
