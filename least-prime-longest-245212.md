# A largest exponent on the smallest odd prime gives an absolute height bound

Let \(p<q<r\) be odd primes and \(a,b,d>0\). Every A245212 solution
\(n=2^k p^a q^b r^d\) with \(a\ge\max(b,d)\) satisfies the **same explicit, computable** bound. This includes ties and puts no bound on \(k\) or any prime. The [standalone Lean proof](LeastTallResearch245212.lean) gives the bound and proves the result as **OMA.LeastTallOriginal245212.original**.

Together with [the bound for a largest exponent on the largest prime](two-long-exponents-245212.md), this leaves just the middle prime in any sequence of distinct solutions tending to infinity: eventually \(b>\max(a,d)\) and \(b/\max(a,d)\to\infty\).

## The sign at the smallest prime

Use the weighted and ordinary prime-power averages \(X_i,Y_i\) and their three replacements from [the dyadic bound](rank-three-dyadic-log-245212.md). Put \(L=a+1\), \(f=1+k2^{k+1}\), and \(g=2^{k+1}-1\). The physical equation is
\[
 f\prod X_i+g\prod Y_i=f+g,\qquad f\ge kg.
\]
It suffices to treat \(k>66,\ p\ge33,\ L\ge32\). The first two exceptions give bounded \(k\) by \(k<2p\), and rank three is already effectively bounded at each fixed \(k\). Bounded \(L\) bounds the divisor count and hence the whole integer.

Write \(u=p-1\). For *every* base \(s\ge p\), the identity \(X=1+(1-Y)/(s-1)\) gives \(u(X-1)\le1,\ X\le33/32\). Telescoping the three-factor product gives
\[
 u(\prod X_i-1)\le (33/32)^2+33/32+1<13/4 .
\]
Every exact or rounded ordinary average is at most \(33/64\), since it is at most \(s/[(e+1)(s-1)]\) with \(s\ge33,\ e\ge1\). And \(\prod Y_i\le2/L\le1/16\). Thus
\[
 g\,u(33/64)^2 < f.
\]
Indeed the reverse inequality, multiplied by \(\prod X_i-1\ge0\) and combined with \(f(\prod X_i-1)=g(1-\prod Y_i)\), would give \(15/16\le(33/64)^2(13/4)\).

Suppose the physical score of a replaced configuration equals \(f+g=(k+1)2^{k+1}\). The largest prime with its reciprocal power removed divides the common target times the denominators. It cannot divide \(2^{k+1}\); the same denominator argument as for the dyadic estimate bounds every such retained prime by \(\max(k+1,L)\).

Restoring a discarded base strictly increases the score. Restoring a retained base \(s\) adds \(\delta(fX'_jX'_\ell-g(s-1)Y'_jY'_\ell)\), with \(\delta>0\). For \(s=p\) this is positive by the inequality above. For any other \(s\), one of \(j,\ell\) is the longest coordinate; its ordinary average is at most \(2/L\). If \(s\le L\), then \((s-1)Y'_jY'_\ell\le2<k\). If \(s\le k+1\), the same strict inequality follows because both ordinary factors are at most \(33/64\). Thus **every changed coordinate increases the score**, including when the other factors have already been restored.

## Ensuring a change

Take \(x=128(f+g+1)(L+1)\). The unconditional logarithmic dyadic bound gives \(2^k\le C(L+1)^E\) with fixed \(C,E\); hence \(x\le512(C+1)^2(L+1)^{2E+1}\). Put \(D=16^7\). For
\[
 L\ \ge\ 2[512(C+1)^2]^D+16[(2E+1)D+1]^2+64
\]
one has \(p^{L-1}>x^D\). This follows by the same elementary squaring and absorption estimate used in the dyadic theorem. Classify the six scales \(s,s^{e_s}\) around an empty interval \((Q,Q^{16}]\) as before. The longest coordinate **cannot** be kept exact because its power exceeds the largest cutoff. Therefore the mixed score cannot equal its target: it would strictly increase on restoration to the exact score, which already equals that target.

On the other hand its cleared denominator is at most \(Q^9\), and its approximation error is at most \(48(f+g)/Q^{16}<Q^{-9}\). This contradiction bounds \(L\); the effective bound at bounded divisor count completes the proof.
