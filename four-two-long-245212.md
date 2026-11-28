# Four odd primes: two comparable exponent lengths imply absolute finiteness

Let \(n=2^k\prod_{i=1}^r p_i^{e_i}\) satisfy the [A245212 equality](https://oeis.org/A245212)
\(W(n)+\sigma(n)=2n\tau(n)\), where \(W(n)=\sum_{d\mid n}d\,\tau(d)\).
The \(p_i\) are distinct odd primes and the exponents are positive. Let
\(L=\max_i(e_i+1)\) and \(m\) be the second largest length, counting ties.
For any fixed \(C\), restrict attention to \(L\le C m\). Then:

- At every fixed rank \(r\ge2\), the dyadic exponent \(k\) is effectively bounded in terms of \(r,C\).
- At rank four the **entire integer** \(n\) is effectively bounded in terms of \(C\). In particular, only finitely many such solutions exist. Neither the odd primes, the dyadic exponent, nor either of the other two odd exponents is fixed.

Thus in any sequence of rank-four solutions tending to infinity the ratio of the largest to the second largest odd exponent length must tend to infinity. This does not rule out a single dominant exponent.

## Proof

Write \(F=k2^{k+1}+1,\ G=2^{k+1}-1\). With the local factors \(X_i,Y_i\) of the [fixed-rank dyadic estimate](fixed-rank-dyadic-height-245212.md), the exact score is \(F\prod X_i+G\prod Y_i=F+G\), and \(F\ge kG\). The dyadic estimate bounds \(2^k\) by a polynomial in \(L\) at fixed rank; since \(L\le Cm\), both coefficients are polynomial in \(m\).

Assume \(k>8+4C\), and \(m\) is large in terms of \(r,C\). Apply the missing-interval argument from the fixed-rank estimate using the **exact** coefficients \(F,G\). It yields a selection of exact, retained-base or dropped-base moments whose score equals \(F+G\). Indeed, their common denominator is at most \(Q^{3r}\), and their score error is strictly smaller than \(Q^{-3r}\). The cutoff \(Q\) is bounded by a fixed polynomial in \(m\), while the largest odd prime power is at least \(2^{m-1}\); hence at least that coordinate has been rounded. If any base is retained, the largest such base is at most \(\max(k+1,L)\), by divisibility in the cleared score; no odd prime divides the extra factor \(2^{k+1}\) in \(F+G=(k+1)2^{k+1}\).

Restore the exact moments. Restoring a dropped base strictly increases the score. When restoring a retained base \(p_i\), at least one of the two long slots \(v\ne i\) still contributes \(Y_v\le2/m\), regardless of whether it has already been restored. The other \(Y\)'s are at most one. As \(p_i-1\le\max(k,L)\) and \(4\max(k,L)< km\), one has \((p_i-1)\prod_{j\ne i}Y_j<k\). Thus the retained restoration is also strictly increasing, by its exact change formula. There is at least one nontrivial restoration; the two scores cannot both equal \(F+G\).

This proves an explicit dichotomy: \(k\le8+4C\), or \(m\) is smaller than the integer \(\mathrm{threshold}(r,C)\) defined in the checked proof. In the latter case all odd exponents are bounded, so the fixed-rank dyadic estimate bounds \(k\) there too. In rank four, apply the separate fixed-\(k\) whole-integer height and sum its values over the bounded range of \(k\). At higher ranks, the last step requires corresponding fixed-\(k\) control; the dyadic bound holds without it.

## Lean

[FixedTallResearch245212.lean](FixedTallResearch245212.lean) imports only the upstream OEIS module. In the pinned Formal Conjectures checkout, run `lake env lean -j 1 -DElab.async=false /path/to/FixedTallResearch245212.lean`. The theorem `OMA.FixedTallInteger245212.four` bounds the original integer; `.finite` gives the finite set for each \(C\). The formal predicate asks for any two different odd prime factors whose lengths are both at least \(L/C\), expressed without division.
