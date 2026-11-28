# Only finitely many A245212 exceptions at each fixed number of odd primes

For every integer \(R\), only finitely many positive integers \(n\) with **between one and \(R\) distinct odd prime divisors** satisfy
\[
 a(n)=\sigma(n),\qquad\text{equivalently}\qquad
 \sum_{d\mid n}d\,\tau(d)+\sigma(n)=2n\tau(n).
\]
Here \(a\) is the original [OEIS A245212](https://oeis.org/A245212) sequence. More precisely, the proof defines a single function \(K(r)\) such that every such solution is at most \(K(r)\), where \(r\) is its number of distinct odd prime factors. Its value is specified by arithmetic bounds, not by taking a maximum over unknown solutions. The power of two, the ranks allowed up to \(R\), the odd primes and all their exponents are otherwise unrestricted.

Pure powers of two form a known infinite family and are excluded by the lower bound on the rank. If there are infinitely many other solutions, their odd-prime ranks must be unbounded. The theorem does **not** say that there are no isolated counterexamples or that there are finitely many in total. The individual bounds are too large to make a direct search practical.

## Where the new step enters

Write \(n=2^k\prod_{i=1}^r p_i^{e_i}\) and \(L=\max_i(e_i+1)\). The [four-prime argument](four-odd-absolute-245212.md) bounds \(k\) at every rank and bounds \(L\) at every rank if \(k\ge256\). At ranks one through four, earlier fixed-\(k\) bounds on the entire integer then suffice. The remaining difficulty is \(r\ge5\) and small \(k\), including odd \(n\) (\(k=0\)).

As in the large-\(k\) argument, a gap between the scales of the primes and their powers gives an exact identity with three types of factors: fully exact factors, retained prime bases with their reciprocal-power terms omitted, and dropped bases at which both moments are replaced by their infinite-prime limits. For very large \(L\) the longest prime power is not exact. Every retained base is at most \(L\). Restore the exact factors one by one. The starting and ending scores are equal.

For an odd prime, the ordinary normalized moment \(Y_i=\sigma(p_i^{e_i})/[(e_i+1)p_i^{e_i}]\), and either rounded version, is at most \(3/4\) and at most \(2/(e_i+1)\). Hence for **any two distinct** coordinates \(i,v\), in any intermediate configuration,
\[
    (e_v+1)\prod_{j\ne i}Y_j\le2(3/4)^{r-2}\le 27/32.
\]
This estimate makes the restoration argument work even when the two weights are equal at \(k=0\). Restoring a retained coordinate \(i\) other than the longest \(v\) increases the score by at least
\[
         G/(32L^3p_i^{e_i}),\qquad G=2^{k+1}-1.
\]
If restoring the longest coordinate loses score, its loss is at most \(G/p_v^{e_v}\). The sign of the same change gives \(32(e_i+1)\le27p_v\). For sufficiently large \(L=e_v+1\), uniformly for \(p_i,p_v\le L\), this forces \(32L^3p_i^{e_i}<p_v^{e_v}\). One elementary ingredient is \(L^{q-1}\le q^{L-1}\) for \(2\le q\le L\). Thus even one other retained coordinate would gain more than the longest can lose. Dropped-base restorations always increase the score, so the longest base alone is retained.

Combine the exact factors with \(2^k\) into \(h\). The resulting [mixed divisor equality and strict sign](uniform-weighted-gap-245212.md) bound \(L\) absolutely at fixed \(r\): the number of prime factors of \(h\) is at most \(r+1\), and \(h\le(L+1)^{D_r}\). It follows that the odd part has at most \(L^r\) divisors. Applying the earlier fixed-divisor-count bound for the entire integer across this bounded range finishes the proof.

## Verification

The [standalone Lean source](FixedRankAbsoluteResearch245212.lean) checks in the upstream Formal Conjectures checkout at 9097e2f90e66d2f6244209cb1c07f7120d17ec53: run **lake env lean /path/to/FixedRankAbsoluteResearch245212.lean**. The final declarations are OMA.FixedRankAbsolute245212.absolute (the height) and OMA.FixedRankAbsolute245212.bounded_finite (the finite set). The [111-module source archive](fixed-rank-absolute-245212.tar.gz) includes its hash manifest and a parallel replay script. Neither verification trusts a numerical search.
