# Lower bounds for the number of divisors when certain exponents are absent

Write \(n=2^km\), let \(r\) be the number of distinct prime divisors of the odd part \(m\), and let \(D=\tau(m)\). Suppose \(n\) satisfies the equality in OEIS A245212. For every integer \(s\ge2\), if no odd prime occurs with exponent \(2^j-2\) for \(2\le j<s\), then

\[
D^s\ \ge\ \bigl[2^{s-1}(2^s-1)\bigr]^r.
\]

| Exponents absent from the odd part | Necessary bound |
| --- | --- |
| none | \(D^2\ge6^r\) |
| 2 | \(D^3\ge28^r\) |
| 2 and 6 | \(D^4\ge120^r\) |
| every exponent in 2, 6, 14, 30, … | \(D\ge4^r\) |

**Why.** For each exponent \(e\), put \(v=\nu_2(e+2)\). The starting point is [DomTheDeveloper's exponent divisibility obstruction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1376): \(r\le\sum v\). We prove
\[
 2^s(2^s-1)^v\le2^v(e+1)^s.
\]
If \(v<s\), the exclusion and positive exponent give \(e+1\ge2\cdot2^v\); if \(v\ge s\), use \(e+1\ge 2^{v-s}(2^s-1)\). Multiplication gives the stated bound. When every exceptional exponent is absent, the first bound applies to every factor. These finite-level constants are sharp for the divisibility argument: one exponent \(2^s-2\) and \(s-1\) exponents equal to 1 realize equality. This does not produce a solution of the original problem.

**A consequence without assuming a rank bound.** Fix \(C\) and a positive rational \(a/b\) strictly smaller than \([2^{s-1}(2^s-1)]^{1/s}\). Only finitely many inputs with the stated exclusions and with \(D\le C(a/b)^r\) can satisfy the OEIS equality. The rank is at most \(a^s C^s\); applying the [fixed-rank height theorem](fixed-rank-absolute-245212.md) bounds the input itself. When all exceptional exponents are excluded, any \(a/b<4\) works and the rank bound is \(aC\). The height proof concerns inputs with at least one odd prime; pure powers of two are handled separately by the existing reduction.

The [source archive](divisor-floor-ladder-245212.tar.gz) contains the original-input theorems `OMA.DivisorFloorLadder245212.original`, `no_pure_shift`, `OMA.DivisorLadderHeight245212.whole` and `all_levels`. Extract it, then in the pinned Formal Conjectures checkout at `9097e2f90e66d2f6244209cb1c07f7120d17ec53`, run `lake env python3 /path/to/DivisorLadderHeight245212/lean_source_bundle_245212.py --workers 4`.

**Equality at a finite level.** It forces exactly \(r/s\) exponents to be \(2^s-2\), all other exponents to be one, and \(s\mid r\). In the scaled proof equality requires \(\sum v=r\) and equality in every local inequality. Since \(2^s-1\) is odd, local equality implies \(2^v\mid 2^s\), hence \(v\le s\). If \(v=s\), cancelling powers gives \(e+1=2^s-1\); if \(v<s\), the ordinary bound forces \(v=0\) and \(e=1\).

**When every exceptional exponent is absent**, the sharper bound is
\[
 2D\ \ge\ 2^r(3\cdot2^r-1).
\]
This is sharp under the exponent divisibility obstruction alone: take one exponent \(3\cdot2^r-2\) and \(r-1\) exponents equal to one. In particular if \(D\le (a/b)4^r\) for a fixed positive rational \(a/b<3/2\), **there are only finitely many candidate inputs at the critical growth rate itself**. In fact \(2^r\le b\).

More generally, assume an integer \(c\ge2\) lower-bounds the odd part of every \(e+2\). Then
\[
 (c-1)D\ \ge\ (c-1)^r(c\cdot2^r-1).
\]
To see it, combine two factors with the identity
\((cA-1)(cB-1)-(c-1)(cAB-1)=c(A-1)(B-1)\).
Apply it successively with \(A,B\) powers of two, and use \(\sum v\ge r\). If \(D\le(a/b)[2(c-1)]^r\) and \((c-1)a<cb\), this again gives \(2^r\le b\) and an absolute input bound from the fixed-rank theorem. The [extended source archive](divisor-critical-prefactor-245212.tar.gz) checks both the equality classification and these bounds, including the consequence for the original input.
