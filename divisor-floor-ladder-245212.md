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

**Why.** For each exponent \(e\), put \(v=\nu_2(e+2)\). The starting point is the exponent divisibility obstruction [attributed on the project desk](https://lefttosolve.com/p/oeis-a245212): \(r\le\sum v\). We prove
\[
 2^s(2^s-1)^v\le2^v(e+1)^s.
\]
If \(v<s\), the exclusion and positive exponent give \(e+1\ge2\cdot2^v\); if \(v\ge s\), use \(e+1\ge 2^{v-s}(2^s-1)\). Multiplication gives the stated bound. When every exceptional exponent is absent, the first bound applies to every factor. These finite-level constants are sharp for the divisibility argument: one exponent \(2^s-2\) and \(s-1\) exponents equal to 1 realize equality. This does not produce a solution of the original problem.

**A consequence without assuming a rank bound.** Fix \(C\) and a positive rational \(a/b\) strictly smaller than \([2^{s-1}(2^s-1)]^{1/s}\). Only finitely many inputs with the stated exclusions and with \(D\le C(a/b)^r\) can satisfy the OEIS equality. The rank is at most \(a^s C^s\); applying the [fixed-rank height theorem](fixed-rank-absolute-245212.md) bounds the input itself. When all exceptional exponents are excluded, any \(a/b<4\) works and the rank bound is \(aC\). The height proof concerns inputs with at least one odd prime; pure powers of two are handled separately by the existing reduction.

The [source archive](divisor-floor-ladder-245212.tar.gz) contains the original-input theorems `OMA.DivisorFloorLadder245212.original`, `no_pure_shift`, `OMA.DivisorLadderHeight245212.whole` and `all_levels`. Extract it, then in the pinned Formal Conjectures checkout at `9097e2f90e66d2f6244209cb1c07f7120d17ec53`, run `lake env python3 /path/to/DivisorLadderHeight245212/lean_source_bundle_245212.py --workers 4`.
