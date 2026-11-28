# Twice a number with exactly three distinct odd prime factors cannot solve A245212

Let $p<q<r$ be odd primes. For every choice of positive exponents $a,b,c$,
the input $n=2p^a q^b r^c$ fails the [A245212 divisor equation](https://oeis.org/A245212).
There is no size cutoff on any base or exponent. Together with the previously
checked [two-odd-prime theorem](two-odd-nonexistence-245212.md) and
[odd four-prime theorem](four-odd-primes-245212.md), this implies that any
counterexample with exactly three distinct odd primes must be divisible by four.

The [Lean statement](RankThreeTwice245212.lean) joins three exhaustive cases:

* If the least prime is at least five, bounding the normalized divisor products
  leaves only the support (5,7,11). A separate fixed-support proof rules it out
  for arbitrary exponents.
* If the least prime is three and the middle prime is at least 17, the Euler
  product bound gives $q\le31$ and $r\le16(q-1)/(q-16)$. There are
  70 ordered prime pairs in the remaining range. Exact sign and exponent
  certificates eliminate each whole support.
* For middle prime 5, 7, 11, or 13, put
  $X_s(d)=W(s^d)/[(d+1)s^d]$, where $W(t)=\sum_{u\mid t}u\tau(u)$.
  A solution would require $5X_3(a)X_q(b)<8$. Monotonicity implies that
  at least one of the two exponents lies below the corresponding cutoff
  pair: (4,4), (7,6), (21,12), or (42,21). This gives 109 short-cofactor
  tests, each still covering an arbitrary final prime and the other exponents.

One change makes the hardest calculations practical. When finishing with
a prime power $r^c$, let $A=W(h)$ and $S=\sigma(h)$ for the prefix
already chosen. The divisor equation forces $r^c\mid A-(r-1)S$.
When that difference is nonzero, its size cuts off exponents without ever
building the power. [The optimized test](CofactorGuardFast245212.lean)
is proved equivalent to the original one, including when the difference is zero.

**Reproduce:** download and extract the [source-only archive](rank-three-twice-245212.tar.gz).
From a built formal-conjectures checkout at `9097e2f90e66d2f6244209cb1c07f7120d17ec53`,
run `lake env python3 /path/to/RankThreeTwice245212/lean_source_bundle_245212.py --workers 4`.
Its manifest identifies all 182 Lean modules. The final theorem is
`OMA.RankThreeTwice245212.original`; its only reported axioms are
`propext`, `Classical.choice`, and `Quot.sound`.
Archive SHA-256: `bf792319f98abd555fd147277dddf86f8842c931a99597c3be95347d456617f6`.
