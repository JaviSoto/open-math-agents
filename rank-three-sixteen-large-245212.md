# Three odd primes, none below seven, at exact dyadic order four

Write `τ=σ₀`, and put `W(n)=∑_{d|n} d τ(d)`. The original OEIS
A245212 balance is `W(n)+σ₁(n)=2nτ(n)`. There is no solution

    n = 16 pᵃ qᵇ rᶜ,    7 ≤ p < q < r prime,    a,b,c ≥ 1.

The statement covers arbitrary positive exponents. Together with separate
results for least odd prime 3 and 5, it can cover the entire valuation-four,
three-odd-prime case. This paper proves only the least-prime-at-least-seven
part. It does not resolve the OEIS conjecture at other valuations or ranks.

## Which supports need checking?

For a prime power put `X(p,e)=W(pᵉ)/(pᵉ(e+1))` and
`Y(p,e)=σ₁(pᵉ)/(pᵉ(e+1))`. The two terms satisfy
`X=1+(1−Y)/(p−1)`; as the exponent increases, X increases and Y decreases.
The exact cofactor 16 has `W=129, σ₁=31, 16τ(16)=80`. The Euler bound
therefore requires

    160 (p−1)(q−1)(r−1) ≤ 129 p q r.

Also `129 X(p,a) X(q,b) < 160`, because the third X is at least one
and the product of the three Y factors is positive. The Euler inequality
leaves seven ordered pairs; the table lists all possibilities for the
last prime after this particular test.

| p | q | upper bound on r | number of possible r |
|---|---|-----------------|----------------------|
| 7 | 11 | unrestricted | infinite |
| 7 | 13 | unrestricted | infinite |
| 7 | 17 | 1706 | 259 |
| 7 | 19 | 140 | 26 |
| 7 | 23 | 60 | 8 |
| 7 | 29 | 38 | 2 |
| 11 | 13 | 25 | 3 |

For the two unrestricted rows, the strict bound on the first two moments
forces `a≤6 or b≤6` for (7,11), and `a≤12 or b≤12` for (7,13).
At each resulting exact prefix the existing two-prime Euler and terminal
digit tests apply to an arbitrary last prime and arbitrary remaining
exponents. The proofs are `SixteenMoving7P11.exclude` and
`SixteenMoving7P13.exclude` in the `OMA` namespace.

## Why are the exponent checks finite?

On the bounded supports, round the three odd-prime moments to the rational
functions given by dropping their reciprocal prime powers. The prior
denominator and exponent bounds imply that sufficiently small errors
force the rounded score to equal the exact score. At all three exponents
above the threshold, restoring the dropped terms increases the score
strictly. These two conclusions contradict one another.
`RankThreeSixteenFixed245212.one_short` implements this argument. At every
base in the table the threshold is 82, so at least one exponent is at most
82. It is only one exponent that has been bounded here.

Fix the corresponding prime power in the cofactor h with moments
`A=W(h), S=σ₁(h), T=hτ(h)`. The two-prime Euler excess and the earlier
two-coordinate rounding bound give a finite interval for at least one of
the two remaining exponents. For the largest family, (7,17), select a
globally least exponent z. Both other exponents are now at least z; if
their two lower moment values already satisfy
`A X(i,z) X(j,z) ≥ 2T`, the whole quadrant is impossible. In the remaining
rows, an exact prefix h′ and terminal prime j require
`j | W(h′)+σ₁(h′)`. For each prefix surviving this congruence the
reverse-digit formula determines its only possible terminal exponent; an
integer equality checks the actual balance.

## Replay

From the OEIS research workspace generate the single-import proof:

    python3 rank_three_sixteen_source_245212.py RankThreeSixteenLargeResearch245212.lean

Check the generated source from the pinned Formal Conjectures project, using
the OEIS 245212 object from that same project. From the research workspace:

    research="$PWD"
    (cd /Users/javi/code/open-math-agents/.oma/formal-conjectures &&
      env LEAN_PATH=/private/tmp lake env lean -j 1 -DElab.async=false "$research/RankThreeSixteenLargeResearch245212.lean")

For parallel replay, `rank_three_sixteen_fixed_245212.py` emits individual
modules from exact prime bounds and checks those modules in the kernel.
The generated single file needs none of these intermediate modules.
Its final declaration is `OMA.RankThreeSixteenLarge245212.original`, on the
original natural number n with `n.factorization 2=4`. The code tests
primality in the kernel and includes a separate proof that the 298 listed
bounded supports exhaust the Euler inequality.
