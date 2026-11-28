# OEIS A245212: exact dyadic order five with three odd primes at least seven

Write `W(n)=Σ_{d|n}dτ(d)`, `S(n)=σ(n)`, and `T(n)=nτ(n)`. The
original divisor balance is `W(n)+S(n)=2T(n)`. We consider exactly
`n=32·p^a·q^b·r^c`, with ordered odd primes `7≤p<q<r` and three
positive exponents. Nothing in the statement bounds the size of n.

For 32 the three moments are 321, 63 and 192 respectively. The
necessary Euler inequality is therefore

    384(p−1)(q−1)(r−1) ≤ 321pqr.

It leaves eight prefixes with unrestricted r: the least prime is 7
and the middle prime is 11, 13, 17, 19, 23, 29, 31 or 37. For these
prefixes the respective upper bounds on min(a,b) are
2, 3, 5, 6, 10, 19, 24 and 81. They follow from monotonicity of the
weighted local average and from the strictly positive ordinary divisor
moment in the original equation. At least one of the two specified powers
can therefore be fixed. The cofactor equations bound the other exponent
or the final prime, according to which side of the two-prime Euler limit
the prefix lies. Exact integer division reconstructs the remaining
exponent. In particular these eight checks place no prior bound on r.

The remaining prime supports are exhausted as follows.

| p | q | Largest permitted r from the Euler inequality | Number of prime r |
|---:|---:|---:|---:|
| 7 | 41 | 2792 | 393 |
| 7 | 43 | 658 | 105 |
| 7 | 47 | 282 | 45 |
| 7 | 53 | 167 | 23 |
| 7 | 59 | 126 | 13 |
| 7 | 61 | 117 | 12 |
| 7 | 67 | 100 | 6 |
| 7 | 71 | 92 | 4 |
| 7 | 73 | 89 | 3 |
| 11 | 13 | 260 | 49 |
| 11 | 17 | 43 | 7 |
| 11 | 19 | 34 | 3 |
| 13 | 17 | 26 | 2 |

There are 665 bounded prime triples. Their exponents are still unrestricted.
At fixed largest base B=r, a simultaneous integer separation on all three
odd powers bounds the least exponent by the larger of ⌊√B⌋ and

    ⌊log₇(32 · 64 B⁹ · (E+1)⁴)⌋,

where E is the explicit four-prime exponent ceiling from the general
height theorem. This bound is at most 69 on these triples. Fix each
possible shortest power, and write the number as h·uᵇ·vᶜ. The weighted
moments and monotonicity first exclude entire exponent quadrants.
In the remaining cases a short-exponent bound is tested in both
orientations; the terminal prime power is checked by an exact integer
reconstruction. Lean verifies the support classification as well as the
individual exclusions.

## Reproduction

In the research workspace, generate the single-import source:

    python3 rank_three_power_source_245212.py RankThreeThirtyTwoLargeResearch245212.lean

The entry point is `OMA.RankThreeThirtyTwoLarge245212.original`. Its
hypotheses on the original input n are positivity, `n.factorization 2=5`,
three distinct odd prime factors, and each such factor at least seven.
The independent modular replay uses `rank_three_power_rows_245212.py`
for the eight unrestricted prefixes and `rank_three_power_fixed_245212.py`
for the thirteen remaining prime-pair families. The latter accepts
`--out /private/tmp --jobs 4` for the row modules, followed by
`--out /private/tmp --jobs 4 --join` for their family proofs, from the
research workspace with its pinned helper modules available.

The least-prime 3 and 5 cases at exact dyadic order five are separate.
