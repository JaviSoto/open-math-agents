# OEIS A245212: exact dyadic order six, least odd prime at least eleven

For a positive integer n satisfying the divisor balance
`Σ_{d|n}dτ(d)+σ(n)=2nτ(n)`, suppose that exactly 2⁶ divides n and that
its odd part has three distinct prime factors. Then n must have an odd
prime factor below eleven. This result treats all exponents, with no
upper bound on n.

Let p<q<r be the three odd primes. The ordinary, weighted and mass
moments of 64 are respectively 127, 769 and 448. If p≥11, the Euler
inequality becomes

    896(p−1)(q−1)(r−1) ≤ 769pqr.

The inequality limits p to at most 20 and q to at most 34, and the
prime check leaves the two unbounded last-prime families (11,13) and
(11,17). Their first two exponents cannot both reach 8 and 52,
respectively. This produces 116 oriented first-power rows. In each one
the two remaining exponents and the last prime are treated without any
input bound, by the exact cofactor moments and the reverse-digit identity.
In the remaining eight families the Euler inequality gives the following
exhaustive list sizes:

| p | q | Upper bound for r | Number of prime r |
|---:|---:|---:|---:|
| 11 | 19 | 288 | 53 |
| 11 | 23 | 76 | 12 |
| 11 | 29 | 45 | 4 |
| 11 | 31 | 40 | 1 |
| 13 | 17 | 82 | 15 |
| 13 | 19 | 53 | 8 |
| 13 | 23 | 35 | 2 |
| 17 | 19 | 26 | 1 |

Each of the 96 fixed supports first uses simultaneous rounding of
the odd powers to bound the smallest exponent. The cofactor and the
remaining two powers are tested using the interval and prime-power
congruences detailed in the companion note on exact dyadic order five.

From the research workspace:

    python3 rank_three_power_source_245212.py --k 6 --fast RankThreeSixtyFourLargeResearch245212.lean

The one-import proof of `OMA.RankThreeSixtyFourLarge245212.original`
passed the pinned Lean kernel in 192.77 seconds with peak physical memory
1,818 MiB. Lean reported only `propext`, `Classical.choice`, and `Quot.sound`.
The checked source is 354,635 bytes; SHA-256
`d9541a8fd7f834feb355446fb0116f865eacc328adaa4c8b24f4f1bb707ce0ae`.
For a second check using separately compiled rows, run
`python3 rank_three_six_module_245212.py --out /private/tmp --jobs 4`.
There is no claim here about 7 being the least prime: that is a separate
part of the order-six problem.
