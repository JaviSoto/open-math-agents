# Three odd prime factors when the dyadic exponent is one

Consider the divisor equation [OEIS A245212](https://oeis.org/A245212) for
`n = 2 p^a q^b r^c`, where `p<q<r` are odd primes and `a,b,c≥1`.
There is no solution if **p≥5**, or if **p=3 and q≥17**. This leaves the
four choices `(p,q)=(3,5),(3,7),(3,11),(3,13)` outside this argument.

### Euler bounds and integer rounding

Write `W(m)=Σ_{d|m} d τ(d)`. The equation is `W(n)+σ(n)=2 n τ(n)`.
For a prime power `u^e`, put `Y=σ(u^e)/((e+1)u^e)` and
`X=W(u^e)/((e+1)u^e)=1+(1−Y)/(u−1)`. The equation becomes

```
5 Xp Xq Xr + 3 Yp Yq Yr = 8.
```

The full cap bounds the left side at a solution by
`5 pqr/((p−1)(q−1)(r−1))`. One can also keep the first factor exact:
`8 ≤ 5 Xp q r/((q−1)(r−1))`, and likewise after permutation. These are
necessary inequalities, even though dropping the positive product of the
three `Y` terms in the equation itself would give the opposite inequality.
The proof uses the two-remaining-factor bound
`Xq Xr ≤ Yq Yr+(1−Yq Yr) qr/((q−1)(r−1))`, together with
`5 Xp+3 Yp≤8` and `Yq Yr<1`.

For `p≥5`, the full cap leaves only `(5,7,11)`, and the one-factor bounds
give `a≥60,b≥45,c≥30`. The four-factor rounding height theorem still
applies to a dyadic factor when its power is bounded: a large selected
singleton is then odd, which is the only place the singleton proof needs
oddness. The height ceiling for largest base 11 is 2,864. Rounding all
three odd factors at once now gives a contradiction: the rationally rounded
score is strictly smaller than the true score, but its integral numerator
differs from that of the integer target by less than one after passage to a
common denominator.

### The 70 remaining supports with q≥17

For `p=3`, the cap reads `(q−16)r≤16(q−1)`; together with `r>q≥17`
it gives `q≤31`. Enumerating the primes in those bounds gives 70 ordered
supports. For each, let `B=r`, let `H` be the four-factor exponent
ceiling, and set `M=2·64 B^9(H+1)^4`. The small-exponent extraction
uses two applications of the integer rounding estimate:

1. At least one base `u` has exponent `e≤floor(log_u M)`. To see why
   simultaneous rounding of the three large factors is strict, put
   `T_v=floor(log_v M)`. For every permutation `(u,v,w)` in every
   support, the exact test `4(u−1)<(T_v+2)(T_w+2)` holds. The rounded
   `Y` at each other odd prime is at most `2/(exponent+1)`.
2. Fix this `u^e`. At least one of the remaining two bases `v,w` has
   exponent at most
   `max(floor(log_v(M u^e)), floor(4(w−1)/(e+1)))`, using the analogous
   expression with `v,w` exchanged for the other choice. If both exceed
   those bounds, the two-factor rounding is again strict and its common
   denominator error is smaller than one.

Thus only two exponents are iterated. The third is recovered by the signed
reverse-digit identity. In detail, for the remaining prime `w` and
cofactor `h`, let `A=W(h), S=σ(h), T=hτ(h)`,
`C=w((w−1)S−A)`, and `D=(w−1)(2T(w−1)−wA)`. At equality `D≠0`, and
`floor(C/D)=g+1` for terminal exponent `g`. The routine first uses
`w | A+S`, checks the exponent ceiling and then tests the exact integer
equation at the recovered exponent. The setup uses the earlier signed
reverse-digit and four-factor rounding lemmas for A245212.

### Replay

- `RankThreeOneResearch245212.lean` is the standalone proof for least
  prime at least five. `python3 rank_three_one_source_245212.py` rebuilds it.
- `RankThreeLargeMiddleResearch245212.lean` includes both sectors and the
  70 numerical support certificates. Regenerate it with
  `python3 rank_three_middle_source_245212.py --standalone --output RankThreeLargeMiddleResearch245212.lean`.
  Its only import is `FormalConjectures.OEIS.«245212»`. Check it in the
  pinned Formal Conjectures checkout with `lake env lean -j 1 -DElab.async=false /absolute/path/to/RankThreeLargeMiddleResearch245212.lean`.
- `python3 rank_three_large_middle_245212.py` is a separate executable
  replay using Python integers. After also applying the two-fixed-factor
  Euler test it visits 182,798 ordered exponent pairs, of which 44,669
  pass the first terminal-prime modulus. Different orders may cover the
  same powers. The Lean verifier does not need that last Euler shortcut,
  so its ordered-pair count is larger. The shortcut is valid here because
  the limiting product for any two odd bases is at most
  `(3/2)(17/16)<8/5`. After two factors are fixed, their partial score
  is below 8: interpolate the second factor between its `Y=0` and
  `Y=1` limits, using the one-factor bound for the latter endpoint.
  Interpolating the final factor can reach 8 only if its `Y=0` endpoint
  reaches 8.
