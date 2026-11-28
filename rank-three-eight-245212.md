# Eight times an odd number with three distinct prime divisors

If $n>0$, $v_2(n)=3$, and exactly three distinct odd primes divide $n$,
then $a(n)\ne\sigma(n)$ for [OEIS A245212](https://oeis.org/A245212).
All three odd exponents and all three primes are unrestricted.

The [standalone Lean proof](RankThreeEightDyadicResearch245212.lean) includes the
two equivalent entry points:

- `OMA.RankThreeEightDyadic245212.odd_part`: the input is $8m$, with
  $m$ odd and supported on three distinct primes.
- `OMA.RankThreeEightDyadic245212.original`: the input is the original
  positive integer $n$, with the two factorization hypotheses above.

For $W(n)=\sum_{d\mid n}d\tau(d)$, the equation being excluded is
$W(n)+\sigma(n)=2n\tau(n)$. For least odd prime 3 the proof reuses the
previously checked cofactor-24 and cofactor-72 tables. For least prime
at least 5, the normalized divisor sums first restrict the ordered
odd support $p<q<r$ to 58 fixed supports or six pairs $(5,q)$
with unrestricted $r$. The ordinary Euler bound and the monotonicity
of the normalized local moments resolve five of those pairs by finite
integer interval checks.

**The exceptional pair (5,23).** Here
$49\cdot5\cdot23-64\cdot4\cdot22=3$.
Put $x=a+1,y=b+1,z=c+1$ and $P=5^a,Q=23^b,R=r^c$.
The finite geometric-sum identities give an integral defect

$$
D=495616xyzR-CW(R)-151800\sigma(R),
\qquad C=5635(4x-1)(22y-1).
$$

For $x\ge8,y\ge2$, $D\ge1$. Indeed, after multiplication by $PQ$,
the error in the weighted sums dominates the error in the ordinary
sums; the proof keeps both exactly. Rounding the last prime-power sum
gives a second integer $J$ with
$(r-1)^2D=JR+151800(r-1)-C$.
If $J=0$, then $151800(r-1)>C$ and $r\mid495616xyz$.
The first condition forces $r>2(x+y)$, whereas
$z\le2(x+y)$ and $r>23$, contradicting divisibility.
Eliminating $R$ now gives, with $H=100000z(x+y)$,

$$
\min(P,Q)\le H((r-1)^2+151800(r-1)+C).
$$

A separate integer estimate gives either $\min(P,Q)\le2H$ or
$r\le2(Cz+151800)+1$. For $r\le2{,}000{,}000$ the previous height
bound controls $x,y,z$; for larger $r$ the one-prime Euler bounds
give $a\ge100,b\ge64,x,y\le200000,z\le1000000$. Substitution excludes
every case with $a>80,b>40$. The remaining two strips are checked
directly with exact integer arithmetic: each fixed first exponent
leaves only finite intervals of possibilities for the terminal prime
or exponent. No experimental cutoff is used.

## Replay

Use the Formal Conjectures checkout at
`9097e2f90e66d2f6244209cb1c07f7120d17ec53`, with its pinned Lean
and mathlib dependencies built. From that checkout run:

```sh
lake build FormalConjectures.OEIS.«245212»
lake env lean -j 1 -DElab.async=false /absolute/path/to/RankThreeEightDyadicResearch245212.lean
```

The standalone source contains every new proof and finite check. It
imports only the original conjecture module. The final audit prints
`[propext, Classical.choice, Quot.sound]`.
