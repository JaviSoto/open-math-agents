# A multiple of three cannot be a counterexample with exactly three odd primes

For every positive integer $n$ divisible by 3 with exactly three distinct odd
prime divisors, the [A245212 equality](https://oeis.org/A245212) fails. The
power of two, the exponents of the odd primes, and the two odd primes other
than 3 are all unrestricted. The [final Lean statement](RankThreeMultipleThree245212.lean)
uses the prime factorization of $n$ itself.

Write $n=2^k3^a p^b q^d$ with $5\le p<q$ and $a,b,d>0$. The earlier odd
theorem eliminates $k=0$, and the [twice-an-odd-number theorem](three-odd-twice-245212.md)
eliminates $k=1$. At $k=2$, the weighted divisor sum leaves seven possible
exponents of 3. The [four-times proof](RankThreeFourSmall_replay_245212.md)
eliminates all seven with bounds on the two remaining primes and their exponents.

For $k\ge3$, there is a useful simplification **even if there are many primes
besides 2 and 3**. Write $W(t)=\sum_{d\mid t}d\tau(d)$ and
$X_s(e)=W(s^e)/[(e+1)s^e]$. For any positive coprime remainder $v$, a solution at
$2^k3^a v$ would require $X_2(k)X_3(a)<2$. In fact each factor is increasing
in its exponent. The products at $(k,a)=(6,1),(3,3),(4,2)$ are already at
least two. This leaves just four pairs:

| $k$ | $a$ | Fixed cofactor $2^k3^a$ | Upper bound for the next prime when two remain |
|---:|---:|---:|---:|
| 3 | 1 | 24 | 29 |
| 3 | 2 | 72 | 260 |
| 4 | 1 | 48 | 73 |
| 5 | 1 | 96 | 698 |

For these cofactors the two-free-prime decision procedure eliminates every
case, including those where a simple Euler estimate puts no upper bound on
the last prime. The exact integer replay checked 2,319 finite prime pairs and
1,618 pairs of exponents in the large-prime branch after the affine cuts.
The Lean proof independently checks the complete ranges in 45 intervals.

**Reproduce:** extract the [complete source archive](rank-three-multiple-three-245212.tar.gz)
and run `lake env python3 /path/to/RankThreeMultipleThree245212/lean_source_bundle_245212.py --workers 4`
from the project's built formal-conjectures checkout at `9097e2f90e66d2f6244209cb1c07f7120d17ec53`.
Its 293 modules include all four regimes. SHA-256:
`4e49d11dae0376f1082eb2f9143525932047ec7331317f32480f48914147a120`.
The smaller [95-module archive for $k\ge3$](rank-three-three-high-245212.tar.gz)
also replays independently. Both joined theorems report only `propext`,
`Classical.choice`, and `Quot.sound`.
