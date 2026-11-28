# Four times three odd prime powers, beginning with 3

For primes $5\le p<q$ and positive $a,b,d$, the integer
$4\cdot 3^a p^bq^d$ cannot satisfy OEIS A245212. The argument below
uses a finite exact-integer computation. In conjunction with
**RankThreeFourLargeResearch245212.lean**, this excludes four times
any product of powers of exactly three distinct odd primes.

Let $W(n)=\sum_{t\mid n}t\tau(t)$, and write $X(n)=W(n)/(n\tau(n))$,
$Y(n)=\sigma(n)/(n\tau(n))$. The equation is $X(n)+Y(n)=2$; both
factors are multiplicative and $X(s^e)\ge1$. At $4$, the normalized
weighted factor is $17/12$. The one-prime weighted factor increases
with its exponent, and $17X(3^8)\ge24$. Consequently $a\le7$.

Fix $h=4\cdot3^a$, $A=W(h)$, $S=\sigma(h)$, $H=2h\tau(h)$ and
$D=H-A$. All seven $D$ are positive. Put $B=b+1$, $C=d+1$,
$u=p-1$, $v=q-1$. Write $y=Y(p^b)$ and $z=Y(q^d)$.
The local identities $uX(p^b)=p-y$, $vX(q^d)=q-z$ give

$$Huv=A(p-y)(q-z)+Suvyz,\qquad 0<By<2,\quad 0<Cz<2.$$

The count-sensitive cofactor reciprocal estimate
**CofactorHarmonic245212.count_sensitive**, applied to the two new primes,
yields $0<D BC-S$ and $p(D BC-S)\le2H BC$.
Putting $L=\max(4,\lfloor S/D\rfloor+1)$ gives $BC\ge L$ and
$p\le\lfloor2HL/(DL-S)\rfloor$. If $pD>2H$, retain the sharper
$BC\le\lfloor pS/(pD-2H)\rfloor$. The seven first-prime ceilings are
16, 27, 48, 92, 259, 2,315 and 7,972. The kernel proof below improves the last two to 678 and 964.

### Remaining finite cases

Put $G=Hu-Ap$. None of the candidate primes gives $G=0$, an explicit
check at each $a$. If $G<0$, the strict inequality $AX(p^b)<H$ implies
$B\le 2A/(-G)$. Fix $b$. The existing final-prime digit determines at
most one $q$ at each $d$, and **PairExtension245212.last_log_base**
bounds $d$. This handles this whole branch.

If $G>0$, the displayed moment identity implies
$Gv\le Ap+Suyv$. Thus either $B\le 4Su/G$ or
$q\le Q=1+\lfloor2Ap/G\rfloor$. In the range $q>Q$, also
$Apq\le Huv$. Expanding the same identity and canceling the positive
$y$ gives $Aq\le(A+Suv)z$, hence $C\le2(A+Su)/A$.
There are now finite ranges for $b,d$, with $q>Q$ still unrestricted.

For a finite pair $p<q\le Q$ with $Apq\le Huv$, the sharper
$C\le2(A+Suv)/(Aq)$ suffices. For $Apq>Huv$ the established
**CofactorEulerPair245212.short_pair** and
**CofactorPairRounding245212.shortened** bounds give
$E\ge\min(b,d)$. The new refinement is as follows. Put
$j=\lfloor\log_p q\rfloor+1$ and
$M=jE+\lfloor\log_p(2(A(E+1)+S))\rfloor+2$. Both exponents are at
most $M$: for the small exponent $i\le E$ at a prime $s$, the cofactor
moment sum is at most $2(A(E+1)+S)s^i$, to which the final-prime
logarithm bound applies. When $q\nmid H$ and $M+1<q$, the simultaneous
rounded integer from **CofactorPairPole245212.tails** is nonzero:
modulo $q$ it equals $\pm HBC(p-1)^2$. Comparing its absolute value
times $p^b q^d$ to the two linear tails and constant term gives

$$p^{\min(b,d)}\le
  2\bigl(A(M+1)q^2+q(A+Sq^2)\bigr)+A+Sq^2.$$

The largest finite-pair smaller-exponent ceiling after these steps is
83. For each shorter exponent and its possible orientation, the signed
reverse-digit formula determines the other exponent. A zero denominator
cannot correspond to a solution. Before constructing the last power,
the program checks the cofactor divisibility and the magnitude bound
from **PrimePowerDiv245212.cofactor_bound**.

### Checking the unrestricted last prime without large powers

For fixed $h,p,b,d$, set $P=p^b$. The last-prime digit is
$q=\lceil N/D'\rceil$ with $D'>0$. After multiplying both $N$ and $D'$
by $u^2$ write them as $N_0P+N_1$ and $D_0P+D_1$, where

$$
\begin{aligned}
D_0&=CBuG+p(CA-Su), &D_1&=Su-CA,\\
N_0&=p(dABu+Su-dA), &N_1&=dA-Su .
\end{aligned}
$$

These are the ordinary geometric-sum formulas at $p^b$. For
$R=\max(p,Q)+1$, the condition $q\ge R$ implies
$(R-1)(D_0P+D_1)<N_0P+N_1$. As soon as
$P>\max(|D_1|,|N_1-(R-1)D_1|)$, a negative integral leading
coefficient could not be corrected by its remainder. Therefore
$D_0\ge0$ and $N_0-(R-1)D_0\ge0$. Both inequalities are linear in $B$.
The first has positive slope; the second has negative slope because
$(R-1)CG>p d A$. Their intersection is an explicit integral interval.
The short initial exponents below this threshold are checked separately.
The program's **--band-literal** mode takes this interval and checks the
original digit with exact powers at every remaining exponent pair.
Primality of the deduced $q$ is unnecessary: enforcing its divisibility
and the original equality even for composite digits yields no examples.

### Replay and current Lean checks

Run **python3 RankThreeFourSmall_replay_245212.py --band-literal** in the
research workspace. It imports **RankThreeFourSmall_profile_245212.py**
and the integer moment formulas from **rank_three_middle_blocks_245212.py**.
On the hardest row ($a=7$) it checks 1,004 possible first primes, 47,782
finite prime pairs, and 33,718 far-range exponent pairs. The result was
zero equalities. A second mode, run without the flag, traverses all
1,805,403 far-range exponent pairs at $a=7$ using a leading-digit
ratio and a prime-power congruence. It returns the same result. Each full
run took under three seconds locally.

The Lean proof uses shorter independent certificates for the last rows.
For $a=6$, the positive integer product $BC$ exceeds 4 and cannot be 5,
so $BC\ge6$ and $p\le678$. For $a=7$, $BC\ge15$. In the exact dyadic
balance, the surplus from $3^7$ is 1, so
$v_2(b+2)+v_2(d+2)\ge4$, with equality when both $b,d$ are even.
Checking $15\le (b+1)(d+1)<30$ leaves no possibilities. Hence $BC\ge30$,
and the same harmonic bound gives $p\le964$.

On a dyadic interval $l\le q\le u$ below $Q$, take the worst endpoint
in the degree and defect estimates above. This bounds $b$ for the full
interval, so one check for fixed $b$ can cover many different $q$.
Above $Q$, if $D_0\ne0$ and $P>2|D_1|$, then $D_0\ge1$ and the digit
inequality gives $q\le2(|N_0|+|N_1|)+2$. The right-hand side is bounded
using the known upper bound on $b$, without computing $p^b$. Applying
the last-power bound with $p,q$ interchanged now reduces $b$ to a
logarithmic bound. The single possible zero $D_0=0$ at each $d$ and the
small powers $P\le2|D_1|$ are handled separately. For $a=7,p=257$,
this reduced a finite-prime interval with 392,061 possible positions
(33,203 primes) to a first-exponent table ending at 95. The complete unrestricted
$p=257$ certificate took 5.37 seconds locally, including loading Lean.

**RankThreeFourSmallFullResearch245212.lean** contains the joined proof:
`OMA.RankThreeFourSmallFull245212.no_four_three` proves the original
OEIS inequality for $4p^a q^b r^c$ for every ordered triple of distinct
odd primes and every positive exponent triple. It imports only
`FormalConjectures.OEIS.«245212»`. To regenerate the source from the
research workspace, run `python3 RankThreeFourSmall_source_245212.py`.
For a direct replay in that pinned Formal Conjectures checkout with
the named OEIS import built, run:

```sh
lake env lean -j 1 -DElab.async=false /absolute/path/to/RankThreeFourSmallFullResearch245212.lean
```

The standalone replay took 259.19 seconds and peaked at 2,361.7 MiB of physical memory.
The final axiom audit reports `propext, Classical.choice, Quot.sound`.
The 474,121-byte source has SHA-256
`cfc8d21210dadb57289a13f6cbad6e4bfad70dda7737f0389cb37086f77de339`.
The computational proof uses ordinary Lean kernel reduction. The Python
replays described above can be run separately without Lean.
