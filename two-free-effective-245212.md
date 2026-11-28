# A computable height for two free odd prime powers

Fix any positive integer $h$. Let $p,q$ be distinct odd primes coprime to
$h$, and let $a,d$ be arbitrary nonnegative integers. If
$n=hp^aq^d$ satisfies [OEIS A245212](https://oeis.org/A245212), then
$n\le\mathrm{height}(h)$ with the explicit integer function below.
There is also a monotone bound depending only on an upper bound for $h$.
No Euler nonresonance hypothesis is needed. This makes the earlier
[two-extension finiteness proof](two-free-extensions-245212.md) effective.
The general bound is much too large to recommend as a search range.

Write $A=\sum_{t\mid h}t\tau(t)$, $S=\sigma(h)$, $H=2h\tau(h)$.
For positive exponents order $p<q$ and set $u=p-1$, $v=q-1$, $B=a+1$,
$C=d+1$. The normalized balance is
$A X_p X_q+S Y_p Y_q=H$, where
$Y_p=\sigma(p^a)/(Bp^a)$ and $uX_p=p-Y_p$, with the analogous
formulas at $q$. The harmonic bound yields $S<(H-A)BC$ and
$p((H-A)BC-S)\le 2HBC$. Thus, if $L=\max(4,\lfloor S/(H-A)\rfloor+1)$,
$$
              p\le P=\left\lfloor\frac{2HL}{(H-A)L-S}\right\rfloor .
$$
The executable formula uses the usual total subtraction and division on
natural numbers. A solution with positive exponents makes this denominator
positive.

## The exceptional smaller prime

Suppose $Ap=Hu$. The exact slope bounds give
$$
 q\le K(a+1),\qquad K=2P(A+S)(SP+1),
$$
and $a+1<q$ whenever $d\ge2$. Set $c=16(A+S+1)$ and suppose
$q>\max(P^4,c,H)$. For $d\ge2$, the last-power bound gives
$$
 q^d\le [2(A(a+1)+S)p^a]^2.
$$
Since $a+1<q$, the factor $2(A(a+1)+S)$ is at most $q^2$. Squaring the
inequality and using $p^4\le q$ gives $2d\le8+a$.
Consequently $d+1<q$ as well.

The cleared leading coefficient of the two local moment identities is an
integer congruent, up to sign, to $HBC(p-1)^2$ modulo $q$.
Since $B,C<q$ and $q>H$, it is nonzero. The expansion of this integer
times $p^a q^d$ consists of two linear terms and a constant; this is the
cleared identity in the earlier paper. Taking absolute values with
$M=\max(a,d)$ gives
$$
 \min(p^a,q^d)\le 2[A(M+1)q^2+q(A+S q^2)]+A+Sq^2 \le c q^3.
$$
If the smaller power is $q^d$, then $q^d<q^4$, hence $d\le3$.
In this case, or whenever $d=1$, the last-power bound in the reverse
direction gives $p^a\le[2(4A+S)]^2q^6$. In the other case the bound
$p^a\le c q^3$ already suffices.

Put $F=\max(c,[2(4A+S)]^2)$. Then
$$
    2^a\le F K^6(a+1)^6,\qquad
    a\le E_0=\max(784,64 FK^6).
$$
For the last step, if $a\ge784=16(6+1)^2$, the elementary inequality
$a^{12}\le2^a$ and $(a+1)^6\le64a^6$ yield $a^6\le64FK^6$.
This supplies a numerical cutoff even at exact resonance.

## The remaining cases and the height

Set $Z=P^4+c+H+2AP+2$. If $q\le Z$, compare $Apq$ with $Huv$.
When $Apq>Huv$, the integral excess is at least one and the normalized
balance gives $\min(a,d)+1\le 2A(p+q)/(Apq-Huv)$. When
$Apq\le Huv$, retaining the last-prime deficit gives
$d+1\le2(A+Suv)/(Aq)$. Thus one of the two powers is at most $Z^{E_1}$,
where $E_1=4AZ+2(A+SZ^2)$.

Suppose $q>Z$ and $Ap\ne Hu$. For $Ap>Hu$ the first deficit gives
$a+1\le2A/(Ap-Hu)\le2A$. For $Ap<Hu$ either
$a+1\le4Su/(Hu-Ap)\le4SP$ or $q\le1+2Ap/(Hu-Ap)$; the second option
contradicts $q>Z$. Combining these cases with the exceptional slope gives
$$
 E_2=2A+4SP+E_0,\qquad U=\max(1,Z^{E_1},P^{E_2}).
$$
At least one prime power is at most $U$. Absorbing this power into $g$
gives $g\le hU$, and the last-power bound gives
$n\le g(W(g)+\sigma(g))^2\le4g^7$. Accordingly
$\mathrm{height}(h)=4(hU)^7$. If one exponent is zero the same last-power
bound applies directly; if both are zero the inequality is immediate.

For $0<h\le R$, set $V=2R^3+1$. Then $A,S,H\le V$ and
$P\le P'=2V(V+4)$. In the formulas for $Z,K,F,E_0,E_1,E_2,U$ above
replace $A,S,H$ by $V$ and $P$ by $P'$; call the new result $U'$.
The monotone uniform envelope is $4(RU')^7$. Evaluating its formula
requires no factoring, search, or maximum over possible cofactors.

## Replaying the theorem

[TwoFreeEffectiveResearch245212.lean](TwoFreeEffectiveResearch245212.lean)
contains the complete proof. The fixed-cofactor declaration is
`OMA.TwoFreeEffective245212.original`; its bounded-cofactor counterpart
is `OMA.TwoFreeEffectiveUniform245212.original`. The `of_rank` corollary takes an odd remaining cofactor with at most two distinct prime divisors directly, and `monotone` proves the displayed envelope increases with the cofactor bound. From the pinned Formal
Conjectures checkout, with `FormalConjectures.OEIS.«245212»` built, run:

`lake env lean -j 1 -DElab.async=false /absolute/path/to/TwoFreeEffectiveResearch245212.lean`

The 163,002-byte standalone passed pinned Lean in 40.56 seconds with 1,336.4 MiB peak physical memory. Each of the four final axiom audits returns `propext, Classical.choice, Quot.sound`. Its SHA-256 is `cba26c83749ad20a2f2cd954be593a32d877f923194fe24720a4d6bc7e2b6c65`.

To regenerate the standalone file from the research workspace, run
`python3 two_free_effective_source_245212.py`.
