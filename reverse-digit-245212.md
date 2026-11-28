# Recovering an odd prime exponent in OEIS A245212

Fix an odd prime $p$ and a positive integer $m$ coprime to $p$.
There is a single rational division that gives the only exponent
$e\geq 0$ for which $mp^e$ could satisfy the equality in
[Jaroslav Křížek’s A245212 conjecture](https://oeis.org/A245212).
It applies equally to odd and even cofactors, without a bound on their
number of prime factors.

Write $W(n)=\sum_{d\mid n}d\tau(d)$, where $\tau$ counts divisors
and $\sigma$ sums them. The OEIS equality is equivalent, for positive
integers, to $W(n)+\sigma(n)=2n\tau(n)$. From the cofactor alone form

$$
A=W(m),\quad S=\sigma(m),\quad T=m\tau(m),\qquad
C=p\big((p-1)S-A\big),\quad
D=(p-1)\big(2T(p-1)-pA\big).
$$

**Theorem.** If $mp^e$ satisfies the equality, then $D\ne0$ and

$$
\frac CD=e+1+\frac{e+1}{p^{e+1}-1},
\qquad e=\left\lfloor C/D\right\rfloor-1.
$$

Thus if $D=0$ or the floor is less than one, no exponent works.
Otherwise test the original equality at the single candidate. The
floor alone is necessary, not sufficient. This does not rule out
solutions as $m$ and $p$ vary.

**Proof.** Put $t=e+1$, $g=1+p+\cdots+p^e$, and
$w=1+2p+\cdots+(e+1)p^e$. Multiplicativity gives
$Aw+Sg=2Ttp^e$. Since $(p-1)w+g=ptp^e$, eliminating $w$
gives

$$
\big((p-1)S-A\big)g=t p^e\big(2T(p-1)-pA\big).
$$

Substituting $g=(p^t-1)/(p-1)$ yields
$C(p^t-1)=Dtp^t$. The earlier [nonzero cofactor-difference lemma](prime-power-height-245212.md)
gives $(p-1)S\ne A$ at a solution with $p$ odd, so $C\ne0$;
the displayed identity then gives $D\ne0$. Division gives the exact
error $t/(p^t-1)$, strictly between zero and one for $p\ge3$ and
$t\ge1$. This proves the floor formula even if $C,D$ are negative.

**Prior work and verification.** [Anmol Sahu’s reduction #5390](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5390)
gives an explicit exponent of **two** for a prescribed odd cofactor.
The preceding result here, `OMA.Abundance245212.unique_exponent`,
already shows uniqueness for odd primes. The present formula gives
the exponent itself and its exact rational error. For separate density
and totient restrictions see [formal-conjectures issue #8382](https://github.com/google-deepmind/formal-conjectures/issues/8382).

The [standalone Lean source](ReverseDigitResearch245212.lean) imports only
`FormalConjectures.OEIS.«245212»`. Its main theorem is
`OMA.ReverseDigit245212.recover`. From the [pinned Formal Conjectures checkout](https://github.com/google-deepmind/formal-conjectures/tree/9097e2f90e66d2f6244209cb1c07f7120d17ec53),
run `lake env lean /path/to/ReverseDigitResearch245212.lean`. The file
prints the proof’s three axioms: propositional extensionality, classical
choice and quotient soundness.
