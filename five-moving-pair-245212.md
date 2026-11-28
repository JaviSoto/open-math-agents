# No solution on the primes 2, 5 and one freely varying larger prime

For every prime $q>5$ and **all** $k\ge0$, $e,f\ge1$, the A245212 equality fails at $2^k5^eq^f$. The [standalone Lean proof](FiveMovingPairResearch245212.lean) begins with the original OEIS declaration and ends with `OMA.FiveMovingPair245212.no_five`. Run `lake env lean /path/to/FiveMovingPairResearch245212.lean` from the project's pinned formal-conjectures checkout. Its axiom audit lists only `propext`, `Classical.choice` and `Quot.sound`.

The [dyadic bound](two-odd-finiteness-245212.md) gives $k<10$. For $k\le2$ the dyadic Euler inequality and prior three-prime exclusions suffice. At $k=3$ the Euler inequality forces $q\le23$. At each of $q=7,11,13,17,19,23$, at least one of $e,f$ is at most $2,5,8,17,29,553$, respectively: with both exponents larger, the product of weighted factors alone exceeds two. Once one exponent is fixed, the [reverse digit](reverse-digit-245212.md) determines the other. The kernel evaluates the exact moment balance on the survivors.

For $k=4,5,6,7,8,9$, the smaller prime's own weighted factor gives $e\le31,4,2,1,1,1$, respectively, regardless of $q,f$. Fix $a=2^k5^e$. The odd last prime satisfies $q^f\le|W(a)-(q-1)\sigma(a)|\le q(W(a)+\sigma(a))$, so $f\le 1+\lfloor\log_2(W(a)+\sigma(a))\rfloor$. For each such exponent the leading digit determines $q$, whether $q$ is small or arbitrarily large. The computed prime-divisibility and moment checks rule out every candidate.

As an independent check, the rectangular interval solver `mixed_three_245212.py` encloses both local moments using rational endpoints and subdivides in $e,f,q$. Fix each dyadic exponent in turn with `runs(5,(k,k))` for $1\le k\le9$. For $k=3,4$, that separate method needs 6,495 and 52,501 boxes. The Lean proof uses the smaller cofactor checks above.

Combined with the [earlier $3,q$ theorem](divisor-balance-245212.md), a counterexample with exactly two distinct odd primes must have both odd primes at least seven. This leaves infinitely many supports, and the unrestricted conjecture remains open.
