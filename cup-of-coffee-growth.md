# A near-linear bound for prime debuts in the cup-of-coffee sequence

Write \(a_1=1,a_2=2,\ldots\) for Rémy Sigrist’s [A280864](https://oeis.org/A280864). For every \(t\ge3\), uniformly,
\[
  \max\{p:p\text{ prime},\ p\mid a_t\}=O\big(t\log\log(t+10)\big),
  \qquad a_t=O\big(t^2\log\log(t+10)\big).
\]
The first bound is within a factor of order \(\log\log t\) of Sloane’s conjectured bound \(p\le t\). The sequence need not be assumed to be a permutation, and this does not show that type-II primes are infinite.

At time \(t\) let \(R_t\) be the product of those primes dividing \(a_{t-1}\) but not \(a_{t-2}\); let \(F_t\) be the product of the primes dividing both. The greedy rule chooses \(a_t=R_t L_t\), with \(L_t\) the least multiplier prime to \(F_t\) for which \(R_tL_t\) has not yet been used. Since a prime of \(R_{t+1}\) divides \(a_t\) but not \(a_{t-1}\), it divides \(L_t\). These primes are distinct, so \(R_{t+1}\mid L_t\). Also \(F_{t+1}=R_t\): required primes continue and forbidden primes leave. For formulas at the start take \(R_2=1\) and \(F_2=1\).

Let \(P_t\) be the least prime dividing none of the first \(t-1\) terms. Then \(R_tP_t\) is eligible and unused, hence \(L_t\le P_t\). Any new prime dividing \(a_t\) divides \(L_t\) and is at least \(P_t\). If a prime makes its debut, it must therefore equal \(P_t=L_t\). This familiar debut argument also gives an unconditional preliminary size estimate: at most one prime is introduced per term, so \(P_t\) is at most the \(t\)-th prime. In particular \(P_t=O(t\log(t+2))\), and \(F_t,R_t\le O(t\log(t+2))\) since \(F_t=R_{t-1}\mid L_{t-2}\). For the few starting indices these bounds hold directly.

**Sieve the multipliers.** Put \(d(F)=2^{\omega(F)}\), \(V(F)=F/\varphi(F)\). Inclusion–exclusion gives
\[
 \#\{1\le j\le x:(j,F)=1\} = x/V(F)+O(d(F)),
\]
with error at most \(d(F)\). Among the smaller multipliers \(j<L_t\) prime to \(F_t\), the distinct values \(R_tj\) have all occurred before time \(t\). Therefore
\[
 L_t\le 1+V(F_t)\big(t-1+d(F_t)\big).
\]
The error is uniformly \(o(t)\): for instance \(2^{\omega(F)}\le 2\sqrt F\) since each distinct prime at least 5 supplies a factor \(\sqrt p>2\). The standard extremal totient estimate \(F/\varphi(F)=O(\log\log(F+10))\) now bounds each multiplier by \(O(t\log\log(t+10))\). This bounds every debut prime. Any other prime factor made its debut at an earlier index.

**Why the term bound has only one logarithm.** We have \(a_t=R_t L_t\le L_{t-1}L_t\). The forbidden products at neighboring steps are coprime: \(F_{t+1}=R_t\), and \(R_t,F_t\) have disjoint prime support. Thus \(V(F_{t-1})V(F_t)=V(F_{t-1}F_t)\), still \(O(\log\log(t+10))\) by the preliminary size estimates. Multiplying the two sieve bounds proves the second assertion.

This addresses the size question about the least missing compatible multiple in [Sloane’s notes, Remark 1.6](https://oeis.org/A280864/a280864_5.txt), on the states actually visited by the sequence. It does not provide his proposed coefficient 1. The proof only uses the greedy rule and standard elementary estimates for primes and Euler’s totient.

**Verification and references.** [CoffeeGrowth.lean](CoffeeGrowth.lean) checks the exact greedy inequalities, the transition of the forbidden primes, and the divisibility of the next required product, against the Formal Conjectures definition. The two asymptotic estimates follow by the preceding written sieve argument, using the prime and totient bounds in [Rosser and Schoenfeld (1962)](https://doi.org/10.1215/ijm/1255631807). The [independent generator](coffee_blocks.cpp) checks the prime-run rule at each step and accepts the [official 100,000-term b-file](https://oeis.org/A280864/b280864.txt) as optional reference input.

Through 50,000,000 terms, the generator matched all 100,000 reference rows and found 715,865 type-II debuts, each at twice the prime. It found no squarefree composite ending a run of overlapping prime factors, and no missing maximal proper divisor of a squarefree term other than the new prime at a type-II debut. The last term was 50,324,704; the next previously unseen prime was 25,162,373. These are finite checks of the patterns recorded in [A280864](https://oeis.org/A280864), not part of the growth proof.
