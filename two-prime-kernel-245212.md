# Lean certificate for the high-exponent part of A245212 with two odd primes

Let $p<q$ be primes with $p\ge13$, and let $a,d\ge5$. For **every**
nonnegative integer $k$, the OEIS divisor equation fails at
$2^kp^aq^d$. There is no upper bound on the primes or exponents. In Lean
the statement is `OMA.RankTwoJoined245212.original`. The
[written proof for all integers with at most two odd prime factors](two-odd-nonexistence-245212.md)
also covers smaller primes and exponents; those additional cases are not
hypotheses this certificate discharges.

The analytic proof turns any proposed solution into one of 54 arithmetic
checks: one for each possible smaller exponent from 5 through 31 and
each ordering of the primes. Each check is split into a tree of small
regions. Lean verifies every split and exclusion, and the final theorem
imports both the analytic proof and every tree root. The generator is
not trusted to certify a region: changing a split or a cutoff still
requires the kernel to verify the corresponding claim.

## Reproduce

Use the LeftToSolve formal-conjectures checkout at
`9097e2f90e66d2f6244209cb1c07f7120d17ec53`, with its pinned Lean toolchain
and compiled dependencies. Keep `RankTwoOriginalCoverResearch245212.lean`,
`RankTwoExport245212.lean`, `RankTwoJoined245212.lean`, and
`rank_two_numeric_245212.py` together in the downloaded research checkout.
From the formal-conjectures checkout run:

```sh
lake env python3 /path/to/research/rank_two_numeric_245212.py --portable 6-32 --workers 8
```

Use fewer workers on smaller machines. Each worker checks one file at a
time with Lean's asynchronous elaboration disabled to limit peak memory.
The command builds the analytic proof and all generated modules in a new
temporary directory; no prebuilt research modules are needed. Successful
completion ends with the axiom report for the original theorem:

```text
'OMA.RankTwoJoined245212.original' depends on axioms: [propext, Classical.choice, Quot.sound]
```
