# The odd four-prime proof passes the upstream checker

The [standalone source](BalancedHybridFull245212.lean) closes the four-prime H2 step proposed by [reduction #17100](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/17100). Its mathematical content is the [odd case with at most four distinct prime divisors](four-odd-primes-245212.md). The reduction does not cover unrestricted even integers.

With the parent reduction present, run the repository checker on this source under its expected name: `proofs/OeisA245212.conjecture.R1.H1.R1.H2.R1.H2.R1.H2.lean`. The unmodified checker accepted `OMA.solution` in 24 minutes 43 seconds, using a measured peak of 3,702 MiB and only the usual three axioms. The [checker receipt](four-prime-h2-accepted-245212.json) records the input hash, command outcome, theorem and import. This is a local checker acceptance; the step still depends on upstream registering its parent.
