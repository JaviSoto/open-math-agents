# Lean verification of the sparse-path inverse theorem

Both claims of [the sparse-path theorem](sparse-doubling-paths.md) now have proofs in Lean on Fonollosa's original finite-set predicate. In [SparsePaths.lean](SparsePaths.lean), \(\mathrm{Covered}(A,h)\) means that one translation of \(A\) is the disjoint union of \(h\) doubling progressions. Empty progressions are permitted. With the three numerical assumptions in the paper, the checked results are:

- \(\mathrm{big\_cycle}\): if \(N<2^n\), there exists a common translation containing a doubling cycle of length at least \(n/2\).
- \(\mathrm{lower}\): \(N\ge 2^n-2^{\lfloor\log_2 n\rfloor}\).
- \(\mathrm{extremal}\): at equality, for \(n\ge4\), there are a unit \(u\) modulo \(N\) and a translation \(t\) for which \(A=\{2^j u-t:0\le j<n\}\).

The final file chooses a maximal-length row using [PathSplice.lean](PathSplice.lean). [PathEndpoint.lean](PathEndpoint.lean) turns a box representation into a subset, rules out zero by [PathPeriod.lean](PathPeriod.lean), and obtains the endpoint representation from [PathHoles.lean](PathHoles.lean), [PathShift.lean](PathShift.lean), and [PathSuccessor.lean](PathSuccessor.lean). [PathCycle.lean](PathCycle.lean) then applies the coding bound to all disjoint rows, including the transient prefix of the returning row. The three main statements use only the standard Lean axioms of propositional extensionality, classical choice, and quotient soundness.
