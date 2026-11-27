# A constant-factor lower bound for Fonollosa’s minimum modulus

For \(n\ge3\), let \(N\) admit \(n\) distinct residues such that the multiset containing each residue once is the only multiset of length \(n\) with its sum. We prove
\[
N\ \ge\ \frac98\,2^{n-1}.
\tag{1}
\]
Thus every such cyclic group needs at least \(12.5\%\) more residues than the \(2^{n-1}\) needed by an unrestricted finite abelian group. [Théo Nicolas Sitjar’s November 2026 bound](https://doi.org/10.5281/zenodo.24228247) gives a surplus of order \(2^n/n\) for large \(n\), and is stronger than (1) for some small \(n\). The conjectured minimum is \(2^n-2^{\lfloor\log_2 n\rfloor}\); (1) does not reach it.

## The doubled translate

Translate the labels so one is zero, and write the \(d=n-1\) others as \(g_1,\ldots,g_d\). Write \(\sigma(F)=\sum_{j\in F}g_j\). The following consequence of validity will be used several times: if a squarefree submultiset \(T\) has the same sum as a multiset \(Y\) drawn from the nonzero labels and \(|Y|\le |T|+1\), then \(Y=T\) as multisets. Indeed, replace \(T\) in the prescribed multiset with \(Y\), and take exactly \(1+|T|-|Y|\) copies of the zero label. In particular all \(2^d\) subset sums are distinct: in a collision, replace the larger set with the smaller. This is the box argument of [Michael Inal](https://doi.org/10.17605/OSF.IO/C58Q9).

Fix a label \(g_b\) such that \(z=2g_b\ne0\). Such a label exists: otherwise all subset sums would belong to the two-torsion subgroup of a cyclic group, which has at most two elements, while \(2^d\ge4\). Set \(S=[d]\setminus\{b\}\), \(r=|S|=n-2\), \(X=2^S\), and \(s=|X|=2^r\). Following the doubled-label count in [Sitjar, §3.2](https://doi.org/10.5281/zenodo.24228247), consider \(z+\sigma(F)\) for \(F\subseteq S\). These values are distinct.

If \(z+\sigma(F)=\sigma(T)\) for any \(T\subseteq[d]\), then \(b\notin T\): otherwise cancellation gives \(\sigma(F\cup\{b\})=\sigma(T\setminus\{b\})\), an impossible subset-sum collision. Further, \(|T|\le |F|\): if \(|T|\ge|F|+1\), replace \(T\) with \(F\) and two copies of \(b\), contradicting the squarefree replacement rule.

Let \(H\subseteq X\) consist of the \(F\) whose translates hit a subset sum. On \(H\) define \(f(F)=T\). It is an injection into \(X\) satisfying \(|f(F)|\le|F|\). For each of the other \(h=s-|H|\) choices the translate is outside the entire subset-sum box. Hence
\[
N\ge 2^d+h.
\tag{2}
\]

## At most half of the cube can stay on its layer

For \(F\in H\) with \(|F|=|f(F)|\), set \(U=F\setminus f(F)\) and \(V=f(F)\setminus F\). Then \(U,V\) are disjoint and nonempty, \(|U|=|V|\), and \(\sigma(V)-\sigma(U)=z\). Fix two different reduced pairs \((U,V)\), \((U',V')\). They satisfy
\[
\sigma(U)+\sigma(V')=\sigma(U')+\sigma(V).
\]
The multisets on both sides have the same size, since \(|U|=|V|\) and \(|U'|=|V'|\). If \(U\cap V'=\varnothing\), the left side is squarefree. The replacement rule forces equality of the multisets, hence \(\mathbf1_U-\mathbf1_V=\mathbf1_{U'}-\mathbf1_{V'}\); the disjoint positive and negative supports give identical reduced pairs. This contradiction proves \(U\cap V'\ne\varnothing\), and symmetrically \(U'\cap V\ne\varnothing\).

Each pair describes a subcube: \(U\subseteq F\subseteq S\setminus V\). Two of these subcubes have Hamming distance at least two, because they force opposite choices on one coordinate in each of the two cross-intersections just proved. Those coordinates are distinct since \(U\cap V=\varnothing\).

**Half-cube lemma.** Pairwise nonadjacent proper faces of a Boolean cube occupy at most half its vertices. To see this, induct on the dimension. If a face fixes just one coordinate, every cube vertex is within one step of that face, so no other face can occur. Otherwise every face fixes at least two coordinates. Cut the cube into the two slices on any coordinate. Every surviving face remains proper in its slice, and no adjacency between distinct faces is introduced. Apply the induction hypothesis to each slice. The dimension-zero case is immediate. The numerical bound also follows from the classical [Bollobás set-pairs inequality](https://web.vu.lt/mif/s.jukna/EC_Book_2nd/Bollobas.pdf).

Every \(F\) for which \(f(F)\) stays on its layer lies in one of these subcubes. The lemma therefore bounds the number of such ties by \(s/2\).

## Counting the gaps

Write \(C=\{\sigma(F):F\subseteq S\}\) and \(g=g_b\). The sets \(C\) and \(C+g\) are disjoint by squarefree injectivity. Walk round every coset of \(\langle g\rangle\) that meets \(C\), always taking steps \(+g\). For each \(F\) let \(\ell(F)\) be the positive number of steps until the next point \(\sigma(T)\in C\). We have \(\ell(F)\ge2\). Even on a coset with a single point of \(C\), \(T\) is defined: return to that point after a full circuit. The map \(F\mapsto T\) permutes the cube and the gap lengths sum to at most \(N\), the total size of the cosets.

The multiset \(F\) together with \(\ell(F)\) copies of \(b\) sums to \(\sigma(T)\). It differs from \(T\). By the replacement rule it has length at least \(|T|+2\). Thus the nonnegative integer
\[
e(F)=\ell(F)-2+|F|-|T|
\]
sums over \(F\) to \(\sum_F\ell(F)-2s\le L\), where \(L=N-2s\). A gap of length two either is a tie or has \(e(F)\ge1\). At most \(s/2\) are ties; hence at most \(s/2+L\) gaps have length two. On the other hand at most \(L\) gaps have length greater than two, since \(\sum_F(\ell(F)-2)\le L\). Counting all \(s\) gaps now gives \(s\le s/2+2L\), or \(N\ge 2s+s/4=(9/8)2^{n-1}\). \(\square\)

**A verification without cosets.** The Lean proof uses the same accounting along individual edges. Define \(P(x)\) as the shortest length of a word in the nonpivot labels summing to \(x\), capped at \(d+2\); use that cap for unreachable residues. Then \(P(x+g)\le P(x)+1\), and \(P(\sigma(T))=|T|\) for every squarefree \(T\). If \(b\notin T\), any word reaching \(\sigma(T)-g\), followed by \(b\), gives a different multiset of sum \(\sigma(T)\); it must have length at least \(|T|+2\). The cap is also large enough. Therefore the nonnegative edge weight \(1+P(x)-P(x+g)\) is at least two at \(x=\sigma(T)-g\). When a two-step hit \(F\mapsto T\) is strictly downward, \(x=\sigma(F\cup\{b\})\), and this weight is at least three. All edge weights together sum to \(N\) by translation invariance. This bounds the number of strict hits by \(L\); (2) bounds the number of misses by \(L\); the half-cube lemma bounds the remaining ties by \(s/2\).

## Context and verification

[José A. R. Fonollosa](https://arxiv.org/html/2607.08366v2#S8) proposed the global cyclic optimum and certified \(n\le7\). Inal proved the order \(2^{n-1}\) is optimal among all finite abelian groups and classified the equality case; the [author’s updated repository](https://github.com/jarfo/min-modulus#open-problem-4-all-finite-abelian-groups) records the result. Sitjar’s Theorem A gives the explicit cyclic surplus \(\max\{2n-2,\lceil(2^{n-1}-1)/(n-1)\rceil\}\) for \(n\ge5\), and his Theorem B settles \(n=8,9\) by exhaustive computation. Sitjar counts doubled-label escapes across all possible doubled labels; our estimate counts equal-weight collisions for a single nonzero double, then bounds strict downward moves across the gaps between successive subset sums.

The formal statement uses the original `IsValidMod` predicate in Formal Conjectures. The proof is divided into [the Boolean cube and word distance](CyclicSurplus.lean), [the potential sum](CyclicCount.lean), and [the final modulus theorem](CyclicSurplusFinal.lean). [WeightedModulus.lean](WeightedModulus.lean) supplies the elementary translation equivalence. The result concerns arbitrary residue sets and all \(n\ge3\); it does not rely on a finite search.
