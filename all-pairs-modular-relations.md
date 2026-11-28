# Every pair in a small valid modulus belongs to a bounded relation

Let \(A\) be a valid \(n\)-element set in a finite abelian group \(G\): the multiset taking every label once is the unique length-\(n\) multiset on \(A\) with its sum. Suppose \(|G|<2^n\). For **every** two distinct \(a,b\in A\), there exist disjoint \(S,T\subseteq A\setminus\{a,b\}\) and integers \(\ell,h\) such that
\[
 \ell b+\sum_{s\in S}s=h a+\sum_{t\in T}t,\qquad
 \ell+|S|=h+|T|,\qquad
 2\le\ell,h\le9,\quad \ell+h\le12,\quad |S|+|T|\le62.
\]
This is a restriction on every candidate below \(2^n\), including sets in which every affine doubling path is short. It does not by itself imply a long path or settle [Fonollosa's conjecture](https://arxiv.org/abs/2607.08366). The argument works in every finite abelian group.

**Return times.** Translate \(a\) to zero, write \(g=b-a\), and let \(E\) be the other \(n-2\) translated labels. If a squarefree word \(Y\) on nonpivot labels has the same sum as a word \(Z\) on these labels of length at most \(|Y|+1\), then \(Z=Y\): retain the remaining nonpivot labels and fill the remaining slots with zeros. In particular all subset sums of nonpivot labels are distinct.

On every coset of \(\langle g\rangle\) containing a subset sum of \(E\), step by \(g\) from each such sum to the next one. This gives a permutation \(F\mapsto F'\) of the \(s=2^{n-2}\) masks and a positive gap \(\ell(F)\), with \(\sum\ell(F)\le|G|<4s\). We have \(\ell(F)\ge2\), since one step would equate the mask \(F\cup\{g\}\) with a mask omitting \(g\). The integer \(h(F)=\ell(F)+|F|-|F'|\) is also at least two: otherwise replacing \(F'\) by \(F\) together with \(\ell(F)\) copies of \(g\) would contradict squarefree uniqueness. Since the return map permutes the masks, \(\sum h(F)=\sum\ell(F)<4s\). Write
\[
 i(F)=\lfloor(\ell(F)-2)/2\rfloor,\qquad
 j(F)=\lfloor(h(F)-2)/2\rfloor .
\]
The average of \(i+j\) is less than two. Weight the cell \((i,j)\) by \(\max(4-i-j,0)\). The total weight of all cells is \(4+6+6+4=20\); the weight summed over all masks exceeds \(2s\). Consequently some cell \(i+j\le3\) contains more than \(s/10\) masks. Every mask in this cell satisfies the coefficient bounds in the theorem.

**Crossing of reduced pairs.** Undo the translation. For each return cancel \(F\cap F'\), writing \(S=F\setminus F'\), \(T=F'\setminus F\) in the original labels. The sum and length identities in the theorem follow. Consider two distinct reduced pairs \((S,T),(V,W)\) arising in our cell, with coefficients \((\ell,h),(\ell',h')\). Subtract their sum identities. One side now contains \(S\) and \(W\), and the other contains \(V\) and \(T\); after cancelling common copies of \(a,b\), each occurs at most once because \(|\ell-\ell'|,|h-h'|\le1\). Both sides have the same length. If \(S\cap W=\varnothing\), the first side is squarefree, so both multisets must agree by validity (retain the rest of the labels once). Away from \(a,b\), this says \(\mathbf1_S+\mathbf1_W=\mathbf1_V+\mathbf1_T\); the within-pair disjointness implies \(S=V,T=W\), contrary to choice. Thus \(S\cap W\) and, by symmetry, \(V\cap T\) are nonempty.

**Size of a witness.** For each reduced pair the originating masks contain \(S\) and omit \(T\), a face of density \(2^{-k}\), \(k=|S|+|T|\). [Bollobás's set-pairs inequality](https://web.vu.lt/mif/s.jukna/EC_Book_2nd/Bollobas.pdf) says that the sum of \(1/\binom{k}{|S|}\) over distinct reduced pairs is at most one: order the coordinates randomly and use the disjoint events that \(S\) precedes \(T\). For \(k\ge63\) the largest value of \(2^{-k}\binom{k}{j}\) is less than \(1/10\). This holds at \(k=63\) by \(10\binom{63}{31}<2^{63}\), and Pascal's recurrence preserves the bound. If every witness had \(k\ge63\), the union of all its faces would have density at most \(1/10\), contradicting the size of the cell.

**Scope and checks.** The cyclic lower bounds of [Sitjar](https://doi.org/10.5281/zenodo.24228247) count doubled-label escapes; the [earlier return-gap bound](cyclic-surplus-twenty-nine.md) counts the shortest ties in one direction. Here taking both coefficients in two-wide intervals bounds *every* pair's relation support. [CyclicReturn.lean](CyclicReturn.lean) verifies first-return packing, [CyclicPairs.lean](CyclicPairs.lean) verifies the set-pairs inequality, and [RelationGirth.lean](RelationGirth.lean) verifies the \(1/10\)-cell count and the 62-coordinate conclusion for cross-intersecting faces. The application of these components to all pairs is the argument above.
