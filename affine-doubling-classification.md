# All valid cyclic sets closed under affine doubling

Let \(A\subseteq\mathbb Z/N\mathbb Z\) have \(n\ge2\) elements. Following [Fonollosa](https://arxiv.org/abs/2607.08366), call \(A\) *valid* if the multiset containing every element of \(A\) once is the only length-\(n\) multiset on \(A\) with its sum. We classify those valid sets for which some map \(a\mapsto2a+h\) sends \(A\) into itself. Surjectivity is not assumed. The condition is invariant under translation and multiplication by a unit and holds for Fonollosa’s extremal construction.

**Theorem.** A valid affine-doubling-closed set of size \(n\) exists modulo \(N>0\) if and only if, for some integer \(b\ge0\) with \(2^b\le n\),
\[
                              2^n-2^b\mid N.
\]
More precisely, after translating by \(h\), every such set is
\[
                 \{x,2x,\ldots,2^{n-1}x\},
         \qquad \operatorname{ord}(x)=2^n-2^b .
\]
Conversely, each element of this order produces a valid closed set by this formula. Its first \(b\) positions are the tail, and the remaining \(n-b\) form a cycle. In particular the least modulus in this class is exactly \(2^n-2^{\lfloor\log_2 n\rfloor}\); at that modulus all such sets are affinely equivalent to Fonollosa’s construction. For odd \(N\) the criterion reduces to \(2^n-1\mid N\).

## Why there is just one orbit

Translate \(A\) by \(h\) so the map becomes \(f(a)=2a\). Translation preserves validity because all compared multisets have equal length. A squarefree submultiset of \(A\) cannot be replaced by any different multiset on \(A\) of equal size and sum: the other labels can be kept unchanged.

By [Sitjar, Lemma 2.3(a)](https://doi.org/10.5281/zenodo.24228247), \(A\) contains at most one antipodal pair. Indeed, if \(2a=2a'\) for distinct residues, they differ by the unique nonzero two-torsion element \(d\). Two distinct such pairs \(\{a,a+d\}\), \(\{c,c+d\}\) are disjoint, and \((a+d)+c=a+(c+d)\) violates the replacement rule. Hence \(A\setminus f(A)\) has size at most one.

Start at its sole element if there is one; otherwise start anywhere in \(A\). Let \(O\) be the resulting forward orbit and \(D=A\setminus O\). Every member of \(D\) has a predecessor in \(A\), necessarily in \(D\) since \(O\) is forward closed. Finiteness gives \(D=f(D)\) and \(f\) permutes \(D\). In particular \(\sum D=2\sum D\), so \(\sum D=0\).

If \(k=|D|>0\), remove \(D\) and the label \(f^k(x)\) from the original multiset, where \(x\) is the chosen start. Replace them with the \(k+1\) labels \(x,f^0(x),\ldots,f^{k-1}(x)\). Their sum is \(2^kx\), exactly the sum removed. None lies in \(D\). This gives a different multiset of the prescribed length, which is impossible. Thus \(O=A\); its initial \(n\) values are distinct and \(2^nx=2^bx\) for some \(0\le b<n\).

## How the order is forced

Put \(m=\operatorname{ord}(x)>0\), \(M=2^n-2^b\). The return gives \(m\mid M\). In fact **any** valid set consisting of \(n\) distinct consecutive dyadic powers of an element has \(m\ge2^n-n\), even without the return assumption. Otherwise \(W=2^n-1-m\) lies between \(n\) and \(2^n-2\). Its binary expansion uses at most \(n\) coins with denominations \(1,2,\ldots,2^{n-1}\). While fewer than \(n\) coins remain, some coin is larger than one, since \(W\ge n\); split it into two equal halves. The resulting \(n\) coins have the same group sum as all \(n\) labels, but their ordinary integer weight is \(W\), not \(2^n-1\). Distinct powers in \(A\) ensure different digit multisets give different label multisets.

Since \(n\le2^{n-1}\), a proper divisor of \(M<2^n\) would be less than \(2^n-n\). Thus \(m=M\), and \(M\ge2^n-n\) gives \(2^b\le n\).

## Why every listed order works

Choose \(x\) of order \(M=2^n-2^b\) with \(2^b\le n\). The first \(n\) powers are distinct: any positive difference of two of their integer weights is smaller than \(2^{n-1}\le M\). Their set is closed because \(2^nx=2^bx\).

Represent a candidate length-\(n\) multiset by its \(n\) binary coins. Its integer weight \(W\) is at least \(n\ge2^b\). A collision would require \(W\equiv2^n-1\pmod M\). Merge any repeated pair of coins at bit \(j\) into one coin at \(j+1\); at the last bit, wrap the output back to \(b\). Merging preserves the congruence, and preserves \(W\ge2^b\): only a wrap reduces the integer value, and its output coin alone has weight \(2^b\). The number of coins decreases at every merge, so eventually all bits are distinct. The final weight is at most \(2^n-1\); the next smaller representative in its congruence class is \(2^b-1\), which was excluded. Thus the final weight is \(2^n-1\) and all \(n\) bits are present. Because the original word already had length \(n\), no merge occurred and it was the prescribed all-ones word. A cyclic group of order \(N\) has an element of order \(M\) exactly when \(M\mid N\), proving the criterion.

**Scope and verification.** Fonollosa’s published theorem determines the optimum for the *specified* binary family by testing arbitrary moduli. This theorem starts with *any* closed set, derives its orbit shape and classifies every permissible modulus. Validity by itself has not been shown to imply affine doubling closure for a global minimum. Sitjar’s antipodal bound is the prior ingredient in the orbit argument; [Inal](https://doi.org/10.17605/OSF.IO/C58Q9) treats the unrestricted abelian minimum. The Lean verification uses the original `IsValidMod` predicate: [functional graph](AffineDoubling.lean), [carrying and the threshold](DyadicDigits.lean), and [classification](AffineDoublingClass.lean). [BinaryPrefix.lean](BinaryPrefix.lean) supplies the elementary binary expansion and splitting lemmas.
