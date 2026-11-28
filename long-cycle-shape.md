# The exceptional nonclosed doubling cycle

In the notation of the [long-cycle theorem](long-doubling-cycles.md), suppose an affine doubling cycle of length \(r\ge n/2\) lies in a valid \(n\)-set \(A\), with \(N<2^n-1\). Translate to make the cycle \(C=\{2^j y:0\le j<r\}\) an ordinary doubling cycle. Then \(A\) is closed under doubling, or
\[
     n\text{ is even},\quad N=2^n-2,\quad r=n-1,\quad A=C\cup\{b\},\quad 2b=0 .
\]
In fact the same dichotomy holds for any \(r>0\) when \(N<(2^{n-r}+1)(2^r-1)\). For every even \(n\ge4\) the exceptional case is realized by a set closed under no affine doubling map.

**Proof of necessity.** The earlier quotient argument gives a subgroup \(H=\langle y\rangle\) of order \(2^r-1\), and the quotient has the smallest feasible order \(2^k\), \(k=n-r\). If \(k>0\), the other labels form a path \(x,2x,\ldots,b=2^{k-1}x\), so \(h=2b\in H\). We show \(h=0\) or \(h\in C\).

Otherwise represent \(h\) by a subset \(S\) of the cycle using ordinary binary digits. It contains at least two labels and cannot exhaust \(C\), since \(\sum C=0\) and \(h\ne0\). The nonempty complement represents \(-h\) with at most \(r-2\) coins. Split any coin into two copies of its cyclic predecessor until exactly \(r-2\) remain. Replacing \(C\cup\{b\}\) by those coins and three copies of \(b\) preserves its cardinality and sum, contradicting validity. If \(2b\in C\), both the cycle and the outside path stay in \(A\) under doubling. If \(2b=0\), then \(r\) is odd: for even \(r\), replace \(C\) by \(r\) copies of \(b\). Nor can \(b\) have any external predecessor \(a\): replace \(C\cup\{b\}\) by \(r-1\) copies of \(b\) and two copies of \(a\). This forces \(k=1\) and gives the asserted modulus.

**The family exists.** Write \(r=n-1\) odd and at least 3, \(M=2^r-1\), and take in \(\mathbb Z/(2M)\)
\[
           C=\{2,4,\ldots,2^r\},\qquad b=M .
\]
The cycle is valid by the binary single-orbit result. Every nonempty zero-sum word on the cycle needs at least \(r\) coins: a shorter one could be split up to \(r-1\) coins, then split once more to obtain a word of length \(r\) with a repeated label, contradicting cycle validity. A competing word for \(C\cup\{b\}\) uses an odd number of copies of the odd label \(b\). They sum to \(b\). If there is more than one copy, the remaining cycle word has fewer than \(r\) coins and sum zero. It cannot be empty either: the entire word has even length \(n\). Thus it contains exactly one \(b\), and validity of \(C\) finishes.

If \(a\mapsto 2a+t\) closed this set, parity forces \(t\) even: an odd \(t\) would map the whole cycle, whose doubles are distinct, to the single odd label. Thus \(C+t=C\) and \(t=2b+t\in C\). Translating an element of \(C\) to \(t\) by \(+t\) would require \(0\in C\), a contradiction.

**Lean proofs.** The endpoint argument is in [CycleTerminal.lean](CycleTerminal.lean). [LongCycleShape.lean](LongCycleShape.lean) proves the dichotomy (theorems **boundary** and **classify**) on the original validity predicate. [SplitCycle.lean](SplitCycle.lean), theorem **examples**, checks the entire infinite family including nonclosure under every affine doubling map.
