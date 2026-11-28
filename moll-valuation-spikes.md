# Separation of large cancellation and a mean-value form of Moll’s conjecture

For each fixed prime \(p\equiv1\pmod4\), write \(G_n=C_n+iA_n=\prod_{k=1}^n(1+ki)\), so \(A_n\) is [A105751](https://oeis.org/A105751). Then
\[
 \sum_{4\le n\le X}\left|v_p(A_n)-\frac n{p-1}\right|=O_p\big(X\log^2(X+2)\big).
\]
Moreover, for every \(\varepsilon>0\) at most \(O_{p,\varepsilon}(\log^2(X+2))\) indices \(4\le n\le X\) have \(\big|v_p(A_n)-n/(p-1)\big|>\varepsilon n\). Thus the all-indices conjecture is true **in mean**, and any counterexample sequence with a fixed relative discrepancy has strong separation. This does not rule out such an infinite sequence.

### The segment obstruction

Let \(b_n=\min(v_p(C_n),v_p(A_n))\), taking \(v_p(0)=+\infty\) in this minimum. The two split embeddings show that \(b_n=\min(U(n),V(n))=n/(p-1)+O_p(\log(n+2))\): the invertible change of variables over \(\mathbb Z_p\) is \((C,A)\mapsto(C+r A,C-r A)\), where \(r^2=-1\) and \(2r\) is a unit. The elementary counting proof is given in the [split-prime note](moll-valuation-density.md). The sequence \(b_n\) is nondecreasing, either by these embeddings or by multiplying the Gaussian integers. For \(n\ge4\), \(A_n\ne0\) by the [verified nonvanishing result](https://github.com/GuillaumeBAUD-coder/open-math-agents/blob/8296a422a4f303dc7498b31c80ea3ae45c8f2079/proofs/OeisA105751.conjecture.variants.moll_p_mod_4_eq_1.R1.H2.lean). Put \(e_n=v_p(A_n)-b_n\).

Fix \(X\ge4\), and \(X\le n<m\le 2X\). Let \(z+iw=\prod_{k=n+1}^m(1+ki)\), \(h=m-n\). Then \(w\ne0\). In fact its argument modulo \(2\pi\) is
\[
  h\pi/2-\sum_{k=n+1}^m\arctan(1/k),
\]
and the sum is strictly between zero and \(h/(n+1)\le1<\pi/2\). This excludes a real product for both parities of \(h\). Also \(|w|\le (2X+1)^h\), by taking the product of absolute values.

**Spacing.** If \(e_n,e_m\ge H>0\) for an integer \(H\), then \(p^H\mid w\), and hence
\[
  m-n\ge H/\log_p(2X+1).
\]
Indeed \(A_m=A_n z+C_n w\), and both \(A_m/p^{b_n}\) and \(A_n/p^{b_n}\) are multiples of \(p^H\), since \(b_m\ge b_n\). But \(C_n/p^{b_n}\) is a unit modulo \(p\) since \(e_n>0\). Thus \(p^H\mid w\). The magnitude estimate and strict nonvanishing of the short segment give the spacing.

### Consequences

By spacing, in \([X,2X]\) there are at most \(1+X\log_p(2X+1)/H\) indices with \(e_n\ge H\). Also \(e_n\le \log_p|A_n|\le 2X\log_p(2X+1)\) there. Summing the counting bound over positive integer \(H\) gives \(\sum_{[X,2X]}e_n=O_p(X\log^2(X+2))\). Adding the \(O_p(\log X)\) split-valuation error per term and summing dyadic intervals proves the displayed mean-value theorem. For fixed \(\varepsilon\), large indices with discrepancy exceeding \(\varepsilon n\) have \(e_n\ge\varepsilon X/2\) in this interval. There are only \(O_{p,\varepsilon}(\log X)\) of them per dyadic interval, hence \(O_{p,\varepsilon}(\log^2 X)\) in total.

In particular the mean of \(v_p(A_n)/n\) tends to \(1/(p-1)\), also in absolute deviation (partial summation suffices). The [digit argument](moll-valuation-density.md) answers a different question: it controls the density of **all ties**, even those with no excess valuation. Spacing needs no distributional assumption on the p-adic digits.

The finite spacing obstruction is verified with the Lean kernel in [MollSegment.lean](MollSegment.lean) and [MollActual.lean](MollActual.lean), where `spacing_actual` refers directly to the pinned OEIS definition. The limiting arguments above are written proofs. [This exact-integer check](moll_digit_probe.py) exercises six split primes, independently comparing the digit formulas to Gaussian multiplication.
