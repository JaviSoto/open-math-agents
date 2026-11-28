# Moll’s split-prime prediction holds outside a zero-density set

Let \(G_n=\prod_{k=1}^{n}(1+ki)\) and \(a_n=\operatorname{Im}G_n\), as in [OEIS A105751](https://oeis.org/A105751). Fix a prime \(p\equiv1\pmod4\). We prove that outside an exceptional set of upper Banach density zero,
\[
  v_p(a_n)=\frac{n}{p-1}+O_p(\log(n+2)).
\]
In fact, for every interval of \(X\) consecutive positive integers, the exceptional set occupies at most \(O_p(X/\sqrt{\log\log X})\) places (for sufficiently large \(X\)). The exceptional set consists of indices where the two split factors have *equal* valuations. This result does not control cancellation on those indices; the original all-indices conjecture remains open. The same conclusion holds for the real part.

### Separate the two valuations

Choose \(r\in\mathbb Z_p\) with \(r^2=-1\), by the prime hypothesis and Hensel lifting. Let \(r_j,s_j\in\{1,\ldots,p^j-1\}\) denote the least residues of \(r,-r\). Thus \(s_j=p^j-r_j\). The embeddings \(i\mapsto\pm r\) give valuations \(U(n),V(n)\) of the two images of \(G_n\). Since \(1+kr=r(k-r)\) and \(1-kr=-r(k+r)\), they count multiples of successive powers of \(p\) in the two residue classes:
\[
 U(n)=\sum_{j\ge1}\big(\lfloor n/p^j\rfloor+1_{n\bmod p^j\ge r_j}\big),
 \quad V(n)=\sum_{j\ge1}\big(\lfloor n/p^j\rfloor+1_{n\bmod p^j\ge s_j}\big).
\]
Every nonzero contribution comes from some \(k\le n\) with \(p^j\mid k^2+1\), so \(j\le\log_p(n^2+1)\). Both sums are \(n/(p-1)+O_p(\log(n+2))\). When \(U\ne V\), the sum and the difference of the two products have valuation exactly \(\min(U,V)\). Dividing by \(2\) or \(2r\) does not change it. It suffices to bound the concentration of \(D(n)=U(n)-V(n)\) at a single integer.

### Independent digits that change the difference by exactly one

Number base-\(p\) digit columns starting at zero, let \(b_j\) be digit \(j\) of \(r\) and put \(t=(p-1)/2\). For \(j\ge1\), digit \(j\) of \(-r\) is \(p-1-b_j\), since the units digit of \(r\) is nonzero. At level \(j+1\) the summand of \(D\) compares the low \(j+1\) digits of \(n\) to the two roots: a strict comparison in the top digit decides the entire comparison; at equality, compare the lower digits.

Call a column \(j\ge2\) usable in any of the three situations below. In each situation there are two choices for the three digits of \(n\) at \(j-1,j,j+1\) such that switching between the choices changes \(D(n)\) by exactly one in absolute value, with fixed sign, independently of **all** the other digits:

* If \(b_j\notin\{0,t,p-1\}\), choose digit \(j\) of \(n\) to be zero or \(t\). Zero is strictly below both root digits, while \(t\) is strictly between them. Fix digit \(j-1\) to be \(t\).
* If \(b_j=t\) and \(b_{j-1}\ne t\), fix digit \(j-1\) of \(n\) to be \(t\), strictly between the two root digits there. At digit \(j\) choose zero or \(t\). The latter inherits those opposite comparisons; the former is below both.
* If \((b_{j-1},b_j)=(0,p-1)\) or \((p-1,0)\), again fix digit \(j-1\) of \(n\) to be \(t\). At digit \(j\), choosing \(t\) lies strictly between the roots. Choosing zero lies below both: one root has digit \(p-1\); for the root with digit zero, its preceding digit is \(p-1>t\).

In every case fix digit \(j+1\) to any value different from both root digits there. This resets both comparisons, so all levels above the one being switched stay unchanged, even if higher digits match a root for a long time. Earlier levels are unchanged as well.

### There are enough usable columns, without any digit normality assumption

A run of a single digit \(b\) of \(r\) from column \(k\) through column \(l-1\) satisfies \(l\le2k+O_p(1)\). Indeed if \(A\) is the integer specified by the first \(k\) digits, then
\[
  (p-1)r\equiv q=(p-1)A-bp^k\pmod{p^l}.
\]
Thus \(p^l\mid q^2+(p-1)^2\), a strictly positive integer \(O_p(p^{2k})\). An interval of unusable columns has only digits \(0,t,p-1\); except at its left boundary, an extreme digit cannot be followed by \(t\) or by its opposite extreme. It is therefore at most two runs, an initial run of \(t\)'s and a constant extreme run (allowing either to be empty). Its right endpoint is at most four times its left endpoint plus \(O_p(1)\). Iteration gives \(\gg_p\log m\) usable columns among the first \(m-1\). Greedily keeping disjoint three-digit blocks loses at most a fixed factor.

### Count ties

Consider any complete aligned block of \(p^m\) consecutive integers. Its low \(m\) digits are independent uniform digits; all higher digits are fixed. For each of the disjoint usable triples, the probability of landing on one of its two prescribed words is \(2/p^3\), independently across triples. Condition on which triples land on their words, all digits off those triples, and the exact words of the nonselected triples. If \(k\) triples land on their words, the remaining \(k\) binary choices are independent fair coins. Each switch changes \(D\) by exactly a signed one, regardless of the other choices. The largest conditional atom of \(D\) is therefore at most \(2^{-k}\binom{k}{\lfloor k/2\rfloor}=O((k+1)^{-1/2})\). With \(k\) binomial on \(\gg_p\log m\) trials of fixed positive success probability, averaging gives \(O_p(1/\sqrt{\log m})\) (split at half the mean and use Chebyshev).

For an arbitrary interval of length \(X\), take \(m=\lfloor\frac12\log_p X\rfloor\), partition it into complete aligned blocks, and discard at most \(2p^m\) endpoints. The stated uniform bound follows for \(D(n)=0\), indeed for any one prescribed value of \(D(n)\). No finite experiment or assumption about typical algebraic digits enters the proof.

The two existing LeftToSolve reductions are complementary: [R1](https://github.com/GuillaumeBAUD-coder/open-math-agents/blob/8296a422a4f303dc7498b31c80ea3ae45c8f2079/reductions/OeisA105751.conjecture.variants.moll_p_mod_4_eq_1.R1.lean) treats the factorial lower bound and nonvanishing, and [R2](https://github.com/GuillaumeBAUD-coder/open-math-agents/blob/8296a422a4f303dc7498b31c80ea3ae45c8f2079/reductions/OeisA105751.conjecture.variants.moll_p_mod_4_eq_1.R2.lean) isolates excess cancellation on ties. The argument here bounds the number of ties but does not assume either reduction’s open hypotheses.
