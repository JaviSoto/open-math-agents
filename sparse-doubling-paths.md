# The conjectured modulus when a valid set has few doubling paths

Let \(A\subseteq\mathbb Z/N\) have \(n\ge2\) distinct labels. Validity means that among multisets of length \(n\) on \(A\), only the all-ones multiset has sum \(\sum A\). Suppose that, after translation, \(A\) is covered by \(h\) pairwise disjoint doubling paths, of lengths \(L_i\) and first elements \(x_i\). Thus path \(i\) is \(x_i,2x_i,\ldots,2^{L_i-1}x_i\). Write \(W_i=2^{L_i}\), \(K=\binom{n+h-1}{h}\), and \(f(n)=2^n-2^{\lfloor\log_2 n\rfloor}\).

**Theorem.**

1. For every such cover, \(N\ge 2^n-K\).
2. Suppose \(2^{\,n-4h}>K\), \(2^{\lceil n/h\rceil}\ge4n\), and \(2h\lfloor\log_2 n\rfloor\le n\). Then \(N\ge f(n)\). For \(n\ge4\), if \(N=f(n)\), the minimizing set is the canonical binary set up to an affine automorphism.

In particular these conclusions hold eventually for every fixed \(h\). More generally an infinite sequence of counterexamples must have \(h=\Omega(n/\log n)\) for every affine doubling map, where \(h\) is its minimum path-cover size. For example \(h\le n/(4\log_2(2n))\) implies all three conditions for sufficiently large \(n\): \(K\le(2n)^h\le2^{n/4}\), \(4h=o(n)\), and \(n/h\ge4\log_2(2n)\). No distribution assumption is made on the path lengths.

### The box and its small simplex

Map the integer box \(R=\prod_i[0,W_i)\) into the group by \(\phi(s)=\sum_i s_i x_i\). The canonical multiset has integer coordinates \(w_i=W_i-1\). A different nonnegative vector representing its group value cannot have a coin representation of length at most \(n\) and coordinate sum at least \(n\): repeatedly split a binary coin larger than one in its own path until the length is \(n\). Distinct tuples produce distinct multisets because all the displayed labels are distinct.

If distinct \(s,t\in R\) map to the same group element, orient them so that the number of \(i\) with \(s_i>t_i\) is no greater than the number with \(s_i<t_i\). The tuple \(w+s-t\) is nonnegative. A decreased coordinate costs at most \(L_i-1\) binary coins; an unchanged one costs \(L_i\). An increased coordinate, with \(d=s_i-t_i>0\), costs at most \(L_i+1\): represent \(W_i\) by two largest coins and \(d-1<W_i-1\) by at most \(L_i-1\) coins. Thus \(w+s-t\) costs at most \(n\) coins. Its coordinate sum must be less than \(n\). Since \(s\le w+s-t\) coordinatewise, \(s\) has coordinate sum less than \(n\).

Consequently the points of \(R\) with coordinate sum at least \(n\) map injectively. There are at most \(K\) nonnegative integer tuples with coordinate sum less than \(n\), by stars and bars (add one slack variable). This proves conclusion 1. More particularly, if \(N<2^n\), then fewer than \(K\) group elements are missing from \(\phi(R)\).

### A long path cannot have a missing successor

Assume \(N<2^n\) and choose among covers by at most \(h\) paths one maximizing its longest length \(L\). Adjoining empty paths if necessary keeps the estimate with the original \(h\). Let \(x=x_J\) start a longest path, with \(W=2^L\ge4n\). The order of \(x\) is at least \(W-L\). Indeed if the order were below \(W-L\), then \(W-1-\operatorname{ord}(x)\) would have a binary expansion using at most \(L\) coins and value at least \(L\); splitting would contradict validity of the path. Every subset of a valid set is valid by retaining the other labels once.

Consider the smaller box \(T=\prod_i[0,2^{\max(L_i-4,0)})\), of size at least \(2^{n-4h}>K\). Its images are distinct: if two distinct inputs collide, orient the displacement as in the preceding proof. Every coordinate of the shifted canonical target is at least \(L_i\): for \(L_i\le4\) the displacement is zero, and otherwise the loss is less than \(2^{L_i-4}\). Thus its coordinate sum is at least \(n\), a contradiction.

If \(Wx\notin\phi(R)\), then every \(Wx+\phi(s)\) for \(s\in T\) must be missing too. In fact, suppose one equals \(\phi(a)\), \(a\in R\). Some \(s_i>a_i\), else \(a-s\) represents \(Wx\). Shift the canonical word by \(We_J+s-a\). For any non-endpoint coordinate with a positive difference \(d=s_i-a_i\), the new coordinate costs at most \(2+\operatorname{popcount}(d-1)\le L_i-2\); a nonpositive difference costs at most \(L_i\). If \(s_J\le a_J\), the endpoint coordinate costs at most \(L+2\), and some other coordinate saves at least two coins. If \(s_J>a_J\), it costs at most \(4+\operatorname{popcount}(s_J-a_J-1)\le L\). In both cases the total cost is at most \(n\) and the endpoint coordinate alone is at least \(W\ge n\), contrary to validity. We would thus have more than \(K\) holes, which is impossible.

Now write \(Wx=\phi(a)\). The shifted coordinates \(w+We_J-a\) are nonnegative, and the \(J\)-coordinate is at least \(W\). These coordinates can be represented using
\[
                  n+2-\sum_i \operatorname{popcount}(a_i)
\]
coins: use two largest coins on the \(J\)-axis, then use the complements of the binary digits of each \(a_i\). Validity says the displayed sum of popcounts is at most one. Thus \(Wx\) is zero or an actual path label.

**The zero endpoint.** If \(Wx=0\), its starting point has order dividing \(W\), and \(W-L>W/2\) forces order exactly \(W\). Project the box on the remaining paths to \(G/\langle x\rangle\). If two different inputs collide, orient their displacement as before, so the displaced outside coordinates cost at most \(n-L\) coins. The group discrepancy is in \(\langle x\rangle\), so it can be corrected on the longest axis by some \(i\in[-W+1,0]\). If \(W-1+i\ge n\), its binary expansion uses at most \(L\) coins, with the required total ordinary size. Otherwise use the equivalent coordinate \(W+(W-1+i)\). It takes two largest coins and at most \(L-2\) more because \(0\le W-1+i<n\le W/4\). Again the ordinary size is at least \(n\); both alternatives contradict validity. Thus the remaining box maps injectively to the quotient, giving \(N/W\ge2^{n-L}\) and \(N\ge2^n\), contrary to hypothesis.

If \(Wx\) lands on another path, append the suffix of that path starting at the landing point to the chosen path, keeping its (possibly empty) prefix as a separate path. This strictly increases the longest length without increasing the number of paths. Thus our path closes within itself. If its first return is to \(2^t x\), the [closed-orbit classification](affine-doubling-classification.md) or the elementary order calculation gives \(2^t\le L\). The cycle has length \(r=L-t\).

### Why this cycle contains at least half the labels

The cycle sums to zero. Any disjoint outside path of length \(s\) satisfies \(2^s\le r+s\): otherwise its ordinary sum \(2^s-1\ge r+s\) can be split into exactly \(r+s\) coins all on that path. They would replace the cycle and path together, an impossible collision. In particular every remaining path has length at most \(\lfloor\log_2 n\rfloor\). The transient length \(t\) obeys the same bound. Hence \(n-r\le h\lfloor\log_2 n\rfloor\le n/2\). The [long-cycle theorem](long-doubling-cycles.md) now gives \(N\ge f(n)\). Its [classification below \(2^n-1\)](long-cycle-shape.md) leaves only doubling-closed sets or the exceptional modulus \(2^n-2\), which is strictly greater than \(f(n)\) for \(n\ge4\); the closed-set equality classification applies.

**Verification and history.** [PathCoins.lean](PathCoins.lean) and [PathBox.lean](PathBox.lean) check conclusion 1 on the original validity predicate, including the exact binomial coefficient. The proof above supplies conclusion 2. Fonollosa's [prescribed binary family](https://arxiv.org/abs/2607.08366) motivates the digit estimates. [Sitjar](https://doi.org/10.5281/zenodo.24228247) establishes bounds for general valid sets and exact universal minima through \(n=9\). Neither the path-cover hypothesis nor the stated conclusions are assumed for a general valid set.
