# A245212 holds for every positive integer with at most two distinct odd prime factors

Let \(n>0\), let \(\tau(n)\) count its positive divisors, let \(\sigma(n)\) be their sum, and put \(W(n)=\sum_{r\mid n}r\tau(r)\). The [A245212 conjecture](https://oeis.org/A245212) is that
\[
                 W(n)+\sigma(n)=2n\tau(n)
                 \quad\Longleftrightarrow\quad n=2^k .
\]
**This equivalence holds whenever at most two distinct odd primes divide \(n\).** There is no bound on \(n\), the primes, or their exponents. Any counterexample to the full conjecture must contain at least three distinct odd primes. This is a written proof with reproducible integer certificates. Several parts are independently checked in Lean; the entire result is not yet a single Lean theorem.

## Reduction to one finite rectangle

Direct summation gives equality for powers of two. For exactly one odd prime, the [one-prime identity](divisor-envelope-245212.md) would force the odd prime minus one to equal \(k+(k+1)/(2^{k+1}-1)\), which is impossible. Now write \(n=2^{K-1}p^{B-1}q^{C-1}\) with odd primes \(p<q\), \(B,C\ge2\). Write \(m=\min(B,C)\), \(M=\max(B,C)\).

1. The [least-prime Lean certificates](eleven-moving-pair-245212.md) give \(p\ge13\). The complementary exponent cannot be [one](linear-power-family-245212.md), [two](quadratic-power-family-245212.md), [three](cubic-power-family-245212.md), or [four](fourth-power-family-245212.md). Hence \(m\ge6\). The [simultaneous integer separation and effective argument](two-odd-effective-245212.md) give \(m\le32\).
2. The [complementary-exponent theorem](ComplementaryBoundedResearch245212.lean) gives \(K\le512m^4\), \(M\le32768m^6\), and \(M\le64m^2K\). For \(K\le5\) the elementary weighted-factor bound already excludes a solution. For \(K\ge6\), \(p\le3K\) and \(pB>(K-1)(B-1)\).
3. The [integer enclosure proof](two-odd-box-audit-245212.md) excludes every point with \(K>1250\) or \(M>225\). It uses the two nonzero integers in the [global separation](TwoOddGlobalGap245212.lean), the two cofactor inequalities, and the two positive deficits at the infinite-prime limit. The [exterior verifier](two_odd_box_audit_245212.py) covers both orientations in 720 disjoint terminal boxes (before discarding ranges forbidden by step 2). All rounding uses integer arithmetic. What remains is \(6\le K\le1250,\quad 6\le B,C\le225,\quad \min(B,C)\le32\).

## Two independent exhaustions

For each \(K,p,B,C\), let \(b=2^{K-1}p^{B-1}\), \(A=W(b),S=\sigma(b),T=b\tau(b)\), and \(D=C(2T-A)-S\). At a solution \(D>0\) and the [last-digit identity](odd-divisor-count-245212.md) forces
\[
 q=\left\lceil\frac{(C-1)A+S}{D}\right\rceil,\qquad
 q\mid A+S,\qquad q^{C-1}\mid A-(q-1)S.
\]
Thus the larger prime never needs an artificial upper bound. Both checks keep even a composite candidate if it passes their necessary conditions.

* The [Python enclosure](two_odd_boxes_245212.py) and [direct replay](two_odd_replay_245212.py) retain 170,873 exponent triples; these give 10,607,398 choices including the smaller prime. Of those, 13,924 meet the size and divisibility tests. None satisfies the original divisor equality. The [independent enclosure comparison](two_odd_box_overlap_245212.py) confirms that its 85,481 candidate exponent triples are all included.
* The [C++/GMP replay](two_odd_rectangle_245212.cpp) **does not use either interior enclosure**. It covers all 2,422,703,259 ordered positions in the whole rectangle after the elementary bounds on the smaller prime in step 2. It constructs the moments by adding one divisor at a time. Where the digit denominator is positive, the displayed ratio is fractional-linear in \(C\), hence monotone. Intervals with equal ceiling at both endpoints have the same only possible \(q\). This groups positions without discarding any candidate. Exactly 2,372 positions pass the stronger divisibility test modulo \(q^2\); none passes it modulo \(q^{C-1}\). An elementary direct loop over the smaller rectangle \(K\le90,M\le50,m\le16\) reproduced the same 1,498,346 positions, 92 square-congruence survivors and zero full-power survivors.

This exhausts both odd prime powers in either order. The tests can be repeated from the research branch:

```sh
python3 two_odd_box_audit_245212.py
python3 two_odd_replay_245212.py --jobs 6
c++ -O3 -std=c++17 two_odd_rectangle_245212.cpp -lgmpxx -lgmp -o replay
./replay 12
```

On the machine used for verification the full C++ rectangle took 39 seconds and the independent Python interior took 2.3 seconds. When using Homebrew's GMP, add its `include` and `lib` paths to the compiler invocation.
