# Exact values at prime-power endpoints for split primes

For each prime \(p\equiv1\pmod 4\) and \(m\ge1\), let \(N=p^m\). For the actual imaginary Gaussian factorial [OEIS A105751](https://oeis.org/A105751),
\[
 v_p(A_{N-1})=v_p(A_N)=\frac{N-1}{p-1}.
\]
This includes the split-valuation **ties** on this subsequence; it is not a claim about all indices. For instance, the 5-adic valuations at indices 24, 124 and 624 are exactly 6, 31 and 156.

Let \(r^2=-1\) in \(\mathbb Z_p\). The two embeddings of \(G_{N-1}=\prod_{k=1}^{N-1}(1+ki)=C_{N-1}+iA_{N-1}\) give two products whose difference is \(2r A_{N-1}\). In the second product permute the factors by \(k\mapsto N-k\). Its factor paired with \(x_k=1+kr\) is exactly \(y_k=x_k-Nr\).

Put \(t_k=\min(v_p(x_k),m)\). Since \(x_k=r(k-r)\), the number of indices with \(t_k\ge j\) is \(N/p^j\) for \(1\le j\le m\): the nonzero residue \(r\bmod p^j\) occurs that many times in \([1,N-1]\). Thus \(\sum_k t_k=(N-1)/(p-1)\). There is exactly one index \(s\) where \(t_s=m\).

After dividing each pair by \(p^{t_k}\), the normalized factors at every \(k\ne s\) are congruent **units** modulo \(p\): their difference is \(p^{m-t_k}r\). At \(s\), the difference is exactly the unit \(r\). Hence the difference of the two normalized products is nonzero modulo \(p\), being \(r\) times the common product of the other units. Dividing by the unit \(2r\) gives the asserted valuation of \(A_{N-1}\). Both products are multiples of the displayed common power of \(p\), so \(C_{N-1}\) is as well. Finally \(A_N=A_{N-1}+NC_{N-1}\), which has the very same valuation.

This direct reflection calculation complements the [spacing bound](moll-valuation-spikes.md), which controls the frequency of large discrepancies but not their locations.
