# An exponent obstruction for A245212

Write a positive integer as \(n=2^a m\), with \(m=\prod_{i=1}^r p_i^{e_i}\) for distinct odd primes. Suppose \(n\) satisfies the divisor identity from [OEIS A245212](https://oeis.org/A245212). Then

\[
                 2^r\ \mid\ \prod_{i=1}^r(e_i+2).
\]

This has no restriction on the number or sizes of the primes, or on the power of two in \(n\). In particular, if the odd part is not a square, at least one odd prime has exponent **2 mod 4**. Thus no solution has a nontrivial squarefree odd part. More generally, a solution with a nonsquare odd part cannot have all odd prime exponents odd or multiples of four.

Write \(\tau,\sigma\) for the number and sum of positive divisors, and define \(W(n)=\sum_{d\mid n}d\tau(d)\). The original identity says \(W(n)+\sigma(n)=2n\tau(n)\). These three divisor functions are multiplicative. Let \(v(x)\) count the factors of two in a positive integer. For every odd prime \(p\), and \(t=e+1\),

\[
 v(W(p^e))+1=v(t)+v(t+1),\qquad 2^{v(t)}\mid\sigma(p^e).
\]

For the first identity, consider a block of \(N=2^{h+1}\) terms in the weighted geometric sum \(\sum_{j=0}^{t-1}(j+1)p^j\). Its weighted sum is \(2^h\bmod N\); its ordinary geometric sum vanishes modulo \(N\). Since \(p^N=1\bmod N\), appending full blocks adds their weighted sums modulo \(N\). If \(t=uN\) with \(u\) odd, the result has valuation exactly \(h\). If \(t\) is odd, apply this result to \(t+1\) and remove the last term: \((t+1)p^t\) is zero modulo the resulting \(N\). The ordinary block congruence gives the second assertion.

Now put \(T=\sum_i v(e_i+1)\). Both \(\sigma(n)\) and \(2n\tau(n)\) are divisible by \(2^T\), hence so is \(W(n)\). Since \(W(2^a)\) is odd, \(v(W(m))\ge T\). Summing the local weighted identity gives \(v(W(m))+r=T+\sum_i v(e_i+2)\), proving the divisibility. If some \(e_j\) is odd, its contribution to this last sum vanishes; another contribution must then be at least two.

The standalone [Lean proof](ParityResearch245212.lean) starts from the original Formal Conjectures definition. The main results are `OMA.ExponentParity245212.exponent_product` and `two_mod_four`. Both replay with only the three standard Lean axioms. This is a necessary condition; it does not settle A245212.
