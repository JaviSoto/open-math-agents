# A necessary prime-factor count for every power in A245212

Suppose $u\equiv5\pmod8$, its number of distinct prime factors is a multiple
of eight, and **each prime dividing $u$ occurs to an odd exponent**. If the
[A245212](https://oeis.org/A245212) equality holds at $2^k u^E$ for any
$k\ge0$ and $E\ge1$, then

$$\Omega(u)\equiv4\pmod8,$$

where $\Omega$ counts prime factors with multiplicity. The surviving residue
is a necessary condition only. The other three even residues eliminate every
$k$ and $E$. The exponents in the factorization of $u$ may all differ.
For instance, take the primes $3,5,7,11,13,17,19,41$ with respective
exponents $1,3,5,7,9,11,13,15$. Their sum is 64 and the product of the primes
is 5 modulo 8. All positive powers of this integer are excluded, after
multiplication by any power of 2.

The [standalone Lean proof](MixedDyadResearch245212.lean) imports only the
original conjecture module. Its final theorem is
`OMA.MixedDyad245212.all_powers`. It includes the
[squarefree result and local block calculation](uniform-squarefree-powers-245212.md)
as special cases.

## Why the total exponent suffices

Write $u=\prod_{i=1}^r p_i^{1+2a_i}$ and put $A=\sum_i a_i$.
Every odd square is 1 modulo 8, so $U=\prod_i p_i\equiv u\equiv5\pmod8$.
Odd $E$ are ruled out by the exponent-parity obstruction: an odd exponent
would require another exponent equal to 2 modulo 4. If $E=2b$ with $b$ odd,
then $u^b\equiv5\pmod8$ cannot be a square, as the square-root obstruction
would require.

Write the remaining exponents as $E=4se$, with $s$ a power of two and $e$
odd. Put $t_i=ea_i$ and $T=\sum_i t_i=eA$. The exponent of $p_i$ is now
$4s(e+2t_i)$. In the squarefree calculation, the factor expressing
$W(p_i^{4se})/\sigma(p_i^{4se})$ modulo $16s$ was
$B_i=1+se(p_i^2+1)$. Here $W(v)=\sum_{d\mid v}d\tau(d)$; the ratio is
well-defined because the divisor sum is odd. Replacing $e$ by $e+2t_i$
changes this coefficient to

$$
1+s(e+2t_i)(p_i^2+1)\equiv B_i\,[1+4s(1+2se)t_i]\pmod{16s}.
$$

Indeed $p_i^2\equiv1\pmod8$, and
$B_i(1+2se)\equiv(1+2se)^2\equiv1\pmod4$. The ordinary divisor sum and
the divisor count at this prime are unchanged modulo $8s$. When the new
weight factors are multiplied, every cross term involving two corrections
is divisible by $16s$. Therefore the factor across the entire odd part is

$$(1+8s)\,[1+4s(1+2se)T]\pmod{16s}.$$

As in the squarefree proof, the equality at $2^ku^E$ would force this factor
to be 1 modulo $16s$. Subtracting 1 and dividing by $4s$ leaves
$(1+2se)T+2\equiv0\pmod4$. Since the coefficient is odd, $T\equiv2\pmod4$.
As $e$ is odd the same holds for $A$, and
$\Omega(u)=r+2A\equiv4\pmod8$.
