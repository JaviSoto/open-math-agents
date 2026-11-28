# A divisor-count obstruction for perfect-power odd parts in A245212

Write $\tau$ for the number of positive divisors, $\sigma$ for their sum, and
$\Omega$ for the number of prime factors counted with multiplicity. If the
[A245212 equality](https://oeis.org/A245212) holds at $2^k u^N$, where $u$
is odd and $N\ge4$ is a power of two, then

$$\tau(u^{N/2})\equiv1\pmod{2N}.$$

The extra factor of two strengthens the [previous complete-block congruence](DyadicPower245212.lean).
There is no restriction on $k$, the size of $u$, or its number of prime factors.
Two useful cases:

- If the odd part is a square $s^2$, then $\tau(s)\equiv1\pmod8$. The
  earlier square-root theorem makes $s=v^2$, so this is the $N=4$ case.
- If the odd part is $u^8$, then $4\mid\Omega(u)$. Indeed, for
  $u=\prod p_i^{e_i}$, one has $\tau(u^4)=\prod(1+4e_i)\equiv1+4\Omega(u)\pmod{16}$.
  More generally, the same restriction holds at $2^k u^E$ for **every
  positive multiple of eight** $E$. To see this, write $E=Nc$ with $N$
  a power of two and $c$ odd. Since $N/2$ is divisible by four, the
  product for $\tau((u^c)^{N/2})$ is $1+(N/2)c\Omega(u)$ modulo $2N$.
  For example, no positive power divisible by eight of a squarefree
  product of six odd primes can be the odd part of a solution.

## Proof

For an odd prime $p$ put $G_n=\sum_{i<n}p^i$,
$V_n=\sum_{i<n}(i+1)p^i$, and $D_n=V_n+n/2-G_n$ for even $n$.
We first show $2n\mid D_n$ for every dyadic $n\ge4$.
At $n=4$ this follows by substituting $p^2\equiv1\pmod8$.
Splitting both sums into two blocks gives

$$D_{2n}=(1+p^n)D_n+\frac n2(1-p^n)+np^nG_n.$$

The three terms on the right are divisible by $4n$: $1+p^n$ is even,
$p^n\equiv1\pmod8$, and $4\mid G_n$. For the last fact, $G_n$ factors
as $\prod_{j<\log_2 n}(1+p^{2^j})$, so $n\mid G_n$.

Now set $n=N$ and work modulo $2N$. We have $p^N\equiv1$ by Euler's
theorem. Each new block of $N$ terms adds $G_N$ to the geometric sum and
$V_N$ to the weighted sum: shifting the weights by a multiple of $N$ has
no effect since $G_N$ is even. At exponent $eN$, include the final term
and use $D_N\equiv0$ and $4\mid G_N$. The result is

$$W(p^{eN})\equiv(1+eN/2)\,\sigma(p^{eN})\pmod{2N},$$

where $W(m)=\sum_{d\mid m}d\tau(d)$. Multiplicativity gives
$W(u^N)\equiv\tau(u^{N/2})\sigma(u^N)\pmod{2N}$.

For $v=u^N$ the ordinary complete-block identities give
$v\tau(v)\equiv\sigma(v)\equiv1\pmod N$. At a solution the exact
equation is $W(2^k)W(v)+\sigma(2^k)\sigma(v)=2^{k+1}\tau(2^k)v\tau(v)$.
The right-hand side is unchanged modulo $2N$ if $v\tau(v)$ is replaced
by $\sigma(v)$, because its coefficient is even. Since powers of two
alone satisfy the equation, subtraction leaves
$W(2^k)W(v)\equiv W(2^k)\sigma(v)\pmod{2N}$. Both $W(2^k)$ and
$\sigma(v)$ are odd. Cancel them to obtain the asserted congruence.

The Lean declarations are `OMA.DyadicExtra245212.tau_extra`,
`.square_root_tau`, `.four_multiplicity`, and `.common_exponent`.
The [standalone source](DyadicExtraResearch245212.lean) starts with the
original OEIS import. Check it with `lake env lean /path/to/DyadicExtraResearch245212.lean`
inside google-deepmind/formal-conjectures at revision
`9097e2f90e66d2f6244209cb1c07f7120d17ec53`.
