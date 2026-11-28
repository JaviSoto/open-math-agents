# Entire perfect-power families excluded in A245212

Let $u$ be squarefree, $u\equiv5\pmod8$, and suppose its number of prime
factors is divisible by eight. Then **for every $k\ge0$ and every $E\ge1$**,
the [A245212](https://oeis.org/A245212) equality fails at $n=2^k u^E$.
For example, one may take $u=3\cdot5\cdot7\cdot11\cdot13\cdot17\cdot19\cdot41
=198843645$. There are such cores with exactly $8,16,24,\ldots$ prime
factors: start from 5 and multiply by distinct primes congruent to 1 modulo 8.

[Standalone Lean proof](UniformDyadResearch245212.lean), theorems
`OMA.UniformDyad245212.all_powers` and `at_every_rank`.
The result allows both exponents and the prime support to grow. It leaves
other odd cores, and products with unequal odd-prime exponents, open.

## Proof

Write $W(v)=\sum_{d\mid v}d\tau(d)$, with $\tau$ the divisor count and
$\sigma$ the divisor sum. The equation under study is
$W(v)+\sigma(v)=2v\tau(v)$. All three arithmetic functions are multiplicative.
Two earlier consequences, included in the proof source, handle $4\nmid E$:

- If an odd-prime exponent is odd, another must be $2\pmod4$. This is
  impossible when all the exponents are the same odd integer.
- If the odd part of a solution is $v^2$, then $v$ is itself a square.
  For $E=2b$ with $b$ odd, $u^b\equiv5\pmod8$ cannot be a square.

For the remaining case write $E=4se$, where $s$ is a power of two and $e$
is odd. Let $r=\Omega(u)$ and $v=u^E$. The two congruences used below are

$$
\begin{aligned}
W(v)&\equiv
\big[(1+2se)^r+se(u^2-1)\big]\sigma(v)&&\pmod{16s},\\
\sigma(v)&\equiv 1+4ser+2se(u-1)&&\pmod{8s}.
\end{aligned}
$$

Here is the local calculation behind them. For an odd prime $p$, put
$G_n=\sum_{i<n}p^i$, $V_n=\sum_{i<n}(i+1)p^i$, and
$C_s=V_{4s}+2s-(2s+1)G_{4s}$. Splitting both sums into equal blocks gives

$$C_{2s}=(1+p^{4s})C_s+2s(1-p^{4s})(1-G_{4s}).$$

Starting with $C_1=p^3-p$, induction gives
$C_s\equiv s(p^2-1)\pmod{16s}$: use $p^{4s}\equiv1\pmod{16s}$ and
$8\mid p^2-1$. The same block split gives
$G_{4s}\equiv2s(p+1)\pmod{8s}$ and $4s\mid G_{4s}$. Repeating the
block $e$ times and adding the endpoint $p^E$ yields

$$W(p^E)\equiv [1+se(p^2+1)]\sigma(p^E)\pmod{16s},\qquad
\sigma(p^E)\equiv1+2se(p+1)\pmod{8s}.$$

To multiply the first local formula, write its coefficient as
$(1+2se)+se(p^2-1)$. Products of two correction terms vanish modulo
$16s$, and the odd factor $1+2se$ can be replaced by 1 in a term already
divisible by $8s$. This gives the displayed formula for $W(v)$; expanding
the second local product similarly gives the formula for $\sigma(v)$.

Now $8\mid r$ and $u\equiv5\pmod8$. Since $(1+2se)^8\equiv1\pmod{16s}$
and $u^2-1\equiv8\pmod{16}$, the coefficient of $\sigma(v)$ in $W(v)$
is $1+8s$ modulo $16s$. On the other hand,
$v\equiv\sigma(v)\equiv\tau(v)\equiv1\pmod{8s}$; for $\tau(v)$ use
$\tau(v)=(1+4se)^r$. With $d=2^k$, the equality at $dv$ would give

$$W(d)W(v)+\sigma(d)\sigma(v)
=2d\tau(d)v\tau(v)
\equiv (W(d)+\sigma(d))\sigma(v)\pmod{16s}.$$

Here the last step uses the exact equality at $d$. Both $W(d)$ and
$\sigma(v)$ are odd. Cancellation now gives $1+8s\equiv1\pmod{16s}$,
contrary to $s>0$.
