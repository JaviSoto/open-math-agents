# A restriction on perfect powers in the odd part

Write $n=2^k m$ with $m$ odd. If $n$ satisfies the [A245212 divisor equality](https://oeis.org/A245212) and $m=u^{2^{h+1}}$ with $h\ge0$, then

$$
  \tau(u^{2^h})\equiv1\pmod{2^{h+1}}.
$$

In particular:

- If $m$ is a square, then $m$ is a fourth power.
- If $m=u^{2^j}$ with $j\ge1$, the number $\Omega(u)$ of prime factors of $u$, counted with multiplicity, must be even. For example, $2^k(p_1\cdots p_{2t+1})^a$ cannot satisfy the equality for any positive even $a$ and distinct odd primes $p_i$.
- Equivalently, among the positive exponents of a nonsingleton odd part that is a square, an even number attain the smallest 2-adic valuation. This concerns the multiplicities of primes, not the size or number of available bases.

To prove the congruence put $N=2^{h+1}$, $H=N/2$, and define the local blocks
$G(p,b)=\sum_{i<b}p^i$ and $B(p,b)=\sum_{i<b}(i+1)p^i$.
For odd $p$, $N\mid G(p,N)$ by doubling the length of the geometric sum. Also $p^N\equiv1\pmod{2N}$ by Euler's theorem. The starting value is $B(p,2)=1+2p\equiv1\bmod2$. Inductively,

$$
 B(p,2N)=(1+p^N)B(p,N)+Np^N G(p,N)
         \equiv 2 B(p,N) \equiv N\pmod{2N}.
$$

Dividing any block of length $aN$ into $a$ blocks of length $N$ now gives $G(p,aN)\equiv0$ and $B(p,aN)\equiv aH\bmod N$. The term with index $aN$ contributes 1 to both sums modulo $N$. For an odd prime $p$ and $v=p^{aN}$ this proves
$v\equiv\tau(v)\equiv\sigma(v)\equiv1$ and $W(v)\equiv1+aH=\tau(p^{aH})\bmod N$, where $W(v)=\sum_{d\mid v}d\tau(d)$. Multiplicativity gives the same relations for $v=u^N$: in particular $W(v)\equiv\tau(u^H)\bmod N$.

Set $d=2^k$. The balance $W(dv)+\sigma(dv)=2dv\tau(dv)$ now yields
$W(d)\tau(u^H)+\sigma(d)\equiv2d\tau(d)\bmod N$. The exact balance $W(d)+\sigma(d)=2d\tau(d)$ holds for powers of two; $W(d)$ is odd. Subtracting and cancelling $W(d)$ gives the required congruence.

For $H=1$ the congruence says $\tau(u)$ is odd, equivalently $u$ is a square. For even $H$, quadratic terms in the product $\tau(u^H)=\prod_{p^a\parallel u}(1+aH)$ vanish modulo $2H$, so $\tau(u^H)\equiv1+H\Omega(u)\bmod 2H$. This proves the parity assertion. At $H=1$ it also follows because a square has an even total prime multiplicity.

The Lean declarations are `OMA.DyadicPower245212.tau_root`, `square_root_is_square`, and `even_multiplicity`, in `DyadicResearch245212.lean`. No restriction is imposed on $k$ or on the odd primes.
