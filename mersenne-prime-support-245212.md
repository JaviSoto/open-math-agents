# Recovering the index from the primes of a Mersenne number

Let $Q(t)=(2^t-1)/\gcd(2^t-1,t)$, for $t\ge1$. Its prime divisors, *without their multiplicities*, determine $t$:

$$
t=\operatorname{lcm}_{p\mid Q(t)}\operatorname{ord}_p(2).
$$

Here and below $p$ ranges over primes; the empty lcm is 1. In fact $Q(t)$ and $2^t-1$ have the same prime divisors. If $d_p=\operatorname{ord}_p(2)$ and $w_p=v_p(2^{p-1}-1)$ for odd $p$, the exact exponent of $p$ is

$$
v_p(Q(t))=\begin{cases} w_p & d_p\mid t,\\0 & d_p\nmid t.\end{cases}
$$

Consequently $\gcd(Q(s),Q(t))=Q(\gcd(s,t))$ and $Q(s)\mid Q(t)$ exactly when $s\mid t$. Even inclusion of the *prime sets* of $2^s-1$ and $2^t-1$ is equivalent to $s\mid t$.

For example, $2^6-1=63$ and $Q(6)=21$. The orders of 2 modulo 3 and 7 are 2 and 3, so their lcm recovers 6. Neither prime separately gives order 6.

## Proof

Fermat's little theorem gives $d_p\mid p-1$, so $p\nmid d_p$. A prime $p$ divides $2^t-1$ exactly when $d_p\mid t$. In that case lifting the exponent at the odd prime $p$ gives

$$
v_p(2^t-1)=v_p(2^{d_p}-1)+v_p(t).
$$

The first term is positive. The gcd in $Q(t)$ therefore removes exactly $v_p(t)$ copies of $p$. Applying the same identity to $t=p-1$ identifies the first term with $w_p$. Since $2^t-1$ is odd, this accounts for every prime.

Put $L=\operatorname{lcm}_{p\mid Q(t)}d_p$. Each order divides $t$, hence $L\mid t$. Also $p^{w_p}\mid 2^{d_p}-1\mid 2^L-1$ for every prime in $Q(t)$, so $Q(t)\mid 2^L-1$. For $t\ge2$, write $a=\lfloor t/2\rfloor$ and $b=t-a$. We have $t\le 2b\le2^b$, and thus
$t(2^a-1)<2^t-1$. Because $\gcd(2^t-1,t)\le t$, it follows that $Q(t)>2^a-1$. If $L$ were a proper divisor of $t$, then $1\le L\le a$, contradicting $Q(t)\mid 2^L-1$. For $t=1$ the formula is immediate. The gcd formula follows by taking the minimum of the two prime valuations.

## Application to the divisor equation

In [Jaroslav Křížek's A245212 conjecture](https://oeis.org/A245212), put $W(m)=\sum_{d\mid m}d\tau(d)$, where $\tau$ counts divisors and $\sigma$ sums them. For a putative solution $2^k m$ with $k\ge1$ and odd $m>1$, set $x=m\tau(m)-\sigma(m)$ and $y=W(m)-m\tau(m)>0$. [Anmol Sahu's dyadic reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5390) gives $k=\lfloor x/y\rfloor$ and $2^{k+1}(x-ky)=x+y$. It follows that the reduced denominator of $x/y$ is $Q(k+1)$. Thus the distinct prime divisors of that denominator recover $k+1$.

Even with just $y$, discard the prime 2 and the primes $p$ for which $v_p(y)<w_p$. Then $k+1$ must divide the lcm of $d_p$ over the remaining primes. In particular it divides the lcm of $p-1$ over the odd prime divisors of $y$. These are necessary conditions; they do not settle which odd cofactors occur. The multiplicative-order and lifting-the-exponent arguments above use standard number theory. The Lean file includes the elementary reduction from the residual equation, so it can be checked without importing another research submission.

## Lean verification

[MersenneOrderSupportResearch245212.lean](MersenneOrderSupportResearch245212.lean) imports only Mathlib. From the [pinned Formal Conjectures checkout](https://github.com/google-deepmind/formal-conjectures/tree/9097e2f90e66d2f6244209cb1c07f7120d17ec53), run:

```bash
lake env lean /path/to/MersenneOrderSupportResearch245212.lean
```

In namespace `OMA.MersenneOrderSupport245212`, the main declarations are `formula`, `index_of_pos`, `strong_divisibility`, `support_embedding`, `eligible_index` and `residual`. The file also characterizes the exact possible $Q(t)$ at a given index (`recognize`).
