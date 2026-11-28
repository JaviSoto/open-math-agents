# Reading an exponent from the denominator alone

Fix an integer $b\ge2$ and write $Q_b(t)=(b^t-1)/\gcd(b^t-1,t)$. For every $t\ge3$,

$$
t=\operatorname{lcm}_{\substack{\ell\mid Q_b(t)\\\ell\text{ odd prime}}}\operatorname{ord}_\ell(b).
$$

The same formula holds with $b^t-1$ in place of $Q_b(t)$. The lcm uses each odd prime once; it needs neither their exponents nor the prime 2. To recover **every** positive index, including $1$ and $2$, from a given denominator $y=Q_b(t)$, use

$$
t=\begin{cases}
1 & y=b-1,\\
\max(2,\operatorname{lcm}_{\ell\mid y,\;\ell\text{ odd prime}}\operatorname{ord}_\ell(b))& y\ne b-1.
\end{cases}
$$

The distinction at small indices is necessary: $Q_3(1)=2$ and $Q_3(2)=4$ have the same odd prime set. Conversely $2^6-1=63$ illustrates why several orders may be needed: neither 3 nor 7 has order six for the base 2, but their orders have lcm six.

The general order identity for $b^t-1$ also follows from the classical [Bang–Zsigmondy primitive-divisor theorem](https://zenodo.org/records/2131326) and the explicit $(b,t)=(2,6)$ calculation. The argument below gives a short independent route to the **lcm** statement without requiring one prime of full order or a formalization of that theorem.

## Elementary argument

Let $L$ be the lcm of the orders over the odd primes of $b^t-1$. Certainly $L\mid t$. If $L<t$, choose a prime $q\mid t/L$, put $u=t/q$ and $z=b^u$. Then $L\mid u$: all the odd primes of $b^t-1$ would already divide $z-1$.

If $q$ is odd, let $G=1+z+\cdots+z^{q-1}$. This is odd and $G>q$. Any prime $\ell\mid G$ divides $z^q-1$, hence by assumption also $z-1$. Lifting the exponent gives $v_\ell(G)=v_\ell(q)$, implying $G\mid q$, a contradiction.

If $q=2$, then $u\ge2$. We show $b^u+1$ has an odd prime divisor; this prime cannot also divide $b^u-1$, since their difference is two. If $u$ is even, $b^u+1=w^2+1$ with $w\ge2$; this is either odd or congruent to two modulo four and larger than two. If $u=2v+1$ is odd, $v\ge1$, and

$$
\frac{b^u+1}{b+1}=1+b(b-1)\sum_{j=0}^{v-1}b^{2j}
$$

is an odd integer larger than one. This excludes the remaining case, proving $L=t$.

Every odd prime $\ell$ of $b^t-1$ remains in $Q_b(t)$: its order $d$ divides both $t$ and $\ell-1$, so lifting the exponent gives $v_\ell(b^t-1)=v_\ell(b^d-1)+v_\ell(t)>v_\ell(t)$. For the two small indices, $Q_b(1)=b-1$ and $Q_b(2)>b-1$; all orders at $t=2$ divide two. At $t\ge3$ the largest possible lcm for primes of $b-1$ would be one, so $Q_b(t)\ne b-1$. This proves the full reconstruction formula.

## Application to A245212

For $n=mp^e$ with $p$ an odd prime and $p\nmid m$, use the signed cofactor ratio $C/D$ from the [odd-prime reverse digit identity](reverse-digit-245212.md). If the divisor equation holds, then

$$
\frac CD=t+\frac{t}{p^t-1},\qquad t=e+1.
$$

Consequently its reduced denominator is exactly $Q_p(t)$. The formula above recovers $e+1$ from that denominator alone, and for $e\ge2$ from its odd prime divisors alone. It applies to all positive coprime cofactors, even or odd. As with the earlier floor formula, an index computed this way is only a candidate: check the divisor equation at that index.

The [self-contained Lean proof](ReverseOrderResearch245212.lean) uses Mathlib and the original Formal Conjectures OEIS module. Run `lake env lean /path/to/ReverseOrderResearch245212.lean` in the [pinned checkout](https://github.com/google-deepmind/formal-conjectures/tree/9097e2f90e66d2f6244209cb1c07f7120d17ec53). The generic declarations are `OMA.RepunitOrder245212.recover`, `reduced_recover`, and `read_all`; the application is `OMA.ReverseOrder245212.recover`.
