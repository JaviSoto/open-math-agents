# A prime factor below 59 rules out a counterexample to Meštrović’s power-sum conjecture

Write $S_e(t)=\sum_{i=1}^{t-1}i^e$. Meštrović asks whether $n^4\nmid S_{n-2}(n)$ for every $n>1$ ([Conjecture 2.11](https://arxiv.org/abs/1211.4570); [OEIS A284760](https://oeis.org/A284760)). We prove this for **every odd $n$ divisible by any prime below 59**. No bound is placed on $n$, on the multiplicity of the prime, or on the other prime factors. The unrestricted conjecture remains open.

The proof covers the first irregular prime, 37, where the simpler obstruction modulo $37^2$ has an exception. It also gives a divisibility test at every prime-power divisor of an odd counterexample.

## Passing to a prime power

For odd $n\ge5$, put $k=n-2$ and $e=n-3$. Reflect each summand about $n/2$. Expansion through second order modulo $n^3$ gives

$$2S_k(n)\equiv nkS_e(n)\pmod{n^3}.$$

The quadratic correction vanishes because $k-2$ is odd and $n\mid S_{k-2}(n)$. Since $\gcd(k,n)=1$, a counterexample must satisfy $n^2\mid S_e(n)$.

**Prime-power test.** If $n$ is an odd counterexample and $P=p^b\mid n$, with $p\ge5$ prime and $b\ge1$, then $P^2\mid S_e(P)$.

To see the role of the multiplicity, let $P\mid m$ and expand $(i+mj)^e$, for $0\le i<m$ and $0\le j<p$. Modulo $pPm$, only the constant, linear and quadratic terms can survive. The linear correction is divisible by $pPm$ because $p\mid\sum j$ and $m\mid S_{e-1}(m)$; the quadratic correction vanishes because $p\mid\sum j^2$ and $P\mid m$. Thus $S_e(pm)\equiv pS_e(m)\pmod{pPm}$. Remove each extra factor of $p$ by this congruence. At $n'=Pu$ with $p\nmid u$, expansion over $u$ blocks gives $S_e(Pu)\equiv uS_e(P)\pmod{P^2}$, and $u$ cancels.

## The exception at 37

For $b=1$, Euler’s theorem reduces $e$ modulo $p(p-1)$. For each prime $5\le p<59$, check the even exponents $r<p(p-1)$ with $p\mid r+3$. The only pair with $p^2\mid S_r(p)$ is $(p,r)=(37,1292)$; in particular $r\equiv32\pmod{36}$. A factor of $3$ already violates the earlier obstruction $p-1\mid n-3$.

There are two cases for 37.

- **If $37^2\mid n$**, write $e=47912+49284j$ using $e\equiv-3\pmod{1369}$ and $e\equiv32\pmod{36}$. The prime-power test with $P=1369$ requires $37^4\mid S_e(1369)$. In fact $S_e(1369)\equiv607836=12\cdot37^3\pmod{37^4}$ for every $j\ge0$. Two computed rows, at $j=0,1$, suffice: for each unit $i$, $i^{49284}-1$ is divisible by $37^2$, so its square vanishes modulo $37^4$. Each summand is therefore affine in $j$; nonunits contribute zero.
- **If $n=37m$ and $37\nmid m$**, then $k=1293+1332j$. The same affine argument, now using $i^{1332}\equiv1\pmod{37^2}$ for $1\le i<37$, gives the following four residues modulo $37^4$ from two rows per exponent:

| Sum | Residue modulo $37^4$ |
| --- | ---: |
| $S_k(37)$ | 1,266,325 |
| $37S_{k-1}(37)$ | 607,836 |
| $37^2 S_{k-2}(37)$ | 0 |
| $37^3 S_{k-3}(37)$ | 0 |

Expand $(37t+i)^k$ through degree three on each block. Because $607836k\equiv2\cdot1266325\pmod{37^4}$, the $t$-th block sums to $1266325(1+2t)$. Summing the first $m$ odd integers gives

$$S_k(37m)\equiv25\cdot37^3m^2\pmod{37^4}.$$

This excludes $37^4\mid S_k(n)$ when $37\nmid m$ and finishes the proof.

## Reproduce

The [standalone Lean file](All37Research284760.lean) imports only mathlib. From the project's pinned Lean checkout run `lake env lean /absolute/path/to/All37Research284760.lean`. Its final three declarations are `OMA.PowerHierarchy284760.power_test`, `OMA.First37Original284760.original`, and `OMA.First37Original284760.low_factor`. All three use only the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`. The finite arithmetic is checked by Lean’s kernel.

Meštrović’s paper supplies the conjecture and the reflection congruence. The [parent case split](https://github.com/lefttosolve2/open-math-agents/pull/24645) is by @adanthar. The [simple-prime](https://github.com/lefttosolve2/open-math-agents/pull/29249) and [repeated-prime](https://github.com/lefttosolve2/open-math-agents/pull/29214) cases and the [second-order reduction](https://github.com/lefttosolve2/open-math-agents/pull/29504) were submitted under @JaviSoto. This note and the Lean proof were prepared for Javi Soto using OpenAI Codex.
