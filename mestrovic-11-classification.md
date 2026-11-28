# Which integers satisfy Meštrović’s two Bernoulli congruences?

Write $S_j(n)=\sum_{a=1}^{n-1}a^j$, and let $B_j$ denote the Bernoulli numbers with $B_1=-1/2$. For every $n\ge2$, the two congruences in [Meštrović’s Conjecture 11](https://cs.uwaterloo.ca/journals/JIS/VOL17/Mestrovic/mes4.pdf#page=7) have the following exact criteria:

| Congruence | Necessary and sufficient condition |
|---|---|
| $S_n(n)\equiv n^3B_{n-1}/2\pmod{n^5}$ | $n$ is odd, and $p-1\nmid n-3$ for every prime $p\mid n$. |
| $S_{n-1}(n)\equiv nB_{n-1}\pmod{n^4}$ | $n$ is odd, and $n\mid\operatorname{num}B_{n-3}$ (for $n\ge3$; $n=2$ fails). |

A rational congruence means divisibility of the reduced numerator of the difference. The second congruence implies the first, and it is equivalent to the cubic condition $n^3\mid S_{n-2}(n)$ in Conjecture 12. For instance, both hold at [the squarefree composite $409407431$](https://github.com/JaviSoto/open-math-agents/blob/787d3410649778abb01731dc169b2dd7bb1c67c2/mestrovic-conjecture-11.md). The first congruence alone holds on a set of natural density greater than $2/7$.

## The local test

Direct calculation handles $2\le n\le6$. If $n\ge4$ is even, $B_{n-1}=0$. A complete even-power sum of positive degree is nonzero modulo even $n$: pair the two halves when $4\mid n$ and descend; when $n/2$ is odd, count the odd terms modulo $2$. For the second congruence, reflection $a\mapsto n-a$ gives

$$2S_{n-1}(n)\equiv n(n-1)S_{n-2}(n)\pmod{n^2}.$$

Thus $n^2\mid S_{n-1}(n)$ would already contradict the even-power obstruction.

Now let $n\ge7$ be odd, $e=n-3$, $c=(n-1)(n-2)$ and $p\mid n$ prime. Write $\mathbb Z_{(p)}$ for the rationals with denominator prime to $p$. Let $F$ and $G$ denote the differences on the first and second lines, respectively. Faulhaber's formula, the vanishing of the odd Bernoulli numbers beyond $B_1$, and the $p$-integrality of every $pB_j$ give

$$24F/n^5-cB_e\in\mathbb Z_{(p)},\qquad
G/n^4-\binom n5 B_{e-2}-\frac{c}{6}\frac{B_e}{n}\in\mathbb Z_{(p)}.$$

Here the omitted terms have at least one factor of $n$ left after division. The coefficient $c$ is a $p$-unit. If $F/n^5$ is $p$-integral, $B_e$ is $p$-integral, which by von Staudt–Clausen means $p-1\nmid e$. Conversely, these conditions at all primes dividing $n$ exclude $3$; at the other odd primes $24$ is a unit and the calculation gives the first congruence.

For $p\ne5$, the identity $5\binom n5=n\binom{n-1}4$ shows that $\binom n5 B_{e-2}$ is $p$-integral. Hence integrality of $G/n^4$ implies that of $B_e/n$, also for $p=3$ after multiplying by $6$. In particular $3$ cannot divide a solution. For the converse, suppose $n\mid\operatorname{num} B_e$. Then no $p\mid n$ has $p-1\mid e$. Nor can $e\equiv2\pmod{p-1}$ at $p\ge5$: the first Kummer congruence would give $B_e/e\equiv B_2/2=1/12\pmod p$, whereas $p\nmid e$. (The proof file verifies this step by doubling the residues in the corresponding power sum.) Thus $B_{e-2}$ is $p$-integral, $6$ is a $p$-unit, and the formula for $G$ proves the converse.

### Why $5$ cannot cancel the two terms

Suppose $n=5m$ and $G/n^4$ is $5$-integral. Multiplying its expansion by $6n$ first shows $B_e$ is $5$-integral; therefore $e\equiv2\pmod4$. Since $e=n-3\equiv2\pmod5$, we have $e\equiv2\pmod{20}$. Euler's theorem gives $S_e(5)\equiv1^2+2^2+3^2+4^2=30\pmod{25}$. Faulhaber's formula at $5$ yields $S_e(5)\equiv 5B_e\pmod{25}$, so $B_e\equiv1\pmod5$. Also $4\mid e-2$, so $5B_{e-2}\equiv-1\pmod5$. Lucas's theorem gives $\binom{5m}5\equiv m\pmod5$. Reducing the expression for $6nG/n^4$ modulo $5$ now gives

$$0\equiv cB_e+6m\binom n5(5B_{e-2})\equiv 2-m^2\pmod5,$$

which is impossible.

Thus $G/n^4$ is $p$-integral at every $p\mid n$ exactly when $B_e/n$ is. This proves the second line, including the full multiplicities in $n$. Since $n\mid\operatorname{num}B_e$ forces $B_e$ to be $p$-integral for each $p\mid n$, the second line implies the first. Reflection to cubic order and Faulhaber's formula identify the second line with $n^3\mid S_{n-2}(n)$.

## More than two sevenths of the integers

For an odd prime $p$, its forbidden condition on odd $n$ is a single class, $n\equiv3p\pmod{p(p-1)}$. Let $D_y$ be the periodic set obtained by testing all $p\le y$ on odd $n$. For $y\ge3$, every member of $D_y$ is coprime to $3$. If an untested $p$ rules out $n\in D_y$, write $n=pt$. Then $t\equiv3\pmod{p-1}$, and $t\ne3$, so $t\ge p+2$ for $p\ge5$. For $n\le X$ there are therefore at most $\sqrt X$ possible untested primes. Their classes contain at most

$$X\sum_{p>y}\frac1{p(p-1)}+O(\sqrt X)\le X/\lfloor y\rfloor+O(\sqrt X)$$

integers up to $X$. The natural density exists and is the limit of the decreasing densities of $D_y$.

Take $y=17$. Primes $7$ and $13$ impose nothing once multiples of $3$ are excluded. Exactly $13,106$ out of $44,880$ residues survive the remaining conditions (the period is $\operatorname{lcm}(6,20,110,272)$). The count can be reproduced directly:

```python
sum(n % 2 == 1 and all(n % (p*(p-1)) != 3*p % (p*(p-1))
                        for p in (3, 5, 11, 17)) for n in range(44880))
```

Any relevant prime $p>17$ must be $6j+5$, $j\ge3$: if $p\equiv1\pmod3$, its forbidden class consists of multiples of $3$. For $p=6j+5$, exactly two thirds of the forbidden class are coprime to $3$. The preceding uniform tail bound justifies summing those densities. Since $(6j+5)(6j+4)>36j(j+1)$,

$$\operatorname{dens}(D)\ \ge\ \frac{13106}{44880}
-\frac23\sum_{j\ge3}\frac1{36j(j+1)}
=\frac{173191}{605880}
=\frac27+\frac{577}{4241160}.$$

## Proof files

[ClassifyElevenOriginal.lean](ClassifyElevenOriginal.lean) contains both equivalences, the implication between them, and the original cubic equivalence for all $n\ge2$. It imports only Mathlib. From the LeftToSolve pinned checkout run `lake env lean /absolute/path/to/ClassifyElevenOriginal.lean`. The density argument above is a separate elementary deduction from the first equivalence.
