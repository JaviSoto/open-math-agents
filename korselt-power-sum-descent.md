# Prime-factor descent for two of Meštrović’s power-sum conjectures

Write $S_e(n)=\sum_{i=1}^{n-1} i^e$. Suppose $p$ is a prime factor of $n$ such that $p-1\mid n-1$. Then:

1. If $n>1$ and $n^4\mid S_{n-2}(n)$, then $p^4\mid S_{p-2}(p)$.
2. If $n\ge5$, $n\equiv1\pmod4$ and $n^3\mid S_{(n-1)/2}(n)$, then $p\equiv1\pmod4$ and $p^3\mid S_{(p-1)/2}(p)$.

These are [Meštrović’s Conjectures 13 and 16](https://cs.uwaterloo.ca/journals/JIS/VOL17/Mestrovic/mes4.pdf), respectively. One prime factor satisfying the displayed divisibilities suffices; $n$ need not be squarefree. For a least counterexample to either conjecture, every prime divisor is either $n$ itself or fails $p-1\mid n-1$. In particular, the least counterexample cannot be a composite prime power or a Carmichael number.

There are also exclusions *without any upper bound on $n$*. Every $p^a$ with $p\le10^{11}$ and $a\ge1$ is excluded from Conjecture 13 by the [quartic prime computation](https://github.com/JaviSoto/open-math-agents/blob/b90d02b716198c7703a21a6e539e5bc3f4f931d8/quartic-bernoulli-284760.md). For Conjecture 16, [van der Poorten, te Riele and Williams](https://doi.org/10.1090/S0025-5718-02-01527-2) excluded ordinary Ankeny–Artin–Chowla exceptions through $2\cdot10^{11}$, a necessary condition at prime inputs. The same exclusions apply to every Carmichael number with at least one prime factor in the corresponding range, and to every other $n$ with even one such factor $p$ satisfying $p-1\mid n-1$.

## Why a prime factor inherits the congruence

Use the [quartic criterion](https://github.com/JaviSoto/open-math-agents/blob/b90d02b716198c7703a21a6e539e5bc3f4f931d8/quartic-bernoulli-284760.md) and the [half-exponent criterion](https://github.com/JaviSoto/open-math-agents/blob/17eb35e32a7ab01225a520fdc62ccedca61045db/half-square-mestrovic-16.md). For the relevant odd $n$, each says $n^2\mid\operatorname{num}B_e$, with $e=n-3$ or $(n-1)/2$ respectively. The even-power-sum criterion used here was proved by [Kellner, Proposition 8.5](https://arxiv.org/pdf/math/0409223#page=36).

In the quartic case put $t=p-3$. Since $n\equiv p$ both modulo $p$ and modulo $p-1$, we have $e\equiv t\pmod{p(p-1)}$. The case $p=3$ is excluded by von Staudt–Clausen. For $p=5$, the congruence gives $e\equiv2\pmod4$, and $B_2=1/6$ excludes this row (the formal proof uses a finite-sum version).

In the half-exponent case, write $n-1=k(p-1)$. The integer $k$ must be odd: otherwise $p-1\mid e$, contradicting $p\mid\operatorname{num}B_e$ by von Staudt–Clausen. Since $e$ is even, $t=(p-1)/2$ is even too; this gives $p\equiv1\pmod4$. We have $e\equiv t\pmod{p-1}$ because $k$ is odd, and $2e\equiv2t\equiv-1\pmod p$. Hence again $e\equiv t\pmod{p(p-1)}$. The small prime cases are excluded as above.

The order-two Kummer congruence now carries $p^2\mid\operatorname{num}B_e$ to $p^2\mid\operatorname{num}B_t$, because the indices are prime to $p$ and not divisible by $p-1$. The corresponding criterion at $p$ gives the original power sum, with its required exponent.

The [standalone Lean proof](PrimePowerMestrovicOriginal.lean) proves the transfer at every order $a$ under its stated unit and index bounds. It uses only finite sums: for $m=p^a$, permute residues by a primitive residue $g$ mod $p$, and write $gi=r_i+mc_i$. Modulo $m^2$ the binomial expansion gives

$$
(g^e-1)\sum_{i=0}^{m-1} i^e\equiv e m\sum_{i=0}^{m-1} c_i r_i^{e-1}\pmod{m^2}.
$$

The right-hand carry sum without its factor $e$ is unchanged modulo $m^2$ if $e$ is replaced by $t\equiv e\pmod{\varphi(m)}$ and both indices exceed $a$. Euler’s theorem handles the unit residues; the others vanish modulo $m$ after raising to either lowered exponent. The even-power criterion translates Bernoulli divisibility into the vanishing of the full sum modulo $m^2$. Both $e$ and $g^t-1$ are units at $p$, so vanishing transfers from $e$ to $t$.

## A restriction on multiplicities within a fixed irregular branch

There is a further consequence of [Kellner’s Theorem 4.10](https://arxiv.org/pdf/math/0409223#page=16). Fix a nonsingular irregular pair $(p,\ell)$, meaning $\Delta(p,\ell)\ne0$. Among all solutions of either one of the two congruences whose Bernoulli index is $\ell\bmod(p-1)$, **at most one exact exponent $a\ge2$ can occur in $p^a\parallel n$**. The two conjectures are treated separately.

Indeed, suppose $p^a\parallel n$ and $p^b\parallel n'$ with $2\le a<b$. Then $v_p(n-n')=a$. The Bernoulli indices $e,e'$ differ by $n-n'$ in the quartic case and by $(n-n')/2$ in the other, so $v_p(e-e')=a$. The normalized interpolation values $(1-p^{e-1})B_e/e$ and $(1-p^{e'-1})B_{e'}/e'$ are both divisible by $p^{2a}$ since the indices are units. On the indicated branch, Kellner’s isometry gives their difference valuation exactly $1+v_p(e-e')=1+a<2a$, a contradiction.

Consequently, if all irregular pairs above a finite prime set $P$ are nonsingular, each conjecture has at most $\prod_{p\in P}(2+i(p))$ solutions supported on $P$, where $i(p)$ is the number of irregular indices for $p$. The choices counted are multiplicity zero, multiplicity one, or at most one higher multiplicity per branch. This last section uses the cited isometry and is not included in the Lean proof. Nonsingularity is a hypothesis here; the two descent theorems do not require it.

To replay the file, run `lake env lean /absolute/path/to/PrimePowerMestrovicOriginal.lean` in the LeftToSolve pinned Mathlib project. The final declarations are `OMA.PrimePowerMestrovic.transfer`, `quartic_descent`, `half_descent`, `quartic_prime_power` and `half_prime_power` in that namespace. Both original conjectures remain open.
