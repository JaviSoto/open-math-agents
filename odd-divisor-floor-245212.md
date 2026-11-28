# How many divisors the odd part of an A245212 exception must have

Write a positive solution to the [original A245212 equality](https://oeis.org/A245212) as \(n=2^k m\), with \(m\) odd. Let \(r\) be the number of distinct primes dividing \(m\) and \(D=\tau(m)\) its number of divisors. Then

\[
   D^2\ge 6^r.
\]

If equality holds, exactly half the primes in \(m\) have exponent one, the other half have exponent two, and
\[
   m\equiv 5^{r/2}\pmod 8 .
\]
Thus the odd part must be 1 modulo 8 when \(r\) is divisible by four, and 5 modulo 8 when \(r\) is 2 modulo four. These conditions are necessary; they give no examples at positive rank.

**A consequence without a rank limit.** Fix a positive rational \(a/b<\sqrt6\) and a constant \(C\) that is a positive integer. Among integers with an odd prime factor and \(D\le C(a/b)^r\), only finitely many solve the equality. Indeed, the two bounds force \(r\le a^2 C^2\); then apply the [explicit height at each rank](fixed-rank-absolute-245212.md). There are also only finitely many solutions with a bounded number of repeated odd prime factors, counted with multiplicity: \(r\le2\sum_{p^e\parallel m}(e-1)\).

**Proof.** For each exponent \(e\ge1\) set \(v=\nu_2(e+2)\). [DomTheDeveloper's exponent obstruction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1376) gives \(\sum v\ge r\). The local inequalities \(4\cdot3^v\le2^v(e+1)^2\) and \(v\le2(e-1)\) now give the two bounds. Equality in the product forces equality at every prime. Then \(2^v\mid4\), and checking \(v=0,1,2\) leaves just \(e=1,2\). Comparing powers of three in \(D^2=6^r\) gives equally many of each.

For the residue condition, call the primes occurring once \(P\) and the squared ones \(Q\), both of size \(s=r/2\). With \(W(n)=\sum_{d\mid n}d\tau(d)\), cancel \(2^s\) from the original balance \(W(n)+\sigma(n)=2n\tau(n)\). The resulting equality implies \(W(m)/2^s\equiv\sigma(m)/2^s\pmod4\), including when \(k=0\). For each \(q\in Q\), \(W(q^2)/2\) and \(\sigma(q^2)\) are equal odd units modulo four. Cancelling them gives \(\prod_{p\in P}(p+1)/2\equiv 3^s\pmod4\). In particular every singly occurring prime is 1 modulo 4. On odd units the map \(x\mapsto2x-1\) from residues modulo four to residues modulo eight preserves multiplication. Applying it to that product, and using \(q^2\equiv1\pmod8\), gives the claimed residue.

**Replay.** In Formal Conjectures at commit `9097e2f90e66d2f6244209cb1c07f7120d17ec53`, run `lake env lean /path/to/SparseDivisorCriticalResearch245212.lean` on the [standalone file](SparseDivisorCriticalResearch245212.lean). The [116-source archive](sparse-divisor-critical-245212.tar.gz) also contains a manifest and parallel replay script. The original-input declarations are `OddDivisorFloor245212.floor`, `SparseDivisorHeight245212.whole`, `SparseDivisorHeight245212.few_repeated` and `CriticalResidueInput245212.original`, all in the `OMA` namespace.
