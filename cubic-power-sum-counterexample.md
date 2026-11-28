# A composite counterexample to Meštrović's cubic power-sum conjecture

Set $n=564458189=5309\cdot106321$ and $e=n-2=564458187$.
Write $S=\sum_{i=1}^{n-1} i^e$. The exact residue is

    S mod n^4 = 23513011 * n^3 = 4228667920943628092530317371454959.

Thus $n^3\mid S$ even though $n$ is composite. This refutes Conjecture 12
in [R. Meštrović, Journal of Integer Sequences 17 (2014), article 14.8.4](https://cs.uwaterloo.ca/journals/JIS/VOL17/Mestrovic/mes4.pdf)
and the equivalent conjecture recorded in [OEIS A284759](https://oeis.org/A284759).
The same example does **not** refute the fourth-power conjecture (Conjecture 13).

## Reproduce the arithmetic

Run `python3 mestrovic_power_witness.py --test 5309 106321` (Python 3.8+,
standard library). It first compares the algorithm with direct summation
on small controls. The witness calculation needs no irregular-prime table.
For either factor $p$, put $u=n/p$ and write $i=x+pj$, with
$0\le x<p$ and $0\le j<u$. Including the term at zero changes nothing.
Expand by the binomial theorem, discarding terms with $p^4$ as a factor:

    S ≡ Σ[k=0..3] binom(e,k) p^k (Σ[j=0..u−1] j^k) (Σ[x=0..p−1] x^(e−k))  (mod p^4).

These are the four moments of the block indices: $u$, $T=u(u-1)/2$,
$T(2u-1)/3$, and $T^2$. Modular exponentiation computes the remaining
short sums. This gives $676657241640338$ modulo $5309^4$ and
$117787976151460234644$ modulo $106321^4$. The Chinese remainder
theorem gives the unique residue modulo $n^4$ above.
