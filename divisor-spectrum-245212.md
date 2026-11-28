# The first possible divisor counts, at any odd-prime rank

For a positive A245212 solution write \(n=2^k m\) with \(m\) odd, and let \(r=\omega(m)\). The [divisor floor](odd-divisor-floor-245212.md) says that the ratio \(R=\tau(m)^2/6^r\) is at least one. It cannot take arbitrary rational values just above one. **At every ceiling there are only finitely many candidate ratios, even when the number of primes is unrestricted.** For example, the entire list at or below four is

\[
  1,\quad 3/2,\quad 9/4,\quad 27/8,\quad 98/27,\quad 4.
\]

Each ratio on the list occurs for some list of positive exponents obeying [the necessary divisibility condition](exponent-parity-245212.md). This does **not** assert that the full divisor equation has a corresponding solution. The Lean computation enumerates the exact possibilities allowed by that condition, rather than searching integers up to some height.

**Why the list is finite.** Write \(v(e)=\nu_2(e+2)\), \(V=\sum v(e)\), and \(d=V-r\ge0\). Then
\[
 R=(3/2)^d\prod_{p^e\parallel m}L(e),
 \qquad L(e)=\frac{2^{v(e)}(e+1)^2}{4\,3^{v(e)}}.
\]
Exponents one and two contribute factors of one. All larger exponents contribute at least \(98/27\), achieved at six, and satisfy \(e<4L(e)\). Below any given ceiling \(X\), only finitely many exponents \(e\ge3\) can occur, and only a bounded number of factors greater than one can be multiplied. Conversely, adjoining an exponent two realizes the generator \(3/2\). To realize \(L(e)\) at zero excess, adjoin \(e\) with one exponent two if \(v(e)=0\), or with \(v(e)-1\) exponents one otherwise. Concatenating such profiles realizes the entire computed list.

**What the first two levels say about the primes.** At \(R=1\) the odd part satisfies \(m\equiv5^{r/2}\pmod8\). At \(R=3/2\) and even \(n\), precisely one of the singly occurring primes is 3 modulo 8; the others are all 1 modulo 4. Consequently \(m\equiv3\pmod4\). Below \(98/27\), the only levels at even rank are 1 and \(9/4\), and at odd rank \(3/2\) and \(27/8\).

**Replay.** Compile the [standalone Lean file](DivisorSpectrumResearch245212.lean) with `lake env lean /path/to/DivisorSpectrumResearch245212.lean` in Formal Conjectures at `9097e2f90e66d2f6244209cb1c07f7120d17ec53`. Or use the [121-module source archive](divisor-spectrum-245212.tar.gz). The original-input theorem is `OMA.DivisorFloorStabilitySpectrum245212.original`. The exact profile characterization is `OMA.DivisorFloorStabilitySpectrumExact245212.spectrum_iff`. To calculate a list, evaluate `(OMA.DivisorFloorStabilitySpectrum245212.spectrum (4 : ℚ)).sort (· ≤ ·)`.
