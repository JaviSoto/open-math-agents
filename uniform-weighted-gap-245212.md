# A uniform one-sided gap for the weighted divisor sum

Put \(W(h)=\sum_{d\mid h}d\tau(d)\), \(M=h\tau(h)\). For every \(r\) there is an explicit polynomial \(P_r\) with nonnegative integer coefficients with the following property. Take any \(h\ge1\) with at most \(r\) distinct prime factors. Let \(x\) bound \(V\) and every exponent length \(1+v_p(h)\) for \(p\mid h\). Then for nonnegative integers \(U,V\),

\[
       R=UM-VW(h)>0\quad\Longrightarrow\quad M\le P_r(x)R.
\]

There is no bound on the primes of \(h\), and the polynomial is independent of the numerator \(U\). For \(V>0\) this gives a lower bound of \(1/(VP_r(x))\) for the distance from \(W(h)/M\) to a rational \(U/V\) strictly above it. The direction is essential to the proof.

## How the prime powers disappear

For positive integers \(z_i\), first consider \(R=U\prod z_i-V\prod(g_i z_i+1)>0\), with all coefficients nonnegative integers. Write \(A=V\prod(g_i+1)\). The integer leading coefficient \(U-V\prod g_i\) is positive. If every \(z_i\ge2(A+1)\), the sum of the lower-order terms is at most half the leading monomial \(\prod z_i\). Otherwise, absorb a small \(z_i\) and \(g_i z_i+1\) into the two coefficients and apply induction. This proves \(\prod z_i\le C(d,A)R\), where \(d\) is the number of coordinates, \(C(0,A)=1\), and \(C(d+1,A)=2(A+1)C(d,2(A+1)^2)\).

Use this with \(z=p^e\) and the exact identity
\[
 (p-1)^2 W(p^e)=p\big((e+1)(p-1)-1\big)p^e+1.
\]
When the prime bases are bounded, clearing denominators now costs only a polynomial in the base and exponent-length bounds at fixed rank. For large bases, each factor \(W(p^e)/((e+1)p^e)\) lies between 1 and \(p/(p-1)\). Removing a factor leaves the remaining product strictly below the same rational target. Induct on the rank: if the previous reciprocal-gap bound is \(K\), then restoring a factor with \(p-1>2KV2^{r-1}\) consumes at most half that gap. Otherwise all bases are small enough to use the cleared-denominator argument. Summing the resulting polynomials through rank \(r\) gives \(P_r\).

## Application to a mixed equality

Let \(H=2h\tau(h), A=W(h), S=\sigma(h),u=q-1\), with \(q\ge2\) and \(B,C\) positive. Suppose
\[
  HBCu^2=q\{AC(Bu-1)+Su\},\qquad CA<uS.
\]
Then \(B\) is bounded by another explicitly defined polynomial in \(\lfloor\log_2 h\rfloor+2\) depending only on the number of prime factors of \(h\). In particular, if \(h\le (B+1)^D\), there is an absolute bound for \(B\) depending only on \(r,D\). No bound is needed on \(q\) or \(C\).

Indeed \(E=uH-qA\) and \(\Delta=H-A\) are positive; the equality gives \(BE\le qH\) and \(q\Delta=E+H\). The one-sided gap bounds apply to \(\Delta\) with \(V=1\) and to \(E\) with \(V=q\). When \(q\) is large relative to the first bound, the identity for \(\Delta\) bounds \(qH/E\) directly. In the other case \(q\) is already polynomially bounded and the second estimate applies. The asserted absolute bound then follows from exponential growth against a polynomial in \(\log h\).

## Check

The [standalone proof](ArbitraryMixedFiniteResearch245212.lean) checks in the Formal Conjectures checkout pinned at 9097e2f90e66d2f6244209cb1c07f7120d17ec53 with **lake env lean /path/to/ArbitraryMixedFiniteResearch245212.lean**. The main declarations are OMA.WeightedGapPolynomial245212.original, OMA.ArbitraryMixedGap245212.mixed, and OMA.ArbitraryMixedFinite245212.bounded. The [28-module source archive](arbitrary-mixed-gap-245212.tar.gz) also includes a hash-checking parallel replay script. These results provide bounds for a step in the A245212 argument; they do not exclude every counterexample to the original conjecture.
