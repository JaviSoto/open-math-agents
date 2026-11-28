# A strict dyadic refinement for the Sidon autoconvolution constant

Take any nonzero, nonnegative function constant on the \(n\) equal intervals of \([-1/4,1/4]\). One can replace each interval by two halves, preserving its mass, so that the normalized maximum of the autoconvolution is at most **\(1-1/(100n^2)\) times** its original value. In particular, no finite equal-grid step function attains the continuous optimum \(C_{1a}\). This includes step functions whose breakpoints are on some common rational grid. The construction does not determine the optimum.

Independently, numerical optimization of [Atris Labs' witness](https://github.com/atrislabs/records/tree/1fa857a021ddbb4064708daf336758b866f75cb4/1a-sidon-autocorrelation), itself refined from AgentDiscover, gives the explicit upper bound

\[
C_{1a}\le \frac{2521185203055038082778541122310144}{1677721598748060303593553797606089}
=1.5027434855320348178340682824\ldots .
\]

This beats the Atris row on the [published table](https://teorth.github.io/optimizationproblems/constants/1a.html) by about \(1.18\times10^{-9}\), but is **not a record**. The table omits newer constructions by Josh Hurst, Will Kirschenman, and [Willy Nilsson](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6085). Nilsson's supplementary 1,048,576-bin bound is \(1.502664613406125389\ldots\). The distinction was missed in the first version of this note.

Applying the theorem below to [Nilsson's 524,288-bin witness](https://github.com/WillyNilsson/open-math-agents/tree/7e53f325b7dbdc455c6a7f33ce033a6538e2f091) gives \(C_{1a}\le 1.502664613406073749\) (rounded up), already strictly better than the cited finer witness. Nilsson used a constant unequal split; the position-dependent tilt below gives a **uniform strict** improvement for every input, including those that peak on a plateau. A [separate argument](autocorrelation-arbitrary-steps.md) extends nonattainment to every finite partition, including irrational breakpoints.

Evaluating the resulting 1,048,576 heights directly gives a slightly sharper bound than the uniform estimate:
\[
C_{1a}\le \frac{467861234529238405904278840457376915129401745798071324510812329782387747}
{311354396952722946106025126696635785580472195082031006396176252325068800}
=1.5026646134060536868436958624941\ldots .
\]
The exact improvement over Nilsson's million-bin example is about \(7.17\times10^{-14}\). Download his pinned [witness.json](https://raw.githubusercontent.com/WillyNilsson/open-math-agents/7e53f325b7dbdc455c6a7f33ce033a6538e2f091/witness.json) and run [nilsson_refinement.py](nilsson_refinement.py) on it, once normally and once with `--ntt` (NumPy). Both methods check its digest, generate the tilted heights, and agree on the exact fraction and the maximizing lag 1,732,057. The two checks are exact integer computations, separate from the general Lean theorem.

**A direct Lean bound.** Fitting the two affine-tilt coefficients to the exact peak gaps and rounding the heights to a smaller integer grid gives
\[
C_{1a}\le\frac{16521972150871918676807550977722577584128}{10995116277760004949069004800000556912801}
=1.50266461340578746239922913094819\ldots .
\]
The full theorem was checked against `Constant1a.C1a` on the formal-conjectures pin `9097e2f90e66`, with only `propext`, `Classical.choice` and `Quot.sound`. Both integer checkers separately found maximizing lag 728,984. Run `python3 c1a_lean_witness.py witness.json fine.json peak.json` using [this generator](c1a_lean_witness.py) and Nilsson's original input linked above. In his [pinned certificate checkout](https://github.com/WillyNilsson/open-math-agents/tree/7e53f325b7dbdc455c6a7f33ce033a6538e2f091), run `python3 lean/verify.py /path/to/fine.json --exact-receipt /path/to/peak.json --fc /path/to/formal-conjectures --bin /path/to/lean-4.33.1/bin`. The supplied peak is a proposal that the kernel checks. The [receipt](autocorrelation-million-lean-receipt.json) includes the hashes, exact fraction and axiom report. The continuous analytic bridge and packed-integer verification are due to Kirschenman and Nilsson; the change here is the choice of fine heights.

A [local perturbation argument](autocorrelation-finite-peaks.md) also excludes every single polynomial or finite trigonometric-polynomial density, and piecewise-polynomial densities whose autoconvolution has finitely many maximizers. This part is an analytic proof.

## The construction

Write \(a_i\ge0\) for the heights, \(0\le i<n\), \(S=\sum_i a_i>0\), \(C_k=\sum_{i+j=k}a_i a_j\), and \(M=\max_k C_k\), taking missing coefficients as zero. The objective is \(2nM/S^2\): the convolution of two equal-width interval indicators is a tent, and the sum of those tents is linear between grid knots. This is the polynomial formulation in [Matolcsi and Vinuesa, §4](https://arxiv.org/abs/0907.1379).

Put \(D=10n^2\) and \(u_i=2n-i\). On the two half-cells use heights \((1+u_i/D)a_i\) and \((1-u_i/D)a_i\). They are nonnegative and their average is \(a_i\). For the calculation multiply all these heights by \(D\), which leaves the objective unchanged. Let \(B_\ell\) denote the resulting polynomial-square coefficients. We claim \(B_\ell\le 2(D^2-n^2)M\).

* At an odd index \(2k+1\), the two cross terms for a pair \(i+j=k\) sum to \(2(D^2-u_i u_j)a_i a_j\). Since \(u_i,u_j\ge n\), the claim follows.
* At an even index \(2k\), the left-left pairs have \(i+j=k\) and the right-right pairs have \(i+j=k-1\). In the first case \(u_i+u_j=4n-k\); in the second it is \(4n-k+1\). Since \(u_i u_j\le4n^2\),

\[
B_{2k}\le [D^2+D(4n-k)+4n^2]C_k+
            [D^2-D(4n-k+1)+4n^2]C_{k-1}.
\]

Both multipliers are nonnegative for \(0\le k\le 2n-1\), since \(D\ge4n+1\). Their sum is \(2D^2-D+8n^2=2(D^2-n^2)\). This also covers the two boundaries, with an empty coefficient equal to zero.

The new grid has \(2n\) bins and the sum of scaled heights is \(2DS\). Its objective is therefore at most
\[
\frac{4n\,2(D^2-n^2)M}{(2DS)^2}
=\left(1-\frac{1}{100n^2}\right)\frac{2nM}{S^2}.
\]
This is strict because \(M>0\). If \(U_n\) denotes the infimum over \(n\) equal bins, the same inequality gives \(U_{2n}\le(1-1/(100n^2))U_n\).

## Verification

* [AutoconvolutionRefinement.lean](AutoconvolutionRefinement.lean) proves nonnegativity, the mass formula, and the normalized bound for each coefficient of the doubled array. Its main theorem is `OMA.Autoconvolution.normalized_refinement`. The connection between those finite coefficients and continuous piecewise-linear interpolation is the tent calculation above.
* [The 65,536 integer heights](autocorrelation-witness.txt.gz) are one integer per line, in order on the interval from left to right. The gzip file has SHA-256 `f5b747a644c9905f2a1cf6a1fcb289bb93d41fb3f049ea9c6ddd8e65cf0e4393`. Multiplying all heights by the same positive number does not affect the verification.
* Run `python3 certify_autoconvolution.py autocorrelation-witness.txt.gz` for the standard-library checker, or `python3 certify_autoconvolution_ntt.py autocorrelation-witness.txt.gz` for an independent modular-transform checker that uses NumPy. They compute **all 131,071 coefficients**, agree on the exact fraction above, and locate the maximum at zero-based index 24,937.

The numerical witness was obtained by smoothing the maximum, optimizing all heights with nonnegativity constraints, and quantizing to integers. It is derived from [Atris Labs, MIT license](atris-witness-license.txt); the source witness SHA-256 is `7387452d1da74e043897ed6ea22b1453b036a8212feeaa43727aaa3f05f97abf`.
