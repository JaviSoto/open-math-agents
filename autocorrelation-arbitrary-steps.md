# No finite step function attains the Sidon autoconvolution optimum

Let \(f\ge0\), with \(\int f>0\), be constant almost everywhere on finitely many intervals of **arbitrary real lengths**, supported in \([0,1]\). Write \(F=f*f\), \(M=\max F\). There exists another nonnegative finite step function on \([0,1]\) with the same integral and a strictly smaller maximum of its autoconvolution. Rescaling the support gives the assertion for [Tao's \(C_{1a}\)](https://teorth.github.io/optimizationproblems/constants/1a.html).

The [equal-grid theorem](autocorrelation-refinement.md) gives an explicit gain for rationally aligned data. Density of rational step functions alone does **not** give strictness for irrational breakpoints: the approximation error can exceed the gain. We compare the *change* caused by the perturbation instead.

### Round the breakpoints, preserving their addition relations

Extend \(f\) by zero. List the finitely many jump positions \(b\), including 0 and 1 as endpoints, with jump sizes \(d_b\) (possibly zero at an endpoint). There are integers \(n\to\infty\) such that \(\eta_n=\max_b\operatorname{dist}(nb,\mathbb Z)\to0\), by simultaneous approximation: pigeonhole multiples of the vector of breakpoints into small cubes on the torus; if the resulting denominators remain bounded, an exact common period exists. Write \(\delta=1/n\). Move each \(b\) to its nearest grid point \(b'\) and keep its jump size, obtaining \(g\). For all sufficiently large such \(n\), order is preserved,
\[
\|f-g\|_1\le\delta\eta_n\sum_b|d_b|=o(\delta),
\qquad \|g\|_\infty\le \|f\|_\infty.
\]

Distinct pair sums \(b+c\) remain in the same order. Equal pair sums round to the **same** grid sum \(b'+c'\): two candidates would differ by at most \(4\eta_n\delta<\delta\). Thus the ordered list of pair sums is moved a distance at most \(2\eta_n\delta\), retaining multiplicities and all jump weights. Indeed,
\[
F(t)=\sum_{b,c}d_bd_c(t-b-c)_+,
\]
and \(G=g*g\) has the same formula with rounded positions. In particular the slopes agree on corresponding intervals; cancellations of simultaneous slope jumps are preserved. We also have \(\|F-G\|_\infty=o(\delta)\). The Lipschitz constants of \(G\) are bounded independently of \(n\) by \(\|f\|_\infty\sum |d_b|\).

### Compare perturbations, not just functions

In cell \(i\), \(0\le i<n\), put \(w_i=1-i/(2n)\) and let \(p=+1\) on its left half and \(-1\) on its right. Set \(\epsilon=\delta/5\) and \(T h=(1+\epsilon v)h\), where \(v=w_i p\). This keeps \(T f\) nonnegative and preserves the integral of \(g\) exactly. Therefore \(\int Tf-\int f=\epsilon\int v(f-g)=o(\delta^2)\).

Write \(\Delta(h)=(Th)*(Th)-h*h=2\epsilon h*(vh)+\epsilon^2(vh)*(vh)\). Since \(|v|\le1\), Young's \(L^1*L^\infty\) estimate applied to differences gives
\[
\|\Delta(f)-\Delta(g)\|_\infty
\le (2\epsilon+\epsilon^2)\big(\|f\|_\infty+\|g\|_\infty\big)\|f-g\|_1
=o(\delta^2).
\]

Here are three bounds on \(\Delta(g)\). Write \(a_i\) for the grid values of \(g\), \(C_k=\sum_{i+j=k}a_i a_j\), \(E_k=\sum_{i+j=k}w_iw_j a_i a_j\), and \(U_k=(1-k/(4n))C_k\), extending these by zero off the support. Then \(C_k/4\le E_k\le C_k\), and symmetry gives \(U_k=\sum_{i+j=k}w_i a_i a_j\). Squaring the two-half-bin construction gives:

1. At each old knot \(t=(k+1)\delta\), \(G(t)=\delta C_k\) and \(\Delta(g)(t)=-\epsilon^2\delta E_k\le -\delta^2 G(t)/100\).
2. At a midpoint \(t=(k+1/2)\delta\), the change is \(\epsilon\delta(U_k-U_{k-1})+(\epsilon^2\delta/2)(E_k+E_{k-1})\). When \(G\) is constant on that cell, \(C_k=C_{k-1}\); the change is at most \((-\epsilon/(4n)+\epsilon^2)G(t)=-\delta^2G(t)/100\). By linear interpolation the same holds throughout any grid-aligned plateau.
3. Everywhere, \(\|\Delta(g)\|_\infty=O(\delta^2)\) and \(\operatorname{Lip}(\Delta(g))=O(\delta)\). For the first bound use the two formulas: the boundedness and uniform Lipschitz bound of \(G\) imply \(\delta |U_k-U_{k-1}|=O(\delta)\), including the outer cells. For the second, \(\Delta(g)\) is linear between half-grid knots, spaced \(\delta/2\). The constants may depend on \(f\), not \(n\).

### Lower every maximum, including flat intervals

Let \(K=\{t:F(t)=M\}\subset[0,2]\). It is a finite union of singletons and closed intervals with endpoints among the pair sums. Each singleton has a corresponding old grid knot of \(G\); each interval has a corresponding plateau of \(G\) (same slopes after rounding). Every \(x\in K\) is within \(2\eta_n\delta=o(\delta)\) of a point \(y\) in the corresponding knot or plateau, where \(G(y)=M+o(1)\), uniformly. The first two bounds give \(\Delta(g)(y)\le-\delta^2(M/100-o(1))\). By the Lipschitz bound and the perturbation comparison, for every fixed \(A>0\) the same upper bound holds for \(\Delta(f)(t)\) whenever \(\operatorname{dist}(t,K)\le A\delta^2\).

Elsewhere, piecewise linearity and compactness give a constant \(\lambda>0\) with \(M-F(t)\ge\lambda\operatorname{dist}(t,K)\) on \([0,2]\): near \(K\) use the finitely many nonzero slopes leaving it, and farther away take the minimum of the positive ratio. We already have \(\|\Delta(f)\|_\infty\le B\delta^2\) for fixed \(B\). Taking \(\lambda A>B+M\) handles all remaining \(t\). We obtain
\[
\|(Tf)*(Tf)\|_\infty\le M-(M/100-o(1))\delta^2 .
\]
Multiplying \(Tf\) by \((\int f)/(\int Tf)=1+o(\delta^2)\) restores the original mass and retains the strict gain. This proves the theorem.

The finite, equal-grid algebra is [verified in Lean](AutoconvolutionRefinement.lean); the simultaneous-approximation extension here is an analytic proof, not a Lean formalization. A separate [exact-arithmetic check](quadratic_step_check.py) computes the original and perturbed maxima directly at every sum of breakpoints for four examples in \(\mathbb Q(\sqrt2)\), including flat peaks. The exact value of the continuous infimum, and whether it has a minimizer among more general functions, are not resolved by this result.
