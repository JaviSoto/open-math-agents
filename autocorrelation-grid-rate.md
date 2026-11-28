# Quantitative comparison of polynomial squares with continuous autoconvolutions

Let \(C\) be twice the infimum of \(\|f*f\|_\infty\) over probability densities on \([0,1]\). This is the usual \(C_{1a}\) after rescaling. Let \(U_n\) be the minimum of \(2n\max_k\sum_{i+j=k}p_i p_j\), for nonnegative \(p_0,\ldots,p_{n-1}\) summing to one. In [Schinzel and Schmidt, Theorem 1](https://doi.org/10.4064/aa104-3-4), their \(A(n)\) and \(B\) are \(2/U_n\) and \(2/C\). They prove a relative discretization error of order \(n^{-1/3}\); Kwapień’s bound quoted on their second page improves the constant at that exponent.

**Theorem.** For positive integers \(m,n\) with \(L=n-1-4m>0\) and \(e=12\cdot3^{-2m}<1\),
\[
  \frac{L}{n}(1-e)^2 U_n\;\le C\;\le\left(1-\frac1{100n^2}\right)U_n .
\]
In particular, taking \(m=\lceil\log_3 n\rceil\) gives \(U_n/C=1+O((\log n)/n)\), improving the convergence rate in that theorem. One can choose \(m\) separately at each \(n\). This is a comparison with the **global** finite minimum: a single numerical candidate, even with an exact certificate, cannot be substituted for \(U_n\) on the lower-bound side.

### Sampling without changing the convolution at the sample points

Write \(\operatorname{sinc}(z)=\sin(\pi z)/(\pi z)\), taking value one at zero. Use the nonnegative probability kernel
\[
  K(x)=c_m\operatorname{sinc}(x/(2m))^{2m},\qquad \int K=1.
\]
Its Fourier transform in cycles per unit vanishes off \([-1/2,1/2]\): each sinc factor has frequencies in \([-1/(4m),1/(4m)]\). Also \(c_m\le2\). Indeed, on \(|x|\le1/2\) the unnormalized function is at least \((1-\pi^2/(96m^2))^{2m}\ge1-\pi^2/(48m)>1/2\).

Take a probability density with finite autoconvolution peak \(M\) on the unit interval; the proof works equally for a probability measure whose square has bounded density. Push it forward under \(x\mapsto 2m+Lx\), yielding a probability measure \(\nu\) supported on \([2m,n-1-2m]\), and let \(h=\nu*K\). Then \(\int h=1\), the transform of \(h\) is supported on \([-1/2,1/2]\), and
\[
 \|h*h\|_\infty=\|(\nu*\nu)*(K*K)\|_\infty\le M/L.
\]
For every integer \(k\), the full samples satisfy
\[
  \sum_{j\in\mathbb Z}h(j)=1,\qquad
  \sum_{j\in\mathbb Z}h(j)h(k-j)=(h*h)(k).
\]
For the first equality periodize \(h\); for the second periodize \(x\mapsto h(x)h(k-x)\). Their transforms are supported, respectively, on \([-1/2,1/2]\) and \([-1,1]\), hence vanish on all nonzero integers. At \(\pm1\) this follows by continuity of the transform of the integrable product. Periodizations converge uniformly on a period by the \(O((1+|x|)^{-2m})\) tails of \(h\). Their Fourier coefficients are the integer-frequency transform values by integration, so both periodizations are constant. Evaluating at zero gives the identities.

### Discard the tails without raising the peak

Uniformly for \(y\in[2m,n-1-2m]\), the total omitted kernel mass \(\sum_{j\notin[0,n-1]}K(j-y)\) is at most
\[
  4\pi^{-2m}\left(1+\int_{2m}^\infty (2m/x)^{2m}\,dx\right)
  =4\pi^{-2m}\left(1+\frac{2m}{2m-1}\right)\le e.
\]
Here the nearest omitted sample on either side is at distance at least \(2m\); use \(K(x)\le2(2m/(\pi |x|))^{2m}\) and the integral test on each side. Integrating against \(\nu\) shows that the retained samples have sum \(s\ge1-e\). Nonnegativity ensures discarding samples decreases every convolution coefficient. Taking \(p_j=h(j)/s\) for \(0\le j<n\) now gives \(U_n\le 2nM/(L(1-e)^2)\). Infimize over input densities. The opposite stated inequality follows from the [strict dyadic refinement](autocorrelation-refinement.md) and \(C\le U_{2n}\).

For example, with \(n=524{,}288, m=7\) the explicit factor \((L/n)(1-e)^2\) exceeds 0.999939. A proof that **all** grids of this size exceed a given value would therefore transfer to the continuum with relative loss below 0.0061%. Obtaining that finite global lower bound is a different problem; this argument does not determine the constant.
