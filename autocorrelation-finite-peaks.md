# A local perturbation rules out finite polynomial and Fourier profiles

Work on \([0,1]\), extending densities by zero. Let \(f\ge0\) have positive integral and be polynomial on each member of a finite interval partition. **If \(f*f\) has only finitely many global maximizers, then \(f\) does not minimize the autoconvolution peak.** Neither rational breakpoints nor information about how sharply the maximum drops are required.

In particular **no single polynomial density on the interval can attain the optimum**. On each of \([0,1]\) and \([1,2]\) its convolution is a polynomial, by integrating \(f(x)f(t-x)\) between the affine endpoints of the overlap. It vanishes at the outside endpoints and has positive maximum, so neither polynomial is identically equal to its maximum.

### The perturbation

Let \(T=\{t_1,\ldots,t_s\}\) be the maximizers, \(F=f*f\) and \(M=\max F>0\). For each \(t_j\) choose centers \(x_j,y_j=t_j-x_j\) at which both factors are positive, in interiors of polynomial pieces. There is a positive-measure choice since \(F(t_j)>0\). Choose them sequentially with these additional properties:

* all \(2s\) centers are distinct;
* for each center \(u\) and \(t\in T\), \(t-u\) is not a breakpoint of \(f\) (including the support endpoints);
* the only two-center sums belonging to \(T\), allowing a center to be used twice, are the designated pairs \(x_j+y_j=t_j\).

At each choice this excludes only finitely many values of \(x_j\): undesired equations against previously chosen centers or doubled new centers have nonzero slope in \(x_j\), while the sum of the two new centers is the required \(t_j\).

Take a common radius \(r>0\) so small that the intervals about the centers are disjoint, \(f\) has a strictly positive lower bound on their union, undesired pair sums remain disjoint from \(T\), and the shifted interval \(t-[u-r,u+r]\) stays inside a single polynomial piece for all \(t\) near each point of \(T\). The zero function outside \([0,1]\) counts as a piece.

Let \(d\) be the maximum degree. Choose a real nonzero smooth bump \(\psi\) compactly supported in \((-r,r)\) with moments of orders \(0,\ldots,d\) zero; take the \((d+1)\)-st derivative of a smooth bump. Put a copy \(\psi(x-x_j)\) at \(x_j\) and the negative reflected copy \(-\psi(y_j-x)\) at \(y_j\), and sum them to obtain \(g\).

Then \(\int g=0\). Near every \(t_j\), \(f*g(t)=0\) **identically**: on each bump, \(f(t-x)\) is polynomial in \(x\) of degree at most \(d\). At \(t_j\) only the two cross terms of its designated pair contribute to \(g*g\), giving \((g*g)(t_j)=-2\int\psi^2<0\). Thus there is a fixed neighborhood of \(T\) on which \(f*g=0\) and \(g*g\le-c<0\).

For sufficiently small \(\varepsilon>0\), \(f+\varepsilon g\) is nonnegative with the same mass. Its autoconvolution is \(F+2\varepsilon f*g+\varepsilon^2 g*g\). This is at most \(M-c\varepsilon^2\) within the neighborhood. Outside it \(F\) is uniformly below \(M\) on the compact sum interval, so the perturbed maximum is strictly below \(M\).

### Finite Fourier profiles

The same proof works when the pieces belong to finite-dimensional spaces of exponential polynomials (finite linear combinations of \(x^m e^{\lambda x}\), using real-valued combinations). Include translations and reflections of the local formulas when choosing the moment conditions; they stay within a finite-dimensional span, as do the real and imaginary parts. A nonzero real smooth bump orthogonal to that span and to constants exists: impose the finitely many homogeneous linear constraints on more disjoint test bumps than there are constraints. This handles reflected and translated copies as in the polynomial proof.

For a single exponential-polynomial profile over \([0,1]\), its convolution on each of the two sum intervals is analytic past the endpoints, by explicit integration of exponential polynomials. It cannot be a positive constant there since it vanishes at the outside endpoint. Thus \(T\) is finite. This excludes finite trigonometric-polynomial profiles on the interval. For each **fixed** finite-dimensional polynomial or Fourier space, the nonnegative unit-mass set is compact (the \(L^1\) norm controls coefficients in fixed finite dimension). The peak is continuous there, so the best value in that space is strictly above the global infimum.

The finite-maxima condition on the first statement is essential to this argument; it does not handle a plateau of a general piecewise polynomial. The [arbitrary-step theorem](autocorrelation-arbitrary-steps.md) treats flat maxima for piecewise **constant** profiles by a different argument. These are written analytic proofs, not claims of a complete solution for \(C_{1a}\).
