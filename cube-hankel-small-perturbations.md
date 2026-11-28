# Simultaneously removing all cube-Hankel singularities by small rational perturbations

For each cube \(k^3\), give entries with that sum the common real weight \(w_k\); keep every other entry zero. Write \(D_n(w)\) for the determinant on indices \(1,\ldots,n\).

**Theorem.** Given any positive tolerances \(\epsilon_k\), there is a single sequence of rational weights with \(w_2=\cdots=w_8=1\), \(1\le w_k<1+\epsilon_k\) for \(k\ge9\), and \(D_n(w)\ne0\) for every \(n\ge177\). Alternatively, one can choose positive integer weights \(w_k=O(k^4)\). The simultaneous conclusion holds over the rationals, without using algebraically independent weights.

For an order \(n\ge365\) let \(k\) be the largest integer with \(k^3\le2n\). Thus \(k\ge9\), and let \(m=k^3-n-1\). We have \(m<n\), \(2m<k^3\), and \(m\ge177\): indeed \(2n<(k+1)^3\), so \(2m\ge2k^3-(k+1)^3-1\), which at \(k=9\) is 457 and increases thereafter. If the integer expression at this lower endpoint is odd, take the next even integer. The northwest \(m\times m\) matrix involves only weights already chosen at roots smaller than \(k\).

Treat \(w_k=X\), with the smaller weights fixed. There are exactly \(d=n-m=2n+1-k^3\) entries equal to the variable \(X\). They form the antidiagonal of the block indexed by \(m+1,\ldots,n\). To attain degree \(d\), a permutation must use all \(d\) positions, so the coefficient of \(X^d\) in \(D_n\) is
\[
                         (-1)^{d(d-1)/2}D_m.
\]
This formula also follows by expanding along the mandatory antidiagonal. In particular the polynomial is nonzero when \(D_m\ne0\), with at most \(d\) distinct exceptional values of \(X\).

Set the first seven weights to one. For each \(177\le m\le364\), the unweighted determinant is nonzero modulo \(1,000,000,007\). This finite base can be reproduced with the [plain-Python elimination](cube_hankel_weight_base.py): one elimination to order 364 suffices, with all pivot swaps restricted to the first 177 rows, so the same sign applies to every subsequently measured leading minor. The endpoint residues are \(1,000,000,006\) and \(225,329,814\).

Now choose \(w_9,w_{10},\ldots\) in order. For a given \(k\) the relevant sizes satisfy \(k^3\le 2n<(k+1)^3\). There are \(O(k^2)\) such integers \(n\), each with \(d\le (k+1)^3-k^3=O(k^2)\). For each one, the smaller determinant \(D_m\) is nonzero by the induction hypothesis. Hence only \(O(k^4)\) real values are excluded for \(w_k\), and no later choice can affect the determinants now being secured. Choose a rational point in the prescribed interval avoiding this finite set. For integer weights, take the least positive integer outside it. This proves both assertions. In fact \(w_k=1\) may be retained whenever it passes the finite tests at this step.

For each *individual* size, still fewer coordinates need change. Take the *smallest* cube \(k^3\ge n+178\). When \(n\) is large, \(177\le m=k^3-n-1\le Cn^{2/3}<n\). An iteration changes at most one new weight at each step; the cube selected at a later, smaller size cannot equal an earlier selected cube since \(2m<k^3\). For the bounded base of this iteration use the preceding simultaneous theorem, changing only a fixed number of coordinates. Each polynomial in its new variable has the displayed nonzero leading coefficient, and so admits rational choices in every neighborhood of \(1\). The inequality \(\log m\le \tfrac23\log n+O(1)\) bounds the depth by \(O(\log\log n)\).

The theorem also proves that the determinant with independently indeterminate cube weights is a nonzero polynomial for every \(n\ge177\). It leaves open whether the single point \(w_k=1\) for every \(k\) is a zero at any such order.

**Lean verification.** The [standalone file](CubeHankelWeightComplete228624.lean) proves the finite unweighted base on the original integer sequence independently over the field of 53 elements (`OMA.CubeWeight.unweighted_base`), simultaneous nonvanishing for rational weights drawn from prescribed infinite sets (`.simultaneous`), and existence in every sequence of open intervals immediately above one (`.near_one`). The integer size bound and the coordinate count for a single order are the written arguments above.
