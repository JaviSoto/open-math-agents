# Gaps between nonsingular cube-indicator Hankel matrices

Let \(H_n=(1_{\{i+j\text{ is a cube}\}})_{1\leq i,j\leq n}\). Zhi-Wei Sun's [conjecture](https://oeis.org/A228624) asserts that \(\det H_n\ne0\) whenever \(n>176\).
Here is a partial result: the nonsingular orders \(q_1<q_2<\cdots\) are infinite and
\[
  \limsup_{k\to\infty}\frac{q_{k+1}}{q_k}\leq 3.
\]
In particular, for every \(\epsilon>0\), all sufficiently large intervals \([x,(3+\epsilon)x]\) contain a nonsingular order. The argument does not exclude single singular orders after 176.

### 1. Four-cycles from equal sums of cubes

View \(H_n\) as the incidence matrix of a bipartite graph on two copies of \([n]\). The number of ordered four-cycles with distinct rows and distinct columns is \(O_\eta(n^{13/9+\eta})\) for any \(\eta>0\).

Indeed, a four-cycle with row indices \(i,k\) and column indices \(j,l\) gives positive cubes
\[
 a^3=i+j,\qquad b^3=k+j,\qquad c^3=k+l,\qquad d^3=i+l
\]
with \(a^3+c^3=b^3+d^3\leq4n\). The two representations differ even as unordered pairs: \(a=b\) forces \(i=k\), and \(a=d\) forces \(j=l\). By the corollary to D. R. Heath-Brown's [*The density of rational points on cubic surfaces*](https://ora.ox.ac.uk/objects/uuid%3A04b73804-727f-43e4-bb2d-b99e175903e6/files/m9ec4d87761c586cdadad7b977f9b3bb8), only \(O_\eta(n^{4/9+\eta})\) integers up to \(4n\) have two such representations. Each integer \(h\) has at most \(2\tau(h)=O_\eta(h^\eta)\) ordered representations: \(a+c\) divides \(h\), and its value determines \(ac=((a+c)^3-h)/(3(a+c))\), hence the unordered pair. Adjusting \(\eta\) gives \(O_\eta(n^{4/9+\eta})\) quadruples. For each quadruple and first row \(i\), the other three indices are determined. This proves the count.

### 2. Rank of the finite matrices

We prove \(\liminf \operatorname{rank}_{\mathbb Q}(H_n)/n\geq1/2\). Ranks over the reals and rationals agree since the matrices have integer entries.

Fix \(0<\alpha,\epsilon<1\). Restrict both indices to \(\alpha\le i/n\le1\); the resulting square matrix has \(m=(1-\alpha)n+O(1)\) rows. For a row \(i\), write \(t=i/n\). The number of its nonzeros whose column fraction lies in an interval \(J\subseteq[\alpha,1]\) is
\[
 n^{1/3}\int_J K(t,s)\,ds+O(1),\qquad K(t,s)=\frac{1}{3(t+s)^{2/3}}.
\]
This follows by taking cube roots at the two interval endpoints, with at most two rounding errors.

Partition \([\alpha,1]\) into finitely many equal intervals \(I_a\) of length \(h\), with midpoints \(t_a\). The positive continuous kernel \(K\) has positive minimum on this compact square. Choose the partition fine enough that for \(t\in I_a,s\in I_b\), the ratio \(K(t,s)/K(t_a,t_b)\) lies in \([1-\epsilon,1+\epsilon]\).

There exist positive weights \(u_a\) with \(u_a\sum_b h K(t_a,t_b)u_b=1\) for every \(a\). For completeness minimize the function
\[
 \Phi(x)=\sum_{a,b}hK(t_a,t_b)e^{x_a+x_b}-2\sum_a x_a .
\]
It is coercive: if the maximum coordinate is large and positive, a positive diagonal term dominates every possible negative linear contribution; on any set with bounded maximum, an unbounded negative minimum forces the linear term to \(+\infty\). At a minimizer take \(u_a=e^{x_a}\); the equations are exactly the vanishing first derivatives, by symmetry.

On the restricted square replace \(H_{ij}\) by \(A_{ij}=\sqrt{u_a u_b}\,H_{ij}\) for \(i/n\in I_a,j/n\in I_b\) (choose half-open intervals at interior boundaries). This changes no rank. If \(R_i=\sum_j A_{ij}^2\), the interval count and the weight equations show uniformly in \(i\) that
\[
 1-\epsilon-o(1)\le n^{-1/3}R_i\le1+\epsilon+o(1).
\]
The partition and weights are held fixed as \(n\to\infty\).

By symmetry, \(\operatorname{tr}(A^2)=\sum_i R_i\). Expand \(\operatorname{tr}(A^4)=\sum_{i,j,k,l} A_{ij}A_{kj}A_{kl}A_{il}\). Terms with \(i=k\) or \(j=l\) contribute at most \(2\sum_i R_i^2\) (the overlap is nonnegative). The other terms are supported on the four-cycles of §1. Their weights are bounded independently of \(n\), so they contribute \(o(n^{5/3})\). Cauchy–Schwarz on the nonzero eigenvalues gives
\[
 \operatorname{rank}(H_n)\ \geq\ \operatorname{rank}(A)
 \ \geq\ \frac{\operatorname{tr}(A^2)^2}{\operatorname{tr}(A^4)}
 \ \geq\ \left(\frac{(1-\epsilon)^2}{2(1+\epsilon)^2}-o(1)\right)m.
\]
Now send \(\epsilon,\alpha\) to zero. This proves the rank assertion.

### 3. Convert rank to nonsingular leading orders

Here is the elementary leading-minor argument, so no result on Padé approximation is needed. Define a rational linear functional \(L\) on polynomials by \(L(X^j)=1_{\{j+2\text{ is a cube}\}}\). The matrix \(H_n\) is the Gram matrix of \(L(PQ)\) on \(1,X,\ldots,X^{n-1}\).

Let \(q\) be any nonsingular order (including \(q=0\), with the empty matrix). There is a unique monic polynomial \(P\) of degree \(q\) such that \(h_j:=L(PX^j)=0\) for \(0\le j<q\), by solving a system with coefficient matrix \(H_q\). Some \(h_d\) with \(d\ge q\) is nonzero: otherwise the \(0,1\) cube-indicator sequence would satisfy the recurrence defined by \(P\) everywhere. The arbitrarily long zero runs immediately preceding later cubes contradict such a monic recurrence, since \(q\) successive zero inputs force the next output to vanish. For \(q=0\) the contradiction just says some term is one.

Let \(d\) be the first such index and \(\ell=d-q+1\). For \(1\le s\le\ell\), use the monic degree-ordered basis
\[
  1,\ldots,X^{q-1},P,XP,\ldots,X^{s-1}P.
\]
The mixed block is zero because its entries are \(h_j\) with \(j\le q+s-2<d\). In the final square block the \(i,j\) entry for \(0\le i,j<s\) equals \(L(P^2X^{i+j})\). Its value is zero for \(i+j<\ell-1\), and is \(h_d\ne0\) for \(i+j=\ell-1\): expand one monic copy of \(P\). Consequently this block has rank \(\max(0,2s-\ell)\). Indeed, if \(2s>\ell\) the last \(2s-\ell\) rows and columns form a nonsingular antitriangular block, and all preceding rows and columns are zero; otherwise every entry is zero.

Thus the next nonsingular order is \(r=q+\ell=d+1\). This construction also proves that there are infinitely many. At the midpoint \(N=\lfloor(q+r)/2\rfloor\), the exact rank is \(q\). Applying §2 there gives \(q\ge(1/2-o(1))N\), which is equivalent to \(r\le(3+o(1))q\).

### 4. Odd determinants on every sufficiently wide multiplicative interval

There is a separate elementary finite-field result: if \(q<r\) are consecutive orders with **odd** integer determinant (start with \(q=0\)), then \(r\le7q+7\). Thus the determinant is not just nonzero but odd at an unbounded sequence of orders, with a uniform bound on the gaps. More generally, \(r\le9q+7\) for the orders nonsingular over any field. No result about rational points is used in this section.

Work over the chosen field. Put \(U(x)=\sum_{j\ge0}1_{\{j+2\text{ is a cube}\}}x^j\) and \(F(x)=1+x+x^2U(x)=\sum_{k\ge0}x^{k^3}\). For a series \(G\), let \(E(G)(x)=\sum_{j\ge0}[x^{2j}]G\;x^j\) extract its even-indexed coefficients. An even cube is eight times a cube, so \(E(F)(x)=F(x^4)\).

By the construction in §3, take the reversed monic recurrence polynomial \(B(x)=1+\sum_{i<q}p_i x^{q-i}\), where \(P(X)=X^q+\sum_{i<q}p_iX^i\). Truncate \(BU\) below degree \(q\) to obtain \(V\) (zero if \(q=0\)). The first nonzero coefficient of \(BU-V\) occurs at \(q+d=q+r-1\). Thus
\[
 R=1+x+x^2V/B=A/B,\qquad
 \deg A\le q+1,\quad\deg B\le q,\quad
 \operatorname{ord}_0(F-R)=M=q+r+1.
\]
Here \(A,B\) may be reduced without increasing the degree bounds, and \(B(0)\ne0\). As \(M\ge2\) and \(F\) begins \(1+x\), \(R\) is nonconstant.

The degree of a rational map is the maximum of the numerator and denominator degrees in reduced form. For any such \(R\), its even section has degree at most \(\deg R\). Indeed \(B(x)B(-x)=D(x^2)\) is even, and \(E(R)=E(A(x)B(-x))/D(x)\), using \(E(G(x)J(x^2))=E(G)J\). Thus \(\deg D\le q\) and the numerator of \(E(R)\) has degree at most \(q\). In characteristic two over the prime field, \(D(x)=B(x)\) by Frobenius. In every field \(\deg R(x^4)=4\deg R\) because coprimality survives composition with \(x^4\). Consequently \(E(R)\ne R(x^4)\).

Since \(E(F)=F(x^4)\), the nonzero rational function \(E(R)-R(x^4)\) vanishes to order at least \(\lceil M/2\rceil\) at zero (the substitution \(x\mapsto x^4\) gives order \(4M\)). Over \(\mathbb F_2\), its numerator over the common denominator \(B^4\) is \(E(AB)B^3-A^4\), of degree at most \(4q+4\). Hence \(q+r+1=M\le8q+8\). Over any field, using the denominator \(D(x)B(x^4)\) instead gives numerator degree at most \(5q+4\), proving the asserted \(9q+7\) bound. The empty starting order gives \(r=7\) over every field, so the additive offset is necessary in either universal bound.

The [checked Lean file](CubeHankel228624.lean) proves unboundedness directly for the original integer determinant and for arbitrary fields; its explicit next-order bound is \((\lfloor\sqrt q\rfloor+2)^3-1-q\). The sharper bounds 3, 7, and 9 are proved on paper here.

### Computational status

The separate [modular calculation](hankel_cubes_probe.cpp) examines the normal indices over a finite field; a determinant nonzero modulo a prime is nonzero as an integer. Compile with a C++17 compiler at optimization level 3, then pass the arguments \(\texttt{48000 1000000007 3 --audit}\). It lists no singular orders from 177 through 48,000. The optional audit compares the recurrence algorithm against direct Gaussian elimination at every order through 225 and at 350 and 577. The finite check is not used in the infinite-family proof.
