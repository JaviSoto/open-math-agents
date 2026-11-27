# Counting quotient-four blocks by quadratic interpolation

For the quotient-four equation of Erdős 686, the number of witness triples
with lower start at most `T` is `O(T^(1/3))`. This is a mathematical argument;
the cubic start bound and the centered strip have Lean proofs, while the
uniform analytic argument below is not formalized. This count does not decide
whether any witness exists.

## Normalize the branch

Let $X=2m+k+1$, $Y=2n+k+1$, $a=4^{1/k}$, and $s=k/Y$. The offsets
$u_i=(2i+1-k)/k$ for $0\le i<k$ are the midpoints of $k$ equal subintervals
of $[-1,1]$. Write $L_k(s)=k^{-1}\sum_i\log(1+u_i s)$ using the power
series at zero. This is even, holomorphic for $|s|<1$, and converges uniformly
on compact subdisks to $L(s)=\frac12\int_{-1}^1\log(1+vs)\,dv$: the
coefficients are midpoint sums of powers, bounded by $1/j$ at degree $j$.

Temporarily let $A$ vary near $1$. The positive product branch is $X/Y=B_k(A,s)$
with $A=a$, where

$$ B_k=A\exp(L_k(s)-L_k(s/B_k)). $$

For precision, take $|A-1|\le1/32$, $|s|\le1/32$, and $|B-1|\le1/4$.
Then $|s/B|\le1/24$, $|L_k(w)|\le|w|/(1-|w|)$, and
$|L_k'(w)|\le1/(1-|w|)$. The displayed right side maps the closed $B$ disk
strictly into itself, and its $B$-derivative has modulus $<1/8$. Iterating
from $1$ therefore gives holomorphic $B_k$ with geometric uniform convergence.
The same bounds and convergence of $L_k$ apply to its limit $B$. Cauchy's
formula gives uniform convergence of all fixed-order derivatives on smaller
polydisks. The real solution selected is the one on the positive branch:
when $s>0$ is this small, all the factors $B+u_i s$ are positive and their
product is strictly increasing for $B>s$. For a witness $X/Y\ge1$.

For all sufficiently large $k$, put

$$ f_k(s)=\frac{B_k(a,s)-a}{(a-1)s}. $$

The numerator vanishes at $A=1$ since $B_k(1,s)=1$, and at $s=0$ since
$B_k(A,0)=A$. Evenness in $s$ gives an odd holomorphic $f_k$. The integral
of $\partial_A(B_k(A,s)-A)$ along the segment from $1$ to $a$ (or the Cauchy
formula) proves that on a smaller fixed disk these functions converge uniformly
to $(\partial_A B(1,s)-1)/s$, with the singularity at zero removed.
Logarithmic differentiation of the implicit equation gives
$\partial_A B(1,s)=(1-s L'(s))^{-1}$.
Since $1-s L'(s)=\frac12\int_{-1}^1(1+vs)^{-1}\,dv=\mathrm{atanh}(s)/s$,

$$ f_k(s)\longrightarrow f(s)=1/\mathrm{atanh}(s)-1/s. $$

The first three coefficients $f_k(s)=c_k s+d_k s^3+e_k s^5+O(s^7)$
converge to $c=-1/3$, $d=-4/45$, $e=-44/945$. They follow by dividing the
series $s+s^3/3+s^5/5+s^7/7+O(s^9)$. In particular
$e-2d^2/c=4/4725$. All power-series remainders below and their fixed-order
derivatives are uniform by the Cauchy bounds. Write

$$ g_k(s)=f_k(s)/s-c_k-(d_k/c_k^2) f_k(s)^2. $$

Then $g_k(s)=(e_k-2d_k^2/c_k)s^4+O(s^6)$.

## No conic has six points of this branch near infinity

The restrictions of the six conic monomials to the normalized branch,
after multiplying all six by $s^2$, have the same real span as

$$1,\quad s,\quad s^2,\quad s^2 f_k,\quad s^2 f_k^2,\quad s^2 g_k.$$

Indeed $Y=k/s$ and $X-aY=k(a-1)f_k(s)$, so the substitutions and
replacement of $f_k/s$ by $g_k$ are invertible. These ordered functions
have respective leading orders $0,1,2,3,4,6$. Their leading coefficients
tend to $1,1,1,c,c^2,4/4725$, all nonzero. Thus for all sufficiently large
$k$ their prefix Wronskians are nonzero throughout one fixed $0<s<s_0$.
In detail, scale the entry in row $i$ (derivative order), column $j$
(leading order $h_j$), by $s^{i-h_j}$. It tends to the leading coefficient
times the falling factorial $(h_j)_i$, with error $O(s)$ uniformly in $k$.
This remains true for $i>h_j$, where the leading falling factorial vanishes.
The limiting determinant is the Vandermonde of the distinct leading orders
times the product of leading coefficients.

For completeness, those Wronskians imply that no nonzero linear combination
of the six functions has six distinct zeros. Divide by the first function
and differentiate; the new ordered functions are $(f_j/f_0)'$ for $j>0$.
Their prefix Wronskians are the old prefix Wronskians divided by the
corresponding powers of $f_0$, by the product rule. Apply induction and Rolle's
theorem. Thus six distinct $Y$ values in this range give a **nonzero** conic
evaluation determinant. A reference for the classical criterion is
[Grau, Mañosas and Villadelprat, Lemma 2.3](https://ddd.uab.cat/pub/artpub/2011/gsduab_2362/traamematsoc_a2011v363n1kp109preprint.pdf).

## The integer determinant is small

Take six witness points in $D\le Y\le2D$, all of the same length $k$.
Their evaluation matrix for $1,Y,X,Y^2,YX,X^2$ is integral. Shear $X$
to $z=X-aY$, leaving the determinant unchanged. From the $Yz$ column subtract
the constant $k^2(a-1)c_k$ and the multiple $d_k/((a-1)c_k^2)$ of $z^2$.
It becomes exactly $k^2(a-1)g_k(s)$. Since $k(a-1)=O(1)$, the six column
sup norms in the resulting order are bounded, up to absolute factors, by

$$ 1,\qquad D,\qquad k/D,\qquad D^2,\qquad k^5/D^4,\qquad k^2/D^2. $$

The permutation expansion gives absolute determinant $O(k^8/D^4)$.
The earlier arithmetic result for this problem (CubicGap686.lean) gives
$Y\gg k^3$ for every witness with large $k$. Hence the determinant has
absolute value less than one eventually, and must vanish. This contradicts
the preceding paragraph, so there are at most five points per dyadic band for
every sufficiently large $k$. The value of $m$ is unique for fixed $k,n$
because the product is strictly increasing in $m$.

If $n\le T$ then $k\ll T^{1/3}$ and $Y\ll T$ for large $k$. Summing
$O(1+\log(T/(c k^3)))$ permissible bands up to $k\le (T/c)^{1/3}$ costs
$O(T^{1/3})$ by the integral of $\log(K/x)$ on $[1,K]$.
The finitely many exceptional lengths cost $O(\log T)$ by the
already established strict-concavity/centered-strip lattice bound (a bounded
number per dyadic band at each fixed length). Small positive $T$ can be
absorbed into the constant.

The [general determinant bound of Pila](https://people.maths.ox.ac.uk/pila/alcurves.pdf)
has degree-dependent constants. Even the stronger degree-uniform affine
estimate $O(d^2 T^{1/d}(\log T)^\kappa)$ of
[Binyamini, Cluckers and Kato, Corollary 8](https://doi.org/10.1112/plms.70016)
retains the factor $d^2$; setting $d=k$ and summing it up to $T^{1/3}$ gives
no improvement over the elementary strip argument. The above conic calculation
uses the shape of this particular sequence of branches.

The integral determinant calculation is kernel-checked as
`OMA.ConicStrip686.vanish` in `ConicStrip686.lean`: if $|Y|\le D$,
$|X-aY|\le Z$, $|Y(X-aY)-c-d(X-aY)^2|\le R$ throughout the six points
and $720D^3Z^3R<1$, then their integral conic determinant vanishes.
