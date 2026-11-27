# Almost every biharmonic crystal has unique components

An odd integer is a crystal if it equals $ab$, where $1<a\le b$ and
$(a+1)(b+1)\mid(a+b)^2$. Abrate, Barbero, Cerruti and Murru
[conjectured in 2016](https://arxiv.org/abs/1601.03081) that each crystal
has only one such pair. Write $C(X)$ for the number of crystals up to $X$,
and $D(X)$ for the number having multiple unordered pairs.

**Main research result.** For every $\epsilon>0$, $D(X)=O_\epsilon(X^\epsilon)$.
The proof below uses the real critical values of the row polynomials and
Siegel’s integral-point theorem. Its constant is ineffective.

**Explicit Lean-checked bounds.** $D(X)=O(X^{1/4})$, $C(X)\gg X^{1/3}$, and hence
$D(X)/C(X)\to0$. This proof is fully checked in Lean with no assumptions
besides the standard axioms. A second argument gives

$$
D(X)=O(X^{1/5}),\qquad
C(X)=(X/4)^{1/3}+(X/4)^{1/4}+O(X^{1/5}).
$$

The second argument uses the published complete list of integral points on
[elliptic curve 2432.a1](https://www.lmfdb.org/EllipticCurve/Q/2432/a/1).
The LMFDB [documents](https://www.lmfdb.org/knowledge/show/rcs.rigor.ec.q)
independent rigorous Magma and SageMath computations. That enumeration
remains an explicit hypothesis of the stronger Lean proof.

## Argument

The starting point is the authors' classification (§3, Theorems 4–5). For
parameter $w\ge4$, write $u_0=0,\ u_1=1$ and
$u_{r+1}=(w-2)u_r-u_{r-1}+2$. Components are $2u_r-1,2u_{r+1}-1$,
starting at $r=2$; smaller $w$ contributes only $35=5\cdot7$.
Our Lean proof establishes this direction by Vieta descent on the smaller
half-component and constructs the two main families directly.

* At $r=2$, the products are $(2w-1)(2(w-1)^2-1)$. They increase
  strictly and contribute $(X/4)^{1/3}+O(1)$ distinct crystals.
* At $w=4$, $u_r=r^2$, giving
  $(2r^2-1)(2(r+1)^2-1)$. They increase strictly and contribute
  $(X/4)^{1/4}+O(1)$.
* Write $d=w-4\ge1$. For $r\ge3$ the product is at least $d^5$;
  for $r\ge4$ it is at least $d^7$. Each fixed $d$ has only
  $O(\log X)$ indices, because the smaller half-component at least
  doubles at each step. The remaining rows therefore contribute at most
  $O(X^{1/5}+X^{1/7}\log X)=O(X^{1/5})$ products.

A repeated product must have a noncubic occurrence, proving the first
unconditional bound. To separate the two dominant families, observe that
the parabolic product plus two is $z^2$, where $z=2r(r+1)-1$.
For a cubic product this implies $z^2=4w^3-10w^2+6w+1$. Substituting
$x=4w-3,\ y=4z$ gives $y^2=x^3-x^2-9x+25$, the minimal equation of
2432.a1. Its integral x-coordinates are
$-3,0,1,3,7,13,16,81,1197$. For $w\ge4$ these allow only
$w=4,21,300$, with $z=11,181,10349$. In the latter two cases $2z+3$
is not a square, whereas a parabolic occurrence requires
$2z+3=(2r+1)^2$. Thus $w=4,r=2$ is the sole intersection: it is the
same pair $(7,17)$ in both descriptions. The stronger estimates follow.

The complete uniqueness conjecture remains open on the sparse rows. An
independent exact-integer search found no repeated pair through $10^{28}$.
It enumerated 7,071,066 parabolic occurrences and 311,658 further sparse
products, using an inverse cube-root test for the entire cubic family.
Direct factorization agreed with the recurrence on all 43 crystals through
100,000.

## A uniformly subpolynomial exceptional bound

For every $\epsilon>0$,

$$D(X)=O_\epsilon(X^\epsilon).$$

This is an ineffective theorem using Siegel finiteness, not a computation
on a bounded list of rows. It does not imply that no crystal has a second
factorization. The explicit Lean bounds above remain useful at finite $X$.

Write $F_j(w)=(2u_{j+1}-1)(2u_{j+2}-1)$, for $j\ge1$. Its degree is
$2j+1$ by the recurrence; it is strictly increasing for integer $w\ge5$
(the positive-coordinate and positive-difference recurrence has nonnegative
coefficients in $w-4$, and each step strictly increases with that parameter).
We will show that two distinct fixed rows have only finitely many integral
intersections, as do a fixed row and the parabolic family.

**The real critical points.** Substitute $w=4\cos^2\phi$, $0<\phi<\pi/2$.
The recurrence gives $u_r=\sin^2(r\phi)/\sin^2\phi$ (both sides have the
same initial conditions and satisfy the same recurrence). Put $c=\cos\phi$,
$L=2j+3$. Direct product-to-sum gives

$$F_j(w)=H(\phi)^2-1-w/4,\qquad
H(\phi)=\frac{c^3-\cos(L\phi)}{1-c^2}.$$

At the $j+1$ nodes $\phi=h\pi/L$, $1\le h\le j+1$, the sign of $H$
alternates. If $\cos(L\phi)=1$ then $F_j=c^2/(1+c)^2>0$; if it is $-1$
then $F_j=c^2/(1-c)^2>0$. Between each consecutive pair of nodes $H$
vanishes, so $F_j<-1$ somewhere in each of $j$ disjoint wells.
There are two distinct zeros in each well and a further one between $w=0$
(where $F_j=-1$) and the smallest positive node. By its degree these are
all the zeros, all simple. Rolle's theorem gives all $2j$ critical points,
also simple and in $(0,4)$. There are $j$ negative minima and $j$ positive
maxima. No two negative minima give the same value: if the first occurs
at $m$ and a later well contains $r>m$ with $H(r)=0$ (writing $H$ via
the monotonically corresponding $\phi$), then
$F_j(m)\ge-1-m/4>-1-r/4=F_j(r)$, which bounds the later minimum above.
Thus each negative critical value has precisely one ramified point above
it, of index two. Also $-2$ is not a critical value.

**Monodromy.** Such a single transposition branch can arise from a
decomposition $F_j=G\circ B$ of polynomial degrees $g,b>1$ only at a
critical value coming from a critical point of $B$. Indeed, if $G$ ramified
at a point over that value, every preimage of that point under $B$ would
be ramified for the composite. Having exactly one such preimage forces
$B$ to be totally ramified there, making the composite index at least $2b$.
Hence $j$ distinct branches would require $j\le b-1$, whereas $g\ge3$
is odd and $b\le(2j+1)/3$. This contradiction proves indecomposability
over $\mathbb C$. Polynomial indecomposability implies that the geometric
monodromy is primitive: an intermediate field gives a rational functional
decomposition by Lüroth, and the unique pole at infinity makes it a
polynomial decomposition after a change of coordinate. A primitive
permutation group with a transposition is the full symmetric group
(the conjugate transpositions form an invariant graph, whose components
are blocks). Thus the group of $F_j$ is $S_{2j+1}$.

**Genus for all fixed pairs.** For $j<k$, put $a=2j+1,b=2k+1$. The
Galois closures of the respective covers of $\mathbb P^1$ have at most
a common quadratic subextension: their intersection is a Galois
quotient of both symmetric groups, and $b\ge5$, $a<b$. Therefore the
joint action on the $ab$ sheets contains $\{1\}\times A_b$ and projects
onto $S_a$. It is transitive, so $F_j(x)=F_k(y)$ is geometrically
irreducible. For a finite branch value $v$, let $e_v,h_v$ count simple
critical points in its two fibers. The contribution to ramification of
the joint cover is $b e_v+a h_v-2e_vh_v$: a pair of two transposition
orbits has four sheets and two cycles, whereas a single ramified orbit
and a singleton have two sheets and one cycle. At infinity there are
$\gcd(a,b)$ cycles. Riemann–Hurwitz gives

$$2g=(a-1)(b-1)-\gcd(a,b)+1-2\sum_v e_vh_v.$$

For negative $v$, $e_v,h_v\le1$, so their contribution to the sum is
at most $j$. For positive $v$ it is at most $jk$, the product of the
total numbers of positive maxima. Thus
$2g\ge2j(k-1)-\gcd(a,b)+1>0$: for $k\ge3$ use $\gcd(a,b)\le2j+1$;
the only smaller pair is $(j,k)=(1,2)$, with coprime degrees $3,5$.
The fixed-row intersections are consequently finite by Siegel. Intersection
with the parabolic family implies $z^2=F_j(w)+2$. The polynomial is
squarefree since $-2$ was not a critical value, and has odd degree
$2j+1$, so this hyperelliptic curve has genus $j\ge1$. Again Siegel applies.

**Tail count.** Within a single fixed row or the parabolic family the
products increase strictly. For any fixed $m$, pairwise finiteness of
the first $m$ rows and the parabolic family leaves just $O_m(1)$ exceptions
supported wholly on these families. Every other exception has a
positive-parameter row $j\ge m+1$. Write $d=w-4\ge1$. The smaller
half-component in row $j$ is at least $d^j$, and the next is at least
$d^{j+1}$: the difference $h$ satisfies $h\ge dx$ for the current
smaller half-component $x$, since the next difference is
$h+d(x+h)+2$. The product is therefore at least $d^{2j+1}$. Row
$m+1$ contributes $O(X^{1/(2m+3)})$ elements, and all subsequent
rows contribute $O(X^{1/(2m+5)}\log X)$ by the fixed-parameter doubling
noted above. Choose $m$ with $1/(2m+3)\le\epsilon$. This proves the
bound. The argument is outside the present Lean verification.

## Finite independent check: disjoint branches for 101 families

For $1\le j\le100$, let $F_j(w)=(2u_{j+1}-1)(2u_{j+2}-1)$; its degree
is $2j+1$. Include the parabolic quartic as a separate polynomial. For a
polynomial $f$, its finite branch locus is the set of roots of
$R_f(T)=\operatorname{Res}_x(f(x)-T,f'(x))$. The accompanying
crystal_branch_certificate.py verifies that the 101 polynomials $R_f$
are pairwise coprime modulo the prime 1,000,000,007, with all degrees
preserved. This implies coprimality in characteristic zero. For the first
seven fixed rows and the quartic, direct symbolic resultants over the
rationals independently give the same answer. An independent run for
**all 101 families** instead uses the prime $2^{31}-1$, direct bivariate
resultants (no interpolation), and a separate binomial-coefficient formula
for each $u_r$. It gives the same 5,050 pairwise coprimality conclusions.
To reproduce, run the two commands below from this directory:

    uv run --no-project --with python-flint python crystal_branch_certificate.py 100
    uv run --no-project --with python-flint python crystal_branch_certificate.py 100 --independent

For two of these polynomials of degrees $a,b$, their Galois closures over
$\mathbb C(T)$ share no subextension: the intersection could ramify only at
infinity, and there is no nontrivial cover of the complex projective line
branched at at most one point. Consequently the fiber product $f(x)=g(y)$ is
geometrically irreducible. On its normalization, finite ramification over
the $T$-line contributes $b(a-1)+a(b-1)$, since the two finite branch
loci are disjoint. Above infinity the product of the $a$-cycle and the
$b$-cycle has $\gcd(a,b)$ orbits; the contribution is $ab-\gcd(a,b)$.
Riemann–Hurwitz therefore gives

$$
2g=(a-1)(b-1)-\gcd(a,b)+1>0.
$$

There is also a direct topological connectedness check: loops around
the finite branch points of $f$ generate its transitive monodromy group
(the loop at infinity is determined by them), but they act trivially
on all sheets of $g$; the corresponding loops for $g$ do the reverse.
Thus the product action is transitive. Independently, in a
$\mathbb P^1\times\mathbb P^1$ compactification the curve has arithmetic
genus $(a-1)(b-1)$ and is smooth away from $(\infty,\infty)$. At that
point the local analytic singularity is $v^b=u^a$ after absorbing units
into the two coordinates. Its delta invariant is
$(ab-a-b+\gcd(a,b))/2$, giving the same geometric genus.

Siegel’s theorem now makes the integral intersections of each pair finite.
Each family itself is strictly increasing on its admissible nonnegative
parameter (the coordinate-and-difference recurrence has nonnegative
coefficients in $d=w-4$). The finitely many pairwise intersections account
for only $O(1)$ exceptions.

For the other exceptions there is some row $j\ge101$ at positive parameter
$d$. Its product is at least $d^{2j+1}$: if $x$ is the smaller
half-component and $h$ the difference, $h\ge dx$ at every step, so moving
one step multiplies $x$ by at least $d$. Row 101 contributes at most
$X^{1/203}$ values, and rows 102 onward contribute at most
$O(X^{1/205}\log X)$. Hence **$D(X)=O(X^{1/203})$**. This argument gives
no effective bound on the finitely many low-row intersections. It does
not presume the LMFDB point enumeration. The finite-field certificate is
executable; the part using Riemann–Hurwitz and Siegel is a mathematical
argument outside the Lean verification above.

## Sources and reproducibility

* Abrate, Barbero, Cerruti and Murru, [*The biharmonic mean*](https://arxiv.org/abs/1601.03081), §3 and conclusion: the recurrence and the uniqueness question.
* C. L. Siegel, *Über einige Anwendungen diophantischer Approximationen*, Abh. Preuss. Akad. Wiss. (1929), no. 1, 1–70; [original and English translation](https://doi.org/10.1007/978-88-7642-520-2): finiteness of integral points on affine curves of positive genus.
* F. Pakovich, [*Algebraic curves P(x)−Q(y)=0 and functional equations*](https://pakovich.github.io/y.pdf), Corollary 2.2, and Zhiguo Ding and Michael E. Zieve, [*The relative Riemann–Hurwitz formula*](https://arxiv.org/abs/2103.07921): genus of the normalization of a separated-variable curve. In our disjoint-branch case the two elementary genus calculations are given above.
* The minimal model and [integral-point data for 2432.a1](https://www.lmfdb.org/EllipticCurve/Q/2432/a/1), together with [the LMFDB reliability statement](https://www.lmfdb.org/knowledge/show/rcs.rigor.ec.q).

To check the Lean part, use the pinned Formal Conjectures checkout named in
the manifest included with this supplement. Build
FormalConjectures.Arxiv.«1601.03081».UniqueCrystalComponents, then run
the normal lake env lean command on CrystalDensity.lean. The statements
density_one, fifth_bound, and two_term all depend, as Lean theorems, only
on propext, Classical.choice, and Quot.sound; the latter two have the
cubic/parabolic intersection as an explicit parameter. The attached R3
source proves that parameter from its H2 (the integral-point list).
