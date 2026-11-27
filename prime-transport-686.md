# The quotient-four length exponent and two tests of its sharpness

For a stronger bound using exponential sums over primes, see the separate
[reciprocal-prime sieve](sander-sieve-686.md). The proof below uses only
elementary prime-counting and variance estimates.

Let the two blocks be $n+i$ and $n+d+j$, with $1\le i,j\le k$,
$d\asymp n/k$, and $n=k^{a+o(1)}$. For any prime $p>2k$ dividing one
block there is a unique term in each divisible by $p$, with the same
valuation. Thus the weight $v_p(n+i)\log p$ may be placed at
$(I,J)=(i/k,j/k)$. In particular $p^{v_p(n+i)}$ divides both $d+j-i$
and $2n+d+i+j$.

## A uniform bound with no exponent loss

**Theorem.** There is an absolute $c>0$ such that every disjoint quotient-four
witness satisfies $n+1\ge c k^{a_0}$, where
$a_0=(5+\sqrt3)/2$. The constants in the proof below are independent of the
witness. Only sufficiently large $k$ need consideration: finitely many smaller
lengths are covered by decreasing $c$. If $n>k^4$ the conclusion already holds.
For all remaining witnesses put $L=\log k$ and $a=(\log n)/L$. The earlier
arithmetic bound $n\gg k^3$, and the two elementary product bounds
$n\asymp kd$, give $2.9\le a\le4$ for sufficiently large $k$,
$\log d=(a-1)L+O(1)$ and $\log(2n+d)=aL+O(1)$.

For a block of $r\le2k$ consecutive positive integers $s+1,\ldots,s+r$,
let $V(s,r)$ be the logarithm of the part of their product supported on
primes $p>2k$. For $s\asymp n$ or $s\asymp d$ the bound

$$ V(s,r)=r(\log s-L)+O(k) \tag{1} $$

holds **uniformly** in $r$ and in each of the translations of size $O(k)$
used below. Here and below the empty block has weight zero. To prove (1),
the sum of the logarithms of the $r$ terms is $r\log s+O(k^2/s)$.
The log of the complementary small-prime part is between $\log r!$ and
$\log r!+\pi(2k)\log(s+r)$. Indeed the product divided by $r!$ is a
binomial coefficient, and for each prime $p$ its valuation in that quotient
is at most $\log(s+r)/\log p$: at each prime-power level the multiple counts
in the two intervals differ by zero or one. All primes of $r!$ are small.
Chebyshev's $\pi(2k)=O(k/L)$ makes the excess $O(k)$.
Finally $\log r!=rL+O(k)$ uniformly even for very short blocks, since
$r\log(r/k)=O(k)$ on $0\le r\le2k$ and
$\log r!=r\log r-r+O(\log(2+r))$. These error terms are why no
$\varepsilon$ in the final exponent is necessary.

Place the weight $v_p(n+i)\log p$ on $(I,J)=(i/k,j/k)$ as above, and
divide the resulting measure by its total weight
$W=V(n,k)=k(a-1)L+O(k)>0$. Write $H=J-I$ and $S=I+J$ for random
variables on this finite probability space. For every interval $E$ inside
$[0,1]$, (1) applied to the consecutive lower or upper terms whose
normalized indices lie in $E$ gives

$$ \Pr(I\in E)=|E|+O(1/L),\qquad
   \Pr(J\in E)=|E|+O(1/L). \tag{2} $$

For the upper block this is an equality of its large-prime weights because
the two block products differ only by the factor $4$. Endpoint conventions
change the number of included integers from $k|E|$ by at most two.

For an interval $E\subseteq[-1,1]$, the distinct prime powers assigned
to cells having $H\in E$ divide the product of the consecutive $d+j-i$
under consideration. Even if several cells have the same difference,
their prime powers are coprime; each prime occurs at only one cell.
Consequently their total logarithmic weight is bounded by (1) for that
difference interval. The same argument for $S$ uses the consecutive
$2n+d+i+j$. Thus for *all* intervals $E$, intersecting with the relevant
support when necessary,

$$ \Pr(H\in E)\le M|E|+O(1/L),\qquad
   \Pr(S\in E)\le |E|+O(1/L),\quad M=\frac{a-2}{a-1}. \tag{3} $$

For example the numerator for the first inequality is at most
$k|E\cap[-1,1]|(a-2)L+O(k)$. Since the support has length two and
$a$ stays in a fixed bounded interval, normalizing by $W$ introduces a
uniform additive error $O(1/L)$, independent of $E$.

Here are the finite variance details. Take a common $\delta=C/L$ dominating
the constants in (2)–(3). If a real variable $Z$ satisfies
$\Pr(Z\in E)\le D|E|+\delta$ for intervals, then

$$ \operatorname{Var}(Z)
 =\int_0^\infty 2t\,\Pr(|Z-\mathbb EZ|>t)\,dt
 \ge\int_0^{(1-\delta)/(2D)}2t(1-\delta-2Dt)\,dt
 =\frac{(1-\delta)^3}{12D^2}. $$

On the other hand,
$\operatorname{Var}(I)\le\mathbb E[(I-1/2)^2]\le 1/12+\delta/4$,
by integrating $2t(1-2t+\delta)$ from $0$ to $1/2$ using the *lower*
bound in (2). The same holds for $J$. The identity
$\operatorname{Var}(H)+\operatorname{Var}(S)
=2\operatorname{Var}(I)+2\operatorname{Var}(J)$ now yields

$$ (1-\delta)^3(M^{-2}+1)\le 4+12\delta. $$

It follows that $M\ge 1/\sqrt3-O(1/L)$.
On the compact interval $2.9\le a\le4$ the inverse function
$a=1+1/(1-M)$ has bounded derivative, giving
$a\ge 1+1/(1-1/\sqrt3)-O(1/L)=a_0-O(1/L)$.
Multiplication by $L$ and exponentiation give $n\ge c k^{a_0}$ as claimed.

## Consequences for counting

In a dyadic range $D\le n\le2D$, there are $O(D^{1/a_0})$ possible
lengths. The strict-concavity/lattice-packing proof in
`LatticeStrip686.lean` and `CountStarts686.lean` gives
$O(1+k^{1/3})$ starts at each such length: its centered strip has width
$O(D)$ and height $O(k/D)$ when $k\le n$, as eventually follows from the
length bound. Summing over $k$ and then geometrically over the dyadic ranges
gives $O(T^{4/(3a_0)})=O(T^{4(5-\sqrt3)/33})$ starts up to $T$.

The six-point interpolation argument in [conic-count-686.md](conic-count-686.md)
improves this to

$$ O(T^{1/a_0})=O(T^{(5-\sqrt3)/11}) $$

even for triples $(k,n,m)$. In fact for all sufficiently large $k$ there are
at most five points in *each* $D\le n\le2D$ and fixed $k$; their centered
ordinates range from $2D+k+1$ to $4D+k+1$, a ratio at most two.
The finitely many smaller lengths have a bounded number per band by the
lattice argument, and $m$ is unique for a given $k,n$. The sum over bands
is geometric, so there is no logarithmic factor.

The arithmetic lemmas and determinant components have local Lean proofs.
The full quantitative transport proof and its improved conic-count corollary
here are mathematical proofs; the numerical exponent and their complete
composition should not be described as kernel-checked.

## Sharpness of the four projections

The projection optimization
cannot be improved by enforcing additional fixed primitive integer directions
alone. Let $Z$ be uniform on the ordinary unit sphere in three dimensions,
let $u,v$ be unit vectors with $u\cdot v=-1/2$, and put
$I=(1+u\cdot Z)/2$, $J=(1+v\cdot Z)/2$. Each linear projection of $Z$ is
uniform on an interval of width twice the norm of its direction (sphere bands
have area proportional to their vertical height). Consequently $I$ and $J$
are uniform on $[0,1]$, $I+J$ is uniform on $[1/2,3/2]$, and $J-I$ is
uniform on $[-\sqrt3/2,\sqrt3/2]$. Both variance lower bounds are attained.
For every nonzero integer pair $(b,c)$, $bI+cJ$ is uniform on an interval
of width $\sqrt{b^2-bc+c^2}\ge1$. All projected congestion bounds from fixed
primitive directions therefore hold, including the strengthened one for $J-I$.

## An independent restriction on large matched prime factors

For lattice pairs $(x,y)$ in
$[N,N+K]\times[D-K,D+K]$ with $\gcd(x,y)\ge B$, assume
$0<K$, $0<B$, $2K\le D\le N$ and $KD\le6N$. All their reduced slopes
$x/y$ have denominator $\le Q=(D+K)/B$. Distinct slopes differ by at least
$1/Q^2$. Their range is contained in
$[N/(D+K),(N+K)/(D-K)]$, whose length times $Q^2$ is

$$ \frac{K(2N+D+K)(D+K)}{(D-K)B^2}\le \frac{12NK}{B^2}. $$

On any fixed ray, distinct ordinates differ by at least one, so abscissae
differ by at least $N/(D+K)\ge K/9$. There are at most ten pairs per ray.
This proves

$$ \#\{(x,y):\gcd(x,y)\ge B\}\le10(1+12NK/B^2). $$

The full statement is kernel-checked: `OMA.FareyMass686.pairs` in
`FareyMass686.lean`. Apply it to $(x,y)=(n+i,d+j-i)$, with
$N=n$, $K=k$, $D=d$. Each pair accounts for $O_a(1)$ primes exceeding $k$,
and each such prime contributes at most $O_a(\log k)$ logarithmic mass.
Consequently, for any fixed $\varepsilon>0$, the total mass of primes
$p>n^{1/2+\varepsilon}$ is $o(k\log k)$. The same conclusion holds
for matched prime powers or products of matched primes attached to a single
pair when their combined value exceeds this threshold.

This estimate alone does **not** exclude a witness or improve the variance
exponent. For example, at the threshold $a=(5+\sqrt3)/2$, an analytic
result giving a positive proportion with a prime factor $>n^{1/2+\varepsilon}$
in every interval of length $k=n^{0.297\ldots+o(1)}$ would contradict
it. The uniform short-interval theorems I found did not reach this range:
[Ramachandra's primary account](https://m.mathnet.ru/links/e71267bb47fa771f948e5cf82dcd0c89/tm3206.pdf)
proves a smaller power of $k$ for the existence of a large factor;
[Merikoski](https://arxiv.org/abs/1805.05123) obtains a much larger factor
in intervals of roughly square-root length. An almost-all interval result
cannot directly be applied to the unknown witness starts.
