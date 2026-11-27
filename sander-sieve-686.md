# Separating two product blocks with a prime of order their length

Put $A(n,k)=\prod_{i=1}^k(n+i)$. All logarithms are natural. There is an
absolute $c>0$ such that every disjoint solution of
$A(n+d,k)=4A(n,k)$, $d\ge k$, with sufficiently large $k$, satisfies

$$
 \log n > c\,\frac{(\log k)^{3/2}}{\sqrt{\log\log k}}.                 \tag{1}
$$

In particular $n/k^A\to\infty$ along witnesses of increasing length,
for every fixed $A>0$. The proof uses a published analytic estimate and
does not assume the existence of a prime in either short block itself.

[All Lean-checked components are in this self-contained file](Erdos686Further.lean),
including the exact final prime obstruction. The analytic argument below is a
paper proof. The earlier [density proof](erdos-686-density.md) is fully
machine-checked. The [elementary transport argument](prime-transport-686.md)
and [conic argument](conic-count-686.md) are independent alternatives.

## A reciprocal-prime estimate

Write $e(t)=\exp(2\pi i t)$. [J. W. Sander, *Prime power divisors of
binomial coefficients*, J. reine angew. Math. **430** (1992), Theorem 2,
p. 13; parameters on p. 2](https://d-nb.info/1211032906/34)
gives, with its single exponent $j=J=1$ and coefficient $h=H=1$,
for real $X\ge P\ge2$,

$$
 \left|\sum_{p\le P}e(X/p)\right|
 \ll \left(P\exp\left[-c_1\frac{(\log P)^3}{(\log X)^2}\right]
              +P^{3/2}X^{-1/2}+P^{5/6}\right)(\log X)^4 .             \tag{2}
$$

Here $p$ denotes a prime and $c_1>0$ is absolute. Negative frequencies
give the complex conjugate. Using the frequency itself as $X$ keeps
Sander's coefficient $h=1$.

## The two fractional parts

The elementary quotient-four bounds, proved in `GapSize686.lean` and
`CubicGap686.lean`, give $n\asymp kd$ and $d\gg k^2$, uniformly for
large $k$. Suppose (1) fails for arbitrarily large $k$, with a positive
$c$ to be fixed. Select such a sequence of witnesses, put $L=\log k$,
and for each prime $10k<p\le20k$ form the point

$$ \bigl(\{n/p\},\{(n+d)/p\}\bigr) \in (\mathbb R/\mathbb Z)^2 . $$

For each fixed nonzero integer frequency pair $(u,v)$, its Fourier
phase has numerator $t=(u+v)n+vd$. If $u+v=0$, then
$|t|=|v|d\gg k^2$. Otherwise $d/n=O(1/k)$, so
$|t|\ge n/2\gg k^3$ for sufficiently large $k$ depending on the
pair. In both cases $X=|t|\le C_{u,v}n$ and therefore eventually

$$
 k^{19/10}\le X,\qquad
 \log X\le 2c\,L^{3/2}/\sqrt{\log L}.
$$

Take $P=10k$ or $20k$. Condition $P\le X$ holds eventually. If
$c_1/(4c^2)>10$, the first term on the right of (2) is
$O(k L^{-10}(\log X)^4)=o(k/L)$, since $(\log X)^4=O(L^6)$.
The other two terms are $O((k^{11/20}+k^{5/6})L^6)=o(k/L)$.
The choice of $c$ is absolute; the point at which each estimate applies
may depend on the fixed integers $u,v$. Subtraction at the two endpoints
thus bounds the prime sum on the band by $o(k/L)$.

The prime number theorem gives $\pi(20k)-\pi(10k)\sim10k/L$.
After division by this cardinality every fixed nonconstant character
therefore has average tending to zero. This proves equidistribution on
the two-torus: for a trigonometric polynomial take its finite Fourier
expansion, then approximate a continuous function uniformly by such
polynomials. In particular a nonnegative continuous function supported in
the open rectangle

$$ (0.96,0.98)\times(0.25,0.50) $$

and nonzero inside it has positive limiting average. For every sufficiently
large witness in the supposed sequence, at least one prime lies in this
rectangle. For that prime the distance from $n$ to the next positive
multiple of $p$ is less than $0.04p\le0.8k$ and greater than zero,
so $p\mid A(n,k)$. The distance from $n+d$ to its next multiple is
greater than $p/2>5k$, so $p\nmid A(n+d,k)$. This contradicts even
$A(n,k)\mid A(n+d,k)$, and proves (1). No varying Fourier-mode cutoff
is needed: the same absolute $c$ works for each fixed frequency.

## Counting and the remaining question

Solving (1) for $k$ gives

$$ k\le \exp\bigl(C(\log(3+n))^{2/3}
                        (\log\log(16+n))^{1/3}\bigr).                \tag{3} $$

Indeed $L\ll\log(3+n)$ already follows from the cubic bound; raise
$L^{3/2}\ll\log n\sqrt{\log L}$ to the power $2/3$ and substitute.
In each dyadic band $D\le n\le2D$ the proved lattice bound in
`LatticeStrip686.lean` and `CountStarts686.lean` allows
$O(1+k^{1/3})$ starts of a given length; for any $k,n$ the upper
start is unique. Summing for $k$ up to (3), then over the $O(\log T)$
bands up to $T$, changes only the constant $C$ in (3). Thus the total
number of witness triples with $n\le T$ is

$$ \le \exp\bigl(C'(\log(3+T))^{2/3}
                        (\log\log(16+T))^{1/3}\bigr)
     = O_\varepsilon((T+1)^\varepsilon)\qquad(\varepsilon>0). $$

This count does not need the six-point conic estimate. It still allows
infinitely many increasingly sparse witnesses and does not decide whether
four is a quotient. The last arithmetic implication, from a prime in the
rectangle to the exclusion of a witness, is independently checked by Lean:
`OMA.SanderSieve686.excludes_four` in `SanderSieve686.lean`. The
reciprocal-prime analytic argument is a written proof, not a Lean
formalization of Sander's theorem.

For context, [Erdős and Straus, *On products of consecutive
integers* (1977), §§2–3](https://combinatorica.hu/~p_erdos/1977-18.pdf)
derive divisibility obstructions assuming either the length is a positive
fraction of the start or the lower block contains a prime. Related use
of reciprocal-prime phases in closely spaced factorial-ratio problems
appears in [Matomäki, Radziwiłł, Shao, Tao and Teräväinen, *Singmaster’s
conjecture in the interior of Pascal’s triangle* (2022), §§3–5](https://arxiv.org/abs/2106.03335).
Their stated multiplicity results concern equal binomial coefficients and
equal falling factorials, rather than the particular fixed-ratio witness
count here.
