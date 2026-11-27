# The five-factor case of Erdős 686 at quotient four

Put X=m+3, Y=n+3 and P(x)=x⁵−5x³+4x. The integer question is whether
P(X)=4P(Y) can hold for Y≥3 and X−Y≥5. The following are necessary
arithmetic conditions and a rank obstruction to a proposed method. They
do not decide whether any admissible integral point exists.

## Two congruences whose moduli grow with the putative solution

Write X=ga, Y=gb with g>0, gcd(a,b)=1. Then

1. **The cubic direction:** `a³−4b³ | 60(Y¹²−4)`, and more precisely
   `a³−4b³ | 60(a−bY⁴)`. Thus no prime p>5, p≡5 (mod 8), can divide
   a³−4b³. The same exclusion holds for p=5 to powers ≥25. Indeed, modulo
   any such p, Y¹²=4 would make one of 2,−2 a square, whereas both are
   nonsquares for p≡5 (mod 8).
   Infinitely many genuine cubic residue classes are excluded: every
   prime p≡5 (mod 24) greater than 5 has gcd(3,p−1)=1, so a³=4b³
   has exactly one slope with b≠0 modulo p, and that slope cannot occur.
2. **The linear direction:** there is an integer e with
   `4(a−4b)=g² e` and `e | 240(17Y²−5)`. In particular, at any prime
   p>5 dividing e, one has `17Y²=5 mod p`. This is impossible at p=17
   and at any p where 85 is a quadratic nonresidue. Such primes occur in
   a−4b only to an **even** exponent, since their exponent in g²e is
   exactly twice their exponent in g.

For the first assertion set A=a³−4b³, B=a²−b² and E=a−bY⁴. Dividing the
original equation by g gives

    g⁴(a⁵−4b⁵) − 5g² A + 4(a−4b) = 0.                                (1)

Multiply (1) by b² to obtain `4BE=(g⁴b²a²−5g²b²+4)A`. The identity
`15b⁴=(a²+4ab+b²)B−(a+4b)A` gives `A|60b⁴E`. Since gcd(A,b)=1,
A|60E. Multiplying this congruence by the cofactor in the difference of
two cubes and again using gcd(A,b)=1 gives `A|60(Y¹²−4)`.

For the second assertion the square divisibility is immediate from (1).
Reduce (1) modulo a−4b, using a≡4b, to get
`a−4b | 60g² b³(17Y²−5)`. Cancel b³ (it is coprime to a−4b), multiply
by 4, and cancel g² using the equality defining e. This proves the
claimed cofactor divisibility. Both full integer divisibilities, their
application to the original length-five block quotient, and the prime
class exclusion p>5 were checked with pinned Lean in
[the Five686 section of the checked source](Erdos686Further.lean).

## The genus-two quotient has Mordell–Weil rank at least four

Let C be the smooth projective curve

    v² = F(t) = 9t⁶+64t⁵−200t³+64t+144.

This is the quotient by simultaneous sign, via t=X/Y: the quadratic in
u=Y² is `(t⁵−4)u²−5(t³−4)u+4(t−4)=0`. For example, t=14/11 lifts to
the nonintegral positive solution (X,Y)=(14/3,11/3), so ruling out every
positive rational point on the original curve is not an available route.

Fix P₀=(0,12) and let P_t have nonnegative ordinate at t=−20,−2,−1,1:
the ordinates are respectively 19308,12,15,9. Write J=Jac(C). To test
the four classes [P_t−P₀] modulo 2, reduce at a good prime p where r,s
are two distinct roots of F. The function (t−r)/(t−s) on C modulo p
has divisor 2(W_r−W_s), where W_r,W_s are its branch points. Evaluation
on a divisor defined over the finite field uses field norms at closed
points. By Weil reciprocity, the quadratic character of this evaluation
is unchanged on principal divisors (move representatives away from
W_r,W_s); it is trivial on doubles. Composing with good reduction gives
a character on J(ℚ)/2J(ℚ). This is also the ratio of the characters of
the two split components in the usual [hyperelliptic 2-descent](https://www.impan.pl/shop/en/publication/transaction/download/product/83397).

The following rows list those characters on the four classes, squared
values encoded as 0 and nonsquares as 1. None of the divisors meets the
chosen branch points modulo the indicated prime.

| p | r | s | −20 | −2 | −1 | 1 |
|---:|---:|---:|---:|---:|---:|---:|
| 37 | 10 | 25 | 1 | 0 | 0 | 1 |
| 37 | 10 | 33 | 0 | 1 | 0 | 1 |
| 43 | 12 | 26 | 0 | 1 | 1 | 0 |
| 101 | 33 | 71 | 0 | 0 | 0 | 1 |

The matrix is invertible over 𝔽₂. Moreover F is irreducible modulo 7,
hence over ℚ. The nonzero geometric 2-torsion classes in genus two
correspond to unordered pairs of the six finite branch points (the
alternative representative is the complementary four-point set).
Transitivity precludes a fixed pair. Thus J(ℚ)[2]=0, and the four
independent mod-2 classes prove rank J(ℚ)≥4. This is a lower bound;
no exact Selmer rank or generators for the full group are asserted.

There is also no elliptic factor hiding inside J: reduction of F at
7, 11, 37 gives squarefree factor degrees (6), (1,5), and (1,1,1,1,2)
respectively. The Galois group therefore acts transitively and contains
a five-cycle and a transposition. A system of nontrivial blocks could
have only 2 or 3 blocks, each of size 3 or 2; the five-cycle must then
fix every block and act trivially on each, an impossibility. In a
primitive group containing a transposition, the graph of all conjugates
of that transposition is connected, since its components form a block
system. Those transpositions generate the full symmetric group.
[Zarhin’s theorem](https://arxiv.org/abs/math/9909052) therefore gives
End(J over ℚ̅)=ℤ and geometric Néron–Severi rank one.

In particular ordinary Chabauty on this projective quotient fails its
rank<genus hypothesis; the familiar projective quadratic-Chabauty
inequality `rank < genus + NS-rank − 1` does not apply either.
This does not rule out Chabauty on covers, other integral-point methods,
or a Mordell–Weil sieve. [five_rank686.py](five_rank686.py) independently
checks all finite matrices, model good reductions, factor types and point
coordinates using only Python's standard library; it does not search for
integer solutions to the original equation.
