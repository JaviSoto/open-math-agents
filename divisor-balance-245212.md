# Fixed prime supports and two mixed families in OEIS A245212

[OEIS A245212](https://oeis.org/A245212) asks whether
$W(n)+\sigma(n)=2n\tau(n)$ holds only for powers of two. Here
$W(n)=\sum_{d\mid n}d\tau(d)$. The unrestricted conjecture remains open.

**Fixed prime supports.** On any fixed finite set of allowed prime bases, there
are only finitely many non-dyadic solutions, even when their exponents are
unbounded. For every prime $p\nmid m$, at most one exponent $e\ge0$ can
satisfy the equality at $mp^e$, apart from the family $p=2,m=1$. The
[proof](fixed-prime-support-245212.md) also gives the general inequality
$W(n)^2\ge n\sigma(n)\tau(n)^2$, implying $\sigma(n)<4n$ at every solution.

**Mixed families with no exceptions.** There is no solution of either form:

- $2^a3^b5^c7^d$ with $a>0$ and $b+c+d>0$;
- $2^a3^bq^c$ with $a,b,c>0$ and any prime $q>3$.

For each prime power use $Y=\sigma(p^e)/((e+1)p^e)$ and
$X=1+(1-Y)/(p-1)$. The equality requires $\prod X+\prod Y=2$.
The certificates subdivide exponent ranges and, in the second family, the
prime range. Each surviving box is excluded by exact rational endpoints.
An absent upper endpoint represents the whole unbounded tail, not a search
cutoff. There are 845 tree nodes in the first certificate and 4,317 in the
second. The kernel checks every leaf; the Python generators are optional.

**Bounding the odd divisor count.** Put $n=2^a m$ with $m>1$ odd and
$t=\tau(m)$. At an equality, $a=O(t\log(2t))$ and
$\log n=O(t^2\log(2t))$, with effective constants.
The [denominator argument](divisor-envelope-245212.md) gives the explicit
inequalities prior to taking logarithms. The Egyptian-fraction identity,
denominator gap, tail and induction steps are formalized; their final
combination and the asymptotic estimates are given on paper.

## Checking the results

[A245212Research.lean](A245212Research.lean) contains the proofs, including
all certificate data. It imports only the original OEIS module. With
[formal-conjectures at 9097e2f](https://github.com/google-deepmind/formal-conjectures/tree/9097e2f90e66d2f6244209cb1c07f7120d17ec53)
and its Lean 4.33.1 dependencies available, run from that checkout:

~~~sh
lake build FormalConjectures.OEIS.245212
lake env lean /path/to/A245212Research.lean
~~~

The full theorems are `OMA.FixedPrimes245212.finite`,
`OMA.Abundance245212.unique_exponent`, `OMA.Smooth245212.mixed`, and
`OMA.Moving245212.mixed_three`. The generators
[smooth_boxes_245212.py](smooth_boxes_245212.py) and
[mixed_three_245212.py](mixed_three_245212.py) reproduce the tables:

~~~sh
python3 smooth_boxes_245212.py --lean-tables
python3 mixed_three_245212.py 3 --lean
~~~

## A bounded-cofactor search

[divisor_balance_245212.cpp](divisor_balance_245212.cpp) examined every
$1\le m\le2{,}000{,}000{,}000$ with every coprime extension $p^e$, $e\ge1$.
There were 102,297,811 candidates in the final $e\ge2$ test and no non-dyadic
equalities. This bounds the **cofactor**, not the candidate integer. A
separate [smooth-cofactor run](divisor_smooth_245212.py) examined 6,011,754
cofactors $1<m\le10^{55}$ with at most three distinct primes, all at most 29;
it found no non-dyadic extensions. These runs are computations, separate
from the Lean theorems.

To see why the exponent and prime can both be searched without arbitrary
cutoffs, put $T=m\tau(m)$, $A=W(m)$, $S=\sigma(m)$,
$D=(e+1)(2T-A)-S$, and $B=eA+S$. For $e=1$ the condition is
$p(4T-2A-S)=A+S$. For $e\ge2$, expanding the two prime-power sums gives

$$Dp^e=Bp^{e-1}+((e-1)A+S)p^{e-2}+\cdots +(A+S).$$

Hence $D>0$ and $B/D<p<B/D+1$: the remaining terms are positive and
their sum after division by $p^{e-1}$ is less than $B/(p-1)$.
Multiplying the original equality by $(p-1)^2$ also gives
$p^e\mid A-S(p-1)$. If the latter integer is nonzero then
$p^{e-1}<A+S$, giving the bit-length cutoff in the search. If it is zero,
$X(m)=(p-1)Y(m)$, so the affine formula in the fixed-support proof shows
that either every exponent works or none does. The programs test this case
separately; the theorem above now rules out a non-dyadic family.

Reproduction (C++17 and Boost headers; the second program uses gmpy2):

~~~sh
c++ -O3 -std=c++17 divisor_balance_245212.cpp -o divisor-balance
./divisor-balance 2000000000 --all-powers
python3 divisor_smooth_245212.py --test --prime-limit 29 --support 3 --digits 55
~~~

## Prior work

Jaroslav Křížek posed the original conjecture. Anmol Sahu's
[dyadic-exponent inversion](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5390)
already gives at most one positive exponent at 2 for any odd cofactor
$m>1$ and is the starting identity of the odd-divisor bound. See also
DomTheDeveloper's [density-zero and totient bounds](https://github.com/google-deepmind/formal-conjectures/issues/8382).
Those results are distinct from finiteness when the allowed prime bases are
fixed. The present note does not assert a proof of the full conjecture.
