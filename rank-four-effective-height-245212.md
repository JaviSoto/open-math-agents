# A computable height for four odd prime factors

For each fixed nonnegative integer $k$, every solution of the [A245212 equation](https://oeis.org/A245212) of the form $2^k m$, with $m$ odd and supported on exactly four different primes, is at most an explicitly computable integer. The primes and their exponents are unrestricted. This proves finiteness at each $k$; it neither excludes all four-prime solutions nor bounds $k$ itself.

Here is the bound. For natural numbers $A,S,r$, define:

    b₀(A) = 1
    bⱼ₊₁(A) = max(2 bⱼ(A), (2 + 2 A 2ʲ bⱼ(A))^(j+1))
    E(A,S,r) = bᵣ(A) (2 A r 2ʳ + 2 S)

For $B,r$, set $C=2B^3+1$, $E=E(C,C,r)$ and $J(B,r)=B[1+\max(E+1,rC(C+1))]^E$. The bound on the original integer is

    envelope(J(J(2^k,4),3)).

The [two-free-prime theorem](two-free-effective-245212.md) defines `envelope` by integer arithmetic and proves it works for every cofactor up to the supplied bound, even when the limiting Euler product equals its target.

For the first two steps, an exact Euler product at a prefix $h$ would force $h\mid W(h)$, where $W(h)=\sum_{d\mid h}d\tau(d)$. The [dyadic and one-odd-prime arguments](rank-three-effective-height-245212.md) exclude that obstruction. They select two whole prime powers successively. At odd rank $r+2$ this leaves an odd cofactor of rank $r$ with the absorbed prefix at most $J(J(2^k,r+2),r+1)$. Apply the two-free-prime theorem at $r=2$.

The [standalone Lean file](RankFourEffectiveResearch245212.lean) proves the arbitrary-rank first-two-step statement `OMA.RankFourEffective245212.two_atoms` and the four-prime bound `OMA.RankFourEffective245212.original`. From the project's pinned Formal Conjectures checkout run `lake env lean /absolute/path/to/RankFourEffectiveResearch245212.lean`. The original-input theorem passed with the standard three axioms and no numerical search input.
