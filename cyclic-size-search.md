# The eight-label cyclic minimum

For eight distinct labels in a cyclic group, the smallest modulus for which the sum of the eight labels has just one representation by eight labels (allowing repetitions and ignoring order) is **248**. At that modulus there is exactly one valid set up to translation and multiplication by a unit:

$$\{0,1,3,7,15,31,63,127\}\pmod {248}.$$

This is an exhaustive computer result, not a Lean theorem. [Fonollosa, §7](https://arxiv.org/html/2607.08366v2#S7) reports exact certification up to seven labels and search evidence through thirteen. The paper already proves the specified binary set works at the predicted minimum for all sizes; what is being checked here is the exclusion of **all other sets below that modulus**, and uniqueness at the extremal modulus.

## How the search covers all sets

1. Every subset of a valid set is valid: a competing multiset on a subset could be extended by one copy of every remaining label. Translation and multiplication by a unit preserve validity.
2. For a full set in $\mathbb Z/N$, let $g$ be the least $\gcd(b-a,N)$ over its distinct pairs. Translate a pair realizing $g$ to $0,b-a$. Multiplication by a unit sends $b-a$ to $g$: after dividing by $g$, invert the residue modulo $N/g$, lifting the inverse to a unit modulo $N$ by the Chinese remainder theorem. No other residue of the image is strictly between $0$ and $g$. The program visits every divisor $g<N$ and extends $(0,g)$ in increasing order, retaining only differences with gcd at least $g$.
3. Among all these normalized copies we can take the lexicographically least sorted tuple. At any partial prefix, a normalization of its members to a smaller sorted prefix disproves minimality: adding the future members to that image can only decrease its first entries. Comparing all affine normalizations whose distinguished pair is already present is therefore valid pruning; it leaves exactly one representative of every full orbit.
4. For each prefix $A$ we store $B_j(A)$, all residues that are sums of exactly $j$ members of $A$ with repetition. The zero pivot implies $B_j\subseteq B_{j+1}$. When adding $t$, use $B_j(A\cup\{t\})=B_j(A)\cup(t+B_{j-1}(A\cup\{t\}))$. If $|A|=r$ and $V=\sum A$, a rival using $t$ exactly $h$ times exists iff $V+(1-h)t\in B_{r+1-h}(A)$. Check $h=0,2,\ldots,r+1$; at $h=1$ the old prefix already has a unique representation.

There is also an optional pruning inequality implemented in the source. In any full valid tuple containing 0, the subset sums of all nonzero labels are distinct: replace the larger of two equal-sum subsets by the smaller and fill the shortfall with zeros. For a prefix of size $r$, consider every subset $U$ of the $n-1$ nonzero labels which uses at least one future label. None of their distinct sums can be in $B_j(A)$ when $j\le|U|+1$; otherwise replace $U$ and the zero pivot with old labels, padding with zeros. If the complement of $B_j(A)$ contains too few residues for this count, no completion is possible. An earlier run without this inequality gave the same eight-label minimum and orbit count.

## Reproduction

The [C++ search](cyclic_min_modulus.cpp) uses fixed-width Boost.Multiprecision bitsets. A one-bit rotation by an appropriate offset implements translation in the cyclic group. The [independent Python check](cyclic_crosscheck.py) directly enumerates multisets and affine orbits for every size 2 through 6 and every corresponding modulus up to 17. It also directly tests all rival multisets for the extremal examples at sizes 2 through 9.

```sh
c++ -std=c++17 -O3 cyclic_min_modulus.cpp -o cyclic-min
python3 cyclic_crosscheck.py ./cyclic-min
./cyclic-min 8 8 247 --first
./cyclic-min 8 248 248 --orbits
```

On Homebrew add `-I/opt/homebrew/include` if Boost is not on the compiler's include path. Each modulus below 248 prints `NONE`; modulus 248 prints `ORBITS 1`. Smaller moduli than eight do not have eight distinct residues. The unrestricted size conjecture remains open.
