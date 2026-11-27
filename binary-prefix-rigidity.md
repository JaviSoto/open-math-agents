# A binary prefix cannot be extended to beat the conjectured modulus

Write $f(r)=2^r-2^{\lfloor\log_2 r\rfloor}$. Suppose $r\ge6$ and $r$ of the $r+1$ labels in a cyclic group form an affine copy of $1,2,4,\ldots,2^{r-1}$: they are $a+b2^j$, $0\le j<r$. The step $b$ need not be a unit. **No choice of the last label gives a valid set below $f(r+1)$.** For a unit step, any valid extension at a modulus below $2^{r+1}$ must add exactly $a+b2^r$.

Validity means that the sum of all the labels has no other representation by the same number of labels with repetitions allowed. [Fonollosa](https://arxiv.org/html/2607.08366v2) proves that the full binary family first works at $f(r+1)$. Here we allow the last label to vary freely and the step to be a nonunit. We do not settle the conjecture for sets with no such prefix.

**Binary coins.** With denominations $1,2,\ldots,2^{r-1}$ the minimum number of coins summing to $L\ge0$ is $\lfloor L/2^{r-1}\rfloor+\operatorname{popcount}(L\bmod 2^{r-1})$. Splitting a coin into two halves realizes every count between that minimum and $L$. Validity is affine invariant. Subsets of valid sets stay valid: a rival extends by appending the omitted labels once.

**Unit step.** Normalize the old labels to the binary coins, and write $0\le y<N<2^{r+1}$ for the new label. Their sum is $2^r-1+y$. A representation of any congruent integer by $r+1$ old coins is already a rival because it omits $y$.

For $y<2^r$ the sum needs at most $r+1$ coins: if it is at least $2^r$, subtract two top coins; the remainder is below $2^r-1$ and has at most $r-1$ one-bits. Below $2^r$ the binary expansion suffices directly. The total is at least $r+1$, so splitting gives a rival. Thus $y\ge2^r$.

Now $L=2^r-1+y-N$ is nonnegative and below $2^r$, and uses at most $r$ coins. Escaping another rival requires $L<r+1$. In particular $y=2^r+t$ with $0\le t\le r+1$. If $t>0$, the unwrapped sum is $2^{r+1}+t-1$. Use four top coins and at most $\lceil(t-1)/2\rceil\le r-3$ coins worth 1 or 2 for the remainder, then split. That leaves only $y=2^r$. See the [Lean proof](BinaryPrefix.lean).

The Lean theorem actually proves this unit-step assertion for every $r\ge4$. Its threshold is sharp: $\{1,2,4,11\}$ works modulo 15 when $r=3$. Both the extension theorem and this example use the original validity predicate.

**Nonunit step.** Translate away $a$ and set $g=\gcd(b,N)$, $M=N/g$. The old labels sit in the order-$M$ subgroup in primitive binary position. By their validity and Fonollosa's binary-family theorem, $M\ge f(r)$. If $g\ge3$, then $N\ge3f(r)\ge f(r+1)$ since $2^r\ge3r$. Suppose therefore $g=2$ and $N<f(r+1)$. If the last label is even, divide all labels by two and apply the unit-step result and Fonollosa's theorem inside the subgroup. Otherwise it is odd.

Normalize the even labels to $2(2^j-1)$ for $0\le j<r$; units modulo $M$ lift to odd units modulo $2M$. Call the odd label $h$. Put $P=2^{\lfloor\log_2 r\rfloor}$ and $s=2^r-M$. If $r+1$ is a power of two, then $f(r+1)=2f(r)$, a contradiction. Otherwise $P/2<s\le P$. Consider the old binary coins inside their subgroup (translate back from coins-minus-one). Their sum $2^r-1$ is congruent to $2^{r+1}-1-s$, whose minimum coin count is $r+2-\operatorname{popcount}(s)$. If $s$ had at least two one-bits this could be split into $r$ coins. The unwrapped sum differs by $M$, so this is not the prescribed multiset. Hence $s$ is a power of two and must be $P$. In particular $M=2^r-P$ is even.

A rival with three odd labels needs $r-2$ even ones. Put $V=2^r-1-r$ and $L=((V-h)\bmod M)+r-2$, taking the least nonnegative residue. Any representation of $L$ by $r-2$ binary coins gives that rival: subtract one from each coin, double the results and add three copies of $h$. Here $L$ is even and $r-2\le L<2^r+r$. Below $2^r$, every even integer except $2^r-2$ has at most $r-2$ one-bits. At or above $2^r$, use two top coins and at most $\lfloor(r-1)/2\rfloor\le r-4$ twos for the even remainder. By splitting, only $L=2^r-2$ can escape. Therefore $h\equiv-1\bmod M$.

The two odd lifts of $-1$ differ by multiplication by the unit $M+1\bmod 2M$, which fixes the even labels. Take $h=-1$ and translate every label by one. The result is exactly $0,1,3,\ldots,2^r-1$, Fonollosa's extremal binary family of size $r+1$, which cannot work below $f(r+1)$. This completes the nonunit argument on paper.
