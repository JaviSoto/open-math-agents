# How often can a ratio of four occur?

Let $A(n,k)=(n+1)\cdots(n+k)$. Write $S(T)$ for the number of integers $0\le n\le T$ for which **there exist** a length $k\ge2$ and an upper start $m\ge n+k$ satisfying $A(m,k)=4A(n,k)$. We prove that, for an absolute constant $C$,

$$S(T)^9\le C(T+1)^4.$$

In particular, $S(T)/(T+1)\to0$. This counts all lengths together and includes arbitrarily large starts. It does **not** settle whether any solution exists.

### Why a lattice-point estimate applies

For one length $k$, consider two solutions with different lower starts $n_1,n_2$ and gaps $d_i=m_i-n_i$. Their line segment has a strictly smaller product ratio in its interior. To see this, put $h(t)=\log(1+1/t)$, which is strictly convex for positive $t$. A solution satisfies

$$\sum_{i=1}^k h((n+i)/d)=\log4.$$

At an interior point $(n,d)=a(n_1,d_1)+b(n_2,d_2)$, with $a+b=1$, each $(n+i)/d$ is the weighted mean of the endpoint values with weights $ad_1/d,bd_2/d$. At least one pair of those endpoint values differs: equality at both $i=1,2$ would force identical endpoints. Strict convexity gives the claim. Because the ratio increases with $d$, an actual intermediate solution must lie strictly above the chord. Thus the ordered integer points $(n,m)$ form a strictly concave chain.

Next center both blocks: $Y=2n+k+1$, $X=2m+k+1$, $\alpha=4^{1/k}$. Pair the offsets $j,-j$ in the centered products. Each pair contributes a correction factor

$$\frac{1-j^2/X^2}{1-j^2/Y^2}.$$

The corrections are at least one, giving $X/Y\le\alpha$. Since $1-\alpha^{-2}\le2\log4/k$, bounding the same corrections above gives $0\le\alpha Y-X\le8k/Y$ when $Y\ge2k$. Consequently, when $U\le n\le2U$ and $k\le U$, the lattice chain lies in a strip of horizontal length $O(U)$ and vertical width $O(k/U)$.

### How many integer points fit?

In a strip of length $L$ and vertical width $h$, a strictly concave chain of integer points has $O(1+(Lh)^{1/3})$ points. Subtract the center line and divide the horizontal and vertical coordinates by $L,h$. The sum of the normalized horizontal steps is bounded; the sum of the absolute vertical steps is also bounded because their slopes decrease and change sign at most once. If there are $s$ edges, at least half have both normalized step sizes $O(1/s)$. In angle order, consecutive selected vectors span disjoint triangles with the origin, each of area at least $1/(2Lh)$: their original determinants were nonzero integers. All these triangles lie in a rectangle of area $O(1/s^2)$. It follows that $s^3=O(Lh)$, up to an absolute additive constant for short chains.

There are therefore $O(1+k^{1/3})$ admissible starts of length $k$ in this range of $n$. The separate arithmetic restriction $k^3\le C_0(n+1)$ follows from the prime-power transfer between blocks. Sum over $k=O(U^{1/3})$ to get $O(U^{4/9})$, and then over dyadic $U$. Small starts and the finitely many small lengths are included by enlarging the constant. The formal proof uses ninth-power endpoints to avoid rounding fractional exponents.

The single Lean source is [Erdos686Four.lean](Erdos686Four.lean). Its final declarations are OMA.CountStarts686.count and OMA.CountStarts686.density_zero; it also contains the earlier cubic starting-point bound and the length-ten exclusion. All four declarations include an axiom audit.
