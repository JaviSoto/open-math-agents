# Two dyadic progressions suffice for Fonollosa’s conjectured bound

Let a finite subset of a cyclic group be **valid** if its all-ones multiset is uniquely determined among multisets on that set by its cardinality and sum. Put \(f(n)=2^n-2^{\lfloor\log_2 n\rfloor}\).

**Theorem.** Suppose some translate of a valid \(n\)-set in \(\mathbb Z/N\) splits into two disjoint progressions
\[
     x,2x,\dots,2^{L-1}x;\qquad y,2y,\dots,2^{b-1}y,
     \qquad L\ge b\ge1,\qquad L+b=n .
\]
All displayed labels are distinct. There is no assumption about the missing successors of the two progressions. Then \(N\ge f(n)\).

For \(n\ge10\), there is an inverse statement: if \(N<2^n-1\), then either the translated set is closed under doubling, or \(n\) is even, \(N=2^n-2\), and the set consists of a complete cycle and a single involution. In particular, at \(N=f(n)\) the only such set for \(n\ge10\) is the canonical one up to an affine automorphism, by the [closed-orbit classification](affine-doubling-classification.md). An arbitrary valid set need not be covered by two progressions. The unrestricted problem remains open.

### A test for a competing multiset

Translation preserves validity. Work with the displayed translated labels. Write \(W=2^L, H=2^b\), and \(s(u)\) for the number of ones in the binary expansion of a nonnegative integer. Let
\[
 \Lambda=\{(i,j)\in\mathbb Z^2:ix+jy=0\},\qquad
 D=[\mathbb Z^2:\Lambda]=|\langle x,y\rangle|\le N.
\]
The canonical word has integer coordinates \((W-1,H-1)\) before mapping to the group. Given any different nonnegative pair \((a,c)\) in this coset, express \(a\) and \(c\) by their respective binary denominations, whose largest coins are \(W/2,H/2\). If this takes at most \(n\) coins and \(a+c\ge n\), repeatedly split a coin larger than 1 into two halves. The resulting word uses exactly \(n\) coins. It cannot equal the canonical multiset because the labels are distinct and its integer coordinate pair differs. Thus such a pair is forbidden. For \(0\le d<W\), the number \(W-1-d\) costs \(L-s(d)\) coins; adding a copy of \(W\) costs at most two more coins. The corresponding statements hold for \(H\).

We prove the inverse result for \(n\ge10\) assuming \(N<WH\), with the slight distinction at \(N=WH-1\) stated below. In this range \(W>2n\): this holds at \(n=10,11\), and both parities follow on increasing \(n\) by two.

### The only collision inside the rectangle

There is no kernel element \((i,-j)\) with \(0<i<W, 0<j<H\). Indeed, the displaced target \((W+i-1,H-j-1)\) costs at most
\[
     2+s(i-1)+b-s(j)\le 2+(L-1)+b-1=n,
\]
and its first coordinate alone is at least \(W\ge n\). There is also no nonzero vertical displacement \((0,j)\), \(0<j<H\): subtract it from the target, at most \(n\) coins suffice and the first coordinate is \(W-1\ge n\).

The \(WH\) points of the integer rectangle \(R=\{0,\ldots,W-1\}\times\{0,\ldots,H-1\}\) take at most \(D<WH\) values. Every nonzero difference of two congruent points is consequently, up to sign, of the form
\[
                   e=(p,q)=(W-u,H-v),\quad p>0,\quad q\ge0 .
\]
Here \(u,v\ge1\). The negative displacement gives coordinates \((u-1,v-1)\), using at most \(n\) coins by binary expansion. Thus \(u+v\le n+1\). In particular \(p\ge W-n>W/2\). This oriented displacement is unique: for two different ones their difference is another nonzero in-box kernel vector, but its first coordinate has absolute value less than \(W/2\). The only repeated pairs in \(R\) are therefore translates of \(e\). There are \(uv\) of these, and no fiber has more than two points since \(2p>W\). Hence
\[
                         WH-uv\le D< WH.\tag{1}
\]

**Horizontal case.** If \(q=0\), then \(v=H\) and \(\operatorname{ord}(x)=p=W-u\): a proper positive divisor would be another forbidden displacement. Adding \(p\) to the first coordinate costs at most \(2+L-s(u)\) coins there, with \(b\) in the other coordinate, so \(s(u)\le1\). Thus \(u=2^t\), \(t<L\). The first path contains a full cycle of length \(L-t\). From \(2^b+2^t\le n+1\) we get \(b+t\le n/2\) for all \(n\ge10\): for \(n\ge20\) use \(b,t\le \log_2 n\le n/4\); smaller values are included in the finite check below. The [long-cycle theorem](long-doubling-cycles.md) now gives \(N\ge f(n)\); if \(N<2^n-1\), its [structural refinement](long-cycle-shape.md) gives the asserted inverse conclusion.

### The lattice basis forces both successors

Suppose \(q>0\). The vector \(e\) is primitive **in the lattice**: a proper integral divisor in \(\Lambda\) would give another in-box displacement. It extends to an oriented basis \(e,(-m,h)\) of \(\Lambda\), normalized by \(0\le m<p\) by adding multiples of \(e\) to the second vector. For completeness, express \(e\) in any basis of the rank-two lattice. Its two coefficients are relatively prime by primitivity, so Bézout gives a second column with determinant one. The index formula gives \(D=ph+qm\). By (1),
\[
          D\ge pH+uq>pq,
\]
and thus \(h>0\). In fact \(h\ge H\): if \(h<H\), the second vector gives an interior mixed-sign displacement for \(m>0\) or a vertical one for \(m=0\). Put \(h=H+j\). Then \(p j<uH\). The elementary inequalities verified below give \(pq>uH\), hence \(j<q\). The other lattice vector \((p+m,-(v+j))\) has negative coordinate of magnitude less than \(H\). It must have \(p+m\ge W\); write \(m=u+i\), \(i\ge0\). We have proved
\[
              D=WH-uv+p j+q i,qquad pj+qi<uv.\tag{2}
\]

In fact \(i=j=0\). If \(i>0\), add \((W+i,-(v+j))\) to the canonical target. The first coordinate costs at most \(4+s(i-1)\) coins, the second \(b-s(v+j)\). Here \(v+j<H\). The sum of the coordinates exceeds \(n\), and \(4+s(i-1)\le L+1\), a numerical bound below. This contradicts validity. If \(j>0\), add \((-(u+i),H+j)\); the costs are \(L-s(u+i)\) and \(4+s(j-1)\). Again \(4+s(j-1)\le b+1\) and the sum of the coordinates is at least \(n\). This is also impossible.

The two boundary vectors are therefore \((W,-v)\) and \((-u,H)\). The first produces a word using \(n+2-s(v)\) coins; the second one uses \(n+2-s(u)\). In both cases the sum of the coordinates is at least \(n\). Thus \(u\) and \(v\) are powers of two. In the original cyclic group \(W x=v y\) and \(H y=u x\): the last element of each path doubles into the other path. The whole set is doubling-closed, and the earlier classification gives \(N\ge f(n)\) and its equality case. There is also a direct lower bound from (2): \(D=WH-uv\), and if both \(u,v\) were even the basis would lie in \(2\mathbb Z^2\), forcing the cyclic quotient to surject onto \((\mathbb Z/2)^2\). Hence one is 1, and \(uv\le n\) is a power of two.

### Numerical inequalities and the small cases

For \(n\ge20\), \(W\ge 2(n+1)^2\) by induction on the two parities. As \(uv\le(n+1)^2/4\), we have \(p=W-u>uv\), and also \(p>u(1+v/q)=uH/q\). Thus (2) gives \(j=0, i<uv\le W/8\), so \(s(i-1)\le L-3\) whenever \(i>0\). The second boundary shift has coordinate sum \(W-1-u+2H-1\ge n\). For the horizontal case, the elementary inequality \(2^{n/4}\ge n\) for \(n\ge16\) follows at 16 and then by monotonicity of \(2^{n/4}/n\).

For \(10\le n<20\) the following integer check verifies exactly the auxiliary inequalities in the proof. It uses the deficit parameters, not residue sets or equivalence classes.

```python
for n in range(10, 20):
    for b in range(1, n//2 + 1):
        L = n-b
        W, H = 2**L, 2**b
        for t in range(L):
            if H + 2**t <= n+1:
                assert 2*(b+t) <= n
        for u in range(1, n+1):
            for v in range(1, min(H, n+2-u)):
                p, q = W-u, H-v
                assert p*q > u*H
                for i in range((u*v-1)//q + 1):
                    for j in range((u*v-1-i*q)//p + 1):
                        assert not i or 4+(i-1).bit_count() <= L+1
                        assert not j or 4+(j-1).bit_count() <= b+1
                        assert i <= W and j <= H
                        assert W-1-u-i + 2*H+j-1 >= n
```

For \(2\le n\le9\), the lower bound without any structural assumption is known from [Fonollosa](https://arxiv.org/abs/2607.08366) and [Sitjar](https://doi.org/10.5281/zenodo.24228247). The small cases do not enter the \(n\ge10\) inverse statement. The binary coin observation is also used by Fonollosa. The lattice collision classification here concerns freely chosen disjoint progressions, not the one prescribed progression in his main theorem.
