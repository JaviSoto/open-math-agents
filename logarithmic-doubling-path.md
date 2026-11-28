# One logarithmic doubling path forces the conjectured modulus

Let \(A\) be a valid \(n\)-element subset of \(\mathbb Z/N\), \(n\ge2\): its all-ones word is the unique length-\(n\) multiset on \(A\) with sum \(\sum A\). Suppose that for some \(x,t\), the \(L\) points \(2^j x-t,\ 0\le j<L\), are distinct and belong to \(A\).

**Theorem.** If \(2^L\ge16n(n+15)\), then \(N\ge2^n-2^{\lfloor\log_2 n\rfloor}\). No cycle, assumptions on the other \(n-L\) labels, or divisors of \(N\) are required. More precisely, if \(N<2^n\), the given path can be continued inside \(A\) until it returns to an earlier path member. The resulting cycle has length \(r\) with \(2^r\ge16(n+15)\), so the [logarithmic cycle classification](logarithmic-doubling-cycle.md) applies.

Translate by \(t\); write \(P=\{x,2x,\ldots,2^{L-1}x\}\), \(B=A\setminus P\), \(k=n-L\), \(W=2^L\), and \(v(S)=\sum_{b\in S}b\) for \(S\subseteq B\). We may assume \(N<W2^k\).

### Coin reserve

The integer sum of the binary weights in the path is \(W-1\). If \(T\subseteq B\) and an exterior multiset \(m\) obey
\[
              v(T)=\sum m+jx,
\]
we can replace \(P\cup T\) by \(m\) and a representation of \(W-1+j\) in the binary coins \(1,2,\ldots,W/2\). Whenever that amount is at least \(n\) and its initial coin count plus \(|m|\) is at most \(L+|T|\), split coins until equality of lengths. Validity passes to subsets by retaining all omitted labels once. It follows that \(m=T\) as multisets, because the replacement's exterior portion must coincide with the original exterior portion.

For \(|j|\le W/8\) the initial coin count is at most \(L\), and it is at most \(L-1\) if \(j\ne0\). For negative \(j\) the ordinary digits of \(W-1-|j|\) complement those of \(|j|\); for positive \(j\) use two coins of size \(W/2\) and the digits of \(j-1<W/8\). Thus whenever \(|j|\le W/8\) equality above implies \(m=T\) if \(|m|\le |T|\). This is the only local rigidity property needed for comparing good gaps.

### Exterior masks form separated starts

The values \(v(S)\) are distinct. This follows from the preceding test at \(j=0\), placing the smaller of two subsets on the multiset side. In the translation order \(z\mapsto z+x\), every positive distance between two mask starts (including a return to the same start) is at least \(W-n\). Indeed, suppose \(v(T)=v(S)+jx\) with \(0<j<W-n\). If \(|S|<|T|\), the amount \(W-1+j\) takes at most \(L+1\) coins: use two top coins, then at most \(L-1\) bits for \(j-1<W-1\). If \(|S|\ge|T|\), reverse the relation and use \(W-1-j\ge n\) with at most \(L\) coins. Consequently \(S=T\), which is impossible because \(\mathrm{ord}(x)\ge W-L\ge W-n\). The order bound follows from validity of the single path and [the binary coin lower bound](DyadicDigits.lean).

On each translation orbit (a coset of \(\langle x\rangle\)) meeting the mask starts, match each start to the next one, wrapping around. This gives a permutation \(F\) of the \(2^k\) masks and positive gaps \(m_S\) satisfying
\[
                v(F(S))=v(S)+m_Sx,\qquad
                m_S\ge W-n,\qquad
                \sum_S m_S\le N.
\]
The length sum counts the occupied orbits once each, including orbits with just one start. Mark a source good if \(m_S\le W+W/16\) and write \(H\) for the number of bad sources. The gap sum implies
\[
               (W/16)H<n\,2^k.
\]
Differences of any two good gaps have absolute value at most \(n+W/16\le W/8\).

### A missing endpoint forces too many bad gaps

Suppose \(Wx\) has no squarefree representation on \(A\). For a good pair \(S\mapsto T=F(S)\) write \(d=|T|-|S|\). The coin reserve at \(j=m_S\) shows \(d\le1\): if \(d\ge2\), use the amount \(W-1+m_S\) with at most \(L+2\) coins. For \(m_S\le W\) use two top coins and the digits of \(m_S-1\); for \(m_S=W+e>W\) use four top coins and the digits of \(e-1<W/16\), costing at most \(L\). In the latter case the same argument excludes \(d\ge0\) unless \(S=T\). In that equality case the replacement uses at least four copies of the top coin and every extension to the canonical path is impossible: the total ordinary path weight is \(W-1+m_S>W-1\), while the actual canonical word \(P\) has ordinary weight exactly \(W-1\). The identical observation also excludes every equality of a nonzero reserve offset when both exterior words coincide, as long as the replacement exists.

Every good source has \(U=S\setminus T\ne\emptyset\). If \(S\subseteq T\) and \(m_S\le W\), then \(Wx=(W-m_S)x+v(T\setminus S)\) has a squarefree representation using the path digits. If \(m_S>W\), the preceding stricter gain bound excludes inclusion.

We apply the Boolean lower-neighbor count from [the cycle proof](logarithmic-doubling-cycle.md); the following two direct verifications account for the unequal gaps.

* Let \(R=S\setminus\{i\}\), \(i\in S\setminus F(S)\), with both rows good. Then \(v(F(S))=v(F(R))+i+(m_S-m_R)x\). If \(|F(R)|+1\le|F(S)|\), local rigidity identifies the multiset \(F(R)+\{i\}\) with the set \(F(S)\), impossible since the latter omits \(i\). Hence the gain at \(R\) strictly exceeds the gain at \(S\).
* If \(S_i=R\cup\{i\}, S_j=R\cup\{j\}\) are different good sources with equal gains, where \(i\notin F(S_i)\), \(j\notin F(S_j)\), then \(j\in F(S_i)\). Otherwise \(F(S_i)\cup\{j\}\) is squarefree and has the same cardinality as \(F(S_j)+\{i\}\); their group values differ by \((m_{S_i}-m_{S_j})x\). Local rigidity identifies these two multisets, a contradiction by membership of \(i\).

The [kernel-checked counting lemma](CubeNeighbors.lean) therefore gives \(2^k\le(k+15)H\). Together with the gap estimate this contradicts \(W\ge16n(k+15)\). Hence \(Wx\) has a squarefree representation. [The subset-successor lemma](PathSuccessor.lean) makes it either zero or an actual label. If \(Wx=0\), the order of \(x\) divides \(W\) and is at least \(W-n>W/2\), so equals \(W\). The spacing \(W-n>W/2\) then allows at most one mask start in each coset, forcing \(W2^k\le N\). Thus \(Wx\) is a label.

Apply this extension repeatedly along the given path until its first repeat, say \(2^M x=2^a x\), \(a<M\); all \(M\) earlier terms are distinct. The threshold stays true because the path grows and the total \(n\) is fixed. The transient length obeys \(2^a\le M\): validity of the \(M\)-term path gives \(\mathrm{ord}(x)\ge2^M-M\), while that order divides \(2^M-2^a\). Its cycle length \(r=M-a\) satisfies \(2^r\ge W/n\ge16(n+15)\). The logarithmic cycle theorem gives the stated bound and classification.
