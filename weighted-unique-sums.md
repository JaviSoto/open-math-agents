# Minimum cyclic moduli for prescribed multiset sums

Fix a positive multiplicity for each of finitely many labels in an abelian group. We require the prescribed multiset to be the only multiset of the same size having its group sum. We compute the minimum cyclic modulus for **every choice of positive multiplicities on three labels**. In any number of labels we determine exactly when a cyclic group attains the abelian minimum: the minimum multiplicity must occur at most twice.

## Statement

Write the prescribed counts as \((m,w_1,\ldots,w_d)\), with \(1\le m\le w_i\), and put
\[
S=m+\sum_{i=1}^d w_i,\qquad D=\prod_{i=1}^d(w_i+1).
\]
A tuple \((a_0,\ldots,a_d)\) in \(G\) is **valid** if the only nonnegative integers \(x_0,\ldots,x_d\) satisfying
\[
\sum_{i=0}^d x_i=S,\qquad \sum_{i=0}^d x_i a_i=m a_0+\sum_{i=1}^d w_i a_i
\]
are the prescribed counts. With positive counts, validity forces the labels to be distinct: moving one copy between equal labels would otherwise give a rival.

**Theorem 1.** The least possible order of a finite abelian group admitting a valid tuple is \(D\). The cyclic group of order \(D\) admits a valid tuple if and only if at most one of \(w_1,\ldots,w_d\) equals \(m\).

**Theorem 2.** Given three positive counts \((m,u,v)\) with \(m=\min(m,u,v)\), the least cyclic modulus is
\[
\begin{cases}
(m+1)(m+2), & m=u=v,\\
(u+1)(v+1), & \text{otherwise}.
\end{cases}
\]
For equal counts the labels \(0,1,m+2\) attain the minimum.

For example, counts \((2,3,3)\) admit the labels \((0,1,4)\) modulo \(16\), the minimum order. The two radices are both \(4\); coprimality is unnecessary. For counts \((2,2,2)\), the abelian minimum is \(9\), attained in \((\mathbb Z/3)^2\), and the cyclic minimum is \(12\), attained by \(0,1,4\).

## Proof of Theorem 1

Translate all labels by \(-a_0\), and write \(g_i=a_i-a_0\) for \(i>0\). Translation preserves equality of sums for tuples of equal size. The pivot count \(x_0\) is now determined by the other counts. Thus validity says that
\[
\sum_{i=1}^d x_i\le S,\qquad \sum_{i=1}^d x_i g_i=\sum_{i=1}^d w_i g_i
\quad\Longrightarrow\quad x=w.
\tag{1}
\]

**A box of distinct sums.** Let \(B=\prod_i\{0,\ldots,w_i\}\) and \(\phi(b)=\sum_i b_i g_i\). If \(\phi(b)=\phi(c)\), interchange \(b,c\) if necessary so that \(\sum b_i\le\sum c_i\). Then \(x=w-c+b\) is nonnegative, has sum at most \(\sum w_i\), and has the target group sum. By (1), \(b=c\). Hence \(|G|\ge |B|=D\).

In \(G=\prod_i\mathbb Z/(w_i+1)\), take \(g_i=e_i\). Any \(x\) giving the target satisfies \(x_i\equiv w_i\pmod{w_i+1}\), so \(x_i\ge w_i\). Any strict increase costs at least \(w_i+1>m\), contrary to the budget in (1). This attains the lower bound.

**What equality forces.** Suppose \(|G|=D\). The box map is now onto. For each \(i\) with \(w_i=m\), write \((m+1)g_i=\phi(b)\) with \(b\in B\). If \(b\ne0\), then \(x=w-b+(m+1)e_i\) has sum at most \(S\) and group sum \(\phi(w)\). It differs from \(w\), since \(b_i\le m\). This contradicts (1). Consequently
\[
(m+1)g_i=0\quad\text{whenever }w_i=m.
\tag{2}
\]
If there are \(t\) such indices, (2) defines a homomorphism \((\mathbb Z/(m+1))^t\to G\) sending its coordinate generators to their labels. Injectivity on the box makes the homomorphism injective. For \(t\ge2\) this subgroup cannot lie in a cyclic group: a cyclic group has at most \(m+1\) elements killed by \(m+1\), whereas this subgroup has \((m+1)^t\). This proves necessity.

**A cyclic construction.** Suppose at most one nonpivot weight equals \(m\). When \(d=0\), the trivial group suffices. Otherwise, reorder the nonpivot labels so that \(w_i>m\) for \(i<d\). Put \(B_i=w_i+1\), \(b_1=1\), and \(b_i=B_1\cdots B_{i-1}\) for \(i>1\). Use labels \(0,b_1,\ldots,b_d\) modulo \(D\). Their prescribed sum is \(D-1\) by telescoping.

For a rival \(x\), ordinary mixed-radix division gives nonnegative integral carries \(t_0=0,t_1,\ldots,t_d\) such that
\[
x_i+t_{i-1}=w_i+B_i t_i\qquad(1\le i\le d).
\]
Indeed, reduce \(\sum_i b_i x_i\equiv D-1\) modulo \(B_1\) to obtain \(x_1=w_1+B_1t_1\); divide the remaining congruence by \(B_1\) and repeat. At each step the required remainder is \(B_i-1\). Summing these equations yields
\[
\sum_i x_i-\sum_i w_i=\sum_{i<d} w_i t_i+(w_d+1)t_d.
\]
Every coefficient on the right is bigger than \(m\). The left side is at most \(m\), so every carry vanishes. It follows that \(x=w\). This proves sufficiency. \(\square\)

## Proof of Theorem 2

The unequal case follows from Theorem 1. Suppose all three counts are \(m\), put \(q=m+1\), and translate the labels to \(0,a,b\). Write \(F(i,j)=ia+jb\). The square \(\{0,\ldots,q-1\}^2\) has distinct images by the box argument. The following comparison will be useful: if \(F(i,j)=F(u,v)\), then
\[
m+i-u\ge0,\quad m+j-v\ge0,\quad (i+j)-(u+v)\le m
\quad\Longrightarrow\quad (i,j)=(u,v).
\tag{3}
\]
Indeed \((m+i-u,m+j-v)\) is an admissible rival in (1).

Now suppose \(|G|<q(q+1)\). The rectangle \(\{0,\ldots,q\}\times\{0,\ldots,q-1\}\) contains more than \(|G|\) points. Its last column also has distinct images, since the first column does. Hence some \(F(q,j)=F(u,v)\) with \(u,v,j<q\). If \(u\ge1\), apply (3) to \((u,v)\) minus \((q,j)\), a contradiction. Thus \(u=0\). If \(v>j\), apply (3) in the opposite direction. Consequently \(v\le j\) and \(qa+h b=0\) for \(h=j-v\), where \(0\le h<q\). Interchanging the axes yields \(qb+k a=0\), with \(0\le k<q\).

If \(h,k>0\), subtract the two relations to get \((q-k)a=(q-h)b\), contrary to injectivity on the square. If \(h=0<k\), then \(qa=0\) and \(qb=(q-k)a\). This is another forbidden coincidence: use (3) with \((i,j)=(0,q)\) and \((u,v)=(q-k,0)\). The case \(k=0<h\) is symmetric. Thus \(qa=qb=0\). All \(q^2\) box sums then lie in the \(q\)-torsion of \(G\). A cyclic group has at most \(q\) such elements, and \(q\ge2\). This rules out every smaller cyclic group.

For the upper bound set \(B=m+2\) and use \(0,1,B\) modulo \(qB\). A rival satisfies \(x+By\equiv m+Bm\bmod qB\). Reducing first modulo \(B\) gives \(x=m+Bt\) with \(t\ge0\); cancellation then gives \(t+y=m+qs\) with \(s\ge0\). Hence \(x+y=2m+q(t+s)\). Since \(x+y\le3m\) and \(q>m\), both carries vanish. \(\square\)

## Relation to earlier work

José A. R. Fonollosa’s [*Minimum modulus for the unique multiset-sum problem*, §8](https://arxiv.org/html/2607.08366v2#S8) lists weighted and rectangular variants together as Problem 3, mentioning rectangular matrices and rows with different supports. It does not prescribe a particular multiplicity vector or ask the cyclic-attainment question above. The theorems here treat fixed positive counts with a common set of available labels. They do not determine the minimum cyclic order with four or more labels when three or more counts are minimal, or treat mixed row supports. The paper’s Problem 4 instead fixes every count to one and varies the finite abelian group. [Michael Inal](https://doi.org/10.17605/OSF.IO/C58Q9) solved that case, including its equality classification; [Fonollosa’s updated repository](https://github.com/jarfo/min-modulus#open-problem-4-all-finite-abelian-groups) records the result and its formalization. The box injection and (2) extend the two steps of Inal’s argument to unequal counts. In additive-combinatorial language, the box injection is properness of a generalized arithmetic progression ([Tao–Vu](https://arxiv.org/abs/math/0701005)); for all ones it is ordinary dissociation.

There is also an older source for the numerical lower bound. Over \(\mathbb C\), average
\[
\chi(-m a_0-\textstyle\sum_i w_i a_i)
  \big(\chi(a_0)X_0+\cdots+\chi(a_d)X_d\big)^S
\]
over all characters \(\chi\) of \(G\), where the sum in the character runs over the nonpivot indices. Orthogonality and validity leave only a nonzero multiple of \(X_0^m\prod_i X_i^{w_i}\). Its complex Waring rank is therefore at most \(|G|\). [Carlini, Catalisano and Geramita, Corollaries 3.3 and 3.8](https://arxiv.org/html/1110.0745#S3) identify that rank as \(D\) and give a roots-of-unity decomposition corresponding to the product group. Fonollosa’s [companion paper, §2.4](https://arxiv.org/html/2607.09949v2#S2.SS4), treats finite-group orthogonality for the permanent, whose prescribed multiplicities are all one.

The minimum-weight restriction also has an algebraic interpretation. In the [complete-intersection theorem of Buczyńska, Buczyński and Teitler](https://arxiv.org/html/1201.2922#S1), a minimum nonpivot exponent has its own equation \(\alpha_i^{m+1}=c_i\alpha_0^{m+1}\) on the projective points of a minimal decomposition. In a normalized character orbit the identity character gives \(c_i=1\). The equations for all characters then imply (2). The elementary proof above gives the cyclic criterion directly and exhibits its realizing labels. None of these observations settles Fonollosa’s all-ones global cyclic optimality conjecture.

For related Fourier formulas for matrices with repeated rows and columns, see [Chabaud, Deshpande and Mehraban, equations (43) and (54)](https://arxiv.org/abs/2208.00327). Those formulas use grids of roots of unity. The three-label question here asks for the smallest order of a *single cyclic* encoding that isolates one prescribed coefficient.

**Formalization.** [WeightedModulus.lean](WeightedModulus.lean) proves the three-label minimum as a least positive modulus (`three_weights_minimum`), the general cyclic equivalence (`homogeneous_cyclic_iff`), and the abelian lower bound and attaining group (`homogeneous_abelian_minimum`). The file imports Mathlib. All three declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
