# A height bound from integer rounding

Suppose a positive solution to the A245212 equality is not a power of two. Write $n=\prod_{i=1}^k p_i^{e_i}$ with $e_i\ge1$, let $B=\max_i p_i$, and $E=\max_i e_i$. Then $E=O_k(B\log(2B))$. In particular this applies to both even and odd solutions, and is uniform in the bases and the other exponents.

## The two rounded moments

For the normalized local factors $x_i=W(p_i^{e_i})/((e_i+1)p_i^{e_i})$ and $y_i=\sigma(p_i^{e_i})/((e_i+1)p_i^{e_i})$, write $a_i=p_i^{e_i}$, $D_i=(e_i+1)(p_i-1)^2$, and set

$$
 x_i^*=\frac{p_i((p_i-1)(e_i+1)-1)}{D_i},\qquad
 y_i^*=\frac{p_i(p_i-1)}{D_i}.
$$

The exact finite geometric sums give

$$
 x_i=x_i^*+\frac1{D_i a_i},\qquad
 y_i=y_i^*-\frac{p_i-1}{D_i a_i}.
$$

All versions of $x_i$ lie in $[1,2]$ and all versions of $y_i$ in $[0,1]$, since $p_i\ge2$ and $e_i\ge1$.

Round any nonempty set $H$ of factors, leaving $L=H^c$ exact. Write $F=\prod_i x_i+\prod_i y_i$ for the true score, $F^*$ for the resulting rounded score and

$$
 D=\prod_{i\in H}D_i\prod_{j\in L}(e_j+1)a_j.
$$

Then $DF^*$ is an integer. Replacing one rounded pair at a time gives

$$
 |D(F-F^*)|\le \sum_{i\in H}(2^{k-1}+p_i-1)\frac{D/D_i}{a_i}.
$$

For a singleton $H=\{i\}$ the change can be zero only if $W(m)=(p_i-1)\sigma(m)$ at $m=n/a_i$. At a solution the prime-power formulas then give $p_i\sigma(m)=2m\tau(m)$ and $W(m)+\sigma(m)=2m\tau(m)$. The no-resonance lemma (recalled below) makes $p_i=2,m=1$, excluded here.

For larger $H$, a sufficient condition for strictly positive change is

$$
 (p_i-1)\prod_{j\ne i} y_j^*<1\qquad(i\in H).
$$

Indeed the coefficient multiplying $1/(D_i a_i)$ is $\prod_{j\ne i}x_j^{\rm current}-(p_i-1)\prod_{j\ne i}y_j^{\rm current}$; the first product is at least one, and the second is at most the displayed product times $p_i-1$. This condition holds whenever all selected $e_i>2B$: for each $i\in H$ pick another $j\in H$, for which $y_j^*\le2/(e_j+1)<1/B$.

Thus if the change is nonzero and its absolute bound is less than one, $F\ne2$: at an equality $D(F-F^*)=2D-DF^*$ would be an integer.

## An explicit bound on all exponents

Set $C=k2^kB^{2k+1}(E+1)^k$ and $V=B^{2B}$. Begin with $L$ empty and $M=1$. If there is a remaining $i$ with $a_i\le\max(V,CM)$, move it to $L$ and multiply $M$ by $a_i$. At termination either all indices have moved, or every remaining $i$ satisfies $a_i>V$ and $a_i>CM$. The latter is impossible for a solution: $a_i>V$ forces $e_i>2B$, and $D/D_i\le (E+1)^{k-1} B^{2k} M$. The integer-rounding bound is then strictly less than one, with nonzero change by the preceding argument.

Every move takes $M$ to at most $(VC)M^2$. After $k$ moves this gives

$$
 2^E\le n=M\le (VC)^{2^k-1}.
$$

Put $d=k2^k$, $b=\lfloor\log_2 B\rfloor+1$, and

$$
 A=2^k\bigl(k+(\lfloor\log_2 k\rfloor+1)+(2k+1+2B)b\bigr).
$$

Taking logarithms gives $E\le A+d\log_2(E+1)$. In particular $E\le t=\max(256d^2,2A+1)$: otherwise $\log_2(E+1)\le2\sqrt E$ and $2d\sqrt E\le E/8$, whereas $A<E/2$. The logarithm bound follows from $2^z\ge1+z$ for $z\ge1$, applied at $z=\sqrt E$. This proves the asserted order of growth. For numerical work one can repeatedly replace $t$ by $\min(t,A+d(\lfloor\log_2 t\rfloor+1))$.

**No resonance.** For completeness $W(m)^2\ge m\,\sigma(m)\tau(m)^2$ by the prime-power estimate $2W(p^f)\ge(f+1)(p^f+\sigma(p^f))$, the arithmetic–geometric mean inequality, and multiplicativity. Hence $\sigma(m)<4m$ at a positive solution. If also $p\sigma(m)=2m\tau(m)$ and $p\nmid m$, an odd $p$ divides $\tau(m)$ and $\sigma(m)/m$ is a positive even integer smaller than four. It must be two and $\tau(m)=p$. Then $m$ is a prime power, which has $\sigma(m)<2m$. For $p=2$ the relation says $\sigma(m)=m\tau(m)$; summing its divisors gives $m=1$. The accompanying prior Lean development proves these facts in **OMA.Abundance245212.no_resonance**.

The local implementation is **rounding_245212.py**. The height argument in this manuscript is a mathematical proof; formal verification is separate from the already pinned finite-decision and large-prime results.
