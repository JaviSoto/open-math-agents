# A245212 through 71 odd divisors

For $n=2^k m$ with $m$ odd and $\tau(m)\le71$, the A245212 equality holds exactly when $m=1$. The [previous computation](odd-tau36-245212.md) proves this through 53. Here the first case is $\tau(m)=54$, whose four-prime patterns are the four permutations of $(1,2,2,2)$. The computation checks exact integer arithmetic; it does not give an unrestricted solution of A245212.

## A residue of the exceptional prime

When exactly one odd prime $q$ has odd exponent, the [exact two-adic order theorem](exponent-parity-245212.md) gives one congruence on $q$ at every fixed $k$. Let $s$ be the number of odd prime factors, $D=\sum_i v_2(e_i+2)-s$ and $H=1+k+v_2(k+1)$. The sole contribution to $U$ in that theorem is $v_2(q+1)-1$. If $D=H$ then $U>H$; if $D\ne H$ then $U=\min(D,H)$. The first case says $q=-1\bmod2^{H+2}$, the second says
$$q=2^{1+\min(D,H)}-1\pmod {2^{2+\min(D,H)}}.$$
For the four-prime profiles at 54, $D=2$. At $k\ge2$, the unique first-power prime must be $7\bmod16$. For the profile $(2,1,2,2)$ this reduces the total widths of the surviving penultimate-prime intervals from 172,297,251,878 to 1,913,400,053, before the sieve below.

## Projecting out a prime over a finite field

Use the notation of the previous paper: $P$ is an odd prefix with moments $A=W(P)$, $S=\sigma(P)$; $G=2^{k+1}-1$ and $F=1+k2^{k+1}$. The last pair of bases is $x<y$ with positive exponents $a,b$. Write
$$w_e(z)=\sum_{j=0}^e(j+1)z^j,\qquad s_e(z)=\sum_{j=0}^e z^j.$$
The necessary equality is
$$Tx^a y^b=FA\,w_a(x)w_b(y)+GS\,s_a(x)s_b(y),\qquad T=(F+G)\tau(m)P.$$
For any auxiliary prime $\ell<x$ both bases are nonzero in $\mathbf F_\ell$. Precompute the following images, once per $\ell,b$:
$$I_u=\{u\,w_b(z)z^{-b}+s_b(z)z^{-b}: z\in\mathbf F_\ell^\times\},\qquad
I_\infty=\{w_b(z)z^{-b}:z\in\mathbf F_\ell^\times\}.$$
For a candidate residue $x\ne0$, put $A_x=FA\,w_a(x)$ and $S_x=GS\,s_a(x)$. If $S_x\ne0$, a nonzero $y$ exists exactly when $Tx^a/S_x\in I_{A_x/S_x}$. If $S_x=0$ but $A_x\ne0$, use $Tx^a/A_x\in I_\infty$. If both vanish, require $Tx^a=0$. All three branches are exact, including at primes dividing the dyadic moments or $t$.

For long intervals above 97, [the implementation](odd_tau54_245212.py) builds one bit pattern for each of the 24 odd primes from 3 to 97. Bit $i$ in a period records the permitted residue $2i\bmod\ell$. Rotating the bytes by $\mathrm{start}/16\bmod\ell$ aligns its first bit to the odd lower endpoint; subsequent bits then represent $\mathrm{start},\mathrm{start}+2,\ldots$. Intersecting the patterns checks up to $2^{18}$ odd integers at once without storing an array indexed by the full prime bound. A surviving $x$ is tested with $2^{x-1}=1\bmod x$. This step is only a necessary condition: a pseudoprime may cause another arithmetic check, but no prime is lost. The final original equation is always checked for each digit passing divisibility. At a true solution both large bases are prime, as assumed in the congruence proof. Short intervals and intervals starting at or below 97 use the original Eratosthenes sieve.

## Reproduce

Keep [odd_tau54_245212.py](odd_tau54_245212.py), [odd_tau36_245212.py](odd_tau36_245212.py) and [odd_divisor_count_245212.py](odd_divisor_count_245212.py) together. No third-party Python modules are needed.

    python3 odd_tau54_245212.py --self-test
    python3 odd_tau54_245212.py --t 54 --through 71 --audit --jobs 4

The self-test makes 480 comparisons against a direct double loop over finite-field residues and tests every bit alignment in each example. For final exponents one and two it also makes 960 comparisons against independent linear and quadratic root criteria. The preceding arithmetic self-tests run as well.

At 54 the 17 surviving ordered profiles use every $k=0,\ldots,1287$. From 55 through 71 the 45 further profiles are distributed as $56:8$, $60:13$, $62:2$, $65:2$, $66:10$, $70:10$. Other divisor counts in this interval have no surviving ordered profile after the exclusions in the previous paper. Every profile uses its own full exponent ceiling. The `--audit` option expands both divisor sums independently for every final divisibility survivor; a candidate equality terminates the command with an error.

The combined run completed all 62 profiles. It checked 24,735,881 final digits and expanded 1,201 divisibility survivors. It also considered 13,551,702 surplus values on the boxes handled by the polynomial method; 436,785 survived modular screening and required exact root tests. No candidate equality survived. The [standalone Lean module](TailProjection245212.lean) proves the cofactor identity, nonzero finite-field witness, common reduced surplus, and linear elimination algebra from the original problem or, for the final algebraic lemma, from the two surplus equalities. The exhaustive search itself is in Python.
