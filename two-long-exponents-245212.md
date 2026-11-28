# In rank three, the largest exponent must separate from the middle one

Write a solution of A245212 as \(n=2^k\prod p_i^{e_i}\), with three
distinct odd primes, \(k\ge0\), and positive exponents. Sort the **lengths**
\(e_i+1\) by size and denote the middle and largest lengths by \(M,L\).

**Theorem.** For each fixed \(C\ge1\), all such solutions with
\(L\le CM\) lie below an explicit computable bound \(V(C)\). There is
no restriction on the shortest exponent, which may even stay equal to 1.
Equivalently \(L/M\to\infty\) along any sequence of distinct solutions.
The bound is too large to use as an enumeration of the remaining cases.

Here are two consequences expressed in terms of the prime order. Write
\(p<q<r\) and \(n=2^k p^a q^b r^d\).

- The entire family with \(d\ge\max(a,b)\) is finite and effectively bounded
  by \(V(20)\). Indeed the [independent last-prime ceiling](largest-prime-absolute-245212.md)
  gives \(d+1\le4(a+b)+32\le20(\max(a,b)+1)\).
- For each \(C\ge1\) the condition
  \(\max(a+1,b+1)\le C\min(a+1,b+1)\) also leaves only finitely many
  solutions, with no further condition on \(d\). The same ceiling bounds
  all three lengths by \(20C\min(a+1,b+1)\). The two lower-prime lengths
  both reach that minimum, so \(V(20C)\) bounds the whole integer.

For example \(2^kp^a q^b r^{a+b}\) has only finitely many solutions with
no prescribed primes or upper bound on \(k,a,b\). This does not settle
the sector where an exponent on \(p\) or \(q\) dominates both others.

## Proof

Label the two longer coordinates 0 and 1; the third can be short.
We use the [rounded weighted and ordinary divisor moments](three-moving-exponent-gap-245212.md)
\(X(p,e)=W(p^e)/[(e+1)p^e]\) and \(Y(p,e)=\sigma(p^e)/[(e+1)p^e]\).
For \(k>0\) the following integer separation holds:
\[
 4\max(k,L)<kM \quad\Longrightarrow\quad M<M_0,\qquad
 M_0=64(F+1)^2,\quad F=(16^5+4)16^5 .
\]

The new ingredient is a third option at coordinate 2: keep **both moments
exactly**, with common denominator \((e_2+1)p_2^{e_2}\). At coordinates
0 and 1 we still either drop reciprocal powers (denominator
\((e_i+1)(p_i-1)^2\)) or discard the base (denominator \(e_i+1\)).

Suppose a replaced score equals its integer target. The largest prime
\(q\) at which we dropped reciprocal powers divides both product
numerators. It cannot divide any retained smaller prime minus one.
It cannot divide a power in an exact denominator either, because that
power belongs to a **different prime**. Thus, as before, \(q\le\max(k+1,L)\).
If no reciprocal powers were dropped this restriction is vacuous.

Restoring an exact coordinate changes nothing. Restoring a discarded base
increases its weighted factor strictly and does not decrease its ordinary
factor. In the remaining case, the changes are \((\delta,-(p_i-1)\delta)\)
with \(\delta>0\). Among the *two other* coordinates, at least one has length
at least \(M\). Hence the product of their ordinary factors is at most
\(4/M\), even if the short coordinate has length 2. The weighted factors
are at least 1. The assumed inequality gives
\(4(p_i-1)<kM\) at each retained base, so this restoration also strictly
increases the score. Coordinates 0 and 1 are never kept exactly. The
calculation therefore ends strictly above the hypothesized target, whereas
the true score is at most the target. This rules out equality for every
allowed choice of replacements.

For the error estimate, consider the four numbers
\(p_0,p_1,p_2,p_2^{e_2}\). Among the **five** disjoint intervals
\((x^{16^j},x^{16^{j+1}}]\), \(0\le j<5\), one contains none of them.
Call its endpoints \(Q,Q^{16}\). If \(p_2^{e_2}\le Q\), keep coordinate 2
exactly. Otherwise its power exceeds \(Q^{16}\); drop its reciprocal power
or discard its base according as the base is at most \(Q\) or exceeds
\(Q^{16}\). The other two coordinates obey the same latter rule. When
\(L\le x\le Q\), the exact denominator is at most \(Q^2\), so the total
denominator is still at most \(Q^9\). Only the two long coordinates need
the power bound \(p_i^{e_i}\ge x^{16^5}\). The perturbation estimates and
dyadic choice from the three-coordinate proof now apply with \(16^5\)
instead of \(16^4\). The strict gap is at least \(Q^{-9}\), while the
total error is at most \((48(f+g)+1)/Q^{16}\) for the chosen coefficients
\(f+g\le Q\). If \(M\ge M_0\), the two long powers meet the required bound
for both dyadic coefficient choices, a contradiction.

For \(L\le CM\), either \(k\le4C\), or \(M\le4\), or the separation
hypothesis holds. In the first case sum the [fixed-dyadic rank-three
heights](rank-three-effective-height-245212.md) over \(0\le k\le4C\).
In the other cases \(M\le M_0\), hence the odd part has at most
\((CM_0)^3\) divisors. Summing the [fixed-divisor-count
heights](divisor-envelope-245212.md) through that cutoff bounds the
whole integer. The sum of the two bounds is the function \(V(C)\).

## Replay

[TwoTallResearch245212.lean](TwoTallResearch245212.lean) imports only
the upstream OEIS problem. Four declarations are audited:
**OMA.TwoTallOriginal245212.shortest**, **OMA.TwoTallFinite245212.bounded**,
**OMA.TwoTallConsequences245212.lower_comparable**, and
**OMA.TwoTallConsequences245212.largest_at_largest**. In the pinned Formal
Conjectures checkout run `lake env lean /absolute/path/to/TwoTallResearch245212.lean`.
