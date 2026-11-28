# A bounded prime power in nonsquare odd cores

Fix the power of two $2^k$ and a bound $K$ on the number of distinct odd
prime factors. There is a finite list of odd prime powers, depending only
on $k,K$, with this property: if $2^km$ satisfies the A245212 equality
and its odd part $m$ is not a square, at least one member $p^e$ of the
list divides $m$ **exactly** ($p^{e+1}$ does not divide it), and
$e\equiv2\pmod4$. Other prime factors and their exponents can be
arbitrarily large in the hypotheses. Earlier work forced such an
exponent without bounding the prime or its exponent.

The standalone [Lean proof](BoundedAtomResearch245212.lean) starts at the
original equality, and its final declaration is
`OMA.BoundedAtom245212.bounded_atom`. It supplies existence of a bound,
not its numerical value or a proof that there are no exceptions.

Write $X(p,e)=W(p^e)/((e+1)p^e)$ and $Y(p,e)=\sigma(p^e)/((e+1)p^e)$.
At equality the product of the $X$ factors plus the product of the $Y$
factors equals 2. For odd $p$, the [local valuation formula](exponent-parity-245212.md)
gives $v_2(X(p,e))=v_2(e+2)-1$. If $e$ is not 2 modulo 4, the rational
$X(p,e)$ therefore admits an odd numerator after cancelling powers of
two. The fixed factor $X(2,k)$ has an odd numerator as well.

Suppose both the largest exponent and the smallest box containing one of
the required $(p,e)$ pairs could escape every bound. Pass to a single
subsequence where every prime and exponent coordinate is nondecreasing.
A prime tending to infinity gives $X\to1$. A fixed prime with exponent
tending to infinity gives $X\to p/(p-1)$. Both limits admit odd
numerators. If both coordinates stabilize, its exponent cannot be 2 modulo
4, by the way the sequence was chosen. Its limit therefore admits an
odd numerator too. Their finite product, including $X(2,k)$, cannot be 2.
But the product of the $Y$ factors tends to zero, since at least one
exponent exceeds the sequence index and $Y(p,e)\le 2/(e+1)$. The
equality gives the contradiction.

This proves that either the exceptional pair lies in a fixed box or all
exponents are bounded. In the latter case only finitely many exponent
vectors occur. For each such vector the normalized score strictly
decreases as the prime bases increase, so its solutions form a finite
antichain by Dickson's lemma. Every nonsquare solution among those
already has an exponent 2 modulo 4 by the parity theorem. Enlarge the
box once to include them.
