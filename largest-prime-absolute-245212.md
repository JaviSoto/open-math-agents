# The largest odd prime has exponent at most \(4(a+b)+31\)

Suppose \(3\le p<q<r\) are primes, \(a,b,d\ge1\), and
\(n=2^kp^a q^b r^d\) satisfies A245212. Then
\[
                 d\le 4(a+b)+31.
\]
The primes and all four exponents can vary independently. In particular the largest
prime cannot carry, say, a hundred times the combined exponents of the other
two. No ordering of the exponents is required.

Combined with the [quadratic separation theorem](three-moving-exponent-gap-245212.md),
this gives an effective bound on the whole integer whenever
\(\max(a+1,b+1)\le c\,\min(a+1,b+1,d+1)^2\), for any fixed \(c\).
Indeed \(d+1\le 20\max(a+1,b+1)\). If \(d\ge\min(a,b)\), the comparison
needs only \(a,b\) and places no upper bound on \(d\). The factor 20 and the
constant 31 are convenient bounds in the proof, not optimized constants.

## Proof

Write \(h=p^a q^b,\ A=W(h),\ S=\sigma(h),\ T=h\tau(h)\), where
\(W(h)=\sum_{v\mid h}v\tau(v)\). Write \(u=r-1,\ R=r^d,\ G=2^{k+1}-1\),
and
\[
        B=(d+1)u^2,\qquad X=r((d+1)u-1),\qquad Y=ru .
\]
The last prime has exact moments \(u^2W(r^d)=XR+1,\ u^2\sigma(r^d)=YR-u\).
Keep both lower-prime moments exact and introduce the integer
\[
        J=(k+1)TB-kAX-SY.
\]
Multiplicativity in \(W(n)+\sigma(n)=2n\tau(n)\), together with
\(W(2^k)=1+k2^{k+1}\), gives the exact integer identity
\[
 G R J= G U +(k+1)A+R V,\quad
 U=kA-uS,\qquad V=(k+1)(AX-TB).
\]
Here \(0<T\le A,\ 2S\le A,\ X\ge B\), so \(V\ge0\).
For the second bound one may check \(3\sigma(z^e)\le2W(z^e)\) at each positive
prime power: it holds for \(e=1\), and the recursions
\(\sigma(z^{e+1})=z\,\sigma(z^e)+1,\ W(z^{e+1})=zW(z^e)+\sigma(z^{e+1})\)
preserve it. Use this at both odd primes.

Suppose \(d>4(a+b)+31\); write \(s=a+b\). The last-power divisibility
argument gives the auxiliary ceiling
\[
        5^k\le r^j\quad\Longrightarrow\quad d\le j+s+1.
\]
This is **LargestPrimeExponent245212.triple_of_power**, included in the source.
It follows by bounding \(W(2^k)\le5^k\) and \(W(z^e)\le(z+1)^{e+1}\),
then using the nonzero discrepancy divisible by \(r^d\) at the largest prime.
Since \(r\ge5\), take \(j=k\) to get \(d+1\le 2k\). If
\(2^k<r^{s+10}\), then \(5^k\le(2^k)^3<r^{3(s+10)}\). Applying the ceiling
again would give \(d\le4s+31\). Consequently \(r^{s+10}\le2^k\).

The reciprocal-sum estimate \(k<2r\) now implies
\(k+1,\ d+1\le r^2\). We also have \(A\le r^{s+2}\) by the prime-power
bound above and \(X,B\le r^4\). Thus
\[
   4\bigl(|U|+(k+1)A\bigr)\le r^{s+6}\le R,\qquad
   4V\le 4(k+1)(AX+TB)\le r^{s+10}\le G .
\]
If \(J\) were a nonzero integer, the left side \(GRJ\) would have
absolute value at least \(GR\), but these bounds put the right side
between \(-GR/4\) and \(GR/2\). Thus \(J=0\).

As \(r\mid X,Y\), this forces \(r\mid(k+1)TB\). Since \(r\nmid h(r-1)\)
and \(\tau(h)=(a+1)(b+1)\), the prime \(r\) divides at least one of
\(k+1,a+1,b+1,d+1\). All are at most \(2k+1\) in the current case.
It follows that \(uS\le2kS\le kA\), so \(U\ge0\). Now the right side
of the integer identity is positive because \((k+1)A>0\); its left
side is zero. This contradiction proves the bound.

## Verification

[LargeLastResearch245212.lean](LargeLastResearch245212.lean) imports only
the upstream OEIS problem. Its main declarations are
**OMA.LargeLastOriginal245212.largest** and **OMA.LargeLastSector245212.bounded**.
Run Lean from the pinned Formal Conjectures checkout:
`lake env lean /absolute/path/to/LargeLastResearch245212.lean`.
