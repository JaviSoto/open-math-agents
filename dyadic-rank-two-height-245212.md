# An explicit height for at most two odd primes

Suppose the [A245212 divisor equality](https://oeis.org/A245212) holds at
\(n=2^k m\), where \(m>1\) is odd and has at most two distinct prime divisors.
Set \(T=(k+1)2^k,\ Q=2T(6T+1)+1,\ E=8TQ\). Then
\[
                n\le 4(2^k Q^E)^7 .
\]
This bounds the entire input once **only the dyadic exponent** is fixed. In
particular, the odd primes and both their exponents are allowed to vary. This
differs from the [bound at fixed odd divisor count](divisor-envelope-245212.md):
neither result follows by just fixing the other parameter. The bound is large;
it does not claim that checking a few dyadic exponents resolves all of them.

The [self-contained Lean file](PairHeightResearch245212.lean) imports the
original OEIS definition. Run `lake env lean /path/to/PairHeightResearch245212.lean`
from the pinned Formal Conjectures checkout. Its final theorem is
`OMA.PairHeight245212.bounded`.

Write \(W(h)=\sum_{d\mid h}d\tau(d)\) and \(A=W(2^k)\). The integer \(A\)
is odd, and \(A<2T\). In the two-prime case let \(p<q\) be the odd primes.
The [Euler inequality](two-odd-finiteness-245212.md) and parity give
\(2T(p-1)(q-1)<Apq\); hence \(p\le 6T+1\). If
\(2T(p-1)>Ap\), the same inequality also gives \(q\le 2Tp+1\).
The gap in the integer inequality is at least one, whereas the difference
between the weighted factors and their limiting Euler factors decays with
the exponents. In this case at least one exponent is at most \(2A(p+q)\).
In the other case, parity gives \(2T(p-1)<Ap\), and the weighted
factor for \(p\) alone bounds its exponent by \(2A\). Thus one odd prime
and its exponent are **simultaneously** at most \(Q,E\), respectively.

Take the cofactor \(h\) consisting of that power and \(2^k\) (just \(2^k\)
in the single-prime case). The remaining prime power \(r^j\) satisfies
\(r\mid W(h)+\sigma(h)\) and \(r^j\le |W(h)-(r-1)\sigma(h)|\).
Together these give \(r^j\le (W(h)+\sigma(h))^2\). Direct divisor sums
give \(W(h)+\sigma(h)\le2h^3\). Therefore \(n=h r^j\le4h^7\), as claimed.
