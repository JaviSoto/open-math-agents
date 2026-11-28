# Recover a dyadic fraction from its denominator

For a hypothetical A245212 solution with odd part \(m>1\), put
\(x=m\tau(m)-\sigma(m)\) and \(y=W(m)-m\tau(m)>0\), where
\(W(m)=\sum_{d\mid m}d\tau(d)\). The previous dyadic reduction gives
\(k=\lfloor x/y\rfloor\). In lowest terms the fractional part of \(x/y\)
must be \((k+1)/(2^{k+1}-1)\).

Let \(h=\gcd(x,y)\) and \(z=y/h\). From **the denominator \(z\) alone**:

1. Set \(t=\operatorname{lcm}_{p\mid z}\operatorname{ord}_p(2)\), over the distinct prime divisors.
2. Let \(b\) be the largest divisor of \(t\) coprime to \(z\).
3. Form \(N=z(t/b)+1\). It must be a power of two whose binary logarithm is \(t\).
4. The entire required numerator is now prescribed: \(x=(t-1)y+hb\).

The test on \(N\) only uses its own bit length. It does not first construct a
power of two whose exponent is the quotient of the original divisor sums.
For example, \(z=21\) gives orders 2 and 3, hence \(t=6,b=2,N=64\);
the only reconstructed ratio is \(107/21\). Conversely \(z=23\) has
order 11 but yields \(N=24\), so it cannot be the entire denominator.

**Why the numerator is determined.** Write \(D=2^t-1,G=\gcd(D,t)\).
The [prime-support theorem](mersenne-prime-support-245212.md) says that
\(z=D/G\) has the same prime divisors as \(D\) and that their orders
recover \(t\). The reduced numerator \(P=t/G\) is coprime to \(z\).
Every divisor of \(t\) coprime to \(z\) is coprime to \(G\) too, so
it divides \(P\). This proves \(b=P\). Now \(z(t/b)+1=D+1\).

[Standalone Lean proof](MersenneFractionInverseResearch245212.lean),
declaration `OMA.MersenneFractionInverse245212.recover`. Run
`lake env lean /path/to/MersenneFractionInverseResearch245212.lean` in the
project's pinned Formal Conjectures checkout. This reconstruction leaves
open whether any nonsquare odd cofactor actually has the prescribed numerator.
