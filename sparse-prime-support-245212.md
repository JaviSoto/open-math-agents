# How close the prime divisors of a counterexample must be

Suppose a positive integer satisfies the OEIS A245212 equality. Write it as
\(n=2^k m\) with \(m\) odd and \(m>1\). Count each prime dividing \(m\) only once.

* If \(n\) is odd, it has two prime divisors \(p<q<2p\). In particular, no odd integer greater than one made up entirely of Mersenne primes can satisfy the equality. The same holds for Fermat primes, including any yet to be discovered.
* More generally, if every pair of odd prime divisors \(p<q\) satisfies \(q>2p\), the least odd prime divisor is at most \(2k+1\). If every such pair satisfies \(q\ge (p-1)^2+1\), the bound is \(k+2\).
* For any positive integer \(P\) no larger than the least odd prime divisor, some interval \([2^jP,2^{j+1}P)\) contains **strictly more** than \(P/(2(k+2))\) odd prime divisors. For odd inputs the threshold is \(P/4\). There is no bound on the number of factors or their exponents in these statements.

**Argument.** The Euler-product necessity gives \(2\le X_2(k)\prod_{p\mid m}p/(p-1)\). From the weighted sum at a power of two we get \(X_2(k)\le 2(k+1)/(k+2)\). For successively doubled primes, the Euler factors telescope under the envelope \((p+1)/(p-1)\), with strict inequality at the last prime. For successively squared shifts, use \((p-1)/(p-2)\). Mersenne primes satisfy the first separation condition; Fermat primes satisfy the second.

The complement of the product of \(1-1/p\) is at most \(\sum_{p\mid m}1/p\). The Euler inequality thus implies \((k+2)\sum_{p\mid m}1/p\ge1\). If every dyadic interval contained at most the claimed threshold, the sum over the finitely many occupied intervals would be strictly smaller than \(1/(k+2)\), by a geometric series.

**Replay.** Extract the [29-module source archive](prime-support-geography-245212.tar.gz). From the pinned Formal Conjectures checkout at `9097e2f90e66d2f6244209cb1c07f7120d17ec53`, use `lake env python3 /path/to/PrimeSupportGeography245212/lean_source_bundle_245212.py --workers 4`. The main declarations are `OMA.SeparatedPrimeSupport245212.odd_original`, `OMA.PrimeDensity245212.original`, and the two explicit odd-input exclusions in `OMA.PrimeSupportGeography245212`.
