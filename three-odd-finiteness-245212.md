# Finiteness with three moving odd primes

For each fixed \(k\ge0\), there are only finitely many odd \(m\) with at most
three distinct prime factors for which \(2^k m\) satisfies the
[A245212 equality](https://oeis.org/A245212). Alternatively, bound just one
odd prime divisor: **all** possible inputs on up to three odd primes then
form a finite set, with the power of two, the other odd primes, and every
odd exponent free. Neither assertion rules out an isolated exception.

The [standalone Lean proof](ThreeOddFiniteResearch245212.lean) starts from
the original OEIS definition and proves both results end to end. Its final
theorems are `OMA.ThreeOddFinite245212.finite_three` and
`OMA.ThreeOddFinite245212.finite_small_prime`. The second follows from
the first since each odd prime divisor \(p\) forces \(k<2p\).

## Why a second prime power must stay bounded

Fix \(k\). Outside a finite set, the [dyadic valuation bound](parity-budget-245212.md)
requires the odd prime powers with bounded base **and** exponent to contribute
more than \(k+v_2(k+1)\) in total. If there are two such factors, fix them.
The last odd prime power is then bounded by the square of the sum of the
two divisor moments of its cofactor.

If only one such factor \(r^a\) is visible, its contribution
\(\max(0,v_2(a+2)-1)\) alone exceeds that threshold. Thus
\(a+2\ge 2^{k+2}\) and \(r^a>W(2^k)\), where
\(W(n)=\sum_{d\mid n}d\tau(d)\). Set \(h=2^kr^a\). For **every** positive
fraction \(U/V\) with \(r\nmid U\),
\[
              \frac{W(h)}{h\tau(h)}\frac UV\ne2.
\]
Indeed equality would imply \(r^a\mid W(2^k)W(r^a)U\).
The prime-power sum \(W(r^a)\) is 1 modulo \(r\), so this contradicts
\(0<W(2^k)<r^a\).

Now suppose the remaining prime powers can escape all bounds. A bounded
exponent vector already permits only finitely many bases (the positive
normalized divisor products strictly decrease as prime bases increase).
Otherwise take a subsequence with the largest exponent tending to infinity
and each base and exponent monotonically varying. The normalized ordinary
divisor-sum product tends to zero. If no additional base and exponent stay
bounded together, each remaining weighted factor tends to 1, or to
\(p/(p-1)\) for a fixed prime \(p\ne r\). Their product has a representation
with numerator coprime to \(r\). The normalized equality at the limit says
exactly that the displayed non-equality fails. Thus a second whole prime
power stays bounded, and the last power is bounded as above.

This argument provides finiteness, without a numerical bound on the
largest three-prime exception. For exactly two odd primes, a
[separate argument](two-odd-global-245212.md) allows \(k\) and the least
odd prime to vary simultaneously.
