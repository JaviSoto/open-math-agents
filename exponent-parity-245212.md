# An exponent obstruction for A245212

Write a positive integer as \(n=2^a m\), with \(m=\prod_{i=1}^r p_i^{e_i}\) for distinct odd primes. Suppose \(n\) satisfies the divisor identity from [OEIS A245212](https://oeis.org/A245212). Then

\[
                 2^r\ \mid\ \prod_{i=1}^r(e_i+2).
\]

This has no restriction on the number or sizes of the primes, or on the power of two in \(n\). In particular, if the odd part is not a square, at least one odd prime has exponent **2 mod 4**. Thus no solution has a nontrivial squarefree odd part. More generally, a solution with a nonsquare odd part cannot have all odd prime exponents odd or multiples of four.

Write \(\tau,\sigma\) for the number and sum of positive divisors, and define \(W(n)=\sum_{d\mid n}d\tau(d)\). The original identity says \(W(n)+\sigma(n)=2n\tau(n)\). These three divisor functions are multiplicative. Let \(v(x)\) count the factors of two in a positive integer. For every odd prime \(p\), and \(t=e+1\),

\[
 v(W(p^e))+1=v(t)+v(t+1),\qquad 2^{v(t)}\mid\sigma(p^e).
\]

For the first identity, consider a block of \(N=2^{h+1}\) terms in the weighted geometric sum \(\sum_{j=0}^{t-1}(j+1)p^j\). Its weighted sum is \(2^h\bmod N\); its ordinary geometric sum vanishes modulo \(N\). Since \(p^N=1\bmod N\), appending full blocks adds their weighted sums modulo \(N\). If \(t=uN\) with \(u\) odd, the result has valuation exactly \(h\). If \(t\) is odd, apply this result to \(t+1\) and remove the last term: \((t+1)p^t\) is zero modulo the resulting \(N\). The ordinary block congruence gives the second assertion.

Now put \(T=\sum_i v(e_i+1)\). Both \(\sigma(n)\) and \(2n\tau(n)\) are divisible by \(2^T\), hence so is \(W(n)\). Since \(W(2^a)\) is odd, \(v(W(m))\ge T\). Summing the local weighted identity gives \(v(W(m))+r=T+\sum_i v(e_i+2)\), proving the divisibility. If some \(e_j\) is odd, its contribution to this last sum vanishes; another contribution must then be at least two.

DomTheDeveloper’s earlier [LeftToSolve reduction #1376](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1376) already proved the equivalent exponent inequality for all inputs, including odd ones. The independent block proof here states it directly as a divisibility and extracts the 2-mod-4 corollary. This is a necessary condition; it does not settle A245212.

The standalone [Lean proof](ParityResearch245212.lean) starts from the original Formal Conjectures definition. The main results are `OMA.ExponentParity245212.exponent_product` and `two_mod_four`. Both replay with only the three standard Lean axioms.

## The exact orders and a sum-of-two-squares test

Let \(E=\sum_i v(e_i+2)\), \(U=\sum_{e_i\text{ odd}}(v(p_i+1)-1)\), and \(H=1+a+v(a+1)\). The coarse lower bound above can be sharpened:

| Comparison | Necessary value of \(E\) |
| --- | --- |
| \(U<H\) | \(r+U\) |
| \(U>H\) | \(r+H\) |
| \(U=H\) | strictly greater than \(r+H\) |

In particular, **the odd part \(m\) of a solution is a sum of two squares if and only if \(E=r\)**. For example, no solution can have odd part \(p^{2j+1}q^{8b+2}u^4\), where \(p,q\) are distinct odd primes, \(p=3\bmod4\), and \(u\) is odd and coprime to both. Here \(E=r\), yet the prime \(p\) has odd exponent so the odd part is not a sum of two squares. Such inputs pass the earlier exponent inequality.

To see the sharper test, the ordinary geometric sum on \(p^e\) has order \(v(e+1)\) for even \(e\), and \(v(e+1)+v(p+1)-1\) for odd \(e\). The latter follows by applying the two-adic lifting-the-exponent formula to \(p^{e+1}-1=(p-1)\sigma(p^e)\). In the original balance, subtracting \(T\) from the orders of the weighted sum, ordinary sum and right-hand side gives \(E-r,U,H\), respectively. If two integer summands have unequal orders, their sum has the smaller order. Equal orders cancel at least one more factor of two. This gives all three rows. Since \(H>0\), equality \(E=r\) is equivalent to \(U=0\): every prime congruent to 3 modulo 4 has even exponent. This is precisely the sum-of-two-squares criterion.

The [standalone Lean file](OrdersResearch245212.lean) proves the table and its sum-of-two-squares equivalence from the original equation. [Reduction #18129](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/18129) uses the table and a reduced Mersenne denominator to narrow the nonsquare branch. The surviving cases remain open.

## Recovering the power of two from a denominator

For an even solution with odd part \(m>1\), write \(n=2^k m\). Put \(A=m\tau(m)\), \(x=A-\sigma(m)\) and \(y=W(m)-A>0\). Then **the denominator of \(x/y\) in lowest terms determines \(k\)**. More precisely, if \(D=y/\gcd(x,y)\), the first positive exponent \(j\) for which \(2^j=1\pmod D\) is exactly \(k+1\).

[Anmolspace’s reduction #5390](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5390) gives \(k=\lfloor x/y\rfloor\) and \(2^{k+1}(x-ky)=x+y\). Write \(t=k+1\) and \(u=x-ky\); the equation becomes \((2^t-1)u=ty\). The fractional part of \(x/y\) is therefore \(t/(2^t-1)\), so its reduced denominator is

\[
Q(t)=\frac{2^t-1}{\gcd(2^t-1,t)}.
\]

For every \(t\ge2\), even when \(Q(t)\) is composite, two has order exactly \(t\) modulo \(Q(t)\). Indeed, write \(a=\lfloor t/2\rfloor\), \(b=\lceil t/2\rceil\). Since \(t\le 2^b\), we have \(t(2^a-1)\le 2^t-2^b<2^t-1\). It follows that \(Q(t)>2^a-1\). The order divides \(t\); a proper divisor would be at most \(a\), and the smaller positive number \(2^j-1\) could not be divisible by \(Q(t)\). In particular distinct indices have distinct denominators, though the denominators do not increase at every step: \(Q(5)=31\), \(Q(6)=21\).

The [order and lowest-terms proof](MersenneDenominator245212.lean) uses only Mathlib. The [application to the original equation](MersenneApplication245212.lean) imports the registered reduction. Both the recovery theorem and injectivity replay with only the standard Lean axioms.

In fact the [distinct primes alone determine the index](mersenne-prime-support-245212.md). If the surplus \(y=W(m)-m\tau(m)\) has at most one odd prime factor \(s\), this yields a sharper test: \(s=2^{k+1}-1\) must be a Mersenne prime, and \(k+1\) itself must be prime. If the reduced denominator has no prime factor above seven, the only possible ratios \(x/y\) are \(5/3,17/7,49/15,107/21\).

Here is why no reduced denominator can be a proper prime power. For composite \(t\), take its least prime factor \(p\) and put \(u=t/p\). The two factors \(A=2^u-1\) and \(B=1+2^u+\cdots+(2^u)^{p-1}\) are coprime: a common prime would divide \(p\), but the order of two modulo an odd \(p\) cannot divide both \(u\) and \(p-1\), which are coprime. For \(p=2\), \(A\) is odd. When \(u\ge5\), both factors exceed \(t\), since \(2^u-1>u^2\ge t\). So dividing their product by \(\gcd(2^t-1,t)\le t\) leaves two coprime nontrivial factors. The smaller cases have \(t\le16\) and check directly. For prime \(t\), \(Q(t)=2^t-1\). Such a number is three modulo four, so it is not an even power. An odd proper power \(r^e\) is impossible as well: \((r^e+1)/(r+1)\) would be an odd factor greater than one of \(2^t\).

Lean checks the [prime-power classification](MersennePrimePowers245212.lean) and its [consequence for the odd cofactor](MersenneCofactor245212.lean). The four ratios follow from the index formula: the index must divide \(\mathrm{lcm}(2,4,6)=12\); index 12 introduces the prime 13, leaving only 2, 3, 4 and 6.
