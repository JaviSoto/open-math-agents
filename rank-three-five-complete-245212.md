# No rank-three multiple of five satisfies A245212

If a positive integer has exactly three distinct odd prime divisors and is divisible by five, it does not satisfy the [OEIS A245212 divisor equality](https://oeis.org/A245212). There is no limit on the integer, the primes, their exponents, or the number of times two divides it. Combined with the earlier exclusion of multiples of three, any remaining three-prime exception is coprime to 15.

If three also divides the integer, the earlier three-divisibility result applies. Otherwise write the integer as \(2^k 5^a p^b q^c\), with \(5<p<q\) prime and \(a,b,c\ge1\). Previous odd and low-dyadic results rule out \(k=0,1,2,3\). For \(k\ge4\) the ratio \(W(h)/(h\tau(h))\) for the prefix \(h=2^k5^a\) must be strictly less than two; it is increasing in each exponent. This leaves exactly forty candidate pairs before considering \(p,q\):

| Power of two \(k\) | Exponent of five \(a\) |
|---|---|
| 4 | 1–31 |
| 5 | 1–4 |
| 6 | 1–2 |
| 7, 8, 9 | 1 |

For each prefix, bounds on the middle prime and the remaining divisor counts make the arithmetic checks finite. Modular obstructions discard classes of exponents. In the largest remaining prefix, \((k,a)=(4,31)\), the near-prime calculation is split into intervals through 65,536; a separate inequality and divisor-count proof covers **all** larger middle primes. A verified square-root trial-divisor test lets the Lean kernel check the prime intervals without repeating an expensive primality calculation. The cutoff only splits the proof; it is not a restriction on the theorem.

The [final Lean declaration](RankThreeFiveComplete245212.lean) is `OMA.RankThreeFiveComplete245212.original`. Its [complete source archive](rank-three-five-complete-245212.tar.gz) includes all 904 Lean modules, their hashes and a parallel replay script. Extract it and run `lake env python3 /path/to/lean_source_bundle_245212.py --workers 4` from the compiled Formal Conjectures checkout at `9097e2f90e66d2f6244209cb1c07f7120d17ec53`. No prebuilt research modules or numerical-search output are required.
