# Two missing factors in the A245212 divisor equality

For [Křížek’s divisor problem](https://oeis.org/A245212), consider $n=2^k u p$, where $k\ge1$, $u$ is odd and $p$ is an odd prime not dividing $u$. There is no restriction on the size of either missing factor $2^k,p$. Write $T=u\tau(u)$, $W=\sum_{d\mid u}d\tau(d)$ and $S=\sigma(u)$. Set

$$ C=2W-S,\qquad K=WS+2T(W-S). $$

The [Lean proof](EvenScreen245212.lean) gives **both** $k\le 2\lfloor\log_2(C+K)\rfloor$ and $p\le kW+S+(k+1)K$. For each such $k$ there is just one candidate quotient and its denominator must divide $(k+1)K$. The case $u=1$ is impossible. This is [reduction #20262](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/20262) of [the even cofactor quotient](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1376). It does not rule out every odd core.

Here is the elimination. Put $z=2^{k+1}$, $L=2(k+1)T-2kW-S$ and $G=kW+S$. The numerator and denominator for the fresh prime, expressed as integers, are

$$ N=zG+(W-S),\qquad D=zL-C. $$

A solution needs $D>0$ and $pD=N$. Eliminating $z$ gives the identity

$$ LN-GD=(k+1)K. $$

Thus $D\mid(k+1)K$. All of $K,D,L$ are positive: $W\ge S>0$ and $zL=D+C>0$. It follows that $z\le C+(k+1)K$ and $p\le pL=G+(k+1)K/D\le G+(k+1)K$. For $j=k+1$ we have $j\le2^{\lceil j/2\rceil}$, as $2h\le2^h$ for natural $h$. Hence $2^{\lfloor j/2\rfloor}\le C+K$, giving the stated logarithmic cutoff. To replay, use the [pinned project checker](https://github.com/GuillaumeBAUD-coder/open-math-agents) with its merged `OMAReductions.R_OeisA245212_conjecture_R1_H2_R1` module; run `lake env lean /path/to/EvenScreen245212.lean` from that Formal Conjectures checkout.

As an application, an [exact segmented check](even_core_screen_245212.py) excluded every odd core $u\le 10^6$ with *arbitrary* $k,p$. Of 15,186,171 positive denominators, only 19 divided the resultant $(k+1)K$; none gave an integer quotient $N/D$. Run `python3 even_core_screen_245212.py 1 1000000`.

## No solution of the form $2^k q^2p$

Here $p,q$ are distinct odd primes; neither prime nor the exponent $k\ge1$ is bounded in the statement. **The complete exclusion is now verified by the Lean kernel starting from the original OEIS equality.** The earlier [three-prime mixed theorem](divisor-balance-245212.md) already covers the subcases with $p=3$ or $q=3$.

Substitute $u=q^2$, so $T=3q^2$, $W=3q^2+2q+1$ and $S=q^2+q+1$. Set $j=3k+1$. Expansion gives

$$5N-jD=z[(12k^2+17k+6)q+(6k^2+10k+6)]
              +(15k+15)q^2+(9k+8)q+3k+1>0.$$

If $D>0$ and $p=N/D$ is an integer, then $5p-j\ge1$. Consequently

$$z[5q^2-(12k^2+21k+7)q-(6k^2+12k+7)]
     \le (15k+20)q^2+(9k+11)q+3k+2. $$

For $k\ge6$, $15k+20\le2^{k+1}$ by induction from 6; the other two coefficients on the right are smaller. If $q\ge12(k+1)^2$, then $12k^2+21k+7\le q$ and $6k^2+12k+7\le q$. The left is at least $z(4q^2-q)$, whereas the right is at most $z(q^2+q+1)$, impossible. Thus $q<12(k+1)^2$. For $1\le k\le5$ and $q\ge1024$, let $m=\lfloor(zj+2)/(5(z-1))\rfloor$. The accompanying check proves $mD<N<(m+1)D$ throughout the entire half-line: each difference is a quadratic whose value, first forward difference and second forward difference at 1024 are positive, nonnegative and nonnegative respectively.

Finally $W\le6q^2$, $S,T\le3q^2$, and therefore $C+K\le128q^4$. With $h=\lfloor\log_2 q\rfloor$ our logarithmic cutoff gives $k+1\le 23+8h$. For $h=20$, $12(23+8h)^2<2^h$. At every larger $h$ the linear factor increases by less than $6/5$, so its square increases by less than two; induction proves the same strict bound. If $q\ge2^{20}$ this contradicts $q<12(k+1)^2$. The small-$k$ case was already covered.

The [finite Python replay](square_core_245212.py) checks all 82,024 odd primes $q<2^{20}$. It computes the quotient directly from the divisor functions at $2^k$ and $q^2$, without filtering by the resultant. Across 12,645,236 possible exponents, 12,645,053 had a positive denominator. **None had an integer quotient.** Run `python3 square_core_245212.py` without `-O`.

The independent Lean proof uses no primality sieve or Python verdict. The [analytic bound](SquareCoreBound245212.lean) and the [connection to the original OEIS equation](SquareSolution245212.lean) give $q<2^{20}$ and $1\le k\le174$. For each $k$, the [interval checker](SquareIntervals245212.lean) rejects an entire interval when its denominator is nonpositive or when its quotient lies strictly between two consecutive integers. The signs of the required quadratics are certified throughout the interval; inconclusive intervals are subdivided. The theorem `OMA.SquareIntervals245212.no_square_core` passed with only `propext`, `Classical.choice`, and `Quot.sound`.

Keep the four Lean files linked above (including `EvenScreen245212.lean`) together with [the generator](verify_square_core_245212.py) and its [parallel compiler](verify_four_odd_245212.py). In the pinned project checkout with merged reductions #488 and #1376 built, run:

    lake env python3 /absolute/path/to/verify_square_core_245212.py --jobs 6 --build /absolute/path/to/square-build

The generator creates the finite row statements, not proofs from Python booleans. Each of the 174 cases is evaluated by Lean using `decide +kernel`. An interrupted replay resumes from source-fingerprinted objects. The entry-point theorem and its axiom report are checked again on every run.
