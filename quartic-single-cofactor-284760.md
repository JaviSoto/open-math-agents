# No composite quartic power-sum counterexample below 4,085,441,820,686,521

Suppose $n$ is composite and $n^4\mid S_{n-2}(n)$, with $S_e(n)=\sum_{a=1}^{n-1}a^e$. The [quartic Bernoulli criterion and local prime-factor calculation](https://github.com/JaviSoto/open-math-agents/blob/b90d02b716198c7703a21a6e539e5bc3f4f931d8/quartic-bernoulli-284760.md) give three facts: $n$ is odd; $n^2\mid\operatorname{num}B_{n-3}$; and every prime factor of $n$ below $M=63,917,461$ must be $6263$ and can occur only once.

If $n<M^2$, two factors $\ge M$, including a repeated factor, are impossible. The factor $6263$ cannot account for a composite by itself. Therefore $n=6263q$ for a prime $M\le q\le652,313,878,442$. The sole surviving small-prime index is $3286$ modulo $6262$, so $q\equiv3289\pmod{6262}$. At $q$ the index has a particularly simple form:

$$n-3=6263q-3\equiv6260\pmod{q-1}.$$

Since $q\nmid n-3$ and $0<6260<q-1$, the [first Kummer congruence](https://arxiv.org/abs/math/0409223) gives $q\mid\operatorname{num}B_{6260}$. This is a single fixed integer, independent of $q$. No evaluation at the enormous index $n-3$ is necessary.

[The exact computation](quartic_single_cofactor.py) uses [Brent and Harvey's tangent-number triangle](https://arxiv.org/abs/1108.0286) to compute $|\operatorname{num}B_{6260}|$ and checks the defining Bernoulli recurrence at the target and two shorter indices. The numerator has 53,339 bits. Its SHA-256, encoding the unsigned integer most-significant byte first, is `1ccd42894dd638f18f56f083afeb0984886b2d1b279c9d483f09835920336c40`.

There are 104,160,007 integers in the required interval and residue class. Removing multiples of primes $\le32768$ leaves 11,745,710. These removals cannot discard a prime in the interval. For each block of 128 remaining integers, take the gcd of their product with the numerator; if it exceeds one, test each integer by direct division. **None divides the numerator.** Consequently $n\ge M^2=4,085,441,820,686,521$.

Run `python3 quartic_single_cofactor.py` to repeat the entire fixed-cofactor computation with standard-library integer arithmetic. The result also agrees through $q<2^{31}$ with [the independent Hart–Harvey–Ong table scan](cofactor_indices_mestrovic.py). The bound concerns composite inputs. The [separate prime-input result](https://github.com/JaviSoto/open-math-agents/blob/b90d02b716198c7703a21a6e539e5bc3f4f931d8/quartic-bernoulli-284760.md) excludes all primes up to $10^{11}$; the full conjecture is still open.
