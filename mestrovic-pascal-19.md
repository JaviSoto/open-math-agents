# The even-modulus binomial power-sum conjecture

[Meštrović, Conjecture 19 (2014), p. 10](https://cs.uwaterloo.ca/journals/JIS/VOL17/Mestrovic/mes4.pdf#page=10), asks whether the following integer is congruent to $-1$ modulo $n^3$ for every positive even $n$ and every $k\ge1$:

$$T=\sum_{i=0}^{k}(1+n(k+1-i)){2k+2\choose 2i}\sum_{a=1}^{n-1}a^{2i}.$$

**It is.** The argument also gives the already-known odd case, so the resulting theorem holds for all positive $n$. No search, Bernoulli tables or primality hypotheses are needed.

### Why the inner powers disappear

Set $d=k+1$ and $N=2d$. Double the sum to select the even powers in the binomial theorem. At each base $a$, the part without the factor $n$ becomes

$$ (a+1)^N-2a^N+(a-1)^N. $$

For the weighted part, $(N-2i){N\choose 2i}=N{N-1\choose 2i}$. The doubled weighted part is therefore

$$nd\big((a+1)^{N-1}-(a-1)^{N-1}\big).$$

Both expressions telescope. Summing over $1\le a<n$ gives the exact endpoint identity

$$2(T+1)=(d+1)n^N+1-dn-[1+(d-1)n](1-n)^{2d-1}.$$

For even $n$, work modulo **$2n^3$** so dividing the final integer congruence by two preserves the full requested modulus. All terms involving $n^4$ vanish. In the remaining product the constant and linear terms cancel and the quadratic coefficient is zero. The cubic coefficient of the right side is

$$ {2d-1\choose 3}-(d-1){2d-1\choose 2}
=-\frac{d(d-1)(2d-1)}{3}
=-2\sum_{j=1}^{d-1}j^2,$$

which is even. Thus $2n^3\mid 2(T+1)$, as desired. For odd $n$, use the same identity modulo $n^3$ and cancel two because it is invertible. The Lean proof obtains the truncated binomial expansion by induction in the residue ring, without divisions in that ring.

**Verification.** [Exact finite-difference identity](PascalPowerSum19.lean), [original double-sum theorem](PascalMod19.lean), [self-contained Lean source archive](mestrovic-pascal-19.tar.gz). In the Formal Conjectures checkout at `9097e2f90e66d2f6244209cb1c07f7120d17ec53`, run `lake env python3 /path/to/lean_source_bundle_245212.py --archive /path/to/mestrovic-pascal-19.tar.gz`. The original even case is `OMA.PascalMod19.conjecture`; the all-positive version is `OMA.PascalMod19.all_positive`.
