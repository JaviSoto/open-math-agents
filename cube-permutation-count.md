# Cube-sum permutations: the exact threshold and their number

Let \(P_n\) be the number of permutations of \(\{1,\ldots,n\}\) for which \(i+\pi(i)\) is a perfect cube for every \(i\). This is [OEIS A096904](https://oeis.org/A096904). In 2018 Robert Israel [conjectured](https://oeis.org/A006063/internal) that \(P_n>0\) for every \(n\ge173\), and reported checking the statement through 1000. The threshold is exact. Moreover,
\[
                    \log P_n=\tfrac13 n\log n+O(n).
\]

## The sharp threshold

Suppose a cube \(k^3\) belongs to \([n+174,2n]\), and put \(m=k^3-n-1\). Then \(173\le m<n\). Given an admissible permutation on \([1,m]\), extend it by \(\pi(i)=k^3-i\) on \([m+1,n]\). This reverses the new interval and makes every new sum equal to \(k^3\). James Tanton gives the corresponding construction for squares and asks about cubes in his [2016 essay on square permutations](https://www.gathering4gardner.org/wp-content/uploads/2021/03/Cool-Math-Essay_September-2016_Square-Permutations1.pdf).

Such a cube exists if \(n\ge365\). Let \(k\) be the first integer with \(k^3\ge n+174\). If \(k\le9\), then \(k^3\le729\le2n\). Otherwise \(s=k-1\ge9\), \(s^3\le n+173\), and \((s+1)^3+346\le2s^3\). The last inequality follows by expanding at \(s=9+t,\ t\ge0\): the difference between the right and left sides is \(t^3+24t^2+186t+112\). Thus \(k^3\le2n\). Strong induction reduces the problem to orders \(173,\ldots,364\).

The [standalone Lean proof](CubePermutation006063.lean) verifies positive witnesses by recording a cube root for each row and each column. For row \(i\) with root \(k\), the selected column is \(j=k^3-i\); the checker verifies \(1\le j\le n\) and that the root recorded at \(j\) is also \(k\). Two rows selecting the same column must then have the same root and hence be equal. This proves the selected map is a permutation. The finite classification also verifies, for each rejected positive order below 173, a set of rows whose possible columns are contained in a strictly smaller set. The [certificate generator](make_cube_permutation_cert.py) uses augmenting paths; the Lean proof does not assume its correctness.

Exactly 48 positive orders below 173 admit a permutation and 172 does not. Thus the increasing sequence of admitted positive orders satisfies \(a(k)=k+124\) already for \(k\ge49\). The theorem applies to the permanent, not to the signed determinant in Sun’s related [A228624 conjecture](https://oeis.org/A228624).

## How many permutations?

Let \(H_{ij}=1\) if \(i+j\) is a cube, and \(0\) otherwise, so \(P_n=\operatorname{per}H\). Every row has at most \((2n)^{1/3}\) choices, whence \(P_n\le(2n)^{n/3}\).

For the lower bound, construct a random admissible permutation. Choose a fixed \(N_0\ge4\cdot173\) large enough that for every \(N\ge N_0\) there are at least \(cN^{1/3}\) cubes \(k^3\) with
\[
                N/4\le k^3-N-1\le N/2.
\]
This follows by subtracting the cube roots of the endpoints \(5N/4+1\) and \(3N/2+1\) and allowing for rounding. At size \(N\), choose such a cube uniformly, reflect the terminal interval, and recurse on the resulting size \(m\). For \(173\le N<N_0\) use one fixed admissible permutation, supplied by the theorem above.

Let \(D_{ij}=\Pr[\pi(i)=j]\). This matrix is doubly stochastic and supported on \(H\). For \(i\ge N_0\), given the entire past and current size \(N\ge i\), the probability of assigning \(i\) to \(j\) at this step is at most \(1/(cN^{1/3})\): at most one cube equals \(i+j\). Along each possible history the sizes halve or better, so summing backwards from the final size still containing \(i\) gives
\[
       \sum_{t:\,N_t\ge i}N_t^{-1/3}
       \le i^{-1/3}\sum_{\ell\ge0}2^{-\ell/3}.
\]
Sum conditional probabilities and take expectations. Enlarging the constant to include the bounded rows \(i<N_0\), we obtain \(D_{ij}\le C i^{-1/3}H_{ij}\) for all \(i,j\).

The permanent is monotone on nonnegative matrices and multilinear in rows. The doubly stochastic permanent theorem of [Egorychev](https://www.mathnet.ru/eng/smj6520) and [Falikman](https://www.mathnet.ru/eng/mzm6253) thus gives
\[
  P_n\ge C^{-n}(n!)^{1/3}\operatorname{per}D
       \ge C^{-n}(n!)^{1/3}\,\frac{n!}{n^n}.
\]
Taking logarithms and using Stirling's formula proves the count.

The positive and negative terms in the determinant are also asymptotically equal in number. Indeed, Hadamard's determinant bound gives \(|\det H|\le(2n)^{n/6}\) from the same row-degree estimate. Consequently, writing \(E_n,O_n\) for the numbers of even and odd admissible permutations,
\[
  \frac{|E_n-O_n|}{P_n} \le \exp\bigl(-\tfrac16 n\log n+O(n)\bigr).
\]
This does not decide whether the difference can be exactly zero. The threshold and finite classification are Lean-certified; the counting and sign estimates here are ordinary mathematical proofs.
