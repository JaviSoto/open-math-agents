"""Check the finite base for the rational-weight cube-Hankel theorem.

The elimination operates modulo a prime. All row swaps are confined to
the first 177 rows; the later leading determinants share the same signed
product of pivots. Plain Python 3; no dependencies.
"""

from math import isqrt


def leading_determinants(first=177, last=364, prime=1_000_000_007):
    assert 1 <= first <= last
    assert all(prime % t for t in range(2, isqrt(prime) + 1))
    cubes = {k**3 for k in range(1, 2 * last + 1) if k**3 <= 2 * last}
    mat = [[int(i + j + 2 in cubes) for j in range(last)] for i in range(last)]
    det = 1
    for j in range(last):
        if j < first:
            pivot = next(i for i in range(j, first) if mat[i][j])
            if pivot != j:
                mat[j], mat[pivot] = mat[pivot], mat[j]
                det = -det
        if mat[j][j] == 0:
            raise ArithmeticError(f"zero pivot at order {j + 1}")
        det = det * mat[j][j] % prime
        if j + 1 >= first:
            yield j + 1, det
        inv = pow(mat[j][j], -1, prime)
        for i in range(j + 1, last):
            if mat[i][j]:
                factor = mat[i][j] * inv % prime
                mat[i][j + 1:] = [
                    (b - factor * a) % prime
                    for a, b in zip(mat[j][j + 1:], mat[i][j + 1:])
                ]


if __name__ == "__main__":
    values = list(leading_determinants())
    assert len(values) == 364 - 177 + 1 and all(v for _, v in values)
    print(f"nonzero: {values[0][0]} through {values[-1][0]}")
    print(f"endpoint residues: {values[0][1]}, {values[-1][1]}")
