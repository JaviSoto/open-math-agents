"""List singular cube-indicator Hankel orders using polynomial half-GCD.

Run with uv run --with python-flint hankel_cubes_halfgcd.py 48000.
The half-GCD returns exactly the Euclidean quotient degrees up to the
midpoint. Their cumulative sums are the normal indices of the moments.
"""

import argparse
from flint import nmod_poly, fmpz


def matvec(m, a, b):
    x, y, z, w = m
    return x * a + y * b, z * a + w * b


def matmul(t, s):
    a, b, c, d = t
    e, f, g, h = s
    return a * e + b * g, a * f + b * h, c * e + d * g, c * f + d * h


def normal_orders(n, prime, exponent):
    if not fmpz(prime).is_prime():
        raise ValueError("the modulus must be a prime")
    x = nmod_poly([0, 1], prime)
    z = nmod_poly([], prime)
    u = nmod_poly([1], prime)
    identity = (u, z, z, u)
    degrees = []

    def half(a, b):
        m = (a.degree() + 1) // 2
        if b.degree() < m:
            return identity
        if m <= 40:
            v, w, y, z1 = identity
            while b.degree() >= m:
                q, r = divmod(a, b)
                degrees.append(q.degree())
                v, w, y, z1 = y, z1, v - q * y, w - q * z1
                a, b = b, r
            return v, w, y, z1
        first = half(a.right_shift(m), b.right_shift(m))
        c, d = matvec(first, a, b)
        if d.degree() < m:
            return first
        q, e = divmod(c, d)
        degrees.append(q.degree())
        v, w, y, z1 = first
        mid = (y, z1, v - q * y, w - q * z1)
        if e.degree() < m:
            return mid
        shift = 2 * m - d.degree()
        last = half(d.right_shift(shift), e.right_shift(shift))
        return matmul(last, mid)

    length = 2 * n
    coeff = [0] * length
    cube_root = 2
    while cube_root**exponent - 2 < length:
        coeff[length - 1 - (cube_root**exponent - 2)] = 1
        cube_root += 1
    half(x**length, nmod_poly(coeff, prime))
    normals = set()
    k = 0
    for q in degrees:
        k += q
        normals.add(k)
    return normals


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("order", type=int)
    parser.add_argument("--prime", type=int, default=1000000007)
    parser.add_argument("--power", type=int, choices=(2, 3), default=3)
    args = parser.parse_args()
    if args.order < 1:
        parser.error("the order must be positive")
    normal = normal_orders(args.order, args.prime, args.power)
    print(" ".join(str(i) for i in range(1, args.order + 1) if i not in normal))
