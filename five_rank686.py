"""A finite 2-descent lower-rank certificate for the length-five quotient of Erdős 686."""

from itertools import product
from math import gcd, isqrt


def sextic(a: int, b: int) -> int:
    return 9*a**6 + 64*a**5*b - 200*a**3*b**3 + 64*a*b**5 + 144*b**6


COEFFS = (144, 64, 0, -200, 0, 64, 9)


def trim(f):
    while f and f[-1] == 0:
        f.pop()
    return f


def good_reduction(p: int) -> bool:
    f = [c % p for c in COEFFS]
    g = trim([i * f[i] % p for i in range(1, len(f))])
    while g:
        while len(f) >= len(g):
            shift = len(f) - len(g)
            scale = f[-1] * pow(g[-1], -1, p) % p
            for i, c in enumerate(g):
                f[i+shift] = (f[i+shift] - scale*c) % p
            trim(f)
        f, g = g, f
    return len(f) == 1


def character_pair(p: int, r: int, s: int, ab: tuple[int, int]) -> int | None:
    a, b = ab
    u = (a - b*r) * (a - b*s) % p
    if not u:
        return None
    return int(pow(u, (p-1)//2, p) != 1)


def rank(rows):
    basis = {}
    for row in rows:
        residual = row
        while residual and residual.bit_length() in basis:
            residual ^= basis[residual.bit_length()]
        if residual:
            basis[residual.bit_length()] = residual
    return len(basis)


def small_factor_degrees(p: int) -> list[int]:
    """Trial-divide the monic sextic over a small prime field; coefficients are ascending."""
    remaining = [c * pow(9, -1, p) % p for c in COEFFS]
    factors = []
    for degree in range(1, 4):
        if 2 * degree > len(remaining) - 1:
            break
        for lower in product(range(p), repeat=degree):
            divisor = [*lower, 1]
            while len(remaining) > degree:
                work = remaining.copy()
                quotient = [0] * (len(work) - degree)
                for k in range(len(quotient) - 1, -1, -1):
                    quotient[k] = work[k + degree]
                    for i, coeff in enumerate(divisor):
                        work[k+i] = (work[k+i] - coeff * quotient[k]) % p
                if any(work):
                    break
                factors.append(degree)
                remaining = quotient
    if len(remaining) > 1:
        factors.append(len(remaining) - 1)
    return factors


def main():
    for p in (7, 11, 37, 43, 101):
        assert all(p % k for k in range(2, isqrt(p) + 1))
        assert good_reduction(p)
    for p, expected in [(7,[6]), (11,[1,5]), (37,[1,1,1,1,2])]:
        degrees = small_factor_degrees(p)
        assert degrees == expected
        print("factor degrees modulo", p, ":", degrees)
    ratios = [(-20,1),(-2,1),(-1,1),(1,1)]
    base = (0,1)
    for a, b in [base, *ratios]:
        val = sextic(a,b)
        assert gcd(a,b) == 1 and isqrt(val)**2 == val
    rows = []
    for p,r,s in [(37,10,25), (37,10,33), (43,12,26), (101,33,71)]:
        assert r != s and sextic(r,1) % p == sextic(s,1) % p == 0
        bits = [character_pair(p,r,s,ab) for ab in [base,*ratios]]
        assert None not in bits
        bits = [x^bits[0] for x in bits[1:]]
        rows.append(sum(bit << i for i,bit in enumerate(bits)))
        print((p,r,s), bits)
    assert rank(rows) == 4
    print("Jacobian rank lower bound:", rank(rows))


if __name__ == "__main__":
    main()
