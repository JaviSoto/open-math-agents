"""Independent modular check for Meštrović's power-sum conjectures.

Run python3 mestrovic_power_witness.py 5309 106321, or specify --half
for exponent (n-1)/2. With --test, compare against the defining sum.
No Bernoulli data, symbolic algebra, or third-party packages are needed.
"""
from argparse import ArgumentParser
from math import comb, gcd


def block_residue(p, blocks, exponent):
    """Sum x^exponent over 0 <= x < p*blocks, modulo p^4."""
    modulus = p**4
    # x = residue + p*j. Terms of degree >= 4 in j vanish modulo p^4.
    triangle = blocks * (blocks - 1) // 2
    moments = (blocks, triangle, triangle * (2 * blocks - 1) // 3, triangle**2)
    answer = 0
    for k in range(min(exponent, 3) + 1):
        coefficient = comb(exponent, k) * p**k * moments[k]
        reduced_modulus = modulus // gcd(coefficient, modulus)
        row = sum(pow(x, exponent - k, reduced_modulus) for x in range(p))
        answer += coefficient * row
    return answer % modulus


def check_pair(p, q, half=False):
    if not 1 < p < q or gcd(p, q) != 1:
        raise ValueError("Give two coprime factors in increasing order")
    n = p * q
    if half and not n % 2:
        raise ValueError("The half-exponent question assumes odd n")
    exponent = (n - 1) // 2 if half else n - 2
    a, b = block_residue(p, q, exponent), block_residue(q, p, exponent)
    m, k = p**4, q**4
    residue = a + m * ((b - a) * pow(m, -1, k) % k)
    return n, exponent, a, b, residue


def test():
    for p, q in [(2, 3), (3, 5), (3, 7), (5, 9), (5, 11), (7, 19), (11, 13), (37, 101)]:
        for half in ([False, True] if p % 2 else [False]):
            n, exponent, a, b, residue = check_pair(p, q, half)
            direct = sum(pow(x, exponent, n**4) for x in range(1, n)) % n**4
            assert (direct, direct % p**4, direct % q**4) == (residue, a, b)
    for exponent in range(1, 7):
        assert block_residue(5, 7, exponent) == sum(x**exponent for x in range(35)) % 5**4


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("factors", type=int, nargs="*")
    parser.add_argument("--half", action="store_true")
    parser.add_argument("--test", action="store_true")
    args = parser.parse_args()
    if args.test:
        test()
        print("Passed direct-sum controls")
    if args.factors:
        if len(args.factors) != 2:
            parser.error("expected two factors")
        p, q = args.factors
        n, exponent, a, b, residue = check_pair(p, q, args.half)
        print(f"n={n}, exponent={exponent}, S mod {p}^4={a}, S mod {q}^4={b}")
        print(f"S mod n^3 = {residue % n**3}; S mod n^4 = {residue}")
        if residue % n**3 == 0:
            print(f"(S / n^3) mod n = {residue // n**3}")
