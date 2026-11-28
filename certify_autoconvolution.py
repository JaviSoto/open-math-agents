"""Certify an upper bound for Tao's C1a using only Python's standard library.

Input: a gzip-compressed text file with one nonnegative integer per equal bin.
Multiplying all heights by the same number leaves the bound unchanged.
"""
import argparse
import gzip
from decimal import Decimal, localcontext
from fractions import Fraction
from pathlib import Path


def exact_bound(heights):
    if not heights or min(heights) < 0 or not any(heights):
        raise ValueError("expected nonnegative heights with positive total")
    n, mass = len(heights), sum(heights)
    # Each digit of A(base)^2 equals one coefficient of A(x)^2: no carry.
    maximum_coefficient = n * max(heights)**2
    width = (maximum_coefficient.bit_length() + 7) // 8
    encoded = int.from_bytes(b"".join(h.to_bytes(width, "little") for h in heights), "little")
    raw = (encoded * encoded).to_bytes(width * (2*n - 1), "little")
    coeffs = [int.from_bytes(raw[i:i+width], "little") for i in range(0, len(raw), width)]
    assert sum(coeffs) == mass**2
    peak = max(coeffs)
    k = coeffs.index(peak)
    assert peak == sum(heights[i]*heights[k-i] for i in range(max(0, k-n+1), min(n-1, k)+1))
    score = Fraction(2*n*peak, mass**2)
    return score, k


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("witness", type=Path)
    args = parser.parse_args()
    with gzip.open(args.witness, "rt", encoding="ascii") as inp:
        heights = [int(line) for line in inp]
    bound, peak_index = exact_bound(heights)
    print(f"bins={len(heights)} peak_index={peak_index}\n{bound}")
    with localcontext() as ctx:
        ctx.prec = 48
        print(Decimal(bound.numerator)/Decimal(bound.denominator))
