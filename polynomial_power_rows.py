"""Generate small-index exact power-sum certificates for the least witness.

Run in the proof workspace: python3 polynomial_power_rows.py. The emitted
Lean checks every coefficient and both endpoints, independent of Python.
"""
from fractions import Fraction
from math import comb, gcd, lcm
from pathlib import Path


def antiderivative(e):
    coefficients = [Fraction(0)] * (e+2)
    for j in reversed(range(e+1)):
        known = sum(coefficients[i] * comb(i, j) for i in range(j+2, e+2))
        coefficients[j+1] = (int(j == e)-known) / Fraction(j+1)
    denominator = lcm(*(c.denominator for c in coefficients))
    return denominator, [int(c*denominator) for c in coefficients]


def declaration(p, e):
    d, coeff = antiderivative(e)
    assert gcd(d, p) == 1
    assert sum(c*pow(p, j, p*p) for j,c in enumerate(coeff)) % (p*p) == 0
    values = ",\n  ".join(map(str, coeff))
    return f"""private def coeff{p} : List ℤ := [
  {values}]

theorem low{p} : (∑i∈range {p}, (i:ZMod ({p}^2))^{e})=0 :=
  OMA.PolynomialPowerRow284759.row (d:={d}) coeff{p}
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
"""


if __name__ == "__main__":
    output = Path(__file__).resolve().with_name("LeastWitnessRows284759.lean")
    text = """import PolynomialPowerRow284759

/-! Kernel-checked antiderivatives for the two reduced-index power sums. -/
namespace OMA.LeastWitnessRows284759
open Finset
set_option maxRecDepth 32768
set_option maxHeartbeats 0
set_option exponentiation.threshold 65536
"""
    output.write_text(text + declaration(157, 110) + declaration(1569473, 154)
                      + "\nend OMA.LeastWitnessRows284759\n")
