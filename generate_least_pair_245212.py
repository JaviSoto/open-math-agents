"""Generate a Lean certificate excluding a fixed least odd prime in A245212.

Example: python3 generate_least_pair_245212.py 7 Least7Pair245212.lean.
Python selects cutoffs; Lean proves every cutoff and checks every leaf.
"""
import argparse
from fractions import Fraction
from pathlib import Path

from fixed_dyadic_pairs_245212 import moments, prime


def weighted(p, e):
    w, _, t = moments(p, e)
    return Fraction(w, t)


def threshold(reaches):
    """Smallest positive exponent with weighted product at least two."""
    high = 1
    while not reaches(high):
        high *= 2
    low = high // 2 if high > 1 else 0
    while high - low > 1:
        middle = (low + high) // 2
        if reaches(middle):
            high = middle
        else:
            low = middle
    return high


def case(p, k):
    c = weighted(2, k)
    limit = c * Fraction(p, p - 1)
    header = [
        f"private theorem at_{k} {{q e f : ℕ}} (hq : q.Prime) (pq : {p}<q) (ep : 0<e) (fp : 0<f) :",
        f"    OeisA245212.a (2^{k}*{p}^e*q^f)≠(σ 1 (2^{k}*{p}^e*q^f):ℤ) := by",
    ]
    if limit > 2:
        bound = threshold(lambda e: c * weighted(p, e) >= 2) - 1
        return header + [f"  apply free_case (B:={bound}) (by decide) hq (by decide) pq ep fp <;> decide +kernel"]
    if limit == 2:
        raise ValueError("Unexpected Euler equality: dyadic numerator and p are odd")
    cutoff = max(p, int(2 / (2 - limit))) + 1
    lines = [f"  by_cases big : {cutoff}≤q",
             f"  · exact OMA.DyadicEuler245212.pair_small (by decide) hq (by decide) pq ep (u:={p}) (v:={cutoff})",
             "      (by decide) (by decide) le_rfl big (by decide +kernel)"]
    bases = [q for q in range(p + 1, cutoff) if prime(q)]
    if not bases:
        return header + lines + ["  interval_cases q <;> norm_num at *"]
    lines += ["  have cases : " + " ∨ ".join(f"q={q}" for q in bases) + " := by",
              "    interval_cases q <;> norm_num at *",
              "  rcases cases with " + "|".join(["rfl"] * len(bases))]
    for q in bases:
        bound = threshold(lambda e: c * weighted(p, e) * weighted(q, e) >= 2) - 1
        lines.append(f"  · apply known_case (B:={bound}) (by decide) hq (by decide) pq ep fp <;> decide +kernel")
    return header + lines


def render(p):
    name = f"OMA.Least{p}Pair245212"
    lines = ["import PairSweep245212", "",
             f"/-! No A245212 equality with least odd prime {p} and exactly two odd primes. -/",
             f"namespace {name}",
             "open Nat Finset ArithmeticFunction OMA.PairSweep245212",
             "open scoped ArithmeticFunction.sigma"]
    for k in range(2 * p):
        lines += ["", "set_option maxHeartbeats 50000000 in", *case(p, k)]
    lines += ["", f"theorem no_pair {{k q e f : ℕ}} (hq : q.Prime) (pq : {p}<q) (ep : 0<e) (fp : 0<f) :",
              f"    OeisA245212.a (2^k*{p}^e*q^f)≠(σ 1 (2^k*{p}^e*q^f):ℤ) := by",
              "  intro eq", "  have oq := hq.odd_of_ne_two (by omega)",
              f"  have odd : Odd ({p}^e*q^f) := ((by decide : Odd {p}).pow).mul oq.pow",
              f"  have mem : {p}∈({p}^e*q^f).primeFactors := Nat.mem_primeFactors.mpr",
              f"    ⟨by decide,dvd_mul_of_dvd_left (dvd_pow_self {p} ep.ne') _,by have := hq.pos; positivity⟩",
              f"  have hi : k<{2*p} := OMA.DyadicLeast245212.exponent_lt_twice_prime odd mem (by simpa [mul_assoc] using eq)",
              "  interval_cases k"]
    lines.extend(f"  · exact at_{k} hq pq ep fp eq" for k in range(2 * p))
    return "\n".join(lines + ["", "#print axioms no_pair", f"end {name}", ""])


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("prime", type=int)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    if args.prime < 3 or not prime(args.prime):
        parser.error("use an odd prime")
    args.output.write_text(render(args.prime))
