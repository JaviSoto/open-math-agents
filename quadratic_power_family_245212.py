"""Exact final digit for A245212 at 2^k p^a q², without a bound on q.

The proof in quadratic-power-family-245212.md gives K=k+1 <224, a<500,
p<4096. The published odd-divisor-count theorem covers a<=22.
"""
from math import isqrt
from time import monotonic


def check():
    started = monotonic()
    primes = [
        p for p in range(3, 4096, 2)
        if all(p % d for d in range(3, isqrt(p) + 1, 2))
    ]
    # Save K-only factors once. Each of the 223 values is still tested.
    rows = []
    for K in range(1, 224):
        z = 1 << K
        rows.append((K, z - 1, 1 + (K - 1) * z, z * K,
                     200 * z * K**3, (1 << 20) * z**3 * K**7))
    total = tested = positive = hits = 0
    for p in primes:
        power = S = W = 1
        for a in range(1, 500):
            previous = power
            power *= p
            b = a + 1
            S += power
            W += b * power
            if a < 23:
                continue
            for K, G, F, zK, small_q_cap, small_p_cap in rows:
                total += 1
                if p > 5 * K:
                    if previous > small_q_cap:
                        continue
                elif power > b * b * small_p_cap:
                    continue
                tested += 1
                A = F * W
                U = G * S
                D = 3 * zK * b * power - 3 * A - U
                if D <= 0:
                    continue
                positive += 1
                N, M = 2 * A + U, A + U
                q = N // D + 1
                if q * (D * q - N) != M:
                    continue
                hits += 1
                if q > 2 and q % 2 and q != p:
                    if A * (3*q*q + 2*q + 1) + U * (q*q + q + 1) != 3*zK*b*power*q*q:
                        raise AssertionError("the integral digit failed original balance")
                    raise ArithmeticError(f"integer candidate: 2^{K-1} * {p}^{a} * {q}^2")
    if total != len(primes) * 477 * 223:
        raise AssertionError("coverage")
    print(f"{len(primes)} primes, {total} triples, {tested} within cofactor bounds, "
          f"{positive} positive denominators, {hits} integral digits, "
          f"no candidate; {monotonic()-started:.3f}s")


if __name__ == "__main__":
    check()
