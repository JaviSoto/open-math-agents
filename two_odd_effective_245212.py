"""Two exact scalar exclusions for the last 253 dyadic indices after the
rank-two rounding estimates. No integer n or primes are enumerated here.
"""


def prime_floor(K, m):
    # Strict reciprocal bound p > k*(B-1)/B, applied with B >= m.
    return max(3, (K - 1) * (m - 1) // m + 1)


def exact_dyadic(K, m, lo, hi, Bmax, Cmax):
    """Certify that each of the three terms of G*T is strictly below 1/3."""
    z, R = 1 << K, lo ** (m - 1)
    G = z - 1
    weight = 3 * G * (K * Cmax + hi)
    # q^(C-2) <=3*z*K*B*P, so q²/P has exponent -(C-4)/(C-2)
    # in P. Using m rather than C only enlarges the upper bound.
    return (weight ** (m - 2) * (3 * z * K * Bmax) ** 2 < R ** (m - 4)
            and 3 * G * hi**2 * (K * Bmax + hi) < R
            and 3 * G * (K + hi**2) < R*R)


def integer_dyadic(K, m, lo, hi, Bmax, Cmax, product):
    """Use the q bound from the positive integer L_C(k), then E_k."""
    z, R = 1 << K, lo ** (m - 1)
    G = z - 1
    if 2 * (K * product * hi * R + G * Cmax * K) > G * R:
        return False
    qmax = 6 * product * K * hi**2
    first_two = qmax**2 * (K*Cmax + hi) + hi**2 * (K*Bmax + qmax)
    last = K + hi * qmax
    return (4*G*(first_two*R + last) + 9*K*hi**2*qmax**2*product*R**2
            < 4*G*R**2)


def main():
    # For every m>=119, the left/right ratio in this coarse estimate is
    # increasing: p>=3 and ((m+1)/m)^8 <=(120/119)^8<3.
    assert 120**8 < 3 * 119**8
    for K in range(3, 256):
        p = prime_floor(K, 119)
        if p**118 <= 2**(37 + 3*K) * K**10 * 119**8:
            raise ArithmeticError(f"coarse exponent cap failed at {K=}")
    counts = [0, 0]
    for K in range(3, 256):
        for m in range(33, 119):
            lo, hi = prime_floor(K, m), 5*K
            M = 64*m*m*K
            if exact_dyadic(K, m, lo, hi, M, M):
                counts[0] += 1
            elif integer_dyadic(K, m, lo, hi, M, M, m*M):
                counts[1] += 1
            else:
                raise ArithmeticError(f"unexcluded scalar region: {K=}, {m=}")
    print(f"253 unbounded-exponent caps; {counts[0]} exact-dyadic and "
          f"{counts[1]} integer-dyadic exclusions, "
          f"{sum(counts)} of {253*86} boxes")


if __name__ == "__main__":
    main()
