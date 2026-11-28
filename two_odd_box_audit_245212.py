"""Independent exterior certificate for the two-odd-prime A245212 search.

Usage: python3 two_odd_box_audit_245212.py. Tests the two disjoint
regions outside 6<=K<=1250 and max(B,C)<=225, for 6<=min(B,C)<=32.
Only integers are used: log2 of a positive integer is enclosed using
bit_length of its exact sixteenth power. Does not import the primary
box solver or depend on its subdivisions or surviving list.
"""
from collections import Counter
from functools import lru_cache
from math import isqrt


SCALE = 16


@lru_cache(maxsize=32_768)
def down(value: int) -> int:
    return (value**SCALE).bit_length() - 1


@lru_cache(maxsize=32_768)
def up(value: int) -> int:
    return (value**SCALE - 1).bit_length()


def over(n: int, d: int) -> int:
    return -((-n) // d)


def veto(kl: int, kh: int, bl: int, bh: int, cl: int, ch: int) -> str:
    # 1 - (13/12)^2/16 <= gamma*(w_p*w_q/(BC)-1) <=
    # K*(2/u + 1/u^2) <= K*(25/12)/u. Therefore u < 9K/4.
    # Strict lower reciprocal bound k(B-1) < Bp.
    p = max(13, 1 + ((kl - 1) * (bl - 1)) // bl)
    p |= 1
    top = 1 + (9 * kh) // 4
    if top < p:
        return "least prime"
    q = p + 2
    lp, hp = down(p), up(top)
    lq = down(q)
    P, Q = (bl - 1) * lp, (cl - 1) * lq
    dz = SCALE * kh
    dg = SCALE * (kl - 1)
    cap = dz + up(3 * kh * bh)
    if (cl - 2) * lq > cap + (bh - 1) * hp:
        return "q cofactor"
    if (cl - bh - 1) * lq > cap:
        return "ordered powers"
    y = over(cap + (bh - 1) * hp, cl - 2)
    ynorm = over(2 * cap - (cl - 4) * P, cl - 2)
    if P >= dz + up(2 * ch * kh):
        y = min(y, dz + up(6 * ch * bh * kh * top**2))
    pole_drift = up(ch * kh * bh * top) - dg
    pole_tail = up(ch * kh) - P
    if max(pole_drift, pole_tail) <= -2 * SCALE:
        y = min(y, up(6 * ch * bh * kh * top**2))
    ynorm = min(ynorm, 2 * y - P)
    if lq > y or (bl - 2) * lp > dz + up(3 * kh * ch) + (ch - 1) * y:
        return "reverse cofactor"
    if SCALE * kl > up(2 * bh * ch) + (bh - 1) * hp + (ch - 1) * y:
        return "dyadic divisor"
    # Each error summand decreases in q after division by Q, except
    # the first, for which ynorm is a direct upper bound on q^2/P.
    e1 = up(kh * ch + top) + ynorm
    e2 = 2 * hp + up(kh * bh + q) - Q
    e3 = up(kh + top * q) - P - Q
    largest = max(e1, e2, e3)
    if largest + up(3) + dz < 0:
        return "exact integer defect"
    # Here 4/3 is an upper bound for (13/12)^2. Retaining 2 avoids
    # rounding a rational factor in a direction-dependent expression.
    left_shift = up(2 * kh * bh * ch) + 2 * hp + 2 * y - dg
    if max(largest, left_shift) + 2 * SCALE < 0:
        return "limiting integer defect"
    # A-kH cannot be zero when a>=2d+4. In x,y orientation use
    # z <= 1 + 2*inner*outer*K*x^2*y^d
    #        + 6*inner^2*outer*(K+x)*y^(2d).
    for bx, ux, cy, xlog, ylog in (
        (bl, bh, ch, hp, y), (cl, ch, bh, y, hp)
    ):
        if bx < 2 * cy + 3:
            continue
        d = cy - 1
        log_first = up(2 * cy * ux * kh) + 2 * xlog + d * ylog
        log_second = (up(6 * cy * cy * ux) + SCALE
                      + max(up(kh), xlog) + 2 * d * ylog)
        if max(0, log_first, log_second) + up(3) < SCALE * kl:
            return "complementary integer"
    return ""


def rectangle(m: int, kl: int, kh: int, ml: int, mh: int, reverse: bool,
              counts: Counter, survivors: list) -> None:
    # At each recursive entry this only discards M forbidden by the
    # independent original-equation exponent bound. All cuts are closed.
    mh = min(mh, 64 * m**2 * kh, 32768 * m**6)
    if kl > kh or ml > mh:
        return
    b0, b1, c0, c1 = (m, m, ml, mh) if reverse else (ml, mh, m, m)
    reason = veto(kl, kh, b0, b1, c0, c1)
    if reason:
        counts[reason] += 1
        return
    if kl == kh and ml == mh:
        survivors.append((kl, b0, c0))
        return
    # Split the coordinate with the larger ratio of endpoints.
    # A geometric midpoint is a different tree from the primary solver.
    if kh * ml >= mh * kl and kl < kh:
        mid = isqrt(kl * kh)
        rectangle(m, kl, mid, ml, mh, reverse, counts, survivors)
        rectangle(m, mid + 1, kh, ml, mh, reverse, counts, survivors)
    else:
        mid = isqrt(ml * mh)
        rectangle(m, kl, kh, ml, mid, reverse, counts, survivors)
        rectangle(m, kl, kh, mid + 1, mh, reverse, counts, survivors)


def run() -> None:
    counts = Counter()
    for m in range(6, 33):
        gap = []
        for reverse in (False, True):
            # Equal exponents are included only in the first orientation.
            first = m + int(reverse)
            rectangle(m, 1251, 512 * m**4, first, 32768 * m**6, reverse, counts, gap)
            rectangle(m, 6, 1250, max(226, first), 32768 * m**6, reverse, counts, gap)
        if gap:
            raise RuntimeError(f"m={m}: {len(gap)} exterior cells survived; first={gap[:10]}")
    print(f"Verified both exterior regions for m=6..32: {sum(counts.values()):,} excluded boxes.")
    print(dict(sorted(counts.items())))


if __name__ == "__main__":
    run()
