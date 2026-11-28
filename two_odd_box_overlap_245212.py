"""Check that the independent survivors all enter the actual final-prime replay.

Run python3 two_odd_box_overlap_245212.py beside the two bounds programs.
The independent exterior certificate must also be run. No primality or
divisor-moment computation is shared between this check and the final sweep.
"""
from collections import Counter

from two_odd_box_audit_245212 import rectangle, run
from two_odd_boxes_245212 import reduce


def main() -> None:
    run()
    independent = set()
    scanned = set()
    for m in range(6, 33):
        possible = []
        for reverse in (False, True):
            rectangle(m, 6, 1250, m + int(reverse), 225, reverse, Counter(), possible)
        independent.update(possible)
        for kl, kh, ml, mh, reverse in reduce(m, 512 * m**4, precision=12)[1]:
            for k in range(kl, kh + 1):
                for maximum in range(ml, mh + 1):
                    b, c = (m, maximum) if reverse else (maximum, m)
                    scanned.add((k, b, c))
    missing = independent.difference(scanned)
    if missing:
        raise RuntimeError(f"{len(missing)} uncovered independent survivors; first={min(missing)}")
    print(f"All {len(independent):,} independent survivors occur in {len(scanned):,} replay cells.")
    print(f"Largest independent K={max(k for k, _, _ in independent)}, "
          f"max(B,C)={max(max(b, c) for _, b, c in independent)}.")


if __name__ == "__main__":
    main()
