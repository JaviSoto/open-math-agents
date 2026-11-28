"""Produce a standalone certificate for the simultaneous cube-weight theorem.

Usage: python3 make_cube_weight_cert.py CubeHankelWeightComplete228624.lean
The generator computes discrepancy witnesses over F_53. The Lean kernel
checks each coefficient against the original cube sequence prior to use.
"""

import argparse
from pathlib import Path


def witnesses(maximum=364, prime=53):
    moments = [int(any(r**3 == j + 2 for r in range(2, 10)))
               for j in range(2 * maximum)]
    support = [i for i, value in enumerate(moments) if value]
    connection, previous = [1], [1]
    q, delay, inverse = 0, 1, 1
    for t in range(2 * maximum - 1):
        d = sum(connection[t - s] for s in support if 0 <= t - s < len(connection)) % prime
        if d:
            before = connection[:]
            if len(connection) < delay + len(previous):
                connection.extend([0] * (delay + len(previous) - len(connection)))
            for i, coefficient in enumerate(previous):
                connection[delay + i] = (connection[delay + i] - d * inverse * coefficient) % prime
            if 2 * q <= t:
                order = t + 1 - q
                before += [0] * (q + 1 - len(before))
                a = [before[q - i] for i in range(q)]
                for j in range(order):
                    disc = (moments[j + q] + sum(a[s - j] for s in support if j <= s < j + q)) % prime
                    assert (disc != 0) == (j + 1 == order)
                yield q, order, sum(v << (6 * i) for i, v in enumerate(a))
                q, previous, inverse, delay = order, before, pow(d, -1, prime), 0
        delay += 1


def cases(low, high, indent='  '):
    if high == low + 1:
        return f'{indent}obtain rfl : n = {low} := by omega\n{indent}exact normal{low}\n'
    mid = (low + high) // 2
    return (f'{indent}by_cases h{mid} : n < {mid}\n' +
            f'{indent}·\n' + cases(low, mid, indent + '  ') +
            f'{indent}·\n' + cases(mid, high, indent + '  '))


def generate():
    root = Path(__file__).resolve().parent
    files = ['CubeHankel228624.lean', 'CubeHankelWeight228624.lean', 'CubeHankelCertificates228624.lean']
    chunks = ['import FormalConjectures.OEIS.«228624»\nimport Mathlib.LinearAlgebra.Matrix.SchurComplement\n']
    for name in files:
        body = (root / name).read_text().splitlines()
        module = '\n'.join(line for line in body if not line.startswith('import '))
        chunks.append((module if name == files[0] else module.replace('/-!', '/-')) + '\n')
    chunks += ['\nnamespace OMA.CubeHankel\n',
               'private theorem normal0 : (hankel (cubeSeq (ZMod 53)) 0).det ≠ 0 := by rw [Matrix.det_isEmpty]; decide\n']
    seen = set()
    for q, n, word in witnesses():
        chunks.append(f'private theorem normal{n} : (hankel (cubeSeq (ZMod 53)) {n}).det ≠ 0 :=\n'
                      f'  certified 0x{word:x} normal{q} (by decide) (by decide) (by decide +kernel)\n')
        seen.add(n)
    assert set(range(177, 365)) <= seen
    chunks += ['\ntheorem base53 (n : ℕ) (lo : 177≤n) (hi : n≤364) :\n'
               '    (hankel (cubeSeq (ZMod 53)) n).det ≠ 0 := by\n', cases(177,365),
               '\nend OMA.CubeHankel\n', (root / 'CubeHankelWeightEnd228624.lean').read_text()]
    return ''.join(chunks)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    args.output.write_text(generate())
