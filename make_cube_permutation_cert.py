"""Generate the finite certificates for the cube-sum permutation theorem.

Run: python3 make_cube_permutation_cert.py CubePermutation006063.lean
The generated file includes its Lean verification code and needs only the
standard project import. No result of this program is trusted by Lean.
"""

import argparse
from pathlib import Path


def find_matching(n):
    roots = range(2, 10)
    edges = [[(k**3 - i - 2, k) for k in roots if 0 <= k**3 - i - 2 < n]
             for i in range(n)]
    owner = [-1] * n

    def augment(i, seen):
        for j, _ in edges[i]:
            if j in seen:
                continue
            seen.add(j)
            if owner[j] < 0 or augment(owner[j], seen):
                owner[j] = i
                return True
        return False

    for i in range(n):
        augment(i, set())
    if -1 not in owner:
        rows = [0] * n
        cols = [0] * n
        for j, i in enumerate(owner):
            cols[j] = rows[i] = next(k for v, k in edges[i] if v == j)
        assert all(rows[i] == cols[rows[i]**3 - i - 2] for i in range(n))
        return rows, cols, None

    rows = set(range(n)).difference(owner)
    cols = set()
    frontier = list(rows)
    while frontier:
        for j, _ in edges[frontier.pop()]:
            if j in cols:
                continue
            cols.add(j)
            assert owner[j] >= 0
            if owner[j] not in rows:
                rows.add(owner[j])
                frontier.append(owner[j])
    for i in sorted(rows):
        reduced = rows - {i}
        neighbors = {j for x in reduced for j, _ in edges[x]}
        if len(neighbors) < len(reduced):
            rows, cols = reduced, neighbors
    assert len(cols) < len(rows)
    return None, None, (sorted(rows), sorted(cols))


def packed(items):
    return '0x' + ''.join(format(i, 'x') for i in reversed(items))


def case_tree(low, high, leaf, indent='  '):
    if high - low == 1:
        return f'{indent}obtain rfl : m = {low} := by omega\n{indent}exact {leaf(low)}\n'
    middle = (low + high) // 2
    return (f'{indent}by_cases h{middle} : m < {middle}\n' +
            f'{indent}·\n' + case_tree(low, middle, leaf, indent + '  ') +
            f'{indent}·\n' + case_tree(middle, high, leaf, indent + '  '))


def generate():
    here = Path(__file__).resolve().parent
    chunks = [(here / 'CubePermutationCore006063.lean').read_text(),
              '\nnamespace OMA.CubePermutation\n',
              'private theorem pos0 : Admits 0 := ⟨Equiv.refl _, fun i => Fin.elim0 i⟩\n']
    good = {0}
    for n in range(1, 365):
        for k in range(2, 10):
            m = k**3 - n - 1
            if m in good and m < n:
                chunks.append(f'private theorem pos{n} : Admits {n} := '
                              f'reflect (k := {k}) (by decide) (by decide) pos{m}\n')
                good.add(n)
                break
        else:
            rows, cols, hall = find_matching(n)
            if hall is None:
                chunks.append(f'private theorem pos{n} : Admits {n} :=\n'
                              f'  of_check (rows := {packed(rows)})\n'
                              f'           (cols := {packed(cols)}) (by decide +kernel)\n')
                good.add(n)
            else:
                xs, ys = hall
                chunks.append(f'private theorem neg{n} : ¬ Admits {n} :=\n'
                              f'  of_hall (by decide) (xs := {xs}) (ys := {ys}) (by decide +kernel)\n')
    assert set(range(173, 365)) <= good and 172 not in good
    chunks += ['\n/-- Robert Israel\'s 2018 conjecture on OEIS A006063. -/\n',
               'theorem israel (n : ℕ) (hn : 173 ≤ n) : Admits n := by\n',
               '  apply of_bases _ n hn\n  intro m low high\n',
               case_tree(173,365,lambda n: f'pos{n}')]
    prior = sorted(n for n in good if 0<n<173)
    assert len(prior) == 48
    chunks += ['\n/-- All positive admitted orders smaller than 173. -/\n',
               f'def earlyOrders : Finset ℕ := ({prior} : List ℕ).toFinset\n\n',
               'theorem prefix_card : earlyOrders.card = 48 := by decide +kernel\n',
               'theorem sharp : ¬ Admits 172 := neg172\n\n',
               'theorem classify_small (m : ℕ) (h : m < 173) :\n'
               '    Admits m ↔ m = 0 ∨ m ∈ earlyOrders := by\n',
               case_tree(0,173, lambda n: (
                   f'iff_of_true pos{n} (by decide +kernel)' if n in good else
                   f'iff_of_false neg{n} (by decide +kernel)')),
               '\n/-- Exact classification, including the empty permutation. -/\n'
               'theorem classification (n : ℕ) : Admits n ↔ n=0 ∨ n∈earlyOrders ∨ 173≤n := by\n'
               '  by_cases large : 173≤n\n'
               '  · exact iff_of_true (israel _ large) (Or.inr (Or.inr large))\n'
               '  · simpa [large] using classify_small n (by omega)\n']
    chunks.append('\nend OMA.CubePermutation\n')
    return ''.join(chunks)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    args.output.write_text(generate())
