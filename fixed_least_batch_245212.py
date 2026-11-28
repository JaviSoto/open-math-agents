"""Build kernel certificates for 2^k l^a p^b q^c, with fixed l,k,a.

From the pinned Formal Conjectures checkout, run
  lake env python3 /path/to/fixed_least_batch_245212.py 7 7 13 /private/tmp
after compiling FixedLeastPair245212 into the output directory. A row is
complete only when its final original-input theorem checks. Large prime
intervals need the separate divisor-count method rather than this direct scan.
"""
from argparse import ArgumentParser
from pathlib import Path

from five_fast_batch_245212 import verify
from rank_three_middle_blocks_245212 import joins, moments


def coefficients(l, k, a):
    return tuple(x*y for x, y in zip(moments(2, k), moments(l, a)))


def sources(l, k, a, span, max_prime):
    weight, sigma, mass = coefficients(l, k, a)
    gap = 2*mass - weight
    if gap <= 0:
        return {}
    length = max(4, sigma//gap + 1)
    end = 4*mass*length//(gap*length - sigma)
    if end > max_prime:
        raise ValueError(f'prefix ({l},{k},{a}) needs a prime interval through {end:,}')
    factor_max = max(l, k+1, a+1)
    start = l+1
    h = 2**k*l**a
    stem = f'FixedLeast{l}K{k}A{a}'
    ns = f'OMA.{stem}'
    header = (f'namespace {ns}\nopen OMA.CofactorEulerPair245212 OMA.FiveFastNear245212\n'
              'open OMA.RankThreeMiddle245212 (joinEvery)\n'
              'set_option maxRecDepth 65536\nset_option maxHeartbeats 0\n')
    ending = f'end {ns}\n'
    data = {}
    names = []
    for lo in range(start, end+1, span):
        hi = min(end, lo+span-1)
        mod = stem+f'S{lo}'
        names.append(f'block{lo}')
        body = (f'theorem block{lo} : every {lo} {hi} '
                f'(fast {h} {weight} {sigma} {mass} {factor_max})=true := by decide +kernel\n')
        data[mod] = ([], 'import FixedLeastPair245212\n'+header+body+ending)
    imports = list(data)
    check = joins(names) if names else '(by decide +kernel)'
    body = (f'theorem original {{p q b c : ℕ}} (pp : p.Prime) (qp : q.Prime) '
            f'(gt : {l}<p) (pq : p<q) (bp : 0<b) (cp : 0<c) :\n'
            f'  OeisA245212.a (2^{k}*{l}^{a}*p^b*q^c)≠'
            f'(ArithmeticFunction.sigma 1 (2^{k}*{l}^{a}*p^b*q^c):ℤ) :=\n'
            f'  OMA.FixedLeastPair245212.certify (L:={start}) (M:={factor_max}) '
            f'(by decide +kernel) (by decide) pp qp gt pq bp cp (by omega) '
            f'(by decide +kernel) {check}\n#print axioms original\n')
    data[stem] = (imports, ''.join(f'import {x}\n' for x in imports)+
                  'import FixedLeastPair245212\n'+header+body+ending)
    return data


if __name__ == '__main__':
    cli = ArgumentParser(description=__doc__)
    cli.add_argument('least', type=int)
    cli.add_argument('first_k', type=int)
    cli.add_argument('last_k', type=int)
    cli.add_argument('output', type=Path)
    cli.add_argument('--first-a', type=int, default=1)
    cli.add_argument('--last-a', type=int, default=10)
    cli.add_argument('--span', type=int, default=96)
    cli.add_argument('--jobs', type=int, choices=range(1,13), default=4)
    cli.add_argument('--seconds', type=int, default=240)
    cli.add_argument('--max-prime', type=int, default=10000)
    args = cli.parse_args()
    if min(args.least-2, args.first_a, args.span, args.seconds) < 1 or args.first_k < 0:
        cli.error('Use an odd prime at least three, nonnegative k and positive exponents and limits.')
    output = args.output.resolve()
    if not (output/'FixedLeastPair245212.olean').is_file():
        cli.error('Compile FixedLeastPair245212.lean into the output directory first.')
    graph = {}
    for k in range(args.first_k, args.last_k+1):
        for a in range(args.first_a, args.last_a+1):
            graph.update(sources(args.least, k, a, args.span, args.max_prime))
    if not graph:
        cli.error('No prefixes in range satisfy the strict weight inequality.')
    for name, (_, source) in graph.items():
        (output/(name+'.lean')).write_text(source)
    raise SystemExit(not verify(graph, output, args.jobs, args.seconds))
