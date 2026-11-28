"""Emit a Lean kernel certificate for one short cofactor or one middle prime.

python3 rank_three_middle_blocks_245212.py row 3 31 13 OUTPUT_DIRECTORY
python3 rank_three_middle_blocks_245212.py join 13 OUTPUT_DIRECTORY
Use the pinned Lean environment to compile each row and then its join, with
the output directory on LEAN_PATH. Python only selects partition endpoints;
every interval and its coverage is proved by the generated Lean declarations.
"""
import argparse
from math import gcd, isqrt
from pathlib import Path

CUTS = {5: (4, 4), 7: (7, 6), 11: (21, 12), 13: (42, 21)}


def moments(p, e):
    power = p**e
    tax = (e+1)*power
    sigma = (p*power-1)//(p-1)
    return (p*tax-sigma)//(p-1), sigma, tax


def ilog(p, n):
    result = 0
    while n >= p:
        n //= p
        result += 1
    return result


def name(s, i, p):
    return f'RankThreeAt{s}E{i}P{p}'


def joins(names):
    if len(names) == 1:
        return names[0]
    mid = len(names)//2
    return f'(joinEvery {joins(names[:mid])} {joins(names[mid:])})'


def slices(low, high, weight, budget):
    start = low
    spent = 0
    for i in range(low, high+1):
        cost = weight(i)
        if i > start and spent + cost > budget:
            yield start, i-1
            start, spent = i, 0
        spent += cost
    yield start, high


def row(s, e, p, folder, budget, *, suffix='', part_size=0):
    middle = max(s, p)
    if {s, p} != {3, middle} or middle not in CUTS or not 1 <= e < CUTS[middle][s != 3]:
        raise ValueError('row outside the four short-cofactor ranges')
    w, y, t = moments(s, e)
    h, A, S, T = 2*s**e, 5*w, 3*y, 4*t
    small, large = A*p, 2*T*(p-1)
    if small == large or A+S > 2*T:
        raise ValueError('needs a different cofactor argument')
    if small > large:
        lo, hi = 1, 2*A//(small-large)
        fun = f'(movingRow {A} {S} {T} {p})'
        lemma = 'movingTest'

        def weight(a):
            u,v,z = moments(p,a)
            gap = 2*T*z-A*u
            base = max(2,p+1,A*u//(2*gap) if gap > 0 else 0)
            return ilog(base,A*u+S*v)+1
    else:
        lo, hi = p+1, large//(large-small)
        fun = f'(fastPair {h} {A} {S} {T} {p})'
        lemma = 'fixedTest'

        def weight(q):
            if gcd(q,h)>1 or any(q%u==0 for u in range(2,isqrt(q)+1)):
                return 1
            excess = small*q-large*(q-1)
            if excess <= 0:
                return 1
            E = 2*A*(p+q)//excess
            M = 2+3*(h.bit_length()+E*q.bit_length())
            cost = 2*A*(M+1)*q*q+A+S*q*q
            return 2*min(E,max(S*q//A+1,ilog(p,cost)+1))+1
    module = name(s,e,p)+suffix
    def header(unit, imports):
        return [*(f'import {item}' for item in imports),
                '/-! Fixed-cofactor arithmetic certificate. -/', f'namespace OMA.{unit}',
                'open OMA.RankThreeMiddle245212 OMA.CofactorEulerPair245212 OMA.CofactorGuardFast245212',
                'set_option maxRecDepth 8192', 'set_option maxHeartbeats 1000000']
    def leaves(intervals):
        return [f'private theorem b{i} : every {l} {r} {fun}=true := by decide +kernel'
                for i,(l,r) in enumerate(intervals)]
    def local_proof(group):
        return joins([f'b{i}' for i in range(len(group))])
    spans = list(slices(lo,hi,weight,budget))
    if part_size and len(spans)>part_size:
        parts=[]
        for start in range(0,len(spans),part_size):
            unit = module+'Part'+str(len(parts))
            group = spans[start:start+part_size]
            piece = header(unit,['CofactorGuardFast245212'])+leaves(group)
            piece += [f'theorem checked : every {group[0][0]} {group[-1][1]} {fun}=true := {local_proof(group)}',
                      '#print axioms checked',f'end OMA.{unit}']
            (folder/(unit+'.lean')).write_text('\n'.join(piece)+'\n')
            parts.append(unit)
        lines = header(module,parts)
        proof = joins([f'OMA.{unit}.checked' for unit in parts])
    else:
        lines = header(module,['CofactorGuardFast245212'])+leaves(spans)
        proof = local_proof(spans)
    if lemma == 'fixedTest':
        proof = f'(restore (by decide) {proof})'
    lines += [f'theorem checked : test {s} {e} {p}=true :=',
              f'  {lemma} (h:={h}) (A:={A}) (S:={S}) (T:={T})',
              f'    (by decide +kernel) (by decide) (by decide) (by decide) (by decide) {proof}',
              '#print axioms checked', f'end OMA.{module}']
    (folder/(module+'.lean')).write_text('\n'.join(lines)+'\n')
    return len(spans)


def join(p, folder, *, hard_split=False):
    bounds = CUTS[p]
    groups = [(3,p,bounds[0]),(p,3,bounds[1])]
    imports = [name(s,i,r) for s,r,L in groups for i in range(1,L)]
    if hard_split:
        imports = ['RankThreeHardRow245212' if mod=='RankThreeAt3E31P13' else mod for mod in imports]
    lines = [f'import {mod}' for mod in imports]
    module = f'RankThreeMiddle{p}'
    lines += ['/-! Both ordered short-cofactor certificates. -/', f'namespace OMA.{module}', 'open OMA.RankThreeMiddle245212 OMA.CofactorEulerPair245212 OMA.Smooth245212']
    for j,(s,r,L) in enumerate(groups):
        refs = [f'(singleTest OMA.{name(s,i,r)}.checked)' for i in range(1,L)]
        lines.append(f'theorem range{j} : rangeCheck {s} {r} {L}=true := range_from_every {joins(refs)}')
    lines += [f'theorem mass : 8≤5*X 3 (some {bounds[0]})*X {p} (some {bounds[1]}) := by decide +kernel',
              f'end OMA.{module}']
    (folder/(module+'.lean')).write_text('\n'.join(lines)+'\n')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_subparsers(dest='mode',required=True)
    one = modes.add_parser('row')
    one.add_argument('s',type=int)
    one.add_argument('e',type=int)
    one.add_argument('p',type=int)
    one.add_argument('--budget',type=int,default=60)
    one.add_argument('--part-size',type=int,default=0,help='emit separately checkable modules of this many stripes')
    combined = modes.add_parser('join')
    combined.add_argument('p',type=int,choices=CUTS)
    combined.add_argument('--hard-split',action='store_true',help='use the distributed near-resonant row')
    for mode in [one,combined]:
        mode.add_argument('folder',type=Path)
    args = parser.parse_args()
    if args.mode=='join':
        join(args.p,args.folder,hard_split=args.hard_split)
    else:
        print(f'{row(args.s,args.e,args.p,args.folder,args.budget,part_size=args.part_size)} checked intervals requested')


if __name__=='__main__':
    main()
