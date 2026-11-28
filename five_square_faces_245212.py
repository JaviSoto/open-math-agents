"""Certify the three infinite-exponent faces of 9*5^a*7^b*11^c.

Each finite binary tree partitions two positive unbounded exponent axes.
All interval arithmetic is rational; reaching a search budget is inconclusive.
"""
from fractions import Fraction as F
from math import prod
from pathlib import Path
from argparse import ArgumentParser
from odd_four_245212 import factors
from equal_power_245212 import split

PRIMES=(5,7,11)


def certify(face,gap,node_limit=100000,tree=None):
    axes=tuple(p for p in PRIMES if p!=face)
    fixed=F(34,27)*F(face,face-1)
    stack=[((1,None),(1,None))]
    count=0
    smallest=None
    while stack:
        box=stack.pop()
        count+=1
        if count>node_limit:
            raise ValueError("unresolved node budget",face,box)
        data=[factors((b,(p,p))) for b,p in zip(box,axes)]
        low=fixed*prod(x[0] for x in data)
        high=fixed*prod(x[1] for x in data)
        separation=max(low-2,2-high)
        if separation>gap:
            smallest=separation if smallest is None else min(smallest,separation)
            if tree is not None:
                tree[box]=None
            continue
        varying=[i for i,(lo,hi) in enumerate(box) if lo!=hi]
        if not varying:
            raise ValueError("unresolved singleton",face,box,float(separation))
        i=max(varying,key=lambda i:data[i][1]-data[i][0])
        lo,hi=box[i]
        cut=split(lo,hi)
        if tree is not None:
            tree[box]=i,cut
        stack.append(box[:i]+((cut+1,hi),)+box[i+1:])
        stack.append(box[:i]+((lo,cut),)+box[i+1:])
    return count,smallest


def write_lean(path):
    lines=["import FiveFaceCore245212","","namespace OMA.FiveFace245212",
           "open OMA.Smooth245212","set_option maxHeartbeats 15000000","set_option maxRecDepth 60000"]
    def band(interval):
        l,h=interval
        return f"⟨{l},"+("none" if h is None else f"some {h}")+"⟩"
    for face in PRIMES:
        p,q=[x for x in PRIMES if x!=face]
        fixed=F(34,27)*F(face,face-1)
        A=f"({fixed.numerator}/{fixed.denominator}:ℚ)"
        tree={}
        certify(face,F(1,10**8),tree=tree)
        def emit(box,name,write=False):
            node=tree[box]
            if node is None:
                text=".leaf"
            else:
                i,c=node
                l,h=box[i]
                left=box[:i]+((l,c),)+box[i+1:]
                right=box[:i]+((c+1,h),)+box[i+1:]
                text=f"(.{('fst','snd')[i]} {c} {emit(left,name+'l')} {emit(right,name+'r')})"
            if not write:
                return text
            typ=f"Good {A} {p} {q} {band(box[0])} {band(box[1])}"
            if text.count(".leaf")<=18:
                lines.append(f"theorem {name} : {typ} := sound (by norm_num) (by decide) (by decide) {text} (by decide +kernel)")
            else:
                emit(left,name+'l',True)
                emit(right,name+'r',True)
                lines.append(f"theorem {name} : {typ} := {('first','second')[i]} (c:={c}) {name}l {name}r")
        emit(((1,None),(1,None)),f"face{face}",True)
        lines.append(f"#print axioms face{face}")
    path.write_text("\n".join(lines+["end OMA.FiveFace245212",""]))


if __name__=="__main__":
    parser=ArgumentParser(description=__doc__)
    parser.add_argument("--lean",type=Path)
    args=parser.parse_args()
    for p in PRIMES:
        print(p,certify(p,F(1,10**8)),flush=True)
    if args.lean:
        write_lean(args.lean)
