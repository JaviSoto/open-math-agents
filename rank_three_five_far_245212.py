"""Generate a Lean certificate for all middle primes above a fixed cutoff.

Example: python3 rank_three_five_far_245212.py 4 26 /tmp/Far426.lean .
The cutoffs select how to partition proofs: Lean checks the underlying
inequalities, residue obstructions, remaining rows, and interval coverage.
"""
from argparse import ArgumentParser
from math import gcd
from pathlib import Path
from rank_three_five_rows_245212 import bounds
from rank_three_five_residue_245212 import MODS, residue_classes
from rank_three_middle_blocks_245212 import joins


def generate(k,a,cut=None,chunk=512):
    _,A,S,T,_=bounds(k,a)
    H=2*T
    D=H-A
    g=gcd(A,gcd(S,H))
    lo=cut or max(129,4*H//D+1)
    first=max(4,S//D+1)
    last=lo*S//(lo*D-2*H)
    lines=['import RankThreeFiveFar245212',
           '/-! Check the terminal divisor counts above the middle-prime cutoff. -/',
           f'namespace OMA.FiveFar{k}x{a}', 'open OMA.RankThreeFiveFar245212 OMA.CofactorEulerPair245212',
           'open OMA.RankThreeMiddle245212 (joinEvery)', 'open OMA.RankThreeEightMoving245212 (single)',
           'set_option maxHeartbeats 2400000','set_option maxRecDepth 65536']
    bucket_names=[]
    for n in range(first,last+1):
        cap=2*H*n//(D*n-S)
        specials={}
        for x in range(2,n//2+1):
            if n%x:
                continue
            y=n//x
            veto=next((m for m in MODS if m<lo and not any(
                ((A//g)*w*u+(S//g)*v*z-(H//g)*t*j)%m==0 for w,v,t in residue_classes(x-1,m)
                for u,z,j in residue_classes(y-1,m))),None)
            if veto:
                continue
            scans=[]
            for p in range(lo,cap+1,chunk):
                high=min(p+chunk-1,cap)
                name=f'p{n}_{x}_{p}'
                lines.append(f'private theorem {name} : every {p} {high} (fixed {A} {S} {T} {x} {y})=true := by decide +kernel')
                scans.append(name)
            name=f'x{n}_{x}'
            ref=joins(scans) if scans else '(by decide +kernel)'
            lines.append(f'private theorem {name} : every {x} {x} (splitPair {A} {S} {T} {lo} {n})=true := single (by_scan {ref})')
            specials[x]=name
        inner=[]
        x=2
        while x<=n//2:
            if x in specials:
                inner.append(specials[x]);x+=1
                continue
            high=min([t-1 for t in specials if t>x]+[n//2])
            name=f'local{n}_{x}'
            lines.append(f'private theorem {name} : every {x} {high} (splitPair {A} {S} {T} {lo} {n})=true := by decide +kernel')
            inner.append(name);x=high+1
        name=f'n{n}'
        lines.append(f'private theorem {name} : every {n} {n} (bucket {A} {S} {T} {lo})=true := single {joins(inner)}')
        bucket_names.append(name)
    proof = joins(bucket_names) if bucket_names else '(by decide +kernel)'
    lines.append(f'theorem scan : every {first} {last} (bucket {A} {S} {T} {lo})=true := {proof}')
    lines.append(f'end OMA.FiveFar{k}x{a}')
    return '\n'.join(lines)+'\n'


if __name__=='__main__':
    parser=ArgumentParser(description=__doc__)
    parser.add_argument('k',type=int);parser.add_argument('a',type=int);parser.add_argument('output',type=Path)
    parser.add_argument('--cut',type=int);parser.add_argument('--chunk',type=int,default=512)
    args=parser.parse_args()
    args.output.write_text(generate(args.k,args.a,args.cut,args.chunk))
