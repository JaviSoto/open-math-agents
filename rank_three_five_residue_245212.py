"""Compute the first locally admissible divisor count for each 2,5 prefix.

The scan supplies cutoffs, not proofs of exclusions; RankThreeFiveResidue245212
verifies all residue exclusions without using this program as an oracle.
"""
from functools import lru_cache
from math import gcd
from argparse import ArgumentParser
from pathlib import Path
from rank_three_middle_blocks_245212 import joins
from rank_three_five_rows_245212 import bounds

MODS=(2,3,4,5,8,9,7,11,13,16,25,27,32,49,64,81,125,128)


@lru_cache(None)
def residue_classes(e,m):
    out=set()
    for x in range(1,m):
        if gcd(x,m)!=1: continue
        t=w=s=1
        for j in range(1,e+1):
            t=t*x%m; s=(s+t)%m;w=(w+(j+1)*t)%m
        out.add((w,s,(e+1)*t%m))
    return out


def obstruction(A,S,H,x,y):
    for m in MODS:
        if not any((A*w*u+S*v*z-H*t*j)%m==0 for w,v,t in residue_classes(x-1,m)
                   for u,z,j in residue_classes(y-1,m)):
            return m
    return None


def refined(k,a):
    h,A,S,T,old=bounds(k,a); D=2*T-A; n0=max(4,S//D+1)
    for n in range(n0,n0+2048):
        if any(n%x==0 and obstruction(A,S,2*T,x,n//x) is None for x in range(2,n//2+1)):
            return n0,n,max(128,4*T*n//(D*n-S))
    raise ValueError((k,a))


def certificate(k,a):
    h,A,S,T,_=bounds(k,a);n0,L,prime_bound=refined(k,a)
    test=f"(fun n=>!(survives {A} {S} {2*T} n))"
    lines=["import RankThreeFiveResidue245212","/-! Middle-prime limit from local obstructions to short divisor counts. -/",
           f"namespace OMA.FiveLocal{k}x{a}","open OMA.RankThreeFiveResidue245212 OMA.CofactorEulerPair245212",
           "open OMA.RankThreeMiddle245212 (joinEvery)","set_option maxRecDepth 65536",
           "set_option maxHeartbeats 2400000"]
    labels=[]
    for n in range(n0,L):
        name=f"n{n}"
        lines.append(f"private theorem {name} : every {n} {n} {test}=true := by decide +kernel")
        labels.append(name)
    ref=joins(labels) if labels else "(by decide +kernel)"
    lines+=[f"theorem clear : every {n0} {L-1} {test}=true := {ref}",
            f"end OMA.FiveLocal{k}x{a}"]
    return "\n".join(lines)+"\n"


if __name__=="__main__":
    parser=ArgumentParser(description=__doc__)
    parser.add_argument("--certificate",nargs=3,metavar=("K","A","OUTPUT"))
    args=parser.parse_args()
    if args.certificate:
        k,a,path=args.certificate
        Path(path).write_text(certificate(int(k),int(a)))
    else:
        for k,m in [(4,31),(5,4),(6,2),(7,1),(8,1),(9,1)]:
            for a in range(1,m+1):
                print(k,a,*(refined(k,a)),flush=True)
