"""Generate 32·7ᵃ·qᵇ·rᶜ certificates with r unrestricted.

    python3 rank_three_power_rows_245212.py 11 /tmp/ThirtyTwoPair7To11.lean
"""
import argparse
from pathlib import Path
from rank_three_sixteen_rows_245212 import table
from rank_three_eight_rows_245212 import joins, row
from rank_three_sixteen_fixed_245212 import replay
from concurrent.futures import ThreadPoolExecutor,as_completed

ENDS={11:3,13:4,17:6,19:7,23:11,29:20,31:25,37:82}


def moving(q,width=16):
    end=ENDS[q]
    common={"dyadic":(32,321,63,192),"tag":"ThirtyTwo"}
    parts=["import RankThreeThirtyTwoMoving245212","/-! Unrestricted third prime at dyadic order five. -/",
           table(7,q,end,width,**common),table(q,7,end,width,**common),
           f"namespace OMA.ThirtyTwoMoving7P{q}","open OMA.RankThreeThirtyTwoMoving245212","open scoped ArithmeticFunction.sigma",
           f"theorem exclude {{r a b c : ℕ}} (pr : r.Prime) (large : {q}<r) (ap : 0<a) (bp : 0<b) (cp : 0<c) :",
           f"    OeisA245212.a (32*7^a*{q}^b*r^c)≠(σ 1 (32*7^a*{q}^b*r^c):ℤ) :=",
           f"  close (k:=5) (l:={end}) (u:={end}) (by decide) (by decide) pr (by decide) (by decide) large ap bp cp (by decide +kernel)",
           f"    OMA.ThirtyTwoShort7P{q}.rows OMA.ThirtyTwoShort{q}P7.rows",
           "#print axioms exclude",f"end OMA.ThirtyTwoMoving7P{q}"]
    return "\n".join(parts)+"\n"


def parts(q,dir,width,block):
    end=ENDS[q]
    imports=[]
    paths=[]
    for s,p in ((7,q),(q,7)):
        names=[]
        for lo in range(1,end,block):
            hi=min(end-1,lo+block-1)
            stem=f"ThirtyTwo{s}P{p}From{lo}"
            text=["import RankThreeThirtyTwoMoving245212","/-! A consecutive interval of exact first powers. -/"]
            for e in range(lo,hi+1):
                text.append(row(s,e,p,width=width,dyadic=(32,321,63,192),tag="ThirtyTwo").split("\n",1)[1].replace("/-!","/-"))
            terms=[f"(single (f:=atom {s} {p}) OMA.ThirtyTwoAt{s}E{e}P{p}.certificate)" for e in range(lo,hi+1)]
            text.extend([f"namespace OMA.{stem}","open OMA.RankThreeThirtyTwoMoving245212 OMA.CofactorEulerPair245212",
                         "open OMA.RankThreeMiddle245212 (joinEvery)",
                         f"theorem rows : every {lo} {hi} (atom {s} {p})=true := {joins(terms)}",f"end OMA.{stem}"])
            path=dir/(stem+".lean");path.write_text("\n".join(text)+"\n")
            paths.append(path);names.append(f"OMA.{stem}.rows");imports.append(f"import {stem}")
        if s==7:
            at_first=joins(names)
        else:
            at_second=joins(names)
    tail=moving(q,width).rsplit(f"namespace OMA.ThirtyTwoMoving7P{q}",1)[1]
    tail=tail.replace("open scoped ArithmeticFunction.sigma","open OMA.RankThreeMiddle245212 (joinEvery)\nopen scoped ArithmeticFunction.sigma")
    tail=tail.replace(f"OMA.ThirtyTwoShort7P{q}.rows OMA.ThirtyTwoShort{q}P7.rows",at_first+" "+at_second)
    final=dir/f"ThirtyTwoPair7To{q}.lean"
    final.write_text("\n".join(imports)+f"\n/-! Exclusion for arbitrary last prime and exponents. -/\nnamespace OMA.ThirtyTwoMoving7P{q}"+tail)
    return paths,final


if __name__=="__main__":
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument("q",type=int,choices=ENDS)
    cli.add_argument("out",type=Path)
    cli.add_argument("--width",type=int,default=16)
    cli.add_argument("--modules",action="store_true",help="OUT is an existing folder; generate independent proofs and their join")
    cli.add_argument("--jobs",type=int,default=0)
    cli.add_argument("--block",type=int,default=10)
    args=cli.parse_args()
    if args.modules:
        paths,final=parts(args.q,args.out,args.width,args.block)
        if args.jobs:
            with ThreadPoolExecutor(args.jobs) as pool:
                tasks=[pool.submit(replay,path,3300) for path in paths]
                for job in as_completed(tasks):
                    print(job.result(),flush=True)
            print(replay(final,3300),flush=True)
    else:
        args.out.write_text(moving(args.q,args.width))
