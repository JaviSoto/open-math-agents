"""Write a single original-import proof of 32 | n, exact dyadic order 5.

Run in the research workspace. --sample writes a quick check of the same
compact arithmetic proof format; GRID sources need no other local imports.
"""
import argparse
from pathlib import Path
import re

from rank_three_eight_rows_245212 import near
from rank_three_middle_blocks_245212 import joins, moments
from rank_three_power_fixed_245212 import PAIRS, candidates, family, limit, namespace
from rank_three_power_rows_245212 import ENDS
from rank_three_sixteen_source_245212 import core_sources
from standalone_odd_support_245212 import assemble


def split_decide(size,width):
    depth=max(0,((max(0,size)+width-1)//width-1).bit_length()) if size>width else 0
    cmds=[f"  iterate {depth} (all_goals apply OMA.RankThreePowerCert245212.half)"] if depth else []
    return "\n".join(cmds+["  all_goals decide +kernel"])


def atom(s,e,p,width,sharp=False):
    w,z,t=moments(s,e)
    h,A,S,T=32*s**e,321*w,63*z,192*t
    R=max(s,p)+1
    num=A*p
    den=2*T*(p-1)
    if num>den:
        size=(max(0,(A*p-1)//((p-1)*(num-den))-1) if sharp else 2*A//(num-den))
        proof=f"high (B:={size}) (by decide +kernel)"
    else:
        Q=den//(den-num)
        if Q<=R+128:
            size=Q+1-R
            proof=f"small (Q:={Q}) (by decide +kernel)"
        else:
            size=near(h,A,S,p,Q)
            proof=f"far (Q:={Q}) (E:={size}) (by decide +kernel) (by decide +kernel)"
    return f"private theorem e{s}_{e}_{p} : atom 5 {s} {p} {e}=true := by\n  apply {proof}\n"+split_decide(size,width)


def moving(q,width,sharp=False):
    end=ENDS[q]
    name=f"OMA.ThirtyTwoMoving7P{q}"
    src=["import RankThreePowerCert245212",f"namespace {name}",
         "open OMA.RankThreePowerCert245212 OMA.RankThreePowerPrefix245212",
         "open OMA.CofactorEulerPair245212 (every)","open OMA.RankThreeMiddle245212 (joinEvery)",
         "open scoped ArithmeticFunction.sigma","set_option maxHeartbeats 4000000","set_option maxRecDepth 65536"]
    row_ids=[]
    for s,p in ((7,q),(q,7)):
        src.extend(atom(s,e,p,width,sharp) for e in range(1,end))
        row=f"row{s}_{p}"
        terms=[f"(single (f:=atom 5 {s} {p}) e{s}_{e}_{p})" for e in range(1,end)]
        src.append(f"private theorem {row} : every 1 {end-1} (atom 5 {s} {p})=true := {joins(terms)}")
        row_ids.append(row)
    src.extend([f"theorem exclude {{r a b c : ℕ}} (pr : r.Prime) (large : {q}<r) (ap : 0<a) (bp : 0<b) (cp : 0<c) :",
                f"    OeisA245212.a (32*7^a*{q}^b*r^c)≠(σ 1 (32*7^a*{q}^b*r^c):ℤ) :=",
                f"  close (k:=5) (l:={end}) (u:={end}) (by decide) (by decide) pr (by decide) (by decide) large ap bp cp (by decide +kernel) {' '.join(row_ids)}",
                f"end {name}"])
    return "\n".join(src)+"\n"


def fixed(p,q,group,width=12):
    name=namespace(p,q,group[0])
    src=["import RankThreePowerCert245212",f"namespace OMA.{name}",
         "open OMA.RankThreePowerFixed245212 (tables)","open OMA.RankThreePowerCert245212 (table72)",
         "set_option maxHeartbeats 3200000","set_option maxRecDepth 65536"]
    for r in group:
        src.append(f"theorem row{r} : tables 5 {p} {q} {r}=true := by apply table72 <;> decide +kernel")
    src.append(f"end OMA.{name}")
    return "\n".join(src)+"\n"


def build(sample=False, preflight=False, fast=False):
    if sample:
        return (moving(11,12)+fixed(7,41,[43],12).replace("import RankThreePowerCert245212\n","")+
                "#print axioms OMA.ThirtyTwoMoving7P11.exclude\n#print axioms OMA.ThirtyTwoRows7x41From43.row43\n")
    sources=core_sources()
    # Only the generic prefix proof and the bounded rank-three pattern
    # are needed; the previously certified k=4 cases are independent.
    sources["RankThreePowerPrefix245212"]=Path("RankThreePowerPrefix245212.lean").read_text().replace(
        "import RankThreeSixteenMoving245212","import RankThreeEightMoving245212\nimport RankThreeFourLargeSmall245212\nimport RankThreeMiddleBlocks245212")
    tables=sources["SixteenTable245212"].split("def panel ")[0]
    tables=tables.replace("import RankThreeSixteenFixed245212","import CofactorEulerBounds245212")
    sources["SixteenTable245212"]=tables.replace(" OMA.RankThreeSixteenFixed245212","")+"\nend OMA.SixteenTable245212\n"
    short=sources["SixteenMin245212"].split("def slot ")[0]
    if fast:
        short=short.split("def panel ")[0]
    sources["SixteenMin245212"]=(short.replace("import SixteenTable245212","import SixteenTable245212\nimport RankThreeFourSmallCut245212").replace(
        "open OMA.RankThreeSixteenFixed245212 OMA.CofactorEulerPair245212","open OMA.CofactorEulerPair245212")+"\nend OMA.SixteenMin245212\n")
    for name in ("RankThreePowerFixed245212","RankThreePowerPrefix245212"):
        content=sources.get(name,Path(name+".lean").read_text())
        sources[name]=re.sub(r"(?<![.\w])tax\b","OMA.Large245212.tax",content)
    if fast:
        sources["RankThreePowerBands245212"]=Path("RankThreePowerBands245212.lean").read_text().replace(
            "import RankThreePowerFixed245212","import RankThreePowerHeight245212\nimport SixteenMin245212")
        for name in ("RankThreeBandTable245212","RankThreeBandPower245212"):
            sources[name]=re.sub(r"(?<![.\w])tax\b","OMA.Large245212.tax",Path(name+".lean").read_text())
        sources["RankThreePowerFixed245212"]=(sources["RankThreePowerFixed245212"].replace(
            "import SixteenMin245212","import RankThreeBandPower245212").replace(
            "OMA.SixteenMin245212.panel (","OMA.RankThreeBandPower245212.panel 3 (").replace(
            "OMA.SixteenMin245212.panel_sound ","OMA.RankThreeBandPower245212.panel_sound 3 "))
        ordinary="2*A/(A*p-2*T*(p-1))"
        sharp="OMA.RankThreePowerCut245212.cutoff A (2*T) p"
        sources["RankThreeEightMoving245212"]=(sources["RankThreeEightMoving245212"]
            .replace("import RankThreeFourSmallFast245212","import RankThreeFourSmallFast245212\nimport RankThreePowerCut245212")
            .replace(ordinary,sharp)
            .replace("have upper:=short_first","have upper:=OMA.RankThreePowerCut245212.bounded")
            .replace("checked ok ap (by omega)","checked ok ap upper"))
        sources["RankThreePowerPrefix245212"]=sources["RankThreePowerPrefix245212"].replace(ordinary,sharp)
        sources["RankThreePowerCert245212"]=Path("RankThreePowerCert245212.lean").read_text().replace(
            "2*A k s e/(A k s e*p-2*T k s e*(p-1))","OMA.RankThreePowerCut245212.cutoff (A k s e) (2*T k s e) p")
    for q in ENDS:
        sources[f"ThirtyTwoPair7To{q}"]=moving(q,16,sharp=fast)
    for p,q in PAIRS:
        rs=candidates(p,q)
        for i in range(0,len(rs),4):
            group=rs[i:i+4]
            sources[namespace(p,q,group[0])]=fixed(p,q,group)
        name,content=family(p,q,4)
        sources[name]=content
    root="RankThreeThirtyTwoLarge245212"
    if preflight:
        root="ThirtyTwoProofSample"
        sources[root]="import ThirtyTwoPair7To11\nimport ThirtyTwoFamily13x17\nimport RankThreeThirtyTwoJoin245212\n"
    source=assemble(root,"OEIS A245212: exact dyadic order five, three odd primes with least at least seven.",sources=sources)
    audits=("#print axioms OMA.ThirtyTwoMoving7P11.exclude\n#print axioms OMA.ThirtyTwoFamily13x17.original"
            if preflight else f"#print axioms OMA.{root}.original")
    if fast:
        # Short, stable names for private generated table groups, not
        # mathematical declarations used by the research papers.
        source=re.sub(r"ThirtyTwoRows(\d+)x(\d+)From(\d+)",r"Rows\1_\2_\3",source)
    return re.sub(r"^import Mathlib.*\n|^#print axioms .+\n","",source,flags=re.M)+f"\n{audits}\n"


if __name__=="__main__":
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument("output",type=Path)
    cli.add_argument("--sample",action="store_true")
    cli.add_argument("--preflight",action="store_true",help="test all generic proofs, a finite family, and a moving family with only the original import")
    cli.add_argument("--fast",action="store_true",help="use the two-interval p-adic terminal sieve for bounded supports")
    args=cli.parse_args()
    args.output.write_text(build(args.sample,args.preflight,args.fast))
