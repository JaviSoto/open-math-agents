"""Generate exact cofactor certificates for two unrestricted odd prime powers.

Use e.g. python3 rank_three_five_rows_245212.py 7 9 /tmp/FiveHigh245212.lean
for all surviving (k,a) in that dyadic interval. Each middle-prime interval
is an ordinary, independently checked Lean theorem.
"""
from argparse import ArgumentParser
from pathlib import Path
from rank_three_middle_blocks_245212 import joins, moments
from RankThreeFourSmall_profile_245212 import prime


def bounds(k,a):
    A,S,T=(u*v for u,v in zip(moments(2,k),moments(5,a)))
    h=2**k*5**a; D=2*T-A; L=max(4,S//D+1)
    return h,A,S,T,4*T*L//(D*L-S)


def build(start,stop,min_a=1,max_a=31,width=12,use_count=False,cutoff=None):
    rule="OMA.RankThreeFiveCount245212.row" if use_count else "OMA.RankThreeFourSmallCompact245212.run"
    sieve="OMA.RankThreeFiveCount245212.test" if use_count else "sieve"
    lines=["import RankThreeFiveCount245212" if use_count else "import RankThreeFiveTail245212",
           "/-! Finite first-prime intervals; both prime powers remain unrestricted. -/",
           "namespace OMA.RankThreeFiveRows245212","open OMA.CofactorEulerPair245212 OMA.RankThreeFiveTail245212",
           "open OMA.RankThreeMiddle245212 (joinEvery)","open scoped ArithmeticFunction.sigma",
           "set_option maxRecDepth 65536","set_option maxHeartbeats 2400000"]
    for k in range(start,stop+1):
        for a in range(min_a,min(max_a,{4:31,5:4,6:2,7:1,8:1,9:1}[k])+1):
            h,A,S,T,cut=bounds(k,a)
            if cutoff is not None:
                cut=min(cutoff,cut)
            labels=[]
            hot={}
            if use_count:
                for p in range(7,min(cut,2*T//(2*T-A)+1)+1):
                    delta=A*p-2*T*(p-1)
                    if prime(p) and delta>0 and 2*A//delta>96:
                        hot[p]=2*A//delta
            lo=7
            while lo<=cut:
                if lo in hot:
                    blocks=[];end=hot[lo]
                    for j in range(1,end+1,12):
                        t=min(j+11,end);name=f"high{k}_{a}_{lo}_{j}"
                        lines.append(f"private theorem {name} : every {j} {t} (OMA.RankThreeEightMoving245212.line {A} {S} {T} {lo} {lo+1})=true := by decide +kernel")
                        blocks.append(name)
                    label=f"block{k}_{a}_{lo}"
                    lines.append(f"private theorem {label} : every {lo} {lo} ({rule} {h} {A} {S} {T})=true := OMA.RankThreeEightMoving245212.single (OMA.RankThreeFiveCount245212.high (E:={end}) (by decide) (by decide) (by decide) (by decide) {joins(blocks)})")
                    labels.append(label);lo+=1;continue
                hi=min(lo+width-1,cut,min((p-1 for p in hot if p>lo),default=cut))
                label=f"block{k}_{a}_{lo}"
                lines.append(f"private theorem {label} : every {lo} {hi} ({rule} {h} {A} {S} {T})=true := by decide +kernel")
                labels.append(label);lo=hi+1
            bound=(f"(OMA.RankThreeFourSmallHarmonic245212.primeCut (wt {k} {a}) (sg {k} {a}) (2*ta {k} {a}))"
                   if cutoff is None else str(cut))
            lines.append(f"theorem c{k}_{a} : every 7 {bound} ({sieve} {k} {a})=true := {joins(labels)}")
    lines.extend(["end OMA.RankThreeFiveRows245212",""])
    return "\n".join(lines)


if __name__=="__main__":
    cli=ArgumentParser(description=__doc__)
    cli.add_argument("start",type=int);cli.add_argument("stop",type=int);cli.add_argument("out",type=Path)
    cli.add_argument("--min-a",type=int,default=1);cli.add_argument("--max-a",type=int,default=31)
    cli.add_argument("--width",type=int,default=12)
    cli.add_argument("--count",action="store_true",help="use the exact divisor-count interval for large primes")
    cli.add_argument("--cutoff",type=int,help="certify only the interval through this upper endpoint")
    args=cli.parse_args()
    args.out.write_text(build(args.start,args.stop,args.min_a,args.max_a,args.width,args.count,args.cutoff))
