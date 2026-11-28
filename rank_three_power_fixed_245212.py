"""Reproduce the fixed-support part of the 32 | n rank-three certificate.

Use --out /tmp --jobs 4 to compile all row modules and their family joins.
--pair P Q, --first, --last select a pilot; --join accepts a previously
completed family at the same block size. Every arithmetic row is decided by
the Lean kernel; Python only proposes the partition and its integer limits.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
from math import isqrt
from pathlib import Path

from RankThreeFourSmall_profile_245212 import ilog
from rank_three_eight_245212 import prime
from rank_three_middle_blocks_245212 import joins
from rank_three_sixteen_fixed_245212 import replay
from rounding_245212 import exponent_ceiling


PAIRS = ((7,41),(7,43),(7,47),(7,53),(7,59),(7,61),(7,67),(7,71),(7,73),
         (11,13),(11,17),(11,19),(13,17))


def radius(p, q):
    lhs = 384 * (p-1) * (q-1)
    return lhs // (lhs-321*p*q)


def candidates(p, q):
    return [r for r in range(q+1, radius(p,q)+1) if prime(r)]


def limit(r):
    ceiling = exponent_ceiling(4, r)
    return max(isqrt(r), ilog(7, 32 * 64 * r**9 * (ceiling+1)**4))


def namespace(p, q, first):
    return f"ThirtyTwoRows{p}x{q}From{first}"


def chunk(p, q, rs):
    name = namespace(p, q, rs[0])
    src = ["import RankThreePowerFixed245212",
           "/-! Fixed odd supports, with no restriction on the exponents. -/",
           f"namespace OMA.{name}",
           "open OMA.RankThreePowerFixed245212 OMA.CofactorEulerPair245212 OMA.RankThreeMiddle245212",
           "set_option maxRecDepth 65536", "set_option maxHeartbeats 2400000"]
    for r in rs:
        top = limit(r)
        src.append(f"private theorem lim{r} : OMA.RankThreePowerHeight245212.limit 5 {r}={top} := by decide +kernel")
        checks = []
        for s, i, j in ((p,q,r), (q,p,r), (r,p,q)):
            spans = []
            for lo in range(1, top+1, 12):
                hi = min(top, lo+11)
                key = f"b{r}s{s}e{lo}"
                src.append(f"private theorem {key} : every {lo} {hi} (slot 5 {s} {i} {j})=true := by decide +kernel")
                spans.append(key)
            key = f"c{r}s{s}"
            src.extend([f"private theorem {key} : check 5 {r} {s} {i} {j}=true := by",
                        f"  rw [check,lim{r}]", f"  exact {joins(spans)}"])
            checks.append(key)
        src.append(f"theorem row{r} : tables 5 {p} {q} {r}=true := by simp only [tables,{','.join(checks)}];rfl")
    src.append(f"end OMA.{name}")
    return name, "\n".join(src)+"\n"


def family(p, q, block):
    rs = candidates(p,q)
    groups = {r:rs[i-i%block] for i,r in enumerate(rs)}
    name = f"ThirtyTwoFamily{p}x{q}"
    src = ["import RankThreeThirtyTwoSupport245212", "import KernelPrimeWindow245212",
           *[f"import {namespace(p,q,r)}" for r in dict.fromkeys(groups.values())],
           "/-! Join the finite prime support rows at original-input level. -/",
           f"namespace OMA.{name}",
           "open OMA.RankThreePowerFixed245212 OMA.CofactorEulerPair245212 OMA.RankThreeThirtyTwoSupport245212",
           "open scoped ArithmeticFunction.sigma",
           "open private OMA.CofactorEulerPair245212.checked from CofactorEulerDecision245212",
           "set_option maxRecDepth 65536", "set_option maxHeartbeats 2400000"]
    pieces = []
    for idx in range(0, len(rs), 24):
        section = rs[idx:idx+24]
        lo = q+1 if not idx else rs[idx-1]+1
        hi = radius(p,q) if idx+24>=len(rs) else section[-1]
        src.extend([
            f"private def allow{idx} : List ℕ := [{','.join(map(str,section))}]",
            f"private theorem choices{idx} : every {lo} {hi} (fun r=>decide (OMA.KernelPrimeWindow245212.trial r=true → r∈allow{idx}))=true := by decide +kernel",
            f"private theorem rows{idx} : ∀r∈allow{idx},tables 5 {p} {q} r=true := by",
            f"  simp only [allow{idx},List.forall_mem_cons,List.not_mem_nil]",
            "  exact ⟨"+",".join(f"OMA.{namespace(p,q,groups[r])}.row{r}" for r in section)+",fun _ h=>h.elim⟩",
            f"private theorem pass{idx} {{r:ℕ}} (pr:r.Prime) (lb:{lo}≤r) (ub:r≤{hi}) : tables 5 {p} {q} r=true :=",
            f"  rows{idx} r (of_decide_eq_true (OMA.CofactorEulerPair245212.checked choices{idx} lb ub) ((OMA.KernelPrimeWindow245212.correct _).mpr pr))"])
        pieces.append((idx,hi))
    src.extend([f"theorem original {{r a b c : ℕ}} (pr : r.Prime) (large : {q}<r) (ap : 0<a) (bp : 0<b) (cp : 0<c) :",
                f"    OeisA245212.a (32*{p}^a*{q}^b*r^c)≠(σ 1 (32*{p}^a*{q}^b*r^c):ℤ) := by",
                "  intro eqn", f"  have ec:=cap (p:={p}) (q:={q}) (by decide) (by decide) pr (by decide) (by decide) large ap eqn",
                f"  have num:=integer_cap (by decide : Nat.Prime {p}) (by decide : Nat.Prime {q}) pr ec",
                f"  have yes : tables 5 {p} {q} r=true := by"])
    for idx,hi in pieces[:-1]:
        src.extend([f"    by_cases h{idx}:r≤{hi}", f"    · exact pass{idx} pr (by omega) h{idx}"])
    src.extend([f"    exact pass{pieces[-1][0]} pr (by omega) (by omega)",
                f"  exact OMA.RankThreePowerFixed245212.original (k:=5) (p:={p}) (q:={q}) (by decide) (by omega) (by decide) (by decide) pr (by decide) (by decide) large ap bp cp yes eqn",
                "#print axioms original", f"end OMA.{name}"])
    return name,"\n".join(src)+"\n"


def materialize(out, pair):
    name, source = pair
    path = out/(name+".lean")
    if not path.exists() or path.read_text()!=source:
        path.write_text(source)
    return path


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--out", type=Path, required=True)
    cli.add_argument("--pair", type=int, nargs=2)
    cli.add_argument("--first", type=int, default=0)
    cli.add_argument("--last", type=int, default=2792)
    cli.add_argument("--block", type=int, default=4)
    cli.add_argument("--jobs", type=int, default=0)
    cli.add_argument("--cap", type=int, default=3200)
    cli.add_argument("--join", action="store_true")
    args = cli.parse_args()
    if not args.out.is_dir() or args.block<=0 or args.jobs<0:
        cli.error("need existing output folder, positive block size, and nonnegative job count")
    paths = []
    for p,q in ([tuple(args.pair)] if args.pair else PAIRS):
        if (p,q) not in PAIRS:
            cli.error("this pair has no bounded support family")
        if args.join:
            paths.append(materialize(args.out, family(p,q,args.block)))
        else:
            rs = candidates(p,q)
            for i in range(0,len(rs),args.block):
                group = rs[i:i+args.block]
                if args.first <= group[0] <= args.last:
                    paths.append(materialize(args.out, chunk(p,q,group)))
    if args.jobs:
        with ThreadPoolExecutor(args.jobs) as pool:
            tasks = {pool.submit(replay,path,args.cap):path for path in paths}
            for job in as_completed(tasks):
                print(tasks[job].stem, job.result(), flush=True)
    print(f"{len(paths)} modules")


if __name__ == "__main__":
    main()
