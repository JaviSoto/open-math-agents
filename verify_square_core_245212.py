"""Generate and kernel-check all finite rows for the square-core theorem.

Run with lake env python3 from the pinned Formal Conjectures checkout with
the two merged OMA modules built. The build directory is reusable.
"""
from argparse import ArgumentParser
from pathlib import Path
import subprocess
from verify_four_odd_245212 import replay

SOURCES = ["EvenScreen245212","SquareCoreBound245212","SquareIntervals245212","SquareSolution245212"]
ROOT = "SquareComplete245212"
THEOREM = "OMA.SquareIntervals245212.no_square_core"


def put(path, text):
    if not path.exists() or path.read_text()!=text:
        path.write_text(text)


def combine(lo, hi, indent):
    if lo==hi:
        return [indent+f"obtain rfl : k={lo} := by omega",indent+f"exact row{lo}"]
    mid=(lo+hi)//2
    lhs=combine(lo,mid,indent+"  ")
    rhs=combine(mid+1,hi,indent+"  ")
    lhs[0]=indent+"· "+lhs[0].lstrip()
    rhs[0]=indent+"· "+rhs[0].lstrip()
    return [indent+f"by_cases b{mid} : k≤{mid}",*lhs,*rhs]


def generate(src):
    here=Path(__file__).resolve().parent
    for module in SOURCES:
        put(src/(module+".lean"),(here/(module+".lean")).read_text())
    names=[]
    for lo in range(1,175,6):
        name=f"SquareRows{lo:03}245212"
        names.append(name)
        lines=["import SquareIntervals245212","namespace OMA.SquareIntervals245212"]
        for k in range(lo,min(lo+6,175)):
            lines += ["set_option maxRecDepth 100000 in","set_option maxHeartbeats 12000000 in",
                      f"theorem row{k} : row {k}=true := by decide +kernel"]
        put(src/(name+".lean"),"\n".join(lines+["end OMA.SquareIntervals245212",""]))
    lines=["import SquareSolution245212",*("import "+n for n in names),
           "namespace OMA.SquareIntervals245212","open scoped ArithmeticFunction.sigma",
           "private theorem rows (k : ℕ) (low : 1≤k) (high : k≤174) : row k=true := by",
           *combine(1,174,"  "),
           """theorem no_square_core {k q p : ℕ} (hk : 1≤k) (hq : q.Prime) (hp : p.Prime)
    (oq : Odd q) (op : Odd p) (ne : p≠q) :
    OeisA245212.a (p*(2^k*q^2))≠(ArithmeticFunction.sigma 1 (p*(2^k*q^2)):ℤ) := by
  intro eqn
  obtain ⟨cut,cap,hd,hn⟩ := OMA.SquareCoreBound245212.original_bounds hk hq hp oq op ne eqn
  let z : ℤ := 2^(k+1)
  have d : 0<(denominator k z).eval q := by rw [dv]; exact hd
  have n : (numerator k z).eval q=(p:ℤ)*(denominator k z).eval q := by rw [nv,dv]; exact hn
  have small : 3≤q := by have := hq.two_le; have := oq.not_two_dvd_nat; omega
  exact sound _ _ oq d n 23 3 (2^20-1) (rows k hk cap) small (by omega)
#print axioms no_square_core
end OMA.SquareIntervals245212
"""]
    put(src/(ROOT+".lean"),"\n".join(lines))


if __name__=="__main__":
    parser=ArgumentParser(description=__doc__)
    parser.add_argument("--build",type=Path,required=True)
    parser.add_argument("--jobs",type=int,default=6)
    args=parser.parse_args()
    if args.jobs<1:
        parser.error("--jobs must be positive")
    for mod,oid in [("R_OeisA245212_conjecture_R1","33430e5fd39d003b3327516e7828ce72b9db31c3"),
                    ("R_OeisA245212_conjecture_R1_H2_R1","ac5e41eaf91913de35ae980033d4c3b44edbee8e")]:
        if subprocess.check_output(["git","hash-object",f"OMAReductions/{mod}.lean"],text=True).strip()!=oid:
            raise SystemExit("Unexpected merged OMA source: "+mod)
    build=args.build.resolve()
    src=build/"src"
    src.mkdir(parents=True,exist_ok=True)
    generate(src)
    replay(src,build/"objects",args.jobs,ROOT,THEOREM)
