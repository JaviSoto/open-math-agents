"""Rebuild the stand-alone effective two-extension theorem from research sources.

Run python3 two_free_effective_source_245212.py in the mathematical workspace.
Only the resulting .lean file and the pinned Formal Conjectures library are
needed for the independent from-source replay.
"""
from pathlib import Path
import re
from odd_box_source_245212 import replay_dependencies
from standalone_odd_support_245212 import assemble


def read(name):
    return Path(name+".lean").read_text()


def main():
    sources={"LargeExact245212":replay_dependencies()["LargeExact245212"]}
    faces=read("OddFaces245212")
    sources["OddFaces245212"]=("import Smooth245212\nnamespace OMA.OddFaces245212\nopen OMA.Smooth245212\n"
        +next(l for l in faces.splitlines() if l.startswith("def limitX "))+"\nend OMA.OddFaces245212\n")
    dyadic=read("DyadicEuler245212").split("/-- The first two positive")[0]
    sources["DyadicEuler245212"]=(dyadic.replace("import MovingMain245212\n","").replace("import SmoothMixed245212\n","")
        +"\nend OMA.DyadicEuler245212\n")
    sep=read("RankThreeFourSmallSeparation245212").split("theorem small {")[0]
    sources["RankThreeFourSmallSeparation245212"]=(sep.replace("import RankThreeFourSmallDegree245212","import CofactorPairPole245212")
        +"end OMA.RankThreeFourSmallSeparation245212\n")
    sources["RankThreeFourSmallBounds245212"]=read("RankThreeFourSmallBounds245212").replace(
        "import CofactorEulerDecision245212","import CofactorEulerBounds245212")
    data=assemble("TwoFreeEffectiveUniform245212","OEIS A245212: an explicit height for any fixed cofactor extended by two free odd prime powers.",sources=sources)
    data=re.sub(r"^import Mathlib.*\n|^#print axioms .+\n","",data,flags=re.M)
    data+="\n#print axioms OMA.TwoFreeEffective245212.original\n#print axioms OMA.TwoFreeEffectiveUniform245212.original\n#print axioms OMA.TwoFreeEffectiveUniform245212.of_rank\n#print axioms OMA.TwoFreeEffectiveUniform245212.monotone\n"
    Path("TwoFreeEffectiveResearch245212.lean").write_text(data)


if __name__=="__main__":
    main()
