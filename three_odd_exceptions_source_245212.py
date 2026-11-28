"""Prepare the rank-three proof for import alongside the earlier rank-two proof.

The two self-contained research packets embed some of the same helper names.
Give the rank-three helpers a separate Lean namespace, retaining its four public
theorems and cutoff. This changes names only; Lean checks the entire result.

For a fresh end-to-end replay, extract rank-two-complete-proof-245212.tar.gz.
From the pinned Lake checkout run:
  lake env python3 /path/three_odd_exceptions_source_245212.py --rank-two /path/rank-two-245212
Use --workers 1 if memory is limited. To recheck the joins with existing
rank-two modules in DIR, add --check-join DIR. With no arguments the script
only emits the rank-three source with nonoverlapping names.
"""
import argparse
import os
from pathlib import Path
import sys
from tempfile import TemporaryDirectory


def bundle():
    here = Path(__file__).resolve().parent
    source = (here / "ThreeOddAbsoluteResearch245212.lean").read_text()
    return source.replace("OMA.", "OMA.ThreeOddBundle.").replace(
        "OMA.ThreeOddBundle.ThreeOddAbsolute245212", "OMA.ThreeOddAbsolute245212")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rank-two", type=Path)
    parser.add_argument("--check-join", type=Path)
    parser.add_argument("--workers", type=int, choices=range(1, 13), default=4)
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    if args.rank_two is None:
        if args.check_join is not None:
            parser.error("--check-join requires --rank-two")
        (here / "ThreeOddRankBundle245212.lean").write_text(bundle())
        return

    sys.path.insert(0, str(args.rank_two.resolve(strict=True)))
    from rank_two_all_245212 import run
    from rank_two_numeric_245212 import compile_at

    with TemporaryDirectory(prefix="a245212-three-exceptions-") as temp:
        output = Path(temp).resolve()
        run(output, args.workers, args.check_join)
        paths = [str(output)]
        if args.check_join is not None:
            paths.append(str(args.check_join.resolve(strict=True)))
        paths.append(os.environ["LEAN_PATH"])
        env = dict(os.environ, LEAN_PATH=os.pathsep.join(paths))
        (output / "ThreeOddRankBundle245212.lean").write_text(bundle())
        final = (here / "ThreeOddExceptions245212.lean").read_text()
        audits = [f"OMA.ThreeOddExceptions245212.{n}" for n in ("bounded", "finite", "eventually_iff")]
        (output / "ThreeOddExceptions245212.lean").write_text(
            final + "".join(f"\n#print axioms {name}\n" for name in audits))
        for module in ("ThreeOddRankBundle245212", "ThreeOddExceptions245212"):
            result = compile_at(output / (module + ".lean"), output, env)
            if result.returncode:
                raise RuntimeError(result.stdout + result.stderr)
        for name in audits:
            required = f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]"
            if required not in result.stdout.splitlines():
                raise RuntimeError("Missing axiom audit: " + required)
            print(required)


if __name__ == "__main__":
    main()
