"""Reproduce the A245212 two-odd-prime theorem using Lean's kernel.

From the pinned formal-conjectures checkout, run:
  lake env python3 /path/to/rank_two_all_245212.py --workers 4

This compiles every research dependency from source, generates both prime
orders for each length 6–32, then checks the full iff statement. Generated
files go into a temporary directory. For an existing complete set of
compiled research modules, --check-join DIR verifies only the final join.
Use --pack FILE.tar.gz to export all source files needed by the default run.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import gzip
import hashlib
from io import BytesIO
import os
from pathlib import Path
import re
from shutil import copyfile
import tarfile
from tempfile import TemporaryDirectory
from types import SimpleNamespace

from rank_two_numeric_245212 import compile_at, verify


HERE = Path(__file__).resolve().parent
FINAL = "RankTwoAll245212"
JOIN = "RankTwoJoined245212"
EXPORT = "RankTwoExport245212"
PIN = "9097e2f90e66d2f6244209cb1c07f7120d17ec53"
AUDIT = "'OMA.RankTwoAll245212.iff_power' depends on axioms: [propext, Classical.choice, Quot.sound]"
CELL = re.compile(r"RankTwoCell(?:[6-9]|[12][0-9]|3[0-2])")
IMPORT = re.compile(r"^import ([^\n]+)$", re.M)


def modules():
    """Local Lean modules, in dependency order; high-cell sources are generated."""
    ordered = {}

    def visit(name):
        if name in ordered or CELL.fullmatch(name):
            return
        if name.startswith(("Mathlib", "FormalConjectures")):
            return
        path = HERE / (name + ".lean")
        for line in IMPORT.findall(path.read_text()):
            for dependency in line.split():
                visit(dependency)
        ordered[name] = path

    visit(FINAL)
    visit(EXPORT)
    return ordered


def pack(target):
    """Stable source-only archive with no platform-specific compiled files."""
    files = {p.name: p.read_bytes() for p in modules().values()}
    for name in ("rank_two_all_245212.py", "rank_two_numeric_245212.py"):
        files[name] = (HERE/name).read_bytes()
    files["README.txt"] = (
        "OEIS A245212: for n>0 with at most two distinct odd prime factors, "
        "a(n)=sigma(n) if and only if n is a power of two.\n\n"
        f"Pin: google-deepmind/formal-conjectures, {PIN}.\n"
        "Extract this archive, then from the pinned Lake environment run:\n"
        "  lake env python3 /absolute/path/to/rank_two_all_245212.py --workers 4\n"
        "Use --workers 1 if RAM is limited. The output ends with the axiom audit "
        "of OMA.RankTwoAll245212.iff_power. No prebuilt research files are used.\n"
    ).encode()
    with target.open("wb") as dest, gzip.GzipFile(fileobj=dest, mode="wb", filename="", mtime=0) as gz:
        with tarfile.open(fileobj=gz, mode="w") as archive:
            for name, data in sorted(files.items()):
                entry = tarfile.TarInfo("rank-two-245212/" + name)
                entry.size = len(data)
                archive.addfile(entry, BytesIO(data))
    print(f"{target}: {len(files)} files, {target.stat().st_size} bytes, "
          f"SHA-256 {hashlib.sha256(target.read_bytes()).hexdigest()}")


def compile_module(name, dest, env, audit=None):
    path = dest / (name+".lean")
    copyfile(HERE/path.name, path)
    result = compile_at(path, dest, env)
    text = result.stdout + result.stderr
    if result.returncode or (audit and audit not in text.splitlines()):
        raise RuntimeError(f"{name} failed ({result.returncode}):\n{text[-3500:]}")
    print(audit or f"Checked {name}.", flush=True)


def run(dest, workers, cached):
    paths = [str(dest)]
    if cached:
        paths.append(str(cached.resolve(strict=True)))
    paths.append(os.environ["LEAN_PATH"])
    env = dict(os.environ, LEAN_PATH=os.pathsep.join(paths))
    if not cached:
        for module in modules():
            if module not in (JOIN, FINAL, EXPORT):
                compile_module(module,dest,env)
        # The same deterministic generator/checker used in the high-length
        # theorem. One verification covers normal and reversed prime order.
        options = SimpleNamespace(portable=True, nodes=19, positions=400)
        with ThreadPoolExecutor(max_workers=workers) as pool:
            futures = [pool.submit(verify, m, options, dest, env) for m in range(6,33)]
            for future in futures:
                future.result()
        compile_module(JOIN,dest,env)
    compile_module(FINAL,dest,env,AUDIT)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workers", type=int, choices=range(1,13), default=4,
                        help="number of simultaneous high-length checks (default: 4)")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--pack",type=Path,metavar="FILE.tar.gz")
    mode.add_argument("--check-join",type=Path,metavar="DIR",
                      help="use already compiled dependencies in this directory")
    args = parser.parse_args()
    if args.pack:
        pack(args.pack)
    else:
        with TemporaryDirectory(prefix="a245212-complete-") as directory:
            run(Path(directory).resolve(),args.workers,args.check_join)


if __name__ == "__main__":
    main()
