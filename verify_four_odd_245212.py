"""Replay the A245212 four-odd-prime theorem inside the pinned Formal Conjectures Lake environment.

Extract the source ZIP, then run lake env python3 /path/to/verify.py from the Formal
Conjectures checkout. Use --jobs 1 to reduce simultaneous memory. A second run
reuses successfully built modules with unchanged transitive sources and toolchain.
"""
from argparse import ArgumentParser
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from hashlib import sha256
from pathlib import Path
import os
import re
import subprocess

PIN = "9097e2f90e66d2f6244209cb1c07f7120d17ec53"
ROOT = "OddFourComplete245212"


def replay(src, cache, jobs, root=ROOT, theorem="OMA.OddSupportClass245212.odd_four"):
    if subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip() != PIN:
        raise SystemExit("Run from Formal Conjectures at " + PIN)
    if not os.environ.get("LEAN_PATH"):
        raise SystemExit("Start through lake env python3 as described above.")
    version = subprocess.check_output(["lean", "--version"], text=True)
    sources = {path.stem: path for path in src.glob("*.lean")}
    if root not in sources:
        raise SystemExit("Missing main theorem source")
    deps = {name: set(re.findall(r"^import (.+)$", path.read_text(), re.M)) & sources.keys()
            for name, path in sources.items()}
    cache.mkdir(exist_ok=True)
    env = dict(os.environ, LEAN_PATH=str(cache) + os.pathsep + os.environ["LEAN_PATH"])
    fingerprints = {}
    done = set()

    def build(name):
        fingerprint = sha256(version.encode() + PIN.encode() + sources[name].read_bytes() +
                             "".join(fingerprints[d] for d in sorted(deps[name])).encode()).hexdigest()
        marker = cache / (name + ".sha256")
        obj = cache / (name + ".olean")
        if name != root and obj.is_file() and marker.is_file() and marker.read_text() == fingerprint:
            return fingerprint
        run = subprocess.run(["lean", "-R", str(src), "-o", str(obj), str(sources[name])],
                             env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        if run.returncode or 'sorryAx' in run.stdout:
            raise RuntimeError(name + "\n" + run.stdout)
        if name == root:
            audit = re.search(r"'" + re.escape(theorem) + r"' depends on axioms: \[(.*?)\]",
                              run.stdout, re.S)
            allowed = {"propext", "Classical.choice", "Quot.sound"}
            if not audit or set(re.split(r",\s*", audit[1])) - allowed:
                raise RuntimeError("Unexpected or absent final axiom audit: " + run.stdout)
            print(audit[0], flush=True)
        marker.write_text(fingerprint)
        return fingerprint

    todo = set(sources)
    running = {}
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        while todo or running:
            ready = sorted(name for name in todo if deps[name] <= done)
            for name in ready[:jobs - len(running)]:
                todo.remove(name)
                running[pool.submit(build, name)] = name
            if not running:
                raise RuntimeError("Unresolved module dependency: " + str(sorted(todo)))
            completed, _ = wait(running, return_when=FIRST_COMPLETED)
            for task in completed:
                name = running.pop(task)
                fingerprints[name] = task.result()
                done.add(name)
            if len(done) % 25 == 0 or not todo and not running:
                print(f"{len(done)}/{len(sources)} modules", flush=True)


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--jobs", type=int, default=2)
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be at least one")
    here = Path(__file__).resolve().parent
    replay(here / "src", here / "build", args.jobs)
