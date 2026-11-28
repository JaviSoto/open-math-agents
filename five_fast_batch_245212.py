"""Generate and check two-free-prime exclusions for n=2^k 5^a p^b q^c.

From the pinned Formal Conjectures checkout use
  lake env python3 PATH/five_fast_batch_245212.py 5 1 4 /private/tmp --jobs 4
The scratch location must already contain the checked task Lean dependencies.
Near intervals are independent; the original arithmetic proof covers the
infinite far interval. Use lean_source_bundle_245212.py for a cold replay.
"""
from argparse import ArgumentParser
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import os
from pathlib import Path
import re
import subprocess
import time

from rank_three_five_far_245212 import generate
from rank_three_five_rows_245212 import bounds
from rank_three_middle_blocks_245212 import joins


def sources(k, a, span, checked_far=None):
    h, weight, sigma, mass, _ = bounds(k, a)
    cutoff = max(129, 8*mass//(2*mass-weight)+1)
    max_factor = max(5, k+1, a+1)
    stem = f"FiveQuick{k}x{a}"
    namespace = f"OMA.{stem}"
    base_header = (
        "import FiveFastNear245212\n"
        f"namespace {namespace}\n"
        "open OMA.CofactorEulerPair245212 OMA.FiveFastNear245212\n"
        "open OMA.RankThreeFiveTail245212 (cofactor wt sg ta)\n"
        "open OMA.RankThreeMiddle245212 (joinEvery)\n"
        "set_option maxRecDepth 65536\nset_option maxHeartbeats 0\n"
    )
    data = {}
    blocks = []
    for lo in range(7, cutoff, span):
        hi = min(lo+span-1, cutoff-1)
        name = stem+f"S{lo}"
        blocks.append(name)
        predicate = f"(fast {h} {weight} {sigma} {mass} {max_factor})"
        body = (f"theorem span{lo} : every {lo} {hi} "
                f"(OMA.RankThreeFiveShort245212.test {k} {a})=true :=\n"
                f"  interval (m:={max_factor}) (by decide +kernel) "
                f"(show every {lo} {hi} {predicate}=true by decide +kernel)\n")
        data[name] = ([], base_header+body+f"end {namespace}\n")
    far = checked_far or stem+"Far"
    if not checked_far:
        data[far] = ([], generate(k, a, cutoff, chunk=128))
    theorem = (f"theorem original {{p q b c : ℕ}} (pp : p.Prime) (qp : q.Prime) "
               "(gt : 5<p) (pq : p<q) (bp : 0<b) (cp : 0<c) :\n"
               f"    OeisA245212.a (2^{k}*5^{a}*p^b*q^c)≠"
               f"(ArithmeticFunction.sigma 1 (2^{k}*5^{a}*p^b*q^c):ℤ) :=\n"
               f"  OMA.RankThreeFiveShort245212.final (lo:={cutoff}) pp qp gt pq bp cp "
               f"{joins([f'span{lo}' for lo in range(7,cutoff,span)])} "
               f"(by decide +kernel) OMA.FiveFar{k}x{a}.scan\n")
    deps = blocks+[far]
    data[stem] = ([n for n in deps if n in data], "".join(f"import {n}\n" for n in deps)+base_header+
                  theorem+f"#print axioms original\nend {namespace}\n")
    return data


def verify(graph, output, jobs, seconds):
    env = dict(os.environ, LEAN_PATH=str(output)+os.pathsep+os.environ["LEAN_PATH"])
    def check(name):
        start = time.monotonic()
        cmd = ["lean", "-j", "1", "-DElab.async=false", "-R", str(output),
               "-o", str(output/(name+".olean")), str(output/(name+".lean"))]
        try:
            result = subprocess.run(cmd, env=env, capture_output=True, text=True, timeout=seconds)
        except subprocess.TimeoutExpired:
            return False, f"exceeded {seconds}s"
        log = result.stdout+result.stderr
        ok = result.returncode == 0 and "sorryAx" not in log
        return ok, f"{time.monotonic()-start:.1f}s" if ok else log[-1400:]

    pending = dict(graph)
    finished, failed, running = set(), set(), {}
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        while pending or running:
            for name, (deps, _) in list(pending.items()):
                if failed.intersection(deps):
                    failed.add(name)
                    del pending[name]
                elif len(running)<jobs and all(dep in finished for dep in deps):
                    running[pool.submit(check, name)] = name
                    del pending[name]
            if not running:
                if pending:
                    raise RuntimeError(f"Unresolved dependencies: {list(pending)}")
                break
            done, _ = wait(running, return_when=FIRST_COMPLETED)
            for future in done:
                name = running.pop(future)
                ok, detail = future.result()
                (finished if ok else failed).add(name)
                print(f"{'checked' if ok else 'failed'} {name}: {detail}", flush=True)
    return not failed


if __name__ == "__main__":
    cli = ArgumentParser(description=__doc__)
    cli.add_argument("k", type=int)
    cli.add_argument("start", type=int)
    cli.add_argument("last", type=int)
    cli.add_argument("output", type=Path)
    cli.add_argument("--span", type=int, default=32)
    cli.add_argument("--jobs", type=int, choices=range(1, 13), default=4)
    cli.add_argument("--timeout", type=int, default=240)
    cli.add_argument("--checked-far", help="Import this existing far certificate for a single exponent; Lean checks its exact type.")
    args = cli.parse_args()
    if args.start<1 or args.last<args.start or args.span<1 or args.timeout<1:
        cli.error("Use a positive ordered exponent range, span and timeout.")
    out = args.output.resolve()
    if not (out/"FiveFastNear245212.olean").is_file():
        cli.error("Compile FiveFastNear245212 and its dependencies into the output directory first.")
    if args.checked_far and (args.start!=args.last or not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*",args.checked_far)
        or not all((out/(args.checked_far+suffix)).is_file() for suffix in (".lean",".olean"))):
        cli.error("--checked-far needs one input exponent and an existing source and object.")
    modules = {}
    for a in range(args.start, args.last+1):
        modules.update(sources(args.k, a, args.span, args.checked_far))
    for module, (_, source) in modules.items():
        (out/(module+".lean")).write_text(source)
    raise SystemExit(not verify(modules, out, args.jobs, args.timeout))
