"""Check prime supports (3,5,7,q,r) for A245212, with resumable exact results.

Usage: python3 five_square_sweep_245212.py --q 11 11 --r 1000 3000 --state results.sqlite3
Both intervals are inclusive. See five-square-sweep-245212.md for the scope.
"""
import argparse
import ast
from concurrent.futures import FIRST_COMPLETED, ProcessPoolExecutor, wait
import hashlib
import json
import math
import multiprocessing
import os
from pathlib import Path
import sqlite3
import subprocess
import sys
from time import monotonic, process_time

from five_square_boxes_245212 import count_support
from odd_four_245212 import prime


def proof_digest():
    """Hash this driver and the entire local proof-module import closure."""
    folder = Path(__file__).resolve().parent
    pending = [Path(__file__).stem]
    sources = {}
    while pending:
        name = pending.pop()
        if name in sources:
            continue
        source = (folder / (name + ".py")).read_bytes()
        sources[name] = source
        for node in ast.walk(ast.parse(source)):
            if isinstance(node, ast.ImportFrom):
                names = [node.module or ""]
            elif isinstance(node, ast.Import):
                names = [alias.name for alias in node.names]
            else:
                continue
            pending.extend(n for n in names if n.endswith("_245212"))
    digest = hashlib.sha256()
    for name, source in sorted(sources.items()):
        digest.update(name.encode() + b"\0" + source + b"\0")
    return digest.hexdigest()


def check_environment(expected):
    if not __debug__:
        raise RuntimeError("use Python without -O; the arithmetic checker uses assertions")
    if proof_digest() != expected:
        raise RuntimeError("proof source changed after the run began; restart to use its new fingerprint")


def available_memory():
    """Best-effort available bytes; omit this bound when host data is unavailable."""
    try:
        meminfo = Path("/proc/meminfo")
        if meminfo.is_file():
            for line in meminfo.read_text().splitlines():
                if line.startswith("MemAvailable:"):
                    return int(line.split()[1]) * 1024
        if sys.platform == "darwin":
            stat = subprocess.run(["/usr/bin/vm_stat"], capture_output=True, text=True,
                                  timeout=2, check=True).stdout.splitlines()
            page_size = int(stat[0].split("page size of ")[1].split()[0])
            pages = {k: int(v.strip().rstrip(".")) for k, v in
                     (line.split(":", 1) for line in stat[1:] if ":" in line)}
            return page_size * sum(pages.get(k, 0) for k in
                                   ("Pages free", "Pages inactive", "Pages speculative"))
    except (OSError, subprocess.SubprocessError, ValueError, IndexError):
        return None
    return None


def default_jobs():
    cpu_count = getattr(os, "process_cpu_count", os.cpu_count)() or 1
    # Leave two cores beyond the existing one-minute load; avoid starting
    # large ranks of processes when this machine is already running Lean.
    spare = cpu_count - math.ceil(os.getloadavg()[0]) - 2
    memory = available_memory()
    slots = 8 if memory is None else (memory - 2 * 2**30) // (512 * 2**20)
    return max(1, min(8, spare, slots))


def check_one(support):
    q, r = support
    start, cpu = monotonic(), process_time()
    try:
        counts = count_support(q, r)
    except Exception as exc:
        raise RuntimeError(f"q={q}, r={r}: {exc}") from exc
    return q, r, *counts, monotonic() - start, process_time() - cpu


def checked_rows(pending, jobs, fingerprint):
    if jobs == 1:
        yield from map(check_one, pending)
        return
    pool = ProcessPoolExecutor(jobs, mp_context=multiprocessing.get_context("spawn"),
                               initializer=check_environment, initargs=(fingerprint,))
    work = iter(pending)
    running = set()
    try:
        def enqueue():
            support = next(work, None)
            if support is not None:
                running.add(pool.submit(check_one, support))

        for _ in range(jobs):
            enqueue()
        while running:
            finished, running = wait(running, return_when=FIRST_COMPLETED)
            for task in finished:
                yield task.result()
                enqueue()
    finally:
        # Only the parent commits completed rows. A failed/unfinished support
        # stays unverified, including when a worker dies or the user interrupts.
        for task in running:
            task.cancel()
        if running and hasattr(pool, "terminate_workers"):
            pool.terminate_workers()
        else:
            pool.shutdown(wait=True, cancel_futures=True)


def sweep(db, q_range, r_range, jobs):
    started = monotonic()
    fingerprint = proof_digest()
    check_environment(fingerprint)
    qs = [q for q in range(*q_range) if q > 7 and prime(q)]
    rs = [r for r in range(*r_range) if prime(r)]
    supports = [(q, r) for q in qs for r in rs if q < r]
    if not supports:
        raise ValueError("the requested rectangle contains no primes 7 < q < r")

    db.execute("""CREATE TABLE IF NOT EXISTS verified (
        fingerprint TEXT NOT NULL, q INTEGER NOT NULL, r INTEGER NOT NULL,
        boxes INTEGER NOT NULL, prefixes INTEGER NOT NULL, two_hits INTEGER NOT NULL,
        four_hits INTEGER NOT NULL, elapsed REAL NOT NULL, cpu REAL NOT NULL,
        PRIMARY KEY (fingerprint, q, r))""")
    query = """SELECT q,r,boxes,prefixes,two_hits,four_hits,elapsed,cpu FROM verified
               WHERE fingerprint=? AND q BETWEEN ? AND ? AND r BETWEEN ? AND ?"""
    bounds = (fingerprint, q_range[0], q_range[1]-1, r_range[0], r_range[1]-1)
    known = {(row[0], row[1]): row for row in db.execute(query, bounds)}
    pending = [s for s in supports if s not in known]
    workers = min(jobs, len(pending))
    cpu_new = 0.0
    for row in checked_rows(pending, max(1, workers), fingerprint):
        key = row[:2]
        with db:
            db.execute("INSERT OR IGNORE INTO verified VALUES(?,?,?,?,?,?,?,?,?)", (fingerprint, *row))
            saved = db.execute("SELECT boxes,prefixes,two_hits,four_hits FROM verified "
                               "WHERE fingerprint=? AND q=? AND r=?", (fingerprint,*key)).fetchone()
            if saved != row[2:6]:
                raise RuntimeError(f"conflicting completed counts at {key}: {saved} vs {row[2:6]}")
        known[key] = row
        cpu_new += row[-1]

    digest = hashlib.sha256()
    totals = [0] * 4
    for support in supports:
        row = known[support]
        digest.update((" ".join(map(str, row[:6])) + "\n").encode("ascii"))
        totals = [a+b for a,b in zip(totals, row[2:6])]
    slow = max((known[s] for s in supports), key=lambda row: row[-2])
    return dict(proof_sha256=fingerprint, results_sha256=digest.hexdigest(), supports=len(supports),
                checked=len(pending), reused=len(supports)-len(pending), workers=workers,
                counts=totals, seconds=round(monotonic()-started, 3), cpu_seconds_new=round(cpu_new, 3),
                slowest=dict(q=slow[0], r=slow[1], seconds=round(slow[-2], 3)))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--q", type=int, nargs=2, default=(11,11), metavar=("LO","HI"))
    parser.add_argument("--r", type=int, nargs=2, required=True, metavar=("LO","HI"))
    parser.add_argument("--jobs", type=int, help="maximum worker processes (default: load/memory-aware, at most 8)")
    parser.add_argument("--state", required=True, help="SQLite receipt file; unchanged completed supports are reused")
    args = parser.parse_args()
    for lo, hi in (args.q, args.r):
        if not (0 <= lo <= hi < 2**63):
            parser.error("each inclusive interval must satisfy 0 ≤ LO ≤ HI < 2^63")
    jobs = default_jobs()
    if args.jobs is not None:
        if args.jobs < 1:
            parser.error("--jobs must be positive")
        jobs = args.jobs
    db = sqlite3.connect(args.state, timeout=30)
    try:
        result = sweep(db, (args.q[0],args.q[1]+1), (args.r[0],args.r[1]+1), jobs)
        print(json.dumps(result, sort_keys=True), flush=True)
    finally:
        db.close()


if __name__ == "__main__":
    main()
