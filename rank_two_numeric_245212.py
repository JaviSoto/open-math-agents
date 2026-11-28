"""Generate and kernel-check the two ordered finite boxes for each given length.

Run from the pinned Lake environment: lake env python3 SCRIPT 22-32 --workers 5.
Use --portable 6-32 for the whole theorem from the published source files,
without prebuilt research modules. Each requested length must pass.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
from tempfile import TemporaryDirectory
import time

HERE = Path(__file__).resolve().parent
ARTIFACTS = Path('/private/tmp')
AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def integers(spec):
    result = set()
    for item in spec.split(','):
        match = re.fullmatch(r'(\d+)(?:-(\d+))?', item)
        if not match:
            raise ValueError('use comma-separated lengths or ranges')
        start = int(match[1])
        stop = int(match[2] or start)
        if not 6 <= start <= stop <= 32:
            raise ValueError('expected a length between 6 and 32')
        result.update(range(start, stop + 1))
    return sorted(result)


def compile_at(source, artifacts, env):
    return subprocess.run(['lean','-j','1','-DElab.async=false','-R',str(artifacts),
                           '-o',str(source.with_suffix('.olean')),str(source)],
                          env=env,capture_output=True,text=True)


def verify(length, opts, artifacts, env):
    module = f'RankTwoCell{length}'
    source = artifacts / (module + '.lean')
    log = artifacts / (module + '-kernel.log')
    start = time.monotonic()
    gen = subprocess.run(['lean', '--run', str(HERE/'RankTwoExport245212.lean'),
                          str(source), module, str(length), '6', '1250',
                          str(opts.nodes), str(opts.positions)], env=env, capture_output=True, text=True)
    if gen.returncode:
        raise RuntimeError(f'{module}: generator: {gen.stdout[-1000:]} {gen.stderr[-500:]}')
    if opts.portable:
        result = compile_at(source,artifacts,env)
        output = result.stdout + result.stderr
    else:
        with log.open('w') as out:
            result = subprocess.run([sys.executable, str(HERE/'profile_box_lean_245212.py'), str(source),
                                     '--jobs', '1', '--max-mib', str(opts.memory)], stdout=out, stderr=subprocess.STDOUT)
        output = log.read_text()
    reports = dict(re.findall(r"'OMA\.\w+\.(normal|reverse)' depends on axioms: \[([^\]]+)\]", output))
    if result.returncode or set(reports) != {'normal','reverse'} or any(
            set(axioms.split(', ')) != AXIOMS for axioms in reports.values()):
        raise RuntimeError(f'{module} failed ({result.returncode}): {output[-1200:]}')
    row = dict(length=length, source=source.name, sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
               bytes=source.stat().st_size, elapsed=round(time.monotonic()-start,2),
               costs=gen.stdout.strip(), kernel=output.splitlines()[-1])
    print(json.dumps(row), flush=True)
    return row


def replay(args, artifacts):
    env = dict(os.environ, LEAN_PATH=str(artifacts) + os.pathsep + os.environ['LEAN_PATH'])
    if args.portable:
        base = artifacts/'RankTwoInteriorCover245212.lean'
        shutil.copyfile(HERE/'RankTwoOriginalCoverResearch245212.lean',base)
        result = compile_at(base,artifacts,env)
        if result.returncode or 'sorryAx' in result.stdout:
            sys.exit('Analytic proof failed: '+(result.stdout+result.stderr)[-1800:])
        print('Analytic reduction checked.',flush=True)
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        futures = [pool.submit(verify, m, args, artifacts, env) for m in args.lengths]
        failures = []
        for future in futures:
            try:
                future.result()
            except (OSError, RuntimeError) as err:
                failures.append(str(err))
    if failures:
        sys.exit('\n'.join(failures))
    if args.portable and args.lengths == list(range(6,33)):
        join = artifacts/'RankTwoJoined245212.lean'
        # The self-contained analytic source contains both the cover and the
        # original-statement theorem under their original namespaces.
        source = (HERE/join.name).read_text()
        join.write_text(source.replace('import RankTwoOriginalCover245212\n',
                                       'import RankTwoInteriorCover245212\n',1))
        result = compile_at(join,artifacts,env)
        expected = "'OMA.RankTwoJoined245212.original' depends on axioms: [propext, Classical.choice, Quot.sound]"
        if result.returncode or expected not in result.stdout.splitlines():
            sys.exit('Final theorem failed: '+(result.stdout+result.stderr)[-1800:])
        print(expected,flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('lengths', type=integers)
    parser.add_argument('--workers', type=int, choices=range(1,13), default=5)
    parser.add_argument('--portable', action='store_true', help='build from the standalone analytic source in a temporary directory')
    parser.add_argument('--memory', type=int, default=4000, help='local macOS profiler ceiling (MiB); portable checks use one Lean thread per file')
    parser.add_argument('--nodes', type=int, default=19)
    parser.add_argument('--positions', type=int, default=400)
    args = parser.parse_args()
    if args.portable:
        with TemporaryDirectory(prefix='a245212-rank-two-') as directory:
            replay(args,Path(directory).resolve())
    else:
        replay(args,ARTIFACTS)


if __name__ == '__main__':
    main()
