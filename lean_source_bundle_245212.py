"""Pack and replay a multi-file Lean proof in the pinned Formal Conjectures checkout.

Pack: python3 lean_source_bundle_245212.py --pack proof.tar.gz --root Module
      --theorem OMA.Namespace.theorem --sources WORKSPACE GENERATED
Replay: extract the archive, then run lake env python3 /path/to/lean_source_bundle_245212.py --workers 4
The replay builds only from the bundled sources. Every file hash is checked,
and success requires the named final theorem's exact standard axiom report.
"""
import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import gzip
import hashlib
from io import BytesIO
import json
import os
from pathlib import Path
import re
import subprocess
import tarfile
from tempfile import TemporaryDirectory
import time

HERE = Path(__file__).resolve().parent
PIN = '9097e2f90e66d2f6244209cb1c07f7120d17ec53'
MANIFEST = 'lean-proof-manifest.json'


def imports(content):
    names = [m for line in re.findall(r'^import (.+)$',content.decode(),re.M) for m in line.split()]
    return {m for m in names if m.split('.')[0] not in {'FormalConjectures','Mathlib','Lean','Std','Init'}}


def digest(content):
    return hashlib.sha256(content).hexdigest()


def pack(target, root, theorem, directories):
    files = {}
    def collect(module):
        if module in files:
            return
        if not re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*',module):
            raise ValueError(f'unsupported local module: {module}')
        name = module+'.lean'
        path = next((d/name for d in directories if (d/name).is_file()),None)
        if path is None:
            raise FileNotFoundError(name)
        files[module] = path.read_bytes()
        for dep in sorted(imports(files[module])):
            collect(dep)
    collect(root)
    manifest = dict(root=root,theorem=theorem,pin=PIN,modules={k:digest(v) for k,v in sorted(files.items())})
    payload = {k+'.lean':v for k,v in files.items()}
    payload[MANIFEST] = json.dumps(manifest,sort_keys=True,indent=2).encode()+b'\n'
    payload[Path(__file__).name] = Path(__file__).read_bytes()
    payload['README.txt'] = (
        f'Kernel proof: {theorem}\n\nFrom the compiled google-deepmind/formal-conjectures checkout at {PIN}, run:\n'
        f'  lake env python3 /absolute/path/to/{Path(__file__).name} --workers 4\n'
        'One worker per file. Use --workers 1 on a smaller machine. No prebuilt research modules are required.\n'
    ).encode()
    with target.open('wb') as raw, gzip.GzipFile(filename='',fileobj=raw,mode='wb',mtime=0) as compressed:
        with tarfile.open(mode='w',fileobj=compressed) as archive:
            for name, content in sorted(payload.items()):
                item = tarfile.TarInfo(root+'/'+name)
                item.mode, item.size = 0o644,len(content)
                archive.addfile(item,BytesIO(content))
    print(f'{len(files)} Lean sources, {target.stat().st_size} bytes, SHA-256 {digest(target.read_bytes())}')


def replay(workers):
    manifest = json.loads((HERE/MANIFEST).read_bytes())
    pin = subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
    if pin != manifest['pin']:
        raise ValueError(f"run from the pinned formal-conjectures checkout: {manifest['pin']}")
    expected = f"'{manifest['theorem']}' depends on axioms: [propext, Classical.choice, Quot.sound]"
    with TemporaryDirectory(prefix='a245212-lean-') as directory:
        dest = Path(directory).resolve()
        env = dict(os.environ,LEAN_PATH=str(dest)+os.pathsep+os.environ['LEAN_PATH'])
        graph = {}
        for module, sha in manifest['modules'].items():
            name = module+'.lean'
            data = (HERE/name).read_bytes()
            if digest(data)!=sha:
                raise ValueError(f'source digest mismatch: {name}')
            (dest/name).write_bytes(data)
            graph[module] = imports(data)
        def compile_one(module):
            start = time.monotonic()
            result = subprocess.run(['lean','-j','1','-DElab.async=false','-R',str(dest),
                    '-o',str(dest/(module+'.olean')),str(dest/(module+'.lean'))],
                    env=env,capture_output=True,text=True)
            log = result.stdout+result.stderr
            if result.returncode or 'sorryAx' in log or (module==manifest['root'] and expected not in log.splitlines()):
                raise RuntimeError(f'{module}:\n{log[-2500:]}')
            return time.monotonic()-start
        checked = set()
        running = {}
        total = len(graph)
        with ThreadPoolExecutor(max_workers=workers) as pool:
            while graph or running:
                ready = sorted(m for m,deps in graph.items() if deps<=checked)
                for module in ready[:workers-len(running)]:
                    running[pool.submit(compile_one,module)] = module
                    del graph[module]
                if not running:
                    raise ValueError(f'missing or circular dependencies: {graph}')
                done,_ = wait(running,return_when=FIRST_COMPLETED)
                for future in done:
                    module = running.pop(future)
                    elapsed = future.result()
                    checked.add(module)
                    if elapsed>=60 or len(checked)%20==0 or module==manifest['root']:
                        print(f'{len(checked)}/{total} checked: {module} ({elapsed:.1f}s)',flush=True)
        print(expected)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--workers',type=int,choices=range(1,17),default=4)
    parser.add_argument('--pack',type=Path)
    parser.add_argument('--root')
    parser.add_argument('--theorem')
    parser.add_argument('--sources',type=Path,nargs='+')
    args = parser.parse_args()
    if args.pack:
        if not args.root or not args.theorem or not args.sources:
            parser.error('--pack needs --root, --theorem and --sources')
        pack(args.pack,args.root,args.theorem,args.sources)
    else:
        replay(args.workers)


if __name__=='__main__':
    main()
