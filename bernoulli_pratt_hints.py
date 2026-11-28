"""Gather proposed Lucas factorizations, checked later by the Lean kernel.

python3 bernoulli_pratt_hints.py candidate-factors.json 101 103 131 149 157
The resulting integer products are private inputs to the proof generator;
the resulting archive contains a standalone check for every Lucas witness.
"""
from argparse import ArgumentParser
import json
from math import prod
from pathlib import Path
from shutil import which
from subprocess import check_output,TimeoutExpired
from urllib.request import urlopen
from cubic_census_284759 import even_bernoulli


def split(n):
    if n.bit_length()<105:
        try:
            return list(map(int,check_output([which("gfactor") or "factor",str(n)],text=True,
                                             timeout=1).partition(":")[2].split()))
        except TimeoutExpired:
            pass
    with urlopen("https://factordb.com/api?query="+str(n),timeout=30) as res:
        record=json.load(res)
    if record["status"] not in {"FF","P","PRP"}:
        # FactorDB may know small factors but leave an unfactored cofactor.
        # Use FLINT only on those pieces; the Lean certificates remain decisive.
        from flint import fmpz
        return sorted(int(prime) for piece,multiplicity in record["factors"]
                      for prime,exponent in fmpz(piece).factor()
                      for _ in range(multiplicity*exponent))
    return sorted(int(p) for p,a in record["factors"] for _ in range(a))


def collect(primes,output):
    known=json.loads(output.read_text()) if output.is_file() else {}
    values=even_bernoulli(max(primes)-3)
    todo=[abs(values[(p-3)//2].numerator) for p in primes]
    seen=set()
    while todo:
        n=todo.pop()
        if n in seen:
            continue
        seen.add(n)
        key=str(n)
        if key not in known:
            fs=split(n)
            if not fs or min(fs)<2 or prod(fs)!=n:
                raise ValueError(f"invalid candidate product for {n}")
            known[key]=fs
            output.write_text(json.dumps(known,sort_keys=True)+"\n")
        todo.extend(p-1 for p in known[key] if p>=1000)
    print(f"{len(seen)} complete product proposals",flush=True)


if __name__=="__main__":
    parser=ArgumentParser(description=__doc__)
    parser.add_argument("output",type=Path)
    parser.add_argument("primes",type=int,nargs="+")
    args=parser.parse_args()
    collect(args.primes,args.output)
