"""Search all semiprimes and bounded-smallest-factor triples in the HHO table.

Build: c++ -std=c++17 -O3 irregular_product_join.cpp -o /path/to/irregular_product_join
Run: python3 hho_product_join.py BINARY --archive twobillion.tar.bz2 --smallest 257 --cases 15
Control: replace --archive with --control To163.gz to compare a complete
smaller range to the independent Python implementation (and known hits).
"""
from argparse import ArgumentParser
from contextlib import closing
import gzip
import hashlib
from pathlib import Path
import subprocess
import tarfile
from tempfile import TemporaryFile
from cofactor_indices_mestrovic import DIGEST
from three_factor_power_search import probe


def search(binary, small, cases, chunks, first=1):
    with TemporaryFile(mode="w+b") as results:
        with subprocess.Popen([str(binary.resolve()),str(small),*map(str,cases),"--from",str(first)],
                              stdin=subprocess.PIPE,stdout=results) as child:
            with closing(child.stdin):
                for chunk in chunks:
                    child.stdin.write(chunk)
            if child.wait():
                raise ValueError("the compiled index search did not finish")
        results.seek(0)
        return {tuple(map(int,line.split())) for line in results}


def primary(path):
    checksum = hashlib.md5(usedforsecurity=False)
    with tarfile.open(path,mode="r|bz2") as archive:
        for entry in archive:
            if entry.name=="twobillion/indices.txt" and entry.isfile():
                with archive.extractfile(entry) as rows:
                    while chunk:=rows.read(1<<20):
                        checksum.update(chunk)
                        yield chunk
                if checksum.hexdigest()!=DIGEST:
                    raise ValueError("uncompressed indices do not match the authors' digest")
                return
    raise ValueError("the archive did not contain twobillion/indices.txt")


def control(path, limit):
    with gzip.open(path,"rb") as rows:
        for line in rows:
            items = line.partition(b";")[0].split()
            if int(items[0])>limit:
                return
            yield b" ".join(item.partition(b":")[0] for item in items)+b"\n"


if __name__=="__main__":
    parser=ArgumentParser(description=__doc__)
    parser.add_argument("binary",type=Path)
    inputs=parser.add_mutually_exclusive_group(required=True)
    inputs.add_argument("--archive",type=Path)
    inputs.add_argument("--control",type=Path)
    parser.add_argument("--smallest",type=int,default=257)
    parser.add_argument("--from-smallest",type=int,default=1,
                        help="skip least prime factors below this value; 1 includes semiprimes")
    parser.add_argument("--cases",type=int,nargs="+",choices=[12,15,16],default=[12,15])
    parser.add_argument("--control-limit",type=int,default=1700000)
    args=parser.parse_args()
    if args.control:
        actual=search(args.binary,args.smallest,args.cases,control(args.control,args.control_limit),args.from_smallest)
        expected={(c,p,q,r) for c,_,p,q,r in probe(args.control,args.control_limit,args.smallest,args.cases)
                  if p>=args.from_smallest}
        if actual!=expected:
            raise ValueError(f"join disagrees with Python: {actual ^ expected}")
        print(f"Control agreed on {len(actual)} candidates",flush=True)
    else:
        actual=search(args.binary,args.smallest,args.cases,primary(args.archive),args.from_smallest)
        print("Full uncompressed HHO digest verified:",DIGEST,flush=True)
    for c,p,q,r in sorted(actual):
        print(c,p*q*r,p,q,r,flush=True)
