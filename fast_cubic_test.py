"""Direct cubic power sums for large witnesses (also handles repeated primes).

Build power_sum_rows.cpp using C++17 with pkg-config's gmpxx flags. Run
python3 fast_cubic_test.py BINARY 77106998694419 --workers 6
The control cases compare to the original finite sum, including prime powers.
"""
from argparse import ArgumentParser
from math import comb
from pathlib import Path
from subprocess import check_output
from mestrovic_power_witness import prime_powers


def block(binary,p,count,exponent,precision,jobs):
    modulus=p**precision
    moments,coefficients=[],[]
    for k in range(min(precision,exponent+1)):
        numerator=count**(k+1)-sum(comb(k+1,i)*v for i,v in enumerate(moments))
        value,remainder=divmod(numerator,k+1)
        assert not remainder
        moments.append(value)
        coefficients.append(comb(exponent,k)*p**k*value%modulus)
    base=exponent+1-len(coefficients)
    args=[binary,jobs,p,modulus,base,*coefficients]
    return int(check_output(list(map(str,args)),text=True))


def check(binary,n,half,jobs):
    if n<3:
        raise ValueError("n must be at least 3")
    e=(n-1)//2 if half else n-2
    return [(p,a,block(binary,p,n//p,e,3*a,jobs)) for p,a in prime_powers(n)]


if __name__=="__main__":
    parser=ArgumentParser(description=__doc__)
    parser.add_argument("binary",type=Path)
    parser.add_argument("inputs",nargs="+",type=int)
    parser.add_argument("--workers",type=int,default=4)
    parser.add_argument("--half",action="store_true")
    args=parser.parse_args()
    binary=args.binary.resolve()
    for n in [3,5,7,9,25,27,49,105,225]:
        for half in [True,False]:
            e=(n-1)//2 if half else n-2
            direct=sum(pow(i,e,n**3) for i in range(1,n))%n**3
            for p,a,r in check(binary,n,half,2):
                assert r==direct%(p**(3*a))
    for n in args.inputs:
        print(n,check(binary,n,args.half,args.workers),flush=True)
