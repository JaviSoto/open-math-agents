"""Independent C1a certificate: modular transforms and Chinese remaindering.

No carry-free polynomial packing is used. Requires NumPy; reads the same
nonnegative-integer gzip text as the standard-library checker.
"""
import gzip
import sys
from fractions import Fraction

import numpy as np


def transform(values, p, primitive, inverse):
    n = len(values)
    if (p-1) % n:
        raise ValueError("length unsupported for this prime")
    rev = np.arange(n, dtype=np.int64)
    index = np.zeros(n, dtype=np.int64)
    for _ in range(n.bit_length()-1):
        index = (index << 1) | (rev & 1)
        rev >>= 1
    out = values[index].copy()
    k = 2
    while k <= n:
        root = pow(primitive,(p-1)//k,p)
        if inverse:
            root = pow(root,-1,p)
        twiddle = np.empty(k//2, dtype=np.int64)
        twiddle[0] = 1
        for i in range(1,len(twiddle)):
            twiddle[i] = int(twiddle[i-1])*root % p
        pairs = out.reshape(-1,k)
        a = pairs[:,:k//2].copy()
        b = pairs[:,k//2:]*twiddle % p
        pairs[:,:k//2] = (a+b)%p
        pairs[:,k//2:] = (a-b)%p
        k *= 2
    if inverse:
        out = out*pow(n,-1,p) % p
    return out


def exact_score(a):
    if not a or min(a)<0 or not max(a):
        raise ValueError("expected a nonzero nonnegative sequence")
    n = len(a)
    m = 1 << (2*n-2).bit_length()
    upper = n*max(a)**2
    product = 1
    coeff = [0]*(2*n-1)
    for p, g in [(998244353,3),(469762049,3),(167772161,3),(754974721,11),(1004535809,3),
                 (2013265921,31),(1811939329,13),(2113929217,5),(1224736769,3),(1107296257,10)]:
        if (p-1)%m:
            continue
        root=pow(g,(p-1)//m,p)
        assert pow(root,m,p)==1 and (m==1 or pow(root,m//2,p)!=1)
        raw = np.zeros(m,dtype=np.int64)
        raw[:n] = [h % p for h in a]
        ft = transform(raw,p,g,False)
        r = transform(ft*ft%p,p,g,True)
        # Lift each coefficient using its new residue modulo p.
        inv = pow(product, -1, p)
        coeff = [v+product*((int(s)-v)*inv % p) for v,s in zip(coeff,r)]
        product *= p
        if product > upper:
            break
    if product <= upper:
        raise ArithmeticError("not enough primes for this witness")
    assert max(coeff)<=upper and sum(coeff)==sum(a)**2
    k = max(range(len(coeff)), key=coeff.__getitem__)
    return k, Fraction(2*n*coeff[k],sum(a)**2)


if __name__ == "__main__":
    with gzip.open(sys.argv[1],"rt",encoding="ascii") as f:
        a = [int(s) for s in f]
    print(exact_score(a))
