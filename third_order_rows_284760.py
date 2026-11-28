"""Complete third-order rows for the four surviving auxiliary-data pairs.

Each result gives S_a(p) and S_(a+p(p-1))(p), reduced modulo p³, for
a=k+(p-1)(k+3).  Running this independent integer-arithmetic calculation
does not require the source Bernoulli tables. The two entries determine all
lifts modulo p³ by the binomial theorem (the increment is a multiple of p²).
"""
from concurrent.futures import ProcessPoolExecutor


def check(row):
    p, k = row
    first = delta = 0
    a = k+(p-1)*(k+3)
    p2 = p*p
    p3 = p2*p
    for i in range(1,p):
        value = pow(i,a,p3)
        first += value
        quotient = (pow(i,p-1,p2)-1)//p
        delta += (value % p)*quotient
    return p,k,a,first%p3,(first+p2*delta)%p3


def repeated_6263():
    """For p²|n, test the uniquely compatible order-three index mod φ(p³)."""
    p,k=6263,3286
    e=k+(p-1)*((k+3)*(p+1)%(p*p))
    high=sum(pow(i,e,p**4) for i in range(1,p))%p**4
    low=sum(pow(i,e-2,p*p) for i in range(1,p))%(p*p)
    corrected=(6*high-e*(e-1)*p*p*low)%p**4
    assert corrected%p**3==0
    return p,e,high,low,corrected//p**3


if __name__=="__main__":
    rows = [(6263,3286),(130811,52324),(599479,359568),(2010401,1234960)]
    with ProcessPoolExecutor(max_workers=3) as pool:
        for result in pool.map(check, rows):
            print(*result,flush=True)
    print("repeated factor: p, exponent, S_e mod p^4, S_(e-2) mod p^2, corrected digit",
          *repeated_6263(),flush=True)
