"""Final exact replay for n=2^k p^a x, p and x distinct odd primes.

The accompanying proof reduces any case not already excluded by tau<=71
to 1<=k+1<128, 35<=a<200 and p<=640. The other prime x is not bounded
by the checker: it is recovered as an exact integer quotient.
"""
from math import isqrt
from time import monotonic


def primes_to(n):
    return [p for p in range(3,n+1,2) if all(p%d for d in range(3,isqrt(p)+1,2))]


def check():
    begin=monotonic()
    primes=primes_to(640)
    seen=positive=integers=0
    for p in primes:
        P=W=S=1
        for a in range(1,200):
            P*=p
            W+=(a+1)*P
            S+=P
            if a<35: continue
            b=a+1
            for K in range(1,128):
                z=1<<K; k=K-1
                A=(1+k*z)*W
                U=(z-1)*S
                N=A+U
                D=2*z*K*b*P-2*A-U
                seen+=1
                if D<=0: continue
                positive+=1
                x,r=divmod(N,D)
                if r: continue
                integers+=1
                if x<=2 or x%2==0 or x==p: continue
                # Fail even for an unproved prime/composite integer. Check
                # the original local moment balance before reporting it.
                if A*(1+2*x)+U*(1+x)!=2*z*K*b*P*x:
                    raise AssertionError("quotient did not reproduce original balance")
                raise ArithmeticError(f"integer candidate: 2^{k} * {p}^{a} * {x}")
    if seen!=len(primes)*165*127: raise AssertionError("coverage")
    print(f"{len(primes)} odd primes; {seen} triples; {positive} positive denominators;"
          f" {integers} integer quotients; no candidate; {monotonic()-begin:.3f}s")


if __name__=="__main__":
    check()
