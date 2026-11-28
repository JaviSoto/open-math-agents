"""Count prospective certificate operations without scanning large powers.

Run python3 RankThreeFourSmall_profile_245212.py. This is a cost model;
it does not itself decide the OEIS equality.
"""
from functools import lru_cache
from math import isqrt
from rank_three_middle_blocks_245212 import moments


def ilog(b,x):
    if x<b: return 0
    e=(x.bit_length()-1)//max(1,b.bit_length()-1)
    while b**e>x: e-=1
    while b**(e+1)<=x: e+=1
    return e


@lru_cache(maxsize=None)
def prime(n):
    return n>=2 and all(n%j for j in range(2,isqrt(n)+1))


def bounds(h,A,S,H,p,q):
    u,v=p-1,q-1
    diff=A*p*q-H*u*v
    if diff<=0:
        return 2*(A+S*u*v)//(A*q)
    E=2*A*(p+q)//diff
    M=2+3*(h.bit_length()+E*q.bit_length())
    T=min(E,max(S*q//A+1,ilog(p,2*A*(M+1)*q*q+A+S*q*q)+1))
    j=ilog(p,q)+1
    Z=j*T+ilog(p,2*(A*(T+1)+S))+2
    if Z+1<q and H%q:
        cost=2*(A*(Z+1)*q*q+q*(A+S*q*q))+A+S*q*q
        return min(T,ilog(p,cost)+1)
    return T


def main():
    for e in range(1,8):
        w,s,t=moments(3,e); h=4*3**e; A,S,H=17*w,7*s,24*t
        D=H-A; L=max(4,S//D+1); P=2*H*L//(D*L-S)
        maxE=(0,None); pairs=0; limits=0; pairs_short=0
        for p in range(5,P+1,2):
            if not prime(p): continue
            G=H*(p-1)-A*p
            if G<=0: continue
            Q=1+2*A*p//G
            for q in range(p+2,Q+1,2):
                if not prime(q):continue
                E=bounds(h,A,S,H,p,q)
                pairs+=1;limits+=E; pairs_short+=(E<=32)
                if E>maxE[0]:maxE=(E,(p,q))
        print(e,"first-prime ceiling",P,"finite pairs",pairs,"sum short exponents",limits,
              "pairs with ceiling <=32",pairs_short,"largest",maxE,flush=True)


if __name__=="__main__":
    main()
