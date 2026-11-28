"""Exclude the only remaining composite shape 6263*q below 63917461².

The prime q must divide the reduced numerator of B_6260 and be 3289 mod
6262. A segmented sieve removes positions with a small prime factor; batched
gcds certify all remaining integers at once. No probable-prime tests are used.
Run with python3 quartic_single_cofactor.py; --max-q permits a short trial.
"""
import argparse
from fractions import Fraction
from hashlib import sha256
import json
from math import comb, gcd, isqrt, prod


FIRST_GAP = 63_917_461
P = 6263
MODULUS = P - 1
RESIDUE = 3289
TOP = (FIRST_GAP**2-1)//P


def bernoulli_numerator(index):
    """Exact even Bernoulli numbers from Brent–Harvey's tangent-number triangle."""
    count = index//2
    tangent = [1]*(count+1)
    for j in range(2,count+1):
        tangent[j]=(j-1)*tangent[j-1]
    for k in range(2,count+1):
        for j in range(k,count+1):
            tangent[j]=(j-k)*tangent[j-1]+(j-k+2)*tangent[j]
    values=[Fraction(1)]
    for j in range(1,count+1):
        p2 = 1<<(2*j)
        values.append(Fraction((-1)**(j-1)*2*j*tangent[j],p2*(p2-1)))
    # Verify the defining Bernoulli recurrence at the target and two lower rows.
    for j in (6,count//2,count):
        degree=2*j+1
        if sum(comb(degree,2*i)*values[i] for i in range(j+1)) != Fraction(degree,2):
            raise ValueError(f"Bernoulli recurrence failed at index {2*j}")
    return abs(values[-1].numerator)


def sieve_rules(limit):
    prime=bytearray(b"\1")*(limit+1)
    prime[:2]=b"\0\0"
    for i in range(2,isqrt(limit)+1):
        if prime[i]:
            prime[i*i::i]=bytes(1+(limit-i*i)//i)
    rules=[]
    for p in range(2,limit+1):
        if prime[p] and MODULUS%p:
            rules.append((p,(-RESIDUE*pow(MODULUS,-1,p))%p))
    return rules


def search(number, upper):
    start=(FIRST_GAP-RESIDUE+MODULUS-1)//MODULUS
    stop=(upper-RESIDUE)//MODULUS+1
    rules=sieve_rules(32_768)
    selected=0
    hits=[]
    for lo in range(start,stop,1<<20):
        count=min(1<<20,stop-lo)
        keep=bytearray(b"\1")*count
        for p,res in rules:
            j=(res-lo)%p
            if j<count:
                keep[j::p]=bytes(1+(count-1-j)//p)
        block=[]
        j=keep.find(b"\1")
        while j>=0:
            selected+=1
            block.append(RESIDUE+MODULUS*(lo+j))
            if len(block)==128:
                if gcd(prod(block),number)!=1:
                    hits.extend(q for q in block if number%q==0)
                block.clear()
            j=keep.find(b"\1",j+1)
        if block and gcd(prod(block),number)!=1:
            hits.extend(q for q in block if number%q==0)
    return dict(first=FIRST_GAP,last=upper,progressionEntries=max(0,stop-start),
                presieveSurvivors=selected,divisors=hits)


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-q",type=int,default=TOP)
    args=parser.parse_args()
    number=bernoulli_numerator(6260)
    result=search(number,args.max_q)
    result["numeratorBits"]=number.bit_length()
    result["numeratorSHA256"]=sha256(number.to_bytes((number.bit_length()+7)//8,"big")).hexdigest()
    print(json.dumps(result,indent=2))
