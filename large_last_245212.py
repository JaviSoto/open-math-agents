"""Certify rational inequalities vetoing arbitrarily large last primes.

For the three possible prefixes (3,5,q) and a chosen lower bound R>q, cover
all three prefix exponents. The exponent of the last prime is removed
algebraically at each leaf, without splitting its entire integer range.
"""
from fractions import Fraction as F
from functools import lru_cache
from math import prod
from time import monotonic
from equal_power_245212 import ybound,split


def cover(q,R,limit=200000,leaf=None,code=None):
    primes=(3,5,q)
    nodes=0
    waiting=[]
    maxima=[0]*3
    def record(box,lo,hi):
        if len(waiting)<10:
            waiting.append((box,lo,hi))
    start=monotonic()
    scale=F(R,R-1)
    def visit(box):
        nonlocal nodes
        nodes+=1
        if code is not None:
            slot=len(code)
            code.append(0)
        if nodes>limit:
            raise TimeoutError(box)
        yl=tuple(ybound(p,e[1])[0] for p,e in zip(primes,box))
        yh=tuple(ybound(p,e[0])[1] for p,e in zip(primes,box))
        xl=tuple(1+(1-y)/(p-1) for p,y in zip(primes,yh))
        xh=tuple(1+(1-y)/(p-1) for p,y in zip(primes,yl))
        X,U=prod(xl),prod(xh)
        Y,V=prod(yl),prod(yh)
        if X>=2 or (U+V/2)*scale<2:
            return 0
        need=2-U*scale
        # d+1 must belong to the closed interval between these bounds.
        dmin=max(2,(Y/(2-X)).__ceil__())
        dmax=(V*scale/need).__floor__() if need>0 else None
        if dmax is not None and dmax<dmin:
            return 0
        varying=[i for i,(a,b) in enumerate(box) if a!=b]
        if not varying:
            if leaf is not None:
                return leaf(primes,tuple(x[0] for x in box),dmin,dmax)
            record(box,dmin,dmax)
            return 1
        variation=[(yh[i]-yl[i])*(prod(xh[:i]+xh[i+1:])/(primes[i]-1)+prod(yh[:i]+yh[i+1:])/2)
            for i in varying]
        i=varying[variation.index(max(variation))]
        l,h=box[i]
        c=split(l,h)
        if code is not None:
            code[slot]=i+1
        maxima[i]=max(maxima[i],c)
        return visit(box[:i]+((l,c),)+box[i+1:])+visit(box[:i]+((c+1,h),)+box[i+1:])
    try:
        left=visit(((1,None),)*3)
    except (TimeoutError,RecursionError) as ex:
        return ("unfinished",str(ex)[:260],nodes,waiting,monotonic()-start)
    return ("finished",left,nodes,maxima,waiting,monotonic()-start)


@lru_cache(maxsize=150)
def local_moment(p,e):
    power=p**e
    tax=(e+1)*power
    sig=(power*p-1)//(p-1)
    return tax,(p*tax-sig)//(p-1),sig


def exact_leaf(R, record):
    def test(primes, exponents, lo, hi):
        if hi is None or hi-lo>100000:
            record.append(("unresolved exponent",exponents,lo,hi))
            return 1
        T,W,S=map(prod,zip(*(local_moment(p,a) for p,a in zip(primes,exponents))))
        for d1 in range(lo,hi+1):
            d=d1-1
            den=d1*(2*T-W)-S
            if den<=0:
                continue
            p,rem=divmod(d*W+S,den)
            if d==1:
                if rem:
                    continue
            else:
                if not rem:
                    continue
                p+=1
            if p<R or (W+S)%p!=0:
                continue
            record.append(("possible prime",exponents,d,p.bit_length()))
            return 1
        return 0
    return test


def generate(R,q,block,budget):
    code=[]
    failures=[]
    proof=cover(q,R,budget,exact_leaf(R,failures),code)
    if proof[:2] != ("finished",0):
        raise ValueError(proof,failures)
    def span(i):
        if code[i]==0:
            return i+1,1
        mid,d=span(i+1)
        end,g=span(mid)
        return end,1+max(d,g)
    def region(box):
        return "!["+",".join(f"⟨{lo},"+("none" if hi is None else f"some {hi}")+"⟩" for lo,hi in box)+"]"
    print("import LargeChecker245212\n")
    print("/-! Exact large-prime arithmetic certificate from large_last_245212.py. -/")
    print("namespace OMA.Large245212")
    def emit(i,box):
        end,depth=span(i)
        label=f"p{q}x{i}"
        b="start" if i==0 else "b"+label
        if i:
            print(f"private def {b} : B := {region(box)}")
        if end-i<=block:
            word=sum(c<<(2*j) for j,c in enumerate(code[i:end]))
            print("set_option maxHeartbeats 10000000 in\nset_option maxRecDepth 100000 in")
            print(f"private theorem {label} : Deny {R} {q} {b} :=")
            print(f"  sound (by decide) (by decide) {depth} {word} (tail:=0) (by decide +kernel)")
        else:
            ax=code[i]-1
            l,h=box[ax]
            cut=split(l,h)
            c1=list(box); c2=list(box); c1[ax]=(l,cut); c2[ax]=(cut+1,h)
            left=emit(i+1,c1)[0]
            right=emit(left,c2)[0]
            assert right==end
            vis="private " if i else ""
            print("set_option maxRecDepth 100000 in")
            print(f"{vis}theorem {label} : Deny {R} {q} {b} := by")
            print(f"  apply split {b} {ax}")
            for child,side in [(i+1,"leftB"),(left,"rightB")]:
                name=f"p{q}x{child}"
                print(f"  · rw [show {side} {b} {ax}=b{name} by funext i; fin_cases i <;> rfl]; exact {name}")
        return end,depth
    emit(0,[(1,None)]*3)
    print("end OMA.Large245212")


if __name__=="__main__":
    import argparse
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("last",type=int)
    ap.add_argument("q",type=int,choices=[7,11,13])
    ap.add_argument("--nodes",type=int,default=200000)
    ap.add_argument("--exact",action="store_true")
    ap.add_argument("--lean",action="store_true")
    ap.add_argument("--block",type=int,default=384)
    a=ap.parse_args()
    unresolved=[]
    if a.lean:
        generate(a.last,a.q,a.block,a.nodes)
    else:
        print(cover(a.q,a.last,a.nodes,exact_leaf(a.last,unresolved) if a.exact else None),unresolved[:20])
