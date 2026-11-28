"""Exact separation of every infinite-exponent face of X(3^a 5^b q^c)
from 2, for the only three prefixes allowing an unbounded fourth prime."""
from fractions import Fraction as F
from math import prod


def y(p,e):
    """Return rational lower and upper bounds for the geometric mean factor."""
    if e is None:
        return F(0), F(0)
    v=F(p,(p-1)*(e+1))
    if e<32:
        value=v*(1-F(1,p**(e+1)))
        return value,value
    return v*(1-F(1,p**32)),v


def face(q,k,delta=F(1,10**8)):
    ps=(3,5,q); stats=[0,0]
    def X(p,e):
        l,h=y(p,e)
        return 1+(1-h)/(p-1),1+(1-l)/(p-1)
    def visit(coords):
        stats[0]+=1
        low=[X(p,lo)[0] for p,(lo,hi) in zip(ps,coords)]
        high=[X(p,hi)[1] for p,(lo,hi) in zip(ps,coords)]
        if prod(high)<2-delta or prod(low)>2+delta:
            return None
        choices=[(high[i]-low[i],i) for i,(l,h) in enumerate(coords) if l!=h]
        if not choices:
            raise ValueError(q,k,coords,prod(low),prod(high))
        _,i=max(choices); l,h=coords[i]
        cut=2*l+1 if h is None else max(l,min(h-1,2*(l+1)*(h+1)//(l+h+2)-1))
        stats[1]=max(stats[1],cut+1)
        return (i,cut,visit(coords[:i]+((l,cut),)+coords[i+1:]),
                visit(coords[:i]+((cut+1,h),)+coords[i+1:]))
    bounds=tuple((None,None) if i==k else (1,None) for i in range(3))
    return visit(bounds),stats


def lean():
    print("import OddFaces245212\n")
    print("/-! Generated face certificates. Regenerate with odd_boundary_245212.py --lean. -/")
    print("namespace OMA.OddFaces245212\nopen OMA.Smooth245212")
    print("set_option maxHeartbeats 10000000\nset_option maxRecDepth 100000")
    print("def initial : Box := fun _ => ⟨1,none⟩")

    def encode(t):
        if t is None:
            return ".leaf"
        i,c,l,r=t
        return f"(.split {i} {c} {encode(l)} {encode(r)})"

    def output(t,q,k,path,box):
        expr=encode(t)
        if expr.count(".split")<=24:
            print(f"private def t{path} : Tree := {expr}")
            print(f"private theorem h{path} : Good {q} {k} {box} := fun _ h => sound (by decide) {k} t{path} (by decide +kernel) h")
        else:
            i,c,l,r=t
            for name,child,cut in [("l",l,"left"),("r",r,"right")]:
                print(f"private def b{path}{name} : Box := {cut} {box} {i} {c}")
                output(child,q,k,path+name,"b"+path+name)
            print(f"private theorem h{path} : Good {q} {k} {box} := bisect {box} {i} {c} h{path}l h{path}r")

    for q in (7,11,13):
        for k in range(3):
            output(face(q,k)[0],q,k,str(q)+str(k),"initial")
    print("theorem separation {q : ℕ} (hq : q=7 ∨ q=11 ∨ q=13) (k : Fin 3) (e : I → ℕ)")
    print("    (he : ∀ i,0<e i) : Separated (face q k e) := by")
    print("  have mem : ∀ i,(initial i).Contains (e i) := fun i => ⟨he i,by simp [initial]⟩")
    print("  rcases hq with rfl|rfl|rfl <;> fin_cases k")
    for q in (7,11,13):
        for k in range(3):
            print(f"  · exact h{q}{k} e mem")
    print("end OMA.OddFaces245212")


if __name__=="__main__":
    import sys
    if "--lean" in sys.argv:
        lean()
    else:
        for q in (7,11,13):
            for k in range(3):
                print(q,k,face(q,k)[1],flush=True)
