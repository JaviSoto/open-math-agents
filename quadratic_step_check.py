"""Exact off-grid tests: all positions lie in Q(sqrt(2)), with irrational breakpoints."""
from bisect import bisect_right
from collections import defaultdict
from functools import cmp_to_key


def plus(a,b):
    return (a[0]+b[0],a[1]+b[1])


def minus(a,b):
    return (a[0]-b[0],a[1]-b[1])


def times(a,b):
    return (a[0]*b[0]+2*a[1]*b[1],a[0]*b[1]+a[1]*b[0])


def scale(a,m):
    return (a[0]*m,a[1]*m)


def sign(a):
    x,y=a
    if not x:
        return (y>0)-(y<0)
    if not y or (x>0)==(y>0):
        return 1 if x>0 else -1
    # Opposite signs: compare absolute magnitudes using integer squares.
    return (1 if x>0 else -1)*(1 if x*x>2*y*y else -1)


def cmp(a,b):
    return sign(minus(a,b))


key=cmp_to_key(cmp)


def peak_mass(cuts,h):
    jumps=[a-b for a,b in zip(h+[0],[0]+h)]
    events=defaultdict(int)
    for i,(x,d) in enumerate(zip(cuts,jumps)):
        for j in range(i+1):
            events[plus(x,cuts[j])]+=(1 if i==j else 2)*d*jumps[j]
    v=peak=last=(0,0)
    slope=0
    for x in sorted(events,key=key):
        v=plus(v,scale(minus(x,last),slope))
        if cmp(v,peak)>0:
            peak=v
        slope+=events[x]
        last=x
    assert slope==0 and v==(0,0)
    mass=(0,0)
    for l,r,y in zip(cuts,cuts[1:],h):
        mass=plus(mass,scale(minus(r,l),y))
    return peak,mass


def experiment(cuts,heights,n):
    # Units are 1/(2n) throughout; breakpoints themselves are never rounded.
    inp=[scale(x,2*n) for x in cuts]
    whole=[(i,0) for i in range(2*n+1)]
    marks=sorted(set(whole)|set(inp),key=key)
    bin_code=list(map(key,whole))
    input_code=list(map(key,inp))
    h=[]
    D=10*n*n
    for x in marks[:-1]:
        half=bisect_right(bin_code,key(x))-1
        value=heights[bisect_right(input_code,key(x))-1]
        tilt=2*n-half//2
        h.append(value*(D+tilt if half%2==0 else D-tilt))
    old,mass=peak_mass(inp,heights)
    new,new_mass=peak_mass(marks,h)
    before=times(old,times(new_mass,new_mass))
    after=times(new,times(mass,mass))
    assert cmp(after,before)<0
    # Check an actual positive margin, not floating-point output.
    assert cmp(scale(minus(before,after),500*n*n),before)>0


if __name__=='__main__':
    zero,one=(0,0),(1,0)
    r=(-1,1)
    cases=[([zero,r,one],[1,2]),
           ([zero,r,scale(r,2),one],[1,2,0]),
           ([zero,minus(one,scale(r,2)),minus(one,r),one],[0,2,1]),
           ([zero,minus(one,scale(r,2)),r,scale(r,2),one],[2,0,1,3])]
    for n in [29,70,169]:
        for cuts,h in cases:
            experiment(cuts,h,n)
        print(f"n={n}: {len(cases)} exact irrational-partition improvements, each >1/(500 n²) relative")
