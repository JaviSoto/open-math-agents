"""Rule out 2^k * q^2 * p with q,p different odd primes; no conjectural cutoff.

The analytic bound q<2^20 is proved in even-core-prime-square-245212.md.
The remaining search intentionally uses N,D from the original even cofactor
and the logarithmic k bound, not the resultant divisibility filter.
"""
from math import isqrt


def prime_bases(stop):
    composite = bytearray(stop)
    for p in range(2,isqrt(stop-1)+1):
        if not composite[p]:
            composite[p*p::p] = bytes([1])*len(composite[p*p::p])
    return (q for q in range(3,stop,2) if not composite[q])


def boundary(k,q):
    z = 2**(k+1)
    w,s,t = 3*q*q+2*q+1,q*q+q+1,3*q*q
    b = z*(2*(k+1)*t-2*k*w-s)-(2*w-s)
    n = z*(k*w+s)+w-s
    return n,b


def small_exponent_certificate():
    for k in range(1,6):
        z = 2**(k+1)
        m = (z*(3*k+1)+2)//(5*(z-1))
        vals = [boundary(k,q) for q in (1024,1025,1026)]
        for line in ([n-m*d for n,d in vals],[(m+1)*d-n for n,d in vals]):
            # A quadratic's forward-difference expansion at 1024.
            assert line[0]>0 and line[1]-line[0]>=0 and line[2]-2*line[1]+line[0]>=0


def scan():
    cases = bases = positive = divisible = 0
    for q in prime_bases(1<<20):
        bases += 1
        u = q*q
        w,s,t = 3*u+2*q+1,u+q+1,3*u
        c = 2*w-s
        factor = w*s+2*t*(w-s)
        cap = 2*((c+factor).bit_length()-1)
        for k in range(1,cap+1):
            cases += 1
            h = 1<<k
            # W(2^k)=2kh+1, sigma(2^k)=2h-1, tau(2^k)=k+1.
            wb,sb = (2*k*h+1)*w,(2*h-1)*s
            d = 4*h*(k+1)*t-2*wb-sb
            if d<=0:
                continue
            positive += 1
            p,rem = divmod(wb+sb,d)
            if rem==0:
                divisible += 1
                if p>=3 and p%2 and p!=q:
                    raise ArithmeticError(f"unresolved q={q} k={k} quotient={p}")
    print(f"{bases} prime bases; {cases} exponents; {positive} positive denominators; {divisible} integer quotients.")


if __name__=="__main__":
    small_exponent_certificate()
    scan()
