"""Find every coprime odd Euler resonance of a cofactor with bounded divisor count.

python3 divisor_count_resonance_245212.py --max-divisors 128
There is no bound on the cofactor, its prime factors, or the requested Euler rank.
Enumerate exponent patterns and possible unused Euler primes first. The weighted
product then decreases strictly as any prefix prime increases; the last prime is
recovered by binary search. All comparisons use integers and reduced fractions.
"""
from argparse import ArgumentParser
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import combinations
from math import gcd,isqrt,prod
from time import monotonic

from cofactor_resonance_245212 import support
from rank_three_middle_blocks_245212 import moments


def v2(n):
    return (n & -n).bit_length()-1


@lru_cache(maxsize=16384)
def factors(n):
    primes = []
    d = 2
    while d*d <= n:
        if n%d==0:
            primes.append(d)
            while n%d==0:
                n//=d
        d = 3 if d==2 else d+2
    if n>1:
        primes.append(n)
    return tuple(primes)


def patterns(t,low=2):
    if t>=low:
        yield (t-1,)
    for a in range(low,isqrt(t)+1):
        if t%a==0:
            for rest in patterns(t//a,a):
                yield (a-1,*rest)


def unused_pool(t):
    found = set()
    stack = list(factors(t))
    while stack:
        p = stack.pop()
        if p!=2 and p not in found:
            found.add(p)
            stack.extend(factors(p-1))
    return sorted(found)


@lru_cache(maxsize=20000)
def weighted(p,e):
    w,_,den = moments(p,e)
    return Fraction(w,den)


def first_false(low,condition):
    """For a nonincreasing predicate, find the first false argument >= low."""
    high=low
    while condition(high):
        high*=2
    while low<high:
        mid=(low+high)//2
        if condition(mid):
            low=mid+1
        else:
            high=mid
    return low


def prime_bases(low,high):
    """Odd primes in [low,high), using bounded blocks and no per-base cache."""
    if low>=high:
        return
    end=isqrt(high-1)
    if high-low<64 and end>10000:
        for p in range(low,high,2):
            if factors(p)==(p,):
                yield p
        return
    sieve=bytearray([1])*(end+1)
    primes=[]
    for d in range(3,end+1,2):
        if sieve[d]:
            primes.append(d)
            if d*d<=end:
                sieve[d*d::2*d]=bytes((end-d*d)//(2*d)+1)
    for start in range(low,high,65536):
        stop=min(start+65536,high)
        flags=bytearray([1])*((stop-start+1)//2)
        for d in primes:
            if d*d>=stop:
                break
            first=max(d*d,((start+d-1)//d)*d)
            if not first%2:
                first+=d
            i=(first-start)//2
            if i<len(flags):
                flags[i::d]=bytes((len(flags)-1-i)//d+1)
        for i,b in enumerate(flags):
            if b:
                yield start+2*i


@lru_cache(maxsize=4096)
def divisors(n):
    small=[i for i in range(1,isqrt(n)+1) if n%i==0]
    return (*small,*(n//i for i in reversed(small) if i*i!=n))


def exact_root(n,e):
    if e==1:
        return n
    if e==2:
        x=isqrt(n)
    else:
        if n.bit_length()<=e:
            return 1 if n==1 else None
        x=1<<((n.bit_length()+e-1)//e)
        while True:
            y=((e-1)*x+n//x**(e-1))//e
            if y>=x:
                break
            x=y
    return x if x**e==n else None


SMALL_PRIMES=(2,*prime_bases(3,1024))
PROBE_PRODUCT=prod(SMALL_PRIMES)
TRIAL_PRIMES=tuple(prime_bases(1025,32768))


@lru_cache(maxsize=32768)
def known_prime(n):
    """Certify a factor by trial division. An unknown factor stays unknown."""
    for p in SMALL_PRIMES+TRIAL_PRIMES:
        if p*p>n:
            return n
        if n%p==0:
            return p
    return None


def denominator_prime(forced,prefix):
    probe=gcd(forced,PROBE_PRODUCT)
    if probe>1:
        return next(q for q in SMALL_PRIMES if not probe%q)
    # The denominator has inherited factors from the weighted moments of
    # individual prefix atoms. Split it there before trying a large integer.
    for p,e in prefix:
        part=gcd(forced,weighted(p,e).numerator)
        if part>1:
            q=known_prime(part)
            if q:
                return q
    return known_prime(forced)


def prefix_search(exponents,unused,target,minimum,prefix,stats):
    # All weighted factors exceed 1 and decrease towards 1 with their base.
    if target<=1:
        return
    if len(exponents)==1:
        e=exponents[0]
        if e==1:
            p,r=divmod(target.denominator,2*(target.numerator-target.denominator))
            stats['linear completions']+=1
            if not r and p>=minimum and p%2 and p not in unused and factors(p)==(p,):
                yield tuple(sorted((*prefix,(p,1))))
            return
        # W(p^e) is 1 mod p. The reduced denominator therefore has
        # exactly the form p^e * t for some t dividing e+1.
        den=target.denominator
        if minimum**e<=den:
            for t in divisors(e+1):
                if den%t:
                    continue
                p=exact_root(den//t,e)
                if p and p>=minimum and p%2 and p not in unused and weighted(p,e)==target and factors(p)==(p,):
                    yield tuple(sorted((*prefix,(p,e))))
        stats['denominator completions']+=1
        return
    # The reduced denominator divides tau(tail)*prod(p^e). A prime still
    # present after removing that single tau factor MUST be a remaining base.
    den=target.denominator
    forced=den//gcd(den,prod(e+1 for e in exponents))
    if forced>1:
        q=denominator_prime(forced,prefix)
        if q is not None:
            if q<minimum or q in unused:
                stats['impossible denominators']+=1
                return
            power=1
            rest=forced//q
            while not rest%q:
                power+=1
                rest//=q
            for i,e in enumerate(exponents):
                if e<power or (i and e==exponents[i-1]):
                    continue
                yield from prefix_search(exponents[:i]+exponents[i+1:],(*unused,q),
                    target/weighted(q,e),minimum,(*prefix,(q,e)),stats)
            stats['forced primes']+=1
            return
    # Replacing every later prime by the smallest possible one only increases
    # the product; stop as soon as even this upper bound falls short.
    upper=first_false(minimum,lambda p: prod(weighted(p,e) for e in exponents)>=target)
    for p in prime_bases(minimum,upper):
        if p in unused:
            continue
        stats['prime prefixes']+=1
        for j,e in enumerate(exponents):
            if j and e==exponents[j-1]:
                continue
            yield from prefix_search(exponents[:j]+exponents[j+1:],unused,target/weighted(p,e),
                                     p+2,(*prefix,(p,e)),stats)


def targets(count,strategy):
    if strategy=='quotient':
        # Integral W(h)/h=j, so there are fewer than count rational targets.
        for j in range(count+1,2*count):
            unused=support(1,j,2*count)
            if unused:
                yield unused,Fraction(j,count)
        return
    pool=unused_pool(count)
    for rank in range(1,len(pool)+1):
        for unused in combinations(pool,rank):
            if count%unused[-1]:
                continue
            t=2*prod(Fraction(q-1,q) for q in unused)
            if t>1 and count%t.denominator==0:
                yield unused,t


def parity_cases(exponents,parity):
    if parity!='even':
        yield (),exponents
    if parity!='odd':
        for j,e in enumerate(exponents):
            if j==0 or e!=exponents[j-1]:
                yield ((2,e),),exponents[:j]+exponents[j+1:]


def search(max_divisors,strategy='closure',minimum_count=2,progress=False,parity='all'):
    stats=Counter()
    for count in range(minimum_count,max_divisors+1):
        start=monotonic()
        feasible=tuple(targets(count,strategy))
        if not feasible:
            continue
        for exponents in patterns(count):
            for prefix,odd_exponents in parity_cases(exponents,parity):
                if not odd_exponents:  # W(2^a) is odd; a nonunit dyadic cannot divide it.
                    continue
                a=prefix[0][1] if prefix else 0
                weight=sum(v2(e+2)-1 for e in odd_exponents)-1-a-v2(a+1)
                for unused,target in feasible:
                    if sum(v2(q-1) for q in unused)!=weight:
                        continue
                    stats['Euler product and exponent patterns']+=1
                    tail=target/weighted(2,a) if prefix else target
                    for hit in prefix_search(odd_exponents,unused,tail,3,prefix,stats):
                        h=prod(p**e for p,e in hit)
                        print(f'h={h} factors={hit} tau={count} Euler={unused}',flush=True)
                        stats['resonances']+=1
        if progress and monotonic()-start>0.25:
            print(f'tau={count} completed in {monotonic()-start:.2f}s',flush=True)
    return stats


if __name__=='__main__':
    parser=ArgumentParser(description=__doc__)
    parser.add_argument('--max-divisors',type=int,required=True)
    parser.add_argument('--min-divisors',type=int,default=2)
    parser.add_argument('--strategy',choices=('closure','quotient'),default='closure')
    parser.add_argument('--progress',action='store_true')
    parser.add_argument('--parity',choices=('all','even','odd'),default='all')
    args=parser.parse_args()
    print(args.parity,'cofactor divisor counts',args.min_divisors,'through',args.max_divisors,
          dict(search(args.max_divisors,args.strategy,args.min_divisors,args.progress,args.parity)))
