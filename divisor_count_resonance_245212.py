"""Find every coprime odd Euler resonance of a cofactor with bounded divisor count.

python3 divisor_count_resonance_245212.py --max-divisors 1024 --jobs 4
There is no bound on the cofactor, its prime factors, or the requested Euler rank.
Enumerate exponent patterns and possible unused Euler primes first. The reduced
denominator forces remaining bases; otherwise monotone comparison bounds their
least prime. One ceiling division recovers the last prime from the residual target.
All comparisons use integers and reduced fractions. GNU factor is optional:
proposed divisors are checked and primality is certified independently.
"""
from argparse import ArgumentParser
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
from fractions import Fraction
from functools import lru_cache
from itertools import combinations
from math import gcd,isqrt,prod
from shutil import which
from subprocess import run,TimeoutExpired
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
    return first_false_below(low,high,condition)


def first_false_below(low,high,condition):
    """First false argument in [low,high), or high when they are all true."""
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
    if end>2_000_000:
        # A near equality can produce an enormous upper endpoint. Never
        # allocate a sieve for its square root before reaching that region.
        for start in range(low,high,65536):
            stop=min(start+65536,high)
            if isqrt(stop-1)<=2_000_000:
                yield from prime_bases(start,stop)
            else:
                for p in range(start,stop,2):
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


def terminal_base(target,e):
    """The first reciprocal term and a strict geometric bound leave one integer."""
    scale=(e+1)*(target.numerator-target.denominator)
    return (e*target.denominator+scale-1)//scale


SMALL_PRIMES=(2,*prime_bases(3,1024))
PROBE_PRODUCT=prod(SMALL_PRIMES)
TRIAL_PRIMES=tuple(prime_bases(1025,32768))
FACTOR=which('gfactor') or which('factor')
ALL_TRIAL=SMALL_PRIMES+TRIAL_PRIMES


@lru_cache(maxsize=32768)
def known_prime(n):
    """Certify a factor by trial division. An unknown factor stays unknown."""
    for p in ALL_TRIAL:
        if p*p>n:
            return n
        if n%p==0:
            return p
    return None


@lru_cache(maxsize=16384)
def proposed_factors(n):
    """Optional accelerator. Factors and primality are verified separately."""
    if not FACTOR:
        return ()
    try:
        result=run([FACTOR,str(n)],capture_output=True,text=True,timeout=0.15,check=False)
        head,sep,tail=result.stdout.strip().partition(':')
        parts=tuple(map(int,tail.split()))
        if result.returncode==0 and sep and int(head)==n and all(1<p<=n for p in parts) and prod(parts)==n:
            return parts
    except (TimeoutExpired,ValueError,OSError):
        pass
    return ()


@lru_cache(maxsize=16384)
def certified_prime(n):
    """Lucas criterion: one unit has exact order n-1, with prime factors proved recursively."""
    if n<2:
        return False
    first=known_prime(n)
    if first is not None:
        return first==n
    parts=proposed_factors(n-1)
    if not parts or not all(certified_prime(q) for q in set(parts)):
        return False
    orders=tuple((n-1)//q for q in set(parts))
    return any(pow(a,n-1,n)==1 and all(pow(a,d,n)!=1 for d in orders) for a in range(2,48))


def denominator_prime(forced,prefix,deep=False):
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
            if deep and part.bit_length()<=112:
                for q in proposed_factors(part):
                    if certified_prime(q):
                        return q
    return known_prime(forced)


def perfect_power(n,e):
    if e==2:
        return isqrt(n)**2==n
    root=1<<((n.bit_length()+e-1)//e)
    while True:
        step=((e-1)*root+n//root**(e-1))//e
        if step>=root:
            return root**e==n
        root=step


@lru_cache(maxsize=32768)
def needs_two_primes(n,maximum):
    """In an admissible branch a composite, non-power cannot use just one base."""
    if n.bit_length()>2048 or maximum>64 or pow(2,n,n)==2%n:
        return False
    # Fermat's theorem proves n composite. A proper prime power with
    # exponent ≤ maximum must also be a perfect power of prime degree.
    return not any(perfect_power(n,d) for d in SMALL_PRIMES
                   if d<=min(maximum,n.bit_length()-1))


def excess_support(forced,prefix,exponents):
    """Partition the residual denominator into disjoint sets of prime divisors."""
    remaining=forced
    pieces=[]
    for p,e in prefix:
        part=gcd(remaining,weighted(p,e).numerator)
        if part==1:
            continue
        remaining//=part
        overlap=gcd(part,remaining)
        while overlap>1:
            remaining//=overlap
            part*=overlap
            overlap=gcd(part,remaining)
        pieces.append(part)
        if remaining==1:
            break
    if remaining>1:
        pieces.append(remaining)
    if len(pieces)>len(exponents):
        return True
    if 2*len(pieces)<=len(exponents):
        return False
    largest=max(exponents)
    return len(pieces)+sum(needs_two_primes(n,largest) for n in pieces)>len(exponents)


def two_prime_windows(exponents,target,minimum,upper,forced):
    """Bound the smaller prime on both sides without factoring a large denominator.

    If p<q and F divides p^e q^f, then q^f >= F/(upper-1)^e.
    This lower bound for q caps its contribution; meanwhile its contribution
    is strictly above 1. These two inequalities bracket p, even near a pole.
    """
    if upper<=minimum:
        return []
    windows=[]
    for i,e in enumerate(exponents):
        if i and e==exponents[0]:
            continue
        f=exponents[1-i]
        maximum=(upper-1)**e
        mass=(forced+maximum-1)//maximum
        lower_q=max(minimum,1<<((mass.bit_length()-1)//f))
        multiplier=weighted(lower_q,f)
        start=first_false_below(minimum,upper,lambda p:weighted(p,e)>=target)
        end=first_false_below(start,upper,lambda p:weighted(p,e)*multiplier>=target)
        if start<end:
            windows.append((e,f,start+(1-start%2),end))
    return windows


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
        p=terminal_base(target,e)
        den=target.denominator
        # W(p^e) is 1 modulo p. Reject nondivisors and impossibly large
        # powers before constructing a potentially enormous weighted value.
        if (p>=minimum and p%2 and p not in unused and den%p==0
                and e*(p.bit_length()-1)<den.bit_length()
                and den%(p**e)==0 and weighted(p,e)==target and factors(p)==(p,)):
            yield tuple(sorted((*prefix,(p,e))))
        stats['denominator completions']+=1
        return
    # The reduced denominator divides tau(tail)*prod(p^e). A prime still
    # present after removing that single tau factor MUST be a remaining base.
    den=target.denominator
    forced=den//gcd(den,prod(e+1 for e in exponents))
    upper=None
    if forced>1:
        q=denominator_prime(forced,prefix)
        if q is None:
            upper=first_false(minimum,lambda p: prod(weighted(p,e) for e in exponents)>=target)
            if upper-minimum>512 and excess_support(forced,prefix,exponents):
                stats['excess denominator support']+=1
                return
            if len(exponents)==2 and upper-minimum>64:
                windows=two_prime_windows(exponents,target,minimum,upper,forced)
                width=sum(max(0,hi-lo) for _,_,lo,hi in windows)
                if width<=max(16,(upper-minimum)//4):
                    stats['bounded two-prime windows']+=1
                    for e,f,lo,hi in windows:
                        for p in prime_bases(lo,hi):
                            if p not in unused:
                                stats['prime prefixes']+=1
                                yield from prefix_search((f,),unused,target/weighted(p,e),
                                    p+2,(*prefix,(p,e)),stats)
                    return
            if upper-minimum>512:
                q=denominator_prime(forced,prefix,deep=True)
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
    if upper is None:
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
        # CofactorCountResidue245212.necessary: tau(h) needs a prime
        # divisor 3 modulo 4, regardless of the size or parity of h.
        if not any(p%4==3 for p in factors(count)):
            continue
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


def run_block(block):
    return search(*block)


def run_ranges(start,end,strategy,progress,parity,jobs):
    if jobs==1:
        return search(end,strategy,start,progress,parity)
    blocks=((min(i+63,end),strategy,i,progress,parity) for i in range(start,end+1,64))
    totals=Counter()
    with ProcessPoolExecutor(max_workers=jobs) as pool:
        for result in pool.map(run_block,blocks):
            totals.update(result)
    return totals


if __name__=='__main__':
    parser=ArgumentParser(description=__doc__)
    parser.add_argument('--max-divisors',type=int,required=True)
    parser.add_argument('--min-divisors',type=int,default=2)
    parser.add_argument('--strategy',choices=('closure','quotient'),default='closure')
    parser.add_argument('--progress',action='store_true')
    parser.add_argument('--parity',choices=('all','even','odd'),default='all')
    parser.add_argument('--jobs',type=int,default=1,help='parallel 64-count blocks')
    args=parser.parse_args()
    if args.jobs<1 or not 2<=args.min_divisors<=args.max_divisors:
        parser.error('use a positive job count and 2 <= min-divisors <= max-divisors')
    print(args.parity,'cofactor divisor counts',args.min_divisors,'through',args.max_divisors,
          dict(run_ranges(args.min_divisors,args.max_divisors,args.strategy,args.progress,args.parity,args.jobs)))
