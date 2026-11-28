"""Check A105751 split valuations, short-segment bounds, and prime-power endpoints."""

from math import gcd


def valuation(value, prime):
    assert value
    value = abs(value)
    exponent = 0
    while value % prime == 0:
        value //= prime
        exponent += 1
    return exponent


def lifted_roots(prime, limit):
    root = next(x for x in range(1, prime) if (x*x + 1) % prime == 0)
    modulus = prime
    while modulus <= limit*limit + 1:
        yield modulus, root
        digit = (-(root*root+1)//modulus * pow(2*root, -1, prime)) % prime
        root += digit*modulus
        modulus *= prime


def check(prime, limit):
    roots = list(lifted_roots(prime, limit))
    endpoints = {}
    power = prime
    while power <= limit+1:
        endpoints[power-1] = endpoints[power] = (power-1)//(prime-1)
        power *= prime
    real, imaginary = 1, 0
    last_spike = {}
    ties = maximum = 0
    for n in range(1, limit+1):
        real, imaginary = real - n*imaginary, imaginary + n*real
        lower = sum(n//q + (n%q >= r) for q,r in roots)
        upper = sum(n//q + (n%q >= q-r) for q,r in roots)
        base = min(lower, upper)
        assert valuation(gcd(real, imaginary), prime) == base
        if imaginary == 0:
            assert n == 3
            continue
        actual = valuation(imaginary, prime)
        if n in endpoints:
            assert actual == endpoints[n]
        if upper != lower:
            assert actual == base
        else:
            ties += 1
        excess = actual-base
        maximum = max(maximum, excess)
        for level in range(1, excess+1):
            previous = last_spike.get(level)
            if previous and n <= 2*previous:
                assert prime**level <= (n+1)**(n-previous)
            last_spike[level] = n
    return ties, maximum


if __name__ == "__main__":
    for p in (5, 13, 17, 29, 37, 41):
        ties, maximum = check(p, 1100)
        print(f"p={p}, n=1..1100: {ties} ties with nonzero imaginary part, max excess {maximum}")
