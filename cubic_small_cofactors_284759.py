"""Emit checked small-cofactor Bernoulli values and Lucas–Pratt certificates.

Run in the proof workspace with GNU factor installed. Factor and modular
pow results are proposals only; the generated Lean checks every product,
prime, and modular witness with the kernel.
"""
from fractions import Fraction
from math import lcm, prod
from pathlib import Path
from shutil import which
from subprocess import check_output
from cubic_census_284759 import even_bernoulli


def factor(n):
    tool = which("gfactor") or which("factor")
    factors = list(map(int, check_output([tool,str(n)],timeout=45,text=True).partition(":")[2].split()))
    if prod(factors) != n:
        raise ValueError(f"incorrect proposed factorization for {n}")
    return factors


def split_product(name, factors, witnesses=False, hp="hp", hd="hd", indent="  "):
    """Turn primality and a numerical product into the full set of possible divisors."""
    f = sorted(factors)
    txt = indent+f"rw [show {name}="+"*(".join(map(str,f))+")"*(len(f)-1)+f" by decide +kernel] at {hd}\n"
    for _ in range(len(f)-1):
        txt += indent+f"rcases {hp}.dvd_mul.mp {hd} with leaf|{hd}\n"
        txt += indent+"· "+case_prime(f.pop(0),hp,"leaf",witnesses)+"\n"
    return txt + indent+case_prime(f[0],hp,hd,witnesses)+"\n"


def case_prime(p,hp,hd,witnesses):
    proof = "(by decide +kernel)" if p<1000 else "prime"+str(p)
    finish = f"exact w{p}" if witnesses else "decide +kernel"
    return f"have eqn:q={p}:=(Nat.prime_dvd_prime_iff_eq {hp} {proof}).mp {hd}; rw [eqn]; {finish}"


def bits(n):
    return "["+",".join("true" if c=="1" else "false" for c in bin(n)[2:][::-1])+"]"


def prime_proofs(primes):
    seen = set()
    text = []
    def emit(p):
        if p < 1000 or p in seen:
            return
        factors = factor(p-1)
        for q in sorted(set(factors)):
            emit(q)
        g = next(a for a in range(2,1000) if pow(a,p-1,p)==1 and
                 all(pow(a,(p-1)//q,p)!=1 for q in factors))
        text.append(f"theorem prime{p} : Nat.Prime {p} := by\n"
                    f"  apply lucas_primality {p} ({g}:ZMod {p})\n"
                    f"  · exact eq_one {bits(p-1)} (by decide +kernel) (by decide +kernel)\n"
                    "  intro q hp hd\n")
        for q in sorted(set(factors)):
            text.append(f"  have w{q}:({g}:ZMod {p})^(({p}-1)/{q})≠1:=\n"
                        f"    ne_one {bits((p-1)//q)} (by decide +kernel) (by decide +kernel)\n")
        text.append(split_product(f"({p}-1)",factors,witnesses=True))
        seen.add(p)
    for p in sorted(set(primes)):
        emit(p)
    return "".join(text)


def generate(primes):
    indices = [p-3 for p in primes]
    evens = even_bernoulli(max(indices))
    values = [Fraction(-1,2) if i==1 else Fraction(0) if i%2 else evens[i//2]
              for i in range(max(indices)+1)]
    denominator = lcm(*(x.denominator for x in values))
    coefficients = ",".join(str(int(x*denominator)) for x in values)
    text = "import BernoulliList284759\nimport PrattRows284759\n\nnamespace OMA.SmallCubicRows284759\n"
    text += "open OMA.BernoulliList284759 OMA.PrattRows284759\nset_option maxRecDepth 65536\nset_option maxHeartbeats 0\n"
    text += f"private def data:List ℤ:=[{coefficients}]\nprivate theorem checked:∀j:Fin {len(values)}, row data j=if (j:ℕ)=0 then ({denominator}:ℤ) else 0:=by decide +kernel\n"
    all_factors = {i:factor(abs(values[i].numerator)) for i in indices}
    text += prime_proofs(q for qs in all_factors.values() for q in qs)
    for i in indices:
        v = values[i]
        n = abs(v.numerator)
        txt = f"theorem numerator{i}: (bernoulli {i}).num.natAbs={n}:=by\n"
        txt += f"  have eqn:=sound (j:={i}) {denominator} data checked (by decide)\n"
        txt += f"  rw [show coeff data {i}={int(v*denominator)} by decide +kernel] at eqn\n"
        txt += f"  have value:bernoulli {i}=({v.numerator}:ℚ)/{v.denominator}:=by push_cast at eqn; linarith\n"
        txt += "  rw [value]; norm_num\n"
        options = sorted(set(all_factors[i]))
        txt += f"theorem factors{i} {{q:ℕ}} (hp:q.Prime) (hd:q∣{n}) : "+" ∨ ".join("q="+str(q) for q in options)+" := by\n"
        text += txt+split_product(n,all_factors[i])
    return text+"end OMA.SmallCubicRows284759\n"


if __name__=="__main__":
    Path("SmallCubicRows284759.lean").write_text(generate([37,59,67]))
