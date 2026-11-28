"""Join consecutive checked 64·7^a prefixes back to the original OEIS input.

Use `python3 seven_prefix_location_245212.py 48 RankThreeSevenRange245212.lean`.
An exact input type on every imported lemma prevents skipping an exponent or
using a certificate for a different prime. Regenerate as more rows finish.
"""
import argparse
from pathlib import Path


def generate(end, module):
    if not 1 <= end <= 127 or not module.isidentifier():
        raise ValueError('use a terminal exponent from 1 through 127 and a module name')
    rows = [f'FixedLeast7K6A{e}' for e in range(1, end+1)]
    imports = '\n'.join(f'import {m}' for m in ['RankThreeSevenWitness245212', *rows])
    cases = '\n'.join(f'    · exact OMA.{m}.original pp qp gt pq bp cp hit' for m in rows)
    return f'''{imports}

/-! Remaining multiplicities of seven on the original rank-three input. -/
namespace OMA.{module}
open Nat OMA.Smooth245212
open scoped ArithmeticFunction.sigma

theorem bounds {{a p q b c : ℕ}} (ap : 0<a) (pp : p.Prime) (qp : q.Prime)
    (gt : 7<p) (pq : p<q) (bp : 0<b) (cp : 0<c)
    (hit : OeisA245212.a (2^6*7^a*p^b*q^c)=(σ 1 (2^6*7^a*p^b*q^c):ℤ)) :
    {end+1}≤a ∧ a≤127 := by
  constructor
  · by_contra! smaller
    interval_cases a
{cases}
  · by_contra! larger
    have cop (u : ℕ) (pr : u.Prime) (large : 7<u) : (2^6*7^a).Coprime u :=
      (((coprime_primes prime_two pr).mpr (by omega)).pow_left 6).mul_left
        (((coprime_primes (by decide : Nat.Prime 7) pr).mpr (by omega)).pow_left a)
    have veto:=OMA.FixedLeastPair245212.veto (by decide : Nat.Prime 7) (by decide)
      (Nat.mul_pos (pow_pos pp.pos b) (pow_pos qp.pos c))
      (((cop p pp gt).pow_right b).mul_right ((cop q qp (by omega)).pow_right c))
      (by simpa only [mul_assoc] using hit) (show 6≤6 by decide) (show 128≤a by omega)
    exact veto.not_ge (by decide +kernel)

theorem original {{n : ℕ}} (pos : 0<n) (rank : (n.primeFactors.erase 2).card=3)
    (hit : OeisA245212.a n=(σ 1 n:ℤ)) :
    64∣n ∧ ¬3∣n ∧ ¬5∣n ∧
      (7∣n → n.factorization 2=6 ∧ {end+1}≤n.factorization 7 ∧ n.factorization 7≤127) := by
  obtain ⟨dy,no3,no5,dy6⟩:=OMA.RankThreeSevenWitness245212.location pos rank hit
  refine ⟨dy,no3,no5,?_⟩;intro seven
  obtain ⟨p,q,b,c,pp,qp,gt,pq,bp,cp,rep⟩:=OMA.RankThreeSevenWitness245212.witness pos rank hit seven
  have ap:=(by decide : Nat.Prime 7).factorization_pos_of_dvd pos.ne' seven
  have lifted:=congrArg (fun t:ℕ=>OeisA245212.a t=(σ 1 t:ℤ)) rep
  exact ⟨dy6 seven,bounds ap pp qp gt pq bp cp (lifted.mp hit)⟩

#print axioms original
end OMA.{module}
'''


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('end', type=int)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    args.output.write_text(generate(args.end, args.output.stem))
