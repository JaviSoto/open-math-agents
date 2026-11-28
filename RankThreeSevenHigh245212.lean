import FixedLeast7K7A1
import FixedLeast7K7A2
import FixedLeast7K7A3
import FixedLeast7K7A4
import FixedLeast7K7A5
import FixedLeast7K7A6
import FixedLeast7K8A1
import FixedLeast7K8A2
import FixedLeast7K8A3
import FixedLeast7K9A1
import FixedLeast7K9A2
import FixedLeast7K10A1
import FixedLeast7K11A1
import FixedLeast7K12A1
import FixedLeast7K13A1

/-! With three odd prime factors and least odd prime seven, the dyadic
exponent seven or higher is ruled out by fifteen fixed-prefix certificates. -/

namespace OMA.RankThreeSevenHigh245212
open Nat OMA.Smooth245212
open scoped ArithmeticFunction.sigma

/-- With least odd prime seven and three distinct odd factors, the dyadic
exponent of a solution is below seven. All odd exponents are unrestricted. -/
theorem original {k a p q b c : ℕ} (hk : 7≤k) (ap : 0<a) (pp : p.Prime) (qp : q.Prime)
    (gt : 7<p) (pq : p<q) (bp : 0<b) (cp : 0<c) :
    OeisA245212.a (2^k*7^a*p^b*q^c)≠(σ 1 (2^k*7^a*p^b*q^c):ℤ) := by
  intro eqn
  have seven : Nat.Prime 7:=by decide
  have cop (r : ℕ) (pr : r.Prime) (gr : 7<r) : (2^k*7^a).Coprime r :=
    (((coprime_primes prime_two pr).mpr (by omega)).pow_left k).mul_left
      (((coprime_primes seven pr).mpr (by omega)).pow_left a)
  have veto {i j : ℕ} (ik : i≤k) (ja : j≤a) (high : 2≤X 2 (some i)*X 7 (some j)) : False :=
    (OMA.FixedLeastPair245212.veto seven (by decide) (Nat.mul_pos (pow_pos pp.pos b) (pow_pos qp.pos c))
      (((cop p pp gt).pow_right b).mul_right ((cop q qp (by omega)).pow_right c))
      (by simpa only [mul_assoc] using eqn) ik ja).not_ge high
  have top : k≤13:=by by_contra! no;exact veto (i:=14) (j:=1) no ap (by decide +kernel)
  have b7 (h : 7≤k) : a≤6:=by by_contra! no;exact veto (i:=7) (j:=7) h no (by decide +kernel)
  have b8 (h : 8≤k) : a≤3:=by by_contra! no;exact veto (i:=8) (j:=4) h no (by decide +kernel)
  have b9 (h : 9≤k) : a≤2:=by by_contra! no;exact veto (i:=9) (j:=3) h no (by decide +kernel)
  have b10 (h : 10≤k) : a≤1:=by by_contra! no;exact veto (i:=10) (j:=2) h no (by decide +kernel)
  interval_cases k
  · have bound : a≤6:=b7 (by decide)
    interval_cases a
    · exact OMA.FixedLeast7K7A1.original pp qp gt pq bp cp eqn
    · exact OMA.FixedLeast7K7A2.original pp qp gt pq bp cp eqn
    · exact OMA.FixedLeast7K7A3.original pp qp gt pq bp cp eqn
    · exact OMA.FixedLeast7K7A4.original pp qp gt pq bp cp eqn
    · exact OMA.FixedLeast7K7A5.original pp qp gt pq bp cp eqn
    · exact OMA.FixedLeast7K7A6.original pp qp gt pq bp cp eqn
  · have bound : a≤3:=b8 (by decide)
    interval_cases a
    · exact OMA.FixedLeast7K8A1.original pp qp gt pq bp cp eqn
    · exact OMA.FixedLeast7K8A2.original pp qp gt pq bp cp eqn
    · exact OMA.FixedLeast7K8A3.original pp qp gt pq bp cp eqn
  · have bound : a≤2:=b9 (by decide)
    interval_cases a
    · exact OMA.FixedLeast7K9A1.original pp qp gt pq bp cp eqn
    · exact OMA.FixedLeast7K9A2.original pp qp gt pq bp cp eqn
  · have bound : a≤1:=b10 (by decide)
    interval_cases a
    · exact OMA.FixedLeast7K10A1.original pp qp gt pq bp cp eqn
  · have bound : a≤1:=b10 (by decide)
    interval_cases a
    · exact OMA.FixedLeast7K11A1.original pp qp gt pq bp cp eqn
  · have bound : a≤1:=b10 (by decide)
    interval_cases a
    · exact OMA.FixedLeast7K12A1.original pp qp gt pq bp cp eqn
  · have bound : a≤1:=b10 (by decide)
    interval_cases a
    · exact OMA.FixedLeast7K13A1.original pp qp gt pq bp cp eqn
#print axioms original
end OMA.RankThreeSevenHigh245212
