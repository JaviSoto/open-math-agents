import RankThreeFront245212
import RankThreeData245212
import RankThreeOne245212

/-! The original divisor equation fails at twice a product of positive
powers of any three distinct odd primes. -/
namespace OMA.RankThreeTwice245212
open Nat
open scoped ArithmeticFunction.sigma

theorem original {p q r a b c : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (odd : 3≤p) (pq : p<q) (qr : q<r) (ap : 0<a) (bp : 0<b) (cp : 0<c) :
    OeisA245212.a (2*p^a*q^b*r^c)≠(σ 1 (2*p^a*q^b*r^c):ℤ) := by
  by_cases least : 5≤p
  · exact OMA.RankThreeOne245212.no_least_ge_five hp hq hr least pq qr ap bp cp
  have three : p=3 := by interval_cases p <;> norm_num at *
  subst p
  by_cases middle : 17≤q
  · exact OMA.RankThreeData245212.no_middle_ge_seventeen hq hr middle qr ap bp cp
  have small : 5≤q ∧ q≤13 := by interval_cases q <;> norm_num at *
  exact OMA.RankThreeFront245212.original hq hr small.1 small.2 qr ap bp cp

#print axioms original
end OMA.RankThreeTwice245212
