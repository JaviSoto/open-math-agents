import EulerSupportUnique245212
import WeightedMultipleHeight245212

/-! For any cofactor of any parity, each fresh odd Euler prime is reached
from a prime divisor of tau(h) by taking prime divisors of q-1 repeatedly. -/
namespace OMA.CofactorEulerAncestry245212
open Nat Finset ArithmeticFunction OMA.Smooth245212 OMA.CofactorEulerSeparation245212
open scoped ArithmeticFunction.sigma

inductive InPool (D : ℕ) : ℕ→Prop where
  | root {p : ℕ} (prime : p.Prime) (divides : p ∣ D) : InPool D p
  | descend {p q : ℕ} (ancestor : InPool D q) (prime : p.Prime) (divides : p ∣ (q-1)) : InPool D p

theorem next {h : ℕ} {T : Finset ℕ} {p : ℕ}
    (pr : ∀q∈T,q.Prime) (odd : ∀q∈T,Odd q) (fresh : ∀q∈T,h.Coprime q)
    (res : W h*num T=2*(h*σ 0 h)*den T) (mem : p∈T) :
    p∣σ 0 h ∨ ∃q∈T,p<q ∧ p∣q-1 := by
  have pp:=pr p mem
  have dv : p∣2*(h*σ 0 h)*den T:=res ▸ dvd_mul_of_dvd_right (dvd_prod_of_mem (fun q=>q) mem) _
  rcases pp.dvd_mul.mp dv with l|d
  · rcases pp.dvd_mul.mp l with two|hd
    · have same:=(prime_dvd_prime_iff_eq pp prime_two).mp two
      have od:=odd p mem
      exact False.elim (od.not_two_dvd_nat (by rw [same]))
    · rcases pp.dvd_mul.mp hd with hh|t
      · exact False.elim ((pp.coprime_iff_not_dvd.mp (fresh p mem).symm) hh)
      · exact Or.inl t
  · obtain ⟨q,mq,div⟩:=(pp.prime.dvd_finsetProd_iff (fun z=>z-1)).mp d
    have :=(pr q mq).one_lt
    have :=Nat.le_of_dvd (by omega : 0<q-1) div
    exact Or.inr ⟨q,mq,by omega,div⟩

theorem ancestry {h : ℕ} {T : Finset ℕ}
    (pr : ∀q∈T,q.Prime) (odd : ∀q∈T,Odd q) (fresh : ∀q∈T,h.Coprime q)
    (res : W h*num T=2*(h*σ 0 h)*den T) {p : ℕ} (mp : p∈T) : InPool (σ 0 h) p := by
  let top:=T.max' ⟨p,mp⟩
  have walk (j : ℕ) : ∀q∈T,top-q=j → InPool (σ 0 h) q := by
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro q mq m
      rcases next pr odd fresh res mq with root|⟨z,mz,lt,dvd⟩
      · exact .root (pr q mq) root
      · have hi : z≤top:=T.le_max' _ mz
        exact .descend (ih (top-z) (by omega) z mz rfl) (pr q mq) dvd
  exact walk _ p mp rfl

/-- All resonant cofactors of a given divisor count lie under one
effectively computable bound, at every rank and dyadic order. -/
theorem bounded {h : ℕ} {T : Finset ℕ} (pos : 0 < h) (fresh : ∀q∈T,h.Coprime q)
    (res : W h*num T=2*(h*σ 0 h)*den T) : h ≤ OMA.WeightedMultipleHeight245212.atCount (σ 0 h) :=
  OMA.WeightedMultipleHeight245212.divisor_count pos (OMA.EulerSupportUnique245212.cofactor_divides fresh res)

#print axioms ancestry
#print axioms bounded
end OMA.CofactorEulerAncestry245212
