import Mathlib

namespace OMA.CyclicDrift
open Finset

/-- Along all edges of a translation, potential differences sum to zero.
Marked predecessors consume at least two units, and strict ones an extra unit. -/
theorem potential_count {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (g : G) (P : G → ℤ) (D K : Finset G) (sub : K⊆D)
    (all : ∀ x, P (x+g) ≤ P x+1) (two : ∀ x∈D, P (x+g)+1 ≤ P x)
    (three : ∀ x∈K, P (x+g)+2 ≤ P x) :
    2*D.card+K.card ≤ Fintype.card G := by
  classical
  have bound (x : G) : (if x∈D then (2:ℤ) else 0)+(if x∈K then (1:ℤ) else 0)
      ≤ 1+P x-P (x+g) := by
    by_cases hk : x∈K
    · simp only [hk,sub hk,if_true]
      linarith [three x hk]
    · by_cases hd : x∈D
      · simp only [hd,hk,if_true,if_false]
        linarith [two x hd]
      · simp only [hd,hk,if_false]
        linarith [all x]
  have total := Finset.sum_le_sum (s:=(univ : Finset G)) (fun x _ => bound x)
  have perm : (∑ x, P (x+g))=∑ x,P x := Equiv.sum_comp (Equiv.addRight g) P
  simp only [sum_add_distrib,sum_sub_distrib,perm,add_sub_cancel_right] at total
  simp at total
  exact_mod_cast (by linarith : (2:ℤ)*D.card+K.card ≤ Fintype.card G)
end OMA.CyclicDrift
