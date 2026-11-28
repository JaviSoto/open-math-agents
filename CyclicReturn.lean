import Mathlib

/-! Positive first returns to a finite set under translation. The disjoint
half-open arcs between visits have total length at most the group order. -/
namespace OMA.CyclicReturn
open Finset

theorem packing {G : Type*} [AddCommGroup G] [Fintype G] (D : Finset G) (x : G)
    (_non : D.Nonempty) :
    ∃ (gap : D → ℕ) (next : D ≃ D), (∀ s, 0 < gap s) ∧
      (∀ s, (next s).val = s.val + gap s • x) ∧
      (∀ s t, 0 < t → t < gap s → s.val + t • x ∉ D) ∧
      (∑ s, gap s) ≤ Fintype.card G := by
  classical
  have existsReturn (s : D) : ∃ k : ℕ, 0<k ∧ s.val+k • x ∈ D := by
    exact ⟨addOrderOf x, addOrderOf_pos x, by simp⟩
  let gap (s : D) := Nat.find (existsReturn s)
  have valid (s : D) : 0<gap s ∧ s.val+gap s • x ∈ D := Nat.find_spec (existsReturn s)
  have minimal (s : D) (t : ℕ) (ht : 0<t) (lt : t<gap s) : s.val+t • x ∉ D :=
    fun h => (Nat.find_min (existsReturn s) lt) ⟨ht,h⟩
  have separate (s t : D) (i j : ℕ) (lt : j < i) (bound : i-j < gap s)
      (e : s.val+i • x=t.val+j • x) : False := by
    apply minimal s (i-j) (by omega) bound
    have same : s.val+(i-j) • x=t.val := by
      apply add_right_cancel (b:=j • x)
      rw [add_assoc, ← add_nsmul, Nat.sub_add_cancel lt.le, e]
    simp [same]
  let T (s : D) : D := ⟨s.val + gap s • x,(valid s).2⟩
  have ti : Function.Injective T := by
    intro s t e
    have eq : s.val+gap s • x=t.val+gap t • x := congrArg Subtype.val e
    rcases lt_trichotomy (gap s) (gap t) with h|h|h
    · exact (separate t s _ _ h (by have := (valid s).1; omega) eq.symm).elim
    · rw [h] at eq; exact Subtype.ext (add_right_cancel eq)
    · exact (separate s t _ _ h (by have := (valid t).1; omega) eq).elim
  let arc (a : (s : D) × Fin (gap s)) := (a.1:G)+a.2.val • x
  have ai : Function.Injective arc := by
    rintro ⟨s,i⟩ ⟨t,j⟩ eq
    change (s:G)+i.val • x=(t:G)+j.val • x at eq
    rcases lt_trichotomy i.val j.val with h|h|h
    · exact (separate t s _ _ h (by have := j.isLt; omega) eq.symm).elim
    · rw [h] at eq
      obtain rfl : s=t := Subtype.ext (add_right_cancel eq)
      obtain rfl : i=j := Fin.ext h
      rfl
    · exact (separate s t _ _ h (by have := i.isLt; omega) eq).elim
  refine ⟨gap, Equiv.ofBijective T (Finite.injective_iff_bijective.mp ti),
    fun s => (valid s).1, fun _ => rfl, minimal, ?_⟩
  simpa [Fintype.card_sigma] using Fintype.card_le_of_injective arc ai

end OMA.CyclicReturn
