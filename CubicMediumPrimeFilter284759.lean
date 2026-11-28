import CubicSmallPrimeFilter284759

namespace OMA.CubicMediumPrimeFilter284759
open Nat Finset

def rows (p k:ℕ) : Prop :=
  (p=101 ∧ k=68) ∨ (p=103 ∧ k=24) ∨ (p=131 ∧ k=22) ∨ (p=149 ∧ k=130) ∨
  (p=157 ∧ (k=62 ∨ k=110))

private theorem table :
    ∀p∈Ico 101 158, p.Prime → ∀ k∈range (p-1), 1<k → k%2=0 →
       p^2∣∑i∈range p,i^k → rows p k := by
  intro p pm pp
  obtain ⟨lo,hi⟩:=mem_Ico.mp pm
  interval_cases p <;> first | contradiction | norm_num at pp
  all_goals unfold rows; decide +kernel

theorem options {n p:ℕ} (on:Odd n) (hp:p.Prime) (lo:101≤p) (hi:p≤157) (pn:p∣n)
    (hit:n^3∣∑i∈Icc 1 (n-1),i^(n-2)) : rows p ((n-3)%(p-1)) := by
  obtain ⟨kl,kh,ev,dv⟩:=OMA.CubicSmallPrimeFilter284759.small_row on hp (by omega) pn hit
  exact table p (mem_Ico.mpr ⟨lo,by omega⟩) hp _ (mem_range.mpr kh) kl
    (Nat.mod_eq_zero_of_dvd ev.two_dvd) dv

#print axioms options
end OMA.CubicMediumPrimeFilter284759
