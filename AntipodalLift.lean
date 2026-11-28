import AffineDoubling

/-! An affine doubling orbit lifts through an antipodal pair in a valid
    cyclic set, even if the individual lifts were chosen arbitrarily. -/

open private OMA.AffineDoubling.replace from AffineDoubling
namespace OMA.AntipodalLift
open Finset Arxiv.«2607.08366»

/-- No choice of lifts can break all affine-doubling closures above a
    doubled fiber. The proof uses one three-label exchange. -/
theorem closed {N : ℕ} {Q : Type*} [AddCommGroup Q] [DecidableEq Q]
    (A : Finset (ZMod N)) (ok : IsValidMod A) (π : ZMod N→+Q) (h : ZMod N)
    (hne : h≠0) (ker : ∀ z,π z=0 ↔ z=0 ∨ z=h) (c : ZMod N)
    (lo : c∈A) (hi : c+h∈A) (t : Q)
    (down : ∀ y∈A.image π,2 • y+t∈A.image π) :
    ∃ u : ZMod N,π u=t ∧ ∀ z∈A,2 • z+u∈A := by
  classical
  have ph := (ker h).mpr (Or.inr rfl)
  have same (y z : ZMod N) (eq : π y=π z) : y=z ∨ y=z+h := by
    have e := (ker (y-z)).mp (by rw [map_sub,eq,sub_self])
    rcases e with z0|zh
    · exact Or.inl (sub_eq_zero.mp z0)
    · exact Or.inr (by rw [←zh]; abel)
  obtain ⟨d,da,de⟩ := mem_image.mp (down (π c) (mem_image_of_mem π lo))
  let u := d-2 • c
  have pu : π u=t := by simp only [u,map_sub,map_nsmul,de]; abel
  refine ⟨u,pu,?_⟩
  intro z za
  let w := 2 • z+u
  change w∈A
  have pw : π w=2 • π z+t := by simp only [w,map_add,map_nsmul,pu]
  obtain ⟨v,va,ev⟩ := mem_image.mp (down (π z) (mem_image_of_mem π za))
  by_cases split : π w=π c
  · rcases same w c split with e|e
    · exact e ▸ lo
    · exact e ▸ hi
  rcases same w v (pw.trans ev.symm) with e|bad
  · exact e ▸ va
  exfalso
  have vc : v≠c := fun e=>split ((pw.trans ev.symm).trans (congrArg π e))
  have vh : v≠c+h := by
    intro e
    apply split
    rw [pw,←ev,e,map_add,ph,add_zero]
  have ch : c≠c+h := fun e=>hne (add_eq_left.mp e.symm)
  let F : Finset (ZMod N) := {v,c,c+h}
  let word : Multiset (ZMod N) := {z,z,d}
  have rival := OMA.AffineDoubling.replace ok F (insert_subset va (insert_subset lo (singleton_subset_iff.mpr hi))) word
    (by simp [word,za,da]) (by simp [F,word,vc,vh,ch])
    (by
      have e : 2 • z+d-2 • c=v+h := by simpa only [w,u,add_sub_assoc] using bad
      have ee := eq_add_of_sub_eq e
      simp only [two_nsmul] at ee
      simp [F,word,vc,vh,ch]
      linear_combination ee)
  have nd := F.nodup
  rw [←rival] at nd
  simp [word] at nd

end OMA.AntipodalLift
