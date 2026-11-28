import CubeHankel228624

/-! # Short certificates for cube-Hankel determinants

Given one nonsingular order, an annihilating recurrence followed by
a nonzero discrepancy certifies the next normal order. We use this to
check the finite starting range of the rational perturbation theorem.
-/

open scoped BigOperators
open Matrix

namespace OMA.CubeHankel

private theorem discrepancy_step {F : Type*} [Field F] (u : ℕ → F)
    {q n : ℕ} (hq : (hankel u q).det ≠ 0) (hn : q<n) (a : Fin q → F)
    (quiet : ∀ j, j+1<n → u (j+q) + ∑ i, a i*u (j+i.val)=0)
    (jump : u (n-1+q) + ∑ i, a i*u (n-1+i.val)≠0) : (hankel u n).det≠0 := by
  classical
  have norec (c : Fin q → F) : ∃ j<n, u (j+q) + ∑ i, c i*u (j+i.val) ≠ 0 := by
    by_contra! no
    have inj := Matrix.mulVec_injective_iff_isUnit.mpr
      ((hankel u q).isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hq))
    have eq : c=a := by
      apply inj
      funext i
      have ec := no i.val (by have := i.isLt; omega)
      have ea := quiet i.val (by have := i.isLt; omega)
      change (∑ j, u (i.val+j.val) * c j) = ∑ j, u (i.val+j.val)*a j
      simpa only [mul_comm (u _) _] using (add_left_cancel (ec.trans ea.symm))
    exact jump (eq ▸ no (n-1) (by omega))
  obtain ⟨t,tq,tn,nz⟩ := next_normal u hq norec
  by_cases eq : t=n
  · exact eq ▸ nz
  exfalso
  let h : Fin t := ⟨q,tq⟩
  let idx (i : Fin q) : Fin t := ⟨i.val, by have := i.isLt; omega⟩
  let v : Fin t → F := Pi.single h 1 + ∑ i : Fin q, Pi.single (idx i) (a i)
  have hnz : v≠0 := by
    intro contra
    have ev := congrFun contra h
    have ne (i : Fin q) : h ≠ idx i := by
      intro e; have hval := Fin.ext_iff.mp e; dsimp [h,idx] at hval; have := i.isLt; omega
    simp [v,ne] at ev
  apply nz
  apply (hankel u t).exists_mulVec_eq_zero_iff.mp
  refine ⟨v,hnz,?_⟩
  rw [show v = _ from rfl,Matrix.mulVec_add,Matrix.mulVec_sum,Matrix.mulVec_single]
  funext i
  simpa [Matrix.mulVec_single,Matrix.col,hankel,h,idx,mul_comm] using
    quiet i.val (by have := i.isLt; omega)

private def sites : Finset ℕ := {6,25,62,123,214,341,510}

private theorem sites_match (j : ℕ) (hj : j≤726) :
    cubeSeq (ZMod 53) j = if j∈sites then 1 else 0 := by
  have iff : (∃ m≤j+2, m^3=j+2) ↔ j∈sites := by
    constructor
    · rintro ⟨m,_,eq⟩
      have sm : m≤8 := by
        by_contra! no
        have p := Nat.pow_le_pow_left no 3; norm_num at p; omega
      interval_cases m <;> simp [sites] at * <;> omega
    · intro mem
      simp [sites] at mem
      rcases mem with h|h|h|h|h|h|h <;> subst j <;> decide +kernel
  unfold cubeSeq
  simp only [iff]

private def digit (word i : ℕ) : ZMod 53 := ((word >>> (6*i)) % 64 : ℕ)

private def disc (q word j : ℕ) : ZMod 53 :=
  (if j+q∈sites then 1 else 0) +
    ∑ t ∈ sites, if j≤t ∧ t<j+q then digit word (t-j) else 0

private theorem disc_eq {q j : ℕ} (word : ℕ) (hj : j+q≤726) :
    cubeSeq (ZMod 53) (j+q) + ∑ i : Fin q, digit word i.val*cubeSeq (ZMod 53) (j+i.val) =
    disc q word j := by
  rw [disc,sites_match _ hj]
  congr 1
  calc
    ∑ i : Fin q, digit word i.val*cubeSeq (ZMod 53) (j+i.val) =
        ∑ i : Fin q, ∑ t ∈ sites, if j+i.val=t then digit word i.val else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [sites_match _ (by have := i.isLt; omega)]
      by_cases mem : j+i.val∈sites <;> simp [mem]
    _ = ∑ t ∈ sites, ∑ i : Fin q, if j+i.val=t then digit word i.val else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl; intro t _
      by_cases yes : j≤t ∧ t<j+q
      · rw [if_pos yes]
        let z : Fin q := ⟨t-j,by omega⟩
        rw [Finset.sum_eq_single z]
        · simp [z,show j+(t-j)=t by omega]
        · intro y _ ne
          rw [if_neg]; intro e; apply ne; apply Fin.ext; dsimp [z]; omega
        · simp
      · rw [if_neg yes]
        apply Finset.sum_eq_zero; intro i _
        rw [if_neg]; have := i.isLt; omega

private def checkWord (q n word : ℕ) : Bool :=
  (List.range n).all fun j => if j+1=n then decide (disc q word j≠0) else decide (disc q word j=0)

theorem certified {q n : ℕ} (word : ℕ) (hq : (hankel (cubeSeq (ZMod 53)) q).det≠0)
    (next : q<n) (bound : n≤364) (h : checkWord q n word = true) :
    (hankel (cubeSeq (ZMod 53)) n).det≠0 := by
  let : Fact (Nat.Prime 53) := ⟨by decide⟩
  apply discrepancy_step (F:=ZMod 53) (cubeSeq (ZMod 53)) hq next (fun i => digit word i.val)
  · intro j low
    rw [disc_eq _ (by omega)]
    have hj := List.all_eq_true.mp h j (List.mem_range.mpr (by omega))
    simpa [show j+1≠n by omega] using hj
  · rw [disc_eq _ (by omega)]
    have hj := List.all_eq_true.mp h (n-1) (List.mem_range.mpr (by omega))
    simpa [show n-1+1=n by omega] using hj

end OMA.CubeHankel
