import CubeHankel228624

/-! Four disjoint classes of columns from even residues give a linear
window between normal orders. This complements the elementary gap estimate
from runs of zeros in the cube sequence. -/

open scoped BigOperators
open Matrix

namespace OMA.CubeHankel

variable {F : Type*} [Field F]

/-- A degree-`q` recurrence makes every later shifted sample vector a linear
combination of the first `q` sample vectors for as long as the recurrence holds. -/
private lemma no_rec_of_minor {I J : Type*} [Fintype I] [Fintype J]
    (u : ℕ → F) {q limit maxCol : ℕ} (row : I → ℕ) (col : J → ℕ)
    (size : q < Fintype.card J)
    (rangeCol : ∀ i, col i ≤ maxCol)
    (within : ∀ i, row i + maxCol < limit + q)
    (ind : LinearIndependent F (fun j i => u (row i + col j)))
    (a : Fin q → F) :
    ∃ j < limit, u (j+q) + ∑ i, a i * u (j+i.val) ≠ 0 := by
  classical
  by_contra! rec
  let V (t : ℕ) : I → F := fun i => u (row i+t)
  let init (i : Fin q) := V i.val
  let S := Submodule.span F (Set.range init)
  have allV (t : ℕ) (ht : t ≤ maxCol) : V t ∈ S := by
    induction t using Nat.strong_induction_on with
    | h t ih =>
      by_cases h : t < q
      · exact Submodule.subset_span ⟨⟨t,h⟩, rfl⟩
      let b := t-q
      have eq : V t = -(∑ j : Fin q, a j • V (b+j.val)) := by
        ext i
        have hi := within i
        have van := rec (row i+b) (by dsimp [b]; omega)
        have offset : row i+b+q = row i+t := by dsimp [b]; omega
        simpa [V,offset,add_assoc] using eq_neg_of_add_eq_zero_left van
      rw [eq]
      apply S.neg_mem
      apply S.sum_mem
      intro j _
      apply S.smul_mem
      have hj := j.isLt
      exact ih (b+j.val) (by dsimp [b]; omega) (by dsimp [b]; omega)
  have sub : Submodule.span F (Set.range fun j i => u (row i + col j)) ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact allV _ (rangeCol j)
  have lo := Submodule.finrank_mono sub
  rw [finrank_span_eq_card ind] at lo
  have up : Module.finrank F S ≤ q := by
    change (Set.range init).finrank F ≤ q
    simpa using finrank_range_le_card (R := F) init
  omega

private lemma even_root {m a : ℕ} (h : m^3=2*a) : ∃ k, m = 2*k := by
  have he : Even (m^3) := ⟨a,by omega⟩
  have hm : Even m := (Nat.even_pow.mp he).1
  obtain ⟨k,hk⟩ := hm
  exact ⟨k,by omega⟩

private lemma cube_dilate (a : ℕ) :
    (∃ m ≤ 8*a, m^3=8*a) ↔ ∃ k ≤ a, k^3=a := by
  constructor
  · rintro ⟨m,_,hm⟩
    obtain ⟨k,rfl⟩ := even_root (m := m) (a := 4*a) (by omega)
    have hk : k^3=a := by nlinarith only [hm]
    exact ⟨k,hk ▸ Nat.le_self_pow (by decide) _,hk⟩
  · rintro ⟨k,ha,hk⟩
    exact ⟨2*k,by omega,by rw [mul_pow,hk]; norm_num⟩

private lemma cube_exclude {a : ℕ} (even : 2∣a) (eight : ¬8∣a) :
    ¬ ∃ m ≤ a, m^3=a := by
  rintro ⟨m,_,hm⟩
  obtain ⟨v,hv⟩ := even
  obtain ⟨k,hk⟩ := even_root (hm.trans hv)
  exact eight ⟨k^3, by rw [← hm,hk,mul_pow]; norm_num⟩

/-- Every normal cube-Hankel order over any field has another normal order
in a linear window. Restrict even columns to even rows. According to its
residue modulo eight, each column lies in a separate piece of the direct sum
of four copies of the old nonsingular Hankel matrix. -/
theorem cube_next_linear {q : ℕ} (hq : (hankel (cubeSeq F) q).det ≠ 0) :
    ∃ n > q, n ≤ 9*q+7 ∧ (hankel (cubeSeq F) n).det ≠ 0 := by
  classical
  by_cases hz : q=0
  · subst q; simpa using cube_next hq
  apply next_normal _ hq
  let row (i : Fin q × Fin 4) := 8*i.1.val + 13 - 2*i.2.val
  let col (j : Fin (q+1)) := 2*j.val+1
  apply no_rec_of_minor (cubeSeq F) (maxCol := 2*q+1) row col
  · simp
  · intro j; dsimp [col]; have := j.isLt; omega
  · intro i; dsimp [row]; have := i.1.isLt; omega
  · let e (j : Fin (q+1)) : Fin q × Fin 4 :=
      (⟨j.val/4,by have := j.isLt; omega⟩,⟨j.val%4,by omega⟩)
    have inj : Function.Injective e := by
      intro b c eq
      have fst := congrArg (fun z : Fin q × Fin 4 => z.1.val) eq
      have snd := congrArg (fun z : Fin q × Fin 4 => z.2.val) eq
      dsimp [e] at fst snd
      apply Fin.ext; omega
    let B := Matrix.blockDiagonal (fun _ : Fin 4 => hankel (cubeSeq F) q)
    have nz : B.det ≠ 0 := by simp [B,Matrix.det_blockDiagonal,hq]
    have eq : (fun j i => cubeSeq F (row i+col j)) = B.col ∘ e := by
      funext j i
      change cubeSeq F (row i+col j) = B i (e j)
      rw [show B i (e j) = _ from Matrix.blockDiagonal_apply _ _ _]
      by_cases h : i.2 = (e j).2
      · rw [if_pos h]
        have hv := Fin.ext_iff.mp h
        change i.2.val=j.val%4 at hv
        have h2 := i.2.isLt
        have arg : row i+col j+2 = 8*(i.1.val+j.val/4+2) := by dsimp [row,col]; omega
        simp only [cubeSeq,arg,cube_dilate]
        rfl
      · rw [if_neg h]
        apply if_neg
        apply cube_exclude
        · dsimp [row,col]; have := i.2.isLt; omega
        · have hn : i.2.val ≠ j.val%4 := fun he => h (Fin.ext he)
          dsimp [row,col]; have := i.2.isLt; omega
    rw [eq]
    exact (Matrix.linearIndependent_cols_of_det_ne_zero nz).comp e inj

private lemma det_mod (F : Type*) [Field F] (n : ℕ) :
    (OeisA228624.b n : F) = (hankel (cubeSeq F) n).det := by
  let M := hankel (cubeSeq ℤ) n
  have det_eq : M.det = OeisA228624.b n := rfl
  have cast_eq : (Int.castRingHom F).mapMatrix M = hankel (cubeSeq F) n := by
    ext i j
    change ((cubeSeq ℤ (i.val+j.val) : ℤ) : F) = cubeSeq F (i.val+j.val)
    by_cases hc : ∃ m ≤ i.val+j.val+2, m^3=i.val+j.val+2 <;> simp [cubeSeq,hc]
  rw [←cast_eq,←RingHom.map_det,det_eq]
  rfl

theorem oeis_next_nonzero {q : ℕ} (hq : OeisA228624.b q ≠ 0) :
    ∃ n > q, n ≤ 9*q+7 ∧ OeisA228624.b n ≠ 0 := by
  have hq' : (OeisA228624.b q : ℚ) ≠ 0 := by exact_mod_cast hq
  rw [det_mod] at hq'
  obtain ⟨n,large,small,ok⟩ := cube_next_linear hq'
  rw [←det_mod] at ok
  exact ⟨n,large,small,by exact_mod_cast ok⟩

theorem oeis_next_odd {q : ℕ} (hq : Odd (OeisA228624.b q)) :
    ∃ n > q, n ≤ 9*q+7 ∧ Odd (OeisA228624.b n) := by
  have cast_odd (z : ℤ) : (z : ZMod 2) ≠ 0 ↔ Odd z := by
    rw [ne_eq,ZMod.intCast_zmod_eq_zero_iff_dvd]
    change (¬ (2:ℤ) ∣ z) ↔ Odd z
    rw [←even_iff_two_dvd,Int.not_even_iff_odd]
  have nz := (cast_odd _).mpr hq
  rw [det_mod] at nz
  obtain ⟨n,large,small,ok⟩ := cube_next_linear nz
  rw [←det_mod] at ok
  exact ⟨n,large,small,(cast_odd _).mp ok⟩

end OMA.CubeHankel
