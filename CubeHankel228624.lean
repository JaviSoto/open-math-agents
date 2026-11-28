import FormalConjectures.OEIS.«228624»

/-!
# Infinitely many nonsingular leading Hankel minors

A normal order and the first failure of its associated linear recurrence give
the next nonsingular leading matrix. Applied to the cube-indicator sequence,
the recurrence must fail because of the unbounded zero runs preceding cubes.
-/

open scoped BigOperators
open Matrix

namespace OMA.CubeHankel

variable {F : Type*} [Field F]

def hankel (u : ℕ → F) (n : ℕ) : Matrix (Fin n) (Fin n) F :=
  fun i j => u (i.val + j.val)

private lemma anti_det {s : ℕ} (A : Matrix (Fin s) (Fin s) F) {b : F} (hb : b ≠ 0)
    (van : ∀ i j : Fin s, i.val + j.val + 1 < s → A i j = 0)
    (bd : ∀ i j : Fin s, i.val + j.val + 1 = s → A i j = b) :
    A.det ≠ 0 := by
  let B := A.submatrix id Fin.revPerm
  have hu : B.IsLowerTriangular := by
    intro i j h
    apply van i (Fin.revPerm j)
    have hj := j.isLt
    change i.val + (s - (j.val+1)) + 1 < s
    change i.val < j.val at h
    omega
  have diag (i : Fin s) : B i i = b := by
    apply bd i (Fin.revPerm i)
    have hi := i.isLt
    change i.val + (s - (i.val+1)) + 1 = s
    omega
  have hB : B.det ≠ 0 := by
    rw [B.det_of_isLowerTriangular hu]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => (diag i).symm ▸ hb)
  contrapose! hB
  simp [B, Matrix.det_permute', hB]

theorem next_normal (u : ℕ → F) {q limit : ℕ} (hq : (hankel u q).det ≠ 0)
    (noRec : ∀ a : Fin q → F, ∃ j < limit, u (j+q) + ∑ i, a i * u (j+i.val) ≠ 0) :
    ∃ n > q, n ≤ limit ∧ (hankel u n).det ≠ 0 := by
  classical
  let M := hankel u q
  let rhs : Fin q → F := fun i => -u (i.val+q)
  let a := M⁻¹ *ᵥ rhs
  let h (j : ℕ) := u (j+q) + ∑ i, a i * u (j+i.val)
  have hinit (i : Fin q) : h i.val = 0 := by
    have mul : M *ᵥ a = rhs := by
      simp [a, Matrix.mulVec_mulVec, M.mul_nonsing_inv (isUnit_iff_ne_zero.mpr hq)]
    have hi := congrFun mul i
    change (∑ j : Fin q, u (i.val+j.val)*a j) = -u (i.val+q) at hi
    simp only [h, mul_comm (a _) _, hi, add_neg_cancel]
  obtain ⟨w, hw, bad⟩ := noRec a
  have ex : ∃ j, h j ≠ 0 := ⟨w,bad⟩
  let d := Nat.find ex
  have hd : h d ≠ 0 := Nat.find_spec ex
  have zero (j : ℕ) (hj : j < d) : h j = 0 := by simpa using Nat.find_min ex hj
  have hqd : q ≤ d := by
    by_contra! hlt
    exact hd (hinit ⟨d,hlt⟩)
  let s := d+1-q
  have sz : q+s=d+1 := by dsimp [s]; omega
  have spos : 0<s := by omega
  have dw : d ≤ w := Nat.find_min' ex bad
  refine ⟨q+s, by omega, by omega, ?_⟩
  let e : Fin q ⊕ Fin s ≃ Fin (q+s) := finSumFinEquiv
  let A := (hankel u (q+s)).submatrix e e
  let idx (i : Fin q) (j : Fin s) : Fin (q+s) := ⟨i.val+j.val, by omega⟩
  let C : Matrix (Fin q ⊕ Fin s) (Fin q ⊕ Fin s) F := fun z w =>
    match w with
    | .inl i => if z = .inl i then 1 else 0
    | .inr j => (if z = .inr j then 1 else 0) +
      ∑ i : Fin q, if z = e.symm (idx i j) then a i else 0
  have left (i : Fin q ⊕ Fin s) (j : Fin q) : (A*C) i (.inl j) = u ((e i).val+j.val) := by
    change (∑ z : Fin q ⊕ Fin s, A i z * (if z = .inl j then 1 else 0)) = _
    simp [mul_ite, A, Matrix.submatrix, e, hankel]
  have right (i : Fin q ⊕ Fin s) (j : Fin s) : (A*C) i (.inr j) = h ((e i).val+j.val) := by
    change (∑ z : Fin q ⊕ Fin s, A i z *
      ((if z = .inr j then 1 else 0) +
        ∑ t : Fin q, if z = e.symm (idx t j) then a t else 0)) = _
    simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum,mul_ite,mul_one,mul_zero,
      Finset.sum_ite_eq',Finset.mem_univ,if_true]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true,A,Matrix.submatrix_apply,
      Equiv.apply_symm_apply,hankel,idx,h]
    congr 1
    · change u ((e i).val+(q+j.val)) = u ((e i).val+j.val+q)
      congr 1; omega
    · apply Finset.sum_congr rfl
      intro t _
      rw [mul_comm]
      congr 2; omega
  let B : Matrix (Fin s) (Fin s) F := fun i j => h (q+i.val+j.val)
  have hB : B.det ≠ 0 := by
    apply anti_det B hd
    · intro i j hij
      apply zero
      omega
    · intro i j hij
      change h (q+i.val+j.val) = h d
      congr 1; omega
  let W : Matrix (Fin s) (Fin q) F := fun i j => u (q+i.val+j.val)
  have blocks : A*C = Matrix.fromBlocks M 0 W B := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j => simpa [M,e,hankel] using left (.inl i) j
      | inr j =>
        rw [right]
        change h (i.val+j.val) = 0
        apply zero
        omega
    | inr i =>
      cases j with
      | inl j => exact left (.inr i) j
      | inr j => exact right (.inr i) j
  have prod_ne : (A*C).det ≠ 0 := by
    rw [blocks,Matrix.det_fromBlocks_zero₁₂]
    exact mul_ne_zero hq hB
  rw [Matrix.det_mul,Matrix.det_submatrix_equiv_self] at prod_ne
  exact left_ne_zero_of_mul prod_ne

def cubeSeq (F : Type*) [Zero F] [One F] (j : ℕ) : F :=
  if ∃ m ≤ j+2, m^3=j+2 then 1 else 0

/-- An explicit next-normal window over any field, including every prime characteristic. -/
theorem cube_next {q : ℕ} (hq : (hankel (cubeSeq F) q).det ≠ 0) :
    ∃ n > q, n ≤ (Nat.sqrt q+2)^3-1-q ∧ (hankel (cubeSeq F) n).det ≠ 0 := by
  apply next_normal _ hq
  intro a
  let k := Nat.sqrt q+2
  have hs := Nat.lt_succ_sqrt q
  have hgap : (k-1)^3 + q < k^3 := by
    dsimp [k]
    nlinarith only [hs, Nat.zero_le ((Nat.sqrt q)^2)]
  have hk : 2 ≤ k := by dsimp [k]; omega
  let j := k^3-2-q
  have hbig : q+2 ≤ k^3 := by
    have : 1 ≤ (k-1)^3 := Nat.one_le_pow _ _ (by omega)
    omega
  have hsuc : j+q+2=k^3 := by dsimp [j]; omega
  refine ⟨j, by dsimp [j,k] at *; omega, ?_⟩
  have this_one : cubeSeq F (j+q)=1 := by
    apply if_pos
    exact ⟨k, by rw [hsuc]; exact Nat.le_self_pow (by decide) _, hsuc.symm⟩
  have small (i : Fin q) : cubeSeq F (j+i.val)=0 := by
    apply if_neg
    rintro ⟨m,_,hm⟩
    by_cases hmk : m < k
    · have h := Nat.pow_le_pow_left (show m ≤ k-1 by omega) 3
      omega
    · have h := Nat.pow_le_pow_left (show k ≤ m by omega) 3
      omega
  simp [this_one, small]

theorem cube_unbounded (F : Type*) [Field F] (N : ℕ) :
    ∃ n ≥ N, (hankel (cubeSeq F) n).det ≠ 0 := by
  induction N with
  | zero => exact ⟨0,by omega,by simp⟩
  | succ N ih =>
    obtain ⟨q,hq,hn⟩ := ih
    obtain ⟨n,gt,_,nonzero⟩ := cube_next hn
    exact ⟨n,by omega,nonzero⟩

/-- The actual integer sequence of the original conjecture is nonzero arbitrarily late. -/
theorem oeis_unbounded (N : ℕ) : ∃ n ≥ N, OeisA228624.b n ≠ 0 := by
  obtain ⟨n,nn,hn⟩ := cube_unbounded ℚ N
  refine ⟨n,nn,fun bad => hn ?_⟩
  let M : Matrix (Fin n) (Fin n) ℤ := fun i j => cubeSeq ℤ (i.val+j.val)
  have eq : M.det = OeisA228624.b n := rfl
  have cast_eq : (Int.castRingHom ℚ).mapMatrix M = hankel (cubeSeq ℚ) n := by
    ext i j
    change ((cubeSeq ℤ (i.val+j.val) : ℤ) : ℚ) = cubeSeq ℚ (i.val+j.val)
    by_cases hc : ∃ m ≤ i.val+j.val+2, m^3=i.val+j.val+2 <;> simp [cubeSeq,hc]
  rw [←cast_eq, ←RingHom.map_det,eq,bad,map_zero]

/-- Even after reduction modulo two the actual integer determinants are frequently nonzero. -/
theorem oeis_odd_unbounded (N : ℕ) : ∃ n ≥ N, Odd (OeisA228624.b n) := by
  obtain ⟨n,nn,hn⟩ := cube_unbounded (ZMod 2) N
  refine ⟨n,nn,?_⟩
  let M : Matrix (Fin n) (Fin n) ℤ := fun i j => cubeSeq ℤ (i.val+j.val)
  have eq : M.det = OeisA228624.b n := rfl
  have cast_eq : (Int.castRingHom (ZMod 2)).mapMatrix M = hankel (cubeSeq (ZMod 2)) n := by
    ext i j
    change ((cubeSeq ℤ (i.val+j.val) : ℤ) : ZMod 2) = cubeSeq (ZMod 2) (i.val+j.val)
    by_cases hc : ∃ m ≤ i.val+j.val+2, m^3=i.val+j.val+2 <;> simp [cubeSeq,hc]
  rw [←cast_eq, ←RingHom.map_det,eq] at hn
  by_contra contra
  obtain ⟨m, hm⟩ := Int.not_odd_iff_even.mp contra
  apply hn
  rw [hm,map_add]
  exact CharTwo.add_self_eq_zero _

end OMA.CubeHankel
