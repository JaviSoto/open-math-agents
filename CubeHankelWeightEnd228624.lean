namespace OMA.CubeWeight

def unitCubes (t : ℕ) : ℚ := if ∃ m≤t, m^3=t then 1 else 0

/-- The actual unweighted cube-indicator matrices are nonsingular throughout
the finite base required by the induction. -/
theorem initial (n : ℕ) (lo : 177≤n) (hi : 2*n<729) : (weighted unitCubes n).det≠0 := by
  let M := OMA.CubeHankel.hankel (OMA.CubeHankel.cubeSeq ℤ) n
  have mod53 : (Int.castRingHom (ZMod 53)).mapMatrix M =
      OMA.CubeHankel.hankel (OMA.CubeHankel.cubeSeq (ZMod 53)) n := by
    ext i j
    change ((OMA.CubeHankel.cubeSeq ℤ (i.val+j.val):ℤ):ZMod 53) =
      OMA.CubeHankel.cubeSeq (ZMod 53) (i.val+j.val)
    by_cases cube : ∃ m ≤ i.val+j.val+2, m^3=i.val+j.val+2 <;> simp [OMA.CubeHankel.cubeSeq,cube]
  have rational : (Int.castRingHom ℚ).mapMatrix M = weighted unitCubes n := by
    ext i j
    change ((OMA.CubeHankel.cubeSeq ℤ (i.val+j.val):ℤ):ℚ) = unitCubes (i.val+j.val+2)
    by_cases cube : ∃ m ≤ i.val+j.val+2, m^3=i.val+j.val+2 <;> simp [OMA.CubeHankel.cubeSeq,unitCubes,cube]
  have h := OMA.CubeHankel.base53 n lo (by omega)
  rw [←mod53,←RingHom.map_det] at h
  rw [←rational,←RingHom.map_det]
  change (M.det:ℚ)≠0
  have int_ne : M.det≠0 := fun eq => h (by simp [eq])
  exact_mod_cast int_ne

theorem unweighted_base (n : ℕ) (lo : 177≤n) (hi : n≤364) :
    OeisA228624.b n ≠ 0 := by
  intro zero
  apply initial n lo (by omega)
  let M := OMA.CubeHankel.hankel (OMA.CubeHankel.cubeSeq ℤ) n
  have cast_eq : (Int.castRingHom ℚ).mapMatrix M = weighted unitCubes n := by
    ext i j
    change ((OMA.CubeHankel.cubeSeq ℤ (i.val+j.val):ℤ):ℚ) = unitCubes (i.val+j.val+2)
    by_cases cube : ∃ m ≤ i.val+j.val+2, m^3=i.val+j.val+2 <;> simp [OMA.CubeHankel.cubeSeq,unitCubes,cube]
  have det_eq : M.det=OeisA228624.b n := rfl
  rw [←cast_eq,←RingHom.map_det,det_eq,zero,map_zero]

/-- Arbitrarily small rational perturbations, shared by every entry on the
same cubical antidiagonal, make every leading determinant after 176 nonzero
simultaneously. All other entries remain the exact original values. -/
theorem near_one (ε : ℕ → ℚ) (pos : ∀ k, 0<ε k) :
    ∃ w : ℕ → ℚ, (∀ n, 177≤n → (weighted w n).det≠0) ∧
      (∀ k, 9≤k → 1 < w (k^3) ∧ w (k^3)<1+ε k) ∧
      ∀ t, (∀ k, 9≤k → k^3≠t) → w t=unitCubes t := by
  exact simultaneous _ initial (fun k => Set.Ioo 1 (1+ε k))
    (fun k _ => Set.Ioo_infinite (show (1:ℚ)<1+ε k by linarith [pos k]))

end OMA.CubeWeight
