import FormalConjectures.OEIS.«228624»
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! # Exceptional values of a cube-antidiagonal weight

If the preceding principal minor is nonsingular, the new cube weight
has at most the length of its antidiagonal many exceptional values.
This is the finite step in the simultaneous rational perturbation proof.
-/

open Matrix

namespace OMA.CubeWeight

theorem block_bad {m d : ℕ} (A : Matrix (Fin m) (Fin m) ℚ)
    (B : Matrix (Fin m) (Fin d) ℚ) (C : Matrix (Fin d) (Fin m) ℚ)
    (D : Matrix (Fin d) (Fin d) ℚ) (hn : A.det ≠ 0) :
    ∃ bad : Finset ℚ, bad.card ≤ d ∧ ∀ x : ℚ,
      (Matrix.fromBlocks A B C (Matrix.scalar (Fin d) x + D)).det = 0 ↔ x∈bad := by
  classical
  let : Invertible A := (A.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hn)).invertible
  let K := C * ⅟A * B - D
  let p := K.charpoly
  refine ⟨p.roots.toFinset, ?_, ?_⟩
  · exact (Multiset.toFinset_card_le _).trans (p.card_roots'.trans_eq (Matrix.charpoly_natDegree_eq_dim K |>.trans (Fintype.card_fin d)))
  · intro x
    rw [Matrix.det_fromBlocks₁₁, mul_eq_zero, or_iff_right hn]
    have eq : Matrix.scalar (Fin d) x+D-C*⅟A*B = Matrix.scalar (Fin d) x-K := by
      dsimp [K]; abel
    rw [eq,← Matrix.eval_charpoly]
    simp [p,K.charpoly_monic.ne_zero,Polynomial.IsRoot]

/-- Set the variable weight on the antidiagonal `i+j+1=2*m+d` in
zero-based coordinates. For cube-sum matrices this is the cube `2*m+d+1`. -/
def patch {m d : ℕ} (A : Matrix (Fin (m+d)) (Fin (m+d)) ℚ) (x : ℚ) :
    Matrix (Fin (m+d)) (Fin (m+d)) ℚ :=
  fun i j => A i j + if i.val+j.val+1=2*m+d then x else 0

theorem patch_bad {m d : ℕ} (A : Matrix (Fin (m+d)) (Fin (m+d)) ℚ)
    (hn : (A.submatrix (Fin.castAdd d) (Fin.castAdd d)).det ≠ 0) :
    ∃ bad : Finset ℚ, bad.card ≤ d ∧ ∀ x : ℚ, (patch (m:=m) (d:=d) A x).det=0 ↔ x∈bad := by
  classical
  let e : Fin m ⊕ Fin d ≃ Fin (m+d) := finSumFinEquiv
  let c : Fin m ⊕ Fin d ≃ Fin (m+d) := (Equiv.sumCongr (Equiv.refl _) Fin.revPerm).trans e
  let A₀ := A.submatrix (Fin.castAdd d) (Fin.castAdd d)
  let B := A.submatrix (Fin.castAdd d) (fun j : Fin d => Fin.natAdd m (Fin.revPerm j))
  let C := A.submatrix (Fin.natAdd m) (Fin.castAdd d)
  let D := A.submatrix (Fin.natAdd m) (fun j : Fin d => Fin.natAdd m (Fin.revPerm j))
  obtain ⟨bad,card,hbad⟩ := block_bad A₀ B C D hn
  refine ⟨bad,card,fun x => ?_⟩
  let T := patch (m:=m) (d:=d) A x
  have blocks : T.submatrix e c = Matrix.fromBlocks A₀ B C (Matrix.scalar (Fin d) x + D) := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        change _ + (if i.val+j.val+1=2*m+d then x else 0) = _
        rw [if_neg (by have := i.isLt; have := j.isLt; omega),add_zero]
        rfl
      | inr j =>
        change _ + (if i.val+(m+(d-(j.val+1)))+1=2*m+d then x else 0) = _
        rw [if_neg (by have := i.isLt; have := j.isLt; omega),add_zero]
        rfl
    | inr i =>
      cases j with
      | inl j =>
        change _ + (if m+i.val+j.val+1=2*m+d then x else 0) = _
        rw [if_neg (by have := i.isLt; have := j.isLt; omega),add_zero]
        rfl
      | inr j =>
        change _ + (if m+i.val+(m+(d-(j.val+1)))+1=2*m+d then x else 0) =
          (Matrix.scalar (Fin d) x) i j + _
        by_cases he : i=j
        · subst j
          rw [if_pos (by have := i.isLt; omega),Matrix.scalar_apply,Matrix.diagonal_apply_eq,add_comm]
          rfl
        · have hv : i.val≠j.val := fun h => he (Fin.ext h)
          rw [if_neg (by have := i.isLt; have := j.isLt; omega),Matrix.scalar_apply,Matrix.diagonal_apply_ne _ he,add_zero,zero_add]
          rfl
  have abs_eq := Matrix.abs_det_submatrix_equiv_equiv e c T
  rw [blocks] at abs_eq
  rw [←hbad,←abs_eq_zero,←abs_eq]
  exact abs_eq_zero

def weighted (w : ℕ → ℚ) (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => w (i.val+j.val+2)

def put (w : ℕ → ℚ) (s : ℕ) (x : ℚ) (t : ℕ) : ℚ := if s=t then x else w t

/-- At the root `k` stage, the next cube is the only changed antidiagonal.
One finite exceptional set controls all orders now in range. -/
theorem cube_stage (k : ℕ) (hk : 9≤k) (w : ℕ → ℚ)
    (secured : ∀ n, 177≤n → 2*n<k^3 → (weighted w n).det ≠ 0) :
    ∃ bad : Finset ℚ, ∀ x ∉ bad, ∀ n, 177≤n → 2*n<(k+1)^3 →
      (weighted (put w (k^3) x) n).det ≠ 0 := by
  classical
  have per (n : ℕ) : ∃ bad : Finset ℚ, ∀ x ∉ bad, 177≤n → 2*n<(k+1)^3 →
      (weighted (put w (k^3) x) n).det ≠ 0 := by
    by_cases inRange : 177≤n ∧ 2*n<(k+1)^3
    · by_cases old : 2*n<k^3
      · refine ⟨∅,fun x _ _ _ => ?_⟩
        have same : weighted (put w (k^3) x) n=weighted w n := by
          ext i j
          apply if_neg
          have := i.isLt; have := j.isLt; omega
        rw [same]
        exact secured n inRange.1 old
      · let m := k^3-n-1
        let d := n-m
        have large : 2*k^3 ≥ (k+1)^3 + 355 := by
          obtain ⟨a,rfl⟩ := Nat.exists_eq_add_of_le hk
          nlinarith only [Nat.zero_le (a^3), Nat.zero_le (a^2), Nat.zero_le a]
        have total : m+n+1=k^3 := by dsimp [m]; omega
        have mn : m<n := by omega
        have size : m+d=n := by dsimp [d]; omega
        have ok : (weighted w m).det≠0 := secured m (by omega) (by omega)
        let A := weighted w (m+d)
        obtain ⟨exc,_,hex⟩ := patch_bad (m:=m) (d:=d) A (show _ from ok)
        refine ⟨exc.image (fun t => t+w (k^3)),fun x hx _ _ => ?_⟩
        have diff : x-w (k^3) ∉ exc := by
          intro mem; apply hx
          exact Finset.mem_image.mpr ⟨_,mem,sub_add_cancel _ _⟩
        have eq : weighted (put w (k^3) x) (m+d) =
            patch (m:=m) (d:=d) A (x-w (k^3)) := by
          ext i j
          change (if k^3=i.val+j.val+2 then x else w (i.val+j.val+2)) =
            w (i.val+j.val+2) + (if i.val+j.val+1=2*m+d then x-w (k^3) else 0)
          by_cases yes : k^3=i.val+j.val+2
          · rw [if_pos yes,if_pos (by omega),←yes]; ring
          · rw [if_neg yes,if_neg (by omega),add_zero]
        rw [←size,eq]
        exact fun no => diff ((hex _).mp no)
    · exact ⟨∅,fun _ _ hn hu => False.elim (inRange ⟨hn,hu⟩)⟩
  choose hit works using per
  refine ⟨(Finset.range ((k+1)^3)).biUnion hit,fun x hx n hn htop => ?_⟩
  apply works n x _ hn htop
  intro mem; apply hx
  exact Finset.mem_biUnion.mpr ⟨n,Finset.mem_range.mpr (by omega),mem⟩

/-- Arbitrary infinite allowed sets for the later cube weights suffice.
The hypothesis only concerns the unchanging finite base, orders 177 to 364.
For example, take the allowed sets to be rational open intervals around one. -/
theorem simultaneous (w₀ : ℕ → ℚ)
    (base : ∀ n, 177≤n → 2*n<729 → (weighted w₀ n).det≠0)
    (allowed : ℕ → Set ℚ) (plenty : ∀ k, 9≤k → (allowed k).Infinite) :
    ∃ w : ℕ → ℚ, (∀ n, 177≤n → (weighted w n).det≠0) ∧
      (∀ k, 9≤k → w (k^3) ∈ allowed k) ∧
      ∀ t, (∀ k, 9≤k → k^3≠t) → w t=w₀ t := by
  classical
  let S (j : ℕ) := {w : ℕ → ℚ // ∀ n, 177≤n → 2*n<(j+9)^3 → (weighted w n).det≠0}
  have step (j : ℕ) (z : S j) : ∃ z' : S (j+1),
      ∃ x ∈ allowed (j+9), z'.val=put z.val ((j+9)^3) x := by
    obtain ⟨bad,works⟩ := cube_stage (j+9) (by omega) z.val z.property
    obtain ⟨x,ok,free⟩ := (plenty (j+9) (by omega)).exists_notMem_finset bad
    refine ⟨⟨put z.val ((j+9)^3) x,fun n hn hu => works x free n hn ?_⟩,x,ok,rfl⟩
    convert! hu using 2
  let start : S 0 := ⟨w₀,base⟩
  let z (j : ℕ) : S j := Nat.rec (motive := S) start (fun i u => (step i u).choose) j
  have transition (j : ℕ) : ∃ x ∈ allowed (j+9),
      (z (j+1)).val=put (z j).val ((j+9)^3) x := (step j (z j)).choose_spec
  have stable {a b t : ℕ} (ab : a≤b) (ht : t<(a+9)^3) :
      (z b).val t=(z a).val t := by
    induction b,ab using Nat.le_induction with
    | base => rfl
    | succ b ab ih =>
      obtain ⟨x,_,eq⟩ := transition b
      have pw := Nat.pow_le_pow_left (show a+9≤b+9 by omega) 3
      rw [eq,put,if_neg (by omega),ih]
  let w (t : ℕ) := (z (t+1)).val t
  have long (t : ℕ) : t<(t+1+9)^3 := by
    have := Nat.le_self_pow (n:=3) (by decide) (t+1+9)
    omega
  have freeze (a t : ℕ) (ht : t<(a+9)^3) : w t=(z a).val t := by
    rcases le_total a (t+1) with h|h
    · exact stable h ht
    · exact (stable h (long t)).symm
  refine ⟨w,?_,?_,?_⟩
  · intro n hn
    have eq : weighted w n=weighted (z (2*n+1)).val n := by
      ext i j
      exact freeze (2*n+1) (i.val+j.val+2) (by
        have := i.isLt; have := j.isLt; have := long (2*n); omega)
    rw [eq]
    exact (z _).property n hn (long (2*n))
  · intro k hk
    obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hk
    obtain ⟨x,ok,eq⟩ := transition j
    have index : 9+j=j+9 := by omega
    rw [index]
    have pw := Nat.pow_lt_pow_left (show j+9<j+1+9 by omega) (show 3≠0 by decide)
    rw [freeze (j+1) _ pw,eq,put,if_pos rfl]
    exact ok
  · intro t none
    have unchanged (j : ℕ) : (z j).val t=w₀ t := by
      induction j with
      | zero => rfl
      | succ j ih =>
        obtain ⟨x,_,eq⟩ := transition j
        rw [eq,put,if_neg (none _ (by omega)),ih]
    exact unchanged (t+1)

end OMA.CubeWeight
