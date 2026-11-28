import FormalConjectures.OEIS.«228624»
import Mathlib.LinearAlgebra.Matrix.SchurComplement

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

/- # Exceptional values of a cube-antidiagonal weight

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

/- # Short certificates for cube-Hankel determinants

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

namespace OMA.CubeHankel
private theorem normal0 : (hankel (cubeSeq (ZMod 53)) 0).det ≠ 0 := by rw [Matrix.det_isEmpty]; decide
private theorem normal7 : (hankel (cubeSeq (ZMod 53)) 7).det ≠ 0 :=
  certified 0x0 normal0 (by decide) (by decide) (by decide +kernel)
private theorem normal19 : (hankel (cubeSeq (ZMod 53)) 19).det ≠ 0 :=
  certified 0x0 normal7 (by decide) (by decide) (by decide +kernel)
private theorem normal26 : (hankel (cubeSeq (ZMod 53)) 26).det ≠ 0 :=
  certified 0x34 normal19 (by decide) (by decide) (by decide +kernel)
private theorem normal37 : (hankel (cubeSeq (ZMod 53)) 37).det ≠ 0 :=
  certified 0x0 normal26 (by decide) (by decide) (by decide +kernel)
private theorem normal44 : (hankel (cubeSeq (ZMod 53)) 44).det ≠ 0 :=
  certified 0x40000000000000000000000000034 normal37 (by decide) (by decide) (by decide +kernel)
private theorem normal56 : (hankel (cubeSeq (ZMod 53)) 56).det ≠ 0 :=
  certified 0xd00000000000 normal44 (by decide) (by decide) (by decide +kernel)
private theorem normal63 : (hankel (cubeSeq (ZMod 53)) 63).det ≠ 0 :=
  certified 0x40000000000000000000000000000000000000000000000000000034 normal56 (by decide) (by decide) (by decide +kernel)
private theorem normal66 : (hankel (cubeSeq (ZMod 53)) 66).det ≠ 0 :=
  certified 0x1000000000000000000000000000040000000000000000000000000000000000000000000000000000034000 normal63 (by decide) (by decide) (by decide +kernel)
private theorem normal68 : (hankel (cubeSeq (ZMod 53)) 68).det ≠ 0 :=
  certified 0x40000001000000000000000000001000000040000000000000000000000000000000000000000000000d00000034 normal66 (by decide) (by decide) (by decide +kernel)
private theorem normal80 : (hankel (cubeSeq (ZMod 53)) 80).det ≠ 0 :=
  certified 0x1000000000000000000000000000000000000000000000000000000d00000000000 normal68 (by decide) (by decide) (by decide +kernel)
private theorem normal82 : (hankel (cubeSeq (ZMod 53)) 82).det ≠ 0 :=
  certified 0x34000000d00000000000000000000000000034000000d00000000000000000000000000d00000000000000000000040000001 normal80 (by decide) (by decide) (by decide +kernel)
private theorem normal85 : (hankel (cubeSeq (ZMod 53)) 85).det ≠ 0 :=
  certified 0xd00000000000000000000000000000000000d00000000000000000000000000d00000000000000000000000000001000 normal82 (by decide) (by decide) (by decide +kernel)
private theorem normal87 : (hankel (cubeSeq (ZMod 53)) 87).det ≠ 0 :=
  certified 0x34000000000000000000000000000040000000000000000000000000000000000040000000000000000034000000040000000000000000000000000034 normal85 (by decide) (by decide) (by decide +kernel)
private theorem normal98 : (hankel (cubeSeq (ZMod 53)) 98).det ≠ 0 :=
  certified 0x34000000000000000000000000000000000000000 normal87 (by decide) (by decide) (by decide +kernel)
private theorem normal100 : (hankel (cubeSeq (ZMod 53)) 100).det ≠ 0 :=
  certified 0x40000034000000000000000000000000000040000000000000000000000000000000000000000000000000000034000000040000000000000000000000000034 normal98 (by decide) (by decide) (by decide +kernel)
private theorem normal103 : (hankel (cubeSeq (ZMod 53)) 103).det ≠ 0 :=
  certified 0x34000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000040000000000000000000000000034000 normal100 (by decide) (by decide) (by decide +kernel)
private theorem normal105 : (hankel (cubeSeq (ZMod 53)) 105).det ≠ 0 :=
  certified 0x1000000000000000000000000034000000000000000000001000000040000000000000000000000000000000000000000000000000000000000000040000000000000000000d00000034 normal103 (by decide) (by decide) (by decide +kernel)
private theorem normal110 : (hankel (cubeSeq (ZMod 53)) 110).det ≠ 0 :=
  certified 0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000d00000000000 normal105 (by decide) (by decide) (by decide +kernel)
private theorem normal112 : (hankel (cubeSeq (ZMod 53)) 112).det ≠ 0 :=
  certified 0xd00000034000000000000000000000000001000000000040000000034000000d00000000000000000000000000000000000000000000000000000000000000d00000000034000000000040000001 normal110 (by decide) (by decide) (by decide +kernel)
private theorem normal115 : (hankel (cubeSeq (ZMod 53)) 115).det ≠ 0 :=
  certified 0x40000034000000000000000000000000001000000000040000000001000000d00000000000000000000000000000000000000000000000000000000000000d00000000034000000000d00000001000 normal112 (by decide) (by decide) (by decide +kernel)
private theorem normal116 : (hankel (cubeSeq (ZMod 53)) 116).det ≠ 0 :=
  certified 0xd0001a00103400068004001b000000000000000000040d0001a001034000680040d0001a0010006c00000000000000000000000000000000000000000000000000000340010006c0d0004001b0340010006c0d0001a normal115 (by decide) (by decide) (by decide +kernel)
private theorem normal117 : (hankel (cubeSeq (ZMod 53)) 117).det ≠ 0 :=
  certified 0x6b46c16a805ad1b05aa016b46cd0000000000000000016b46c16a805ad1b05aa016b46c16a805ad1b340000000000000000000000000000000000000000000000000000d1b05ad1b3746c16b46cdd1b05ad1b3746c16a8 normal116 (by decide) (by decide) (by decide +kernel)
private theorem normal118 : (hankel (cubeSeq (ZMod 53)) 118).det ≠ 0 :=
  certified 0xb56a80b56b2d5aa02d5acb56a80b00000000000000004b56a80b56b2d5aa02d5acb56a80b56b2d5aa02c0000000000000000000000000000000000000000000000000034aa02d5aa02aa80b56a80aaa02d5aa02aa80b56a normal117 (by decide) (by decide) (by decide +kernel)
private theorem normal119 : (hankel (cubeSeq (ZMod 53)) 119).det ≠ 0 :=
  certified 0xc1d34041002074d01040081d340410000000000000010c1d34041002074d01040081d34041002074d01040000000000000000000000000000000000000000000000000d32d01074d00cf4041d34033d01074d00cf4041d34 normal118 (by decide) (by decide) (by decide +kernel)
private theorem normal120 : (hankel (cubeSeq (ZMod 53)) 120).det ≠ 0 :=
  certified 0x1a6da6db69b00069b6da6c001a6db69b00000000000005a6da6db69b00069b6da6c001a6db69b00069b6da6c00000000000000000000000000000000000000000000000346da6da69b68001b69a6da0006da69b68001b69a6da normal119 (by decide) (by decide) (by decide +kernel)
private theorem normal121 : (hankel (cubeSeq (ZMod 53)) 121).det ≠ 0 :=
  certified 0x40040040001000001000040000040001000000000001040040040001000001000040000040001000001000040000000000000000000000000000000000000000000000d34034034000d00000d00034000034000d00000d00034 normal120 (by decide) (by decide) (by decide +kernel)
private theorem normal122 : (hankel (cubeSeq (ZMod 53)) 122).det ≠ 0 :=
  certified 0x40000001000000000040000000001000000000000040040000001000000000040000000001000000000040000000000000000000000000000000000000000000000034034000000d00000000034000000000d00000000034000 normal121 (by decide) (by decide) (by decide +kernel)
private theorem normal123 : (hankel (cubeSeq (ZMod 53)) 123).det ≠ 0 :=
  certified 0xd00d00000034000000000d00000000034000000001000d00d00000034000000000d00000000034000000000d00000000000000000000000000000000000000000000d00001001000000040000000001000000000040000000001 normal122 (by decide) (by decide) (by decide +kernel)
private theorem normal125 : (hankel (cubeSeq (ZMod 53)) 125).det ≠ 0 :=
  certified 0x340740b4040001d01000000074040000001d010000000740740b4040001d01000000074040000001d01000000074040000000000000000000000000000000000000000034074073074000d01d00000034074000000d01d00000034074 normal123 (by decide) (by decide) (by decide +kernel)
private theorem normal126 : (hankel (cubeSeq (ZMod 53)) 126).det ≠ 0 :=
  certified 0x20f31001f3101083cc40000420f3100001083cc40000420f31001f3101083cc40000420f3100001083cc40000420f3100000000000000000000000000000000000000034cf20b102e0b1d33c82c40034cf20b1000d33c82c40034cf20b1 normal125 (by decide) (by decide) (by decide +kernel)
private theorem normal127 : (hankel (cubeSeq (ZMod 53)) 127).det ≠ 0 :=
  certified 0x5ed3c89800089d7b4f2260015ed3c8980057b4f2260015ed3c89800089d7b4f2260015ed3c8980057b4f2260015ed3c8980000000000000000000000000000000000000d1e226b4f000b4e7889ad3c0d1e226b4f0347889ad3c0d1e226b4f normal126 (by decide) (by decide) (by decide +kernel)
private theorem normal128 : (hankel (cubeSeq (ZMod 53)) 128).det ≠ 0 :=
  certified 0xf881934440000822064d1104f8819344413e2064d1104f881934440000822064d1104f8819344413e2064d1104f881934440000000000000000000000000000000000034993d110640000154f4441934993d11064d264f4441934993d11064 normal127 (by decide) (by decide) (by decide +kernel)
private theorem normal129 : (hankel (cubeSeq (ZMod 53)) 129).det ≠ 0 :=
  certified 0xa8b82a28ba80000020a8a2eba8b82a28baea2e0a8a2eba8b82a28ba80000020a8a2eba8b82a28baea2e0a8a2eba8b82a28ba80000000000000000000000000000000000d0ba952eba8b00000054baea28ba952eba8a2ea54baea28ba952eba8b normal128 (by decide) (by decide) (by decide +kernel)
private theorem normal130 : (hankel (cubeSeq (ZMod 53)) 130).det ≠ 0 :=
  certified 0x2681019d1bd00000000674701681019d1c05a040674701681019d1bd00000000674701681019d1c05a040674701681019d1bd00000000000000000000000000000000034cdbd0070168100000001c059d1bd007016746f401c059d1bd00701681 normal129 (by decide) (by decide) (by decide +kernel)
private theorem normal131 : (hankel (cubeSeq (ZMod 53)) 131).det ≠ 0 :=
  certified 0x4654520008a48c00000000230134520008c04d14800230134520008a48c00000000230134520008c04d14800230134520008a48c0000000000000000000000000000000d244248c00134520000000004808a48c00120229230004808a48c0013452 normal130 (by decide) (by decide) (by decide +kernel)
private theorem normal132 : (hankel (cubeSeq (ZMod 53)) 132).det ≠ 0 :=
  certified 0x40000034000000000000000040000000001000000000040000034000000000000000040000000001000000000040000034000000000000000000000000000000000034034000000040000000000000034000000000d00000000034000000040000 normal131 (by decide) (by decide) (by decide +kernel)
private theorem normal133 : (hankel (cubeSeq (ZMod 53)) 133).det ≠ 0 :=
  certified 0x4cc5cc1d00c42d00000000000004cc1000000133040000004cc1d00c42d00000000000004cc1000000133040000004cc1d00c42d00000000000000000000000000000d00c42c02d01004cc1000000000000c42d000000310b4000000c42d01004cc1 normal132 (by decide) (by decide) (by decide +kernel)
private theorem normal135 : (hankel (cubeSeq (ZMod 53)) 135).det ≠ 0 :=
  certified 0x1b00001b01a68000068000000000000001b0000000006c000000001a68000068000000000000001b0000000006c000000001a6800006800000000000000000000000000346800006806db00001b00000000000000068000000001a0000000006db00001b normal133 (by decide) (by decide) (by decide +kernel)
private theorem normal147 : (hankel (cubeSeq (ZMod 53)) 147).det ≠ 0 :=
  certified 0x34000000000000000000000000000000000000000000034000000000000000000000000000000000000000000034000000000000000000000000000000000034000000000040000000000000000000000000000000000000000000040000000000 normal135 (by decide) (by decide) (by decide +kernel)
private theorem normal149 : (hankel (cubeSeq (ZMod 53)) 149).det ≠ 0 :=
  certified 0x41000001034d00000d00000000000000000000000000000000000034d00000d00000000000000000000000000000000000034d00000d00000034000000000000000000034d00000d00041000001000000000000000000000000000000000000041000001 normal147 (by decide) (by decide) (by decide +kernel)
private theorem normal150 : (hankel (cubeSeq (ZMod 53)) 150).det ≠ 0 :=
  certified 0x34040000000000000000000001001d01000d00d01d00000000000000000000000000000000000000d00d01d00000000000000000000000000000000000000d00d01d00034074000000000000000000000d00d01d00001001d01000000000000000000000000000000000000001001d01 normal149 (by decide) (by decide) (by decide +kernel)
private theorem normal151 : (hankel (cubeSeq (ZMod 53)) 151).det ≠ 0 :=
  certified 0x40000000034000000000000000000000000000000000000000000034000000000000000000000000000000000000000000034000000d00000000000000000000000000034000000000040000000000000000000000000000000000000000000040000 normal150 (by decide) (by decide) (by decide +kernel)
private theorem normal152 : (hankel (cubeSeq (ZMod 53)) 152).det ≠ 0 :=
  certified 0xd01d00000000000000000000000034074000000074040000000000000000000000000000000000000000074040000000000000000000000000000000000000000074074001d01000000000000000000000000074040000034074000000000000000000000000000000000000000034074 normal151 (by decide) (by decide) (by decide +kernel)
private theorem normal155 : (hankel (cubeSeq (ZMod 53)) 155).det ≠ 0 :=
  certified 0x40000d00000000000000000000000000034000000000040000000000000000000000000000000000000000000040000000000000000000000000000000000000000000034000001000000000000000000000000000040000000034000000000000000000000000000000000000000000034 normal152 (by decide) (by decide) (by decide +kernel)
private theorem normal156 : (hankel (cubeSeq (ZMod 53)) 156).det ≠ 0 :=
  certified 0x34000000000000000000000000000d00000000001000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000040000000000000000000000000001000000000d00000000000000000000000000000000000000000000d00000 normal155 (by decide) (by decide) (by decide +kernel)
private theorem normal159 : (hankel (cubeSeq (ZMod 53)) 159).det ≠ 0 :=
  certified 0x1000000d00000000000000000000034000034000040000040000000000000000000000000000000000000040000040000000000000000000000000000000000000000000000000001000000000000000000000040000040034000034000000000000000000000000000000000000034000034 normal156 (by decide) (by decide) (by decide +kernel)
private theorem normal171 : (hankel (cubeSeq (ZMod 53)) 171).det ≠ 0 :=
  certified 0xd00000000001000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000d00000000000000000000000000000000000000000000d00000000000 normal159 (by decide) (by decide) (by decide +kernel)
private theorem normal173 : (hankel (cubeSeq (ZMod 53)) 173).det ≠ 0 :=
  certified 0x1000000d00034000034000000000000000000000000040041000000000d00000d00000000000000001000000000040000034000d00000d00000000000000000000000000000000000000000000000000000000000000000000034034d00000000001000001000000000000000d00000000034000000040001000001 normal171 (by decide) (by decide) (by decide +kernel)
private theorem normal174 : (hankel (cubeSeq (ZMod 53)) 174).det ≠ 0 :=
  certified 0x34040000001d01000d01034074034074000000000000000000000074040001000001d01d00d01d00000000000001d01000000074040034040d01d00d01d00000000000000000000000000000000000000000000000000000000000000000034074000d00000d01d01001d01000000000000d01d00000034074000074001d01001d01 normal173 (by decide) (by decide) (by decide +kernel)
private theorem normal175 : (hankel (cubeSeq (ZMod 53)) 175).det ≠ 0 :=
  certified 0x40000034001000000d00000000000000000000000001000000000000040000034000000000000000040000000001000000d00040000034000000000000000000000000000000000000000000000000000000000000000000000d00000000000034000000040000000000000034000000000d00000001034000000040000 normal174 (by decide) (by decide) (by decide +kernel)
private theorem normal177 : (hankel (cubeSeq (ZMod 53)) 177).det ≠ 0 :=
  certified 0x74040001001d01d00001034073034074000000000000000000040074040001001001d01cc0d01d00000000001001d01000040074074000040d01cc0d01d00000000000000000000000000000000000000000000000000000000000000034034074000d00d00d01d02001d01000000000d00d01d00034034074040034001d02001d01 normal175 (by decide) (by decide) (by decide +kernel)
private theorem normal178 : (hankel (cubeSeq (ZMod 53)) 178).det ≠ 0 :=
  certified 0x1d01000000034040034074d01000d01000000000000000040000001d01000000000d34040034040000001000000074040000000d01000d01d34040034040000000000000000000000000000000000000000000000000000000000034000000d01d00000000001074000074000000d00000034074000000001d00001d01074000074 normal177 (by decide) (by decide) (by decide +kernel)
private theorem normal179 : (hankel (cubeSeq (ZMod 53)) 179).det ≠ 0 :=
  certified 0x80d00002cc20340340330c0d33073cc4000cc3000000000000001080d00002cc2034034033cf31000330c00000420340000b3080d00d00cc3034cc1cf31000330c0000000000000000000000000000000000000000000000000000000000d33001000cc2cc00400400820b10000b2000034cc00400330b3001001002c80042d020b10000b2 normal178 (by decide) (by decide) (by decide +kernel)
private theorem normal180 : (hankel (cubeSeq (ZMod 53)) 180).det ≠ 0 :=
  certified 0x2a83434009e5e0d0dd0dcd84f42d6ad364603361300000000000006a83434009e5e0d0dd0dcd84d9180cd84c0001aa0d0d002797834374373613d0b5ab4d9180cd84c00000000000000000000000000000000000000000000000000000000342d50680335de541a01a0276272f002762000d0b541a00cd779506806809d881a9f2a272f002762 normal179 (by decide) (by decide) (by decide +kernel)
private theorem normal181 : (hankel (cubeSeq (ZMod 53)) 181).det ≠ 0 :=
  certified 0xac5d0c7428158b431c31b5965cac6cb972b0cd6598000000000001ac5d0c7428158b431c31b5965cac3359660006b17431d0a0562d0c70c6d65972b1b2e5cac33596600000000000000000000000000000000000000000000000000000000d0ac01a58cd581306966969f7deac509f7dd0342b00696335604c1a59a5a7df7ab1091deac509f7dd normal180 (by decide) (by decide) (by decide +kernel)
private theorem normal182 : (hankel (cubeSeq (ZMod 53)) 182).det ≠ 0 :=
  certified 0x7b40957b4d7cd0655a655f75fb491c87ad247a5d834000000000047b40957b4d7cd0655a655f75fb491e9760d011ed0255ed35f3419569957dd7ed24721eb491e9760d00000000000000000000000000000000000000000000000000000034b88010788a16a3441f3e0598588b2e318541d2e20041e2285a8d107cf81661622cbad5c8b2e318541 normal181 (by decide) (by decide) (by decide +kernel)
private theorem normal183 : (hankel (cubeSeq (ZMod 53)) 183).det ≠ 0 :=
  certified 0xb5a0ab4ab7885567d1cc419f129a2b925028ae494584c000000001b5a0ab4ab7885567d1cc419f129a2b92516136d682ad2ade21559f4731067c4a68ae4940a2b925161300000000000000000000000000000000000000000000000000000d086f32a3297b607d6902c6f5b130d29143052821bcca8ca5ed81f5a40b1bd6c4c34a45000d291430529 normal182 (by decide) (by decide) (by decide +kernel)
private theorem normal184 : (hankel (cubeSeq (ZMod 53)) 184).det ≠ 0 :=
  certified 0xc30771e7085cc9e5a50c50949261ba578056e95e015b2900000004c30771e7085cc9e5a50c50949261ba578056d00c1dc79c21732796943142524986e95e015ba578056ca40000000000000000000000000000000000000000000000000034a69b995d9b5ea4e40c944950b2c507417020200a6e65766d7a939032512542cb141d05c080741702024c normal183 (by decide) (by decide) (by decide +kernel)
private theorem normal185 : (hankel (cubeSeq (ZMod 53)) 185).det ≠ 0 :=
  certified 0x4272e8be81c011946d195a917de9864510276114409d70520000014272e8be81c011946d195a917de98645102761110ba2fa07004651b4656a45f7a61914409d84510275c1480000000000000000000000000000000000000000000000000d253aa34636e03172422f80b9165cfbe490039d931a8d18db80c5c908be02e45973ef92400e76490039ed23 normal184 (by decide) (by decide) (by decide +kernel)
private theorem normal186 : (hankel (cubeSeq (ZMod 53)) 186).det ≠ 0 :=
  certified 0x95064ef91a2c6404085745a1655dbd7aa451002a9143ec59e0000495064ef91a2c6404085745a1655dbd7aa451002a913be468b19010215d16859576f5ea914400aa450fb16780000000000000000000000000000000000000000000000034b21be21916eabe5c73c18c0d7e060678b4619402d188645baaf971cf063035f81819e2d186500b4619897d7 normal185 (by decide) (by decide) (by decide +kernel)
private theorem normal187 : (hankel (cubeSeq (ZMod 53)) 187).det ≠ 0 :=
  certified 0x813030cc58db5b04633461dbc8c02794c28fd2f80a3f33cd294001813030cc58db5b04633461dbc8c02794c28fd2f80a3f31636d6c118cd1876f23009e530a3f4be028fccf34a500000000000000000000000000000000000000000000000d15880142c1269f1644a8bee683a40390a6b981195ae60b049a7c5912a2fb9a0e900e429ae604656b9829a8ae1 normal186 (by decide) (by decide) (by decide +kernel)
private theorem normal188 : (hankel (cubeSeq (ZMod 53)) 188).det ≠ 0 :=
  certified 0x225011e25f409c8c03eb316401790a65a109e81135679d7d148050625011e25f409c8c03eb316401790a65a109e81135679d7d0272300facc59005e429968427a044d59e75f45201400000000000000000000000000000000000000000000344e1d2e4de0736520262a97e5d1794c40d94e3718a038e781cd948098aa5f9745e531036538dc6280e39e061570 normal187 (by decide) (by decide) (by decide +kernel)
private theorem normal189 : (hankel (cubeSeq (ZMod 53)) 189).det ≠ 0 :=
  certified 0xa57a41785be78221185a64e01747a41a67227ad45b85d12f9e0d00a57a41785be78221185a64e01747a41a67227ad45b85d12f9e0884616993805d1e90699c89eb516e1744be7834d00000000000000000000000000000000000000000000d0c78cd17c063954f175f3e257005746f3d94d722469463118e553c5d7cf895c015d1bcf6535c891a518c46395041 normal188 (by decide) (by decide) (by decide +kernel)
private theorem normal190 : (hankel (cubeSeq (ZMod 53)) 190).det ≠ 0 :=
  certified 0xcd1d2c075b7cf17280f568d09c859468c27a39721da159cdf3c5ca4d1d2c075b7cf17280f568d09c859468c27a39721da159cdf3c5ca03d5a342721651a309e8e5c876856737cf171600000000000000000000000000000000000000000034a4162a0186969b00d59a0341b03c10bd2cd74900ee6f07025a6c0356680d06c0f042f4b35d2403b9bc1c0969b011d normal189 (by decide) (by decide) (by decide +kernel)
private theorem normal191 : (hankel (cubeSeq (ZMod 53)) 191).det ≠ 0 :=
  certified 0x1325a10d1494cc0c937658120525899e0563aa67957c3361d330324dd5a10d1494cc0c937658120525899e0563aa67957c3361d330324dd9604814962678158ea99e55f0cd874cc0c4f800000000000000000000000000000000000000000d310df5329238420038984158f48dfb0e56048b3d7816ca85010800e2610563d237ec3958122cf5e05b2a14042004995 normal190 (by decide) (by decide) (by decide +kernel)
private theorem normal192 : (hankel (cubeSeq (ZMod 53)) 192).det ≠ 0 :=
  certified 0x2e5ef9db32bc994e87e2ca75c6ade89952470987008ebb3708713a1f8b29db32bc994e87e2ca75c6ade89952470987008ebb3708713a1f8b29d71ab7a265491c261c023aecdc21c4e798b0c00000000000000000000000000000000000000341de18e6a92837223564c339ebca5d3721459b141739c7099b5988d5930ce7af2974dc85166c505ce71c266d66238fab2 normal191 (by decide) (by decide) (by decide +kernel)
private theorem normal193 : (hankel (cubeSeq (ZMod 53)) 193).det ≠ 0 :=
  certified 0x6648e55c567122f3e7c9781717100d526213d1e8b284c4e72b1a8f9f25e05c567122f3e7c9781717100d526213d1e8b284c4e72b1a8f9f25e05c5c403549884f47a2ca13139cac6a38e3a9c00000000000000000000000000000000000000d1c45241ec1c12d1a63837957b0100a213ed8815d30d4a623ab10b98e0de55ec0402884fb620574c352988eac42e79e7305 normal192 (by decide) (by decide) (by decide +kernel)
private theorem normal194 : (hankel (cubeSeq (ZMod 53)) 194).det ≠ 0 :=
  certified 0x2ca29b41a1135f5b3398ba57a844d1979e06ae516bb43cda3290e6ce62e95ea1135f5b3398ba57a844d1979e06ae516bb43cda3290e6ce62e95ea113465e781ab945aed0f368ca439a5e516d74000000000000000000000000000000000003424d308d0d92859f0a7747417364a2f78e55b1e17c7066a0d0d19da9dd1d05cd928bde3956c785f1c19a83434676de430218 normal193 (by decide) (by decide) (by decide +kernel)
private theorem normal195 : (hankel (cubeSeq (ZMod 53)) 195).det ≠ 0 :=
  certified 0x44890968e82235435668fb145e088d51ecc11935801d352ed2d0877da3ec51782235435668fb145e088d51ecc11935801d352ed2d0877da3ec5178223547b30464d60074d4bb4b4218e4a08ef240000000000000000000000000000000000d24b51b1b9d54e88687db98985e553a215c2d2f89f02e8a11c1233b966e62617954e88570b4be27c0ba2847048cef9e35521ac normal194 (by decide) (by decide) (by decide +kernel)
private theorem normal196 : (hankel (cubeSeq (ZMod 53)) 196).det ≠ 0 :=
  certified 0x118203c3883a3238f51f8652ca2a8c8e3d49201cd0c52b18eece45f19a194b28aa3238f51f8652ca2a8c8e3d49201cd0c52b18eece45f19a194b28aa3238f52480734314ac63bb391680605621d1c0000000000000000000000000000000034915566c93c8d0e79a159442aaeb3439e685156ea32c2b1121c245e10f510aabacd0e79a1455ba8cb0ac44870917d5bf47ed62e normal195 (by decide) (by decide) (by decide +kernel)
private theorem normal197 : (hankel (cubeSeq (ZMod 53)) 197).det ≠ 0 :=
  certified 0x80379954e4dfa8c7d87db99072d4aa31f61f6ec1310e036681a65a9843a641cb52a8c7d87db99072d4aa31f61f6ec1310e036681a65a9843a641cb52a8c7d87dbb04c4380d9a069964606537039aa00000000000000000000000000000000d15c977209e258ba5675668f9592232e959d59a2711325683d56dc6cfc673e56488cba56756689c44c95a0f55b71cbf44281676cd normal196 (by decide) (by decide) (by decide +kernel)
private theorem normal198 : (hankel (cubeSeq (ZMod 53)) 198).det ≠ 0 :=
  certified 0x244f79109e8d47632a36c735722251d8ca8db1cd40c0811df7c67df35a1cd5c88947632a36c735722251d8ca8db1cd40c0811df7c67df35a1cd5c88947632a36c73503020477df19e7712dec557f4000000000000000000000000000000034ce49979335d28584ab49aba87ad4e1612ad26aea25a73d2e596bd65a86eea1eb538584ab49aba8969cf4b965af5d812a5c4816040 normal197 (by decide) (by decide) (by decide +kernel)
private theorem normal199 : (hankel (cubeSeq (ZMod 53)) 199).det ≠ 0 :=
  certified 0xb895dfbee28b0408dbac554854e7857636eb15521538d340b5abd90af61995539e15d8dbac554854e7857636eb15521538d340b5abd90af61995539e15d8dbac554854e34d02d6af609981beb7044c4740000000000000000000000000000d07b1e5861ebab401268ac20b609d7c1849a2b082d827a280086c673319d7108275f061268ac20b609e8a0021b19db0fd06299c62c58 normal198 (by decide) (by decide) (by decide +kernel)
private theorem normal200 : (hankel (cubeSeq (ZMod 53)) 200).det ≠ 0 :=
  certified 0x2988b2c7a62bd142f9e3211111b30a232278c844446cc28563c5f29db49a177ecc288c89e3211111b30a232278c844446cc28563c5f29db49a177ecc288c89e3211111b30a158f17c9a4bcdd42b2815d3380000000000000000000000000034313aaab8c4c692518e4ad93190914d4ad392b64c642453604845ab608b0d796245352b4e4ad93190914d812116b0ca826252abd1e8a7 normal199 (by decide) (by decide) (by decide +kernel)
private theorem normal201 : (hankel (cubeSeq (ZMod 53)) 201).det ≠ 0 :=
  certified 0x9093272d5570b43a50b5d818395129a6c66d76060e544a69b21a9e30199c251784a69b19b5d818395129a6c66d76060e544a69b21a9e30199c251784a69b19b5d818395129a6c86a75db5aab3c49271983240000000000000000000000000d11b293aa820148c8c94861576783130c25c21855d9e0c4c30950b5e9d0f66c917c4c30970861576783130c2542d86086cb084b2c10fcac normal200 (by decide) (by decide) (by decide +kernel)
private theorem normal202 : (hankel (cubeSeq (ZMod 53)) 202).det ≠ 0 :=
  certified 0x74af916c7400532fa2fa46bef2d2a401a91a91afbcb4a9006a461a61d2aa318c7a9006a46a46bef2d2a401a91a91afbcb4a9006a461a61d2aa318c7a9006a46a46bef2d2a401a91857ea60634a35e929301300000000000000000000000034ba31917c4040c2918d18cbc61aa8cc02f32f32f186aa3300bccbef3ee8cb4afa57300bccbccbc61aa8cc02f32fc162ddbe8ae85d1329d29 normal201 (by decide) (by decide) (by decide +kernel)
private theorem normal203 : (hankel (cubeSeq (ZMod 53)) 203).det ≠ 0 :=
  certified 0x2d841a21518b524183be471022a4d65c52f2b5c408a9359714bcae9ddbe70c7c967d714bcad71022a4d65c52f2b5c408a9359714bcae9ddbe70c7c967d714bcad71022a4d65c52f2b5c15f3709ec2cba34203240000000000000000000000d2a7656ed82faa146fc8645996d2e27dec2a0c8665b4b89f7b0a831ce6063b2b837d67b0a8321996d2e27dec2a0c86705a814e26aa8d06dcac normal202 (by decide) (by decide) (by decide +kernel)
private theorem normal204 : (hankel (cubeSeq (ZMod 53)) 204).det ≠ 0 :=
  certified 0x1faa4c6c2ca9923227efcf48119048c76c53188a04641231db14c64c540a8928a588a9b14c6228119048c76c53188a04641231db14c64c540a8928a588a9b14c6228119048c76c53188a046e4b4025adeb9b49a8c000000000000000000003458b44426aacf8e94d6182055911c52b9ac297535644714ae6b0a5ca6000bb2badfb4b6b0a5d4d5911c52b9ac297535641e304040a5c76a36d2 normal203 (by decide) (by decide) (by decide +kernel)
private theorem normal205 : (hankel (cubeSeq (ZMod 53)) 205).det ≠ 0 :=
  certified 0xa46a8286909b4ab4b478da5579788c94b09cc2835e5e23252c27317134d938f6a0be40c2730a0d79788c94b09cc2835e5e23252c27317134d938f6a0be40c2730a0d79788c94b09cc2835e5e26d815dba60f38f4b40000000000000000000d0cbcbcd43336a32a3057a0c817793a50ab36453685de4e942acd91198a272799b546472cd914da17793a50ab36453685de4da7706073f2092048 normal204 (by decide) (by decide) (by decide +kernel)
private theorem normal206 : (hankel (cubeSeq (ZMod 53)) 206).det ≠ 0 :=
  certified 0xf6593619649abc27ac521e4aaad47257b23dcbb232b51c95ec8f7485a50c03147b000950f72ec8cad47257b23dcbb232b51c95ec8f7485a50c03147b000950f72ec8cad47257b23dcbb232b51c96d1455de2944205c000000000000000003499c72851044f28538ac2d5e32ca8594170e66470e92a16505c3998b5f432029857140b219991c3a4a8594170e66470e92a1650230c1e5eb86555e normal205 (by decide) (by decide) (by decide +kernel)
private theorem normal207 : (hankel (cubeSeq (ZMod 53)) 207).det ≠ 0 :=
  certified 0xc3099bca92a263709042290cb011e9b3628140848b447a6cd8a060e4291ce856885c3e394502122d11e9b3628140848b447a6cd8a060e4291ce856885c3e394502122d11e9b3628140848b447a6cd8ba86a40eb44bc80000000000000000d32cb3706ad12ec499b34ceb9431715cf09d370014b48c573c274dbf246b902360354666490c0052d2315cf09d370014b48c573c274735b4722a4a83 normal206 (by decide) (by decide) (by decide +kernel)
private theorem normal208 : (hankel (cubeSeq (ZMod 53)) 208).det ≠ 0 :=
  certified 0xc4d787265c32c41dcd83da4978db46381781b9eb2ec3118e05e0733262609a8ab0ec042e9327acbb0c46381781b9eb2ec3118e05e0733262609a8ab0ec042e9327acbb0c46381781b9eb2ec3118e05e070d472359a49980000000000000034a627940dc6692656027666e37926a449579568e2aa26991255e5590ac4ddb0bac99c5c6a32938aa89a6449579568e2aa26991255e559a240e870cb0f normal207 (by decide) (by decide) (by decide +kernel)
private theorem normal209 : (hankel (cubeSeq (ZMod 53)) 209).det ≠ 0 :=
  certified 0xe978435078016dc2f64f56cc002d97cd2eac8e630c148df34bab344c67487320d422b8b946618c305237cd2eac8e630c148df34bab344c67487320d422b8b946618c305237cd2eac8e630c148df34bab344cb03840c09280000000000000d32317c6895703020519c9a024502a716a2a2c39dd1458525a8a8b0a4a5c0540ada254c7a90bdd745161496a2a2c39dd1458525a8a8b0a4a49c94005b2b normal208 (by decide) (by decide) (by decide +kernel)
private theorem normal210 : (hankel (cubeSeq (ZMod 53)) 210).det ≠ 0 :=
  certified 0x32c824db88c49354c8315f11499f10db55eb70c210d476b9d57adc6d7859c36339f134861a723b4351dae755eb70c210d476b9d57adc6d7859c36339f134861a723b4351dae755eb70c210d476b9d57adc6d7859e8be28683000000000000340c3ce2693a638a0a5511e130b0e1326a05c814553285828e817204217c0ec9d08e128b5d6d9488ca160a3a05c814553285828e817204217c0e3464d4369 normal209 (by decide) (by decide) (by decide +kernel)
private theorem normal211 : (hankel (cubeSeq (ZMod 53)) 211).det ≠ 0 :=
  certified 0x4b4717b0d8a63f191d65a970c0e3592a8c24317cd0012250a7090da72b17256c9a2a0c515911c4440489429c24317cd0012250a7090da72b17256c9a2a0c515911c4440489429c24317cd0012250a7090da72b172569c5946040000000000d23059789a133e611161c6d01459e872b3454697829408ec94c151a0c0c97ac7c36eb54491f92ec64023b253054697829408ec94c151a0c0c97ac7cec10bf4 normal210 (by decide) (by decide) (by decide +kernel)
private theorem normal212 : (hankel (cubeSeq (ZMod 53)) 212).det ≠ 0 :=
  certified 0x1bcdf59f3ebc6c19e11a4566130b29e732334410d48c1a688dc4d15f2f18a50182684e38e53432136869a237134410d48c1a688dc4d15f2f18a50182684e38e53432136869a237134410d48c1a688dc4d15f2f18a5018274c0138000000003468259f5a628426f5f16e47dd8b30ce3a94a8c71a23a6f3d3a04a305aa11340076c362492428cad89bbcf4e8128c71a23a6f3d3a04a305aa11340076c045d27 normal211 (by decide) (by decide) (by decide +kernel)
private theorem normal213 : (hankel (cubeSeq (ZMod 53)) 213).det ≠ 0 :=
  certified 0xaa98c0e4880cee323d1976ad0d2449748d419e20c81bbf042d487832cac79e750acb4cec5651376a66fc10b5219e20c81bbf042d487832cac79e750acb4cec5651376a66fc10b5219e20c81bbf042d487832cac79e750acb44acc0000000d332cfa724530021e94817182c1a2cc5005286f5eda55686165223b950c32575d894aaa29c47e18982dc1859488ef5eda55686165223b950c32575d894aaa4ac2 normal212 (by decide) (by decide) (by decide +kernel)
private theorem normal214 : (hankel (cubeSeq (ZMod 53)) 214).det ≠ 0 :=
  certified 0x33ac705628ad0e48ca5730469d5569efad3a5d45e43022f50758814f517c5e11e1a46910eb8c00e1cdc5941d620445e43022f50758814f517c5e11e1a46910eb8c00e1cdc5941d620445e43022f50758814f517c5e11e1a46910d470000003408abb47ebac19e3a4c7a9c5b6207ce18a88c6245e516d1a1b9fb709a17845f15ef45b93229203250265f86e7edc645e516d1a1b9fb709a17845f15ef45b932859 normal213 (by decide) (by decide) (by decide +kernel)
private theorem normal215 : (hankel (cubeSeq (ZMod 53)) 215).det ≠ 0 :=
  certified 0xb2c9734dab1ad5065c6e96e99998451a13174974350975ec9c497a1a02b5aa4ee4a76185ae6cf6ec7d61b27125a674350975ec9c497a1a02b5aa4ee4a76185ae6cf6ec7d61b27125a674350975ec9c497a1a02b5aa4ee4a76185ae740000d330c37a8a0b10a8344041d01cf70fc616f1118b18ca1b185c366378d6c029f2e21e339d75f1da99a2567ef0d98df3d8ca1b185c366378d6c029f2e21e339d75f1d8 normal214 (by decide) (by decide) (by decide +kernel)
private theorem normal216 : (hankel (cubeSeq (ZMod 53)) 216).det ≠ 0 :=
  certified 0x223ee40331d82631d92db9ba81b62aa59b406216bac84d11ce4c92e5424616764b845685087732de71bb8565324a0c1ac84d11ce4c92e5424616764b845685087732de71bb8565324a0c1ac84d11ce4c92e5424616764b845685087732c00344e61e5ca96153e961120768bd084cb40f0744f028ab6292e9e2b2a42545d7d8447c60361b580aa5d9687c1c8acaf2d0ab6292e9e2b2a42545d7d8447c60361b580aa normal215 (by decide) (by decide) (by decide +kernel)
private theorem normal217 : (hankel (cubeSeq (ZMod 53)) 217).det ≠ 0 :=
  certified 0xb617407139903742e2824c562c49f125c709d010cf3eec4bc6838011a44f54fc4c00d2e61402eb680cf15a734ed0cba93eec4bc6838011a44f54fc4c00d2e61402eb680cf15a734ed0cba93eec4bc6838011a44f54fc4c00d2e61402eb680d0851801988f96806a4d54447eac4e12c659b01d329a61c4a843670316e49a0984a40a2a3f002a29b00211f3a89c1a473261c4a843670316e49a0984a40a2a3f002a29b normal216 (by decide) (by decide) (by decide +kernel)
private theorem normal218 : (hankel (cubeSeq (ZMod 53)) 218).det ≠ 0 :=
  certified 0x337ea41859904c304421743bc7a4354c02b447a64cd0bc437153212f6941526a6ca0248286c483216800152005c3c707eabc437153212f6941526a6ca0248286c483216800152005c3c707eabc437153212f6941526a6ca0248286c483216b40962e575f734a69c65518c86b8cca0a402a4b8c442946c681210f119b8708db3c356cb6bbc4b6951b00082d01ec841562c6c681210f119b8708db3c356cb6bbc4b6951b normal217 (by decide) (by decide) (by decide +kernel)
private theorem normal219 : (hankel (cubeSeq (ZMod 53)) 219).det ≠ 0 :=
  certified 0xa25a615176057708e9d175157e431e16617222064aac2a9c5ef021b27a4524cd1c5f03e098b65eae3a000009634c408066aa9c5ef021b27a4524cd1c5f03e098b65eae3a000009634c408066aa9c5ef021b27a4524cd1c5f03e098b65eae39cd40c52179dc181523017a18164695f03f00ed55cacaccb65e18050938cc2ca4165e16654fa9c5ca48d0000104a2c7301c2cb65e18050938cc2ca4165e16654fa9c5ca48d normal218 (by decide) (by decide) (by decide +kernel)
private theorem normal220 : (hankel (cubeSeq (ZMod 53)) 220).det ≠ 0 :=
  certified 0x2020b8803a83830505285c582f0ccb8238d2a59c4733792349ab25d40f28cc4405edce7a2b528b0b0e39800000046b09c1303349ab25d40f28cc4405edce7a2b528b0b0e39800000046b09c1303349ab25d40f28cc4405edce7a2b528b0b0e21ada93027367cb496135ec151b2a47ce7a2b40ec590978e8b0b0de8720d2a6401e20238d2a1349ab248f000000c5b14ed29ca8b0b0de8720d2a6401e20238d2a1349ab248f normal219 (by decide) (by decide) (by decide +kernel)
private theorem normal221 : (hankel (cubeSeq (ZMod 53)) 221).det ≠ 0 :=
  certified 0x5237c434991e006cf48911ec9cec91918b712c53e969e024c6fa9f257669354c9abf074812ac0418b5cb7c00000004ef9402cec6fa9f257669354c9abf074812ac0418b5cb7c00000004ef9402cec6fa9f257669354c9abf074812ac0418b5acc56c68b115c0bc205392e24e9c391174812ac2631b5c044418b5ac79c3288436c6158b712c5c6fa9ea9600000002219002a9c418b5ac79c3288436c6158b712c5c6fa9ea96 normal220 (by decide) (by decide) (by decide +kernel)
private theorem normal222 : (hankel (cubeSeq (ZMod 53)) 222).det ≠ 0 :=
  certified 0x1f674a9245d3e24ca3007c46496af9074086f3d288a263068f89a0a1698ca928114fb4cb5a0813536f4cf47000000000085ee66b89a0a1698ca928114fb4cb5a0813536f4cf47000000000085ee66b89a0a1698ca928114fb4cb5a0813536f351b74b8e46264e2ae9016c5cb1b191ba5b5a0813534dd15b9936f351b74332bd30988a486f3d2889a042059000000000b5e1dc2936f351b74332bd30988a486f3d2889a042059 normal221 (by decide) (by decide) (by decide +kernel)
private theorem normal223 : (hankel (cubeSeq (ZMod 53)) 223).det ≠ 0 :=
  certified 0x4491859c67e08342700e509aa47824cdcb649f3a5bcec8565a0ced48e7809e6c1e43204d44e08c682274c1d140000000000811ce5ced48e7809e6c1e43204d44e08c682274c1d140000000000811ce5ced48e7809e6c1e43204d44e08c6822239d700ebd655506c1724336ccb9544264844e08c6822547df5422239d700e3c55e50f4a249f3a5bcec0456300000000000159024022239d700e3c55e50f4a249f3a5bcec045630 normal222 (by decide) (by decide) (by decide +kernel)
private theorem normal224 : (hankel (cubeSeq (ZMod 53)) 224).det ≠ 0 :=
  certified 0x155188cabe48ec39c23106c4174981c78d7badba993419415840d1e9647431be45daa63c5520731106f8704533800000000000298db1e9647431be45daa63c5520731106f8704533800000000000298db1e9647431be45daa63c5520731106e31cba510645226766d1342657a376eb9278720731106f870765a2e31cba510645e6cc48482dba99341941648a70000000000003126ae31cba510645e6cc48482dba99341941648a7 normal223 (by decide) (by decide) (by decide +kernel)
private theorem normal225 : (hankel (cubeSeq (ZMod 53)) 225).det ≠ 0 :=
  certified 0x6452e38505097abac798341bc1b32ebf2ad038155b1a07962814d209b56415f5097a5b89318d206af5577ebd1c980000000000000bc309b56415f5097a5b89318d206af5577ebd1c980000000000000bc309b56415f5097a5b89318d206af5336a04705a1b1728ab8fca56856a91c60ca967d206af5577ebd228f36a04705a1b17407b2974155b1a079628164f000000000000006cb36a04705a1b17407b2974155b1a079628164f normal224 (by decide) (by decide) (by decide +kernel)
private theorem normal226 : (hankel (cubeSeq (ZMod 53)) 226).det ≠ 0 :=
  certified 0x1b725be69afd1e18186659881b25c21520714819bb8d68f6acb49c0505c9ef85fd1e181067c8a687a1b99b248b0540000000000000001505c9ef85fd1e181067c8a687a1b99b248b0540000000000000001505c9ef85fd1e181067c8a687a1a2f464e1945815efd143df7556ac66d82dbb0b6f687a1b99b248b05c3464e1945815efd34383adbb8d68f6acb49c2500000000000000083464e1945815efd34383adbb8d68f6acb49c25 normal225 (by decide) (by decide) (by decide +kernel)
private theorem normal227 : (hankel (cubeSeq (ZMod 53)) 227).det ≠ 0 :=
  certified 0x16f3135e8a9c4286dd4e0b123cdcebb9959a5adc8c094bd4042227c473557da9a34286dd4ed331a73846874ced384b800000000000000003557da9a34286dd4ed331a73846874ced384b800000000000000003557da9a34286dd4ed331a738019e88166cf4a535a6225498e6a0228771f6df203a73846874ced384ba88166cf4a535a62222910c094bd4042227c470000000000000000288166cf4a535a62222910c094bd4042227c47 normal226 (by decide) (by decide) (by decide +kernel)
private theorem normal228 : (hankel (cubeSeq (ZMod 53)) 228).det ≠ 0 :=
  certified 0x1f7957c79019e453122b547c1db58b90b57168a6c182a6244c585b450ab00c706a5a53122b5471c4ccc4e4a5fc08c3328000000000000000000c706a5a53122b5471c4ccc4e4a5fc08c3328000000000000000000c706a5a53122b5471c4ccba46500a59bcc6e112d2a0b856087479487b034c26fccc4e4a5fc08c33280a59bcc6e112d2a0baec42a6244c585b450ab000000000000000000a59bcc6e112d2a0baec42a6244c585b450ab normal227 (by decide) (by decide) (by decide +kernel)
private theorem normal229 : (hankel (cubeSeq (ZMod 53)) 229).det ≠ 0 :=
  certified 0x8620f22482c028524c78f1c82cd9dd315aa0bac41c7660265f4b2d09d3b300035d60324c78f1c82da3c03de04923362708000000000000000000035d60324c78f1c82da3c03de04923362708000000000000000000035d60324c78f1c82da39489b10002861dcaca579aeb6aa0e62980b5472656583c03de04923362708002861dcaca579aeb6a6e60265f4b2d09d3b300000000000000000002861dcaca579aeb6a6e60265f4b2d09d3b3 normal228 (by decide) (by decide) (by decide +kernel)
private theorem normal230 : (hankel (cubeSeq (ZMod 53)) 230).det ≠ 0 :=
  certified 0xa99f72a71b69f2ce3695e35db69f6085812c5b43b2c6d0cd69c165a6e393000000dbc93695e35db69f9427ced1c6da49114000000000000000000000dbc93695e35db69f9427ced1c6da49114000000000000000000000dbc93695e35db69e6d1027280000a06b2831e49e69b59db5fd2ac08c8925a9427ced1c6da491140000a06b2831e49e69b590cd69c165a6e3930000000000000000000000a06b2831e49e69b590cd69c165a6e3930 normal229 (by decide) (by decide) (by decide +kernel)
private theorem normal231 : (hankel (cubeSeq (ZMod 53)) 231).det ≠ 0 :=
  certified 0x74f7c0a625019510493b04a58419510679093424444285f49707ad87442474d0000007963b04a5841951050157214065458a000000000000000000000007963b04a5841951050157214065458a000000000000000000000007963b04a58419299e61636c00000177e7163414d10934391b28ce4c6535e050157214065458a000000177e7163414d109349707ad87442474d0000000000000000000000177e7163414d109349707ad87442474d normal230 (by decide) (by decide) (by decide +kernel)
private theorem normal232 : (hankel (cubeSeq (ZMod 53)) 232).det ≠ 0 :=
  certified 0x18aeb1b324e727960d06062114d27960d067e39984e6b8fc81bed46264e41505800000001e062114d27960d062244dc9e583474000000000000000000000001e062114d27960d062244dc9e583474000000000000000000000001e062114d2636a24029b1400000005f44f1841390541bd648f7623c7983d062244dc9e58347400000005f44f1841390541bed46264e4150580000000000000000000000005f44f1841390541bed46264e415058 normal231 (by decide) (by decide) (by decide +kernel)
private theorem normal233 : (hankel (cubeSeq (ZMod 53)) 233).det ≠ 0 :=
  certified 0x79b1e50f26d970514fd1c68169d00514fd1c69b6c27452af34165b019670c2605900000000068169d00514fd1c68071c1453f470000000000000000000000000068169d00514fd1c68071c1453f470000000000000000000000000068169dd1c7c83d975a0c000000001bd1b600c3098165b69acd8c2b1a8d1c68071c1453f470000000001bd1b600c3098165b019670c2605900000000000000000000000001bd1b600c3098165b019670c26059 normal232 (by decide) (by decide) (by decide +kernel)
private theorem normal234 : (hankel (cubeSeq (ZMod 53)) 234).det ≠ 0 :=
  certified 0x2504b128e38d351624048001290151624048001206556a7c90230008e285fb008c00000000000129015162404800124d45890120000000000000000000000000000129015162404800124d45890120000000000000000000000000000129004821490124a40000000000008d1d217ec0230008f44202d6b004800124d45890120000000000008d1d217ec0230008e285fb008c00000000000000000000000000008d1d217ec0230008e285fb008c0 normal233 (by decide) (by decide) (by decide +kernel)
private theorem normal235 : (hankel (cubeSeq (ZMod 53)) 235).det ≠ 0 :=
  certified 0xcf0caea570f40f1c7099ccc1000cc0c3099ccc1000cf3c2b84d682d000021053d90b4000000000000cc0c3099ccc1000cf1c26733040000000000000000000000000000cc0c3099ccc1000cf1c26733040000000000000000000000000000c82033b6873307208000000000000200514f642d00002085294a1bcc1000cf1c2673304000000000000200514f642d000021053d90b400000000000000000000000000000200514f642d000021053d90b4 normal234 (by decide) (by decide) (by decide +kernel)
private theorem normal236 : (hankel (cubeSeq (ZMod 53)) 236).det ≠ 0 :=
  certified 0x248a519742010f04f5ee4028a60019049ae4028a6001968a9f2529133c0d0f7879734cf0000000000019049ae4028a6001997b900a29800000000000000000000000000019049ae4028a6001997b900a2980000000000000000000000000000017068ba70a29805c0000000000d11c4f1e5cd33c0d1034b5ac8d18a6001997b900a2980000000000d11c4f1e5cd33c0d0f7879734cf000000000000000000000000000d11c4f1e5cd33c0d0f7879734cf normal235 (by decide) (by decide) (by decide +kernel)
private theorem normal237 : (hankel (cubeSeq (ZMod 53)) 237).det ≠ 0 :=
  certified 0x5e19f4734caf9dc65bd33caea1a0578676b3caea1a0580d3318c2b84d6f471b0420c735b0000000000578676b3caea1a0596b4cf2ba86800000000000000000000000000578676b3caea1a0596b4cf2ba86800000000000000000000000000000006d7cf1ba8680d0000000003479439b0831cd6f47728a9745294a1a0596b4cf2ba868000000003479439b0831cd6f471b0420c735b00000000000000000000000003479439b0831cd6f471b0420c735b normal236 (by decide) (by decide) (by decide +kernel)
private theorem normal238 : (hankel (cubeSeq (ZMod 53)) 238).det ≠ 0 :=
  certified 0x755f7d3b2739a86991fa1c350a961d57df4dc350a9621cd09cafa5d14b7ec4a1359a252e00000000011d57df4dc350a9626352870d42a5400000000000000000000000011d57df4dc350a9626352870d42a5400000000000000000000000000000000256c242a574a80000000d2e8165a266894b7ed641b0318c630a9626352870d42a540000000d2e8165a266894b7ec4a1359a252e0000000000000000000000000d2e8165a266894b7ec4a1359a252e0 normal237 (by decide) (by decide) (by decide +kernel)
private theorem normal239 : (hankel (cubeSeq (ZMod 53)) 239).det ≠ 0 :=
  certified 0x1679129dbd0a20110246f5b4033d009e44a76f4033d01b1604435ad33c81cc4b507c10020850000000459e44a76f4033d02c48956d00cf3c000000000000000000000000459e44a76f4033d02c48956d00cf3c00000000000000000000000000000000000aebcf3becac0000034c0e46339a040081d097f4c686c1083d02c48956d00cf3c00000034c0e46339a040081cc4b507c1002085000000000000000000000034c0e46339a040081cc4b507c1002085 normal238 (by decide) (by decide) (by decide +kernel)
private theorem normal240 : (hankel (cubeSeq (ZMod 53)) 240).det ≠ 0 :=
  certified 0x343c388b8043d79704670a004f5c1b8c0e22e010f5c1bcb4a5b6b913998c45ad435bd26780183000001d0f0e22e010f5c1c0a8686813d702fc80000000000000000000001d0f0e22e010f5c1c0a8686813d702fc8000000000000000000000000000000000001102ebe6bc0000d019b24ea57199ed06aa340829188f744c0a8686813d702fc80000d019b24ea57199ed05ad435bd26780183000000000000000000000d019b24ea57199ed05ad435bd26780183 normal239 (by decide) (by decide) (by decide +kernel)
private theorem normal241 : (hankel (cubeSeq (ZMod 53)) 241).det ≠ 0 :=
  certified 0x1502d80ab317d88d37c2bec2df621ccfb602acc5f622ce4b58a81a1b086842c48960a967945e6000040540b602acc5f623cc4b5054b7d785e3c0000000000000000000040540b602acc5f623cc4b5054b7d785e3c000000000000000000000000000000000000081aad678003402000856b24459d4c244874bd0d6b3bd4cc4b5054b7d785e3c003402000856b24459d482c48960a967945e600000000000000000003402000856b24459d482c48960a967945e6 normal240 (by decide) (by decide) (by decide +kernel)
private theorem normal242 : (hankel (cubeSeq (ZMod 53)) 242).det ≠ 0 :=
  certified 0x1d41f5f268ed010210585504ce6c07f1b71c9a3b404081921b517a0d00186265dc0a868681cd49db0017507d7c9a3b4040841605ad435bd0284e6800000000000000000017507d7c9a3b4040841605ad435bd0284e6800000000000000000000000000000000000000256c1d00d189567836e707401572d6a178da00d144dc605ad435bd0284e680d189567836e7074014d1dc0a868681cd49db000000000000000000d189567836e7074014d1dc0a868681cd49db normal241 (by decide) (by decide) (by decide +kernel)
private theorem normal243 : (hankel (cubeSeq (ZMod 53)) 243).det ≠ 0 :=
  certified 0x164485729aa7bdb590b0b7c781f514199715a6a9ef6d52c8b9a41e7215719870aa5898e48a67ae78704591215ca6a9ef6d642c2dfb124533d71d7b8000000000000000004591215ca6a9ef6d642c2dfb124533d71d7b800000000000000000000000000000000000000009679f4c118f064c2ce19a82ab476e55d952010fbb32dfb124533d71d7bb4c118f064c2ce19a7e526a5898e48a67ae787000000000000000034c118f064c2ce19a7e526a5898e48a67ae787 normal242 (by decide) (by decide) (by decide +kernel)
private theorem normal244 : (hankel (cubeSeq (ZMod 53)) 244).det ≠ 0 :=
  certified 0x13d1074e9e44b1c9c197ac2c4891021564bc95912c726e861b6a35813ae66274db7312d4152dfb124534f441d3a7912c727065eb0b122582a5898e48c00000000000000014f441d3a7912c727065eb0b122582a5898e48c00000000000000000000000000000000000000000014220656273918c40da35d69b49fd271dc4d8a080b122582a5898e48a20656273918c40d9bde2b312d4152dfb12452000000000000000d220656273918c40d9bde2b312d4152dfb12452 normal243 (by decide) (by decide) (by decide +kernel)
private theorem normal245 : (hankel (cubeSeq (ZMod 53)) 245).det ≠ 0 :=
  certified 0x961c296d72d0cf2526862ca48a6797bd4b158e9433c930409c924b6cec1115239f8514cf5c79dcc86a87870a5b5cb433c949a18b292299eb8e643bcc780000000000000065870a5b5cb433c949a18b292299eb8e643bcc7800000000000000000000000000000000000000000005d414c69eaa50838b400eb2ca9a9c59308e759492299eb8e643bcbb9414c69eaa508384f5130d14cf5c79dcc86a5700000000000003441414c69eaa508384f5130d14cf5c79dcc86a57 normal244 (by decide) (by decide) (by decide +kernel)
private theorem normal246 : (hankel (cubeSeq (ZMod 53)) 246).det ≠ 0 :=
  certified 0x2468242a4a52422498a8591105ad435b05299a59608923339404fa062cb4ab5499d52702a1a1a07312eccd090a92949089262a1644416b50d6f40b122634000000000000191a090a92949089262a1644416b50d6f40b122634000000000000000000000000000000000000000000003394b8d0b33b2d0a787498dbeaaa32a0b0e82c16b50d6f40b11c2a3394b8d0b33b2c4cd7e4c702a1a1a07312d3e8000000000000d116f394b8d0b33b2c4cd7e4c702a1a1a07312d3e8 normal245 (by decide) (by decide) (by decide +kernel)
private theorem normal247 : (hankel (cubeSeq (ZMod 53)) 247).det ≠ 0 :=
  certified 0xb67480b6f45a0615e924c598516263922996a20a4a856c57bd681a1648832f2562baca9fb124533d721e60902dbd1681857a493166145898e48a67ae3cf24000000000006d9d202dbd1681857a493166145898e48a67ae3cf24000000000000000000000000000000000000000000000020691bd147c47867d56f0453caa0e04c724b5898e48a67ad5ddb0020691bd1478cb297dd85fb124533d71e69ac00000000003420e8c020691bd1478cb297dd85fb124533d71e69ac normal246 (by decide) (by decide) (by decide +kernel)
private theorem normal248 : (hankel (cubeSeq (ZMod 53)) 248).det ≠ 0 :=
  certified 0x279a2c40009c6e2adb4ba44872603bcc7702a1c862c8b06687221c8f1c10a50f4b657956f21a9605ad5cdc433000271b8ab6d2e9121c980ef31dc0a869292cc00000000019e68b1000271b8ab6d2e9121c980ef31dc0a869292cc000000000000000000000000000000000000000000000002c107ac9bdbbad5039aed3343204841781a0ef31dc0a80266508002c107ac822a3315037721a9605ad432b8c2000000000d0e3d310002c107ac822a3315037721a9605ad432b8c2 normal247 (by decide) (by decide) (by decide +kernel)
private theorem normal249 : (hankel (cubeSeq (ZMod 53)) 249).det ≠ 0 :=
  certified 0x6049a83800009d958a7f008d46b2a8681cc4b51aca3dc9db28fd11aca0418296b23de1c0c8d6f40b124738ec8700002765629fc02351acaa1a07312d46b62b1c0000000058126a0e00002765629fc02351acaa1a07312d46b62b1c000000000000000000000000000000000000000000000000039c80e6ab98190aaf4d1531b0e65ee003a1a07312cba79c3b8000039c7eb585ce890aacd6f40b122429d2ae0000000347713cd9c000039c7eb585ce890aacd6f40b122429d2ae normal248 (by decide) (by decide) (by decide +kernel)
private theorem normal250 : (hankel (cubeSeq (ZMod 53)) 250).det ≠ 0 :=
  certified 0x33bde49ca8000000334007134fa52be1a1a0731694af8241987e66a94af865341c8970318c6d435bd03b86318cd50000000cd001c4d3e94af868681cc5a52bde540000001cef79272a0000000cd001c4d3e94af868681cc5a52bde5400000000000000000000000000000000000000000000000000339af7563db323194428d03b19cafa5a868681c87be9742800000032a00d04a2632319435bd02c0c8c65e0000000d021978d92c0000032a00d04a2632319435bd02c0c8c65e0 normal249 (by decide) (by decide) (by decide +kernel)
private theorem normal251 : (hankel (cubeSeq (ZMod 53)) 251).det ≠ 0 :=
  certified 0x4eb545c1e900000053c4a744b82a6d59bd02c49069b55198a982504e9b566a11a7872c2b84ec5a07314aaa135b6120000014f129d12e0a9b566f40b1241a6d546480000053ad51707a40000014f129d12e0a9b566f40b1241a6d546480000000000000000000000000000000000000000000000000000bcb76c9623087db52f3940c52949c46f40b0acb52869d8c0000d2212b6311f33087da07312cd0c220be300003488a830157440000d2212b6311f33087da07312cd0c220be3 normal250 (by decide) (by decide) (by decide +kernel)
private theorem normal252 : (hankel (cubeSeq (ZMod 53)) 252).det ≠ 0 :=
  certified 0x2e5d61e8014cc0001b975a2a879f25910ee3991260164089746c21d3d1644202c0d7c6e9139d4c479ddaa65a662d93400006e5d68aa1e7c96443b8e644980590225d00001b97587a0053300006e5d68aa1e7c96443b8e644980590225d0000000000000000000000000000000000000000000000000000001acee8817e4cc02727841d188e844b8e60b3df3dd2110400341de7d32ee3837e4c879dcc4f01f96d401000d0779fb8d0210800341de7d32ee3837e4c879dcc4f01f96d401 normal251 (by decide) (by decide) (by decide +kernel)
private theorem normal253 : (hankel (cubeSeq (ZMod 53)) 253).det ≠ 0 :=
  certified 0xc5880cb9241db0007162032e76a3447e5244b513efb1e9ee79600b6a535f90d84d1564824633ee371260266550817d16001c5880cb9da8d11f94912d44fbec7a7b9e58007162032e49076c001c5880cb9da8d11f94912d44fbec7a7b9e580000000000000000000000000000000000000000000000000000000a9b428591a14a307e3ce44a61e812c56c3e09557817c0d04755a4760ba31590b312249862573875df03411d5691e3958240d04755a4760ba31590b312249862573875df normal252 (by decide) (by decide) (by decide +kernel)
private theorem normal254 : (hankel (cubeSeq (ZMod 53)) 254).det ≠ 0 :=
  certified 0x298afb716b41c8281a62bedc5ad00c4cbdc648992cf3c44490705000ba90aea2c3ae599d3120658086e0d0c6f0168ac8450698afb716b403132f7192264b3cf111241c141a62bedc5ad0720a0698afb716b403132f7192264b3cf111241c1400000000000000000000000000000000000000000000000000000000073331cd2671df70112dbdf0141f29441807d3254c3431318811b04012919972d3e30821318e5670d0c4c62046c1badaf431318811b04012919972d3e30821318e5670 normal253 (by decide) (by decide) (by decide +kernel)
private theorem normal255 : (hankel (cubeSeq (ZMod 53)) 255).det ≠ 0 :=
  certified 0x5409c26f34d8a8da5502709bcd362a7247212814cf2651a7be45d400000fc07858d2d46b3512cb22b2d4898babb61786ad55409c26f34d8a9c91c84a0533c99469ef91755502709bcd362a3695409c26f34d8a9c91c84a0533c99469ef917500000000000000000000000000000000000000000000000000000000000985b947412242a892aaad2aa853747288517bca82000ecda0a274b651654af48a6b10bce1917a08003b368289d2e832000ecda0a274b651654af48a6b10bce1917a1 normal254 (by decide) (by decide) (by decide +kernel)
private theorem normal256 : (hankel (cubeSeq (ZMod 53)) 256).det ≠ 0 :=
  certified 0x127a46ae55802420485e91ab9560090811d6d8452bf091b5258192e2000000c72a6c65a624b0c843ce98cca9f2af110124bb47a46ae55802420475b6114afc246d496064cd1e91ab956009081217a46ae55802420475b6114afc246d496064b8800000000000000000000000000000000000000000000000000000000000040cc25c6dd449a54c82312a4b5ab1b197144705745b1e074046dc5869d92318545a85055ca415d16c781d011b7151745b1e074046dc5869d92318545a85055ca93 normal255 (by decide) (by decide) (by decide +kernel)
private theorem normal257 : (hankel (cubeSeq (ZMod 53)) 257).det ≠ 0 :=
  certified 0x45e36b84b32e1e12b3b8dae12ccb8784ad0a6045af66ebd74c8b3334800000144b3aa90d028ac926271a4134a846a6f4a8c9a636b84b32e1e12b4298116bd9baf5d322cd1e98dae12ccb8784acee36b84b32e1e12b4298116bd9baf5d322cccd200000000000000000000000000000000000000000000000000000000000d24aa72d1a0034ab2c4d96e58a33642da04ba4f3e8294aa91ee52b06b7717c670719e8ad2415cfa0a52aa47b94ac21e8294aa91ee52b06b7717c670719e8ad242a2d normal256 (by decide) (by decide) (by decide +kernel)
private theorem normal258 : (hankel (cubeSeq (ZMod 53)) 258).det ≠ 0 :=
  certified 0xe1c3c4b1303cb3128451312c4c0f2cc4a24cbd2e8513e2a918b151e31b00004e1c38dd5805ded0078ab5aca0c571b3790cc3b9ec4b1303cb3128932f4ba144f8aa462c55b137b12c4c0f2cc4a1144c4b1303cb3128932f4ba144f8aa462c5478c6c00000000000000000000000000000000000000000000000000000000349eec9261f01e5c1017ac86c35447af097942c875c4ab1166aa98d38aa0475249932e44c480989712ac459aaa63530c44ab1166aa98d38aa0475249932e44c4857a5a normal257 (by decide) (by decide) (by decide +kernel)
private theorem normal259 : (hankel (cubeSeq (ZMod 53)) 259).det ≠ 0 :=
  certified 0x6046dd5078638ca9b44967941e18e32a602a684c5b2a40455ea10284f95b0016046dd51e053c26a8f7805e5ba519c32e1a44c39835078638ca980a9a1316ca901157a840c44cb0d41e18e32a6d1259e5078638ca980a9a1316ca901157a840a13e56c0000000000000000000000000000000000000000000000000000000d1dc5a6215f48853cb99701e40742f6691ef462c8fca1b94492acf00b6f111aad1d3078bc72c62ab286e5124ab3c18df5e1b94492acf00b6f111aad1d3078bc7352641a normal258 (by decide) (by decide) (by decide +kernel)
private theorem normal260 : (hankel (cubeSeq (ZMod 53)) 260).det ≠ 0 :=
  certified 0x625f14e4f25ddd01045551253c977740422dec0e8505335c43f4073d33bd804625f14e4f25980cda5926fc644956d33800031975e64f25ddd0108b7b03a1414cd710fd02108774993c977740411554494f25ddd0108b7b03a1414cd710fd01cf4cef600000000000000000000000000000000000000000000000000000034bec5b09e20df772a0c72c18446381a8a7000caf79e3e20de601d33a971675258427b1981cf1b5804f883798074d30824b220de601d33a971675258427b1981d0204219d normal259 (by decide) (by decide) (by decide +kernel)
private theorem normal261 : (hankel (cubeSeq (ZMod 53)) 261).det ≠ 0 :=
  certified 0xc1a4316ee44162909956a205651058a426903d807429264cb8fbc005cb6a891c1a4316ee44162ca9f9d900972b945209bc262ec9360944162909a40f601d0a49932e3ef071048988251058a42655a8815944162909a40f601d0a49932e3ef00172daa2400000000000000000000000000000000000000000000000000000d056e511a1e4d1d24b58e700b19290c2db06cdd1c389db24d1d3336e599dd01ae37291e61b4134b4fb6c93474ccdc80bb70724d1d3336e599dd01ae37291e6180d1920b4e5 normal260 (by decide) (by decide) (by decide +kernel)
private theorem normal262 : (hankel (cubeSeq (ZMod 53)) 262).det ≠ 0 :=
  certified 0x1602f7ccc1da2a41e5ca76c4f47a8a9079881d9b22d941d16e068ab31408f143102f7ccc1da2a41e20e8c8929b62cefa5da5915d257943a2a41e620766c8b650745b81a2b505bcd20a0e8a9079729db13d1ea2a41e620766c8b650745b81a2acc5023c4f6c00000000000000000000000000000000000000000000000000347c0196a4560d2e55ed9d2b513084c218c60c73062c790c8d2e55dd5583c3a9c958c07d0d2a1c06a2daf234b9577ab6098815cd2e55dd5583c3a9c958c07d0d2c2c0048499a normal261 (by decide) (by decide) (by decide +kernel)
private theorem normal263 : (hankel (cubeSeq (ZMod 53)) 263).det ≠ 0 :=
  certified 0x6525a568bae78e99c091962baf4ae3a67048aee6d02a15576e8219a745102020945a568bae78e99c0914adaac1b323b084e3251488ea5a98e99c122bb9b40a8555dba0868d46a022314a63a67024658aebd2b8e99c122bb9b40a8555dba08669d1440805e080000000000000000000000000000000000000000000000000d1c8df41ba8a39230e01184a6cad090e71549e9430b522df31230ed2d2876a5ad481e68db5ba242c04e984c48c38045c74a28129230ed2d2876a5ad481e68db5c301865b745f3 normal262 (by decide) (by decide) (by decide +kernel)
private theorem normal264 : (hankel (cubeSeq (ZMod 53)) 264).det ≠ 0 :=
  certified 0x1903295c9275eb29979a8c3cee70864a65fce302354bbf00230dc1ca983808215ca995c9275eb29979a8c3805ab08e67e3494a6062b9e02e22997f38c08d52efc008c37088e601092b8d488a65e6a30f3b9c2192997f38c08d52efc008c37072a60e0207c72b000000000000000000000000000000000000000000000000347000d065139e2ab7176d2c95c0b1523d64a384c55d28e56a4eb71609201282a185012c99b523c0951292853adc5db4b208766d72b71609201282a185012c99bab3f256db840c9 normal263 (by decide) (by decide) (by decide +kernel)
private theorem normal265 : (hankel (cubeSeq (ZMod 53)) 265).det ≠ 0 :=
  certified 0x274206d298197ebca40ab6ce21359c4f294baa35071c1032a22beb4303490ca2e39efd298197ebca40ab6ce201ca555c9475077922f4467c9fca52ea8d41c7040ca88afb19bd53c2ca22097f2902adb3884d6713ca52ea8d41c7040ca88afad0c0d24324291fa40000000000000000000000000000000000000000000000d2c06dbc131571628347329a9edd03420650ba1b978ea06438358342a2d286ebb4003353189706826cc34edb160d1cca6a7b627d988342a2d286ebb400335318a945a2ccaccd158c normal264 (by decide) (by decide) (by decide +kernel)
private theorem normal266 : (hankel (cubeSeq (ZMod 53)) 266).det ≠ 0 :=
  certified 0x1fcee5e75da7dc452bc60270e529f732cf097381a5e110664f35f0c13a1bdc3d129649d5da7dc452bc60270e529fa1cb2216eb54b5c5d84f4088c25ce06978441993cd7c480c6913a532b10c22f1809c394a7dccb3c25ce06978441993cd7c304e86f70e9cc770ac00000000000000000000000000000000000000000000345821de39e6d66648c6bc03b242b58d6494f01c884865e762073b4540255b794c6f726a16c55a5b9274292b1a6d1af00ec90ad664308540255b794c6f726a16cb49d41999cea5814a normal265 (by decide) (by decide) (by decide +kernel)
private theorem normal267 : (hankel (cubeSeq (ZMod 53)) 267).det ≠ 0 :=
  certified 0xb965a991d46a08c2ca508150bc9b4bac734d79b11e98902d4d85f1aa862c8d182a9921de46a08c2ca508150bc9b4baef4e75a194e89f5d9c0d90c35e6c47a6240b53617ca326e812b43252aa32d420542f26d2eb1cd35e6c47a6240b53617c6aa18b23427510798040000000000000000000000000000000000000000000d077df3116242f3a6aae1b70946b08a8a1a239f5109d359e705a11a685dac573ec00889d7834ac1d58c8cac8cb4aa86dc251ac22a2aea285dac573ec00889d7842cd7494a53a1957774 normal266 (by decide) (by decide) (by decide +kernel)
private theorem normal268 : (hankel (cubeSeq (ZMod 53)) 268).det ≠ 0 :=
  certified 0x1d3846d0bde30e40ec42188950c10ac034ab9430b82ab8239d62a56a14c7d96437db2a228b30e40ec42188950c10ac034a2d77ef78cb55d14470bcc50c2e0aae08e758a96493405a5211d97480c90622543042b00d2ae50c2e0aae08e758a95a8531f6586d15e4490880000000000000000000000000000000000000000034627c5a9465e99e59c4cefb5094594a028aea796197a48801864146a61a6a54b1f39d874b7e38a5c0c8f1610055a51bed425165280a2b1e1a6a54b1f39d874b80bc2959c75a91e463953 normal267 (by decide) (by decide) (by decide +kernel)
private theorem normal269 : (hankel (cubeSeq (ZMod 53)) 269).det ≠ 0 :=
  certified 0xb067680e6cd178b11fcc5905d2508609060a9ccb425805e06dca646967e28a97d2ae9b5371f78b11fcc5905d2508609060a9c6a4260ccabb416eb85932d09601781b72995170756566676c32e31c4e41749421824182a732d09601781b72991a59f8a2a2830e06a89e380000000000000000000000000000000000000000d09bd83723c2917ab1582c11c01433bf395dacebcccdda43288d1a2947292337c0795699310919ba041c3d82691e9662470050cefce576b3a92337c07956993116df5934cd3699f42d35e7 normal268 (by decide) (by decide) (by decide +kernel)
private theorem normal270 : (hankel (cubeSeq (ZMod 53)) 270).det ≠ 0 :=
  certified 0x110929c24c240500cd31a2ba88a61556bd0502d1c2878e56ef713c96422755d0a0a3547b1599b00cd31a2ba88a61556bd0502d1c9152b0844a2ab0185e70a1e395bbdc4f39d2d0f5d1c105a34583c932a2298555af4140b470a1e395bbdc4f259089d573b804631594d65800000000000000000000000000000000000000349338cece2ce5c00a4110d28bb4c5207c6961cc165182b154c4d2c9d145d9aee49068666208e8c199e90595f4a4766b292ed31481f1a5873059aee4906866620df9536200870244b07227df normal269 (by decide) (by decide) (by decide +kernel)
private theorem normal271 : (hankel (cubeSeq (ZMod 53)) 271).det ≠ 0 :=
  certified 0x73407325431a7c590252a3eaadb9a0832bd221d6f4bf214a09e51baeba273d8147c874902f305990252a3eaadb9a0832bd221d6f4bd4c9e917a734e4187d2fc85282794712aa9958aea89b3adcd33a626b6e6820caf48875bd2fc852827946ebae89cf5de231249c74657500000000000000000000000000000000000000d190740ac8696d6c11ce12e62ca68f5550c68ed61a0468435d178c0a246fb81183c2bcd78598cb31074a2d36a72028a73ec29a3d55431a3b58681183c2bcd785a28a34e99e5ed12cb0405c7a1 normal270 (by decide) (by decide) (by decide +kernel)
private theorem normal272 : (hankel (cubeSeq (ZMod 53)) 272).det ≠ 0 :=
  certified 0x1cb6996a333d11d010aac6b6c7ce328d2741c2c0d18a849788009ad02ed86a8513a1ba670f20d6060aac6b6c7ce328d2741c2c0d18a84935210d92bbb4a412a125e20026cb038517eca15248c921859f43338ca349d070b03462a125e20026b40bb61aa0a96b49c50449c591400000000000000000000000000000000000346483102e9081901d332c429ab824aba2c06ecc5a2fad4b288f1a1128704cd2b52c5ed02c249c9491624d82cb438efc0e069092ae8b01bb3168beb52c5ed02c2a5a8850b54b7c8b04964b04730 normal271 (by decide) (by decide) (by decide +kernel)
private theorem normal273 : (hankel (cubeSeq (ZMod 53)) 273).det ≠ 0 :=
  certified 0x9a896b570b038141d27c56e97970e0a9d80485a3e11ef8d5c6758ab8296fc6cbd6518703a728233a77c56e97970e0a9d80485a3e11ef8d5c485981e76806a7be35719d62dfa9595198098f04e69cd1b0e5b0382a76012168f847be35719d62ae0a5bf1ac98e4887232bc03c7540000000000000000000000000000000000d0f3502a0149c9586e8d6c1a3177b254b615c546e652e192804b5f76e39b01b3864a010e7ea58b81090f00f9b49db6416b2409c952d857151b994b864a010e7eb1f340610ab12453bad0c6026ba0 normal272 (by decide) (by decide) (by decide +kernel)
private theorem normal274 : (hankel (cubeSeq (ZMod 53)) 274).det ≠ 0 :=
  certified 0xbdf382ace0a50cbc83869c1518b9432e6714655d141e7a0ec595853d06cb20a2415694b31969c4a2f869c1518b9432e6714655d141e7a0ec592ac4289867909e83b1657149be93726111cac99a2569f3b10a50cb99c5195745079e83b165614f41b2c728f5c79dc9449a4babb000000000000000000000000000000000340065a7cca9f3432a83c9430582fa90caa3d985c80186e38d9c472b26534fbd794e36711c7b0b063280dd92eac370d41b5a7133432a8f661720061b8e36711c7f09a56aabab99eb8e650c4f447289 normal273 (by decide) (by decide) (by decide +kernel)
private theorem normal275 : (hankel (cubeSeq (ZMod 53)) 275).det ≠ 0 :=
  certified 0xac9667ba0174a7195c80845fd28787c6571e22c054ae556584c1672496837d4767857655692be7a7042a45fd28787c6571e22c054ae556584c16726a98b417028961305a344b3a98cec7718504406d75431cea7195c788b0152b9559613059c925a0df4e7788960a954c6ac4525880000000000000000000000000000000d0ab1c38757004c110655b64581357b844195ed27484a420414a703ac2cfaa5780350529c0d06308b74225811496401a7a0cae9cc110657b49d21290810529c0eb2c6f25a2397b5054b822bcac61413 normal274 (by decide) (by decide) (by decide +kernel)
private theorem normal276 : (hankel (cubeSeq (ZMod 53)) 276).det ≠ 0 :=
  certified 0x2b659c4cb25cc072e5f134c753370c8db97be13c3c48557ad5411726ac07d672e2222299eea4f75691bb9b753370c8db97be13c3c48557ad5411726ac0094c2badc55045d70f65b892a222685921436dec1a69e72e5ef84f0f12155eb55045c9ab01f59b0e424c77026b3c174d7e13c000000000000000000000000000003429c704a494020191de128a588a8143a07786526c84b6078a8259193ca03384528a66096461999c6938cd4ec35f8f0c9a5c56db5d91de1949b212d81e2a096464f28059f6b246ca5816c2a6d18a16526 normal275 (by decide) (by decide) (by decide +kernel)
private theorem normal277 : (hankel (cubeSeq (ZMod 53)) 277).det ≠ 0 :=
  certified 0x7d37ee95551b7b00dca1f2eb50d4b480f72659a8a29026229df34869ab8a7d6b0abe76e98172931b4be20df50d4b480f72659a8a29026229df34869ab8a7ccc15ab37cd244b580cfaa14aea6ec346ec3979590980dc9966a28a40988a77cd21a6ae29f54db10bab50cc616036070eda40000000000000000000000000000d168961d082169717264d5aa2a1a230559993df6d34d1cdd4ce5a8b5b6c7ad6a4580b096a2cc4877298b5231cc1c505a26779073377264f7db4d3473753396a2d6db1eb5a0a099472a1a4451dc9dbb220c normal276 (by decide) (by decide) (by decide +kernel)
private theorem normal278 : (hankel (cubeSeq (ZMod 53)) 278).det ≠ 0 :=
  certified 0xb7c93d89dd89f9f23e6a2b90d6c02d35ef912892921a0500987308a78a7eb52e66254cd025826ab72028ad226c02d35ef912892921a0500987308a78a7eb52e8e1b8ccc35484ee3852dc0ed99c2dc3971a8be29e73e44a24a4868140261cc229e29fad38ef646a4d6a9628b8dbd7510540000000000000000000000000034a96b2674e61358e0e63cd291a1a02a89e1918d38d150dc00b140b3ad7ad62a11d2507a42ca0b621e7c2a67220f66a6677af3464ce3a64634e345437002c502ceb5eb58a89219cbcca1b31d347a067a1960 normal277 (by decide) (by decide) (by decide +kernel)
private theorem normal279 : (hankel (cubeSeq (ZMod 53)) 279).det ≠ 0 :=
  certified 0x42291a62ec692492b02ae491b5dc589cb8d5383cee8db75b846ad78636c182148cb2a16d6149866324ca05e810c589cb8d5383cee8db75b846ad78636c182148cb144c363140a6c36734d166cbe666f3867c5a5661620e0f3ba36dd6e11ab5e18db0608027c8422d1c81dc8e089464368a00000000000000000000000000d254d16dd1c432cb2b16b1e390860474ea92827c821d2698694bca79449ad15523a49862c9d125adac9c0a291c2463dc1a7bd6c0c7dd7ed9f208749a61a52f29e5126b4555cd6b654c16556039f3b2446834d normal278 (by decide) (by decide) (by decide +kernel)
private theorem normal280 : (hankel (cubeSeq (ZMod 53)) 280).det ≠ 0 :=
  certified 0x2c9e55732619179ec2e1a4169659f8d6ba389b74585b17468576845a51671d5937a4105cf159e4304132ac6ee78a8d6ba389b74585b17468576845a51671d5937a41058274461b16de21b596cc0c5b20369b44432f1aa19d1616c5d1a15da1169459c75572cd241ea4271de1059d6ac160880000000000000000000000003424e4200ac51178e26a50cd1b7df5927c7493698c146b005bc183646e17d961f897471c153a4bef11a5ed69f7c20046adc9b6a4c691af2ef63051ac016f060d91b85f65881924146e2e53ae5f1c0e7cad1db55 normal279 (by decide) (by decide) (by decide +kernel)
private theorem normal281 : (hankel (cubeSeq (ZMod 53)) 281).det ≠ 0 :=
  certified 0x4cf1cbc7384034e2096259707c9aaa9679d808888948d2867d208e603ca668289ece668f52f5cab190d1b695f19699679d808888948d2867d208e603ca668289ece668f52c484c56d303c4a6668b7efb0e6555ad81f2f21e225234a19f4823980f299a04f3ec6de468bcac64420848bada30d00000000000000000000000d229aea840940289edb1d410156b0b2d038e773b53b23a2bbd68f39ddc833dbcd35c23db9a1263c447c1166c4c3dba961899dc81f2155aa0ee4ec8e8aef5a3ce77720cf6f49a625a5e4346ac4465554b4720d141 normal280 (by decide) (by decide) (by decide +kernel)
private theorem normal282 : (hankel (cubeSeq (ZMod 53)) 282).det ≠ 0 :=
  certified 0x10596c34751005007ac4858444aedd28c05ab216a3ae1037c2d032733090b051d2cb0eb89e4b261a42066c40d319c18c05ab216a3ae1037c2d032733090b051d2cb0eb89e4b27f2bf07aabc8cf04734295d052c1ef38b78168eb840df0b40c9ccc242c1336aa88b05352b584da72d53425687194000000000000000000003495f7c5058900c00b8ac54764c4a201345c0b0f02e71f1c96cc1cac0a9b3316162aab22935e30d60c61572c6b421640a531e96126e1a7a97d1b9c7c725b3072b02a6ccc58a82cbb49c288c87626d922106c7d4110 normal281 (by decide) (by decide) (by decide +kernel)
private theorem normal283 : (hankel (cubeSeq (ZMod 53)) 283).det ≠ 0 :=
  certified 0xaa251324b09f75809c2b494352f8981948333a402f782af304c3971dc19fa0e24a5e97040e6466cac0e03101040a3cc88333a402f782af304c3971dc19fa0e24a5e97040e6466cb16161e0b9554b19944f29b122850223bed8de0abcc130e5c77067e8354743593b811e93b042e85c3652952eda40000000000000000000d0b4e18acab359877366b050ca119376f8550a7440197cca0b4a677ae66f58d9ecade319c723e43c311d7ee547820aaf7249ab6b14d496d4862125f3282d299deb99bd6368858c9f887d2e3271651d466842b82a20c normal282 (by decide) (by decide) (by decide +kernel)
private theorem normal284 : (hankel (cubeSeq (ZMod 53)) 284).det ≠ 0 :=
  certified 0x113740d2bd7934a6a7ef1ac4316c73991e9a8f6e9cec97348b85759ccc49ee31a3686a81815ad2692c5b1606ab1d96c06aa8f6e9cec97348b85759ccc49ee31a3686a81815ad2692c5824a0b2eb66d965c074b40ed8869721edb65cd22e15d6733127b8b240a5758c7e7b95d212e67e6b915974ef0400000000000000000349280728c679104c2d61af26511aba772e30b99a3022500a3a9479f642c4e1e96e835b36fd1f22c32ac1544daaa29c210405ba3072213bd00ee2084028ea51e7d90b1387aac00c79fa5638780152a3d63c791f7a21b4 normal283 (by decide) (by decide) (by decide +kernel)
private theorem normal285 : (hankel (cubeSeq (ZMod 53)) 285).det ≠ 0 :=
  certified 0x28d79cb495d299b6b13e968dbe966ece644f7c28941565c55244510f00c42a898d363cef14e91da06c334b380b9ad5ea24b7c28941565c55244510f00c42a898d363cef14e91da06c334958a08b29583c8cc50eb5c29ac046632497154911443c0310a9dc0241c69a3c7308e2a12ad9a65cdd1912dc40000000000000000d2ba17648b1e8cf69b12631ba0631c1c23e4996cd38707dec21464932172c6b34fa284821b09d160dbc50a38135530d0766b42c3229eccf274bdd0e37b0851924c85cb1ace64046ebcf4840b39eb52b20f3dea01731204 normal284 (by decide) (by decide) (by decide +kernel)
private theorem normal286 : (hankel (cubeSeq (ZMod 53)) 286).det ≠ 0 :=
  certified 0x2e685a9616535385421f021862c9b1149580121aa94dc1066e5a8ac1c122e62e66ad52d407522cec4dd74d18b54b7c7261a441aa94dc1066e5a8ac1c122e62e66ad52d407522cec4dd74d18bad3047c3314866100a0580a17495a4099b96a2b07048b98ab40a1f5cb5c73d260bcdd85a79895ba192699c00000000000000341dbc0b7f042889486d5805144c36b18507408ef2d0a0595c1df34ad058ea3ea3db221225ba14c2262618a2fa8a8b4b850b0b5c500af4773518b1f4737077cd2b4163a8fac800d59ea9eba68dda826146d775068d72c30e normal285 (by decide) (by decide) (by decide +kernel)
private theorem normal287 : (hankel (cubeSeq (ZMod 53)) 287).det ≠ 0 :=
  certified 0xad71616090842d542a4c3b0a007574b27397890596a0646009d60dbc83989cd78c272b301e53658a74cab8f9a473425596f930596a0646009d60dbc83989cd78c272b301e53658a74cab8f9a471892e6921151aeb34d2942810a7932c275836f20e627328a844549c5842412c801c21667470128d7602800000000000000d0a7b051db33c6a8252e2c89ac0ba00493a779395f7cdbe457361da06b6774ea17a6c0c916e4284133a2ac798f4597511db8f182f1c9041325371ad78aacd87681ad9dd3a934bc6484ec14ce58c302ecf03d8b808d279dcd5 normal286 (by decide) (by decide) (by decide +kernel)
private theorem normal288 : (hankel (cubeSeq (ZMod 53)) 288).det ≠ 0 :=
  certified 0x12ae15ca7d15e8ab20a852f5c4c5d1478443a23a80069043db18860950875019c4a0bb34cbcd6a62501a509cc9ab8b08565100160069043db18860950875019c4a0bb34cbcd6a62501a509cc9ab8b0756a4eada771303c2b70062a9c124621825421d40529cd17a69bdc8f495239559022a39da404868e78c00000000000348ca51ead691e34b0f336119ec44630b94c674e7340bd1c666afb5db21b5896f6635470a2a827cc4e1d0c94ea4f2931587cc9ca6d8129c8529901d2ced2cbed76c86d625c2b64178c3066520508e781f96d2e760c023bd2392 normal287 (by decide) (by decide) (by decide +kernel)
private theorem normal289 : (hankel (cubeSeq (ZMod 53)) 289).det ≠ 0 :=
  certified 0x342a7a9c7cb6d2a80824651995c0c533472b4c8724ae261300932ac08c559971bd15bca2eb129550b59a0702f8cc3c2a2dd2e8064ae261300932ac08c559971bd15bca2eb129550b59a0702f8cc3c2a11948063a605e031c069a5038b264cab02315661c72a8c58e181e5e040da8facf6a8030117c078b4240000000000d0006b38b656a9a8cb01545c90f805a610a40c8a540e31ec5290110ca012c1f719681806aea2b132094870db80192a66ccd910b7448c55e56967430c967aac4432804b07dd6592d2c125155de565a0b98a99b340171785b9306c normal288 (by decide) (by decide) (by decide +kernel)
private theorem normal290 : (hankel (cubeSeq (ZMod 53)) 290).det ≠ 0 :=
  certified 0x2bb402447b438a2c6700515cd029694f72952fbeeba1665259a064d1999b566a55ca2e535f31b3e8c524b025e9cb812982c9f5ab110665259a064d1999b566a55ca2e535f31b3e8c524b025e9cb812982c9fa23aa70b192ac43bc25655b3a9346666d599bdf2828648334448954b36cb39dab00ca39e95cc8b90000000003428802cc57067aeabd902180296b7d09993211861c751c42c70dbe290f7087db41eaea4285a96a63448e316c5cea958cfcc358d48b3b31112c4c86ce041f08b8a43dc21f7065abcd44550a4c5382309aaa760b172ae75d0643a91 normal289 (by decide) (by decide) (by decide +kernel)
private theorem normal291 : (hankel (cubeSeq (ZMod 53)) 291).det ≠ 0 :=
  certified 0x623bb21b39f32863d865465f9105debee38c7932c5833ad13ce68b8f27ef2e74ec3e77277949523ee71b8a155e310ab4ae499a944185ad13ce68b8f27ef2e74ec3e77277949523ee71b8a155e310ab4ae499a943c346931462c85b36293404a3c9fbcb9b0256a96a6c59b3005831c90a63aa9f019d6081dad1b1c0000000d1d4870ef08e0abbe675c85c59195e5c61e7a578aac1508a9269dba920d61aa3a22663993978508e61d96935205e994b04a44f6d0c8505b8b0beab5f09d328023483586a8f16c7cb7cc25f6a901fcaeb333e72ce16f61db6e6c16ae normal290 (by decide) (by decide) (by decide +kernel)
private theorem normal292 : (hankel (cubeSeq (ZMod 53)) 292).det ≠ 0 :=
  certified 0x2ab8a1856cfc1842f27360e2d55a9c91c677b39116b05c0488ba3427c1c79f06da111d2bb040d7f1ad6aac2912c67ed0da5c330fbf04d6488ba3427c1c79f06da111d2bb040d7f1ad6aac2912c67ed0da5c330fbf08d3411b618d016f18e8cc23071e7c00ef1c1353855a8f0a26127b4c6a4a2707a2e15dcd50315800000342c7aefc1a9857651ac09d9ea81f30390439709191b15e023b474a53856575b420d92e8c7165a1610a7cb26b92abd62326deca99861528a59085129701af9d2a6d1595d60321aed2889480b9b34dd8d70442e34d9b8d1f060280011f normal291 (by decide) (by decide) (by decide +kernel)
private theorem normal293 : (hankel (cubeSeq (ZMod 53)) 293).det ≠ 0 :=
  certified 0x7a3056859d304ce3d26085046018dac87b215683144846270caa60cd531120ac9201e3dec8b9241082e5a54451ccf62568db160925e5c6e0caa60cd531120ac9201e3dec8b9241082e5a54451ccf62568db160925e5c65767c8096f56e22e31770c4482549342231734115aaae875542e410a9b7a38578ebcc58591c0000d174b47d47011629e68ddb61c5dd126c3b89520369863c5d3b2acc54282992dac38c05e65c3a91471b6a40c86490299d41ba097f38de4044183830101a01ed1e9799a64b6c85106d4b00a591f2ca3588251e594b697494792282c1472e normal292 (by decide) (by decide) (by decide +kernel)
private theorem normal294 : (hankel (cubeSeq (ZMod 53)) 294).det ≠ 0 :=
  certified 0x3291dc301b0532c91243680527a250d4c125c48710a8059b69bc7299ad44c6213c0b6991ac2925e7417b8525f98d2d056e22f117665295869bc7299ad44c6213c0b6991ac2925e7417b8525f98d2d056e22f117665295869b5c3e73d03d111355f51318758c8df780c6b55a58751416ab73748c5a726ad86d7c89c690000340d160516f1610c392cc9b02138d4328458dec54133374708306bab70a862bed885a9b72f26b8de3a5787c2c58fa2a9601ed1b179c42b8143086663a69669318a05a18afb9fa525970042a06dfba18702c8098b446d93ca75a783b04300 normal293 (by decide) (by decide) (by decide +kernel)
private theorem normal295 : (hankel (cubeSeq (ZMod 53)) 295).det ≠ 0 :=
  certified 0x94ac6ec13cf23aba2c62429e40f62898635764913376422b400c4b9d73e59ec7f41a614ace079cc9f81645e15f1090c43da0a06ad1829c57d6c4b9d73e59ec7f41a614ace079cc9f81645e15f1090c43da0a06ad1829c57d6c5f9e6366bda79199e1a7aefa8ab4ab008d098aa089c702a421592cc20de5d6bde4df3cf580d10ac41c58820e728d25d46b5e599d34fbe879cb3109846d2a5004a8e7a640e25606f3f0ac25576435957e45f05b1b32c666f355b22fccec167c458e3e83c66d790f5ef38a18bac8ac901294facdb4eb802e551f8c2cf25de7c65e25a699f normal294 (by decide) (by decide) (by decide +kernel)
private theorem normal296 : (hankel (cubeSeq (ZMod 53)) 296).det ≠ 0 :=
  certified 0x75460ec28656ac94b2861693bd276922c5ab0dd54aade580463b941724a4280b557e28251dc66a051150505a8f74c0dbd1e981602791a03010b941724a4280b557e28251dc66a051150505a8f74c0dbd1e981602791a03010b944446546e11d7001449010047525ca31a386451992f9f0c8063091ea23643b68a120e48b401885d9c535c7cab230d451b8868d832d25f2b2620aca5df0244878700e346b0088164d542e65c2f4930961c0b998a726815cfd1dcd790dc80947864c5c85a52e780d24b00974ba14034af49446171118e14301d1515cd49cc8834d8f2453 normal295 (by decide) (by decide) (by decide +kernel)
private theorem normal297 : (hankel (cubeSeq (ZMod 53)) 297).det ≠ 0 :=
  certified 0xc2785834e3cf909a20a8b089aa8c647ac355292d13cdad145d711e3cfb33ae9588016b5e85c6ae1528d2b815b43b4361a8a6aaad592e85c8a321b3cfb33ae9588016b5e85c6ae1528d2b815b43b4361a8a6aaad592e85c8a321b3cfb0e66acb15c22af95b594ce041236b9529ee1ecb61312424a9da9062c0a652220b304c453947689e6991b0d54bab3b0b34445726882b8c18826c185e7b15e698908a31fb407c85d465b1f08d28c7d1f06706850badb2ca8111d46534ad6a69899dc2c311eceb19069f8425658e82908ce1ee2485298e544b60b95d2733e14edaa9c43 normal296 (by decide) (by decide) (by decide +kernel)
private theorem normal298 : (hankel (cubeSeq (ZMod 53)) 298).det ≠ 0 :=
  certified 0x15c6836d0875e5b8face4db4540a7ba9207c264d5aafd0865ab135d8201a305a14f13c67083731a1b17220a89834a948249a6c23ba1c59ccf00d5ea201a305a14f13c67083731a1b17220a89834a948249a6c23ba1c59ccf00d5ea201a30154a62af1a9579724239a06b38d48126a159a9e37181876b01d3849f245aa89bf4c84368233b9e40798a9e26a487338732db853e280b181b5c6c989e76dd0d15f522126bd9b680af5097ad54bb1504b85544f3c5487504702980a1e2edd0d17084c4ca10b8177acce76f42a7a23d2c2f070b5e8115758280627c4e0e46cbb06023 normal297 (by decide) (by decide) (by decide +kernel)
private theorem normal299 : (hankel (cubeSeq (ZMod 53)) 299).det ≠ 0 :=
  certified 0xb82b0bb0da628d7628b60292ad255e8b31d20e25d76853a210dbc91e5c12c22c576032b194dcb4b723278a170388616c65d4f094536d0d02af42c41ec12c22c576032b194dcb4b723278a170388616c65d4f094536d0d02af42c41ec12c22c714c1d113cc3a1b5393180f7552941d83e698d758b922d038e8e8a2a8c6896890b09a89a0c4d279d34856b8ca8e05d30ae8f24de79bc274f1a06b2e4058c54c479dcab110a030480e9393519c93bf025c622150c2823296b1a52655c58c54c4122d01926a6750889111599882b86e7663cfa187478ea9679d234d2d2bd37d2b07 normal298 (by decide) (by decide) (by decide +kernel)
private theorem normal300 : (hankel (cubeSeq (ZMod 53)) 300).det ≠ 0 :=
  certified 0x2b94e8e92b1b5f73175d584ab1563c0d2840ef21d2279957ce8411e25089c86a466e9b345b7517d4d0691bac67ad89a88e7ccb8190b38c12faa0c4d9d09c86a466e9b345b7517d4d0691bac67ad89a88e7ccb8190b38c12faa0c4d9d09c86a466ea709ce647a032877e59c361778e5c12892a735829c4a665c65db1a8497e9aa3bd232b10859911861fc4b120485a2bc721ad62d38f8169d4d2e4e1b4eb5b45c1cf0a4698916841bd168abd72136d39d6a47d11aa7a7118b544a0e94eb5b45c1cc14e9dcb8dcabb9640ec9d7979ded2bb2b3a876b6633dc65c6096d4b162d58ad normal299 (by decide) (by decide) (by decide +kernel)
private theorem normal301 : (hankel (cubeSeq (ZMod 53)) 301).det ≠ 0 :=
  certified 0x6722a072d1a7ab9513f39cda60bcb7cf02343274101631b3d446b59815f90a6ea82e78d26571f64101f4acbdd351566bd96a2991b868230d362f3162d890a6ea82e78d26571f64101f4acbdd351566bd96a2991b868230d362f3162d890a6ea82e7ab35005ec9d40a2f3a699668607c6c931ab5efaca94942e954229d070ea3331340c16d729092608ea0c546a969804a50d8d007e96a686429f770591ada2d51d7a2c41959cd005a32466289203c671b4cf907bd54b289d1a97ea751ada2d51d72a89745c3625aea08c3103d4556bc38af29e18aad0b251d086d301bb1282bc7 normal300 (by decide) (by decide) (by decide +kernel)
private theorem normal302 : (hankel (cubeSeq (ZMod 53)) 302).det ≠ 0 :=
  certified 0xeaa0a647db4e591518b2698cb9daa64b0ca47432869c0e3f22dfa2971e0a98d86c60095e795bd2e419a6b61fcccb446107f426aced800b9448db66188a9d8d86c60095e795bd2e419a6b61fcccb446107f426aced800b9448db66188a9d8d86c60095e71d01743ad312ad064a3a00aa50c9c456112bb6eb521259df5c78c492ad341566a241182faac312a8e6cc449a4cba50d43059e60ea58d3195f331275abc0b1e3906811e570c29d582a48c5d95606c2c2215007863a083efb4b61275abc0b1e3ae9700672298ca95cae75732e1a4ec605312881c88f140e59eb92c0359634c normal301 (by decide) (by decide) (by decide +kernel)
private theorem normal303 : (hankel (cubeSeq (ZMod 53)) 303).det ≠ 0 :=
  certified 0x30f0903c14cfce980790498485ea950642207e58a411460982c6337eac53aa5aea81ea735d93e35c84ad3960612b2861aa5964c8188c8f434d86665e230241aea81ea735d93e35c84ad3960612b2861aa5964c8188c8f434d86665e230241aea81ea735d93eaaee384291bec063a5d4950d5760ca2146d1049eb4bae25899e368a345422982315b91c4fc545cb83446d55641347185db1525d0962c488b40a2d55cc09e72649eb632277f452b0d450b410443d13a52068a143dc5ed16cd0a2d55cc09e7262ca1e7c6b90627448c6238328185434f0bc19635c8a8a4dfb0d18ca58864 normal302 (by decide) (by decide) (by decide +kernel)
private theorem normal304 : (hankel (cubeSeq (ZMod 53)) 304).det ≠ 0 :=
  certified 0x23704a1710895a86a51bc6ec302cc1468c79f197309f4e45423d7aafa25909016a67641a304607a215d3a708ace42e988eb13c1c0e3c1e52b8419981a08106d2a67641a304607a215d3a708ace42e988eb13c1c0e3c1e52b8419981a08106d2a67641a304607a298a9211b2b66092b873e86068f41c55cb78111dbf4a527f0c2cb09957a506d42e16841c516aa70bd2b8e1100b35a2460ce678b18d411b007cc39cd0d1645574f06273b3ac246a3139c98856724855e1294d0f76f55595a8cc39cd0d1645574cfad152f0c83f38c7ba635dbd206ec1ea97d3160604c8d611788512e684 normal303 (by decide) (by decide) (by decide +kernel)
private theorem normal305 : (hankel (cubeSeq (ZMod 53)) 305).det ≠ 0 :=
  certified 0x1d44e7d131eb574906ac22f360b8729e1d0e0a4ca310b00914f51fb4d155aa592690791694f5c8bc19a3626bc81154f36e25179da0e8a201de0207d2c6f1931e090791694f5c8bc19a3626bc81154f36e25179da0e8a201de0207d2c6f1931e090791694f5c8bc19814c224bc3084da17c9862149c512a2ab347685c23e1020999a12411120051bcacea09da940ce5019f34434b1a80b309a1588a3080b4113d1b917d099eb46d0f49d3c6b7182209a4e178e6f234d56e5c05568c41af8ae551b917d099eb46d0fd22ceca85154a0d78375d5236618cd2c905835ece65343b025b912746 normal304 (by decide) (by decide) (by decide +kernel)
private theorem normal306 : (hankel (cubeSeq (ZMod 53)) 306).det ≠ 0 :=
  certified 0x1179b86bbe48180c37556c178055399f456628c0e2f29748c26325232920eeb996f26edc26d31349c5624c570a0e59e16637255e6cec64acb37435a2484a83a04d26edc26d31349c5624c570a0e59e16637255e6cec64acb37435a2484a83a04d26edc26d31349c5624cb8a1940632ecc13c25d2942a29a41044c94826a0ad6d642311b60dcb2c9881ad1702088f5a47dd3459ea0d0052cdd0e14ab8f21c771a0da2053c1128b047eca6014d9df5f03e80e05da9c444aaa80686ecb633675628da2053c1128b047eca47aef8744aa2458854013252eb6e5964a50b6c2f31c904a98682e220 normal305 (by decide) (by decide) (by decide +kernel)
private theorem normal307 : (hankel (cubeSeq (ZMod 53)) 307).det ≠ 0 :=
  certified 0x2a6474d23114031d28b0668c56015e8828612899a14339085a8a26cadb6c6060ae8b37678a49a67b07a31648998273587d7c4e9a321457051908ea56356aa01e382b7678a49a67b07a31648998273587d7c4e9a321457051908ea56356aa01e382b7678a49a67b07a316489f22776060db9b2605b3ae71400ad5a6a3398f722b44813b015b3c41349bdba605705d3cd452bb0f525091b5f34d3c320825dbf31d309839344f3d71574b04537153a87567849cf4ad8601617339cc7e87cb56e49529839344f3d71574b04535ad39855da076ac55f08a3b003321f3cd08f9982578168dbc0b088 normal306 (by decide) (by decide) (by decide +kernel)
private theorem normal308 : (hankel (cubeSeq (ZMod 53)) 308).det ≠ 0 :=
  certified 0x48d044739365848d15c4554466997e40e7246b66ca1d24b97c140169556ac86c19121d6a161b4b36abceaa992d51ef88740a970c986ca323602046a268702dcc438426a161b4b36abceaa992d51ef88740a970c986ca323602046a268702dcc438426a161b4b36abceaa992d53e25594e6c5d2df54712d280b1c6d331d8c085506bc914923c7370664824bdb7164723acbc83c35014477858407d081b25426f92d61b51d6a309b2822cb72a82e193ba5ad014375aae949dcf4bcd3d416a644c94cdb51d6a309b2822cb72a8264e07223c462a5a0bb122b00965a8a9612d10ca4bb159028e71b normal307 (by decide) (by decide) (by decide +kernel)
private theorem normal309 : (hankel (cubeSeq (ZMod 53)) 309).det ≠ 0 :=
  certified 0xc21a742174a5a4529108c9e0c0972e84a0aca0068e6dd19998748e1122aa3d485a7e900faee36d3cb8985067434a032495b4e80e94af9d3150aa632630f88982531ece7aee36d3cb8985067434a032495b4e80e94af9d3150aa632630f88982531ece7aee36d3cb8985067434a03226e2beb9e06a3920a1e6ec4a1bd42585cda0e6cb4e26ee9691f3a4e545b191d4af324d01b9da62f70fba39f18eb2e68546d630098a1e8226a93761bd8ca35694506a237232318e8b094b3e93e9993b154295c238a1e8226a93761bd8ca35694da4c628e55b49154d5da26350686c75db61cdb88b06a4cb09d normal308 (by decide) (by decide) (by decide +kernel)
private theorem normal310 : (hankel (cubeSeq (ZMod 53)) 310).det ≠ 0 :=
  certified 0x3052a54c3a1386cd0c2d02e5e800369a7cb14aa8130a3c19afb656894aa98702c56a42c465688ce3a8712c80da0bc04cc9262b2095e86d9e24cbb2766865112c01374c891688ce3a8712c80da0bc04cc9262b2095e86d9e24cbb2766865112c01374c891688ce3a8712c80da0bc04cc96a82167d4cc46027d9512b01a1b6d18e8253ceb51260f156a401de340c9b6d6ab0acbd29ae6d0f18841bb232cfb802602e526441bb4248bbb1255a0da85c42b2c4c95505d420e4e2a8939c35c931240898a5391bb4248bbb1255a0da85c42b1b36d7d6842c5dcd67218c9d0d69a8d7b8236bc40557a20914 normal309 (by decide) (by decide) (by decide +kernel)
private theorem normal311 : (hankel (cubeSeq (ZMod 53)) 311).det ≠ 0 :=
  certified 0x266a4fb69809974b571c629b7e5a0cb6c2a0b1a71a709ac7be992fc732a5a5f9cc1de7012895989a81ca484c08c6a888791622a5e46162396f71016e3c7b5949e680ae1d275989a81ca484c08c6a888791622a5e46162396f71016e3c7b5949e680ae1d275989a81ca484c08c6a8887916097aa4549a120d12a62272b1ad54029120c18026361726362b69640da4826b5496d96d9b0ab863111840ab40c58ea6e5d9d2bb1f74f36eae3c45b442d3b5791d4cc5e451d4901999701e6b887235db00a50139f74f36eae3c45b442d3b5791db172e484f52da312dd4d92af21fb05c1ec4656389e9952d7 normal310 (by decide) (by decide) (by decide +kernel)
private theorem normal312 : (hankel (cubeSeq (ZMod 53)) 312).det ≠ 0 :=
  certified 0x1930f6e301ac5e3505e83a370a3e142d04428b9d03091d802a1105974e6d0c12202146e2138d89508b27f09340223c2608aa6074ae710a0f1ce3ae2344663b93256b6e7d85239508b27f09340223c2608aa6074ae710a0f1ce3ae2344663b93256b6e7d85239508b27f09340223c2608aa60742971206cf91f7b29c31ef4d49e3134a6a30d30f940498759ae6525234c6ba8e969b2e7402f195f7a23c1a714c05241ed8927509530d61510404e6cddb4b3f404a3b1af210248a4e8c5c4878ac7c81d67614909530d61510404e6cddb4b3f406b7b155a9915970cecae1a282a1a26de2cfb0b6407b03ea normal311 (by decide) (by decide) (by decide +kernel)
private theorem normal313 : (hankel (cubeSeq (ZMod 53)) 313).det ≠ 0 :=
  certified 0x58c49720d25910fc461dda42a318aa75894ca954c61969148a07dc1ded005e85f2ad7ac07008444a5a930c65a67a4729c23ab1bf445104a9a61d2b3359266a5d95031b47661b04a5a930c65a67a4729c23ab1bf445104a9a61d2b3359266a5d95031b47661b04a5a930c65a67a4729c23ab1bf444b5c071cb8bc12ac419da8f245c2faac0da494baf266a8d1132d8750a4b822bef7d185355666e5c101e35e0ca78a019014c6340b8b2bdf3d745930548b106064934acf3ee8c909f8dc2de721caf0583ef16340b8b2bdf3d745930548b106064a9e019647a858cac6f60a4207a3cf30195d4941d0f6c9 normal312 (by decide) (by decide) (by decide +kernel)
private theorem normal314 : (hankel (cubeSeq (ZMod 53)) 314).det ≠ 0 :=
  certified 0x272ac1063824e2cb081d850b851963f034800ec4371c2ef3aa6ef1609d7bed307ca230428a32c4d3d0885722b52d42e4aea8e5c1cc59aa1f4865a5005e26e6206e08408ef142c97d0885722b52d42e4aea8e5c1cc59aa1f4865a5005e26e6206e08408ef142c97d0885722b52d42e4aea8e5c1cc59aa01bcd779bc2e286ae3cc540bc335cb45806e20dc26d2f7e6168b409c4c9966a1a72da1b054e786229b834e9c6bae9262881b547ad2a12251e31cb9ded02c0f2ee05440c9745ec1dd55a5540121b0cc3781b547ad2a12251e31cb9ded02c0f2c06827976851ebbca4509ae9b4a5c5c28047101ea5b1 normal313 (by decide) (by decide) (by decide +kernel)
private theorem normal315 : (hankel (cubeSeq (ZMod 53)) 315).det ≠ 0 :=
  certified 0x10d1281333df5691c42522acd17c1b7e114a3d6a5f61f684a008816114c201bba93d208b6618507e4593994ced69688996465fc0376068a2559c9c03827a640985e95c588d3983e7593994ced69688996465fc0376068a2559c9c03827a640985e95c588d3983e7593994ced69688996465fc0376068a2476450401965451d4689ca52ef1688ceac03d8466845696530ae67cc59d59bc4d013d1d922cc06873268f3a9c51495645f88f84221b7d3b1045c585c9855baec80eb05c9538c47375e31ec13a2776639f88f84221b7d3b1045c585c9855baecb9cc3402f7e0c2d74ea1032cb11b5e806b144ed432 normal314 (by decide) (by decide) (by decide +kernel)
private theorem normal316 : (hankel (cubeSeq (ZMod 53)) 316).det ≠ 0 :=
  certified 0x34b140225cd8951347343d588ca9da0b1c9302009b9639b2e0943a9fb9da729e1d0808378fbc79d609046174b9e12ee4c66d28988ccc8f4223ea363d269336704f37d390998ecb25ee46174b9e12ee4c66d28988ccc8f4223ea363d269336704f37d390998ecb25ee46174b9e12ee4c66d28988ccc8f4223eaae4a4509f9d714fab05100a759945fc1d9de42004daaeb29cc0b077e76aa550c8b58760c0ce501b73c97986b8e7f3964518a8e52a1e2bda8d3752a439a54e62e84813d109c162096891b0f9c30de1e4518a8e52a1e2bda8d3752a439a54e62ca44cc3358e771bec1743a684a625bc626ea99817 normal315 (by decide) (by decide) (by decide +kernel)
private theorem normal317 : (hankel (cubeSeq (ZMod 53)) 317).det ≠ 0 :=
  certified 0x7801db8db9a782826f8a6cdb8c14c4b328d5b266a739cad58d7bddae879e39a5e33e37704b36a71f4bad24ab4ec59c6ebeb0d22c5c4c58c8664e394d4c92676607dcb677e8232a2a8a324ab4ec59c6ebeb0d22c5c4c58c8664e394d4c92676607dcb677e8232a2a8a324ab4ec59c6ebeb0d22c5c4c58c8664e3960b333d91516a314d9d12e5187ca0125973a969c90d28093db3a764a81278660a3575e76de4a649816309b3ae04722cac89c47041c62b28eac04a5fa543e2490a22b2c39c55664839636d0cd2d34acac89c47041c62b28eac04a5fa543e24905490a672f19b2d5168cc3947949a0b4aa50a30a normal316 (by decide) (by decide) (by decide +kernel)
private theorem normal318 : (hankel (cubeSeq (ZMod 53)) 318).det ≠ 0 :=
  certified 0x158d47097aa8aad0c5301282719cd7428d99c341d457ba38d9a876882092830e828d4e2698748aaa3227606836ed7dfb6a24f2e7bca45733029ea18a5e29151231481f6908c83ac9cd3726836ed7dfb6a24f2e7bca45733029ea18a5e29151231481f6908c83ac9cd3726836ed7dfb6a24f2e7bca45733029ea18a5e5d55cdc33059168a9548e9a1c823501a94c841270eca562478749270bb9bb6db2bcb236ba224db758b4b2e94d855bc9a2165882ec9aa386ae47a916b5cd74c5eb9218e985559b952b6724ea280dbc9a2165882ec9aa386ae47a916b5cd74c5de81e9e5520027916ceea03008bc0733695423 normal317 (by decide) (by decide) (by decide +kernel)
private theorem normal319 : (hankel (cubeSeq (ZMod 53)) 319).det ≠ 0 :=
  certified 0x40d0e2680a731455ef188870c9552f0e71242b0c8576934b6d1d2d42ba34168547472485598830752669c3296fa4e5443cd087555d0b7ad3184175d18a61ee76056c19644c5480af2eacdf96fa4e5443cd087555d0b7ad3184175d18a61ee76056c19644c5480af2eacdf96fa4e5443cd087555d0b7ad3184175d18a61d17ac3ac15d1946f4a925ea84949d2131c0c3146b143c18328a9a90122528d070360ba40e3c1f7551588dc3050d018c9e0c66a33ba0801a9722976579e9133ee1d856026f7e4a60b731aa2c259018c9e0c66a33ba0801a9722976579e9133ee916b9a18ecefb5cc4632414c2e86d83b4c93 normal318 (by decide) (by decide) (by decide +kernel)
private theorem normal320 : (hankel (cubeSeq (ZMod 53)) 320).det ≠ 0 :=
  certified 0x16b9e51e8c4cb23449090d9bec4dbab180671d92b9e2b5d008a4aac498600f5d3c9ed1d75e0aa0d995f487c1125cada82f61f8d39403310b47734d4502b29a5d1a1c910f3367c5764c90ec2925cada82f61f8d39403310b47734d4502b29a5d1a1c910f3367c5764c90ec2925cada82f61f8d39403310b47734d4502b29a5cbea4d8c6418c1a696c3086741d61dd2d549961128e4c8600b4cacac4fbc099e8835c16185f32f27105a3b8592c64a6d519d5928900291330580a2861cc930c62f5039320a838479ca519c532c64a6d519d5928900291330580a2861cc930c62548425b8ebb3208c6a0a831c23138ee01d normal319 (by decide) (by decide) (by decide +kernel)
private theorem normal321 : (hankel (cubeSeq (ZMod 53)) 321).det ≠ 0 :=
  certified 0x55cc2a5a352e1482f4317b815c8c6e88c9d346dbdd91fbdd1d86302828074044202f2b6952d584b2d10692e0a122ca49bae383b6ebeb8722f344b3275446ee402967cc34f2a45162c005ab9a722ca49bae383b6ebeb8722f344b3275446ee402967cc34f2a45162c005ab9a722ca49bae383b6ebeb8722f344b3275446ee3e226f22a1e17958b04288da02c8b00459b2a2420661158662e75d16bcd5ba5c6556a0c832121fc49231bd11f352d24cb071e7c881c62940ea0a4aa93a0c5a1e5cd0382ca20ccc304c501f28f3ad24cb071e7c881c62940ea0a4aa93a0c5a1e5cd02c3a8b01e6cbbe60708b49cb24638346f normal320 (by decide) (by decide) (by decide +kernel)
private theorem normal322 : (hankel (cubeSeq (ZMod 53)) 322).det ≠ 0 :=
  certified 0x125d55ae40c0ae7d97e32169673e1bdf3a426b7043c53121cc0ed59672ec1925ab8a0ad1ea62505e8af50e7050af331c2b3c572084488a2c0712d16b44a5969e0112eebea22801ad0889dce01ab331c2b3c572084488a2c0712d16b44a5969e0112eebea22801ad0889dce01ab331c2b3c572084488a2c0712d16b44a5969d8efad81c1b4539f74949d88f283894949b30199c66c298eea7221f7d91c572c6c7af322e2dd4345d31a19d9c331a91052a6c19554c53aea0198c17c8c4c71b5c092a1c62ed3406c1b5360256f2a91052a6c19554c53aea0198c17c8c4c71b5c092a1c0931baeb343404320448e79e679ac44 normal321 (by decide) (by decide) (by decide +kernel)
private theorem normal323 : (hankel (cubeSeq (ZMod 53)) 323).det ≠ 0 :=
  certified 0x3655d4d14bdfc5b4f146f2e86de4994201116a8a8bc23b4eaac40e5e2b5a9dd08e36f3405f292c8a304d33416c85d6a19efc915da39c2e29a23d3b93531af415799c5c45c43d2c920e070ccd9ae56a19efc915da39c2e29a23d3b93531af415799c5c45c43d2c920e070ccd9ae56a19efc915da39c2e29a23d3b93531af410a0450c50c97dd1ec224355a2a1a5bc08aa46554ba854889cb2659de4c86ce6339e81a801e0d12534b4a2907025461b50e18391e6e766a4cf4e68878a110a07078f65ec5ec668c38f2559a4270a41b50e18391e6e766a4cf4e68878a110a07078f65ec5ecac713af102e55a951ce29681d3aed normal322 (by decide) (by decide) (by decide +kernel)
private theorem normal324 : (hankel (cubeSeq (ZMod 53)) 324).det ≠ 0 :=
  certified 0x2f2cc09465c62d3da5000d027024b7b2b6e39bce8c2200826ccde0831d518c9af122085904bef00889e8dd12caa50c448c0d5c8a0141ad64cbc59c69505717250dec0f96baf444f5814d6cdfb4f41c48c0d5c8a0141ad64cbc59c69505717250dec0f96baf444f5814d6cdfb4f41c48c0d5c8a0141ad64cbc59c695057172425390d4523dc11f9629eea88320347c42bea10f9454c0b6c2425f3cae82fa4f1b14f3c11c46180b535d263124b432c63a72803ac086f21ca46c0ebd09601194325c599028a06499fd227c25889a5663a72803ac086f21ca46c0ebd09601194325c599028a0441ebd0e13092e31d40718dc96a1d normal323 (by decide) (by decide) (by decide +kernel)
private theorem normal325 : (hankel (cubeSeq (ZMod 53)) 325).det ≠ 0 :=
  certified 0x1242228918aba1ac1f3621de3542e865404e7911200c31eb96674e1488207248188304409a2883be66d8a15b1a8a07a044d6cfac839f5ee7e4c0b7100efcd3c972183d7912d1d7464d6ad71b278c6f344d6cfac839f5ee7e4c0b7100efcd3c972183d7912d1d7464d6ad71b278c6f344d6cfac839f5ee7e4c0b7100efcd3c536508aa4e526a0c3b660cbc560622df8ce29342ea32cae2903d89f0b5555945575516400f4d3c863da74d8096d3557564a1a98ab6759e1d6445a999721828837ad7667918c1618be27ca7af0d7a5a0a4a1a98ab6759e1d6445a999721828837ad7667918c161809e0908db4a0202cb399d1140e2 normal324 (by decide) (by decide) (by decide +kernel)
private theorem normal326 : (hankel (cubeSeq (ZMod 53)) 326).det ≠ 0 :=
  certified 0x1b24d5987c65ddcc89d152fb92ac6447b978d3c2cb077c5b5578d4abb12a4e4cf05aaebbda4163e3182b2b26c8070d4bcc2cb38974f8f451b01f6c4bdc197489383292274bcd79470f3865e50a32c2a1f2cb38974f8f451b01f6c4bdc197489383292274bcd79470f3865e50a32c2a1f2cb38974f8f451b01f6c4bdc197488a2fcb1995a6b05651d24bc965201c62555e924db02316c08817a232898cc9e29b46ca2866e57e64afcc92ac255bb2846a6aaa7b1899206168059ac4666f7a3b27cab8ec046a178599a7bde4334aaccd5aaaa7b1899206168059ac4666f7a3b27cab8ec046a1785999b58998f7e87a59c7799b521e2 normal325 (by decide) (by decide) (by decide +kernel)
private theorem normal327 : (hankel (cubeSeq (ZMod 53)) 327).det ≠ 0 :=
  certified 0x507266a54d2166d75671b1a1ccf40594478a3aa4805de7e921bb25a1d261a1678338309e3ae512884122389a6f22ec88b9c9e47cf270a2f067cd7b891ae3079c68723599890d3bcbc1840e5107805ec7839e47cf270a2f067cd7b891ae3079c68723599890d3bcbc1840e5107805ec7839e47cf270a2f067cd7b891ae3079a76a972548a5ef0a36b1a9e54fb5c99204230848890ecd632d68940d62c50d7d7ca7cb35e71e18d3c714e7b0c1ad1c3b4764e4569ac14d1b4382787b2f1e9b8ebd40e870fb32886a857659e195701e257c8e4569ac14d1b4382787b2f1e9b8ebd40e870fb32886a85765474a2e24acf055f7ee6d1419 normal326 (by decide) (by decide) (by decide +kernel)
private theorem normal328 : (hankel (cubeSeq (ZMod 53)) 328).det ≠ 0 :=
  certified 0x25934aa45de56dc2b6228812a899ac052a9bdbc1118da07af304ea52a084668d928b917bde79eb91cf49976523028e17c469089f1098474b3942a9269c024a41027524cc676b725344774363a1fbc38f2cea89f1098474b3942a9269c024a41027524cc676b725344774363a1fbc38f2cea89f1098474b3942a9269c024a4040356f3e4d1692a5e1c1231985e83161f7620911b38664ca0b49cc8cdb643d272ba917865d75c790204f79c8e9cd2516c5b9535b1b14ba3090ccb8db64044cd003a1442bd8299428c5806848d586c920c22d35b1b14ba3090ccb8db64044cd003a1442bd8299428c580684a19b0258324658a5ec4771b normal327 (by decide) (by decide) (by decide +kernel)
private theorem normal329 : (hankel (cubeSeq (ZMod 53)) 329).det ≠ 0 :=
  certified 0x7f348b24f41701426b80952b6283422f414749e6800cf60999fc716096850b152732dce5291a4975c3660701970605dd22b0c21dd4a488aa854738903c46d508a1ead19663630c81a4f4a49d56b1bd1b032501dd4a488aa854738903c46d508a1ead19663630c81a4f4a49d56b1bd1b032501dd4a488aa854738903c46d5060258a502930707adce4250c729cf706a9cb07a33a61ce314f58411db1bc331213a920242b90cb186683f416f7b455e62d2b2cee623453acbc24093966c5a833aee2c171c49d143d0c9a344e81b106909cac96e623453acbc24093966c5a833aee2c171c49d143d0c9a344e81b65790c50272474c468be7 normal328 (by decide) (by decide) (by decide +kernel)
private theorem normal330 : (hankel (cubeSeq (ZMod 53)) 330).det ≠ 0 :=
  certified 0x205015dd459b12af0b069695856cbb2c08c71bc5948945cb2502d9008e0aa912d266532774700b613af4306464157e508594a918c214aa32ab2800eadccacc11388c480ec6455dd2dbb7215fc7285d322ca7ad0c214aa32ab2800eadccacc11388c480ec6455dd2dbb7215fc7285d322ca7ad0c214aa32ab2800eadccacc108e9c266db00e1674249cd449b175a62df34508652d53105020021101254b33122c3e10d80590085271a515cbe5816433c10ad17455232e92c93409ca643245927b44b7225cc1e62a6880f05840d46294c338a9455232e92c93409ca643245927b44b7225cc1e62a6880f05840d463351c518cc8ad8a18b88 normal329 (by decide) (by decide) (by decide +kernel)
private theorem normal331 : (hankel (cubeSeq (ZMod 53)) 331).det ≠ 0 :=
  certified 0x9522229577927cbccca2c62909d560344aa6b84100549ce16b494986f7503a31a25e8226b1212f76e78892d58878e7a6d1c30a903a2b64800c71a40d8e496c4644c651724b0b14cc992bb30ab4c828a18acd1b5ba2b64800c71a40d8e496c4644c651724b0b14cc992bb30ab4c828a18acd1b5ba2b64800c71a40d8e496c4340739e79e295220e69f09b3a9ae87f20accb1add6676a96e4650b141989674af4de36d3c98f11981d7b5121fb579d73c1669ad1c8d29cb40a596e5a12450264462be17acab3122a4f8c70b32a2b6baefac290868d29cb40a596e5a12450264462be17acab3122a4f8c70b32a2b6baef5122c651cb923aeb1d normal330 (by decide) (by decide) (by decide +kernel)
private theorem normal332 : (hankel (cubeSeq (ZMod 53)) 332).det ≠ 0 :=
  certified 0x376a52c5491e1b2f11292f3d605b8053678ebd348f4924ca7acd5d091598a41278469262165f9d598a1afb6c84519599b0f4565c595c115a758093d1ca813a00d01c4b3339a3229d44aac1a34128cc038e1a672dc5c115a758093d1ca813a00d01c4b3339a3229d44aac1a34128cc038e1a672dc5c115a758093d1ca8139f0284a501e15382bb5000604bb00921aebc73185b5c7b1cd7419ade95180fae58d7c5b8dd51c58e80faef188254c2f80f6b206040471ed306d877388164bd2757296ec490a76e94ce8632c56e8d2ba45c9250c3aa65ed306d877388164bd2757296ec490a76e94ce8632c56e8d2ba45c92504c49ad85538739b2 normal331 (by decide) (by decide) (by decide +kernel)
private theorem normal333 : (hankel (cubeSeq (ZMod 53)) 333).det ≠ 0 :=
  certified 0x2d984b844a92b10213003287024813b05b17c1571521c06148e0313125438134ea5c71820541b0243811ca681a62261a543cd870cb614dc08db11b86c48b95262a5c14e0abb525743015e75ccc6195a06c9d9d065954dc08db11b86c48b95262a5c14e0abb525743015e75ccc6195a06c9d9d065954dc08db11b86c48b95217430be2cc16db16cb8151d40c3414a3c4041e7e681936854685eb698e0c958a22debafcf486f16cc959033d56dd4dd6e0c82759a48522673a09907bc4b4782c4cc6709f32888e0069d1e39ea445106f424e701bdf822673a09907bc4b4782c4cc6709f32888e0069d1e39ea445106f424e701a0050c3347465cc normal332 (by decide) (by decide) (by decide +kernel)
private theorem normal334 : (hankel (cubeSeq (ZMod 53)) 334).det ≠ 0 :=
  certified 0x290ed3f0c6c88d9828e069296b0eeb0e6580301acbe481b1715304a1511b6c1653e3c1ba2074e3981ec0c82739f20da3227925688308c070d25b845b87717696a1aae4815999b3026da892de60206704282617336aa8f70d25b845b87717696a1aae4815999b3026da892de60206704282617336aa8f70d25b845b87717695d17cd5959bec7ca1ca2a4bae8b4230a1e2262ad5b0997ba03ced2a8e190827042648568d5589e776e272b6c08e0f26e94d78e0355152019a2c694c07b9979b7cd6ca45580f70916c20bb2a5ddcf43b4cd53f00a82cb999a2c694c07b9979b7cd6ca45580f70916c20bb2a5ddcf43b4cd53f00a82e0ce142a4c6ba6 normal333 (by decide) (by decide) (by decide +kernel)
private theorem normal335 : (hankel (cubeSeq (ZMod 53)) 335).det ≠ 0 :=
  certified 0x324b0478fbea0619d9c031811f132502f388548380745630357d2ea450de54aa467077540c86271e66c8468bb45892f15d71a6204d0455502295f705782bd3ab019b65a241a9f531186b92b4d2e0cdd7f43aa5e884875b02295f705782bd3ab019b65a241a9f531186b92b4d2e0cdd7f43aa5e884875b02295f705782bd3a645e4571bc701ea0a88baccb063d439d9661953da8606252423632d40725e0accbd9b98872b5d3ae3dab6434705fb2a11e7af3edc41c608004d0599c17cc688b16f69c6ecd0b5a112fbc78c8a2a5426160672de354b586804d0599c17cc688b16f69c6ecd0b5a112fbc78c8a2a5426160672de354b58b719914f1b6f normal334 (by decide) (by decide) (by decide +kernel)
private theorem normal336 : (hankel (cubeSeq (ZMod 53)) 336).det ≠ 0 :=
  certified 0x35cbd1d1148a8557ccd8b380c0f4089a147c37f251658729a2b0bc0553c293f21ac3856834988a08441ac3564004905e60886734c0828797b0c5e36a45457aa51529a44fb4e7b156c31baf1469a0691e6c1a56acdb59b90b0c5e36a45457aa51529a44fb4e7b156c31baf1469a0691e6c1a56acdb59b90b0c5e36a45457a9473d1ba4b661adcceed2eb51166a446eb1d79acbae5c39c6cce4939b06c53260ef267c1bca3753554c6f2687e502395e3f3b5c0a2015357789a5e49b460c172e182b6e49889d712026968a12430dbd15dad0c7caa08707949a5e49b460c172e182b6e49889d712026968a12430dbd15dad0c7caa0870795d768a0f947 normal335 (by decide) (by decide) (by decide +kernel)
private theorem normal337 : (hankel (cubeSeq (ZMod 53)) 337).det ≠ 0 :=
  certified 0xad62454acc1a1a503495408d92c3963c479469f56d74170334ca60a1482c227441a299cf67229a66701498a59f0e18f3ced2001c51192a11cd5ee7475086291e58184900ab92d92005eb9a4cbb8128843286b55c292159ace5ee7475086291e58184900ab92d92005eb9a4cbb8128843286b55c292159ace5ee7475086291af28f3732f02a7d200ae69819c0a8a6e314351ac74aa132a012d23886442ad3a4d0d30e99c0eb6dc38084fadf5b251208222d02ec3172b52ea1e1d8ba1b5d32e4157639732912115745c76e2a87d2bb650d42a066b8f070a9de1d8ba1b5d32e4157639732912115745c76e2a87d2bb650d42a066b8f070a9debc7148474 normal336 (by decide) (by decide) (by decide +kernel)
private theorem normal338 : (hankel (cubeSeq (ZMod 53)) 338).det ≠ 0 :=
  certified 0xf8d764f4ded21372293c34c2f81ec251060499307efc895d5d187826421ca949652596213a2372c34a1c0bd966d5cca960b296c61b8b41ca5a50eac9382e40fb99aae5a01951d460e3539e074b1064ed1c44e2bde5c51e3ad70eac9382e40fb99aae5a01951d460e3539e074b1064ed1c44e2bde5c51e3ad70eac9382e40e7eb4d51cd7566c76c4bd8a258e06cb8e90432b3d34748ccc59880c11c5ce750b1c8df7ed88d499268aee00671c21ea4b7f30d025d69306eadf4322c38951e598770b1df56f82e85d9e888e558ab1be222ec624c65dec2e48a7b22c38951e598770b1df56f82e85d9e888e558ab1be222ec624c65dec2e48a7b22ef01c80e normal337 (by decide) (by decide) (by decide +kernel)
private theorem normal339 : (hankel (cubeSeq (ZMod 53)) 339).det ≠ 0 :=
  certified 0x2130541693f04dd4260a6a61c0caacb87a72584ad00d03b150d59dc72c1800e9a97e6905a974eec4561011913369d3218a94635221592cd0db74006262d3236672210e2c68cdec147474609743c5b0d1e106a76085ab651c9cdc06262d3236672210e2c68cdec147474609743c5b0d1e106a76085ab651c9cdc06262d32361faa091d2190cb4c4b0582c1040d001402d11466a4577572ea9866666c92d638f3163d1c0b7a21c4c1d97173109b6295133244a14f072aa326980344dd22949c3ad5324c43425c5858ba4550066c09a2e5342d85546c842eb026744dd22949c3ad5324c43425c5858ba4550066c09a2e5342d85546c842eb026744ddc527d9 normal338 (by decide) (by decide) (by decide +kernel)
private theorem normal340 : (hankel (cubeSeq (ZMod 53)) 340).det ≠ 0 :=
  certified 0x1d249329a880a15f3549c418d20a501d20fa045c95ca52875ec4286b8006eaa247a008f66f2e30e066322c774967bdf1d62a491142ab5759e2a3828cee5cdcadc0c409a703d284ebd004491e8d68ae3477f39283c69953c05f446ecee5cdcadc0c409a703d284ebd004491e8d68ae3477f39283c69953c05f446ecee5cdcac4c31f20061d002cc70b488f0454cae97440b8111a4701718b833cd20e5e77335d757399c1aa4b255c4ad2580503865ae7eb4519252c879f5eb4953421dea03205a65b0c1668d49c6974c515d27d31e8b96091366bcf82601e0641c21dea03205a65b0c1668d49c6974c515d27d31e8b96091366bcf82601e0641c21dea243ef normal339 (by decide) (by decide) (by decide +kernel)
private theorem normal341 : (hankel (cubeSeq (ZMod 53)) 341).det ≠ 0 :=
  certified 0xc2eaca51c98fba8c9772129a398c2f32c08dab30ee5aab2629988e3e93a0cc3065b2f4d199e3dd5ac58bc887ef2ce3c07427334f378910ba6e210d1060a9ca560d144736e86c86b38aa28c8041cc7cd1012b1cd035cd23ce04a44f060a9ca560d144736e86c86b38aa28c8041cc7cd1012b1cd035cd23ce04a44f060a9ca52519e1dfd0230f9c12ce7821ab911941374c8700d5062ac356b821619311cc453c091a290f5e661f25fa83b561aa9e6018cd90a2097b31a8c1ed94195daceae054186409a35ab5b0932eba55c6ea56a31d2b10296864148256346215daceae054186409a35ab5b0932eba55c6ea56a31d2b10296864148256346215daceae1855 normal340 (by decide) (by decide) (by decide +kernel)
private theorem normal342 : (hankel (cubeSeq (ZMod 53)) 342).det ≠ 0 :=
  certified 0xe8a69436b3929533522746ac83e53011cc6b28e0cc095dad865f297b109d786e9598913904a222159036581359a214d055658c1219d041a7061b1c0ec8d32925f128f1af88145dced7d0509c5d752829adb0d5ce1916ad552b2254a58d32925f128f1af88145dced7d0509c5d752829adb0d5ce1916ad552b2254a58d329124f65f0d5912749019ca8393a4eb467e27c11a74e392639fc5279bc2e4e1a2541f5539279634ed51f96841589f6ed841c20412d2d701c6f3b45096722528ab8de12b9af193d24602216961b046188d530a6b28025117ca8212ad4234128ab8de12b9af193d24602216961b046188d530a6b28025117ca8212ad4234128ab92c987 normal341 (by decide) (by decide) (by decide +kernel)
private theorem normal343 : (hankel (cubeSeq (ZMod 53)) 343).det ≠ 0 :=
  certified 0x130a4a07425654cb7423301e15177431ba44b40086153694293c744897eda0eb27557a21ba68f095810425f8045abb2fb9801aa482585db32178e64e4ed6a3a458316952330d3aa7a4f3556053e52c4aed06ebd42b25415063016b36c86a3a458316952330d3aa7a4f3556053e52c4aed06ebd42b25415063016b36c86a3a0194841426a8b37afa873d5bc0cc832d404c81bd212d09c031b856e149e8b068ace8b8d5073d2150771c6c595c5f2891877406ccb6c75e6a95179dc9e221b48cc1511b82d0b288b38c9a881dc2642ac4a2341c686b0e0d21be9d1b09ab5b48cc1511b82d0b288b38c9a881dc2642ac4a2341c686b0e0d21be9d1b09ab5b48dd10b65 normal342 (by decide) (by decide) (by decide +kernel)
private theorem normal344 : (hankel (cubeSeq (ZMod 53)) 344).det ≠ 0 :=
  certified 0x223dc3749f262128f993a26b6804416d8c91195a52c6ccd3eabd574f68f5024535246e01994b4a26415b0d212aeca06967508ba446b62d5b31634c7558cb24a75d98a936724dc235c73ac388c879d77c6ac743446f517d174001317de64b4a75d98a936724dc235c73ac388c879d77c6ac743446f517d174001317de64b4a6a8a19c38032a3d9216c047502868d29d8883b1e8643999c86c69144042ac4155eb5c18ef72304d3e5809a2d8ca24dbd03a1b4746429d21f0b04a2ba07430e339e7133283aca0549eba7267b43b8e796bcaba50641a17817a50311165dcaa339e7133283aca0549eba7267b43b8e796bcaba50641a17817a50311165dcaa33cbaef667 normal343 (by decide) (by decide) (by decide +kernel)
private theorem normal345 : (hankel (cubeSeq (ZMod 53)) 345).det ≠ 0 :=
  certified 0x5d625a06c0af49a26ece1c5f594ad93c725053485c2ed8097f27296ca3f39d5504b15ceba54c470590c0b8b531c94cde4c89271e80427a09e0bd1b5fae0218c325d5a34c82bec3a83c98f394d3cc26aa11452b4b31526282660b4e00ae19ec325d5a34c82bec3a83c98f394d3cc26aa11452b4b31526282660b4e00ae19ebdb04c3b318001aa5f58b0821acc1695b848073b9f94a4425c76e47c5b5f22c687c95b8040c844bb4732007aa11038425e2b513ae374cd754e54690858a56d7450de80d043cc6267366b12090a26a6c2cd9248c8aa982c4d53ddaa25731ef5c50de80d043cc6267366b12090a26a6c2cd9248c8aa982c4d53ddaa25731ef5c66b4a670af normal344 (by decide) (by decide) (by decide +kernel)
private theorem normal346 : (hankel (cubeSeq (ZMod 53)) 346).det ≠ 0 :=
  certified 0x1dae054834c04f74eac36e6b027291cfaa10d1591965ad82f04992aa3103958d2ad232ed00a40c813c005b3f172818509b85a8ef00486e04163181b9ee1aad0d8803326110013dd51d14c0527057449a7580497d2432a6e4774820c5a8c50c18803326110013dd51d14c0527057449a7580497d2432a6e4774820c5a8c50c014a85d404a400001a70a641b69ea725f2ab20418f47340d98a21d61ce4ec8d2a143d15c5a4c003d260346a611936fc336946d2180c541f4d1d11568e1ef2c1a130290dd900d26621630a748d9c18c4f39f0237814692da4580555446d2c32d130290dd900d26621630a748d9c18c4f39f0237814692da4580555446d2c32030ad4625c4c normal345 (by decide) (by decide) (by decide +kernel)
private theorem normal347 : (hankel (cubeSeq (ZMod 53)) 347).det ≠ 0 :=
  certified 0x5066f28693727a2591a9692d8cb025b30bc2b4819fbee8913cc5ce5d452b5a231b784ab199b459865924065aa57165669ac28316d8c06a389c91c9805d16c532e15d1a642f49e89644ca411419a276845044a3080a06471c741483465a821b8e15d1a642f49e89644ca411419a276845044a3080a06471c741483465a821b6fd022457225400000174d23536e2b715963d210262681aaed13249d146a8b2e3659150831be471441147440b4197e03cf26bcb021201b49365164f01e91ac291f062f3e51a35d37e4a4cd30d0f4d8364964ae9b7355cbaeba585505c6d55079f062f3e51a35d37e4a4cd30d0f4d8364964ae9b7355cbaeba585505c6d5508181cecc194e0 normal346 (by decide) (by decide) (by decide +kernel)
private theorem normal348 : (hankel (cubeSeq (ZMod 53)) 348).det ≠ 0 :=
  certified 0xd7985c255f605a5222ec438909e74aba33aa56a3b95203bd03d4c723e540d0e63252736df5681510ef48e8d878e4ce6c9031b4868852e4931c40a2034ce015c28d14f0c00a72a9488bb110560f39c8d68af070388362cc9a2902ea61ae197465214f0c00a72a9488bb110560f39c8d68af070388362cc9a2902ea61ae19733298ad06060f14000000005821d70ab6390545680fb5ac0f61a872b121916306ddca40c5baf4b09321a39d27579e29dab00108b5bb611e38aec734c004257066ba309b20333ab323b47131c1d9a76527d31b4167b684c2b0d3001cc50a51005c8f09b20333ab323b47131c1d9a76527d31b4167b684c2b0d3001cc50a5100a931323455d9b0 normal347 (by decide) (by decide) (by decide +kernel)
private theorem normal349 : (hankel (cubeSeq (ZMod 53)) 349).det ≠ 0 :=
  certified 0x77128f965360d349d2b0a10528596f36a1c1a5c0b0bf2ba835a5899982c8a22258703962cc17ef2c219f45b62e76220f5cb5a710b25114c103c95b96663d07a2b674cc96dc3d38274ac28415594c36e7a27087c57c75c659bbd6ad2bd263209ab60cc96dc3d38274ac28415594c36e7a27087c57c75c659bbd6ad2bd2632072c56919acf91484000000000b81c4e1a5b6d40c390d68d8ce5408a15c740a52966f8692518ea9eacef5a469d1d84ed99ea9f3b1aac930a71c838077dc481b8d29c042b1a6668953a326bc70810a681d74d9b56c16b9ebdf6867ca8c68dd0f36c8542b1a6668953a326bc70810a681d74d9b56c16b9ebdf6867ca8c68dd0f40c47d170a991854 normal348 (by decide) (by decide) (by decide +kernel)
private theorem normal350 : (hankel (cubeSeq (ZMod 53)) 350).det ≠ 0 :=
  certified 0x1a1266aeb276e70e88440b394f64595a46c4476a95709e4693021ac31d95a10dd44fd2d918705a4d51986bac1373a51be44316a58af599aad16c1ad54934b8266cc69136f525157b61102ce53d92183089026d41d265418191a603c1125f8d395fb9636f525157b61102ce53d92183089026d41d265418191a603c1125f8d22db23150388a4d41400000000000e89ecb6652f4f27a25dc45ab0db4a94908f8cabb27142a33a0b6171428ad2808c90646511b41319f70b23026f220b28a953daa5b9281a1430788531cc242672d769b51cda86e8dc86fd116ddc8592c5928905877e81a1430788531cc242672d769b51cda86e8dc86fd116ddc8592c5928ea6ad121c93ae2870 normal349 (by decide) (by decide) (by decide +kernel)
private theorem normal351 : (hankel (cubeSeq (ZMod 53)) 351).det ≠ 0 :=
  certified 0x599aca6a792c4df24d78a7d7c47a86ccb2c34d16d20917e5bf03e2947787c178d1318cd30303a838dc18664bad7d686a033ce786ca2b080640bee45c118291c88700460283b925f195e29f5f11ea1a6c1e11d51ac70806ae88c915e192a2944a6ed103283b925f195e29f5f11ea1a6c1e11d51ac70806ae88c915e192a29429082bde6140b4b6860000000000002895304a0f47ee3dc1aea2f62ed2986eb869ab5e01541e615a2c575c4472167d42c008239424d2b301c0061e467176b903b5902456bc878de1105eb59e12e2ef3c55f16216c4155bca352b305ef8cd324ada231cabc878de1105eb59e12e2ef3c55f16216c4155bca352b305ef8cd325333cc65dd87304835d normal350 (by decide) (by decide) (by decide +kernel)
private theorem normal352 : (hankel (cubeSeq (ZMod 53)) 352).det ≠ 0 :=
  certified 0xb456c4a1e4856b718598c9b1145ea6ad26b005ef711874608c8b712413aec81f42704b4e7b4e6424e0aae28d22350ccd2651aaea748619ad35e2826b24b28b40e2550ba05281433047a326c4517a9ab47c98ca76c886b6e469b416870442e42918204655281433047a326c4517a9ab47c98ca76c886b6e469b416870442e3d002a41de94790b418140000000000000b928e88d045ab9626c89a22c8ce503565623c4bccf5a738568b1eba2d4a1a428dc90b1cc05450f2285ebcdb0e30d30724e0947561370ca9c574ac26491730b056b12ad8253bc81e4308d1bbb4c6a46b915564421370ca9c574ac26491730b056b12ad8253bc81e4308d1bbb4c6a48102b46e5d0b91aa5770 normal351 (by decide) (by decide) (by decide +kernel)
private theorem normal353 : (hankel (cubeSeq (ZMod 53)) 353).det ≠ 0 :=
  certified 0xc1cc1a19541365850b3b4615592456819cc9701d111c01273c4c9eaec1299413c554c366c86920bef3807745cd75f7b350ca601da089a995e3b47b4a10284c012213a02961020b6c80d2185564915a067326a9ed8859d52a04e0c72c68c9b6b43e82d792a020b6c80d2185564915a067326a9ed8859d52a04e0c72c68c9b644a2d9913da88755857424000000000000000e9ae4739d16113e34c716426b62a8d868479d718a9e6e625805ea185970a1a4c56e6f3b0b71e488b88af1cd4a408ed88dcd0500548255a2d7607e391f55c0ac2ce213c0e82b5625440c434369b06636a7912c0548255a2d7607e391f55c0ac2ce213c0e82b5625440c434369cc4d20f9266d3ba076006c normal352 (by decide) (by decide) (by decide +kernel)
private theorem normal354 : (hankel (cubeSeq (ZMod 53)) 354).det ≠ 0 :=
  certified 0x142dca4b11f26a69c490b310a351810619228bbd89b14e6ba20c709425b3a81565319d4bcf5b43db01b46836564979bbaf7c6bee5028c0719c83b4faaec1865d86034094dae94d8359a974c28d460418648a2ef78d32811104a2dea1db441d48c92e6b2758b4d8359a974c28d460418648a2ef78d32811104a2dea1db441d33f3932863b027b39876a05c000000000000000019c4154d850711c5144ab50eb9fa0b3697617e42c7d0f92841cb17687196bc61e1cd2019703c8898b1c575c614568010a0a32276870b7a2cd285dc6fbe3aea197a29371934aea5cd608c6e852b2a3c939faa276870b7a2cd285dc6fbe3aea197a29371934aea5cd608c6e8a60910d4489cd708fb9b55e normal353 (by decide) (by decide) (by decide +kernel)
private theorem normal355 : (hankel (cubeSeq (ZMod 53)) 355).det ≠ 0 :=
  certified 0x356b2d765230284441c03026a5f68a0409822840550d122dce465b780b0342125105b0d71a571b1605a35738275562613e400f6594991095eed097687116c03b435012c46a6f3c8dced0d34697da28102608a101566082c20743373b999dec328490293aab9ec8dced0d34697da28102608a101566082c20743373b999debe52d220c7a2cd4bb1cb20138000000000000000000239af0e2b9f9d5ba290e39cbd18891dc3ad4ec49c4b38953a07ec52644099c723731b1e1c1b1835991a0270689712642da083a022328a43166ebd003f3af1d203f3cc5558ca808770e5c50d4b003272c75c3a022328a43166ebd003f3af1d203f3cc5558ca808770e5c642a8eda574c28471030c0895 normal354 (by decide) (by decide) (by decide +kernel)
private theorem normal356 : (hankel (cubeSeq (ZMod 53)) 356).det ≠ 0 :=
  certified 0x836f46f3cf516891bd57612f3b1db971c3a8194ecd729126e6404563f359dc11a2374f4c4aaf19ad317e1c8362bb60665b8e095a5fc2ca5f3c316e7a00db261134c942893cfb58805a4c62c36c76e5c70ea0653b35ca73441a51c4e85415d0ac20a355dcc6667805a4c62c36c76e5c70ea0653b35ca73441a51c4e85415cf8ea2126ce9270c53cb524b213c00000000000000000002eb5c150bc995e0bd44826aa330832274a8c6052e431d28855c4079f380c58524c5a6cb01d75726ac53104386bb26988755c0ca5d2682581debb22f442709ead90656e1662360d1e94acf34a0602bdc395c0ca5d2682581debb22f442709ead90656e1662360d1e9922ed8da9d13b2c26aa1449526 normal355 (by decide) (by decide) (by decide +kernel)
private theorem normal357 : (hankel (cubeSeq (ZMod 53)) 357).det ≠ 0 :=
  certified 0x6572059d420cadf62c0f0ae36ad299527c6820e4f25a254b9cda675c86290049281532f409514cb4798c3912495f119744f4f20ad4165d832c2a5b713ccc16463d006deb9e92b9436991d154a7ca6549f1a08393c968952cc6e200bcb4551ce19abb4c3ea29d56a6991d154a7ca6549f1a08393c968952cc6e200bcb4551c883e3a1ac22ce7ad28d631b9e59c000000000000000000001a3ae3a9a9c851b9971e54fc607a27da72500d59c79e12f7a49a20f32257de76926b408126a457e448101a5c75d1290c9b72e920ad6adc84e10db678837d382aa5a4c0a8306090250f288a662eb6202db72e920ad6adc84e10db678837d382aa5a4c0a83060903b6648d6c54c238a8d27e968e40e normal356 (by decide) (by decide) (by decide +kernel)
private theorem normal358 : (hankel (cubeSeq (ZMod 53)) 358).det ≠ 0 :=
  certified 0x1c8628149e23c568c6a55e9700b0a10c631ca72f18844861db5855628319e9152c5b7d309f2d402f44c82d1634cea887d47ec8256c50a3be1323b8e4a23d26187da0a7a42c12627ccc9565e2c8a004318c729cbc621121876d674290c6cfa2543332c442bc07a44429565e2c8a004318c729cbc621121876d674290c6cfa24a527ccc9036664a15d0348c6c93ac00000000000000000000006220a17ddd1f5d61227ce8db14a2cca54ac13c074bb5685625541ac334865294879e34e68dd7566f338ccc58dd382a507de4c3ac0c697440cea844f18efb9a7d8cd1a5a98d4250a9264cc6017464cd07de4c3ac0c697440cea844f18efb9a7d8cd1a5a98d44c8d6a439683dcaf0600052bc388a normal357 (by decide) (by decide) (by decide +kernel)
private theorem normal359 : (hankel (cubeSeq (ZMod 53)) 359).det ≠ 0 :=
  certified 0xd199572c793380c3026c8a39dcd06557988702d0b3677453220abbaf8ee1afd0300438f82401f581ccf267d0d61224a2b4817ad22572d03d5b8b84dc21b6c80a399bd42074c705b9286e51d08522155e621c0b42cd9dd14c882adc36bb29b4d8037dba6b5a07e00aa6e51d08522155e621c0b42cd9dd14c882adc36bb29b0a3d22b4c8d0d27e51e190365e1530800000000000000000000000234c8ce3c8b3121a68e251200f1a356f9dfb7096caeb05578a8ec7aa966807a94a05508255ae770686dba2bb469135a42e9548ed81e3ed67306aa0e630a53cca668289308a15c9668c29f5565732da42e9548ed81e3ed67306aa0e630a53cca668289309ae68eb043a328d642e511c9c5f08b3 normal358 (by decide) (by decide) (by decide +kernel)
private theorem normal360 : (hankel (cubeSeq (ZMod 53)) 360).det ≠ 0 :=
  certified 0x4897b30ae432030c90db8d50c8db988bd12e1a51155cd25709ab8c041cd314254eb0599f0aee68f5d59e14e0772acb61a4ee32e80f9f30ac17434406d3d888a1eac4caac181270b9ac17d226f024776f44b869445573495c26ae30107ab9df8e1bc63b01285ca18846cd226f024776f44b869445573495c26ae30107ab9de7f460f4c555cb33bd91339ce3cd8d65400000000000000000000000000acacebe188ebd36a6cd980290c1b09259a029d6e21e91d598e0b3270068c74226753aee2c4a4b26fd2c1476c57814da16cb981a4a94324c200a38053ca48095728e592506be717135eaefb642414da16cb981a4a94324c200a38053ca48095728e5d605d9a2c2064908673108e9e6a127e0 normal359 (by decide) (by decide) (by decide +kernel)
private theorem normal361 : (hankel (cubeSeq (ZMod 53)) 361).det ≠ 0 :=
  certified 0x7ea159862a1d1a4c6a0719743a7a2256289971a534b30ab4be77160c9bde51971c50ed314f354071f81d3ae40e828b059e791d822616b61151306c1016472080bd18a6776ad1988608bccc2816176087a265c694d2cc2ad2f9dc58326f79b5c574992375f5e456c9819882816176087a265c694d2cc2ad2f9dc58326f79b59ba042c2c2cbde9b0c40a982e89a4ae8c40000000000000000000000000007cb4325c83d19c4999449534a4986040f1b0e3916154dd7c8530929bc5970459555a8174c3982c1713bf3a82a6bd1d79db574dc65b8412452c118e65fcac19769ec18b1149859e46024fd0fb6bd1d79db574dc65b8412452c118e65fcac19769f68dc6acc52465cf14400b76a34f44a344 normal360 (by decide) (by decide) (by decide +kernel)
private theorem normal362 : (hankel (cubeSeq (ZMod 53)) 362).det ≠ 0 :=
  certified 0x8a600e85acb483ca9c0184bd2482653053183196162d04bc7617a090f419b4f244fb1eab288575a9a38aa9a37966098d2302274ce3beb07007212e1afc97cc711dc5f2ec5ed6cc38e419c733699d08872c60c65858b412f1d85e8243d066d40aca455f312b5c79731e80ab3699d08872c60c65858b412f1d85e8243d066d3bc324291d3733ed6cc1e2cf1c1796c3c6b40000000000000000000000000000ca7bcb1a841129005b64024b36e3d41986e9cec0424862b41740f11ef183782bb16045aa25e21aa679e57040a830e953baabf2bdfc130711ae75e36cc81bda87324cc1e0b129eb900ae3732a830e953baabf2bdfc130711ae75e36cc81bda886caccd16280a621aa6e4c2105790266bc8 normal361 (by decide) (by decide) (by decide +kernel)
private theorem normal363 : (hankel (cubeSeq (ZMod 53)) 363).det ≠ 0 :=
  certified 0x364216ab3bc75d66c6118aa34efb5da32842a092c51c285bc33aab24c994257a2b1999e7a28266549661b034eb8e239d3e40cd38d411b95a9ca930d396ac1e25ea110e80d954584999c3f23ee6e8821cc492824b1470a16f0ceaac93265096006a448e789789a6a85f2339db6e8821cc492824b1470a16f0ceaac93265095e8adcc5980f5e74cf6db9491088700ee058880000000000000000000000000000016627b9c91e8af48211206aacd5a0649cf2a27a2590780b64b8b28902c55ec5cd932372720c14b0f6660e61da355502c5136cab0bb351a1422cab293e1b1d01b4639d7b17b0c2d45ad08e69a355502c5136cab0bb351a1422cab293e1b1e34a64471599e3a299a690b31b541721f4753 normal362 (by decide) (by decide) (by decide +kernel)
private theorem normal364 : (hankel (cubeSeq (ZMod 53)) 364).det ≠ 0 :=
  certified 0x1782638241451bd173f18115ad88b7093c19c57510189823af2a60c7a8ccd9cec46b85cb4e190631ad739e56744f5436c00526631cf55f342c66a0caf48002e4466a325cc32ec2a1c440945bacdd1a0e79e79dd44062608ebca9831ea3336743b172f01e9119a852d383a4caefd1a0e79e79dd44062608ebca9831ea333673b11ae1cce4322e9c9e49862bccda73bd89808800000000000000000000000000000005d60acc11068c0abd633169eb329b441c4ae9a05a8cc43cda4a05502a4643cd0dea691c52eec65b2468aa016f238e38e62401d3f39c6acfcae2e909c0671191805d190f361227c8ca4a1816f238e38e62401d3f39c6acfcae2e909c08990a5029e50ea3035e375d282a0c08674f013 normal363 (by decide) (by decide) (by decide +kernel)

theorem base53 (n : ℕ) (lo : 177≤n) (hi : n≤364) :
    (hankel (cubeSeq (ZMod 53)) n).det ≠ 0 := by
  by_cases h271 : n < 271
  ·
    by_cases h224 : n < 224
    ·
      by_cases h200 : n < 200
      ·
        by_cases h188 : n < 188
        ·
          by_cases h182 : n < 182
          ·
            by_cases h179 : n < 179
            ·
              by_cases h178 : n < 178
              ·
                obtain rfl : n = 177 := by omega
                exact normal177
              ·
                obtain rfl : n = 178 := by omega
                exact normal178
            ·
              by_cases h180 : n < 180
              ·
                obtain rfl : n = 179 := by omega
                exact normal179
              ·
                by_cases h181 : n < 181
                ·
                  obtain rfl : n = 180 := by omega
                  exact normal180
                ·
                  obtain rfl : n = 181 := by omega
                  exact normal181
          ·
            by_cases h185 : n < 185
            ·
              by_cases h183 : n < 183
              ·
                obtain rfl : n = 182 := by omega
                exact normal182
              ·
                by_cases h184 : n < 184
                ·
                  obtain rfl : n = 183 := by omega
                  exact normal183
                ·
                  obtain rfl : n = 184 := by omega
                  exact normal184
            ·
              by_cases h186 : n < 186
              ·
                obtain rfl : n = 185 := by omega
                exact normal185
              ·
                by_cases h187 : n < 187
                ·
                  obtain rfl : n = 186 := by omega
                  exact normal186
                ·
                  obtain rfl : n = 187 := by omega
                  exact normal187
        ·
          by_cases h194 : n < 194
          ·
            by_cases h191 : n < 191
            ·
              by_cases h189 : n < 189
              ·
                obtain rfl : n = 188 := by omega
                exact normal188
              ·
                by_cases h190 : n < 190
                ·
                  obtain rfl : n = 189 := by omega
                  exact normal189
                ·
                  obtain rfl : n = 190 := by omega
                  exact normal190
            ·
              by_cases h192 : n < 192
              ·
                obtain rfl : n = 191 := by omega
                exact normal191
              ·
                by_cases h193 : n < 193
                ·
                  obtain rfl : n = 192 := by omega
                  exact normal192
                ·
                  obtain rfl : n = 193 := by omega
                  exact normal193
          ·
            by_cases h197 : n < 197
            ·
              by_cases h195 : n < 195
              ·
                obtain rfl : n = 194 := by omega
                exact normal194
              ·
                by_cases h196 : n < 196
                ·
                  obtain rfl : n = 195 := by omega
                  exact normal195
                ·
                  obtain rfl : n = 196 := by omega
                  exact normal196
            ·
              by_cases h198 : n < 198
              ·
                obtain rfl : n = 197 := by omega
                exact normal197
              ·
                by_cases h199 : n < 199
                ·
                  obtain rfl : n = 198 := by omega
                  exact normal198
                ·
                  obtain rfl : n = 199 := by omega
                  exact normal199
      ·
        by_cases h212 : n < 212
        ·
          by_cases h206 : n < 206
          ·
            by_cases h203 : n < 203
            ·
              by_cases h201 : n < 201
              ·
                obtain rfl : n = 200 := by omega
                exact normal200
              ·
                by_cases h202 : n < 202
                ·
                  obtain rfl : n = 201 := by omega
                  exact normal201
                ·
                  obtain rfl : n = 202 := by omega
                  exact normal202
            ·
              by_cases h204 : n < 204
              ·
                obtain rfl : n = 203 := by omega
                exact normal203
              ·
                by_cases h205 : n < 205
                ·
                  obtain rfl : n = 204 := by omega
                  exact normal204
                ·
                  obtain rfl : n = 205 := by omega
                  exact normal205
          ·
            by_cases h209 : n < 209
            ·
              by_cases h207 : n < 207
              ·
                obtain rfl : n = 206 := by omega
                exact normal206
              ·
                by_cases h208 : n < 208
                ·
                  obtain rfl : n = 207 := by omega
                  exact normal207
                ·
                  obtain rfl : n = 208 := by omega
                  exact normal208
            ·
              by_cases h210 : n < 210
              ·
                obtain rfl : n = 209 := by omega
                exact normal209
              ·
                by_cases h211 : n < 211
                ·
                  obtain rfl : n = 210 := by omega
                  exact normal210
                ·
                  obtain rfl : n = 211 := by omega
                  exact normal211
        ·
          by_cases h218 : n < 218
          ·
            by_cases h215 : n < 215
            ·
              by_cases h213 : n < 213
              ·
                obtain rfl : n = 212 := by omega
                exact normal212
              ·
                by_cases h214 : n < 214
                ·
                  obtain rfl : n = 213 := by omega
                  exact normal213
                ·
                  obtain rfl : n = 214 := by omega
                  exact normal214
            ·
              by_cases h216 : n < 216
              ·
                obtain rfl : n = 215 := by omega
                exact normal215
              ·
                by_cases h217 : n < 217
                ·
                  obtain rfl : n = 216 := by omega
                  exact normal216
                ·
                  obtain rfl : n = 217 := by omega
                  exact normal217
          ·
            by_cases h221 : n < 221
            ·
              by_cases h219 : n < 219
              ·
                obtain rfl : n = 218 := by omega
                exact normal218
              ·
                by_cases h220 : n < 220
                ·
                  obtain rfl : n = 219 := by omega
                  exact normal219
                ·
                  obtain rfl : n = 220 := by omega
                  exact normal220
            ·
              by_cases h222 : n < 222
              ·
                obtain rfl : n = 221 := by omega
                exact normal221
              ·
                by_cases h223 : n < 223
                ·
                  obtain rfl : n = 222 := by omega
                  exact normal222
                ·
                  obtain rfl : n = 223 := by omega
                  exact normal223
    ·
      by_cases h247 : n < 247
      ·
        by_cases h235 : n < 235
        ·
          by_cases h229 : n < 229
          ·
            by_cases h226 : n < 226
            ·
              by_cases h225 : n < 225
              ·
                obtain rfl : n = 224 := by omega
                exact normal224
              ·
                obtain rfl : n = 225 := by omega
                exact normal225
            ·
              by_cases h227 : n < 227
              ·
                obtain rfl : n = 226 := by omega
                exact normal226
              ·
                by_cases h228 : n < 228
                ·
                  obtain rfl : n = 227 := by omega
                  exact normal227
                ·
                  obtain rfl : n = 228 := by omega
                  exact normal228
          ·
            by_cases h232 : n < 232
            ·
              by_cases h230 : n < 230
              ·
                obtain rfl : n = 229 := by omega
                exact normal229
              ·
                by_cases h231 : n < 231
                ·
                  obtain rfl : n = 230 := by omega
                  exact normal230
                ·
                  obtain rfl : n = 231 := by omega
                  exact normal231
            ·
              by_cases h233 : n < 233
              ·
                obtain rfl : n = 232 := by omega
                exact normal232
              ·
                by_cases h234 : n < 234
                ·
                  obtain rfl : n = 233 := by omega
                  exact normal233
                ·
                  obtain rfl : n = 234 := by omega
                  exact normal234
        ·
          by_cases h241 : n < 241
          ·
            by_cases h238 : n < 238
            ·
              by_cases h236 : n < 236
              ·
                obtain rfl : n = 235 := by omega
                exact normal235
              ·
                by_cases h237 : n < 237
                ·
                  obtain rfl : n = 236 := by omega
                  exact normal236
                ·
                  obtain rfl : n = 237 := by omega
                  exact normal237
            ·
              by_cases h239 : n < 239
              ·
                obtain rfl : n = 238 := by omega
                exact normal238
              ·
                by_cases h240 : n < 240
                ·
                  obtain rfl : n = 239 := by omega
                  exact normal239
                ·
                  obtain rfl : n = 240 := by omega
                  exact normal240
          ·
            by_cases h244 : n < 244
            ·
              by_cases h242 : n < 242
              ·
                obtain rfl : n = 241 := by omega
                exact normal241
              ·
                by_cases h243 : n < 243
                ·
                  obtain rfl : n = 242 := by omega
                  exact normal242
                ·
                  obtain rfl : n = 243 := by omega
                  exact normal243
            ·
              by_cases h245 : n < 245
              ·
                obtain rfl : n = 244 := by omega
                exact normal244
              ·
                by_cases h246 : n < 246
                ·
                  obtain rfl : n = 245 := by omega
                  exact normal245
                ·
                  obtain rfl : n = 246 := by omega
                  exact normal246
      ·
        by_cases h259 : n < 259
        ·
          by_cases h253 : n < 253
          ·
            by_cases h250 : n < 250
            ·
              by_cases h248 : n < 248
              ·
                obtain rfl : n = 247 := by omega
                exact normal247
              ·
                by_cases h249 : n < 249
                ·
                  obtain rfl : n = 248 := by omega
                  exact normal248
                ·
                  obtain rfl : n = 249 := by omega
                  exact normal249
            ·
              by_cases h251 : n < 251
              ·
                obtain rfl : n = 250 := by omega
                exact normal250
              ·
                by_cases h252 : n < 252
                ·
                  obtain rfl : n = 251 := by omega
                  exact normal251
                ·
                  obtain rfl : n = 252 := by omega
                  exact normal252
          ·
            by_cases h256 : n < 256
            ·
              by_cases h254 : n < 254
              ·
                obtain rfl : n = 253 := by omega
                exact normal253
              ·
                by_cases h255 : n < 255
                ·
                  obtain rfl : n = 254 := by omega
                  exact normal254
                ·
                  obtain rfl : n = 255 := by omega
                  exact normal255
            ·
              by_cases h257 : n < 257
              ·
                obtain rfl : n = 256 := by omega
                exact normal256
              ·
                by_cases h258 : n < 258
                ·
                  obtain rfl : n = 257 := by omega
                  exact normal257
                ·
                  obtain rfl : n = 258 := by omega
                  exact normal258
        ·
          by_cases h265 : n < 265
          ·
            by_cases h262 : n < 262
            ·
              by_cases h260 : n < 260
              ·
                obtain rfl : n = 259 := by omega
                exact normal259
              ·
                by_cases h261 : n < 261
                ·
                  obtain rfl : n = 260 := by omega
                  exact normal260
                ·
                  obtain rfl : n = 261 := by omega
                  exact normal261
            ·
              by_cases h263 : n < 263
              ·
                obtain rfl : n = 262 := by omega
                exact normal262
              ·
                by_cases h264 : n < 264
                ·
                  obtain rfl : n = 263 := by omega
                  exact normal263
                ·
                  obtain rfl : n = 264 := by omega
                  exact normal264
          ·
            by_cases h268 : n < 268
            ·
              by_cases h266 : n < 266
              ·
                obtain rfl : n = 265 := by omega
                exact normal265
              ·
                by_cases h267 : n < 267
                ·
                  obtain rfl : n = 266 := by omega
                  exact normal266
                ·
                  obtain rfl : n = 267 := by omega
                  exact normal267
            ·
              by_cases h269 : n < 269
              ·
                obtain rfl : n = 268 := by omega
                exact normal268
              ·
                by_cases h270 : n < 270
                ·
                  obtain rfl : n = 269 := by omega
                  exact normal269
                ·
                  obtain rfl : n = 270 := by omega
                  exact normal270
  ·
    by_cases h318 : n < 318
    ·
      by_cases h294 : n < 294
      ·
        by_cases h282 : n < 282
        ·
          by_cases h276 : n < 276
          ·
            by_cases h273 : n < 273
            ·
              by_cases h272 : n < 272
              ·
                obtain rfl : n = 271 := by omega
                exact normal271
              ·
                obtain rfl : n = 272 := by omega
                exact normal272
            ·
              by_cases h274 : n < 274
              ·
                obtain rfl : n = 273 := by omega
                exact normal273
              ·
                by_cases h275 : n < 275
                ·
                  obtain rfl : n = 274 := by omega
                  exact normal274
                ·
                  obtain rfl : n = 275 := by omega
                  exact normal275
          ·
            by_cases h279 : n < 279
            ·
              by_cases h277 : n < 277
              ·
                obtain rfl : n = 276 := by omega
                exact normal276
              ·
                by_cases h278 : n < 278
                ·
                  obtain rfl : n = 277 := by omega
                  exact normal277
                ·
                  obtain rfl : n = 278 := by omega
                  exact normal278
            ·
              by_cases h280 : n < 280
              ·
                obtain rfl : n = 279 := by omega
                exact normal279
              ·
                by_cases h281 : n < 281
                ·
                  obtain rfl : n = 280 := by omega
                  exact normal280
                ·
                  obtain rfl : n = 281 := by omega
                  exact normal281
        ·
          by_cases h288 : n < 288
          ·
            by_cases h285 : n < 285
            ·
              by_cases h283 : n < 283
              ·
                obtain rfl : n = 282 := by omega
                exact normal282
              ·
                by_cases h284 : n < 284
                ·
                  obtain rfl : n = 283 := by omega
                  exact normal283
                ·
                  obtain rfl : n = 284 := by omega
                  exact normal284
            ·
              by_cases h286 : n < 286
              ·
                obtain rfl : n = 285 := by omega
                exact normal285
              ·
                by_cases h287 : n < 287
                ·
                  obtain rfl : n = 286 := by omega
                  exact normal286
                ·
                  obtain rfl : n = 287 := by omega
                  exact normal287
          ·
            by_cases h291 : n < 291
            ·
              by_cases h289 : n < 289
              ·
                obtain rfl : n = 288 := by omega
                exact normal288
              ·
                by_cases h290 : n < 290
                ·
                  obtain rfl : n = 289 := by omega
                  exact normal289
                ·
                  obtain rfl : n = 290 := by omega
                  exact normal290
            ·
              by_cases h292 : n < 292
              ·
                obtain rfl : n = 291 := by omega
                exact normal291
              ·
                by_cases h293 : n < 293
                ·
                  obtain rfl : n = 292 := by omega
                  exact normal292
                ·
                  obtain rfl : n = 293 := by omega
                  exact normal293
      ·
        by_cases h306 : n < 306
        ·
          by_cases h300 : n < 300
          ·
            by_cases h297 : n < 297
            ·
              by_cases h295 : n < 295
              ·
                obtain rfl : n = 294 := by omega
                exact normal294
              ·
                by_cases h296 : n < 296
                ·
                  obtain rfl : n = 295 := by omega
                  exact normal295
                ·
                  obtain rfl : n = 296 := by omega
                  exact normal296
            ·
              by_cases h298 : n < 298
              ·
                obtain rfl : n = 297 := by omega
                exact normal297
              ·
                by_cases h299 : n < 299
                ·
                  obtain rfl : n = 298 := by omega
                  exact normal298
                ·
                  obtain rfl : n = 299 := by omega
                  exact normal299
          ·
            by_cases h303 : n < 303
            ·
              by_cases h301 : n < 301
              ·
                obtain rfl : n = 300 := by omega
                exact normal300
              ·
                by_cases h302 : n < 302
                ·
                  obtain rfl : n = 301 := by omega
                  exact normal301
                ·
                  obtain rfl : n = 302 := by omega
                  exact normal302
            ·
              by_cases h304 : n < 304
              ·
                obtain rfl : n = 303 := by omega
                exact normal303
              ·
                by_cases h305 : n < 305
                ·
                  obtain rfl : n = 304 := by omega
                  exact normal304
                ·
                  obtain rfl : n = 305 := by omega
                  exact normal305
        ·
          by_cases h312 : n < 312
          ·
            by_cases h309 : n < 309
            ·
              by_cases h307 : n < 307
              ·
                obtain rfl : n = 306 := by omega
                exact normal306
              ·
                by_cases h308 : n < 308
                ·
                  obtain rfl : n = 307 := by omega
                  exact normal307
                ·
                  obtain rfl : n = 308 := by omega
                  exact normal308
            ·
              by_cases h310 : n < 310
              ·
                obtain rfl : n = 309 := by omega
                exact normal309
              ·
                by_cases h311 : n < 311
                ·
                  obtain rfl : n = 310 := by omega
                  exact normal310
                ·
                  obtain rfl : n = 311 := by omega
                  exact normal311
          ·
            by_cases h315 : n < 315
            ·
              by_cases h313 : n < 313
              ·
                obtain rfl : n = 312 := by omega
                exact normal312
              ·
                by_cases h314 : n < 314
                ·
                  obtain rfl : n = 313 := by omega
                  exact normal313
                ·
                  obtain rfl : n = 314 := by omega
                  exact normal314
            ·
              by_cases h316 : n < 316
              ·
                obtain rfl : n = 315 := by omega
                exact normal315
              ·
                by_cases h317 : n < 317
                ·
                  obtain rfl : n = 316 := by omega
                  exact normal316
                ·
                  obtain rfl : n = 317 := by omega
                  exact normal317
    ·
      by_cases h341 : n < 341
      ·
        by_cases h329 : n < 329
        ·
          by_cases h323 : n < 323
          ·
            by_cases h320 : n < 320
            ·
              by_cases h319 : n < 319
              ·
                obtain rfl : n = 318 := by omega
                exact normal318
              ·
                obtain rfl : n = 319 := by omega
                exact normal319
            ·
              by_cases h321 : n < 321
              ·
                obtain rfl : n = 320 := by omega
                exact normal320
              ·
                by_cases h322 : n < 322
                ·
                  obtain rfl : n = 321 := by omega
                  exact normal321
                ·
                  obtain rfl : n = 322 := by omega
                  exact normal322
          ·
            by_cases h326 : n < 326
            ·
              by_cases h324 : n < 324
              ·
                obtain rfl : n = 323 := by omega
                exact normal323
              ·
                by_cases h325 : n < 325
                ·
                  obtain rfl : n = 324 := by omega
                  exact normal324
                ·
                  obtain rfl : n = 325 := by omega
                  exact normal325
            ·
              by_cases h327 : n < 327
              ·
                obtain rfl : n = 326 := by omega
                exact normal326
              ·
                by_cases h328 : n < 328
                ·
                  obtain rfl : n = 327 := by omega
                  exact normal327
                ·
                  obtain rfl : n = 328 := by omega
                  exact normal328
        ·
          by_cases h335 : n < 335
          ·
            by_cases h332 : n < 332
            ·
              by_cases h330 : n < 330
              ·
                obtain rfl : n = 329 := by omega
                exact normal329
              ·
                by_cases h331 : n < 331
                ·
                  obtain rfl : n = 330 := by omega
                  exact normal330
                ·
                  obtain rfl : n = 331 := by omega
                  exact normal331
            ·
              by_cases h333 : n < 333
              ·
                obtain rfl : n = 332 := by omega
                exact normal332
              ·
                by_cases h334 : n < 334
                ·
                  obtain rfl : n = 333 := by omega
                  exact normal333
                ·
                  obtain rfl : n = 334 := by omega
                  exact normal334
          ·
            by_cases h338 : n < 338
            ·
              by_cases h336 : n < 336
              ·
                obtain rfl : n = 335 := by omega
                exact normal335
              ·
                by_cases h337 : n < 337
                ·
                  obtain rfl : n = 336 := by omega
                  exact normal336
                ·
                  obtain rfl : n = 337 := by omega
                  exact normal337
            ·
              by_cases h339 : n < 339
              ·
                obtain rfl : n = 338 := by omega
                exact normal338
              ·
                by_cases h340 : n < 340
                ·
                  obtain rfl : n = 339 := by omega
                  exact normal339
                ·
                  obtain rfl : n = 340 := by omega
                  exact normal340
      ·
        by_cases h353 : n < 353
        ·
          by_cases h347 : n < 347
          ·
            by_cases h344 : n < 344
            ·
              by_cases h342 : n < 342
              ·
                obtain rfl : n = 341 := by omega
                exact normal341
              ·
                by_cases h343 : n < 343
                ·
                  obtain rfl : n = 342 := by omega
                  exact normal342
                ·
                  obtain rfl : n = 343 := by omega
                  exact normal343
            ·
              by_cases h345 : n < 345
              ·
                obtain rfl : n = 344 := by omega
                exact normal344
              ·
                by_cases h346 : n < 346
                ·
                  obtain rfl : n = 345 := by omega
                  exact normal345
                ·
                  obtain rfl : n = 346 := by omega
                  exact normal346
          ·
            by_cases h350 : n < 350
            ·
              by_cases h348 : n < 348
              ·
                obtain rfl : n = 347 := by omega
                exact normal347
              ·
                by_cases h349 : n < 349
                ·
                  obtain rfl : n = 348 := by omega
                  exact normal348
                ·
                  obtain rfl : n = 349 := by omega
                  exact normal349
            ·
              by_cases h351 : n < 351
              ·
                obtain rfl : n = 350 := by omega
                exact normal350
              ·
                by_cases h352 : n < 352
                ·
                  obtain rfl : n = 351 := by omega
                  exact normal351
                ·
                  obtain rfl : n = 352 := by omega
                  exact normal352
        ·
          by_cases h359 : n < 359
          ·
            by_cases h356 : n < 356
            ·
              by_cases h354 : n < 354
              ·
                obtain rfl : n = 353 := by omega
                exact normal353
              ·
                by_cases h355 : n < 355
                ·
                  obtain rfl : n = 354 := by omega
                  exact normal354
                ·
                  obtain rfl : n = 355 := by omega
                  exact normal355
            ·
              by_cases h357 : n < 357
              ·
                obtain rfl : n = 356 := by omega
                exact normal356
              ·
                by_cases h358 : n < 358
                ·
                  obtain rfl : n = 357 := by omega
                  exact normal357
                ·
                  obtain rfl : n = 358 := by omega
                  exact normal358
          ·
            by_cases h362 : n < 362
            ·
              by_cases h360 : n < 360
              ·
                obtain rfl : n = 359 := by omega
                exact normal359
              ·
                by_cases h361 : n < 361
                ·
                  obtain rfl : n = 360 := by omega
                  exact normal360
                ·
                  obtain rfl : n = 361 := by omega
                  exact normal361
            ·
              by_cases h363 : n < 363
              ·
                obtain rfl : n = 362 := by omega
                exact normal362
              ·
                by_cases h364 : n < 364
                ·
                  obtain rfl : n = 363 := by omega
                  exact normal363
                ·
                  obtain rfl : n = 364 := by omega
                  exact normal364

end OMA.CubeHankel
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
