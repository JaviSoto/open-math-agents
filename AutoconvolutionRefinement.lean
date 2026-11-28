import Mathlib

/-! A strict, quantitative dyadic refinement for nonnegative equal-grid
step functions in the Sidon autoconvolution problem.  The rows are the
coefficients of the product of two generating polynomials. -/

namespace OMA.Autoconvolution
open Finset

private def row (n : ℕ) (k : ℤ) : Finset (Fin n × Fin n) :=
  univ.filter fun p => (p.1.val : ℤ) + p.2.val = k

noncomputable def coeff {n : ℕ} (a b : Fin n → ℝ) (k : ℤ) : ℝ :=
  ∑ p ∈ row n k, a p.1 * b p.2

private def shift {n : ℕ} (i : Fin n) : ℝ := 2 * (n : ℝ) - i.val
private def scale (n : ℕ) : ℝ := 10 * (n : ℝ)^2

noncomputable def left {n : ℕ} (a : Fin n → ℝ) (i : Fin n) :=
  (scale n + shift i) * a i
noncomputable def right {n : ℕ} (a : Fin n → ℝ) (i : Fin n) :=
  (scale n - shift i) * a i

private lemma shift_bounds {n : ℕ} (i : Fin n) :
    (n : ℝ) ≤ shift i ∧ shift i ≤ 2 * (n : ℝ) := by
  have h : (i.val : ℝ) ≤ n := by exact_mod_cast i.isLt.le
  unfold shift
  constructor <;> linarith [show 0 ≤ (i.val : ℝ) by positivity]

private lemma shift_sum {n : ℕ} {k : ℤ} {p : Fin n × Fin n} (hp : p ∈ row n k) :
    shift p.1 + shift p.2 = 4*(n : ℝ) - (k : ℝ) := by
  have ht : (p.1.val : ℤ) + p.2.val = k := (mem_filter.mp hp).2
  have h : (p.1.val : ℝ) + p.2.val = k := by exact_mod_cast ht
  unfold shift
  linarith

private lemma product_bounds {n : ℕ} (i j : Fin n) :
    (n : ℝ)^2 ≤ shift i * shift j ∧ shift i * shift j ≤ 4*(n : ℝ)^2 := by
  obtain ⟨li,ui⟩ := shift_bounds i
  obtain ⟨lj,uj⟩ := shift_bounds j
  have n0 := Nat.cast_nonneg (α := ℝ) n
  constructor
  · simpa [pow_two] using mul_le_mul li lj n0 (n0.trans li)
  · calc
      shift i * shift j ≤ (2*(n:ℝ))*(2*n) :=
        mul_le_mul ui uj (n0.trans lj) (by positivity)
      _ = _ := by ring

theorem halves_nonnegative {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hn : 0 < n) (i : Fin n) : 0 ≤ left a i ∧ 0 ≤ right a i := by
  have on : (1:ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨lo,hi⟩ := shift_bounds i
  unfold left right scale
  constructor <;> apply mul_nonneg _ (ha i) <;> nlinarith [mul_nonneg (sub_nonneg.mpr on) (Nat.cast_nonneg (α:=ℝ) n)]

theorem halves_mass {n : ℕ} (a : Fin n → ℝ) :
    (∑ i : Fin n, (left a i + right a i)) = 2 * scale n * ∑ i, a i := by
  rw [mul_sum]
  apply sum_congr rfl
  intro i _
  unfold left right
  ring

private lemma same_parity {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (k : ℤ) :
    coeff (left a) (left a) k ≤
      (scale n^2 + scale n*(4*(n:ℝ)-k)+4*(n:ℝ)^2)*coeff a a k ∧
    coeff (right a) (right a) k ≤
      (scale n^2 - scale n*(4*(n:ℝ)-k)+4*(n:ℝ)^2)*coeff a a k := by
  unfold coeff
  rw [mul_sum, mul_sum]
  constructor <;> apply sum_le_sum <;> intro p hp
  all_goals
    have h := shift_sum hp
    have hi := (product_bounds p.1 p.2).2
    have pos := mul_nonneg (ha p.1) (ha p.2)
  · unfold left
    calc
      _ = (scale n^2 + scale n*(shift p.1 + shift p.2) + shift p.1 * shift p.2) *
          (a p.1 * a p.2) := by ring
      _ ≤ _ := by rw [h]; exact mul_le_mul_of_nonneg_right (by linarith) pos
  · unfold right
    calc
      _ = (scale n^2 - scale n*(shift p.1 + shift p.2) + shift p.1 * shift p.2) *
          (a p.1 * a p.2) := by ring
      _ ≤ _ := by rw [h]; exact mul_le_mul_of_nonneg_right (by linarith) pos

/-- Even and odd coefficients of the doubled vector, before mass normalization.
For B(X)=L(X²)+X R(X²), these are [X^(2k)]B² and [X^(2k+1)]B². -/
theorem refinement {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i)
    (M : ℝ) (bound : ∀ k, coeff a a k ≤ M) (k : ℤ) (k0 : 0 ≤ k)
    (kmax : k ≤ 2*(n:ℤ)-1) :
    coeff (left a) (left a) k + coeff (right a) (right a) (k-1) ≤
        2 * (scale n^2 - (n:ℝ)^2) * M ∧
    coeff (left a) (right a) k + coeff (right a) (left a) k ≤
        2 * (scale n^2 - (n:ℝ)^2) * M := by
  have on : (1:ℝ) ≤ n := by exact_mod_cast hn
  have k0' : (0:ℝ) ≤ k := by exact_mod_cast k0
  have kt : (k:ℝ) ≤ 2*(n:ℝ)-1 := by exact_mod_cast kmax
  have big : 4*(n:ℝ)+1 ≤ scale n := by
    unfold scale
    nlinarith [mul_nonneg (sub_nonneg.mpr on) (Nat.cast_nonneg (α:=ℝ) n)]
  have s0 : 0 ≤ scale n := by unfold scale; positivity
  constructor
  · have hp := (same_parity a ha k).1
    have hm := (same_parity a ha (k-1)).2
    have cp : 0 ≤ scale n^2 + scale n*(4*(n:ℝ)-(k:ℝ))+4*(n:ℝ)^2 := by
      nlinarith [mul_nonneg s0 (show 0 ≤ 4*(n:ℝ)-(k:ℝ) by linarith)]
    have cm : 0 ≤ scale n^2 - scale n*(4*(n:ℝ)-((k-1:ℤ):ℝ))+4*(n:ℝ)^2 := by
      push_cast
      nlinarith [mul_nonneg s0 (show 0 ≤ scale n-(4*(n:ℝ)-((k:ℝ)-1)) by linarith)]
    refine (add_le_add hp hm).trans ((add_le_add
      (mul_le_mul_of_nonneg_left (bound k) cp)
      (mul_le_mul_of_nonneg_left (bound (k-1)) cm)).trans ?_)
    push_cast
    unfold scale
    apply le_of_eq
    ring
  · have hcoef : coeff (left a) (right a) k + coeff (right a) (left a) k ≤
          2 * (scale n^2-(n:ℝ)^2) * coeff a a k := by
      unfold coeff
      rw [← sum_add_distrib, mul_sum]
      apply sum_le_sum
      intro p _
      have hl := (product_bounds p.1 p.2).1
      unfold left right
      calc
        _ = 2*(scale n^2 - shift p.1*shift p.2) * (a p.1 * a p.2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg (ha _) (ha _))
    refine hcoef.trans (mul_le_mul_of_nonneg_left (bound k) ?_)
    nlinarith [mul_self_le_mul_self (Nat.cast_nonneg (α:=ℝ) n)
      (show (n:ℝ) ≤ scale n by linarith)]

/-- Direct convolution on the doubled grid, indexing its cells by an old
index and a bit. Offsets false/true select the left/right half respectively. -/
noncomputable def doubledCoeff {n : ℕ} (a : Fin n → ℝ) (j : ℤ) : ℝ :=
  ∑ p : Fin n × Fin n, ∑ s : Bool, ∑ t : Bool,
    if 2*((p.1.val : ℤ)+p.2.val) + (if s then 1 else 0) + (if t then 1 else 0) = j then
      (if s then right a p.1 else left a p.1) * (if t then right a p.2 else left a p.2)
    else 0

private lemma even_row {n : ℕ} (a : Fin n → ℝ) (k : ℤ) :
    doubledCoeff a (2*k) = coeff (left a) (left a) k + coeff (right a) (right a) (k-1) := by
  classical
  unfold doubledCoeff coeff row
  rw [sum_filter, sum_filter, ← sum_add_distrib]
  apply sum_congr rfl
  intro p _
  simp only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]
  split_ifs <;> first | omega | ring

private lemma odd_row {n : ℕ} (a : Fin n → ℝ) (k : ℤ) :
    doubledCoeff a (2*k+1) = coeff (left a) (right a) k + coeff (right a) (left a) k := by
  classical
  unfold doubledCoeff coeff row
  rw [sum_filter, sum_filter, ← sum_add_distrib]
  apply sum_congr rfl
  intro p _
  simp only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]
  split_ifs <;> first | omega | ring

/-- For a nonzero nonnegative n-bin input, every normalized convolution
coefficient of its 2n-bin refinement is at most (1-1/(100 n²)) times the
input's normalized maximum. The common denominator is its squared mass. -/
theorem normalized_refinement {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hS : 0 < ∑ i, a i) (M : ℝ) (bound : ∀ k, coeff a a k ≤ M)
    (j : ℤ) (j0 : 0 ≤ j) (jmax : j ≤ 4*(n:ℤ)-2) :
    4*(n:ℝ)*doubledCoeff a j / (∑ i : Fin n, (left a i + right a i))^2 ≤
        (1 - 1/(100*(n:ℝ)^2))*(2*(n:ℝ)*M/(∑ i, a i)^2) := by
  let k := j/2
  have r := refinement hn a ha M bound k (by dsimp [k]; omega) (by dsimp [k]; omega)
  have hj : doubledCoeff a j ≤ 2*(scale n^2-(n:ℝ)^2)*M := by
    by_cases he : j = 2*k
    · simpa only [he, even_row] using r.1
    · have ho : j = 2*k+1 := by dsimp [k] at *; omega
      simpa only [ho, odd_row] using r.2
  have nn : (0:ℝ) < n := by exact_mod_cast hn
  rw [halves_mass]
  refine (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hj (by positivity))
    (sq_nonneg _)).trans ?_
  apply le_of_eq
  unfold scale
  field_simp
  ring

end OMA.Autoconvolution
