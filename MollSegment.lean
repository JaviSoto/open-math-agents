import Mathlib

/-! Short segments of the Gaussian factorial are never real. The cone proof uses only
integer inequalities; it gives an explicit spacing obstruction for p-adic cancellation. -/
namespace OMA.MollSegment

open Finset

def core (n h : ℕ) : GaussianInt :=
  ∏ j ∈ range h, (⟨(n+j+1 : ℕ), 1⟩ : GaussianInt)

def segment (n h : ℕ) : GaussianInt :=
  ∏ j ∈ range h, (⟨1, (n+j+1 : ℕ)⟩ : GaussianInt)

private theorem cone (n h : ℕ) (hh : h ≤ n) :
    0 < (core n h).re ∧ 0 ≤ (core n h).im ∧
    ((n : ℤ)-h) * (core n h).im ≤ (h : ℤ) * (core n h).re ∧
    (0 < h → 0 < (core n h).im) := by
  induction h with
  | zero => simp [core]
  | succ h ih =>
    obtain ⟨hr, hi, hc, _⟩ := ih (by omega)
    let z := core n h
    have hr' : 0 < z.re := hr
    have hi' : 0 ≤ z.im := hi
    have hc' : ((n : ℤ) - h)*z.im ≤ h*z.re := hc
    let k : ℤ := n+h+1
    have hkn : (n : ℤ) ≤ k := by dsimp [k]; omega
    have hjn : (h : ℤ)+1 ≤ n := by exact_mod_cast hh
    have him : z.im ≤ (h : ℤ)*z.re := by
      calc z.im ≤ ((n:ℤ)-h)*z.im := by nlinarith [mul_nonneg (show 0≤(n:ℤ)-h-1 by omega) hi']
           _ ≤ _ := hc'
    have hrnew : 0 < k*z.re-z.im := by
      nlinarith [mul_nonneg (show 0≤k-h-1 by omega) hr'.le]
    have hinew : 0 < z.re+k*z.im := by nlinarith [mul_nonneg (show 0≤k by omega) hi']
    have hcnew : ((n:ℤ)-h-1)*(z.re+k*z.im) ≤ ((h:ℤ)+1)*(k*z.re-z.im) := by
      nlinarith [mul_nonneg (show 0≤k by omega) (sub_nonneg.mpr hc'),
        mul_nonneg (show 0≤k-n+h+1 by omega) hr'.le,
        mul_nonneg (show 0≤k-h-1 by omega) hi']
    have step : core n (h+1) = z * (⟨k,1⟩ : GaussianInt) := by
      simp [core, z, k, prod_range_succ]
    rw [step]
    simp only [Zsqrtd.re_mul, Zsqrtd.im_mul, mul_one, Nat.cast_succ]
    constructor
    · nlinarith
    constructor
    · nlinarith
    constructor
    · nlinarith only [hcnew]
    · intro; nlinarith

private def I : GaussianInt := ⟨0,1⟩
private def conj (z : GaussianInt) : GaussianInt := ⟨z.re, -z.im⟩

private theorem rotation (n h : ℕ) : segment n h = I^h * conj (core n h) := by
  induction h with
  | zero => simp [core, segment, conj]; rfl
  | succ h ih =>
    have se : segment n (h+1) = segment n h * (⟨1,(n+h+1:ℕ)⟩ : GaussianInt) :=
      prod_range_succ _ _
    have co : core n (h+1) = core n h * (⟨(n+h+1:ℕ),1⟩ : GaussianInt) :=
      prod_range_succ _ _
    rw [se, co, ih, pow_succ, mul_assoc, mul_assoc]
    congr 1
    apply Zsqrtd.ext <;> simp [I, conj, Zsqrtd.re_mul, Zsqrtd.im_mul]

private theorem rotate_nonzero (h : ℕ) (z : GaussianInt) (a : z.re ≠ 0) (b : z.im ≠ 0) :
    (I^h*z).re ≠ 0 ∧ (I^h*z).im ≠ 0 := by
  induction h with
  | zero => simpa using And.intro a b
  | succ h ih =>
    rw [pow_succ', mul_assoc]
    let w := I^h*z
    change (I*w).re ≠ 0 ∧ (I*w).im ≠ 0
    have e : ∀ y : GaussianInt, (I*y).re = -y.im ∧ (I*y).im = y.re := by
      intro y; simp [I, Zsqrtd.re_mul, Zsqrtd.im_mul]
    rw [(e w).1, (e w).2]
    exact ⟨neg_ne_zero.mpr ih.2, ih.1⟩

theorem segment_nonzero (n h : ℕ) (hp : 0 < h) (hn : h ≤ n) :
    (segment n h).re ≠ 0 ∧ (segment n h).im ≠ 0 := by
  obtain ⟨a, _, _, b⟩ := cone n h hn
  rw [rotation]
  exact rotate_nonzero h _ a.ne' (neg_ne_zero.mpr (b hp).ne')

private def size (z : GaussianInt) : ℤ := |z.re| + |z.im|

private theorem size_mul (u v : GaussianInt) : size (u*v) ≤ size u * size v := by
  unfold size
  simp only [Zsqrtd.re_mul, Zsqrtd.im_mul, neg_one_mul]
  calc _ ≤ (|u.re*v.re| + |(-u.im)*v.im|) + (|u.re*v.im| + |u.im*v.re|) :=
          add_le_add (abs_add_le ..) (abs_add_le ..)
       _ = _ := by simp only [abs_mul, abs_neg]; ring

private theorem segment_size (n h K : ℕ) (hk : n+h+1 ≤ K) : size (segment n h) ≤ (K:ℤ)^h := by
  induction h with
  | zero => simp [segment, size]
  | succ h ih =>
    rw [show segment n (h+1) = segment n h * (⟨1,(n+h+1:ℕ)⟩ : GaussianInt) from prod_range_succ _ _, pow_succ]
    apply (size_mul _ _).trans
    have hb : size (⟨1,(n+h+1:ℕ)⟩ : GaussianInt) ≤ (K:ℤ) := by
      simp [size, abs_of_nonneg (show (0:ℤ) ≤ n+h+1 by positivity)]; omega
    exact mul_le_mul (ih (by omega)) hb (by dsimp [size]; positivity) (by positivity)

/-- Two large excesses force the intervening Gaussian product to have a large imaginary
part. Use this with q a power of p, after dividing the first pair by its common p-power. -/
theorem spacing (n h : ℕ) (hp : 0 < h) (hn : h ≤ n) (q c a : ℤ)
    (hc : IsCoprime c q) (ha : q ∣ a)
    (hb : q ∣ a*(segment n h).re+c*(segment n h).im) :
    q ≤ ((n+h+1 : ℕ):ℤ)^h := by
  let w := (segment n h).im
  have hw : w ≠ 0 := (segment_nonzero n h hp hn).2
  have hd : q ∣ c*w := by
    exact (dvd_add_right (dvd_mul_of_dvd_left ha _)).mp hb
  obtain ⟨x,y,xy⟩ := hc
  have div : q ∣ w := by
    have eq : w = x*(c*w) + (y*w)*q := by linear_combination w*xy.symm
    rw [eq]
    exact dvd_add (dvd_mul_of_dvd_right hd _) (dvd_mul_left q _)
  have bound : q ≤ |w| := Int.le_of_dvd (abs_pos.mpr hw) ((dvd_abs q w).mpr div)
  exact bound.trans ((le_add_of_nonneg_left (abs_nonneg _)).trans (segment_size n h _ le_rfl))

end OMA.MollSegment
