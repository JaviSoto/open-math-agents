import MollSegment
import FormalConjectures.OEIS.«105751»

/-! The segment-spacing obstruction stated directly for OEIS A105751. The
comparison with its complex product follows @skhakim's LeftToSolve R2 reduction. -/
namespace OMA.MollSegment
open Finset

def full (n : ℕ) : GaussianInt := ∏ k ∈ range (n+1), (⟨1,(k:ℤ)⟩ : GaussianInt)

private theorem embed_full (n : ℕ) :
    ∏ k ∈ range (n+1), ((1:ℂ)+(k:ℂ)*Complex.I) =
      ((full n).re:ℂ) + ((full n).im:ℂ)*Complex.I := by
  induction n with
  | zero => simp [full]
  | succ n ih =>
    have hs : full (n+1) = full n * (⟨1,((n+1:ℕ):ℤ)⟩ : GaussianInt) := prod_range_succ _ _
    rw [prod_range_succ, ih, hs]
    simp only [Zsqrtd.re_mul, Zsqrtd.im_mul]
    push_cast
    linear_combination ((full n).im:ℂ)*((n:ℂ)+1)*Complex.I_sq

theorem sequence_eq_im (n : ℕ) : OeisA105751.a n = (full n).im := by
  unfold OeisA105751.a
  dsimp only
  rw [embed_full]
  simp only [Complex.add_im, Complex.intCast_im, Complex.mul_im, Complex.intCast_re,
    Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add]
  exact Int.floor_intCast _

theorem full_append (n h : ℕ) : full (n+h) = full n * segment n h := by
  induction h with
  | zero => simp [segment]
  | succ h ih =>
    have hs : full (n+h+1) = full (n+h) * (⟨1,((n+h+1:ℕ):ℤ)⟩ : GaussianInt) :=
      prod_range_succ _ _
    have step : segment n (h+1) = segment n h * (⟨1,((n+h+1:ℕ):ℤ)⟩ : GaussianInt) :=
      prod_range_succ _ _
    exact hs.trans (by rw [ih, mul_assoc, step])

/-- If two sequence values have a common extra divisor after removing the first
content d, that divisor is bounded in terms of their gap. In applications q=p^H. -/
theorem spacing_actual (n h : ℕ) (hp : 0 < h) (hn : h ≤ n) (d q c a : ℤ)
    (hd : d ≠ 0) (hc : IsCoprime c q) (ha : q ∣ a)
    (hre : (full n).re = d*c) (him : OeisA105751.a n = d*a)
    (hlater : d*q ∣ OeisA105751.a (n+h)) :
    q ≤ ((n+h+1 : ℕ):ℤ)^h := by
  apply spacing n h hp hn q c a hc ha
  rw [sequence_eq_im] at him
  rw [sequence_eq_im, full_append, Zsqrtd.im_mul, hre, him] at hlater
  obtain ⟨k,hk⟩ := hlater
  refine ⟨k, mul_left_cancel₀ hd ?_⟩
  linear_combination hk

end OMA.MollSegment
