import FiveFaces245212

/-! Effective control of the remaining 9*5^a*7^b*11^c*r^d family. -/
namespace OMA.FiveFace245212
open Finset OMA.Smooth245212
open scoped ArithmeticFunction.sigma

private theorem xcap {p : ℕ} (hp : 5≤p) (e : ℕ) : X p (some e)≤5/4 := by
  have pc : (5:ℚ)≤p := by exact_mod_cast hp
  have pos : 0<(p:ℚ)-1 := by linarith
  have yn := y_nonneg (show 1<p by omega) (some e)
  change 1+(1-Y p (some e))/((p:ℚ)-1)≤5/4
  have := (div_le_iff₀ pos).mpr (show 1-Y p (some e)≤(1/4:ℚ)*((p:ℚ)-1) by linarith)
  linarith

private theorem off {p r e d : ℕ} (hp : p.Prime) (large : 5≤p)
    (hr : 10000000000≤r) (he : 2000000000≤e) (A B : ℚ)
    (a0 : 0≤A) (a4 : A≤4) (b0 : 0≤B) (b1 : B≤1)
    (far : away (A*X p none))
    (score : A*X p (some e)*X r (some d)+B*Y p (some e)*Y r (some d)=2) : False := by
  let eps : ℚ := 1/1000000000
  have py := y_nonneg hp.one_lt (some e)
  have py1 := y_one hp.one_lt (some e)
  have pp : (5:ℚ)≤p := by exact_mod_cast large
  have rp : (10000000000:ℚ)≤r := by exact_mod_cast hr
  have ee : (2000000000:ℚ)≤e := by exact_mod_cast he
  have ry := y_nonneg (show 1<r by omega) (some d)
  have ry1 := y_one (show 1<r by omega) (some d)
  have ysmall : Y p (some e)≤eps := by
    have a := OMA.CapOrder245212.y_short hp e
    have b := mul_nonneg (sub_nonneg.mpr ee) py
    dsimp [eps]; nlinarith only [a,b,py]
  have px := x_nonneg hp.one_lt (some e)
  have pcap := xcap large e
  have ppos : 0<(p:ℚ)-1 := by linarith
  have rpos : 0<(r:ℚ)-1 := by linarith
  have dx : X p none-X p (some e)=Y p (some e)/((p:ℚ)-1) := by
    simp only [X,Y]; ring
  have xd0 : 0≤X p none-X p (some e) := by rw [dx]; positivity
  have xd : X p none-X p (some e)≤eps := by
    rw [dx,div_le_iff₀ ppos]
    dsimp [eps] at ysmall ⊢; linarith
  have xr0 : 1≤X r (some d) := by
    change 1≤1+(1-Y r (some d))/((r:ℚ)-1)
    exact le_add_of_nonneg_right (div_nonneg (sub_nonneg.mpr ry1) rpos.le)
  have xr : X r (some d)-1≤eps := by
    simp only [X,add_sub_cancel_left]; rw [div_le_iff₀ rpos]; dsimp [eps]; linarith
  have coarse : A*X p (some e)≤8 := by
    exact (mul_le_mul a4 (pcap.trans (by norm_num : (5/4:ℚ)≤2)) px (by norm_num)).trans (by norm_num)
  have plus := mul_le_mul coarse xr (sub_nonneg.mpr xr0) (by norm_num : (0:ℚ)≤8)
  have minus := mul_le_mul a4 xd xd0 (by norm_num : (0:ℚ)≤4)
  have yp := mul_le_mul (mul_le_mul b1 ysmall py (by norm_num)) ry1 ry
    (by dsimp [eps]; norm_num : 0≤(1:ℚ)*eps)
  have axpos := mul_nonneg a0 px
  have addpos := mul_nonneg axpos (sub_nonneg.mpr xr0)
  have yypos := mul_nonneg (mul_nonneg b0 py) ry
  have difference := mul_nonneg a0 xd0
  rcases far with f|f <;> dsimp [eps,gap] at * <;>
    nlinarith only [f,score,plus,minus,yp,addpos,yypos,difference]

private theorem prefOff {p q s r e f g d : ℕ} (hp : p.Prime)
    (p5 : 5 ≤ p) (q5 : 5 ≤ q) (s5 : 5 ≤ s) (hr : 10000000000 ≤ r)
    (far : away ((34/27:ℚ)*X p none*X q (some f)*X s (some g)))
    (score : (34/27:ℚ)*X p (some e)*X q (some f)*X s (some g)*X r (some d)+
        (13/27:ℚ)*Y p (some e)*Y q (some f)*Y s (some g)*Y r (some d)=2) :
    e<2000000000 := by
  by_contra! big
  let A := (34/27:ℚ)*X q (some f)*X s (some g)
  let B := (13/27:ℚ)*Y q (some f)*Y s (some g)
  have xq := x_nonneg (show 1<q by omega) (some f)
  have xs := x_nonneg (show 1<s by omega) (some g)
  have yq := y_nonneg (show 1<q by omega) (some f)
  have ys := y_nonneg (show 1<s by omega) (some g)
  have a4 : A≤4 := by
    have h := mul_le_mul (mul_le_mul_of_nonneg_left (xcap q5 f) (by norm_num : (0:ℚ)≤34/27))
      (xcap s5 g) xs (by norm_num); exact h.trans (by norm_num)
  have b1 : B≤1 := by
    have h := mul_le_mul (mul_le_mul_of_nonneg_left (y_one (show 1<q by omega) (some f)) (by norm_num : (0:ℚ)≤13/27))
      (y_one (show 1<s by omega) (some g)) ys (by norm_num); exact h.trans (by norm_num)
  apply off hp p5 hr big A B (by dsimp [A]; positivity) a4 (by dsimp [B]; positivity) b1
  · dsimp [A]; convert far using 1 <;> ring
  · dsimp [A,B]; linear_combination score

theorem prefix_exponents {r a b c d : ℕ} (hr : 10000000000≤r)
    (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (score : (34/27:ℚ)*X 5 (some a)*X 7 (some b)*X 11 (some c)*X r (some d)+
      (13/27:ℚ)*Y 5 (some a)*Y 7 (some b)*Y 11 (some c)*Y r (some d)=2) :
    a<2000000000 ∧ b<2000000000 ∧ c<2000000000 := by
  have inside {j : ℕ} (h : 0<j) : (⟨1,none⟩:Band).Contains j := ⟨h,by simp⟩
  constructor
  · apply prefOff (p:=5) (q:=7) (s:=11) (f:=b) (g:=c) (by decide) (by decide) (by decide) (by decide) hr _ score
    simpa only [show (34/27:ℚ)*X 5 none=85/54 by decide +kernel] using face5 b c (inside hb) (inside hc)
  constructor
  · apply prefOff (p:=7) (q:=5) (s:=11) (f:=a) (g:=c) (d:=d) (by decide) (by decide) (by decide) (by decide) hr
    · simpa only [show (34/27:ℚ)*X 7 none=119/81 by decide +kernel] using face7 a c (inside ha) (inside hc)
    · linear_combination score
  · apply prefOff (p:=11) (q:=5) (s:=7) (f:=a) (g:=b) (d:=d) (by decide) (by decide) (by decide) (by decide) hr
    · simpa only [show (34/27:ℚ)*X 11 none=187/135 by decide +kernel] using face11 a b (inside ha) (inside hb)
    · linear_combination score

#print axioms prefix_exponents
end OMA.FiveFace245212
