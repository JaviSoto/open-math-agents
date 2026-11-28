import FormalConjectures.OEIS.«245212»

/-! Integer separation for a dyadic factor, an odd prime power and one
additional odd prime. All polynomial expressions below are over ℤ. -/
namespace OMA.LinearPowerGap245212

/-- The second pole is absent even without assuming its base prime. -/
theorem pole {p b k : ℤ} (hp : 3 ≤ p) (hb : 4 ≤ b) :
    2*b*(p-1)*(p-1-k)+(2*k-(p-1))*p ≠ 0 := by
  intro hit
  let u := p-1
  let d := b*u-p
  have hu : 0<u := by dsimp [u]; omega
  have hd : p<d := by
    dsimp [d,u]
    nlinarith only [hp,hb,mul_nonneg (by omega : 0≤b-4) (by omega : 0≤p-1)]
  have eqn : (2*(k-u))*d=u*p := by
    dsimp [d,u]; linear_combination -hit
  have hmul : 0<u*p := mul_pos hu (by omega)
  have pos : 0<2*(k-u) := (pos_of_mul_pos_left (eqn ▸ hmul) (by omega : 0≤d))
  have div : u ∣ 2*(k-u) := by
    refine ⟨(2*(k-u))*(b-1)-p, ?_⟩
    dsimp [d,u] at eqn ⊢
    linear_combination -eqn
  have hle := Int.le_of_dvd pos div
  nlinarith only [eqn, mul_pos hu (sub_pos.mpr hd),
    mul_nonneg (sub_nonneg.mpr hle) (by omega : 0≤d)]

def intercept (p x b : ℤ) := 2*b*x*(p-1)^2-(p-1)*(x+1)*p
def slope (p x b : ℤ) := b*(p-1)*(2*x+p)-(2*x+1)*p
def residual (p x k : ℤ) := k*(2*x+1)-(p-1)*(x+1)

private theorem divisor {p x b k : ℕ} (hp : p.Prime) (xp : x<p) (hx : 0<x)
    (kp : k+1<p) (hp2 : 2<p)
    (hit : intercept p x b=(k:ℤ)*slope p x b) : p ∣ b := by
  let : Fact p.Prime := ⟨hp⟩
  have h := congrArg (fun z : ℤ => (z : ZMod p)) hit
  simp only [intercept,slope] at h
  push_cast at h
  simp only [ZMod.natCast_self] at h
  have eqn : (b:ZMod p)*(2*(x:ZMod p)*(k+1))=0 := by
    linear_combination h
  have nonzero (n : ℕ) (h₁ : 0<n) (h₂ : n<p) : (n:ZMod p)≠0 := by
    simpa [ZMod.natCast_eq_zero_iff] using (Nat.not_dvd_of_pos_of_lt h₁ h₂)
  have hn : (2*(x:ZMod p)*(k+1))≠0 := by
    apply mul_ne_zero (mul_ne_zero (by exact_mod_cast nonzero 2 (by omega) hp2)
      (nonzero x hx xp))
    exact_mod_cast nonzero (k+1) (by omega) kp
  exact (ZMod.natCast_eq_zero_iff b p).mp ((mul_eq_zero.mp eqn).resolve_right hn)

/-- The exact cleared dyadic equation separates the limiting integer from
zero. In fact the second odd base need only be an integer at least three. -/
theorem gap {p x a k : ℕ} (hp : p.Prime) (hp3 : 3≤p) (hx : 3≤x) (ha : 3≤a)
    (eqn : (p:ℤ)^a * (((2:ℤ)^(k+1)-1)*
      (intercept p x (a+1) - (k:ℤ)*slope p x (a+1)) -
      (k+1)*slope p x (a+1)) =
      ((2:ℤ)^(k+1)-1)*residual p x k+(k+1)*(2*x+1)) :
    intercept p x (a+1) ≠ (k:ℤ)*slope p x (a+1) := by
  intro hit
  let G : ℤ := 2^(k+1)-1
  let B : ℤ := slope p x (a+1)
  let C : ℤ := residual p x k
  have ep : 1<(2:ℤ)^(k+1) := one_lt_pow₀ (by norm_num) (by omega)
  have gpos : 0<G := by dsimp [G]; omega
  have pp : 0<(p:ℤ)^a := by positivity
  have hx' : (3:ℤ)≤x := by exact_mod_cast hx
  have hp' : (3:ℤ)≤p := by exact_mod_cast hp3
  have ha' : (3:ℤ)≤a := by exact_mod_cast ha
  have bu : (p:ℤ)<(a+1)*(p-1) := by
    nlinarith only [ha',hp',mul_nonneg (by omega : (0:ℤ)≤a-3) (by omega : (0:ℤ)≤p-1)]
  have bpos : 0<B := by
    dsimp [B,slope]
    nlinarith only [mul_pos (sub_pos.mpr bu) (by omega : (0:ℤ)<2*x+p),
      mul_pos (by omega : (0:ℤ)<p) (by omega : (0:ℤ)<p-1)]
  have h : (p:ℤ)^a*((k:ℤ)+1)*B+((k:ℤ)+1)*(2*x+1) = -G*C := by
    dsimp [G,B,C]; rw [hit,sub_self,mul_zero,zero_sub] at eqn
    linear_combination -eqn
  have hpos : 0 < (p:ℤ)^a*((k:ℤ)+1)*B+((k:ℤ)+1)*(2*x+1) := by positivity
  have cneg : C<0 := by
    by_contra! hc
    nlinarith only [h,hpos,mul_nonneg gpos.le hc]
  have sep : B*C=((a:ℤ)+1)*(p-1)^2*(2*(x:ℤ)^2-p*(x+1)) := by
    dsimp [B,C,slope,intercept,residual] at hit ⊢
    linear_combination -(2*(x:ℤ)+1)*hit
  have qneg : 2*(x:ℤ)^2<p*(x+1) := by
    have h₁ := mul_neg_of_pos_of_neg bpos cneg
    rw [sep] at h₁
    exact sub_neg.mp (neg_of_mul_neg_right h₁ (by positivity))
  have xp : x<p := by
    by_contra! hxp
    have hp'' : (p:ℤ)≤x := by exact_mod_cast hxp
    nlinarith only [qneg,mul_nonneg (sub_nonneg.mpr hp'') (by positivity : (0:ℤ)≤x+1),
      mul_nonneg (by omega : (0:ℤ)≤x) (by omega : (0:ℤ)≤x-1)]
  have kp : k+1<p := by
    by_contra! hkp
    dsimp [C,residual] at cneg
    have hp'' : (p:ℤ)≤k+1 := by exact_mod_cast hkp
    nlinarith only [cneg,mul_nonneg (by omega : (0:ℤ)≤k-(p-1)) (by omega : (0:ℤ)≤2*x+1),
      mul_nonneg (by omega : (0:ℤ)≤p-1) (by omega : (0:ℤ)≤x)]
  have divis : p ∣ a+1 := divisor hp xp (by omega) kp (by omega) (by exact_mod_cast hit)
  have pa := Nat.le_of_dvd (by omega : 0<a+1) divis
  have hp5 : 5≤p := by
    by_contra! hlt
    have : p=4 := by omega
    subst p; norm_num at hp
  have expPow : 2^(k+1) ≤ p^(a-2) := calc
    2^(k+1) ≤ 2^(2*(p-3)) := Nat.pow_le_pow_right (by decide) (by omega)
    _ = 4^(p-3) := by rw [pow_mul]; norm_num
    _ ≤ p^(p-3) := Nat.pow_le_pow_left (by omega) _
    _ ≤ p^(a-2) := Nat.pow_le_pow_right (by omega) (by omega)
  have pw : (p:ℤ)^2 * (2:ℤ)^(k+1) ≤ (p:ℤ)^a := by
    have hh : (2:ℤ)^(k+1) ≤ (p:ℤ)^(a-2) := by exact_mod_cast expPow
    have mul := mul_le_mul_of_nonneg_left hh (sq_nonneg (p:ℤ))
    rwa [←pow_add,show 2+(a-2)=a by omega] at mul
  have hcx : -C ≤ (p:ℤ)^2 := by
    dsimp [C,residual]
    have xp' : (x:ℤ)<p := by exact_mod_cast xp
    nlinarith only [mul_nonneg (by omega : (0:ℤ)≤p) (by omega : (0:ℤ)≤p-x-1),
      mul_nonneg (by positivity : (0:ℤ)≤k) (by positivity : (0:ℤ)≤2*x+1),hx']
  have gg := mul_le_mul_of_nonneg_left hcx gpos.le
  have bk : (1:ℤ)≤((k:ℤ)+1)*B := by
    nlinarith only [mul_nonneg (by positivity : (0:ℤ)≤k) (by omega : 0≤B),bpos]
  have v := mul_le_mul_of_nonneg_left bk pp.le
  dsimp [G] at gg h
  nlinarith only [pw,h,gg,v,sq_nonneg (p:ℤ),
    mul_pos (by positivity : (0:ℤ)<k+1) (by positivity : (0:ℤ)<2*x+1)]

/-- The cleared equation used in `gap` follows by an integral polynomial
identity from the divisor-moment balance and both local geometric sums. -/
theorem clear (p x b k z P W S : ℤ)
    (weighted : (p-1)*W=b*p*P-S) (geometric : (p-1)*S=p*P-1)
    (balance : (1+k*z)*(2*x+1)*W+(z-1)*(x+1)*S = 2*z*(k+1)*b*P*x) :
    P*((z-1)*(intercept p x b-k*slope p x b)-(k+1)*slope p x b) =
    (z-1)*residual p x k+(k+1)*(2*x+1) := by
  unfold intercept slope residual
  linear_combination -(p-1)^2*balance + (1+k*z)*(2*x+1)*(p-1)*weighted +
    ((p-1)*(z-1)*(x+1)-(1+k*z)*(2*x+1))*geometric

end OMA.LinearPowerGap245212
