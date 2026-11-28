import FormalConjectures.OEIS.«245212»

/-! Integer separations for a repeated prime and its complementary power.
The resonance identities apply to arbitrary positive complementary moments. -/
namespace OMA.QuadraticPowerGap245212

def A (p b J S : ℤ) := b*(p-1)^2*J-(p-1)*p*S
def H (p b J V : ℤ) := b*(p-1)*(p*V-(p-1)*J)-p*V
def C (p v V S : ℤ) := v*V-(p-1)*S

theorem clear (p b k z P W s J V S : ℤ)
    (weighted : (p-1)*W=b*p*P-s) (geometric : (p-1)*s=p*P-1)
    (balance : (1+k*z)*V*W+(z-1)*S*s=z*(k+1)*b*P*J) :
    P*((z-1)*(A p b J S-k*H p b J V)-(k+1)*H p b J V) =
    (z-1)*C p k V S+(k+1)*V := by
  unfold A H C
  linear_combination -(p-1)^2*balance+(1+k*z)*V*(p-1)*weighted+
    ((p-1)*(z-1)*S-(1+k*z)*V)*geometric

/-- All three consequences of an integer resonance, independently of any
particular exponent on the complementary prime. -/
theorem resonance {p b k a J V S : ℕ} (hp : p.Prime) (hp3 : 3≤p) (hb : 3≤b)
    (hS : 0<S) (hV : S≤V) (hJ : J≤V)
    (hit : A p b J S=(k:ℤ)*H p b J V)
    (eqn : (p:ℤ)^a*(((2:ℤ)^(k+1)-1)*(A p b J S-(k:ℤ)*H p b J V)-
          (k+1)*H p b J V)=((2:ℤ)^(k+1)-1)*C p k V S+(k+1)*V) :
    k+1<p ∧ p∣b*J ∧ (J:ℤ)*(V-(S:ℤ))<p*S*(V-(J:ℤ)) ∧
    (p:ℤ)^a < (2:ℤ)^(k+1)*(p-1)*S := by
  let : Fact p.Prime := ⟨hp⟩
  have hp' : (3:ℤ)≤p := by exact_mod_cast hp3
  have hb' : (3:ℤ)≤b := by exact_mod_cast hb
  have hs : (0:ℤ)<S := by exact_mod_cast hS
  have hv : (S:ℤ)≤V := by exact_mod_cast hV
  have hj : (J:ℤ)≤V := by exact_mod_cast hJ
  have bu : (p:ℤ)<b*(p-1) := by
    nlinarith only [hp',hb',mul_nonneg (by omega : (0:ℤ)≤b-3) (by omega : (0:ℤ)≤p-1)]
  have hh : 0<H p b J V := by
    unfold H
    nlinarith only [mul_pos (sub_pos.mpr bu) (by omega : (0:ℤ)<V),
      mul_nonneg (mul_nonneg (by positivity : (0:ℤ)≤b) (sq_nonneg ((p:ℤ)-1))) (sub_nonneg.mpr hj)]
  have zpos : 1<(2:ℤ)^(k+1) := one_lt_pow₀ (by norm_num) (by omega)
  have red : (p:ℤ)^a*(k+1)*H p b J V+(k+1)*V= -((2:ℤ)^(k+1)-1)*C p k V S := by
    rw [hit,sub_self,mul_zero,zero_sub] at eqn
    linear_combination -eqn
  have lhs : 0<(p:ℤ)^a*(k+1)*H p b J V+(k+1)*V := by positivity
  have hneg : C p k V S<0 := by
    by_contra! ge
    nlinarith only [red,lhs,mul_nonneg (by omega : (0:ℤ)≤2^(k+1)-1) ge]
  have hk : k+1<p := by
    by_contra! h
    have hp'' : (p:ℤ)≤k+1 := by exact_mod_cast h
    unfold C at hneg
    nlinarith only [hneg,mul_nonneg (by omega : (0:ℤ)≤k-(p-1)) (by omega : (0:ℤ)≤V),
      mul_nonneg (by omega : (0:ℤ)≤p-1) (sub_nonneg.mpr hv)]
  have modp := congrArg (fun z:ℤ => (z:ZMod p)) hit
  unfold A H at modp
  push_cast at modp
  simp only [ZMod.natCast_self] at modp
  have mod0 : ((b:ZMod p)*J)*(k+1)=0 := by linear_combination modp
  have knz : (↑(k+1:ℕ):ZMod p)≠0 := by
    exact fun he => Nat.not_dvd_of_pos_of_lt (by omega) hk
      ((ZMod.natCast_eq_zero_iff (k+1) p).mp he)
  have dv : p∣b*J := by
    apply (ZMod.natCast_eq_zero_iff (b*J) p).mp
    push_cast at knz ⊢
    exact (mul_eq_zero.mp mod0).resolve_right knz
  have iden : H p b J V*C p k V S=(b:ℤ)*(p-1)^2*
      (J*(V-(S:ℤ))-p*S*(V-(J:ℤ))) := by
    simp only [H,C,A] at hit ⊢
    linear_combination -(V:ℤ)*hit
  have neg := mul_neg_of_pos_of_neg hh hneg
  rw [iden] at neg
  refine ⟨hk,dv,sub_neg.mp (neg_of_mul_neg_right neg (by positivity)),?_⟩
  have hle : 1≤((k:ℤ)+1)*H p b J V := by
    nlinarith only [hh,mul_nonneg (by positivity : (0:ℤ)≤k) hh.le]
  have pbound := mul_le_mul_of_nonneg_left hle (by positivity : 0≤(p:ℤ)^a)
  have cmax : -C p k V S ≤ ((p:ℤ)-1)*S := by unfold C; nlinarith only [mul_nonneg (by positivity : (0:ℤ)≤k) (by positivity : (0:ℤ)≤V)]
  have gc := mul_le_mul_of_nonneg_left cmax (by omega : (0:ℤ)≤2^(k+1)-1)
  nlinarith only [red,pbound,gc,mul_pos (by omega : (0:ℤ)<p-1) hs,
    mul_nonneg (by positivity : (0:ℤ)≤k+1) (by positivity : (0:ℤ)≤V)]

/-- For arbitrary complementary exponent d, this integer cannot vanish if
the weighted cofactor b(p−1)−p already exceeds dp. -/
theorem pole {p b k d : ℤ} (hp : 1<p) (hd : 0<d)
    (large : d*p<b*(p-1)-p) :
    (d+1)*b*(p-1)*(p-1-k)+((d+1)*k-(p-1))*p ≠ 0 := by
  intro hit
  let u := p-1
  let v := b*u-p
  have hu : 0<u := by dsimp [u]; omega
  have hv : d*p<v := large
  have hdpos : 0<d*p := mul_pos hd (by omega)
  have eqn : ((d+1)*(k-u))*v=u*(d*p) := by
    dsimp [v,u]; linear_combination -hit
  have pos : 0<(d+1)*(k-u) := pos_of_mul_pos_left (eqn ▸ mul_pos hu hdpos) (by omega : 0≤v)
  have div : u ∣ (d+1)*(k-u) := by
    refine ⟨((d+1)*(k-u))*(b-1)-d*p,?_⟩
    dsimp [v,u] at eqn ⊢; linear_combination -eqn
  have hle := Int.le_of_dvd pos div
  nlinarith only [eqn,mul_pos hu (sub_pos.mpr hv),
    mul_nonneg (sub_nonneg.mpr hle) (by omega : 0≤v)]

def j (q : ℕ) := 3*q^2
def v (q : ℕ) := 3*q^2+2*q+1
def s (q : ℕ) := q^2+q+1

/-- For complementary exponent two, an exact balance precludes integer
resonance for every a≥6; the cofactor base need not itself be prime. -/
theorem quadratic {p q a k : ℕ} (hp : p.Prime) (hp3 : 3≤p) (hq : 3≤q) (ha : 6≤a)
    (eqn : (p:ℤ)^a*(((2:ℤ)^(k+1)-1)*
      (A p (a+1) (j q) (s q)-(k:ℤ)*H p (a+1) (j q) (v q))-
      (k+1)*H p (a+1) (j q) (v q))=((2:ℤ)^(k+1)-1)*C p k (v q) (s q)+(k+1)*v q) :
    A p (a+1) (j q) (s q)≠(k:ℤ)*H p (a+1) (j q) (v q) := by
  intro hit
  have facts := resonance (b:=a+1) hp hp3 (by omega) (show 0<s q by unfold s; positivity)
    (show s q≤v q by dsimp [s,v]; omega) (show j q≤v q by dsimp [j,v]; omega) (by exact_mod_cast hit)
    (by exact_mod_cast eqn)
  rcases facts with ⟨hk,dv,sep,ub⟩
  have q' : (3:ℤ)≤q := by exact_mod_cast hq
  have qp : q<p := by
    by_contra! pq
    have p' : (p:ℤ)≤q := by exact_mod_cast pq
    simp only [v,s,j] at sep
    push_cast at sep
    have good := mul_pos (mul_pos (by omega : (0:ℤ)<q) (by omega : (0:ℤ)<q-1))
      (sq_pos_of_pos (by omega : (0:ℤ)<2*q+1))
    have diff := mul_nonneg (mul_nonneg (sub_nonneg.mpr p')
      (by positivity : (0:ℤ)≤q^2+q+1)) (by positivity : (0:ℤ)≤2*q+1)
    nlinarith only [sep,good,diff]
  have hp4 : 4≤p := by omega
  have ndj : ¬p∣j q := by
    intro dd
    rcases hp.dvd_mul.mp dd with bad | bad
    · exact Nat.not_dvd_of_pos_of_lt (by decide : 0<3) (by omega) bad
    · exact Nat.not_dvd_of_pos_of_lt (by omega) qp (hp.dvd_of_dvd_pow bad)
  have pa := Nat.le_of_dvd (by omega : 0<a+1) ((hp.dvd_mul.mp dv).resolve_right ndj)
  have ep : 2^(k+1)≤p^(a-3) := calc
    2^(k+1) ≤ 2^(2*(a-3)) := Nat.pow_le_pow_right (by decide) (by omega)
    _ = 4^(a-3) := by rw [pow_mul]; norm_num
    _ ≤ p^(a-3) := Nat.pow_le_pow_left hp4 _
  have pbound : (2:ℤ)^(k+1)*p^3 ≤ (p:ℤ)^a := by
    have ep' : (2:ℤ)^(k+1)≤(p:ℤ)^(a-3) := by exact_mod_cast ep
    have mult := mul_le_mul_of_nonneg_right ep' (by positivity : (0:ℤ)≤p^3)
    rwa [←pow_add,show a-3+3=a by omega] at mult
  have ss : (s q:ℤ)≤(p:ℤ)^2 := by
    have pq' : (q:ℤ)+1≤p := by exact_mod_cast qp
    have sq := pow_le_pow_left₀ (by positivity : (0:ℤ)≤q+1) pq' 2
    unfold s; push_cast; nlinarith only [sq,q']
  have bb := mul_le_mul_of_nonneg_left ss (by omega : (0:ℤ)≤p-1)
  have ab : ((p:ℤ)-1)*s q ≤ (p:ℤ)^3 := by nlinarith only [bb,sq_nonneg (p:ℤ)]
  have tt := mul_le_mul_of_nonneg_left ab (by positivity : (0:ℤ)≤2^(k+1))
  nlinarith only [ub,pbound,tt]

end OMA.QuadraticPowerGap245212
