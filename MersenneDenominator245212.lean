import Mathlib

/-! The multiplicative order of two recovers the index of a reduced
Mersenne denominator. This applies even when the denominator is composite. -/
namespace OMA.MersenneDenominator245212

def Q (t : ℕ) := (2^t-1)/Nat.gcd (2^t-1) t

private theorem twice_le_pow {b : ℕ} (hb : 0 < b) : 2*b ≤ 2^b := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb.ne'
  induction j with
  | zero => decide
  | succ j ih =>
    rw [pow_succ (2:ℕ) (j+1)]
    omega

theorem bound {t : ℕ} (ht : 2 ≤ t) : 2^(t/2)-1 < Q t := by
  let a := t/2
  let b := t-a
  have hp : 0 < b := by dsimp [a,b]; omega
  have cover : a+b=t := by dsimp [a,b]; omega
  have tcap : t ≤ 2^b := (show t≤2*b by dsimp [a,b]; omega).trans (twice_le_pow hp)
  have pa := Nat.two_pow_pos a
  have pb : 1 < 2^b := Nat.one_lt_two_pow hp.ne'
  have det : t*(2^a-1)<2^t-1 := by
    have h := Nat.mul_le_mul_right (2^a-1) tcap
    have z := congrArg (fun x : ℕ => 2^b*x) (Nat.sub_add_cancel (by omega : 1≤2^a))
    have prod : 2^t=2^a*2^b := by rw [←pow_add,cover]
    rw [prod]
    have s : 2^b*(2^a-1)+2^b=2^a*2^b := by nlinarith only [z]
    omega
  have gd := Nat.gcd_dvd_left (2^t-1) t
  have small : (2^t-1).gcd t ≤ t := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right _ _)
  have mul : Q t * ((2^t-1).gcd t)=2^t-1 := Nat.div_mul_cancel gd
  by_contra! h
  have le := Nat.mul_le_mul h small
  change Q t * _ ≤ (2^a-1)*t at le
  rw [mul,mul_comm (2^a-1)] at le
  omega

private theorem pow_test (t m : ℕ) :
    (2 : ZMod (Q t))^m=1 ↔ Q t ∣ 2^m-1 := by
  have h := Nat.modEq_iff_dvd' (show 1≤(2:ℕ)^m from Nat.one_le_pow _ _ (by decide)) (n:=Q t)
  rw [←ZMod.natCast_eq_natCast_iff,Nat.cast_one,Nat.cast_pow,Nat.cast_ofNat] at h
  exact eq_comm.trans h

theorem order {t : ℕ} (ht : 2≤t) : orderOf (2 : ZMod (Q t))=t := by
  have gd := Nat.gcd_dvd_left (2^t-1) t
  have mul : Q t * ((2^t-1).gcd t)=2^t-1 := Nat.div_mul_cancel gd
  apply orderOf_eq_of_pow_and_pow_div_prime (by omega) ((pow_test t t).mpr ⟨_,mul.symm⟩)
  intro p pp pt eq
  have pos : 0<t/p := Nat.div_pos (Nat.le_of_dvd (by omega) pt) pp.pos
  have cap : t/p≤t/2 := Nat.div_le_div_left pp.two_le (by decide)
  have le := Nat.pow_le_pow_right (by decide : 0 < 2) cap
  have mid := bound ht
  have d := Nat.le_of_dvd (by have := Nat.one_lt_two_pow pos.ne'; omega : 0<2^(t/p)-1)
    ((pow_test t _).mp eq)
  omega

theorem injective_on_indices {s t : ℕ} (hs : 2 ≤ s) (ht : 2 ≤ t) (eq : Q s=Q t) : s=t := by
  rw [←order hs,←order ht,eq]

/-- A positive solution of the residual equation has reduced denominator Q(k+1). -/
theorem reduced {x y k : ℕ} (hy : 0 < y) (hk : 1≤k) (quot : k=x/y)
    (sol : 2^(k+1)*(x-k*y)=x+y) : y/(x.gcd y)=Q (k+1) := by
  let t := k+1
  let D := 2^t-1
  let g := D.gcd t
  let P := t/g
  let q := Q t
  let u := x%y
  have qq : u+k*y=x := by simpa only [u,quot,mul_comm] using Nat.mod_add_div x y
  have rem : x-k*y=u := by omega
  change 2^t*(x-k*y)=x+y at sol
  rw [rem] at sol
  have pos : 1<2^t := Nat.one_lt_two_pow (by dsimp [t]; omega)
  have ds : D+1=2^t := by dsimp only [D]; omega
  have ratio : D*u=t*y := by
    change D*u=(k+1)*y
    nlinarith only [sol,qq,congrArg (fun n : ℕ => n*u) ds]
  have dp : 0 < D := by omega
  have gp : 0 < g := Nat.gcd_pos_of_pos_left _ dp
  have qp : 0 < q := Nat.div_pos (Nat.le_of_dvd dp (Nat.gcd_dvd_left D t)) gp
  have af : q*g=D := Nat.div_mul_cancel (Nat.gcd_dvd_left D t)
  have bf : P*g=t := Nat.div_mul_cancel (Nat.gcd_dvd_right D t)
  have red : q*u=P*y := by
    apply Nat.eq_of_mul_eq_mul_right gp
    calc
      q*u*g = q*g*u := by ring
      _ = D*u := by rw [af]
      _ = t*y := ratio
      _ = P*y*g := by rw [←bf]; ring
  have cp : q.Coprime P := Nat.coprime_div_gcd_div_gcd gp
  have d : q∣y := cp.dvd_of_dvd_mul_left (red ▸ dvd_mul_right q u)
  let z := y/q
  have yz : y=q*z := (Nat.mul_div_cancel' d).symm
  have uz : u=P*z := by
    apply Nat.eq_of_mul_eq_mul_left qp
    calc
      q*u = P*y := red
      _ = P*(q*z) := congrArg (P*·) yz
      _ = q*(P*z) := by ring
  have gz : x.gcd y=z := by
    calc
      _ = u.gcd y := by rw [←qq,Nat.gcd_add_mul_right_left]
      _ = (P*z).gcd (q*z) := congrArg₂ Nat.gcd uz yz
      _ = z := by rw [Nat.gcd_mul_right,cp.symm.gcd_eq_one]; simp
  change y/(x.gcd y)=q
  rw [gz]
  have zp : 0 < z := Nat.div_pos (Nat.le_of_dvd hy d) qp
  exact (Nat.div_eq_iff_eq_mul_left zp (by exact ⟨q,yz.trans (Nat.mul_comm q z)⟩)).mpr yz

/-- The denominator alone recovers k+1, without needing the numerator. -/
theorem residual_order {x y k : ℕ} (hy : 0 < y) (hk : 1≤k) (quot : k=x/y)
    (sol : 2^(k+1)*(x-k*y)=x+y) : orderOf (2 : ZMod (y/(x.gcd y)))=k+1 := by
  rw [reduced hy hk quot sol]
  exact order (by omega)

end OMA.MersenneDenominator245212
