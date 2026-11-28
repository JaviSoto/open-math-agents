import Mathlib

/-! An explicit large-prime cutoff for the quadratic even cofactor quotient.
The numerator and positive denominator are the expansions at u=q^2. -/
namespace OMA.SquareCoreBound245212

def den (k q z : ℤ) := z*(5*q^2-(4*k+1)*q-(2*k+1))-(5*q^2+3*q+1)
def num (k q z : ℤ) := z*((3*k+1)*q^2+(2*k+1)*q+(k+1))+(2*q^2+q)

private theorem exp_dominates {k : ℕ} (hk : 6≤k) : 15*k+20 ≤ 2^(k+1) := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih => rw [pow_succ]; omega

private theorem big_k {k q : ℕ} {p : ℤ} (hk : 6≤k) (hq : 2≤q)
    (positive : 0<den k q (2^(k+1)))
    (eqn : num k q (2^(k+1))=p*den k q (2^(k+1))) : q<12*(k+1)^2 := by
  by_contra! lower
  let z : ℤ := 2^(k+1)
  let d := den k q z
  let n := num k q z
  change 0<d at positive
  change n=p*d at eqn
  have kz : (15:ℤ)*k+20≤z := by dsimp [z]; exact_mod_cast exp_dominates hk
  have qz : (2:ℤ)≤q := by exact_mod_cast hq
  have kl : (12:ℤ)*((k:ℤ)+1)^2≤q := by exact_mod_cast lower
  have kn : (0:ℤ)≤k := Nat.cast_nonneg _
  have zp : 0<z := by dsimp [z]; positivity
  have gap : (0:ℤ)<5*n-(3*k+1)*d := by
    have poly : 5*n-(3*k+1)*d=z*((12*k^2+17*k+6)*q+(6*k^2+10*k+6))+
        (15*k+15)*q^2+(9*k+8)*q+3*k+1 := by dsimp [n,d,num,den]; ring
    rw [poly]; positivity
  have pd : (1:ℤ)≤5*p-(3*k+1) := by
    by_contra! bad
    have := mul_nonpos_of_nonpos_of_nonneg (show 5*p-(3*k+1)≤0 by omega) positive.le
    rw [eqn] at gap; nlinarith only [gap,this]
  have slope := mul_le_mul_of_nonneg_right pd positive.le
  have qs : (0:ℤ)≤q := Nat.cast_nonneg _
  have a : 12*(k:ℤ)^2+21*k+7≤q := by nlinarith only [kl,kn]
  have b : 6*(k:ℤ)^2+12*k+7≤q := by nlinarith only [kl,kn,sq_nonneg (k:ℤ)]
  have enough : z*(4*(q:ℤ)^2-q) ≤ z*(5*q^2-(12*(k:ℤ)^2+21*k+7)*q-(6*k^2+12*k+7)) := by
    apply mul_le_mul_of_nonneg_left _ zp.le
    nlinarith only [mul_le_mul_of_nonneg_right a qs,b]
  have opposite : z*(5*(q:ℤ)^2-(12*(k:ℤ)^2+21*k+7)*q-(6*k^2+12*k+7)) ≤
      (15*k+20)*q^2+(9*k+11)*q+3*k+2 := by
    have sl : d≤5*n-(3*k+1)*d := by rw [eqn]; nlinarith only [slope]
    dsimp [d,n,den,num] at sl
    nlinarith only [sl]
  have ends : (15*(k:ℤ)+20)*q^2+(9*k+11)*q+3*k+2 ≤ z*((q:ℤ)^2+q+1) := by
    have t1 := mul_le_mul_of_nonneg_right kz (sq_nonneg (q:ℤ))
    have t2 := mul_le_mul_of_nonneg_right (show 9*(k:ℤ)+11≤z by omega) qs
    nlinarith only [t1,t2,kz,kn]
  have absurd := (enough.trans opposite).trans ends
  have h := (mul_le_mul_iff_right₀ zp).mp absurd
  nlinarith only [h,qz,mul_nonneg (show (0:ℤ)≤(q:ℤ)-2 by omega) qs]

private theorem no_integer {n d p m : ℤ} (e : n=p*d) (hd : 0<d)
    (low : m*d<n) (high : n<(m+1)*d) : False := by
  rw [e] at low high
  have := (mul_lt_mul_iff_left₀ hd).mp low
  have := (mul_lt_mul_iff_left₀ hd).mp high
  omega

private theorem small_k {k q : ℕ} {p : ℤ} (hk : 1≤k) (hk' : k≤5) (hq : 1024≤q)
    (hd : 0<den k q (2^(k+1))) (eqn : num k q (2^(k+1))=p*den k q (2^(k+1))) : False := by
  obtain ⟨x,rfl⟩ := Nat.exists_eq_add_of_le hq
  have xp : (0:ℤ)≤x := Nat.cast_nonneg _
  interval_cases k
  all_goals first
    | apply no_integer (m:=1) eqn hd <;> norm_num [den,num] <;> nlinarith only [xp,sq_nonneg (x:ℤ)]
    | apply no_integer (m:=2) eqn hd <;> norm_num [den,num] <;> nlinarith only [xp,sq_nonneg (x:ℤ)]
    | apply no_integer (m:=3) eqn hd <;> norm_num [den,num] <;> nlinarith only [xp,sq_nonneg (x:ℤ)]

private theorem growth {h : ℕ} (hh : 20≤h) : 12*(23+8*h)^2<2^h := by
  induction h, hh using Nat.le_induction with
  | base => decide
  | succ h hh ih =>
    rw [pow_succ (2:ℕ) h]
    nlinarith only [ih,hh,Nat.mul_le_mul hh hh]

/-- Once the cofactor logarithmic cutoff is supplied, the quadratic equation
has no integer quotient for q at or above 2^20, irrespective of primality. -/
theorem square_cutoff {k q A : ℕ} {p : ℤ} (hk : 1≤k) (hq : 2≤q)
    (coarse : A≤128*q^4) (cap : k≤2*Nat.log 2 A)
    (hd : 0<den k q (2^(k+1))) (eqn : num k q (2^(k+1))=p*den k q (2^(k+1))) :
    q<2^20 := by
  by_contra! large
  by_cases ksmall : k≤5
  · exact small_k hk ksmall (by omega) hd eqn
  let h := Nat.log 2 q
  have hh : 20≤h := Nat.le_log_of_pow_le (by decide) large
  have up : q≤2^(h+1) := (Nat.lt_pow_succ_log_self (by decide : 1<2) q).le
  have expbound : A≤2^(7+4*(h+1)) := by
    calc A ≤ 128*q^4 := coarse
         _ ≤ 128*(2^(h+1))^4 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left up 4)
         _ = _ := by rw [Nat.mul_comm 4 (h+1),pow_add (2:ℕ) 7 ((h+1)*4),pow_mul]; rfl
  have logle := Nat.log_mono_right (b:=2) expbound
  rw [Nat.log_pow (by decide)] at logle
  have sk : k+1≤23+8*h := by omega
  have upper := (big_k (by omega) hq hd eqn).trans_le (Nat.mul_le_mul_left 12 (Nat.pow_le_pow_left sk 2))
  exact (not_lt_of_ge (Nat.pow_log_le_self 2 (show q≠0 by omega))) (upper.trans (growth hh))

#print axioms square_cutoff
end OMA.SquareCoreBound245212
