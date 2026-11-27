import Mathlib
import FormalConjectures.ErdosProblems.«686»

/-! Partial results on the quotient four in Erdős problem 686. This file does not settle the open case. -/

/- The large-prime part of a binomial coefficient for the lower block must
divide a binomial coefficient for the *differences* of the two blocks. No
fixed-ratio or parity assumption is needed for this divisibility theorem. -/
namespace OMA.Gap686
open Nat Finset
def block (s k : ℕ) := ∏ i ∈ range k, (s+1+i)
lemma block_eq (s k : ℕ) : block s k = k.factorial*(s+k).choose k := by
  rw [block,←Nat.ascFactorial_eq_prod_range,Nat.ascFactorial_eq_factorial_mul_choose]

lemma extract {s k p e : ℕ} (hp : p.Prime) (hk : k<p) (he : 0<e)
    (hd : p^e ∣ block s k) : ∃ i<k, p^e ∣ s+1+i := by
  have hd' : p ∣ block s k := (dvd_pow_self p he.ne').trans hd
  obtain ⟨i,hi,di⟩ := (hp.prime.dvd_finsetProd_iff _).mp hd'
  refine ⟨i,mem_range.mp hi,?_⟩
  have hc : p.Coprime (∏ j ∈ (range k).erase i, (s+1+j)) := by
    apply hp.coprime_iff_not_dvd.mpr
    intro bad
    obtain ⟨j,hj,dj⟩ := (hp.prime.dvd_finsetProd_iff _).mp bad
    obtain ⟨ne,mem⟩ := mem_erase.mp hj
    have il := mem_range.mp hi
    have jl := mem_range.mp mem
    rcases lt_or_gt_of_ne ne with ji|ij
    · have h : p ∣ i-j := by
        convert Nat.dvd_sub di dj using 1; omega
      have := Nat.le_of_dvd (by omega : 0 < i-j) h
      omega
    · have h : p ∣ j-i := by
        convert Nat.dvd_sub dj di using 1; omega
      have := Nat.le_of_dvd (by omega : 0 < j-i) h
      omega
  apply (hc.pow_left e).dvd_of_dvd_mul_left
  rw [prod_erase_mul _ _ hi]
  exact hd

lemma move_power {s d k p e : ℕ} (hk : 0<k) (disj : k≤d) (hp : p.Prime) (big : 2*k<p)
    (h : block s k ∣ block (s+d) k) (div : p^e ∣ (s+k).choose k) :
    p^e ∣ (d+k).choose (2*k) := by
  by_cases he : e=0
  · simp [he]
  have low : p^e ∣ block s k := by rw [block_eq]; exact div.trans (dvd_mul_left _ _)
  obtain ⟨i,hi,a⟩ := extract hp (by omega) (by omega) low
  obtain ⟨j,hj,b⟩ := extract hp (by omega) (by omega) (low.trans h)
  have v := Nat.dvd_sub b a
  let z := k+j-i-1
  have hz : z<2*k := by dsimp [z]; omega
  have ev : s+d+1+j-(s+1+i) = d-k+1+z := by dsimp [z]; omega
  rw [ev] at v
  have inside : p^e ∣ block (d-k) (2*k) := v.trans (Finset.dvd_prod_of_mem _ (mem_range.mpr hz))
  rw [block_eq,show d-k+2*k=d+k by omega] at inside
  exact ((hp.coprime_factorial_of_lt big).pow_left e).dvd_of_dvd_mul_left inside

theorem difference_bound {s d k : ℕ} (hk : 0<k) (disj : k≤d)
    (h : block s k ∣ block (s+d) k) :
    (s+k).choose k ≤ (s+k)^(2*k).primeCounting * (d+k).choose (2*k) := by
  let a := (s+k).choose k
  let b := (d+k).choose (2*k)
  let T := (2*k).primesLE
  let L := ∏ p ∈ T, p^a.factorization p
  have ap : 0<a := Nat.choose_pos (by omega : k ≤ s+k)
  have bp : 0<b := Nat.choose_pos (by omega : 2*k ≤ d+k)
  have lp : 0<L := Finset.prod_pos (fun p hp => pow_pos (Nat.mem_primesLE.mp hp).2.pos _)
  have hdiv : a ∣ L*b := by
    apply (Nat.factorization_le_iff_dvd ap.ne' (Nat.mul_pos lp bp).ne').mp
    intro p
    by_cases hp : p.Prime
    · apply (hp.pow_dvd_iff_le_factorization (Nat.mul_pos lp bp).ne').mp
      by_cases small : p≤2*k
      · have mem : p∈T := Nat.mem_primesLE.mpr ⟨small,hp⟩
        exact (Finset.dvd_prod_of_mem (fun p => p^a.factorization p) mem).trans (dvd_mul_right L b)
      · have into : p^a.factorization p ∣ b := move_power hk disj hp (by omega) h
          ((hp.pow_dvd_iff_le_factorization ap.ne').mpr le_rfl)
        exact into.trans (dvd_mul_left b L)
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  have lbound : L ≤ (s+k)^(2*k).primeCounting := by
    calc
      L ≤ ∏ _p ∈ T, (s+k) := by
        apply Finset.prod_le_prod'
        intro p hp
        exact (Nat.pow_le_pow_right (Nat.mem_primesLE.mp hp).2.pos Nat.factorization_choose_le_log).trans
          (Nat.pow_log_le_self p (by omega))
      _ = _ := by simp [T,Nat.primesLE_card_eq_primeCounting]
  exact (Nat.le_of_dvd (Nat.mul_pos lp bp) hdiv).trans (Nat.mul_le_mul_right b lbound)

end OMA.Gap686

namespace OMA.Gap686
open Nat Finset Real Filter

lemma block_pos (s k : ℕ) : 0<block s k :=
  Finset.prod_pos fun _ _ => by omega

lemma ratio {s d k : ℕ} (eq : block (s+d) k = 4*block s k) :
    (∏ i ∈ range k, (1+(d:ℝ)/(s+1+i)))=4 := by
  have cop : ∀ i : ℕ, (1:ℝ)+d/(s+1+i)=(s+d+1+i)/(s+1+i) := by
    intro i; field_simp; ring
  simp_rw [cop]
  rw [Finset.prod_div_distrib,div_eq_iff]
  · exact_mod_cast eq
  · exact ne_of_gt (Finset.prod_pos fun i _ => by positivity)

lemma size {s d k : ℕ} (hk : 6 ≤ k) (hd : k ≤ d) (eq : block (s+d) k = 4*block s k) :
    (k:ℝ)*d/6 ≤ s ∧ (s:ℝ)+1 < k*d := by
  have rat := ratio eq
  have sk : 0<(s:ℝ)+k := by positivity
  have kr : 6 ≤ (k:ℝ) := by exact_mod_cast hk
  have dr : 6 ≤ (d:ℝ) := by exact_mod_cast hk.trans hd
  have posk : 0<(k:ℝ) := by linarith
  have below : (1+(d:ℝ)/(s+k))^k ≤ 4 := by
    rw [←rat,←Finset.card_range k,←Finset.prod_const,Finset.card_range]
    apply Finset.prod_le_prod
    · intro _ _; positivity
    · intro i hi
      apply add_le_add_right
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      have il : (i:ℝ)+1 ≤ k := by exact_mod_cast mem_range.mp hi
      linarith
  have nz : (0:ℝ) ≤ d/(s+k) := by positivity
  have bl := (one_add_mul_le_pow (show (-2:ℝ) ≤ d/(s+k) by linarith) k).trans below
  have small : (k:ℝ)*d ≤ 3*(s+k) := by
    rw [←mul_div_assoc] at bl
    exact (div_le_iff₀ sk).mp (by linarith)
  constructor
  · nlinarith [mul_nonneg posk.le (sub_nonneg.mpr dr)]
  · by_contra! big
    have upper : (∏ i ∈ range k, (1+(d:ℝ)/(s+1+i))) ≤ (Real.exp (1/(k:ℝ)))^k := by
      rw [←Finset.card_range k,←Finset.prod_const,Finset.card_range]
      apply Finset.prod_le_prod
      · intro i _; positivity
      · intro i _
        apply le_trans _ (Real.add_one_le_exp _)
        rw [add_comm]
        apply add_le_add_left
        apply (div_le_div_iff₀ (by positivity) posk).mpr
        nlinarith [(Nat.cast_nonneg i : 0≤(i:ℝ))]
    rw [rat,←Real.exp_nat_mul,show (k:ℝ)*(1/k)=1 by field_simp] at upper
    linarith [Real.exp_one_lt_three]

lemma lower_choose (s k : ℕ) :
    (s:ℝ)^k ≤ (k:ℝ)^k * ((s+k).choose k:ℕ) := by
  have h : s^k ≤ block s k := by
    change _ ≤ ∏ i ∈ range k, (s+1+i)
    calc
      _ = ∏ _i ∈ range k, s := by simp
      _ ≤ _ := Finset.prod_le_prod' fun i _ => by omega
  rw [block_eq] at h
  exact_mod_cast h.trans (Nat.mul_le_mul_right _ (Nat.factorial_le_pow k))

lemma upper_choose {d k : ℕ} (hd : k ≤ d) (hk : 0<k) :
    (((d+k).choose (2*k):ℕ):ℝ) ≤ (Real.exp 1*d/k)^(2*k) := by
  have h := (Nat.choose_le_pow_div (α:=ℝ) (2*k) (d+k))
  have pos : 0 < (2*k:ℕ) := by omega
  have hm := Real.pow_div_factorial_le_exp (2*k) (by positivity) (2*k)
  rw [show Real.exp (2*(k:ℝ)) = (Real.exp 1)^(2*k) by rw [←Real.exp_nat_mul]; push_cast; ring_nf] at hm
  have kp : 0<(k:ℝ) := by exact_mod_cast hk
  have dr : (k:ℝ) ≤ d := by exact_mod_cast hd
  have den : 0 < ((2*k).factorial:ℝ) := by positivity
  apply h.trans
  rw [div_pow,mul_pow,div_le_div_iff₀ den (pow_pos kp _)]
  push_cast
  have u : ((d:ℝ)+k)*k ≤ (2*k)*d := by nlinarith [mul_nonneg kp.le (sub_nonneg.mpr dr)]
  have est := pow_le_pow_left₀ (by positivity) u (2*k)
  rw [mul_pow,mul_pow] at est
  have high := (div_le_iff₀ den).mp hm
  calc
    _ ≤ (2*(k:ℝ))^(2*k)*(d:ℝ)^(2*k) := est
    _ ≤ _ := by nlinarith [mul_nonneg (sub_nonneg.mpr high) (pow_nonneg (Nat.cast_nonneg d) (2*k))]

end OMA.Gap686

namespace OMA.Gap686
open Nat Finset Real Filter

lemma prime_budget : ∀ᶠ k : ℕ in atTop,
    ((2*k).primeCounting:ℝ)*Real.log (2*(k:ℝ)) ≤ 8*k := by
  have t : Tendsto (fun k : ℕ => 2*(k:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  filter_upwards [t.eventually (Chebyshev.eventually_primeCounting_le (ε:=1) (by norm_num)),
    eventually_ge_atTop 2] with k hp hk
  have kr : 2 ≤ (k:ℝ) := by exact_mod_cast hk
  have lp : 0 < Real.log (2*(k:ℝ)) := Real.log_pos (by linarith)
  have fl : ⌊2*(k:ℝ)⌋₊ = 2*k := by exact_mod_cast (Nat.floor_natCast (R:=ℝ) (2*k))
  rw [fl] at hp
  have h := (le_div_iff₀ lp).mp hp
  have lg : Real.log 4 ≤ 3 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)]
  nlinarith [mul_nonneg (sub_nonneg.mpr lg) (Nat.cast_nonneg k : 0≤(k:ℝ))]

/-- A fixed quotient of four requires a gap at least a constant times k²
and a starting point at least a constant times k³, as k grows. -/
theorem obstruction : ∃ C : ℝ, 0<C ∧ ∀ᶠ k : ℕ in atTop,
    ∀ s d : ℕ, k ≤ d → block (s+d) k=4*block s k →
      (k:ℝ)^2 ≤ C*d ∧ (k:ℝ)^3 ≤ 6*C*s := by
  let C := 6*Real.exp 24*(Real.exp 1)^2
  have cpos : 0<C := by dsimp [C]; positivity
  have c1 : 1≤C := by
    have h1 := Real.one_le_exp (show (0:ℝ)≤1 by norm_num)
    have h24 := Real.one_le_exp (show (0:ℝ)≤24 by norm_num)
    dsimp [C]
    nlinarith [mul_nonneg (sub_nonneg.mpr h24) (sq_nonneg (Real.exp 1)),
      mul_nonneg (sub_nonneg.mpr h1) (by positivity : 0 ≤ Real.exp 1+1)]
  refine ⟨C,cpos,?_⟩
  filter_upwards [prime_budget,eventually_ge_atTop 6] with k pb hk s d hd eq
  have kr : 6 ≤ (k:ℝ) := by exact_mod_cast hk
  have dr : (k:ℝ) ≤ d := by exact_mod_cast hd
  have kp : (0:ℝ)<k := by linarith
  have dp : (0:ℝ)<d := by linarith
  obtain ⟨sl,su⟩ := size hk hd eq
  have gap : (k:ℝ)^2 ≤ C*d := by
    by_cases big : (k:ℝ)^2 ≤ d
    · exact big.trans (le_mul_of_one_le_left dp.le c1)
    have height : (s:ℝ)+k ≤ (2*(k:ℝ))^3 := by
      nlinarith [mul_nonneg kp.le (sub_nonneg.mpr (le_of_not_ge big)),
        mul_nonneg (sub_nonneg.mpr kr) (sq_nonneg (k:ℝ))]
    have smooth : ((s:ℝ)+k)^(2*k).primeCounting ≤ (Real.exp 24)^k := by
      calc
        _ ≤ ((2*(k:ℝ))^3)^(2*k).primeCounting := pow_le_pow_left₀ (by positivity) height _
        _ = Real.exp (((2*k).primeCounting:ℝ)*(3*Real.log (2*(k:ℝ)))) := by
          have leq : 3*Real.log (2*(k:ℝ))=Real.log ((2*(k:ℝ))^3) := by
            simpa only [Nat.cast_ofNat] using (Real.log_pow (2*(k:ℝ)) 3).symm
          rw [leq,Real.exp_nat_mul,Real.exp_log (by positivity)]
        _ ≤ Real.exp ((k:ℝ)*24) := by apply Real.exp_le_exp.mpr; linarith
        _ = _ := Real.exp_nat_mul _ _
    have dv : block s k ∣ block (s+d) k := by rw [eq]; exact dvd_mul_left _ _
    have combin := difference_bound (by omega : 0<k) hd dv
    have comb : (((s+k).choose k:ℕ):ℝ) ≤
      ((s:ℝ)+k)^(2*k).primeCounting * ((d+k).choose (2*k):ℕ) := by exact_mod_cast combin
    have bd : ((d:ℝ)/6)^k ≤ (Real.exp 24*(Real.exp 1*d/k)^2)^k := by
      apply (mul_le_mul_iff_right₀ (pow_pos kp k)).mp
      calc
        (k:ℝ)^k*((d:ℝ)/6)^k = ((k:ℝ)*d/6)^k := by rw [←mul_pow]; ring_nf
        _ ≤ (s:ℝ)^k := pow_le_pow_left₀ (by positivity) sl _
        _ ≤ _ := (lower_choose s k).trans (mul_le_mul_of_nonneg_left comb (by positivity))
        _ ≤ (k:ℝ)^k*((Real.exp 24)^k*(Real.exp 1*d/k)^(2*k)) := by
          gcongr
          exact upper_choose hd (by omega)
        _ = _ := by rw [mul_pow,←pow_mul]
    have b := le_of_pow_le_pow_left₀ (by omega : k≠0) (by positivity) bd
    have b' : d*(k:ℝ)^2 ≤ 6*Real.exp 24*(Real.exp 1)^2*d^2 := by
      field_simp at b
      nlinarith only [b]
    apply (mul_le_mul_iff_right₀ dp).mp
    dsimp [C]; nlinarith only [b']
  refine ⟨gap,?_⟩
  nlinarith [mul_nonneg (sub_nonneg.mpr gap) kp.le,
    mul_nonneg (show 0≤6*(s:ℝ)-k*d by linarith) cpos.le]

end OMA.Gap686

/- The ten-factor case of Erdős 686. The leading polynomial of the
square root has odd values at odd centers. This rules out large centers;
for the remaining interval we bracket each target between consecutive
values of the strictly increasing integer product. -/
namespace OMA.Ten686

def P (x : ℤ) := (x^2-1)*(x^2-9)*(x^2-25)*(x^2-49)*(x^2-81)
def G (x : ℤ) := 8*x^5-660*x^3+7887*x
def R (x : ℤ) := 649000*x^4-5457375*x^2+57153600

lemma identity (x : ℤ) : G x^2 - 64*P x = R x := by unfold G P R; ring

lemma at_large {x : ℤ} (hx : 200000 ≤ x) : 0≤R x ∧ 2*R x<G x := by
  obtain ⟨t,ht⟩ := le_iff_exists_nonneg_add.mp hx
  rcases ht with ⟨ht,rfl⟩
  constructor
  · unfold R
    ring_nf
    positivity
  · rw [←sub_pos]
    unfold R G
    ring_nf
    positivity

lemma no_large {n m : ℕ} (sep : n ≤ m) (yn : 200000 ≤ 2*(n:ℤ)+11) :
    P (2*(m:ℤ)+11) ≠ 4*P (2*(n:ℤ)+11) := by
  let x := 2*(m:ℤ)+11
  let y := 2*(n:ℤ)+11
  intro eq
  change P x=4*P y at eq
  have yx : y≤x := by dsimp [x,y]; omega
  have hb := at_large (yn.trans yx)
  have ha := at_large yn
  change 0≤R y ∧ 2*R y<G y at ha
  have hx : 0<G x := by linarith
  have hy : 0<G y := by linarith
  have dif : G x^2 - (2*G y)^2 = R x-4*R y := by
    linear_combination identity x - 4*identity y + 64*eq
  have gap : G x≠2*G y := by
    intro bad
    have h : G x % 2 = 1 := by
      have t : G x = 2*(4*x^5-330*x^3+3943*x+(m:ℤ)+5)+1 := by unfold G; dsimp [x]; ring
      rw [t]; omega
    rw [bad] at h
    omega
  rcases lt_or_gt_of_ne gap with lt | gt
  · have h : G x+1≤2*G y := by omega
    nlinarith [mul_nonneg (by linarith : 0 ≤ 2*G y-G x-1) (by linarith : 0≤2*G y+G x)]
  · have h : 2*G y+1≤G x := by omega
    nlinarith [mul_nonneg (by linarith : 0 ≤ G x-2*G y-1) (by linarith : 0≤G x+2*G y)]

def F (n : ℕ) := (n+1)*(n+2)*(n+3)*(n+4)*(n+5)*(n+6)*(n+7)*(n+8)*(n+9)*(n+10)

lemma centered (n : ℕ) : 1024*(F n:ℤ)=P (2*(n:ℤ)+11) := by
  unfold F P; push_cast; ring

lemma monoF : StrictMono F := by
  apply strictMono_nat_of_lt_succ
  intro n
  dsimp [F]
  gcongr <;> omega

/-- This integer is only a proposed bracket. The verifier checks the endpoints
themselves, so no floating-point or irrational approximation enters the proof. -/
def middle (n : ℕ) := (1148698355*(2*n+11)/1000000000-11)/2
def brackets (v e : ℕ) := F e < v && v < F (e+1)
def good (n : ℕ) :=
  let v := 4*F n
  let e := middle n
  v < F (n+10) || brackets v e || brackets v (e-1) || brackets v (e-2)

lemma ruled_by_bracket {m v e : ℕ} (h : brackets v e) : F m≠v := by
  simp only [brackets,Bool.and_eq_true,decide_eq_true_eq] at h
  rcases le_or_gt m e with hm | hm
  · exact ne_of_lt ((monoF.monotone hm).trans_lt h.1)
  · exact ne_of_gt (h.2.trans_le (monoF.monotone hm))

lemma ruled {m n : ℕ} (sep : n+10 ≤ m) (h : good n) : F m ≠ 4*F n := by
  simp only [good,Bool.or_eq_true,decide_eq_true_eq] at h
  rcases h with ((h|h)|h)|h
  · exact ne_of_gt (h.trans_le (monoF.monotone sep))
  all_goals exact ruled_by_bracket h

def interval (n : ℕ) : ℕ → Bool
  | 0 => good n
  | l+1 => interval n l && interval (n+2^l) l

lemma interval_sound {d n : ℕ} (h : interval n d) {x : ℕ} (lo : n≤x) (hi : x<n+2^d) : good x := by
  induction d generalizing n with
  | zero =>
    simp only [pow_zero] at hi
    obtain rfl : n=x := by omega
    exact h
  | succ d ih =>
    simp only [interval,Bool.and_eq_true] at h
    obtain ⟨a,b⟩ := h
    rw [pow_succ] at hi
    by_cases side : x<n+2^d
    · exact ih a lo side
    · exact ih b (by omega) (by omega)

end OMA.Ten686

namespace OMA.Ten686

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma all_small : interval 0 17 := by decide +kernel

theorem no_ten {m n : ℕ} (sep : n+10 ≤ m) : F m≠4*F n := by
  by_cases h : 200000 ≤ 2*(n:ℤ)+11
  · intro eq
    apply no_large (by omega : n ≤ m) h
    rw [←centered,←centered,eq]
    push_cast; ring
  · exact ruled sep (interval_sound all_small (by omega) (by norm_num; omega))

end OMA.Ten686

/- Consequences for the precise consecutive-products predicate in problem 686. -/
namespace OMA.Gap686
open Finset Filter

lemma block_Icc (s k : ℕ) : (∏ i ∈ Icc 1 k, (s+i))=block s k := by
  rw [show Icc 1 k = Ico 1 (k+1) by ext i; simp,prod_Ico_eq_prod_range]
  simp [block,Nat.add_comm,Nat.add_left_comm]

def four (k n m : ℕ) : Prop := 2 ≤ k ∧ n+k ≤ m ∧
  (4:ℚ) = ((∏ i ∈ Icc 1 k,(m+i)):ℕ) / ((∏ i ∈ Icc 1 k,(n+i)):ℕ)

lemma equation {k n m : ℕ} (h : four k n m) : block m k=4*block n k := by
  have q := h.2.2
  rw [block_Icc,block_Icc] at q
  have b := (eq_div_iff (by exact_mod_cast (block_pos n k).ne' : ((block n k:ℕ):ℚ)≠0)).mp q
  exact_mod_cast b.symm

theorem growing_gap : ∃ C : ℝ, 0<C ∧ ∀ᶠ k : ℕ in atTop,
    ∀ n m : ℕ, four k n m → (k:ℝ)^2 ≤ C*(m-n:ℕ) ∧ (k:ℝ)^3 ≤ 6*C*n := by
  obtain ⟨C,hc,ev⟩ := obstruction
  refine ⟨C,hc,?_⟩
  filter_upwards [ev] with k hk n m h
  have sep := h.2.1
  exact hk n (m-n) (by omega) (by simpa [Nat.add_sub_of_le (by omega : n ≤ m)] using equation h)

theorem no_ten (m n : ℕ) : ¬ four 10 n m := by
  intro h
  have e := equation h
  have ident (v : ℕ) : block v 10=OMA.Ten686.F v := by
    rw [block,←Nat.ascFactorial_eq_prod_range]
    simp [Nat.ascFactorial,OMA.Ten686.F]
    ring
  simp only [ident] at e
  exact OMA.Ten686.no_ten h.2.1 e

end OMA.Gap686
#print axioms OMA.Gap686.growing_gap
#print axioms OMA.Gap686.no_ten

/- The centered coordinates of a quotient-four solution lie just below
the ray of slope 4^(1/k). Pair terms with their reflections in each block. -/
namespace OMA.Slope686
open Finset OMA.Gap686

private def center (s k : ℕ) : ℝ := 2*s+k+1
private def offset (k i : ℕ) : ℝ := 2*i+1-k

private lemma paired (s k : ℕ) :
    ∏ i ∈ range k, (center s k ^ 2 - offset k i ^ 2) =
      ((2:ℝ)^k * (block s k:ℝ))^2 := by
  let f (i : ℕ) : ℝ := 2*((s:ℝ)+1+i)
  have single : ∏ i ∈ range k, f i = (2:ℝ)^k * (block s k:ℝ) := by
    simp [f,block,prod_mul_distrib]
  calc
    _ = ∏ i ∈ range k, (f i * f (k-1-i)) := by
      apply prod_congr rfl
      intro i hi
      have il := mem_range.mp hi
      have eq : ((k-1-i:ℕ):ℝ) = (k:ℝ)-1-i := by
        rw [Nat.cast_sub (by omega),Nat.cast_sub (by omega),Nat.cast_one]
      dsimp [center,offset,f]
      rw [eq]
      ring
    _ = _ := by rw [prod_mul_distrib,prod_range_reflect,single]; ring

theorem strip {k n m : ℕ} (h : OMA.Gap686.four k n m)
    (hy : 2*(k:ℝ) ≤ 2*n+k+1) :
    let Y : ℝ := 2*n+k+1
    let X : ℝ := 2*m+k+1
    0 ≤ (4:ℝ)^(1/(k:ℝ))*Y-X ∧ (4:ℝ)^(1/(k:ℝ))*Y-X ≤ 8*k/Y := by
  let Y := center n k
  let X := center m k
  let a : ℝ := (4:ℝ)^(1/(k:ℝ))
  let r := X/Y
  let u := 8*(k:ℝ)/Y^2
  change 0 ≤ a*Y-X ∧ a*Y-X ≤ 8*k/Y
  have hk := h.1
  have hm : n ≤ m := by have := h.2.1; omega
  have kp : 0<(k:ℝ) := by exact_mod_cast (by omega : 0<k)
  have kt : 2≤(k:ℝ) := by exact_mod_cast hk
  have yp : 0<Y := by dsimp [Y,center]; positivity
  have cy : 2*(k:ℝ)≤Y := hy
  have ry : r*Y=X := div_mul_cancel₀ _ yp.ne'
  have rr : 1≤r := by
    apply (le_div_iff₀ yp).mpr
    dsimp [X,Y,center]
    linarith [show (n:ℝ) ≤ m by exact_mod_cast hm]
  have rp : 0≤r := by linarith
  have ap : 0<a := Real.rpow_pos_of_pos (by norm_num) _
  have ak : a^k=4 := by
    dsimp [a]
    rw [one_div,Real.rpow_inv_natCast_pow (by norm_num) (by omega)]
  have asq : (a^2)^k=16 := by rw [←pow_mul,Nat.mul_comm,pow_mul,ak]; norm_num
  let F (i : ℕ) := (X^2-offset k i^2)/(Y^2-offset k i^2)
  have bounds {i : ℕ} (hi : i∈range k) : offset k i^2 ≤ (k:ℝ)^2 := by
    have il : (i:ℝ)+1 ≤ k := by exact_mod_cast mem_range.mp hi
    have ha : -(k:ℝ)≤offset k i := by dsimp [offset]; linarith [Nat.cast_nonneg (α:=ℝ) i]
    have hb : offset k i≤k := by dsimp [offset]; linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hb) (show 0 ≤ k+offset k i by linarith)]
  have yy : 4*(k:ℝ)^2 ≤ Y^2 := by
    nlinarith [sq_le_sq' (by linarith : -Y≤2*(k:ℝ)) cy]
  have den {i : ℕ} (hi : i∈range k) : 0<Y^2-offset k i^2 := by
    nlinarith [bounds hi,sq_pos_of_pos yp]
  have prodF : ∏ i ∈ range k, F i = 16 := by
    dsimp [F,X,Y]
    rw [prod_div_distrib,paired,paired]
    have eq : (block m k:ℝ)=4*(block n k:ℝ) := by exact_mod_cast equation h
    have bp : 0<(block n k:ℝ) := by exact_mod_cast block_pos n k
    rw [eq]
    field_simp
    ring
  have low (i : ℕ) (hi : i∈range k) : r^2≤F i := by
    apply (le_div_iff₀ (den hi)).mpr
    rw [←ry]
    nlinarith [mul_nonneg (show 0≤r^2-1 by nlinarith [sq_nonneg (r-1)]) (sq_nonneg (offset k i))]
  have ra : r≤a := by
    have step := prod_le_prod (s:=range k) (f:=fun _ => r^2) (g:=F) (fun _ _ => sq_nonneg _) low
    simp only [prod_const,card_range,prodF,←asq] at step
    have := le_of_pow_le_pow_left₀ (by omega : k≠0) (sq_nonneg a) step
    nlinarith [sq_nonneg (r-a)]
  have rk : r^k ≤ 4 := ak ▸ pow_le_pow_left₀ rp ra k
  have kr : (k:ℝ)*(r-1) ≤ 3 := by
    have bern := one_add_mul_le_pow (a:=r-1) (by linarith) k
    rw [show 1+(r-1)=r by ring] at bern
    linarith
  have rbound : r≤5/2 := by nlinarith [mul_nonneg (sub_nonneg.mpr kt) (sub_nonneg.mpr rr)]
  have excess : (r^2-1)*(k:ℝ)^2 ≤ 11*k := by
    have H := mul_le_mul kr (show r+1≤7/2 by linarith) (by linarith : 0≤r+1) (by norm_num : (0:ℝ)≤3)
    nlinarith [mul_le_mul_of_nonneg_right H kp.le]
  have up : 0≤u := by dsimp [u]; positivity
  have uy : u*Y^2=8*k := div_mul_cancel₀ _ (pow_ne_zero _ yp.ne')
  have high (i : ℕ) (hi : i∈range k) : F i≤(r+u)^2 := by
    apply (div_le_iff₀ (den hi)).mpr
    rw [←ry]
    let z := offset k i
    have loss : (r^2-1)*z^2 ≤ 11*k := (mul_le_mul_of_nonneg_left (bounds hi)
      (by nlinarith [sq_nonneg (r-1)] : 0≤r^2-1)).trans excess
    have saving : 12*k ≤ (2*u)*(Y^2-z^2) := by
      have dz : 3*Y^2 ≤ 4*(Y^2-z^2) := by dsimp [z]; nlinarith [bounds hi]
      nlinarith [mul_le_mul_of_nonneg_left dz up]
    have rad : r^2+2*u ≤ (r+u)^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr rr) up,sq_nonneg u]
    have lift := mul_le_mul_of_nonneg_right rad (den hi).le
    change (r*Y)^2-z^2 ≤ (r+u)^2*(Y^2-z^2)
    change (r^2+2*u)*(Y^2-z^2) ≤ (r+u)^2*(Y^2-z^2) at lift
    nlinarith only [loss,saving,lift]
  have au : a≤r+u := by
    have step := prod_le_prod (s:=range k) (f:=F) (g:=fun _ => (r+u)^2)
      (fun i hi => (sq_nonneg r).trans (low i hi)) high
    simp only [prod_const,card_range,prodF,←asq] at step
    have := le_of_pow_le_pow_left₀ (by omega : k≠0) (sq_nonneg (r+u)) step
    nlinarith [sq_nonneg (a-(r+u))]
  constructor
  · linarith [mul_le_mul_of_nonneg_right ra yp.le]
  · apply (le_div_iff₀ yp).mpr
    have b := mul_le_mul_of_nonneg_right au (sq_nonneg Y)
    nlinarith only [b,uy,congrArg (fun v:ℝ => v*Y) ry]

end OMA.Slope686

/- Strict concavity of the locus of two blocks with fixed quotient. -/
namespace OMA.Curve686
open Finset Real Set

noncomputable def cost (t : ℝ) := Real.log (t+1) - Real.log t

lemma cost_deriv {t : ℝ} (ht : 0<t) : HasDerivAt cost (-(1/(t*(t+1)))) t := by
  have h := (((hasDerivAt_id t).add_const 1).log (by change t+1≠0; positivity)).sub
    ((hasDerivAt_id t).log ht.ne')
  have eval : -(1/(t*(t+1))) = 1/(t+1)-1/t := by field_simp; ring
  rw [eval]
  exact h

lemma cost_convex : StrictConvexOn ℝ (Ioi 0) cost := by
  apply StrictMonoOn.strictConvexOn_of_deriv (convex_Ioi _)
  · exact fun t ht => (cost_deriv ht).continuousAt.continuousWithinAt
  · rw [isOpen_Ioi.interior_eq]
    intro x hx y hy hxy
    change 0<x at hx
    change 0<y at hy
    rw [(cost_deriv hx).deriv,(cost_deriv hy).deriv,neg_lt_neg_iff]
    apply one_div_lt_one_div_of_lt (by positivity)
    exact mul_lt_mul_of_pos hxy (by linarith) (by positivity) (by positivity)

noncomputable def total (k : ℕ) (n d : ℝ) := ∑ i ∈ range k, cost ((n+1+i)/d)

lemma total_ratio {k n m : ℕ} (h : OMA.Gap686.four k n m) :
    total k n ((m:ℝ)-n) = Real.log 4 := by
  have hk := h.1
  have hd := h.2.1
  have md : n < m := by omega
  have r := OMA.Gap686.ratio (s:=n) (d:=m-n) (k:=k) (by
    simpa [Nat.add_sub_of_le md.le] using OMA.Gap686.equation h)
  rw [Nat.cast_sub md.le] at r
  have posd : 0<(m:ℝ)-n := sub_pos.mpr (by exact_mod_cast md)
  have term (i : ℕ) : cost (((n:ℝ)+1+i)/(m-n)) = Real.log (1+((m:ℝ)-n)/(n+1+i)) := by
    rw [cost,←Real.log_div (by positivity) (by positivity)]
    congr 1
    field_simp
  rw [total]; simp_rw [term]; rw [←Real.log_prod, r]
  exact fun i _ => by positivity

/-- Increasing the gap increases the logarithm of the product quotient. -/
lemma total_mono {k : ℕ} {n a b : ℝ} (hn : 0≤n) (ha : 0<a) (hab : a≤b) :
    total k n a ≤ total k n b := by
  apply sum_le_sum
  intro i _
  have hb := ha.trans_le hab
  rw [cost,cost,←Real.log_div (by positivity) (by positivity),
    ←Real.log_div (by positivity) (by positivity)]
  apply Real.log_le_log (by positivity)
  have eval (d : ℝ) (hd : 0<d) :
      ((n+1+i)/d+1)/((n+1+i)/d) = 1+d/(n+1+i) := by field_simp
  rw [eval a ha,eval b hb]
  gcongr

/-- The gap linearly interpolated between two solutions has a strictly smaller quotient. -/
theorem chord {k : ℕ} (hk : 2≤k) {x y d e a b : ℝ}
    (hx : 0≤x) (hy : 0≤y) (hxy : x<y) (hd : 0<d) (he : 0<e)
    (ha : 0<a) (hb : 0<b) (hs : a+b=1) :
    total k (a*x+b*y) (a*d+b*e) <
      (a*d/(a*d+b*e))*total k x d + (b*e/(a*d+b*e))*total k y e := by
  let D := a*d+b*e
  have hD : 0<D := by dsimp [D]; positivity
  let u := a*d/D
  let v := b*e/D
  have hu : 0<u := by dsimp [u]; positivity
  have hv : 0<v := by dsimp [v]; positivity
  have huv : u+v=1 := by dsimp [u,v,D]; field_simp
  let X (i : ℕ) := (x+1+i)/d
  let Y (i : ℕ) := (y+1+i)/e
  have Xpos (i : ℕ) : 0<X i := by dsimp [X]; positivity
  have Ypos (i : ℕ) : 0<Y i := by dsimp [Y]; positivity
  have bary (i : ℕ) : (a*x+b*y+1+i)/D = u*(X i)+v*(Y i) := by
    dsimp [u,v,X,Y]
    field_simp
    nlinarith [congrArg (fun t : ℝ => t*(i:ℝ)) hs]
  have distinct : ∃ i ∈ range k, X i ≠ Y i := by
    by_contra! eq
    have f := eq 0 (mem_range.mpr (by omega))
    have g := eq 1 (mem_range.mpr (by omega))
    dsimp [X,Y] at f g
    field_simp at f g
    norm_num at f g
    have same : d=e := by nlinarith only [f,g]
    subst e
    nlinarith [mul_pos (sub_pos.mpr hxy) hd]
  change (∑ i ∈ range k, cost ((a*x+b*y+1+i)/D)) <
    u*(∑ i ∈ range k, cost (X i))+v*(∑ i ∈ range k, cost (Y i))
  simp_rw [bary]
  rw [mul_sum,mul_sum,←sum_add_distrib]
  apply sum_lt_sum
  · exact fun i _ => cost_convex.convexOn.2 (Xpos i) (Ypos i) hu.le hv.le huv
  · obtain ⟨i,hi,ne⟩ := distinct
    exact ⟨i,hi,cost_convex.2 (Xpos i) (Ypos i) ne hu hv huv⟩

theorem secants {k a b c u v w : ℕ} (h₁ : OMA.Gap686.four k a u)
    (h₂ : OMA.Gap686.four k b v) (h₃ : OMA.Gap686.four k c w)
    (hab : a < b) (hbc : b < c) :
    ((v:ℝ)-u)*((c:ℝ)-b) > ((w:ℝ)-v)*((b:ℝ)-a) := by
  have ab : (a:ℝ)<b := by exact_mod_cast hab
  have bc : (b:ℝ)<c := by exact_mod_cast hbc
  have ac := ab.trans bc
  let l := ((c:ℝ)-b)/(c-a)
  let r := ((b:ℝ)-a)/(c-a)
  have hl : 0<l := div_pos (sub_pos.mpr bc) (sub_pos.mpr ac)
  have hr : 0<r := div_pos (sub_pos.mpr ab) (sub_pos.mpr ac)
  have hsum : l+r=1 := by dsimp [l,r]; field_simp; ring
  have hbary : l*a+r*c = b := by dsimp [l,r]; field_simp; ring
  have gap {x y : ℕ} (h : OMA.Gap686.four k x y) : 0<(y:ℝ)-x := by
    have sep := h.2.1
    have hk := h.1
    apply sub_pos.mpr
    exact_mod_cast (show x < y by omega)
  have low := chord h₁.1 (Nat.cast_nonneg a) (Nat.cast_nonneg c) ac
    (gap h₁) (gap h₃) hl hr hsum
  rw [hbary,total_ratio h₁,total_ratio h₃,←add_mul,←add_div,div_self,one_mul] at low
  · have cmp : l*((u:ℝ)-a)+r*((w:ℝ)-c) < (v:ℝ)-b := by
      by_contra! rev
      have t := total_mono (k:=k) (Nat.cast_nonneg b) (gap h₂) rev
      rw [total_ratio h₂] at t
      linarith
    dsimp [l,r] at cmp
    field_simp [sub_pos.mpr ac] at cmp
    linarith only [cmp]
  · exact (add_pos (mul_pos hl (gap h₁)) (mul_pos hr (gap h₃))).ne'

end OMA.Curve686

/- A convex chain of lattice points in an oblique strip. Consecutive edge
    vectors span a triangle of area at least one half. After rescaling the
    strip, the slope coordinate v/(u+|v|) converts this into a spacing bound.
    This is a direct argument, with no lattice point asymptotics. -/
namespace OMA.LatticeStrip686
open Finset

private lemma telescope (f : ℕ→ℝ) (n : ℕ) :
    ∑ i∈range n, (f (i+1)-f i) = f n-f 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ,ih]; ring

private lemma variation (n : ℕ) (z : ℕ→ℝ) (zbound : ∀i≤n, |z i|≤1)
    (dec : ∀i, i+1<n → z (i+1)≤z i → z (i+2)≤z (i+1)) :
    ∑ i∈range n, |z (i+1)-z i| ≤ 4 := by
  classical
  obtain ⟨m,hm,pos,neg⟩ : ∃ m≤n, (∀ i < m, z i≤z (i+1)) ∧
      ∀ i, m ≤ i → i<n → z (i+1)≤z i := by
    by_cases h : ∃i, i<n ∧ z (i+1)≤z i
    · let m := Nat.find h
      have start : m<n ∧ z (m+1)≤z m := Nat.find_spec h
      refine ⟨m,start.1.le,fun i hi => ?_,fun i hi => ?_⟩
      · exact le_of_not_ge (fun bad => Nat.find_min h hi ⟨hi.trans start.1,bad⟩)
      · induction i, hi using Nat.le_induction with
        | base => exact fun _ => start.2
        | succ i _ ih => exact fun hx => dec i hx (ih (by omega))
    · push Not at h
      exact ⟨n,le_rfl,fun i hi => (h i hi).le,fun i hi hlt => by omega⟩
  have telesc (j : ℕ) (hj : j≤n) :
      ∑ i∈range j, |z (i+1)-z i| =
        if j ≤ m then z j-z 0 else 2*z m-z 0-z j := by
    induction j with
    | zero => simp
    | succ i ih =>
      rw [sum_range_succ,ih (by omega)]
      rcases lt_trichotomy i m with h|h|h
      · rw [if_pos h.le,if_pos (by omega),abs_of_nonneg (sub_nonneg.mpr (pos i h))]; ring
      · subst i
        rw [if_pos le_rfl,if_neg (by omega),abs_of_nonpos (sub_nonpos.mpr (neg m le_rfl (by omega)))]; ring
      · rw [if_neg (by omega),if_neg (by omega),
          abs_of_nonpos (sub_nonpos.mpr (neg i h.le (by omega)))]; ring
  have h0 := abs_le.mp (zbound 0 (by omega))
  have hn := abs_le.mp (zbound n le_rfl)
  have hpeak := abs_le.mp (zbound m hm)
  rw [telesc n le_rfl]
  split <;> linarith

private lemma direction {u v a b : ℝ} (hu : 0<u) (ha : 0<a) (H : 0<v*a-b*u) :
    v*a-b*u ≤ (u+|v|)*(a+|b|)*(v/(u+|v|)-b/(a+|b|)) := by
  have au : 0<u+|v| := by positivity
  have aa : 0<a+|b| := by positivity
  rw [show (u+|v|)*(a+|b|)*(v/(u+|v|)-b/(a+|b|)) =
    v*(a+|b|)-b*(u+|v|) by field_simp]
  rcases le_or_gt 0 v with hv|hv <;> rcases le_or_gt 0 b with hb|hb
  · rw [abs_of_nonneg hv,abs_of_nonneg hb]; linarith
  · rw [abs_of_nonneg hv,abs_of_neg hb]; nlinarith [mul_nonpos_of_nonneg_of_nonpos hv hb.le]
  · nlinarith [mul_neg_of_neg_of_pos hv ha,mul_nonneg hb hu.le]
  · rw [abs_of_neg hv,abs_of_neg hb]; linarith

private lemma pack (k : ℕ) (H : ℝ) (hH : 0<H) (u v : ℕ→ℝ)
    (hu : ∀i≤k, 0<u i) (budget : ∑i∈range (k+1), (u i+|v i|) ≤ 5)
    (det : ∀i<k, 1≤H*(v i*u (i+1)-v (i+1)*u i)) : (k:ℝ)^3 ≤ 1600*H := by
  let l (i : ℕ) := u i+|v i|
  let z (i : ℕ) := v i/l i
  have hl (i : ℕ) (hi : i≤k) : 0<l i := add_pos_of_pos_of_nonneg (hu i hi) (abs_nonneg _)
  have hz (i : ℕ) (hi : i≤k) : |z i|≤1 := by
    dsimp only [z]; rw [abs_div,abs_of_pos (hl i hi)]
    apply (div_le_one (hl i hi)).2
    dsimp [l]; linarith [hu i hi]
  have gap (i : ℕ) (hi : i<k) : 1 ≤ H*((l i*l (i+1))*(z i-z (i+1))) := by
    apply (det i hi).trans
    apply mul_le_mul_of_nonneg_left _ hH.le
    apply direction (hu i hi.le) (hu _ (by omega))
    exact pos_of_mul_pos_right (lt_of_lt_of_le zero_lt_one (det i hi)) hH.le
  by_cases hk : k=0
  · simp [hk,hH.le]
  have kp : (0:ℝ)<k := by exact_mod_cast Nat.pos_of_ne_zero hk
  let t : ℝ := 20/k
  have ht : 0<t := by dsimp [t]; positivity
  have point (i : ℕ) (hi : i<k) :
      1 ≤ (l i+l (i+1))/t + H*t^2*(z i-z (i+1)) := by
    have g := gap i hi
    have lg : 0<l i*l (i+1) := mul_pos (hl _ hi.le) (hl _ (by omega))
    have gp : 0<z i-z (i+1) :=
      pos_of_mul_pos_right (pos_of_mul_pos_right (zero_lt_one.trans_le g) hH.le) lg.le
    by_cases big : t≤l i+l (i+1)
    · have first : 1≤(l i+l (i+1))/t := (one_le_div ht).mpr big
      linarith [mul_pos (mul_pos hH (sq_pos_of_pos ht)) gp]
    · have small : l i*l (i+1) ≤ t^2 := by
        have a := hl i hi.le
        have b := hl (i+1) (by omega)
        calc
          _ ≤ t*t := mul_le_mul (by linarith) (by linarith) b.le ht.le
          _ = _ := by ring
      have sc := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right small gp.le) hH.le
      have first : 0≤(l i+l (i+1))/t :=
        div_nonneg (add_nonneg (hl i hi.le).le (hl _ (by omega)).le) ht.le
      linarith
  have ls : ∑ i∈range k, (l i+l (i+1)) ≤ 10 := by
    change ∑ i∈range (k+1), l i ≤ 5 at budget
    have a := budget
    have b := budget
    rw [sum_range_succ] at a
    rw [sum_range_succ'] at b
    rw [sum_add_distrib]
    linarith [hl 0 (by omega),hl k le_rfl]
  have gs : ∑ i∈range k, (z i-z (i+1)) ≤ 2 := by
    have tel := telescope (fun i => -z i) k
    simp only [neg_sub_neg] at tel
    rw [tel]
    linarith [(abs_le.mp (hz 0 (by omega))).2,(abs_le.mp (hz k le_rfl)).1]
  have total := sum_le_sum (s:=range k) (fun i hi => point i (mem_range.mp hi))
  rw [sum_add_distrib,←sum_div,←mul_sum] at total
  simp only [sum_const,card_range,nsmul_eq_mul,mul_one] at total
  have main : (k:ℝ) ≤ 10/t+H*t^2*2 := by
    exact total.trans (add_le_add (div_le_div_of_nonneg_right ls ht.le)
      (mul_le_mul_of_nonneg_left gs (by positivity)))
  dsimp [t] at main
  field_simp at main
  nlinarith only [main]

/-- If k+2 points in increasing x are on a strictly concave lattice chain
    in a strip about an affine function, its width times its height controls
    the cube of k. The integers x,y may be negative. -/
theorem bound (k : ℕ) (x y : ℕ→ℤ) (T h s b : ℝ) (hT : 0<T) (hh : 0<h)
    (inc : ∀ i < k+1, x i<x (i+1))
    (width : (x (k+1):ℝ)-(x 0:ℝ)≤T)
    (strip : ∀ i ≤ k+1, |(y i:ℝ)-s*(x i:ℝ)-b|≤h)
    (conc : ∀ i < k, (y (i+1)-y i)*(x (i+2)-x (i+1)) >
      (y (i+2)-y (i+1))*(x (i+1)-x i)) : (k:ℝ)^3≤1600*T*h := by
  let d (i : ℕ) := x (i+1)-x i
  let e (i : ℕ) := y (i+1)-y i
  let u (i : ℕ) := (d i:ℝ)/T
  let v (i : ℕ) := ((e i:ℝ)-s*(d i:ℝ))/h
  let z (i : ℕ) := ((y i:ℝ)-s*(x i:ℝ)-b)/h
  have eqv (i : ℕ) : z (i+1)-z i=v i := by dsimp [z,v,d,e]; push_cast; ring
  have upos (i : ℕ) (hi : i≤k) : 0<u i := by
    apply div_pos _ hT
    exact_mod_cast sub_pos.mpr (inc i (by omega))
  have det (i : ℕ) (hi : i<k) : 1 ≤ T*h*(v i*u (i+1)-v (i+1)*u i) := by
    have integer : (1:ℤ) ≤ e i*d (i+1)-e (i+1)*d i := by
      have pos : e (i+1)*d i < e i*d (i+1) := by
        simpa only [e,d,Nat.add_assoc] using conc i hi
      omega
    calc
      (1:ℝ) ≤ ((e i*d (i+1)-e (i+1)*d i:ℤ):ℝ) := by exact_mod_cast integer
      _ = _ := by dsimp only [v,u]; push_cast; field_simp; ring
  have xmass : ∑i∈range (k+1),u i ≤ 1 := by
    dsimp only [u,d]
    push_cast
    rw [←sum_div,telescope (fun i => (x i:ℝ))]
    exact (div_le_one hT).mpr width
  have ymass : ∑i∈range (k+1), |v i| ≤ 4 := by
    simp_rw [←eqv]
    apply variation
    · intro i hi; dsimp only [z]; rw [abs_div,abs_of_pos hh]
      exact (div_le_one hh).mpr (strip i hi)
    · intro i hi hprev
      have hv : v i≤0 := eqv i ▸ sub_nonpos.mpr hprev
      have D := pos_of_mul_pos_right (zero_lt_one.trans_le (det i (by omega))) (mul_pos hT hh).le
      apply sub_nonpos.mp
      rw [eqv]
      by_contra! bad
      linarith [mul_nonpos_of_nonpos_of_nonneg hv (upos (i+1) (by omega)).le,
        mul_pos bad (upos i (by omega))]
  have total : ∑i∈range (k+1), (u i+|v i|) ≤ 5 := by
    rw [sum_add_distrib]; linarith only [xmass,ymass]
  simpa [mul_assoc] using pack k (T*h) (mul_pos hT hh) u v upos total det

end OMA.LatticeStrip686

/- Count distinct starting points of quotient-four solutions. Blocks starting
    at the ninth power of a dyadic parameter make the geometric sum integral. -/
namespace OMA.CountStarts686
open Finset Filter OMA.Gap686

private abbrev Secants :=
  ∀ {k a b c u v w : ℕ}, four k a u → four k b v → four k c w → a<b → b<c →
    ((v:ℝ)-u)*((c:ℝ)-b) > ((w:ℝ)-v)*((b:ℝ)-a)

private theorem lengths : ∃ A : ℕ, 1≤A ∧ ∀ k n m : ℕ, four k n m → k^3≤A*(n+1) := by
  obtain ⟨C,hC,large⟩ := growing_gap
  obtain ⟨K,hK⟩ := eventually_atTop.mp large
  let A := K^3+⌈6*C⌉₊+1
  refine ⟨A,by dsimp [A]; omega,fun k n m hf => ?_⟩
  by_cases big : K≤k
  · have c : 6*C ≤ (A:ℝ) := by
      have ce := Nat.le_ceil (6*C)
      dsimp [A]; push_cast; linarith [show (0:ℝ)≤(K:ℝ)^3 by positivity]
    have ln := (hK k big n m hf).2
    exact_mod_cast (show (k:ℝ)^3 ≤ (A:ℝ)*((n:ℝ)+1) by
      nlinarith [mul_le_mul_of_nonneg_right c (Nat.cast_nonneg (α:=ℝ) n),
        Nat.cast_nonneg (α:=ℝ) A])
  · have p := Nat.pow_le_pow_left (by omega : k≤K) 3
    have lk : K^3≤A := by dsimp [A]; omega
    exact (p.trans lk).trans (Nat.le_mul_of_pos_right _ (by omega))

private noncomputable def fiber (Y k : ℕ) := by
  classical
  exact (Ico (Y^9) ((2*Y)^9)).filter (fun n => k≤n ∧ ∃m, four k n m)

private lemma fiber_count (sec : Secants) (B Y k : ℕ) (hB : 0<B) (hY : 0<Y)
    (hk : k≤B*Y^3) :
    (fiber Y k).card ≤ (3276800*B+3)*Y := by
  classical
  let S := fiber Y k
  by_cases few : S.card<2
  · change S.card ≤ _
    have l : 2≤3276800*B+3 := by omega
    have w := Nat.le_mul_of_pos_right (3276800*B+3) hY
    omega
  let j := S.card-2
  have size : S.card=j+2 := by dsimp [j]; omega
  let point := S.orderIsoOfFin size
  let x (i : ℕ) : ℕ := if hi : i<j+2 then (point ⟨i,hi⟩).val else 0
  have mem (i : ℕ) (hi : i<j+2) : x i∈S := by
    dsimp only [x]; rw [dif_pos hi]; exact (point _).property
  let y (i : ℕ) := if hi : i<j+2 then
      ((mem_filter.mp (mem i hi)).2.2 : ∃m, four k (x i) m).choose else 0
  have sol (i : ℕ) (hi : i<j+2) : four k (x i) (y i) := by
    dsimp only [y]; rw [dif_pos hi]; exact Exists.choose_spec _
  have slab (i : ℕ) (hi : i<j+2) : Y^9 ≤ x i ∧ x i < (2*Y)^9 :=
    mem_Ico.mp (mem_filter.mp (mem i hi)).1
  have kx (i : ℕ) (hi : i<j+2) : k ≤ x i := (mem_filter.mp (mem i hi)).2.1
  have inc (i : ℕ) (hi : i<j+1) : x i<x (i+1) := by
    dsimp only [x]; rw [dif_pos (by omega),dif_pos (by omega)]
    exact point.strictMono (show (⟨i,by omega⟩:Fin (j+2))<⟨i+1,by omega⟩ by exact Nat.lt_succ_self _)
  let a : ℝ := (4:ℝ)^(1/(k:ℝ))
  let b : ℝ := ((k:ℝ)+1)*(a-1)/2
  let H : ℝ := 4*(B:ℝ)*(Y:ℝ)^3/(Y:ℝ)^9
  have yP : 0<(Y:ℝ) := by exact_mod_cast hY
  have bP : 0<(B:ℝ) := by exact_mod_cast hB
  have thick : 0<H := by dsimp [H]; positivity
  have within (i : ℕ) (hi : i≤j+1) :
      |(y i:ℝ)-a*(x i:ℝ)-b|≤H := by
    have h := sol i (by omega)
    have K : (k:ℝ)≤x i := by exact_mod_cast kx i (by omega)
    have X : (Y:ℝ)^9 ≤ x i := by exact_mod_cast (slab i (by omega)).1
    have cross := Slope686.strip h (by linarith)
    change 0≤a*(2*(x i:ℝ)+k+1)-(2*(y i:ℝ)+k+1) ∧ _ at cross
    have lower := cross.1
    have high : a*(2*(x i:ℝ)+k+1)-(2*(y i:ℝ)+k+1) ≤
        8*(k:ℝ)/(2*(x i:ℝ)+k+1) := cross.2
    have div : (k:ℝ)/(2*(x i:ℝ)+k+1) ≤ ((B:ℝ)*(Y:ℝ)^3)/(Y:ℝ)^9 := by
      apply div_le_div₀ (by positivity) (by exact_mod_cast hk) (by positivity)
      linarith [Nat.cast_nonneg (α:=ℝ) k,Nat.cast_nonneg (α:=ℝ) (x i)]
    rw [abs_of_nonpos (by dsimp [b]; linarith only [lower])]
    dsimp [H,b]
    rw [mul_div_assoc] at high
    rw [show 4*(B:ℝ)*(Y:ℝ)^3/Y^9=4*((B:ℝ)*(Y:ℝ)^3/Y^9) by ring]
    linarith only [high,div]
  have cube := LatticeStrip686.bound j (fun i => (x i:ℤ)) (fun i => (y i:ℤ))
    ((2*(Y:ℝ))^9) H a b (by positivity) thick
    (fun i hi => by exact_mod_cast inc i hi)
    (by push_cast; have w : (x (j+1):ℝ)<(2*(Y:ℝ))^9 := by exact_mod_cast (slab (j+1) (by omega)).2
        linarith [Nat.cast_nonneg (α:=ℝ) (x 0)])
    (fun i hi => by simpa using within i hi)
    (fun i hi => by
      have q := sec (sol i (by omega)) (sol (i+1) (by omega)) (sol (i+2) (by omega))
        (inc i (by omega)) (inc (i+1) (by omega))
      exact_mod_cast q)
  have jc : (j:ℝ)^3 ≤ 3276800*(B:ℝ)*(Y:ℝ)^3 := by
    apply cube.trans_eq
    dsimp [H]; field_simp; ring
  have jnat : j^3≤(3276800*B)*(Y^3) := by exact_mod_cast jc
  have coeff : 3276800*B ≤ (3276800*B+1)^3 :=
    (Nat.le_succ _).trans (le_self_pow₀ (by omega) (by decide : 3≠0))
  have jle : j≤(3276800*B+1)*Y := by
    apply le_of_pow_le_pow_left₀ (by decide : 3≠0) (Nat.zero_le _)
    rw [mul_pow]
    exact jnat.trans (Nat.mul_le_mul_right _ coeff)
  change S.card≤_
  rw [size]
  nlinarith

private noncomputable def starts (N : ℕ) : Finset ℕ := by
  classical
  exact (range N).filter (fun n => ∃ k m, four k n m)

private lemma slab_step (sec : Secants) (A : ℕ) (g : ∀k n m, four k n m → k^3≤A*(n+1)) :
    ∃ D : ℕ, 1≤D ∧ ∀Y, 0<Y →
      (starts ((2*Y)^9)).card ≤ (starts (Y^9)).card + D*Y^4 := by
  classical
  let B := 512*A+1
  have bp : 0<B := by dsimp [B]; omega
  let E := 3276800*B+3
  let D := B+(B+1)*E+1
  refine ⟨D,by dsimp [D]; omega,fun Y hy => ?_⟩
  let K := B*Y^3
  have klimit (k n m : ℕ) (up : n<(2*Y)^9) (hf : four k n m) : k≤K := by
    have bd := (g k n m hf).trans (Nat.mul_le_mul_left A up)
    have cf : 512*A ≤ B^3 := (Nat.le_succ _).trans (le_self_pow₀ bp (by decide : 3≠0))
    apply le_of_pow_le_pow_left₀ (by decide : 3≠0) (Nat.zero_le _)
    calc
      k^3 ≤ A*(2*Y)^9 := bd
      _ = (512*A)*Y^9 := by ring
      _ ≤ B^3*Y^9 := Nat.mul_le_mul_right _ cf
      _ = K^3 := by dsimp [K]; ring
  have subset : starts ((2*Y)^9) ⊆ (starts (Y^9) ∪ range K) ∪
      (range (K+1)).biUnion (fiber Y) := by
    intro n hn
    obtain ⟨nr,k,m,hf⟩ := mem_filter.mp hn
    have nb := mem_range.mp nr
    by_cases low : n<Y^9
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨mem_range.mpr low,k,m,hf⟩))
    by_cases nk : n<k
    · exact mem_union_left _ (mem_union_right _ (mem_range.mpr (nk.trans_le (klimit k n m nb hf))))
    · apply mem_union_right _
      apply mem_biUnion.mpr
      refine ⟨k,mem_range.mpr (by have := klimit k n m nb hf; omega),?_⟩
      exact mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega,nb⟩,by omega,m,hf⟩
  have fc : ((range (K+1)).biUnion (fiber Y)).card ≤ (K+1)*(E*Y) := by
    calc
      _ ≤ ∑ k ∈ range (K+1),(fiber Y k).card := card_biUnion_le
      _ ≤ ∑ _k ∈ range (K+1),E*Y := sum_le_sum (fun k h => fiber_count sec B Y k bp hy
            (by have := mem_range.mp h; change k≤K; omega))
      _ = _ := by simp
  have first := card_le_card subset
  have split := card_union_le (starts (Y^9) ∪ range K) ((range (K+1)).biUnion (fiber Y))
  have split2 := card_union_le (starts (Y^9)) (range K)
  rw [card_range] at split2
  have total : (starts ((2*Y)^9)).card ≤ (starts (Y^9)).card+(K+(K+1)*(E*Y)) := by omega
  apply total.trans
  apply Nat.add_le_add_left
  have yp : 1≤Y^3 := Nat.one_le_pow _ _ hy
  have a : K≤B*Y^4 := by
    change B*Y^3≤B*Y^4
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hy (by decide : 3≤4))
  have a' : K+1≤(B+1)*Y^3 := by dsimp [K]; nlinarith only [yp]
  calc
    _ ≤ B*Y^4 + ((B+1)*Y^3)*(E*Y) := Nat.add_le_add a (Nat.mul_le_mul_right _ a')
    _ ≤ D*Y^4 := by dsimp [D]; nlinarith only [Nat.zero_le (Y^4)]

open Classical in
/-- Among starts up to T, the number admitting a quotient-four witness is
    O((T+1)^(4/9)). This counts starts once even if several lengths work. -/
theorem count : ∃ C : ℕ, ∀ T : ℕ,
    (Finset.filter (fun n => ∃ k m, four k n m) (range (T+1))).card^9 ≤ C*(T+1)^4 := by
  classical
  obtain ⟨A,_,len⟩ := lengths
  obtain ⟨D,hd,step⟩ := slab_step Curve686.secants A len
  have graded (j : ℕ) : (starts ((2^j)^9)).card ≤ D*(2^j)^4 := by
    induction j with
    | zero =>
      have small : (starts 1).card ≤ 1 := by simpa [starts] using
        (card_filter_le (s:=range 1) (fun n => ∃ k m, four k n m))
      simpa using small.trans hd
    | succ j ih =>
      simp only [pow_succ' (2:ℕ) j]
      have a := step (2^j) (by positivity)
      calc
        _ ≤ (starts ((2^j)^9)).card + D*(2^j)^4 := a
        _ ≤ D*(2^j)^4+D*(2^j)^4 := Nat.add_le_add_right ih _
        _ ≤ D*(2*2^j)^4 := by rw [mul_pow]; norm_num; nlinarith only [Nat.zero_le (D*(2^j)^4)]
  refine ⟨D^9*2^36,fun T => ?_⟩
  have existsJ : ∃j:ℕ, T+1≤(2^j)^9 := by
    refine ⟨T+1,?_⟩
    exact (Nat.lt_two_pow_self (n:=T+1)).le.trans
      (le_self_pow₀ (Nat.one_le_pow _ _ (by decide : 0<2)) (by decide : 9≠0))
  let j := Nat.find existsJ
  have top : T+1≤(2^j)^9 := Nat.find_spec existsJ
  have mon : starts (T+1)⊆starts ((2^j)^9) := by
    intro n hn
    obtain ⟨hr,hf⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨mem_range.mpr ((mem_range.mp hr).trans_le top),hf⟩
  change (starts (T+1)).card^9 ≤ _
  apply (Nat.pow_le_pow_left ((card_le_card mon).trans (graded j)) 9).trans
  have cmp : (2^j)^36 ≤ 2^36*(T+1)^4 := by
    by_cases hz : j=0
    · simp only [hz,pow_zero,one_pow]
      exact Nat.mul_pos (by decide) (pow_pos (Nat.succ_pos T) _)
    · have pred := Nat.find_min existsJ (show j-1<j by omega)
      have lower : (2^(j-1))^9 ≤ T+1 := by omega
      have restore : 2^j=2*2^(j-1) := by conv_lhs => rw [show j=(j-1)+1 by omega,pow_succ']
      rw [restore,mul_pow]
      apply Nat.mul_le_mul_left
      simpa only [←pow_mul,Nat.mul_assoc] using Nat.pow_le_pow_left lower 4
  rw [mul_pow,←pow_mul]
  calc
    _ ≤ D^9*(2^36*(T+1)^4) := Nat.mul_le_mul_left _ cmp
    _ = _ := by ring

open Classical in
/-- The proportion of starting points up to T admitting any quotient-four
    representation tends to zero. -/
theorem density_zero : Tendsto (fun T : ℕ =>
    ((Finset.filter (fun n => ∃ k m, four k n m) (range (T+1))).card:ℝ)/((T:ℝ)+1))
    atTop (nhds 0) := by
  classical
  obtain ⟨C,hC⟩ := count
  let c := (C:ℝ)^((9:ℝ)⁻¹)
  have up (T : ℕ) : ((starts (T+1)).card:ℝ)/((T:ℝ)+1) ≤ c*((T:ℝ)+1)^(-(5/9:ℝ)) := by
    let x : ℝ := (T:ℝ)+1
    have xp : 0<x := by dsimp [x]; positivity
    have b : ((starts (T+1)).card:ℝ)^9 ≤ (C:ℝ)*x^4 := by
      dsimp [x]
      exact_mod_cast hC T
    have base := Real.rpow_le_rpow (by positivity) b (by positivity : (0:ℝ)≤(9:ℝ)⁻¹)
    have root9 : (((starts (T+1)).card:ℝ)^9)^((9:ℝ)⁻¹)=(starts (T+1)).card := by
      convert Real.pow_rpow_inv_natCast (x:=((starts (T+1)).card:ℝ)) (n:=9) (by positivity)
        (by decide) using 2; norm_num
    rw [root9,
      Real.mul_rpow (Nat.cast_nonneg C) (pow_nonneg xp.le _),
      ←Real.rpow_natCast_mul xp.le] at base
    change ((starts (T+1)).card:ℝ)/x ≤ c*x^(-(5/9:ℝ))
    rw [div_le_iff₀ xp,mul_assoc,←Real.rpow_add_one xp.ne']
    have expo : -(5/9:ℝ)+1=(4:ℕ)*(9:ℝ)⁻¹ := by norm_num
    rw [expo]
    exact base
  have go : Tendsto (fun T:ℕ => (T:ℝ)+1) atTop atTop := tendsto_natCast_atTop_atTop.atTop_add
    (tendsto_const_nhds (x:=(1:ℝ)))
  have decay := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<5/9)).comp go
  apply squeeze_zero (fun _ => by positivity) up
  simpa only [mul_zero,Function.comp_def] using decay.const_mul c

end OMA.CountStarts686

#print axioms OMA.CountStarts686.count
#print axioms OMA.CountStarts686.density_zero
