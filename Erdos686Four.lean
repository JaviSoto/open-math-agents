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
