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

/- Finite arithmetic inputs to a limiting prime-transport bound. -/
namespace OMA.Transport686
open Finset Nat OMA.Gap686

/-- Distinct prime powers above the block length project into its binomial coefficient. -/
theorem projection {T : Finset ℕ} {s l : ℕ} {e : ℕ → ℕ}
    (large : ∀ p ∈ T, p.Prime ∧ l < p)
    (loc : ∀ p ∈ T, ∃ i < l, p^(e p) ∣ s+1+i) :
    (∏ p ∈ T, p^(e p)) ∣ (s+l).choose l := by
  classical
  have one (p : ℕ) (hp : p ∈ T) : p ^ e p ∣ (s+l).choose l := by
    obtain ⟨i,hi,h⟩ := loc p hp
    have whole : p^e p ∣ block s l := h.trans (Finset.dvd_prod_of_mem _ (mem_range.mpr hi))
    rw [block_eq] at whole
    exact (((large p hp).1.coprime_factorial_of_lt (large p hp).2).pow_left _).dvd_of_dvd_mul_left whole
  induction T using Finset.induction_on with
  | empty => simp
  | @insert p T hp ih =>
    have within (q : ℕ) (hq : q∈T) : q∈insert p T := mem_insert_of_mem hq
    rw [prod_insert hp]
    apply Nat.Coprime.mul_dvd_of_dvd_of_dvd _ (one _ (mem_insert_self ..))
      (ih (fun q h => large q (within q h)) (fun q h => loc q (within q h)) (fun q h => one q (within q h)))
    apply Nat.coprime_prod_right_iff.mpr
    intro q hq
    exact ((Nat.coprime_primes (large p (mem_insert_self ..)).1 (large q (within q hq)).1).mpr
      (by rintro rfl; exact hp hq)).pow _ _

/-- The power assigned to a cell divides both its difference and sum coordinates. -/
theorem sum_diff {n d k p e : ℕ} (sep : k≤d) (hp : p.Prime) (big : k<p)
    (he : 0<e) (div : p^e ∣ block n k) (ratio : block n k ∣ block (n+d) k) :
    ∃ i < k, ∃ j < k, p^e ∣ n+1+i ∧ p^e ∣ n+d+1+j ∧
      p^e ∣ d+j-i ∧ p^e ∣ 2*n+d+2+i+j := by
  obtain ⟨i,hi,a⟩ := extract hp big he div
  obtain ⟨j,hj,b⟩ := extract hp big he (div.trans ratio)
  refine ⟨i,hi,j,hj,a,b,?_,?_⟩
  · convert Nat.dvd_sub b a using 1; omega
  · convert Nat.dvd_add a b using 1; omega

def largePart (B z : ℕ) : ℕ := ∏ p ∈ z.primeFactors with B < p, p^z.factorization p

/-- Loss on discarding primes at most B is at most (s+l)^π(B), uniformly in subinterval length. -/
theorem interval {s l B : ℕ} (pos : 0 < s+l) :
    largePart B ((s+l).choose l) ≤ (s+l).choose l ∧
    (s+l).choose l ≤ (s+l)^B.primeCounting * largePart B ((s+l).choose l) := by
  let z := (s+l).choose l
  have nz : 0<z := Nat.choose_pos (by omega)
  let small := z.primeFactors.filter fun p => p ≤ B
  have split : (∏ p ∈ small, p^z.factorization p)*largePart B z = z := by
    rw [largePart]
    dsimp [small]
    simpa only [not_le] using ((Finset.prod_filter_mul_prod_filter_not z.primeFactors
      (fun p => p ≤ B) (fun p => p^z.factorization p)).trans (Nat.prod_primeFactors_pow_factorization nz.ne').symm)
  have ps : small ⊆ B.primesLE := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨(mem_filter.mp hp).2,Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1⟩
  have bound : (∏ p ∈ small, p^z.factorization p) ≤ (s+l)^B.primeCounting := by
    calc
      _ ≤ ∏ _p ∈ small, (s+l) := by
        apply prod_le_prod'
        intro p hp
        have prime := (Nat.mem_primesLE.mp (ps hp)).2
        exact (Nat.pow_le_pow_right prime.pos Nat.factorization_choose_le_log).trans
          (Nat.pow_log_le_self p pos.ne')
      _ = (s+l)^small.card := by simp
      _ ≤ _ := Nat.pow_le_pow_right pos (by simpa [Nat.primesLE_card_eq_primeCounting] using card_le_card ps)
  change largePart B z ≤ z ∧ z ≤ _
  constructor
  · apply Nat.le_of_dvd nz
    exact (dvd_mul_left (largePart B z) (∏ p ∈ small, p^z.factorization p)).trans (dvd_of_eq split)
  · calc
      z = _ := split.symm
      _ ≤ _ := Nat.mul_le_mul_right _ bound

end OMA.Transport686

/- Finite second-moment bounds for matching prime powers. -/
namespace OMA.TransportVariance686
open Finset Set MeasureTheory
open scoped Interval

private noncomputable def layer (w r : ℝ) : ℝ → ℝ :=
  (Iic r).indicator (fun t => (2*w)*t)

private theorem layer_integrable (w r c : ℝ) :
    IntervalIntegrable (layer w r) volume 0 c := by
  apply intervalIntegrable_iff.mpr
  exact ((continuous_const.mul continuous_id).intervalIntegrable 0 c).def'.indicator measurableSet_Iic

private theorem layer_value (w r c : ℝ) (hr : 0≤r) (hc : 0≤c) :
    (∫ t in 0..c, layer w (min c r) t) = w*(min c r)^2 := by
  have h : min c r ∈ Icc (0:ℝ) c := ⟨le_min hc hr,min_le_left ..⟩
  unfold layer
  rw [show Iic (min c r) = {t | t ≤ min c r} from rfl,
    intervalIntegral.integral_indicator h,intervalIntegral.integral_const_mul,integral_id]
  ring

private theorem layer_sum {ι : Type*} (S : Finset ι) (w z : ι → ℝ)
    {t c : ℝ} (ht : t≤c) :
    (∑ i ∈ S, layer (w i) (min c |z i|) t) =
    (2*t)*(∑ i ∈ S, if |z i| < t then 0 else w i) := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : |z i| < t
  · have hn : ¬ t ≤ min c |z i| := fun u => h.not_ge (u.trans (min_le_right ..))
    simp [layer,hn,h]
  · have hy : t ≤ min c |z i| := le_min ht (le_of_not_gt h)
    simp [layer,hy,h]; ring

private theorem part_sum {ι : Type*} (S : Finset ι) (w z : ι → ℝ) (t : ℝ) :
    (∑ i ∈ S, if |z i| < t then w i else 0) +
    (∑ i ∈ S, if |z i| < t then 0 else w i) = ∑ i ∈ S, w i := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  split <;> simp_all

private theorem layers_integrable {ι : Type*} (S : Finset ι) (w z : ι → ℝ) (c : ℝ) :
    IntervalIntegrable (fun t => ∑ i ∈ S, layer (w i) (min c |z i|) t) volume 0 c := by
  let f (i : ι) := layer (w i) (min c |z i|)
  change IntervalIntegrable (fun t => ∑ i ∈ S, f i t) volume 0 c
  rw [show (fun t => ∑ i ∈ S, f i t) = ∑ i ∈ S, f i by ext; simp]
  exact IntervalIntegrable.sum S (fun i _ => layer_integrable ..)

/-- A finite probability distribution with at most 2Bt+E mass at distance
less than t from z=0 has second moment at least (1−E)^3/(12B²). -/
theorem second_moment {ι : Type*} {S : Finset ι} {w z : ι → ℝ} {B E : ℝ}
    (hw : ∀ i ∈ S, 0≤w i) (total : ∑ i ∈ S, w i = 1) (hB : 0<B) (hE : E≤1)
    (small : ∀ t : ℝ, 0 ≤ t → (∑ i ∈ S, if |z i| < t then w i else 0) ≤ 2*B*t+E) :
    (1-E)^3/(12*B^2) ≤ ∑ i ∈ S, w i*(z i)^2 := by
  classical
  let c := (1-E)/(2*B)
  have hc : 0≤c := div_nonneg (sub_nonneg.mpr hE) (by positivity)
  let f (i : ι) := layer (w i) (min c |z i|)
  have fi (i : ι) : IntervalIntegrable (f i) volume 0 c := layer_integrable ..
  have gl : Continuous (fun t : ℝ => (2*(1-E))*t - (4*B)*t^2) := by fun_prop
  have lower (t : ℝ) (ht : t ∈ Icc 0 c) :
      (2*(1-E))*t - (4*B)*t^2 ≤ ∑ i ∈ S, f i t := by
    have tail : 1-(2*B*t+E) ≤ ∑ i ∈ S, if |z i| < t then 0 else w i := by
      linarith [small t ht.1,(part_sum S w z t).trans total]
    rw [show (∑ i ∈ S, f i t) = _ from layer_sum S w z ht.2]
    nlinarith only [mul_le_mul_of_nonneg_left tail (by linarith [ht.1] : 0 ≤ 2*t)]
  have fsum : IntervalIntegrable (fun t => ∑ i ∈ S, f i t) volume 0 c := layers_integrable S w z c
  have lowInt := intervalIntegral.integral_mono_on hc (gl.intervalIntegrable 0 c) fsum lower
  rw [intervalIntegral.integral_finsetSum (fun i _ => fi i)] at lowInt
  have lit : (∫ t in 0..c, (2*(1-E))*t-(4*B)*t^2) = (1-E)^3/(12*B^2) := by
    rw [intervalIntegral.integral_sub,intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,integral_id,integral_pow]
    · dsimp [c]; field_simp; ring
    all_goals exact (by fun_prop : Continuous _).intervalIntegrable _ _
  rw [lit] at lowInt
  apply lowInt.trans
  apply Finset.sum_le_sum
  intro i hi
  change (∫ t in 0..c, layer (w i) (min c |z i|) t) ≤ _
  rw [layer_value _ _ _ (abs_nonneg _) hc]
  apply mul_le_mul_of_nonneg_left _ (hw i hi)
  calc
    _ ≤ |z i|^2 := by gcongr; exact min_le_right ..
    _ = _ := sq_abs _

/-- An approximately uniform coordinate on [-1/2,1/2] has almost the same
second moment as the uniform distribution. -/
theorem marginal {ι : Type*} {S : Finset ι} {w z : ι → ℝ} {E : ℝ}
    (total : ∑ i ∈ S, w i = 1) (supp : ∀ i ∈ S, |z i| ≤ 1/2)
    (near : ∀ t ∈ Icc (0:ℝ) (1/2), 2*t-E ≤ ∑ i ∈ S, if |z i| < t then w i else 0) :
    (∑ i ∈ S, w i*(z i)^2) ≤ 1/12+E/4 := by
  let c : ℝ := 1/2
  have hc : 0≤c := by norm_num [c]
  let f (i : ι) := layer (w i) (min c |z i|)
  have fi (i : ι) : IntervalIntegrable (f i) volume 0 c := layer_integrable ..
  have gl : Continuous (fun t : ℝ => (2*(1+E))*t - 4*t^2) := by fun_prop
  have upper (t : ℝ) (ht : t ∈ Icc 0 c) :
      (∑ i ∈ S, f i t) ≤ (2*(1+E))*t - 4*t^2 := by
    have tail : (∑ i ∈ S, if |z i| < t then 0 else w i) ≤ 1-2*t+E := by
      linarith [near t ht,(part_sum S w z t).trans total]
    rw [show (∑ i ∈ S, f i t) = _ from layer_sum S w z ht.2]
    nlinarith only [mul_le_mul_of_nonneg_left tail (by linarith [ht.1] : 0 ≤ 2*t)]
  have highInt := intervalIntegral.integral_mono_on hc (layers_integrable S w z c)
    (gl.intervalIntegrable 0 c) upper
  change (∫ t in 0..c, ∑ i ∈ S, f i t) ≤ _ at highInt
  rw [intervalIntegral.integral_finsetSum (fun i _ => fi i)] at highInt
  have lit : (∫ t in 0..c, (2*(1+E))*t-4*t^2) = 1/12+E/4 := by
    rw [intervalIntegral.integral_sub,intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,integral_id,integral_pow]
    · dsimp [c]; ring
    all_goals exact (by fun_prop : Continuous _).intervalIntegrable _ _
  rw [lit] at highInt
  convert highInt using 1
  apply Finset.sum_congr rfl
  intro i hi
  symm
  change (∫ t in 0..c, layer (w i) (min c |z i|) t) = _
  rw [layer_value _ _ _ (abs_nonneg _) hc, min_eq_right (supp i hi),sq_abs]

/-- Quantitative four-projection inequality. x and y are the centered
coordinates; only masses in intervals about the origin are required. -/
theorem four_projections {ι : Type*} {S : Finset ι} {w x y : ι → ℝ} {B E : ℝ}
    (hw : ∀ i ∈ S, 0 ≤ w i) (total : ∑ i ∈ S, w i = 1)
    (hB : 0 < B) (hE : E ≤ 1)
    (hx : ∀ i ∈ S, |x i| ≤ 1/2) (hy : ∀ i ∈ S, |y i| ≤ 1/2)
    (mx : ∀ t ∈ Icc (0:ℝ) (1/2), 2*t-E ≤ ∑ i ∈ S, if |x i| < t then w i else 0)
    (my : ∀ t ∈ Icc (0:ℝ) (1/2), 2*t-E ≤ ∑ i ∈ S, if |y i| < t then w i else 0)
    (dif : ∀ t : ℝ, 0 ≤ t → (∑ i ∈ S, if |y i-x i| < t then w i else 0) ≤ 2*B*t+E)
    (add : ∀ t : ℝ, 0 ≤ t → (∑ i ∈ S, if |x i+y i| < t then w i else 0) ≤ 2*t+E) :
    (1-E)^3*(1+B^2) ≤ (4+12*E)*B^2 := by
  have lowH := second_moment (z:=fun i => y i-x i) hw total hB hE dif
  have lowS := second_moment (z:=fun i => x i+y i) (B:=1) hw total zero_lt_one hE (by simpa using add)
  have upX := marginal total hx mx
  have upY := marginal total hy my
  have ident : (∑ i ∈ S, w i*(y i-x i)^2)+(∑ i ∈ S, w i*(x i+y i)^2) =
      2*(∑ i ∈ S, w i*(x i)^2)+2*(∑ i ∈ S, w i*(y i)^2) := by
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have both : (1-E)^3/(12*B^2)+(1-E)^3/12 ≤ 1/3+E := by
    norm_num at lowS
    linarith
  field_simp [ne_of_gt hB] at both
  nlinarith only [both]

end OMA.TransportVariance686

/- Large shared divisors in two short intervals. Reduced slopes have bounded
denominator; on each ray, distinct lattice points have separated abscissae. -/
namespace OMA.FareyMass686
open Finset

private lemma pack {α : Type*} (S : Finset α) (f : α→ℝ) (l h : ℝ) (lh : l≤h)
    (bounds : ∀ x∈S, l≤f x ∧ f x≤h)
    (sep : ∀ x∈S, ∀ y∈S, x≠y → 1≤|f x-f y|) : (S.card:ℝ) ≤ 1+(h-l) := by
  let idx (x : α) := ⌊f x-l⌋₊
  have maps : Set.MapsTo idx (S:Set α) (range (⌊h-l⌋₊+1) : Finset ℕ) := fun x hx =>
    mem_range.mpr (Nat.lt_succ_of_le (Nat.floor_mono (sub_le_sub_right (bounds x hx).2 l)))
  have inj : Set.InjOn idx (S:Set α) := by
    intro x hx y hy same
    by_contra ne
    have eq : ((⌊f x-l⌋₊:ℕ):ℝ)=⌊f y-l⌋₊ := by exact_mod_cast same
    have xl := Nat.floor_le (sub_nonneg.mpr (bounds x hx).1)
    have yl := Nat.floor_le (sub_nonneg.mpr (bounds y hy).1)
    have small : |f x-f y|<1 := abs_lt.mpr ⟨by linarith [Nat.lt_floor_add_one (f y-l)],
      by linarith [Nat.lt_floor_add_one (f x-l)]⟩
    exact (not_lt_of_ge (sep x hx y hy ne)) small
  have hc := Finset.card_le_card_of_injOn idx maps inj
  rw [card_range] at hc
  have hc' : (S.card:ℝ) ≤ ⌊h-l⌋₊+1 := by exact_mod_cast hc
  linarith [Nat.floor_le (sub_nonneg.mpr lh)]

private lemma unit_gap {a b : ℤ} (ne : a≠b) : (1:ℝ)≤|(a:ℝ)-(b:ℝ)| := by
  have h : 1≤|a-b| := by
    have n := abs_pos.mpr (sub_ne_zero.mpr ne)
    omega
  exact_mod_cast h

private lemma farey {a b c d : ℕ} {Q : ℝ} (bp : 0<b) (dp : 0<d)
    (bq : (b:ℝ)≤Q) (dq : (d:ℝ)≤Q) (ne : (a:ℝ)/b≠(c:ℝ)/d) :
    1≤Q^2*|(a:ℝ)/b-(c:ℝ)/d| := by
  have bP : (0:ℝ)<b := by exact_mod_cast bp
  have dP : (0:ℝ)<d := by exact_mod_cast dp
  have cross : (a:ℤ)*d≠(c:ℤ)*b := by
    intro bad
    apply ne
    apply (div_eq_div_iff bP.ne' dP.ne').mpr
    exact_mod_cast bad
  have sep : (1:ℝ)≤|(a:ℝ)*d-c*b| := by exact_mod_cast unit_gap cross
  have id : ((b:ℝ)*d)*((a:ℝ)/b-c/d)=a*d-c*b := by field_simp
  have absid := congrArg abs id
  rw [abs_mul,abs_of_pos (mul_pos bP dP)] at absid
  rw [←absid] at sep
  apply sep.trans
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  rw [sq]
  exact mul_le_mul bq dq dP.le (bP.le.trans bq)

/-- Assume the shorter ordinate center D and the abscissa center N satisfy
the scale relations for a quotient-four solution. This bound holds for *all*
lattice pairs, without assuming the consecutive product equation. -/
theorem pairs (S : Finset (ℕ×ℕ)) (N D K B : ℝ) (kp : 0<K) (bp : 0<B)
    (sep : 2*K≤D) (dn : D≤N) (scale : K*D≤6*N)
    (box : ∀ z∈S, N≤z.1 ∧ (z.1:ℝ)≤N+K ∧ D-K≤z.2 ∧ (z.2:ℝ)≤D+K)
    (large : ∀ z∈S, B ≤ (Nat.gcd z.1 z.2:ℝ)) :
    (S.card:ℝ)≤10*(1+12*N*K/B^2) := by
  classical
  let ratio (z : ℕ×ℕ) : ℝ := z.1/z.2
  let Q := (D+K)/B
  let l := N/(D+K)
  let h := (N+K)/(D-K)
  have dp : 0<D := by linarith
  have np : 0<N := by linarith
  have lo : 0<D-K := by linarith
  have plus : 0<D+K := by linarith
  have lr : l≤h := div_le_div₀ (by positivity : 0≤N+K) (by linarith) lo (by linarith)
  have rg (z) (hz : z∈S) : l≤ratio z ∧ ratio z≤h := by
    obtain ⟨x₁,x₂,y₁,y₂⟩ := box z hz
    exact ⟨div_le_div₀ (Nat.cast_nonneg _) x₁ (lo.trans_le y₁) y₂,
      div_le_div₀ (by positivity) x₂ lo y₁⟩
  have rep (z) (hz : z∈S) : ∃ a b : ℕ, 0<b ∧ (b:ℝ)≤Q ∧ ratio z=(a:ℝ)/b := by
    let g := Nat.gcd z.1 z.2
    obtain ⟨a,ha⟩ := Nat.gcd_dvd_left z.1 z.2
    obtain ⟨b,hb⟩ := Nat.gcd_dvd_right z.1 z.2
    change z.1=g*a at ha
    change z.2=g*b at hb
    have gp : 0<(g:ℝ) := bp.trans_le (large z hz)
    have yp : (0:ℝ)<z.2 := lo.trans_le (box z hz).2.2.1
    have ha' : (z.1:ℝ)=g*a := by exact_mod_cast ha
    have hb' : (z.2:ℝ)=g*b := by exact_mod_cast hb
    have bl : 0<(b:ℝ) := pos_of_mul_pos_right (hb' ▸ yp) gp.le
    refine ⟨a,b,by exact_mod_cast bl,(le_div_iff₀ bp).mpr ?_,?_⟩
    · nlinarith [mul_le_mul_of_nonneg_right (large z hz) bl.le,(box z hz).2.2.2]
    · dsimp only [ratio]; rw [ha',hb']; field_simp
  have sp := pack (S.image ratio) (fun t=>Q^2*t) (Q^2*l) (Q^2*h)
    (mul_le_mul_of_nonneg_left lr (sq_nonneg _)) (fun t ht => by
      obtain ⟨z,hz,rfl⟩ := mem_image.mp ht
      exact ⟨mul_le_mul_of_nonneg_left (rg z hz).1 (sq_nonneg _),
        mul_le_mul_of_nonneg_left (rg z hz).2 (sq_nonneg _)⟩) (fun t ht v hv ne => by
        obtain ⟨p,hp,rfl⟩ := mem_image.mp ht
        obtain ⟨q,hq,rfl⟩ := mem_image.mp hv
        obtain ⟨a,b,hb,bq,eq⟩ := rep p hp
        obtain ⟨c,d,hd,dq,eq'⟩ := rep q hq
        rw [eq,eq',←mul_sub,abs_mul,abs_of_nonneg (sq_nonneg _)]
        exact farey hb hd bq dq (eq ▸ eq' ▸ ne))
  have width : Q^2*h-Q^2*l≤12*N*K/B^2 := by
    have h1 : 2*N+D+K≤4*N := by linarith
    have h2 : D+K≤3*(D-K) := by linarith
    have eq : Q^2*h-Q^2*l = K*(2*N+D+K)*(D+K)/(D-K)/B^2 := by
      dsimp [Q,h,l]; field_simp; ring
    rw [eq]
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    apply (div_le_iff₀ lo).mpr
    nlinarith only [mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 plus.le (by positivity)) kp.le]
  have smallF (t : ℝ) (ht : t∈S.image ratio) : (S.filter fun z => ratio z=t).card≤10 := by
    have rt := mem_image.mp ht
    obtain ⟨z,hz,et⟩ := rt
    have lt' : l≤t := et ▸ (rg z hz).1
    have kt : K≤9*t := by
      have a : K≤9*l := by
        dsimp [l]; rw [←mul_div_assoc]
        apply (le_div_iff₀ plus).mpr
        nlinarith [mul_nonneg (show 0≤D-2*K by linarith) kp.le]
      linarith
    have tp : 0<t := by linarith
    let pts := S.filter fun z => ratio z=t
    have xy (v : ℕ×ℕ) (hv : v∈pts) : (v.1:ℝ)=t*v.2 := by
      obtain ⟨m,eq⟩ := mem_filter.mp hv
      exact (div_eq_iff (lo.trans_le (box v m).2.2.1).ne').mp eq
    have b := pack pts (fun v=>9*(v.1:ℝ)/K) (9*N/K) (9*(N+K)/K)
      (by gcongr; linarith) (fun v hv => by
        obtain ⟨xx,xx',_⟩ := box v (mem_filter.mp hv).1
        exact ⟨by gcongr,by gcongr⟩) (fun p hp q hq n => by
          have py := xy p hp
          have qy := xy q hq
          have diff : p.2≠q.2 := by
            intro same
            apply n
            apply Prod.ext _ same
            rw [same] at py
            exact_mod_cast py.trans qy.symm
          have se : (1:ℝ)≤|(p.2:ℝ)-q.2| := by exact_mod_cast unit_gap (by exact_mod_cast diff : (p.2:ℤ)≠q.2)
          rw [py,qy,←sub_div,←mul_sub,←mul_sub,abs_div,abs_mul,abs_mul,
            abs_of_pos kp,abs_of_pos tp,abs_of_pos (by norm_num : (0:ℝ)<9)]
          apply (le_div_iff₀ kp).mpr
          nlinarith [mul_le_mul_of_nonneg_left se tp.le])
    have ident : 9*(N+K)/K-9*N/K=9 := by field_simp; ring
    rw [ident] at b
    change pts.card≤10
    exact_mod_cast (show (pts.card:ℝ)≤10 by linarith)
  have tot : (S.card:ℝ)≤10*(S.image ratio).card := by exact_mod_cast card_le_mul_card_image S 10 smallF
  linarith

end OMA.FareyMass686

/- An integral six-point conic determinant vanishes when its transformed
columns, including the quadratic remainder, have sufficiently small product. -/
namespace OMA.ConicStrip686
open Matrix Finset

def conic {R : Type*} [CommRing R] (y x : Fin 6 → R) : Matrix (Fin 6) (Fin 6) R :=
  of fun i => ![1,y i,x i,y i^2,y i*x i,x i^2]

private def bump (M : Matrix (Fin 6) (Fin 6) ℝ) (i j : Fin 6) (c : ℝ) :=
  M.updateCol i fun k => M k i + c * M k j

private lemma bump_det (M : Matrix (Fin 6) (Fin 6) ℝ) (i j : Fin 6) (h : i≠j) (c : ℝ) :
    (bump M i j c).det = M.det := M.det_updateCol_add_smul_self h c

private lemma size (M : Matrix (Fin 6) (Fin 6) ℝ) (a : Fin 6→ℝ)
    (h : ∀ i j, |M i j| ≤ a j) : |M.det| ≤ 720*∏ j, a j := by
  rw [det_apply']
  calc
    _ ≤ ∑ σ : Equiv.Perm (Fin 6), |((Equiv.Perm.sign σ:ℤ):ℝ) * ∏ i, M (σ i) i| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin 6), ∏ j, a j := by
      apply sum_le_sum
      intro σ _
      rw [abs_mul,←Int.cast_abs,Equiv.Perm.sign_abs,Int.cast_one,one_mul,Finset.abs_prod]
      exact prod_le_prod (fun _ _ => abs_nonneg _) fun j _ => h (σ j) j
    _ = _ := by simp [Fintype.card_perm]; norm_num [Nat.factorial]

theorem vanish (y x : Fin 6 → ℤ) (a c d D Z R : ℝ)
    (hy : ∀ i, |(y i:ℝ)| ≤ D) (hz : ∀ i, |(x i:ℝ)-a*(y i:ℝ)| ≤ Z)
    (rest : ∀ i, |(y i:ℝ)*((x i:ℝ)-a*(y i:ℝ))-c-d*((x i:ℝ)-a*(y i:ℝ))^2| ≤ R)
    (budget : 720*D^3*Z^3*R < 1) : (conic y x).det = 0 := by
  let Y := fun i => (y i:ℝ)
  let X := fun i => (x i:ℝ)
  let z := fun i => X i-a*Y i
  let M := conic Y X
  let N := bump (bump (bump (bump (bump (bump M 5 4 (-2*a)) 5 3 (a^2))
    4 3 (-a)) 2 1 (-a)) 4 0 (-c)) 4 5 (-d)
  have same : N.det=M.det := by
    dsimp only [N]
    repeat rw [bump_det _ _ _ (by decide)]
  have row (i j : Fin 6) : N i j=(![1,Y i,z i,Y i^2,Y i*z i-c-d*z i^2,z i^2]:Fin 6→ℝ) j := by
    fin_cases j <;> simp [N,bump,M,conic,z,Matrix.updateCol,Function.update] <;> ring
  let upper : Fin 6→ℝ := ![1,D,Z,D^2,R,Z^2]
  have y2 (i : Fin 6) : |Y i^2|≤D^2 := by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hy i) 2
  have z2 (i : Fin 6) : |z i^2|≤Z^2 := by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hz i) 2
  have hb (i j : Fin 6) : |N i j|≤upper j := by
    rw [row]
    fin_cases j
    · simp [upper]
    · exact hy i
    · exact hz i
    · exact y2 i
    · exact rest i
    · exact z2 i
  have upperprod : ∏ j, upper j = D^3*Z^3*R := by simp [upper,Fin.prod_univ_succ]; ring
  have v := size N upper hb
  rw [upperprod,same] at v
  have cast : ((conic y x).det:ℝ)=M.det := by
    rw [Int.cast_det]
    congr 1
    ext i j
    fin_cases j <;> simp [M,X,Y,conic]
  have small : |((conic y x).det:ℝ)|<1 := by rw [cast]; linarith
  rw [←Int.cast_abs] at small
  have hi : |(conic y x).det| < 1 := by exact_mod_cast small
  exact abs_eq_zero.mp (le_antisymm (by omega) (abs_nonneg _))

end OMA.ConicStrip686

/- A zero-counting criterion for a function basis on a real interval.
Divide by a nonvanishing first function, differentiate, and repeat Rolle. -/
namespace OMA.RolleBasis686
open Finset Set

def Basis (lo hi : ℝ) : (n : ℕ) → (Fin n → ℝ → ℝ) → Prop
  | 0, _ => True
  | n+1, f => (∀ x ∈ Ioo lo hi, f 0 x ≠ 0) ∧ ∃ g : Fin n → ℝ → ℝ,
      (∀ j x, x ∈ Ioo lo hi → HasDerivAt (fun y => f j.succ y/f 0 y) (g j x) x) ∧
      Basis lo hi n g

private lemma coefficients {lo hi : ℝ} {n : ℕ} (f : Fin n → ℝ → ℝ)
    (ok : Basis lo hi n f) (t : Fin n→ℝ) (inc : StrictMono t)
    (mem : ∀ i, t i∈Ioo lo hi) (c : Fin n → ℝ)
    (zero : ∀ i, ∑ j, c j*f j (t i) = 0) : ∀ j, c j=0 := by
  induction n with
  | zero => exact fun j => j.elim0
  | succ n ih =>
    obtain ⟨hn,g,hg,bg⟩ := ok
    let F (x : ℝ) := c 0 + ∑ j : Fin n, c j.succ*(f j.succ x/f 0 x)
    let G (x : ℝ) := ∑ j : Fin n, c j.succ*g j x
    have fd (x : ℝ) (hx : x∈Ioo lo hi) : HasDerivAt F (G x) x := by
      apply HasDerivAt.const_add
      exact HasDerivAt.fun_sum (fun j _ => (hg j x hx).const_mul (c j.succ))
    have fz (i : Fin (n+1)) : F (t i)=0 := by
      have eq := zero i
      rw [Fin.sum_univ_succ] at eq
      suffices w : F (t i)*f 0 (t i)=0 from (mul_eq_zero.mp w).resolve_right (hn _ (mem i))
      dsimp [F]
      rw [add_mul,sum_mul]
      convert! eq using 2
      apply sum_congr rfl
      intro j _
      field_simp [hn _ (mem i)]
    have gaps (i : Fin n) : ∃ z ∈ Ioo (t i.castSucc) (t i.succ), G z=0 := by
      have sub : Icc (t i.castSucc) (t i.succ) ⊆ Ioo lo hi := by
        intro x hx
        exact ⟨(mem _).1.trans_le hx.1,hx.2.trans_lt (mem _).2⟩
      exact exists_hasDerivAt_eq_zero (inc (Fin.castSucc_lt_succ (i:=i)))
        (fun x hx => (fd x (sub hx)).continuousAt.continuousWithinAt)
        ((fz _).trans (fz _).symm) (fun x hx => fd x (sub ⟨hx.1.le,hx.2.le⟩))
    choose u iu gu using gaps
    have iu' (i : Fin n) : u i∈Ioo lo hi := ⟨(mem _).1.trans (iu i).1,
      (iu i).2.trans (mem _).2⟩
    have mon : StrictMono u := by
      intro i j ij
      have ij' : i.succ ≤ j.castSucc := by exact ij
      exact (iu i).2.trans_le ((inc.monotone ij').trans (iu j).1.le)
    have tail := ih g bg u mon iu' (fun j => c j.succ) gu
    have eq := zero 0
    rw [Fin.sum_univ_succ] at eq
    simp only [tail,zero_mul,sum_const_zero,add_zero] at eq
    exact Fin.cases ((mul_eq_zero.mp eq).resolve_right (hn _ (mem 0))) tail

/-- The evaluation matrix of such a basis at any strictly increasing
sequence of sample points in the interval is nonsingular. -/
theorem determinant {lo hi : ℝ} {n : ℕ} (f : Fin n → ℝ → ℝ)
    (ok : Basis lo hi n f) (t : Fin n→ℝ) (inc : StrictMono t)
    (mem : ∀ i, t i∈Ioo lo hi) : (Matrix.of fun i j => f j (t i)).det≠0 := by
  intro hz
  obtain ⟨v,nz,zeros⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hz
  apply nz
  funext j
  apply coefficients f ok t inc mem v _ j
  intro i
  simpa [Matrix.mulVec, dotProduct,mul_comm] using congrFun zeros i

end OMA.RolleBasis686

/- Uniform Chebyshev property near zero for a parameter-dependent basis
whose distinct leading powers have jointly convergent nonvanishing factors. -/
namespace OMA.JetRolle686
open Filter Set
open scoped Topology
variable {P : Type*} (l : Filter P)

abbrev Fam (P : Type*) := P → ℝ → ℝ
private abbrev near := l ×ˢ 𝓝 (0:ℝ)

/-- Uniform finite jet: the values and the first n derivatives converge as the
parameter tends along l and the real argument tends independently to zero. -/
def Jet : ℕ → Fam P → ℝ → Prop
  | 0, u, c => Tendsto (fun z : P×ℝ => u z.1 z.2) (near l) (𝓝 c)
  | n+1, u, c => Tendsto (fun z : P×ℝ => u z.1 z.2) (near l) (𝓝 c) ∧
    ∃ v : Fam P, ∃ d : ℝ, (∀ᶠ z : P×ℝ in near l, HasDerivAt (u z.1) (v z.1 z.2) z.2) ∧
      Jet n v d

variable {l} {n : ℕ} {u v : Fam P} {c d : ℝ}

lemma Jet.limit (hu : Jet l n u c) : Tendsto (fun z : P×ℝ => u z.1 z.2) (near l) (𝓝 c) := by
  cases n with
  | zero => exact hu
  | succ _ => exact hu.1

lemma Jet.lower (hu : Jet l (n+1) u c) : Jet l n u c := by
  induction n generalizing u c with
  | zero => exact hu.1
  | succ n ih =>
    obtain ⟨h,v,d,hv,hd⟩ := hu
    exact ⟨h,v,d,hv,ih hd⟩

lemma Jet.const (n : ℕ) (c : ℝ) : Jet l n (fun _ _ => c) c := by
  induction n generalizing c with
  | zero => exact tendsto_const_nhds
  | succ n ih => exact ⟨tendsto_const_nhds,fun _ _ => 0,0,
      Eventually.of_forall (fun z => hasDerivAt_const z.2 c),ih 0⟩

lemma Jet.id (n : ℕ) : Jet l n (fun _ x => x) 0 := by
  cases n with
  | zero => exact tendsto_snd
  | succ n => exact ⟨tendsto_snd,fun _ _ => 1,1,
      Eventually.of_forall (fun z => hasDerivAt_id z.2),.const n 1⟩

lemma Jet.add (hu : Jet l n u c) (hv : Jet l n v d) :
    Jet l n (fun p x => u p x+v p x) (c+d) := by
  induction n generalizing u v c d with
  | zero => exact hu.limit.add hv.limit
  | succ n ih =>
    obtain ⟨lu,u',c',du,ju⟩ := hu
    obtain ⟨lv,v',d',dv,jv⟩ := hv
    refine ⟨lu.add lv,_,_,?_,ih ju jv⟩
    filter_upwards [du,dv] with z a b using a.add b

lemma Jet.neg (hu : Jet l n u c) : Jet l n (fun p x => -u p x) (-c) := by
  induction n generalizing u c with
  | zero => exact hu.limit.neg
  | succ n ih =>
    obtain ⟨lu,u',c',du,ju⟩ := hu
    exact ⟨lu.neg,_,_,du.mono (fun _ a => a.neg),ih ju⟩

lemma Jet.mul (hu : Jet l n u c) (hv : Jet l n v d) :
    Jet l n (fun p x => u p x*v p x) (c*d) := by
  induction n generalizing u v c d with
  | zero => exact hu.limit.mul hv.limit
  | succ n ih =>
    obtain ⟨_,u',c',du,ju⟩ := hu
    obtain ⟨_,v',d',dv,jv⟩ := hv
    rename_i lu lv
    have lowU := (show Jet l (n+1) u c from ⟨lu,u',c',du,ju⟩).lower
    have lowV := (show Jet l (n+1) v d from ⟨lv,v',d',dv,jv⟩).lower
    refine ⟨lu.mul lv,_,_,?_,(ih ju lowV).add (ih lowU jv)⟩
    filter_upwards [du,dv] with z a b using a.mul b

lemma Jet.div (hu : Jet l n u c) (hv : Jet l n v d) (hd : d≠0) :
    Jet l n (fun p x => u p x/v p x) (c/d) := by
  induction n generalizing u v c d with
  | zero => exact hu.limit.div hv.limit hd
  | succ n ih =>
    obtain ⟨lu,u',c',du,ju⟩ := hu
    obtain ⟨lv,v',d',dv,jv⟩ := hv
    have lowU := (show Jet l (n+1) u c from ⟨lu,u',c',du,ju⟩).lower
    have lowV := (show Jet l (n+1) v d from ⟨lv,v',d',dv,jv⟩).lower
    refine ⟨lu.div lv hd,_,_,?_,ih ((ju.mul lowV).add (lowU.mul jv).neg)
       (lowV.mul lowV) (mul_ne_zero hd hd)⟩
    filter_upwards [du,dv,lv.eventually_ne hd] with z a b nz
    simpa [sq,sub_eq_add_neg] using a.fun_div b nz

private lemma interval {A : P → ℝ → Prop} (h : ∀ᶠ z : P×ℝ in near l, A z.1 z.2) :
    ∃ ε>0, ∀ᶠ p in l, ∀ x∈Ioo 0 ε, A p x := by
  obtain ⟨q,hq,ε,hε,ok⟩ := Metric.eventually_prod_nhds_iff.mp h
  exact ⟨ε,hε,hq.mono fun _ hp x hx => ok hp (by simpa [Real.dist_eq,abs_of_pos hx.1] using hx.2)⟩

private lemma restrict {a b : ℝ} {f : Fin n → ℝ → ℝ} (h : OMA.RolleBasis686.Basis 0 b n f)
    (hab : a≤b) : OMA.RolleBasis686.Basis 0 a n f := by
  induction n with
  | zero => trivial
  | succ n ih =>
    obtain ⟨nz,g,dg,reg⟩ := h
    refine ⟨fun x hx => nz x ⟨hx.1,hx.2.trans_le hab⟩,g,fun j x hx =>
      dg j x ⟨hx.1,hx.2.trans_le hab⟩,ih reg⟩

/-- A sequence of distinct monomial orders, times factors with uniform jets
and nonzero leading coefficients, is a Chebyshev basis on one fixed interval. -/
theorem basis {n : ℕ} (h : Fin n → ℕ) (inc : StrictMono h)
    (u : Fin n → Fam P) (c : Fin n→ℝ) (nz : ∀ j, c j≠0)
    (jet : ∀ j, Jet l n (u j) (c j)) : ∃ ε>0, ∀ᶠ p in l,
      OMA.RolleBasis686.Basis 0 ε n (fun j t => t^(h j)*u j p t) := by
  induction n with
  | zero => exact ⟨1,by norm_num,Eventually.of_forall fun _ => trivial⟩
  | succ n ih =>
    let m (j : Fin n) := h j.succ-h 0-1
    have ex (j : Fin n) : h j.succ=h 0+(m j+1) := by
      have := inc (Fin.succ_pos j)
      dsimp [m]; omega
    have mi : StrictMono m := by
      intro i j ij
      have := inc (Fin.strictMono_succ ij)
      have e := ex i
      have e' := ex j
      omega
    let v (j : Fin n) (p : P) (t : ℝ) := u j.succ p t/u 0 p t
    have vj (j : Fin n) : Jet l (n+1) (v j) (c j.succ/c 0) :=
      (jet j.succ).div (jet 0) (nz 0)
    have vj' := vj
    choose _ v' d' dv jv using vj'
    let w (j : Fin n) (p : P) (t : ℝ) := (m j+1:ℕ)*v j p t+t*v' j p t
    let e (j : Fin n) : ℝ := (m j+1:ℕ)*(c j.succ/c 0)
    have je (j : Fin n) : Jet l n (w j) (e j) := by
      simpa [w,e] using (((Jet.const n ((m j+1:ℕ):ℝ)).mul (vj j).lower).add
        ((Jet.id n).mul (jv j)))
    obtain ⟨b,hb,eb⟩ := ih m mi w e (fun j => mul_ne_zero (by positivity) (div_ne_zero (nz _) (nz _))) je
    have all : ∀ᶠ z : P×ℝ in near l, u 0 z.1 z.2≠0 ∧
        ∀ j, HasDerivAt (v j z.1) (v' j z.1 z.2) z.2 :=
      ((jet 0).limit.eventually_ne (nz 0)).and (eventually_all.mpr dv)
    obtain ⟨a,ha,ea⟩ := interval (l:=l) (A:=fun p t => u 0 p t≠0 ∧
      ∀ j, HasDerivAt (v j p) (v' j p t) t) all
    refine ⟨min a b,lt_min ha hb,?_⟩
    filter_upwards [ea,eb] with p ep ep'
    refine ⟨fun t ht => mul_ne_zero (pow_ne_zero _ ht.1.ne') (ep t ⟨ht.1,ht.2.trans_le (min_le_left _ _)⟩).1,
      fun j t => t^(m j)*w j p t,?_,restrict ep' (min_le_right _ _)⟩
    intro j t ht
    have ept := ep t ⟨ht.1,ht.2.trans_le (min_le_left _ _)⟩
    have dh := (hasDerivAt_pow (m j+1) t).mul (ept.2 j)
    have eq : (fun x : ℝ => x^(h j.succ)*u j.succ p x/(x^(h 0)*u 0 p x)) =ᶠ[𝓝 t]
        fun x => x^(m j+1)*v j p x := by
      filter_upwards [eventually_ne_nhds ht.1.ne'] with x hx
      rw [ex,pow_add]
      dsimp [v]
      field_simp [pow_ne_zero (h 0) hx]
    apply HasDerivAt.congr_of_eventuallyEq _ eq
    convert! dh using 1
    dsimp [w]
    simp only [Nat.cast_add,Nat.cast_one,pow_succ]
    ring

end OMA.JetRolle686

/- Recover an absolute limit of five observations from a nonsingular
normalized evaluation basis and the integer conic determinant estimate. -/
namespace OMA.ConicBasis686
open Matrix Finset

def row (f g : ℝ→ℝ) (t : ℝ) : Fin 6→ℝ :=
  ![1,t,t^2,t^2*f t,t^2*(f t)^2,t^2*g t]

theorem transfer (y x t : Fin 6→ℝ) (a k b c d : ℝ) (hk : k≠0) (hb : b≠0)
    (f g : ℝ→ℝ) (ht : ∀ i, t i≠0) (yt : ∀ i, y i=k/t i)
    (xt : ∀ i, x i=a*y i+b*f (t i))
    (gt : ∀ i, g (t i)=f (t i)/t i-c-d*(f (t i))^2)
    (non : (Matrix.of fun i j => row f g (t i) j).det≠0) :
    (OMA.ConicStrip686.conic y x).det≠0 := by
  intro eq
  obtain ⟨A,ne,zero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr eq
  let v1 := A 1+a*A 2
  let v2 := b*A 2
  let v3 := A 3+a*A 4+a^2*A 5
  let v4 := b*A 4+2*a*b*A 5
  let v5 := b^2*A 5
  let w : Fin 6→ℝ := ![k^2*v3,k*v1,A 0+k*c*v4,v2,v5+k*d*v4,k*v4]
  have vanish : (Matrix.of fun i j => row f g (t i) j) *ᵥ w=0 := by
    funext i
    have ev := congrFun zero i
    simp [OMA.ConicStrip686.conic,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] at ev
    simp [row,w,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,v1,v2,v3,v4,v5,gt]
    rw [xt,yt] at ev
    field_simp [ht i] at ev ⊢
    linear_combination ev
  have w0 : w=0 := by
    by_contra nz
    exact non (Matrix.exists_mulVec_eq_zero_iff.mp ⟨w,nz,vanish⟩)
  have z0 := congrFun w0 0
  have z1 := congrFun w0 1
  have z2 := congrFun w0 2
  have z3 := congrFun w0 3
  have z4 := congrFun w0 4
  have z5 := congrFun w0 5
  simp [w] at z0 z1 z2 z3 z4 z5
  have z : v4=0 := z5.resolve_left hk
  have e5 : A 5=0 := (mul_eq_zero.mp (show v5=0 by rw [z] at z4; linarith)).resolve_left (pow_ne_zero _ hb)
  have e2 : A 2=0 := (mul_eq_zero.mp z3).resolve_left hb
  have e4 : A 4=0 := (mul_eq_zero.mp (show b*A 4=0 by simpa [v4,e5] using z)).resolve_left hb
  have e3 : A 3=0 := by simpa [v3,e4,e5,hk] using z0
  have e1 : A 1=0 := by simpa [v1,e2,hk] using z1
  have e0 : A 0=0 := by simpa [z] using z2
  apply ne; funext j
  fin_cases j <;> first | exact e0 | exact e1 | exact e2 | exact e3 | exact e4 | exact e5

end OMA.ConicBasis686

/- A large prime power in either block must also occur in one factor from
    the opposite block. Its k-th power divides the nonzero difference of the
    two k-th powers obtained by repeating the factors instead of their blocks. -/
namespace OMA.SmoothBlocks686
open Finset OMA.Gap686

private lemma envelope (s k : ℕ) : (s+1)^k ≤ block s k ∧ block s k ≤ (s+k)^k := by
  constructor
  · calc
      (s+1)^k = ∏ _i∈range k,(s+1) := by simp
      _ ≤ _ := prod_le_prod' (fun i _ => Nat.le_add_right (s+1) i)
  · calc
      _ ≤ ∏ _i∈range k,(s+k) := prod_le_prod' (fun i hi => by
        have := mem_range.mp hi; change s+1+i ≤ s+k; omega)
      _ = _ := by simp

private lemma spread (s k : ℕ) (hk : 1 ≤ k) :
    (s+k)^k ≤ (s+1)^k + k^2*(s+k)^(k-1) := by
  have hk' : (1:ℤ) ≤ k := by exact_mod_cast hk
  have h := abs_pow_sub_pow_le (α:=ℤ) ((s:ℤ)+k) ((s:ℤ)+1) k
  rw [abs_of_nonneg (by omega : 0 ≤ (s:ℤ)+k-((s:ℤ)+1)),abs_of_nonneg (by positivity : 0 ≤ (s:ℤ)+k),
    abs_of_nonneg (by positivity : 0 ≤ (s:ℤ)+1),max_eq_left (by omega)] at h
  have diff := (le_abs_self _).trans h
  have kcap : ((s:ℤ)+k-((s:ℤ)+1))*k ≤ (k:ℤ)^2 := by nlinarith
  have final := diff.trans (mul_le_mul_of_nonneg_right kcap (by positivity))
  exact_mod_cast (show ((s:ℤ)+k)^k ≤ ((s:ℤ)+1)^k+(k:ℤ)^2*((s:ℤ)+k)^(k-1) by linarith)

private lemma independent (x y k : ℕ) (hx : 0<x) (hk : 3 ≤ k) : y^k ≠ 4*x^k := by
  intro h
  have pw := congrArg (fun z:ℕ => z.factorization 2) h
  simp only [Nat.factorization_mul (by decide : 4 ≠ 0) (pow_ne_zero k hx.ne'),Nat.factorization_pow,
    Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul] at pw
  have ev : Nat.factorization 4 2=2 := by
    change (2^2:ℕ).factorization 2=2
    rw [Nat.factorization_pow,Finsupp.smul_apply,Nat.Prime.factorization_self Nat.prime_two]
    decide
  rw [ev] at pw
  have ne := congrArg (fun t:ℕ => t%k) pw
  simp [Nat.add_mod,Nat.mod_eq_of_lt (by omega : 2<k)] at ne

/-- A common divisor of a denominator factor and a numerator factor is small,
    without requiring that divisor to be a prime power. -/
theorem common {k n m i j q : ℕ} (hk : 3 ≤ k) (hf : four k n m)
    (hi : i<k) (hj : j<k) (lo : q ∣ n+1+i) (up : q ∣ m+1+j) :
    q^k ≤ k^2*(3^(k-1)+4)*(n+k)^(k-1) := by
  let x := n+1+i
  let y := m+1+j
  have xn : n+1 ≤ x := by dsimp [x]; omega
  have nx : x ≤ n+k := by dsimp [x]; omega
  have ym : m+1 ≤ y := by dsimp [y]; omega
  have my : y ≤ m+k := by dsimp [y]; omega
  have qx : q^k ∣ 4*x^k := (pow_dvd_pow_of_dvd lo k).trans (dvd_mul_left _ 4)
  have qy := pow_dvd_pow_of_dvd up k
  change q^k ∣ y^k at qy
  obtain ⟨n1,n2⟩ := envelope n k
  obtain ⟨m1,m2⟩ := envelope m k
  have eq := equation hf
  have rel : m+1 ≤ 2*(n+k) := by
    apply le_of_pow_le_pow_left₀ (by omega : k ≠ 0) (Nat.zero_le _)
    rw [mul_pow]
    have coeff : 4 ≤ 2^k := (Nat.pow_le_pow_right (by decide : 0<2) (by omega : 2 ≤ k))
    calc
      _ ≤ block m k := m1
      _ = 4*block n k := eq
      _ ≤ 2^k*(n+k)^k := Nat.mul_le_mul coeff n2
  have cap : m+k ≤ 3*(n+k) := by omega
  let t := (n+k)^(k-1)
  let E := k^2*(3^(k-1)+4)*t
  have s := spread n k (by omega)
  have r := spread m k (by omega)
  have power := Nat.pow_le_pow_left cap (k-1)
  rw [mul_pow] at power
  have top : k^2*(m+k)^(k-1)+4*(k^2*t) ≤ E := by
    dsimp [E,t]; nlinarith only [Nat.mul_le_mul_left (k^2) power]
  have estimates : y^k ≤ 4*x^k+E ∧ 4*x^k ≤ y^k+E := by
    have xn' := Nat.pow_le_pow_left xn k
    have nx' := Nat.pow_le_pow_left nx k
    have ym' := Nat.pow_le_pow_left ym k
    have my' := Nat.pow_le_pow_left my k
    dsimp only [t] at top
    omega
  have dif := independent x y k (by omega) hk
  change q^k ≤ E
  rcases lt_or_gt_of_ne dif with h|h
  · exact (Nat.le_of_dvd (by omega : 0<4*x^k-y^k) (Nat.dvd_sub qx qy)).trans (by omega)
  · exact (Nat.le_of_dvd (by omega : 0<y^k-4*x^k) (Nat.dvd_sub qy qx)).trans (by omega)

/-- Every prime power with prime greater than the block length, occurring in
    either entire product, satisfies the common-factor bound. -/
theorem smooth {k n m p e : ℕ} (hk : 3 ≤ k) (hf : four k n m) (hp : p.Prime) (big : k<p)
    (hd : p^e ∣ block n k ∨ p^e ∣ block m k) :
    (p^e)^k ≤ k^2*(3^(k-1)+4)*(n+k)^(k-1) := by
  by_cases he : e=0
  · subst e
    simp only [pow_zero,one_pow]
    exact Nat.mul_pos (Nat.mul_pos (pow_pos (by omega) _) (by positivity)) (pow_pos (by omega) _)
  have eq := equation hf
  have cp : p.Coprime 4 := by
    apply hp.coprime_iff_not_dvd.mpr
    intro dv
    have p4 := Nat.le_of_dvd (by decide : 0<4) dv
    have eq : p=4 := by omega
    subst p; norm_num at hp
  have low : p^e ∣ block n k := by
    rcases hd with d|d
    · exact d
    · rw [eq] at d; exact (cp.pow_left _).dvd_of_dvd_mul_left d
  have high : p^e ∣ block m k := by rw [eq]; exact low.trans (dvd_mul_left _ _)
  obtain ⟨i,hi,di⟩ := extract hp big (by omega) low
  obtain ⟨j,hj,dj⟩ := extract hp big (by omega) high
  exact common hk hf hi hj di dj

end OMA.SmoothBlocks686

namespace OMA.SmoothBlocks686
open OMA.Gap686 Finset

/-- Derivative of the length-k block polynomial at its i-th integer zero. -/
private def tangent (k i : ℕ) : ℤ := ∏ j ∈ (range k).erase i, ((j:ℤ)-i)

private lemma tangent_nonzero (k i : ℕ) : tangent k i ≠ 0 := by
  refine prod_ne_zero_iff.mpr fun j hj => ?_
  have ne := (mem_erase.mp hj).1
  omega

private lemma tangent_mod {s k i q : ℕ} (hi : i<k) (hd : q∣s+1+i) :
    (q:ℤ)^2 ∣ (block s k:ℤ)-tangent k i*((s:ℤ)+1+i) := by
  let z : ℤ := (s:ℤ)+1+i
  have qz : (q:ℤ) ∣ z := by dsimp [z]; exact_mod_cast hd
  have aux (S : Finset ℕ) : (∏ j∈S, ((j:ℤ)-i)) ≡
      (∏ j∈S, ((s:ℤ)+1+j)) [ZMOD (q:ℤ)] := by
    induction S using Finset.induction_on with
    | empty => simp
    | insert a S ha ih =>
      rw [prod_insert ha,prod_insert ha]
      refine Int.ModEq.mul (Int.modEq_iff_dvd.mpr ?_) ih
      convert qz using 1; dsimp [z]; ring
  have h := mul_dvd_mul (aux ((range k).erase i)).dvd qz
  rw [← sq,sub_mul] at h
  simpa only [block,Nat.cast_prod,Nat.cast_add,Nat.cast_one,z,tangent,
    (range k).prod_erase_mul (fun j => (s:ℤ)+1+(j:ℤ)) (mem_range.mpr hi)] using h

/-- For every fixed length at least three, a divisor shared by *any* two
    opposite factors is bounded by a constant times the square root of n.
    When the first-order congruence vanishes identically, the common-divisor
    power bound forces n itself to be bounded in terms of k. -/
theorem common_sqrt (k : ℕ) (hk : 3≤k) : ∃ C : ℕ,
    ∀ {n m i j q : ℕ}, four k n m → i<k → j<k →
      q∣n+1+i → q∣m+1+j → q^2 ≤ C*(n+k) := by
  let B := ∑ i∈range k,(tangent k i).natAbs
  let K := (k*B)^k*(k^2*(3^(k-1)+4))
  refine ⟨7*B+K,?_⟩
  intro n m i j q hf hi hj lo up
  let x := n+1+i
  let y := m+1+j
  let g := x.gcd y
  have maxT {l : ℕ} (hl : l<k) : (tangent k l).natAbs ≤ B :=
    single_le_sum (f:=fun l => (tangent k l).natAbs) (by simp) (mem_range.mpr hl)
  have xx : x≤n+k := by dsimp [x]; omega
  have xlo : n+1 ≤ x := by dsimp [x]; omega
  have xpos : 0<x := by omega
  have gp : 0<g := Nat.gcd_pos_of_pos_left y xpos
  have mcap : m+1 ≤ 2*(n+k) := by
    apply le_of_pow_le_pow_left₀ (by omega : k≠0) (Nat.zero_le _)
    rw [mul_pow]
    calc
      _ ≤ block m k := (envelope m k).1
      _ = 4*block n k := equation hf
      _ ≤ 2^k*(n+k)^k := Nat.mul_le_mul
        (Nat.pow_le_pow_right (by decide : 0<2) (by omega : 2≤k)) (envelope n k).2
  have yy : y≤3*(n+k) := by dsimp [y]; omega
  let L : ℤ := tangent k j*(y:ℤ)-4*tangent k i*(x:ℤ)
  have div : (q:ℤ)^2 ∣ L := by
    obtain ⟨u,hu⟩ := tangent_mod hi lo
    obtain ⟨v,hv⟩ := tangent_mod hj up
    have h : (block m k:ℤ)=4*(block n k:ℤ) := by exact_mod_cast equation hf
    refine ⟨4*u-v,?_⟩
    dsimp [L,x,y]
    linear_combination 4*hu-hv+h
  by_cases zero : L=0
  · have equality : (tangent k j).natAbs * y = (4*tangent k i).natAbs*x := by
      have h : tangent k j*(y:ℤ)=4*tangent k i*(x:ℤ) := sub_eq_zero.mp zero
      simpa only [Int.natAbs_mul,Int.natAbs_natCast] using congrArg Int.natAbs h
    have d1 : x ∣ (tangent k j).natAbs*x := dvd_mul_left _ _
    have d2 : x ∣ (tangent k j).natAbs*y := equality ▸ dvd_mul_left _ _
    have divg : x ∣ (tangent k j).natAbs*g := by
      simpa only [Nat.gcd_mul_left] using Nat.dvd_gcd d1 d2
    have xbound := (Nat.le_of_dvd (Nat.mul_pos (Int.natAbs_pos.mpr (tangent_nonzero k j)) gp) divg).trans
      (Nat.mul_le_mul_right g (maxT hj))
    have nx : n+k ≤ k*x := by nlinarith [Nat.mul_le_mul_left k xlo]
    have power := Nat.pow_le_pow_left (nx.trans (Nat.mul_le_mul_left k xbound)) k
    have power' : (n+k)^k ≤ (k*B)^k*g^k := by simpa only [←mul_assoc,mul_pow] using power
    have hcommon := common hk hf hi hj (Nat.gcd_dvd_left x y) (Nat.gcd_dvd_right x y)
    change g^k ≤ _ at hcommon
    have trim : (n+k)^(k-1)*(n+k) ≤ (n+k)^(k-1)*K := by
      calc
        _ = (n+k)^k := by rw [←pow_succ, Nat.sub_add_cancel (by omega : 1≤k)]
        _ ≤ _ := power'
        _ ≤ (k*B)^k*(k^2*(3^(k-1)+4)*(n+k)^(k-1)) := Nat.mul_le_mul_left _ hcommon
        _ = _ := by dsimp [K]; ring
    have nk := Nat.le_of_mul_le_mul_left trim (pow_pos (by omega : 0<n+k) _)
    have qx := (Nat.le_of_dvd xpos lo).trans xx
    rw [sq]
    exact Nat.mul_le_mul (qx.trans (by omega)) qx
  · have bound : L.natAbs ≤ 7*B*(n+k) := by
      have h := Int.natAbs_add_le (tangent k j*(y:ℤ)) (-(4*tangent k i*(x:ℤ)))
      change (tangent k j*(y:ℤ)-4*tangent k i*(x:ℤ)).natAbs ≤ _
      rw [←sub_eq_add_neg] at h
      simp only [Int.natAbs_neg,Int.natAbs_mul,Int.natAbs_natCast] at h
      have lhs := Nat.mul_le_mul (maxT hj) yy
      have rhs := Nat.mul_le_mul (maxT hi) xx
      norm_num at h
      nlinarith only [h,lhs,rhs]
    have qsmall : q^2 ≤ L.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr zero)
      (by simpa only [Int.natAbs_pow,Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr div)
    exact (qsmall.trans bound).trans (Nat.mul_le_mul_right _ (by omega))

private lemma capture_any {s k p e c : ℕ} (hk : 0<k) (hp : p.Prime) (hc : 0<c)
    (hd : p^e ∣ c*block s k) :
    ∃ i<k, p^e ∣ c*k.factorial^k*(s+1+i) := by
  classical
  let x (j : ℕ) := s+1+j
  have pos (j : ℕ) : 0<x j := by dsimp [x]; omega
  obtain ⟨i,hi,maxi⟩ := (range k).exists_max_image (fun j => (x j).factorization p)
    ⟨0,mem_range.mpr hk⟩
  refine ⟨i,mem_range.mp hi,?_⟩
  let S := (range k).erase i
  have each (j : ℕ) (hj : j∈S) : (x j).factorization p ≤ k.factorial.factorization p := by
    obtain ⟨ne,mem⟩ := mem_erase.mp hj
    let t := p^((x j).factorization p)
    have a : t ∣ x j := (hp.pow_dvd_iff_le_factorization (pos j).ne').mpr le_rfl
    have b : t ∣ x i := (hp.pow_dvd_iff_le_factorization (pos i).ne').mpr (maxi j mem)
    apply (hp.pow_dvd_iff_le_factorization (Nat.factorial_ne_zero k)).mp
    have jlt := mem_range.mp mem
    have ilt := mem_range.mp hi
    rcases lt_or_gt_of_ne ne with h|h
    · exact (Nat.dvd_sub b a).trans (Nat.dvd_factorial (by dsimp [x]; omega) (by dsimp [x]; omega))
    · exact (Nat.dvd_sub a b).trans (Nat.dvd_factorial (by dsimp [x]; omega) (by dsimp [x]; omega))
  have sum : (∑ j∈S,(x j).factorization p) ≤ k*k.factorial.factorization p := calc
    _ ≤ ∑ _j∈S,k.factorial.factorization p := sum_le_sum each
    _ ≤ _ := by
      simp only [sum_const,nsmul_eq_mul]
      exact Nat.mul_le_mul_right _ ((card_le_card (erase_subset i (range k))).trans_eq (card_range k))
  have total := (hp.pow_dvd_iff_le_factorization (Nat.mul_pos hc (block_pos s k)).ne').mp hd
  rw [Nat.factorization_mul hc.ne' (block_pos s k).ne',Finsupp.add_apply] at total
  have val : (block s k).factorization p=(∑ j∈S,(x j).factorization p)+(x i).factorization p := by
    change (∏ j∈range k,x j).factorization p=_
    rw [Nat.factorization_prod_apply (fun j _ => (pos j).ne'),sum_erase_add _ _ hi]
  rw [val] at total
  apply (hp.pow_dvd_iff_le_factorization (Nat.mul_pos
    (Nat.mul_pos hc (pow_pos (Nat.factorial_pos k) k)) (pos i)).ne').mpr
  rw [Nat.factorization_mul (Nat.mul_pos hc (pow_pos (Nat.factorial_pos k) k)).ne' (pos i).ne',
    Nat.factorization_mul hc.ne' (pow_pos (Nat.factorial_pos k) k).ne',Nat.factorization_pow]
  simp only [Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul]
  omega

/-- At every fixed length k≥3 all the prime powers in either full product
    are O_k(√n), including those over small primes dividing several factors. -/
theorem smooth_sqrt (k : ℕ) (hk : 3≤k) : ∃ C : ℕ,
    ∀ {n m p e : ℕ}, four k n m → p.Prime →
      (p^e∣block n k ∨ p^e∣block m k) → (p^e)^2 ≤ C*(n+k) := by
  obtain ⟨C,hC⟩ := common_sqrt k hk
  let F := 4*k.factorial^k
  refine ⟨F^2*C,?_⟩
  intro n m p e hf hp hd
  have upper : p^e∣block m k := hd.elim
    (fun d => by rw [equation hf]; exact d.trans (dvd_mul_left _ _)) id
  have lower : p^e∣4*block n k := equation hf ▸ upper
  obtain ⟨i,hi,di⟩ := capture_any (by omega) hp (by decide : 0<4) lower
  obtain ⟨j,hj,dj⟩ := capture_any (k:=k) (s:=m) (by omega) hp (by decide : 0<1)
    (by simpa using upper)
  let x := n+1+i
  let y := m+1+j
  let g := x.gcd y
  have dx : p^e ∣ F*x := di
  have dy : p^e ∣ F*y := dj.trans ⟨4,by dsimp [F,y]; ring⟩
  have dg : p^e ∣ F*g := by simpa only [Nat.gcd_mul_left] using Nat.dvd_gcd dx dy
  have gp : 0<g := Nat.gcd_pos_of_pos_left _ (by dsimp [x]; omega)
  have small := Nat.le_of_dvd (Nat.mul_pos (by dsimp [F]; positivity) gp) dg
  have line := hC hf hi hj (Nat.gcd_dvd_left x y) (Nat.gcd_dvd_right x y)
  calc
    _ ≤ (F*g)^2 := Nat.pow_le_pow_left small _
    _ = F^2*g^2 := mul_pow _ _ _
    _ ≤ F^2*(C*(n+k)) := Nat.mul_le_mul_left _ line
    _ = _ := by ring

end OMA.SmoothBlocks686

namespace OMA.SmoothBlocks686
open Finset OMA.Gap686

private def slope (i : ℕ) : ℤ := 5*(2-(i:ℤ))^4-15*(2-(i:ℤ))^2+4

private lemma linear_part {s i q : ℕ} (hi : i<5) (h : q ∣ s+1+i) :
    (q:ℤ)^2 ∣ (block s 5:ℤ)-slope i*((s:ℤ)+1+i) := by
  let c : ℤ := 2-i
  let z : ℤ := (s:ℤ)+1+i
  have center : (s:ℤ)+3=z+c := by dsimp [z,c]; ring
  have zero : c^5-5*c^3+4*c=0 := by
    dsimp [c]; interval_cases i <;> norm_num
  have body : (block s 5:ℤ) = ((s:ℤ)+3)^5-5*((s:ℤ)+3)^3+4*((s:ℤ)+3) := by
    simp [block,Finset.prod_range_succ]; ring
  obtain ⟨a,ha⟩ := h
  have za : z=(q:ℤ)*a := by dsimp [z]; exact_mod_cast ha
  refine ⟨(a:ℤ)^2*(z^3+5*c*z^2+10*c^2*z+10*c^3-5*z-15*c),?_⟩
  change (block s 5:ℤ)-(5*c^4-15*c^2+4)*z = _
  rw [body,center,←mul_assoc,←mul_pow,←za]
  linear_combination zero

/-- If q divides a factor from each length-five block, its square divides a
    signed linear combination of just those two factors, not the whole blocks. -/
private lemma linear_dvd {n m i j q : ℕ} (hf : four 5 n m) (hi : i<5) (hj : j<5)
    (lo : q ∣ n+1+i) (up : q ∣ m+1+j) :
    (q:ℤ)^2 ∣ slope j*((m:ℤ)+1+j)-4*slope i*((n:ℤ)+1+i) := by
  obtain ⟨u,hu⟩ := linear_part hi lo
  obtain ⟨v,hv⟩ := linear_part hj up
  have eq : (block m 5:ℤ)=4*(block n 5:ℤ) := by exact_mod_cast equation hf
  exact ⟨4*u-v,by linear_combination 4*hu-hv+eq⟩

private lemma slope_cases {i : ℕ} (hi : i<5) : slope i=24 ∨ slope i= -6 ∨ slope i=4 := by
  interval_cases i <;> norm_num [slope]

/-- For length five the first-order coefficients rule out every large common
    divisor: the square of that divisor is at most 168 times the block scale. -/
theorem common_five {n m i j q : ℕ} (hf : four 5 n m) (hi : i<5) (hj : j<5)
    (lo : q ∣ n+1+i) (up : q ∣ m+1+j) : q^2 ≤ 168*(n+5) := by
  let x := n+1+i
  let y := m+1+j
  have hx : 0<x := by dsimp [x]; omega
  have xx : x ≤ n+5 := by dsimp [x]; omega
  have xy : x<y := by dsimp [x,y]; have := hf.2.1; omega
  have qx : q ≤ x := Nat.le_of_dvd hx lo
  have mcap : m+1 ≤ 2*(n+5) := by
    apply le_of_pow_le_pow_left₀ (by decide : 5≠0) (Nat.zero_le _)
    rw [mul_pow]
    calc
      _ ≤ block m 5 := (envelope m 5).1
      _ = 4*block n 5 := equation hf
      _ ≤ 2^5*(n+5)^5 := Nat.mul_le_mul (by decide) (envelope n 5).2
  by_cases small : n<7
  · calc
      q^2 ≤ (n+5)^2 := Nat.pow_le_pow_left (qx.trans xx) _
      _ ≤ _ := by rw [pow_two]; exact Nat.mul_le_mul_right _ (by omega)
  have upper : y<4*x := by dsimp [x,y]; omega
  have yy : y ≤ 3*(n+5) := by dsimp [y]; omega
  let L : ℤ := slope j*(y:ℤ)-4*slope i*(x:ℤ)
  have div : (q:ℤ)^2 ∣ L := by simpa [L,x,y] using linear_dvd hf hi hj lo up
  have xy' : (x:ℤ)<y := by exact_mod_cast xy
  have upper' : (y:ℤ)<4*x := by exact_mod_cast upper
  have xpos : 0<(x:ℤ) := by exact_mod_cast hx
  have nz : L≠0 := by
    dsimp only [L]
    rcases slope_cases hi with a|a|a <;> rcases slope_cases hj with b|b|b <;>
      rw [a,b] <;> omega
  have SI (r : ℕ) (hr : r<5) : |slope r| ≤ 24 := by
    rcases slope_cases hr with a|a|a <;> rw [a] <;> decide
  have bound : |L| ≤ 24*y+96*(x:ℤ) := by
    dsimp only [L]
    calc
      _ ≤ |slope j*(y:ℤ)|+|4*slope i*(x:ℤ)| := abs_sub ..
      _ ≤ _ := by
        simp only [abs_mul,abs_of_nonneg (by positivity : 0≤(y:ℤ)),
          abs_of_nonneg (by positivity : 0≤(x:ℤ)),abs_of_nonneg (by decide : (0:ℤ)≤4)]
        linarith only [mul_le_mul_of_nonneg_right (SI j hj) (by positivity : 0≤(y:ℤ)),
          mul_le_mul_of_nonneg_right (SI i hi) (by positivity : 0≤(x:ℤ))]
  have qsmall : (q:ℤ)^2 ≤ |L| := Int.le_of_dvd (abs_pos.mpr nz)
    (by rcases abs_choice L with h|h <;> rw [h]; exacts [div,dvd_neg.mpr div])
  have xu : (x:ℤ)≤(n:ℤ)+5 := by exact_mod_cast xx
  have yu : (y:ℤ)≤3*((n:ℤ)+5) := by exact_mod_cast yy
  exact_mod_cast (show (q:ℤ)^2≤168*((n:ℤ)+5) by linarith)

/-- Every prime power of prime greater than five in any of the ten factors
    is at most the square root of 168(n+5). -/
theorem smooth_five {n m p e : ℕ} (hf : four 5 n m) (hp : p.Prime) (big : 5<p)
    (hd : p^e∣block n 5 ∨ p^e∣block m 5) : (p^e)^2 ≤ 168*(n+5) := by
  by_cases he : e=0
  · simp [he]; omega
  have eq := equation hf
  have cp : p.Coprime 4 := hp.coprime_iff_not_dvd.mpr (fun dv =>
    (not_le.mpr (by omega : 4<p)) (Nat.le_of_dvd (by decide) dv))
  have low : p^e∣block n 5 := by
    rcases hd with d|d
    · exact d
    · rw [eq] at d; exact (cp.pow_left _).dvd_of_dvd_mul_left d
  have high : p^e∣block m 5 := by rw [eq]; exact low.trans (dvd_mul_left _ _)
  obtain ⟨i,hi,di⟩ := extract hp big (by omega) low
  obtain ⟨j,hj,dj⟩ := extract hp big (by omega) high
  exact common_five hf hi hj di dj

/-- For any five consecutive integers, every prime-power divisor of their
    product divides 4! times one of the five integers. Multipliers can be
    carried through unchanged. -/
private theorem capture {s p e c : ℕ} (hp : p.Prime) (hc : 0<c)
    (hd : p^e ∣ c*block s 5) : ∃ i<5, p^e ∣ 24*c*(s+1+i) := by
  classical
  let xs (j : ℕ) := s+1+j
  obtain ⟨i,hi,maxi⟩ := (range 5).exists_max_image (fun j => (xs j).factorization p) ⟨0,by decide⟩
  refine ⟨i,mem_range.mp hi,?_⟩
  have factor (A j : ℕ) (hj : j<5) (he : A*xs j=block s 5) :
      p^e ∣ c*A*xs i := by
    have posj : 0<xs j := by dsimp [xs]; omega
    have posi : 0<xs i := by dsimp [xs]; omega
    have posA : 0<A := by
      by_contra! no
      have aa : A=0 := by omega
      have bd := block_pos s 5
      simp [aa] at he; omega
    have first := (hp.pow_dvd_iff_le_factorization
      (Nat.mul_pos hc (block_pos s 5)).ne').1 hd
    rw [←he,←mul_assoc,Nat.factorization_mul (Nat.mul_pos hc posA).ne' posj.ne',
      Finsupp.add_apply] at first
    apply (hp.pow_dvd_iff_le_factorization (Nat.mul_pos (Nat.mul_pos hc posA) posi).ne').2
    rw [Nat.factorization_mul (Nat.mul_pos hc posA).ne' posi.ne',Finsupp.add_apply]
    exact first.trans (Nat.add_le_add_left (maxi j (mem_range.mpr hj)) _)
  have int_factor (A j : ℕ) (hj : j<5) (he : A*xs j=block s 5) :
      ∃ t : ℤ, (c:ℤ)*A*(xs i:ℤ)=(p^e:ℕ)*t := by
    obtain ⟨t,ht⟩ := factor A j hj he
    exact ⟨(t:ℤ),by exact_mod_cast ht⟩
  obtain ⟨a,ha⟩ := int_factor (xs 1*xs 2*xs 3*xs 4) 0 (by decide) (by
    simp [block,xs,prod_range_succ]; ring)
  obtain ⟨b,hb⟩ := int_factor (xs 0*xs 2*xs 3*xs 4) 1 (by decide) (by
    simp [block,xs,prod_range_succ]; ring)
  obtain ⟨d,hd'⟩ := int_factor (xs 0*xs 1*xs 3*xs 4) 2 (by decide) (by
    simp [block,xs,prod_range_succ]; ring)
  obtain ⟨f,hf⟩ := int_factor (xs 0*xs 1*xs 2*xs 4) 3 (by decide) (by
    simp [block,xs,prod_range_succ]; ring)
  obtain ⟨g,hg⟩ := int_factor (xs 0*xs 1*xs 2*xs 3) 4 (by decide) (by
    simp [block,xs,prod_range_succ])
  apply Int.natCast_dvd_natCast.mp
  refine ⟨a-4*b+6*d-4*f+g,?_⟩
  dsimp only [xs] at ha hb hd' hf hg
  push_cast at ha hb hd' hf hg ⊢
  linear_combination ha-4*hb+6*hd'-4*hf+hg

/-- There is no small-prime exception. In particular any of the ten factors
    which is itself a prime power must be small for the given start. -/
theorem smooth_five_all {n m p e : ℕ} (hf : four 5 n m) (hp : p.Prime)
    (hd : p^e ∣ block n 5 ∨ p^e ∣ block m 5) : (p^e)^2 ≤ 1548288*(n+5) := by
  have upper : p^e ∣ block m 5 := hd.elim
    (fun d => by rw [equation hf]; exact d.trans (dvd_mul_left _ _)) id
  have lower : p^e ∣ 4*block n 5 := equation hf ▸ upper
  obtain ⟨i,hi,di⟩ := capture hp (by decide : 0<4) lower
  obtain ⟨j,hj,dj⟩ := capture hp (by decide : 0<1) (by simpa using upper)
  let x := n+1+i
  let y := m+1+j
  let g := x.gcd y
  have dx : p^e ∣ 96*x := di
  have dy : p^e ∣ 96*y := dvd_trans dj ⟨4,by dsimp [y]; ring⟩
  have div : p^e ∣ 96*g := by
    simpa only [Nat.gcd_mul_left] using Nat.dvd_gcd dx dy
  have gp : 0<g := Nat.gcd_pos_of_pos_left _ (by dsimp [x]; omega)
  have hq := Nat.le_of_dvd (Nat.mul_pos (by decide) gp) div
  have res := common_five hf hi hj (Nat.gcd_dvd_left x y) (Nat.gcd_dvd_right x y)
  calc
    _ ≤ (96*g)^2 := Nat.pow_le_pow_left hq _
    _ = 96^2*g^2 := mul_pow _ _ _
    _ ≤ 96^2*(168*(n+5)) := Nat.mul_le_mul_left _ res
    _ = _ := by ring

/-- From start 171 onward none of the ten integers can itself be a power
    of a prime above five. The all-prime version has a larger threshold. -/
theorem no_power_five {n m s i p e : ℕ} (hf : four 5 n m) (hs : s=n ∨ s=m)
    (hi : i<5) (hp : p.Prime) (threshold : (171≤n ∧ 5<p) ∨ 1548291≤n) :
    s+1+i ≠ p^e := by
  intro pow
  have dv : p^e ∣ block s 5 := by
    rw [←pow]
    exact dvd_prod_of_mem (fun j => s+1+j) (mem_range.mpr hi)
  have inBlocks : p^e ∣ block n 5 ∨ p^e ∣ block m 5 := hs.elim
    (fun h => Or.inl (h ▸ dv)) (fun h => Or.inr (h ▸ dv))
  have low : n+1 ≤ p^e := by
    have sep := hf.2.1
    omega
  have square := Nat.pow_le_pow_left low 2
  rcases threshold with ⟨hn,big⟩|hn
  · have bound := smooth_five hf hp big inBlocks
    obtain ⟨t,ht⟩ := Nat.exists_eq_add_of_le hn
    rw [ht] at square bound
    nlinarith
  · have bound := smooth_five_all hf hp inBlocks
    obtain ⟨t,ht⟩ := Nat.exists_eq_add_of_le hn
    rw [ht] at square bound
    nlinarith

private def fiveValue (s : ℕ) := (s+1)*(s+2)*(s+3)*(s+4)*(s+5)

private lemma five_eval (s : ℕ) : block s 5=fiveValue s := by
  simp [block,fiveValue,prod_range_succ]

private lemma five_mono : StrictMono fiveValue := by
  apply strictMono_nat_of_lt_succ
  intro n
  dsimp [fiveValue]
  gcongr <;> omega

/-- The bisection merely suggests consecutive products to check. -/
private def propose (a v : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | t+1, lo, hi =>
    let b := (lo+hi)/2
    if a*fiveValue b ≤ v then propose a v t b hi else propose a v t lo b

private def excluded (a v R : ℕ) :=
  let b := propose a v 25 0 R
  v < a*fiveValue 0 || (a*fiveValue b < v && v < a*fiveValue (b+1))

private lemma exclude_sound {a v R : ℕ} (ok : excluded a v R) (j : ℕ) : a*fiveValue j ≠ v := by
  simp only [excluded,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at ok
  rcases ok with low|⟨l,r⟩
  · exact ne_of_gt (low.trans_le (Nat.mul_le_mul_left _ (five_mono.monotone (Nat.zero_le j))))
  rcases le_or_gt j (propose a v 25 0 R) with h|h
  · exact ne_of_lt ((Nat.mul_le_mul_left _ (five_mono.monotone h)).trans_lt l)
  · exact ne_of_gt (r.trans_le (Nat.mul_le_mul_left _ (five_mono.monotone h)))

private def clear5 (s : ℕ) :=
  excluded 1 (4*fiveValue s) (3*(s+5)) && excluded 4 (fiveValue s) (3*(s+5))

private lemma clear_sound {n m s : ℕ} (hf : four 5 n m) (hs : s=n ∨ s=m) : ¬clear5 s := by
  intro h
  have eq := equation hf
  rw [five_eval,five_eval] at eq
  obtain ⟨low,high⟩ := Bool.and_eq_true_iff.mp h
  rcases hs with rfl|rfl
  · exact exclude_sound low m (by simpa using eq)
  · exact exclude_sound high n eq.symm

private lemma clear_small : ∀ j : Fin 171, clear5 j.val := by decide +kernel

private lemma clear_powers : ∀ p : Fin 6, p.val.Prime → ∀ e : Fin 22, ∀ i : Fin 5,
    let s := p.val^e.val-1-i.val
    s<3100000 → clear5 s := by decide +kernel

/-- At length five all ten entries must have at least two distinct prime
    factors: none is a power of any prime at any starting height. -/
theorem no_prime_power_five {n m s i p e : ℕ} (hf : four 5 n m) (hs : s=n ∨ s=m)
    (hi : i<5) (hp : p.Prime) : s+1+i ≠ p^e := by
  by_cases small : n<171
  · exact (clear_sound hf (.inl rfl) (clear_small ⟨n,small⟩)).elim
  by_cases big : 5<p
  · exact no_power_five hf hs hi hp (.inl ⟨by omega,big⟩)
  by_cases large : 1548291≤n
  · exact no_power_five hf hs hi hp (.inr large)
  intro eq
  have mcap : m+1≤2*(n+5) := by
    apply le_of_pow_le_pow_left₀ (by decide : 5≠0) (Nat.zero_le _)
    calc
      _ ≤ block m 5 := (envelope m 5).1
      _ = 4*block n 5 := equation hf
      _ ≤ 2^5*(n+5)^5 := Nat.mul_le_mul (by decide) (envelope n 5).2
      _ = _ := (mul_pow _ _ _).symm
  have sCap : s<3100000 := by omega
  have eCap : e<22 := by
    by_contra! h
    have h1 := (Nat.pow_le_pow_left hp.two_le e)
    have h2 := Nat.pow_le_pow_right (by decide : 0<2) h
    norm_num at h2
    omega
  have ident : p^e-1-i=s := by omega
  have c := clear_powers ⟨p,by omega⟩ hp ⟨e,eCap⟩ ⟨i,hi⟩
  change p^e-1-i<3100000 → clear5 (p^e-1-i) at c
  rw [ident] at c
  exact clear_sound hf hs (c sCap)

end OMA.SmoothBlocks686

/- Arithmetic restrictions on the primitive coordinates of a length-five witness to quotient four. -/
namespace OMA.Five686

def P {R : Type*} [Ring R] (x : R) : R := x^5-5*x^3+4*x

private theorem normalized {a b g : ℤ} (hg : g ≠ 0) (he : P (g*a)=4*P (g*b)) :
    g^4*(a^5-4*b^5)-5*g^2*(a^3-4*b^3)+4*(a-4*b)=0 := by
  apply (mul_eq_zero.mp (b := _) (show g*(_ : ℤ)=0 by
    unfold P at he; linear_combination he)).resolve_left hg

/-- The common scale divides the difference of the primitive directions to second order. -/
theorem scale {a b g : ℤ} (hg : g ≠ 0) (he : P (g*a)=4*P (g*b)) :
    g^2 ∣ 4*(a-4*b) := by
  exact ⟨5*(a^3-4*b^3)-g^2*(a^5-4*b^5),by linear_combination normalized hg he⟩

/-- After removing the common square scale, the linear direction has a quadratic
norm obstruction. In particular a prime >5 dividing the cofactor must admit 17Y²=5. -/
theorem conic {a b g : ℤ} (cop : IsCoprime a b) (hg : g ≠ 0)
    (he : P (g*a)=4*P (g*b)) :
    ∃ e : ℤ, 4*(a-4*b)=g^2*e ∧ e ∣ 240*(17*(g*b)^2-5) := by
  obtain ⟨e,he'⟩ := scale hg he
  refine ⟨e,he',?_⟩
  have cf : IsCoprime (a-4*b) b := by
    obtain ⟨u,v,h⟩ := cop
    exact ⟨u,v+4*u,by linear_combination h⟩
  have dv : (a-4*b) ∣ 60*g^2*(17*(g*b)^2-5) := by
    apply (cf.pow_right (n:=3)).dvd_of_dvd_mul_left
    refine ⟨-(g^4*(a^4+4*a^3*b+16*a^2*b^2+64*a*b^3+256*b^4)-
      5*g^2*(a^2+4*a*b+16*b^2)+4),?_⟩
    linear_combination normalized hg he
  obtain ⟨k,hk⟩ := dv
  refine ⟨k,?_⟩
  apply mul_left_cancel₀ (a := g^2) (pow_ne_zero _ hg)
  linear_combination 4*hk+k*he'

private theorem coprime_cubic {a b : ℤ} (cop : IsCoprime a b) :
    IsCoprime (a^3-4*b^3) b := by
  obtain ⟨u,v,h⟩ := cop.pow_left (m:=3)
  exact ⟨u,v+4*u*b^2,by linear_combination h⟩

/-- Removing the resultant 60 leaves a fourth-power congruence on the cubic factor. -/
theorem direction {a b g : ℤ} (cop : IsCoprime a b) (hg : g ≠ 0)
    (he : P (g*a)=4*P (g*b)) : a^3-4*b^3 ∣ 60*(a-g^4*b^5) := by
  apply ((coprime_cubic cop).pow_right (n:=4)).dvd_of_dvd_mul_left
  refine ⟨(a*(a+4*b)+b^2)*(g^4*b^2*a^2-5*g^2*b^2+4)-
    4*(a+4*b)*(a-g^4*b^5),?_⟩
  linear_combination -(a*(a+4*b)+b^2)*b^2 * normalized hg he

/-- At every prime power in the cubic direction except a bounded resultant,
four must be a twelfth power; this is an integer divisibility, not a bounded search. -/
theorem twelfth {a b g : ℤ} (cop : IsCoprime a b) (hg : g ≠ 0)
    (he : P (g*a)=4*P (g*b)) : a^3-4*b^3 ∣ 60*((g*b)^12-4) := by
  have H := direction cop hg he
  obtain ⟨j,hj⟩ := H
  apply ((coprime_cubic cop).pow_right (n:=3)).dvd_of_dvd_mul_left
  exact ⟨60-j*(a^2+a*(g^4*b^5)+(g^4*b^5)^2),by
    linear_combination -(a^2+a*(g^4*b^5)+(g^4*b^5)^2)*hj⟩

/-- A prime greater than five that is five modulo eight cannot divide a³−4b³. -/
theorem exclude {a b g : ℤ} (cop : IsCoprime a b) (hg : g ≠ 0)
    (he : P (g*a)=4*P (g*b)) {p : ℕ} (hp : p.Prime) (large : 5<p)
    (exc : p%8=5) : ¬(p:ℤ) ∣ a^3-4*b^3 := by
  let _ : Fact p.Prime := ⟨hp⟩
  intro hd
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr (hd.trans (twelfth cop hg he))
  have h60 : (60 : ZMod p) ≠ 0 := by
    intro eq
    have h := (ZMod.natCast_eq_zero_iff 60 p).mp (show ((60:ℕ):ZMod p)=0 by exact_mod_cast eq)
    have hh : p ∣ 2*2*3*5 := h
    simp only [hp.dvd_mul] at hh
    rcases hh with ((h|h)|h)|h <;> have := Nat.le_of_dvd (by decide) h <;> omega
  push_cast at hz
  have h12 : (((g:ZMod p)*b)^6-2)*(((g:ZMod p)*b)^6+2)=0 := by
    linear_combination (mul_eq_zero.mp hz).resolve_left h60
  rcases mul_eq_zero.mp h12 with h|h
  · have s : IsSquare (2:ZMod p) := ⟨((g:ZMod p)*b)^3,by linear_combination -h⟩
    have := (ZMod.exists_sq_eq_two_iff (p:=p) (by omega)).mp s
    omega
  · have s : IsSquare (-2:ZMod p) := ⟨((g:ZMod p)*b)^3,by linear_combination -h⟩
    have := (ZMod.exists_sq_eq_neg_two_iff (p:=p) (by omega)).mp s
    omega

private lemma centered (s : ℕ) :
    P ((s:ℤ)+3) = ((∏ i ∈ Finset.Icc 1 5, (s+i)) : ℕ) := by
  rw [show Finset.Icc 1 5 = ({1,2,3,4,5} : Finset ℕ) by decide]
  simp [P]
  ring

/-- Both global congruences from the original quotient of length-five blocks. -/
theorem of_blocks {m n : ℕ}
    (h : (4:ℚ) = ((∏ i ∈ Finset.Icc 1 5,(m+i)):ℕ) / ((∏ i ∈ Finset.Icc 1 5,(n+i)):ℕ)) :
    ∃ a b g : ℤ, 0<g ∧ IsCoprime a b ∧ (m:ℤ)+3=g*a ∧ (n:ℤ)+3=g*b ∧
      (a^3-4*b^3 ∣ 60*(((n:ℤ)+3)^12-4)) ∧
      ∃ e : ℤ, 4*(a-4*b)=g^2*e ∧ e ∣ 240*(17*((n:ℤ)+3)^2-5) := by
  let X := m+3
  let Y := n+3
  let g := Nat.gcd X Y
  have hg : 0<g := Nat.gcd_pos_of_pos_left _ (by dsimp [X]; omega)
  let a := X/g
  let b := Y/g
  have co : IsCoprime (a:ℤ) (b:ℤ) := (Nat.coprime_div_gcd_div_gcd hg).isCoprime
  have A : (m:ℤ)+3=(g:ℤ)*a := by exact_mod_cast (Nat.mul_div_cancel' (Nat.gcd_dvd_left X Y)).symm
  have B : (n:ℤ)+3=(g:ℤ)*b := by exact_mod_cast (Nat.mul_div_cancel' (Nat.gcd_dvd_right X Y)).symm
  have pn : 0< ∏ i ∈ Finset.Icc 1 5,(n+i) := Finset.prod_pos fun i hi => by
    have := (Finset.mem_Icc.mp hi).1; omega
  have Q := (eq_div_iff (by exact_mod_cast pn.ne' : ((∏ i ∈ Finset.Icc 1 5,(n+i)):ℕ)≠(0:ℚ))).mp h
  have eq : P ((g:ℤ)*a) = 4*P ((g:ℤ)*b) := by
    rw [← A,← B,centered,centered]
    exact_mod_cast Q.symm
  have gn : (g:ℤ) ≠ 0 := by exact_mod_cast hg.ne'
  refine ⟨a,b,g,by exact_mod_cast hg,co,A,B,?_,?_⟩
  · rw [B]; exact twelfth co gn eq
  · rw [B]; exact conic co gn eq

end OMA.Five686

#print axioms OMA.Transport686.projection
#print axioms OMA.Transport686.sum_diff
#print axioms OMA.Transport686.interval
#print axioms OMA.TransportVariance686.four_projections
#print axioms OMA.FareyMass686.pairs
#print axioms OMA.ConicStrip686.vanish
#print axioms OMA.JetRolle686.basis
#print axioms OMA.SmoothBlocks686.smooth_sqrt
#print axioms OMA.SmoothBlocks686.no_prime_power_five
#print axioms OMA.Five686.of_blocks

/- The exact arithmetic contradiction at the end of the reciprocal-prime
sieve. The exponential-sum input producing the prime is separate. -/
namespace OMA.SanderSieve686
open Finset OMA.Gap686

/-- A prime hits a block exactly when the next multiple lies in the block. -/
theorem hits {p s k : ℕ} (hp : p.Prime) :
    p ∣ block s k ↔ p ≤ s % p + k := by
  have small := Nat.mod_lt s hp.pos
  constructor
  · intro h
    obtain ⟨i,hi,hit⟩ := (hp.prime.dvd_finsetProd_iff _).mp h
    have il := mem_range.mp hi
    change p ∣ s + 1 + i at hit
    have reduced : p ∣ s % p + (1+i) := by
      rw [Nat.dvd_iff_mod_eq_zero, Nat.mod_add_mod]
      simpa [Nat.add_assoc] using Nat.mod_eq_zero_of_dvd hit
    have := Nat.le_of_dvd (by omega : 0 < s % p + (1+i)) reduced
    omega
  · intro h
    let i := p - s%p - 1
    have hi : i < k := by dsimp [i]; omega
    apply (hp.prime.dvd_finsetProd_iff _).mpr
    refine ⟨i,mem_range.mpr hi,?_⟩
    change p ∣ s+1+i
    rw [Nat.dvd_iff_mod_eq_zero, Nat.add_assoc, ← Nat.mod_add_mod s]
    have eq : s%p+(1+i)=p := by dsimp [i]; omega
    simp [eq]

/-- A prime with residues in the indicated open rectangle separates the
supports, even under the weaker hypothesis of block divisibility. -/
theorem separates {n m k p : ℕ} (hp : p.Prime) (lo : 10*k<p) (hi : p≤20*k)
    (near : 24*p < 25*(n%p)) (far : 2*(m%p)<p) :
    ¬ block n k ∣ block m k := by
  intro h
  have lower : p ∣ block n k := (hits hp).mpr (by omega)
  have upper := (hits hp).mp (lower.trans h)
  omega

theorem excludes_four {n m k p : ℕ} (hp : p.Prime) (lo : 10*k<p) (hi : p≤20*k)
    (near : 24*p < 25*(n%p)) (far : 2*(m%p)<p) :
    ¬ four k n m := by
  intro w
  apply separates hp lo hi near far
  rw [equation w]
  exact dvd_mul_left _ _

end OMA.SanderSieve686

#print axioms OMA.SanderSieve686.excludes_four
