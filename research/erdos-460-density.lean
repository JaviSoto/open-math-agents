import OMAStatements.S_erdos_460
import Mathlib

/-!
# Erdős 460: divergence in natural density (checked, elementary)

Problem `erdos-460` on Left to Solve. The statement `OMA.S_erdos_460` (`a`, `partialSum`, `main`) is
`statements/erdos-460.lean` in lefttosolve2/open-math-agents (stated by @YourFriendPollux, #1017),
imported unchanged as the checker builds it (`OMAStatements.S_erdos_460`).

Main result (`E460Density.density_zero`): for every real `B`,
`#{n < N | partialSum n < B} / N → 0`, i.e. `partialSum n → ∞` along a set of natural density one.
This is **not** the pointwise statement `main` (divergence for every `n`), which remains open here.

Route (elementary): rough offsets are greedy terms (`rough_mem`, `dom`), truncated primorial sums `ST`,
exact residue means, an assumption-free Mertens-type lower bound, a second-moment/Paley–Zygmund bound
inside each primorial class (`class_pz`, `class_pz_trunc_block`), a geometric bad-fraction step
(`E460Boost.boost`), and iteration plus counting (`E460Density`).

Credits and prior work: the rough-offset minorant and the lim sup statement follow Przemyslaw Chojecki,
https://www.ulam.ai/research/erdos-460-v2.pdf (Prop. 7, Thm. 8). Sven Hardy Benson,
https://erdos460paper.lovable.app/ , earlier claimed a stronger quantitative density-one result by
spectral-sieve methods; that claim is not checked or used here. Desk notes #104173 and #134993.
No novelty or solve credit is claimed.

Reproduction pins: formal-conjectures 9097e2f90e66d2f6244209cb1c07f7120d17ec53,
Mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Lean v4.33.1. With `OMAStatements` built as in
`tools/check.sh`, run `lake env lean` on this file inside the formal-conjectures checkout. Expected:
every `#print axioms` at the end reports `[propext, Classical.choice, Quot.sound]`.

Formalized by Claude Opus 5.5 High (claude-code) for @JaviSoto.
-/

namespace E460Rough
open OMA.S_erdos_460

lemma a_zero (n : ℕ) : a n 0 = 0 := by
  simp only [a]; rw [Nat.strongRec_eq]; rfl

lemma a_one (n : ℕ) : a n 1 = 1 := by
  simp only [a]; rw [Nat.strongRec_eq]; rfl

lemma a_succ_succ (n k : ℕ) : a n (k + 1 + 1) = sInf {m : ℕ | a n (k + 1) < m ∧
    ∀ i : ℕ, ∀ _ : i < k + 1 + 1,
      Int.gcd ((n : ℤ) - (m : ℤ)) ((n : ℤ) - ((a n i : ℕ) : ℤ)) = 1} := by
  simp only [a]; rw [Nat.strongRec_eq]; rfl

/-- If every prime factor of `n - t` exceeds `t` and `b < t < n`, then `n - t` and `n - b` are
coprime: a common prime would divide `t - b ≤ t`. -/
lemma cop (n t b : ℕ) (hbt : b < t) (htn : t < n)
    (hrough : ∀ p : ℕ, p.Prime → p ∣ n - t → t < p) :
    Int.gcd ((n : ℤ) - (t : ℤ)) ((n : ℤ) - (b : ℤ)) = 1 := by
  by_contra hd
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd
  have hdl : ((Int.gcd ((n : ℤ) - t) ((n : ℤ) - b) : ℕ) : ℤ) ∣ (n : ℤ) - t := Int.gcd_dvd_left ..
  have hdr : ((Int.gcd ((n : ℤ) - t) ((n : ℤ) - b) : ℕ) : ℤ) ∣ (n : ℤ) - b := Int.gcd_dvd_right ..
  have hp1 : (p : ℤ) ∣ (n : ℤ) - t := (Int.natCast_dvd_natCast.mpr hpd).trans hdl
  have hp2 : (p : ℤ) ∣ (n : ℤ) - b := (Int.natCast_dvd_natCast.mpr hpd).trans hdr
  have e1 : (n : ℤ) - t = ((n - t : ℕ) : ℤ) := by push_cast [htn.le]; ring
  have e2 : ((n : ℤ) - b) - ((n : ℤ) - t) = ((t - b : ℕ) : ℤ) := by push_cast [hbt.le]; ring
  have hq1 : p ∣ n - t := by rw [e1] at hp1; exact Int.natCast_dvd_natCast.mp hp1
  have hq2 : p ∣ t - b := by
    have := dvd_sub hp2 hp1; rw [e2] at this; exact Int.natCast_dvd_natCast.mp this
  have hle : p ≤ t - b := Nat.le_of_dvd (by omega) hq2
  have := hrough p hp hq1
  omega

/-- One greedy step: while all earlier terms are below `t`, the next term lies in `(a k, t]`. -/
lemma step (n t : ℕ) (htn : t < n) (hrough : ∀ p : ℕ, p.Prime → p ∣ n - t → t < p)
    (k : ℕ) (hk : ∀ i ≤ k, a n i < t) : a n k < a n (k + 1) ∧ a n (k + 1) ≤ t := by
  rcases k with _ | k
  · have h0 := hk 0 le_rfl
    rw [a_zero] at h0 ⊢; rw [a_one]; omega
  · rw [a_succ_succ]
    have hmem : t ∈ {m : ℕ | a n (k + 1) < m ∧ ∀ i : ℕ, ∀ _ : i < k + 1 + 1,
        Int.gcd ((n : ℤ) - (m : ℤ)) ((n : ℤ) - ((a n i : ℕ) : ℤ)) = 1} :=
      ⟨hk (k + 1) le_rfl, fun i hi => cop n t (a n i) (hk i (by omega)) htn hrough⟩
    exact ⟨(Nat.sInf_mem ⟨t, hmem⟩).1, Nat.sInf_le hmem⟩

/-- **Rough offsets are terms.** For `1 ≤ t < n`, if every prime factor of `n - t` exceeds `t`,
then `t` is a term of the greedy sequence `a n`. -/
theorem rough_mem (n t : ℕ) (ht1 : 1 ≤ t) (htn : t < n)
    (hrough : ∀ p : ℕ, p.Prime → p ∣ n - t → t < p) : ∃ k, a n k = t := by
  have hex : ∃ k, t ≤ a n k := by
    by_contra hno
    push_neg at hno
    have hmono : ∀ k, k ≤ a n k := by
      intro k
      induction k with
      | zero => omega
      | succ k ih => have := (step n t htn hrough k (fun i _ => hno i)).1; omega
    have h1 := hno t
    have h2 := hmono t
    omega
  classical
  set K := Nat.find hex with hKdef
  have hK : t ≤ a n K := Nat.find_spec hex
  have hmin : ∀ i < K, a n i < t := fun i hi => by
    have := Nat.find_min hex hi; omega
  have hK0 : K ≠ 0 := by
    intro h0; rw [h0, a_zero] at hK; omega
  obtain ⟨j, hj⟩ : ∃ j, K = j + 1 := ⟨K - 1, by omega⟩
  have hs := (step n t htn hrough j (fun i hi => hmin i (by omega))).2
  rw [← hj] at hs
  exact ⟨K, le_antisymm hs hK⟩

/-- `rough_mem` with the witness index bounded: `k ≤ t`, hence `k < n`. -/
theorem rough_mem' (n t : ℕ) (ht1 : 1 ≤ t) (htn : t < n)
    (hrough : ∀ p : ℕ, p.Prime → p ∣ n - t → t < p) : ∃ k, k ≤ t ∧ a n k = t := by
  have hex : ∃ k, t ≤ a n k := by
    obtain ⟨k, hk⟩ := rough_mem n t ht1 htn hrough
    exact ⟨k, hk.ge⟩
  classical
  set K := Nat.find hex with hKdef
  have hK : t ≤ a n K := Nat.find_spec hex
  have hmin : ∀ i < K, a n i < t := fun i hi => by
    have := Nat.find_min hex hi; omega
  have hK0 : K ≠ 0 := by
    intro h0; rw [h0, a_zero] at hK; omega
  obtain ⟨j, hj⟩ : ∃ j, K = j + 1 := ⟨K - 1, by omega⟩
  have hs := (step n t htn hrough j (fun i hi => hmin i (by omega))).2
  rw [← hj] at hs
  have hidx : ∀ i, i ≤ K → i ≤ a n i := by
    intro i
    induction i with
    | zero => intro _; omega
    | succ i ih =>
      intro hi
      have := (step n t htn hrough i (fun j hj => hmin j (by omega))).1
      have := ih (by omega)
      omega
  exact ⟨K, by have := hidx K le_rfl; omega, le_antisymm hs hK⟩

open scoped Classical in
/-- The offsets `1 ≤ t < n` whose complement `n - t` has no prime divisor `≤ t`. -/
noncomputable def R (n : ℕ) : Finset ℕ :=
  (Finset.Ico 1 n).filter (fun t => ∀ p : ℕ, p.Prime → p ∣ n - t → t < p)

lemma mem_R {n t : ℕ} (ht : t ∈ R n) :
    1 ≤ t ∧ t < n ∧ ∀ p : ℕ, p.Prime → p ∣ n - t → t < p := by
  classical
  simp only [R, Finset.mem_filter, Finset.mem_Ico] at ht
  exact ⟨ht.1.1, ht.1.2, ht.2⟩

/-- **Domination.** For every `n`, the exact upstream `partialSum n` is at least the reciprocal sum
over the rough offsets. -/
theorem dom (n : ℕ) : ∑ t ∈ R n, (1 : ℝ) / t ≤ partialSum n := by
  have hw : ∀ t ∈ R n, ∃ k, k ≤ t ∧ a n k = t := by
    intro t ht
    obtain ⟨h1, h2, h3⟩ := mem_R ht
    exact rough_mem' n t h1 h2 h3
  choose! g hg using hw
  have hinj : Set.InjOn g (R n) := by
    intro x hx y hy hxy
    rw [← (hg x hx).2, ← (hg y hy).2, hxy]
  calc ∑ t ∈ R n, (1 : ℝ) / t
      = ∑ t ∈ R n, (fun i => if 0 < a n i ∧ a n i < n then (1 : ℝ) / (a n i : ℝ) else 0) (g t) := by
        refine Finset.sum_congr rfl fun t ht => ?_
        obtain ⟨h1, h2, -⟩ := mem_R ht
        simp only [(hg t ht).2]
        rw [if_pos ⟨by omega, h2⟩]
    _ = ∑ i ∈ (R n).image g,
          (fun i => if 0 < a n i ∧ a n i < n then (1 : ℝ) / (a n i : ℝ) else 0) i :=
        (Finset.sum_image (f := fun i => if 0 < a n i ∧ a n i < n then (1 : ℝ) / (a n i : ℝ) else 0)
          hinj).symm
    _ ≤ ∑ i ∈ Finset.range n,
          (fun i => if 0 < a n i ∧ a n i < n then (1 : ℝ) / (a n i : ℝ) else 0) i := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro i hi
          obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hi
          obtain ⟨-, h2, -⟩ := mem_R ht
          rw [Finset.mem_range]
          have := (hg t ht).1
          omega
        · intro i _ _
          split_ifs <;> first | positivity | exact le_rfl
    _ = partialSum n := rfl

/-- **Sufficient condition for Erdős 460.** If the rough-offset reciprocal sums diverge, so do the
upstream partial sums, which is `OMA.S_erdos_460.main`. -/
theorem suff (h : Filter.Tendsto (fun n : ℕ => ∑ t ∈ R n, (1 : ℝ) / t) Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun n : ℕ => partialSum n) Filter.atTop Filter.atTop :=
  Filter.tendsto_atTop_mono dom h

end E460Rough


namespace E460Avg
open Finset

/-- Among `q·P` consecutive integers, exactly `q·φ(P)` are coprime to `P`. -/
lemma count_shift (P a q : ℕ) : #{x ∈ Ico a (a + q * P) | P.Coprime x} = q * P.totient := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show a + (q + 1) * P = (a + q * P) + P by ring,
      ← Finset.Ico_union_Ico_eq_Ico (b := a + q * P) (by omega) (by omega), Finset.filter_union,
      Finset.card_union_of_disjoint
        (Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive _ _ _)),
      ih, Nat.filter_coprime_Ico_eq_totient]
    ring

/-- Shifted version: `n - t` runs over a complete block as `n` does (`t ≤ N`). -/
lemma block_count (P q N t : ℕ) (hNt : t ≤ N) :
    #{n ∈ Ico N (N + q * P) | P.Coprime (n - t)} = q * P.totient := by
  rw [← count_shift P (N - t) q]
  apply Finset.card_nbij' (fun n => n - t) (fun x => x + t)
  · intro n hn
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Ico] at hn ⊢
    exact ⟨⟨by omega, by omega⟩, hn.2⟩
  · intro x hx
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Ico] at hx ⊢
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [Nat.add_sub_cancel]; exact hx.2
  · intro n hn
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Ico] at hn
    show n - t + t = n
    omega
  · intro x _
    show x + t - t = x
    omega

/-- The rough condition is coprimality with the primorial. -/
lemma rough_iff (t m : ℕ) : (∀ p : ℕ, p.Prime → p ∣ m → t < p) ↔ (primorial t).Coprime m := by
  unfold primorial
  rw [Nat.coprime_prod_left_iff]
  constructor
  · intro h p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    exact (Nat.Prime.coprime_iff_not_dvd hp.2).mpr (fun hd => by have := h p hp.2 hd; omega)
  · intro h p hp hd
    by_contra hle
    have := h p (by simp only [Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hp⟩)
    exact (Nat.Prime.coprime_iff_not_dvd hp).mp this hd

lemma primorial_dvd {s t : ℕ} (h : s ≤ t) : primorial s ∣ primorial t := by
  unfold primorial
  apply Finset.prod_dvd_prod_of_subset
  intro p
  simp only [Finset.mem_filter, Finset.mem_range]
  intro hp
  exact ⟨by omega, hp.2⟩

/-- **Finite averaging lemma.** Over any block of `P_T` consecutive `n ≥ T`, the truncated rough sum
`∑_{1 ≤ t ≤ T, P_t ⊥ n - t} 1/t` has total `∑_t (P_T / P_t) φ(P_t) / t`, i.e. mean
`∑_t (φ(P_t)/P_t)/t`. -/
theorem mean (T N : ℕ) (hNT : T ≤ N) :
    ∑ n ∈ Ico N (N + primorial T), ∑ t ∈ Icc 1 T,
      (if (primorial t).Coprime (n - t) then (1 : ℝ) / t else 0)
    = ∑ t ∈ Icc 1 T, (((primorial T / primorial t) * (primorial t).totient : ℕ) : ℝ) / t := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t ht => ?_
  have htT : t ≤ T := (Finset.mem_Icc.mp ht).2
  have hdvd : primorial t ∣ primorial T := primorial_dvd htT
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have hL : N + primorial T = N + (primorial T / primorial t) * primorial t := by
    rw [Nat.div_mul_cancel hdvd]
  rw [hL, block_count _ _ _ _ (by omega)]
  ring

end E460Avg


namespace E460Limsup
open Finset E460Rough E460Avg OMA.S_erdos_460

/-- In every block of `P_T` consecutive `n > T` some `n` has `partialSum n` at least the mean
`(∑_{1≤t≤T} (P_T/P_t) φ(P_t) / t) / P_T = ∑_{1≤t≤T} (φ(P_t)/P_t)/t`. -/
theorem exists_large (T N : ℕ) (hNT : T < N) :
    ∃ n ∈ Ico N (N + primorial T),
      (∑ t ∈ Icc 1 T, (((primorial T / primorial t) * (primorial t).totient : ℕ) : ℝ) / t)
        / (primorial T : ℝ) ≤ partialSum n := by
  have hL : 0 < primorial T := primorial_pos T
  have hne : (Ico N (N + primorial T)).Nonempty := ⟨N, by simp [hL]⟩
  have hsum := mean T N hNT.le
  obtain ⟨n, hn, hle⟩ := Finset.exists_le_of_sum_le hne
    (f := fun _ => (∑ t ∈ Icc 1 T, (((primorial T / primorial t) * (primorial t).totient : ℕ) : ℝ) / t)
        / (primorial T : ℝ))
    (g := fun n => ∑ t ∈ Icc 1 T, (if (primorial t).Coprime (n - t) then (1 : ℝ) / t else 0)) (by
      rw [hsum, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.add_sub_cancel_left]
      field_simp
      exact le_rfl)
  refine ⟨n, hn, le_trans hle (le_trans ?_ (dom n))⟩
  have hnN : N ≤ n := (Finset.mem_Ico.mp hn).1
  show ∑ t ∈ Icc 1 T, (if (primorial t).Coprime (n - t) then (1 : ℝ) / t else 0) ≤ _
  rw [← Finset.sum_filter]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_Icc] at ht
    classical
    simp only [R, Finset.mem_filter, Finset.mem_Ico]
    exact ⟨⟨ht.1.1, by omega⟩, (rough_iff t (n - t)).mpr ht.2⟩
  · intro t _ _
    positivity

end E460Limsup


namespace E460Cond
open Finset E460Rough E460Avg E460Limsup OMA.S_erdos_460

/-- `C T = ∑_{1≤t≤T} (φ(P_t)/P_t)/t`, the exact block mean of the truncated rough sum. -/
noncomputable def C (T : ℕ) : ℝ :=
  ∑ t ∈ Icc 1 T, ((primorial t).totient : ℝ) / (primorial t : ℝ) / (t : ℝ)

lemma C_eq (T : ℕ) :
    (∑ t ∈ Icc 1 T, (((primorial T / primorial t) * (primorial t).totient : ℕ) : ℝ) / t)
      / (primorial T : ℝ) = C T := by
  unfold C
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun t ht => ?_
  have hdvd : primorial t ∣ primorial T := primorial_dvd (Finset.mem_Icc.mp ht).2
  have hPt : (primorial t : ℝ) ≠ 0 := by exact_mod_cast (primorial_pos t).ne'
  have hPT : (primorial T : ℝ) ≠ 0 := by exact_mod_cast (primorial_pos T).ne'
  rw [Nat.cast_mul, Nat.cast_div hdvd hPt]
  field_simp

/-- **Conditional lim sup theorem.** If `C T → ∞`, then for every bound `B`, infinitely many `n`
have `partialSum n ≥ B`, i.e. `limsup partialSum = ∞`. (Not uniform divergence.) -/
theorem limsup_of_C (hC : Filter.Tendsto C Filter.atTop Filter.atTop) (B : ℝ) :
    ∃ᶠ n in Filter.atTop, B ≤ partialSum n := by
  obtain ⟨T, hT⟩ := (hC.eventually_ge_atTop B).exists
  rw [Filter.frequently_atTop]
  intro N
  obtain ⟨n, hn, hle⟩ := exists_large T (max N (T + 1)) (by omega)
  refine ⟨n, ?_, ?_⟩
  · have := (Finset.mem_Ico.mp hn).1; omega
  · rw [C_eq] at hle; linarith

/-- The exact analytic input still missing (Mertens-type lower bound), stated as a `Prop`. -/
def MertensLower : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ t : ℕ, 2 ≤ t → c / Real.log t ≤ ((primorial t).totient : ℝ) / (primorial t : ℝ)

end E460Cond


namespace E460Mertens
open Finset Filter E460Cond
open scoped Topology

/-- `f n = 1 / ((n+1) log (n+1))`. -/
noncomputable def f (n : ℕ) : ℝ := 1 / (((n : ℝ) + 1) * Real.log ((n : ℝ) + 1))

lemma f_nonneg (n : ℕ) : 0 ≤ f n := by
  unfold f
  have : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  positivity

lemma f_anti : ∀ ⦃m n : ℕ⦄, 0 < m → m ≤ n → f n ≤ f m := by
  intro m n hm hmn
  unfold f
  have h1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have h2 : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hm' : (2 : ℝ) ≤ (m : ℝ) + 1 := by linarith
  have hmn' : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by linarith
  have hl : 0 < Real.log ((m : ℝ) + 1) := Real.log_pos (by linarith)
  have hl2 : Real.log ((m : ℝ) + 1) ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log (by linarith) hmn'
  apply one_div_le_one_div_of_le (by positivity)
  exact mul_le_mul hmn' hl2 hl.le (by linarith)

/-- Condensed terms dominate a harmonic series. -/
lemma condensed_ge (k : ℕ) : 1 / (2 * Real.log 2) * (1 / ((k : ℝ) + 1)) ≤ (2 : ℝ) ^ k * f (2 ^ k) := by
  unfold f
  push_cast
  have hp : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA : (2 : ℝ) ^ k + 1 ≤ 2 ^ (k + 1) := by rw [pow_succ]; linarith
  have hL : Real.log ((2 : ℝ) ^ k + 1) ≤ ((k : ℝ) + 1) * Real.log 2 := by
    calc Real.log ((2 : ℝ) ^ k + 1) ≤ Real.log ((2 : ℝ) ^ (k + 1)) := Real.log_le_log (by positivity) hA
      _ = ((k : ℝ) + 1) * Real.log 2 := by rw [Real.log_pow]; push_cast; ring
  have hLpos : 0 < Real.log ((2 : ℝ) ^ k + 1) := Real.log_pos (by linarith)
  have hden : ((2 : ℝ) ^ k + 1) * Real.log ((2 : ℝ) ^ k + 1) ≤ 2 ^ (k + 1) * (((k : ℝ) + 1) * Real.log 2) :=
    mul_le_mul hA hL hLpos.le (by positivity)
  rw [one_div_mul_one_div, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  calc 1 * (((2 : ℝ) ^ k + 1) * Real.log ((2 : ℝ) ^ k + 1))
      ≤ 2 ^ (k + 1) * (((k : ℝ) + 1) * Real.log 2) := by linarith
    _ = 2 ^ k * (2 * Real.log 2 * ((k : ℝ) + 1)) := by rw [pow_succ]; ring

/-- Divergence of `∑ 1/(t log t)` via Cauchy condensation (kept as a second proof). -/
theorem f_tendsto_condensation : Tendsto (fun N : ℕ => ∑ n ∈ range N, f n) atTop atTop := by
  rw [← not_summable_iff_tendsto_nat_atTop_of_nonneg f_nonneg]
  intro hs
  have hc := (summable_condensed_iff_of_nonneg f_nonneg f_anti).mpr hs
  have hh : Summable (fun k : ℕ => 1 / (2 * Real.log 2) * (1 / ((k : ℝ) + 1))) :=
    Summable.of_nonneg_of_le (fun k => by
      have : 0 < Real.log 2 := Real.log_pos (by norm_num); positivity) condensed_ge hc
  have hh2 : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1)) := by
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    refine (hh.mul_left (2 * Real.log 2)).congr fun k => ?_
    field_simp
  apply Real.not_summable_one_div_natCast
  apply (summable_nat_add_iff 1).mp
  refine hh2.congr fun k => ?_
  push_cast; ring

/-- `g x = 1 / (x log x)`. -/
noncomputable def g (x : ℝ) : ℝ := 1 / (x * Real.log x)

lemma g_anti (N : ℕ) : AntitoneOn g (Set.Icc 2 (2 + N)) := by
  intro x hx y hy hxy
  simp only [Set.mem_Icc] at hx hy
  unfold g
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hl : Real.log x ≤ Real.log y := Real.log_le_log (by linarith) hxy
  apply one_div_le_one_div_of_le (mul_pos (by linarith) hlx)
  exact mul_le_mul hxy hl hlx.le (by linarith)

/-- `∫₂^{2+N} dx/(x log x) = log log (2+N) − log log 2`. -/
lemma integral_g (N : ℕ) :
    ∫ x in (2 : ℝ)..(2 + N), g x = Real.log (Real.log (2 + N)) - Real.log (Real.log 2) := by
  have hN : (2 : ℝ) ≤ 2 + N := by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => Real.log (Real.log x)) ?_ ?_
  · intro x hx
    rw [Set.uIcc_of_le hN] at hx
    have hx2 : 2 ≤ x := hx.1
    have hl : Real.log x ≠ 0 := (Real.log_pos (by linarith)).ne'
    have hd := (Real.hasDerivAt_log (by linarith : x ≠ 0)).log hl
    have hx0 : x ≠ 0 := by linarith
    have hg : g x = x⁻¹ / Real.log x := by unfold g; field_simp
    rw [hg]; exact hd
  · apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hN]
    apply ContinuousOn.div continuousOn_const
    · exact continuousOn_id.mul (Real.continuousOn_log.mono (fun x hx => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        have := hx.1; intro h; rw [h] at this; norm_num at this))
    · intro x hx
      have h1 : 0 < Real.log x := Real.log_pos (by linarith [hx.1])
      have h2 : 0 < x := by linarith [hx.1]
      positivity

/-- **Divergence of `∑_{t≥2} 1/(t log t)` by integral comparison.** -/
theorem f_tendsto : Tendsto (fun N : ℕ => ∑ n ∈ range N, f n) atTop atTop := by
  have hsum : ∀ N : ℕ, Real.log (Real.log (2 + N)) - Real.log (Real.log 2) ≤
      ∑ n ∈ range (N + 1), f n := by
    intro N
    rw [← integral_g N]
    refine ((g_anti N).integral_le_sum).trans (le_of_eq ?_)
    rw [Finset.sum_range_succ']
    have h0 : f 0 = 0 := by simp [f]
    rw [h0, add_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [g, f]
    rw [show ((i + 1 : ℕ) : ℝ) + 1 = 2 + (i : ℝ) by push_cast; ring]
  have hlim : Tendsto (fun N : ℕ => Real.log (Real.log (2 + N)) - Real.log (Real.log 2)) atTop atTop := by
    have h := Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp
      (tendsto_atTop_add_const_left _ 2 tendsto_natCast_atTop_atTop))
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right _ (-Real.log (Real.log 2)) h
  exact (tendsto_add_atTop_iff_nat 1).mp (tendsto_atTop_mono hsum hlim)

/-- `MertensLower → C T → ∞`. -/
theorem C_tendsto (h : MertensLower) : Tendsto C atTop atTop := by
  obtain ⟨c, hc, hb⟩ := h
  have hle : ∀ T : ℕ, c * ∑ n ∈ range T, f n ≤ C T := by
    intro T
    unfold C
    rw [Finset.mul_sum]
    have hre : ∑ t ∈ Icc 1 T, ((primorial t).totient : ℝ) / (primorial t : ℝ) / (t : ℝ) =
        ∑ n ∈ range T, ((primorial (n + 1)).totient : ℝ) / (primorial (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) := by
      clear hb
      induction T with
      | zero => simp
      | succ T ih => rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]
    rw [hre]
    refine Finset.sum_le_sum fun n _ => ?_
    unfold f
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Nat.cast_zero, zero_add, Real.log_one, mul_zero, div_zero, mul_zero]
      positivity
    · have h2 : 2 ≤ n + 1 := by omega
      have hb' := hb (n + 1) h2
      have hl : 0 < Real.log ((n : ℝ) + 1) := Real.log_pos (by
        have : (1 : ℝ) ≤ n := by exact_mod_cast hn
        linarith)
      push_cast at hb' ⊢
      have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      calc c * (1 / (((n : ℝ) + 1) * Real.log ((n : ℝ) + 1)))
          = c / Real.log ((n : ℝ) + 1) / ((n : ℝ) + 1) := by field_simp
        _ ≤ _ := div_le_div_of_nonneg_right hb' hpos.le
  exact tendsto_atTop_mono hle (Tendsto.const_mul_atTop hc f_tendsto)

/-- **Conditional lim sup for Erdős 460**, with `MertensLower` as the only premise. -/
theorem limsup_of_mertens (h : MertensLower) (B : ℝ) :
    ∃ᶠ n in atTop, B ≤ OMA.S_erdos_460.partialSum n :=
  limsup_of_C (C_tendsto h) B

end E460Mertens



namespace E460Mertens1
open Finset Chebyshev

lemma prod_Ioc_eq_factorial (n : ℕ) : ∏ x ∈ Ioc 0 n, x = n.factorial := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.prod_Ioc_succ_top (by omega), ih, Nat.factorial_succ]; ring

/-- The primes of `s` dividing `m > 0` have log-sum at most `log m`. -/
lemma sum_log_primes_dvd (m : ℕ) (hm : 0 < m) (s : Finset ℕ) :
    ∑ p ∈ s.filter (fun p => p.Prime ∧ p ∣ m), Real.log p ≤ Real.log m := by
  set F := s.filter (fun p => p.Prime ∧ p ∣ m)
  have hdvd : ∏ p ∈ F, p ∣ m :=
    Finset.prod_primes_dvd m (fun p hp => (mem_filter.mp hp).2.1.prime) (fun p hp => (mem_filter.mp hp).2.2)
  have hpos : 0 < ∏ p ∈ F, p := Finset.prod_pos (fun p hp => (mem_filter.mp hp).2.1.pos)
  have hle : ∏ p ∈ F, p ≤ m := Nat.le_of_dvd hm hdvd
  calc ∑ p ∈ F, Real.log p = Real.log (∏ p ∈ F, (p : ℝ)) :=
        (Real.log_prod (fun p hp => Nat.cast_ne_zero.mpr (mem_filter.mp hp).2.1.ne_zero)).symm
    _ = Real.log ((∏ p ∈ F, p : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ Real.log m := Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hle)

/-- Weak Legendre: `∑_{p ≤ n} ⌊n/p⌋ log p ≤ log n!` (double counting). -/
lemma legendre_weak (n : ℕ) :
    ∑ p ∈ Nat.primesLE n, ((n / p : ℕ) : ℝ) * Real.log p ≤ Real.log n.factorial := by
  have hcard : ∀ p ∈ Nat.primesLE n,
      ((n / p : ℕ) : ℝ) * Real.log p =
        ∑ m ∈ Ioc 0 n, (if p.Prime ∧ p ∣ m then Real.log p else 0) := by
    intro p hp
    have hpr : p.Prime := (Nat.mem_primesBelow.mp hp).2
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    congr 2
    rw [← Nat.Ioc_filter_dvd_card_eq_div n p]
    congr 1
    apply filter_congr
    intro m _
    simp [hpr]
  rw [Finset.sum_congr rfl hcard, Finset.sum_comm]
  calc ∑ m ∈ Ioc 0 n, ∑ p ∈ Nat.primesLE n, (if p.Prime ∧ p ∣ m then Real.log p else 0)
      ≤ ∑ m ∈ Ioc 0 n, Real.log m := by
        refine Finset.sum_le_sum fun m hm => ?_
        rw [← Finset.sum_filter]
        exact sum_log_primes_dvd m (Finset.mem_Ioc.mp hm).1 _
    _ = Real.log ((∏ m ∈ Ioc 0 n, m : ℕ) : ℝ) := by
        push_cast
        rw [Real.log_prod]
        intro m hm; exact Nat.cast_ne_zero.mpr (Finset.mem_Ioc.mp hm).1.ne'
    _ = Real.log n.factorial := by rw [prod_Ioc_eq_factorial]

/-- **Mertens-type bound.** `∑_{p ≤ n} (log p)/p ≤ log n + log 4` for `n ≥ 1`. -/
theorem mertens1 (n : ℕ) (hn : 1 ≤ n) :
    ∑ p ∈ Nat.primesLE n, Real.log p / p ≤ Real.log n + Real.log 4 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hθ : ∑ p ∈ Nat.primesLE n, Real.log p ≤ Real.log 4 * n := by
    rw [← theta_eq_sum_primesLE_log]; exact theta_le_log4_mul_x (Nat.cast_nonneg n)
  have hfl : ∀ p ∈ Nat.primesLE n, (n : ℝ) * (Real.log p / p) ≤
      ((n / p : ℕ) : ℝ) * Real.log p + Real.log p := by
    intro p hp
    have hpr : p.Prime := (Nat.mem_primesBelow.mp hp).2
    have hpR : (0 : ℝ) < p := by exact_mod_cast hpr.pos
    have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpr.one_lt.le)
    have h1 : (n : ℝ) ≤ p * (((n / p : ℕ) : ℝ) + 1) := by
      have := Nat.lt_mul_div_succ n hpr.pos
      exact_mod_cast this.le
    have h2 : (n : ℝ) / p ≤ ((n / p : ℕ) : ℝ) + 1 := by rw [div_le_iff₀ hpR]; linarith
    calc (n : ℝ) * (Real.log p / p) = ((n : ℝ) / p) * Real.log p := by ring
      _ ≤ (((n / p : ℕ) : ℝ) + 1) * Real.log p := mul_le_mul_of_nonneg_right h2 hl
      _ = _ := by ring
  have hfact : Real.log n.factorial ≤ n * Real.log n := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by exact_mod_cast Nat.factorial_pos n) (by exact_mod_cast Nat.factorial_le_pow n)
  have hsum : (n : ℝ) * ∑ p ∈ Nat.primesLE n, Real.log p / p ≤ n * Real.log n + n * Real.log 4 := by
    rw [Finset.mul_sum]
    calc ∑ p ∈ Nat.primesLE n, (n : ℝ) * (Real.log p / p)
        ≤ ∑ p ∈ Nat.primesLE n, (((n / p : ℕ) : ℝ) * Real.log p + Real.log p) := Finset.sum_le_sum hfl
      _ = ∑ p ∈ Nat.primesLE n, ((n / p : ℕ) : ℝ) * Real.log p + ∑ p ∈ Nat.primesLE n, Real.log p :=
          Finset.sum_add_distrib
      _ ≤ n * Real.log n + Real.log 4 * n := add_le_add ((legendre_weak n).trans hfact) hθ
      _ = _ := by ring
  have := (mul_le_mul_iff_of_pos_left hnR).mp (by linarith [hsum] : (n : ℝ) * ∑ p ∈ Nat.primesLE n, Real.log p / p ≤ n * (Real.log n + Real.log 4))
  exact this

end E460Mertens1


namespace E460EulerRatio
open Finset E460Mertens1

lemma ratio_nonneg (p : ℕ) (hp : 2 ≤ p) (δ : ℝ) (hδ : 0 ≤ δ) :
    0 ≤ (1 - (p : ℝ) ^ (-1 - δ)) / (1 - 1 / p) := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  apply div_nonneg
  · have := Real.rpow_le_one_of_one_le_of_nonpos (by linarith : (1 : ℝ) ≤ p) (by linarith : -1 - δ ≤ 0)
    linarith
  · have : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith

/-- Each Euler factor ratio is at most `exp(2δ log p / p)`. -/
lemma ratio_le (p : ℕ) (hp : 2 ≤ p) (δ : ℝ) (hδ : 0 ≤ δ) :
    (1 - (p : ℝ) ^ (-1 - δ)) / (1 - 1 / p) ≤ Real.exp (2 * δ * Real.log p / p) := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hpne : (p : ℝ) ≠ 0 := by linarith
  have hl : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  set q := (p : ℝ) ^ (-δ) with hq
  have hpow : (p : ℝ) ^ (-1 - δ) = q / p := by
    rw [show (-1 - δ) = -δ + (-1) by ring, Real.rpow_add hp0, Real.rpow_neg_one, ← hq]
    field_simp
  have hqexp : q = Real.exp (-(δ * Real.log p)) := by
    rw [hq, Real.rpow_def_of_pos hp0]; ring_nf
  have hq1 : 1 - δ * Real.log p ≤ q := by
    rw [hqexp]; linarith [Real.add_one_le_exp (-(δ * Real.log p))]
  have hratio : (1 - (p : ℝ) ^ (-1 - δ)) / (1 - 1 / p) = 1 + (1 - q) / (p - 1) := by
    rw [hpow]; field_simp; ring
  rw [hratio]
  have hdl : 0 ≤ δ * Real.log p := mul_nonneg hδ hl
  have hy : (1 - q) / (p - 1) ≤ 2 * δ * Real.log p / p := by
    rw [div_le_div_iff₀ (by linarith) hp0]
    calc (1 - q) * p ≤ (δ * Real.log p) * p := mul_le_mul_of_nonneg_right (by linarith) hp0.le
      _ ≤ (δ * Real.log p) * (2 * (p - 1)) := mul_le_mul_of_nonneg_left (by linarith) hdl
      _ = 2 * δ * Real.log p * (p - 1) := by ring
  calc 1 + (1 - q) / (p - 1) ≤ 1 + 2 * δ * Real.log p / p := by linarith
    _ ≤ Real.exp (2 * δ * Real.log p / p) := by
        linarith [Real.add_one_le_exp (2 * δ * Real.log p / p)]

/-- **Euler-product ratio bound.** For `n ≥ 2` and `δ = 1/log n`,
`∏_{p≤n} (1 − p^(−1−δ))/(1 − 1/p) ≤ exp 6`. -/
theorem prod_le (n : ℕ) (hn : 2 ≤ n) :
    ∏ p ∈ Nat.primesLE n, (1 - (p : ℝ) ^ (-1 - 1 / Real.log n)) / (1 - 1 / p) ≤ Real.exp 6 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hln : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hnR
  have hlnpos : 0 < Real.log n := lt_of_lt_of_le hl2 hln
  set δ := 1 / Real.log n with hδdef
  have hδ : 0 ≤ δ := by positivity
  have hp2 : ∀ p ∈ Nat.primesLE n, 2 ≤ p := fun p hp => (Nat.mem_primesBelow.mp hp).2.two_le
  have hM := mertens1 n (by omega)
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  calc ∏ p ∈ Nat.primesLE n, (1 - (p : ℝ) ^ (-1 - δ)) / (1 - 1 / p)
      ≤ ∏ p ∈ Nat.primesLE n, Real.exp (2 * δ * Real.log p / p) :=
        Finset.prod_le_prod (fun p hp => ratio_nonneg p (hp2 p hp) δ hδ)
          (fun p hp => ratio_le p (hp2 p hp) δ hδ)
    _ = Real.exp (∑ p ∈ Nat.primesLE n, 2 * δ * Real.log p / p) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp 6 := by
        apply Real.exp_le_exp.mpr
        have hs : ∑ p ∈ Nat.primesLE n, 2 * δ * Real.log p / p =
            2 * δ * ∑ p ∈ Nat.primesLE n, Real.log p / p := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun p _ => by ring
        rw [hs]
        have h1 : 2 * δ * ∑ p ∈ Nat.primesLE n, Real.log p / p ≤ 2 * δ * (Real.log n + Real.log 4) :=
          mul_le_mul_of_nonneg_left hM (by positivity)
        have h2 : 2 * δ * (Real.log n + Real.log 4) = 2 + 2 * Real.log 4 / Real.log n := by
          rw [hδdef]; field_simp
        have h3 : 2 * Real.log 4 / Real.log n ≤ 4 := by
          rw [div_le_iff₀ hlnpos, h4]; linarith
        linarith

end E460EulerRatio


namespace E460Zeta
open Finset

/-- `m ↦ m^(−s)` as a multiplicative map. -/
noncomputable def fs (s : ℝ) : ℕ →* ℝ where
  toFun n := (n : ℝ) ^ (-s)
  map_one' := by simp
  map_mul' m n := by push_cast; exact Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)

/-- Finite Euler product = sum over `(n+1)`-smooth numbers. -/
lemma prod_hasSum (s : ℝ) (hs : 1 < s) (n : ℕ) :
    HasSum (fun m : (n + 1).smoothNumbers => ((m : ℕ) : ℝ) ^ (-s))
      (∏ p ∈ Nat.primesLE n, (1 - (p : ℝ) ^ (-s))⁻¹) := by
  have h := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
    (f := fs s) (fun {p} hp => by
      show ‖(p : ℝ) ^ (-s)‖ < 1
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)) (n + 1)).2
  exact h

/-- `∑_{i<a} (i+2)^(−s) ≤ 1/(s−1)` by integral comparison. -/
lemma psum_le (s : ℝ) (hs : 1 < s) (a : ℕ) : ∑ i ∈ range a, ((i : ℝ) + 2) ^ (-s) ≤ 1 / (s - 1) := by
  have ha : (1 : ℝ) ≤ 1 + a := by linarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a)]
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-s)) (Set.Icc 1 (1 + a)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by linarith)
  have hsum := hanti.sum_le_integral
  have hint : ∫ x in (1 : ℝ)..(1 + a), x ^ (-s) = ((1 + a) ^ (-s + 1) - 1 ^ (-s + 1)) / (-s + 1) := by
    apply integral_rpow
    right
    refine ⟨by linarith, ?_⟩
    rw [Set.uIcc_of_le ha]
    intro h0; linarith [h0.1]
  rw [hint] at hsum
  have hpos : 0 ≤ (1 + (a : ℝ)) ^ (-s + 1) := by positivity
  have hb : ((1 + (a : ℝ)) ^ (-s + 1) - 1 ^ (-s + 1)) / (-s + 1) ≤ 1 / (s - 1) := by
    rw [Real.one_rpow, show -s + 1 = -(s - 1) by ring, div_neg, ← neg_div]
    have hpos' : 0 ≤ (1 + (a : ℝ)) ^ (-(s - 1)) := by positivity
    apply div_le_div_of_nonneg_right _ (by linarith)
    linarith
  calc ∑ i ∈ range a, ((i : ℝ) + 2) ^ (-s)
      = ∑ i ∈ range a, (1 + ((i + 1 : ℕ) : ℝ)) ^ (-s) := by
        refine Finset.sum_congr rfl fun i _ => ?_; push_cast; ring_nf
    _ ≤ _ := hsum
    _ ≤ 1 / (s - 1) := hb

/-- `∑_{m ≥ 0} m^(−s) ≤ 1 + 1/(s−1)` (the `m = 0` term is `0`). -/
lemma tsum_le (s : ℝ) (hs : 1 < s) : ∑' m : ℕ, ((m : ℝ) ^ (-s)) ≤ 1 + 1 / (s - 1) := by
  apply Real.tsum_le_of_sum_range_le (fun m => by positivity)
  intro N
  calc ∑ m ∈ range N, ((m : ℝ) ^ (-s))
      ≤ ∑ m ∈ range (N + 2), ((m : ℝ) ^ (-s)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
          (fun _ _ _ => by positivity)
    _ = ∑ i ∈ range N, ((i : ℝ) + 2) ^ (-s) + 1 := by
        rw [Finset.sum_range_succ', Finset.sum_range_succ']
        simp only [Nat.cast_zero, zero_add, Real.zero_rpow (by linarith : -s ≠ 0), Nat.cast_one,
          Real.one_rpow, add_zero]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_; push_cast; ring_nf
    _ ≤ 1 / (s - 1) + 1 := by linarith [psum_le s hs N]
    _ = 1 + 1 / (s - 1) := by ring

/-- **Finite Euler product bound.** For real `s > 1` and every `n`,
`∏_{p≤n} (1 − p^(−s))⁻¹ ≤ 1 + 1/(s − 1)`. -/
theorem finite_euler_le (s : ℝ) (hs : 1 < s) (n : ℕ) :
    ∏ p ∈ Nat.primesLE n, (1 - (p : ℝ) ^ (-s))⁻¹ ≤ 1 + 1 / (s - 1) := by
  rw [← (prod_hasSum s hs n).tsum_eq]
  have hsum : Summable (fun m : ℕ => ((m : ℝ) ^ (-s))) := Real.summable_nat_rpow.mpr (by linarith)
  exact (tsum_comp_le_tsum_of_inj hsum (fun m => by positivity) Subtype.val_injective).trans
    (tsum_le s hs)

end E460Zeta


namespace E460Final
open Finset E460Cond E460EulerRatio E460Zeta

/-- `φ(P_t)/P_t = ∏_{p≤t} (1 − 1/p)`. -/
lemma totient_ratio (t : ℕ) :
    ((primorial t).totient : ℝ) / (primorial t : ℝ) = ∏ p ∈ Nat.primesLE t, (1 - 1 / (p : ℝ)) := by
  have hq := Nat.totient_eq_mul_prod_factors (primorial t)
  rw [primeFactors_primorial] at hq
  have hr : ((primorial t).totient : ℝ) = (primorial t : ℝ) * ∏ p ∈ Nat.primesLE t, (1 - (p : ℝ)⁻¹) := by
    have := congrArg (fun x : ℚ => (x : ℝ)) hq
    push_cast at this
    exact this
  have hP : (primorial t : ℝ) ≠ 0 := by exact_mod_cast (primorial_pos t).ne'
  rw [hr, mul_div_cancel_left₀ _ hP]
  simp only [one_div]

/-- **MertensLower holds** with `c = e^{−6} / (1 + 1/log 2)`. -/
theorem mertens_lower : MertensLower := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨Real.exp (-6) / (1 + 1 / Real.log 2), by positivity, fun t ht => ?_⟩
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have hL2 : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) htR
  have hL : 0 < Real.log t := lt_of_lt_of_le hl2 hL2
  set δ := 1 / Real.log t with hδ
  have hδpos : 0 < δ := by positivity
  have hp2 : ∀ p ∈ Nat.primesLE t, 2 ≤ p := fun p hp => (Nat.mem_primesBelow.mp hp).2.two_le
  -- the two checked bounds
  have hE : ∏ p ∈ Nat.primesLE t, (1 - (p : ℝ) ^ (-(1 + δ)))⁻¹ ≤ 1 + Real.log t := by
    have := finite_euler_le (1 + δ) (by linarith) t
    rwa [show 1 + δ - 1 = δ by ring, hδ, one_div_one_div] at this
  have hR := prod_le t ht
  rw [← hδ] at hR
  -- split ∏ (1 − 1/p)⁻¹
  have hsplit : ∏ p ∈ Nat.primesLE t, (1 - 1 / (p : ℝ))⁻¹ =
      (∏ p ∈ Nat.primesLE t, (1 - (p : ℝ) ^ (-(1 + δ)))⁻¹) *
        ∏ p ∈ Nat.primesLE t, (1 - (p : ℝ) ^ (-1 - δ)) / (1 - 1 / p) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp2 p hp
    have hlt : (p : ℝ) ^ (-1 - δ) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
    have h1 : 1 - (p : ℝ) ^ (-1 - δ) ≠ 0 := by linarith
    have h2 : 1 - 1 / (p : ℝ) ≠ 0 := by
      have : 1 / (p : ℝ) ≤ 1 / 2 := by rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
      linarith
    rw [show -(1 + δ) = -1 - δ by ring]
    field_simp
  set X := ∏ p ∈ Nat.primesLE t, (1 - 1 / (p : ℝ)) with hX
  have hXpos : 0 < X := Finset.prod_pos (fun p hp => by
    have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp2 p hp
    have : 1 / (p : ℝ) ≤ 1 / 2 := by rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    linarith)
  have hRnn : 0 ≤ ∏ p ∈ Nat.primesLE t, (1 - (p : ℝ) ^ (-1 - δ)) / (1 - 1 / p) :=
    Finset.prod_nonneg (fun p hp => ratio_nonneg p (hp2 p hp) δ hδpos.le)
  have hXinv : X⁻¹ ≤ (1 + Real.log t) * Real.exp 6 := by
    rw [hX, ← Finset.prod_inv_distrib, hsplit]
    exact mul_le_mul hE hR hRnn (by positivity)
  have hXlow : 1 / ((1 + Real.log t) * Real.exp 6) ≤ X := by
    rw [div_le_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hXinv hXpos.le
    rw [mul_inv_cancel₀ hXpos.ne'] at this
    linarith
  rw [totient_ratio t, ← hX]
  refine le_trans ?_ hXlow
  have hkey : 1 + Real.log t ≤ (1 + 1 / Real.log 2) * Real.log t := by
    have : 1 ≤ Real.log t / Real.log 2 := by rw [le_div_iff₀ hl2]; linarith
    have e : (1 + 1 / Real.log 2) * Real.log t = Real.log t + Real.log t / Real.log 2 := by
      field_simp
    linarith
  rw [div_div, Real.exp_neg, show 1 / ((1 + Real.log t) * Real.exp 6) = (Real.exp 6)⁻¹ / (1 + Real.log t) by
    field_simp]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) hkey

/-- **Erdős 460, unbounded lim sup (assumption-free).** For every `B`, infinitely many `n` have
`partialSum n ≥ B`. This is NOT uniform divergence (`OMA.S_erdos_460.main`). -/
theorem limsup_unbounded (B : ℝ) : ∃ᶠ n in Filter.atTop, B ≤ OMA.S_erdos_460.partialSum n :=
  E460Mertens.limsup_of_mertens mertens_lower B

end E460Final


namespace E460Gap
open Finset Filter E460Rough E460Avg E460Limsup E460Cond E460Final OMA.S_erdos_460

/-- The truncated rough sum `S_T(n)`. -/
noncomputable def ST (T n : ℕ) : ℝ :=
  ∑ t ∈ Icc 1 T, (if (primorial t).Coprime (n - t) then (1 : ℝ) / t else 0)

lemma trunc_le (T n : ℕ) (hn : T < n) : ST T n ≤ partialSum n := by
  classical
  refine le_trans ?_ (dom n)
  unfold ST
  rw [← Finset.sum_filter]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_Icc] at ht
    simp only [R, Finset.mem_filter, Finset.mem_Ico]
    exact ⟨⟨ht.1.1, by omega⟩, (rough_iff t (n - t)).mpr ht.2⟩
  · intro t _ _; positivity

lemma ST_periodic (T n : ℕ) (hn : T ≤ n) : ST T (n + primorial T) = ST T n := by
  unfold ST
  refine Finset.sum_congr rfl fun t ht => ?_
  have htT : t ≤ T := (Finset.mem_Icc.mp ht).2
  obtain ⟨q, hq⟩ := primorial_dvd htT
  have e : n + primorial T - t = (n - t) + q * primorial t := by
    rw [hq, Nat.mul_comm (primorial t) q]; omega
  simp only [e, Nat.coprime_add_mul_right_right]

lemma ST_periodic_mul (T n k : ℕ) (hn : T ≤ n) : ST T (n + k * primorial T) = ST T n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show n + (k + 1) * primorial T = (n + k * primorial T) + primorial T by ring,
      ST_periodic T _ (by omega), ih]

/-- **Bounded gaps.** For every `B` there are `P > 0` and `N₀` such that every interval
`[N, N + P)` with `N ≥ N₀` contains some `n` with `partialSum n ≥ B`. -/
theorem bounded_gap (B : ℝ) :
    ∃ P > 0, ∃ N0, ∀ N ≥ N0, ∃ n ∈ Ico N (N + P), B ≤ partialSum n := by
  obtain ⟨T, hT⟩ := ((E460Mertens.C_tendsto mertens_lower).eventually_ge_atTop B).exists
  refine ⟨primorial T, primorial_pos T, T + 1, fun N hN => ?_⟩
  obtain ⟨n, hn, hle⟩ := exists_large T N (by omega)
  rw [C_eq] at hle
  exact ⟨n, hn, hT.trans hle⟩

/-- **A whole residue class.** For every `B` there are `P > 0` and `n₀` with
`partialSum (n₀ + k·P) ≥ B` for all `k`. -/
theorem residue_class (B : ℝ) :
    ∃ P > 0, ∃ n0, ∀ k : ℕ, B ≤ partialSum (n0 + k * P) := by
  obtain ⟨T, hT⟩ := ((E460Mertens.C_tendsto mertens_lower).eventually_ge_atTop B).exists
  have hL : 0 < primorial T := primorial_pos T
  have hne : (Ico (T + 1) (T + 1 + primorial T)).Nonempty := ⟨T + 1, by simp [hL]⟩
  have hsum := mean T (T + 1) (by omega)
  obtain ⟨n0, hn0, hle⟩ := Finset.exists_le_of_sum_le hne
    (f := fun _ => (∑ t ∈ Icc 1 T, (((primorial T / primorial t) * (primorial t).totient : ℕ) : ℝ) / t)
        / (primorial T : ℝ))
    (g := fun n => ST T n) (by
      unfold ST
      rw [hsum, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.add_sub_cancel_left]
      field_simp
      exact le_rfl)
  have hn0T : T + 1 ≤ n0 := (Finset.mem_Ico.mp hn0).1
  rw [C_eq] at hle
  refine ⟨primorial T, hL, n0, fun k => ?_⟩
  calc B ≤ C T := hT
    _ ≤ ST T n0 := hle
    _ = ST T (n0 + k * primorial T) := (ST_periodic_mul T n0 k (by omega)).symm
    _ ≤ partialSum (n0 + k * primorial T) := trunc_le T _ (by nlinarith [hL])

/-- **Positive lower density (counting form).** For every `B` there are `P > 0` and `n₀` such that
for all `k`, at least `k` of the `n < n₀ + k·P` satisfy `partialSum n ≥ B`. -/
theorem lower_density (B : ℝ) :
    ∃ P > 0, ∃ n0, ∀ k : ℕ, k ≤ #{n ∈ range (n0 + k * P) | B ≤ partialSum n} := by
  classical
  obtain ⟨P, hP, n0, h⟩ := residue_class B
  refine ⟨P, hP, n0, fun k => ?_⟩
  calc k = #((range k).image (fun i => n0 + i * P)) := by
        rw [Finset.card_image_of_injective _ (fun a b hab => by
          have : a * P = b * P := by simpa using hab
          exact Nat.eq_of_mul_eq_mul_right hP this), card_range]
    _ ≤ #{n ∈ range (n0 + k * P) | B ≤ partialSum n} := by
        apply card_le_card
        intro n hn
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
        rw [Finset.mem_range] at hi
        rw [Finset.mem_filter, Finset.mem_range]
        exact ⟨by nlinarith, h i⟩

end E460Gap


namespace E460Obstruction
open Finset E460Rough E460Gap

lemma prime_dvd_primorial {p t : ℕ} (hp : p.Prime) (hpt : p ≤ t) : p ∣ primorial t := by
  unfold primorial
  apply Finset.dvd_prod_of_mem
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, hp⟩

/-- **(1)** If `P_T ∣ n` and `n > T ≥ 1`, the truncated rough sum is exactly `1`. -/
theorem ST_eq_one (T n : ℕ) (hT : 1 ≤ T) (hTn : T < n) (hdvd : primorial T ∣ n) :
    E460Gap.ST T n = 1 := by
  unfold E460Gap.ST
  rw [Finset.sum_eq_single 1]
  · have h1 : primorial 1 = 1 := by decide
    simp [h1]
  · intro t ht ht1
    have ht2 : 2 ≤ t := by have := (Finset.mem_Icc.mp ht).1; omega
    have htT : t ≤ T := (Finset.mem_Icc.mp ht).2
    have hp := Nat.minFac_prime (show t ≠ 1 by omega)
    have hpt : t.minFac ≤ t := Nat.minFac_le (by omega)
    have hpn : t.minFac ∣ n := (prime_dvd_primorial hp (by omega)).trans hdvd
    have hpd : t.minFac ∣ n - t := Nat.dvd_sub hpn (Nat.minFac_dvd t)
    rw [if_neg]
    exact Nat.not_coprime_of_dvd_of_dvd hp.one_lt (prime_dvd_primorial hp hpt) hpd
  · intro h; exact absurd (Finset.mem_Icc.mpr ⟨le_rfl, hT⟩) h

/-- **(2)** If `P_T ∣ n`, every rough offset `t ∈ R n` (any size) is coprime to `P_T`. -/
theorem rough_coprime (T n t : ℕ) (hdvd : primorial T ∣ n) (ht : t ∈ R n) :
    Nat.Coprime (primorial T) t := by
  obtain ⟨h1, h2, h3⟩ := mem_R ht
  apply Nat.coprime_of_dvd
  intro p hp hpP hpt
  have hpn : p ∣ n := hpP.trans hdvd
  have hpd : p ∣ n - t := Nat.dvd_sub hpn hpt
  have hle : p ≤ t := Nat.le_of_dvd (by omega) hpt
  have := h3 p hp hpd
  omega

end E460Obstruction



namespace E460CRT
open Finset

lemma coprime_mod_iff (Q x : ℕ) : Nat.Coprime Q x ↔ Nat.Coprime Q (x % Q) := by
  unfold Nat.Coprime
  rw [Nat.gcd_comm Q (x % Q), ← Nat.gcd_rec]

/-- One block of `Q` consecutive `k`: exactly `φ(Q)` values make `c + k·A` coprime to `Q`. -/
lemma block (A Q c K : ℕ) (hQ : 0 < Q) (hAQ : Nat.Coprime A Q) :
    #{k ∈ Ico K (K + Q) | Nat.Coprime Q (c + k * A)} = Q.totient := by
  set f : ℕ → ℕ := fun k => (c + k * A) % Q with hf
  have hinj : Set.InjOn f (Ico K (K + Q)) := by
    intro k1 h1 k2 h2 h12
    simp only [coe_Ico, Set.mem_Ico] at h1 h2
    have hm : c + k1 * A ≡ c + k2 * A [MOD Q] := h12
    have hm2 : k1 * A ≡ k2 * A [MOD Q] := Nat.ModEq.add_left_cancel' c hm
    have hm3 : k1 ≡ k2 [MOD Q] := Nat.ModEq.cancel_right_of_coprime (by
      rw [Nat.gcd_comm]; exact hAQ) hm2
    obtain ⟨a, rfl⟩ : ∃ a, k1 = K + a := ⟨k1 - K, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, k2 = K + b := ⟨k2 - K, by omega⟩
    have hab : a ≡ b [MOD Q] := Nat.ModEq.add_left_cancel' K hm3
    have := hab
    unfold Nat.ModEq at this
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    omega
  have himg : (Ico K (K + Q)).image f = range Q := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨k, -, rfl⟩ := mem_image.mp hy
      exact mem_range.mpr (Nat.mod_lt _ hQ)
    · rw [card_image_of_injOn hinj, card_range, Nat.card_Ico]; omega
  calc #{k ∈ Ico K (K + Q) | Nat.Coprime Q (c + k * A)}
      = #{k ∈ Ico K (K + Q) | Nat.Coprime Q (f k)} := by
        congr 1; apply filter_congr; intro k _; exact coprime_mod_iff Q _
    _ = #(((Ico K (K + Q)).image f).filter (fun y => Nat.Coprime Q y)) := by
        rw [filter_image, card_image_of_injOn (hinj.mono (filter_subset _ _))]
    _ = Q.totient := by rw [himg, Nat.totient_eq_card_coprime]

/-- **Conditional residue count (CRT).** For coprime `A, Q`, any `c` and start `K₀`, over `m·Q`
consecutive `k`, the number of `k` with `A·Q` coprime to `c + k·A` is `m·φ(Q)` if `A` is coprime to
`c`, and `0` otherwise. -/
theorem crt_count (A Q c K0 m : ℕ) (hQ : 0 < Q) (hAQ : Nat.Coprime A Q) :
    #{k ∈ Ico K0 (K0 + m * Q) | Nat.Coprime (A * Q) (c + k * A)} =
      if Nat.Coprime A c then m * Q.totient else 0 := by
  have hsplit : ∀ k, Nat.Coprime (A * Q) (c + k * A) ↔ Nat.Coprime A c ∧ Nat.Coprime Q (c + k * A) := by
    intro k; rw [Nat.coprime_mul_iff_left, Nat.coprime_add_mul_right_right]
  split_ifs with hc
  · have hfc : (Ico K0 (K0 + m * Q)).filter (fun k => Nat.Coprime (A * Q) (c + k * A)) =
        (Ico K0 (K0 + m * Q)).filter (fun k => Nat.Coprime Q (c + k * A)) :=
      filter_congr (fun k _ => by rw [hsplit]; exact ⟨fun h => h.2, fun h => ⟨hc, h⟩⟩)
    rw [hfc]
    clear hfc
    induction m with
    | zero => simp
    | succ m ih =>
      rw [show K0 + (m + 1) * Q = (K0 + m * Q) + Q by ring,
        ← Finset.Ico_union_Ico_eq_Ico (b := K0 + m * Q) (by omega) (by omega), Finset.filter_union,
        Finset.card_union_of_disjoint
          (Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive _ _ _)),
        ih, block A Q c _ hQ hAQ]
      ring
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro k _ h
    exact hc ((hsplit k).mp h).1

end E460CRT


namespace E460CRTPrimorial
open Finset E460CRT

lemma mem_primesLE {p n : ℕ} : p ∈ Nat.primesLE n ↔ p ≤ n ∧ p.Prime := by
  unfold Nat.primesLE; rw [Nat.mem_primesBelow]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by omega, h2⟩

/-- `Q_t`: the product of the primes in `(R, t]`. -/
def Qt (R t : ℕ) : ℕ := ∏ p ∈ (Nat.primesLE t).filter (fun p => R < p), p

lemma split (R t : ℕ) (h : R ≤ t) : primorial t = primorial R * Qt R t := by
  unfold Qt
  rw [primorial_eq_prod_primesLE, primorial_eq_prod_primesLE,
    ← Finset.prod_filter_mul_prod_filter_not (Nat.primesLE t) (fun p => p ≤ R)]
  congr 2
  · ext p; simp only [mem_filter, mem_primesLE]
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨by omega, h2⟩, h1⟩
  · ext p; simp only [mem_filter, not_le]

lemma coprime_split (R t : ℕ) : Nat.Coprime (primorial R) (Qt R t) := by
  unfold Qt
  rw [primorial_eq_prod_primesLE]
  apply Nat.Coprime.prod_right
  intro p hp
  apply Nat.Coprime.prod_left
  intro q hq
  obtain ⟨hpt, hpp⟩ := mem_primesLE.mp (mem_filter.mp hp).1
  have hRp := (mem_filter.mp hp).2
  obtain ⟨hqR, hqp⟩ := mem_primesLE.mp hq
  exact (Nat.coprime_primes hqp hpp).mpr (by omega)

/-- **Conditional residue count for a primorial class.** For `R ≤ t ≤ T`, `t ≤ r` and any start `K₀`:
among the `P_T / P_R` consecutive `k`, the number with `n = r + k·P_R` making `n − t` coprime to `P_t`
(i.e. `t`-rough) is `(P_T / P_t)·φ(Q_t)` if `gcd(P_R, r − t) = 1`, and `0` otherwise. -/
theorem primorial_class (R t T r K0 : ℕ) (hRt : R ≤ t) (htT : t ≤ T) (hr : t ≤ r) :
    #{k ∈ Ico K0 (K0 + primorial T / primorial R) | Nat.Coprime (primorial t) (r + k * primorial R - t)} =
      if Nat.Coprime (primorial R) (r - t) then (primorial T / primorial t) * (Qt R t).totient else 0 := by
  have hQpos : 0 < Qt R t := Finset.prod_pos (fun p hp => (mem_primesLE.mp (mem_filter.mp hp).1).2.pos)
  have hsp := split R t hRt
  obtain ⟨q, hq⟩ : primorial t ∣ primorial T := by
    unfold primorial
    apply Finset.prod_dvd_prod_of_subset
    intro p
    simp only [Finset.mem_filter, Finset.mem_range]
    intro hp
    exact ⟨by omega, hp.2⟩
  have hRpos : 0 < primorial R := primorial_pos R
  have hlen : primorial T / primorial R = q * Qt R t := by
    rw [hq, hsp, show primorial R * Qt R t * q = primorial R * (q * Qt R t) by ring,
      Nat.mul_div_cancel_left _ hRpos]
  have hq' : primorial T / primorial t = q := by
    rw [hq]; exact Nat.mul_div_cancel_left _ (primorial_pos t)
  rw [hlen, hq', ← crt_count (primorial R) (Qt R t) (r - t) K0 q hQpos (coprime_split R t), hsp]
  congr 1
  apply filter_congr
  intro k _
  rw [show r + k * primorial R - t = r - t + k * primorial R by omega]

end E460CRTPrimorial

namespace E460Class
open Finset E460Final E460CRTPrimorial

/-- **Mertens bound for the class factor.** There is `c > 0` with `φ(Q_t)/Q_t ≥ c / log t` for all
`R ≤ t`, `t ≥ 2`, where `Q_t = ∏_{R<p≤t} p`. -/
theorem Qt_mertens : ∃ c : ℝ, 0 < c ∧ ∀ R t : ℕ, R ≤ t → 2 ≤ t →
    c / Real.log t ≤ ((Qt R t).totient : ℝ) / (Qt R t : ℝ) := by
  obtain ⟨c, hc, hb⟩ := mertens_lower
  refine ⟨c, hc, fun R t hRt ht => (hb t ht).trans ?_⟩
  have hsp := split R t hRt
  have htot : (primorial t).totient = (primorial R).totient * (Qt R t).totient := by
    rw [hsp]; exact Nat.totient_mul (coprime_split R t)
  have hRpos : (0 : ℝ) < primorial R := by exact_mod_cast primorial_pos R
  have hQpos : (0 : ℝ) < Qt R t := by
    exact_mod_cast Finset.prod_pos (fun p hp => (mem_primesLE.mp (mem_filter.mp hp).1).2.pos)
  have hR1 : ((primorial R).totient : ℝ) / (primorial R : ℝ) ≤ 1 := by
    rw [div_le_one hRpos]; exact_mod_cast Nat.totient_le _
  have hQ0 : 0 ≤ ((Qt R t).totient : ℝ) / (Qt R t : ℝ) := by positivity
  calc ((primorial t).totient : ℝ) / (primorial t : ℝ)
      = ((primorial R).totient : ℝ) / (primorial R : ℝ) * (((Qt R t).totient : ℝ) / (Qt R t : ℝ)) := by
        rw [htot, hsp]; push_cast; field_simp
    _ ≤ 1 * (((Qt R t).totient : ℝ) / (Qt R t : ℝ)) := mul_le_mul_of_nonneg_right hR1 hQ0
    _ = _ := one_mul _

end E460Class


namespace E460AP
open Finset Filter E460Mertens

lemma integral_g_gen (x0 x1 : ℝ) (h0 : 2 ≤ x0) (h01 : x0 ≤ x1) :
    ∫ x in x0..x1, g x = Real.log (Real.log x1) - Real.log (Real.log x0) := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => Real.log (Real.log x)) ?_ ?_
  · intro x hx
    rw [Set.uIcc_of_le h01] at hx
    have hx2 : 2 ≤ x := le_trans h0 hx.1
    have hl : Real.log x ≠ 0 := (Real.log_pos (by linarith)).ne'
    have hd := (Real.hasDerivAt_log (by linarith : x ≠ 0)).log hl
    have hx0 : x ≠ 0 := by linarith
    have hg : g x = x⁻¹ / Real.log x := by unfold g; field_simp
    rw [hg]; exact hd
  · apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h01]
    apply ContinuousOn.div continuousOn_const
    · exact continuousOn_id.mul (Real.continuousOn_log.mono (fun x hx => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro h; have := hx.1; rw [h] at this; linarith))
    · intro x hx
      have h1 : 0 < Real.log x := Real.log_pos (by linarith [hx.1])
      have h2 : 0 < x := by linarith [hx.1]
      positivity

/-- **Divergence along an arithmetic progression.** For `a ≥ 2`, `M ≥ 1`:
`∑_{j<N} 1/((a + jM) log (a + jM)) → ∞`. -/
theorem ap_tendsto (a M : ℕ) (ha : 2 ≤ a) (hM : 1 ≤ M) :
    Tendsto (fun N : ℕ => ∑ j ∈ range N, g ((a : ℝ) + (M : ℝ) * j)) atTop atTop := by
  have haR : (2 : ℝ) ≤ a := by exact_mod_cast ha
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (M : ℝ) ≠ 0 := by linarith
  have hanti : ∀ N : ℕ, AntitoneOn (fun y : ℝ => g ((a : ℝ) + (M : ℝ) * y)) (Set.Icc 0 (0 + N)) := by
    intro N x hx y hy hxy
    simp only [Set.mem_Icc] at hx hy
    have hgx : 2 ≤ (a : ℝ) + M * x := by nlinarith
    have hxy' : (a : ℝ) + M * x ≤ a + M * y := by nlinarith
    unfold g
    have hlx : 0 < Real.log ((a : ℝ) + M * x) := Real.log_pos (by linarith)
    have hl : Real.log ((a : ℝ) + M * x) ≤ Real.log ((a : ℝ) + M * y) := Real.log_le_log (by linarith) hxy'
    apply one_div_le_one_div_of_le (mul_pos (by linarith) hlx)
    exact mul_le_mul hxy' hl hlx.le (by linarith)
  have hbound : ∀ N : ℕ, (M : ℝ)⁻¹ * (Real.log (Real.log ((a : ℝ) + M * N)) - Real.log (Real.log a)) ≤
      ∑ j ∈ range N, g ((a : ℝ) + (M : ℝ) * j) := by
    intro N
    have h1 := (hanti N).integral_le_sum
    simp only [zero_add] at h1
    rw [intervalIntegral.integral_comp_add_mul (fun x => g x) hM0, mul_zero, add_zero,
      integral_g_gen _ _ haR (by nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]), smul_eq_mul] at h1
    exact h1
  have hlim : Tendsto (fun N : ℕ => (M : ℝ)⁻¹ *
      (Real.log (Real.log ((a : ℝ) + M * N)) - Real.log (Real.log a))) atTop atTop := by
    apply Tendsto.const_mul_atTop (inv_pos.mpr (by linarith))
    have h := Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp
      (tendsto_atTop_add_const_left _ (a : ℝ)
        (Tendsto.const_mul_atTop (by linarith : (0 : ℝ) < M) tendsto_natCast_atTop_atTop)))
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right _ (-Real.log (Real.log a)) h
  exact tendsto_atTop_mono hbound hlim

end E460AP


namespace E460ClassFull
open Finset Filter E460Gap E460CRT E460CRTPrimorial E460Class E460AP

set_option maxHeartbeats 1000000 in
/-- **Unboundedness in every primorial residue class.** For every `R`, `r`, `B` and `N₀` there is
`n ≥ N₀` with `n ≡ r (mod P_R)` and `partialSum n ≥ B`. -/
theorem class_unbounded (R r : ℕ) (B : ℝ) (N0 : ℕ) :
    ∃ n ≥ N0, n % primorial R = r % primorial R ∧ B ≤ OMA.S_erdos_460.partialSum n := by
  classical
  set A := primorial R with hA
  have hApos : 0 < A := primorial_pos R
  obtain ⟨c, hc, hQ⟩ := Qt_mertens
  -- the progression of offsets t_j = a + jA with a ≡ r − 1 (mod A), a ≥ R + 2
  set u := r % A with hu
  set v := (u + A - 1) % A with hv
  set a := v + A * (R + 2) with ha
  have ha2 : R + 2 ≤ a := by have : R + 2 ≤ A * (R + 2) := Nat.le_mul_of_pos_left _ hApos; omega
  -- choose J
  have hT := ap_tendsto a A (by omega) hApos
  obtain ⟨J, hJ⟩ := ((hT.eventually_ge_atTop (B / c)).and (eventually_ge_atTop 1)).exists
  set T := a + J * A with hTdef
  set r' := u + A * (N0 + T + 1) with hr'
  have hr'T : T < r' := by have : N0 + T + 1 ≤ A * (N0 + T + 1) := Nat.le_mul_of_pos_left _ hApos; omega
  have hr'N : N0 ≤ r' := by have : N0 + T + 1 ≤ A * (N0 + T + 1) := Nat.le_mul_of_pos_left _ hApos; omega
  set L := primorial T / A with hL
  -- per-offset facts
  have hfacts : ∀ j ∈ range J,
      let t := a + j * A
      R ≤ t ∧ t ≤ T ∧ t ≤ r' ∧ 2 ≤ t ∧ Nat.Coprime A (r' - t) := by
    intro j hj
    rw [mem_range] at hj
    have hjA : j * A ≤ J * A := Nat.mul_le_mul_right _ hj.le
    refine ⟨by omega, by omega, by omega, by omega, ?_⟩
    -- r' − t ≡ 1 (mod A)
    obtain ⟨w, hw⟩ : ∃ w, w = (u + A - 1) / A := ⟨_, rfl⟩
    have hvw : v + A * w = u + A - 1 := by rw [hw]; exact Nat.mod_add_div _ _
    have hu' : u < A := Nat.mod_lt _ hApos
    have hle : a + j * A ≤ r' := by omega
    have hmod : 1 ≡ r' - (a + j * A) [MOD A] := by
      rw [Nat.modEq_iff_dvd]
      refine ⟨(w : ℤ) - 1 + (N0 + T + 1) - (R + 2) - j, ?_⟩
      have hvw' : (v : ℤ) + A * (w : ℤ) = u + A - 1 := by
        have := congrArg (fun z : ℕ => (z : ℤ)) hvw
        simp only [Nat.cast_add, Nat.cast_mul] at this
        rw [this, Nat.cast_sub (by omega)]; push_cast; ring
      have hcast : ((r' - (a + j * A) : ℕ) : ℤ) = (u : ℤ) + A * (N0 + T + 1) - (v + A * (R + 2) + j * A) := by
        rw [Nat.cast_sub hle, hr', ha]; push_cast; ring
      rw [hcast]
      linear_combination -hvw'
    rw [coprime_mod_iff, ← (hmod : 1 % A = (r' - (a + j * A)) % A), ← coprime_mod_iff]
    exact Nat.coprime_one_right A
  -- lower bound for ST on the class
  have hSTlow : ∀ n : ℕ, (∑ j ∈ range J,
      (if (primorial (a + j * A)).Coprime (n - (a + j * A)) then (1 : ℝ) / ((a + j * A : ℕ) : ℝ) else 0))
      ≤ E460Gap.ST T n := by
    intro n
    unfold E460Gap.ST
    have hinj : Set.InjOn (fun j => a + j * A) (range J) := by
      intro x _ y _ hxy
      have hxy' : a + x * A = a + y * A := hxy
      have : x * A = y * A := by omega
      exact Nat.eq_of_mul_eq_mul_right hApos this
    rw [← Finset.sum_image (f := fun t => if (primorial t).Coprime (n - t) then (1 : ℝ) / (t : ℝ) else 0) hinj]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro t ht
      obtain ⟨j, hj, rfl⟩ := mem_image.mp ht
      have := hfacts j hj
      exact mem_Icc.mpr ⟨by omega, this.2.1⟩
    · intro t _ _; split_ifs <;> positivity
  -- each offset contributes at least L·c·g(t_j) to the class sum
  have hcontrib : ∀ j ∈ range J,
      (L : ℝ) * (c * E460Mertens.g ((a : ℝ) + (A : ℝ) * j)) ≤
        ∑ k ∈ range L, (if (primorial (a + j * A)).Coprime (r' + k * A - (a + j * A))
          then (1 : ℝ) / ((a + j * A : ℕ) : ℝ) else 0) := by
    intro j hj
    obtain ⟨hR, hTt, hr't, h2, hcop⟩ := hfacts j hj
    set t := a + j * A with ht
    have hcount := primorial_class R t T r' 0 hR hTt hr't
    rw [if_pos hcop, zero_add] at hcount
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Finset.range_eq_Ico, hcount]
    obtain ⟨m, hm⟩ := E460Avg.primorial_dvd hTt
    have hsp := split R t hR
    have hQpos : 0 < Qt R t := Finset.prod_pos (fun p hp => (mem_primesLE.mp (mem_filter.mp hp).1).2.pos)
    have hm' : primorial T / primorial t = m := by rw [hm]; exact Nat.mul_div_cancel_left _ (primorial_pos t)
    have hLm : L = Qt R t * m := by
      rw [hL, hm, hsp, show A * Qt R t * m = A * (Qt R t * m) by ring]; exact Nat.mul_div_cancel_left _ hApos
    rw [hm', hLm]
    have hb := hQ R t hR h2
    have htR : (2 : ℝ) ≤ t := by exact_mod_cast h2
    have hlt : 0 < Real.log t := Real.log_pos (by linarith)
    have hQR : (0 : ℝ) < Qt R t := by exact_mod_cast hQpos
    have hcast : ((a : ℝ) + (A : ℝ) * j) = (t : ℝ) := by rw [ht]; push_cast; ring
    rw [hcast]
    unfold E460Mertens.g
    rw [div_le_div_iff₀ (by positivity) hQR] at hb
    push_cast
    have htpos : (0 : ℝ) < t := by linarith
    rw [show ((Qt R t : ℝ) * m) * (c * (1 / ((t : ℝ) * Real.log t))) =
        (m / t) * (c * Qt R t / Real.log t) by field_simp]
    rw [show ((m : ℝ) * ((Qt R t).totient : ℝ)) * (1 / (t : ℝ)) = (m / t) * ((Qt R t).totient : ℝ) by
      field_simp]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [div_le_iff₀ hlt]; linarith
  -- pigeonhole over the class period
  have hLpos : 0 < L := by
    obtain ⟨m, hm⟩ := E460Avg.primorial_dvd (show R ≤ T by omega)
    rw [hL, hm]; rw [Nat.mul_div_cancel_left _ hApos]
    exact Nat.pos_of_ne_zero (fun h0 => by rw [h0, mul_zero] at hm; exact (primorial_pos T).ne' hm)
  have hne : (range L).Nonempty := ⟨0, mem_range.mpr hLpos⟩
  have hsum : ∑ _k ∈ range L, B ≤ ∑ k ∈ range L, E460Gap.ST T (r' + k * A) := by
    rw [Finset.sum_const, card_range, nsmul_eq_mul]
    calc (L : ℝ) * B ≤ (L : ℝ) * (c * ∑ j ∈ range J, E460Mertens.g ((a : ℝ) + (A : ℝ) * j)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have := hJ.1
          rw [div_le_iff₀ hc] at this; linarith
      _ = ∑ j ∈ range J, (L : ℝ) * (c * E460Mertens.g ((a : ℝ) + (A : ℝ) * j)) := by
          rw [Finset.mul_sum, Finset.mul_sum]
      _ ≤ ∑ j ∈ range J, ∑ k ∈ range L, (if (primorial (a + j * A)).Coprime (r' + k * A - (a + j * A))
            then (1 : ℝ) / ((a + j * A : ℕ) : ℝ) else 0) := Finset.sum_le_sum hcontrib
      _ = ∑ k ∈ range L, ∑ j ∈ range J, (if (primorial (a + j * A)).Coprime (r' + k * A - (a + j * A))
            then (1 : ℝ) / ((a + j * A : ℕ) : ℝ) else 0) := Finset.sum_comm
      _ ≤ _ := Finset.sum_le_sum fun k _ => hSTlow _
  obtain ⟨k, -, hk⟩ := Finset.exists_le_of_sum_le hne hsum
  refine ⟨r' + k * A, by omega, ?_, ?_⟩
  · rw [Nat.add_mul_mod_self_right, hr', Nat.add_mul_mod_self_left, Nat.mod_mod]
  · exact hk.trans (trunc_le T _ (by omega))

end E460ClassFull



namespace E460Pair
open Finset

/-- **CRT product count.** For coprime `a, b > 0` and any conditions `P` on residues mod `a` and `Q` on
residues mod `b`: `#{n < ab : P (n % a) ∧ Q (n % b)} = #{x < a : P x} · #{y < b : Q y}`. -/
theorem crt_prod (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b)
    (P Q : ℕ → Prop) [DecidablePred P] [DecidablePred Q] :
    #{n ∈ range (a * b) | P (n % a) ∧ Q (n % b)} = #{x ∈ range a | P x} * #{y ∈ range b | Q y} := by
  set f : ℕ → ℕ × ℕ := fun n => (n % a, n % b) with hf
  have hinj : Set.InjOn f (range (a * b)) := by
    intro x hx y hy hxy
    simp only [coe_range, Set.mem_Iio] at hx hy
    simp only [hf, Prod.mk.injEq] at hxy
    have h := (Nat.modEq_and_modEq_iff_modEq_mul hab).mp ⟨hxy.1, hxy.2⟩
    unfold Nat.ModEq at h
    rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h
  have himg : (range (a * b)).image f = range a ×ˢ range b := by
    apply Finset.eq_of_subset_of_card_le
    · intro p hp
      obtain ⟨n, -, rfl⟩ := mem_image.mp hp
      exact mem_product.mpr ⟨mem_range.mpr (Nat.mod_lt _ ha), mem_range.mpr (Nat.mod_lt _ hb)⟩
    · rw [card_product, card_range, card_range, card_image_of_injOn hinj, card_range]
  calc #{n ∈ range (a * b) | P (n % a) ∧ Q (n % b)}
      = #(((range (a * b)).image f).filter (fun p => P p.1 ∧ Q p.2)) := by
        rw [filter_image, card_image_of_injOn (hinj.mono (filter_subset _ _))]
    _ = #((range a ×ˢ range b).filter (fun p => P p.1 ∧ Q p.2)) := by rw [himg]
    _ = _ := by rw [filter_product, card_product]

/-- **Per-prime pair count.** For a prime `p` and offsets `t, u`, the residues `x < p` avoiding both
`t` and `u` mod `p` number `p − 1` if `t ≡ u (mod p)` and `p − 2` otherwise. -/
theorem prime_count (p t u : ℕ) (hp : p.Prime) :
    #{x ∈ range p | x ≠ t % p ∧ x ≠ u % p} = if t % p = u % p then p - 1 else p - 2 := by
  have ht : t % p ∈ range p := mem_range.mpr (Nat.mod_lt _ hp.pos)
  have hu : u % p ∈ range p := mem_range.mpr (Nat.mod_lt _ hp.pos)
  have heq : (range p).filter (fun x => x ≠ t % p ∧ x ≠ u % p) = range p \ {t % p, u % p} := by
    ext x; simp only [mem_filter, mem_sdiff, mem_insert, mem_singleton]; tauto
  rw [heq]
  have hsub : ({t % p, u % p} : Finset ℕ) ⊆ range p := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ht
    · exact hu
  rw [Finset.card_sdiff_of_subset hsub, card_range]
  split_ifs with h
  · rw [h, Finset.insert_eq_of_mem (mem_singleton_self _), card_singleton]
  · rw [card_pair h]

/-- The pair event at one prime depends only on `n mod p`: for `u ≤ n`,
`p ∤ n − t ∧ p ∤ n − u ↔ n % p ≠ t % p ∧ n % p ≠ u % p`. -/
lemma event_iff (p n t u : ℕ) (ht : t ≤ n) (hu : u ≤ n) :
    (¬ p ∣ n - t ∧ ¬ p ∣ n - u) ↔ (n % p ≠ t % p ∧ n % p ≠ u % p) := by
  rw [← Nat.modEq_iff_dvd' ht, ← Nat.modEq_iff_dvd' hu]
  unfold Nat.ModEq
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨fun h => h1 h.symm, fun h => h2 h.symm⟩

/-- **Multi-prime CRT product.** For a finite set `s` of primes and conditions `A p` on residues mod `p`:
`#{n < ∏_{p∈s} p : ∀ p ∈ s, A p (n % p)} = ∏_{p∈s} #{x < p : A p x}`. -/
theorem crt_primes (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (A : ℕ → ℕ → Prop) [∀ p, DecidablePred (A p)] :
    #{n ∈ range (∏ p ∈ s, p) | ∀ p ∈ s, A p (n % p)} = ∏ p ∈ s, #{x ∈ range p | A p x} := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert q s hq ih =>
    have hs' : ∀ p ∈ s, p.Prime := fun p hp => hs p (mem_insert_of_mem hp)
    have hqp : q.Prime := hs q (mem_insert_self q s)
    have hprod_pos : 0 < ∏ p ∈ s, p := Finset.prod_pos (fun p hp => (hs' p hp).pos)
    have hcop : Nat.Coprime (∏ p ∈ s, p) q := by
      apply Nat.Coprime.prod_left
      intro p hp
      exact (Nat.coprime_primes (hs' p hp) hqp).mpr (fun h => hq (h ▸ hp))
    rw [Finset.prod_insert hq, Finset.prod_insert hq, ← ih hs', mul_comm q (∏ p ∈ s, p)]
    have hcongr : ∀ n, (∀ p ∈ insert q s, A p (n % p)) ↔
        ((∀ p ∈ s, A p ((n % ∏ p ∈ s, p) % p)) ∧ A q (n % q)) := by
      intro n
      simp only [mem_insert, forall_eq_or_imp]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨fun p hp => ?_, h1⟩
        rw [Nat.mod_mod_of_dvd _ (Finset.dvd_prod_of_mem _ hp)]; exact h2 p hp
      · rintro ⟨h2, h1⟩
        refine ⟨h1, fun p hp => ?_⟩
        have := h2 p hp
        rwa [Nat.mod_mod_of_dvd _ (Finset.dvd_prod_of_mem _ hp)] at this
    rw [Finset.filter_congr (fun n _ => hcongr n)]
    rw [crt_prod (∏ p ∈ s, p) q hprod_pos hqp.pos hcop (fun x => ∀ p ∈ s, A p (x % p)) (A q), mul_comm]

end E460Pair


namespace E460PairFull
open Finset E460Pair

lemma mem_primesLE {p n : ℕ} : p ∈ Nat.primesLE n ↔ p ≤ n ∧ p.Prime := by
  unfold Nat.primesLE; rw [Nat.mem_primesBelow]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by omega, h2⟩

/-- A condition on `n % M`, counted over one block of `M` consecutive `n`. -/
lemma periodic_one (M N : ℕ) (hM : 0 < M) (Q : ℕ → Prop) [DecidablePred Q] :
    #{n ∈ Ico N (N + M) | Q (n % M)} = #{x ∈ range M | Q x} := by
  have hinj : Set.InjOn (fun n => n % M) (Ico N (N + M)) := by
    intro x hx y hy hxy
    simp only [coe_Ico, Set.mem_Ico] at hx hy
    obtain ⟨a, rfl⟩ : ∃ a, x = N + a := ⟨x - N, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, y = N + b := ⟨y - N, by omega⟩
    have h : a ≡ b [MOD M] := Nat.ModEq.add_left_cancel' N hxy
    unfold Nat.ModEq at h
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h
    omega
  have himg : (Ico N (N + M)).image (fun n => n % M) = range M := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy; obtain ⟨n, -, rfl⟩ := mem_image.mp hy; exact mem_range.mpr (Nat.mod_lt _ hM)
    · rw [card_image_of_injOn hinj, card_range, Nat.card_Ico]; omega
  rw [← himg, filter_image, card_image_of_injOn (hinj.mono (filter_subset _ _))]

lemma periodic_block (M N m : ℕ) (hM : 0 < M) (Q : ℕ → Prop) [DecidablePred Q] :
    #{n ∈ Ico N (N + m * M) | Q (n % M)} = m * #{x ∈ range M | Q x} := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show N + (m + 1) * M = (N + m * M) + M by ring,
      ← Finset.Ico_union_Ico_eq_Ico (b := N + m * M) (by omega) (by omega), Finset.filter_union,
      Finset.card_union_of_disjoint
        (Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive _ _ _)),
      ih, periodic_one M _ hM Q]
    ring

lemma coprime_primorial_iff (t x : ℕ) :
    Nat.Coprime (primorial t) x ↔ ∀ p ∈ Nat.primesLE t, ¬ p ∣ x := by
  rw [primorial_eq_prod_primesLE, Nat.coprime_prod_left_iff]
  refine forall₂_congr fun p hp => ?_
  exact Nat.Prime.coprime_iff_not_dvd (mem_primesLE.mp hp).2

/-- **Exact pair count.** For `t ≤ u ≤ T` and any block of length `P_T` starting at `N ≥ u`, the number of
`n` with `n − t` coprime to `P_t` and `n − u` coprime to `P_u` is
`(P_T / P_u) · ∏_{p ≤ u} (if p ≤ t then (if t ≡ u mod p then p − 1 else p − 2) else p − 1)`. -/
theorem pair_count (t u T N : ℕ) (htu : t ≤ u) (huT : u ≤ T) (hN : u ≤ N) :
    #{n ∈ Ico N (N + primorial T) | Nat.Coprime (primorial t) (n - t) ∧ Nat.Coprime (primorial u) (n - u)} =
      (primorial T / primorial u) * ∏ p ∈ Nat.primesLE u,
        (if p ≤ t then (if t % p = u % p then p - 1 else p - 2) else p - 1) := by
  classical
  set Pu := primorial u with hPu
  have hPupos : 0 < Pu := primorial_pos u
  have hdvd : Pu ∣ primorial T := by
    unfold Pu primorial
    apply Finset.prod_dvd_prod_of_subset
    intro p; simp only [Finset.mem_filter, Finset.mem_range]; intro hp; exact ⟨by omega, hp.2⟩
  obtain ⟨m, hm⟩ := hdvd
  set A : ℕ → ℕ → Prop := fun p x => (p ≤ t → x ≠ t % p) ∧ x ≠ u % p with hA
  -- the event as a condition on n % P_u
  have hev : ∀ n ∈ Ico N (N + primorial T),
      (Nat.Coprime (primorial t) (n - t) ∧ Nat.Coprime (primorial u) (n - u)) ↔
        (fun x => ∀ p ∈ Nat.primesLE u, A p (x % p)) (n % Pu) := by
    intro n hn
    have hnu : u ≤ n := le_trans hN (mem_Ico.mp hn).1
    have hdiv : ∀ p ∈ Nat.primesLE u, (n % Pu) % p = n % p := fun p hp =>
      Nat.mod_mod_of_dvd _ (by rw [hPu, primorial_eq_prod_primesLE]; exact Finset.dvd_prod_of_mem _ hp)
    have hsingle : ∀ p s, s ≤ n → (¬ p ∣ n - s ↔ n % p ≠ s % p) := by
      intro p s hs
      rw [← Nat.modEq_iff_dvd' hs]
      unfold Nat.ModEq
      exact ⟨fun h h' => h h'.symm, fun h h' => h h'.symm⟩
    simp only [coprime_primorial_iff, hA]
    constructor
    · rintro ⟨h1, h2⟩ p hp
      rw [hdiv p hp]
      refine ⟨fun hpt => (hsingle p t (by omega)).mp (h1 p (mem_primesLE.mpr ⟨hpt, (mem_primesLE.mp hp).2⟩)),
        (hsingle p u hnu).mp (h2 p hp)⟩
    · intro h
      refine ⟨fun p hp => ?_, fun p hp => ?_⟩
      · have hpu : p ∈ Nat.primesLE u := mem_primesLE.mpr ⟨by have := (mem_primesLE.mp hp).1; omega, (mem_primesLE.mp hp).2⟩
        have := (h p hpu).1 (mem_primesLE.mp hp).1
        rw [hdiv p hpu] at this
        exact (hsingle p t (by omega)).mpr this
      · have := (h p hp).2
        rw [hdiv p hp] at this
        exact (hsingle p u hnu).mpr this
  rw [Finset.filter_congr hev, show primorial T = m * Pu by rw [hm]; ring,
    show m * Pu / Pu = m by rw [Nat.mul_div_cancel _ hPupos]]
  have hcrt := crt_primes (Nat.primesLE u) (fun p hp => (mem_primesLE.mp hp).2) A
  rw [← primorial_eq_prod_primesLE, ← hPu] at hcrt
  calc _ = m * #{x ∈ range Pu | ∀ p ∈ Nat.primesLE u, A p (x % p)} := by
        convert periodic_block Pu N m hPupos (fun x => ∀ p ∈ Nat.primesLE u, A p (x % p)) using 2
    _ = m * ∏ p ∈ Nat.primesLE u, #{x ∈ range p | A p x} := by
        congr 1
    _ = _ := by
      congr 1
      refine Finset.prod_congr rfl fun p hp => ?_
      have hpp := (mem_primesLE.mp hp).2
      by_cases hpt : p ≤ t
      · rw [if_pos hpt, ← prime_count p t u hpp]
        congr 1; apply filter_congr; intro x _
        simp only [hA]; exact ⟨fun h => ⟨h.1 hpt, h.2⟩, fun h => ⟨fun _ => h.1, h.2⟩⟩
      · rw [if_neg hpt]
        have hfil : (range p).filter (A p) = range p \ {u % p} := by
          ext x; simp only [mem_filter, mem_sdiff, mem_singleton, hA]
          exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, fun h' => absurd h' hpt, h.2⟩⟩
        rw [hfil, Finset.card_sdiff_of_subset (singleton_subset_iff.mpr (mem_range.mpr (Nat.mod_lt _ hpp.pos))),
          card_range, card_singleton]

end E460PairFull


namespace E460Second
open Finset E460Pair E460PairFull

lemma rho_eq (t : ℕ) :
    ((primorial t).totient : ℝ) / (primorial t : ℝ) = ∏ p ∈ Nat.primesLE t, (1 - (p : ℝ)⁻¹) := by
  have hq := Nat.totient_eq_mul_prod_factors (primorial t)
  rw [primeFactors_primorial] at hq
  have hr : ((primorial t).totient : ℝ) = (primorial t : ℝ) * ∏ p ∈ Nat.primesLE t, (1 - (p : ℝ)⁻¹) := by
    have := congrArg (fun x : ℚ => (x : ℝ)) hq; push_cast at this; exact this
  have hP : (primorial t : ℝ) ≠ 0 := by exact_mod_cast (primorial_pos t).ne'
  rw [hr, mul_div_cancel_left₀ _ hP]

lemma filter_le_eq (t u : ℕ) (htu : t ≤ u) : (Nat.primesLE u).filter (fun p => p ≤ t) = Nat.primesLE t := by
  ext p; simp only [mem_filter, mem_primesLE]
  constructor
  · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨by omega, h2⟩, h1⟩

/-- **Pair bound.** For `t < u ≤ T` and a block of `P_T` consecutive `n ≥ u`:
`#{both rough} / P_T ≤ ρ_t · ρ_u · ∏_{p ≤ t, p ∣ u − t} p/(p − 1)`. -/
theorem pair_prob_le (t u T N : ℕ) (htu : t < u) (huT : u ≤ T) (hN : u ≤ N) :
    ((#{n ∈ Ico N (N + primorial T) |
        Nat.Coprime (primorial t) (n - t) ∧ Nat.Coprime (primorial u) (n - u)} : ℕ) : ℝ) /
        (primorial T : ℝ) ≤
      ((primorial t).totient : ℝ) / (primorial t : ℝ) * (((primorial u).totient : ℝ) / (primorial u : ℝ)) *
        ∏ p ∈ (Nat.primesLE t).filter (fun p => p ∣ u - t), (p : ℝ) / ((p : ℝ) - 1) := by
  classical
  rw [pair_count t u T N htu.le huT hN]
  obtain ⟨m, hm⟩ : primorial u ∣ primorial T := by
    unfold primorial
    apply Finset.prod_dvd_prod_of_subset
    intro p; simp only [Finset.mem_filter, Finset.mem_range]; intro hp; exact ⟨by omega, hp.2⟩
  have hPu : (0 : ℝ) < primorial u := by exact_mod_cast primorial_pos u
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, mul_zero] at hm; exact absurd hm (primorial_pos T).ne'
    · exact h
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  rw [hm, Nat.mul_div_cancel_left _ (primorial_pos u)]
  push_cast
  rw [rho_eq, rho_eq]
  have hPprod : (primorial u : ℝ) = ∏ p ∈ Nat.primesLE u, (p : ℝ) := by
    rw [primorial_eq_prod_primesLE]; push_cast; rfl
  set U := Nat.primesLE u with hU
  have hprime : ∀ p ∈ U, p.Prime := fun p hp => (mem_primesLE.mp hp).2
  have hR : (∏ p ∈ Nat.primesLE t, (1 - (p : ℝ)⁻¹)) * (∏ p ∈ U, (1 - (p : ℝ)⁻¹)) *
      ∏ p ∈ (Nat.primesLE t).filter (fun p => p ∣ u - t), (p : ℝ) / ((p : ℝ) - 1) =
      ∏ p ∈ U, ((if p ≤ t then (1 - (p : ℝ)⁻¹) else 1) * (1 - (p : ℝ)⁻¹) *
        (if p ≤ t ∧ p ∣ u - t then (p : ℝ) / ((p : ℝ) - 1) else 1)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, ← Finset.prod_filter, ← Finset.prod_filter,
      filter_le_eq t u htu.le, ← filter_le_eq t u htu.le, Finset.filter_filter, filter_le_eq t u htu.le]
  rw [hR]
  calc (m : ℝ) * (∏ x ∈ U, if x ≤ t then (if t % x = u % x then ((x - 1 : ℕ) : ℝ) else ((x - 2 : ℕ) : ℝ))
          else ((x - 1 : ℕ) : ℝ)) / ((primorial u : ℝ) * m)
      = (∏ x ∈ U, if x ≤ t then (if t % x = u % x then ((x - 1 : ℕ) : ℝ) else ((x - 2 : ℕ) : ℝ))
          else ((x - 1 : ℕ) : ℝ)) / ∏ p ∈ U, (p : ℝ) := by
        rw [← hPprod]; field_simp
    _ = ∏ x ∈ U, ((if x ≤ t then (if t % x = u % x then ((x - 1 : ℕ) : ℝ) else ((x - 2 : ℕ) : ℝ))
          else ((x - 1 : ℕ) : ℝ)) / (x : ℝ)) := (Finset.prod_div_distrib _ _).symm
    _ ≤ _ := by
        apply Finset.prod_le_prod
        · intro p hp
          have := (hprime p hp).two_le
          apply div_nonneg _ (Nat.cast_nonneg _)
          split_ifs <;> exact Nat.cast_nonneg _
        · intro p hp
          have h2 := (hprime p hp).two_le
          have hpR : (2 : ℝ) ≤ p := by exact_mod_cast h2
          have hp0 : (p : ℝ) ≠ 0 := by linarith
          have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
          have c1 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; norm_num
          have c2 : ((p - 2 : ℕ) : ℝ) = (p : ℝ) - 2 := by rw [Nat.cast_sub h2]; norm_num
          by_cases hpt : p ≤ t
          · have hiff : t % p = u % p ↔ p ∣ u - t := by
              rw [← Nat.modEq_iff_dvd' htu.le]; rfl
            by_cases hd : t % p = u % p
            · rw [if_pos hpt, if_pos hd, if_pos hpt, if_pos ⟨hpt, hiff.mp hd⟩, c1]
              apply le_of_eq; field_simp
            · rw [if_pos hpt, if_neg hd, if_pos hpt, if_neg (fun h => hd (hiff.mpr h.2)), c2]
              rw [mul_one, div_le_iff₀ (by linarith)]
              have : (1 - (p : ℝ)⁻¹) * (1 - (p : ℝ)⁻¹) * p = (p - 2) + 1 / p := by field_simp; ring
              rw [this]
              have : 0 < 1 / (p : ℝ) := by positivity
              linarith
          · rw [if_neg hpt, if_neg hpt, if_neg (fun h => hpt h.1), c1]
            apply le_of_eq; field_simp

/-- `φ(∏_{p∈S} p) = ∏_{p∈S} (p − 1)` for a finite set of primes. -/
lemma totient_prod_primes (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (∏ p ∈ S, p).totient = ∏ p ∈ S, (p - 1) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert q S hq ih =>
    have hS' : ∀ p ∈ S, p.Prime := fun p hp => hS p (mem_insert_of_mem hp)
    have hqp : q.Prime := hS q (mem_insert_self q S)
    have hcop : Nat.Coprime q (∏ p ∈ S, p) := by
      apply Nat.Coprime.prod_right
      intro p hp
      exact (Nat.coprime_primes hqp (hS' p hp)).mpr (fun h => hq (h ▸ hp))
    rw [Finset.prod_insert hq, Finset.prod_insert hq, Nat.totient_mul hcop, Nat.totient_prime hqp, ih hS']

/-- **Divisor expansion.** For a finite set `s` of primes,
`∏_{p∈s} p/(p − 1) = ∑_{S ⊆ s} 1/φ(∏_{p∈S} p)`, i.e. the sum over squarefree divisors `e` of
`∏ s` of `1/φ(e)`. -/
theorem expand (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    ∏ p ∈ s, (p : ℝ) / ((p : ℝ) - 1) = ∑ S ∈ s.powerset, 1 / ((∏ p ∈ S, p).totient : ℝ) := by
  classical
  have hterm : ∀ p ∈ s, (p : ℝ) / ((p : ℝ) - 1) = 1 / ((p : ℝ) - 1) + 1 := by
    intro p hp
    have : (2 : ℝ) ≤ p := by exact_mod_cast (hs p hp).two_le
    have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [Finset.prod_congr rfl hterm, Finset.prod_add]
  refine Finset.sum_congr rfl fun S hS => ?_
  have hSs : S ⊆ s := Finset.mem_powerset.mp hS
  have hSp : ∀ p ∈ S, p.Prime := fun p hp => hs p (hSs hp)
  rw [Finset.prod_const_one, mul_one, totient_prod_primes S hSp, Finset.prod_div_distrib, Finset.prod_const_one]
  congr 1
  push_cast
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [Nat.cast_sub (hSp p hp).one_lt.le]; norm_num

end E460Second


namespace E460Second2
open Finset E460Second

/-- A block of `d` integers ending at `a + d` dominates `d · f(a + d)` for decreasing `f`. -/
lemma block_ge (f : ℕ → ℝ) (hf : Antitone f) (a d : ℕ) :
    (d : ℝ) * f (a + d) ≤ ∑ v ∈ Ioc a (a + d), f v := by
  have := Finset.card_nsmul_le_sum (Ioc a (a + d)) f (f (a + d))
    (fun v hv => hf (Finset.mem_Ioc.mp hv).2)
  rw [Nat.card_Ioc, show a + d - a = d by omega, nsmul_eq_mul] at this
  exact this

/-- **(1) Sparse right endpoints.** For decreasing nonnegative `f`, `d > 0` and `t + K·d ≤ T`:
`∑_{k<K} f(t + (k+1)d) ≤ (1/d) ∑_{t<u≤T} f(u)`. -/
theorem sparse_le (f : ℕ → ℝ) (hf : Antitone f) (hf0 : ∀ n, 0 ≤ f n) (t d K T : ℕ) (hd : 0 < d)
    (hK : t + K * d ≤ T) :
    ∑ k ∈ range K, f (t + (k + 1) * d) ≤ (1 / (d : ℝ)) * ∑ u ∈ Ioc t T, f u := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have key : ∀ K : ℕ, (d : ℝ) * ∑ k ∈ range K, f (t + (k + 1) * d) ≤ ∑ v ∈ Ioc t (t + K * d), f v := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.sum_range_succ, mul_add,
        show t + (K + 1) * d = (t + K * d) + d by ring,
        ← Finset.Ioc_union_Ioc_eq_Ioc (b := t + K * d) (by omega) (by omega),
        Finset.sum_union (Finset.Ioc_disjoint_Ioc_of_le le_rfl)]
      exact add_le_add ih (block_ge f hf _ d)
  have hsub : ∑ v ∈ Ioc t (t + K * d), f v ≤ ∑ u ∈ Ioc t T, f u :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ioc_subset_Ioc le_rfl hK) (fun i _ _ => hf0 i)
  rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hdR, mul_comm]
  exact (key K).trans hsub

/-- Telescoping: `∑_{m=2}^{N} 1/(m(m−1)) = 1 − 1/N` for `N ≥ 1`. -/
lemma telescope (N : ℕ) (hN : 1 ≤ N) :
    ∑ m ∈ Icc 2 N, 1 / ((m : ℝ) * ((m : ℝ) - 1)) = 1 - 1 / (N : ℝ) := by
  induction N with
  | zero => omega
  | succ N ih =>
    rcases Nat.eq_zero_or_pos N with rfl | hN'
    · norm_num
    · rw [Finset.sum_Icc_succ_top (by omega), ih hN']
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN'
      have h1 : (N : ℝ) ≠ 0 := by linarith
      have h2 : (N : ℝ) + 1 ≠ 0 := by linarith
      push_cast
      rw [show (N : ℝ) + 1 - 1 = N by ring]
      field_simp
      ring

/-- **(2) Product bound.** For any finite set `s` of primes, `∏_{p∈s} (1 + 1/(p(p−1))) ≤ e`. -/
theorem prod_le_exp_one (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    ∏ p ∈ s, (1 + 1 / ((p : ℝ) * ((p : ℝ) - 1))) ≤ Real.exp 1 := by
  have hx : ∀ p ∈ s, 0 ≤ 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
    intro p hp
    have : (2 : ℝ) ≤ p := by exact_mod_cast (hs p hp).two_le
    apply div_nonneg zero_le_one; nlinarith
  calc ∏ p ∈ s, (1 + 1 / ((p : ℝ) * ((p : ℝ) - 1)))
      ≤ ∏ p ∈ s, Real.exp (1 / ((p : ℝ) * ((p : ℝ) - 1))) :=
        Finset.prod_le_prod (fun p hp => by linarith [hx p hp])
          (fun p hp => by linarith [Real.add_one_le_exp (1 / ((p : ℝ) * ((p : ℝ) - 1)))])
    _ = Real.exp (∑ p ∈ s, 1 / ((p : ℝ) * ((p : ℝ) - 1))) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp 1 := by
        apply Real.exp_le_exp.mpr
        set N := s.sup id + 2 with hN
        have hsub : s ⊆ Icc 2 N := by
          intro p hp
          have h2 := (hs p hp).two_le
          have hle : p ≤ s.sup id := Finset.le_sup (f := id) hp
          exact Finset.mem_Icc.mpr ⟨h2, by omega⟩
        calc ∑ p ∈ s, 1 / ((p : ℝ) * ((p : ℝ) - 1))
            ≤ ∑ m ∈ Icc 2 N, 1 / ((m : ℝ) * ((m : ℝ) - 1)) :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m hm _ => by
                have : (2 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
                apply div_nonneg zero_le_one; nlinarith)
          _ = 1 - 1 / (N : ℝ) := telescope N (by omega)
          _ ≤ 1 := by have : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
                      linarith

/-- Expansion: `∏_{p∈s} (1 + 1/(p(p−1))) = ∑_{S⊆s} 1/(e·φ(e))` with `e = ∏_{p∈S} p`. -/
theorem expand2 (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    ∏ p ∈ s, (1 + 1 / ((p : ℝ) * ((p : ℝ) - 1))) =
      ∑ S ∈ s.powerset, 1 / (((∏ p ∈ S, p : ℕ) : ℝ) * ((∏ p ∈ S, p).totient : ℝ)) := by
  classical
  rw [show (∏ p ∈ s, (1 + 1 / ((p : ℝ) * ((p : ℝ) - 1)))) =
      ∏ p ∈ s, (1 / ((p : ℝ) * ((p : ℝ) - 1)) + 1) from Finset.prod_congr rfl (fun p _ => add_comm _ _),
    Finset.prod_add]
  refine Finset.sum_congr rfl fun S hS => ?_
  have hSs : S ⊆ s := Finset.mem_powerset.mp hS
  have hSp : ∀ p ∈ S, p.Prime := fun p hp => hs p (hSs hp)
  rw [Finset.prod_const_one, mul_one, totient_prod_primes S hSp, Finset.prod_div_distrib, Finset.prod_const_one]
  congr 1
  push_cast
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [Nat.cast_sub (hSp p hp).one_lt.le]; norm_num

end E460Second2


namespace E460Second3
open Finset E460Second E460Second2 E460PairFull

/-- Sparse bound in filter form: `∑_{t<u≤T, e ∣ u − t} f u ≤ (1/e) ∑_{t<u≤T} f u`. -/
lemma sparse_filter (f : ℕ → ℝ) (hf : Antitone f) (hf0 : ∀ n, 0 ≤ f n) (t T e : ℕ) (he : 0 < e) :
    ∑ u ∈ (Ioc t T).filter (fun u => e ∣ u - t), f u ≤ (1 / (e : ℝ)) * ∑ u ∈ Ioc t T, f u := by
  classical
  rcases Nat.lt_or_ge T t with hTt | hTt
  · have hE : Ioc t T = ∅ := Finset.Ioc_eq_empty (by omega)
    simp [hE]
  set K := (T - t) / e with hK
  have hKT : t + K * e ≤ T := by
    have := Nat.div_mul_le_self (T - t) e
    rw [← hK] at this
    omega
  have himg : (Ioc t T).filter (fun u => e ∣ u - t) = (range K).image (fun k => t + (k + 1) * e) := by
    ext u
    simp only [mem_filter, mem_Ioc, mem_image, mem_range]
    constructor
    · rintro ⟨⟨h1, h2⟩, q, hq⟩
      refine ⟨q - 1, ?_, ?_⟩
      · have hq1 : 1 ≤ q := by
          rcases Nat.eq_zero_or_pos q with h0 | h0
          · rw [h0, mul_zero] at hq; omega
          · exact h0
        have : q * e ≤ T - t := by rw [mul_comm]; omega
        have : q ≤ K := by rw [hK]; exact (Nat.le_div_iff_mul_le he).mpr this
        omega
      · have hq1 : 1 ≤ q := by
          rcases Nat.eq_zero_or_pos q with h0 | h0
          · rw [h0, mul_zero] at hq; omega
          · exact h0
        rw [show q - 1 + 1 = q by omega, mul_comm]; omega
    · rintro ⟨k, hk, rfl⟩
      have hke : (k + 1) * e ≤ K * e := Nat.mul_le_mul_right _ (by omega)
      refine ⟨⟨by nlinarith, by omega⟩, ⟨k + 1, by rw [mul_comm]; omega⟩⟩
  have hinj : Set.InjOn (fun k => t + (k + 1) * e) (range K) := by
    intro x _ y _ hxy
    have hxy' : t + (x + 1) * e = t + (y + 1) * e := hxy
    have : (x + 1) * e = (y + 1) * e := by omega
    have := Nat.eq_of_mul_eq_mul_right he this
    omega
  rw [himg, Finset.sum_image hinj]
  exact sparse_le f hf hf0 t e K T he hKT

/-- `∀ p ∈ S, p ∣ d` iff `∏ S ∣ d`, for a set of primes. -/
lemma all_dvd_iff (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (d : ℕ) :
    (∀ p ∈ S, p ∣ d) ↔ (∏ p ∈ S, p) ∣ d :=
  ⟨fun h => Finset.prod_primes_dvd d (fun p hp => (hS p hp).prime) h,
   fun h p hp => (Finset.dvd_prod_of_mem _ hp).trans h⟩

/-- **Off-diagonal control for fixed `t`.** For decreasing nonnegative `f`:
`∑_{t<u≤T} f(u) · ∏_{p≤t, p ∣ u−t} p/(p−1) ≤ e · ∑_{t<u≤T} f(u)`. -/
theorem off_diag (f : ℕ → ℝ) (hf : Antitone f) (hf0 : ∀ n, 0 ≤ f n) (t T : ℕ) :
    ∑ u ∈ Ioc t T, f u * ∏ p ∈ (Nat.primesLE t).filter (fun p => p ∣ u - t), (p : ℝ) / ((p : ℝ) - 1) ≤
      Real.exp 1 * ∑ u ∈ Ioc t T, f u := by
  classical
  have hP : ∀ p ∈ Nat.primesLE t, p.Prime := fun p hp => (mem_primesLE.mp hp).2
  -- expand and swap
  have hexp : ∀ u, ∏ p ∈ (Nat.primesLE t).filter (fun p => p ∣ u - t), (p : ℝ) / ((p : ℝ) - 1) =
      ∑ S ∈ (Nat.primesLE t).powerset,
        (if (∏ p ∈ S, p) ∣ u - t then 1 / ((∏ p ∈ S, p).totient : ℝ) else 0) := by
    intro u
    rw [expand _ (fun p hp => hP p (mem_filter.mp hp).1), ← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext S
    simp only [mem_powerset, mem_filter]
    constructor
    · intro hS
      have hSs : S ⊆ Nat.primesLE t := hS.trans (filter_subset _ _)
      exact ⟨hSs, (all_dvd_iff S (fun p hp => hP p (hSs hp)) _).mp (fun p hp => (mem_filter.mp (hS hp)).2)⟩
    · rintro ⟨hSs, hd⟩ p hp
      exact mem_filter.mpr ⟨hSs hp, (all_dvd_iff S (fun p hp => hP p (hSs hp)) _).mpr hd p hp⟩
  simp_rw [hexp, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hstep : ∀ S ∈ (Nat.primesLE t).powerset,
      ∑ u ∈ Ioc t T, f u * (if (∏ p ∈ S, p) ∣ u - t then 1 / ((∏ p ∈ S, p).totient : ℝ) else 0) ≤
        1 / (((∏ p ∈ S, p : ℕ) : ℝ) * ((∏ p ∈ S, p).totient : ℝ)) * ∑ u ∈ Ioc t T, f u := by
    intro S hS
    have hSs : S ⊆ Nat.primesLE t := mem_powerset.mp hS
    have hepos : 0 < ∏ p ∈ S, p := Finset.prod_pos (fun p hp => (hP p (hSs hp)).pos)
    have hphi : (0 : ℝ) < ((∏ p ∈ S, p).totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hepos
    have hsf := sparse_filter f hf hf0 t T (∏ p ∈ S, p) hepos
    calc ∑ u ∈ Ioc t T, f u * (if (∏ p ∈ S, p) ∣ u - t then 1 / ((∏ p ∈ S, p).totient : ℝ) else 0)
        = (1 / ((∏ p ∈ S, p).totient : ℝ)) * ∑ u ∈ (Ioc t T).filter (fun u => (∏ p ∈ S, p) ∣ u - t), f u := by
          rw [Finset.mul_sum, Finset.sum_filter]
          refine Finset.sum_congr rfl fun u _ => ?_
          split_ifs <;> ring
      _ ≤ (1 / ((∏ p ∈ S, p).totient : ℝ)) * ((1 / ((∏ p ∈ S, p : ℕ) : ℝ)) * ∑ u ∈ Ioc t T, f u) :=
          mul_le_mul_of_nonneg_left hsf (by positivity)
      _ = _ := by field_simp
  calc ∑ S ∈ (Nat.primesLE t).powerset, ∑ u ∈ Ioc t T,
        f u * (if (∏ p ∈ S, p) ∣ u - t then 1 / ((∏ p ∈ S, p).totient : ℝ) else 0)
      ≤ ∑ S ∈ (Nat.primesLE t).powerset,
          1 / (((∏ p ∈ S, p : ℕ) : ℝ) * ((∏ p ∈ S, p).totient : ℝ)) * ∑ u ∈ Ioc t T, f u :=
        Finset.sum_le_sum hstep
    _ = (∏ p ∈ Nat.primesLE t, (1 + 1 / ((p : ℝ) * ((p : ℝ) - 1)))) * ∑ u ∈ Ioc t T, f u := by
        rw [← Finset.sum_mul, expand2 _ hP]
    _ ≤ Real.exp 1 * ∑ u ∈ Ioc t T, f u :=
        mul_le_mul_of_nonneg_right (prod_le_exp_one _ hP)
          (Finset.sum_nonneg fun u _ => hf0 u)
    _ = _ := by rw [Finset.mul_sum]

end E460Second3


namespace E460Second4
open Finset E460Second E460Second2 E460Second3 E460PairFull

noncomputable def rho (t : ℕ) : ℝ := ((primorial t).totient : ℝ) / (primorial t : ℝ)

lemma rho_nonneg (t : ℕ) : 0 ≤ rho t := by unfold rho; positivity

lemma rho_anti : Antitone rho := by
  intro u v huv
  unfold rho
  rw [rho_eq, rho_eq]
  have hsub : Nat.primesLE u ⊆ Nat.primesLE v := by
    intro p hp; rw [mem_primesLE] at hp ⊢; exact ⟨by omega, hp.2⟩
  have hfac : ∀ p ∈ Nat.primesLE v, 0 ≤ 1 - (p : ℝ)⁻¹ ∧ 1 - (p : ℝ)⁻¹ ≤ 1 := by
    intro p hp
    have : (2 : ℝ) ≤ p := by exact_mod_cast (mem_primesLE.mp hp).2.two_le
    have h1 : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    have h2 : 0 ≤ (p : ℝ)⁻¹ := by positivity
    constructor <;> linarith
  rw [← Finset.prod_sdiff hsub]
  have hA : ∏ p ∈ Nat.primesLE v \ Nat.primesLE u, (1 - (p : ℝ)⁻¹) ≤ 1 :=
    Finset.prod_le_one (fun p hp => (hfac p (mem_sdiff.mp hp).1).1) (fun p hp => (hfac p (mem_sdiff.mp hp).1).2)
  have hB : 0 ≤ ∏ p ∈ Nat.primesLE u, (1 - (p : ℝ)⁻¹) :=
    Finset.prod_nonneg (fun p hp => (hfac p (hsub hp)).1)
  calc (∏ p ∈ Nat.primesLE v \ Nat.primesLE u, (1 - (p : ℝ)⁻¹)) * ∏ p ∈ Nat.primesLE u, (1 - (p : ℝ)⁻¹)
      ≤ 1 * ∏ p ∈ Nat.primesLE u, (1 - (p : ℝ)⁻¹) := mul_le_mul_of_nonneg_right hA hB
    _ = _ := one_mul _

/-- `f u = ρ_u / max u 1`: decreasing and nonnegative. -/
noncomputable def f (u : ℕ) : ℝ := rho u / (max u 1 : ℕ)

lemma f_nonneg (u : ℕ) : 0 ≤ f u := by unfold f; exact div_nonneg (rho_nonneg u) (Nat.cast_nonneg _)

lemma f_anti : Antitone f := by
  intro u v huv
  unfold f
  have h1 : (0 : ℝ) < (max u 1 : ℕ) := by exact_mod_cast (show 0 < max u 1 by omega)
  have h2 : ((max u 1 : ℕ) : ℝ) ≤ (max v 1 : ℕ) := by exact_mod_cast (show max u 1 ≤ max v 1 by omega)
  calc rho v / ((max v 1 : ℕ) : ℝ) ≤ rho u / ((max v 1 : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right (rho_anti huv) (le_trans h1.le h2)
    _ ≤ rho u / ((max u 1 : ℕ) : ℝ) := div_le_div_of_nonneg_left (rho_nonneg u) h1 h2

/-- **Off-diagonal second-moment bound.** For `T ≤ N`, with blocks of length `P_T` starting at `N`:
`∑_{1≤t≤T} ∑_{t<u≤T} (#both rough)/(P_T · t · u) ≤ e · (∑_{1≤t≤T} ρ_t / t)²`. -/
theorem off_diag_total (T N : ℕ) (hN : T ≤ N) :
    ∑ t ∈ Icc 1 T, ∑ u ∈ Ioc t T,
      ((#{n ∈ Ico N (N + primorial T) |
          Nat.Coprime (primorial t) (n - t) ∧ Nat.Coprime (primorial u) (n - u)} : ℕ) : ℝ) /
        (primorial T : ℝ) * (1 / ((t : ℝ) * u)) ≤
      Real.exp 1 * (∑ t ∈ Icc 1 T, rho t / t) ^ 2 := by
  classical
  have hfu : ∀ u ∈ Ioc 0 T, f u = rho u / u := by
    intro u hu
    have : 1 ≤ u := (mem_Ioc.mp hu).1
    unfold f; rw [show max u 1 = u by omega]
  have hfinal : Real.exp 1 * (∑ t ∈ Icc 1 T, rho t / t) ^ 2 =
      ∑ t ∈ Icc 1 T, Real.exp 1 * (rho t / t * ∑ u ∈ Icc 1 T, rho u / u) := by
    rw [← Finset.mul_sum, ← Finset.sum_mul, sq]
  rw [hfinal]
  refine Finset.sum_le_sum fun t ht => ?_
  have ht1 : 1 ≤ t := (mem_Icc.mp ht).1
  have htT : t ≤ T := (mem_Icc.mp ht).2
  have htR : (0 : ℝ) < t := by exact_mod_cast ht1
  -- termwise pair bound
  have hterm : ∀ u ∈ Ioc t T,
      ((#{n ∈ Ico N (N + primorial T) |
          Nat.Coprime (primorial t) (n - t) ∧ Nat.Coprime (primorial u) (n - u)} : ℕ) : ℝ) /
        (primorial T : ℝ) * (1 / ((t : ℝ) * u)) ≤
      (rho t / t) * (f u * ∏ p ∈ (Nat.primesLE t).filter (fun p => p ∣ u - t), (p : ℝ) / ((p : ℝ) - 1)) := by
    intro u hu
    have htu : t < u := (mem_Ioc.mp hu).1
    have huT : u ≤ T := (mem_Ioc.mp hu).2
    have hpb := pair_prob_le t u T N htu huT (by omega)
    have huR : (0 : ℝ) < u := by exact_mod_cast (show 0 < u by omega)
    rw [hfu u (mem_Ioc.mpr ⟨by omega, huT⟩)]
    have hnn : (0 : ℝ) ≤ 1 / ((t : ℝ) * u) := by positivity
    calc _ ≤ (rho t * rho u * ∏ p ∈ (Nat.primesLE t).filter (fun p => p ∣ u - t), (p : ℝ) / ((p : ℝ) - 1)) *
            (1 / ((t : ℝ) * u)) := mul_le_mul_of_nonneg_right hpb hnn
      _ = _ := by unfold rho; field_simp
  calc ∑ u ∈ Ioc t T, ((#{n ∈ Ico N (N + primorial T) |
          Nat.Coprime (primorial t) (n - t) ∧ Nat.Coprime (primorial u) (n - u)} : ℕ) : ℝ) /
        (primorial T : ℝ) * (1 / ((t : ℝ) * u)) ≤ ∑ u ∈ Ioc t T,
        (rho t / t) * (f u * ∏ p ∈ (Nat.primesLE t).filter (fun p => p ∣ u - t), (p : ℝ) / ((p : ℝ) - 1)) :=
        Finset.sum_le_sum hterm
    _ = (rho t / t) * ∑ u ∈ Ioc t T,
        f u * ∏ p ∈ (Nat.primesLE t).filter (fun p => p ∣ u - t), (p : ℝ) / ((p : ℝ) - 1) := by
        rw [Finset.mul_sum]
    _ ≤ (rho t / t) * (Real.exp 1 * ∑ u ∈ Ioc t T, f u) :=
        mul_le_mul_of_nonneg_left (off_diag f f_anti f_nonneg t T) (div_nonneg (rho_nonneg t) htR.le)
    _ ≤ (rho t / t) * (Real.exp 1 * ∑ u ∈ Icc 1 T, rho u / u) := by
        apply mul_le_mul_of_nonneg_left _ (div_nonneg (rho_nonneg t) htR.le)
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos 1).le
        calc ∑ u ∈ Ioc t T, f u = ∑ u ∈ Ioc t T, rho u / u :=
              Finset.sum_congr rfl fun u hu => hfu u (mem_Ioc.mpr ⟨by have := (mem_Ioc.mp hu).1; omega, (mem_Ioc.mp hu).2⟩)
          _ ≤ ∑ u ∈ Icc 1 T, rho u / u :=
              Finset.sum_le_sum_of_subset_of_nonneg
                (fun u hu => mem_Icc.mpr ⟨by have := (mem_Ioc.mp hu).1; omega, (mem_Ioc.mp hu).2⟩)
                (fun u _ _ => div_nonneg (rho_nonneg u) (Nat.cast_nonneg u))
    _ = Real.exp 1 * (rho t / t * ∑ u ∈ Icc 1 T, rho u / u) := by ring

end E460Second4

namespace E460PZ
open Finset Filter E460Gap E460Second4

/-- `(Σ g)² = Σ g² + 2 Σ_{t<u} g t g u` over `Icc 1 T`. -/
lemma sq_expand (g : ℕ → ℝ) (T : ℕ) :
    (∑ t ∈ Icc 1 T, g t) ^ 2 = ∑ t ∈ Icc 1 T, g t ^ 2 + 2 * ∑ t ∈ Icc 1 T, ∑ u ∈ Ioc t T, g t * g u := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega),
      Finset.sum_Icc_succ_top (by omega), Finset.Ioc_self, Finset.sum_empty, add_zero]
    have hin : ∀ t ∈ Icc 1 T, ∑ u ∈ Ioc t (T + 1), g t * g u = ∑ u ∈ Ioc t T, g t * g u + g t * g (T + 1) := by
      intro t ht; rw [Finset.sum_Ioc_succ_top (mem_Icc.mp ht).2]
    rw [Finset.sum_congr rfl hin, Finset.sum_add_distrib, ← Finset.sum_mul]
    have := ih
    nlinarith [this]

lemma inv_sq_sum_le (T : ℕ) : ∑ t ∈ Icc 1 T, (1 : ℝ) / ((t : ℝ) * t) ≤ 2 := by
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · simp
  have hsplit : Icc 1 T = insert 1 (Icc 2 T) := by
    ext x; simp only [mem_Icc, mem_insert]; omega
  rw [hsplit, Finset.sum_insert (by simp)]
  have hle : ∑ t ∈ Icc 2 T, (1 : ℝ) / ((t : ℝ) * t) ≤ ∑ t ∈ Icc 2 T, 1 / ((t : ℝ) * ((t : ℝ) - 1)) := by
    refine Finset.sum_le_sum fun t ht => ?_
    have h2 : (2 : ℝ) ≤ t := by exact_mod_cast (mem_Icc.mp ht).1
    apply one_div_le_one_div_of_le (by nlinarith); nlinarith
  rw [E460Second2.telescope T hT] at hle
  have h0 : (0 : ℝ) ≤ (T : ℝ)⁻¹ := by positivity
  norm_num at hle ⊢; linarith

/-- The `t`-th term of `ST`. -/
noncomputable def a (t n : ℕ) : ℝ := if (primorial t).Coprime (n - t) then (1 : ℝ) / t else 0

lemma ST_eq (T n : ℕ) : E460Gap.ST T n = ∑ t ∈ Icc 1 T, a t n := rfl

/-- **Second moment.** For `N ≥ T`: `Σ_{n in block} ST(n)² ≤ P_T · (2 + 2e·C(T)²)`. -/
theorem second_moment (T N : ℕ) (hN : T ≤ N) :
    ∑ n ∈ Ico N (N + primorial T), (E460Gap.ST T n) ^ 2 ≤
      (primorial T : ℝ) * (2 + 2 * Real.exp 1 * (∑ t ∈ Icc 1 T, rho t / t) ^ 2) := by
  classical
  set C := ∑ t ∈ Icc 1 T, rho t / t with hC
  have hP : (0 : ℝ) < primorial T := by exact_mod_cast primorial_pos T
  have hpt : ∀ n t u, a t n * a u n =
      (if (primorial t).Coprime (n - t) ∧ (primorial u).Coprime (n - u) then 1 / ((t : ℝ) * u) else 0) := by
    intro n t u; unfold a; split_ifs <;> simp_all <;> field_simp
  have hsq : ∀ n t, a t n ^ 2 ≤ 1 / ((t : ℝ) * t) := by
    intro n t; unfold a; split_ifs
    · rw [div_pow, one_pow, sq]
    · rw [sq, mul_zero]; positivity
  simp_rw [ST_eq, sq_expand, Finset.sum_add_distrib]
  have hdiag : ∑ n ∈ Ico N (N + primorial T), ∑ t ∈ Icc 1 T, a t n ^ 2 ≤ (primorial T : ℝ) * 2 := by
    calc ∑ n ∈ Ico N (N + primorial T), ∑ t ∈ Icc 1 T, a t n ^ 2
        ≤ ∑ n ∈ Ico N (N + primorial T), ∑ t ∈ Icc 1 T, 1 / ((t : ℝ) * t) :=
          Finset.sum_le_sum fun n _ => Finset.sum_le_sum fun t _ => hsq n t
      _ = (primorial T : ℝ) * ∑ t ∈ Icc 1 T, 1 / ((t : ℝ) * t) := by
          rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.add_sub_cancel_left]
      _ ≤ _ := mul_le_mul_of_nonneg_left (inv_sq_sum_le T) hP.le
  have hoff : ∑ n ∈ Ico N (N + primorial T), 2 * ∑ t ∈ Icc 1 T, ∑ u ∈ Ioc t T, a t n * a u n ≤
      2 * ((primorial T : ℝ) * (Real.exp 1 * (∑ t ∈ Icc 1 T, rho t / t) ^ 2)) := by
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    have hot := off_diag_total T N hN
    calc ∑ n ∈ Ico N (N + primorial T), ∑ t ∈ Icc 1 T, ∑ u ∈ Ioc t T, a t n * a u n
        = ∑ t ∈ Icc 1 T, ∑ u ∈ Ioc t T, ∑ n ∈ Ico N (N + primorial T), a t n * a u n := by
          rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun t _ => Finset.sum_comm
      _ = ∑ t ∈ Icc 1 T, ∑ u ∈ Ioc t T,
            ((#{n ∈ Ico N (N + primorial T) |
              Nat.Coprime (primorial t) (n - t) ∧ Nat.Coprime (primorial u) (n - u)} : ℕ) : ℝ) *
              (1 / ((t : ℝ) * u)) := by
          refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun u _ => ?_
          simp_rw [hpt]
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      _ = (primorial T : ℝ) * ∑ t ∈ Icc 1 T, ∑ u ∈ Ioc t T,
            ((#{n ∈ Ico N (N + primorial T) |
              Nat.Coprime (primorial t) (n - t) ∧ Nat.Coprime (primorial u) (n - u)} : ℕ) : ℝ) /
              (primorial T : ℝ) * (1 / ((t : ℝ) * u)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun u _ => ?_
          field_simp
      _ ≤ (primorial T : ℝ) * (Real.exp 1 * (∑ t ∈ Icc 1 T, rho t / t) ^ 2) :=
          mul_le_mul_of_nonneg_left hot hP.le
  have hring : (primorial T : ℝ) * (2 + 2 * Real.exp 1 * (∑ t ∈ Icc 1 T, rho t / t) ^ 2) =
      (primorial T : ℝ) * 2 + 2 * ((primorial T : ℝ) * (Real.exp 1 * (∑ t ∈ Icc 1 T, rho t / t) ^ 2)) := by ring
  linarith [hdiag, hoff, hring]

lemma C_ge_one (T : ℕ) (hT : 1 ≤ T) : 1 ≤ ∑ t ∈ Icc 1 T, rho t / t := by
  have h1 : rho 1 / (1 : ℕ) = 1 := by
    unfold rho; rw [show primorial 1 = 1 by decide]; simp
  calc (1 : ℝ) = rho 1 / (1 : ℕ) := h1.symm
    _ ≤ ∑ t ∈ Icc 1 T, rho t / t :=
      Finset.single_le_sum (fun t _ => div_nonneg (rho_nonneg t) (Nat.cast_nonneg t))
        (mem_Icc.mpr ⟨le_rfl, hT⟩)

/-- **Paley–Zygmund for the truncated rough sum.** For `T ≥ 1` and `N ≥ T`, at least a proportion
`1/(8(1+e))` of every block of `P_T` consecutive `n ≥ N` has `ST(n) ≥ C(T)/2`. -/
theorem pz (T N : ℕ) (hT : 1 ≤ T) (hN : T ≤ N) :
    (primorial T : ℝ) / (8 * (1 + Real.exp 1)) ≤
      #{n ∈ Ico N (N + primorial T) | (∑ t ∈ Icc 1 T, rho t / t) / 2 ≤ E460Gap.ST T n} := by
  classical
  set C := ∑ t ∈ Icc 1 T, rho t / t with hC
  set s := Ico N (N + primorial T) with hs
  set P : ℝ := (primorial T : ℝ) with hPdef
  have hP : 0 < P := by rw [hPdef]; exact_mod_cast primorial_pos T
  have hcard : (s.card : ℝ) = P := by rw [hs, Nat.card_Ico, Nat.add_sub_cancel_left]
  have hC1 : 1 ≤ C := C_ge_one T hT
  -- mean
  have hmean : ∑ n ∈ s, E460Gap.ST T n = P * C := by
    have h1 := E460Avg.mean T N hN
    have h2 := E460Cond.C_eq T
    have hCC : E460Cond.C T = C := by rw [hC]; rfl
    rw [hCC] at h2
    unfold E460Gap.ST
    have hPne : ((primorial T : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (primorial_pos T).ne'
    rw [h1, ← h2, hPdef]
    field_simp
  set A := s.filter (fun n => C / 2 ≤ E460Gap.ST T n) with hA
  have hSTnn : ∀ n, 0 ≤ E460Gap.ST T n := fun n =>
    Finset.sum_nonneg fun t _ => by split_ifs <;> positivity
  -- mass on A
  have hmass : P * C / 2 ≤ ∑ n ∈ A, E460Gap.ST T n := by
    have hsplit := Finset.sum_filter_add_sum_filter_not s (fun n => C / 2 ≤ E460Gap.ST T n) (E460Gap.ST T)
    have hnot : ∑ n ∈ s.filter (fun n => ¬ C / 2 ≤ E460Gap.ST T n), E460Gap.ST T n ≤ P * (C / 2) := by
      calc _ ≤ ∑ n ∈ s.filter (fun n => ¬ C / 2 ≤ E460Gap.ST T n), C / 2 :=
            Finset.sum_le_sum fun n hn => le_of_lt (not_le.mp (mem_filter.mp hn).2)
        _ = ((s.filter (fun n => ¬ C / 2 ≤ E460Gap.ST T n)).card : ℝ) * (C / 2) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (s.card : ℝ) * (C / 2) := by
            apply mul_le_mul_of_nonneg_right _ (by linarith)
            exact_mod_cast Finset.card_filter_le _ _
        _ = P * (C / 2) := by rw [hcard]
    rw [hmean] at hsplit
    linarith
  -- Cauchy–Schwarz
  have hcs : (∑ n ∈ A, E460Gap.ST T n) ^ 2 ≤ (A.card : ℝ) * ∑ n ∈ A, (E460Gap.ST T n) ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq A (fun _ => (1 : ℝ)) (E460Gap.ST T)
    simpa using this
  have hsub : ∑ n ∈ A, (E460Gap.ST T n) ^ 2 ≤ ∑ n ∈ s, (E460Gap.ST T n) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun n _ _ => sq_nonneg _)
  have hsm := second_moment T N hN
  rw [← hs, ← hPdef, ← hC] at hsm
  have hAnn : (0 : ℝ) ≤ A.card := Nat.cast_nonneg _
  have hkey : (P * C / 2) ^ 2 ≤ (A.card : ℝ) * (P * (2 + 2 * Real.exp 1 * C ^ 2)) := by
    calc (P * C / 2) ^ 2 ≤ (∑ n ∈ A, E460Gap.ST T n) ^ 2 := by
          apply pow_le_pow_left₀ (by positivity) hmass
      _ ≤ (A.card : ℝ) * ∑ n ∈ A, (E460Gap.ST T n) ^ 2 := hcs
      _ ≤ (A.card : ℝ) * (P * (2 + 2 * Real.exp 1 * C ^ 2)) :=
          mul_le_mul_of_nonneg_left (hsub.trans hsm) hAnn
  -- divide by P and compare
  have hk2 : P * C ^ 2 / 4 ≤ (A.card : ℝ) * (2 + 2 * Real.exp 1 * C ^ 2) := by
    have : (P * C / 2) ^ 2 = P * (P * C ^ 2 / 4) := by ring
    rw [this, show (A.card : ℝ) * (P * (2 + 2 * Real.exp 1 * C ^ 2)) =
      P * ((A.card : ℝ) * (2 + 2 * Real.exp 1 * C ^ 2)) by ring] at hkey
    exact le_of_mul_le_mul_left hkey hP
  have hC2 : 1 ≤ C ^ 2 := by nlinarith
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hk3 : P * C ^ 2 / 4 ≤ (A.card : ℝ) * (2 * (1 + Real.exp 1)) * C ^ 2 := by
    have : (A.card : ℝ) * (2 + 2 * Real.exp 1 * C ^ 2) ≤ (A.card : ℝ) * (2 * (1 + Real.exp 1)) * C ^ 2 := by
      have : 2 + 2 * Real.exp 1 * C ^ 2 ≤ 2 * (1 + Real.exp 1) * C ^ 2 := by nlinarith
      calc (A.card : ℝ) * (2 + 2 * Real.exp 1 * C ^ 2) ≤ (A.card : ℝ) * (2 * (1 + Real.exp 1) * C ^ 2) :=
            mul_le_mul_of_nonneg_left this hAnn
        _ = _ := by ring
    linarith
  have hk4 : P / 4 ≤ (A.card : ℝ) * (2 * (1 + Real.exp 1)) := by
    have hCpos : 0 < C ^ 2 := by linarith
    have : P / 4 * C ^ 2 ≤ (A.card : ℝ) * (2 * (1 + Real.exp 1)) * C ^ 2 := by linarith
    exact le_of_mul_le_mul_right this hCpos
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- **Fixed positive proportion for every threshold.** For every `B` there is `T` such that every block
of `P_T` consecutive `n > T` contains at least `P_T / (8(1+e))` integers with `partialSum n ≥ B`. -/
theorem uniform_proportion (B : ℝ) :
    ∃ T : ℕ, ∀ N : ℕ, T < N →
      (primorial T : ℝ) / (8 * (1 + Real.exp 1)) ≤
        #{n ∈ Ico N (N + primorial T) | B ≤ OMA.S_erdos_460.partialSum n} := by
  classical
  obtain ⟨T, hT⟩ := (((E460Mertens.C_tendsto E460Final.mertens_lower).eventually_ge_atTop (2 * B)).and
    (eventually_ge_atTop 1)).exists
  refine ⟨T, fun N hN => (pz T N hT.2 hN.le).trans ?_⟩
  have hCC : E460Cond.C T = ∑ t ∈ Icc 1 T, rho t / t := rfl
  exact_mod_cast Finset.card_le_card (fun n hn => by
    rw [mem_filter] at hn ⊢
    refine ⟨hn.1, ?_⟩
    have h1 : T < n := lt_of_lt_of_le hN (mem_Ico.mp hn.1).1
    have h2 := trunc_le T n h1
    have h3 := hT.1
    rw [hCC] at h3
    linarith [hn.2])

end E460PZ


namespace E460ClassPair
open Finset E460CRT E460Pair

/-- **Affine period.** For `A` coprime to `M > 0`, any `c` and start `K₀`: as `k` runs over `M`
consecutive values, `(c + k·A) mod M` runs over all residues exactly once, so for any condition `Q`,
`#{k : Q ((c + kA) % M)} = #{x < M : Q x}`. -/
lemma affine_block (A M c K0 : ℕ) (hM : 0 < M) (hAM : Nat.Coprime A M) (Q : ℕ → Prop) [DecidablePred Q] :
    #{k ∈ Ico K0 (K0 + M) | Q ((c + k * A) % M)} = #{x ∈ range M | Q x} := by
  set f : ℕ → ℕ := fun k => (c + k * A) % M with hf
  have hinj : Set.InjOn f (Ico K0 (K0 + M)) := by
    intro k1 h1 k2 h2 h12
    simp only [coe_Ico, Set.mem_Ico] at h1 h2
    have hm : c + k1 * A ≡ c + k2 * A [MOD M] := h12
    have hm2 : k1 * A ≡ k2 * A [MOD M] := Nat.ModEq.add_left_cancel' c hm
    have hm3 : k1 ≡ k2 [MOD M] := Nat.ModEq.cancel_right_of_coprime (by rw [Nat.gcd_comm]; exact hAM) hm2
    obtain ⟨a, rfl⟩ : ∃ a, k1 = K0 + a := ⟨k1 - K0, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, k2 = K0 + b := ⟨k2 - K0, by omega⟩
    have hab : a ≡ b [MOD M] := Nat.ModEq.add_left_cancel' K0 hm3
    unfold Nat.ModEq at hab
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hab
    omega
  have himg : (Ico K0 (K0 + M)).image f = range M := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy; obtain ⟨k, -, rfl⟩ := mem_image.mp hy; exact mem_range.mpr (Nat.mod_lt _ hM)
    · rw [card_image_of_injOn hinj, card_range, Nat.card_Ico]; omega
  rw [← himg, filter_image, card_image_of_injOn (hinj.mono (filter_subset _ _))]

lemma affine_blocks (A M c K0 m : ℕ) (hM : 0 < M) (hAM : Nat.Coprime A M) (Q : ℕ → Prop) [DecidablePred Q] :
    #{k ∈ Ico K0 (K0 + m * M) | Q ((c + k * A) % M)} = m * #{x ∈ range M | Q x} := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show K0 + (m + 1) * M = (K0 + m * M) + M by ring,
      ← Finset.Ico_union_Ico_eq_Ico (b := K0 + m * M) (by omega) (by omega), Finset.filter_union,
      Finset.card_union_of_disjoint
        (Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive _ _ _)),
      ih, affine_block A M c _ hM hAM Q]
    ring

/-- The primes in `(R, u]`. -/
def mid (R u : ℕ) : Finset ℕ := (Nat.primesLE u).filter (fun p => R < p)

lemma prod_mid (R u : ℕ) : ∏ p ∈ mid R u, p = E460CRTPrimorial.Qt R u := rfl

/-- **Class pair count.** Let `A = P_R`, `R ≤ t ≤ u ≤ r`, with `A` coprime to `r − t` and to `r − u`
(e.g. `t ≡ u ≡ r − 1 mod A`). Over `m·Q_u` consecutive `k` (`Q_u` = product of the primes in `(R,u]`),
the number of `k` for which both `n − t` and `n − u` are rough, `n = r + k·A`, is
`m · ∏_{R<p≤u} (if p ≤ t then (if t ≡ u mod p then p − 1 else p − 2) else p − 1)`. -/
theorem class_pair_count (R t u r K0 m : ℕ) (hRt : R ≤ t) (htu : t ≤ u) (hur : u ≤ r)
    (hct : Nat.Coprime (primorial R) (r - t)) (hcu : Nat.Coprime (primorial R) (r - u)) :
    #{k ∈ Ico K0 (K0 + m * E460CRTPrimorial.Qt R u) |
        Nat.Coprime (primorial t) (r + k * primorial R - t) ∧
          Nat.Coprime (primorial u) (r + k * primorial R - u)} =
      m * ∏ p ∈ mid R u, (if p ≤ t then (if t % p = u % p then p - 1 else p - 2) else p - 1) := by
  classical
  set A := primorial R with hA
  set Qu := E460CRTPrimorial.Qt R u with hQu
  have hQpos : 0 < Qu := Finset.prod_pos (fun p hp =>
    (E460CRTPrimorial.mem_primesLE.mp (mem_filter.mp hp).1).2.pos)
  have hAQ : Nat.Coprime A Qu := E460CRTPrimorial.coprime_split R u
  have hmidP : ∀ p ∈ mid R u, p.Prime := fun p hp => (E460CRTPrimorial.mem_primesLE.mp (mem_filter.mp hp).1).2
  set B : ℕ → ℕ → Prop := fun p x => (p ≤ t → x ≠ t % p) ∧ x ≠ u % p with hB
  -- the event depends only on (r + kA) % Qu
  have hev : ∀ k, (Nat.Coprime (primorial t) (r + k * A - t) ∧ Nat.Coprime (primorial u) (r + k * A - u)) ↔
      (fun x => ∀ p ∈ mid R u, B p (x % p)) ((r + k * A) % Qu) := by
    intro k
    have hsingle : ∀ p s, s ≤ r + k * A → (¬ p ∣ r + k * A - s ↔ (r + k * A) % p ≠ s % p) := by
      intro p s hs
      rw [← Nat.modEq_iff_dvd' hs]; unfold Nat.ModEq
      exact ⟨fun h h' => h h'.symm, fun h h' => h h'.symm⟩
    have hsmall : ∀ p s, p.Prime → p ≤ R → s ≤ r → Nat.Coprime A (r - s) → ¬ p ∣ r + k * A - s := by
      intro p s hp hpR hs hcop hd
      have hpA : p ∣ A := by
        rw [hA, primorial_eq_prod_primesLE]
        exact Finset.dvd_prod_of_mem _ (E460CRTPrimorial.mem_primesLE.mpr ⟨hpR, hp⟩)
      have : p ∣ r - s := by
        have h2 : p ∣ k * A := Dvd.dvd.mul_left hpA k
        rw [show r + k * A - s = (r - s) + k * A by omega] at hd
        exact (Nat.dvd_add_right h2).mp (by rwa [add_comm] at hd)
      exact Nat.not_coprime_of_dvd_of_dvd hp.one_lt hpA this hcop
    have hdiv : ∀ p ∈ mid R u, ((r + k * A) % Qu) % p = (r + k * A) % p := fun p hp =>
      Nat.mod_mod_of_dvd _ (Finset.dvd_prod_of_mem _ hp)
    simp only [E460PairFull.coprime_primorial_iff, hB]
    constructor
    · rintro ⟨h1, h2⟩ p hp
      have hpu := (mem_filter.mp hp).1
      obtain ⟨hpu', hpp⟩ := E460CRTPrimorial.mem_primesLE.mp hpu
      rw [hdiv p hp]
      exact ⟨fun hpt => (hsingle p t (by omega)).mp (h1 p (E460CRTPrimorial.mem_primesLE.mpr ⟨hpt, hpp⟩)),
        (hsingle p u (by omega)).mp (h2 p hpu)⟩
    · intro h
      refine ⟨fun p hp => ?_, fun p hp => ?_⟩
      · obtain ⟨hpt, hpp⟩ := E460CRTPrimorial.mem_primesLE.mp hp
        by_cases hpR : p ≤ R
        · exact hsmall p t hpp hpR (by omega) hct
        · have hpm : p ∈ mid R u := mem_filter.mpr ⟨E460CRTPrimorial.mem_primesLE.mpr ⟨by omega, hpp⟩, by omega⟩
          have := (h p hpm).1 hpt
          rw [hdiv p hpm] at this
          exact (hsingle p t (by omega)).mpr this
      · obtain ⟨hpu, hpp⟩ := E460CRTPrimorial.mem_primesLE.mp hp
        by_cases hpR : p ≤ R
        · exact hsmall p u hpp hpR hur hcu
        · have hpm : p ∈ mid R u := mem_filter.mpr ⟨hp, by omega⟩
          have := (h p hpm).2
          rw [hdiv p hpm] at this
          exact (hsingle p u (by omega)).mpr this
  rw [Finset.filter_congr (fun k _ => hev k)]
  have hcrt := crt_primes (mid R u) hmidP B
  rw [prod_mid, ← hQu] at hcrt
  calc _ = m * #{x ∈ range Qu | ∀ p ∈ mid R u, B p (x % p)} := by
        convert affine_blocks A Qu r K0 m hQpos hAQ (fun x => ∀ p ∈ mid R u, B p (x % p)) using 2
    _ = m * ∏ p ∈ mid R u, #{x ∈ range p | B p x} := by congr 1
    _ = _ := by
      congr 1
      refine Finset.prod_congr rfl fun p hp => ?_
      have hpp := hmidP p hp
      by_cases hpt : p ≤ t
      · rw [if_pos hpt, ← prime_count p t u hpp]
        congr 1; apply filter_congr; intro x _
        simp only [hB]; exact ⟨fun h => ⟨h.1 hpt, h.2⟩, fun h => ⟨fun _ => h.1, h.2⟩⟩
      · rw [if_neg hpt]
        have hfil : (range p).filter (B p) = range p \ {u % p} := by
          ext x; simp only [mem_filter, mem_sdiff, mem_singleton, hB]
          exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, fun h' => absurd h' hpt, h.2⟩⟩
        rw [hfil, Finset.card_sdiff_of_subset (singleton_subset_iff.mpr (mem_range.mpr (Nat.mod_lt _ hpp.pos))),
          card_range, card_singleton]

end E460ClassPair


namespace E460ClassSecond
open Finset E460ClassPair E460Second E460Second2 E460Second3

/-- `ρ'_t = ∏_{R<p≤t} (1 − 1/p)`. -/
noncomputable def rho' (R t : ℕ) : ℝ := ∏ p ∈ mid R t, (1 - (p : ℝ)⁻¹)

lemma mid_prime {R t p : ℕ} (hp : p ∈ mid R t) : p.Prime :=
  (E460CRTPrimorial.mem_primesLE.mp (mem_filter.mp hp).1).2

/-- `ρ'_t = φ(Q_t)/Q_t`. -/
lemma rho'_eq (R t : ℕ) :
    rho' R t = ((E460CRTPrimorial.Qt R t).totient : ℝ) / (E460CRTPrimorial.Qt R t : ℝ) := by
  unfold rho'
  rw [← prod_mid, totient_prod_primes _ (fun p hp => mid_prime hp)]
  push_cast
  rw [← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun p hp => ?_
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (mid_prime hp).two_le
  rw [Nat.cast_sub (mid_prime hp).one_lt.le]; push_cast
  field_simp

lemma mid_filter (R t u : ℕ) (htu : t ≤ u) : (mid R u).filter (fun p => p ≤ t) = mid R t := by
  ext p; simp only [mid, mem_filter, E460CRTPrimorial.mem_primesLE]
  constructor
  · rintro ⟨⟨⟨_, h2⟩, h3⟩, h4⟩; exact ⟨⟨h4, h2⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨⟨by omega, h2⟩, h3⟩, h1⟩

/-- **Normalized class pair bound.** -/
theorem class_pair_prob_le (R t u r K0 m : ℕ) (hm : 0 < m) (hRt : R ≤ t) (htu : t < u) (hur : u ≤ r)
    (hct : Nat.Coprime (primorial R) (r - t)) (hcu : Nat.Coprime (primorial R) (r - u)) :
    ((#{k ∈ Ico K0 (K0 + m * E460CRTPrimorial.Qt R u) |
        Nat.Coprime (primorial t) (r + k * primorial R - t) ∧
          Nat.Coprime (primorial u) (r + k * primorial R - u)} : ℕ) : ℝ) /
        ((m : ℝ) * (E460CRTPrimorial.Qt R u : ℝ)) ≤
      rho' R t * rho' R u * ∏ p ∈ (mid R t).filter (fun p => p ∣ u - t), (p : ℝ) / ((p : ℝ) - 1) := by
  classical
  rw [class_pair_count R t u r K0 m hRt htu.le hur hct hcu]
  set U := mid R u with hU
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hQ : (E460CRTPrimorial.Qt R u : ℝ) = ∏ p ∈ U, (p : ℝ) := by
    rw [← prod_mid]; push_cast; rfl
  have hR : rho' R t * rho' R u *
      ∏ p ∈ (mid R t).filter (fun p => p ∣ u - t), (p : ℝ) / ((p : ℝ) - 1) =
      ∏ p ∈ U, ((if p ≤ t then (1 - (p : ℝ)⁻¹) else 1) * (1 - (p : ℝ)⁻¹) *
        (if p ≤ t ∧ p ∣ u - t then (p : ℝ) / ((p : ℝ) - 1) else 1)) := by
    unfold rho'
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, ← Finset.prod_filter, ← Finset.prod_filter,
      mid_filter R t u htu.le, ← mid_filter R t u htu.le, Finset.filter_filter, mid_filter R t u htu.le]
  rw [hR]
  push_cast
  calc (m : ℝ) * (∏ x ∈ U, if x ≤ t then (if t % x = u % x then ((x - 1 : ℕ) : ℝ) else ((x - 2 : ℕ) : ℝ))
          else ((x - 1 : ℕ) : ℝ)) / ((m : ℝ) * (E460CRTPrimorial.Qt R u : ℝ))
      = (∏ x ∈ U, if x ≤ t then (if t % x = u % x then ((x - 1 : ℕ) : ℝ) else ((x - 2 : ℕ) : ℝ))
          else ((x - 1 : ℕ) : ℝ)) / ∏ p ∈ U, (p : ℝ) := by
        rw [← hQ]; field_simp
    _ = ∏ x ∈ U, ((if x ≤ t then (if t % x = u % x then ((x - 1 : ℕ) : ℝ) else ((x - 2 : ℕ) : ℝ))
          else ((x - 1 : ℕ) : ℝ)) / (x : ℝ)) := (Finset.prod_div_distrib _ _).symm
    _ ≤ _ := by
        apply Finset.prod_le_prod
        · intro p hp
          apply div_nonneg _ (Nat.cast_nonneg _)
          split_ifs <;> exact Nat.cast_nonneg _
        · intro p hp
          have h2 := (mid_prime hp).two_le
          have hpR : (2 : ℝ) ≤ p := by exact_mod_cast h2
          have hp0 : (p : ℝ) ≠ 0 := by linarith
          have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
          have c1 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; norm_num
          have c2 : ((p - 2 : ℕ) : ℝ) = (p : ℝ) - 2 := by rw [Nat.cast_sub h2]; norm_num
          by_cases hpt : p ≤ t
          · have hiff : t % p = u % p ↔ p ∣ u - t := by
              rw [← Nat.modEq_iff_dvd' htu.le]; rfl
            by_cases hd : t % p = u % p
            · rw [if_pos hpt, if_pos hd, if_pos hpt, if_pos ⟨hpt, hiff.mp hd⟩, c1]
              apply le_of_eq; field_simp
            · rw [if_pos hpt, if_neg hd, if_pos hpt, if_neg (fun h => hd (hiff.mpr h.2)), c2]
              rw [mul_one, div_le_iff₀ (by linarith)]
              have : (1 - (p : ℝ)⁻¹) * (1 - (p : ℝ)⁻¹) * p = (p - 2) + 1 / p := by field_simp; ring
              rw [this]
              have : 0 < 1 / (p : ℝ) := by positivity
              linarith
          · rw [if_neg hpt, if_neg hpt, if_neg (fun h => hpt h.1), c1]
            apply le_of_eq; field_simp

/-- **`off_diag` for an arbitrary finite set of primes.** -/
theorem off_diag_gen (f : ℕ → ℝ) (hf : Antitone f) (hf0 : ∀ n, 0 ≤ f n) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) (i J : ℕ) :
    ∑ j ∈ Ioc i J, f j * ∏ p ∈ s.filter (fun p => p ∣ j - i), (p : ℝ) / ((p : ℝ) - 1) ≤
      Real.exp 1 * ∑ j ∈ Ioc i J, f j := by
  classical
  have hexp : ∀ j, ∏ p ∈ s.filter (fun p => p ∣ j - i), (p : ℝ) / ((p : ℝ) - 1) =
      ∑ S ∈ s.powerset, (if (∏ p ∈ S, p) ∣ j - i then 1 / ((∏ p ∈ S, p).totient : ℝ) else 0) := by
    intro j
    rw [expand _ (fun p hp => hs p (mem_filter.mp hp).1), ← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext S
    simp only [mem_powerset, mem_filter]
    constructor
    · intro hS
      have hSs : S ⊆ s := hS.trans (filter_subset _ _)
      exact ⟨hSs, (all_dvd_iff S (fun p hp => hs p (hSs hp)) _).mp (fun p hp => (mem_filter.mp (hS hp)).2)⟩
    · rintro ⟨hSs, hd⟩ p hp
      exact mem_filter.mpr ⟨hSs hp, (all_dvd_iff S (fun p hp => hs p (hSs hp)) _).mpr hd p hp⟩
  simp_rw [hexp, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hstep : ∀ S ∈ s.powerset,
      ∑ j ∈ Ioc i J, f j * (if (∏ p ∈ S, p) ∣ j - i then 1 / ((∏ p ∈ S, p).totient : ℝ) else 0) ≤
        1 / (((∏ p ∈ S, p : ℕ) : ℝ) * ((∏ p ∈ S, p).totient : ℝ)) * ∑ j ∈ Ioc i J, f j := by
    intro S hS
    have hSs : S ⊆ s := mem_powerset.mp hS
    have hepos : 0 < ∏ p ∈ S, p := Finset.prod_pos (fun p hp => (hs p (hSs hp)).pos)
    have hphi : (0 : ℝ) < ((∏ p ∈ S, p).totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hepos
    have hsf := sparse_filter f hf hf0 i J (∏ p ∈ S, p) hepos
    calc ∑ j ∈ Ioc i J, f j * (if (∏ p ∈ S, p) ∣ j - i then 1 / ((∏ p ∈ S, p).totient : ℝ) else 0)
        = (1 / ((∏ p ∈ S, p).totient : ℝ)) * ∑ j ∈ (Ioc i J).filter (fun j => (∏ p ∈ S, p) ∣ j - i), f j := by
          rw [Finset.mul_sum, Finset.sum_filter]
          refine Finset.sum_congr rfl fun j _ => ?_
          split_ifs <;> ring
      _ ≤ (1 / ((∏ p ∈ S, p).totient : ℝ)) * ((1 / ((∏ p ∈ S, p : ℕ) : ℝ)) * ∑ j ∈ Ioc i J, f j) :=
          mul_le_mul_of_nonneg_left hsf (by positivity)
      _ = _ := by field_simp
  calc ∑ S ∈ s.powerset, ∑ j ∈ Ioc i J,
        f j * (if (∏ p ∈ S, p) ∣ j - i then 1 / ((∏ p ∈ S, p).totient : ℝ) else 0)
      ≤ ∑ S ∈ s.powerset, 1 / (((∏ p ∈ S, p : ℕ) : ℝ) * ((∏ p ∈ S, p).totient : ℝ)) * ∑ j ∈ Ioc i J, f j :=
        Finset.sum_le_sum hstep
    _ = (∏ p ∈ s, (1 + 1 / ((p : ℝ) * ((p : ℝ) - 1)))) * ∑ j ∈ Ioc i J, f j := by
        rw [← Finset.sum_mul, expand2 _ hs]
    _ ≤ Real.exp 1 * ∑ j ∈ Ioc i J, f j :=
        mul_le_mul_of_nonneg_right (prod_le_exp_one _ hs) (Finset.sum_nonneg fun j _ => hf0 j)
    _ = _ := by rw [Finset.mul_sum]

/-- For offsets `t_i = a + i·P_R`, a prime `p > R` divides `t_j − t_i` iff it divides `j − i`. -/
lemma offset_dvd_iff (R a i j p : ℕ) (hij : i ≤ j) (hp : p.Prime) (hpR : R < p) :
    p ∣ (a + j * primorial R) - (a + i * primorial R) ↔ p ∣ j - i := by
  have hcop : Nat.Coprime p (primorial R) := by
    rw [primorial_eq_prod_primesLE]
    apply Nat.Coprime.prod_right
    intro q hq
    obtain ⟨hqR, hqp⟩ := E460CRTPrimorial.mem_primesLE.mp hq
    exact (Nat.coprime_primes hp hqp).mpr (by omega)
  rw [show (a + j * primorial R) - (a + i * primorial R) = (j - i) * primorial R by
    rw [Nat.sub_mul]; omega]
  exact ⟨fun h => hcop.dvd_of_dvd_mul_right h, fun h => Dvd.dvd.mul_right h _⟩

lemma Qt_dvd (R u T : ℕ) (h : u ≤ T) : E460CRTPrimorial.Qt R u ∣ E460CRTPrimorial.Qt R T := by
  rw [← prod_mid, ← prod_mid]
  apply Finset.prod_dvd_prod_of_subset
  intro p hp
  simp only [mid, mem_filter, E460CRTPrimorial.mem_primesLE] at hp ⊢
  exact ⟨⟨by omega, hp.1.2⟩, hp.2⟩

lemma rho'_nonneg (R t : ℕ) : 0 ≤ rho' R t :=
  Finset.prod_nonneg fun p hp => by
    have : (2 : ℝ) ≤ p := by exact_mod_cast (mid_prime hp).two_le
    have : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    linarith

lemma rho'_anti (R : ℕ) : Antitone (rho' R) := by
  intro u v huv
  unfold rho'
  have hsub : mid R u ⊆ mid R v := by
    intro p hp
    simp only [mid, mem_filter, E460CRTPrimorial.mem_primesLE] at hp ⊢
    exact ⟨⟨by omega, hp.1.2⟩, hp.2⟩
  have hfac : ∀ p ∈ mid R v, 0 ≤ 1 - (p : ℝ)⁻¹ ∧ 1 - (p : ℝ)⁻¹ ≤ 1 := by
    intro p hp
    have : (2 : ℝ) ≤ p := by exact_mod_cast (mid_prime hp).two_le
    have h1 : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    have h2 : 0 ≤ (p : ℝ)⁻¹ := by positivity
    constructor <;> linarith
  rw [← Finset.prod_sdiff hsub]
  have hA : ∏ p ∈ mid R v \ mid R u, (1 - (p : ℝ)⁻¹) ≤ 1 :=
    Finset.prod_le_one (fun p hp => (hfac p (mem_sdiff.mp hp).1).1) (fun p hp => (hfac p (mem_sdiff.mp hp).1).2)
  have hB : 0 ≤ ∏ p ∈ mid R u, (1 - (p : ℝ)⁻¹) := Finset.prod_nonneg (fun p hp => (hfac p (hsub hp)).1)
  calc (∏ p ∈ mid R v \ mid R u, (1 - (p : ℝ)⁻¹)) * ∏ p ∈ mid R u, (1 - (p : ℝ)⁻¹)
      ≤ 1 * ∏ p ∈ mid R u, (1 - (p : ℝ)⁻¹) := mul_le_mul_of_nonneg_right hA hB
    _ = _ := one_mul _

/-- **Class off-diagonal bound on offset indices.** Offsets `t_i = a + i·P_R` (`1 ≤ i ≤ J`), class
representative `r ≥ t_J` with `P_R` coprime to every `r − t_i`, block of `Q_T` consecutive `k`
(`T = t_J`). Then `Σ_{i<j} (pair count)/Q_T · 1/(t_i t_j) ≤ e · (Σ_i ρ'(t_i)/t_i)²`. -/
theorem class_off_diag (R a r J K0 : ℕ) (ha : 1 ≤ a) (hRa : R ≤ a)
    (hr : a + J * primorial R ≤ r)
    (hcop : ∀ i ∈ Icc 1 J, Nat.Coprime (primorial R) (r - (a + i * primorial R))) :
    ∑ i ∈ Icc 1 J, ∑ j ∈ Ioc i J,
      ((#{k ∈ Ico K0 (K0 + E460CRTPrimorial.Qt R (a + J * primorial R)) |
          Nat.Coprime (primorial (a + i * primorial R)) (r + k * primorial R - (a + i * primorial R)) ∧
          Nat.Coprime (primorial (a + j * primorial R)) (r + k * primorial R - (a + j * primorial R))} : ℕ) : ℝ) /
        (E460CRTPrimorial.Qt R (a + J * primorial R) : ℝ) *
        (1 / (((a + i * primorial R : ℕ) : ℝ) * ((a + j * primorial R : ℕ) : ℝ))) ≤
      Real.exp 1 * (∑ i ∈ Icc 1 J, rho' R (a + i * primorial R) / ((a + i * primorial R : ℕ) : ℝ)) ^ 2 := by
  classical
  set A := primorial R with hA
  set T := a + J * A with hT
  set g : ℕ → ℝ := fun j => rho' R (a + j * A) / ((a + j * A : ℕ) : ℝ) with hg
  have hApos : 0 < A := primorial_pos R
  have hg0 : ∀ j, 0 ≤ g j := fun j => div_nonneg (rho'_nonneg R _) (Nat.cast_nonneg _)
  have hganti : Antitone g := by
    intro x y hxy
    have h1 : (0 : ℝ) < ((a + x * A : ℕ) : ℝ) := by exact_mod_cast (show 0 < a + x * A by omega)
    have h2 : ((a + x * A : ℕ) : ℝ) ≤ ((a + y * A : ℕ) : ℝ) := by
      exact_mod_cast (show a + x * A ≤ a + y * A by have := Nat.mul_le_mul_right A hxy; omega)
    simp only [hg]
    calc rho' R (a + y * A) / ((a + y * A : ℕ) : ℝ) ≤ rho' R (a + x * A) / ((a + y * A : ℕ) : ℝ) :=
          div_le_div_of_nonneg_right (rho'_anti R (by have := Nat.mul_le_mul_right A hxy; omega)) (le_trans h1.le h2)
      _ ≤ rho' R (a + x * A) / ((a + x * A : ℕ) : ℝ) := div_le_div_of_nonneg_left (rho'_nonneg R _) h1 h2
  have hfinal : Real.exp 1 * (∑ i ∈ Icc 1 J, g i) ^ 2 =
      ∑ i ∈ Icc 1 J, Real.exp 1 * (g i * ∑ j ∈ Icc 1 J, g j) := by
    rw [← Finset.mul_sum, ← Finset.sum_mul, sq]
  rw [show (∑ i ∈ Icc 1 J, rho' R (a + i * A) / ((a + i * A : ℕ) : ℝ)) = ∑ i ∈ Icc 1 J, g i from rfl, hfinal]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi1 : 1 ≤ i := (mem_Icc.mp hi).1
  have hiJ : i ≤ J := (mem_Icc.mp hi).2
  have htiR : (0 : ℝ) < ((a + i * A : ℕ) : ℝ) := by exact_mod_cast (show 0 < a + i * A by omega)
  have hterm : ∀ j ∈ Ioc i J,
      ((#{k ∈ Ico K0 (K0 + E460CRTPrimorial.Qt R T) |
          Nat.Coprime (primorial (a + i * A)) (r + k * A - (a + i * A)) ∧
          Nat.Coprime (primorial (a + j * A)) (r + k * A - (a + j * A))} : ℕ) : ℝ) /
        (E460CRTPrimorial.Qt R T : ℝ) * (1 / (((a + i * A : ℕ) : ℝ) * ((a + j * A : ℕ) : ℝ))) ≤
      (g i) * (g j * ∏ p ∈ (mid R (a + i * A)).filter (fun p => p ∣ j - i), (p : ℝ) / ((p : ℝ) - 1)) := by
    intro j hj
    have hij : i < j := (mem_Ioc.mp hj).1
    have hjJ : j ≤ J := (mem_Ioc.mp hj).2
    have hiA : i * A < j * A := Nat.mul_lt_mul_of_pos_right hij hApos
    have hjA : j * A ≤ J * A := Nat.mul_le_mul_right A hjJ
    obtain ⟨q, hq⟩ := Qt_dvd R (a + j * A) T (by omega)
    have hqpos : 0 < q := by
      rcases Nat.eq_zero_or_pos q with h | h
      · have hTpos : 0 < E460CRTPrimorial.Qt R T := Finset.prod_pos (fun p hp => (mid_prime hp).pos)
        rw [h, mul_zero] at hq; omega
      · exact h
    have hpb := class_pair_prob_le R (a + i * A) (a + j * A) r K0 q hqpos (by nlinarith) (by omega) (by omega)
      (hcop i hi) (hcop j (mem_Icc.mpr ⟨by omega, hjJ⟩))
    rw [show q * E460CRTPrimorial.Qt R (a + j * A) = E460CRTPrimorial.Qt R T by rw [hq]; ring] at hpb
    rw [show ((q : ℝ) * (E460CRTPrimorial.Qt R (a + j * A) : ℝ)) = (E460CRTPrimorial.Qt R T : ℝ) by
      rw [hq]; push_cast; ring] at hpb
    have hfilt : (mid R (a + i * A)).filter (fun p => p ∣ (a + j * A) - (a + i * A)) =
        (mid R (a + i * A)).filter (fun p => p ∣ j - i) := by
      apply filter_congr; intro p hp
      exact offset_dvd_iff R a i j p hij.le (mid_prime hp) (mem_filter.mp hp).2
    rw [hfilt] at hpb
    have htjR : (0 : ℝ) < ((a + j * A : ℕ) : ℝ) := by exact_mod_cast (show 0 < a + j * A by omega)
    have hnn : (0 : ℝ) ≤ 1 / (((a + i * A : ℕ) : ℝ) * ((a + j * A : ℕ) : ℝ)) := by positivity
    calc _ ≤ (rho' R (a + i * A) * rho' R (a + j * A) *
            ∏ p ∈ (mid R (a + i * A)).filter (fun p => p ∣ j - i), (p : ℝ) / ((p : ℝ) - 1)) *
            (1 / (((a + i * A : ℕ) : ℝ) * ((a + j * A : ℕ) : ℝ))) := mul_le_mul_of_nonneg_right hpb hnn
      _ = _ := by simp only [hg]; field_simp
  calc ∑ j ∈ Ioc i J, _ ≤ ∑ j ∈ Ioc i J,
        (g i) * (g j * ∏ p ∈ (mid R (a + i * A)).filter (fun p => p ∣ j - i), (p : ℝ) / ((p : ℝ) - 1)) :=
        Finset.sum_le_sum hterm
    _ = g i * ∑ j ∈ Ioc i J, g j * ∏ p ∈ (mid R (a + i * A)).filter (fun p => p ∣ j - i), (p : ℝ) / ((p : ℝ) - 1) := by
        rw [Finset.mul_sum]
    _ ≤ g i * (Real.exp 1 * ∑ j ∈ Ioc i J, g j) :=
        mul_le_mul_of_nonneg_left (off_diag_gen g hganti hg0 _ (fun p hp => mid_prime hp) i J) (hg0 i)
    _ ≤ g i * (Real.exp 1 * ∑ j ∈ Icc 1 J, g j) := by
        apply mul_le_mul_of_nonneg_left _ (hg0 i)
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos 1).le
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (fun j hj => mem_Icc.mpr ⟨by have := (mem_Ioc.mp hj).1; omega, (mem_Ioc.mp hj).2⟩)
          (fun j _ _ => hg0 j)
    _ = Real.exp 1 * (g i * ∑ j ∈ Icc 1 J, g j) := by ring

end E460ClassSecond


namespace E460ClassPZ
open Finset Filter E460ClassPair E460ClassSecond E460PZ

lemma sum_Icc_shift (F : ℕ → ℝ) (J : ℕ) : ∑ i ∈ Icc 1 J, F i = ∑ j ∈ range J, F (j + 1) := by
  induction J with
  | zero => simp
  | succ J ih => rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]

set_option maxHeartbeats 4000000 in
/-- **Conditional Paley–Zygmund.** For every primorial modulus `P_R`, residue `r`, threshold `B` and `N₀`
there are a representative `r' ≥ N₀` of `r` mod `P_R` and a block length `L > 0` such that at least
`L/(8(1+e))` of the `L` numbers `r' + k·P_R` (`k < L`) satisfy `partialSum ≥ B`. -/
theorem class_pz (R r : ℕ) (B : ℝ) (N0 : ℕ) :
    ∃ r' ≥ N0, ∃ L : ℕ, 0 < L ∧ r' % primorial R = r % primorial R ∧
      (L : ℝ) / (8 * (1 + Real.exp 1)) ≤
        #{k ∈ range L | B ≤ OMA.S_erdos_460.partialSum (r' + k * primorial R)} := by
  classical
  set A := primorial R with hA
  have hApos : 0 < A := primorial_pos R
  obtain ⟨c, hc, hQm⟩ := E460Class.Qt_mertens
  set u := r % A with hu
  set v := (u + A - 1) % A with hv
  set a := v + A * (R + 2) with ha
  have ha2 : R + 2 ≤ a := by have : R + 2 ≤ A * (R + 2) := Nat.le_mul_of_pos_left _ hApos; omega
  -- choose J with μ ≥ max(1, 2B)
  have hT := (E460AP.ap_tendsto (a + A) A (by omega) hApos).const_mul_atTop hc
  obtain ⟨J, hJ⟩ := ((hT.eventually_ge_atTop (max 1 (2 * B))).and (eventually_ge_atTop 1)).exists
  set T := a + J * A with hTdef
  set r' := u + A * (N0 + T + 1) with hr'
  have hr'T : T < r' := by have : N0 + T + 1 ≤ A * (N0 + T + 1) := Nat.le_mul_of_pos_left _ hApos; omega
  have hr'N : N0 ≤ r' := by have : N0 + T + 1 ≤ A * (N0 + T + 1) := Nat.le_mul_of_pos_left _ hApos; omega
  -- coprimality of every offset
  have hcop : ∀ i ∈ Icc 1 J, Nat.Coprime A (r' - (a + i * A)) := by
    intro i hi
    have hiJ : i * A ≤ J * A := Nat.mul_le_mul_right _ (mem_Icc.mp hi).2
    obtain ⟨w, hw⟩ : ∃ w, w = (u + A - 1) / A := ⟨_, rfl⟩
    have hvw : v + A * w = u + A - 1 := by rw [hw]; exact Nat.mod_add_div _ _
    have hu' : u < A := Nat.mod_lt _ hApos
    have hle : a + i * A ≤ r' := by omega
    have hmod : 1 ≡ r' - (a + i * A) [MOD A] := by
      rw [Nat.modEq_iff_dvd]
      refine ⟨(w : ℤ) - 1 + (N0 + T + 1) - (R + 2) - i, ?_⟩
      have hvw' : (v : ℤ) + A * (w : ℤ) = u + A - 1 := by
        have := congrArg (fun z : ℕ => (z : ℤ)) hvw
        simp only [Nat.cast_add, Nat.cast_mul] at this
        rw [this, Nat.cast_sub (by omega)]; push_cast; ring
      have hcast : ((r' - (a + i * A) : ℕ) : ℤ) = (u : ℤ) + A * (N0 + T + 1) - (v + A * (R + 2) + i * A) := by
        rw [Nat.cast_sub hle, hr', ha]; push_cast; ring
      rw [hcast]
      linear_combination -hvw'
    rw [E460CRT.coprime_mod_iff, ← (hmod : 1 % A = (r' - (a + i * A)) % A), ← E460CRT.coprime_mod_iff]
    exact Nat.coprime_one_right A
  set QT := E460CRTPrimorial.Qt R T with hQT
  have hQTpos : 0 < QT := Finset.prod_pos (fun p hp => (mid_prime hp).pos)
  -- the variable Y
  obtain ⟨b, hb⟩ : ∃ b : ℕ → ℕ → ℝ, b = fun i k =>
    if (primorial (a + i * A)).Coprime (r' + k * A - (a + i * A)) then (1 : ℝ) / ((a + i * A : ℕ) : ℝ) else 0 :=
    ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ℕ → ℝ, Y = fun k => ∑ i ∈ Icc 1 J, b i k := ⟨_, rfl⟩
  obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, μ = ∑ i ∈ Icc 1 J, rho' R (a + i * A) / ((a + i * A : ℕ) : ℝ) := ⟨_, rfl⟩
  have htpos : ∀ i, (0 : ℝ) < ((a + i * A : ℕ) : ℝ) := fun i => by exact_mod_cast (show 0 < a + i * A by omega)
  -- μ ≥ max 1 (2B)
  have hμbig : max 1 (2 * B) ≤ μ := by
    refine le_trans hJ.1 ?_
    rw [hμ, sum_Icc_shift, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have hj2 : 2 ≤ (a + (j + 1) * A) := by nlinarith
    have hRj : R ≤ (a + (j + 1) * A) := by nlinarith
    have hb' := hQm R ((a + (j + 1) * A)) hRj hj2
    rw [← rho'_eq] at hb'
    have ht2 : (2 : ℝ) ≤ ((a + (j + 1) * A : ℕ) : ℝ) := by exact_mod_cast hj2
    have hlog : 0 < Real.log ((a + (j + 1) * A : ℕ) : ℝ) := Real.log_pos (by linarith)
    have hcast : ((a + A : ℕ) : ℝ) + (A : ℝ) * (j : ℝ) = ((a + (j + 1) * A : ℕ) : ℝ) := by
      push_cast; ring
    rw [hcast]; unfold E460Mertens.g
    have hgoal : c * (1 / (((a + (j + 1) * A : ℕ) : ℝ) * Real.log ((a + (j + 1) * A : ℕ) : ℝ))) =
        (c / Real.log ((a + (j + 1) * A : ℕ) : ℝ)) / ((a + (j + 1) * A : ℕ) : ℝ) := by
      have h1 : ((a + (j + 1) * A : ℕ) : ℝ) ≠ 0 := (htpos _).ne'
      field_simp
    rw [hgoal]
    exact div_le_div_of_nonneg_right hb' (htpos _).le
  have hμ1 : 1 ≤ μ := le_trans (le_max_left _ _) hμbig
  have hμB : 2 * B ≤ μ := le_trans (le_max_right _ _) hμbig
  -- mean
  have hmean : ∑ k ∈ range QT, Y k = (QT : ℝ) * μ := by
    rw [hY]
    rw [Finset.sum_comm, hμ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hiJ : i * A ≤ J * A := Nat.mul_le_mul_right _ (mem_Icc.mp hi).2
    have hRi : R ≤ a + i * A := by nlinarith
    have hiT : a + i * A ≤ T := by omega
    have hir : a + i * A ≤ r' := by omega
    have hpc := E460CRTPrimorial.primorial_class R (a + i * A) T r' 0 hRi hiT hir
    rw [if_pos (hcop i hi), zero_add] at hpc
    have hspT := E460CRTPrimorial.split R T (by omega)
    have hspt := E460CRTPrimorial.split R (a + i * A) hRi
    obtain ⟨m, hm⟩ := E460Avg.primorial_dvd hiT
    have hPTPR : primorial T / A = QT := by rw [hspT]; exact Nat.mul_div_cancel_left _ hApos
    have hPTPt : primorial T / primorial (a + i * A) = m := by rw [hm]; exact Nat.mul_div_cancel_left _ (primorial_pos _)
    have hQm' : QT = E460CRTPrimorial.Qt R (a + i * A) * m := by
      have : A * QT = A * (E460CRTPrimorial.Qt R (a + i * A) * m) := by rw [← hspT, hm, hspt]; ring
      exact Nat.eq_of_mul_eq_mul_left hApos this
    rw [hPTPR, hPTPt, ← Finset.range_eq_Ico] at hpc
    simp only [hb]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hpc, rho'_eq]
    have hQtpos : (0 : ℝ) < (E460CRTPrimorial.Qt R (a + i * A) : ℝ) := by
      exact_mod_cast Finset.prod_pos (fun p hp => (mid_prime hp).pos)
    rw [hQm']; push_cast; field_simp
  -- second moment
  have hsecond : ∑ k ∈ range QT, Y k ^ 2 ≤ (QT : ℝ) * (2 + 2 * Real.exp 1 * μ ^ 2) := by
    have hpt : ∀ k i j, b i k * b j k =
        (if (primorial (a + i * A)).Coprime (r' + k * A - (a + i * A)) ∧ (primorial (a + j * A)).Coprime (r' + k * A - (a + j * A))
          then 1 / (((a + i * A : ℕ) : ℝ) * ((a + j * A : ℕ) : ℝ)) else 0) := by
      intro k i j; simp only [hb]; rw [ite_zero_mul_ite_zero, one_div_mul_one_div]
    have hsq : ∀ k i, i ∈ Icc 1 J → b i k ^ 2 ≤ 1 / ((i : ℝ) * i) := by
      intro k i hi
      have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast (mem_Icc.mp hi).1
      have hti : (i : ℝ) ≤ ((a + i * A : ℕ) : ℝ) := by
        push_cast; nlinarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a),
          (show (1 : ℝ) ≤ A by exact_mod_cast hApos)]
      simp only [hb]; split_ifs
      · rw [div_pow, one_pow, sq]
        apply one_div_le_one_div_of_le (by positivity); nlinarith
      · rw [sq, mul_zero]; positivity
    rw [hY]
    simp only []
    simp_rw [sq_expand, Finset.sum_add_distrib]
    have hdiag : ∑ k ∈ range QT, ∑ i ∈ Icc 1 J, b i k ^ 2 ≤ (QT : ℝ) * 2 := by
      calc _ ≤ ∑ k ∈ range QT, ∑ i ∈ Icc 1 J, 1 / ((i : ℝ) * i) :=
            Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun i hi => hsq k i hi
        _ = (QT : ℝ) * ∑ i ∈ Icc 1 J, 1 / ((i : ℝ) * i) := by rw [Finset.sum_const, card_range, nsmul_eq_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_left (inv_sq_sum_le J) (Nat.cast_nonneg _)
    have hod := class_off_diag R a r' J 0 (by omega) (by omega) (by rw [← hA]; omega)
      (by rw [← hA]; exact hcop)
    have hoff : ∑ k ∈ range QT, 2 * ∑ i ∈ Icc 1 J, ∑ j ∈ Ioc i J, b i k * b j k ≤
        2 * ((QT : ℝ) * (Real.exp 1 * μ ^ 2)) := by
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      have hQR : (0 : ℝ) < QT := by exact_mod_cast hQTpos
      calc ∑ k ∈ range QT, ∑ i ∈ Icc 1 J, ∑ j ∈ Ioc i J, b i k * b j k
          = ∑ i ∈ Icc 1 J, ∑ j ∈ Ioc i J, ∑ k ∈ range QT, b i k * b j k := by
            rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
        _ = ∑ i ∈ Icc 1 J, ∑ j ∈ Ioc i J,
              ((#{k ∈ Ico 0 (0 + QT) |
                Nat.Coprime (primorial (a + i * A)) (r' + k * A - (a + i * A)) ∧
                Nat.Coprime (primorial (a + j * A)) (r' + k * A - (a + j * A))} : ℕ) : ℝ) /
                (QT : ℝ) * (1 / (((a + i * A : ℕ) : ℝ) * ((a + j * A : ℕ) : ℝ))) * QT := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            simp_rw [hpt]
            rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, zero_add, ← Finset.range_eq_Ico]
            field_simp
        _ = (QT : ℝ) * ∑ i ∈ Icc 1 J, ∑ j ∈ Ioc i J,
              ((#{k ∈ Ico 0 (0 + QT) |
                Nat.Coprime (primorial (a + i * A)) (r' + k * A - (a + i * A)) ∧
                Nat.Coprime (primorial (a + j * A)) (r' + k * A - (a + j * A))} : ℕ) : ℝ) /
                (QT : ℝ) * (1 / (((a + i * A : ℕ) : ℝ) * ((a + j * A : ℕ) : ℝ))) := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; ring
        _ ≤ (QT : ℝ) * (Real.exp 1 * μ ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ hQR.le
            rw [hμ]
            convert hod using 2
    have hring : (QT : ℝ) * (2 + 2 * Real.exp 1 * μ ^ 2) = (QT : ℝ) * 2 + 2 * ((QT : ℝ) * (Real.exp 1 * μ ^ 2)) := by ring
    linarith [hdiag, hoff, hring]
  -- Paley–Zygmund
  have hYnn : ∀ k, 0 ≤ Y k := fun k => by rw [hY]; exact Finset.sum_nonneg fun i _ => by rw [hb]; dsimp only; split_ifs <;> positivity
  set P : ℝ := (QT : ℝ) with hPdef
  have hP : 0 < P := by rw [hPdef]; exact_mod_cast hQTpos
  set As := (range QT).filter (fun k => μ / 2 ≤ Y k) with hAs
  have hmass : P * μ / 2 ≤ ∑ k ∈ As, Y k := by
    have hsplit := Finset.sum_filter_add_sum_filter_not (range QT) (fun k => μ / 2 ≤ Y k) Y
    have hnot : ∑ k ∈ (range QT).filter (fun k => ¬ μ / 2 ≤ Y k), Y k ≤ P * (μ / 2) := by
      calc _ ≤ ∑ k ∈ (range QT).filter (fun k => ¬ μ / 2 ≤ Y k), μ / 2 :=
            Finset.sum_le_sum fun k hk => le_of_lt (not_le.mp (mem_filter.mp hk).2)
        _ = (((range QT).filter (fun k => ¬ μ / 2 ≤ Y k)).card : ℝ) * (μ / 2) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((range QT).card : ℝ) * (μ / 2) := by
            apply mul_le_mul_of_nonneg_right _ (by linarith)
            exact_mod_cast Finset.card_filter_le _ _
        _ = P * (μ / 2) := by rw [card_range]
    rw [hmean] at hsplit
    linarith
  have hcs : (∑ k ∈ As, Y k) ^ 2 ≤ (As.card : ℝ) * ∑ k ∈ As, Y k ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq As (fun _ => (1 : ℝ)) Y
    simpa using this
  have hsub : ∑ k ∈ As, Y k ^ 2 ≤ ∑ k ∈ range QT, Y k ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun k _ _ => sq_nonneg _)
  have hAnn : (0 : ℝ) ≤ As.card := Nat.cast_nonneg _
  have hkey : (P * μ / 2) ^ 2 ≤ (As.card : ℝ) * (P * (2 + 2 * Real.exp 1 * μ ^ 2)) := by
    calc (P * μ / 2) ^ 2 ≤ (∑ k ∈ As, Y k) ^ 2 := pow_le_pow_left₀ (by positivity) hmass 2
      _ ≤ (As.card : ℝ) * ∑ k ∈ As, Y k ^ 2 := hcs
      _ ≤ _ := mul_le_mul_of_nonneg_left (hsub.trans hsecond) hAnn
  have hk2 : P * μ ^ 2 / 4 ≤ (As.card : ℝ) * (2 + 2 * Real.exp 1 * μ ^ 2) := by
    have : (P * μ / 2) ^ 2 = P * (P * μ ^ 2 / 4) := by ring
    rw [this, show (As.card : ℝ) * (P * (2 + 2 * Real.exp 1 * μ ^ 2)) =
      P * ((As.card : ℝ) * (2 + 2 * Real.exp 1 * μ ^ 2)) by ring] at hkey
    exact le_of_mul_le_mul_left hkey hP
  have hμ2 : 1 ≤ μ ^ 2 := by nlinarith
  have hk3 : P * μ ^ 2 / 4 ≤ (As.card : ℝ) * (2 * (1 + Real.exp 1)) * μ ^ 2 := by
    have h1 : 2 + 2 * Real.exp 1 * μ ^ 2 ≤ 2 * (1 + Real.exp 1) * μ ^ 2 := by nlinarith
    have h2 : (As.card : ℝ) * (2 + 2 * Real.exp 1 * μ ^ 2) ≤ (As.card : ℝ) * (2 * (1 + Real.exp 1) * μ ^ 2) :=
      mul_le_mul_of_nonneg_left h1 hAnn
    linarith [show (As.card : ℝ) * (2 * (1 + Real.exp 1) * μ ^ 2) = (As.card : ℝ) * (2 * (1 + Real.exp 1)) * μ ^ 2 by ring]
  have hk4 : P / 4 ≤ (As.card : ℝ) * (2 * (1 + Real.exp 1)) := by
    have hpos : 0 < μ ^ 2 := by linarith
    have : P / 4 * μ ^ 2 ≤ (As.card : ℝ) * (2 * (1 + Real.exp 1)) * μ ^ 2 := by linarith
    exact le_of_mul_le_mul_right this hpos
  have hAsize : P / (8 * (1 + Real.exp 1)) ≤ As.card := by
    rw [div_le_iff₀ (by positivity)]; linarith
  -- lift to partialSum
  refine ⟨r', hr'N, QT, hQTpos, ?_, hAsize.trans ?_⟩
  · rw [hr', show u + A * (N0 + T + 1) = u + (N0 + T + 1) * A by ring, Nat.add_mul_mod_self_right, hu,
      Nat.mod_mod]
  · exact_mod_cast Finset.card_le_card (fun k hk => by
      rw [mem_filter] at hk ⊢
      refine ⟨hk.1, ?_⟩
      have hYST : Y k ≤ E460Gap.ST T (r' + k * A) := by
        rw [hY, hb]
        dsimp only
        unfold E460Gap.ST
        have hinj : Set.InjOn (fun i => a + i * A) (Icc 1 J) := by
          intro x _ y _ hxy
          have hxy' : a + x * A = a + y * A := hxy
          have : x * A = y * A := by omega
          exact Nat.eq_of_mul_eq_mul_right hApos this
        rw [← Finset.sum_image (f := fun s => if (primorial s).Coprime (r' + k * A - s) then (1 : ℝ) / (s : ℝ) else 0) hinj]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro s hs
          obtain ⟨i, hi, rfl⟩ := mem_image.mp hs
          have hiJ : i * A ≤ J * A := Nat.mul_le_mul_right _ (mem_Icc.mp hi).2
          exact mem_Icc.mpr ⟨by omega, by omega⟩
        · intro s _ _; split_ifs <;> positivity
      have hlt : T < r' + k * A := by omega
      have := E460Gap.trunc_le T _ hlt
      linarith [hk.2])

end E460ClassPZ


namespace E460ClassPZTrunc
open Finset Filter E460ClassPair E460ClassSecond E460PZ E460ClassPZ

set_option maxHeartbeats 4000000 in
/-- **Periodic truncated witness inside `class_pz`.** For every `R`, residue `r` and `B`, there is a
truncation level `T ≥ R`, chosen from `(R, r, B)` only, such that `Q_T = Qt R T = P_T / P_R > 0` and for
**every** `r' > T` with `r' ≡ r (mod P_R)`, at least `Q_T / (8(1+e))` of the `k < Q_T` have truncated
`S_T(r' + k·P_R) ≥ B`. -/
theorem class_pz_trunc (R r : ℕ) (B : ℝ) :
    ∃ T ≥ R, 0 < E460CRTPrimorial.Qt R T ∧ E460CRTPrimorial.Qt R T = primorial T / primorial R ∧
      ∀ r' : ℕ, T < r' → r' % primorial R = r % primorial R →
        ((E460CRTPrimorial.Qt R T : ℕ) : ℝ) / (8 * (1 + Real.exp 1)) ≤
          #{k ∈ range (E460CRTPrimorial.Qt R T) | B ≤ E460Gap.ST T (r' + k * primorial R)} := by
  classical
  set A := primorial R with hA
  have hApos : 0 < A := primorial_pos R
  obtain ⟨c, hc, hQm⟩ := E460Class.Qt_mertens
  set u := r % A with hu
  set v := (u + A - 1) % A with hv
  set a := v + A * (R + 2) with ha
  have ha2 : R + 2 ≤ a := by have : R + 2 ≤ A * (R + 2) := Nat.le_mul_of_pos_left _ hApos; omega
  -- choose J with μ ≥ max(1, 2B)
  have hT := (E460AP.ap_tendsto (a + A) A (by omega) hApos).const_mul_atTop hc
  obtain ⟨J, hJ⟩ := ((hT.eventually_ge_atTop (max 1 (2 * B))).and (eventually_ge_atTop 1)).exists
  set T := a + J * A with hTdef
  set QT := E460CRTPrimorial.Qt R T with hQT
  have hQTpos : 0 < QT := Finset.prod_pos (fun p hp => (mid_prime hp).pos)
  refine ⟨T, by omega, hQTpos, ?_, ?_⟩
  · rw [E460CRTPrimorial.split R T (by omega)]; exact (Nat.mul_div_cancel_left _ hApos).symm
  intro r' hr'T hmod
  obtain ⟨q, hq⟩ : ∃ q, r' = u + A * q := ⟨r' / A, by rw [← hmod]; exact (Nat.mod_add_div r' A).symm⟩
  -- coprimality of every offset
  have hcop : ∀ i ∈ Icc 1 J, Nat.Coprime A (r' - (a + i * A)) := by
    intro i hi
    have hiJ : i * A ≤ J * A := Nat.mul_le_mul_right _ (mem_Icc.mp hi).2
    obtain ⟨w, hw⟩ : ∃ w, w = (u + A - 1) / A := ⟨_, rfl⟩
    have hvw : v + A * w = u + A - 1 := by rw [hw]; exact Nat.mod_add_div _ _
    have hu' : u < A := Nat.mod_lt _ hApos
    have hle : a + i * A ≤ r' := by omega
    have hmod : 1 ≡ r' - (a + i * A) [MOD A] := by
      rw [Nat.modEq_iff_dvd]
      refine ⟨(w : ℤ) - 1 + q - (R + 2) - i, ?_⟩
      have hvw' : (v : ℤ) + A * (w : ℤ) = u + A - 1 := by
        have := congrArg (fun z : ℕ => (z : ℤ)) hvw
        simp only [Nat.cast_add, Nat.cast_mul] at this
        rw [this, Nat.cast_sub (by omega)]; push_cast; ring
      have hcast : ((r' - (a + i * A) : ℕ) : ℤ) = (u : ℤ) + A * q - (v + A * (R + 2) + i * A) := by
        rw [Nat.cast_sub hle, hq, ha]; push_cast; ring
      rw [hcast]
      linear_combination -hvw'
    rw [E460CRT.coprime_mod_iff, ← (hmod : 1 % A = (r' - (a + i * A)) % A), ← E460CRT.coprime_mod_iff]
    exact Nat.coprime_one_right A
  -- the variable Y
  obtain ⟨b, hb⟩ : ∃ b : ℕ → ℕ → ℝ, b = fun i k =>
    if (primorial (a + i * A)).Coprime (r' + k * A - (a + i * A)) then (1 : ℝ) / ((a + i * A : ℕ) : ℝ) else 0 :=
    ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ℕ → ℝ, Y = fun k => ∑ i ∈ Icc 1 J, b i k := ⟨_, rfl⟩
  obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, μ = ∑ i ∈ Icc 1 J, rho' R (a + i * A) / ((a + i * A : ℕ) : ℝ) := ⟨_, rfl⟩
  have htpos : ∀ i, (0 : ℝ) < ((a + i * A : ℕ) : ℝ) := fun i => by exact_mod_cast (show 0 < a + i * A by omega)
  -- μ ≥ max 1 (2B)
  have hμbig : max 1 (2 * B) ≤ μ := by
    refine le_trans hJ.1 ?_
    rw [hμ, sum_Icc_shift, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have hj2 : 2 ≤ (a + (j + 1) * A) := by nlinarith
    have hRj : R ≤ (a + (j + 1) * A) := by nlinarith
    have hb' := hQm R ((a + (j + 1) * A)) hRj hj2
    rw [← rho'_eq] at hb'
    have ht2 : (2 : ℝ) ≤ ((a + (j + 1) * A : ℕ) : ℝ) := by exact_mod_cast hj2
    have hlog : 0 < Real.log ((a + (j + 1) * A : ℕ) : ℝ) := Real.log_pos (by linarith)
    have hcast : ((a + A : ℕ) : ℝ) + (A : ℝ) * (j : ℝ) = ((a + (j + 1) * A : ℕ) : ℝ) := by
      push_cast; ring
    rw [hcast]; unfold E460Mertens.g
    have hgoal : c * (1 / (((a + (j + 1) * A : ℕ) : ℝ) * Real.log ((a + (j + 1) * A : ℕ) : ℝ))) =
        (c / Real.log ((a + (j + 1) * A : ℕ) : ℝ)) / ((a + (j + 1) * A : ℕ) : ℝ) := by
      have h1 : ((a + (j + 1) * A : ℕ) : ℝ) ≠ 0 := (htpos _).ne'
      field_simp
    rw [hgoal]
    exact div_le_div_of_nonneg_right hb' (htpos _).le
  have hμ1 : 1 ≤ μ := le_trans (le_max_left _ _) hμbig
  have hμB : 2 * B ≤ μ := le_trans (le_max_right _ _) hμbig
  -- mean
  have hmean : ∑ k ∈ range QT, Y k = (QT : ℝ) * μ := by
    rw [hY]
    rw [Finset.sum_comm, hμ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hiJ : i * A ≤ J * A := Nat.mul_le_mul_right _ (mem_Icc.mp hi).2
    have hRi : R ≤ a + i * A := by nlinarith
    have hiT : a + i * A ≤ T := by omega
    have hir : a + i * A ≤ r' := by omega
    have hpc := E460CRTPrimorial.primorial_class R (a + i * A) T r' 0 hRi hiT hir
    rw [if_pos (hcop i hi), zero_add] at hpc
    have hspT := E460CRTPrimorial.split R T (by omega)
    have hspt := E460CRTPrimorial.split R (a + i * A) hRi
    obtain ⟨m, hm⟩ := E460Avg.primorial_dvd hiT
    have hPTPR : primorial T / A = QT := by rw [hspT]; exact Nat.mul_div_cancel_left _ hApos
    have hPTPt : primorial T / primorial (a + i * A) = m := by rw [hm]; exact Nat.mul_div_cancel_left _ (primorial_pos _)
    have hQm' : QT = E460CRTPrimorial.Qt R (a + i * A) * m := by
      have : A * QT = A * (E460CRTPrimorial.Qt R (a + i * A) * m) := by rw [← hspT, hm, hspt]; ring
      exact Nat.eq_of_mul_eq_mul_left hApos this
    rw [hPTPR, hPTPt, ← Finset.range_eq_Ico] at hpc
    simp only [hb]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hpc, rho'_eq]
    have hQtpos : (0 : ℝ) < (E460CRTPrimorial.Qt R (a + i * A) : ℝ) := by
      exact_mod_cast Finset.prod_pos (fun p hp => (mid_prime hp).pos)
    rw [hQm']; push_cast; field_simp
  -- second moment
  have hsecond : ∑ k ∈ range QT, Y k ^ 2 ≤ (QT : ℝ) * (2 + 2 * Real.exp 1 * μ ^ 2) := by
    have hpt : ∀ k i j, b i k * b j k =
        (if (primorial (a + i * A)).Coprime (r' + k * A - (a + i * A)) ∧ (primorial (a + j * A)).Coprime (r' + k * A - (a + j * A))
          then 1 / (((a + i * A : ℕ) : ℝ) * ((a + j * A : ℕ) : ℝ)) else 0) := by
      intro k i j; simp only [hb]; rw [ite_zero_mul_ite_zero, one_div_mul_one_div]
    have hsq : ∀ k i, i ∈ Icc 1 J → b i k ^ 2 ≤ 1 / ((i : ℝ) * i) := by
      intro k i hi
      have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast (mem_Icc.mp hi).1
      have hti : (i : ℝ) ≤ ((a + i * A : ℕ) : ℝ) := by
        push_cast; nlinarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a),
          (show (1 : ℝ) ≤ A by exact_mod_cast hApos)]
      simp only [hb]; split_ifs
      · rw [div_pow, one_pow, sq]
        apply one_div_le_one_div_of_le (by positivity); nlinarith
      · rw [sq, mul_zero]; positivity
    rw [hY]
    simp only []
    simp_rw [sq_expand, Finset.sum_add_distrib]
    have hdiag : ∑ k ∈ range QT, ∑ i ∈ Icc 1 J, b i k ^ 2 ≤ (QT : ℝ) * 2 := by
      calc _ ≤ ∑ k ∈ range QT, ∑ i ∈ Icc 1 J, 1 / ((i : ℝ) * i) :=
            Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun i hi => hsq k i hi
        _ = (QT : ℝ) * ∑ i ∈ Icc 1 J, 1 / ((i : ℝ) * i) := by rw [Finset.sum_const, card_range, nsmul_eq_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_left (inv_sq_sum_le J) (Nat.cast_nonneg _)
    have hod := class_off_diag R a r' J 0 (by omega) (by omega) (by rw [← hA]; omega)
      (by rw [← hA]; exact hcop)
    have hoff : ∑ k ∈ range QT, 2 * ∑ i ∈ Icc 1 J, ∑ j ∈ Ioc i J, b i k * b j k ≤
        2 * ((QT : ℝ) * (Real.exp 1 * μ ^ 2)) := by
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      have hQR : (0 : ℝ) < QT := by exact_mod_cast hQTpos
      calc ∑ k ∈ range QT, ∑ i ∈ Icc 1 J, ∑ j ∈ Ioc i J, b i k * b j k
          = ∑ i ∈ Icc 1 J, ∑ j ∈ Ioc i J, ∑ k ∈ range QT, b i k * b j k := by
            rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
        _ = ∑ i ∈ Icc 1 J, ∑ j ∈ Ioc i J,
              ((#{k ∈ Ico 0 (0 + QT) |
                Nat.Coprime (primorial (a + i * A)) (r' + k * A - (a + i * A)) ∧
                Nat.Coprime (primorial (a + j * A)) (r' + k * A - (a + j * A))} : ℕ) : ℝ) /
                (QT : ℝ) * (1 / (((a + i * A : ℕ) : ℝ) * ((a + j * A : ℕ) : ℝ))) * QT := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            simp_rw [hpt]
            rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, zero_add, ← Finset.range_eq_Ico]
            field_simp
        _ = (QT : ℝ) * ∑ i ∈ Icc 1 J, ∑ j ∈ Ioc i J,
              ((#{k ∈ Ico 0 (0 + QT) |
                Nat.Coprime (primorial (a + i * A)) (r' + k * A - (a + i * A)) ∧
                Nat.Coprime (primorial (a + j * A)) (r' + k * A - (a + j * A))} : ℕ) : ℝ) /
                (QT : ℝ) * (1 / (((a + i * A : ℕ) : ℝ) * ((a + j * A : ℕ) : ℝ))) := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; ring
        _ ≤ (QT : ℝ) * (Real.exp 1 * μ ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ hQR.le
            rw [hμ]
            convert hod using 2
    have hring : (QT : ℝ) * (2 + 2 * Real.exp 1 * μ ^ 2) = (QT : ℝ) * 2 + 2 * ((QT : ℝ) * (Real.exp 1 * μ ^ 2)) := by ring
    linarith [hdiag, hoff, hring]
  -- Paley–Zygmund
  have hYnn : ∀ k, 0 ≤ Y k := fun k => by rw [hY]; exact Finset.sum_nonneg fun i _ => by rw [hb]; dsimp only; split_ifs <;> positivity
  set P : ℝ := (QT : ℝ) with hPdef
  have hP : 0 < P := by rw [hPdef]; exact_mod_cast hQTpos
  set As := (range QT).filter (fun k => μ / 2 ≤ Y k) with hAs
  have hmass : P * μ / 2 ≤ ∑ k ∈ As, Y k := by
    have hsplit := Finset.sum_filter_add_sum_filter_not (range QT) (fun k => μ / 2 ≤ Y k) Y
    have hnot : ∑ k ∈ (range QT).filter (fun k => ¬ μ / 2 ≤ Y k), Y k ≤ P * (μ / 2) := by
      calc _ ≤ ∑ k ∈ (range QT).filter (fun k => ¬ μ / 2 ≤ Y k), μ / 2 :=
            Finset.sum_le_sum fun k hk => le_of_lt (not_le.mp (mem_filter.mp hk).2)
        _ = (((range QT).filter (fun k => ¬ μ / 2 ≤ Y k)).card : ℝ) * (μ / 2) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((range QT).card : ℝ) * (μ / 2) := by
            apply mul_le_mul_of_nonneg_right _ (by linarith)
            exact_mod_cast Finset.card_filter_le _ _
        _ = P * (μ / 2) := by rw [card_range]
    rw [hmean] at hsplit
    linarith
  have hcs : (∑ k ∈ As, Y k) ^ 2 ≤ (As.card : ℝ) * ∑ k ∈ As, Y k ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq As (fun _ => (1 : ℝ)) Y
    simpa using this
  have hsub : ∑ k ∈ As, Y k ^ 2 ≤ ∑ k ∈ range QT, Y k ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun k _ _ => sq_nonneg _)
  have hAnn : (0 : ℝ) ≤ As.card := Nat.cast_nonneg _
  have hkey : (P * μ / 2) ^ 2 ≤ (As.card : ℝ) * (P * (2 + 2 * Real.exp 1 * μ ^ 2)) := by
    calc (P * μ / 2) ^ 2 ≤ (∑ k ∈ As, Y k) ^ 2 := pow_le_pow_left₀ (by positivity) hmass 2
      _ ≤ (As.card : ℝ) * ∑ k ∈ As, Y k ^ 2 := hcs
      _ ≤ _ := mul_le_mul_of_nonneg_left (hsub.trans hsecond) hAnn
  have hk2 : P * μ ^ 2 / 4 ≤ (As.card : ℝ) * (2 + 2 * Real.exp 1 * μ ^ 2) := by
    have : (P * μ / 2) ^ 2 = P * (P * μ ^ 2 / 4) := by ring
    rw [this, show (As.card : ℝ) * (P * (2 + 2 * Real.exp 1 * μ ^ 2)) =
      P * ((As.card : ℝ) * (2 + 2 * Real.exp 1 * μ ^ 2)) by ring] at hkey
    exact le_of_mul_le_mul_left hkey hP
  have hμ2 : 1 ≤ μ ^ 2 := by nlinarith
  have hk3 : P * μ ^ 2 / 4 ≤ (As.card : ℝ) * (2 * (1 + Real.exp 1)) * μ ^ 2 := by
    have h1 : 2 + 2 * Real.exp 1 * μ ^ 2 ≤ 2 * (1 + Real.exp 1) * μ ^ 2 := by nlinarith
    have h2 : (As.card : ℝ) * (2 + 2 * Real.exp 1 * μ ^ 2) ≤ (As.card : ℝ) * (2 * (1 + Real.exp 1) * μ ^ 2) :=
      mul_le_mul_of_nonneg_left h1 hAnn
    linarith [show (As.card : ℝ) * (2 * (1 + Real.exp 1) * μ ^ 2) = (As.card : ℝ) * (2 * (1 + Real.exp 1)) * μ ^ 2 by ring]
  have hk4 : P / 4 ≤ (As.card : ℝ) * (2 * (1 + Real.exp 1)) := by
    have hpos : 0 < μ ^ 2 := by linarith
    have : P / 4 * μ ^ 2 ≤ (As.card : ℝ) * (2 * (1 + Real.exp 1)) * μ ^ 2 := by linarith
    exact le_of_mul_le_mul_right this hpos
  have hAsize : P / (8 * (1 + Real.exp 1)) ≤ As.card := by
    rw [div_le_iff₀ (by positivity)]; linarith
  -- lift to partialSum
  -- truncated sum, no lift to partialSum
  refine hAsize.trans ?_
  exact_mod_cast Finset.card_le_card (fun k hk => by
      rw [mem_filter] at hk ⊢
      refine ⟨hk.1, ?_⟩
      have hYST : Y k ≤ E460Gap.ST T (r' + k * A) := by
        rw [hY, hb]
        dsimp only
        unfold E460Gap.ST
        have hinj : Set.InjOn (fun i => a + i * A) (Icc 1 J) := by
          intro x _ y _ hxy
          have hxy' : a + x * A = a + y * A := hxy
          have : x * A = y * A := by omega
          exact Nat.eq_of_mul_eq_mul_right hApos this
        rw [← Finset.sum_image (f := fun s => if (primorial s).Coprime (r' + k * A - s) then (1 : ℝ) / (s : ℝ) else 0) hinj]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro s hs
          obtain ⟨i, hi, rfl⟩ := mem_image.mp hs
          have hiJ : i * A ≤ J * A := Nat.mul_le_mul_right _ (mem_Icc.mp hi).2
          exact mem_Icc.mpr ⟨by omega, by omega⟩
        · intro s _ _; split_ifs <;> positivity
      linarith [hk.2])

/-- **Any full block.** With the same `T`, every block `K0 ≤ k < K0 + Q_T` (for every `r' > T` in the
class) has the same proportion; this is the `∀ r'` statement applied to `r' + K0·P_R`. -/
theorem class_pz_trunc_block (R r : ℕ) (B : ℝ) :
    ∃ T ≥ R, 0 < E460CRTPrimorial.Qt R T ∧ E460CRTPrimorial.Qt R T = primorial T / primorial R ∧
      ∀ r' : ℕ, T < r' → r' % primorial R = r % primorial R → ∀ K0 : ℕ,
        ((E460CRTPrimorial.Qt R T : ℕ) : ℝ) / (8 * (1 + Real.exp 1)) ≤
          #{k ∈ Ico K0 (K0 + E460CRTPrimorial.Qt R T) | B ≤ E460Gap.ST T (r' + k * primorial R)} := by
  obtain ⟨T, hTR, hQ, hQe, h⟩ := class_pz_trunc R r B
  refine ⟨T, hTR, hQ, hQe, fun r' hr' hmod K0 => ?_⟩
  have h1 := h (r' + K0 * primorial R) (by omega)
    (by rw [Nat.add_mul_mod_self_right, hmod])
  refine h1.trans (le_of_eq ?_)
  norm_cast
  refine Finset.card_nbij' (fun k => k + K0) (fun k => k - K0) ?_ ?_ ?_ ?_
  · intro k hk
    simp only [coe_filter, Set.mem_setOf_eq, mem_range, mem_Ico] at hk ⊢
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [show r' + (k + K0) * primorial R = r' + K0 * primorial R + k * primorial R by ring]; exact hk.2
  · intro k hk
    simp only [coe_filter, Set.mem_setOf_eq, mem_range, mem_Ico] at hk ⊢
    refine ⟨by omega, ?_⟩
    rw [show r' + K0 * primorial R + (k - K0) * primorial R = r' + k * primorial R by
      rw [add_assoc, ← add_mul, Nat.add_sub_cancel' hk.1.1]]; exact hk.2
  · intro k _; simp
  · intro k hk
    simp only [coe_filter, Set.mem_setOf_eq, mem_Ico] at hk
    simp only; omega

end E460ClassPZTrunc



namespace E460Boost
open Finset E460Gap

lemma ST_mono (T T' n : ℕ) (h : T ≤ T') : E460Gap.ST T n ≤ E460Gap.ST T' n := by
  unfold E460Gap.ST
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl h)
  intro t _ _; split_ifs <;> positivity

lemma ST_congr (T n n' : ℕ) (hn : T ≤ n) (hn' : T ≤ n') (h : n % primorial T = n' % primorial T) :
    E460Gap.ST T n = E460Gap.ST T n' := by
  rcases le_total n n' with hle | hle
  · obtain ⟨j, hj⟩ := (Nat.modEq_iff_dvd' hle).mp h
    rw [show n' = n + j * primorial T by rw [mul_comm j]; omega, ST_periodic_mul T n j hn]
  · obtain ⟨j, hj⟩ := (Nat.modEq_iff_dvd' hle).mp h.symm
    rw [show n = n' + j * primorial T by rw [mul_comm j]; omega, ST_periodic_mul T n' j hn']

lemma sum_range_mul (a b : ℕ) (g : ℕ → ℝ) :
    ∑ y ∈ range (a * b), g y = ∑ x ∈ range a, ∑ k ∈ range b, g (x + a * k) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [mul_add, mul_one, Finset.sum_range_add, ih]
    simp only [Finset.sum_range_succ, Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun x _ => by rw [add_comm]

/-- Lifting a class-level proportion from level `T0` to any `T ≥ T0`: periodicity (blocks of
`Q_{T0}` tile `range Q_T` since `Q_{T0} ∣ Q_T`) plus monotonicity of `ST` in the level. -/
lemma lift_good (R T0 T n r : ℕ) (B C : ℝ) (hRT0 : R ≤ T0) (hT0T : T0 ≤ T) (hTn : T < n)
    (hn : n % primorial R = r % primorial R)
    (hg : ∀ r' : ℕ, T0 < r' → r' % primorial R = r % primorial R → ∀ K0 : ℕ,
      ((E460CRTPrimorial.Qt R T0 : ℕ) : ℝ) / C ≤
        #{k ∈ Ico K0 (K0 + E460CRTPrimorial.Qt R T0) | B ≤ E460Gap.ST T0 (r' + k * primorial R)}) :
    ((E460CRTPrimorial.Qt R T : ℕ) : ℝ) / C ≤
      #{k ∈ range (E460CRTPrimorial.Qt R T) | B ≤ E460Gap.ST T (n + k * primorial R)} := by
  obtain ⟨m, hm⟩ := E460Avg.primorial_dvd hT0T
  have hQ : E460CRTPrimorial.Qt R T = E460CRTPrimorial.Qt R T0 * m := by
    apply Nat.eq_of_mul_eq_mul_left (primorial_pos R)
    rw [← E460CRTPrimorial.split R T (by omega), hm, E460CRTPrimorial.split R T0 hRT0, mul_assoc]
  have hind : ∀ m : ℕ, ((E460CRTPrimorial.Qt R T0 * m : ℕ) : ℝ) / C ≤
      #{k ∈ range (E460CRTPrimorial.Qt R T0 * m) | B ≤ E460Gap.ST T0 (n + k * primorial R)} := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hb := hg n (by omega) hn (E460CRTPrimorial.Qt R T0 * m)
      rw [mul_add, mul_one, Finset.range_eq_Ico,
        ← Finset.Ico_union_Ico_eq_Ico (Nat.zero_le _) (Nat.le_add_right _ _), Finset.filter_union,
        Finset.card_union_of_disjoint
          (Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive _ _ _)),
        ← Finset.range_eq_Ico]
      push_cast at ih ⊢
      rw [add_div]
      linarith
  rw [hQ]
  refine (hind m).trans ?_
  exact_mod_cast Finset.card_le_card (fun k hk => by
    simp only [mem_filter] at hk ⊢
    exact ⟨hk.1, hk.2.trans (ST_mono _ _ _ hT0T)⟩)

/-- Residues `x < P_R` that are **bad** at level `R`: `S_R < B`, evaluated at the common
representative `x + (R+1)·P_R` (any representative `≥ R` gives the same value, `ST_congr`). -/
noncomputable def bad (B : ℝ) (R : ℕ) : Finset ℕ :=
  (range (primorial R)).filter (fun x => E460Gap.ST R (x + (R + 1) * primorial R) < B)

/-- The bad fraction `D_B(R)` modulo `P_R`. -/
noncomputable def D (B : ℝ) (R : ℕ) : ℝ := ((bad B R).card : ℝ) / primorial R

lemma ind_split (s : Finset ℕ) (f : ℕ → ℝ) (B : ℝ) :
    (∑ k ∈ s, if f k < B then (1 : ℝ) else 0) =
      (s.card : ℝ) - ((s.filter (fun k => B ≤ f k)).card : ℝ) := by
  have h1 : ∀ k, (if f k < B then (1 : ℝ) else 0) = 1 - if B ≤ f k then 1 else 0 := fun k => by
    by_cases h : B ≤ f k
    · simp [h, not_lt.mpr h]
    · simp [h, not_le.mp h]
  rw [Finset.sum_congr rfl (fun k _ => h1 k), Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    mul_one, ← Finset.natCast_card_filter]

/-- **Geometric density-boost step.** For every `R` and `B` there is `T ≥ R` with
`D_B(T) ≤ (1 − 1/(8(1+e))) · D_B(R)`. -/
theorem boost (R : ℕ) (B : ℝ) :
    ∃ T ≥ R, D B T ≤ (1 - 1 / (8 * (1 + Real.exp 1))) * D B R := by
  classical
  have hgood := fun r => E460ClassPZTrunc.class_pz_trunc_block R r B
  choose Tf hTfR hQpos hQeq hg using hgood
  obtain ⟨T, hT⟩ : ∃ T, T = R + ∑ r ∈ range (primorial R), Tf r := ⟨_, rfl⟩
  have hTr : ∀ r ∈ range (primorial R), Tf r ≤ T := fun r hr => by
    have := Finset.single_le_sum (f := Tf) (fun _ _ => Nat.zero_le _) hr; omega
  have hRT : R ≤ T := by omega
  refine ⟨T, hRT, ?_⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = E460CRTPrimorial.Qt R T := ⟨_, rfl⟩
  have hsplit : primorial T = primorial R * Q := by rw [hQ]; exact E460CRTPrimorial.split R T hRT
  have hPR : (0 : ℝ) < primorial R := by exact_mod_cast primorial_pos R
  have hPT0 := primorial_pos T
  have hQpos' : 0 < Q := by
    rcases Nat.eq_zero_or_pos Q with h | h
    · rw [h, mul_zero] at hsplit; omega
    · exact h
  have hclass : ∀ x ∈ range (primorial R),
      (∑ k ∈ range Q, if E460Gap.ST T (x + primorial R * k + (T + 1) * primorial T) < B then (1 : ℝ) else 0) ≤
        (1 - 1 / (8 * (1 + Real.exp 1))) * Q *
          (if E460Gap.ST R (x + (R + 1) * primorial R) < B then 1 else 0) := by
    intro x hx
    split_ifs with hbad
    · have hl := lift_good R (Tf x) T (x + (T + 1) * primorial T) x B (8 * (1 + Real.exp 1))
        (hTfR x) (hTr x hx) (by nlinarith)
        (by rw [hsplit, show x + (T + 1) * (primorial R * Q) = x + ((T + 1) * Q) * primorial R by ring,
              Nat.add_mul_mod_self_right])
        (hg x)
      rw [← hQ] at hl
      have hs := ind_split (range Q) (fun k => E460Gap.ST T (x + primorial R * k + (T + 1) * primorial T)) B
      beta_reduce at hs
      rw [hs, card_range]
      rw [Finset.filter_congr (fun k _ => by
        rw [show x + primorial R * k + (T + 1) * primorial T =
          x + (T + 1) * primorial T + k * primorial R by ring])]
      have hC : (0 : ℝ) < 8 * (1 + Real.exp 1) := by positivity
      have : (1 - 1 / (8 * (1 + Real.exp 1))) * (Q : ℝ) * 1 = Q - Q / (8 * (1 + Real.exp 1)) := by ring
      rw [this]; linarith
    · push_neg at hbad
      rw [mul_zero]
      apply le_of_eq; apply Finset.sum_eq_zero; intro k _
      rw [if_neg]; rw [not_lt]
      refine hbad.trans (le_trans (le_of_eq ?_) (ST_mono R T _ hRT))
      apply ST_congr R _ _ (by nlinarith [primorial_pos R]) (by nlinarith)
      rw [hsplit, show x + primorial R * k + (T + 1) * (primorial R * Q) =
          x + (k + (T + 1) * Q) * primorial R by ring,
        Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right]
  unfold D bad
  rw [Finset.natCast_card_filter, Finset.natCast_card_filter,
    show range (primorial T) = range (primorial R * Q) by rw [hsplit], sum_range_mul]
  have hsum := Finset.sum_le_sum hclass
  rw [← Finset.mul_sum] at hsum
  have hPT : (primorial T : ℝ) = primorial R * Q := by exact_mod_cast hsplit
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQpos'
  rw [hPT, div_le_iff₀ (by positivity)]
  refine hsum.trans (le_of_eq ?_)
  field_simp

end E460Boost



namespace E460Density
open Finset Filter E460Boost
open scoped Topology

lemma D_le_one (B : ℝ) (R : ℕ) : D B R ≤ 1 := by
  unfold D bad
  rw [div_le_one (by exact_mod_cast primorial_pos R)]
  exact_mod_cast (card_filter_le _ _).trans_eq (card_range _)

lemma c_bounds : 0 ≤ 1 - 1 / (8 * (1 + Real.exp 1)) ∧ 1 - 1 / (8 * (1 + Real.exp 1)) < 1 := by
  have he := Real.exp_pos 1
  have h1 : 1 ≤ 8 * (1 + Real.exp 1) := by nlinarith
  have h2 : 1 / (8 * (1 + Real.exp 1)) ≤ 1 := (div_le_one (by positivity)).mpr h1
  have h3 : 0 < 1 / (8 * (1 + Real.exp 1)) := by positivity
  constructor <;> linarith

/-- Iterating `boost` `j` times: some level has bad fraction `≤ (1 − c)^j`. -/
lemma iterate (B : ℝ) (j : ℕ) : ∃ T, D B T ≤ (1 - 1 / (8 * (1 + Real.exp 1))) ^ j := by
  induction j with
  | zero => exact ⟨0, by simpa using D_le_one B 0⟩
  | succ j ih =>
    obtain ⟨T, hT⟩ := ih
    obtain ⟨T', -, hT'⟩ := boost T B
    refine ⟨T', hT'.trans ?_⟩
    rw [pow_succ, mul_comm ((1 - 1 / (8 * (1 + Real.exp 1))) ^ j)]
    exact mul_le_mul_of_nonneg_left hT c_bounds.1

lemma small (B ε : ℝ) (hε : 0 < ε) : ∃ R, D B R < ε := by
  obtain ⟨j, hj⟩ :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one c_bounds.1 c_bounds.2).eventually (gt_mem_nhds hε)).exists
  obtain ⟨T, hT⟩ := iterate B j
  exact ⟨T, hT.trans_lt hj⟩

lemma residue_count (P N : ℕ) (hP : 0 < P) (S : Finset ℕ) :
    #{n ∈ range N | n % P ∈ S} ≤ (N / P + 1) * #S := by
  calc #{n ∈ range N | n % P ∈ S} ≤ #(S ×ˢ range (N / P + 1)) := by
        apply card_le_card_of_injOn (fun n => (n % P, n / P))
        · intro n hn
          simp only [coe_filter, Set.mem_setOf_eq, mem_range, coe_product, Set.mem_prod, mem_coe] at hn ⊢
          exact ⟨hn.2, Nat.lt_succ_of_le (Nat.div_le_div_right hn.1.le)⟩
        · intro a _ b _ h
          simp only [Prod.mk.injEq] at h
          rw [← Nat.mod_add_div a P, ← Nat.mod_add_div b P, h.1, h.2]
    _ = (N / P + 1) * #S := by rw [card_product, card_range, mul_comm]

/-- Bad `n < N` are either `≤ R` or lie in a bad residue class mod `P_R`. -/
lemma bad_count (B : ℝ) (R N : ℕ) :
    #{n ∈ range N | OMA.S_erdos_460.partialSum n < B} ≤
      (R + 1) + (N / primorial R + 1) * #(bad B R) := by
  calc #{n ∈ range N | OMA.S_erdos_460.partialSum n < B}
      ≤ #(range (R + 1) ∪ {n ∈ range N | n % primorial R ∈ bad B R}) := by
        apply card_le_card
        intro n hn
        simp only [mem_filter, mem_range] at hn
        rw [mem_union, mem_range, mem_filter, mem_range]
        by_cases hnR : n < R + 1
        · exact Or.inl hnR
        · right
          refine ⟨hn.1, ?_⟩
          have hRn : R < n := by omega
          have h1 := E460Gap.trunc_le R n hRn
          unfold bad
          rw [mem_filter, mem_range]
          refine ⟨Nat.mod_lt _ (primorial_pos R), ?_⟩
          have hRP : R + 1 ≤ (R + 1) * primorial R := Nat.le_mul_of_pos_right _ (primorial_pos R)
          rw [← E460Boost.ST_congr R n _ hRn.le (by omega)
            (by rw [Nat.add_mul_mod_self_right, Nat.mod_mod])]
          linarith [hn.2]
    _ ≤ #(range (R + 1)) + #{n ∈ range N | n % primorial R ∈ bad B R} := card_union_le _ _
    _ ≤ _ := by
        rw [card_range]
        exact Nat.add_le_add_left (residue_count _ _ (primorial_pos R) _) _

/-- **Divergence in natural density.** For every real `B`, the set of `n` with
`partialSum n < B` has natural density `0`. (Not the pointwise `main`.) -/
theorem density_zero (B : ℝ) :
    Tendsto (fun N : ℕ => (#{n ∈ range N | OMA.S_erdos_460.partialSum n < B} : ℝ) / N)
      atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨R, hR⟩ := small B (ε / 2) (by linarith)
  obtain ⟨M, hM⟩ := exists_nat_gt (2 * ((R : ℝ) + 1 + (#(bad B R) : ℝ)) / ε)
  refine ⟨M + 1, fun N hN => ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNM : (M : ℝ) < N := by exact_mod_cast (show M < N by omega)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity), div_lt_iff₀ hNpos]
  have hcR : (#{n ∈ range N | OMA.S_erdos_460.partialSum n < B} : ℝ) ≤
      ((R : ℝ) + 1) + (((N / primorial R : ℕ) : ℝ) + 1) * (#(bad B R) : ℝ) := by
    exact_mod_cast bad_count B R N
  have hP : (0 : ℝ) < primorial R := by exact_mod_cast primorial_pos R
  have hdiv : ((N / primorial R : ℕ) : ℝ) ≤ (N : ℝ) / primorial R := Nat.cast_div_le
  have hb0 : (0 : ℝ) ≤ (#(bad B R) : ℝ) := Nat.cast_nonneg _
  have hprod : ((N / primorial R : ℕ) : ℝ) * (#(bad B R) : ℝ) ≤ (N : ℝ) * D B R := by
    calc _ ≤ (N : ℝ) / primorial R * (#(bad B R) : ℝ) := mul_le_mul_of_nonneg_right hdiv hb0
      _ = (N : ℝ) * D B R := by unfold D; ring
  have hND : (N : ℝ) * D B R < N * (ε / 2) := mul_lt_mul_of_pos_left hR hNpos
  have hsmall : 2 * ((R : ℝ) + 1 + (#(bad B R) : ℝ)) < N * ε := (div_lt_iff₀ hε).mp (hM.trans hNM)
  nlinarith

end E460Density

#print axioms E460ClassPZ.class_pz
#print axioms E460ClassPZTrunc.class_pz_trunc_block
#print axioms E460Boost.boost
#print axioms E460Density.iterate
#print axioms E460Density.bad_count
#print axioms E460Density.density_zero
