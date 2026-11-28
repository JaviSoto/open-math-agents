import MersenneDenominator245212
import MersenneOrderSupport245212

/-! Four linear ratios cover every solution whose reduced denominator divides 105. -/
namespace OMA.MersenneDenominator245212
def smallLines (x y : ℕ) := 3*x=5*y ∨ 7*x=17*y ∨ 15*x=49*y ∨ 21*x=107*y

theorem four_lines {x y k : ℕ} (hy : 0 < y) (hk : 1≤k) (quot : k=x/y)
    (sol : 2^(k+1)*(x-k*y)=x+y) (small : y/(x.gcd y) ∣ 105) : smallLines x y := by
  let t := k+1
  have ht : 2≤t := by dsimp [t]; omega
  have qd : Q t∣105 := (reduced hy hk quot sol) ▸ small
  have div : Q t∣2^12-1 := qd.trans (by decide : 105∣(2:ℕ)^12-1)
  have m := (Nat.modEq_iff_dvd' (by decide : 1≤(2:ℕ)^12) (n:=Q t)).mpr div
  rw [←ZMod.natCast_eq_natCast_iff] at m
  have pow : (2:ZMod (Q t))^12=1 := by simpa only [Nat.cast_one,Nat.cast_pow,Nat.cast_ofNat] using m.symm
  have dt := orderOf_dvd_of_pow_eq_one pow
  rw [order ht] at dt
  have up := Nat.le_of_dvd (by decide : 0<12) dt
  have can : t=2 ∨ t=3 ∨ t=4 ∨ t=6 := by
    revert qd dt
    clear_value t
    interval_cases t <;> decide +kernel
  have le : k*y≤x := by rw [quot]; exact Nat.div_mul_le_self _ _
  unfold smallLines
  rcases can with a|a|a|a <;> dsimp [t] at a
  · left; have kk : k=1 := by omega
    rw [kk] at sol le; omega
  · right; left; have kk : k=2 := by omega
    rw [kk] at sol le; omega
  · right; right; left; have kk : k=3 := by omega
    rw [kk] at sol le; omega
  · right; right; right; have kk : k=5 := by omega
    rw [kk] at sol le; omega

def hasLarge (z : ℕ) := ∃ p∈z.primeFactors, 7<p

theorem smooth_lines {x y k : ℕ} (hy : 0<y) (hk : 1≤k) (quot : k=x/y)
    (sol : 2^(k+1)*(x-k*y)=x+y) (sm : ¬hasLarge (y/(x.gcd y))) : smallLines x y := by
  let t := k+1
  have ht : 2≤t := by dsimp [t]; omega
  have den : y/(x.gcd y)=Q t := reduced hy hk quot sol
  rw [den] at sm
  have qnz : Q t≠0 := by have h := bound ht; omega
  have dt0 := OMA.MersenneOrderSupport245212.index_dvd ht qnz (dvd_refl (Q t))
  have dt : t∣12 := dt0.trans (Finset.lcm_dvd (fun p mem => by
    obtain ⟨pf,odd⟩ := Finset.mem_filter.mp mem
    have prime := (Nat.mem_primeFactors.mp pf).1
    have le : p≤7 := by by_contra! bad; exact sm ⟨p,pf,bad⟩
    interval_cases p <;> norm_num at *))
  have top := Nat.le_of_dvd (by decide : 0<12) dt
  have good : Q t∣105 := by
    revert dt sm
    clear_value t
    interval_cases t <;> unfold hasLarge <;> decide +kernel
  exact four_lines hy hk quot sol (den ▸ good)

end OMA.MersenneDenominator245212
