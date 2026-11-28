import DyadicResearch245212

/-! An odd number of odd divisors at an A245212 equality must be 1 mod 8. -/
namespace OMA.OddCountResidue245212
open Nat ArithmeticFunction OMA.DyadicPower245212
open scoped ArithmeticFunction.sigma
open private OMA.DyadicPower245212.tau_linear OMA.DyadicPower245212.square_of_odd_tau
  from DyadicResearch245212

theorem power_count {h k v : ℕ} (ov : Odd v)
    (eqn : OeisA245212.a (2^k*v^(2^(h+1)))=(σ 1 (2^k*v^(2^(h+1))):ℤ)) :
    σ 0 (v^(2^(h+1))) ≡ 1 [MOD 2^(h+2)] := by
  let H := 2^(h+1)
  have he : Even H := even_iff_two_dvd.mpr (dvd_pow_self _ (Nat.succ_ne_zero _))
  obtain ⟨j,hj⟩ := even_multiplicity ov eqn
  have lin := OMA.DyadicPower245212.tau_linear v H he ov.pos.ne'
  change σ 0 (v^H) ≡ 1 [MOD 2^(h+2)]
  rw [pow_succ' (2:ℕ) (h+1)]
  apply lin.trans
  rw [hj,show (j+j)*H=(2*H)*j by ring]
  exact Nat.ModEq.add_left _ (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right _ _))

theorem odd_count {k m : ℕ} (om : Odd m) (ot : Odd (σ 0 m))
    (eqn : OeisA245212.a (2^k*m)=(σ 1 (2^k*m):ℤ)) :
    σ 0 m ≡ 1 [MOD 8] := by
  obtain ⟨u,hu⟩ := OMA.DyadicPower245212.square_of_odd_tau ot
  rw [←sq] at hu
  have ou : Odd u := by rw [hu,pow_two,Nat.odd_mul] at om; exact om.1
  rw [hu] at eqn
  obtain ⟨v,hv⟩ := square_root_is_square ou eqn
  rw [←sq] at hv
  have ov : Odd v := by rw [hv,pow_two,Nat.odd_mul] at ou; exact ou.1
  have power : m=v^4 := by rw [hu,hv,←pow_mul]
  rw [hv,←pow_mul] at eqn
  rw [power]
  exact power_count (k:=k) (h:=1) ov eqn

#print axioms odd_count
end OMA.OddCountResidue245212
