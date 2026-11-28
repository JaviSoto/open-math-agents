import DyadicResearch245212

/-! An odd number of odd divisors at an A245212 equality must be 1 mod 8. -/
namespace OMA.OddCountResidue245212
open Nat ArithmeticFunction OMA.DyadicPower245212
open scoped ArithmeticFunction.sigma
open private OMA.DyadicPower245212.tau_linear OMA.DyadicPower245212.square_of_odd_tau
  from DyadicResearch245212

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
  have even := even_multiplicity (k:=k) (h:=1) ov eqn
  obtain ⟨j,hj⟩ := even
  have lin := OMA.DyadicPower245212.tau_linear v 4 (by decide) ov.pos.ne'
  rw [power]
  apply lin.trans
  rw [hj]
  change (1+(j+j)*4)%8=1%8
  omega

#print axioms odd_count
end OMA.OddCountResidue245212
