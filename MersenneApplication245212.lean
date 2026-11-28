import OMAReductions.R_OeisA245212_conjecture_R1_H2_R2
import MersenneDenominator245212

/-! The power of two in each nontrivial even A245212 equality is
recoverable from the odd cofactor's reduced denominator alone. -/
namespace OMA.MersenneDenominator245212
open Nat Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma
open private OMA.R_OeisA245212_conjecture_R1_H2_R2.collapse
  OMA.R_OeisA245212_conjecture_R1_H2_R2.weighted_gt from OMAReductions.R_OeisA245212_conjecture_R1_H2_R2

theorem recover (k m : ℕ) (hk : 1≤k) (om : Odd m) (hm : 1 < m)
    (eq : OeisA245212.a (2^k*m) = (σ 1 (2^k*m) : ℤ)) :
    let A := m*m.divisors.card
    let F := ∑ d ∈ m.divisors, d*d.divisors.card
    let x := A-σ 1 m
    let y := F-A
    orderOf (2 : ZMod (y/(x.gcd y)))=k+1 := by
  dsimp only
  have res := OMA.R_OeisA245212_conjecture_R1_H2_R2.collapse k m hk om hm eq
  have yp := Nat.sub_pos_of_lt (OMA.R_OeisA245212_conjecture_R1_H2_R2.weighted_gt m hm)
  exact residual_order yp hk res.1.symm res.2

#print axioms recover
#print axioms injective_on_indices
end OMA.MersenneDenominator245212
