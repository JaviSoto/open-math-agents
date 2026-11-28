import MersenneApplication245212
import MersennePrimePowers245212

/-! If the weighted divisor surplus has only one possible odd prime factor,
that factor must be Mersenne, and its index fixes the even exponent. -/
namespace OMA.MersenneDenominator245212
open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma
open private OMA.R_OeisA245212_conjecture_R1_H2_R2.collapse
  OMA.R_OeisA245212_conjecture_R1_H2_R2.weighted_gt from OMAReductions.R_OeisA245212_conjecture_R1_H2_R2

theorem surplus_two_primes (k m s : ℕ) (hk : 1≤k) (om : Odd m) (hm : 1 < m)
    (eq : OeisA245212.a (2^k*m)=(σ 1 (2^k*m):ℤ)) :
    let A := m*m.divisors.card
    let F := ∑ d∈m.divisors,d*d.divisors.card
    let y := F-A
    (∀ p : ℕ, p.Prime → p∣y → p=2 ∨ p=s) →
      (k+1).Prime ∧ s=2^(k+1)-1 ∧ s.Prime ∧ s∣y := by
  dsimp only
  intro pp
  let A := m*m.divisors.card
  let F := ∑ d∈m.divisors,d*d.divisors.card
  let x := A-σ 1 m
  let y := F-A
  have r := OMA.R_OeisA245212_conjecture_R1_H2_R2.collapse k m hk om hm eq
  have yp : 0<y := Nat.sub_pos_of_lt (OMA.R_OeisA245212_conjecture_R1_H2_R2.weighted_gt m hm)
  have den : y/(x.gcd y)=Q (k+1) := reduced yp hk r.1.symm r.2
  have qd : Q (k+1)∣y := den ▸ Nat.div_dvd_of_dvd (Nat.gcd_dvd_right x y)
  have t2 : 2≤k+1 := by omega
  have qbig : 1<Q (k+1) := by
    have bd := bound t2
    have two := Nat.pow_le_pow_right (by decide : 0<2) (by omega : 1≤(k+1)/2)
    rw [pow_one] at two
    omega
  have full : Q (k+1)∣2^(k+1)-1 :=
    Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)
  have no2 : ¬2∣Q (k+1) := by
    intro d
    have a := d.trans full
    have b : 2∣(2:ℕ)^(k+1) := dvd_pow_self 2 (by omega)
    have z := Nat.two_pow_pos (k+1)
    omega
  have only {p : ℕ} (pr : p.Prime) (inside : p∣Q (k+1)) : p=s := by
    rcases pp p pr (inside.trans qd) with rfl|ok
    · exact (no2 inside).elim
    · exact ok
  let d := (Q (k+1)).minFac
  have dp : d.Prime := Nat.minFac_prime qbig.ne'
  have dd : d∣Q (k+1) := Nat.minFac_dvd _
  have ds := only dp dd
  have power : IsPrimePow (Q (k+1)) :=
    isPrimePow_iff_unique_prime_dvd.mpr ⟨d,⟨dp,dd⟩,fun p h => (only h.1 h.2).trans ds.symm⟩
  obtain ⟨ip,val,pq⟩ := prime_power_classification t2 power
  have eqs := only pq (dvd_refl _)
  exact ⟨ip,eqs.symm.trans val,eqs ▸ pq,eqs ▸ qd⟩

#print axioms surplus_two_primes
end OMA.MersenneDenominator245212
