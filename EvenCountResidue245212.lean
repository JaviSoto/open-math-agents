import ParityResearch245212

/-! Every even odd-divisor count at equality has a prime factor which is 3 mod 4. -/
namespace OMA.EvenCountResidue245212
open Nat Finset ArithmeticFunction OMA.Smooth245212
open scoped ArithmeticFunction.sigma

private theorem prime_three : ∀ d : ℕ, d%4=3 → ∃ l : ℕ, l.Prime ∧ l∣d ∧ l%4=3 := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro mod
    have one : d≠1 := by omega
    obtain ⟨l,hl,dv⟩ := Nat.exists_prime_and_dvd one
    obtain ⟨s,hs⟩ := dv
    by_cases good : l%4=3
    · exact ⟨l,hl,⟨s,hs⟩,good⟩
    have reduce : s<d := by
      have nz : s≠0 := by rintro rfl; simp at hs; omega
      have lt := Nat.mul_lt_mul_of_pos_right hl.one_lt (Nat.pos_of_ne_zero nz)
      simpa only [one_mul,←hs] using lt
    rw [hs,Nat.mul_mod] at mod
    have sm : s%4=3 := by
      have ll := Nat.mod_lt l (by decide : 0<4)
      have ss := Nat.mod_lt s (by decide : 0<4)
      interval_cases l%4 <;> interval_cases s%4 <;> norm_num at *
    obtain ⟨r,hr,rd,rm⟩ := ih s reduce sm
    exact ⟨r,hr,rd.trans (hs ▸ dvd_mul_left s l),rm⟩

theorem even_count {k m : ℕ} (om : Odd m) (ec : Even (σ 0 m))
    (eqn : OeisA245212.a (2^k*m)=(σ 1 (2^k*m):ℤ)) :
    ∃ l : ℕ, l.Prime ∧ l∣σ 0 m ∧ l%4=3 := by
  let p : m.primeFactors → ℕ := Subtype.val
  let e (i : m.primeFactors) := m.factorization i
  have hp (i : m.primeFactors) := Nat.prime_of_mem_primeFactors i.property
  have op (i : m.primeFactors) : Odd (p i) := by
    apply Nat.not_even_iff_odd.mp
    intro ev
    exact om.not_two_dvd_nat ((even_iff_two_dvd.mp ev).trans (Nat.dvd_of_mem_primeFactors i.property))
  have rep : total p e=m := (Nat.prod_primeFactors_coe_pow_factorization om.pos.ne').symm
  have counts : σ 0 m=∏ q∈m.primeFactors,(m.factorization q+1) := by
    rw [sigma_zero_apply,Nat.card_divisors om.pos.ne']
  have even := even_iff_two_dvd.mp ec
  rw [counts] at even
  obtain ⟨q,hq,div⟩ := ((Nat.prime_iff.mp Nat.prime_two).dvd_finsetProd_iff (fun q => m.factorization q+1)).mp even
  have nonsq : ∃ i,Odd (e i) :=
    ⟨⟨q,hq⟩,Nat.odd_iff.mpr (show m.factorization q%2=1 by omega)⟩
  obtain ⟨i,ii⟩ := OMA.ExponentParity245212.two_mod_four p e hp op Subtype.val_injective k (by rw [rep]; exact eqn) nonsq
  obtain ⟨l,hl,ld,lm⟩ := prime_three (e i+1) (by omega)
  have fac : e i+1∣σ 0 m := by rw [counts]; exact Finset.dvd_prod_of_mem _ i.property
  exact ⟨l,hl,ld.trans fac,lm⟩

#print axioms even_count
end OMA.EvenCountResidue245212
