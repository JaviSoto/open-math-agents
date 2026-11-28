import OddCountResidue245212

/-! A count-only congruence sieve for all possible odd divisor counts in A245212. -/
namespace OMA.CountPrimeLayer245212
open Nat Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

private theorem product_one {H : ℕ} (l : List ℕ) (h : ∀ p∈l,p ≡ 1 [MOD H]) :
    l.prod ≡ 1 [MOD H] := by
  induction l with
  | nil => exact Nat.ModEq.refl _
  | cons p l ih =>
    simpa only [List.prod_cons,one_mul] using
      (h p (.head _)).mul (ih (fun q hq => h q (.tail _ hq)))

/-- If every prime factor of the odd divisor count is 1 modulo 2^s,
then the count has to be 1 modulo twice that modulus at equality. -/
theorem lift {h k m : ℕ} (om : Odd m)
    (primeLayer : ∀ p : ℕ,p.Prime → p ∣ σ 0 m → p ≡ 1 [MOD 2^(h+1)])
    (eqn : OeisA245212.a (2^k*m)=(σ 1 (2^k*m):ℤ)) :
    σ 0 m ≡ 1 [MOD 2^(h+2)] := by
  let H := 2^(h+1)
  have tau : σ 0 m=∏ p∈m.primeFactors,(m.factorization p+1) := by
    rw [sigma_zero_apply,Nat.card_divisors om.pos.ne']
  have exps (p : ℕ) (hp : p∈m.primeFactors) : H∣m.factorization p := by
    let d := m.factorization p+1
    have dv : d∣σ 0 m := by rw [tau]; exact dvd_prod_of_mem _ hp
    have all : d ≡ 1 [MOD H] := by
      rw [←Nat.prod_primeFactorsList (show d≠0 from Nat.succ_ne_zero _)]
      exact product_one _ fun q hq => primeLayer q (Nat.prime_of_mem_primeFactorsList hq)
        ((Nat.dvd_of_mem_primeFactorsList hq).trans dv)
    exact Nat.modEq_zero_iff_dvd.mp (all.add_right_cancel' 1)
  let u := ∏ p∈m.primeFactors,p^(m.factorization p/H)
  have rep : u^H=m := by
    dsimp only [u]
    rw [←prod_pow]
    conv_rhs => rw [Nat.prod_primeFactors_pow_factorization om.pos.ne']
    exact prod_congr rfl fun p hp => by rw [←pow_mul,Nat.div_mul_cancel (exps p hp)]
  have odd : Odd u := by
    apply Nat.not_even_iff_odd.mp
    intro he
    exact om.not_two_dvd_nat (rep ▸ ((even_iff_two_dvd.mp he).trans
      (dvd_pow_self u (pow_ne_zero _ (by decide : 2≠0)))))
  rw [←rep] at eqn ⊢
  exact OMA.OddCountResidue245212.power_count odd eqn

/-- An odd prime power can be the odd divisor count only with an even exponent. -/
theorem prime_power {p s k m : ℕ} (pp : p.Prime) (op : Odd p) (om : Odd m)
    (count : σ 0 m=p^s) (eqn : OeisA245212.a (2^k*m)=(σ 1 (2^k*m):ℤ)) :
    Even s := by
  by_contra neg
  obtain ⟨j,hj⟩ := Nat.not_even_iff_odd.mp neg
  have pos : p-1≠0 := by have := pp.one_lt; omega
  obtain ⟨h,u,nu,dec⟩ := Nat.exists_eq_pow_mul_and_not_dvd pos 2 (by decide)
  cases h with
  | zero =>
    simp only [pow_zero,one_mul] at dec
    have odd := op
    rw [Nat.odd_iff] at odd
    omega
  | succ h =>
    let H := 2^(h+1)
    have pe : p=1+H*u := by change p-1=H*u at dec; omega
    have lm : p ≡ 1 [MOD H] := by simp [pe,Nat.ModEq,H]
    have good := lift (h:=h) om (fun q hq d => by
      rw [count] at d
      have same := (Nat.prime_dvd_prime_iff_eq hq pp).mp (hq.dvd_of_dvd_pow d)
      simpa [same] using lm) eqn
    have twice : 2^(h+2)=2*H := pow_succ' _ _
    rw [count,twice] at good
    have Htwo : 2∣H := dvd_pow_self _ (by omega)
    obtain ⟨v,hv⟩ := Htwo
    have sq : p^2 ≡ 1 [MOD 2*H] := by
      rw [pe,show (1+H*u)^2=2*H*(u+v*u^2)+1 by rw [hv]; ring]
      simp [Nat.ModEq]
    have red : p^s ≡ p [MOD 2*H] := by
      rw [hj,pow_succ,pow_mul]
      simpa using (sq.pow j).mul_right p
    have one := red.symm.trans good
    have last : 2*H∣H*u := by
      apply Nat.modEq_zero_iff_dvd.mp
      apply Nat.ModEq.add_right_cancel' 1
      simpa [pe,add_comm] using one
    have hp : 0<H := by dsimp [H]; positivity
    rw [Nat.mul_comm 2 H] at last
    exact nu ((Nat.dvd_of_mul_dvd_mul_left hp last))

#print axioms lift
#print axioms prime_power
end OMA.CountPrimeLayer245212
