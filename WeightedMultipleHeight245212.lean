import CofactorHarmonic245212
import CofactorEffectiveTree245212

/-! Explicit height for any h dividing its weighted divisor sum when the
divisor count and quotient are fixed. Applies in particular to every
candidate resonant cofactor in the odd A245212 reduction. -/
namespace OMA.WeightedMultipleHeight245212
open Nat Finset ArithmeticFunction OMA.Smooth245212
open scoped ArithmeticFunction.sigma
open private OMA.CofactorHarmonic245212.to_mass OMA.CofactorHarmonic245212.from_mass
  OMA.CofactorHarmonic245212.divisor_bounds from CofactorHarmonic245212

private theorem weight_positive {m : ℕ} (pos : 0 < m) : 0<W m := by
  rw [w_apply]
  exact sum_pos' (fun _ _=>Nat.zero_le _) ⟨1,Nat.one_mem_divisors.mpr pos.ne',by simp⟩

private theorem strict_weight {v : ℕ} (big : 1 < v) : v*σ 0 v<W v := by
  have vn : v≠0:=by omega
  rw [w_apply,sigma_zero_apply]
  have vm:=Nat.mem_divisors_self v vn
  rw [←sum_erase_add _ _ vm]
  have one : 1∈v.divisors.erase v :=
    mem_erase.mpr ⟨by omega,Nat.one_mem_divisors.mpr vn⟩
  have sub:=single_le_sum (f:=fun d : ℕ=>d*d.divisors.card) (fun _ _=>Nat.zero_le _) one
  simp at sub
  omega

/-- After selecting a unitary prefix u of a weighted multiple, the smallest
remaining prime p obeys p*(j*u-W(u)*tau(v)) ≤ rank(v)*j*u. -/
theorem next {u v j p : ℕ} (up : 0 < u) (vp : 1 < v) (cop : u.Coprime v)
    (lower : ∀q∈v.primeFactors,p≤q) (eqn : W (u*v)=j*(u*v)) :
    W u*σ 0 v < j*u ∧ p*(j*u-W u*σ 0 v)≤v.primeFactors.card*(j*u) := by
  have vn : v≠0:=by omega
  rw [w_mult.map_mul_of_coprime cop,←mul_assoc] at eqn
  have wu:=weight_positive up
  have gap : W u*σ 0 v<j*u := by
    apply Nat.lt_of_mul_lt_mul_right (a:=v)
    have s:=Nat.mul_lt_mul_of_pos_left (strict_weight vp) wu
    nlinarith only [s,eqn]
  have wbound:=(OMA.CofactorHarmonic245212.divisor_bounds vp).2.2
  have phi:=OMA.CofactorHarmonic245212.phi_sigma v
  have totientBound : j*u*v.totient≤W u*σ 0 v*v := by
    apply Nat.le_of_mul_le_mul_right (c:=v) _ (by omega)
    have a:=Nat.mul_le_mul_right v.totient (Nat.mul_le_mul_left (W u) wbound)
    have b:=Nat.mul_le_mul_left (W u*σ 0 v) phi
    nlinarith only [a,b,congrArg (·*v.totient) eqn]
  have mass : (j*u-W u*σ 0 v)*v≤j*u*(v-v.totient) := by
    have g:=Nat.sub_add_cancel gap.le
    have l:=Nat.sub_add_cancel v.totient_le
    nlinarith only [totientBound,congrArg (·*v) g,congrArg (j*u*·) l]
  exact ⟨gap,OMA.CofactorHarmonic245212.from_mass lower (OMA.CofactorHarmonic245212.to_mass (by omega) mass)⟩

/-- Iterating this simple increasing bound once per remaining prime gives a
height independent of all the unknown bases and exponents. -/
def limit (D j r : ℕ) : ℕ→ℕ
  | 0=>1
  | i+1=>let u:=limit D j r i;u*(r*j*u+1)^D

theorem bounded {n j : ℕ} (pos : 0 < n) (eqn : W n=j*n) :
    n≤limit (σ 0 n) j n.primeFactors.card n.primeFactors.card := by
  let D:=σ 0 n
  let r:=n.primeFactors.card
  have step (s : ℕ) : ∀{u v : ℕ}, u*v=n → u.Coprime v → v.primeFactors.card=s →
      ∀i, i+s=r → u≤limit D j r i → n≤limit D j r r := by
    induction s with
    | zero =>
      intro u v id _ card i total bounded
      have emp:=primeFactors_eq_empty.mp (card_eq_zero.mp card)
      have non : v≠0:=by intro zero;simp [zero] at id;omega
      have one : v=1:=by omega
      have same : u=n:=by simpa only [one,mul_one] using id
      simpa only [same,show i=r by omega] using bounded
    | succ s ih =>
      intro u v id cop card i total bounded
      have uv : 0<u*v:=id ▸ pos
      have up:=Nat.pos_of_mul_pos_right uv
      have v0:=Nat.pos_of_mul_pos_left uv
      have big : 1 < v:=by
        by_contra! low
        have unit : v=1:=by omega
        simp [unit] at card
      have ne:=Nat.nonempty_primeFactors.mpr big
      let p:=v.primeFactors.min' ne
      have mp : p∈v.primeFactors:=v.primeFactors.min'_mem ne
      have hp:=prime_of_mem_primeFactors mp
      obtain ⟨gap,b⟩:=next (p:=p) up big cop (fun q mq=>v.primeFactors.min'_le _ mq) (id ▸ eqn)
      have pbound : p≤r*j*limit D j r i := by
        calc
          p ≤ p*(j*u-W u*σ 0 v) := Nat.le_mul_of_pos_right _ (Nat.sub_pos_of_lt gap)
          _ ≤ v.primeFactors.card*(j*u) := b
          _ ≤ r*(j*limit D j r i) := Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ bounded)
          _ = _ := by ring
      let e:=v.factorization p
      let t:=ordCompl[p] v
      have powCop := Nat.coprime_ordCompl hp v0.ne'
      have rep : p^e*t=v:=Nat.ordProj_mul_ordCompl_eq_self v p
      have nid : u*p^e*t=n := by rw [mul_assoc,rep,id]
      have nc:=(cop.of_dvd_right (Nat.ordCompl_dvd v p)).mul_left (powCop.pow_left e)
      have cr : t.primeFactors.card=s:=by
        rw [show t.primeFactors=v.primeFactors.erase p from OMA.CofactorEffectiveTree245212.support_rest v p,
          card_erase_of_mem mp,card];omega
      have eBound : e≤D := by
        have scale : D=(σ 0 u)*((e+1)*(σ 0 t)) := by
          change σ 0 n=_
          rw [←id,isMultiplicative_sigma.map_mul_of_coprime cop,←rep,
            isMultiplicative_sigma.map_mul_of_coprime (powCop.pow_left e),sigma_zero_apply_prime_pow hp]
        have t0 : 0<t:=Nat.ordCompl_pos p v0.ne'
        have eu:=sigma_pos 0 u up.ne'
        have et:=sigma_pos 0 t t0.ne'
        calc
          e ≤ (e+1)*σ 0 t := (Nat.le_succ e).trans (Nat.le_mul_of_pos_right _ et)
          _ ≤ σ 0 u*((e+1)*σ 0 t) := Nat.le_mul_of_pos_left _ eu
          _ = D := scale.symm
      apply ih nid nc cr (i+1) (by omega)
      exact Nat.mul_le_mul bounded ((Nat.pow_le_pow_left (pbound.trans (Nat.le_succ _)) _).trans
        (Nat.pow_le_pow_right (Nat.succ_pos _) eBound))
  exact step r (u:=1) (v:=n) (one_mul n) (Nat.coprime_one_left _) rfl 0 (zero_add r) le_rfl

/-- A uniform height indexed by the divisor count alone, without assuming a
prior bound on the rank, cofactor, or quotient. -/
def atCount (D : ℕ) :=
  limit D (D^2) D D

private theorem limit_params {D j r J R : ℕ} (a : j≤J) (b : r≤R) (i : ℕ) :
    limit D j r i≤limit D J R i := by
  induction i with
  | zero => rfl
  | succ i ih => simp only [limit];gcongr

private theorem limit_index (D j r : ℕ) : Monotone (limit D j r) := by
  apply monotone_nat_of_le_succ
  intro i
  exact Nat.le_mul_of_pos_right _ (pow_pos (Nat.succ_pos _) _)

theorem divisor_count {n : ℕ} (pos : 0 < n) (hit : n∣W n) : n ≤ atCount (σ 0 n) := by
  obtain ⟨j,id⟩:=hit
  have eqn : W n=j*n := by rw [id,mul_comm]
  have weight : W n≤n*(σ 0 n)^2 := by
    rw [w_apply,sigma_zero_apply]
    calc
      (∑ d∈n.divisors,d*d.divisors.card) ≤ ∑ _d∈n.divisors,n*n.divisors.card :=
        sum_le_sum fun d hd=>Nat.mul_le_mul (Nat.le_of_dvd pos (Nat.mem_divisors.mp hd).1)
          (card_le_card (Nat.divisors_subset_of_dvd pos.ne' (Nat.mem_divisors.mp hd).1))
      _ = _ := by simp [pow_two,mul_left_comm]
  have jBound : j≤(σ 0 n)^2 := Nat.le_of_mul_le_mul_left (id ▸ weight) pos
  have rank : n.primeFactors.card≤σ 0 n := by
    rw [sigma_zero_apply]
    exact card_le_card fun p mp=>Nat.mem_divisors.mpr ⟨dvd_of_mem_primeFactors mp,pos.ne'⟩
  exact (bounded pos eqn).trans ((limit_params jBound rank _).trans (limit_index _ _ _ rank))

#print axioms divisor_count
#print axioms next
#print axioms bounded
end OMA.WeightedMultipleHeight245212
