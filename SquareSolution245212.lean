import EvenScreen245212
import SquareCoreBound245212

/-! Apply the quadratic large-prime cutoff to the original divisor equality. -/

namespace OMA.SquareCoreBound245212
open Nat Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma
open OMA.R_OeisA245212_conjecture_R1_H2_R1_H2_R1
open private OMA.R_OeisA245212_conjecture_R1_H2_R1.linear_criterion
  OMA.R_OeisA245212_conjecture_R1_H2_R1.moment_mul
  OMA.R_OeisA245212_conjecture_R1_H2_R1.moment_at_power
  from OMAReductions.R_OeisA245212_conjecture_R1_H2_R1
open private OMA.R_OeisA245212_conjecture_R1_H2_R1_H2_R1.power_moments from EvenScreen245212

/-- The finite base cutoff starts at the original OEIS sequence equality. -/
theorem original_bounds {k q p : ℕ} (hk : 1≤k) (hq : q.Prime) (hp : p.Prime)
    (oq : Odd q) (op : Odd p) (ne : p≠q)
    (eqn : OeisA245212.a (p*(2^k*q^2))=(σ 1 (p*(2^k*q^2)):ℤ)) :
    q<2^20 ∧ k≤174 ∧ 0<den k q (2^(k+1)) ∧
      num k q (2^(k+1))=(p:ℤ)*den k q (2^(k+1)) := by
  let u := q^2
  let b := 2^k*u
  have ou : Odd u := oq.pow
  have c2 := (Nat.coprime_two_left.mpr ou).pow_left k
  have cp : p.Coprime b := ((Nat.coprime_two_right.mpr op).pow_right k).mul_right
    (((Nat.coprime_primes hp hq).mpr ne).pow_right 2)
  have bp : 0<b := by dsimp [b,u]; positivity [hq.pos]
  have cr := (OMA.R_OeisA245212_conjecture_R1_H2_R1.linear_criterion p b hp bp cp).mp eqn
  change 0<D b ∧ N b=p*D b at cr
  have dv : D b∣N b := ⟨p,cr.2.trans (Nat.mul_comm _ _)⟩
  obtain ⟨_,logcap,_⟩ := screen_proof k u ou cr.1 dv
  have wu : W u=3*q^2+2*q+1 := by
    unfold W u
    rw [OMA.R_OeisA245212_conjecture_R1_H2_R1.moment_at_power _ _ hq]
    simp [sum_range_succ]; ring
  have su : S u=q^2+q+1 := by
    unfold S u; rw [sigma_apply_prime_pow hq]; simp [sum_range_succ]; ring
  have tu : T u=3*q^2 := by
    unfold T u; rw [Nat.divisors_prime_pow hq,card_map,card_range]; ring
  have diff : W u-S u=2*q^2+q := by rw [wu,su]; omega
  have coef : C u+K u ≤ 128*q^4 := by
    unfold C K; rw [diff,wu,su,tu]
    have a := hq.two_le
    have b1 := Nat.pow_le_pow_right hq.pos (by decide : 1≤4)
    have b2 := Nat.pow_le_pow_right hq.pos (by decide : 2≤4)
    have b3 := Nat.pow_le_pow_right hq.pos (by decide : 3≤4)
    simp only [pow_one] at b1
    nlinarith only [b1,b2,b3,a]
  have geom := OMA.R_OeisA245212_conjecture_R1_H2_R1_H2_R1.power_moments k
  have wb : W b=(k*2^(k+1)+1)*W u := by
    unfold b W
    rw [OMA.R_OeisA245212_conjecture_R1_H2_R1.moment_mul _ _ c2,
      OMA.R_OeisA245212_conjecture_R1_H2_R1.moment_at_power _ _ Nat.prime_two,geom.1]
  have sb : S b+S u=2^(k+1)*S u := by
    unfold b S
    rw [isMultiplicative_sigma.map_mul_of_coprime c2,sigma_apply_prime_pow Nat.prime_two]
    simpa only [mul_one,add_mul,one_mul] using congrArg (fun z : ℕ => z*(σ 1 u)) geom.2
  have tb : T b=2^k*(k+1)*T u := by
    unfold b T; rw [c2.card_divisors_mul,Nat.divisors_prime_pow Nat.prime_two,card_map,card_range]; ring
  have da : D b+(2*W b+S b)=4*T b :=
    (Nat.sub_add_cancel (Nat.le_of_lt (Nat.sub_pos_iff_lt.mp cr.1))).trans (by unfold T; ring)
  rw [wu] at wb; rw [su] at sb; rw [tu] at tb
  zify at wb sb tb da
  have deneq : (D b:ℤ)=den k q (2^(k+1)) := by
    unfold den
    rw [pow_succ (2:ℤ) k] at wb sb ⊢
    linear_combination da-2*wb-sb+4*tb
  have numeq : (N b:ℤ)=num k q (2^(k+1)) := by
    unfold N num; push_cast
    linear_combination wb+sb
  have hd : 0<den k q (2^(k+1)) := by rw [←deneq]; exact_mod_cast cr.1
  have hn : num k q (2^(k+1))=(p:ℤ)*den k q (2^(k+1)) := by rw [←deneq,←numeq]; exact_mod_cast cr.2
  have cut := square_cutoff hk hq.two_le coef (by omega) hd hn
  have ceiling : C u+K u≤2^87 :=
    (coef.trans (Nat.mul_le_mul_left 128 (Nat.pow_le_pow_left cut.le 4))).trans (by decide)
  have bound := Nat.log_mono_right (b:=2) ceiling
  rw [Nat.log_pow (by decide)] at bound
  exact ⟨cut,by omega,hd,hn⟩

#print axioms original_bounds
end OMA.SquareCoreBound245212
