import RankThreeFourSmallFast245212

/-! Only four prefixes with dyadic exponent at least three and least
odd prime three survive, even if the number of further primes is arbitrary. -/
namespace OMA.RankThreeThreeTail245212
open Nat Finset ArithmeticFunction OMA.Smooth245212 OMA.CofactorEulerPair245212
open OMA.RankThreeFourSmallHarmonic245212
open scoped ArithmeticFunction.sigma
open private OMA.CofactorEulerPair245212.checked from CofactorEulerDecision245212

private theorem prefix_bound {h t : ℕ} (hh : 0 < h) (ht : 0 < t) (cop : h.Coprime t)
    (eqn : OeisA245212.a (h*t)=(σ 1 (h*t):ℤ)) : W h<2*(h*σ 0 h) := by
  by_cases unit : t=1
  · subst t
    simp only [mul_one] at eqn
    have bal:=OMA.Abundance245212.balance hh.ne' eqn
    have sp:=sigma_pos 1 h hh.ne'
    nlinarith
  · have g:=(OMA.CofactorHarmonic245212.gap hh (by omega) cop eqn).1
    by_contra! no
    have b:=Nat.mul_le_mul_right (σ 0 t) no
    omega

private theorem rises (p i j : ℕ) (pr : p.Prime) (le : i≤j) : X p (some i)≤X p (some j) :=
  add_le_add_right (div_le_div_of_nonneg_right (sub_le_sub_left (y_anti pr.one_lt le) 1)
    (sub_nonneg.mpr (by exact_mod_cast pr.one_le))) 1

theorem prefixes {k a t : ℕ} (kl : 3≤k) (ap : 0<a) (tp : 0 < t)
    (ct : (2^k*3^a).Coprime t)
    (eqn : OeisA245212.a (2^k*3^a*t)=(σ 1 (2^k*3^a*t):ℤ)) :
    (k=3 ∧ a=1) ∨ (k=3 ∧ a=2) ∨ (k=4 ∧ a=1) ∨ (k=5 ∧ a=1) := by
  have c : (2^k).Coprime (3^a) := ((by decide : Coprime 2 3).pow_left k).pow_right a
  have bound:=prefix_bound (by positivity) tp ct eqn
  rw [w_mult.map_mul_of_coprime c,isMultiplicative_sigma.map_mul_of_coprime c,
    sigma_zero_apply_prime_pow prime_two,sigma_zero_apply_prime_pow prime_three] at bound
  have x2:=x_factor prime_two k
  have x3:=x_factor prime_three a
  have low : X 2 (some k)*X 3 (some a)<2 := by
    have mass : (0:ℚ)<((k:ℚ)+1)*2^k*(((a:ℚ)+1)*3^a) := by positivity
    apply (mul_lt_mul_iff_left₀ mass).mp
    have cast : (W (2^k):ℚ)*W (3^a)<2*(2^k*3^a*((k:ℚ)+1)*((a:ℚ)+1)) := by
      exact_mod_cast (by simpa only [mul_assoc] using bound)
    rw [←x2,←x3] at cast
    simpa only [Nat.cast_ofNat,mul_assoc,mul_left_comm,mul_comm] using cast
  have veto (i j : ℕ) (ik : i≤k) (ja : j≤a) (hit : 2≤X 2 (some i)*X 3 (some j)) : False := by
    have both:=mul_le_mul (rises 2 i k prime_two ik) (rises 3 j a prime_three ja)
      (x_nonneg prime_three.one_lt _) (x_nonneg prime_two.one_lt _)
    exact low.not_ge (hit.trans both)
  have k6 : k<6 := by
    by_contra! high;exact veto 6 1 high ap (by decide +kernel)
  have a3 : a<3 := by
    by_contra! high;exact veto 3 3 kl high (by decide +kernel)
  have a2 : 4≤k → a<2 := by
    intro hk;by_contra! high;exact veto 4 2 hk high (by decide +kernel)
  omega

def cert (h : ℕ) := every 5 (primeCut (W h) (σ 1 h) (2*(h*σ 0 h)))
  (OMA.RankThreeFourSmallFast245212.run h (W h) (σ 1 h) (h*σ 0 h))

theorem certified {h p q b d : ℕ} (hh : 0 < h) (hp : p.Prime) (hq : q.Prime) (lo : 5≤p)
    (pq : p<q) (bp : 0<b) (dp : 0<d) (cp : h.Coprime p) (cq : h.Coprime q)
    (ok : cert h=true) : OeisA245212.a (h*p^b*q^d)≠(σ 1 (h*p^b*q^d):ℤ) := by
  intro eqn
  have hi:=first_prime hh hp hq cp cq pq bp dp eqn
  exact OMA.RankThreeFourSmallFast245212.sound hh hp hq (by omega) cp cq pq bp dp
    (OMA.CofactorEulerPair245212.checked ok lo hi) eqn

#print axioms prefixes
#print axioms certified
end OMA.RankThreeThreeTail245212
