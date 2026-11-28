import FixedLeastPoleWindows245212

/-! Skip the entire initial middle-prime interval before running any
prime or exponent tests. The first possible prime follows from its first
weighted moment and monotonicity at every higher exponent. -/
namespace OMA.FixedLeastStart245212
open Nat ArithmeticFunction OMA.Smooth245212 OMA.FixedLeastPair245212 OMA.CofactorEulerPair245212
open scoped ArithmeticFunction.sigma
open private OMA.Large245212.moments from LargeExact245212
open private OMA.RankThreeThreeTail245212.rises from RankThreeThreeTail245212

theorem scalar {A H p q b c : ℕ} (pp : p.Prime) (qp : q.Prime) (bp : 0<b)
    (strict : (A:ℚ)*(X p (some b)*X q (some c))<H) : A/(2*(H-A))+1≤p := by
  have one : 1≤X q (some c):=le_add_of_nonneg_right (div_nonneg (sub_nonneg.mpr (y_one qp.one_lt _))
    (sub_nonneg.mpr (by exact_mod_cast qp.one_le)))
  have low:=(OMA.RankThreeThreeTail245212.rises p 1 b pp bp).trans
    (le_mul_of_one_le_right (x_nonneg pp.one_lt _) one)
  have small:=(mul_le_mul_of_nonneg_left low (Nat.cast_nonneg A : (0:ℚ)≤A)).trans_lt strict
  have lin:=x_factor pp 1
  have calcW : W (p^1)=1+2*p:=by rw [w_pow pp];simp [Finset.sum_range_succ];ring
  rw [calcW] at lin
  push_cast at lin;simp only [pow_one] at lin
  have pr : (0:ℚ)<p:=by exact_mod_cast pp.pos
  have integer : A*(2*p+1)<H*(2*p):=by
    have scale:=congrArg (fun z:ℚ=>(A:ℚ)*z) lin
    have lg:=mul_lt_mul_of_pos_right small (show (0:ℚ)<2*p by positivity)
    exact_mod_cast (by nlinarith only [lg,scale] : (A:ℚ)*(2*p+1)<H*(2*p))
  have ah : A<H:=by
    by_contra! no;have :=Nat.mul_le_mul_right (2*p) no;nlinarith
  have eql:=congrArg (·*(2*p)) (Nat.sub_add_cancel ah.le)
  have lt : A<p*(2*(H-A)):=by nlinarith only [integer,eql]
  exact (Nat.div_lt_iff_lt_mul (Nat.mul_pos (by decide) (Nat.sub_pos_of_lt ah))).mpr lt

theorem fixed {l k a p q b c : ℕ} (lp : l.Prime) (odd : 2<l) (pp : p.Prime) (qp : q.Prime)
    (gt : l<p) (pq : p<q) (bp : 0<b)
    (hit : OeisA245212.a (2^k*l^a*p^b*q^c)=(σ 1 (2^k*l^a*p^b*q^c):ℤ)) :
    wt l k a/(2*(2*ta l k a-wt l k a))+1≤p := by
  let h:=2^k*l^a
  have pos : 0<h:=Nat.mul_pos (Nat.two_pow_pos k) (pow_pos lp.pos a)
  have cop (r : ℕ) (pr : r.Prime) (gr : l<r) : h.Coprime r :=
    (((coprime_primes prime_two pr).mpr (by omega)).pow_left k).mul_left
      (((coprime_primes lp pr).mpr (by omega)).pow_left a)
  have inner:=((coprime_primes prime_two lp).mpr (by omega)).pow_left k |>.pow_right a
  have w : W h=wt l k a:=by
    dsimp [h];rw [w_mult.map_mul_of_coprime inner,←(OMA.Large245212.moments prime_two k).2,←(OMA.Large245212.moments lp a).2];rfl
  have t : h*σ 0 h=ta l k a:=by
    dsimp [h];rw [isMultiplicative_sigma.map_mul_of_coprime inner,sigma_zero_apply_prime_pow prime_two,sigma_zero_apply_prime_pow lp,ta,OMA.Large245212.tax,OMA.Large245212.tax];ring
  rw [←w,←t]
  apply scalar (b:=b) (c:=c) pp qp bp
  apply OMA.RankThreeFourSmallBounds245212.strict pp qp (sigma_pos 1 h pos.ne')
  simpa only [OMA.RankThreeFourSmallBounds245212.Bal,Nat.cast_mul,Nat.cast_ofNat] using
    normalized pos pp qp (cop p pp gt) (cop q qp (by omega)) pq.ne hit

#print axioms fixed
end OMA.FixedLeastStart245212
