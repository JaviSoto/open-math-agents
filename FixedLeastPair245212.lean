import FiveFastNear245212

/-! Reusable certificates for any two-prime prefix and two moving prime powers.
The square-root primality check runs only on the bounded middle-prime interval. -/
namespace OMA.FixedLeastPair245212
open Nat ArithmeticFunction OMA.Smooth245212 OMA.CofactorEulerPair245212
open OMA.FiveFastNear245212 OMA.RankThreeFourSmallHarmonic245212
open scoped ArithmeticFunction.sigma
open private OMA.Large245212.moments from LargeExact245212
open private OMA.CofactorEulerPair245212.checked from CofactorEulerDecision245212
open private OMA.RankThreeThreeTail245212.prefix_bound OMA.RankThreeThreeTail245212.rises from RankThreeThreeTail245212

def wt (l k a : ℕ) := OMA.Large245212.wt 2 k*OMA.Large245212.wt l a
def sg (l k a : ℕ) := OMA.Large245212.sig 2 k*OMA.Large245212.sig l a
def ta (l k a : ℕ) := OMA.Large245212.tax 2 k*OMA.Large245212.tax l a

theorem veto {l k a t : ℕ} (lp : l.Prime) (odd : 2<l) (tp : 0 < t)
    (ct : (2^k*l^a).Coprime t)
    (hit : OeisA245212.a (2^k*l^a*t)=(σ 1 (2^k*l^a*t):ℤ))
    {i j : ℕ} (ik : i≤k) (ja : j≤a) : X 2 (some i)*X l (some j)<2 := by
  have cop := ((coprime_primes prime_two lp).mpr (by omega)).pow_left k |>.pow_right a
  have bound:=OMA.RankThreeThreeTail245212.prefix_bound (Nat.mul_pos (Nat.two_pow_pos k) (pow_pos lp.pos a)) tp ct hit
  rw [w_mult.map_mul_of_coprime cop,isMultiplicative_sigma.map_mul_of_coprime cop,
    sigma_zero_apply_prime_pow prime_two,sigma_zero_apply_prime_pow lp] at bound
  have mass : (0:ℚ)<((k:ℚ)+1)*2^k*(((a:ℚ)+1)*(l:ℚ)^a) := by have :=lp.pos;positivity
  have cast : (W (2^k):ℚ)*W (l^a)<2*(2^k*(l:ℚ)^a*((k:ℚ)+1)*((a:ℚ)+1)) := by
    exact_mod_cast (by simpa only [mul_assoc] using bound)
  rw [←x_factor prime_two k,←x_factor lp a] at cast
  have low : X 2 (some k)*X l (some a)<2 := (mul_lt_mul_iff_left₀ mass).mp
    (by simpa only [Nat.cast_ofNat,mul_assoc,mul_left_comm,mul_comm] using cast)
  exact lt_of_le_of_lt (mul_le_mul (OMA.RankThreeThreeTail245212.rises 2 i k prime_two ik)
    (OMA.RankThreeThreeTail245212.rises l j a lp ja) (x_nonneg lp.one_lt _) (x_nonneg prime_two.one_lt _)) low

theorem certify {l k a p q b c L M : ℕ} (lp : l.Prime) (odd : 2<l)
    (pp : p.Prime) (qp : q.Prime) (gt : l<p) (pq : p<q) (bp : 0<b) (cp : 0<c) (start : L≤p)
    (limit : (2*ta l k a).primeFactorsList.all (fun v=>decide (v≤M))=true)
    (tested : every L (primeCut (wt l k a) (sg l k a) (2*ta l k a))
      (fast (2^k*l^a) (wt l k a) (sg l k a) (ta l k a) M)=true) :
    OeisA245212.a (2^k*l^a*p^b*q^c)≠(σ 1 (2^k*l^a*p^b*q^c):ℤ) := by
  have cop (r : ℕ) (pr : r.Prime) (gr : l<r) : (2^k*l^a).Coprime r :=
    (((coprime_primes prime_two pr).mpr (by omega)).pow_left k).mul_left
      (((coprime_primes lp pr).mpr (by omega)).pow_left a)
  have inner := ((coprime_primes prime_two lp).mpr (by omega)).pow_left k |>.pow_right a
  have w : W (2^k*l^a)=wt l k a := by
    rw [w_mult.map_mul_of_coprime inner,←(OMA.Large245212.moments prime_two k).2,←(OMA.Large245212.moments lp a).2];rfl
  have s : σ 1 (2^k*l^a)=sg l k a := by
    rw [isMultiplicative_sigma.map_mul_of_coprime inner,←(OMA.Large245212.moments prime_two k).1,←(OMA.Large245212.moments lp a).1];rfl
  have t : 2^k*l^a*σ 0 (2^k*l^a)=ta l k a := by
    rw [isMultiplicative_sigma.map_mul_of_coprime inner,sigma_zero_apply_prime_pow prime_two,sigma_zero_apply_prime_pow lp,ta,OMA.Large245212.tax,OMA.Large245212.tax];ring
  have pos:=Nat.mul_pos (Nat.two_pow_pos k) (pow_pos lp.pos a)
  intro hit
  have cap:=first_prime pos pp qp (cop p pp gt) (cop q qp (by omega)) pq bp cp hit
  rw [w,s,t] at cap
  apply OMA.RankThreeFiveShort245212.sound pos pp qp (cop p pp gt) (cop q qp (by omega)) pq (by omega) bp cp _ hit
  rw [w,s,t]
  exact OMA.FiveFastNear245212.sound limit (OMA.CofactorEulerPair245212.checked tested start cap)
end OMA.FixedLeastPair245212
