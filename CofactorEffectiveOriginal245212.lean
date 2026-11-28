import CofactorEffectiveAtom245212
import CofactorHarmonic245212

/-! Explicit simultaneous base and exponent bounds for at least one
odd prime power of any solution with fixed dyadic exponent and rank. -/
namespace OMA.CofactorEffectiveOriginal245212
open Nat Finset ArithmeticFunction OMA.Smooth245212 OMA.CofactorEulerSeparation245212
open OMA.CofactorEffectiveAtom245212
open scoped ArithmeticFunction.sigma

def height (h r : ℕ) := threshold (W h) (σ 1 h) r
def primeHeight (h r : ℕ) :=
  let H:=2*(h*σ 0 h)
  max (height h r+1) (r*H*(σ 1 h+1)/(H-W h))

theorem original {h m : ℕ} (hh : 0<h) (hm : 1 < m) (cop : h.Coprime m)
    (apart : miss (W h) (2*(h*σ 0 h)) m.primeFactors)
    (eqn : OeisA245212.a (h*m)=(σ 1 (h*m):ℤ)) :
    ∃p∈m.primeFactors,p≤primeHeight h m.primeFactors.card ∧ m.factorization p≤height h m.primeFactors.card := by
  classical
  let t:=m.primeFactors
  let p : t→ℕ:=Subtype.val
  let e (i : t):=m.factorization (p i)
  have mn : m≠0:=by omega
  have pr (i:t) : (p i).Prime:=prime_of_mem_primeFactors i.property
  have localCop (i:t) : h.Coprime (p i):=cop.of_dvd_right (dvd_of_mem_primeFactors i.property)
  have repr : total p e=m := (Nat.prod_primeFactors_coe_pow_factorization mn).symm
  let D:=h*σ 0 h
  have d0 : 0<D:=mul_pos hh (sigma_pos 0 h hh.ne')
  have sc:=OMA.CofactorCrossOriginal245212.normalized_extension (p:=p) (e:=e) hh pr
    Subtype.val_injective localCop (repr ▸ eqn)
  have sx : (∏i,X (p i) (some (e i)))=∏x∈t,X x (some (m.factorization x)) :=
    t.prod_coe_sort (fun x=>X x (some (m.factorization x)))
  have sy : (∏i,Y (p i) (some (e i)))=∏x∈t,Y x (some (m.factorization x)) :=
    t.prod_coe_sort (fun x=>Y x (some (m.factorization x)))
  rw [sx,sy] at sc
  change ((W h:ℚ)/D)*_+((σ 1 h:ℚ)/D)*_=2 at sc
  field_simp [show (D:ℚ)≠0 by exact_mod_cast d0.ne'] at sc
  have mass : (W h:ℚ)*(∏x∈t,X x (some (m.factorization x)))+
      (σ 1 h:ℚ)*(∏x∈t,Y x (some (m.factorization x)))=((2*D:ℕ):ℚ) := by push_cast;linarith only [sc]
  rcases alternative (W h) (σ 1 h) (2*D) t m.factorization (fun _ hp=>prime_of_mem_primeFactors hp) apart mass with
    short|⟨q,hq,pq,eq⟩
  · have ne : t.Nonempty := by
      exact ⟨m.minFac,(Nat.mem_primeFactors_of_ne_zero mn).mpr ⟨Nat.minFac_prime (by omega),Nat.minFac_dvd _⟩⟩
    let q:=t.min' ne
    have mem : q∈t:=t.min'_mem ne
    have bound:=OMA.CofactorHarmonic245212.least_prime (r:=q) hh hm cop (fun r hr=>t.min'_le r hr) eqn
    have g:=(OMA.CofactorHarmonic245212.gap hh hm cop eqn).1
    have below : W h<2*D := by
      by_contra! no
      have bad:=Nat.mul_le_mul_right (σ 0 m) no
      change W h*σ 0 m+σ 1 h<2*D*σ 0 m at g
      omega
    have qp : q≤t.card*(2*D)*(σ 1 h+1)/(2*D-W h) := by
      apply (Nat.le_div_iff_mul_le (Nat.sub_pos_of_lt below)).mpr
      simpa only [D,mul_assoc] using bound
    exact ⟨q,mem,qp.trans (le_max_right _ _),short q mem⟩
  · exact ⟨q,hq,pq.trans (le_max_left _ _),eq⟩

theorem dyadic {k m : ℕ} (hm : 1 < m) (odd : Odd m)
    (eqn : OeisA245212.a (2^k*m)=(σ 1 (2^k*m):ℤ)) :
    ∃p∈m.primeFactors,p≤primeHeight (2^k) m.primeFactors.card ∧
      m.factorization p≤height (2^k) m.primeFactors.card := by
  apply original (by positivity) hm ((Nat.coprime_two_left.mpr odd).pow_left k) _ eqn
  apply miss_odd (OMA.DyadicPower245212.dyadic_odd k) (even_two_mul _)
  intro p mem
  exact Nat.coprime_two_left.mp ((Nat.coprime_two_left.mpr odd).of_dvd_right (dvd_of_mem_primeFactors mem))

#print axioms original
#print axioms dyadic
end OMA.CofactorEffectiveOriginal245212
