import FormalConjectures.OEIS.«245212»

/-! Project out the last prime power of an A245212 solution over any
auxiliary prime field. The cofactor may include the full power of two. -/

namespace OMA.TailProjection245212
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.sigma

def weighted : ArithmeticFunction ℕ :=
  (ArithmeticFunction.id.pmul (σ 0)) * ArithmeticFunction.zeta

private theorem multiplicative : weighted.IsMultiplicative :=
  (isMultiplicative_id.pmul isMultiplicative_sigma).mul isMultiplicative_zeta

private theorem weighted_apply (n : ℕ) :
    weighted n = ∑ d ∈ n.divisors, d * d.divisors.card := by
  rw [weighted, mul_zeta_apply]
  simp only [pmul_apply, id_apply, sigma_zero_apply]

def w {R : Type*} [CommSemiring R] (a : ℕ) (x : R) : R :=
  ∑ j ∈ range (a+1), x^j * (j+1)

def s {R : Type*} [CommSemiring R] (a : ℕ) (x : R) : R :=
  ∑ j ∈ range (a+1), x^j

private theorem weighted_pow {x : ℕ} (hx : x.Prime) (a : ℕ) :
    weighted (x^a) = w a x := by
  rw [weighted_apply, Nat.sum_divisors_prime_pow hx]
  simp [w, Nat.divisors_prime_pow hx]

private theorem balance {n : ℕ} (hn : n≠0)
    (eq : OeisA245212.a n=(σ 1 n:ℤ)) : weighted n+σ 1 n=2*n*(σ 0 n) := by
  have total : weighted n = n*n.divisors.card+∑ d∈n.properDivisors,d*d.divisors.card := by
    calc
      _ = ∑ d∈insert n n.properDivisors,d*d.divisors.card := by
        rw [Nat.insert_self_properDivisors hn,weighted_apply]
      _ = _ := sum_insert Nat.self_notMem_properDivisors
  unfold OeisA245212.a at eq
  zify at total ⊢
  simp only [sigma_zero_apply]
  linarith

theorem identity {M x y : ℕ} (a b : ℕ) (hM : M≠0) (hx : x.Prime) (hy : y.Prime)
    (cx : M.Coprime x) (cy : (M*x^a).Coprime y)
    (eq : OeisA245212.a (M*x^a*y^b) = (σ 1 (M*x^a*y^b) : ℤ)) :
    (2*M*(σ 0 M)*(a+1)*(b+1))*x^a*y^b =
      weighted M*w a x*w b y + (σ 1 M)*s a x*s b y := by
  have bal := balance (mul_ne_zero (mul_ne_zero hM (pow_ne_zero _ hx.ne_zero))
    (pow_ne_zero _ hy.ne_zero)) eq
  rw [multiplicative.map_mul_of_coprime (cy.pow_right b),
    multiplicative.map_mul_of_coprime (cx.pow_right a),
    isMultiplicative_sigma.map_mul_of_coprime (cy.pow_right b),
    isMultiplicative_sigma.map_mul_of_coprime (cx.pow_right a),
    isMultiplicative_sigma.map_mul_of_coprime (cy.pow_right b),
    isMultiplicative_sigma.map_mul_of_coprime (cx.pow_right a),
    weighted_pow hx,weighted_pow hy,sigma_one_apply_prime_pow hx,sigma_one_apply_prime_pow hy,
    sigma_zero_apply_prime_pow hx,sigma_zero_apply_prime_pow hy] at bal
  dsimp only [s]
  rw [bal]
  ring

/-- The exact necessary image-membership test used for each auxiliary prime:
    the last base gives a nonzero residue and both displayed divisions are valid. -/
theorem project (p : ℕ) [Fact p.Prime] {M x y : ℕ} (a b : ℕ) (hM : M≠0)
    (hx : x.Prime) (hy : y.Prime) (py : p<y)
    (cx : M.Coprime x) (cy : (M*x^a).Coprime y)
    (eq : OeisA245212.a (M*x^a*y^b) = (σ 1 (M*x^a*y^b) : ℤ)) :
    ∃ z : ZMod p, z ≠ 0 ∧
      ((2*M*(σ 0 M)*(a+1)*(b+1) : ℕ) : ZMod p)*(x:ZMod p)^a =
      (weighted M:ZMod p)*w a (x:ZMod p)*(w b z/z^b) +
      ((σ 1 M:ℕ):ZMod p)*s a (x:ZMod p)*(s b z/z^b) := by
  have nz : (y:ZMod p)≠0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun dy => (Nat.dvd_prime hy).mp dy |>.elim
      (fun ep => (Fact.out (p := p.Prime)).ne_one ep) (fun ep => py.ne ep)
  refine ⟨y,nz,?_⟩
  have modEq := congrArg (fun n : ℕ => (n : ZMod p)) (identity a b hM hx hy cx cy eq)
  simp only [w,s,Nat.cast_add,Nat.cast_mul,Nat.cast_sum,Nat.cast_pow,Nat.cast_one] at modEq ⊢
  field_simp [nz]
  simpa using modEq

private theorem dyadic_balance (k : ℕ) :
    weighted (2^k)+σ 1 (2^k)=2*2^k*(σ 0 (2^k)) := by
  rw [weighted_pow Nat.prime_two,sigma_zero_apply_prime_pow Nat.prime_two,
    sigma_one_apply_prime_pow Nat.prime_two]
  unfold w
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ _ (k+1),sum_range_succ _ (k+1),pow_succ]
    simpa using (show _ from by push_cast at *; linarith only [ih])

private theorem common_multiplier {Q H U V : ℤ} (cop : IsCoprime Q H)
    (rel : Q*V=H*U) : ∃ h : ℤ, U=h*Q ∧ V=h*H := by
  obtain ⟨a,b,bez⟩ := cop
  exact ⟨a*U+b*V,by linear_combination -U*bez-b*rel,by linear_combination -V*bez+a*rel⟩

/-- The two surpluses are integer multiples of a single reduced slope, also at k=0. -/
theorem surpluses (k m : ℕ) (odd : Odd m)
    (eq : OeisA245212.a (2^k*m)=(σ 1 (2^k*m):ℤ)) :
    let G := σ 1 (2^k)
    let F := weighted (2^k)
    let J := m*(σ 0 m)
    ∃ h : ℤ, (weighted m:ℤ)-J=h*(G/(G.gcd F):ℕ) ∧
      (J:ℤ)-(σ 1 m:ℕ)=h*(F/(G.gcd F):ℕ) := by
  let G := σ 1 (2^k)
  let F := weighted (2^k)
  let g := G.gcd F
  let Q := G/g
  let H := F/g
  let J := m*(σ 0 m)
  have cp := (Nat.coprime_two_left.mpr odd).pow_left k
  have bal := balance (mul_ne_zero (pow_ne_zero k (by decide : 2≠0)) odd.pos.ne') eq
  rw [multiplicative.map_mul_of_coprime cp,isMultiplicative_sigma.map_mul_of_coprime cp,
    isMultiplicative_sigma.map_mul_of_coprime cp] at bal
  have bal' : F*weighted m + G*(σ 1 m)=(F+G)*J := by
    dsimp only [F,G,J]
    rw [bal,dyadic_balance]
    ring
  have gp : 0<G := by
    dsimp only [G]
    rw [sigma_one_apply_prime_pow Nat.prime_two]
    exact sum_pos' (fun _ _ => Nat.zero_le _) ⟨0, by simp, by simp⟩
  have gpos : 0<g := Nat.gcd_pos_of_pos_left _ gp
  have cpn : Q.Coprime H := Nat.coprime_div_gcd_div_gcd gpos
  have qfac : Q*g=G := Nat.div_mul_cancel (Nat.gcd_dvd_left G F)
  have hfac : H*g=F := Nat.div_mul_cancel (Nat.gcd_dvd_right G F)
  change ∃ h : ℤ, (weighted m:ℤ)-J=h*Q ∧ (J:ℤ)-(σ 1 m:ℕ)=h*H
  refine common_multiplier (Q:=Q) (H:=H) (Int.isCoprime_iff_nat_coprime.mpr (by simpa using cpn)) ?_
  apply mul_left_cancel₀ (show (g:ℤ)≠0 by exact_mod_cast gpos.ne')
  have bint := congrArg (Nat.cast : ℕ → ℤ) bal'
  have qint := congrArg (Nat.cast : ℕ → ℤ) qfac
  have hint := congrArg (Nat.cast : ℕ → ℤ) hfac
  push_cast at bint qint hint
  linear_combination ((J:ℤ)-(σ 1 m:ℕ))*qint-((weighted m:ℤ)-J)*hint-bint

/-- Eliminate an unknown first-power prime x from the two surplus equations.
    V is the target after removing x, W and Z are the two cofactor moments. -/
theorem eliminate {x V W Z h Q H : ℤ}
    (first : W*(1+2*x)-V*x=h*Q) (second : V*x-Z*(1+x)=h*H) :
    h*((Q+H)*V-Q*Z-2*H*W)+V*(Z-W)-W*Z=0 ∧ (V-Z)*x=h*H+Z := by
  exact ⟨by linear_combination (2*W-V)*second-(V-Z)*first,by linear_combination second⟩

/-- At a solution with first-power odd prime x, its cofactor moments alone
    satisfy the eliminant. Substitution M=P*y^d gives the polynomial in y. -/
theorem cofactor_eliminant (k M x : ℕ) (om : Odd M) (ox : Odd x) (hx : x.Prime)
    (cop : M.Coprime x) (eq : OeisA245212.a (2^k*(M*x)) = (σ 1 (2^k*(M*x)):ℤ)) :
    let G := σ 1 (2^k)
    let F := weighted (2^k)
    let Q : ℤ := (G/(G.gcd F):ℕ)
    let H : ℤ := (F/(G.gcd F):ℕ)
    let V : ℤ := 2*(M:ℤ)*((σ 0 M:ℕ):ℤ)
    let W : ℤ := weighted M
    let Z : ℤ := σ 1 M
    ∃ h : ℤ, h*((Q+H)*V-Q*Z-2*H*W)+V*(Z-W)-W*Z=0 ∧
      (V-Z)*x=h*H+Z := by
  dsimp only
  obtain ⟨h,hw,hs⟩ := surpluses k (M*x) (om.mul ox) eq
  have wp : weighted x=1+2*x := by
    simpa [w,Finset.sum_range_succ,mul_comm] using weighted_pow hx 1
  have sp : σ 1 x = 1+x := by
    simpa [Finset.sum_range_succ] using sigma_one_apply_prime_pow hx (i:=1)
  have tp : σ 0 x = 2 := by simpa using sigma_zero_apply_prime_pow hx (i:=1)
  rw [multiplicative.map_mul_of_coprime cop,isMultiplicative_sigma.map_mul_of_coprime cop,
    wp,tp] at hw
  rw [isMultiplicative_sigma.map_mul_of_coprime cop,isMultiplicative_sigma.map_mul_of_coprime cop,
    sp,tp] at hs
  push_cast at hw hs
  refine ⟨h,eliminate ?_ ?_⟩
  · convert! hw using 1
    ring
  · convert! hs using 1
    ring

#print axioms project
#print axioms cofactor_eliminant

end OMA.TailProjection245212
