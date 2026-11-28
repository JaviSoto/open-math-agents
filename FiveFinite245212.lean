import FiveFaceBound245212
import FiveSquareThree245212

/-! Finiteness of the entire odd five-prime branch with exact 3-adic valuation two. -/
namespace OMA.FiveFinite245212
open Finset Nat ArithmeticFunction OMA.Smooth245212
open scoped ArithmeticFunction.sigma

def cofactorCap (k : ℕ) : ℕ := 9*5^k*7^k*11^k
def primeCap (k : ℕ) : ℕ := 10000000000+2*(cofactorCap k)^3

private theorem sum_bounds {m : ℕ} (hm : 0 < m) : W m+σ 1 m ≤ 2*m^3 := by
  have small {d : ℕ} (hd : d∈m.divisors) : d ≤ m :=
    Nat.le_of_dvd hm (Nat.dvd_of_mem_divisors hd)
  have ss : σ 1 m ≤ m*m := by
    rw [sigma_one_apply]
    calc ∑ d∈m.divisors,d ≤ ∑ _d∈m.divisors,m := sum_le_sum fun d hd => small hd
         _ = m.divisors.card*m := by simp
         _ ≤ m*m := Nat.mul_le_mul_right _ (Nat.card_divisors_le_self m)
  have ww : W m ≤ m*(m*m) := by
    rw [w_apply]
    calc ∑ d∈m.divisors,d*d.divisors.card ≤ ∑ _d∈m.divisors,m*m :=
           sum_le_sum fun d hd => Nat.mul_le_mul (small hd) ((Nat.card_divisors_le_self _).trans (small hd))
         _ = m.divisors.card*(m*m) := by simp
         _ ≤ _ := Nat.mul_le_mul_right _ (Nat.card_divisors_le_self m)
  nlinarith only [ss,ww,Nat.mul_le_mul_right (m*m) hm]

theorem sorted_bound (k : ℕ) (hk : 2000000000≤k) (p e : Fin 5 → ℕ) (pr : ∀ i,(p i).Prime) (ord : StrictMono p)
    (p0 : p 0=3) (e0 : e 0=2) (pos : ∀ i,0 < e i)
    (eqn : OeisA245212.a (total p e)=(σ 1 (total p e):ℤ)) : p 4≤primeCap k := by
  have basic : 10000000000≤primeCap k := Nat.le_add_right _ _
  by_cases hr : 10000000000≤p 4
  · obtain ⟨p1,p2,choices,lim,_,_⟩ := OMA.FiveSquareThree245212.support p e pr ord p0 e0 eqn
    have p3 : p 3=11 := by
      rcases choices with h|h|h|h
      · exact h
      all_goals have lt := lim (show 13≤p 3 by omega); omega
    let m := 9*5^(e 1)*7^(e 2)*11^(e 3)
    have value : total p e=m*(p 4)^(e 4) := by
      simp [total,Fin.prod_univ_succ,p0,p1,p2,p3,e0,m,mul_assoc]
    have balance := normalized_of_eq p pr ord.injective e eqn
    simp [normalized,Fin.prod_univ_succ,p0,p1,p2,p3,e0] at balance
    have score : (34/27:ℚ)*X 5 (some (e 1))*X 7 (some (e 2))*X 11 (some (e 3))*X (p 4) (some (e 4))+
      (13/27:ℚ)*Y 5 (some (e 1))*Y 7 (some (e 2))*Y 11 (some (e 3))*Y (p 4) (some (e 4))=2 := by
      rw [show X 3 (some 2)=34/27 by decide +kernel,show Y 3 (some 2)=13/27 by decide +kernel] at balance
      simpa only [mul_one,mul_assoc] using balance
    obtain ⟨a,b,c⟩:=OMA.FiveFace245212.prefix_exponents hr (pos 1) (pos 2) (pos 3) score
    have mb : m≤cofactorCap k :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 9
        (Nat.pow_le_pow_right (by decide : 0<5) (a.le.trans hk)))
        (Nat.pow_le_pow_right (by decide : 0<7) (b.le.trans hk)))
        (Nat.pow_le_pow_right (by decide : 0<11) (c.le.trans hk))
    have cp (i : Fin 5) (hi : i≠4) : (p i).Coprime (p 4) :=
      (Nat.coprime_primes (pr i) (pr 4)).mpr (fun h => hi (ord.injective h))
    have cop : m.Coprime (p 4) := by
      have h0 := (cp 0 (by decide)).pow_left 2
      have h1 := (cp 1 (by decide)).pow_left (e 1)
      have h2 := (cp 2 (by decide)).pow_left (e 2)
      have h3 := (cp 3 (by decide)).pow_left (e 3)
      rw [p0] at h0; rw [p1] at h1; rw [p2] at h2; rw [p3] at h3
      exact ((h0.mul_left h1).mul_left h2).mul_left h3
    have mp : 0 < m := by dsimp [m]; positivity
    have divides := OMA.OddCofactor245212.last_dvd mp (pr 4) cop (pos 4) (value ▸ eqn)
    have spos : 0<σ 1 m := by
      rw [sigma_one_apply]; exact sum_pos' (fun _ _ => Nat.zero_le _) ⟨1,Nat.one_mem_divisors.mpr mp.ne',by decide⟩
    have bound := Nat.le_of_dvd (show 0<W m+σ 1 m by omega) divides
    exact (bound.trans (sum_bounds mp)).trans ((Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left mb 3)).trans
      (Nat.le_add_left (2*(cofactorCap k)^3) 10000000000))
  · exact (Nat.le_of_lt (Nat.lt_of_not_ge hr)).trans basic

#print axioms sorted_bound

/-- Finiteness for arbitrary integers in the branch; no bound on the input or its exponents. -/
private theorem finite_with_cap (k : ℕ) (hk : 2000000000≤k) :
    {n : ℕ | Odd n ∧ n.primeFactors.card=5 ∧ n.factorization 3=2 ∧
      OeisA245212.a n=(σ 1 n:ℤ)}.Finite := by
  classical
  apply (OMA.FixedPrimes245212.finite (range (primeCap k+1))).subset
  rintro n ⟨odd,card,fac,eqn⟩
  let S := n.primeFactors
  let p := S.orderEmbOfFin card
  let e (i : Fin 5) := n.factorization (p i)
  have mem (i) : p i∈n.primeFactors := orderEmbOfFin_mem S card i
  have pr (i) := Nat.prime_of_mem_primeFactors (mem i)
  have contains {q : ℕ} (hq : q∈n.primeFactors) : q∈Set.range p := by
    rw [show Set.range p=(S:Set ℕ) from range_orderEmbOfFin S card]; exact hq
  have three : 3∈n.primeFactors := Finsupp.mem_support_iff.mpr (show n.factorization 3≠0 by rw [fac]; decide)
  obtain ⟨i,hi⟩ := contains three
  have p0 : p 0=3 := by
    have low := (pr 0).two_le
    have up := p.monotone (Fin.zero_le i)
    have dv := Nat.dvd_of_mem_primeFactors (mem 0)
    have not2 : p 0≠2 := fun h => (Nat.not_even_iff_odd.mpr odd) (even_iff_two_dvd.mpr (h ▸ dv))
    omega
  have pos (j) : 0<e j := (pr j).factorization_pos_of_dvd odd.pos.ne' (Nat.dvd_of_mem_primeFactors (mem j))
  have repr : total p e=n := by
    unfold total e
    exact (Fintype.prod_equiv (S.orderIsoOfFin card).toEquiv _
      (fun j : S => j.val^(n.factorization j.val)) (fun _ => rfl)).trans
      (Nat.prod_primeFactors_coe_pow_factorization odd.pos.ne').symm
  have top := sorted_bound k hk p e pr p.strictMono p0
    (by change n.factorization (p 0)=2; rw [p0,fac]) pos (by rw [repr]; exact eqn)
  refine ⟨odd.pos,?_,eqn,?_⟩
  · intro q hq
    obtain ⟨j,rfl⟩ := contains hq
    have last : p j≤p 4 := p.monotone (Fin.le_last j)
    exact mem_range.mpr (Nat.lt_succ_of_le (last.trans top))
  · rintro ⟨j,hj⟩
    have dv := Nat.dvd_of_mem_primeFactors three
    rw [hj] at dv
    exact (by decide : ¬3∣2) ((by decide : Nat.Prime 3).dvd_of_dvd_pow dv)

theorem finite_square_three :
    {n : ℕ | Odd n ∧ n.primeFactors.card=5 ∧ n.factorization 3=2 ∧
      OeisA245212.a n=(σ 1 n:ℤ)}.Finite := finite_with_cap 2000000000 (le_refl _)

#print axioms finite_square_three
end OMA.FiveFinite245212
