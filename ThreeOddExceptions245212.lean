import ThreeOddRankBundle245212
import RankTwoAll245212

/-! Combining the absolute rank-three height with the independently proved
rank-two classification. Dyadic solutions themselves form an infinite family. -/
namespace OMA.ThreeOddExceptions245212
open scoped ArithmeticFunction.sigma

theorem bounded {n : ℕ} (pos : 0<n) (rank : (n.primeFactors.erase 2).card≤3)
    (eqn : OeisA245212.a n=(σ 1 n:ℤ)) (other : ¬∃k:ℕ,n=2^k) :
    n≤OMA.ThreeOddAbsolute245212.cutoff := by
  by_cases few : (n.primeFactors.erase 2).card≤2
  · exact False.elim (other ((OMA.RankTwoAll245212.iff_power n pos few).mp eqn))
  · exact OMA.ThreeOddAbsolute245212.original pos (by omega) eqn

theorem finite : {n : ℕ | 0<n ∧ (n.primeFactors.erase 2).card≤3 ∧
    OeisA245212.a n=(σ 1 n:ℤ) ∧ ¬∃k:ℕ,n=2^k}.Finite :=
  (Set.finite_Iic OMA.ThreeOddAbsolute245212.cutoff).subset (fun _ h=>bounded h.1 h.2.1 h.2.2.1 h.2.2.2)

theorem eventually_iff : ∀ n>OMA.ThreeOddAbsolute245212.cutoff, (n.primeFactors.erase 2).card≤3 →
    (OeisA245212.a n=(σ 1 n:ℤ) ↔ ∃k:ℕ,n=2^k) := by
  intro n large rank
  constructor
  · intro eqn
    by_contra no
    exact (not_le_of_gt large) (bounded ((Nat.zero_le _).trans_lt large) rank eqn no)
  · rintro ⟨k,rfl⟩
    exact OMA.RankTwoAll245212.dyadic k

end OMA.ThreeOddExceptions245212
