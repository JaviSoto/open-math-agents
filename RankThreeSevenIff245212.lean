import RankThreeSevenRange245212
import RankThreeSixtyFourLarge245212

/-! For any rank-three exception, seven divides the input precisely when
the dyadic valuation is six. Its 7-adic valuation is then severely restricted. -/
namespace OMA.RankThreeSevenIff245212
open Nat Finset
open scoped ArithmeticFunction.sigma

theorem original {n : ℕ} (pos : 0<n) (rank : (n.primeFactors.erase 2).card=3)
    (hit : OeisA245212.a n=(σ 1 n:ℤ)) :
    64∣n ∧ ¬3∣n ∧ ¬5∣n ∧ (7∣n ↔ n.factorization 2=6) ∧
    (7∣n → 65≤n.factorization 7 ∧ n.factorization 7≤127) := by
  obtain ⟨dy,no3,no5,seven⟩:=OMA.RankThreeSevenRange245212.original pos rank hit
  refine ⟨dy,no3,no5,⟨fun h=>(seven h).1,?_⟩,fun h=>(seven h).2⟩
  intro six
  by_contra no7
  apply OMA.RankThreeSixtyFourLarge245212.original pos six rank _ hit
  intro p mem
  obtain ⟨ne,mp⟩:=mem_erase.mp mem
  have pr:=prime_of_mem_primeFactors mp
  have dvd:=dvd_of_mem_primeFactors mp
  have n3 : p≠3:=fun e=>no3 (e ▸ dvd)
  have n5 : p≠5:=fun e=>no5 (e ▸ dvd)
  have n7 : p≠7:=fun e=>no7 (e ▸ dvd)
  have n9 : p≠9:=by rintro rfl;exact (by decide : ¬Nat.Prime 9) pr
  have pl:=pr.two_le;obtain ⟨j,hj⟩:=pr.odd_of_ne_two ne
  omega

#print axioms original
end OMA.RankThreeSevenIff245212
