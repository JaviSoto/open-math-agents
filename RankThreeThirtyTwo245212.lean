import RankThreeFiveComplete245212
import RankThreeSixteenLarge245212

/-! On the actual OEIS input, any rank-three exception must be a
multiple of 32 and have no factor 3 or 5. -/
namespace OMA.RankThreeThirtyTwo245212
open Nat Finset
open scoped ArithmeticFunction.sigma

theorem low {k m : ℕ} (small : k≤4) (odd : Odd m) (rank : m.primeFactors.card=3)
    (least7 : ∀p∈m.primeFactors,7≤p) :
    OeisA245212.a (2^k*m)≠(σ 1 (2^k*m):ℤ) := by
  by_cases zero : k=0
  · subst k;simp only [pow_zero,one_mul];intro hit
    have one:=OMA.OddSupportClass245212.odd_three odd rank.le hit
    simp [one] at rank
  let P : Fin 3 ↪o ℕ := m.primeFactors.orderEmbOfFin rank
  let e (i : Fin 3):=m.factorization (P i)
  have mem (i : Fin 3) : P i∈m.primeFactors:=m.primeFactors.orderEmbOfFin_mem rank i
  have prime (i) := prime_of_mem_primeFactors (mem i)
  have ep (i) : 0<e i := (prime i).factorization_pos_of_dvd odd.pos.ne' (dvd_of_mem_primeFactors (mem i))
  have first:=least7 (P 0) (mem 0)
  have pq:=P.strictMono (by decide : (0:Fin 3)<1)
  have qr:=P.strictMono (by decide : (1:Fin 3)<2)
  have prod:=Nat.prod_primeFactors_pow_factorization odd.pos.ne'
  have lift : Finset.univ.map P.toEmbedding=m.primeFactors:=m.primeFactors.map_orderEmbOfFin_univ rank
  rw [←lift,prod_map,Fin.prod_univ_three] at prod
  change m=(P 0)^(e 0)*(P 1)^(e 1)*(P 2)^(e 2) at prod
  have repr : 2^k*m=2^k*(P 0)^(e 0)*(P 1)^(e 1)*(P 2)^(e 2):=by
    simpa only [mul_assoc] using congrArg (2^k*·) prod
  rw [repr]
  have kp : 1≤k:=by omega
  interval_cases k
  · exact OMA.RankThreeTwice245212.original (prime 0) (prime 1) (prime 2) (by omega) pq qr (ep 0) (ep 1) (ep 2)
  · exact OMA.RankThreeFourLargeSolution245212.no_least_ge_five (prime 0) (prime 1) (prime 2) (by omega) pq qr (ep 0) (ep 1) (ep 2)
  · exact OMA.RankThreeEightAll245212.original (prime 0) (prime 1) (prime 2) (by omega) pq qr (ep 0) (ep 1) (ep 2)
  · exact OMA.RankThreeSixteenLarge245212.vector (prime 0) (prime 1) (prime 2) first pq qr (ep 0) (ep 1) (ep 2)

theorem original {n : ℕ} (pos : 0<n) (rank : (n.primeFactors.erase 2).card=3)
    (hit : OeisA245212.a n=(σ 1 n:ℤ)) : 32∣n ∧ ¬3∣n ∧ ¬5∣n := by
  have no3 : ¬3∣n:=fun h=>OMA.RankThreeMultipleThree245212.original pos h rank hit
  have no5 : ¬5∣n:=fun h=>OMA.RankThreeFiveComplete245212.original pos h rank hit
  refine ⟨?_,no3,no5⟩
  let m:=ordCompl[2] n
  have odd:=Nat.coprime_two_left.mp (Nat.coprime_ordCompl prime_two pos.ne')
  have supp : m.primeFactors=n.primeFactors.erase 2:=OMA.CofactorEffectiveTree245212.support_rest n 2
  have bound : ∀p∈m.primeFactors,7≤p:=by
    intro p mp
    have pr:=prime_of_mem_primeFactors mp
    have dv:=dvd_of_mem_primeFactors mp
    have nd:=dv.trans (Nat.ordCompl_dvd n 2)
    have od:=Nat.coprime_two_left.mp ((Nat.coprime_two_left.mpr odd).of_dvd_right dv)
    obtain ⟨u,hu⟩:=od
    have n3 : p≠3:=fun e=>no3 (e ▸ nd)
    have n5 : p≠5:=fun e=>no5 (e ▸ nd)
    have :=pr.two_le;omega
  apply (prime_two.pow_dvd_iff_le_factorization pos.ne').2 (show 5≤n.factorization 2 from ?_)
  by_contra! small
  have no:=low (by omega : n.factorization 2≤4) odd (supp ▸ rank) bound
  exact no (by simpa only [m,Nat.ordProj_mul_ordCompl_eq_self] using hit)

#print axioms original
end OMA.RankThreeThirtyTwo245212
