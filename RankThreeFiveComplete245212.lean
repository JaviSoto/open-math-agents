import RankThreeFiveThirty245212
import RankThreeFiveHigher245212
import FiveQuick4x31
import RankThreeEightAll245212
import RankThreeMultipleThree245212
import RankThreeFourLargeSolution245212

/-! No positive multiple of five with exactly three distinct odd prime
divisors satisfies the original OEIS A245212 equality. -/
namespace OMA.RankThreeFiveComplete245212
open Nat Finset
open scoped ArithmeticFunction.sigma

theorem vector {k a p q b c : ℕ} (kp : 0<k) (ap : 0<a) (pp : p.Prime) (qp : q.Prime)
    (gt : 5<p) (pq : p<q) (bp : 0<b) (cp : 0<c) :
    OeisA245212.a (2^k*5^a*p^b*q^c)≠(σ 1 (2^k*5^a*p^b*q^c):ℤ) := by
  have five : Nat.Prime 5 := by decide
  by_cases high : 5≤k
  · exact OMA.RankThreeFiveHigher245212.original high ap pp qp gt pq bp cp
  interval_cases k
  · exact OMA.RankThreeTwice245212.original five pp qp (by decide) gt pq ap bp cp
  · exact OMA.RankThreeFourLargeSolution245212.no_least_ge_five five pp qp le_rfl gt pq ap bp cp
  · exact OMA.RankThreeEightAll245212.original five pp qp le_rfl gt pq ap bp cp
  · intro eqn
    have cop (r : ℕ) (pr : r.Prime) (gr : 5<r) : (2^4*5^a).Coprime r :=
      (((coprime_primes prime_two pr).mpr (by omega)).pow_left 4).mul_left
        (((coprime_primes five pr).mpr (by omega)).pow_left a)
    have bounds:=OMA.RankThreeFiveTail245212.prefixes (k:=4) le_rfl ap
      (Nat.mul_pos (pow_pos pp.pos b) (pow_pos qp.pos c))
      (((cop p pp gt).pow_right b).mul_right ((cop q qp (by omega)).pow_right c))
      (by simpa only [mul_assoc] using eqn)
    by_cases low : a≤30
    · exact OMA.RankThreeFiveThirty245212.cases ap low pp qp gt pq bp cp eqn
    · have : a=31:=by omega
      subst a;exact OMA.FiveQuick4x31.original pp qp gt pq bp cp eqn

theorem odd_part {m : ℕ} (k : ℕ) (om : Odd m) (five : 5∣m) (three : ¬3∣m)
    (rank : m.primeFactors.card=3) : OeisA245212.a (2^k*m)≠(σ 1 (2^k*m):ℤ) := by
  by_cases zero : k=0
  · subst k;simp only [pow_zero,one_mul]
    intro hit
    have one:=OMA.OddSupportClass245212.odd_three om rank.le hit
    rw [one] at five;omega
  have prime5 : Nat.Prime 5:=by decide
  have mt : 5∈m.primeFactors:=Nat.mem_primeFactors.mpr ⟨prime5,five,om.pos.ne'⟩
  have rest : (m.primeFactors.erase 5).card=2:=by rw [card_erase_of_mem mt,rank]
  obtain ⟨p,q,ne,rs⟩:=card_eq_two.mp rest
  have props {p : ℕ} (mem : p∈m.primeFactors.erase 5) : p.Prime ∧ 5<p ∧ 0 < m.factorization p := by
    obtain ⟨diff,mass⟩:=mem_erase.mp mem
    have pr:=prime_of_mem_primeFactors mass
    have dv:=dvd_of_mem_primeFactors mass
    have op:=Nat.coprime_two_left.mp ((Nat.coprime_two_left.mpr om).of_dvd_right dv)
    have n3 : p≠3:=fun eq=>three (eq ▸ dv)
    obtain ⟨j,hj⟩:=op
    exact ⟨pr,by have :=pr.two_le;omega,pr.factorization_pos_of_dvd om.pos.ne' dv⟩
  obtain ⟨pp,pl,bp⟩:=props (p:=p) (by simp [rs])
  obtain ⟨qp,ql,cp⟩:=props (p:=q) (by simp [rs])
  have ap:=prime5.factorization_pos_of_dvd om.pos.ne' five
  have rep:=Nat.prod_primeFactors_pow_factorization om.pos.ne'
  rw [←mul_prod_erase _ _ mt,rs,prod_insert (by simpa using ne),prod_singleton] at rep
  have id : 2^k*m=2^k*5^(m.factorization 5)*p^(m.factorization p)*q^(m.factorization q) := by
    simpa only [mul_assoc] using congrArg (2^k*·) rep
  rw [id]
  by_cases pq : p<q
  · exact vector (by omega) ap pp qp pl pq bp cp
  · simpa only [mul_right_comm (2^k*5^(m.factorization 5))] using
      vector (by omega : 0<k) ap qp pp ql (by omega : q<p) cp bp

theorem original {n : ℕ} (pos : 0<n) (five : 5∣n) (rank : (n.primeFactors.erase 2).card=3) :
    OeisA245212.a n≠(σ 1 n:ℤ) := by
  by_cases three : 3∣n
  · exact OMA.RankThreeMultipleThree245212.original pos three rank
  let m:=ordCompl[2] n
  have odd : Odd m:=Nat.coprime_two_left.mp (Nat.coprime_ordCompl prime_two pos.ne')
  have inpart : 5∣m:=Nat.dvd_ordCompl_of_dvd_not_dvd five (by decide : ¬2∣5)
  have no3 : ¬3∣m:=fun h=>three (h.trans (Nat.ordCompl_dvd n 2))
  have r : m.primeFactors.card=3:=by rwa [show m.primeFactors=n.primeFactors.erase 2 from OMA.CofactorEffectiveTree245212.support_rest n 2]
  simpa only [m,Nat.ordProj_mul_ordCompl_eq_self] using odd_part (n.factorization 2) odd inpart no3 r

#print axioms original
end OMA.RankThreeFiveComplete245212
