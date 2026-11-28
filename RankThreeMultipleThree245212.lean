import RankThreeTwice245212
import RankThreeThreeHigh245212
import RankThreeFourSmallSolution245212
import OddThreeSolution245212
import CofactorEffectiveTree245212

/-! No solution with three distinct odd prime divisors can be a multiple
of three, even when the exponent of two is completely unrestricted. -/
namespace OMA.RankThreeMultipleThree245212
open Nat Finset
open scoped ArithmeticFunction.sigma

theorem vector (k : ℕ) {p q a b d : ℕ} (hp : p.Prime) (hq : q.Prime)
    (lo : 5≤p) (pq : p<q) (ap : 0<a) (bp : 0<b) (dp : 0<d) :
    OeisA245212.a (2^k*3^a*p^b*q^d)≠(σ 1 (2^k*3^a*p^b*q^d):ℤ) := by
  by_cases high : 3≤k
  · exact OMA.RankThreeThreeHigh245212.original high hp hq lo pq ap bp dp
  interval_cases k
  · simp only [pow_zero,one_mul]
    intro eqn
    have op:=hp.odd_of_ne_two (by omega)
    have oq:=hq.odd_of_ne_two (by omega)
    have three : Odd (3:ℕ):=by decide
    have odd : Odd (3^a*p^b*q^d):=(three.pow.mul op.pow).mul oq.pow
    have card : (3^a*p^b*q^d).primeFactors.card≤3 := by
      rw [primeFactors_mul (mul_ne_zero (by positivity) (pow_ne_zero _ hp.ne_zero)) (pow_ne_zero _ hq.ne_zero),
        primeFactors_mul (by positivity) (pow_ne_zero _ hp.ne_zero),
        primeFactors_prime_pow ap.ne' prime_three,primeFactors_prime_pow bp.ne' hp,primeFactors_prime_pow dp.ne' hq]
      have ne : (3:ℕ)≠p:=by omega
      have nz : (3:ℕ)≠q:=by omega
      simp [ne,nz,pq.ne]
    have one:=OMA.OddSupportClass245212.odd_three odd card eqn
    have dv : 3∣3^a*p^b*q^d := dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_pow_self _ ap.ne') _) _
    rw [one] at dv
    omega
  · exact OMA.RankThreeTwice245212.original prime_three hp hq le_rfl (by omega) pq ap bp dp
  · exact OMA.RankThreeFourSmallSolution245212.no_least_three hp hq lo pq ap bp dp

theorem odd_part {m : ℕ} (k : ℕ) (om : Odd m) (three : 3∣m) (rank : m.primeFactors.card=3) :
    OeisA245212.a (2^k*m)≠(σ 1 (2^k*m):ℤ) := by
  have mt : 3∈m.primeFactors:=Nat.mem_primeFactors.mpr ⟨prime_three,three,om.pos.ne'⟩
  have rest : (m.primeFactors.erase 3).card=2 := by rw [card_erase_of_mem mt,rank]
  obtain ⟨p,q,ne,rs⟩:=card_eq_two.mp rest
  have props {p : ℕ} (mem : p∈m.primeFactors.erase 3) : p.Prime ∧ 5≤p ∧ 0 < m.factorization p := by
    obtain ⟨diff,mass⟩:=mem_erase.mp mem
    have pr:=prime_of_mem_primeFactors mass
    have dv:=dvd_of_mem_primeFactors mass
    have op:=Nat.coprime_two_left.mp ((Nat.coprime_two_left.mpr om).of_dvd_right dv)
    refine ⟨pr,?_,pr.factorization_pos_of_dvd om.pos.ne' dv⟩
    obtain ⟨j,hj⟩:=op
    have :=pr.two_le
    omega
  obtain ⟨hp,pl,bp⟩:=props (p:=p) (by simp [rs])
  obtain ⟨hq,ql,dp⟩:=props (p:=q) (by simp [rs])
  have ap:=prime_three.factorization_pos_of_dvd om.pos.ne' three
  have rep:=Nat.prod_primeFactors_pow_factorization om.pos.ne'
  rw [←mul_prod_erase _ _ mt,rs,prod_insert (by simpa using ne),prod_singleton] at rep
  have id : 2^k*m=2^k*3^(m.factorization 3)*p^(m.factorization p)*q^(m.factorization q) := by
    calc
      _ = 2^k*(3^(m.factorization 3)*(p^(m.factorization p)*q^(m.factorization q))) := congrArg (2^k*·) rep
      _ = _ := by ring
  rw [id]
  by_cases pq : p<q
  · exact vector k hp hq pl pq ap bp dp
  · have qp : q<p:=by omega
    simpa only [mul_right_comm (2^k*3^(m.factorization 3))] using
      vector k hq hp ql qp ap dp bp

theorem original {n : ℕ} (hn : 0 < n) (three : 3∣n) (rank : (n.primeFactors.erase 2).card=3) :
    OeisA245212.a n≠(σ 1 n:ℤ) := by
  let m:=ordCompl[2] n
  have odd : Odd m:=Nat.coprime_two_left.mp (Nat.coprime_ordCompl prime_two hn.ne')
  have t : 3∣m:=Nat.dvd_ordCompl_of_dvd_not_dvd three (by decide : ¬2∣3)
  have r : m.primeFactors.card=3:=by rwa [show m.primeFactors=n.primeFactors.erase 2 from OMA.CofactorEffectiveTree245212.support_rest n 2]
  simpa only [m,Nat.ordProj_mul_ordCompl_eq_self] using odd_part (n.factorization 2) odd t r

#print axioms original
end OMA.RankThreeMultipleThree245212
