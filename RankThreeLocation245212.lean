import RankThreeThirtyTwo245212
import RankThreeSevenHigh245212

/-! Locate the remaining possible exceptions with three distinct odd primes
in the original OEIS A245212 equation. -/
namespace OMA.RankThreeLocation245212
open Nat Finset
open scoped ArithmeticFunction.sigma

theorem original {n : ℕ} (pos : 0<n) (rank : (n.primeFactors.erase 2).card=3)
    (hit : OeisA245212.a n=(σ 1 n:ℤ)) :
    32∣n ∧ ¬3∣n ∧ ¬5∣n ∧ (7∣n → n.factorization 2=5 ∨ n.factorization 2=6) := by
  obtain ⟨dy,no3,no5⟩:=OMA.RankThreeThirtyTwo245212.original pos rank hit
  refine ⟨dy,no3,no5,?_⟩
  intro seven
  let k:=n.factorization 2
  let m:=ordCompl[2] n
  have rp : m.primeFactors=n.primeFactors.erase 2:=OMA.CofactorEffectiveTree245212.support_rest n 2
  have odd : Odd m:=Nat.coprime_two_left.mp (Nat.coprime_ordCompl prime_two pos.ne')
  have d7 : 7∣m:=Nat.dvd_ordCompl_of_dvd_not_dvd seven (by decide : ¬2∣7)
  have pr7 : Nat.Prime 7:=by decide
  have mt : 7∈m.primeFactors:=Nat.mem_primeFactors.mpr ⟨pr7,d7,odd.pos.ne'⟩
  have rk : m.primeFactors.card=3:=rp ▸ rank
  have rest : (m.primeFactors.erase 7).card=2:=by rw [card_erase_of_mem mt,rk]
  obtain ⟨p,q,ne,rs⟩:=card_eq_two.mp rest
  have props {p : ℕ} (mem : p∈m.primeFactors.erase 7) : p.Prime ∧ 7<p ∧ 0 < m.factorization p := by
    obtain ⟨diff,mass⟩:=mem_erase.mp mem
    have pr:=prime_of_mem_primeFactors mass
    have dv:=dvd_of_mem_primeFactors mass
    have nd:=dv.trans (Nat.ordCompl_dvd n 2)
    have od:=Nat.coprime_two_left.mp ((Nat.coprime_two_left.mpr odd).of_dvd_right dv)
    obtain ⟨j,hj⟩:=od
    have n3 : p≠3:=fun e=>no3 (e ▸ nd)
    have n5 : p≠5:=fun e=>no5 (e ▸ nd)
    have pl := pr.two_le
    exact ⟨pr,by omega,pr.factorization_pos_of_dvd odd.pos.ne' dv⟩
  obtain ⟨pp,pl,bp⟩:=props (p:=p) (by simp [rs])
  obtain ⟨qp,ql,cp⟩:=props (p:=q) (by simp [rs])
  have ap:=pr7.factorization_pos_of_dvd odd.pos.ne' d7
  have rep:=Nat.prod_primeFactors_pow_factorization odd.pos.ne'
  rw [←mul_prod_erase _ _ mt,rs,prod_insert (by simpa using ne),prod_singleton] at rep
  have id : n=2^k*7^(m.factorization 7)*p^(m.factorization p)*q^(m.factorization q):=by
    calc
      n=2^k*m:=(Nat.ordProj_mul_ordCompl_eq_self n 2).symm
      _=_:=by simpa only [mul_assoc] using congrArg (2^k*·) rep
  have lower : 5≤k:=(prime_two.pow_dvd_iff_le_factorization pos.ne').mp dy
  change k=5 ∨ k=6
  by_contra! neither
  have hi : 7≤k:=by omega
  rw [id] at hit
  by_cases order : p<q
  · exact OMA.RankThreeSevenHigh245212.original hi ap pp qp pl order bp cp hit
  · have rev:=OMA.RankThreeSevenHigh245212.original hi ap qp pp ql (by omega : q<p) cp bp
    exact rev (by simpa only [mul_right_comm (2^k*7^(m.factorization 7))] using hit)

#print axioms original
end OMA.RankThreeLocation245212
