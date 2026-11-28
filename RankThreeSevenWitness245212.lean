import RankThreeLocation245212
import RankThreeThirtyTwoLarge245212

/-! Any three-odd-prime exception is divisible by 64. If it contains seven,
then the exponent of two is six, and its other factors are ordered primes
greater than seven. This supplies the original input for prefix certificates. -/
namespace OMA.RankThreeSevenWitness245212
open Nat Finset
open scoped ArithmeticFunction.sigma

theorem location {n : ℕ} (pos : 0<n) (rank : (n.primeFactors.erase 2).card=3)
    (hit : OeisA245212.a n=(σ 1 n:ℤ)) :
    64∣n ∧ ¬3∣n ∧ ¬5∣n ∧ (7∣n → n.factorization 2=6) := by
  obtain ⟨dy,no3,no5,sev⟩:=OMA.RankThreeLocation245212.original pos rank hit
  have least (p) (mem : p∈n.primeFactors.erase 2) : 7≤p:=by
    obtain ⟨ne,mp⟩:=mem_erase.mp mem
    have pr:=prime_of_mem_primeFactors mp
    have dvd:=dvd_of_mem_primeFactors mp
    have n3 : p≠3:=fun e=>no3 (e ▸ dvd)
    have n5 : p≠5:=fun e=>no5 (e ▸ dvd)
    have lb:=pr.two_le
    obtain ⟨j,hj⟩:=pr.odd_of_ne_two ne
    omega
  have ne : n.factorization 2≠5:=fun five=>OMA.RankThreeThirtyTwoLarge245212.original pos five rank least hit
  have lb : 5≤n.factorization 2:=(prime_two.pow_dvd_iff_le_factorization pos.ne').mp dy
  exact ⟨(prime_two.pow_dvd_iff_le_factorization pos.ne').mpr (by omega : 6≤n.factorization 2),
    no3,no5,fun seven=>(sev seven).resolve_left ne⟩

theorem witness {n : ℕ} (pos : 0<n) (rank : (n.primeFactors.erase 2).card=3)
    (hit : OeisA245212.a n=(σ 1 n:ℤ)) (seven : 7∣n) :
    ∃p q b c : ℕ,p.Prime ∧ q.Prime ∧ 7<p ∧ p<q ∧ 0<b ∧ 0<c ∧
      n=2^6*7^(n.factorization 7)*p^b*q^c := by
  obtain ⟨_,no3,no5,dy⟩:=location pos rank hit
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
  have dy6 : k=6:=dy seven
  have a7 : m.factorization 7=n.factorization 7:=by
    dsimp only [m];rw [Nat.factorization_ordCompl,Finsupp.erase_ne (by decide : 7≠2)]
  rw [dy6,a7] at id
  by_cases lt : p<q
  · exact ⟨p,q,_,_,pp,qp,pl,lt,bp,cp,id⟩
  · exact ⟨q,p,_,_,qp,pp,ql,by omega,cp,bp,id.trans (mul_right_comm ..)⟩

#print axioms location
#print axioms witness
end OMA.RankThreeSevenWitness245212
