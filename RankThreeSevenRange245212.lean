import RankThreeSevenWitness245212
import FixedLeast7K6A1
import FixedLeast7K6A2
import FixedLeast7K6A3
import FixedLeast7K6A4
import FixedLeast7K6A5
import FixedLeast7K6A6
import FixedLeast7K6A7
import FixedLeast7K6A8
import FixedLeast7K6A9
import FixedLeast7K6A10
import FixedLeast7K6A11
import FixedLeast7K6A12
import FixedLeast7K6A13
import FixedLeast7K6A14
import FixedLeast7K6A15
import FixedLeast7K6A16
import FixedLeast7K6A17
import FixedLeast7K6A18
import FixedLeast7K6A19
import FixedLeast7K6A20
import FixedLeast7K6A21
import FixedLeast7K6A22
import FixedLeast7K6A23
import FixedLeast7K6A24
import FixedLeast7K6A25
import FixedLeast7K6A26
import FixedLeast7K6A27
import FixedLeast7K6A28
import FixedLeast7K6A29
import FixedLeast7K6A30
import FixedLeast7K6A31
import FixedLeast7K6A32
import FixedLeast7K6A33
import FixedLeast7K6A34
import FixedLeast7K6A35
import FixedLeast7K6A36
import FixedLeast7K6A37
import FixedLeast7K6A38
import FixedLeast7K6A39
import FixedLeast7K6A40
import FixedLeast7K6A41
import FixedLeast7K6A42
import FixedLeast7K6A43
import FixedLeast7K6A44
import FixedLeast7K6A45
import FixedLeast7K6A46
import FixedLeast7K6A47
import FixedLeast7K6A48
import FixedLeast7K6A49
import FixedLeast7K6A50
import FixedLeast7K6A51
import FixedLeast7K6A52
import FixedLeast7K6A53
import FixedLeast7K6A54
import FixedLeast7K6A55
import FixedLeast7K6A56
import FixedLeast7K6A57
import FixedLeast7K6A58
import FixedLeast7K6A59
import FixedLeast7K6A60
import FixedLeast7K6A61
import FixedLeast7K6A62
import FixedLeast7K6A63
import FixedLeast7K6A64

/-! Remaining multiplicities of seven on the original rank-three input. -/
namespace OMA.RankThreeSevenRange245212
open Nat OMA.Smooth245212
open scoped ArithmeticFunction.sigma

theorem bounds {a p q b c : ℕ} (ap : 0<a) (pp : p.Prime) (qp : q.Prime)
    (gt : 7<p) (pq : p<q) (bp : 0<b) (cp : 0<c)
    (hit : OeisA245212.a (2^6*7^a*p^b*q^c)=(σ 1 (2^6*7^a*p^b*q^c):ℤ)) :
    65≤a ∧ a≤127 := by
  constructor
  · by_contra! smaller
    interval_cases a
    · exact OMA.FixedLeast7K6A1.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A2.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A3.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A4.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A5.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A6.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A7.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A8.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A9.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A10.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A11.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A12.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A13.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A14.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A15.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A16.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A17.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A18.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A19.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A20.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A21.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A22.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A23.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A24.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A25.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A26.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A27.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A28.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A29.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A30.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A31.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A32.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A33.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A34.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A35.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A36.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A37.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A38.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A39.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A40.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A41.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A42.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A43.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A44.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A45.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A46.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A47.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A48.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A49.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A50.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A51.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A52.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A53.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A54.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A55.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A56.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A57.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A58.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A59.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A60.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A61.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A62.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A63.original pp qp gt pq bp cp hit
    · exact OMA.FixedLeast7K6A64.original pp qp gt pq bp cp hit
  · by_contra! larger
    have cop (u : ℕ) (pr : u.Prime) (large : 7<u) : (2^6*7^a).Coprime u :=
      (((coprime_primes prime_two pr).mpr (by omega)).pow_left 6).mul_left
        (((coprime_primes (by decide : Nat.Prime 7) pr).mpr (by omega)).pow_left a)
    have veto:=OMA.FixedLeastPair245212.veto (by decide : Nat.Prime 7) (by decide)
      (Nat.mul_pos (pow_pos pp.pos b) (pow_pos qp.pos c))
      (((cop p pp gt).pow_right b).mul_right ((cop q qp (by omega)).pow_right c))
      (by simpa only [mul_assoc] using hit) (show 6≤6 by decide) (show 128≤a by omega)
    exact veto.not_ge (by decide +kernel)

theorem original {n : ℕ} (pos : 0<n) (rank : (n.primeFactors.erase 2).card=3)
    (hit : OeisA245212.a n=(σ 1 n:ℤ)) :
    64∣n ∧ ¬3∣n ∧ ¬5∣n ∧
      (7∣n → n.factorization 2=6 ∧ 65≤n.factorization 7 ∧ n.factorization 7≤127) := by
  obtain ⟨dy,no3,no5,dy6⟩:=OMA.RankThreeSevenWitness245212.location pos rank hit
  refine ⟨dy,no3,no5,?_⟩;intro seven
  obtain ⟨p,q,b,c,pp,qp,gt,pq,bp,cp,rep⟩:=OMA.RankThreeSevenWitness245212.witness pos rank hit seven
  have ap:=(by decide : Nat.Prime 7).factorization_pos_of_dvd pos.ne' seven
  have lifted:=congrArg (fun t:ℕ=>OeisA245212.a t=(σ 1 t:ℤ)) rep
  exact ⟨dy6 seven,bounds ap pp qp gt pq bp cp (lifted.mp hit)⟩

#print axioms original
end OMA.RankThreeSevenRange245212
