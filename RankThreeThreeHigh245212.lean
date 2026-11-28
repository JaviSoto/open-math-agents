import RankThreeTailRows245212

/-! No rank-three solution can have 8 dividing the input and 3 dividing
its odd part. No bound on either of the other odd primes or any exponent. -/
namespace OMA.RankThreeThreeHigh245212
open Nat OMA.RankThreeThreeTail245212 OMA.RankThreeTailRows245212
open scoped ArithmeticFunction.sigma

theorem original {k p q a b d : ℕ} (kl : 3≤k) (hp : p.Prime) (hq : q.Prime)
    (lo : 5≤p) (pq : p<q) (ap : 0<a) (bp : 0<b) (dp : 0<d) :
    OeisA245212.a (2^k*3^a*p^b*q^d)≠(σ 1 (2^k*3^a*p^b*q^d):ℤ) := by
  intro eqn
  have cop (r : ℕ) (pr : r.Prime) (lr : 5≤r) : (2^k*3^a).Coprime r :=
    (((coprime_primes prime_two pr).mpr (by omega)).pow_left k).mul_left
      (((coprime_primes prime_three pr).mpr (by omega)).pow_left a)
  have cp:=cop p hp lo
  have cq:=cop q hq (by omega)
  have bounds:=prefixes kl ap (Nat.mul_pos (pow_pos hp.pos b) (pow_pos hq.pos d))
    ((cp.pow_right b).mul_right (cq.pow_right d)) (by simpa only [mul_assoc] using eqn)
  apply certified (by positivity) hp hq lo pq bp dp cp cq _ eqn
  rcases bounds with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact c24
  · exact c72
  · exact c48
  · exact c96

#print axioms original
end OMA.RankThreeThreeHigh245212
