import RankTwoJoined245212
import SmallOriginal245212
import Least7Pair245212
import Least11Pair245212
import FiveMovingPair245212

/-! The original A245212 equivalence on every positive integer divisible
by at most two distinct odd primes. The primes and exponents are unbounded. -/
namespace OMA.RankTwoAll245212
open Finset
open scoped ArithmeticFunction.sigma
open private OMA.DyadicPower245212.dyadic_balance from DyadicPower245212

theorem dyadic (k : ℕ) : OeisA245212.a (2^k)=(σ 1 (2^k):ℤ) :=
  OMA.Abundance245212.eq_of_balance (by positivity) (OMA.DyadicPower245212.dyadic_balance k)

theorem one {p e k : ℕ} (hp : p.Prime) (op : 3≤p) (ep : 0<e) :
    OeisA245212.a (2^k*p^e)≠(σ 1 (2^k*p^e):ℤ) := by
  intro eqn
  have nd : ¬p∣2^k := fun h => (by omega : p≠2) ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  have eq0 : OeisA245212.a (2^k*p^0)=(σ 1 (2^k*p^0):ℤ) := by simpa using dyadic k
  have := OMA.Abundance245212.unique_exponent (by positivity) hp nd eqn eq0
  omega

private theorem ordered {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (op : 3≤p) (pq : p<q) (ha : 0<a) (hd : 0<d) :
    OeisA245212.a (2^k*p^a*q^d)≠(σ 1 (2^k*p^a*q^d):ℤ) := by
  by_cases wide : 13≤p
  · by_cases small : min a d≤4
    · exact OMA.SmallOriginal245212.closed hp hq op (by omega) pq.ne ha hd small
    · exact OMA.RankTwoJoined245212.original hp hq wide pq (by omega) (by omega)
  have choice : p=3 ∨ p=5 ∨ p=7 ∨ p=11 := by interval_cases p <;> norm_num at *
  rcases choice with rfl|rfl|rfl|rfl
  · by_cases pos : 0<k
    · exact OMA.Moving245212.mixed_three pos ha hd hq pq
    · have zero : k=0 := by omega
      subst k
      have big : 5≤q := by by_contra! sm; interval_cases q; norm_num at *
      exact OMA.DyadicEuler245212.pair_small (by decide) hq (by decide) pq ha
        (u:=3) (v:=5) (by decide) (by decide) le_rfl big (by decide +kernel)
  · exact OMA.FiveMovingPair245212.no_five hq pq ha hd
  · exact OMA.Least7Pair245212.no_pair hq pq ha hd
  · exact OMA.Least11Pair245212.no_pair hq pq ha hd

theorem two {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p)
    (oq : 3≤q) (pq : p≠q) (ha : 0<a) (hd : 0<d) :
    OeisA245212.a (2^k*p^a*q^d)≠(σ 1 (2^k*p^a*q^d):ℤ) := by
  rcases lt_or_gt_of_ne pq with lt|gt
  · exact ordered hp hq op lt ha hd
  · rw [mul_right_comm (2^k)]
    exact ordered hq hp oq gt hd ha

/-- A245212 for the entire rank-at-most-two odd support. -/
theorem iff_power (n : ℕ) (hn : 0<n) (rank : (n.primeFactors.erase 2).card≤2) :
    OeisA245212.a n=(σ 1 n:ℤ) ↔ ∃ k : ℕ, n=2^k := by
  classical
  refine ⟨fun eqn => ?_, fun ⟨k,h⟩ => h ▸ dyadic k⟩
  let e:=n.factorization
  let s:=n.primeFactors.erase 2
  have fac : 2^(e 2)*(∏ p∈s,p^(e p))=n := by
    by_cases h : 2∈n.primeFactors
    · exact (mul_prod_erase n.primeFactors (fun p => p^(e p)) h).trans (Nat.prod_primeFactors_pow_factorization hn.ne').symm
    · have z : e 2=0 := Finsupp.notMem_support_iff.mp h
      simpa [z,s,erase_eq_of_notMem h,e] using (Nat.prod_primeFactors_pow_factorization hn.ne').symm
  have each {p} (h : p∈s) : p.Prime ∧ 3≤p ∧ 0<e p := by
    obtain ⟨np,mem⟩:=mem_erase.mp h
    have pr:=Nat.prime_of_mem_primeFactors mem
    exact ⟨pr,by have := pr.two_le;omega,Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp mem)⟩
  have cases' : s.card=0 ∨ s.card=1 ∨ s.card=2 := by change s.card≤2 at rank;omega
  rcases cases' with empty|single|pair
  · rw [card_eq_zero.mp empty,prod_empty,mul_one] at fac
    exact ⟨e 2,fac.symm⟩
  · obtain ⟨p,hs⟩:=card_eq_one.mp single
    obtain ⟨hp,op,ep⟩:=each (p:=p) (by simp [hs])
    rw [hs,prod_singleton] at fac
    exact False.elim (one hp op ep (fac.symm ▸ eqn))
  · obtain ⟨p,q,pq,hs⟩:=card_eq_two.mp pair
    obtain ⟨hp,op,ep⟩:=each (p:=p) (by simp [hs])
    obtain ⟨hq,oq,eq⟩:=each (p:=q) (by simp [hs])
    rw [hs,prod_insert (by simpa using pq),prod_singleton,←mul_assoc] at fac
    exact False.elim (two hp hq op oq pq ep eq (fac.symm ▸ eqn))

#print axioms iff_power
end OMA.RankTwoAll245212
