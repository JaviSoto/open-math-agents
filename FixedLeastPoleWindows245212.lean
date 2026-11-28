import FixedLeastPair245212
import RankThreePowerCut245212

/-! When the middle prime nearly cancels the prefix Euler defect, split
the last prime at the length bound. On the far side only the smaller
exponent needs a logarithmic scan. -/
namespace OMA.FixedLeastPoleWindows245212
open Nat ArithmeticFunction OMA.Smooth245212 OMA.CofactorEulerPair245212
open OMA.RankThreeFiveRound245212 OMA.RankThreeFiveShort245212 OMA.RankThreeFourSmallCompact245212
open OMA.RankThreeEightMoving245212 (line line_sound)
open OMA.FixedLeastPair245212 (wt sg ta)
open scoped ArithmeticFunction.sigma
open private OMA.CofactorEulerPair245212.checked from CofactorEulerDecision245212
open private OMA.Large245212.moments from LargeExact245212

def windows (h A S T p B C : ℕ) :=
  let Q:=max B C+1
  let R:=max (p+1) (Q+1)
  let Z:=shortCap A S p B C
  neverZero A S (2*T) p B C R &&
  every 1 (min B (max (nearDegree h A S p Q) Z)) (line A S T p (p+1)) &&
  every 1 (min C Z) (smallFar A S T p R B)

theorem windows_false {h p q b c B C : ℕ} (hh : 0<h) (pp : p.Prime) (qp : q.Prime)
    (hc : h.Coprime p) (cq : h.Coprime q) (pq : p<q) (op : 3≤p) (bp : 0<b) (cp : 0<c)
    (bb : b≤B) (cc : c≤C) (good : ¬q∣2*(h*σ 0 h))
    (ok : windows h (W h) (σ 1 h) (h*σ 0 h) p B C=true)
    (eqn : OeisA245212.a (h*p^b*q^c)=(σ 1 (h*p^b*q^c):ℤ)) : False := by
  let A:=W h;let S:=σ 1 h;let T:=h*σ 0 h
  let Q:=max B C+1;let R:=max (p+1) (Q+1);let Z:=shortCap A S p B C
  simp only [windows,Bool.and_eq_true] at ok
  have small (bound : b ≤ max (nearDegree h A S p Q) Z) : False :=
    line_sound hh pp qp (by omega) hc cq pq.ne cp pq
      (OMA.CofactorEulerPair245212.checked ok.1.2 bp (le_min bb bound)) eqn
  by_cases near : q≤Q
  · exact small (le_max_of_le_left (near_degree hh pp qp hc cq pq op bp cp near good eqn))
  have far : R≤q:=max_le pq (by omega)
  obtain ⟨lt,nz⟩:=never_zero pp bp cp bb cc ok.1.1
  have z:=short hh pp qp hc cq pq cp bb cc (lt.trans_le far) nz good eqn
  change min b c≤Z at z
  by_cases bc : b≤c
  · exact small (le_max_of_le_right (by simpa only [min_eq_left bc] using z))
  have last:=OMA.CofactorEulerPair245212.checked ok.2 cp (le_min cc (by simpa only [min_eq_right (le_of_not_ge bc)] using z))
  have limited:=OMA.RankThreeFourSmallBand245212.budget_ge hh pp qp hc cq pq bp cp bb eqn
  unfold smallFar at last
  rw [if_neg (Nat.ne_of_gt (bp.trans_le limited))] at last
  split at last
  · exact OMA.RankThreeFourSmallBand245212.band_sound hh pp qp hc cq pq bp cp far limited last eqn
  · exact OMA.RankThreeFourSmallFar245212.clipped_sound hh pp qp op hc cq pq bp cp far limited last eqn

def pole (h A S T m p : ℕ) :=
  let B:=OMA.RankThreePowerCut245212.cutoff A (2*T) p
  decide (m≤p ∧ 2*T*(p-1)<A*p) &&
    (every 1 (min B (highCap A S T p)) (line A S T p (p+1)) ||
     windows h A S T p B (nextDegree A S p B))

theorem pole_false {h p q b c m : ℕ} (hh : 0<h) (pp : p.Prime) (qp : q.Prime)
    (hc : h.Coprime p) (cq : h.Coprime q) (pq : p<q) (op : 3≤p) (bp : 0<b) (cp : 0<c)
    (factors : (2*(h*σ 0 h)).primeFactorsList.all (fun v=>decide (v ≤ m))=true)
    (ok : pole h (W h) (σ 1 h) (h*σ 0 h) m p=true)
    (eqn : OeisA245212.a (h*p^b*q^c)=(σ 1 (h*p^b*q^c):ℤ)) : False := by
  simp only [pole,Bool.and_eq_true,decide_eq_true_eq] at ok
  let B:=OMA.RankThreePowerCut245212.cutoff (W h) (2*(h*σ 0 h)) p
  have bb : b≤B:=OMA.RankThreePowerCut245212.bounded pp qp ok.1.2
    (OMA.RankThreeFourSmallBounds245212.strict pp qp (sigma_pos 1 _ hh.ne') (by simpa only [OMA.RankThreeFourSmallBounds245212.Bal,Nat.cast_mul,Nat.cast_ofNat] using normalized hh pp qp hc cq pq.ne eqn))
  have good : ¬q∣2*(h*σ 0 h):=by
    intro dvd
    have pos:=sigma_pos 0 h hh.ne'
    have mem:=Nat.mem_primeFactors_iff_mem_primeFactorsList.mp (qp.mem_primeFactors dvd (by positivity))
    exact pq.not_ge ((of_decide_eq_true (List.all_eq_true.mp factors q mem)).trans ok.1.1)
  have tests:=ok.2
  rw [Bool.or_eq_true] at tests
  rcases tests with lines|rest
  · exact line_sound hh pp qp (by omega) hc cq pq.ne cp pq
      (OMA.CofactorEulerPair245212.checked lines bp (le_min bb (high_bound hh pp qp hc cq pq op bp cp ok.1.2 good eqn))) eqn
  · exact windows_false hh pp qp hc cq pq op bp cp bb (next_le hh pp qp hc cq pq cp bb eqn) good rest eqn

def either (h A S T m p : ℕ) :=
  if OMA.KernelPrimeWindow245212.trial p && m≤p && 2*T*(p-1)<A*p && p≤2*A/(A*p-2*T*(p-1))
  then pole h A S T m p || OMA.FiveFastNear245212.fast h A S T m p
  else OMA.FiveFastNear245212.fast h A S T m p

theorem old_interval {h A S T m l u : ℕ}
    (ok : every l u (OMA.FiveFastNear245212.fast h A S T m)=true) :
    every l u (either h A S T m)=true := by
  apply List.all_eq_true.mpr;intro p mem
  have yes:=List.all_eq_true.mp ok p mem
  simp [either,yes]

theorem certify {l k a p q b c L M : ℕ} (lp : l.Prime) (odd : 2<l)
    (pp : p.Prime) (qp : q.Prime) (gt : l<p) (pq : p<q) (bp : 0<b) (cp : 0<c) (start : L≤p)
    (limit : (2*ta l k a).primeFactorsList.all (fun v=>decide (v≤M))=true)
    (tested : every L (OMA.RankThreeFourSmallHarmonic245212.primeCut (wt l k a) (sg l k a) (2*ta l k a))
      (either (2^k*l^a) (wt l k a) (sg l k a) (ta l k a) M)=true) :
    OeisA245212.a (2^k*l^a*p^b*q^c)≠(σ 1 (2^k*l^a*p^b*q^c):ℤ) := by
  have cop (r : ℕ) (pr : r.Prime) (gr : l<r) : (2^k*l^a).Coprime r :=
    (((coprime_primes prime_two pr).mpr (by omega)).pow_left k).mul_left
      (((coprime_primes lp pr).mpr (by omega)).pow_left a)
  have inner:=((coprime_primes prime_two lp).mpr (by omega)).pow_left k |>.pow_right a
  have w : W (2^k*l^a)=wt l k a:=by
    rw [w_mult.map_mul_of_coprime inner,←(OMA.Large245212.moments prime_two k).2,←(OMA.Large245212.moments lp a).2];rfl
  have s : σ 1 (2^k*l^a)=sg l k a:=by
    rw [isMultiplicative_sigma.map_mul_of_coprime inner,←(OMA.Large245212.moments prime_two k).1,←(OMA.Large245212.moments lp a).1];rfl
  have t : 2^k*l^a*σ 0 (2^k*l^a)=ta l k a:=by
    rw [isMultiplicative_sigma.map_mul_of_coprime inner,sigma_zero_apply_prime_pow prime_two,sigma_zero_apply_prime_pow lp,ta,OMA.Large245212.tax,OMA.Large245212.tax];ring
  rw [←w,←s,←t] at tested
  rw [←t] at limit
  have pos:=Nat.mul_pos (Nat.two_pow_pos k) (pow_pos lp.pos a)
  intro hit
  have cap:=OMA.RankThreeFourSmallHarmonic245212.first_prime pos pp qp (cop p pp gt) (cop q qp (by omega)) pq bp cp hit
  have ev:=OMA.CofactorEulerPair245212.checked tested start cap
  let h:=2^k*l^a
  have cases : pole h (W h) (σ 1 h) (h*σ 0 h) M p=true ∨
      OMA.FiveFastNear245212.fast h (W h) (σ 1 h) (h*σ 0 h) M p=true:=by
    unfold either at ev;split at ev
    · simpa only [Bool.or_eq_true] using ev
    · exact Or.inr ev
  rcases cases with hard|fast
  · exact pole_false pos pp qp (cop p pp gt) (cop q qp (by omega)) pq (by omega) bp cp limit hard hit
  · exact OMA.RankThreeFiveShort245212.sound pos pp qp (cop p pp gt) (cop q qp (by omega)) pq (by omega) bp cp
      (OMA.FiveFastNear245212.sound limit fast) hit

#print axioms certify
end OMA.FixedLeastPoleWindows245212
