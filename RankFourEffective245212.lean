import SinglePrefixEffective245212
import CofactorEffectiveTree245212
import TwoFreeEffectiveUniform245212

/-! A computable height for the entire integer with four distinct odd primes
and fixed two-adic order. Neither the formula nor its proof enumerates
cofactors up to the height. -/
namespace OMA.RankFourEffective245212
open Finset Nat ArithmeticFunction OMA.Smooth245212 OMA.CofactorEffectiveOriginal245212
open OMA.CofactorEffectiveAtom245212 OMA.CofactorEulerSeparation245212
open scoped ArithmeticFunction.sigma
open private OMA.PairHeight245212.count_le OMA.PairHeight245212.moment_bound from PairHeight245212

/-- Bounds a prefix after attaching one of the controlled whole prime powers. -/
def step (B r : ℕ) :=
  let C:=2*B^3+1
  let E:=threshold C C r
  B*(max (E+1) (r*C*(C+1))+1)^E

def bound (k : ℕ) := OMA.TwoFreeEffectiveUniform245212.envelope (step (step (2^k) 4) 3)

private theorem bud_mono {A C : ℕ} (le : A≤C) (r : ℕ) : budget A r≤budget C r := by
  induction r with
  | zero=>rfl
  | succ r ih=>simp only [budget];gcongr

private theorem step_le {h B r p a : ℕ} (hh : 0 < h) (hb : h≤B)
    (pb : p≤primeHeight h r) (eb : a≤height h r) : h*p^a ≤ step B r := by
  let C:=2*B^3+1
  have bp:=hh.trans_le hb
  have m:=(OMA.PairHeight245212.moment_bound hh).trans (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hb 3))
  have wc : W h≤C:=by dsimp [C];omega
  have sc : σ 1 h≤C:=by dsimp [C];omega
  have H : 2*(h*σ 0 h)≤C := by
    have d : σ 0 h≤B:=by rw [sigma_zero_apply];exact (OMA.PairHeight245212.count_le h).trans hb
    have b:=Nat.pow_le_pow_right bp (by decide : 2≤3)
    have prod:=Nat.mul_le_mul hb d
    dsimp [C];nlinarith only [b,prod]
  have ec : height h r ≤ threshold C C r := by
    unfold height threshold
    gcongr
    exact bud_mono wc r
  have pc : primeHeight h r ≤ max (threshold C C r+1) (r*C*(C+1)) := by
    apply max_le_max (Nat.succ_le_succ ec)
    exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ H) (Nat.succ_le_succ sc))
  exact Nat.mul_le_mul hb ((Nat.pow_le_pow_left ((pb.trans pc).trans (Nat.le_succ _)) _).trans
    (Nat.pow_le_pow_right (Nat.succ_pos _) (eb.trans ec)))

private theorem peel {h m r B p : ℕ} (hp : 0 < h) (hb : h≤B) (odd : Odd m)
    (cop : h.Coprime m) (mp : p∈m.primeFactors) (card : m.primeFactors.card=r+1)
    (pb : p≤primeHeight h (r+1)) (eb : m.factorization p≤height h (r+1)) :
    let g:=h*p^(m.factorization p)
    let t:=ordCompl[p] m
    0 < g ∧ g ≤ step B (r+1) ∧ Odd t ∧ g.Coprime t ∧ t.primeFactors.card=r ∧ g*t=h*m := by
  have pr:=prime_of_mem_primeFactors mp
  have dvd:=Nat.ordCompl_dvd m p
  exact ⟨mul_pos hp (pow_pos pr.pos _),step_le hp hb pb eb,
    Nat.coprime_two_left.mp ((Nat.coprime_two_left.mpr odd).of_dvd_right dvd),
    (cop.of_dvd_right dvd).mul_left ((Nat.coprime_ordCompl pr odd.pos.ne').pow_left _),
    by rw [OMA.CofactorEffectiveTree245212.support_rest m p,card_erase_of_mem mp,card];omega,
    by rw [mul_assoc,Nat.ordProj_mul_ordCompl_eq_self]⟩

private theorem large {m : ℕ} (pos : 0 < m) (many : 0 < m.primeFactors.card) : 1 < m := by
  by_contra! low
  have one : m=1:=by omega
  simp [one] at many

theorem two_atoms {k m r : ℕ} (odd : Odd m) (rank : m.primeFactors.card=r+2)
    (eqn : OeisA245212.a (2^k*m)=(σ 1 (2^k*m):ℤ)) :
    ∃g v, 0 < g ∧ g ≤ step (step (2^k) (r+2)) (r+1) ∧ Odd v ∧
      g.Coprime v ∧ v.primeFactors.card=r ∧ g*v=2^k*m := by
  obtain ⟨p,mp,pb,pe⟩:=dyadic (large odd.pos (by omega)) odd eqn
  rw [rank] at pb pe
  let a:=m.factorization p
  let h:=2^k*p^a
  let u:=ordCompl[p] m
  obtain ⟨hh,hb,ou,hc,ur,id⟩:=peel (Nat.two_pow_pos k) le_rfl odd
    ((Nat.coprime_two_left.mpr odd).pow_left k) mp (r:=r+1) rank pb pe
  have pr:=prime_of_mem_primeFactors mp
  have op:=Nat.coprime_two_left.mp ((Nat.coprime_two_left.mpr odd).of_dvd_right (dvd_of_mem_primeFactors mp))
  have ap:=pr.factorization_pos_of_dvd odd.pos.ne' (dvd_of_mem_primeFactors mp)
  have eq1 : OeisA245212.a (h*u)=(σ 1 (h*u):ℤ):=id ▸ eqn
  obtain ⟨q,mq,qb,qe⟩:=OMA.SinglePrefixEffective245212.next_atom pr op ap
    (large ou.pos (by omega)) hc eq1
  rw [ur] at qb qe
  let g:=h*q^u.factorization q
  let v:=ordCompl[q] u
  obtain ⟨gp,gb,ov,gc,vr,join⟩:=peel hh hb ou hc mq (r:=r) ur qb qe
  exact ⟨g,v,gp,gb,ov,gc,vr,join.trans id⟩

theorem original {k m : ℕ} (odd : Odd m) (rank : m.primeFactors.card=4)
    (eqn : OeisA245212.a (2^k*m)=(σ 1 (2^k*m):ℤ)) : 2^k*m ≤ bound k := by
  obtain ⟨g,v,gp,gb,ov,gc,vr,same⟩:=two_atoms (r:=2) odd rank eqn
  have last:=OMA.TwoFreeEffectiveUniform245212.of_rank gp gb ov gc vr.le (same ▸ eqn)
  rwa [same] at last

#print axioms original
end OMA.RankFourEffective245212
