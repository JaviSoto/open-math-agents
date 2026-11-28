import TerminalPrimeInverse245212
import RankThreeAnchor245212

/-! Two prime powers cannot have the same normalized weighted moment
unless their prime bases and exponents both coincide. -/
namespace OMA.PrimeMomentSignature245212
open Nat Finset ArithmeticFunction OMA.Smooth245212
open scoped ArithmeticFunction.sigma
open private OMA.RankThreeAnchor245212.weight_unit from RankThreeAnchor245212

private theorem unitSigma {p : ℕ} (pr : p.Prime) (e : ℕ) : p.Coprime (σ 1 (p^e)) := by
  have modw : σ 1 (p^e) ≡ 1 [MOD p] := by
    rw [sigma_one_apply_prime_pow pr]
    induction e with
    | zero=>simp [Nat.ModEq]
    | succ j ih=>
      rw [sum_range_succ]
      have zero : p^(j+1) ≡ 0 [MOD p]:=Nat.modEq_zero_iff_dvd.mpr (dvd_pow_self p (by omega : j+1≠0))
      simpa only [add_zero] using ih.add zero
  apply pr.coprime_iff_not_dvd.mpr
  intro dv
  have eq0:=Nat.modEq_zero_iff_dvd.mpr dv
  have one:=Nat.modEq_zero_iff_dvd.mp (modw.symm.trans eq0)
  exact pr.not_dvd_one one

/-- This needs no formula for the numerators: being coprime to the
corresponding base suffices to force the two primes to coincide. -/
theorem base {p q e f A B : ℕ} (pp : p.Prime) (qp : q.Prime) (ep : 0<e) (fp : 0<f)
    (ca : p.Coprime A) (cb : q.Coprime B) (eqn : A*((f+1)*q^f)=B*((e+1)*p^e)) : p=q := by
  by_contra ne
  have forced {p q a b U V : ℕ} (cop : p.Coprime q) (cu : p.Coprime U)
      (cross : U*((b+1)*q^b)=V*((a+1)*p^a)) : p^a≤b+1 := by
    have dv : p^a∣U*((b+1)*q^b):=by rw [cross];exact dvd_mul_of_dvd_right (dvd_mul_left ..) _
    have rem:=(cu.pow_left a).dvd_of_dvd_mul_left dv
    exact Nat.le_of_dvd (by omega) (((cop.pow_left a).pow_right b).dvd_of_dvd_mul_right rem)
  have cp:=(coprime_primes pp qp).mpr ne
  have aa:=forced cp ca eqn
  have bb:=forced cp.symm cb eqn.symm
  have bp:=Nat.pow_le_pow_left pp.two_le e
  have bq:=Nat.pow_le_pow_left qp.two_le f
  have eg:=Nat.lt_two_pow_self (n:=e)
  have fg:=Nat.lt_two_pow_self (n:=f)
  by_cases big : 2<p
  · have hl:=Nat.pow_lt_pow_left big ep.ne';omega
  · have bigq : 2<q:=by have :=qp.two_le;have :=pp.two_le;omega
    have hl:=Nat.pow_lt_pow_left bigq fp.ne';omega

theorem injective {p q e f : ℕ} (pp : p.Prime) (qp : q.Prime) (ep : 0<e) (fp : 0<f)
    (same : X p (some e)=X q (some f)) : p=q ∧ e=f := by
  have l:=x_factor pp e
  have r:=x_factor qp f
  rw [same] at l
  have cross : (W (p^e):ℚ)*(((f:ℚ)+1)*(q:ℚ)^f)=(W (q^f):ℚ)*(((e:ℚ)+1)*(p:ℚ)^e):=by
    rw [←l,←r];ring
  have pq:=base pp qp ep fp (OMA.RankThreeAnchor245212.weight_unit pp e)
    (OMA.RankThreeAnchor245212.weight_unit qp f) (by exact_mod_cast cross)
  subst q
  refine ⟨rfl,(OMA.Abundance245212.y_strict pp.one_lt).injective ?_⟩
  have nz : (p:ℚ)-1≠0:=by
    have h : (1:ℚ)<p:=by exact_mod_cast pp.one_lt
    linarith
  dsimp only [X] at same
  field_simp [nz] at same
  linarith only [same]

theorem ordinary {p q e f : ℕ} (pp : p.Prime) (qp : q.Prime) (ep : 0<e) (fp : 0<f)
    (same : Y p (some e)=Y q (some f)) : p=q ∧ e=f := by
  have l:=y_factor pp e
  have r:=y_factor qp f
  rw [same] at l
  have cross : (σ 1 (p^e):ℚ)*(((f:ℚ)+1)*(q:ℚ)^f)=(σ 1 (q^f):ℚ)*(((e:ℚ)+1)*(p:ℚ)^e):=by
    rw [←l,←r];ring
  have pq:=base pp qp ep fp (unitSigma pp e) (unitSigma qp f) (by exact_mod_cast cross)
  subst q
  exact ⟨rfl,(OMA.Abundance245212.y_strict pp.one_lt).injective same⟩

#print axioms injective
#print axioms ordinary
end OMA.PrimeMomentSignature245212
