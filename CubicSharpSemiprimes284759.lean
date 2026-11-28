import CubicSmallSemiprimes284759
import CubicMediumPrimeFilter284759
import MediumCubicRows284759
import SharpCubicRows284759
import LeastCubicWitness284759

/-! An exhaustive classification of semiprimes with least prime factor at most 157.
The complementary prime is unrestricted, including when both factors coincide. -/
namespace OMA.CubicSharpSemiprimes284759
open Nat Finset OMA.MediumCubicRows284759 OMA.SharpCubicRows284759

theorem classify {p q:ℕ} (pp:p.Prime) (qp:q.Prime) (ord:p≤q) (small:p≤157) :
    (p*q)^3∣∑i∈Icc 1 (p*q-1),i^(p*q-2) ↔ p=157 ∧ q=1569473 := by
  constructor
  · intro hit
    by_cases tiny:p<101
    · exact False.elim (OMA.CubicSmallSemiprimes284759.excluded pp qp ord tiny hit)
    have on:=((OMA.CubicBernoulliAll284759.original_all (Nat.mul_pos pp.pos qp.pos)).mp hit).1
    have options:=OMA.CubicMediumPrimeFilter284759.options on pp (by omega) small (dvd_mul_right p q) hit
    have bound (lt:p<q) : q∣(bernoulli (p-3)).num.natAbs :=
      OMA.CubicCofactorBound284759.bound qp lt (by omega) (Nat.odd_mul.mp on).1
        (by simpa only [mul_comm q p] using hit)
    rcases options with ⟨rfl,idx⟩|⟨rfl,idx⟩|⟨rfl,idx⟩|⟨rfl,idx⟩|⟨rfl,idx⟩
    · have lt:101<q:=by
        by_contra! le
        have eq:q=101:=by omega
        rw [eq] at idx
        norm_num at idx
      have dv:=bound lt
      rw [show (101:ℕ)-3=98 by decide,numerator98] at dv
      rcases factors98 qp dv with rfl|rfl|rfl|rfl|rfl|rfl <;> revert idx <;> decide +kernel
    · have lt:103<q:=by
        by_contra! le
        have eq:q=103:=by omega
        rw [eq] at idx
        norm_num at idx
      have dv:=bound lt
      rw [show (103:ℕ)-3=100 by decide,numerator100] at dv
      rcases factors100 qp dv with rfl|rfl|rfl|rfl|rfl <;> revert idx <;> decide +kernel
    · have lt:131<q:=by
        by_contra! le
        have eq:q=131:=by omega
        rw [eq] at idx
        norm_num at idx
      have dv:=bound lt
      rw [show (131:ℕ)-3=128 by decide,numerator128] at dv
      rcases factors128 qp dv with rfl|rfl|rfl|rfl|rfl|rfl <;> revert idx <;> decide +kernel
    · have lt:149<q:=by
        by_contra! le
        have eq:q=149:=by omega
        rw [eq] at idx
        norm_num at idx
      have dv:=bound lt
      rw [show (149:ℕ)-3=146 by decide,numerator146] at dv
      rcases factors146 qp dv with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> revert idx <;> decide +kernel
    · have lt:157<q:=by
        by_contra! le
        have eq:q=157:=by omega
        rw [eq] at idx
        norm_num at idx
      have dv:=bound lt
      rw [show (157:ℕ)-3=154 by decide,numerator154] at dv
      rcases factors154 qp dv with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> revert idx <;> decide +kernel
  · rintro ⟨rfl,rfl⟩
    exact OMA.LeastCubicWitness284759.witness.2

#print axioms classify
end OMA.CubicSharpSemiprimes284759
