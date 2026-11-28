import CofactorEulerSeparation245212
import CofactorEffectiveOriginal245212

/-! A cofactor has at most one resonant Euler support, even without a rank
cutoff. The largest prime in the reduced numerator identifies the next factor. -/
namespace OMA.EulerSupportUnique245212
open Finset Nat ArithmeticFunction OMA.Smooth245212 OMA.CofactorEulerSeparation245212
open scoped ArithmeticFunction.sigma

private theorem forced {s t : Finset ℕ} {p : ℕ} (ps : ∀x∈s,x.Prime) (pt : ∀x∈t,x.Prime)
    (mem : p∈s) (hi : ∀x∈s,x≤p) (cross : num s*den t=num t*den s) : p∈t := by
  have pp:=ps p mem
  have dv : p∣num t*den s := cross ▸ dvd_mul_of_dvd_left (dvd_prod_of_mem (fun q=>q) mem) _
  rcases pp.dvd_mul.mp dv with a|b
  · obtain ⟨x,mx,px⟩:=(pp.prime.dvd_finsetProd_iff (fun q=>q)).mp a
    rwa [(prime_dvd_prime_iff_eq pp (pt x mx)).mp px]
  · obtain ⟨x,mx,px⟩:=(pp.prime.dvd_finsetProd_iff (fun q=>q-1)).mp b
    have :=(ps x mx).one_lt
    have :=Nat.le_of_dvd (by omega : 0<x-1) px
    have :=hi x mx
    omega

theorem unique_support (s t : Finset ℕ) (ps : ∀x∈s,x.Prime) (pt : ∀x∈t,x.Prime)
    (cross : num s*den t=num t*den s) : s=t := by
  induction s using Finset.strongInductionOn generalizing t with
  | _ s ih =>
    by_cases empty : s∪t=∅
    · have := Finset.union_eq_empty.mp empty
      exact this.1.trans this.2.symm
    have ne:=nonempty_iff_ne_empty.mpr empty
    let p:=(s∪t).max' ne
    have mp : p∈s∪t:=(s∪t).max'_mem ne
    have ls (x) (mx:x∈s) : x≤p := (s∪t).le_max' x (mem_union_left _ mx)
    have lt (x) (mx:x∈t) : x≤p := (s∪t).le_max' x (mem_union_right _ mx)
    have both : p∈s ∧ p∈t := by
      rcases mem_union.mp mp with a|b
      · exact ⟨a,forced ps pt a ls cross⟩
      · exact ⟨forced pt ps b lt cross.symm,b⟩
    have cut : num (s.erase p)*den (t.erase p)=num (t.erase p)*den (s.erase p) := by
      have ns : num s=p*num (s.erase p) := (mul_prod_erase s (fun q=>q) both.1).symm
      have nt : num t=p*num (t.erase p) := (mul_prod_erase t (fun q=>q) both.2).symm
      have ds : den s=(p-1)*den (s.erase p) := (mul_prod_erase s (fun q=>q-1) both.1).symm
      have dt : den t=(p-1)*den (t.erase p) := (mul_prod_erase t (fun q=>q-1) both.2).symm
      have pr:=(ps p both.1).one_lt
      apply Nat.eq_of_mul_eq_mul_left (show 0<p*(p-1) by exact mul_pos (by omega) (by omega))
      rw [ns,nt,ds,dt] at cross
      simpa only [mul_assoc,mul_left_comm,mul_comm] using cross
    have equal:=ih (s.erase p) (erase_ssubset both.1) (t.erase p)
      (fun _ mem=>ps _ (mem_of_mem_erase mem)) (fun _ mem=>pt _ (mem_of_mem_erase mem)) cut
    simpa only [insert_erase both.1,insert_erase both.2] using congrArg (insert p) equal

theorem only_one {A H : ℕ} (ap : 0<A) {s t : Finset ℕ} (ps : ∀x∈s,x.Prime) (pt : ∀x∈t,x.Prime)
    (hs : A*num s=H*den s) (ht : A*num t=H*den t) : s=t := by
  apply unique_support s t ps pt
  apply Nat.eq_of_mul_eq_mul_left ap
  rw [←mul_assoc,hs,←mul_assoc,ht]
  ring

theorem cofactor_divides {h : ℕ} {s : Finset ℕ} (cop : ∀p∈s,h.Coprime p)
    (hit : W h*num s=2*(h*σ 0 h)*den s) : h∣W h := by
  have cp : h.Coprime (num s) := coprime_prod_right_iff.mpr cop
  apply cp.dvd_of_dvd_mul_right
  rw [hit]
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) _

#print axioms unique_support
#print axioms cofactor_divides
end OMA.EulerSupportUnique245212
