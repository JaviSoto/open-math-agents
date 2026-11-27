import FormalConjectures.Arxiv.«2607.08366».MinModulus
import CyclicSurplus
import CyclicCount

/-! Quantitative partial result for Fonollosa's all-ones minimum-modulus
conjecture. The final theorem uses the upstream IsValidMod predicate. -/

namespace OMA.CyclicSurplus
open Finset Arxiv.«2607.08366»

theorem modulus_lower {N n : ℕ} (hn : 3≤n) (hN : 0<N) (A : Finset (ZMod N))
    (card : A.card=n) (ok : IsValidMod A) :
    9*2^(n-1)≤8*N := by
  classical
  have : NeZero N := ⟨hN.ne'⟩
  obtain ⟨p,hp⟩ := A.card_pos.mp (by omega)
  let B := A.erase p
  let g (i : B) := i.val-p
  have valid : OMA.WeightedModulus.Valid 1 (fun _ : B=>1) g := normalize_residues A p hp ok
  have bc : Fintype.card B=n-1 := by
    rw [Fintype.card_coe]
    exact (card_erase_of_mem hp).trans (by rw [card])
  obtain ⟨i,dbl⟩ := nontrivial_double g valid (by omega)
  let S := (univ : Finset B).erase i
  have sc : S.card=n-2 := by
    dsimp only [S]
    rw [card_erase_of_mem (mem_univ i),card_univ,bc]
    omega
  obtain ⟨P,D,K,holes,sub,grow,two,three,dc,cover,space⟩ := potential_sets g valid i dbl
  have low := OMA.CyclicDrift.potential_count (g i) P D K sub grow two three
  change D.card=2^S.card at dc
  change 2^S.card≤2*(K.card+holes) at cover
  rw [dc,sc,ZMod.card] at low
  rw [sc] at cover
  rw [bc,ZMod.card] at space
  have double : 2^(n-1)=2^(n-2)*2 := by
    rw [←Nat.pow_succ]
    congr 1
    omega
  rw [double] at space ⊢
  omega

end OMA.CyclicSurplus
