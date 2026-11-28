import Mathlib

/-! Finite averaging on the lower neighbors of a Boolean cube. -/

namespace OMA.CubeCharge
open Finset

/-- Sharing unit mass over every available receiver bounds the source
    count whenever the incoming degree is bounded by each sender's
    outgoing degree times c. -/
theorem distribute {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (T : Finset β) (nb : α→Finset β) (c : ℕ)
    (maps : ∀ i∈S,nb i⊆T) (non : ∀ i∈S,(nb i).Nonempty)
    (bound : ∀ j∈T,∀ i∈S,j∈nb i → (S.filter (fun a=>j∈nb a)).card≤c*(nb i).card) :
    S.card≤c*T.card := by
  classical
  let w (i : α) (j : β) : ℚ := if j∈nb i then 1 / ((nb i).card:ℚ) else 0
  have row (i) (hi : i∈S) : (∑ j∈T,w i j)=1 := by
    have e : T.filter (fun j=>j∈nb i)=nb i := by
      ext j; simp only [mem_filter]; exact ⟨And.right,fun h=>⟨maps i hi h,h⟩⟩
    simp only [w,←sum_filter,e,sum_const,nsmul_eq_mul]
    have pos : 0<((nb i).card:ℚ) := by exact_mod_cast card_pos.mpr (non i hi)
    field_simp
  have col (j) (hj : j∈T) : (∑ i∈S,w i j)≤c := by
    let D := S.filter (fun a=>j∈nb a)
    change (∑ i∈S,if j∈nb i then 1/((nb i).card:ℚ) else 0)≤_
    rw [←sum_filter]
    change (∑ i∈D,1/((nb i).card:ℚ))≤_
    by_cases emp : D.Nonempty
    · have dp : 0<(D.card:ℚ) := by exact_mod_cast card_pos.mpr emp
      calc (∑ i∈D,1/((nb i).card:ℚ)) ≤ ∑ _∈D,(c:ℚ)/D.card := by
             apply sum_le_sum; intro i hi
             obtain ⟨si,ji⟩ := mem_filter.mp hi
             have ip : 0<((nb i).card:ℚ) := by exact_mod_cast card_pos.mpr (non i si)
             apply (div_le_div_iff₀ ip dp).mpr
             rw [one_mul]; exact_mod_cast bound j hj i si ji
           _ = c := by simp only [sum_const,nsmul_eq_mul]; field_simp
    · simp [not_nonempty_iff_eq_empty.mp emp]
  have chk := sum_le_sum col
  rw [sum_comm] at chk
  simp only [sum_congr rfl row,sum_const,nsmul_eq_mul,mul_one] at chk
  exact_mod_cast (by simpa [mul_comm] using chk : (S.card:ℚ)≤c*T.card)

/-- Total downward rank movement of a partial injection is charged to
    its missing range and to its moves of gain one. -/
theorem rank_budget {α : Type*} [DecidableEq α] (X : Finset α)
    (D : Finset (Finset α)) (f : Finset α→Finset α) (sub : D⊆X.powerset)
    (inj : Set.InjOn f D) (maps : ∀ S∈D,f S⊆X)
    (gain : ∀ S∈D,(f S).card≤S.card+1) :
    (D.filter (fun S=>(f S).card<S.card)).card ≤
      (D.filter (fun S=>S.card<(f S).card)).card+X.card*(X.powerset.card-D.card) := by
  classical
  let Q := X.powerset
  let miss := Q\D.image f
  have fi : D.image f⊆Q := by
    intro s h; obtain ⟨i,hi,rfl⟩ := mem_image.mp h
    exact mem_powerset.mpr (maps i hi)
  have sum1 := sum_sdiff fi (f:=Finset.card)
  rw [sum_image inj] at sum1
  have dom : (∑ d∈D,d.card)≤∑ d∈Q,d.card := sum_le_sum_of_subset sub
  have rem : (∑ d∈miss,d.card)≤X.card*(Q.card-D.card) := by
    calc (∑ d∈miss,d.card) ≤ ∑ _∈miss,X.card := by
          apply sum_le_sum; intro d hd; exact card_le_card (mem_powerset.mp (mem_sdiff.mp hd).1)
         _ = X.card*(Q.card-D.card) := by
          rw [sum_const,smul_eq_mul,mul_comm]
          dsimp [miss]; rw [card_sdiff_of_subset fi,card_image_of_injOn inj]
  have pt (s) (hs : s∈D) : (f s).card+(if (f s).card<s.card then 1 else 0) ≤
      s.card+(if s.card<(f s).card then 1 else 0) := by
    have := gain s hs; split_ifs <;> omega
  have len := sum_le_sum pt
  simp only [sum_add_distrib,←card_filter] at len
  change (∑ d∈miss,d.card)+(∑ d∈D,(f d).card)=∑ d∈Q,d.card at sum1
  change _≤_+X.card*(Q.card-D.card)
  omega

end OMA.CubeCharge
