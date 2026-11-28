import CycleTerminal

/-! Coin costs for arbitrary unions of disjoint dyadic progressions. -/

open private OMA.BinaryPrefix.bounded OMA.BinaryPrefix.weight OMA.BinaryPrefix.digits
  OMA.BinaryPrefix.split_one OMA.BinaryPrefix.sum_bits from BinaryPrefix
namespace OMA.PathCoins
open Finset
abbrev Bounded := OMA.BinaryPrefix.bounded
abbrev weight := OMA.BinaryPrefix.weight

/-- Displacing a binary all-ones word costs one extra coin at most in
    a positive coordinate, and saves at least one in a negative one. -/
theorem displaced {k s t : ℕ} (hs : s<2^k) (ht : t<2^k) :
    ∃ w : List ℕ, Bounded k w ∧ weight w=2^k-1+s-t ∧
      w.length+(if s<t then 1 else 0)≤k+(if t<s then 1 else 0) := by
  rcases lt_trichotomy s t with lt|rfl|lt
  · let m := 2^k-1+s-t
    have pos : 0<2^k := by positivity
    obtain ⟨w,bnd,eq,_,strict⟩ := OMA.BinaryPrefix.digits k m (by dsimp [m]; omega)
    have len := strict (by dsimp [m]; omega)
    exact ⟨w,bnd,eq,by simp only [if_pos lt,if_neg lt.not_gt]; omega⟩
  · have pos : 0<2^k := by positivity
    obtain ⟨w,bnd,eq,le,_⟩ := OMA.BinaryPrefix.digits k (2^k-1) (by omega)
    exact ⟨w,bnd,by simpa using eq,by simpa using le⟩
  · let m := s-t-1
    have pos : 0<2^k := by positivity
    have kp : 0<k := by by_contra! no; have := Nat.eq_zero_of_le_zero no; simp_all
    obtain ⟨w,bnd,eq,_,strict⟩ := OMA.BinaryPrefix.digits k m (by dsimp [m]; omega)
    have len := strict (by dsimp [m]; omega)
    have top : k-1<k := by omega
    refine ⟨(k-1)::(k-1)::w,(by intro j hj; rcases List.mem_cons.mp hj with rfl|hj; exact top
                                 ; rcases List.mem_cons.mp hj with rfl|hj; exact top; exact bnd j hj),?_,?_⟩
    · change 2^(k-1)+(2^(k-1)+weight w)=_
      have e : 2^k=2^(k-1)*2 := by rw [←pow_succ,show k-1+1=k by omega]
      change weight w=m at eq
      dsimp [m] at eq; omega
    · simp only [List.length_cons,if_neg lt.not_gt,if_pos lt]; omega

/-- Fill to any intermediate total number of coins across all chains,
    preserving each individual coordinate exactly. -/
theorem fill {I : Type*} [Fintype I] [DecidableEq I] (L : I→ℕ) (n : ℕ)
    (w : I→List ℕ) (bnd : ∀ i,Bounded (L i) (w i))
    (little : (∑ i,(w i).length)≤n) (big : n≤∑ i,weight (w i)) :
    ∃ v : I→List ℕ, (∀ i,Bounded (L i) (v i)) ∧ (∀ i,weight (v i)=weight (w i)) ∧
      (∑ i,(v i).length)=n := by
  by_cases eq : (∑ i,(w i).length)=n
  · exact ⟨w,bnd,fun _=>rfl,eq⟩
  obtain ⟨i,_,lt⟩ := exists_lt_of_sum_lt (lt_of_lt_of_le (lt_of_le_of_ne little eq) big)
  obtain ⟨w',b',v',c'⟩ := OMA.BinaryPrefix.split_one (L i) (w i) (bnd i) lt
  let u := Function.update w i w'
  have ub (j : I) : Bounded (L j) (u j) := by
    by_cases e : j=i
    · subst j; simpa [u] using b'
    · simpa [u,e] using bnd j
  have same (j : I) : weight (u j)=weight (w j) := by
    by_cases e : j=i
    · subst j; simpa [u] using v'
    · simp [u,e]
  have count : (∑ j,(u j).length)=(∑ j,(w j).length)+1 := by
    rw [←sum_erase_add _ _ (mem_univ i),←sum_erase_add _ (fun j=>(w j).length) (mem_univ i)]
    have equal : (∑ j∈univ.erase i,(u j).length)=∑ j∈univ.erase i,(w j).length :=
      sum_congr rfl (fun j hj=>by simp [u,(mem_erase.mp hj).1])
    rw [equal]; simp only [u,Function.update_self,c']; omega
  obtain ⟨v,vb,values,vc⟩ := fill L n u ub (by omega)
    (by simpa only [same] using big)
  exact ⟨v,vb,fun j=>(values j).trans (same j),vc⟩
termination_by n-∑ i,(w i).length
decreasing_by
  change n-(∑ j,(u j).length)<n-(∑ j,(w j).length)
  rw [count]; omega

end OMA.PathCoins
