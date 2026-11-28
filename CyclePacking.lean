import AffineDoublingClass

/-! A complete doubling cycle represents every element of its subgroup in
    exactly r coins, and every nonzero element in r−1. -/

open private OMA.AffineDoubling.replace from AffineDoubling
open private OMA.BinaryPrefix.digits OMA.BinaryPrefix.bounded OMA.BinaryPrefix.weight from BinaryPrefix
namespace OMA.CyclePacking
open Finset Arxiv.«2607.08366»

private lemma grow {G : Type*} [AddCommGroup G] (C : Finset G)
    (pred : ∀ a∈C,∃ b∈C,2 • b=a) (s : Multiset G) (inside : ∀ a∈s,a∈C)
    (non : s≠0) (l : ℕ) (le : s.card≤l) :
    ∃ w : Multiset G, (∀ a∈w,a∈C) ∧ w.card=l ∧ w.sum=s.sum := by
  classical
  induction l,le using Nat.le_induction with
  | base => exact ⟨s,inside,rfl,rfl⟩
  | succ l le ih =>
    obtain ⟨w,ins,sz,sm⟩ := ih
    have pos := Multiset.card_pos.mpr non
    obtain ⟨a,ha⟩ := Multiset.card_pos_iff_exists_mem.mp (by omega : 0<w.card)
    obtain ⟨v,ev⟩ := Multiset.exists_cons_of_mem ha
    obtain ⟨b,bc,ba⟩ := pred a (ins a ha)
    refine ⟨b ::ₘ b ::ₘ v,?_,?_,?_⟩
    · intro z hz
      simp only [Multiset.mem_cons] at hz
      rcases hz with e|e|h
      · exact e ▸ bc
      · exact e ▸ bc
      · exact ins z (by rw [ev]; simp [h])
    · simpa [ev] using congrArg Nat.succ sz
    · rw [←sm,ev,Multiset.sum_cons,Multiset.sum_cons,Multiset.sum_cons,←ba,two_nsmul,add_assoc]

/-- Uniform coverage by the cycle, including all larger word lengths. -/
theorem represents {N r : ℕ} [NeZero N] (hr : 0<r) (y : ZMod N)
    (ord : addOrderOf y=2^r-1) (z : ZMod N) (hz : z∈AddSubgroup.zmultiples y)
    (l : ℕ) (le : r≤l ∨ (z≠0 ∧ r≤l+1)) :
    let C := (range r).image (fun j=>2^j • y)
    ∃ s : Multiset (ZMod N),(∀ a∈s,a∈C) ∧ s.card=l ∧ s.sum=z := by
  classical
  let v (j : ℕ) := 2^j • y
  let C := (range r).image v
  have wrap : v r=v 0 := by
    apply nsmul_eq_nsmul_iff_modEq.mpr
    simp only [pow_zero,ord]
    exact ((Nat.modEq_iff_dvd' (Nat.one_le_two_pow (n:=r))).mpr (dvd_refl _)).symm
  have step (j : ℕ) : 2 • v j=v (j+1) := by simp only [v,pow_succ',mul_smul]
  have pred (a : ZMod N) (ha : a∈C) : ∃ b∈C,2 • b=a := by
    obtain ⟨j,hj,rfl⟩ := mem_image.mp ha
    cases j with
    | zero =>
      exact ⟨v (r-1),mem_image_of_mem _ (mem_range.mpr (by omega)),by
        rw [step,show r-1+1=r by omega,wrap]⟩
    | succ j => exact ⟨v j,mem_image_of_mem _ (mem_range.mpr (by have := mem_range.mp hj; omega)),step j⟩
  have vsum : ∀ L : List ℕ,(L.map v).sum=OMA.BinaryPrefix.weight L • y := by
    intro L
    induction L with
    | nil => simp [OMA.BinaryPrefix.weight]
    | cons i L ih =>
      simpa only [List.map_cons,List.sum_cons,OMA.BinaryPrefix.weight,add_nsmul] using
        congrArg (fun x=>v i+x) ih
  by_cases zero : z=0
  · have ln := le.resolve_right (fun h=>h.1 zero)
    let s := (range r).val.map v
    have sz : s.card=r := by simp [s]
    have sm : s.sum=0 := by
      have eq := addOrderOf_nsmul_eq_zero y
      rw [ord,←OMA.DyadicDigits.value_range r] at eq
      change (∑ j∈range r,2^j • y)=0
      change (∑ j∈range r,2^j) • y=0 at eq
      simpa only [Finset.sum_smul] using eq
    obtain ⟨w,ins,c,same⟩ := grow C pred s (by
      intro a ha; obtain ⟨j,hj,rfl⟩ := Multiset.mem_map.mp ha; exact mem_image_of_mem _ hj)
      (by intro e; rw [e,Multiset.card_zero] at sz; omega) l (sz ▸ ln)
    exact ⟨w,ins,c,same.trans (sm.trans zero.symm)⟩
  obtain ⟨k,kr,ek⟩ := mem_image.mp (mem_zmultiples_iff_mem_range_addOrderOf.mp hz)
  have os := mem_range.mp kr
  rw [ord] at os
  have pp : 0<2^r := by positivity
  obtain ⟨L,bL,wt,_,tight⟩ := OMA.BinaryPrefix.digits r k (by omega)
  let s : Multiset (ZMod N) := ((L.map v : List _) : Multiset _)
  have sm : s.sum=z := (vsum L).trans (by rw [wt,ek])
  have sz : s.card=L.length := List.length_map ..
  have short := tight (by omega)
  obtain ⟨w,ins,c,e⟩ := grow C pred s (by
    intro a ha
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ha
    exact mem_image_of_mem _ (mem_range.mpr (bL _ hj)))
    (by intro e; rw [e,Multiset.sum_zero] at sm; exact zero sm.symm) l (by rcases le with h|h <;> omega)
  exact ⟨w,ins,c,e.trans sm⟩

/-- Outside words of no greater length cannot represent the same coset as
    an outside squarefree mask. One extra letter still cannot do so unless
    the two actual sums agree, since the cycle fills every nonzero deficit
    using one fewer letter. -/
theorem absorb {N : ℕ} [NeZero N] {A C : Finset (ZMod N)} (ok : IsValidMod A)
    (sub : C⊆A) (sc : (∑ a∈C,a)=0) (rc : 0<C.card)
    (T : Finset (ZMod N)) (out : T⊆A\C) (m : Multiset (ZMod N))
    (outside : ∀ x∈m,x∈A\C)
    (fill : ∀ l : ℕ,C.card≤l ∨ ((∑ a∈T,a)≠m.sum ∧ C.card≤l+1) →
      ∃ w : Multiset (ZMod N),(∀ a∈w,a∈C) ∧ w.card=l ∧ w.sum=(∑ a∈T,a)-m.sum)
    (budget : m.card≤T.card ∨ ((∑ a∈T,a)≠m.sum ∧ m.card≤T.card+1)) : m=T.val := by
  classical
  let l := C.card+T.card-m.card
  have good : C.card≤l ∨ ((∑ a∈T,a)≠m.sum ∧ C.card≤l+1) := by
    dsimp [l]; rcases budget with h|h
    · exact .inl (by omega)
    · exact .inr ⟨h.1,by omega⟩
  have count : l+m.card=C.card+T.card := by dsimp [l]; rcases budget with h|h <;> omega
  obtain ⟨w,wi,wc,ws⟩ := fill l good
  have dis : Disjoint C T := disjoint_left.mpr (fun x hx tx=>(mem_sdiff.mp (out tx)).2 hx)
  have z := OMA.AffineDoubling.replace ok (C∪T) (union_subset sub (out.trans sdiff_subset)) (w+m)
    (fun x hx=>(Multiset.mem_add.mp hx).elim (fun h=>sub (wi x h))
      (fun h=>(mem_sdiff.mp (outside x h)).1))
    (by rw [Multiset.card_add,wc,count,card_union_of_disjoint dis])
    (by rw [Multiset.sum_add,ws,sub_add_cancel,sum_union dis,sc,zero_add])
  have eq : (C∪T).val=C.val+T.val := by rw [←disjUnion_val C T dis,disjUnion_eq_union]
  rw [eq] at z
  have e := congrArg (Multiset.filter (fun a=>a∉C)) z
  have fc : C.val.filter (fun x=>x∉C)=0 := Multiset.filter_eq_nil.mpr (fun _ hx h=>h hx)
  have fw : w.filter (fun x=>x∉C)=0 := Multiset.filter_eq_nil.mpr (fun _ hx h=>h (wi _ hx))
  have ft : T.val.filter (fun x=>x∉C)=T.val := Multiset.filter_eq_self.mpr (fun _ hx=>(mem_sdiff.mp (out hx)).2)
  have fm : m.filter (fun x=>x∉C)=m := Multiset.filter_eq_self.mpr (fun _ hx=>(mem_sdiff.mp (outside _ hx)).2)
  simpa only [Multiset.filter_add,fc,fw,ft,fm,zero_add] using e

end OMA.CyclePacking
