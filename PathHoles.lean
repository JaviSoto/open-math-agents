import PathShift

/-! The translates of a small coordinate box force a missing long
    path endpoint to occur among the full box's subset sums. -/

open private OMA.PathBox.low_size from PathBox
namespace OMA.PathHoles
open OMA.PathCoins OMA.PathBox OMA.PathShift Finset Arxiv.«2607.08366»

abbrev Tiny {I : Type*} (L : I→ℕ) := (i : I)→Fin (width (L i))
def lin {I G : Type*} [Fintype I] [AddCommMonoid G] (x : I→G) (a : I→ℕ) := ∑ i,a i • x i

private lemma compare {I : Type*} [Fintype I] [DecidableEq I] {N : ℕ}
    (L : I→ℕ) (x : I→ZMod N) (inj : Function.Injective (label L x)) (ok : IsValidMod (univ.image (label L x)))
    (s : Tiny L) (a : Box L) (endpt : I→Bool) (nz : ∀ i,endpt i=true → 0<L i)
    (coins : (∑ i,if endpt i then 2 else 0 : ℕ)≤∑ i,if (a i).val<(s i).val then 2 else 0)
    (enough : (∑ i,L i)≤∑ i,(full (L i)+(s i).val-(a i).val+(if endpt i then 2^(L i) else 0)))
    (hit : lin x (fun i=>(s i).val)+lin x (fun i=>if endpt i then 2^(L i) else 0)=lin x (fun i=>(a i).val)) :
    ∀ i,(s i).val+(if endpt i then 2^(L i) else 0)=(a i).val := by
  choose v vb vs vc using (fun i=>row _ _ (a i).val (s i).isLt (endpt i) (nz i))
  have count := sum_le_sum (s:=univ) (fun i _=>vc i)
  simp only [sum_add_distrib,gt_iff_lt] at count
  have low : (∑ i,(v i).length)≤∑ i,L i := by omega
  have hi : (∑ i,L i)≤∑ i,weight (v i) := by simpa only [vs] using enough
  have le (i) : (a i).val≤full (L i) := by have h := (a i).isLt; dsimp [full]; omega
  have eq (i) : weight (v i)+(a i).val=full (L i)+(s i).val+(if endpt i then 2^(L i) else 0) := by
    have := le i; rw [vs]; omega
  have mass : (∑ i,weight (v i) • x i)=∑ i,full (L i) • x i := by
    apply add_right_cancel (b:=lin x (fun i=>(a i).val))
    change _+(∑ i,(a i).val • x i)=_+_
    conv_lhs => rw [←sum_add_distrib]
    simp only [←add_nsmul,eq]
    simp only [add_nsmul,sum_add_distrib,add_assoc]
    dsimp only [lin] at hit ⊢; rw [hit]
  have same := rigid L x inj ok v vb low hi mass
  intro i
  have h := eq i; rw [same i] at h; omega

theorem tiny_injective {I : Type*} [Fintype I] [DecidableEq I] {N : ℕ}
    (L : I→ℕ) (x : I→ZMod N) (inj : Function.Injective (label L x)) (ok : IsValidMod (univ.image (label L x))) :
    Function.Injective (fun s : Tiny L=>lin x (fun i=>(s i).val)) := by
  intro s t hit
  let a : Box L := fun i=>⟨(t i).val,(t i).isLt.trans_le (shrunk _)⟩
  have same := compare L x inj ok s a (fun _=>false) (by simp)
    (by simp) (by
      apply sum_le_sum; intro i _
      have := slack (L i) (t i).val (t i).isLt
      change L i≤full (L i)+(s i).val-(t i).val+0
      omega)
    (by simpa [lin,a] using hit)
  funext i; exact Fin.ext (by simpa [a] using same i)

theorem represented {I : Type*} [Fintype I] [DecidableEq I] {N : ℕ} [NeZero N]
    (L : I→ℕ) (x : I→ZMod N) (inj : Function.Injective (label L x)) (ok : IsValidMod (univ.image (label L x)))
    (J : I) (pos : 0<L J) (large : (∑ i,L i)≤2^L J) (small : N<2^(∑ i,L i))
    (enough : ((∑ i,L i)+Fintype.card I-1).choose (Fintype.card I) < Fintype.card (Tiny L)) :
    ∃ a : Box L,lin x (fun i=>(a i).val)=2^L J • x J := by
  classical
  let w := 2^L J • x J
  let eval (a : Box L) := lin x (fun i=>(a i).val)
  let B := univ.image eval
  let K := ((∑ i,L i)+Fintype.card I-1).choose (Fintype.card I)
  have np : 0<∑ i,L i := pos.trans_le (single_le_sum (f:=L) (fun _ _=>Nat.zero_le _) (mem_univ J))
  let high (a : Box L) := (∑ i,L i)≤∑ i,(a i).val
  let hi := univ.filter high
  have hi_le : hi.card≤B.card := by
    have h := card_le_card (image_subset_image (filter_subset high univ) (f:=eval))
    have ii : Set.InjOn eval (hi : Set _) := (injective_high L x inj ok).mono (fun a ha=>(mem_filter.mp ha).2)
    rwa [card_image_of_injOn ii] at h
  have lo := OMA.PathBox.low_size L np
  have hv := card_filter_add_card_filter_not (s:=(univ : Finset (Box L))) high
  have vol : Fintype.card (Box L)=2^(∑ i,L i) := by rw [Fintype.card_pi]; simp [prod_pow_eq_pow_sum]
  rw [card_univ,vol] at hv
  change hi.card+_=_ at hv
  change ((univ : Finset (Box L)).filter (fun a=>¬high a)).card≤K at lo
  have hc := card_sdiff_add_card_eq_card (subset_univ B)
  rw [card_univ,ZMod.card] at hc
  by_contra! miss
  let shift (s : Tiny L) := w+lin x (fun i=>(s i).val)
  have distinct : Function.Injective shift := fun _ _ e=>tiny_injective L x inj ok (add_left_cancel e)
  have holes : univ.image shift⊆univ\B := by
    intro z hz
    obtain ⟨s,_,rfl⟩ := mem_image.mp hz
    apply mem_sdiff.mpr ⟨mem_univ _,?_⟩
    intro rep
    obtain ⟨a,_,ea⟩ := mem_image.mp rep
    have less : ∃ i,(a i).val<(s i).val := by
      by_contra! no
      let b : Box L := fun i=>⟨(a i).val-(s i).val,(Nat.sub_le ..).trans_lt (a i).isLt⟩
      apply miss b
      apply add_right_cancel (b:=lin x (fun i=>(s i).val))
      rw [←show eval a=w+lin x (fun i=>(s i).val) from ea]
      change (∑ i,((a i).val-(s i).val) • x i)+(∑ i,(s i).val • x i)=∑ i,(a i).val • x i
      rw [←sum_add_distrib]; simp only [←add_nsmul,Nat.sub_add_cancel (no _)]
    obtain ⟨i,il⟩ := less
    let endpt (i : I) := decide (i=J)
    have su : lin x (fun i=>if endpt i then 2^L i else 0)=w := by
      simp [lin,endpt,w]
    have same := compare L x inj ok s a endpt (by simpa [endpt] using pos)
      (by
        have le := single_le_sum (f:=fun j : I=>if (a j).val<(s j).val then 2 else 0) (fun _ _=>Nat.zero_le _) (mem_univ i)
        simpa [endpt,il] using le)
      (by
        apply large.trans
        apply le_trans _ (single_le_sum (fun _ _=>Nat.zero_le _) (mem_univ J))
        simp [endpt])
      (by rw [su,add_comm]; exact ea.symm)
    have h := same J
    simp only [endpt,decide_true,if_true] at h
    have := (a J).isLt; omega
  have lt := card_le_card holes
  rw [card_image_of_injective _ distinct,card_univ] at lt
  change K<Fintype.card (Tiny L) at enough
  omega

end OMA.PathHoles
