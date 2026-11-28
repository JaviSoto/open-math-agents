import CubeNeighbors
import CycleQuotient

/-! The quotient cube near a complete doubling cycle. -/

namespace OMA.QuotientShadow
open Finset

theorem successor {G Q : Type*} [AddCommGroup G] [DecidableEq G] [AddCommGroup Q]
    [DecidableEq Q] [Fintype Q] (B : Finset G) (π : G→+Q)
    (rigid : ∀ T⊆B,∀ m : Multiset G,(∀ a∈m,a∈B) → π (∑ a∈T,a)=π m.sum →
      (m.card≤T.card ∨ ((∑ a∈T,a)≠m.sum ∧ m.card≤T.card+1)) → m=T.val)
    {b : G} (bi : b∈B) (alive : 2 • π b≠0)
    (few : (B.card+14)*(Fintype.card Q-2^B.card)<2^(B.card-1)) : 2 • b∈B := by
  classical
  let v (S : Finset G) := π (∑ z∈S,z)
  have sm (S : Finset G) : S.val.sum=∑ z∈S,z := by change _=(S.val.map id).sum; simp
  have insertV (i) (S : Finset G) (off : i∉S) : v (insert i S)=π i+v S := by
    dsimp [v]; rw [sum_insert off,map_add]
  have ordered (S T : Finset G) (si : S⊆B) (ti : T⊆B) (le : S.card≤T.card) (eq : v S=v T) : S=T := by
    exact Finset.val_inj.mp (rigid T ti S.val (fun _ h=>si h) (by rw [sm]; exact eq.symm) (.inl le))
  have vi : Set.InjOn v B.powerset := by
    intro s hs t ht e
    rcases le_total s.card t.card with le|le
    · exact ordered s t (mem_powerset.mp hs) (mem_powerset.mp ht) le e
    · exact (ordered t s (mem_powerset.mp ht) (mem_powerset.mp hs) le e.symm).symm
  let g := 2 • π b
  let box := B.powerset.image v
  by_contra fail
  have hole : g∉box := by
    intro h
    obtain ⟨T,ht,hit⟩ := mem_image.mp h
    let m : Multiset G := {b,b}
    have bad : m≠T.val := fun e=>by have h := T.nodup; rw [←e] at h; simp [m] at h
    have force := rigid T (mem_powerset.mp ht) m (by simp [m,bi])
      (by simpa [m,two_nsmul,g,v] using hit)
    have mc : m.card=2 := by simp [m]
    have tc : T.card<2 := by by_contra! many; exact bad (force (.inl (mc ▸ many)))
    have pos : T.card≠0 := fun eq=>by rw [card_eq_zero.mp eq] at hit; exact alive (by simpa [v,g] using hit.symm)
    obtain ⟨a,at'⟩ := card_eq_one.mp (by omega : T.card=1)
    have eq : (∑ z∈T,z)=m.sum := by by_contra ne; exact bad (force (.inr ⟨ne,by omega⟩))
    have same : a=2 • b := by simpa [at',m,two_nsmul] using eq
    exact fail (same ▸ mem_powerset.mp ht (by simp [at']))
  let X := B.erase b
  let D := X.powerset.filter (fun s=>g+v s∈box)
  have ds := filter_subset (fun s=>g+v s∈box) X.powerset
  have abs (s : Finset G) (xs : s⊆X) : b∉s := fun m=>notMem_erase b B (xs m)
  have rep (s) (sd : s∈D) : ∃ t⊆X,v t=g+v s := by
    obtain ⟨h,mem⟩ := mem_filter.mp sd
    obtain ⟨t,ht,eq⟩ := mem_image.mp mem
    refine ⟨t,?_,eq⟩
    have xs := mem_powerset.mp h; have tb := mem_powerset.mp ht
    intro z zt
    apply mem_erase.mpr ⟨?_,tb zt⟩
    rintro rfl
    have es := insertV z (t.erase z) (notMem_erase z t)
    rw [insert_erase zt] at es
    have ez : v (t.erase z)=v (insert z s) := by
      rw [insertV _ _ (abs s xs)]
      change v t=2 • π z+v s at eq
      rw [two_nsmul,es,add_assoc] at eq; exact add_left_cancel eq
    have both := vi (mem_powerset.mpr ((erase_subset ..).trans tb))
      (mem_powerset.mpr (insert_subset bi (xs.trans (erase_subset ..)))) ez
    exact notMem_erase z t (both ▸ mem_insert_self ..)
  choose t ti tv using rep
  let f (s : Finset G) := if hs : s∈D then t s hs else ∅
  have fi (s) (hs : s∈D) : f s⊆X := by simpa [f,hs] using ti s hs
  have fv (s) (hs : s∈D) : v (f s)=g+v s := by simpa [f,hs] using tv s hs
  have imp (s) (hs : s∈D) : s⊆B := (mem_powerset.mp (ds hs)).trans (erase_subset ..)
  have out (s) (hs : s∈D) : f s⊆B := (fi s hs).trans (erase_subset ..)
  have inj : Set.InjOn f D := by
    intro s hs t ht e
    exact vi (mem_powerset.mpr (imp _ hs)) (mem_powerset.mpr (imp _ ht))
      (add_left_cancel (((fv s hs).symm.trans (congrArg v e)).trans (fv t ht)))
  have move (s) (hs : s∈D) : (s\f s).Nonempty := by
    by_contra! no
    have sub : s⊆f s := sdiff_eq_empty_iff_subset.mp no
    apply hole
    apply mem_image.mpr ⟨f s\s,mem_powerset.mpr (sdiff_subset.trans (out s hs)),?_⟩
    apply add_right_cancel (b:=v s)
    rw [←fv s hs]; change π _ + π _=π _
    rw [←map_add,sum_sdiff sub]
  have gain (s) (hs : s∈D) : (f s).card ≤ s.card+1 := by
    let m := b ::ₘ b ::ₘ s.val
    by_contra! no
    have eq := rigid (f s) (out s hs) m (by
      intro z hz; simp only [m,Multiset.mem_cons] at hz
      exact hz.elim (fun h=>h ▸ bi) (fun h=>h.elim (fun e=>e ▸ bi) (fun h=>imp s hs h)))
      (by simpa [m,sm,g,v,two_nsmul,add_assoc] using fv s hs)
      (.inl (by simp [m]; omega))
    have nd := (f s).nodup; rw [←eq] at nd; simp [m] at nd
  have up (s) (hs : s∈D) (i) (hi : i∈s\f s) (low : s.erase i∈D) :
      (f s).card≤(f (s.erase i)).card := by
    let u := s.erase i
    have mem := mem_sdiff.mp hi
    have step := insertV i (s.erase i) (notMem_erase i s)
    rw [insert_erase mem.1] at step
    have eq : v (f s)=π i+v (f u) := by rw [fv _ hs,fv _ low,step]; abel
    by_contra! lt
    let m := i ::ₘ (f u).val
    have bad := rigid (f s) (out _ hs) m (fun a ha=>by
      rcases Multiset.mem_cons.mp ha with rfl|ins
      · exact imp _ hs mem.1
      · exact out _ low ins) (by simpa [m,sm,v] using eq) (.inl (by simp [m]; omega))
    have inside : i∈(f s).val := bad ▸ Multiset.mem_cons_self i _
    exact mem.2 inside
  have cross (s) (hs : s∈D) (t') (ht : t'∈D) (card : (f s).card=(f t').card)
      (i) (hi : i∈s\f s) (j) (hj : j∈t'\f t') (er : s.erase i=t'.erase j) (ne : i≠j) : j∈f s := by
    by_contra no
    obtain ⟨is,off⟩ := mem_sdiff.mp hi; obtain ⟨jt,_⟩ := mem_sdiff.mp hj
    have ss := insertV i (s.erase i) (notMem_erase i s)
    have tt := insertV j (t'.erase j) (notMem_erase j t')
    rw [insert_erase is,er] at ss; rw [insert_erase jt] at tt
    let m := i ::ₘ (f t').val
    have eq : v (insert j (f s))=π m.sum := by
      simp only [m,Multiset.sum_cons,sm,map_add,insertV _ _ no]
      change π j+v (f s)=π i+v (f t')
      rw [fv _ hs,fv _ ht,ss,tt]; abel
    have bad := rigid (insert j (f s)) (insert_subset (imp _ ht jt) (out _ hs)) m
      (fun a h=>by
        rcases Multiset.mem_cons.mp h with rfl|h
        · exact imp _ hs is
        · exact out _ ht h) eq (.inl (by simp [m,no,card]))
    have inside : i∈(insert j (f s)).val := bad ▸ Multiset.mem_cons_self i _
    exact (mem_insert.mp inside).elim ne off
  have loss := OMA.CubeNeighbors.loss X D f ds inj fi move gain up cross
  let miss := X.powerset\D
  have imiss : Set.InjOn (fun s=>g+v s) (miss : Set _) := by
    intro s hs t ht e
    exact vi (mem_powerset.mpr ((mem_powerset.mp (mem_sdiff.mp hs).1).trans (erase_subset ..)))
      (mem_powerset.mpr ((mem_powerset.mp (mem_sdiff.mp ht).1).trans (erase_subset ..))) (add_left_cancel e)
  have holes : miss.image (fun s=>g+v s)⊆univ\box := by
    intro z hz; obtain ⟨s,hs,rfl⟩ := mem_image.mp hz
    exact mem_sdiff.mpr ⟨mem_univ _,fun yes=>(mem_sdiff.mp hs).2 (mem_filter.mpr ⟨(mem_sdiff.mp hs).1,yes⟩)⟩
  have card := card_le_card holes
  rw [card_image_of_injOn imiss,card_sdiff_of_subset (subset_univ _),card_univ] at card
  have bc : box.card=2^B.card := (card_image_of_injOn vi).trans (card_powerset _)
  rw [bc] at card
  change (X.powerset\D).card≤_ at card
  rw [card_sdiff_of_subset ds] at card
  have dim : X.card+1=B.card := card_erase_add_one bi
  have low := loss.trans (Nat.mul_le_mul_left (X.card+15) card)
  rw [show B.card-1=X.card by omega,show B.card+14=X.card+15 by omega] at few
  exact few.not_ge low

end OMA.QuotientShadow
