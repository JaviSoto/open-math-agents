import CubeCharge

/-! A gain restriction on a partial Boolean translation forces holes. -/

namespace OMA.CubeNeighbors
open Finset

private def neighbors {α : Type*} [DecidableEq α] (f : Finset α→Finset α) (s : Finset α) :=
  (s\f s).image (fun i=>s.erase i)

private theorem layer {α : Type*} [DecidableEq α] (f : Finset α→Finset α)
    (D T : Finset (Finset α)) (d : ℕ)
    (move : ∀ s∈D,(s\f s).Nonempty)
    (len : ∀ s∈D,(f s).card=s.card+d)
    (maps : ∀ s∈D,∀ i∈s\f s,s.erase i∈T)
    (cross : ∀ s∈D,∀ t∈D,∀ i∈s\f s,∀ j∈t\f t,
      s.erase i=t.erase j → i≠j → j∈f s) :
    D.card≤(d+2)*T.card := by
  classical
  apply OMA.CubeCharge.distribute D T (neighbors f) (d+2)
  · intro s hs r hr; obtain ⟨i,hi,rfl⟩ := mem_image.mp hr; exact maps s hs i hi
  · intro s hs; exact (move s hs).image _
  · intro r _ s hs hrs
    let P := D.filter (fun a=>r∈neighbors f a)
    have ss : s∈P := mem_filter.mpr ⟨hs,hrs⟩
    have rep (t) (ht : t∈P) : ∃ j∈t\f t,t.erase j=r := mem_image.mp (mem_filter.mp ht).2
    choose j jmem erase using rep
    let bit (t : Finset α) := if ht : t∈P then some (j t ht) else none
    have ins (t) (ht : t∈P) : insert (j t ht) r=t := by
      rw [←erase t ht,insert_erase (mem_sdiff.mp (jmem t ht)).1]
    have inject : Set.InjOn bit P := by
      intro t ht u hu eq
      change t∈P at ht
      change u∈P at hu
      have b : j t ht=j u hu := by simpa [bit,ht,hu] using eq
      rw [←ins t ht,←ins u hu,b]
    let Q := (f s)\s
    have sub : (P.erase s).image bit⊆Q.image some := by
      intro a ha
      obtain ⟨t,ht,rfl⟩ := mem_image.mp ha
      obtain ⟨diff,tp⟩ := mem_erase.mp ht
      have nb : j s ss≠j t tp := fun e=>diff (by rw [←ins t tp,←ins s ss,e])
      have l := cross s hs t (mem_filter.mp tp).1 (j s ss) (jmem s ss) (j t tp) (jmem t tp)
        ((erase s ss).trans (erase t tp).symm) nb
      have nr : j t tp∉r := by rw [←erase t tp]; simp
      have nots : j t tp∉s := by rw [←ins s ss]; simpa [nb.symm] using nr
      exact mem_image.mpr ⟨j t tp,mem_sdiff.mpr ⟨l,nots⟩,by simp [bit,tp]⟩
    have count := card_le_card sub
    rw [card_image_of_injOn (inject.mono (erase_subset ..)),card_image_of_injective _ (Option.some_injective _)] at count
    have remove := card_erase_add_one ss
    have displace : Q.card=(s\f s).card+d := by
      have one := card_sdiff_add_card_inter (f s) s
      have two := card_sdiff_add_card_inter s (f s)
      rw [inter_comm] at one
      have := len s hs
      dsimp [Q]; omega
    have size : (neighbors f s).card=(s\f s).card := by
      apply card_image_of_injOn
      intro i hi j hj eq
      change s.erase i=s.erase j at eq
      by_contra ne
      have a : i∈s.erase j := mem_erase.mpr ⟨ne,(mem_sdiff.mp hi).1⟩
      rw [←eq] at a; exact notMem_erase _ _ a
    change P.card≤_
    rw [size]
    have pos := card_pos.mpr (move s hs)
    nlinarith [Nat.mul_le_mul_left (d+1) pos]

theorem loss {α : Type*} [DecidableEq α] (X : Finset α) (D : Finset (Finset α))
    (f : Finset α→Finset α) (sub : D⊆X.powerset) (inj : Set.InjOn f D)
    (maps : ∀ s∈D,f s⊆X) (move : ∀ s∈D,(s\f s).Nonempty)
    (gain : ∀ s∈D,(f s).card ≤ s.card+1)
    (up : ∀ s∈D,∀ i∈s\f s,s.erase i∈D → (f s).card≤(f (s.erase i)).card)
    (cross : ∀ s∈D,∀ t∈D,(f s).card=(f t).card → ∀ i∈s\f s,∀ j∈t\f t,
      s.erase i=t.erase j → i≠j → j∈f s) :
    2^X.card≤(X.card+15)*(X.powerset.card-D.card) := by
  classical
  let U := D.filter (fun s=>s.card<(f s).card)
  let E := D.filter (fun s=>s.card=(f s).card)
  let H := X.powerset\D
  have outside (s) (hs : s∈D) (i : α) : s.erase i∈X.powerset :=
    mem_powerset.mpr ((erase_subset ..).trans (mem_powerset.mp (sub hs)))
  have aux (Z : Finset (Finset α)) (zs : Z⊆D) (d : ℕ) (len : ∀ s∈Z,(f s).card=s.card+d) (T : Finset (Finset α))
      (hit : ∀ s∈Z,∀ i∈s\f s,s.erase i∈T) : Z.card≤(d+2)*T.card := by
    apply layer f Z T d (fun s hs=>move s (zs hs)) len hit
    intro s hs t ht i hi j hj erase ne
    have sc := card_erase_add_one (mem_sdiff.mp hi).1; have tc := card_erase_add_one (mem_sdiff.mp hj).1
    rw [erase] at sc
    apply cross s (zs hs) t (zs ht) _ i hi j hj erase ne
    rw [len s hs,len t ht]; omega
  have top := aux U (filter_subset ..) 1 (fun s hs=>by
    have := (mem_filter.mp hs).2; have := gain s (mem_filter.mp hs).1; omega) H (by
    intro s hs i hi
    obtain ⟨sd,g⟩ := mem_filter.mp hs
    apply mem_sdiff.mpr ⟨outside s sd i,?_⟩
    intro low
    have := up s sd i hi low
    have := gain _ low
    have := card_erase_add_one (mem_sdiff.mp hi).1
    omega)
  have same := aux E (filter_subset ..) 0 (fun s hs=>by simpa using (mem_filter.mp hs).2.symm) (H∪U) (by
    intro s hs i hi
    obtain ⟨sd,g⟩ := mem_filter.mp hs
    by_cases low : s.erase i∈D
    · apply mem_union_right _ (mem_filter.mpr ⟨low,?_⟩)
      have := up s sd i hi low; have := card_erase_add_one (mem_sdiff.mp hi).1; omega
    · exact mem_union_left _ (mem_sdiff.mpr ⟨outside s sd i,low⟩))
  have rem := OMA.CubeCharge.rank_budget X D f sub inj maps gain
  have whole := card_filter_add_card_filter_not (s:=D) (fun s=>s.card<(f s).card)
  have middle := card_filter_add_card_filter_not (s:=D.filter (fun s=>¬s.card<(f s).card)) (fun s=>s.card=(f s).card)
  simp only [filter_filter] at middle
  have fe : (D.filter (fun s=>¬s.card<(f s).card ∧ s.card=(f s).card))=E :=
    filter_congr (fun _ _=>by omega)
  have fl : (D.filter (fun s=>¬s.card<(f s).card ∧ ¬s.card=(f s).card))=D.filter (fun s=>(f s).card<s.card) :=
    filter_congr (fun _ _=>by omega)
  rw [fe,fl] at middle
  have count := card_sdiff_add_card_eq_card sub
  have HC : H.card=X.powerset.card-D.card := card_sdiff_of_subset sub
  have union := card_union_le H U
  change U.card+_=D.card at whole
  change H.card+D.card=X.powerset.card at count
  rw [←HC] at rem ⊢
  rw [←card_powerset]
  change _≤U.card+_ at rem
  nlinarith

end OMA.CubeNeighbors
