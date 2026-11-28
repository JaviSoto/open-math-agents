import CyclePacking

/-! At the minimum possible quotient size, the labels outside a full
    doubling cycle are themselves one dyadic progression. -/

namespace OMA.CycleQuotient
open Finset

theorem box {G Q : Type*} [AddCommGroup G] [DecidableEq G] [AddCommGroup Q] [Fintype Q]
    [IsAddCyclic Q] (B : Finset G) (π : G→+Q)
    (rigid : ∀ T⊆B,∀ m : Multiset G,(∀ a∈m,a∈B) → π (∑ a∈T,a)=π m.sum →
      (m.card≤T.card ∨ ((∑ a∈T,a)≠m.sum ∧ m.card≤T.card+1)) → m=T.val) :
    2^B.card≤Fintype.card Q ∧ (Fintype.card Q=2^B.card →
      B.Nonempty → ∃ x : G, B=(range B.card).image (fun j=>2^j • x)) := by
  classical
  let k := B.card
  let v (T : Finset G) := π (∑ a∈T,a)
  have valSum (T : Finset G) : T.val.sum=∑ a∈T,a := by change _=(T.val.map id).sum; simp
  have ordered (S T : Finset G) (sB : S⊆B) (tB : T⊆B) (len : T.card≤S.card)
      (eq : v S=v T) : S=T := by
    have z := rigid S sB T.val (fun _ h=>tB h) (by rwa [valSum]) (.inl len)
    exact (Finset.val_inj.mp z).symm
  have inj : Set.InjOn v (B.powerset : Finset (Finset G)) := by
    intro S sB T tB eq
    rcases le_total S.card T.card with le|le
    · exact (ordered _ _ (mem_powerset.mp tB) (mem_powerset.mp sB) le eq.symm).symm
    · exact ordered _ _ (mem_powerset.mp sB) (mem_powerset.mp tB) le eq
  have c : (B.powerset.image v).card=2^k := (card_image_of_injOn inj).trans (card_powerset B)
  refine ⟨c ▸ card_le_univ _,?_⟩
  intro perfect non
  have surj := eq_univ_of_card (B.powerset.image v) (c.trans perfect.symm)
  have repr (z : Q) : ∃ T⊆B,v T=z := by
    have mem : z∈B.powerset.image v := by rw [surj]; simp
    obtain ⟨T,ht,eq⟩ := mem_image.mp mem
    exact ⟨T,mem_powerset.mp ht,eq⟩
  have doubled (a : G) (ha : a∈B) (nz : 2 • π a≠0) : 2 • a∈B := by
    obtain ⟨T,tB,tval⟩ := repr (2 • π a)
    let words : Multiset G := {a,a}
    have eq : π (∑ x∈T,x)=π words.sum := by simpa [words,two_nsmul,v] using tval
    have cc : words.card=2 := by simp [words]
    have ins : ∀ x∈words,x∈B := by simp [words,ha]
    have absurd (q : words=T.val) : False := by
      have bad := T.nodup
      rw [←q] at bad
      simp [words] at bad
    have small : T.card<2 := by by_contra! big; exact absurd (rigid T tB words ins eq (.inl (cc ▸ big)))
    have pos : T.card≠0 := by
      intro zero; rw [card_eq_zero.mp zero] at tval
      exact nz (by simpa [v] using tval.symm)
    obtain ⟨b,tb⟩ := card_eq_one.mp (by omega : T.card=1)
    have mass : (∑ x∈T,x)=words.sum := by
      by_contra no
      exact absurd (rigid T tB words ins eq (.inr ⟨no,by omega⟩))
    have same : b=2 • a := by simpa [tb,words,two_nsmul] using mass
    rw [←same]; exact tB (by rw [tb]; simp)
  have pos : 0<k := card_pos.mpr non
  obtain ⟨z,zo⟩ := isAddCyclic_iff_exists_addOrderOf_eq_natCard.mp (inferInstance : IsAddCyclic Q)
  rw [Nat.card_eq_fintype_card,perfect] at zo
  obtain ⟨x,hx,off⟩ : ∃ x∈B,2^(k-1) • π x≠0 := by
    by_contra! all
    obtain ⟨T,sub,eq⟩ := repr z
    have zero : 2^(k-1) • z=0 := by
      rw [←eq]; dsimp [v]; rw [map_sum,smul_sum]
      exact sum_eq_zero (fun a ha=>all a (sub ha))
    have d := addOrderOf_dvd_iff_nsmul_eq_zero.mpr zero
    have less := Nat.pow_lt_pow_right (by decide : 1<2) (show k-1<k by omega)
    rw [zo] at d
    have big := Nat.le_of_dvd (by positivity : 0<2^(k-1)) d
    change 2^k≤_ at big; omega
  have ox : addOrderOf (π x)=2^k := by
    have d := addOrderOf_dvd_natCard (π x)
    rw [Nat.card_eq_fintype_card,perfect] at d
    obtain ⟨j,jk,eq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp d
    change j≤k at jk
    by_contra ne
    have lt : j<k := by
      by_contra! no
      have e : j=k := by omega
      exact ne (eq.trans (by rw [e]))
    apply off
    apply addOrderOf_dvd_iff_nsmul_eq_zero.mp
    rw [eq]; exact Nat.pow_dvd_pow 2 (by omega)
  have live (j : ℕ) (hj : j<k) : 2^j • π x≠0 := by
    intro eq
    have d := addOrderOf_dvd_iff_nsmul_eq_zero.mpr eq
    rw [ox] at d
    exact (Nat.not_le_of_gt (Nat.pow_lt_pow_right (by decide) hj)) (Nat.le_of_dvd (by positivity) d)
  have labels (j : ℕ) (jk : j<k) : 2^j • x∈B := by
    induction j with
    | zero => simpa using hx
    | succ j ih =>
      rw [pow_succ',mul_smul]
      apply doubled _ (ih (by omega))
      rw [map_nsmul,←mul_smul,←pow_succ']
      exact live _ jk
  have ne (j l : ℕ) (lt : j<l) (lk : l<k) : 2^j • x≠2^l • x := by
    intro eq
    have q := congrArg π eq
    simp only [map_nsmul] at q
    have p := Nat.pow_lt_pow_right (by decide : 1<2) lt
    have d := (Nat.modEq_iff_dvd' p.le).mp (nsmul_eq_nsmul_iff_modEq.mp q)
    rw [ox] at d
    have b := Nat.le_of_dvd (Nat.sub_pos_of_lt p) d
    have b' := Nat.pow_lt_pow_right (by decide : 1<2) lk
    exact (not_le_of_gt ((Nat.sub_le _ _).trans_lt b')) b
  have jinj : Set.InjOn (fun j : ℕ=>2^j • x) (range k : Finset ℕ) := by
    intro j hj l hl eq
    rcases lt_trichotomy j l with a|e|a
    · exact False.elim (ne _ _ a (mem_range.mp hl) eq)
    · exact e
    · exact False.elim (ne _ _ a (mem_range.mp hj) eq.symm)
  exact ⟨x,(eq_of_subset_of_card_le (by
    intro a ha
    obtain ⟨j,hj,rfl⟩ := mem_image.mp ha
    exact labels j (mem_range.mp hj)) (by rw [card_image_of_injOn jinj,card_range])).symm⟩

end OMA.CycleQuotient
