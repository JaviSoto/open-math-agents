import CycleTerminal

/-! A classification at the smallest possible index of a full doubling cycle. -/

open private OMA.LongCycle.cycle_order from LongCycle
open private OMA.BinaryPrefix.sum_bits from BinaryPrefix
namespace OMA.LongCycleShape
open Finset Arxiv.«2607.08366»

theorem boundary {N n r : ℕ} [NeZero N] (rr : 0<r)
    (A : Finset (ZMod N)) (card : A.card=n) (ok : IsValidMod A) (y : ZMod N)
    (wrap : 2^r • y=y) (C : Finset (ZMod N)) (cs : C.card=r)
    (im : C=(range r).image (fun j=>2^j • y)) (inc : C⊆A)
    (small : N<(2^(n-r)+1)*(2^r-1)) :
    (∀ a∈A,2 • a∈A) ∨
      (Even n ∧ N=2^n-2 ∧ r+1=n ∧ ∃ x∈A\C,2 • x=0 ∧ A=insert x C) := by
  classical
  let H := AddSubgroup.zmultiples y
  let Q := ZMod N ⧸ H
  let π : ZMod N→+Q := QuotientAddGroup.mk' H
  let : Fintype Q := Fintype.ofFinite Q
  have : IsAddCyclic Q := isAddCyclic_of_surjective π (QuotientAddGroup.mk'_surjective H)
  let B := A\C
  let k := B.card
  let q := Fintype.card Q
  have dis : Disjoint C B := disjoint_sdiff_self_right
  have part : C∪B=A := by rw [union_comm]; exact sdiff_union_of_subset inc
  have dim : r+k=n := by
    rw [←card,←cs]; exact (card_union_of_disjoint dis).symm.trans (congrArg Finset.card part)
  have ord := OMA.LongCycle.cycle_order ok y rr wrap C im cs inc
  have index : q*(2^r-1)=N := by
    have e := H.index_mul_card
    rw [AddSubgroup.index_eq_card,Nat.card_eq_fintype_card,Nat.card_eq_fintype_card (α:=ZMod N),ZMod.card] at e
    change q*Nat.card (AddSubgroup.zmultiples y)=N at e
    rwa [Nat.card_zmultiples,ord] at e
  have inj : Set.InjOn (fun j : ℕ=>2^j • y) (range r : Finset ℕ) :=
    card_image_iff.mp (by rw [←im,cs,card_range])
  have sc : (∑ a∈C,a)=0 := by
    rw [im,sum_image inj,←sum_smul,OMA.BinaryPrefix.sum_bits,←ord,addOrderOf_nsmul_eq_zero]
  have result := OMA.CycleQuotient.box B π (by
    intro T tB m mB eq len
    apply OMA.CyclePacking.absorb ok inc sc (cs ▸ rr) T tB m mB _ len
    intro l hl
    have zh : (∑ a∈T,a)-m.sum∈H := QuotientAddGroup.eq_iff_sub_mem.mp eq
    have cond : r≤l ∨ ((∑ a∈T,a)-m.sum≠0 ∧ r≤l+1) := by
      rw [cs] at hl
      simpa only [sub_ne_zero] using hl
    simpa only [←im] using OMA.CyclePacking.represents rr y ord _ zh l cond)
  change 2^k≤q ∧ (q=2^k → B.Nonempty → ∃ x,B=(range k).image (fun j=>2^j • x)) at result
  have unfoldN : (2:ℕ)^n=2^r*2^k := by rw [←dim,pow_add]
  have pos : 0<2^r := by positivity
  have eq : q=2^k := by
    rw [show n-r=k by omega] at small
    by_contra ne
    have le := Nat.mul_le_mul_right (2^r-1) (show 2^k+1≤q by omega)
    omega
  have cstay := (OMA.CycleTerminal.turn rr y wrap C im).1
  by_cases non : B.Nonempty
  · obtain ⟨x,path⟩ := result.2 eq non
    have kp : 0<k := card_pos.mpr non
    let v (j : ℕ) := 2^j • x
    have step (j : ℕ) : 2 • v j=v (j+1) := by simp only [v,pow_succ',mul_smul]
    have mem (j : ℕ) (h : j<k) : v j∈B := path ▸ mem_image_of_mem _ (mem_range.mpr h)
    let b := v (k-1)
    have bB : b∈B := mem _ (by omega)
    have endpt : 2 • b=v k := by rw [show b=v (k-1) from rfl,step,show k-1+1=k by omega]
    have hit : 2 • b∈H := by
      rw [endpt]
      apply (QuotientAddGroup.eq_zero_iff _).mp
      change π (2^k • x)=0
      rw [map_nsmul]
      apply addOrderOf_dvd_iff_nsmul_eq_zero.mp
      have d := addOrderOf_dvd_natCard (π x)
      rw [Nat.card_eq_fintype_card] at d
      exact eq ▸ (d : addOrderOf (π x) ∣ q)
    rcases OMA.CycleTerminal.terminal rr ok inc cs sc y wrap ord im
      (mem_sdiff.mp bB).1 (mem_sdiff.mp bB).2 hit with zero|next
    · right
      have dead := OMA.CycleTerminal.dead ok (card_pos.mp (cs ▸ rr)) inc sc
        (mem_sdiff.mp bB).1 (mem_sdiff.mp bB).2 zero
      have one : k=1 := by
        by_contra ne
        apply dead.2 (v (k-2)) (mem _ (by omega))
        rw [step,show k-2+1=k-1 by omega]
      have sing : B={b} := by
        apply eq_singleton_iff_unique_mem.mpr ⟨bB,?_⟩
        intro a ha
        exact card_le_one.mp (one.le : B.card≤1) a ha b bB
      have kd : r+1=n := by omega
      have actual : N+2^k=2^n := by
        rw [←index,eq,unfoldN,mul_comm (2^r)]
        rw [←Nat.mul_succ,Nat.succ_eq_add_one,Nat.sub_add_cancel (by omega)]
      rw [one,pow_one] at actual
      refine ⟨kd ▸ cs ▸ dead.1.add_one,by omega,kd,b,bB,zero,?_⟩
      rw [←part,sing,union_singleton]
    · left
      intro a ha
      rcases mem_union.mp (part ▸ ha) with ac|ab
      · exact inc (cstay a ac)
      · obtain ⟨j,hj,rfl⟩ := mem_image.mp (path ▸ ab)
        have jlt := mem_range.mp hj
        change 2 • v j∈A
        by_cases interior : j+1<k
        · rw [step]; exact (mem_sdiff.mp (mem _ interior)).1
        · rw [step,show j+1=k by omega,←endpt]; exact inc next
  · have empty := not_nonempty_iff_eq_empty.mp non
    have same : C=A := by simpa [empty] using part
    exact .inl (by rwa [←same])

/-- Below 2^n−1 a long cycle is either part of one closed orbit or the
    only other label is an involution, with n even and N=2^n−2. -/
theorem classify {N n r : ℕ} [NeZero N] (rr : 0<r) (large : n≤2*r)
    (A : Finset (ZMod N)) (card : A.card=n) (ok : IsValidMod A) (y : ZMod N)
    (wrap : 2^r • y=y) (C : Finset (ZMod N)) (cs : C.card=r)
    (im : C=(range r).image (fun j=>2^j • y)) (inc : C⊆A) (small : N<2^n-1) :
    (∀ a∈A,2 • a∈A) ∨
      (Even n ∧ N=2^n-2 ∧ r+1=n ∧ ∃ x∈A\C,2 • x=0 ∧ A=insert x C) := by
  apply boundary rr A card ok y wrap C cs im inc
  have le : r≤n := cs ▸ card ▸ card_le_card inc
  let k := n-r
  have dim : r+k=n := by dsimp [k]; omega
  have pow := Nat.pow_le_pow_right (by decide : 0<2) (show k≤r by omega)
  have pos := Nat.one_le_two_pow (n:=r)
  have exp : (2^k+1)*(2^r-1)+2^k+1=2^n+2^r := by
    rw [add_assoc,←Nat.mul_succ,Nat.succ_eq_add_one,Nat.sub_add_cancel pos,
      Nat.add_mul,Nat.one_mul,←dim,pow_add,mul_comm (2^k)]
  change N<(2^k+1)*(2^r-1)
  omega

end OMA.LongCycleShape
