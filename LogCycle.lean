import QuotientShadow
import LongCycleShape

/-! A single logarithmic-size affine doubling cycle suffices, with no
    hypotheses on the remaining labels. -/

open private OMA.LongCycle.cycle_order OMA.LongCycle.inherited OMA.LongCycle.translate from LongCycle
open private OMA.BinaryPrefix.sum_bits from BinaryPrefix
namespace OMA.LogCycle
open Finset Arxiv.«2607.08366»

private theorem only_involution {G : Type*} [AddCommGroup G] [Fintype G] [IsAddCyclic G]
    {a b : G} (an : a≠0) (bn : b≠0) (ak : 2 • a=0) (bk : 2 • b=0) : a=b := by
  classical
  by_contra diff
  let T := (univ : Finset G).filter (fun z=>2 • z=0)
  have up : T.card≤2 := IsAddCyclic.card_nsmul_eq_zero_le (by decide : 0<2)
  have le : ({a,b,0} : Finset G)⊆T := by
    intro z hz
    apply mem_filter.mpr ⟨mem_univ _,?_⟩
    rcases (by simpa [or_assoc] using hz : z=a ∨ z=b ∨ z=0) with rfl|rfl|rfl
    · exact ak
    · exact bk
    · simp
  have := card_le_card le; simp [diff,an,bn] at this; omega

private theorem connected {N : ℕ} [NeZero N] {A C D : Finset (ZMod N)} (ok : IsValidMod A)
    (sub : C∪D⊆A) (dis : Disjoint C D) (cp : C.Nonempty)
    (cc : ∀ z∈C,2 • z∈C) (dd : ∀ z∈D,2 • z∈D) : D=∅ := by
  classical
  let f (z : ZMod N) := 2 • z+0
  have non := cp.mono (subset_union_left (s₂:=D))
  have full : ∀ z∈C∪D,f z∈C∪D := by
    intro z hz
    rcases mem_union.mp hz with c|d
    · simpa [f] using mem_union_left D (cc z c)
    · simpa [f] using mem_union_right C (dd z d)
  obtain ⟨u,hu,orbit⟩ := OMA.AffineDoubling.closed_orbit (OMA.LongCycle.inherited ok sub) non 0 full
  have cont (P : Finset (ZMod N)) (mem : u∈P) (stay : ∀ z∈P,2 • z∈P) : C∪D⊆P := by
    have ind (i : ℕ) : f^[i] u∈P := by
      induction i with
      | zero => exact mem
      | succ i ih => rw [Function.iterate_succ_apply']; simpa [f] using stay _ ih
    intro z hz
    obtain ⟨i,_,rfl⟩ := mem_image.mp (orbit ▸ hz); exact ind i
  by_contra ne
  obtain ⟨x,hx⟩ := cp
  obtain ⟨z,hz⟩ := nonempty_iff_ne_empty.mpr ne
  rcases mem_union.mp hu with uc|ud
  · exact disjoint_left.mp dis ((cont C uc cc) (mem_union_right _ hz)) hz
  · exact disjoint_left.mp dis hx ((cont D ud dd) (mem_union_left _ hx))

/-- Below 2^n the logarithmic cycle forces closure, with one possible
    terminal involution as the sole label outside the cycle. -/
theorem shape {N n r : ℕ} [NeZero N] (rp : 0<r) (A : Finset (ZMod N)) (card : A.card=n)
    (ok : IsValidMod A) (y : ZMod N) (wrap : 2^r • y=y) (C : Finset (ZMod N)) (cs : C.card=r)
    (im : C=(range r).image (fun j=>2^j • y)) (inc : C⊆A) (lt : N<2^n)
    (threshold : 2*(n-r+14)≤2^r-1) :
    (∀ a∈A,2 • a∈A) ∨ (r+1=n ∧ ∃ b∈A\C,2 • b=0 ∧ A=insert b C) := by
  classical
  let H := AddSubgroup.zmultiples y
  let Q := ZMod N ⧸ H
  let π : ZMod N→+Q := QuotientAddGroup.mk' H
  let : Fintype Q := Fintype.ofFinite Q
  have : IsAddCyclic Q := isAddCyclic_of_surjective π (QuotientAddGroup.mk'_surjective H)
  let B := A\C
  let k := B.card
  let q := Fintype.card Q
  have part : C∪B=A := by rw [union_comm]; exact sdiff_union_of_subset inc
  have dis : Disjoint C B := disjoint_sdiff_self_right
  have dim : r+k=n := cs ▸ card ▸ (card_union_of_disjoint dis).symm.trans (congrArg Finset.card part)
  have ord := OMA.LongCycle.cycle_order ok y rp wrap C im cs inc
  have index : q*(2^r-1)=N := by
    have e := H.index_mul_card
    rw [AddSubgroup.index_eq_card,Nat.card_eq_fintype_card,Nat.card_eq_fintype_card (α:=ZMod N),ZMod.card] at e
    change q*Nat.card (AddSubgroup.zmultiples y)=N at e
    rwa [Nat.card_zmultiples,ord] at e
  have inj : Set.InjOn (fun j : ℕ=>2^j • y) (range r : Finset ℕ) :=
    card_image_iff.mp (by rw [←im,cs,card_range])
  have sc : (∑ a∈C,a)=0 := by
    rw [im,sum_image inj,←sum_smul,OMA.BinaryPrefix.sum_bits,←ord,addOrderOf_nsmul_eq_zero]
  have rigid (T : Finset (ZMod N)) (tb : T⊆B) (m : Multiset (ZMod N)) (mb : ∀ a∈m,a∈B)
      (eq : π (∑ a∈T,a)=π m.sum)
      (len : m.card≤T.card ∨ ((∑ a∈T,a)≠m.sum ∧ m.card≤T.card+1)) : m=T.val := by
    apply OMA.CyclePacking.absorb ok inc sc (cs ▸ rp) T tb m mb _ len
    intro l hl
    have zh : (∑ a∈T,a)-m.sum∈H := QuotientAddGroup.eq_iff_sub_mem.mp eq
    have cond : r≤l ∨ ((∑ a∈T,a)-m.sum≠0 ∧ r≤l+1) := by rw [cs] at hl; simpa only [sub_ne_zero] using hl
    simpa only [←im] using OMA.CyclePacking.represents rp y ord _ zh l cond
  have count : 2^k≤q := (OMA.CycleQuotient.box B π rigid).1
  have distinct (a) (ab : a∈B) (b) (bb : b∈B) (eq : π a=π b) : a=b := by
    have e := rigid {b} (singleton_subset_iff.mpr bb) {a} (by simpa using ab)
      (by simpa using eq.symm) (.inl (by simp))
    simpa using e
  have nz (a) (ab : a∈B) : π a≠0 := by
    intro zero
    have e := rigid {a} (singleton_subset_iff.mpr ab) 0 (by simp) (by simpa using zero) (.inl (by simp))
    simp at e
  have succ (a) (ab : a∈B) (live : 2 • π a≠0) : 2 • a∈B := by
    apply OMA.QuotientShadow.successor B π rigid ab live
    have kp : 0<k := card_pos.mpr ⟨a,ab⟩
    have exp : 2^k=2^(k-1)*2 := by conv_lhs => rw [show k=k-1+1 by omega,pow_succ]
    have thresh : 2*(k+14)≤2^r-1 := by rwa [show k=n-r by omega]
    let e := q-2^k
    have qsum : e+2^k=q := Nat.sub_add_cancel count
    have vol : 2^n=2^r*2^k := by rw [←dim,pow_add]
    have u := Nat.one_le_two_pow (n:=r)
    have rem : e*(2^r-1)<2^k := by
      rw [←qsum,add_mul] at index
      rw [show 2^r=2^r-1+1 by omega,add_mul,one_mul,mul_comm (2^r-1)] at vol
      omega
    have mult := (Nat.mul_le_mul_left e thresh).trans_lt rem
    rw [exp] at mult
    change (k+14)*e<2^(k-1)
    nlinarith
  have terminal (a) (ab : a∈B) (dead : 2 • π a=0) : 2 • a=0 ∨ 2 • a∈C := by
    apply OMA.CycleTerminal.terminal rp ok inc cs sc y wrap ord im (mem_sdiff.mp ab).1 (mem_sdiff.mp ab).2
    apply (QuotientAddGroup.eq_zero_iff _).mp
    change π (2 • a)=0; rwa [map_nsmul]
  have turn := (OMA.CycleTerminal.turn rp y wrap C im).1
  by_cases miss : ∃ b∈B,2 • b=0
  · right
    obtain ⟨b,bb,kill⟩ := miss
    have dead := OMA.CycleTerminal.dead ok (card_pos.mp (cs ▸ rp)) inc sc
      (mem_sdiff.mp bb).1 (mem_sdiff.mp bb).2 kill
    let D := B.erase b
    have rem : D=∅ := by
      apply connected ok (union_subset inc ((erase_subset b B).trans sdiff_subset)) (dis.mono_right (erase_subset ..))
        (card_pos.mp (cs ▸ rp)) turn
      intro a ha
      obtain ⟨ne,ab⟩ := mem_erase.mp ha
      have live : 2 • π a≠0 := fun die=>ne (distinct a ab b bb
        (only_involution (nz a ab) (nz b bb) die (by rw [←map_nsmul,kill,map_zero])))
      exact mem_erase.mpr ⟨dead.2 a ab,succ a ab live⟩
    have sing : B={b} := by
      have e := insert_erase bb
      change insert b D=B at e; simpa [rem] using e.symm
    have one : k=1 := by simp [k,sing]
    exact ⟨by omega,b,bb,kill,by rw [←part,sing,union_singleton]⟩
  · left
    intro a ha
    rcases mem_union.mp (part ▸ ha) with c|b
    · exact inc (turn a c)
    · by_cases dead : 2 • π a=0
      · exact inc ((terminal a b dead).resolve_left (fun z=>miss ⟨a,b,z⟩))
      · exact (mem_sdiff.mp (succ a b dead)).1

theorem lower {N n r : ℕ} [NeZero N] (hn : 2≤n) (rp : 0<r) (A : Finset (ZMod N)) (card : A.card=n)
    (ok : IsValidMod A) (y t : ZMod N) (wrap : 2^r • y=y)
    (inj : Set.InjOn (fun j : ℕ=>2^j • y) (range r : Finset ℕ))
    (inc : ∀ j<r,2^j • y-t∈A) (threshold : 2*(n-r+14)≤2^r-1) : minModulus n≤N := by
  classical
  by_cases lt : N<2^n
  · let A' := A.image (fun z=>z+t)
    let C := (range r).image (fun j=>2^j • y)
    have ca : A'.card=n := (card_image_of_injective A (fun _ _ e=>add_right_cancel e)).trans card
    have cs : C.card=r := (card_image_of_injOn inj).trans (card_range _)
    have sub : C⊆A' := by
      intro z hz; obtain ⟨j,hj,rfl⟩ := mem_image.mp hz
      exact mem_image.mpr ⟨_,inc j (mem_range.mp hj),sub_add_cancel ..⟩
    rcases shape rp _ ca (OMA.LongCycle.translate A ok t) y wrap C cs rfl sub lt threshold with closed|exc
    · exact (OMA.AffineDoublingClass.optimum hn).2 ⟨NeZero.pos _,A',0,ca,OMA.LongCycle.translate A ok t,
        by simpa using closed⟩
    · exact OMA.LongCycle.affine hn rp (by have := exc.1; omega) A card ok y t wrap inj inc
  · exact (Nat.sub_le (2^n) _).trans (by omega)

end OMA.LogCycle
