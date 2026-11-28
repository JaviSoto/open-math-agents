import CyclePacking
import CycleQuotient

/-! The conjectured bound in the presence of one large doubling cycle,
    without requiring the remaining labels to be closed under doubling. -/

open private OMA.AffineDoubling.replace from AffineDoubling
open private OMA.AffineDoublingClass.total_iff from AffineDoublingClass
open private OMA.BinaryPrefix.fill OMA.BinaryPrefix.digits OMA.BinaryPrefix.weight
  OMA.BinaryPrefix.sum_bits from BinaryPrefix
namespace OMA.LongCycle
open Finset Arxiv.«2607.08366»

private lemma inherited {N : ℕ} {A C : Finset (ZMod N)} (ok : IsValidMod A) (sub : C⊆A) :
    IsValidMod C := (OMA.AffineDoublingClass.total_iff C).mpr (fun m ins sz mass=>
      OMA.AffineDoubling.replace ok C sub m (fun a ha=>sub (ins a ha)) sz mass)

private lemma cycle_order {N r : ℕ} [NeZero N] {A : Finset (ZMod N)} (ok : IsValidMod A)
    (y : ZMod N) (rpos : 0<r) (wrap : 2^r • y=y)
    (C : Finset (ZMod N)) (im : C=(range r).image (fun j=>2^j • y))
    (sz : C.card=r) (sub : C⊆A) : addOrderOf y=2^r-1 := by
  have eq : (1:ℕ) • y=2^r • y := by simpa using wrap.symm
  have dvd := (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp (nsmul_eq_nsmul_iff_modEq.mp eq)
  have digits := (OMA.AffineDoublingClass.orbit_iff 0 y C sz (by simpa using im)).mp (inherited ok sub)
  have lower := OMA.DyadicDigits.lower (addOrderOf_pos y) digits
  have lb : 2*r≤2^r := by
    obtain ⟨a,rfl⟩ : ∃ a,r=a+1 := ⟨r-1,by omega⟩
    rw [pow_succ]; have b := a.lt_two_pow_self; omega
  obtain ⟨d,ed⟩ := dvd
  by_contra ne
  have oddpos := Nat.one_lt_two_pow (n:=r) rpos.ne'
  have dk : 2 ≤ d := by
    by_contra! low
    interval_cases d
    · simp only [Nat.mul_zero] at ed; omega
    · simp only [Nat.mul_one] at ed; exact ne ed.symm
  have prod := Nat.mul_le_mul_left (addOrderOf y) dk
  rw [←ed] at prod
  omega

private lemma path_bound {N : ℕ} [NeZero N] {A C B : Finset (ZMod N)} (ok : IsValidMod A)
    (part : C∪B=A) (dis : Disjoint C B) (non : C.Nonempty) (sc : (∑ a∈C,a)=0)
    (x : ZMod N) (path : B=(range B.card).image (fun j=>2^j • x)) :
    2^B.card≤A.card := by
  classical
  let k := B.card
  have bA : B⊆A := part ▸ subset_union_right
  have count := card_union_of_disjoint dis
  rw [part] at count
  have inj : Set.InjOn (fun j : ℕ=>2^j • x) (range k : Finset ℕ) :=
    card_image_iff.mp (by rw [←path,card_range])
  have sm : (∑ a∈A,a)=(2^k-1) • x := by
    rw [←part,sum_union dis,sc,zero_add]
    calc (∑ a∈B,a) = ∑ j∈range k,2^j • x := by conv_lhs => rw [path,sum_image inj]
         _ = _ := by rw [←sum_smul,OMA.BinaryPrefix.sum_bits]
  by_contra! lt
  change A.card<2^k at lt
  have pos : 0<2^k := by positivity
  obtain ⟨L,ins,e,len,_⟩ := OMA.BinaryPrefix.digits k (2^k-1) (by omega)
  obtain ⟨M,bnd,wt,sz⟩ := OMA.BinaryPrefix.fill k A.card L ins
    (by dsimp [k] at len; omega) (by rw [e]; omega)
  let w : Multiset (ZMod N) := ((M.map (fun j=>2^j • x) : List _) : Multiset _)
  have inside (a : ZMod N) (ha : a∈w) : a∈B := by
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ha
    exact path ▸ mem_image_of_mem _ (mem_range.mpr (bnd j hj))
  have mass : w.sum=∑ a∈A,a := by
    rw [sm,←e,←wt]
    change (M.map (fun j=>2^j • x)).sum=OMA.BinaryPrefix.weight M • x
    clear bnd wt sz inside
    induction M with
    | nil => simp [OMA.BinaryPrefix.weight]
    | cons a l ih =>
      simpa only [OMA.BinaryPrefix.weight,List.map_cons,List.sum_cons,add_nsmul] using
        congrArg (fun z=>2^a • x+z) ih
  have wc : w.card=A.card := (List.length_map ..).trans sz
  have all := (OMA.AffineDoublingClass.total_iff A).mp ok w (fun a ha=>bA (inside a ha)) wc mass
  obtain ⟨a,ha⟩ := non
  have yA : a∈A := part ▸ mem_union_left _ ha
  exact disjoint_left.mp dis ha (inside a (all ▸ yA))

/-- The sharp conjectured lower bound already holds when a complete
    doubling cycle accounts for at least half of the input set. -/
theorem ordinary {N n r : ℕ} [NeZero N] (hn : 2≤n) (rr : 0<r) (large : n≤2*r)
    (A : Finset (ZMod N)) (card : A.card=n) (ok : IsValidMod A) (y : ZMod N)
    (wrap : 2^r • y=y) (C : Finset (ZMod N)) (cs : C.card=r)
    (im : C=(range r).image (fun j=>2^j • y)) (inc : C⊆A) :
    minModulus n≤N := by
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
  have ord := cycle_order ok y rr wrap C im cs inc
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
  have introN : minModulus n=2^n-2^(Nat.log 2 n) := rfl
  by_cases eq : q=2^k
  · have threshold : 2^k≤n := by
      by_cases empty : B.Nonempty
      · obtain ⟨x,path⟩ := result.2 eq empty
        rw [←card]; exact path_bound ok part dis (card_pos.mp (cs ▸ rr)) sc x path
      · have z : k=0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp empty)
        rw [z]; omega
    have log := (Nat.le_log_iff_pow_le (by decide : 1<2) (by omega : n≠0)).mpr threshold
    have power := Nat.pow_le_pow_right (by decide : 0<2) log
    have count : N+2^k=2^n := by
      rw [←index,eq,unfoldN,mul_comm (2^r)]
      rw [←Nat.mul_succ,Nat.succ_eq_add_one,Nat.sub_add_cancel (by omega)]
    rw [introN]; omega
  · have exc : 2^k+1≤q := by omega
    have big := Nat.mul_le_mul_right (2^r-1) exc
    have l := Nat.pow_le_pow_right (by decide : 0<2) (show k≤r by omega)
    have expansion : (2^k+1)*(2^r-1)+2^k+1=2^n+2^r := by
      rw [add_assoc,←Nat.mul_succ,Nat.succ_eq_add_one,Nat.sub_add_cancel (by omega),
        Nat.add_mul,Nat.one_mul,unfoldN,mul_comm (2^k)]
    have lg : 0<2^Nat.log 2 n := by positivity
    rw [index] at big
    rw [introN]; omega

private lemma translate {N : ℕ} (A : Finset (ZMod N)) (ok : IsValidMod A) (h : ZMod N) :
    IsValidMod (A.image (fun x=>x+h)) := by
  classical
  have inj : Function.Injective (fun x : ZMod N=>x+h) := fun _ _ eq=>add_right_cancel eq
  intro c total mass a ha
  obtain ⟨b,hb,rfl⟩ := mem_image.mp ha
  rw [sum_image inj.injOn,card_image_of_injective _ inj] at total
  rw [sum_image inj.injOn,sum_image inj.injOn] at mass
  simp only [mul_add,sum_add_distrib,←sum_mul,←Nat.cast_sum,total,sum_const,nsmul_eq_mul] at mass
  exact ok (fun z=>c (z+h)) total (add_right_cancel mass) b hb

/-- The affine form includes cycles with no relation imposed at all on
    the other n−r labels. -/
theorem affine {N n r : ℕ} [NeZero N] (hn : 2≤n) (rr : 0<r) (large : n≤2*r)
    (A : Finset (ZMod N)) (card : A.card=n) (ok : IsValidMod A) (y t : ZMod N)
    (wrap : 2^r • y=y)
    (distinct : Set.InjOn (fun j : ℕ=>2^j • y) (range r : Finset ℕ))
    (inside : ∀ j<r,2^j • y-t∈A) : minModulus n≤N := by
  classical
  let A' := A.image (fun x=>x+t)
  let C := (range r).image (fun j=>2^j • y)
  have ac : A'.card=n := (card_image_of_injective _ (fun _ _ eq=>add_right_cancel eq)).trans card
  apply ordinary hn rr large A' ac (translate A ok t) y wrap C
    ((card_image_of_injOn distinct).trans (card_range _)) rfl
  intro z hz
  obtain ⟨j,hj,rfl⟩ := mem_image.mp hz
  exact mem_image.mpr ⟨_,inside j (mem_range.mp hj),sub_add_cancel ..⟩

end OMA.LongCycle
