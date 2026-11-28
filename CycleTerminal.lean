import LongCycle

/-! Endpoints of a dyadic path attached to a complete doubling cycle. -/

open private OMA.CyclePacking.grow from CyclePacking
open private OMA.AffineDoubling.replace from AffineDoubling
namespace OMA.CycleTerminal
open Finset Arxiv.«2607.08366»

theorem mask (r e : ℕ) (h : e<2^r) :
    ∃ J⊆range r,(∑ j∈J,2^j)=e := by
  classical
  induction r generalizing e with
  | zero => exact ⟨∅,empty_subset _,by simpa using (show e=0 by simpa using h).symm⟩
  | succ r ih =>
    by_cases lo : e<2^r
    · obtain ⟨J,s,eq⟩ := ih e lo
      exact ⟨J,s.trans (range_mono (by omega)),eq⟩
    · rw [pow_succ] at h
      obtain ⟨J,s,eq⟩ := ih (e-2^r) (by omega)
      have miss : r∉J := fun hr=>lt_irrefl r (mem_range.mp (s hr))
      exact ⟨insert r J,insert_subset (mem_range.mpr (by omega)) (s.trans (range_mono (by omega))),
        by rw [sum_insert miss,eq]; omega⟩

theorem turn {G : Type*} [AddCommGroup G] [DecidableEq G] {r : ℕ} (hr : 0<r) (y : G)
    (wrap : 2^r • y=y) (C : Finset G) (im : C=(range r).image (fun j=>2^j • y))
    : (∀ a∈C,2 • a∈C) ∧ (∀ a∈C,∃ b∈C,2 • b=a) := by
  classical
  let v (j : ℕ) := 2^j • y
  have step (j : ℕ) : 2 • v j=v (j+1) := by simp only [v,pow_succ',mul_smul]
  have mem (j : ℕ) (lt : j<r) : v j∈C := im ▸ mem_image_of_mem _ (mem_range.mpr lt)
  have endpt : v r=v 0 := by simpa [v] using wrap
  constructor
  · intro a ha
    obtain ⟨j,hj,rfl⟩ := mem_image.mp (im ▸ ha)
    have lt := mem_range.mp hj
    change 2 • v j∈C
    rw [step]
    by_cases short : j+1<r
    · exact mem _ short
    · rw [show j+1=r by omega,endpt]; exact mem _ hr
  · intro a ha
    obtain ⟨j,hj,rfl⟩ := mem_image.mp (im ▸ ha)
    have lt := mem_range.mp hj
    cases j with
    | zero => exact ⟨v (r-1),mem _ (by omega),by rw [step,show r-1+1=r by omega,endpt]⟩
    | succ j => exact ⟨v j,mem j (by omega),step j⟩

/-- If a doubled external label falls into the cycle subgroup, its only
    possible targets are zero or an actual member of the cycle. -/
theorem terminal {N r : ℕ} [NeZero N] (hr : 0<r) {A C : Finset (ZMod N)}
    (ok : IsValidMod A) (sub : C⊆A) (cs : C.card=r) (sc : (∑ a∈C,a)=0)
    (y : ZMod N) (wrap : 2^r • y=y) (ord : addOrderOf y=2^r-1)
    (im : C=(range r).image (fun j=>2^j • y)) {b : ZMod N} (ba : b∈A) (bc : b∉C)
    (hit : 2 • b∈AddSubgroup.zmultiples y) : 2 • b=0 ∨ 2 • b∈C := by
  classical
  by_contra! no
  obtain ⟨e,he,eq⟩ := mem_image.mp (mem_zmultiples_iff_mem_range_addOrderOf.mp hit)
  have lt := mem_range.mp he
  rw [ord] at lt
  obtain ⟨J,js,jv⟩ := mask r e (by omega)
  let f (j : ℕ) := 2^j • y
  let S := J.image f
  have inc : S⊆C := by rw [im]; exact image_subset_image js
  have inj : Set.InjOn f (range r : Finset ℕ) :=
    card_image_iff.mp (by rw [←im,cs,card_range])
  have sv : (∑ x∈S,x)=2 • b := by
    rw [show S=J.image f from rfl,sum_image (inj.mono js)]
    change (∑ j∈J,2^j • y)=2 • b
    rw [←sum_smul,jv,eq]
  have few : 2≤S.card := by
    by_contra! tiny
    rcases Nat.eq_zero_or_pos S.card with z|p
    · rw [card_eq_zero.mp z,sum_empty] at sv; exact no.1 sv.symm
    · obtain ⟨a,sa⟩ := card_eq_one.mp (by omega : S.card=1)
      have ea : a=2 • b := by simpa [sa] using sv
      exact no.2 (ea ▸ inc (by rw [sa]; simp))
  let T := C\S
  have tally : T.card+S.card=r := (card_sdiff_add_card_eq_card inc).trans cs
  have tv : T.val.sum=-(2 • b) := by
    have sm := sum_sdiff inc (f:=id)
    change (∑ x∈T,x)+(∑ x∈S,x)=(∑ x∈C,x) at sm
    rw [sv,sc] at sm
    have same : T.val.sum=∑ x∈T,x := by change _=(T.val.map id).sum; simp
    rw [same]; exact eq_neg_of_add_eq_zero_left sm
  obtain ⟨w,ins,ws,wm⟩ := OMA.CyclePacking.grow C (turn hr y wrap C im).2 T.val
    (fun _ hx=>(mem_sdiff.mp hx).1) (by
      intro z; rw [z,Multiset.sum_zero] at tv; exact no.1 (neg_eq_zero.mp tv.symm)) (r-2)
    (by change T.card≤r-2; omega)
  let m := b ::ₘ b ::ₘ b ::ₘ w
  have rival := OMA.AffineDoubling.replace ok (insert b C) (insert_subset ba sub) m
    (by
      intro z hz
      simp only [m,Multiset.mem_cons] at hz
      rcases hz with rfl|rfl|rfl|hw
      · exact ba
      · exact ba
      · exact ba
      · exact sub (ins z hw))
    (by simp only [m,Multiset.card_cons,ws,card_insert_of_notMem bc,cs]; omega)
    (by simp only [m,Multiset.sum_cons,wm,tv,sum_insert bc,sc,two_nsmul]; abel)
  have nd := (insert b C).nodup
  rw [←rival] at nd
  simp [m] at nd

/-- An external involutive label forces odd cycle length and cannot itself
    have an external dyadic predecessor. -/
theorem dead {N : ℕ} {A C : Finset (ZMod N)} (ok : IsValidMod A)
    (non : C.Nonempty) (sub : C⊆A) (sc : (∑ x∈C,x)=0)
    {b : ZMod N} (ba : b∈A) (bc : b∉C) (kill : 2 • b=0) :
    Odd C.card ∧ ∀ a∈A\C,2 • a≠b := by
  classical
  obtain ⟨z,hz⟩ := non
  have zb : z≠b := fun e=>bc (e ▸ hz)
  have odd : Odd C.card := by
    by_contra h
    obtain ⟨l,el⟩ := Nat.not_odd_iff_even.mp h
    let w := Multiset.replicate C.card b
    have sm : w.sum=0 := by
      simp only [w,Multiset.sum_replicate,el,←two_mul,mul_comm 2,mul_smul,kill,smul_zero]
    have eq := OMA.AffineDoubling.replace ok C sub w
      (fun x hx=>(Multiset.eq_of_mem_replicate hx) ▸ ba) (Multiset.card_replicate ..) (sm.trans sc.symm)
    exact zb (Multiset.eq_of_mem_replicate (eq ▸ hz : z∈w))
  refine ⟨odd,?_⟩
  intro a ha step
  obtain ⟨l,el⟩ := odd
  let w := a ::ₘ a ::ₘ Multiset.replicate (2*l) b
  have sm : (Multiset.replicate (2*l) b).sum=0 := by rw [Multiset.sum_replicate,mul_comm,mul_smul,kill,smul_zero]
  have eq := OMA.AffineDoubling.replace ok (insert b C) (insert_subset ba sub) w
    (by intro x hx
        simp only [w,Multiset.mem_cons] at hx
        rcases hx with rfl|rfl|hm
        · exact (mem_sdiff.mp ha).1
        · exact (mem_sdiff.mp ha).1
        · exact (Multiset.eq_of_mem_replicate hm) ▸ ba)
    (by simp [w,card_insert_of_notMem bc,el])
    (by simp only [w,Multiset.sum_cons,sm,sum_insert bc,sc,add_zero]; exact (two_nsmul a).symm.trans step)
  have inw : z∈w := eq ▸ (show z∈(insert b C).val from mem_insert_of_mem hz)
  simp only [w,Multiset.mem_cons] at inw
  rcases inw with rfl|rfl|h
  · exact (mem_sdiff.mp ha).2 hz
  · exact (mem_sdiff.mp ha).2 hz
  · exact zb (Multiset.eq_of_mem_replicate h)

end OMA.CycleTerminal
