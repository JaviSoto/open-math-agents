import PathSuccessor
import PathShift
import CycleTerminal

/-! Use a long dyadic path as spare room in a squarefree replacement. -/

open private OMA.BinaryPrefix.fill OMA.BinaryPrefix.sum_bits OMA.BinaryPrefix.digits from BinaryPrefix
open private OMA.PathSuccessor.value_word from PathSuccessor
open private OMA.AffineDoubling.replace from AffineDoubling
open private OMA.LongCycle.inherited from LongCycle
open private OMA.PathShift.pack from PathShift
namespace OMA.PathReserve
open Finset Arxiv.«2607.08366» OMA.PathCoins

structure Chain {N : ℕ} (A : Finset (ZMod N)) (x : ZMod N) (L : ℕ) : Prop where
  distinct : Set.InjOn (fun j : ℕ=>2^j • x) (range L : Finset ℕ)
  inside : ∀ j<L,2^j • x∈A

def row {N : ℕ} (x : ZMod N) (L : ℕ) := (range L).image (fun j=>2^j • x)
def v {G : Type*} [AddCommMonoid G] (S : Finset G) := ∑ z∈S,z

section
variable {N L : ℕ} {A : Finset (ZMod N)} {x : ZMod N}
variable (c : Chain A x L)

include c in
theorem row_size : (row x L).card=L := (card_image_of_injOn c.distinct).trans (card_range _)

include c in
theorem row_sub : row x L⊆A := by
  intro z h; obtain ⟨j,hj,rfl⟩ := mem_image.mp h; exact c.inside j (mem_range.mp hj)

include c in
theorem order [NeZero N] (ok : IsValidMod A) : 2^L-L≤addOrderOf x :=
  OMA.DyadicDigits.lower (addOrderOf_pos x) ((OMA.AffineDoublingClass.orbit_iff 0 x (row x L)
    (row_size c) (by simp [row])).mp (OMA.LongCycle.inherited ok (row_sub c)))

include c in
theorem replace_word (ok : IsValidMod A) (T : Finset (ZMod N)) (sub : T⊆A\row x L)
    (m : Multiset (ZMod N)) (ext : ∀ z∈m,z∈A\row x L)
    (w : List ℕ) (b : Bounded L w) (budget : w.length+m.card≤L+T.card)
    (enough : A.card≤weight w) (sum : weight w • x + m.sum=(2^L-1) • x + v T) :
    m=T.val ∧ weight w≤2^L-1 := by
  classical
  let C := row x L
  have ds : Disjoint C T := disjoint_left.mpr (fun _ h ht=>(mem_sdiff.mp (sub ht)).2 h)
  have un := union_subset (row_sub c) (sub.trans sdiff_subset)
  have sz : L+T.card≤A.card := by
    have h := card_le_card un; rw [card_union_of_disjoint ds,row_size c] at h; exact h
  have bb : Bounded L w := b
  obtain ⟨u,ub,wt,len⟩ := OMA.BinaryPrefix.fill L (L+T.card-m.card) w bb (by omega) (by
    change _≤weight w; omega)
  let P : Multiset (ZMod N) := ((u.map (fun j=>2^j • x):List _) : Multiset _)
  have inside (z : ZMod N) (hz : z∈P) : z∈C := by
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hz
    exact mem_image_of_mem _ (mem_range.mpr (ub j hj))
  have plen : P.card=u.length := List.length_map ..
  have pathSum : (∑ z∈C,z)=(2^L-1) • x := by
    change (∑ z∈(range L).image (fun i=>2^i • x),z)=_
    rw [sum_image c.distinct,←sum_smul,OMA.BinaryPrefix.sum_bits]
  have eq := OMA.AffineDoubling.replace ok (C∪T) un (P+m)
    (fun z hz=>(Multiset.mem_add.mp hz).elim (fun a=>row_sub c (inside z a)) (fun a=>(mem_sdiff.mp (ext z a)).1))
    (by rw [Multiset.card_add,plen,len,card_union_of_disjoint ds,row_size c]; omega)
    (by rw [Multiset.sum_add,sum_union ds,pathSum]
        change (u.map (fun j=>2^j • x)).sum+m.sum=_
        rw [OMA.PathSuccessor.value_word,show weight u=weight w from wt]; exact sum)
  have f1 : m.filter (fun z=>z∉C)=m := Multiset.filter_eq_self.mpr (fun z hz=>(mem_sdiff.mp (ext z hz)).2)
  have f2 : T.val.filter (fun z=>z∉C)=T.val := Multiset.filter_eq_self.mpr (fun z hz=>(mem_sdiff.mp (sub hz)).2)
  have f3 : P.filter (fun z=>z∉C)=0 := Multiset.filter_eq_nil.mpr (fun z hz h=>h (inside z hz))
  have f4 : C.val.filter (fun z=>z∉C)=0 := Multiset.filter_eq_nil.mpr (fun _ h off=>off h)
  have union : (C∪T).val=C.val+T.val := by rw [←disjUnion_val _ _ ds,disjUnion_eq_union]
  have proj := congrArg (Multiset.filter (fun z=>z∉C)) eq
  rw [union,Multiset.filter_add,Multiset.filter_add,f1,f2,f3,f4,zero_add,zero_add] at proj
  refine ⟨proj,?_⟩
  have pEq : P=C.val := add_right_cancel (b:=m) (by rw [eq,union,proj])
  have nodup : (u : Multiset ℕ).Nodup := Multiset.Nodup.of_map (fun i=>2^i • x) (pEq ▸ C.nodup : P.Nodup)
  have inc : (u : Multiset ℕ)≤(range L).val :=
    (Multiset.le_iff_subset nodup).mpr (fun j hj=>mem_range.mpr (ub j hj))
  obtain ⟨a,eq⟩ := exists_add_of_le inc
  have e := congrArg OMA.DyadicDigits.value eq
  rw [OMA.DyadicDigits.value_range] at e
  change _=(Multiset.map (fun j=>2^j) ((u:Multiset ℕ)+a)).sum at e
  simp only [Multiset.map_add,Multiset.sum_add] at e
  change weight u=weight w at wt
  rw [←wt]; exact e ▸ Nat.le_add_right _ _

end
end OMA.PathReserve
