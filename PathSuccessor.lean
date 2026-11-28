import PathBox

/-! A represented successor of a sufficiently long doubling path is
    either zero or one of the actual labels. -/

open private OMA.AffineDoubling.replace from AffineDoubling
open private OMA.BinaryPrefix.fill OMA.BinaryPrefix.sum_bits from BinaryPrefix
namespace OMA.PathSuccessor
open Finset OMA.PathCoins OMA.PathBox Arxiv.«2607.08366»

private lemma value_word {G : Type*} [AddCommMonoid G] (x : G) (w : List ℕ) :
    (w.map (fun j=>2^j • x)).sum=weight w • x := by
  induction w with
  | nil => exact (zero_nsmul x).symm
  | cons a w ih =>
    change 2^a • x+(w.map (fun j=>2^j • x)).sum=(2^a+weight w) • x
    rw [ih,add_nsmul]

/-- Every subset representing the next term of a chain of coin capacity
    at least |A| has at most one member. -/
theorem subset_succ {N k : ℕ} {A : Finset (ZMod N)} (ok : IsValidMod A)
    (x : ZMod N) (hk : 0<k) (large : A.card≤2^k)
    (chain : ∀ j<k,2^j • x∈A) (T : Finset (ZMod N)) (sub : T⊆A)
    (shape : (∑ a∈T,a)=2^k • x) : T.card≤1 := by
  classical
  by_contra! two
  let base := [k-1,k-1]
  have v : weight base=2^k := by
    change 2^(k-1)+(2^(k-1)+0)=2^k
    conv_rhs => rw [show k=k-1+1 by omega,pow_succ]
    omega
  have bounded : Bounded k base := by
    intro j hj
    simp only [base,List.mem_cons,List.not_mem_nil,or_false,or_self] at hj
    omega
  obtain ⟨w,bnd,wt,len⟩ := OMA.BinaryPrefix.fill k T.card base bounded
    (by change 2≤T.card; omega) (by change T.card≤weight base; rw [v]; exact (card_le_card sub).trans large)
  have wt' : weight w=2^k := wt.trans v
  let m : Multiset (ZMod N) := ((w.map (fun j=>2^j • x) : List _) : Multiset _)
  have same := OMA.AffineDoubling.replace ok T sub m (by
    intro a ha; obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ha; exact chain _ (bnd _ hj))
    ((List.length_map ..).trans len) ((value_word x w).trans (by rw [wt',shape]))
  have nd := T.nodup
  rw [←same] at nd
  have wn : (w : Multiset ℕ).Nodup := Multiset.Nodup.of_map (fun j=>2^j • x) nd
  have inc : (w : Multiset ℕ)≤(range k).val :=
    (Multiset.le_iff_subset wn).mpr (fun j hj=>mem_range.mpr (bnd j hj))
  obtain ⟨u,eu⟩ := exists_add_of_le inc
  have lim : weight w≤2^k-1 := by
    have e := congrArg OMA.DyadicDigits.value eu
    rw [OMA.DyadicDigits.value_range] at e
    change _=(Multiset.map (fun j=>2^j) ((w:Multiset ℕ)+u)).sum at e
    simp only [Multiset.map_add,Multiset.sum_add] at e
    exact e ▸ Nat.le_add_right _ _
  have pos : 0<2^k := by positivity
  omega

end OMA.PathSuccessor
