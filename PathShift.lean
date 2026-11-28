import PathSuccessor

/-! Coin representations for the shifted small box in the inverse theorem. -/

open private OMA.BinaryPrefix.digits OMA.BinaryPrefix.bounded_cons
  OMA.BinaryPrefix.wt_cons from BinaryPrefix
namespace OMA.PathShift
open OMA.PathCoins OMA.PathBox Finset Arxiv.«2607.08366»

def width (k : ℕ) := 2^(k-4)
def full (k : ℕ) := 2^k-1

theorem shrunk (k : ℕ) : width k≤2^k :=
  Nat.pow_le_pow_right (by decide) (Nat.sub_le ..)

theorem slack (k s : ℕ) (lt : s<width k) : k+s≤full k := by
  by_cases sm : k≤4
  · have zero : s=0 := by simpa [width,Nat.sub_eq_zero_of_le sm] using lt
    have h := Nat.lt_two_pow_self (n:=k)
    dsimp [full]; omega
  · let j := k-4
    have e : k=j+4 := by dsimp [j]; omega
    have h := j.lt_two_pow_self
    have p : 0<2^j := by positivity
    change s<2^j at lt
    dsimp [full]; rw [e,pow_add]; norm_num; omega

private theorem pack (k c u v : ℕ) (kp : 0<k) (uv : u<2^v) (vk : v≤k) :
    ∃ w : List ℕ,Bounded k w ∧ weight w=c*2^k+u ∧ w.length≤2*c+v := by
  obtain ⟨w,wb,wv,wl,_⟩ := OMA.BinaryPrefix.digits v u uv
  let out := List.replicate (2*c) (k-1) ++ w
  refine ⟨out,?_,?_,?_⟩
  · intro j hj
    rcases List.mem_append.mp hj with high|old
    · obtain ⟨_,rfl⟩ := List.mem_replicate.mp high; omega
    · exact (wb j old).trans_le vk
  · change ((List.replicate (2*c) (k-1) ++ w).map (fun j=>2^j)).sum=_
    simp only [List.map_append,List.map_replicate,List.sum_append,List.sum_replicate_nat]
    change 2*c*2^(k-1)+weight w=_
    have e : 2^k=2*2^(k-1) := by rw [←pow_succ',show k-1+1=k by omega]
    change weight w=u at wv
    rw [e,wv]; ring
  · simp only [out,List.length_append,List.length_replicate]; omega

/-- The endpoint row is allowed two extra coins only when its own
    displacement is nonpositive. Other rows save two on positive shifts. -/
theorem row (k s a : ℕ) (small : s<width k)
    (endpt : Bool) (nz : endpt=true → 0<k) :
    ∃ w : List ℕ,Bounded k w ∧ weight w=full k+s-a+(if endpt then 2^k else 0) ∧
      w.length+(if s>a then 2 else 0)≤k+(if endpt then 2 else 0) := by
  have p : 0<2^k := by positivity
  by_cases pos : a<s
  · have four : 4≤k := by
      by_contra! low
      have h : s<1 := by simpa [width,Nat.sub_eq_zero_of_le low.le] using small
      omega
    have less : s-a-1<2^(k-4) := by change s<2^(k-4) at small; omega
    have kpos : 0<k := by omega
    cases endpt with
    | false =>
      obtain ⟨w,b,v,l⟩ := pack k 1 _ _ kpos less (Nat.sub_le ..)
      exact ⟨w,b,by simp only [full,Bool.false_eq_true,if_false,one_mul,add_zero] at v ⊢; omega,
        by simp only [Bool.false_eq_true,if_false,add_zero,gt_iff_lt,if_pos pos]; omega⟩
    | true =>
      obtain ⟨w,b,v,l⟩ := pack k 2 _ _ kpos less (Nat.sub_le ..)
      exact ⟨w,b,by simp only [full,if_true] at v ⊢; omega,
        by simp only [if_true,gt_iff_lt,if_pos pos]; omega⟩
  · have low : full k+s-a<2^k := by dsimp [full]; omega
    cases endpt with
    | false =>
      obtain ⟨w,b,v,l,_⟩ := OMA.BinaryPrefix.digits k _ low
      exact ⟨w,b,by simpa using v,by simpa [not_lt.mpr (le_of_not_gt pos)] using l⟩
    | true =>
      obtain ⟨w,b,v,l⟩ := pack k 1 _ _ (nz rfl) low le_rfl
      exact ⟨w,b,by simpa [add_comm] using v,by simpa [not_lt.mpr (le_of_not_gt pos),add_comm] using l⟩

theorem rigid {I : Type*} [Fintype I] [DecidableEq I] {N : ℕ}
    (L : I→ℕ) (x : I→ZMod N) (inj : Function.Injective (label L x))
    (ok : IsValidMod (univ.image (label L x))) (v : I→List ℕ)
    (vb : ∀ i,Bounded (L i) (v i)) (low : (∑ i,(v i).length)≤∑ i,L i)
    (hi : (∑ i,L i)≤∑ i,weight (v i))
    (mass : (∑ i,weight (v i) • x i)=∑ i,full (L i) • x i) :
    ∀ i,weight (v i)=full (L i) := by
  obtain ⟨w,wb,wv,wc⟩ := OMA.PathCoins.fill L _ v vb low hi
  have hit : (∑ i,weight (w i) • x i)=∑ i,full (L i) • x i := by simpa only [wv] using mass
  intro i; exact (wv i).symm.trans (coordinates L x inj ok w wb wc hit i)

end OMA.PathShift
