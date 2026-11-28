import PathCoins

/-! Subset-sum points outside the low simplex are all distinct on any
    valid union of disjoint doubling progressions. -/

open private OMA.BinaryPrefix.sum_bits from BinaryPrefix
namespace OMA.PathBox
open Finset OMA.PathCoins Arxiv.«2607.08366»

def label {I : Type*} (L : I→ℕ) {G : Type*} [AddMonoid G] (x : I→G)
    (a : Σ i,Fin (L i)) : G := 2^a.2.val • x a.1

private lemma counts {k : ℕ} (w : List ℕ) (b : Bounded k w) :
    let m := (w : Multiset ℕ)
    (∑ j : Fin k,m.count j.val)=w.length ∧
    (∑ j : Fin k,m.count j.val * 2^j.val)=weight w := by
  classical
  let m := (w : Multiset ℕ)
  have inside : ∀ a∈m,a∈range k := fun a ha=>mem_range.mpr (b a ha)
  have sub : m.toFinset⊆range k := fun _ h=>inside _ (Multiset.mem_toFinset.mp h)
  constructor
  · rw [Fin.sum_univ_eq_sum_range (fun j=>m.count j)]
    exact Multiset.sum_count_eq_card inside
  · rw [Fin.sum_univ_eq_sum_range (fun j=>m.count j*2^j)]
    rw [←sum_subset sub (fun j _ off=>by simp [(Multiset.count_eq_zero.mpr (by simpa using off) : m.count j=0)])]
    exact (sum_multiset_map_count m (fun j=>2^j)).symm

/-- Recover each integer coordinate of a size-n word if its actual
    residue agrees with the all-ones target. -/
theorem coordinates {I : Type*} [Fintype I] [DecidableEq I] {N : ℕ}
    (L : I→ℕ) (x : I→ZMod N) (inj : Function.Injective (label L x))
    (ok : IsValidMod (univ.image (label L x))) (w : I→List ℕ)
    (bnd : ∀ i,Bounded (L i) (w i))
    (len : (∑ i,(w i).length)=∑ i,L i)
    (hit : (∑ i,weight (w i) • x i) = ∑ i,(2^(L i)-1) • x i) :
    ∀ i,weight (w i)=2^(L i)-1 := by
  classical
  let f := label L x
  let c (a : Σ i,Fin (L i)) := ((w a.1 : Multiset ℕ)).count a.2.val
  let mult := Function.extend f c (fun _=>0)
  have evaluate (a) : mult (label L x a)=c a := inj.extend_apply c _ a
  have nc : (∑ a∈univ.image f,mult a)=(univ.image f).card := by
    rw [sum_image inj.injOn,card_image_of_injective _ inj,card_univ,Fintype.card_sigma]
    simp only [evaluate,Fintype.sum_sigma,Fintype.card_fin]
    exact (sum_congr rfl (fun i _=>(counts _ (bnd i)).1)).trans len
  have row (i : I) : (∑ j : Fin (L i),c ⟨i,j⟩ • label L x ⟨i,j⟩)=weight (w i) • x i := by
    simp only [label,←mul_smul,←sum_smul]
    exact congrArg (fun z : ℕ=>z • x i) (counts _ (bnd i)).2
  have mass : (∑ a∈univ.image f,(mult a:ZMod N)*a)=∑ a∈univ.image f,a := by
    rw [sum_image inj.injOn,sum_image inj.injOn]
    simp only [evaluate,←nsmul_eq_mul,Fintype.sum_sigma,row]
    rw [hit]
    apply sum_congr rfl; intro i _
    change (2^L i-1) • x i=∑ j : Fin (L i),2^j.val • x i
    rw [Fin.sum_univ_eq_sum_range (fun j=>2^j • x i),←sum_smul,OMA.BinaryPrefix.sum_bits]
  have all (a) : c a=1 := (evaluate a) ▸ ok mult nc mass (f a) (mem_image_of_mem _ (mem_univ _))
  intro i
  rw [←(counts _ (bnd i)).2]
  change (∑ j : Fin (L i),c ⟨i,j⟩*2^j.val)=_
  simp only [all,one_mul,Fin.sum_univ_eq_sum_range (fun j=>2^j),OMA.BinaryPrefix.sum_bits]

abbrev Box {I : Type*} (L : I→ℕ) := (i : I)→Fin (2^(L i))

/-- Every pair of distinct box inputs mapping to the same group point
    has at least one endpoint below the simplex cutoff. -/
theorem injective_high {I : Type*} [Fintype I] [DecidableEq I] {N : ℕ}
    (L : I→ℕ) (x : I→ZMod N) (inj : Function.Injective (label L x))
    (ok : IsValidMod (univ.image (label L x))) :
    Set.InjOn (fun s : Box L=>∑ i,(s i).val • x i)
      {s | (∑ i,L i)≤∑ i,(s i).val} := by
  classical
  intro s sh t th e
  let wins (s t : Box L) := ∑ i,if t i<s i then 1 else 0
  have oriented (s t : Box L) (high : (∑ i,L i)≤∑ i,(s i).val)
      (eq : (∑ i,(s i).val • x i)=∑ i,(t i).val • x i)
      (order : wins s t≤wins t s) : s=t := by
    choose w wb wv wc using (fun i=>displaced (s i).isLt (t i).isLt)
    have bound := sum_le_sum (s:=univ) (fun i _=>wc i)
    simp only [sum_add_distrib] at bound
    change (∑ i,(w i).length)+wins t s≤(∑ i,L i)+wins s t at bound
    have low : (∑ i,(w i).length)≤∑ i,L i := by omega
    have nd (i) : (t i).val≤2^L i-1 := by have h := (t i).isLt; omega
    have rel (i) : weight (w i)+(t i).val=(2^L i-1)+(s i).val := by rw [wv i]; have := nd i; omega
    have big : (∑ i,L i)≤∑ i,weight (w i) := high.trans (sum_le_sum (fun i _=>by
      have := rel i; have := nd i; omega))
    obtain ⟨v,vb,vs,vl⟩ := OMA.PathCoins.fill L _ w wb low big
    have hi : (∑ i,weight (v i) • x i)=∑ i,(2^L i-1) • x i := by
      apply add_right_cancel (b:=∑ i,(t i).val • x i)
      conv_lhs => rw [←sum_add_distrib]
      simp only [vs,←add_nsmul,rel]
      simp only [add_nsmul,sum_add_distrib,eq]
    have same := coordinates L x inj ok v vb vl hi
    funext i; apply Fin.ext
    have h := (vs i).symm.trans (same i)
    have := rel i; omega
  rcases le_total (wins s t) (wins t s) with le|le
  · exact oriented s t sh e le
  · exact (oriented t s th e.symm le).symm

private theorem low_size {I : Type*} [Fintype I] [DecidableEq I]
    (L : I→ℕ) {n : ℕ} (np : 0<n) :
    ((univ : Finset (Box L)).filter (fun s=>¬n≤∑ i,(s i).val)).card≤
      (n+Fintype.card I-1).choose (Fintype.card I) := by
  classical
  let T := (univ : Finset (Option I)).finsuppAntidiag (n-1)
  let coeff (s : Box L) (i : Option I) := i.elim (n-1-∑ j,(s j).val) (fun j=>(s j).val)
  let F (s : Box L) : Option I→₀ℕ := Finsupp.equivFunOnFinite.symm (coeff s)
  have cap := card_le_card_of_injOn (t:=T) F (s:=(univ : Finset (Box L)).filter (fun s=>¬n≤∑ i,(s i).val))
    (by
      intro s hs
      apply mem_finsuppAntidiag.mpr ⟨?_,subset_univ _⟩
      have small := (mem_filter.mp hs).2
      change (∑ i,coeff s i)=n-1
      rw [Fintype.sum_option]
      simp only [coeff,Option.elim_none,Option.elim_some]
      omega)
    (by
      intro s _ t _ eq
      funext i; apply Fin.ext
      exact DFunLike.congr_fun eq (some i))
  change _ ≤ (n+Fintype.card I-1).choose (Fintype.card I)
  have count : T.card=(n+Fintype.card I-1).choose (Fintype.card I) := by
    rw [show T=(univ : Finset (Option I)).finsuppAntidiag (n-1) from rfl,
      card_finsuppAntidiag_nat_eq_choose,card_univ,Fintype.card_option]
    rw [show Fintype.card I+1+(n-1)-1=n+Fintype.card I-1 by omega]
    have symm := Nat.choose_symm (show Fintype.card I≤n+Fintype.card I-1 by omega)
    rwa [show n+Fintype.card I-1-Fintype.card I=n-1 by omega] at symm
  exact cap.trans_eq count

/-- For h disjoint dyadic chains with a total of n valid labels,
    the modulus misses 2^n by at most a stars-and-bars term. -/
theorem lower {I : Type*} [Fintype I] [DecidableEq I] {N : ℕ} [NeZero N]
    (L : I→ℕ) (x : I→ZMod N) (inj : Function.Injective (label L x))
    (ok : IsValidMod (univ.image (label L x))) (np : 0<∑ i,L i) :
    2^(∑ i,L i)≤N+((∑ i,L i)+Fintype.card I-1).choose (Fintype.card I) := by
  classical
  let cut (s : Box L) := (∑ i,L i)≤∑ i,(s i).val
  let eval (s : Box L) := ∑ i,(s i).val • x i
  let S := (univ : Finset (Box L)).filter cut
  have hi : S.card≤N := by
    have injs : Set.InjOn eval (S : Set _) :=
      (injective_high L x inj ok).mono (fun s h=>(mem_filter.mp h).2)
    have le := card_le_univ (S.image eval)
    rwa [card_image_of_injOn injs,ZMod.card] at le
  have lo := low_size L np
  have part := card_filter_add_card_filter_not (s:=(univ : Finset (Box L))) cut
  have vol : Fintype.card (Box L)=2^(∑ i,L i) := by
    rw [Fintype.card_pi]; simp only [Fintype.card_fin,prod_pow_eq_pow_sum]
  rw [card_univ,vol] at part
  change S.card+_=_ at part
  change ((univ : Finset (Box L)).filter (fun s=>¬cut s)).card≤_ at lo
  omega

end OMA.PathBox
