import PathBox

/-! Rerouting between intersecting endpoints of disjoint doubling rows. -/

namespace OMA.PathSplice
open Finset OMA.PathBox

theorem label_mem {I G : Type*} [Fintype I] [AddMonoid G] [DecidableEq G] (L : I→ℕ) (x : I→G)
    (i : I) {j : ℕ} (le : j<L i) : 2^j • x i∈univ.image (label L x) :=
  mem_image.mpr ⟨⟨i,⟨j,le⟩⟩,mem_univ _,rfl⟩

theorem size {I G : Type*} [Fintype I] [AddMonoid G] [DecidableEq G] (L : I→ℕ) (x : I→G)
    (inj : Function.Injective (label L x)) : (univ.image (label L x)).card=∑ i,L i := by
  rw [card_image_of_injective _ inj,card_univ,Fintype.card_sigma]; simp

theorem splice {I G : Type*} [Fintype I] [DecidableEq I] [AddMonoid G] [DecidableEq G]
    (L : I→ℕ) (x : I→G) (inj : Function.Injective (label L x)) {J K : I} (diff : J≠K)
    {a : ℕ} (lt : a<L K) (join : 2^L J • x J=2^a • x K) :
    ∃ M : I→ℕ, L J<M J ∧ (∑ i,M i)=∑ i,L i ∧
      univ.image (label M x)=univ.image (label L x) ∧ Function.Injective (label M x) := by
  classical
  let delta := L K-a
  let M (i : I) := if i=J then L i+delta else if i=K then a else L i
  have mj : M J=L J+delta := by simp [M]
  have mk : M K=a := by simp [M,diff.symm]
  have dpos : 0<delta := by dsimp [delta]; omega
  have dsum : a+delta=L K := by dsimp [delta]; omega
  have same : (∑ i,M i)=∑ i,L i := by
    have point (i : I) : M i+(if i=K then delta else 0)=L i+(if i=J then delta else 0) := by
      by_cases ij : i=J
      · subst i; simp [mj,diff]
      by_cases ik : i=K
      · subst i; simp [mk,diff.symm,dsum]
      · simp [M,ij,ik]
    have := sum_congr (s₁:=univ) rfl (fun i _=>point i)
    simp only [sum_add_distrib,sum_ite_eq',mem_univ,if_true] at this
    omega
  have sub : univ.image (label L x)⊆univ.image (label M x) := by
    intro z hz
    obtain ⟨⟨i,j⟩,_,rfl⟩ := mem_image.mp hz
    change 2^j.val • x i∈_
    by_cases ik : i=K
    · subst i
      by_cases before : j.val<a
      · exact label_mem M x K (mk ▸ before)
      · have shorter : L J+(j.val-a)<M J := by rw [mj]; have := j.isLt; omega
        have hit : 2^(L J+(j.val-a)) • x J=2^j.val • x K := by
          rw [add_comm,pow_add,mul_smul,join,←mul_smul,←pow_add,show j.val-a+a=j.val by omega]
        exact hit ▸ label_mem M x J shorter
    · apply label_mem
      have old := j.isLt
      by_cases ij : i=J
      · subst i; rw [mj]; omega
      · simpa only [M,if_neg ij,if_neg ik] using old
  have dom : (univ : Finset (Σ i,Fin (M i))).card=∑ i,L i := by
    rw [card_univ,Fintype.card_sigma]; simpa using same
  have eq : univ.image (label L x)=univ.image (label M x) := by
    apply eq_of_subset_of_card_le sub
    exact (card_image_le.trans_eq dom).trans_eq (size L x inj).symm
  refine ⟨M,by rw [mj]; omega,same,eq.symm,?_⟩
  apply Set.injOn_univ.mp
  rw [←coe_univ (α:=Σ i,Fin (M i)),←card_image_iff,←eq,dom,size L x inj]

/-- Among all length-h covers of the same set, choose a row that cannot
    be lengthened by appending the tail of another row. -/
theorem maximal {I G : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    [AddMonoid G] [DecidableEq G] (L : I→ℕ) (x : I→G)
    (inj : Function.Injective (label L x)) :
    ∃ (M : I→ℕ) (J : I), Function.Injective (label M x) ∧
      univ.image (label M x)=univ.image (label L x) ∧ (∑ i,M i)=∑ i,L i ∧
      (∀ i,M i≤M J) ∧
      ∀ i j, j<M i → 2^M J • x J=2^j • x i → i=J := by
  classical
  let A := univ.image (label L x)
  let lens := (range (A.card+1)).filter (fun l=>∃ (M : I→ℕ) (i:I),
    Function.Injective (label M x) ∧ univ.image (label M x)=A ∧ M i=l)
  have mem (M : I→ℕ) (i : I) (mi : Function.Injective (label M x)) (eq : univ.image (label M x)=A) :
      M i∈lens := by
    have total := size M x mi
    rw [eq] at total
    have le : M i≤∑ k,M k := single_le_sum (fun _ _=>Nat.zero_le _) (mem_univ i)
    exact mem_filter.mpr ⟨mem_range.mpr (by omega),M,i,mi,eq,rfl⟩
  have non : lens.Nonempty := ⟨_,mem L (Classical.arbitrary I) inj rfl⟩
  obtain ⟨M,J,mi,eq,e⟩ := (mem_filter.mp (lens.max'_mem non)).2
  refine ⟨M,J,mi,eq,(size M x mi).symm.trans ((congrArg Finset.card eq).trans (size L x inj)),
    fun i=>e ▸ lens.le_max' _ (mem M i mi eq),?_⟩
  intro i j ij join
  by_contra diff
  obtain ⟨W,gt,_,same,wi⟩ := splice M x mi (Ne.symm diff) ij join
  have le := lens.le_max' _ (mem W J wi (same.trans eq))
  omega

end OMA.PathSplice
