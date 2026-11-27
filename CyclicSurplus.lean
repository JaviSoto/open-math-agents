import WeightedModulus

/-! A lower bound beyond the Boolean-box bound for unique all-ones multiset
sums in cyclic groups. A tie under doubling one label occupies a proper
subcube; distinct such subcubes cannot have neighboring vertices. -/

namespace OMA.CyclicSurplus
open Finset

private noncomputable def density {α : Type*} (u v : Finset α) : ℝ := (1/2:ℝ)^(u.card+v.card)

/-- Bollobás-type half-cube bound with variable support sizes. Slicing one
coordinate suffices because proper faces at distance at least two remain
separated in each hyperplane. -/
theorem separated_half {α I : Type*} [DecidableEq α] [DecidableEq I]
    (S : Finset α) (K : Finset I) (U V : I→Finset α)
    (inside : ∀ i∈K,U i⊆S ∧ V i⊆S)
    (consistent : ∀ i∈K,Disjoint (U i) (V i))
    (proper : ∀ i∈K,(U i ∪ V i).Nonempty)
    (cross : ∀ i∈K,∀ j∈K,i≠j → ((U i)∩(V j)).Nonempty) :
    (∑ i∈K,density (U i) (V i))≤1/2 := by
  classical
  induction S using Finset.induction_on generalizing K U V with
  | empty =>
    have ke : K=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro i hi
      have tmp := inside i hi
      simp only [subset_empty] at tmp
      simpa [tmp.1,tmp.2] using proper i hi
    simp [ke]
  | insert a S ha ih =>
    by_cases one : ∃ i∈K, U i=∅ ∨ V i=∅
    · obtain ⟨i,hi,one⟩ := one
      have eq : K={i} := by
        apply eq_singleton_iff_unique_mem.mpr ⟨hi,?_⟩
        intro j hj
        by_contra ne
        rcases one with e|e
        · simpa [e] using cross i hi j hj (Ne.symm ne)
        · simpa [e] using cross j hj i hi ne
      obtain ⟨z,hz⟩ := proper i hi
      have pos : 0 < (U i).card+(V i).card := by
        rcases mem_union.mp hz with h|h
        · have := card_pos.mpr ⟨z,h⟩; omega
        · have := card_pos.mpr ⟨z,h⟩; omega
      rw [eq,sum_singleton,density]
      simpa using pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ)≤1) pos
    have both (i : I) (hi : i∈K) : (U i).Nonempty ∧ (V i).Nonempty := by
      exact ⟨nonempty_iff_ne_empty.mpr (fun e=>one ⟨i,hi,.inl e⟩),
        nonempty_iff_ne_empty.mpr (fun e=>one ⟨i,hi,.inr e⟩)⟩
    let u (i : I) := (U i).erase a
    let v (i : I) := (V i).erase a
    have inside' (i : I) (hi : i∈K) : u i⊆S ∧ v i⊆S := by
      obtain ⟨hu,hv⟩ := inside i hi
      exact ⟨fun x hx => (mem_insert.mp (hu (mem_erase.mp hx).2)).resolve_left (mem_erase.mp hx).1,
        fun x hx => (mem_insert.mp (hv (mem_erase.mp hx).2)).resolve_left (mem_erase.mp hx).1⟩
    have step (L : Finset I) (sub : L⊆K)
        (side : (∀ i∈L,a∉U i) ∨ (∀ i∈L,a∉V i)) :
        (∑ i∈L,density (u i) (v i))≤1/2 := by
      apply ih L u v (fun i hi => inside' i (sub hi))
        (fun i hi => (consistent i (sub hi)).mono (erase_subset ..) (erase_subset ..))
      · intro i hi
        obtain ⟨hu,hv⟩ := both i (sub hi)
        rcases side with e|e
        · exact hu.mono (by simp [u,erase_eq_of_notMem (e i hi)])
        · exact hv.mono (by simp [v,erase_eq_of_notMem (e i hi)])
      · intro i hi j hj ne
        obtain ⟨z,hz⟩ := cross i (sub hi) j (sub hj) ne
        rcases mem_inter.mp hz with ⟨hu,hv⟩
        have nz : z≠a := by
          rintro rfl
          rcases side with e|e
          · exact e i hi hu
          · exact e j hj hv
        exact ⟨z,mem_inter.mpr ⟨mem_erase.mpr ⟨nz,hu⟩,mem_erase.mpr ⟨nz,hv⟩⟩⟩
    have zero := step (K.filter (fun i=>a∉U i)) (filter_subset ..) (.inl (fun _ hi=>(mem_filter.mp hi).2))
    have one := step (K.filter (fun i=>a∉V i)) (filter_subset ..) (.inr (fun _ hi=>(mem_filter.mp hi).2))
    rw [sum_filter] at zero one
    have double : (∑ i∈K,((if a∉U i then density (u i) (v i) else 0)+
          (if a∉V i then density (u i) (v i) else 0)))=2*(∑ i∈K,density (U i) (V i)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i hi
      by_cases hu : a∈U i
      · have hv := Finset.disjoint_left.mp (consistent i hi) hu
        simp only [u,v,hu,hv,not_true_eq_false,if_false,not_false_eq_true,if_true,
          zero_add,erase_eq_of_notMem hv,density]
        have count := card_erase_add_one hu
        rw [←count,add_right_comm,pow_succ]
        ring
      by_cases hv : a∈V i
      · simp only [u,v,hu,hv,not_true_eq_false,if_false,not_false_eq_true,if_true,
          add_zero,erase_eq_of_notMem hu,density]
        have count := card_erase_add_one hv
        rw [←count,←add_assoc,pow_succ]
        ring
      simp [hu,hv,u,v,two_mul]
    rw [sum_add_distrib] at double
    linarith

section Masks
variable {α G : Type*} [Fintype α] [DecidableEq α] [AddCommGroup G]

private def bit (A : Finset α) (i : α) : ℕ := if i∈A then 1 else 0

private lemma bit_size (A : Finset α) : (∑ i,bit A i)=A.card := by simp [bit]

private lemma bit_sum (A : Finset α) (g : α→G) :
    (∑ i,bit A i • g i)=∑ i∈A,g i := by simp [bit,ite_smul]

private lemma squarefree (g : α→G) (h : OMA.WeightedModulus.Valid 1 (fun _=>1) g)
    (A : Finset α) (c : α→ℕ) (len : (∑ i,c i)≤A.card+1)
    (hit : (∑ i,c i • g i)=∑ i∈A,g i) : c=bit A := by
  classical
  let x (i : α) := c i + bit (univ\A) i
  have budget : (∑ i,x i)≤1+∑ _ : α,(1:ℕ) := by
    simp only [x,sum_add_distrib,bit_size,card_univ_sdiff,sum_const_nat,card_univ,mul_one]
    have := A.card_le_univ
    omega
  have mass : (∑ i,x i • g i)=∑ i,(1:ℕ) • g i := by
    simp only [x,add_nsmul,sum_add_distrib,bit_sum,hit,one_smul]
    exact sum_add_sum_compl A g
  have eq := h x budget mass
  funext i
  have t := congrFun eq i
  by_cases hi : i∈A <;> simpa [x,bit,hi] using t

private lemma masks_injective (g : α→G) (h : OMA.WeightedModulus.Valid 1 (fun _=>1) g) :
    Function.Injective (fun A : Finset α=>∑ i∈A,g i) := by
  intro A B eq
  have ordered (A B : Finset α) (mass : (∑ i∈A,g i)=∑ i∈B,g i) (len : A.card≤B.card) : A=B := by
    have t := squarefree g h B (bit A) (by rw [bit_size]; omega) ((bit_sum A g).trans mass)
    ext i
    have u := congrFun t i
    by_cases ha : i∈A <;> by_cases hb : i∈B <;> simp_all [bit]
  rcases le_total A.card B.card with le|le
  · exact ordered A B eq le
  · exact (ordered B A eq.symm le).symm

/-- For fixed nonzero translation, two different reduced ties conflict in
    both directions. If one crossing were empty, it would represent a
    squarefree multiset by a different multiset of the same length. -/
private lemma ties_cross (g : α→G) (h : OMA.WeightedModulus.Valid 1 (fun _=>1) g)
    (U V U' V' : Finset α) (dis : Disjoint U V) (dis' : Disjoint U' V')
    (size : U.card=V.card) (size' : U'.card=V'.card)
    (value : (∑ i∈U,g i)+(∑ i∈V',g i)=(∑ i∈U',g i)+(∑ i∈V,g i))
    (different : (U,V)≠(U',V')) : (U∩V').Nonempty := by
  classical
  by_contra none
  have across : Disjoint U V' := Finset.disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp none)
  let c (i : α) := bit U' i+bit V i
  have len : (∑ i,c i)≤(U∪V').card+1 := by
    rw [card_union_of_disjoint across]
    simp only [c,sum_add_distrib,bit_size]
    omega
  have hit : (∑ i,c i • g i)=∑ i∈U∪V',g i := by
    simpa only [c,add_nsmul,sum_add_distrib,bit_sum,sum_union across] using value.symm
  have equality := squarefree g h (U∪V') c len hit
  apply different
  have bits (i : α) : (i∈U ↔ i∈U') ∧ (i∈V ↔ i∈V') := by
    have e := congrFun equality i
    have d : i∈U → i∉V := fun hi=>Finset.disjoint_left.mp dis hi
    have d' : i∈U' → i∉V' := fun hi=>Finset.disjoint_left.mp dis' hi
    have a : i∈U → i∉V' := fun hi=>Finset.disjoint_left.mp across hi
    simp only [c,bit,mem_union] at e
    by_cases u : i∈U <;> by_cases v : i∈V <;> by_cases u' : i∈U' <;> by_cases v' : i∈V' <;>
      simp_all
  exact Prod.ext (Finset.ext fun i => (bits i).1) (Finset.ext fun i => (bits i).2)

omit [Fintype α] in
private lemma reduced_sum (g : α→G) (A B : Finset α) :
    (∑ i∈A\B,g i)+(∑ i∈A∩B,g i)=∑ i∈A,g i := by
  rw [←sum_union (disjoint_sdiff_inter A B),sdiff_union_inter]

/-- At most half of a Boolean box can be translated inside the same layer
    by a fixed nonzero group element, assuming unique all-ones sums. -/
theorem ties_half (g : α→G) (h : OMA.WeightedModulus.Valid 1 (fun _=>1) g)
    (S : Finset α) (z : G) (nz : z≠0) (H : Finset (Finset α))
    (ties : ∀ A∈H,A⊆S ∧ ∃ B⊆S, A.card=B.card ∧ (∑ i∈B,g i)=z+∑ i∈A,g i) :
    2*H.card≤2^S.card := by
  classical
  let K : Finset (Finset α × Finset α) := (S.powerset ×ˢ S.powerset).filter fun p =>
    Disjoint p.1 p.2 ∧ p.1.card=p.2.card ∧ (∑ i∈p.2,g i)=z+∑ i∈p.1,g i
  have info (p : Finset α × Finset α) : p∈K ↔ p.1⊆S ∧ p.2⊆S ∧ Disjoint p.1 p.2 ∧
      p.1.card=p.2.card ∧ (∑ i∈p.2,g i)=z+∑ i∈p.1,g i := by
    obtain ⟨u,v⟩ := p
    simp only [K,mem_filter,mem_product,mem_powerset,and_assoc]
  have half := separated_half S K Prod.fst Prod.snd (fun p hp=>⟨((info p).mp hp).1,((info p).mp hp).2.1⟩)
    (fun p hp=>((info p).mp hp).2.2.1) (by
      intro p hp
      obtain ⟨_,_,_,_,mass⟩ := (info p).mp hp
      by_contra no
      simp only [not_nonempty_iff_eq_empty,union_eq_empty] at no
      exact nz (by simpa [no.1,no.2] using mass.symm))
    (by
      intro p hp q hq ne
      obtain ⟨_,_,dp,cp,ep⟩ := (info p).mp hp
      obtain ⟨_,_,dq,cq,eq⟩ := (info q).mp hq
      exact ties_cross g h p.1 p.2 q.1 q.2 dp dq cp cq (by rw [ep,eq]; abel) ne)
  let box (p : Finset α × Finset α) := Icc p.1 (S\p.2)
  have cover : H ⊆ K.biUnion box := by
    intro A hA
    obtain ⟨sub,B,sub',same,mass⟩ := ties A hA
    let p : Finset α × Finset α := (A\B,B\A)
    apply mem_biUnion.mpr ⟨p,(info p).mpr ?_,?_⟩
    · refine ⟨sdiff_subset.trans sub,sdiff_subset.trans sub',?_,card_sdiff_comm same,?_⟩
      · exact disjoint_sdiff_self_left.mono_right sdiff_subset
      · apply add_right_cancel (b:=∑ i∈A∩B,g i)
        change (∑ i∈B\A,g i)+_=(z+∑ i∈A\B,g i)+_
        rw [add_assoc,reduced_sum g A B,inter_comm A B,reduced_sum g B A,mass]
    · exact mem_Icc.mpr ⟨sdiff_subset,fun i hi => mem_sdiff.mpr ⟨sub hi,fun hb=>(mem_sdiff.mp hb).2 hi⟩⟩
  have card (p : Finset α × Finset α) (hp : p∈K) :
      ((box p).card:ℝ)=2^S.card*density p.1 p.2 := by
    obtain ⟨us,vs,dis,_,_⟩ := (info p).mp hp
    have sub : p.1⊆S\p.2 := fun i hi => mem_sdiff.mpr ⟨us hi,disjoint_left.mp dis hi⟩
    have le : p.1.card+p.2.card≤S.card := by
      rw [←card_union_of_disjoint dis]
      exact card_le_card (union_subset us vs)
    rw [show (box p).card=2^((S.card-p.2.card)-p.1.card) by
      dsimp only [box]
      rw [card_Icc_finset sub,card_sdiff_of_subset vs]]
    have exp : S.card-p.2.card-p.1.card+(p.1.card+p.2.card)=S.card := by omega
    simp only [Nat.cast_pow,Nat.cast_ofNat,density,one_div,inv_pow]
    apply (eq_div_iff (pow_ne_zero _ (by norm_num : (2:ℝ)≠0))).mpr
    rw [←pow_add,exp]
  have bound := (card_le_card cover).trans (card_biUnion_le)
  have realbound : (H.card:ℝ)≤∑ p∈K,((box p).card:ℝ) := by exact_mod_cast bound
  rw [sum_congr rfl card,←mul_sum] at realbound
  have endBound := mul_le_mul_of_nonneg_left half (by positivity : (0:ℝ)≤2^S.card)
  have final : (2:ℝ)*H.card≤2^S.card := by linarith
  exact_mod_cast final

private lemma shifted_subset (g : α→G) (h : OMA.WeightedModulus.Valid 1 (fun _=>1) g)
    (i : α) (A B : Finset α) (ni : i∉A)
    (hit : (∑ j∈B,g j)=2 • g i+∑ j∈A,g j) : i∉B ∧ B.card≤A.card := by
  classical
  constructor
  · intro hi
    have eq : (∑ j∈insert i A,g j)=∑ j∈B.erase i,g j := by
      apply add_right_cancel (b:=g i)
      rw [sum_erase_add _ _ hi,hit,sum_insert ni,two_nsmul]
      abel
    have bad := masks_injective g h eq
    have yes : i∈insert i A := mem_insert_self ..
    rw [bad] at yes
    exact (notMem_erase i B) yes
  · by_contra! lt
    let c (j : α) := bit A j+2*bit {i} j
    have len : (∑ j,c j)≤B.card+1 := by
      simp only [c,sum_add_distrib,←mul_sum,bit_size,card_singleton,mul_one]
      omega
    have mass : (∑ j,c j • g j)=∑ j∈B,g j := by
      simp only [c,add_nsmul,sum_add_distrib,←smul_smul,bit_sum,←smul_sum]
      simpa only [bit_sum,sum_singleton,add_comm] using hit.symm
    have e := congrFun (squarefree g h B c len mass) i
    by_cases ib : i∈B <;> simp [c,bit,ni,ib] at e

/-- The partial downwards translation on the remaining Boolean cube.
    Every missing domain point lies above the ordinary box bound in the
    group count. -/
theorem partial_shift [Fintype G] (g : α→G) (h : OMA.WeightedModulus.Valid 1 (fun _=>1) g)
    (i : α) (nz : 2 • g i≠0) :
    let S := univ.erase i
    ∃ (H : Finset (Finset α)) (f : Finset α→Finset α),
      H⊆S.powerset ∧ Set.InjOn f (H : Set (Finset α)) ∧
      (∀ A∈H,f A⊆S ∧ (f A).card≤A.card) ∧
      2*(H.filter (fun A => (f A).card=A.card)).card ≤ 2^S.card ∧
      2^(Fintype.card α)+(2^S.card-H.card)≤Fintype.card G ∧
      (∀ A∈H,(∑ j∈f A,g j)=2 • g i+∑ j∈A,g j) := by
  classical
  let S := (univ : Finset α).erase i
  let value (A : Finset α) := ∑ j∈A,g j
  let shift (A : Finset α) := 2 • g i+value A
  let H := S.powerset.filter (fun A=>∃ B⊆S,value B=shift A)
  have valInj : Function.Injective value := masks_injective g h
  have shiftInj : Function.Injective shift := fun _ _ eq=>valInj (add_left_cancel eq)
  have sub : H⊆S.powerset := filter_subset ..
  have get (A : Finset α) (mem : A∈H) := (mem_filter.mp mem).2
  let f (A : Finset α) := if ha : A∈H then (get A ha).choose else ∅
  have fp (A : Finset α) (ha : A∈H) : f A⊆S ∧ value (f A)=shift A := by
    simpa [f,ha] using (get A ha).choose_spec
  have down (A : Finset α) (ha : A∈H) : f A⊆S ∧ (f A).card≤A.card := by
    exact ⟨(fp A ha).1,(shifted_subset g h i A (f A)
      (fun hi=>notMem_erase i univ ((mem_powerset.mp (sub ha)) hi)) (fp A ha).2).2⟩
  refine ⟨H,f,sub,?_,down,?_,?_,fun A ha=>(fp A ha).2⟩
  · intro A ha B hb eq
    apply shiftInj
    exact (fp A ha).2.symm.trans ((congrArg value eq).trans (fp B hb).2)
  · apply ties_half g h S (2 • g i) nz
    intro A ha
    obtain ⟨mem,eq⟩ := mem_filter.mp ha
    exact ⟨mem_powerset.mp (sub mem),f A,(fp A mem).1,eq.symm,(fp A mem).2⟩
  · let full := (univ : Finset (Finset α)).image value
    let extra := (S.powerset\H).image shift
    have dis : Disjoint full extra := by
      apply disjoint_left.mpr
      intro y hy ey
      obtain ⟨B,_,rfl⟩ := mem_image.mp hy
      obtain ⟨A,hm,eq⟩ := mem_image.mp ey
      obtain ⟨subA,missing⟩ := mem_sdiff.mp hm
      have na : i∉A := fun hi=>notMem_erase i univ ((mem_powerset.mp subA) hi)
      have nb := (shifted_subset g h i A B na eq.symm).1
      apply missing
      exact mem_filter.mpr ⟨subA,B,fun j hj=>mem_erase.mpr ⟨fun e=>nb (e ▸ hj),mem_univ _⟩,eq.symm⟩
    have eq1 : full.card=2^(Fintype.card α) := by
      rw [show full.card=(univ.image value).card by rfl,card_image_of_injective _ valInj]
      simp
    have eq2 : extra.card=2^S.card-H.card := by
      rw [show extra.card=((S.powerset\H).image shift).card by rfl,card_image_of_injective _ shiftInj,
        card_sdiff_of_subset sub,card_powerset]
    rw [←eq1,←eq2,←card_union_of_disjoint dis]
    exact card_le_univ _

/-- Unless there is at most one nonpivot label, not every label difference
    can lie in the two-torsion subgroup of a finite cyclic group. -/
theorem nontrivial_double [Fintype G] [IsAddCyclic G] (g : α→G)
    (h : OMA.WeightedModulus.Valid 1 (fun _=>1) g) (hd : 2≤Fintype.card α) :
    ∃ i,2 • g i≠0 := by
  classical
  by_contra! no
  let T := (univ : Finset G).filter fun z => (2:ℕ) • z=0
  let F (A : Finset α) : T := ⟨∑ i∈A,g i,mem_filter.mpr
    ⟨mem_univ _,by simp only [smul_sum,no,sum_const_zero]⟩⟩
  have inj : Function.Injective F := fun _ _ eq => masks_injective g h (congrArg Subtype.val eq)
  have lo := Fintype.card_le_of_injective F inj
  simp only [Fintype.card_finset,Fintype.card_coe] at lo
  have up : T.card≤2 := IsAddCyclic.card_nsmul_eq_zero_le (by decide : 0 < 2)
  have bigger : (2:ℕ)^2≤2^(Fintype.card α) := Nat.pow_le_pow_right (by decide) hd
  omega

end Masks

section Potential
variable {α G : Type*} [Fintype α] [DecidableEq α] [AddCommGroup G]

/-- A capped word distance. The extra dummy length makes the function total
even on cosets that cannot be reached by the given labels. -/
private def Possible (g : α→G) (x : G) (l : ℕ) : Prop :=
  l=Fintype.card α+2 ∨ ∃ c : α→ℕ, (∑ i,c i)=l ∧ (∑ i,c i • g i)=x

omit [DecidableEq α] in
private lemma exists_length (g : α→G) (x : G) : ∃ l,Possible g x l := ⟨_,Or.inl rfl⟩

private noncomputable def length (g : α→G) (x : G) : ℕ := by
  classical
  exact Nat.find (exists_length g x)

omit [DecidableEq α] in
private lemma length_spec (g : α→G) (x : G) : Possible g x (length g x) := by
  classical
  exact Nat.find_spec (exists_length g x)

omit [DecidableEq α] in
private lemma length_le (g : α→G) {x : G} {l : ℕ} (h : Possible g x l) : length g x≤l := by
  classical
  exact Nat.find_min' (exists_length g x) h

private lemma increase (g : α→G) (x : G) (i : α) : length g (x+g i)≤length g x+1 := by
  rcases length_spec g x with top|⟨c,size,sum⟩
  · have le : length g (x+g i)≤Fintype.card α+2 := length_le g (.inl rfl)
    omega
  apply length_le g (.inr ⟨fun j=>c j+bit {i} j,?_,?_⟩)
  · simp only [sum_add_distrib,bit_size,card_singleton,size]
  · simp only [add_nsmul,sum_add_distrib,bit_sum,sum_singleton,sum]

private lemma length_subset (g : α→G) (h : OMA.WeightedModulus.Valid 1 (fun _=>1) g)
    (A : Finset α) : length g (∑ i∈A,g i)=A.card := by
  have le : length g (∑ i∈A,g i)≤A.card := length_le g (.inr ⟨bit A,bit_size A,bit_sum A g⟩)
  rcases length_spec g (∑ i∈A,g i) with top|⟨c,size,mass⟩
  · have := A.card_le_univ
    omega
  have eq := squarefree g h A c (by omega) mass
  rwa [eq,bit_size,eq_comm] at size

private lemma predecessor (g : α→G) (h : OMA.WeightedModulus.Valid 1 (fun _=>1) g)
    (i : α) (A : Finset α) (hi : i∉A) : A.card+1≤length g ((∑ j∈A,g j)-g i) := by
  rcases length_spec g ((∑ j∈A,g j)-g i) with top|⟨c,size,mass⟩
  · have := A.card_le_univ
    omega
  by_contra! small
  let y (j : α) := c j+bit {i} j
  have elen : (∑ j,y j)≤A.card+1 := by
    simp only [y,sum_add_distrib,bit_size,card_singleton,size]
    omega
  have sum : (∑ j,y j • g j)=∑ j∈A,g j := by
    simp only [y,add_nsmul,sum_add_distrib,bit_sum,sum_singleton,mass,sub_add_cancel]
  have e := congrFun (squarefree g h A y elen sum) i
  simp [y,bit,hi] at e

/-- The quantitative potential argument is exposed without constructing any
first-return maps. The baseline predecessor set has one point per subset;
the strictly descending shifts contribute an extra unit of drop. -/
theorem potential_sets [Fintype G] [DecidableEq G] (g : α→G)
    (h : OMA.WeightedModulus.Valid 1 (fun _=>1) g) (i : α) (nz : 2 • g i≠0) :
    let S := univ.erase i
    ∃ (P : G→ℤ) (D K : Finset G) (holes : ℕ),
      K⊆D ∧ (∀ x,P (x+g i)≤P x+1) ∧
      (∀ x∈D,P (x+g i)+1≤P x) ∧ (∀ x∈K,P (x+g i)+2≤P x) ∧
      D.card=2^S.card ∧ 2^S.card≤2*(K.card+holes) ∧
      2^Fintype.card α+holes≤Fintype.card G := by
  classical
  let S := (univ : Finset α).erase i
  let val (A : Finset α) := ∑ j∈A,g j
  have vinj : Function.Injective val := masks_injective g h
  let prev (A : Finset α) := val A-g i
  have pinj : Function.Injective prev := fun _ _ eq=>vinj (sub_left_inj.mp eq)
  let D := S.powerset.image prev
  obtain ⟨H,f,sub,inj,down,ties,space,shift⟩ := partial_shift g h i nz
  let strict := H.filter (fun A => (f A).card<A.card)
  let T := strict.image f
  let K := T.image prev
  let P (x : G) : ℤ := length g x
  have hiS (A : Finset α) (su : A⊆S) : i∉A := fun hi=>notMem_erase i univ (su hi)
  have di : T⊆S.powerset := by
    intro B hb
    obtain ⟨A,ha,rfl⟩ := mem_image.mp hb
    exact mem_powerset.mpr (down A (mem_filter.mp ha).1).1
  refine ⟨P,D,K,2^S.card-H.card,image_subset_image di,?_,?_,?_,?_,?_,space⟩
  · intro x
    dsimp only [P]
    exact_mod_cast increase g x i
  · intro x hx
    obtain ⟨A,ha,rfl⟩ := mem_image.mp hx
    change (length g (val A-g i+g i):ℤ)+1≤length g (val A-g i)
    rw [sub_add_cancel,length_subset g h]
    exact_mod_cast predecessor g h i A (hiS A (mem_powerset.mp ha))
  · intro x hx
    obtain ⟨B,hb,rfl⟩ := mem_image.mp hx
    obtain ⟨A,ha,rfl⟩ := mem_image.mp hb
    obtain ⟨ha,lt⟩ := mem_filter.mp ha
    have eq : val (f A)=2 • g i+val A := shift A ha
    have na := hiS A (mem_powerset.mp (sub ha))
    have e : prev (f A)=val (insert i A) := by
      simp only [prev,eq,val,sum_insert na,two_nsmul]
      abel
    change (length g (val (f A)-g i+g i):ℤ)+2≤length g (prev (f A))
    rw [sub_add_cancel,e,length_subset g h,length_subset g h,card_insert_of_notMem na]
    omega
  · change (S.powerset.image prev).card=_
    rw [card_image_of_injective _ pinj,card_powerset]
  · have eq : K.card=strict.card :=
      (card_image_of_injective _ pinj).trans (card_image_of_injOn (inj.mono (by exact filter_subset ..)))
    have partition := card_filter_add_card_filter_not (s:=H) (fun A=>(f A).card=A.card)
    have other : (H.filter (fun A=>¬(f A).card=A.card))=strict := by
      apply filter_congr
      intro A ha
      have := (down A ha).2
      omega
    rw [other,←eq] at partition
    have bound := card_le_card sub
    change H.card≤S.powerset.card at bound
    rw [card_powerset] at bound
    change 2*(H.filter _).card≤2^S.card at ties
    change 2^S.card ≤ 2*(K.card + (2^S.card-H.card))
    omega

end Potential

/-- Normalizing an actual set of residues, with exactly the multiplicity
    predicate used by the Formal Conjectures statement. -/
theorem normalize_residues {N : ℕ} (A : Finset (ZMod N)) (p : ZMod N) (hp : p∈A)
    (valid : ∀ c : ZMod N→ℕ, (∑ a∈A,c a)=A.card →
      (∑ a∈A,(c a:ZMod N)*a)=∑ a∈A,a → ∀ a∈A,c a=1) :
    OMA.WeightedModulus.Valid 1 (fun _ : A.erase p=>1) (fun i=>i.val-p) := by
  classical
  apply (OMA.WeightedModulus.normalize _ _ p (fun i : A.erase p=>i.val)).mp
  intro x y total mass
  let c (a : ZMod N) : ℕ := if h : a∈A.erase p then y ⟨a,h⟩ else x
  have split {M : Type} [AddCommMonoid M] (F : ZMod N→M) :
      (∑ a∈A,F a)=F p+∑ a : A.erase p,F a.val := by
    rw [←sum_erase_add A F hp,add_comm]
    rw [sum_coe_sort]
  have cp : c p=x := by simp [c]
  have ca (a : A.erase p) : c a.val=y a := by
    dsimp only [c]
    rw [dif_pos a.property]
  have csize : (∑ a∈A,c a)=A.card := by
    rw [split c,cp]
    simp_rw [ca]
    simp only [sum_const_nat,card_univ,Fintype.card_coe,mul_one] at total
    rw [total]
    have := card_erase_add_one hp
    omega
  have csum : (∑ a∈A,(c a:ZMod N)*a)=∑ a∈A,a := by
    rw [split (fun a=>(c a:ZMod N)*a),split (fun a=>a)]
    simpa only [cp,ca,nsmul_eq_mul,Nat.cast_one,one_mul] using mass
  have eq := valid c csize csum
  exact ⟨by simpa only [cp] using eq p hp,funext fun i => by
    simpa only [ca] using eq i.val (mem_of_mem_erase i.property)⟩

end OMA.CyclicSurplus
