import CyclicSurplusFinal

/-! A constant improvement by combining two- and three-step gaps. -/

open private OMA.CyclicSurplus.density OMA.CyclicSurplus.masks_injective
  OMA.CyclicSurplus.ties_cross OMA.CyclicSurplus.reduced_sum OMA.CyclicSurplus.length
  OMA.CyclicSurplus.length_subset OMA.CyclicSurplus.increase OMA.CyclicSurplus.predecessor
  from CyclicSurplus

namespace OMA.CyclicSurplus
open Finset
variable {α G : Type*} [Fintype α] [DecidableEq α] [AddCommGroup G]

/-- The target masks are restricted to a face; their source masks may use
    coordinates outside that face. Equal source and target sizes are enough
    to keep the projected subcubes proper and separated. -/
theorem ties_into_face (g : α→G) (h : OMA.WeightedModulus.Valid 1 (fun _=>1) g)
    (S : Finset α) (z : G) (nz : z≠0) (H : Finset (Finset α))
    (ties : ∀ B∈H,B⊆S ∧ ∃ A : Finset α,A.card=B.card ∧ (∑ i∈B,g i)=z+∑ i∈A,g i) :
    2*H.card≤2^S.card := by
  classical
  let K := (S.powerset ×ˢ (univ : Finset (Finset α))).filter fun p =>
    Disjoint p.1 p.2 ∧ p.1.card=p.2.card ∧ (∑ i∈p.1,g i)=z+∑ i∈p.2,g i
  have info (p : Finset α × Finset α) : p∈K ↔ p.1⊆S ∧ Disjoint p.1 p.2 ∧
      p.1.card=p.2.card ∧ (∑ i∈p.1,g i)=z+∑ i∈p.2,g i := by
    simp only [K,mem_filter,mem_product,mem_univ,and_true,mem_powerset]
  let pos (p : Finset α × Finset α) := p.1
  let neg (p : Finset α × Finset α) := p.2∩S
  have half := separated_half S K pos neg (fun p hp=>⟨((info p).mp hp).1,inter_subset_right⟩)
    (fun p hp=>((info p).mp hp).2.1.mono_right inter_subset_left) (by
      intro p hp
      obtain ⟨_,_,cd,mass⟩ := (info p).mp hp
      apply Finset.Nonempty.mono subset_union_left
      by_contra no
      have em : p.1=∅ := not_nonempty_iff_eq_empty.mp no
      have em' : p.2=∅ := card_eq_zero.mp (by simpa [em] using cd.symm)
      exact nz (by simpa [em,em'] using mass.symm))
    (by
      intro p hp q hq ne
      obtain ⟨ps,dp,cp,ep⟩ := (info p).mp hp
      obtain ⟨_,dq,cq,eq⟩ := (info q).mp hq
      obtain ⟨j,hj⟩ := OMA.CyclicSurplus.ties_cross g h p.1 p.2 q.1 q.2 dp dq cp cq
        (by rw [ep,eq]; abel) ne
      obtain ⟨j1,j2⟩ := mem_inter.mp hj
      exact ⟨j,mem_inter.mpr ⟨j1,mem_inter.mpr ⟨j2,ps j1⟩⟩⟩)
  let box (p : Finset α × Finset α) := Icc (pos p) (S\neg p)
  have cover : H⊆K.biUnion box := by
    intro B hb
    obtain ⟨bs,A,same,mass⟩ := ties B hb
    let p : Finset α × Finset α := (B\A,A\B)
    apply mem_biUnion.mpr ⟨p,(info p).mpr ?_,?_⟩
    · refine ⟨sdiff_subset.trans bs,disjoint_sdiff_self_left.mono_right sdiff_subset,
        card_sdiff_comm same.symm,?_⟩
      apply add_right_cancel (b:=∑ i∈A∩B,g i)
      change (∑ i∈B\A,g i)+_=(z+∑ i∈A\B,g i)+_
      rw [add_assoc,OMA.CyclicSurplus.reduced_sum g A B,inter_comm A B,OMA.CyclicSurplus.reduced_sum g B A,mass]
    · exact mem_Icc.mpr ⟨sdiff_subset,fun j hj => mem_sdiff.mpr
        ⟨bs hj,fun bad=>(mem_sdiff.mp (mem_inter.mp bad).1).2 hj⟩⟩
  have card (p : Finset α × Finset α) (hp : p∈K) :
      ((box p).card:ℝ)=2^S.card*OMA.CyclicSurplus.density (pos p) (neg p) := by
    obtain ⟨ps,ds,_,_⟩ := (info p).mp hp
    have ns : neg p⊆S := inter_subset_right
    have dis : Disjoint (pos p) (neg p) := ds.mono_right inter_subset_left
    have sub : pos p⊆S\neg p := fun j hj=>mem_sdiff.mpr ⟨ps hj,disjoint_left.mp dis hj⟩
    have le : (pos p).card+(neg p).card≤S.card := by
      rw [←card_union_of_disjoint dis]
      exact card_le_card (union_subset ps ns)
    rw [show (box p).card=2^((S.card-(neg p).card)-(pos p).card) by
      dsimp only [box]; rw [card_Icc_finset sub,card_sdiff_of_subset ns]]
    have exp : S.card-(neg p).card-(pos p).card+((pos p).card+(neg p).card)=S.card := by omega
    simp only [Nat.cast_pow,Nat.cast_ofNat,OMA.CyclicSurplus.density,one_div,inv_pow]
    apply (eq_div_iff (pow_ne_zero _ (by norm_num : (2:ℝ)≠0))).mpr
    rw [←pow_add,exp]
  have b := (card_le_card cover).trans card_biUnion_le
  have bound : (H.card:ℝ)≤∑ p∈K,((box p).card:ℝ) := by exact_mod_cast b
  rw [sum_congr rfl card,←mul_sum] at bound
  have prod := mul_le_mul_of_nonneg_left half (by positivity : (0:ℝ)≤2^S.card)
  exact_mod_cast (by linarith : (2:ℝ)*H.card≤2^S.card)

/-- Charge two consecutive predecessor edges per marked site; the spacing
    hypothesis makes all charged edges distinct. -/
theorem two_step_count [Fintype G] [DecidableEq G] (g : G) (P : G→ℤ) (C K : Finset G)
    (sub : K⊆C) (grow : ∀ x,P (x+g)≤P x+1) (sep : ∀ x∈C,x+g∉C)
    (base : ∀ x∈C,P x≤P (x-2 • g)) (strict : ∀ x∈K,P x+1≤P (x-2 • g)) :
    2*C.card+K.card≤Fintype.card G := by
  classical
  let D (x : G) : ℤ := 1+P x-P (x+g)
  have nn (x : G) : 0≤D x := by dsimp [D]; linarith [grow x]
  let L := C.image (fun x=>x-g)
  let R := C.image (fun x=>x-2 • g)
  have dis : Disjoint L R := by
    apply disjoint_left.mpr
    intro y hy ry
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
    obtain ⟨w,hw,eq⟩ := mem_image.mp ry
    apply sep x hx
    convert hw using 1
    rw [eq_sub_iff_add_eq] at eq
    rw [eq.symm,two_nsmul]
    abel
  have bound (x : G) (hx : x∈C) :
      2+(if x∈K then (1:ℤ) else 0) ≤ D (x-g)+D (x-2 • g) := by
    have eo : x-2 • g+g=x-g := by rw [two_nsmul]; abel
    simp only [D,sub_add_cancel,eo]
    by_cases k : x∈K
    · simp only [k,if_true]; linarith [strict x k]
    · simp only [k,if_false]; linarith [base x hx]
  have all := sum_le_sum bound
  have l : (∑ x∈C,D (x-g))=∑ x∈L,D x :=
    (sum_image (fun _ _ _ _ eq=>sub_left_inj.mp eq)).symm
  have r : (∑ x∈C,D (x-2 • g))=∑ x∈R,D x :=
    (sum_image (fun _ _ _ _ eq=>sub_left_inj.mp eq)).symm
  have total := sum_le_sum_of_subset_of_nonneg (subset_univ (L∪R)) (f:=D) (fun x _ _=>nn x)
  have perm := Equiv.sum_comp (Equiv.addRight g) P
  change (∑ x,P (x+g))=∑ x,P x at perm
  rw [sum_union dis,←l,←r] at total
  have totalEq : (∑ x,D x)=Fintype.card G := by
    simp only [D,sum_sub_distrib,sum_add_distrib,perm,add_sub_cancel_right,sum_const,card_univ,
      nsmul_eq_mul,mul_one]
  rw [totalEq] at total
  rw [sum_add_distrib,sum_add_distrib] at all
  have eq : C.filter (fun x=>x∈K)=K := by ext x; simp only [mem_filter]; exact ⟨And.right,fun hx=>⟨sub hx,hx⟩⟩
  have cnt : (∑ x∈C,if x∈K then (1:ℤ) else 0)=K.card := by
    rw [←Finset.sum_filter,eq]; simp
  rw [cnt] at all
  simp only [sum_const,nsmul_eq_mul] at all
  exact_mod_cast (by linarith : (2:ℤ)*C.card+K.card≤Fintype.card G)

private def shiftSet [DecidableEq G] (C : Finset G) (v : G) := C.image (fun z=>z+v)

private lemma shiftCard [DecidableEq G] (C : Finset G) (v : G) : (shiftSet C v).card=C.card :=
  card_image_of_injective _ (fun _ _ eq=>add_right_cancel eq)

private lemma shiftDisjoint [DecidableEq G] (C F : Finset G) (u v : G)
    (notIn : ∀ x∈F, x+(v-u)∉C) : Disjoint (shiftSet C u) (shiftSet F v) := by
  apply disjoint_left.mpr
  intro z hz fz
  obtain ⟨a,ha,rfl⟩ := mem_image.mp hz
  obtain ⟨b,hb,eq⟩ := mem_image.mp fz
  apply notIn b hb
  have e : b+(v-u)=a := by rw [←add_sub_assoc,eq,add_sub_cancel_right]
  rwa [e]

/-- For a target missing short returns, both predecessor sites are outside
    the full original box, and the two sets of predecessor sites are disjoint. -/
private lemma far_count [Fintype G] [DecidableEq G] (g : G) (C F : Finset G)
    (sub : F⊆C) (sep : ∀ x∈C,x+g∉C)
    (far : ∀ x∈F,(x-2 • g)∉C ∧ (x-3 • g)∉C) :
    2*C.card+2*F.card≤Fintype.card G := by
  classical
  have back (x : G) (hx : x∈C) : x-g∉C := fun hx' => sep _ hx' (by simpa using hx)
  have d01 : Disjoint (shiftSet C 0) (shiftSet C g) :=
    shiftDisjoint _ _ _ _ (fun x hx => by simpa using sep x hx)
  have d12 : Disjoint (shiftSet F (-g)) (shiftSet F (-(2 • g))) := by
    apply shiftDisjoint
    intro x hx hit
    apply back x (sub hx)
    convert sub hit using 1
    rw [two_nsmul]; abel
  have d0f1 : Disjoint (shiftSet C 0) (shiftSet F (-g)) := by
    apply shiftDisjoint
    intro x hx
    simpa [sub_eq_add_neg] using back x (sub hx)
  have d0f2 : Disjoint (shiftSet C 0) (shiftSet F (-(2 • g))) := by
    apply shiftDisjoint
    intro x hx
    simpa [sub_eq_add_neg] using (far x hx).1
  have d1f1 : Disjoint (shiftSet C g) (shiftSet F (-g)) := by
    apply shiftDisjoint
    intro x hx
    convert (far x hx).1 using 2
    rw [two_nsmul]; abel
  have d1f2 : Disjoint (shiftSet C g) (shiftSet F (-(2 • g))) := by
    apply shiftDisjoint
    intro x hx
    convert (far x hx).2 using 2
    rw [show 3 • g=2 • g+g by simp only [succ_nsmul]]
    abel
  have dis := Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_right.mpr ⟨d0f1,d0f2⟩,
    Finset.disjoint_union_right.mpr ⟨d1f1,d1f2⟩⟩
  have sz := card_le_univ ((shiftSet C 0∪shiftSet C g)∪(shiftSet F (-g)∪shiftSet F (-(2 • g))))
  rw [card_union_of_disjoint dis,card_union_of_disjoint d01,card_union_of_disjoint d12] at sz
  simp only [shiftCard] at sz
  omega

/-- Separate targets with strict potential change, targets with a distant
    return, and the remaining equal-length representations. -/
theorem seven_bound [Fintype G] [DecidableEq G] (g : α→G)
    (h : OMA.WeightedModulus.Valid 1 (fun _=>1) g) (i : α) (nz : 2 • g i≠0) :
    7*2^((univ : Finset α).erase i).card≤3*Fintype.card G := by
  classical
  let S := (univ : Finset α).erase i
  let val (A : Finset α) := ∑ j∈A,g j
  let C := S.powerset.image val
  have inj : Function.Injective val := OMA.CyclicSurplus.masks_injective g h
  have inside (A : Finset α) (a : A⊆S) : i∉A := fun hi=>notMem_erase i univ (a hi)
  have insertVal (A : Finset α) (a : A⊆S) : val (insert i A)=val A+g i := by
    simp only [val,sum_insert (inside A a),add_comm]
  have sep (x : G) (hx : x∈C) : x+g i∉C := by
    obtain ⟨A,as,rfl⟩ := mem_image.mp hx
    intro hit
    obtain ⟨B,bs,eq⟩ := mem_image.mp hit
    have mask := inj (eq.trans (insertVal A (mem_powerset.mp as)).symm)
    exact inside B (mem_powerset.mp bs) (by rw [mask]; exact mem_insert_self ..)
  let P (x : G) : ℤ := OMA.CyclicSurplus.length g x
  have grow (x : G) : P (x+g i)≤P x+1 := by
    dsimp only [P]; exact_mod_cast OMA.CyclicSurplus.increase g x i
  have wc (A : Finset α) : P (val A)=A.card := by
    dsimp only [P,val]; exact_mod_cast OMA.CyclicSurplus.length_subset g h A
  have base (x : G) (xc : x∈C) : P x≤P (x-2 • g i) := by
    obtain ⟨A,as,rfl⟩ := mem_image.mp xc
    have pred : (A.card:ℤ)+1≤P (val A-g i) := by
      dsimp only [P,val]
      exact_mod_cast OMA.CyclicSurplus.predecessor g h i A (inside A (mem_powerset.mp as))
    have gr := grow (val A-2 • g i)
    rw [show val A-2 • g i+g i=val A-g i by rw [two_nsmul]; abel] at gr
    rw [wc]; omega
  let K := C.filter (fun x=>P x<P (x-2 • g i))
  let F := C.filter (fun x=>x-2 • g i∉C ∧ x-3 • g i∉C)
  have kb := two_step_count (g i) P C K (filter_subset ..) grow sep base
    (fun x hx=>by have q : P x<P (x-2 • g i) := (mem_filter.mp hx).2; omega)
  have fb := far_count (g i) C F (filter_subset ..) sep (fun _ hx=>(mem_filter.mp hx).2)
  let E := S.powerset.filter (fun B=>∃ A : Finset α,A.card=B.card ∧ val B=2 • g i+val A)
  have eb := ties_into_face g h S (2 • g i) nz E
    (fun B hb=>⟨mem_powerset.mp (mem_filter.mp hb).1,(mem_filter.mp hb).2⟩)
  have cover : C⊆((E.image val)∪K)∪F := by
    intro x xc
    by_cases k : x∈K
    · exact mem_union_left _ (mem_union_right _ k)
    by_cases f : x∈F
    · exact mem_union_right _ f
    obtain ⟨B,bs,eq⟩ := mem_image.mp xc
    subst x
    have eqP : P (val B-2 • g i)=P (val B) := by
      have le := base (val B) xc
      by_contra ne
      exact k (mem_filter.mpr ⟨xc,by omega⟩)
    have hit : val B-2 • g i∈C ∨ val B-3 • g i∈C := by
      by_contra! no
      exact f (mem_filter.mpr ⟨xc,no⟩)
    apply mem_union_left _ (mem_union_left _ (mem_image.mpr ⟨B,mem_filter.mpr ⟨bs,?_⟩,rfl⟩))
    have source (A : Finset α) (eq : val A=val B-2 • g i) :
        ∃ A : Finset α,A.card=B.card ∧ val B=2 • g i+val A := by
      refine ⟨A,?_,?_⟩
      · exact_mod_cast ((wc A).symm.trans ((congrArg P eq).trans (eqP.trans (wc B))))
      · rw [eq]; abel
    rcases hit with hit|hit
    · obtain ⟨A,_,ae⟩ := mem_image.mp hit
      exact source A ae
    · obtain ⟨A,as,ae⟩ := mem_image.mp hit
      apply source (insert i A)
      rw [insertVal A (mem_powerset.mp as),ae,show 3 • g i=2 • g i+g i by simp only [succ_nsmul]]
      abel
  have cc : C.card=2^S.card := (card_image_of_injective _ inj).trans (card_powerset S)
  have sumc := (card_le_card cover).trans (card_union_le ..)
  have first := card_union_le (E.image val) K
  rw [card_image_of_injective _ inj] at first
  rw [cc] at kb fb sumc
  change 7*2^S.card≤3*Fintype.card G
  omega

open Arxiv.«2607.08366» in
/-- A uniform factor 7/6 over the binary lower bound for the minimum
    cyclic modulus in Fonollosa's conjecture. -/
theorem modulus_seven_lower {N n : ℕ} (hn : 3≤n) (hN : 0<N) (A : Finset (ZMod N))
    (card : A.card=n) (ok : IsValidMod A) : 7*2^(n-1)≤6*N := by
  classical
  have : NeZero N := ⟨hN.ne'⟩
  obtain ⟨p,hp⟩ := A.card_pos.mp (by omega)
  let B := A.erase p
  let g (j : B) := j.val-p
  have valid : OMA.WeightedModulus.Valid 1 (fun _ : B=>1) g := normalize_residues A p hp ok
  have bc : Fintype.card B=n-1 := by
    rw [Fintype.card_coe]
    exact (card_erase_of_mem hp).trans (by rw [card])
  obtain ⟨i,dbl⟩ := nontrivial_double g valid (by omega)
  have low := seven_bound g valid i dbl
  rw [card_erase_of_mem (mem_univ i),card_univ,bc,ZMod.card] at low
  have power : 2^(n-1)=2^(n-1-1)*2 := by rw [←Nat.pow_succ]; congr 1; omega
  rw [power]
  omega

end OMA.CyclicSurplus
