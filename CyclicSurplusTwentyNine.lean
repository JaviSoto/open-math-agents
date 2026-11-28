import CyclicPairs

/-! A 29/24 lower bound for the cyclic all-ones modulus. -/

open private OMA.CyclicSurplus.density OMA.CyclicSurplus.masks_injective
  OMA.CyclicSurplus.ties_cross OMA.CyclicSurplus.reduced_sum OMA.CyclicSurplus.length
  OMA.CyclicSurplus.length_subset OMA.CyclicSurplus.increase OMA.CyclicSurplus.predecessor
  from CyclicSurplus
open private OMA.CyclicSurplus.shifted_subset from CyclicSurplus
open private OMA.CyclicSurplus.far_count from CyclicSurplusSeven
namespace OMA.CyclicSurplus
open Finset
variable {α G : Type*} [Fintype α] [DecidableEq α] [AddCommGroup G]

private lemma ties_strong (g : α→G) (h : OMA.WeightedModulus.Valid 1 (fun _=>1) g)
    (i : α) (nz : 2 • g i≠0) (four : 4 • g i≠0)
    (nt : ∀ a : α, a≠i → g a≠3 • g i)
    (H : Finset (Finset α)) (ties : ∀ B∈H,B⊆univ.erase i ∧ ∃ A : Finset α,
      A.card=B.card ∧ (∑ a∈B,g a)=2 • g i+∑ a∈A,g a) :
    8*H.card≤3*2^((univ : Finset α).erase i).card := by
  classical
  let S := (univ : Finset α).erase i
  let z := 2 • g i
  let K := (S.powerset ×ˢ (univ : Finset (Finset α))).filter fun p =>
    Disjoint p.1 p.2 ∧ p.1.card=p.2.card ∧ (∑ i∈p.1,g i)=z+∑ i∈p.2,g i
  have info (p : Finset α × Finset α) : p∈K ↔ p.1⊆S ∧ Disjoint p.1 p.2 ∧
      p.1.card=p.2.card ∧ (∑ i∈p.1,g i)=z+∑ i∈p.2,g i := by
    simp only [K,mem_filter,mem_product,mem_univ,and_true,mem_powerset]
  let pos (p : Finset α × Finset α) := p.1
  let neg (p : Finset α × Finset α) := p.2∩S
  have non (p : Finset α × Finset α) (hp : p∈K) : (pos p).Nonempty := by
    obtain ⟨_,_,cd,mass⟩ := (info p).mp hp
    by_contra no
    have em : p.1=∅ := not_nonempty_iff_eq_empty.mp no
    have em' : p.2=∅ := card_eq_zero.mp (by simpa [em] using cd.symm)
    exact nz (by simpa [em,em'] using mass.symm)
  have both (p : Finset α × Finset α) (hp : p∈K) : (pos p).Nonempty ∧ (neg p).Nonempty := by
    refine ⟨non p hp,?_⟩
    by_contra none
    obtain ⟨ps,_,cd,mass⟩ := (info p).mp hp
    have sub : p.2⊆{i} := by
      intro a ha
      by_contra ne
      apply none
      exact ⟨a,mem_inter.mpr ⟨ha,mem_erase.mpr ⟨by simpa using ne,mem_univ _⟩⟩⟩
    have em : p.2={i} := by
      rcases Finset.subset_singleton_iff.mp sub with em|eq
      · have e : p.1=∅ := card_eq_zero.mp (by simpa [em] using cd)
        simpa [pos,e] using non p hp
      · exact eq
    obtain ⟨a,ae⟩ := card_eq_one.mp (by simpa [em] using cd : p.1.card=1)
    apply nt a (mem_erase.mp (ps (by rw [ae]; simp))).1
    simpa [em,ae,z,show 3 • g i=2 • g i+g i by simp only [succ_nsmul]] using mass
  have rv (p : Finset α × Finset α) (hp : p∈K) (a b : α)
      (u : pos p={a}) (v : neg p={b}) : p.1={a} ∧ p.2={b} := by
    obtain ⟨_,_,cd,_⟩ := (info p).mp hp
    have s : (neg p)⊆p.2 := inter_subset_left
    have e : neg p=p.2 := eq_of_subset_of_card_le s (by change p.1={a} at u; simp [v,←cd,u])
    exact ⟨u,e.symm.trans v⟩
  have joint := OMA.CyclicPairs.joint S K pos neg (fun p hp=>⟨((info p).mp hp).1,inter_subset_right⟩)
    (fun p hp=>((info p).mp hp).2.1.mono_right inter_subset_left)
    (by
      intro p hp q hq ne
      obtain ⟨ps,dp,cp,ep⟩ := (info p).mp hp
      obtain ⟨_,dq,cq,eq⟩ := (info q).mp hq
      obtain ⟨j,hj⟩ := OMA.CyclicSurplus.ties_cross g h p.1 p.2 q.1 q.2 dp dq cp cq
        (by rw [ep,eq]; abel) ne
      obtain ⟨j1,j2⟩ := mem_inter.mp hj
      exact ⟨j,mem_inter.mpr ⟨j1,mem_inter.mpr ⟨j2,ps j1⟩⟩⟩)
    both (by
      intro p hp q hq a b ua vb ub va
      obtain ⟨pu,pv⟩ := rv p hp a b ua vb
      obtain ⟨qu,qv⟩ := rv q hq b a ub va
      have pEq := ((info p).mp hp).2.2.2
      have qEq := ((info q).mp hq).2.2.2
      simp only [pu,pv,qu,qv,sum_singleton] at pEq qEq
      apply four
      have e : z+z+g a=0+g a := by rw [add_assoc,←qEq,←pEq,zero_add]
      have d := add_right_cancel e
      change 2 • g i+2 • g i=0 at d
      rwa [show 4 • g i=2 • g i+2 • g i by rw [←add_nsmul]])
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
  change (∑ p∈K,OMA.CyclicSurplus.density (pos p) (neg p))≤3/8 at joint
  have prod := mul_le_mul_of_nonneg_left joint (by positivity : (0:ℝ)≤2^S.card)
  exact_mod_cast (by linarith : (8:ℝ)*H.card≤3*2^S.card)

/-- The two coordinates g and 3g give five translates of the remaining
    box, because the four squarefree translates have all differences
    1, 2, 3, 4. Here the only new translate, at 2g, is checked directly. -/
private lemma triple_bound [Fintype G] (g : α→G) (h : OMA.WeightedModulus.Valid 1 (fun _=>1) g)
    (i j : α) (ne : j≠i) (triple : g j=3 • g i) :
    5*2^(((univ : Finset α).erase i).erase j).card≤Fintype.card G := by
  classical
  let S := ((univ : Finset α).erase i).erase j
  let val (A : Finset α) := ∑ a∈A,g a
  let full := (univ : Finset (Finset α)).image val
  let extra := S.powerset.image (fun A=>2 • g i+val A)
  have inj : Function.Injective val := OMA.CyclicSurplus.masks_injective g h
  have dis : Disjoint full extra := by
    apply disjoint_left.mpr
    intro z hz ez
    obtain ⟨B,_,rfl⟩ := mem_image.mp hz
    obtain ⟨A,as,mass⟩ := mem_image.mp ez
    have aS := mem_powerset.mp as
    have ni : i∉A := fun hi=>notMem_erase i univ (mem_of_mem_erase (aS hi))
    have nj : j∉A := fun hj=>notMem_erase j (univ.erase i) (aS hj)
    have niB := (OMA.CyclicSurplus.shifted_subset g h i A B ni mass.symm).1
    by_cases bj : j∈B
    · have nb : i∉B.erase j := fun hh=>niB (mem_of_mem_erase hh)
      have e : val (B.erase j)+g j=val B := sum_erase_add B g bj
      have eq : val (insert i (B.erase j))=val A := by
        change (∑ a∈insert i (B.erase j),g a)=val A
        rw [sum_insert nb]
        rw [triple,mass.symm] at e
        rw [show 3 • g i=g i+2 • g i by simp only [succ_nsmul,add_comm]] at e
        exact add_right_cancel (b:=2 • g i) (by
          rw [add_comm (val A) (2 • g i),←e]; dsimp only [val]; abel)
      apply ni
      rw [←inj eq]
      exact mem_insert_self ..
    · have eq : val (insert i B)=val (insert j A) := by
        simp only [val,sum_insert niB,sum_insert nj,triple]
        change g i+val B=3 • g i+val A
        rw [←mass,show 3 • g i=2 • g i+g i by simp only [succ_nsmul]]
        abel
      have yes := mem_insert_self i B
      rw [inj eq] at yes
      exact (mem_insert.mp yes).elim (Ne.symm ne) ni
  have count := card_le_univ (full∪extra)
  rw [card_union_of_disjoint dis] at count
  have fullCard : full.card=2^Fintype.card α := by
    dsimp only [full]; rw [card_image_of_injective _ inj]; simp
  have extraCard : extra.card=2^S.card :=
    (card_image_of_injective _ (fun _ _ eq=>inj (add_left_cancel eq))).trans (card_powerset S)
  have mem : j∈(univ : Finset α).erase i := mem_erase.mpr ⟨ne,mem_univ _⟩
  have c1 := card_erase_add_one (mem_univ i)
  have c2 := card_erase_add_one mem
  have size : Fintype.card α=S.card+1+1 := by rw [←card_univ,←c1,←c2]
  rw [fullCard,extraCard,size,pow_succ,pow_succ] at count
  change 5*2^S.card≤_
  omega

private lemma four_generator [Fintype G] [IsAddCyclic G] (g : α→G)
    (h : OMA.WeightedModulus.Valid 1 (fun _=>1) g) (hd : 3≤Fintype.card α) :
    ∃ i,4 • g i≠0 := by
  classical
  by_contra! no
  let T := (univ : Finset G).filter fun z => (4:ℕ) • z=0
  let F (A : Finset α) : T := ⟨∑ i∈A,g i,mem_filter.mpr
    ⟨mem_univ _,by simp only [smul_sum,no,sum_const_zero]⟩⟩
  have inj : Function.Injective F := fun _ _ eq=>OMA.CyclicSurplus.masks_injective g h (congrArg Subtype.val eq)
  have lo := Fintype.card_le_of_injective F inj
  simp only [Fintype.card_finset,Fintype.card_coe] at lo
  have up : T.card≤4 := IsAddCyclic.card_nsmul_eq_zero_le (by decide : 0 < 4)
  have big : (2:ℕ)^3≤2^Fintype.card α := Nat.pow_le_pow_right (by decide) hd
  omega

private theorem twenty_nine_bound [Fintype G] [DecidableEq G] (g : α→G)
    (h : OMA.WeightedModulus.Valid 1 (fun _=>1) g) (i : α) (four : 4 • g i≠0) :
    29*2^((univ : Finset α).erase i).card≤12*Fintype.card G := by
  classical
  have nz : 2 • g i≠0 := by
    intro z; apply four; rw [show 4 • g i=2 • g i+2 • g i by rw [←add_nsmul],z,zero_add]
  by_cases tr : ∃ j : α,j≠i ∧ g j=3 • g i
  · obtain ⟨j,ne,eq⟩ := tr
    have b := triple_bound g h i j ne eq
    have c := card_erase_add_one (mem_erase.mpr ⟨ne,mem_univ j⟩ : j∈(univ : Finset α).erase i)
    rw [←c,pow_succ]; omega
  push Not at tr
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
  have fb := OMA.CyclicSurplus.far_count (g i) C F (filter_subset ..) sep (fun _ hx=>(mem_filter.mp hx).2)
  let E := S.powerset.filter (fun B=>∃ A : Finset α,A.card=B.card ∧ val B=2 • g i+val A)
  have eb := ties_strong g h i nz four tr E
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
  change 8*E.card≤3*2^S.card at eb
  change 29*2^S.card≤12*Fintype.card G
  rw [←cc] at eb ⊢
  omega

open Arxiv.«2607.08366» in
/-- The 29/24 bound for the all-ones cyclic minimum modulus. -/
theorem modulus_twenty_nine_lower {N n : ℕ} (hn : 3≤n) (hN : 0<N) (A : Finset (ZMod N))
    (card : A.card=n) (ok : IsValidMod A) : 29*2^(n-1)≤24*N := by
  classical
  by_cases small : n=3
  · have first := modulus_seven_lower hn hN A card ok
    rw [small] at first ⊢
    norm_num at first ⊢
    omega
  have : NeZero N := ⟨hN.ne'⟩
  obtain ⟨p,hp⟩ := A.card_pos.mp (by omega)
  let B := A.erase p
  let g (j : B) := j.val-p
  have valid : OMA.WeightedModulus.Valid 1 (fun _ : B=>1) g := normalize_residues A p hp ok
  have bc : Fintype.card B=n-1 := by
    rw [Fintype.card_coe]
    exact (card_erase_of_mem hp).trans (by rw [card])
  obtain ⟨i,four⟩ := four_generator g valid (by omega)
  have low := twenty_nine_bound g valid i four
  rw [card_erase_of_mem (mem_univ i),card_univ,bc,ZMod.card] at low
  have power : 2^(n-1)=2^(n-1-1)*2 := by rw [←Nat.pow_succ]; congr 1; omega
  rw [power]
  omega

end OMA.CyclicSurplus
