import FormalConjectures.Arxiv.«2607.08366».MinModulus

/-! Functional-graph rigidity of valid cyclic sets closed under affine
doubling.  The antipodal-pair observation is Sitjar, Lemma 2.3(a). -/

namespace OMA.AffineDoubling
open Finset Function Arxiv.«2607.08366»

private lemma total {N : ℕ} (A : Finset (ZMod N)) (ok : IsValidMod A)
    (m : Multiset (ZMod N)) (ins : ∀ x∈m,x∈A) (sz : m.card=A.card)
    (sum : m.sum=∑ x∈A,x) : m=A.val := by
  classical
  have sub : m.toFinset⊆A := fun x hx=>ins x (Multiset.mem_toFinset.mp hx)
  have e : (∑ x∈A,m.count x • x)=m.sum := by
    rw [←sum_subset sub (fun x _ nx=>by simp [(Multiset.count_eq_zero.mpr (by simpa using nx) : m.count x=0)])]
    simpa using (sum_multiset_map_count m id).symm
  have a := ok (fun x=>m.count x) ((Multiset.sum_count_eq_card ins).trans sz)
    (by simpa only [nsmul_eq_mul] using e.trans sum)
  apply Multiset.ext'
  intro x
  by_cases hx : x∈A
  · exact (a x hx).trans (Multiset.count_eq_one_of_mem A.nodup hx).symm
  · have nm : x∉m := fun yes=>hx (ins x yes)
    simp [Multiset.count_eq_zero.mpr nm,hx]

private lemma replace {N : ℕ} {A : Finset (ZMod N)} (ok : IsValidMod A)
    (F : Finset (ZMod N)) (sub : F⊆A) (m : Multiset (ZMod N))
    (ins : ∀ x∈m,x∈A) (sz : m.card=F.card) (sum : m.sum=∑ x∈F,x) :
    m=F.val := by
  classical
  have split := sdiff_union_of_subset sub
  have dis : Disjoint (A\F) F := disjoint_sdiff_self_left
  have eq : (A\F).val+F.val=A.val := by rw [←disjUnion_val _ _ dis,disjUnion_eq_union,split]
  apply add_left_cancel (a:=(A\F).val)
  rw [eq]
  apply total A ok _ (fun x hx=>(Multiset.mem_add.mp hx).elim
    (fun h=>mem_of_subset sdiff_subset h) (ins x))
  · rw [Multiset.card_add,sz]; exact card_sdiff_add_card_eq_card sub
  · rw [Multiset.sum_add,sum]
    have vs : (A\F).val.sum=∑ x∈A\F,x := by change _=(Multiset.map id _).sum; simp
    rw [vs]; exact sum_sdiff sub (f:=id)

private lemma small_kernel {N : ℕ} [NeZero N] {x y : ZMod N}
    (hx : x≠0) (hy : y≠0) (tx : 2 • x=0) (ty : 2 • y=0) : x=y := by
  classical
  by_contra ne
  let T := (univ : Finset (ZMod N)).filter (fun z=>2 • z=0)
  have up : T.card≤2 := IsAddCyclic.card_nsmul_eq_zero_le (by decide : 0<2)
  have inc : ({x,y,0} : Finset (ZMod N))⊆T := by
    intro z hz
    simp only [mem_insert,mem_singleton] at hz
    apply mem_filter.mpr ⟨mem_univ _,?_⟩
    rcases hz with rfl|rfl|rfl
    · exact tx
    · exact ty
    · simp
  have lo := card_le_card inc
  simp [ne,hx,hy] at lo
  omega

/-- The image under affine doubling drops at most one point; this is
    Sitjar's antipodal-pair lemma in functional form. -/
theorem image_large {N : ℕ} [NeZero N] {A : Finset (ZMod N)} (ok : IsValidMod A)
    (t : ZMod N) : A.card ≤ (A.image (fun a=>2 • a+t)).card+1 := by
  classical
  let f (a : ZMod N) := 2 • a+t
  by_cases inj : Set.InjOn f (A : Set (ZMod N))
  · rw [card_image_of_injOn inj]; omega
  simp only [Set.InjOn,Finset.mem_coe] at inj
  push Not at inj
  obtain ⟨a,ha,b,hb,ab,ne⟩ := inj
  have tors {u v : ZMod N} (e : f u=f v) : 2 • (u-v)=0 :=
    by rw [nsmul_sub,sub_eq_zero]; exact add_right_cancel e
  have forb (c d : ZMod N) (hc : c∈A.erase b) (hd : d∈A.erase b) (cd : f c=f d)
      (diff : c≠d) (ad : a≠d) : False := by
    have eq := small_kernel (sub_ne_zero.mpr ne) (sub_ne_zero.mpr diff) (tors ab) (tors cd)
    have mass : b+c=a+d := by
      apply add_right_cancel (b:=-b-d)
      convert eq.symm using 1 <;> abel
    let F : Finset (ZMod N) := {a,d}
    let m : Multiset (ZMod N) := {b,c}
    have q := replace ok F (insert_subset ha (singleton_subset_iff.mpr (mem_of_mem_erase hd))) m
      (by simp [m,hb,mem_of_mem_erase hc])
      (by simp [F,m,ad]) (by simpa [F,m,ad] using mass)
    have yes : b∈F.val := q ▸ (show b∈m by simp [m])
    have := (mem_erase.mp hd).1
    simp [F,Ne.symm ne,Ne.symm this] at yes
  have inj' : Set.InjOn f ((A.erase b : Finset _) : Set _) := by
    intro c hc d hd eq
    by_contra ne'
    by_cases ad : a=d
    · exact forb d c hd hc eq.symm (Ne.symm ne') (by simpa [ad] using Ne.symm ne')
    · exact forb c d hc hd eq ne' ad
  have le := card_le_card (image_subset_image (erase_subset b A) (f:=f))
  rw [card_image_of_injOn inj'] at le
  have count := card_erase_add_one (show b∈A from hb)
  change A.card ≤ (A.image f).card+1; omega

private lemma orbit_cut {α : Type*} [DecidableEq α] (f : α→α) (A : Finset α) (x : α)
    (stay : ∀ k,f^[k] x∈A) {y : α} (hit : ∃ k,f^[k] x=y) :
    ∃ k<A.card,f^[k] x=y := by
  classical
  let m := Nat.find hit
  have found : f^[m] x=y := Nat.find_spec hit
  have earlier (i j : ℕ) (lt : i<j) (le : j ≤ m) (eq : f^[i] x=f^[j] x) : False := by
    have e : f^[m-j+i] x=y := by
      rw [iterate_add_apply,eq,←iterate_add_apply,Nat.sub_add_cancel le,found]
    have small : m ≤ m-j+i := Nat.find_min' hit e
    omega
  have inj : Set.InjOn (fun i : ℕ=>f^[i] x) (range (m+1) : Finset ℕ) := by
    intro i hi j hj eq
    have bi := mem_range.mp hi
    have bj := mem_range.mp hj
    rcases lt_trichotomy i j with lt|e|gt
    · exact False.elim (earlier i j lt (by omega) eq)
    · exact e
    · exact False.elim (earlier j i gt (by omega) eq.symm)
  have inc : (range (m+1)).image (fun i=>f^[i] x)⊆A := by
    intro z hz
    obtain ⟨k,_,rfl⟩ := mem_image.mp hz
    exact stay k
  have b := card_le_card inc
  rw [card_image_of_injOn inj,card_range] at b
  exact ⟨m,by omega,found⟩

/-- A valid nonempty closed set is one forward orbit, including any
    transient tail before periodicity. -/
theorem closed_orbit {N : ℕ} [NeZero N] {A : Finset (ZMod N)} (ok : IsValidMod A)
    (non : A.Nonempty) (t : ZMod N) (closed : ∀ a∈A,2 • a+t∈A) :
    ∃ x∈A,A=(range A.card).image (fun k=>(fun a : ZMod N=>2 • a+t)^[k] x) := by
  classical
  let f (a : ZMod N) := 2 • a+t
  have inc : A.image f⊆A := by
    intro z hz; obtain ⟨a,ha,rfl⟩ := mem_image.mp hz; exact closed a ha
  let miss := A\A.image f
  have small : miss.card≤1 := by
    have a := card_sdiff_add_card_eq_card inc
    have b := image_large ok t
    change A.card≤(A.image f).card+1 at b
    dsimp only [miss]; omega
  obtain ⟨x,hx,unique⟩ : ∃ x∈A,∀ y∈A,y≠x → y∈A.image f := by
    by_cases yes : miss.Nonempty
    · obtain ⟨x,hx⟩ := yes
      refine ⟨x,(mem_sdiff.mp hx).1,?_⟩
      intro y hy ne
      by_contra no
      exact ne (card_le_one.mp small y (mem_sdiff.mpr ⟨hy,no⟩ : y∈miss) x hx)
    · obtain ⟨x,hx⟩ := non
      exact ⟨x,hx,fun y hy _=>by by_contra no; exact yes ⟨y,mem_sdiff.mpr ⟨hy,no⟩⟩⟩
  have stay (k : ℕ) : f^[k] x∈A := by
    induction k with
    | zero => exact hx
    | succ k ih => rw [iterate_succ_apply']; exact closed _ ih
  let O := A.filter (fun y=>∃ k : ℕ,f^[k] x=y)
  let D := A\O
  have memO (k : ℕ) : f^[k] x∈O := mem_filter.mpr ⟨stay k,k,rfl⟩
  have backward : D ⊆ D.image f := by
    intro y hy
    obtain ⟨yA,yo⟩ := mem_sdiff.mp hy
    have ne : y≠x := fun eq=>yo (eq ▸ memO 0)
    obtain ⟨z,za,zy⟩ := mem_image.mp (unique y yA ne)
    apply mem_image.mpr ⟨z,mem_sdiff.mpr ⟨za,?_⟩,zy⟩
    intro zo
    obtain ⟨k,ek⟩ := (mem_filter.mp zo).2
    exact yo (mem_filter.mpr ⟨yA,k+1,by rw [iterate_succ_apply',ek,zy]⟩)
  have perm : D=D.image f := eq_of_subset_of_card_le backward card_image_le
  have di : Set.InjOn f (D : Set (ZMod N)) := card_image_iff.mp (congrArg Finset.card perm.symm)
  have mass : (∑ y∈D,y)+D.card • t=0 := by
    have e : (∑ y∈D,f y)=∑ y∈D,y := (sum_image di).symm.trans (congrArg (fun E : Finset (ZMod N)=>∑ y∈E,y) perm.symm)
    simp only [f,sum_add_distrib,sum_const,two_nsmul] at e
    exact add_left_cancel (a:=∑ y∈D,y) (by simpa only [←add_assoc,add_zero] using e)
  have all : A⊆O := by
    intro y hy
    by_contra no
    have yd : y∈D := mem_sdiff.mpr ⟨hy,no⟩
    let k := D.card
    let L : Multiset (ZMod N) := x ::ₘ ((range k).val.map (fun j=>f^[j] x))
    let F := insert (f^[k] x) D
    have nd : f^[k] x∉D := fun h=>(mem_sdiff.mp h).2 (memO _)
    have sm (l : ℕ) : x+(∑ j∈range l,f^[j] x)+l • t=f^[l] x := by
      induction l with
      | zero => simp
      | succ l ih =>
        rw [sum_range_succ,succ_nsmul,iterate_succ_apply' (f:=f) (x:=x) (n:=l)]
        change _=2 • f^[l] x+t
        rw [two_nsmul,←ih]; abel
    have lin (a : ZMod N) (h : a∈L) : a∈O := by
      rcases Multiset.mem_cons.mp h with rfl|mem
      · exact memO 0
      · obtain ⟨j,_,rfl⟩ := Multiset.mem_map.mp mem
        exact memO _
    have same := replace ok F (insert_subset (stay _) sdiff_subset) L
      (fun a ha=>(mem_filter.mp (lin a ha)).1)
      (by simp [F,L,k,nd]) (by
        have e := sm k
        change x+(∑ j∈range k,f^[j] x)=∑ z∈insert (f^[k] x) D,z
        rw [sum_insert nd,←e]
        have mm : k • t + (∑ y∈D,y)=0 := by rw [add_comm]; exact mass
        rw [add_assoc,_root_.add_assoc,mm,add_zero])
    have hh : y∈L := same ▸ (show y∈F.val from mem_insert_of_mem yd)
    exact no (lin _ hh)
  refine ⟨x,hx,?_⟩
  apply Subset.antisymm
  · intro y hy
    obtain ⟨k,hk,eq⟩ := orbit_cut f A x stay (mem_filter.mp (all hy)).2
    exact mem_image.mpr ⟨k,mem_range.mpr hk,eq⟩
  · intro y hy; obtain ⟨k,_,rfl⟩ := mem_image.mp hy; exact stay k

end OMA.AffineDoubling
