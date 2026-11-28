import CyclicReturn
import CubeNeighbors
import PathGapCoins

/-! A logarithmic length path has a genuine successor, using a
    first-return permutation of its exterior subset sums. -/

namespace OMA.PathReturn
open Finset OMA.PathReserve OMA.PathGapCoins Arxiv.«2607.08366»

private theorem transport {G α : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] [DecidableEq α]
    (Q : Finset α) (non : Q.Nonempty) (v : α→G) (inj : Set.InjOn v Q) (x : G) :
    ∃ (f : α→α) (g : α→ℕ), Set.InjOn f Q ∧ (∀ s∈Q,f s∈Q) ∧
      (∀ s∈Q,0<g s ∧ v (f s)=v s+g s • x) ∧ (∑ s∈Q,g s)≤Fintype.card G := by
  classical
  let D := Q.image v
  let ptr (s : Q) : D := ⟨v s,mem_image_of_mem v s.property⟩
  have bi : Function.Bijective ptr := by
    refine ⟨fun a b e=>Subtype.ext (inj a.property b.property (congrArg Subtype.val e)),?_⟩
    intro z; obtain ⟨s,hs,e⟩ := mem_image.mp z.property; exact ⟨⟨s,hs⟩,Subtype.ext e⟩
  let e := Equiv.ofBijective ptr bi
  obtain ⟨gap,next,pos,step,_,total⟩ := OMA.CyclicReturn.packing D x (non.image _)
  let send := (e.trans next).trans e.symm
  let f (s : α) := if h : s∈Q then (send ⟨s,h⟩).val else s
  let g (s : α) := if h : s∈Q then gap (e ⟨s,h⟩) else 0
  have ff (s) (h : s∈Q) : f s=(send ⟨s,h⟩).val := dif_pos h
  have gg (s) (h : s∈Q) : g s=gap (e ⟨s,h⟩) := dif_pos h
  refine ⟨f,g,?_,fun s hs=>ff s hs ▸ (send ⟨s,hs⟩).property,?_,?_⟩
  · intro s hs t ht eq
    rw [ff _ hs,ff _ ht] at eq
    exact congrArg Subtype.val (send.injective (Subtype.ext eq))
  · intro s hs
    rw [ff s hs,gg s hs]
    have same : e (send ⟨s,hs⟩)=next (e ⟨s,hs⟩) := by simp [send]
    exact ⟨pos _,(congrArg Subtype.val same).trans (step _)⟩
  · rw [←sum_attach Q g]; change (∑ s : Q,g s.val)≤_
    simpa only [fun s : Q=>gg s s.property,e.sum_comp] using total

private theorem tile {N L : ℕ} {A : Finset (ZMod N)} {x : ZMod N} (c : Chain A x L)
    {j : ℕ} (lt : j<2^L) : ∃ T⊆row x L,v T=j • x := by
  classical
  obtain ⟨S,sub,eq⟩ := OMA.CycleTerminal.mask L j lt
  refine ⟨_,image_subset_image sub,?_⟩
  change (∑ z∈S.image (fun i=>2^i • x),z)=_
  rw [sum_image (c.distinct.mono sub),←sum_smul,eq]

theorem successor {N L : ℕ} [NeZero N] {A : Finset (ZMod N)} {x : ZMod N}
    (ok : IsValidMod A) (c : Chain A x L) (ell : 4≤L)
    (big : 16*A.card*(A.card+15)≤2^L) (lt : N<2^A.card) : 2^L • x∈A := by
  classical
  let W := 2^L
  let n := A.card
  let B := A\row x L
  let k := B.card
  let Q := B.powerset
  have dim : k+L=n := by
    have h := card_sdiff_add_card_eq_card (row_sub c); rwa [row_size c] at h
  have hW : W=16*2^(L-4) := by
    dsimp [W]; conv_lhs => rw [show L=L-4+4 by omega,pow_add]
    exact Nat.mul_comm _ _
  have h8 : 2^(L-3)=2*2^(L-4) := by rw [←pow_succ',show L-4+1=L-3 by omega]
  change 16*n*(n+15)≤W at big
  have wn : 16*n≤W := by nlinarith
  have large : 4*A.card≤2^L := by change 4*n≤W; omega
  have vol : W*2^k=2^n := by rw [←dim,pow_add,mul_comm]
  have qc : Q.card=2^k := card_powerset _
  obtain ⟨f,g,fi,stay,step,total⟩ := transport Q (powerset_nonempty B) v (subset_injective c ok ell large) x
  rw [ZMod.card] at total
  have gapmin (s) (hs : s∈Q) : W-n≤g s :=
    spacing c ok ell large s _ (mem_powerset.mp hs) (mem_powerset.mp (stay _ hs)) (g s) (step _ hs).1 (step _ hs).2
  have kill : W • x≠0 := by
    intro zero
    have all (s) (hs : s∈Q) : W≤g s := by
      by_contra! off
      have e : v s=v (f s)+(W-g s) • x := by
        rw [(step _ hs).2,add_assoc,←add_nsmul,show g s+(W-g s)=W by omega,zero,add_zero]
      have back := spacing c ok ell large _ _ (mem_powerset.mp (stay _ hs)) (mem_powerset.mp hs)
        (W-g s) (by omega) e
      change W-n≤W-g s at back
      have := gapmin _ hs; omega
    have sum := (sum_le_sum all).trans total
    simp only [sum_const,smul_eq_mul,qc] at sum
    change N<2^n at lt; rw [←vol,mul_comm] at lt; omega
  by_contra missing
  have empty (T : Finset (ZMod N)) (tA : T⊆A) (eq : v T=W • x) : False := by
    have le := OMA.PathSuccessor.subset_succ ok x (by omega : 0<L) (by omega : A.card≤2^L) c.inside T tA eq
    have non : T.Nonempty := by
      by_contra e; rw [not_nonempty_iff_eq_empty.mp e] at eq; exact kill (by simpa [v] using eq.symm)
    obtain ⟨a,ea⟩ := card_eq_one.mp (by have := card_pos.mpr non; omega : T.card=1)
    have hit : a=W • x := by simpa [ea,v] using eq
    exact missing (hit ▸ tA (by simp [ea]))
  let D := Q.filter (fun s=>g s≤W+2^(L-4))
  have sub : D⊆Q := filter_subset ..
  have bounds (s) (sd : s∈D) := And.intro (gapmin _ (sub sd)) (mem_filter.mp sd).2
  have close (s) (sd : s∈D) (t) (td : t∈D) : g s≤g t+2^(L-3) := by
    have := bounds _ sd; have := bounds _ td; omega
  have ranks (s) (sd : s∈D) := gains c ok ell large s _ (mem_powerset.mp (sub sd))
    (mem_powerset.mp (stay _ (sub sd))) (g s) (step _ (sub sd)).1 (mem_filter.mp sd).2 (step _ (sub sd)).2
  have move (s) (sd : s∈D) : (s\f s).Nonempty := by
    by_contra! no
    have ss : s⊆f s := sdiff_eq_empty_iff_subset.mp no
    have le := card_le_card ss
    have max : g s≤W := by by_contra! bad; exact le.not_gt ((ranks _ sd).2 bad)
    have pos := (step _ (sub sd)).1
    obtain ⟨T,tr,eq⟩ := tile c (j:=W-g s) (by change W-g s<W; omega)
    have fb : f s⊆B := mem_powerset.mp (stay _ (sub sd))
    have dis : Disjoint T (f s\s) := disjoint_left.mpr (fun a at' out=>(mem_sdiff.mp (fb (mem_sdiff.mp out).1)).2 (tr at'))
    apply empty (T∪(f s\s)) (union_subset (tr.trans (row_sub c)) (sdiff_subset.trans (fb.trans sdiff_subset)))
    have rem : v (f s\s)=g s • x := by
      apply add_right_cancel (b:=v s)
      rw [show v (f s\s)+v s=v (f s) from sum_sdiff ss,(step _ (sub sd)).2,add_comm]
    change (∑ z∈T∪(f s\s),z)=_
    rw [sum_union dis,show (∑ z∈T,z)=_ from eq,show (∑ z∈f s\s,z)=_ from rem,
      ←add_nsmul,Nat.sub_add_cancel max]
  have sum (U : Finset (ZMod N)) : U.val.sum=v U := by change _=(U.val.map id).sum; simp
  have insertV (i) (S : Finset (ZMod N)) (off : i∉S) : v (insert i S)=i+v S := sum_insert off
  have up (s) (hs : s∈D) (i) (hi : i∈s\f s) (low : s.erase i∈D) : (f s).card≤(f (s.erase i)).card := by
    obtain ⟨si,nf⟩ := mem_sdiff.mp hi
    let t := s.erase i
    have ins := insertV i t (notMem_erase i s)
    rw [show insert i t=s from insert_erase si] at ins
    by_contra! wrong
    let m := i ::ₘ (f t).val
    have id := local_rigid c ok ell large (f s) (mem_powerset.mp (stay _ (sub hs))) m (fun a ha=>by
      rcases Multiset.mem_cons.mp ha with rfl|mem
      · exact mem_powerset.mp (sub hs) si
      · exact mem_powerset.mp (stay _ (sub low)) mem)
      (close t low s hs) (close s hs t low)
      (by simp only [m,Multiset.sum_cons,sum,(step s (sub hs)).2,(step t (sub low)).2,ins]; abel)
      (by simp [m]; omega)
    have member : i∈(f s).val := id ▸ Multiset.mem_cons_self i _
    exact nf member
  have cross (s) (hs : s∈D) (t) (ht : t∈D) (card : (f s).card=(f t).card)
      (i) (hi : i∈s\f s) (j) (hj : j∈t\f t) (er : s.erase i=t.erase j) (ne : i≠j) : j∈f s := by
    by_contra off
    obtain ⟨si,is⟩ := mem_sdiff.mp hi; obtain ⟨tj,_⟩ := mem_sdiff.mp hj
    have ss := insertV i (s.erase i) (notMem_erase i s)
    have tt := insertV j (t.erase j) (notMem_erase j t)
    rw [insert_erase si,er] at ss; rw [insert_erase tj] at tt
    let m := i ::ₘ (f t).val
    have id := local_rigid c ok ell large (insert j (f s))
      (insert_subset (mem_powerset.mp (sub ht) tj) (mem_powerset.mp (stay _ (sub hs))))
      m (fun a h=>by
        rcases Multiset.mem_cons.mp h with rfl|h
        · exact mem_powerset.mp (sub hs) si
        · exact mem_powerset.mp (stay _ (sub ht)) h) (close t ht s hs) (close s hs t ht)
      (by simp only [m,Multiset.sum_cons,sum,insertV _ _ off,(step s (sub hs)).2,(step t (sub ht)).2,ss,tt]; abel)
      (by simp [m,off,card])
    have member : i∈(insert j (f s)).val := id ▸ Multiset.mem_cons_self i _
    exact (mem_insert.mp member).elim ne is
  have loss := OMA.CubeNeighbors.loss B D f sub (fi.mono sub) (fun s hs=>mem_powerset.mp (stay _ (sub hs)))
    move (fun s hs=>(ranks s hs).1) up cross
  let H := Q\D
  have hc : H.card=Q.card-D.card := card_sdiff_of_subset sub
  change 2^k≤(k+15)*(Q.card-D.card) at loss
  rw [←hc] at loss
  have minsum := sum_le_sum (s:=Q) (f:=fun s=>(W-n)+(if s∈H then 2^(L-4) else 0)) (g:=g) (by
    intro s hs
    by_cases bad : s∈H
    · have off := (mem_sdiff.mp bad).2
      have outside : ¬g s≤W+2^(L-4) := fun h=>off (mem_filter.mpr ⟨hs,h⟩)
      simp only [if_pos bad]; omega
    · simpa [bad] using gapmin s hs)
  have filt : Q.filter (fun s=>s∈H)=H := by
    ext a; exact mem_filter.trans ⟨And.right,fun h=>⟨(mem_sdiff.mp h).1,h⟩⟩
  rw [sum_add_distrib,←sum_filter,filt,sum_const,sum_const,smul_eq_mul,smul_eq_mul,qc] at minsum
  have big' : n*(k+15)≤2^(L-4) := by
    have r := Nat.mul_le_mul_left (16*n) (show k+15≤n+15 by omega)
    nlinarith
  have shortage := minsum.trans total
  have nw : W-n+n=W := Nat.sub_add_cancel (by omega)
  have vol' : (W-n)*2^k+n*2^k=2^n := by rw [←add_mul,nw,vol]
  have scale := Nat.mul_le_mul_left n loss
  have bad := Nat.mul_le_mul_right H.card big'
  change N<2^n at lt
  nlinarith

end OMA.PathReturn
