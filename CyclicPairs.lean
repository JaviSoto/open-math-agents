import CyclicSurplusSeven

/-! A weighted set-pairs bound for the joint family of short gaps. -/

namespace OMA.CyclicPairs
open Finset
open private OMA.CyclicSurplus.density from CyclicSurplus

noncomputable def weight (u v : ℕ) : ℝ := 1 / ((u+v).choose u : ℝ)

private lemma recurrence (a b : ℕ) :
    ((a:ℝ)+1)*weight a b=(a+b+1:ℕ)*weight (a+1) b := by
  have h := Nat.add_one_mul_choose_eq (a+b) a
  rw [show (a+b+1)=(a+1+b) by omega] at h
  have ha : 0<((a+b).choose a : ℝ) := by exact_mod_cast Nat.choose_pos (by omega : a≤a+b)
  have hb : 0<((a+1+b).choose (a+1) : ℝ) := by exact_mod_cast Nat.choose_pos (by omega : a+1≤a+1+b)
  simp only [weight]
  field_simp
  exact_mod_cast (by nlinarith [h] : (a+1)*(a+1+b).choose (a+1)=(a+b).choose a*(a+b+1))

/-- Bollobás's set-pairs inequality, proved by exposing the first
    coordinate of a uniformly ordered ground set. -/
theorem bollobas {α I : Type*} [DecidableEq α] [DecidableEq I]
    (S : Finset α) (K : Finset I) (U V : I→Finset α)
    (inside : ∀ i∈K,U i⊆S ∧ V i⊆S)
    (consistent : ∀ i∈K,Disjoint (U i) (V i))
    (cross : ∀ i∈K,∀ j∈K,i≠j → ((U i)∩(V j)).Nonempty) :
    (∑ i∈K,weight (U i).card (V i).card)≤1 := by
  classical
  induction cardeq : S.card using Nat.strong_induction_on generalizing S K U V with
  | h n ih =>
    by_cases empty : K=∅
    · simp [empty]
    by_cases one : ∃ i∈K,U i=∅
    · obtain ⟨i,hi,em⟩ := one
      have eq : K={i} := by
        apply eq_singleton_iff_unique_mem.mpr ⟨hi,?_⟩
        intro j hj
        by_contra ne
        simpa [em] using cross i hi j hj (Ne.symm ne)
      simp [eq,em,weight]
    have pos (i : I) (hi : i∈K) : 0<(U i).card :=
      card_pos.mpr (nonempty_iff_ne_empty.mpr (fun em=>one ⟨i,hi,em⟩))
    have sp : 0<S.card := by
      obtain ⟨i,hi⟩ := nonempty_iff_ne_empty.mpr empty
      exact (pos i hi).trans_le (card_le_card (inside i hi).1)
    let R (x : α) (i : I) : ℝ := if x∈V i then 0 else weight ((U i).erase x).card (V i).card
    have cut (x : α) (hx : x∈S) : (∑ i∈K,R x i)≤1 := by
      let J := K.filter (fun i=>x∉V i)
      have sz := card_erase_lt_of_mem hx
      have b := ih ((S.erase x).card) (by omega) (S.erase x) J (fun i=>(U i).erase x) V
        (by
          intro i hi
          obtain ⟨ik,notin⟩ := mem_filter.mp hi
          exact ⟨erase_subset_erase x (inside i ik).1,fun a ha=>mem_erase.mpr
            ⟨fun eq=>notin (eq ▸ ha),(inside i ik).2 ha⟩⟩)
        (fun i hi=>(consistent i (mem_filter.mp hi).1).mono_left (erase_subset ..))
        (by
          intro i hi j hj ne
          obtain ⟨a,as⟩ := cross i (mem_filter.mp hi).1 j (mem_filter.mp hj).1 ne
          obtain ⟨hu,hv⟩ := mem_inter.mp as
          exact ⟨a,mem_inter.mpr ⟨mem_erase.mpr ⟨fun eq=>(mem_filter.mp hj).2 (eq ▸ hv),hu⟩,hv⟩⟩)
        rfl
      simpa only [J,sum_filter,R,ite_not] using b
    have balance (i : I) (hi : i∈K) :
        (∑ x∈S,R x i)=(S.card:ℝ)*weight (U i).card (V i).card := by
      let u := (U i).card
      let v := (V i).card
      let W := S\(U i∪V i)
      have nc := pos i hi
      have split : S=(U i∪V i)∪W := by
        simpa [W,union_comm] using (sdiff_union_of_subset (union_subset (inside i hi).1 (inside i hi).2)).symm
      have sw : Disjoint (U i∪V i) W := disjoint_sdiff_self_right
      have pr : ∀ x∈U i,R x i=weight (u-1) v := by
        intro x hx
        simp [R,disjoint_left.mp (consistent i hi) hx,card_erase_of_mem hx,u,v]
      have nr : ∀ x∈V i,R x i=0 := by intro x hx; simp [R,hx]
      have wr : ∀ x∈W,R x i=weight u v := by
        intro x hx
        obtain ⟨_,bad⟩ := mem_sdiff.mp hx
        have ⟨nu,nv⟩ := not_or.mp (fun h=>bad (mem_union.mpr h))
        simp [R,nu,nv,u,v]
      have cs : S.card=u+v+W.card := by
        calc S.card = ((U i∪V i)∪W).card := congrArg _ split
             _ = _ := by rw [card_union_of_disjoint sw,card_union_of_disjoint (consistent i hi)]
      conv_lhs => rw [split,sum_union sw,sum_union (consistent i hi)]
      rw [sum_congr rfl pr,sum_congr rfl nr,sum_congr rfl wr]
      simp only [sum_const,smul_zero,nsmul_eq_mul,add_zero]
      have e : u-1+1=u := by dsimp [u]; omega
      have step := recurrence (u-1) v
      rw [show u-1+v+1=u+v by omega,e] at step
      change (u:ℝ)*weight (u-1) v+_=(S.card:ℝ)*weight u v
      rw [←Nat.cast_succ,Nat.succ_eq_add_one,e] at step
      rw [step,cs]
      push_cast; ring
    have total := sum_le_sum cut
    rw [sum_comm,sum_congr rfl balance,←mul_sum] at total
    simp only [sum_const,nsmul_eq_mul,mul_one] at total
    exact (mul_le_mul_iff_right₀ (by exact_mod_cast sp : (0:ℝ)<S.card)).mp (by simpa using total)

private lemma binom_three (m : ℕ) (hm : 3 ≤ m) (u : ℕ) :
    8 * m.choose u ≤ 3 * 2^m := by
  induction m,hm using Nat.le_induction generalizing u with
  | base =>
    by_cases le : u≤3
    · interval_cases u <;> decide
    · rw [Nat.choose_eq_zero_of_lt (by omega)]; decide
  | succ m hm ih =>
    cases u with
    | zero =>
      simp only [Nat.choose_zero_right,Nat.mul_one,Nat.pow_succ]
      have b := ih 0
      simp only [Nat.choose_zero_right,Nat.mul_one] at b
      omega
    | succ u =>
      rw [Nat.choose_succ_succ,Nat.pow_succ]
      have h := ih u
      have h' := ih u.succ
      omega

theorem large_faces {α I : Type*} [DecidableEq α] [DecidableEq I]
    (S : Finset α) (K : Finset I) (U V : I→Finset α)
    (inside : ∀ i∈K,U i⊆S ∧ V i⊆S)
    (consistent : ∀ i∈K,Disjoint (U i) (V i))
    (cross : ∀ i∈K,∀ j∈K,i≠j → ((U i)∩(V j)).Nonempty)
    (size : ∀ i∈K,3≤(U i).card+(V i).card) :
    (∑ i∈K,(1/2:ℝ)^((U i).card+(V i).card))≤3/8 := by
  have bb := bollobas S K U V inside consistent cross
  have localBound (i : I) (hi : i∈K) : (1/2:ℝ)^((U i).card+(V i).card)≤
      (3/8)*weight (U i).card (V i).card := by
    let a := (U i).card
    let b := (V i).card
    have hp : 0<((a+b).choose a : ℝ) := by exact_mod_cast Nat.choose_pos (by omega : a≤a+b)
    have h := binom_three (a+b) (size i hi) a
    change (1/2:ℝ)^(a+b)≤(3/8)*(1/((a+b).choose a : ℝ))
    rw [one_div_pow]
    field_simp
    exact_mod_cast (by omega : 8*(a+b).choose a≤2^(a+b)*3)
  have hb := sum_le_sum localBound
  rw [←mul_sum] at hb
  linarith

/-- A single face fixing one positive and one negative bit forces every
    other face into the opposite quadrant. Excluding its exact reverse
    recovers the same 3/8 bound as for large supports. -/
theorem joint {α I : Type*} [DecidableEq α] [DecidableEq I]
    (S : Finset α) (K : Finset I) (U V : I→Finset α)
    (inside : ∀ i∈K,U i⊆S ∧ V i⊆S)
    (consistent : ∀ i∈K,Disjoint (U i) (V i))
    (cross : ∀ i∈K,∀ j∈K,i≠j → ((U i)∩(V j)).Nonempty)
    (nonempty : ∀ i∈K,(U i).Nonempty ∧ (V i).Nonempty)
    (noReverse : ∀ i∈K,∀ j∈K, ∀ a b:α,U i={a} → V i={b} → U j={b} → V j≠{a}) :
    (∑ i∈K,(1/2:ℝ)^((U i).card+(V i).card))≤3/8 := by
  classical
  by_cases small : ∃ i∈K,(U i).card+(V i).card<3
  · obtain ⟨i,hi,sz⟩ := small
    obtain ⟨cu,cv⟩ := nonempty i hi
    have uc := card_pos.mpr cu
    have vc := card_pos.mpr cv
    obtain ⟨a,ua⟩ := card_eq_one.mp (by omega : (U i).card=1)
    obtain ⟨b,vb⟩ := card_eq_one.mp (by omega : (V i).card=1)
    let J := K.erase i
    have fixed (j : I) (hj : j∈J) : b∈U j ∧ a∈V j := by
      obtain ⟨ne,jk⟩ := mem_erase.mp hj
      obtain ⟨x,hx⟩ := cross j jk i hi ne
      obtain ⟨y,hy⟩ := cross i hi j jk ne.symm
      simp only [vb,ua,mem_inter,mem_singleton] at hx hy
      exact ⟨hx.2 ▸ hx.1,hy.1 ▸ hy.2⟩
    let u (j : I) := (U j).erase b
    let v (j : I) := (V j).erase a
    have half := OMA.CyclicSurplus.separated_half S J u v
      (fun j hj=>⟨(erase_subset ..).trans (inside j (mem_of_mem_erase hj)).1,
        (erase_subset ..).trans (inside j (mem_of_mem_erase hj)).2⟩)
      (fun j hj=>(consistent j (mem_of_mem_erase hj)).mono (erase_subset ..) (erase_subset ..))
      (by
        intro j hj
        by_contra no
        have eq := not_nonempty_iff_eq_empty.mp no
        obtain ⟨eu,ev⟩ := union_eq_empty.mp eq
        have u' := insert_erase (fixed j hj).1
        have v' := insert_erase (fixed j hj).2
        change (U j).erase b=∅ at eu
        change (V j).erase a=∅ at ev
        rw [eu,insert_empty_eq] at u'
        rw [ev,insert_empty_eq] at v'
        exact noReverse i hi j (mem_of_mem_erase hj) a b ua vb u'.symm v'.symm)
      (by
        intro j hj k hk ne
        obtain ⟨z,hz⟩ := cross j (mem_of_mem_erase hj) k (mem_of_mem_erase hk) ne
        obtain ⟨ju,kv⟩ := mem_inter.mp hz
        have nb : z≠b := fun eq=>disjoint_left.mp (consistent k (mem_of_mem_erase hk))
          (fixed k hk).1 (eq ▸ kv)
        have na : z≠a := fun eq=>disjoint_left.mp (consistent j (mem_of_mem_erase hj))
          (eq ▸ ju) (fixed j hj).2
        exact ⟨z,mem_inter.mpr ⟨mem_erase.mpr ⟨nb,ju⟩,mem_erase.mpr ⟨na,kv⟩⟩⟩)
    change (∑ j∈J,(1/2:ℝ)^((u j).card+(v j).card))≤1/2 at half
    have factor (j : I) (hj : j∈J) : (1/2:ℝ)^((U j).card+(V j).card)=
        (1/4)*(1/2:ℝ)^((u j).card+(v j).card) := by
      have c1 := card_erase_add_one (fixed j hj).1
      have c2 := card_erase_add_one (fixed j hj).2
      rw [show (U j).card+(V j).card=(u j).card+(v j).card+2 by dsimp [u,v]; omega,pow_add]
      ring
    rw [←sum_erase_add _ _ hi]
    change (∑ j∈J,(1/2:ℝ)^((U j).card+(V j).card)) + _ ≤ _
    rw [sum_congr rfl factor,←mul_sum,ua,vb]
    norm_num
    linarith
  · exact large_faces S K U V inside consistent cross (fun i hi=>by
      by_contra! small'
      exact small ⟨i,hi,small'⟩)

end OMA.CyclicPairs
