import PathSplice
import LongCycleShape

/-! Once one row returns to itself, every disjoint row is short. -/

open private OMA.LongCycle.inherited OMA.LongCycle.cycle_order OMA.LongCycle.path_bound from LongCycle
open private OMA.BinaryPrefix.sum_bits from BinaryPrefix
namespace OMA.PathCycle
open Finset OMA.PathBox OMA.PathSplice Arxiv.«2607.08366»

theorem cycle {I : Type*} [Fintype I] [DecidableEq I] {N : ℕ} [NeZero N]
    (L : I→ℕ) (x : I→ZMod N) (inj : Function.Injective (label L x))
    (ok : IsValidMod (univ.image (label L x))) (J : I) {a n : ℕ}
    (ia : a<L J) (wrap : 2^L J • x J=2^a • x J) (num : (∑ i,L i)=n)
    (half : 2*Fintype.card I*Nat.log 2 n≤n) :
    ∃ (r : ℕ) (y : ZMod N) (C : Finset (ZMod N)), 0<r ∧ n≤2*r ∧ 2^r • y=y ∧
      C.card=r ∧ C=(range r).image (fun j=>2^j • y) ∧ C⊆univ.image (label L x) := by
  classical
  let A := univ.image (label L x)
  let r := L J-a
  let y := 2^a • x J
  let C := (range r).image (fun j=>2^j • y)
  have dim : r+a=L J := by dsimp [r]; omega
  have rp : 0<r := by dsimp [r]; omega
  have ac : A.card=n := (size L x inj).trans num
  have shift (j : ℕ) : 2^j • y=2^(j+a) • x J := by simp [y,pow_add,mul_smul]
  have period : 2^r • y=y := (shift r).trans (dim ▸ wrap)
  have unique (i j : I) {s t : ℕ} (sb : s<L i) (tb : t<L j) (eq : 2^s • x i=2^t • x j) :
      i=j ∧ s=t := by
    have e := inj (a₁:=⟨i,⟨s,sb⟩⟩) (a₂:=⟨j,⟨t,tb⟩⟩) eq
    exact ⟨congrArg Sigma.fst e,congrArg (fun z : Σ i,Fin (L i)=>z.2.val) e⟩
  have csInj : Set.InjOn (fun j : ℕ=>2^j • y) (range r : Finset ℕ) := by
    intro s hs t ht e
    change 2^s • y=2^t • y at e
    rw [shift,shift] at e
    have hs' := mem_range.mp hs; have ht' := mem_range.mp ht
    have z := (unique J J (by omega) (by omega) e).2
    omega
  have cs : C.card=r := (card_image_of_injOn csInj).trans (card_range _)
  have inc : C⊆A := by
    intro z hz
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hz
    rw [shift]; apply label_mem; have := mem_range.mp hj; omega
  have ord := OMA.LongCycle.cycle_order ok y rp period C rfl cs inc
  have sc : (∑ z∈C,z)=0 := by
    dsimp [C]
    rw [sum_image csInj,←sum_smul,OMA.BinaryPrefix.sum_bits,←ord,addOrderOf_nsmul_eq_zero]
  let width (i : I) := if i=J then a else L i
  have short (i : I) : width i≤Nat.log 2 n := by
    let k := width i
    have kl : k≤L i := by
      by_cases e : i=J
      · subst i; simpa [k,width] using ia.le
      · simp [k,width,e]
    let B := (range k).image (fun j=>2^j • x i)
    have bs : B.card=k := by
      apply (card_image_of_injOn ?_).trans (card_range _)
      intro s hs t ht eq
      exact (unique i i (lt_of_lt_of_le (mem_range.mp hs) kl) (lt_of_lt_of_le (mem_range.mp ht) kl) eq).2
    have bi : B⊆A := by
      intro z hz; obtain ⟨j,hj,rfl⟩ := mem_image.mp hz
      exact label_mem L x i (lt_of_lt_of_le (mem_range.mp hj) kl)
    have dis : Disjoint C B := by
      apply disjoint_left.mpr
      intro z hs ht
      obtain ⟨s,ss,rfl⟩ := mem_image.mp hs
      obtain ⟨j,jj,eq⟩ := mem_image.mp ht
      rw [shift] at eq
      have sb := mem_range.mp ss; have jb := mem_range.mp jj
      obtain ⟨eqi,eqj⟩ := unique i J (lt_of_lt_of_le jb kl) (by omega) eq
      have kw : k=a := by simp [k,width,eqi]
      omega
    have both := union_subset inc bi
    have pow := OMA.LongCycle.path_bound (OMA.LongCycle.inherited ok both) rfl dis (card_pos.mp (cs ▸ rp)) sc
      (x i) (by rw [bs])
    rw [bs] at pow
    exact (Nat.le_log_iff_pow_le (by decide) (by have := card_le_card inc; omega : n≠0)).mpr
      (pow.trans ((card_le_card both).trans_eq ac))
  have bound := sum_le_sum (s:=univ) (fun i _=>short i)
  simp only [sum_const,card_univ,smul_eq_mul] at bound
  have eq (i : I) : width i+(if i=J then r else 0)=L i := by
    by_cases same : i=J
    · subst i; simp [width]; omega
    · simp [width,same]
  have mass := sum_congr (s₁:=univ) rfl (fun i _=>eq i)
  simp only [sum_add_distrib,sum_ite_eq',mem_univ,if_true,num] at mass
  rw [mul_assoc] at half
  exact ⟨r,y,C,rp,by omega,period,cs,rfl,inc⟩

end OMA.PathCycle
