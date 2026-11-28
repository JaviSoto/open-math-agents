import PathHoles

/-! A long path returning to zero forces the full (unreduced) modulus. -/

open private OMA.PathShift.pack from PathShift
open private OMA.BinaryPrefix.digits from BinaryPrefix
namespace OMA.PathPeriod
open OMA.PathCoins OMA.PathBox OMA.PathShift OMA.PathHoles Finset Arxiv.«2607.08366»

private lemma adjust {k n original : ℕ} (kp : 2≤k) (large : 4*n≤2^k) :
    ∃ w : List ℕ,Bounded k w ∧ w.length≤k ∧ n≤weight w ∧
      weight w≡original [MOD 2^k] := by
  let W : ℕ := 2^k
  have Wp : 0<W := by dsimp [W]; positivity
  let r := original%W
  have range : r<W := Nat.mod_lt _ Wp
  have same : r≡original [MOD W] := Nat.mod_modEq ..
  by_cases enough : n≤r
  · obtain ⟨w,b,v,c,_⟩ := OMA.BinaryPrefix.digits k r range
    change weight w=r at v
    exact ⟨w,b,c,v ▸ enough,v ▸ same⟩
  · have exp : W=4*2^(k-2) := by
      dsimp [W]; conv_lhs => rw [show k=(k-2)+2 by omega,pow_add]
      ring
    have le : n≤2^(k-2) := by change 4*n≤W at large; omega
    obtain ⟨w,b,v,c⟩ := OMA.PathShift.pack k 1 r (k-2) (by omega) (by omega) (Nat.sub_le ..)
    have hit : weight w=W+r := by simpa [W] using v
    refine ⟨w,b,by omega,by rw [hit]; change 4*n≤W at large; omega,?_⟩
    rw [hit]; exact Nat.add_modEq_left.trans same

theorem full_modulus {I : Type*} [Fintype I] [DecidableEq I] {N : ℕ} [NeZero N]
    (L : I→ℕ) (x : I→ZMod N) (inj : Function.Injective (label L x)) (ok : IsValidMod (univ.image (label L x)))
    (J : I) (kp : 2≤L J) (large : 4*(∑ i,L i)≤2^(L J)) (kill : 2^(L J) • x J=0) :
    2^(∑ i,L i)≤N := by
  classical
  let f (s : Box L) := ∑ i,(s i).val • x i
  let wins (s t : Box L) := ∑ i∈univ.erase J,if t i<s i then 1 else 0
  have go (s t : Box L) (eq : f s=f t) (order : wins s t≤wins t s) : s=t := by
    let c (i : I) := full (L i)+(s i).val-(t i).val
    have e (i) : c i+(t i).val=full (L i)+(s i).val := by
      have lt := (t i).isLt; dsimp [c,full]; omega
    choose z zb zw zc using (fun i=>displaced (s i).isLt (t i).isLt)
    obtain ⟨w,wb,wc,wide,cong⟩ := adjust (original:=c J) kp large
    let v := Function.update z J w
    have vb (i : I) : Bounded (L i) (v i) := by
      by_cases same : i=J
      · subst i; simpa [v] using wb
      · simpa [v,same] using zb i
    have budget := sum_le_sum (s:=univ.erase J) (fun i _=>zc i)
    simp only [sum_add_distrib] at budget
    change (∑ i∈univ.erase J,(z i).length)+wins t s≤(∑ i∈univ.erase J,L i)+wins s t at budget
    have outside : (∑ i∈univ.erase J,(z i).length)≤∑ i∈univ.erase J,L i := by omega
    have tiny : (∑ i,(v i).length)≤∑ i,L i := by
      rw [←sum_erase_add _ (fun i=>(v i).length) (mem_univ J),←sum_erase_add _ L (mem_univ J)]
      have o : (∑ i∈univ.erase J,(v i).length)=∑ i∈univ.erase J,(z i).length :=
        sum_congr rfl (fun i hi=>by simp [v,(mem_erase.mp hi).1])
      rw [o]; simpa [v] using Nat.add_le_add outside wc
    have cap : (∑ i,L i)≤∑ i,weight (v i) := by
      apply le_trans _ (single_le_sum (fun _ _=>Nat.zero_le _) (mem_univ J))
      simpa [v] using wide
    have ar (i) : weight (v i) • x i=c i • x i := by
      by_cases ij : i=J
      · subst i; simp only [v,Function.update_self]
        exact nsmul_eq_nsmul_iff_modEq.mpr (cong.of_dvd (addOrderOf_dvd_iff_nsmul_eq_zero.mpr kill))
      · simp only [v,Function.update_of_ne ij,zw]; rfl
    have mass : (∑ i,weight (v i) • x i)=∑ i,full (L i) • x i := by
      simp only [ar]
      apply add_right_cancel (b:=f t)
      change _+(∑ i,(t i).val • x i)=_+_
      conv_lhs => rw [←sum_add_distrib]
      simp only [←add_nsmul,e]
      simp only [add_nsmul,sum_add_distrib]
      exact congrArg (fun a=>(∑ i,full (L i) • x i)+a) eq
    have fullword := rigid L x inj ok v vb tiny cap mass
    funext i
    apply Fin.ext
    by_cases ij : i=J
    · subst i
      have rel : full (L J)≡c J [MOD 2^L J] := by
        simpa only [←fullword J,v,Function.update_self] using cong
      have same := rel.add_right (t J).val
      rw [e] at same
      exact (Nat.ModEq.add_left_cancel' (full (L J)) same).symm.eq_of_lt_of_lt (s J).isLt (t J).isLt
    · have exactWord := fullword i
      simp only [v,Function.update_of_ne ij,zw] at exactWord
      change c i=full (L i) at exactWord
      have := e i; omega
  have fi : Function.Injective f := by
    intro s t e
    rcases le_total (wins s t) (wins t s) with h|h
    · exact go s t e h
    · exact (go t s e.symm h).symm
  have sz := Fintype.card_le_of_injective f fi
  simpa [Box,Fintype.card_pi,prod_pow_eq_pow_sum] using sz

end OMA.PathPeriod
