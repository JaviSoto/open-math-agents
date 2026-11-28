import CycleTerminal

/-! A complete doubling cycle together with an independent involution.
    The extra affine class exists in every even size at least four. -/

open private OMA.CyclePacking.grow from CyclePacking
open private OMA.AffineDoubling.total from AffineDoubling
open private OMA.BinaryPrefix.sum_bits from BinaryPrefix
namespace OMA.SplitCycle
open Finset Arxiv.«2607.08366»

private lemma zero_word {N : ℕ} {C : Finset (ZMod N)} (ok : IsValidMod C)
    (pred : ∀ a∈C,∃ b∈C,2 • b=a) (zero : (∑ a∈C,a)=0)
    (s : Multiset (ZMod N)) (ins : ∀ x∈s,x∈C) (mass : s.sum=0)
    (small : s.card<C.card) : s=0 := by
  classical
  by_contra ne
  have pos := Multiset.card_pos.mpr ne
  obtain ⟨u,ui,uc,us⟩ := OMA.CyclePacking.grow C pred s ins ne (C.card-1) (by omega)
  obtain ⟨a,ha⟩ := Multiset.card_pos_iff_exists_mem.mp (by omega : 0<u.card)
  obtain ⟨v,ev⟩ := Multiset.exists_cons_of_mem ha
  obtain ⟨b,bc,eq⟩ := pred a (ui a ha)
  let z := b ::ₘ b ::ₘ v
  have e := OMA.AffineDoubling.total C ok z (by
    intro x hx
    simp only [z,Multiset.mem_cons] at hx
    rcases hx with rfl|rfl|mem
    · exact bc
    · exact bc
    · exact ui _ (ev ▸ Multiset.mem_cons_of_mem mem))
    (by rw [ev,Multiset.card_cons] at uc; simp only [z,Multiset.card_cons]; omega)
    (by rw [←mass,←us,ev,←eq] at zero
        simp only [z,Multiset.sum_cons] at zero ⊢
        simpa only [two_nsmul,add_assoc] using zero.symm)
  have nd := C.nodup
  rw [←e] at nd
  simp [z] at nd

/-- The direct sum of an odd cycle and an involution in the opposite
    parity class is valid. -/
theorem insert_involution {N : ℕ} (C : Finset (ZMod N)) (ok : IsValidMod C)
    (odd : Odd C.card) (zero : (∑ a∈C,a)=0) (pred : ∀ a∈C,∃ b∈C,2 • b=a)
    (x : ZMod N) (kill : 2 • x=0) (π : ZMod N →+ ZMod 2)
    (pc : ∀ a∈C,π a=0) (px : π x=1) : IsValidMod (insert x C) := by
  classical
  have xc : x∉C := fun h=>by have e := pc x h; rw [px] at e; exact one_ne_zero e
  intro c sz sm a ha
  rw [sum_insert xc,card_insert_of_notMem xc] at sz
  rw [sum_insert xc,sum_insert xc,zero,add_zero] at sm
  let s : Multiset (ZMod N) := ∑ z∈C,Multiset.replicate (c z) z
  have wc : s.card=∑ z∈C,c z := by simp [s,Multiset.card_sum]
  have ws : s.sum=∑ z∈C,(c z : ZMod N)*z := by
    simp [s,Multiset.sum_sum,Multiset.sum_replicate,nsmul_eq_mul]
  have hsum : c x • x+s.sum=x := by simpa only [ws,nsmul_eq_mul] using sm
  have pz : π s.sum=0 := by
    rw [ws,map_sum]
    apply sum_eq_zero
    intro z hz
    rw [←nsmul_eq_mul,map_nsmul,pc z hz,smul_zero]
  have co : (c x : ZMod 2)=1 := by
    have e := congrArg π hsum
    rw [map_add,map_nsmul,px,pz,add_zero,nsmul_eq_mul,mul_one] at e
    exact e
  have oc : Odd (c x) := by
    by_contra h
    obtain ⟨l,el⟩ := Nat.not_odd_iff_even.mp h
    rw [el,Nat.cast_add,←two_mul] at co
    rw [show (2:ZMod 2)=0 from rfl,zero_mul] at co
    exact zero_ne_one co
  obtain ⟨u,eu⟩ := oc
  have scaled : c x • x=x := by rw [eu,add_nsmul,mul_comm 2,mul_smul,kill,smul_zero,one_nsmul,zero_add]
  rw [scaled,add_eq_left] at hsum
  have one : c x=1 := by
    by_contra ne
    have small : s.card<C.card := by omega
    have ins (z : ZMod N) (mem : z∈s) : z∈C := by
      by_contra nz
      have hk := Multiset.count_pos.mpr mem
      change 0<Multiset.count z ((C.val.map (fun a=>Multiset.replicate (c a) a)).sum) at hk
      rw [Multiset.count_sum] at hk
      change 0<(∑ a∈C,(Multiset.replicate (c a) a).count z) at hk
      simp [Multiset.count_replicate,nz] at hk
    have em := zero_word ok pred zero s ins hsum small
    have ec : s.card=0 := by rw [em,Multiset.card_zero]
    have same : c x=C.card+1 := by omega
    obtain ⟨l,el⟩ := odd
    omega
  rcases mem_insert.mp ha with rfl|ac
  · exact one
  · exact ok c (by omega) (by rw [←ws,hsum,zero]) a ac

/-- Such a split set is closed under no affine doubling map if it contains
    a nontrivial cycle avoiding zero. -/
theorem not_closed {N : ℕ} (C : Finset (ZMod N)) (big : 2≤C.card) (nz : 0∉C)
    (pred : ∀ a∈C,∃ b∈C,2 • b=a) (x : ZMod N) (kill : 2 • x=0)
    (π : ZMod N→+ZMod 2) (pc : ∀ a∈C,π a=0) (px : π x=1) :
    ¬ ∃ u : ZMod N,∀ a∈insert x C,2 • a+u∈insert x C := by
  classical
  rintro ⟨u,closed⟩
  have shift (a : ZMod N) (ac : a∈C) : a+u∈insert x C := by
    obtain ⟨b,bc,back⟩ := pred a ac
    rw [←back]; exact closed b (mem_insert_of_mem bc)
  have uc : u∈insert x C := by simpa only [kill,zero_add] using closed x (mem_insert_self ..)
  by_cases zero : π u=0
  · have ux : u≠x := fun e=>by rw [e,px] at zero; exact one_ne_zero zero
    have inside := (mem_insert.mp uc).resolve_left ux
    let D := C.image (fun a=>a+u)
    have sub : D⊆C := by
      intro a ha
      obtain ⟨b,bc,rfl⟩ := mem_image.mp ha
      apply (mem_insert.mp (shift b bc)).resolve_left
      intro e; have h := congrArg π e
      rw [map_add,pc b bc,zero,zero_add,px] at h
      exact zero_ne_one h
    have eq : D=C := eq_of_subset_of_card_le sub (by
      rw [show D=C.image (fun a=>a+u) from rfl,card_image_of_injective _ (fun _ _ e=>add_right_cancel e)])
    obtain ⟨a,ac,e⟩ := mem_image.mp (eq ▸ inside : u∈D)
    exact nz (add_eq_right.mp e ▸ ac)
  · have unique (a : ZMod N) (ha : a∈C) : a+u=x := by
      apply (mem_insert.mp (shift a ha)).resolve_right
      intro h
      exact zero (by simpa only [map_add,pc a ha,zero_add] using pc _ h)
    have sm : C.card≤1 := card_le_one.mpr (fun a ha b hb=>add_right_cancel ((unique a ha).trans (unique b hb).symm))
    omega

/-- Explicit infinite family: in modulus 2(2^r−1), take the even dyadic
    cycle and adjoin the unique element of order two. -/
theorem examples (r : ℕ) (hr : 2≤r) (odd : Odd r) :
    let N := 2*(2^r-1)
    ∃ A : Finset (ZMod N), A.card=r+1 ∧ IsValidMod A ∧
      ¬∃ u : ZMod N,∀ a∈A,2 • a+u∈A := by
  classical
  let M := 2^r-1
  let N := 2*M
  let y : ZMod N := (2:ℕ)
  let x : ZMod N := M
  let f (j : ℕ) := 2^j • y
  let C := (range r).image f
  let π := ZMod.castHom (show 2∣N from ⟨M,rfl⟩) (ZMod 2)
  have exp : 2^r=2*2^(r-1) := by rw [←pow_succ',show r-1+1=r by omega]
  have pos : 0<2^(r-1) := by positivity
  have more : 1<2^(r-1) := Nat.one_lt_two_pow (by omega)
  have mp : 0<M := by dsimp [M]; omega
  have np : 0<N := by dsimp [N]; omega
  have ord : addOrderOf y=M := by
    rw [show y=((2:ℕ):ZMod N) from rfl,ZMod.addOrderOf_coe _ np.ne']
    change 2*M/(2*M).gcd 2=M
    rw [Nat.gcd_mul_right_left]; omega
  have small (j : ℕ) (hj : j<r) : 2^j<M := by
    have le := Nat.pow_le_pow_right (by decide : 0<2) (show j≤r-1 by omega)
    dsimp [M]; omega
  have inj : Set.InjOn f (range r : Finset ℕ) := by
    intro a ha b hb e
    have h := nsmul_eq_nsmul_iff_modEq.mp e
    rw [ord] at h
    exact Nat.pow_right_injective (by decide : 2≤2)
      (h.eq_of_lt_of_lt (small _ (mem_range.mp ha)) (small _ (mem_range.mp hb)))
  have cs : C.card=r := (card_image_of_injOn inj).trans (card_range _)
  have valid : IsValidMod C := by
    apply (OMA.AffineDoublingClass.orbit_iff 0 y C cs (by simp [C,f])).mpr
    rw [ord]; exact OMA.DyadicDigits.valid_of_threshold (t:=0) (by omega) (by simp; omega)
  have wrap : 2^r • y=y := by
    nth_rw 2 [←one_nsmul y]
    apply nsmul_eq_nsmul_iff_modEq.mpr
    rw [ord]
    exact ((Nat.modEq_iff_dvd' Nat.one_le_two_pow).mpr (dvd_refl _)).symm
  have sc : (∑ a∈C,a)=0 := by
    change (∑ a∈(range r).image f,a)=0
    rw [sum_image inj]
    change (∑ j∈range r,2^j • y)=0
    rw [←sum_smul,OMA.BinaryPrefix.sum_bits,←show addOrderOf y=2^r-1 from ord,addOrderOf_nsmul_eq_zero]
  have pc (a : ZMod N) (ha : a∈C) : π a=0 := by
    obtain ⟨j,_,rfl⟩ := mem_image.mp ha
    change π (2^j • ((2:ℕ):ZMod N))=0
    rw [map_nsmul,map_natCast]
    simp only [show ((2:ℕ):ZMod 2)=0 from rfl,smul_zero]
  have px : π x=1 := by
    change π (M:ZMod N)=1
    rw [map_natCast]
    apply (ZMod.natCast_eq_natCast_iff M 1 2).mpr
    change (2^r-1)%2=1%2
    omega
  have kill : 2 • x=0 := by
    change 2 • (M:ZMod N)=0
    simpa only [nsmul_eq_mul,←Nat.cast_mul] using ZMod.natCast_self N
  have xc : x∉C := fun h=>by have e := pc x h; rw [px] at e; exact one_ne_zero e
  have nz : 0∉C := by
    intro h
    obtain ⟨j,hj,eq⟩ := mem_image.mp h
    have d := addOrderOf_dvd_iff_nsmul_eq_zero.mpr eq
    rw [ord] at d
    exact (not_le_of_gt (small _ (mem_range.mp hj))) (Nat.le_of_dvd (by positivity) d)
  have pred := (OMA.CycleTerminal.turn (by omega : 0<r) y wrap C rfl).2
  exact ⟨insert x C,by rw [card_insert_of_notMem xc,cs],
    insert_involution C valid (cs ▸ odd) sc pred x kill π.toAddMonoidHom pc px,
    not_closed C (cs ▸ hr) nz pred x kill π.toAddMonoidHom pc px⟩

end OMA.SplitCycle
