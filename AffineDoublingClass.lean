import AffineDoubling
import DyadicDigits

/-! Classification of the moduli of valid affine-doubling-closed sets. -/

open private OMA.AffineDoubling.total from AffineDoubling

namespace OMA.AffineDoublingClass
open Finset Function Arxiv.«2607.08366»
open OMA.DyadicDigits

private lemma total_iff {N : ℕ} (A : Finset (ZMod N)) :
    IsValidMod A ↔ ∀ m : Multiset (ZMod N), (∀ z∈m,z∈A) → m.card=A.card →
      m.sum=∑ z∈A,z → m=A.val := by
  classical
  refine ⟨OMA.AffineDoubling.total A,?_⟩
  intro fully c sz mass x hx
  let m : Multiset (ZMod N) := ∑ z∈A,Multiset.replicate (c z) z
  have count (a : ZMod N) : m.count a=if a∈A then c a else 0 := by
    change Multiset.count a ((A.val.map (fun z=>Multiset.replicate (c z) z)).sum)=_
    rw [Multiset.count_sum]
    change (∑ z∈A,(Multiset.replicate (c z) z).count a)=_
    simp [Multiset.count_replicate]
  have inside (a : ZMod N) (ha : a∈m) : a∈A := by
    by_contra no
    have lt := Multiset.count_pos.mpr ha
    rw [count,if_neg no] at lt
    omega
  have eq := fully m inside (by simp [m,Multiset.card_sum,sz]) (by
    simpa [m,Multiset.sum_sum,Multiset.sum_replicate,nsmul_eq_mul] using mass)
  have e := congrArg (Multiset.count x) eq
  rw [count,if_pos hx,Multiset.count_eq_one_of_mem A.nodup hx] at e
  exact e

private lemma pack_sum {N : ℕ} (a x : ZMod N) (s : Multiset ℕ) :
    (s.map (fun j=>2^j • x+a)).sum=value s • x+s.card • a := by
  induction s using Multiset.induction_on with
  | empty => simp [value]
  | cons j s ih =>
    rw [Multiset.map_cons,Multiset.sum_cons,ih,value_cons,Multiset.card_cons,add_nsmul,succ_nsmul]
    abel

/-- On n distinct members of a dyadic progression, the homogeneous
    multiset condition is exactly binary-word uniqueness modulo ord(x). -/
theorem orbit_iff {N n : ℕ} (a x : ZMod N) (A : Finset (ZMod N)) (card : A.card=n)
    (orbit : A=(range n).image (fun j=>2^j • x+a)) :
    IsValidMod A ↔ Valid n (addOrderOf x) := by
  classical
  let f (j : ℕ) := 2^j • x+a
  have im : A=(range n).image f := orbit
  have inj : Set.InjOn f (range n : Finset ℕ) := card_image_iff.mp (by rw [←im,card,card_range])
  have all : (range n).val.map f=A.val := by rw [im,image_val_of_injOn inj]
  let inv (z : ZMod N) : ℕ := if h : ∃ j∈range n,f j=z then h.choose else 0
  have pre (z : ZMod N) (hz : z∈A) : inv z∈range n ∧ f (inv z)=z := by
    have e := mem_image.mp (im ▸ hz)
    simpa only [inv,dif_pos e] using e.choose_spec
  have left (j : ℕ) (hj : j∈range n) : inv (f j)=j := by
    have ⟨b,e⟩ := pre (f j) (im ▸ mem_image_of_mem f hj)
    exact inj b hj e
  have same (s : Multiset ℕ) (bd : ∀ j∈s,j<n) : (s.map f).map inv=s := by
    rw [Multiset.map_map]
    simpa only [Multiset.map_id] using
      (Multiset.map_congr rfl (fun j hj=>left j (mem_range.mpr (bd j hj))) :
        s.map (inv ∘ f)=s.map id)
  have fullSum : (2^n-1) • x+n • a=∑ z∈A,z := by
    have e := congrArg Multiset.sum all
    rw [pack_sum,value_range] at e
    change _=(Multiset.map id A.val).sum
    rw [Multiset.map_id]
    simpa only [←Finset.card_def,card_range] using e
  rw [total_iff]
  constructor
  · intro ok s bd sz hit
    have hit' := (nsmul_eq_nsmul_iff_modEq (x:=x)).mpr hit
    have q := ok (s.map f) (by
      intro z hz; obtain ⟨j,hj,rfl⟩ := Multiset.mem_map.mp hz
      rw [im]; exact mem_image_of_mem _ (mem_range.mpr (bd j hj)))
      (by simp only [Multiset.card_map,sz,card]) (by rw [pack_sum,sz,hit',fullSum])
    have e := congrArg (Multiset.map inv) (q.trans all.symm)
    rwa [same s bd,same (range n).val (fun j hj=>mem_range.mp hj)] at e
  · intro ok m ins sz mass
    let s := m.map inv
    have back : s.map f=m := by
      rw [show s=m.map inv by rfl,Multiset.map_map]
      simpa only [Multiset.map_id] using
        (Multiset.map_congr rfl (fun z hz=>(pre z (ins z hz)).2) : m.map (f ∘ inv)=m.map id)
    have sl : s.card=n := (Multiset.card_map ..).trans (sz.trans card)
    have hit : value s ≡ 2^n-1 [MOD addOrderOf x] := by
      apply nsmul_eq_nsmul_iff_modEq.mp
      apply add_right_cancel (b:=n • a)
      rw [←sl,←pack_sum,back,mass,sl,fullSum]
    have eq := ok s (by
      intro j hj
      obtain ⟨z,hz,rfl⟩ := Multiset.mem_map.mp hj
      exact mem_range.mp (pre z (ins z hz)).1) sl hit
    exact back.symm.trans ((congrArg (Multiset.map f) eq).trans all)

private lemma affine_iter {G : Type*} [AddCommGroup G] (u t : G) (k : ℕ) :
    (fun a : G=>2 • a+t)^[k] u=2^k • (u+t)-t := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iterate_succ_apply',ih,pow_succ',mul_smul,two_nsmul,two_nsmul]
    abel

/-- Both the orbit shape and the precise additive order of its step are
    forced.  The integer b is the position at which doubling first returns. -/
theorem structure_of_closed {N n : ℕ} [NeZero N] (hn : 2≤n)
    (A : Finset (ZMod N)) (card : A.card=n) (ok : IsValidMod A) (t : ZMod N)
    (closed : ∀ a∈A,2 • a+t∈A) :
    ∃ (x : ZMod N) (b : ℕ), b<n ∧ 2^b≤n ∧ addOrderOf x=2^n-2^b ∧
      A=(range n).image (fun j=>2^j • x-t) := by
  classical
  obtain ⟨u,hu,im⟩ := OMA.AffineDoubling.closed_orbit ok (card_pos.mp (by omega)) t closed
  let x := u+t
  have im' : A=(range n).image (fun j=>2^j • x-t) := by
    simpa only [affine_iter,card] using im
  have stay (k : ℕ) : (fun a : ZMod N=>2 • a+t)^[k] u∈A := by
    induction k with
    | zero => exact hu
    | succ k ih => rw [iterate_succ_apply']; exact closed _ ih
  have mem := stay n
  rw [affine_iter,im'] at mem
  obtain ⟨b,bR,eq⟩ := mem_image.mp mem
  have bn := mem_range.mp bR
  have eq' : 2^b • x=2^n • x := sub_left_inj.mp eq
  have p : (2:ℕ)^b<2^n := Nat.pow_lt_pow_right (by decide) bn
  have dvd : addOrderOf x ∣ 2^n-2^b :=
    (Nat.modEq_iff_dvd' p.le).mp (nsmul_eq_nsmul_iff_modEq.mp eq')
  have ordpos := addOrderOf_pos x
  have val := (orbit_iff (-t) x A card (by simpa only [←sub_eq_add_neg] using im')).mp ok
  have lo := OMA.DyadicDigits.lower ordpos val
  have bound : 2*n≤2^n := by
    obtain ⟨k,rfl⟩ : ∃ k,n=k+1 := ⟨n-1,by omega⟩
    rw [pow_succ]; have := k.lt_two_pow_self; omega
  have exactOrder : addOrderOf x=2^n-2^b := by
    obtain ⟨k,dk⟩ := dvd
    by_contra no
    have one : k≠1 := fun e=>no (by simpa [e] using dk.symm)
    have zero : k≠0 := fun e=>by simp [e] at dk; omega
    have lb := Nat.mul_le_mul_left (addOrderOf x) (show 2≤k by omega)
    rw [←dk] at lb
    have pb : 0<2^b := by positivity
    omega
  exact ⟨x,b,bn,by omega,exactOrder,im'⟩

/-- A valid affine-doubling-closed n-element set exists in Z/N exactly
    at the multiples of 2^n−2^b, for 0≤b with 2^b≤n. -/
theorem modulus_classification {N n : ℕ} [NeZero N] (hn : 2≤n) :
    (∃ (A : Finset (ZMod N)) (t : ZMod N),A.card=n ∧ IsValidMod A ∧
      ∀ a∈A,2 • a+t∈A) ↔ ∃ b : ℕ,b<n ∧ 2^b≤n ∧ (2^n-2^b)∣N := by
  classical
  constructor
  · rintro ⟨A,t,card,ok,closed⟩
    obtain ⟨x,b,bn,p,ord,_⟩ := structure_of_closed hn A card ok t closed
    have d := addOrderOf_dvd_natCard x
    rw [Nat.card_eq_fintype_card,ZMod.card,ord] at d
    exact ⟨b,bn,p,d⟩
  · rintro ⟨b,bn,p,k,nk⟩
    let M := 2^n-2^b
    have small : (2:ℕ)^b<2^n := Nat.pow_lt_pow_right (by decide) bn
    have mp : 0<M := Nat.sub_pos_of_lt small
    have np := NeZero.pos N
    have kp : 0<k := by
      by_contra! no
      have z : k=0 := by omega
      simp [z] at nk
      omega
    let x := (k : ZMod N)
    have kd : k∣N := ⟨M,by simpa [M,mul_comm] using nk⟩
    have ord : addOrderOf x=M := by
      rw [show x=(k : ZMod N) by rfl,ZMod.addOrderOf_coe _ np.ne',Nat.gcd_eq_right kd,nk]
      exact Nat.mul_div_cancel _ kp
    let v (j : ℕ) : ZMod N := 2^j • x
    let A := (range n).image v
    have half (j : ℕ) (hj : j<n) : 2^j ≤ M := by
      have le := Nat.pow_le_pow_right (by decide : 0<2) (show j≤n-1 by omega)
      have le' := Nat.pow_le_pow_right (by decide : 0<2) (show b≤n-1 by omega)
      have db : 2^n=2^(n-1)*2 := by rw [←Nat.pow_succ]; congr 1; omega
      dsimp only [M]; omega
    have notEq (j l : ℕ) (jl : j<l) (ln : l<n) : v j≠v l := by
      intro eq
      have lt := Nat.pow_lt_pow_right (by decide : 1<2) jl
      have d := (Nat.modEq_iff_dvd' lt.le).mp (nsmul_eq_nsmul_iff_modEq.mp eq)
      rw [ord] at d
      have lb := Nat.le_of_dvd (Nat.sub_pos_of_lt lt) d
      have h := half l ln
      have ne : 0<2^j := by positivity
      omega
    have inj : Set.InjOn v (range n : Finset ℕ) := by
      intro j hj l hl eq
      rcases lt_trichotomy j l with a|e|a
      · exact False.elim (notEq _ _ a (mem_range.mp hl) eq)
      · exact e
      · exact False.elim (notEq _ _ a (mem_range.mp hj) eq.symm)
    have card : A.card=n := (card_image_of_injOn inj).trans (card_range _)
    refine ⟨A,0,card,(orbit_iff 0 x A card (by simp [A,v])).mpr ?_,?_⟩
    · rw [ord]; exact valid_of_threshold bn p
    · intro a ha
      obtain ⟨j,hj,rfl⟩ := mem_image.mp ha
      have e : 2 • v j+0=v (j+1) := by simp only [v,add_zero,pow_succ',mul_smul]
      rw [e]
      have jl := mem_range.mp hj
      by_cases ss : j+1<n
      · exact mem_image_of_mem v (mem_range.mpr ss)
      · have je : j+1=n := by omega
        have vb : v b=v n := nsmul_eq_nsmul_iff_modEq.mpr ((Nat.modEq_iff_dvd' small.le).mpr (by rw [ord]))
        rw [je,←vb]; exact mem_image_of_mem v (mem_range.mpr bn)

/-- The restricted optimum is precisely Fonollosa's predicted number. -/
theorem optimum {n : ℕ} (hn : 2≤n) : IsLeast
    {N : ℕ | 0<N ∧ ∃ (A : Finset (ZMod N)) (t : ZMod N),A.card=n ∧
      IsValidMod A ∧ ∀ a∈A,2 • a+t∈A} (minModulus n) := by
  have pn : n≠0 := by omega
  have hpos := minModulus_pos (by omega : 0<n)
  constructor
  · have : NeZero (minModulus n) := ⟨hpos.ne'⟩
    exact ⟨hpos,(modulus_classification hn).mpr ⟨Nat.log 2 n,Nat.log_lt_self 2 pn,
      Nat.pow_log_le_self 2 pn,dvd_refl _⟩⟩
  · intro N h
    obtain ⟨np,ex⟩ := h
    have : NeZero N := ⟨np.ne'⟩
    obtain ⟨b,_,hb,dvd⟩ := (modulus_classification hn).mp ex
    have l := (Nat.le_log_iff_pow_le (by decide : 1<2) pn).mpr hb
    have power := Nat.pow_le_pow_right (by decide : 0<2) l
    exact (Nat.sub_le_sub_left power _).trans (Nat.le_of_dvd np dvd)

/-- At the optimum the orbit step is a unit, so there is a single affine
    equivalence class of valid closed sets. -/
theorem extremal_shape {n : ℕ} (hn : 2≤n) (A : Finset (ZMod (minModulus n)))
    (card : A.card=n) (ok : IsValidMod A) (t : ZMod (minModulus n))
    (closed : ∀ a∈A,2 • a+t∈A) :
    ∃ u : (ZMod (minModulus n))ˣ,A=(range n).image (fun j=>2^j • (u : ZMod (minModulus n))-t) := by
  have pn : n≠0 := by omega
  have np := minModulus_pos pn.bot_lt
  have : NeZero (minModulus n) := ⟨np.ne'⟩
  obtain ⟨x,b,_,hb,ord,shape⟩ := structure_of_closed hn A card ok t closed
  have l := (Nat.le_log_iff_pow_le (by decide : 1<2) pn).mpr hb
  have power := Nat.pow_le_pow_right (by decide : 0<2) l
  have below : minModulus n≤addOrderOf x := by rw [ord]; exact Nat.sub_le_sub_left power _
  have dvd := addOrderOf_dvd_natCard x
  rw [Nat.card_eq_fintype_card,ZMod.card] at dvd
  have full := le_antisymm (Nat.le_of_dvd np dvd) below
  have eq := ZMod.addOrderOf_coe x.val np.ne'
  rw [ZMod.natCast_zmod_val,full] at eq
  have cop : x.val.Coprime (minModulus n) := by
    rw [Nat.coprime_comm]
    change (minModulus n).gcd x.val=1
    have pos := Nat.gcd_pos_of_pos_left x.val np
    by_contra ne
    have smaller := Nat.div_lt_self np (show 1<(minModulus n).gcd x.val by omega)
    omega
  have unit := (ZMod.isUnit_iff_coprime x.val _).mpr cop
  rw [ZMod.natCast_zmod_val] at unit
  exact ⟨unit.unit,by simpa only [unit.unit_spec] using shape⟩

end OMA.AffineDoublingClass
