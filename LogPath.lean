import PathReturn
import LogCycle

/-! A single sufficiently long affine doubling path gives the sharp
    unrestricted modulus bound, regardless of all exterior labels. -/

open private OMA.LongCycle.translate from LongCycle
namespace OMA.LogPath
open Finset OMA.PathReserve Arxiv.«2607.08366»

theorem continuation {N L : ℕ} [NeZero N] {A : Finset (ZMod N)} {x : ZMod N}
    (c : Chain A x L) (ok : IsValidMod A) (hn : 2≤A.card)
    (large : 16*A.card*(A.card+15)≤2^L) (lt : N<2^A.card) :
    ∃ (M a : ℕ), L≤M ∧ Chain A x M ∧ a<M ∧ 2^M • x=2^a • x ∧
      2^a≤M ∧ 16*(A.card+15)≤2^(M-a) := by
  classical
  let P := (range (A.card+1)).filter (fun i=>Chain A x i)
  have mem (i : ℕ) (p : Chain A x i) : i∈P := by
    have card := (row_size p).symm.trans_le (card_le_card (row_sub p))
    exact mem_filter.mpr ⟨mem_range.mpr (by omega),p⟩
  let M := P.max' ⟨L,mem L c⟩
  have stays : Chain A x M := (mem_filter.mp (P.max'_mem _)).2
  have ml : L≤M := P.le_max' _ (mem L c)
  have full := large.trans (Nat.pow_le_pow_right (by decide : 0<2) ml)
  have ell : 4≤M := by
    by_contra! bad
    have p := Nat.pow_le_pow_right (by decide : 0<2) (show M≤3 by omega)
    norm_num at p; nlinarith
  have hit := OMA.PathReturn.successor ok stays ell full lt
  have closes : 2^M • x∈row x M := by
    by_contra no
    have ext : Chain A x (M+1) := by
      constructor
      · intro i hi j hj eq
        have il := mem_range.mp hi; have jl := mem_range.mp hj
        by_cases a : i=M
        · subst i; by_contra ne
          apply no
          exact mem_image.mpr ⟨j,mem_range.mpr (by omega),eq.symm⟩
        by_cases b : j=M
        · subst j
          exact False.elim (no (mem_image.mpr ⟨i,mem_range.mpr (by omega),eq⟩))
        exact stays.distinct (mem_range.mpr (by omega)) (mem_range.mpr (by omega)) eq
      · intro j hj
        by_cases e : j=M
        · exact e ▸ hit
        · exact stays.inside j (by omega)
    have bad := P.le_max' _ (mem _ ext)
    change M+1≤M at bad; omega
  obtain ⟨a,am,e⟩ := mem_image.mp closes
  have less := mem_range.mp am
  have pow := Nat.pow_lt_pow_right (by decide : 1<2) less
  have dvd := (Nat.modEq_iff_dvd' pow.le).mp (nsmul_eq_nsmul_iff_modEq.mp e)
  have up := Nat.le_of_dvd (Nat.sub_pos_of_lt pow) dvd
  have lb := order stays ok
  have transient : 2^a≤M := by omega
  have cm := (row_size stays).symm.trans_le (card_le_card (row_sub stays))
  have w : 2^M=2^a*2^(M-a) := by rw [←pow_add,show a+(M-a)=M by omega]
  have major := Nat.mul_le_mul_right (2^(M-a)) (transient.trans cm)
  refine ⟨M,a,ml,stays,less,e.symm,transient,?_⟩
  rw [w] at full
  have z : A.card*(16*(A.card+15))≤A.card*2^(M-a) := by nlinarith
  exact Nat.le_of_mul_le_mul_left z (by omega)

theorem cycle {N n L : ℕ} [NeZero N] (hn : 2≤n) (A : Finset (ZMod N)) (card : A.card=n)
    (ok : IsValidMod A) (x t : ZMod N) (inj : Set.InjOn (fun j : ℕ=>2^j • x) (range L : Finset ℕ))
    (inc : ∀ j<L,2^j • x-t∈A) (large : 16*n*(n+15)≤2^L) (lt : N<2^n) :
    ∃ (r : ℕ) (y : ZMod N), 0<r ∧ 16*(n+15)≤2^r ∧ 2^r • y=y ∧
      Set.InjOn (fun j : ℕ=>2^j • y) (range r : Finset ℕ) ∧ ∀ j<r,2^j • y-t∈A := by
  classical
  let A' := A.image (fun z=>z+t)
  have ca : A'.card=n := (card_image_of_injective A (fun _ _ e=>add_right_cancel e)).trans card
  have c : Chain A' x L := ⟨inj,fun j hj=>mem_image.mpr ⟨_,inc j hj,sub_add_cancel ..⟩⟩
  obtain ⟨M,a,_,stays,am,endpt,_,bound⟩ := continuation c (OMA.LongCycle.translate A ok t)
    (ca ▸ hn) (ca ▸ large) (ca ▸ lt)
  let r := M-a
  let y := 2^a • x
  have id (i : ℕ) : 2^i • y=2^(i+a) • x := by simp [y,pow_add,mul_smul]
  have dims : r+a=M := by dsimp [r]; omega
  refine ⟨r,y,by dsimp [r]; omega,ca ▸ bound,(id r).trans (dims ▸ endpt),?_,?_⟩
  · intro i hi j hj e
    change 2^i • y=2^j • y at e; rw [id,id] at e
    have ih := mem_range.mp hi; have jh := mem_range.mp hj
    have same := stays.distinct (mem_range.mpr (by omega)) (mem_range.mpr (by omega)) e
    omega
  · intro i hi
    rw [id]
    obtain ⟨b,ba,be⟩ := mem_image.mp (stays.inside (i+a) (by omega))
    exact (eq_sub_iff_add_eq.mpr be) ▸ ba

theorem lower {N n L : ℕ} [NeZero N] (hn : 2≤n) (A : Finset (ZMod N)) (card : A.card=n)
    (ok : IsValidMod A) (x t : ZMod N) (inj : Set.InjOn (fun j : ℕ=>2^j • x) (range L : Finset ℕ))
    (inc : ∀ j<L,2^j • x-t∈A) (large : 16*n*(n+15)≤2^L) : minModulus n≤N := by
  by_cases lt : N<2^n
  · obtain ⟨r,y,rp,threshold,wrap,distinct,inside⟩ := cycle hn A card ok x t inj inc large lt
    exact OMA.LogCycle.lower hn rp A card ok y t wrap distinct inside (by omega)
  · exact (Nat.sub_le (2^n) _).trans (by omega)

end OMA.LogPath
