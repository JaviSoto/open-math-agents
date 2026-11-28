import PathReserve

/-! Coin costs for a bounded change in return time. -/

open private OMA.BinaryPrefix.digits from BinaryPrefix
open private OMA.PathShift.pack from PathShift
namespace OMA.PathGapCoins
open Finset OMA.PathCoins OMA.PathReserve Arxiv.«2607.08366»

section
variable {N L : ℕ} {A : Finset (ZMod N)} {x : ZMod N} (c : Chain A x L) (ok : IsValidMod A)
include c ok

private theorem from_coins (T : Finset (ZMod N)) (ts : T⊆A\row x L)
    (m : Multiset (ZMod N)) (ms : ∀ z∈m,z∈A\row x L)
    {a b z : ℕ} (shift : z+a=2^L-1+b) (eq : v T+a • x=m.sum+b • x) (cap : A.card≤z)
    (coins : ∃ w : List ℕ,Bounded L w ∧ weight w=z ∧ w.length+m.card≤L+T.card) :
    m=T.val ∧ z≤2^L-1 := by
  obtain ⟨w,wb,wt,len⟩ := coins
  have mass : weight w • x+m.sum=(2^L-1) • x+v T := by
    rw [wt]; apply add_right_cancel (b:=a • x)
    calc z • x+m.sum+a • x=(z+a) • x+m.sum := by rw [add_nsmul]; abel
         _ = (2^L-1) • x+(m.sum+b • x) := by rw [shift,add_nsmul]; abel
         _ = _ := by rw [←eq]; abel
  have r := replace_word c ok T ts m ms w wb len (wt ▸ cap) mass
  rwa [wt] at r

/-- Exterior squarefree words are rigid when the two gap lengths differ
    by at most one eighth of the available long binary row. -/
theorem local_rigid (ell : 4≤L) (big : 4*A.card≤2^L)
    (T : Finset (ZMod N)) (ts : T⊆A\row x L)
    (m : Multiset (ZMod N)) (ms : ∀ z∈m,z∈A\row x L)
    {a b : ℕ} (low : a≤b+2^(L-3)) (high : b≤a+2^(L-3))
    (eq : v T+a • x=m.sum+b • x) (len : m.card≤T.card) : m=T.val := by
  let z := 2^L-1+b-a
  have w : 2^L=8*2^(L-3) := by
    conv_lhs => rw [show L=L-3+3 by omega,pow_add]
    exact Nat.mul_comm _ _
  have pos : 0<2^(L-3) := by positivity
  have shift : z+a=2^L-1+b := by dsimp [z]; omega
  apply (from_coins c ok T ts m ms shift eq (by omega) ?_).1
  by_cases lt : z<2^L
  · obtain ⟨u,ub,uv,uc,_⟩ := OMA.BinaryPrefix.digits L z lt
    exact ⟨u,ub,uv,by omega⟩
  · obtain ⟨u,ub,uv,uc⟩ := OMA.PathShift.pack L 1 (z-2^L) (L-3) (by omega) (by omega) (Nat.sub_le ..)
    refine ⟨u,ub,?_,by omega⟩; simp only [one_mul] at uv; omega

theorem subset_injective (ell : 4≤L) (big : 4*A.card≤2^L) :
    Set.InjOn (v (G:=ZMod N)) ((A\row x L).powerset : Set (Finset (ZMod N))) := by
  intro s hs t ht e
  have compare (s t : Finset (ZMod N)) (si : s⊆A\row x L) (ti : t⊆A\row x L)
      (bound : s.card≤t.card) (eq : v s=v t) : s=t := by
    have sm : s.val.sum=v s := by change _=(s.val.map id).sum; simp
    exact val_inj.mp (local_rigid c ok ell big t ti s.val (fun _ z=>si z) (a:=0) (b:=0)
      (Nat.zero_le _) (Nat.zero_le _) (by simpa only [zero_nsmul,add_zero,sm] using eq.symm) bound)
  rcases le_total s.card t.card with le|le
  · exact compare s t (mem_powerset.mp hs) (mem_powerset.mp ht) le e
  · exact (compare t s (mem_powerset.mp ht) (mem_powerset.mp hs) le e.symm).symm

/-- A positive separation of two starts cannot use fewer than W−n
    copies of the path generator. -/
theorem spacing [NeZero N] (ell : 4≤L) (big : 4*A.card≤2^L)
    (S T : Finset (ZMod N)) (si : S⊆A\row x L) (ti : T⊆A\row x L)
    (j : ℕ) (jp : 0<j) (eq : v T=v S+j • x) : 2^L-A.card≤j := by
  by_contra! low
  have wc : L≤A.card := (row_size c) ▸ card_le_card (row_sub c)
  have wp : 0<2^L := by positivity
  have sum (U : Finset (ZMod N)) : U.val.sum=v U := by change _=(U.val.map id).sum; simp
  by_cases ord : S.card<T.card
  · have bad := from_coins c ok T ti S.val (fun _ z=>si z) (a:=0) (b:=j) (z:=2^L-1+j)
      (by omega) (by simpa only [zero_nsmul,add_zero,sum] using eq)
      (by omega) (by
        obtain ⟨u,ub,w,l⟩ := displaced (k:=L) (s:=j) (t:=0) (by omega) (by positivity)
        simp only [Nat.sub_zero,if_neg (by omega : ¬j<0),if_pos jp,add_zero] at w l
        exact ⟨u,ub,w,by change u.length+S.card≤_; omega⟩)
    omega
  · have small : 2^L-1-j<2^L := by omega
    obtain ⟨u,ub,wt,len,_⟩ := OMA.BinaryPrefix.digits L (2^L-1-j) small
    have hit := from_coins c ok S si T.val (fun _ z=>ti z) (a:=j) (b:=0) (z:=2^L-1-j)
      (by omega) (by simp only [sum,zero_nsmul,add_zero]; exact eq.symm)
      (by omega) ⟨u,ub,wt,by change u.length+T.card≤_; omega⟩
    have same := val_inj.mp hit.1
    rw [same] at eq
    have zero : j • x=0 := add_left_cancel (a:=v S) (by simpa using eq.symm)
    have dvd := addOrderOf_dvd_iff_nsmul_eq_zero.mpr zero
    have bound := Nat.le_of_dvd jp dvd
    have strong := order c ok; omega

/-- For a good return, exterior rank increases by at most one and
    strictly decreases for a return greater than W. -/
theorem gains (ell : 4≤L) (big : 4*A.card≤2^L)
    (S T : Finset (ZMod N)) (si : S⊆A\row x L) (ti : T⊆A\row x L)
    (j : ℕ) (jp : 0<j) (high : j≤2^L+2^(L-4)) (eq : v T=v S+j • x) :
    T.card≤S.card+1 ∧ (2^L<j → T.card<S.card) := by
  have wp : 0<2^L := by positivity
  have sSum : S.val.sum=v S := by change _=(S.val.map id).sum; simp
  have force (h : ∃ w : List ℕ,Bounded L w ∧ weight w=2^L-1+j ∧ w.length+S.card≤L+T.card) : False := by
    have hit := from_coins c ok T ti S.val (fun _ z=>si z) (a:=0) (b:=j) (z:=2^L-1+j) (by omega)
      (by simpa only [sSum,zero_nsmul,add_zero] using eq) (by omega) h
    omega
  by_cases lo : j≤2^L
  · refine ⟨?_,fun h=>(h.not_ge lo).elim⟩
    by_contra! bad
    obtain ⟨w,wb,wv,wl⟩ := OMA.PathShift.pack L 1 (j-1) L (by omega) (by omega) le_rfl
    apply force ⟨w,wb,?_,by omega⟩
    simp only [one_mul] at wv; omega
  · have drop : T.card<S.card := by
      by_contra! wrong
      obtain ⟨w,wb,wv,wl⟩ := OMA.PathShift.pack L 2 (j-2^L-1) (L-4) (by omega) (by omega) (Nat.sub_le ..)
      apply force ⟨w,wb,?_,by omega⟩
      omega
    exact ⟨by omega,fun _=>drop⟩

end
end OMA.PathGapCoins
