import FormalConjectures.OEIS.«245212»

/-! An explicit uniform distance from a rational target to Euler products
of bounded length, provided none of their subproducts hits the target. -/
namespace OMA.CofactorEulerSeparation245212
open Finset Nat

def num (s : Finset ℕ) := ∏p∈s,p
def den (s : Finset ℕ) := ∏p∈s,(p-1)
def gap (A H : ℕ) (s : Finset ℕ) := ((A:ℤ)*num s-(H:ℤ)*den s).natAbs
def miss (A H : ℕ) (s : Finset ℕ) := ∀t⊆s,A*num t≠H*den t

def budget (A : ℕ) : ℕ→ℕ
  | 0=>1
  | r+1=>let b:=budget A r;max (2*b) ((2+2*A*2^r*b)^(r+1))

private theorem budget_pos (A r : ℕ) : 0<budget A r := by
  induction r with
  | zero=>simp [budget]
  | succ r ih=>exact (Nat.mul_pos (by decide) ih).trans_le (le_max_left _ _)

private theorem gap_pos {A H : ℕ} {s : Finset ℕ} (m : A*num s≠H*den s) : 0<gap A H s := by
  apply Int.natAbs_pos.mpr
  intro z
  exact m (by exact_mod_cast sub_eq_zero.mp z)

private theorem size {s : Finset ℕ} (positive : ∀p∈s,2≤p) : num s≤2^s.card*den s := by
  calc
    num s ≤ ∏p∈s,(2*(p-1)) := by
      apply prod_le_prod'
      intro p mem;have:=positive p mem;omega
    _ = _ := by simp [den,prod_mul_distrib]

private theorem spread {u x z : ℤ} (u0 : 0≤u) (x0 : 0≤x) (large : 2*x≤u*|z|) :
    u*|z|≤2*|u*z+x| := by
  have tri:=abs_add_le (u*z+x) (-x)
  rw [add_neg_cancel_right,abs_mul,abs_of_nonneg u0,abs_neg,abs_of_nonneg x0] at tri
  linarith

theorem separated (A H K : ℕ) (s : Finset ℕ) (card : s.card≤K)
    (positive : ∀p∈s,2≤p) (apart : miss A H s) : den s≤budget A K*gap A H s := by
  classical
  induction K generalizing s with
  | zero=>
    have empty : s=∅:=card_eq_zero.mp (by omega)
    subst s
    simpa [den,budget] using Nat.succ_le_of_lt (gap_pos (apart ∅ (by simp)))
  | succ K ih=>
    by_cases empty : s=∅
    · subst s
      simpa [den] using Nat.succ_le_of_lt (Nat.mul_pos (budget_pos A (K+1)) (gap_pos (apart ∅ (by simp))))
    have nonempty:=nonempty_iff_ne_empty.mpr empty
    let q:=s.max' nonempty
    have mem : q∈s:=s.max'_mem _
    have qp:=positive q mem
    let t:=s.erase q
    have sub : t⊆s:=erase_subset _ _
    have oldBound:=ih t (by dsimp [t];rw [card_erase_of_mem mem];omega)
      (fun p hp=>positive p (sub hp)) (fun z hz=>apart z (hz.trans sub))
    have scale:=size (s:=t) (fun p hp=>positive p (sub hp))
    have tc : t.card≤K := by dsimp [t];rw [card_erase_of_mem mem];omega
    let B:=budget A K
    have U : num s=q*num t := (mul_prod_erase s (fun p=>p) mem).symm
    have V : den s=(q-1)*den t := (mul_prod_erase s (fun p=>p-1) mem).symm
    by_cases large : 2*A*2^K*B≤q-1
    · have twice : 2*A*num t≤(q-1)*gap A H t := by
        calc
          _ ≤ 2*A*(2^K*(B*gap A H t)) := Nat.mul_le_mul_left _ (scale.trans
            (Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) tc) oldBound))
          _ = (2*A*2^K*B)*gap A H t := by ring
          _ ≤ _ := Nat.mul_le_mul_right _ large
      have twiceInt : 2*((A:ℤ)*num t)≤((q-1:ℕ):ℤ)*|(A:ℤ)*num t-(H:ℤ)*den t| := by
        have cast:=Int.ofNat_le.mpr twice
        simpa only [gap,Nat.cast_mul,Nat.cast_ofNat,Int.natCast_natAbs,mul_assoc] using cast
      have pre:=spread (u:=((q-1:ℕ):ℤ)) (x:=(A:ℤ)*num t) (z:=(A:ℤ)*num t-(H:ℤ)*den t)
        (by positivity) (by positivity) twiceInt
      have id : ((q-1:ℕ):ℤ)*((A:ℤ)*num t-(H:ℤ)*den t)+A*num t=(A:ℤ)*num s-(H:ℤ)*den s := by
        rw [U,V];push_cast [Nat.cast_sub (show 1≤q by omega)];ring
      rw [id] at pre
      have control : (q-1)*gap A H t≤2*gap A H s := by
        apply Int.ofNat_le.mp
        simpa [gap,Int.natCast_natAbs] using pre
      calc
        den s ≤ (q-1)*(B*gap A H t) := V ▸ Nat.mul_le_mul_left _ oldBound
        _ = B*((q-1)*gap A H t) := by ring
        _ ≤ B*(2*gap A H s) := Nat.mul_le_mul_left _ control
        _ = (2*B)*gap A H s := by ring
        _ ≤ _ := Nat.mul_le_mul_right _ (le_max_left _ _)
    · let J:=2+2*A*2^K*B
      have lo : 0<J := by dsimp [J];omega
      have modest : den s≤J^(K+1) := by
        refine (prod_le_pow_card s (fun p=>p-1) J ?_).trans (Nat.pow_le_pow_right lo card)
        intro p hp
        have below : p≤q:=s.le_max' p hp
        dsimp [J];omega
      have nonzero := gap_pos (apart s (Subset.rfl))
      exact modest.trans ((le_max_right _ _).trans (Nat.le_mul_of_pos_right _ nonzero))

#print axioms separated

theorem miss_odd {A H : ℕ} {s : Finset ℕ} (oa : Odd A) (eh : Even H)
    (pr : ∀p∈s,Odd p) : miss A H s := by
  intro t ht eqn
  have all (u : Finset ℕ) (ho : ∀p∈u,Odd p) : Odd (num u) := by
    induction u using Finset.induction_on with
    | empty=>simp [num]
    | @insert p u fresh ih=>
      rw [num,prod_insert fresh]
      exact (ho p (mem_insert_self ..)).mul (ih (fun q hq=>ho q (mem_insert_of_mem hq)))
  have left:=oa.mul (all t (fun p hp=>pr p (ht hp)))
  rw [eqn] at left
  exact (Nat.not_even_iff_odd.mpr left) (eh.mul_right _)

theorem miss_avoids {A H : ℕ} {s : Finset ℕ} (different : A≠H)
    (pr : ∀p∈s,p.Prime) (avoid : ∀p∈s,¬p∣H) : miss A H s := by
  intro t ht eqn
  by_cases empty : t=∅
  · exact different (by simpa [empty,num,den] using eqn)
  have nonempty:=nonempty_iff_ne_empty.mpr empty
  let q:=t.max' nonempty
  have mq : q∈t:=t.max'_mem _
  have pq:=pr q (ht mq)
  have dvd : q∣H*den t := eqn ▸ dvd_mul_of_dvd_right (dvd_prod_of_mem (fun p=>p) mq) A
  rcases pq.dvd_mul.mp dvd with bad|denom
  · exact avoid q (ht mq) bad
  obtain ⟨p,mp,dv⟩:=(pq.prime.dvd_finsetProd_iff (fun j=>j-1)).mp denom
  have upper : p≤q:=t.le_max' _ mp
  have lower:=(pr p (ht mp)).one_lt
  have:=Nat.le_of_dvd (show 0<p-1 by omega) dv
  omega

/-- A computable absolute gap, uniform over all allowed support sets. -/
theorem rational_gap {A H K : ℕ} {s : Finset ℕ} (card : s.card≤K)
    (positive : ∀p∈s,2≤p) (apart : miss A H s) :
    1 ≤ (budget A K:ℚ)*|(A:ℚ)*((num s:ℚ)/den s)-H| := by
  have n:=separated A H K s card positive apart
  have dp : 0<den s := prod_pos (fun p hp=>by have:=positive p hp;omega)
  have v : (0:ℚ)<den s := by exact_mod_cast dp
  let u : ℤ:=(A:ℤ)*num s-(H:ℤ)*den s
  have cast : (den s:ℚ)≤(budget A K:ℚ)*|(u:ℚ)| := by
    have intBound:=Int.ofNat_le.mpr n
    simp only [gap,Nat.cast_mul,Int.natCast_natAbs] at intBound
    dsimp [u]
    exact_mod_cast intBound
  have eqn : ((A:ℚ)*((num s:ℚ)/den s)-H)*(den s:ℚ)=(u:ℚ) := by
    dsimp [u];push_cast;field_simp
  apply (mul_le_mul_iff_of_pos_right v).mp
  have ab:=congrArg (fun z:ℚ=>|z|) eqn
  rw [abs_mul,abs_of_pos v] at ab
  simpa only [one_mul,mul_assoc,ab] using cast

#print axioms rational_gap
end OMA.CofactorEulerSeparation245212
