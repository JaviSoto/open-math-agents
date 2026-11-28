import DivisorLadderEquality245212

/-! Coalescing all powers of two into a single exponent gives a sharp
finite-rank bound from below on the odd parts of the shifted exponents.
This also proves finiteness at the critical exponential growth rate. -/
namespace OMA.OddUnitDivisorFloor245212
open Nat Finset ArithmeticFunction OMA.FixedRankInteger245212
open scoped ArithmeticFunction.sigma

private theorem coalesce {c A B : ℕ} (cp : 1≤c) (ap : 1≤A) (bp : 1≤B) :
    (c-1)*(c*(A*B)-1)≤(c*A-1)*(c*B-1) := by
  obtain ⟨u,rfl⟩:=Nat.exists_eq_add_of_le cp
  obtain ⟨a,rfl⟩:=Nat.exists_eq_add_of_le ap
  obtain ⟨b,rfl⟩:=Nat.exists_eq_add_of_le bp
  simp only [Nat.add_sub_cancel_left,mul_add,add_mul,one_mul,mul_one,Nat.add_assoc,
    Nat.add_sub_cancel_left]
  nlinarith only [Nat.zero_le ((u+1)*a*b)]

private theorem product (t : Finset ℕ) (v e : ℕ→ℕ) {c : ℕ} (cp : 1≤c)
    (bound : ∀p∈t,c*2^(v p)≤e p+2) :
    (c-1)^t.card*(c*2^(∑p∈t,v p)-1)≤(c-1)*(∏p∈t,(e p+1)) := by
  induction t using Finset.induction_on with
  | empty=>simp
  | @insert p t fresh ih=>
    have rest:=ih (fun i hi=>bound i (mem_insert_of_mem hi))
    let V:=∑i∈t,v i
    have merge:=coalesce cp (Nat.two_pow_pos (v p)) (Nat.two_pow_pos V)
    have single : c*2^(v p)-1≤e p+1:=by have :=bound p (mem_insert_self ..);omega
    rw [card_insert_of_notMem fresh,sum_insert fresh,prod_insert fresh,pow_succ,pow_add]
    change (c-1)^t.card*(c-1)*(c*(2^(v p)*2^V)-1)≤_
    calc
      _ ≤ (c-1)^t.card*((c*2^(v p)-1)*(c*2^V-1)):=by
        rw [mul_assoc];exact Nat.mul_le_mul_left _ merge
      _ ≤ (e p+1)*((c-1)*(∏i∈t,(e i+1))):=by
        rw [mul_left_comm];exact Nat.mul_le_mul single rest
      _ = _ := by ring

theorem original {n c : ℕ} (pos : 0<n) (hit : OeisA245212.a n=(σ 1 n:ℤ))
    (cp : 2≤c) (units : ∀p∈support n,c≤ordCompl[2] (n.factorization p+2)) :
    (c-1)^(support n).card*(c*2^(support n).card-1)≤(c-1)*(σ 0 (ordCompl[2] n)) := by
  let v (p : ℕ):=(n.factorization p+2).factorization 2
  have localBound p (mem : p∈support n) : c*2^(v p)≤n.factorization p+2:=by
    rw [mul_comm];exact (Nat.mul_le_mul_left _ (units p mem)).trans_eq
      (Nat.ordProj_mul_ordCompl_eq_self (n.factorization p+2) 2)
  have low:=OMA.OddDivisorFloor245212.budget pos hit
  have pow:=Nat.pow_le_pow_right (by decide : 0<2) low
  rw [OMA.SparseDivisorHeight245212.odd_count pos]
  exact (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right (Nat.mul_le_mul_left c pow) 1)).trans
    (product (support n) v (fun p=>n.factorization p) (by omega) localBound)

theorem critical {n c a b : ℕ} (pos : 0<n) (non : (support n).Nonempty)
    (hit : OeisA245212.a n=(σ 1 n:ℤ)) (cp : 2≤c)
    (units : ∀p∈support n,c≤ordCompl[2] (n.factorization p+2))
    (prefactor : (c-1)*a<c*b)
    (small : σ 0 (ordCompl[2] n)*b≤a*(2*(c-1))^(support n).card) :
    2^(support n).card≤b ∧ n≤OMA.SparseDivisorHeight245212.height (Nat.log 2 b) := by
  let r:=(support n).card
  let D:=σ 0 (ordCompl[2] n)
  have lower:=original pos hit cp units
  have high : (c-1)^r*((c*2^r-1)*b)≤(c-1)^r*((c-1)*a*2^r):=calc
    _ = ((c-1)^r*(c*2^r-1))*b:=by ring
    _ ≤ ((c-1)*D)*b:=Nat.mul_le_mul_right _ lower
    _ ≤ (c-1)*(a*(2*(c-1))^r):=by rw [mul_assoc];exact Nat.mul_le_mul_left _ small
    _ = _:=by rw [mul_pow];ring
  have posc : 0<c-1:=by omega
  have bound:=Nat.le_of_mul_le_mul_left high (pow_pos posc r)
  have restore:=congrArg (·*b) (Nat.sub_add_cancel (Nat.mul_pos (by omega : 0<c) (Nat.two_pow_pos r)))
  have scale:=Nat.mul_le_mul_right (2^r) (Nat.succ_le_of_lt prefactor)
  have cap : 2^r≤b:=by nlinarith only [bound,restore,scale]
  refine ⟨cap,(OMA.FixedRankAbsolute245212.absolute pos non hit).trans ?_⟩
  exact single_le_sum (f:=OMA.FixedRankAbsolute245212.bound) (fun _ _=>Nat.zero_le _)
    (mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_log_iff_pow_le (by decide) (by have :=Nat.two_pow_pos r;omega)).mpr cap)))

theorem no_pure_shift {n : ℕ} (pos : 0<n) (hit : OeisA245212.a n=(σ 1 n:ℤ))
    (excluded : ∀p∈support n,∀j,2≤j → n.factorization p+2≠2^j) :
    2^(support n).card*(3*2^(support n).card-1)≤2*(σ 0 (ordCompl[2] n)) := by
  apply original pos hit (c:=3) (by decide)
  intro p mem
  let e:=n.factorization p
  have ep : 0<e:=Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (mem_erase.mp mem).2)
  let j:=(e+2).factorization 2
  have odd:=Nat.coprime_two_left.mp (Nat.coprime_ordCompl prime_two (by omega : e+2≠0))
  obtain ⟨u,hu⟩:=odd
  by_contra! small
  have one : ordCompl[2] (e+2)=1:=by change ordCompl[2] (e+2)<3 at small;omega
  have h : 2^j=e+2:=by simpa only [one,mul_one] using Nat.ordProj_mul_ordCompl_eq_self (e+2) 2
  by_cases two : 2≤j
  · exact excluded p mem j two h.symm
  · have cap:=Nat.pow_le_pow_right (by decide : 0<2) (show j≤1 by omega);omega

#print axioms original
#print axioms critical
#print axioms no_pure_shift
end OMA.OddUnitDivisorFloor245212
