import DivisorLadderHeight245212

/-! At equality in any divisor-count level, exactly one in every s odd
prime exponents is a shifted power of two; all other exponents are one. -/
namespace OMA.DivisorLadderEquality245212
open Nat Finset ArithmeticFunction OMA.FixedRankInteger245212 OMA.DivisorFloorLadder245212
open scoped ArithmeticFunction.sigma
open private OMA.DivisorFloorLadder245212.ordinary OMA.DivisorFloorLadder245212.local_bound from DivisorFloorLadder245212

private theorem local_eq {s e : ℕ} (sp : 2 ≤ s) (ep : 0<e)
    (omitted : ∀j,2≤j → j<s → e+2≠2^j)
    (equal : 2^s*(2^s-1)^((e+2).factorization 2)=2^((e+2).factorization 2)*(e+1)^s) :
    (e=1 ∧ (e+2).factorization 2=0) ∨ (e+2=2^s ∧ (e+2).factorization 2=s) := by
  generalize hv : (e+2).factorization 2=v at equal ⊢
  have odd : Odd (2^s-1):=by
    rw [Nat.odd_iff]
    obtain ⟨u,hu⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : s≠0)
    rw [hu,pow_succ];have :=Nat.two_pow_pos u;omega
  have cop:=((Nat.coprime_two_left.mpr odd).pow_left v).pow_right v
  have d:=cop.dvd_of_dvd_mul_right (show 2^v∣2^s*(2^s-1)^v from ⟨_,equal⟩)
  have cap:=Nat.le_of_dvd (Nat.two_pow_pos s) d
  have vs : v ≤ s:=by
    by_contra! hi
    have :=Nat.pow_le_pow_right (by decide : 0<2) (show s+1≤v by omega)
    rw [pow_succ] at this;have :=Nat.two_pow_pos s;omega
  by_cases eq : v=s
  · rw [eq] at equal ⊢
    have same:=Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos s) equal
    have base_eq:=Nat.pow_left_injective (by omega : s≠0) same
    right;have :=Nat.two_pow_pos s;omega
  · have len:=OMA.DivisorFloorLadder245212.ordinary ep hv (fun lo=>omitted v lo (by omega))
    have lp:=Nat.pow_le_pow_left len s
    rw [mul_pow,←pow_mul,Nat.mul_comm v s,pow_mul] at lp
    have high:=(Nat.mul_le_mul_left (2^s) (Nat.pow_le_pow_left (Nat.sub_le (2^s) 1) v)).trans lp
    rw [equal] at high
    have one : 2^v≤1:=Nat.le_of_mul_le_mul_right (by simpa using high : 2^v*(e+1)^s≤1*(e+1)^s) (by positivity)
    have vz : v=0:=by have :=Nat.lt_two_pow_self (n:=v);omega
    rw [vz] at equal ⊢
    simp only [pow_zero,mul_one,one_mul] at equal
    have same:=Nat.pow_left_injective (by omega : s≠0) equal
    left;omega

theorem original {n s : ℕ} (pos : 0<n) (hit : OeisA245212.a n=(σ 1 n:ℤ))
    (sp : 2 ≤ s) (excluded : misses n s)
    (edge : (base s)^(support n).card=(σ 0 (ordCompl[2] n))^s) :
    (∀p∈support n,n.factorization p=1 ∨ n.factorization p+2=2^s) ∧
    (support n).card=s*((support n).filter (fun p=>n.factorization p+2=2^s)).card := by
  let t:=support n
  let r:=t.card
  let v (p : ℕ):=(n.factorization p+2).factorization 2
  let V:=∑p∈t,v p
  let left (p : ℕ):=2^s*(2^s-1)^v p
  let right (p : ℕ):=2^v p*(n.factorization p+1)^s
  have ep p (hp : p∈t) : 0<n.factorization p:=Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (mem_erase.mp hp).2)
  have le p (hp : p∈t) : left p≤right p:=OMA.DivisorFloorLadder245212.local_bound (ep p hp) (excluded p hp)
  have budget : r≤V:=OMA.OddDivisorFloor245212.budget pos hit
  have G : 2<2^s-1:=by have :=Nat.pow_le_pow_right (by decide : 0<2) sp;omega
  have sb : 2^s=2*2^(s-1):=by conv_lhs=>rw [show s=(s-1)+1 by omega,pow_succ,mul_comm]
  have pr : (∏p∈t,right p)=2^V*(base s)^r:=by
    rw [edge,OMA.SparseDivisorHeight245212.odd_count pos]
    simp only [right,prod_mul_distrib,prod_pow_eq_pow_sum,prod_pow,V,t,OMA.OddDivisorFloor245212.lengthProd]
  have pl : (∏p∈t,left p)=(2^s)^r*(2^s-1)^V:=by
    simp only [left,prod_mul_distrib,prod_const,prod_pow_eq_pow_sum,r,V]
  obtain ⟨d,hd⟩:=Nat.exists_eq_add_of_le budget
  have lhs : (∏p∈t,left p)=((2^s)^r*(2^s-1)^r)*(2^s-1)^d:=by rw [pl,hd,pow_add];ring
  have rhs : (∏p∈t,right p)=((2^s)^r*(2^s-1)^r)*2^d:=by
    rw [pr,hd,pow_add,base,mul_pow]
    have rewriteFirst : (2^s)^r=2^r*(2^(s-1))^r:=by rw [sb,mul_pow]
    rw [rewriteFirst];ring
  have d0 : d=0:=by
    have high:=prod_le_prod' (s:=t) le
    rw [lhs,rhs] at high
    have cap:=Nat.le_of_mul_le_mul_left high (by positivity)
    by_contra! no
    exact (Nat.pow_lt_pow_left G no).not_ge cap
  have equal : (∏p∈t,left p)=(∏p∈t,right p):=by simp only [lhs,rhs,d0,pow_zero]
  have shape p (mem : p∈t) := local_eq sp (ep p mem) (excluded p mem) (show left p=right p by
    by_contra! ne
    have strict:=prod_lt_prod (s:=t) (fun i _=>by dsimp [left];positivity) le
      ⟨p,mem,lt_of_le_of_ne (le p mem) ne⟩
    exact strict.ne equal)
  refine ⟨fun p h=>(shape p h).imp And.left And.left,?_⟩
  have big : 3<2^s:=by omega
  have same : V=∑p∈t,if n.factorization p+2=2^s then s else 0:=by
    apply sum_congr rfl;intro p mem
    rcases shape p mem with ⟨one,z⟩|⟨hi,h⟩
    · simp only [if_neg (show n.factorization p+2≠2^s by omega)];exact z
    · simpa only [if_pos hi] using h
  rw [sum_ite] at same
  change r=_
  simpa [d0,Nat.mul_comm] using (hd.symm.trans same)

#print axioms original
end OMA.DivisorLadderEquality245212
