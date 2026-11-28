import Mathlib

/-! Complete criteria for the two congruences in Meštrović's 2014 Conjecture 11. -/

/-! The prime-local obstruction for Meštrović's A284760 power sum.
Compare Carlitz–von Staudt and Meštrović, arXiv:1211.4570, §2.4.
The repeated-prime case follows by lifting the complete residue sum one
factor of the prime at a time. -/
namespace OMA.PowerSum284760
open Finset Nat

private theorem taylor {R : Type*} [CommRing R] (x y:R) (hy:y^2=0) (e:ℕ) :
    (x+y)^e=x^e+e*x^(e-1)*y := by
  cases e with
  | zero => simp
  | succ e =>
    induction e with
    | zero=>simp
    | succ e ih =>
      rw [pow_succ (x+y),ih]
      simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,pow_succ]
      linear_combination ((e:R)+1)*x^e*hy

private theorem blocks {R : Type*} [AddCommMonoid R] (f : ℕ→R) (m k : ℕ) :
    (∑i∈range (m*k),f i)=∑j∈range k,∑i∈range m,f (m*j+i) := by
  induction k with
  | zero=>simp
  | succ k ih=>rw [Nat.mul_succ,sum_range_succ,sum_range_add,ih]

private theorem blocks_cast (m k e : ℕ) :
    (∑i∈range (m*k), (i:ZMod m)^e)=(k:ZMod m)*∑i∈range m,(i:ZMod m)^e := by
  rw [blocks];simp


end OMA.PowerSum284760

/-! A second-order local test for odd A284760 counterexamples, including primes
where the first complete power-sum obstruction vanishes. -/
namespace OMA.PowerSumRegular284760
open Finset Nat

private theorem quad {R : Type*} [CommRing R] (x y:R) (hy:y^3=0) (e:ℕ) :
    (x+y)^e=x^e+e*x^(e-1)*y+(e.choose 2:R)*x^(e-2)*y^2 := by
  cases e with
  | zero=>simp
  | succ e=>
    cases e with
    | zero=>simp
    | succ a=>
      induction a with
      | zero=>norm_num [pow_two];ring
      | succ a ih=>
        rw [pow_succ (x+y),ih,Nat.choose_succ_succ (a+2) 1]
        simp only [Nat.choose_one_right,Nat.cast_add,Nat.cast_one,Nat.succ_sub_succ_eq_sub,
          Nat.sub_zero,Nat.cast_ofNat,pow_succ]
        linear_combination ((a+2).choose 2:R)*x^a*hy

private theorem mirror {R : Type*} [AddCommMonoid R] (n:ℕ) (f:ℕ→R) :
    (∑i∈Ico 1 n,f (n-i))=∑i∈Ico 1 n,f i := by
  apply sum_bij' (fun i _=>n-i) (fun i _=>n-i)
  all_goals intro i hi;obtain ⟨lo,hi⟩:=mem_Ico.mp hi
  all_goals first | exact mem_Ico.mpr ⟨by omega,by omega⟩ | omega | rfl

private theorem ico_range {f:ℕ→ℕ} {n:ℕ} (np:0<n) (z:f 0=0) :
    (∑i∈Ico 1 n,f i)=∑i∈range n,f i := by
  simpa [z] using sum_range_add_sum_Ico f np

private theorem odd_sum {n e:ℕ} (on:Odd n) (oe:Odd e) : n∣∑i∈Ico 1 n,i^e := by
  have ref:=mirror n (fun i:ℕ=>(i:ZMod n)^e)
  have rev (i) (hi:i∈Ico 1 n) : ((n-i:ℕ):ZMod n)^e = -(i:ZMod n)^e := by
    rw [Nat.cast_sub (mem_Ico.mp hi).2.le,ZMod.natCast_self,zero_sub,oe.neg_pow]
  rw [sum_congr rfl rev,sum_neg_distrib] at ref
  have two : 2*(∑i∈Ico 1 n,(i:ZMod n)^e)=0 := by linear_combination -ref
  apply (Nat.coprime_two_right.mpr on).dvd_of_dvd_mul_left
  exact (ZMod.natCast_eq_zero_iff _ _).mp (by push_cast;exact two)

private theorem reflect3 {n e : ℕ} (on:Odd n) (oe:Odd e) (big:3≤e) :
    2*(∑i∈Ico 1 n,(i:ZMod (n^3))^e)=
      (n:ZMod (n^3))*e*(∑i∈Ico 1 n,(i:ZMod (n^3))^(e-1)) := by
  let R:=ZMod (n^3)
  have z : (n:R)^3=0 := by rw [←Nat.cast_pow];exact ZMod.natCast_self _
  have ev : Even (e-1) := by obtain ⟨b,hb⟩:=oe;exact ⟨b,by omega⟩
  have od : Odd (e-2) := by obtain ⟨b,hb⟩:=oe;exact ⟨b-1,by omega⟩
  have vanish : (n:R)^2*(∑i∈Ico 1 n,(i:R)^(e-2))=0 := by
    simp only [←Nat.cast_pow,←Nat.cast_sum,←Nat.cast_mul]
    apply (ZMod.natCast_eq_zero_iff _ _).mpr
    rw [show (3:ℕ)=2+1 by decide,pow_succ]
    exact Nat.mul_dvd_mul_left _ (odd_sum on od)
  rw [two_mul]
  nth_rw 1 [←mirror n (fun i=>(i:R)^e)]
  rw [←sum_add_distrib]
  calc
    _=∑i∈Ico 1 n, ((n:R)*e*(i:R)^(e-1) - (e.choose 2:R)*n^2*(i:R)^(e-2)) := by
      apply sum_congr rfl;intro i hi
      rw [Nat.cast_sub (mem_Ico.mp hi).2.le,sub_eq_neg_add,quad _ _ z,
        oe.neg_pow,ev.neg_pow,od.neg_pow];ring
    _=_ := by rw [sum_sub_distrib,←mul_sum,←mul_sum,mul_assoc _ ((n:R)^2),vanish,mul_zero,sub_zero]


end OMA.PowerSumRegular284760

/-! Faulhaber at the actual exponent n−2.  Since its denominator n−1
is a unit at every prime dividing n, all but one of the top terms can be
controlled directly with von Staudt–Clausen. -/
namespace OMA.BernoulliScreen284760
open Finset Nat
open private Bernoulli.not_dvd_den_bernoulli_add_indicator Bernoulli.vonStaudtIndicator from Mathlib.NumberTheory.Bernoulli

private abbrev integers (p:ℕ) [Fact p.Prime] : Subring ℚ := (Rat.padicValuation p).integer

private theorem integral_iff {p:ℕ} [Fact p.Prime] (x:ℚ) :
    x∈integers p ↔ ¬p∣x.den := Rat.padicValuation_le_one_iff

private theorem bernoulli_integral {p i:ℕ} [Fact p.Prime] (ip : 0 < i)
    (ei:Even i) (nd:¬p-1∣i) : bernoulli i∈integers p := by
  obtain ⟨k,h⟩:=ei
  have hh:i=2*k:=by omega
  clear h
  subst i
  have x:=Bernoulli.not_dvd_den_bernoulli_add_indicator (p:=p) (k:=k) (by omega)
  apply (integral_iff _).mpr
  simpa [Bernoulli.vonStaudtIndicator,nd] using x

private theorem p_bernoulli {p:ℕ} [Fact p.Prime] (hp:5≤p) (i:ℕ) :
    (p:ℚ)*bernoulli i∈integers p := by
  by_cases iz:i=0
  · subst i;simp
  by_cases io:i=1
  · subst i;apply (integers p).mul_mem (natCast_mem (integers p) _) ((integral_iff _).mpr ?_)
    norm_num [bernoulli_one];intro d;have :=Nat.le_of_dvd (by decide : 0<2) d;omega
  rcases Nat.even_or_odd i with ev|od
  · obtain ⟨k,h⟩:=ev;have hh:i=2*k:=by omega
    clear h
    subst i
    have z:=(integral_iff _).mpr (Bernoulli.not_dvd_den_bernoulli_add_indicator (p:=p) (k:=k) (by omega))
    have mult:=(integers p).mul_mem (natCast_mem (integers p) p) z
    by_cases d:p-1∣2*k
    · have nz:(p:ℚ)≠0:=by exact_mod_cast (Fact.out : p.Prime).ne_zero
      have ident:(p:ℚ)*bernoulli (2*k)=p*(bernoulli (2*k)+1/p)-1:=by field_simp;ring
      rw [ident]
      apply (integers p).sub_mem _ (integers p).one_mem
      simpa [Bernoulli.vonStaudtIndicator,d] using mult
    · simpa [Bernoulli.vonStaudtIndicator,d] using mult
  · rw [bernoulli_eq_zero_of_odd od (by omega),mul_zero];exact (integers p).zero_mem


end OMA.BernoulliScreen284760

namespace OMA.DoubleBernoulli284760
open Nat Finset

private theorem perm {R:Type*} [AddCommMonoid R] (p:ℕ) (odd:Odd p) (f:ℕ→R):
    (∑i∈range p,f ((2*i)%p))=∑i∈range p,f i := by
  let u:=(p+1)/2
  have id:2*u=p+1:=by dsimp [u];obtain ⟨t,h⟩:=odd;omega
  have inv (i:ℕ) (hi:i<p) : (2*u*i)%p=i := by
    rw [id,add_mul,one_mul,Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt hi]
  apply sum_bij' (fun i _=>(2*i)%p) (fun i _=>(u*i)%p)
  · intro i _;exact mem_range.mpr (Nat.mod_lt _ odd.pos)
  · intro i _;exact mem_range.mpr (Nat.mod_lt _ odd.pos)
  · intro i hi;rw [Nat.mul_mod_mod,←mul_assoc,mul_comm u 2];exact inv _ (mem_range.mp hi)
  · intro i hi;rw [Nat.mul_mod_mod,←mul_assoc];exact inv _ (mem_range.mp hi)
  · intro _ _;rfl

private theorem weight (h:ℕ) :
    (∑i∈range (2*h+1), ((2*i)/(2*h+1))*((2*i)%(2*h+1)))=h^2 := by
  conv_lhs => arg 1;rw [show 2*h+1=(h+1)+h by omega]
  rw [sum_range_add]
  have first (i:ℕ) (hi:i∈range (h+1)) : ((2*i)/(2*h+1))*((2*i)%(2*h+1))=0:=by
    have :=mem_range.mp hi;rw [Nat.div_eq_of_lt (by omega),zero_mul]
  have last (i:ℕ) (hi:i∈range h) :
      ((2*(h+1+i))/(2*h+1))*((2*(h+1+i))%(2*h+1))=2*i+1:=by
    have ih:=mem_range.mp hi
    rw [show 2*(h+1+i)=(2*i+1)+(2*h+1) by omega,Nat.add_div_right _ (by omega),
        Nat.div_eq_of_lt (by omega),Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)];simp
  rw [sum_congr rfl first,sum_congr rfl last,sum_const_zero,zero_add,sum_add_distrib,
    ←mul_sum,sum_const,card_range,nsmul_eq_mul,mul_one]
  cases h with
  | zero=>simp
  | succ h=>
    have id:=sum_range_id_mul_two (h+1)
    rw [Nat.add_sub_cancel] at id;nlinarith only [id]

/-- Under the square-local test, doubling the representatives forces one
weighted half-residue sum to vanish modulo p. -/
private theorem weight_zero {e p:ℕ} (hp:p.Prime) (odd:Odd p)
    (de:¬p∣e) (he:p^2∣∑i∈range p,i^e) :
    p∣∑i∈range p, (2*i/p)*((2*i)%p)^(e-1) := by
  let R:=ZMod (p^2)
  have sq:(p:R)^2=0:=by rw [←Nat.cast_pow];exact ZMod.natCast_self _
  have base : (∑i∈range p,(i:R)^e)=0 := by
    simpa only [Nat.cast_pow,Nat.cast_sum] using (ZMod.natCast_eq_zero_iff _ _).mpr he
  have eq (i:ℕ) : ((2*i:ℕ):R)^e = (((2*i)%p:ℕ):R)^e+
      ((p:R)*e)*((2*i/p:ℕ):R)*(((2*i)%p:ℕ):R)^(e-1) := by
    calc
      _ = ((((2*i)%p:ℕ):R)+(p:R)*((2*i/p:ℕ):R))^e := by
        congr 1
        simpa only [R,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using congrArg (fun a:ℕ=>(a:ZMod (p^2))) (Nat.mod_add_div (2*i) p).symm
      _ = _ := by rw [OMA.PowerSum284760.taylor _ _ (by rw [mul_pow,sq,zero_mul])];ring
  have tot := sum_congr (s₁:=range p) rfl (fun i _=>eq i)
  rw [sum_add_distrib,perm p odd (fun i=>(i:R)^e)] at tot
  have lm : (∑i∈range p,((2*i:ℕ):R)^e)=0 := by
    change (∑i∈range p,((2*i:ℕ):ZMod (p^2))^e)=0
    simp only [Nat.cast_mul,Nat.cast_ofNat,mul_pow,←mul_sum];rw [base,mul_zero]
  rw [lm,base,zero_add] at tot
  have val : (p:R)*((e:R)*(∑i∈range p, ((2*i/p:ℕ):R)*(((2*i)%p:ℕ):R)^(e-1)))=0 := by
    rw [mul_sum,mul_sum];simpa only [mul_assoc] using tot.symm
  have dv:p^2∣p*(e*(∑i∈range p, (2*i/p)*((2*i)%p)^(e-1))) :=
    (ZMod.natCast_eq_zero_iff _ _).mp (by push_cast;exact val)
  rw [pow_two] at dv
  exact (hp.coprime_iff_not_dvd.mpr de).dvd_of_dvd_mul_left (Nat.dvd_of_mul_dvd_mul_left hp.pos dv)

/-- The missing second Bernoulli index is impossible for an actual odd
counterexample: its half-residue sum would be a nonzero triangular number. -/
theorem not_two_of_test {n p:ℕ} (hp:p.Prime) (big:5≤p) (on:Odd n) (pn:p∣n)
    (h:p^2∣∑i∈range p,i^(n-3)) : ¬p-1∣n-5 := by
  have nn:=Nat.le_of_dvd on.pos pn
  have op:=hp.odd_of_ne_two (by omega)
  have de:¬p∣n-3 := by
    intro dv
    have dd:p∣3 := (Nat.dvd_add_left dv).mp (by rwa [Nat.add_sub_cancel' (by omega : 3≤n)])
    have := Nat.le_of_dvd (by decide : 0<3) dd;omega
  have half:=weight_zero hp op de h
  intro twice
  obtain ⟨q,hq⟩:=twice
  have exp:n-3-1=1+(p-1)*q:=by omega
  let _ : Fact p.Prime:=⟨hp⟩
  have same (a:ℕ) : ((a%p:ℕ):ZMod p)^(n-3-1)=((a%p:ℕ):ZMod p) := by
    by_cases z:((a%p:ℕ):ZMod p)=0
    · rw [z,zero_pow (by omega : n-3-1≠0)]
    · rw [exp,pow_add,pow_mul,ZMod.pow_card_sub_one_eq_one z,one_pow,pow_one,mul_one]
  have z1 : (∑i∈range p,((2*i/p:ℕ):ZMod p)*(((2*i)%p:ℕ):ZMod p)^(n-3-1))=0 := by
    simpa only [Nat.cast_sum,Nat.cast_mul,Nat.cast_pow] using (ZMod.natCast_eq_zero_iff _ _).mpr half
  simp_rw [same] at z1
  have dw : p∣∑i∈range p,(2*i/p)*((2*i)%p) := (ZMod.natCast_eq_zero_iff _ _).mp (by
    simpa only [Nat.cast_sum,Nat.cast_mul] using z1)
  obtain ⟨b,hb⟩:=op
  rw [hb,weight] at dw
  have pb:(2*b+1).Prime:=hb ▸ hp
  have small: 2*b+1 ≤ b := Nat.le_of_dvd (by omega) (pb.dvd_of_dvd_pow dw)
  omega


end OMA.DoubleBernoulli284760

namespace OMA.ThirdOrder284760
open Finset Nat
open OMA.BernoulliScreen284760

private abbrev localRing (p:ℕ) [Fact p.Prime] := OMA.BernoulliScreen284760.integers p

private theorem inv_mem {p d:ℕ} [Fact p.Prime] (pos:0<d) (good:¬p∣d):
    (d:ℚ)⁻¹∈localRing p := by
  apply (OMA.BernoulliScreen284760.integral_iff _).mpr
  rwa [Rat.inv_natCast_den_of_pos pos]


end OMA.ThirdOrder284760

namespace OMA.QuarticIff284760
open Nat Finset
open private Bernoulli.not_dvd_den_bernoulli_add_indicator Bernoulli.vonStaudtIndicator from Mathlib.NumberTheory.Bernoulli
private abbrev R (p:ℕ) [Fact p.Prime] := OMA.BernoulliScreen284760.integers p

private theorem nat_of_local {n s t:ℕ} (nn:0<n)
    (h:∀ p:ℕ, ∀ hp:p.Prime, p∣n → (s:ℚ)/(n:ℚ)^t∈@R p ⟨hp⟩) : n^t∣s := by
  let x:ℚ:=(s:ℚ)/(n:ℚ)^t
  have co:n.Coprime x.den:=Nat.coprime_of_dvd (fun p hp pn=>by
    let _ : Fact p.Prime:=⟨hp⟩
    exact (OMA.BernoulliScreen284760.integral_iff x).mp (h p hp pn))
  have zn:(n:ℚ)≠0:=by exact_mod_cast nn.ne'
  have id:(x.num:ℚ)/x.den=(s:ℚ)/(n:ℚ)^t:=Rat.num_div_den _
  have dn:(x.den:ℚ)≠0:=by exact_mod_cast x.den_ne_zero
  field_simp at id
  have eq:x.num*(n:ℤ)^t=(s:ℤ)*x.den:=by rw [mul_comm (s:ℤ)];exact_mod_cast id
  have val:=congrArg Int.natAbs eq
  simp only [Int.natAbs_mul,Int.natAbs_natCast,Int.natAbs_pow] at val
  have d:=dvd_mul_left (n^t) x.num.natAbs
  rw [val] at d;exact (co.pow_left _).dvd_of_dvd_mul_right d

private theorem quotient {p d:ℕ} [Fact p.Prime] (x:ℚ) (pos:0<d) (pd:p∣d)
    (dv:d∣x.num.natAbs) : x/(d:ℚ)∈R p := by
  have dn:(d:ℚ)≠0:=by exact_mod_cast pos.ne'
  have cp:¬p∣x.den := (Fact.out : p.Prime).coprime_iff_not_dvd.mp (x.reduced.of_dvd_left (pd.trans dv))
  obtain ⟨z,hz⟩:=Int.natCast_dvd.mpr dv
  have num:(x.num:ℚ)=(d:ℚ)*z:=by exact_mod_cast hz
  have id:x/(d:ℚ)=(z:ℚ)*(x.den:ℚ)⁻¹:=by nth_rw 1 [←Rat.num_div_den x];rw [num];field_simp
  rw [id];exact (R p).mul_mem (intCast_mem _ _) (OMA.ThirdOrder284760.inv_mem x.den_pos cp)


end OMA.QuarticIff284760

namespace OMA.QuarticAll284760
open Nat Finset

/-- For n even and e positive even, already n itself fails to divide the
complete power sum. Halving the number of terms preserves the obstruction. -/
theorem even_obstruction {n e:ℕ} (nn:0<n) (en:Even n) (ep:0<e) (ee:Even e) :
    ¬n∣∑i∈range n,i^e := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    obtain ⟨m,hm⟩:=en
    have nf:n=2*m:=by omega
    have mp:0 < m :=by omega
    intro hz
    rw [nf] at hz
    rcases Nat.even_or_odd m with em|om
    · let R:=ZMod (2*m)
      have sq:(m:R)^2=0:=by
        rw [←Nat.cast_pow,ZMod.natCast_eq_zero_iff,pow_two]
        exact Nat.mul_dvd_mul_right em.two_dvd _
      have emul:(m:R)*e=0:=by
        rw [←Nat.cast_mul,ZMod.natCast_eq_zero_iff,mul_comm 2 m]
        exact Nat.mul_dvd_mul_left _ ee.two_dvd
      have term (i:ℕ) : ((m+i:ℕ):R)^e=(i:R)^e := by
        rw [Nat.cast_add,add_comm,OMA.PowerSum284760.taylor _ _ sq e]
        linear_combination (i:R)^(e-1)*emul
      have val:(∑i∈range (2*m),(i:R)^e)=0:=by
        simpa only [Nat.cast_pow,Nat.cast_sum] using (ZMod.natCast_eq_zero_iff _ _).mpr hz
      conv at val => lhs;arg 1;rw [two_mul m]
      rw [sum_range_add,sum_congr rfl (fun i _=>term i),←two_mul] at val
      have div:2*m∣2*(∑i∈range m,i^e):=(ZMod.natCast_eq_zero_iff _ _).mp (by push_cast;exact val)
      exact ih m (by omega) mp em ((Nat.dvd_of_mul_dvd_mul_left (by decide : 0<2)) div)
    · have span:=OMA.PowerSum284760.blocks_cast 2 m e
      have zero:(∑i∈range (2*m),(i:ZMod 2)^e)=0:=by
        simpa only [Nat.cast_sum,Nat.cast_pow] using (ZMod.natCast_eq_zero_iff _ _).mpr
          ((dvd_mul_right 2 m).trans hz)
      rw [zero] at span
      have base:(∑i∈range 2,(i:ZMod 2)^e)=1:=by
        rw [sum_range_succ,sum_range_succ];simp [zero_pow ep.ne']
      rw [base,mul_one] at span
      exact om.not_two_dvd_nat ((ZMod.natCast_eq_zero_iff ..).mp span.symm)


end OMA.QuarticAll284760

/-! At every sufficiently large prime dividing the upper summation
limit, compare the entire even-power sum with n times a Bernoulli
number modulo the full square of the p-part of n. -/
namespace OMA.CubicBernoulliLocal284759
open Finset Nat
open private Bernoulli.not_dvd_den_bernoulli_add_indicator Bernoulli.vonStaudtIndicator
  from Mathlib.NumberTheory.Bernoulli

abbrev localRing (p:ℕ) [Fact p.Prime] := (Rat.padicValuation p).integer

private theorem odd_prime_scaled {p:ℕ} [Fact p.Prime] (hp:3≤p) (i:ℕ) :
    (p:ℚ)*bernoulli i∈localRing p := by
  by_cases big:5≤p
  · exact OMA.BernoulliScreen284760.p_bernoulli big i
  have prime:=Fact.out (p:=p.Prime)
  have eq:p=3 := by interval_cases p <;> norm_num at *
  subst p
  by_cases iz:i=0
  · subst i;simp
  by_cases io:i=1
  · subst i;apply Rat.padicValuation_le_one_iff.mpr;norm_num [bernoulli_one]
  rcases Nat.even_or_odd i with even|odd
  · obtain ⟨k,hk⟩:=even
    have ik:i=2*k:=by omega
    subst i
    have hd:=Bernoulli.not_dvd_den_bernoulli_add_indicator (p:=3) (k:=k) (by omega)
    have frac:bernoulli (2*k)+1/3∈localRing 3 := Rat.padicValuation_le_one_iff.mpr
      (by simpa [Bernoulli.vonStaudtIndicator] using hd)
    have alg:3*bernoulli (2*k)=3*(bernoulli (2*k)+1/3)-1:=by ring
    rw [ik]
    norm_num only [Nat.cast_ofNat]
    rw [alg]
    exact (localRing 3).sub_mem ((localRing 3).mul_mem (by exact_mod_cast natCast_mem (localRing 3) 3) frac)
      (localRing 3).one_mem
  · rw [bernoulli_eq_zero_of_odd odd (by omega),mul_zero];exact (localRing 3).zero_mem

theorem inverse_mem {p d:ℕ} [Fact p.Prime] (hd:¬p∣d) :
    (d:ℚ)⁻¹∈localRing p := by
  apply Rat.padicValuation_le_one_iff.mpr
  by_cases dz : d=0
  · exact False.elim (hd (dz ▸ dvd_zero _))
  simpa [Rat.den_inv,Int.natAbs_natCast,dz] using hd

theorem error {p n b:ℕ} [Fact p.Prime] (big:3≤p) (nn:0<n) (pn:p∣n)
    (even:Even b) (bp:0<b) (unit:¬p∣b+3) :
    ((∑i∈range n,(i:ℚ)^(b+2))/(n:ℚ)^2 - bernoulli (b+2)/n)∈localRing p := by
  let S:=∑i∈range n,(i:ℚ)^(b+2)
  let F (i:ℕ):=bernoulli i*((b+3).choose i:ℚ)*(n:ℚ)^(b+3-i)/(n:ℚ)^2
  have nz : (n:ℚ)≠0:=by exact_mod_cast nn.ne'
  obtain ⟨u,nu⟩:=pn
  have np : (n:ℚ)=(p:ℚ)*u:=by exact_mod_cast nu
  have early:(∑i∈range (b+1),F i)∈localRing p := by
    apply (localRing p).sum_mem
    intro i hi
    have ib:=mem_range.mp hi
    have form : F i=(p*bernoulli i)*u*((b+3).choose i:ℚ)*(n:ℚ)^(b-i) := by
      dsimp [F];rw [show b+3-i=(b-i)+1+2 by omega,pow_add _ _ 2,pow_succ]
      field_simp;rw [np];ring
    rw [form]
    exact (localRing p).mul_mem ((localRing p).mul_mem ((localRing p).mul_mem
      (odd_prime_scaled big i) (natCast_mem _ _)) (natCast_mem _ _))
      ((localRing p).pow_mem (natCast_mem _ _) _)
  have odd:Odd (b+1):=by obtain ⟨j,h⟩:=even;exact ⟨j,by omega⟩
  have penult:F (b+1)=0:=by simp [F,bernoulli_eq_zero_of_odd odd (by omega)]
  have final:F (b+2)=(b+3:ℚ)*bernoulli (b+2)/n := by
    dsimp only [F];rw [Nat.choose_succ_self_right,show b+3-(b+2)=1 by omega,pow_one]
    push_cast;field_simp;ring
  have faul:=sum_range_pow n (b+2)
  rw [←Finset.sum_div] at faul
  push_cast at faul
  have nonzero:(b+2+1:ℚ)≠0:=by positivity
  have all:(∑i∈range (b+3),F i)=(b+3:ℚ)*S/(n:ℚ)^2 := by
    dsimp only [F,S];rw [←Finset.sum_div]
    congr 1
    have v:=(eq_div_iff nonzero).mp faul
    linear_combination -v
  rw [Finset.sum_range_succ,Finset.sum_range_succ,penult,add_zero,final] at all
  have id : S/(n:ℚ)^2-bernoulli (b+2)/n =
      (∑i∈range (b+1),F i)*((b+3:ℕ):ℚ)⁻¹ := by
    push_cast
    field_simp [nz] at all ⊢
    linear_combination -all
  rw [id]
  exact (localRing p).mul_mem early (inverse_mem unit)

end OMA.CubicBernoulliLocal284759

/-! Pass from the local even power-sum comparison to ordinary divisibility
of the reduced Bernoulli numerator, without a squarefreeness assumption. -/
namespace OMA.CubicBernoulliCriterion284759
open Nat Finset OMA.CubicBernoulliLocal284759

theorem denominator {n:ℕ} (nn:0<n) (q:ℚ) :
    n∣q.num.natAbs ↔ n.Coprime (q/(n:ℚ)).den := by
  let x:=q/(n:ℚ)
  have hn:(n:ℚ)≠0:=by exact_mod_cast nn.ne'
  have xd:(x.den:ℚ)≠0:=by exact_mod_cast x.den_ne_zero
  have qd:(q.den:ℚ)≠0:=by exact_mod_cast q.den_ne_zero
  have frac : (x.num:ℚ)/x.den=((q.num:ℚ)/q.den)/n := by rw [Rat.num_div_den,Rat.num_div_den]
  have cross:x.num*(q.den:ℤ)*n=q.num*x.den := by
    exact_mod_cast (by field_simp at frac;linear_combination frac :
      (x.num:ℚ)*q.den*n=q.num*x.den)
  have eqn:=congrArg Int.natAbs cross
  simp only [Int.natAbs_mul,Int.natAbs_natCast] at eqn
  change _ ↔ n.Coprime x.den
  constructor
  · rintro ⟨z,hz⟩
    have can : x.num.natAbs*q.den=z*x.den := Nat.eq_of_mul_eq_mul_right nn
      (by rw [hz] at eqn;simpa only [mul_left_comm,mul_assoc,mul_comm] using eqn)
    apply Nat.coprime_of_dvd;intro p pp pn pd
    have lhs : p∣x.num.natAbs*q.den := can ▸ dvd_mul_of_dvd_right pd z
    rcases pp.dvd_mul.mp lhs with a|b
    · exact (Nat.not_coprime_of_dvd_of_dvd pp.one_lt a pd) x.reduced
    · exact (Nat.not_coprime_of_dvd_of_dvd pp.one_lt
        (pn.trans (show n∣q.num.natAbs from ⟨z,hz⟩)) b) q.reduced
  · intro cp
    apply cp.dvd_of_dvd_mul_right
    rw [←eqn];exact dvd_mul_left _ _

/-- For positive n all of whose prime factors are odd, even t=b+2≥4,
and gcd(t+1,n)=1, n² divides the complete even-power sum iff n divides
the numerator of B_t. -/
theorem even_iff {n b:ℕ} (nn:0<n) (bp:0<b) (ev:Even b)
    (large:∀p:ℕ,p.Prime→p∣n→3≤p) (unit:n.Coprime (b+3)) :
    n^2∣∑i∈range n,i^(b+2) ↔ n∣(bernoulli (b+2)).num.natAbs := by
  let S:=∑i∈range n,i^(b+2)
  let B:=bernoulli (b+2)
  let X:ℚ:=S/(n:ℚ)^2
  let Y:ℚ:=B/n
  have eqv {p:ℕ} (pp:p.Prime) (pn:p∣n) : ¬p∣X.den ↔ ¬p∣Y.den := by
    let : Fact p.Prime:=⟨pp⟩
    have d : X-Y∈localRing p := by
      have err:=error (b:=b) (large p pp pn) nn pn ev bp
        (fun pd=>(Nat.not_coprime_of_dvd_of_dvd pp.one_lt pn pd) unit)
      dsimp [X,Y,S,B];push_cast;exact err
    rw [←Rat.padicValuation_le_one_iff,←Rat.padicValuation_le_one_iff]
    change X∈localRing p ↔ Y∈localRing p
    constructor
    · intro x;simpa only [sub_sub_cancel] using (localRing p).sub_mem x d
    · intro y;simpa only [sub_add_cancel] using (localRing p).add_mem d y
  have left:n^2∣S ↔ n.Coprime X.den := by
    have f:=denominator (pow_pos nn 2) (S:ℚ)
    simpa only [Rat.num_natCast,Int.natAbs_natCast,Nat.cast_pow,Nat.coprime_pow_left_iff
      (by decide : 0<2),X] using f
  have right:=denominator nn B
  change n^2∣S↔n∣B.num.natAbs
  rw [left,right]
  change n.Coprime X.den ↔ n.Coprime Y.den
  constructor
  · intro x;apply Nat.coprime_of_dvd;intro p pp pn
    exact (eqv pp pn).mp (fun pd=>(Nat.not_coprime_of_dvd_of_dvd pp.one_lt pn pd) x)
  · intro y;apply Nat.coprime_of_dvd;intro p pp pn
    exact (eqv pp pn).mpr (fun pd=>(Nat.not_coprime_of_dvd_of_dvd pp.one_lt pn pd) y)

end OMA.CubicBernoulliCriterion284759

/-! The odd cubic test is an ordinary divisibility test on the numerator
of one Bernoulli number. Multiplicities in n are retained on both sides. -/
namespace OMA.CubicBernoulliOriginal284759
open Nat Finset
open OMA.CubicBernoulliCriterion284759

theorem reflection {n e:ℕ} (on:Odd n) (oe:Odd e) (large:3≤e) (cop:n.Coprime e) :
    n^3∣∑i∈Icc 1 (n-1),i^e ↔ n^2∣∑i∈range n,i^(e-1) := by
  have nn:=on.pos
  rw [show Icc 1 (n-1)=Ico 1 n by ext x;simp;omega,
    ←OMA.PowerSumRegular284760.ico_range (f:=fun i:ℕ=>i^(e-1)) nn (zero_pow (by omega : e-1≠0))]
  have ref:=OMA.PowerSumRegular284760.reflect3 (e:=e) on oe large
  constructor
  · intro h
    have z:(∑i∈Ico 1 n,(i:ZMod (n^3))^e)=0 := by
      simpa only [Nat.cast_sum,Nat.cast_pow] using (ZMod.natCast_eq_zero_iff _ _).mpr h
    rw [z,mul_zero] at ref
    have dv:n^3∣n*(e*(∑i∈Ico 1 n,i^(e-1))) := by
      apply (ZMod.natCast_eq_zero_iff _ _).mp;push_cast;rw [←mul_assoc];exact ref.symm
    rw [pow_succ'] at dv
    exact (cop.pow_left 2).dvd_of_dvd_mul_left (Nat.dvd_of_mul_dvd_mul_left nn dv)
  · intro h
    have cube:n^3∣n*(∑i∈Ico 1 n,i^(e-1)) := by rw [pow_succ'];exact Nat.mul_dvd_mul_left _ h
    have zero:(n:ZMod (n^3))*(∑i∈Ico 1 n,(i:ZMod (n^3))^(e-1))=0 := by
      simpa only [Nat.cast_mul,Nat.cast_sum,Nat.cast_pow] using (ZMod.natCast_eq_zero_iff _ _).mpr cube
    rw [mul_right_comm,zero,zero_mul] at ref
    have two:n^3∣2*(∑i∈Ico 1 n,i^e):=(ZMod.natCast_eq_zero_iff _ _).mp (by push_cast;exact ref)
    exact ((Nat.coprime_two_right.mpr on).pow_left 3).dvd_of_dvd_mul_left two

theorem test {n e:ℕ} (on:Odd n) (oe:Odd e) (big:5≤e) (cop:n.Coprime e)
    :
    n^3∣∑i∈Icc 1 (n-1),i^e ↔ n∣(bernoulli (e-1)).num.natAbs := by
  rw [reflection on oe (by omega) cop]
  let b:=e-3
  have form:b+2=e-1:=by dsimp [b];omega
  have plus:b+3=e:=by dsimp [b];omega
  have ev:Even b:=by obtain ⟨j,h⟩:=oe;exact ⟨j-1,by dsimp [b];omega⟩
  rw [←form]
  apply even_iff on.pos (by dsimp [b];omega) ev _ (by rwa [plus])
  intro p hp pn
  have pos:=hp.two_le
  have two:=Nat.not_even_iff_odd.mpr on
  by_contra! h
  exact two (even_iff_two_dvd.mpr (by simpa only [show p=2 by omega] using pn))

theorem original {n:ℕ} (big:7≤n) (on:Odd n) :
    n^3∣∑i∈Icc 1 (n-1),i^(n-2) ↔ n∣(bernoulli (n-3)).num.natAbs := by
  have oe:Odd (n-2):=by obtain ⟨j,h⟩:=on;exact ⟨j-1,by omega⟩
  exact test on oe (by omega) ((Nat.coprime_self_sub_right (by omega)).mpr (Nat.coprime_two_right.mpr on))


end OMA.CubicBernoulliOriginal284759

/-! Both congruences in Conjecture 11 of R. Meštrović, JIS 17 (2014),
Article 14.8.4, hold for one and the same composite input. A rational
congruence modulo m means divisibility by m of the reduced numerator. -/
namespace OMA.ConjectureElevenMestrovic
open Nat Finset
private abbrev R (p : ℕ) [Fact p.Prime] := OMA.BernoulliScreen284760.integers p

def first (n : ℕ) : ℚ := (∑ i ∈ range n, (i : ℚ)^n) - (n:ℚ)^3/2 * bernoulli (n-1)
def second (n : ℕ) : ℚ := (∑ i ∈ range n, (i : ℚ)^(n-1)) - (n:ℚ) * bernoulli (n-1)

theorem first_five : 5^5 ∣ (first 5).num.natAbs := by
  have b : bernoulli 4 = -1/30 := by decide +kernel
  norm_num [first,Finset.sum_range_succ,b]

private theorem numerator {n t : ℕ} (nn:0<n) (x : ℚ)
    (h : ∀ p : ℕ, ∀ hp : p.Prime, p ∣ n → x / (n:ℚ)^t ∈ @R p ⟨hp⟩) :
    n^t ∣ x.num.natAbs := by
  apply OMA.QuarticIff284760.nat_of_local nn
  intro p hp pn
  let _ : Fact p.Prime := ⟨hp⟩
  have id : (x.num:ℚ)/(n:ℚ)^t = x/(n:ℚ)^t*x.den := by
    nth_rw 2 [←Rat.num_div_den x];field_simp
  have m : (x.num:ℚ)/(n:ℚ)^t ∈ R p := by
    rw [id];exact (R p).mul_mem (h p hp pn) (natCast_mem _ _)
  rcases Int.natAbs_eq x.num with a|a
  · rwa [a,Int.cast_natCast] at m
  · rw [a,Int.cast_neg,Int.cast_natCast,neg_div] at m
    exact ((R p).neg_mem_iff).mp m

private theorem early {n p i h : ℕ} [Fact p.Prime] (large:5≤p) (nn:0<n)
    (pn:p∣n) (lt:i+5<h) :
    bernoulli i*(h.choose i:ℚ)*(n:ℚ)^(h-i)/(n:ℚ)^5 ∈R p := by
  have nz : (n:ℚ)≠0 := by exact_mod_cast nn.ne'
  obtain ⟨w, hw⟩ := pn
  have nw : (n:ℚ)=(p:ℚ)*w := by exact_mod_cast hw
  have id : bernoulli i*(h.choose i:ℚ)*(n:ℚ)^(h-i)/(n:ℚ)^5 =
      (p*bernoulli i)*w*(h.choose i:ℚ)*(n:ℚ)^(h-i-6) := by
    conv_lhs => rw [show h-i=(h-i-6)+1+5 by omega,pow_add _ _ 5,pow_succ]
    field_simp;rw [nw];ring
  rw [id]
  exact (R p).mul_mem ((R p).mul_mem ((R p).mul_mem
    (OMA.BernoulliScreen284760.p_bernoulli large i) (natCast_mem _ _)) (natCast_mem _ _))
    ((R p).pow_mem (natCast_mem _ _) _)

private theorem choose4 (b : ℕ) :
    (24:ℚ)*((b+6).choose (b+2):ℚ)=(b+3)*(b+4)*(b+5)*(b+6) := by
  rw [Nat.choose_symm_of_eq_add (show b+6=(b+2)+4 by omega)]
  exact_mod_cast (show 24*((b+6).choose 4)=(b+3)*(b+4)*(b+5)*(b+6) by
    rw [show 24=Nat.factorial 4 by decide,←Nat.descFactorial_eq_factorial_mul_choose]
    simp [Nat.descFactorial,mul_assoc])

private theorem choose3 (b : ℕ) :
    (6:ℚ)*((b+5).choose (b+2):ℚ)=(b+3)*(b+4)*(b+5) := by
  rw [Nat.choose_symm_of_eq_add (show b+5=(b+2)+3 by omega)]
  exact_mod_cast (show 6*((b+5).choose 3)=(b+3)*(b+4)*(b+5) by
    rw [show 6=Nat.factorial 3 by decide,←Nat.descFactorial_eq_factorial_mul_choose]
    simp [Nat.descFactorial,mul_assoc])

private theorem choose2 (b : ℕ) :
    (2:ℚ)*((b+6).choose (b+4):ℚ)=(b+5)*(b+6) := by
  rw [Nat.choose_symm_of_eq_add (show b+6=(b+4)+2 by omega)]
  exact_mod_cast (show 2*((b+6).choose 2)=(b+5)*(b+6) by
    nth_rw 1 [show 2=Nat.factorial 2 by decide]
    rw [←Nat.descFactorial_eq_factorial_mul_choose]
    simp [Nat.descFactorial])

private theorem first_local {p b:ℕ} [Fact p.Prime] (large:5≤p) (bp:0<b) (ev:Even b)
    (pn:p∣b+5) (good:¬p-1∣b+2) : first (b+5) / ((b+5:ℕ):ℚ)^5 ∈ R p := by
  have hp := Fact.out (p:=p.Prime)
  let n := b+5
  have nz : (n:ℚ)≠0 := by dsimp [n];positivity
  have dz : ((b+6:ℕ):ℚ)≠0 := by positivity
  let f (i:ℕ) := bernoulli i*((b+6).choose i:ℚ)*(n:ℚ)^(b+6-i)/(n:ℚ)^5
  have e : (∑ i ∈ range (b+1),f i) ∈ R p := by
    apply (R p).sum_mem
    intro i hi
    exact early large (by dsimp [n];omega) pn (by have :=mem_range.mp hi;omega)
  obtain ⟨j,hj⟩ := ev
  have z1 : f (b+1)=0 := by
    simp [f,bernoulli_eq_zero_of_odd (show Odd (b+1) from ⟨j,by omega⟩) (by omega)]
  have z3 : f (b+3)=0 := by
    simp [f,bernoulli_eq_zero_of_odd (show Odd (b+3) from ⟨j+1,by omega⟩) (by omega)]
  have z5 : f (b+5)=0 := by
    simp [f,bernoulli_eq_zero_of_odd (show Odd (b+5) from ⟨j+2,by omega⟩) (by omega)]
  have nd : ¬ p ∣ 24 := by
    intro dv
    have le := Nat.le_of_dvd (by decide : 0<24) dv
    interval_cases p <;> norm_num at *
  have v : f (b+2) = bernoulli (b+2)*((b+3:ℕ):ℚ)*((b+4:ℕ):ℚ)*((b+6:ℕ):ℚ)*(24:ℚ)⁻¹ := by
    dsimp only [f];rw [show b+6-(b+2)=4 by omega]
    field_simp
    dsimp [n];push_cast
    linear_combination bernoulli (b+2) * (choose4 b)
  have mid : f (b+2)∈R p := by
    rw [v]
    exact (R p).mul_mem ((R p).mul_mem ((R p).mul_mem ((R p).mul_mem
      (OMA.BernoulliScreen284760.bernoulli_integral (by omega) ⟨j+1,by omega⟩ good)
      (natCast_mem _ _)) (natCast_mem _ _)) (natCast_mem _ _))
      (OMA.ThirdOrder284760.inv_mem (d:=24) (by decide) nd)
  have integral : (∑i∈range (b+4), f i) ∈ R p := by
    rw [sum_range_succ,sum_range_succ,sum_range_succ,z1,z3,add_zero,add_zero]
    exact (R p).add_mem e mid
  have faul : (∑ i ∈ range n,(i:ℚ)^n)/(n:ℚ)^5 =
      (∑i ∈ range (b+6), f i)/((b+6:ℕ):ℚ) := by
    rw [sum_range_pow,←Finset.sum_div]
    unfold f;rw [←Finset.sum_div];dsimp [n];push_cast;ring
  have principal : f (b+4)/((b+6:ℕ):ℚ) =
      ((n:ℚ)^3/2*bernoulli (b+4))/(n:ℚ)^5 := by
    dsimp only [f];rw [show b+6-(b+4)=2 by omega]
    field_simp
    dsimp [n];push_cast
    linear_combination bernoulli (b+4) * (choose2 b)
  have unit : ¬p∣b+6 := by
    intro dv
    apply hp.not_dvd_one
    exact (Nat.dvd_add_left pn).mp (by rwa [show 1+(b+5)=b+6 by omega])
  change first n / (n:ℚ)^5 ∈ R p
  rw [first,sub_div,faul,show n-1=b+4 by dsimp [n],←principal,
    sum_range_succ,sum_range_succ,z5,add_zero,add_div,add_sub_cancel_right,div_eq_mul_inv]
  exact (R p).mul_mem integral (OMA.ThirdOrder284760.inv_mem (by omega) unit)

private theorem second_local {p b:ℕ} [Fact p.Prime] (large:5≤p) (bp:0<b) (ev:Even b)
    (pn:p∣b+5) (good:¬p-1∣b) (num:b+5∣(bernoulli (b+2)).num.natAbs) :
    second (b+5)/((b+5:ℕ):ℚ)^4 ∈R p := by
  let n := b+5
  have nz : (n:ℚ)≠0 := by dsimp [n];positivity
  let f (i:ℕ) := bernoulli i*(n.choose i:ℚ)*(n:ℚ)^(n-i)/(n:ℚ)^5
  have e : (∑ i∈range b,f i)∈R p := by
    apply (R p).sum_mem
    intro i hi
    exact early large (by dsimp [n];omega) pn (by have :=mem_range.mp hi;dsimp [n];omega)
  have t0 : f b∈R p := by
    have id : f b=bernoulli b*(n.choose b:ℚ) := by
      dsimp only [f];rw [show n-b=5 by dsimp [n];omega];field_simp
    rw [id];exact (R p).mul_mem (OMA.BernoulliScreen284760.bernoulli_integral bp ev good) (natCast_mem _ _)
  obtain ⟨j,hj⟩ := ev
  have z1 : f (b+1)=0 := by
    simp [f,bernoulli_eq_zero_of_odd (show Odd (b+1) from ⟨j,by omega⟩) (by omega)]
  have z3 : f (b+3)=0 := by
    simp [f,bernoulli_eq_zero_of_odd (show Odd (b+3) from ⟨j+1,by omega⟩) (by omega)]
  have nd : ¬p∣6 := by
    have hp := Fact.out (p:=p.Prime)
    intro dv
    have le := Nat.le_of_dvd (by decide : 0<6) dv
    interval_cases p <;> norm_num at *
  have t2 : f (b+2)∈R p := by
    have eq : f (b+2)=bernoulli (b+2)/(n:ℚ)*((b+3:ℕ):ℚ)*((b+4:ℕ):ℚ)*(6:ℚ)⁻¹ := by
      dsimp only [f];rw [show n-(b+2)=3 by dsimp [n];omega]
      field_simp
      dsimp [n];push_cast
      linear_combination bernoulli (b+2)*(choose3 b)
    rw [eq]
    exact (R p).mul_mem ((R p).mul_mem ((R p).mul_mem
      (OMA.QuarticIff284760.quotient _ (by dsimp [n];omega) pn num) (natCast_mem _ _)) (natCast_mem _ _))
      (OMA.ThirdOrder284760.inv_mem (d:=6) (by decide) nd)
  have integral : (∑i∈range (b+4),f i)∈R p := by
    rw [sum_range_succ,sum_range_succ,sum_range_succ,sum_range_succ,z1,z3,add_zero,add_zero]
    exact (R p).add_mem ((R p).add_mem e t0) t2
  have faul : (∑ i∈range n,(i:ℚ)^(b+4))/(n:ℚ)^4 = ∑i∈range (b+5),f i := by
    rw [sum_range_pow,←Finset.sum_div]
    unfold f;rw [←Finset.sum_div,div_div,pow_succ' (n:ℚ) 4]
    congr 1;dsimp [n];push_cast;ring
  have main : f (b+4)=(n:ℚ)*bernoulli (b+4)/(n:ℚ)^4 := by
    dsimp only [f]
    rw [show n.choose (b+4)=n by exact Nat.choose_succ_self_right _,show n-(b+4)=1 by dsimp [n];omega]
    field_simp
  change second n/(n:ℚ)^4∈R p
  rw [second,show n-1=b+4 by dsimp [n],sub_div,faul,←main,sum_range_succ,add_sub_cancel_right]
  exact integral

/-- A sufficient local test for the first printed congruence. -/
theorem first_test {n:ℕ} (big:7≤n) (on:Odd n)
    (rows : ∀ p:ℕ, p.Prime → p∣n → 5≤p ∧ ¬p-1∣n-3) :
    n^5∣(first n).num.natAbs := by
  apply numerator on.pos
  intro p hp pn
  let _ : Fact p.Prime:=⟨hp⟩
  let b:=n-5
  have bn : n=b+5 := by dsimp [b];omega
  have eq : n-3=b+2 := by omega
  obtain ⟨j,hj⟩:=on
  obtain ⟨large,good⟩:=rows p hp pn
  rw [eq] at good;rw [bn] at pn ⊢
  exact first_local large (by omega) ⟨j-2,by omega⟩ pn good

/-- A sufficient local test for the second printed congruence. -/
theorem second_test {n:ℕ} (big:7≤n) (on:Odd n)
    (num:n∣(bernoulli (n-3)).num.natAbs)
    (rows : ∀ p:ℕ, p.Prime → p∣n → 5≤p ∧ ¬p-1∣n-5) :
    n^4∣(second n).num.natAbs := by
  apply numerator on.pos
  intro p hp pn
  let _ : Fact p.Prime:=⟨hp⟩
  let b:=n-5
  have bn : n=b+5 := by dsimp [b];omega
  have eq : n-3=b+2 := by omega
  obtain ⟨j,hj⟩:=on
  obtain ⟨large,good⟩:=rows p hp pn
  rw [eq,bn] at num;rw [bn] at pn ⊢
  exact second_local large (by omega) ⟨j-2,by omega⟩ pn good num


end OMA.ConjectureElevenMestrovic

/-! The two rational congruences in Meštrović's Conjecture 11, for all inputs. -/
namespace OMA.ClassifyEleven
open Nat Finset OMA.ConjectureElevenMestrovic
open OMA.CubicBernoulliLocal284759
open private Bernoulli.not_dvd_den_bernoulli_add_indicator Bernoulli.vonStaudtIndicator from Mathlib.NumberTheory.Bernoulli

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private theorem regular_iff {p t:ℕ} [Fact p.Prime] (pos:0<t) (ev:Even t) :
    bernoulli t ∈ localRing p ↔ ¬p-1∣t := by
  obtain ⟨k,h⟩:=ev
  have f:t=2*k:=by omega
  have a:=Bernoulli.not_dvd_den_bernoulli_add_indicator (p:=p) (k:=k) (by omega)
  by_cases d:p-1∣t
  · have add:bernoulli t+(p:ℚ)⁻¹ ∈ localRing p := Rat.padicValuation_le_one_iff.mpr
      (by simpa [Bernoulli.vonStaudtIndicator,←f,d] using a)
    simp only [d,not_true_eq_false,iff_false]
    intro bad
    have inv:=(localRing p).sub_mem add bad
    rw [add_sub_cancel_left] at inv
    have nd:=Rat.padicValuation_le_one_iff.mp inv
    rw [Rat.inv_natCast_den_of_pos (Fact.out (p:=p.Prime)).pos] at nd
    exact nd (dvd_refl _)
  · simp only [d,not_false_eq_true,iff_true]
    exact Rat.padicValuation_le_one_iff.mpr (by simpa [Bernoulli.vonStaudtIndicator,←f,d] using a)

private theorem early {n p i h : ℕ} [Fact p.Prime] (large:3≤p) (nn:0<n)
    (pn:p∣n) (lt:i+5<h) :
    bernoulli i*(h.choose i:ℚ)*(n:ℚ)^(h-i)/(n:ℚ)^5 ∈localRing p := by
  have nz : (n:ℚ)≠0 := by exact_mod_cast nn.ne'
  obtain ⟨w,hw⟩:=pn
  have nw:(n:ℚ)=(p:ℚ)*w:=by exact_mod_cast hw
  have id : bernoulli i*(h.choose i:ℚ)*(n:ℚ)^(h-i)/(n:ℚ)^5 =
      (p*bernoulli i)*w*(h.choose i:ℚ)*(n:ℚ)^(h-i-6) := by
    conv_lhs => rw [show h-i=(h-i-6)+1+5 by omega,pow_add _ _ 5,pow_succ]
    field_simp;rw [nw];ring
  rw [id]
  exact (localRing p).mul_mem ((localRing p).mul_mem ((localRing p).mul_mem
    (OMA.CubicBernoulliLocal284759.odd_prime_scaled large i) (natCast_mem _ _)) (natCast_mem _ _))
    ((localRing p).pow_mem (natCast_mem _ _) _)

private theorem first_error {p b:ℕ} [Fact p.Prime] (large:3≤p) (bp:0<b) (ev:Even b)
    (pn:p∣b+5) : 24 * (first (b+5)/((b+5:ℕ):ℚ)^5) -
      ((b+3:ℕ):ℚ)*(b+4:ℕ)*bernoulli (b+2) ∈localRing p := by
  let n:=b+5
  have nz:(n:ℚ)≠0:=by dsimp [n];positivity
  let f (i:ℕ):=bernoulli i*((b+6).choose i:ℚ)*(n:ℚ)^(b+6-i)/(n:ℚ)^5
  have e:(∑i∈range (b+1),f i)∈localRing p:=(localRing p).sum_mem fun i hi=>
    early large (by dsimp [n];omega) pn (by have :=mem_range.mp hi;omega)
  obtain ⟨j,hj⟩:=ev
  have z1:f (b+1)=0:=by simp [f,bernoulli_eq_zero_of_odd (show Odd (b+1) from ⟨j,by omega⟩) (by omega)]
  have z3:f (b+3)=0:=by simp [f,bernoulli_eq_zero_of_odd (show Odd (b+3) from ⟨j+1,by omega⟩) (by omega)]
  have z5:f (b+5)=0:=by simp [f,bernoulli_eq_zero_of_odd (show Odd (b+5) from ⟨j+2,by omega⟩) (by omega)]
  have faul:(∑i∈range n,(i:ℚ)^n)/(n:ℚ)^5=(∑i∈range (b+6),f i)/((b+6:ℕ):ℚ) := by
    rw [sum_range_pow,←Finset.sum_div];unfold f;rw [←Finset.sum_div];dsimp [n];push_cast;ring
  have principal : f (b+4)/((b+6:ℕ):ℚ)=((n:ℚ)^3/2*bernoulli (b+4))/(n:ℚ)^5 := by
    dsimp only [f];rw [show b+6-(b+4)=2 by omega];field_simp;dsimp [n];push_cast
    linear_combination bernoulli (b+4) * (OMA.ConjectureElevenMestrovic.choose2 b)
  have mid : 24*f (b+2)/((b+6:ℕ):ℚ)=((b+3:ℕ):ℚ)*(b+4:ℕ)*bernoulli (b+2) := by
    dsimp only [f];rw [show b+6-(b+2)=4 by omega];field_simp;dsimp [n];push_cast
    linear_combination bernoulli (b+2) * (OMA.ConjectureElevenMestrovic.choose4 b)
  have unit : ¬p∣b+6:=by
    intro dv;exact (Fact.out (p:=p.Prime)).not_dvd_one ((Nat.dvd_add_left pn).mp (by rwa [show 1+(b+5)=b+6 by omega]))
  change 24*(first n/(n:ℚ)^5)-_∈_
  rw [first,sub_div,faul,show n-1=b+4 by dsimp [n],←principal,←mid]
  rw [sum_range_succ,sum_range_succ,sum_range_succ,sum_range_succ,sum_range_succ,z1,z3,z5]
  convert (localRing p).mul_mem ((localRing p).mul_mem (natCast_mem _ 24) e) (inverse_mem unit) using 1; ring

private theorem even_fail {n:ℕ} (big:4≤n) (en:Even n) :
    ¬n^5∣(first n).num.natAbs ∧ ¬n^4∣(second n).num.natAbs := by
  obtain ⟨j,hj⟩:=en
  have oe:Odd (n-1):=⟨j-1,by omega⟩
  have ev:Even (n-1-1):=⟨j-1,by omega⟩
  have bz:=bernoulli_eq_zero_of_odd oe (by omega)
  have castpow (e:ℕ) : (∑i∈range n,(i:ℚ)^e)=((∑i∈range n,i^e:ℕ):ℚ):=by push_cast;rfl
  simp only [first,second,bz,mul_zero,sub_zero,castpow,Rat.num_natCast,Int.natAbs_natCast]
  refine ⟨fun h=>OMA.QuarticAll284760.even_obstruction (by omega) ⟨j,hj⟩ (by omega) ⟨j,hj⟩
    ((dvd_pow_self n (by decide : 5≠0)).trans h),?_⟩
  intro h
  let R:=ZMod (n^2)
  have nn:0<n:=by omega
  have sq:(n:R)^2=0:=by rw [←Nat.cast_pow];exact ZMod.natCast_self _
  have reflected:2*(∑i∈Ico 1 n,(i:R)^(n-1))=(n:R)*(n-1:ℕ)*(∑i∈Ico 1 n,(i:R)^(n-1-1)):=by
    rw [two_mul];nth_rw 1 [←OMA.PowerSumRegular284760.mirror n (fun i=>(i:R)^(n-1))]
    rw [←sum_add_distrib,Finset.mul_sum];apply sum_congr rfl;intro i hi
    rw [Nat.cast_sub (mem_Ico.mp hi).2.le,sub_eq_neg_add,OMA.PowerSum284760.taylor _ _ sq,
      oe.neg_pow,ev.neg_pow];ring
  have div:n^2∣∑i∈Ico 1 n,i^(n-1):=by
    rw [OMA.PowerSumRegular284760.ico_range (f:=fun i:ℕ=>i^(n-1)) nn (zero_pow (by omega))]
    exact (pow_dvd_pow n (by decide : 2≤4)).trans h
  have z:(∑i∈Ico 1 n,(i:R)^(n-1))=0:=by
    simpa only [Nat.cast_sum,Nat.cast_pow] using (ZMod.natCast_eq_zero_iff _ _).mpr div
  rw [z,mul_zero,mul_assoc] at reflected
  have d:n*n∣n*((n-1)*(∑i∈Ico 1 n,i^(n-1-1))):=by
    rw [←pow_two];apply (ZMod.natCast_eq_zero_iff _ _).mp;push_cast;exact reflected.symm
  have cop:n.Coprime (n-1):=(Nat.coprime_self_sub_right (by omega)).mpr (by simp)
  have fail:=cop.dvd_of_dvd_mul_left (Nat.dvd_of_mul_dvd_mul_left nn d)
  rw [OMA.PowerSumRegular284760.ico_range (f:=fun i:ℕ=>i^(n-1-1)) nn (zero_pow (by omega))] at fail
  exact OMA.QuarticAll284760.even_obstruction nn ⟨j,hj⟩ (by omega) ev fail

private theorem units {p b:ℕ} [Fact p.Prime] (hg:3≤p) (pn:p∣b+5) :
    ¬p∣b+3 ∧ ¬p∣b+4 := by
  constructor
  · intro d
    have t:p∣2:=(Nat.dvd_add_left d).mp (by rwa [show 2+(b+3)=b+5 by omega])
    have :=Nat.le_of_dvd (by decide : 0<2) t;omega
  · intro d
    exact (Fact.out (p:=p.Prime)).not_dvd_one ((Nat.dvd_add_left d).mp (by rwa [show 1+(b+4)=b+5 by omega]))

private theorem cancel_units {p b:ℕ} [Fact p.Prime] (hg:3≤p) (pn:p∣b+5)
    {x:ℚ} (h : ((b+3:ℕ):ℚ)*(b+4:ℕ)*x∈localRing p) : x∈localRing p := by
  obtain ⟨u,v⟩:=units hg pn
  have m:=(localRing p).mul_mem ((localRing p).mul_mem h (inverse_mem u)) (inverse_mem v)
  convert m using 1;field_simp

private theorem scaled_mem {n p t:ℕ} [Fact p.Prime] (nn:0<n) (pn:p∣n)
    (tp:0<t) {x:ℚ} (h:n^t∣x.num.natAbs) : x/(n:ℚ)^t∈localRing p := by
  simpa only [Nat.cast_pow] using OMA.QuarticIff284760.quotient x (pow_pos nn t)
    (pn.trans (dvd_pow_self n tp.ne')) h

private theorem odd_prime_three {n p:ℕ} (on:Odd n) (pr:p.Prime) (pn:p∣n) : 3≤p := by
  have :=pr.two_le
  by_contra! h
  exact on.not_two_dvd_nat ((show p=2 by omega) ▸ pn)

/-- The first congruence is exactly a list of divisibility tests on the prime factors. -/
theorem first_iff {n:ℕ} (hn:2≤n) : n^5∣(first n).num.natAbs ↔
    Odd n ∧ ∀ p:ℕ, p.Prime → p∣n → ¬p-1∣n-3 := by
  by_cases big:7≤n
  · rcases Nat.even_or_odd n with en|on
    · simp [(even_fail (by omega) en).1,Nat.not_odd_iff_even.mpr en]
    · let b:=n-5
      have nf:n=b+5:=by dsimp [b];omega
      have bp:0<b:=by omega
      have ev:Even b:=by obtain ⟨j,h⟩:=on;exact ⟨j-2,by omega⟩
      have eq:n-3=b+2:=by omega
      refine ⟨fun good=>⟨on,fun p hp pn=>?_⟩,fun good=>?_⟩
      · let _ : Fact p.Prime:=⟨hp⟩
        have hg:=odd_prime_three on hp pn
        have h:=scaled_mem on.pos pn (by decide : 0<5) good
        rw [nf] at pn h
        have err:=first_error hg bp ev pn
        have val:= (localRing p).sub_mem ((localRing p).mul_mem (natCast_mem (localRing p) 24) h) err
        norm_num only [Nat.cast_ofNat,sub_sub_cancel] at val
        rw [eq]
        exact (regular_iff (by omega) (ev.add (by decide : Even 2))).mp (cancel_units hg pn val)
      · apply first_test big on
        intro p hp pn
        have d:=good.2 p hp pn
        have hg:=odd_prime_three on hp pn
        refine ⟨?_,d⟩
        by_contra! small
        have prim:p=3:=by interval_cases p <;> norm_num at *
        obtain ⟨j,h⟩:=on
        rw [prim] at d;omega
  · interval_cases n
    · simp [show ¬Odd 2 by decide];decide +kernel
    · constructor
      · intro h;exact False.elim ((by decide +kernel : ¬3^5∣(first 3).num.natAbs) h)
      · intro h;exact False.elim (h.2 3 (by decide) (by decide) (dvd_zero _))
    · simp [show ¬Odd 4 by decide];decide +kernel
    · refine ⟨fun _=>⟨by decide,fun p hp pn=>?_⟩,fun _=>first_five⟩
      obtain rfl:=(Nat.prime_dvd_prime_iff_eq hp (by decide)).mp pn;decide
    · simp [show ¬Odd 6 by decide];decide +kernel

private theorem second_error {p b:ℕ} [Fact p.Prime] (large:3≤p) (bp:0<b) (ev:Even b)
    (pn:p∣b+5) : second (b+5)/((b+5:ℕ):ℚ)^4 -
      bernoulli b*((b+5).choose 5:ℚ) -
      (((b+3:ℕ):ℚ)*(b+4:ℕ)*(bernoulli (b+2)/(b+5:ℕ)))/6 ∈localRing p := by
  let n:=b+5
  have nz:(n:ℚ)≠0:=by dsimp [n];positivity
  let f (i:ℕ):=bernoulli i*(n.choose i:ℚ)*(n:ℚ)^(n-i)/(n:ℚ)^5
  have e:(∑i∈range b,f i)∈localRing p:=(localRing p).sum_mem fun i hi=>
    early large (by dsimp [n];omega) pn (by have :=mem_range.mp hi;dsimp [n];omega)
  obtain ⟨j,hj⟩:=ev
  have z1:f (b+1)=0:=by simp [f,bernoulli_eq_zero_of_odd (show Odd (b+1) from ⟨j,by omega⟩) (by omega)]
  have z3:f (b+3)=0:=by simp [f,bernoulli_eq_zero_of_odd (show Odd (b+3) from ⟨j+1,by omega⟩) (by omega)]
  have term0:f b=bernoulli b*((b+5).choose 5:ℚ):=by
    dsimp only [f];rw [show n-b=5 by dsimp [n];omega,Nat.choose_symm_of_eq_add (show n=b+5 by rfl)]
    field_simp;rfl
  have term2:f (b+2)=(((b+3:ℕ):ℚ)*(b+4:ℕ)*(bernoulli (b+2)/(b+5:ℕ)))/6:=by
    dsimp only [f];rw [show n-(b+2)=3 by dsimp [n];omega]
    dsimp [n];field_simp;push_cast;linear_combination bernoulli (b+2)*(OMA.ConjectureElevenMestrovic.choose3 b)
  have faul:(∑i∈range n,(i:ℚ)^(b+4))/(n:ℚ)^4=∑i∈range (b+5),f i:=by
    rw [sum_range_pow,←Finset.sum_div];unfold f;rw [←Finset.sum_div,div_div,pow_succ' (n:ℚ) 4]
    congr 1;dsimp [n];push_cast;ring
  have main:f (b+4)=(n:ℚ)*bernoulli (b+4)/(n:ℚ)^4:=by
    dsimp only [f];rw [show n.choose (b+4)=n by exact Nat.choose_succ_self_right _,show n-(b+4)=1 by dsimp [n];omega];field_simp
  change second n/(n:ℚ)^4-_-_∈_
  rw [second,show n-1=b+4 by dsimp [n],sub_div,faul,←main,←term0,←term2]
  rw [sum_range_succ,sum_range_succ,sum_range_succ,sum_range_succ,sum_range_succ,z1,z3]
  convert e using 1;ring

private theorem middle_combo {p b:ℕ} [Fact p.Prime] (hg:3≤p) (bp:0<b) (ev:Even b)
    (pn:p∣b+5) (good:second (b+5)/((b+5:ℕ):ℚ)^4∈localRing p) :
    bernoulli b*((b+5).choose 5:ℚ) +
      (((b+3:ℕ):ℚ)*(b+4:ℕ)*(bernoulli (b+2)/(b+5:ℕ)))/6 ∈localRing p := by
  have err:=second_error hg bp ev pn
  convert (localRing p).sub_mem good err using 1;ring

private theorem middle_away {p b:ℕ} [Fact p.Prime] (hg:3≤p) (bp:0<b) (ev:Even b)
    (pn:p∣b+5) (ne:p≠5) (good:second (b+5)/((b+5:ℕ):ℚ)^4∈localRing p) :
    bernoulli (b+2)/(b+5:ℕ)∈localRing p := by
  have eq:=Nat.add_one_mul_choose_eq (b+4) 4
  have d:p∣((b+5).choose 5)*5:=eq ▸ dvd_mul_of_dvd_left pn _
  have div:=((Fact.out (p:=p.Prime)).dvd_mul.mp d).resolve_right
    (fun h=>ne ((Nat.prime_dvd_prime_iff_eq (Fact.out (p:=p.Prime)) (by decide : Nat.Prime 5)).mp h))
  obtain ⟨t,ht⟩:=div
  have m:bernoulli b*((b+5).choose 5:ℚ)∈localRing p:=by
    rw [ht,Nat.cast_mul,mul_left_comm];rw [←mul_assoc]
    exact (localRing p).mul_mem (OMA.CubicBernoulliLocal284759.odd_prime_scaled hg b) (natCast_mem _ _)
  have val:=(localRing p).sub_mem (middle_combo hg bp ev pn good) m
  apply cancel_units hg pn
  convert (localRing p).mul_mem val (natCast_mem _ 6) using 1;push_cast;ring

private theorem residue_five {b:ℕ} (bp:0<b) (ev:Even b) (bn:5∣b+5) (row:4∣b) :
    (bernoulli (b+2)-1)/5∈localRing 5 := by
  have h:5∣b:=by omega
  have f:b+2=20*(b/20)+2:=by omega
  let S:=∑i∈range 5,i^(b+2)
  have congr:(S:ZMod 25)=5:=by
    dsimp [S];push_cast
    rw [f];simp only [sum_range_succ,sum_range_zero,Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat,
      pow_add,pow_mul,show (0:ZMod 25)^20=0 by decide,show (1:ZMod 25)^20=1 by decide,
      show (2:ZMod 25)^20=1 by decide,show (3:ZMod 25)^20=1 by decide,
      show (4:ZMod 25)^20=1 by decide,zero_pow (by decide : 2≠0),mul_zero,
      one_pow,one_mul,zero_add];decide
  have md:S%25=5:=by exact (ZMod.natCast_eq_natCast_iff S 5 25).mp congr
  have sn:S=25*(S/25)+5:=by omega
  have err:=error (p:=5) (n:=5) (b:=b) (by decide) (by decide) (dvd_refl _)
    ev bp (by omega)
  have er:(S:ℚ)/25-bernoulli (b+2)/5∈localRing 5:=by
    dsimp [S];push_cast;norm_num at err ⊢;exact err
  have fs:(S:ℚ)=25*((S/25:ℕ):ℚ)+5:=by exact_mod_cast sn
  convert (localRing 5).sub_mem (natCast_mem _ (S/25)) er using 1
  rw [fs];ring

private theorem five_impossible {b:ℕ} (bp:0<b) (ev:Even b) (pn:5∣b+5)
    (good:second (b+5)/((b+5:ℕ):ℚ)^4 ∈localRing 5) : False := by
  obtain ⟨m,hm⟩:=pn
  have pn:5∣b+5:=⟨m,hm⟩
  have nq:((b+5:ℕ):ℚ)=5*m:=by exact_mod_cast hm
  let c:ℚ:=((b+3:ℕ):ℚ)*(b+4:ℕ)
  let T:ℕ:=(b+5).choose 5
  let E:ℚ:=bernoulli b*T+c*(bernoulli (b+2)/(b+5:ℕ))/6
  have e:E∈localRing 5:=middle_combo (by decide) bp ev pn good
  have nz:((b+5:ℕ):ℚ)≠0:=by positivity
  have ben:c*bernoulli (b+2)∈localRing 5:=by
    have a:=(localRing 5).mul_mem ((localRing 5).mul_mem (natCast_mem _ 6) (natCast_mem _ (b+5))) e
    have v:=(localRing 5).mul_mem ((localRing 5).mul_mem ((localRing 5).mul_mem (natCast_mem _ 6)
      (natCast_mem _ m)) (OMA.CubicBernoulliLocal284759.odd_prime_scaled (p:=5) (by decide) b)) (natCast_mem _ T)
    convert (localRing 5).sub_mem a v using 1
    dsimp only [E];rw [nq]
    have mn:(m:ℚ)≠0:=by intro z;rw [z,mul_zero] at nq;contradiction
    push_cast;field_simp;ring
  have nr:= (regular_iff (p:=5) (by omega : 0<b+2) (ev.add (by decide : Even 2))).mp
    (cancel_units (by decide) pn ben)
  obtain ⟨j,hj⟩:=ev
  have row:4∣b:=by omega
  have rb:=residue_five bp ⟨j,hj⟩ pn row
  have two:b=2*j:=by omega
  have ind:=Bernoulli.not_dvd_den_bernoulli_add_indicator (p:=5) (k:=j) (by omega)
  have cb:bernoulli b+1/5∈localRing 5:=by
    apply Rat.padicValuation_le_one_iff.mpr
    simpa [Bernoulli.vonStaudtIndicator,←two,show (5:ℕ)-1=4 by decide,row,one_div] using ind
  have cn:c∈localRing 5:=(localRing 5).mul_mem (natCast_mem _ _) (natCast_mem _ _)
  have sub:(c-6*m*T)/5∈localRing 5:=by
    have a:=(localRing 5).mul_mem ((localRing 5).mul_mem (natCast_mem _ 6) (natCast_mem _ m)) e
    have v:=(localRing 5).mul_mem ((localRing 5).mul_mem ((localRing 5).mul_mem (natCast_mem _ 6)
      (natCast_mem _ m)) (natCast_mem _ T)) cb
    convert (localRing 5).sub_mem ((localRing 5).sub_mem a v) ((localRing 5).mul_mem cn rb) using 1
    dsimp only [E];rw [nq];have mn:(m:ℚ)≠0:=by intro z;rw [z,mul_zero] at nq;contradiction
    push_cast;field_simp;ring
  let x:ℤ:= ((b+3:ℕ):ℤ)*(b+4:ℕ)-6*(m:ℤ)*T
  have mem:(x:ℚ)/5∈localRing 5:=by dsimp [x];push_cast;dsimp [c] at sub;push_cast at sub;exact sub
  have dv:5∣x.natAbs:=by
    convert (OMA.ConjectureElevenMestrovic.numerator (n:=5) (t:=1) (by decide) (x:ℚ) ?_) using 1 <;> simp
    intro p hp pd;obtain rfl:=(Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5)).mp pd
    simpa using mem
  have z:(x:ZMod 5)=0:=(ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr (Int.natCast_dvd.mpr dv)
  have luc:T≡m [MOD 5]:=by
    dsimp [T];rw [hm]
    simpa using (Choose.choose_mul_mul_modEq_choose_nat (p:=5) (a:=m) (b:=1))
  have l: (T:ZMod 5)=m:=(ZMod.natCast_eq_natCast_iff ..).mpr luc
  have bz:(b:ZMod 5)=0:=(ZMod.natCast_eq_zero_iff ..).mpr (by omega)
  dsimp [x] at z;push_cast at z;rw [l,bz] at z
  have nonsq:∀y:ZMod 5,(0+3)*(0+4)-6*y*y≠0:=by decide
  exact nonsq m z

private theorem second_of_num {n:ℕ} (big:7≤n) (on:Odd n) (num:n∣(bernoulli (n-3)).num.natAbs) :
    n^4∣(second n).num.natAbs := by
  let b:=n-5
  have bn:n=b+5:=by dsimp [b];omega
  have exp:n-3=b+2:=by omega
  have bp:0<b:=by omega
  have ev:Even b:=by obtain ⟨j,h⟩:=on;exact ⟨j-2,by omega⟩
  apply second_test big on num
  intro p hp pn
  let _ : Fact p.Prime:=⟨hp⟩
  have hg:=odd_prime_three on hp pn
  have dx:p∣(bernoulli (b+2)).num.natAbs:=by rw [←exp];exact pn.trans num
  have nr:¬p-1∣b+2:=(regular_iff (p:=p) (by omega) (ev.add (by decide : Even 2))).mp
    (Rat.padicValuation_le_one_iff.mpr (hp.coprime_iff_not_dvd.mp ((bernoulli (b+2)).reduced.of_dvd_left dx)))
  have large:5≤p:=by
    by_contra! small
    have four:p≠4:=by intro h;subst p;exact (by decide : ¬Nat.Prime 4) hp
    have h3:p=3:=by omega
    rw [h3] at nr;obtain ⟨j,h⟩:=ev;omega
  have unit:p.Coprime (b+3):=hp.coprime_iff_not_dvd.mpr (units hg (bn ▸ pn)).1
  have ls:p^2∣∑i∈range p,i^(b+2):=(OMA.CubicBernoulliCriterion284759.even_iff hp.pos bp ev
    (fun q hq qp=>(Nat.prime_dvd_prime_iff_eq hq hp).mp qp ▸ hg) unit).mpr dx
  rw [←exp] at ls
  exact ⟨large,OMA.DoubleBernoulli284760.not_two_of_test hp large on pn ls⟩

/-- The second congruence is precisely divisibility of the adjacent Bernoulli numerator. -/
theorem second_iff {n:ℕ} (hn:2≤n) : n^4∣(second n).num.natAbs ↔
    Odd n ∧ n∣(bernoulli (n-3)).num.natAbs := by
  by_cases big:7≤n
  · rcases Nat.even_or_odd n with en|on
    · simp [(even_fail (by omega) en).2,Nat.not_odd_iff_even.mpr en]
    · refine ⟨fun good=>⟨on,?_⟩,fun pair=>second_of_num big on pair.2⟩
      let b:=n-5
      have nf:n=b+5:=by dsimp [b];omega
      have bp:0<b:=by omega
      have ev:Even b:=by obtain ⟨j,h⟩:=on;exact ⟨j-2,by omega⟩
      apply (OMA.CubicBernoulliCriterion284759.denominator on.pos _).mpr
      apply Nat.coprime_of_dvd
      intro p hp pn
      let _ : Fact p.Prime:=⟨hp⟩
      apply Rat.padicValuation_le_one_iff.mp
      change _∈localRing p
      have hg:=odd_prime_three on hp pn
      have localmem:=scaled_mem on.pos pn (by decide : 0<4) good
      rw [show n-3=b+2 by omega,nf]
      rw [nf] at pn localmem
      by_cases is5:p=5
      · subst p;exact False.elim (five_impossible bp ev pn localmem)
      · exact middle_away hg bp ev pn is5 localmem
  · interval_cases n <;> decide +kernel

/-- Thus the second congruence always implies the first one. -/
theorem second_implies_first {n:ℕ} (hn:2≤n) (h:n^4∣(second n).num.natAbs) :
    n^5∣(first n).num.natAbs := by
  obtain ⟨on,num⟩:=(second_iff hn).mp h
  by_cases big:7≤n
  · apply (first_iff hn).mpr
    refine ⟨on,fun p hp pn=>?_⟩
    let _ : Fact p.Prime:=⟨hp⟩
    obtain ⟨j,hj⟩:=on
    exact (regular_iff (p:=p) (by omega : 0<n-3) ⟨j-1,by omega⟩).mp
      (Rat.padicValuation_le_one_iff.mpr (hp.coprime_iff_not_dvd.mp ((bernoulli (n-3)).reduced.of_dvd_left (pn.trans num))))
  · interval_cases n <;> revert h <;> decide +kernel

#print axioms first_iff
#print axioms second_iff
#print axioms second_implies_first

/-- Equality of the input sets in the second part of Conjecture 11 and in the
cubic divisibility condition of Conjecture 12. -/
theorem second_iff_cubic {n:ℕ} (hn:2≤n) : n^4∣(second n).num.natAbs ↔
    n^3∣∑i∈Icc 1 (n-1),i^(n-2) := by
  by_cases big:7≤n
  · rw [second_iff hn]
    rcases Nat.even_or_odd n with en|on
    · have no:¬Odd n:=Nat.not_odd_iff_even.mpr en
      simp only [no,false_and,false_iff]
      have ev:Even (n-2):=by obtain ⟨k,h⟩:=en;exact ⟨k-1,by omega⟩
      rw [show Icc 1 (n-1)=Ico 1 n by ext i;simp;omega,
        OMA.PowerSumRegular284760.ico_range (f:=fun i:ℕ=>i^(n-2)) (by omega) (zero_pow (by omega))]
      intro test
      exact OMA.QuarticAll284760.even_obstruction (by omega) en (by omega) ev
        ((dvd_pow_self n (by decide : 3≠0)).trans test)
    · simpa [on] using (OMA.CubicBernoulliOriginal284759.original big on).symm
  · interval_cases n <;> decide +kernel

#print axioms second_iff_cubic
end OMA.ClassifyEleven
