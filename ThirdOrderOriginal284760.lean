import Mathlib

/-! Quartic power sums and the reduced Bernoulli numerator. See quartic-bernoulli-284760.md for the theorem and data provenance. -/

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

private theorem lift_pow_sum {p m : ℕ} (odd : Odd p) (pm : p∣m) (e : ℕ) :
    (∑i∈range (m*p),(i:ZMod (p*m))^e)=(p:ZMod (p*m))*∑i∈range m,(i:ZMod (p*m))^e := by
  have mm : (m:ZMod (p*m))^2=0 := by
    rw [←Nat.cast_pow,ZMod.natCast_eq_zero_iff,pow_two]
    exact Nat.mul_dvd_mul_right pm m
  have sum_div : p ∣ ∑j∈range p,j := by
    obtain ⟨u,h⟩:=odd
    use u
    have s:=sum_range_id_mul_two p
    rw [show p-1=2*u by omega] at s
    nlinarith only [s]
  have vanish : (m:ZMod (p*m))*(∑j∈range p,(j:ZMod (p*m)))=0 := by
    rw [←Nat.cast_sum,←Nat.cast_mul,ZMod.natCast_eq_zero_iff,Nat.mul_comm p m]
    exact Nat.mul_dvd_mul_left m sum_div
  rw [blocks,sum_comm,mul_sum]
  apply sum_congr rfl
  intro i _
  calc
    _=∑j∈range p, ((i:ZMod (p*m))^e + ((e:ZMod (p*m))*i^(e-1)*m)*j) := by
      apply sum_congr rfl;intro j _
      push_cast
      rw [add_comm,taylor (i:ZMod (p*m)) (_*_) (by rw [mul_pow,mm,zero_mul])]
      ring
    _ = _ := by
      rw [sum_add_distrib,←mul_sum,mul_assoc _ (m:ZMod (p*m)),vanish,mul_zero,add_zero,sum_const,card_range,nsmul_eq_mul]

private theorem base_nonzero {p e : ℕ} (hp:p.Prime) (ep:0<e) (he:p-1∣e) :
    (∑ i∈range p,(i:ZMod p)^e)≠0 := by
  let _ : Fact p.Prime := ⟨hp⟩
  have h1:=sum_range_add_sum_Ico (fun i:ℕ=>(i:ZMod p)^e) hp.one_le
  rw [←h1]
  have same (i) (hi:i∈Ico 1 p) : (i:ZMod p)^e=1 := by
    have nz : (i:ZMod p)≠0 := by
      intro h
      have := Nat.le_of_dvd (mem_Ico.mp hi).1 ((ZMod.natCast_eq_zero_iff ..).mp h)
      exact (mem_Ico.mp hi).2.not_ge this
    obtain ⟨a,ha⟩:=he
    rw [ha,pow_mul,ZMod.pow_card_sub_one_eq_one nz,one_pow]
  simp only [sum_congr rfl same,sum_const,Nat.card_Ico,nsmul_eq_mul,mul_one]
  simp [zero_pow ep.ne',Nat.cast_sub hp.one_le]

/-- For a positive exponent divisible by p−1, the complete sum is not a
multiple of n whenever n is an odd multiple of p. -/
private theorem obstruction {p e : ℕ} (hp : p.Prime) (odd : Odd p) (ep:0<e)
    (he:p-1∣e) (n:ℕ) (np:0<n) (div:p∣n) : ¬n∣∑i∈range n,i^e := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    obtain ⟨m,rfl⟩:=div
    have mp : 0 < m := Nat.pos_of_mul_pos_left np
    by_cases pm : p∣m
    · intro hz
      have hzero: (∑i∈range (m*p),(i:ZMod (p*m))^e)=0 := by
        simpa only [mul_comm m p,←Nat.cast_pow,←Nat.cast_sum,ZMod.natCast_eq_zero_iff] using hz
      rw [lift_pow_sum odd pm e] at hzero
      simp only [←Nat.cast_pow,←Nat.cast_sum,←Nat.cast_mul,ZMod.natCast_eq_zero_iff] at hzero
      exact ih m (by nlinarith only [hp.one_lt,mp]) mp pm (Nat.dvd_of_mul_dvd_mul_left hp.pos hzero)
    · intro hz
      have hzero : (∑i∈range (p*m),(i:ZMod p)^e)=0 := by
        simpa only [←Nat.cast_pow,←Nat.cast_sum,ZMod.natCast_eq_zero_iff] using
          (show p∣∑i∈range (p*m),i^e from (dvd_mul_right p m).trans hz)
      rw [blocks_cast] at hzero
      let _ : Fact p.Prime:=⟨hp⟩
      exact (mul_ne_zero (fun hm=>(pm ((ZMod.natCast_eq_zero_iff ..).mp hm))) (base_nonzero hp ep he)) hzero

private theorem reflect {n e : ℕ} (he : Odd e) :
    2*(∑i∈Ico 1 n,(i:ZMod (n^2))^e)=
      (n:ZMod (n^2))*e*(∑i∈Ico 1 n,(i:ZMod (n^2))^(e-1)) := by
  let R:= ZMod (n^2)
  have sq : (n:R)^2=0 := by rw [←Nat.cast_pow];exact ZMod.natCast_self _
  have mirror : (∑i∈Ico 1 n,((n-i:ℕ):R)^e)=∑i∈Ico 1 n,(i:R)^e := by
    apply sum_bij' (fun i _=>n-i) (fun i _=>n-i)
    all_goals intro i hi;obtain ⟨low,high⟩:=mem_Ico.mp hi
    all_goals first | exact mem_Ico.mpr ⟨by omega,by omega⟩ | omega | rfl
  have ev : Even (e-1) := by obtain ⟨b,hb⟩:=he;exact ⟨b,by omega⟩
  rw [two_mul]
  nth_rw 1 [←mirror]
  rw [←sum_add_distrib,mul_sum]
  apply sum_congr rfl
  intro i hi
  rw [Nat.cast_sub (mem_Ico.mp hi).2.le,sub_eq_neg_add,taylor _ _ sq,he.neg_pow,ev.neg_pow]
  ring

/-- A prime with p−1 ∣ n−3 already obstructs divisibility by n². -/
theorem local_obstruction {n p:ℕ} (odd:Odd n) (hp:p.Prime) (pn:p∣n) (he:p-1∣n-3) :
    ¬ n^2∣∑i∈Ico 1 n,i^(n-2) := by
  have pos:=odd.pos
  have hn:=Nat.le_of_dvd pos pn
  have po : Odd p := Nat.coprime_two_left.mp ((Nat.coprime_two_left.mpr odd).of_dvd_right pn)
  have big : 3≤n := by have :=hp.two_le;obtain ⟨b,h⟩:=odd;omega
  by_cases eq : n=3
  · subst n;decide
  have exp : 0<n-3 := by omega
  have eodd : Odd (n-2) := by obtain ⟨b,h⟩:=odd;exact ⟨b-1,by omega⟩
  intro zz
  have val := reflect (n:=n) eodd
  have left : (∑i∈Ico 1 n,(i:ZMod (n^2))^(n-2))=0 := by
    simpa only [←Nat.cast_pow,←Nat.cast_sum,ZMod.natCast_eq_zero_iff] using zz
  rw [left,mul_zero,show n-2-1=n-3 by omega] at val
  have sqdiv : n^2∣n*(n-2)*(∑i∈Ico 1 n,i^(n-3)) := by
    simpa only [←Nat.cast_pow,←Nat.cast_sum,←Nat.cast_mul,ZMod.natCast_eq_zero_iff] using val.symm
  rw [pow_two,mul_assoc n] at sqdiv
  have cut:=Nat.dvd_of_mul_dvd_mul_left pos sqdiv
  have cop : n.Coprime (n-2) :=
    (Nat.coprime_self_sub_right (by omega)).mpr (Nat.coprime_two_right.mpr odd)
  have dvd:=cop.dvd_of_dvd_mul_left cut
  have id := sum_range_add_sum_Ico (fun i:ℕ=>i^(n-3)) (show 1≤n by omega)
  have conv : (∑i∈Ico 1 n,i^(n-3))=∑i∈range n,i^(n-3) := by
    simpa [zero_pow exp.ne'] using id
  exact obstruction hp po exp he n pos pn (conv ▸ dvd)

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

private theorem div_linear {p:ℕ} (odd:Odd p) : p∣∑j∈range p,j := by
  obtain ⟨u,h⟩:=odd
  refine ⟨u,?_⟩
  have s:=sum_range_id_mul_two p
  rw [show p-1=2*u by omega] at s
  nlinarith only [s]

private theorem div_square {p:ℕ} (hp:p.Prime) (big:5≤p) : p∣∑j∈range p,j^2 := by
  have formula (b:ℕ) : 6*(∑j∈range b,j^2)+3*b^2=2*b^3+b := by
    induction b with
    | zero=>simp
    | succ b ih=>rw [sum_range_succ];nlinarith only [ih]
  have h : p∣6*(∑j∈range p,j^2) := by
    apply (Nat.dvd_add_left (show p∣3*p^2 from dvd_mul_of_dvd_right (dvd_pow_self p (by decide : 2≠0)) _)).mp
    rw [formula];exact dvd_add (dvd_mul_of_dvd_right (dvd_pow_self p (by decide : 3≠0)) _) (dvd_refl p)
  apply (hp.dvd_mul.mp h).resolve_left
  intro hd
  change p ∣ 2*3 at hd
  rcases hp.dvd_mul.mp hd with a|a
  · have :=Nat.le_of_dvd (by decide : 0<2) a;omega
  · have :=Nat.le_of_dvd (by decide : 0<3) a;omega

/-- Sum the second-order expansion over a rectangle of complete blocks. -/
private theorem moments {R:Type*} [CommRing R] (m k e:ℕ) (zero:(m:R)^3=0) :
    (∑i∈range (m*k),(i:R)^e)=
    k*(∑i∈range m,(i:R)^e) +
    (e:R)*(m:R)*(∑j∈range k,(j:R))*(∑i∈range m,(i:R)^(e-1))+
    (e.choose 2:R)*(m:R)^2*(∑j∈range k,(j:R)^2)*(∑i∈range m,(i:R)^(e-2)) := by
  rw [OMA.PowerSum284760.blocks,sum_comm]
  calc
    _ = ∑i∈range m, ∑j∈range k, ((i:R)^e +
          ((e:R)*m*(i:R)^(e-1))*j + ((e.choose 2:R)*(m:R)^2*(i:R)^(e-2))*j^2) := by
      apply sum_congr rfl;intro i _
      apply sum_congr rfl;intro j _
      push_cast
      rw [add_comm,quad (i:R) (_*_) (by rw [mul_pow,zero,zero_mul])]
      ring
    _ = ∑i∈range m, ((k:R)*(i:R)^e +
         ((e:R)*m*(∑j∈range k,(j:R)))*(i:R)^(e-1)+
         ((e.choose 2:R)*(m:R)^2*(∑j∈range k,(j:R)^2))*(i:R)^(e-2)) := by
      apply sum_congr rfl;intro i _
      simp only [sum_add_distrib,←mul_sum,sum_const,card_range,nsmul_eq_mul]
      ring
    _ = _ := by simp only [sum_add_distrib,←mul_sum]

private theorem odd_range {n e:ℕ} (on:Odd n) (oe:Odd e) : n∣∑i∈range n,i^e := by
  rw [←ico_range on.pos (by exact zero_pow oe.pos.ne')]
  exact odd_sum on oe

private theorem lift_two {p m e : ℕ} (hp:p.Prime) (big:5≤p) (pm:p∣m)
    (om:Odd m) (odd:Odd (e-1)) :
    (∑i∈range (m*p),(i:ZMod (p^2*m))^e)=
      (p:ZMod (p^2*m))*∑i∈range m,(i:ZMod (p^2*m))^e := by
  let R:=ZMod (p^2*m)
  have vanish (a:ℕ) (h:p^2*m∣a) : (a:R)=0 := (ZMod.natCast_eq_zero_iff ..).mpr h
  have cube : (m:R)^3=0 := by
    rw [←Nat.cast_pow]; apply vanish;rw [pow_succ];exact Nat.mul_dvd_mul_right (pow_dvd_pow_of_dvd pm 2) m
  have lin : (m:R)*(∑j∈range p,(j:R))*(∑i∈range m,(i:R)^(e-1))=0 := by
    have h : p^2*m ∣ m*(∑j∈range p,j)*(∑i∈range m,i^(e-1)) := by
      obtain ⟨u,hu⟩:=div_linear (hp.odd_of_ne_two (by omega))
      obtain ⟨v,hv⟩:=pm.trans (odd_range om odd)
      use u*v;rw [hu,hv];ring
    simpa only [R,Nat.cast_mul,Nat.cast_sum,Nat.cast_pow] using vanish _ h
  have sq : (m:R)^2*(∑j∈range p,(j:R)^2)=0 := by
    simp only [←Nat.cast_pow,←Nat.cast_sum,←Nat.cast_mul];apply vanish
    obtain ⟨u,hu⟩:=pm;obtain ⟨v,hv⟩:=div_square hp big
    use u*v;rw [hu,hv];ring
  rw [moments (R:=R) m p e cube]
  linear_combination (e:R)*lin + (e.choose 2:R)*(∑i∈range m,(i:R)^(e-2))*sq

private theorem first_block {p m e : ℕ} (op:Odd p) (od:Odd (e-1)) :
    (∑i∈range (p*m),(i:ZMod (p^2))^e)=(m:ZMod (p^2))*∑i∈range p,(i:ZMod (p^2))^e := by
  let R:=ZMod (p^2)
  have sq : (p:R)^2=0 := by rw [←Nat.cast_pow];exact ZMod.natCast_self _
  have lin : (p:R)*(∑i∈range p,(i:R)^(e-1))=0 := by
    have h : p^2 ∣ p*(∑i∈range p,i^(e-1)) := by
      rw [pow_two];exact Nat.mul_dvd_mul_left _ (odd_range op od)
    simpa only [Nat.cast_mul,Nat.cast_sum,Nat.cast_pow] using (ZMod.natCast_eq_zero_iff _ _).mpr h
  rw [moments (R:=R) p m e (by rw [pow_succ,sq,zero_mul]),sq];simp only [mul_zero,zero_mul,add_zero]
  linear_combination (e:R)*(∑j∈range m,(j:R))*lin

private theorem shrink {p e : ℕ} (hp : p.Prime) (big:5≤p) (od:Odd (e-1))
    (n:ℕ) (on:Odd n) (pn:p∣n) (hs:p*n∣∑i∈range n,i^e) : p^2∣∑i∈range p,i^e := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    obtain ⟨m,rfl⟩:=pn
    have mp:=Nat.pos_of_mul_pos_left on.pos
    have op := hp.odd_of_ne_two (by omega)
    have om : Odd m := (Nat.odd_mul.mp on).2
    rw [←mul_assoc,pow_two p|>.symm] at hs
    by_cases pm:p∣m
    · have hzero : (∑i∈range (m*p),(i:ZMod (p^2*m))^e)=0 := by
        simpa only [mul_comm m p,Nat.cast_sum,Nat.cast_pow] using (ZMod.natCast_eq_zero_iff _ _).mpr hs
      rw [lift_two hp big pm om od] at hzero
      have hz : p^2*m∣p*(∑i∈range m,i^e) := (ZMod.natCast_eq_zero_iff _ _).mp (by push_cast;exact hzero)
      rw [pow_two,mul_assoc] at hz
      exact ih m (by nlinarith only [hp.one_lt,mp]) om pm (Nat.dvd_of_mul_dvd_mul_left hp.pos hz)
    · have hzero : (∑i∈range (p*m),(i:ZMod (p^2))^e)=0 := by
        simpa only [Nat.cast_sum,Nat.cast_pow] using
          (ZMod.natCast_eq_zero_iff _ _).mpr ((dvd_mul_right (p^2) m).trans hs)
      rw [first_block op od] at hzero
      apply ((hp.coprime_iff_not_dvd.mpr pm).pow_left 2).dvd_of_dvd_mul_left
      exact (ZMod.natCast_eq_zero_iff _ _).mp (by push_cast;exact hzero)

/-- Every prime divisor of an odd counterexample must already pass this
complete residue test modulo its square, regardless of its multiplicity. -/
theorem prime_test {n p:ℕ} (on:Odd n) (hp:p.Prime) (big:5≤p) (pn:p∣n)
    (hz:n^4∣∑i∈Ico 1 n,i^(n-2)) : p^2∣∑i∈Ico 1 p,i^(n-3) := by
  have np:=on.pos
  have nn:=Nat.le_of_dvd np pn
  have od : Odd (n-2) := by obtain ⟨k,h⟩:=on;exact ⟨k-1,by omega⟩
  have od' : Odd (n-3-1) := by obtain ⟨k,h⟩:=on;exact ⟨k-2,by omega⟩
  have val := reflect3 on od (by omega)
  have zeros : (∑i∈Ico 1 n,(i:ZMod (n^3))^(n-2))=0 := by
    simpa only [Nat.cast_sum,Nat.cast_pow] using (ZMod.natCast_eq_zero_iff _ _).mpr
      ((pow_dvd_pow n (by decide : 3≤4)).trans hz)
  rw [zeros,mul_zero,show n-2-1=n-3 by omega] at val
  have dv : n^3∣n*((n-2)*(∑i∈Ico 1 n,i^(n-3))) :=
    (ZMod.natCast_eq_zero_iff _ _).mp (by push_cast;rw [←mul_assoc];exact val.symm)
  have cop : n.Coprime (n-2) :=
    (Nat.coprime_self_sub_right (by omega)).mpr (Nat.coprime_two_right.mpr on)
  rw [pow_succ'] at dv
  have sq := (cop.pow_left 2).dvd_of_dvd_mul_left (Nat.dvd_of_mul_dvd_mul_left np dv)
  rw [ico_range np (by exact zero_pow (by omega : n-3≠0))] at sq
  rw [ico_range hp.pos (by exact zero_pow (by omega : n-3≠0))]
  exact shrink hp big od' n on pn ((show p*n∣n^2 by rw [pow_two];exact Nat.mul_dvd_mul_right pn n).trans sq)

/-- The local test is finite for each prime: the exponent has period p(p−1). -/
theorem finite_test {n p:ℕ} (on:Odd n) (hp:p.Prime) (big:5≤p) (pn:p∣n)
    (hz:n^4∣∑i∈Ico 1 n,i^(n-2)) :
    let r:=(n-3)%(p*(p-1))
    r%2=0 ∧ (r+3)%p=0 ∧ p^2∣∑i∈Ico 1 p,i^r := by
  have evenp : 2∣p-1 := by
    obtain ⟨b,hb⟩:=hp.odd_of_ne_two (by omega)
    exact ⟨b,by omega⟩
  have parity : 2∣n-3 := by
    obtain ⟨b,hb⟩:=on;exact ⟨b-1,by omega⟩
  have nn:=Nat.le_of_dvd on.pos pn
  refine ⟨?_,?_,?_⟩
  · rw [Nat.mod_mod_of_dvd _ (dvd_mul_of_dvd_right evenp _)]
    exact Nat.mod_eq_zero_of_dvd parity
  · rw [Nat.add_mod, Nat.mod_mod_of_dvd _ (dvd_mul_right p (p-1)),←Nat.add_mod,
        Nat.sub_add_cancel (by omega : 3≤n)]
    exact Nat.mod_eq_zero_of_dvd pn
  have loc:=prime_test on hp big pn hz
  have moduli : (p^2).totient=p*(p-1) := by simpa using Nat.totient_prime_pow_succ hp 1
  have congr (i:ℕ) (hi:i∈Ico 1 p) :
      (i:ZMod (p^2))^(n-3)=(i:ZMod (p^2))^((n-3)%(p*(p-1))) := by
    have c : p.Coprime i := hp.coprime_iff_not_dvd.mpr (fun d=>
      (mem_Ico.mp hi).2.not_ge (Nat.le_of_dvd (mem_Ico.mp hi).1 d))
    have h := Nat.pow_totient_mod (x:=i) (k:=n-3) (n:=p^2) (by nlinarith only [big]) (c.symm.pow_right 2)
    rw [moduli] at h
    simpa only [Nat.cast_pow] using (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  simp only [Nat.cast_sum,Nat.cast_pow,←sum_congr rfl congr]
  simpa only [Nat.cast_sum,Nat.cast_pow] using (ZMod.natCast_eq_zero_iff _ _).mpr loc

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

private theorem scaled_terms {p n b:ℕ} [Fact p.Prime] (hp:5≤p)
    (nn:0<n) (pn:p∣n) (i:ℕ) (lt:i<b) :
    bernoulli i*((b+4).choose i:ℚ)*(n:ℚ)^(b+4-i)/(n:ℚ)^4 ∈integers p := by
  obtain ⟨u,hu⟩:=pn
  have hpow : b+4-i=(b-i-1)+1+4:=by omega
  have nz:(n:ℚ)≠0:=by exact_mod_cast nn.ne'
  have hm:(n:ℚ)=(p:ℚ)*u:=by exact_mod_cast hu
  have id : bernoulli i*((b+4).choose i:ℚ)*(n:ℚ)^(b+4-i)/(n:ℚ)^4 =
      (p*bernoulli i)*u*((b+4).choose i:ℚ)*(n:ℚ)^(b-i-1) := by
    rw [hpow,pow_add _ _ 4,pow_succ];field_simp;rw [hm];ring
  rw [id]
  exact (integers p).mul_mem ((integers p).mul_mem ((integers p).mul_mem (p_bernoulli hp i)
    (natCast_mem (integers p) u)) (natCast_mem (integers p) _))
    ((integers p).pow_mem (natCast_mem (integers p) _) _)

private theorem principal {n p b:ℕ} [Fact p.Prime] (hp:7≤p) (nform:n=b+5)
    (eb:Even b) (pn:p∣n) (nd:¬p-1∣b) (sq:n^4∣∑i∈range n,i^(b+3)) :
    bernoulli (b+2)*((b+4).choose (b+2):ℚ)/(n:ℚ)^2 ∈integers p := by
  have nn:0<n:=by omega
  have bpos:0<b:=by have :=Nat.le_of_dvd nn pn;omega
  have nz:(n:ℚ)≠0:=by exact_mod_cast nn.ne'
  let f (i:ℕ) := bernoulli i*((b+4).choose i:ℚ)*(n:ℚ)^(b+4-i)/(n:ℚ)^4
  have integral : (∑i∈range (b+4),f i)∈integers p := by
    obtain ⟨c,hc⟩:=sq
    have faul:=sum_range_pow n (b+3)
    have scast : (∑i∈range n,(i:ℚ)^(b+3))=(n:ℚ)^4*c:=by exact_mod_cast hc
    rw [scast,←Finset.sum_div] at faul
    have den:(b+3+1:ℚ)≠0:=by positivity
    have alg: (∑i∈range (b+4),f i)= (b+3+1:ℚ)*c := by
      unfold f;rw [←Finset.sum_div]
      rw [div_eq_iff (pow_ne_zero 4 nz)]
      push_cast at faul
      have v:=(eq_div_iff den).mp faul
      linear_combination -v
    rw [alg];exact (integers p).mul_mem (by exact_mod_cast natCast_mem (integers p) (b+3+1)) (natCast_mem (integers p) c)
  have early : (∑i∈range b,f i)∈integers p :=
    (integers p).sum_mem (fun i hi=>scaled_terms (by omega : 5≤p) nn pn i (mem_range.mp hi))
  have fb : f b∈integers p := by
    have nb:=bernoulli_integral bpos eb nd
    have eq:f b=bernoulli b*((b+4).choose b:ℚ):=by dsimp [f];rw [show b+4-b=4 by omega];field_simp
    rw [eq];exact (integers p).mul_mem nb (natCast_mem (integers p) _)
  have odd1:Odd (b+1):=by obtain ⟨t,ht⟩:=eb;exact ⟨t,by omega⟩
  have odd3:Odd (b+3):=by obtain ⟨t,ht⟩:=eb;exact ⟨t+1,by omega⟩
  have z1:f (b+1)=0:=by simp [f,bernoulli_eq_zero_of_odd odd1 (by omega)]
  have z3:f (b+3)=0:=by simp [f,bernoulli_eq_zero_of_odd odd3 (by omega)]
  rw [Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_succ,z1,z3,add_zero,add_zero] at integral
  have last:= (integers p).sub_mem integral ((integers p).add_mem early fb)
  rw [add_sub_cancel_left] at last
  have eq:f (b+2)=bernoulli (b+2)*((b+4).choose (b+2):ℚ)/(n:ℚ)^2:=by
    dsimp [f];rw [show b+4-(b+2)=2 by omega];field_simp
  simpa only [eq] using last

private theorem numerator_of_scaled_integral {p n a c:ℕ} [Fact p.Prime] (q:ℚ)
    (nn:0<n) (pn:p^a∣n) (pc:p.Coprime c)
    (mem:q*c/(n:ℚ)^2∈integers p) : p^(2*a)∣q.num.natAbs := by
  let x:=q*c/(n:ℚ)^2
  have dx:¬p∣x.den:=(integral_iff _).mp mem
  have nz:(n:ℚ)≠0:=by exact_mod_cast nn.ne'
  have alg : (x.num:ℚ)*q.den*(n:ℚ)^2=q.num*c*x.den := by
    have h : (x.num:ℚ)/x.den=((q.num:ℚ)/q.den)*c/(n:ℚ)^2 := by
      rw [Rat.num_div_den,Rat.num_div_den]
    have xd:(x.den:ℚ)≠0:=by exact_mod_cast x.den_ne_zero
    have qd:(q.den:ℚ)≠0:=by exact_mod_cast q.den_ne_zero
    field_simp at h;linear_combination h
  have ints : x.num*(q.den:ℤ)*(n:ℤ)^2=q.num*c*x.den := by exact_mod_cast alg
  have natid:=congrArg Int.natAbs ints
  simp only [Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_natCast] at natid
  have left:p^(2*a)∣n^2 := by
    rw [mul_comm 2 a,pow_mul];exact pow_dvd_pow_of_dvd pn 2
  have prod := dvd_mul_of_dvd_right left (x.num.natAbs*q.den)
  rw [natid,mul_assoc] at prod
  exact ((pc.mul_right ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr dx)).pow_left (2*a)).dvd_of_dvd_mul_right prod

/-- If p−1 does not divide n−5, a counterexample forces the full square of
each p-power divisor of n to divide the Bernoulli numerator at n−3. -/
theorem square_bernoulli {n p a:ℕ} (hp:p.Prime) (large:7≤p) (on:Odd n)
    (pos:0<a) (dvd:p^a∣n) (nonres:¬p-1∣n-5)
    (bad:n^4∣∑i∈Ico 1 n,i^(n-2)) : p^(2*a)∣(bernoulli (n-3)).num.natAbs := by
  let _ : Fact p.Prime:=⟨hp⟩
  have pn:= (dvd_pow_self _ pos.ne').trans dvd
  have lg:=Nat.le_of_dvd on.pos pn
  let b:=n-5
  have nf:n=b+5:=by dsimp [b];omega
  have ev:Even b:=by obtain ⟨j,hj⟩:=on;exact ⟨j-2,by dsimp [b];omega⟩
  have exp:n-2=b+3:=by omega
  have exp':n-3=b+2:=by omega
  have cd:p.Coprime ((b+4).choose (b+2)) := by
    apply hp.coprime_iff_not_dvd.mpr
    intro h
    have id:2*((b+4).choose (b+2))=(b+4)*(b+3) := by
      rw [Nat.choose_symm_of_eq_add (show b+4=(b+2)+2 by omega),Nat.choose_two_right]
      have even:2∣(b+4)*(b+3):=dvd_mul_of_dvd_left (show 2∣b+4 from ev.add (by decide : Even 4) |>.two_dvd) _
      rw [show b+4-1=b+3 by omega,Nat.mul_div_cancel' even]
    have d:=(dvd_mul_of_dvd_right h 2);rw [id] at d
    rcases hp.dvd_mul.mp d with d|d
    · have dd:p∣1:=by apply (Nat.dvd_add_left d).mp;simpa only [nf,show b+4+1=b+5 by omega,add_comm 1 (b+4)] using pn
      exact hp.not_dvd_one dd
    · have dd:p∣2:=by apply (Nat.dvd_add_left d).mp;simpa only [nf,show b+3+2=b+5 by omega,add_comm 2 (b+3)] using pn
      have :=Nat.le_of_dvd (by decide : 0<2) dd;omega
  rw [exp] at bad
  have split:=sum_range_add_sum_Ico (fun i:ℕ=>i^(b+3)) on.pos
  have same:(∑i∈Ico 1 n,i^(b+3))=∑i∈range n,i^(b+3):=by simpa using split
  rw [same] at bad
  rw [exp']
  exact numerator_of_scaled_integral _ on.pos dvd cd (principal large nf ev pn nonres bad)

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

theorem not_two {n p:ℕ} (hp:p.Prime) (big:5≤p) (on:Odd n) (pn:p∣n)
    (bad:n^4∣∑i∈Ico 1 n,i^(n-2)) : ¬p-1∣n-5 := by
  have nn:=Nat.le_of_dvd on.pos pn
  have h:=OMA.PowerSumRegular284760.prime_test on hp big pn bad
  rw [OMA.PowerSumRegular284760.ico_range hp.pos (by exact zero_pow (by omega : n-3≠0))] at h
  exact not_two_of_test hp big on pn h

/-- All prime divisors p≥7 of a counterexample, without an index exception,
must divide the Bernoulli numerator to twice their multiplicity in n. -/
theorem square_bernoulli {n p a:ℕ} (hp:p.Prime) (large:7≤p) (on:Odd n)
    (pos:0<a) (dvd:p^a∣n) (bad:n^4∣∑i∈Ico 1 n,i^(n-2)) :
    p^(2*a)∣(bernoulli (n-3)).num.natAbs :=
  OMA.BernoulliScreen284760.square_bernoulli hp large on pos dvd
    (not_two hp (by omega) on ((dvd_pow_self _ pos.ne').trans dvd) bad) bad

/-- Meštrović's quartic divisibility at any odd n forces the entire square
of n to divide the reduced numerator of the single Bernoulli number B_(n−3). -/
theorem whole_square {n:ℕ} (on:Odd n) (bad:n^4∣∑i∈Ico 1 n,i^(n-2)) :
    n^2∣(bernoulli (n-3)).num.natAbs := by
  by_cases z:(bernoulli (n-3)).num.natAbs=0
  · rw [z];exact dvd_zero _
  apply (Nat.factorization_prime_le_iff_dvd (pow_ne_zero _ on.pos.ne') z).mp
  intro p hp
  simp only [Nat.factorization_pow,Finsupp.nsmul_apply,smul_eq_mul]
  by_cases a:n.factorization p=0
  · simp [a]
  have pd:= (hp.dvd_iff_one_le_factorization on.pos.ne').mpr (by omega)
  have nr : ¬p-1∣n-3 := fun h => OMA.PowerSum284760.local_obstruction on hp pd h
    ((pow_dvd_pow n (by decide : 2≤4)).trans bad)
  have large:7≤p := by
    by_contra! small
    have op:=Nat.coprime_two_left.mp ((Nat.coprime_two_left.mpr on).of_dvd_right pd)
    obtain ⟨j,hj⟩:=op
    have :=hp.two_le
    have :=Nat.le_of_dvd on.pos pd
    obtain ⟨t,ht⟩:=on
    have cases:p=3 ∨ p=5 := by omega
    rcases cases with rfl|rfl
    · omega
    · have nt:=not_two hp (by decide) (show Odd n from ⟨t,ht⟩) pd bad
      omega
  apply (hp.pow_dvd_iff_le_factorization z).mp
  exact square_bernoulli hp large on (by omega) ((hp.pow_dvd_iff_le_factorization on.pos.ne').mpr le_rfl) bad

end OMA.DoubleBernoulli284760

namespace OMA.ThirdOrder284760
open Finset Nat
open OMA.BernoulliScreen284760

private abbrev localRing (p:ℕ) [Fact p.Prime] := OMA.BernoulliScreen284760.integers p

private theorem inv_mem {p d:ℕ} [Fact p.Prime] (pos:0<d) (good:¬p∣d):
    (d:ℚ)⁻¹∈localRing p := by
  apply (OMA.BernoulliScreen284760.integral_iff _).mpr
  rwa [Rat.inv_natCast_den_of_pos pos]

private theorem quotient_mem {p:ℕ} [Fact p.Prime] (x:ℚ) (d:p^2∣x.num.natAbs) :
    x/(p:ℚ)^2∈localRing p := by
  have pr:=Fact.out (p:=p.Prime)
  have dvd:p∣x.num.natAbs := (dvd_pow_self p (by decide : 2≠0)).trans d
  have good : ¬p∣x.den := pr.coprime_iff_not_dvd.mp (x.reduced.of_dvd_left dvd)
  obtain ⟨t, ht⟩:=Int.natCast_dvd.mpr d
  have hid:(x.num:ℚ)=(p:ℚ)^2*t:=by exact_mod_cast ht
  have zn:(p:ℚ)≠0:=by exact_mod_cast pr.ne_zero
  have eq:x/(p:ℚ)^2=(t:ℚ)*(x.den:ℚ)⁻¹ := by
    nth_rw 1 [←Rat.num_div_den x]
    rw [hid];field_simp
  rw [eq];exact (localRing p).mul_mem (intCast_mem _ _) (inv_mem x.den_pos good)

private theorem integral_cube {p a:ℕ} [Fact p.Prime]
    (h:(a:ℚ)/(p:ℚ)^3∈localRing p) : p^3∣a := by
  let x:ℚ:=(a:ℚ)/(p:ℚ)^3
  have hp:=Fact.out (p:=p.Prime)
  have good:=hp.coprime_iff_not_dvd.mpr ((OMA.BernoulliScreen284760.integral_iff x).mp h)
  have nz:(p:ℚ)≠0:=by exact_mod_cast hp.ne_zero
  have eq:(x.num:ℚ)/x.den=a/(p:ℚ)^3 := Rat.num_div_den _
  have dn:(x.den:ℚ)≠0:=by exact_mod_cast x.den_ne_zero
  field_simp at eq
  have eq':x.num*(p:ℤ)^3=(a:ℤ)*x.den:=by rw [mul_comm (a:ℤ)];exact_mod_cast eq
  have nat:=congrArg Int.natAbs eq'
  simp only [Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_natCast] at nat
  have dv:=dvd_mul_left (p^3) x.num.natAbs
  rw [nat] at dv
  exact (good.pow_left 3).dvd_of_dvd_mul_right dv

/-- The full third-order complete residue test, independent of the remaining
prime factors or their multiplicities. -/
theorem cube_test {n p:ℕ} (hp:p.Prime) (big:7≤p) (on:Odd n) (pn:p∣n)
    (bad:n^4∣∑i∈Ico 1 n,i^(n-2)) : p^3∣∑i∈range p,i^(n-3) := by
  let _ : Fact p.Prime:=⟨hp⟩
  let b:=n-5
  have nn:=Nat.le_of_dvd on.pos pn
  have bp:0<b:=by dsimp [b];omega
  have eb:Even b:=by obtain ⟨j,hj⟩:=on;exact ⟨j-2,by dsimp [b];omega⟩
  have e:n-3=b+2 := by dsimp [b];omega
  have nform:n=b+5 := by dsimp [b];omega
  have nd:=OMA.DoubleBernoulli284760.not_two hp (by omega) on pn bad
  have sq:=OMA.DoubleBernoulli284760.square_bernoulli (a:=1) hp big on (by decide)
    (by simpa using pn) bad
  rw [e] at sq ⊢
  have zn:(p:ℚ)≠0:=by exact_mod_cast hp.ne_zero
  let f (i:ℕ) := bernoulli i*((b+3).choose i:ℚ)*(p:ℚ)^(b+3-i)/(p:ℚ)^3
  have early : (∑i∈range b,f i)∈localRing p := by
    apply (localRing p).sum_mem
    intro i hi
    have lt:=mem_range.mp hi
    have id:f i=(p*bernoulli i)*((b+3).choose i:ℚ)*(p:ℚ)^(b-i-1) := by
      dsimp [f];rw [show b+3-i=(b-i-1)+1+3 by omega,pow_add _ _ 3,pow_succ]
      field_simp
    rw [id]
    exact (localRing p).mul_mem ((localRing p).mul_mem
      (OMA.BernoulliScreen284760.p_bernoulli (by omega : 5≤p) i) (natCast_mem _ _))
      ((localRing p).pow_mem (natCast_mem _ p) _)
  have fb:f b∈localRing p := by
    have id:f b=bernoulli b*((b+3).choose b:ℚ) := by dsimp [f];rw [show b+3-b=3 by omega];field_simp
    rw [id];exact (localRing p).mul_mem (OMA.BernoulliScreen284760.bernoulli_integral bp eb nd) (natCast_mem _ _)
  have ob:Odd (b+1):=by obtain ⟨j,hj⟩:=eb;exact ⟨j,by omega⟩
  have z1:f (b+1)=0 := by simp [f,bernoulli_eq_zero_of_odd ob (by omega)]
  have z2:f (b+2)∈localRing p := by
    have id:f (b+2)=bernoulli (b+2)/(p:ℚ)^2*((b+3).choose (b+2):ℚ) := by
      dsimp [f];rw [show b+3-(b+2)=1 by omega,pow_one];field_simp
    rw [id];exact (localRing p).mul_mem (quotient_mem _ sq) (natCast_mem _ _)
  have all:(∑i∈range (b+3),f i)∈localRing p := by
    rw [sum_range_succ,sum_range_succ,sum_range_succ,z1,add_zero]
    exact (localRing p).add_mem ((localRing p).add_mem early fb) z2
  have unit:¬p∣b+3 := by
    intro d
    have two:p∣2:=(Nat.dvd_add_left d).mp (by simpa only [show 2+(b+3)=n by omega] using pn)
    have :=Nat.le_of_dvd (by decide : 0<2) two;omega
  apply integral_cube
  have val:((∑i∈range p,i^(b+2):ℕ):ℚ)/(p:ℚ)^3 =
      (∑i∈range (b+3),f i)*((b+3:ℕ):ℚ)⁻¹ := by
    push_cast
    rw [sum_range_pow,←Finset.sum_div]
    unfold f;rw [←Finset.sum_div]
    push_cast;ring
  rw [val];exact (localRing p).mul_mem all (inv_mem (by omega) unit)

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

private theorem not_regular_den {p t:ℕ} [Fact p.Prime] (pos:0<t)
    (ev:Even t) (hd:p∣(bernoulli t).num.natAbs): ¬p-1∣t := by
  intro reg
  have hp:=Fact.out (p:=p.Prime)
  have be:bernoulli t∈R p:=(OMA.BernoulliScreen284760.integral_iff _).mpr
    (hp.coprime_iff_not_dvd.mp ((bernoulli t).reduced.of_dvd_left hd))
  obtain ⟨k,hk⟩:=ev
  have tform:t=2*k:=by omega
  have v:=Bernoulli.not_dvd_den_bernoulli_add_indicator (p:=p) (k:=k) (by omega)
  have add:bernoulli t+(p:ℚ)⁻¹∈R p:=by
    apply (OMA.BernoulliScreen284760.integral_iff _).mpr
    simpa [←tform,Bernoulli.vonStaudtIndicator,reg] using v
  have inv:=(R p).sub_mem add be
  rw [add_sub_cancel_left] at inv
  have contra:=(OMA.BernoulliScreen284760.integral_iff _).mp inv
  rw [Rat.inv_natCast_den_of_pos hp.pos] at contra
  exact contra (dvd_refl _)

private theorem local_square {p b:ℕ} [Fact p.Prime] (big:5≤p) (ev:Even b) (bp:0<b)
    (unit:¬p∣b+3) (num:p^2∣(bernoulli (b+2)).num.natAbs) :
    p^2∣∑i∈range p,i^(b+2) := by
  have hp:=Fact.out (p:=p.Prime)
  have nz:(p:ℚ)≠0:=by exact_mod_cast hp.ne_zero
  let f (i:ℕ):=bernoulli i*((b+3).choose i:ℚ)*(p:ℚ)^(b+3-i)/(p:ℚ)^2
  have early :(∑i∈range (b+1),f i)∈R p := by
    apply (R p).sum_mem;intro i hi;have lt:=mem_range.mp hi
    have id:f i=(p*bernoulli i)*((b+3).choose i:ℚ)*(p:ℚ)^(b-i) := by
      dsimp [f];rw [show b+3-i=(b-i)+1+2 by omega,pow_add _ _ 2,pow_succ];field_simp
    rw [id];exact (R p).mul_mem ((R p).mul_mem
      (OMA.BernoulliScreen284760.p_bernoulli big i) (natCast_mem _ _)) ((R p).pow_mem (natCast_mem _ p) _)
  have ob:Odd (b+1):=by obtain ⟨j,hj⟩:=ev;exact ⟨j,by omega⟩
  have z1:f (b+1)=0:=by simp [f,bernoulli_eq_zero_of_odd ob (by omega)]
  have top:f (b+2)∈R p := by
    have id:f (b+2)=bernoulli (b+2)/(p^2:ℕ)*(((b+3).choose (b+2):ℚ)*p) := by
      dsimp [f];rw [show b+3-(b+2)=1 by omega,pow_one];push_cast;field_simp
    rw [id];exact (R p).mul_mem (quotient _ (pow_pos hp.pos _) (dvd_pow_self p (by decide)) num)
      ((R p).mul_mem (natCast_mem _ _) (natCast_mem _ _))
  have all:(∑i∈range (b+3),f i)∈R p := by
    rw [sum_range_succ,sum_range_succ,z1,add_zero];exact (R p).add_mem early top
  have mem:((∑i∈range p,i^(b+2):ℕ):ℚ)/(p:ℚ)^2∈R p := by
    have id:((∑i∈range p,i^(b+2):ℕ):ℚ)/(p:ℚ)^2 =
        (∑i∈range (b+3),f i)*((b+3:ℕ):ℚ)⁻¹ := by
      push_cast;rw [sum_range_pow,←Finset.sum_div];unfold f;rw [←Finset.sum_div];push_cast;ring
    rw [id];exact (R p).mul_mem all (OMA.ThirdOrder284760.inv_mem (by omega) unit)
  apply nat_of_local hp.pos
  intro q hq dq
  obtain rfl:=(Nat.prime_dvd_prime_iff_eq hq hp).mp dq;exact mem

private theorem quartic_local {p n b:ℕ} [Fact p.Prime] (big:5≤p) (pn:p∣n)
    (nf:n=b+5) (bp:0<b) (ev:Even b) (good:¬p-1∣b)
    (num:n^2∣(bernoulli (b+2)).num.natAbs) :
    ((∑i∈range n,i^(b+3):ℕ):ℚ)/(n:ℚ)^4∈R p := by
  have nn:0<n:=by omega
  have nz:(n:ℚ)≠0:=by exact_mod_cast nn.ne'
  let f (i:ℕ):=bernoulli i*((b+4).choose i:ℚ)*(n:ℚ)^(b+4-i)/(n:ℚ)^4
  have early:(∑i∈range b,f i)∈R p := (R p).sum_mem fun i hi=>
    OMA.BernoulliScreen284760.scaled_terms big nn pn i (mem_range.mp hi)
  have term0:f b∈R p := by
    have id:f b=bernoulli b*((b+4).choose b:ℚ):=by dsimp [f];rw [show b+4-b=4 by omega];field_simp
    rw [id];exact (R p).mul_mem (OMA.BernoulliScreen284760.bernoulli_integral bp ev good) (natCast_mem _ _)
  have term2:f (b+2)∈R p := by
    have id:f (b+2)=bernoulli (b+2)/(n^2:ℕ)*((b+4).choose (b+2):ℚ):=by
      dsimp [f];rw [show b+4-(b+2)=2 by omega];push_cast;field_simp
    rw [id];exact (R p).mul_mem
      (quotient _ (pow_pos nn _) (pn.trans (dvd_pow_self _ (by decide))) num) (natCast_mem _ _)
  have ob:Odd (b+1):=by obtain ⟨j,hj⟩:=ev;exact ⟨j,by omega⟩
  have oc:Odd (b+3):=by obtain ⟨j,hj⟩:=ev;exact ⟨j+1,by omega⟩
  have z1:f (b+1)=0:=by simp [f,bernoulli_eq_zero_of_odd ob (by omega)]
  have z3:f (b+3)=0:=by simp [f,bernoulli_eq_zero_of_odd oc (by omega)]
  have all:(∑i∈range (b+4),f i)∈R p := by
    rw [sum_range_succ,sum_range_succ,sum_range_succ,sum_range_succ,z3,z1,add_zero,add_zero]
    exact (R p).add_mem ((R p).add_mem early term0) term2
  have unit:¬p∣b+4:=by
    intro d
    exact (Fact.out : p.Prime).not_dvd_one <| (Nat.dvd_add_left d).mp (by rwa [show 1+(b+4)=n by omega])
  have id:((∑i∈range n,i^(b+3):ℕ):ℚ)/(n:ℚ)^4 =
      (∑i∈range (b+4),f i)*((b+4:ℕ):ℚ)⁻¹ := by
    push_cast;rw [sum_range_pow,←Finset.sum_div];unfold f;rw [←Finset.sum_div];push_cast;ring
  rw [id];exact (R p).mul_mem all (OMA.ThirdOrder284760.inv_mem (by omega) unit)

/-- Exact composite-and-prime Bernoulli characterization of the original
quartic power-sum congruence for every positive odd n. -/
theorem original_iff {n:ℕ} (on:Odd n) :
    n^4∣∑i∈Ico 1 n,i^(n-2) ↔ n^2∣(bernoulli (n-3)).num.natAbs := by
  refine ⟨OMA.DoubleBernoulli284760.whole_square on,?_⟩
  intro sq
  by_cases nn:7≤n
  · let b:=n-5
    have nf:n=b+5:=by dsimp [b];omega
    have bp:0<b:=by omega
    have ev:Even b:=by obtain ⟨j,hj⟩:=on;exact ⟨j-2,by omega⟩
    have exp:n-3=b+2:=by omega
    rw [exp] at sq
    rw [show n-2=b+3 by omega]
    have split:=sum_range_add_sum_Ico (fun i:ℕ=>i^(b+3)) on.pos
    have same:(∑i∈Ico 1 n,i^(b+3))=∑i∈range n,i^(b+3):=by simpa using split
    rw [same]
    apply nat_of_local on.pos
    intro p hp pn
    let _ : Fact p.Prime:=⟨hp⟩
    have q2:p^2∣(bernoulli (b+2)).num.natAbs := (pow_dvd_pow_of_dvd pn 2).trans sq
    have nr:=not_regular_den (by omega : 0<b+2) (ev.add (by decide : Even 2))
      ((dvd_pow_self _ (by decide : 2≠0)).trans q2)
    have oddp:=Nat.coprime_two_left.mp ((Nat.coprime_two_left.mpr on).of_dvd_right pn)
    have big:5≤p := by
      obtain ⟨j,hj⟩:=oddp
      obtain ⟨t,ht⟩:=ev
      have :=hp.two_le
      by_contra! small
      have h3:p=3:=by omega
      rw [h3] at nr;omega
    have unit:¬p∣b+3:=by
      intro d
      have d2:p∣2:=(Nat.dvd_add_left d).mp (by rwa [show 2+(b+3)=n by omega])
      have :=Nat.le_of_dvd (by decide : 0<2) d2;omega
    have loc:=local_square big ev bp unit q2
    rw [←exp] at loc
    exact quartic_local big pn nf bp ev (OMA.DoubleBernoulli284760.not_two_of_test hp big on pn loc) sq
  · obtain ⟨j,hj⟩:=on
    have cases:n=1∨n=3∨n=5:=by omega
    rcases cases with rfl|rfl|rfl
    · simp
    · norm_num [bernoulli_zero] at sq
    · norm_num [bernoulli_two] at sq

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

/-- Complete characterization for the original positive integer n. -/
theorem all_iff {n:ℕ} (pos:0<n) :
    n^4∣∑i∈Ico 1 n,i^(n-2) ↔ Odd n ∧ n^2∣(bernoulli (n-3)).num.natAbs := by
  rcases Nat.even_or_odd n with en|on
  · by_cases nt:n=2
    · subst n;decide
    have lo:4≤n:=by obtain ⟨j,hj⟩:=en;omega
    have ev:Even (n-2):=by obtain ⟨j,hj⟩:=en;exact ⟨j-1,by omega⟩
    have fail:=even_obstruction pos en (by omega : 0<n-2) ev
    rw [←OMA.PowerSumRegular284760.ico_range pos (by exact zero_pow (by omega : n-2≠0))] at fail
    constructor
    · intro d;exact False.elim (fail ((dvd_pow_self n (by decide : 4≠0)).trans d))
    · intro h;obtain ⟨u,hu⟩:=h.1;obtain ⟨t,ht⟩:=en;omega
  · simpa [on] using OMA.QuarticIff284760.original_iff on

end OMA.QuarticAll284760

namespace OMA.HalfResidue284760
open Finset Nat

private theorem pairs {R:Type*} [AddCommMonoid R] (f:ℕ→R) (h c:ℕ) (hc:c=1∨c=2) :
    (∑i∈range (2*h+1),f i)= f 0 + ∑i∈range h,(f (c*(i+1))+f (2*h+1-c*(i+1))) := by
  rw [sum_range_succ',add_comm _ (f 0),sum_add_distrib]
  congr 1
  rcases hc with rfl|rfl
  · simp only [one_mul]
    rw [show 2*h=h+h by omega,sum_range_add]
    congr 1
    rw [←sum_range_reflect (fun i=>f (h+i+1)) h]
    apply sum_congr rfl;intro i hi;have :=mem_range.mp hi
    congr 1;omega
  · have split (k:ℕ) : (∑i∈range (2*k),f (i+1))=
        (∑i∈range k,f (2*(i+1)))+(∑i∈range k,f (2*i+1)) := by
      induction k with
      | zero=>simp
      | succ k ih=>rw [show 2*(k+1)=2*k+1+1 by omega,sum_range_succ,sum_range_succ,ih,
          sum_range_succ (f:=fun i=>f (2*(i+1))),sum_range_succ (f:=fun i=>f (2*i+1))]
                   rw [show 2*(k+1)=2*k+1+1 by omega];ac_rfl
    rw [split]
    congr 1
    rw [←sum_range_reflect (fun i=>f (2*i+1)) h]
    apply sum_congr rfl;intro i hi;have :=mem_range.mp hi
    congr 1;omega

private theorem field_zero {p b:ℕ} (hp:p.Prime) (pos:0<b) (nd:¬p-1∣b) :
    (∑i∈range p,(i:ZMod p)^b)=0 := by
  let _ : Fact p.Prime:=⟨hp⟩
  let k:=b%(p-1)
  have small:k<p-1:=Nat.mod_lt _ (by have :=hp.two_le;omega)
  have nz:k≠0:= fun z => nd (Nat.dvd_of_mod_eq_zero z)
  let equiv : Fin p ≃ ZMod p :=
    ⟨fun i=>i.val,fun a=>⟨a.val,a.val_lt⟩,fun i=>Fin.ext (ZMod.val_natCast_of_lt i.isLt),
      fun a=>ZMod.natCast_zmod_val a⟩
  have id (x:ZMod p):x^b=x^k := by
    by_cases z:x=0
    · rw [z,zero_pow pos.ne',zero_pow nz]
    · nth_rw 1 [←Nat.mod_add_div b (p-1)]
      rw [pow_add,pow_mul,ZMod.pow_card_sub_one_eq_one z,one_pow,mul_one]
  rw [←Fin.sum_univ_eq_sum_range]
  change (∑i:Fin p,(equiv i)^b)=0
  simp_rw [id]
  rw [equiv.sum_comp (fun x:ZMod p=>x^k)]
  exact FiniteField.sum_pow_lt_card_sub_one (ZMod p) _ (by simpa using small)

private def half (h t:ℕ) := ∑i∈range h,(i+1)^t

private theorem even_half {p b h:ℕ} (hp:p.Prime) (big:7≤p) (ph:p=2*h+1)
    (ev:Even b) (bp:0<b) (nd:¬p-1∣b) : p∣half h b := by
  have pair := pairs (fun i:ℕ=>(i:ZMod p)^b) h 1 (Or.inl rfl)
  rw [←ph] at pair
  have rev (i:ℕ) (hi:i∈range h) : ((p-1*(i+1):ℕ):ZMod p)^b=((i+1:ℕ):ZMod p)^b := by
    have :=mem_range.mp hi
    rw [one_mul,Nat.cast_sub (by omega : i+1≤p),ZMod.natCast_self,zero_sub,ev.neg_pow]
  rw [sum_add_distrib,sum_congr rfl rev] at pair
  simp only [one_mul,Nat.cast_zero,zero_pow bp.ne',zero_add,
    field_zero hp bp nd] at pair
  have d:p∣2*half h b := (ZMod.natCast_eq_zero_iff _ _).mp (by
    simpa only [half,Nat.cast_mul,Nat.cast_add,Nat.cast_sum,Nat.cast_pow,Nat.cast_ofNat,two_mul] using pair.symm)
  exact (hp.dvd_mul.mp d).resolve_left (by intro h;have :=Nat.le_of_dvd (by decide : 0<2) h;omega)

private theorem expansion {p b h c:ℕ} (ph:p=2*h+1) (hc:c=1∨c=2) (ev:Even b)
    (van:p∣half h b) :
    (∑i∈range p,(i:ZMod (p^3))^(b+2))=
      2*(c:ZMod (p^3))^(b+2)*half h (b+2)-
      (b+2:ℕ)*(p:ZMod (p^3))*c^(b+1)*half h (b+1) := by
  let R:=ZMod (p^3)
  have cube:(p:R)^3=0:=by rw [←Nat.cast_pow];exact ZMod.natCast_self _
  have ep:Even (b+2):=ev.add (by decide)
  have eo:Odd (b+1):=by obtain ⟨j,hj⟩:=ev;exact ⟨j,by omega⟩
  let term (i t:ℕ):R:=((i+1:ℕ):R)^t
  have pair:=pairs (fun i:ℕ=>(i:R)^(b+2)) h c hc
  rw [←ph] at pair
  have form (i:ℕ) (hi:i∈range h) :
      ((c*(i+1):ℕ):R)^(b+2)+((p-c*(i+1):ℕ):R)^(b+2) =
      (2*(c:R)^(b+2))*term i (b+2)-((b+2:ℕ)*(p:R)*c^(b+1))*term i (b+1)+
      ((b+2).choose 2*(p:R)^2*c^b)*term i b := by
    have ih:=mem_range.mp hi
    have bound:c*(i+1)≤p:=by rcases hc with rfl|rfl <;> omega
    rw [Nat.cast_sub bound,sub_eq_neg_add,OMA.PowerSumRegular284760.quad _ _ cube,
      show b+2-1=b+1 by omega,show b+2-2=b by omega,ep.neg_pow,eo.neg_pow,ev.neg_pow]
    simp only [term,R,Nat.cast_mul,mul_pow];ring
  have sumTerm (t:ℕ) : (∑i∈range h,term i t)=(half h t:R) := by
    simp only [half,term,R,Nat.cast_sum,Nat.cast_pow]
  have v:(p:R)^2*(half h b:R)=0 := by
    obtain ⟨j,hj⟩:=van
    rw [hj,Nat.cast_mul,←mul_assoc,←pow_succ,cube,zero_mul]
  rw [sum_congr rfl form,Nat.cast_zero,zero_pow (by omega : b+2≠0),zero_add,sum_add_distrib,
    sum_sub_distrib,←mul_sum,←mul_sum,←mul_sum,sumTerm,sumTerm,sumTerm] at pair
  rw [pair];linear_combination ((b+2).choose 2:R)*c^b*v

/-- The half-interval auxiliary sum used in the irregular-prime tables must
vanish modulo p² for any prime divisor of an odd counterexample. -/
theorem half_test {n p:ℕ} (hp:p.Prime) (big:7≤p) (on:Odd n) (pn:p∣n)
    (bad:n^4∣∑i∈Ico 1 n,i^(n-2)) : p^2∣∑i∈range (p/2),(i+1)^(n-4) := by
  let b:=n-5
  have nn:=Nat.le_of_dvd on.pos pn
  have nf:n=b+5 := by dsimp [b];omega
  have bp:0<b:=by omega
  have ev:Even b:=by obtain ⟨j,hj⟩:=on;exact ⟨j-2,by omega⟩
  obtain ⟨h,ph⟩:=hp.odd_of_ne_two (by omega)
  have pair:p=2*h+1:=by omega
  have nd:=OMA.DoubleBernoulli284760.not_two hp (by omega) on pn bad
  have van:=even_half hp big pair ev bp nd
  have one:=expansion (c:=1) pair (Or.inl rfl) ev van
  have two:=expansion (c:=2) pair (Or.inr rfl) ev van
  have cube:=OMA.ThirdOrder284760.cube_test hp big on pn bad
  rw [show n-3=b+2 by omega] at cube
  have z:(∑i∈range p,(i:ZMod (p^3))^(b+2))=0 := by
    simpa only [Nat.cast_sum,Nat.cast_pow] using (ZMod.natCast_eq_zero_iff _ _).mpr cube
  rw [z] at one two
  simp only [Nat.cast_one,one_pow,mul_one] at one
  simp only [Nat.cast_ofNat] at two
  have d:p^3∣p*((b+2)*2^(b+1)*half h (b+1)) := (ZMod.natCast_eq_zero_iff _ _).mp (by
    push_cast
    rw [pow_succ (2:ZMod (p^3)) (b+1)] at two
    push_cast at one two
    linear_combination 2*(2:ZMod (p^3))^(b+1)*one - two)
  rw [show p^3=p*p^2 by ring] at d
  have dv:=Nat.dvd_of_mul_dvd_mul_left hp.pos d
  have evprime:¬p∣b+2:=by
    intro dx
    have three:p∣3:=(Nat.dvd_add_left dx).mp (by rwa [show 3+(b+2)=n by omega])
    have :=Nat.le_of_dvd (by decide : 0<3) three;omega
  have c2:p.Coprime 2:=hp.coprime_iff_not_dvd.mpr (by intro hh;have :=Nat.le_of_dvd (by decide : 0<2) hh;omega)
  have unit:=((hp.coprime_iff_not_dvd.mpr evprime).mul_right (c2.pow_right (b+1))).pow_left 2
  rw [show n-4=b+1 by omega,show p/2=h by omega]
  exact unit.dvd_of_dvd_mul_left dv

end OMA.HalfResidue284760

namespace OMA.IrregularHalfRow284760
open Finset Nat

/-- The two half-interval power sums for a single irregular-index row. -/
def halfRow (p e:ℕ) : ZMod (p^2) := ∑i∈range (p/2), ((i+1:ℕ):ZMod (p^2))^e

private theorem affine {p a:ℕ} (hp:p.Prime) (cp:a.Coprime p) (e j:ℕ) :
    (a:ZMod (p^2))^(e+(p-1)*j) =
    (a:ZMod (p^2))^e+j*((a:ZMod (p^2))^(e+(p-1))-(a:ZMod (p^2))^e) := by
  let R:=ZMod (p^2)
  have a1:0<a:=by by_contra! z;have :=Nat.eq_zero_of_le_zero z;subst a;simp [hp.ne_one] at cp
  have ferm:=Nat.ModEq.pow_totient cp
  rw [Nat.totient_prime hp] at ferm
  obtain ⟨t,ht⟩:=ferm.symm.dvd'
  have ax:0<a^(p-1):=pow_pos a1 _
  have id:a^(p-1)=1+p*t:=by omega
  have cast:(a:R)^(p-1)=1+(p:R)*t := by
    simpa only [R,Nat.cast_pow,Nat.cast_add,Nat.cast_one,Nat.cast_mul] using
      congrArg (fun x:ℕ=>(x:ZMod (p^2))) id
  have nil:((a:R)^(p-1)-1)^2=0 := by
    rw [cast,add_sub_cancel_left,mul_pow,←Nat.cast_pow,ZMod.natCast_self,zero_mul]
  have linear:=OMA.PowerSum284760.taylor (1:R) ((a:R)^(p-1)-1) nil j
  have step:((a:R)^(p-1))^j=1+j*((a:R)^(p-1)-1) := by simpa using linear
  rw [pow_add,pow_mul,step,pow_add];ring

/-- The compatible second digit is forced: if k=(n−3) mod (p−1), the two
half-row values at k−1 and k+p−2 satisfy this explicit relation modulo p². -/
theorem test {n p:ℕ} (hp:p.Prime) (big:7≤p) (on:Odd n) (pn:p∣n)
    (bad:n^4∣∑i∈Ico 1 n,i^(n-2)) :
    let k:=(n-3)%(p-1)
    halfRow p (k-1) + (k+3:ℕ)*(halfRow p (k-1+(p-1))-halfRow p (k-1))=0 := by
  let k:=(n-3)%(p-1)
  let y:=(n-3)/(p-1)
  have id:k+(p-1)*y=n-3:=Nat.mod_add_div _ _
  have nn:=Nat.le_of_dvd on.pos pn
  have nr:¬p-1∣n-3:=fun d=>OMA.PowerSum284760.local_obstruction on hp pn d
    ((pow_dvd_pow n (by decide : 2≤4)).trans bad)
  have kp:0<k:=Nat.pos_of_ne_zero (fun z=>nr (Nat.dvd_of_mod_eq_zero z))
  have nform:n=k+(p-1)*y+3:=by omega
  have cls:y≡k+3 [MOD p] := by
    apply (ZMod.natCast_eq_natCast_iff ..).mp
    have z: (n:ZMod p)=0:=(ZMod.natCast_eq_zero_iff _ _).mpr pn
    rw [nform,Nat.cast_add,Nat.cast_add,Nat.cast_mul,Nat.cast_sub hp.one_le,
      ZMod.natCast_self,Nat.cast_one,zero_sub,neg_one_mul,Nat.cast_ofNat] at z
    push_cast;linear_combination -z
  have index : n-4≡k-1+(p-1)*(k+3) [MOD (p-1)*p] := by
    rw [show n-4=k-1+(p-1)*y by omega]
    exact (cls.mul_left' (p-1)).add_left _
  have tot:(p^2).totient=(p-1)*p := by rw [Nat.totient_prime_pow_succ hp];simp [mul_comm]
  have term (i:ℕ) (hi:i∈range (p/2)) :
      ((i+1:ℕ):ZMod (p^2))^(n-4) = ((i+1:ℕ):ZMod (p^2))^(k-1) +
      (k+3:ℕ)*(((i+1:ℕ):ZMod (p^2))^(k-1+(p-1))-((i+1:ℕ):ZMod (p^2))^(k-1)) := by
    have bound:=mem_range.mp hi
    have cp:(i+1).Coprime p := (hp.coprime_iff_not_dvd.mpr (by
      intro z;have :=Nat.le_of_dvd (by omega : 0 < i+1) z;omega)).symm
    rw [←affine hp cp _ _]
    have reduce (z:ℕ) := Nat.pow_totient_mod (x:=i+1) (n:=p^2) (k:=z) (by nlinarith) (cp.pow_right 2)
    simp only [tot] at reduce
    have eq:(i+1)^(n-4)≡(i+1)^(k-1+(p-1)*(k+3)) [MOD p^2] := calc
      _ ≡ (i+1)^((n-4)%((p-1)*p)) [MOD p^2] := reduce _
      _ ≡ (i+1)^((k-1+(p-1)*(k+3))%((p-1)*p)) [MOD p^2] := by rw [show (n-4)%((p-1)*p)=_ from index]
      _ ≡ _ [MOD p^2] := (reduce _).symm
    simpa only [Nat.cast_pow] using (ZMod.natCast_eq_natCast_iff _ _ _).mpr eq
  have yes:=OMA.HalfResidue284760.half_test hp big on pn bad
  have z:(∑i∈range (p/2),((i+1:ℕ):ZMod (p^2))^(n-4))=0 := by
    simpa only [Nat.cast_sum,Nat.cast_pow] using (ZMod.natCast_eq_zero_iff _ _).mpr yes
  rw [sum_congr rfl term,sum_add_distrib,←mul_sum,sum_sub_distrib] at z
  exact z

end OMA.IrregularHalfRow284760

#print axioms OMA.QuarticAll284760.all_iff
#print axioms OMA.ThirdOrder284760.cube_test
#print axioms OMA.IrregularHalfRow284760.test
