import Mathlib

/-! Prime-factor descent for Meštrović's 2014 Conjectures 13 and 16. The argument uses an elementary finite-sum form of Kummer's congruences. -/

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

/-! The even half-exponent in Conjecture 16 of Meštrović, JIS 17 (2014). -/
namespace OMA.ConjectureSixteen
open Nat Finset OMA.CubicBernoulliLocal284759

theorem error {p n b:ℕ} [Fact p.Prime] (big:5≤p) (nn:0<n) (pn:p∣n)
    (even:Even b) (bp:0<b) (unit:¬p∣b+3) (good:¬p-1∣b) :
    ((∑i∈range n,(i:ℚ)^(b+2))/(n:ℚ)^3 - bernoulli (b+2)/(n:ℚ)^2)∈localRing p := by
  let S:=∑i∈range n,(i:ℚ)^(b+2)
  let F (i:ℕ):=bernoulli i*((b+3).choose i:ℚ)*(n:ℚ)^(b+3-i)/(n:ℚ)^3
  have nz : (n:ℚ)≠0:=by exact_mod_cast nn.ne'
  obtain ⟨u,nu⟩:=pn
  have np : (n:ℚ)=(p:ℚ)*u:=by exact_mod_cast nu
  have early:(∑i∈range b,F i)∈localRing p := by
    apply (localRing p).sum_mem
    intro i hi
    have ib:=mem_range.mp hi
    have form : F i=(p*bernoulli i)*u*((b+3).choose i:ℚ)*(n:ℚ)^(b-i-1) := by
      dsimp [F];conv_lhs => rw [show b+3-i=(b-i-1)+1+3 by omega,pow_add _ _ 3,pow_succ]
      field_simp;rw [np];ring
    rw [form]
    exact (localRing p).mul_mem ((localRing p).mul_mem ((localRing p).mul_mem
      (OMA.BernoulliScreen284760.p_bernoulli big i) (natCast_mem _ _)) (natCast_mem _ _))
      ((localRing p).pow_mem (natCast_mem _ _) _)
  have zeroIndex : F b∈localRing p := by
    have id:F b=bernoulli b*((b+3).choose b:ℚ):=by dsimp [F];rw [show b+3-b=3 by omega];field_simp
    rw [id];exact (localRing p).mul_mem (OMA.BernoulliScreen284760.bernoulli_integral bp even good) (natCast_mem _ _)
  have odd:Odd (b+1):=by obtain ⟨j,h⟩:=even;exact ⟨j,by omega⟩
  have penult:F (b+1)=0:=by simp [F,bernoulli_eq_zero_of_odd odd (by omega)]
  have final:F (b+2)=(b+3:ℚ)*bernoulli (b+2)/(n:ℚ)^2 := by
    dsimp only [F];rw [Nat.choose_succ_self_right,show b+3-(b+2)=1 by omega,pow_one]
    push_cast;field_simp;ring
  have faul:=sum_range_pow n (b+2)
  rw [←Finset.sum_div] at faul
  push_cast at faul
  have nonzero:(b+2+1:ℚ)≠0:=by positivity
  have all:(∑i∈range (b+3),F i)=(b+3:ℚ)*S/(n:ℚ)^3 := by
    dsimp only [F,S];rw [←Finset.sum_div]
    congr 1
    have v:=(eq_div_iff nonzero).mp faul
    linear_combination -v
  rw [Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_succ,penult,add_zero,final] at all
  have id : S/(n:ℚ)^3-bernoulli (b+2)/(n:ℚ)^2 =
      ((∑i∈range b,F i)+F b)*((b+3:ℕ):ℚ)⁻¹ := by
    push_cast
    field_simp [nz] at all ⊢
    linear_combination -all
  rw [id]
  exact (localRing p).mul_mem ((localRing p).add_mem early zeroIndex) (inverse_mem unit)

private theorem not_two {p b:ℕ} (pr:p.Prime) (odd:Odd p) (unit:¬p∣b+2)
    (sq:p^2∣∑i∈range p,i^(b+2)) : ¬p-1∣b := by
  have vanish:=OMA.DoubleBernoulli284760.weight_zero pr odd unit sq
  intro dv
  obtain ⟨q,hq⟩:=dv
  have ex:b+2-1=1+(p-1)*q:=by omega
  let _ : Fact p.Prime:=⟨pr⟩
  have same (a:ℕ) : ((a%p:ℕ):ZMod p)^(b+2-1)=((a%p:ℕ):ZMod p) := by
    by_cases z:((a%p:ℕ):ZMod p)=0
    · rw [z,zero_pow (by omega : b+2-1≠0)]
    · rw [ex,pow_add,pow_mul,ZMod.pow_card_sub_one_eq_one z,one_pow,pow_one,mul_one]
  have z1 : (∑i∈range p,((2*i/p:ℕ):ZMod p)*(((2*i)%p:ℕ):ZMod p)^(b+2-1))=0 := by
    simpa only [Nat.cast_sum,Nat.cast_mul,Nat.cast_pow] using (ZMod.natCast_eq_zero_iff _ _).mpr vanish
  simp_rw [same] at z1
  have dw : p∣∑i∈range p,(2*i/p)*((2*i)%p) := (ZMod.natCast_eq_zero_iff _ _).mp (by
    simpa only [Nat.cast_sum,Nat.cast_mul] using z1)
  obtain ⟨s,hs⟩:=odd
  rw [hs,OMA.DoubleBernoulli284760.weight] at dw
  have pb:(2*s+1).Prime:=hs ▸ pr
  have :=pr.two_le
  have small: 2*s+1 ≤ s := Nat.le_of_dvd (by omega) (pb.dvd_of_dvd_pow dw)
  omega

private theorem local_num {n d:ℕ} (nn:0<n) (dd:0<d) (x:ℚ) :
    n^d∣x.num.natAbs ↔ ∀p:ℕ,∀hp:p.Prime,p∣n → x/(n:ℚ)^d∈@localRing p ⟨hp⟩ := by
  rw [OMA.CubicBernoulliCriterion284759.denominator (pow_pos nn d)]
  push_cast
  constructor
  · intro h p hp pn
    let _ : Fact p.Prime:=⟨hp⟩
    apply Rat.padicValuation_le_one_iff.mpr
    exact hp.coprime_iff_not_dvd.mp (h.of_dvd_left (pn.trans (dvd_pow_self n dd.ne')))
  · intro h
    apply Nat.coprime_of_dvd
    intro p hp pn
    let _ : Fact p.Prime:=⟨hp⟩
    exact Rat.padicValuation_le_one_iff.mp (h p hp (hp.dvd_of_dvd_pow pn))

private theorem unit_succ {n b p:ℕ} (hp:p.Prime) (pn:p∣n) (form:n=2*(b+2)+1) :
    ¬p∣b+3 := by
  intro pd
  have dv:p∣n+1:=by rw [show n+1=2*(b+3) by omega];exact dvd_mul_of_dvd_right pd 2
  exact hp.not_dvd_one ((Nat.dvd_add_right pn).mp dv)

private theorem rows {n b:ℕ} (form:n=2*(b+2)+1) (ev:Even b) (bp:0<b)
    (num:n∣(bernoulli (b+2)).num.natAbs) {p:ℕ} (hp:p.Prime) (pn:p∣n) :
    5≤p ∧ ¬p-1∣b := by
  let _ : Fact p.Prime:=⟨hp⟩
  have nOdd : Odd n := ⟨b+2,by omega⟩
  have op:=Nat.coprime_two_left.mp ((Nat.coprime_two_left.mpr nOdd).of_dvd_right pn)
  have nr:=OMA.QuarticIff284760.not_regular_den (by omega : 0<b+2) (ev.add (by decide : Even 2)) (pn.trans num)
  have big:5≤p:=by
    have ht:=hp.two_le
    obtain ⟨s,t⟩:=op;obtain ⟨u,v⟩:=ev
    by_contra! h
    rw [show p=3 by omega] at nr;omega
  have small (q:ℕ) (hq:q.Prime) (dq:q∣p) : 3≤q := by
    obtain rfl:=(Nat.prime_dvd_prime_iff_eq hq hp).mp dq;omega
  have sq: p^2∣∑i∈range p,i^(b+2) :=
    (OMA.CubicBernoulliCriterion284759.even_iff hp.pos bp ev small
      (hp.coprime_iff_not_dvd.mpr (unit_succ hp pn form))).mpr (pn.trans num)
  have de:¬p∣b+2 := by
    intro de
    have dm:p∣2*(b+2) := dvd_mul_of_dvd_right de _
    exact hp.not_dvd_one ((Nat.dvd_add_right dm).mp (form ▸ pn))
  exact ⟨big,not_two hp op de sq⟩

private theorem iff_coarse {n b:ℕ} (form:n=2*(b+2)+1) (ev:Even b) (bp:0<b)
    (num:n∣(bernoulli (b+2)).num.natAbs) :
    n^3∣∑i∈range n,i^(b+2) ↔ n^2∣(bernoulli (b+2)).num.natAbs := by
  let S:=∑i∈range n,i^(b+2)
  change n^3∣S ↔ _
  rw [←show (S:ℚ).num.natAbs=S by simp,local_num (by omega) (by decide),local_num (by omega) (by decide)]
  have compare (p:ℕ) (hp:p.Prime) (pn:p∣n) :
      (S:ℚ)/(n:ℚ)^3∈@localRing p ⟨hp⟩ ↔ bernoulli (b+2)/(n:ℚ)^2∈@localRing p ⟨hp⟩ := by
    let _ : Fact p.Prime:=⟨hp⟩
    obtain ⟨large,good⟩:=rows form ev bp num hp pn
    have diff:(S:ℚ)/(n:ℚ)^3-bernoulli (b+2)/(n:ℚ)^2∈localRing p := by
      dsimp [S];push_cast;exact error large (by omega) pn ev bp (unit_succ hp pn form) good
    constructor
    · intro m
      simpa only [sub_sub_cancel] using (localRing p).sub_mem m diff
    · intro m
      simpa only [sub_add_cancel] using (localRing p).add_mem diff m
  exact ⟨fun h p hp pn=>(compare p hp pn).mp (h p hp pn),fun h p hp pn=>(compare p hp pn).mpr (h p hp pn)⟩

/-- Exact square-numerator characterization of the half-exponent cube. -/
theorem original {n:ℕ} (big:5≤n) (res:n%4=1) :
    n^3∣∑i∈Icc 1 (n-1),i^((n-1)/2) ↔ n^2∣(bernoulli ((n-1)/2)).num.natAbs := by
  by_cases five:n=5
  · subst n;norm_num [Finset.sum_Icc_succ_top,bernoulli_two]
  let b:=(n-1)/2-2
  have ex:(n-1)/2=b+2:=by dsimp [b];omega
  have form:n=2*(b+2)+1:=by omega
  have bp:0<b:=by omega
  have ev:Even b:=⟨n/4-1,by omega⟩
  have on:Odd n:=⟨b+2,by omega⟩
  have small (p:ℕ) (hp:p.Prime) (pn:p∣n) : 3≤p:=by
    have po:=Nat.coprime_two_left.mp ((Nat.coprime_two_left.mpr on).of_dvd_right pn)
    obtain ⟨k,hk⟩:=po;have :=hp.two_le;omega
  have cop:n.Coprime (b+3):=Nat.coprime_of_dvd fun p hp pn=>unit_succ hp pn form
  have idx:Icc 1 (n-1)=Ico 1 n:=by ext x;simp;omega
  have sums:=sum_range_add_sum_Ico (fun i:ℕ=>i^(b+2)) on.pos
  have same : (∑i∈Ico 1 n,i^(b+2))=∑i∈range n,i^(b+2):=by simpa using sums
  rw [ex,idx,same]
  constructor
  · intro h
    have d2: n^2∣∑i∈range n,i^(b+2) := (pow_dvd_pow n (by decide : 2≤3)).trans h
    exact (iff_coarse form ev bp ((OMA.CubicBernoulliCriterion284759.even_iff on.pos bp ev small cop).mp d2)).mp h
  · intro h
    exact (iff_coarse form ev bp ((dvd_pow_self n (by decide : 2≠0)).trans h)).mpr h


end OMA.ConjectureSixteen

/-! Change the exponent of a complete power sum modulo p². Multiplication
by g permutes residues; its first-order carry determines every exponent
in one class modulo p−1 from one small-index row. -/
namespace OMA.PowerSumIndexTransfer284759
open Finset Nat

private theorem permute {p g v : ℕ} (pos : 0<p) (inverse : g*v ≡ 1 [MOD p])
    {R : Type*} [AddCommMonoid R] (f : ℕ → R) :
    (∑i∈range p, f ((g*i)%p))=∑i∈range p, f i := by
  have cancel {a b i : ℕ} (one : a*b ≡ 1 [MOD p]) (ip : i<p) :
      a*((b*i)%p)%p=i := by
    rw [Nat.mul_mod_mod,←Nat.mul_assoc]
    simpa only [Nat.ModEq,one_mul,Nat.mod_eq_of_lt ip] using one.mul_right i
  apply sum_bij' (fun i _ => g*i%p) (fun i _ => v*i%p)
  · intro i _;exact mem_range.mpr (mod_lt _ pos)
  · intro i _;exact mem_range.mpr (mod_lt _ pos)
  · intro i hi;exact cancel (by simpa [mul_comm] using inverse) (mem_range.mp hi)
  · intro i hi;exact cancel inverse (mem_range.mp hi)
  · intro _ _;rfl

private def cs (p g e : ℕ) : ZMod (p^2) :=
  ∑i∈range p, (((g*i)%p:ℕ):ZMod (p^2))^(e-1) * (p:ZMod (p^2)) * ((g*i)/p:ℕ)

private theorem voronoi {p g v e : ℕ} (pos : 0<p) (inverse : g*v ≡ 1 [MOD p]) :
    ((g:ZMod (p^2))^e-1)*(∑i∈range p,(i:ZMod (p^2))^e)=(e:ZMod (p^2))*cs p g e := by
  let R:=ZMod (p^2)
  have nil : (p:R)^2=0 := by
    rw [←Nat.cast_pow];exact ZMod.natCast_self _
  have line (i:ℕ) : ((g:R)*i)^e=(((g*i)%p:ℕ):R)^e +
      (e:R)*((((g*i)%p:ℕ):R)^(e-1)*(p:R)*((g*i)/p:ℕ)) := by
    have h : (g:R)*i=(((g*i)%p:ℕ):R)+(p:R)*((g*i)/p:ℕ) := by
      rw [←Nat.cast_mul g i,←Nat.cast_mul p ((g*i)/p),←Nat.cast_add,Nat.mod_add_div]
    rw [h,OMA.PowerSum284760.taylor _ _ (by rw [mul_pow,nil,zero_mul])];ring
  have all := Finset.sum_congr (s₁:=range p) rfl (fun i _=>line i)
  simp only [mul_pow,←mul_sum,sum_add_distrib] at all
  rw [permute pos inverse (fun i=>(i:R)^e)] at all
  change ((g:R)^e-1)*_=_*(∑i∈range p,_)
  linear_combination all

private theorem same_times_p {a b p : ℕ} (eqn : (a:ZMod p)=b) :
    (a:ZMod (p^2))*p=(b:ZMod (p^2))*p := by
  rw [←Nat.cast_mul,←Nat.cast_mul,ZMod.natCast_eq_natCast_iff,pow_two]
  exact ((ZMod.natCast_eq_natCast_iff ..).mp eqn).mul_right' p


end OMA.PowerSumIndexTransfer284759

/-! Elementary transfer of Bernoulli numerator zeros modulo prime powers,
via a permutation of residues modulo p^a and a first-order carry modulo p^(2a). -/
namespace OMA.PrimePowerMestrovic
open Nat Finset

private theorem transfer_sum {p a e t:ℕ} (hp:p.Prime) (ha:0<a) (he:a<e) (ht:a<t)
    (cong:e≡t [MOD (p^a).totient]) (pe:¬p∣e) (no:¬p-1∣t)
    (z:p^(2*a)∣∑i∈range (p^a),i^e) : p^(2*a)∣∑i∈range (p^a),i^t := by
  let _ : Fact p.Prime:=⟨hp⟩
  let m:=p^a
  let R:=ZMod (m^2)
  have mp : 1 < m := one_lt_pow₀ hp.one_lt ha.ne'
  have power:m^2=p^(2*a):=by dsimp [m];rw [←pow_mul,mul_comm]
  obtain ⟨w,hw⟩:=isCyclic_iff_exists_orderOf_eq_natCard.mp (inferInstance : IsCyclic (ZMod p)ˣ)
  let g:ℕ:=(w:ZMod p).val
  have gv:(g:ZMod p)=w:=ZMod.natCast_zmod_val _
  have pg:¬p∣g:=by rw [←ZMod.natCast_eq_zero_iff,gv];exact Units.ne_zero _
  have cp:g.Coprime m:=(hp.coprime_iff_not_dvd.mpr pg).symm.pow_right _
  obtain ⟨v,_,hv⟩:=Nat.exists_mul_mod_eq_one_of_coprime cp mp
  have inv:g*v≡1 [MOD m]:=by change _=_;rwa [mod_eq_of_lt mp]
  have sep:(g:ZMod p)^t≠1:=by
    rw [gv];intro eq
    have d:=orderOf_dvd_of_pow_eq_one eq
    rw [orderOf_units,hw,Nat.card_eq_fintype_card,ZMod.card_units_eq_totient,Nat.totient_prime hp] at d
    exact no d
  have unit_of {y:R} (out:ZMod.castHom (show p∣m^2 by rw [power];exact dvd_pow_self _ (by omega)) (ZMod p) y≠0) : IsUnit y:=by
    have nd:¬p∣y.val:=by
      intro d;apply out;rw [←ZMod.natCast_zmod_val y,map_natCast,ZMod.natCast_eq_zero_iff];exact d
    have cast (x:ℕ) (h:¬p∣x) : IsUnit (x:R):=by
      unfold R;rw [power];exact (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by omega)).mpr h
    have yy:((y.val:ℕ):R)=y:=ZMod.natCast_zmod_val y
    rw [←yy];exact cast y.val nd
  have eu:IsUnit (e:R):=unit_of (by rw [map_natCast];exact fun z=>pe ((ZMod.natCast_eq_zero_iff e p).mp z))
  have tu:IsUnit ((g:R)^t-1):=unit_of (by rw [map_sub,map_pow,map_one,map_natCast];exact sub_ne_zero.mpr sep)
  have zz:(∑i∈range m,(i:R)^e)=0:=by
    have d:m^2∣∑i∈range m,i^e:=power.symm ▸ z
    simpa only [Nat.cast_pow,Nat.cast_sum] using (ZMod.natCast_eq_zero_iff (∑i∈range m,i^e) (m^2)).mpr d
  have eq:OMA.PowerSumIndexTransfer284759.cs m g e = OMA.PowerSumIndexTransfer284759.cs m g t := by
    unfold OMA.PowerSumIndexTransfer284759.cs
    apply sum_congr rfl;intro i _
    apply congrArg (·*(((g*i)/m:ℕ):R))
    let x:=g*i%m
    change (x:R)^(e-1)*m=(x:R)^(t-1)*m
    rw [←Nat.cast_pow,←Nat.cast_pow]
    apply OMA.PowerSumIndexTransfer284759.same_times_p
    apply (ZMod.natCast_eq_natCast_iff ..).mpr
    by_cases dx:p∣x
    · have zero (k:ℕ) (hk:a≤k):m∣x^k:=(pow_dvd_pow_of_dvd dx a).trans (pow_dvd_pow x hk)
      change _%m=_%m
      rw [mod_eq_zero_of_dvd (zero _ (by omega)),mod_eq_zero_of_dvd (zero _ (by omega))]
    · have u:x.Coprime m:=(hp.coprime_iff_not_dvd.mpr dx).symm.pow_right _
      have ce:e-1≡t-1 [MOD m.totient]:=Nat.ModEq.sub_right (by omega) (by omega) cong
      exact (Nat.pow_totient_mod (k:=e-1) (by omega) u).trans
        (by rw [show (e-1)%m.totient=(t-1)%m.totient from ce];exact (Nat.pow_totient_mod (k:=t-1) (by omega) u).symm)
  have s1:=OMA.PowerSumIndexTransfer284759.voronoi (e:=e) (by omega : 0 < m) inv
  have c0:OMA.PowerSumIndexTransfer284759.cs m g t=0:=by
    rw [←eq];apply eu.mul_right_inj.mp;simpa [zz] using s1.symm
  have s2:=OMA.PowerSumIndexTransfer284759.voronoi (e:=t) (by omega : 0 < m) inv
  have s0:(∑i∈range m,(i:R)^t)=0:=tu.mul_right_inj.mp (by simpa [c0] using s2)
  rw [←power];apply (ZMod.natCast_eq_zero_iff _ _).mp;push_cast;exact s0

/-- Change the index of a Bernoulli numerator zero modulo p^a. This
special case of Kummer's congruences preserves arbitrary prime multiplicity. -/
theorem transfer {p a e t:ℕ} (hp:p.Prime) (large:3≤p) (ha:0<a)
    (ep:2<e) (tp:2<t) (he:a<e) (ht:a<t) (ee:Even e) (te:Even t)
    (pe:¬p∣e) (se:¬p∣e+1) (st:¬p∣t+1) (no:¬p-1∣t)
    (cong:e≡t [MOD (p^a).totient]) (num:p^a∣(bernoulli e).num.natAbs) :
    p^a∣(bernoulli t).num.natAbs := by
  have mean (j:ℕ) (jp:2<j) (je:Even j) (unit:¬p∣j+1):
      (p^a)^2∣∑i∈range (p^a),i^j ↔ p^a∣(bernoulli j).num.natAbs:=by
    let b:=j-2
    have bj:b+2=j:=by dsimp [b];omega
    have be:Even b:=by obtain ⟨i,hi⟩:=je;exact ⟨i-1,by omega⟩
    have cop:(p^a).Coprime (b+3):=(hp.coprime_iff_not_dvd.mpr (by rwa [show b+3=j+1 by omega])).pow_left _
    rw [←bj]
    exact OMA.CubicBernoulliCriterion284759.even_iff (pow_pos hp.pos _) (by omega) be
      (fun q hq d=>(Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow d) ▸ large) cop
  apply (mean t tp te st).mp
  have d:=(mean e ep ee se).mpr num
  rw [←pow_mul,mul_comm a 2] at d ⊢
  exact transfer_sum hp ha he ht cong pe no d


private theorem crt {p x y:ℕ} (hp:p.Prime) (h:x≡y [MOD p]) (g:x≡y [MOD p-1]) :
    x≡y [MOD (p^2).totient] := by
  rw [Nat.totient_prime_pow_succ hp,pow_one]
  exact (Nat.modEq_and_modEq_iff_modEq_mul ((Nat.coprime_self_sub_right hp.one_le).mpr (by simp))).mp ⟨h,g⟩

/-- A Korselt divisor (p|n with p−1|n−1) of any quartic counterexample
is itself a prime counterexample. This does not require squarefreeness. -/
theorem quartic_descent {n p:ℕ} (nn:1<n) (hp:p.Prime) (pn:p∣n) (korselt:p-1∣n-1)
    (bad:n^4∣∑i∈Ico 1 n,i^(n-2)) : p^4∣∑i∈Ico 1 p,i^(p-2) := by
  let _ : Fact p.Prime:=⟨hp⟩
  obtain ⟨on,num⟩:=(OMA.QuarticAll284760.all_iff (by omega)).mp bad
  have np:=Nat.le_of_dvd on.pos pn
  by_cases ns:7≤n
  · have oe:Even (n-3):=by obtain ⟨j,h⟩:=on;exact ⟨j-1,by omega⟩
    have sq:p^2∣(bernoulli (n-3)).num.natAbs:=(pow_dvd_pow_of_dvd pn 2).trans num
    have nr:=OMA.QuarticIff284760.not_regular_den (by omega : 0<n-3) oe
      ((dvd_pow_self p (by decide : 2≠0)).trans sq)
    have po:=Nat.coprime_two_left.mp ((Nat.coprime_two_left.mpr on).of_dvd_right pn)
    have large:7≤p:=by
      have :=hp.two_le
      have ⟨i,h⟩:=po;have ⟨j,g⟩:=on
      by_contra! small
      rcases (show p=3∨p=5 by omega) with h3|h5
      · rw [h3] at nr;omega
      · have not2:=OMA.DoubleBernoulli284760.not_two hp (by omega) on pn bad
        rw [h5] at not2 korselt
        omega
    have pt:Even (p-3):=by obtain ⟨j,h⟩:=po;exact ⟨j-1,by omega⟩
    have np0:n≡p [MOD p]:=(Nat.modEq_zero_iff_dvd.mpr pn).trans (Nat.modEq_zero_iff_dvd.mpr (dvd_refl p)).symm
    have np1:n≡p [MOD p-1]:=by
      have j: n-1≡p-1 [MOD p-1]:=(Nat.modEq_zero_iff_dvd.mpr korselt).trans
        (Nat.modEq_zero_iff_dvd.mpr (dvd_refl (p-1))).symm
      simpa only [Nat.sub_add_cancel (by omega : 1≤n),Nat.sub_add_cancel hp.one_le] using j.add_right 1
    have diff (k:ℕ) (hk:0<k) (small:k<p) : ¬p∣n-k:=by
      intro dv
      have d:p∣k:=(Nat.dvd_add_left dv).mp (by rwa [Nat.add_sub_of_le (by omega : k≤n)])
      exact (not_le.mpr small) (Nat.le_of_dvd hk d)
    apply (OMA.QuarticAll284760.all_iff hp.pos).mpr
    refine ⟨po,transfer hp (by omega) (by decide : 0<2) (by omega) (by omega) (by omega) (by omega)
      oe pt (diff 3 (by decide) (by omega)) ?_ ?_ ?_ ?_ sq⟩
    · rw [show n-3+1=n-2 by omega];exact diff 2 (by decide) (by omega)
    · intro d;have :=Nat.le_of_dvd (by omega : 0<p-3+1) d;omega
    · intro d;have :=Nat.le_of_dvd (by omega : 0<p-3) d;omega
    · exact Nat.ModEq.sub_right (by omega) (by omega) (crt hp np0 np1)
  · exfalso;revert bad;interval_cases n <;> decide +kernel

/-- The half-exponent conjecture has the same descent property; the prime
automatically lies in the residue class 1 mod 4 required in its statement. -/
theorem half_descent {n p:ℕ} (nn:5≤n) (nr:n%4=1) (hp:p.Prime) (pn:p∣n)
    (korselt:p-1∣n-1) (bad:n^3∣∑i∈Icc 1 (n-1),i^((n-1)/2)) :
    p%4=1 ∧ p^3∣∑i∈Icc 1 (p-1),i^((p-1)/2) := by
  let _ : Fact p.Prime:=⟨hp⟩
  have num:=(OMA.ConjectureSixteen.original nn nr).mp bad
  by_cases ns:9≤n
  · let e:=(n-1)/2
    let t:=(p-1)/2
    let b:=e-2
    have nf:n=2*e+1:=by dsimp [e];omega
    have en:Even e:=⟨n/4,by dsimp [e];omega⟩
    have eb:b+2=e:=by dsimp [b,e];omega
    have bp:0<b:=by dsimp [b,e];omega
    have bv:Even b:=⟨n/4-1,by dsimp [b,e];omega⟩
    have sq:p^2∣(bernoulli e).num.natAbs:=(pow_dvd_pow_of_dvd pn 2).trans num
    have re:=OMA.QuarticIff284760.not_regular_den (by omega : 0<e) en ((dvd_pow_self p (by decide : 2≠0)).trans sq)
    have rows:=OMA.ConjectureSixteen.rows (n:=n) (b:=b) (by omega) bv bp
      (eb ▸ ((dvd_pow_self n (by decide : 2≠0)).trans num)) hp pn
    have op:=hp.odd_of_ne_two (by omega)
    have pf:p=2*t+1:=by obtain ⟨j,h⟩:=op;dsimp [t];omega
    obtain ⟨k,hk⟩:=korselt
    have ek:e=t*k:=by
      rw [show n-1=2*e by omega,show p-1=2*t by omega,mul_assoc] at hk;omega
    have ko:Odd k:=by
      rcases Nat.even_or_odd k with even|odd
      · exfalso;apply re
        obtain ⟨q,hq⟩:=even
        refine ⟨q,?_⟩;rw [ek,show p-1=2*t by omega,hq];ring
      · exact odd
    have te:Even t:=by
      rw [ek,Nat.even_mul] at en
      exact en.resolve_right (Nat.not_even_iff_odd.mpr ko)
    have pr:p%4=1:=by obtain ⟨j,h⟩:=te;omega
    have pg:7≤p:=by
      by_contra! small
      have p5:p=5:=by omega
      rw [p5] at rows re
      obtain ⟨j,h⟩:=bv
      omega
    have ce:e≡t [MOD p]:=by
      apply Nat.ModEq.cancel_left_of_coprime (Nat.coprime_two_right.mpr op)
      apply Nat.ModEq.add_right_cancel' 1
      simpa only [←nf,←pf] using (Nat.modEq_zero_iff_dvd.mpr pn).trans (Nat.modEq_zero_iff_dvd.mpr (dvd_refl p)).symm
    have ct:e≡t [MOD p-1]:=by
      obtain ⟨j,h⟩:=ko
      rw [ek,h,show t*(2*j+1)=(p-1)*j+t by rw [show p-1=2*t by omega];ring]
      exact Nat.modulus_mul_add_modEq_iff.mpr .rfl
    have ne:¬p∣e:=by
      intro d
      exact hp.not_dvd_one ((Nat.dvd_add_right (dvd_mul_of_dvd_right d 2)).mp (nf ▸ pn))
    have sn:¬p∣e+1:=by
      intro d
      have v:p∣n+1:=by rw [show n+1=2*(e+1) by omega];exact dvd_mul_of_dvd_right d 2
      exact hp.not_dvd_one ((Nat.dvd_add_right pn).mp v)
    refine ⟨pr,(OMA.ConjectureSixteen.original (by omega) pr).mpr ?_⟩
    change p^2∣(bernoulli t).num.natAbs
    exact transfer hp (by omega) (by decide) (by omega) (by omega) (by omega) (by omega) en te ne sn
      (by intro d;have :=Nat.le_of_dvd (by omega : 0<t+1) d;omega)
      (by intro d;have :=Nat.le_of_dvd (by omega : 0<t) d;omega) (crt hp ce ct) sq
  · have n5:n=5:=by omega
    subst n;exact False.elim ((by decide +kernel : ¬5^3∣∑i∈Icc 1 (5-1),i^((5-1)/2)) bad)

#print axioms transfer
#print axioms quartic_descent
#print axioms half_descent

theorem quartic_prime_power {p a:ℕ} (hp:p.Prime) (ha:0<a)
    (bad:(p^a)^4∣∑i∈Ico 1 (p^a),i^(p^a-2)) :
    p^4∣∑i∈Ico 1 p,i^(p-2) :=
  quartic_descent (one_lt_pow₀ hp.one_lt ha.ne') hp (dvd_pow_self _ ha.ne') (Nat.sub_one_dvd_pow_sub_one ..) bad

theorem half_prime_power {p a:ℕ} (hp:p.Prime) (ha:0<a) (big:5≤p^a) (res:p^a%4=1)
    (bad:(p^a)^3∣∑i∈Icc 1 (p^a-1),i^((p^a-1)/2)) :
    p%4=1 ∧ p^3∣∑i∈Icc 1 (p-1),i^((p-1)/2) :=
  half_descent big res hp (dvd_pow_self _ ha.ne') (Nat.sub_one_dvd_pow_sub_one ..) bad

#print axioms quartic_prime_power
#print axioms half_prime_power
end OMA.PrimePowerMestrovic
