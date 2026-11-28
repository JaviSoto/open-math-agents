import Mathlib

/-! Both parts of Meštrović's Conjecture 11, JIS 17 (2014), Article 14.8.4, fail at the same composite input. -/

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


end OMA.BernoulliScreen284760

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

namespace OMA.CubicBridge284759
open Nat Finset

private theorem lift {n p e:ℕ} (pn:p∣n) (op:Odd p) (prev:Odd (e-1))
    (localSum:(∑i∈range p,(i:ZMod (p^2))^e)=0) : p^2∣∑i∈range n,i^e := by
  obtain ⟨m,rfl⟩:=pn
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  rw [Nat.cast_sum]
  simp only [Nat.cast_pow]
  rw [OMA.PowerSumRegular284760.first_block op prev,localSum,mul_zero]

private theorem omit_zero {m e n:ℕ} (nn:0<n) (ep:0<e)
    (h:m∣∑i∈range n,i^e) : m∣∑i∈Ico 1 n,i^e := by
  rwa [OMA.PowerSumRegular284760.ico_range nn (by exact zero_pow ep.ne')]

/-- The three complete even-power rows imply the original cubic congruence:
lift each row in blocks, combine by coprimality, then reflect the odd sum. -/
theorem witness
    (first:(∑i∈range 59,(i:ZMod (59^2))^409407428)=0)
    (second:(∑i∈range 1559,(i:ZMod (1559^2))^409407428)=0)
    (third:(∑i∈range 4451,(i:ZMod (4451^2))^409407428)=0) :
    409407431^3∣∑i∈Icc 1 (409407431-1),i^(409407431-2) := by
  let n : ℕ := 409407431
  have nn:0<n:=by decide
  have no:Odd n:=by decide
  have rem₁:=lift (n:=n) (by decide : 59∣n) (by decide) (by decide) first
  have rem₂:=lift (n:=n) (by decide : 1559∣n) (by decide) (by decide) second
  have rem₃:=lift (n:=n) (by decide : 4451∣n) (by decide) (by decide) third
  have cq : (59^2*1559^2).Coprime (4451^2):=by decide
  have cp : (59^2).Coprime (1559^2):=by decide
  have sq:n^2∣∑i∈range n,i^409407428 := by
    rw [show n^2=59^2*1559^2*4451^2 by decide]
    exact cq.mul_dvd_of_dvd_of_dvd (cp.mul_dvd_of_dvd_of_dvd rem₁ rem₂) rem₃
  have sqI:=omit_zero nn (by decide : 0<409407428) sq
  have cube:n^3∣n*(∑i∈Ico 1 n,i^409407428) := by
    rw [pow_succ'];exact Nat.mul_dvd_mul_left _ sqI
  have zero : (n:ZMod (n^3))*(∑i∈Ico 1 n,(i:ZMod (n^3))^409407428)=0 := by
    simpa only [Nat.cast_mul,Nat.cast_sum,Nat.cast_pow] using (ZMod.natCast_eq_zero_iff _ _).mpr cube
  have ref:=OMA.PowerSumRegular284760.reflect3 (e:=409407429) no (by decide) (by decide)
  have result : 2*(∑i∈Ico 1 n,(i:ZMod (n^3))^409407429)=0 := by
    rw [ref,show 409407429-1=409407428 by decide,mul_right_comm,zero,zero_mul]
  have two:n^3∣2*(∑i∈Ico 1 n,i^409407429) :=
    (ZMod.natCast_eq_zero_iff _ _).mp (by push_cast;exact result)
  have endpts : Icc 1 (409407431-1)=Ico 1 n := by ext x; simp [n];omega
  rw [endpts]
  exact ((Nat.coprime_two_right.mpr no).pow_left 3).dvd_of_dvd_mul_left two

end OMA.CubicBridge284759

/-! Arithmetic witness for the even complete power sums in the cubic
conjecture. The exponent in hexadecimal is 18670fc4. -/
namespace OMA.CubicCertificate284759
open Finset

private def step (m x a b:ℕ) : ℕ := (a^16 * x^b) % m

private def value (m x:ℕ) : ℕ :=
  let a := x
  let b := step m x a 8
  let c := step m x b 6
  let d := step m x c 7
  let e := step m x d 0
  let f := step m x e 15
  let g := step m x f 12
  step m x g 4

private theorem step_cast (m x a b t:ℕ) (h:(a:ZMod m)=(x:ZMod m)^t) :
    (step m x a b:ZMod m)=(x:ZMod m)^(t*16+b) := by
  simp only [step,ZMod.natCast_mod,Nat.cast_mul,Nat.cast_pow,pow_add,pow_mul,h]

private theorem value_cast (m x:ℕ) : (value m x:ZMod m)=(x:ZMod m)^409407428 := by
  unfold value
  apply step_cast _ _ _ 4 25587964
  apply step_cast _ _ _ 12 1599247
  apply step_cast _ _ _ 15 99952
  apply step_cast _ _ _ 0 6247
  apply step_cast _ _ _ 7 390
  apply step_cast _ _ _ 6 24
  apply step_cast _ _ _ 8 1
  simp

private def batch (m a:ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => batch m a n + value m (a+n)

private theorem batch_cast (m a n:ℕ) :
    (batch m a n:ZMod m) = ∑i∈range n, ((a+i:ℕ):ZMod m)^409407428 := by
  induction n with
  | zero=>simp [batch]
  | succ n ih=>rw [batch,Nat.cast_add,ih,value_cast,sum_range_succ]

def tree (m:ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0,a,n => batch m a n % m
  | f+1,a,n =>
      (tree m f a (n/2) + tree m f (a+n/2) (n-n/2)) % m

private theorem tree_cast (m f a n:ℕ) :
    (tree m f a n:ZMod m) = ∑i∈range n, ((a+i:ℕ):ZMod m)^409407428 := by
  induction f generalizing a n with
  | zero => simp only [tree,ZMod.natCast_mod,batch_cast]
  | succ f ih =>
    rw [tree,ZMod.natCast_mod,Nat.cast_add,ih,ih]
    conv_rhs => arg 1;rw [show n=n/2+(n-n/2) by omega]
    rw [sum_range_add]
    simp only [add_assoc]

theorem finish {p f:ℕ} (check:tree (p^2) f 0 p=0) :
    (∑i∈range p,(i:ZMod (p^2))^409407428)=0 := by
  simpa only [tree_cast,zero_add,Nat.cast_zero] using congrArg (fun t:ℕ=>(t:ZMod (p^2))) check

end OMA.CubicCertificate284759

namespace OMA.CubicRows284759
open Finset OMA.CubicCertificate284759

set_option maxRecDepth 8192 in
private theorem r59_0_0 : tree 3481 0 0 59=0 := by decide +kernel

theorem row59 : (∑i∈range 59,(i:ZMod (59^2))^409407428)=0 := finish r59_0_0

set_option maxRecDepth 8192 in
private theorem r1559_0_0 : tree 2430481 0 0 389=1089229 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem r1559_0_389 : tree 2430481 0 389 390=1794150 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem r1559_1_0 : tree 2430481 1 0 779=452898 := by rw [tree,r1559_0_0,r1559_0_389]

set_option maxRecDepth 8192 in
private theorem r1559_0_779 : tree 2430481 0 779 390=940282 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem r1559_0_1169 : tree 2430481 0 1169 390=1037301 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem r1559_1_779 : tree 2430481 1 779 780=1977583 := by rw [tree,r1559_0_779,r1559_0_1169]

set_option maxRecDepth 8192 in
private theorem r1559_2_0 : tree 2430481 2 0 1559=0 := by rw [tree,r1559_1_0,r1559_1_779]

theorem row1559 : (∑i∈range 1559,(i:ZMod (1559^2))^409407428)=0 := finish r1559_2_0

set_option maxRecDepth 8192 in
private theorem r4451_0_0 : tree 19811401 0 0 278=13569437 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem r4451_0_278 : tree 19811401 0 278 278=8576304 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem r4451_1_0 : tree 19811401 1 0 556=2334340 := by rw [tree,r4451_0_0,r4451_0_278]

set_option maxRecDepth 8192 in
private theorem r4451_0_556 : tree 19811401 0 556 278=1501239 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem r4451_0_834 : tree 19811401 0 834 278=8091446 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem r4451_1_556 : tree 19811401 1 556 556=9592685 := by rw [tree,r4451_0_556,r4451_0_834]

set_option maxRecDepth 8192 in
private theorem r4451_2_0 : tree 19811401 2 0 1112=11927025 := by rw [tree,r4451_1_0,r4451_1_556]

set_option maxRecDepth 8192 in
private theorem r4451_0_1112 : tree 19811401 0 1112 278=16427160 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem r4451_0_1390 : tree 19811401 0 1390 278=1979117 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem r4451_1_1112 : tree 19811401 1 1112 556=18406277 := by rw [tree,r4451_0_1112,r4451_0_1390]

set_option maxRecDepth 8192 in
private theorem r4451_0_1668 : tree 19811401 0 1668 278=11573378 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem r4451_0_1946 : tree 19811401 0 1946 279=7204327 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem r4451_1_1668 : tree 19811401 1 1668 557=18777705 := by rw [tree,r4451_0_1668,r4451_0_1946]

set_option maxRecDepth 8192 in
private theorem r4451_2_1112 : tree 19811401 2 1112 1113=17372581 := by rw [tree,r4451_1_1112,r4451_1_1668]

set_option maxRecDepth 8192 in
private theorem r4451_3_0 : tree 19811401 3 0 2225=9488205 := by rw [tree,r4451_2_0,r4451_2_1112]

set_option maxRecDepth 8192 in
private theorem r4451_0_2225 : tree 19811401 0 2225 278=14813253 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem r4451_0_2503 : tree 19811401 0 2503 278=1184437 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem r4451_1_2225 : tree 19811401 1 2225 556=15997690 := by rw [tree,r4451_0_2225,r4451_0_2503]

set_option maxRecDepth 8192 in
private theorem r4451_0_2781 : tree 19811401 0 2781 278=11590021 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem r4451_0_3059 : tree 19811401 0 3059 279=8721160 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem r4451_1_2781 : tree 19811401 1 2781 557=499780 := by rw [tree,r4451_0_2781,r4451_0_3059]

set_option maxRecDepth 8192 in
private theorem r4451_2_2225 : tree 19811401 2 2225 1113=16497470 := by rw [tree,r4451_1_2225,r4451_1_2781]

set_option maxRecDepth 8192 in
private theorem r4451_0_3338 : tree 19811401 0 3338 278=19636521 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem r4451_0_3616 : tree 19811401 0 3616 278=18643185 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem r4451_1_3338 : tree 19811401 1 3338 556=18468305 := by rw [tree,r4451_0_3338,r4451_0_3616]

set_option maxRecDepth 8192 in
private theorem r4451_0_3894 : tree 19811401 0 3894 278=14008953 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem r4451_0_4172 : tree 19811401 0 4172 279=971270 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem r4451_1_3894 : tree 19811401 1 3894 557=14980223 := by rw [tree,r4451_0_3894,r4451_0_4172]

set_option maxRecDepth 8192 in
private theorem r4451_2_3338 : tree 19811401 2 3338 1113=13637127 := by rw [tree,r4451_1_3338,r4451_1_3894]

set_option maxRecDepth 8192 in
private theorem r4451_3_2225 : tree 19811401 3 2225 2226=10323196 := by rw [tree,r4451_2_2225,r4451_2_3338]

set_option maxRecDepth 8192 in
private theorem r4451_4_0 : tree 19811401 4 0 4451=0 := by rw [tree,r4451_3_0,r4451_3_2225]

theorem row4451 : (∑i∈range 4451,(i:ZMod (4451^2))^409407428)=0 := finish r4451_4_0

end OMA.CubicRows284759

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

private theorem factors {p:ℕ} (hp:p.Prime) (dv:p∣409407431) : p=59 ∨ p=1559 ∨ p=4451 := by
  rw [show 409407431=59*(1559*4451) by decide] at dv
  rcases hp.dvd_mul.mp dv with d|d
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp d)
  rcases hp.dvd_mul.mp d with d|d
  · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp d))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp d))

/-- The first congruence in fact holds at every prime p≥5. -/
theorem first_prime {p:ℕ} (pr:p.Prime) (large:5≤p) : p^5∣(first p).num.natAbs := by
  by_cases h : 7≤p
  · apply first_test h (pr.odd_of_ne_two (by omega))
    intro q hq dq
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hq pr).mp dq
    refine ⟨large,fun dv=>?_⟩
    have := Nat.le_of_dvd (by omega : 0<q-3) dv
    omega
  · have : p=5 := by interval_cases p <;> norm_num at *
    simpa only [this] using first_five

/-- Both assertions fail at the same odd squarefree composite number. -/
theorem composite :
    ¬Nat.Prime 409407431 ∧
    409407431^5∣(first 409407431).num.natAbs ∧
    409407431^4∣(second 409407431).num.natAbs := by
  refine ⟨Nat.not_prime_of_dvd_of_lt (m:=59) (by decide) (by decide) (by decide),?_,?_⟩
  · apply first_test (by decide) (by decide)
    intro p hp dv;rcases factors hp dv with rfl|rfl|rfl <;> decide
  · apply second_test (by decide) (by decide)
    · apply (OMA.CubicBernoulliOriginal284759.original (by decide) (by decide)).mp
      exact OMA.CubicBridge284759.witness OMA.CubicRows284759.row59
        OMA.CubicRows284759.row1559 OMA.CubicRows284759.row4451
    · intro p hp dv;rcases factors hp dv with rfl|rfl|rfl <;> decide

#print axioms first_five
#print axioms first_prime
#print axioms composite

end OMA.ConjectureElevenMestrovic
