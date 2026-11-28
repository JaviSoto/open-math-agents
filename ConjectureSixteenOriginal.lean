import Mathlib

/-! The Bernoulli-square characterization of Meštrović Conjecture 16, JIS 17 (2014), Article 14.8.4. -/

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


end OMA.QuarticIff284760

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


end OMA.IrregularHalfRow284760

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


private theorem local_cube {p n b:ℕ} (hp:p.Prime) (pn:p∣n) (form:n=2*(b+2)+1) (ev:Even b)
    (bp:0<b) (sq:n^2∣(bernoulli (b+2)).num.natAbs) : p^3∣∑ i∈range p,i^(b+2) := by
  let _ : Fact p.Prime:=⟨hp⟩
  obtain ⟨large,good⟩:=rows form ev bp ((dvd_pow_self n (by decide : 2≠0)).trans sq) hp pn
  have diff:=error large hp.pos (dvd_refl p) ev bp (unit_succ hp pn form) good
  have localSq:= (local_num hp.pos (by decide : 0<2) _).mp ((pow_dvd_pow_of_dvd pn 2).trans sq) p hp (dvd_refl p)
  have zero:= (localRing p).add_mem diff localSq
  let S:=∑ i∈range p,i^(b+2)
  change p^3∣S
  rw [←show (S:ℚ).num.natAbs=S by simp,local_num hp.pos (by decide)]
  intro q hq dq
  obtain rfl:=(Nat.prime_dvd_prime_iff_eq hq hp).mp dq
  dsimp [S];push_cast
  simpa only [sub_add_cancel] using zero

private theorem half {p b:ℕ} (hp:p.Prime) (big:7≤p) (ev:Even b) (bp:0<b)
    (evprime:¬p∣b+2) (nd:¬p-1∣b) (cube:p^3∣∑i∈range p,i^(b+2)) :
    p^2∣∑i∈range (p/2),(i+1)^(b+1) := by
  obtain ⟨h,ph⟩:=hp.odd_of_ne_two (by omega)
  have pair:p=2*h+1:=by omega

  have van:=OMA.HalfResidue284760.even_half hp big pair ev bp nd
  have one:=OMA.HalfResidue284760.expansion (c:=1) pair (Or.inl rfl) ev van
  have two:=OMA.HalfResidue284760.expansion (c:=2) pair (Or.inr rfl) ev van
  have z:(∑i∈range p,(i:ZMod (p^3))^(b+2))=0 := by
    simpa only [Nat.cast_sum,Nat.cast_pow] using (ZMod.natCast_eq_zero_iff _ _).mpr cube
  rw [z] at one two
  simp only [Nat.cast_one,one_pow,mul_one] at one
  simp only [Nat.cast_ofNat] at two
  have d:p^3∣p*((b+2)*2^(b+1)*OMA.HalfResidue284760.half h (b+1)) := (ZMod.natCast_eq_zero_iff _ _).mp (by
    push_cast
    rw [pow_succ (2:ZMod (p^3)) (b+1)] at two
    push_cast at one two
    linear_combination 2*(2:ZMod (p^3))^(b+1)*one - two)
  rw [show p^3=p*p^2 by ring] at d
  have dv:=Nat.dvd_of_mul_dvd_mul_left hp.pos d
  have c2:p.Coprime 2:=hp.coprime_iff_not_dvd.mpr (by intro hh;have :=Nat.le_of_dvd (by decide : 0<2) hh;omega)
  have unit:=((hp.coprime_iff_not_dvd.mpr evprime).mul_right (c2.pow_right (b+1))).pow_left 2
  rw [show p/2=h by omega]
  exact unit.dvd_of_dvd_mul_left dv

open OMA.IrregularHalfRow284760

/-- The two published half-row invariants obey a linear congruence with the
digit k + 1/2 mod p, because the half-exponent e satisfies 2e+1=n. -/
theorem half_row {n p:ℕ} (big:5≤n) (res:n%4=1) (hp:p.Prime) (large:7≤p) (pn:p∣n)
    (test:n^3∣∑i∈Icc 1 (n-1),i^((n-1)/2)) :
    let k:=((n-1)/2)%(p-1)
    halfRow p (k-1)+(k+(p+1)/2:ℕ)*(halfRow p (k-1+(p-1))-halfRow p (k-1))=0 := by
  let _ : Fact p.Prime:=⟨hp⟩
  let b := (n-1)/2-2
  have ex:(n-1)/2=b+2 := by dsimp [b];omega
  have form:n=2*(b+2)+1 := by omega
  have pnle:=Nat.le_of_dvd (by omega : 0<n) pn
  have bp:0<b:=by omega
  have ev:Even b:=⟨n/4-1,by omega⟩
  have sq: n^2∣(bernoulli (b+2)).num.natAbs:=ex ▸ (original big res).mp test
  have num:n∣(bernoulli (b+2)).num.natAbs:=(dvd_pow_self n (by decide : 2≠0)).trans sq
  have nr:=OMA.QuarticIff284760.not_regular_den (by omega : 0<b+2) (ev.add (by decide : Even 2)) (pn.trans num)
  obtain ⟨_,good⟩:=rows form ev bp num hp pn
  have de:¬p∣b+2:=by
    intro dv;have pd:p∣2*(b+2):=dvd_mul_of_dvd_right dv 2
    exact hp.not_dvd_one ((Nat.dvd_add_right pd).mp (form ▸ pn))
  have yes:=half hp large ev bp de good (local_cube hp pn form ev bp sq)
  rw [ex]
  let k:=(b+2)%(p-1)
  let y:=(b+2)/(p-1)
  let t:=(p+1)/2
  have id:k+(p-1)*y=b+2 := Nat.mod_add_div _ _
  have kp:0<k:=Nat.pos_of_ne_zero (fun z=>nr (Nat.dvd_of_mod_eq_zero z))
  have nform:n=2*(k+(p-1)*y)+1:=by omega
  have pt:2*t=p+1:=by dsimp [t];obtain ⟨h,hp⟩:=hp.odd_of_ne_two (by omega);omega
  have cls:y≡k+t [MOD p] := by
    apply (ZMod.natCast_eq_natCast_iff ..).mp
    have z: (n:ZMod p)=0:=(ZMod.natCast_eq_zero_iff _ _).mpr pn
    rw [nform,Nat.cast_add,Nat.cast_mul,Nat.cast_add,Nat.cast_mul,Nat.cast_sub hp.one_le,
      ZMod.natCast_self,Nat.cast_one,zero_sub,neg_one_mul,Nat.cast_ofNat] at z
    have th :(2:ZMod p)*t=1 := by
      have d:=congrArg (fun x:ℕ=>(x:ZMod p)) pt
      simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,ZMod.natCast_self,Nat.cast_one,zero_add] using d
    have non:(2:ZMod p)≠0:=by
      change ((2:ℕ):ZMod p)≠0
      rw [ne_eq,ZMod.natCast_eq_zero_iff];intro h;have :=Nat.le_of_dvd (by decide : 0<2) h;omega
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp (show (2:ZMod p)*((y:ZMod p)-(k+t:ℕ))=0 by
      push_cast;linear_combination -z-th)).resolve_left non
  have index : b+1≡k-1+(p-1)*(k+t) [MOD (p-1)*p] := by
    rw [show b+1=k-1+(p-1)*y by omega]
    exact (cls.mul_left' (p-1)).add_left _
  have tot:(p^2).totient=(p-1)*p := by rw [Nat.totient_prime_pow_succ hp];simp [mul_comm]
  have term (i:ℕ) (hi:i∈range (p/2)) :
      ((i+1:ℕ):ZMod (p^2))^(b+1) = ((i+1:ℕ):ZMod (p^2))^(k-1) +
      (k+t:ℕ)*(((i+1:ℕ):ZMod (p^2))^(k-1+(p-1))-((i+1:ℕ):ZMod (p^2))^(k-1)) := by
    have bound:=mem_range.mp hi
    have cp:(i+1).Coprime p := (hp.coprime_iff_not_dvd.mpr (by
      intro z;have :=Nat.le_of_dvd (by omega : 0 < i+1) z;omega)).symm
    rw [←OMA.IrregularHalfRow284760.affine hp cp _ _]
    have reduce (z:ℕ) := Nat.pow_totient_mod (x:=i+1) (n:=p^2) (k:=z) (by nlinarith) (cp.pow_right 2)
    simp only [tot] at reduce
    have eq:(i+1)^(b+1)≡(i+1)^(k-1+(p-1)*(k+t)) [MOD p^2] := calc
      _ ≡ (i+1)^((b+1)%((p-1)*p)) [MOD p^2] := reduce _
      _ ≡ (i+1)^((k-1+(p-1)*(k+t))%((p-1)*p)) [MOD p^2] := by rw [show (b+1)%((p-1)*p)=_ from index]
      _ ≡ _ [MOD p^2] := (reduce _).symm
    simpa only [Nat.cast_pow] using (ZMod.natCast_eq_natCast_iff _ _ _).mpr eq
  have z:(∑i∈range (p/2),((i+1:ℕ):ZMod (p^2))^(b+1))=0 := by
    simpa only [Nat.cast_sum,Nat.cast_pow] using (ZMod.natCast_eq_zero_iff _ _).mpr yes
  rw [sum_congr rfl term,sum_add_distrib,←mul_sum,sum_sub_distrib] at z
  exact z

#print axioms original
#print axioms half_row

end OMA.ConjectureSixteen
