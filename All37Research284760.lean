import Mathlib

/-! Meštrović’s quartic power-sum conjecture, OEIS A284760.
Complete prime-power obstruction and full exclusion of factors below 59.
Original Lean proof for @JaviSoto (OpenAI Codex); see arXiv:1211.4570. -/

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

namespace OMA.PowerTable284760
open Finset

/-- First nonempty local-power-sum row below 59: 37, at index 32 modulo 36. -/
theorem small :
    ∀ p ∈ range 59, p.Prime → 5≤p → ∀ r ∈ range (p*(p-1)),
      r%2=0 → (r+3)%p=0 → p^2∣∑i∈Ico 1 p,i^r → p=37 ∧ r%36=32 := by
  intro p hp pr big
  rw [mem_range] at hp
  interval_cases p <;> first | contradiction | norm_num at pr
  all_goals decide +kernel

end OMA.PowerTable284760

/-! A p-adic obstruction at every prime-power divisor, including arbitrary
multiplicities and other coprime factors of the original integer. -/
namespace OMA.PowerHierarchy284760
open Nat Finset

private theorem even_square {n:ℕ} (on:Odd n) (nn:5≤n)
    (hz:n^4∣∑i∈Ico 1 n,i^(n-2)) : n^2∣∑i∈range n,i^(n-3) := by
  have od : Odd (n-2) := by obtain ⟨k,h⟩:=on;exact ⟨k-1,by omega⟩
  have val := OMA.PowerSumRegular284760.reflect3 on od (by omega)
  have zeros : (∑i∈Ico 1 n,(i:ZMod (n^3))^(n-2))=0 := by
    simpa only [Nat.cast_sum,Nat.cast_pow] using (ZMod.natCast_eq_zero_iff _ _).mpr
      ((pow_dvd_pow n (by decide : 3≤4)).trans hz)
  rw [zeros,mul_zero,show n-2-1=n-3 by omega] at val
  have dv : n^3∣n*((n-2)*(∑i∈Ico 1 n,i^(n-3))) :=
    (ZMod.natCast_eq_zero_iff _ _).mp (by push_cast;rw [←mul_assoc];exact val.symm)
  have cop : n.Coprime (n-2) :=
    (Nat.coprime_self_sub_right (by omega)).mpr (Nat.coprime_two_right.mpr on)
  rw [pow_succ'] at dv
  rw [←OMA.PowerSumRegular284760.ico_range on.pos (by exact zero_pow (by omega : n-3≠0))]
  exact (cop.pow_left 2).dvd_of_dvd_mul_left (Nat.dvd_of_mul_dvd_mul_left on.pos dv)

private theorem lift {p P m e : ℕ} (hp:p.Prime) (big:5≤p) (pP:p∣P) (Pm:P∣m)
    (om:Odd m) (odd:Odd (e-1)) :
    (∑i∈range (m*p),(i:ZMod (p*(P*m)))^e)=
      (p:ZMod (p*(P*m)))*∑i∈range m,(i:ZMod (p*(P*m)))^e := by
  let R:=ZMod (p*(P*m))
  have vanish (a:ℕ) (h:p*(P*m)∣a) : (a:R)=0 := (ZMod.natCast_eq_zero_iff ..).mpr h
  have cube : (m:R)^3=0 := by
    rw [←Nat.cast_pow];apply vanish
    rw [pow_succ,pow_two,←mul_assoc];exact Nat.mul_dvd_mul_right (Nat.mul_dvd_mul (pP.trans Pm) Pm) m
  have lin : (m:R)*(∑j∈range p,(j:R))*(∑i∈range m,(i:R)^(e-1))=0 := by
    have h : p*(P*m)∣m*(∑j∈range p,j)*(∑i∈range m,i^(e-1)) := by
      obtain ⟨u,hu⟩:=OMA.PowerSumRegular284760.div_linear (hp.odd_of_ne_two (by omega))
      obtain ⟨v,hv⟩:=Pm.trans (OMA.PowerSumRegular284760.odd_range om odd)
      use u*v;rw [hu,hv];ring
    simpa only [R,Nat.cast_mul,Nat.cast_sum,Nat.cast_pow] using vanish _ h
  have sq : (m:R)^2*(∑j∈range p,(j:R)^2)=0 := by
    have h : p*(P*m)∣m^2*(∑j∈range p,j^2) := by
      obtain ⟨u,hu⟩:=Pm;obtain ⟨v,hv⟩:=OMA.PowerSumRegular284760.div_square hp big
      use u*v;rw [hu,hv];ring
    simpa only [R,Nat.cast_mul,Nat.cast_sum,Nat.cast_pow] using vanish _ h
  rw [OMA.PowerSumRegular284760.moments (R:=R) m p e cube]
  linear_combination (e:R)*lin + (e.choose 2:R)*(∑i∈range m,(i:R)^(e-2))*sq


private theorem strip {p b e:ℕ} (hp:p.Prime) (big:5≤p) (bp:0<b) (oe:Odd (e-1))
    (u:ℕ) (ou:Odd u) (hs:p^b*(p^b*u)∣∑i∈range (p^b*u),i^e) :
    (p^b)^2∣∑i∈range (p^b),i^e := by
  let P:=p^b
  have pP:p∣P:=dvd_pow_self _ bp.ne'
  have oP:Odd P := (hp.odd_of_ne_two (by omega)).pow
  induction u using Nat.strong_induction_on with
  | h u ih =>
    by_cases pu:p∣u
    · obtain ⟨v,rfl⟩:=pu
      have ov:= (Nat.odd_mul.mp ou).2
      let m:=P*v
      have ident : p^b*(p*v)=m*p := by dsimp [m,P];ring
      have modid : p^b*(m*p)=p*(P*m) := by dsimp [P];ring
      rw [ident,modid] at hs
      have zero : (∑i∈range (m*p),(i:ZMod (p*(P*m)))^e)=0 := by
        simpa only [Nat.cast_sum,Nat.cast_pow] using (ZMod.natCast_eq_zero_iff _ _).mpr hs
      rw [lift hp big pP (dvd_mul_right P v) (oP.mul ov) oe] at zero
      have dv : p*(P*m) ∣ p*(∑i∈range m,i^e) :=
        (ZMod.natCast_eq_zero_iff _ _).mp (by push_cast;exact zero)
      exact ih v (by nlinarith only [ov.pos,hp.one_lt]) ov (Nat.dvd_of_mul_dvd_mul_left hp.pos dv)
    · have zero : (∑i∈range (P*u),(i:ZMod (P^2))^e)=0 := by
        have div:(P^2)∣∑i∈range (P*u),i^e:=(show P^2∣P*(P*u) by rw [pow_two,←mul_assoc];exact dvd_mul_right _ _).trans hs
        simpa only [Nat.cast_sum,Nat.cast_pow] using (ZMod.natCast_eq_zero_iff _ _).mpr div
      rw [OMA.PowerSumRegular284760.first_block oP oe] at zero
      apply (((hp.coprime_iff_not_dvd.mpr pu).pow_left b).pow_left 2).dvd_of_dvd_mul_left
      exact (ZMod.natCast_eq_zero_iff _ _).mp (by push_cast;exact zero)

/-- Passing the original test forces a separate quadratic divisibility test
at every positive power of each prime p≥5 dividing n. -/
theorem power_test {n p b:ℕ} (on:Odd n) (hp:p.Prime) (big:5≤p) (bp:0<b) (div:p^b∣n)
    (hz:n^4∣∑i∈Ico 1 n,i^(n-2)) : (p^b)^2∣∑i∈Ico 1 (p^b),i^(n-3) := by
  have nn:=Nat.le_of_dvd on.pos ((dvd_pow_self p bp.ne').trans div)
  have t:=even_square on (by omega) hz
  have od : Odd (n-3-1) := by obtain ⟨k,h⟩:=on;exact ⟨k-2,by omega⟩
  rw [OMA.PowerSumRegular284760.ico_range (pow_pos hp.pos _) (by exact zero_pow (by omega : n-3≠0))]
  obtain ⟨u,hu⟩:=div
  have sq:p^b*n∣n^2 := by rw [pow_two];exact Nat.mul_dvd_mul_right ⟨u,hu⟩ n
  have div' := sq.trans t
  conv at div' => lhs;right;rw [hu]
  conv at div' => rhs;arg 1;rw [hu]
  exact strip hp big bp od u ((Nat.odd_mul.mp (hu ▸ on)).2) div'

end OMA.PowerHierarchy284760

namespace OMA.Square37Table284760
open Nat Finset

/-- Binary modular exponentiation; fuel bounds the bit length of the exponent. -/
def binary (m x : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | f+1, e =>
      let h:=binary m x f (e/2)
      (h*h*(if e%2=0 then 1 else x))%m

private theorem binary_cast (m x f e:ℕ) (he:e<2^f) : (binary m x f e:ZMod m)=(x:ZMod m)^e := by
  induction f generalizing e with
  | zero=>simp at he;subst e;simp [binary]
  | succ f ih=>
    rw [pow_succ] at he
    rw [binary,ZMod.natCast_mod]
    push_cast
    rw [ih _ (by omega)]
    split_ifs with h
    · simp only [mul_one,←pow_add];congr 1;omega
    · convert (show ((x:ZMod m)^(e/2)*(x:ZMod m)^(e/2))*(x:ZMod m)=(x:ZMod m)^(e/2+e/2+1) by
          rw [pow_succ,pow_add]) using 2;omega

private theorem row (e:ℕ) (lt:e<2^17)
    (w:(∑i∈Ico (1:ℕ) 1369,binary 1874161 i 17 e)%1874161=607836) :
    (∑i∈Ico (1:ℕ) 1369,(i:ZMod 1874161)^e)=607836 := by
  calc
    _ = ((∑i∈Ico (1:ℕ) 1369,binary 1874161 i 17 e:ℕ):ZMod 1874161) := by
      push_cast;apply sum_congr rfl;intro i _;exact (binary_cast _ _ _ _ lt).symm
    _ = _ := by rw [←ZMod.natCast_mod,w];rfl

set_option maxRecDepth 8192 in
theorem row_one : (∑i∈Ico (1:ℕ) 1369,(i:ZMod 1874161)^47912)=607836 := by
  apply row _ (by decide);decide +kernel

set_option maxRecDepth 8192 in
theorem row_two : (∑i∈Ico (1:ℕ) 1369,(i:ZMod 1874161)^97196)=607836 := by
  apply row _ (by decide);decide +kernel

end OMA.Square37Table284760

/-! The first surviving prime in the local table can occur only once in any
counterexample. Two computed rows suffice for every lift of the exponent. -/
namespace OMA.Square37Original284760
open Finset Nat

private theorem period_term (i j:ℕ) (ip : 0 < i) :
    (i:ZMod 1874161)^(47912+49284*j) =
      (i:ZMod 1874161)^47912+j*((i:ZMod 1874161)^97196-(i:ZMod 1874161)^47912) := by
  let R:=ZMod 1874161
  by_cases d:37∣i
  · have v : (i:R)^4=0 := by
      rw [←Nat.cast_pow];apply (ZMod.natCast_eq_zero_iff _ _).mpr
      exact pow_dvd_pow_of_dvd d 4
    have vanish (k:ℕ) (large:4≤k) : (i:R)^k=0 := by
      obtain ⟨a,ha⟩:=Nat.exists_eq_add_of_le large;rw [ha,pow_add,v,zero_mul]
    rw [vanish _ (by omega),vanish _ (by decide),vanish _ (by decide)];ring
  · have c : i.Coprime (37^2) := ((show Nat.Prime 37 by decide).coprime_iff_not_dvd.mpr d).symm.pow_right _
    have phi : (37^2:ℕ).totient=1332 := by
      rw [Nat.totient_prime_pow_succ (by decide : Nat.Prime 37) 1];decide
    have h:=Nat.ModEq.pow_totient c
    rw [phi] at h
    have h':1 ≡ i^49284 [MOD 1369] := by
      simpa only [←pow_mul,one_pow,show 1332*37=49284 by decide,show 37^2=1369 by decide] using (h.pow 37).symm
    obtain ⟨a,ha⟩:=h'.dvd'
    have bound : 1 ≤ i^49284 := pow_pos ip _
    have len:i^49284=1+1369*a := by omega
    have zz : (1369:R)^2=0 := by decide
    have step : (i:R)^49284=1+1369*(a:R) := by
      simpa only [R,Nat.cast_pow,Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat] using congrArg (fun t:ℕ=>(t:ZMod 1874161)) len
    have linear : ((i:R)^49284)^j=1+j*((i:R)^49284-1) := by
      rw [step,OMA.PowerSum284760.taylor 1 _ (by rw [mul_pow,zz,zero_mul])]
      simp
    rw [pow_add,pow_mul,linear,show (97196:ℕ)=47912+49284 by decide,pow_add];ring

/-- In fact no odd multiple of 1369, with arbitrary other prime factors,
can satisfy the quartic divisibility in the conjecture. -/
theorem original (n:ℕ) (odd:Odd n) (div:37^2∣n) :
    (∑i∈Ico 1 n,i^(n-2))%n^4≠0 := by
  intro fail
  have bad:=Nat.dvd_of_mod_eq_zero fail
  have prime : Nat.Prime 37 := by decide
  have pn:= (show 37∣37^2 by decide).trans div
  have loc:=OMA.PowerSumRegular284760.finite_test odd prime (by decide) pn bad
  have table:=OMA.PowerTable284760.small 37 (by decide) prime (by decide) _
    (mem_range.mpr (Nat.mod_lt _ (by decide))) loc.1 loc.2.1 loc.2.2
  have mod36 : n-3 ≡ 47912 [MOD 36] := by
    change (n-3)%36=32
    simpa only [Nat.mod_mod_of_dvd _ (by decide : 36∣37*(37-1))] using table.2
  have nn:=Nat.le_of_dvd odd.pos div
  have mod1369 : n-3 ≡ 47912 [MOD 1369] := by
    change (n-3)%1369=1366
    have nzero : n%1369=0:=Nat.mod_eq_zero_of_dvd div
    omega
  have both:=(Nat.modEq_and_modEq_iff_modEq_mul (by decide : Nat.Coprime 36 1369)).mp ⟨mod36,mod1369⟩
  change (n-3)%49284=47912 at both
  let j:=(n-3)/49284
  have exp:n-3=47912+49284*j:=by rw [←both];exact (Nat.mod_add_div _ _).symm
  have t:=OMA.PowerHierarchy284760.power_test odd prime (by decide) (by decide : 0<2) div bad
  norm_num only [show 37^2=1369 by decide,show 1369^2=1874161 by decide] at t
  have z : (∑i∈Ico (1:ℕ) 1369,(i:ZMod 1874161)^(47912+49284*j))=0 := by
    rw [←exp];simpa only [Nat.cast_sum,Nat.cast_pow] using (ZMod.natCast_eq_zero_iff _ _).mpr t
  simp only [sum_congr rfl (fun i (hi:i∈Ico (1:ℕ) 1369)=>period_term i j (mem_Ico.mp hi).1),
    sum_add_distrib,←mul_sum,sum_sub_distrib,OMA.Square37Table284760.row_one,
    OMA.Square37Table284760.row_two,sub_self,mul_zero,add_zero] at z
  exact (by decide : (607836:ZMod 1874161)≠0) z

end OMA.Square37Original284760

namespace OMA.First37Rows284760
open Nat Finset

private theorem tangent {R:Type*} [CommRing R] (x:R) (d e j:ℕ)
    (zero:(x^d-1)^2=0) :
    x^(e+d*j)=x^e+j*(x^(e+d)-x^e) := by
  have h:((x^d)^j)=1+j*(x^d-1) := by
    have q:=OMA.PowerSum284760.taylor (1:R) (x^d-1) zero j
    simpa using q
  rw [pow_add,pow_mul,h,pow_add];ring

private theorem term (i e j:ℕ) (hi:i∈range 37) (ep:0<e) :
    (i:ZMod 1874161)^(e+1332*j) =
      (i:ZMod 1874161)^e+j*((i:ZMod 1874161)^(e+1332)-(i:ZMod 1874161)^e) := by
  by_cases iz:i=0
  · subst i;simp [zero_pow ep.ne',zero_pow (by omega : e+1332*j≠0)]
  have bound:=mem_range.mp hi
  have cp : i.Coprime (37^2) := ((show Nat.Prime 37 by decide).coprime_iff_not_dvd.mpr
    (fun h=>bound.not_ge (Nat.le_of_dvd (by omega) h))).symm.pow_right _
  have phi : (37^2:ℕ).totient=1332 := by
    rw [Nat.totient_prime_pow_succ (by decide : Nat.Prime 37) 1];decide
  have h:=Nat.ModEq.pow_totient cp
  rw [phi] at h
  obtain ⟨a,ha⟩:=h.symm.dvd'
  have pos : 0 < i^1332 := pow_pos (by omega : 0 < i) _
  have len:i^1332=1+1369*a := by norm_num at ha;omega
  have step : (i:ZMod 1874161)^1332=1+1369*(a:ZMod 1874161) := by
    simpa only [Nat.cast_pow,Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat] using congrArg (fun t:ℕ=>(t:ZMod 1874161)) len
  apply tangent
  rw [step,add_sub_cancel_left,mul_pow,show (1369:ZMod 1874161)^2=0 by decide,zero_mul]

private theorem stable (w e v j:ℕ) (ep:0<e)
    (first:(w*(∑i∈range 37,i^e))%1874161=v)
    (next:(w*(∑i∈range 37,i^(e+1332)))%1874161=v) :
    (w:ZMod 1874161)*(∑i∈range 37,(i:ZMod 1874161)^(e+1332*j))=v := by
  have castrow (u:ℕ) (h:(w*(∑i∈range 37,i^u))%1874161=v) :
      (w:ZMod 1874161)*(∑i∈range (37:ℕ),(i:ZMod 1874161)^u)=v := by
    simpa only [ZMod.natCast_mod,Nat.cast_mul,Nat.cast_sum,Nat.cast_pow] using congrArg (fun t:ℕ=>(t:ZMod 1874161)) h
  rw [sum_congr rfl (fun i hi=>term i e j hi ep),sum_add_distrib,←mul_sum,sum_sub_distrib]
  linear_combination (1-(j:ZMod 1874161))*castrow _ first+(j:ZMod 1874161)*castrow _ next

set_option maxHeartbeats 1000000 in
/-- Four weighted Taylor coefficients for a full block, independent of the
lift of the exponent by a multiple of 37·36. -/
theorem rows (j:ℕ) :
    (∑i∈range (37:ℕ),(i:ZMod 1874161)^(1293+1332*j))=1266325 ∧
    37*(∑i∈range (37:ℕ),(i:ZMod 1874161)^(1292+1332*j))=607836 ∧
    37^2*(∑i∈range (37:ℕ),(i:ZMod 1874161)^(1291+1332*j))=0 ∧
    37^3*(∑i∈range (37:ℕ),(i:ZMod 1874161)^(1290+1332*j))=0 := by
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [Nat.cast_one,one_mul,Nat.cast_ofNat] using stable 1 1293 1266325 j (by decide) (by decide +kernel) (by decide +kernel)
  · simpa only [Nat.cast_ofNat] using stable 37 1292 607836 j (by decide) (by decide +kernel) (by decide +kernel)
  · rw [show (37:ZMod 1874161)^2=(1369:ℕ) by decide]
    exact stable 1369 1291 0 j (by decide) (by decide +kernel) (by decide +kernel)
  · rw [show (37:ZMod 1874161)^3=(50653:ℕ) by decide]
    exact stable 50653 1290 0 j (by decide) (by decide +kernel) (by decide +kernel)

end OMA.First37Rows284760

namespace OMA.First37Blocks284760
open Finset Nat

private theorem cubic {R:Type*} [CommRing R] (x y:R) (h:y^4=0) (k:ℕ) (big:3≤k) :
    (x+y)^k = x^k+(k:R)*x^(k-1)*y+(k.choose 2:R)*x^(k-2)*y^2+
      (k.choose 3:R)*x^(k-3)*y^3 := by
  rw [add_comm x y,add_pow]
  have cut :
      (∑i∈range (k+1),y^i*x^(k-i)*(k.choose i:R))=
      ∑i∈range 4,y^i*x^(k-i)*(k.choose i:R) := by
    symm;apply sum_subset (range_mono (by omega))
    intro i hi out
    have large : 4 ≤ i := by simp only [mem_range] at out;omega
    obtain ⟨a,ha⟩:=Nat.exists_eq_add_of_le large
    rw [ha,pow_add,h];ring
  rw [cut];simp only [sum_range_succ,sum_range_zero,Nat.choose_zero_right,Nat.choose_one_right,
    Nat.cast_one,pow_zero,pow_one,Nat.sub_zero,zero_add,one_mul,mul_one]
  ring

private theorem block (t j:ℕ) :
    (∑i∈range (37:ℕ),((37*t+i:ℕ):ZMod 1874161)^(1293+1332*j))=
    1266325*(1+2*(t:ZMod 1874161)) := by
  let R:=ZMod 1874161
  let k:=1293+1332*j
  obtain ⟨h0,h1,h2,h3⟩:=OMA.First37Rows284760.rows j
  have castk : (k:R)*607836=2*1266325 := by
    dsimp [k,R];push_cast
    have h : (1332:ZMod 1874161)*607836=0 := by decide
    have h' : (1293:ZMod 1874161)*607836=2*1266325 := by decide
    linear_combination h'+(j:ZMod 1874161)*h
  have ex1 : k-1=1292+1332*j := by dsimp [k];omega
  have ex2 : k-2=1291+1332*j := by dsimp [k];omega
  have ex3 : k-3=1290+1332*j := by dsimp [k];omega
  calc
    _ = ∑i∈range (37:ℕ), ((i:R)^k +
          ((k:R)*t*37)*(i:R)^(k-1)+
          ((k.choose 2:R)*(t:R)^2*37^2)*(i:R)^(k-2)+
          ((k.choose 3:R)*(t:R)^3*37^3)*(i:R)^(k-3)) := by
      apply sum_congr rfl;intro i _
      push_cast
      rw [add_comm,cubic (i:R) (37*(t:R)) (by rw [mul_pow,show (37:R)^4=0 by decide,zero_mul]) k (by dsimp [k];omega)]
      ring
    _ = _ := by
      simp only [sum_add_distrib,←mul_sum,ex1,ex2,ex3]
      linear_combination h0+(k:R)*(t:R)*h1+(k.choose 2:R)*(t:R)^2*h2+
        (k.choose 3:R)*(t:R)^3*h3+(t:R)*castk

/-- Once 37 divides n only once, this residue modulo 37⁴ is nonzero. -/
theorem block_sum (m j:ℕ) :
    (∑i∈range (37*m),(i:ZMod 1874161)^(1293+1332*j))=1266325*(m:ZMod 1874161)^2 := by
  rw [OMA.PowerSum284760.blocks]
  simp_rw [block _ j]
  rw [←mul_sum,sum_add_distrib,←mul_sum,sum_const,card_range,nsmul_eq_mul,mul_one]
  congr 1
  have id := sum_range_id_mul_two m
  cases m with
  | zero=>simp
  | succ m=>
    have castid := congrArg (fun a:ℕ=>(a:ZMod 1874161)) id
    simp only [Nat.cast_mul,Nat.cast_sum,Nat.cast_ofNat,Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one] at castid ⊢
    linear_combination castid

end OMA.First37Blocks284760

namespace OMA.First37Original284760
open Finset Nat

/-- No odd multiple of 37 is a counterexample to Meštrović's conjecture,
including numbers divisible by 37 only once. -/
theorem original (n:ℕ) (odd:Odd n) (div:37∣n) :
    (∑i∈Ico 1 n,i^(n-2))%n^4≠0 := by
  by_cases square:37^2∣n
  · exact OMA.Square37Original284760.original n odd square
  intro fail
  have bad:=Nat.dvd_of_mod_eq_zero fail
  have hp:Nat.Prime 37:=by decide
  have nn:=Nat.le_of_dvd odd.pos div
  have loc:=OMA.PowerSumRegular284760.finite_test odd hp (by decide) div bad
  have table:=OMA.PowerTable284760.small 37 (by decide) hp (by decide) _
    (mem_range.mpr (Nat.mod_lt _ (by decide))) loc.1 loc.2.1 loc.2.2
  have mod36 : n-3 ≡ 1292 [MOD 36] := by
    change (n-3)%36=32
    simpa only [Nat.mod_mod_of_dvd _ (by decide : 36∣37*(37-1))] using table.2
  have mod37 : n-3 ≡ 1292 [MOD 37] := by
    change (n-3)%37=34
    have z :=Nat.mod_eq_zero_of_dvd div
    omega
  have both:=(Nat.modEq_and_modEq_iff_modEq_mul (by decide : Nat.Coprime 36 37)).mp ⟨mod36,mod37⟩
  change (n-3)%1332=1292 at both
  let j:=(n-3)/1332
  have exp:n-3=1292+1332*j:=by rw [←both];exact (Nat.mod_add_div _ _).symm
  have ek:n-2=1293+1332*j:=by omega
  have di : 1874161∣∑i∈range n,i^(n-2) := by
    have replace : (∑i∈Ico 1 n,i^(n-2))=∑i∈range n,i^(n-2) := by
      simpa [zero_pow (by omega : n-2≠0)] using sum_range_add_sum_Ico (fun i:ℕ=>i^(n-2)) odd.pos
    rw [←replace];exact (pow_dvd_pow_of_dvd div 4).trans bad
  rw [ek] at di
  obtain ⟨m,rfl⟩:=div
  have z : (∑i∈range (37*m),(i:ZMod 1874161)^(1293+1332*j))=0 := by
    simpa only [Nat.cast_sum,Nat.cast_pow] using (ZMod.natCast_eq_zero_iff _ _).mpr di
  rw [OMA.First37Blocks284760.block_sum] at z
  have dm : 37^3*37∣37^3*(25*m^2) := (ZMod.natCast_eq_zero_iff _ _).mp (by
    push_cast;rw [←mul_assoc,show (50653:ZMod 1874161)*25=1266325 by decide];exact z)
  have a:=Nat.dvd_of_mul_dvd_mul_left (by decide : 0<37^3) dm
  have pm:=hp.dvd_of_dvd_pow ((hp.dvd_mul.mp a).resolve_left (by decide))
  apply square;rw [pow_two];exact Nat.mul_dvd_mul_left _ pm

/-- A single prime factor below 59 rules out a counterexample; the other
prime factors and every multiplicity are unrestricted. -/
theorem low_factor {n p:ℕ} (odd:Odd n) (hp:p.Prime) (div:p∣n) (small:p<59) :
    (∑i∈Ico 1 n,i^(n-2))%n^4≠0 := by
  have nn:=Nat.le_of_dvd odd.pos div
  by_cases big:5≤p
  · intro z
    have l:=OMA.PowerSumRegular284760.finite_test odd hp big div (Nat.dvd_of_mod_eq_zero z)
    have period:0<p*(p-1):=Nat.mul_pos (by omega) (by omega)
    obtain ⟨rfl,_⟩:=OMA.PowerTable284760.small p (mem_range.mpr small) hp big _
      (mem_range.mpr (Nat.mod_lt _ period)) l.1 l.2.1 l.2.2
    exact original n odd div z
  · have po:=Nat.coprime_two_left.mp ((Nat.coprime_two_left.mpr odd).of_dvd_right div)
    have eq:p=3 := by obtain ⟨b,h⟩:=po;have :=hp.two_le;omega
    subst p
    intro z
    apply OMA.PowerSum284760.local_obstruction odd hp div
      (show 3-1∣n-3 from by obtain ⟨b,h⟩:=odd;exact ⟨b-1,by omega⟩)
    exact (pow_dvd_pow n (by decide : 2≤4)).trans (Nat.dvd_of_mod_eq_zero z)

end OMA.First37Original284760

#print axioms OMA.PowerHierarchy284760.power_test
#print axioms OMA.First37Original284760.original
#print axioms OMA.First37Original284760.low_factor
