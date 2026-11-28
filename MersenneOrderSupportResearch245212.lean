import Mathlib


/-! Prime support of reduced Mersenne denominators, with an application to A245212. -/

section

/- The multiplicative order of two recovers the index of a reduced
Mersenne denominator. This applies even when the denominator is composite. -/
namespace OMA.MersenneDenominator245212

def Q (t : ℕ) := (2^t-1)/Nat.gcd (2^t-1) t

private theorem twice_le_pow {b : ℕ} (hb : 0 < b) : 2*b ≤ 2^b := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb.ne'
  induction j with
  | zero => decide
  | succ j ih =>
    rw [pow_succ (2:ℕ) (j+1)]
    omega

theorem bound {t : ℕ} (ht : 2 ≤ t) : 2^(t/2)-1 < Q t := by
  let a := t/2
  let b := t-a
  have hp : 0 < b := by dsimp [a,b]; omega
  have cover : a+b=t := by dsimp [a,b]; omega
  have tcap : t ≤ 2^b := (show t≤2*b by dsimp [a,b]; omega).trans (twice_le_pow hp)
  have pa := Nat.two_pow_pos a
  have pb : 1 < 2^b := Nat.one_lt_two_pow hp.ne'
  have det : t*(2^a-1)<2^t-1 := by
    have h := Nat.mul_le_mul_right (2^a-1) tcap
    have z := congrArg (fun x : ℕ => 2^b*x) (Nat.sub_add_cancel (by omega : 1≤2^a))
    have prod : 2^t=2^a*2^b := by rw [←pow_add,cover]
    rw [prod]
    have s : 2^b*(2^a-1)+2^b=2^a*2^b := by nlinarith only [z]
    omega
  have gd := Nat.gcd_dvd_left (2^t-1) t
  have small : (2^t-1).gcd t ≤ t := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right _ _)
  have mul : Q t * ((2^t-1).gcd t)=2^t-1 := Nat.div_mul_cancel gd
  by_contra! h
  have le := Nat.mul_le_mul h small
  change Q t * _ ≤ (2^a-1)*t at le
  rw [mul,mul_comm (2^a-1)] at le
  omega

private theorem pow_test (t m : ℕ) :
    (2 : ZMod (Q t))^m=1 ↔ Q t ∣ 2^m-1 := by
  have h := Nat.modEq_iff_dvd' (show 1≤(2:ℕ)^m from Nat.one_le_pow _ _ (by decide)) (n:=Q t)
  rw [←ZMod.natCast_eq_natCast_iff,Nat.cast_one,Nat.cast_pow,Nat.cast_ofNat] at h
  exact eq_comm.trans h

theorem order {t : ℕ} (ht : 2≤t) : orderOf (2 : ZMod (Q t))=t := by
  have gd := Nat.gcd_dvd_left (2^t-1) t
  have mul : Q t * ((2^t-1).gcd t)=2^t-1 := Nat.div_mul_cancel gd
  apply orderOf_eq_of_pow_and_pow_div_prime (by omega) ((pow_test t t).mpr ⟨_,mul.symm⟩)
  intro p pp pt eq
  have pos : 0<t/p := Nat.div_pos (Nat.le_of_dvd (by omega) pt) pp.pos
  have cap : t/p≤t/2 := Nat.div_le_div_left pp.two_le (by decide)
  have le := Nat.pow_le_pow_right (by decide : 0 < 2) cap
  have mid := bound ht
  have d := Nat.le_of_dvd (by have := Nat.one_lt_two_pow pos.ne'; omega : 0<2^(t/p)-1)
    ((pow_test t _).mp eq)
  omega

theorem injective_on_indices {s t : ℕ} (hs : 2 ≤ s) (ht : 2 ≤ t) (eq : Q s=Q t) : s=t := by
  rw [←order hs,←order ht,eq]

/-- A positive solution of the residual equation has reduced denominator Q(k+1). -/
theorem reduced {x y k : ℕ} (hy : 0 < y) (hk : 1≤k) (quot : k=x/y)
    (sol : 2^(k+1)*(x-k*y)=x+y) : y/(x.gcd y)=Q (k+1) := by
  let t := k+1
  let D := 2^t-1
  let g := D.gcd t
  let P := t/g
  let q := Q t
  let u := x%y
  have qq : u+k*y=x := by simpa only [u,quot,mul_comm] using Nat.mod_add_div x y
  have rem : x-k*y=u := by omega
  change 2^t*(x-k*y)=x+y at sol
  rw [rem] at sol
  have pos : 1<2^t := Nat.one_lt_two_pow (by dsimp [t]; omega)
  have ds : D+1=2^t := by dsimp only [D]; omega
  have ratio : D*u=t*y := by
    change D*u=(k+1)*y
    nlinarith only [sol,qq,congrArg (fun n : ℕ => n*u) ds]
  have dp : 0 < D := by omega
  have gp : 0 < g := Nat.gcd_pos_of_pos_left _ dp
  have qp : 0 < q := Nat.div_pos (Nat.le_of_dvd dp (Nat.gcd_dvd_left D t)) gp
  have af : q*g=D := Nat.div_mul_cancel (Nat.gcd_dvd_left D t)
  have bf : P*g=t := Nat.div_mul_cancel (Nat.gcd_dvd_right D t)
  have red : q*u=P*y := by
    apply Nat.eq_of_mul_eq_mul_right gp
    calc
      q*u*g = q*g*u := by ring
      _ = D*u := by rw [af]
      _ = t*y := ratio
      _ = P*y*g := by rw [←bf]; ring
  have cp : q.Coprime P := Nat.coprime_div_gcd_div_gcd gp
  have d : q∣y := cp.dvd_of_dvd_mul_left (red ▸ dvd_mul_right q u)
  let z := y/q
  have yz : y=q*z := (Nat.mul_div_cancel' d).symm
  have uz : u=P*z := by
    apply Nat.eq_of_mul_eq_mul_left qp
    calc
      q*u = P*y := red
      _ = P*(q*z) := congrArg (P*·) yz
      _ = q*(P*z) := by ring
  have gz : x.gcd y=z := by
    calc
      _ = u.gcd y := by rw [←qq,Nat.gcd_add_mul_right_left]
      _ = (P*z).gcd (q*z) := congrArg₂ Nat.gcd uz yz
      _ = z := by rw [Nat.gcd_mul_right,cp.symm.gcd_eq_one]; simp
  change y/(x.gcd y)=q
  rw [gz]
  have zp : 0 < z := Nat.div_pos (Nat.le_of_dvd hy d) qp
  exact (Nat.div_eq_iff_eq_mul_left zp (by exact ⟨q,yz.trans (Nat.mul_comm q z)⟩)).mpr yz

/-- The denominator alone recovers k+1, without needing the numerator. -/
theorem residual_order {x y k : ℕ} (hy : 0 < y) (hk : 1≤k) (quot : k=x/y)
    (sol : 2^(k+1)*(x-k*y)=x+y) : orderOf (2 : ZMod (y/(x.gcd y)))=k+1 := by
  rw [reduced hy hk quot sol]
  exact order (by omega)

end OMA.MersenneDenominator245212

end

section

/- The reduced Mersenne denominator is determined by its distinct
prime divisors. Each such prime occurs to its base-two Wieferich
valuation, independently of the index. -/
namespace OMA.MersenneOrderSupport245212
open OMA.MersenneDenominator245212 Finset

noncomputable def ord (p : ℕ) := orderOf (2 : ZMod p)

private theorem test (p m : ℕ) :
    (2 : ZMod p)^m=1 ↔ p∣2^m-1 := by
  have h:=Nat.modEq_iff_dvd' (show 1≤(2:ℕ)^m from Nat.one_le_pow _ _ (by decide)) (n:=p)
  rw [←ZMod.natCast_eq_natCast_iff,Nat.cast_one,Nat.cast_pow,Nat.cast_ofNat] at h
  exact eq_comm.trans h

theorem primeOrder {p : ℕ} (hp : p.Prime) (odd : p≠2) : ord p∣p-1 := by
  let _ : Fact p.Prime:=⟨hp⟩
  have nz : (2:ZMod p)≠0 := by
    change ((2:ℕ):ZMod p)≠0
    rw [Ne,ZMod.natCast_eq_zero_iff]
    exact fun d=>odd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp d)
  exact ZMod.orderOf_dvd_card_sub_one nz

private theorem oddOrder {p : ℕ} (hp : p.Prime) (odd : p≠2) :
    0<ord p ∧ ¬p∣ord p := by
  have div:=primeOrder hp odd
  have sub : 0<p-1 := by have:= hp.one_lt;omega
  refine ⟨Nat.pos_of_dvd_of_pos div sub,?_⟩
  exact fun d=>by have:=Nat.le_of_dvd sub (d.trans div);omega

private theorem order_test (p m : ℕ) : ord p ∣ m ↔ p∣2^m-1 :=
  (orderOf_dvd_iff_pow_eq_one).trans (test p m)

private theorem qdiv (t : ℕ) : Q t∣2^t-1 := Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)

private theorem qpos {t : ℕ} (ht : 0<t) : 0<Q t := by
  have z : 0<2^t-1 := Nat.sub_pos_of_lt (Nat.one_lt_two_pow ht.ne')
  apply Nat.div_pos (Nat.le_of_dvd z (Nat.gcd_dvd_left _ _))
  exact Nat.gcd_pos_of_pos_left _ z

private theorem indexLTE {p t : ℕ} (hp : p.Prime) (odd : p≠2) (ht : 0<t) (div : ord p∣t) :
    (2^t-1).factorization p=(2^(ord p)-1).factorization p+t.factorization p := by
  obtain ⟨k,eq⟩:=div
  have kp : k≠0 := fun h=>by simp [eq,h] at ht
  have dp:=oddOrder hp odd
  have sub := (order_test p (ord p)).mp dvd_rfl
  have nd : ¬ p∣2^(ord p) := fun h=>odd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
    (hp.dvd_of_dvd_pow h))
  let _ : Fact p.Prime:=⟨hp⟩
  have h:=padicValNat.pow_sub_pow (hp.odd_of_ne_two odd) (x:=2^ord p) (y:=1)
    (Nat.one_lt_two_pow dp.1.ne') sub nd kp
  rw [one_pow,←pow_mul,←eq,←Nat.factorization_def _ hp,
    ←Nat.factorization_def _ hp,←Nat.factorization_def _ hp] at h
  rw [eq,Nat.factorization_mul dp.1.ne' kp,Finsupp.add_apply,Nat.factorization_eq_zero_of_not_dvd dp.2,
    zero_add,←eq]
  exact h

/-- Removing gcd(2^t−1,t) cancels precisely the index's contribution in LTE. -/
theorem valuation {p t : ℕ} (hp : p.Prime) (odd : p≠2) (ht : 0<t) (div : ord p∣t) :
    (Q t).factorization p=(2^(ord p)-1).factorization p := by
  have mn := (Nat.sub_pos_of_lt (Nat.one_lt_two_pow ht.ne')).ne'
  have h:=indexLTE hp odd ht div
  rw [Q,Nat.factorization_div (Nat.gcd_dvd_left _ _),Finsupp.tsub_apply,
    Nat.factorization_gcd mn ht.ne',Finsupp.inf_apply]
  omega

/-- Which primes survive the reduction: all the Mersenne number's prime factors
survive, with no extra primes, even if they also divide the index. -/
theorem support {p t : ℕ} (hp : p.Prime) (odd : p≠2) (ht : 0<t) :
    p∣Q t ↔ ord p∣t := by
  constructor
  · exact fun h=>(order_test p t).mpr (h.trans (qdiv t))
  · intro dv
    have h:=hp.factorization_pos_of_dvd (Nat.sub_pos_of_lt
      (Nat.one_lt_two_pow (oddOrder hp odd).1.ne')).ne' ((order_test p (ord p)).mp dvd_rfl)
    rw [←valuation hp odd ht dv] at h
    exact (dvd_pow_self p h.ne').trans (Nat.ordProj_dvd _ _)

theorem wieferich {p t : ℕ} (hp : p.Prime) (odd : p≠2) (ht : 0<t) (div : p∣Q t) :
    (Q t).factorization p=(2^(p-1)-1).factorization p := by
  rw [valuation hp odd ht ((support hp odd ht).mp div)]
  have sp : 0<p-1 := by have:=hp.one_lt;omega
  have h:=indexLTE hp odd sp (primeOrder hp odd)
  rw [Nat.factorization_eq_zero_of_not_dvd (p:=p) (n:=p-1)
    (fun h=>by have:=Nat.le_of_dvd sp h;omega),add_zero] at h
  exact h.symm

private theorem not_two {t : ℕ} (ht : 0<t) : ¬2∣Q t := by
  have ev : 2∣2^t := dvd_pow_self _ ht.ne'
  intro d; have h:=d.trans (qdiv t); have:=Nat.two_pow_pos t;omega

/-- The index is the lcm of the orders modulo DISTINCT primes of Q(t);
no prime-power order or factorization exponent is needed. -/
theorem index {t : ℕ} (ht : 2≤t) : (Q t).primeFactors.lcm ord=t := by
  let L:=(Q t).primeFactors.lcm ord
  have tpos : 0<t := by omega
  have qnz:=(qpos tpos).ne'
  apply Nat.dvd_antisymm
  · refine Finset.lcm_dvd fun p mem=>?_
    obtain ⟨hp,pd,_⟩:=Nat.mem_primeFactors.mp mem
    exact (order_test p t).mpr (pd.trans (qdiv t))
  · suffices all : Q t∣2^L-1 by
      simpa only [OMA.MersenneDenominator245212.order ht] using orderOf_dvd_of_pow_eq_one ((test _ L).mpr all)
    apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
    intro p j hp jd
    by_cases z : j=0
    · simp [z]
    have pd: p∣Q t := (dvd_pow_self p z).trans jd
    have odd : p≠2 := fun eq=>not_two tpos (eq ▸ pd)
    have dv:ord p∣L := Finset.dvd_lcm (f:=ord) (Nat.mem_primeFactors.mpr ⟨hp,pd,qnz⟩)
    have ordp:=(oddOrder hp odd).1
    have pk:= (hp.pow_dvd_iff_le_factorization qnz).mp jd
    rw [valuation hp odd tpos ((support hp odd tpos).mp pd)] at pk
    have jm:= (hp.pow_dvd_iff_le_factorization (Nat.sub_pos_of_lt (Nat.one_lt_two_pow ordp.ne')).ne').mpr pk
    obtain ⟨a,ha⟩:=dv
    exact jm.trans (by rw [ha,pow_mul]; simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow (2^ord p) 1 a)

theorem support_injective {s t : ℕ} (hs : 2 ≤ s) (ht : 2 ≤ t) (eq : (Q s).primeFactors=(Q t).primeFactors) :
    s=t := by rw [←index hs,←index ht,eq]

theorem index_dvd {t y : ℕ} (ht : 2≤t) (hy : y≠0) (div : Q t∣y) :
    t∣(y.primeFactors.filter (·≠2)).lcm (fun p=>p-1) := by
  rw [←index ht]
  refine Finset.lcm_dvd fun p mem=>?_
  obtain ⟨hp,pd,_⟩:=Nat.mem_primeFactors.mp mem
  have odd : p≠2 := fun eq=>not_two (by omega) (eq ▸ pd)
  exact (primeOrder hp odd).trans (Finset.dvd_lcm (Finset.mem_filter.mpr
    ⟨Nat.mem_primeFactors.mpr ⟨hp,pd.trans div,hy⟩,odd⟩))

theorem residual {x y k : ℕ} (hy : 0<y) (hk : 1≤k) (quot : k=x/y)
    (sol : 2^(k+1)*(x-k*y)=x+y) : k+1∣(y.primeFactors.filter (·≠2)).lcm (fun p=>p-1) := by
  apply index_dvd (by omega) hy.ne'
  rw [←OMA.MersenneDenominator245212.reduced hy hk quot sol]
  exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_right _ _)

/-- An elementary exact formula for every odd prime's exponent,
including the zero case. -/
theorem formula {p t : ℕ} (hp : p.Prime) (odd : p≠2) (ht : 0<t) :
    (Q t).factorization p=if ord p∣t then (2^(p-1)-1).factorization p else 0 := by
  classical
  split_ifs with h
  · exact wieferich hp odd ht ((support hp odd ht).2 h)
  · exact Nat.factorization_eq_zero_of_not_dvd (fun d=>h ((support hp odd ht).1 d))

theorem index_of_pos {t : ℕ} (ht : 0<t) : (Q t).primeFactors.lcm ord=t := by
  by_cases ht' : 2≤t
  · exact index ht'
  · have eq : t=1 := by omega
    simp [eq,Q]

/-- Strong divisibility: the gcd of any two denominators is the
denominator of the gcd of their indices. -/
theorem strong_divisibility {s t : ℕ} (hs : 0 < s) (ht : 0 < t) :
    (Q s).gcd (Q t)=Q (s.gcd t) := by
  have hg:=Nat.gcd_pos_of_pos_left t hs
  apply Nat.factorization_inj (Nat.gcd_pos_of_pos_left _ (qpos hs)).ne' (qpos hg).ne'
  rw [Nat.factorization_gcd (qpos hs).ne' (qpos ht).ne']
  ext p
  rw [Finsupp.inf_apply]
  by_cases prime : p.Prime
  · by_cases isTwo : p=2
    · subst p;simp only [Nat.factorization_eq_zero_of_not_dvd (not_two hs),
        Nat.factorization_eq_zero_of_not_dvd (not_two ht),Nat.factorization_eq_zero_of_not_dvd (not_two hg),inf_idem]
    · rw [formula prime isTwo hs,formula prime isTwo ht,formula prime isTwo hg]
      by_cases a : ord p∣s <;> by_cases b : ord p∣t <;> simp [a,b,Nat.dvd_gcd_iff]
  · simp [Nat.factorization_eq_zero_of_not_prime _ prime]

/-- Divisibility of denominators is precisely divisibility of indices. -/
theorem divisor_embedding {s t : ℕ} (hs : 0 < s) (ht : 0 < t) : Q s∣Q t ↔ s∣t := by
  constructor
  · intro d
    have sub : (Q s).primeFactors⊆(Q t).primeFactors := fun p mem=>
      Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors mem,(Nat.dvd_of_mem_primeFactors mem).trans d,(qpos ht).ne'⟩
    simpa only [index_of_pos hs,index_of_pos ht] using Finset.lcm_mono (f:=ord) sub
  · intro st
    have g := strong_divisibility hs ht
    rw [Nat.gcd_eq_left st] at g
    exact g ▸ Nat.gcd_dvd_right (Q s) (Q t)

def eligible (y : ℕ) : Finset ℕ :=
  y.primeFactors.filter fun p=>p≠2 ∧ (2^(p-1)-1).factorization p≤y.factorization p

/-- Before considering the index at all, discard primes not occurring
to their necessary Wieferich exponent in y. The remaining prime orders
give a generally sharper bound than the lcm of p−1. -/
theorem eligible_index {t y : ℕ} (ht : 0<t) (hy : y≠0) (qy : Q t∣y) :
    t∣(eligible y).lcm ord := by
  have weights:=(Nat.factorization_le_iff_dvd (qpos ht).ne' hy).2 qy
  have sub : (Q t).primeFactors⊆eligible y := by
    intro p mem
    obtain ⟨hp,pd,_⟩:=Nat.mem_primeFactors.mp mem
    have odd : p≠2 := fun h=>not_two ht (h ▸ pd)
    apply Finset.mem_filter.mpr
    refine ⟨Nat.mem_primeFactors.mpr ⟨hp,pd.trans qy,hy⟩,odd,?_⟩
    rw [←wieferich hp odd ht pd]
    exact (Finsupp.le_def.mp weights) p
  simpa only [index_of_pos ht] using Finset.lcm_mono (f:=ord) sub

/-- Cancelling the gcd with the index preserves the full prime support. -/
theorem q_primes {t : ℕ} (ht : 0<t) : (Q t).primeFactors=(2^t-1).primeFactors := by
  have mp := Nat.sub_pos_of_lt (Nat.one_lt_two_pow ht.ne')
  ext p
  constructor
  · intro mem
    obtain ⟨hp,d,_⟩:=Nat.mem_primeFactors.mp mem
    exact Nat.mem_primeFactors.mpr ⟨hp,d.trans (qdiv t),mp.ne'⟩
  · intro mem
    obtain ⟨hp,d,_⟩:=Nat.mem_primeFactors.mp mem
    have odd : p≠2 := by
      rintro rfl
      have ev : 2∣2^t:=dvd_pow_self _ ht.ne'
      omega
    exact Nat.mem_primeFactors.mpr ⟨hp,(support hp odd ht).2 ((order_test p t).2 d),(qpos ht).ne'⟩

/-- Even for the unreduced Mersenne sequence, knowing only which primes occur
determines the order of divisibility of the indices. -/
theorem support_embedding {s t : ℕ} (hs : 0<s) (ht : 0<t) :
    (2^s-1).primeFactors⊆(2^t-1).primeFactors ↔ s∣t := by
  rw [←q_primes hs,←q_primes ht]
  constructor
  · intro sub
    simpa only [index_of_pos hs,index_of_pos ht] using Finset.lcm_mono (f:=ord) sub
  · intro d p mem
    obtain ⟨hp,pd,_⟩:=Nat.mem_primeFactors.mp mem
    exact Nat.mem_primeFactors.mpr ⟨hp,pd.trans ((divisor_embedding hs ht).2 d),(qpos ht).ne'⟩

/-- Exact recognition: the candidate index is computed from the distinct
prime divisors. It remains only to check their permitted exponents and
that no further Mersenne prime has been omitted. -/
theorem recognize {t y : ℕ} (ht : 0<t) (hy : 0<y) :
    Q t=y ↔ y.primeFactors=(2^t-1).primeFactors ∧
      ∀ p∈y.primeFactors, y.factorization p=(2^(p-1)-1).factorization p := by
  constructor
  · rintro rfl
    refine ⟨q_primes ht,fun p mem=>?_⟩
    obtain ⟨hp,pd,_⟩:=Nat.mem_primeFactors.mp mem
    exact wieferich hp (fun h=>not_two ht (h ▸ pd)) ht pd
  · rintro ⟨h,exps⟩
    have same : (Q t).primeFactors=y.primeFactors := (q_primes ht).trans h.symm
    apply Nat.factorization_inj (qpos ht).ne' hy.ne'
    ext p
    by_cases mem : p∈(Q t).primeFactors
    · obtain ⟨hp,pd,_⟩:=Nat.mem_primeFactors.mp mem
      exact (wieferich hp (fun eq=>not_two ht (eq ▸ pd)) ht pd).trans
        (exps p (same ▸ mem)).symm
    · have m' : p∉y.primeFactors := by rwa [←same]
      rw [←Nat.support_factorization] at mem m'
      simp only [Finsupp.mem_support_iff,not_not] at mem m'
      rw [mem,m']

end OMA.MersenneOrderSupport245212

end

#print axioms OMA.MersenneOrderSupport245212.recognize
