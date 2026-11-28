import FormalConjectures.OEIS.«245212»

import Mathlib


/-! Recovering every exponent from a reduced prime-power denominator. -/

section

/- The distinct odd prime divisors of (b^t-1) recover the index (t\ge3),
even for odd bases. No existence theorem for primitive prime divisors is needed. -/
namespace OMA.RepunitOrder245212

private def geom (x : ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => geom x k+x^k

private theorem telescope (x k : ℕ) (hx : 1≤x) : geom x k*(x-1)+1=x^k := by
  induction k with
  | zero => simp [geom]
  | succ k ih =>
    have h : x-1+1=x := by omega
    simp only [geom,pow_succ]
    nlinarith only [ih, congrArg (fun j : ℕ => x^k*j) h]

private theorem geom_gt {x : ℕ} (hx : 2≤x) (k : ℕ) : k+2<geom x (k+2) := by
  induction k with
  | zero => simpa [geom] using (by omega : 2<1+x)
  | succ k ih =>
    have h:=Nat.one_lt_pow (a:=x) (by omega : k+2≠0) (by omega)
    change k+1+2<geom x (k+2)+x^(k+2)
    omega

private theorem geom_mod_two {x k : ℕ} (hk : Odd k) : ¬2∣geom x k := by
  by_cases ev : 2∣x
  · obtain ⟨a,rfl⟩:=ev
    suffices h : ∀ j, ¬2∣geom (2*a) (j+1) by
      cases k with
      | zero => simp at hk
      | succ k => exact h k
    intro j
    induction j with
    | zero => simp [geom]
    | succ j ih =>
      have d : 2∣(2*a)^(j+1) := (dvd_mul_right 2 a).trans (dvd_pow_self _ (by omega))
      change ¬2∣geom (2*a) (j+1)+(2*a)^(j+1)
      omega
  · have xodd:=Nat.odd_iff.mpr (by omega : x%2=1)
    have h : ∀ j, geom x j%2=j%2 := by
      intro j
      induction j with
      | zero => rfl
      | succ j ih =>
        have o:=Nat.odd_iff.mp (xodd.pow (n:=j))
        change (geom x j+x^j)%2=(j+1)%2
        omega
    have := h k
    have := Nat.odd_iff.mp hk
    omega

private theorem odd_step {x q : ℕ} (hx : 2≤x) (hq : 2≤q) (odd : Odd q) :
    ∃ p : ℕ, p.Prime ∧ p≠2 ∧ p∣x^q-1 ∧ ¬p∣x-1 := by
  let G:=geom x q
  have lower : q<G := by
    have e : q=q-2+2 := by omega
    simpa only [G,←e] using geom_gt hx (q-2)
  have xq : G*(x-1)=x^q-1 := by have := telescope x q (by omega); dsimp only [G];omega
  by_contra! none
  suffices G∣q from (Nat.not_le_of_lt lower) (Nat.le_of_dvd (by omega) this)
  apply (Nat.factorization_le_iff_dvd (by omega) (by omega)).mp
  intro p
  by_cases hp : p.Prime
  · by_cases dv : p∣G
    · have po : p≠2 := fun eq=>geom_mod_two odd (eq ▸ dv)
      have pg : p∣x^q-1 := xq ▸ (dv.trans (dvd_mul_right G (x-1)))
      have px:=none p hp po pg
      have nn : ¬p∣x := by
        intro hh
        have h1 : p∣1 := (show x-(x-1)=1 by omega) ▸ Nat.dvd_sub hh px
        have := Nat.le_of_dvd (by decide : 0<1) h1
        have:=hp.two_le;omega
      let _ : Fact p.Prime:=⟨hp⟩
      have h:=padicValNat.pow_sub_pow (hp.odd_of_ne_two po) (x:=x) (y:=1) (by omega) px nn (by omega : q≠0)
      rw [one_pow,←Nat.factorization_def _ hp,←Nat.factorization_def _ hp,←Nat.factorization_def _ hp,
        ←xq,Nat.factorization_mul (by omega) (by omega),Finsupp.add_apply] at h
      omega
    · simp [Nat.factorization_eq_zero_of_not_dvd dv]
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

private theorem odd_factor {z : ℕ} (hz : 1<z) (zo : ¬2∣z) :
    ∃ p, p.Prime ∧ p≠2 ∧ p∣z := by
  let p:=z.minFac
  have d : p∣z := z.minFac_dvd
  exact ⟨p,Nat.minFac_prime (by omega),fun eq=>zo (eq ▸ d),d⟩

private theorem square_plus {z : ℕ} (hz : 1<z) :
    ∃ p, p.Prime ∧ p≠2 ∧ p∣z^2+1 := by
  rcases Nat.even_or_odd z with ⟨w,hw⟩|⟨w,hw⟩
  · have h : z^2+1=2*(2*w^2)+1 := by rw [hw];ring
    exact odd_factor (by nlinarith) (by rw [h];omega)
  · have wpos : 0<w := by omega
    have fac : z^2+1=2*(2*(w*(w+1))+1) := by rw [hw];ring
    obtain ⟨p,prime,odd,d⟩:=odd_factor (z:=2*(w*(w+1))+1)
      (by have h : 0<w*(w+1) := by positivity
          omega) (by omega)
    exact ⟨p,prime,odd,fac ▸ d.trans (dvd_mul_left _ _)⟩

private theorem power_plus {b u : ℕ} (hb : 2≤b) (hu : 2≤u) :
    ∃ p, p.Prime ∧ p≠2 ∧ p∣b^u+1 := by
  rcases Nat.even_or_odd u with ⟨v,hv⟩|⟨v,hv⟩
  · have vp : 0<v := by omega
    have h : b^u=(b^v)^2 := by rw [←pow_mul];congr 1;omega
    rw [h];exact square_plus (Nat.one_lt_pow vp.ne' (by omega))
  · have vp : 0<v := by omega
    let G := geom (b^2) v
    have tel := telescope (b^2) v (Nat.one_le_pow _ _ (by omega))
    have pb : 1<(b^2)^v := Nat.one_lt_pow vp.ne' (by nlinarith)
    change G*(b^2-1)+1=(b^2)^v at tel
    have Gp : 0<G := by by_contra! nz;rw [show G=0 by omega] at tel;omega
    have bsub : b-1+1=b := by omega
    have bsub2 := Nat.sub_add_cancel (Nat.one_le_pow 2 b (by omega))
    have bz : b^2-1=(b-1)*(b+1) := by nlinarith [congrArg (fun j : ℕ=>j*(b+1)) bsub]
    rw [bz] at tel
    have shift : b^u=(b^2)^v*b := by rw [←pow_mul,←pow_succ,hv]
    let R := 1+b*(b-1)*G
    have fact : b^u+1=R*(b+1) := by rw [shift,←tel];dsimp only [R];ring
    have dv : 2∣b*(b-1) := by
      by_cases ev : 2∣b
      · exact ev.trans (dvd_mul_right _ _)
      · exact (by omega : 2∣b-1).trans (dvd_mul_left _ _)
    have no : ¬2∣R := by have := dv.trans (dvd_mul_right (b*(b-1)) G);dsimp only [R];omega
    have rb : 1<R := by
      dsimp only [R]
      have dpos : 0<b-1:=by omega
      have bpos : 0<b:=by omega
      have prod : 0<b*(b-1)*G:=by positivity
      omega
    obtain ⟨p,prime,odd,d⟩:=odd_factor rb no
    exact ⟨p,prime,odd,fact ▸ d.trans (dvd_mul_right _ _)⟩

noncomputable def ord (b p : ℕ) := orderOf (b : ZMod p)

private theorem order_test {b p m : ℕ} (hb : 0<b) :
    ord b p ∣ m ↔ p∣b^m-1 := by
  rw [ord,orderOf_dvd_iff_pow_eq_one]
  have h:=Nat.modEq_iff_dvd' (show 1≤b^m from Nat.one_le_pow _ _ hb) (n:=p)
  rw [←ZMod.natCast_eq_natCast_iff,Nat.cast_one,Nat.cast_pow] at h
  exact eq_comm.trans h

noncomputable def oddOrders (b t : ℕ) :=
  ((b^t-1).primeFactors.filter (·≠2)).lcm (ord b)

/-- All distinct odd prime divisors together recover the exponent for every
integer base at least two and every exponent at least three. -/
theorem recover {b t : ℕ} (hb : 2≤b) (ht : 3≤t) : oddOrders b t=t := by
  let L:=oddOrders b t
  have based : ∀ {p : ℕ}, p.Prime → p≠2 → p∣b^t-1 → ord b p∣L := by
    intro p hp po d
    apply Finset.dvd_lcm
    exact Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp,d,
      (Nat.sub_pos_of_lt (Nat.one_lt_pow (by omega) (by omega))).ne'⟩,po⟩
  have Lt : L∣t := by
    apply Finset.lcm_dvd
    exact fun p h=>(order_test (by omega : 0<b)).2
      (Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp h).1)
  change L=t
  by_contra different
  obtain ⟨c,tc⟩:=Lt
  have cp : 1<c := by
    by_contra! small
    interval_cases c <;> simp_all
  let q:=c.minFac
  have qp : q.Prime:=Nat.minFac_prime (by omega)
  obtain ⟨j,cj⟩:=c.minFac_dvd
  let u:=L*j
  have expn : t=u*q := by dsimp only [u];rw [tc,cj];ring
  have up : 0<u := by by_contra! z;rw [show u=0 by omega] at expn;omega
  have all : ∀ {p:ℕ}, p.Prime → p≠2 → p∣b^t-1 → p∣b^u-1 := fun hp po d=>
    (order_test (by omega : 0<b)).1 ((based hp po d).trans (dvd_mul_right L j))
  by_cases two : q=2
  · have t2 : t=u*2 := by rwa [two] at expn
    have u2 : 2≤u := by omega
    obtain ⟨p,hp,po,d⟩:=power_plus hb u2
    have z : 1<b^u:=Nat.one_lt_pow up.ne' (by omega)
    have fac : b^t-1=(b^u+1)*(b^u-1) := by
      rw [t2,pow_mul]
      have h : b^u-1+1=b^u := by omega
      have pos : 0<(b^u)^2 := by positivity
      have h2 : (b^u)^2-1+1=(b^u)^2 := by omega
      nlinarith [congrArg (fun j : ℕ=>j*(b^u+1)) h]
    have prev:=all hp po (fac ▸ d.trans (dvd_mul_right _ _))
    have dp : p∣2 := (show b^u+1-(b^u-1)=2 by omega) ▸ Nat.dvd_sub d prev
    exact po ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 dp)
  · obtain ⟨p,hp,po,d,no⟩:=odd_step (x:=b^u) (Nat.one_lt_pow up.ne' (by omega)) qp.two_le
      (qp.odd_of_ne_two two)
    exact no (all hp po (by simpa only [expn,pow_mul] using d))

/-- The reduced denominator of t/(b^t-1). -/
def Q (b t : ℕ) := (b^t-1)/Nat.gcd (b^t-1) t

theorem odd_primes {b t : ℕ} (hb : 2≤b) (ht : 0<t) :
    ((Q b t).primeFactors.filter (·≠2))=((b^t-1).primeFactors.filter (·≠2)) := by
  have mn : 0<b^t-1:=Nat.sub_pos_of_lt (Nat.one_lt_pow ht.ne' (by omega))
  have gd:=Nat.gcd_dvd_left (b^t-1) t
  have qd : Q b t ∣ b^t-1:=Nat.div_dvd_of_dvd gd
  have qpos := Nat.pos_of_dvd_of_pos qd mn
  ext p
  simp only [Finset.mem_filter]
  refine and_congr_left fun odd=>?_ 
  constructor
  · intro mem
    obtain ⟨hp,d,_⟩:=Nat.mem_primeFactors.mp mem
    exact Nat.mem_primeFactors.mpr ⟨hp,d.trans qd,mn.ne'⟩
  · intro mem
    obtain ⟨hp,d,_⟩:=Nat.mem_primeFactors.mp mem
    let _ : Fact p.Prime:=⟨hp⟩
    have pb : ¬p∣b := by
      intro h
      have h' := h.trans (dvd_pow_self b ht.ne')
      have d1 : p∣1 := (show b^t-(b^t-1)=1 by omega) ▸ Nat.dvd_sub h' d
      have:=Nat.le_of_dvd (by decide : 0<1) d1
      have:=hp.two_le;omega
    have dn : ord b p∣p-1 := ZMod.orderOf_dvd_card_sub_one (fun eq=>pb (ZMod.natCast_eq_zero_iff b p|>.mp eq))
    have dp : 0<ord b p := Nat.pos_of_dvd_of_pos dn (by have:=hp.two_le;omega)
    have dn' : ¬p∣ord b p := by
      intro d'
      have := Nat.le_of_dvd (by have:=hp.two_le;omega : 0<p-1) (d'.trans dn)
      have:=hp.two_le
      omega
    obtain ⟨k,eq⟩:=(order_test (by omega : 0<b)).2 d
    have kp : k≠0 := fun h=>by simp [eq,h] at ht
    have test:= (order_test (by omega : 0<b) (p:=p) (m:=ord b p)).1 dvd_rfl
    have posD : 0<b^(ord b p)-1:=Nat.sub_pos_of_lt (Nat.one_lt_pow dp.ne' (by omega))
    have vp:=hp.factorization_pos_of_dvd posD.ne' test
    have h:=padicValNat.pow_sub_pow (hp.odd_of_ne_two odd) (x:=b^ord b p) (y:=1)
      (by omega) test (fun dd=>pb (hp.dvd_of_dvd_pow dd)) kp
    rw [one_pow,←pow_mul,←eq,←Nat.factorization_def _ hp,←Nat.factorization_def _ hp,←Nat.factorization_def _ hp] at h
    have vpT : t.factorization p=k.factorization p := by
      rw [eq,Nat.factorization_mul dp.ne' kp,Finsupp.add_apply,Nat.factorization_eq_zero_of_not_dvd dn',zero_add]
    have posQ : 0<(Q b t).factorization p := by
      rw [Q,Nat.factorization_div gd,Finsupp.tsub_apply,Nat.factorization_gcd mn.ne' ht.ne',Finsupp.inf_apply]
      omega
    exact Nat.mem_primeFactors.mpr ⟨hp,(dvd_pow_self p posQ.ne').trans (Nat.ordProj_dvd _ _),qpos.ne'⟩

theorem reduced_recover {b t : ℕ} (hb : 2≤b) (ht : 3≤t) :
    ((Q b t).primeFactors.filter (·≠2)).lcm (ord b)=t := by
  rw [odd_primes hb (by omega)]
  exact recover hb ht

theorem denominator {b t : ℕ} (hb : 2≤b) (ht : 0<t) :
    ((t:ℚ)+(t:ℚ)/((b:ℚ)^t-1)).den=Q b t := by
  have mn : 0<b^t-1 := Nat.sub_pos_of_lt (Nat.one_lt_pow ht.ne' (by omega))
  have bpos : 0<b:=by omega
  have castD : (((b^t-1:ℕ):ℤ):ℚ)=(b:ℚ)^t-1 := by
    push_cast [Nat.one_le_pow t b bpos]
    rfl
  rw [Rat.natCast_add_den,←castD,←Int.cast_natCast (R:=ℚ) t,←Rat.divInt_eq_div,Rat.den_divInt,
    if_neg (Int.ofNat_ne_zero.mpr mn.ne')]
  rfl

/-- For indices one and two, it suffices to test if the denominator equals
the first term. For all larger indices the odd prime set alone suffices. -/
noncomputable def readIndex (b y : ℕ) :=
  if y=b-1 then 1 else max 2 ((y.primeFactors.filter (·≠2)).lcm (ord b))

theorem read_all {b t : ℕ} (hb : 2≤b) (ht : 0<t) : readIndex b (Q b t)=t := by
  by_cases one : t=1
  · simp [one,readIndex,Q]
  by_cases two : t=2
  · subst t
    have neq : Q b 2≠b-1 := by
      intro eq
      have mult : Q b 2 * (b^2-1).gcd 2=b^2-1:=Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)
      have cap := Nat.le_of_dvd (by decide : 0<2) (Nat.gcd_dvd_right (b^2-1) 2)
      have bound:=Nat.mul_le_mul_left (b-1) cap
      have bb := Nat.sub_add_cancel (Nat.one_le_pow 2 b (by omega))
      have bp : b-1+1=b := by omega
      rw [eq] at mult
      have sq : 0<(b-1)*(b-1) := Nat.mul_pos (by omega) (by omega)
      nlinarith [congrArg (fun j : ℕ=>j*b) bp,congrArg (fun j : ℕ=>j*(b-1)) bp]
    rw [readIndex,if_neg neq,max_eq_left]
    rw [odd_primes hb (by decide)]
    apply Nat.le_of_dvd (by decide)
    apply Finset.lcm_dvd
    exact fun p mem=>(order_test (by omega : 0<b) (m:=2)).2
      (Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp mem).1)
  · have large : 3≤t := by omega
    have recov:=reduced_recover hb large
    have neq : Q b t≠b-1 := by
      intro eq
      rw [eq] at recov
      have bound : ((b-1).primeFactors.filter (·≠2)).lcm (ord b)∣1 := by
        apply Finset.lcm_dvd
        intro p mem
        apply (order_test (by omega : 0<b) (m:=1)).2
        simpa only [pow_one] using Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp mem).1
      rw [recov] at bound
      have:=Nat.le_of_dvd (by decide : 0<1) bound
      omega
    simp only [readIndex,if_neg neq,recov,max_eq_right (by omega : 2≤t)]

end OMA.RepunitOrder245212

end

section

/- Exact interval certificates for the mixed 7-smooth A245212 family.
An absent upper endpoint represents the limit at an unbounded exponent. -/
namespace OMA.Smooth245212
open Finset

def Y (p : ℕ) : Option ℕ → ℚ
  | none => 0
  | some e => (((p:ℚ)⁻¹^(e+1)-1)/((p:ℚ)⁻¹-1))/(e+1)

def X (p : ℕ) (e : Option ℕ) : ℚ := 1+(1-Y p e)/((p:ℚ)-1)

theorem y_avg {p : ℕ} (hp : 1<p) (e : ℕ) :
    Y p (some e)=(∑ i ∈ range (e+1), (p:ℚ)⁻¹^i)/((e:ℚ)+1) := by
  rw [geom_sum_eq (x := (p:ℚ)⁻¹) (by
    have : (1:ℚ)<p := by exact_mod_cast hp
    exact (inv_lt_one_of_one_lt₀ this).ne)]; rfl

theorem y_nonneg {p : ℕ} (hp : 1<p) (e : Option ℕ) : 0≤Y p e := by
  cases e with
  | none => rfl
  | some e => rw [y_avg hp]; positivity

theorem y_anti {p : ℕ} (hp : 1<p) : Antitone (fun e : ℕ => Y p (some e)) := by
  have pr : (1:ℚ)<p := by exact_mod_cast hp
  have lp := (inv_lt_one_of_one_lt₀ pr).le
  have pos : 0≤(p:ℚ)⁻¹ := by positivity
  apply antitone_nat_of_succ_le
  intro e
  simp only [y_avg hp,Nat.cast_add,Nat.cast_one]
  rw [sum_range_succ _ (e+1),div_le_div_iff₀ (by positivity) (by positivity)]
  have small : (∑ _i ∈ range (e+1), (p:ℚ)⁻¹^(e+1)) ≤ ∑ i∈range (e+1), (p:ℚ)⁻¹^i :=
    sum_le_sum (fun i hi => pow_le_pow_of_le_one pos lp (mem_range.mp hi).le)
  simp only [sum_const,card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one] at small
  nlinarith only [small]

theorem y_one {p : ℕ} (hp : 1<p) (e : Option ℕ) : Y p e ≤ 1 := by
  cases e with
  | none => norm_num [Y]
  | some e =>
    have h := y_anti hp (Nat.zero_le e)
    simpa [y_avg hp] using h

theorem x_nonneg {p : ℕ} (hp : 1<p) (e : Option ℕ) : 0≤X p e := by
  have pr : (1:ℚ)<p := by exact_mod_cast hp
  have := sub_nonneg.mpr (y_one hp e)
  unfold X; positivity

structure Band where
  lo : ℕ
  hi : Option ℕ
  deriving DecidableEq

def Band.Contains (b : Band) (e : ℕ) := b.lo≤e ∧ ∀ h, b.hi=some h → e≤h

private theorem mono_range {p e : ℕ} (hp : 1<p) {b : Band} (h : b.Contains e) :
    Y p b.hi ≤ Y p (some e) ∧ Y p (some e) ≤ Y p (some b.lo) ∧
    X p (some b.lo) ≤ X p (some e) ∧ X p (some e) ≤ X p b.hi := by
  have le' : Y p b.hi ≤ Y p (some e) := by
    cases hh : b.hi with
    | none => exact y_nonneg hp _
    | some t => exact y_anti hp (h.2 t hh)
  have ge' := y_anti hp h.1
  have pr : (1:ℚ)<p := by exact_mod_cast hp
  exact ⟨le',ge',by unfold X; gcongr,by unfold X; gcongr⟩

abbrev I := Fin 4
abbrev Box := I → Band
def prime (i : I) : ℕ := ![2,3,5,7] i
theorem prime_lt (i : I) : 1 < prime i := by fin_cases i <;> decide

def score (e : I → ℕ) : ℚ :=
  (∏ i, X (prime i) (some (e i))) + ∏ i, Y (prime i) (some (e i))
def lower (b : Box) : ℚ :=
  (∏ i, X (prime i) (some (b i).lo)) + ∏ i, Y (prime i) (b i).hi
def upper (b : Box) : ℚ :=
  (∏ i, X (prime i) (b i).hi) + ∏ i, Y (prime i) (some (b i).lo)

theorem enclosure {b : Box} {e : I → ℕ} (h : ∀ i,(b i).Contains (e i)) :
    lower b ≤ score e ∧ score e ≤ upper b := by
  have v (i : I) := mono_range (prime_lt i) (h i)
  constructor
  · exact add_le_add
      (prod_le_prod (fun i _ => x_nonneg (prime_lt i) _) (fun i _ => (v i).2.2.1))
      (prod_le_prod (fun i _ => y_nonneg (prime_lt i) _) (fun i _ => (v i).1))
  · exact add_le_add
      (prod_le_prod (fun i _ => x_nonneg (prime_lt i) _) (fun i _ => (v i).2.2.2))
      (prod_le_prod (fun i _ => y_nonneg (prime_lt i) _) (fun i _ => (v i).2.1))

inductive Tree
| leaf
| split (i : I) (cut : ℕ) (left right : Tree)

def left (b : Box) (i : I) (cut : ℕ) : Box := Function.update b i ⟨(b i).lo, some cut⟩
def right (b : Box) (i : I) (cut : ℕ) : Box := Function.update b i ⟨cut+1, (b i).hi⟩
def Tree.check : Tree → Box → Bool
| .leaf,b => decide (2 < lower b ∨ upper b < 2)
| .split i cut l r,b => l.check (left b i cut) && r.check (right b i cut)

theorem Tree.sound (tree : Tree) {b : Box} (cert : tree.check b = true)
    {e : I → ℕ} (h : ∀ i,(b i).Contains (e i)) : score e ≠ 2 := by
  induction tree generalizing b with
  | leaf =>
    obtain pos|neg := of_decide_eq_true cert
    · exact ((enclosure h).1.trans_lt' pos).ne'
    · exact ((enclosure h).2.trans_lt neg).ne
  | split i cut l r il ir =>
    obtain ⟨cl,cr⟩ := Bool.and_eq_true_iff.mp cert
    by_cases ec : e i≤cut
    · apply il cl
      intro j; by_cases ji : j=i
      · subst j; simpa [left,Band.Contains] using And.intro (h i).1 ec
      · simpa [left,ji] using h j
    · apply ir cr
      intro j; by_cases ji : j=i
      · subst j; simpa [right,Band.Contains] using And.intro (by omega : cut+1≤e i) (h i).2
      · simpa [right,ji] using h j

end OMA.Smooth245212

end

section

/- Identification of the interval score with the original weighted sum. -/
namespace OMA.Smooth245212
open Finset ArithmeticFunction Nat
open scoped ArithmeticFunction.sigma Function

def W : ArithmeticFunction ℕ := (ArithmeticFunction.id.pmul (σ 0)) * ArithmeticFunction.zeta
lemma w_mult : W.IsMultiplicative :=
  (isMultiplicative_id.pmul isMultiplicative_sigma).mul isMultiplicative_zeta
lemma w_apply (n : ℕ) : W n = ∑ d∈n.divisors, d*d.divisors.card := by
  rw [W,mul_zeta_apply]
  simp only [pmul_apply,id_apply,sigma_zero_apply]
lemma w_pow {p : ℕ} (hp : Nat.Prime p) (e : ℕ) :
    W (p^e) = ∑ j ∈ range (e+1), p^j*(j+1) := by
  rw [w_apply,Nat.sum_divisors_prime_pow hp]
  simp [Nat.divisors_prime_pow hp]

private lemma weighted (p : ℚ) (e : ℕ) :
    (p-1)*(∑ j ∈ range (e+1), p^j*((j:ℚ)+1)) =
      ((e:ℚ)+1)*p^(e+1)-∑ j ∈ range (e+1), p^j := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [sum_range_succ _ (e+1),sum_range_succ _ (e+1),mul_add,ih,pow_succ p (e+1)]
    push_cast; ring

theorem y_factor {p : ℕ} (hp : Nat.Prime p) (e : ℕ) :
    Y p (some e)*(((e:ℚ)+1)*(p:ℚ)^e) = (σ 1 (p^e) : ℚ) := by
  have pn : (p:ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [y_avg hp.one_lt,sigma_one_apply_prime_pow hp]
  push_cast
  calc
    _ = ∑ j ∈ range (e+1), (p:ℚ)⁻¹^j*(p:ℚ)^e := by rw [←sum_mul]; field_simp
    _ = ∑ j ∈ range (e+1), (p:ℚ)^(e-j) := by
      refine sum_congr rfl fun j hj => ?_
      have add : j+(e-j)=e := by have := mem_range.mp hj; omega
      calc
        _ = (p:ℚ)⁻¹^j*((p:ℚ)^j*(p:ℚ)^(e-j)) := by rw [←pow_add,add]
        _ = _ := by rw [inv_pow,←mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ pn),one_mul]
    _ = _ := by simpa using sum_range_reflect (fun j => (p:ℚ)^j) (e+1)

theorem x_factor {p : ℕ} (hp : Nat.Prime p) (e : ℕ) :
    X p (some e)*(((e:ℚ)+1)*(p:ℚ)^e) = (W (p^e) : ℚ) := by
  have y := y_factor hp e
  rw [sigma_one_apply_prime_pow hp] at y
  push_cast at y
  rw [w_pow hp]; push_cast
  have pp : (1:ℚ)<p := by exact_mod_cast hp.one_lt
  have h := weighted (p:ℚ) e
  rw [pow_succ] at h
  dsimp [X]
  field_simp [sub_ne_zero.mpr pp.ne']
  linear_combination -h - y

theorem prime_prime (i : I) : Nat.Prime (prime i) := by fin_cases i <;> decide
theorem different : Function.Injective prime := by decide
def number (e : I → ℕ) := ∏ i, prime i^(e i)

section General
variable {ι : Type*} [Fintype ι] (p : ι → ℕ)
def total (e : ι → ℕ) : ℕ := ∏ i, p i^(e i)
private def tax (e : ι → ℕ) : ℚ := ∏ i, (((e i:ℕ):ℚ)+1)*(p i:ℚ)^(e i)
def normalized (e : ι → ℕ) : ℚ :=
  (∏ i, X (p i) (some (e i))) + ∏ i, Y (p i) (some (e i))

theorem normalized_of_eq (hp : ∀ i, Nat.Prime (p i)) (hinj : Function.Injective p)
    (e : ι → ℕ) (heq : OeisA245212.a (total p e)=(σ 1 (total p e) : ℤ)) :
    normalized p e=2 := by
  classical
  let z (i : ι) := p i ^ (e i)
  have cop : (↑(univ : Finset ι) : Set ι).Pairwise (Coprime on z) := by
    intro i _ j _ h
    exact (((Nat.coprime_primes (hp i) (hp j)).mpr
      (fun eq => h (hinj eq))).pow_left _).pow_right _
  have nz (i : ι) : z i ≠ 0 := pow_ne_zero _ (hp i).ne_zero
  have nn : total p e ≠ 0 := prod_ne_zero_iff.mpr (fun i _ => nz i)
  have tot : W (total p e) = total p e*(total p e).divisors.card +
      ∑ d ∈ (total p e).properDivisors,d*d.divisors.card := by
    calc
      _ = ∑ d ∈ insert (total p e) (total p e).properDivisors, d*d.divisors.card := by
        rw [Nat.insert_self_properDivisors nn,w_apply]
      _ = _ := sum_insert Nat.self_notMem_properDivisors
  have balanced : (W (total p e) : ℚ)+(σ 1 (total p e) : ℚ) =
      2*(total p e:ℚ)*(σ 0 (total p e) : ℚ) := by
    unfold OeisA245212.a at heq
    have ti : (W (total p e):ℤ) = (total p e:ℤ)*(total p e).divisors.card+
        ∑ d∈(total p e).properDivisors,(d:ℤ)*d.divisors.card := by exact_mod_cast tot
    rw [sigma_zero_apply]
    exact_mod_cast (by linarith : (W (total p e):ℤ)+(σ 1 (total p e):ℤ) =
      2*(total p e:ℤ)*(total p e).divisors.card)
  have wp := IsMultiplicative.map_prod z w_mult univ cop
  have sp := IsMultiplicative.map_prod z (isMultiplicative_sigma (k:=1)) univ cop
  have tp := IsMultiplicative.map_prod z (isMultiplicative_sigma (k:=0)) univ cop
  change W (total p e)=_ at wp
  change σ 1 (total p e)=_ at sp
  change σ 0 (total p e)=_ at tp
  simp only [z,sigma_zero_apply_prime_pow (hp _)] at tp
  have factors : tax p e = (total p e:ℚ)*(σ 0 (total p e):ℚ) := by
    rw [tax,prod_mul_distrib,tp,total]
    push_cast; ring
  have taxpos : 0<tax p e := by
    unfold tax
    exact prod_pos fun i _ => mul_pos (by positivity) (pow_pos (by exact_mod_cast (hp i).pos) _)
  apply mul_right_cancel₀ taxpos.ne'
  unfold normalized
  rw [add_mul,show (∏ i, X (p i) (some (e i)))*tax p e = (W (total p e):ℚ) by
    rw [tax,←prod_mul_distrib,wp]; push_cast
    exact prod_congr rfl fun i _ => x_factor (hp i) (e i),
    show (∏ i, Y (p i) (some (e i)))*tax p e = (σ 1 (total p e):ℚ) by
      rw [tax,←prod_mul_distrib,sp]; push_cast
      exact prod_congr rfl fun i _ => y_factor (hp i) (e i),factors]
  linarith only [balanced]

end General

theorem score_of_eq (e : I → ℕ)
    (heq : OeisA245212.a (number e)=(σ 1 (number e) : ℤ)) : score e=2 :=
  normalized_of_eq prime prime_prime different e heq

end OMA.Smooth245212

end

section

/- A uniform abundancy obstruction and the exclusion of constant
prime-exponent families in the A245212 divisor equality. -/
namespace OMA.Abundance245212
open OMA.Smooth245212 Finset ArithmeticFunction Nat
open scoped ArithmeticFunction.sigma

private theorem twice_weighted {p : ℕ} (hp : 1≤p) (e : ℕ) :
    (e+1)*(p^e+∑ i∈range (e+1),p^i) ≤
      2*(∑ i∈range (e+1),p^i*(i+1)) := by
  induction e with
  | zero => simp
  | succ e ih =>
    have bound : (∑ i∈range (e+1), p^i) ≤ (e+1)*p^e := by
      calc
        _ ≤ ∑ _i∈range (e+1),p^e := sum_le_sum (fun i hi =>
          Nat.pow_le_pow_right hp (by have := mem_range.mp hi; omega))
        _ = _ := by simp
    rw [sum_range_succ _ (e+1),sum_range_succ _ (e+1)]
    linarith only [ih,bound]

theorem square_bound (n : ℕ) : (σ 0 n)^2*n*(σ 1 n) ≤ (W n)^2 := by
  induction n using Nat.recOnPrimeCoprime with
  | zero => simp
  | prime_pow p e hp =>
    rw [sigma_zero_apply_prime_pow hp,sigma_one_apply_prime_pow hp,w_pow hp]
    have h := twice_weighted hp.pos e
    have hs := Nat.pow_le_pow_left h 2
    have am (u v : ℕ) : 4*u*v ≤ (u+v)^2 := by
      zify; nlinarith only [sq_nonneg ((u:ℤ)-v)]
    have haux := Nat.mul_le_mul_left ((e+1)^2) (am (p^e) (∑ i∈range (e+1),p^i))
    linarith only [haux,hs]
  | coprime a b _ _ cop ia ib =>
    rw [isMultiplicative_sigma.map_mul_of_coprime cop,
      isMultiplicative_sigma.map_mul_of_coprime cop,w_mult.map_mul_of_coprime cop]
    simpa only [mul_pow,mul_assoc,mul_left_comm,mul_comm] using Nat.mul_le_mul ia ib

theorem balance {n : ℕ} (hn : n≠0)
    (eq : OeisA245212.a n=(σ 1 n:ℤ)) : W n+σ 1 n=2*n*(σ 0 n) := by
  have total : W n = n*n.divisors.card+∑ d∈n.properDivisors,d*d.divisors.card := by
    calc
      _ = ∑ d∈insert n n.properDivisors,d*d.divisors.card := by
        rw [Nat.insert_self_properDivisors hn,w_apply]
      _ = _ := sum_insert Nat.self_notMem_properDivisors
  unfold OeisA245212.a at eq
  zify at total ⊢
  simp only [sigma_zero_apply]
  linarith

theorem sigma_lt {n : ℕ} (hn : n≠0)
    (eq : OeisA245212.a n=(σ 1 n:ℤ)) : σ 1 n<4*n := by
  have tpos : 0<σ 0 n := by
    rw [sigma_zero_apply,card_pos]; exact ⟨n,Nat.mem_divisors_self _ hn⟩
  have spos : 0<σ 1 n := by
    rw [sigma_one_apply]; exact sum_pos' (fun _ _ => by omega)
      ⟨n,Nat.mem_divisors_self _ hn,by omega⟩
  have bal := balance hn eq
  have ww : W n < 2*n*(σ 0 n) := by omega
  have strict := (square_bound n).trans_lt (Nat.pow_lt_pow_left ww (by decide : 2≠0))
  by_contra! ge
  have bad := Nat.mul_le_mul_left ((σ 0 n)^2*n) ge
  linarith only [bad,strict]

private theorem tau_gt_one {n : ℕ} (h : 1<n) : 1<σ 0 n := by
  rw [sigma_zero_apply]
  have hs : ({1,n}:Finset ℕ) ⊆ n.divisors := by
    intro d hd; simp only [mem_insert,mem_singleton] at hd
    rcases hd with rfl|rfl
    · exact one_mem_divisors.mpr (by omega)
    · exact mem_divisors_self _ (by omega)
  have := card_le_card hs
  have hc : 2≤n.divisors.card := by simpa [h.ne] using this
  omega

private theorem sigma_lt_twice_of_prime_tau (n : ℕ) :
    Nat.Prime (σ 0 n) → σ 1 n < 2*n := by
  induction n using Nat.recOnPrimeCoprime with
  | zero => simp
  | prime_pow p e hp =>
    intro ht; clear ht; rw [sigma_one_apply_prime_pow hp]
    induction e with
    | zero => simp
    | succ e ih =>
      rw [sum_range_succ _ (e+1),pow_succ]
      have hh := Nat.mul_le_mul_left (p^e) hp.two_le
      omega
  | coprime a b ha hb cop _ _ =>
    rw [isMultiplicative_sigma.map_mul_of_coprime cop]
    intro h
    rcases Nat.prime_mul_iff.mp h with ⟨_,h⟩|⟨_,h⟩
    · have := tau_gt_one hb; omega
    · have := tau_gt_one ha; omega

theorem no_resonance {m p : ℕ} (hm : m≠0) (hp : Nat.Prime p) (cop : ¬p∣m)
    (eq : OeisA245212.a m=(σ 1 m:ℤ)) (resonant : p*(σ 1 m)=2*m*(σ 0 m)) :
    p=2 ∧ m=1 := by
  by_cases p2 : p=2
  · subst p; refine ⟨rfl,?_⟩
    by_contra! more
    have s : σ 1 m < (σ 0 m)*m := by
      rw [sigma_one_apply,sigma_zero_apply]
      calc
        _ < ∑ _i∈m.divisors,m := sum_lt_sum
          (fun i hi => le_of_dvd (by omega) (dvd_of_mem_divisors hi))
          ⟨1,one_mem_divisors.mpr hm,by omega⟩
        _ = _ := by simp
    linarith only [s,resonant]
  · have p2nd : ¬p∣2 := fun h => p2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
    have hdiv : p ∣ 2*m*(σ 0 m) := resonant ▸ dvd_mul_right _ _
    obtain ⟨k,hk⟩ := (hp.dvd_mul.mp hdiv).resolve_left
      (fun f => (hp.dvd_mul.mp f).elim p2nd cop)
    have can : p*(σ 1 m) = p*(2*m*k) := by rw [resonant,hk]; ring
    have sm := Nat.eq_of_mul_eq_mul_left hp.pos can
    have low := sigma_lt hm eq
    have tpos : 0<σ 0 m := by
      rw [sigma_zero_apply,Finset.card_pos]; exact ⟨m,mem_divisors_self _ hm⟩
    have k0 : 0<k := by by_contra! hz; simp [show k=0 by omega] at hk; omega
    have k1 : k=1 := by
      by_contra! h; have large := Nat.mul_le_mul_left (2*m) (show 2≤k by omega)
      linarith only [low,sm,large]
    rw [k1,mul_one] at hk sm
    have hlt := sigma_lt_twice_of_prime_tau m (hk ▸ hp)
    omega

theorem eq_of_balance {n : ℕ} (hn : n≠0) (bal : W n+σ 1 n=2*n*(σ 0 n)) :
    OeisA245212.a n=(σ 1 n:ℤ) := by
  have total : W n = n*n.divisors.card+∑ d∈n.properDivisors,d*d.divisors.card := by
    calc
      _ = ∑ d∈insert n n.properDivisors,d*d.divisors.card := by
        rw [Nat.insert_self_properDivisors hn,w_apply]
      _ = _ := sum_insert Nat.self_notMem_properDivisors
  rw [sigma_zero_apply] at bal
  unfold OeisA245212.a
  zify at total bal
  linarith

theorem affine_of_eq {p m e : ℕ} (hm : m≠0) (hp : Nat.Prime p) (cop : ¬p∣m)
    (eq : OeisA245212.a (m*p^e)=(σ 1 (m*p^e):ℤ)) :
    (W m:ℚ)*X p (some e)+(σ 1 m:ℚ)*Y p (some e)=2*m*(σ 0 m:ℚ) := by
  have cb := ((hp.coprime_iff_not_dvd.mpr cop).pow_left e).symm
  have bal := balance (mul_ne_zero hm (pow_ne_zero _ hp.ne_zero)) eq
  rw [w_mult.map_mul_of_coprime cb,isMultiplicative_sigma.map_mul_of_coprime cb,
    isMultiplicative_sigma.map_mul_of_coprime cb,sigma_zero_apply_prime_pow hp] at bal
  have cast : (W m:ℚ)*(W (p^e):ℚ)+(σ 1 m:ℚ)*(σ 1 (p^e):ℚ)=
      2*(m*(p:ℚ)^e)*((σ 0 m:ℚ)*((e:ℚ)+1)) := by exact_mod_cast bal
  have z : ((e:ℚ)+1)*(p:ℚ)^e ≠ 0 := mul_ne_zero (by positivity)
    (pow_ne_zero _ (by exact_mod_cast hp.ne_zero))
  apply mul_right_cancel₀ z
  rw [add_mul,mul_assoc,mul_assoc (σ 1 m:ℚ),x_factor hp e,y_factor hp e]
  linarith only [cast]

theorem y_strict {p : ℕ} (hp : 1<p) : StrictAnti (fun e : ℕ => Y p (some e)) := by
  have pp : (1:ℚ)<p := by exact_mod_cast hp
  have pos : 0<(p:ℚ)⁻¹ := by positivity
  have lt := inv_lt_one_of_one_lt₀ pp
  apply strictAnti_nat_of_succ_lt
  intro e
  simp only [y_avg hp,Nat.cast_add,Nat.cast_one]
  rw [sum_range_succ _ (e+1),div_lt_div_iff₀ (by positivity) (by positivity)]
  have small : (∑ _i ∈ range (e+1), (p:ℚ)⁻¹^(e+1)) < ∑ i∈range (e+1), (p:ℚ)⁻¹^i :=
    sum_lt_sum_of_nonempty (by simp) (fun _ hi =>
      pow_right_strictAnti₀ pos lt (mem_range.mp hi))
  simp only [sum_const,card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one] at small
  linarith only [small]

theorem unique_exponent {p m e f : ℕ} (hm : m≠0) (hp : Nat.Prime p) (cop : ¬p∣m)
    (he : OeisA245212.a (m*p^e)=(σ 1 (m*p^e):ℤ))
    (hf : OeisA245212.a (m*p^f)=(σ 1 (m*p^f):ℤ)) :
    e=f ∨ p=2 ∧ m=1 := by
  by_cases ef : e=f
  · exact Or.inl ef
  refine Or.inr ?_
  have ee := affine_of_eq hm hp cop he
  have ff := affine_of_eq hm hp cop hf
  have ne := (y_strict hp.one_lt).injective.ne ef
  have pp : (p:ℚ) ≠ 1 := by exact_mod_cast hp.ne_one
  unfold X at ee ff
  field_simp [sub_ne_zero.mpr pp] at ee ff
  have coeff : ((σ 1 m:ℚ)*((p:ℚ)-1)-(W m:ℚ)) *
      (Y p (some e)-Y p (some f))=0 := by linear_combination ee-ff
  have w := (mul_eq_zero.mp coeff).resolve_right (sub_ne_zero.mpr ne)
  have res : (p:ℚ)*(σ 1 m:ℚ)=2*m*(σ 0 m:ℚ) := by
    apply mul_right_cancel₀ (sub_ne_zero.mpr pp)
    linear_combination ee+w*((p:ℚ)-Y p (some e))
  apply no_resonance hm hp cop _ (by exact_mod_cast res)
  apply eq_of_balance hm
  exact_mod_cast (show (W m:ℚ)+(σ 1 m:ℚ)=2*m*(σ 0 m:ℚ) by linarith only [w,res])

end OMA.Abundance245212

end

section

/- Every prime-power divisor of an A245212 solution divides a nonzero
combination of the two divisor moments of its coprime cofactor. -/
namespace OMA.PrimePowerDiv245212
open Finset ArithmeticFunction OMA.Smooth245212 OMA.Abundance245212
open scoped ArithmeticFunction.sigma

theorem weighted {p : ℕ} (hp : p.Prime) (e : ℕ) :
    (p-1)*W (p^e)+σ 1 (p^e)=p*((e+1)*p^e) := by
  rw [w_pow hp,sigma_one_apply_prime_pow hp]
  induction e with
  | zero => simp; have := hp.one_lt; omega
  | succ e ih =>
    rw [sum_range_succ _ (e+1),sum_range_succ _ (e+1),mul_add,pow_succ]
    have add := Nat.sub_add_cancel (show 1≤p from hp.pos)
    nlinarith only [ih,congrArg (fun z:ℕ => z*(p^e*p)*(e+2)) add]

theorem power_divides {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (cop : m.Coprime p) (e : ℕ)
    (eq : OeisA245212.a (m*p^e)=(σ 1 (m*p^e):ℤ)) :
    (p:ℤ)^e ∣ (W m:ℤ)-((p:ℤ)-1)*(σ 1 m:ℤ) := by
  have van : (p:ZMod (p^e))^e=0 := by rw [←Nat.cast_pow]; exact ZMod.natCast_self _
  have w := congrArg (fun n : ℕ => (n:ZMod (p^e))) (weighted hp e)
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_sub hp.pos,Nat.cast_one,Nat.cast_pow,van,
    mul_zero] at w
  have s : ((p:ZMod (p^e))-1)*(σ 1 (p^e):ℕ) = -1 := by
    rw [sigma_one_apply_prime_pow hp]
    simp only [Nat.cast_sum,Nat.cast_pow]
    rw [mul_comm,geom_sum_mul,pow_succ,van,zero_mul,zero_sub]
  have b := balance (mul_ne_zero hm.ne' (pow_ne_zero _ hp.ne_zero)) eq
  rw [w_mult.map_mul_of_coprime (cop.pow_right e),
    isMultiplicative_sigma.map_mul_of_coprime (cop.pow_right e)] at b
  have bb := congrArg (fun n : ℕ => (n:ZMod (p^e))) b
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,van,mul_zero,zero_mul] at bb
  rw [←Nat.cast_pow]
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p^e)).mp
  push_cast
  linear_combination ((p:ZMod (p^e))-1)^2*bb - (W m:ZMod (p^e))*((p:ZMod (p^e))-1)*w +
    ((W m:ZMod (p^e))-((p:ZMod (p^e))-1)*(σ 1 m:ZMod (p^e)))*s

theorem nonzero {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hp2 : p≠2)
    (cop : m.Coprime p) (e : ℕ) (eq : OeisA245212.a (m*p^e)=(σ 1 (m*p^e):ℤ)) :
    (W m:ℤ)-((p:ℤ)-1)*(σ 1 m:ℤ)≠0 := by
  intro zero
  have same : W m=(p-1)*(σ 1 m) := by
    apply Nat.cast_inj (R:=ℤ) |>.mp
    push_cast [Nat.cast_sub hp.pos]; omega
  have b := balance (mul_ne_zero hm.ne' (pow_ne_zero _ hp.ne_zero)) eq
  rw [w_mult.map_mul_of_coprime (cop.pow_right e),
    isMultiplicative_sigma.map_mul_of_coprime (cop.pow_right e),
    isMultiplicative_sigma.map_mul_of_coprime (cop.pow_right e),
    sigma_zero_apply_prime_pow hp,same] at b
  have t := congrArg (fun v:ℕ => v*(σ 1 m)) (weighted hp e)
  have v : (p*(σ 1 m))*((e+1)*p^e)=(2*m*(σ 0 m))*((e+1)*p^e) := by
    nlinarith only [b,t]
  have res := Nat.eq_of_mul_eq_mul_right (show 0<(e+1)*p^e by have := hp.pos; positivity) v
  have mb : W m+σ 1 m=2*m*(σ 0 m) := by
    rw [←res,same]
    nlinarith only [congrArg (fun v:ℕ => v*(σ 1 m)) (Nat.sub_add_cancel hp.pos)]
  exact hp2 (no_resonance hm.ne' hp (hp.coprime_iff_not_dvd.mp cop.symm)
    (eq_of_balance hm.ne' mb) res).1

theorem cofactor_bound {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hp2 : p≠2)
    (cop : m.Coprime p) (e : ℕ) (eq : OeisA245212.a (m*p^e)=(σ 1 (m*p^e):ℤ)) :
    p^e ≤ ((W m:ℤ)-((p:ℤ)-1)*(σ 1 m:ℤ)).natAbs := by
  have d := power_divides hm hp cop e eq
  have nz := nonzero hm hp hp2 cop e eq
  apply Nat.le_of_dvd (Int.natAbs_pos.mpr nz)
  simpa using Int.natAbs_dvd_natAbs.mpr d

end OMA.PrimePowerDiv245212

end

section

/- Rational approximations to the two local divisor moments.  Their errors
are exactly opposite in sign, in the ratio one to p-1. -/
namespace OMA.Height245212
open OMA.Smooth245212 Finset

def den (p e : ℕ) : ℕ := (e+1)*(p-1)^2
def err (p e : ℕ) : ℚ := 1 / ((den p e : ℚ)*(p:ℚ)^e)
def yr (p e : ℕ) : ℚ := p / (((p:ℚ)-1)*(e+1))
def xr (p e : ℕ) : ℚ := 1+(1-yr p e)/((p:ℚ)-1)

theorem den_pos {p : ℕ} (hp : 1<p) (e : ℕ) : 0<den p e := by
  unfold den; exact Nat.mul_pos (by omega) (pow_pos (by omega) _)

theorem err_pos {p : ℕ} (hp : 1<p) (e : ℕ) : 0<err p e := by
  have hd : (0:ℚ)<den p e := by exact_mod_cast den_pos hp e
  have pp : (0:ℚ)<p := by exact_mod_cast (by omega : 0<p)
  unfold err; positivity

theorem localY {p : ℕ} (hp : 1<p) (e : ℕ) :
    Y p (some e)=yr p e-((p:ℚ)-1)*err p e := by
  have pp : (1:ℚ)<p := by exact_mod_cast hp
  have p0 : (p:ℚ)≠0 := by linarith
  have p1 : (p:ℚ)-1≠0 := by linarith
  have inv1 : (p:ℚ)⁻¹-1≠0 := sub_ne_zero.mpr (inv_lt_one_of_one_lt₀ pp).ne
  have flip : (1:ℚ)-p≠0 := by linarith
  simp only [Y,yr,err,den,Nat.cast_mul,Nat.cast_add,Nat.cast_one,
    Nat.cast_pow,Nat.cast_sub (by omega : 1≤p),inv_pow,pow_succ (p:ℚ) e]
  field_simp
  ring_nf

theorem localX {p : ℕ} (hp : 1<p) (e : ℕ) :
    X p (some e)=xr p e+err p e := by
  have pp : (1:ℚ)<p := by exact_mod_cast hp
  rw [X,localY hp,xr]
  field_simp [sub_ne_zero.mpr pp.ne']; ring

theorem y_range {p e : ℕ} (hp : 1<p) (he : 0<e) :
    0≤ yr p e ∧ yr p e≤1 ∧ yr p e*((e:ℚ)+1)≤2 := by
  have pp : (2:ℚ)≤p := by exact_mod_cast (by omega : 2≤p)
  have ee : (1:ℚ)≤e := by exact_mod_cast he
  have pos : 0<((p:ℚ)-1)*((e:ℚ)+1) := mul_pos (by linarith) (by positivity)
  unfold yr
  refine ⟨div_nonneg (by positivity) pos.le,(div_le_iff₀ pos).mpr ?_,?_⟩
  · nlinarith only [mul_nonneg (sub_nonneg.mpr ee) (show 0≤(p:ℚ)-1 by linarith),pp]
  · rw [div_mul_eq_mul_div,div_le_iff₀ pos]
    nlinarith only [mul_nonneg (sub_nonneg.mpr pp) (show 0≤(e:ℚ)+1 by positivity)]

theorem x_range {p e : ℕ} (hp : 1<p) (he : 0<e) :
    1≤xr p e ∧ X p (some e)≤2 := by
  have pp : (2:ℚ)≤p := by exact_mod_cast (by omega : 2≤p)
  have dp : 0<(p:ℚ)-1 := by linarith
  constructor
  · exact le_add_of_nonneg_right (div_nonneg (sub_nonneg.mpr (y_range hp he).2.1) dp.le)
  · have bd : (1-Y p (some e))/((p:ℚ)-1)≤1 :=
      (div_le_iff₀ dp).mpr (by linarith only [pp,y_nonneg hp (some e)])
    unfold X; linarith

theorem rounded_integers {p : ℕ} (hp : 1<p) (e : ℕ) :
    ∃ u v : ℤ, (u:ℚ)=xr p e*den p e ∧ (v:ℚ)=yr p e*den p e := by
  have pp : (1:ℚ)<p := by exact_mod_cast hp
  refine ⟨(p:ℤ)*(((p:ℤ)-1)*((e:ℤ)+1)-1),(p:ℤ)*((p:ℤ)-1),?_,?_⟩
  all_goals
    simp only [xr,yr,den]; push_cast [Nat.cast_sub (by omega : 1≤p)]
    field_simp [sub_ne_zero.mpr pp.ne'] <;> ring

end OMA.Height245212

end

section

/- Recover the exponent of an odd prime power exactly from the prime
and its coprime cofactor in an A245212 solution. The previously known
uniqueness theorem does not provide this floor or its exact error. -/
namespace OMA.ReverseDigit245212
open OMA.Smooth245212 OMA.Abundance245212 OMA.Height245212
open scoped ArithmeticFunction.sigma

def numerator (p A S : ℚ) := p*((p-1)*S-A)
def denominator (p A T : ℚ) := (p-1)*(2*T*(p-1)-p*A)

private theorem y_closed {p : ℕ} (hp : 1<p) (e : ℕ) :
    Y p (some e)*(((e:ℚ)+1)*((p:ℚ)-1)*(p:ℚ)^(e+1)) =
      (p:ℚ)*((p:ℚ)^(e+1)-1) := by
  have hpp : (1:ℚ)<p := by exact_mod_cast hp
  rw [localY hp]
  simp only [yr,err,den,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_pow,
    Nat.cast_sub (by omega : 1≤p),pow_succ (p:ℚ) e]
  field_simp [show (p:ℚ)-1≠0 by linarith,show (p:ℚ)≠0 by linarith,
    show (e:ℚ)+1≠0 by positivity]

/-- The signed identity is valid even when either coefficient vanishes. -/
theorem identity {p e : ℕ} (hp : 1<p) {A S T : ℚ}
    (balance : A*X p (some e)+S*Y p (some e)=2*T) :
    numerator p A S*((p:ℚ)^(e+1)-1)=denominator p A T*((e:ℚ)+1)*(p:ℚ)^(e+1) := by
  have hpp : (1:ℚ)<p := by exact_mod_cast hp
  unfold X at balance
  field_simp [(show (p:ℚ)-1≠0 by linarith)] at balance
  have y:=y_closed hp e
  unfold numerator denominator
  linear_combination (((e:ℚ)+1)*((p:ℚ)-1)*(p:ℚ)^(e+1))*balance -
    (((p:ℚ)-1)*S-A)*y

private theorem grows {p : ℕ} (hp : 3≤p) (e : ℕ) : e+2<p^(e+1) := by
  induction e with
  | zero => simpa using (show 2<p by omega)
  | succ e ih => rw [pow_succ p (e+1)];nlinarith

/-- For an odd prime the reverse base-p digit is an ordinary floor:
the signed ratio exceeds e+1 by exactly (e+1)/(p^(e+1)-1). -/
theorem recover {p m e : ℕ} (hm : 0 < m) (hp : p.Prime) (odd : p≠2) (cop : m.Coprime p)
    (eq : OeisA245212.a (m*p^e)=(σ 1 (m*p^e):ℤ)) :
    let C:=numerator p (W m) (σ 1 m)
    let D:=denominator p (W m) (m*(σ 0 m:ℚ))
    D≠0 ∧ C/D=((e:ℚ)+1)+((e:ℚ)+1)/((p:ℚ)^(e+1)-1) ∧
      ⌊C/D⌋=(e:ℤ)+1 := by
  let C:=numerator p (W m) (σ 1 m)
  let D:=denominator p (W m) (m*(σ 0 m:ℚ))
  have bal:=affine_of_eq hm.ne' hp (hp.coprime_iff_not_dvd.mp cop.symm) eq
  have exactId : C*((p:ℚ)^(e+1)-1)=D*((e:ℚ)+1)*(p:ℚ)^(e+1) :=
    identity hp.one_lt (by simpa only [mul_assoc] using bal)
  have nonzero:=OMA.PrimePowerDiv245212.nonzero hm hp odd cop e eq
  have nQ : (W m:ℚ)-((p:ℚ)-1)*(σ 1 m:ℚ)≠0 := by exact_mod_cast nonzero
  have cne : C≠0 := mul_ne_zero (Nat.cast_ne_zero.mpr hp.ne_zero) (sub_ne_zero.mpr
    (sub_ne_zero.mp nQ).symm)
  have big0:=grows (p:=p) (by have:=hp.two_le;omega) e
  have big : (e:ℚ)+2 < (p:ℚ)^(e+1) := by exact_mod_cast big0
  have pos : 0<(p:ℚ)^(e+1)-1 := by linarith [Nat.cast_nonneg (α:=ℚ) e]
  have dne : D≠0 := by
    intro z;rw [z,zero_mul,zero_mul] at exactId
    exact (mul_ne_zero cne pos.ne') exactId
  have ratio : C/D=((e:ℚ)+1)+((e:ℚ)+1)/((p:ℚ)^(e+1)-1) := by
    field_simp [dne,pos.ne']
    linear_combination exactId
  refine ⟨dne,ratio,?_⟩
  change ⌊C/D⌋=_
  rw [ratio,Int.floor_eq_iff]
  push_cast
  have lo : 0≤((e:ℚ)+1)/((p:ℚ)^(e+1)-1) := div_nonneg (by positivity) pos.le
  have hi : ((e:ℚ)+1)/((p:ℚ)^(e+1)-1)<1 := (div_lt_one pos).mpr (by linarith)
  constructor <;> linarith

end OMA.ReverseDigit245212

end

section

/- Recover an odd prime exponent in OEIS A245212 from the denominator
of the signed cofactor ratio. -/
namespace OMA.ReverseOrder245212
open OMA.Smooth245212 OMA.ReverseDigit245212 OMA.RepunitOrder245212
open scoped ArithmeticFunction.sigma

/-- The exact dyadic-style denominator filter applies also to odd prime
multipliers. In exponents at least two, only its odd prime divisors matter. -/
theorem recover {p m e : ℕ} (hm : 0 < m) (hp : p.Prime) (odd : p ≠ 2) (cop : m.Coprime p)
    (eq : OeisA245212.a (m*p^e)=(σ 1 (m*p^e):ℤ)) :
    let C:=numerator p (W m) (σ 1 m)
    let D:=OMA.ReverseDigit245212.denominator p (W m) (m*(σ 0 m:ℚ))
    let y:=(C/D).den
    y=Q p (e+1) ∧ readIndex p y=e+1 ∧
      (2≤e → (y.primeFactors.filter (·≠2)).lcm (ord p)=e+1) := by
  dsimp only
  obtain ⟨_,ratio,_⟩:=OMA.ReverseDigit245212.recover hm hp odd cop eq
  have den := OMA.RepunitOrder245212.denominator (t:=e+1) hp.two_le (by omega)
  push_cast at den
  rw [ratio,den]
  exact ⟨rfl,read_all hp.two_le (by omega),fun bound=>reduced_recover hp.two_le (by omega)⟩

end OMA.ReverseOrder245212

end

#print axioms OMA.ReverseOrder245212.recover
