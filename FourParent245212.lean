import OMAReductions.R_OeisA245212_conjecture_R1_H1_R1_H2_R1
import Mathlib.Tactic
import Mathlib.Data.Nat.Log

/-! Restricting the four-odd-prime A245212 case to bounded prime supports. -/

namespace OMA.R_OeisA245212_conjecture_R1_H1_R1_H2_R1_H2_R1

open Finset
open scoped ArithmeticFunction.sigma

/-- The prime support of any four-prime solution beginning with three lies
in this explicit range, independently of its exponents. -/
def H1 : Prop :=
  ∀ k p q r e f g : ℕ, 2 ≤ k → p.Prime → q.Prime → r.Prime →
    5 ≤ p → p < q → q < r → 0 < e → 0 < f → 0 < g →
    let n := 3^k*p^e*q^f*r^g
    OeisA245212.a n = (σ 1 n : ℤ) →
      p ∈ ({5,7} : Finset ℕ) ∧ q ≤ 31 ∧ r < 1000000000000000000

/-- Exclude the surviving bounded prime supports, with arbitrary positive exponents. -/
def H2 : Prop :=
  ∀ p ∈ ({5,7} : Finset ℕ), ∀ q ∈ Icc (p+1) 31,
    ∀ r ∈ Icc (q+1) 999999999999999999, q.Prime → r.Prime →
    ∀ k e f g : ℕ, 2 ≤ k → 0 < e → 0 < f → 0 < g →
    let n := 3^k*p^e*q^f*r^g
    2*n.totient < n → OeisA245212.a n ≠ (σ 1 n : ℤ)

theorem main : H1 → H2 → OMA.R_OeisA245212_conjecture_R1_H1_R1_H2_R1.H2 := by
  intro bound remaining k p q r e f g hk hp hq hr hp5 pq qr he hf hg n ht eq
  obtain ⟨p57, qs, rs⟩ := bound k p q r e f g hk hp hq hr hp5 pq qr he hf hg eq
  exact remaining p p57 q (mem_Icc.mpr ⟨pq, qs⟩) r (mem_Icc.mpr ⟨qr, by omega⟩)
    hq hr k e f g hk he hf hg ht eq
end OMA.R_OeisA245212_conjecture_R1_H1_R1_H2_R1_H2_R1
/- Four-prime exclusion for odd solutions of the OEIS A245212 divisor identity.
The proof bounds the four exponents, covers ten possible smallest-prime supports,
and verifies the interval, divisibility and exponent cuts on every branch. -/

namespace OMA.HeightLog245212

/-- The positive integer bit-length (also used for zero as an upper bound). -/
def bits (n : ℕ) := Nat.log 2 n+1
def slope (k : ℕ) := k*2^k
def offset (k B : ℕ) := 2^k*(k+bits k+(2*k+1+2*B)*bits B)
def start (k B : ℕ) := max (256*(slope k)^2) (2*offset k B+1)
def step (k B t : ℕ) := offset k B+slope k*bits t

private theorem upper (n : ℕ) : n+1≤2^bits n := Nat.lt_pow_succ_log_self (by decide : 1<2) n

private theorem bit_square {n : ℕ} (hn : 0<n) : (bits n)^2≤4*n := by
  have all (j : ℕ) : (j+1)^2≤4*2^j := by
    rcases j with _|_|j
    · decide
    · decide
    · induction j with
      | zero => decide
      | succ j ih =>
        rw [pow_succ 2]
        nlinarith only [ih,sq_nonneg (j:ℤ),Nat.zero_le j]
  exact (all (Nat.log 2 n)).trans (Nat.mul_le_mul_left 4 (Nat.pow_log_le_self 2 hn.ne'))

theorem self_bound {k B E : ℕ}
    (power : 2^E≤(B^(2*B)*(k*2^k*B^(2*k+1)*(E+1)^k))^(2^k-1)) :
    E ≤ step k B E := by
  have b := (Nat.le_succ B).trans (upper B)
  have h := (Nat.le_succ k).trans (upper k)
  let L := k+bits k+(2*k+1+2*B)*bits B+k*bits E
  have c : B^(2*B)*(k*2^k*B^(2*k+1)*(E+1)^k)≤2^L := by
    calc _ ≤ (2^bits B)^(2*B)*((2^bits k)*2^k*(2^bits B)^(2*k+1)*(2^bits E)^k) := by
               gcongr
               exact upper E
         _ = 2^L := by simp only [←pow_mul,←pow_add]; congr 1; dsimp only [L];ring
  have z := (Nat.pow_le_pow_left c (2^k-1)).trans (Nat.pow_le_pow_right (by positivity : 0<2^L)
    (Nat.sub_le (2^k) 1))
  have est := power.trans z
  rw [←pow_mul] at est
  have out := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp est
  convert out using 1
  dsimp [step,offset,slope,L];ring

theorem refinement {k B E : ℕ} (self : E ≤ step k B E) {t : ℕ} (prev : E≤t) : E ≤ step k B t := by
  exact self.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.add_le_add_right
    (Nat.log_mono_right prev) 1)) _)

theorem initial {k B E : ℕ} (pos : 0<E) (self : E ≤ step k B E) : E ≤ start k B := by
  by_contra! bad
  have s : 256*slope k^2<E := (le_max_left ..).trans_lt bad
  have a : 2*offset k B+1<E := (le_max_right ..).trans_lt bad
  have small : 2*slope k*bits E≤E := by
    by_cases h : bits E≤16*slope k
    · have t := Nat.mul_le_mul_left (2*slope k) h
      nlinarith only [t,s,sq_nonneg (slope k:ℤ)]
    · have t := Nat.mul_le_mul_right (bits E) (show 16*slope k≤bits E by omega)
      have bs := bit_square pos
      nlinarith only [t,bs,Nat.zero_le (slope k*bits E)]
  change E≤offset k B+slope k*bits E at self
  nlinarith only [small,self,a]


/-- The decreasing loop in exponent_ceiling: iterate until another round
    no longer improves the upper endpoint. -/
def settle (k B t : ℕ) : ℕ :=
  if _h : step k B t<t then settle k B (step k B t) else t
termination_by t

def ceiling (k B : ℕ) := settle k B (start k B)

theorem settle_bound {k B E t : ℕ} (self : E ≤ step k B E) (ht : E≤t) :
    E ≤ settle k B t := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    rw [settle]
    split_ifs with h
    · exact ih _ h (refinement self ht)
    · exact ht

theorem bound {k B E : ℕ} (pos : 0<E)
    (power : 2^E≤(B^(2*B)*(k*2^k*B^(2*k+1)*(E+1)^k))^(2^k-1)) : E≤ceiling k B :=
  settle_bound (self_bound power) (initial pos (self_bound power))

theorem four {B E : ℕ} (pos : 0<E)
    (power : 2^E≤(B^(2*B)*(64*B^9*(E+1)^4))^15) : E≤ceiling 4 B :=
  bound pos power

end OMA.HeightLog245212

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


end OMA.Smooth245212

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


end OMA.Smooth245212

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


end OMA.Abundance245212

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

namespace OMA.Height245212
open OMA.Smooth245212 Finset
open scoped ArithmeticFunction.sigma

noncomputable section
variable (p e : Fin 4 → ℕ)
def xm (s : Finset (Fin 4)) (i : Fin 4) : ℚ :=
  if i∈s then xr (p i) (e i) else X (p i) (some (e i))
def ym (s : Finset (Fin 4)) (i : Fin 4) : ℚ :=
  if i∈s then yr (p i) (e i) else Y (p i) (some (e i))
def scoreM (s : Finset (Fin 4)) : ℚ := (∏ i,xm p e s i)+∏ i,ym p e s i
def localDen (s : Finset (Fin 4)) (i : Fin 4) : ℕ :=
  if i∈s then den (p i) (e i) else (e i+1)*p i^e i
def commonDen (s : Finset (Fin 4)) : ℕ := ∏ i,localDen p e s i

theorem integral (prime : ∀ i,(p i).Prime) (s : Finset (Fin 4)) :
    ∃ z : ℤ, (z:ℚ)=scoreM p e s*commonDen p e s := by
  have ints (i : Fin 4) : ∃ u v : ℤ,
      (u:ℚ)=xm p e s i*localDen p e s i ∧ (v:ℚ)=ym p e s i*localDen p e s i := by
    by_cases h : i∈s
    · simpa [xm,ym,localDen,h] using rounded_integers (prime i).one_lt (e i)
    · refine ⟨(W (p i^e i):ℕ),(σ 1 (p i^e i):ℕ),?_,?_⟩
      · simpa [xm,localDen,h] using (x_factor (prime i) (e i)).symm
      · simpa [ym,localDen,h] using (y_factor (prime i) (e i)).symm
  choose u v hu hv using ints
  refine ⟨(∏ i,u i)+∏ i,v i,?_⟩
  simp only [scoreM, commonDen,Int.cast_add,Int.cast_prod,Nat.cast_prod,hu,hv,
    prod_mul_distrib,add_mul]

theorem difference (great : ∀ i,1<p i) {s : Finset (Fin 4)} {i : Fin 4} (hi : i∉s) :
    scoreM p e s-scoreM p e (insert i s)=err (p i) (e i)*
      ((∏ j∈univ.erase i,xm p e s j)-((p i:ℚ)-1)*(∏ j∈univ.erase i,ym p e s j)) := by
  have extx : (∏ j∈univ.erase i,xm p e (insert i s) j)=∏ j∈univ.erase i,xm p e s j :=
    prod_congr rfl fun j hj => by simp [xm,(mem_erase.mp hj).1]
  have exty : (∏ j∈univ.erase i,ym p e (insert i s) j)=∏ j∈univ.erase i,ym p e s j :=
    prod_congr rfl fun j hj => by simp [ym,(mem_erase.mp hj).1]
  unfold scoreM
  rw [←prod_erase_mul _ (xm p e s) (mem_univ i),←prod_erase_mul _ (ym p e s) (mem_univ i),
    ←prod_erase_mul _ (xm p e (insert i s)) (mem_univ i),
    ←prod_erase_mul _ (ym p e (insert i s)) (mem_univ i),extx,exty]
  simp only [xm,ym,hi,if_false,mem_insert_self,if_true,localX (great i),localY (great i)]
  ring

theorem mixed_range (great : ∀ i,1<p i) (pos : ∀ i,0<e i) (s : Finset (Fin 4)) (i : Fin 4) :
    1≤xm p e s i ∧ xm p e s i≤2 ∧ 0≤ym p e s i ∧ ym p e s i≤1 ∧ ym p e s i≤yr (p i) (e i) := by
  have yb := y_range (great i) (pos i)
  have xb := x_range (great i) (pos i)
  have er := err_pos (great i) (e i)
  have pp : (1:ℚ)<p i := by exact_mod_cast great i
  have xle : xr (p i) (e i)≤X (p i) (some (e i)) := by rw [localX (great i)]; linarith
  have yle : Y (p i) (some (e i))≤yr (p i) (e i) := by
    rw [localY (great i)]; exact sub_le_self _ (mul_nonneg (by linarith) er.le)
  by_cases h : i∈s
  · simp only [xm,ym,h,if_true]
    exact ⟨xb.1,xle.trans xb.2,yb.1,yb.2.1,le_rfl⟩
  · simp only [xm,ym,h,if_false]
    exact ⟨xb.1.trans xle,xb.2,y_nonneg (great i) _,y_one (great i) _,yle⟩

theorem coefficient (great : ∀ i,1<p i) (pos : ∀ i,0<e i)
    (s : Finset (Fin 4)) (i : Fin 4) :
    let xx := ∏ j∈univ.erase i,xm p e s j
    let yy := ∏ j∈univ.erase i,ym p e s j
    1≤xx ∧ xx≤8 ∧ 0≤yy ∧ yy≤1 := by
  dsimp only
  have b := mixed_range p e great pos s
  have upper := Finset.prod_le_prod (s:=univ.erase i) (fun j _ => zero_le_one.trans (b j).1)
    (fun j _ => (b j).2.1)
  refine ⟨one_le_prod (fun j _ => (b j).1),?_,prod_nonneg (fun j _ => (b j).2.2.1),
    prod_le_one (fun j _ => (b j).2.2.1) (fun j _ => (b j).2.2.2.1)⟩
  norm_num at upper ⊢; exact upper

theorem step_abs (great : ∀ i,1<p i) (pos : ∀ i,0<e i)
    {s : Finset (Fin 4)} {i : Fin 4} (hi : i∉s) :
    |scoreM p e s-scoreM p e (insert i s)| ≤
        err (p i) (e i)*(8+((p i:ℚ)-1)) := by
  obtain ⟨hx,ux,hy,uy⟩ := coefficient p e great pos s i
  have pp : (1:ℚ)<p i := by exact_mod_cast great i
  have bypos := mul_nonneg (show 0≤(p i:ℚ)-1 by linarith) hy
  have byle := mul_le_mul_of_nonneg_left uy (show 0≤(p i:ℚ)-1 by linarith)
  rw [difference p e great hi,abs_mul,abs_of_pos (err_pos (great i) _)]
  apply mul_le_mul_of_nonneg_left _ (err_pos (great i) _).le
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- Exact error budget, useful for either a local search box or a global height bound. -/
theorem telescope (great : ∀ i,1<p i) (pos : ∀ i,0<e i) (s : Finset (Fin 4)) :
    |normalized p e-scoreM p e s| ≤ ∑ i∈s,err (p i) (e i)*(8+((p i:ℚ)-1)) := by
  induction s using Finset.induction_on with
  | empty => simp [normalized,scoreM,xm,ym]
  | @insert i s hi ih =>
    rw [sum_insert hi]
    have tr := abs_sub_le (normalized p e) (scoreM p e s) (scoreM p e (insert i s))
    linarith only [tr, ih,step_abs p e great pos hi]

theorem step_strict (great : ∀ i,1<p i) (pos : ∀ i,0<e i)
    {s : Finset (Fin 4)} {i j : Fin 4} (hi : i∉s) (ij : j≠i)
    (small : ((p i:ℚ)-1)*yr (p j) (e j)<1) :
    scoreM p e (insert i s)<scoreM p e s := by
  obtain ⟨hx,_,_,_⟩ := coefficient p e great pos s i
  have b := mixed_range p e great pos s
  have pj : j∈univ.erase i := by simp [ij]
  have no := prod_le_one (s:=(univ.erase i).erase j) (f:=ym p e s)
    (fun z _ => (b z).2.2.1) (fun z _ => (b z).2.2.2.1)
  have full : (∏ z∈univ.erase i,ym p e s z)≤yr (p j) (e j) := by
    rw [←prod_erase_mul _ _ pj]
    exact (mul_le_of_le_one_left (b j).2.2.1 no).trans (b j).2.2.2.2
  have pp : (1:ℚ)<p i := by exact_mod_cast great i
  have strict := (mul_le_mul_of_nonneg_left full (show 0≤(p i:ℚ)-1 by linarith)).trans_lt small
  apply sub_pos.mp
  rw [difference p e great hi]
  exact mul_pos (err_pos (great i) _) (sub_pos.mpr (strict.trans_le hx))

theorem strict_rounding (great : ∀ i,1<p i) (pos : ∀ i,0<e i)
    (s : Finset (Fin 4)) (non : s.Nonempty)
    (controls : ∀ i∈s, ∃ j, j≠i ∧ ((p i:ℚ)-1)*yr (p j) (e j)<1) :
    scoreM p e s<normalized p e := by
  have go (t : Finset (Fin 4)) (ht : t⊆s) : scoreM p e t≤normalized p e ∧
      (t.Nonempty → scoreM p e t<normalized p e) := by
    induction t using Finset.induction_on with
    | empty => simp [normalized,scoreM,xm,ym]
    | @insert i t hi ih =>
      obtain ⟨j,jne,sl⟩ := controls i (ht (mem_insert_self i t))
      have lt := (step_strict p e great pos hi jne sl).trans_le
        (ih (fun _ h => ht (mem_insert_of_mem h))).1
      exact ⟨lt.le,fun _=>lt⟩
  exact (go s (fun _ h=>h)).2 non

end
end OMA.Height245212

namespace OMA.Height245212
open OMA.Smooth245212 Finset
open scoped ArithmeticFunction.sigma
noncomputable section
variable (p e : Fin 4 → ℕ)

theorem strict_prod (great : ∀ i,1<p i) (pos : ∀ i,0<e i)
    (s : Finset (Fin 4)) (non : s.Nonempty)
    (controls : ∀ i∈s, ((p i:ℚ)-1)*(∏ j∈univ.erase i,yr (p j) (e j))<1) :
    scoreM p e s<normalized p e := by
  have go (t : Finset (Fin 4)) (ht : t⊆s) : scoreM p e t≤normalized p e ∧
      (t.Nonempty → scoreM p e t<normalized p e) := by
    induction t using Finset.induction_on with
    | empty => simp [normalized,scoreM,xm,ym]
    | @insert i t hi ih =>
      have b := mixed_range p e great pos t
      have yy := prod_le_prod (s:=univ.erase i) (fun j _ => (b j).2.2.1) (fun j _ => (b j).2.2.2.2)
      have pp : (1:ℚ)<p i := by exact_mod_cast great i
      have ss := (mul_le_mul_of_nonneg_left yy (show 0≤(p i:ℚ)-1 by linarith)).trans_lt
        (controls i (ht (mem_insert_self i t)))
      have lt : scoreM p e (insert i t)<scoreM p e t := by
        apply sub_pos.mp
        rw [difference p e great hi]
        exact mul_pos (err_pos (great i) _) (sub_pos.mpr
          (ss.trans_le (coefficient p e great pos t i).1))
      have l := lt.trans_le (ih (fun _ h=>ht (mem_insert_of_mem h))).1
      exact ⟨l.le,fun _=>l⟩
  exact (go s (fun _ h=>h)).2 non

theorem common_pos (great : ∀ i,1<p i) (s : Finset (Fin 4)) : 0<commonDen p e s := by
  apply prod_pos
  intro i _
  unfold localDen
  split_ifs
  · exact den_pos (great i) _
  · exact Nat.mul_pos (by omega) (pow_pos ((Nat.zero_lt_one).trans (great i)) _)

theorem gap_eq (prime : ∀ i,(p i).Prime) (pos : ∀ i,0<e i) (s : Finset (Fin 4))
    (sol : normalized p e=2)
    (budget : (∑ i∈s,err (p i) (e i)*(8+((p i:ℚ)-1)))*commonDen p e s<1) :
    scoreM p e s=2 := by
  let D := commonDen p e s
  have positive : (0:ℚ)<D := by exact_mod_cast common_pos p e (fun i=>(prime i).one_lt) s
  obtain ⟨z,hz⟩ := integral p e prime s
  have fine := (mul_le_mul_of_nonneg_right
    (telescope p e (fun i=>(prime i).one_lt) pos s) positive.le).trans_lt budget
  rw [sol] at fine
  have zz : |(((2:ℤ)*D-z:ℤ):ℚ)|<1 := by
    push_cast
    rw [hz,←sub_mul,abs_mul,abs_of_pos positive]
    exact fine
  have zi : |(2:ℤ)*D-z|<1 := by exact_mod_cast zz
  have zero : (2:ℤ)*D-z=0 := by rw [abs_lt] at zi; omega
  have rat : (2:ℚ)*D=(z:ℚ) := by exact_mod_cast sub_eq_zero.mp zero
  exact mul_right_cancel₀ positive.ne' (hz.symm.trans rat.symm)

def outside (s : Finset (Fin 4)) : ℕ := ∏ i,if i∈s then 1 else p i^e i
def budgetDen (B E : ℕ) := (E+1)^4*B^8
def coefficientBound (B E : ℕ) := 64*B^9*(E+1)^4

theorem common_le {B E : ℕ} (great : ∀ i,1<p i) (bp : ∀ i,p i≤B) (be : ∀ i,e i≤E)
    (s : Finset (Fin 4)) : commonDen p e s≤budgetDen B E*outside p e s := by
  have B1 : 1≤B := by have := great 0; have := bp 0; omega
  have B2 : 1≤B^2 := Nat.one_le_pow _ _ B1
  have one (i : Fin 4) : localDen p e s i≤
      ((E+1)*B^2)*(if i∈s then 1 else p i^e i) := by
    by_cases h : i∈s
    · simp only [localDen,h,if_true,den,mul_one]
      exact Nat.mul_le_mul (by have:=be i; omega) (Nat.pow_le_pow_left (by have:=bp i; omega) _)
    · simp only [localDen,h,if_false]
      gcongr
      exact (Nat.succ_le_succ (be i)).trans (Nat.le_mul_of_pos_right _ (by omega))
  have all := prod_le_prod' (s:=univ) (fun i _=>one i)
  rw [prod_mul_distrib] at all
  simpa only [commonDen,outside,budgetDen,prod_const,card_univ,Fintype.card_fin,mul_pow,
    ←pow_mul] using all

theorem enough {B E : ℕ} (prime : ∀ i,(p i).Prime)
    (bp : ∀ i,p i≤B) (be : ∀ i,e i≤E) (s : Finset (Fin 4))
    (large : ∀ i∈s, coefficientBound B E*outside p e s < p i^e i) :
    (∑ i∈s,err (p i) (e i)*(8+((p i:ℚ)-1)))*commonDen p e s<1 := by
  let M := outside p e s
  let D := commonDen p e s
  have gd (i) := (prime i).one_lt
  have B1 : 2≤B := by have:=gd 0; have:=bp 0; omega
  have BD : (2:ℚ)≤B := by exact_mod_cast B1
  have dp : (0:ℚ)<D := by exact_mod_cast common_pos p e gd s
  have bounds : 64*B*D≤coefficientBound B E*M := by
    have h := Nat.mul_le_mul_left (64*B) (common_le p e gd bp be s)
    dsimp only [D,M,coefficientBound,budgetDen] at *
    convert h using 1; ring
  have one (i) (hi : i∈s) : err (p i) (e i)*(8+((p i:ℚ)-1))*D ≤ 1/5 := by
    have powpos : (0:ℚ)<(p i:ℚ)^e i := pow_pos (by exact_mod_cast (prime i).pos) _
    have big : (64:ℚ)*B*D<(p i:ℚ)^e i := by exact_mod_cast bounds.trans_lt (large i hi)
    have den1 : (1:ℚ)≤den (p i) (e i) := by exact_mod_cast den_pos (gd i) (e i)
    have scale := mul_le_mul_of_nonneg_right den1 powpos.le
    have boundp : (p i:ℚ)≤B := by exact_mod_cast bp i
    have scale' := mul_le_mul_of_nonneg_right boundp dp.le
    have higher := mul_le_mul_of_nonneg_right BD dp.le
    unfold err
    rw [one_div,←div_eq_inv_mul,div_mul_eq_mul_div,div_le_iff₀
      (mul_pos (lt_of_lt_of_le zero_lt_one den1) powpos)]
    linarith
  rw [sum_mul]
  have h := sum_le_sum one
  have c : s.card≤4 := (card_le_univ s).trans_eq (by simp)
  have cq : (s.card:ℚ)≤4 := by exact_mod_cast c
  simp only [sum_const,nsmul_eq_mul] at h
  change (∑ i∈s,err (p i) (e i)*(8+((p i:ℚ)-1))*D)<1
  linarith

end
end OMA.Height245212

namespace OMA.Height245212
open OMA.Smooth245212 Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma Function
noncomputable section
variable (p e : Fin 4 → ℕ)

theorem singleton_ne (hp : ∀ i,(p i).Prime) (odd : ∀ i,3≤p i)
    (inj : Function.Injective p) (sol : OeisA245212.a (total p e)=(σ 1 (total p e):ℤ))
    (i : Fin 4) : scoreM p e {i}≠normalized p e := by
  let s := (univ : Finset (Fin 4)).erase i
  let a (j : Fin 4) := p j^e j
  let m := ∏ j∈s,a j
  let t := ∏ j∈s,(((e j:ℕ):ℚ)+1)*(p j:ℚ)^e j
  have cop (j k : Fin 4) (ne : j≠k) : (p j).Coprime (p k) :=
    (Nat.coprime_primes (hp j) (hp k)).mpr (fun h=>ne (inj h))
  have pair : (↑s : Set (Fin 4)).Pairwise (Nat.Coprime on a) :=
    fun _ _ _ _ diff => ((cop _ _ diff).pow_left _).pow_right _
  have mpi : m.Coprime (p i) := Nat.Coprime.prod_left fun j hj =>
    (cop _ _ (mem_erase.mp hj).1).pow_left _
  have mpos : 0 < m := prod_pos fun j _=>pow_pos (hp j).pos _
  have rep : total p e=m*p i^e i := (prod_erase_mul _ a (mem_univ i)).symm
  have nz := OMA.PrimePowerDiv245212.nonzero mpos (hp i) (by have:=odd i; omega) mpi (e i) (rep ▸ sol)
  have wp : (∏ j∈s,X (p j) (some (e j)))*t=(W m:ℚ) := by
    rw [IsMultiplicative.map_prod a w_mult s pair]
    push_cast
    unfold t
    rw [←prod_mul_distrib]
    exact prod_congr rfl fun j _=>x_factor (hp j) (e j)
  have sp : (∏ j∈s,Y (p j) (some (e j)))*t=(σ 1 m:ℚ) := by
    rw [IsMultiplicative.map_prod a (isMultiplicative_sigma (k:=1)) s pair]
    push_cast
    unfold t
    rw [←prod_mul_distrib]
    exact prod_congr rfl fun j _=>y_factor (hp j) (e j)
  intro he
  have dif := difference p e (fun j=>(hp j).one_lt) (s:=∅) (i:=i) (notMem_empty i)
  have sc : scoreM p e ∅=normalized p e := by simp [scoreM,normalized,xm,ym]
  rw [sc,insert_empty_eq,he,sub_self] at dif
  have zero := (mul_eq_zero.mp dif.symm).resolve_left (err_pos (hp i).one_lt _).ne'
  simp only [xm,ym,notMem_empty,if_false] at zero
  have z := congrArg (fun q : ℚ=>q*t) (sub_eq_zero.mp zero)
  change (∏ j∈s,X (p j) (some (e j)))*t=
    ((p i:ℚ)-1)*(∏ j∈s,Y (p j) (some (e j)))*t at z
  rw [wp,mul_assoc,sp] at z
  apply nz
  exact_mod_cast sub_eq_zero.mpr z

end
end OMA.Height245212

namespace OMA.Height245212
open OMA.Smooth245212 Finset
open scoped ArithmeticFunction.sigma
noncomputable section
variable (p e : Fin 4 → ℕ)

theorem large_y {B : ℕ} (hp : ∀ i,1<p i) (positive : ∀ i,0<e i) (bp : ∀ i,p i≤B)
    (i j : Fin 4) (h : B^(2*B)<p j^e j) :
    ((p i:ℚ)-1)*yr (p j) (e j)<1 := by
  have Bpos : 0<B := (Nat.zero_lt_one.trans (hp i)).trans_le (bp i)
  have exp : 2*B<e j := by
    by_contra! fail
    exact (h.not_ge ((Nat.pow_le_pow_left (bp j) _).trans (Nat.pow_le_pow_right Bpos fail)))
  have ep : (2:ℚ)*B < e j := by exact_mod_cast exp
  have pb : (p i:ℚ)≤B := by exact_mod_cast bp i
  have scale : 2*((p i:ℚ)-1)<(e j:ℚ)+1 := by linarith
  have y := y_range (hp j) (positive j)
  by_cases eq : yr (p j) (e j)=0
  · simp [eq]
  · have v := mul_lt_mul_of_pos_right scale (lt_of_le_of_ne y.1 (Ne.symm eq))
    linarith only [v,y.2.2]

theorem peel {B E : ℕ} (prime : ∀ i,(p i).Prime) (odd : ∀ i,3≤p i)
    (pos : ∀ i,0<e i) (inj : Function.Injective p) (bp : ∀ i,p i≤B) (be : ∀ i,e i≤E)
    (sol : OeisA245212.a (total p e)=(σ 1 (total p e):ℤ))
    (s : Finset (Fin 4)) (non : s.Nonempty) :
    ∃ i∈s, p i^e i ≤ max (B^(2*B)) (coefficientBound B E*outside p e s) := by
  by_contra! fail
  have gd (i) := (prime i).one_lt
  have big (i) (h : i∈s) := lt_of_le_of_lt (le_max_right _ _) (fail i h)
  have norm := normalized_of_eq p prime inj e sol
  have same := gap_eq p e prime pos s norm (enough p e prime bp be s big)
  by_cases size : 1<s.card
  · have controls (i) (h : i∈s) : ∃ j, j≠i ∧ ((p i:ℚ)-1)*yr (p j) (e j)<1 := by
      have nn : (s.erase i).Nonempty := card_pos.mp (by rw [card_erase_of_mem h]; omega)
      obtain ⟨j,hj⟩ := nn
      have jm := mem_erase.mp hj
      exact ⟨j,jm.1,large_y p e gd pos bp i j ((le_max_left _ _).trans_lt (fail j jm.2))⟩
    have strict := strict_rounding p e gd pos s non controls
    linarith only [same,norm,strict]
  · have eq : s.card=1 := by have := card_pos.mpr non; omega
    obtain ⟨i,rfl⟩ := card_eq_one.mp eq
    exact singleton_ne p e prime odd inj sol i (same.trans norm.symm)

theorem outside_erase {s : Finset (Fin 4)} {i : Fin 4} (hi : i∈s) :
    outside p e (s.erase i)=outside p e s*(p i^e i) := by
  let a (j : Fin 4) := if j∈s then 1 else p j^e j
  let b (j : Fin 4) := if j∈s.erase i then 1 else p j^e j
  have eq : (∏ j∈univ.erase i,b j)=∏ j∈univ.erase i,a j :=
    prod_congr rfl fun j hj=>by simp [a,b,(mem_erase.mp hj).1]
  change (∏ j,b j)=(∏ j,a j)*(p i^e i)
  rw [←prod_erase_mul _ b (mem_univ i),←prod_erase_mul _ a (mem_univ i),eq]
  simp [a,b,hi]

theorem total_bound {B E : ℕ} (prime : ∀ i,(p i).Prime) (odd : ∀ i,3≤p i)
    (pos : ∀ i,0<e i) (inj : Function.Injective p) (bp : ∀ i,p i≤B) (be : ∀ i,e i≤E)
    (sol : OeisA245212.a (total p e)=(σ 1 (total p e):ℤ)) :
    total p e≤(B^(2*B)*coefficientBound B E)^15 := by
  let V := B^(2*B)
  let C := coefficientBound B E
  let K := V*C
  have Bpos : 0<B := (prime 0).pos.trans_le (bp 0)
  have cp : 0<C := by dsimp [C,coefficientBound]; positivity
  have vp : 0<V := pow_pos Bpos _
  have kp : 0<K := Nat.mul_pos vp cp
  have steps (k : ℕ) (le : k≤4) :
      ∃ s : Finset (Fin 4), s.card=4-k ∧ outside p e s≤K^(2^k-1) := by
    induction k with
    | zero => exact ⟨univ,by simp,by simp [outside]⟩
    | succ k ih =>
      obtain ⟨s,hc,base⟩ := ih (by omega)
      obtain ⟨i,hi,sm⟩ := peel p e prime odd pos inj bp be sol s (card_pos.mp (by omega))
      let M := outside p e s
      have mp : 0<M := prod_pos fun j _ => by split_ifs <;> first | decide | exact pow_pos (prime j).pos _
      change p i^e i ≤ max V (C*M) at sm
      have a : p i^e i≤K*M := sm.trans (max_le
        (by dsimp [K]; nlinarith only [Nat.le_mul_of_pos_right V cp,Nat.le_mul_of_pos_right (V*C) mp])
        (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left C vp)))
      refine ⟨s.erase i,by rw [card_erase_of_mem hi]; omega,?_⟩
      rw [outside_erase p e hi]
      change M*(p i^e i)≤_
      calc
        M*(p i^e i)≤M*(K*M) := Nat.mul_le_mul_left _ a
        _ = K*M^2 := by ring
        _ ≤ K*(K^(2^k-1))^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left base 2)
        _ = K^(2^(k+1)-1) := by
          rw [←pow_mul,←pow_succ']
          congr 1; rw [pow_succ]; have := Nat.two_pow_pos k; omega
  obtain ⟨s,empty,bd⟩ := steps 4 (by decide)
  have es : s=∅ := card_eq_zero.mp (by omega)
  simpa [es,outside,total,K,V,C] using bd

/-- Numerical premise for the exponent-only calculation, with E the actual maximum. -/
theorem max_power {B : ℕ} (prime : ∀ i,(p i).Prime) (odd : ∀ i,3≤p i)
    (pos : ∀ i,0<e i) (inj : Function.Injective p) (bp : ∀ i,p i≤B)
    (sol : OeisA245212.a (total p e)=(σ 1 (total p e):ℤ)) :
    let E := univ.sup e
    2^E ≤ (B^(2*B)*(64*B^9*(E+1)^4))^15 := by
  dsimp only
  have be (i : Fin 4) : e i≤univ.sup e := le_sup (f:=e) (mem_univ i)
  obtain ⟨i,_,eq⟩ := exists_mem_eq_sup univ univ_nonempty e
  have one : p i^e i≤total p e := single_le_prod' (fun j _ => Nat.one_le_pow _ _ (prime j).pos) (mem_univ i)
  calc
    2^(univ.sup e) = 2^e i := by rw [eq]
    _ ≤ p i^e i := Nat.pow_le_pow_left (prime i).two_le _
    _ ≤ total p e := one
    _ ≤ _ := total_bound p e prime odd pos inj bp be sol

end
end OMA.Height245212

namespace OMA.OddFaces245212
open OMA.Smooth245212
def limitX (p : ℕ) : ℚ := X p none
end OMA.OddFaces245212

namespace OMA.OddFaces245212
open Finset OMA.Smooth245212
variable {ι : Type*} [DecidableEq ι]

private theorem factor (p e : ℕ) :
    X p (some e)=Y p (some e)+(1-Y p (some e))*limitX p := by
  simp only [limitX,X,Y]; ring

private theorem cap_one {p : ℕ} (hp : 1<p) : 1≤limitX p := by
  have h : (1:ℚ)<p := by exact_mod_cast hp
  simp only [limitX,X,Y,sub_zero]
  exact le_add_of_nonneg_right (by positivity)

private theorem envelope (s : Finset ι) (p e : ι → ℕ) (hp : ∀ i,1<p i) :
    (∏ i∈s,X (p i) (some (e i))) ≤ (∏ i∈s,Y (p i) (some (e i)))+
      (1-∏ i∈s,Y (p i) (some (e i)))*(∏ i∈s,limitX (p i)) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s js ih =>
    simp only [prod_insert js]
    have mult := mul_le_mul_of_nonneg_left ih (x_nonneg (hp j) (some (e j)))
    refine mult.trans ?_
    rw [factor (p j)]
    let T := ∏ i∈s,Y (p i) (some (e i))
    let C := ∏ i∈s,limitX (p i)
    have t0 : 0≤T := prod_nonneg (fun i _ => y_nonneg (hp i) _)
    have t1 : T≤1 := prod_le_one (fun i _ => y_nonneg (hp i) _) (fun i _ => y_one (hp i) _)
    have c1 : 1≤C := one_le_prod (fun i _ => cap_one (hp i))
    have l1 := cap_one (hp j)
    have u1 := y_one (hp j) (some (e j))
    have u0 := y_nonneg (hp j) (some (e j))
    change (_+_*_)*(T+(1-T)*C)≤_*T+(1-_*T)*(_*C)
    nlinarith only [mul_nonneg (mul_nonneg (mul_nonneg t0 (sub_nonneg.mpr u1)) (by linarith only [l1] : 0≤limitX (p j))) (sub_nonneg.mpr c1),
      mul_nonneg (mul_nonneg (mul_nonneg u0 (sub_nonneg.mpr t1)) (by linarith only [c1] : 0≤C)) (sub_nonneg.mpr l1)]

theorem cap_needed [Fintype ι] (p e : ι → ℕ) (hp : ∀ i,1<p i) (i : ι) (hi : 0<e i)
    (eq : normalized p e=2) : 2≤∏ j,limitX (p j) := by
  by_contra! lt
  have ylt : Y (p i) (some (e i))<1 := by
    have := OMA.Abundance245212.y_strict (hp i) hi
    simpa [y_avg (hp i)] using this
  have prodlt : (∏ j,Y (p j) (some (e j)))<1 := by
    rw [←prod_erase_mul _ _ (mem_univ i)]
    apply lt_of_le_of_lt _ ylt
    exact mul_le_of_le_one_left (y_nonneg (hp i) _) (prod_le_one
      (fun j _ => y_nonneg (hp j) _) (fun j _ => y_one (hp j) _))
  have h := envelope univ p e hp
  unfold normalized at eq
  nlinarith only [eq,h,mul_pos (sub_pos.mpr prodlt) (sub_pos.mpr lt)]

end OMA.OddFaces245212

namespace OMA.Moving245212
open Finset OMA.Smooth245212

def approx (upper : Bool) (q e : Option ℕ) : ℚ :=
  match q, e with
  | _, none => 0
  | none, some k => 1/((k:ℚ)+1)
  | some p, some k =>
    if k<32 then Y p (some k) else
      let v := (p:ℚ)/(((p:ℚ)-1)*((k:ℚ)+1))
      if upper then v else v*(1-(p:ℚ)⁻¹^32)

private theorem approx_correct {p e : ℕ} (hp : 1<p) :
    approx false (some p) (some e) ≤ Y p (some e) ∧
      Y p (some e) ≤ approx true (some p) (some e) := by
  by_cases small : e<32
  · simp [approx,small]
  simp only [approx,if_neg small,Bool.false_eq_true,↓reduceIte]
  have pp : (1:ℚ)<p := by exact_mod_cast hp
  have pn : (p:ℚ)≠0 := by positivity
  have pe := sub_ne_zero.mpr pp.ne'
  have norm : Y p (some e) =
      (p:ℚ)/(((p:ℚ)-1)*((e:ℚ)+1)) * (1-(p:ℚ)⁻¹^(e+1)) := by
    simp only [Y]
    rw [show (p:ℚ)⁻¹-1=(1-p)/p by field_simp]
    generalize (p:ℚ)⁻¹^(e+1) = z
    field_simp [show 1-(p:ℚ)≠0 by linarith]
    ring
  rw [norm]
  have hle : (p:ℚ)⁻¹^(e+1) ≤ (p:ℚ)⁻¹^32 :=
    pow_le_pow_of_le_one (by positivity) (inv_lt_one_of_one_lt₀ pp).le (by omega)
  have v : 0≤(p:ℚ)/(((p:ℚ)-1)*((e:ℚ)+1)) := by positivity
  constructor
  · exact mul_le_mul_of_nonneg_left (by linarith only [hle]) v
  · simpa using mul_le_mul_of_nonneg_left
      (show 1-(p:ℚ)⁻¹^(e+1) ≤ 1 by exact sub_le_self _ (by positivity)) v

private theorem y_prime {p q : ℕ} (hp : 1<p) (hpq : p≤q) (e : ℕ) :
    Y q (some e) ≤ Y p (some e) := by
  rw [y_avg hp,y_avg (hp.trans_le hpq)]
  gcongr with i _

private theorem y_infty {p e : ℕ} (hp : 1<p) :
    1/((e:ℚ)+1) ≤ Y p (some e) := by
  rw [y_avg hp]
  gcongr
  calc
    (1:ℚ) = (p:ℚ)⁻¹^0 := by simp
    _ ≤ ∑ i∈range (e+1),(p:ℚ)⁻¹^i :=
      single_le_sum (f:= fun i => (p:ℚ)⁻¹^i) (fun _ _ => by positivity) (by simp)

def yl (prime exp : Band) := max 0 (approx false prime.hi exp.hi)
def yu (prime exp : Band) := approx true (some prime.lo) (some exp.lo)
def xl (prime exp : Band) : ℚ := match prime.hi with
  | none => 1
  | some p => max 1 (1+(1-yu prime exp)/((p:ℚ)-1))
def xu (prime exp : Band) : ℚ := 1+(1-yl prime exp)/((prime.lo:ℚ)-1)

private theorem y_bounds {p e : ℕ} {pb eb : Band} (hp : 1<pb.lo)
    (pi : pb.Contains p) (ei : eb.Contains e) :
    yl pb eb ≤ Y p (some e) ∧ Y p (some e) ≤ yu pb eb := by
  have pp := hp.trans_le pi.1
  constructor
  · refine max_le (y_nonneg pp _) ?_
    cases he : eb.hi with
    | none => simpa [he,approx] using y_nonneg pp (some e)
    | some t =>
      have et := y_anti pp (ei.2 _ he)
      cases hq : pb.hi with
      | none => simpa [he,hq,approx] using (y_infty pp).trans et
      | some q =>
        have pq := pi.2 _ hq
        exact (approx_correct (e:=t) (pp.trans_le pq)).1.trans
          ((y_prime pp pq t).trans et)
  · exact (y_anti pp ei.1).trans ((y_prime hp pi.1 _).trans (approx_correct hp).2)

theorem factor_bounds {p e : ℕ} {pb eb : Band} (hp : 1<pb.lo)
    (pi : pb.Contains p) (ei : eb.Contains e) :
    0≤xl pb eb ∧ xl pb eb ≤ X p (some e) ∧ X p (some e) ≤ xu pb eb ∧
    0≤yl pb eb ∧ yl pb eb ≤ Y p (some e) ∧ Y p (some e) ≤ yu pb eb := by
  obtain ⟨ylb,yub⟩ := y_bounds hp pi ei
  have pp := hp.trans_le pi.1
  have pp' : (1:ℚ)<p := by exact_mod_cast pp
  have pl : (1:ℚ)<pb.lo := by exact_mod_cast hp
  have oneX : 1≤X p (some e) := by
    have := sub_nonneg.mpr (y_one pp (some e))
    exact le_add_of_nonneg_right (by positivity)
  have yl0 : 0≤yl pb eb := le_max_left _ _
  refine ⟨?_,?_,?_,yl0,ylb,yub⟩
  · cases h : pb.hi <;> simp [xl,h]
  · cases h : pb.hi with
    | none => simpa [xl,h] using oneX
    | some q =>
      simp only [xl,h,max_le_iff]
      refine ⟨oneX,?_⟩
      have pq : (p:ℚ)≤q := by exact_mod_cast pi.2 q h
      unfold X
      apply add_le_add_right
      exact div_le_div₀ (by linarith only [y_one pp (some e)]) (by linarith only [yub])
        (by linarith only [pp']) (by linarith only [pq])
  · have pq : (pb.lo:ℚ) ≤ p := by exact_mod_cast pi.1
    unfold X xu
    apply add_le_add_right
    exact div_le_div₀ (by linarith only [y_one pp (some e),ylb]) (by linarith only [ylb])
      (by linarith only [pl]) (by linarith only [pq])

end OMA.Moving245212

namespace OMA.Box245212
open Finset OMA.Smooth245212 OMA.Moving245212
open scoped ArithmeticFunction.sigma

structure Range where
  lo : ℕ
  hi : ℕ
  deriving DecidableEq
def Range.has (a : Range) (n : ℕ) := a.lo ≤ n ∧ n ≤ a.hi
def Range.band (a : Range) : Band := ⟨a.lo,some a.hi⟩
theorem Range.band_has {a : Range} {n : ℕ} (h : a.has n) : a.band.Contains n :=
  ⟨h.1,by intro j hj; cases Option.some.inj hj; exact h.2⟩

abbrev Box := Fin 5 → Range
abbrev Values := Fin 5 → ℕ
def Fits (b : Box) (v : Values) := ∀ i,(b i).has (v i)
def bases (p q : ℕ) (v : Values) : Fin 4 → ℕ := ![3,p,q,v 4]
def exponents (v : Values) (i : Fin 4) := v i.castSucc
def baseBox (p q : ℕ) (b : Box) : Fin 4 → Range :=
  ![⟨3,3⟩,⟨p,p⟩,⟨q,q⟩,b 4]

structure Candidate (p q : ℕ) (v : Values) : Prop where
  prime : ∀ i,(bases p q v i).Prime
  ordered : StrictMono (bases p q v)
  pos : ∀ i,0 < exponents v i
  first : 2 ≤ v 0
  eqn : let n := total (bases p q v) (exponents v)
        OeisA245212.a n=(σ 1 n:ℤ)

theorem Candidate.score {p q : ℕ} {v : Values} (h : Candidate p q v) :
    normalized (bases p q v) (exponents v)=2 :=
  normalized_of_eq _ h.prime h.ordered.injective _ h.eqn

def Deny (p q : ℕ) (b : Box) := ∀ v,Fits b v → ¬ Candidate p q v
def clip (b : Box) (i : Fin 5) (c : Range) : Box := Function.update b i c
theorem clip_fits {b : Box} {v : Values} (h : Fits b v) {i : Fin 5} {c : Range}
    (hc : c.has (v i)) : Fits (clip b i c) v := by
  intro j
  by_cases e : j=i
  · subst j; simpa [clip] using hc
  · simpa [clip,e] using h j

theorem split (p q : ℕ) (b : Box) (i : Fin 5) (m : ℕ)
    (lower : Deny p q (clip b i ⟨(b i).lo,m⟩))
    (upper : Deny p q (clip b i ⟨m+1,(b i).hi⟩)) : Deny p q b := by
  intro v inside
  by_cases small : v i ≤ m
  · exact lower v (clip_fits inside ⟨(inside i).1,small⟩)
  · exact upper v (clip_fits inside ⟨show m+1≤v i by omega,(inside i).2⟩)

def factor (f : Band → Band → ℚ) (p q : ℕ) (b : Box) (i : Fin 4) :=
  f (baseBox p q b i).band (b i.castSucc).band

theorem inside_primes {p q : ℕ} {b : Box} {v : Values} (inside : Fits b v) (i : Fin 4) :
    (baseBox p q b i).has (bases p q v i) := by
  fin_cases i <;> simp [baseBox,bases,Range.has]
  exact inside 4

theorem moments {p q : ℕ} {b : Box} {v : Values} (inside : Fits b v)
    (start : ∀ i,1<(baseBox p q b i).lo) (i : Fin 4) :
    let P := bases p q v i; let E := some (exponents v i)
    0≤factor xl p q b i ∧ factor xl p q b i≤X P E ∧ X P E≤factor xu p q b i ∧
    0≤factor yl p q b i ∧ factor yl p q b i≤Y P E ∧ Y P E≤factor yu p q b i :=
  factor_bounds (start i) (Range.band_has (inside_primes inside i)) (Range.band_has (inside i.castSucc))

def prod4 (f : Fin 4 → ℚ) := ∏ i,f i
def interval (p q : ℕ) (b : Box) : Bool :=
  decide ((∀ i,1<(baseBox p q b i).lo) ∧
    (2 < prod4 (factor xl p q b)+prod4 (factor yl p q b) ∨
      prod4 (factor xu p q b)+prod4 (factor yu p q b)<2))

theorem interval_sound {p q : ℕ} {b : Box} (check : interval p q b=true) : Deny p q b := by
  obtain ⟨start,why⟩ := of_decide_eq_true check
  intro v inside candidate
  have m := moments inside start
  have s := candidate.score
  unfold normalized at s
  have lowerX := prod_le_prod (s:=univ) (fun i _ => (m i).1) (fun i _ => (m i).2.1)
  have lowerY := prod_le_prod (s:=univ) (fun i _ => (m i).2.2.2.1) (fun i _ => (m i).2.2.2.2.1)
  have upperX := prod_le_prod (s:=univ) (fun i _ => (m i).1.trans (m i).2.1) (fun i _ => (m i).2.2.1)
  have upperY := prod_le_prod (s:=univ) (fun i _ => (m i).2.2.2.1.trans (m i).2.2.2.2.1)
    (fun i _ => (m i).2.2.2.2.2)
  rcases why with h|h <;> unfold prod4 at h <;> linarith

end OMA.Box245212

namespace OMA.Box245212
open Finset OMA.Smooth245212 OMA.Height245212 OMA.OddFaces245212
open scoped ArithmeticFunction.sigma

theorem maxExponent {B : ℕ} (p e : Fin 4 → ℕ) (prime : ∀ i,(p i).Prime)
    (odd : ∀ i,3≤p i) (pos : ∀ i,0<e i) (inj : Function.Injective p) (bp : ∀ i,p i≤B)
    (sol : OeisA245212.a (total p e)=(σ 1 (total p e):ℤ)) (i : Fin 4) :
    e i ≤ OMA.HeightLog245212.ceiling 4 B := by
  have mem (j : Fin 4) : e j≤univ.sup e := le_sup (f:=e) (mem_univ j)
  exact (mem i).trans (OMA.HeightLog245212.four ((pos i).trans_le (mem i))
    (max_power p e prime odd pos inj bp sol))

def topR (p q : ℕ) :=
  let m := 4*(p-1)*(q-1)
  if 3*p*q < m then min 999999999999999999 (m/(m-3*p*q)) else 999999999999999999

def families : Finset (ℕ×ℕ) :=
  {(5,7),(5,11),(5,13),(5,17),(5,19),(5,23),(5,29),(5,31),(7,11),(7,13)}

def rootBox (p q : ℕ) : Box :=
  let r := topR p q
  let h := OMA.HeightLog245212.ceiling 4 r
  ![⟨2,h⟩,⟨1,h⟩,⟨1,h⟩,⟨1,h⟩,⟨q+1,r⟩]

private theorem ratio {p : ℕ} (hp : 1<p) : limitX p=(p:ℚ)/((p:ℚ)-1) := by
  have hh : (1:ℚ)<p := by exact_mod_cast hp
  simp only [limitX,X,Y,sub_zero]; field_simp [sub_ne_zero.mpr hh.ne']; ring

theorem cap_integer {p q : ℕ} {v : Values} (c : Candidate p q v) :
    4*(p-1)*(q-1)*(v 4-1)≤3*p*q*v 4 := by
  have gd (i) := (c.prime i).one_lt
  have h := cap_needed _ _ gd 0 (c.pos 0) c.score
  simp only [Fin.prod_univ_four,bases,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three] at h
  have hp : 1<p := gd 1
  have hq : 1<q := gd 2
  have hr : 1<v 4 := gd 3
  have pp : (1:ℚ)<p := by exact_mod_cast hp
  have pq : (1:ℚ)<q := by exact_mod_cast hq
  have pr : (1:ℚ)<v 4 := by exact_mod_cast hr
  change 2≤limitX 3*limitX p*limitX q*limitX (v 4) at h
  rw [ratio (by decide : 1<3),ratio hp,ratio hq,ratio hr] at h
  norm_num at h
  field_simp at h
  have hd : 0<((p:ℚ)-1)*((q:ℚ)-1)*((v 4:ℚ)-1) :=
    mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  have hh := (le_div_iff₀ hd).mp h
  rw [←Nat.cast_le (α:=ℚ)]
  push_cast [Nat.cast_sub hp.le,Nat.cast_sub hq.le,Nat.cast_sub hr.le]
  linarith only [hh]

theorem last_bound {p q : ℕ} {v : Values} (c : Candidate p q v) (cut : v 4≤999999999999999999) :
    v 4≤topR p q := by
  dsimp only [topR]
  split_ifs with lt
  · refine le_min cut ((Nat.le_div_iff_mul_le (Nat.sub_pos_of_lt lt)).mpr ?_)
    let m := 4*(p-1)*(q-1)
    let a := 3*p*q
    have al : a ≤ m := lt.le
    have r1 : 1≤v 4 := (c.prime 3).pos
    have hh := cap_integer c
    change m*(v 4-1)≤a*v 4 at hh
    have prod1 := congrArg (fun x:ℕ=>m*x) (Nat.sub_add_cancel r1)
    have prod2 := congrArg (fun x:ℕ=>x*(v 4)) (Nat.sub_add_cancel al)
    change v 4*(m-a) ≤ m
    nlinarith only [hh,prod1,prod2]
  · exact cut

theorem family_cover : ∀ p∈({5,7}:Finset ℕ), ∀ q∈Icc (p+1) 31,
    q.Prime → q<topR p q → (p,q)∈families := by decide +kernel

theorem exclude_bounded
    (proofs : ∀ pq∈families,Deny pq.1 pq.2 (rootBox pq.1 pq.2)) :
    ∀ p∈({5,7}:Finset ℕ), ∀ q∈Icc (p+1) 31, ∀ r∈Icc (q+1) 999999999999999999,
    q.Prime → r.Prime → ∀ k e f g : ℕ, 2≤k → 0<e → 0<f → 0<g →
    let n := 3^k*p^e*q^f*r^g
    OeisA245212.a n ≠ (σ 1 n : ℤ) := by
  intro p ps q qs r rs hq hr k e f g hk he hf hg n sol
  let v : Values := ![k,e,f,g,r]
  have hp : p.Prime := by simp only [mem_insert,mem_singleton] at ps; rcases ps with rfl|rfl <;> decide
  have pp : 3<p := by simp only [mem_insert,mem_singleton] at ps; omega
  obtain ⟨pq,qmax⟩ := mem_Icc.mp qs
  obtain ⟨qr,rmax⟩ := mem_Icc.mp rs
  have c : Candidate p q v := by
    constructor
    · intro i; fin_cases i <;> simp [bases,v,hp,hq,hr,Nat.prime_three]
    · apply Fin.strictMono_iff_lt_succ.mpr
      intro i; fin_cases i <;> simp [bases,v] <;> omega
    · intro i; fin_cases i <;> simp [exponents,v] <;> omega
    · exact hk
    · simpa [total,bases,exponents,v,Fin.prod_univ_four,n] using sol
  have rb : r≤topR p q := last_bound (v:=v) c rmax
  have mem := family_cover p ps q qs hq (by omega)
  have exp (i : Fin 4) : exponents v i ≤ OMA.HeightLog245212.ceiling 4 (topR p q) :=
    maxExponent _ _ c.prime (fun i=>c.ordered.monotone (Fin.zero_le i)) c.pos c.ordered.injective
      (fun i=>(c.ordered.monotone (Fin.le_last i)).trans rb) c.eqn i
  apply proofs (p,q) mem v _ c
  intro i; fin_cases i
  · exact ⟨hk,exp 0⟩
  · exact ⟨he,exp 1⟩
  · exact ⟨hf,exp 2⟩
  · exact ⟨hg,exp 3⟩
  · exact ⟨qr,rb⟩

theorem h2_of_roots
    (proofs : ∀ pq∈families,Deny pq.1 pq.2 (rootBox pq.1 pq.2)) :
    OMA.R_OeisA245212_conjecture_R1_H1_R1_H2_R1_H2_R1.H2 := by
  intro p ps q qs r rs hq hr k e f g hk he hf hg _ _
  exact exclude_bounded proofs p ps q qs r rs hq hr k e f g hk he hf hg

end OMA.Box245212

namespace OMA.PageTree245212

inductive Pages where
  | p (values : List ℕ)
  | b (cut : ℕ) (left right : Pages)

def get : Pages→ℕ→ℕ
  | .p vs,i => vs.getD (i%16) 0
  | .b n l r,i => if i<n then get l i else get r i

end OMA.PageTree245212

namespace OMA.Box245212
open Finset

-- Nat.log squares its base at each recursive step, so the kernel can
-- compute the exact bit bound in logarithmically many comparisons.
def sizeLo (n : ℕ) := Nat.log 2 (n^128)
def sizeHi (n : ℕ) := sizeLo n+1
def Enc (l h n : ℕ) := 2^l ≤ n^128 ∧ n^128 ≤ 2^h

theorem enc_range {r : Range} {n : ℕ} (pos : 0<r.lo) (inside : r.has n) :
    Enc (sizeLo r.lo) (sizeHi r.hi) n := by
  unfold sizeHi sizeLo
  simp only [←Nat.log2_eq_log_two]
  exact ⟨(Nat.log2_self_le (pow_ne_zero 128 pos.ne')).trans (Nat.pow_le_pow_left inside.1 128),
    (Nat.pow_le_pow_left inside.2 128).trans Nat.lt_log2_self.le⟩

theorem enc_one : Enc 0 0 1 := by simp [Enc]
theorem enc_mul {a b l h L H : ℕ} (x : Enc l h a) (y : Enc L H b) :
    Enc (l+L) (h+H) (a*b) := by
  unfold Enc; rw [pow_add,pow_add,mul_pow]
  exact ⟨Nat.mul_le_mul x.1 y.1,Nat.mul_le_mul x.2 y.2⟩

theorem enc_pow {a e l h : ℕ} {b : Range} (x : Enc l h a) (y : b.has e) :
    Enc (l*b.lo) (h*b.hi) (a^e) := by
  unfold Enc
  have swap : (a^e)^128=(a^128)^e := by rw [←pow_mul,←pow_mul,mul_comm e]
  rw [swap, pow_mul, pow_mul]
  exact ⟨(Nat.pow_le_pow_right (by positivity) y.1).trans (Nat.pow_le_pow_left x.1 e),
    (Nat.pow_le_pow_left x.2 e).trans (Nat.pow_le_pow_right (by positivity) y.2)⟩

theorem enc_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (l h a : ι→ℕ)
    (hs : ∀ i∈s,Enc (l i) (h i) (a i)) : Enc (∑ i∈s,l i) (∑ i∈s,h i) (∏ i∈s,a i) := by
  induction s using Finset.induction_on with
  | empty => simpa using enc_one
  | @insert i s hi ih =>
    simpa [hi] using enc_mul (hs i (mem_insert_self i s))
      (ih (fun j hj => hs j (mem_insert_of_mem hj)))

theorem enc_lt {a b l h L H : ℕ} (x : Enc l h a) (y : Enc L H b) (sep : h<L) : a<b := by
  by_contra! wrong
  have big := Nat.pow_lt_pow_right (by decide : 1 < 2) sep
  have sm := (y.1.trans (Nat.pow_le_pow_left wrong 128)).trans x.2
  exact big.not_ge sm

end OMA.Box245212

namespace OMA.Height245212
open Finset OMA.Smooth245212
noncomputable section

theorem point_gap (p e : Fin 4 → ℕ) (prime : ∀ i,(p i).Prime) (pos : ∀ i,0<e i)
    (s : Finset (Fin 4)) (sol : normalized p e=2)
    (small : ∀ i∈s,4*(8+(p i-1))*(∏ j∈univ.erase i,localDen p e s j)<p i^e i) :
    scoreM p e s=2 := by
  apply gap_eq p e prime pos s sol
  by_cases empty : s=∅
  · simp [empty]
  have one (i) (hi : i∈s) : err (p i) (e i)*(8+((p i:ℚ)-1))*commonDen p e s<1/4 := by
    have hd : (0:ℚ)<den (p i) (e i) := by exact_mod_cast den_pos (prime i).one_lt _
    have pp : (0:ℚ)<(p i:ℚ)^e i := by exact_mod_cast pow_pos (prime i).pos (e i)
    have h : (4:ℚ)*(8+((p i:ℚ)-1))*(∏ j∈univ.erase i,(localDen p e s j:ℚ))<(p i:ℚ)^e i := by
      have t : (4:ℚ)*(8+((p i-1:ℕ):ℚ))*(∏ j∈univ.erase i,(localDen p e s j:ℚ))<(p i:ℚ)^e i := by
        exact_mod_cast small i hi
      simpa only [Nat.cast_sub (prime i).pos,Nat.cast_one] using t
    have common : (commonDen p e s:ℚ)=
        (∏ j∈univ.erase i,(localDen p e s j:ℚ))*den (p i) (e i) := by
      unfold commonDen
      rw [Nat.cast_prod,←prod_erase_mul ((univ):Finset (Fin 4)) (fun j => (localDen p e s j:ℚ)) (mem_univ i)]
      simp [localDen,hi]
    rw [common,err]
    field_simp [hd.ne',pp.ne']
    nlinarith only [mul_pos hd (sub_pos.mpr h)]
  rw [sum_mul]
  have sum := sum_lt_sum_of_nonempty (Finset.nonempty_iff_ne_empty.mpr empty) one
  have card : s.card≤4 := (card_le_univ s).trans_eq (by simp)
  have cq : (s.card:ℚ)≤4 := by exact_mod_cast card
  simp only [sum_const,nsmul_eq_mul] at sum
  linarith

end
end OMA.Height245212

namespace OMA.Height245212
open OMA.Smooth245212 Finset
open scoped ArithmeticFunction.sigma
noncomputable section

theorem selected_numerator (p e : Fin 4 → ℕ) (prime : ∀ i,(p i).Prime) (s : Finset (Fin 4))
    (t : Fin 4) (ht : t∈s) :
    ∃ z : ℤ,(z:ℚ)=scoreM p e s*commonDen p e s ∧ (p t:ℤ)∣z := by
  have ints (i : Fin 4) : ∃ u v : ℤ,
      (u:ℚ)=xm p e s i*localDen p e s i ∧ (v:ℚ)=ym p e s i*localDen p e s i ∧
      (i=t → (p t:ℤ)∣u ∧ (p t:ℤ)∣v) := by
    by_cases h : i∈s
    · refine ⟨(p i:ℤ)*(((p i:ℤ)-1)*((e i:ℤ)+1)-1),(p i:ℤ)*((p i:ℤ)-1),?_,?_,?_⟩
      · have pi : (1:ℚ)<p i := by exact_mod_cast (prime i).one_lt
        simp only [xm,localDen,h,if_pos,xr,yr,den]; push_cast [Nat.cast_sub (prime i).pos]
        field_simp [sub_ne_zero.mpr pi.ne']; ring
      · have pi : (1:ℚ)<p i := by exact_mod_cast (prime i).one_lt
        simp only [ym,localDen,h,if_pos,yr,den]; push_cast [Nat.cast_sub (prime i).pos]
        field_simp [sub_ne_zero.mpr pi.ne']
      · rintro rfl; exact ⟨dvd_mul_right _ _,dvd_mul_right _ _⟩
    · refine ⟨(W (p i^e i):ℕ),(σ 1 (p i^e i):ℕ),?_,?_,fun h' => (h (h' ▸ ht)).elim⟩
      · simpa [xm,localDen,h] using (x_factor (prime i) (e i)).symm
      · simpa [ym,localDen,h] using (y_factor (prime i) (e i)).symm
  choose u v hu hv d using ints
  refine ⟨(∏ i,u i)+∏ i,v i,?_,dvd_add ((d t rfl).1.trans
    (dvd_prod_of_mem u (mem_univ t))) ((d t rfl).2.trans (dvd_prod_of_mem v (mem_univ t)))⟩
  simp only [scoreM,commonDen,Int.cast_add,Int.cast_prod,Nat.cast_prod,hu,hv,
    prod_mul_distrib,add_mul]

theorem selected_divides (p e : Fin 4 → ℕ) (prime : ∀ i,(p i).Prime) (ord : StrictMono p)
    (s : Finset (Fin 4)) (t : Fin 4) (ht : t∈s) (high : ∀ j∈s,p j≤p t)
    (odd : 2<p t) (score : scoreM p e s=2) : ∃ j,p t∣e j+1 := by
  obtain ⟨z,h,d⟩ := selected_numerator p e prime s t ht
  rw [score] at h
  have h' : z=2*(commonDen p e s:ℤ) := by exact_mod_cast h
  rw [h'] at d
  have dd : p t∣2*commonDen p e s := by exact_mod_cast d
  have div := ((prime t).dvd_mul.mp dd).resolve_left (fun h => (Nat.le_of_dvd (by decide) h).not_gt odd)
  obtain ⟨j,_,dj⟩ := ((prime t).prime.dvd_finsetProd_iff _).mp div
  by_cases hj : j∈s
  · simp only [localDen,hj,if_pos,den] at dj
    rcases (prime t).dvd_mul.mp dj with d|d
    · exact ⟨j,d⟩
    · have bad := Nat.le_of_dvd (show 0 < p j-1 by have := (prime j).one_lt; omega)
        ((prime t).dvd_of_dvd_pow d)
      have := high j hj; omega
  · simp only [localDen,hj] at dj
    rcases (prime t).dvd_mul.mp dj with d|d
    · exact ⟨j,d⟩
    · have same := (Nat.prime_dvd_prime_iff_eq (prime t) (prime j)).mp ((prime t).dvd_of_dvd_pow d)
      exact (hj (ord.injective same ▸ ht)).elim

end
end OMA.Height245212

namespace OMA.Box245212
open Finset OMA.Height245212
noncomputable section

def denBits (p q : ℕ) (b : Box) (s : Finset (Fin 4)) (i : Fin 4) : ℕ :=
  sizeHi ((b i.castSucc).hi+1) + (if i∈s then 2 else (b i.castSucc).hi)*sizeHi (baseBox p q b i).hi
def powBits (p q : ℕ) (b : Box) (i : Fin 4) : ℕ :=
  (b i.castSucc).lo*sizeLo (baseBox p q b i).lo
def comparison (p q : ℕ) (b : Box) (s : Finset (Fin 4)) (i : Fin 4) :=
  sizeHi (4*(8+((baseBox p q b i).hi-1)))+∑ j∈univ.erase i,denBits p q b s j

private theorem enc_upper {n l h : ℕ} (en : Enc l h n) : Enc 0 h n :=
  ⟨(Nat.one_le_two_pow.trans en.1),en.2⟩

theorem denBits_body {p q : ℕ} {b : Box} {v : Values} (inside : Fits b v)
    (c : Candidate p q v) (s : Finset (Fin 4)) (i : Fin 4) :
    Enc 0 (denBits p q b s i) (localDen (bases p q v) (exponents v) s i) := by
  have hp := inside_primes (p:=p) (q:=q) inside i
  have he := inside i.castSucc
  have hpos := (c.prime i).one_lt
  have add := enc_range (r:=⟨1,(b i.castSucc).hi+1⟩) (n:=exponents v i+1)
    Nat.zero_lt_one ⟨Nat.succ_le_succ (Nat.zero_le _), Nat.add_le_add_right he.2 1⟩
  by_cases hi : i∈s
  · have ep := enc_range (r:=⟨1,(baseBox p q b i).hi⟩) (n:=bases p q v i-1) Nat.zero_lt_one
      ⟨show 1≤bases p q v i-1 by omega,(Nat.sub_le _ _).trans hp.2⟩
    have two := enc_pow ep (b:=⟨2,2⟩) (e:=2) ⟨le_rfl,le_rfl⟩
    simpa [denBits,localDen,den,hi,Nat.mul_comm 2] using enc_upper (enc_mul add two)
  · have ep := enc_range (r:=⟨1,(baseBox p q b i).hi⟩) (n:=bases p q v i)
      Nat.zero_lt_one ⟨hpos.le,hp.2⟩
    have power := enc_pow ep (b:=b i.castSucc) (e:=exponents v i) he
    simpa [denBits,localDen,hi,Nat.mul_comm (sizeHi _)] using enc_upper (enc_mul add power)

theorem comparison_sound {p q : ℕ} {b : Box} {v : Values} (inside : Fits b v)
    (c : Candidate p q v) (start : ∀ i,1<(baseBox p q b i).lo) (s : Finset (Fin 4)) (i : Fin 4)
    (cmp : comparison p q b s i < powBits p q b i) :
    4*(8+(bases p q v i-1))*(∏ j∈univ.erase i,localDen (bases p q v) (exponents v) s j) <
      bases p q v i^exponents v i := by
  have hp := inside_primes (p:=p) (q:=q) inside i
  have ep := enc_range (r:=baseBox p q b i) (by have := start i; omega) hp
  have pl := enc_pow ep (inside i.castSucc)
  have co := enc_range (r:=⟨1,4*(8+((baseBox p q b i).hi-1))⟩) (n:=4*(8+(bases p q v i-1)))
    Nat.zero_lt_one ⟨by change 1≤4*(8+_); omega, by have := hp.2; change 4*(8+_)≤4*(8+_); omega⟩
  have ds := enc_prod (univ.erase i) (fun _=>0) (denBits p q b s)
    (localDen (bases p q v) (exponents v) s) (fun j _ => denBits_body inside c s j)
  apply enc_lt (enc_mul co ds) pl
  simpa only [comparison,powBits,Nat.mul_comm ((b i.castSucc).lo)] using cmp

def noExp (b : Box) (t : Range) : Bool :=
  decide (∀ j : Fin 4,(b j.castSucc).hi+1<t.lo ∨
    t.lo=t.hi ∧ (b j.castSucc).hi+1<((b j.castSucc).lo/t.lo+1)*t.lo)

theorem exp_sound {b : Box} {v : Values} {t : Range} {P : ℕ} (fit : Fits b v) (pt : t.has P)
    (h : noExp b t=true) (i : Fin 4) : ¬P∣exponents v i+1 := by
  have hi := fit i.castSucc
  have eLo := hi.1
  have eHi := hi.2
  have pLo := pt.1
  have z := of_decide_eq_true h i
  dsimp only [exponents]
  intro d
  rcases z with lt|⟨eq,no⟩
  · exact (Nat.le_of_dvd (by omega) d).not_gt (show v i.castSucc+1<P by omega)
  · have same : P=t.lo := le_antisymm (pt.2.trans_eq eq.symm) pt.1
    subst P
    obtain ⟨w,d⟩ := d
    have pp : 0<t.lo := by by_contra! h; simp [show t.lo=0 by omega] at d
    have low : (b i.castSucc).lo/t.lo < w := (Nat.div_lt_iff_lt_mul pp).mpr (by
      rw [mul_comm]; omega)
    have bad := Nat.mul_le_mul_right t.lo (Nat.succ_le_of_lt low)
    rw [mul_comm w,←d] at bad
    exact (no.trans_le bad).not_ge (Nat.add_le_add_right eHi 1)

theorem yr_antitone {p P e E : ℕ} (hp : 1<p) (pp : p≤P) (ee : e≤E) : yr P E≤yr p e := by
  have a : (1:ℚ)<p := by exact_mod_cast hp
  have b : (p:ℚ)≤P := by exact_mod_cast pp
  have f : (e:ℚ)≤E := by exact_mod_cast ee
  unfold yr
  rw [div_le_div_iff₀ (mul_pos (by linarith) (by positivity)) (mul_pos (by linarith) (by positivity))]
  have l : (P:ℚ)*((p:ℚ)-1)≤(p:ℚ)*((P:ℚ)-1) := by nlinarith
  calc
    _ = ((P:ℚ)*((p:ℚ)-1))*(e+1) := by ring
    _ ≤ ((p:ℚ)*((P:ℚ)-1))*(E+1) := mul_le_mul l (by linarith) (by positivity) (mul_nonneg (by positivity) (by linarith))
    _ = _ := by ring

def upperY (p q : ℕ) (b : Box) (i : Fin 4) := yr (baseBox p q b i).lo (b i.castSucc).lo

def strictBits (p q : ℕ) (b : Box) (i : Fin 4) : Prop :=
  ((baseBox p q b i).hi-1)*(∏ j∈univ.erase i,(baseBox p q b j).lo) <
    ∏ j∈univ.erase i,((baseBox p q b j).lo-1)*((b j.castSucc).lo+1)
instance (p q : ℕ) (b : Box) (i : Fin 4) : Decidable (strictBits p q b i) :=
  inferInstanceAs (Decidable (_<_))

theorem strictBits_sound {p q : ℕ} {b : Box} (start : ∀ i,1<(baseBox p q b i).lo)
    {i : Fin 4} (real : (baseBox p q b i).lo≤(baseBox p q b i).hi) (strict : strictBits p q b i) :
    (((baseBox p q b i).hi:ℚ)-1)*(∏ j∈univ.erase i,upperY p q b j)<1 := by
  let base (j : Fin 4) := (baseBox p q b j).lo
  let d (j : Fin 4) := (base j-1)*((b j.castSucc).lo+1)
  have dp (j : Fin 4) : 0<d j := Nat.mul_pos (Nat.sub_pos_of_lt (start j)) (Nat.zero_lt_succ _)
  have denom : (0:ℚ)<∏ j∈univ.erase i,(d j:ℚ) := prod_pos (fun j _=>by exact_mod_cast dp j)
  have y (j : Fin 4) : upperY p q b j=(base j:ℚ)/(d j:ℚ) := by
    simp only [upperY,yr,d,base,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_sub (start j).le]
  simp_rw [y]
  rw [prod_div_distrib,←mul_div_assoc,div_lt_iff₀ denom,one_mul]
  have c : (((baseBox p q b i).hi-1:ℕ):ℚ)=((baseBox p q b i).hi:ℚ)-1 := by
    rw [Nat.cast_sub ((start i).le.trans real),Nat.cast_one]
  rw [←c]
  exact_mod_cast strict

def roundLeaf (p q : ℕ) (b : Box) (s : Finset (Fin 4)) (t : Fin 4) : Bool :=
  decide ((∀ i,1<(baseBox p q b i).lo) ∧ t∈s ∧ (∀ i∈s,i≤t) ∧
    (∀ i∈s,comparison p q b s i < powBits p q b i) ∧
    (s={t} ∨ noExp b (baseBox p q b t)=true ∨ (∀ i∈s,strictBits p q b i)))

theorem round_sound {p q : ℕ} {b : Box} {s : Finset (Fin 4)} {t : Fin 4}
    (h : roundLeaf p q b s t=true) : Deny p q b := by
  obtain ⟨start,ht,high,cmp,why⟩ := of_decide_eq_true h
  intro v inside c
  have odd (i : Fin 4) : 3≤bases p q v i := c.ordered.monotone (Fin.zero_le i)
  have same := point_gap _ _ c.prime c.pos s c.score
    (fun i hi => comparison_sound inside c start s i (cmp i hi))
  rcases why with singleton|no|strict
  · subst s
    exact singleton_ne _ _ c.prime odd c.ordered.injective c.eqn t (same.trans c.score.symm)
  · obtain ⟨j,dj⟩ := selected_divides _ _ c.prime c.ordered s t ht
      (fun j hj => c.ordered.monotone (high j hj)) (odd t) same
    exact exp_sound inside (inside_primes inside t) no j dj
  · have nonneg (i : Fin 4) : 0≤yr (bases p q v i) (exponents v i) := by
      have a : (1:ℚ)<bases p q v i := by exact_mod_cast (c.prime i).one_lt
      unfold yr
      exact div_nonneg (by positivity) (mul_nonneg (by linarith) (by positivity))
    have le (i : Fin 4) : yr (bases p q v i) (exponents v i)≤upperY p q b i :=
      yr_antitone (start i) (inside_primes inside i).1 (inside i.castSucc).1
    have neg := strict_prod _ _ (fun i=>(c.prime i).one_lt) c.pos s ⟨t,ht⟩ (by
      intro i hi
      have bounds := inside_primes (p:=p) (q:=q) inside i
      apply lt_of_le_of_lt _ (strictBits_sound start (bounds.1.trans bounds.2) (strict i hi))
      have lp : (bases p q v i:ℚ) ≤ (baseBox p q b i).hi := by exact_mod_cast (inside_primes inside i).2
      have gpN : 1≤(baseBox p q b i).hi := (c.prime i).one_lt.le.trans (inside_primes inside i).2
      have gp : (1:ℚ)≤(baseBox p q b i).hi := by exact_mod_cast gpN
      exact mul_le_mul (by linarith) (prod_le_prod (fun j _ => nonneg j) (fun j _ => le j))
        (prod_nonneg (fun j _=> nonneg j)) (by linarith))
    exact (same.trans c.score.symm).not_lt neg

end
end OMA.Box245212

namespace OMA.LastDigit245212
open Finset ArithmeticFunction OMA.Smooth245212 OMA.Abundance245212
open scoped ArithmeticFunction.sigma

def digitSum (p A S e : ℕ) := ∑ j∈range e,p^j*(A*(j+1)+S)
def denom (A S T d : ℕ) := 2*T*(d+1)-(A*(d+1)+S)

private theorem digit_pos {p A S d : ℕ} (hs : 0<S) (hd : 0<d) :
    0<digitSum p A S d := by
  apply sum_pos' (fun _ _ => Nat.zero_le _)
  exact ⟨0,mem_range.mpr hd,by simpa using (show 0<A+S by omega)⟩

private theorem geom (p e : ℕ) (hp : 1≤p) :
    (∑ j∈range e,p^j)*(p-1)+1=p^e := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [sum_range_succ,add_mul,pow_succ]
    have v := congrArg (fun x : ℕ => p^e*x) (Nat.sub_add_cancel hp)
    simp only [Nat.mul_add,Nat.mul_one] at v
    nlinarith only [ih,v]

theorem digits {p A S T d : ℕ} (hp : 1<p) (hs : 0<S) (hd : 0<d)
    (eq : digitSum p A S (d+1)=p^d*(2*T*(d+1))) :
    0<denom A S T d ∧ denom A S T d*(p-1)<A*d+S ∧ A*d+S≤denom A S T d*p ∧
      (1<d → A*d+S<denom A S T d*p) := by
  have dp := digit_pos (p:=p) (A:=A) hs hd
  have h := eq
  rw [digitSum,sum_range_succ,←digitSum] at h
  have co : A*(d+1)+S<2*T*(d+1) := by
    by_contra! v
    have := Nat.mul_le_mul_left (p^d) v
    omega
  have cut := Nat.sub_add_cancel co.le
  change denom A S T d+_= _ at cut
  have rest : digitSum p A S d=p^d*denom A S T d := by
    rw [←cut] at h
    rw [Nat.mul_add (p^d) (denom A S T d)] at h
    exact Nat.add_right_cancel h
  have ppos : 0<p^d := by positivity
  have up : digitSum p A S d ≤ (∑ j∈range d,p^j)*(A*d+S) := by
    rw [sum_mul]
    exact sum_le_sum (fun j hj => Nat.mul_le_mul_left _ (Nat.add_le_add_right
      (Nat.mul_le_mul_left A (mem_range.mp hj)) S))
  have sm := Nat.mul_le_mul_right (p-1) up
  have strict : denom A S T d*(p-1)<A*d+S := by
    apply Nat.lt_of_mul_lt_mul_left (a:=p^d)
    calc
      p^d*(denom A S T d*(p-1)) = digitSum p A S d*(p-1) := by rw [rest,mul_assoc]
      _ ≤ ((∑ j∈range d,p^j)*(p-1))*(A*d+S) := by simpa only [mul_right_comm] using sm
      _ < p^d*(A*d+S) := Nat.mul_lt_mul_of_pos_right (by have := geom p d hp.le; omega) (by omega)
  refine ⟨Nat.sub_pos_of_lt co,strict,?_⟩
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  rw [digitSum,sum_range_succ,←digitSum,pow_succ,mul_assoc] at rest
  have v : (A*(k+1)+S)*p^k ≤ (denom A S T (k+1)*p)*p^k := by
    nlinarith only [rest, Nat.zero_le (digitSum p A S k)]
  have pk : 0<p^k := by positivity
  exact ⟨(le_of_mul_le_mul_right v pk), fun hk =>
    (lt_of_mul_lt_mul_right (by nlinarith only [rest, digit_pos (p:=p) (A:=A) hs (by omega : 0<k)] :
      (A*(k+1)+S)*p^k < (denom A S T (k+1)*p)*p^k) (Nat.zero_le _))⟩

theorem balance_digits {p m d : ℕ} (hm : 0 < m) (hp : Nat.Prime p) (cop : m.Coprime p) (hd : 0<d)
    (eq : OeisA245212.a (m*p^d)=(σ 1 (m*p^d):ℤ)) :
    let A := W m; let S := σ 1 m; let T := m*(σ 0 m);
    0<denom A S T d ∧ denom A S T d*(p-1)<A*d+S ∧ A*d+S≤denom A S T d*p ∧
      (1<d → A*d+S<denom A S T d*p) := by
  have b := balance (mul_ne_zero hm.ne' (pow_ne_zero _ hp.ne_zero)) eq
  have c := cop.pow_right d
  rw [w_mult.map_mul_of_coprime c,isMultiplicative_sigma.map_mul_of_coprime c,
    isMultiplicative_sigma.map_mul_of_coprime c,w_pow hp,sigma_one_apply_prime_pow hp,
    sigma_zero_apply_prime_pow hp] at b
  have spos : 0<σ 1 m := by
    rw [sigma_one_apply]
    exact sum_pos' (fun _ _ => Nat.zero_le _) ⟨1,Nat.one_mem_divisors.mpr hm.ne',by decide⟩
  apply digits hp.one_lt spos hd
  unfold digitSum
  simp_rw [show ∀ j:ℕ,p^j*(W m*(j+1)+σ 1 m)=W m*(p^j*(j+1))+σ 1 m*p^j by intro j; ring]
  rw [sum_add_distrib,←mul_sum,←mul_sum]
  simpa only [mul_comm,mul_left_comm,mul_assoc] using b

end OMA.LastDigit245212

namespace OMA.OddCofactor245212
open Finset ArithmeticFunction OMA.Smooth245212 OMA.Abundance245212
open scoped ArithmeticFunction.sigma

/-- Each new prime divides the sum of the two divisor moments of the remaining cofactor. -/
theorem last_dvd {m p d : ℕ} (hm : 0 < m) (hp : Nat.Prime p) (cop : m.Coprime p)
    (hd : 0<d) (eq : OeisA245212.a (m*p^d)=(σ 1 (m*p^d):ℤ)) : p∣W m+σ 1 m := by
  have b := balance (mul_ne_zero hm.ne' (pow_ne_zero _ hp.ne_zero)) eq
  have c := cop.pow_right d
  rw [w_mult.map_mul_of_coprime c,isMultiplicative_sigma.map_mul_of_coprime c,
    w_pow hp,sigma_one_apply_prime_pow hp] at b
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  have b' := congrArg (fun t : ℕ => (t:ZMod p)) b
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_sum,Nat.cast_pow,Nat.cast_ofNat,
    Nat.cast_one,ZMod.natCast_self] at b' ⊢
  rw [sum_range_succ',sum_range_succ'] at b'
  simp [zero_pow hd.ne',pow_succ] at b'
  exact b'


end OMA.OddCofactor245212

namespace OMA.Large245212
open OMA.Smooth245212 OMA.Moving245212 Finset

def scale (R : ℕ) : ℚ := (R:ℚ)/((R:ℚ)-1)
theorem y_both {r d : ℕ} (hr : 1<r) :
    1/((d:ℚ)+1)≤Y r (some d) ∧ Y r (some d)≤ scale r/((d:ℚ)+1) := by
  have rr : (1:ℚ)<r := by exact_mod_cast hr
  rw [y_avg hr]
  have low : (1:ℚ) ≤ ∑ i∈range (d+1),(r:ℚ)⁻¹^i := by
    simpa using single_le_sum (s:=range (d+1)) (f:=fun i => (r:ℚ)⁻¹^i)
      (fun i _ => by positivity) (mem_range.mpr (by omega : 0<d+1))
  have up : (∑ i∈range (d+1),(r:ℚ)⁻¹^i) ≤ (r:ℚ)/((r:ℚ)-1) := by
    have u := geom_sum_Ico_le_of_lt_one (m:=0) (n:=d+1) (by positivity : (0:ℚ)≤(r:ℚ)⁻¹)
      (inv_lt_one_of_one_lt₀ rr)
    rw [Nat.Ico_zero_eq_range,pow_zero] at u
    rwa [show (1:ℚ)-(r:ℚ)⁻¹=(r-1)/r by field_simp,div_div_eq_mul_div,one_mul] at u
  exact ⟨by gcongr, by dsimp [scale]; gcongr⟩

end OMA.Large245212

namespace OMA.Large245212
open OMA.Smooth245212 OMA.LastDigit245212 Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma Function

def tax (p e : ℕ) := (e+1)*p^e
def sig (p e : ℕ) := (p^(e+1)-1)/(p-1)
def wt (p e : ℕ) := (p*tax p e-sig p e)/(p-1)

theorem moments {p : ℕ} (hp : Nat.Prime p) (e : ℕ) :
    sig p e=σ 1 (p^e) ∧ wt p e=W (p^e) := by
  have pp : 0<p-1 := by have := hp.one_lt; omega
  have s : sig p e=σ 1 (p^e) := by
    rw [sig,sigma_one_apply_prime_pow hp,←geom_sum_mul_of_one_le hp.pos (e+1),Nat.mul_div_cancel _ pp]
  refine ⟨s,?_⟩
  have w : (p-1)*W (p^e)+σ 1 (p^e)=p*tax p e := by
    clear s
    rw [w_pow hp,sigma_one_apply_prime_pow hp,tax]
    induction e with
    | zero => simp; omega
    | succ k ih =>
      rw [sum_range_succ _ (k+1),sum_range_succ _ (k+1),mul_add,pow_succ]
      have add := Nat.sub_add_cancel (show 1≤p from hp.pos)
      nlinarith only [ih,congrArg (fun z:ℕ => z*(p^k*p)*(k+2)) add]
  rw [wt,s,←w,Nat.add_sub_cancel,Nat.mul_div_cancel_left _ pp]

def candidate (A S T d : ℕ) := (A*d+S-1)/denom A S T d+1
theorem force {A S T d p : ℕ} (hs : 0<S) (hp : 1<p) (hD : 0<denom A S T d)
    (lo : denom A S T d*(p-1)<A*d+S) (hi : A*d+S≤denom A S T d*p) :
    candidate A S T d=p := by
  unfold candidate
  have low : p-1≤(A*d+S-1)/denom A S T d := (Nat.le_div_iff_mul_le hD).2 (by rw [mul_comm]; omega)
  have up : (A*d+S-1)/denom A S T d<p := (Nat.div_lt_iff_lt_mul hD).2
    (by rw [Nat.mul_comm p (denom A S T d)]; omega)
  omega

end OMA.Large245212

namespace OMA.PrefixLeaf245212
open OMA.LastDigit245212 OMA.Large245212 OMA.Smooth245212 ArithmeticFunction
open scoped ArithmeticFunction.sigma
open OMA.Large245212 (force moments)

/-- Intersect the natural interval with the single half-space v*d ≤ w. -/
def trim (B : ℕ×ℕ) (v w : ℤ) : ℕ×ℕ :=
  if 0<v then
    if w<0 then (1,0) else (B.1,min B.2 (w/v).toNat)
  else if v<0 then (max B.1 (-(w/(-v))).toNat,B.2)
  else if w<0 then (1,0) else B

theorem trim_sound {B : ℕ×ℕ} {v w : ℤ} {d : ℕ} (blo : B.1≤d) (bhi : d≤B.2)
    (eq : v*(d:ℤ)≤w) : (trim B v w).1≤d ∧ d≤(trim B v w).2 := by
  unfold trim
  split_ifs with pos neg vn wn
  · have := mul_nonneg pos.le (Int.natCast_nonneg d); omega
  · have v1 : (d:ℤ)≤w/v := (Int.le_ediv_iff_mul_le pos).2 (by simpa [mul_comm] using eq)
    exact ⟨blo,le_min bhi (by omega)⟩
  · have v1 : -(d:ℤ)≤w/(-v) := (Int.le_ediv_iff_mul_le (by omega)).2 (by nlinarith only [eq])
    exact ⟨max_le blo (by omega),bhi⟩
  · have : v=0 := by omega
    simp [this] at eq
    omega
  · exact ⟨blo,bhi⟩

private def slope (A T u : ℕ) : ℤ := ((u:ℤ)+1)*A-2*u*T
private def offset (A S u : ℕ) : ℤ := (A:ℤ)-((u:ℤ)+1)*S

def bounds (A S T rl rh gl gh : ℕ) : ℕ×ℕ :=
  let cap := Nat.log rl (A+rh*S)
  let v := slope A T rh
  let w := offset A S rh
  let B := trim (gl,min gh cap) v (w-v)
  let u := rl-1
  let v' := slope A T u
  let w' := offset A S u
  trim B (-v') (v'-w'-1)

private theorem bounds_sound {A S T rl rh gl gh r d : ℕ} (base : 1<rl)
    (lo : rl≤r) (hi : r≤rh) (dlo : gl≤d) (dhi : d≤gh)
    (positive : 0<denom A S T d)
    (lower : denom A S T d*(r-1)<A*d+S) (upper : A*d+S≤denom A S T d*r)
    (power : r^d≤A+rh*S) :
    (bounds A S T rl rh gl gh).1≤d ∧ d≤(bounds A S T rl rh gl gh).2 := by
  have cap : d≤Nat.log rl (A+rh*S) :=
    Nat.le_log_of_pow_le base ((Nat.pow_le_pow_left lo d).trans power)
  have eq : denom A S T d+(A*(d+1)+S)=2*T*(d+1) := by
    apply Nat.sub_add_cancel
    exact (Nat.sub_pos_iff_lt.mp positive).le
  have lm : denom A S T d*(rl-1)<A*d+S :=
    lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right lo 1)) lower
  have um : A*d+S≤denom A S T d*rh := upper.trans (Nat.mul_le_mul_left _ hi)
  have eq' : (denom A S T d:ℤ)+(A*(d+1)+S)=2*T*(d+1) := by exact_mod_cast eq
  have um' : (A:ℤ)*d+S≤denom A S T d*rh := by exact_mod_cast um
  have lm' : (denom A S T d:ℤ)*((rl-1:ℕ):ℤ)<(A:ℤ)*d+S := by exact_mod_cast lm
  have cm := congrArg (fun z:ℤ=>z*(rh:ℤ)) eq'
  have f := trim_sound (B:=(gl,min gh (Nat.log rl (A+rh*S)))) dlo (le_min dhi cap)
    (v:=slope A T rh) (w:=offset A S rh-slope A T rh) (by
      unfold slope offset; nlinarith only [um',cm])
  apply trim_sound f.1 f.2
  unfold slope offset
  have c := congrArg (fun z:ℤ=>z*((rl-1:ℕ):ℤ)) eq'
  have lm'' : (denom A S T d:ℤ)*((rl-1:ℕ):ℤ)+1≤(A:ℤ)*d+S := by omega
  nlinarith only [lm'',c]

/-- Exclude one exponent using the only possible last prime. Full
    divisor moments are needed only after the inexpensive tests pass. -/
def rejects (A S T rl rh d : ℕ) : Bool :=
  let D := denom A S T d
  let r := candidate A S T d
  D==0 || r<rl || rh<r || (A+S)%r != 0 ||
    (1<d && A*d+S==D*r) ||
    A*wt r d+S*sig r d != 2*T*OMA.Large245212.tax r d

/-- True certifies that the given prime and exponent window contains no
    solution with the specified cofactor moments. -/
def exact (A S T rl rh gl gh : ℕ) : Bool :=
  let B := bounds A S T rl rh gl gh
  (List.range' B.1 (B.2+1-B.1)).all (rejects A S T rl rh)

theorem sound {A S T rl rh gl gh r d : ℕ} (base : 1<rl)
    (lo : rl≤r) (hi : r≤rh) (dlo : gl≤d) (dhi : d≤gh) (hs : 0<S)
    (positive : 0<denom A S T d)
    (lower : denom A S T d*(r-1)<A*d+S) (upper : A*d+S≤denom A S T d*r)
    (strict : 1<d → A*d+S<denom A S T d*r)
    (powBound : r^d≤A+rh*S) (dvd : r∣A+S)
    (eq : A*wt r d+S*sig r d=2*T*OMA.Large245212.tax r d) : exact A S T rl rh gl gh=false := by
  have fit := bounds_sound base lo hi dlo dhi positive lower upper powBound
  have cand := OMA.Large245212.force hs (lt_of_lt_of_le base lo) positive lower upper
  have no : rejects A S T rl rh d=false := by
    simp [rejects,cand,Nat.mod_eq_zero_of_dvd dvd,eq,positive.ne',not_lt.mpr lo,not_lt.mpr hi]
    exact fun gt=>(strict gt).ne
  cases h : exact A S T rl rh gl gh with
  | false => rfl
  | true =>
    have hit : d∈List.range' (bounds A S T rl rh gl gh).1
          ((bounds A S T rl rh gl gh).2+1-(bounds A S T rl rh gl gh).1) := by
      exact List.mem_range'.mpr ⟨d-(bounds A S T rl rh gl gh).1,by omega,by simp; omega⟩
    have bad := List.all_eq_true.mp h d hit
    simp [no] at bad

/-- A genuine odd prime-power extension satisfying the divisor equality
    must survive the exact-prefix test. No primality of the other factors
    of the cofactor is needed. -/
theorem extension {m rl rh gl gh r d : ℕ} (hm : 0 < m) (hp : r.Prime) (hp2 : r ≠ 2)
    (cop : m.Coprime r) (base : 1<rl) (lo : rl≤r) (hi : r≤rh)
    (dlo : gl≤d) (dhi : d≤gh) (dp : 0<d)
    (eq : OeisA245212.a (m*r^d)=(σ 1 (m*r^d):ℤ)) :
    exact (W m) (σ 1 m) (m*(σ 0 m)) rl rh gl gh=false := by
  obtain ⟨pos,lower,upper,strict⟩ := balance_digits hm hp cop dp eq
  have sp : 0<σ 1 m := by
    rw [sigma_one_apply]
    exact Finset.sum_pos' (fun _ _=>Nat.zero_le _)
      ⟨1,Nat.one_mem_divisors.mpr hm.ne',by decide⟩
  apply sound base lo hi dlo dhi sp pos lower upper strict
  · have h := OMA.PrimePowerDiv245212.cofactor_bound hm hp hp2 cop d eq
    have le := Int.natAbs_sub_le (W m:ℤ) (((r:ℤ)-1)*(σ 1 m:ℤ))
    rw [Int.natAbs_mul] at le
    have sub : (r:ℤ)-1=((r-1:ℕ):ℤ) := by omega
    rw [sub] at le h
    simp only [Int.natAbs_natCast] at le
    exact (h.trans le).trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega : r-1≤rh)) _)
  · exact OMA.OddCofactor245212.last_dvd hm hp cop dp eq
  · have b := OMA.Abundance245212.balance (mul_ne_zero hm.ne' (pow_ne_zero _ hp.ne_zero)) eq
    rw [w_mult.map_mul_of_coprime (cop.pow_right d),
      isMultiplicative_sigma.map_mul_of_coprime (cop.pow_right d),
      isMultiplicative_sigma.map_mul_of_coprime (cop.pow_right d),sigma_zero_apply_prime_pow hp] at b
    obtain ⟨ss,ww⟩ := OMA.Large245212.moments hp d
    rw [ss,ww,OMA.Large245212.tax]
    nlinarith only [b]

/-- Closed products for a cofactor consisting of three distinct prime
    powers; these are the arguments passed to the arithmetic leaf. -/
theorem triple {p q z : ℕ} (hp : p.Prime) (hq : q.Prime) (hz : z.Prime)
    (pq : p≠q) (pz : p≠z) (qz : q≠z) (i j k : ℕ) :
    let m := p^i*q^j*z^k
    W m=wt p i*wt q j*wt z k ∧ (σ 1 m)=sig p i*sig q j*sig z k ∧
      m*(σ 0 m)=OMA.Large245212.tax p i*OMA.Large245212.tax q j*OMA.Large245212.tax z k := by
  let m := p^i*q^j*z^k
  have c1 := (((Nat.coprime_primes hp hq).mpr pq).pow_left i).pow_right j
  have c2 := ((((Nat.coprime_primes hp hz).mpr pz).pow_left i).pow_right k).mul_left
    ((((Nat.coprime_primes hq hz).mpr qz).pow_left j).pow_right k)
  obtain ⟨s1,w1⟩ := OMA.Large245212.moments hp i
  obtain ⟨s2,w2⟩ := OMA.Large245212.moments hq j
  obtain ⟨s3,w3⟩ := OMA.Large245212.moments hz k
  dsimp only
  rw [w_mult.map_mul_of_coprime c2,w_mult.map_mul_of_coprime c1,
    isMultiplicative_sigma.map_mul_of_coprime c2,isMultiplicative_sigma.map_mul_of_coprime c1,
    isMultiplicative_sigma.map_mul_of_coprime c2,isMultiplicative_sigma.map_mul_of_coprime c1]
  simp only [s1,s2,s3,w1,w2,w3,sigma_zero_apply_prime_pow hp,sigma_zero_apply_prime_pow hq,
    sigma_zero_apply_prime_pow hz,OMA.Large245212.tax,true_and]
  ring

end OMA.PrefixLeaf245212

namespace OMA.Box245212
open OMA.Smooth245212 Finset OMA.Large245212
open scoped ArithmeticFunction.sigma

def Range.entries (r : Range) := List.range' r.lo (r.hi+1-r.lo)
theorem Range.mem_entries {r : Range} {v : ℕ} (h : r.has v) : v∈r.entries := by
  rcases h with ⟨l,u⟩
  exact List.mem_range'_1.mpr ⟨l,by omega⟩

def exactBlock (p q : ℕ) (b : Box) : Bool :=
  decide (1<(b 4).lo) &&
  (b 0).entries.all (fun k => (b 1).entries.all (fun e => (b 2).entries.all (fun f =>
    PrefixLeaf245212.exact (wt 3 k*wt p e*wt q f) (sig 3 k*sig p e*sig q f)
      (tax 3 k*tax p e*tax q f) (b 4).lo (b 4).hi (b 3).lo (b 3).hi)))

theorem prefix_sound {p q : ℕ} {b : Box} (yes : exactBlock p q b=true) : Deny p q b := by
  intro v inside c
  have h := Bool.and_eq_true_iff.mp yes
  have check0 := List.all_eq_true.mp h.2 (v 0) (Range.mem_entries (inside 0))
  have check1 := List.all_eq_true.mp check0 (v 1) (Range.mem_entries (inside 1))
  have check2 := List.all_eq_true.mp check1 (v 2) (Range.mem_entries (inside 2))
  let m := 3^(v 0)*p^(v 1)*q^(v 2)
  have hp : p.Prime := c.prime 1
  have hq : q.Prime := c.prime 2
  have hr : (v 4).Prime := c.prime 3
  have small : 3<p := c.ordered (show (0:Fin 4)<1 by decide)
  have pq : p<q := c.ordered (show (1:Fin 4)<2 by decide)
  have qr : q<v 4 := c.ordered (show (2:Fin 4)<3 by decide)
  have same : total (bases p q v) (exponents v)=m*(v 4)^(v 3) := by
    simp [total,bases,exponents,m,Fin.prod_univ_four]
  have s := c.eqn; dsimp only at s; rw [same] at s
  have cop : m.Coprime (v 4) :=
    (((Nat.coprime_primes Nat.prime_three hr).mpr (by omega)).pow_left _).mul_left
      (((Nat.coprime_primes hp hr).mpr (by omega)).pow_left _) |>.mul_left
        (((Nat.coprime_primes hq hr).mpr qr.ne).pow_left _)
  have mp : 0 < m := mul_pos (mul_pos (pow_pos (by decide) _) (pow_pos hp.pos _)) (pow_pos hq.pos _)
  have no := PrefixLeaf245212.extension mp
    hr (by omega) cop (of_decide_eq_true h.1) (inside 4).1 (inside 4).2 (inside 3).1 (inside 3).2
    (c.pos 3) s
  have triple := PrefixLeaf245212.triple Nat.prime_three hp hq small.ne (by omega) pq.ne (v 0) (v 1) (v 2)
  dsimp only at triple
  dsimp only [m] at no
  rw [triple.1,triple.2.1,triple.2.2] at no
  exact Bool.noConfusion (check2.symm.trans no)

end OMA.Box245212

namespace OMA.DigitBox245212
open Finset OMA.Box245212 OMA.Smooth245212 OMA.Moving245212 OMA.LastDigit245212 ArithmeticFunction
open scoped ArithmeticFunction.sigma
open OMA.PrefixLeaf245212 (trim_sound)
open OMA.Large245212 (y_both)

def den (x y : ℚ) (d : ℕ) := ((d:ℚ)+1)*(2-x)-y
def num (x y : ℚ) (d : ℕ) := (d:ℚ)*x+y

theorem digitsQ {r d : ℕ} (hp : r.Prime) (hd : 0<d) {x y : ℚ} (hx : 0≤x) (hy : 0<y)
    (value : x*X r (some d)+y*Y r (some d)=2) :
    0<den x y d ∧ ((r:ℚ)-1)*den x y d<num x y d ∧ num x y d≤r*den x y d := by
  let A := x.num.toNat*y.den
  let S := y.num.toNat*x.den
  let T := x.den*y.den
  have pos : 0<T := Nat.mul_pos x.den_pos y.den_pos
  have sp : 0<S := Nat.mul_pos (by have := Rat.num_pos.mpr hy; omega) x.den_pos
  have scale (z : ℚ) (hz : 0≤z) : (z.num.toNat:ℚ)=z*z.den := by
    rw [Rat.mul_den_eq_num]
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr hz)
  have a : (A:ℚ)=x*T := by simp only [A,T,Nat.cast_mul,scale x hx,mul_assoc]
  have s : (S:ℚ)=y*T := by simp only [S,T,Nat.cast_mul,scale y hy.le]; ring
  have eq : A*W (r^d)+S*σ 1 (r^d)=2*T*((d+1)*r^d) := by
    exact_mod_cast (show (A:ℚ)*(W (r^d):ℚ)+(S:ℚ)*(σ 1 (r^d):ℚ)=2*(T:ℚ)*(((d:ℚ)+1)*(r:ℚ)^d) from by
      rw [a,s,←x_factor hp,←y_factor hp]
      linear_combination (T:ℚ)*(((d:ℚ)+1)*(r:ℚ)^d)*value)
  have form : digitSum r A S (d+1)=r^d*(2*T*(d+1)) := by
    rw [w_pow hp,sigma_one_apply_prime_pow hp] at eq
    unfold digitSum
    simp_rw [show ∀ j:ℕ,r^j*(A*(j+1)+S)=A*(r^j*(j+1))+S*r^j by intro j; ring]
    rw [sum_add_distrib,←mul_sum,←mul_sum]
    nlinarith only [eq]
  obtain ⟨pd,lo,hi,_⟩ := digits hp.one_lt sp hd form
  have eqD : denom A S T d+(A*(d+1)+S)=2*T*(d+1) := Nat.sub_add_cancel (Nat.sub_pos_iff_lt.mp pd).le
  have dQ : (denom A S T d:ℚ)=den x y d*T := by
    have e : (denom A S T d:ℚ)+((A:ℚ)*(d+1)+S)=2*(T:ℚ)*(d+1) := by exact_mod_cast eqD
    rw [a,s] at e; unfold den; linarith only [e]
  have nQ : (A:ℚ)*d+S=num x y d*T := by rw [a,s]; unfold num;ring
  have lo' : (denom A S T d:ℚ)*((r-1:ℕ):ℚ)<(A:ℚ)*d+S := by exact_mod_cast lo
  have hi' : (A:ℚ)*d+S≤(denom A S T d:ℚ)*r := by exact_mod_cast hi
  have posT : (0:ℚ)<T := by exact_mod_cast pos
  have posD : 0<(denom A S T d:ℚ) := by exact_mod_cast pd
  rw [dQ] at posD
  rw [dQ,nQ,Nat.cast_sub hp.pos,Nat.cast_one] at lo'
  rw [dQ,nQ] at hi'
  refine ⟨pos_of_mul_pos_left posD posT.le,?_,?_⟩
  · exact lt_of_mul_lt_mul_right (show (((r:ℚ)-1)*den x y d)*T<num x y d*T by linarith only [lo']) posT.le
  · exact le_of_mul_le_mul_right (show num x y d*T≤((r:ℚ)*den x y d)*T by linarith only [hi']) posT

private def cut (R : Range) (strict : Bool) (v w : ℚ) : Range :=
  let z := w-v
  let a := v.num*z.den
  let b := z.num*v.den
  let c := OMA.PrefixLeaf245212.trim (R.lo,R.hi) a (b-(if strict then 1 else 0))
  ⟨c.1,c.2⟩

private theorem cut_ok {R : Range} {d : ℕ} {v w : ℚ} (hr : R.has d) (strict : Bool)
    (eq : if strict then v*((d:ℚ)+1)<w else v*((d:ℚ)+1)≤w) : (cut R strict v w).has d := by
  let z := w-v
  let a := v.num*(z.den:ℤ)
  let b := z.num*(v.den:ℤ)
  have e1 : (a:ℚ)*(d:ℚ)=(v*d)*((v.den:ℚ)*z.den) := by
    simp only [a,Int.cast_mul,Int.cast_natCast,←Rat.mul_den_eq_num]; ring
  have e2 : (b:ℚ)=z*((v.den:ℚ)*z.den) := by
    simp only [b,Int.cast_mul,Int.cast_natCast,←Rat.mul_den_eq_num]; ring
  have pos : 0<(v.den:ℚ)*z.den := by exact_mod_cast Nat.mul_pos v.den_pos z.den_pos
  apply OMA.PrefixLeaf245212.trim_sound hr.1 hr.2
  change a*d≤b-(if strict then 1 else 0)
  cases strict with
  | false =>
    simp only [Bool.false_eq_true,if_false,sub_zero] at eq ⊢
    have e : (a:ℚ)*d≤(b:ℚ) := by
      rw [e1,e2]
      apply mul_le_mul_of_nonneg_right _ pos.le
      dsimp [z]; linarith only [eq]
    exact_mod_cast e
  | true =>
    simp only [if_true] at eq ⊢
    have e : (a:ℚ)*d<(b:ℚ) := by
      rw [e1,e2]
      apply mul_lt_mul_of_pos_right _ pos
      dsimp [z]; linarith only [eq]
    have e' : a*d<b := by exact_mod_cast e
    omega

def co (f : Band→Band→ℚ) (p q : ℕ) (b : Box245212.Box) (i : Fin 4) :=
  ∏ j∈univ.erase i,factor f p q b j

private def digitAt (p q : ℕ) (b : Box245212.Box) (i : Fin 4) : Range :=
  let x := co xl p q b i
  let y := co yl p q b i
  let u := co xu p q b i
  let v := co yu p q b i
  let P : ℚ := (baseBox p q b i).hi
  let r : ℚ := (baseBox p q b i).lo
  let R := cut (b i.castSucc) true (x-2) (-y)
  let R := cut R false ((P+1)*x-2*P) (x-(P+1)*y)
  cut R true (2*(r-1)-r*u) (r*v-u)

theorem facts {p q : ℕ} {b : Box245212.Box} {v : Values}
    (cand : Candidate p q v) (fit : Fits b v) (start : ∀ i,1<(baseBox p q b i).lo)
    (i : Fin 4) (l h : ℕ) (lp : 1≤l) (hl : l≤bases p q v i) (hh : bases p q v i≤h) :
    let d := exponents v i
    let X := co xl p q b i; let Y := co yl p q b i
    let U := co xu p q b i; let V := co yu p q b i
    0<den X Y d ∧ num X Y d≤h*den X Y d ∧ ((l:ℚ)-1)*den U V d<num U V d := by
  let d := exponents v i
  let r := bases p q v i
  let xj (j : Fin 4) := X (bases p q v j) (some (exponents v j))
  let yj (j : Fin 4) := Y (bases p q v j) (some (exponents v j))
  let x := ∏ j∈univ.erase i,xj j
  let y := ∏ j∈univ.erase i,yj j
  have bx := moments fit start
  have yl0 (j : Fin 4) : 0<yj j := by
    exact (show (0:ℚ)<1/((exponents v j:ℚ)+1) by positivity).trans_le
      (OMA.Large245212.y_both (cand.prime j).one_lt).1
  have xl0 : 0≤x := prod_nonneg (fun j _=>(bx j).1.trans (bx j).2.1)
  have yp : 0<y := prod_pos (fun j _=>yl0 j)
  have xl' : co xl p q b i≤x := prod_le_prod (fun j _=>(bx j).1) (fun j _=>(bx j).2.1)
  have xu' : x≤co xu p q b i := prod_le_prod (fun j _=>(bx j).1.trans (bx j).2.1) (fun j _=>(bx j).2.2.1)
  have yl' : co yl p q b i≤y := prod_le_prod (fun j _=>(bx j).2.2.2.1) (fun j _=>(bx j).2.2.2.2.1)
  have yu' : y≤co yu p q b i := prod_le_prod (fun j _=>(yl0 j).le) (fun j _=>(bx j).2.2.2.2.2)
  have eq : x*X r (some d)+y*Y r (some d)=2 := by
    change (∏ j∈univ.erase i,xj j)*xj i+(∏ j∈univ.erase i,yj j)*yj i=2
    rw [prod_erase_mul _ _ (mem_univ i),prod_erase_mul _ _ (mem_univ i)]
    exact cand.score
  obtain ⟨dp,low,up⟩ := digitsQ (cand.prime i) (cand.pos i) xl0 yp eq
  have ph : (r:ℚ)≤(h:ℚ) := by exact_mod_cast hh
  have pl : (l:ℚ)≤(r:ℚ) := by exact_mod_cast hl
  have ps : (1:ℚ)≤l := by exact_mod_cast lp
  have a1 : den x y d≤den (co xl p q b i) (co yl p q b i) d := by
    unfold den; nlinarith only [xl',yl',mul_nonneg (sub_nonneg.mpr xl') (Nat.cast_nonneg (α:=ℚ) d)]
  have a2 : den (co xu p q b i) (co yu p q b i) d≤den x y d := by
    unfold den; nlinarith only [xu',yu',mul_nonneg (sub_nonneg.mpr xu') (Nat.cast_nonneg (α:=ℚ) d)]
  have b1 : num (co xl p q b i) (co yl p q b i) d≤num x y d :=
    add_le_add (mul_le_mul_of_nonneg_left xl' (Nat.cast_nonneg d)) yl'
  have b2 : num x y d≤num (co xu p q b i) (co yu p q b i) d :=
    add_le_add (mul_le_mul_of_nonneg_left xu' (Nat.cast_nonneg d)) yu'
  have h1 := dp.trans_le a1
  have h2 := (b1.trans up).trans (mul_le_mul ph a1 dp.le (Nat.cast_nonneg h))
  have h3 := ((mul_le_mul_of_nonneg_left a2 (show 0≤(l:ℚ)-1 by linarith)).trans
    (mul_le_mul_of_nonneg_right (sub_le_sub_right pl 1) dp.le)).trans_lt (low.trans_le b2)
  exact ⟨h1,h2,h3⟩

private theorem digitAt_ok {p q : ℕ} {b : Box245212.Box} {v : Values}
    (cand : Candidate p q v) (fit : Fits b v) (start : ∀ i,1<(baseBox p q b i).lo)
    (i : Fin 4) : (digitAt p q b i).has (exponents v i) := by
  have sp := inside_primes (p:=p) (q:=q) fit i
  obtain ⟨h1,h2,h3⟩ := facts cand fit start i _ _ (start i).le sp.1 sp.2
  dsimp only [exponents] at h1 h2 h3
  unfold digitAt
  refine cut_ok (cut_ok (cut_ok (fit i.castSucc) true ?_) false ?_) true ?_
  · dsimp only [den] at h1; simp only [if_true]; linarith only [h1]
  · dsimp only [den,num] at h2; simp only [Bool.false_eq_true,if_false]; linarith only [h2]
  · dsimp only [den,num] at h3; simp only [if_true]; linarith only [h3]

private def rawBox (p q : ℕ) (b : Box245212.Box) : Box245212.Box :=
  Fin.lastCases (b 4) (digitAt p q b)

/-- Tighten the four exponent ranges simultaneously, using the initial
    box to enclose each of the four cofactors. -/
def digit (p q : ℕ) (b : Box245212.Box) : Option Box245212.Box :=
  let out := rawBox p q b
  if ∀ i,(out i).lo≤(out i).hi then some out else none

theorem digit_sound {p q : ℕ} {v : Values} {b : Box245212.Box}
    (c : Candidate p q v) (fit : Fits b v) (start : ∀ i,1<(baseBox p q b i).lo) :
    ∃ b',digit p q b=some b' ∧ Fits b' v := by
  have f : Fits (rawBox p q b) v := by
    intro i
    refine Fin.lastCases ?_ (fun j=>?_) i
    · exact fit 4
    · simpa [rawBox,exponents] using digitAt_ok c fit start j
  exact ⟨_,if_pos (fun i=>(f i).1.trans (f i).2),f⟩

end OMA.DigitBox245212

namespace OMA.DigitBox245212
open OMA.Box245212 OMA.Moving245212

private theorem extreme (x y z k : ℚ) {E : Range} {d : ℕ} (fit : E.has d) :
    let F (a : ℕ) := z*den x y a+k*num x y a
    F d≤F E.lo ∨ F d≤F E.hi := by
  have dl : (E.lo:ℚ)≤d := by exact_mod_cast fit.1
  have dh : (d:ℚ)≤E.hi := by exact_mod_cast fit.2
  by_cases sign : 0≤z*(2-x)+k*x
  · right; unfold den num
    nlinarith only [mul_nonneg (sub_nonneg.mpr dh) sign]
  · left; unfold den num
    nlinarith only [mul_nonneg (sub_nonneg.mpr dl) (neg_nonneg.mpr (le_of_not_ge sign))]

private def ceilQ (x y : ℚ) (d : ℕ) := ⌈num x y d/den x y d⌉₊

private def lowPrime (x y : ℚ) (E R : Range) : Range :=
  if den x y E.lo≤0 ∧ den x y E.hi≤0 then ⟨1,0⟩
  else if 0<den x y E.lo ∧ 0<den x y E.hi then
    ⟨max R.lo (min (ceilQ x y E.lo) (ceilQ x y E.hi)),R.hi⟩ else R

private def highPrime (x y : ℚ) (E R : Range) : Range :=
  if 0<den x y E.lo ∧ 0<den x y E.hi then
    ⟨R.lo,min R.hi (max (ceilQ x y E.lo) (ceilQ x y E.hi))⟩ else R

private theorem low_ok {x y : ℚ} {E R : Range} {d r : ℕ} (ed : E.has d) (rr : R.has r)
    (pos : 0<den x y d) (low : num x y d≤r*den x y d) : (lowPrime x y E R).has r := by
  unfold lowPrime
  split_ifs with neg both
  · have ex := extreme x y 1 0 ed
    simp only [one_mul,zero_mul,add_zero] at ex
    rcases ex with e|e <;> linarith [neg.1,neg.2]
  · refine ⟨max_le rr.1 ?_,rr.2⟩
    have one (s : ℕ) (ps : 0<den x y s) (e : r*den x y d + (-1)*num x y d≤r*den x y s+(-1)*num x y s) :
        ceilQ x y s≤r := by
      apply Nat.ceil_le.mpr
      apply (div_le_iff₀ ps).mpr
      linarith only [low,e]
    rcases extreme x y r (-1) ed with e|e
    · exact (min_le_left ..).trans (one _ both.1 e)
    · exact (min_le_right ..).trans (one _ both.2 e)
  · exact rr

private theorem high_ok {x y : ℚ} {E R : Range} {d r : ℕ} (rp : 0<r) (ed : E.has d) (rr : R.has r)
    (up : ((r:ℚ)-1)*den x y d<num x y d) : (highPrime x y E R).has r := by
  unfold highPrime
  split_ifs with both
  · refine ⟨rr.1,le_min rr.2 ?_⟩
    have one (s : ℕ) (ps : 0<den x y s)
        (e : (1-(r:ℚ))*den x y d+1*num x y d≤(1-r)*den x y s+1*num x y s) :
        r≤ceilQ x y s := by
      have lt : ((r-1:ℕ):ℚ)<num x y s/den x y s := by
        rw [Nat.cast_sub rp,Nat.cast_one,lt_div_iff₀ ps]
        linarith only [up,e]
      have h := Nat.lt_ceil.mpr lt
      change r≤⌈num x y s/den x y s⌉₊
      omega
    rcases extreme x y (1-r) 1 ed with e|e
    · exact (one _ both.1 e).trans (le_max_left ..)
    · exact (one _ both.2 e).trans (le_max_right ..)
  · exact rr

/-- Cofactor bounds come from the original box, as in the reference
    computation. The mask returned by digit supplies the new exponents. -/
def primeWindow (p q : ℕ) (original rounded : Box245212.Box) : Option Box245212.Box :=
  let E := rounded 3
  let R := lowPrime (co xl p q original 3) (co yl p q original 3) E (rounded 4)
  let R := highPrime (co xu p q original 3) (co yu p q original 3) E R
  if R.lo≤R.hi then some (clip rounded 4 R) else none

theorem primeWindow_sound {p q : ℕ} {v : Values} {b b' : Box245212.Box}
    (c : Candidate p q v) (fit : Fits b v) (newFit : Fits b' v) (start : ∀ i,1<(baseBox p q b i).lo) :
    ∃ out,primeWindow p q b b'=some out ∧ Fits out v := by
  have hr : Nat.Prime (v 4) := c.prime 3
  have ⟨one,lo,hi⟩ := facts c fit start 3 (v 4) (v 4) hr.pos (by rfl) (by rfl)
  change 0<den _ _ (v 3) at one
  change num _ _ (v 3)≤_*den _ _ (v 3) at lo
  change _*den _ _ (v 3)<num _ _ (v 3) at hi
  have R1 := low_ok (newFit 3) (newFit 4) one lo
  have R2 := high_ok hr.pos (newFit 3) R1 hi
  exact ⟨_,if_pos (R2.1.trans R2.2),clip_fits newFit R2⟩

end OMA.DigitBox245212

namespace OMA.Box245212
open Finset

def primeTrim (b : Box) : Option Box :=
  let R := b 4
  let live := (Icc R.lo R.hi).filter Nat.Prime
  if h : live.Nonempty then some (clip b 4 ⟨live.min' h,live.max' h⟩) else none

theorem primeTrim_sound {b : Box} {v : Values} {p q : ℕ} (fit : Fits b v) (c : Candidate p q v) :
    ∃ out,primeTrim b=some out ∧ Fits out v := by
  let live := (Icc (b 4).lo (b 4).hi).filter Nat.Prime
  have mem : v 4∈live := mem_filter.mpr ⟨mem_Icc.mpr (fit 4),c.prime 3⟩
  have ne : live.Nonempty := ⟨_,mem⟩
  exact ⟨_,dif_pos ne,clip_fits fit ⟨min'_le _ _ mem,le_max' _ _ mem⟩⟩

def digitTrim (p q : ℕ) (b : Box) : Option Box :=
  if ∀ i,1<(baseBox p q b i).lo then do
    let d ← DigitBox245212.digit p q b
    DigitBox245212.primeWindow p q b d
  else some b

theorem digitTrim_sound {b : Box} {v : Values} {p q : ℕ} (fit : Fits b v) (c : Candidate p q v) :
    ∃ out,digitTrim p q b=some out ∧ Fits out v := by
  unfold digitTrim
  split_ifs with start
  · obtain ⟨d,hd,hf⟩ := DigitBox245212.digit_sound c fit start
    obtain ⟨e,he,ef⟩ := DigitBox245212.primeWindow_sound c fit hf start
    exact ⟨e,by simpa [hd] using he,ef⟩
  · exact ⟨_,rfl,fit⟩

def cutPoint (r : Range) := max r.lo (min (r.hi-1) (2*(r.lo+1)*(r.hi+1)/(r.lo+r.hi+2)-1))
def leftBox (b : Box) (i : Fin 5) := clip b i ⟨(b i).lo,cutPoint (b i)⟩
def rightBox (b : Box) (i : Fin 5) := clip b i ⟨cutPoint (b i)+1,(b i).hi⟩
def selected (mask : ℕ) := (univ : Finset (Fin 4)).filter fun i=>mask.testBit i.val
def selectedTop (mask : ℕ) : Fin 4 := ⟨min 3 mask.log2,by omega⟩
def banned (p q : ℕ) (b : Box) (op : ℕ) : Bool :=
  if op=1 then decide (∃ i,(b i).hi<(b i).lo)
  else if op=2 then interval p q b
  else if op=3 then exactBlock p q b
  else roundLeaf p q b (selected (op-16)) (selectedTop (op-16))

theorem banned_sound {p q op : ℕ} {b : Box} (good : banned p q b op=true) : Deny p q b := by
  unfold banned at good
  split_ifs at good
  · obtain ⟨i,hi⟩ := of_decide_eq_true good
    exact fun v fit _ => (hi.not_ge ((fit i).1.trans (fit i).2))
  · exact interval_sound good
  · exact prefix_sound good
  · exact round_sound good

abbrev Stack := List Box
def solved (p q : ℕ) (s : Stack) := ∀ b∈s,Deny p q b
def put (out : Option Box) (rest : Stack) : Stack := match out with
  | none => rest
  | some b => b::rest

theorem put_sound {p q : ℕ} {b : Box} {rest : Stack} {out : Option Box}
    (act : ∀ v,Fits b v → Candidate p q v → ∃ w,out=some w ∧ Fits w v)
    (yes : solved p q (put out rest)) : solved p q (b::rest) := by
  intro w hw
  rcases List.mem_cons.mp hw with rfl|hr
  · intro v fit c
    obtain ⟨w,hw,hf⟩ := act v fit c
    rw [hw] at yes
    exact yes w List.mem_cons_self v hf c
  · cases out with
    | none => exact yes _ hr
    | some d => exact yes _ (List.mem_cons_of_mem _ hr)

/-- `none` records an invalid trace. A successful pruning operation whose
box is empty pops that box and preserves the rest of the stack. -/
def advance (shrink : ℕ→ℕ→Box→Box) (p q op : ℕ) (s : Stack) : Option Stack :=
  if op=0 then some s else match s with
  | [] => none
  | b::rest =>
    if op=4 then some (put (primeTrim b) rest)
    else if op=5 then some (shrink p q b::rest)
    else if op=6 then some (put (digitTrim p q b) rest)
    else if h : 7≤op ∧ op<12 then
      let i : Fin 5 := ⟨op-7,by omega⟩
      some (leftBox b i::rightBox b i::rest)
    else if banned p q b op then some rest else none

theorem advance_sound (shrink : ℕ→ℕ→Box→Box)
    (valid : ∀ p q b v,Fits b v → Candidate p q v → Fits (shrink p q b) v)
    {p q op : ℕ} {s t : Stack} (check : advance shrink p q op s=some t)
    (yes : solved p q t) : solved p q s := by
  by_cases z : op=0
  · exact (Option.some.inj (by simpa [advance,z] using check)) ▸ yes
  cases s with
  | nil => simp [advance,z] at check
  | cons b rest =>
    simp only [advance,if_neg z] at check
    split_ifs at check with h4 h5 h6 hi ok
    · cases Option.some.inj check
      exact put_sound (fun _ f c=>primeTrim_sound f c) yes
    · cases Option.some.inj check
      exact put_sound (out:=some (shrink p q b)) (fun v f c=>⟨_,rfl,valid _ _ _ v f c⟩) yes
    · cases Option.some.inj check
      exact put_sound (fun _ f c=>digitTrim_sound f c) yes
    · cases Option.some.inj check
      intro w hw
      rcases List.mem_cons.mp hw with rfl|hr
      · exact split p q _ _ _ (yes _ List.mem_cons_self) (yes _ (List.mem_cons_of_mem _ List.mem_cons_self))
      · exact yes _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))
    · cases Option.some.inj check
      exact fun w hw=> (List.mem_cons.mp hw).elim (fun h=>h ▸ banned_sound ok) (yes w)

end OMA.Box245212

namespace OMA.Height245212
open Finset OMA.Smooth245212
open scoped ArithmeticFunction.sigma

theorem singleton_bound (p e : Fin 4 → ℕ) (prime : ∀ i,(p i).Prime)
    (odd : ∀ i,3≤p i) (pos : ∀ i,0<e i) (inj : Function.Injective p)
    (sol : OeisA245212.a (total p e)=(σ 1 (total p e):ℤ)) (i : Fin 4) :
    p i^e i ≤ (8+(p i-1))*(∏ j∈univ.erase i,(e j+1)*p j^e j) := by
  let A := ∏ j∈univ.erase i,(e j+1)*p j^e j
  have hden : commonDen p e {i}=A*den (p i) (e i) := by
    unfold commonDen
    rw [←prod_erase_mul _ _ (mem_univ i)]
    have cut : (∏ j∈univ.erase i,localDen p e {i} j)=A :=
      prod_congr rfl fun j hj=>by simp [localDen,(mem_erase.mp hj).1]
    rw [cut]; simp [localDen]
  have norm := normalized_of_eq p prime inj e sol
  by_contra! wrong
  change (8+(p i-1))*A<p i^e i at wrong
  have less : (8+((p i:ℚ)-1))*A<(p i:ℚ)^e i := by
    have cast : ((8+(p i-1):ℕ):ℚ)*A<(p i:ℚ)^e i := by exact_mod_cast wrong
    simpa only [Nat.cast_add,Nat.cast_ofNat,Nat.cast_sub (prime i).pos,Nat.cast_one] using cast
  have n0 : (0:ℚ)<den (p i) (e i) := by exact_mod_cast den_pos (prime i).one_lt (e i)
  have a0 : (0:ℚ)<(p i:ℚ)^e i := pow_pos (by exact_mod_cast (prime i).pos) _
  have budget : (∑ j∈({i}:Finset (Fin 4)),err (p j) (e j)*(8+((p j:ℚ)-1)))*
      commonDen p e {i}<1 := by
    simp only [sum_singleton,hden,Nat.cast_mul,err]
    field_simp
    nlinarith only [mul_lt_mul_of_pos_right less n0]
  exact singleton_ne p e prime odd inj sol i ((gap_eq p e prime pos {i} norm budget).trans norm.symm)

end OMA.Height245212

namespace OMA.Box245212
open Finset OMA.Height245212

def coefficientHi (p q : ℕ) (b : Box) (i : Fin 4) : ℕ :=
  sizeHi (8+((baseBox p q b i).hi-1)) +
  ∑ j∈univ.erase i,sizeHi ((b j.castSucc).hi+1)

theorem linear_bound {p q : ℕ} {b : Box} {v : Values} (fit : Fits b v) (c : Candidate p q v)
    (start : ∀ j,0<(baseBox p q b j).lo) (i : Fin 4) :
    exponents v i*sizeLo (baseBox p q b i).lo ≤ coefficientHi p q b i +
      ∑ j∈univ.erase i,exponents v j*sizeHi (baseBox p q b j).hi := by
  let P := bases p q v
  let E := exponents v
  let U := baseBox p q b
  have odd (j : Fin 4) : 3≤P j := c.ordered.monotone (show (0:Fin 4)≤j from Fin.zero_le j)
  have bp (j) := inside_primes (p:=p) (q:=q) fit j
  have ep (j) : (b j.castSucc).has (E j) := fit _
  have encP (j) := enc_range (start j) (bp j)
  have encE (j : Fin 4) : Enc 0 (sizeHi ((b j.castSucc).hi+1)) (E j+1) := by
    have h := enc_range (r:=⟨1,(b j.castSucc).hi+1⟩) (show 0<1 by decide)
      (n:=E j+1) ⟨Nat.succ_le_succ (Nat.zero_le _),Nat.succ_le_succ (ep j).2⟩
    simpa only [show sizeLo 1=0 by decide +kernel] using h
  have encT (j : Fin 4) := enc_mul (encE j) (enc_pow (b:=⟨E j,E j⟩) (encP j) (show Range.has _ (E j) from ⟨le_rfl,le_rfl⟩))
  have encC := enc_range (r:=⟨1,8+((U i).hi-1)⟩) (n:=8+(P i-1)) (show 0<1 by decide)
    (show Range.has _ _ from ⟨show 1≤8+(P i-1) by omega,Nat.add_le_add_left (Nat.sub_le_sub_right (bp i).2 1) 8⟩)
  have upper := (enc_mul encC (enc_prod (univ.erase i) _ _ _ (fun j _=>encT j))).2
  have lower := (enc_pow (b:=⟨E i,E i⟩) (encP i) (show Range.has _ (E i) from ⟨le_rfl,le_rfl⟩)).1
  have bound := singleton_bound P E c.prime odd c.pos c.ordered.injective c.eqn i
  have powers := lower.trans ((Nat.pow_le_pow_left bound 128).trans upper)
  apply le_of_not_gt
  intro contrary
  apply (Nat.pow_lt_pow_right (by decide : 1<2) contrary).not_ge
  simpa [coefficientHi,P,E,U,mul_comm,Finset.sum_add_distrib,Nat.add_assoc] using powers

def upperClip (p q : ℕ) (b : Box) (i : Fin 4) : Box :=
  let U := baseBox p q b
  let z := coefficientHi p q b i + ∑ j∈univ.erase i,(b j.castSucc).hi*sizeHi (U j).hi
  clip b i.castSucc ⟨(b i.castSucc).lo,min (b i.castSucc).hi (z/sizeLo (U i).lo)⟩

theorem upper_sound {p q : ℕ} {b : Box} {v : Values} (fit : Fits b v) (c : Candidate p q v)
    (starts : ∀ j,1<(baseBox p q b j).lo) (i : Fin 4) : Fits (upperClip p q b i) v := by
  let U := baseBox p q b
  have hp : 0<(U i).lo := Nat.zero_lt_one.trans (starts i)
  have hd : 1 ≤ sizeLo (U i).lo := (Nat.le_log_iff_pow_le (by decide : 1<2) (pow_ne_zero 128 hp.ne')).mpr (by
    have t := Nat.pow_le_pow_left (starts i) 128
    exact (by decide : 2^1≤2^128).trans t)
  apply clip_fits fit
  refine ⟨(fit _).1,le_min (fit _).2 ((Nat.le_div_iff_mul_le hd).mpr ?_)⟩
  have h := linear_bound fit c (fun j=>Nat.zero_lt_one.trans (starts j)) i
  apply h.trans
  apply Nat.add_le_add_left
  exact sum_le_sum fun j _=>Nat.mul_le_mul_right _ (fit j.castSucc).2

/-- Least integer whose product with d reaches z; d is positive here. -/
def upDiv (z d : ℕ) := if z=0 then 0 else (z-1)/d+1
theorem upDiv_le {z d v : ℕ} (dpos : 0<d) (bounded : z≤v*d) : upDiv z d≤v := by
  unfold upDiv; split_ifs with h
  · omega
  · exact Nat.succ_le_of_lt ((Nat.div_lt_iff_lt_mul dpos).mpr (by omega))

def lowerClip (p q : ℕ) (b : Box) (i j : Fin 4) : Box :=
  if i=j then b else
  let U := baseBox p q b
  let others := coefficientHi p q b i +
    ∑ k∈(univ.erase i).erase j,(b k.castSucc).hi*sizeHi (U k).hi
  let floor := upDiv ((b i.castSucc).lo*sizeLo (U i).lo-others) (sizeHi (U j).hi)
  clip b j.castSucc ⟨max (b j.castSucc).lo floor,(b j.castSucc).hi⟩

theorem lower_sound {p q : ℕ} {b : Box} {v : Values} (fit : Fits b v) (c : Candidate p q v)
    (starts : ∀ x,1<(baseBox p q b x).lo) (i j : Fin 4) : Fits (lowerClip p q b i j) v := by
  unfold lowerClip
  split_ifs with h
  · exact fit
  · apply clip_fits fit
    refine ⟨max_le (fit _).1 (upDiv_le (Nat.zero_lt_succ _) ?_), (fit _).2⟩
    let U := baseBox p q b
    have lj := (Nat.mul_le_mul_right (sizeLo (U i).lo) (fit i.castSucc).1).trans
      (linear_bound fit c (fun k=>Nat.zero_lt_one.trans (starts k)) i)
    have jm : j∈univ.erase i := by simp [Ne.symm h]
    rw [←sum_erase_add _ _ jm] at lj
    have other := sum_le_sum (s:=(univ.erase i).erase j) (fun k _=>
      Nat.mul_le_mul_right (sizeHi (U k).hi) (fit k.castSucc).2)
    change (b i.castSucc).lo*sizeLo (U i).lo-(coefficientHi p q b i+
      ∑ k∈(univ.erase i).erase j,(b k.castSucc).hi*sizeHi (U k).hi)≤
      v j.castSucc*sizeHi (U j).hi
    change (b i.castSucc).lo*sizeLo (U i).lo ≤ coefficientHi p q b i +
      ((∑ k∈(univ.erase i).erase j,v k.castSucc*sizeHi (U k).hi)+v j.castSucc*sizeHi (U j).hi) at lj
    omega

def topPass (p q : ℕ) (b : Box) := (List.finRange 4).foldl (upperClip p q) b
def bottomPass (p q : ℕ) (b : Box) := (List.finRange 4).foldl
  (fun box i => (List.finRange 4).foldl (fun w j=>lowerClip p q w i j) box) b
def singletonCaps (p q : ℕ) (b : Box) :=
  if ∀ j,1<(baseBox p q b j).lo then bottomPass p q (topPass p q (topPass p q b)) else b

private theorem fold_keep {α : Type*} (g : Box → α → Box) (P : Box → Prop)
    (step : ∀ b i,P b → P (g b i)) (xs : List α) (b : Box) (ok : P b) : P (xs.foldl g b) := by
  induction xs generalizing b with
  | nil => exact ok
  | cons x xs ih => exact ih _ (step b x ok)

theorem singletonCaps_sound {p q : ℕ} {b : Box} {v : Values} (fit : Fits b v) (c : Candidate p q v) :
    Fits (singletonCaps p q b) v := by
  unfold singletonCaps
  split_ifs with init
  · let good (w : Box) := Fits w v ∧ ∀ j,1<(baseBox p q w j).lo
    have preserved {x y : Box} (eq : x 4=y 4) : baseBox p q x=baseBox p q y := by simp [baseBox,eq]
    have last (i : Fin 4) : (4:Fin 5)≠i.castSucc := by intro h; have := congrArg Fin.val h; simp at this; omega
    have up (w : Box) (i : Fin 4) (g : good w) : good (upperClip p q w i) := by
      have e : upperClip p q w i 4=w 4 := by simp [upperClip,clip,Function.update_of_ne (last i)]
      exact ⟨upper_sound g.1 c g.2 i, preserved e ▸ g.2⟩
    have down (i : Fin 4) (w : Box) (j : Fin 4) (g : good w) : good (lowerClip p q w i j) := by
      have e : lowerClip p q w i j 4=w 4 := by
        unfold lowerClip; split_ifs <;> simp [clip,Function.update_of_ne (last j)]
      exact ⟨lower_sound g.1 c g.2 i j,preserved e ▸ g.2⟩
    have top (w : Box) (g : good w) : good (topPass p q w) :=
      fold_keep _ good up _ w g
    exact (fold_keep _ good (fun w i g=>fold_keep _ good (down i) _ w g) (List.finRange 4) _
      (top _ (top _ ⟨fit,init⟩))).1
  · exact fit

end OMA.Box245212

namespace OMA.SparseEngine245212
open OMA.Box245212

abbrev Cut := ℕ→ℕ→Box→Option Box
abbrev Test := ℕ→ℕ→Box→ℕ→Bool
abbrev Advance := ℕ→ℕ→ℕ→Stack→Option Stack
def CutSound (cut : Cut) := ∀ p q b v,Fits b v → Candidate p q v →
  ∃ out,cut p q b=some out ∧ Fits out v
def TestSound (test : Test) := ∀ p q b op,test p q b op=true → Deny p q b
def AdvanceSound (step : Advance) := ∀ p q op s t,step p q op s=some t → solved p q t → solved p q s

/-- 32+i contracts exponent i above; 36+4*i+j contracts j below
    using the height requirement at i. The old complete pass is op 5. -/
def single (p q op : ℕ) (b : Box) : Box :=
  if ∀ i,1<(baseBox p q b i).lo then
    if op<36 then upperClip p q b (Fin.ofNat 4 (op-32))
    else lowerClip p q b (Fin.ofNat 4 ((op-36)/4)) (Fin.ofNat 4 ((op-36)%4))
  else b

theorem single_sound {p q op : ℕ} {b : Box} {v : Values} (fit : Fits b v) (c : Candidate p q v) :
    Fits (single p q op b) v := by
  unfold single
  split_ifs with start h
  · exact upper_sound fit c start _
  · exact lower_sound fit c start _ _
  · exact fit

def step (digit : Cut) (leaf : Test) (p q op : ℕ) (s : Stack) : Option Stack :=
  if op=0 ∨ op=4 ∨ op=5 ∨ 7≤op ∧ op<12 then advance singletonCaps p q op s
  else match s with
  | [] => none
  | b::rest =>
    if op=6 then some (put (digit p q b) rest)
    else if 32≤op ∧ op<52 then some (single p q op b::rest)
    else if leaf p q b op then some rest else none

theorem step_sound {digit : Cut} {leaf : Test} (ds : CutSound digit) (ls : TestSound leaf) :
    AdvanceSound (step digit leaf) := by
  intro p q op s t check yes
  unfold step at check
  by_cases old : op=0 ∨ op=4 ∨ op=5 ∨ 7≤op ∧ op<12
  · rw [if_pos old] at check
    exact advance_sound singletonCaps (fun _ _ _ _ f c=>singletonCaps_sound f c) check yes
  rw [if_neg old] at check
  cases s with
  | nil => cases check
  | cons b rest =>
    dsimp only at check
    split_ifs at check with digitOp shrink passed
    · cases Option.some.inj check
      intro x hx
      rcases List.mem_cons.mp hx with rfl|other
      · intro v hv c
        obtain ⟨out,h,ho⟩ := ds p q _ _ hv c
        rw [h] at yes
        exact yes out List.mem_cons_self v ho c
      · cases h : digit p q b with
        | none => rw [h] at yes; exact yes x other
        | some out => rw [h] at yes; exact yes x (List.mem_cons_of_mem _ other)
    · cases Option.some.inj check
      intro x hx
      rcases List.mem_cons.mp hx with rfl|other
      · exact fun v f c=>yes _ List.mem_cons_self v (single_sound f c) c
      · exact yes _ (List.mem_cons_of_mem _ other)
    · cases Option.some.inj check
      intro x hx
      rcases List.mem_cons.mp hx with rfl|other
      · exact ls p q _ op passed
      · exact yes _ other

def word (advance : Advance) (p q : ℕ) : ℕ→ℕ→Stack→Option Stack
  | 0,_,s => some s
  | n+1,w,s => (advance p q (w%64) s).bind (word advance p q n (w/64) ·)

theorem word_sound {action : Advance} (good : AdvanceSound action) (p q n w : ℕ) (s t : Stack)
    (check : word action p q n w s=some t) (yes : solved p q t) : solved p q s := by
  induction n generalizing w s with
  | zero => cases Option.some.inj check;exact yes
  | succ n ih =>
    cases h : action p q (w%64) s with
    | none => simp [word,h] at check
    | some u => exact good p q _ s u h (ih (w/64) u (by simpa only [word,h,Option.bind_some] using check))

/-- A subtree can begin with an arbitrary word of verified cuts and
    one split, followed by two independent proofs on explicit boxes. -/
theorem branchAction {action : Advance} (ok : AdvanceSound action)
    (p q fuel code : ℕ) (b l r : Box)
    (check : word action p q fuel code [b]=some [l,r])
    (left : Deny p q l) (right : Deny p q r) : Deny p q b := by
  apply word_sound ok p q fuel code [b] [l,r] check _ b List.mem_cons_self
  intro x hx
  rcases List.mem_cons.mp hx with rfl|hx
  · exact left
  · exact (List.mem_singleton.mp hx) ▸ right

end OMA.SparseEngine245212


namespace OMA.Tape245212
open OMA.Box245212 OMA.SparseEngine245212

def field (w i n : ℕ) := (n >>> (i*w)) &&& ((1 <<< w)-1)

def box (numbers : ℕ→ℕ) (bits data : ℕ) : Box := fun i=>
  ⟨numbers (field bits (2*i.val) data),numbers (field bits (2*i.val+1) data)⟩

abbrev Before (test : ℕ→Bool) (last : ℕ) := ∀ i<last,test i=true
def rangeTest (test : ℕ→Bool) (start len : ℕ) := (List.range' start len).all test

theorem zero (test : ℕ→Bool) : Before test 0 := by simp [Before]

theorem extend {f : ℕ→Bool} {start len : ℕ} (was : Before f start)
    (next : rangeTest f start len=true) : Before f (start+len) := by
  intro j h
  by_cases h0 : j<start
  · exact was j h0
  · exact List.all_eq_true.mp next j (List.mem_range'_1.mpr ⟨by omega,h⟩)

/-- The endpoint is ordinary data. A later block starts at the endpoint
of the preceding checked block, while each endpoint reduces to a numeral. -/
structure Cursor (f : ℕ→Bool) where
  endAt : ℕ
  checked : Before f endAt

def Cursor.start (f : ℕ→Bool) : Cursor f := ⟨0,zero f⟩


/-- Both endpoints of the expensive computation are numerals. The separate
equality checks that the stored endpoint is exactly the previous one. -/
def Cursor.atRange {f : ℕ→Bool} (old : Cursor f) (first last : ℕ)
    (same : old.endAt=first)
    (ok : (first≤last && rangeTest f first (last-first))=true) : Cursor f :=
  ⟨last,by
    obtain ⟨le,verified⟩:=Bool.and_eq_true_iff.mp ok
    have le : first≤last := of_decide_eq_true le
    have pre : Before f first := same ▸ old.checked
    simpa only [Nat.add_sub_of_le le] using extend pre verified⟩

end OMA.Tape245212

namespace OMA.RankTape245212
open OMA.Box245212 OMA.SparseEngine245212

structure Store where
  values : ℕ→ℕ
  rows : ℕ→ℕ
  ranks : ℕ
  codes : ℕ
  width : ℕ

def Store.vertex (s : Store) (i : ℕ) := Tape245212.box s.values s.width (s.rows i >>> 24)
def Store.child (s : Store) (i : ℕ) := (s.rows i)&&&65535

/-- The 20 rank entries for a previous action occupy a 120-bit lane.
Rank 20 is an escape followed by one literal six-bit action. -/
def unpack (s : Store) (bits prev : ℕ) : ℕ×ℕ :=
  let cell:=(s.codes >>> (9*(bits&&&255)))&&&511
  let rank:=cell&&&31
  let rest:=bits >>> (cell>>>5)
  if rank=20 then (rest&&&63,rest>>>6)
  else ((s.ranks >>> (120*prev+6*rank))&&&63,rest)

def run (act : Advance) (p q : ℕ) (s : Store) : ℕ→ℕ→ℕ→Stack→Option Stack
  | 0,_,_,stack=>some stack
  | n+1,bits,prev,stack=>
    let op:=unpack s bits prev
    (act p q op.1 stack).bind (fun next=>run act p q s n op.2 op.1 next)

private theorem run_sound {act : Advance} (valid : AdvanceSound act) (p q : ℕ) (s : Store)
    (n bits prev : ℕ) (a b : Stack) (h : run act p q s n bits prev a=some b)
    (ok : solved p q b) : solved p q a := by
  induction n generalizing bits prev a with
  | zero=>cases Option.some.inj h;exact ok
  | succ n ih=>
    cases step : act p q (unpack s bits prev).1 a with
    | none=>simp [run,step] at h
    | some v=>exact valid p q _ _ _ step (ih _ _ v (by simpa only [run,step,Option.bind_some] using h))

def test (act : Advance) (p q : ℕ) (s : Store) (i : ℕ) : Bool :=
  let row:=s.rows i
  let got:=run act p q s ((row>>>16)&&&255) (row>>>(24+10*s.width)) 64 [s.vertex i]
  let left:=s.child i
  if left=0 then decide (got=some [])
  else decide (0 < left) && decide (left ≤ i) && decide (got=some [s.vertex (i-left),s.vertex (i-1)])

theorem close {act : Advance} (valid : AdvanceSound act) (p q : ℕ) (s : Store) (last : ℕ)
    (checked : Tape245212.Before (test act p q s) (last+1)) : Deny p q (s.vertex last) := by
  suffices ∀ i≤last,Deny p q (s.vertex i) by exact this _ le_rfl
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih=>
    intro le
    have h:=checked i (by omega)
    unfold test at h
    by_cases leaf : s.child i=0
    · rw [if_pos leaf] at h
      exact run_sound valid p q _ _ _ _ _ _ (of_decide_eq_true h) (by simp [solved]) _ List.mem_cons_self
    · rw [if_neg leaf] at h
      obtain ⟨⟨hp,hm⟩,right⟩:=(Bool.and_eq_true_iff.mp h).imp_left Bool.and_eq_true_iff.mp
      have pos : 0 < s.child i :=of_decide_eq_true hp
      have mx : s.child i ≤ i :=of_decide_eq_true hm
      apply run_sound valid p q _ _ _ _ _ _ (of_decide_eq_true right) _ _ List.mem_cons_self
      intro b hb
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
      rcases hb with rfl|rfl
      · exact ih _ (by omega) (by omega)
      · exact ih _ (by omega) (by omega)

end OMA.RankTape245212

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

end OMA.ReverseDigit245212

namespace OMA.ReverseClipTheory245212
open OMA.Smooth245212 OMA.ReverseDigit245212

def F (t x y w : ℚ) := 2*t-(1+w)*y-(1+w)*(t-w)*x

/-- For t≥2 the residual decreases in both cofactor moments and in
w=1/(p−1), so the mixed three-variable interval needs two corners. -/
theorem antitone {t x X y Y w W : ℚ} (ht : 2≤t) (lx : 0≤x) (xx : x≤X) (ly : 0≤y)
    (yy : y≤Y) (lw : 0≤w) (ww : w≤W) (hw : W≤1/2) : F t X Y W≤F t x y w := by
  calc
    F t X Y W ≤ F t x y W := by
      unfold F
      have c : 0≤(1+W)*(t-W) := mul_nonneg (by linarith) (by linarith)
      linarith only [mul_le_mul_of_nonneg_left xx c,
        mul_le_mul_of_nonneg_left yy (show 0≤1+W by linarith)]
    _ ≤ F t x y w := by
      unfold F
      have coeff : 0≤y+(t-1-w-W)*x := add_nonneg ly (mul_nonneg (by linarith) lx)
      nlinarith only [mul_nonneg (sub_nonneg.mpr ww) coeff]

def fp (p Z A S t : ℚ) := t*denominator p A Z-numerator p A S
private theorem flat {p Z : ℚ} (pp : 1<p) (zp : 0<Z) (A S t : ℚ) :
    fp p Z A S t=((p-1)^2*Z)*F t (A/Z) (S/Z) (1/(p-1)) := by
  unfold fp F denominator numerator
  field_simp [sub_ne_zero.mpr pp.ne',zp.ne'];ring

private theorem margin {p : ℕ} (pp : 3≤p) {e : ℕ} (he : 0<e) :
    ((e:ℚ)+1)/((p:ℚ)^(e+1)-1)≤1/(p:ℚ) := by
  obtain ⟨j,rfl⟩:=Nat.exists_eq_succ_of_ne_zero he.ne'
  have grow (k : ℕ) : (k+2)*p+1 ≤ p^(k+2) := by
    induction k with
    | zero => norm_num [pow_two];nlinarith
    | succ k ih =>
      rw [pow_succ p (k+2)]
      nlinarith [Nat.mul_le_mul_left (p^(k+2)) (show 2≤p by omega)]
  have bound : ((j:ℚ)+2)*(p:ℚ)+1≤(p:ℚ)^(j+2) := by exact_mod_cast grow j
  have pp' : (3:ℚ)≤p := by exact_mod_cast pp
  have den : 0<(p:ℚ)^(j+2)-1 := by nlinarith [Nat.cast_nonneg (α:=ℚ) j]
  apply (div_le_div_iff₀ den (show (0:ℚ)<p by linarith)).mpr
  push_cast;linarith

private theorem bracket {p e : ℕ} (pp : 3≤p) (ep : 0<e) {x y : ℚ}
    (eq : x*X p (some e)+y*Y p (some e)=2) {u : ℚ} (up : 1/(p:ℚ)≤u) :
    let t:ℚ:=e+1
    (fp p 1 x y t≤0 ∧ 0≤fp p 1 x y (t+u)) ∨ (fp p 1 x y (t+u)≤0 ∧ 0≤fp p 1 x y t) := by
  let eps:=((e:ℚ)+1)/((p:ℚ)^(e+1)-1)
  have hbig : 2≤p := by omega
  have hp : 1<(p:ℚ) := by exact_mod_cast hbig
  have pow : (1:ℚ)<(p:ℚ)^(e+1) := one_lt_pow₀ hp (by omega)
  have ez : 0≤eps := div_nonneg (by positivity) (sub_nonneg.mpr pow.le)
  have eu : eps≤u := (margin pp ep).trans up
  have id:=identity (p:=p) (e:=e) (by omega) (T:=1) (by simpa using eq)
  have zero : fp p 1 x y ((e:ℚ)+1+eps)=0 := by
    unfold fp eps
    field_simp [sub_ne_zero.mpr pow.ne']
    linear_combination -id
  by_cases pos : 0≤denominator p x 1
  · left; unfold fp at *
    constructor <;> nlinarith only [zero,mul_nonneg ez pos,mul_nonneg (sub_nonneg.mpr eu) pos]
  · right; unfold fp at *
    constructor <;> nlinarith only [zero,mul_nonneg ez (neg_nonneg.mpr (le_of_not_ge pos)),
      mul_nonneg (sub_nonneg.mpr eu) (neg_nonneg.mpr (le_of_not_ge pos))]

/-- The smaller allowed prime and upper cofactor moments give the lower
residual; the larger prime and lower moments give the upper residual.
The sign of the leading coefficient need not be determined in advance. -/
theorem corners {p l h e : ℕ} (hl : 3≤l) (lr : l≤p) (rh : p≤h) (ep : 0<e)
    {x y Z xl yl xu yu : ℚ} (zp : 0<Z) (xpos : 0≤xl) (ypos : 0≤yl)
    (xx : xl≤Z*x) (XX : Z*x≤xu) (yy : yl≤Z*y) (YY : Z*y≤yu)
    (eq : x*X p (some e)+y*Y p (some e)=2) :
    let t:ℚ:=e+1;let u:ℚ:=1/l
    (fp l Z xu yu t≤0 ∧ 0≤fp h Z xl yl (t+u)) ∨
      (fp l Z xu yu (t+u)≤0 ∧ 0≤fp h Z xl yl t) := by
  have ll : (3:ℚ)≤l := by exact_mod_cast hl
  have lq : (l:ℚ)≤p := by exact_mod_cast lr
  have hq : (p:ℚ)≤h := by exact_mod_cast rh
  have xx' : xl/Z≤x := (div_le_iff₀ zp).2 (by linarith)
  have yy' : yl/Z≤y := (div_le_iff₀ zp).2 (by linarith)
  have bounds (t : ℚ) (ht : 2≤t) :
      (fp p 1 x y t≤0 → fp l Z xu yu t≤0) ∧ (0≤fp p 1 x y t → 0≤fp h Z xl yl t) := by
    have p1 : 0<(p:ℚ)-1 := by linarith
    have l1 : 0<(l:ℚ)-1 := by linarith
    have h1 : 0<(h:ℚ)-1 := by linarith
    have wl : 1/((p:ℚ)-1)≤1/((l:ℚ)-1) := one_div_le_one_div_of_le l1 (by linarith)
    have wh : 1/((h:ℚ)-1)≤1/((p:ℚ)-1) := one_div_le_one_div_of_le p1 (by linarith)
    have top : 1/((l:ℚ)-1)≤1/2 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    have f1:=antitone ht ((div_nonneg xpos zp.le).trans xx') ((le_div_iff₀ zp).2 (by linarith : x*Z≤xu))
      ((div_nonneg ypos zp.le).trans yy') ((le_div_iff₀ zp).2 (by linarith : y*Z≤yu))
      (one_div_nonneg.mpr p1.le) wl top
    have f2:=antitone ht (div_nonneg xpos zp.le) xx' (div_nonneg ypos zp.le) yy'
      (one_div_nonneg.mpr h1.le) wh (wl.trans top)
    rw [flat (by linarith : 1<(p:ℚ)) (by decide : (0:ℚ)<1),
      flat (by linarith : 1<(l:ℚ)) zp,flat (by linarith : 1<(h:ℚ)) zp]
    simp only [mul_one,div_one]
    constructor
    · intro mid
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (f1.trans (nonpos_of_mul_nonpos_right mid (by positivity)))
    · intro mid
      exact mul_nonneg (by positivity) (((nonneg_of_mul_nonneg_right mid (by positivity))).trans f2)
  have b:=bracket (hl.trans lr) ep eq (one_div_le_one_div_of_le (show (0:ℚ)<l by linarith) lq)
  have hh : (2:ℚ)≤(e:ℚ)+1 := by exact_mod_cast (by omega : 2≤e+1)
  have hh' : (2:ℚ)≤(e:ℚ)+1+1/l := by linarith [one_div_nonneg.mpr (show (0:ℚ)≤l by positivity)]
  rcases b with ⟨a,b⟩|⟨a,b⟩
  · exact Or.inl ⟨(bounds _ hh).1 a,(bounds _ hh').2 b⟩
  · exact Or.inr ⟨(bounds _ hh').1 a,(bounds _ hh).2 b⟩

end OMA.ReverseClipTheory245212

namespace OMA.FastDigit245212
open OMA.Box245212 OMA.DigitBox245212 OMA.PrefixLeaf245212
open OMA.PrefixLeaf245212 (trim_sound)
open OMA.DigitBox245212 (digitsQ)

structure Span where
  xl : ℕ
  yl : ℕ
  xu : ℕ
  yu : ℕ

def dI (Z A S d : ℕ) : ℤ := (d+1:ℤ)*(2*(Z:ℤ)-A)-S
def nI (A S d : ℕ) : ℤ := d*(A:ℤ)+S
def obey (Z : ℕ) (b : Span) (d l h : ℕ) : Prop :=
  0<dI Z b.xl b.yl d ∧ nI b.xl b.yl d≤h*dI Z b.xl b.yl d ∧
    ((l:ℤ)-1)*dI Z b.xu b.yu d<nI b.xu b.yu d

theorem obey_of_score {Z r d l h : ℕ} {b : Span} {x y : ℚ} (z : 0<Z) (prime : r.Prime)
    (hd : 0<d) (hx : 0≤x) (hy : 0<y) (low : 1≤l) (lr : l≤r) (rh : r≤h)
    (value : x*OMA.Smooth245212.X r (some d)+y*OMA.Smooth245212.Y r (some d)=2)
    (ax : (b.xl:ℚ)≤Z*x) (ay : (b.yl:ℚ)≤Z*y)
    (ux : (Z:ℚ)*x≤b.xu) (uy : (Z:ℚ)*y≤b.yu) : obey Z b d l h := by
  obtain ⟨dp,lo,up⟩ := OMA.DigitBox245212.digitsQ prime hd hx hy value
  have zz : (0:ℚ)<Z := by exact_mod_cast z
  have denLo : (Z:ℚ)*den x y d≤dI Z b.xl b.yl d := by
    unfold dI den; push_cast
    nlinarith only [ax,ay,mul_le_mul_of_nonneg_left ax (Nat.cast_nonneg (α:=ℚ) d)]
  have denHi : (dI Z b.xu b.yu d:ℚ)≤Z*den x y d := by
    unfold dI den; push_cast
    nlinarith only [ux,uy,mul_le_mul_of_nonneg_left ux (Nat.cast_nonneg (α:=ℚ) d)]
  have numLo : (nI b.xl b.yl d:ℚ)≤Z*num x y d := by
    unfold nI num; push_cast
    nlinarith only [ay,mul_le_mul_of_nonneg_left ax (Nat.cast_nonneg (α:=ℚ) d)]
  have numHi : (Z:ℚ)*num x y d≤nI b.xu b.yu d := by
    unfold nI num; push_cast
    nlinarith only [uy,mul_le_mul_of_nonneg_left ux (Nat.cast_nonneg (α:=ℚ) d)]
  have hi' : (r:ℚ)≤h := by exact_mod_cast rh
  have lo' : (l:ℚ)-1≤r-1 := by exact_mod_cast sub_le_sub_right (show (l:ℤ)≤r by exact_mod_cast lr) 1
  have ll : (1:ℚ)≤l := by exact_mod_cast low
  refine ⟨?_,?_,?_⟩
  · exact_mod_cast (mul_pos zz dp).trans_le denLo
  · have h1 := (mul_le_mul_of_nonneg_left up zz.le)
    have h2 := (mul_le_mul hi' denLo (mul_pos zz dp).le (Nat.cast_nonneg h))
    exact_mod_cast numLo.trans ((show (Z:ℚ)*num x y d≤r*(Z*den x y d) by linarith only [h1]).trans h2)
  · have h1 := mul_lt_mul_of_pos_left lo zz
    have h2 := (mul_le_mul_of_nonneg_left denHi (show 0≤(l:ℚ)-1 by linarith)).trans
      (mul_le_mul_of_nonneg_right lo' (mul_pos zz dp).le)
    exact_mod_cast h2.trans_lt ((show ((r:ℚ)-1)*(Z*den x y d)<Z*num x y d by linarith only [h1]).trans_le numHi)

private def cut (r : Range) (v w : ℤ) (strict : Bool) : Range :=
  let c := trim (r.lo,r.hi) v (w-v-(if strict then 1 else 0))
  ⟨c.1,c.2⟩
private theorem cut_ok {r : Range} {v w : ℤ} {d : ℕ} (fit : r.has d) (strict : Bool)
    (h : if strict then v*((d:ℤ)+1)<w else v*((d:ℤ)+1)≤w) : (cut r v w strict).has d := by
  apply OMA.PrefixLeaf245212.trim_sound fit.1 fit.2
  cases strict <;> simp only [Bool.false_eq_true,if_false,if_true,sub_zero] at h ⊢ <;> nlinarith only [h]

def digitAt (Z : ℕ) (b : Span) (d pp : Range) : Range :=
  let X : ℤ := b.xl; let Y : ℤ := b.yl
  let U : ℤ := b.xu; let V : ℤ := b.yu
  let r : ℤ := pp.lo; let P : ℤ := pp.hi
  let d := cut d (X-2*Z) (-Y) true
  let d := cut d ((P+1)*X-2*P*Z) (X-(P+1)*Y) false
  cut d (2*(r-1)*Z-r*U) (r*V-U) true

theorem digitAt_ok {Z d : ℕ} {b : Span} {r pp : Range} (fit : r.has d)
    (h : obey Z b d pp.lo pp.hi) : (digitAt Z b r pp).has d := by
  obtain ⟨h1,h2,h3⟩ := h
  simp only [dI,nI] at h1 h2 h3
  refine cut_ok (cut_ok (cut_ok fit true ?_) false ?_) true ?_
  · simp only [if_true]; linarith only [h1]
  · simp only [Bool.false_eq_true,if_false]; linarith only [h2]
  · simp only [if_true]; linarith only [h3]

def ceilD (Z A S e : ℕ) : ℕ := ((nI A S e+dI Z A S e-1)/dI Z A S e).toNat

private theorem ex (Z A S : ℕ) (u v : ℤ) {E : Range} {d : ℕ} (fit : E.has d) :
    let f (j : ℕ) := u*dI Z A S j+v*nI A S j
    f d≤f E.lo ∨ f d≤f E.hi := by
  have le1 : (E.lo:ℤ)≤d := by exact_mod_cast fit.1
  have le2 : (d:ℤ)≤E.hi := by exact_mod_cast fit.2
  by_cases sign : 0≤u*(2*(Z:ℤ)-A)+v*A
  · right; unfold dI nI; nlinarith only [mul_nonneg (sub_nonneg.mpr le2) sign]
  · left; unfold dI nI; nlinarith only [mul_nonneg (sub_nonneg.mpr le1) (neg_nonneg.mpr (le_of_not_ge sign))]

def lowPrime (Z A S : ℕ) (E R : Range) : Range :=
  if dI Z A S E.lo≤0 ∧ dI Z A S E.hi≤0 then ⟨1,0⟩
  else if 0<dI Z A S E.lo ∧ 0<dI Z A S E.hi then
    ⟨max R.lo (min (ceilD Z A S E.lo) (ceilD Z A S E.hi)),R.hi⟩ else R

def highPrime (Z A S : ℕ) (E R : Range) : Range :=
  if 0<dI Z A S E.lo ∧ 0<dI Z A S E.hi then
    ⟨R.lo,min R.hi (max (ceilD Z A S E.lo) (ceilD Z A S E.hi))⟩ else R

theorem lowPrime_ok {Z A S d r : ℕ} {E R : Range} (ed : E.has d) (rr : R.has r)
    (pos : 0<dI Z A S d) (low : nI A S d≤r*dI Z A S d) : (lowPrime Z A S E R).has r := by
  unfold lowPrime;split_ifs with neg both
  · have ext := ex Z A S 1 0 ed
    simp only [one_mul,zero_mul,add_zero] at ext
    rcases ext with h|h <;> linarith [neg.1,neg.2]
  · refine ⟨max_le rr.1 ?_,rr.2⟩
    have one (j : ℕ) (pd : 0<dI Z A S j)
        (h : r*dI Z A S d+(-1)*nI A S d≤r*dI Z A S j+(-1)*nI A S j) : ceilD Z A S j≤r := by
      apply Int.toNat_le.mpr
      apply Int.le_of_lt_add_one
      apply (Int.ediv_lt_iff_lt_mul pd).mpr
      nlinarith only [low,h]
    rcases ex Z A S r (-1) ed with h|h
    · exact (min_le_left ..).trans (one _ both.1 h)
    · exact (min_le_right ..).trans (one _ both.2 h)
  · exact rr

theorem highPrime_ok {Z A S d r : ℕ} {E R : Range} (ed : E.has d) (rr : R.has r)
    (up : ((r:ℤ)-1)*dI Z A S d<nI A S d) : (highPrime Z A S E R).has r := by
  unfold highPrime;split_ifs with both
  · refine ⟨rr.1,le_min rr.2 ?_⟩
    have one (j : ℕ) (pd : 0<dI Z A S j)
        (h : (1-r)*dI Z A S d+1*nI A S d≤(1-r)*dI Z A S j+1*nI A S j) : r≤ceilD Z A S j := by
      have le : (r:ℤ)≤(nI A S j+dI Z A S j-1)/dI Z A S j := by
        apply (Int.le_ediv_iff_mul_le pd).mpr
        nlinarith only [up,h]
      exact (Int.toNat_le_toNat le)
    rcases ex Z A S (1-r) 1 ed with h|h
    · exact (one _ both.1 h).trans (le_max_left ..)
    · exact (one _ both.2 h).trans (le_max_right ..)
  · exact rr

end OMA.FastDigit245212

namespace OMA.FastFactor245212
open OMA.Box245212 OMA.Smooth245212 OMA.Moving245212 Finset

def scale : ℕ := 2^256
def smallQuot (p e : ℕ) :=
  let h := p^min (e+1) 32
  (scale*p*(h-1))/((p-1)*(e+1)*h)
def lowY (pb eb : Range) := smallQuot pb.hi eb.hi
def highY (pb eb : Range) :=
  let p := pb.lo
  let e := eb.lo
  min scale ((if e<32 then smallQuot p e else scale*p/((p-1)*(e+1)))+1)
def lowX (pb eb : Range) := scale+(scale-highY pb eb)/(pb.hi-1)
def highX (pb eb : Range) := scale+(scale-lowY pb eb)/(pb.lo-1)+1

theorem scale_pos : 0<scale := pow_pos (by decide) _
private theorem frac_lo (n d : ℕ) (pos : 0<d) : ((n/d:ℕ):ℚ)≤(n:ℚ)/d := by
  apply (le_div_iff₀ (by exact_mod_cast pos)).mpr
  exact_mod_cast Nat.div_mul_le_self n d
private theorem frac_hi (n d : ℕ) (pos : 0<d) : (n:ℚ)/d≤((n/d+1:ℕ):ℚ) := by
  apply (div_le_iff₀ (by exact_mod_cast pos)).mpr
  exact_mod_cast (Nat.lt_mul_div_succ n pos).le.trans_eq (Nat.mul_comm _ _)

private theorem true_form {p : ℕ} (hp : 1<p) (e : ℕ) :
    Y p (some e)=(p:ℚ)/(((p:ℚ)-1)*(e+1))*(1-(p:ℚ)⁻¹^(e+1)) := by
  have pp : (1:ℚ)<p := by exact_mod_cast hp
  simp only [Y]
  rw [show (p:ℚ)⁻¹-1=(1-p)/p by field_simp]
  generalize (p:ℚ)⁻¹^(e+1) = z
  field_simp [show 1-(p:ℚ)≠0 by linarith, show (p:ℚ)-1≠0 by linarith]; ring

private theorem raw_form {p : ℕ} (hp : 1<p) (e : ℕ) :
    let h := p^min (e+1) 32
    ((scale*p*(h-1):ℕ):ℚ)/((p-1)*(e+1)*h:ℕ) =
       (scale:ℚ)*approx false (some p) (some e) := by
  dsimp only
  have pp : (1:ℚ)<p := by exact_mod_cast hp
  have h1 : 1≤p^min (e+1) 32 := Nat.one_le_pow _ _ hp.le
  push_cast [Nat.cast_sub hp.le,Nat.cast_sub h1]
  unfold approx
  by_cases small : e<32
  · simp only [small,if_true, min_eq_left (show e+1≤32 by omega),true_form hp,inv_pow]
    field_simp
  · simp only [small,if_false, min_eq_right (show 32≤e+1 by omega),Bool.false_eq_true,inv_pow]
    field_simp

private theorem local_bounds {p : ℕ} (hp : 1<p) (e : ℕ) :
    (smallQuot p e:ℚ) ≤ scale*approx false (some p) (some e) ∧
    scale*approx true (some p) (some e)≤
      ((if e<32 then smallQuot p e else scale*p/((p-1)*(e+1)))+1:ℕ) := by
  let h := p^min (e+1) 32
  have p0 : 0<p-1 := by omega
  have dp : 0<(p-1)*(e+1)*h := Nat.mul_pos (Nat.mul_pos p0 (by omega)) (pow_pos hp.le _)
  have raw := raw_form hp e
  refine ⟨(frac_lo _ _ dp).trans_eq raw,?_⟩
  by_cases small : e<32
  · have same : approx true (some p) (some e)=approx false (some p) (some e) := by
      simp [approx,small]
    rw [same,←raw,if_pos small]
    exact frac_hi _ _ dp
  · simp only [approx,small,↓reduceIte]
    have t := frac_hi (scale*p) ((p-1)*(e+1)) (Nat.mul_pos p0 (by omega))
    push_cast [Nat.cast_sub hp.le] at t ⊢
    simpa only [mul_div_assoc'] using t

theorem bounds {pb eb : Range} {p e : ℕ} (valid : 1<pb.lo) (pi : pb.has p) (ei : eb.has e) :
    (lowX pb eb:ℚ) ≤ scale*X p (some e) ∧ scale*X p (some e)≤highX pb eb ∧
    (lowY pb eb:ℚ) ≤ scale*Y p (some e) ∧ scale*Y p (some e)≤highY pb eb := by
  have hP := valid.trans_le pi.1
  have hQ := hP.trans_le pi.2
  have S : (0:ℚ)<scale := by exact_mod_cast scale_pos
  have m := factor_bounds valid (Range.band_has pi) (Range.band_has ei)
  have l : approx false (some pb.hi) (some eb.hi)≤Y p (some e) :=
    (le_max_right _ _).trans m.2.2.2.2.1
  have u : Y p (some e)≤approx true (some pb.lo) (some eb.lo) := m.2.2.2.2.2
  have lo : (lowY pb eb:ℚ) ≤ scale*Y p (some e) :=
    (local_bounds hQ eb.hi).1.trans (mul_le_mul_of_nonneg_left l S.le)
  have hi : (scale:ℚ)*Y p (some e)≤highY pb eb := by
    unfold highY
    rw [Nat.cast_min]
    exact le_min (mul_le_of_le_one_right S.le (y_one hP _))
      ((mul_le_mul_of_nonneg_left u S.le).trans (local_bounds valid eb.lo).2)
  have yu : highY pb eb ≤ scale := min_le_left _ _
  have yl : lowY pb eb ≤ scale := by
    exact_mod_cast lo.trans (mul_le_of_le_one_right S.le (y_one hP _))
  have P1 : (1:ℚ)<p := by exact_mod_cast hP
  have L1 : (1:ℚ)<pb.lo := by exact_mod_cast valid
  have LL : (pb.lo:ℚ)≤p := by exact_mod_cast pi.1
  have HH : (p:ℚ)≤pb.hi := by exact_mod_cast pi.2
  have id : (scale:ℚ)*X p (some e)=scale+(scale-scale*Y p (some e))/((p:ℚ)-1) := by
    unfold X; ring
  rw [id]
  refine ⟨?_,?_,lo,hi⟩
  · have f := frac_lo (scale-highY pb eb) (pb.hi-1) (by omega)
    unfold lowX
    push_cast [Nat.cast_sub yu,Nat.cast_sub hQ.le] at f ⊢
    apply add_le_add_right
    exact f.trans (div_le_div₀ (sub_nonneg.mpr (mul_le_of_le_one_right S.le (y_one hP _)))
      (by linarith only [hi]) (by linarith) (by linarith))
  · have f := frac_hi (scale-lowY pb eb) (pb.lo-1) (by omega)
    unfold highX
    push_cast [Nat.cast_sub yl,Nat.cast_sub valid.le] at f ⊢
    have D := div_le_div₀ (show 0≤(scale:ℚ)-lowY pb eb by exact sub_nonneg.mpr (by exact_mod_cast yl))
      (show (scale:ℚ)-scale*Y p (some e) ≤ scale-lowY pb eb by linarith only [lo])
      (show 0<(pb.lo:ℚ)-1 by linarith) (show (pb.lo:ℚ)-1≤(p:ℚ)-1 by linarith)
    linarith only [D.trans f]

end OMA.FastFactor245212

namespace OMA.FastDigit245212
open OMA.Box245212 Finset
open OMA.Smooth245212 (X Y)

def Correct (M : ℕ) (F : Range→Range→Span) :=
  ∀ (bp be : Range) (p e : ℕ),1<bp.lo → bp.has p → be.has e →
    ((F bp be).xl:ℚ) ≤ M*X p (some e) ∧ M*X p (some e) ≤ (F bp be).xu ∧
    ((F bp be).yl:ℚ) ≤ M*Y p (some e) ∧ M*Y p (some e) ≤ (F bp be).yu

def cofactor (F : Range→Range→Span) (p q : ℕ) (b : Box) (i : Fin 4) : Span :=
  let f (j : Fin 4) := F (baseBox p q b j) (b j.castSucc)
  ⟨∏ j∈univ.erase i,(f j).xl, ∏ j∈univ.erase i,(f j).yl,
   ∏ j∈univ.erase i,(f j).xu, ∏ j∈univ.erase i,(f j).yu⟩

open OMA.Large245212 (y_both)
theorem obey_box {M : ℕ} (positive : 0<M) {F : Range→Range→Span} (valid : Correct M F)
    {p q : ℕ} {b : Box} {v : Values} (c : Candidate p q v) (fit : Fits b v)
    (start : ∀i,1<(baseBox p q b i).lo) (i : Fin 4) (l h : ℕ) (lp : 1≤l)
    (lr : l≤bases p q v i) (rh : bases p q v i≤h) :
    obey (M^3) (cofactor F p q b i) (exponents v i) l h := by
  let xv (j : Fin 4) := X (bases p q v j) (some (exponents v j))
  let yv (j : Fin 4) := Y (bases p q v j) (some (exponents v j))
  let f (j : Fin 4) := F (baseBox p q b j) (b j.castSucc)
  let s := (univ : Finset (Fin 4)).erase i
  have local_ (j : Fin 4) := valid _ _ _ _ (start j) (inside_primes fit j) (fit j.castSucc)
  have xx (j : Fin 4) : 0≤xv j := (moments fit start j).1.trans (moments fit start j).2.1
  have yy (j : Fin 4) : 0<yv j := (show (0:ℚ)<1/((exponents v j:ℚ)+1) by positivity).trans_le
    (OMA.Large245212.y_both (c.prime j).one_lt).1
  have triple (g : Fin 4→ℚ) : ∏ j∈s,(M:ℚ)*g j=(M:ℚ)^3*(∏ j∈s,g j) := by
    rw [prod_mul_distrib,prod_const];simp [s]
  have xl : (∏ j∈s,((f j).xl:ℚ)) ≤ ∏ j∈s,(M:ℚ)*xv j :=
    prod_le_prod (fun j _=>Nat.cast_nonneg _) (fun j _=>(local_ j).1)
  have yl : (∏ j∈s,((f j).yl:ℚ)) ≤ ∏ j∈s,(M:ℚ)*yv j :=
    prod_le_prod (fun j _=>Nat.cast_nonneg _) (fun j _=>(local_ j).2.2.1)
  have xu : (∏ j∈s,(M:ℚ)*xv j) ≤ ∏ j∈s,((f j).xu:ℚ) :=
    prod_le_prod (fun j _=>mul_nonneg (Nat.cast_nonneg _) (xx j)) (fun j _=>(local_ j).2.1)
  have yu : (∏ j∈s,(M:ℚ)*yv j) ≤ ∏ j∈s,((f j).yu:ℚ) :=
    prod_le_prod (fun j _=>mul_nonneg (Nat.cast_nonneg _) (yy j).le) (fun j _=>(local_ j).2.2.2)
  rw [triple] at xl yl xu yu
  refine obey_of_score (x:=∏ j∈s,xv j) (y:=∏j∈s,yv j) (pow_pos positive _) (c.prime i) (c.pos i) (prod_nonneg fun j _=>xx j)
    (prod_pos fun j _=>yy j) lp lr rh ?_ ?_ ?_ ?_ ?_
  · change (∏j∈univ.erase i,xv j)*xv i+(∏j∈univ.erase i,yv j)*yv i=2
    rw [prod_erase_mul _ _ (mem_univ i),prod_erase_mul _ _ (mem_univ i)]
    exact c.score
  · simpa only [cofactor,Nat.cast_prod,Nat.cast_pow] using xl
  · simpa only [cofactor,Nat.cast_prod,Nat.cast_pow] using yl
  · simpa only [cofactor,Nat.cast_prod,Nat.cast_pow] using xu
  · simpa only [cofactor,Nat.cast_prod,Nat.cast_pow] using yu

/-- In a single pass compute the four digit cuts, then bound the last
prime using the tightened exponent and the original cofactor. -/
def contract (M : ℕ) (F : Range→Range→Span) (p q : ℕ) (b : Box) : Option Box :=
  if ∀i,1<(baseBox p q b i).lo then
    let C := cofactor F p q b
    let digit (i : Fin 4) := digitAt (M^3) (C i) (b i.castSucc) (baseBox p q b i)
    let D := digit 3
    let R := lowPrime (M^3) (C 3).xl (C 3).yl D (b 4)
    let R := highPrime (M^3) (C 3).xu (C 3).yu D R
    let out : Box := Fin.lastCases R digit
    if ∀i,(out i).lo≤(out i).hi then some out else none
  else some b

theorem contract_sound {M : ℕ} {F : Range→Range→Span} (mz : 0<M) (valid : Correct M F)
    {p q : ℕ} {v : Values} {b : Box} (fit : Fits b v) (c : Candidate p q v) :
    ∃ out,contract M F p q b=some out ∧ Fits out v := by
  unfold contract
  split_ifs with start
  · let C := cofactor F p q b
    let D (i : Fin 4) := digitAt (M^3) (C i) (b i.castSucc) (baseBox p q b i)
    have f (i : Fin 4) : (D i).has (exponents v i) :=
      digitAt_ok (fit i.castSucc) (obey_box mz valid c fit start i _ _ (start i).le
        (inside_primes fit i).1 (inside_primes fit i).2)
    have good := obey_box mz valid c fit start 3 (v 4) (v 4) (c.prime 3).pos (by rfl) (by rfl)
    let rl := lowPrime (M^3) (C 3).xl (C 3).yl (D 3) (b 4)
    have fl : rl.has (v 4) := lowPrime_ok (f 3) (fit 4) good.1 good.2.1
    let rr := highPrime (M^3) (C 3).xu (C 3).yu (D 3) rl
    have fr : rr.has (v 4) := highPrime_ok (f 3) fl good.2.2
    let out : Box := Fin.lastCases rr D
    have ff : Fits out v := by
      intro i
      refine Fin.lastCases ?_ (fun j=>?_) i
      · exact fr
      · simpa [out,exponents] using f j
    exact ⟨out,if_pos (fun i=>(ff i).1.trans (ff i).2),ff⟩
  · exact ⟨_,rfl,fit⟩

def hull (base exp : Range) : Span :=
  ⟨FastFactor245212.lowX base exp,FastFactor245212.lowY base exp,
    FastFactor245212.highX base exp,FastFactor245212.highY base exp⟩

def fastDigit := contract FastFactor245212.scale hull

theorem fastDigit_sound {p q : ℕ} {v : Values} {b : Box} (fit : Fits b v) (c : Candidate p q v) :
    ∃ out,fastDigit p q b=some out ∧ Fits out v :=
  contract_sound FastFactor245212.scale_pos
    (fun _ _ _ _ start pi ei=>FastFactor245212.bounds start pi ei) fit c

def fastInterval (p q : ℕ) (b : Box) : Bool :=
  let f (i : Fin 4) := hull (baseBox p q b i) (b i.castSucc)
  decide ((∀i,1<(baseBox p q b i).lo) ∧
    ((∏i,(f i).xu)+(∏i,(f i).yu)<2*FastFactor245212.scale^4 ∨
    2*FastFactor245212.scale^4<(∏i,(f i).xl)+(∏i,(f i).yl)))

theorem fastInterval_sound {p q : ℕ} {b : Box} (yes : fastInterval p q b=true) : Deny p q b := by
  obtain ⟨start,why⟩ := of_decide_eq_true yes
  intro v fit c
  let f (i : Fin 4) := hull (baseBox p q b i) (b i.castSucc)
  let M := FastFactor245212.scale
  let x (i : Fin 4) := X (bases p q v i) (some (exponents v i))
  let y (i : Fin 4) := Y (bases p q v i) (some (exponents v i))
  have within (i : Fin 4) : ((f i).xl:ℚ)≤M*x i ∧ M*x i≤(f i).xu ∧
      ((f i).yl:ℚ)≤M*y i ∧ M*y i≤(f i).yu :=
    FastFactor245212.bounds (start i) (inside_primes fit i) (fit i.castSucc)
  have l := add_le_add (prod_le_prod (s:=univ) (fun i _=>Nat.cast_nonneg _) (fun i _=>(within i).1))
    (prod_le_prod (s:=univ) (fun i _=>Nat.cast_nonneg _) (fun i _=>(within i).2.2.1))
  have h := add_le_add (prod_le_prod (s:=univ) (fun i _=>(Nat.cast_nonneg _).trans (within i).1) (fun i _=>(within i).2.1))
    (prod_le_prod (s:=univ) (fun i _=>(Nat.cast_nonneg _).trans (within i).2.2.1) (fun i _=>(within i).2.2.2))
  have eq : (∏i,x i)+(∏i,y i)=2 := c.score
  have mid : (∏i,(M:ℚ)*x i)+(∏i,(M:ℚ)*y i)=2*(M:ℚ)^4 := by
    simp only [prod_mul_distrib,prod_const,card_univ,Fintype.card_fin,←mul_add,eq,mul_comm]
  rw [mid] at l h
  rcases why with upper|lower
  · exact upper.not_ge (by exact_mod_cast h)
  · exact lower.not_ge (by exact_mod_cast l)

end OMA.FastDigit245212

namespace OMA.ReverseClip245212
open OMA.Box245212 OMA.FastDigit245212
open OMA.ReverseClipTheory245212 OMA.ReverseDigit245212
open OMA.PrefixLeaf245212 (trim_sound)

def dc (p Z A : ℕ) : ℤ := ((p:ℤ)-1)*(2*Z*((p:ℤ)-1)-p*A)
def nc (p A S : ℕ) : ℤ := (p:ℤ)*(((p:ℤ)-1)*S-A)
private theorem castD (p Z A : ℕ) : (dc p Z A:ℚ)=denominator p A Z := by
  simp [dc,denominator]
private theorem castN (p A S : ℕ) : (nc p A S:ℚ)=numerator p A S := by
  simp [nc,numerator]

def half (r : Range) (v w : ℤ) : Range :=
  let a:=OMA.PrefixLeaf245212.trim (r.lo,r.hi) v w
  ⟨a.1,a.2⟩
private theorem half_ok {r : Range} {d : ℕ} (fit : r.has d) {v w : ℤ} (h : v*d≤w) :
    (half r v w).has d := OMA.PrefixLeaf245212.trim_sound fit.1 fit.2 h

def hull (a b : Range) : Range :=
  if a.hi<a.lo then b else if b.hi<b.lo then a else ⟨min a.lo b.lo,max a.hi b.hi⟩
private theorem hull_ok {a b : Range} {d : ℕ} (h : a.has d ∨ b.has d) : (hull a b).has d := by
  rcases h with ⟨l,r⟩|⟨l,r⟩ <;> unfold hull <;> split_ifs <;> constructor <;> (try simp_all) <;> omega

def reverseAt (Z : ℕ) (b : Span) (E R : Range) : Range :=
  let dl:=dc R.lo Z b.xu; let dh:=dc R.hi Z b.xl
  let cu:=nc R.lo b.xu b.yu; let cl:=nc R.hi b.xl b.yl
  let l:ℤ:=R.lo
  hull (half (half E dl (cu-dl)) (-(l*dh)) ((l+1)*dh-l*cl))
    (half (half E (l*dl) (l*cu-(l+1)*dl)) (-dh) (dh-cl))

private theorem coCorners {Z p d : ℕ} {b : Span} {R : Range} (hl : 3≤R.lo) (fit : R.has p)
    (hd : 0<d) (hz : 0<Z) {x y : ℚ} (loX : (b.xl:ℚ)≤Z*x) (hiX : (Z:ℚ)*x≤b.xu)
    (loY : (b.yl:ℚ)≤Z*y) (hiY : (Z:ℚ)*y≤b.yu)
    (eq : x*OMA.Smooth245212.X p (some d)+y*OMA.Smooth245212.Y p (some d)=2) :
    let dl:=dc R.lo Z b.xu; let dh:=dc R.hi Z b.xl
    let cu:=nc R.lo b.xu b.yu; let cl:=nc R.hi b.xl b.yl
    let l:ℤ:=R.lo
    (dl*d≤cu-dl ∧ -(l*dh)*d≤(l+1)*dh-l*cl) ∨
      (l*dl*d≤l*cu-(l+1)*dl ∧ (-dh)*d≤dh-cl) := by
  have co:=corners hl fit.1 fit.2 hd (by exact_mod_cast hz) (Nat.cast_nonneg b.xl) (Nat.cast_nonneg b.yl)
    loX hiX loY hiY eq
  let dl:=dc R.lo Z b.xu; let dh:=dc R.hi Z b.xl
  let cu:=nc R.lo b.xu b.yu; let cl:=nc R.hi b.xl b.yl;let l:ℤ:=R.lo
  have lp : 0<(l:ℚ) := by dsimp [l];exact_mod_cast (by omega : 0<R.lo)
  dsimp only [fp] at co
  simp only [← castD,← castN] at co
  change ((d+1:ℚ)*(dl:ℚ)-cu≤0 ∧ 0≤((d+1:ℚ)+1/(l:ℚ))*(dh:ℚ)-cl) ∨
    (((d+1:ℚ)+1/(l:ℚ))*(dl:ℚ)-cu≤0 ∧ 0≤(d+1:ℚ)*(dh:ℚ)-cl) at co
  rcases co with ⟨a,b⟩|⟨a,b⟩
  · left
    field_simp [lp] at b
    constructor
    · exact_mod_cast (show (dl:ℚ)*d≤cu-dl by linarith only [a])
    · exact_mod_cast (show -((l:ℚ)*dh)*d≤(l+1:ℚ)*dh-l*cl by linarith only [b])
  · right
    field_simp [lp] at a
    constructor
    · exact_mod_cast (show (l:ℚ)*dl*d≤l*cu-(l+1:ℚ)*dl by linarith only [a])
    · exact_mod_cast (show -(dh:ℚ)*d≤dh-cl by linarith only [b])

theorem apply_at {Z p d : ℕ} {b : Span} {E R : Range} (hl : 3≤R.lo) (pr : R.has p) (ed : E.has d)
    (hd : 0<d) (hz : 0<Z) {x y : ℚ} (loX : (b.xl:ℚ)≤Z*x) (hiX : (Z:ℚ)*x≤b.xu)
    (loY : (b.yl:ℚ)≤Z*y) (hiY : (Z:ℚ)*y≤b.yu)
    (eq : x*OMA.Smooth245212.X p (some d)+y*OMA.Smooth245212.Y p (some d)=2) :
    (reverseAt Z b E R).has d := by
  apply hull_ok
  rcases coCorners hl pr hd hz loX hiX loY hiY eq with ⟨a,b⟩|⟨a,b⟩
  · exact Or.inl (half_ok (half_ok ed a) b)
  · exact Or.inr (half_ok (half_ok ed a) b)

end OMA.ReverseClip245212

namespace OMA.QuickPrefix245212
open OMA.Box245212 OMA.PrefixLeaf245212 OMA.Large245212

private theorem trim_subset {B : ℕ×ℕ} {v w : ℤ} {d : ℕ}
    (lo : (trim B v w).1≤d) (hi : d≤(trim B v w).2) : B.1≤d ∧ d≤B.2 := by
  unfold trim at lo hi
  split_ifs at lo hi <;> omega

private theorem bounds_subset {A S T rl rh gl gh d : ℕ}
    (lo : (bounds A S T rl rh gl gh).1≤d) (hi : d≤(bounds A S T rl rh gl gh).2) :
    gl≤d ∧ d≤gh := by
  unfold bounds at lo hi
  obtain ⟨a,b⟩ := trim_subset lo hi
  obtain ⟨u,v⟩ := trim_subset a b
  exact ⟨u,v.trans (min_le_left ..)⟩

def noPrime (A S rl rh : ℕ) : Bool :=
  rh-rl<8 && (List.range' rl (rh+1-rl)).all (fun r=>(A+S)%r != 0)

def quick (A S T rl rh gl gh : ℕ) : Bool :=
  noPrime A S rl rh || (if gh-gl<6 then (List.range' gl (gh+1-gl)).all (rejects A S T rl rh)
    else exact A S T rl rh gl gh)

private theorem from_noPrime {A S T rl rh : ℕ} (h : noPrime A S rl rh=true) (d : ℕ) :
    rejects A S T rl rh d=true := by
  obtain ⟨_,no⟩ := Bool.and_eq_true_iff.mp h
  let r := candidate A S T d
  by_cases l : r<rl
  · simp [rejects,show candidate A S T d<rl from l]
  by_cases u : rh<r
  · simp [rejects,show rh<candidate A S T d from u]
  have mem : r∈List.range' rl (rh+1-rl) := List.mem_range'_1.mpr ⟨by omega,by omega⟩
  have neq := List.all_eq_true.mp no r mem
  simp [rejects,show ((A+S)%(candidate A S T d)!=0)=true from neq]

theorem quick_ok {A S T rl rh gl gh : ℕ} (h : quick A S T rl rh gl gh=true) :
    exact A S T rl rh gl gh=true := by
  rcases Bool.or_eq_true_iff.mp h with no|rest
  · exact List.all_eq_true.mpr fun d _=>from_noPrime no d
  by_cases short : gh-gl<6
  · rw [if_pos short] at rest
    apply List.all_eq_true.mpr
    intro d hd
    have lo := (List.mem_range'_1.mp hd).1
    have hi := (List.mem_range'_1.mp hd).2
    have dh : d≤(bounds A S T rl rh gl gh).2 := by omega
    obtain ⟨gl,gh⟩ := bounds_subset lo dh
    exact List.all_eq_true.mp rest d (List.mem_range'_1.mpr ⟨gl,by omega⟩)
  · simpa only [if_neg short] using rest


theorem atPrefix {p q : ℕ} {b : Box} {v : Values} (fit : Fits b v) (c : Candidate p q v)
    (base : decide (1<(b 4).lo)=true)
    (last : quick (wt 3 (v 0)*wt p (v 1)*wt q (v 2))
      (sig 3 (v 0)*sig p (v 1)*sig q (v 2)) (tax 3 (v 0)*tax p (v 1)*tax q (v 2))
      (b 4).lo (b 4).hi (b 3).lo (b 3).hi=true) : False := by
  let bb : Box := ![⟨v 0,v 0⟩,⟨v 1,v 1⟩,⟨v 2,v 2⟩,b 3,b 4]
  have inside : Fits bb v := by
    intro i; fin_cases i <;> first | exact ⟨le_rfl,le_rfl⟩ | apply fit
  apply prefix_sound (b:=bb) _ v inside c
  simp [exactBlock,bb,Range.entries]
  exact ⟨base,quick_ok last⟩

end OMA.QuickPrefix245212

namespace OMA.FastRound245212
open OMA.Box245212 Finset

private def page : ℕ → ℕ
  | 0 => 0x7d1e7765ca6e9a96558059d4a4a5003288000000
  | 1 => 0x9ea749b6679825994a4a90e3a8ca2987e1582e00
  | 2 => 0xb1ac3afabaadab2ab6a9a929fa6a95a428ba1680
  | 3 => 0xbf6fabdef4bc2edbaae7b92e0b76d9b5ad2b3aca
  | 4 => 0xc9b24c8b1fc771ac6315c4f10c370bc2305c0b00
  | 5 => 0xd2346d1743d033ecf33ace336cd332cc32dcaf29
  | 6 => 0xd9764d8b60d7b5dd6f59d5f56d5352d434ed334a
  | 7 => 0xdfb7ddef7ade377dd774dcb70dbf6ddb36ada367
  | 8 => 0xe5393e4790e3f8de338be2788e1f85e1382e0780
  | 9 => 0xea3a6e97a4e8fa2e839fe7b9de739ae6798e5f95
  | 10 => 0xee7b8edfb6ed7b4ecfb2ec7b0ebbadeb3abeaba9
  | 11 => 0xf27c8f1fc6f1bc5f13c3f0bc0effbeef7bceefba
  | 12 => 0xf63d7f5bd6f57d4f4fd2f47d0f3fcef37ccf2fca
  | 13 => 0xf9be5f93e4f8fe2f87e0f7fdef7bddf73dbf6bd9
  | 14 => 0xfcff2fc7f0fc3effbbedfb7ecfafeafa7e8fa3e7
  | 15 => 0xffffeff7fdff3fbfebfafe7f8fdff7fdbf5fd3f4
  | _ => 0

private def lookup (n : ℕ) := ((page (n/16)) >>> (10*(n%16))) &&& 1023

private theorem table_ok : ∀ i : Fin 256, lookup i.val = sizeLo i.val := by decide +kernel

def low (n : ℕ) := if n<256 then lookup n else sizeLo n
def high (n : ℕ) := low n+1

theorem low_eq (n : ℕ) : low n = sizeLo n := by
  unfold low
  split_ifs with h
  · exact table_ok ⟨_,h⟩
  · rfl

private theorem high_eq (n : ℕ) : high n=sizeHi n := by simp [high,sizeHi,low_eq]

def all4 (f : Fin 4→Bool) := f 0 && f 1 && f 2 && f 3

private theorem all4_iff {f : Fin 4→Bool} : all4 f=true ↔ ∀ i,f i=true := by
  simp only [all4,Bool.and_eq_true_iff]
  constructor
  · rintro ⟨⟨⟨h0,h1⟩,h2⟩,h3⟩ i
    fin_cases i <;> assumption
  · exact fun h=>⟨⟨⟨h 0,h 1⟩,h 2⟩,h 3⟩

def skipSum (f : Fin 4→ℕ) (i : Fin 4) := f 0+f 1+f 2+f 3-f i

private theorem skipSum_eq (f : Fin 4→ℕ) (i : Fin 4) :
    skipSum f i=∑ j∈univ.erase i,f j := by
  have h := sum_erase_add _ f (mem_univ i)
  rw [Fin.sum_univ_four] at h
  unfold skipSum
  omega

def skipProd (f : Fin 4→ℕ) (i : Fin 4) :=
  if i.val<2 then (if i.val=0 then f 1 else f 0)*f 2*f 3
  else f 0*f 1*(if i.val=2 then f 3 else f 2)

private theorem skipProd_eq (f : Fin 4→ℕ) (i : Fin 4) :
    skipProd f i=∏ j∈univ.erase i,f j := by
  have h0 : univ.erase (0:Fin 4)={1,2,3} := by decide
  have h1 : univ.erase (1:Fin 4)={0,2,3} := by decide
  have h2 : univ.erase (2:Fin 4)={0,1,3} := by decide
  have h3 : univ.erase (3:Fin 4)={0,1,2} := by decide
  fin_cases i <;> simp_all [skipProd,Finset.prod_insert,mul_assoc]

private def allOn (mask : ℕ) (test : Fin 4→Bool) :=
  all4 fun i=>if mask.testBit i.val then test i else true

private theorem on_of_true {mask : ℕ} {test : Fin 4→Bool} (h : allOn mask test=true)
    {i : Fin 4} (inside : i∈selected mask) : test i=true := by
  have flag : mask.testBit i.val=true := (mem_filter.mp inside).2
  simpa only [flag,if_true] using (all4_iff.mp h i)

private def denominator (p q mask : ℕ) (b : Box) (i : Fin 4) :=
  high ((b i.castSucc).hi+1) +
    (if mask.testBit i.val then 2 else (b i.castSucc).hi)*high (baseBox p q b i).hi

private def smaller (p q mask : ℕ) (b : Box) (i : Fin 4) :=
  decide (high (4*(8+((baseBox p q b i).hi-1))) + skipSum (denominator p q mask b) i <
    (b i.castSucc).lo*low (baseBox p q b i).lo)

private def strictly (p q : ℕ) (b : Box) (i : Fin 4) :=
  decide (((baseBox p q b i).hi-1)*skipProd (fun j=>(baseBox p q b j).lo) i <
    skipProd (fun j=>((baseBox p q b j).lo-1)*((b j.castSucc).lo+1)) i)

private def noExponent (b : Box) (t : Range) :=
  all4 fun j => decide ((b j.castSucc).hi+1<t.lo ∨
    t.lo=t.hi ∧ (b j.castSucc).hi+1<((b j.castSucc).lo/t.lo+1)*t.lo)

def accept (p q : ℕ) (b : Box) (mask : ℕ) : Bool :=
  let t := selectedTop mask
  all4 (fun i=>decide (1<(baseBox p q b i).lo)) &&
    mask.testBit t.val && allOn mask (fun i=>decide (i≤t)) &&
    allOn mask (smaller p q mask b) &&
    (allOn mask (fun i=>decide (i=t)) || noExponent b (baseBox p q b t) ||
      allOn mask (strictly p q b))

theorem sound {p q mask : ℕ} {b : Box} (yes : accept p q b mask=true) : Deny p q b := by
  apply round_sound (s:=selected mask) (t:=selectedTop mask)
  apply decide_eq_true
  simp only [accept,Bool.and_eq_true_iff,Bool.or_eq_true_iff] at yes
  obtain ⟨⟨⟨⟨start,chosen⟩,top⟩,cmp⟩,why⟩ := yes
  have mem : selectedTop mask∈selected mask := mem_filter.mpr ⟨mem_univ _,chosen⟩
  refine ⟨fun i=>of_decide_eq_true (all4_iff.mp start i),mem,
    fun i hi=>of_decide_eq_true (on_of_true top hi),?_,?_⟩
  · intro i hi
    have raw := of_decide_eq_true (on_of_true cmp hi)
    simpa only [skipSum_eq,denominator,high_eq,low_eq,comparison,powBits,denBits,selected,
      mem_filter,mem_univ,true_and] using raw
  · rcases why with (one|never)|strict
    · left
      ext i
      constructor
      · intro hi
        exact mem_singleton.mpr (of_decide_eq_true (on_of_true one hi))
      · intro hi
        exact (mem_singleton.mp hi) ▸ mem
    · right; left
      exact decide_eq_true fun i=>of_decide_eq_true (all4_iff.mp never i)
    · right;right
      intro i hi
      have raw := of_decide_eq_true (on_of_true strict hi)
      simpa only [skipProd_eq,strictBits] using raw

/-- Replace just the 16 selected-mask leaf instructions. -/
def dispatch (fallback : OMA.SparseEngine245212.Test) (p q : ℕ) (b : Box) (op : ℕ) :=
  if 16≤op ∧ op<32 then accept p q b (op-16) else fallback p q b op

theorem dispatch_sound {fallback : OMA.SparseEngine245212.Test}
    (ok : OMA.SparseEngine245212.TestSound fallback) :
    OMA.SparseEngine245212.TestSound (dispatch fallback) := by
  intro p q b op checked
  unfold dispatch at checked
  split_ifs at checked
  · exact sound checked
  · exact ok p q b op checked

private def pad (p q : ℕ) (b : Box) (i : Fin 4) :=
  high (8+((baseBox p q b i).hi-1)) + skipSum (fun j=>high ((b j.castSucc).hi+1)) i

private def term (p q : ℕ) (b : Box) (j : Fin 4) :=
  (b j.castSucc).hi*high (baseBox p q b j).hi

private def upper (p q : ℕ) (b : Box) (i : Fin 4) :=
  let ceiling := (pad p q b i+skipSum (term p q b) i)/low (baseBox p q b i).lo
  clip b i.castSucc ⟨(b i.castSucc).lo,min (b i.castSucc).hi ceiling⟩

private def lower (p q : ℕ) (b : Box) (i j : Fin 4) :=
  if i=j then b else
  let rest := pad p q b i+(skipSum (term p q b) i-term p q b j)
  let floor := upDiv ((b i.castSucc).lo*low (baseBox p q b i).lo-rest) (high (baseBox p q b j).hi)
  clip b j.castSucc ⟨max (b j.castSucc).lo floor,(b j.castSucc).hi⟩

private theorem upper_eq (p q : ℕ) (b : Box) (i : Fin 4) : upper p q b i=upperClip p q b i := by
  simp only [upper,upperClip,pad,term,skipSum_eq,coefficientHi,high_eq,low_eq]

private theorem lower_eq (p q : ℕ) (b : Box) (i j : Fin 4) : lower p q b i j=lowerClip p q b i j := by
  by_cases same : i=j
  · simp [same,lower,lowerClip]
  have mem : j∈(univ.erase i) := mem_erase.mpr ⟨Ne.symm same,mem_univ _⟩
  have hs := sum_erase_add (univ.erase i) (term p q b) mem
  have eq : skipSum (term p q b) i-term p q b j =
      ∑ k∈(univ.erase i).erase j,term p q b k := by rw [skipSum_eq]; omega
  simp only [lower,lowerClip,if_neg same]
  rw [eq]
  simp only [pad,coefficientHi,term,skipSum_eq,high_eq,low_eq]

private def single (p q op : ℕ) (b : Box) :=
  if all4 (fun i=>decide (1<(baseBox p q b i).lo)) then
    if op<36 then upper p q b (Fin.ofNat 4 (op-32))
    else lower p q b (Fin.ofNat 4 ((op-36)/4)) (Fin.ofNat 4 ((op-36)%4))
  else b

private theorem single_eq (p q op : ℕ) (b : Box) : single p q op b=OMA.SparseEngine245212.single p q op b := by
  simp only [single,OMA.SparseEngine245212.single,all4_iff,decide_eq_true_eq,upper_eq,lower_eq]

open OMA.SparseEngine245212
/-- Replace the height instructions of any independently sound replay engine. -/
def withSingles (fallback : Advance) (p q op : ℕ) (s : Stack) :=
  if 32≤op ∧ op<52 then match s with
  | [] => none
  | b::rest => some (single p q op b::rest)
  else fallback p q op s

theorem withSingles_sound {fallback : Advance} (ok : AdvanceSound fallback) :
    AdvanceSound (withSingles fallback) := by
  intro p q op s t check yes
  unfold withSingles at check
  by_cases special : 32≤op ∧ op<52
  · rw [if_pos special] at check
    cases s with
    | nil => cases check
    | cons b rest =>
      cases Option.some.inj check
      intro x hx
      rcases List.mem_cons.mp hx with rfl|hx
      · intro v fit c
        exact yes _ List.mem_cons_self v ((single_eq p q op _) ▸ single_sound fit c) c
      · exact yes _ (List.mem_cons_of_mem _ hx)
  · rw [if_neg special] at check
    exact ok p q op s t check yes

def withRounds (fallback : Advance) (p q op : ℕ) (s : Stack) :=
  if 16≤op ∧ op<32 then match s with
  | [] => none
  | b::rest => if accept p q b (op-16) then some rest else none
  else fallback p q op s

theorem withRounds_sound {fallback : Advance} (ok : AdvanceSound fallback) :
    AdvanceSound (withRounds fallback) := by
  intro p q op s t check yes
  unfold withRounds at check
  by_cases special : 16≤op ∧ op<32
  · rw [if_pos special] at check
    cases s with
    | nil => cases check
    | cons b rest =>
      dsimp only at check
      split_ifs at check with done
      cases Option.some.inj check
      intro x hx
      exact (List.mem_cons.mp hx).elim (fun e=>e ▸ sound done) (yes x)
  · rw [if_neg special] at check
    exact ok p q op s t check yes

end OMA.FastRound245212

namespace OMA.FastReplay245212
open Box245212 SparseEngine245212 FastDigit245212

private def basic (p q : ℕ) (b : Box) (op : ℕ) :=
  if op=2 then fastInterval p q b else banned p q b op

def leaf := FastRound245212.dispatch basic

theorem leaf_sound : TestSound leaf := by
  apply FastRound245212.dispatch_sound
  intro p q b op check
  unfold basic at check
  split_ifs at check
  · exact fastInterval_sound check
  · exact banned_sound check

end OMA.FastReplay245212

namespace OMA.SparseDigit245212
open Box245212 SparseEngine245212 FastDigit245212

private theorem correct : Correct FastFactor245212.scale hull :=
  fun _ _ _ _ start pi ei=>FastFactor245212.bounds start pi ei

def individual (ax : ℕ) (p q : ℕ) (b : Box) : Option Box :=
  if ∀i,1<(baseBox p q b i).lo then
    let Z := FastFactor245212.scale^3
    let i : Fin 4 := Fin.ofNat 4 (ax-52)
    let j : Fin 5 := if ax=56 then 4 else i.castSucc
    let r := if ax=56 then
      let V := cofactor hull p q b 3
      highPrime Z V.xu V.yu (b 3) (lowPrime Z V.xl V.yl (b 3) (b 4))
    else digitAt Z (cofactor hull p q b i) (b i.castSucc) (baseBox p q b i)
    if r.lo≤r.hi then some (clip b j r) else none
  else some b

theorem individual_sound (ax : ℕ) : CutSound (individual ax) := by
  intro p q b v fit c
  unfold individual
  by_cases start : ∀i,1<(baseBox p q b i).lo
  · simp only [if_pos start]
    let i : Fin 4 := Fin.ofNat 4 (ax-52)
    by_cases last : ax=56
    · simp only [last,if_true]
      have ob := obey_box FastFactor245212.scale_pos correct c fit start 3 (v 4) (v 4) (c.prime 3).pos le_rfl le_rfl
      have w := highPrime_ok (fit 3) (lowPrime_ok (fit 3) (fit 4) ob.1 ob.2.1) ob.2.2
      exact ⟨_,if_pos (w.1.trans w.2),clip_fits fit w⟩
    · simp only [last,if_false]
      have bp := inside_primes (p:=p) (q:=q) fit i
      have w := digitAt_ok (fit i.castSucc) (obey_box FastFactor245212.scale_pos correct c fit start i
        _ _ (start i).le bp.1 bp.2)
      exact ⟨_,if_pos (w.1.trans w.2),clip_fits fit w⟩
  · exact ⟨_,if_neg start,fit⟩

def act (p q op : ℕ) : Stack→Option Stack :=
  if 52≤op ∧ op≤56 then step (individual op) FastReplay245212.leaf p q 6
  else step fastDigit FastReplay245212.leaf p q op

theorem act_sound : AdvanceSound act := by
  intro p q op s t h y
  unfold act at h
  split_ifs at h
  · exact step_sound (individual_sound op) FastReplay245212.leaf_sound p q 6 s t h y
  · exact step_sound (fun _ _ _ _ f c=>fastDigit_sound f c) FastReplay245212.leaf_sound p q op s t h y

end OMA.SparseDigit245212

namespace OMA.PrefixRule245212
open OMA.Box245212 OMA.SparseEngine245212

def withPrefix (test : ℕ→ℕ→Box→Bool) (fallback : Advance) (p q op : ℕ) (s : Stack) :=
  if op=3 then match s with
    | [] => none
    | b::rest => if test p q b then some rest else fallback p q op s
  else fallback p q op s

theorem prefix_sound {test : ℕ→ℕ→Box→Bool}
    (good : ∀ {p q b}, test p q b=true → Deny p q b)
    {fallback : Advance} (ok : AdvanceSound fallback) : AdvanceSound (withPrefix test fallback) := by
  intro p q op s t check yes
  unfold withPrefix at check
  split_ifs at check with special
  · cases s with
    | nil => cases check
    | cons b rest =>
      dsimp only at check
      split_ifs at check with done
      · cases Option.some.inj check
        intro x hx
        exact (List.mem_cons.mp hx).elim (fun e=>e ▸ good done) (yes x)
      · exact ok p q op _ t check yes
  · exact ok p q op s t check yes

def base := FastRound245212.withSingles (FastRound245212.withRounds SparseDigit245212.act)
theorem base_sound : AdvanceSound base :=
  FastRound245212.withSingles_sound (FastRound245212.withRounds_sound SparseDigit245212.act_sound)

end OMA.PrefixRule245212

namespace OMA.WheelPrefix245212
open OMA.Box245212 OMA.Large245212 ArithmeticFunction Finset
open OMA.Smooth245212 (W total w_mult w_pow)
open scoped ArithmeticFunction.sigma

private theorem localData {m r d : ℕ} (hm : 0 < m) (prime : r.Prime) (cop : m.Coprime r)
    (hd : 0<d) (eq : OeisA245212.a (m*r^d)=(σ 1 (m*r^d):ℤ)) :
    let A:=W m; let S:=σ 1 m; let T:=m*(σ 0 m)
    r∣A+S ∧ (d=1 → A+S+r*(2*A+S)=4*T*r) ∧
      (2≤d → (A+S)%(r*r)=(r*S)%(r*r)) := by
  dsimp only
  refine ⟨OMA.OddCofactor245212.last_dvd hm prime cop hd eq,?_,?_⟩
  · rintro rfl
    have b:=OMA.Abundance245212.balance (mul_ne_zero hm.ne' (pow_ne_zero _ prime.ne_zero)) eq
    simp only [pow_one] at b
    rw [w_mult.map_mul_of_coprime cop,isMultiplicative_sigma.map_mul_of_coprime cop,
      isMultiplicative_sigma.map_mul_of_coprime cop] at b
    have w:=w_pow prime 1
    simp [sum_range_succ] at w
    have sig : (σ 1) (r^1)=∑ j∈range (1+1),r^j := sigma_one_apply_prime_pow prime
    have tau : (σ 0) (r^1)=1+1 := sigma_zero_apply_prime_pow prime
    simp [sum_range_succ] at sig tau
    rw [w,sig,tau] at b
    nlinarith only [b]
  · intro two
    have div := (pow_dvd_pow (r:ℤ) two).trans (OMA.PrimePowerDiv245212.power_divides hm prime cop d eq)
    have div' : (r:ℤ)*(r:ℤ) ∣ (W m:ℤ)+(σ 1 m:ℤ)-(r:ℤ)*(σ 1 m:ℤ) := by
      rw [pow_two] at div
      rwa [show (W m:ℤ)+(σ 1 m:ℤ)-(r:ℤ)*(σ 1 m:ℤ)=
        (W m:ℤ)-((r:ℤ)-1)*(σ 1 m:ℤ) by ring]
    have mod := Int.modEq_iff_dvd.mpr div'
    change ((r:ℤ)*(σ 1 m:ℤ))%((r:ℤ)*(r:ℤ))=((W m:ℤ)+(σ 1 m:ℤ))%((r:ℤ)*(r:ℤ)) at mod
    exact_mod_cast mod.symm

def eligible (r : ℕ) : Bool :=
  r≤7 || (r%2!=0 && r%3!=0 && r%5!=0 && r%7!=0)
theorem eligible_of {r : ℕ} (hp : r.Prime) : eligible r=true := by
  by_cases sm : r≤7
  · simp [eligible,sm]
  have nr (x : ℕ) (a : 1<x) (b : x≤7) : r%x≠0 := by
    intro h
    have := (Nat.dvd_prime hp).1 (Nat.dvd_of_mod_eq_zero h)
    omega
  have od:=Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
  simp [eligible,sm,od,nr 3 (by decide) (by decide),
    nr 5 (by decide) (by decide),nr 7 (by decide) (by decide)]

structure Packet where
  primes : List ℕ
  product : ℕ
def pack (R : Range) : Packet :=
  let cs:=R.entries.filter eligible
  ⟨cs,cs.prod⟩
theorem divides {r : ℕ} {rs : List ℕ} (h : r∈rs) : r∣rs.prod := by
  induction rs with
  | nil => simp at h
  | cons a rs ih =>
    rw [List.mem_cons] at h
    rw [List.prod_cons]
    rcases h with rfl|h
    · exact dvd_mul_right _ _
    · exact (ih h).trans (dvd_mul_left _ _)

def viable (A S T : ℕ) (D : Range) (r : ℕ) : Bool :=
  (A+S)%r==0 && ((D.lo≤1 && A+S+r*(2*A+S)==4*T*r) ||
    (2≤D.hi && (A+S)%(r*r)==(r*S)%(r*r)))

def veto (w : Packet) (A S T : ℕ) (R D : Range) : Bool :=
  (Nat.gcd (A+S) w.product < R.lo) || !w.primes.any (viable A S T D)

private theorem veto_false {m r d : ℕ} (hm : 0 < m) (pr : r.Prime) (cop : m.Coprime r)
    (hd : 0<d) (eq : OeisA245212.a (m*r^d)=(σ 1 (m*r^d):ℤ)) {R D : Range}
    (hr : R.has r) (he : D.has d) : veto (pack R) (W m) (σ 1 m) (m*(σ 0 m)) R D=false := by
  have hr' : r∈(pack R).primes := List.mem_filter.mpr ⟨Range.mem_entries hr,eligible_of pr⟩
  obtain ⟨dv,one,two⟩ := localData hm pr cop hd eq
  have dc : r∣Nat.gcd (W m+σ 1 m) (pack R).product := Nat.dvd_gcd dv (divides hr')
  have gp : 0<Nat.gcd (W m+σ 1 m) (pack R).product :=
    Nat.gcd_pos_of_pos_left _ (by have := sigma_pos 1 m hm.ne';omega)
  have large := hr.1.trans (Nat.le_of_dvd gp dc)
  have live : viable (W m) (σ 1 m) (m*(σ 0 m)) D r=true := by
    unfold viable
    rw [Nat.mod_eq_zero_of_dvd dv]
    by_cases h : d=1
    · simp [one h,show D.lo≤1 by simpa [h] using he.1]
    · simp [two (by omega),show 2≤D.hi by have := he.2;omega]
  simp [veto,not_lt.mpr large,List.any_eq_true.mpr ⟨r,hr',live⟩]

theorem candidateVeto {p q : ℕ} {v : Values} (c : Candidate p q v) {D R : Range}
    (ed : D.has (v 3)) (rr : R.has (v 4)) :
    veto (pack R) (wt 3 (v 0)*wt p (v 1)*wt q (v 2)) (sig 3 (v 0)*sig p (v 1)*sig q (v 2))
      (tax 3 (v 0)*tax p (v 1)*tax q (v 2)) R D=false := by
  let m:=3^(v 0)*p^(v 1)*q^(v 2)
  have hp : p.Prime := c.prime 1
  have hq : q.Prime := c.prime 2
  have hr : (v 4).Prime := c.prime 3
  have p3 : 3<p := c.ordered (show (0:Fin 4)<1 by decide)
  have pq : p<q := c.ordered (show (1:Fin 4)<2 by decide)
  have qr : q<v 4 := c.ordered (show (2:Fin 4)<3 by decide)
  have same : total (Box245212.bases p q v) (exponents v)=m*(v 4)^(v 3) := by
    simp [total,Box245212.bases,exponents,m,Fin.prod_univ_four]
  have s:=c.eqn; dsimp only at s; rw [same] at s
  have cop : m.Coprime (v 4) :=
    (((Nat.coprime_primes Nat.prime_three hr).mpr (by omega)).pow_left _).mul_left
      (((Nat.coprime_primes hp hr).mpr (by omega)).pow_left _) |>.mul_left
        (((Nat.coprime_primes hq hr).mpr qr.ne).pow_left _)
  have mp : 0 < m := mul_pos (mul_pos (pow_pos (by decide) _) (pow_pos hp.pos _)) (pow_pos hq.pos _)
  have no:=veto_false mp hr cop (c.pos 3) s rr ed
  obtain ⟨aa,ss,tt⟩:=OMA.PrefixLeaf245212.triple Nat.prime_three hp hq p3.ne (by omega) pq.ne (v 0) (v 1) (v 2)
  dsimp only [m] at no
  simpa only [aa,ss,tt] using no

/-- `limit` caps how many sequential integers may be put in the wheel.
The same theorem covers any timing-driven choice of the threshold. -/
def test (limit p q : ℕ) (b : Box) : Bool :=
  let short:=decide ((b 4).hi-(b 4).lo<limit)
  let w:=pack (b 4)
  decide (1<(b 4).lo) && ((b 0).entries.all fun k=>(b 1).entries.all fun e=>(b 2).entries.all fun f=>
    (let A:=wt 3 k*wt p e*wt q f; let S:=sig 3 k*sig p e*sig q f
     let T:=tax 3 k*tax p e*tax q f
     (short && veto w A S T (b 4) (b 3)) ||
       OMA.QuickPrefix245212.quick A S T (b 4).lo (b 4).hi (b 3).lo (b 3).hi))

theorem test_ok {limit p q : ℕ} {b : Box} (yes : test limit p q b=true) : Deny p q b := by
  intro v fit c
  obtain ⟨base,all⟩ := Bool.and_eq_true_iff.mp yes
  have yes := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp all (v 0)
    (Range.mem_entries (fit 0))) (v 1) (Range.mem_entries (fit 1))) (v 2) (Range.mem_entries (fit 2))
  dsimp only at yes
  rw [candidateVeto c (fit 3) (fit 4)] at yes
  simp only [Bool.false_or,Bool.and_false] at yes
  exact OMA.QuickPrefix245212.atPrefix fit c base yes

end OMA.WheelPrefix245212

namespace OMA.WheelRule245212
open OMA.SparseEngine245212
def rule := PrefixRule245212.withPrefix (WheelPrefix245212.test 128) PrefixRule245212.base
theorem sound : AdvanceSound rule :=
  PrefixRule245212.prefix_sound WheelPrefix245212.test_ok PrefixRule245212.base_sound
end OMA.WheelRule245212

namespace OMA.RawDigit245212
open OMA.Box245212 OMA.FastDigit245212 OMA.SparseEngine245212
open Finset

private def start (p q : ℕ) (b : Box) : Bool := 1<p && 1<q && 1<(b 4).lo

private theorem start_iff (p q : ℕ) (b : Box) :
    start p q b=true ↔ ∀ i,1<(baseBox p q b i).lo := by
  simp only [start,Bool.and_eq_true_iff,decide_eq_true_eq]
  constructor
  · rintro ⟨⟨hp,hq⟩,hr⟩ i
    fin_cases i <;> first | exact hp | exact hq | exact hr | exact (show 1<3 by decide)
  · exact fun h=>⟨⟨h 1,h 2⟩,h 3⟩

private def span (P E : Range) : Span :=
  let l:=FastFactor245212.lowY P E
  let u:=FastFactor245212.highY P E
  let M:=FastFactor245212.scale
  ⟨M+(M-u)/(P.hi-1),l,M+(M-l)/(P.lo-1)+1,u⟩

private theorem span_eq (P E : Range) : span P E=hull P E := rfl

def co (p q : ℕ) (b : Box) (i : Fin 4) : Span :=
  let f (j : Fin 4) := span (baseBox p q b j) (b j.castSucc)
  let raw (v : Span→ℕ) := FastRound245212.skipProd (fun j=>v (f j)) i
  ⟨raw Span.xl,raw Span.yl,raw Span.xu,raw Span.yu⟩

private theorem triple (f : Fin 4→ℕ) (i : Fin 4) :
    FastRound245212.skipProd f i=∏ j∈univ.erase i,f j := by
  have h0 : univ.erase (0:Fin 4)={1,2,3} := by decide
  have h1 : univ.erase (1:Fin 4)={0,2,3} := by decide
  have h2 : univ.erase (2:Fin 4)={0,1,3} := by decide
  have h3 : univ.erase (3:Fin 4)={0,1,2} := by decide
  fin_cases i <;> simp_all [FastRound245212.skipProd,prod_insert,mul_assoc]

theorem co_eq (p q : ℕ) (b : Box) (i : Fin 4) : co p q b i=cofactor hull p q b i := by
  simp only [co,triple,span_eq,cofactor]

private def individual (ax : ℕ) (p q : ℕ) (b : Box) : Option Box :=
  if start p q b then
    let Z:=FastFactor245212.scale^3
    let i:=Fin.ofNat 4 (ax-52)
    let j : Fin 5 := if ax=56 then 4 else i.castSucc
    let r:=if ax=56 then
      let V:=co p q b 3
      highPrime Z V.xu V.yu (b 3) (lowPrime Z V.xl V.yl (b 3) (b 4))
    else digitAt Z (co p q b i) (b i.castSucc) (baseBox p q b i)
    if r.lo≤r.hi then some (clip b j r) else none
  else some b

private theorem individual_eq (ax p q : ℕ) (b : Box) :
    individual ax p q b=SparseDigit245212.individual ax p q b := by
  simp only [individual,SparseDigit245212.individual,start_iff,co_eq]

private def interval (p q : ℕ) (b : Box) : Bool :=
  let f (j : Fin 4) := span (baseBox p q b j) (b j.castSucc)
  let prod (v : Span→ℕ) := v (f 0)*v (f 1)*v (f 2)*v (f 3)
  let z:=2*FastFactor245212.scale^4
  start p q b && (prod Span.xu + prod Span.yu < z || z < prod Span.xl + prod Span.yl)

private theorem interval_sound {p q : ℕ} {b : Box} (yes : interval p q b=true) : Deny p q b := by
  apply fastInterval_sound
  simpa only [interval,fastInterval,Bool.and_eq_true_iff,Bool.or_eq_true_iff,
    decide_eq_true_eq,start_iff,Fin.prod_univ_four,span_eq,mul_assoc] using yes

def rule (p q op : ℕ) (s : Stack) :=
  if 52≤op ∧ op≤56 then step (individual op) FastReplay245212.leaf p q 6 s
  else if op=2 then
    match s with
    | [] => none
    | b::rest => if interval p q b then some rest else none
  else WheelRule245212.rule p q op s

theorem sound : AdvanceSound rule := by
  intro p q op s t checked solved
  unfold rule at checked
  split_ifs at checked with digit inter
  · apply step_sound (digit:=individual op) _ FastReplay245212.leaf_sound p q 6 s t checked solved
    intro p q b v fits candidate
    simpa only [individual_eq] using SparseDigit245212.individual_sound op p q b v fits candidate
  · cases s with
    | nil => cases checked
    | cons b rest =>
      dsimp only at checked
      split_ifs at checked with yes
      · cases Option.some.inj checked
        exact fun x hx=>(List.mem_cons.mp hx).elim (fun e=>e ▸ interval_sound yes) (solved x)
  · exact WheelRule245212.sound p q op s t checked solved

end OMA.RawDigit245212

namespace OMA.FastPrimeTrim245212
open OMA.Box245212 OMA.SparseEngine245212
open OMA.Box245212 (put_sound)

private def scan (n : ℕ) : ℕ→ℕ→Bool
  | 0,_ => true
  | k+1,d => if n<d*d then true else n%d != 0 && scan n k (d+2)

private theorem scan_prime {p : ℕ} (hp : p.Prime) (k d : ℕ) (hd : 2≤d) : scan p k d=true := by
  induction k generalizing d with
  | zero => rfl
  | succ k ih =>
    rw [scan]
    split_ifs with done
    · rfl
    · have dp : d<p := by nlinarith
      have ne : p%d≠0 := fun z=>(Nat.prime_def_lt'.mp hp).2 d hd dp (Nat.dvd_of_mod_eq_zero z)
      simp [ne,ih (d+2) (by omega)]

private def keep (n : ℕ) : Bool :=
  n==2 || (n%2==1 && 2<n && scan n 500 3)

private theorem keeps {p : ℕ} (hp : p.Prime) : keep p=true := by
  by_cases two : p=2
  · simp [keep,two]
  · have odd := Nat.odd_iff.mp (hp.odd_of_ne_two two)
    have gt : 2<p := by have := hp.two_le; omega
    simp [keep,odd,gt,scan_prime hp 500 3 (by decide)]

private def lo : ℕ→ℕ→ℕ
  | 0,a => a
  | k+1,a => if keep a then a else lo k (a+1)
private def hi : ℕ→ℕ→ℕ
  | 0,a => a
  | k+1,a => if keep a then a else hi k (a-1)

private theorem lower {v : ℕ} (pv : v.Prime) (n a : ℕ) (h : a≤v) : lo n a≤v := by
  induction n generalizing a with
  | zero => exact h
  | succ n ih =>
    rw [lo]; split_ifs with yes
    · exact h
    · apply ih; have z : a≠v := fun same=>yes (same ▸ keeps pv); omega

private theorem upper {v : ℕ} (pv : v.Prime) (n a : ℕ) (h : v≤a) : v≤hi n a := by
  induction n generalizing a with
  | zero => exact h
  | succ n ih =>
    rw [hi]; split_ifs with yes
    · exact h
    · apply ih; have z : a≠v := fun same=>yes (same ▸ keeps pv); omega

private def trim (b : Box) : Option Box :=
  let r:=b 4
  let n:=r.hi-r.lo+1
  let l:=lo n r.lo
  let u:=hi n r.hi
  if l≤u then some (clip b 4 ⟨l,u⟩) else none

private theorem trim_ok {p q : ℕ} {b : Box} {v : Values} (f : Fits b v) (c : Candidate p q v) :
    ∃ out,trim b=some out ∧ Fits out v := by
  have l:=lower (c.prime 3) ((b 4).hi-(b 4).lo+1) _ (f 4).1
  have u:=upper (c.prime 3) ((b 4).hi-(b 4).lo+1) _ (f 4).2
  exact ⟨_,if_pos (l.trans u),clip_fits f ⟨l,u⟩⟩

private def rest := PrefixRule245212.withPrefix (WheelPrefix245212.test 640) RawDigit245212.rule

def rule (p q op : ℕ) (s : Stack) : Option Stack := if op=4 then
  match s with
  | [] => none
  | b::tail => some (put (trim b) tail)
  else rest p q op s

theorem sound : AdvanceSound rule := by
  intro p q op s t ck yes
  unfold rule at ck
  split_ifs at ck with prime
  · cases s with
    | nil => cases ck
    | cons b tail =>
      cases Option.some.inj ck
      exact OMA.Box245212.put_sound (fun _ f c=>trim_ok f c) yes
  · exact PrefixRule245212.prefix_sound WheelPrefix245212.test_ok RawDigit245212.sound p q op s t ck yes

end OMA.FastPrimeTrim245212

namespace OMA.ReverseRule245212
open OMA.Box245212 OMA.SparseEngine245212 OMA.FastDigit245212 Finset
open OMA.Smooth245212 (X Y)
open OMA.RawDigit245212 (co co_eq)
open OMA.Large245212 (y_both)

private theorem fitsReverse {p q : ℕ} {b : Box} {v : Values} (fit : Fits b v)
    (c : Candidate p q v) (valid : ∀j,3≤(baseBox p q b j).lo) (i : Fin 4) :
    (ReverseClip245212.reverseAt (FastFactor245212.scale^3) (OMA.RawDigit245212.co p q b i)
        (b i.castSucc) (baseBox p q b i)).has (v i.castSucc) := by
  rw [OMA.RawDigit245212.co_eq]
  let M := FastFactor245212.scale
  let xv (j : Fin 4) := X (bases p q v j) (some (exponents v j))
  let yv (j : Fin 4) := Y (bases p q v j) (some (exponents v j))
  let f (j : Fin 4) := hull (baseBox p q b j) (b j.castSucc)
  let s := (univ : Finset (Fin 4)).erase i
  have start (j : Fin 4) : 1<(baseBox p q b j).lo := by have := valid j;omega
  have loc (j : Fin 4) := FastFactor245212.bounds (start j) (inside_primes (p:=p) (q:=q) fit j) (fit j.castSucc)
  have xx (j : Fin 4) : 0≤xv j := (moments fit start j).1.trans (moments fit start j).2.1
  have yy (j : Fin 4) : 0<yv j := (show (0:ℚ)<1/((exponents v j:ℚ)+1) by positivity).trans_le
    (OMA.Large245212.y_both (c.prime j).one_lt).1
  have triple (g : Fin 4→ℚ) : ∏ j∈s,(M:ℚ)*g j=(M:ℚ)^3*(∏ j∈s,g j) := by
    rw [prod_mul_distrib,prod_const];simp [s]
  have xl : (∏ j∈s,((f j).xl:ℚ)) ≤ ∏ j∈s,(M:ℚ)*xv j :=
    prod_le_prod (fun j _=>Nat.cast_nonneg _) (fun j _=>(loc j).1)
  have yl : (∏ j∈s,((f j).yl:ℚ)) ≤ ∏ j∈s,(M:ℚ)*yv j :=
    prod_le_prod (fun j _=>Nat.cast_nonneg _) (fun j _=>(loc j).2.2.1)
  have xu : (∏ j∈s,(M:ℚ)*xv j) ≤ ∏ j∈s,((f j).xu:ℚ) :=
    prod_le_prod (fun j _=>mul_nonneg (Nat.cast_nonneg _) (xx j)) (fun j _=>(loc j).2.1)
  have yu : (∏ j∈s,(M:ℚ)*yv j) ≤ ∏ j∈s,((f j).yu:ℚ) :=
    prod_le_prod (fun j _=>mul_nonneg (Nat.cast_nonneg _) (yy j).le) (fun j _=>(loc j).2.2.2)
  rw [triple] at xl yl xu yu
  apply ReverseClip245212.apply_at (x:=∏ j∈s,xv j) (y:=∏ j∈s,yv j)
    (valid i) (inside_primes fit i) (fit i.castSucc) (c.pos i) (pow_pos FastFactor245212.scale_pos _)
  · simpa only [cofactor,Nat.cast_prod,Nat.cast_pow] using xl
  · simpa only [cofactor,Nat.cast_prod,Nat.cast_pow] using xu
  · simpa only [cofactor,Nat.cast_prod,Nat.cast_pow] using yl
  · simpa only [cofactor,Nat.cast_prod,Nat.cast_pow] using yu
  · change (∏j∈univ.erase i,xv j)*xv i+(∏j∈univ.erase i,yv j)*yv i=2
    rw [prod_erase_mul _ _ (mem_univ i),prod_erase_mul _ _ (mem_univ i)]
    exact c.score

private def cut (op p q : ℕ) (b : Box) : Option Box :=
  if 3≤p ∧ 3≤q ∧ 3≤(b 4).lo then
    let i:=Fin.ofNat 4 (op-52)
    let r:=ReverseClip245212.reverseAt (FastFactor245212.scale^3) (OMA.RawDigit245212.co p q b i)
      (b i.castSucc) (baseBox p q b i)
    if r.lo≤r.hi then some (clip b i.castSucc r) else none
  else some b

private theorem cut_ok (op : ℕ) : CutSound (cut op) := by
  intro p q b v fit c
  unfold cut
  by_cases enough : 3≤p ∧ 3≤q ∧ 3≤(b 4).lo
  · rw [if_pos enough]
    have good (j : Fin 4) : 3≤(baseBox p q b j).lo := by
      rcases enough with ⟨u,w,z⟩
      fin_cases j <;> first | exact u | exact w | exact z | exact (show 3≤3 by decide)
    have keep := fitsReverse fit c good (Fin.ofNat 4 (op-52))
    exact ⟨_,if_pos (keep.1.trans keep.2),clip_fits fit keep⟩
  · exact ⟨_,if_neg enough,fit⟩

def rule (p q op : ℕ) (s : Stack) :=
  if 52≤op ∧ op<56 then step (cut op) FastReplay245212.leaf p q 6 s
  else FastPrimeTrim245212.rule p q op s

theorem sound : AdvanceSound rule := by
  intro p q op s t h yes
  unfold rule at h
  split_ifs at h
  · exact step_sound (cut_ok op) FastReplay245212.leaf_sound _ _ _ _ _ h yes
  · exact FastPrimeTrim245212.sound _ _ _ _ _ h yes

end OMA.ReverseRule245212

namespace OMA.FourCofactor245212
open Nat Finset OMA.Box245212 OMA.Smooth245212 OMA.Large245212
open scoped ArithmeticFunction.sigma

def distinct (i j k l : Fin 4) : Prop :=
  i≠j ∧ i≠k ∧ i≠l ∧ j≠k ∧ j≠l ∧ k≠l
instance (i j k l : Fin 4) : Decidable (distinct i j k l) := by unfold distinct;infer_instance

theorem congruence {p q h : ℕ} {v : Values} (c : Candidate p q v) {i j k l : Fin 4}
    (ok : distinct i j k l) (small : h≤exponents v i) :
    let b:=bases p q v; let e:=exponents v
    wt (b j) (e j)*wt (b k) (e k)*wt (b l) (e l) ≡
      (b i-1)*(sig (b j) (e j)*sig (b k) (e k)*sig (b l) (e l)) [MOD (b i)^h] := by
  let b:=bases p q v; let e:=exponents v
  obtain ⟨ij,ik,il,jk,jl,kl⟩:=ok
  have nz {s t : Fin 4} (st:s≠t) : b s≠b t := fun eq=>st (c.ordered.injective eq)
  have cover : ({i,j,k,l} : Finset (Fin 4))=univ := by
    apply eq_univ_of_card
    simp [ij,ik,il,jk,jl,kl]
  let m:=b j^e j*b k^e k*b l^e l
  have eqn : total b e=m*b i^e i := by
    unfold total
    rw [←cover]
    simp [ij,ik,il,jk,jl,kl,m];ring
  have always:=c.eqn
  change OeisA245212.a (total b e)=(σ 1 (total b e):ℤ) at always
  rw [eqn] at always
  have mp : 0 < m := mul_pos (mul_pos (pow_pos (c.prime j).pos _) (pow_pos (c.prime k).pos _)) (pow_pos (c.prime l).pos _)
  have cop {t : Fin 4} (hi:t≠i) : (b t^e t).Coprime (b i) :=
    ((Nat.coprime_primes (c.prime t) (c.prime i)).mpr (nz hi)).pow_left _
  have cp : m.Coprime (b i):=((cop ij.symm).mul_left (cop ik.symm)).mul_left (cop il.symm)
  have exactpow := OMA.PrimePowerDiv245212.power_divides mp (c.prime i) cp (e i) always
  have reduces := (pow_dvd_pow (b i:ℤ) small).trans exactpow
  obtain ⟨ww,ss,_⟩ := OMA.PrefixLeaf245212.triple (c.prime j) (c.prime k) (c.prime l)
    (nz jk) (nz jl) (nz kl) (e j) (e k) (e l)
  change ((b i:ℤ)^h)∣(W m:ℤ)-((b i:ℤ)-1)*(σ 1 m:ℤ) at reduces
  dsimp [m] at reduces
  rw [ww,ss] at reduces
  apply Nat.ModEq.symm
  apply Nat.modEq_iff_dvd.mpr
  have pos : 1≤b i:=(c.prime i).pos
  simp only [Nat.cast_pow,Nat.cast_mul,Nat.cast_sub (c.prime i).pos,Nat.cast_one]
  simpa only [Nat.cast_mul] using reduces

end OMA.FourCofactor245212

namespace OMA.PackedResidues245212

private def pack (d : ℕ) (f : α→ℕ) : List α→ℕ
  | [] => 0
  | x::xs => 2^d * pack d f xs + f x

private theorem scaled (d k : ℕ) (f : α→ℕ) (xs : List α) :
    k*pack d f xs=pack d (fun a=>k*f a) xs := by
  induction xs with
  | nil => simp [pack]
  | cons a l ih => simp only [pack, Nat.mul_add, Nat.mul_left_comm k (2^d), ih]

private theorem added (d : ℕ) (f g : α→ℕ) (xs : List α) :
    pack d f xs+pack d g xs=pack d (fun a=>f a+g a) xs := by
  induction xs with
  | nil => rfl
  | cons a l ih => simp only [pack,←ih]; ring

private theorem band (d a b c e : ℕ) (hb : b<2^d) (he : e<2^d) :
    (2^d*a+b) &&& (2^d*c+e) = 2^d*(a &&& c)+(b &&& e) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add _ hb, Nat.testBit_two_pow_mul_add _ he,
    Nat.testBit_two_pow_mul_add _ (Nat.and_le_left.trans_lt hb)]
  by_cases h : j<d <;> simp [h,Nat.testBit_and]

private theorem masked (d : ℕ) (f g : α→ℕ) (xs : List α)
    (lo : ∀a∈xs,f a<2^d) (hi : ∀a∈xs,g a<2^d) :
    (pack d f xs &&& pack d g xs)=pack d (fun a=>f a &&& g a) xs := by
  induction xs with
  | nil => simp [pack]
  | cons a l ih =>
    simp only [pack,band _ _ _ _ _ (lo a List.mem_cons_self) (hi a List.mem_cons_self),
      ih (fun a h=>lo a (List.mem_cons_of_mem _ h)) (fun a h=>hi a (List.mem_cons_of_mem _ h))]

private theorem member_eq (d : ℕ) (f g : α→ℕ) (xs : List α)
    (lo : ∀a∈xs,f a<2^d) (hi : ∀a∈xs,g a<2^d)
    (eq : pack d f xs=pack d g xs) : ∀a∈xs,f a=g a := by
  induction xs with
  | nil=>simp
  | cons z l ih=>
    change 2^d*pack d f l+f z=2^d*pack d g l+g z at eq
    have head:=congrArg (fun x=>x%(2^d)) eq
    simp only [Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt (lo _ List.mem_cons_self),
      Nat.mod_eq_of_lt (hi _ List.mem_cons_self)] at head
    have tail : pack d f l=pack d g l := by
      rw [head] at eq
      exact Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos _) (Nat.add_right_cancel eq)
    intro a h
    rcases List.mem_cons.mp h with rfl|inside
    · exact head
    · exact ih (fun a h=>lo a (List.mem_cons_of_mem _ h))
        (fun a h=>hi a (List.mem_cons_of_mem _ h)) tail a inside

structure Panel where
  weights : ℕ
  sigmas : ℕ
  ones : ℕ

def panel (t : ℕ) (rows : List (ℕ×ℕ)) : Panel :=
  ⟨pack (t+t) Prod.fst rows,pack (t+t) Prod.snd rows,pack (t+t) (fun _=>1) rows⟩

private theorem append_pack (d : ℕ) (f : α→ℕ) (xs ys : List α) :
    pack d f (xs++ys)=pack d f xs+(2^d)^xs.length*pack d f ys := by
  induction xs with
  | nil=>simp [pack]
  | cons a l ih=>simp only [List.cons_append,List.length_cons,pack,ih,pow_succ];ring

private theorem pack_map (d : ℕ) (f : α→ℕ) (g : β→α) (xs : List β) :
    pack d f (xs.map g)=pack d (fun x=>f (g x)) xs := by
  induction xs with
  | nil=>rfl
  | cons a l ih=>simp [pack,ih]

private theorem at_range (d a n : ℕ) (f : ℕ→ℕ) :
    pack d f (List.range' a n)= ∑ j∈Finset.range n,(2^d)^j*f (a+j) := by
  induction n with
  | zero=>simp [pack]
  | succ n ih=>simp [List.range'_1_concat,append_pack,Finset.sum_range_succ,ih,pack]

theorem panel_eq (t a n : ℕ) (f : ℕ→ℕ×ℕ) :
    panel t ((List.range' a n).map f) =
    ⟨∑j∈Finset.range n,(2^(t+t))^j*(f (a+j)).1,
     ∑j∈Finset.range n,(2^(t+t))^j*(f (a+j)).2, ∑j∈Finset.range n,(2^(t+t))^j⟩ := by
  simp [panel,pack_map,at_range]

def guarded (t c bound x y : ℕ) (p : Panel) : Bool :=
  let B:=2^t
  let threshold:=bound+1
  let z:=(c*(x*p.weights+y*p.sigmas)) &&& ((B-1)*p.ones)
  let marks:=B*p.ones
  ((z + (B-threshold)*p.ones) &&& marks) == marks

def room (m t c bound : ℕ) : Bool :=
  let B:=2^t
  decide (2≤B ∧ bound+1≤B ∧ c*bound<B*B ∧ B ≤ m*c ∧ m*c≤B+m)

def check (m t c x y : ℕ) := guarded t c (2*m*m) x y
def ready (m t c : ℕ) := room m t c (2*m*m)

private theorem small_rem {m B c v : ℕ} (low : B ≤ m*c) (high : m*c≤B+m) (dv : m∣v) :
    (c*v)%B≤v := by
  obtain ⟨l,rfl⟩:=dv
  have identity : c*(m*l)=B*l+(m*c-B)*l := by
    rw [←Nat.add_mul,Nat.add_sub_of_le low]; ac_rfl
  rw [identity,Nat.mul_add_mod_self_left]
  exact (Nat.mod_le _ _).trans (Nat.mul_le_mul_right l (by omega))

theorem guarded_sound {m t c bound x y : ℕ} {rows : List (ℕ×ℕ)} (good : room m t c bound=true)
    (valid : ∀z∈rows,x*z.1+y*z.2≤bound)
    (hits : guarded t c bound x y (panel t rows)=true) {z : ℕ×ℕ} (mem : z∈rows) :
    ¬m∣x*z.1+y*z.2 := by
  let B:=2^t
  let cap:=bound+1
  let v (a : ℕ×ℕ):=x*a.1+y*a.2
  let d:=t+t
  change decide (2≤B ∧ cap≤B ∧ c*bound<B*B ∧ B ≤ m*c ∧ m*c≤B+m)=true at good
  obtain ⟨bb,caple,mulB,low,high⟩:=of_decide_eq_true good
  have pow : 2^d=B*B:=Nat.pow_add 2 t t
  have double : B+B≤B*B := by nlinarith only [Nat.mul_le_mul_right B bb]
  have vv (a) (ha:a∈rows) : v a≤bound := valid a ha
  have first (a) (ha:a∈rows) : c*v a<2^d:=pow ▸ (Nat.mul_le_mul_left c (vv a ha)).trans_lt mulB
  have second (a : ℕ×ℕ) (_ : a∈rows) : B-1<2^d:=by rw [pow];omega
  have third (a : ℕ×ℕ) (_ : a∈rows) : B<2^d:=by rw [pow];omega
  have fourth (a : ℕ×ℕ) (_ : a∈rows) : (c*v a)%B+(B-cap)<2^d:=by
    have :=Nat.mod_lt (c*v a) (by omega : 0<B); rw [pow];omega
  have fifth (a : ℕ×ℕ) (ha : a∈rows) : (((c*v a)%B+(B-cap)) &&& B)<2^d :=
    Nat.and_le_right.trans_lt (third a ha)
  have H:=beq_iff_eq.mp hits
  change ((c*(x*pack d Prod.fst rows+y*pack d Prod.snd rows) &&& ((B-1)*pack d (fun _=>1) rows)) +
    (B-cap)*pack d (fun _=>1) rows) &&& (B*pack d (fun _=>1) rows) = B*pack d (fun _=>1) rows at H
  simp only [scaled,added,mul_one] at H
  rw [masked _ _ _ _ first second] at H
  have asMod (u : ℕ) : u &&& (B-1) = u%B := Nat.and_two_pow_sub_one_eq_mod ..
  simp only [asMod,added] at H
  rw [masked _ _ _ _ fourth third] at H
  have tag:=member_eq _ _ _ _ fifth third H z mem
  intro dv
  have sm:=small_rem low high dv
  have le:=Nat.and_le_left (n:=(c*v z)%B+(B-cap)) (m:=B)
  change (((c*v z)%B+(B-cap)) &&& B)=B at tag
  rw [tag] at le
  have vz:=vv z mem
  change (c*v z)%B≤v z at sm
  dsimp only [cap] at *;omega

theorem sound {m t c x y : ℕ} {rows : List (ℕ×ℕ)} (good : ready m t c=true)
    (xx : x < m) (yy : y < m) (valid : ∀z∈rows,z.1 < m ∧ z.2 < m)
    (hits : check m t c x y (panel t rows)=true) {z : ℕ×ℕ} (mem : z∈rows) :
    ¬m∣x*z.1+y*z.2 := by
  apply guarded_sound good _ hits mem
  intro a ha
  obtain ⟨l,r⟩:=valid a ha
  have l1:=Nat.mul_le_mul xx.le l.le;have l2:=Nat.mul_le_mul yy.le r.le
  nlinarith only [l1,l2]

end OMA.PackedResidues245212

namespace OMA.SievePanel245212
open OMA.Box245212 OMA.Large245212 OMA.PackedResidues245212

def row (p e m : ℕ) : ℕ×ℕ := (wt p e%m,sig p e%m)
def table (p m : ℕ) (r : Range) := r.entries.map (fun e=>row p e m)

theorem coefficient_dvd {P m X Y Z u v w : ℕ} (gp : 0 < P) (pm : P ≤ m)
    (cong : X*Y*Z ≡ (P-1)*(u*v*w) [MOD m]) :
    m ∣ (((X%m)*(Y%m))%m)*(Z%m) + (((m+1-P)*(u%m)*(v%m))%m)*(w%m) := by
  have left := ((Nat.mod_modEq ((X%m)*(Y%m)) m).trans ((Nat.mod_modEq _ m).mul (Nat.mod_modEq _ m))).mul (Nat.mod_modEq Z m)
  have right := ((Nat.mod_modEq ((m+1-P)*(u%m)*(v%m)) m).trans
    (((Nat.mod_modEq u m).mul_left (m+1-P)).mul (Nat.mod_modEq v m))).mul (Nat.mod_modEq w m)
  have a:=left.add right
  have b :=cong.add_right ((m+1-P)*u*v*w)
  have same : (P-1)*(u*v*w)+(m+1-P)*u*v*w=m*(u*v*w) := by
    have h : (P-1)+(m+1-P)=m := by omega
    calc _ = ((P-1)+(m+1-P))*(u*v*w) := by ring
         _ = _ := by rw [h]
  rw [same] at b
  apply Nat.dvd_of_mod_eq_zero
  simpa [Nat.ModEq] using a.trans b

def rejects (pivot m a b z : ℕ) (I J K : Range) : Bool :=
  let t := if m<256 then 27 else if m<65536 then 51 else 84
  let c := (2^t+m-1)/m
  let wide := panel t (table z m K)
  ready m t c && (table a m I).all (fun i=>(table b m J).all (fun j=>
    check m t c ((i.1*j.1)%m) (((m+1-pivot)*i.2*j.2)%m) wide))

theorem rejects_sound {P m a b z i j k : ℕ} {I J K : Range} (gp : 0 < P) (pm : P ≤ m)
    (ui : I.has i) (uj : J.has j) (uk : K.has k)
    (cong : wt a i*wt b j*wt z k ≡ (P-1)*(sig a i*sig b j*sig z k) [MOD m]) :
    rejects P m a b z I J K ≠ true := by
  intro h
  have mp : 0 < m := gp.trans_le pm
  obtain ⟨good,all⟩:=Bool.and_eq_true_iff.mp h
  have mem (x e) (R : Range) (sel : R.has e) : row x e m∈table x m R :=
    List.mem_map_of_mem (Range.mem_entries sel)
  have ch :=List.all_eq_true.mp (List.all_eq_true.mp all _ (mem a i I ui)) _ (mem b j J uj)
  apply (sound good (Nat.mod_lt _ mp) (Nat.mod_lt _ mp) _ ch (mem z k K uk)) (coefficient_dvd gp pm cong)
  intro r hr
  obtain ⟨_,_,rfl⟩:=List.mem_map.mp hr
  exact ⟨Nat.mod_lt _ mp,Nat.mod_lt _ mp⟩

end OMA.SievePanel245212

namespace OMA.ClosedPanel245212
open OMA.PackedResidues245212 OMA.Box245212 OMA.Large245212 Finset

private def G (z n : ℕ) := ∑ j∈range n,z^j
private def H (z n : ℕ) := ∑ j∈range n,(j+1)*z^j

private theorem weighted (z n : ℕ) (hz : 1≤z) : (z-1)*H z n+G z n=n*z^n := by
  have lift:=Nat.sub_add_cancel hz
  induction n with
  | zero=>simp [G,H]
  | succ n ih=>
    simp only [H,G,sum_range_succ,pow_succ] at ⊢
    change (z-1)*H z n+G z n=n*z^n at ih
    unfold H G at ih
    nlinarith only [ih,congrArg (fun a=>a*((n+1)*z^n)) lift]

private theorem geom (z n : ℕ) (hz : 1<z) : (z^n-1)/(z-1)=G z n := by
  rw [←geom_sum_mul_of_one_le hz.le,Nat.mul_div_cancel _ (by omega : 0<z-1)];rfl

private theorem arith (z n : ℕ) (hz : 1<z) : (n*z^n-G z n)/(z-1)=H z n := by
  rw [←weighted _ _ hz.le,Nat.add_sub_cancel,Nat.mul_div_cancel_left _ (by omega : 0<z-1)]

private theorem localid {p : ℕ} (hp : 1<p) (e : ℕ) :
    (p-1)*sig p e+1=p^(e+1) ∧ (p-1)*wt p e+sig p e=(e+1)*p^(e+1) := by
  have s : sig p e=G p (e+1):=geom _ _ hp
  have ga :=geom_sum_mul_of_one_le hp.le (e+1)
  have one : 1≤p^(e+1):=Nat.one_le_pow _ _ hp.le
  have w:=weighted p (e+1) hp.le
  have win : wt p e=H p (e+1) := by
    unfold wt tax
    rw [s,←arith _ _ hp]
    congr 2;rw [pow_succ];ring
  rw [s,win];exact ⟨by unfold G;rw [Nat.mul_comm,ga,Nat.sub_add_cancel one],w⟩

def batch (t p lo n : ℕ) : Panel :=
  let d:=2*t
  let L:=1 <<< d
  let big:=1 <<< (d*n)
  let power:=(p^n) <<< (d*n)
  let ones:=(big-1)/(L-1)
  let geom:=(power-1)/(p*L-1)
  let weighted:=(n*power-geom)/(p*L-1)
  let head:=p^(lo+1)
  let s:=(head*geom-ones)/(p-1)
  ⟨(head*(lo*geom+weighted)-s)/(p-1),s,ones⟩

theorem batch_eq {p t : ℕ} (hp : 1<p) (ht : 0<t) (lo n : ℕ) :
    batch t p lo n = panel t ((List.range' lo n).map (fun e=>(wt p e,sig p e))) := by
  let L:=2^(t+t)
  let z:=p*L
  let U:=∑j∈range n,L^j*wt p (lo+j)
  let V:=∑j∈range n,L^j*sig p (lo+j)
  have hl : 1<L:=one_lt_pow₀ (by decide) (by omega : t+t≠0)
  have hz : 1<z:=by dsimp only [z]; nlinarith
  have a (j:ℕ) : p^(lo+j+1)=p^(lo+1)*p^j:=by rw [←pow_add];congr 1;omega
  have ss : (p-1)*V+G L n=p^(lo+1)*G z n := by
    simp only [V,G,mul_sum,←sum_add_distrib]
    apply sum_congr rfl;intro j _
    have h := congrArg (fun b=>L^j*b) (localid hp (lo+j)).1
    rw [a] at h
    dsimp only [z];rw [mul_pow];nlinarith only [h]
  have ww : (p-1)*U+V=p^(lo+1)*(lo*G z n+H z n) := by
    simp only [U,V,G,H,mul_sum,←sum_add_distrib]
    apply sum_congr rfl;intro j _
    have h := congrArg (fun b=>L^j*b) (localid hp (lo+j)).2
    rw [a] at h
    dsimp only [z];rw [mul_pow];nlinarith only [h]
  have Ldef : 1 <<< (2*t)=L:=by simp [Nat.shiftLeft_eq,L,two_mul]
  have big : 1 <<< (2*t*n)=L^n:=by simp [Nat.shiftLeft_eq,L,Nat.pow_mul,two_mul]
  have start : (p^n) <<< (2*t*n)=z^n:=by simp [Nat.shiftLeft_eq,L,z,Nat.pow_mul,two_mul,mul_pow]
  have sv : (p^(lo+1)*G z n-G L n)/(p-1)=V:=by
    rw [←ss,Nat.add_sub_cancel,Nat.mul_div_cancel_left _ (by omega : 0<p-1)]
  have wv : (p^(lo+1)*(lo*G z n+H z n)-V)/(p-1)=U:=by
    rw [←ww,Nat.add_sub_cancel,Nat.mul_div_cancel_left _ (by omega : 0<p-1)]
  simp only [batch,Ldef,big,start,show p*L=z from rfl,geom _ _ hl,geom _ _ hz,arith _ _ hz,sv,wv,panel_eq]
  rfl

def bound (m p e : ℕ) := 2*m*(e+1)*p^(e+1)
def bits (m p e : ℕ) := (e+1)*(p.log2+1)+2*(m.log2+1)+e.log2+6

def rejects (pivot m a b z : ℕ) (I J K : Range) : Bool :=
  if (K.hi+1)*(z.log2+1)>3000 then SievePanel245212.rejects pivot m a b z I J K else
  let t:=bits m z K.hi
  let u:=bound m z K.hi
  let c:=(2^t+m-1)/m
  let P:=batch t z K.lo (K.hi-K.lo+1)
  room m t c u && (SievePanel245212.table a m I).all (fun i=>(SievePanel245212.table b m J).all (fun j=>
    guarded t c u ((i.1*j.1)%m) (((m+1-pivot)*i.2*j.2)%m) P))

private theorem estimate {p e hi : ℕ} (hp : 1<p) (eh : e≤hi) :
    wt p e≤(hi+1)*p^(hi+1) ∧ sig p e≤(hi+1)*p^(hi+1) := by
  have step:= (localid hp e).2
  have h:=Nat.mul_le_mul (Nat.succ_le_succ eh) (Nat.pow_le_pow_right hp.le (Nat.succ_le_succ eh))
  change (e+1)*p^(e+1)≤(hi+1)*p^(hi+1) at h
  have u := Nat.mul_le_mul_right (wt p e) (by omega : 1≤p-1)
  simp only [one_mul] at u
  omega

theorem rejects_sound {P m a b z i j k : ℕ} {I J K : Range} (gp : 0 < P) (pm : P ≤ m)
    (pz : 1<z) (ui : I.has i) (uj : J.has j) (uk : K.has k)
    (cong : wt a i*wt b j*wt z k ≡ (P-1)*(sig a i*sig b j*sig z k) [MOD m]) :
    rejects P m a b z I J K ≠ true := by
  unfold rejects;split_ifs
  · exact SievePanel245212.rejects_sound gp pm ui uj uk cong
  · intro h
    have mp : 0 < m := gp.trans_le pm
    let t:=bits m z K.hi;let mx:=bound m z K.hi; let c:=(2^t+m-1)/m
    let x:=((wt a i%m)*(wt b j%m))%m
    let y:=((m+1-P)*(sig a i%m)*(sig b j%m))%m
    obtain ⟨ok,all⟩:=Bool.and_eq_true_iff.mp h
    have mem (p e) (R : Range) (fit:R.has e) : SievePanel245212.row p e m∈SievePanel245212.table p m R :=
      List.mem_map_of_mem (Range.mem_entries fit)
    have ch:=List.all_eq_true.mp (List.all_eq_true.mp all _ (mem a i I ui)) _ (mem b j J uj)
    change guarded t c mx x y (batch t z K.lo (K.hi-K.lo+1))=true at ch
    rw [batch_eq pz (by dsimp [t,bits];omega)] at ch
    have em : k∈List.range' K.lo (K.hi-K.lo+1) := List.mem_range'_1.mpr ⟨uk.1,by have :=uk.1;have :=uk.2;omega⟩
    have mm : (wt z k,sig z k)∈(List.range' K.lo (K.hi-K.lo+1)).map (fun e=>(wt z e,sig z e)) := List.mem_map_of_mem em
    have no:=guarded_sound (m:=m) ok (z:=(wt z k,sig z k)) ?_ ch mm
    · apply no
      have hit:=SievePanel245212.coefficient_dvd gp pm cong
      change m∣x*(wt z k%m)+y*(sig z k%m) at hit
      have tr := ((Nat.mod_modEq (wt z k) m).mul_left x).add ((Nat.mod_modEq (sig z k) m).mul_left y)
      exact Nat.dvd_of_mod_eq_zero (Eq.trans tr.symm (Nat.mod_eq_zero_of_dvd hit))
    · intro u hu
      obtain ⟨e,he,rfl⟩:=List.mem_map.mp hu
      have high : e≤K.hi:=by
        obtain ⟨l,r⟩:=List.mem_range'_1.mp he
        have :=uk.1;have :=uk.2;omega
      obtain ⟨w,s⟩:=estimate pz high
      change x*wt z e+y*sig z e ≤ mx
      have hx : x ≤ m := (Nat.mod_lt _ mp).le
      have hy : y ≤ m := (Nat.mod_lt _ mp).le
      dsimp only [mx,bound]
      nlinarith only [Nat.mul_le_mul hx w,Nat.mul_le_mul hy s]

end OMA.ClosedPanel245212

namespace OMA.SingleWheel245212
open OMA.Box245212 OMA.Large245212 OMA.SparseEngine245212
open OMA.WheelPrefix245212 (viable divides candidateVeto)

def veto (w : WheelPrefix245212.Packet) (A S T : ℕ) (R D : Range) : Bool :=
  let g:=Nat.gcd (A+S) w.product
  if g<R.lo then true
  else if 0<g ∧ g<2*R.lo then !OMA.WheelPrefix245212.viable A S T D g
  else !w.primes.any (OMA.WheelPrefix245212.viable A S T D)

theorem veto_ok {A S T : ℕ} {R D : Range}
    (live : WheelPrefix245212.veto (WheelPrefix245212.pack R) A S T R D=false) :
    veto (WheelPrefix245212.pack R) A S T R D=false := by
  unfold WheelPrefix245212.veto at live
  obtain ⟨bound,found⟩:=Bool.or_eq_false_iff.mp live
  let w:=WheelPrefix245212.pack R
  let g:=Nat.gcd (A+S) w.product
  have ge : ¬g<R.lo:=of_decide_eq_false bound
  unfold veto; dsimp only; rw [if_neg ge]
  split_ifs with narrow
  · have hits : w.primes.any (OMA.WheelPrefix245212.viable A S T D)=true := by simpa using found
    obtain ⟨r,mem,hit⟩:=List.any_eq_true.mp hits
    have inside := (List.mem_filter.mp mem).1
    have lo : R.lo≤r := (List.mem_range'_1.mp inside).1
    have d : r∣A+S := Nat.dvd_of_mod_eq_zero (beq_iff_eq.mp (Bool.and_eq_true_iff.mp hit).1)
    have dg : r∣g := Nat.dvd_gcd d (OMA.WheelPrefix245212.divides mem)
    have same : r=g := by
      obtain ⟨c,hc⟩:=dg
      rcases c with _|(_|k)
      · simp_all [g,w]
      · simpa using hc.symm
      · have big : r*2≤g := hc ▸ Nat.mul_le_mul_left r (by omega)
        change (0<g ∧ g<2*R.lo) at narrow
        omega
    change (!OMA.WheelPrefix245212.viable A S T D g)=false
    rw [←same,hit]; rfl
  · exact found

def test (limit p q : ℕ) (b : Box) : Bool :=
  let short:=decide ((b 4).hi-(b 4).lo<limit)
  let w:=if short then WheelPrefix245212.pack (b 4) else ⟨[],1⟩
  decide (1<(b 4).lo) && ((b 0).entries.all fun k=>(b 1).entries.all fun e=>(b 2).entries.all fun f=>
    (let A:=wt 3 k*wt p e*wt q f; let S:=sig 3 k*sig p e*sig q f
     let T:=tax 3 k*tax p e*tax q f
     (short && veto w A S T (b 4) (b 3)) ||
       QuickPrefix245212.quick A S T (b 4).lo (b 4).hi (b 3).lo (b 3).hi))

theorem good {lim p q : ℕ} {b : Box} (yes : test lim p q b=true) : Deny p q b := by
  intro v fit c
  obtain ⟨base,all⟩:=Bool.and_eq_true_iff.mp yes
  have k:=List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp all (v 0)
    (Range.mem_entries (fit 0))) (v 1) (Range.mem_entries (fit 1))) (v 2) (Range.mem_entries (fit 2))
  have no:=veto_ok (OMA.WheelPrefix245212.candidateVeto c (fit 3) (fit 4))
  apply QuickPrefix245212.atPrefix fit c base
  dsimp only at k
  by_cases h : (b 4).hi-(b 4).lo<lim <;> simpa [h,no] using k

def rule := PrefixRule245212.withPrefix (test 640) ReverseRule245212.rule
theorem sound : AdvanceSound rule := PrefixRule245212.prefix_sound good ReverseRule245212.sound

end OMA.SingleWheel245212

namespace OMA.BroadRule245212
open OMA.Box245212 OMA.SparseEngine245212
open OMA.WheelPrefix245212 (eligible eligible_of)

private def others (i : Fin 4) : Fin 4×Fin 4×Fin 4 :=
  if i=0 then (1,2,3) else if i=1 then (0,2,3) else if i=2 then (0,1,3) else (0,1,2)

private def ordered (b : Box) (i : Fin 4) : Fin 4×Fin 4×Fin 4 :=
  let f (j : Fin 4):= (b j.castSucc).hi-(b j.castSucc).lo
  let (a,c,e):=others i
  let (u,v):=if f a≤f c then (a,c) else (c,a)
  if f e≤f u then (e,u,v) else if f e≤f v then (u,e,v) else (u,v,e)

private def exponent (prime low : ℕ) := min low (max 1 (Nat.log prime (2^24)))

def direction (closed : Bool) (p q r : ℕ) (b : Box) (i : Fin 4) : Bool :=
  let a : Fin 4→ℕ := ![3,p,q,r]
  let (j,k,l):=ordered b i
  let I:=b j.castSucc;let J:=b k.castSucc;let K:=b l.castSucc
  let h:=exponent (a i) (b i.castSucc).lo
  decide (OMA.FourCofactor245212.distinct i j k l ∧ 0<h ∧
    (I.hi-I.lo+1)*(J.hi-J.lo+1)≤32 ∧ K.hi-K.lo+1≤300 ∧ max (max I.hi J.hi) K.hi≤5000) &&
    (if closed then ClosedPanel245212.rejects else SievePanel245212.rejects)
      (a i) (a i^h) (a j) (a k) (a l) I J K

private theorem survive {p q : ℕ} {b : Box} {v : Values} (fit : Fits b v)
    (c : Candidate p q v) (closed : Bool) (i : Fin 4) : direction closed p q (v 4) b i ≠ true := by
  intro hit
  let a:=bases p q v
  let x:=ordered b i
  let j:=x.1;let k:=x.2.1;let l:=x.2.2
  let h:=exponent (a i) (b i.castSucc).lo
  have hbound : h≤exponents v i := (min_le_left _ _).trans (fit i.castSucc).1
  obtain ⟨ok,test⟩:=Bool.and_eq_true_iff.mp hit
  have good := of_decide_eq_true ok
  have pr:=c.prime i
  change OMA.FourCofactor245212.distinct i j k l ∧ 0<h ∧ _ at good
  have hm : a i ≤ a i^h := by
    simpa only [pow_one] using (Nat.pow_le_pow_right pr.pos good.2.1 : a i^1≤a i^h)
  have cong:=FourCofactor245212.congruence c good.1 hbound
  cases closed
  · exact SievePanel245212.rejects_sound pr.pos hm (fit j.castSucc) (fit k.castSucc) (fit l.castSucc) cong test
  · exact ClosedPanel245212.rejects_sound pr.pos hm (c.prime l).one_lt
      (fit j.castSucc) (fit k.castSucc) (fit l.castSucc) cong test

def test (closed : Bool) (p q op : ℕ) (b : Box) : Bool :=
  let d (r : ℕ) := if op<61 then direction closed p q r b (Fin.ofNat 4 (op-57))
    else direction closed p q r b 0 || direction closed p q r b 1 || direction closed p q r b 2 || direction closed p q r b 3
  (WheelPrefix245212.pack (b 4)).primes.all d

theorem test_sound {closed : Bool} {p q op : ℕ} {b : Box} (yes : test closed p q op b=true) : Deny p q b := by
  intro v fit c
  have pr : (v 4).Prime:=c.prime 3
  have mm : v 4∈(WheelPrefix245212.pack (b 4)).primes:=
    List.mem_filter.mpr ⟨Range.mem_entries (fit 4),OMA.WheelPrefix245212.eligible_of pr⟩
  have h:=List.all_eq_true.mp yes _ mm
  split_ifs at h
  · exact survive fit c _ _ h
  · simp only [Bool.or_eq_true_iff] at h
    rcases h with ((h|h)|h)|h <;> exact survive fit c _ _ h

def withPanel (closed : Bool) (p q op : ℕ) (s : List Box) :=
  if 57≤op ∧ op≤61 then match s with
    | [] => none
    | b::rest => if test closed p q op b then some rest else none
  else SingleWheel245212.rule p q op s

theorem withPanel_sound (closed : Bool) : AdvanceSound (withPanel closed) := by
  intro p q op s t h done
  unfold withPanel at h
  split_ifs at h
  · cases s with
    | nil => cases h
    | cons b rest =>
      change (if test closed p q op b then some rest else none)=some t at h
      split_ifs at h with yes
      cases Option.some.inj h
      exact fun x hx=>(List.mem_cons.mp hx).elim (fun e=>e ▸ test_sound yes) (done x)
  · exact SingleWheel245212.sound _ _ _ _ _ h done


end OMA.BroadRule245212

namespace OMA.GeoRule245212
def rule := BroadRule245212.withPanel true
theorem sound : SparseEngine245212.AdvanceSound rule := BroadRule245212.withPanel_sound true
end OMA.GeoRule245212

namespace OMA.SweepPrefix245212
open OMA.Box245212 OMA.Large245212 OMA.SparseEngine245212
open OMA.SingleWheel245212 (veto_ok)
open OMA.WheelPrefix245212 (candidateVeto)

def scan (A K step lo hi : ℕ) : ℕ→ℕ→ℕ→Bool
  | 0,_,_ => true
  | fuel+1,N,D =>
    let r:=(N-1)/D+1
    (K%r != 0 || r<lo || hi<r) && scan A K step lo hi fuel (N+A) (D+step)

private theorem at_step {A K step lo hi N D n j : ℕ} (hj : j<n)
    (yes : scan A K step lo hi n N D=true) :
    let r:=(N+j*A-1)/(D+j*step)+1
    K%r ≠ 0 ∨ r<lo ∨ hi<r := by
  induction n generalizing j N D with
  | zero=>omega
  | succ n ih=>
    obtain ⟨one,rest⟩:=Bool.and_eq_true_iff.mp yes
    cases j with
    | zero=>simpa [Bool.or_eq_true_iff,or_assoc] using one
    | succ j=>
      have z:=ih (j:=j) (by omega) rest
      simpa only [Nat.succ_mul,add_assoc,add_comm,add_left_comm] using z

def skip (A S T : ℕ) (R E : Range) : Bool :=
  let step:=2*T-A
  if step=0 then true else
  let b:=PrefixLeaf245212.bounds A S T R.lo R.hi E.lo E.hi
  let l:=max b.1 (S/step)
  scan A (A+S) step R.lo R.hi (b.2+1-l) (A*l+S) (step*(l+1)-S)

theorem skip_ok {A S T : ℕ} {R E : Range} (yes : skip A S T R E=true) :
    PrefixLeaf245212.exact A S T R.lo R.hi E.lo E.hi=true := by
  let b:=PrefixLeaf245212.bounds A S T R.lo R.hi E.lo E.hi
  let step:=2*T-A
  let l:=max b.1 (S/step)
  apply List.all_eq_true.mpr
  intro d mem
  have fit : b.1≤d ∧ d<b.1+(b.2+1-b.1) := List.mem_range'_1.mp mem
  unfold PrefixLeaf245212.rejects
  by_cases zd : LastDigit245212.denom A S T d=0
  · simp [zd]
  have enough : A*(d+1)+S<2*T*(d+1) := Nat.sub_pos_iff_lt.mp (Nat.pos_of_ne_zero zd)
  have ax : A<2*T := by
    by_contra! contra
    have := Nat.mul_le_mul_right (d+1) contra
    omega
  have eq : step+A=2*T := Nat.sub_add_cancel ax.le
  have pos : 0<step := Nat.sub_pos_of_lt ax
  have form : 2*T*(d+1)=(step+A)*(d+1) := by rw [eq]
  have den : LastDigit245212.denom A S T d=step*(d+1)-S := by
    simp only [LastDigit245212.denom,form,Nat.add_mul];omega
  have d0 : S<step*(d+1) := by rw [form,Nat.add_mul] at enough;omega
  have floor : S/step≤d := by
    have := (Nat.div_lt_iff_lt_mul pos).mpr (d0.trans_eq (Nat.mul_comm ..))
    omega
  have low : l≤d := max_le fit.1 floor
  have l0 : S<step*(l+1) := by
    have small : S/step<l+1 := Nat.lt_succ_of_le (le_max_right ..)
    exact ((Nat.div_lt_iff_lt_mul pos).mp small).trans_eq (Nat.mul_comm ..)
  have j : d-l+l=d := Nat.sub_add_cancel low
  have num : A*l+S+(d-l)*A=A*d+S := by
    have h:=congrArg (fun z=>A*z) j
    simp only [Nat.mul_add] at h; nlinarith only [h]
  have dm : step*(l+1)-S+(d-l)*step=LastDigit245212.denom A S T d := by
    rw [den]
    have h:=congrArg (fun z=>step*z) j
    simp only [Nat.mul_add] at h
    have a:=Nat.sub_add_cancel l0.le
    have b:=Nat.sub_add_cancel d0.le
    simp only [Nat.mul_add,mul_one] at a b ⊢
    nlinarith only [a,b,h]
  have yes' : scan A (A+S) step R.lo R.hi (b.2+1-l) (A*l+S) (step*(l+1)-S)=true := by
    simpa only [skip,show 2*T-A≠0 from pos.ne',if_false] using yes
  have q := at_step (j:=d-l) (by omega) yes'
  dsimp only at q
  rw [num,dm] at q
  change (A+S)%(candidate A S T d)≠0 ∨ candidate A S T d<R.lo ∨ R.hi<candidate A S T d at q
  rcases q with q|q|q <;> simp [q]

def test (p q : ℕ) (b : Box) : Bool :=
  let R:=b 4;let E:=b 3
  let short:=R.hi-R.lo<640
  let pack:=if short then WheelPrefix245212.pack R else ⟨[],1⟩
  decide (1<R.lo) && ((b 0).entries.all fun k=>(b 1).entries.all fun e=>(b 2).entries.all fun f=>
    (let A:=wt 3 k*wt p e*wt q f;let S:=sig 3 k*sig p e*sig q f;let T:=tax 3 k*tax p e*tax q f
     (short && SingleWheel245212.veto pack A S T R E) || skip A S T R E ||
       QuickPrefix245212.quick A S T R.lo R.hi E.lo E.hi))

def rule := PrefixRule245212.withPrefix test GeoRule245212.rule

theorem sound : AdvanceSound rule := by
  apply PrefixRule245212.prefix_sound _ GeoRule245212.sound
  intro p q b h v fit c
  obtain ⟨base,all⟩:=Bool.and_eq_true_iff.mp h
  have k:=List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp all (v 0)
    (Range.mem_entries (fit 0))) (v 1) (Range.mem_entries (fit 1))) (v 2) (Range.mem_entries (fit 2))
  have no:=OMA.SingleWheel245212.veto_ok (OMA.WheelPrefix245212.candidateVeto c (fit 3) (fit 4))
  let bb : Box:=![⟨v 0,v 0⟩,⟨v 1,v 1⟩,⟨v 2,v 2⟩,b 3,b 4]
  have inside : Fits bb v := by intro i; fin_cases i <;> first | exact ⟨le_rfl,le_rfl⟩ | apply fit
  apply prefix_sound (b:=bb) _ v inside c
  simp [exactBlock,bb,Range.entries]
  refine ⟨base,?_⟩
  dsimp only at k
  by_cases short : (b 4).hi-(b 4).lo<640
  all_goals
    simp only [short,if_true,if_false,decide_true,decide_false,Bool.true_and,Bool.false_and,
      no,Bool.false_or,Bool.or_eq_true_iff] at k
    exact k.elim skip_ok QuickPrefix245212.quick_ok
end OMA.SweepPrefix245212

namespace OMA.CaseJoin245212
open OMA.Box245212
private theorem cover {p q : ℕ} {b : Box} (d : Deny p q b)
    (inside : ∀ i,(b i).lo≤(rootBox p q i).lo ∧ (rootBox p q i).hi≤(b i).hi) :
    Deny p q (rootBox p q) := by
  intro v fit c; apply d v _ c
  exact fun i=>⟨(inside i).1.trans (fit i).1,(fit i).2.trans (inside i).2⟩
theorem finish
    (d5_7 : Deny 5 7 ![⟨2,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨8,999999999999999999⟩])
    (d5_11 : Deny 5 11 ![⟨2,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨12,999999999999999999⟩])
    (d5_13 : Deny 5 13 ![⟨2,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨14,999999999999999999⟩])
    (d5_17 : Deny 5 17 ![⟨2,76224⟩,⟨1,76224⟩,⟨1,76224⟩,⟨1,76224⟩,⟨18,256⟩])
    (d5_19 : Deny 5 19 ![⟨2,23584⟩,⟨1,23584⟩,⟨1,23584⟩,⟨1,23584⟩,⟨20,96⟩])
    (d5_23 : Deny 5 23 ![⟨2,11472⟩,⟨1,11472⟩,⟨1,11472⟩,⟨1,11472⟩,⟨24,50⟩])
    (d5_29 : Deny 5 29 ![⟨2,8400⟩,⟨1,8400⟩,⟨1,8400⟩,⟨1,8400⟩,⟨30,34⟩])
    (d5_31 : Deny 5 31 ![⟨2,7952⟩,⟨1,7952⟩,⟨1,7952⟩,⟨1,7952⟩,⟨32,32⟩])
    (d7_11 : Deny 7 11 ![⟨2,5824⟩,⟨1,5824⟩,⟨1,5824⟩,⟨1,5824⟩,⟨12,26⟩])
    (d7_13 : Deny 7 13 ![⟨2,4704⟩,⟨1,4704⟩,⟨1,4704⟩,⟨1,4704⟩,⟨14,19⟩])
    : OMA.R_OeisA245212_conjecture_R1_H1_R1_H2_R1_H2_R1.H2 := by
  apply h2_of_roots
  intro pq mem
  simp only [families,Finset.mem_insert,Finset.mem_singleton] at mem
  rcases mem with h|h|h|h|h|h|h|h|h|h <;> subst pq
  · exact cover d5_7 (by decide +kernel)
  · exact cover d5_11 (by decide +kernel)
  · exact cover d5_13 (by decide +kernel)
  · exact cover d5_17 (by decide +kernel)
  · exact cover d5_19 (by decide +kernel)
  · exact cover d5_23 (by decide +kernel)
  · exact cover d5_29 (by decide +kernel)
  · exact cover d5_31 (by decide +kernel)
  · exact cover d7_11 (by decide +kernel)
  · exact cover d7_13 (by decide +kernel)
end OMA.CaseJoin245212

namespace OMA.OddFaces245212
open OMA.Smooth245212 Finset
theorem cap_anti {a b : ℕ} (ha : 1<a) (hab : a≤b) : limitX b≤limitX a := by
  have a' : (1:ℚ)<a := by exact_mod_cast ha
  have ab : (a:ℚ)≤b := by exact_mod_cast hab
  simp only [limitX,X,Y,sub_zero]
  exact add_le_add_right (one_div_le_one_div_of_le (by linarith) (by linarith)) 1

private theorem compare4 {p u : Fin 4 → ℕ} (h : ∀ i,1<u i) (lower : ∀ i,u i≤p i) :
    (∏ i,limitX (p i))≤∏ i,limitX (u i) := by
  exact prod_le_prod (f:=fun i => limitX (p i)) (g:=fun i => limitX (u i))
    (fun i _ => x_nonneg ((h i).trans_le (lower i)) none)
    (fun i _ => cap_anti (h i) (lower i))

private theorem prime_at_least {p t : ℕ} (hp : Nat.Prime p) (lo : t≤p)
    (no : ¬Nat.Prime t) : t<p := lt_of_le_of_ne lo (fun eq => no (eq ▸ hp))

theorem small_bases {p : Fin 4 → ℕ} (hp : ∀ i,Nat.Prime (p i)) (ord : StrictMono p)
    (odd : 3≤p 0) (big : 257≤p 3) (cap : 2≤∏ i,limitX (p i)) :
    p 0=3 ∧ p 1=5 ∧ (p 2=7 ∨ p 2=11 ∨ p 2=13) := by
  have h01 := ord (by decide : (0:Fin 4)<1)
  have h12 := ord (by decide : (1:Fin 4)<2)
  have h23 := ord (by decide : (2:Fin 4)<3)
  have drop (u : Fin 4 → ℕ) (a : ∀ i,1<u i) (b : ∀ i,u i≤p i)
      (c : (∏ i,limitX (u i))<2) : False := (cap.trans (compare4 a b)).not_gt c
  have first : p 0=3 := by
    by_contra! ne
    have h0 := prime_at_least (hp 0) (by omega : 4≤p 0) (by decide)
    apply drop ![5,6,7,257] (by decide) _ (by decide +kernel)
    intro i; fin_cases i <;> simp <;> omega
  have h1 := prime_at_least (hp 1) (by omega : 4≤p 1) (by decide)
  have second : p 1=5 := by
    by_contra! ne
    have h1' := prime_at_least (hp 1) (by omega : 6≤p 1) (by decide)
    have h2 := prime_at_least (hp 2) (by omega : 8≤p 2) (by decide)
    apply drop ![3,7,9,257] (by decide) _ (by decide +kernel)
    intro i; fin_cases i <;> simp <;> omega
  have third : p 2<17 := by
    by_contra! zl
    apply drop ![3,5,17,257] (by decide) _ (by decide +kernel)
    intro i; fin_cases i <;> simp <;> omega
  refine ⟨first,second,?_⟩
  have h2 := hp 2
  have lb : 6≤p 2 := by omega
  generalize p 2=u at h2 lb third ⊢
  interval_cases u <;> norm_num at *

end OMA.OddFaces245212

namespace OMA.Large245212
open OMA.Smooth245212 OMA.LastDigit245212 Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma Function
abbrev B := Fin 3 → Band
def bases (q : ℕ) : Fin 3 → ℕ := ![3,5,q]
def prefProd (f : ℕ → Option ℕ → ℚ) (q : ℕ) (e : Fin 3 → ℕ) :=
  ∏ i,f (bases q i) (some (e i))

def full (f : ℕ → ℕ → ℕ) (q : ℕ) (e : Fin 3 → ℕ) := ∏ i,f (bases q i) (e i)
def prev (q : ℕ) (e : Fin 3 → ℕ) := total (bases q) e
private theorem full_mom {q : ℕ} (hq : q=7 ∨ q=11 ∨ q=13) (e : Fin 3 → ℕ) :
    full sig q e=σ 1 (prev q e) ∧ full wt q e=W (prev q e) ∧
      full tax q e=prev q e*(σ 0 (prev q e)) := by
  have hp (i : Fin 3) : Nat.Prime (bases q i) := by
    rcases hq with rfl|rfl|rfl <;> fin_cases i <;> decide
  have diff : Function.Injective (bases q) := by rcases hq with rfl|rfl|rfl <;> decide
  let z (i : Fin 3) := bases q i ^ e i
  have cp : (↑(univ : Finset (Fin 3)) : Set (Fin 3)).Pairwise (Nat.Coprime on z) := by
    intro i _ j _ ij
    exact (((Nat.coprime_primes (hp i) (hp j)).mpr (fun h => ij (diff h))).pow_left _).pow_right _
  have hs := IsMultiplicative.map_prod z (isMultiplicative_sigma (k:=1)) univ cp
  have hw := IsMultiplicative.map_prod z w_mult univ cp
  have ht := IsMultiplicative.map_prod z (isMultiplicative_sigma (k:=0)) univ cp
  change σ 0 (prev q e)=_ at ht
  dsimp only [z] at hs hw ht
  unfold full
  simp_rw [(moments (hp _) _).1,(moments (hp _) _).2]
  refine ⟨hs.symm,hw.symm,?_⟩
  rw [ht]
  simp only [sigma_zero_apply_prime_pow (hp _),tax,prod_mul_distrib,prev,total]
  exact Nat.mul_comm _ _

def test (R A S T t : ℕ) : Bool :=
  let d:=t-1
  let D:=denom A S T d
  let p:=candidate A S T d
  decide (D=0 ∨ p<R ∨ ¬p∣A+S ∨ (1<d ∧ A*d+S=D*p) ∨ (d=1 ∧ A*d+S≠D*p))

theorem valid_exact {q r d : ℕ} (hq : q=7 ∨ q=11 ∨ q=13) (e : Fin 3 → ℕ)
    (hr : r.Prime) (hd : 0<d) (R : ℕ) (big : R≤r) (cop : (prev q e).Coprime r)
    (eq : OeisA245212.a (prev q e*r^d)=(σ 1 (prev q e*r^d):ℤ)) :
    test R (full wt q e) (full sig q e) (full tax q e) (d+1)=false := by
  obtain ⟨hs,hw,ht⟩ := full_mom hq e
  rw [hs,hw,ht]
  let m := prev q e
  have mp : 0 < m := by
    change 0<∏ i : Fin 3,bases q i ^ e i
    exact prod_pos (fun i _ => pow_pos (by rcases hq with rfl|rfl|rfl <;> fin_cases i <;> decide) _)
  have sp : 0<σ 1 m := by
    rw [sigma_one_apply]
    exact sum_pos' (fun _ _ => Nat.zero_le _) ⟨1,Nat.one_mem_divisors.mpr mp.ne',by decide⟩
  have div := OMA.OddCofactor245212.last_dvd mp hr cop hd eq
  obtain ⟨D,lo,hi,strict⟩ := balance_digits mp hr cop hd eq
  have same := force sp hr.one_lt D lo hi
  have atOne (h : d=1) : W m*d+σ 1 m=denom (W m) (σ 1 m) (m*(σ 0 m)) d*r := by
    subst d
    have b := OMA.Abundance245212.balance (mul_ne_zero mp.ne' (pow_ne_zero 1 hr.ne_zero)) eq
    rw [pow_one,w_mult.map_mul_of_coprime cop,isMultiplicative_sigma.map_mul_of_coprime cop,
      isMultiplicative_sigma.map_mul_of_coprime cop] at b
    have w := w_pow hr 1
    have s := sigma_one_apply_prime_pow hr (i:=1)
    have t := sigma_zero_apply_prime_pow hr (i:=1)
    simp [sum_range_succ] at w s t
    rw [w,s,t] at b
    have le : W m*(1+1)+σ 1 m≤2*(m*(σ 0 m))*(1+1) := by dsimp [denom] at D; omega
    have cut := Nat.sub_add_cancel le
    change denom (W m) (σ 1 m) (m*(σ 0 m)) 1+_= _ at cut
    nlinarith only [b,congrArg (fun z:ℕ => z*r) cut]
  change test R (W m) (σ 1 m) (m*(σ 0 m)) (d+1)=false
  simp only [test,Nat.add_sub_cancel,same,decide_eq_false_iff_not]
  rintro (z|sm|nd|⟨lg,bad⟩|⟨one,bad⟩)
  · omega
  · omega
  · exact nd div
  · exact (strict lg).ne bad
  · exact bad (atOne one)

end OMA.Large245212

namespace OMA.Large245212
open OMA.Smooth245212 Finset
open scoped ArithmeticFunction.sigma
def Deny (R q : ℕ) (b : B) := ∀ (e : Fin 3 → ℕ), (∀ i,(b i).Contains (e i)) →
  ∀ r d : ℕ, Nat.Prime r → 0<d → R≤r → (prev q e).Coprime r →
  prefProd X q e*X r (some d)+prefProd Y q e*Y r (some d)=2 →
  OeisA245212.a (prev q e*r^d)≠(σ 1 (prev q e*r^d):ℤ)

def cutAt (a : Band) := match a.hi with
  | none => 2*a.lo+1
  | some h => max a.lo (min (h-1) (2*(a.lo+1)*(h+1)/(a.lo+h+2)-1))
def leftB (b : B) (i : Fin 3) : B := Function.update b i ⟨(b i).lo,some (cutAt (b i))⟩
def rightB (b : B) (i : Fin 3) : B := Function.update b i ⟨cutAt (b i)+1,(b i).hi⟩

theorem split {R q : ℕ} (b : B) (i : Fin 3) (l : Deny R q (leftB b i)) (r : Deny R q (rightB b i)) :
    Deny R q b := by
  intro e inside
  by_cases low : e i≤cutAt (b i)
  · apply l
    intro j; by_cases ji : j=i
    · subst j; simpa [leftB,Band.Contains] using And.intro (inside i).1 low
    · simpa [leftB,ji] using inside j
  · apply r
    intro j; by_cases ji : j=i
    · subst j; simpa [rightB,Band.Contains] using And.intro (by omega : cutAt (b i)+1≤e i) (inside i).2
    · simpa [rightB,ji] using inside j

def start : B := fun _ => ⟨1,none⟩

end OMA.Large245212

namespace OMA.Infinity245212
open OMA.Smooth245212 OMA.FastDigit245212 Finset
open OMA.Large245212 (B Deny bases prefProd)
open OMA.Large245212 (y_both)
open scoped ArithmeticFunction.sigma

abbrev M := OMA.FastFactor245212.scale
abbrev R : ℕ := 10^18

def span (p : ℕ) (b : Band) : Span :=
  let u := OMA.FastFactor245212.highY ⟨p,p⟩ ⟨b.lo,b.lo⟩
  let l := match b.hi with | none => 0 | some h => OMA.FastFactor245212.smallQuot p h
  ⟨M+(M-u)/(p-1),l,M+(M-l)/(p-1)+1,u⟩

private theorem span_ok {p e : ℕ} (hp : 1<p) (b : Band) (fit : b.Contains e) :
    ((span p b).xl:ℚ)≤M*X p (some e) ∧ (M:ℚ)*X p (some e)≤(span p b).xu ∧
    ((span p b).yl:ℚ)≤M*Y p (some e) ∧ (M:ℚ)*Y p (some e)≤(span p b).yu := by
  have z {h : ℕ} (hi : e≤h) := OMA.FastFactor245212.bounds (pb:=⟨p,p⟩) (eb:=⟨b.lo,h⟩)
    (p:=p) (e:=e) hp ⟨le_rfl,le_rfl⟩ ⟨fit.1,hi⟩
  cases H : b.hi with
  | some h => simpa [span,H,OMA.FastFactor245212.lowX,OMA.FastFactor245212.highX,
      OMA.FastFactor245212.lowY,OMA.FastFactor245212.highY] using z (fit.2 _ H)
  | none =>
    obtain ⟨xl,xu,_,yu⟩:=z (le_refl e)
    refine ⟨xl,?_,?_,yu⟩
    · apply xu.trans
      simp only [span,H,OMA.FastFactor245212.highX,Nat.sub_zero]
      exact_mod_cast Nat.add_le_add_right (Nat.add_le_add_left
        (Nat.div_le_div_right (Nat.sub_le _ _)) _) 1
    · simp only [span,H,Nat.cast_zero]; exact mul_nonneg (Nat.cast_nonneg _) (y_nonneg hp _)

def triple (s : Fin 3 → Span) : Span :=
  let mul (f : Span→ℕ) := f (s 0)*f (s 1)*f (s 2)
  ⟨mul Span.xl,mul Span.yl,mul Span.xu,mul Span.yu⟩

private theorem product {n : Fin 3→ℕ} {x : Fin 3→ℚ} (le : ∀ i,(n i:ℚ)≤M*x i) :
    ((n 0*n 1*n 2:ℕ):ℚ)≤(M^3:ℕ)*(∏ i,x i) := by
  have h:=prod_le_prod (s:=(univ:Finset (Fin 3))) (f:=fun i=>(n i:ℚ))
    (fun _ _=>Nat.cast_nonneg _) (fun i _=>le i)
  simpa only [Fin.prod_univ_three,prod_mul_distrib,prod_const,card_univ,Fintype.card_fin,
    mul_assoc,Nat.cast_mul,Nat.cast_pow] using h

private theorem product' {n : Fin 3→ℕ} {x : Fin 3→ℚ} (nn : ∀ i,0≤x i) (le : ∀ i,(M:ℚ)*x i≤n i) :
    (M^3:ℕ)*(∏ i,x i)≤((n 0*n 1*n 2:ℕ):ℚ) := by
  have h:=prod_le_prod (s:=(univ:Finset (Fin 3))) (g:=fun i=>(n i:ℚ))
    (fun i _=>mul_nonneg (Nat.cast_nonneg _) (nn i)) (fun i _=>le i)
  simpa only [prod_mul_distrib,prod_const,card_univ,Fintype.card_fin,Fin.prod_univ_three,
    mul_assoc,Nat.cast_mul,Nat.cast_pow] using h

def Z := M^3
def lower (V : Span) := max 2 (V.yl/(2*Z-V.xl)+1)
def upper (V : Span) := R*V.yu / (2*(R-1)*Z-R*V.xu)

private theorem cap_mul {r z x y d : ℤ} (nx : 0≤x)
    (h : (r-1)*((d+1)*(2*z-x)-y)<d*x+y) :
    (d+1)*(2*(r-1)*z-r*x)≤r*y := by linarith only [h,nx]

set_option maxHeartbeats 2000000 in
private theorem bounds {q d r : ℕ} (hq : 1<q) (pr : r.Prime) (gd : 0<d) (big : R≤r)
    (b : B) (e : Fin 3→ℕ) (fit : ∀ i,(b i).Contains (e i))
    (value : prefProd X q e*X r (some d)+prefProd Y q e*Y r (some d)=2) :
    let V:=triple fun i=>span (bases q i) (b i)
    V.xl<2*Z ∧ lower V≤d+1 ∧ (R*V.xu<2*(R-1)*Z → d+1≤upper V) := by
  let S i:=span (bases q i) (b i)
  let V:=triple S
  have one (i : Fin 3) : 1<bases q i := by fin_cases i <;> simp [bases,hq]
  have s (i) := span_ok (one i) (b i) (fit i)
  have xn (i) := x_nonneg (one i) (some (e i))
  have yp (i) : 0<Y (bases q i) (some (e i)) :=
    (show (0:ℚ)<1/((e i:ℚ)+1) by positivity).trans_le (OMA.Large245212.y_both (one i)).1
  have h:=obey_of_score (b:=V) (Z:=Z) (d:=d) (l:=R) (h:=r) (pow_pos OMA.FastFactor245212.scale_pos 3)
    pr gd (prod_nonneg fun i _=>xn i) (prod_pos fun i _=>yp i) (by decide) big le_rfl value
    (product (n:=fun i=>(S i).xl) (x:=fun i=>X (bases q i) (some (e i))) fun i=>(s i).1)
    (product (n:=fun i=>(S i).yl) (x:=fun i=>Y (bases q i) (some (e i))) fun i=>(s i).2.2.1)
    (product' (n:=fun i=>(S i).xu) xn fun i=>(s i).2.1)
    (product' (n:=fun i=>(S i).yu) (fun i=>(yp i).le) fun i=>(s i).2.2.2)
  obtain ⟨h1,_,h3⟩:=h
  simp only [dI,nI] at h1 h3
  change V.xl<2*Z ∧ lower V≤d+1 ∧ (R*V.xu<2*(R-1)*Z → d+1≤upper V)
  have ax : V.xl<2*Z := by
    by_contra! no
    have ne : (2:ℤ)*Z-V.xl≤0 := sub_nonpos.mpr (by exact_mod_cast no : (2:ℤ)*Z≤V.xl)
    have bad:=mul_nonpos_of_nonneg_of_nonpos (show 0≤(d:ℤ)+1 by positivity) ne
    omega
  refine ⟨ax,max_le (by omega) ?_,fun pos=>?_⟩
  · have h' : V.yl<(d+1)*(2*Z-V.xl) := by
      exact_mod_cast (by push_cast [Nat.cast_sub ax.le]; linarith only [h1] : (V.yl:ℤ)<((d+1)*(2*Z-V.xl):ℕ))
    have small := (Nat.div_lt_iff_lt_mul (Nat.sub_pos_of_lt ax)).mpr h'
    exact small
  · apply (Nat.le_div_iff_mul_le (Nat.sub_pos_of_lt pos)).mpr
    have R1 : 1≤R := by decide
    have converted : ((d+1:ℕ):ℤ)*(2*((R:ℤ)-1)*Z-(R:ℤ)*V.xu)≤(R:ℤ)*V.yu := by
      rw [Nat.cast_add,Nat.cast_one];exact cap_mul (Nat.cast_nonneg _) h3
    exact_mod_cast (show (((d+1)*(2*(R-1)*Z-R*V.xu):ℕ):ℤ)≤((R*V.yu:ℕ):ℤ) by
      simpa only [Nat.cast_mul,Nat.cast_sub pos.le,Nat.cast_sub R1,Nat.cast_one,Nat.cast_ofNat] using converted)

def fixed (b : Band) := b.hi==some b.lo

def witness (q : ℕ) (b : B) (lo hi : ℕ) : Bool :=
  let raw (f : ℕ→ℕ→ℕ) := f 3 (b 0).lo*f 5 (b 1).lo*f q (b 2).lo
  let A:=raw OMA.Large245212.wt;let S:=raw OMA.Large245212.sig;let T:=raw OMA.Large245212.tax
  (List.range' lo (hi+1-lo)).all (OMA.Large245212.test R A S T)

private theorem witness_sound {q d r : ℕ} (hq : q=7 ∨ q=11 ∨ q=13) (pr : r.Prime)
    (gd : 0<d) (big : R≤r) (b : B) (e : Fin 3→ℕ) (fit : ∀ i,(b i).Contains (e i))
    (closed : fixed (b 0) && fixed (b 1) && fixed (b 2))
    (cop : (OMA.Large245212.prev q e).Coprime r)
    (eq : OeisA245212.a (OMA.Large245212.prev q e*r^d)=(σ 1 (OMA.Large245212.prev q e*r^d):ℤ))
    {lo hi : ℕ} (ok1 : lo≤d+1) (ok2 : d+1≤hi) (done : witness q b lo hi=true) : False := by
  obtain ⟨⟨f,g⟩,h⟩ := (Bool.and_eq_true_iff.mp closed).imp_left Bool.and_eq_true_iff.mp
  have matchLo (i : Fin 3) : (b i).lo=e i := by
    have z : fixed (b i)=true := by fin_cases i <;> assumption
    exact le_antisymm (fit i).1 ((fit i).2 _ (beq_iff_eq.mp z))
  have got:=List.all_eq_true.mp done (d+1) (List.mem_range'_1.mpr ⟨ok1,by omega⟩)
  have bad:=OMA.Large245212.valid_exact hq e pr gd R big cop eq
  simp only [OMA.Large245212.full,Fin.prod_univ_three,bases,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,mul_assoc] at bad
  simp only [matchLo,mul_assoc] at got
  exact Bool.noConfusion (got.symm.trans bad)

def tip (q : ℕ) (b : B) (v : Span) : Bool :=
  (2*Z≤v.xl) || (R*v.xu<2*(R-1)*Z &&
    (upper v<lower v || (fixed (b 0) && fixed (b 1) && fixed (b 2) && witness q b (lower v) (upper v))))

private theorem tip_ok {q : ℕ} (hq : q=7 ∨ q=11 ∨ q=13) (b : B)
    (yes : tip q b (triple fun i=>span (bases q i) (b i))=true) : Deny R q b := by
  intro e fit r d pr gd big cop score eq
  have qp : 1<q := by rcases hq with rfl|rfl|rfl <;> decide
  obtain ⟨ax,lo,cap⟩:=bounds qp pr gd big b e fit score
  simp only [tip,Bool.or_eq_true_iff,Bool.and_eq_true_iff,decide_eq_true_eq] at yes
  rcases yes with h|⟨pos,h|⟨fix,w⟩⟩
  · exact (not_le_of_gt ax) h
  · exact (not_lt_of_ge (lo.trans (cap pos))) h
  · exact witness_sound hq pr gd big b e fit (by simpa only [Bool.and_eq_true_iff] using fix)
      cop eq lo (cap pos) w

def pick (q : ℕ) (b : B) (s : Fin 3→Span) : Fin 3 :=
  let w (i : Fin 3) := if fixed (b i) then 0 else ((s i).yu-(s i).yl)/(bases q i-1)+1
  if w 1≤w 0 && w 2≤w 0 then 0 else if w 2≤w 1 then 1 else 2


/-- Keep the two unchanged normalized intervals at each binary split. -/
structure Axis where
  band : Band
  hull : Span
  weight : ℕ

def axis (p : ℕ) (b : Band) : Axis :=
  let s:=span p b
  ⟨b,s,if fixed b then 0 else (s.yu-s.yl)/(p-1)+1⟩

def left (p : ℕ) (a : Axis) := axis p ⟨a.band.lo,some (OMA.Large245212.cutAt a.band)⟩
def right (p : ℕ) (a : Axis) := axis p ⟨OMA.Large245212.cutAt a.band+1,a.band.hi⟩

def go (q : ℕ) : ℕ→Axis→Axis→Axis→Bool
  | 0,_,_,_=>false
  | n+1,a,b,c=>
    let v : Span := ⟨a.hull.xl*b.hull.xl*c.hull.xl,a.hull.yl*b.hull.yl*c.hull.yl,
      a.hull.xu*b.hull.xu*c.hull.xu,a.hull.yu*b.hull.yu*c.hull.yu⟩
    tip q ![a.band,b.band,c.band] v ||
      if b.weight≤a.weight && c.weight≤a.weight then
        go q n (left 3 a) b c && go q n (right 3 a) b c
      else if c.weight≤b.weight then
        go q n a (left 5 b) c && go q n a (right 5 b) c
      else go q n a b (left q c) && go q n a b (right q c)

private theorem branch {q : ℕ} (i : Fin 3) (b : B) {l r : B}
    (hl : ∀ j,OMA.Large245212.leftB b i j=l j) (hr : ∀ j,OMA.Large245212.rightB b i j=r j)
    (a : Deny R q l) (c : Deny R q r) : Deny R q b :=
  OMA.Large245212.split b i (funext hl ▸ a) (funext hr ▸ c)

theorem go_ok {q : ℕ} (hq : q=7 ∨ q=11 ∨ q=13) (fuel : ℕ) (a b c : Band)
    (ok : go q fuel (axis 3 a) (axis 5 b) (axis q c)=true) : Deny R q ![a,b,c] := by
  induction fuel generalizing a b c with
  | zero=>cases ok
  | succ n ih=>
    unfold go at ok
    rcases Bool.or_eq_true_iff.mp ok with tip|fork
    · exact tip_ok hq _ tip
    · split_ifs at fork with f g
      · obtain ⟨l,r⟩:=Bool.and_eq_true_iff.mp fork
        apply branch 0 _ _ _ (ih _ _ _ l) (ih _ _ _ r) <;> intro j <;> fin_cases j <;> rfl
      · obtain ⟨l,r⟩:=Bool.and_eq_true_iff.mp fork
        apply branch 1 _ _ _ (ih _ _ _ l) (ih _ _ _ r) <;> intro j <;> fin_cases j <;> rfl
      · obtain ⟨l,r⟩:=Bool.and_eq_true_iff.mp fork
        apply branch 2 _ _ _ (ih _ _ _ l) (ih _ _ _ r) <;> intro j <;> fin_cases j <;> rfl

/-- Run a tile with a fixed triple of endpoints. -/
def tile (q : ℕ) (b : B) := go q 70 (axis 3 (b 0)) (axis 5 (b 1)) (axis q (b 2))

theorem tile_ok {q : ℕ} (hq : q=7 ∨ q=11 ∨ q=13) (b : B) (ok : tile q b=true) : Deny R q b := by
  have e : ![b 0,b 1,b 2]=b := by funext i; fin_cases i <;> rfl
  exact e ▸ go_ok hq 70 _ _ _ ok

end OMA.Infinity245212

namespace OMA.Infinity245212
open OMA.Large245212 (B Deny)

/-- Consecutive leaves of a full binary frontier are adjacent dyadic
intervals. Store only the first path and the depths of the sixteen leaves. -/
def readPath : ℕ→ℕ→ℕ→ℕ→ℕ
  | 0,p,_,_=>p
  | k+1,p,d,bits=>
    let e:=bits&&&63
    readPath k (((p+1)<<<e)>>>d) e (bits>>>6)

def pagePath (pages : ℕ→ℕ) (i : ℕ) :=
  let raw:=pages (i/16)
  readPath (i%16) (raw>>>96) (raw&&&63) (raw>>>6)

def child (q : ℕ) (b : B) (right : Bool) : B :=
  let i:=pick q b (fun j=>span (OMA.Large245212.bases q j) (b j))
  if right then OMA.Large245212.rightB b i else OMA.Large245212.leftB b i

structure Frame where
  a : OMA.Smooth245212.Band
  b : OMA.Smooth245212.Band
  c : OMA.Smooth245212.Band

def Frame.box (f : Frame) : B := ![f.a,f.b,f.c]

def changeAt (i : Fin 3) (r : Bool) : Frame→Frame
  | ⟨a,b,c⟩=>
    let next (x : OMA.Smooth245212.Band) := if r then
      ⟨OMA.Large245212.cutAt x+1,x.hi⟩ else ⟨x.lo,some (OMA.Large245212.cutAt x)⟩
    if i=0 then ⟨next a,b,c⟩ else if i=1 then ⟨a,next b,c⟩ else ⟨a,b,next c⟩

def step (q : ℕ) (r : Bool) (f : Frame) : Frame :=
  changeAt (pick q f.box (fun j=>span (OMA.Large245212.bases q j) (f.box j))) r f

private theorem step_box (q : ℕ) (r : Bool) (f : Frame) : (step q r f).box=child q f.box r := by
  unfold step child
  generalize pick q _ _=i
  cases f
  fin_cases i <;> cases r <;> funext j <;> fin_cases j <;> rfl

def frame (q : ℕ) : ℕ→ℕ→Frame
  | 0,_=>⟨⟨1,none⟩,⟨1,none⟩,⟨1,none⟩⟩
  | k+1,n=>step q (n%2=1) (frame q k (n/2))

def boxAt (q n : ℕ) : B := (frame q n.log2 n).box

private theorem siblings (q n : ℕ) (positive : 0<n)
    (l : Deny R q (boxAt q (2*n))) (r : Deny R q (boxAt q (2*n+1))) : Deny R q (boxAt q n) := by
  have a : (2*n).log2=n.log2+1 := Nat.log2_two_mul positive.ne'
  have b : (2*n+1).log2=n.log2+1 := by
    rw [Nat.log2_def];simp only [show 2≤2*n+1 by omega,if_pos,show (2*n+1)/2=n by omega]
  simp only [boxAt,a,b,frame,step_box,show 2*n/2=n by omega,show (2*n+1)/2=n by omega,
    show 2*n%2=0 by omega,show (2*n+1)%2=1 by omega,child] at l r
  exact OMA.Large245212.split _ _ l r

def push : ℕ→ℕ→List ℕ→List ℕ
  | 0,n,s=>n::s
  | _+1,n,[]=>[n]
  | k+1,n,a::s=>if 0<a/2 && a=2*(a/2) && n=2*(a/2)+1 then push k (a/2) s else n::a::s

private def Holds (q : ℕ) (s : List ℕ) := ∀ i∈s,Deny R q (boxAt q i)

private theorem push_ok (q k n : ℕ) (s : List ℕ) (h : Holds q s) (t : Deny R q (boxAt q n)) :
    Holds q (push k n s) := by
  induction k generalizing n s with
  | zero=>intro i mem;rcases List.mem_cons.mp mem with rfl|m;exact t;exact h _ m
  | succ k ih=>
    cases s with
    | nil=>intro i mem;have e : i=n := List.mem_singleton.mp mem;exact e ▸ t
    | cons a s=>
      unfold push
      split_ifs with yes
      · obtain ⟨⟨p,e⟩,f⟩ := (Bool.and_eq_true_iff.mp yes).imp_left Bool.and_eq_true_iff.mp
        have e' := of_decide_eq_true e;have f' := of_decide_eq_true f
        exact ih _ _ (fun i m=>h i (List.mem_cons_of_mem _ m))
          (siblings q _ (of_decide_eq_true p) (e' ▸ h a List.mem_cons_self) (f' ▸ t))
      · intro i mem;rcases List.mem_cons.mp mem with rfl|m;exact t;exact h _ m

theorem root {q : ℕ} (hq : q=7 ∨ q=11 ∨ q=13) (paths : ℕ→ℕ) (count : ℕ)
    (tests : OMA.Tape245212.Before (fun i=>tile q (boxAt q (paths i))) count)
    (covers : (List.range count).foldl (fun s i=>push 70 (paths i) s) []=[1]) : Deny R q OMA.Large245212.start := by
  have all (xs : List ℕ) (sub : ∀ i∈xs,i<count) (s : List ℕ) (h : Holds q s) :
      Holds q (xs.foldl (fun a i=>push 70 (paths i) a) s) := by
    induction xs generalizing s with
    | nil=>exact h
    | cons i is ih=>
      exact ih (fun j m=>sub j (List.mem_cons_of_mem _ m)) _
        (push_ok _ _ _ _ h (tile_ok hq _ (tests _ (sub i List.mem_cons_self))))
  have t:=all (List.range count) (fun _ h=>List.mem_range.mp h) [] (by intro i m;cases m)
  rw [covers] at t
  have one : boxAt q 1=OMA.Large245212.start := by funext i;fin_cases i <;> rfl
  exact one ▸ t 1 List.mem_cons_self

end OMA.Infinity245212

namespace OMA.Large245212
open OMA.Smooth245212 Finset
open scoped ArithmeticFunction.sigma
abbrev cutoff : ℕ := 1000000000000000000
abbrev Certs := ∀ q : ℕ,q=7 ∨ q=11 ∨ q=13 → Deny cutoff q start

theorem four {p e : Fin 4 → ℕ} (cert : Certs) (hp : ∀ i,Nat.Prime (p i))
    (ord : StrictMono p) (odd : 3≤p 0) (positive : ∀ i,0<e i)
    (eq : OeisA245212.a (total p e)=(σ 1 (total p e):ℤ)) : p 3<cutoff := by
  by_contra! large
  have norm := normalized_of_eq p hp ord.injective _ eq
  have cap := OMA.OddFaces245212.cap_needed p e (fun i => (hp i).one_lt) 0 (positive 0) norm
  obtain ⟨a,b,c⟩ := OMA.OddFaces245212.small_bases hp ord odd
    ((by decide : 257≤cutoff).trans large) cap
  let q := p 2
  let r := p 3
  let f (i : Fin 3) := e i.castSucc
  have qq : q=7 ∨ q=11 ∨ q=13 := c
  have pp (i : Fin 3) : p i.castSucc=bases q i := by fin_cases i <;> simp [bases,q,a,b]
  have score : prefProd X q f*X r (some (e 3))+prefProd Y q f*Y r (some (e 3))=2 := by
    unfold normalized at norm
    rw [Fin.prod_univ_castSucc (fun i => X (p i) (some (e i))),
      Fin.prod_univ_castSucc (fun i => Y (p i) (some (e i)))] at norm
    simpa only [pp,prefProd,f,r,show Fin.last 3=(3:Fin 4) by decide] using norm
  have fact : total p e=prev q f*r^(e 3) := by
    simp [total,prev,bases,Fin.prod_univ_four,Fin.prod_univ_three,f,r,q,a,b,mul_assoc]
  have cop (i : Fin 4) (hi : i<3) : (p i).Coprime r :=
    (Nat.coprime_primes (hp i) (hp 3)).mpr (ord hi).ne
  have cm : (prev q f).Coprime r := by
    simp only [prev,total,Fin.prod_univ_three,bases,f,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two]
    have r3 : (3:ℕ).Coprime r := a ▸ cop 0 (by decide)
    have r5 : (5:ℕ).Coprime r := b ▸ cop 1 (by decide)
    exact Nat.coprime_mul_iff_left.mpr ⟨Nat.coprime_mul_iff_left.mpr
      ⟨r3.pow_left _,r5.pow_left _⟩,(cop 2 (by decide)).pow_left _⟩
  exact cert q qq f (fun i => by simp [start,Band.Contains,f]; exact positive _)
    r (e 3) (hp 3) (positive 3) large cm score (fact ▸ eq)


end OMA.Large245212

open Finset OMA.Smooth245212 OMA.Large245212
open scoped ArithmeticFunction.sigma
theorem OMA.Infinity245212.support (cert : Certs) : OMA.R_OeisA245212_conjecture_R1_H1_R1_H2_R1_H2_R1.H1 := by
  intro k p q r e f g hk hp hq hr hp5 pq qr he hf hg n eq
  let P : Fin 4 → ℕ := ![3,p,q,r]
  let E : Fin 4 → ℕ := ![k,e,f,g]
  have pp (i : Fin 4) : Nat.Prime (P i) := by fin_cases i <;> simp [P,hp,hq,hr,Nat.prime_three]
  have pm : StrictMono P := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i; fin_cases i <;> simp [P] <;> omega
  have repr : total P E=n := by simp [total,P,E,n,Fin.prod_univ_four]
  have norm := normalized_of_eq P pp pm.injective E (by rw [repr]; exact eq)
  have cap := OMA.OddFaces245212.cap_needed P E (fun i => (pp i).one_lt) 0 (by simpa [E] using (by omega : 0<k)) norm
  have drop (u : Fin 4 → ℕ) (hu : ∀ i,1<u i) (ge : ∀ i,u i≤P i)
      (cut : (∏ i,OMA.OddFaces245212.limitX (u i))<2) : False := by
    have b := prod_le_prod (s:=univ) (f:=fun i => OMA.OddFaces245212.limitX (P i))
      (fun i _ => x_nonneg ((hu i).trans_le (ge i)) none) (fun i _ => OMA.OddFaces245212.cap_anti (hu i) (ge i))
    exact (cap.trans b).not_gt cut
  have smallP : p≤7 := by
    by_contra! h
    have pm : 11≤p := by by_contra! z; interval_cases p <;> norm_num at *
    apply drop ![3,11,12,13] (by decide) _ (by decide +kernel)
    intro i; fin_cases i <;> simp [P] <;> omega
  have p57 : p∈({5,7}:Finset ℕ) := by interval_cases p <;> norm_num at *
  have smallQ : q≤31 := by
    by_contra! h
    apply drop ![3,5,32,33] (by decide) _ (by decide +kernel)
    intro i; fin_cases i <;> simp [P] <;> omega
  have pos (i : Fin 4) : 0 < E i := by fin_cases i <;> simp [E] <;> omega
  exact ⟨p57,smallQ,four cert pp pm (by change 3 ≤ 3; exact le_rfl) pos (by rw [repr]; exact eq)⟩

namespace OMA.Infinite7_245212
open OMA.Infinity245212 OMA.Tape245212
private def pages := OMA.PageTree245212.get (.p [0x25124503ce30b2881c61440c1,0x1bf77d1c61093d045249049244f4d4,0x1d64524904934d140f34c2ca248,0xebff4503cd2ca24818520924718f,0x7b7ae1c738f4104103ce41144f492,0xf9000000000000000000005187])
private def paths := pagePath pages
private def test (i:ℕ) := tile 7 (boxAt 7 (paths i))
private abbrev C := Cursor test
private def c0 := Cursor.start test
set_option maxHeartbeats 0 in
def c1:C:=c0.atRange 0 20 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c2:C:=c1.atRange 20 34 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c3:C:=c2.atRange 34 46 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c4:C:=c3.atRange 46 54 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c5:C:=c4.atRange 54 68 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c6:C:=c5.atRange 68 78 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c7:C:=c6.atRange 78 83 rfl (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem deny : OMA.Large245212.Deny R 7 OMA.Large245212.start :=
  root (by decide) paths 83 c7.checked (by decide +kernel)
end OMA.Infinite7_245212

namespace OMA.Infinite11_245212
open OMA.Infinity245212 OMA.Tape245212
private def pages := OMA.PageTree245212.get (.p [0x249140f38d30b2481c6143081,0x1efbfc6585d561a6996db699616554,0xf7dff5c59865965a6985d861a71d75b,0x3df7ff4114503cf3ce35040f38d315,0x3dfea39040f4524d3493555511451,0x7c45040f3d145038c2ca2481c6,0xfbfe41d04524d34135145165d7553,0x1fa41144f41145145038c2ca248,0x7eff40f30d34c2ca34e38c2ca24e,0x1fd9330c2ca2cc34d30d38e34f3d0,0x1fe838c30b30d34c34d38f3ce38c,0x7fc900000000000024b30d34c34e])
private def paths := pagePath pages
private def test (i:ℕ) := tile 11 (boxAt 11 (paths i))
private abbrev C := Cursor test
private def c0 := Cursor.start test
set_option maxHeartbeats 0 in
def c1:C:=c0.atRange 0 27 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c2:C:=c1.atRange 27 38 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c3:C:=c2.atRange 38 53 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c4:C:=c3.atRange 53 65 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c5:C:=c4.atRange 65 73 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c6:C:=c5.atRange 73 90 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c7:C:=c6.atRange 90 100 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c8:C:=c7.atRange 100 115 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c9:C:=c8.atRange 115 125 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c10:C:=c9.atRange 125 135 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c11:C:=c10.atRange 135 141 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c12:C:=c11.atRange 141 149 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c13:C:=c12.atRange 149 159 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c14:C:=c13.atRange 159 166 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c15:C:=c14.atRange 166 175 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c16:C:=c15.atRange 175 184 rfl (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem deny : OMA.Large245212.Deny R 11 OMA.Large245212.start :=
  root (by decide) paths 184 c16.checked (by decide +kernel)
end OMA.Infinite11_245212

namespace OMA.Infinite13_245212
open OMA.Infinity245212 OMA.Tape245212
private def pages := OMA.PageTree245212.get (.b 32 (.b 16 (.p [0x24d244f38c2ca248185103081,0x1fdf6e9248e285f79d71b6995d6554,0x7f7dbfbfc8638e28e38a17de75b6a18a2,0xfefb7fb89e8a269648e28249238a181f,0xfefb7fbac9238608639248a3925964923,0x1fdf6ff78b8618a281f75c79f8628e38a4,0x7f7dbfe728218a28a286079f8628e38a2,0x3fbedff508218e38a28a181c79f8228a1,0xfefb7fe206585d551349b71d7e08628e3,0x3fbeef75d7594659617595517659619,0xfefbdc75c6da6586db6996175565d7,0x7f7df37e69965a6985d869a65f86181e,0xfefbea671a65769b6dc71b69e79d71b,0x3fbefb1a6dc71765b71d75d75c6db75d,0x7f7df713d45976196576185d75d865a,0x3fbf45d65545134d3496595513491]) (.p [0xfefde74d45134945554d2454515557,0xfefed556595557618595555513493,0x1fdfe738c2ca251493514493515554,0xff7a5d75954d76596165544d140f,0x3fdefe79c6da6585d65544d140f555,0xff7ddffa7df79d6985944de7a08a285f,0x1fefbf5569c71b69a71d75d75c71d75c,0x3fdf7ed87dd71b6996db6996186dc75d,0x1fefbfafac72cf5d74c289e69648e2860,0xff7dfd7dff8165a6db65a6db7a9aabb2dbaf,0x1fefbfd6155554d86595d65544d05d8,0x3fdfaf251555555459969a61c71b699,0x1fefdc6595545134d34d4513493514,0x1feff295996585d65d75555975d65d8,0x3fdfeb3ce34c4924503ce34c2d14d5,0x1ff5e6da6585d551349140e351450])) (.b 48 (.p [0xffb6fdf71b6996165544d24586595db,0x1ff6efdf6586595d66185d655445861c,0x3fedf515d8618617595597618597619,0x7fdbf35534924514924514503d3516,0x7fddaa4924904104d35176db699616,0x3fef589a59238607de75c6da657595,0xffbd677fde4d34904d4622a29aabb2db67,0x3fef93d35144914d34913ce30f411,0x1ff9a4535144d34d34914d4512450,0x7fe784934d34d14924503904534d2,0x7fe9d4913d049245149249244f452,0xffd864d34d45145134934d34d24d3,0x7fecb38e3d04524d33d04524d3412,0xffe24114514924513d149249244f,0xffe74534d24545554d451349244f,0xffe9844e3d045248f4114924524d3]) (.p [0x3ffc100000000000000030d38f411])))
private def paths := pagePath pages
private def test (i:ℕ) := tile 13 (boxAt 13 (paths i))
private abbrev C := Cursor test
private def c0 := Cursor.start test
set_option maxHeartbeats 0 in
def c1:C:=c0.atRange 0 34 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c2:C:=c1.atRange 34 53 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c3:C:=c2.atRange 53 67 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c4:C:=c3.atRange 67 75 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c5:C:=c4.atRange 75 82 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c6:C:=c5.atRange 82 94 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c7:C:=c6.atRange 94 106 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c8:C:=c7.atRange 106 115 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c9:C:=c8.atRange 115 124 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c10:C:=c9.atRange 124 144 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c11:C:=c10.atRange 144 156 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c12:C:=c11.atRange 156 168 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c13:C:=c12.atRange 168 182 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c14:C:=c13.atRange 182 195 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c15:C:=c14.atRange 195 204 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c16:C:=c15.atRange 204 213 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c17:C:=c16.atRange 213 222 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c18:C:=c17.atRange 222 245 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c19:C:=c18.atRange 245 256 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c20:C:=c19.atRange 256 263 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c21:C:=c20.atRange 263 270 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c22:C:=c21.atRange 270 277 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c23:C:=c22.atRange 277 285 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c24:C:=c23.atRange 285 295 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c25:C:=c24.atRange 295 319 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c26:C:=c25.atRange 319 341 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c27:C:=c26.atRange 341 353 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c28:C:=c27.atRange 353 364 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c29:C:=c28.atRange 364 376 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c30:C:=c29.atRange 376 410 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c31:C:=c30.atRange 410 425 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c32:C:=c31.atRange 425 438 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c33:C:=c32.atRange 438 448 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c34:C:=c33.atRange 448 458 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c35:C:=c34.atRange 458 467 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c36:C:=c35.atRange 467 480 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c37:C:=c36.atRange 480 510 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c38:C:=c37.atRange 510 527 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c39:C:=c38.atRange 527 537 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c40:C:=c39.atRange 537 548 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c41:C:=c40.atRange 548 561 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c42:C:=c41.atRange 561 570 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c43:C:=c42.atRange 570 584 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c44:C:=c43.atRange 584 591 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c45:C:=c44.atRange 591 623 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c46:C:=c45.atRange 623 635 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c47:C:=c46.atRange 635 642 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c48:C:=c47.atRange 642 651 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c49:C:=c48.atRange 651 658 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c50:C:=c49.atRange 658 666 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c51:C:=c50.atRange 666 674 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c52:C:=c51.atRange 674 681 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c53:C:=c52.atRange 681 689 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c54:C:=c53.atRange 689 698 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c55:C:=c54.atRange 698 705 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c56:C:=c55.atRange 705 720 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c57:C:=c56.atRange 720 729 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c58:C:=c57.atRange 729 735 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c59:C:=c58.atRange 735 743 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c60:C:=c59.atRange 743 751 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c61:C:=c60.atRange 751 761 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c62:C:=c61.atRange 761 774 rfl (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem deny : OMA.Large245212.Deny R 13 OMA.Large245212.start :=
  root (by decide) paths 774 c62.checked (by decide +kernel)
end OMA.Infinite13_245212

theorem OMA.Infinity245212.bound : OMA.R_OeisA245212_conjecture_R1_H1_R1_H2_R1_H2_R1.H1 := by
  apply support
  intro q cases
  rcases cases with rfl|rfl|rfl
  · exact OMA.Infinite7_245212.deny
  · exact OMA.Infinite11_245212.deny
  · exact OMA.Infinite13_245212.deny


namespace OMA.TapeShared245212
def rule := OMA.SweepPrefix245212.rule
theorem valid : OMA.SparseEngine245212.AdvanceSound rule := OMA.SweepPrefix245212.sound
def model : ℕ := 0x582e1f8219efaf68b5287d081092e3000000000000000000000000000000000000000000000000000000000000000000f1ee1f26fdb4d4b23dac48cae1d703da7ddf1cbd6b23426f8fc10abe65e22bba8b79c8f5776d077c8109e36857ac96a329b2f5e9e1d67f4204817d93549d6720b65b763e4a1dfd0465ae974dc79655de5bf1f20724b2836952d74d60dd7bc1fae5c21fec92b855c6795fa75e6967fc1c80ca2c9df85796967997137dbf091c328b237e3657b7d365a6dcf1d2092b70cb1f8db5000000000000000000000000000000000000000000000000000000000d1c00000000000000000000000000001a0000000000000000000000000000190395badc3207282d8be3525f79dd1c000000000000000000000000000000000000000000000000015d57d385af0000000000000000002020f8574b6fdfae535832872422f87f62356ded1a000000e43ddee07d572b6202274ad60000000000000000000000000000000000000000000000000004f60b4aea017dd5e4308a7c920bdb81f56ddd190000005f97760df278288d421f49d500000000000000a5f62480b4d669d3000000000000000000000000000000e5a71f75edc3db81c8289d6b9cbbf4b6cd9d2f859f7950aa1c92889b5bf469605f0c894b4e8d82e3524a1ebab45db6770c14c72c2276238d4a9669f46960d7d9e9f5af4747bc810b24a7e38bcdeae1c5b41f62352c9ac429ebe3899737d552387c7da72c427429dbe30a27dd7b7e321c8d3570ad8b109be3e436b74fc278d5f20a1c4d0b9eb6e30bcc776f67f81de25ad3528420bae38030b6df8d5f25b21d647284d0b9e3000000000000000000000000000034e938b9aa6dbbe17d4420b1c98f429febb857e22d87d1612ad4920b7e329eef9817d788b62041d599f24bd2329d000000def76221cd351f8d8a1232c9db8ebce617e5d494c42d7207d0a8db01f49bdeb59ae361f42448752888cb0000224db55d9f523880910a8c7d0b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006b92205975622921d1d2179d6df1232d42382757c4d39ea04ca5a1557ee26df74a2387831c2d7ae5c804874f237db9cbe4a1f8683260136ec28bcd239eb57a2d92bb2048780c9dbc882d63000000000000000000000000000000000000000000000000000000000000ec3eb90b6afc9e0be1d62248287d231156dd5cabdfacb9f8207d890f5d23ebb7c20f89fcaefdb51f42c82898c40000000000000006f5744d082a224b000000000000000000000000000000
def codes : ℕ := 0x899890c40551850840669890a405418506406a1890c40549850840559890a40539850640781890c40551850840661890a40541850640671890c40549850840559890a40539850640789890c40551850840669890a405418506406a1890c40549850840559890a40539850640779890c40551850840661890a40541850640671890c40549850840559890a40539850640891890c40551850840669890a405418506406a1890c40549850840559890a40539850640781890c40551850840661890a40541850640671890c40549850840559890a40539850640789890c40551850840669890a405418506406a1890c40549850840559890a40539850640779890c40551850840661890a40541850640671890c40549850840559890a40539850640

end OMA.TapeShared245212
namespace OMA.Tape5_7_245212
open OMA.Box245212 OMA.RankTape245212 OMA.TapeShared245212
private def vals := OMA.PageTree245212.get (.b 64 (.b 32 (.b 16 (.p [1,2,3,4,5,6,7,8,9,10,11,13,14,15,16,17]) (.p [22,23,25,26,27,28,29,30,31,32,33,34,35,39,40,46])) (.b 48 (.p [47,50,51,54,58,59,61,62,63,65,66,67,69,70,71,94]) (.p [95,102,103,106,107,118,119,126,127,132,133,134,139,142,143,158]))) (.b 96 (.b 80 (.p [159,175,185,186,197,210,211,212,238,239,259,286,287,290,305,310]) (.p [311,336,350,351,362,414,580,581,672,673,702,703,828,829,830,919])) (.b 112 (.p [924,1660,1661,0xde0b6b3a763ffff,0x1194016689cceefdec,0x1438153583cd19c1d6,0x19a23e6db0f50228be,0x1caa8dbd637741d2b5,0x1caa8dbd637741d340,0x1fe3aeb80e426218bb,0x21dc775b3d0983f8fa,0x23db429df515f8b624,0x23db429df515f8b6fc,0x2f48238a53aaf207d3,0x2f9c78a8c10a4ecc8d,0x2f9c78a8c10a4ecc8e]) (.p [0x381357d378e3127794,0x38ed7ec8a39c063e6c,0x391e73188090a8ae61,0x3ff9006bf198d98a19,0x4189a5d9998ffb35cd,0x42424a0cfb94beba82,0x47a4f822a6277ee57a,0x4a756a356c78a75257,0x4ac47059c80fdb3bfc,0x4f7d935ff72fb78c3d,0x4f7d935ff72fb78c3e,0x5705d1291130b5012e,0x5953e2ee24156e32c8,0x5953e2ee24156e32ca,0x63b483fd0519192177,0x68155a43676e002c70]))))

private def rows := OMA.PageTree245212.get (.b 96 (.b 48 (.b 16 (.p [0x2c473187fe03f800200181050000,0x17358e1cf739ad60058afe00080fe08181100000,0x2e6579ae5e0d686a29751c98851adf27884b0684210c058afe03f820a081812e0000,0x50b99b0defe15e24e6b2968a38e5f81bc5bad054428d6f5d0b43abf11bffa7b475cbc727fd0a0bfacd31567b7930f3c18a60578efb8aae183cf6554f4193ff9c5768891678b94d5afda43b7dc576624c6efa8f34f3239a6b7e10b458afe03f82fe18181af0000,0x2458afe03f82fe08181010002,0x144707fe03f80fe08181020004,0x1fee0ffe03f81fe08081010000,0xc41d081fc421627a4470548ffe03f820e0c1821b0000,0x3ea241e1e19ce44d265130ffe00282fe20182160000,0xb885cc98aee2a62ce1ac88f0203f86fe20182140000,0xfcca235358cc7f6954bd1b29563990c43b5bf6b459b30903915650ca95e96cf26015eb58cdb3a57f26204f31c98057ae87563345264c72c87c224c852666948d6fde111d4ca69ca32985b9f9bbac1f42110a68b488ffe0bf86fe20182b30000,0x4498ffe03f86fe20182020002,0x1fd316fe03f86fe28102010000,0xb7214110ac0d48b5562fc910e642c0c5eae8471316fe03f8620281832f0000,0x47d145bca3f98516379241aa50f598464e6ba371316fe00707fe441832d0000,0x1beaf7d58da654af4b67a61340d2d633450acbda044f65639310a069742d156bf690eee3a6044e96fe03f8ffe44183500000]) (.b 32 (.p [0x17dbd7adebf4524e81a955246afdbbcbd7aecc2dd573b8871570c48a2d732a4af112a78a2919b7b84ce09e6ee0c952557ad6bd430a2e91779dc4283532985aa8503f8cee2149110a2e50531efe03f8ffe44183980000,0x9316fe03f8ffe44183010002,0x36d316fe03f86fe44183020004,0x25316fe03f86fe28183010006,0x18c5314fe03f86fe20182030008,0x930ffe03f86fe2018201000a,0x14548ffe03f82fe2018202000e,0x284ee0ffe03f81fe08182040010,0x126f18ffe03f80fe08181030012,0xb187fe03f80fe08181010014,0x27187fe03f80fe0018101001a,0x352f2c1d4878103054d66578e5f3aa4f12f39b9120c84206200c7058afe03f8002004843a0000,0x26b6695fd5c62b378cde4f77a4b37a4037c5a648ec60fe15eff75632bc72f95d4706704bd21ae85a4a1639b9d6243fe841bf1a0946f1718e5c47a48f74e8da341677fc48277319858afe03f800203f8a860000,0x184707fe03f800203f84020002,0x31074fc40de0842c90a5447318ffe03f8002004841c0000,0x8f540991be57a21e477731812b8318ffe001810203f8a1e0000]) (.p [0x7f409212a16108542168b58a492e8f6f3731e24130c0ffe03f84020080a320000,0x1d2378923e4f2b374690215c1beb8a1e89ff7bffd7beb8f93c22f432e93f9cbfc8e2d20d3e015e28db0691bc494f09b1ec62c26f9dd1bd63bbdeee441a21cbc523e2e1fc13e0862426e6911facde0ec606d090488b64c0ffe03f840203f91a70000,0x184d8ffe03f840203f8a020002,0x1ff19cf803f840003f8c010000,0x2dcfcdaa500bfa017f5b5610855a64bf77e01e8c41900bd5d07319cf803f840204a8c3c0000,0x11facde0ac1a9cac402b122630276d75b319cf8004840207f96240000,0xff12114c88c69cacfad4a9e24b21468668b10a439d93fe68b0569cf803f8a0207f96380000,0x16429f27ab250088c81c9133e044066108547cdb40cd87125d0834427db10731aeee03f8a02052164e0000,0x8f59ec4841a01026e6bdac18e0ac5b4c565bad35b31aeee0080a0207fa5310000,0x18437116118d3959fd399c48598abbdcf92bec18b05eaeee03f910207fa52d0000,0x11a23590a7c53e29c403db10731bee603f910205aa51e0000,0x13093b3dec5df5a63146f5b31bee600f910207fb6170000,0x508c32825bee603fa00207fb60c0000,0xade15b31ccd6017a00206436090000,0xdaf1cc0203fb00206436020000,0x3282b4dd60bfb00206436060000]))) (.b 64 (.p [0xf12421508d1cbe5211a397ed878705211a397ca423472fc3590bb0e2c9cbef62eb7834c81ef029c40331d7d20bfb00205fb65d0000,0xcb032a5f212726432319121912191219121a6463226702b79de779de779dffc6020d902933669b056c59a0328057b3ce78e8cd82b06380c9c182838b3406500ef1d7d20bfb002064409a0000,0xb31d7d60bfb00206436020002,0xcff1ccd60bfb00206436020004,0xf1ccd603fb00206436010006,0xd31cce003fa00206436020008,0xc7f1cc0201d200207fc9030000,0x309844282c51ca09d200207fc90b0000,0x2337c87fe0c31010639ee908284049426d0921b42631d9c8096200207fc9320000,0x1a7849141321227164e27138998984c2f137f553df3c7d6f27184e3098c263098c263098c2614c06c1177d52e5dffc6020cb82b668b01420cbe1309b668b30984c20cbe1309b668b30984c20d971d9c809d2d0207fc9bc0000,0xd31d9ca09d200207fc9020002,0xdb31cce009d200207fc9030004,0x4ef1cce003fa00207fc9020006,0xb31cce603fa00207fb6020008,0xb1bee603fa00207fb6010012,0x1b1bee603f910207fb6010014]) (.b 80 (.p [0xb31beee03f910207fa5020016,0xb1aeee03f910207fa5010018,0x1b1aeee03f8a0207fa501001a,0xb31aef803f8a0207f9602001c,0xb19cf803f8a0207f9601001e,0x1b19cf803f840207f96010020,0x3719cf803f840207f8c010022,0x2c319cfe03f840203f8a030024,0xb18ffe03f840203f8a010026,0x36f18ffe03f800203f8a02002a,0x3718ffe03f800203f8401002c,0xb187fe03f800203f8401002e,0x13490f091bf28c8cdf73fe2cd35fe696cc05a5151eb9a29e07ffa7964ffe078348c1cbcb193cb3f57835c99b84707fe03f80fe0bf84590000,0x238bf826914af3bfc1a810d0311d53f822dc9a62c7ed5ebff22fe4da71562b7dbf048fc44d75b118902a5318ffe00080fe08484570000,0x1b318fec002820a08484030000,0x18b46133c4962ee5fae5e0cd8816ad628016e2f42d32d3c42822ee5e22e5fabad9b9d878d0bfd61883a7e610290ecc84218b04d8fec03f860a084846a0000]) (.p [0x12f6a5e3f24e397e1796081d1c90b6f2979e2d86c1d52f3c3f62d5ffeefc91a0bfa3706b985b9f87779e1e789fc3c00352c494d1013511828862bf1f884f116ae9799b9d7f1ea9ac5b9f8297f16991edea68a4421461cdb469e238a8e1a4428b319cec03f860a08484cb0000,0xb18fec03f860a08484010002,0xd318ffe03f820a08484020004,0x7e214461358c1ad993eef12a9788d42a6b5a2da06974306b458ed0252a862f4600bae56eaf0635295e3dc2238bf896295e699a92bc40a476834b59fabc98b144d8ffe03f82fe184847e0000,0x11227e949c3510d68fdabd7fe567bd292996249241affbf4a0bf997350d2943df8b9060a0a825e135d25319cda00282fe18284580000,0x26cd319cda002821818486060000,0x580daa1260e1267f0e4c24244228b6d2578e54cd992bc73beae4cd1037f495e3948024cffb263fa94af182db495e39533664af1c8c95c1243acce25270c504717f12c5095e25a54c05176a72928b34469575a9a34b1a0649248359cf1fdb46e4d31563344b19cda00282fe34486d50000,0x2719cda00282fe18486010002,0xb319cfe00282fe18484020004,0x62d4d3f245a83c0526abeef10c145851083bbc14d262d8b079e7f8bfc66504143c42921c46288d1ddf87779e1e79fe03d9a4ad16e7e0a5fc4219bbbcd16319cfe03f861818284880000,0xfc42c60b9fe67451c10ada860ad68a66b7cad7ac83262bf11afe13238744754482a69248ed35bd6bdc7b46e4fd5e4cd0569cfe03f86fe34284620000,0x1ba1c2bf54d382a124cc849332124af4393260e4c987f09931b209b341d11229c05277a555257a4a6cb11a5090916527dfce4998f11c5fc4fc365543694d74085252316cdfdbcca0ed69d9331aef600606fe34284a90000,0x15573a70409c11811b710230731c102160e6d52f3c193ca5e33fc5c6c360ed534d00d46ea30a4e266c9364cc204448884b5ede23afbbcd26210a8f0f7e230327711a8e862a916e7e1dde18186cffd5d6c59d20532c938b1631aef603f8d2e34284cf0000,0xdc176f60d67cf8cacf9f102edc550f24f164a3fad6af3a7f266daeb9192febae45163e7d291d5c8a2f2fc2ae236464c05eaef603f8dfe602845e0000,0x2ee6c8abb829a0d710b5235b4a52531bef000c8efe60204220000,0x81408d1e69e6ae181edc5b31bef003f9a4e602041b0000])))) (.b 144 (.b 112 (.p [0x3f2c8b8532725bef003f9afea02040d0000,0x49ff928fe94daab93268a1209c245aee1cd3848270907bec5ee0a2ae1b2970d95531cce80151afea02044c0000,0x372fc397e5ab7472fcb53f150e5f839b8d03a8144f50add29a28f7d8bdd298531c5ce61714db88dc762f74a638b9c95cf12e78331cce803fab6aa0204690000,0x3ff1cc020252bbed8204010000,0x16452e55a80a52bbed8204060000,0x55b31dd76099ab8cd8204050000,0x2a0530de760a5348ad8204070000,0x2877514c29a289c5c2e170b85c0a268146584a1b056055c58a051b64cd05028c1a8c6c5028db2668281460d46580e1b156ddaa4d4d2634d2693029850386c51458d82a62ad9a4c150298f8ab66930591418ab64cd31e2760a5348ad8204da0000,0x194f1dd760a5348cd8204030002,0xd31dd9c0a52b8cd8204020004,0xcb8dae56762b9914d263498d209cd209cd209cd209c99a4c6931a4c6f1dd9c0a52bbf1c204450000,0x1331dda80a52bbed8204020002,0xdb31ccd80a52bbed8204030008,0x12731cce803fabbed820403000a,0xcf1cce803fabfea020402000c,0xd31ccf003f9afea020402000e]) (.b 128 (.p [0xb1bef003f9afea0204010010,0x271bef003f9afe60204010012,0x36f1bef003f8dfe60204020014,0x1c36284f1bef003f8dfe602850b0000,0xb31bef603f8dfe60284020002,0xb1aef603f8dfe60284010018,0x271aef603f8dfe3428401001a,0xd31aefe03f86fe3428402001c,0xb19cfe03f86fe3428401001e,0x2719cfe03f86fe18284010020,0x100070d8b92e4cc90b2e4c05cc92ad0205681027044eeeb9a01a8901732881023dcd83afeb601c1d52f0c69e2dd38b26293103a2b7ffbbcd198a2ca7b3fc1e7f51fb79a0d4528157357266931da157dde0c514cf19cfe03f86fe18486bd0000,0x3719cfe03f86fe18484010002,0x1b19cfe03f82fe18484010024,0xb18ffe03f82fe1848401002a,0x2718ffe03f82fe0848401002c,0x1b18ffe03f80fe08484010032]) (.p [0x101277abd927985ecdeafe63ba98c095d833d0cd717ad2927ef75668985e4b37a3dfcc648b6ba9a37caf62c388f540991bc9592b6f560b35c5ebd8b318ffc000800a0bf8a6d0000,0x5989fb7980f3cad166fdda80a37aae57a3c02dec64c3df989a579853c3c2238bf896619ac62c7784b07ae7fc98b04d8ffc00080fe1bf8a5b0000,0x2da23e802a124a8492a1260934cd992bd6ceeb042914809b160e88914e2004046b44753eff61d6212bf2d2bfdfa0176a729283deaf6fca92bcc21f6fca45f6f2608c448204bfa12247f8de4ea945a5798464e6ba301a2dae1b1d93319cf400080fe1880ac90000,0x3254a96009200920092009804c02699b3237e263260842295059734d9304412413726034468376a088f54cde0ad4a9cad002b304c7aa331ed16319cf400080181bf918d0000,0x3713fd08419e7b1aff262c4b025503359ee41916bb58c11122e68019ce554584f289fb0266b1823d9f3d9f0a7918b0569cf200000fe37f91630000,0x1122e9e05beb7330fa12e900b02735d2531aeea00000fe35092270000,0x11ea334210601f23b0458839ad04d545e4a335b31aeea000002e37fa22c0000,0x377a1a823c8c05eaeea00000fe63fa20d0000,0x18645cdde2dbbc53e825551e52531bee200000fe618a21b0000,0x8cdfb07fec19408b0131fffa22c66a441a8092a024c66941cd00291bd04c6009209b9522dde48331833e966331bee2000004e63fb2600000,0x73f1be0200000fea3032020000,0xd202941d408000fea3032070000,0x35b31d3ce080006ea2132050000,0xc8322902d53ce08000fee21320b0000,0x279483a7b260ecfff652120ebfa5167fe5dff62f8649848bd342905458fe8524cf664af412331dbcc08000fee1cb24f0000,0x427d11f4422db90918381c0c981930326064c0c92a84efdda8687bd414ef1a77ff8c1901901924064c0c98192509b070941a80d5490692821301a8120d25164c06a04cf1dbcc08000fee213a9b0000]))) (.b 160 (.p [0xb31dbce08000fee2132020002,0xb1d3ce08000fee2132010004,0x1331d3d008000fea2132020006,0x22088b202d53d00800078a30430c0000,0x123e64c6bace664ffc629df278c1c0e044c08981130226044cb0b191b262c10196544cd8b26080cb835b262c06901b2835b262c06901b2888226d9331db880800078a27c38e0000,0x4d8841c8ed458320320381c0e0703819880994f1db880800078a3050310000,0xb31dbd00800078a3043020002,0x4cf1d3d008000fea3043020004,0xb31d3d408000fea3032020006,0xdb31bee208000fea303203000e,0xd71bee200000fea3fb2020010,0x271bee200000fe63fb2010012,0xb31beea00000fe63fa2020014,0xb1aeea00000fe63fa2010016,0x271aeea00000fe37fa2010018,0x431aef200000fe37f9103001a]) (.b 176 (.p [0x6319cf400000fe37f9102001c,0x21719cf400081fe37f91040000,0x1b19cf400080fe37f91010002,0x2719cf400080fe1bf91010020,0xb319cfc00080fe1bf8a020022,0xb18ffc00080fe1bf8a010024,0x13318ffe00080fe0bf8a020026,0x8de2177fc193eef125eef357f9a0effe6984d8ffe03f820a0bf8a200000,0x4d93319ce4002820a0880a060000,0x1568578924bdbcc2c624b1772f182e5fabac092d7f16990c15fe6930569ce403f860a0880a370000,0x8241331aedc00606060880a090000,0x481241b04518811a040ec1bf8d081c10d04029e8148c7245abffdde2481fe4f9fd0734c1a230e081d11fff77ecd199c5a678fe0c1d4218af8cc06c114421500d033d503cc1a666d21242e651085ffeef0e6d8fe089e23f72201e80316371aedc03f8d060880ad80000,0xd31aede03f86060880a020002,0x100b9305cc971aede03f860a1080a0f0000,0x1331aee403f860a0880a020002,0xb19ce403f860a0880a010006]) (.p [0xd319cfa03f820a0880a020008,0x251706817069024208cdf20cdf20cdfb6ef404dffb3237ecc67f8908b4cd991bf663066104904dced207073319bc966f10a10f27c8949f318846f4b319222034593156ac1ff12130bd9bd5fcd45318b46f9ff161fb19316319cfa002820a0bf91af0000,0x2054a9769a024221505555c58b15029426c59a2d7b7a05810319cfa00e860a0bf913f0000,0x36f19cfa03f820a0bf91020002,0xb319cfe03f820a0bf8a020004,0xb18ffe03f820a0bf8a01000e,0x90186b2628021480517245555c98b26b9e00b09718ffe03f82461bf8a340000,0xcf18ffe03f82fe0bf8a020002,0x1b18ffe03f80fe0bf8a010012,0x3718ffe03f80fe0bf8401003a,0xb187fe03f80fe0bf8401006e,0x27187fe03f80fe03f84010070,0x37187fe03f80fe03f810100a2])))))
private def data : Store := ⟨vals,rows,model,codes,7⟩
def ok := test rule 5 7 data
theorem finish (checked : OMA.Tape245212.Before ok 189) : Deny 5 7 ![⟨2,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨8,999999999999999999⟩] := by
  have same : data.vertex 188=![⟨2,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨8,999999999999999999⟩] := by decide +kernel
  rw [← same]
  exact close valid _ _ data 188 checked
end OMA.Tape5_7_245212
namespace OMA.Tape5_11_245212
open OMA.Box245212 OMA.RankTape245212 OMA.TapeShared245212
private def vals := OMA.PageTree245212.get (.b 128 (.b 64 (.b 32 (.b 16 (.p [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16]) (.p [17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32])) (.b 48 (.p [33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48]) (.p [49,50,51,52,53,54,55,56,57,59,60,62,63,64,65,66]))) (.b 96 (.b 80 (.p [68,69,70,71,72,73,79,80,83,84,85,86,87,89,90,91]) (.p [92,93,94,97,100,101,102,103,104,105,106,107,108,109,110,111])) (.b 112 (.p [114,115,118,119,126,127,131,134,135,136,153,155,159,160,164,166]) (.p [167,169,172,173,179,180,181,182,199,203,205,206,207,214,215,222])))) (.b 192 (.b 160 (.b 144 (.p [240,248,254,255,290,320,322,323,329,374,375,398,414,415,436,455]) (.p [526,604,701,703,830,831,1208,1209,1662,1663,0xde0b6b3a763ffff,0x12fbd81c64fa4d50de,0x1578f53917add90308,0x1578f53917add9030a,0x1578f53917add9030e,0x18b652cfa1171f7af5])) (.b 176 (.p [0x18b652cfa1171f7af7,0x1bde27cee26ba7b932,0x1bde27cee26ba7b937,0x1bde27cee26ba7b944,0x1f856d06e271f6afe9,0x1f856d06e271f6afeb,0x1f856d06e271f6afed,0x1f856d06e271f6afee,0x1f856d06e271f6aff0,0x1f856d06e271f6b022,0x1f856d06e271f6b0d0,0x21ae45c984343d04ac,0x2446eb1001ea74d53a,0x2446eb1001ea74d53d,0x2446eb1001ea74d53f,0x2446eb1001ea74d540]) (.p [0x252798b11ff870b1bc,0x252798b11ff870b1d1,0x252798b11ff870b1e5,0x296d7907bcd54ca999,0x296d7907bcd54ca99a,0x296d7907bcd54ca9a2,0x296d7907bcd54ca9a4,0x296d7907bcd54ca9a7,0x296d7907bcd54ca9b3,0x296d7907bcd54ca9be,0x296d7907bcd54ca9bf,0x2ab912b6d19858ee6a,0x2edbd30b17ee23fb26,0x2edbd30b17ee23fb27,0x2edbd30b17ee23fb28,0x2edbd30b17ee23fb29]))) (.b 224 (.b 208 (.p [0x2edbd30b17ee23fb2a,0x2edbd30b17ee23fb2b,0x2edbd30b17ee23fb2d,0x2edbd30b17ee23fb2f,0x2edbd30b17ee23fb30,0x2edbd30b17ee23fb34,0x2edbd30b17ee23fb36,0x2edbd30b17ee23fb51,0x2edbd30b17ee23fb62,0x34fe623ffa1fcfb2d4,0x34fe623ffa1fcfb2d5,0x35edb87fbe1f8b5185,0x35edb87fbe1f8b5187,0x35edb87fbe1f8b5188,0x35edb87fbe1f8b5189,0x35edb87fbe1f8b518d]) (.p [0x35edb87fbe1f8b518f,0x35edb87fbe1f8b5190,0x35edb87fbe1f8b5191,0x35edb87fbe1f8b5194,0x35edb87fbe1f8b51ae,0x35edb87fbe1f8b51d2,0x3738658a7790343655,0x3a969752817537b8d9,0x3c69512421cf99fa26,0x3cfd3ddfa301945010,0x3e25ea9a1dc8978473,0x3ee788f996852ff3da,0x3ee788f996852ff3de,0x3ee788f996852ff3e1,0x3ee788f996852ff3e3,0x3ee788f996852ff3e4])) (.b 240 (.p [0x3f82cda5402b7f0c74,0x4454c8442f9bfcfe11,0x454ba0d69f40f462b1,0x47d37ed16c665b1879,0x48a05eb73bb0f1dc16,0x4a3fe056d5882f1e95,0x4a3fe056d5882f1e97,0x4a3fe056d5882f1e98,0x4e614011fa601aaaeb,0x4e614011fa601aaaf2,0x4e614011fa601aaaf3,0x4ea40b4f5f36aacc57,0x4ea40b4f5f36aacc5f,0x4ea40b4f5f36aacc61,0x53f87dfff6b08d2044,0x54e574efde0f611c97]) (.p [0x57c99afff64436733b,0x582994e65ef372327f,0x5a34a38fc00a00269e,0x5a34a38fc00a0026a6,0x5a34a38fc00a0026a9,0x5bbacead425b5b4ec1,0x5c9d39bfdaf9813683,0x5d25a8e52220966aa8,0x5e0e4ce25fa68666b3,0x5eb3849b131bf8f276,0x5fc7cc224fdcd69669,0x68155a43676e002c70])))))

private def rows := OMA.PageTree245212.get (.b 288 (.b 144 (.b 64 (.b 32 (.b 16 (.p [0x3f15b50e19e3a8006a2001160bfb00fb00070305021a0000,0x701ffc9d661ffc04c62d180160cfb010301fb0805031a0000,0x1344c76eeb48e3866b19a7da26278bb97eb978b706a6a4a168a4efaae1ee95e33dc550a546739e05707b108df388e166fe4ce56534e8e6a38333cd3890a2a1610f0cfb01fb04fb0805037e0000,0xe5eb1214428d6f9d4ba8e0cdf8a92d834259e911c1610fb02fb04190c05042b0000,0xe814ae0cf42e7b7e322e815efdf9f693c2a68057ad6336a35079399e68057ae85a4c9f2829e4cdb935afd31bba8f5eb3df5ebd2383adf8425c9931cb38783e1120f4ce567a4ca61610fb02fb04fb1a05048d0000,0xb851610fb01fb04fb080503040002,0x2160cfb01fb04fb080503010004,0xc921160bfb00fb00fb080502050006,0x5539a0bfb00fb00fb000502030008,0xdd1b837e311f27845ea1175fd47168e6ef89205a490e9bfe6494830447a979c0afd246f919d4c9a1b51c16e47045a186c26a869211205a48951259a0bfb00fb000100fb06820000,0x1f8fc1ea1c3954003a92f525b9783964c1d4039542c657ad4aea39924240fe45dcbf5cbc3e85b4a5250a60b15a296cd2dcbc1ac3a8478d0866c4ffb902a1ea59aea594b40684aa64ba9ff31c160cfb00fb0005020d06a10000,0x23ad492fe0d7fd66199a779e5300b1fb57affc9d6a397f329b9051567b7820bcf1ab9ac61f3c0fff6ffe4ab5a0b92c61f4c4b58c160cfb000100fb060d06670000,0x26907ee2bd31643d2abf5cf49931cba096fefe7b75c07b12fb8cca1cfc5b108cc98aa30cabf901cfc6551fb4af03ec0efe33d3d0faa9e8caca3eb160c0100fb02fb060d06710000,0x4d2d344c775a2c910f0cfb02fb02fb060d06110000,0x1b4bb2a7342da84b4004d0b993431621403dac210a842d0e311afc10b1e2145991f6b1c1610f102fb020d060806560000,0xa40cd2a19a950f502928eead37a89ea5d470f285b52099285a4c5b42ac72d6839a3ed61610f102fb020d060d09510000]) (.p [0x2c1610fb02fb020d060d06020002,0x4717f12e5013c0c90fa86fe258c5889167a62d6fe8dc9ede4c1610fb020502fb0e0806350000,0x7a0d3beaba7344e68fe98ab187cd1c3df4b75a08e663ba8e14e7bf896339594c94fb496a5e898a39a972b419adceb4c8586211f4799750a2a14593a95e226476863c193bea2359e8d6f5cf44613d147e7a864c428d6fdad9431fa1610fb02fb06fb0e0806b60000,0x61610fb02fb02fb0e0806010002,0x1342ac72d6831426801fe05e68526fe69358c1acb34c2694fdbc7f8db1610fb02fb02fb0e0d093d0000,0xd1610fb02fb02fb0e0d06010002,0x91610fb02fb02fb060d06010006,0x2160cfb02fb02fb060d0601000a,0x3160cfb00fb02fb060d0601000c,0x6160cfb00fb00fb060d0601000e,0x9160cfb00fb00fb020d06010010,0x47aa043c8d74690b37a491bd1c5b3783b192b7b247b98c160cfb0001000502fb0e2b0000,0x5fd5f6c1beb88e41822bd888f472e2353e3c91b83bbf5ef7ec447a23b8c5f23eb160c0100fb020502fb0e390000,0xd2346b4775a2c5a10f0cfb02fb020502fb0e120000,0x1dd029242b1352f4966578e5f2ba8e4a5b835a4a168b14d2a3ed2cd752e56d470670550b0029a8842ac73574872210ab4942c72769ff7239a8e0aa182a5e90f6b0c41d3f044806b45ae85a4c1610fb02fb0205021d0ea70000,0xb34dff16d004ad8ccfc696ba397ffef8af9f341106fc414119bf0cf95e865b87758591393e648266546f12ddc46469237896182230f3ac4a4f80578a5425e43179fa47c8c02410f1ca043caf7b18b91610fb02fb020502fb1ea20000])) (.b 48 (.p [0xd1610fb02fb020502fb0e010002,0x2160cfb02fb020502fb0e010004,0x3160cfb00fb020502fb0e010006,0x6160cfb00fb000502fb0e010008,0xb309fc20bc19ac76ef1bbc19ac62c0781e0f1e5cac0781e043c7299bc15b5024fa100af9910106b95ef633453ddd309e0784483cba04f28238bf8963072cfb1ec98ba62c6606ed44862e6eb93ad6f89f5dffcf8cef8cd2f23160cfb000100fb06fb0eb10000,0xd0abeef06000d00480ad794d406802774c598047d48af933f56446f825fe3160cfb00fb02fb06fb0e460000,0x6160cfb00fb00fb06fb0e010002,0x9160cfb00fb00fb02fb0e010004,0x61170bfb00fb00fb02fb0602000e,0x36b72001d44f51f9ab9787ccca462045f923b0e31022fc91c19084b0025e01222009a18fb00fb0109040d064d0000,0x224d00911d6787a56112282839ad673942002e1cfb000301fb0a0d062e0000,0x3ce08a04f05a3102cb16808d211202e1cfb01fb051f0f0806240000,0x47138a25abf8850632735d1802e1cfb010b05fb2008061d0000,0x2e2267470fa057bf7e79a08c9ad7c9bacd1a23aaae7262ac669d13187f8ba8f34e09e6ca168a4c98e5904d9b5742161221cfb01fb0cfb200806620000,0x6cc240e4e81ac6f3a41aecdc7d5d071570c240a5736ad517c5d24cddc26716e0b4526b5f209b36ae8425e11d77594c063cf141d1e0867710a48880150212e23fb01fb0cfb200806900000,0x22e1cfb01fb0cfb200806010002]) (.p [0x62e1cfb01fb05fb200806010004,0x15132e1cfb00fb04fb0a0806040006,0xeef2e1c0100fb04150a0d09010000,0x1e02e1ce6020904150a0d09040000,0x2b452067a862f50866eef10b9ea18718898c40b650c1a1688d9adf82d1772fd72f0fa1cb3216472661221ce602fb0a150a0d09580000,0x2898e5ad39287f169b2508535162eef10242b131cb586225fc5a4c5ae85842154c053572f592ab16d24a44231fb34ded204b5d08527362d54fc10b1e210cf17aba10a2c12e23e602fb0a150a0d099d0000,0x22e1ce602fb0a150a0d09010002,0x62e1ce602fb04150a0d09010004,0xc2e1cfb00fb04150a0d09020006,0x13d5935dfee9ee2a2115762119ee3a61cb12a57ed553f79931cb2392df8903ab2e1c0100fb04fb160d093f0000,0x2470e921f753f8963164923841e11d53f89630695e6111c5fc4b59ce5214584d2fdbc1380bad7490eb49fc4b18b92c66582e1cfb020904fb160d09670000,0x9a42f342f48f50c58221221cfb02fb0afb160d09160000,0xa5e2351d0cc210a8f32c59439d0e5985b4740fe2d867260a97889ee2351d0cd3e3ad19b690898b556e94d16fa05a3f5d0b42e24fb02fb0a2d160a096f0000,0x55947f112babde49991d71135d44285479a2c55c6e7dabd19a4c9eb52039d88467b8c8a2edabd6d5e79167a6488e948b3cfd6fcea4662e24fb02fb0afb2e0a096f0000,0x92e24fb02fb0afb160a09010002,0x4af120462cb19a7c62144316f779bad266e50a8d2b1695ad633492e24fb02fb0afb160d0b380000]))) (.b 96 (.b 80 (.p [0x612e23fb02fb0afb160d09020002,0x22e1cfb02fb0afb160d09010006,0x62e1cfb02fb04fb160d09010008,0x32e1cfb00fb04fb160d0901000a,0x92e1cfb00fb04fb0a0d0901000c,0xd2e1cfb00fb04fb0a0d06010014,0x512e18fb00fb01fb0a0d0602001c,0x12b214110855b43047916acadb469e21488e0c6214c788506002f574200852ffb00fb04170b0d084b0000,0x7f4834fb01fb0cfb200808010000,0x4285479ab997fc1dc428a6911c4834fb01fb0c40210a091f0000,0x4755dc44c82a1a4dc4834fb01190cfb410a09150000,0x54a3a4ddc47150a2cf7fa4dc7128c958de748354a69f72fdd6fabfc19dc429221c55c303968516b88e6e1338b7060cf6ba455d58c99a2a51d269d1c54292740d6379d20d766df56eb3b8871570c489726b5fa60524834fb01fb1afb410a09b70000,0x64834fb01fb0cfb410a09010002,0x334834fb01fb0cfb200a09020004,0x2d134834fb00fb05fb180a08040006,0x8e2fe25ca097f01227a60889054393d3962ad9e8dc8300067395944834fb000b05fb180d0b400000]) (.p [0x17100b48340100fb0c31180d0b070000,0x1b400b4e584834df02190c31180d0b0d0000,0x3d6a5194bc44c42421313fcdceb419ad3c46a3a43f144cd3a19847bd7a5a81fc58e65be13d34df02fb1a31180d0b4d0000,0xe92262367a8f32c18b054bc44cf11a8e93f144cdc878eb460b447c0d0494a8627f82fa760866c5aab9dc42922212c1483edf02fb1a31180d0b6b0000,0x24834df02fb1a31180d0b010002,0x64834df02fb0c31180d0b010004,0xc4834fb00fb0c31180d0b020006,0x132632b48340100fb0cfb320d0b070000,0x17648386487916784de7709906a212cd4af1029e1243ec9bb3c97be584834fb02190cfb320d0b400000,0x1b4d6007e294b6786e664dfa293bee0c5ee0a2d52d3932126d53a14986e4c28d48c11ac6ec423334428d3a149a922ca88144f51e0864adf6f4a6ee0c98b24f0999fd9036e28924834fb02fb1afb320d0b9e0000,0x64834fb02fb0cfb320d0b010002,0x34834fb00fb0cfb320d0b010004,0x94834fb00fb0cfb180d0b010006,0x64834fb00fb05fb180d0b01000e,0xcf1492ffb00fb04fb180d08030010,0x210ab710a6c3382788d40bfad0355a8f05a2e45122216522d542853488e0d7d2214c282f574200854af800fb0a351a0d0a600000])) (.b 112 (.p [0x2f9c6451748bb349838e2dc41cddd70c28cd2214664df700fb0bfb360b0a300000,0x448a7fff4828bdc4048ed29594664df700170bfb360d0c1f0000,0x135af1cb664d0100fb18fb360d0c060000,0x2ca88914488d6152c0cd362dd56e214104b30aa0aeefc226ba8851bbe8b7f1be53b822e01d6536af5135af3e45634664df702fb185e360d0c690000,0x2a1133fa2bd78cc9a6a57a1458dc9838e25187582a400b1f557f095ca6fb089d48c5e93411749a258fe0250fa5235f49a4a12bc66664df702fb18fb5f0d0c730000,0x9664df702fb18fb360d0c010002,0x3664df700fb18fb360d0c010004,0x6664df700fb0bfb360d0c010006,0x19c1674af800fb0afb360d0a040008,0x170c48a484d6be4192b8a2c2bd7cc26f92608adf5445133b88524438aa386282a4a6ea641378e2518b16be622184b861028baa8ba41534522dd56fbbeae18159228690e2ae181c3008568f800fb0afb360d0aa40000,0x2854af800fb0afb360d0a010002,0xd00854afb00fb04fb180d0805000c,0x2852ffb00fb04fb180d0801000e,0x14058a2ffb00fb01fb0a0d06050026,0x33f9a18fb00fb01fb0a0d06020028,0x6939a18fb00fb00fb020d06030046]) (.b 128 (.p [0x11facde0ec691bd2401f1a9807418fb0003010502fb0e190000,0x2366b7e0862149291772fd72f27569e2393b250b1e24b4e088563ad2cc5258b73f043321874a975a2366b7e084293c4f1243511c38c4834aa142a1cfb00fb0405021f0f800000,0x1310228997041d7c938b357492906fc6287dc26e744c27eafd4e680eec48244470680dd61a37a4bbfbec57c7b19a6520df88eec1ddc9e09fe8d5d092588fd66f076346d180cba590a7c3f9bc1a484428b5b2a1cfb00fb040302fb20ac0000,0x18232b8f6bab2a1c0100fb040504fb200c0000,0x6908df62c08207d0825ffc59a034092857894dfff05447bfad0057ca47c5c818b054bd24863d8cd0fb0762490343328b551f170fe0b4c861d680578903b52a158d11e3941f2a2688f54cde0f75319a483a7c41a4846f25662a1cfb02fb040504fb20bb0000,0x32a1cfb00fb040504fb20010002,0x92a1cfb00fb040502fb20010004,0xa12b18fb00fb040502fb0e030006,0x1642ad89064002788320727c168b1112224a548842ad2110a6c7b4200c8124214742cfa00fb040503371b570000,0x11facde0ec775a631ff125a8151bd180742cfa0009040503fb38200000,0xa120432ef900fb0a0303fb38080000,0x37e230446b432e0100fb0a0504fb380a0000,0xf81f1e8a4a88113497d0d34692496c7b3438bd7e224a621894ec537c5b0585aa8f8b87f058e2c953b257b34432ef902fb0a05046038640000,0x1ed0845252be81f4265ebe0c59aba49627845114110209b108ec483239bccd3e069cce50837e3146b0899f34126a2c9ff12127304c737943cb4e51bc66432ef902fb0a0504fb61870000,0xd432ef902fb0a0504fb38010002,0x3432ef900fb0a0504fb38010004]) (.p [0x4c1442cfa00fb0a0503fb38030006,0x9faad890640221fcd20462ad8c41842157bb120910e6def5742007445ef00fb0a05046239430000,0x3fc484d0d319b917041d7c5b074f62403418e69f026bf64f522336022822bb7ac104141cdb07574248e4d7ec1d4200a30ea73d8908bd2265745ef00fb0b0504fb637a0000,0x884708a0a0e0d06ec0132c1938b377496278451154820e4fd44776241221c11388120017458ef00fb0b0504fb635a0000,0x3b7445ef00fb0a0504fb63020002,0xc07445fa00fb0a0503fb38040004,0x2742cfa00fb0a0503fb38010006,0x6742cfa00fb040503fb3801000e,0xc0742cfb00fb040502fb0e040010,0x27418fb00fb040502fb0e010012,0x9b9a18fb00fb000502fb0e03001a,0xc7c934b57ce5227e804b19a95e6148e11ac2241e99cad871a012d67bd942e1cee000100fb061d0e410000,0x8fd66f07630904646258124137380ebd43395a0077731dedc2e1cee0001000d06fb1e360000,0x5cdd727d6ae4f98054f2e1c01000100fb0efb1e130000,0x174ef184e1a8133f7c73fccd05bbd45bbd63fc67f9d7f54a688f53e889b9402c4fa09186b779b265bdbbd63dea0ac1988ae758c8ac20453eb77e0372680921d6b37793b5b91ad6efc00d4ca0c02e1cee020000fb0efb1e940000,0x1342dad104904c84333f30763262a37e014ca5798524f2916a277df1ef193267f096f4cd2e1cee020101fb0efb1e480000]))))) (.b 208 (.b 176 (.b 160 (.p [0x62e1cee020100fb0efb1e010002,0x32e1cee000100fb0efb1e010004,0x92e1cee000100fb06fb1e010006,0x2c12f18f0000100fb06fb0e030008,0x99808630e4000000fb0cfb19060000,0x11d70c831a00402735d1948630e4000101fb0c351a1b0000,0x27827fd0844458354a819a9e694924191679bbc99b95dbbc53c8c95833d5ceb1951337c875948839a00566098f5466b405414a30e4000101fb0dfb36670000,0xde66ddf23503676ef918cdd8961875316ef592a43cd74941827d04a81b38e7f9821bb016c218c7fd084d6ef95dbbe7798c98b18645b77820139ae929a23d44441806e876bac0b13e82540864be4000101fb0dfb369a0000,0x1338630e4000101fb0cfb36020002,0x158630e4000101fb0cfb19020004,0x2808f30f0000100fb06fb0e050006,0x36c9a18fb000100fb06fb0e030008,0x3fc2e1ce70005020d061d0e020000,0xeef2e1c0100fb060d061d0e010000,0x665799fdf87d0c1108544df22d2111cd8842a4294942c714c98eeb0c40d27e0858e4c9425582e1ce502fb060806130e550000,0x6002492d08980b52a2044f656ac4280722119f9a0885651772fd72f062d743068430eb44380563d22e1ce502fb060d09130e5e0000]) (.p [0x4c2e1ce702fb060d06130e020002,0x3005a501d2b31c0680109f187f695fd2958e2c5b4816e2f42d3777892c46cf568b6902dc5e8f1ac4ac8046206a5137ae85a4c942d10e0158f5892e1ce702fb060d061d14830000,0xd2e1ce702fb060d061d0e010002,0x32e1ce700fb060d061d0e010006,0x342e1cfb00fb020d061d0e020008,0x600bae5023005d722c602a349f4cd160a84d0029365437aea5590f3c0dfcc2ca95eb774cdd1a00585ee4245ee11120f258cd352bd2523b4f583e5a299eb72b12c662e1cfb00fb02fb0e1d0e930000,0x92e1cfb00fb02fb061d0e010002,0x1a17b4b74c1800d0021011e734ef1047c7395bb88c8c511802d2af699a0803400a4d9cfcd3d26b8c50453221074f882223d533783b19a4823f188304b13bac332476316332e1cfb00fb02fb06fb1e980000,0x613118fb00fb02fb06fb0e020002,0x62004d34db0009040d061d0e070000,0x10b4846851e010c0f0eb4a2dfc58943f8b4cb63106250fe2513c4806a20ddde2005944d34db00fb0a0d06130e530000,0x5b4b240fe0c4013005b4740fe2c2d21120d92950954cb63000eef1002dc4d34db00fb0a08061d144c0000,0xeef10242b29e84b68e81fc5a6cf4244a540fe2c216908d0a3c1960c98b58a2629494a8432665bd2b1d3960434d34db00fb0a0d091d14660000,0x94d34db00fb0a0d061d14010002,0xd4d34db00fb0a0d061d0e010004,0x3414f32e000fb040d061d0e030006])) (.b 192 (.p [0x108db48003bbc4012002f5742148e50d600fb0a0d081612250000,0x5aa9f9b7bbc0489003c262175beefc6163a21c97f4826830b1112220d3897eef0005648a08110a15a891d7f1610895a2a147b0eef581875842d21d83fca8730b1d10527bbc0095ac19d39bbbc40127128e50d600fb0a0d081d17b90000,0x3008e50e000fb040d061d0e050002,0xc1c9a32fb00fb020d061d0e040004,0x1fc05212396a45ee989624b5a88ea9fc3bfd273d0258c93a485bac62c992bcd2867c4048c588e2fe27e012a0487dfae3faf20f4ac238bf83358c97f30122803df8891da372317abd7d8980984c15632bb000502fb0e1d0ea50000,0x24ffca7967fad3f8b024cff8160499ff064af412afe634c0448b2095f893cf39b06334c92a656c501a70448a7c7d5fb77e012aa1d5f858223aa7f247e6169ae901209691884af1127df1994db886214dc828337f13f0091de950495e84283009a57bb000502fb0e1d0ed30000,0x189a32fb000502fb0e1d0e020002,0x618850600b49ce1296fc038c5534dc000d061d0e130e1d0000,0xeef55340100fb0e1d0e130e010000,0x26aa5e205295683bb515eb65a59a8842cad38842cac21192ac98a696215944216568b1fae85a2c914134dc02fb0e1d0e130e5b0000,0x4226a561085421990c37bf6f308113528431fed625600116aada19840889114e37e086191f63000f588024e2c5543d702fb0e130e130e6f0000,0x1b42429456552f113da4137fdd7958421656583362dcfc10ed090a2c4310242b1310ac4dfc6097a145bfd6108db48382193251f6b4d5543d702fb0e1d14130e790000,0x4c15542dc02fb0e1d0e130e030002,0x25534dc02fb0e1d0e130e010004,0x35534dc00fb0e1d0e130e010006,0x345534dd00fb061d0e130e020008]) (.p [0x62df2f14003bdde20529568b2621400a66898a3233f27c96564c5a46b72c7e564adec665534dd00fb061d0e1d144e0000,0x2c5534fb00fb061d0e1d0e020002,0x2424729b269a23ad4f4c9247083d32bbd69fc4fc4b48cd1695e6959325fc052123b764d424af1eccfcac94b58c5534fb000d06fb1e130e5e0000,0x372bcf1ab42690f1a813813400b02e6065492d4bc4090acbda144e6743043164c368f5c4b74cc807bd27d2b261347e4fa563fc68b05443005d7200a46fefc4391e67a32b267ccf44468f835534fb00fb0efb1e130ea60000,0x65534fb00fb06fb1e130e010002,0x12bc40a4662e5613400b0b2c66935534fb00fb06fb1e1d14200000,0xd5534fb00fb06fb1e1d0e010002,0x915632fb00fb06fb0e1d0e020006,0x618853722009357cf00150a1d0e130e0f0000,0x2dcfc3bbc001c30040ea048596a2569842d214a69b2460246164b7e847f80d01962d07457cb00fb16130e130e590000,0xf01214213103a2b65687103a2395858ed20d44887164c3c04854c497627f043fe958d16e7e1dde002802d55b4330b553f043362c444888592dfa1201801962dcd7457cb00fb161d14130e9d0000,0x917557cb00fb161d0e130e020002,0x42177be3374e1a4143bbc001d9fe480081d11efdbc5e5f8c2d55b49287778812061dfcfbe3108e312018c428294c2c45a420244882c856b1409376cb00fb161d0e130e840000,0x189357cf00fb161d0e130e020002,0x21c9a57d000fb061d0e130e040006,0x4c37be6660598682ec0c008029f6fddf19b8b26f8f628c389f807939b7c6651462141a098b6c9a57d0000d061d0e1d14560000]))) (.b 240 (.b 224 (.p [0xf2f1400856cd4408858490ada862c98b68014e541de3213ede4c535bb2fb4563081ee25344d4ac210b23c0a31000c98057881215944226a5692b6bc3fe1b429bdbf1a2c7857cc00fb0e130e1d149d0000,0x1b680160017e7f77e05edc7be4f8c0485e5e2801624427ddeb45787788a0ef190d92c629adc9631634d7857cc00fb0e1d141d14530000,0x4c17b57d000fb0e1d0e1d14030002,0x109cbcfdc3c56a164815a89be30531a4003bbc001a588149a7cbc00fb0e130e1714380000,0xa090280023d509104002241336c9a7cbc001d0e130e1d18290000,0x201704140ef25440806815a8112dc9ae0c6b15894f75cd243c187102099391a056a047b8ec66c9984237360ec542cc012eb6c3bbc0019a20064c8c7cbc00fb1e130e1d188a0000,0x1e25b820c7042ccc10b9608910212076699821883a344a5e7879b0102829840810506a5e0049c9a8db300fb1e100e1d18620000,0x1210a842a3c0014bc04818230230225410b96089ada9783bef13c47ca8d2d3b34108dd734542a360002092bef18236fbd7dc4069b60a5e000c9a8db300fb1e13111a18880000,0x2fbd24a94cd04604604604604604604604642dc42dd7268cb75cd26680091868266cd360d734db9a8db300fb1e13111d1b670000,0xd9a8db300fb1e13111d18010002,0x4c9a8dbc00fb1e130e1d18020004,0x29a7cbc00fb1e130e1d18010006,0x69a7cbc00fb0e130e1d18010008,0x2c9a7cbf00fb0e130e1d1402000a,0x1df4241207f8001df7bf5724410842443002241336c9a7cbe001d0e1d1417143c0000,0x2040197246815a81016e094102dd7341aa8f4412ac98aeb62c0c5984219b8b1339f3a150bb933d1beeb937c6bef234a0ec59220064c8c7cbe00fb1e1d1417147c0000]) (.p [0x1b52f0c49c102bc39982254112205a814a68211bae68a8d2440810506a5f80f0143f7364824a66100a5e0049c9a8db400fb1e171417146d0000,0x2aa9cd104219c980090b994573799b1042d1282952c42ac9a8db4003b1e1d181714390000,0x4cdc0ddc0530a638204e08c08c08c089a0465bb8b775cc201a0764cd06b400240937f37703770149a98e0815a0408a08c085c35044a8227b931751ee2506608dbef9de7f494d04272fdc2c23062a15094bd6a37d9a8db400fb3c1d181714d00000,0x69a8db400fb1e1d181714010002,0x4c9a8dbe00fb1e1d141714020004,0x29a7cbe00fb1e1d141714010006,0x349a7cbf00fb0e1d141714020008,0x3545ccaaaa706aab344d9aa033069314caa2b9a1f5576315c3ac9989a7cbf001d0e1d141d183d0000,0x803608655a5e0b70328974682302302302365b996eb9840340cd64aa41f300122768b70d668a002aaab835c901458a90ec8bc61de0cc4cd5808120352e4cc01339a7cbf00fb1e1d141d18a10000,0x69a7cbf00fb0e1d141d18010002,0xd9a7cbf00fb0e1d141d14010004,0x4c9a7cd000fb0e1d0e1d1402000e,0x29a57d000fb0e1d0e1d1401001a,0x69a57d000fb061d0e1d1401001e,0x2c9a57f400fb061d0e1d0e020020,0x90fa91feaf264923b412c23aa7f13f0169192fe81921d0b758c59256162374b8d42649c314911d4fbf927a52e5e411120a8a84e2d2bce78a2f2fd8c421a04fc4048c17b57ac000d06fb1e130e910000])) (.b 256 (.p [0x7264ffc0a7fe99f4a50932efe85209fa44049a69fc38bb495e25a51d2bc44ab57837efd0b088e7798c145dad2000ca5788099009a7cac000d06fb1e130e6e0000,0x189a57f3000d06fb1e130e020002,0x6ccb78570100fb0e3b1e100e040000,0x18621418027fd5a108ebe19c9587857d0021d0e3b1e100e1f0000,0x1e2351385fe2832450be3ad1933ee68850ab0851a74814cb24e2c916857d002fb1e3b1e100e400000,0x1dde22628c5f19d5e7c50665103a2b51e1ddeb503261e0a241a3ebbf3fc1d8e92eea534cc75a945630851a7428975814cb592a7165c525764898b340fe3fee207b9d9840889110964c17869d002fb1e3b1e100ea20000,0x27857d002fb1e3b1e100e010002,0x67857d002fb0e3b1e100e010004,0xc7857d100fb0e3b1e100e020006,0x1b421ad44880965c42fcbc503581add331c42801601ee07d4b969314d69f5692a647d5eb7e2356227c667857d100fb0e3b1e13115c0000,0x2c7857f200fb0e3b1e130e020002,0x12bc429a49052306a03148c1ad0af10a4e3733513fa337213165446e2b50bac0cd266154906878d93eafffd19abee0c9938999fd40196412926b5f228bb6af3c8a7fabf6f3b889906a214593249093523e3beb2548a4667857f200fb0efb3c100eb80000,0x188148b280614c937857f200fb0efb3c1311160000,0xd7857f200fb0efb3c130e010002,0x4c17b57f300fb0efb1e130e030004,0x850a8513b88524414c78843141022160d42b0b5fdde7e8d78bfbbd61934669842151e1dde231b9f1b06bbbf00d74078e19cc2d547829788d40e19cd38a570c2dc1ad2139a7cc400fb0e3b1e100e950000]) (.b 272 (.p [0x9894198949012eb81e94f4828a972440e2c98975bda144bac92ea789b060257e20255fc425937c66e0c665365a39336c9a7cc4001d0e3b1e13116f0000,0xf4246f8040b1391a046851a054c65f7cd6e949a820f3f8193510f75a8dc6ff2fe781845e66df1885164881c18c4258b7f031f2fbf815b1884b348c7cc000fb1e281e13117d0000,0x25b40a1ebc9834322d82b512b502800460145aa1412ae0d7343ac6600b29e16bdfc6b37f1f878d4f3fa94fbe337250cca4887262ba3eb36fb838c7cc000fb1e3b2913117b0000,0x4c8c7cc400fb1e3b1e1311020002,0xaaabbefd5a040a881197b9d5a040ecc7f35187f35183c351b71020412eb70d40df7e051ebf707461a5a766102043930f0e085c96e13cba6ba308678ae5eff62c69e212e8d0efe32440889110b44008214d040ff6c1002006ae000c9a8db500fb1e281e1311da0000,0x313360cc0e2ef2ad9a26c18212c91360c10b440639300c25170561364cdd03133649b0fa2084b34551837af10d503d02e54212c9a8db5003b1e3b291311820000,0x4397e14f0e4c72fdb9e1cdd6e949a82254103dd28297ac0bd781840a4e6a5e18914140acf5e6b6f0f13c57c669945aa8f0eef0c0c55fe0c4a5eb039a8db500fb3c3b291111790000,0xaabba282813828c0a04e0a04e0a04e0a3028c0a268144eee2ddd734502d40ec99a0a01a31a814b375dee68a9968515a145681027044d020544397e051cbe6844d472f9a3d6a26a089adc3518e4c7f3512b755555ddd1300d4093143d78b5096a066b3498287af16a121230a29a8db500fb3c3b291312fc0000,0xd9a8db500fb3c3b291311010002,0x69a8db500fb1e3b291311010004,0x4c9a8dc400fb1e3b1e1311020006,0x29a7cc400fb1e3b1e1311010008,0x69a7cc400fb0e3b1e131101000c,0x2c9a7cea00fb0e3b1e130e02000e,0x2ee02934005d922dabf65e455d3187340276ad7655abcff6f5b3910d91de95537710a642813f03293e52a56c9a7ce9001d0efb3c100e610000,0x594be1576ae8262dd56fab86062c9828c2a8330021e37157fbf18ecbf43913670e7d5eb89fd1985baadf77d5c308145f7128c8c7ce800fb1e643c100e6c0000]) (.p [0x185994818ba499a692748200b07c299de5d4c9f0a6778e251930591452aa224553c55cd523b4a56cd5c9838c7ce800fb1efb65100e640000,0x4c8c7ce900fb1efb3c100e020002,0x7f9a8db800fb1f643c0e0e010000,0x170cb9a8d0100fb1f643c100f050000,0x1b0b81e80f407a55b5a4149a8db8023d1f643c100f1a0000,0x37098b7ddf2afb9a23715ab0a8f066102206a0962ee0c948db802fb3e643c100f330000,0x50a7af50f914c282813828c0a04e0a0450513a8c7050270502705181460502a204653cd98e5fb61e1c1d4289a8226851a089add2829786064c140a04d40f0a7dbcab66102224442388140880549a95b802fb3e643c100fbc0000,0x29a8db802fb3e643c100f010002,0x69a8db802fb1f643c100f010004,0x39a8db800fb1f643c100f010006,0x19c9a8de200fb1e643c100e030008,0xbac0ef31ae184a3ca8149a8de200fb1efb650e0e180000,0x257ec8f9a8d01003b1efb65100f050000,0x1122ae5d22e2a534826f710a2c5e93453e948c948da3023b1efb65100f2d0000,0x1f645c58ef44c98955f64d14d145c2e165459516545c2e170b8245c8493afe6a2454483327f8ea2499ffa68905fd298e122d770990664d0e4c82792122825cea4c9a4114d20932690453482280a779170ce4c9a95a3023b1efb65100fc20000,0x29a8da3023b1efb65100f010002])))))) (.b 432 (.b 352 (.b 320 (.b 304 (.p [0xc9a8de2003b1efb65100f020004,0x2e2262c8b9546bbac948de200fb3cfb65100f120000,0xff9a950100fb3c8265100f010000,0x3707951b9a95b202fb3c82650f0f090000,0x1b82e59149895b2026a3c806510100a0000,0x250d82b0b1b04f8ab64cd0540a6584a1b056ddaa69a0a814c7c55b26682c8a4cf2ede55b349a995f026a3c6f6510105d0000,0x1286c15b76a9a6802994f3d7a9275dd5c8ecd9b366ffc66931a4953492a69254d24a9a4953492a6931a693482283b9a995f026a3c807010106f0000,0x4c9a99b2026a3c80651010020002,0x939a95b202fb3c82651010030004,0xd9a95b202fb3c8265100f010006,0xc9a95da00fb3c8265100f020008,0x26b9a950100fb3cfb830f0f030000,0x4fff1ff8d4799ff8d4fe2c9ff928ff3936a2499fe3a89262e5dfe721d7493147ba990ea79a28b2b8e452bc5c8c9a95da02643cfb830f0f590000,0xd265138a27144e289c5139aa372f9a1cbf0b41e2d03a8144f50a1502899e511451145114511459531c98b8a61714c65c504536f2a539a95da02fb65fb830f0f790000,0x69a95da02fb3cfb830f0f010002,0x359a95da00fb3cfb83100f020004]) (.p [0x4c9a95e200fb3cfb65100f020006,0x29a8de200fb3cfb65100f010010,0x69a8de200fb1efb65100f010012,0xd9a8de200fb1efb65100e010018,0x4c9a8de900fb1efb3c100e02001a,0x29a7ce900fb1efb3c100e010024,0x349a7cea00fb0efb3c100e020028,0x124922c023869c99f269a91c328b9944d831994d59315a8a4677f7e8404df8d6be13e9dce2c3d10425e4d26bbf5b77e13a64507e96fc3654d79345148c8c7ca8001d0efb3c1311860000,0x30b1b0e70382a69170664c681c362ac4e4dc264549792415706252410964c16149d71643c804c8291c11899b2668b092cd1452307a4026450534050527360c5321ebbf1fa4146af070de4f0e505ac677388945bf884338ff600b4a9cad3b349a8da2001d0e643c1311e30000,0x909241922932693cbd77e849824c126093048b3ec9f66bbe6a124a8492a1209c2494338498245c9309090664c4848a92c9a8da201130efb651311780000,0x1a487d3ea8a270542495147641990904516126093049824c122ce1b22e0e5d3aec82a124cc8492a68fe1320ef7099349855e499a424c0a4959a8da2011d14fb6513118e0000,0xe79a8da2001d0efb651311020002,0x4c9a8da8001d0efb3c1311020004,0x189a7cea001d0efb3c1311020006,0x29fea706a0b9500659008c7caa00901e833c13111c0000,0x301c266cd070b2e49b00e2ec99a01c5c505cb22983e59540a6db0aa7c878a2ef953e0530baab957135c19b24411c5d9334dbcab62c9a8d5800391e553c1311800000])) (.b 336 (.p [0x28bb228a6e9d493a9cd3933498d263498d24a9a4114d263498d24a9a4953492a6931a4c6931a45c9a4c69c3642726a82ae0e272139176693005495f22933d9286f0daef51ca9ca4af5b3498f5e1ba504cadc822981a59a8d5800391e83561311cd0000,0x4c9a8d8400391e833c1311020002,0x4a2e082e5906a3c7a14114948d8100903a543c11111b0000,0x5814d9334014cb0b13364cd00531f156c99a0a814dbcb3bd85cf11e2be973c5bcab64c9a957f005c3a543c1111560000,0x7f37751455a345345c2e170b85c2e170b81460518146051814605181460518146051814605181460502705027051814605181460518144d028cb579a957f00905d543c11119d0000,0x349a958100903a543c1111020002,0x189a8d8400903a543c1111020004,0x149a8d8400903a543c1212050000,0xc59a8d8400903a833c1311030002,0x349a8daa00901e833c1311020008,0x2549a7cea00901efb3c131103000c,0xdb9a7cea00fb0efb3c131102000e,0xd9a7cea00fb0efb3c130e010016,0x4c9a7cf300fb0efb1e130e020040,0x29a57f300fb0efb1e130e010050,0x349a57f400fb06fb1e130e02005e]) (.p [0x1fc0522ca0b1a06fea513cb24cd59248ed00427495f2a695e3d1802efc0d94f537797ec4fad5fe056461e3eafdef2fdac4048cd164c17b57ad000d06fb1e1d146c0000,0x205cd3192e0c4d9334d15c910c068b2602140d97341a4184b994573564cd898061809040202aae0cf3ae0c301a6a927882145933120002aa490481fe000f3ae0cf386e4cd1042583dd0025d6301a60e2c9a7ca5000d063b1e1d14cf0000,0x1fd257a9aef593e1a848bb9a848b86809312126003257804aa823aa0e204bfc882664af1825780b48c9a7ca4000806fb3c17145a0000,0xfe023802909c8a18014827c9a0a9fea00b2d9922d339b1643bfaf24c8c7ca4000d09fb3c1714440000,0x6e5d3ae1d601324e1360cd992bd6c8c9101682015038939345388855dfa2c98909164a0d2bc36462c9a8da1000d09643c17145c0000,0x7f30317fe1482a6849824c126093049824c126091721260dffc697808d2bcc02b23093049824c126093049824c126093048b909275fcd448a9fc17f10961260933fecc95e3914af9e919a2e79a8da1000d09fb651714ba0000,0x4c9a8da4000d09fb3c1714020002,0x29a7ca4000d09fb3c1714010004,0x349a7ca5000d06fb3c1714020006,0x5d2bd08f4af4210918492a126093049824c126091721260d247f4290419212081a12609304982459cc8eb93867091724c11d643eb9c4210a424c79ce218da4c048e212fa2c99abc009539495eb62c98fe024ff948a8eb9316a49989a7ca5000706fb3c1d18dc0000,0x234bf08423861482bd093049824c126093049824c126c8ea85899f499a00292409a7ca5000b08fb3c1d185a0000,0xdb9a7ca5000d06fb3c1d18020002,0xd9a7ca5000d06fb3c1d14010004,0x4c9a7cad000d06fb1e1d1402000c,0x189a57f4000d06fb1e1d1402000e,0x620769c5b400b002e3eafff90017b57f400fb0e6e1e1c14200000]))) (.b 384 (.b 368 (.p [0x40b9a90205c5a54b9a6930300b98004c200d82185707aa68a97245734987f457066c047166b2457066c04717669b5a70693010a0255c9828124b8315c3ac90492e0c5726689359a4cc2c9a7cc3001d0e331e1c14b70000,0x900205baa5cd34d008c7cc300fb1e331e17141a0000,0x5a8360addd715006a052035006a36d79a846dd5a0409c1027046046046cb7128b98c0d29504b0099beea3574624f40c9ada0424614910240605dcc58b5a2325c99a2800980c4f4410960c982402a68a80c35d0315c99a1f593349a8dc300fb1e331e1714e90000,0x959a7cc300fb1e331e1c14020002,0x349a7cc700fb0e331e1c14020004,0x1080c1b21b1667361d61e400520a4a92a5cd26280488101b1432a82e886031c98a6555387d3d48c3eb349a4af102903089c9a6800a59a7cc700fb0e6e341c14880000,0x4c9a7cf400fb0e6e1e1c14020002,0x2459a57f400fb0efb1e1d14030008,0x69a57f400fb06fb1e1d1401000a,0xd9a57f400fb06fb1e1d0e01001a,0x4c9a57fb00fb06fb0e1d0e02007c,0x29a32fb00fb06fb0e1d0e0100a4,0x69a32fb00fb02fb0e1d0e0100b6,0x99a32fb00fb02fb061d0e0100ba,0x1bf98d2378094e450408b165ad2ce5600480029601318b7433400024824892f63162589611facde0ac02632447aa5ec62c5838810601223d507ca89909c3af5619cdf141588098c589a32f60005020d06fb1eaa0000,0x3fc5534dd000d0608063b1e020000]) (.p [0x1cdeb55340100fb0e08063b1e020000,0x1802d4af212112a169bbbc497bbc494ad2621400b6542c210bb010c054bc492159442150862f6852726614134dd02fb0e08063b1e670000,0x36856262c89ecad160a9788121531ed610855b120c83762490d0cc210a7c10c5ec6205389049cd88f12588dd0b2b0842ada8674e4a18bbbc4b76813f24488e52f2d108594218bd8f66162224448262c15542dd02fb0e08063b1ebe0000,0x25534dd02fb0e08063b1e010002,0x35534dd00fb0e08063b1e010004,0x345534de00fb0608063b1e020006,0x3cbc6800498a5b34a864c4280257b4cd1621400a551b0f698b14c5ed332dec665534de00fb060d093b1e4b0000,0x4c5534f500fb060d063b1e020002,0x6e3ab0dd6974c60d6ee269b37ec4c3106084546f408411756246a8d21e3567c07657b590b8ff47d19a2cdc0ea4816c3b27fcd26086ce60dff30029138187332e88c51022affe2c90404192bff9908de33495534f500fb060d06fb3cb30000,0x2c15632f600fb060d06fb1e030002,0xe00b8b570100fb0c08063b1f060000,0x213fccecd2a3428c14c2c444882985eae8148b57cd02fb0c0806291f2c0000,0x2d547c5d890280207472597a3432457c85985888dc8906c59020a2c49fc18018532f72d61258b55642f67e5b97eeb2341bf9e5fb12099b94bd25ae919135bf9e3d2b1548b111b91243f2fd8921a801a28b57cd02fb0c08063b2ab50000,0x2c8b57d002fb0c08063b1f020002,0x4209a57d200fb0608063b1e050004,0x4cd9330d4b30ca4cc3002003bcbf6b9af23d54fcfbe3d831ec15804c64df1ec38cd03d623c9c1df1e431a00f580791458b6c9a57d2000d060d093b1e6c0000])) (.b 400 (.p [0x1e5e2801093102302409e20485836568b0dcac81294b65ebe9a21123da3d9334542cac210a3000eef0005649c58bbbc497bbc53408751fb10859421996d6633f83167dbd62d23b15b19b93347857ce00fb0e0d09281eaf0000,0x4c9bf76f9492da16014ad166f6f4019033d88c5dc689f778b01a496f797cccfaf69e3e32667857ce00fb0e0d093b294a0000,0x2c17b57d200fb0e0d093b1e030002,0x4d9330ca0ec04292809a7cbc001d0e0d09281e190000,0x423000846da900c712fdde000ac1e7f4209a7cbc00fb1e0a09281e2d0000,0x1020dd704681c902b770302ae1f43bc3c437379984237be3cafbe668a85def8c4706085162bad8c48264860062c8c7cbc00fb1e0d0b281e670000,0x18811a7e0ea9789210f72a2016e7e48000cdbca5e002d52f1000ce9c9a8db300fb1e0d0b221e400000,0x203704b7041906382056810270409c1181181181187b8340340ecd3555241e8c9678904c118118113dd4044f73068a923609299ab041b825b99348c922441b99207240ec1eea0f10490c04b0176310387d5019b0482669a8db300fb1e0d0b2823e50000,0x2c9a8dbc00fb1e0d0b281e020002,0x29a7cbc00fb1e0d0b281e010004,0x99a7cbc00fb1e0d09281e010006,0x349a7cc100fb0e0d09281e020008,0x1970509b3718ae682413244d9a0900c4068b0004545b97164aaae6ae0c571668b36207340e4cc125de388eb04c9a7cc1001d0e0d093b296f0000,0xf124640a118173244c1a17dd424c0b98aeb1857cdc5f792ec542e85dc54e1c62383998aeb1a2f60c8c7cc000fb1e0a093b295c0000,0x1fd2dc124286418e0815a0409c118118118112b755538339918c890c890c890cb46e92052c4640894c108189642a3626cd30640605cca26cc716233609299846e57242ad882fabf0f03833d600241000f3fa0e2c9a8dc000fb1e0a093b29da0000,0x189a7cc100fb1e0a093b29020002]) (.b 416 (.p [0x14c092aaaef316280098102aaaaa8d560248151009232d1e25df78ce08140204e08c089106481d82978fc18b043978778b2464094bf240c1c0604b635cd3499399980778e205b2668b01024023024b7316600959a7cc100fb1e0d0b3b29ce0000,0x99a7cc100fb1e0d093b29010002,0x69a7cc100fb0e0d093b29010006,0x2c9a7cd200fb0e0d093b1e020008,0x29a57d200fb0e0d093b1e010012,0x69a57d200fb060d093b1e010016,0x4c9a57ed00fb060d063b1e020018,0x812411601083001020df14cb6b0098d6eb0cd6c9a57ec000d060806fb3c330000,0xf981dd92620687216653c572f5d6468b0446464127f60774668b34f98151490058fd8b64abfccce20157319842151f14f8a7c023da102ec48e4c7857eb00fb0e0806643c870000,0x49931ad6e09b1345124439b38096dae818834634e6fff890e3891bdcb7225fc26835ebfabac3b070727b5d6cc6288c59b81d4230ca0520df8c527b10084ff8927fde731990f2d3946f946f18b97857eb00fb0e0806fb65a50000,0x2c17b57ec00fb0e0806fb3c030002,0x7f9a7cc600fb0e0606643c010000,0x2f9ab7fac591134236fa934d6cd8902e09a7cc6001d0e0807643c260000,0x43f9a4ff4c8cb03a334c8149fd81dd18a7cddd02c2881d1c96468b37237210a05b2c5aa8f98e0bd5d096fb1fe855bd7cbff7466668bd8b60c8c7cc600fb1e0807643c810000,0x2c8547c538900d6bf88149a8db700fb1e0807493c1a0000,0x388e84009e456d4aec9a8db7003b1e0807644a160000]) (.p [0x310a68c811259a8db700fb3c0707644a100000,0xc8046223320948db700fb3c0808644a0e0000,0x10dcbd57868254bd297a52f4a5ffe327122831c915a244e489c9139227244e4e24546e5f8681194f156397edcf0e2eb792260226b620c716081029207bd8a73c952f100c9a95b000fb3c0808554a8b0000,0x2a4aa353ba05dd240cc81ebefc6463231918c81ebefc6463231918c8c6463231918c8c640a0c8139918c8c6409cc8c6463231918c8c644adc14157162c4415bc2b62cd0194619403b9a95b000fb3c08086456be0000,0x2c9a95b700fb3c0808644a020002,0x29a8db700fb3c0808644a010004,0x99a8db700fb3c0807644a010006,0x69a8db700fb1e0807644a010008,0x2c9a8dc600fb1e0807643c02000a,0x29a7cc600fb1e0807643c01000c,0x69a7cc600fb0e0807643c01000e,0x4c9a7ce100fb0e0806643c020010,0x20bb7ac549bb7ce0c8309209222f6e71488cd27849c8426f9041d7c5b2508a0e2f1c5844209a7ce100fb0e0606fb65540000,0x8de0d1f9a7c01001d0e0807fb65050000,0x7fa041373d8a763acbac4ffb7a9477fd7a94766337b102c4d32378c8c7c9e021d0e0807fb65370000,0x3f495254a7be6a63398c04c02480248024802480260130098049420261082024e05ff83408a8106340828404148404148404900131b5a8d6a310680105061050612434f08a2604041c1a74e2c9a8d9e021d0e0807fb65c40000]))))) (.b 512 (.b 464 (.b 448 (.p [0x29a7c9e021d0e0807fb65010002,0xc9a7ce1001d0e0807fb65020004,0x8de241b62c33f61bf8a48bbd177e8f7ca30ca1118b08c7ce100fb1e0807fb65280000,0x2a0509a51ad462086984c613184c613184c61318490c263092184c613184c6131849898415038b835038b828d80727668bc734173201df354d7939d9ef38b37d6f0ad9a2c0508c32826414230a104c9a8dba003b1e08078265c40000,0x36b9a8d0100fb3c08078265020000,0x6c1888c948db902fb3c07078265080000,0x646d7df849021c9a95b102fb3c07077266100000,0x56c9a95b102643c07078273050000,0xca09895b102fb6507078273060000,0x21cbf070fd8290854397ca591a4e5f6342eb79234c89ad88052f1049c9a99ab02fb6507077a73400000,0x6596dd57b0e084c264349c48af61c58a8c894b6ea5e284652d4bc51e506409cc8c640a0c890c890c890c8c644a13064008c90d019383c8c890e2cd019403b9a99ab02fb650707827b9b0000,0x2c9a99b102fb6507078273020002,0x29a95b102fb6507078273010004,0x69a95b102fb3c07078273010006,0x109a95b902fb3c07078265030008,0x189a8dba02fb3c0707826502000a]) (.p [0x259a8dba02fb3c08088265040000,0x99a8dba02fb3c08078265010002,0x39a8dba00fb3c0807826501000e,0x349a8dd800fb1e08078265020010,0x31f9a8d01006a1e0707fb83030000,0x2089ee70670631050808290808290808290808280104e0260136cf7b3237ea98c9a8d9b02321e0707fb834f0000,0x184c20a096919b026a33070792830a0000,0x6277d67ffe97f8d0a7d6f3bc9e4e61243098c263098c263098c263098c2614c0b9955499b32ac580a10614c0b934646c15c15b16680ca0182b668b01420da415b34580a100f0984db349a9771026a3307078983b60000,0x34f2d674f7e4132122716489c9138b27184c612626131b9a9771026a330707928a340000,0x2c9a979b026a3307079283020002,0x3659a8d9b026a330707fb83030004,0x349a8dd8026a1e0707fb83020006,0x4939a8dd800fb1e0807fb83030008,0x2c9a8de100fb1e0807fb6502000a,0x29a7ce100fb1e0807fb6501001c,0x69a7ce100fb0e0807fb6501001e])) (.b 480 (.p [0x99a7ce100fb0e0806fb65010024,0x2c9a7cec00fb0e0806fb3c020026,0x29a57ec00fb0e0806fb3c010038,0x349a57ed00fb060806fb3c02003c,0x808324fcbad8d57f9899fabfe5af672b2735c4d266eae98c17b579f000d060d09fb3c330000,0x1a23d6b8b3450420a9ab3669816315cd36482098b0010868920210425cca2605cc147d319b344344999b34c12092d1bf131926ac0e2ef2a2030b37989a5d6cde02cc649f950e680133ec2dd69a0e4c9a7c9c000d060d09643cb90000,0x1152106254b5424cda026013009804c024d6a94260093b2b004c08f51302a57068b3fd084049a1302024ecd46fd5a639a7c9c000d060a09fb65770000,0xd059bd74bd131cc60260130098049004c0248024802486809804c3f484c3f484c02640820bd377a2c66fc0260130098049883afc10694c04c026013009358a57aa6ff98098024a8098580808284c6a37a95a73b9a7c9c000d060d0bfb65d10000,0x99a7c9c000d060d09fb65010002,0x2c9a7c9f000d060d09fb3c020004,0x189a57ed000d060d09fb3c020006,0xf2f1a0058034fff1f55a9f90017b57ed00fb0e0d09883c1c0000,0x38b83302ae0c5b971668b0300b980052038b8348d80904894c76fc09226314b96fd08cd89b341253244d9a0921880c716020038b9391ab362cd35734cf0484d8b0e278ae686a99a2cc4c9a7cc5001d0e0d095a3cb70000,0xa94446639bdbd2058030ca08c7cc500fb1e0a095a3c1c0000,0x19201a072dc4d8b3404903b5e9211924232d02052bef4b72f3d12a339227244e48ad12282652347f5a30fe9230fe9230789230d6ea5f9216c14bc4903166c4967f941394099b166537c99393cfb28a11d07c284a60291fc9878acfb28a197e23de79c466349a8db600fb1e0a09463cdf0000,0x605c9a038b835361b0762cd01186500939a8db600fb1e0a095a472a0000]) (.b 496 (.p [0x2c9a8dc500fb1e0a095a3c020002,0x1339a7cc500fb1e0d095a3c020004,0x349a7cc800fb0e0d095a3c020006,0x337aa5174e63013026013009804c026013009804c026013009804900490049004c0260130098049880982560310d106aaab8b1602424880621e20d23566c9982420e4228de84a6024a2cde6263426c45898d16024228de80420939a7cc800fb0e0d09885be70000,0x2c9a7ced00fb0e0d09883c020002,0x959a57ed00fb0e0d09fb3c02000a,0x69a57ed00fb060d09fb3c01000c,0x99a57ed00fb060d06fb3c010014,0x2c9a57f600fb060d06fb1e020052,0x29a32f600fb060d06fb1e010070,0x349a32fb00fb020d06fb1e02007c,0x13404ef9f1ed742046021191104041caffe0ec6693fe2043bfe0d258d15277cc66b37e7d024ff134af30049275cb37793262beb7234b30a277df1ef18b2b260fcc00e54af5ab3d8c9931219e461ea3d262c15632e3000502fb0efb1ea50000,0x8941ccc069b97910cbd166cc2d89a0336b6280181aaffb19b9221b83198c7ff301a0ef8cd0519a0b809a8b109c9a57af0005021d0e3b1e6c0000,0x377adadca40c924906b966ef14fcd6e6fac90eb58fb57ac5ee48c9247089637d1906a8c34af183d8fabc63c7d18f830e2c5be48c17b57ae000302fb1e3b1e640000,0x1034859a38d73f8bc86a90a3211219f41d20eb6868009a7ca60003023d1f3b1f320000,0x23ae9a0276b723495e8149a7ca6000302fb3e291f170000]) (.p [0xd5fbb416248c24c1260930492a0ca832a0ca8492a124a8498245c84994c849ff96bfa4be9a148201260934f4f664af9e9de414754a0200c92032606459c9c86522e09832133e45833248c8322a504260c8323f179e596323522d48206241914c069a7ca6000302fb3e3b2aeb0000,0xd9a7ca6000302fb3e3b1f010002,0x409a7cae000302fb1e3b1e040004,0x189a57af000302fb1e3b1e020006,0x3429165014a4af1823004355ef2f58fabc639918b04017b57af000504fb1e3b1e2e0000,0x211817071b0c0bb0f3421098264886368b260807e65b5a54a88bdf8c99c6336218d2070602180211f95c79c370fc9e70dc18cc6d34431a410a084cc2c9a7ca70005043b1e3b1e940000,0x7f42909169120cc8493321248a424999092547f324a8fe6413dfd08fa23880580a849332124a8492a126091721265a4848a97a2e7323ae2d1d72608524e9208522996b6af072a672722ce5257a0e2c98fe023881924926c8eb824c6a645d8bd779e49989a7ca7000504fb3c241ee70000,0x1036afd11f442123093049824c126093049824950930492a124a8492a126093049824d91cc8eb838c0652699cd8b39495eb62c3fa00292549a7ca7000504fb3c2f25910000,0x159a7ca7000504fb3c3b1e020002,0x4c9a7caf000504fb1e3b1e020004,0x29a57af000504fb1e3b1e010006,0x69a57af000502fb1e3b1e010008,0x4c9a57d9000502fb0e3b1e020010,0x7608b66f588ababfcb77ee6918eb5a59ae7434a6e4189324198c17b579f0003021d0efb3c330000,0x105fe84bd506a08337c802480248024c882009200260125404c024cad52d508200248089202260404d8054580808310981012500704049102dbbc2bcc2433480dad684b6bac845ed4142098c16003237804d409a7c9f0003021d0efb3cd40000,0x189a57a00003021d0efb3c020002])))) (.b 544 (.b 528 (.p [0x124116010ea8d002d92bfe260c0098cd4017b57a00005041d0efb3c2e0000,0x1084a2e0a3566c587e78421128b24431b498b0012f45b2b5c59a2cd9336686024102d602830154f7eb66f3fba55cd7116b111a412153409535c4c4c9a7c9d0005041d0e643c8d0000,0x8de0d09f9a7c01000504160efb65060000,0x3fd4a0415be1aaa11508b42020a53013009804c024d62913541d9580248008bbd0130b0101050989a7c9c020504110efb65640000,0x408d9bf097a86b3515fc2bf857f0afe15fc2bf8437e54fbf2b31809804c02601300920098049004900490049004c02177cc1f82131fe0213659a7c9c0205041612fb658a0000,0x4c9a7c9d020504160efb65020002,0xb39a7c9d0005041d0efb65020004,0x2c9a7ca00005041d0efb3c020006,0x29a57a00005041d0efb3c010008,0x349a57d90005021d0efb3c02000a,0xd002d77d78d8d7131cc7319304390017b57d9000402fb1efb3c230000,0x1b37e8b4262b39993272b35c41901c0c80c80c80c80c80ca1012446cdfb51e20cdf90840411ffc0322020e5020c4202480a87c8983c4263fd084da222089b6682024e099fea44441a921f41348093e826309a7cc90002023b1efb3cbc0000,0x3f9b169500925424902490249024902490245e9e05cd00a7d04aa848322d5bbc53c8c19fc48c9a7cc9000202fb3c593c5d0000,0x1fc73f7c1e18c98b47f00a408c7ca9000202873c875a190000,0xd6d0d6c9a8d53000202593c6c5a090000,0x1f308411040948d53000202593c876d0e0000]) (.p [0x7ea9509e3044c08981130226044c0899616266c98b0406ca0d6c98b01a4067f1cc4419efc842089b64c9a954c000202593c7d6d630000,0xfd52d508b5307038191c0e070381c0e0703203200c80226044c08920224808981130226044c08931044ca779a954c000202593c877e6e0000,0x2c9a9553000202593c876d020002,0x29a8d53000202593c876d010004,0x2c9a8d6b000202593c875a020006,0x13fdda0b1848ecdc92aa0c981930326064c0c981930326064d9180d8b92a5099304293642c646c98b340906b62c980d20323835b164c06901b686359a8d6b000202875a875a960000,0x4c9a8da9000202873c875a020002,0x2549a7cc9000202fb3c875a03000a,0x159a7cc9000202fb3cfb3c02000c,0x4c9a7cca000202fb1efb3c02000e,0xb6e1ac59a04adc4cd9316681b361b1762c98204350052128b8315f9327331759894a0eb68691b51f30a277990bacc9c8cf7f86334c4c9a7cca0004034e1e513c7d0000,0x54aa608981130226044988224e1632364c582109b2bf268dfaa6bab263deb628deb64c59a210dc4590841149a7cca0004034e1e7752620000,0xc59a7cca000403fb1efb3c030002,0x349a7cd9000402fb1efb3c020004,0x3b9a57d9000502fb1efb3c020014,0x99a57d9000502fb0efb3c010016])) (.b 560 (.p [0x2c9a57e3000502fb0efb1e020024,0x189a32fb000502fb0efb1e020036,0xd1ab476801600dbe797c12ff90015632fb00fb06550e791e230000,0xc0010858673f2ba20d4b9324573572668304604ab93345706b8b245706b9b7c66e2cd262c17b5727000d06190e351e550000,0x10b72e2cd1402442b835cd11b4555c18ae4c598915c95cd10382a62aae68ae2c99b0001dd1cd048266d9a0c5706208262c555c18ae4c59b0001dd1c1821458b6c900010ca6ef80d307262c9a7c27000d06190e351eb70000,0x189a57d3000d06190e351e020002,0x28b958b680160059fdde7c90017b57d300fb0e190e351e1e0000,0x30f57244c18e0c45c62530a2c0c02e6515cd062b9a21b9a4c5989a7cbd001d0e120e261e410000,0x1090b93101862b733400485cc282601455266cd260d440248c65490a9230a2c118118118118113dc12c40340ecd8816a0762cd040b0d746491b3d07893d3669a4c58009009232dd72683bc19330029a7cbd00fb1e120e261ecf0000,0x349a7cbf00fb0e120e261e020002,0x500c2cb9ab07b9a7cbf00fb0e1913261e130000,0x4c9a7cc200fb0e190e261e020002,0x805c988402e4d2a5c5ccd1502e6800939a7cc200fb0e190e35272a0000,0x2c9a7cd300fb0e190e351e020002,0x29a57d300fb0e190e351e010008,0x349a57d400fb06190e351e02000a]) (.b 576 (.p [0x91c425cd260029052040b9a6555c98b26020522e6800a40282cb9a0cc2000c2cb9a2c98857354062034555c188d62cc68b2602140c2dc359a0c010a59a57d400fb06551a351ea00000,0x4c9a57d500fb06550e351e020002,0x2043ab124035ae2c9830017b57d5000e06190e79361d0000,0xa65497262c50014842048c97173262dcb9a20904cd11b4d910102114ed9136b15c95c98b31a4c9a7c3f000e06190e4b36610000,0x3744cf7e059bf1b45809813009804c026013009804c026013009804c026013009804c02601300824ac0911706928d6b8b262c00420939a7c3f000e06190e794c900000,0x2c9a7cd5000e06190e7936020002,0x939a57d500fb06550e7936030004,0x2c9a57fb00fb06550e791e020006,0x2459a32fb00fb06fb0efb1e030016,0x69a32fb00fb02fb0efb1e010018,0x99a32fb00fb02fb06fb1e010050,0xd9a32fb00fb02fb06fb0e0100ce,0x29a18fb00fb02fb06fb0e010194,0x69a18fb00fb00fb06fb0e0101a2,0x99a18fb00fb00fb02fb0e0101b4,0xd9a18fb00fb00fb02fb060101d0]) (.p [0x29a0bfb00fb00fb02fb06010218,0x99a0bfb00fb00fb00fb06010238,0x159a0bfb00fb00fb00fb0102023a])))))))
private def data : Store := ⟨vals,rows,model,codes,8⟩
def ok := test rule 5 11 data
theorem finish (checked : OMA.Tape245212.Before ok 579) : Deny 5 11 ![⟨2,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨12,999999999999999999⟩] := by
  have same : data.vertex 578=![⟨2,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨12,999999999999999999⟩] := by decide +kernel
  rw [← same]
  exact close valid _ _ data 578 checked
end OMA.Tape5_11_245212
namespace OMA.Tape5_13_245212
open OMA.Box245212 OMA.RankTape245212 OMA.TapeShared245212
private def vals := OMA.PageTree245212.get (.b 272 (.b 128 (.b 64 (.b 32 (.b 16 (.p [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16]) (.p [17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32])) (.b 48 (.p [33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48]) (.p [49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64]))) (.b 96 (.b 80 (.p [65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80]) (.p [81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96])) (.b 112 (.p [97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112]) (.p [113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128])))) (.b 192 (.b 160 (.b 144 (.p [130,131,133,134,135,136,137,138,139,140,141,142,143,144,150,151]) (.p [153,154,155,158,159,160,161,163,164,165,166,167,168,169,172,173])) (.b 176 (.p [175,176,177,178,179,181,182,185,186,187,188,189,190,191,192,193]) (.p [196,197,199,205,206,207,208,209,210,211,212,213,214,215,217,221]))) (.b 224 (.b 208 (.p [222,223,233,237,238,239,249,252,253,254,255,256,259,260,261,262]) (.p [263,269,270,276,277,286,287,292,293,302,303,307,310,313,314,317])) (.b 240 (.p [318,319,320,331,334,335,339,348,350,351,352,358,365,366,374,375]) (.b 256 (.p [382,383,385,396,406,414,415,432,452,453,455,456,457,478,479,517]) (.p [558,561,564,624,633,638,639,660,715,768,776,777,800,830,831,835])))))) (.b 400 (.b 336 (.b 304 (.b 288 (.p [836,846,902,903,958,959,968,993,1025,1034,1035,1053,1069,1113,1135,1161]) (.p [1266,1267,1297,1320,1321,1407,1606,1918,1919,1936,1937,1986,1987,2050,2051,2070])) (.b 320 (.p [2071,2106,2107,2226,2227,2270,2271,2594,2595,2642,2643,2790,3257,3692,3700,3838]) (.p [3839,4096,5580,5581,6535,7661,7678,7679,8696,8862,15358,15359,30718,30719,61438,61439]))) (.b 368 (.b 352 (.p [0x1dffe,0x1dfff,0x3bffe,0x3bfff,0x77ffe,0x77fff,0xefffe,0xeffff,0x1dfffe,0x1dffff,0x3bfffe,0x3bffff,0x77fffe,0x77ffff,0xeffffe,0xefffff]) (.p [0x1dffffe,0x1dfffff,0x3bffffe,0x3bfffff,0x77ffffe,0x77fffff,0xde0b6b3a763ffff,0xf256c8fc5d45d9dfb,0x10ad25178760d42ed5,0x10ad25178760d42eda,0x10ad25178760d42edd,0x10ad25178760d42ede,0x10ad25178760d42ef8,0x128ce887a1615f1ab0,0x128ce887a1615f1ab3,0x128ce887a1615f1ab5])) (.b 384 (.p [0x128ce887a1615f1ab9,0x128ce887a1615f1abb,0x128ce887a1615f1abd,0x128ce887a1615f1ac9,0x128ce887a1615f1ad9,0x128ce887a1615f2389,0x145a2e34d2b66ee684,0x14e627a5b754e268c4,0x14e627a5b754e268c6,0x14e627a5b754e268c9,0x163bfb6ce86668a3bf,0x17a257ca02025b19b1,0x17f4a917a3fee7a8df,0x187b054496cfb81c58,0x187b054496cfb81c5b,0x187b054496cfb81c5d]) (.p [0x187b054496cfb81c67,0x187b054496cfb81c81,0x1b3b4dc85d23bf50c1,0x1b3b4dc85d23bf50c4,0x1b3b4dc85d23bf50c5,0x1b3b4dc85d23bf50c6,0x1b3b4dc85d23bf50c7,0x1b3b4dc85d23bf50d0,0x1b3b4dc85d23bf50d1,0x1b3b4dc85d23bf50ee,0x1eadec03a98064531f,0x1eadec03a980645321,0x1eadec03a980645324,0x1eadec03a980645326,0x1eadec03a98064532c,0x1eadec03a980645332])))) (.b 464 (.b 432 (.b 416 (.p [0x1eadec03a980645393,0x205f5585d89c2a629c,0x22ab8ae837ae440fa4,0x22b1c8c1227a000ef5,0x22ea5b2775dafb2abe,0x230a18eeb1004de0a7,0x232a9ff2c8634775f1,0x2350ba6377f02e3d01,0x235db090056a319b9b,0x235db090056a319b9c,0x235db090056a319ba0,0x235db090056a319ba3,0x235db090056a319bac,0x235db090056a319bbb,0x235db090056a319be7,0x26f059218034103ac7]) (.p [0x26f059218034103ac8,0x26f059218034103ac9,0x26f059218034103aca,0x26f059218034103acb,0x26f059218034103acc,0x26f059218034103ace,0x26f059218034103acf,0x26f059218034103ad1,0x26f059218034103ad2,0x26f059218034103ad3,0x26f059218034103adb,0x26f059218034103aeb,0x26f059218034103aec,0x26f059218034103aed,0x26f059218034103b1c,0x26f059218034103b1f])) (.b 448 (.p [0x293eedfb643886e0be,0x2b50957e451d5eb235,0x2b50957e451d5eb237,0x2b50957e451d5eb239,0x2b50957e451d5eb23a,0x2b50957e451d5eb23c,0x2b50957e451d5eb242,0x2b50957e451d5eb244,0x2b50957e451d5eb245,0x2b50957e451d5eb247,0x2b50957e451d5eb25f,0x2b50957e451d5eb260,0x2dc8364ffe851e6b4d,0x30cc7ad76f8aee9c31,0x30cc7ad76f8aee9c34,0x30cc7ad76f8aee9c36]) (.p [0x30cc7ad76f8aee9c37,0x30cc7ad76f8aee9c3c,0x30cc7ad76f8aee9c3d,0x30cc7ad76f8aee9c3e,0x30cc7ad76f8aee9c43,0x30cc7ad76f8aee9c44,0x30cc7ad76f8aee9c45,0x30cc7ad76f8aee9c4c,0x31f2563002a3441a67,0x3299bd9adc6c9d9f95,0x339413a960d546bbbc,0x339413a960d546bbbe,0x339413a960d546bbc2,0x3434f873142f0c4736,0x3434f873142f0c4741,0x3434f873142f0c4742]))) (.b 496 (.b 480 (.p [0x372f66d66c19ad9f70,0x372f66d66c19ad9f72,0x372f66d66c19ad9f78,0x372f66d66c19ad9f80,0x372f66d66c19ad9f81,0x372f66d66c19ad9f82,0x372f66d66c19ad9f83,0x379d7e390794e46978,0x37ef9c7b4c7b8d27b4,0x37ef9c7b4c7b8d27bb,0x37ef9c7b4c7b8d27bc,0x37ef9c7b4c7b8d27c4,0x3999abfcedd09a3f38,0x3999abfcedd09a3f39,0x3b1f490a6c622f1e98,0x3d35d8f94472dfb4a2]) (.p [0x3d35d8f94472dfb4a6,0x3d35d8f94472dfb4a8,0x3d35d8f94472dfb4b8,0x3d35d8f94472dfb4b9,0x3ddd7e05e67ebdccc0,0x3ddd7e05e67ebdccc2,0x3f6b5e661703c856fc,0x3f6b5e661703c856fd,0x419b1372a80091cfe3,0x419b1372a80091cfea,0x419b1372a80091cfec,0x419b1372a80091cfed,0x419b1372a80091cfee,0x419b1372a80091cff7,0x4557c1ec39ac594ebd,0x4557c1ec39ac594ec6])) (.b 512 (.p [0x45b2a27d26dfd104cf,0x45b2a27d26dfd104d0,0x45b2a27d26dfd104d8,0x468be346a2411e02d0,0x4805ce57c0486149db,0x4805ce57c0486149df,0x4a13cf3b80f6a62d9d,0x4a13cf3b80f6a62da3,0x4ed1bea06e1c08b8f3,0x4ed1bea06e1c08b8f5,0x4f71ffa3fd52b9a3e8,0x4f71ffa3fd52b9a3ee,0x4f71ffa3fd52b9a3ef,0x4f7a66db190b52ef23,0x4f7a66db190b52ef24,0x4f7a66db190b52ef29]) (.b 528 (.p [0x4f7a66db190b52ef2b,0x4f7a66db190b52ef2d,0x4f7a66db190b52ef33,0x4fe44592f07a74d064,0x4fe44592f07a74d067,0x4fe44592f07a74d06f,0x53f87dfff6b08d2044,0x53f87dfff6b08d204f,0x576cc6197d4ebccfae,0x59e12f978e93adae37,0x59e12f978e93adae39,0x5b1a3c6e14ded49d6d,0x5b1a3c6e14ded49d75,0x5b1a3c6e14ded49d77,0x5b1a3c6e14ded49d81,0x5db3e7637d74643dea]) (.p [0x5db3e7637d74643ded,0x5db3e7637d74643df6,0x5e54f160d23c893699,0x6021b0f75b563ad5b0,0x6021b0f75b563ad5b1,0x63b15ae6fe106d6d60,0x63b15ae6fe106d6d61,0x68155a43676e002c70])))))))

private def rows := OMA.PageTree245212.get (.b 912 (.b 448 (.b 224 (.b 112 (.b 48 (.b 16 (.p [0x1f105c0d85c0085c0085c0401003020000,0x6a14428d6f9d47351c19bf1525b0684b33c42922000581085c0285c030540a01c05300000,0x475ca1346b7e11d442873759762e92735d1800581085c0201c0385c1601c052b0000,0x2abe49af5eb7af51130581085c0285c0885c1601405100000,0x1fbdffef5e3af8ba45d3269d0a2a053b889ae63cbe71915f3ea9e2ee69d1c16e470667077c8e08e4e8d6f3f2fe15e20cf40d6254afcb7757e7c461fabc02be77fd0a49f6ffe99e1509bcfaac6618813cd382782168bb108cf7153e908a383a0581085c0285c0885c1601c06b40000,0xd0581085c0285c0885c1601c05010002,0x60581085c0285c0385c1601c05010004,0x1503105c0d85c0085c0085c0401c05050006,0x9535980d85c0085c0085c0101c03030008,0x1e200106c0d85c0085c0000c0104c09080000,0x174706204f9a0aa1688521cea403a8e6d23df991c1d423e0e852789e2403511c0581085c0185c0200c020a414490000,0x408791eeb4c609780d4dc0581085c010140200c0285c2a160000,0x3746e0c11188f87caf508bb9c10853e647066f827cc900c1035a3bad37ba3706fc4447c408a22ebfa8e2d1c197f39be2470696ae90e41822315f8d33798da37157470590a7cc7066f83a7c9111cddfc935fb7f27ec473974c830581085c0185c0600c0285c2ab80000,0x60581085c0185c0200c0285c2a010002,0x2d03106c0d85c0085c0000c0185c14050004,0x4e55980d85c0085c0000c0185c08030006]) (.b 32 (.p [0x3dbc058108480100c010240404408020000,0xc46bf04310ed6fdada850751adeba163c4a73c4834e4add497a92c96f7a42241290994058108480185c040240402c084e0000,0x27ab4620e9f8216dcd8c41d3f042da847d481728758e2da17b497a92f52ea558b54310a01ed69325089be5cbefa5bada904c4292dcbefa5ba5bf9d4807521ae858f12099285210e643058108480185c04024040440c9f0000,0xd058108480185c040240404408010002,0x191c0581085c0085c000240404408040004,0x3fdffd320a9e54006d1ea45ee11122cf2e009bf089177ca2143e5e5adc0581085c000040085c0a04408410000,0x6c0fb0d33c988e99319052bc59d4af10699fba6395fae67f6f15d83d896812dfdfcf6fb108cc98e985b10eee332876f78cabf99cc71846b058100040085c0285c0a044086a0000,0x3bab6a0529569b1883cac85250b0842acba902a40a9021cb4bb44f51a854d6b56097a01aeb46fcc2ad2ad6d428b10a17b5a3bad262d74306b4947df6f340581085c0285c020540a02c088c0000,0x4483c22241517fe850739cac01347f0bf8057c8311d53f930f59a62acf80581085c020140285c1602c08400000,0x134717054b2d69a4cfd5904f0f340e254afcb6eb2288916792c66d428310b33c9a8399c13c10b1c5264c5775d31be3fc2bdfa42fbbc340af7fbab4d0c7833d06dd6567a01895e2c88c3a0581085c0285c0685c1602c08990000,0x60581085c0285c0285c1602c08010002,0x90581085c0285c0285c0a02c08010004,0x703f9e5cc9a026b18038291dab7258c27bdf8da28558a5d402d2ad0864c19ba4774c10c4b857bf405f4b7bf6b490581085c0285c0285c0a0440c640000,0xd0581085c0285c0285c0a04408010002,0x30581085c0085c0285c0a04408010008,0x60581085c0085c0085c0a0440801000a]) (.p [0x90581085c0085c0085c040440801000c,0x21e3dd9bc1d8d6e501b88c8888fd66f0763ba98c09bf08114ea6440391dadc0581085c00004000240485c123e0000,0xff848de2f81a26bae7fc3ffe18418c111a5b0608caeb3e2719fdbc46b058100040085c020240485c12330000,0x32c4d1f149452f6a2bd6dd6dc582b4218b14c0be968f7b497a968d3e814b613542c90642da945b91c1d421ecaa38bd053d14b66a210ab1c59310a01ae85a4a3e06b40581085c0285c020240409412960000,0x2c49237a7f15e341f04515ef78d1c67a860cd4219b6ff822bc7921df1dc7bcac07a3c23f59bc1dcec612fc0146f93f23b3e2660581085c0285c020240485c265d0000,0xd0581085c0285c020240485c12010002,0x30581085c0085c020240485c12010004,0x60581085c0085c000240485c12010006,0x1f3027f486f3ea7d2bf401abeddfb8b16adde29e462c39bc2be40f1ac0f1a8df973a0878e4f95e03493c051bd54646ff67c29e5ae739187243ad66ef1701a0b30addebad766fe0996327ff03915b934c587acfbd32560cd4eb9066af8c8c0581085c000040085c0a85c12af0000,0x1cd660d013584858e15f05bbf818340963096217a476314c16d6f7e1669a091bc582f3df9f38c94af12ca1bdfd0f4757ede3223de30581085c0085c0285c0a85c12670000,0x60581085c0085c0085c0a85c12010002,0x90581085c0085c0085c0485c12010004,0x6106c0d85c0085c0085c0485c0802000c,0x4215658396800442b134b312efeb0a5688500d75a31079421873a168c41e5683a814a26fdadb484a73c483248e4c5b1880273108558f13c4806a200912011641c85c0085c020440804408970000,0x21469e0b46235f99669e2393968e4a4220010a41c85c0285c0609c1302c082c0000,0x6d924e64db9304e8e2a072746b7c955eb5af50c29bce906a6e69f16f91c199c19dc447046691130a01c85c0285c0685c2802408500000]))) (.b 80 (.b 64 (.p [0x6cc240e4e81a927ab5af5585379d20d4d3269f3debe4e0cce0cee2238bdc425a072b807935af916f7ff857bf4692357ed55c52649cd6f1bd7ceeab19a744d7511e6382a0ea14999c13cd250b45264c577590561120f4939ae8ca60a01c85c0285c0685c2802c0ab60000,0x610a41c85c0285c0685c2802c08020002,0x51131601c85c0085c0285c1202c08050004,0x1fffc9d6295e9006a578814f0889167a77a462c448b3d3bd327162d8c4013395940a81c85c000140285c120440c480000,0x3621199e8c2ab88c229733c0f6211dd645b108eeabb0051c96fcdc8451cb0a81c0040085c0685c120440c410000,0x266be91f52f102515eb6ee9580a26396b45885004cd68842ac310795a6430eb4c861f4ac510841c7f00285c06094120440c530000,0xc41d1e6cb428223e242ca55231075a4223990310a63c425a140a8247d80285c07094120380c3e0000,0x1a8121589ad3cf328b73f31c59fc1f4316214096f4ac5a72c61883cac2d5958e65a7885160885626215949591c3ca15b1ecd32160a8247d80285c07094120440f7a0000,0x19c10a8227f00285c06094120440c040002,0x180a81c85c0285c06094120440c020004,0x5c2bc432e403e6790312a57ede67a322316e9df11d290792c62c510841c85c0285c0685c260440c360000,0xfbfc3243c992bcc96a224598c0099caca2c0a82485c020340685c260440c280000,0x9931cb2b0a8240140285c0e85c260380c090000,0xfe4c621751e69ce09e08649efa5bdea46204f34e09e2a48dc3bfbf884b340a82485c0685c0e134260380c3e0000,0x4a7e29492f8f323ee2a591d064acf4090d7064d6be4517493349827cf7af3adf45dc1df2393273d561a3e72424dd9e984f0d61122aee1c9254d75b1660a82485c0685c0e85c4e0380c7e0000,0x90a82485c0685c0e85c260380c010002]) (.p [0x30a82485c0285c0e85c260380c010004,0x1f8901f5246ee9584d0258d046fefcfa43b799e8c830a82485c0285c0e85c260440f2e0000,0xd0a82485c0285c0e85c260440c010002,0x510a82285c0285c0685c260440c020008,0x20a81c85c0285c0685c260440c01000a,0x90a81c85c0285c0685c120440c01000c,0x30a81c85c0085c0685c120440c010012,0x510ac1c85c0085c0285c120440c020014,0x108540022146e3ad19842851ecd321137c8c42ccf32c134884b0421563d2420051201602e85c0185c060b4160440c570000,0x22453efc1413734885060c9535d1801602e85c010340685c2e0440c250000,0x548149bbd78e9c644aa2e9157fa009d589d0b2c4cd5af943a09b36ae8425e177102914c0610a151e1fd5e0ee20011205def0f02e85c0185c0e85c2e0380c710000,0x1b108cd710032b0f02e00c0185c0e85c2e0440f0f0000,0x30aa244c5baadf4e0c38b551e0862f0ba27dcd7af39d201505a7885160a97a04893a1922a7b57a337711ab0aa0cc21190a2140d616f5fe5f8d251f6ffb885373b340f02e85c0485c0e1742e0440f8f0000,0x6e29bb9349a0976ae6464cdd887413e326b5e38517482a6ecc2defd27edf5722b3207d88743e9bf8b5d7275abf885164bf80a784fabbdd6a721e498b12bc660f02e85c0485c0e85c5e0440f810000,0x90f02e85c0485c0e85c2e0440f010002,0x30f02e85c0185c0e85c2e0440f010004])) (.b 96 (.p [0xd0f02e85c0185c0e85c2e0440c010006,0xaa6f2f5ea94d5c303b884b4013b84f649b6f5e75c9889838e2518b1508532c6f3a41ae0c2dd56fbb884baff0677100488815700120011603d85c0185c0e85c2e0440c7f0000,0x21602e85c0185c0e85c2e0440c010002,0x61602e85c0185c0685c2e0440c01000a,0x150311602c85c0085c0285c120440c05000c,0x21601c85c0085c0285c120440c01000e,0x611641c85c0085c0285c1204408020024,0xa135981c85c0085c0085c040440804002a,0x81357b4801eea63dd8980120c1c85c0000c010240485c121b0000,0x62000b81c7e801024040240509412070000,0x1b428fe0a85a0c5469582d1881ea168842cac8e6c6204219987425b8710855b690906c6235f9962429285920910881c7e80185c0a0240509412700000,0x129565920022da19b627f05894a3a8e6e4481fed6188163c492f56210a4a58010b8237e80185c0a02405094124f0000,0x20b81c7e80185c0a0240509412010002,0xd940b81c85c0085c040240409412040004,0x1f1043b3783b1a46f184ff8900d4d00b81c85c01024040140485c261d0000,0x23789246f4bbfa057bfbe7cd160df8887e14bdd5fbb7a483574878ddf04f8a71205b9334408a7cac506088c13e1f069568c41d7a7c91125b5d6fc5be09f04aa1d096e610881c85c0185c0a0140485c26850000]) (.p [0x987904dce88a0820a0e089c40920dd9a1ff90997041d7c4223d8cd160df8887c4f62424e42613f57ea734076240223833b124a9210b82385c0185c0a0140485c267a0000,0x20b81c85c0185c0a0140485c26010002,0x6def0b81c85c0085c040140485c26020004,0xdfaf62239ad8304657c976bab0b81c0040085c040240685c26190000,0xff12425ec6289a23d533783b18711eabaf6688f9406dd4c61ffc1d8c25f821d3e20f68de4e580b81c85c02024040240685c264d0000,0xd0a5fbe9601da64e6860a10881c85c0285c0a0240685c26190000,0x1881a47c10b0bdc8911209887647b198620727c5be4f37825bf91642cac8036fdf4b756d4923e6d47169295b62ce680b40b8247dc0285c0a01c06134266f0000,0x2fdf4b123d8cd58a005b73c04868e8db52703e8545aa8f8bdf2061d688775137e16adeb8c160b8247dc0285c0a02408134264e0000,0x4c0b82485c0285c0a0240613426020002,0x2378b7bbcdefff34c8de241b7f7628d1ff1253c0a9e9ae22cd06abdfdf62d91ec665d27eafd760afa0b982c4a6fefb16c8f63347f85837e23d88c510c9ef988abff83b18b90b82485c0285c0a0240685c4e820000,0x610b82385c0285c0a0240685c26020002,0x20b81c85c0285c0a0240685c26010006,0x60b81c85c0285c040240685c26010008,0x30b81c85c0085c040240685c2601000a,0x90b81c85c0085c040240485c2601000c,0xd0b81c85c0085c040240485c12010012])))) (.b 160 (.b 128 (.p [0x842a3e6401bb125881d11a3e69be1fc1c3eef91d1d9bdf330b21568744df22c85d880043835ce2001a13c4806a200204348500085c0602406144286c0000,0x23d5758002b1013946f5941203484c00034060240685c52190000,0x304460b120340040085c0e0240685c52090000,0x4c132ddbd60820a0e08ffac22401b39a1fe242659bd5d693e2820cdee83760098f520822b7ae838b388068e0df888a4f6122289a48872f149fa8bf82fd760ec48149511cd1203484c0285c0e01c0685c52960000,0x374b13f54fd5fe87d9a2d54fd5fa9c00183cdf3a815fd0049cd9cc18e25381d19332a97894ae9246bf13f61fb878dfe46f9f19a2f64ff84df81203484c0285c0e0240826852710000,0x7343fc484c1fc7ccb820c5837e222939826c451349ff10210beb6d746dc1341afff843a1203484c0285c0e0240885c9b4e0000,0xd1203484c0285c0e0240885c52010002,0x91203484c0285c0e0240685c52010004,0x31203484c0085c0e0240685c52010006,0x341128348500085c060240685c52030008,0x111e08bb0e2c104141c59c5841d892d40a8de25203aba5ddbd62c408a22822041044f8a2332c1f76021373908a09a27eafd4f8047b4205d892586f7aba11c19d8902a0012044b8500085c060240685c52a00000,0x2204348500085c060240685c52010002,0x30012042f85c0085c040240485c1206000c,0x2ef120c1c85c0085c040240485c1202000e,0x9b5981c85c0085c000240485c12030026,0x6191701addf85b6b18337f12c77a554cb6340082eb42141381c81c000040085c0a0a414340000]) (.b 144 (.p [0x1f3404503d1820b13c429fe63164c546fc02c95033538c881e8c1d30c8b6ef12c62c99fc02cfe7934c1b77e03760af799f22b1eb0c93adde0d760888f53eb779b94029f4128c06cfa37a9d6344a8810604826d9bd62cde2a0c6a450ce56801ee691c910a41c818000040085c0a85c2aca0000,0x6f39a77c8e67b66f588ddf3b14de665f5b9df3faa50609f412b0133e687fa10888b04fbd7e2cfe2a2cd6efc02cbb778a791922e9de322b08114fb3301b93404475c3264af1d99801a9805a141382a818000040085c0a85c2a9b0000,0x181381c81c000040085c0a85c2a020002,0x4e05981c85c000040085c0a85c12040004,0xda005b1f64e58dc0d01c7ec00014020540a09412130000,0xeef0d01c0040085c060540a09412010000,0x4c98a40215b50c15ad16214092e8f89e3107942183586205b508fa904ac485162da27a8121539a16992e860f4ac5a725acd3340901c7ec0285c060540a06012790000,0x7f3eb0903b44c72d68b01a005b2a182bda17968b01a005b2d9a660901c7ec0285c060540a09419400000,0xd0901c7ec0285c060540a09412010002,0x5b90008b556d0c26f9108111c3ac21022412921200d0287d00285c070340a06012360000,0x6d0227b2b4068129108595a298347e50b12956d5272633516815efd02953542d2549295659228215898c42ecad942c4a559649c98b128da45a10060d0287d00285c070540e060128f0000,0x69c0d0287d40285c060540a06012030002,0xd86b456b47ec56f6851c8f58ac1f4c0d0287d402034060540a094191f0000,0xda1595fc0125fe8430e210a85a210a843160d6e52f40a54d695492b20110aca37e08665b58588891120dd527ca5e814ac210a84306956250c0d0287d40285c0e0340a09419870000,0xde01da663ac5002127b42b24b10227a84307b4cd1983589430d0287d40285c0e0540e094193b0000,0x90d0287d40285c0e0540a09419010002]) (.p [0x60d0287d40285c060540a09419010004,0x2c10d0257ec0285c060540a09412030006,0x20d01c7ec0285c060540a0941201000a,0x30d01c7ec0085c060540a0941201000e,0x340d01c85c0085c020540a09412020010,0xeaf0d01c004000140285c1609412010000,0x12bcc69e34f6ffe14f4c59a13400b6cb18b968248b2a0623acf088fa28ab1927053d2b034af34cd0901c720020140285c1609412590000,0xbd240fa914f4c5af3400a72d4448b3d35b9093414f4ac23a9feaf277a477350448b3d2b0ab18b968223a9feaf12c6b723846b08ea7dfec937a6bad87c220fa50a49362809cd6aa2c10d025720020140285c16094129e0000,0x20d01c720020140285c1609412010002,0xc0d01c85c000140285c1609412020004,0x4a86f5dd55d8872d9ccf47257a0d399e8cea9d884667a7e2bb10edf75947c44f9b1164707ad7e7a2ab8834e66331cb22b3eb0d01c0040085c0685c1609412600000,0x257a48f9eb2cf59302bd01358485e692f7782a5159a4d01ab18d34b660b67c834093fde6b72d262da0496b18b34d050901c85c0285c0685c1609412660000,0x1dde2408c4a860af49f4cd1da04867eef34e49d002126b45b4742a10c1e4ba66ac728cc32d23fa6606b128d2b340d02885c0285c060b41606012650000,0x26901d2c6e959a68a1340180cfc267869ccf451e0d1f118a486e4420a7a6bcd002c22459e99fe8148e11ac2ac660d02885c0285c0685c2e060126c0000,0x90d02885c0285c0685c1606012010002,0x1b9118b2c66a04620c7a5553406a3e2c6cd6e5a4f4680109359963f969319834b58c59a6930d02885c0285c0685c1609419540000]))) (.b 192 (.b 176 (.p [0x610d02585c0285c0685c1609412020002,0x20d01c85c0285c0685c1609412010006,0x30d01c85c0085c0685c1609412010008,0x60d01c85c0085c0285c160941201000a,0x90d01c85c0085c0285c0a09412010010,0x34088f55cf88b0e0927cea12f63144d11ea99bc1eea63345a37ca9f98b10c42dc4644440821a4b37eee5258d368de6d317bd8c0d01c85c00014020540a85c26670000,0x1c406c18980ff012eb1025cf8c88b30b180aa5f8d025848069635680d002c07f600b522ada1596ba382211a6e7fd0864c1af699a3b4096250c158c37d8b5ad19825bd8c3e99a2c4b9f580377203938830c578d2e08e888e7bac2a2f89cfcd3d26bacf830d01c85c0085c060540a85c26e20000,0x60d01c85c0085c020540a85c26010002,0xbe634602dc8d02580cb5103c0cbbf60d5891ab30a2208a9ef462c11066334d26fcc2b7782d06920c9bbb6b19336b4812c4a77df191878f2e46a7bdd7cfbf256693166a9ef5002eb9018c5cdd72758c8cdb0d01c85c0085c0285c1685c26ae0000,0x90d01c85c0085c0285c0a85c26010002,0x610e41c85c0085c0285c0a85c12020006,0x2f880d120c3a0040085c0705c0b09414080000,0x4ac800442165616aca517aba11cd8842cacb1545ec6004c42c406ae8142043a7a00285c0705c0b068144b0000,0x2d595960ce9c116ed89fc3ca26f9108558f120917abad8716908900c6001eb10049c1383a7a00285c0703c0b0941b500000,0x34400b67f3a2141a01383a7a00203c0705c100941b160000,0x7778810ef82d11ea6e5eba1650864c152f10295cd0c26f911f96e5e3372f5d0a35e560b45ab2b1e241abda1241310c0485e5665b5cd108595a647c4c51a62afb23cca0055e66febb23e1661383a7a00285c1005c100941b9f0000]) (.p [0x61383a7a00285c0705c100941b010002,0x911403a7a00285c0705c0b0941b020004,0x85abf8a12147a200db822dce5effa0ae65c3e8f2218b57484855ae880244dc38c4830842cac2c95120917aba120d141204517a00285c0705c0b0941b720000,0x22043a7a00285c0705c0b0941b010002,0x2c120c3a7a80285c0705c0b09414030008,0x4205983a85c0085c0305c0b0941205000a,0x8914fbf101d620264e492122d4f4ac111228fb7e09dadc8c55bda00592ed2095838222451f6f000466f4d740a0e72301c03a85c0001c0385c1809412700000,0x618853722001c03a7a401044080c418060120f0000,0x4285474b730b556e2048c8e6cf10960a97a048e8667f05c50278219b10a34f32c1996dff711c934ecc210ab0b111222392b074871571002dc1203a7a40185c120c41805012860000,0x2978814ae68668a31d68cca2dd141e56996eb341beff7782abf9025bd87bc962da17b4c558ac61085958421647b34cb442165658b28b16d13eef10242b28842cad0f2856f680169cb1a6431203a7a40185c120c41806015ac0000,0x611303a7a40185c120c41806012020002,0x42156e214d96800447bd79d0a8e860b45aab48442871085958f1086b12403d27dcc06400a9fa0011c04d7a40185c120c41806012630000,0x21c03a7a40185c120c41806012010002,0x6dc1c03a85c0085c080c41806012030006,0x1b108cf7154190e7eb1c03a0040085c0885c3206012120000,0x4d5f2577977cb5789b229f7e0a09bc920d4141ca950243eff0c90f228cfb79eb182216eb5b04916d5fb6451f6f0e4ce466581c03a85c020440885c3206012610000])) (.b 208 (.p [0x5f7dc54b7f41dc356fbbeee6e710a34efeba330850ab710a647164c42901e1e6d4304487ab16ebf478b238bdc4258a602eb93f27d5896564ac6ec1aeef3e0c1203a85c0285c121943205012860000,0x6e0b899f3fe7d71d11d15e7d4e1206fe852357e49756a2bd7ad164dd5caaf24c96af7af9021bf694a40963762119831203a85c0285c1285c6605012590000,0x91203a85c0285c1285c3205012010002,0x95e2593f14a5b3a4804ffb7ac26812c6de67a0c91203a85c0285c1285c32060152a0000,0x611303a85c0285c1285c3206012020002,0xb755b8803000b755855066173b88847108547ca4c178519c4f805da00aa57100211c1c04e8540285c121943205012580000,0x26b5f228af5f334542145c9838e251dc429902ec0064ee603742936c26b5e38192746b7e15ebe66ae4c1c7128eac66e38947710a638b149ad7c82b07cb401223aae98f62f49903f2ef3694d746e61c04e8540285c1285c6605012a90000,0x4c1c04e8580285c1285c3205012020002,0x30cdc5188e0ebf884b4013ab16eac5a2f562dd5a11c98ab1581c04e78802094121943206015390000,0x3701ee2a3eaa3209b8a96f9f19847eef15a3e08a37469d0cd362142a3cd3cd5c31bac93d6a49afbee2a5bfa68851a743343e53b831c04e7880285c2619432060156c0000,0x341c04e8580285c121943206015020002,0x173006e2a3eb22b2331afe0291ebf4f8533bc712886effb8a9471c9bf2e7c8cd262e4d6be418b3f07f8a907591da962492443abab5263d8b268223aaee1c9953bac97f014c600b694cef56a4f2c9ab250fe4661c04e8580285c1285c6606015af0000,0x91c04e8580285c1285c3206015010002,0x2c11c04d85c0285c1285c3206012030006,0x21c03a85c0285c1285c320601201000a,0x61c03a85c0285c0885c3206012010010]) (.p [0x31c03a85c0085c0885c3206012010012,0x91c03a85c0085c0885c1806012010014,0x3e92eef3eb1c03a0040085c080c41809419070000,0xac1ec19400a2b12ac1c1e188524428b1456b7422b168bede972d266581c03a7b002044080c41809419430000,0x34016a498e374acd04bd002c6a1dcac89ee564a2160d95a4c58850252bccf72562ca1739604326611303a7b00285c120c418094195f0000,0x44ac23742cafa439858889111cd9bd22141ac5b8220da161029584216569b10f7d6f9a165616acadb4247264a15bd3265341c04e7800285c120801807419780000,0x36891448e5ce86610b6862a16569b10a151fbbcf06616e7e6ee1895ac9393250c42899d24a7800920d95a1e50adecbdc428bdc5b0f63aac62c61c04e7800285c120c42107419830000,0x4c1c04e7840285c120c41807419020002,0x144d4bc4087a241fe334334588502522b19b6859448a10ef82d1397ee7428ef8218b17440862862a91433491c04e7840285c120c4180941e610000,0x2c11c04d7b00285c120c41809419030002,0x21c03a7b00285c120c41809419010006,0x61c03a7b00285c080c41809419010008,0xc1c03a85c0085c080c4180941902000a,0xbe063ebde2bb108ce5f9a0e8c8e99f31e7a0d35afbf7d748e8c88a5a7d299e290ffb35323ab1c03a0040085c0885c3209419460000,0x121248a66f26eb0ff7c7bc62c835129374e2b1682216efd730ac8c59167e5efcdcd262c373181967aa3490dc8b00a6346a3d63262c581c03a85c020440885c3209419750000,0x6802eb935fc40a49d5a31ab41a80614cecf5bfaecadda3710240a075135ce8669324e92005907dc1d5a300adbd58b45eac5bafef833298e4c558c26906ad6ead04cb158d262c5ae633f032efe400b651c03a85c0285c1285c3209419ba0000]))))) (.b 336 (.b 272 (.b 240 (.p [0x61c03a85c0285c0885c3209419010002,0x31c03a85c0085c0885c3209419010004,0x91c03a85c0085c0885c1809419010006,0xd1c03a85c0085c0885c1809412010012,0x511d43a85c0085c0385c180941202002e,0x260bd7aa8e934541c554850d2214378768300085c0e85c2d05413220000,0xb556e2048c2822dd56fb7f02862e025d02985cee2048910e6c5cee2210c500af101aba11c3787682c0085c0e1742e06416580000,0x1ba505d24cc7c299d85f38c89545d22c9ab93071c5b824ffe95b3911c8cdc7056b86d5d0717518223aaee004ed2914af553762e649c12787682c0085c0e85c5e06416740000,0xa3bebd7aa8e3e94a60093f3df54728b5ebad933451dd56b86d5d0258c5c0357420555379d20d501ab80091c3789f82c0085c0e85c5e06416600000,0x23787682c0085c0e85c5e06416010002,0x54378768300085c0e85c2d06416030004,0x2414598768340085c0685c1806413050006,0x2375d0148350149a0020fbeeb53917bbf1c89b19c8a336410d4a49884af0e0ba2001a801353949459876834000340685c180941a5e0000,0xbe00b3dc760040085c0e0c4180941a060000,0x81d142df82b9973489fccbfb78cc0ce02e9a07fd2801797e8904ac6034d8b556e80cb06022d547469985c8a244145a7f1ff710a6e4d0c2d5918003a2001367feae848054989e087eb007503412a0767600285c0e0c4180941ab70000,0x7a84851e80196b2400421462fd003308428f4401a4c7bbefed370744717b88506830b54728c834e21003dca97600285c0e0c4180941a690000]) (.b 256 (.p [0x183dc767680285c0e0c4180941a020002,0x16c598768340085c0e0c4180941a030004,0xbe20f3087e004000740e85c320941a050000,0x11d5764875dc38a7c3003abcde77014835099329520889040d24924eb91f7e7578f6d5e75dc05268a4ec90f3d29722f20885fe2fc5ad5f86ae4723059262a12bcda00596ead0850fb481fe0e4c3087e64c020740e85c320781aa90000,0xfe02916f339ea77dd62c1062ffdc64cd2492f9a094df914afc2b3cbc562b1317f8e30d17e012a068a2b15893087e64c020740e85c320941f5a0000,0xd3087e64c020740e85c320941a010002,0xc3087e828000740e85c320941a020004,0x6eb3087e0040085c1e194320781a020000,0x1afceafff5b7f154bad59f56f9f1d5a51873a47a04a2a952d7e5fe27400bcbf085164c25c7e74c020f41e194320781a410000,0x7ff5d04c46f3d42d7ac83349141bdc54aa32320cc0d1f13ee688113123a19a1b41d0cc0d48842a3ccb24e088113d4743156175fe0c925c7e74c0285c3e194320781a790000,0x512607e74c0285c1e194320781a020002,0x428542d7f77e06419a0889dc5090b5efeaa320c5522df7755ae1b575b0e210a8f32c93822142a3a1dc4258aa4de910a2c593ffa52f023abf23d40dd800c13089974c0285c1e194320781a890000,0x23087e74c0285c1e194320781a010002,0xc3087e8240085c1e194320781a020006,0x37001629ae84be3833ee0c5551748abbfeb88099d5f835632314523349150065517d26ac6087148c553b10e833087e8240085c1e85c660781a640000,0x4c3087e8280085c1e85c320781a020002]) (.p [0x6eb3087e0040085c1e194320941f020000,0xd306ad7feae8c00cccf8acf4093fdd8bfae8c998f12607e7540285c1e194320941f2b0000,0xcccf89fba513f73ac66927eeb6fe2bbfab7cf8a3f31590aabe3b88527a680e880151c93f7c3b0f4a971087bc56164c3089b738020f41e194320941f5d0000,0x14bc40afbd71133f751a8c59a2cf4094eec62fe3d5e2c75fe28c83308513d4782b8afe0648a0f30bae2dcbfc90ee864188fac93089b7380285c3e194320941f660000,0x341308997540285c1e194320941f030002,0x23087e7540285c1e194320941f010004,0xc3087e8280085c1e194320941f020006,0x7e2695e2052680755ba7a67ee85231668a2294925810e2919a2cf40923087e8280085c1e85c660941f420000,0x93087e8280085c1e85c320941f010002,0xd3087e8280085c1e85c320941a01000a,0x341310768340085c0e85c320941a030014,0xffd009da0132001f7ff7efdc35722e76896941c1523f12bf217f8999a8f4e467a70e439f4429ba214800278127c004d0578809480598c5800000740e85c320941a780000,0xb8a08b755baa1ee000e1800b755855c0cd046f3d5855062a916eab755ae01aba047d854078ad701ee40f1348830842a3cdbdc4003868254ae004efb89203e0c57f40085c1e1f43e0781a950000,0xb93375d0e9bae4c1c7128c998e2ae551a18b5f31c616cc2a86eba1d113071c4a32561754aa23aa9e2ae20ca5541748ab971b5c3472e50a456b80f726d7abf8843393262c2e914145c5232a4663e0c57f40085c1e85c7e0781aa90000,0x4c3e0c57fc0085c1e85c3e0781a020002,0x9ff9c54309470c002f9c6451748b0d261e49838e254a3a40055c00900504f97fc0085c1e85c3e0781a490000]))) (.b 304 (.b 288 (.p [0xc94598c58000085c1e85c320781a040002,0xbacb598c50040085c1e194320941f040000,0xee5f9bb57125a0c7ea5710866eafc79f13d6097636bd2e07ad9343b06bbbf01e9703c56b80f726d7e9dc542ba2a74dc1d11c9348852704c3f4c570c020f41e194320941f730000,0x40a0500783b1716e2142a1ff400556154d040a27a87f7e971f19062ac2fb9a21428c4fc25df0d590033410281421a197f81912ff1418aa442854783a80158b62c93f4c570c0285c3e194320941f9b0000,0x343f4c57140285c1e194320941f020002,0x4397e0e1e1c1d47d4d86a0895042e180207ba0052f4009fa80480d042854782b832573cd10851e801ab67f8839ba006dbcb80740a6197df35bed9fe4bf8d6904314598fe7140285c1e194320941f9b0000,0x2598c57140285c1e194320941f010002,0xc598c58000085c1e194320941f020006,0x8f3f4c5004000f41e85c660941f030000,0x78bfe9b672294c7847fe70f66a3b5c44e9c886ae6fd1f353a002b29717230f19eafd862ab194a394fdd2e20ca442bc425927eea5f89619e522b131523f4c518c020f41e2d0660841f790000,0x3f7ae90eb8674323eafc31d5cd4bda94299919335257881483b5f650de2557acaaf5b6aaf3d6714c89f19a0d23f4c518c020f41e2d06609422510000,0x2c3f4c5638020f41e2d0660941f020002,0x24d22e473f4c5638020f41e85cb50941f0a0000,0x93f4c5638020f41e85c660941f010002,0xc3f4c57f8000f41e85c660941f020006,0xc7125db8906550ea33f4c57f80085c3e85c660941f140000]) (.p [0x343f4c58000085c1e85c660941f020002,0xbe0f598fe004000f41e85c660941f040000,0x1fba5c33a1542e768853b2669eb43572386fd21b297009912c450fe178020f41e2d06609420360000,0xa6539a29a4114d209cd263483c2a05f6beb7956c5e9349929b0ce653d6825ebbc62f4879067ee956d690e4c3f74a307a4d3645d9a7eea723f88992414d6829de5420d0059915178020f41e2d066094209b0000,0x90598fe620020f41e2d0660941f030002,0x24d22ec598fe620020f41e85cb50841f090000,0x2e9164450fe620020f41e85cb509422080000,0x2424dd4aeea6bbf0a693cbc83adeb5126ea2453e1a9a1260930498245cb09304920498245aeea7ba5e38ab5dc382a2e3fba50ebb87270c5090403498c95f969de459915600020a01e85cb509422960000,0x1a449d1520c020f4293d4b509422030000,0x1a44fd281e4020f4293d4b509422030000,0x1a4519401b8020f4293d4b509423030000,0x1a452947198020f4293d4b509423030000,0x1a45314b178020f4293d4b509423030000,0x1a45394d160020f4293d4b509423030000,0x7f5994f148020f4293d4b508c23010000,0x1a45414f148020f4293d4b509424030000])) (.b 320 (.p [0x1a454951134020f4293d4b509424030000,0x1a455153124020f4293d4b509424030000,0x1a455955114020f4293d4b509424030000,0x1a456157104020f4293d4b509424030000,0x1a4569590f8020f4293d4b509424030000,0x1a45715b0ec020f4293d4b509424030000,0x1a45795d0e4020f4293d4b509424030000,0x1a45815f0d8020f4293d4b509424030000,0x1a4589610d0020f4293d4b509424030000,0x1a4591630c8020f4293d4b509424030000,0x29d0bc29a91f75b5ce0e5173514499144d6f12c98a3d5df8d5de3d5df8d5df8d20f577e3577e3498d263483d5df8d5df8d5df8d5df8d263493b33e9f75bd0bda26dc6dc6dc6dc25a351accec572b35de4bf8e64d3498d263498d263498599650c8020f4293d4b509424c00000,0x18599630d0020f4293d4b509424020002,0x18599610d8020f4293d4b509424020004,0x185995f0e4020f4293d4b509424020006,0x185995d0ec020f4293d4b509424020008,0x185995b0f8020f4293d4b50942402000a]) (.p [0x1859959104020f4293d4b50942402000c,0x1859957114020f4293d4b50942402000e,0x1859955124020f4293d4b509424020010,0x1859953134020f4293d4b509424020012,0x1859951148020f4293d4b509424020014,0x25994f148020f4293d4b509424010016,0x2c5994f160020f4293d4b509423020018,0x185994d178020f4293d4b50942302001a,0x185994b198020f4293d4b50942302001c,0x18599471b8020f4293d4b50942302001e,0x90599401e4020f4293d4b509422030020,0x185992820c020f4293d4b509422020022,0x1859915600020f4293d4b509422020024,0x1f5357bd7c9c98b332124832424d251268247d5dc38a7075fc429a2ae4595144e0a8a24f2f22c8b2424d25126896126093049824c12609304982494759915600020f42985cf609422910000,0x959915600020f42985cb509422010002,0x3459915620020f41e85cb509422020028])))) (.b 384 (.b 352 (.p [0x2598fe620020f41e85cb50942201002a,0xd598fe620020f41e85cb50941f01002c,0x9598fe620020f41e85c660941f01002e,0xc598fe7cc000f41e85c660941f020032,0x6eb598fe0040085c3e2d0660941f020000,0x18e25c00914c716e0cd956c598fe6e80285c3e2d0660841f1c0000,0xb3ba8c450fe6e80285c3e2d06609422070000,0x6e261b3345149c2cb926c1283b26682a05ca814c7f0aafade55b162e8f5bca929a2a10960a9460cfd36bd2adad3b167ee956d694a682a5183152ad9b8852412c599151b0021f43e2186609422940000,0x386c558d80717668a83e541c150555caaa0c55bca9298e0b27cb27062ade541c9cb054a3062a55b5a7668a956d690e68a0a9462599151b0021f43e2d08708c227c0000,0x1502e591449d151b0021f43e2d087094240c0000,0x1c5c1c2c6c9360941d9334128b820a63e2e033fafade55b178548f5bca9292085161e3b10f7a5198599281500214c3e26487094245d0000,0x14583f49804c82a0a6c553c2abeb7956cd26013206c9a28260386c599b0d8bb0678548f5bca929a0a8172c8a0c55bcab62f0a80f5bca929a2d057889e176775dd62599281500214c3e2d09a094249d0000,0x4c599281880214c3e2d08709424020002,0x2c8b95404fd28188021f4542b887094240b0000,0x1c362ac0a6c5362ade55b2668250d820a60c2517329b0d821c980717345062ade55b3455bca8382a0aab955418ab7952532ac5994015c021f45425487094247e0000,0x5511298e4c5149c0717354d8250760a9a0b22e59149c251727859724d8250760a9a0b22e591418ab79507054d059172c8a0a55994015c021f4542b896094247c0000]) (.b 368 (.p [0x4c59940188021f4542b88709424020002,0x13359928188021f4542d08709424020004,0x34599281b0021f43e2d08709424020006,0x2599151b0021f43e2d0870942401000a,0xd599151b0021f43e2d0870942201000c,0x4c599156ac021f43e2d0660942202000e,0xdcbe6872fc29fb0750a345c3479bb87270d41033cd5c31270517f03344a5eb03599156a80285c7e2186608c22430000,0x502814642461449d156a80285c7e2186609424130000,0x7753a9d351850502705181409c1460512a0a254144a828c0a2685037df835028c94c204604b0518599281fc023247e1d06609424650000,0xaaabbefd382813828c0a3028c0a2701c3629b140b503b26682a0d46098a14288a6350281141409c1408a0a04e0a04d40a0450512a0a254144d0a054b50294d582c8242599281fc023247e2187509424aa0000,0x4c59928670023247e2186609424020002,0x10232e4750231a8144c4851a08c08c08c089a0f0122757599286700285cca2186609424400000,0x34599286a80285c7e2186609424020002,0x2599156a80285c7e2186609424010006,0x2c599156ac0285c7e2186609422020008,0x502a8d4660049d156ac0285c7e2d087090220f0000]) (.p [0xa05659531a8c2828114144a828950512a0a254144a82818a929abac0c599286740285c7e2d08708822490000,0x14cbba705181408a0a04e0a04e0a04e0a3028c0a30289c0a6c558597241a04a0ec99a01a83608298f8ab7956c99a0a8172a05304c5c30b79502582854a3261859928200022fc7e25c8709023a30000,0x1502e59145093b200022f87e2c89808c230c0000,0x386c514d86ccaa708be600b9502996038a700e6176bb14d8ab7956c99a0a8172c8a0c55bcab64c599431bc022547e2c89808c23600000,0x3d7a99774dbef9141409c1408a0a04e0a04e0a3028c0a3028c0a32ddc4a1b0561286c1362816a0764cd05028c1a8c6c5037df835028db2668281460d4653599431bc022f8962c89808c23980000,0x3459943200022f87e2c89808c23020002,0xc2559928200022fc7e2c89809023040004,0x4c59928674022fc7e2c88709023020006,0x2850eea714e68a68b8595165459526a0a254144a8289a15028c8485992867402444c02c88709023420000,0x313599286740285c7e2d08709023030002,0x2c599286ac0285c7e2d0870902202000a,0x95599156ac0285c7e2d0870942202000c,0x9599156ac0285c7e2d0660942201000e,0x34599156e80285c3e2d06609422020018,0x2598fe6e80285c3e2d06609422010028,0xd598fe6e80285c3e2d0660941f01002a]))) (.b 416 (.b 400 (.p [0xc598fe7cc0085c3e2d0660941f02002c,0x1b82e5485f28a3266a8cca30450fe7cc0085c3e85cb50901f1b0000,0x13ff9993fe54ffc6a3ccffc6a7f267fe353f8b27fcebfa536a24d04ba455d20cc9a4953492a6931a4c49ff96bfa5ed44933fc75124cff1d44933ff2effb0eba49cb0916bbce459164848a096690609f9fc2e56cdc4293b157c4a148c59915798001f43e85cb50841fc80000,0xff599150040085c7e85cb50841f010000,0x6eb599150140285c7e3d4b50841f020000,0x1528c49d156b80685c7e3d4b50841f060000,0x140a1414599286780685c7e3d4b507c1f0b0000,0x183e20cf8ee7e467c419f1067c419f1067c419f1dcfcae212e7e575df8c59928678063247e3d4b508420320000,0x7ad4227a8468e5f3a8468e5f3a842a1cbe7508d170d078d03a8144f50a140a36cddc5a3450512a68b9a891020414582dd518599286780685cca34cb508420760000,0x1970a27170b85c2e0518146051826372fc397e5ab550e5f853f60ea10a872f9d423472fc341e340ea144d459d479a2e3fb8d0b3cd5d6062c16502599286780685cca3d4d4084207f0000,0x9599286780685cca3d4b508420010002,0x6599286780685c7e3d4b508420010004,0x2c599286b80685c7e3d4b50841f020006,0x2599156b80685c7e3d4b50841f010008,0xc599157980285c7e3d4b50841f02000a,0x59172ca049d157980285c7e85cf60841f0b0000]) (.p [0x9348a9459928770023247e85cf607c1f0a0000,0xff599280140285cca85cf607c1f010000,0x65d956c599287700685cca434f607c1f080000,0x4397e14f5c7508d1cbe750854397cea11a397e1a0f1a075089ea1cbe750854397cea1468b868dc681d47935166679a2ecabafe6a24dd44933fc753f933ff4e47f5326d449bb27f8ea24593fc75122c9fe3aba498ba6ba45eea64d156a78a295534164533f599287700685cca85d0e07c1fd50000,0x9599287700685cca85cf607c1f010002,0x3599287700285cca85cf607c1f010004,0x34599287740285c7e85cf607c1f020006,0x6e6c9a4512f83f27e4fc9f93f27e4fc9f93f27e4f9f064f2c93599287740285c7e85cf6084202d0000,0x2c599287980285c7e85cf60841f020002,0x2599157980285c7e85cf60841f01000a,0x9599157980285c7e85cb50841f01000c,0x3599157980085c7e85cb50841f010018,0x345991579c0085c3e85cb50841f02001a,0xff59915004003403e47cb509022010000,0xd20b3ba8cd0049d153c8023403e47cb5090220f0000,0x2e1b2b7953f599281e4021943e3a4b5088220c0000])) (.b 432 (.p [0x1a416764d144fd281e4021943e3a4b5090230d0000,0xf5fb27526bbf194ca2f6e994d59f6d1e4b4792d93e96c9f4b64fa5b27e4faf233498d263498d24a9a4953498d263498d263498599401bc021303e3a4b509023730000,0xc6cca68e5ca3f27e4fc9f93f27e4f9b3727c9cd263498d263492a69254d263498d263498d260e01c266cd0713360c4a4d4d05926418ab7956c5e90546c8a94c7059dd466045599401bc021944d3a4b509023a40000,0x34599401e4021943e3a4b509023020002,0x2599281e4021943e3a4b509023010004,0x2c59928288021943e3a4b509022020006,0xb22e59004fd28288023406639cb508c220c0000,0x183e20cf8833e3b9f93f27e4fc9f93f27ffc79545bb54d00530bb84d933451418ab7956cd260a8172a05304c55bcaa6b34599402580234066330b508c22690000,0x307cdced723b93e4534824c9a4114d208a6931a4c6931a4c6931a4c6907783e20cf8833e20cfc9f93f27e4fc9fff4ab3156f2ad9a4cd20b3b268a0a559940258023406639ccd08c22850000,0x4c59940288023406639cb508c22020002,0x2455992828802340663a4b509022030004,0x34599283a0023403e3a4b509022020006,0x32e5cb965451145139a0be9345c2e262e3498d263498d26164d20a5599283a0023403e47cea09022450000,0x4c599283c8023403e47cb509022020002,0x185991579c023403e47cb509022020010,0x4935991579c0085c3e85cb509022030012]) (.p [0x2c599157cc0085c3e85cb50901f020014,0x95598fe7cc0085c3e85cb50941f020030,0x9598fe7cc0085c3e85c660941f010032,0x34598fe8000085c1e85c660941f020060,0x2598c58000085c1e85c660941f010094,0x9598c58000085c1e85c320941f01009e,0xd598c58000085c1e85c320941a0100a6,0x34598c58340085c0e85c320941a0200ac,0x2598768340085c0e85c320941a0100ae,0x9598768340085c0e85c180941a0100c8,0x6598768340085c0685c180941a0100ce,0x1a05987685c0085c0385c18094120400d0,0x25983a85c0085c0385c18094120100d8,0x6935983a85c0085c0285c0a09412030108,0x25ed21083de412212f6306313211be56000887904dc880260a3b5d605983a84400014020540a85c26430000,0x30cdc18cc028c42820aba116e3ec4bb0d6996d623cac480541c03a7ac00034060540a134263a0000])))))) (.b 672 (.b 560 (.b 496 (.b 464 (.p [0x7100b1c03a0040085c0e0340a13426070000,0x2bfb4742e81fc5844a542a149c5885689f95a6522d55b10064804590ab0842cac789295891ccb075a00f2fd8902e5341203a7a40285c0e0340a0cc26750000,0x3eb484b3c048f8b90234330b21468668b346920fe4bbfabe34334cb0756fff15c230da661203a7a40285c0e0340a134344d0000,0x611303a7a40285c0e0340a13426020002,0x18b5347c5c807b30b557bb1024488706b066dfffc3f8af8d0cc2c851a19a4ffef202a4590a7c1237063100610bdde091c90bb1065832a2141a011c04d7a40285c0e0340a13426880000,0x21c03a7a40285c0e0340a13426010002,0xc1c03a7ac0085c0e0340a13426020006,0xeef1c03a0040085c0e0540e13426010000,0x1dde60d5896ed0b9580d00295b193313d89feff7782a1428122efdbbb44c46d0d2302dfc5a2c428125d0cd5f1f66958b4e5bd8c99a611303a7ac0285c0e0540e13426760000,0xbeddde7ed10a4f44013055f644e5b18904c1c04e77c020740e0540e0cc26290000,0x210a9ea2737fcbeddcd90cc213978f77e486418a81fcf2b458b6898848405bfaad682a862910b696cd3ba1460061622244428358920116d0c40de0b0894a81fc5a4a15891c04e77c0285c1e0540e0cc269d0000,0x341c04e7840285c0e0540e0cc26020002,0x17bec42be3ec5a2c55f6a5b18b7928c42820b25cb41d8ac4c1c04e784020740e0540e13434370000,0x1fe2913daffda1215e5f4481c3343345885024bb46d7de3d0e89cdfc468fa1985ba0c81cbb7ccdc8c81486edfba07f11a3e8668b377016a52a15891c04e7840285c1e0540e134347b0000,0x61c04e7840285c0e0540e13434010002,0x2c11c04d7ac0285c0e0540e13426030004]) (.b 480 (.p [0x21c03a7ac0285c0e0540e13426010008,0x31c03a7ac0085c0e0540e1342601000a,0x91c03a7ac0085c0e0540a1342601000c,0x341c03a8400085c060540a13426020014,0x2ff2f822c455d4f9c7a2c90437116012effb8f458b08115758003dd6198c24408ab9f132c0dfd6198c1c03a84000034060540a85c4e5a0000,0xdf88ffc308edffa8cf8d55bf44723eb1c03a0040085c0e0340a85c4e1b0000,0xfc1086e22c00b75a721f3ebeefc22a200db156312dc9f99a611303a83c0285c0e0340a85c4e370000,0x156684c1c04e78c020740e0340a24c4e080000,0x36b1c04e0140285c1e0340a24c4e020000,0x27ea9faec1c0a11c7624a661642ad88031c59bb0076087dfc6f9f19b687cde0cc211348f8a7340fdf0dfe4747624a669921c04e78c0685c1e02c0a24c4e6c0000,0x7f1f1e92aa5e2057de71291a3e6616cf50d0ae9299a1b4343156363d8cd1669f5a94921c04e78c0685c1e0340c24c4e480000,0x91c04e78c0685c1e0340a24c4e010002,0x31c04e78c0285c1e0340a24c4e010004,0x341c04e8200285c0e0340a24c4e020006,0x1600fc667feff8485fefe13708b008453894ebe2119be0666314462cdc08f4e40dc56a57d64e6213fcc9ef15ddbd7fea67bcf8cd04d144d88a261c04e8200285c0e0340a85c94750000,0x2c11c04d83c0285c0e0340a85c4e030002]) (.p [0x21c03a83c0285c0e0340a85c4e01000a,0xc1c03a8400085c0e0340a85c4e02000c,0x6a40c32736fe801480cc10adc45804b8d1b8f1ab4580d025bc972d1629a5b15898b320068016109c0c33e3d11831c03a8400085c0e0540e85c4e6f0000,0x91c03a8400085c0e0540a85c4e010002,0x61c03a8400085c060540a85c4e010010,0x2c11d43a8440085c060540a85c26030012,0x2d54372fc0063fa2001822d594aa772469400bcbf0830b6a57b95124292a20d8b116afdf220244888506b12142bc7e7400085c0c0540d0cc266b0000,0xde516c7bf94f15b198019400bcbf08017942bc7e740000640c0540d13434290000,0x1fe0b2bc7e0040085c1a0540d13434040000,0x210a8f8bb1000c1108543431548b557bb102448896c5aab620cb04954a6c69000a71000c2bc7e7400285c1a0400d134345d0000,0x2c55f9f4698a75ee3352a34adf97e88527a6026a29dfc61c9ee33234ac2c2bc7e740020d41a05411134343f0000,0x1b4b15906b9bc1984089a590d0cd14facda86700c986d0d289fc5fc5064c6a44215397ae0ee834f818bcbe5cbcfb12064dab03161efe3f9a2d55b102ec4003b1fc48e4c13c40bffbbccb95d1846cd4a93c4fe0c958d2bc7e7400285c360541113434b70000,0x62bc7e7400285c1a0541113434010002,0x92bc7e7400285c1a0540d13434010004,0x32bc7e7400085c1a0540d13434010006,0x62bc7e7400085c0c0540d13434010008]))) (.b 528 (.b 512 (.p [0x19c12c0767640085c0b0540d1342604000a,0x7100b408b10040085c170541013432070000,0x2118e08428cfb120d38aa45888910e1c592a20dd10049e6d6ae814408b17240285c18054100f032450000,0x8dc8915b3e5eb15925fc54158cff20e96fe54402b16516fd6321feef3003163438b216460a611b91220a0d60cdd7be148dafda2145ee2f7daadeb8f7a1d15396025d1b8a311c38c480545135cb17240285c18054101343da20000,0x2c8c805b4854b7f2a204205522c4448894ac914408d87240285c18054101343d330000,0x2408b17240285c18054101343d010002,0x7b408b17240285c170541013432020004,0x900408b17640085c0b0540d13426050006,0x1814598768100085c060540a13426050008,0xd9bf4036ba009ca378094c691be400408fd08fd6cdf3243ac08b37e93fe2422c7822d9bf622af7c005be31167cc5162139a1e413722098b29c334945987681000034060540a85c4e7d0000,0x2d547c53e29d0023be4a892e90197388012142c87e7e00085c0e0340a24c4e2d0000,0x3fc244d3e6e43e34d0b820ebe2110fd8805127319a69fc7e9934e57493d488c5837e22084d7df118a1e41372842639bb1484d7ee2230f593c2288aa411020ebe09f14e201d8a0e2c1062c9ee83666f2b426ceb0488a262c87e7e00085c0e0340a85c94bc0000,0x2c12d07680c0085c0e0340a85c4e030002,0x370099376f1c884df20881041198502830099376f511411020ebe2119b0476284964f0831098e29041d7c5b2506c5028b38184900424b580c0085c0e0340a85c4e7a0000,0x36c598768100085c0e0340a85c4e030002,0x7978d24b786970f00f6801797ca9a2c4b5a5d86b4cb6f99f9c593498ef88055cc57481797acea35ff6b10131954834fb7af97ec492a38bc6e4c3087e758000740e0540e24c4e770000]) (.p [0x36b3087e0040085c1e0540e24c4e020000,0x36b3087e0140285c1e0400e24c4e020000,0xfad4ac6922678090d0cd1668d2400a5620442c2486866164638b3762490d0c9a58dc7b19a612607e7500685c1e0400e24c4e5a0000,0x362199e0a3c544623344fd5fa9f00cddd05f063fe02b1b8f9bc1424fc661642acb1fe03b158e317624a661646e5ac024638b0440885804b605442a0cc210a87ddf8076241334ca45ee44888371f77892e901a2c1308997500685c1e0400e24c4ec20000,0x23087e7500685c1e0400e24c4e010002,0xc3087e7580285c1e0400e24c4e020004,0x1dde60d5883e3491fff3e3a31660012607e7580285c1e0541124c4e1e0000,0x7fc6f44a47b3c4f9f7f1be7c62ac55fa9f115e3efd2b7e8a1bea7124fc668b058022907d78fbf90fab7e8a9f1be7c608218f6bfd1c668f68462c4c3089b734020f41e054111a04e6b0000,0x32c7129c34b08e8c998988110b0096434334d166e40d0cc0949fd8b33089b7340285c3e054111a04e440000,0x343089b73c0285c1e054111a04e020002,0x3108c8088edfd0258c18e60c71291ed6113e64d63109f7f1be7c47b423262cd1ed0022b0963133089b73c0285c1e0541124c69550000,0x2c1308997580285c1e0541124c4e030002,0x23087e7580285c1e0541124c4e010006,0x93087e7580285c1e0540e24c4e010008,0x33087e7580085c1e0540e24c4e01000e,0x343087e7e40085c0e0540e24c4e020010])) (.b 544 (.p [0x38949f0919fbe2c9bf34d56f9d7472e846118837e220c1dc125fa376a088f94bd8c58a26189208a640422c1226e4424e64e6bdad134cc510e212f624aecd209221cdff120589a4bf1cdfc7a5dbd6269bb802cb710d7bd18a268a7531162d1be51bc663087e7e40085c0e0540e85c94d00000,0x2c1310768100085c0e0540e85c4e030002,0x17c401f42cc5004000740e0541124c51070000,0x2ebcbf6baf2fc1d795481797ec1abaf9bf6be2bba357b9f7d11cc862486a1c3af2a24864419400974fd205e5fb189068a613b0c50d8020740e0541124c52630000,0x65ee3a11f1e7bd08026cdfb92eb02ee727b9e0899e09298b000aebcbc635892e8490833566c5df766824b750849c89221b8718906e9801d10a0c517800428ed0d8020740e0541124c528c0000,0x36042cc50f0020740e0541124c51040002,0x480598c5718000740e0540e24c4e050004,0x9fabf989c0090013f5408cc2f7224441be0e24ba11e4030b2151f176200914ca4e000f6c420598c57180085c1e0400e24c4e610000,0x36b3f4c50040085c1e0541124c4e020000,0xc343b3892e84719b14253f4c50e8020f41e048111a04e160000,0x1a422bdd1f19f19abdd2b7eda1be7c56c66f7cc5f2f5ee95bf465714ade71ef15b19bde3f2f5ef3b143d89299a61380c50e8020f41e054131a04e490000,0x2c4feef1497facb9efec5093f422bdf6e32a9025d2caec55ee3b125ba00641b3809740a2c3f4e10e8020f41e054131a04e4d0000,0x23f4c50e8020f41e054131a04e010002,0x4c3f4c56f8020f41e054111a04e020004,0x590ab21f77892e8dc5d88e0d22543984088910e0808dc8911a1a198421564ba40975b02eec4806bb34ca760c3f4c56f80285c3e048111a04e6c0000,0xc8dc8580497a25ff5dde7c557daf8397eafd548ca357fac78c8317668842ac97b8ec491ce60061ab17f4fd7f80a1ec494cd3458348030c93102216012d3e5fdde8115a90c6908c99a69923f4c56f80285c3e054131a04ea40000]) (.p [0x93f4c56f80285c3e054111a04e010002,0x343f4c570c0285c1e054111a04e020004,0x3c1bea3588f2907c6a7a828513aff47181fb12976f9d76f12d846faae8f13dbd760750cacf3ebff6bc66583f4c5114020f41e0481124c69500000,0xff8435dbfa04b0853028423a80111dbfa04b18faf79013efe37cf8c162114812de99a0a1380c5114020f41e0541324c69500000,0xb3e2737f5c9bc9bcfca4bac227ae9d87fffea3dfa34a44f7e876894df261f24c7bcf388af2c49fed147124fc62af2c49fa13c437072bb9a2c4ba18d623a4812eb1a13343f4e1108020f41e054131f469810000,0xff89c0ea8223261b7f400b204e6a46f124b1ce53df918108acbe894df264f43cf9fba25cdefdeb6b17738e8cd16034090f0dfc74574788ec35dfdd95df5c45d87b5c5ebabe8f8c71c46b11d1a191c589757e663f4e1108020f41e0541324c7ea50000,0x2c3f4e1114020f41e0541324c69020002,0x23f4c5114020f41e0541324c69010004,0x4c3f4c570c020f41e0541124c69020006,0x38906edba356c22a4a01a8a419513f55b3b7a9150668b266407828f1511ef198129d8b33f4c570c0285c3e0541124c694f0000,0x63f4c570c0285c1e0541124c69010002,0xd3f4c570c0285c1e0541124c4e01000a,0xc3f4c57180085c1e0541124c4e020014,0x36b510fe0040085c29054121a04e020000,0xe00b510fe0140285c29054121a04e060000,0xd7c9879eb1563292eef914238ca8a56b3efde3de2ab490c56fdef847424310f1d172ee5220b6bde525cb2bcab08e800510fe6c40614c29054121a04e5f0000])))) (.b 608 (.b 576 (.p [0x8463832fbe6b2be092160d2a2d04df2252a1c1ce801e0a397c8d6596cb62cbc4b9a32367f11bfaf3a9fc5365e8f3e3345461646871640881fa510fe6c40685c54054121a04e7d0000,0x6510fe6c40685c29054121a04e010002,0xc510fe6d00285c29054121a04e020004,0x814598fe6dc0085c1e054111a04e050006,0x56f450fe004000f41e0541224c69010000,0x18ff019bf9b6487f9388e9189bf08f28e8e23ca5450fe0f4020f41e04c1224c69290000,0xc4dfc4613d4e084e20a47d7a7127e2a704f7e5deab3bb7bf913c9824b752c7523eaffd09e208e6f66808902f742788238bdc97fdd88e6e44732d8240b834450fe0f4020f41e054141f469810000,0x71291f37aa48bbd75844f1afbdbf0abd121051a43fe5dfa117998bcbf1a2c414fe0d4020a01e0541424c7e390000,0x2114945734ddf047424132f82489af220b22eefd08ad883f136b0471602d9e7bd75883f134cb60904c5be20a3474711c6187cdefdebff6fa8450d7ba3417624b4e2c451060d4020a01e0541424c7e8e0000,0x18450fe0f4020a01e0541424c7e020002,0x189bf932622febcd29c4c9ce13891d6286f9379f12737f5c9bc9bcfc80ffd1e23450fe0f4020f4290541424c7e360000,0x6450fe0f4020f41e0541424c7e010002,0xd450fe0f4020f41e0541424c69010006,0x9450fe0f4020f41e0541224c69010008,0xc450fe10c000f41e0541224c6902000a,0x1b125599150f0000f42004c1324c73050000]) (.b 592 (.p [0xdb03a791423a11d8925de141c599150f0000f42005414208731d0000,0x17c4164474711d082f82aaaed79f1ef4279eb04737b12420ec5be20b223a141c58f624977856c599150f0000a8200541424c83500000,0x646c9038b194181d428464a981d428460f0fe6c37d5f42b7852517028daf42b785028b3137f264c45fd798e5191c6f9379fd428462599150f0000f42b0541424c83710000,0x6599150f0000f4200541424c83010002,0xd599150f0000f4200541424c73010004,0xd005991510c000f41e0541224c69050006,0x254598fe6dc000f41e0541124c69030008,0x27ea9fa9c0094027ea811984fd5071020031c593b07856c598fe6dc0085c3e0481124c693a0000,0x605441310fc56ac4e733cc6222adeaade7dcf88c1dc0dc462e3051e320cd17b108c450fe6dc0085c3e0541324c69420000,0x740b599150040085c3e054131f469050000,0xc4ce206443399c40c8811af8fdc51fb9c40a9e2be8f816d4aec59915694021f43e054131f469370000,0x1190220599156940285c7e04c131f4690b0000,0x590a849d156940285c7e054141f469080000,0x811e248d883209a4640204e0814020500895046040f7b052f3c952f4240c599286680285c7e054141c8694f0000,0xdd684fd286680285c7e054141f473040000,0xdcbd5255b20191c8e472391c8e472391c8e472391c8e4500c9c4e2713344e3231918c8c646320506409cc8c6463231918c8139902732050646323190b333226859940644023247e054141f4739f0000]) (.p [0x4b1023253046046046046046044d7599406440285cca054141f4732d0000,0x34599406680285c7e054141f473020002,0x2599286680285c7e054141f473010004,0x2c599286940285c7e054141f469020006,0x2599156940285c7e054141f469010008,0x9599156940285c7e054131f46901000a,0x6599156940285c3e054131f46901000c,0xc599156a40085c3e054131f46902000e,0x36b599150040085c3e0541324c7e020000,0x18158eb1853f59915150021f43e04c1324c7e0d0000,0x181506223049d15150021f43e0541424c7e0b0000,0x14d86ccaaab16646c8c899b16680832fb02843bebeafade15b1665391912253302a2119b361b2666c936180762e0508eb78507068303a8466c12533459928130021f43e054142247e950000,0x1817268c9724d86010e2cd0c06c11186500a980d8390340340ec5c8c8c1c580ca481e055f5bc2b068b303a846194138c0b9955499b31c19c58605cc8054e051b5eb7850826607508cc659928130021f43e0541424c8abb0000,0x2c59928150021f43e0541424c7e020002,0x259915150021f43e0541424c7e010004,0x4c599156a4021f43e0541324c7e020006]))) (.b 640 (.b 624 (.p [0x657d5255df78d54bc56cc833231918c8c69bad18c8c6463231918c8c640a8b619246d232d998230230230230226b6ea714e0d0639902732050640ad190292320506448642cccc8c68b0464649133599156a40285c7e0541324c7ecb0000,0x6599156a40285c3e0541324c7e010002,0x3599156a40085c3e0541324c7e01000a,0x2c599156dc0085c3e0541324c6902000c,0x2598fe6dc0085c3e0541324c6901001c,0x9598fe6dc0085c3e0541124c6901001e,0x6598fe6dc0085c1e0541124c69010020,0x2c598fe7180085c1e0541124c4e020034,0x2598c57180085c1e0541124c4e01003c,0x9598c57180085c1e0540e24c4e010052,0x34598c57c40085c0e0540e24c4e020054,0x46f52b1f598c5004000740e0540e85c94060000,0x81060027fd889a0016237809698c51bd60598c55e4020740e0400e85c94290000,0x1fe8066fc34092fc108b00a7b09115f7794f098514c41effe4af6a2596b1253948495ec68eb60589a2c46021257b59092202116d3304dcf09b8e84035fd62130c45838b3684248248839e9ecd0d76f1aaf84d357b5c4d14ea622c4cdfaf8b125b911133ac44f5fbfed602531cc6289b132378c3f4c55e4020740e0541185c94fa0000,0x4d8489220598fe148020740f04811380940e0000,0x81fe5e1d6091240424e0598fe1480204c0f05413380941a0000]) (.p [0x26ff7d74d2ed23052ede15e6a3c8e52a73deb89b9ecb05139e6426380908b8284ca7bf6b038a22ad82098b35f5c7441093d75e5f858f7484dc75b02d9bcd5935580ffe4475f79582f9bf4490df164d5758b26ae7bd759ab366994f79ffc493f98b595d134450fe1340707414054132e894c50000,0x13fcc3c875224f7ed9ef117b357376f99ef9dc62bf39ef3e3177450fe134070741405413380bb290000,0x144450fe14802074140541338094030002,0x2adf7900260130092009804900413808b3a701300934cde094e70a66282f9d925c357f6cf7ad152a1c584e6204364afb1298a268a260404c205820265222e5994f78881fefaaaed7cd60ab3df873debcf2c0e487167bf689b1211414105991514802074140541338094d10000,0x2598fe14802074140541338094010002,0x6598fe148020740f0541338094010006,0x69c598fe5bc020740e0541138094030008,0xfc1066b7a17b408a8105080928404104202080024a8098598fe5bc0404c0e0541185ce13b0000,0x1fe0c40411ffdb466f11a0458cdf8fffc07ff125a66f068013009bff6646fd9ca37ea98c598fe5bc04074140481185ce1430000,0x8083420808349020d29809804c02601300980411a1bf1a66fddde5a5e898e6a2d7c5745af93264c993264c9acece63013009804c026013009804c02601300931161f4263fc0422598fe5bc04074140541385ce1b00000,0x9598fe5bc04074140541185ce1010002,0x6f7598fe5bc020740e0541185ce1020004,0x2c598fe5e4020740e0541185c94020006,0x2598c55e4020740e0541185c94010010,0x9598c55e4020740e0540e85c94010012,0xc598c57c4000740e0540e85c94020014])) (.b 656 (.p [0x1b4013c22898f8d395c11020ebe2d83856fda8889a3889ea9267d6025b91d55e9ced49c44c7318a088462c3f4c57c00085c1e0400e85c945f0000,0xd33b24035f16c10cfce2c8898ec492801a49c001e141c598fe7900085c1e0400e38094390000,0x2b598fe0040085c1e0400e85ce1030000,0xd9be508cdf28466fc0d1eb19bf034cde2c66fd909ffa261a0419c66f11a66f16026ffc1b9ec4039d4008228083da53237a59ca3784a98c598fe790020f41e0400e85ce1690000,0x19520ac615a708baf8864e2c388c450fe7900285c3e0400e85ce1210000,0x2211e14205991575c0285c3e0380e85ce10e0000,0x1b4d79ca98a8d298a5314a72a64f4d1bcfd46f174c46f3d4e28c077ff47d98c599156bc021f43e0400f414e1380000,0x3e1bcef3bcef3bcef3bceffe83820465ef0d2408c9204649023248c89a47cc732050640a0c81419121918c8c6463232e0ad9a0c8284130119223599156bc0285c7e0400f414e1910000,0x345991575c0285c3e0400f414e1020002,0x2b599150140285c3e0400f85d06030000,0xd9be508cdf28466f9066fc0d3378b19bf034cde288cdf81a66f14466f91ffc18681056f864cf08b3c22cc263098c263098c24c45991575c061f43e0400f85d06650000,0xd33127039bb7a8984151b97e1cbf0b478b40a423472f94842a1cbe527e2a1cbe52c8d270d1b1a0523e693327cd2644415b34580ca0c855991575c0685c7e0400f85d06730000,0x65991575c0685c3e0400f85d06010002,0x35991575c0285c3e0400f85d06010004,0xd5991575c0285c3e0400f85ce1010006,0x4c599157900285c3e0400e85ce102000a]) (.p [0x2598fe7900285c3e0400e85ce101000c,0x6598fe7900285c1e0400e85ce101000e,0x3598fe7900085c1e0400e85ce1010010,0x2c598fe7c00085c1e0400e85c94020012,0x18598c57c40085c1e0400e85c94020014,0x36c422a48f63a3dc81b43267c28eecdee449ce6635d46f129d896cfd0368f34018d39030ca03f4c57c40085c1e0541185c94520000,0x51ac0620d061050610506104e610784d3df8484c260e0e6669e5983083830827cccde1345107854aec5c0a11d0ada950e0d06019c108efb5802ae7334698c938898c598fe180000f41e04811380949c0000,0x56f450fe004000f41e0541338094010000,0xc84c20849d1bc4906a59a261ac4d134581a0a84c92989bdf049631a47ac07ff225ba248c963d329ef5caff5c4d1633484ff04908b00a7bc7b4ef9aa6bc9ccf4d4d67bc709b5ee9068f6b9d60e08613fd7373909841067aebcbc77c4154e2c3f737d689a2e624c450fe118020a01e054132cc94d70000,0x189cce8469bea948bf87ccbf7d708ac232a4de4de7f5630a53450fe118020f429054132cc942e0000,0x34450fe168020f41e054132cc94020002,0x61309814450fe168020f41e0541335cb40b0000,0x15450fe168020f41e0541338094020002,0xc450fe180000f41e0541338094020006,0xc26116120599150f4000a01e04c132e8940d0000,0x36c1cef88249449ce57b06b01ff8f6bcf8cfed8a5dbc77e69773debcef8253de84964cf136b5c59a0929809210c84ca6f9327a6ca69eaf3be08e847053f7e3bea954f7ecca7be4c928df1d8902c4d14449d150f4000a01e054142e8949d0000]))))) (.b 784 (.b 720 (.b 688 (.p [0x55c1a933669a200c49c1a0e665f3259b3de229cb01ffc893f5c41e59b3d3de21c9d152bb36b3d603124417d46b551ed7aeb3d608e48717b028de81410599280f4000a01e054142e8947f0000,0x2599150f4000a01e054142e894010002,0x4c59915114000a01e054132e894020004,0x3079fe877d7d0a3c4f38b37d5f42b7856c59915114000f42904c132e894200000,0x61fc148fe4c99cfa9930f538a342fe4c99c9bf4f7588df3fb28c328c23049d15114000f429054142e894390000,0x38b8348414683033b5e84648ca53c7129c0ea1427ccd990935994106c7fa1dfff7508cdbc28383999af82930fd1a13893fd42846634599280f8000f4290541429494780000,0x24071706a6426c59a020c789e6886893b345808c32825133669a200c49d9b59a200c490e080fe4c98a30aa23494fae2617bb599280f8000f429054142e8a67a0000,0x2c59928114000f429054142e894020002,0x259915114000f429054142e894010004,0x959915114000f429054132e894010006,0x3459915158000f41e054132e894020008,0x24856f6d7a494e0ce2cc263098c2630921841267bd24092d4620d21a8b734a13109a6130b308b333098c263098c263098c24c459915158000a01e05413380bb7c0000,0x67cd008449d15158000f42905013378bb0a0000,0x38b82950612430921a61309848411ad52e9304c011a1078158eb785605ffdaf18b0142424e32546da6984c29c26116708b84dcf7e0624aeb13459928134000f42905013320bb8b0000,0x2a5ba5b0d6a977730591ce247239c48e713332271648f4f7e3098c20f4f7e3098c20f098c263098c263098c263098c263098c263098c263098c263098c248613184c613184c61318498984127759928134000f42905013378c9c00000,0x2c59928158000f42905013378bb020002]) (.b 704 (.p [0x24559915158000f42905413380bb030004,0x659915158000f41e05413380bb010006,0x2c59915180000f41e0541338094020008,0x2598fe180000f41e0541338094010016,0x4c598fe6ec000f41e054113809402001e,0x36b598fe0040085c3e0501138094020000,0xc818540450fe6ec0285c3e05011380940c0000,0x3803bebeb7856c599156a8021f43e048112e894100000,0xc813a3449d156a80285c7e048112e894090000,0x8c8cbd8b40a5919008c089ac8c8d8052f100ec494c599286700285c7e0481129494390000,0x32cb489c9948c724504c86448644864634c894b5f5495468257dffc664632268c8139902832319121918c8c644a555510c890c8182b06380cad03c8c8c1c10d0194903c8c8c1c59a6c4919034902a23204d9599286700285c7e048112e8a6d60000,0x2c599286a80285c7e048112e894020002,0x2599156a80285c7e048112e894010004,0x34599156b00285c3e048112e894020006,0x508c49d151b4021f43e04811380bb060000,0xade142559928168021f43e04411328bb0a0000]) (.p [0x3001c364ccd93b07232266c59a020cbe9dbc2b62cd014230ca01530282862684d9207043406500a89b24144011830560c7160284619403056f0ad9a2c0508c2841b4e055f5bc2b6659928168021f43e04812328bbba0000,0x4c5992818c021f43e04811328bb020002,0x180d82bef62c4415831c064e0c141c580ca11180c15bc2b6282b785070401423060ac61420db5992818c021f43e04411380cb5c0000,0xd8ff4950a7d6f3bcef3bcee4c9ffade779de779de779dffc661318490c248613184c613184c6130a070d922980d83a74ede15b345809080312441b4e055f5bc2b668b0121308220c255992818c021f43e04812380cbac0000,0x95992818c021f43e04811380cb010002,0x2c599281b4021f43e04811380bb020004,0x18599156b0021f43e04811380bb020008,0x1900ac22304004b5186b00285c7e04811370bb110000,0x1913038b34049184b10231c3c38290226919134b2320c890c8c6463232e0ad8a7c07cc5992e6540285c7e0481131cbb5e0000,0x3028654be406646323190273231918c8c6463231918c8da71bcef3bcef3bcef3bffade142c15bc2b62cd014230ca0c135992e6540285c7e04811370c8740000,0x2c5992e6b00285c7e04811370bb020002,0x365599156b00285c7e04811380bb030004,0x6599156b00285c3e04811380bb010006,0x2c599156b40285c3e0481138094020010,0x2846190049d156b4022d83e05013304940d0000,0xc0b93426c59a0230a106c95499b356020c2f02afade15b16680a11850830a702afade14bcc5992812c0217c3e0501329c945e0000]))) (.b 752 (.b 736 (.p [0x1555562a0155424d668a8060ade15b34580a1186504a55136638b1504a325c93601c9d821a6046794619403c0abeb7856c59a028461941335992812c0217c3e05013304a8880000,0x2c599281c40217c3e0501330494020002,0x1499b3562a0150518a54a1a680a1240f02336f0ad9a2c0508c328057b6eaaaa39779dd297a52f4a5e94bd297c80cc8c6463204e6463231918c8c64632078157d6f0ad9a2c0508c328245599281c4022d8600501330494af0000,0x34599286b4022d83e0501330494020002,0xa5599156b40285c3e0501338094030006,0x4c599156ec0285c3e0501138094020008,0x2598fe6ec0285c3e0501138094010020,0xb3598fe6ec0085c3e0541138094020022,0x34598fe7940085c1e0541138094020024,0x31f598fe004001d41e0501185ce1030000,0x1308300450fe5d0021d41e0501185ce10b0000,0x1bf1a66f5ddcf4bd0ba73999315d3264c993264e54f78c245048a09c4c84c84ca101050020a0049ef3a8308283098c24c4599155a8030c01e04811414e16e0000,0x404914841820808349020c9408a8408cde2806488a26809804c026013009804c024f7599155a8030c01e0481185d065c0000,0x2c599155ac030c01e0481185ce1020002,0x37e4a7e882f485c6efc94bb33cd457f0afe15f3fa2bf857f0afe16bf85afe16bf85af9326798c04c026013009804c026013009804c026013009804c026013009804c024c404c25599155ac030c01e0501385ce1b00000,0x2c4599155b0020c01e0501185ce1030002]) (.p [0x6130830049d155b0021d43104811430e10b0000,0x32e929ef9a1349c48e71389c4e27138c263098c263098c263098c24861318415b333098c263098c263098c24c4599281d00211431048113ece1740000,0x309841a04fd281d0021d446044113e4e10a0000,0x6c6f3bffade4771423287715f7ff1984c61243098c263098c263098c20aaa93366ac54841505266cd19056cd16032807a76f0ad9a2c065186500f0984db34599401a8021d446044113b8e1930000,0xd979939ff5f4c6a6294c67399ff8cc263098c24861243098c263098c26309313083b599401a8021d446044113e4ef4f0000,0x2c599401d0021d446044113e4e1020002,0x245599281d0021d446048113ece1030004,0x345992826c021d431048113ece1020006,0x4df8c4dd00c73dc620a1261389909c4e271389c024c40412775992826c021d43104811430fc3a0000,0x2c599285b0021d43104811430e1020002,0x245599155b0021d4310501185ce103000a,0x34599155d0021d41e0501185ce102000c,0x18598fe794021d41e0501185ce1020012,0x493598fe7940085c1e0541185ce1030014,0x2c598fe7c40085c1e0541185c94020016,0x2598c57c40085c1e0541185c9401005a])) (.b 768 (.p [0x9598c57c40085c1e0540e85c9401005c,0x6598c57c40085c0e0540e85c94010072,0x2c598c58100085c0e0540e85c4e020088,0x2598768100085c0e0540e85c4e0100e2,0x9598768100085c0e0540a85c4e0100f6,0x6598768100085c060540a85c4e0100fc,0x2c598768440085c060540a85c260200fe,0x25983a8440085c060540a85c26010112,0x345983a85c0085c020540a85c2602013a,0x7c00f1c03a004000140285c1613426060000,0xc334063328300d9ef5f3e33dfce7b5b8b867ccc069909c1c03a6c002014020b41613426310000,0x475c320c6000813324584b0c8b481cce8c130c8b6efc02f2f13933219fc48c1c03a6c00200c0285c2e13426470000,0x1fc058645a0f83c3958f7ee1cd6d7b93bc0918b356d7b862b0227eddfbc8bb6b4801797e262cddad00235941dcde9ac20596d732758c982921c03a6c0020140485c2e13426750000,0x61c03a6c0020140285c2e13426010002,0x91c03a6c0020140285c1613426010004,0xc1c03a7b8000140285c1613426020006]) (.p [0x26d9bc6441caebfe4c58a8de2043ab3774c18960772228cd7b39888b998090006a3318483b04588abffcf6b89332c6c198c1c03a7b800014020b41685c4e6a0000,0x7cc0207a32608d4099f400b2043189f30a9bbe5611e18cddbbcd143b5d204111145bbc90663360cc62c64d40e6460d50333fadfd4fe2466e81ecfff453c8c59a226888b2040ce43b7780e654e791990c5d3bc64661c03a7b8000140285c2e85c4eae0000,0x91c03a7b8000140285c1685c4e010002,0x2c11d43a7bc000140285c1685c26030004,0x448b877d99801a801a2849275370e40e666322c98332bbd7864987379241a980dd2069074838d6663600151624d1906a0a0ce7c02468f281459876778000140285c1614428880000,0xcc0420c001d82692228a53da4139deccc1b9141391493e20263164a3341c5987677800014020b41685c524b0000,0x737f51a81b0413b77c9bccc73f8a8301488e40268517bec6a826ba406c786a0888a2dde49f4233c0cc77a099fd73fadfd4fa09c7991458b23e8256c598767780000c0285c2e85c527c0000,0x880d09444992810335540cd4e0e4d247fddc3903d193262cd191039919a094a167c1ad9a9fc2ae6ff4629e70c62c131076778000140485c2e85c52670000,0x4ffe664ff953ff649fc99ffb2909075fd25e4ff9489267fe9a7f9c82b0c8b52124ac322c0917a7834e19fd64c48fea1c1cc40b033fadfd4f2a67f5c3877d40d64bac035c13b1d93164a40d43cfff45900a7d6ce3e82554598c5728000140485c2e26852bb0000,0x6cdf28466f942337c8337ed40820cdf94a66f14466fd83ff21065020e44041c8ee441a8092a024c8a1c0cc67b073c020086e845de80b77a8981012438b980127c02630111144445334044112c4afffb889324198c19f0598c598c572800014041742e85c9bbf0000,0xd410d4118c3f4c5728000140485c5e85c9b0d0000,0x4ef598fe004000140485c5e3909b010000,0x18c450fe1dc02014042b05e3909b040000,0x3494599151ac02014052b05e3009b060000,0x54a020089200892008920089811241ac03110445c02003198599151ac02014051f45e390c1420000,0xd404d51e1ac02014052b07e37cc1060000])))) (.b 848 (.b 816 (.b 800 (.p [0x5845e62c101b232126b26080cb835b164c069019632126b26080cb18170709b054580d40906b64c580d40906b64c580d40906b64c5993617002014052b07e338c1870000,0x109df2235053be438c1130226044901130226044c08981132db845e62c1084cb0b098262c1019706b64c580d2032e0d6c98b01a406535993617002014052b07e37ccf830000,0x2c599361ac02014052b07e37cc1020002,0x365599151ac02014052b07e390c1030004,0x9599151ac02014052b05e390c1010006,0x19c599151dc02014042b05e3909b030008,0x18598fe62402014042b05e3909b02000a,0x7031869c450fe624020140485cad3909b0a0000,0x24ffcb5fd21489267fca44933ff2eff391744933ff2eff391744933ff4f0c8b9a99160cce722fa7948b01917a68053e8254559915604020100485cad3909b690000,0x320c990a44ad1760402014053e8ad3049b0c0000,0x57f7208d6766ffc60c98192541930326064c0c981930326cb76a1a8326064c0c981930326c8c0b8b4a94264c0690a4906b62c980d21499706b62c98320c990a4c8e320c9b62c5992c21c0201405344ad3049baa0000,0x38709f45a02c04098381c0c80c80c84c1930322e41936475992c21c02014053e8d23049b3c0000,0x4c5992c60402014053e8ad3049b020002,0xc8559915604020140585cad3909b040004,0x3459915624020140485cad3909b020006,0x2598fe624020140485cad3909b010008]) (.p [0x9598fe624020140485c5e3909b01000a,0xc598fe6f0000140485c5e3909b020016,0x9f598fe00400014045205e85ce5030000,0x11484f3909a8a721d40195160c80c808981130226044c08981126208990208cdfb24083019be65022c66f99408b19be65022c66fda27fe88328116337cc8888b072f3d1162222c199e88b19a03237a2466a6d04406b883398598fe5d402014042a85e85ce5c20000,0x6eaff3070381c0e070381db43425598fe5d40201404520ab85ce5200000,0x4c598fe6f002014045205e85ce5020002,0xb3598fe6f0000140485c5e85ce5020004,0x2c598fe728000140485c5e85c9b020006,0x2598c5728000140485c5e85c9b01001e,0x9598c5728000140485c2e85c9b010020,0x2c598c5778000140485c2e85c52020022,0x259876778000140485c2e85c52010024,0x659876778000140285c2e85c52010026,0x959876778000140285c1685c52010028,0x10598767bc000140285c1685c2603002a,0x185983a85c000140285c1685c2602002c])) (.b 832 (.p [0xe6f1c03a00400034060b41613426010000,0x16246acdd5a69baec44bd0258c6e958b6812dec60aea6b62d26611303a0c802034060b416134263b0000,0x689cd2d9bfd8c98b01a005b6ec3da62c0683cf6bbec66585d87b4c580d0baeb1bec665b5a0e6febcba3f63072b14c32d65ce5b3e6602602d39617cbf447374428340b25427262c11c04d0c802034060b416134269f0000,0x21c03a0c802034060b41613426010002,0xc1c03a7b400034060b41613426020004,0x2febf886a0d025ff22fa00fdfae312403ddf802faf9448fca5dfd6f78a19a2c1510a0052b8bfdb49f7e334593be96be89afbccefa049fa04a72f7831c03a7b40085c0e0b41613426770000,0x341c03a85c0085c060b41613426020002,0x4d2d3c69e5cacd054268016467e34967e008d27f7e63568b2613400a652bcc0cd3099044f4c590548b5269a95e8125cf4ac1f98054f2c56262cd09a004281d4efbe22b33b1c03a85c0085c0685c2e134269c0000,0x91c03a85c0085c0685c1613426010002,0x920820856e22c02114f7b20b6301a0042b660b6301a00590bfcd260803400b0023e2cfe7c1518aae639c931c03a85c0085c0685c1685c4e6b0000,0x611d43a85c0085c0685c1685c26020002,0x192e5a4c0696e5a4ade4b3393164b9692b0bab98f9b429b3de19a56c62145ee2e199419400bcbf085168e0f0cca1c66032141012c0760c800034060b41613426790000,0x17f6f41d240bcbcbbd744806a200400b109c00034080b41c0f0321c0000,0x437bc74483744292241bff1dc62a5b7ba2b6afe31e9e21941ccc613292ff448374429223994ae00974200510a3bcbf7bcbf0ba737fddffff5f58921aa3c19941ccc06dc19c25e5e271f2fddfc8daf062413d120547252400b109c00034080b41c1343dba0000,0x2400404b10c800034060b41613426060002,0x36c5987676c00034060b41613426030004]) (.p [0xbdeb3087e0040085c0e0b41613426020000,0x232c7988ac677c04ba0581dfca452d2087fc24278c3087e744020740e0b4160cc262f0000,0x16a8e503fe4296904bbbe703303940df32c9145827808728114336fa39408a19a6583087e7440285c1e074160cc264e0000,0x1b44a266d1957b460a5e204395acad610a4a27246103a231ca07f19a28668b14c844f68944d742957b46682923087e7440285c1e0b41e0cc26660000,0x93087e7440285c1e0b4160cc26010002,0x343087e7480285c0e0b4160cc26020004,0x17c1fac8a6ca4addf5a95103a2843be0ff850cd164c5beb5200a572fa17348bdbe9df4096421e17bbe658f22f1dc7b85a10f025b57fbefc663087e7480285c0e0b41613434760000,0xd3087e7480285c0e0b41613426010002,0xc13107676c0085c0e0b41613426030008,0xbe00b598c50040085c0f0b4170cc26060000,0x107c36dfd603dc825ebeb200e800598c56fc0207c0f0b4170cc26210000,0x6214c728d057c8d8da6f7cf4d055d1201a800220598c56fc0285c20078170cc26320000,0x78090a50b04a17240ee2344639469a8be3dde5debfd2fff3be0291c0e8f778a53be021aa5cbf5c7a8fa9f0cfd71eac78bf5b46610851ca050a5842bc4611825ddf91e929a2c3f4c56fc0285c200b41f0cc268f0000,0x10851df356d0814598fe6c80285c200b41f0b027130000,0x25b6f80748f494598fe6c802104200b41f0cc2d100000,0x210a8940ec598fe6c80285c420901f0cc2d0e0000]))) (.b 880 (.b 864 (.p [0x8428e46968cff36ad423062a34450fe6c80285c420b4250cc2d1f0000,0xa1bba210c5250b8604a25700484006412391a9dcd866fbdf8c0650b0544ca251840b0599156800220c420b4250cc2d590000,0x2250294599156800385c840b4250bc2d0a0000,0x1eb50854231e212c72f93c41b8f56a361802302263d1a34599156800385c840a0250cc30380000,0x20dcea59e25ba31310230242151e13c3d44d2c1181181181181181181134fe4efcebf11a04703046046046046046046046363636363634e828b3481b1b1a68d0408c0242599156800385c840b4290cc30be0000,0x9599156800385c840b4250cc30010002,0x5d7599156800285c840b4250cc2d020004,0x34599156c80285c420b4250cc2d020006,0x2598fe6c80285c420b4250cc2d010008,0x9598fe6c80285c420b41f0cc2d01000a,0x6598fe6c80285c200b41f0cc2d01000c,0x10598fe6fc0285c200b41f0cc2603000e,0x2598c56fc0285c200b41f0cc26010010,0x9598c56fc0285c200b4170cc26010012,0x6598c56fc0285c0f0b4170cc26010014,0x914598c57040085c0e0b4160cc26040016]) (.p [0x8d209567f97f55a7c0e28415f5803ad8e420598c50cc000740e07416134342a0000,0x5ef3f4c5004000740e0b41e13434010000,0xdeef89117bf5b27ef5b8f11b027f95e3f4c5014020740e0b41e0f8341e0000,0x17cbf9fe76feb957c67ffaaf2afa8d925d7536e12f576897d25b11e87acf8a5adff88d6e3c45c64c5790c4626fd17f94fdeb71fba045f592c5fbe790214ff7cfe3f4c5014020740e0b41e1343f770000,0xd3f4c5014020740e0b41e13434010002,0x5f3f4c50b4060740e0b41e13434010000,0x33f4c50b4020740e0b41e13434010002,0xc3f4c50cc000740e0b41e13434020006,0x25b7203d071c814598fe0b8000740e0b41e0f834130000,0x25c98bacc4b13df05283a00e80041fdc243349fa7ec40431131e880853fdc788c4df27c46caa7c4611213d4f3ed8e494598fe0b80004c0e0b41e1343f6b0000,0x22f818fc23a03663ebeb6396c598fe0b800074140901e1343f1d0000,0x8dab0c450fe0b800074140b4251343f080000,0xaaa7354e4c46d5864a3247ad8e41c588dab0c94657d6c72d9a8c91eb6392534599150a400074140b4251143f4a0000,0x12051ac98001849544d9a0c4d921b316236ac330310972570621f21b316236ac32517c0c7ebeafad8e5b266599150a400074140b425134466a0000,0x2c599150b800074140b4251343f020002,0x2598fe0b800074140b4251343f010004])) (.b 896 (.p [0x9598fe0b800074140b41e1343f010006,0x6598fe0b8000740e0b41e1343f010008,0x2c598fe0cc000740e0b41e1343402000a,0x2598c50cc000740e0b41e1343401000c,0x4c598c5704000740e0b41613434020014,0xbdeb3f4c50040085c1e0741613434020000,0x2dcfc15ccb9a44fe64962ef5bb6884304bfd082f77c9e3343f4c56f40285c1e074160f834330000,0x28ff77edfe8923f21dfdde259e892d5cbfd2ffe1f1a896ff16205b94b3bbc10d2f77a3f4c5014020f41e064161343f3e0000,0x1c4906a5d7a2fa02f779f6ae165e4437bd67f72ff52b87c993d323af69d3afc57fa2ef11eefdd857da7fbbe57004ba3ceef12ef2bfd487c0f2094525ef3c5177ecf77a3f4c5014020f41e0741a1343f7a0000,0x93f4c5014020f41e074161343f010002,0x5f3f4c50dc060f41e074161343f010000,0xc3f4c56f4020f41e074161343f020002,0x9425a84597ae32fe28909022588110b00961a5ccacbc99365e7e4c9fc51418a8c210a391a5c3c4783066fbe7285942cbee8d161e021acb421ff5749794230e855893f4c56f40285c3e074161343f900000,0x63f4c56f40285c1e074161343f010002,0xd3f4c56f40285c1e0741613434010008,0xc3f4c57000085c1e074161343402000a]) (.p [0xf5090a3be482001a58814598fe6c80085c1e074160f8341d0000,0x5ef4f8fe004000f41e074181343f010000,0x170484d963504a567d554f57c6091f93e20a3d182475be2464baf499ffea66b9fb048feaf64c9cf17f77896eef05a230890cf824bc7ec121df469ae5fae7e5c6090ef825be8c209729e343cfe014020f41e074181343f950000,0xb80254090c4626fc25b812048fcaae75754c2cbeaf6a0844b9012cbbe441472a2af4c121df11d1b5e8054f110014020f41e074181343f5f0000,0x33f4f4fe014020f41e074181343f020002,0x5f4f4fe0c4060f41e074181343f010000,0x16c4f8fe0dc020f41e074181343f030002,0x494598fe6c8000f41e074161343f040006,0x18898f4048c00210ab0d2e233f8b246d1257dea94d30b547a024638bd9fd6c598fe6c80085c3e064161343f4c0000,0x250970ef8af106ad908804411e532e2c78fe2314173e0cca2040ad1c8d48d4ee2589e5f19423062a341bf8c450fe6c80085c3e0741a1343f5c0000,0x35089a4215085478b70c48d046046046046046046044f7041b1a63dd930d3b8324b506c61023070e204488260842a12978d071ae080125052f1000c599156800085c3e0741a1143fa20000,0x4957bc3d1aaf78625928c4a242512128c4a27b8823830251b101a48d73e15e240c83151328109021c583289461299235c120f1598822bc3bd7c78e9811e59703151859915680001f43e0741a134469b0000,0x204604849d156800385c7e0741a134460c0000,0x25881192d881197bc31458230230230224046046044efbd20519c11810270409c102b4081490204e659d38231a766ba34599286600385c7e06c1a13446840000,0x62197deb4bd24bd84bc897912fb3c7f5d297a52f4a5e7c1ec25e44bc897912f225e44bc897912f225e44bc897912f225e44b9f0608c08c08c08c08c08c08c08c08c08c08c08c6c69a040a5599286600385c7e0741c13446ad0000,0x4c599286800385c7e0741a13446020002]))))))) (.b 1376 (.b 1136 (.b 1024 (.b 960 (.b 928 (.p [0x4d7599156800085c7e0741a13446020004,0x6599156800085c3e0741a13446010006,0x2c599156c80085c3e0741a1343f020008,0x2598fe6c80085c3e0741a1343f01000a,0x9598fe6c80085c3e074161343f01000c,0x6598fe6c80085c1e074161343f01000e,0x2c598fe7000085c1e0741613434020016,0x18598c57040085c1e0741613434020018,0x5f0be3dde27a5cf1495f7e80db504cf0121129ff667ec3fe2886814ba377c5efdad2a54bfacdfacad5ef0af11a351f8abfac486bb0b9f397bd55f22f7eabda3341cbde0c3f4c57040085c1e0b41e134347d0000,0x117c03a03663ebeb6396c598fe0e0000f41e0901e0f834180000,0x96ddab0c450fe0e0000f41e0b4250f8340a0000,0x1360f549010d446d5864a3247ad8e49413210a2c46d5864a3236bd6c72c1a8c80f596cd10a4a531c599150c8000f41e0b4250e034630000,0xdcb923d1364824a60a3236bd6c7204b11b561928c8475b1cb64c599150c8000a01e0b4250f8393d0000,0x102e69812266cd5c58edcb92a734104c46d586634588da80074a0daa5c91042d3069311b557866c4d921a3125828be063f01e8daf5b1c838b11b561989599150c8000f4290b4250f839980000,0x6599150c8000f41e0b4250f839010002,0x2c599150e0000f41e0b4250f834020004]) (.b 944 (.p [0x2598fe0e0000f41e0b4250f834010006,0x4c598fe6cc000f41e0b41e0f834020008,0x2042c021c8d6edff8f28334c210a391a2fac694b9f368efbe7b92262a341bf8c450fe6c80085c3e0901e0f834470000,0x4842a119681027044efbcdbef18a089011200895044c7a941d05052f0005649c5991567c0085c3e0901e0e034500000,0x15697a4b787b32518946251894625094bc494c94625189462518944a928c4a31289ee7ee6c90d18214593b88bcc544ca5a45b32400250272513de18a4a04e2c91c8d1b4668a899448f4c00a120764c5991567c001f43e0901e0f839c00000,0x3fc40c1210a842a119681027040ad0205008c0890044808c0898f760a5e340c5991567c0385c7e0801e0f839540000,0x81180484a51667c0385c7e090210f8390d0000,0x1078bde1933c12e8db5e921192982302302302302302302276fbd0afe19cd3fa212cd8d8d8d8d8d8d8d8d3bb37465992a65c0385c7e090210ec39750000,0x3502bef5a5e91fcb4bd0320c118118118118118118118d8d8d8d8d8d8d8d8d3408c135992a65c0385c7e090210f83c5b0000,0x2c5992a67c0385c7e090210f839020002,0x33f5991567c0385c7e090210f839020004,0xdd75991567c0085c7e0901e0f839020006,0x65991567c0085c3e0901e0f839010008,0x2c599156c80085c3e0901e0f83402000a,0x18598fe6cc0085c3e0901e0f83402000c,0x4a16a5e5060800e900450fe6cc0085c3e0b4250f834180000]) (.p [0x6829a0a63fa0964a04e4a04e4a04e4a16670ce4a24094484a26500f7360a00501a48e468da334d12979e0c59915124001f43e0a0250e034680000,0x28a7066b79bb9d51d2f04a3bc9e59b6bc42a64a3128c4a3128c4a3128c4a3128c4a3128c4a3128c4a256e028b831084b93c3592061e89b34904ab2619751b136482e824b450c741f59a1a524259915124001f43e0b4290e034bb0000,0x4c59915684001f43e0b4250e034020002,0x811804849d156840385c7e0ac250e0340d0000,0x20f12cf12dd18d6f1210a84612c11811811811811811811287a02468b7a25331fd104cd3a0966c6c6c6c69dd8ba34599286600385c7e09c250e0347d0000,0x32fbd06979ade8428fe12f225e44bc897912f225e44bc897912f225e44b80deb9f0608c08c08c08c08c6c6c6c6c6c6c6c6c6c6c69a040a5599286600385c7e0ac280e034830000,0x4c599286840385c7e0ac250e034020002,0x2757599156840085c7e0b4250e034030004,0x34599156880085c3e0b4250e034020006,0x204a3bd2d2f4a64c57de9029c5a541334d8d8d8d8d8d8d344a3128c4a3128c4a3128c4a3128c4a245b884a85e668009029688402e4d2e4cd00120545971771366920ba094c31d07d64cd2508da304007480093599156880085c3e0b4250f839d40000,0x2c599156cc0085c3e0b4250f834020002,0x2598fe6cc0085c3e0b4250f83401000c,0x9598fe6cc0085c3e0b41e0f83401000e,0x34598fe6d40085c1e0b41e0f83402001c,0x96ddab0c450fe0e4000f41e0901e1343f0a0000,0x8036089093d30688dab0cc0c99b3570572602936bd6c72d932449e9b04c85a3360680a531c588dab0c94b82c7e3df1219f8f7c494f7c149efa3088eafad8e5b3517c0c7e47abeb6392534599150cc000f41e0901e1143fad0000]))) (.b 992 (.b 976 (.p [0x212e4ae0e11e9b011c95e6689b06b926c042929459a236ac3252e4c3c4f7c48791efa527be8c37d5f5b1cb64c599150cc000a01e0901e13446630000,0x83ea8d9633c45df05af78d21051e8c465ef9eb7eeef891fd5dbab0c49d150c8000f4290801e13446340000,0x1a2dc35926c04724d989710858679dba31caa6c49e9b241253244d9a60d12ea909b2c7b756192b86d7ed124bb1cb64824a62c599280c8000f4290801e13446750000,0x18599150cc000f4290801e13446020002,0x201097268425c913668b3400074a0c6a5599150cc000f42909021134462e0000,0x9599150cc000f4290901e13446010002,0x6599150cc000f41e0901e13446010006,0x2c599150e4000f41e0901e1343f020008,0x18598fe0ec000f41e0901e1343f02000a,0x8db21b0c6fa00100450fe0ec000ec1e0b42512c3f160000,0x40b9a900a2e0a126b1730001d20138102e088125c1c2b9ab346fa4956c32637d000806f709b264a8a236ac331345f031f91eafad8e583446d5866262c599150d00009c1e0b42512c3f980000,0x54952e2e6280488102e2d084b9226cd593340145c186c31be80040245599150d0000ec280b42512c3f490000,0x34599150ec000ec1e0b42512c3f020002,0xa5598fe0ec000f41e0b4251343f030004,0x4c598fe6d4000f41e0b41e1343f020006,0x942328b608067f900450fe6d40085c3e0901e1303f170000]) (.p [0x29bba8a4a8964a312813928c4a312890942cac2518944c7235c4242c0234689242e0d247235235f76e5f6fad423df7cf8cd151859915124001f43e0801e1103f780000,0x14d6f491e24afbf5564a3128c4a3128c4a3128c4a3128c4a3128c4a245be8812dccd0012052d12a5b99a00246cfdcd920b46085164ee22f31518de66864024259915124001f43e090211103fa00000,0x4c5991512c001f43e0901e1103f020002,0x145c9125329bba8a638b2518946251894625189462512b7d129814d8759a00246d54177df3d1257df3251b0694ae0d246b88b0ae818a83eb173250216eb9a0881d201335991512c001f43e0901e13045a50000,0x2c59915688001f43e0901e1303f020002,0x81180484c51b6880285c7e0841e1143f0d0000,0x402d9dd19404b0460460460460460461ee07f451e59a744b75018e6c0a5e340c599326500385c7e07c1e1043f550000,0x1aeb77f0d697a47f097912f225e44bc897912f225e44bc897912e94bcf830460460460460460460460460460460463636363634d0231b599326500385c7e07c1e11442870000,0xd599326500385c7e07c1e1143f010002,0x68b4bd240706736309cc273636363637408c25599326500385c7e084201143f2f0000,0x6e8599326880285c7e0841e1143f030002,0x19097599156880085c7e0901e1303f050006,0x34599156d40085c3e0901e1303f020008,0x245598fe6d40085c3e0b41e1343f03000e,0x6598fe6d40085c1e0b41e1343f010010,0x2c598fe7040085c1e0b41e13434020022])) (.b 1008 (.p [0x2598c57040085c1e0b41e13434010048,0x9598c57040085c1e0b4161343401004a,0x6598c57040085c0e0b4161343401006e,0x2c598c576c0085c0e0b41613426020084,0x25987676c0085c0e0b4161342601009c,0x34598768380085c060b416134260200a6,0x91d305ba5c9a688f53d3243efbaf79345a585bad60590f24c59249bae7645305ba95268258466ef4a4d3fbae7645f75b02c245bac62eea6794879260d2bc52bcc970cc06839583f31a972d072b16e9f304e47127b7ccc009a1a4c3087e64c000340685c2e0cc26c80000,0x1eb6bd9014ef7e9deab1ef15283eddf31a413dcdfdc319ba9ef72e1c62f2f99980d17dbe66026a2cd5b5a9ea71992e1980d2664318c3087e0ec00020061742e13434660000,0x5e67d025848d1e3568b69258d07ede0d0258c6a5d2b09a17396d693160fc485df8d085cacd005ba9deb233087e0ec00034091742e13434600000,0x343087e64c00034061742e13434020002,0x320e5b58e8d77e36bc5fc7bc64cd0e3268c83540dff2c324cd1668c9a3221004275b46e67695f3b3087e64c000340685c5e134344e0000,0x93087e64c000340685c2e13434010002,0x2c131076658000340685c2e13426030006,0x12bc00f598c5004000340785c340cc26060000,0x1beefd1e2bba463df8809066004005fffd71985237f69b5fb4428beeba24a41a8287f2fd12cf4483504c5800598c562802034071a4340cc26610000,0x95e20f598c5014020340785c6a0cc26050000]) (.p [0x4fe69f7ddfa93ec66fd6ac677917bbf42d35d2149a4eeb9d916045fe2fd0b088e1bf784472b62c8b093fc66b2316b7585b9e899d5fb2d35d6c5cd0a419c8b17fbf0af30b4e467a4574264dc8814d907b24c3f4c5628060340785c6a0cc26a50000,0x649ff90074fe2a2454483321248a424100241002413849bfd71008cf2a5788165ce254e40fb14290438248498141a0598fe628060340785c6a0cc26770000,0x2598c5628060340785c6a0cc26010002,0x3598c5628020340785c6a0cc26010004,0x9598c5628020340785c340cc26010006,0x914598c5630000340685c2e0cc26040008,0x245f5a1ee51ea23abf20e907c7d079ccc614abdbd6cf98853729491ad93300280598c50e800020061742e13434460000,0x437061bde719b939400b7c5cff0d63406180c801d327d0299f21c19805583f4c50c400034090f42e0f834480000,0x5ae65fcfad6325f18c51380c50c400034091743e0f834110000,0x81480b6b828b031d1efd18b418475c19e70dc98b34533d6f7d8570fc8ae0c63dfa21805c6d12eb1abae1ce3bee69ab897208d91871980d12eb6ff4429e8902e012ea666034992ff7c46ac499bf3cfbfc8443f4b7e8c283e3e202560343f4e10c400034091743e0f834cf0000,0x23f4c50c400034091743e0f834010002,0x4c3f4c50d000034091742e0f834020004,0x4ef3f4c500400034091742e1343f010000,0x37c02a5c998e015e610811dfc812dee957062b87d10c9668975853e612f2b8315c99a21a0ba1a25d6c437374428b35bbf7db7a2b6180d266886e0c321ccc6d12ea5f883ac23626e0c621410d1be7d002c0b93a5583f4c50d002034090f42e1343fc20000,0x7cd86b44c2bcc20d5b3f97f9f308365c3c8efbdeb34983516d002904f98d5ffc408d612c0cf7db7def5c9834fc993d3210fb970e3344bac0c352e2ec235f3f109746e4c93ceb8b7e20e8ca68b12eb621b830c87331b44bac4c59a37cfa04b0855ede34923f4c50d002034091743e1343fd70000,0x93f4c50d002034091742e1343f010002])))) (.b 1072 (.b 1040 (.p [0x33f4c50d000034091742e1343f010004,0x2c3f4c50e800034091742e13434020006,0x10c873d8a03707c8f4f3e9a0a2ebfd329103fc00061191d726488a6bbe4f7f59a21b9208e2c98184a8eb93268309724437bf4592b679c3706190e6630a50467360c32c7444c8b9f4481414d10dc1d11c9e8902881feda3e012814598fe0cc00034091742e0f834d50000,0x4c321ccc61400af3be30ec19fd8a4b1762002aae0c5795c98b3744c2bcc25c95c3e5b7fa2149e8902c05706ff447266581bfd11cdd10a080ae0dfe88e4ccb6feba2403534054d01410c69047256d8085251b4db4341c598fe0cc00034090f42e1343fc80000,0x4ef450fe00400034091743e1343f010000,0x2cb83c4d7344341761c6fc4c9507539f41d23681a01b2e2c1153f32ff7f1acc5dfea9c67886e0c32587d3621a0a8015c1886e0a59b0c00ec1ef803cfbee2e6659640133ae0cf386e2ee6bfccca4d07fb0c614a2c450fe0b802028091743e1343fbe0000,0x9084a97266830d973449ac19e70dc54a1f40c20d05c55899d70eb36d7ec425c913668310dc9047266860340490612fa0edc21b9337443706192c26fc4c450fe0b8020340b1743e1143f940000,0x2bcc255bef78d64cdf09632406055c98289ae0c434166b34980850128612e693062933450fe0b8020340b1743e13446530000,0xd450fe0b8020340b1743e1343f010002,0x6450fe0b802034091743e1343f010004,0xc450fe0cc00034091743e1343f020006,0x4d830ca69817686800599150b800028091743e1343f190000,0x6e1e86369a210ca1cf26cd933003b064e40d522828338210b0e66b9324987c88603499a21b8b9994a036319b01411012071fec10a4ed0d07054599150b8000340b1743e1143f8f0000,0x688c0b83b709b0541ef59226cd300cc02a68211817156165cd1362ec3acdfe319b108d926c0c00ecd000dc18090145eda1ac1a700e084be838425e4446d26688682a03631989599150b8000340b1743e13446b20000,0xd599150b8000340b1743e1343f010002,0x34599150cc00034091743e1343f020004]) (.b 1056 (.p [0x2598fe0cc00034091743e1343f010006,0x9598fe0cc00034091742e1343f01000e,0x2c598fe0e800034091742e13434020010,0x2598c50e800034091742e13434010012,0x34598c563000034061742e1343402001e,0x95e20f598c5004000200685c5e13434050000,0x121229b870e5b7e8cfc6320b5e821629fd4762b3a3264c111d70e190600eea7fcf24c9be8dc8c3f4c562c020200685c5e13434530000,0x124f2d35afe64b260e4a4d4c833cd4bf8a904dde849824c122f4d293d928f398e78260e5e6941cf069c1c0bfe52122cd124e59feb44933ff2efe92fa7949a80917a6000a8b0448b2624245461a579ba77c3209cf39b17334bfce09d8e5228704909141410598fe62c020200685c5e13434e50000,0x2598c562c020200685c5e13434010002,0xc598c5630000200685c5e13434020004,0x1fc0586498948fccafc993cb1953aef3e317291405223014931029415e612aaefd34fae211d70fc8892f31ec9879160cc8a60a45229f327e4f7dcec95fff45917c38727ea91fe35deab5f57c64c5b77804bf6efdf21905ffaad39162c9a4c0522342cd1c645e49a9349dd2e41524c3f4c5630000340985c5e13434e40000,0x1c2710ca440bb04d30148aa645e4450fe11004028092b05e0f834230000,0x17feed5e7f2fa4f10b75976af10b4a52fe758732aef542aef9149c9bfc87873fdfa5ad5fc7b5dffe314e2daa6880d3508f3ae1f54b388614873e87260d4991564eeb297f1ef45c4239339b260cf38a6455321e44291797e42aef3d77e164450fe110040340b2b05e0e034b80000,0xc293fc4052061484e450c6522e29a716364ae2c57f189c452ff38164d2624710a9f9330b19dde4d376bbf033450fe110040340b2b05e0f839670000,0xd450fe110040340b2b05e0f834010002,0x1e4450fe12800034092b05e0f834030004]) (.p [0x26d5e2086f32db904a3a57a30a3c52bc05a500029b578b13cb9999611d09cb19d938a9abd4c2c21577937ce829bfb9c10288164d39495e81459915108000340a2b05e0e034760000,0x132bbf4f4f2915007c4fdbbd6c5917d3c0b5dfa724d0a4153599151080002c0a2b05e0f839300000,0x1304ef4108f3e9535de791672720852287064e569109619486c534e2c1f23583323ae0c42934108f398261ebbd673ce6c54fe61483b0ebc9859915108000340c1f45e0f839800000,0x1002504a0f6a1a86522e0cc989e301b1508989499cad297a089376459cd86c59894d101a1d635781840dabc1ca99c5cf119e58f7a42916759915108000340c2b07e0f839810000,0x959915108000340c2b05e0f839010002,0x659915108000340a2b05e0f839010004,0x19c5991512800034092b05e0f834030006,0x18598fe60800034092b05e0f834020008,0x11f764450fe608030340985cad0f834070000,0x24ffc8479dd4fe81bfa43d926126242411224d12c24c126093049824c122ce293e1a83202bd3c13066690e7834007024849928b4afcb48c599155f4030280985cad0f834880000,0x1f8a449d155f4030340b85cad0f834050000,0x1f8a44fd285e8030340b85cad0f834050000,0x4849269789120891209b424c1260930498245a995dfa7862116f4d9b366cd9b366cdc80cc91849824c1260930492a124a8492a12609304827091724c599405d8030340b85cad0e0349b0000,0x4cf49f9a5f27c301992a6dbe26dc6d1fe9b366cd9b36bc8c24c126093049824c126093049824c1260917212093599405d8030340b85cad0f8396f0000,0x2c599405e8030340b85cad0f834020002,0x18599285f4030340b85cad0f834020004]))) (.b 1104 (.b 1088 (.p [0x2599155f4030340b85cad0f834010006,0x3459915608030340985cad0f834020008,0x167598fe608000340985cad0f83402000a,0x4c598fe60c000340985c5e0f83402000c,0x190014804c92857e21196c6205e8b61bc1ac4d5c4664c1ac6a211815dd8393c16b15cdf5b999de4d3764450fe128000340928c5e1343f5e0000,0x1aab0d4d99062d93e19b41930326064c0c981930326064c0c981930326064c0c8b3992e29c9c86522ec58c86522a507331b47e204696264f2e667175cbd27a1bccabbd500acef260626c53e18032480322ee603248c8fc535deb291400c95e02d2aa2c59915108000280928c5e1343fe60000,0x344aa4d148223aa5011482a0c981931a0c98193091c421286c9c8e64b832721391762c3fa002905440180d8ab1359347551eee0ca49b07bd62d09cc951eb29495e901a3f0c2267173c64423ed6629c2ab5f4cec9858b559915108000340b28c5e1343fcd0000,0x3459915128000340928c5e1343f020002,0x18598fe60c000340928c5e1343f020004,0x2448d073cc0302c09494a412c3f030000,0x244e5243980302c09494a412c3f030000,0x1d2533a4a673dabce79deac9bd366cd9b5937332a6dc6dbe26dc6dc6dc6dc6dc2deaed1bd1fe9b5e46126093049824c126093049824c4c24c126093049824c126093049824c12609304985993a3980302c09494a412c3fbd0000,0x18599243cc0302c09494a412c3f020002,0x184a4598fe60c0003409494a41343f060004,0x33598fe60c000340985c5e1343f020006,0x2c598fe630000340985c5e1343402000c]) (.p [0x2598c5630000340985c5e13434010026,0x6598c5630000340685c5e13434010028,0x9598c5630000340685c2e1343401002e,0x2c598c5658000340685c2e1342602004e,0x1859876838000340685c2e13426020058,0x3d5f7c12ff4003a4507228e4580149b993f7d7dde781ab231eff7d477f790f5877f7945de7e775ef064c101310768380085c0e85c2e13426530000,0x5ef3f4c5004000740e1742e0cc26010000,0x1a0bd2a2becf52eff38f7fa65e5de4ffc2a50ac56df1cdf136d10860d456b0a1d1886f78c10b431b021fac097abe447d5fb5800acc5804f721b35d0e1bef804ac088ad6da210c10fd61293f4c5014020740e1742e0ac269d0000,0x17c5fa95eefdf1efc8f8f7ac7930f90d4fc42d049686eafc7e3f4c5014020740e0f42e0cc2c2e0000,0x2f82e3d5e27d0f5789eafaeaf3e3deb6cb8bf51b2e2f5c45c6002d74ae447e971117eb71e7f0c43f4b7e6309ebd42b99adc77e4e6ba102287abcbbd0829df012e8d3af57977e3f4c5014020740e1743e0cc2c7c0000,0x93f4c5014020740e1742e0cc2c010002,0xd3f4c5014020740e1742e0cc26010004,0x5f3f4c50d8060740e1742e0cc26010000,0x33f4c50d8020740e1742e0cc26010002,0xc3f4c50f0000740e1742e0cc26020008,0x12fab3f625a25ed2063fa399fb0149efa30825ee401d0075b1c814598fe0d8000740e1742e0b0273e0000])) (.b 1120 (.p [0x46407ad8e41c598fe0d8000740e0f42e0cc2d0f0000,0x11bbe3119800337c5ca3df3477c357282501eb6396c598fe0d80004c0e1743e0cc2d2e0000,0x8dab0c450fe0d800074141743e0cc2d080000,0x9b240e0c05a08430041f47d5860a0599150c000074141283e0cc2d270000,0x4b930f1986a9fa52cfa886b3f6021acf2efdc8f7d184daf46d7ad8e41c599150c000074141744b0bc2d370000,0x205cd5549706207266883fbb57954fffd9df0c3fa081707081c99a29c5cddf49cd886e481c3ac988ca7ac33621f207066d6c43830421a88dab0cc6599150c000074141744b0cc30880000,0xd599150c000074141744b0cc2d010002,0x4c599150d800074141743e0cc2d020004,0x2598fe0d800074141743e0cc2d010006,0x6598fe0d8000740e1743e0cc2d010008,0x9598fe0d8000740e1742e0cc2d01000a,0x10598fe0f0000740e1742e0cc2603000c,0x18598c5718000740e1742e0cc2602000e,0xbdeb3f4c50040085c1e1742e0cc26020000,0x5b00751ec7bbf1f1e21bdfbbe8f77cae43d5f2feab76d10b73ea97c2a47bbf71df88433d452c2afeadbb6884306a2b5946a5623ddf2b2097fa114f77a3f4c5014020f41e0f42e0ac26720000,0x161afccf47bd464d0258dd71254fdeb08eb278d78bd6c6f8f10fd9a59eb71e0bbc9ff85177af41bfa1551295c3ffb4fd5fb1174fc42dd3f108ea3f528573faa95c0f9043f57cfeaf33c0923f4c5014020f41e1743e0ac26900000]) (.p [0x93f4c5014020f41e1742e0ac26010002,0x5f3f4c5110060f41e1742e0ac26010000,0xc3f4c5708020f41e1742e0ac26020002,0x4a076bed8aac75519190665b942d00d9e4b06f787788c3c64663d5fbb688d423194be51a3e0cca22502b4687bbd612e80510fd65819ab26b681eaf066005333f4c57080285c3e1742e0ac26860000,0x343f4c570c0285c1e1742e0ac26020002,0x17c2fe868af1eef91aeef3e235f45bd46c7abcbbd7a3ddf7cfcbf5c60d1f1ef40bca4933f4c570c0285c1e1742e0cc2c370000,0xd3f4c570c0285c1e1742e0cc26010002,0xc3f4c57180085c1e1742e0cc2602000a,0x42b5e09281e3a40d8ad7eef829355704bae8d83cf803ad8e420598fe104000f41e0fc300ac26380000,0xff450fe004000f41e174400ac26010000,0x36bafa3b073ffa52f57365603d2e214a5e450fe014020f41e174400a026220000,0x1bdbfe9f54b8bb9179178ae3b5af32173e4df31ad7e8ec7ab9d1196cfaada8299f0165971808f3b70c8fabe77f9fb016e3d7cf9e456bc4bc0d6bf77c10d64dfb92e0a6fa5cfe450fe014020f41e174400ac29780000,0xd450fe014020f41e174400ac26010002,0x5f450fe0f0060f41e174400ac26010000,0x3450fe0f0020f41e174400ac26010002,0xc450fe104000f41e174400ac26020006]))))) (.b 1248 (.b 1184 (.b 1152 (.p [0xaa55b5a414599150ec000f41e174400a0260d0000,0x10ad788c2035af262e38486b93fa52c9bf723eb88528f407ad8e494599150ec000a01e174400ac29360000,0x2a464b9a0f71b011c54966e5c42e2b20d775922ab7954f44d830429a2034154a3274425831360c10b44068857528cd88238bb3710a4873744259a215d4a3250aabeb7956c9599150ec000f429174400ac29a40000,0x6599150ec000f41e174400ac29010002,0x2c59915104000f41e174400ac26020004,0x2598fe104000f41e174400ac26010006,0x54598fe6d8000f41e1742e0ac2603000e,0x1740b598fe0040085c3e0f42e0ac26050000,0x11289e8e46856bc3f4d2b0ce1e1572fad78788a5d7487855e70334c0e50a391ca00542a8f3688e6cf10b2c9414a6ac450fe6d00285c3e0f42e0ac26660000,0x10230246e000a8c20464a608c08c0895044a82170d41181135b8737629fdc5df7ee3d4a4c34e895f7ee8018530f710a0d4d042854488940ec3a97ad4694215c3083033442928014a61020412c599156d00285c3e0f42e0ac26c50000,0x2598fe6d00285c3e0f42e0ac26010002,0xc598fe6d80085c3e0f42e0ac26020004,0x340485a86ba3042620502b463bdbf8aa3c55711864f19190668bee0c450fe6d80085c3e1743e0ac263d0000,0x1c5cd5535028139325133140a30259289ee6c3665039300d42e63922ab7956cdd10966923154a3349944a308526b412eab79fd60dbe6955bca901a0aa51932815420010e4c5991569c001f43e1743e0a026a90000,0x872f138a2b4289c102bc314102282254112008c081efb052f3c952f1a0e85991569c0185c7e1283e0a026460000,0x5028104849d1569c0185c7e1744b0a0260c0000]) (.b 1168 (.p [0x284fd281d8023247e1744b0a026030000,0x28519401b0023247e1744b0a026030000,0x2852947190023247e1744b0a026030000,0x285314b170023247e1744b0a026030000,0x7f5994d158023247e1744c09826010000,0x285394d158023247e1744c0a027030000,0x285414f140023247e1744c0a027030000,0x2854951130023247e1744c0a027030000,0x285515311c023247e1744c0a027030000,0x285595510c023247e1744c0a027030000,0x2856157100023247e1744c0a027030000,0x28569590f4023247e1744c0a027030000,0x285715b0e8023247e1744d0a027030000,0x285795d0dc023247e1744d0a027030000,0x143debd77554c2b5ccb8d46a351a8d46a351a8d6702b851ae16681409c1ed79bbbf3abbefd350a714e68a65e1ad0b1befc0df7e06fbf028c0a3028c0a3028c0a3037df814605181460518146051814605185995f0dc023247e1744d0a027b10000,0x185995d0e8023247e1744d0a027020002]) (.p [0x2545995b0f4023247e1744c0a027030004,0x1859959100023247e1744c0a027020006,0x185995710c023247e1744c0a027020008,0x185995511c023247e1744c0a02702000a,0x1859953130023247e1744c0a02702000c,0x1859951140023247e1744c0a02702000e,0x185994f158023247e1744c0a027020010,0x25994d158023247e1744c0a027010012,0xd45994d170023247e1744b0a026030014,0x185994b190023247e1744b0a026020016,0x18599471b0023247e1744b0a026020018,0x18599401d8023247e1744b0a02602001a,0x2685992866c013247e1744b0a02603001c,0x8dc262db8734531c5138a2b428897464b102302421efb7de6b7886b14bffc62e170b8d170b859a36593046046046046046046044d75992866c0185cca1744b0a026820000,0x345992869c0185c7e1744b0a026020002,0x25991569c0185c7e1744b0a026010020]))) (.b 1216 (.b 1200 (.p [0xdd75991569c0085c7e1743e0a026020022,0x34599156a00085c3e1743e0a026020024,0x91a15d4a33449d15138001f43e1283e0ac290c0000,0x14ca6efaa4d2c9462518944f7017940340cf4fdc4a4c251899a4a2518d44ca251835128d3d5141409a8942e18a4a04e4a07b884ba0622526a2a81c11a8cd9b0328294904219c42ba9464a15407a55b3710a487374428353459928138001f43e1283e0ac29d70000,0x185991514c001f43e1283e0ac29020002,0x5502e590049d1514c001f43e1744b0ac290d0000,0x289b34112e1b2680e2e6a9b34ca087164cd415e21415906a30629280c2cb9941a0d83b0e3c06361b067a4cd83a212c99b9710b8ac835dd648aade55b164c5992812c0014c3e1744b0ac29930000,0x155540e117cc5350296ea354ca1a2a4a312895b8b50b985e502d40cd66930564122455992812c001f4541744b0ac29520000,0x345992814c001f43e1744b0ac29020002,0x25991514c001f43e1744b0ac29010004,0x4c599156a0001f43e1743e0ac29020006,0xa051804849d156a00185c7e1343e0ac290d0000,0x20464b1023024786a0f0532485dc12befdd982302302302302302302365ba9ade6eefceaefbf4e2c1460518140aefce9bbc33930518146051814605181460518d8d3a0960a30289a34599286680285c7e1103e0ac29ba0000,0x5f79a8c0b7532eead2f46a8ef14c4f6f334146051814605181460518146051814605181460518146051814605181460518144d028c25599286680285c7e134450ac298b0000,0x6e8599286a00185c7e1343e0ac29030002,0x2757599156a00085c7e1743e0ac29030004]) (.p [0x6599156a00085c3e1743e0ac29010006,0x2c599156d80085c3e1743e0ac26020010,0x2598fe6d80085c3e1743e0ac26010036,0x9598fe6d80085c3e1742e0ac26010038,0x34598fe6dc0085c1e1742e0ac2602003e,0x25b76377f60e678886399f2b3f57bf47bf18f21f03e31efe9957a3deb0c450fe0ec000f41e0f42e0cc2c360000,0x25c98bacc4b19809723f4818faa86e894fd3f61f5c12df1253df46115777c149fa4486018fc8d38f80f407ad8e413599150d0000f41e0f42e0bc2c680000,0x26c13211c1865241086288ca7ac3254599150d0000a01e0f42e0cc30280000,0x26c1894d11b561925f00e8429a6cd1205c0264241a711b56198599150d0000f4290d02e0cc30440000,0x805cc6dc2535682bc428b83172c804a108cb7324412431018e25d52d8f57391fffab0c3eb0621135c99226c904969c4b8ec7ab9c8fffd4a30fe88b8cd825f00e8425933446d5862599150d0000f4290f4350cc30a50000,0x9599150d0000f4290f42e0cc30010002,0x6599150d0000f41e0f42e0cc30010004,0x2c599150ec000f41e0f42e0cc2c020006,0x18598fe10c000f41e0f42e0cc2c020008,0x22f8b2f7aa32f7c9f27a16c556d9afadfc86c30450fe10c000f41e1743e0cc2c260000,0x25c9878cc16661aa7e9035f5afd5e10c59e22cfd930fd5cd504b8fafabeb6396c599150cc000a01e1283e0bc2c420000])) (.b 1232 (.p [0x20faaae9d4fd3f00d6bc5b76eb79f3cf2ad8c4c8fcdf0c2dabd5ec43c661aab9fd5dbab0c49d150cc000a01e1744b0bc2c460000,0x57244c1a4c4baa4a9758f6ea519297262589f5c14a3d5f5bcab66a5c012a80b4127fb901e91eb6392534599280bc000a01e1744b0b42c5f0000,0x100b995541564c4b825bd17b75572aa93952e0c4d93344b4302ecebb676bd619297261e330d5beafad8e5b266599280bc000a01e1744b0bc2e630000,0x2c599280cc000a01e1744b0bc2c020002,0x2599150cc000a01e1744b0bc2c010004,0x4c599150ec000a01e1743e0bc2c020006,0x117d6bc60d6bc7bf528c49d150dc000f4291283e0bc2c0e0000,0x313d7fa212c91360e884339310aea51928555f5bcab60a15c039fc6d7a36bd6f2a0e4c599280c8000f4291283e0b42c4d0000,0x165c98952e489b3499a215d93e59382aa9724149e9b3498856bcc975bfd4a3252e4c4b13eb829beafade55b349599280c8000f4291283e0bc2e600000,0x2c599280dc000f4291283e0bc2c020002,0x18599150ec000f4291283e0bc2c020004,0xd16897d345009168950189ac99a2804ad12adcc9360650412c42ba33a8cc4cd0328b980ea3c7a0010095599150ec000f4291704b0bc2c6c0000,0x33599150ec000f4291743e0bc2c020002,0x34599150f0000f41e1743e0bc2c020008,0x80360a12a4b8b5a25c90145930102e080e553135aa2e4f0ae481c151194f5866244d920705441fd4359fffa9466cd808e2a53459311b55472a98599150f0000981e1543e0cc308d0000,0x102e088102e6a4a92e0c05164cd120f8c66b78eea8fffd9172c806000ca800c80599150f0000d0271543e0cc30520000]) (.p [0x313599150f0000f41e1743e0cc30030002,0x2c5991510c000f41e1743e0cc2c020004,0x2598fe10c000f41e1743e0cc2c010014,0x4c598fe6dc000f41e1742e0cc2c020016,0x4a24683fbb573c2a79f16d9925d6dbe78a231906698019ff140450fe6dc0085c3e1282e0cc2c370000,0x952defbc0349409c9462502292813928c4a3128c4a2634b802ddabc15e08797c7bfc9615f5b1cb60ca251839394b48805491a0f8b0a9fa61f15fa5615cafe0470b858669859915688001f43e0e02e0bc2ca00000,0x44a27a849d156880285c7e0e02e0bc2c0a0000,0x80300974651023253046046046046046046044f70377014c736309fd051669dd9ba949a9b184081146a5f920e8599286640285c7e0c82e0bc2c7b0000,0x3770351816e06b7add382052039a1cd41334d8d8d8d8d8d344a304c40814b10e5f804842a11968982302302302302302302268f11a7a978973a29a08138204e0813984e613984e613fa086734e9b336052f1a37d599286640285c7e0e0330bc2cd70000,0x4c599286880285c7e0e02e0bc2c020002,0x4d7599156880085c7e0e02e0bc2c020004,0x6599156880085c3e0e02e0bc2c010006,0x48d1b557864d449d15110001a83e0e02e0cc300e0000,0x15697a5336d79bbc3d9928c4a3128c4a3128c4a3128c4a3128c4a31289eeaa0ba1bb289463662328b0cc4a804a0452512a4a2517c0041849414bc31bac599280f8001a83e0c82e0cc309d0000,0x200d821ade812a4a94cd25189462518946251894625196eea80c6c59226c9042de625d4caa0fc452e479f355786634d599280f8001a83e0e0330cc30760000,0x4c59928110001a83e0e02e0cc30020002])))) (.b 1312 (.b 1280 (.b 1264 (.p [0x1859915688001a83e0e02e0cc30020004,0x26786eea6a328c57de2c779bbddf7e9c1ad2f163bd1a8c2707b5e94e5efbe66c6928c4a3128c4a3128c4a3128c4a3128c84859915688003ac6b0e02e0cc306c0000,0xdb599156880085c3e0e02e0cc30020002,0x2c599156980085c3e0e02e0cc2c020008,0x12842b5e06ddabdd01681a2bf76af44472aa3228a1d4660049d156980031c3e128390c02c350000,0xa0283dcd9a4c18842032e2c9ad10186b241a032820964cd12e0902828c4794d9172c806f751aa65e5928c4a30a6fbe68d83dc3283b5a760ca5a4dd38856bc3bc46061554b821e144a30fac599280fc001903e100390c02cb40000,0x386c1ddc436669285cc6a2440282cb9a0f0b2e63eb9312c40f5bcab64c59a215d9172c800a5599280fc001903e128410c02c5c0000,0x4c599281cc001903e128390c02c020002,0x46b793bf3bba71608c08c08c08c089a044887a232aaecc940a8f29a8514c25928c6928c4a3128c4a268944897599281cc0031c65128390c02c720000,0x34599286980031c3e128390c02c020002,0xa5599156980085c3e128390cc2c030006,0x4c599156dc0085c3e1282e0cc2c020008,0x133598fe6dc0085c3e1742e0cc2c020018,0x6598fe6dc0085c1e1742e0cc2c01001a,0x2c598fe7180085c1e1742e0cc2602003a,0x2598c57180085c1e1742e0cc26010088]) (.p [0x34598c58040085c0e1742e0cc26020094,0x7221c8b0283924d934d2424534e33bfdaaafff048fb9577e3c6bc5eb930623fefcd4bda93c3a9df2d7ff694d612d34bcae2f1c9a68e4d260f68dc8c3f4c5634000700e85c5e0cc26760000,0x95e20f598fe004000700e85c5e0ac26050000,0x2ec8a7075fc421a8390450724a8390450722e1800e41403924720cfa240a0028804019c67433ae4c188cc164b5c8ea564b38cd1c9a4c91c83932031c598fe60c020700e2b05e0ac268d0000,0x3f87bf8aba24d39ff9fc12e9fc41a80933f8002008eb2095e3914afcb48c598fe60c030480e85cad0ac263f0000,0x8916a4450fe60c030701385cad0ac26090000,0xff24d49122a245a427f4a094c4f0ce2d493fe49a093f8a891512081a126093048270904e1209c24c122cfb2714d77cd4249509275293534e8259a7528b7f10a7a0068a613992bcdd23599155f8030701385cad0a026af0000,0x4e7fe834bd003972a25b84b70969b366d70d72a6dc6dc6dc6dc6dc6dc6dc6dc25b84b708de8ae46126093049824c126093049824c126093049824c1209cd8c273632e4599155f803070133c0ad0ac29ae0000,0x95fefea645006fe803c826ff92682449ba8916909fc27960bfa1577cd4933424c126093049824c1260931a7599155f8030701385cf10ac296a0000,0x9599155f8030701385cad0ac29010002,0x2c5991560c030701385cad0ac26020004,0x2598fe60c030701385cad0ac26010006,0xe7598fe60c020700e85cad0ac26020008,0x9598fe60c020700e85c5e0ac2601000a,0xc598fe610000700e85c5e0ac2602000c,0x194507a7d16af1cdd46f500a7d30a4c2583924072480e4c48499012a28390400720a0100726067ff5904afc48c598fe138000480e2b05e0cc2c700000])) (.b 1296 (.p [0x33ea01ff2d352316a4450fe13800070132b05e0cc2c140000,0x680b93db3c39aefd07209c1c981c985ec981c9b15c1878a5c0d957d6d257ad9a0cf3e18a0e4138393679c0e6e8853b495e8382960ce1f55ac61bcf153eabc3756b5cb4c8c5924720ce60d1c83948bb345991511800070131f45e0bc2ca40000,0x2140d3a8a68a0d2aef41a5e0abbd000af41c82aa25930724880ca4c83daef0475011577e3930726c4ab7393e192feb0724a9a0e413839303930393039303930391675991511800070132b07e0bc2c920000,0x95991511800070132b05e0bc2c010002,0x12917352040b8b4a972669304293664c0a4c00293212aa9c98393039074e2b831298e226a77aefde4c0c41068a0e4138391671c81b22870eb06719d236e8c98b2634599151180006c131e05e0cc309e0000,0x42c77a141a55de8106032a8964c1c981c981c981c981c981c981c981c981c981c984a4599151180006c13270790cc30550000,0x6935991511800070132b05e0cc30030002,0x2c5991513800070132b05e0cc2c020004,0x2598fe13800070132b05e0cc2c010008,0x34598fe610000700e2b05e0cc2c02000a,0x4c9300a4450fe6100205c0e85cad0cc2c0b0000,0x24249d6f49122a2414724ffca4f87a89151209b424c126093049824c12609167d4238809dcd4249536309cd3a1cdd04338498c95f3d23599155f4030440e85cad0bc2c870000,0x267d5ff8d2fc03b0ca9b674bcdb44db8db8db8db8dabb46f4d9b366cdaf23093049824c126093049824c1260930498245c84933599155f4030440e85cad0cc307f0000,0x2c599155f8030440e85cad0cc2c020002,0x2449d155f80305c1240cad0c02c030000,0x5f4fd282480405c1240cad0c02c010000]) (.p [0x5f5194022c0405c1240cad0c02c010000,0x99d25314ce7afb15ad7b366cd9b366d793f6cd9b366cdaf2a6dbe26dc6dc6dc6dc6dc6dc6dc6dc25a3fd36bc8c24c126093049824c1260930498d8d8d85994722c0405c1240cad0c02c930000,0x18599402480405c1240cad0c02c020002,0x2e4599285f80305c1240cad0c02c030004,0x245599155f80305c1285cad0cc2c030006,0x1e4599156100205c0e85cad0cc2c030008,0x3a7598fe610000700e85cad0cc2c03000c,0x9598fe610000700e85c5e0cc2c01000e,0x2c598fe634000700e85c5e0cc2602001a,0x18598c5804000700e85c5e0cc26020028,0x2d012d52086f00470dcfcd8675e8ae1b27eaf5d6238f0f02697990d8637d0021003f4c5640003381d4705e0bc26490000,0xedfd69591519ec56bd196d662d588caa868c0d5e81956b19a5c233a672e0194378282ae9f7d5b4ccec8ae01322e32fc0072e6770d622b2b0c450fe14c000d41d2805e0a826790000,0x4b81858f8c86eaf71f5c3572180c4c5a2235e9312f5705b8c0015ddbe2e50dfae1ab9c4abeb63960599150f8000941d1e85e0a8265a0000,0x10aabeb7953f599150f8000d4261e85e09c260b0000,0xaaab930713362cc4a0ef2a04b05528c94aa4e414c822e89b2410964c42ba94648aa109648945cca6c0ca08ba26c904259305528c9154214d0ae033fafabe956d69d9a4c42ba9462599150f8000d4261e85e0a828aa0000,0xd599150f8000d4261e85e0a826010002]))) (.b 1344 (.b 1328 (.p [0x345991512c000d41d1e85e0a826020004,0x17645383b6649addaa4d41c8fd0a2c193eed52727c39926a0e4d812feb072480e4c0e4901c985991512c000941d2807b0a826550000,0x38b9ba70d3ae0e27269b22a99349839049bd78127d826bbd0287eeb3269ca4af40b549934822839170e64c70726c411cd14154a3170c510aced7a51827260ce857528c9985991512c000d4262807b09c26980000,0x174ebb26aeed531c983930391720e41480c1b2139145128b93c6cd0eb001482a0717354157064e42722ecd26293292bc44c8229239099c720ce45d9a2c9adc8393000935991512c000d4262807b0a8289f0000,0xd5991512c000d4262807b0a826010002,0x65991512c000d41d2807b0a826010004,0x4c5991514c000d41d2805e0a826020006,0x18598fe150000d41d2805e0a82602000c,0x1945c10361a4af401800464ff150000b81d23c5e0bc2b1b0000,0x4b824a9758c00790812325d6380d5eaa21bc0cabbacd5c674ca9f200e9004bd1a108000b81d23c5e0bc2b460000,0x34406d47d141482968952e1fd1400577094c7164c4b82464baf77dbaaa3a4036aaa7066c0ca087060218a25c423e320bb180b71880676eac30fac599300d40008c1d1cc5e0bc2b8c0000,0x1c5cd484a2e4c40ab83360238a09669310ad7e89726f99fb22e591495599300d4000b8241cc5e0bc2b400000,0x34599300f0000b81d1cc5e0bc2b020002,0x21487c98caaa7260e41d3ae9d4e69c1c8270eb0720e4d0520a5599300f0000b81d23c740bc2b3a0000,0x4c59930108000b81d23c5e0bc2b020002,0x185991a150000b81d23c5e0bc2b020006]) (.p [0xc13598fe150000d41d2805e0bc2b040008,0x2c598fe278000d41d2805e0bc2602000a,0xaa00ea3c7a00100450fe278003383627c5e0a826150000,0x1286c10e0b081c99a00a699c5fa9410536de55b34d2785407ade540a2c15183c2a36bd029b1fa414db7956c553c981c505363f4829a556f2a4a682a94625991513000168361e45e09c26940000,0x1c3628a0a4cd9a4c014d33601c5d9a4c1540a6de55101c5cd505d8cd86c1d9a4c0172c8a0a406128b93db84d9334d005cb2287f4053605360534aade55b164cd05500751e3d000800935991513000168361e45e0a828bd0000,0x2c5991516000168361e45e0a826020002,0xaa00ea3c7a0011449d15160001643627c7a09c26140000,0xa26cd2600a614584d9334014ca78557d6f2ad9a4cbf950298fa8d01c5cd380a6c599b0d8bb34d278540bec07a55bca814582a9466345992813c00164362307a09c26850000,0x1458d9a2c804c82a0a2c6cd2600a63ea2f5e02fb02fb5f4ab692bd6cd2682bc44c81b268a0a55992813c001643627c8d09c26590000,0x4c59928160001643627c7a09c26020002,0xa559915160001683627c7a0a826030004,0x4c59915240001683627c5e0a826020006,0xff59915004003385b1e45e09c26010000,0x159004dd22224023385b1e45e09c26070000,0x4a1b0560386c5141a05a815e6682a0d465815554e117cc014c6f0aafade55b26687ee8172a053640a6c36655d99300d464a0293362e600a636f5e02fb02fb5f5bcab64cdbc2a03d6f2a04b0fdd28cc4c599381e4022145b1e45e09c26c20000,0xc3ba8bc69ea5e24d4bc49837ae2aa5e94bc4c0c14605181409c140ad02813828c0a3028c0a3028c85599381e402338861e45e09c26570000])) (.b 1360 (.p [0x3459938224023385b1e45e09c26020002,0x36c59915240023385b1e45e09c26030004,0x14559915240003385b27c5e0a826030006,0x3459915278003383627c5e0a826020008,0x245598fe27800338362805e0bc26030012,0x34598fe3d0003381d2805e0bc26020014,0xe4450fe3d0000d41d470a10a826030000,0x160a449d15354010d41d470a10a826060000,0x204a6511f424c126093049824c12609172120a47dc29932aaa9cd38b26924406dc1a75d90549a59a74425e4d0726260e4994af16d778a68a122e424950904509254249509254241278670904e1209c2459d499348229a45c339a4c8b0722e45992817c010941d364a10a826ec0000,0x858ef41f24d77a26bbf0a120932690523ea9a4135bc93ef0bd3483d5df8d263483d5df8d263498d263498d263498d263492a690434bd0ab7b6bbd127539a29a4f2cd266931a4c6931a4c6931a4c6931a4c6931a4c6931a4c69172692455992817c010d426364a10a826de0000,0x3459928334010d41d364a10a826020002,0x3a4a733ed778697a0db76cd9b362b91d9bff1849824c126091724c24c126093049824c12609172120a4759928334010d41d470da0a826660000,0x4c59928354010d41d470a10a826020002,0x2e4599153d0000d41d470a10a826030006,0xa5598fe3d0003381d470a10bc26030008,0x4c598fe640003381d4705e0bc2602000a]) (.p [0x240598c5804003381d85c5e0cc26040036,0xdb598c58040085c0e85c5e0cc26020038,0x4c598c58080085c0e85c2e0cc26020062,0x5ef3f4c5004000600e1382e13434010000,0x3d6be20d7c42e646fb7dc4435e831380c5014020600e1382e0f0341f0000,0x2d80d9236b825bd480c314b962bdaa31fa95d70313d9f44486b910d18087a3da23f47cf8f97c7abcbbe625bb2eab631010cd3b44bea5750fda210cf50f88db6bc55f18931598c7bf12548eb93f4e1014020600e1382e0f0349f0000,0x23f4c5014020600e1382e0f034010002,0xd01003ff7fdc81b6cade8095ff01b6a0f99237afed15d7f68a2efddcf7c12c133f4c5014020600e1382e1243d460000,0xd3f4c5014020600e1382e12434010002,0x5f3f4c50d0060600e1382e12434010000,0x353f4c50d0020600e1382e13434020002,0xc3f4c50ec000600e1382e13434020008,0x15c9360cd808e2a534d80852501a236ac325195f5b1cb66a5c03d23d6494d10a4a5051901eb2d9a214905068107d4c2234aecadbe086b1f10d18087137ee57c484db6bf56198598fe0c4000600e0e82e0f834a80000,0x5ef450fe004000600e1383b0f834010000,0x83e096d51b288425c67b1a99508d2a94a3e7932d8c4123ae3c40528cb1806c9085867cb1f1619e687631049523adfec45c625a234e90c7d52a3f2a08eaf9d27c46dbc93f3e73fa3450fe0b0020600e1383b0f8349f0000,0xc450fe0c4000600e1383b0f834020002])))))) (.b 1600 (.b 1488 (.b 1424 (.b 1392 (.p [0x4d83129a180901418a25c12daac22e75c7a82105d049fce9d10aae824ff74a4ff56192b93049507421410599150b0000440e1383b0f834680000,0x2aae689834988dab0cd89b240e1e6b93049507596cd3002809136482168241a8262367c4626f93faff56198599150b000060121383b0e034690000,0x212e4c0049707093d361d665040b9a6555c1ea588dab0cc6893d300c46d34988d9f54a87afc9e5de7d4f917862599150b000060121383b0f839670000,0xd599150b000060121383b0f834010002,0x34599150c4000600e1383b0f834020004,0x2598fe0c4000600e1383b0f834010006,0x4c598fe0d0000600e1382e0f83402000a,0x83ea9028f71a80f611a12030c66c35bb56e989be40c25e5cbe8f6bef8c5845ceb8f1171890e91089ec622e73937ec45c624b842bcc6cb1f1123c88086626fbe739fd9df0c450fe0bc000600e0e82e1343f8c0000,0x40b8384d933440e0c10a08689704b6a844f6310d39cfee18cd89b060850733019025c12d8c4c8eb8f26029463fab0cc0c982050012e23d0d180867c879f6c724a2c599150a8000440e0e82e1343fa00000,0x902ae2c5a32d8d795144b888d37c487b756187d6688d9fdda8f279779fd940e939b5518d44c0b988dab0cd89b240e1e6b87ec5075b1c901a2367c4626f3fab0cc4c599150a800060120e82e1143f8f0000,0x40b822040b9a92aae0c46b164cd0402e6007480093599150a800060120e82e13446380000,0xd599150a800060120e82e1343f010002,0x34599150bc000600e0e82e1343f020004,0x18598fe0d0000600e0e82e1343f020006,0x4b802da8604b7aa061e87acfa096f407ffa80074a0450fe0d0000500e1383b1343f340000,0xcb8348102e6a8ae0cd9a2c9808170410e4027024b8384d87e4423649b06180dd127a6c18602405164c4b81812daadbb75bcbbf45025b1eae445d71b777fab0cc2c599150b4000400e1383b1343f9e0000]) (.b 1408 (.p [0x2000517052a126b264c0ca2e0c0c4c5599150b400050111383b1343f290000,0x34599150d0000500e1383b1343f020002,0x3b598fe0d0000600e1383b1343f020004,0x9598fe0d0000600e1382e1343f010006,0x2c598fe0ec000600e1382e1343402000e,0x18598c515c000600e1382e1343402001a,0x11b464efa00580d8637d0021003f4c515c0014c191382e10c34220000,0x46d1ec30450fe0cc00098190e82e10c340a0000,0x1360ed52544b11b561928c80f596cd10a4a5346407ac0e480c811b56198599150b000098190cc2e0e8344d0000,0x24640ab8b3418ae480b4104c46d58663457076a92a2588dab0c946407ad8e40843446d5862599150b000098190e8340e834600000,0x4c599150b800098190e82e0e834020002,0x80030c56e64c4210205c1c26c98b344b9303134216e5c592225a203446d5866164cd11b6401d20133599150b800098190e82e10c3b6c0000,0x2c599150cc00098190e82e10c34020002,0x18598fe0e000098190e82e10c34020006,0x402e64952e6931451706282901858425e572668a04952e6831360c4a480962cd26236c803a4030000e900c25598fe0e000098191383b10c34750000,0x4c598fe12c00098191382e10c34020002]) (.p [0xc02e081b0c6fa00100450fe12c0014c270e82e0e8341b0000,0x2017324212e4d0ae69a4c100b9801d2298000720030928a2e0c4212e4d2a11259a4cd11b6451d201bdcb92219458cd8250529202588dab0cc2c46d1ec30c4c599150f4000d4270e82e0e834a60000,0x1410956e668009196100b9944d921b326236acaa634000720531285599150f40014c360e82e0e8344e0000,0x345991512c0014c270e82e0e834020002,0x245598fe12c0014c271382e10c34030004,0x34598fe15c0014c191382e10c34020006,0x95598c515c0014c191382e13434020010,0x34598c58080014c0e1382e13434020012,0x16808e08c3dcf9ae80d8692bd0021003f4c5224000600e3244f10c34250000,0x83e2c7d622284063eb18845ab11c15e6086f3e380dd3262eb306b5c79815588acccca074a0450fe0f4000600e1e04f10c344f0000,0x48e06266cd5838584b9038a7025fc6a2e79f72904c79312a0a41c822839057770949129a4e56c4ca68603209833a5d54fac5080b71ee3eb186ee3c423fab311403200437a9b835633ab0c998599150d8000440e1e04f0e834b30000,0x28a6dc25eac1a406160406c59ae1fd052994e2e0ed534d51726a63457066c18949012c59a4c46cfee16ac4657bc357159d90074802599150d800060121e04f0e834800000,0x34599150dc000600e1e04f0e834020002,0x252028b1b3566a4081546b35412030d60e105d0402a2a8865ee880960f0c2efd164c4b81812daac22e78aac675407480093599150dc000600e1e04f10c3b7b0000,0x2c599150f4000600e1e04f10c34020002,0x18598fe180000600e1e04f10c34020006]))) (.b 1456 (.b 1440 (.p [0xe448104180010480e324790e834030000,0x21080d48e091d7045a06930726072607260726421286c1a473239b1453239b16625eac9800a4d9e7364ef45c429093259e491c83930714e04bf8d4ffdf7930b345992113c010480e260790e8349c0000,0x4ce92995de6979a684db8db85bd1fe9b366ffd4db7c4db8db8db8db8db8db8dabb46f4daf23093049824c126093049824c126093049824c126093049824c126093049824c2475992113c010480e324990e834b40000,0x4c59921180010480e324790e834020002,0xc247598fe180000600e3247910c34050004,0x4c598fe224000600e3244f10c34020006,0xa0598c58080014c0e3244f1343404000e,0x693598c58080085c0e85c2e13434030010,0x2c598c58380085c0e85c2e13426020046,0x2598768380085c0e85c2e13426010154,0x6598768380085c0685c2e13426010156,0x4c5987685c0085c0685c16134260201b6,0x1620423e5e340d6062fcbc680109fcb498b14c014ed5df5ecc7b98d6cc6ab9ca9f1067cd683a400bcbc4e4c586e23234b30916ef7fb18a20f69990c630f53eb3f4ce4c5897dc458497be3f88c4193f69996df4087fc0b355ee5602539001ff6b10135b9a4c3087e5ec00034060b41624c4ed00000,0x1fe129f92229887fcc08c11177ec45ffec4589b30913034be6f7e4adacb718b6a6976a6b883220c911773087e5ec00034060b41685c94540000,0x2c1310765f000034060b41685c4e030002,0x2e214f7e005d9bce2fff7fdcf17af218909f6ea693d66c14736280553bd102534002ba1808ea67aebcbf1acdeb06b862bd953a087bf68094d7106b01797ccf1a007b89391367ef4176c56c340633003a240a0065b6b73420598c50f000034060741624c4eb90000]) (.p [0x45f88475d2912400534258a5631ef18ade8abf90a7bf715bd15b5804a627ae335a3d75865062820b006ff9bdbe44fb33084dc980ddbbf74339001fc4622e6b41d601797977eccc2910532d847c404d60598c50f000020060b41e24c4eac0000,0x570621bdf31625d6c43734341760c4328316ccc048a505731cf0dc3a24121f910514f81e4ebdbf7feb339bd05583f4c50ac00034090901e1a04e650000,0x7b7ed4ef3e5f18c51380c50ac00034090b4251a04e0c0000,0x5fff7400b090236fbdfb99a3bee2cd14cf581ea779f3c124b8315f4d10ca2cd12eb63b1bfd1253073301a25d615fef893f19a2b830cb910d05c068b12eb621b8399801d8310ca0c2bcc6dab662001aa52463343f4e10ac00034090b4251a04eb70000,0x23f4c50ac00034090b4251a04e010002,0x4c3f4c50d800034090b41e1a04e020004,0x484049664789a289a489fea084532b04097bedbef79efe669a1a8f116b10d098a2689752b886a7f336b10ca69a18426897531260dbbd4c8c1b7eb5996c62368b12eb77c66a7eb58a441a04ba988b5886a7ea8012ea54513451bc40846451f1154c43f4c50d800034090901e24c69da0000,0xf896eeb044ac0046b7bcd9efd1efdd7091bcc21277c7f94ba421054af7c20d2b5cd10def98b3453496c352e0c4353f99b58efb8b9980d1625d62648c668cc04393d23f4c50d800034090b42524c698a0000,0x93f4c50d800034090b41e24c69010002,0x2c3f4c50f000034090b41e24c4e020004,0xaa2be9a2b9aaa64cd12a15c587c9bf621941ccc04c015e5fe66034d10dc1ccc6983fc488239a0900802bc886369aff447041fec3018e48cf7fa2393d1201005735fe88524dc1bfd11c9e8925328b99980c904c448fe0b0000340a0b4211a04ec30000,0x130c00cc0526609029f00e901b97374da6887543937ec412cf4492ec1bfd3283998014a4ae1c665e6600400515130b0000340a0b4211a04e6a0000,0x1814598fe0d400034090b41e1a04e050002,0xd59b27566cd300c30120827758669084450fe0b401028090901e24c692a0000,0x133c4910c6d88b588680e8904cd0c068094352e6dfaf75c4340fc991b48243da3344352d6194142137cae18dbdf442922424c450fe0b4010340b0901e1f469790000,0x3500212cc8d7f3164d191ab364aeb5886a54a289a0021012323c45ac41a1ed52a107448498becaf5459ef553dd70c6d343084d173211705282e7be44353f5ac5220a109be622f7450fe0b4010340b0901e24c7e9f0000])) (.b 1472 (.p [0xd450fe0b4010340b0901e24c69010002,0x6c4450fe0cc00034090901e24c69030004,0x3566c146d20969c048c83f622d6211b3df222036fe669fbcaa109b1360002653df2093f5ac0517b628de839a7acd9bfe61083a2a54496a0599150cc00034090901e24c697e0000,0x18598fe0d400034090901e24c69020002,0x42860bdf9f9affe31ac52b37fe561325533dfba21282f3235faffc68bfb266cd6b121a991f98c40bb57e6a639aeb26b9a6cd302e660340d5b1c7ac328791d8c31b45ec437bd756194dff318704c918c450fe0c000028090b42524c69a30000,0x1021009124042299557262cdd006108cfd12a1366f3244d1061941093f398c0428b8312a356b8b0fcea77ae67c4c15450fe0c0000340b0b42524c696e0000,0x34450fe0d400034090b42524c69020002,0x141509b32186869c7e212c52b18f78c5629ff9429ef3eb89b10021a0b58945ed8a37a0e0c4414892240b0599150c000028090b42524c695d0000,0xa9191b163542024104c109797f99805a8c663446d00501773050b2e4ccd9a6099b18cd882d180a080612e488636c498aa64b9b7efe6b130481c1df00e3166c301a4c599150c0000340b0b4251f469a40000,0x1085222e0f6e26b0fa002105210b72e2cf7e800849c212e93fb5cc548c8c1b7eb131a200d10d828c0b9efda228deb0682910d124256184a12fffe636c498a9084a1b7eff0318989599150c0000340b0b42524c7eaa0000,0xd599150c0000340b0b42524c69010002,0x34599150d400034090b42524c69020004,0x2598fe0d400034090b42524c69010006,0x9598fe0d400034090b41e24c6901000a,0x2c598fe0f000034090b41e24c4e020012,0x2598c50f000034090b41e24c4e010016]) (.p [0x6598c50f000034060b41e24c4e010020,0x4c598c55e400034060b41624c4e020022,0x8dfab09f598c500400034060741685c94060000,0x10420ea4090eb07157f8908a1224ec598c55dc02020060741685c94270000,0x1086cde6a9ca17e3dd766f3677cf5a14f7eaa98f65f04b6b2d612a6b529f7c6b6b1badc8f222cf4494f4faebda3c535a538976b6a6a6398c511443f4c55dc02034090741685c94710000,0x6464bdf7300459580208a024d021eb148921224828340266f5d9bcc4d7de444212c6222dc8b6b64a6b57cea717faf6827fe50929f938a2604045104c598fe5b402034090741638094880000,0x94083daf14d1a041ca0454366fc68579bb220b859ccc99e63013009804c02601049106a0260104e024a809804c024f7598fe5b402034090741685ce1720000,0x2c598fe5dc02034090741685c94020002,0x2598c55dc02034090741685c94010004,0x6598c55dc02034060741685c94010006,0xc598c55e400034060741685c94020008,0x8de0d09f598c500400020060b41e85c94060000,0x3b076266f9af27f2bad93a33ca7bc744983ffd88b11443f4c55e002020060b41e85c942b0000,0xfc94cdf848dea4e8dfb4bd0cff893d9cc6026013009804c288092208092208082b79582c0127bee68498098049501177350125404c024c6694d5056792c012401244202480092210441001124044c0809b02e66026a2c598fe5e002020060b41e85c94d20000,0x2598c55e002020060b41e85c94010002,0xc598c55e400020060b41e85c94020004])))) (.b 1536 (.b 1504 (.p [0xff0108cde211f5bbe442cde7e69021c5a93ee70bb7f25f04b6cf7a062480843f4c55e400034090b41e524943e0000,0x3378025aa9efcfaa0315b5c4258c54f7cd1aa0bcdff9c92ae63004b027fc605fdaa6a0886282fdda347e548bf35faccc9f9c73424bbb77a4211ffdff7395f992d8d70bb535abf99bcd9ad5939d1a379a94d75417ec754c7318a26c4450fe13801034090901e37494ae0000,0x2504a0ecac0124012401240045dcc004950130d9bc41348464a9684131dfd8826b1d689fe6108294c8de84a6305991511801028090901e374946f0000,0x2cb9a180d06cde210815735e7bd7126b344108490e6820d40cde2045eedd6f3ea976b14ac628429ef15cf5891f73dfb049f9f45fe2bf9092ae6b898599150d8010340b0801e2e0947c0000,0x250d9212b266c1aee5cd0c6d19bc423d629ff1c7d712fccd266c93c104212725acd105224a50434ff5221a24808466f14ac9c890a563142348847ac4876e7befbf5c41a422599150d8010340b090212e0949a0000,0x4c59915118010340b0901e2e094020002,0x7e08449d15118020340b08c1e374b9060000,0x44fd28100020340b08c1e374b9030000,0x18d9bd2d2f44c6a89cce1be1f7c9932679a8afe15fc2bf857f0afaeeb0df26339a8afe15fc2bf857f0afe15fc2bf857f0b5fff1809804c026013009804c026013009804c026013009804c024c4599400e8020340b0801e374b9b10000,0x1852bd2fd4b004c0248024802601262020a5599400e8020340b08c21374b92e0000,0x4c59940100020340b08c1e374b9020002,0x1859928118020340b08c1e374b9020004,0x267759915118010340b0901e374b9030006,0xd59915118010340b0901e37494010008,0x345991513801034090901e3749402000c,0x18598fe14401034090901e3749402000e]) (.b 1520 (.p [0x441130084450fe14401030090b425374940d0000,0x54295ea829fac0130226044c08981105697a4477a40bd2f4a6026013009804c0260130098049893260212657a25d9136d7a250d38b044c08981130226044d93360a3298fcc864498cd0841132534301309a17ff62ddea26262c5991512001028090b42537494d80000,0xc090841fa4c580084c8559915120010300b0b425374941f0000,0x345991514401030090b42537494020002,0x3b598fe14401034090b42537494020004,0x4c598fe49801034090b41e37494020006,0x3f250c4cdf820bf5237a82cf5bc157355a64c993264c99e63013009804c0260130b013009804c0260130098277598fe49801034090b41e524de6a0000,0x144598fe5e400034090b41e52494030002,0x95598c55e400034090b41e85c94020018,0x6598c55e400034060b41e85c9401001a,0x9598c55e400034060b41685c94010020,0x2c598c55f000034060b41685c4e02002a,0x185987681400034060b41685c4e02004e,0x19fc4352f825ff200e9001310768140085c0e0b41685c4e190000,0x5ef3f4c5004000740e0741624c4e010000,0x377c484f12fadabfca5d30a452e44128d202bc490d410a7fdabf977ef6f124351293f4c50140204c0e074161a04e420000]) (.p [0x5c143bd7b2c62090c46cabb44bea57003ca45f58f9d10ff2bfc102913461deb37be41086912a0853fa3f4c50140207414064161a04e570000,0xd12ff007feffb916d292e91b0f884bc877df46d5c7bf11fc68bbc43eaaba758ab8f7e25f526ef89259d46ab4ed27e5177e8bfa3f4c501402074140741a1a04e5f0000,0x93f4c50140207414074161a04e010002,0x63f4c5014020740e074161a04e010004,0x7c98d6fa059d331cc687f129dae24c7b98f0ee6b312fa3a9eff27586428beb6614f58913dd1024b8ddfcf319f3f4c50140204c0e0741624c69590000,0x68095ff01b6a16f4048de20d35f7ffd41a3ebcd236b504179d2cd769670cd74a25f12464baf5412d8c4123fa2afe293f12fa95cf35eaba025be01319c664be8bbf5798ffef81b5333f4c501402074140741624c698e0000,0x63f4c5014020740e0741624c69010002,0xd3f4c5014020740e0741624c4e010004,0x5f3f4c50e0060740e0741624c4e010000,0x33f4c50e0020740e0741624c4e010002,0xc3f4c50fc000740e0741624c4e02000c,0x97030e56030f4c8fc9f5266db46091d6f8902991b6eeb1e9f04978fd990efa3137c9f04b563f6096aae3c012a8243010cf429025b18f5fffc01ee67aa087fdb137ee3c124a25bb5f21eb0c450fe0b80007410074171a04ea40000,0x25c01080b4469c7d8eb1d1f2a0025c420f198f552112d1189bcbbe440522e9f95121e19e51c66c0df00e800599150b80007410074171a04e650000,0x114598fe0e0000740e074161a04e040002,0x135c559a21a24ec99c4389b048241a287125701a82f005ff389ad1344908a000820f9898c1131df40b359f5043fc931dfd800b3a67399ac324fb9f7d10a4e099ce4a8834e20e88a37a104c598fe0e00004c0e0741624c69ab0000,0x5ef450fe00400074140641624c69010000]))) (.b 1568 (.b 1552 (.p [0x4baa5d95521e8950247d56d410ead11950a8dfc3fea0317eaffbb75ec9992cc9e88166f889ad8fee4ba821ff08e84746cc450fe0c40207414064161f4696b0000,0x9f85789205a6bc6bcd723d2c806d7f4f4e672a0923d6b9beae0908b134479ef153dd2ea8f28e3b125a712e0bcd7aa8f73d9cf4561625c125487fdb319a9573999e740421ceb603cf7ed1349450fe0c402074140641624c7e990000,0xd450fe0c402074140641624c69010002,0xc450fe0dc00074140641624c69020004,0x1521047050d501c45999a1d6aaa37f3144d89b3412430c068b17dc090247dd559d10824a6355dfdd335c493887580a483127649eb01892001d7ba125eeb823a0504307146f420d4b8023204862348097847423acb6a541410599150dc00074140641624c69d20000,0x18598fe0e000074140641624c69020002,0x25c4105e6a8861085812048e79501e46be240a3dd6841741222f19fda8902aaee3ade5dfa3b6e8c1c30450fe0e000074140741a24c695a0000,0x87c868cd9a6004383bd1242025c422633c9327a6dba00954121a88478487b756198599150b40005c140741a1f469540000,0x97030e76c8484204b6b319e447a2365161e8808f38e7f77fab0c49d150b400074180741a1f4693c0000,0x53084be8b14005770f44050fa25f44233cedd58663550201880c712fb87a2090c0473fab0cd882393b34481441bcc599280b400074180741a1f469720000,0x2599150b400074180741a1f469010002,0x34599150c800074140741a1f469020004,0x100a94150928c0b9821098988402a1366f3268125496b51419c38983898389297260b3346f125be8daf5b146f5b37987112e2582f3eb949e98f4cf460e44c6599150c800074140741a24c7e8b0000,0x2c599150e000074140741a24c69020002,0x2598fe0e000074140741a24c69010008,0x9598fe0e000074140741624c6901000a]) (.p [0x6598fe0e0000740e0741624c69010012,0x2c598fe0fc000740e0741624c4e020014,0x18598c5110000740e0741624c4e020018,0x496104b01b2420497fbf8d45b5a4212e6314a4c6b96da7ad17c12c975c42d10b133239c9be66da345f04b0b6b884233ced12f9e85498f5797fff10f727af74f94d797fff38bf727c89b4824a69c5fef9ce7e401c303f4c5110000740e0b41e24c4eb20000,0x107d52a15c9fb27b18824a92e3c46912f2e5e476311b57b1014891f93e23658f88087137ee57c4b443dfab0c450fe0b00004c0e0901e1a04e5e0000,0x21f207341298970484d963261f21a75dbab0c92f8074686ae4c4a507da60070392526b880a507596d6c50130599150b00004c0e0901e1a04e6c0000,0x18598fe0b80004c0e0901e1a04e020002,0x970313912030c6a4c7a6dbb8c0c3180c459f16d43b5f93e7084bcee1e88dba06165f447b1171890a544c9eeff71e6cb3fa3dfab0c450fe0b80004c0e0b4251a04e730000,0x5484d8b188f44bd1625c0c0bb3aedd1ec30d8868c10a0820fae9e3f6ba76eac330310490c10a0c04b996c62243dfa2029c84fd5866c3013534599150a40004c0e0b4251644e860000,0xa2e0d2032e0d45734d9a2c98028b920039409ca6dcb9ba0a3dd8c4bd1625c0c061cacbe8f7e8f619b1129a2348634c12e096c622e7dd31fd5866266599150a40004c0e0b4251a05a900000,0x2c599150b80004c0e0b4251a04e020002,0x2598fe0b80004c0e0b4251a04e010004,0x4c598fe0c80004c0e0b41e1a04e020006,0x8dab0c450fe0c0000741408c1e1a04e080000,0xa9732aecc5497377c33626c9039a080eb11b47b0c94b93059373f4c121e47be0a6fabeb6392fa8be063f018fd8e91eb6392534599150ac000741408c1e1644e730000,0x1085845e62c9a5515cd344d9207166f3107d5557719fffaa039549c212a1799221f21b3162368c1c30d89b34c120925820faa4ff56197e66599150ac000741408c1e1a05a800000])) (.b 1584 (.p [0x2c599150c0000741408c1e1a04e020002,0x18598fe0c8000741408c1e1a04e020004,0xca65c1ef58001830240a3593140052530b13dccd162806d55706b9a20b662c46d58663498b010a2e481b0c6fa0010095598fe0c800074140b0241a04e7d0000,0x33598fe0c800074140b41e1a04e020002,0x34598fe0f0000740e0b41e1a04e020008,0x4b9b05f386683196c6bee825bd45f15b3a0bc63167d795f54faf80bf8f8f127a089aeaae639ccc7b0c450fe0d4000480e08c1e24c69500000,0x5145c1e7fff354cd15210f134e6c47a2368b12e06165f476dd1ec30d930393812ea8c2ccfa7d3325d8e5b25fe89218949e98d304baa264c50cc862059dbab0cd985b1301a4c599150bc000480e08c1e1f469a20000,0xa902ae6eb1001082a065c15b19a269a8453f4588f3de80420a812b3c4188425c1ccf7e87130713071307136065cd04862034475ee12f567bd7130b0e20b2e68284da81c4d994f7c8249fac0e26349599150bc000480e08c1e24c7eb50000,0x2c599150d4000480e08c1e24c69020002,0x18598fe0d8000480e08c1e24c69020004,0xc096e62c004260ca280bb9835032e0a13668253349897108c951f3faaa3a4530b0001c800c25598fe0d8000480e0a82424c69660000,0x4c598fe0f0000480e0a81e24c69020002,0x50d92840280bb9833084ab73244d9a6c0429383498b107d5557719fffaa03940c68000e900c80598fe0f000068130a81e24c69660000,0x313598fe0f0000740e0b41e24c69030002,0x2c598fe110000740e0b41e24c4e02000a,0x2598c5110000740e0b41e24c4e01001c]) (.p [0x4c598c571c000740e0b41624c4e02001e,0x36b3f4c50040085c1e078162304e020000,0x34011504e610b0cf85f4045f3cbbd742decdfc469e3e2bbbef9cf925dde0960fecd5bd613d7779f5ab79c7bd0ed7f3f27d7fd47bc42bc49497d48f77977ece24ba48e777df93f4c5014020d81e0701617c4e760000,0x133896f442278e05bd3effbce3e2ba2119495fdd56f4fdea72a913ce2b673096811bf3122ef1533f4c5014020d81e070161ec60490000,0xd3f4c5014020d81e070161ec4e010002,0x5f3f4c50f4060d81e070161ec4e010000,0xc3f4c570c020d81e070161ec4e020002,0x6c048d3a5d0f77e3d5be4478a88c182803f4c570c0231837070161ec4e210000,0x6003f4c57100285c1e078162304e050002,0x1403f4c571c0085c1e08c1624c4e040008,0x56f450fe004000f41e06c161a04e010000,0x2d1d15ee865299a2795bfe866fe23137affaaf5fdda24130568a36bf689069cd450fe0d4020f41e060161a04e400000,0x25af37f161263de28c862c642e7183dd7c9bcfc9fd99c302aaa9eb2e7d0526b3891f51471238f7ed9bf8b2f971dc6bab79c7bcf3afe1f20ab3896a17f119e5555567123af723893fbfa3de3450fe0d4020f41e06c191a04e8a0000,0x9450fe0d4020f41e06c161a04e010002,0xc450fe0ec000f41e06c161a04e020004,0x5ee854c0e6f6249440bdd09eff44727a686950e4f4e01d6026f915b36240a20599150d4000f41e060161a04e480000]))))) (.b 1712 (.b 1648 (.b 1616 (.p [0x260d3316bfa887bf508c9d388e84282b823a10a0c016bfaaeade75efb261f21a3010f7affc0779ca28e25bb5f3b5e84609c599150d4000f41e06c191644e640000,0x105d0494c4baa1ff49fea119b10d01dc77a40bb24412ced0578a1c5a40b05afe642e35e4fcacc729c49fea1198599150d4000a01e06c191a05a600000,0x51416051799a0d4498a3068605cc844613a710ef8475bc2b66830484d920ab0c97262232f8c4d920727a24a62d1d423302b4508eb78508262c5a3a8462599150d4000f42906c191a05a920000,0x6599150d4000f41e06c191a05a010002,0xd599150d4000f41e06c191a04e010004,0x4c599150ec000f41e06c161a04e020006,0x18598fe6d4000f41e06c161a04e020008,0x191285a3a3272bdd08c98bdd00615078c1fc85b37fdc23119b454173e0cca232046b25ee3147afe92dbfe9ab08076249762e1e809021c5992f7da2a0c55a2a1e570d0da241316137e349833e2fe0c450fe6d40085c3e06c161a04eae0000,0x11b0e6c3835ec3829196ccc1181181181135b104c84cd6f04c247b10600c8c610230a712d224a60b215094bc683ac3d42408817b9e0003320052f1000c5991568c0085c3e060161644e9f0000,0xbdd07c32b5ee71ad150f0494c5a2a1f1a6f5f7fbb0888afd8408408e201a388c49d15130001f43e060161a05a470000,0x6464612559928114001f43e058161a05a0b0000,0x55ba8641918c81e41920762e4b48a3999964bdc7b3334540d737deb04df7e1a0c0280caa5e0049c59928114001f43e060171805a5c0000,0x2a550559a024814956ea1906409cc8c644d5f260b26d7a1acfeb62e464487379991b6eb8aebdc08f15d0327a89eeaa20732e834192043873c494c04717272325c19935939be0b7b1b5e8652388cc659928114001f43e060171a061b40000,0xd59928114001f43e060171a05a010002,0x4c59928130001f43e060161a05a020004,0x185991568c001f43e060161a05a020006]) (.b 1632 (.p [0x464604849d1568c0285c7e060161a05a0c0000,0x42302bef4b7fe206bbef1a48914122923204d6f4b77f0d77de34902056c9d66463231918c8c6463231a6463231918c8c6463231918c8c644d19029620dd5246c419063932919008c08c08c08c08c359191b6610230706a5f92064c5992868c0285c7e060161a05aec0000,0x4d75991568c0085c7e060161a05a020002,0x65991568c0085c3e060161a05a010004,0x2c599156900085c3e060161a04e02000c,0x92a828add54144341aa4286503833928d824a62c940f2323094c944f732dd727b944a36431039bd8904cd12e084e21df604e2a288464a5c0011e2de15b3412533491ad3aca947a664715159f0322884669859915684001f43e06c1915c4ec60000,0x81180484cd1d6840385c7e06c1915c4e0d0000,0x106a5e1aefe1a9c4bc897912f225e44bc897912f225c500c11811811811811811811811811811810270409c7f5a04e081402319185e97a48d895f7a41348c8244e081382056810270409c10283224266463226859934648033247e06c1915c4ed90000,0x4b1023c496c4130c92320982302302302302268119097599346480385cca06c1915c4e430000,0x34599346840385c7e06c1915c4e020002,0x30d7599156840085c7e06c1915c4e030004,0x34599156900085c3e06c1915c4e020006,0xe1b272dcc06c117900d03359a4a3216e605c9a325c9362cd011865009812053241b0666cddc60f7360f17e88e488168a8336f0a5e62cd168a88030c8009c599156900085c3e06c19190589c0000,0x15599156900085c3e06c191a04e020002,0x4c599156d40085c3e06c161a04e02000a,0x2598fe6d40085c3e06c161a04e010018]) (.p [0x34598fe6e00085c1e06c161a04e02001a,0x56f450fe004000d81e0681624c69010000,0x16bf8217f54a32ef5ae11be7f50a57ba3c4fdd2ae6bfd11c9354c5a3a2b626c9e89299221b93d125ba603458b66feba62ade7cfe9f1a4c450fe0f0020d81e064161f0696e0000,0x68190821812efbdeb9a2f3fa40b210238b834877dcddf417316cdfd726f3fa2b1a2c5a3b201814450fe0f0020d81e064162487d580000,0xc5450fe0f0020d81e0681624c69030002,0x154450fe108000d81e06c1624c69030004,0x102ea8db239c7b124a205afe20a393ea7144e339e456cd8902ec599150d4000981e060161f4693b0000,0xe2e0d2136482382a78e2537d52e1dfe8508c99b546c903839980ab828412c891c466244d920a20bdc6228466cd81a038241253341253167beaaaab91da74f1d1453f428462599150d4000d827060161f469a00000,0x34599150e8000d81e060161f469020002,0x302e08280ab92974b828c44e24ff462dffc64647cfe9f1a0a0d05cca26cd160238b8343d9eb047040351e26d626cf7e8bc4886e686808737388c49d150d0000981e0601624c7e840000,0x92361b052868092117042f8d55705025301254a845ac4c4aa5090482602426c903828e23364c372766c4817669a0804d920717b785094c599280d0000981e0601624c7e8d0000,0x18599150e8000981e0601624c7e020002,0x1001c5c140ab9a6c047243821a1809ae2cc8c32831a91913362c9a136481c10d00e2aae2c1a30c9c150417d52edb5e84661061fc416763f3b5e8466de141c59334482f992f94c97938bf761db66b43ff19a8c328c2a02599150e8000d8270601624c7ecd0000,0x6599150e8000d81e0601624c7e010002,0x2c599150ec000d81e0601624c69020006,0x80c0b99570d99554671618173230ca0c0230a106d8ab0181217982954d828ca625f72a048e3dfa84662499b0660727785094c4b885b8679501e10bf8931cb7fa846634599150ec000d01e06c191d869a40000]))) (.b 1680 (.b 1664 (.p [0x1001c3648a646c1c8d86c9d9a2c04619418d14599150ec000d01e06c1921c77350000,0x1a5599150ec000d81e06c1924c69030002,0x4c59915108000d81e06c1624c69020004,0x18598fe6e0000d81e06c1624c6902000e,0x389739bdeb9abcfe902c0088f3fa00100450fe2300030c370601622069250000,0xb3df325c45555dafd828f788bf882c8a39472d0ffcf7e854f88c49d151040016437060161dc692f0000,0x2030029b166507b9b24d920ab1601c5c1a308c30b4090293d3602393834302e642232f8d509b164824a62d738bf673dd96fd0a119858baf9327330f1982c8a499c43be1444fb4ce84f8daf423a388eb785094c599281040016437060161dc69c10000,0x18599151100016437060161dc69020002,0x24646c1c9540e0829c5c10c6808c328250293366ac041b7850bd7c10efafa14827d7d0ade15b166808c284223cfe900a0c69359915110001643706016220787f0000,0x2c599151ec00164370601622069020002,0x96efe1aefbc6824524489c914190273231918c81399027320568c8139918c8c646323216ea9434c8c646cb7301b04506805a2762cd0c900d02248c18c06c114e4646129996dc99b162a27a8c2c5464646012245599151ec0030c5a0601622069db0000,0x34599152300030c370601622069020002,0x240598fe6e00030c3706c1624c69040008,0xdb598fe6e00085c1e06c1624c6902000a,0x2c598fe6e40085c1e06c1624c4e02001e,0x20fa98597dd504b0a216e19e5412941df7d1a6f8253eaa0a34a5177eee997bd6678a18ad8f7fb200e900450fe6e4001781e08c1c1b04e590000]) (.p [0x2d386165f6560313912112d11a4587a2023937df3a9f325cb19f84844b9010d770f44487137df19f04867ec121479dbab0c49d150b8000b81e07c1c1684e6d0000,0x2017324a9424104c4b8b0c52a048fa8eea1198188f441084344baa4a972c7b7508cdbfd11c9d9b1205104cd15cd50d12eaa2beaedd5864ae4c05223ad8e41cd371de902892c34599280b8000b81e07c1c1684ea60000,0x18599150bc000b81e07c1c1684e020002,0x805c98b45b971668a82700a2e0d44d9a1d6682017040074800a5599150bc000b81e08c201684e450000,0x4c599150c8000b81e08c1c1684e020002,0x80165c598ca6dcb9ab140270197069093d101a25c587a22479dbab0cbf3345897536e5f754063bedd9007480093599150c8000b81e08c1c1b05b700000,0x2c59915110000b81e08c1c1b04e020002,0x20325c9adc437bc52869a2e1de4a48c08805370241b334514c0cca6dcb9ab1400525c03828c0336a5706897030241a7d0483462479dba8465f98b344b8842c09069cf2a0315b6ec81864024559915110001782f08c1c1b04ec00000,0x34599156e4001781e08c1c1b04e020002,0xa5598fe6e40085c1e08c1c24c4e03000a,0x4c598fe71c0085c1e08c1624c4e02000c,0x133598c571c0085c1e0b41624c4e020052,0x34598c57c80085c0e0b41624c4e02005c,0x7f80843883003f4c57c8000a40e0841685c940f0000,0x177e3dd766fdc6a669dc84c715fac4450fe140010540e06816380941a0000,0xff340c13d95802480248024802480248026ff30130049d1215012750191bd094d4059915120010400e0681638094590000])) (.b 1696 (.p [0x1c538312aa9c11ff125336b503893b3a70680e26c1298713071364ccb752c750841d1342449104c599151200105411068162e8945e0000,0x14e020183fe636809804c026013009804c02601049582403117051909a337ec242607024a94ccb330126268b0e26cc8db20049ef2b004140098193df312622f759915120010541106816380bba20000,0xd5991512001054110681638094010002,0x3459915140010540e0681638094020004,0x4c4598fe5b8000540e0681638094030006,0x4450fe5b8040540e0681685ce1030000,0x449d155a0040540e0681685ce1030000,0x193de873deb4bc66978a7bf6d7a47d3264c993264c99e63013009804c024c404935f820c94083244041ca18c4cdfa4e45a64c99c739d6f059ace66798c04c026013009804c024c88b3404c0260130098599285a0040540e0681685ce1b20000,0x18599155b8040540e0681685ce1020002,0x4f7598fe5b8000540e0681685ce1020004,0x2c598fe5c4000540e0681685c94020006,0x5d9bf7941b8d09a084d01082084450fe5c4000a41606816388941f0000,0x3599183414094c04946b5c55bfff9b8438afd62666f3564e7560b37d68a95d124d59b2666019980744ff1242287165f344364e420a059bd7266c3bb0eecd2efd7136b54aa7bf4d8d28f580c41a530f7c4d8203b9efe4e02e092e7be6268a22599150e4010701605c162e894cd0000,0x489b8f1341994c09191b2e60f2981254a62c389b04a668b16084c1c495599150e40107016068182e8944b0000,0x2c4599150f80007016068162e894030002,0x311706aaa4cd98e2c51012104c0311706aaaa7162c046194849102ae0c6209909a0d2344018922098bd1201a9af51ff8c6b136cbbae7bd7131a2d6e25f54aa7bc76ca7bd0909a90933599150f8000a41d068162e894a30000]) (.p [0x3459915140000a416068162e894020002,0x1248de6adf7353dfa026013009804c026013009804c12b0386c906b55538b1602424e0188b828c134094c10c6cde09022639ee8c5131a2886420208084127759915140000a41606816388bb9b0000,0x2c599155c4000a4160681638894020002,0x95598fe5c4000a4160681685c94020008,0x34598fe5c8000a40e0681685c9402000a,0x1c4450fe5c8000500e0841b36c94030000,0x1608449d1511c010500e0841b36c94060000,0x10018425cd160021303581842d03458713071366421c4db3459a96880501254a60e56092a42a1f4389838983898389281254a6661c4c1c4d88421c4c80dacfee60711674e2c5cc59928104010500e0841b2dc94b40000,0x90c5e68ff9ba6a6026013009804c02601300824cf7a3024a94c58098d38c8c02bd14404127759928104010500e0841b36cb85f0000,0x2c5992811c010500e0841b36c94020002,0x4c4599155c8000500e0841b36c94030004,0xa5598fe5c8000a40e0841b85c94030006,0x4c598fe7c8000a40e0841685c94020008,0x93598c57c80085c0e0b41685c94030020,0x2c598c58140085c0e0b41685c4e020022,0x2598768140085c0e0b41685c4e0100c2])))) (.b 1776 (.b 1744 (.b 1728 (.p [0x345987685c0085c060b41685c4e0200c4,0x83e213e24aff7c8bdf8ae8010e404390013107685c000480685c2e85c4e240000,0x4ef3f4c500400024061742e24c4e010000,0x10b3e0f0d4e6630fa1be23433e8f199f43dce4a7d18fee18c3f4c50dc0201c061742e1a04e2d0000,0x41f03a5b12149685ff588e69de097fa471ee3dfa902359509de217ff633e669de097fee19fbef7ae0c437266860344bac2d09de4c52a91fc6395beb64a7d1a67ee5cf18b27bc315893f4c50dc02024081742e1a04e8c0000,0x343f4c510802024061742e1a04e020002,0x20263425a08d4099fc2583ebccf98553dee1df558593d5a0469002c8541f177d7b353e94889bf97fbeff70c663f4c510802024061742e24c695f0000,0xd3f4c510802024061742e24c4e010002,0xc3f4c512000024061742e24c4e020006,0x907d0758e907c3400213bd52a5a18992e4a7d1a61d43e5c38cdb43420598fe0dc00024070f42e1a04e410000,0x83e2d3bc4878487bc44fa31fc9de610a0d25eae41a829de31e55fea3d990a58cfa32cf27d18fee1e18c450fe0dc00024071743e1a04e4f0000,0x60264d60e325c1931835b435b260c1ada1a46d1207bb878632520fa053bf5f4fe7d186fabf86b686b62d2425de5de31a40242778e5611294844fe4fd4f50f86718d6c7f30029419c599150dc00024071743e1a04e940000,0x2598fe0dc00024071743e1a04e010002,0x69c598fe10000024061742e1a04e030004,0x605c5a266cd304c980d409c4cd83128306928200c648358262c06a0483480d8e60d6d0d07160d6d0d0282081ee1e18c9485ce9df91f8fa538e907c7d07188d6cff30038054598fe1000001c061742e24c69a20000,0x4ef450fe00400024080f42e24c69010000]) (.p [0x127e2c3940a779f983943ffdc33c9ae6886e4ec188682a507331b40d05c1c6119eb930693f7fff10f738e90750f8fa0e3026fc4c450fe0c802024080f42e1f4696b0000,0x481eea408684a9f8b0e66209a83399af3df235991a209d3f2625283a47e3e83a4bd1628de61444ff344dca12c34ad734f59b14498b09bf033450fe0c802024080f42e24c7e770000,0xd450fe0c802024080f42e24c69010002,0xc450fe0e000024080f42e24c69020004,0x1002cfe421cf900909de4c98a7fba3119e2004d83128bd81fe988c3b43494599150c800024080f42e1f469460000,0x1084d9a1a020035c495c8945c1422504262ad8aa1aa938301a2c9a1524a6fffea0290240bbf63c319b3566cd34410849c0334414892941a07e64a9f8f41e58f58a7fe518faeb356b9a7ac3293b277a28989599150c800024080f42e24c7ebd0000,0x2c599150e000024080f42e24c69020002,0x18598fe10000024080f42e24c69020004,0x81ea40868010d40450fe10000024081743e24469150000,0x210b2e0a54653260350321ae325c1892c06a08c64835b435b262c439021a821a805df2251707859734d81949d930541a4a8691b4481eee1e18cc4c599150e400024081743e1f0698d0000,0x1284cd93078c899b162d41ada1ad93164d021a4086a0093599150e400024081743e2447d390000,0x2c5991510000024081743e24469020002,0x95598fe10000024081743e24c69020004,0x9598fe10000024081742e24c69010006,0x6598fe10000024061742e24c69010010,0x2c598fe12000024061742e24c4e020012])) (.b 1760 (.p [0x18598c563c00024061742e24c4e020018,0xc8903c9de89a5e666508c60825dcca03f4c563c000240685c5e24c4e220000,0xfe0f598fe0040001c0685c5e1a04e040000,0x1a23e80200c92a0c92a0c9200c9200c9200c9200c920324835805fcc04c01c90319c679cd01b18c998598fe6140201c062b05e1a04e670000,0x619164450fe6140201c0685cad1a04e080000,0x123f169a1493400a934a0c01905a904024c12481209c24c122f4d1e690e69080af4f04c199a5073c0200aef4c95e6e9de4599155fc0201c0685cad1644e770000,0x4e6d5fbb75624cc6464646464642663232323232323232323232321230702b9070381c0e070381930324a8492a0c981930326064c0c926ef41930322e4599155fc0201c063c0ad1a05a8b0000,0x127fe5afe90a448b27fca44933ff2effb17d3ca498483a7599155fc0201c0685cf11a05a310000,0x9599155fc0201c0685cad1a05a010002,0x2c599156140201c0685cad1a04e020004,0x2598fe6140201c0685cad1a04e010006,0x9598fe6140201c0685c5e1a04e010008,0xc598fe6180001c0685c5e1a04e02000a,0x980a44fc428b3e358cc8aceac218c463040450fe61800024083585e1a04e270000,0xc0b83951cc02a0c92960c92a320d77e429064c8039f713144e40d324e098818ceaa86b324a7e203ef9b904e1a47a9ca4af4941ee61313f3f290b3f544c98a7faf9cf16188ef88a1f41386a02b387bc98599150f000024082305e1644eb10000,0x10b543e41e325c193905324a50664582990f90629256e1364c14219410980d550d54906b686928b2627fa04812086a086a0177e599150f000024082305e1a05a7b0000]) (.p [0x2c5991517800024082305e1a04e020002,0x1a0e61f67862116f4d9b36bca88fa2d97f1803200c813064c0c92a68326064c0c981930326064c0c981930326064c0c981930326064c0c981930326064c0c8b90649475991517800024083588d1a04ea60000,0x4c5991561800024083585e1a04e020002,0x133598fe618000240885c5e1a04e020006,0x34598fe61c000240685c5e1a04e020008,0x128b83c4cd83b50d4580d40942cb8306b00a80d54906928b260350276a83248032480326064906b62c64191528200f79241ac13160350241ad8b0692923184d28b7adf8110c623198598fe14c00018062705e24c69ae0000,0x20345a86a0c981930324a8326064c0c981930326c8e2cb82844964c06a2924e0d2526f9c600c6a4c4c10a494644c9ac98203642c4cd9316080c8e0d6c59301a819fc734231ada1ad8b264d021a408c68fe0240c4c5598fe14c00020072705e24c69d20000,0x34598fe61c00020062705e24c69020002,0xf920c5b604c1c0e070381c0e070381c0e064c0c981930326064c0c9819303260649006495064c0c92a0c981930326064c0c98191720c984a4598fe61c00020064209d24c69940000,0x693598fe61c000240685c5e24c69030002,0x2c598fe63c000240685c5e24c4e020006,0x2598c563c000240685c5e24c4e01001a,0x4c598c572c000240685c2e24c4e02001c,0x1104413fcbf185a220d54892021044d0e3183003f4c572c00024062002e85c942d0000,0x44450a82f9a12bf91cfa59f18b06222c4450fe1540001c061102e38094200000,0x2694d5056792c01244202488404910822480226ff31a684599151300001c060d82e380943b0000]))) (.b 1808 (.b 1792 (.p [0xc25ef84fc401124011302248089200892008981124044901124044c08922ccc6d044c08981126b55a210044c08981124044900449004495044950449887d0a7bd3bf2053bf63a52228de9283504503599ef18a24acf9a31b4d599151300001c061103738094d20000,0x4c599151540001c061102e38094020002,0x18598fe1580001c061102e38094020004,0x514ac8efc008022480226044c08981124044c08981130226044c08931044c12bddaa2c113022652b14ad7051a20a449c84150c84110644c2c1084148c06c15376a8b062888226406822610cf788c4989316088222c021245598fe15800024081102e38094dc0000,0x34598fe5c000024061102e38094020002,0x7f8084450fe5c00301c061102e85ce1070000,0x788449d155a40301c061102e85ce1050000,0x119be452328107281050809200208d0cf99efdd95e97e10ad3264c993264c993ff18381c0e070381c0e0645998db1161f424c45992859c0301c060d82e85ce1720000,0xcf94cdf853df84bd4343598d4e56993264c9c839c894d401c0c80c803819019019019420c802601262020a55992859c0301c061103785ce1650000,0x4c599285a40301c061102e85ce1020002,0x18599155c00301c061102e85ce1020004,0x8f7598fe5c000024061102e85ce1030006,0x2c598fe5cc00024061102e85c94020008,0x9a0435043900450fe5cc0001c062004538c94100000,0x180d8ab0b2e0ad001ae2605406aa86b2261668850579842642132141ada1a3f4599151280001c06168452f0944d0000,0x94364e4a954c980d40942c4cd9316080cb835b164c06a04a302a50986426070945c1426c59301a8120d6c98b01a8120d6c59301a8031ca5599151280001c062005b2f0948d0000]) (.p [0x4c599151740001c06200452f094020002,0x2e97e10c89b00600c884112645213bc69de34ef1a778d3bc69de34ef1a7793ffc9df229df208c67551608981130226044c08981130226044c08981130226044c0898113022604498822093599151740001c062004538cbd990000,0x2c599155cc0001c062004538c94020002,0xa5598fe5cc00024062004585c94030006,0x4c598fe72c00024062002e85c94020008,0x133598c572c000240685c2e85c94020018,0x2c598c5730000240685c2e85c4e02001a,0xa021a8133e8016109f31abffef84b022824835135c59a0f797e345931be7d0027e801600439003f4c5730000480a1b02e2384e5e0000,0x4ef450fe004000340a1002e1984e010000,0x15e600365c582854fc42264cf24c465bfdc33c437be40e4c589f88465b1c4c5c51cfee19f13b857264935c1eaf45809190ae1f47fb10ca480021bdf2ff331b4188682e6634d45ed9a4c450fe0ac020340a1002e1604ea50000,0x1205c5408f9804fcc8993dc7a0fff5204630709f3097910defd0621bdf27f7a4c5a3e6106f7ae4c99cf984b9226cd262f13273450fe0ac020340a1002e198596d0000,0xd450fe0ac020340a1002e1984e010002,0xc450fe0c0000340a1002e1984e020004,0x42dc6c3c8983418897207262c54830973498a013b709b0fe92319b264e6618d2071660293b435b2444a57998c28054b83d5cbfccc69a8b0635b5b10e4c599150ac000340a1002e1604e910000,0x30972443f4189b06253458081706615e612e489b34992319b040218d2a717b040bb435b34599150ac000340a0d42e19859580000,0x6055c98b0003210846c3029f222eb998da0c49e86348201516020555c98274fc4283be7f70cf26b9a18da4c918cc6599150ac000340a1003619859750000])) (.b 1824 (.p [0x9599150ac000340a1002e19859010002,0x2c599150c0000340a1002e1984e020004,0x18598fe0c8000340a1002e1984e020006,0xa02ae4c19812055cde62800a4028b83495443f45930001d201b10f93669b01004e09897030c5093ddfee18cc693160240b9a0231a3e80040245598fe0c8000480e1002e1984e950000,0x34598fe0f8000480a1002e1984e020002,0xc027e642c25b8f41ffea408c60a043900450fe0f8000340a1b0411984e2a0000,0x100605c1c2cb9a6c0ca4ec98b040869021a818c6049557164c000c84211b04a49f226c186369a26cd300c31a6130421021a584d930f342109b0fc935c186368b146331a2c599150d8000340a144411984eb40000,0x2004a2e0a325c1c4e4302ec5930c06c54086a06325599150d8000340a1b0521984e390000,0x4c599150f8000340a1b0411984e020002,0x3b598fe0f8000480a1b0411984e020004,0x4c598fe118000480a1b02e1984e020006,0x906106c399ae2cd266e8032043900450fe118000340a1002e23867290000,0x80128b83c2cb828d105224af31606109b220c0c630842517078587a6c0ca4ec98b04a2e4a0435031940cabb98b0003210846c3649f226cd0c6d0624f431a41242a2c048421361f41aa8f498f431b49923198d262c59915118000340a1002e23867db0000,0x93598fe118000480a1b02e23867030002,0x2c598fe730000480a1b02e2384e020004,0x245598c5730000480a85c2e85c4e030018]) (.p [0x34598c585c000480685c2e85c4e02001a,0x3b5987685c0085c0685c2e85c4e020070,0x95987685c0085c0685c1685c4e010072,0xd5987685c0085c0685c1685c26010188,0x25983a85c0085c0685c1685c260103ea,0x65983a85c0085c0285c1685c260103f6,0x95983a85c0085c0285c0a85c2601042e,0xd5983a85c0085c0285c0a85c1201056a,0x25981c85c0085c0285c0a85c1201067e,0x65981c85c0085c0085c0a85c120106a6,0x95981c85c0085c0085c0485c120106ac,0xd5981c85c0085c0085c0485c080106d4,0x25980d85c0085c0085c0485c08010700,0x95980d85c0085c0085c0185c0801071e,0xc55980d85c0085c0085c0085c01030726]))))))))
private def data : Store := ⟨vals,rows,model,codes,10⟩
def ok := test rule 5 13 data
theorem finish (checked : OMA.Tape245212.Before ok 1839) : Deny 5 13 ![⟨2,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨14,999999999999999999⟩] := by
  have same : data.vertex 1838=![⟨2,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨14,999999999999999999⟩] := by decide +kernel
  rw [← same]
  exact close valid _ _ data 1838 checked
end OMA.Tape5_13_245212
namespace OMA.Tape5_17_245212
open OMA.Box245212 OMA.RankTape245212 OMA.TapeShared245212
private def vals := OMA.PageTree245212.get (.b 48 (.b 16 (.p [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,17]) (.b 32 (.p [18,19,20,21,22,23,24,25,26,27,28,29,30,31,34,35]) (.p [36,37,38,39,40,41,43,44,45,46,47,49,50,53,54,57]))) (.b 64 (.p [58,59,61,62,63,67,74,75,78,79,80,81,82,83,90,91]) (.b 80 (.p [96,101,102,150,151,162,163,255,256,7533,56320,56337,60018,60041,64353,64363]) (.p [0x11f71,0x129c0]))))

private def rows := OMA.PageTree245212.get (.b 96 (.b 48 (.b 16 (.p [0xd926dc982f5eb7af119a44084c10a206881a228487180000,0xfd6d4216ed0b23823118847d1e6d47272d0a6e4470a91a20a882343468a300000,0x744c54ff7d7af3ae6eb2293cbff26e3891c59d086089adeef35f4b75a2ce901ffdebd7573cd0466eb2293d3b4a779371dfefb50a2cc8591c3e527a04b264c577594b31d5c46118a4f08c5a3018a91a20a882a26c68aa00000,0x540c4c10a206881a22868a050002,0x48816410a202880a20c686060004,0x3692dfada8fc29751c98732bd6a756ea3839547250b244a88004e90a2068810e0cf0f380000,0x2623d44cb820ae8e0a254494e91a206881080e89f1a0000,0xe06112040f07f897258d0b458feb8c1011411574716929dbfe915e3d86b07ca88a34afae7ea5a367cc8e6d7490d6c02da468d68eeb458b9cbfdfedd67f7c13e647043215b5ecd163fae207c1d4c9a18e91a2068810e1689fac0000,0x244e90a2068810e0e89f020002,0x24496410a2028800e0e88e050004,0x27879796a397f30122600e91a200080a220e0e180000,0x4c98ad025933c98af6eabb003cd43c19bae800a93755461957eb9cf2ce910202882a220e0e3d0000,0x695e00a91a0082822020e0e070000,0xda16400872e697b42d32187d2b152e8da5bb4ba8e6fb1b97891c38c41e5648321484481770a91a00a886202090e540000,0x13267ac87c7756da16990c3e910d14c14f5c7bd24948c42c295895a4a16d4815002da147695fadaa4e4c18a84ab18f51c0ca91a00a8862020e13710000,0x34a91a00a8862020e0e010002]) (.b 32 (.p [0x18a91a00a8822020e0e010004,0x4ac8004e16a00a8822020e0e0a0000,0xdb0e91a20a8822020e0e030002,0x27819ea7a6684d025bcb4592ac25a93c31ec4b18b0a91a208282a244e0e2f0000,0xdd72caca910a0a886a24490e070000,0x1c115f34b0d679fc819fb457cf6fb4287832670fa1871d2f40a470e93cb3d3162934096e605f48fdc54210c59d2ea052b45aeafe71671650ebe599cbefa5bada8e1f51c9c33992a87581a2eef02fa58dd2b15624a91a21a886a24490eae0000,0xca91a20a886a24490e010002,0x1e19692d9817cf5c62dd9863d23efc959a0a825e8014eb7a0db8ee9a93406a3e38f5f23d2ea3e320ca91a20a886a244e13530000,0x34a91a20a886a244e0e010002,0x18a91a20a882a244e0e010006,0x99315be715550764879bfee6f79f710964cd5af98e827427f51c1a9b8bdc4287dc401b7049e5ca4e7b3797af5329ab861679684b44ce9ba20a883a24490e6e0000,0x9bfeeb9d9054839804ce5650e9ba208383a244e131a0000,0x728b3fff331c5940024f7d5bcdfc2bd759062ed33498ae3377ddfa7fe4d7cdb42d262b8c019aba599e880054db42d076965a26f97eb770c0c9eef3000c4019fad124241a293dde00b70e9ba20a8884444e139d0000,0x1baaeeaa7a6eba611ace9b0a0a888a28ce13120000,0x50bda62c02bc408af3d29eb8c645a52bd13a1bf73cb96bdf4a8ef8f78c99a7428f5e3524e80040f33d071c192740395d72686015f27bd78efa49d00c67062c5ed5e8bd7ac10c126ffbaf790f22cf259a04b193374e9ba21a888a28ce13a20000,0xce9ba20a888a28ce13010002]) (.p [0x24e9ba20a888a244e13010004,0x18e9ba20a883a244e13010006,0x33c4e96a20a882a244e0e030008,0x8e91a20a882a244e0e01000a,0x24e91a20a882a220e0e010012,0xce91a202882a220e0e01001a,0x18e91a202880a220e0e01001c,0x1675892a0ccc0082c57091dcc099f30a0ba778c8c3ffc0fa956efc02a37e10cf6332c68b7cf9f339985b6b183ff80ddad6f7ee47f1167f5dccb1bcf62d12c62f07c9e71bdaeb629f41230e91a200080a22289d970000,0x1a2e9de2337c11d3d7bc447a23be4cf5af1c7d7bc64474e4f802be8011c322e9de30159ea77e48dce20c7bf8f44622bd9f0387d7bc70a2b359af7bf9e47addbf8c9bf4646560cd5f1126f906fe83088c16c7f5e571afb1e8cace910202882a22289d9a0000,0x46f4000f00ac737200935fcde7d0bf3f2231663834685ed3166401f42945293e1f325430734ab494a84b7261d68a60b690258c7ac83345d4fac43ec7d8c598a91a20a882202289d880000,0x20455ffc1d8f773500e9ba208282202289d130000,0xff69075b0c7890643b1006480e9b9c0a886162599d200000,0x3f857bfd072d00afdcacc950ae949f1fe5df064cd5d00e4caf47d6ea41310a5b34a863fc6dfd2cac10cdbf42188500e49591c17e847c1ce02d252a14a9e240a904c3ec3da141010ce9b9c0a886203199d9a0000,0x150e9ba20a886202199d030002,0x11bd1baec41a019f5a1779bc2bdfa539fd69b50c982208fc620c12ea7e62c51fd71928de9631e80578ae7c6b1066f72fce4f613458a4d79e22221fbe5d218c63d0421cc00ec401b72668b9f1157ff0763051fd71a03e4e9ba20a88620228b4a60000,0x34e9ba20a886202289d010002]))) (.b 64 (.p [0x144e96a20a882202289d020006,0x8e91a20a882202289d010008,0x6855e69115e34fef934a23110d12f0353fc69a40dde06ee4fe5a2c1501a0053358cd0694a91a20a882a24689d4b0000,0xb608e66404736ef04202020c6269233dad47d73dc9f99a0ec62f6b5b4c322e5b5e8c99b7238453c2ff75a779e99a2ae6a7bd31f66f28bb400bd098b0e9ba208282a24689d7f0000,0x5f1f538c5dfae32462ebf11ace9b0a0a886444599d150000,0xb022bc52890a5f16f821b14a68dcbdff499b5c18b280737c114a0c983bb682be6fcde15f3b8f47bf2e876e463b723d1ef19aba1159e67f2e8f58c3e42bac85164c598e9b9e1a886444599d7f0000,0x30e9ba20a886444599d020002,0x9a40857ab186b102bd00dfe5cacd3435f468afeaf119a7a0ce9ba20a886a28d99d300000,0x24e9ba20a886a24599d010002,0x46f42c17cc15f3751e8f78834031057d6be923e71e8c8a2b44ce9ba20a886a2464b42f0000,0x54e9ba20a886a24689d020002,0x144e96a20a882a24689d020008,0x8e91a20a882a24689d01000a,0x24e91a20a882a22289d01000c,0xce91a202882a22289d010016,0x18e91a202880a22289d010018]) (.b 80 (.p [0x184f10a202880a22288e02001a,0x168ea120e3d400e98015d100488800579fa20688448490112a0000,0x12fc481dd5ae1b7738113d593ddca34c10f406ae8d011c93c33bcffa264dc88024444d6a1a206885a294c13500000,0x27ab5c4068d432d6a10606885a295019110000,0x227a6492444a4598c0092735d2516a1a210585a295019220000,0x3e0ef837cd357076e20048024e7ae334f382783280064ac4e5002afe5efc077d280345329011548123d759e32a14031321a21288c78950196d0000,0xf8cf4b29815e21aabd719043e8613262b397e6ed5c400ea06567e08af1df11c6d47cdce492483599ef822ff4013b8ef8c9fabc912adb262cd2abc552a5af9e89038f59e96dc770efcc78450e8ca99989b31dcc5660d321a21288ca2f5019a70000,0x25321a21288ca295019010002,0x557ee0560a6ea3906a85269304f5f574241a0856a7a21288ca2950192c0000,0x96a1a21288ca295019010002,0x196a1a212885a295019010006,0xd6a1a206885a295019010008,0x348579fa206884a29501104000a,0x2881639fa202881a22101006000c,0x2e8037752ede2347d6415bd94402d16aaf8483af5740122239bd89028800581fa2068842021d24470000,0x30466622822ebfaba0e6f6249627030884956a1a20688516268bb2b0000]) (.p [0x3388308c8b0ad6a1060688520328bb100000,0x38b1021373816a1a21058520328bb100000,0x76f91dcf1ee57444d5d611137f4ab458a8de811d4c451140678f73fe7d7574462883cbfbb7a822e589b9d114459c1070d0d23d0cd47c3cbffc483502c972d32c0870d7811c4815c12b0014e20019335321a21288c20328bbaa0000,0x26bc1531159c584744518b6ba52228208fe80d5d085060856a7a21288c20328bb360000,0x96a1a21288c20328bb010002,0x196a1a21288520328bb010004,0xd6a1a20688520328bb010006,0x1a0c581fa20688420228bb040008,0x2449639fa20288120228a105000a,0xfe266fea39000fb77ac666fea3153b5a0507b66f589b31006e440a7c025601921a200181a2468a1420000,0x1afeb19ecb7af7ac4769dea1f7d28889f7cd847b5cfc467c35f0faf7aef78c9f12db19be801942611ad9210202884a2468a1450000,0x3680164ab631203ac0383100488018a198084844445b21270000,0x7ea3d37cf7e814dfc6a8bbe5faa89f8ca882d3210a0a88a4445b21200000,0x7e0dff4d15b4d0471a0dff6527380d1650bad41bf8bfe93268528a0a99400a3d5f3bde27d4f07e942996d99cbf509071ea0074c00ae8802443931321981a88a44455a1800000,0xba26788d4081e8ef9a4d735fe41d1f05fcac0663d471a0e729b2939c068b294e5efa92929568b345282a65002e53fa1fa50a658d1321981a88a2e45b2c780000,0x2c5d0a514c96b7bedf3fe9a29418b1452400a52dbdd199321981a88a4461b2c330000])))) (.b 144 (.b 112 (.p [0x25321981a88a4445b2c010002,0x35321981a88a4445b21010004,0x45421980a88a4445b21020006,0x12e2401b886fe2fe0a001529fea40a8e6ae0aca14dc88e1c1ca156f922241ba200c80058a9980a88a4445b21550000,0x98a1980a88a4445b21010002,0x3b1921a20a8844445b2103000a,0x3f88166ef4b4f63266a57a04b0269ac723266fb1ccf8c127a562d396c79487907b400b49d2a139315631321a208484a28db21580000,0x2f7cfff7a9dea2b271ae57a77d1afefaf52ddf3e8e337f1aabe78e9baf87315dd73efc51911ad3210a0a88aa28db213d0000,0x465d5d1803ae8573332330b8bf8ae47035d1807f011dfa3a42b193a3261d5e3cb5a4962663e90a514cb40b572fdce37fd160a9baaefe229418b14524094a42bdd19a1f5321a21a88aa28db218d0000,0xd321a20a88aa28db21010002,0x1454a1a20a884a28db21020004,0xdb58eccd5248870796edde8e2cd6ef400350004de49ed0520d41493e202560192aa208484a28db21490000,0x72f5cd7c1df3f8ae1feef1000ae88024447192aa20a88a708d5a1240000,0x7efae230ce066639fad92a0a0a88aa2e55a1130000,0x3f744d6be413f75b9b394d360090b2bf7ad51bde3934fdf3f88cbf18e8a0c58557ffc821f5838e499a4c13f7cffa7a04a2ba700eea3e0c3af07be6806ed5f3d11d4f7c9994df915d1226bad9992aa21a88aa2e55a1970000,0xd92aa20a88aa2e55a1010002]) (.b 128 (.p [0x2592aa20a88aa28d5a1010004,0x246514c91b74ef7ce75493136bf688e4f44834015215a87d15b64df41af8efaf19561f83192aa20a88a708db2c500000,0x11d67c31f5ef1931d77fdbf8d2801d1ca2b88355799464505cf8bfeb4b4ee75a0d94048cd98811d6ffc771828573332334e0c90f207d0e9f7ffdf6faf93045f8e769a0ac8c98bc4df0faf78c8a8d6b03a0d92aa20a88aa2e5b2ca20000,0x2592aa20a88aa28db2c010002,0x3592aa20a88aa28db21010004,0x1992aa20a884a28db2101000a,0x9921a20a884a28db2101000c,0x25921a20a884a245b21010012,0x816ef3f86b9f599bd6cdfb126288a7ec3da62c0685ccdf633296efc00ff83c680165b3f68532139307631321a20848444468b7550000,0x7561061dc11153dff77ed9457b4a9f3df3e075585dced1d45911ad3210a0a88a44468b7360000,0x94830d68cd0fffafb727cfe9af97ccb59c7dde7c64c776f99a68a3eb20c588f490253b797c7d8cd9ca2c86728b99ca0ce527380d162ac37b7335975fcbdff415f6f46658d13219a1a88a2e461b78b0000,0x2f885246f6e54feced3219a1a88a44621b7110000,0x131321a21a88a44461b7020002,0x1ff00d1bc4097be6fbdd75d3dac600117375f4c51064414207d4884c4d321a21a88a44468c43d0000,0x35321a21a88a44468b7010002,0xd321a20a88a44468b7010006]) (.p [0x1454a1a20a88444468b7020008,0xec11608b3c8248831157ff998010034408a2412a3350192aa20848444468b7390000,0xc3d30037cc80375b5c11a19bbb78877c1be2ae904c91400314e8800447192a940a88a2e461b7440000,0x5f21fad92a0a0a88a44621b7060000,0x5bfe0282bdf6eb7367283285162a4294532cfefb55bf6efe8a0cd48528a0df06fea37fda9069c59aba04a77cff902514ba8f83262e5fbc51aac6d7ed11cdd10a0c0152db19f456d9992a941a88a44621b7990000,0xd92a940a88a44621b7010002,0x13192aa20a88a44461b7020004,0x2b7ef2ac419826c45047098e1c1056b890a2c546f4298118830404bd644cc127224cf820ad7d5d6ddf155bf6e5741c0a823e6f76f5d98c53e3d064c5e3794084966f3acf2c9535ceb688a22837e220d92aa20a88a2e468c49f0000,0x2c0dc565ce21052d3e3d145057ba1d3b9a4c58b7d4cd7eab7edcae8a2324078dd2ebda3d9bd760ee304eb4c62c50fbe7d73cb38623a22220d92aa20a88a44628c46d0000,0x2592aa20a88a44468c4010002,0x3592aa20a88a44468b7010004,0x1992aa20a88444468b701000a,0x9921a20a88444468b701000c,0x2f98deda036df3e7cfdfd80d83bc178a19e84cb78e6ab19c2f7cfaa77aac64663c54a1a20a884a28e8b73b0000,0x2685ffd8e7b66f58b77c9f41233939adde3199f067b198c5e14de662778132735bbc38e63b6b193061fc48c26f99df0428cf3c59636bc629f0d918b192aa208484a28e8b76c0000,0xfe34083e9de78d021762af9efec9de7ac5a75977ead92a0a0a88a708e1b7240000]))) (.b 160 (.p [0x586f6f443e9fa3e96dee9e5f3b9b3b8b176d612c69a96deee5b8f56f7cee6cee2c5db5a96052dbdd193356aa8018a0a708e1b7570000,0x12dbdd9b77ef3b18291b74ef78ca4b650861f3fe39a91b74ef78cadd94213e9d0d7fc28b0592e8018a0a708e1b74a0000,0x6192a9618a0a708e1b7020002,0x8ca0d92a961a895708e1b7060000,0x1992a961a88a708e1b7010002,0x3192aa20a88a708e1b7020006,0x48d3332a283941e34902dc7ab76b7ffa6c6334138c8dde4c83d3a15cce5bffd0f58cd262cc735bbf7406c57329000efaff7e627d93bd5623a0d92aa20a88aa2e61b7720000,0x2592aa20a88aa28e1b7010002,0x1f009cc684b691a67335817e0b7db58deffe7b5b8e6733182b6f4a16639ed88b77ac13a98cd262cc70df7944eeb37be7ceb4dfee3debec3e9fa001df6fe313ec0a8c5743e592aa20a88aa28e8c4850000,0x3592aa20a88aa28e8b7010002,0x1992aa20a884a28e8b701000c,0x9921a20a884a28e8b701000e,0x25921a20a884a2468b7010010,0x35921a20a884a2468a1010026,0xd921a202884a2468a1010044,0x14599fa202881a2468a1020046]) (.b 176 (.p [0x2557cefa0356b5ebdfa57bc775611a353cdb921cfa200dd10a499412f880108e2cfdd2e1c83a200510860a77c406ae844e3b4a202884a249d246d0000,0x5ee873f8ea51638e20e88517a0a75ee30e098e209d7b8c3cce95678d962174f69a13345be08af082b075d0109b9d1140450455ae205056ce061d5d0906ce5355bef98db018fb1205d0953a20055d10a6e4428b4820b5a2028844e528bbc50000,0x9de04e77d60233d5cf802e4fa015dc8271f0095046b420b5a200484a2a28bb320000,0x1ab80eae0b5020288aa2a28bb070000,0x2323cc96e3dfeff3faa9ffd7ef90026f800320b5a20a88a7ca22bb250000,0x17cc86221f30a3a77cd2331ae8d342355e651911ea3e2ca1f44a453e88034024917fd57ff11a373b9f74efdc686b1efdbffd8c66821ffd7fe73a4fde757ae63a20173d124b274e01509c9990cf88919a0b5a20a88aa2fe2bb9f0000,0x260b5a20a88aa2a22bb010002,0x8be08e9ebde30766d93b6b01a6bcca23d47c594df42445df4400bd0937dffec45dd2db5b399cc3e2026b437ffb4efff1598ac0ca4093f7ce459cc46620422f00ab1326f9f510233158d20b5a20a88a7ca28c69c0000,0x17cd174ef1159153286ae3a23e989dfbff5ccf9c6f336efdfface18c5933e241a6037fc442319a2fa8eddfbff5919b18cc86319a0b5a20a88aa2fe8c6610000,0x260b5a20a88aa2a28c6010002,0x360b5a20a88aa2a28bb010004,0xe0b5a20288aa2a28bb010008,0x1a0b5a202884a2a28bb01000a,0x8c60b4a202884a24a8bb03000c,0x1a7d04e440057c00904a647db71e18c1353bdfbf7231d161932fe802e8b0c589de0a6b3e0233d5cf802c668409c7c0270d401464002d2727a4d7cef806ee4005a502d2935f0024163c2a202884a24a8bba60000,0xa3b4a202884a24a8bb010002]) (.p [0xc163b4a202881a2468a1040010,0xa39fa202881a2468a1010012,0x2639fa202881a2228a101005a,0x69639fa202880a22288e030066,0xcfe410a202880a22288e020074,0x26410a202880a20e88e0100ac,0x316410a202880a2028810300b2])))))
private def data : Store := ⟨vals,rows,model,codes,7⟩
def ok := test rule 5 17 data
theorem finish (checked : OMA.Tape245212.Before ok 183) : Deny 5 17 ![⟨2,76224⟩,⟨1,76224⟩,⟨1,76224⟩,⟨1,76224⟩,⟨18,256⟩] := by
  have same : data.vertex 182=![⟨2,76224⟩,⟨1,76224⟩,⟨1,76224⟩,⟨1,76224⟩,⟨18,256⟩] := by decide +kernel
  rw [← same]
  exact close valid _ _ data 182 checked
end OMA.Tape5_17_245212
namespace OMA.Tape5_19_245212
open OMA.Box245212 OMA.RankTape245212 OMA.TapeShared245212
private def vals := OMA.PageTree245212.get (.b 32 (.b 16 (.p [1,2,3,4,6,7,8,9,11,12,13,14,15,16,17,18]) (.p [19,20,22,23,26,27,28,29,30,31,36,37,38,40,41,42])) (.b 48 (.p [46,47,52,53,54,55,56,57,58,59,60,61,89,94,95,96]) (.p [114,115,118,119,10604,20709,22194,23584])))

private def rows := OMA.PageTree245212.get (.b 64 (.b 32 (.b 16 (.p [0x375598af93c33269d29ce85a4e8006a205653dc2dc3dd034a280000,0x1e1e64ab5fc1657a3e860d0b5fa16ea11f520547244caf38273751c9cb429b911c653dc2dc375148e460000,0xda4d260ee2005408da4a95e96aaf9ee9ac8bd56cf8d5b28ada862debe6f9c6458193d334dd56609d0b4e84bdc39c9e1534dd740052653dc2dc3dde48e700000,0x33653dc2dc3dd048e020002,0x12205b13dc0dc0dc4488060004,0xfd9972ac450450410e20048e6f6249502ddc0dc1dc1119845b766f4920f95106440f4afe3e0860d68b1fd718286ba52edeb045041d5d1cdc8925875326108babe00f992a1be27f90a6ef89201cc0042228af5b75b56ef51c1caa00dc880372205b13dc0dc0244dd3dc0000,0x1a40133fa4379bce66b8506b00ab1f23b031b41c133fadfe45a050609f009580653dc0040dcadd34a0000,0x6acfa42c4fad4efe39b88e5befe4b8ecfa0534ef5c555bcfe550474fbe20046fc543f7cd054e7af8801d3088b653040dc2dcadd3520000,0x6200653d8210250a813070000,0xf538c5c60b4d3102dc550a8130a0000,0x58115e2945bb33753eff2e8f53efc62c5da42c77569a4c7756da169324f5c3b08c365d0d07b5a3bad0663badb42d2649ebcaac0db5607580c4a55b50a2d004cd4d3d85dc550a8138d0000,0x11513d82dc550a813020002,0x69fb97aecdd4a0c013818e00e8803688032001655d82dc550a813320000,0x2653d82dc550a813010002,0x34653dc2dc250a813020006,0x18feebde45e459e130c8b805889150a0e72b006e46ef494f4ac99a7f2d049e1e98ab158653dc2102dd58134f0000]) (.p [0x6d27e7861df193d520661a78d33e90b980b3d71ef902fbfa9eb8c645be91dd2b10efa9e93f19a2c126fd2bd2d55e3bfb9f0dea96bfa6bacf454dd72c88c11513dc2dc5dd5813730000,0x23cd3cc8524f7ef7af19a79c1ae78218fc67f5201a88526bcc80077788037684a3a900d4481520657dc3dc5a17613560000,0x1bf77980666390b657183dc5de96130f0000,0x8eb318704de4df720a4f44048c657dc72c5de96131f0000,0xeb6f5eb7afd27c1e175fe52693349ccf4989716d57ee62b3073d7a59d2740035000eef1000c9657dc7dccde95134d0000,0x3e004239fdc9584d255df859266dc9ccd40af9260e62b3071c17af5a6bfbf8ffe5c6347af315c62fe46fcf4491e3a0c9657dc7dccde96155b0000,0xd657dc7dccde9613010002,0x6657dc7dc5de9613010004,0x3657dc3dc5de9613010006,0x5d3657dc2dc5dd5613030008,0x7dfaeb94cf6f78acf3f1cbe3eaa8011cb657102dc5dd58191f0000,0x2cfa5ab97ef9ff4ddc62c5940397fd34529ae5eb8abdf05735f0456d1002381935d1e39edafcba1d00e91cd5d6428b34657dc5dc59158195f0000,0x10af52267ae2c05f30be88327e2990d55e29464dceb8578829252ddf06b415c5679aca926e49a0cc8057c83243affdf6fbfc7758cd10ef8d723166657dc5dc5de5819770000,0x9657dc5dc5dd5819010002,0x3657dc2dc5dd5819010004,0x61655dc2dc5dd5813020006])) (.b 48 (.p [0x2653dc2dc5dd5813010010,0x6653dc2dc2dd5813010012,0x9653dc2dc2dca813010014,0x867eb7cc4d04daffe688115209dcd60241167d4d6441c9f92e983b158653dc210250ade13e0000,0x237a04bfd4f9d685d53ea92f77817d2dd693060bfe08af1cd66bc7a862c88c11513dc2dc550ade13a0000,0x3d77778801180b657102dc550ab610f0000,0x30d0bb78e0ff77800c401859dbf738043b120c78902a1419c657d45dc538ab61370000,0xba1db919f30f6dd00e90a2c657d452c550fb611a0000,0x4a53b86ce34a3265f4cd3451f5934a26e5eb8b1bbe0ae0c59403c4ef99cbd71685f32bfbe09f34d7f2200c428d6f97e8490a2ca4bda5bab4c8f89ae3d83959a68a3eb20cd657d45dcc50fb618e0000,0x6657d45dc550fb61010002,0x9657d45dc550ab61010004,0xc657dc2dc550ab61020006,0x9af53e2a2222b657102dc550adee0b0000,0x2fb117c815e20457ac41a6bf6c40af1d59118b026f383479f9fddb919e7c7318b15ff41fcc99824e4499f0411f37bb7c833574013bb4c06807bda62c89bf0b175f046bc1a68753f20cd12ef8b3958809adc58b9657dc5dc550adeea50000,0x3657dc2dc550adee010002,0x61655dc2dc550ade1020004]) (.p [0x2653dc2dc550ade101000c,0x6653dc2dc250ade101000e,0x395ee33d8c1ed9bc6467b18b3455833dde67b32e6818c919bcf6312c62cd9ed200f3e8265bef8cadef58653dc2102dd5de1500000,0xd021513dc2dc5dd5de1060000,0xfffc02e78b8ac40af7f8d3558ca4816be4fbbc435268063ab223141ee9c057882519f5bdeba1db919f19bb6ef3dfd63c0edc8cfe5d0edc8cf8c98b3415df41a6fd7bd7a727c364bde235ef11e8c83657dc2dc5dd5b618f0000,0x11bd1afa37a37e6f0af137e6f0af17e7dfee30e7f029df96e7c3691e8c8a2bd3657dc2dc5dd5dee300000,0x61655dc2dc5dd5de1020002,0x2653dc2dc5dd5de1010004,0x6653dc2dc2dd5de1010006,0x9653dc2dc2dcade1010008,0xd653dc2dc2dcadd3010018,0x3653dc0dc2dcadd3010034,0x51693dc0dc0dcadd3020036,0x557ae3229ba8e41ace4d27ab27a354b9826c0d5d085a4f5f57424035102189bdc2dc4dd86d6420000,0x1280150a580cfcf7af48517b939d0553a2001d120511c85bdc2dc4a9899c360000,0x717f948b24c948a75d0800232735d18085bdc2244deb99c270000]))) (.b 96 (.b 80 (.p [0x36b9b908d57cef880d1a9eb85b102dcadeb99c150000,0x344b7fea4dfc7ff0d4c8e8c8a1ffd64142bdf1f92fc5062f61ffd64d2609fbe7fd2565025255789307319143ffac9a7ee9fe7068d4c069dc1d100687d79bdc5dcadeb99c7b0000,0xfdf3f8ffabfe8801d143ffac9a7ee2f5e77afdd406d30192ce5209185fdc5dcadeb99c370000,0x285bdc5dcadeb99c010002,0x385bdc2dcadeb99c010004,0x685bdc2dc4deb99c010006,0x9189bdc2dc4dd899c020008,0x9113b1bdc0dc2dcb99605000a,0xc97c029d7dc13fb34e527394cb194c2d6f9226527a600744002200189bdc2dc458bca9440000,0xc08c450450411fd01aba11cdbb1243512585bdc2dc43cbdf3290000,0x22822af620cd8083b10a6eb37388391141057be7f5d8902a14daedebe8a4041888a88a6eb822c451141056b9b4faf57450563dde206447c62680cd58fa8906e88598cd172adf3b72331145d620424e42685bdc2dc4590df3b20000,0x9189bdc2dc458bdf3020002,0x9125b1bdc0dc258bde7050004,0x73db37ac5bbcc6f6ba0e2c3e2026ba0524f804adc85bdc0102dd7de72b0000,0xd3f80660b85b040dc5dd7de70a0000,0x20f81b3ddfdbbe4de28efa053dbf8e66542611af8f149b77e807480177ff337bedbd9cf6b7154ae857b5e6959429b9120ddb77e02444013b26fa0366fe3cb9be8011eac000c85bdc2dc5a17c27900000]) (.p [0x1bd7f5efdc8c66fae3caf9bdeb113df8903ab85b102dc5de9c271d0000,0x1876d7296c752bd024fef97d6e4669316ddfbdaef9fdb8f2778cadd942d33e85d6e399df2ff989df7c7bc66821f6326ffe7914fbdbfbe33204a2bd28d58cd2f33dad1b9a4cd79bd052c5de9c277f0000,0xc39bbd6ffc763e334ef94b58bfcb19adb6e673120d266ee66032383fe3d2ad5e73e880150a2c185fd052c5de9c274e0000,0x1885bdc52c5de9c27020002,0xfe95e20c7ef8fe35991d11df2fccfdfd152abc9cc51d2f8012fc6474ef97e6b32385efc37cd4c9f377e64dfa28c8acf8385bdc5dccde9c27540000,0x685bdc5dc5de9c27010002,0x385bdc2dc5de9c27010006,0x985bdc2dc5dd7c27010008,0x5f56fd3cf9874efab78a9ebde235f6b1022bab85b102dc5a17df11d0000,0x37dffec41ff9c117befff0a4f4404c668881f4284117bed4f733187a8c652ce501311aedced1e739af663070cf5ec1d10b319317885bdc52c5a17df16a0000,0x2d8bfca6116ed62efdeb26bf44622221e2b9c4145fdb9553e3c811c283329c136c4bd61069af36fe35ae7fcde32288c3a85bdc5dcca17df15b0000,0x685bdc5dc5a17df1010002,0x385bdc2dc5a17df1010004,0x37a4b7ea77aac454769dfab85b102dc5de9df1100000,0x377a09c07fcc03ea45ffd04e6f336ef40a4dffe82a07d48bffb1edffed67d020f8f4a55f68f37f30fa0e33498b267d023b0fa7e83839011ccc3e9fa3fbff98bffa6b77a0043feb4ef3f87a7399a77a3686399bf19317885bdc52c5de9df1a20000,0xbe6ad3bcd4ef1d9ccc733e7efcc35748585bdc5dccde9df11c0000])) (.b 112 (.p [0x685bdc5dc5de9df1010002,0x385bdc2dc5de9df1010004,0x985bdc2dc5dd7df1010006,0xd85bdc2dc5dd7de701000c,0x385bdc0dc5dd7de7010016,0x5189bdc0dc2dd7de7020018,0x24cda6e6bf8e884304a8ca6dcf290e7ff984df224cda240a0a697108077c004205b23dc1dc4dd7c274e0000,0xd04da2145a005d26bd71199fd43d7bc4438d7401abdd020a97f1d10a489259b9c494211552e210a6e45bb23dc1dc4a17df15d0000,0x69bce67c027b918e930787b4472574429b9d825f0010734be00204b7c005bdfa06db60c66c6304d3d822f77ef959f42ec6a20466317a650f7cdbe29f112304db4d0d0ebab80e82a4379ccf8809ee40246634686b23dc1dc4de9df1bd0000,0x9b23dc1dc4dd7df1010002,0xb5bb23dc0dc2dd7de7030004,0x2b1bdc0dc2dd7de7010006,0x9b1bdc0dc2dcbde7010020,0x305b1bdc0dc0dcadd3040026,0x2b13dc0dc0dcadd3010032,0x9b13dc0dc0dc4dd301006a]) (.p [0x621bd1dc0dc0dc0dc104006c]))))
private def data : Store := ⟨vals,rows,model,codes,6⟩
def ok := test rule 5 19 data
theorem finish (checked : OMA.Tape245212.Before ok 113) : Deny 5 19 ![⟨2,23584⟩,⟨1,23584⟩,⟨1,23584⟩,⟨1,23584⟩,⟨20,96⟩] := by
  have same : data.vertex 112=![⟨2,23584⟩,⟨1,23584⟩,⟨1,23584⟩,⟨1,23584⟩,⟨20,96⟩] := by decide +kernel
  rw [← same]
  exact close valid _ _ data 112 checked
end OMA.Tape5_19_245212
namespace OMA.Tape5_23_245212
open OMA.Box245212 OMA.RankTape245212 OMA.TapeShared245212
private def vals := OMA.PageTree245212.get (.b 16 (.p [1,2,3,4,5,6,10,11,15,16,24,25,29,31,32,33]) (.p [34,35,36,37,47,50,51,68,102,103,136,137,11472]))

private def rows := OMA.PageTree245212.get (.b 16 (.p [0x3f7bd7cdfc771d87ff542934983b8902a11c3e8801701a4d71003a1a60d2ca001a88168ce0781e22ab4f0000,0x2e135d08028ce0461e27960d0000,0x16b09afd888882b2807811670415ae21d7c1be69a6f8622042288aadf3967841011411762145a4a54eb5f575836f82b890a6e44968ce078472796720000,0x37ab80cc064f8063f80662dac18784e3f96190000,0xf3d9ef9b7c9822557ffc9bfc438e453df266adf159d723a1fbeff7c670e63b98accf40a6fd75c823caf8801d11995f26feda37be6f89f88ef88015a0018b4dde81035cf6b5bdeb1d5cf2e54d3120983dbf00f200a7c404aa99ace1384e3f16af0000,0x81a8bffb1cce1cf60ec11620fff622c6634085dca8d731dfda8c66bcd59bd0023dbbf4884df3310a2f7173301a49f10131931ace10c4e3f99640000,0x580fef9c21bf53bd6540f18c53bd4745bdefc4def93be2c9be1f7c11d115c311d3efedcee566fab7996d30776d002cdf0025f8c88c3e5ace1387e3f99640000,0x19ace1384e3f99010002,0x35ace1384e3f96010004,0x462ce0784e3f96020006,0x2f7cd7bd5636dbbf01226e0e88e4ae881ee444e93e0b85e4357270000,0xdaf7c89e6db77e0244dc1d16ee884312adffec632753bf4caf93a7c408ae87eedbbf7193a7c481d317c40030eb9167c404f409198d6c9d3e60110034a04ba1f7d06111c229bbf7a88aa745b2ba214dc8b6693e0b85e439baf0000,0xb408692e0784e3f96060002,0xa8ce0784e3f96010004,0x268ce0784e279601000c,0x9ce8ce0781e239602000e]) (.p [0xb4086aae0380e0381060010]))
private def data : Store := ⟨vals,rows,model,codes,5⟩
def ok := test rule 5 23 data
theorem finish (checked : OMA.Tape245212.Before ok 17) : Deny 5 23 ![⟨2,11472⟩,⟨1,11472⟩,⟨1,11472⟩,⟨1,11472⟩,⟨24,50⟩] := by
  have same : data.vertex 16=![⟨2,11472⟩,⟨1,11472⟩,⟨1,11472⟩,⟨1,11472⟩,⟨24,50⟩] := by decide +kernel
  rw [← same]
  exact close valid _ _ data 16 checked
end OMA.Tape5_23_245212
namespace OMA.Tape5_29_245212
open OMA.Box245212 OMA.RankTape245212 OMA.TapeShared245212
private def vals := OMA.PageTree245212.get (.p [1,2,30,34,8400])

private def rows := OMA.PageTree245212.get (.p [0xd4efd36dbbf01b70656eca59ca4857941a5eb4085a820821290000])
private def data : Store := ⟨vals,rows,model,codes,3⟩
def ok := test rule 5 29 data
theorem finish (checked : OMA.Tape245212.Before ok 1) : Deny 5 29 ![⟨2,8400⟩,⟨1,8400⟩,⟨1,8400⟩,⟨1,8400⟩,⟨30,34⟩] := by
  have same : data.vertex 0=![⟨2,8400⟩,⟨1,8400⟩,⟨1,8400⟩,⟨1,8400⟩,⟨30,34⟩] := by decide +kernel
  rw [← same]
  exact close valid _ _ data 0 checked
end OMA.Tape5_29_245212
namespace OMA.Tape5_31_245212
open OMA.Box245212 OMA.RankTape245212 OMA.TapeShared245212
private def vals := OMA.PageTree245212.get (.p [1,2,32,7952])

private def rows := OMA.PageTree245212.get (.p [0x1acccd010000])
private def data : Store := ⟨vals,rows,model,codes,2⟩
def ok := test rule 5 31 data
theorem finish (checked : OMA.Tape245212.Before ok 1) : Deny 5 31 ![⟨2,7952⟩,⟨1,7952⟩,⟨1,7952⟩,⟨1,7952⟩,⟨32,32⟩] := by
  have same : data.vertex 0=![⟨2,7952⟩,⟨1,7952⟩,⟨1,7952⟩,⟨1,7952⟩,⟨32,32⟩] := by decide +kernel
  rw [← same]
  exact close valid _ _ data 0 checked
end OMA.Tape5_31_245212
namespace OMA.Tape7_11_245212
open OMA.Box245212 OMA.RankTape245212 OMA.TapeShared245212
private def vals := OMA.PageTree245212.get (.b 16 (.p [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16]) (.b 32 (.p [17,18,19,20,21,22,23,26,30,31,34,35,42,43,86,87]) (.p [5824])))

private def rows := OMA.PageTree245212.get (.b 16 (.p [0x3d7ac4cfd59076dabf5ebe466ae7177df54faa9e31b9f75992d7ff28bff428b33f4210b751cdea145a38b331dd7401472740b7220558c8008018023c76b0000,0x46f537e7c7b2d6ad2dfd086687c8828feb8d008088f822ae8e6d747076552522ff603b010f56401b912558c800801142810590000,0x17d029e92df7c472e3fae37e233e611857c82580558c040801806810250000,0x7d23fcfae3b77e19ac60c5c25631c47a9f23dce50292df7c604a9e37fb82c17b92758f72a141530c8020c18068104b0000,0xf4aaa6eb964533157600b7bc5660a0074cb30c142804806690270000,0x3807685caccafd6055afd0b752098738698f51c6ea04a2bd63dfa16ea145875b685b50a0d061400b287cb6031c30c8068043466906c0000,0x4d0a7fa053d306b749d68873595ff40a785abf258c393cb0598029a02462c30c80624480e690430000,0x4d21f8efeea9115ebad0d28e34f6ae314574e690fe78d5a2a4a285cc99eb20c3ec3d2b166833140e6796ac8a8ef8887aeb3c6d1937d30c80680a80e6906c0000,0x630c80680480e690010002,0x930c806804806690010004,0x330c802804806690010006,0x26910de346e3408fae3763ec668b15248de836ff1e10f568558e01de5ed3166263843dbaef73ed59060887ed30fb4c58b1da37a160befe10f568cfefcf2d3d28c888df3eaf88a8febcae23d17e330c80280480681b970000,0xd30c802804806810010002,0x513cc80280180681002000a,0x4cc55d8048359e8dbb900d14d024480880e7151b0000,0xf37af39e0efaf9a7425a04ab267c07fe01abf2ddf36fc8cdb3ee5eb83ddf34d5cd7cd0eb933d6bc74e2bd715eef88ae321f7fad13960131650135d6cddb57ae969dd4e80266933d003afcd3debc77d7af48e4c9d03dc884772f5cc70057056f92220914d080a80880e715be0000]) (.b 32 (.p [0x4205590802803806714060002,0x1326ba0420c422820ae851692ddc0dc116dc12609b107222937fdef19379fe2a227e417f47ec57482668b97fdefff5efae3e4f08a22aeb775d253aba14dc891c9afdbfa0377200287c8f731a966fc21244c02e8c7002fe95dbc95a419faf8483ad40191cdaba40351006e45b59080280334681de10000,0xfa0533f8996f17d995cdf3eb0574572a1e57b4803721c537997e409de474f99fc5455cdbbf013addf809110a6e4d55908021c380e81d5f0000,0x353bf6ebde35efd33e03dd85ef9f512d622a1efd54d856f8805cfc467c12c3ebdea7cfa0776bf6f8815f1003a61d49014280880e81d540000,0xf7f50a2d002ca5ad715f5bf8ee334d947174ae5eb8b75a2cd17be3fe5da169326b9af9a2f1afde8f53b5f900a65f2d057b5fa51c959401b9343449080680860e79d770000,0x1fe3d2347be6df9d7c5b77e02602ce156d732316748fb6ef951cf224669bb6ef91b77a005d0d262e45679acc1cf2027b9c48c49080644881979d630000,0x5f7f5c457be3a33be22b88cf984ff3807650038c3a77f1b2fcd6647031437ad2af9451d3e3f5d57bcd9f8a32235cf8349080681281979d590000,0x649080680881979d010002,0x949080680880e79d010004,0x1337ae739189a08bde5000848202693baf3179682a33d47abcc61d9bf79177ef9ef23d262e76e46bdaca036350598c49080644860e81f5d0000,0x94b09afd3c7b57d74644629baeffbce727264e512b4c62f4eb4fe5520561a500639332ac37ba403906adfb6b7be6fcd72acf0cc5694fc672902bb0ce500aaa8de682f5a0d35eb05b95dff7bf6ef8edcae8c8acf8349080681260e81fa10000,0x649080680860e81f010002,0x17f2c179ce9dfbbf8d73d19cae177cdbe0acc8e3eb3eb8a9f7e28c8e9df403ff9a6ef011cca57cde6fcc681198cd162dbbf7b58c159db6efc0639336cf6900c6b4ef9402d696b9ca027333e82573e96f6e66b8f7cf9e2ab1d5e6fe49080680881981fa40000,0x949080680880e81f010002,0xd49080680880e81d010006,0x349080280880e81d01000c]) (.p [0x2db77e03493fb5fa56eca12d02159380280880e81d1b0000,0x259080280880e81d010002,0x659080280380e81d010010,0x959080280380681d010012,0x1a5590802801806810030014,0x258c802801806810010018,0x358c800801806810010024,0x958c800801802810010026,0x18215cb800800800801050028])))
private def data : Store := ⟨vals,rows,model,codes,6⟩
def ok := test rule 7 11 data
theorem finish (checked : OMA.Tape245212.Before ok 41) : Deny 7 11 ![⟨2,5824⟩,⟨1,5824⟩,⟨1,5824⟩,⟨1,5824⟩,⟨12,26⟩] := by
  have same : data.vertex 40=![⟨2,5824⟩,⟨1,5824⟩,⟨1,5824⟩,⟨1,5824⟩,⟨12,26⟩] := by decide +kernel
  rw [← same]
  exact close valid _ _ data 40 checked
end OMA.Tape7_11_245212
namespace OMA.Tape7_13_245212
open OMA.Box245212 OMA.RankTape245212 OMA.TapeShared245212
private def vals := OMA.PageTree245212.get (.p [1,2,14,19,4704])

private def rows := OMA.PageTree245212.get (.p [0x940976277812b1a745cfa01623395f400adf400e81cf3a24b7441a5eb4085a820821450000])
private def data : Store := ⟨vals,rows,model,codes,3⟩
def ok := test rule 7 13 data
theorem finish (checked : OMA.Tape245212.Before ok 1) : Deny 7 13 ![⟨2,4704⟩,⟨1,4704⟩,⟨1,4704⟩,⟨1,4704⟩,⟨14,19⟩] := by
  have same : data.vertex 0=![⟨2,4704⟩,⟨1,4704⟩,⟨1,4704⟩,⟨1,4704⟩,⟨14,19⟩] := by decide +kernel
  rw [← same]
  exact close valid _ _ data 0 checked
end OMA.Tape7_13_245212
namespace OMA.CheckedTapes245212
open OMA.Tape245212
def tests (i : ℕ) : Bool :=
  if i<189 then OMA.Tape5_7_245212.ok (i-0) else
  if i<768 then OMA.Tape5_11_245212.ok (i-189) else
  if i<2607 then OMA.Tape5_13_245212.ok (i-768) else
  if i<2790 then OMA.Tape5_17_245212.ok (i-2607) else
  if i<2903 then OMA.Tape5_19_245212.ok (i-2790) else
  if i<2920 then OMA.Tape5_23_245212.ok (i-2903) else
  if i<2921 then OMA.Tape5_29_245212.ok (i-2920) else
  if i<2922 then OMA.Tape5_31_245212.ok (i-2921) else
  if i<2963 then OMA.Tape7_11_245212.ok (i-2922) else
  OMA.Tape7_13_245212.ok (i-2963)
private abbrev C := Cursor tests
def c0 := Cursor.start tests
set_option maxHeartbeats 0 in
def c1:C:=c0.atRange 0 28 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c2:C:=c1.atRange 28 49 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c3:C:=c2.atRange 49 57 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c4:C:=c3.atRange 57 79 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c5:C:=c4.atRange 79 86 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c6:C:=c5.atRange 86 91 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c7:C:=c6.atRange 91 92 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c8:C:=c7.atRange 92 103 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c9:C:=c8.atRange 103 104 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c10:C:=c9.atRange 104 128 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c11:C:=c10.atRange 128 131 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c12:C:=c11.atRange 131 143 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c13:C:=c12.atRange 143 148 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c14:C:=c13.atRange 148 149 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c15:C:=c14.atRange 149 173 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c16:C:=c15.atRange 173 182 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c17:C:=c16.atRange 182 199 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c18:C:=c17.atRange 199 207 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c19:C:=c18.atRange 207 220 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c20:C:=c19.atRange 220 241 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c21:C:=c20.atRange 241 260 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c22:C:=c21.atRange 260 288 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c23:C:=c22.atRange 288 313 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c24:C:=c23.atRange 313 341 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c25:C:=c24.atRange 341 359 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c26:C:=c25.atRange 359 370 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c27:C:=c26.atRange 370 383 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c28:C:=c27.atRange 383 396 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c29:C:=c28.atRange 396 402 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c30:C:=c29.atRange 402 405 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c31:C:=c30.atRange 405 412 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c32:C:=c31.atRange 412 414 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c33:C:=c32.atRange 414 415 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c34:C:=c33.atRange 415 420 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c35:C:=c34.atRange 420 421 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c36:C:=c35.atRange 421 422 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c37:C:=c36.atRange 422 445 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c38:C:=c37.atRange 445 449 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c39:C:=c38.atRange 449 450 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c40:C:=c39.atRange 450 451 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c41:C:=c40.atRange 451 452 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c42:C:=c41.atRange 452 459 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c43:C:=c42.atRange 459 482 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c44:C:=c43.atRange 482 483 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c45:C:=c44.atRange 483 500 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c46:C:=c45.atRange 500 501 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c47:C:=c46.atRange 501 502 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c48:C:=c47.atRange 502 508 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c49:C:=c48.atRange 508 509 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c50:C:=c49.atRange 509 512 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c51:C:=c50.atRange 512 526 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c52:C:=c51.atRange 526 527 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c53:C:=c52.atRange 527 530 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c54:C:=c53.atRange 530 535 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c55:C:=c54.atRange 535 541 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c56:C:=c55.atRange 541 542 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c57:C:=c56.atRange 542 543 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c58:C:=c57.atRange 543 544 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c59:C:=c58.atRange 544 546 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c60:C:=c59.atRange 546 547 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c61:C:=c60.atRange 547 569 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c62:C:=c61.atRange 569 576 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c63:C:=c62.atRange 576 580 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c64:C:=c63.atRange 580 581 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c65:C:=c64.atRange 581 586 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c66:C:=c65.atRange 586 587 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c67:C:=c66.atRange 587 589 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c68:C:=c67.atRange 589 590 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c69:C:=c68.atRange 590 608 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c70:C:=c69.atRange 608 620 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c71:C:=c70.atRange 620 624 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c72:C:=c71.atRange 624 631 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c73:C:=c72.atRange 631 644 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c74:C:=c73.atRange 644 645 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c75:C:=c74.atRange 645 658 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c76:C:=c75.atRange 658 659 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c77:C:=c76.atRange 659 660 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c78:C:=c77.atRange 660 665 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c79:C:=c78.atRange 665 666 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c80:C:=c79.atRange 666 667 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c81:C:=c80.atRange 667 668 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c82:C:=c81.atRange 668 672 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c83:C:=c82.atRange 672 680 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c84:C:=c83.atRange 680 685 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c85:C:=c84.atRange 685 690 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c86:C:=c85.atRange 690 691 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c87:C:=c86.atRange 691 698 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c88:C:=c87.atRange 698 702 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c89:C:=c88.atRange 702 704 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c90:C:=c89.atRange 704 716 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c91:C:=c90.atRange 716 722 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c92:C:=c91.atRange 722 723 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c93:C:=c92.atRange 723 728 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c94:C:=c93.atRange 728 737 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c95:C:=c94.atRange 737 738 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c96:C:=c95.atRange 738 741 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c97:C:=c96.atRange 741 742 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c98:C:=c97.atRange 742 749 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c99:C:=c98.atRange 749 750 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c100:C:=c99.atRange 750 753 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c101:C:=c100.atRange 753 781 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c102:C:=c101.atRange 781 793 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c103:C:=c102.atRange 793 808 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c104:C:=c103.atRange 808 821 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c105:C:=c104.atRange 821 844 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c106:C:=c105.atRange 844 869 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c107:C:=c106.atRange 869 896 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c108:C:=c107.atRange 896 909 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c109:C:=c108.atRange 909 924 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c110:C:=c109.atRange 924 936 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c111:C:=c110.atRange 936 953 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c112:C:=c111.atRange 953 968 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c113:C:=c112.atRange 968 984 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c114:C:=c113.atRange 984 1006 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c115:C:=c114.atRange 1006 1026 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c116:C:=c115.atRange 1026 1050 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c117:C:=c116.atRange 1050 1078 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c118:C:=c117.atRange 1078 1106 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c119:C:=c118.atRange 1106 1114 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c120:C:=c119.atRange 1114 1115 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c121:C:=c120.atRange 1115 1118 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c122:C:=c121.atRange 1118 1119 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c123:C:=c122.atRange 1119 1129 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c124:C:=c123.atRange 1129 1137 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c125:C:=c124.atRange 1137 1139 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c126:C:=c125.atRange 1139 1140 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c127:C:=c126.atRange 1140 1168 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c128:C:=c127.atRange 1168 1191 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c129:C:=c128.atRange 1191 1218 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c130:C:=c129.atRange 1218 1236 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c131:C:=c130.atRange 1236 1259 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c132:C:=c131.atRange 1259 1282 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c133:C:=c132.atRange 1282 1300 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c134:C:=c133.atRange 1300 1317 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c135:C:=c134.atRange 1317 1338 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c136:C:=c135.atRange 1338 1366 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c137:C:=c136.atRange 1366 1372 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c138:C:=c137.atRange 1372 1376 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c139:C:=c138.atRange 1376 1399 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c140:C:=c139.atRange 1399 1427 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c141:C:=c140.atRange 1427 1440 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c142:C:=c141.atRange 1440 1446 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c143:C:=c142.atRange 1446 1453 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c144:C:=c143.atRange 1453 1466 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c145:C:=c144.atRange 1466 1472 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c146:C:=c145.atRange 1472 1473 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c147:C:=c146.atRange 1473 1481 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c148:C:=c147.atRange 1481 1488 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c149:C:=c148.atRange 1488 1490 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c150:C:=c149.atRange 1490 1507 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c151:C:=c150.atRange 1507 1532 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c152:C:=c151.atRange 1532 1550 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c153:C:=c152.atRange 1550 1553 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c154:C:=c153.atRange 1553 1564 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c155:C:=c154.atRange 1564 1592 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c156:C:=c155.atRange 1592 1611 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c157:C:=c156.atRange 1611 1639 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c158:C:=c157.atRange 1639 1656 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c159:C:=c158.atRange 1656 1674 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c160:C:=c159.atRange 1674 1692 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c161:C:=c160.atRange 1692 1700 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c162:C:=c161.atRange 1700 1713 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c163:C:=c162.atRange 1713 1721 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c164:C:=c163.atRange 1721 1728 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c165:C:=c164.atRange 1728 1738 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c166:C:=c165.atRange 1738 1745 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c167:C:=c166.atRange 1745 1747 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c168:C:=c167.atRange 1747 1766 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c169:C:=c168.atRange 1766 1783 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c170:C:=c169.atRange 1783 1790 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c171:C:=c170.atRange 1790 1795 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c172:C:=c171.atRange 1795 1799 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c173:C:=c172.atRange 1799 1805 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c174:C:=c173.atRange 1805 1815 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c175:C:=c174.atRange 1815 1826 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c176:C:=c175.atRange 1826 1833 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c177:C:=c176.atRange 1833 1846 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c178:C:=c177.atRange 1846 1863 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c179:C:=c178.atRange 1863 1877 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c180:C:=c179.atRange 1877 1893 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c181:C:=c180.atRange 1893 1908 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c182:C:=c181.atRange 1908 1936 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c183:C:=c182.atRange 1936 1958 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c184:C:=c183.atRange 1958 1959 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c185:C:=c184.atRange 1959 1975 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c186:C:=c185.atRange 1975 1985 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c187:C:=c186.atRange 1985 1992 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c188:C:=c187.atRange 1992 1998 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c189:C:=c188.atRange 1998 2007 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c190:C:=c189.atRange 2007 2014 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c191:C:=c190.atRange 2014 2021 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c192:C:=c191.atRange 2021 2022 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c193:C:=c192.atRange 2022 2038 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c194:C:=c193.atRange 2038 2050 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c195:C:=c194.atRange 2050 2075 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c196:C:=c195.atRange 2075 2078 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c197:C:=c196.atRange 2078 2082 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c198:C:=c197.atRange 2082 2083 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c199:C:=c198.atRange 2083 2090 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c200:C:=c199.atRange 2090 2098 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c201:C:=c200.atRange 2098 2100 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c202:C:=c201.atRange 2100 2103 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c203:C:=c202.atRange 2103 2104 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c204:C:=c203.atRange 2104 2110 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c205:C:=c204.atRange 2110 2111 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c206:C:=c205.atRange 2111 2139 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c207:C:=c206.atRange 2139 2146 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c208:C:=c207.atRange 2146 2153 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c209:C:=c208.atRange 2153 2159 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c210:C:=c209.atRange 2159 2169 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c211:C:=c210.atRange 2169 2174 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c212:C:=c211.atRange 2174 2177 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c213:C:=c212.atRange 2177 2185 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c214:C:=c213.atRange 2185 2187 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c215:C:=c214.atRange 2187 2189 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c216:C:=c215.atRange 2189 2194 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c217:C:=c216.atRange 2194 2209 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c218:C:=c217.atRange 2209 2215 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c219:C:=c218.atRange 2215 2223 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c220:C:=c219.atRange 2223 2229 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c221:C:=c220.atRange 2229 2233 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c222:C:=c221.atRange 2233 2252 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c223:C:=c222.atRange 2252 2260 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c224:C:=c223.atRange 2260 2274 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c225:C:=c224.atRange 2274 2299 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c226:C:=c225.atRange 2299 2308 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c227:C:=c226.atRange 2308 2313 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c228:C:=c227.atRange 2313 2323 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c229:C:=c228.atRange 2323 2328 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c230:C:=c229.atRange 2328 2334 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c231:C:=c230.atRange 2334 2338 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c232:C:=c231.atRange 2338 2343 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c233:C:=c232.atRange 2343 2348 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c234:C:=c233.atRange 2348 2368 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c235:C:=c234.atRange 2368 2370 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c236:C:=c235.atRange 2370 2379 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c237:C:=c236.atRange 2379 2389 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c238:C:=c237.atRange 2389 2396 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c239:C:=c238.atRange 2396 2403 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c240:C:=c239.atRange 2403 2409 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c241:C:=c240.atRange 2409 2412 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c242:C:=c241.atRange 2412 2415 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c243:C:=c242.atRange 2415 2422 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c244:C:=c243.atRange 2422 2424 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c245:C:=c244.atRange 2424 2426 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c246:C:=c245.atRange 2426 2433 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c247:C:=c246.atRange 2433 2437 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c248:C:=c247.atRange 2437 2439 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c249:C:=c248.atRange 2439 2449 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c250:C:=c249.atRange 2449 2460 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c251:C:=c250.atRange 2460 2463 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c252:C:=c251.atRange 2463 2465 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c253:C:=c252.atRange 2465 2483 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c254:C:=c253.atRange 2483 2494 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c255:C:=c254.atRange 2494 2501 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c256:C:=c255.atRange 2501 2505 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c257:C:=c256.atRange 2505 2518 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c258:C:=c257.atRange 2518 2527 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c259:C:=c258.atRange 2527 2533 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c260:C:=c259.atRange 2533 2534 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c261:C:=c260.atRange 2534 2547 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c262:C:=c261.atRange 2547 2559 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c263:C:=c262.atRange 2559 2567 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c264:C:=c263.atRange 2567 2573 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c265:C:=c264.atRange 2573 2575 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c266:C:=c265.atRange 2575 2582 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c267:C:=c266.atRange 2582 2583 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c268:C:=c267.atRange 2583 2588 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c269:C:=c268.atRange 2588 2608 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c270:C:=c269.atRange 2608 2620 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c271:C:=c270.atRange 2620 2633 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c272:C:=c271.atRange 2633 2647 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c273:C:=c272.atRange 2647 2653 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c274:C:=c273.atRange 2653 2672 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c275:C:=c274.atRange 2672 2687 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c276:C:=c275.atRange 2687 2701 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c277:C:=c276.atRange 2701 2715 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c278:C:=c277.atRange 2715 2729 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c279:C:=c278.atRange 2729 2742 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c280:C:=c279.atRange 2742 2753 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c281:C:=c280.atRange 2753 2771 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c282:C:=c281.atRange 2771 2787 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c283:C:=c282.atRange 2787 2800 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c284:C:=c283.atRange 2800 2811 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c285:C:=c284.atRange 2811 2830 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c286:C:=c285.atRange 2830 2851 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c287:C:=c286.atRange 2851 2864 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c288:C:=c287.atRange 2864 2874 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c289:C:=c288.atRange 2874 2893 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c290:C:=c289.atRange 2893 2907 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c291:C:=c290.atRange 2907 2920 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c292:C:=c291.atRange 2920 2929 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c293:C:=c292.atRange 2929 2939 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c294:C:=c293.atRange 2939 2944 rfl (by decide +kernel)
set_option maxHeartbeats 0 in
def c295:C:=c294.atRange 2944 2964 rfl (by decide +kernel)
theorem passed : Before tests 2964 := c295.checked
end OMA.CheckedTapes245212
namespace OMA.Tape5_7_245212
open OMA.Box245212
theorem deny5_7 : Deny 5 7 ![⟨2,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨8,999999999999999999⟩] := by
  apply finish
  intro i hi
  have h := OMA.CheckedTapes245212.passed (0+i) (by omega)
  simpa (disch := omega) only [OMA.CheckedTapes245212.tests,if_pos,if_neg,show 0+i-0=i by omega] using h
end OMA.Tape5_7_245212
namespace OMA.Tape5_11_245212
open OMA.Box245212
theorem deny5_11 : Deny 5 11 ![⟨2,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨12,999999999999999999⟩] := by
  apply finish
  intro i hi
  have h := OMA.CheckedTapes245212.passed (189+i) (by omega)
  simpa (disch := omega) only [OMA.CheckedTapes245212.tests,if_pos,if_neg,show 189+i-189=i by omega] using h
end OMA.Tape5_11_245212
namespace OMA.Tape5_13_245212
open OMA.Box245212
theorem deny5_13 : Deny 5 13 ![⟨2,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨14,999999999999999999⟩] := by
  apply finish
  intro i hi
  have h := OMA.CheckedTapes245212.passed (768+i) (by omega)
  simpa (disch := omega) only [OMA.CheckedTapes245212.tests,if_pos,if_neg,show 768+i-768=i by omega] using h
end OMA.Tape5_13_245212
namespace OMA.Tape5_17_245212
open OMA.Box245212
theorem deny5_17 : Deny 5 17 ![⟨2,76224⟩,⟨1,76224⟩,⟨1,76224⟩,⟨1,76224⟩,⟨18,256⟩] := by
  apply finish
  intro i hi
  have h := OMA.CheckedTapes245212.passed (2607+i) (by omega)
  simpa (disch := omega) only [OMA.CheckedTapes245212.tests,if_pos,if_neg,show 2607+i-2607=i by omega] using h
end OMA.Tape5_17_245212
namespace OMA.Tape5_19_245212
open OMA.Box245212
theorem deny5_19 : Deny 5 19 ![⟨2,23584⟩,⟨1,23584⟩,⟨1,23584⟩,⟨1,23584⟩,⟨20,96⟩] := by
  apply finish
  intro i hi
  have h := OMA.CheckedTapes245212.passed (2790+i) (by omega)
  simpa (disch := omega) only [OMA.CheckedTapes245212.tests,if_pos,if_neg,show 2790+i-2790=i by omega] using h
end OMA.Tape5_19_245212
namespace OMA.Tape5_23_245212
open OMA.Box245212
theorem deny5_23 : Deny 5 23 ![⟨2,11472⟩,⟨1,11472⟩,⟨1,11472⟩,⟨1,11472⟩,⟨24,50⟩] := by
  apply finish
  intro i hi
  have h := OMA.CheckedTapes245212.passed (2903+i) (by omega)
  simpa (disch := omega) only [OMA.CheckedTapes245212.tests,if_pos,if_neg,show 2903+i-2903=i by omega] using h
end OMA.Tape5_23_245212
namespace OMA.Tape5_29_245212
open OMA.Box245212
theorem deny5_29 : Deny 5 29 ![⟨2,8400⟩,⟨1,8400⟩,⟨1,8400⟩,⟨1,8400⟩,⟨30,34⟩] := by
  apply finish
  intro i hi
  have h := OMA.CheckedTapes245212.passed (2920+i) (by omega)
  simpa (disch := omega) only [OMA.CheckedTapes245212.tests,if_pos,if_neg,show 2920+i-2920=i by omega] using h
end OMA.Tape5_29_245212
namespace OMA.Tape5_31_245212
open OMA.Box245212
theorem deny5_31 : Deny 5 31 ![⟨2,7952⟩,⟨1,7952⟩,⟨1,7952⟩,⟨1,7952⟩,⟨32,32⟩] := by
  apply finish
  intro i hi
  have h := OMA.CheckedTapes245212.passed (2921+i) (by omega)
  simpa (disch := omega) only [OMA.CheckedTapes245212.tests,if_pos,if_neg,show 2921+i-2921=i by omega] using h
end OMA.Tape5_31_245212
namespace OMA.Tape7_11_245212
open OMA.Box245212
theorem deny7_11 : Deny 7 11 ![⟨2,5824⟩,⟨1,5824⟩,⟨1,5824⟩,⟨1,5824⟩,⟨12,26⟩] := by
  apply finish
  intro i hi
  have h := OMA.CheckedTapes245212.passed (2922+i) (by omega)
  simpa (disch := omega) only [OMA.CheckedTapes245212.tests,if_pos,if_neg,show 2922+i-2922=i by omega] using h
end OMA.Tape7_11_245212
namespace OMA.Tape7_13_245212
open OMA.Box245212
theorem deny7_13 : Deny 7 13 ![⟨2,4704⟩,⟨1,4704⟩,⟨1,4704⟩,⟨1,4704⟩,⟨14,19⟩] := by
  apply finish
  intro i hi
  have h := OMA.CheckedTapes245212.passed (2963+i) (by omega)
  simpa (disch := omega) only [OMA.CheckedTapes245212.tests,if_pos,if_neg,show 2963+i-2963=i by omega] using h
end OMA.Tape7_13_245212

theorem OMA.Infinity245212.bounded : OMA.R_OeisA245212_conjecture_R1_H1_R1_H2_R1_H2_R1.H2 :=
  OMA.CaseJoin245212.finish
    OMA.Tape5_7_245212.deny5_7
    OMA.Tape5_11_245212.deny5_11
    OMA.Tape5_13_245212.deny5_13
    OMA.Tape5_17_245212.deny5_17
    OMA.Tape5_19_245212.deny5_19
    OMA.Tape5_23_245212.deny5_23
    OMA.Tape5_29_245212.deny5_29
    OMA.Tape5_31_245212.deny5_31
    OMA.Tape7_11_245212.deny7_11
    OMA.Tape7_13_245212.deny7_13

theorem OMA.solution : OMA.R_OeisA245212_conjecture_R1_H1_R1_H2_R1.H2 :=
  OMA.R_OeisA245212_conjecture_R1_H1_R1_H2_R1_H2_R1.main OMA.Infinity245212.bound OMA.Infinity245212.bounded
