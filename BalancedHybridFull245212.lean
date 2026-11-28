import OMAReductions.R_OeisA245212_conjecture_R1_H1_R1_H2_R1_H2_R1
import Mathlib.Tactic
import Mathlib.Data.Nat.Log

/-! Four-prime exclusion for odd solutions of the OEIS A245212 divisor identity.
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

/-- Each round gives a certified bound; finite rounds are convenient for
    kernel reduction even when the starting exponent has 22 digits. -/
def rounds (k B t : ℕ) : ℕ→ℕ
  | 0 => t
  | n+1 => let v := rounds k B t n; min v (step k B v)

theorem rounds_bound {k B E : ℕ} (pos : 0<E)
    (power : 2^E≤(B^(2*B)*(k*2^k*B^(2*k+1)*(E+1)^k))^(2^k-1)) (n : ℕ) :
    E≤rounds k B (start k B) n := by
  have b := self_bound power
  induction n with
  | zero => exact initial pos b
  | succ n ih => exact le_min ih (refinement b ih)

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

theorem last_le {m p d : ℕ} (hm : 0 < m) (hp : Nat.Prime p) (cop : m.Coprime p)
    (hd : 0<d) (eq : OeisA245212.a (m*p^d)=(σ 1 (m*p^d):ℤ)) : p≤W m+σ 1 m := by
  apply Nat.le_of_dvd _ (last_dvd hm hp cop hd eq)
  have pos : 0<σ 1 m := by
    rw [ArithmeticFunction.sigma_one_apply]
    exact sum_pos' (fun _ _ => Nat.zero_le _) ⟨1,Nat.one_mem_divisors.mpr hm.ne',by decide⟩
  omega

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

namespace OMA.TraceZip245212

/-- A 15-bit cell stores one six-bit symbol and a positive frequency
in a 256-slot alphabet. Common symbols come first. -/
def symbolAt : ℕ→ℕ→ℕ→ℕ×ℕ×ℕ
  | 0,_,_ => (0,1,0)
  | k+1,row,slot =>
    let n := (row/64)%512
    if slot<n then (row%64,n,slot) else symbolAt k (row/32768) (slot-n)

/-- Reverse-order rANS decoding with an exact integer state. The context
is the next instruction on the forward trace. No floating point is used. -/
def unpackANS (table : ℕ→ℕ) : ℕ→ℕ→ℕ→ℕ→ℕ
  | 0,_,_,acc => acc
  | k+1,data,last,acc =>
    let v := symbolAt 64 (table last) (data%256)
    unpackANS table k (v.2.1*(data/256)+v.2.2) v.1 (64*acc+v.1)

def readANS (table : ℕ→ℕ) (size data : ℕ) := unpackANS table size data 64 0

end OMA.TraceZip245212

namespace OMA.Tape245212
open OMA.Box245212 OMA.SparseEngine245212

def field (w i n : ℕ) := (n >>> (i*w)) &&& ((1 <<< w)-1)

def box (numbers : ℕ→ℕ) (bits data : ℕ) : Box := fun i=>
  ⟨numbers (field bits (2*i.val) data),numbers (field bits (2*i.val+1) data)⟩

structure Store where
  numbers : ℕ→ℕ
  rows : ℕ→ℕ
  model : ℕ→ℕ
  coordBits : ℕ
  edgeBits : ℕ
  lengthBits : ℕ

def Store.vertex (s : Store) (i : ℕ) := box s.numbers s.coordBits (s.rows i)
def Store.side (s : Store) (i : ℕ) := field s.edgeBits 0 (s.rows i >>> (10*s.coordBits))
def Store.length (s : Store) (i : ℕ) :=
  field s.lengthBits 0 (s.rows i >>> (10*s.coordBits+s.edgeBits))
def Store.word (s : Store) (i : ℕ) :=
  let raw := s.rows i >>> (10*s.coordBits+s.edgeBits+s.lengthBits)
  OMA.TraceZip245212.readANS s.model (s.length i) raw

def test (act : Advance) (p q : ℕ) (s : Store) (i : ℕ) : Bool :=
  let left := s.side i
  let got := word act p q (s.length i) (s.word i) [s.vertex i]
  if left=0 then decide (got=some [])
  else decide (0 < i) && decide (left ≤ i) && decide (got=some [s.vertex (left-1),s.vertex (i-1)])

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

def Cursor.next {f : ℕ→Bool} (old : Cursor f) (last : ℕ)
    (ok : (old.endAt≤last && rangeTest f old.endAt (last-old.endAt))=true) : Cursor f :=
  ⟨last,by
    obtain ⟨le,cert⟩ := Bool.and_eq_true_iff.mp ok
    have le : old.endAt≤last := of_decide_eq_true le
    simpa only [Nat.add_sub_of_le le] using extend old.checked cert⟩

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

theorem close {act : Advance} (ok : AdvanceSound act) (p q : ℕ) (s : Store) (last : ℕ)
    (tested : Before (test act p q s) (last+1)) : Deny p q (s.vertex last) := by
  suffices ∀ i≤last,Deny p q (s.vertex i) by exact this _ le_rfl
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro les
    have verified := tested i (by omega)
    unfold test at verified
    by_cases leaf : s.side i=0
    · rw [if_pos leaf] at verified
      have h := of_decide_eq_true verified
      exact word_sound ok p q _ _ _ _ h (by simp [solved]) _ List.mem_cons_self
    · rw [if_neg leaf] at verified
      obtain ⟨⟨pos,side⟩,cert⟩ := Bool.and_eq_true_iff.mp verified |>.imp_left Bool.and_eq_true_iff.mp
      have ip : 0 < i := of_decide_eq_true pos
      have sideLe : s.side i ≤ i := of_decide_eq_true side
      apply branchAction ok p q _ _ _ _ _ (of_decide_eq_true cert)
      · exact ih _ (by omega) (by omega)
      · exact ih _ (by omega) (by omega)

end OMA.Tape245212

namespace OMA.DirectTape245212
open OMA.Box245212 OMA.SparseEngine245212

structure Store where
  values : ℕ→ℕ
  rows : ℕ→ℕ
  model : ℕ→ℕ
  width : ℕ
  compressed : Bool

def Store.vertex (s : Store) (i : ℕ) := Tape245212.box s.values s.width (s.rows i >>> 24)

def Store.child (s : Store) (i : ℕ) := (s.rows i)&&&65535

def test (act : Advance) (p q : ℕ) (s : Store) (i : ℕ) : Bool :=
  let row:=s.rows i
  let n:=(row >>> 16)&&&255
  let bits:=row >>> (24+10*s.width)
  let w:=if s.compressed then TraceZip245212.readANS s.model n bits else bits
  let got:=word act p q n w [s.vertex i]
  let left:=s.child i
  if left=0 then decide (got=some [])
  else decide (0 < left) && decide (left ≤ i) && decide (got=some [s.vertex (i-left),s.vertex (i-1)])

theorem close {act : Advance} (valid : AdvanceSound act) (p q : ℕ) (s : Store) (last : ℕ)
    (checked : Tape245212.Before (test act p q s) (last+1)) : Deny p q (s.vertex last) := by
  suffices ∀ i≤last,Deny p q (s.vertex i) by exact this _ le_rfl
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro le
    have h:=checked i (by omega)
    unfold test at h
    by_cases leaf : s.child i=0
    · rw [if_pos leaf] at h
      exact word_sound valid p q _ _ _ _ (of_decide_eq_true h) (by simp [solved]) _ List.mem_cons_self
    · rw [if_neg leaf] at h
      obtain ⟨⟨hp,hm⟩,right⟩:=(Bool.and_eq_true_iff.mp h).imp_left Bool.and_eq_true_iff.mp
      have pos : 0<s.child i:=of_decide_eq_true hp
      have mx : s.child i ≤ i:=of_decide_eq_true hm
      apply branchAction valid p q _ _ _ _ _ (of_decide_eq_true right)
      · exact ih _ (by omega) (by omega)
      · exact ih _ (by omega) (by omega)

end OMA.DirectTape245212

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

def quickBlock (p q : ℕ) (b : Box) : Bool :=
  decide (1<(b 4).lo) &&
  (b 0).entries.all (fun k =>
    let a0 := wt 3 k; let s0 := sig 3 k; let t0 := tax 3 k
    (b 1).entries.all (fun e =>
      let a1 := a0*wt p e; let s1 := s0*sig p e; let t1 := t0*tax p e
      (b 2).entries.all (fun f => quick (a1*wt q f) (s1*sig q f) (t1*tax q f)
        (b 4).lo (b 4).hi (b 3).lo (b 3).hi)))

theorem prefix_ok {p q : ℕ} {b : Box} (yes : quickBlock p q b=true) : Deny p q b := by
  apply prefix_sound
  obtain ⟨base,all⟩ := Bool.and_eq_true_iff.mp yes
  apply Bool.and_eq_true_iff.mpr
  refine ⟨base,List.all_eq_true.mpr fun k hk=>List.all_eq_true.mpr fun e he=>List.all_eq_true.mpr fun f hf=>?_⟩
  exact quick_ok (List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp all k hk) e he) f hf)

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
def quickRule := withPrefix QuickPrefix245212.quickBlock base
theorem quickRule_sound : AdvanceSound quickRule :=
  prefix_sound QuickPrefix245212.prefix_ok base_sound

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

def rule := withPanel false
theorem sound : AdvanceSound rule := withPanel_sound false

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

namespace OMA.TapeShared245212
def rule := OMA.SweepPrefix245212.rule
theorem valid : OMA.SparseEngine245212.AdvanceSound rule := OMA.SweepPrefix245212.sound
def model := OMA.PageTree245212.get (.b 32 (.b 16 (.p [16384,0x4c80b5096a2,0x4a00c601a002e006c0086026805b809901ca04080b501660340081015c032706420c2c237846b09c413245040dc7,0xae01e402c805b00f60180033004200d801a8030809f0108028805e00ab014e02bc07b81090210051c15a033509ec160c2d1a0b8,0x88010403a007500ee01d805e8091012402500618117022604540ab019b033206680fd021d0410087811d8279048e092414e02df05940d0821e134b,16384,16384,0xc001a802a0052010e029804d009e015e024406e00d6019403ac06980c201aa037406c80fa022e0424090811b0278042009c813b02be052c0bb8162044e0a1017a83c308e812d831c0de3,0xd80150032804100a201f405300aa013a02200500095014202bc04c80920172035c06d80d30192037006f010a024e042c081013a022c05ec0ad014702f806dc0ef81f403880788115838308ec13d429c0da3,0x19402d807d00a2014803300410126028004480aa0172026404d00ba01ce03ac06580d401c2035808b8108022a040808f014a02ba05f00a38162030806dc0ef81f403ea08ec15782dc068615e031b0ca3,0x194033006a0082015003e80a00156021c0490091017602e806480e701c2034c06d80c80186036407c80da019603bc061011e0238055c0b1015602ba06540ef81c403e809f015b82f5069411d853c0a63,0x820110025807d0140022404380940142024c05c80b7017402ec06b80c20190034406d80de0194038808c812b025e0448093811d022a045809e015a02b8067c0e182f407ea17d83fc1163,16384,16384,16384,16384]) (.p [16384,0x12a022005b01490d6e322881c1a4b,0x24805b0249086e3a28a5c15cb,0x34005101be035c06d80f401f4031c07000eb020605d80dc81b5039608241298261066e12944bc1b4a,0xc3086e242cbe51ab8,0x57009201b40220051010402d005600b50176029c06f80c8023a051c0dc81b603ee080c12a834b06c41de0493184a,0x74008801bc0290087012e028405d808201ea03b4075811f020604780a40237046c095815d02e206161ce04f516ca,0x6600ca018002100670108028404380ad0168022405a80aa0190035806a80fa027204880bd819f042e094c13b827606860f2c35c1cca,16440,0x5b008802d004480b00114028006f80c801ba03d409b818303ec07e40f182190416091c21c2827,0x1f00220052013602d005a809e010e02c404500a10186032408f817a02ee07d8111821a04960c2023c272b,0x410088014802500600084014405e00b40142026806f80f6018e04640bb81750310068c0dd0209040608e42c585db0e70209c42989ab,0x10802a009d0106022005a0087011402d407e00df01bc03c807101360376072c0f1829c066e0d241fc25ef,0x4100a20108022006600a8022005a808a0178021c04e00f402b206880db01c303ee07240fc823b053e0b8c1e585380b3a1e9c3ea8aef,0x21007d010e02f005080aa016a027006180da019404200cf81b6037407ec11b824905440e8c205845e0a701f584758b2f,0x29006000cc017003a005e00fa024c04380990104021005080b501340374064011b027804240bb0162034e06540dc81ba034607ec12b024a05560adc181838b092e15bc3fc089f])) (.b 48 (.p [0x8e015c03e005d00f4014c04f80820132026c05b80d10206045409c858b0b081f205249b4a,0x4800b6025c04f80820172024c05d80c301ac03e806905040b961a1c5e49c8a,0x5100840150021805c008202e804f8097017202f004b009d013c035409d824b0808161c364264a,0xec01dc03e807a00a801440290097012602e404100bb01ac035407e01d903b4086c10f021d04380a7c18184c40f0e22204c58a49,16384,0xab815b05f422844e9a8a0,0x114037408201790286077c11d82a5062e20547301be2,0x14c03b005100ee01540410087014a0328065811f021004e4084813c02cc06100ed81dd06401064221a563,16417,16384,0x870174020c045015e0308087c12b83280af625587511721,0x1d403b00520094012003e80b70150032406580c7018403e80a2016a033e08f012f029b06c20e0c2ad2323,0x4100828361b562,0x70c9b62b22,16384,0x5400aa01e4025005600ee012403e807b016c022c0440087015803080768144043e090c13e031e06ba0e882ee22a3]) (.b 64 (.p [0xad1aa99,16410,0x39e07441ceca119e1c,16384,0x1c80340058008e01d0020806c00ee01d403b006d00ca017802a007d00a402a804b009a014c0244041009c01be034c06d80d901f403e406580fb022e048008e8115027806280f0820905440a1016402eb05de0c9c2c192a3,0x20807500ec01dc028805500b20174033006500da015003e805200d4024c04b809b014002e4050808b010402e806f80fb01bc037007e00c901ac03680850104034e06ac0d101ef060e0f0c51198f4,0xae01a0029805b00cc01dc025806500ec01a803e807900a4016802c805400f4027c04500a00142028804e80950108020805e009e017602580778127021004ac08e014704861b8c6fa18b5,0x184021006b00ce012002a007a00a401e4025804400b601a802d005500de018002c80830112027c043809d013c027005100fc04c60fd063aa4b6,0x5f00d80110033005300da0148035005b00b4010802c805100f2017802b007d00b801e802a007b00f8015404b80a00142028804e80ca019203ac06400ef020e049c0e184f40cc625d459b9136,0x330059008601bc035006b0136024c04f809d01aa030807380e201ea045c0e2027605460ee41e583c80c1219dc57c0f4a,0x1d003c805a00bc01f0037806b013e0258051009301ae030809181c406160cd81bd03470e121ddc47c148a,0x17c03d005e012a025805a80b401ec038c061010402ae07ec1258387097018203bb9f8a,0xb201e803e805a00ac024c04f809d0172027805d809b0168030809a818b04080bdc1db05470c781ee04241449,0x2e8055c0a5017c02ec05d4122025b07120e881c383b7091616f471c0e23,16384,16384]) (.p [0x2c006500e001b4034007100d801440290054008201f40390093014c028005500ba0172035c06d80d501b2036807080d601f6030808e811e0244047009e016702d6067c0d7818403ee0920123828305960b2416503b507680ed81fc07e3]))))

end OMA.TapeShared245212
namespace OMA.Tape5_7_245212
open OMA.Box245212 OMA.DirectTape245212 OMA.TapeShared245212
private def vals := OMA.PageTree245212.get (.b 64 (.b 32 (.b 16 (.p [1,2,3,4,5,6,7,8,9,10,11,13,14,15,16,17]) (.p [22,23,25,26,27,28,29,30,31,32,33,34,35,39,40,46])) (.b 48 (.p [47,50,51,54,58,59,61,62,63,65,66,67,69,70,71,94]) (.p [95,102,103,106,107,118,119,126,127,132,133,134,139,142,143,158]))) (.b 96 (.b 80 (.p [159,175,185,186,197,210,211,212,238,239,259,286,287,290,305,310]) (.p [311,336,350,351,362,414,580,581,672,673,702,703,828,829,830,919])) (.b 112 (.p [924,1660,1661,0xde0b6b3a763ffff,0x1194016689cceefdec,0x1438153583cd19c1d6,0x19a23e6db0f50228be,0x1caa8dbd637741d2b5,0x1caa8dbd637741d340,0x1fe3aeb80e426218bb,0x21dc775b3d0983f8fa,0x23db429df515f8b624,0x23db429df515f8b6fc,0x2f48238a53aaf207d3,0x2f9c78a8c10a4ecc8d,0x2f9c78a8c10a4ecc8e]) (.p [0x381357d378e3127794,0x38ed7ec8a39c063e6c,0x391e73188090a8ae61,0x3ff9006bf198d98a19,0x4189a5d9998ffb35cd,0x42424a0cfb94beba82,0x47a4f822a6277ee57a,0x4a756a356c78a75257,0x4ac47059c80fdb3bfc,0x4f7d935ff72fb78c3d,0x4f7d935ff72fb78c3e,0x5705d1291130b5012e,0x5953e2ee24156e32c8,0x5953e2ee24156e32ca,0x63b483fd0519192177,0x68155a43676e002c70]))))

private def rows := OMA.PageTree245212.get (.b 96 (.b 48 (.b 16 (.p [0xe78df68f187fe03f800200181050000,0x3cd7a2821f5089d7a2b7d748c58afe00080fe08181100000,0x1cc9cca229c88a8fb2b4ef7d9cdf68c88c4ef7db52dce37db51e323c27b2bc27b2b48c58afe03f820a081812e0000,0xef7db5f36d61ec22f6d7a2612b7dbbdf68dc88188adfc2632358c4ef7db52fb2bc263207eb8df6d5adf50ab688df52768c46b7db58cbdba2bc2231fa2bd8c88c9eb6d56aa11022f65a2216e36d622ba247ec8e8988a11e89e888df56ab6ab8c87a3237d632560abaa12765a2216db588adb588a735bde8c97a3277da3236d4be37db51c58afe03f82fe18181af0000,0x2058afe03f82fe08181010002,0x910707fe03f80fe08181020004,0xae0ffe03f81fe08081010000,0x71cbe22af72f8c950af09ecaf09db5087e37da31148ffe03f820e0c1821b0000,0x1adab6ab8c8f08f08d4284a1021f8df58d30ffe00282fe20182160000,0x16e37db5a96aa2216888e89ec80878888f0203f86fe20182140000,0xeb8df58fce35e8a8c9dbcdf6537db5bfc27c2768c8eca8c4ef7d4bf098c8796db588adf6d447962b7d636ab8522b7d9e8c88c408be8a8c9d9edf6736d5cbe229e8c9da32231022fb29ee8a8c98c85aa5aa888ec888a2daadaae3277db58c469aae12b7db52fc21aada238df58c90a12b8df58c972f70972325ee3588aecaf09e37db58c8db51c88ffe0bf86fe20182b30000,0xa1098ffe03f86fe20182020002,0x9316fe03f86fe28102010000,0x72f709df6d6311cbe3f09db510b72f709bc4723109e368c8ecaf09db51028842b8df68d316fe03f8620281832f0000,0x6ab688db58c4f37d636a3276d6310b6ab11aae3108e358c9e8af08d440a110ae378d316fe00707fe441832d0000,0x168845a210be37d5aae148adf6afc22313adf6d442fa2a325ebe3f09d82be372f8c9d6ff09da322313bdf6d442fb2bc2632160abaa1256888db588a10e96fe03f8ffe44183500000]) (.b 32 (.p [0x1ed9e21e236d6311edf6d442d629aae3689dab11e2388c972f789bc4789e368c85b8db588adb58c45b8df58d2e37db5ade8c85aa84a8c9d9ee36d5e88a7a325688a8c810b5aa116238db588a6ab7ab8c8ac47b8df6d63108e37d6325cbdc26f7af8c950a11ee37db58c4278df6d63237d631131efe03f8ffe44183980000,0x2d316fe03f8ffe44183010002,0x9d9316fe03f86fe44183020004,0x21316fe03f86fe28183010006,0x1f511314fe03f86fe20182030008,0x2d30ffe03f86fe2018201000a,0x91148ffe03f82fe2018202000e,0x8e36d6e0ffe03f81fe08182040010,0x1f8db18ffe03f80fe08181030012,0x2f187fe03f80fe08181010014,0x23187fe03f80fe0018101001a,0x1cdf60878c4737db42e372f88ad23f09d1cca370adbb2b61368c41f8df6d2323b2bc27b2bce37db5d232768c58afe03f8002004843a0000,0x3cdb4f36d39dbb1e22998d98c9d02263119df6d232f66679a02bc1f92a327b08bdf4f097328dc2b6737da31f68c4df6d0becaf098c7ecaf09da31c8e78df6d15db4566547db488a449ec7888ec7e4988ae77d3cd04e4ae37d2327c1d9e37db48c80a02a32458afe03f800203f8a860000,0x710707fe03f800203f84020002,0x1c72f88abdc8c90622bc27b2bc277db48c2238df68f18ffe03f8002004841c0000,0x199d91e76678c744ae789e31fc1f40a02b48c4088e348f18ffe001810203f8a1e0000]) (.p [0x1cdb48c4ecae36d3b2bc25cbdcbe327c27b2bc2631e3ef7db410becaf78de325ce37db48c88cc0ffe03f84020080a320000,0xf34478df6d27f07f078c98f9df6d2310bd959a2ec7d39262295de2777809dd99dd9e31f7d2325cd2f749d1d277da31f7db48c47631022f6d235622b4478df6d277678c77792a31e324b551266884562107e36d2229cbe3707d2f76325dbec88a76327b2a313c278de31c46676476631f92b48c4e4ae37db48c4278df620c0ffe03f840203f91a70000,0x710d8ffe03f840203f8a020002,0xb19cf803f840003f8c010000,0x1cbdc25c8c9dbb2b6d2311cdb48c450ae34f0972f72f8c9f098c710bef8d222b4f38db48c9db48c40a210ae368f19cf803f840204a8c3c0000,0x199d91d98c7e78da780ae78db48c7e78df6d202b48c40a68042b88f19cf8004840207f96240000,0x19e36d278c4f07e36d2356680ad9d8fb2b6738db4bddbe325deca8c98c78c4ef7db42d588ae632631e31169cf803f8a0207f96380000,0x1cbddbe325d8c9d0288adb48c472f8ddbe3278d2f755578d221f488a8c972f72f8c9bdd8c90af88a8c7755e36d042b8db48c98c42f68d588ae368f1aeee03f8a02052164e0000,0x6676479dde36d278c7db48d99d99e31dd6792b8d232768c7e78db49a02842e30a79a02b88f1aeee0080a0207fa5310000,0x7678c40a78c42f8db48d59a02b6763555578df6d202748091152e22b65622a31e311eaeee03f910207fa52d0000,0x1cbe3709e2f76f8c976325d8c9578db488a8d588ae368f1bee603f910205aa51e0000,0x6678dd9e31f89dde231d59e680a8d12b88f1bee600f910207fb6170000,0x1d54ae36d2354adb48e5bee603fa00207fb60c0000,0x7552b88d52b88f1ccd6017a00206436090000,0x158b1cc0203fb00206436020000,0x1d54adb48eb4dd60bfb00206436060000]))) (.b 64 (.p [0x738db4bdcbe326f72f8c98dc2f4bdcbe326370be23738da31f4bdcbe326370bd2f72f8c98dc2f8bddbe325de368c78dd2f87788c7bdde348c98ddbe32dde348c9578db488a8f1d7d20bfb00205fb65d0000,0x1dbdd7552942f488ada374bd2376f8cb8ddbe32f48ddbe32f48ddbe32f48ddbe32f48c98ddbe32e376f8cbd1d7552952d52d52d52d52d52ca8c3e36d232f8d03e360f80f88c98c77552b88c78c98dd54adb48cbd9de15e1528a8c77552b8d232768dd54ada32dd54ae368c78c98dd54adb48cbdb1d7d20bfb002064409a0000,0x78f1d7d60bfb00206436020002,0xbe31ccd60bfb00206436020004,0x2b1ccd603fb00206436010006,0x98f1cce003fa00206436020008,0x566831cc0201d200207fc9030000,0x7678dd9e310bdb48ec51ca09d200207fc90b0000,0x199e364bd23678d232769e36678c7da7776d278c7d278d99e32f49e37749e32f48ddd278cb8f1d9c8096200207fc9320000,0x1d9dd9e374bdb48dd2f48dd2f68c78dd2e374b8dd2e374b9e37678cbe3675d5550f49c9d092952f42b48dd2e37678cb8dd9e32e37678cb8dd9e32e37678cb8dd9e32f8d83e348c3e23278d9d0f40f42552ca8c3e36d232f87552b88c98c78dd54ae36d232f87678dd9e32f88c98c78dd9e37678cbe36d232f87678dd9e32f88c98c78dd9e37678cbe36d232f8d31d9c809d2d0207fc9bc0000,0x98f1d9ca09d200207fc9020002,0x2f88f1cce009d200207fc9030004,0xadb1cce003fa00207fc9020006,0x78f1cce603fa00207fb6020008,0x2f1bee603fa00207fb6010012,0x271bee603f910207fb6010014]) (.b 80 (.p [0x78f1beee03f910207fa5020016,0x2f1aeee03f910207fa5010018,0x271aeee03f8a0207fa501001a,0x78f1aef803f8a0207f9602001c,0x2f19cf803f8a0207f9601001e,0x2719cf803f840207f96010020,0x1f19cf803f840207f8c010022,0x2348f19cfe03f840203f8a030024,0x2f18ffe03f840203f8a010026,0x9db18ffe03f800203f8a02002a,0x1f18ffe03f800203f8401002c,0x2f187fe03f800203f8401002e,0xeb7db4e77d74477d63f07db5e4ae631e3263236eb7db4f36d748fb2b5d3b2838c98c8eb7d746b7d421e311adf5d0b8daae12b48fc234e8a8c9d3a2ba8c80e322324710707fe03f80fe0bf84590000,0x6ab6886a321aae12922bae348c8db48c4f38d746ab688ada8c86aba212bc22325ac5a29a84a0612bc2368c7e8a10bf78d23204eb8db48442b88fce37db48c8e358f18ffe00080fe08484570000,0xf88f18fec002820a08484030000,0x3ce36d3ce36d5ce37db473270a7222a321cbe22bc2478fbdf6d748c42f8ecaf098c8eca738df6d6311cc9c28472210ae23107e23738be22b8f0971cbe22af72325cbe2284f09e2323b2bc27b2a31e310d8fec03f860a084846a0000]) (.p [0xf8db4714e3688ada370be360878dcbe311c278d2f8c42f88d4e222b88c3e2327853888a21cbdc26fef8d2f8c98c450ae378c80e325cbdc25c8c9ef888a0efb6c88a0f8db5d232630a22b8d631c3e35d232758fce36d6313ce3672372310bd8472f8842b8223107e142b4f09d1cbdc25c8c9eca50af098c8ecaf758c98c42dcbdcbe327ce368c90af88a738df68c8df68c4087e37db58c78f19cec03f860a08484cb0000,0x2f18fec03f860a08484010002,0x98f18ffe03f820a08484020004,0x3ae37db58fce36d7a2a31f6d3cdb5ef8df6538df6d6f8fc275f098c4f37db510beca8c8f098c78fcdf6d7410bd3b2a3234f38db5d23e8adb4ea323ce3548ad3c21aada21a8c8e8a48af088c98d2e37db5d2b8fc236d442fa2ba8c88c78c910d8ffe03f82fe184847e0000,0x1aadaae323ae358c8087d6313ce356b168a6a12b50ab84ae358c710b6ab8c46ab8c4238eb8d6321ae37d49d631021f8d6327ae3684af38db58c8d63135d2110ae358f19cda00282fe18284580000,0x30f88c98f19cda002821818486060000,0xf8d43e36d43d636ab8cbe368daae32dae368c88daae36ab8c42f6d6310be234b884ae03e23212e212870e32231c3e35d1a8d2e212b8d748daae32dae232236b8d522b48c42f88d2e212b80f88c84b884a8c90e321aae3688e2b0f8d632021f6d636ab6886a323a2842d2e36d2b84ae03e36d632388c284ae358c78c98fce358fa2b5d3ce35f38d746ab8c46ab8c4238afc2090abaa884af088c7e8a8c98c42f19cda00282fe34486d50000,0x2319cda00282fe18486010002,0x78f19cfe00282fe18484020004,0x1c72f10bbdc8c90f8d6f88a0f8db58c9d63ee313ce36d6310be3672f72f8c9ef8db58c98c88c42c3e3588a0efb622b8f38df58c9e36d63738df6d631f8da3f38d9cbe3709e1c8c9ef888a0efb622bce232631fb29cbdc25c8c9eca50af09eca8c8ee326310b8f19cfe03f861818284880000,0x3ae37db5f38db58d684adbbdf68dcbe3f09dbb2a3235f098c4f36d4b5bb2222a32231fae37db56b8db5ae3f08d5aada22b6ab8c8d6326311aae3f08db52fa2870abaa884aea32232631169cfe03f86fe34284620000,0xf56ab083d632368c8d636ab8cbd6b8daae32f5ae36ab8cbd498dadb5ae32e36b6d6b8cb8dae36d6b8cbe36ae30c3e232632356ab6ab8c8ac3e36d63202ae12b58d22b8d632421e3f38d636ab8daae310be35afae2b8c88c9d9aada21a8c8eb8db584ad63102aea8442b8db51f4aea84a8c42c3e3de37d632788c21f88c88f1aef600606fe34284a90000,0xf8d83d822368dcbe32f68dcbe32e372f8cbe1cbe372f8cbe368c9da372f8dcbe310be368cbe14e222a3223538bed88ad43e230f88c8d43d632632630f8db5be30f5be3276d632f50f80f88c90f88c88c972f8c472f8c4278df6d478fde37da3ee3236d5cbdcbe326f7a327ae37db588a8c47b8df6d6f7bb2a32442dcbdc25c8c9ef8db588a8c40afb6210ae2321eecae36d6324288ada31e310b8f1aef603f8d2e34284cf0000,0x1ee36d63596db51162e220458b88ae36d635a22b58de8c47a310be358dae35689ada8c88c9d9eda12a311a8fa2b6d6310be16aea84a7ba2b6d6313c2e3216e37db584a8c9d2311eaef603f8dfe602845e0000,0x1aadee36ae322b7b8db58c8db55b8df6d6a84a8c2aea84ae358f1bef000c8efe60204220000,0x72f8debe3278bde8c97a3256e36d622a35a22b88f1bef003f9a4e602041b0000])))) (.b 144 (.b 112 (.p [0x7a358adb58d6aa12b68e5bef003f9afea02040d0000,0x1aae368be358dae358c9dab7b6d6b8c8db58daae32f68daae32eb7b8da32368daae32f68daae32dee2321ee36d63216e36d61296e36d612b58f1cce80151afea02044c0000,0x71c2e370be35bdc26370be35bdc8c9be370be368dee2f8c8d6f8debe3275bdebdee358c98de2dee2321ee358c9db58c9da37b68cb8dedb58cbe1cbe3789e2321ee358c9da37b68cb5b888a5b888a8f1cce803fab6aa0204690000,0x5b1cc020252bbed8204010000,0x1e58adb58ee55a80a52bbed8204060000,0x7962b88f1dd76099ab8cd8204050000,0x7962b8db58f0de760a5348ad8204070000,0x1ebdebc3db58c9db58c98de2f68de2e378b8de2e378b8de2e37af8cbbe37af8cbe350f8d630f88c9e350f8d838c87af8debe32f88c88c98debe37af8cbe36d6f8cbe367af8debe32f88c88c98debe37af8cbe36d6f8cbe350f8da30f88c8e350f50f58c9d637ab8cb8c98deae37ab8cbe36d632f8d83e368c3e23238d83e350f88c9e357962b88c98c88de58ae36d632f87962b88c98c88de58adb58cb7962b88c88c98f1e2760a5348ad8204da0000,0x2f8d71dd760a5348cd8204030002,0x98f1dd9c0a52b8cd8204020004,0x7ab79e5b684ad522f684adb58deae32e37ab8cb8deae32f68deae32f68deae32f68deae32f68c88deae32e37ab8cb8deae32f8db1dd9c0a52bbf1c204450000,0x88f1dda80a52bbed8204020002,0x2f88f1ccd80a52bbed8204030008,0x2b68f1cce803fabbed820403000a,0x8d71cce803fabfea020402000c,0x98f1ccf003f9afea020402000e]) (.b 128 (.p [0x2f1bef003f9afea0204010010,0x231bef003f9afe60204010012,0x9db1bef003f8dfe60204020014,0xf8da30f88c8e36d71bef003f8dfe602850b0000,0x78f1bef603f8dfe60284020002,0x2f1aef603f8dfe60284010018,0x231aef603f8dfe3428401001a,0x98f1aefe03f86fe3428402001c,0x2f19cfe03f86fe3428401001e,0x2319cfe03f86fe18284010020,0xf8d748c3e368c3e23238d038c88c9db40f8d438c9d748c38c9db40f6be372f8cbdaf8dcbe32f68dcbe32f5bc38c98c3e36d6f8cbd748c38c9d9cbe372f8c9e2f0f88c9e142b88c3e368c9e14e36d6229ce37d88da31e32230f6d5cbe311c278d6fee3263f36d6310be350afb622a350ad7d8c98c7d6310bd03e360e31c38c88c98c88fcdf6d63ee31f6d6310bd719cfe03f86fe18486bd0000,0x1f19cfe03f86fe18484010002,0x2719cfe03f82fe18484010024,0x2f18ffe03f82fe1848401002a,0x2318ffe03f82fe0848401002c,0x2718ffe03f80fe08484010032]) (.p [0x6678d99e31f88f9e231f867064a6602829e02b48c4088e232039e580ae39e358c7e02263e78df46708c464ae1980a8c46678042b844ae788c78c96676479d99e31d12bc1e32042f88f9e36d602b8e788c78f18ffc000800a0bf8a6d0000,0xe78df5d3de37d7485384adf4663e4ad748d12b5f078f9df5d2310be4a8c88c9eb8df5d12e37d74afc23c21aada21a8c8e8af08d7a2a31e3f37d7410b8c9e8ae632231e310d8ffc00080fe1bf8a5b0000,0xf8d43d74ac3d748c8d636ab8cbd636ab8cbd636ab8cb8daae32f80f88c84b8d612878c3e35d2b8c42f48c30f88c78c8d5aadaae322b0f8d748c8d748fce356ab688afae232078c42d2e34ae12b8eb8d748c8e230a12b8d631c2263f77d634b8df5d2bf78d2b8c8f632231f46ab6ab8c8d748c46b8d74adaae320b6ab11a238d631d22bc2351028442b8df5d2326310b0e31022788c88f19cf400080fe1880ac90000,0xf8d03d03d08d236678cbd236678cbd236678cbd236678cb8d99e32e36678cbe03e231d1e3480a8c88c3e35d278c42f58c3e350e31c3e232231f46678c46678c41f8df5d23263f38d748f92b5d199d91e76631f9e359e02b9e35d231f9e37d7480ad029602b426310b8f19cf400080181bf918d0000,0xa78d9e35d278c7d5be4ad398c88c78c4f35d232f58d39602b50ab8dbae32346fa2a321aadaae321be35d232350a12b58c78c4eb7d63f1bd748cbd7a2a31f42fc6f928b8c84e12a31e31169cf200000fe37f91630000,0x6ab6ab8c8adbe348c84eba2129b4f8d7410ae35d232348c40a110ae358f1aeea00000fe35092270000,0x199d91e76f8d749e31f5d236759db6678c89e31dbe78d7480ad631cb8c29602b88f1aeea000002e37fa22c0000,0x6e34cad748d384ad2311eaeea00000fe63fa20d0000,0x6ab6eb8c8adb8c86e3213e35d212b58d384ae358f1bee200000fe618a21b0000,0x199e364be348d9e232359d99e31e36678cbe19e278c89dbe359e31f58d99e32f58d99e32e76f8d631dbe35d231f4478d7480ad236678c46678c41f8d676e31d39602a32d3e3580a8f1bee2000004e63fb2600000,0x13871be0200000fea3032020000,0x6d32b8d748e941d408000fea3032070000,0x6d32b88f1d3ce080006ea2132050000,0x6eb8dbae310bd748ed53ce08000fee21320b0000,0x6f8d2b8dbadbe2322323569a2f8d2b8daae32356b8d631e368be1ae231eb6eb8c88daae32eb6f8d74ae32358c78dae35d2b8cb6f88c84b8d7484a8f1dbcc08000fee1cb24f0000,0x6dbac3d74ac3d74235d0848bd7484a8db2e36cb8dbae32e36eb8cb8dbae32e36eb8cb8dbae32f46db4c3d43d47d472b5d132d32ca8db2f48db2f48dbae32f48dbae32e36eb8cb8dbae32f40c3e232350f8d631f58db4cad632db4cae358c7d232236d32b5d232db4cae358c78c88db4cad748cbd71dbcc08000fee213a9b0000]))) (.b 160 (.p [0x78f1dbce08000fee2132020002,0x2f1d3ce08000fee2132010004,0x88f1d3d008000fea2132020006,0x1b9e36e78c42f8d748ed53d00800078a30430c0000,0x1b6db44b44b4f580a44b44b2b44cbd4a8db2e36cb8db9e32e36e78cb8db9e32e36e78cb8db9e32f8d43e350f8d03e232231e30f8d748cbe350f40f80f88c78c88c3e35d232f86d32b88c88c78db4cae35d232f8d1b4cae232231e36d32b8d748cbe346e78db9e32f88c88f1db880800078a27c38e0000,0x6678dbd749e31f59dbd631e36cbd236cbd236cb8db2e36cb8db2e36cb8db2e78d99e32f8d71db880800078a3050310000,0x78f1dbd00800078a3043020002,0xbd71d3d008000fea3043020004,0x78f1d3d408000fea3032020006,0x2f88f1bee208000fea303203000e,0xad31bee200000fea3fb2020010,0x231bee200000fe63fb2010012,0x78f1beea00000fe63fa2020014,0x2f1aeea00000fe63fa2010016,0x231aeea00000fe37fa2010018,0x1f48f1aef200000fe37f9103001a]) (.b 176 (.p [0xb8f19cf400000fe37f9102001c,0x3e35d319cf400081fe37f91040000,0x2719cf400080fe37f91010002,0x2319cf400080fe1bf91010020,0x78f19cfc00080fe1bf8a020022,0x2f18ffc00080fe1bf8a010024,0x88f18ffe00080fe0bf8a020026,0x11e37db58f98c7db5ef8df6d3be37d398c98c8d798c98c710d8ffe03f820a0bf8a200000,0x30f88c88f19ce4002820a0880a060000,0xf6d02e37db4be3f63276d7ce37db473270a8c472210ae348c4ecae142bc26323b2a31f4e632632231169ce403f860a0880a370000,0xc3e37db48c88f1aedc00606060880a090000,0x3e36d03e36d2f8c3e23278d9c72f8c9e2f8dcbe32788c750ad030f8da31f48c98dcbe30f8d83be31f4be32768cb72f709bfbe36d2f8c950ada350ae368c70f8d23263f38da372f8c4709e2fef88c98fcda310be03bec88a8c7d3c27b2a310b203e348c3e23278d9cbdcbe326f8c3e2f8c9e070f488a0f8d2324222373b2b8db4be30e327672f72f8c9bfbe368c90afb22284738df6107e36d23203d7488a8c42e31f1aedc03f8d060880ad80000,0x98f1aede03f86060880a020002,0xf8d748c38c9d230e3276d31aede03f860a1080a0f0000,0x88f1aee403f860a0880a020002,0x2f19ce403f860a0880a010006]) (.p [0x98f19cfa03f820a0880a020008,0xf8d630e31f6d230e31f6d03e37db46678d92f48d92f48d92f8d022636678cb6788c747880a8d9e36d278c42f80f88c747880a8c80f8d199e31199e3107e34243e368c70888d98c466310bdb46671191f8db420180a8c42d1e3580a8c90c3e35d232631e32230f6d3cd74678df6d19c1929980a66780a8c844ae631e32792a322310b8f19cfa002820a0bf91af0000,0xf8db48c3d03d03d098c98c3e36d278c42f60f8d83d838c78c78c3db48c42f40c3e231e32631e3f76d2310b8c8d748f19cfa00e860a0bf913f0000,0x9db19cfa03f820a0bf91020002,0x78f19cfe03f820a0bf8a020004,0x2f18ffe03f820a0bf8a01000e,0x3e36d03e36d431e32230f6d748c42f6d03e36d630e31f8d83d838c88c78c88fadb5d2310be36d318ffe03f82461bf8a340000,0x8d718ffe03f82fe0bf8a020002,0x2718ffe03f80fe0bf8a010012,0x1f18ffe03f80fe0bf8401003a,0x2f187fe03f80fe0bf8401006e,0x23187fe03f80fe03f84010070,0x1f187fe03f80fe03f810100a2])))))
private def data : Store := ⟨vals,rows,model,7,false⟩
def ok := test rule 5 7 data
theorem finish (checked : OMA.Tape245212.Before ok 189) : Deny 5 7 ![⟨2,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨8,999999999999999999⟩] := by
  have same : data.vertex 188=![⟨2,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨8,999999999999999999⟩] := by decide +kernel
  rw [← same]
  exact close valid _ _ data 188 checked
end OMA.Tape5_7_245212
namespace OMA.Tape5_11_245212
open OMA.Box245212 OMA.DirectTape245212 OMA.TapeShared245212
private def vals := OMA.PageTree245212.get (.b 128 (.b 64 (.b 32 (.b 16 (.p [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16]) (.p [17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32])) (.b 48 (.p [33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48]) (.p [49,50,51,52,53,54,55,56,57,59,60,62,63,64,65,66]))) (.b 96 (.b 80 (.p [68,69,70,71,72,73,79,80,83,84,85,86,87,89,90,91]) (.p [92,93,94,97,100,101,102,103,104,105,106,107,108,109,110,111])) (.b 112 (.p [114,115,118,119,126,127,131,134,135,136,153,155,159,160,164,166]) (.p [167,169,172,173,179,180,181,182,199,203,205,206,207,214,215,222])))) (.b 192 (.b 160 (.b 144 (.p [240,248,254,255,290,320,322,323,329,374,375,398,414,415,436,455]) (.p [526,604,701,703,830,831,1208,1209,1662,1663,0xde0b6b3a763ffff,0x12fbd81c64fa4d50de,0x1578f53917add90308,0x1578f53917add9030a,0x1578f53917add9030e,0x18b652cfa1171f7af5])) (.b 176 (.p [0x18b652cfa1171f7af7,0x1bde27cee26ba7b932,0x1bde27cee26ba7b937,0x1bde27cee26ba7b944,0x1f856d06e271f6afe9,0x1f856d06e271f6afeb,0x1f856d06e271f6afed,0x1f856d06e271f6afee,0x1f856d06e271f6aff0,0x1f856d06e271f6b022,0x1f856d06e271f6b0d0,0x21ae45c984343d04ac,0x2446eb1001ea74d53a,0x2446eb1001ea74d53d,0x2446eb1001ea74d53f,0x2446eb1001ea74d540]) (.p [0x252798b11ff870b1bc,0x252798b11ff870b1d1,0x252798b11ff870b1e5,0x296d7907bcd54ca999,0x296d7907bcd54ca99a,0x296d7907bcd54ca9a2,0x296d7907bcd54ca9a4,0x296d7907bcd54ca9a7,0x296d7907bcd54ca9b3,0x296d7907bcd54ca9be,0x296d7907bcd54ca9bf,0x2ab912b6d19858ee6a,0x2edbd30b17ee23fb26,0x2edbd30b17ee23fb27,0x2edbd30b17ee23fb28,0x2edbd30b17ee23fb29]))) (.b 224 (.b 208 (.p [0x2edbd30b17ee23fb2a,0x2edbd30b17ee23fb2b,0x2edbd30b17ee23fb2d,0x2edbd30b17ee23fb2f,0x2edbd30b17ee23fb30,0x2edbd30b17ee23fb34,0x2edbd30b17ee23fb36,0x2edbd30b17ee23fb51,0x2edbd30b17ee23fb62,0x34fe623ffa1fcfb2d4,0x34fe623ffa1fcfb2d5,0x35edb87fbe1f8b5185,0x35edb87fbe1f8b5187,0x35edb87fbe1f8b5188,0x35edb87fbe1f8b5189,0x35edb87fbe1f8b518d]) (.p [0x35edb87fbe1f8b518f,0x35edb87fbe1f8b5190,0x35edb87fbe1f8b5191,0x35edb87fbe1f8b5194,0x35edb87fbe1f8b51ae,0x35edb87fbe1f8b51d2,0x3738658a7790343655,0x3a969752817537b8d9,0x3c69512421cf99fa26,0x3cfd3ddfa301945010,0x3e25ea9a1dc8978473,0x3ee788f996852ff3da,0x3ee788f996852ff3de,0x3ee788f996852ff3e1,0x3ee788f996852ff3e3,0x3ee788f996852ff3e4])) (.b 240 (.p [0x3f82cda5402b7f0c74,0x4454c8442f9bfcfe11,0x454ba0d69f40f462b1,0x47d37ed16c665b1879,0x48a05eb73bb0f1dc16,0x4a3fe056d5882f1e95,0x4a3fe056d5882f1e97,0x4a3fe056d5882f1e98,0x4e614011fa601aaaeb,0x4e614011fa601aaaf2,0x4e614011fa601aaaf3,0x4ea40b4f5f36aacc57,0x4ea40b4f5f36aacc5f,0x4ea40b4f5f36aacc61,0x53f87dfff6b08d2044,0x54e574efde0f611c97]) (.p [0x57c99afff64436733b,0x582994e65ef372327f,0x5a34a38fc00a00269e,0x5a34a38fc00a0026a6,0x5a34a38fc00a0026a9,0x5bbacead425b5b4ec1,0x5c9d39bfdaf9813683,0x5d25a8e52220966aa8,0x5e0e4ce25fa68666b3,0x5eb3849b131bf8f276,0x5fc7cc224fdcd69669,0x68155a43676e002c70])))))

private def rows := OMA.PageTree245212.get (.b 288 (.b 144 (.b 64 (.b 32 (.b 16 (.p [0x723f09dbb2821f611cdf6d748c4238df6d748c4160bfb00fb00070305021a0000,0x6b6d746a12ba2bc21adf5d2327513a2b8df5d23160cfb010301fb0805031a0000,0xeb7db5ef7d5ae8adf68fc235e8a8c91fcdf6d7bddcc9c29c88ade323c2758c7ecaf098c85aa8bb237d56489a96888df6d47ec8d7a27588a7b6d565aa849a9e888d6229a6a320284adf58c97b7da3737da32357a325e88adf6d63237db51c40f0cfb01fb04fb0805037e0000,0x1c0a22b7db58c4ef7db52dcdf6737da3235723244ecae2323c27b2b5087e37da31610fb02fb04190c05042b0000,0x1edf6d7411edb55b7db5a96da22222a21022f77b7d5aafc2358c98c408be8a8c9737db5be37a32757a32631022fb2bc2632047b7d636ab7a32232765aa588db588a7358de2b578978adf68c8d4be37db51d6a96aa223b2021f588a2daadaae323c20284ad421f8df58c91610fb02fb04fb1a05048d0000,0x237d741610fb01fb04fb080503040002,0xb160cfb01fb04fb080503010004,0x9df6d04160bfb00fb00fb080502050006,0x8e359a0bfb00fb00fb000502030008,0x776d2256654788add99dd9e31f7d278c975d737da31f7da31dd88adf6d231f7db413bdf48f98c9db410b566566887884ec7e3488a676d112b69c4f07e37d2325cdf68dcbdc277da31f48fb2b48ddd23274ecad04f09e37db48c7df6d04088e37db49a0bfb00fb000100fb06820000,0x1c8dc8c7dbb2821c2237db5d2311cdf6d1cdf6d1c88a0878c88c4737db5d0bd3b2bc25cca3ecad9cdf68c713b2b8df6d2320b73270a7222bb2bc2421f8d631fb2bc275d23ef7dbbdf6d3cdb47222a3087d3c27b288f09eca8c872f89c277db5d3b2b4f09f36737d87ecadf48c8f09ecad631c42fb2b98c9da3160cfb00fb0005020d06a10000,0x1aada234ae311a8c4238e8af0869aae12abf08e37d748c96b168a6a12ba2b511ae37d63107e36d631fa2bd8c8d748fadf5d3cd7a2a327adf5d1adf56b7d47e8adf48c9f08e8a8c7f088c42fa2a3160cfb000100fb060d06670000,0x3adf6d225a2234e89ec813adb4ec82fa256a96aa223b236d7411687a2765b8db55b6d475a2202aa127688a596aa126a5aa888df6d621fb20bd74849da21fb23ad92db5d16db5d16849d3a2622bb23a2621fb2042e2160c0100fb02fb060d06710000,0x3adf6d3adf6d7bdfc2631e32040f0cfb02fb02fb060d06110000,0x73b2b5bfc275ecaf09737db51f7db5d2313adf6d7cdb5eca8c78c4ef7db5d0bf0972f72f8c9f09ecaf098c771cbe229c8c9ecaf09738df6d631e323b28bf09da31610f102fb020d060806560000,0x3bdf6d23f36d3b2a3236d3b2b4f09ef7db4ef7d3c26321cdf6d5cdf6737da3207ecaf09737db48c88c7ecaf098c88c4f37db58fbdf5f098c7d7b28bf091610f102fb020d060d09510000]) (.p [0x1e31610fb02fb020d060d06020002,0x1aada21a8c8e8adb48c4eb7d746ab8da236d1a8c8e8a8c96ab6ab8c8afc2231cbeabaa884af632231610fb020502fb0e0806350000,0x5b7db5d2a8bb237d7adf6d7adf6f088c7e8a8c9eb7da37a2ecadfc2632355ba26aec8d6229ad9a8c8e8a0a12b7d63277d87f37db4537db5ef7da3737daff098c8d7b287f098c8ecaf0971cbe22b7bde8c9d9cdf6d63237db58c78c8112e37db5ae3f08db5d3adb55aa8bb235116df6d4be8988788af36ef7dbcdbb2a322313bdf6d4bf091fb2a320b1610fb02fb06fb0e0806b60000,0x91610fb02fb02fb0e0806010002,0x3adf6d63ef7d7c2631f6d6313adf6d748cbdf5d23eb7db58da6a3236d7a2a31f6d3a2bc22313adf6d3d8c82e32761610fb02fb02fb0e0d093d0000,0x71610fb02fb02fb0e0d06010002,0x81610fb02fb02fb060d06010006,0xb160cfb02fb02fb060d0601000a,0xa160cfb00fb02fb060d0601000c,0x9160cfb00fb00fb060d0601000e,0x8160cfb00fb00fb020d06010010,0x199d91e76678c7f07d63e77db4677db4477da32198c7e4a8c810be4af070a02a3160cfb0001000502fb0e2b0000,0x39dbb1c45668bb1f42d59959a21d5887e49888ec7e49579277db48959a2547dd5887e49888d7927b1c42e2160c0100fb020502fb0e390000,0xe77db48f9df6ef7f098c78c8d040f0cfb02fb020502fb0e120000,0x3bdfc27bdf6d2f8fc276d54df6d1cca370ad9cdf68c7ecade323c2631fb2bc2631e313cdb4eca2fc27cd9cdf6bfc25cdf68c7da31f4ecaf09db5d2313cd9cbdcbe327c2768c4777db42dcbdcbe327c2631fb2bc2768c80af89c277da3737da31f4eca8c4537db42fc25c72f88abdc8c9e37db48c8f098c72fb2bc2632231610fb02fb0205021d0ea70000,0xe78df48f98c4f37db5d232f4e4a8c9db9df6777da37627622b77632631f4566547d222999e3649da7f07df48c9df623bdfc25cbddbe3274763277db48c88c7111e37db40a78fc1f6d11e37db49959a21e2288e78df6d1d8c408bdb4ecaf0923b2a31cb676d27f07db5d231199e3647d676678c7f072f92a32481610fb02fb020502fb1ea20000])) (.b 48 (.p [0x71610fb02fb020502fb0e010002,0xb160cfb02fb020502fb0e010004,0xa160cfb00fb020502fb0e010006,0x9160cfb00fb000502fb0e010008,0x39e37d74e75d204e580adf56e36e3235e8a8c78c4e77d742e3279df5f078c4e77d742d99e3647d676631f4e4ad748c46749e31022f59e36678c7d7c1cbe4a8c98c8eb7d3c22313adf5d0b6ab6ab8c8f08df48c4eb7d636ab6886a323a2a31f4e8a2fce2322327c2231e3f36d748f92b5d042d39539611d3847e87e484e0e48d7a1e110b84a160cfb000100fb06fb0eb10000,0xe77db58fb8c7db5d23139df6d748cbd748fcd7cf09d63139df6d748cbd3c2231e3276d748c210bd74e76d7adbb2221f9db5d042ca160cfb00fb02fb06fb0e460000,0x9160cfb00fb00fb06fb0e010002,0x8160cfb00fb00fb02fb0e010004,0x1c4170bfb00fb00fb02fb0602000e,0x2bdc277db5d2311cdf6d5cdf6f367222888c710b71cbe2284723109e231dc72f88a11c8c4278d2323b2bc27b2b7d748c4db5d23109e37db5d239a18fb00fb0109040d064d0000,0x6ab6ab8c8db5d2311aada22bf08f0810b6ab6ab8c8e36d631f5e8ad4284ae37db5d232e1cfb000301fb0a0d062e0000,0x71e88a7af88a7a327b29c72f88af090a22b7d2323513c278df6d232e1cfb01fb051f0f0806240000,0x1aada21adb58c8e8a6b8df6d631f51028442b8df5d232e1cfb010b05fb2008061d0000,0x5b8df6d5edf68de88408bdde8c98c8d56a96222287eb7db56ab688adeda32231fa2a325edf6d5c72fb622b5bde8c97a229e8c91fb2bc263216a96aa223b22229e5b6d6210ae37db51c4221cfb01fb0cfb200806620000,0x796db588adf6d447b7db510b6ab11eae3108e2325e7a210ae368c85b8db588adf6d7411edb588458ae376ab7ab8c88c97b8db57a229688af098c85aa58888a796db58842b8df6d472daada22b13c238df5d2327771ebe22af7a327b2847b8df6d63109e37db5d23237db5d042e23fb01fb0cfb200806900000,0xb2e1cfb01fb0cfb200806010002]) (.p [0x92e1cfb01fb05fb200806010004,0x237db52e1cfb00fb04fb0a0806040006,0x3b2e1c0100fb04150a0d09010000,0xf38d232e1ce6020904150a0d09040000,0xef7dbbdf6d23f36eca8c8d3c27b2a323be37db5f36eca8c7f38df6d5c72f88af091fb2a323c27b29cbe3709d1c8c9eca73270a7222bb2821e323b2bc277da32231c4221ce602fb0a150a0d09580000,0x3bdf6d7bdf5f091dcbfc2542bc26321cbfc27b2bc2758c78c4ef8df6d74be3f09db5ef7d7c25c72f88a50af098c88c72fb2bc25cbdcbe327c275d2313cd9c0a22b61e313cdf6d042dcbdcbe325ce2326321cecae36d472fb2bc27b2b68c872f709bdc8c9ecaf09738df6d47d840a210ae37db58c78c42e23e602fb0a150a0d099d0000,0xb2e1ce602fb0a150a0d09010002,0x92e1ce602fb04150a0d09010004,0x2a32e1cfb00fb04150a0d09020006,0x16aa2116aa22f7d2a5a2216aa127b2165aa849a96888db5887116aa1489dbb216dea5aa888ec888710beb8df6d212622e1c0100fb04fb160d093f0000,0x1aae3f08d5aae3688dab6a323a2a31e311aae3f08d742daada22b6a323a2a32522bc21aada21a8c8e8ad4284adf6d631e313adf6f6321adb5d23e8ad5aae3688d2b6a323a2a327c23a2a31c42e32e1cfb020904fb160d09670000,0xeb7db48fadf6d7cf07dbb2a31e3235d04221cfb02fb0afb160d09160000,0x14e37db5bdeeca8c972f72f8c9bde8c90a22b7d631deeca0878c972f73b2af8c950af09087da3223114e37db57b8df6d6f7bb2a324779eeca2a325cecae37db572f709bdee358c98c7eaf88af098c82fb2bc2632e24fb02fb0a2d160a096f0000,0x1e58adf58dae37db5adee8aae3223276d16e37db57b672f7af8c9bde8c98c87962b588a1de7ba28a8c98c811e8fb2b6d742d65aa849a9688888a6ab79a25a26b8c8afc22311aadadb4ae322bf082fae2a84a8c92e24fb02fb0afb2e0a096f0000,0x82e24fb02fb0afb160a09010002,0x4b8df6d23f38db4e8a8c8dbce37db58c4f38df6ef8dfc263223107e35d3b2bcf078c4f3c1cbe8a8c98c82e24fb02fb0afb160d0b380000]))) (.b 96 (.b 80 (.p [0x1c42e23fb02fb0afb160d09020002,0xb2e1cfb02fb0afb160d09010006,0x92e1cfb02fb04fb160d09010008,0xa2e1cfb00fb04fb160d0901000a,0x82e1cfb00fb04fb0a0d0901000c,0x72e1cfb00fb04fb0a0d06010014,0x2442e18fb00fb01fb0a0d0602001c,0x1cbfc277db58c472f72f8c9bdceca8c9eca2dcbdc26ff090af88a738df6d47e37da323ce37db58c9738df6d631f6d748c40a210ae37db5d23852ffb00fb04170b0d084b0000,0x24834fb01fb0cfb200808010000,0x1cbdebe326f7a3256e37d6d88a7b8df6d63244087e37da34834fb01fb0c40210a091f0000,0x1aada22b7b8df6d6b8c8d631021f8de34834fb01190cfb410a09150000,0x1e58a58a7ab8c97b8df68c8df6d63116ddeae325e7a22962a32042daac47ab8c4238d6325e708bde256b622847b8df6d63109e368c85b8db588a087df6d63116e37da37b8db57a229688a8c8d42adeae322b7ba2a322325e58a58a7ab8c97b7da3237db58c47b7db510b6ab11eae3108e2325cd6f78911e278da3216e36d622b6d475aa588db588a10b4834fb01fb1afb410a09b70000,0x94834fb01fb0cfb410a09010002,0x2354834fb01fb0cfb200a09020004,0x1f7db54834fb00fb05fb180a08040006,0x6ab6886a323a2b6d2311ae36d74adaafc22321aadaae32358c76abf080878c910b0ebaa884af38db5d232350a12b7d634834fb000b05fb180d0b400000]) (.p [0x16e37db5d2248340100fb0c31180d0b070000,0x3cdf6d748c4f3c1c42e34834df02190c31180d0b0d0000,0x1e8fb2b6d23538df6d5cbe313c278db57afb62287f098c8d7b29ce37db5bdeecae377af8c88c97bb2a325cbdc78ae35be32542bc2768c8eca1c43d34df02fb1a31180d0b4d0000,0x1eecadf6d5cbe3709d6f7a324288a8c78c4538df6d5ce37db5bdeecaddebe322324710b79eeca2a327b29cbded748c98c472ff0910b7afb622bc087e2327b2a321cbdc26f11ee37db58c4278df6d478c4483edf02fb1a31180d0b6b0000,0xb4834df02fb1a31180d0b010002,0x94834df02fb0c31180d0b010004,0x2a34834fb00fb0c31180d0b020006,0x16a96aa222248340100fb0cfb320d0b070000,0x6ab79aae3278d1aae326b8c8afc21aac47b8db5ae3108e37db51e3112e37db5d2bf086ab8dadab8c8dabf08e8a1c42e34834fb02190cfb320d0b400000,0x7ab8442f8db5d215aa84adf67a37965ba24988a88ad9688a8c87b8db58c458ae356b6d6b8daae3276adedf6d63223102ae379e58aaa12a323510b8c9596aa126a88a72f7af8c97b7db58c9d6311e58ad9cbe37af8c9d6f7a327b2a32042fde358c95a22a32231e311e8de5ba24a2b6d748d688ad7410b4834fb02fb1afb320d0b9e0000,0x94834fb02fb0cfb320d0b010002,0xa4834fb00fb0cfb320d0b010004,0x84834fb00fb0cfb180d0b010006,0x94834fb00fb05fb180d0b01000e,0x7d84492ffb00fb04fb180d08030010,0x72f72f8c9bdee37db58c9087da311ce37db5be311cdaf8c4238d6f7a327b29cbc47af8c4278df6d4710b72f709bdebe3244087e37da323c087e37db58c9db58c40a210ae37db5d23854af800fb0a351a0d0a600000])) (.b 112 (.p [0x796a9e88888a6ab7ab8c8e23256aa229e7a229688ae368c8d96e36d622b51021f8df6d63664df700fb0bfb360b0a300000,0x1aadaae322be821f8db58c87b8df6d7484a0abaa12b7d63664df700170bfb360d0c1f0000,0x5aa588d62664d0100fb18fb360d0c060000,0x1e58ad9cbe311ebe3109e2f79e58ae3588a8c98c872f789bdee37db58c9e36d478de7962a2284ecbe37db57b672f7af8c97898c85b588a1c42d688a796e36d742b7d6379ee8a296a962212842e3263664df702fb185e360d0c690000,0x1e58ae37db57b56ab788d6b8c98c44b7db58c42f8d96aa229e7a22962a32078de58adf6d748c42f858a6b8db5adeade59eae1278aa12a321eae326321aadeae3236d478dae36d74ade5abaa12b47ab8c98c810b48a8c9664df702fb18fb5f0d0c730000,0x8664df702fb18fb360d0c010002,0xa664df700fb18fb360d0c010004,0x9664df700fb0bfb360d0c010006,0x1f68c4674af800fb0afb360d0a040008,0x796e36d622b6d6311e5aa58888a8c47b6d6310b6ab7888c92d6aa229ebde25629ebe32047b8df6d63109e368c858a087db58de58ae358dee35ae3278d9e7a22962a321e582849e36d62296e36d622b8db58c758a6ab7ab8c8d6326310b72f789bde25e256e36d6228288adb58c4087e368c85b8db588a087db5d238568f800fb0afb360d0aa40000,0xb854af800fb0afb360d0a010002,0x8db5d23854afb00fb04fb180d0805000c,0xb852ffb00fb04fb180d0801000e,0x8e36d748a2ffb00fb01fb0a0d06050026,0x2f89a18fb00fb01fb0a0d06020028,0x8db59a18fb00fb00fb020d06030046]) (.b 128 (.p [0x199d91d98c7e4ad112b7db48c4084238df5d237418fb0003010502fb0e190000,0x72f8dc27472327b2a313bdf6d042dcc9c29c88adbb29ce37da31f88c7ecaf09738df6d08da311cbe3f09da3ecad7bdf6d1cbdc25c8c9eca8c8eca8c7f0910beca72f8dc27472327b2bc27b2b611ce37db4108e37da31fce37db48c9088df6d632a1cfb00fb0405021f0f800000,0x7599d99e31e78c9d959a229d7622b68c78c4777db410b56654788a66711d9e3107e278c972f749749578df488a11de37db48c4278df68c7db48c40a79a044adf67625622b77792a32631c42d59951e68845668841f888a755db48842b8df6d086676476631f92b41392b8df5d2325cd2f76f8c976327988ad04f09e37db58c7df62a1cfb00fb040302fb20ac0000,0x566566887ec70a02622a1c0100fb040504fb200c0000,0x1decae36d225622b7d746678c40842f6d749f98c78c98c4e77db5d042c2e37db47627552a22b7736be31022f4bdd8c976f88a8c78c4537db410b7792a326321588a778df6d2f8ddeca8c9d9cbdc26f76325dbec88af098c8eca8c7f098c40b8df6d23f08db4eca10b8c7667647d67667f079e31d99d91e76631c29e02a32631199e3e678c7db410b44af078c92a1cfb02fb040504fb20bb0000,0xa2a1cfb00fb040504fb20010002,0x82a1cfb00fb040502fb20010004,0x7d042b18fb00fb040502fb0e030006,0x1cbddbe326f778df6d23277db5d2311ce36d2376f88ad1d8c9eca72f11cbe3109e37db42042dcbdcbe326f13c278df6d631dde4ae37db5d23276d2313b2b8df6d63742cfa00fb040503371b570000,0x6676476631f92829e680ad19e37db4236d231112b8df5d23742cfa0009040503fb38200000,0x7552b8df6d23432ef900fb0a0303fb38080000,0x5665479959a21e2432e0100fb0a0504fb380a0000,0x763755e4988a88ad9cbe372f8c9d2f777d2326311decadf6d042fce232631dcbc4749e37db422313ce37db4778db476229588af0972f709bdd8c976fb222bc2768c78c810b5622b9e23263432ef902fb0a05046038640000,0x1de4ae36d152b7db4777d236749e327675d88a8c78c4777db410b6677678c79e32559a22959a229d56229529de37db48c9df68c722311d8dd56680a80adb456654788ad442d99d99dd8c76678c9d631e3119e37db46677599e32768c72042dd9e680a44a8c9432ef902fb0a0504fb61870000,0x7432ef902fb0a0504fb38010002,0xa432ef900fb0a0504fb38010004]) (.p [0x88c4442cfa00fb0a0503fb38030006,0x1cbdd26f778df6d23276d2311cbe3749d2f7552a32442fce36d2325cbdcbe326f11de37db48c4278da31c456210ae37db5d237445ef00fb0a05046239430000,0x678db49e311d56680a8c41f8d959a229d76229588a767778df6d231f6d232768c476375598a2b610b54a8c77559a22999e325d1d59a229d54ae368c71159a210ae37db42159845668842f6d7488a6599c42e7778db49e31f7d678c95745ef00fb0b0504fb637a0000,0x7559a229529d9e325d54ae368c7db48c47748d99e32767552b68c78c4776d042d99dd9e31e78c910b56688a76f74954a11de37db48c4278da31f4578db488adf6d748c47458ef00fb0b0504fb635a0000,0x2f67445ef00fb0a0504fb63020002,0x1f5d237445fa00fb0a0503fb38040004,0xb742cfa00fb0a0503fb38010006,0x9742cfa00fb040503fb3801000e,0x1f5d23742cfb00fb040502fb0e040010,0xb7418fb00fb040502fb0e010012,0x9e369a18fb00fb000502fb0e03001a,0x1aadb6ab8c711a1f8d2b8c8eb8d748c8e8a8c44b8df5d2b8fc23510b6ab6ab8c8f080a12b88c7f38d748c8e8ad42277d632e1cee000100fb061d0e410000,0x6676476631f92b48c46678fc1f5d042d99e31199e3107e348c8e789e580ae78d748c7d0280a089de32e1cee0001000d06fb1e360000,0x139539611d3e358474f8df5d212612e1c01000100fb0efb1e130000,0x6d39531f5d212932b5d23113ddbadb2231d99db1e76c78c82daadb2046c8e358c76676479c46e78c41f8d748c8d13e35d212b48c46e36f5d256e11cad744d396023595384784a10b6676678c79c46f7d748c41f8df48c86ab8da234adb8c80aba212b411bdf5d23108e37d631f5d232e1cee020000fb0efb1e940000,0x6f8d74e4adf46678c46678cbe35d276f92231f92a3223111df5d2310bd52e37d74ae36f8d2b8c8d1b4fa1ca8c88c44f7d7410bf088c72e1cee020101fb0efb1e480000]))))) (.b 208 (.b 176 (.b 160 (.p [0x92e1cee020100fb0efb1e010002,0xa2e1cee000100fb0efb1e010004,0x82e1cee000100fb06fb1e010006,0x78c42f18f0000100fb06fb0e030008,0x6f8df5d238630e4000000fb0cfb19060000,0x1aada22b6eb8c8f38d748c8d748c40a110ae37d638630e4000101fb0c351a1b0000,0x1be348c4678d749db9e31e3108e358d39602b56f8d6311aae36eb8c8e2b6e3223107e1b8c84e12a31d34e580895384784a66764466710be359e31dbe35d231f9e37d7480ad029602b7d232358c44a30e4000101fb0dfb36670000,0x6d396129b1d32b5d236f56c74ca8c46f5d042d966710b9db1e32042db4e110ae358c7d744f8d7484ad748dbd5badb2231f48c46f5d2310be348d32b4678d749e311b1f86c74e02a322310b6ab6eb8c86e3235d231028442b8d631d99d91e76e78c7d748c40a796010ae348c8d13e35d212b5d23864be4000101fb0dfb369a0000,0x2f58630e4000101fb0cfb36020002,0x1f48630e4000101fb0cfb19020004,0x9e35d238f30f0000100fb06fb0e050006,0xbe239a18fb000100fb06fb0e030008,0xe632e1ce70005020d061d0e020000,0x3b2e1c0100fb060d061d0e010000,0x1c7328c973688aeca8c472f72f8c9f092dcbc4f09e37da321cbdcbe3244f09e358c7ecaf09da313cdb5ef7f0971cbe22b4bdc8c9ecaf09da32231fb2bc2442e32e1ce502fb060806130e550000,0xf38db5d2313b2b8d7c27b2bcdb5d23ecad9cbe372f8c9d6ff091e313bdf6d742dcbdcbe325c8c98c472f8fc27673270a7222a31cbeca8c8f09eca8c7f098c4ef7d748fc27610b2e1ce502fb060d09130e5e0000]) (.p [0x2232e1ce702fb060d06130e020002,0x3ce36d748fb2b5d23f3c1e32768c4e77db5d2310bdbce36f37d9cdb4bfc2768c78c4f37db48c42f8ecaf098c8ef8df6d1cbe3709d3c26313cdf6d2310be3b288f0972ff09db48c471cbe22b4bfc24becaf098c88c7ecaf098c4ef7d748fc27610b8c82e1ce702fb060d061d14830000,0x72e1ce702fb060d061d0e010002,0xa2e1ce700fb060d061d0e010006,0x2632e1cfb00fb020d061d0e020008,0x3ce36d748fa2b6d23f38db5d23e8adb5f38db5d3b2bcf07f088c98c78c8d6313adf6d748c42f5d02aa1ec8db4ec888aeb7d746b8df5d2b8522b7d3c223263e77db5d2310be360ab8daae3234f086ab6ab8c8f08e8a8c98c44b7db4ae3f08d842e31fcf098c4f3610bf078c8e8a8c92e1cfb00fb02fb0e1d0e930000,0x82e1cfb00fb02fb061d0e010002,0xe77db5f37db4f088c7d748c4e77db5d2310bdb5d234e11132f6d74e4880adb40a78fc1f6d63f38db5d23ecad7cf088c98c7d23139df6d748c42f5d029a0566808db5ec788a6678c4f07e36d199e3e678c7d199d91e76631f92a32631199e36769e31f6d7410b8c80a79a580af07e4a8c92352e1cfb00fb02fb06fb1e980000,0x1c43118fb00fb02fb06fb0e020002,0x3ce37db5d234d34db0009040d061d0e070000,0x1cbdcbc4f09e2f8c9f38d2327b2b48dce368fb2b5d142bc25cbfc2542bc2631c42fce36d2325cbfc2542bc244738df6d23108e36d2323be37db5d222b7d634d34db00fb0a0d06130e530000,0x72f73b2b8d2f8c950af38df6d748c9d748dcbdcecabe32542bc25cbc4f09e37db48c872ff09f09ecad631c42fce36d748c9ef8df6d7488ade34d34db00fb0a08061d144c0000,0xef8df6d74be3f09d9ce35d2f73b2af8c950af098c8738d74bdcbfc26f8c950af0972f72f13c278be327ce348c90a22a32231e3ef7db5ef7d9cbfc27c27b2a32231c42fcf078fcf0710b8c9eca4d34db00fb0a0d091d14660000,0x84d34db00fb0a0d061d14010002,0x74d34db00fb0a0d061d0e010004,0x98c44f32e000fb040d061d0e030006])) (.b 192 (.p [0x1cbdcbe325cecae36d748c9ef8df6d7488adb5d231028842b8df6d638e50d600fb0a0d081612250000,0x1cbdc26f723276ef8db5d2f88adb5d23738db572f8c7bdcecb8c972f11c278da31fbd2f88af36d2325cbc472f8c4278db48c8da310bef8db5d2228288adb58dcbe311cbe3f09e35be3109e142bc25cbdcbdcbfc26326f8c9f388c9ef8d622a31fc25cbdcbc4f09e2327b088e368c972f11c278db58c7ef8db5d222b60a22822368c8ef8df6d7488ada310b8e50d600fb0a0d081d17b90000,0x7db5d238e50e000fb040d061d0e050002,0x2f8da39a32fb00fb020d061d0e040004,0x1ae36d74ae36ab8fc234ae3234f088c4f35d042fa29aada22b6a3239ae12badb48c8e8a8c46b6d2b6ab6ba2a322b8c848af0810b4f8df6d7484a8c96ab6886a323ae36d7484ad748c46abeb86ab1eb8c8f0810b6ab6886a3235e8a8c46b8df5d23109e35d2327ae36d21282aeaa212a31faf02278df5d232748c88c45632bb000502fb0e1d0ea50000,0x1aae368be350878da2eb6a32348daae32dae348c8d236ab8cb6b8d23212e35d2129ae37d742748daadaae322b8cb4b8d21283ac3e2323ce37d6b8c7e35ae3089e35d232368daadaae322beba2daeb8db5d212b58c4e8b8c78c86ab688ada8c813ae37d74ae110ae35d23243e36d2b84a8c42d2e36d21283f38df58c9de313ce37db58c41f8db58c869a8c8eb8db5d21282ae12b5d2348ae37db58c7db5d239a57bb000502fb0e1d0ed30000,0x2e39a32fb000502fb0e1d0e020002,0x3cf38df6d631f6d748c4f3c1fcd232042fae36d742a35534dc000d061d0e130e1d0000,0x3b55340100fb0e1d0e130e010000,0x3cd94e37db5d2ff09f098c7d02be2f09df5f09f3672f72f8c9bfc24772f72f8c9bfc25cbdcbe3277d878c88c4f36d1cbe3f09d9cbdcbe326ff098c78c82fb2bc2631e32044134dc02fb0e1d0e130e5b0000,0x1cbdcbe3274bfc25cbdcbe327c27b2a323b2a3102bfd8c972f8dcbe3274bfc27b2a320bf0972ff09db5d2311cbdc26f73b2a325cbe311cbe3109e361dc72327b2b48c8eca2fce36d748c9e78df6d7488ada31e35543d702fb0e130e130e6f0000,0x2be313c278d63f09d94e37db573b2b8db550a1eff0972f72f8c9bfc24288a8c872f70972327b282be22b7db58c78c4f38df6d74be3f09db572f8fc276d542a3137db58c42f8f0972f72f8c973b2b8da327b2a32231fb28bf098c75543d702fb0e1d14130e790000,0x88c45542dc02fb0e1d0e130e030002,0xb5534dc02fb0e1d0e130e010004,0xa5534dc00fb0e1d0e130e010006,0x2635534dd00fb061d0e130e020008]) (.p [0xf38db4f3bdf6d748cbdbbe37db5d2ff09f098c78c88c4ef7db5d2310bd7b2bcdb58fc1f6f07f3c27c1e322313cf07db4f3c276f078c810be4a8c95534dd00fb061d0e1d144e0000,0x1e35534fb00fb061d0e1d0e020002,0x6ab8daae3f08e36ae3236d5aada234afc22311aae3f08d742da6ab2eb6a323ae36d2b84a8c98c748af3c1e322311ae36d74ae36ab8fc236ae3236d2348ad3cdbc1e32042fa2a35534fb000d06fb1e130e5e0000,0xab8fadf5d3c26313adf6d0b8c8db48fcd2313adf6d748c42f8db5f36d748d62b7db4538df6d74be3f09d82bdebe32757bb2a327b2a31e3223102be25b8df6d3c223277db5d0bf3c1fcf078c88c4eb7dbc1fcf078c82e32631e32358c4f38db5d23e8adb5d2310bd56856aa1276d16e89888116aa25ba26223510b88a5534fb00fb0efb1e130ea60000,0x95534fb00fb06fb1e130e010002,0x4b8df6d74ae3f36d7c1e313adf6d748c42f8db4e8a8c8db55534fb00fb06fb1e1d14200000,0x75534fb00fb06fb1e1d0e010002,0x2045632fb00fb06fb0e1d0e020006,0x3cf38df6d63107e37db5d239357cf00150a1d0e130e0f0000,0x1cbdc25c8c9ef8db5d222821f5d2372f8c4737db5d2f8c42f8d6f72ff098c972f72f13c278d6326321cbfce36d74be3276d4710beb8d74bed88af38d748c90a22b7d237457cb00fb16130e130e590000,0x1ce36d74be3f09e36d5cbe311c278d6ff098c772f8c4709e2ff0972f11cecae36d6f8c4278da31e3223738db5d2f8fc275d042c2bedb222bc27b087e3588a72f70972327be36d7488ad748dcbdc26f73b2a325cbdc26f72327b2a321cbc472f8c4278df6d4710beb8d74be22bce36d748c90a22b78c77457cb00fb161d14130e9d0000,0x2047557cb00fb161d0e130e020002,0x72f72f8c9bc3f38d88da31021f8db58c9ef8db5d22282bed88adb5d2372f8c4709e2ff6313c2e325cbdc26f73b2b8d6327be37db5d2f88a8c850a0fce37db51fce37db48c8f38df6d63278d6325cbc472f13c278db5d2f8c4278db51c42f60a22b5d239376cb00fb161d0e130e840000,0x2e39357cf00fb161d0e130e020002,0x278da39a57d000fb061d0e130e040006,0xf80f8dc7e03e348c8e03e37d232388c3e37d748c9e36d748fdf4b0fce378c78c90fce2327ce368c8eb8db5d0ada31c3f38df58c9f38df6d631f6d2322310be239a57d0000d061d0e1d14560000]))) (.b 240 (.b 224 (.p [0x3cef7db5d2310bdb4f3672f8c472f8c42f8db4be3f09dbb2a31e322313cdf6d748c42f50f40e22222bdf6322313cdb4f08ed728a10b8c972f8dc735d042ef8c9d2ff0972f72f8c9bfce348c9f38df6d7488a8c88c40b8df6d74be3f09d9cbdcbe3274bfc2632042f9e34b622bcdf6d6313d2e32631e37857cc00fb0e130e1d149d0000,0x3cf37db5d2310be36d748d7efb2f8db55ca1cadbce36d74be313cef7db5d2310b8c4278db5ef8d620e21f40e22222bcf08e8a8c4f36d3c23a2a310b8c98c77857cc00fb0e1d141d14530000,0x88c47b57d000fb0e1d0e1d14030002,0x72f72f703bc3e09e35be22b8d2f8c9e35be3243f38db58c71021f8db5d2327be36d7488a8c288ae36d639a7cbc00fb0e130e1714380000,0x3e360f8df6d23238db5d230c31c3d232430f8df6d748c9e37db48c88cbe239a7cbc001d0e130e1d18290000,0xf8d748c38c9e36d630e22b672f8dcbe30f8be3278d6f8c9e36d2f0f80e32031e3f35d042ef0e3263243e222a31dcbe372f8c3e03e07e2f8c9e35be3278bc30c80f88c88c972f72f72f0f88c9e2326f8c9f36d748c4f042f88c9ef8db5d222a31c3e35d222a32238c7cbc00fb1e130e1d188a0000,0x738db4bc3e36d232768dcbe32c222372f8cb0878dcbe32dcbe30f8d74be32788c90888dcbdc72f88abe32632d4e22283e230f8db48c8e36d6325cbe372f8c9e36d631d4e36d7488ada39a8db300fb1e100e1d18620000,0xd74bdcbe326f72f8c9bdce36d748c9538db5d2f88a8dcbe32e372f8cb8dcbe32f58dcbe32c21e372f8cbbdc503e2f27888ae02238be3087e2326372f72f72f0e326326f8c9be32c3e36d748c30f8df6d2f203e37db5bc7bc3e35d232632f88c9538db5d222a39a8db300fb1e13111a18880000,0x1cbf7db40f6d088c98dcbe32e372f8cb8dcbe32e372f8cb8dcbe32e372f8cb8dcbe32e372f8cbe35d2f0f8d74bc38c9d03e34bc38c98c88c98c3e36d74be32f8be30f80f88c70f88c80e32632769a8db300fb1e13111d1b670000,0x79a8db300fb1e13111d18010002,0x2239a8dbc00fb1e130e1d18020004,0xb9a7cbc00fb1e130e1d18010006,0x99a7cbc00fb0e130e1d18010008,0x1e39a7cbf00fb0e130e1d1402000a,0xf8db5d230c3df48c90f8df6d2320be36d748c30f71c38c90c3e37db51f48c90c3e37d748c9e37db48c88cbe239a7cbe001d0e1d1417143c0000,0x72f8dcbe30f8db50e31f8be3278d6f8c9e36d74bc3e37d83e37db5d2f0e3263203d831c30f8df61e3223f042c3e3588a8c78c972f72f71cbc3e350f81c92af8c9be326f0f80ef8c8bc38c90fce08bfce358c9e231e3243e35d222a32238c7cbe00fb1e1d1417147c0000]) (.p [0x1c538db588ada372f8cbd821c222372f8cbd6372f8cb72f8c3e35be3278d6326372f72f72f0e326326f8c98cb72f8dcbe3278db58c7538d22283e36d630ef0f88c90f8df6d088cbe36d23254e36d7488ada39a8db400fb1e171417146d0000,0x3d83da31c30f8df6d47da32230f8db5d2f8c38c9d830e31c88cb0c3e37db51c3e358c9e358c288ae361e39a8db4003b1e1d181714390000,0xf8db572f0f8db5bc3e36d63276d632768dcbe32f68dcbe32e372f8cb8dcbe32e372f8cbbe372f8cbe35bc3e35bc38c972f8c3e2f8c9e232232631f6be30f8db5d2f8cbdb5736d6f0f8db5bc3e36d632758c9da372f8cbdaf8dcbe32f6d6372f8cb8dcbe32c21f58dcbe32f58dcbe32ef0f80f8238bc3e358c9e03e37db5bc7e2350ae358c98dcbdcbdc0f50f8d621e22a326f8c9be32d4e35be22879a8db400fb3c1d181714d00000,0x99a8db400fb1e1d181714010002,0x2239a8dbe00fb1e1d141714020004,0xb9a7cbe00fb1e1d141714010006,0x2639a7cbf00fb0e1d141714020008,0x3d630e32760f60f68c80f61e31c30f88c70f48c80f8d232632230f6d43d830e32632070f60c80c38c81e32232e39a7cbf001d0e1d141d183d0000,0x3e35d230f88c9e36d43db4db5d2f0f8db50f6d47be326372f8cb8dcbe32e372f8cb8dcbe32f8d2f0f8d2f0e325cbe30f8be32781e3243d2f88a2230f8db5d2f8cbd43d740f50c78c98c3db5d232f60f60e32038c90f8db58c78c3db40c32080e22a32e32232478c3e37db5d2f8c3e37d038c88c9db5d232f59a7cbf00fb1e1d141d18a10000,0x99a7cbf00fb0e1d141d18010002,0x79a7cbf00fb0e1d141d14010004,0x2239a7cd000fb0e1d0e1d1402000e,0xb9a57d000fb0e1d0e1d1401001a,0x99a57d000fb061d0e1d1401001e,0x1e39a57f400fb061d0e1d0e020020,0x1aae3688db4afa8c88c46ab8fc236d7410b6ab688ada8c8eb8db5d2b84a8c46b8d746ab8c9adaadae8a8c8ae32042e325aadaac4f04238db5ae32021f6d6311aada22be846abf0810b087ae321aadaae32358c910bda31d22badb58c4f0bf38df6d47db48c8eb8df6d7484a8c47b57ac000d06fb1e130e910000])) (.b 256 (.p [0x6b6d6b8da2f8db58da2f8ac21f8d636ab8cbe1ae35d2b8c9e021f8db48daae32f8adae368c8e234b8db4ae12b84b8db484a683e21eb8d74ae127884aafce36d632388c21f8db5d232354b8df6d7484adb5d239a7cac000d06fb1e130e6e0000,0x2e39a57f3000d06fb1e130e020002,0x5b6d6278570100fb0e3b1e100e040000,0x3cf38df6d631f6d748c4f1ee8ae37db51fc087da32042e37857d0021d0e3b1e100e1f0000,0x738df6d6f8c479e5ad88a88a8c4278d7479eeca2a32745a229cbdebe327c25cbdebe325eecae36d6324288ada31e32046857d002fb1e3b1e100e400000,0xef8df6d5ebe379e5b513a2e22a22a327672f8c4709e35bde8c9ef8d6f88a8c88de8debe22b6d442c75afb6229e79eeca58a28a58af088de7bb28a58a10b8c972f7af8c97b7db58c4f042f8db58c9d8288ad8772f79edb58c478be34be322378bbe32542bc7b8df6d441f88c972f8c472f8c4278df6d478c88c47869d002fb1e3b1e100ea20000,0xb7857d002fb1e3b1e100e010002,0x97857d002fb0e3b1e100e010004,0x2a37857d100fb0e3b1e100e020006,0xaf8c4f38d6f8c4278db5d2f8d6e37db5f3bdf6d442e31f6d3c2232768c4ef7db5d2310be36d5688af34f09f3c26322313cdb4f34f098c810b5bae8beb8df6d611e124a8c97857d100fb0e3b1e13115c0000,0x1e37857f200fb0e3b1e130e020002,0x4b8df6d637ab8c4796aa12a3108e36d56aa12a31f6d02e37db58c479e596e8984928a8c41f8db57962b672f8de278d6f796e3588a8c98c88de7962a22b6d442de796db5e8b28a8c91d688a8c88c479e5ba24a2b8db5d2358adb5d042d6a9622229aade689ae322be9eac47b8df6d6b8c4238df6d631e322311aae36ab8c8db4afae878c810b5aa84a8c97857f200fb0efb3c100eb80000,0xf38df6d74ae313c238db5d235aa84adb57857f200fb0efb3c1311160000,0x77857f200fb0efb3c130e010002,0x88c47b57f300fb0efb1e130e030004,0x1cbdebe326f7af8c47b8df6d63109e36d6325ce37db51f6d6372f8c472f8c42f8db5bdebde796ef8884238ef8d6222228a8c98c972f72f8c9bde8c9ef8df6d6228779e5b6d44ecbe36d442b8db52821f68c972f709bde8c9538df6d6f88a087da32368c42d6e36d6229688a8c21f8db59a7cc400fb0e3b1e100e950000]) (.b 272 (.p [0x3e03e358c9e03e358c90f8db51d6e36d4ae35087e36d630f40e32430f8da31e322313c10bf37db58c4f042f8d4758a0c3e23203e36d47eb8df6d7484a6b8df6d478c90fce378c8f38df58c9087df68c88cbe239a7cc4001d0e3b1e13116f0000,0x1ce35d2f8dee348dcbe30f8d43e07e2f8c9e2f8c8e2f8c9e3571cbcbbdee358c9d6372f8dc7b588a8c9d6310b7b8d6f88a1d4294283e36d430f82231c3f38df6d631e32430f8da323ce37db51e3216d622a3f16d622842fce37db51e32638c7cc000fb1e281e13117d0000,0x1cbe30af8debe3783e03e2f88888ae23278d6f8c7e35be3278d748c3e37db50f8db58c458ae360f8df60e32038c98c81e3f36d748c42f8d5e7960c42380c4eb8d8423824a296283f38de3204f38df58c4278da3223f042c78c9d9688a8c7cc000fb1e3b2913117b0000,0x2238c7cc400fb1e3b1e1311020002,0xf60f6bc8daf8dcbe32f672f8dcbe3276bc2236be372f8cbd888dcdb5be32e3736d6f8cb8dce36d6f8cbe1cbe372f8c9e36d47bdee36d6f8debcbe36d63783d622af8cbe2f8c21f88c972f8dcbe3278da3223738da372f8c8e34bdee36d5e78be07be325cbdc738d9c20b0f8d6229ce37db51ef8c98c850a8cb72f8c472f8c4278df6d470f8d748c30f8df6d631c3e36d2320be230f8d748c9e36d748c95b8db5d222a39a8db500fb1e281e1311da0000,0xf8db50f80f88c9e03e368c8e2358ae231c30f88c80f8df6d478c90c3e23203e37db51c3e35d232768c88c3e36d43e358c38c9e350c3e232232470f8db50f80f88c90f88c81c30f8df6d478c98c858a8cb7830f8d88e36d4ae36d6358ae37db51e39a8db5003b1e3b291311820000,0x1cbe370be36738da322370be1ce368c8bdee358c9d6372f8cbd6372f8cb7b8d63254e3588a783e36d622b8db58c9d54e36d622b6d637af8debde783e2d0f827888ae0a8c98c9d9cbdc26f7a327be36d622a3216b622a32d4e3588a9a8db500fb3c3b291111790000,0xf60f6236d637af8cbda37af8cb8debe32f68debe32f68debe32f68debe32e37af8cb8debe32ef8debe32f5bc3e35bc38c97af8c3e35be32788c88c98debe30f8be3276d6f8cbdb472f0f67b8d88d63276be378bdaf8de2f6be372f8cbda372f8cbbe372f8cbd9cbe370be36d6370bbdcbe32758dc2ef738d6f8c9d6372f8cbbdee36d6f8c9da3223736d6f8cbd2f0f60f60f622f8c88c3e36d6f8cbdb57af8de0f8d6f88ae35be32781e32632237af8de0f8d6f88ae35d2f8c9db58cb9a8db500fb3c3b291312fc0000,0x79a8db500fb3c3b291311010002,0x99a8db500fb1e3b291311010004,0x2239a8dc400fb1e3b1e1311020006,0xb9a7cc400fb1e3b1e1311010008,0x99a7cc400fb0e3b1e131101000c,0x1e39a7cea00fb0e3b1e130e02000e,0x1aadee36d74ae3236d748daade6ab8c9689087ae322b7abf38da3236d748c479ee8ad6129a7bde35844278db584a0ab84ad6325ee37db58c710bdb48c8eb8db5d2a84a2e30aa84ae239a7ce9001d0efb3c100e610000,0x7962b6d1e7962b58842b8db572f789bde256e36d622a31e32237af8de7962a22a3276d748c42de7967962b8eb88495bae35109e362021f5e8b84928a8c972f789bde25e256e36d622b8db58c75a22962a38c7ce800fb1e643c100e6c0000]) (.p [0x79e58a84ae35d1aadeae32232637ab8c47ab8cbdb5d2310be368d6aa12b679eaa12b68d6aa12b679e88a58a8c88de58adb58c42d629aadaae322b7a3216e36aa1282aea84ae232475aa88a8c7ce800fb1efb65100e640000,0x2238c7ce900fb1efb3c100e020002,0x29a8db800fb1f643c0e0e010000,0x16e36d629a8d0100fb1f643c100f050000,0x79e796e36d4ae36d4ae36d4a58ae23087e36d639a8db8023d1f643c100f1a0000,0x1ee36d5cbde25e2761d688a72f8de278d6f79e58ae222a325cbe311cbe3108e36d478c85a22a3948db802fb3e643c100f330000,0x7af7af783db52b6d63276d637af8cbda37af8cb8debe32f68debe32f6d637af8cbd6f8c9da37af8cbda37af8cbda37af8cb8debe32e37af8cbd9cbe372f8c9d9ce3622370be23738da3235bdebe32758dcbe32ef7af8c98dcbe32ef7b8d63254e36d622a32237af8debe32f6d6f8cb79e58a2f88d62b88c972f8c472f8c4278df6d4772f8debe3278db48c8d639a95b802fb3e643c100fbc0000,0xb9a8db802fb3e643c100f010002,0x99a8db802fb1f643c100f010004,0xa9a8db800fb1f643c100f010006,0x7da39a8de200fb1e643c100e030008,0x796e3588a789d56e36d622962a358ae36d639a8de200fb1efb650e0e180000,0x12e34aa19a8d01003b1efb65100f050000,0x1aadaae322b7ab7ab8c38c8e358deae3278d9ee37db58c78c87ab8c98c85abaa12a3948da3023b1efb65100f2d0000,0x6b6ae37b6d63df6d6b8c9db5adedab8c8db58c8db58de2e378b8de2f58de2f58de2f58de2e378b8de2e378b8daae32eb8daae32f56b8dab6ab8c8adaae3235ae368bdab6ab8c88da2f8adaae321ae358c9da36ab8cbadee36d6b8c8d6b8c98dadb5ae32f66ab8daae3238db51eb0f6d6b8deae32f6d637ab8cbdb5ae37ab8cbdb58deae32f6d63796aa12ab8cb087da32239a95a3023b1efb65100fc20000,0xb9a8da3023b1efb65100f010002])))))) (.b 432 (.b 352 (.b 320 (.b 304 (.p [0x2a39a8de2003b1efb65100f020004,0x5b8df6d5e58adb58d62b558a1e3948de200fb3cfb65100f120000,0x169a950100fb3c8265100f010000,0x1e5a22a358ae369a95b202fb3c82650f0f090000,0x7b8db58d62b6d639895b2026a3c806510100a0000,0x3e358c3e23278d43e350f88c9e1e58ae232232637962b8db58cbe350f8d630f88c9e350f50f58c98c98de58ae36d632f87962b88c88c98de58adb58cbd5e78be2358ae232639a995f026a3c6f6510105d0000,0x3e358c3e23278d43d43d632632630f8db58cbe3579e0f6d6b0f623684a48b48b48b48b48b2a37ab8cb8deae32f58deae32f58deae32f58deae32f58deae32f58deae32f58deae32e32637ab8deae32f6d632f69a995f026a3c807010106f0000,0x2239a99b2026a3c80651010020002,0xbdb59a95b202fb3c82651010030004,0x79a95b202fb3c8265100f010006,0x2a39a95da00fb3c8265100f020008,0x16aa29a950100fb3cfb830f0f030000,0x1a68b8da2f8dab6888da2f8dab6a322b8da2f8d636b8ae3276adaae322368bdab6ab8c88de2f86b8ae326b7ab8c88de2dee35ae326b7a3236d6378b5b884a4b8da12a39a95da02643cfb830f0f590000,0x1eae379e2f68de2f68de2f68de2f68de2f68c8d9c70bbe370be36be3738daf8c8d6f8debe3275bdebe326f8debe32f579e2f6d6378bdb58de2f6d6378bdb58de2f58c9da32237b6d632e37b6d632e379edb58cbdb58cbe2358ae359a95da02fb65fb830f0f790000,0x99a95da02fb3cfb830f0f010002,0x2b49a95da00fb3cfb83100f020004]) (.p [0x2239a95e200fb3cfb65100f020006,0xb9a8de200fb3cfb65100f010010,0x99a8de200fb1efb65100f010012,0x79a8de200fb1efb65100e010018,0x2239a8de900fb1efb3c100e02001a,0xb9a7ce900fb1efb3c100e010024,0x2639a7cea00fb0efb3c100e020028,0x6ab8c46ab8c42f8db5d2b0f8dab0f80eb8c98c8db4ac3e37d630e32760c3e2323ce37d632478c88fcd6310bd1adbae35d03e36d7ae211eb849ae12ab0f8d431c30f8df6d47ae3263223e842daeb8db5ae12b6d6313a10beb8db584ae07ae3263216aa12a38c7ca8001d0efb3c1311860000,0x3e36d43e350f88c9ac3e368c8d637ab8c38c8d6b8cb8c70f8da30f88c8e350f8ae37b8db5ae3238d47ae3243e360e3203e358c90f8df6d478c88c3e350f8d6b0e322b8c9ae30f8db5ae32f6d2b0f8df6d43e03e232231c3e350f8d478c98c85aa84a8cb7ab8c3e36d6b8c8e36d631c3e36d630f8d6b0f88c80f8d6b8c9acbe021f8db58da0f8843e2b849d83e3684784aac30f8d6325ae37db51f68c82c3e36d74ae12b8ae3087e232639a8da2001d0e643c1311e30000,0x6ab8daae32f5d1aae30f6d6b8c8db5087ac98daae32e36ab8cb8daae32e36ab8cb8daae32eb0f5ac3d6b2758daae32f58daae32f58daae32f68daae32f51f68daae32e36ab8cbae32236ab8daae3235ae32daae36ab8c8e351e39a8da201130efb651311780000,0xf8db56ab8dadab0f58de2f68c8d636ab8cbd6378bdab8c8d6b8daae32f6d631e36ab8cb8daae32e36ab8cb8daae32e36ab8cbac3e36ae30e32350f6ac3dab8c8d636ab8cbd6b8daae32f58c98dae36d6b8cbd9ee36d6b8deae32f8d87ae32237ab8daae3276d74ae32f49a8da2011d14fb6513118e0000,0x26b9a8da2001d0efb651311020002,0x2239a8da8001d0efb3c1311020004,0x2e39a7cea001d0efb3c1311020006,0xf8db58c40f68c4238db58d62b8db5d2358adb5d238c7caa00901e833c13111c0000,0xf8db50f8da30f80f88c98c8d43e350e3243e230f8da32388c88c98c3e368c38c8e36d6358adb58cb8c779e2d62b8db58de79e79e58ad4adb52842cb58a2f8db58de79628ad6358ad43e038c80f88c90c3e37da32388c88c98cbe2358ae231e39a8d5800391e553c1311800000])) (.b 336 (.p [0x3e36d630f6ae30f6d63236ac3db5ac3da32368c88deae32e37ab8cb8deae32e37ab8cbd637ab8cbdb58deae32e37ab8cb8deae32f58deae32f58deae32f58deae32e37ab8cb8deae32e37ab8cbae37ab8cbe36ac3e36ae30f8ae32360f8d838c8d43e2b8c3e2b8c8e232632230f8db58d22b6d632f579eaea843e36ac8e212b8ae348ae23263223783e36ae12b8db5ae30ab8cbdb58cb8c7db49a8d5800391e83561311cd0000,0x2239a8d8400391e833c1311020002,0x3e358c38c9e36d6358adb558a8d6df6d632f6d63948d8100903a543c11111b0000,0xf8d43e360f88c88c98c3e36d632f8d43e350f80f88c88c98c3e36d632f87962b88c88c98de58ae36d632f88d62b679e796e222b888ae0a5b888ae2358ae232239a957f005c3a543c1111560000,0x1cdb5bc3db58c3daf8c8db58c98de2e378b8de2e378b8de2e378b8de2e378b8debe32e37af8cb8debe32e37af8cb8debe32e37af8cb8debe32e37af8cb8debe32e37af8cb8debe32e37af8cb8debe32e37af8cbda37af8cbda37af8cb8debe32e37af8cb8debe32e37af8cb8debe32ef8debe32f8d6f9a957f00905d543c11119d0000,0x2639a958100903a543c1111020002,0x2e39a8d8400903a543c1111020004,0x3e36d639a8d8400903a543c1212050000,0x7d749a8d8400903a833c1311030002,0x2639a8daa00901e833c1311020008,0xbd639a7cea00901efb3c131103000c,0x2769a7cea00fb0efb3c131102000e,0x79a7cea00fb0efb3c130e010016,0x2239a7cf300fb0efb1e130e020040,0xb9a57f300fb0efb1e130e010050,0x2639a57f400fb06fb1e130e02005e]) (.p [0x6b8db5d2b8c4f08e36d7ce35d1ae35adaafc22b8c88c91e311aae3f08db5d2310bda348adb448ad3ce36d748fae36d745cad4ad74f3c2c30e11fae3484984a8c9eba2fcf0be78df6d7484a8c98c78c88c47b57ad000d06fb1e1d146c0000,0x3e36d230e3236d43e340e32030f88c88c98c70c38c90c3e37d748c98c78c88c3e37db58c3e37d438c98c7db40f8df5d038c9d830e32478c88cb0c3e348c80f8df5d23243e36d23235d230f60e3203ac38c80f8df5d232631c3d212830f8df6d631e32232e3243e36d748c30f4ae3243e37db48c82f8db5d230eb0e3203ac3e378c88c70c3e37db51e3203df6d748c4f042f8df5d232632f8da31e39a7ca5000d063b1e1d14cf0000,0x6a34b8d6b2b5ac21f58daae32c22758daae32c21f6d236ab8cb6ab8daae32f8db5d23212e36d7484ad636ab688adaac30f8db5ac7e36d232232122a32d2e36d74ae12a39a7ca4000806fb3c17145a0000,0x6b8db5d2b0f8db5d2b8c3e2b8c8e36d43e36d74ae30c3ae32632358c40f6d748c42f8d5a6ab8c42f8ac3e2322b8c9ac7ae32238c7ca4000d09fb3c1714440000,0xf50f6ac38c81e30f8db5ae32f50c3e23203e23212e3584a8c90c3e36d470f8db48c8d636ab0c3e2b8c98c8ac30f8d74ac98c8ae32daae36ab8c42f8d63252e36d612a31e39a8da1000d09643c17145c0000,0x6b8df5d1aadadf5d2b8c8d632636ab8cb8daae32e36ab8cb8daae32e36ab8cb8daae32e36ab8cb8daae32eb8daae32f8db56b7d74d748494b8df5d212612a36ab8cb8daae32e36ab8cb8daae32e36ab8cb8daae32e36ab8cb8daae32e36ab8cb8daae32eb8daae32f56b8dab6ab8c8ada8c86b8df6d478daae32e36ab8cb6b88c84b884a4b8ae12a32631eb9a8da1000d09fb651714ba0000,0x2239a8da4000d09fb3c1714020002,0xb9a7ca4000d09fb3c1714010004,0x2639a7ca5000d06fb3c1714020006,0x692e35d2b4b8d74235d212a36ab8cbd636ab8cb8daae32e36ab8cb8daae32e36ab8cb8daae32eb8daae32f8db56ab8dae35d2b8c8d746ab8daae3235d232636ab8cb8daae32e36ab8cb8daae32eb0f8d2b0e32021f68daae32eb8c88daada22b8cb1eb0f8d740f8d74ae36ab8cbe09ac30f8df5d098c88c3e36d2b0f8d740c98c8ae32da0f8db5d212b8ae348ae231e32236b8db5d2b6b8d2b8c3d2b0e3223234ae32232e39a7ca5000706fb3c1d18dc0000,0xf8d74df5d03e35d2b0f8df5d2b8c8d498daae32e36ab8cb8daae32e36ab8cb8daae32e36ab8cb8daae32e36ab8cbe34ac3d03e350f81c98c88c98c3e36d74ae32f5d239a7ca5000b08fb3c1d185a0000,0x2769a7ca5000d06fb3c1d18020002,0x79a7ca5000d06fb3c1d14010004,0x2239a7cad000d06fb1e1d1402000c,0x2e39a57f4000d06fb1e1d1402000e,0xf38db48fc2368c4f37db5d2310be36d748fae8b2b6d748c47b57f400fb0e6e1e1c14200000]))) (.b 384 (.b 368 (.p [0x3e36d230e3236d03e36d230e32340f40e32632632230f8df5d230e3276d748cbdb50f8d748c3e23278db50c38c80f58c98c3d038c90c38c98c88cb1c30e3203e230f8df68c8e078c90c38c80f88c3e37da32388c70f88c21f8d232632230f8df6d630f8df60e32231f40f8df6d038c80c38c81e3243e37db40e32030e32231c30f81e32632232e31e39a7cc3001d0e331e1c14b70000,0xf8df6d230f8df6d74bc3d038c98c98c8db5d238c7cc300fb1e331e17141a0000,0x3e35be30f88c9e35bc38c9be30f8db5be32f6d03e36d6f8c3e36d6f8c9db6d6f72f8c9d88daf8dcbe32f68dcbe32f68dcbe32e372f8cb8dcbe32f8d2f0f8d630e3276d43e2f8c2238db51e30f8db572f0f5be3247be32e3243be22a32230af8c3e35d2f8c9db58cbd740f8db40f8db50f8d832231e32340f5d03e340e32232630f6d748cbdb50f8db50f81c30f8df6d478c80f80f8df6d232358c98c3d03e36d431ef8c80c38c88c98cb1e32232639a8dc300fb1e331e1714e90000,0x2f49a7cc300fb1e331e1c14020002,0x2639a7cc700fb0e331e1c14020004,0xf8d740f8db50f8dab8c3e23238ac3e232078c9ae30f8db5d2b8cbdb40f6d03d038c98c88c3db5d232f5d03e36d230f88c8e36d43d83e361c30f8df5d232768c88c3db50f60f68c81c3aa12a32c78c98c88d2e37db5d2b8c3e37d740f8ae3263236d748cbdb49a7cc700fb0e6e341c14880000,0x2239a7cf400fb0e6e1e1c14020002,0xbd749a57f400fb0efb1e1d14030008,0x99a57f400fb06fb1e1d1401000a,0x79a57f400fb06fb1e1d0e01001a,0x2239a57fb00fb06fb0e1d0e02007c,0xb9a32fb00fb06fb0e1d0e0100a4,0x99a32fb00fb02fb0e1d0e0100b6,0x89a32fb00fb02fb061d0e0100ba,0x65980ad11e36d749e02b6d636676678c78c42d9e78d602b9e36d748c7e36d748c7d39e36d7480ad230a79602b8db5d236678c46678cbd749d9e4a8c78c4f35d042d99d91d98c7e78db5d202a31199d91e76792a31e310b8c96676678c7db5d231199d91e7667f079e31c42f68c8e789e69602b9db58c7e78df6d7480a8c42e39a32f60005020d06fb1eaa0000,0xe635534dd000d0608063b1e020000]) (.p [0xe6255340100fb0e08063b1e020000,0x3ce36d748fb2b676f8c4f09e36d3b2bc26323be37db4ef8df6d2ff098c88c4ef7db5d2310be34ecaf0972f72f8c97748c9ecad23114e37db4be3f09d9cbdcbe327c27b2a31cbf09ecada32231c44134dd02fb0e08063b1e670000,0xaf8fc276d5cbddbe3275bfc2631e3114e37db5d2f8fc2742fc25cbdcbe326f778df6d23276d2311de37db4bddeca8c972f72f8c976327b2a31cbf38db48c9578df6d222b68c872f738df6d1cbe322f8c9bfc25cbdcbe327c276eca088da31fb2a313be37db40af8c4738d2f8c4278bfc248eca72f72f8c9bfc27b2a31cbf388c972f11cbe3109e37db48c88c78c45542dd02fb0e08063b1ebe0000,0xb5534dd02fb0e08063b1e010002,0xa5534dd00fb0e08063b1e010004,0x2635534de00fb0608063b1e020006,0x3ce77db5d232f6d7bdf6d3cdb4eca8c88c4ef7db5d232f5f3c2232631e313bdf6d748c42f4ecaf3c23cf088c78c4f36d7cf088c710be4a8c95534de00fb060d093b1e4b0000,0x2235534f500fb060d063b1e020002,0x29e3e78db5e78d6680a8c7db40a78dd7592678c9da78c7db5d278c4477db5d278cbdb58f9e37db48f9e77db42e323676375528ad82bddbe325d755db428a8c98c78c475d54a2b7db48c42f8d1588ae632632231f48c4578df5d23e63276d748c42f4578db5d265559a02621e22999d99e31e7e631e31199e36678c7db59f98c710b44a8c98c85534f500fb060d06fb3cb30000,0x78c45632f600fb060d06fb1e030002,0x578db5d228b570100fb0c08063b1f060000,0x72f72f77c1f88c9088e2f8c9f38db58c972f11cbe3109e36d631c40a210ae36d638b57cd02fb0c0806291f2c0000,0x1cbdc26f76325de37db488ad748dcbe311c278d2f76f11deca8c427876f8c78c972f11cbe3107e37db48c872f76f8c9e36d631e310b50af38db5d23276d6376f11dbc42f8df6d1cbdc26f76f8c921ce34708bddbe32631d42bc778df6d23223263537db4734be376f8c9d14288f3c1e32442dcbc472f8c41f8df6d08f1de37db4108e36d748c98cb8b57cd02fb0c08063b2ab50000,0x1e38b57d002fb0c08063b1f020002,0xae36d239a57d200fb0608063b1e050004,0xf80f88c7e03e37d08e03e37d631f80f8df5d23278db5d23f3c2f9e032431c3d08283f388c8f388c7e78db5d202a3243f388c7f38df48c9e78db42b68c80fce3423ce35d23279e36d742b6d631e310be239a57d2000d060d093b1e6c0000])) (.b 400 (.p [0x3cef7db5d2310bdb572f8dcbe3276d74be311ce37db5d2f8c42f8db5bfc2631e3102bfc277db5d042f40ec0c988a72f72f72ff38d3ce2322326326f8c9bfc25cbdcbe327ce36d748c9ef8db5d2228288ada31e313be37db4ee313cdb48c42f6eca21cbdcbe326ff09eca8c710be78df5d2c88a8c8f7d1e313cf07e4a10bf38de32232637857ce00fb0e0d09281eaf0000,0xf36d5c74adb4be30af8c42f8db5d2ff098c78c4f77db5d232f8d7455588788ad79df6d7b8c78c4e77db410bf3c2d5579e3427424a8c88c97857ce00fb0e0d093b294a0000,0x78c47b57d200fb0e0d093b1e030002,0x30f88c7e03e37d632788c3e37db58c7e35d239a7cbc001d0e0d09281e190000,0x1cbdcbe3276d748dcbdcbe325cecadb5d232768c42fbe36d7488a0a22a350ae36d239a7cbc00fb1e0a09281e2d0000,0x1cbe372f8dcbc38c9e2f8c9e34be3278d6f0f8db50f8d838c81c388a0c3e378c722325cbdcbdcbc3f38d2f22326326f8c9bc3f38df68c80f8df6d631e3f042fce37db48c88c90f8df5d222a31e38c7cbc00fb1e0d0b281e670000,0x71cbe3278bdc8c9e14e36d2f88ae2f088e36d2372f709723243e36d7488a8cbe23538db5d222b8538df6d7488a088da39a8db300fb1e0d0b221e400000,0x3e36d2372f0f8db4bc3e36d23276d232768dcbe32f6be372f8cbda372f8cbda372f8cb8dcbe32e372f8cb8dcbe32f8bc3e2f8c3e2f8c9e232632360f6d2f8c3be3276d1ce37db48c88dcbe32e372f8cb8dcbe32ef0f48dcbe32ef0f8d232630f6d2f8cb0f8df6d088c91e372f8dcbc3e36d03223274be3276d2f8cb72f8dcbc3e34be3278d2f8c9e23203d6f88a0c3e37db4203e36d478c3e360c80c3e368c81c3d222a32c3e37db48c88c99a8db300fb1e0d0b2823e50000,0x1e39a8dbc00fb1e0d0b281e020002,0xb9a7cbc00fb1e0d0b281e010004,0x89a7cbc00fb1e0d09281e010006,0x2639a7cc100fb0e0d09281e020008,0x3e36d438c7d030f88c72030e31c3e37db48c88c90c3e231c3e37db48c80f8d748c98c78c3e36d7454ad740f50e31e3243d838c70e32030e31e32631e32c30f8da31c3e368c7e03e36d08e23578db42b8d232239a7cc1001d0e0d093b296f0000,0x738db4be376f8c9e35d03e348c38c9db40f80f8be31ef0f48c90f8d232488fc10b8c972f75cbc3e1de342388c9be31ef8c9bc30f68c7f38df68c70888fc10b8c98c75622a38c7cc000fb1e0a093b295c0000,0x736d2f0f8db4be30f48c9db48c9da372f8cbdaf8dcbe32f68dcbe32e372f8cb8dcbe32e372f8cbd2f0f60f68c7da376f8cb8ddbe32f48ddbe32f48ddbe32f48c9daf8dddb4be32f6d1cbe376f8c9e36d088dcbdcbe31f5d2f76f8c9be32c30f88c70f8d23276d230f8d230e32760c3e232768c754a8cb0f8df6d088c972f72f088e34be326f778db48dd0f688a0f8da31f610be36d748c90f8df6d7488a8d42b8da31e39a8dc000fb1e0a093b29da0000,0x2e39a7cc100fb1e0a093b29020002]) (.b 416 (.p [0xf6d43e36d03d83d872231e30f6d748cbdb50f8db48c3d83d83d87d878c3e36d2f8cbd9cbe30f8db4be3276bdce37daf1f68dcbe32f6d2372f8cbda372f8cb8dcbe32dcbe30f8d2f8c9e23254e3688a8c78dcbe370388ae34be3276d232d4e34be22a32350f8db50f8db40c80e32631c3e03e07e03e348c9e23578db488ae232232631e30f8df6d74be30f8df6d43e37db40c88c78c9db5d232f49a7cc100fb1e0d0b3b29ce0000,0x89a7cc100fb1e0d093b29010002,0x99a7cc100fb0e0d093b29010006,0x1e39a7cd200fb0e0d093b1e020008,0xb9a57d200fb0e0d093b1e010012,0x99a57d200fb060d093b1e010016,0x2239a57ed00fb060d063b1e020018,0x199d99e31199e310be36d749e31f6d748d99d99e31f9db58c710be78db5d202a30a79a580ae239a57ec000d060806fb3c330000,0x1d8dd75528a2b6d5cbe377b29dbe31e3276738d9c1ef76f8c98c78c472f8ddbe3276d232f575d75528a2a32631e311d8dd7552a22a22b6d748c42f856229588ae792d5578df6d7480980a8c972f72f8c9bdd8c9763255e3488a7792b8db48c95622b7da32237857eb00fb0e0806643c870000,0x199e37599dde78d599e32678c98c79e3109e368c4578db5d279a010ae369e31f6d2356680ad99e36d278d5e37db4804767804278ddd9e32631f675d8842b8d1588a75d578da010ae202a32552a31e311d75528ae36d2354adb48c42d59951e22999dde36d231f48c4678db49d977680a8c710b7679a02912912a32487857eb00fb0e0806fb65a50000,0x78c47b57ec00fb0e0806fb3c030002,0x29a7cc600fb0e0606643c010000,0x743e279a0e78d87e36d202b8db48f910b56680ae23778df6d23238d239a7cc6001d0e0807643c260000,0x1cbe3749d2f7498ddbe376f75d54a2a3263276d2310bd5d75d54a28a8c976311ddb48c42f8d9cbe311c278d2f76f8c98c78c476f8c476f8c42f6d2310be3472f709bdd8c9da31028842b8db421d75d576d15ec710b28a2822232631d588a5622a38c7cc600fb1e0807643c810000,0x72f76f8c9bdd8c9578df6d222a30ac88ae36d639a8db700fb1e0807493c1a0000,0x755e36d0ae36d2375528b54ae23088e239a8db7003b1e0807644a160000]) (.p [0x71cbe310bbe376f8c9e37db49a8db700fb3c0707644a100000,0x76f8dd54ad152a3276d23948db700fb3c0808644a0e0000,0x1cbdc703d821f6d222942d42d42d42ca8dd2e374bdb48c9da374bdaf8dd2f68dd2f68dd2f68dd2f68dd2f68dd2e374bd9c70be2f8dcbe3276738d878dc2f8738da31ef778d2f8c9d2372f8cbbdde36d232768c78dcbe372f8cbdb4be32dde23255e22294e36d222a39a95b000fb3c0808554a8b0000,0xf6d03d87db4776d2325ddb4be22a376f8cb76f2e376f8cb8ddbe32e376f8cb8ddbe32ddbcb8ddbe32e376f8cb8ddbe32e376f8cb8ddbe32e376f8cb8ddbe32e376f8cb8ddbe32f6d2376f8cbda376f8cb8ddbe32e376f8cbda376f8cb8ddbe32e376f8cb8ddbe32e376f8cb8ddbe32f4bc3e360f8d838c78c754a7552b88d52b88c78c98dd54adb48d52b6d232f69a95b000fb3c08086456be0000,0x1e39a95b700fb3c0808644a020002,0xb9a8db700fb3c0808644a010004,0x89a8db700fb3c0807644a010006,0x99a8db700fb1e0807644a010008,0x1e39a8dc600fb1e0807643c02000a,0xb9a7cc600fb1e0807643c01000c,0x99a7cc600fb0e0807643c01000e,0x2239a7ce100fb0e0806643c020010,0x7559a229d1d52999dd1f8d23276d237678c46678c4278d9d7768c42d52a31d99dd9e31f8d278c92d59a229d76229588adb454ae368c78d5e36d2688ae36d239a7ce100fb0e0606fb65540000,0x11e369e09a7c01001d0e0807fb65050000,0x19e35d199e3267778db475d9c42f82199d975de27809e20e789e027880a8c7778db48c89e32631d12a38c7c9e021d0e0807fb65370000,0x676d03db40f6d2727444bda02a36678cb8d99e32f48d99e32f48d99e32f48d99e32f48d99e32e36678cb8d99e32e36678cbd278d99e32f8db46678d99e31f8d23219e369d99e31e76678c7da76678c7d278d99e32f6d278d99e32f6d278d99e32f5d236678cb8c99c3da70f69e31f6d236678cbdb48dd9e32f6d237678cbd237677678c79e32d99e36678c9e348c9088da31e39a8d9e021d0e0807fb65c40000]))))) (.b 512 (.b 464 (.b 448 (.p [0xb9a7c9e021d0e0807fb65010002,0x2a39a7ce1001d0e0807fb65020004,0x478df6d2375de36d2655d75de4bdb410b10b2472b6d2354adb454a8c8d238c7ce100fb1e0807fb65280000,0xf6d230f48c9d03da70f69e31f48c98dd9e32e37678cb8dd9e32e37678cb8dd9e32e37678cb8dd9e32f48dd9e32e37678cbd237678cb8dd9e32e37678cb8dd9e32e37678cb9e37678cbd83e368c38c7d83e368c38c7d03e230f8da31f88c98c78d5e37d230e3276d232dd0f89e60f81f89d5e361f82b88d52b88c98c78dd54ae36d2354adb48cbd1d54ae36d2354ae36d232239a8dba003b1e08078265c40000,0x5629a8d0100fb3c08078265020000,0x75588ad152a3948db902fb3c07078265080000,0x76f8dd76f2f8db4be3278da39a95b102fb3c07077266100000,0x1d54ae239a95b102643c07078273050000,0x7552b6d239895b102fb6507078273060000,0x72f8dc2f8da37388c7d2f72f8c9be370bd2f76f8c98dd2f8778be31ef778d2f8c98ddbe32ef778db48c9538db488ada39a99ab02fb6507077a73400000,0x1dbddbddbc3d9de368c7d232748dd2f48c98dd2e374bd9de368c78c9be376f8cbd2f75d50bdb454adb450bdb42b6d2376f8cbda376f8cb8ddbe32f6d2376f8cbd2376f8cbd2376f8cbd2376f8cb8ddbe32f40c3e348c9db48dd54a8cbd232637552b68cb76f8ddbe31f8da31e32637552b6d232f69a99ab02fb650707827b9b0000,0x1e39a99b102fb6507078273020002,0xb9a95b102fb6507078273010004,0x99a95b102fb3c07078273010006,0x7d239a95b902fb3c07078265030008,0x2e39a8dba02fb3c0707826502000a]) (.p [0xf8db49a8dba02fb3c08088265040000,0x89a8dba02fb3c08078265010002,0xa9a8dba00fb3c0807826501000e,0x2639a8dd800fb1e08078265020010,0x159a09a8d01006a1e0707fb83030000,0x199e36676677768c7da31f69e31f49e36678cbdb49e36678cbdb49e36678cbdb49e36678cbdb48d99e32f68d99e32e36678cbe277788c74789e02a39a8d9b02321e0707fb834f0000,0x7678dd9e32f6d2396919b026a33070792830a0000,0x75d5559e6815db49c7db48092952d52f42b68dd9e32f48dd9e32e37678cb8dd9e32e37678cb8dd9e32e37678cb8dd9e32e37678cbe360f8d230e32760f60f80f88c9d878c78dd54ae36d232f8d83e348c38c9d03e340f88c9e1d54ae231e32637552b6d232dd54ae232631e37552b8db48cbe347552b88c98c78dd54ae36d232dd9e37678cbe232639a9771026a3307078983b60000,0x7677670f4767276d2374bd2374bda31e374bda374bda31e374b8dd9e32e37678cb9e37678cbe369a9771026a330707928a340000,0x1e39a979b026a3307079283020002,0xbe349a8d9b026a330707fb83030004,0x2639a8dd8026a1e0707fb83020006,0xadb59a8dd800fb1e0807fb83030008,0x1e39a8de100fb1e0807fb6502000a,0xb9a7ce100fb1e0807fb6501001c,0x99a7ce100fb0e0807fb6501001e])) (.b 480 (.p [0x89a7ce100fb0e0806fb65010024,0x1e39a7cec00fb0e0806fb3c020026,0xb9a57ec00fb0e0806fb3c010038,0x2639a57ed00fb060806fb3c02003c,0x199e36678c7db59fcf042f8d23e792e78c9db9e4b679e202b9e3680a9e32632231c3d6680a8c47b579f000d060d09fb3c330000,0x3d740e70e31e32630f6d749e32f60f89c3e231c3e348c92030e31c3e23243e36d232231e30f8db5d278c3e278c7e36d749e30f8d740e32760c3e348c92231f40e680a8cb0f89e30f89e31f80f88c70f8d23243e36d08478d202a3243e270f8da31e7088e36d230f8d190f8d202b82190f8db580a8c90c2238da31c3e36d7480a2f8d230a79a02b8da32239a7c9c000d060d09643cb90000,0x199e30f6d278c7d740f49c3d278c9d742636678cb8d99e32e36678cb8d99e32e36678cb9c3d03d232748d99e32f4088d236678cb8d99d91e78cb6678c2238d232631e3678d749e36678c9d278cb6678d99e31f88c94789e680a9a7c9c000d060a09fb65770000,0x3d74643d36d202202a36678cb8d99e32e36678cb8d99e32f48d99e32e36678cbd236678cbd236678cbd232636678cb8d99e32e3676d278cb8d9db49e32e36678cbe35d199e36670f5d022631e364b8d99e32e36678cb8d99e32e36678cb9e31f40999e31f6d088d99e32e36678cb8d99e32e36678cb9c3e359c3d631d9e37d748c9d236678cbd636678cb8c78d99e36678c7d278cb8c9478d679a02b69a7c9c000d060d0bfb65d10000,0x89a7c9c000d060d09fb65010002,0x1e39a7c9f000d060d09fb3c020004,0x2e39a57ed000d060d09fb3c020006,0xf39df6d748c42f8db5d23555d438098092b6d748c47b57ed00fb0e0d09883c1c0000,0x3e368c38c7db50f8d838c7d740f50e31e32631e30f8df5d230e3276d748cbdb40f8da30e31f6d03e230f8df6d231f8db42237750f8df6d03e031f40f42482952a32c30f88c70f8df6d088c90c3e231c3e37db4203e35d232768c78c3e36d230f8da30e31f8d03e270f88c78c98c8d959a0283e36d030f88c78c854a0c38c70f8df42232631e32e32239a7cc5001d0e0d095a3cb70000,0xf40f454a8c9da313ddf6d2310be36d748d52b6d238c7cc500fb1e0a095a3c1c0000,0x3e34be30f8be3278d2f0c3e231e32630f8db4be32f6db4bdcbe3276d2f72f8c9daf8dcbe32f6d2fdb4703be22b61f68dd2f68dd2f68dd2f6be374bdb48dd2f4be3263736be32e3736d2f8cb8dcdb4be32e3738db4be32f8bdd538d2f88ae23254e36d2f88a8c78dde36d2f8d42b6d232f50f48c3e03e231e3276d1d0f80f81f8578d0954ae36d0ae368d52b8db42230f8db47550f80f8887578d0954a54ada21ca2152a32e32639a8db600fb1e0a09463cdf0000,0xf8d230e32740f8da30e31f60f88c3e232788c78c98c3e36d2354adb48cbdb59a8db600fb1e0a095a472a0000]) (.b 496 (.p [0x1e39a8dc500fb1e0a095a3c020002,0x2f59a7cc500fb1e0d095a3c020004,0x2639a7cc800fb0e0d095a3c020006,0x190f40f4809da02a36678cb6678cb8d99e32e36678cb8d99e32e36678cb8d99e32e36678cb8d99e32e36678cb8d99e32e36678cb8d99e32f48d99e32f48d99e32f48d99e32e36678cb8d99e32e36678cb8d99e32e78d99e32f8db59c3e369e30f89e31f60f60e31e31e30f8db49e32f5d03e369e30e78c7db40f89c3e231f80f8db49e3278d278d12b8db42230f8db40f4643e3480ad278c99e32278cb8c98c78c3e36d278d12b8db5d278cbdb59a7cc800fb0e0d09885be70000,0x1e39a7ced00fb0e0d09883c020002,0x2f49a57ed00fb0e0d09fb3c02000a,0x99a57ed00fb060d09fb3c01000c,0x89a57ed00fb060d06fb3c010014,0x1e39a57f600fb060d06fb1e020052,0xb9a32f600fb060d06fb1e010070,0x2639a32fb00fb020d06fb1e02007c,0x1be35d23113e488042b8db48fce36d749e3f07d199e36678c7d67e631f92a3263119e37db5d278f98c7db410b8c8db58d3da580ad7a4f7db5d042f7d744b8df5d236ab8c4688e34adb8c88c9d234eba212b4e78df5d1b4fa1ca8c9f078c88c4eb8df5d236eb8522b7d1be4a8c88c9d7410b4e12a3279e498c88c78c45632e3000502fb0efb1ea50000,0xc3e358c76f8df5d232630f50c90c3e37d498c78cb0f8d23089e37d23203e23089e35d231f6d748f9e4bf38de32430f8de323ce37d74259e37d748c98c80fce37d2327ce37d23237d748c9d631e310bda39a57af0005021d0e3b1e6c0000,0x6e30aba212b8d746ab8c46ab8c4238d2b6e3213e2ba212896ab8da234adb6878c86f484a8c46ab8fc235d042daac46eb8c4238d742522a31dbeba2d3293e35d092bce368c78c84f484a8c47b57ae000302fb1e3b1e640000,0x6db4cae35d1be354cad43139e34108e351f40f8d08d7410b4f8d742b8d742b88d32b8db5d239a7ca60003023d1f3b1f320000,0x1aada22b6f8d748c80aba212a348ae36d639a7ca6000302fb3e291f170000]) (.p [0x1a0f50f5d211f484a8daae32e36ab8cb8daae32e36ab8cbd636cbd636cbd636cbd636ab8cbd636ab8cbd636ab8cb8daae32eb8daae32f8d6b8daae368be356b8d47adbe35d2b8c8d748daae32e36ab8cbe2b6f88c84b8ae12ab8c7d2b0f40f48c8d748dbae32f48dbae32e36eb8cbac3e2b8c3e34ae3238d232236eb8c3e03ae31e3235ae32dbae36eb8c8e358c7d232236eb8dbae36c3e1be34ae11e12b4ae3234ae3235d232daae36eb8c8e37d748c99a7ca6000302fb3e3b2aeb0000,0x79a7ca6000302fb3e3b1f010002,0x235d239a7cae000302fb1e3b1e040004,0x2e39a57af000302fb1e3b1e020006,0xf38d74ae313c238db5d2b8d22b48fce36d748d32b5f3c2fae8b4ca84a8c78c8d748c47b57af000504fb1e3b1e2e0000,0xf8d740f8d230e32350f88c3e348c8e231c9d03e35d030f8d232232430f8df5d098c78c88c3e35d236c3e340c8d03d03d0820a8c9d532a32c30f8df5d090f8da3203e36d47d748c3e35d0384ad43ac3e378c8243ac3e378c8f38df5d098c70c3e37d74243e37db58c7d232232e31e39a7ca70005043b1e3b1e940000,0x1ae35d2b8daae3234adaae3235ae36ab8cbd6b8daae32f5d2b8daae32f5ae36ab8cbd636b5ae32f58dad6b8cbd9ae35d2b0f5d2b0f8d748c8d232358daae32f5ae36ab8cbd636ab8cbd636ab8cb8daae32eb8daae32f8d5aae36ab8c8e352631eb0f8d2b0e3234ac38c88c3e35d2b8cbd5aae30f8d74ae3238df525a0f884ae2b0f8ae3238ae348ae368c78c88dae36d74ac3e35d1aae311aae32f8d2b0e321aafce35ae32388c7ac9ae32232e39a7ca7000504fb3c241ee70000,0x3e35d1a0f5d2b0f5d08d7484a8daae32e36ab8cb8daae32e36ab8cb8daae32e36ab8cb8daae32f58daae32e36ab8cbd636ab8cbd636ab8cbd636ab8cb8daae32e36ab8cb8daae32f8d2b0f8d2b0e32350f8d230f8d2b8cbe2b0f88c8e2b8d22b88c78c82630f8db5d2b8cbd639a7ca7000504fb3c2f25910000,0x1f49a7ca7000504fb3c3b1e020002,0x2239a7caf000504fb1e3b1e020004,0xb9a57af000504fb1e3b1e010006,0x99a57af000502fb1e3b1e010008,0x2239a57d9000502fb0e3b1e020010,0x199db6678c86489e31e7e792db0a02b8d74259e78d602a713ce358c41f8da78c88c74e580a8c47b579f0003021d0efb3c330000,0x6678d99d9e35d270f58c7d631f48d92f48d99e32f48d99e32f48d99e32f59e31f48d99e32f5d236678cb8d99e32f58d99e32e36678cbd670f49c3d278c8d748d99e32f48db9e32f48db9e32d99e36678cbe348c8d631e36678d99e31f5d278cb6678d99e31f8d748c96678d99e31f8db48c86c2e37d749e580ae35d236d9e78d749e010ae349e321bd631f40f8d7480ad2310be36d748c7478db5d202b5d239a7c9f0003021d0efb3cd40000,0x2e39a57a00003021d0efb3c020002])))) (.b 544 (.b 528 (.p [0x6678c46678c42f8db5d278f9e77db5d2310be34e792e32231f5d230f8da580ad748c47b57a00005041d0efb3c2e0000,0x3e35d03e358c38c7d03e270f88c78c82750f8d740c3e358c78c90c3e37d742632231e30f8db5d270f5d03d670e31e32631e32c3e03e231c3e37d748c90f8db48c89c3e36d631f5d230f60e72190c29e02602a78c89c30f8d74243e36d08d631c3e36d6780a9e32e32239a7c9d0005041d0e643c8d0000,0x478da79609a7c01000504160efb65060000,0x678d676678c7d27087d83d278c3d278c8d278d99e32f6d088d99e32e36678cb8d99e32e36678cb9c3e359e30f58c7d022348d99e32f5d236678cb0898d99e32e31e36678d99e31f49e32e39a7c9c020504110efb65640000,0xf8d74659df5d270f51f580a66780b66780b66780b66780b66780b66780b6679602f40602f580a8d99e32e36678cb8d99e32e36678cb8d99e32f48d99e32e36678cbd236678cbd236678cbd236678cbd236678cb8d99e32c9d23676d749e32e3678db5d278cbe349a7c9c0205041612fb658a0000,0x2239a7c9d020504160efb65020002,0x2b59a7c9d0005041d0efb65020004,0x1e39a7ca00005041d0efb3c020006,0xb9a57a00005041d0efb3c010008,0x2639a57d90005021d0efb3c02000a,0x3ce35d236d34d3e78d20108e3480880880a8c9d748d32b6d748c47b57d9000402fb1efb3c230000,0x6590f5d03d74808d602912d12d12f580a9e36cbd236cb8db2f48db2f48db2f48db2f48db2f48db2f49e36678cbd1964be27647d2364be35d278d99e31f4678d232359e36678c7d676678c7d749e36678cbd232358d9d678cb8d9d749e32e3678d749e32f89db9e36e78cbe231d99e36678c7e348c88d9e359db9e31f58cb6d3e35d202b8d748c74f8d7480ad239a7cc90002023b1efb3cbc0000,0x1a8dbd74ae12b5d236ab8cbd636ab8cbd236ab8cbd236ab8cbd236ab8cbd236ab8cbd236ab8cbadbe348c86f8d748c84f8d7484ad636ab8dbae32346e321384a8cb4f8d212a39a7cc9000202fb3c593c5d0000,0x13df54f76d32932a32231e34f7d748c42f5d238c7ca9000202873c875a190000,0x1b4cae234cae239a8d53000202593c6c5a090000,0x4f8df5d278db9e3235d23948d53000202593c876d0e0000]) (.p [0x1b0f40f42352a36e78cb8db9e32e36e78cb8db9e32e36e78cb8db9e32f8d43e350f80f88c88c78c3e35d232f8d1b4cae232231e36d32b8d748cbe1329b9e36e72f8d749e36e78cbe232239a954c000202593c7d6d630000,0x6c3d270f49e32342236cb8db2e36cb6cb8db2e36cb8db2e36cb8db2e36cb8db2f48db2f5d236cbd748db9e32e36e78cb8db9e32f48db9e32f48db9e32e36e78cb8db9e32e36e78cb8db9e32e78db9e32f8d679a954c000202593c877e6e0000,0x1e39a9553000202593c876d020002,0xb9a8d53000202593c876d010004,0x1e39a8d6b000202593c875a020006,0x6db0f50f5d211f5d212922d22f484ad636eb8cb8dbae32e36eb8cb8dbae32e36eb8cb8dbae32e36eb8cb8dbae32f8d03e348c3e23238d03d03d232232230f8d74ae32f8d03e350f8d03e232231e30f5d232db4cae231e32236d32b8d748cbe356d32b88c78c88db4cae35d232f88d32b49a8d6b000202875a875a960000,0x2239a8da9000202873c875a020002,0xbd639a7cc9000202fb3c875a03000a,0x1f49a7cc9000202fb3cfb3c02000c,0x2239a7cca000202fb1efb3c02000e,0x3e350f50c78c78c3d748cbd03d43e03e232231e30f5d232c3e230f88c8e231e32230f8d748d32b5d232f6d03e358c38c7d746c3e03e07e03e08e03e351f8d742b88d32b8d742634f8df5d1b4c3e340f82380f81d32882932a32632e32239a7cca0004034e1e513c7d0000,0xf40f42236e78cb8db9e32e36e78cb8db9e32e78db9e32f50f8d43e340f88c88c78c3e35d278cbe346c3e11e27808e270f81cae2344ae232231e30f5d278c40a78c42f8d749e32f6d639a7cca0004034e1e7752620000,0x7d749a7cca000403fb1efb3c030002,0x2639a7cd9000402fb1efb3c020004,0x2f69a57d9000502fb1efb3c020014,0x89a57d9000502fb0efb3c010016])) (.b 560 (.p [0x1e39a57e3000502fb0efb1e020024,0x2e39a32fb000502fb0efb1e020036,0x3ce35d3c263f37db5d2310be36d748f9d84e76d7410b2b6d748c45632fb00fb06550e791e230000,0x3ce36d748c3e35d03e350c724ad83d740f8df40e32232430e31c38c88c98c80f8df6d43e37d838c88c70c38c80e31e32430e32038c70fce378c78c98c88c78c47b5727000d06190e351e550000,0x3e35d03d438c78c98c3db5d232f5d030e32038c70f8d742630f60e32030e32231e32e32430e32438c70c3e368c7d088c3d838c70c38c78c88cb0f8db5d230c3df68c70f8df6d232232f88c98c80c38c80c3e36d232231e30f60e32030e32231e32c3e36d748c30f7da3203e37db58c78c42f88c90f8db5d230c3e37d631c3df5d232632f8da32231e39a7c27000d06190e351eb70000,0x2e39a57d3000d06190e351e020002,0xf6d7c1e313cdf6d748c42f8db5d23efb2e22b6d748c47b57d300fb0e190e351e1e0000,0x3e36d431c38c90c3e348c9da32030f8203e358c9db58c78c3e37d748c38c9d830e32632030e31c30f8de32632231e32e39a7cbd001d0e120e261e410000,0x3e35d2f8c38c9d740f8db50c7d032232630f8db5d2f8c38c9db58cbdb50f8db58c3d83e03e232632231f672f8c3e36d2f8c9db50f6d2f8c3db4be3276d631e372f8cb8dcbe32e372f8cb8dcbe32e372f8cbbc3e36d1cbe30f8be32788c872f8c3e35be32788c78c98dcbe30f8d431ef8c9db4be32c3be22830f81c3e232632632231e30f8db5d2f8c3e37db40f8d2f0e32740e22a3223276d748cb9a7cbd00fb1e120e261ecf0000,0x2639a7cbf00fb0e120e261e020002,0x3e36d630f8db50f8d438c91e31f69a7cbf00fb0e1913261e130000,0x2239a7cc200fb0e190e261e020002,0xf8d748c38c9d740f8d748c38c9d03d038c92232630f6d230e3236d748cbdb59a7cc200fb0e190e35272a0000,0x1e39a7cd300fb0e190e351e020002,0xb9a57d300fb0e190e351e010008,0x2639a57d400fb06190e351e02000a]) (.b 576 (.p [0xf8db4ac3e35d038c98c88c3e36d74ae32f6d03e36d230e3236d43d838c88c78c88c3e37db5d2b8c38c8db5d232f6d03e36d630f8d438c98c7db50f8d748c3e36d43e350e32631e3275d030e31c3d23203e35d232630f60e32030c78c78cb8c98c78c88c3e37db58c3e37d740f50c78c98c7db5d2310bdb49a57d400fb06551a351ea00000,0x2239a57d500fb06550e351e020002,0x3e37db5d278f9e37db40f8da70e31e32231f6d748c47b57d5000e06190e79361d0000,0x3db50f6d038c88c78c3db5d232f6d03e35d03e36d03e340e32488c9d740f50e31c30f8df6d232231c3e35d098c3d678c3e37db5d278c42f50f59e32670c38c90e32231e32e32632239a7c3f000e06190e4b36610000,0xf7db59f7d74677d742631e36678cb6678cb8d99e32e36678cb8d99e32e36678cb8d99e32e36678cb8d99e32e36678cb8d99e32e36678cb8d99e32e36678cb8d99e32e36678cb8d99e32e36678cb8d99e32f6d670f8db59e30e31f6d03da70e31e32231e30f8db5d278cbdb59a7c3f000e06190e794c900000,0x1e39a7cd5000e06190e7936020002,0xbdb59a57d500fb06550e7936030004,0x1e39a57fb00fb06550e791e020006,0xbd749a32fb00fb06fb0efb1e030016,0x99a32fb00fb02fb0efb1e010018,0x89a32fb00fb02fb06fb1e010050,0x79a32fb00fb02fb06fb0e0100ce,0xb9a18fb00fb02fb06fb0e010194,0x99a18fb00fb00fb06fb0e0101a2,0x89a18fb00fb00fb02fb0e0101b4,0x79a18fb00fb00fb02fb060101d0]) (.p [0xb9a0bfb00fb00fb02fb06010218,0x89a0bfb00fb00fb00fb06010238,0x1f49a0bfb00fb00fb00fb0102023a])))))))
private def data : Store := ⟨vals,rows,model,8,false⟩
def ok := test rule 5 11 data
theorem finish (checked : OMA.Tape245212.Before ok 579) : Deny 5 11 ![⟨2,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨12,999999999999999999⟩] := by
  have same : data.vertex 578=![⟨2,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨12,999999999999999999⟩] := by decide +kernel
  rw [← same]
  exact close valid _ _ data 578 checked
end OMA.Tape5_11_245212
namespace OMA.Tape5_13_245212
open OMA.Box245212 OMA.DirectTape245212 OMA.TapeShared245212
private def vals := OMA.PageTree245212.get (.b 272 (.b 128 (.b 64 (.b 32 (.b 16 (.p [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16]) (.p [17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32])) (.b 48 (.p [33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48]) (.p [49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64]))) (.b 96 (.b 80 (.p [65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80]) (.p [81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96])) (.b 112 (.p [97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112]) (.p [113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128])))) (.b 192 (.b 160 (.b 144 (.p [130,131,133,134,135,136,137,138,139,140,141,142,143,144,150,151]) (.p [153,154,155,158,159,160,161,163,164,165,166,167,168,169,172,173])) (.b 176 (.p [175,176,177,178,179,181,182,185,186,187,188,189,190,191,192,193]) (.p [196,197,199,205,206,207,208,209,210,211,212,213,214,215,217,221]))) (.b 224 (.b 208 (.p [222,223,233,237,238,239,249,252,253,254,255,256,259,260,261,262]) (.p [263,269,270,276,277,286,287,292,293,302,303,307,310,313,314,317])) (.b 240 (.p [318,319,320,331,334,335,339,348,350,351,352,358,365,366,374,375]) (.b 256 (.p [382,383,385,396,406,414,415,432,452,453,455,456,457,478,479,517]) (.p [558,561,564,624,633,638,639,660,715,768,776,777,800,830,831,835])))))) (.b 400 (.b 336 (.b 304 (.b 288 (.p [836,846,902,903,958,959,968,993,1025,1034,1035,1053,1069,1113,1135,1161]) (.p [1266,1267,1297,1320,1321,1407,1606,1918,1919,1936,1937,1986,1987,2050,2051,2070])) (.b 320 (.p [2071,2106,2107,2226,2227,2270,2271,2594,2595,2642,2643,2790,3257,3692,3700,3838]) (.p [3839,4096,5580,5581,6535,7661,7678,7679,8696,8862,15358,15359,30718,30719,61438,61439]))) (.b 368 (.b 352 (.p [0x1dffe,0x1dfff,0x3bffe,0x3bfff,0x77ffe,0x77fff,0xefffe,0xeffff,0x1dfffe,0x1dffff,0x3bfffe,0x3bffff,0x77fffe,0x77ffff,0xeffffe,0xefffff]) (.p [0x1dffffe,0x1dfffff,0x3bffffe,0x3bfffff,0x77ffffe,0x77fffff,0xde0b6b3a763ffff,0xf256c8fc5d45d9dfb,0x10ad25178760d42ed5,0x10ad25178760d42eda,0x10ad25178760d42edd,0x10ad25178760d42ede,0x10ad25178760d42ef8,0x128ce887a1615f1ab0,0x128ce887a1615f1ab3,0x128ce887a1615f1ab5])) (.b 384 (.p [0x128ce887a1615f1ab9,0x128ce887a1615f1abb,0x128ce887a1615f1abd,0x128ce887a1615f1ac9,0x128ce887a1615f1ad9,0x128ce887a1615f2389,0x145a2e34d2b66ee684,0x14e627a5b754e268c4,0x14e627a5b754e268c6,0x14e627a5b754e268c9,0x163bfb6ce86668a3bf,0x17a257ca02025b19b1,0x17f4a917a3fee7a8df,0x187b054496cfb81c58,0x187b054496cfb81c5b,0x187b054496cfb81c5d]) (.p [0x187b054496cfb81c67,0x187b054496cfb81c81,0x1b3b4dc85d23bf50c1,0x1b3b4dc85d23bf50c4,0x1b3b4dc85d23bf50c5,0x1b3b4dc85d23bf50c6,0x1b3b4dc85d23bf50c7,0x1b3b4dc85d23bf50d0,0x1b3b4dc85d23bf50d1,0x1b3b4dc85d23bf50ee,0x1eadec03a98064531f,0x1eadec03a980645321,0x1eadec03a980645324,0x1eadec03a980645326,0x1eadec03a98064532c,0x1eadec03a980645332])))) (.b 464 (.b 432 (.b 416 (.p [0x1eadec03a980645393,0x205f5585d89c2a629c,0x22ab8ae837ae440fa4,0x22b1c8c1227a000ef5,0x22ea5b2775dafb2abe,0x230a18eeb1004de0a7,0x232a9ff2c8634775f1,0x2350ba6377f02e3d01,0x235db090056a319b9b,0x235db090056a319b9c,0x235db090056a319ba0,0x235db090056a319ba3,0x235db090056a319bac,0x235db090056a319bbb,0x235db090056a319be7,0x26f059218034103ac7]) (.p [0x26f059218034103ac8,0x26f059218034103ac9,0x26f059218034103aca,0x26f059218034103acb,0x26f059218034103acc,0x26f059218034103ace,0x26f059218034103acf,0x26f059218034103ad1,0x26f059218034103ad2,0x26f059218034103ad3,0x26f059218034103adb,0x26f059218034103aeb,0x26f059218034103aec,0x26f059218034103aed,0x26f059218034103b1c,0x26f059218034103b1f])) (.b 448 (.p [0x293eedfb643886e0be,0x2b50957e451d5eb235,0x2b50957e451d5eb237,0x2b50957e451d5eb239,0x2b50957e451d5eb23a,0x2b50957e451d5eb23c,0x2b50957e451d5eb242,0x2b50957e451d5eb244,0x2b50957e451d5eb245,0x2b50957e451d5eb247,0x2b50957e451d5eb25f,0x2b50957e451d5eb260,0x2dc8364ffe851e6b4d,0x30cc7ad76f8aee9c31,0x30cc7ad76f8aee9c34,0x30cc7ad76f8aee9c36]) (.p [0x30cc7ad76f8aee9c37,0x30cc7ad76f8aee9c3c,0x30cc7ad76f8aee9c3d,0x30cc7ad76f8aee9c3e,0x30cc7ad76f8aee9c43,0x30cc7ad76f8aee9c44,0x30cc7ad76f8aee9c45,0x30cc7ad76f8aee9c4c,0x31f2563002a3441a67,0x3299bd9adc6c9d9f95,0x339413a960d546bbbc,0x339413a960d546bbbe,0x339413a960d546bbc2,0x3434f873142f0c4736,0x3434f873142f0c4741,0x3434f873142f0c4742]))) (.b 496 (.b 480 (.p [0x372f66d66c19ad9f70,0x372f66d66c19ad9f72,0x372f66d66c19ad9f78,0x372f66d66c19ad9f80,0x372f66d66c19ad9f81,0x372f66d66c19ad9f82,0x372f66d66c19ad9f83,0x379d7e390794e46978,0x37ef9c7b4c7b8d27b4,0x37ef9c7b4c7b8d27bb,0x37ef9c7b4c7b8d27bc,0x37ef9c7b4c7b8d27c4,0x3999abfcedd09a3f38,0x3999abfcedd09a3f39,0x3b1f490a6c622f1e98,0x3d35d8f94472dfb4a2]) (.p [0x3d35d8f94472dfb4a6,0x3d35d8f94472dfb4a8,0x3d35d8f94472dfb4b8,0x3d35d8f94472dfb4b9,0x3ddd7e05e67ebdccc0,0x3ddd7e05e67ebdccc2,0x3f6b5e661703c856fc,0x3f6b5e661703c856fd,0x419b1372a80091cfe3,0x419b1372a80091cfea,0x419b1372a80091cfec,0x419b1372a80091cfed,0x419b1372a80091cfee,0x419b1372a80091cff7,0x4557c1ec39ac594ebd,0x4557c1ec39ac594ec6])) (.b 512 (.p [0x45b2a27d26dfd104cf,0x45b2a27d26dfd104d0,0x45b2a27d26dfd104d8,0x468be346a2411e02d0,0x4805ce57c0486149db,0x4805ce57c0486149df,0x4a13cf3b80f6a62d9d,0x4a13cf3b80f6a62da3,0x4ed1bea06e1c08b8f3,0x4ed1bea06e1c08b8f5,0x4f71ffa3fd52b9a3e8,0x4f71ffa3fd52b9a3ee,0x4f71ffa3fd52b9a3ef,0x4f7a66db190b52ef23,0x4f7a66db190b52ef24,0x4f7a66db190b52ef29]) (.b 528 (.p [0x4f7a66db190b52ef2b,0x4f7a66db190b52ef2d,0x4f7a66db190b52ef33,0x4fe44592f07a74d064,0x4fe44592f07a74d067,0x4fe44592f07a74d06f,0x53f87dfff6b08d2044,0x53f87dfff6b08d204f,0x576cc6197d4ebccfae,0x59e12f978e93adae37,0x59e12f978e93adae39,0x5b1a3c6e14ded49d6d,0x5b1a3c6e14ded49d75,0x5b1a3c6e14ded49d77,0x5b1a3c6e14ded49d81,0x5db3e7637d74643dea]) (.p [0x5db3e7637d74643ded,0x5db3e7637d74643df6,0x5e54f160d23c893699,0x6021b0f75b563ad5b0,0x6021b0f75b563ad5b1,0x63b15ae6fe106d6d60,0x63b15ae6fe106d6d61,0x68155a43676e002c70])))))))

private def rows := OMA.PageTree245212.get (.b 912 (.b 448 (.b 224 (.b 112 (.b 48 (.b 16 (.p [0x47cd05c0d85c0085c0085c0401003020000,0x293a3b152dafdc78f086cb5c1d15e0b1d026fbd0581085c0285c030540a01c05300000,0x18f572ead899849dc2aec431df28b4d8a8c2d80581085c0201c0385c1601c052b0000,0x2f226cc149db16c40581085c0285c0885c1601405100000,0x15d7d02f8d2fbe765ffd2d39c4042f4509d18a60d2e15790a30af34f8b13fdc25663673170d6d5205f55f4ad22ca4d29f35e25e2d52f04f2aca033374bce2a19fedaba2ef2173b528d43a9eb1a5bc1897b707ff35ce129a3e9cd40581085c0285c0885c1601c06b40000,0x840581085c0285c0885c1601c05010002,0x640581085c0285c0385c1601c05010004,0xaa08c05c0d85c0085c0085c0401c05050006,0x798a5980d85c0085c0085c0101c03030008,0x15b67bd06c0d85c0085c0000c0104c09080000,0x60ab79ceeeee480f7eecf258ea3014a73eba31ba0233d7bfa71453b07cb6f73cb0581085c0185c0200c020a414490000,0xf09c64ae812d5be19d8db0581085c010140200c0285c2a160000,0x16dfbd56eff573a70f0f18bdff0c3584ecb3adf1c9f3f879968747d44f2464148c9076c80069c685b17e4220e6e09444bcc204840519fa879b3f24057c2d663a63629dee8bcd82462763f6bcb8c9d0a198630dc99b77c80581085c0185c0600c0285c2ab80000,0x640581085c0185c0200c0285c2a010002,0xcbc8a06c0d85c0085c0000c0185c14050004,0xce835980d85c0085c0000c0185c08030006]) (.b 32 (.p [0x1f4058108480100c010240404408020000,0xc9799d201641c871f0cf5344143254a8af0b2dd0c6ccf284e43b0345aad0f08df1be058108480185c040240402c084e0000,0xb3202cb572983c87a4dfa4894a477caadf0f1b48db7bb0ec86a829bb28f00305a1e264200fea6e5ffa548c9f707ddf478be42f861f4c6c677f39406da3a1865a9ec6e0003f0ba058108480185c04024040440c9f0000,0x84058108480185c040240404408010002,0x40e670581085c0085c000240404408040004,0x863c5dee89f544b57579c99b3e0970ef9938783364e900f7c356176fdd80581085c000040085c0a04408410000,0xe84840089d2291e99e4f925c264eab6c7457ffb03c490283679c428ebb8bb90420b41ac45bd59b970cb28956faa70ebacd02d4398d2058100040085c0285c0a044086a0000,0x942e56576d43b33470e6fc28fc6b3a31e01f56374ee22709f54ea7d52ed16788d192d44ad3b8bd6029f82e9ed2e112c3263ccd3f3a529292587cf0581085c0285c020540a02c088c0000,0x28584a85692e7227334d3c505832f61b458f7a45a9dc74e9803bd8da0581085c020140285c1602c08400000,0x19fac5a537f90394c288cb4eac942b670dc71e94a53462a97892f919e44874b9cb93ae0ca3659a678e5ede73f8182eacce33f4cad6610ec44a792c69a8ac6b4fd28844f96ccb3ce90581085c0285c0685c1602c08990000,0x640581085c0285c0285c1602c08010002,0x8d0581085c0285c0285c0a02c08010004,0x8131a85648670718b6cae081c83af397082dc95526eca96588637dfd9f439e3badaa6ecf07a0a25e7a342fcf0581085c0285c0285c0a0440c640000,0x840581085c0285c0285c0a04408010002,0x590581085c0085c0285c0a04408010008,0x640581085c0085c0085c0a0440801000a]) (.p [0x8d0581085c0085c0085c040440801000c,0x42f218526b741f9d2a2e8ff5b5957a717df6f9029a6b658a6502b30f0b5dc0581085c00004000240485c123e0000,0x4edf4fc66258156195ea840c80035ff0cd1b0b4d6ca3df1c2046df058100040085c020240485c12330000,0x17f2fcd045028dccb1f54bd31aef8be39d58f080d1f72acbf187490de6db6379b6488d328a527ca9134caedce989589fe75ad2fde2aec43afd9f53ffecf2451d8a8ba0581085c0285c020240409412960000,0xb00c4e9045cf1f113f4a454b9b589e70b0c49292e8586031fb77e61a89b528f2f9d495e414487c3012ea606b2e70581085c0285c020240485c265d0000,0x840581085c0285c020240485c12010002,0x590581085c0085c020240485c12010004,0x640581085c0085c000240485c12010006,0x6a43e4ec80db98ec2170d6dcfe9678ddb550f9c9deb15c3d20f9187c0418f87884e21ebce174472b321c8d8799fd9a4387e8023fc27b89fe90ec83fbec9e016b46546c77854acc7135d7bceeed257b383a0b753db3ef10581085c000040085c0a85c12af0000,0x12040d9beb2af3551e354b6c1a147a3ecf22fe725e5837e03d88d0a6b7c2c79afb7d3d073d9c64a0403e4a75d686860e90581085c0085c0285c0a85c12670000,0x640581085c0085c0085c0a85c12010002,0x8d0581085c0085c0085c0485c12010004,0xf8906c0d85c0085c0085c0485c0802000c,0x18bfdf668eec28241ae9582a42e531ba8e46d834cb5088ad76f88cb9b890750d21e2c862b112e0fc5e84e35a4aa709b52f6374fbe50442147e2952bc1641c85c0085c020440804408970000,0x43fb4c96a78b25face2122bc0009279d213bc0a41c85c0285c0609c1302c082c0000,0x17fb3329764871904f3cf3c2d60a267281e7bd2bfbcf0849f48b60bf2b3fdd492adece3c40a01c85c0285c0685c2802408500000]))) (.b 80 (.b 64 (.p [0x2c29f6ffd33612cab8144bd6f2cc2dbf34910a2594e3e8d3e773f03fef2f3b0162f0facced9927aa94da6136b43f56b2c5c2ac665416b7d9f4815805b1d85caeaeb1b6b532ad4d91778a1be6b743a008a709856c50a01c85c0285c0685c2802c0ab60000,0xf890a41c85c0285c0685c2802c08020002,0x5c8f1601c85c0085c0285c1202c08050004,0x11ef6b545e56b2f07d710debd41a8b81b2d7c1f5a7c31d925765047d50d90a81c85c000140285c120440c480000,0x12c4130533c70dcec646f841f9fda1045c98528397c1625c402a48fdcbebd40a81c0040085c0685c120440c410000,0x14e32e0f42ba842df1e2b20066df27193910c1d2e4dd965a5c6048a7287ca06f466fba0841c7f00285c06094120440c530000,0x1b455f8b4b0a2c8b74ebbd1b314a3a2d9428b9b3aee180b431bf0a8247d80285c07094120380c3e0000,0x4d8343a64744596d986efd70f26225079e768fb98d51e6160893f4480540213dd1cc91da4b64d9216c05568ac658391663dadbd0a8247d80285c07094120440f7a0000,0x8ec880a8227f00285c06094120440c040002,0x6f0a81c85c0285c06094120440c020004,0x3551a1918e3a2195998c9802f60b3d55a1a6efeb0450eb28efab90841c85c0285c0685c260440c360000,0xed38631d3b7893b6fbda37cc8a2e2d8d80a82485c020340685c260440c280000,0x126203c9d30a8240140285c0e85c260380c090000,0x1cc14b9554c468f4ced0328de61c0b86ccdb490c6ea7c435fa8960177bd0a82485c0685c0e134260380c3e0000,0x3a1f527562914f85ced7216546bec74710415131e0f50c27b12d32a2dbf9834722e9da149fdd4ca485a4fca2ebfc17717f14020b9bfc31adf9cd0a82485c0685c0e85c4e0380c7e0000,0x8d0a82485c0685c0e85c260380c010002]) (.p [0x590a82485c0285c0e85c260380c010004,0x8a198e5a1910375fa35f438d83189b6c4c239e39e90a82485c0285c0e85c260440f2e0000,0x840a82485c0285c0e85c260440c010002,0xf630a82285c0285c0685c260440c020008,0x6f0a81c85c0285c0685c260440c01000a,0x8d0a81c85c0285c0685c120440c01000c,0x590a81c85c0085c0685c120440c010012,0xf630ac1c85c0085c0285c120440c020014,0x1d43f4b36822523b60ff20a1809694ac0e0972a47ec5149e7cc7e72cdcfcaf49bc1602e85c0185c060b4160440c570000,0x471bed69993fcb4627d8710196cd81602e85c010340685c2e0440c250000,0x2f62cba26002274be5d758424ca48fe70e3b023d147c26792ee7443706705d2e36e2e141ef340c33e0146a846d5c60f02e85c0185c0e85c2e0380c710000,0xebf96617f96d20f02e00c0185c0e85c2e0440f0f0000,0x20befbc3ac2f7dd50a125531d96496ab72ef6ea65a929495f5c222e17c6de2c7a9ba0de931f9989201bb8076d6c557e6bba58fea7f7f8bce5a14d2322c60f02e85c0485c0e1742e0440f8f0000,0x6d02c589a62439b202cbdce5c9aff8174fcf7db627756ac8ca4e7df2e7f2a660f7e222a4d85b6798ec7e4ab228ea84749594b9cb4fca3c85bb3e058c70f02e85c0485c0e85c5e0440f810000,0x8d0f02e85c0485c0e85c2e0440f010002,0x590f02e85c0185c0e85c2e0440f010004])) (.b 96 (.p [0x840f02e85c0185c0e85c2e0440c010006,0x25f13e76bd787682d5ba3bbf37a879ce84430d1a098f6d8751044ed398a640a266fd2d13adfad5c5ce84f9057ccb4c3952bbdac71603d85c0185c0e85c2e0440c7f0000,0x6f1602e85c0185c0e85c2e0440c010002,0x641602e85c0185c0685c2e0440c01000a,0xaa08c1602c85c0085c0285c120440c05000c,0x6f1601c85c0085c0285c120440c01000e,0xf891641c85c0085c0285c1204408020024,0x68d5981c85c0085c0085c040440804002a,0xc60fa32ae48b28648e9dcdc20c1c85c0000c010240485c121b0000,0x9ebb0b81c7e801024040240509412070000,0x34bec2a43323b74ee295c5d857ddb215af97c715364903f8418351a832f650162493acef97a95f9d4e07401b3b90881c7e80185c0a0240509412700000,0x2de9523e9be87143719a7d0d3b8933f7f813a26b516301efe1dbfd3c5a74dbc0b8237e80185c0a02405094124f0000,0x6f0b81c7e80185c0a0240509412010002,0xa0e670b81c85c0085c040240409412040004,0xec8ea6df74ec9be858aadccefedd0b81c85c01024040140485c261d0000,0x93d8c241397ee802eb6bbaa30e3f180bf6a13dfa00027150ad44acfecd6041d33d7a6ace614f3d91570edf0e0785b76f6fd3957ba752e82415420a5bafe2195f80881c85c0185c0a0140485c26850000]) (.p [0xc6e75c4adbb74681bd790bf657a6ef71d029e4f5e45b82e5079d1ab522ed296250f70ea317f72967afec41fcb224eef89df9cb0b82385c0185c0a0140485c267a0000,0x6f0b81c85c0185c0a0140485c26010002,0xe680b81c85c0085c040140485c26020004,0x2c32158ed37ab4086137d98d79e00b81c0040085c040240685c26190000,0x4291880912e13dd46086acb7c8c8891fa74fef926ea5f760ff970bccffb27b4839039dd0b81c85c02024040240685c264d0000,0x3fd8f8ecc3c9c63e93538e80881c85c0285c0a0240685c26190000,0x117e41580300d245ff76b1d505c6c761c31fe0dfb3fbdaea53a290828a588927002639e905c7bd4474dddb8979076b1bd0b8247dc0285c0a01c06134266f0000,0x45dad50133697c7e066c66a5049bf6a51630a16039a0708e6c0d92f4d6fee49fe9ef9c80b8247dc0285c0a02408134264e0000,0x8d0b82485c0285c0a0240613426020002,0x1b67cbf97355a07d411397b05c2dc83c0af9a336906c221b0e1696da0eb9d92bac7f03a7942b701233c9b4cfa04b6b15c9a6128f72867d2f34a7cc92498af80b82485c0285c0a0240685c4e820000,0xf890b82385c0285c0a0240685c26020002,0x6f0b81c85c0285c0a0240685c26010006,0x640b81c85c0285c040240685c26010008,0x590b81c85c0085c040240685c2601000a,0x8d0b81c85c0085c040240485c2601000c,0x840b81c85c0085c040240485c12010012])))) (.b 160 (.b 128 (.p [0x3a0f2ddc80d3197816a6df3fd1b52c3f572616be6be87ed42758e60c3aa745459a98f64a83c0a83142c4bc204348500085c0602406144286c0000,0x14bb787abfcef959b0cfdc1203484c00034060240685c52190000,0x192ff76df120340040085c0e0240685c52090000,0x1709b19e204bac2fed9efa735d248355875dba6d946422187eaaadfbe9f7239ba07ec45e4e8cd8995db82ab4f3c26b1b5788d506bef8b238420df70d3981d4f77ac91203484c0285c0e01c0685c52960000,0x7fb99c3ece20312184b31771ccb0fe6a51d295617fc4cb066939336b434e9f6f85b4ccf44080c0d69f5c829f573a990847619b7c81203484c0285c0e0240826852710000,0x1293ec93435565740ea52bbb4ac8419c260ac38b9ce57664636aa3b7df1c346adede1203484c0285c0e0240885c9b4e0000,0x841203484c0285c0e0240885c52010002,0x8d1203484c0285c0e0240685c52010004,0x591203484c0085c0e0240685c52010006,0x3269128348500085c060240685c52030008,0xa1af3f161e490e7636e137185f65323d9433825f5fbcc733910ada88a93b17641f5ad41f45a84ae3275109159e48d212e6c4db51a91827a8139be4224817ecccb2044b8500085c060240685c52a00000,0x6f204348500085c060240685c52010002,0xcb4872042f85c0085c040240485c1206000c,0x2e7220c1c85c0085c040240485c1202000e,0x66c5981c85c0085c000240485c12030026,0x19fe233ba660d1e31f9fb6834e30e379c501a3cffcad91381c81c000040085c0a0a414340000]) (.b 144 (.p [0x14d5542d3bc3bc2ead476b276ea0e4d610eb447f6d9593b5ca6c39993520219c58ee4faca7e06a8359dd8704bad84ddfcdfcf57c80b045ffedd9a917e2e7b95652b3dff7265ce5ecbebe4b1d3f3c13aec4d6b2617d0e50c8674a9943f10a41c818000040085c0a85c2aca0000,0x2d740c687301574879044a48a9e6ea5f980c9a445068c3614c48a0c56ca492948b8783bd87719858367c2d6dea554e991db7a89ebddf3d58bb85976395aa7ee464b7576f85e6ae31382a818000040085c0a85c2a9b0000,0x6f1381c81c000040085c0a85c2a020002,0xce835981c85c000040085c0a85c12040004,0x8a941da9167c373b90d01c7ec00014020540a09412130000,0xd00d01c0040085c060540a09412010000,0x4a9124110016813f85d8901d929af88f24adc4906ad461becb7c2153a8014b31e4d01740f43de834a0537c96c57f25b1b80901c7ec0285c060540a06012790000,0x69c498789c0e7c20cb5c53c305dc7ae7e27f1cddeb0b6d4fd00901c7ec0285c060540a09419400000,0x840901c7ec0285c060540a09412010002,0x3489e6e171e4a6a66b89906a1d32848afffcabc0d0287d00285c070340a06012360000,0x4d516e1317c0e3f8bbc1e48e93ee6019b06c963fca6aa48104ea925605929ede5d3b09728ae6f4debca6ef560ffcef6b310ce57b2e6f2a1136cd0d0287d00285c070540e060128f0000,0x10a900d0287d40285c060540a06012030002,0x538ee4ca69e21b0226bddacca8e8b80d0287d402034060540a094191f0000,0xaa748082e80fb654d5ffa756880802311e6bc1df55575be618f2e1b8a460aa1588248f354e5a9f0ebfeadb1941f9d8c0f6273d889ce0d0287d40285c0e0340a09419870000,0x13f91c1e0c30c92509fbc774cbc9d3e6ab3f1038aac3b4ba0d0287d40285c0e0540e094193b0000,0x8d0d0287d40285c0e0540a09419010002]) (.p [0x640d0287d40285c060540a09419010004,0x3c890d0257ec0285c060540a09412030006,0x6f0d01c7ec0285c060540a0941201000a,0x590d01c7ec0085c060540a0941201000e,0x640d01c85c0085c020540a09412020010,0xea0d01c004000140285c1609412010000,0xe8eecb93ef031ad8f4c61a4eef204747212f449da8a930b957461e19bc47a0616c1a7b667f70901c720020140285c1609412590000,0xe71914c672a10320393572b86e7d405ba32fa52c11990828a716083b4378128d7fc4d4625a8413f2ac4024ac57356d2e0ef0c3c318ca7a5407f0cb0eac6c534157e4f64c79bb0d025720020140285c16094129e0000,0x6f0d01c720020140285c1609412010002,0x590d01c85c000140285c1609412020004,0xa4736175f810eb9117ff0ba4c61af0b74b83f34359f846d57f0f8096f2746c8a115af6c955c0592e0e63a3a736d0b164dcd0d01c0040085c0685c1609412600000,0xfb3832f4f6c8399ca7eb5d72fbacc92b332dd2195ea7d87329d9b893099073b93e255f07d09be9da93e4f70901c85c0285c0685c1609412660000,0x1f4108089f46144e51cc046fa4cc974648fd74448c90bd020a844625b0da488d41e9acad93100c30e8d10d02885c0285c060b41606012650000,0xa1ebccc778f38330125e9b483293970480a8be260c318ef767be76a2c608eebdfbb252c99cd1da47bee90d02885c0285c0685c2e060126c0000,0x8d0d02885c0285c0685c1606012010002,0x1ab7ba0018795be412e840e3da4df2a5bb7e78942c00d78158a32792f8d70cd9d83ce0d02885c0285c0685c1609419540000]))) (.b 192 (.b 176 (.p [0xf890d02585c0285c0685c1609412020002,0x6f0d01c85c0285c0685c1609412010006,0x590d01c85c0085c0685c1609412010008,0x640d01c85c0085c0285c160941201000a,0x8d0d01c85c0085c0285c0a09412010010,0x53c89f2667994a5265e77df9cec46c794a21d12d4c89013a026d47c457e73b52f6d1490d376a940f254e85321fb80d01c85c00014020540a85c26670000,0x1f0bb0c776730de1816dbbe5dd0e7c2a4da40d3fa1f45b9d1b5c6a75129e3060436c3b66ab6b445549be33917c346919d87532a5a5c2d66b00b488c3ed4f093373d50511c1faf305cccb7c30a8d4d4c43786a17d4c55e4a612888584df0d01c85c0085c060540a85c26e20000,0x640d01c85c0085c020540a85c26010002,0x1c3f23864329019424c87b95de9b433374f83174a52b2c932b1b21cfacbe98d64ebfaaea278282bac38d3083495b9bcc4bfd73fa9fde60fe88a15212ca33815512a0abb7a96cf983583e60d01c85c0085c0285c1685c26ae0000,0x8d0d01c85c0085c0285c0a85c26010002,0xf890e41c85c0085c0285c0a85c12020006,0x121182e420c3a0040085c0705c0b09414080000,0xca58f384306c6c7d3d376cd3a954f7133a87cd6facd89769fd25df44bf2043a7a00285c0705c0b068144b0000,0x3449844be17c10dae65e751370d99254709cde0d1cf8d55fa98fc7e62010b08abd1383a7a00285c0703c0b0941b500000,0x3a3ebade9b41530ac1383a7a00203c0705c100941b160000,0x4d1f8eb1b5867c47bf9abb7ddfab5b85b0aa3ead4a0492dcdd1a6a6e0554304d2e2d517719dfbd28e81c4ffdf73a6d041cb09b6d4560ed42116249b28c2740394a561ac51ebd11383a7a00285c1005c100941b9f0000]) (.p [0x641383a7a00285c0705c100941b010002,0xf911403a7a00285c0705c0b0941b020004,0x325801f02e28da1186007f86cd3d113d2a3a93914dd278ca2021dfa6b0c6003778a22831c8ab792059962a79c94bf204517a00285c0705c0b0941b720000,0x6f2043a7a00285c0705c0b0941b010002,0x3c8920c3a7a80285c0705c0b09414030008,0xa65f5983a85c0085c0305c0b0941205000a,0x169da876f1d8fc844f070853b42279b7ec3acd1d28a7d1423c435311dfae2e8abd07cbb667994ee3ee4524d81c03a85c0001c0385c1809412700000,0x34547929bb1c03a7a401044080c418060120f0000,0x5fa230bd20f517007438d36fe353112e6f6b6882609383d8e846c1e37f928dbdbc4cc586ab3a5d723d15c1ca6a2f7355e85dbe8d5dcbd1203a7a40185c120c41805012860000,0x1571bf5f74fb41af5efd07148b787b5c15d7045473978bd56a9cc978e016a620470cd3605f3a9ba11762d7e711f041f5c4d21b55b382d8204a10b5f83cee3be87d4b325530f61203a7a40185c120c41806015ac0000,0xf891303a7a40185c120c41806012020002,0x109a0e383f6ff05e885c23fd943b6f736effdfadf489c94cfdfcad850c3e11eab133169bda1bd1c04d7a40185c120c41806012630000,0x6f1c03a7a40185c120c41806012010002,0x33d631c03a85c0085c080c41806012030006,0x5f08c76b55cae40d21c03a0040085c0885c3206012120000,0x60562343f1dddff4c1ac480e4cfc59d9091cac352e8dbb226416ea5c9a75e51124a1bb5cb514a78c79b13da1c03a85c020440885c3206012610000])) (.b 208 (.p [0x1680ba6d075962bbf13b5ab0be870ddd7adbf523c31c227c27a9349d3cf5ba2eeb928d679ef3a21dbc1dd811e8eae5f657867275b7fbe95b3314b3b6c61203a85c0285c121943205012860000,0x2720897c688bac777507d657a4ea12029acbedb335c752d6422c3f0739bc0e8c82d328c96687d3b1a5cc51203a85c0285c1285c6605012590000,0x8d1203a85c0285c1285c3205012010002,0x6e56203fa39a007f923fb849fd92a799a3f71203a85c0285c1285c32060152a0000,0xf891303a85c0285c1285c3206012020002,0x27661c0df33ebe7331fa5d6c9c1ae94e26775605031d29b2003670e945411c31f841bd1c04e8540285c121943205012580000,0x1fd5243100ddeeae0a9d8c5123287fbe325c2edd449f803ef17a2676d42229893ac6512f78dca989d68e566c3cf6233bdfe462beb4e7b1a90d5acc17d9b08cec95cf794675fa99c71c04e8540285c1285c6605012a90000,0x8d1c04e8580285c1285c3205012020002,0xafb9e8514833cb924da4dfedcfe12541d1578a79f3966ba1c04e78802094121943206015390000,0x605e12c9bbce288a1e77ecf6d86e1ba9eefa1595ea63e03d44c5f81ece38c82f644d2bdc3c883a974225647d0fdc01cb6ddc61c04e7880285c2619432060156c0000,0x641c04e8580285c121943206015020002,0x2f5a901d74a9b57db1a7c4e574bcbbe6084d1033b21e64061827f8f9828bc1d2812920194a6ccf9d96b1794cdd95ef202f24e1780af60b5ff85baefdc6d526283309bc780dffdbca01f9c3b2cd31c04e8580285c1285c6606015af0000,0x8d1c04e8580285c1285c3206015010002,0x3c891c04d85c0285c1285c3206012030006,0x6f1c03a85c0285c1285c320601201000a,0x641c03a85c0285c0885c3206012010010]) (.p [0x591c03a85c0085c0885c3206012010012,0x8d1c03a85c0085c0885c1806012010014,0xd25d639e61c03a0040085c080c41809419070000,0x1586ac02eb16d005ec341477061681dec2139a20936544ec1f29eaa1c03a7b002044080c41809419430000,0xbf64607478fb1148490217f10bdfe31a0a918ffda365c7e2811c45525852abe86001edd68ddad1303a7b00285c120c418094195f0000,0x4911a3176225b8ad75b88d37ec5c4eee5e2c288aed6bd0694c97efac1081fb8e4e60e14a38c3f5275dbddecc940917bc1c04e7800285c120801807419780000,0x11494fe93008e3375e3464f6373d7b04937c417c4f265fd51142ec00f4b36985a29396de6695d216a25b3036e94d0bb7414bb2283e87ce1c04e7800285c120c42107419830000,0x8d1c04e7840285c120c41807419020002,0x8fa8255439307a259ef873447ec20454e5525cd8de3978b8b82aa08ab2df84c77637b0863f96ddd01c04e7840285c120c4180941e610000,0x3c891c04d7b00285c120c41809419030002,0x6f1c03a7b00285c120c41809419010006,0x641c03a7b00285c080c41809419010008,0x591c03a85c0085c080c4180941902000a,0xa9df720406666a44fa24310031ad4f205879189a6ea013781335a4b2fb7a6f912538080e61c03a0040085c0885c3209419460000,0x2583f22aaec068788e64de66dd26ac1eed3740f3ebf2a15f773d5b980964d7c62b53a847d30ccea50a0b162a60ff7c4d91c03a85c020440885c3209419750000,0xe436f762dda13d7fb84ab9c5d5570bd6f0fa555057d8b69316499e8b6f3b39771706e1dbad578d4276eb1839c63f7646a2fbbeab2c13996cfb5f5e425d0d3c558aeabb65a1e23653ece87a81c03a85c0285c1285c3209419ba0000]))))) (.b 336 (.b 272 (.b 240 (.p [0x641c03a85c0285c0885c3209419010002,0x591c03a85c0085c0885c3209419010004,0x8d1c03a85c0085c0885c1809419010006,0x841c03a85c0085c0885c1809412010012,0xf631d43a85c0085c0385c180941202002e,0x2ec39adafa081de44d27afee57c6378768300085c0e85c2d05413220000,0x2459be25b69b844581370c3fbc567d3e4ecab4d3f33099008c94db82f855e77cd57b19be3787682c0085c0e1742e06416580000,0x8982e0c47ece9d29a76293a3496e60c5d023ab88f0261cba3430c0c165e1a08a2fff6f0159abc608a86f72c5dc2b047340649fc42787682c0085c0e85c5e06416740000,0x2706da4d4b8e42b1f27236e48d1ad8883447748901e4158a6aee6ab256e2b25648e1ed0118f9459989dcdac53789f82c0085c0e85c5e06416600000,0x6f3787682c0085c0e85c5e06416010002,0x978c378768300085c0e85c2d06416030004,0x3cd8b598768340085c0685c1806413050006,0x68dbae9eb77d9aad12bcd057af5c850a44ebbd4a29d33a39fed80934078f3e81b2995200c9d959876834000340685c180941a5e0000,0x2481e53dc760040085c0e0c4180941a060000,0x1ebb12ca746f9d1a5d8915928ce644bbdab5761eeb49c9e248db9816c2e86e847a390407e350dfe05aa4c8a473cdd37ae6c4a368fc3bf931c9bd6f70f4d5735e5ae2022b8555455131a06bf2a0767600285c0e0c4180941ab70000,0xe64780f6740fef985fe796dcda65b17550251fefca76653d651941dd4550bf509d60a8ac490bc3dca97600285c0e0c4180941a690000]) (.b 256 (.p [0x6f3dc767680285c0e0c4180941a020002,0x4c58598768340085c0e0c4180941a030004,0x2828e63087e004000740e85c320941a050000,0x2f73466f70ec626e1a98270113418d5c82b5513075b7ad29784fcb0fd0fb3aa28c8822f812fffba69d0f24aeca05fa0f06de6c3971849ab684003db1ed434af90eee547adcf55bda3087e64c020740e85c320781aa90000,0x1a50c43df5a94013f5f47208d6739cfbed1321d75d5e239c4d61cb4a48b8eba97da47464b7d4f68bd83087e64c020740e85c320941f5a0000,0x843087e64c020740e85c320941a010002,0x593087e828000740e85c320941a020004,0x39d23087e0040085c1e194320781a020000,0x137bb448e5c080b33fd085692183347b63c36ae58f742274fc41b52efa43ef5c625c7e74c020f41e194320781a410000,0x4dd47d6ac91e28694459ed3ef96d7a5495c90d9eca8a19f015efb78b7ce3774674c809868bcfb99d735a069d55d589f359ab3c725c7e74c0285c3e194320781a790000,0xf632607e74c0285c1e194320781a020002,0x5dac14e7b2c892cab9a667460c27fb776cda4b7f66f76457f9731e386317cc3037c7132992730b3dc131a38c99091c864bc9aaa16670c9d74d862bc3089974c0285c1e194320781a890000,0x6f3087e74c0285c1e194320781a010002,0x593087e8240085c1e194320781a020006,0x39ed11b7618abd691c173405deb918d8f04eaeda65cf01a83dc624871e7c3a69299150433b8ecfd9bc63087e8240085c1e85c660781a640000,0x8d3087e8280085c1e85c320781a020002]) (.p [0x39d23087e0040085c1e194320941f020000,0x2a4d9f4d3355af4302334ed97d2a481a2f0f15ead2607e7540285c1e194320941f2b0000,0xbf4fcffda52a3e9335b8ca721c312e5afb685aa80e6083cbe6bc0dda7b23c917d092e19a10ba17b760b932f0ac3089b738020f41e194320941f5d0000,0x20ed1a862756d71bffa2e853feb376ec8fcd593a5898d0d883ef73e96870a4357cbfe39f327af97a92e5cd8d9792ff63089b7380285c3e194320941f660000,0x3269308997540285c1e194320941f030002,0x6f3087e7540285c1e194320941f010004,0x593087e8280085c1e194320941f020006,0x3c04c736877629b11daf61ebb7fc76b2026aea5cd777a710f1d33087e8280085c1e85c660941f420000,0x8d3087e8280085c1e85c320941f010002,0x843087e8280085c1e85c320941a01000a,0x3269310768340085c0e85c320941a030014,0x79ff1dcadb64756b5e80fad08cf52dd02d3f15d85cdf1d5bdcccf4a90322aecd57f62b289bcd95d442edeef5ebadc444bda598c5800000740e85c320941a780000,0x27e093eecadf4f09a80c9d2fa2787e9a0646a0a56d657329446eafc9fa9225d8227c2f4e0c3b44f46a236ffb8cc8ac0a183faa0606843413e6ec48836b7c43e0c57f40085c1e1f43e0781a950000,0x8da29af5dc95bb282a9a1122e3c780aea70c2a2f3f04d846274ec90f9b1496a831851f58fb34f50f27666a62bfe3a6a3a4febbcf1d06757ef2cdb899521818479b87361276096e37c53e0c57f40085c1e85c7e0781aa90000,0x8d3e0c57fc0085c1e85c3e0781a020002,0x6af0a3c1b84302919a6a30fe9e02a7babb275ad775f9af33786b0f55c5504f97fc0085c1e85c3e0781a490000]))) (.b 304 (.b 288 (.p [0x1da73598c58000085c1e85c320781a040002,0xddad4598c50040085c1e194320941f040000,0x997a70d2deec01f0504d1466a3d3c5efafa5a2d092853ca4b6c774681dd2d8787172dee968d05284ca4a16e4845ff324f23a191efad3f4c570c020f41e194320941f730000,0x6d44e865818069400a844c54f808fe2d590a9214489a05d3c85b0e6b1cff41eb956354d958751dae64448ef3880878abf4e3ad564b5d9df810fc95d8ba02f96bf3f4c570c0285c3e194320941f9b0000,0x643f4c57140285c1e194320941f020002,0x59c6cf436b510bba2d7d0ef1b977a036382e1af60f01260abf834a7fcbed8c3c7951ed6c2cdcb97b3ed1d1c357e534d04a97844650f119694220e14799fbd598fe7140285c1e194320941f9b0000,0x6f598c57140285c1e194320941f010002,0x59598c58000085c1e194320941f020006,0x1ed43f4c5004000f41e85c660941f030000,0xee5069900b92cbdc6ae1b317dd142cb03a014e4892f5eebeb579414dfb1483c60be57c404937866ee352927ddf9cd178a9dc13574ca9a56706b8c63f4c518c020f41e2d0660841f790000,0x3feed589bf63787290a830101cb0dfb8a8c4f1b250acfbbaacd40a1841d685f79f288d9b349d2ac3f4c518c020f41e2d06609422510000,0x843f4c5638020f41e2d0660941f020002,0x431e8b3d93f4c5638020f41e85cb50941f0a0000,0x8d3f4c5638020f41e85c660941f010002,0x593f4c57f8000f41e85c660941f020006,0x273fd7c8ff520e1c73f4c57f80085c3e85c660941f140000]) (.p [0x643f4c58000085c1e85c660941f020002,0x1ad6d2598fe004000f41e85c660941f040000,0x494ac0fdeff4010a4a94b7a5e135b3c9b852d2d97166b8c4450fe178020f41e2d06609420360000,0x1649e948c79bb27c0d77b0be04923e0e0d2972b4efecbc9695172c6331bab407f520312f4020296a1fcadf9e461e20e5ac48c43e9f1f223fa564dd6cd700ef87f59915178020f41e2d066094209b0000,0xc75598fe620020f41e2d0660941f030002,0x5aaf2ada598fe620020f41e85cb50841f090000,0x2b111da450fe620020f41e85cb509422080000,0xc95e8911264267636225221020695deb95f511fd692e750a8f8b03d7cf023aaef50128e83f230578b6848e997a5251c43b5826b173366d087a0731da59915600020a01e85cb509422960000,0xbc549d1520c020f4293d4b509422030000,0xbc54fd281e4020f4293d4b509422030000,0xbc5519401b8020f4293d4b509423030000,0xbc552947198020f4293d4b509423030000,0xbc55314b178020f4293d4b509423030000,0xbc55394d160020f4293d4b509423030000,0xcd5994f148020f4293d4b508c23010000,0xbc55414f148020f4293d4b509424030000])) (.b 320 (.p [0xbc554951134020f4293d4b509424030000,0xbc555153124020f4293d4b509424030000,0xbc555955114020f4293d4b509424030000,0xbc556157104020f4293d4b509424030000,0xbc5569590f8020f4293d4b509424030000,0xbc55715b0ec020f4293d4b509424030000,0xbc55795d0e4020f4293d4b509424030000,0xbc55815f0d8020f4293d4b509424030000,0xbc5589610d0020f4293d4b509424030000,0xbc5591630c8020f4293d4b509424030000,0x94bc6b94081589534c6218cc9767a5fab31f302b9d8e1a71c7bbda7b3fbe6bb4494cd98dd18ce83085ffc2d5f0f0103251f1a31deeec9d9069526dd8cb4ee67701cc9a3223f73b003808913ec0e2032b623a935fe75f0ad9599650c8020f4293d4b509424c00000,0x6f599630d0020f4293d4b509424020002,0x6f599610d8020f4293d4b509424020004,0x6f5995f0e4020f4293d4b509424020006,0x6f5995d0ec020f4293d4b509424020008,0x6f5995b0f8020f4293d4b50942402000a]) (.p [0x6f59959104020f4293d4b50942402000c,0x6f59957114020f4293d4b50942402000e,0x6f59955124020f4293d4b509424020010,0x6f59953134020f4293d4b509424020012,0x6f59951148020f4293d4b509424020014,0x6f5994f148020f4293d4b509424010016,0x845994f160020f4293d4b509423020018,0x6f5994d178020f4293d4b50942302001a,0x6f5994b198020f4293d4b50942302001c,0x6f599471b8020f4293d4b50942302001e,0xc75599401e4020f4293d4b509422030020,0x6f5992820c020f4293d4b509422020022,0x6f59915600020f4293d4b509422020024,0x9e87d188ddf4f9a335f813cb64df6161c31d237d9d86a04c59746661fe4130e8f7094e92e553d281b6a2c52e15ff8d083afed90741b446da59915600020f42985cf609422910000,0x8d59915600020f42985cb509422010002,0x6459915620020f41e85cb509422020028])))) (.b 384 (.b 352 (.p [0x6f598fe620020f41e85cb50942201002a,0x84598fe620020f41e85cb50941f01002c,0x8d598fe620020f41e85c660941f01002e,0x59598fe7cc000f41e85c660941f020032,0x39d2598fe0040085c3e2d0660941f020000,0x15c95ccbbda6eb5da311a3c6598fe6e80285c3e2d0660841f1c0000,0x46d4c4450fe6e80285c3e2d06609422070000,0x2478b72dcbe3f83ec2d7b862e26dc83da18d022576a7cdf968329f68cf7b2cb2badcdd68d29944e66e955a3d935ac3b3ed535d319442e9df017657a7b599151b0021f43e2186609422940000,0x7ecfc53a205bc27160c1c1d70edc3d2eccbd25edd40bdd7a6ca3e1c742155c112e1d1bef8437e0c3b9f3d816d52a1bdd99a7d599151b0021f43e2d08708c227c0000,0x7ff3d755c549d151b0021f43e2d087094240c0000,0x2a6ae6cf2c00620426b966724c524bec0c8311bb55eb9e95f3bb84cc7ea1ff26ec0c450537c599281500214c3e26487094245d0000,0x11f48ceea3c57031d3cc18243aaaf0d0654dec659c6e1ad00c12233f2584a847b325290c1ee247df21608922148a8dd4cdc77232490fd5febc0b7726d7c599281500214c3e2d09a094249d0000,0x8d599281880214c3e2d08709424020002,0x2125b58c64fd28188021f4542b887094240b0000,0xb349c81ab2a8d001e36ca5c1048d3114b382168221ddd1f33c4c7f88fbcff9fa2a606040da8ab59e4cd10451cd1d537a5994015c021f45425487094247e0000,0xa1582adf611ecb3fc0e385646c91d2126fcf73268fe2334ef37d69e84a159dfe2fab74e36f13125193c96e18b1f391805994015c021f4542b896094247c0000]) (.b 368 (.p [0x8d59940188021f4542b88709424020002,0xb7159928188021f4542d08709424020004,0x64599281b0021f43e2d08709424020006,0x6f599151b0021f43e2d0870942401000a,0x84599151b0021f43e2d0870942201000c,0x8d599156ac021f43e2d0660942202000e,0x122eb5a8b9ad7a68ed221c3aff03a214c76a6b8c3ca39e837206829d0bb2bc599156a80285c7e2186608c22430000,0xcd88cf85e8c9c749d156a80285c7e2186609424130000,0x3a36b88afdb1792187d95149453e67c3f98984a7b9d09bfffc1bcd25e724fe92625c9108c5599281fc023247e1d06609424650000,0xcf855766a676d763e4c8c4538e52acd78ae272d63f973518a1c16e77d2fdc1d1a98f8436c66385dbcd62cddd343eda9fc24723eef5679bc53f4084168fde7d599281fc023247e2187509424aa0000,0x8d59928670023247e2186609424020002,0x6a48afe5ebcd37d8bd1a81cee283cc3bc558187c35abd599286700285cca2186609424400000,0x64599286a80285c7e2186609424020002,0x6f599156a80285c7e2186609424010006,0x84599156ac0285c7e2186609422020008,0x40b91834ac749d156ac0285c7e2d087090220f0000]) (.p [0x1de8b1e8e7a02566c9a033c2c82e70f0c1658adc58449b8e64dd84c7599286740285c7e2d08708822490000,0x39d688b261b2d495af64aa89794c11b10c9f8337d32bdd160649e9aaddd35b362ac671510049b0555d55c433aaeea57e8121f76e16f6cb4e4fd927f59928200022fc7e25c8709023a30000,0x7ff3d755c55093b200022f87e2c89808c230c0000,0x59bba61d6df61a02e5f34c1352d9d371bad56473a7a1f974b54063026ae90da8289c596d7d599431bc022547e2c89808c23600000,0x9422f2e6d3e1c74de837ed1714e53561b8b284603bae84e5aa62fb3d17e3ffc60dff4ccc4a8f753b13ee822acd4b109dea3d6aec52ebf9bbc7599431bc022f8962c89808c23980000,0x6459943200022f87e2c89808c23020002,0xd87359928200022fc7e2c89809023040004,0x8d59928674022fc7e2c88709023020006,0x3112c3550f2e199f82dfbabe570c937bb369216f2fe1cba2fc400c55992867402444c02c88709023420000,0x46a599286740285c7e2d08709023030002,0x84599286ac0285c7e2d0870902202000a,0xc75599156ac0285c7e2d0870942202000c,0x8d599156ac0285c7e2d0660942201000e,0x64599156e80285c3e2d06609422020018,0x6f598fe6e80285c3e2d06609422010028,0x84598fe6e80285c3e2d0660941f01002a]))) (.b 416 (.b 400 (.p [0x59598fe7cc0085c3e2d0660941f02002c,0x627e075b6e93b7602fa1bc7450fe7cc0085c3e85cb50901f1b0000,0x106184e5cd9eb2b24040960b0f6e5f0918bc22a34f47b8e8757f4256de887d6007e278233d3d3e0bff6ed2095fd9a5f2f026089962d9cfd87e1b92d83cd1f0c98da101e616dba9138afd420c1e6ed4ebc11700841d859915798001f43e85cb50841fc80000,0xd3599150040085c7e85cb50841f010000,0x39d2599150140285c7e3d4b50841f020000,0x29bc549d156b80685c7e3d4b50841f060000,0x468f1c6c5599286780685c7e3d4b507c1f0b0000,0x1a67f54acff13c78c32ce71109ae028ca0418ccf51d2c889421c659928678063247e3d4b508420320000,0x2bf63c4e022371372c104683a77107cb783a3cdb754eba892667f9c5fb269efc6d0a8e619cd0539a764b56d79ba6bc599286780685cca34cb508420760000,0x132061b4fff6a42fb595663ead7b9a4f8f05a7dd3f60678584025316f2ff7743ce674442a455f75f843546d746576a898076a1ed0ed3324c5599286780685cca3d4d4084207f0000,0x8d599286780685cca3d4b508420010002,0x64599286780685c7e3d4b508420010004,0x84599286b80685c7e3d4b50841f020006,0x6f599156b80685c7e3d4b50841f010008,0x59599157980285c7e3d4b50841f02000a,0x1ca56555c449d157980285c7e85cf60841f0b0000]) (.p [0x1954110d859928770023247e85cf607c1f0a0000,0xd3599280140285cca85cf607c1f010000,0x2a38da2c6599287700685cca434f607c1f080000,0x12bc0b906d07d9c1bb9c4655c09fc38cf9ff482f7b8c844439ae4ab2540c5593accdae5cf86ac2f930b24e4e9fe3d247c19951a085359bc84021558e2e1c989e9cb8f6b93b141050faa1461737491d01fd3d4497574ea84463e160378dabe599287700685cca85d0e07c1fd50000,0x8d599287700685cca85cf607c1f010002,0x59599287700285cca85cf607c1f010004,0x64599287740285c7e85cf607c1f020006,0x24e87bab105d39a600fd8b6ea9bf57ddba913ac333601fc4599287740285c7e85cf6084202d0000,0x84599287980285c7e85cf60841f020002,0x6f599157980285c7e85cf60841f01000a,0x8d599157980285c7e85cb50841f01000c,0x59599157980085c7e85cb50841f010018,0x645991579c0085c3e85cb50841f02001a,0xd359915004003403e47cb509022010000,0xc04c35a10c749d153c8023403e47cb5090220f0000,0x307f38d59c6599281e4021943e3a4b5088220c0000])) (.b 432 (.p [0x1e22088290c74fd281e4021943e3a4b5090230d0000,0x21c16ee7e95b6a8c35f9967ff359f92276b74af72eebae70dc94c25504ea80c13e581e77d162c68de4883cc43d6bc5a91503cc5599401bc021303e3a4b509023730000,0x361f6e592fa469a2ce3375f5a0fc95058129f512a77ac9b50317de2f3691ea9756c5d250557a3950a16266797fcf05331db6a0b828c234b673968f86387602e3ae63c7599401bc021944d3a4b509023a40000,0x64599401e4021943e3a4b509023020002,0x6f599281e4021943e3a4b509023010004,0x8459928288021943e3a4b509022020006,0x9f3e59c64fd28288023406639cb508c220c0000,0x5f06966ce754654abba9a23d523e5c39d5cf8c8a5419a2cb7b94c0eb7a82703ba375a0c940c415beb42c8561c4599402580234066330b508c22690000,0x1256a3fd0800491932caf66701df01477e5b371bfb279160e1952cfd107d99afd4dff7b310a2e80c1c590d23391804e2ec0104c8eb6674ce1c759940258023406639ccd08c22850000,0x8d59940288023406639cb508c22020002,0xb715992828802340663a4b509022030004,0x64599283a0023403e3a4b509022020006,0x117d31402ea35d4e9fa4c99065b9632e66014c26181771048d286d2c5599283a0023403e47cea09022450000,0x8d599283c8023403e47cb509022020002,0x6f5991579c023403e47cb509022020010,0x75e5991579c0085c3e85cb509022030012]) (.p [0x84599157cc0085c3e85cb50901f020014,0xc75598fe7cc0085c3e85cb50941f020030,0x8d598fe7cc0085c3e85c660941f010032,0x64598fe8000085c1e85c660941f020060,0x6f598c58000085c1e85c660941f010094,0x8d598c58000085c1e85c320941f01009e,0x84598c58000085c1e85c320941a0100a6,0x64598c58340085c0e85c320941a0200ac,0x6f598768340085c0e85c320941a0100ae,0x8d598768340085c0e85c180941a0100c8,0x64598768340085c0685c180941a0100ce,0x98835987685c0085c0385c18094120400d0,0x6f5983a85c0085c0385c18094120100d8,0xa905983a85c0085c0285c0a09412030108,0xc2ffaea665729632d8a891b1d5c5740aea612f1c53731d3072edd5983a84400014020540a85c26430000,0xb43fcb859cd51c1a520aae8b38a2aebee5efe61a1ab96a9b81c03a7ac00034060540a134263a0000])))))) (.b 672 (.b 560 (.b 496 (.b 464 (.p [0x5932df1c03a0040085c0e0340a13426070000,0x3a61230906a88ea01a5cb0b4928e7be718b88248d0848420f15553b18d5df00e0340a0cc43c88a180506bd53092bd1203a7a40285c0e0340a0cc26750000,0x46e3cfd84c4f0deaf3dffb7184a2f55833fc5d8355de05c89f0b9df9bf5a3affa9cb1203a7a40285c0e0340a134344d0000,0xf891303a7a40285c0e0340a13426020002,0xbf1ea9f1166ffe53b66cca29bfe18ed318209077e12ace5f78e2ecdc79e9abb6b880e11004de6bc9dcf2000d90c991d705a0e9796d6dba30bc1c04d7a40285c0e0340a13426880000,0x6f1c03a7a40285c0e0340a13426010002,0x591c03a7ac0085c0e0340a13426020006,0xd01c03a0040085c0e0540e13426010000,0x16478c1ddc40b2d0c54dd173c61fa864f45b29492445ed5524e7bd727ae427f9ca6564ae388eec41cb6ffabb056f835ead01303a7ac0285c0e0540e13426760000,0xa5b90d589b0f5c3e311154d20d554ee24ac1c04e77c020740e0540e0cc26290000,0x2be79d8d740e4ddc6f0e21e0c21263c0efec3170c33e1145669ae23d18d83233078a09839c5ad2e4a2765d6276c91110998d420d9f58b9a79035283c3410dbc1c04e77c0285c1e0540e0cc269d0000,0x641c04e7840285c0e0540e0cc26020002,0x1e4952562ae6365f2386c1b22f42244f243129758b86e79bb1c04e784020740e0540e13434370000,0x929882256c55428d18f8145e14a682552fde45eb7932ed11a7065c768a30cfbaf7aa10c28a65aec221378a7ee2b033cc4293287c33a9cf1c04e7840285c1e0540e134347b0000,0x641c04e7840285c0e0540e13434010002,0x3c891c04d7ac0285c0e0540e13426030004]) (.b 480 (.p [0x6f1c03a7ac0285c0e0540e13426010008,0x591c03a7ac0085c0e0540e1342601000a,0x8d1c03a7ac0085c0e0540a1342601000c,0x641c03a8400085c060540a13426020014,0x25f4455357f2e4a37f6a565294536137d12e941cfc263b9f66192c5698d9f51dc952901f2fdd1c03a84000034060540a85c4e5a0000,0xa12d509e9bc84fe6836fbf60f1b80e01c03a0040085c0e0340a85c4e1b0000,0x32ce188aab0b06b0c234cdb44cd50cdc9fd5baa321b99ddd1303a83c0285c0e0340a85c4e370000,0x15f9dbe81c04e78c020740e0340a24c4e080000,0x36df1c04e0140285c1e0340a24c4e020000,0x11fbe9bccd812128182087e03684558bc7f9d44221a9fdc8d614d3af600623c4f6ff4e828410d10f615e16bed19bbc1c04e78c0685c1e02c0a24c4e6c0000,0x153d5d99d45bad76c1aec3bd84dafb5383588724a175f7f3c2a34fb67496e28ca1c04e78c0685c1e0340c24c4e480000,0x8d1c04e78c0685c1e0340a24c4e010002,0x591c04e78c0285c1e0340a24c4e010004,0x641c04e8200285c0e0340a24c4e020006,0xad57642cb77a67516811e93aff01330f73505ef6b8d112d0356fb51f8cad89f1ab110bb79ebff75a30aa6758f97e162e8aa2ae81c04e8200285c0e0340a85c94750000,0x3c891c04d83c0285c0e0340a85c4e030002]) (.p [0x6f1c03a83c0285c0e0340a85c4e01000a,0x591c03a8400085c0e0340a85c4e02000c,0x169160c303521f4d8eeded1cfe4200e580795f57fa2502d0da28d343bfac8feb3ca49e2a6783550da9efc81c03a8400085c0e0540e85c4e6f0000,0x8d1c03a8400085c0e0540a85c4e010002,0x641c03a8400085c060540a85c4e010010,0x3c891d43a8440085c060540a85c26030012,0x3035b2af59905b24acb56fa6294c267a8a6bb13047e0f1466714a8ca8b30f9cc22682cf58adadb5fa3521be2bc7e7400085c0c0540d0cc266b0000,0x6488f4e1dc347affff5ecdc07dee4fe33b92bc7e740000640c0540d13434290000,0x33a6e02bc7e0040085c1a0540d13434040000,0x302de1a3c87c76f85e8bb99ce12dfdd42e1c292ad7e4da926ce5108bbfb36a86b504dbe2bc7e7400285c1a0400d134345d0000,0x3693879296dcaea546dbe912e920b23c3a47b53dfd8cc117a2949c46bc82bc7e740020d41a05411134343f0000,0x4c74dac7c648c4370449d8e266cbd3b2dabeb823f440f9ddb549a156d4b60809aea0eacc184db62f83d0773872db79e513a1bd5b57cb7d270f04409eba7f7064f94e7fbd87da58405e4527e272f48acc2bc7e7400285c360541113434b70000,0x642bc7e7400285c1a0541113434010002,0x8d2bc7e7400285c1a0540d13434010004,0x592bc7e7400085c1a0540d13434010006,0x642bc7e7400085c0c0540d13434010008]))) (.b 528 (.b 512 (.p [0x8ec882c0767640085c0b0540d1342604000a,0x5932df408b10040085c170541013432070000,0x1e173a4dd50e01f9e8cbc11b5c74eefc873389235076590f0c98bbf408b17240285c18054100f032450000,0x4476f7c129d186262f594df3a78fdfd62d22d77cb2be402693e5d23c0f2906373efd5760974c73e5d92cab7a026452c02d66b1847c495dabd02a6a004dbd6290e80e4aedc0f9dbe35cb17240285c18054101343da20000,0x376de389d969fc3e265d894ddf38059e30aad85fbc408d87240285c18054101343d330000,0x6f408b17240285c18054101343d010002,0x88b408b17240285c170541013432020004,0x75e408b17640085c0b0540d13426050006,0x26477598768100085c060540a13426050008,0x1631df2f3ad6d0635c958a14a57b9b7e0073ec639f272b7f549f2ac703f35833ab8f6c63f5c4ede117ef4ce25c3606d4dce54325f96dc5987681000034060540a85c4e7d0000,0xe8cfe29beee3e4a1517c344333a87f8926ccbf2c87e7e00085c0e0340a24c4e2d0000,0x51e4fe52c5610d31ed3b87d04bddf8adc343e9c2c18c336874c74c337bc844b4814f43c604419914d183e62bc127c66b31ad192637a7263fd91312943d10058af2af4196fb57a7cb0f7e67c89a6eab9be0dc2c87e7e00085c0e0340a85c94bc0000,0x3c892d07680c0085c0e0340a85c4e030002,0x32b5597a1f07463732d23e36dabad418bcdcdb823cb295d2a1195ff567bf94165d03a1a50d80ddf4a0e48d81959637c8424b580c0085c0e0340a85c4e7a0000,0x6576598768100085c0e0340a85c4e030002,0x89d40073defe31ee948414d86a223379777fcc30ebec8c8d7dc68951b1b1ab4b9bd2cbd795f711a3502a44986a1d5f1352bc2ae7cbb3087e758000740e0540e24c4e770000]) (.p [0x36df3087e0040085c1e0540e24c4e020000,0x36df3087e0140285c1e0400e24c4e020000,0x421f627bfd8a03de98fa101a405be1a849388915b83e383c4867e4bed2f1f764b79129c92607e7500685c1e0400e24c4e5a0000,0x72832ac551625426600ec92b669751ba8980bd304273e050ef51a8be2bb4342922a2281f8b063eda155c4425e71b3c99d581196b36a5b503b19c4fc8a18ab51dae4815da948e9b44fff1125777e8f3e1ca308997500685c1e0400e24c4ec20000,0x6f3087e7500685c1e0400e24c4e010002,0x593087e7580285c1e0400e24c4e020004,0x37f98f7991f3e9efda60dbf93d12607e7580285c1e0541124c4e1e0000,0x13a732bacaa35b9b2428324c41a0cd57ef7c946590cf82fbb4020d40da7b23a054f8c6ad285631941f66abe177122f88d0cc47a79bde3089b734020f41e054111a04e6b0000,0x1cc79561a2dd78c502be0cd6db805a5162eb4b68f2e036cb644cb3089b7340285c3e054111a04e440000,0x643089b73c0285c1e054111a04e020002,0x2e340553c6b0bf9920e702e97447d80dd25bc7778e20591baa12578c007630dc10ce3b93089b73c0285c1e0541124c69550000,0x3c89308997580285c1e0541124c4e030002,0x6f3087e7580285c1e0541124c4e010006,0x8d3087e7580285c1e0540e24c4e010008,0x593087e7580085c1e0540e24c4e01000e,0x643087e7e40085c0e0540e24c4e020010])) (.b 544 (.p [0x6d9563a5c099e8a8ec28b9371c44a059cf18402222356e13bc8ac5cab06dd62bc7fd13d6c49031a3d9e931dd6c3a155a80c8aeeccf2bf47cf8ba4a1b1e42ebfca3c4593b2780a2344fc06e6ca8cc65f9762fdbd48ee4124861ec33df3087e7e40085c0e0540e85c94d00000,0x3c89310768100085c0e0540e85c4e030002,0x66d3e642cc5004000740e0541124c51070000,0xd3d229a487fd8a9258402529f975498cd634ffb777fa1ba388a02729d5ff98abf5435bb54b063be953948e72b5ba3b0c50d8020740e0541124c52630000,0xb4c12ef5407be4ff906ae165ea89d555f2384878c57215fb2c6a7bcf2e4ff7ad38d8d6971a2f6f0743e01a895b43867d50b958bdb0135ec9428ed0d8020740e0541124c528c0000,0x7c7342cc50f0020740e0541124c51040002,0x3559598c5718000740e0540e24c4e050004,0x47d946dfd945612ebaf1d3e8ac32ae3059c593d0e3533c4f7c99035718d089eb208c0c48c4be598c57180085c1e0400e24c4e610000,0x36df3f4c50040085c1e0541124c4e020000,0x10505b8d4eb97d11f1ecb3f4c50e8020f41e048111a04e160000,0x7a758f67320d17e8f9e782dafc01eff3f6497ae48945f8fc1337aeee24bb06c9858b145543bc8eec8380c50e8020f41e054131a04e490000,0x289dd4fb55c2cf48ff08af2f8cf95c514c5106eb9bce666d15ebc0af94b26a360caebc83f4e10e8020f41e054131a04e4d0000,0x6f3f4c50e8020f41e054131a04e010002,0x8d3f4c56f8020f41e054111a04e020004,0x281cffd7b36d6bd21323e6e9b2945cf79cc45a3e35631e896486581b59a7c9f81519f1d89bd729d2e1c4bd3f4c56f80285c3e048111a04e6c0000,0xfaa78010b9621677e2f12502ea9f5b3bbfaf0de3b7627aabb5d719a915146a98a9eaf55e00b43657c1f7b5cc3ff1dd77c594339dd26fc179de5e6aead0764056b70ed1863781ca3f4c56f80285c3e054131a04ea40000]) (.p [0x8d3f4c56f80285c3e054111a04e010002,0x643f4c570c0285c1e054111a04e020004,0x804902450a626cc74f92711f1dbb1bd3f88462005244ecbb566eb4aa0fc799d1832fb060fea53b551ca3f4c5114020f41e0481124c69500000,0x180a315e1abe538a47b5b005739284dcf0e91b6ef3627f030d254947a6daa6beefdf380c5114020f41e0541324c69500000,0x17ca7edaca29e33f3f0fdca3c25be8140f856c9bcb4e2af652d3e02e50fc461084b671dff02259962a648717b3f9b048dbb67e3c2d8618ab89dad8bc56592bc83f4e1108020f41e054131f469810000,0xd5a0a0a544239f171630717c1017b2326ede94a54815f139d0cab316b5c63b9de7903c3daaa9eeb4373e9d8c6ecceecab12c67fac8d32a9e90d5f6c68c63e0b56fbbd5ec2bc042e0d544f0e03f4e1108020f41e0541324c7ea50000,0x843f4e1114020f41e0541324c69020002,0x6f3f4c5114020f41e0541324c69010004,0x8d3f4c570c020f41e0541124c69020006,0x3999c404977635eb0f0f506fe12de776a42c8091e2be4c6bd99bd6fcebaed10cc32e03f4c570c0285c3e0541124c694f0000,0x643f4c570c0285c1e0541124c69010002,0x843f4c570c0285c1e0541124c4e01000a,0x593f4c57180085c1e0541124c4e020014,0x36df510fe0040085c29054121a04e020000,0x20dade510fe0140285c29054121a04e060000,0x4d5baa85a630b73ac83516443d377c167a9149f5935301988b540bdd8ff91ed480ba4d29da80872febef47133ddca510fe6c40614c29054121a04e5f0000])))) (.b 608 (.b 576 (.p [0x425eb70f10ef1368962360a448fba5ee330c8b32c1b4d959ae74da00b97fee8bfb1531b387b708527b70a844d16b95306fe75730ebe510fe6c40685c54054121a04e7d0000,0x64510fe6c40685c29054121a04e010002,0x59510fe6d00285c29054121a04e020004,0x1d55c598fe6dc0085c1e054111a04e050006,0xdf450fe004000f41e0541224c69010000,0x8c025f99ebae7a4e40ef261da680866d6f81cc8450fe0f4020f41e04c1224c69290000,0x5e320d5429275163314f6c41e42e2e760012397ad33adb5d7200af4955b19618047734d2adf8a8f92260d36967e95cda1dd457132a302af20895dc9450fe0f4020f41e054141f469810000,0xac68d1275bdc189701d3ade7eeea5bb9f5b8fe78faf27a5a4aba32df414fe0d4020a01e0541424c7e390000,0x16bd4bf1a5bf1fcb2ce74a849f1b77c3f30358231b2e8ebc0db85b605e4ec37daf5f6dde8767fd3ea683e9f5f923800f21460f6a48ef56534f38c096f7a451060d4020a01e0541424c7e8e0000,0x6f450fe0f4020a01e0541424c7e020002,0x3a053e5f19e2ea9ff7885541c6d5bf85797b488fa97c0606d6408839ac8450fe0f4020f4290541424c7e360000,0x64450fe0f4020f41e0541424c7e010002,0x84450fe0f4020f41e0541424c69010006,0x8d450fe0f4020f41e0541224c69010008,0x59450fe10c000f41e0541224c6902000a,0x762c9599150f0000f42004c1324c73050000]) (.b 592 (.p [0x11447afa090bbbf103e0f441ecb599150f0000f42005414208731d0000,0x4552d42993803dfd5f7583a36b770f9da763e95e2a85b296a8b6be6e3071876c473cf6c8599150f0000a8200541424c83500000,0xd8f6a53dcaa2c837ab4f9e021affc640bce10a603529e3d7e3516c0907c196b4a64f737983ca709f22d8cbd0bf4d5474f737a599150f0000f42b0541424c83710000,0x64599150f0000f4200541424c83010002,0x84599150f0000f4200541424c73010004,0xa905991510c000f41e0541224c69050006,0x9776598fe6dc000f41e0541124c69030008,0x19497562b8f958e177b8da0adf8bbe6906028b5212e745bf598fe6dc0085c3e0481124c693a0000,0x368e6cdcd65d34a757cf0f18da880fed43668ffa16b79f537a3f84d86e5bd9fc9450fe6dc0085c3e0541324c69420000,0x18e0de599150040085c3e054131f469050000,0xd4c7491f29027f34e9c3364249a6afc70644d7a663a6c9a269ccb59915694021f43e054131f469370000,0x5a2050bf599156940285c7e04c131f4690b0000,0xaf4fbc49d156940285c7e054141f469080000,0x34b1dd68f8829d9bd9b289052bb1589d82cb078f1918b64b5060c4bd599286680285c7e054141c8694f0000,0x8f6cb4fd286680285c7e054141f473040000,0x312e93c1d4a381881664048672bdb5cdcd902f8b940688d23539d601cd577ce473ad2b66dcf859b4dd2ce34c62adc6f2c25d3fba019e1f6c6a360d5ce7da04eb8b330bd59940644023247e054141f4739f0000]) (.p [0x3034b6892e075db562dddbfbfa07f599406440285cca054141f4732d0000,0x64599406680285c7e054141f473020002,0x6f599286680285c7e054141f473010004,0x84599286940285c7e054141f469020006,0x6f599156940285c7e054141f469010008,0x8d599156940285c7e054131f46901000a,0x64599156940285c3e054131f46901000c,0x59599156a40085c3e054131f46902000e,0x36df599150040085c3e0541324c7e020000,0x3a69d8069dc959915150021f43e04c1324c7e0d0000,0xe58980daca49d15150021f43e0541424c7e0b0000,0x7fdc77dc3c40d946f8c79246add9008db75a103b8baa4c7e9e2ecbbc4591eb0298f6a78b60af377828fc51ecf9220cc2d63211225603c727b59928130021f43e054142247e950000,0x10ad00849ce2970f87d9db33eb7377a6e0ebded6f97db18ead094105040cba5e412a39a585422460818b84ccb6d7bbf36e2f192b22c8b4df0266b20bcb72a0634ac0a3a377a27c59928130021f43e0541424c8abb0000,0x8459928150021f43e0541424c7e020002,0x6f59915150021f43e0541424c7e010004,0x8d599156a4021f43e0541324c7e020006]))) (.b 640 (.b 624 (.p [0x1ced2d9e67aed2ffd31d5244a7c5e620eaf221caaaf86afd0e4c97193682d9c6a0b71604d8fba77d528d05bf4893f699b827e96428bfa3d93f7e3cce77977279d74d25ed1dbad1ff8e3555c5c8599156a40285c7e0541324c7ecb0000,0x64599156a40285c3e0541324c7e010002,0x59599156a40085c3e0541324c7e01000a,0x84599156dc0085c3e0541324c6902000c,0x6f598fe6dc0085c3e0541324c6901001c,0x8d598fe6dc0085c3e0541124c6901001e,0x64598fe6dc0085c1e0541124c69010020,0x84598fe7180085c1e0541124c4e020034,0x6f598c57180085c1e0541124c4e01003c,0x8d598c57180085c1e0540e24c4e010052,0x64598c57c40085c0e0540e24c4e020054,0x69619ef8598c5004000740e0540e85c94060000,0x7608edf6b6eb81a5239b234671c82dc598c55e4020740e0400e85c94290000,0x58f9c45d7a252090991fd8d0348ec9a526ae18c0ee98614f18eae43b87ca77bb439f9ccc1d62e159fa9146fc855640118190d2bf5a33540a7dddb4eec62ba26122df3e2696b3c1c6a3aa7976f8ad4f9545c33e8c9b43f102ecbd10e977d38a68df4489520016704075d9839db3f4c55e4020740e0541185c94fa0000,0x18d9b7fb7dc598fe148020740f04811380940e0000,0x55c3560ee85a4c336cdc598fe1480204c0f05413380941a0000]) (.p [0xbc3868ae0fd52e845d23615ef2415133c2989e0a5de3de96ac7750ec15ad21e7da1f45db40d32827c1a447b49e76365ffdb40eaf8b793ff79f8b6d66b894ed25c4a12a2559448eb6cca3fadaf45e562b515df215cc4a013538b7b0bf9cb450fe1340707414054132e894c50000,0x4ba3734066a3f4136075ba711012981b19205e4e076bbdd450fe134070741405413380bb290000,0x108a450fe14802074140541338094030002,0x38d66158cbabfeec62d1728a941be474d3295870cadbbe1049d4e927310c7ee1919b43fad9f05b52b019179568a729167e58d048ff7ee5d0192013cbcd1168ad1bde05cd504c28a0bef00ce0887565b61f04110617f5991514802074140541338094d10000,0x6f598fe14802074140541338094010002,0x64598fe148020740f0541338094010006,0x10a90598fe5bc020740e0541138094030008,0x363534d6fc04449c468610e69d58a1cd0883cfccd598fe5bc0404c0e0541185ce13b0000,0x1cccac844900d7d06f8640e19a17d215ea2ac1deb9bd6872df9e5f2f5e3db598fe5bc04074140481185ce1430000,0x7c43fdc9eaeda0614af6448d17bc9e49c16a351a950525518a057b848f85d1f4ce7df52c3948f415b1d32a51361e0e1ad971d994435fd070ba7d20d5d34f72ce12dd598fe5bc04074140541385ce1b00000,0x8d598fe5bc04074140541185ce1010002,0x1563598fe5bc020740e0541185ce1020004,0x84598fe5e4020740e0541185c94020006,0x6f598c55e4020740e0541185c94010010,0x8d598c55e4020740e0540e85c94010012,0x59598c57c4000740e0540e85c94020014])) (.b 656 (.p [0x50e1fbf0e7885db03f28721a95994d5497054fb4532bbe4f3bd90a5d4577c10366a6e8ff0dbb4162ca3f4c57c00085c1e0400e85c945f0000,0x4827e7392a6a1852089fc7ef673105b0ad6b0b798a9acb598fe7900085c1e0400e38094390000,0x20e0598fe0040085c1e0400e85ce1030000,0x1a03e64c8f0542f423fac9055492f99d151556307f413a93f5be8ddf28d1c21427923a6a4859172571e60d421d40dd598fe790020f41e0400e85ce1690000,0xb0c27886094fec8b9760379cdc9450fe7900285c3e0400e85ce1210000,0x3b7b4b690cb5991575c0285c3e0380e85ce10e0000,0x16114c37c150f9c394f4ac9ca159765623a8580eea40f192be7660ddca599156bc021f43e0400f414e1380000,0x4793b1d73ad2364881248e14e264492f31e8761f0e9e94c7304d3d3e0dee0646cc9752d5b44503ef80bf2c4482b0ff73a51d9b1b53df3c4a8c9599156bc0285c7e0400f414e1910000,0x645991575c0285c3e0400f414e1020002,0x20e0599150140285c3e0400f85d06030000,0x1a569c7442bf28646b7672d3f1fb5dce325c6850e46a21c8ba8cc19f712db5511619da7c6409f61c4c3337296db5991575c061f43e0400f85d06650000,0x764138e1641978f41470e13dacdf6bac93b230bbb432bd266041a7e021197ce6e3051f2654eb9b52d79eb9d6a1d87753b3275fc95991575c0685c7e0400f85d06730000,0x645991575c0685c3e0400f85d06010002,0x595991575c0285c3e0400f85d06010004,0x845991575c0285c3e0400f85ce1010006,0x8d599157900285c3e0400e85ce102000a]) (.p [0x6f598fe7900285c3e0400e85ce101000c,0x64598fe7900285c1e0400e85ce101000e,0x59598fe7900085c1e0400e85ce1010010,0x84598fe7c00085c1e0400e85c94020012,0x6f598c57c40085c1e0400e85c94020014,0x27303329d3532ecec1f36a5d224e77eda4e53ef8b47fe21fd20ab1f34707277b3d33f31cc83f4c57c40085c1e0541185c94520000,0x1b01afee30237df31891d3983dfb7708f755603389540cb7cda57d9e9a8bfacfe32d97814a281a750e5799e529467b00fbeca5429f4edb12ea701dba26de7d598fe180000f41e04811380949c0000,0xdf450fe004000f41e0541338094010000,0x402d1a0738cf5eda3e5c38ca7db4498993a22701641f0a54b0daf78c53ae18c66d22c347f90c262cf10999fbaf3b5672d562a50a67a88b9c0d57d321614a95c815ef5d08a6e33ec3ecd9166673782b95ea27872fbc833cee0854519fea717d450fe118020a01e054132cc94d70000,0xc4263660d6fcf1ed92b8630f046e8f880100c3e500a09ecb450fe118020f429054132cc942e0000,0x64450fe168020f41e054132cc94020002,0x4a59015c9450fe168020f41e0541335cb40b0000,0xa8b450fe168020f41e0541338094020002,0x59450fe180000f41e0541338094020006,0x16a22496c9599150f4000a01e04c132e8940d0000,0x206babe8cb15f71c66c7dcc558ca8c182ad6eaab6ab8bcbbb954b2bfda23d5dd9563103ae747533b1c9ebae1917a02131220759be38d3bd791d698ae68db999f525a49dc3b90dd5dbc949d150f4000a01e054142e8949d0000]))))) (.b 784 (.b 720 (.b 688 (.p [0x28e1cf86ef4afa9080d94b20c5c18b59b961c48ffb5de686de43bd4d149d12bdeb0804b76253f883d3cb99d3f53db0eb8e3a62316ba233a7d599280f4000a01e054142e8947f0000,0x6f599150f4000a01e054142e894010002,0x8d59915114000a01e054132e894020004,0x1513bf79057244a2e89b676505e208c5dc959915114000f42904c132e894200000,0x1934b05636add11b9781d7c583fed39c907e341a6950de8735b609ec949d15114000f429054142e894390000,0x981beef16396bca51665de5b1a71b2d45d9da73f1fceeff1530610ffb9ee11689841650f3aac1732e1277d642a8271ccad77e599280f8000f4290541429494780000,0x20b5ecc531914d23f7403c7314f5340bf225a1119d2422f99df398f9883dd92ea66fa3e38d98629f22f4517199d00367d599280f8000f429054142e8a67a0000,0x8459928114000f429054142e894020002,0x6f59915114000f429054142e894010004,0x8d59915114000f429054132e894010006,0x6459915158000f41e054132e894020008,0x30813b8c548ded93f23ad433813973fe7bdc42f03040fb7f4df1f00d0800eec3d25fe67ef10897ceaef59f067b66c89859915158000a01e05413380bb7c0000,0xc33bfcb49d15158000f42905013378bb0a0000,0x9115fd4b4e6e7c8c562e252acce31733720784ad555de3d3204a9fc27d540f89071c88b984b32667290e41dfb1a7fd13163086e9e14f877f59928134000f42905013320bb8b0000,0x52b236ed42834c0da070a6ecf51fd7ed8002c98480d47c50e2a390bcabf1ca3109159bdfc9c51bb35311b33eb9e7facf468d88596a492ba5688d2691c6d6e9ad2113fb56a174e9b56d055ab8259928134000f42905013378c9c00000,0x8459928158000f42905013378bb020002]) (.b 704 (.p [0xb7159915158000f42905413380bb030004,0x6459915158000f41e05413380bb010006,0x8459915180000f41e0541338094020008,0x6f598fe180000f41e0541338094010016,0x8d598fe6ec000f41e054113809402001e,0x36df598fe0040085c3e0501138094020000,0x2a7d90fcb450fe6ec0285c3e05011380940c0000,0x10d2f0aa0a8d52c8599156a8021f43e048112e894100000,0x1dd42ca49d156a80285c7e048112e894090000,0xbd6bbec886f345e349769f309315e83727db0dc2bd599286700285c7e0481129494390000,0x12baaa1d6f6ec05d89ca8bbaf96ce54997128efb370b970d2d98d209435397fd64fd476fe665bdfa71544d3bf75bfd3c37bdb2b71a6d35af35aa51f470f83ba45f442f3899aa35ca5ca876c2bd83c16b0f92c7c8599286700285c7e048112e8a6d60000,0x84599286a80285c7e048112e894020002,0x6f599156a80285c7e048112e894010004,0x64599156b00285c3e048112e894020006,0x28ec849d151b4021f43e04811380bb060000,0x852e18ecb59928168021f43e04411328bb0a0000]) (.p [0x4caa988ab6714d54368f7707f9d72c071f6de5562b6d3bd1caf4585d3f50b357fffd56a112890d040acfba3058f52de0222a92df67dbd3f1bc6fe85521911ab83e07df2ff28159928168021f43e04812328bbba0000,0x8d5992818c021f43e04811328bb020002,0x13e5f52df947de450423b89f2979626767aedf845fc19a6211c6c18d9e889384239152087d5992818c021f43e04411380cb5c0000,0x211e5e7c0db023dc8fb8186afcee2a33d4d5e0aacdb86b80887d40a4c9d38abba5e605ffe03b4bd1f7dc9d0a3f64c85079ccc62bcdec3e4e2f7740e4f3e13b04cb9ac21db78189bcb5992818c021f43e04812380cbac0000,0x8d5992818c021f43e04811380cb010002,0x84599281b4021f43e04811380bb020004,0x6f599156b0021f43e04811380bb020008,0xb3f2a6ccac94b5186b00285c7e04811370bb110000,0x5320c54bb4f7b8d3d299b527db5767425cb7e425ea193739ee684dbf5360222373e7b5992e6540285c7e0481131cbb5e0000,0x1147f23d242e8ad8efdb1fc656c3ca4fb5389bcfda48966e8c3ead11f539a251575dc12a34c1073eea01d4437adac85992e6540285c7e04811370c8740000,0x845992e6b00285c7e04811370bb020002,0x7c73599156b00285c7e04811380bb030004,0x64599156b00285c3e04811380bb010006,0x84599156b40285c3e0481138094020010,0xdfd14cc849d156b4022d83e05013304940d0000,0xe21580bbd957db0d2bc6273bb1523b285664462c32cde1a319ce5517700e9e7d298ba7c5992812c0217c3e0501329c945e0000]))) (.b 752 (.b 736 (.p [0x11af81ae571f095f305ea9590a3796be47b47f802cdb0de5a9c63fa8c748ccae9740632c5fa89ae0362e6321ecf661daf5769dd8511815992812c0217c3e05013304a8880000,0x84599281c40217c3e0501330494020002,0x25709f7b2871ba741066288f436dc2cdbcbc91a133d83f1e85b18a55a87fa8b40f534fd235e355dad8dab6df047c4fdbd6ff74b98a9c79e9e4f595d880b48bbadf14eccf23b7e599281c4022d8600501330494af0000,0x64599286b4022d83e0501330494020002,0x6677599156b40285c3e0501338094030006,0x8d599156ec0285c3e0501138094020008,0x6f598fe6ec0285c3e0501138094010020,0xa5b598fe6ec0085c3e0541138094020022,0x64598fe7940085c1e0541138094020024,0x121e0598fe004001d41e0501185ce1030000,0x40dd5db450fe5d0021d41e0501185ce10b0000,0x27a622b084706615de22d080dab935b06584474aeb865a13cbe578c687a3878f53aeaa42159a32d988a1d9fa1936599e97db599155a8030c01e04811414e16e0000,0x1fd620bfd0180905b1842be80b945954217a83a32d3b6c82256da6a2895adc599155a8030c01e0481185d065c0000,0x84599155ac030c01e0481185ce1020002,0xe33a18eae02933a2261cdb57f7fa4cd5b6cffe8a4b8fed7a75a304f6c1addce2ef70fba9a38e7f06dfb331101ed50ee0aa470d343dc0ef3d049b0b3bed099b5e940dc599155ac030c01e0501385ce1b00000,0x1691599155b0020c01e0501185ce1030002]) (.p [0x103799c949d155b0021d43104811430e10b0000,0x776c0a5e594838f422e02e3435bd75374b8a4c35e69fa38e26475d3ce1dbff00c9dd6887c31bf1b4d6b5bc9ac9599281d00211431048113ece1740000,0x1314dd3cb4fd281d0021d446044113e4e10a0000,0x9b131ed4d62654607a42df2aeeb927a764e7057358ff6727dc75cb85b7a1b304a167c6d953639225f8b3486bc029c53f10ad64cc0b3aab9cec52dbca599401a8021d446044113b8e1930000,0x67adc9328f5c489153335a9cd404a423166b7c6aa111bcf27046250a746789deca599401a8021d446044113e4ef4f0000,0x84599401d0021d446044113e4e1020002,0xb71599281d0021d446048113ece1030004,0x645992826c021d431048113ece1020006,0x1faba5c37710c3ad07afc5ffa6afee9f1c09d4e36f03aa2713ac95992826c021d43104811430fc3a0000,0x84599285b0021d43104811430e1020002,0xb71599155b0021d4310501185ce103000a,0x64599155d0021d41e0501185ce102000c,0x6f598fe794021d41e0501185ce1020012,0x75e598fe7940085c1e0541185ce1030014,0x84598fe7c40085c1e0541185c94020016,0x6f598c57c40085c1e0541185c9401005a])) (.b 768 (.p [0x8d598c57c40085c1e0540e85c9401005c,0x64598c57c40085c0e0540e85c94010072,0x84598c58100085c0e0540e85c4e020088,0x6f598768100085c0e0540e85c4e0100e2,0x8d598768100085c0e0540a85c4e0100f6,0x64598768100085c060540a85c4e0100fc,0x84598768440085c060540a85c260200fe,0x6f5983a8440085c060540a85c26010112,0x645983a85c0085c020540a85c2602013a,0x26c0f21c03a004000140285c1613426060000,0xdf2bb2c85ef745575d813e14a4f1f2f9e3ee645f0c26bb1c03a6c002014020b41613426310000,0x4eacaaf3f3cdad7cc4c0dfbf7ff71b2054811f96aa9b205c41b1baada1c03a6c00200c0285c2e13426470000,0x8efb79ea52401c72ec7b324d6c6fd013a2fdec637bc6eeecb89f68092709b787b65c8bdf1709f375a62be0e6b048dc6ccdd36da1c03a6c0020140485c2e13426750000,0x641c03a6c0020140285c2e13426010002,0x8d1c03a6c0020140285c1613426010004,0x591c03a7b8000140285c1613426020006]) (.p [0x7413074c9ed2c1766d4e51cf7e327d26a0e671c626cad5de19076abab4a8a50d48dd9811ae70ec28d6c62266edd1c03a7b800014020b41685c4e6a0000,0x2d703eae58aef06f5925ecc6f11bbd8540ada9b5f949ec9ceb3cb7d7a341bf7b630eb2b4d1347aede815420ee79d039416ac746af0286febeca90f716986eb194d89bd52e1e40e0efecb9f21c03a7b8000140285c2e85c4eae0000,0x8d1c03a7b8000140285c1685c4e010002,0x3c891d43a7bc000140285c1685c26030004,0x3796a260fd303c247f56b86c8aa9cc033bba86bf81bd995913c9528d9048a94de1b1cc0fdb8d7b28f74a41a7036f3908b1d78d76c09d959876778000140285c1614428880000,0x157bc0ca4a79146ec4da342aa7506abafa1f4c9af4a966de07795f316fdc5987677800014020b41685c524b0000,0x64a9c440728b5d04ab67985007e15d4942931057148f50348af14098d3f8607eba64ae441616ae9bc9ceae1a30dbfeb6475f4c7c1b98962e2598767780000c0285c2e85c527c0000,0x29658fb349c0706e200442a22b5d01b5ddd44ef1f24c42e1ae62156a8df355653468a6d195684dc074292c6e331076778000140485c2e85c52670000,0x21d60b5177d3e617d432210bad4e340e792c9b410c019a4bb8a839966134c042a990220f1d0f366c480e0e46a1170b82010bff7e4bcc7e761fabe316605db40c8c12e9deefc651223282248e1bca0e5e322fd42d9598c5728000140485c2e26852bb0000,0xf9e47b9a0d63be1a401e5fc8fde8d2538c1524313fe147901400af1c584c3037cd766ea490f7187988428fe66afe981d286c3cf3f602f2ce75ff050ce016fef829b08eb4416bd666e49053a0825a1297dc598c572800014041742e85c9bbf0000,0x117efe66ae23f4c5728000140485c5e85c9b0d0000,0xf2598fe004000140485c5e3909b010000,0xde1450fe1dc02014042b05e3909b040000,0x5b68e2599151ac02014052b05e3009b060000,0x3d17d1fcc596f4fe7f4b3c549500a1ffadb173e1cdd2e17d599151ac02014051f45e390c1420000,0x26be34d51e1ac02014052b07e37cc1060000])))) (.b 848 (.b 816 (.b 800 (.p [0xfcc049344483e5bde8ca4b5b6d214dd78e0dd3013a424841d76fef4d82d52101d47d067d7697eaa9c1ebf45c8de39ff27d5993617002014052b07e338c1870000,0x12d96f583dfa83185b05a69f0b0aceb24a32543a07f5f0e8ae25db462b5436f32bf3844abd32a38abb8a3609f9ee721dde35993617002014052b07e37ccf830000,0x84599361ac02014052b07e37cc1020002,0x7c73599151ac02014052b07e390c1030004,0x8d599151ac02014052b05e390c1010006,0xed87599151dc02014042b05e3909b030008,0x6f598fe62402014042b05e3909b02000a,0x8e1a1c60e3450fe624020140485cad3909b0a0000,0x3ff4a4e134ce713259a3eced8f97768efdef6e9bd658522bf9652dedc5315493bfc47038fedf2d98179c8a1cad6da59915604020100485cad3909b690000,0xa59a00ce14ad1760402014053e8ad3049b0c0000,0x1a8daf7ce66a581bfe11b5a6562cc5b08b89734a26bb54a09424254577965c84711db3f62ee103eab54ecdc994953d32d5a6c4b03c764a0a9b5fdeaf9f565cd7e25992c21c0201405344ad3049baa0000,0x27bd5950edb55c6cc3f0871340653d281d63bb70f42f645ce15992c21c02014053e8d23049b3c0000,0x8d5992c60402014053e8ad3049b020002,0x4d7859915604020140585cad3909b040004,0x6459915624020140485cad3909b020006,0x6f598fe624020140485cad3909b010008]) (.p [0x8d598fe624020140485c5e3909b01000a,0x59598fe6f0000140485c5e3909b020016,0x49f2598fe00400014045205e85ce5030000,0x1bb07ea113df2d451be34f91ce8cb6dfc4832d97659da2a4bed640dafc5d1c439e62a46ee3fbf13107b83f6efafad7713ea33ce9a6189a8f631f73ea403633d7e7b68be00bf919acb41a1b230e495f71e1598fe5d402014042a85e85ce5c20000,0x10a30eedc94c044f8a698e63a84f52e1598fe5d40201404520ab85ce5200000,0x8d598fe6f002014045205e85ce5020002,0xa5b598fe6f0000140485c5e85ce5020004,0x84598fe728000140485c5e85c9b020006,0x6f598c5728000140485c5e85c9b01001e,0x8d598c5728000140485c2e85c9b010020,0x84598c5778000140485c2e85c52020022,0x6f59876778000140485c2e85c52010024,0x6459876778000140285c2e85c52010026,0x8d59876778000140285c1685c52010028,0xa8b598767bc000140285c1685c2603002a,0x6f5983a85c000140285c1685c2602002c])) (.b 832 (.p [0xe81c03a00400034060b41613426010000,0xcea5a12f41f3bbb038b463ea2c03e6676caa32963096752fe71303a0c802034060b416134263b0000,0xbdee18cac10983b924f58bb70339d8ca0288d8c3fcc3afa8c881ee877c5ed9234eeb80fab5dfe10e2e094befcd21c46181cf3fff9ca0a4538e364a14ae4feef727db9e81c04d0c802034060b416134269f0000,0x6f1c03a0c802034060b41613426010002,0x591c03a7b400034060b41613426020004,0x208046b3ffd51ddc0cb8a9f765a1cefbed864b9b621b92c8afce22b90800512df6bfa9ed12626825eb06dafa31c7a6912844ea46c8ab1c03a7b40085c0e0b41613426770000,0x641c03a85c0085c060b41613426020002,0x934aece3c9f08b979688ac992f85d818f92396da4adbbab38e9eb218ac136dcd10903989432d1415321da2fa0f069316eecb206a1dfac78a804f0f663be91c03a85c0085c0685c2e134269c0000,0x8d1c03a85c0085c0685c1613426010002,0x17d4ba5c799f70e023b397829497899b6a8fe84008d0f606f45d9cbe0d32fa91d0248b8374dd700db1c03a85c0085c0685c1685c4e6b0000,0xf891d43a85c0085c0685c1685c26020002,0x1f2cf5817497e34b2bd65016099932c955fda142ee72f87ea1129e0a311fd50d6477508015f6c8fb898616b128b4edd068ba2c0760c800034060b41613426790000,0x25e0c7d6170fc102665d4a9400b109c00034080b41c0f0321c0000,0x125c3991de7890c2e0d31365d579fd4da6af92ba57a9d0788b3bf85931b73a34d323d21a4887c8ff3f0635e9b79c1c098fdcbe555b91e9b1989dac29d83a819c2019962aaac77bc781824b98624280400b109c00034080b41c1343dba0000,0x685404b10c800034060b41613426060002,0x65765987676c00034060b41613426030004]) (.p [0x48e43087e0040085c0e0b41613426020000,0x10413ace8bfe3e28ce5be4dbd340649f4ba049e83a83087e744020740e0b4160cc262f0000,0x1254a2f155380d9609d422f5927c55e82843f219c64828f96f88e6bf6e5e3be5bd3087e7440285c1e074160cc264e0000,0x80583c7b4a5883f688984072f87b907add1b07b85dff63e9477a5d6f1a509672fb7b7b1a0964e35234cc3087e7440285c1e0b41e0cc26660000,0x8d3087e7440285c1e0b4160cc26010002,0x643087e7480285c0e0b4160cc26020004,0x31c0c0fd0c197f35a6a4ca12ef76be769ac49f06e3dd185cfe945963d506ded0cd3cc4bf78f8c547dfdbb685b8fca5809bea55d6fc8a83087e7480285c0e0b41613434760000,0x843087e7480285c0e0b41613426010002,0x47603107676c0085c0e0b41613426030008,0x2481e5598c50040085c0f0b4170cc26060000,0x1ac914838ad39ecc1e2593784ac598c56fc0207c0f0b4170cc26210000,0xf52246c914a7d6f712a506a2735541377b4332bc598c56fc0285c20078170cc26320000,0xaa77f592af22df2da2699c8a9a9c292350efb60b452bd9767336a210de3c37f48e4ab7ca72a28dc3da8f69d8e4c65ca4544bfbcccce487bf96e7da53e65c05ee9bd3f4c56fc0285c200b41f0cc268f0000,0x6efe82790236dbbc598fe6c80285c200b41f0b027130000,0x61028a02d2700a9598fe6c802104200b41f0cc2d100000,0x6d27bb74dbe598fe6c80285c420901f0cc2d0e0000]))) (.b 880 (.b 864 (.p [0x3b95a0759f0e53a6e054acebd450fe6c80285c420b4250cc2d1f0000,0x1b011950bb475bfa03f7ca84b3d1a6e82261581405c763ad1a0a16c546cb427d320681599156800220c420b4250cc2d590000,0x14fd599bd599156800385c840b4250bc2d0a0000,0xf37ab42bc1bd129eb36e0714af9d572b001210ee8bd599156800385c840a0250cc30380000,0x2ce606a24470bf8adf10a7938b6212b32c056768c7ecf26920b13275bd55655fcb1a5291131a24943598760445cb4d2d58c160418d331a714024f8dcc7f768cf7d04b6e21be599156800385c840b4290cc30be0000,0x8d599156800385c840b4250cc30010002,0x1b83599156800285c840b4250cc2d020004,0x64599156c80285c420b4250cc2d020006,0x6f598fe6c80285c420b4250cc2d010008,0x8d598fe6c80285c420b41f0cc2d01000a,0x64598fe6c80285c200b41f0cc2d01000c,0xa8b598fe6fc0285c200b41f0cc2603000e,0x6f598c56fc0285c200b41f0cc26010010,0x8d598c56fc0285c200b4170cc26010012,0x64598c56fc0285c0f0b4170cc26010014,0x16461598c57040085c0e0b4160cc26040016]) (.p [0x120cec5fb8f86d64e0de93d0cff8a330baeab598c50cc000740e07416134342a0000,0xe53f4c5004000740e0b41e13434010000,0x15ce8903f789561cf84b62133cb3bac3f4c5014020740e0b41e0f8341e0000,0x4734ad07c6e03f2b222182e95705a67b574a6a278cc672c5289bc7bee6b9f63a1f84c7d70ad1547a1c78cd9170aa61f13260092c422b44b5ff02dff88d73aab3f4c5014020740e0b41e1343f770000,0x843f4c5014020740e0b41e13434010002,0xa93f4c50b4060740e0b41e13434010000,0x593f4c50b4020740e0b41e13434010002,0x593f4c50cc000740e0b41e13434020006,0x949b70a39ff0d9a8598fe0b8000740e0b41e0f834130000,0x3781e7f574e6bb2e477e8fb59a36d01c259e1973f7b29f79edaffb7e8747a682df20cdb6d2b98547a31e9503a5a62da9598fe0b80004c0e0b41e1343f6b0000,0x257efb640a85aef905d3b158aa598fe0b800074140901e1343f1d0000,0x23b59a8450fe0b800074140b4251343f080000,0x39eea50cdc48061fce73ad9c02b369fc2dbf7740b9a96ff3657bc750342c7f599150a400074140b4251143f4a0000,0x9cbdb3f7dc9d58a05bf066160a24c39a89f2c53227c649d1b56e5035f1f84d559df0919f49a51b77a599150a400074140b425134466a0000,0x84599150b800074140b4251343f020002,0x6f598fe0b800074140b4251343f010004])) (.b 896 (.p [0x8d598fe0b800074140b41e1343f010006,0x64598fe0b8000740e0b41e1343f010008,0x84598fe0cc000740e0b41e1343402000a,0x6f598c50cc000740e0b41e1343401000c,0x8d598c5704000740e0b41613434020014,0x48e43f4c50040085c1e0741613434020000,0x468dd01e6768e6016ad9a8968ec3f5b5e8e100ea20be3f4c56f40285c1e074160f834330000,0x3ca167dacdd8c7828d9195bb61e305bfc1dad3e6bd0403066199efafd4971ac3f4c5014020f41e064161343f3e0000,0xe19fddede8f956ee873bb473731f22f12e26e1641ecdc6c5db82036ad8b9d5cd43601163592b987530fe4bbb7d07bb767a27ceb7e33690cd4087bc2cedfe03f4c5014020f41e0741a1343f7a0000,0x8d3f4c5014020f41e074161343f010002,0xa93f4c50dc060f41e074161343f010000,0x593f4c56f4020f41e074161343f020002,0x1ef63eda63a475dd6a84efcf1db8bb8138b4426c60f902e42d77437dd21d85779449deb73a4451d4b451bc220b225cd3e9aa0000654f50761d82e3a93f4c56f40285c3e074161343f900000,0x643f4c56f40285c1e074161343f010002,0x843f4c56f40285c1e0741613434010008,0x593f4c57000085c1e074161343402000a]) (.p [0x1076232c0b0e04e728051bf598fe6c80085c1e074160f8341d0000,0xe54f8fe004000f41e074181343f010000,0x6900c835940c767c436881e89bd8996bb1130f448a2d836b208788ec6a5d25f11b668bce0d5b986574bd838c88ec0b0c831707739cd22985f67a044a91668dd36d402898b94ad43cfe014020f41e074181343f950000,0x65558314634add5e6099095b565fb66e04428fb386ec4c61a0d14db5b1bc5bfef387a6d5e37269a84f110014020f41e074181343f5f0000,0x6724f4fe014020f41e074181343f020002,0xa94f4fe0c4060f41e074181343f010000,0x4c584f8fe0dc020f41e074181343f030002,0x16458598fe6c8000f41e074161343f040006,0x53e3f145b171b487a365f1db22cdc0d527cb86466c2a08900ad41ca30be598fe6c80085c3e064161343f4c0000,0x11760f90ec4bd5c2e6c0412e6818a22cfbf088f26d057fca54e9452a0b135a352a2c8c44d390277e3ab450fe6c80085c3e0741a1343f5c0000,0x1296385019ddd0265660526623497686c96dbe7687c65d5cadc101cc77ba7d161f27fefbf96446e2bdbf2ee0f056bf898bdc8e0df0908abb2e599156800085c3e0741a1143fa20000,0x1d1ca0b374dbb334cb725250cbadeafaf7c7cbbc4a9280a71acb37e7099578369f72c0039c5b868fece04f51be445486fd399f3dfd21d0bf3e38d78bad5098159915680001f43e0741a134469b0000,0x2ea2dbbe49d156800385c7e0741a134460c0000,0x83cfdc210b7f83323a4c43453475e332195c8f173426a5ef63119ab1450291d04494a6f18eeabad2472b8d282577d599286600385c7e06c1a13446840000,0x576d5193c18462806bade19a484ce698db48ee11cb2973efe4ab3e8395d0fa3d5fc74f2fa9def4df2b8e0f10b2b0fab9ee121442feed122f1270267dbbe034690d7c177420e59f1bf599286600385c7e0741c13446ad0000,0x8d599286800385c7e0741a13446020002]))))))) (.b 1376 (.b 1136 (.b 1024 (.b 960 (.b 928 (.p [0x1178599156800085c7e0741a13446020004,0x64599156800085c3e0741a13446010006,0x84599156c80085c3e0741a1343f020008,0x6f598fe6c80085c3e0741a1343f01000a,0x8d598fe6c80085c3e074161343f01000c,0x64598fe6c80085c1e074161343f01000e,0x84598fe7000085c1e0741613434020016,0x6f598c57040085c1e0741613434020018,0x7068063e7822b15665913b85e8051562b8195e84b531ae5ee3a19c8197843bff39687b86fc47ef1ab3802afc38167c1a1130f46de06564cb5e05026320bf3a93f4c57040085c1e0b41e134347d0000,0xf8c0fd94fcca45acf5aaa598fe0e0000f41e0901e0f834180000,0x7347600ad450fe0e0000f41e0b4250f8340a0000,0xa362381e449f394547b1d29eb2261c8aded037cf5345aae39b3723fc4b004fb6b7054cf3c9767c599150c8000f41e0b4250e034630000,0x1c5dfd7c55236f5310c5b8d31fbcccf6d3062e158f5a87ad7f599150c8000a01e0b4250f8393d0000,0x9e3a95968af6b277ee37f3e445f51080f9cb460f076be3024f9db53efd34bcb520fade026ffda7dc42589a84e1462d1bd4a5e18e5c4c09e628179599150c8000f4290b4250f839980000,0x64599150c8000f41e0b4250f839010002,0x84599150e0000f41e0b4250f834020004]) (.b 944 (.p [0x6f598fe0e0000f41e0b4250f834010006,0x8d598fe6cc000f41e0b41e0f834020008,0xbee3a507cb1246c65c11a6aca4826e7aee9c68929cdadbc344dc43662c5be450fe6c80085c3e0901e0f834470000,0x3caae2fd085c8e7a1fed1a995b3ea6deee430213bfd66a92745161eb2b525991567c0085c3e0901e0e034500000,0x72c284e633f8a3879e1bf8b15749275bcf29098dacb178b04fd24553849fbbfc863984c8ac1b69e8f2cf0d513a664632ce8cea0a1c59c8ec5267db0784fe8d385bd731f2405d3123de7b5991567c001f43e0901e0f839c00000,0x1b998aff54622a4f189ffbd40e6a205593f46d7dc56780429b87085fece5991567c0385c7e0801e0f839540000,0x8c005ebc4a51667c0385c7e090210f8390d0000,0xb7faf9bd83a33f7ef89b1d5cc471499741f14920e5adb18c0cdc34d46610f81cc8dd8a5b2e3087cf9851ab4c146bc5992a65c0385c7e090210ec39750000,0x1fda9067e095c3680d3c66cc87cff92a39d4d63778fdb3bb34cb1c15d08bbf1dd72ebc5992a65c0385c7e090210f83c5b0000,0x845992a67c0385c7e090210f839020002,0x6725991567c0385c7e090210f839020004,0x1a8d5991567c0085c7e0901e0f839020006,0x645991567c0085c3e0901e0f839010008,0x84599156c80085c3e0901e0f83402000a,0x6f598fe6cc0085c3e0901e0f83402000c,0x64e75681c13390caa450fe6cc0085c3e0b4250f834180000]) (.p [0x316ec3bef1b7e8e224f8f322a36816e73e73e9638b703347d99cf61d524b8d1ed110cecef1056b3ac59915124001f43e0a0250e034680000,0x16c68bfa694995dd5a8f8d8f1b4f5e4f2fb213742857268aad547f1c1a6c7b144e9b33d0632659dcd5ad75f42c3accc2413f0377dc3460a62ba94344ca8d5bb3cb40a1db50836d3a3559915124001f43e0b4290e034bb0000,0x8d59915684001f43e0b4250e034020002,0x8c005ebc49d156840385c7e0ac250e0340d0000,0xaefe4f407a1a5181f5be493358c6df1ed3a3da6bf179668eaf4df3c8351f372ffb03e9b846f11b9e985ac9aec0be599286600385c7e09c250e0347d0000,0x50fbb2caaaf6cf8a6bbe280c2d5d71f9bc32f8bf2a8cc75c85a8d47e91d5d193900944c92740bf35cc5e39319fb3c7fb7f17b1b0b874e2f1be599286600385c7e0ac280e034830000,0x8d599286840385c7e0ac250e034020002,0x10b72599156840085c7e0b4250e034030004,0x64599156880085c3e0b4250e034020006,0x142d364f404038abc15d0c350fe1ca29edac7d7c663b7cda328991a4cf64547303c8382b6e15a0d117e0ea432b1a3962a66e76a9ae2157afa4b56e2a3305915cf2f998eb012bae66c1dac6f8446d729b599156880085c3e0b4250f839d40000,0x84599156cc0085c3e0b4250f834020002,0x6f598fe6cc0085c3e0b4250f83401000c,0x8d598fe6cc0085c3e0b41e0f83401000e,0x64598fe6d40085c1e0b41e0f83402001c,0x7347600ad450fe0e4000f41e0901e1343f0a0000,0x4d2d65b05a4b51e14e0d4e6dfc1aceb2a05bda6778cc5b25c936d6b8be00f8d7b15d1fbd13bf5f02bccc904993515c9786c2642d95436508c06f258f9ca6bd1e218e11d66a57c599150cc000f41e0901e1143fad0000]))) (.b 992 (.b 976 (.p [0x274c45b3f89dedb900cc81d364f2bfc7f6bc07ba8f44499db726e1041a6764d156ea59ab3c9873d5282599150cc000a01e0901e13446630000,0x12707b3be72c804e0128ac3a85d964d897434001ff94cc32ed6ad49d150c8000f4290801e13446340000,0x16eaff1fa35e4f88ab9d11529caa3ad680da5c3c18403605243b9cee7b1514f4d6dc9130b8b0adecbb0cd6c40682e07f599280c8000f4290801e13446750000,0x6f599150cc000f4290801e13446020002,0xe43ca968b3a6696fed041001e03a1b82599150cc000f42909021134462e0000,0x8d599150cc000f4290901e13446010002,0x64599150cc000f41e0901e13446010006,0x84599150e4000f41e0901e1343f020008,0x6f598fe0ec000f41e0901e1343f02000a,0x13595377bdcbadad450fe0ec000ec1e0b42512c3f160000,0xe4ebe7c9099596728a4161de797075cf4cbb18f51e7e1fa9d9c822d24a32d7180c2fb1c3a03e1edb01d14b1c08764868f28663891e64117a380599150d00009c1e0b42512c3f980000,0xf71793211718ee0ae490ea792e954926ce006511af4ec92b95e82599150d0000ec280b42512c3f490000,0x64599150ec000ec1e0b42512c3f020002,0x6677598fe0ec000f41e0b4251343f030004,0x8d598fe6d4000f41e0b41e1343f020006,0x91b841d3dcd5e1a8450fe6d40085c3e0901e1303f170000]) (.p [0x10cdeb52225d6b14756282e3991950dd4270c50a576fcb319b974f37f0b35e37424574828bd13343a75c2b6bad21a07a35e7b59915124001f43e0801e1103f780000,0x33e2a6e40b0c1fd24d59dab7e7d958626527eb3872e27ae8eef985a4e4abf7ba7b5e4e2f6963d64668c01cdb2cc56368adfde5a9caf3d7318e5787e59915124001f43e090211103fa00000,0x8d5991512c001f43e0901e1103f020002,0x11f625922be3ff4e5ba7ee7beff3cfffd73f88ffbeef08fa6ca7d6f44549f60bb80b2b15912202509dbf3d78f9b80d6f146e4fc756e08e294cdc3370e450ad82815991512c001f43e0901e13045a50000,0x8459915688001f43e0901e1303f020002,0x8c005ebc4c51b6880285c7e0841e1143f0d0000,0x160e77724e7ecf540840af441862fef4f21ea136a57864f00f67d09d855160bc599326500385c7e07c1e1043f550000,0x84fbea358739fc4df3468527cd0b7b37bbd04f277e8f63466869d4edb5262e172ede5d44a66f5559466c6786e7c7490759aa8fe3fefbf599326500385c7e07c1e11442870000,0x84599326500385c7e07c1e1143f010002,0xea86f3276f65a231e407bc80184db3a4eb045bab599326500385c7e084201143f2f0000,0x1a8d599326880285c7e0841e1143f030002,0x59376599156880085c7e0901e1303f050006,0x64599156d40085c3e0901e1303f020008,0xb71598fe6d40085c3e0b41e1343f03000e,0x64598fe6d40085c1e0b41e1343f010010,0x84598fe7040085c1e0b41e13434020022])) (.b 1008 (.p [0x6f598c57040085c1e0b41e13434010048,0x8d598c57040085c1e0b4161343401004a,0x64598c57040085c0e0b4161343401006e,0x84598c576c0085c0e0b41613426020084,0x6f5987676c0085c0e0b4161342601009c,0x64598768380085c060b416134260200a6,0x3879f6aa408ca9e010a618765ed2aa9279c3742edc96b6ef2234d61675a9b5f76c1983efa1f7f524d654584c232a97ffb581393c9d41c2ae401d66824f35c5e05da0b6a695fd41d8b69f94878f87f2b4dd055361eda3087e64c000340685c2e0cc26c80000,0xfc3ca0dfd87cce37b0ec88634e9d15de208094ea336d60366ddfaf802959134c853dda1d0a941327308486df1e6b1bbba3087e0ec00020061742e13434660000,0xdf4ab22517bd0c4c51b7faaeab57d7754034a0c6efff0d6ed598af417a79dc19a53135f4f37b93087e0ec00034091742e13434600000,0x643087e64c00034061742e13434020002,0x5aab329fc6e436afb9e4606e6c4ae833cd59d88835b0e6287ac34e11b5572f000ace23087e64c000340685c5e134344e0000,0x8d3087e64c000340685c2e13434010002,0x3c8931076658000340685c2e13426030006,0x22a8f7598c5004000340785c340cc26060000,0x2f4b78b05607ff4b0efc0f9fca9307d7153abf939cb9e9c61da62c59a04d69ba0ed5ea5392a7fcaa598c562802034071a4340cc26610000,0x2662f7598c5014020340785c6a0cc26050000]) (.p [0x607f49a55fa5741497c0e5d3ba8e8d2588b252358ddadcd3eb29875e985abb07ba6aae9fd752ce16fa0f0db2673e9e0a564b1d57e7de3b7a3e5f2ce3338490f5d083352acd0aef827a4980d83f4c5628060340785c6a0cc26a50000,0x8cd0bf7132b0084ba6f858f23e768ef09af6082de93c332f5613132ae786bc7e30c55a56616c7a30c1a5f4f598fe628060340785c6a0cc26770000,0x6f598c5628060340785c6a0cc26010002,0x59598c5628020340785c6a0cc26010004,0x8d598c5628020340785c340cc26010006,0x16461598c5630000340685c2e0cc26040008,0x31bd1dd0363ee228d3b3f0a824447b4ef60c996753b9a700f44e9fe1e085e2598c50e800020061742e13434460000,0x262882d5b48aa3f4d2f092549d4ee1a2fa5b16b9d681818870b3cc5297d3f4c50c400034090f42e0f834480000,0x72fd00d85d4fe33ad39b8380c50c400034091743e0f834110000,0xf9b3a42ac0ab499ad2a907e9753baf1fad1baecd8bbb1190811209801566614d73ef6332078a17ed4851f57d9ebbbed026eaa94b67eea49c4cd000bde890dc9f5a61421341f793c6afb0d8355b6766186ebee9fd199803f4e10c400034091743e0f834cf0000,0x6f3f4c50c400034091743e0f834010002,0x8d3f4c50d000034091742e0f834020004,0xf23f4c500400034091742e1343f010000,0x21b5404e10e296ec8c3367913230c0573c5984b989eb2fea001d32a50f9980928bb7ab8c895691d75ead7fe6ecb65b6c238286cfb7cdebcf19aec2b57c6436dc8ce96f321a701d80dd2a049a7d7d7b3f4c50d002034090f42e1343fc20000,0xd71b7caced972fabd3cbd218c199d36f20ec8a551dbf91d483b2007bd5034cb26d2ff8b7f6ac537c6a6576b6002f7ea359786ba35cdff0d53f7a2be9fe219c95340d61743a7f00a56fddfb9ae4f5414979e83e6eb2129d5d89b8b7f23f4c50d002034091743e1343fd70000,0x8d3f4c50d002034091742e1343f010002])))) (.b 1072 (.b 1040 (.p [0x593f4c50d000034091742e1343f010004,0x843f4c50e800034091742e13434020006,0x47a988dafbe76d120c7e85d1f19e0178e293ed1f4a701a4a5c868322782bce1eb30b3e186313af46e95bd6dd03f0b9a49f8517e95ad0975f6f73a856de2183dcbdea1d58b87a0c0ebc4b09b7e44a0d8082cbbb25e7a598fe0cc00034091742e0f834d50000,0x34390cbe17084f28d540f163ed8c1572a57df2b9ec2d9a63874a5d6cc54a19ea35bd37d0fbfbf5c2a21a993382b1f3e7256c7ef5126d0d0db08d63dadb9669e5fac4f4222ed09612c62246652dbe67b77b598fe0cc00034090f42e1343fc80000,0xf2450fe00400034091743e1343f010000,0xf233bc711958e0d8b6dcd724532c30e67d89160ea50c708ff0b0c529fd4135f599ac4e004a7b319c2f7cbbf1774f4b96f1895a9335cf2e313067b6e50b2c88d241b19b32450c203d834692ffdf41f68a2179450fe0b802028091743e1343fbe0000,0x1deb64d6db4c3093a327f534bf57e82cc4908fe32a9978cc314faf982cbe976b292a027924e4d64a7245c47c9769f6bfb1f9732430db46879450fe0b8020340b1743e1143f940000,0xf39f3e5775112f42cb723d569384c00421977794542ea6ba4b6b9d952e9f1cd450fe0b8020340b1743e13446530000,0x84450fe0b8020340b1743e1343f010002,0x64450fe0b802034091743e1343f010004,0x59450fe0cc00034091743e1343f020006,0x145c1c955a7bcdd79599150b800028091743e1343f190000,0x2aa57a7b8f13c5e93b23c69abe88303329a16159155e924a485ae38a73221eabf6c70ce4294f16a8cd3754162a8c164826543b629e07b599150b8000340b1743e1143f8f0000,0xa6863498ca0d4dc8ee6ebe4d44c95379b3c52988a520a5c2f114758a0e89e49b12d739c28338fb070bc370aa36c0d89f9f21f3a42ab7628ce61db36f273d9faf147a599150b8000340b1743e13446b20000,0x84599150b8000340b1743e1343f010002,0x64599150cc00034091743e1343f020004]) (.b 1056 (.p [0x6f598fe0cc00034091743e1343f010006,0x8d598fe0cc00034091742e1343f01000e,0x84598fe0e800034091742e13434020010,0x6f598c50e800034091742e13434010012,0x64598c563000034061742e1343402001e,0x2662f7598c5004000200685c5e13434050000,0xf9ef2993363dbe8ef2a3885c3698791d79d19376ffb429274acde8c4f1e33f803d16ccfda3f4c562c020200685c5e13434530000,0x1f32f3a93fba108ae28e3837a86d9c380e8fd6f370cf3a7007623115f75e707ef214bb220020819b3c1b663357e8b36d6ce18012c6ef8de7b72103ae3e4fbd07b87730455bdf5320f804149968dbe9c0aa6e924ff46b7befe4462ec21cef82d8598fe62c020200685c5e13434e50000,0x6f598c562c020200685c5e13434010002,0x59598c5630000200685c5e13434020004,0x14a6e6e22655a4acc98d14da19320eb598a3510bb406d1a6d31cb628aa5e58a963c3cc4ac95c669b8bfc4b517c183e9610fe9dc091999410f0b369deb74a52e317c179b09cf72602c8285dcf6768407db1b9ce2060c2bd5b8ef18fc9be13f7a68c6354be2da3f4c5630000340985c5e13434e40000,0xd473fcf68d206af400c10a105e1450fe11004028092b05e0f834230000,0x1c40766a7e9ab2fa87f17a7bdfa3afacbe3db929ef97712bb1c2ed146917879ab6a0ff8f297031bb24a27a68aef0cda2123109bce7193955a202acda4292c9d2732f9db664b01a99b3dea9a44ed3f396dfddc40f84d8450fe110040340b2b05e0e034b80000,0x3904d9ba0d05d0d63019ead3b526d08c2b65a8679eadedb5f28cb2881b4c511fa8f700bed4e6558c3e79450fe110040340b2b05e0f839670000,0x84450fe110040340b2b05e0f834010002,0x146b450fe12800034092b05e0f834030004]) (.p [0x2e47228b26052cc6723d63101b60646e6cd1b95e5f0201206e8bc03eb84bd6b2992c5b0439c0c5cbfd7cdfcefc04da13497d859915108000340a2b05e0e034760000,0x435565c99276d992cd618786e66a68b00fa1b01ee442d9599151080002c0a2b05e0f839300000,0x343b4b38cf1bc2bdb0fb4ea3e1191b9344f574c6c4b4a93b7aa9dbd7e94840995a3e31e496df32fe083ac34092591d8ba5baab8f8059915108000340c1f45e0f839800000,0x18fce157639283e83327856ad4e0473134848a55f71ff3763d954f8196836d4324596048684097a0383de769fe60edd2de8ec357b59915108000340c2b07e0f839810000,0x8d59915108000340c2b05e0f839010002,0x6459915108000340a2b05e0f839010004,0xed875991512800034092b05e0f834030006,0x6f598fe60800034092b05e0f834020008,0x658d6da450fe608030340985cad0f834070000,0x8a10552e3e55585f5964d2c185a56bc24fd59b99258373ffd6aafc95fdce5b2cb90900f28c0da9d141ec78c393c78f3bdd38b02d8599155f4030280985cad0f834880000,0x2e52da49d155f4030340b85cad0f834050000,0x2e52da4fd285e8030340b85cad0f834050000,0x62a00f2e80cd61aad6839d0bc861dd3dbfac4322085f1082416867f1a385a5920f740bf15bf3e7812797cf779911e5ce28d70e40b7970d8599405d8030340b85cad0e0349b0000,0xa560cbf3a5dfb3d0ee6e7902a54a39901105510b6600e01a3f37a01bf2132af0db6e5d48246f635a29541d8599405d8030340b85cad0f8396f0000,0x84599405e8030340b85cad0f834020002,0x6f599285f4030340b85cad0f834020004]))) (.b 1104 (.b 1088 (.p [0x6f599155f4030340b85cad0f834010006,0x6459915608030340985cad0f834020008,0x1271598fe608000340985cad0f83402000a,0x8d598fe60c000340985c5e0f83402000c,0x758f1a87d520c366acb74eddd73ec7993a5e64c49a5e883ff679eb0015a55769453590c7bd68fb5e3450fe128000340928c5e1343f5e0000,0xd704217266b4bcef9f80aee780177212d1bb7b46f25f5188a7fdbe1545155422ed82918c96adfa39d31256f8b8ff86c3c23b33a596412f8b421eb89eb9cdffd28a37d78032e7b5124d5d344ef2262d93e10d7e93ebc61685d2605617959915108000280928c5e1343fe60000,0x6f25f6926a0b3bd2bab136fda1cfcfee3aeea6d7aebda323a1d5d2f0a1604cdcf0f7b3e5ea42fd2f3b23769735590c35ebfe31146691ec4229533e536d3088692bf973b6af1ace58dbc9bcf4a41a8780ad8259915108000340b28c5e1343fcd0000,0x6459915128000340928c5e1343f020002,0x6f598fe60c000340928c5e1343f020004,0xd948d073cc0302c09494a412c3f030000,0xd94e5243980302c09494a412c3f030000,0x4b975386fef5bd260c83f3572b9c421c4f31d1578e944589cea2a624c09da981affaf03c6d969799353a6bf6a023078866cf3ab417eb5c9213dfa116f094b3ea795af3063b0fa47d95993a3980302c09494a412c3fbd0000,0x6f599243cc0302c09494a412c3f020002,0x6c26f598fe60c0003409494a41343f060004,0x88f598fe60c000340985c5e1343f020006,0x84598fe630000340985c5e1343402000c]) (.p [0x6f598c5630000340985c5e13434010026,0x64598c5630000340685c5e13434010028,0x8d598c5630000340685c2e1343401002e,0x84598c5658000340685c2e1342602004e,0x6f59876838000340685c2e13426020058,0x2dbe4b607a0eaf002c3dd5c92b9af4f9b04faf27706f7609e294b16520ca04847da08ca899b471eab310768380085c0e85c2e13426530000,0xe53f4c5004000740e1742e0cc26010000,0xd71cfcacd227b352073fa40343a4c6c66d3edaa27151fb163ce73c62bdae968eeeed5e5360055893ecda30daf7929a20c3f833923f78830add44bd2d7ae6ce47fa075e8d0dceb0ac3f4c5014020740e1742e0ac269d0000,0x49c99e76f91bdb2c0ae29eb6cbf5d9367ff3a1a373b9a93f4c5014020740e0f42e0cc2c2e0000,0x8e74dd91201c8129fa284b03be380b6179da968abd073bf0b8d8049a51f411c78b85470d488b41a39504a29c0a76c46095ed9fd2492aff9ccd8129eb2490ab3f4c5014020740e1743e0cc2c7c0000,0x8d3f4c5014020740e1742e0cc2c010002,0x843f4c5014020740e1742e0cc26010004,0xa93f4c50d8060740e1742e0cc26010000,0x593f4c50d8020740e1742e0cc26010002,0x593f4c50f0000740e1742e0cc26020008,0x13335c90f4d3a2caec6988ec02bc29fbd010bbb070eec4d98225aa8598fe0d8000740e1742e0b0273e0000])) (.b 1120 (.p [0x816a93c1c01ac598fe0d8000740e0f42e0cc2d0f0000,0x25ce5210db619dfdb71c306582afdcc605660cdaa9598fe0d80004c0e1743e0cc2d2e0000,0x23b59a8450fe0d800074141743e0cc2d080000,0x5d96f827d146c1cdc689a56c8c379599150c000074141283e0cc2d270000,0x30ea368655fa587824c273960a3fe96298f9d11a24c6943077530a9599150c000074141744b0bc2d370000,0xafbc3f5d7d21383ebff4d0edbfe0e049fa6569cae022998ba651ca485e9dc8642c2bdadfb548de8e3265c9904ec278a000041393c6292867f599150c000074141744b0cc30880000,0x84599150c000074141744b0cc2d010002,0x8d599150d800074141743e0cc2d020004,0x6f598fe0d800074141743e0cc2d010006,0x64598fe0d8000740e1743e0cc2d010008,0x8d598fe0d8000740e1742e0cc2d01000a,0xa8b598fe0f0000740e1742e0cc2603000c,0x6f598c5718000740e1742e0cc2602000e,0x48e43f4c50040085c1e1742e0cc26020000,0x35b669a6339c9e737cf2a1a3d5d644d9946cc1c5570333a728e835369f9b2ae3b1a6d21ffdcbd748fe02e009d8a1cb69e5ec88975a7b1c6afaa3f4c5014020f41e0f42e0ac26720000,0x9acbaf92fb2c5b93767eefe181b5b72b43787a75f58a019868e62ac13cfa0bc2af2ccf364e0d32f1b5b6b73d66ab0d9980b5ad062dce08aab18ddba43b28851f13f3f52c591423ab3f4c5014020f41e1743e0ac26900000]) (.p [0x8d3f4c5014020f41e1742e0ac26010002,0xa93f4c5110060f41e1742e0ac26010000,0x593f4c5708020f41e1742e0ac26020002,0xe9bfbf449ce323f075b5c8a3989b486b1dd6cbc530e4533e88e5de1dfb61ff66429431492e939c8c201f94369d4a9ae80b3eac7b6f0c7e9b88ee2ab3f4c57080285c3e1742e0ac26860000,0x643f4c570c0285c1e1742e0ac26020002,0x1cc3bdcb2ad58c60e4e0c22b7f06dc964183abcf231dc37ba363423d348a83f4c570c0285c1e1742e0cc2c370000,0x843f4c570c0285c1e1742e0cc26010002,0x593f4c57180085c1e1742e0cc2602000a,0x848efa0d2c0538157084a481fefebae6f0d060820f25256a9598fe104000f41e0fc300ac26380000,0xd3450fe004000f41e174400ac26010000,0x4df7321d53f7a35b53ad51c039b28e941d2450fe014020f41e174400a026220000,0xf8c84266e636faa298df39da94759c82e7a7f6dcbb11e33adc6bd428d68b57d08e0155cb8ed222b6d424a917aef16503d8a1e5bd08643d6f455d71a46e7b1ebd3450fe014020f41e174400ac29780000,0x84450fe014020f41e174400ac26010002,0xa9450fe0f0060f41e174400ac26010000,0x59450fe0f0020f41e174400ac26010002,0x59450fe104000f41e174400ac26020006]))))) (.b 1248 (.b 1184 (.b 1152 (.p [0x9511e75645aa599150ec000f41e174400a0260d0000,0xb5df57b5106007ad597126b73cfacf1297a925b9b3e9e3e2eab599150ec000a01e174400ac29360000,0x3a3efd5335f16b7d9e5dc19fad9c1ffe10bb67f02299c9bba6de86509b8d22ac8a195c67cfaa823b1ecb27a09a528e73be67044ad6d91508c52d0106e47879599150ec000f429174400ac29a40000,0x64599150ec000f41e174400ac29010002,0x8459915104000f41e174400ac26020004,0x6f598fe104000f41e174400ac26010006,0x978c598fe6d8000f41e1742e0ac2603000e,0x19dbd4598fe0040085c3e0f42e0ac26050000,0x51c0028ae6f4e40d894118fc1f12b8e018872153d858a04c3277b6db7eed41715a4f9d76cf3eda58a8656dba0bc450fe6d00285c3e0f42e0ac26660000,0x37c30100d3cf3fdd97c615ce1dfdc299335d1819945c4ba0011db67390387801162fb77b0ce6712f8b2782e90fb749cef5f45671e5afddb207dc252af94c154e62a16f8ce6f6cfbf599156d00285c3e0f42e0ac26c50000,0x6f598fe6d00285c3e0f42e0ac26010002,0x59598fe6d80085c3e0f42e0ac26020004,0xa08efa7b374b461936d65bb47386bc902faf4d033531e4cc06a8450fe6d80085c3e1743e0ac263d0000,0x116d3e04e2c8e462ec19e9b6da551cecfb972c004957b7d8384efa3f96d6c015f7aa6df2f49329d26d5622eac116ea12cfa87ebe5cd05d842fffd31b6fa7943257e5991569c001f43e1743e0a026a90000,0x124f1d9c179e08ea424b0aded2320476517644045debb459c7d09abf5991569c0185c7e1283e0a026460000,0x26ea5c8c449d1569c0185c7e1744b0a0260c0000]) (.b 1168 (.p [0xc54fd281d8023247e1744b0a026030000,0xc5519401b0023247e1744b0a026030000,0xc552947190023247e1744b0a026030000,0xc55314b170023247e1744b0a026030000,0xcd5994d158023247e1744c09826010000,0xc55394d158023247e1744c0a027030000,0xc55414f140023247e1744c0a027030000,0xc554951130023247e1744c0a027030000,0xc55515311c023247e1744c0a027030000,0xc55595510c023247e1744c0a027030000,0xc556157100023247e1744c0a027030000,0xc5569590f4023247e1744c0a027030000,0xc55715b0e8023247e1744d0a027030000,0xc55795d0dc023247e1744d0a027030000,0x1bbb986216f2a28344d3bc010f7ebfb7a1ffb5d55b7e94745fc16ed9f71b155bd9c6651bbcd48e56e2178a7c1c60e7b3b6a1c78f018e182d2644dc081f1d752c3b1c024f1267d4466bb3b7bff3bb375995f0dc023247e1744d0a027b10000,0x6f5995d0e8023247e1744d0a027020002]) (.p [0x97765995b0f4023247e1744c0a027030004,0x6f59959100023247e1744c0a027020006,0x6f5995710c023247e1744c0a027020008,0x6f5995511c023247e1744c0a02702000a,0x6f59953130023247e1744c0a02702000c,0x6f59951140023247e1744c0a02702000e,0x6f5994f158023247e1744c0a027020010,0x6f5994d158023247e1744c0a027010012,0x10e875994d170023247e1744b0a026030014,0x6f5994b190023247e1744b0a026020016,0x6f599471b0023247e1744b0a026020018,0x6f599401d8023247e1744b0a02602001a,0x11785992866c013247e1744b0a02603001c,0x22abfc2888a9b851896323b0b1f758709be6298aee7f4e8c1b12f5a26a92c3fef54fe8591dcb9ac3687398f1baee551118b6e40bc5992866c0185cca1744b0a026820000,0x645992869c0185c7e1744b0a026020002,0x6f5991569c0185c7e1744b0a026010020]))) (.b 1216 (.b 1200 (.p [0x1a8d5991569c0085c7e1743e0a026020022,0x64599156a00085c3e1743e0a026020024,0x7ea2e62ab49d15138001f43e1283e0ac290c0000,0xb9182bd1ef53db5f01058fe44ba4b5463cee1529945046ee41b22295cdebb13a59ed0bf25f9f5d44448a20836994e3015ef2a002b18173433fb5a996d39adb363daa16e7abad047e8c49aeb4014bc987fec58259928138001f43e1283e0ac29d70000,0x6f5991514c001f43e1283e0ac29020002,0x23a9d1aab49d1514c001f43e1744b0ac290d0000,0x7a2513176affe67910ba27f5d31f710c7e152319814e1d6426546ccdfe7260187be365b23c1d2657da62097276ea6428144386fb6c72857825992812c0014c3e1744b0ac29930000,0xa4fe19010aebe8f7c0c6815cea6be0f2abedd902a55eb0b141056a468dc56b787b5992812c001f4541744b0ac29520000,0x645992814c001f43e1744b0ac29020002,0x6f5991514c001f43e1744b0ac29010004,0x8d599156a0001f43e1743e0ac29020006,0x6710784c749d156a00185c7e1343e0ac290d0000,0x22c979c16634c548e2f57275c6ad8e826b05e08853dfecf4b8a01cee58303566252f7edaa3288f8210c79992769a0ec9a029a553d031a83fa257d24c5904d4ff337d997bf599286680285c7e1103e0ac29ba0000,0x611904d178ebdeaadfd32f4557951680a22767f3b209fbea2c5e3adfb01192f09551915d916dfdd6ca8914a35d71fd8948bf599286680285c7e134450ac298b0000,0x1a8d599286a00185c7e1343e0ac29030002,0x10b72599156a00085c7e1743e0ac29030004]) (.p [0x64599156a00085c3e1743e0ac29010006,0x84599156d80085c3e1743e0ac26020010,0x6f598fe6d80085c3e1743e0ac26010036,0x8d598fe6d80085c3e1742e0ac26010038,0x64598fe6dc0085c1e1742e0ac2602003e,0x8c42de4b0d61001be5b56d93d6608917bd0f2e165a32e2635013349bacad450fe0ec000f41e0f42e0cc2c360000,0x60e5cbbf51bdda7dfbdc97049d8d5af1a244ad59b285974ce7b39a3c97afeaac64e97643f1f2adadaf4e71c2da9599150d0000f41e0f42e0bc2c680000,0x270804970aabddb34c9af17458e117a599150d0000a01e0f42e0cc30280000,0x11aeab7b5e87469aa30be69edef3ea363520d195770ae8107f599150d0000f4290d02e0cc30440000,0xb0fde3875968cd24365141007652e9bc247da6e381a7caec87d3a023f2d3c4c862357cbdea6f366adc36a7cef607b36b8cdaff70f94259f0906589eddd5a1833fafec82599150d0000f4290f4350cc30a50000,0x8d599150d0000f4290f42e0cc30010002,0x64599150d0000f41e0f42e0cc30010004,0x84599150ec000f41e0f42e0cc2c020006,0x6f598fe10c000f41e0f42e0cc2c020008,0x2fc874677f9acb23aa5b9d2afbceb3401aafad450fe10c000f41e1743e0cc2c260000,0x2c1476281daf53535f30f230b72d3a538de7a77f92e989e9b4f478baf543181ad599150cc000a01e1283e0bc2c420000])) (.b 1232 (.p [0x2fc1595c3d9cc309e9b30eeff39f7a6e8abead87349472bb7dce52e6ffb5b4f8f247b659a949d150cc000a01e1744b0bc2c460000,0x1c6baca5c02e1a316db9e764f868005309a5a8c74ab90faa2329bb88a567f7ffad52beafe3aaa777f599280bc000a01e1744b0b42c5f0000,0x5e5fa4fd38cf86a3fc5887bda87cdc4fc040f830a02523ee7d68102f19ea890494c9b2c13d104e6c23a7c599280bc000a01e1744b0bc2e630000,0x84599280cc000a01e1744b0bc2c020002,0x6f599150cc000a01e1744b0bc2c010004,0x8d599150ec000a01e1743e0bc2c020006,0x525fafb09d8d01ab49d150dc000f4291283e0bc2c0e0000,0x25ae19d567787fc9d636e36f37dc8ebc354ef9c73c061ee0ae3477c2f7633c7e599280c8000f4291283e0b42c4d0000,0x18a7967f4832fe4d339fb5f5ba38d1ee9918ce923b2ae51b3ab8ae9748428d8fcbf29ac64a7b5174c727e599280c8000f4291283e0bc2e600000,0x84599280dc000f4291283e0bc2c020002,0x6f599150ec000f4291283e0bc2c020004,0xc86f284d86baa3e8f6126d75d39babfde715ffa53b0e320879c67f074e2afa7c37edf7e805c35fa7c599150ec000f4291704b0bc2c6c0000,0x88f599150ec000f4291743e0bc2c020002,0x64599150f0000f41e1743e0bc2c020008,0x2b9452f48b3f00f62421868bef14391090a211985487c788174260eefa64ffa7b2645366ac6d133cf12959e078c92cd2e4176d08b68ae980599150f0000981e1543e0cc308d0000,0x154e86dd84a79b05fcebf88a628e1ade4e94f76fe71eb1744c9bf0144ef81599150f0000d0271543e0cc30520000]) (.p [0x46a599150f0000f41e1743e0cc30030002,0x845991510c000f41e1743e0cc2c020004,0x6f598fe10c000f41e1743e0cc2c010014,0x8d598fe6dc000f41e1742e0cc2c020016,0x50e3849bc316215a7c57340a241b089c4bb81450a1e74bb37ac450fe6dc0085c3e1282e0cc2c370000,0xd787380f62798a849853ae39512cf5583cc51f49e7ecacb8c3b6d8b2f3d0e3c4f7fb69c23c26abb73692cc9c86fa5b926d5b23ab349a81fc15806e96d2462b5441743359915688001f43e0e02e0bc2ca00000,0x1050f56be49d156880285c7e0e02e0bc2c0a0000,0x2964e08031df3184df37ef35ee35fb1383530d3dd935ad964c70c244b8d1e86830243229cd9febdb3ce748ebc599286640285c7e0c82e0bc2c7b0000,0x5d5d7b6ad2e63f6924bad73c0d8d2194a596da7aaf0ed637ee47762cbc0470e028c60f34fba83fc7bc0ac070d2b8c2d8bc347893f92f3a88358ac7ce13bba6204e61f729559d6f14c25844c2e3ca973e79599286640285c7e0e0330bc2cd70000,0x8d599286880285c7e0e02e0bc2c020002,0x1178599156880085c7e0e02e0bc2c020004,0x64599156880085c3e0e02e0bc2c010006,0x108d8e4038fe2ac49d15110001a83e0e02e0cc300e0000,0x89eb5d29f282d6132ce825b5461f13c9938c931f470e8b3f754389f0796097a2a5e8d81221573932fb81e0001b2b0c5178054e9dfcd5e4458cb3838599280f8001a83e0c82e0cc309d0000,0x15b579a7be05de8704a146dd481a16f004392ca344fa9165245818f65b225b152b43fcbb9ef89a351e1fff99b7e599280f8001a83e0e0330cc30760000,0x8d59928110001a83e0e02e0cc30020002])))) (.b 1312 (.b 1280 (.b 1264 (.p [0x6f59915688001a83e0e02e0cc30020004,0x14879bab9da7787f5d097285bd82ab06cc3a466d9167a08209aac31a026c8054e0766c215c2844a026d260b1612e59915688003ac6b0e02e0cc306c0000,0x46a599156880085c3e0e02e0cc30020002,0x84599156980085c3e0e02e0cc2c020008,0x1ecb3e81c0f623499c54cbe3f73f90d37a20ec20f5c70ea949d156980031c3e128390c02c350000,0x794e3da7922d0c15012c923c8302a995bc56fc6f198d308d2e561235b0f88c2cbd503930e25923d35504a23e87518fa63ef14766e739d0a149221b260dea5c9fd55576bfaae1c7a599280fc001903e100390c02cb40000,0x6ca7508227dcd7f6e167a8bd5d9f9818d4f98805710192b2270cd309958fa52eeb8c3580599280fc001903e128410c02c5c0000,0x8d599281cc001903e128390c02c020002,0xc0ac50e187c758bf07fda3645f6c2d070db0459fb56313c5c5a9aee9d58bd3e0afd86d54b63c437e9f2696599281cc0031c65128390c02c720000,0x64599286980031c3e128390c02c020002,0x6677599156980085c3e128390cc2c030006,0x8d599156dc0085c3e1282e0cc2c020008,0xb71598fe6dc0085c3e1742e0cc2c020018,0x64598fe6dc0085c1e1742e0cc2c01001a,0x84598fe7180085c1e1742e0cc2602003a,0x6f598c57180085c1e1742e0cc26010088]) (.p [0x64598c58040085c0e1742e0cc26020094,0x316ac1b6ec0b6f4396727b52f6120618afbd3bc93c4e046fd6daae8c9b161c5b7c9ed1daf98c8d480c1dc3df4b96ba031765e689edab3f4c5634000700e85c5e0cc26760000,0x2662f7598fe004000700e85c5e0ac26050000,0x36311c9a4ceb0c44d7036a98ff3f48ad604e6e26fa5472aecd47fb07cae6cd8da95c8c6925ba1a578cedfca748b7fcbb41bf57e3a8154f64581598fe60c020700e2b05e0ac268d0000,0x31f15a3418c2a8cc149af64c92140f017c8ca78a1780ffe8337d8598fe60c030480e85cad0ac263f0000,0xa57c7d9450fe60c030701385cad0ac26090000,0x44d645d26991427744e044cfbc03890e88a535f806838633facc801d1dd5a447fb3f406ac6f8505c3f4eb751dfcb29a35a79050c293112b89778d2296df214e1267fdce599155f8030701385cad0a026af0000,0x1db7477a0444e50b065d87392ebff237a68cb074e0868ed65d2494e440d913c9281a39b4fc7f2bac80549a13a83cb0b791c15ec5b052798aabbae1c0d9b53943952843d8599155f803070133c0ad0ac29ae0000,0xe665ee5db92f1f7dafd574c78c29986bef83180ce60314c6f58df1c673781230a585f0ca0967d8599155f8030701385cf10ac296a0000,0x8d599155f8030701385cad0ac29010002,0x845991560c030701385cad0ac26020004,0x6f598fe60c030701385cad0ac26010006,0x146b598fe60c020700e85cad0ac26020008,0x8d598fe60c020700e85c5e0ac2601000a,0x59598fe610000700e85c5e0ac2602000c,0x17d32e018087c66ab72ee70bca5365aac7b9daa8b31681a91c01db3d15d2f08a3d818e31fde72fcda736b7f598fe138000480e2b05e0cc2c700000])) (.b 1296 (.p [0x470f2a2438b16e5c3a8450fe13800070132b05e0cc2c140000,0x79d21881b5194d086f1b064d0d93c927e53fc67a5ae69371fa5ff1bec7ef3b1451324cc4e0f5e6be7256c1535ada8886b34785ecf876ece6cebbe0caa55663a388e395536754fe00147d5991511800070131f45e0bc2ca40000,0x171dee95ed16f2bb8951a90dce53be3824dae672420d3243f45c664ed2aa89e6e0018b5355def2794c4f88ae72826eb605a8b78624d4c0d342b3dd955991511800070132b07e0bc2c920000,0x8d5991511800070132b05e0bc2c010002,0x13174d7d51a225d5f42bc24617e172524598a2a2af27320c80c59a633f8a72786609b52da8c7b317670fa7a059e6f19b8e42d8a65fc6c9b90485e23737a599151180006c131e05e0cc309e0000,0x18de80887e9053324e9fa366a07fce828f169ff2375a5f70850e3d444171498599151180006c13270790cc30550000,0xa905991511800070132b05e0cc30030002,0x845991513800070132b05e0cc2c020004,0x6f598fe13800070132b05e0cc2c010008,0x64598fe610000700e2b05e0cc2c02000a,0x38a396d8450fe6100205c0e85cad0cc2c0b0000,0x181a674d6d8757ce360692279ae71572156f4ebacb55719bd407a97eb5c798053ba2d5751898af7a9c7fad0ce2205a0f464d0d9599155f4030440e85cad0bc2c870000,0xf07d69c781e94ac15625619f024b672db70bca1286276397b5faaf3fbe6ca2f2417261a23563127cfba6700cddac15c9e42da599155f4030440e85cad0cc307f0000,0x84599155f8030440e85cad0cc2c020002,0xd949d155f80305c1240cad0c02c030000,0xa94fd282480405c1240cad0c02c010000]) (.p [0xa95194022c0405c1240cad0c02c010000,0x23a396440cb0e93216bf91280bcee915a40ede1b0554a290096eca8ab8b118e2195ecbb6bb5c2d20e60ce94b29c8e86ea6dcbf833ad3d653bb054b6c7ac8edd85994722c0405c1240cad0c02c930000,0x6f599402480405c1240cad0c02c020002,0x1271599285f80305c1240cad0c02c030004,0xb71599155f80305c1285cad0cc2c030006,0x146b599156100205c0e85cad0cc2c030008,0xc475598fe610000700e85cad0cc2c03000c,0x8d598fe610000700e85c5e0cc2c01000e,0x84598fe634000700e85c5e0cc2602001a,0x6f598c5804000700e85c5e0cc26020028,0x47e733926843e518426452aa3db60dbddef2f8f3d24d3642cbf47f0e2ad9ad3f4c5640003381d4705e0bc26490000,0x3f89151ae43a75f2827c0d3a893d3cd338de4402da0fece45c6cc1d7f7d4dec5241d697bac0ce1f9881d2477bfdad25902dbacb6cf6bf09bad450fe14c000d41d2805e0a826790000,0x39d9341660fc5d6792aaff49954a47c099370ee121329df55d6dc7c5c2c4f40317ff584fc5b181ab599150f8000941d1e85e0a8265a0000,0x30a308855ac599150f8000d4261e85e09c260b0000,0x2fcb48a5c8a0927213dd09a5fa0411c8407b68b2c7a4a49745d4adbe4ed84ed82f819fd72f33c63ea1c3f8439479cfba5108d257568ca7d1ad1f2725ff6c1f85e7f9f81599150f8000d4261e85e0a828aa0000,0x84599150f8000d4261e85e0a826010002]))) (.b 1344 (.b 1328 (.p [0x645991512c000d41d1e85e0a826020004,0xdad97ce1b1a128f60c497c2204da3f402790d9e8a819966924d9150206298fe28e3750927a5991512c000941d2807b0a826550000,0x1082b4b3d47d2c40dae10a14b48eb5c57838301636c971553c01bbc1dbe160e06bcf261da18fe3b4fc01a5544e47e2db48fbb4cd77ef84e87bfe97826aa25805991512c000d4262807b09c26980000,0x42b94a470259bdc8349931f4e1f22dc6d0bd22ef8f8c2e797f22e90d0934e464d14ed9e02d40e45a9626d59abfd8409f0b76a8d808ddb7b2b4e39a26c6795991512c000d4262807b0a8289f0000,0x845991512c000d4262807b0a826010002,0x645991512c000d41d2807b0a826010004,0x8d5991514c000d41d2805e0a826020006,0x6f598fe150000d41d2805e0a82602000c,0xafd5f2eed7cdb3980464ff150000b81d23c5e0bc2b1b0000,0xe7703eaebc72b010bc9e77cd209a22e23248e277f24deb77b7420a62ea94bd1a108000b81d23c5e0bc2b460000,0x2c1e5cb8823e302cf14dcf4ff6dd22a88f86f7da3648929c48d698645c2e5a83598f979df142a6605269b0dcdda9f3b87518c21426d73937d599300d40008c1d1cc5e0bc2b8c0000,0x31bed0c7104a4ae8ca8f8e48c5e612d2697b1c04d4630dd06507a599300d4000b8241cc5e0bc2b400000,0x64599300f0000b81d1cc5e0bc2b020002,0x13439340af0be9a4ab9ea1862816799970332b34131c1a717e599300f0000b81d23c740bc2b3a0000,0x8d59930108000b81d23c5e0bc2b020002,0x6f5991a150000b81d23c5e0bc2b020006]) (.p [0x672598fe150000d41d2805e0bc2b040008,0x84598fe278000d41d2805e0bc2602000a,0xf9d013865b45aa450fe278003383627c5e0a826150000,0x8a15dd5ed50ccdfad03775235abf7942c62303f559c52f7fb1927a81c48d0eb38e380ee9ee9f9919409bfdc8b667ebae1a2258807a4dd07340c805991513000168361e45e09c26940000,0x13e1fe2e5245c168c8c1bdc338e4f6a8ebe62abeb1698b34b2a45b07a523b27590dd9e274307e6e457ad9ee56a6d37a00f9da61eee0a67939ecf7566af36a1361b46a5067f5991513000168361e45e0a828bd0000,0x845991516000168361e45e0a826020002,0x24d6f340381cf0ad49d15160001643627c7a09c26140000,0x44e7b72a609826a4b4101df0ecf6b2a09c2986deb3b6153e28d218df820822c508de951cacc35c852c0f98b26bf68a726e805992813c00164362307a09c26850000,0x7bc691d1e9a5b234d3c9cb8555bcbc168470073bd65a16af0fc8b61706b01cf884e7b5992813c001643627c8d09c26590000,0x8d59928160001643627c7a09c26020002,0x667759915160001683627c7a0a826030004,0x8d59915240001683627c5e0a826020006,0xd359915004003385b1e45e09c26010000,0x19aad4dd22224023385b1e45e09c26070000,0xbfcfca919a2bce36a52fc8aabe223e3ebe0e6c1737c82501edcc01e6d5ae62c897a6f2a62e899975d125a7530d199aa06abf18ff4d5bc8406df0c8a6781a22ee9036df83d9c54ae6aa4eb7c599381e4022145b1e45e09c26c20000,0xb2ca2cac03b3f05da0d4738532b043d7de592e6a8b5ec00ea913b8d78533813483e4c4599381e402338861e45e09c26570000])) (.b 1360 (.p [0x6459938224023385b1e45e09c26020002,0x657659915240023385b1e45e09c26030004,0xa5b59915240003385b27c5e0a826030006,0x6459915278003383627c5e0a826020008,0xb71598fe27800338362805e0bc26030012,0x64598fe3d0003381d2805e0bc26020014,0x17ab450fe3d0000d41d470a10a826030000,0x13cea949d15354010d41d470a10a826060000,0x5cd10b007a1185da6ec9189a5244b16af7dcfa48fee158b28309a372e102be4319aa59a2ba605e5532f1d62f319a295849c9ca7ff8b35cc659ac5c0e513f31c5753a2e37084079b268a47cbdbeadbffb6625748d55b7955992817c010941d364a10a826ec0000,0x11659639eb796fb45fb5ac3fa827c8b1c76bbe3b6f5ac590cf4d03ccb2d61b0486be5f21ceaffe11d13f006f8cf204a7f7045f7ee9fd9a6e42f4f3ef1059186d06796e8062f3877743d5476ff3661b98c0812959b5992817c010d426364a10a826de0000,0x6459928334010d41d364a10a826020002,0x7bfa09f71bad40f2642505dd31298c937e9ee6f10b70f3e412b7327636bea6141f2af7dee09cda59928334010d41d470da0a826660000,0x8d59928354010d41d470a10a826020002,0x1271599153d0000d41d470a10a826030006,0x6677598fe3d0003381d470a10bc26030008,0x8d598fe640003381d4705e0bc2602000a]) (.p [0xb71598c5804003381d85c5e0cc26040036,0x46a598c58040085c0e85c5e0cc26020038,0x8d598c58080085c0e85c2e0cc26020062,0xe53f4c5004000600e1382e13434010000,0x59c4c96542a1a124725b47cdae4e9380c5014020600e1382e0f0341f0000,0x20130820d8ea77b6b674576e258c8cc23be94250d8abea6a7c1fe8f4f53e19b6c14f7fd9306a35983c022854eb2cffe56b68b2b839c86221abb79745fb09ec964f597856132e1b4036e385aa3f4e1014020600e1382e0f0349f0000,0x6f3f4c5014020600e1382e0f034010002,0x8fca2e059c2470c5844ddd6ffc3db5388add739c62c3ca04bc7984d0431aa3f4c5014020600e1382e1243d460000,0x843f4c5014020600e1382e12434010002,0xa93f4c50d0060600e1382e12434010000,0xd583f4c50d0020600e1382e13434020002,0x593f4c50ec000600e1382e13434020008,0x2072ef20dece303463e8da1016af7169865fd39d6c6ca912287dbd89774763a241afbb9345485cba218ce50d767efd8305ef6ec7df571cffb62456b54234c15f3dd7a598fe0c4000600e0e82e0f834a80000,0xe5450fe004000600e1383b0f834010000,0x2e234ade3c801cd449eee71efb2025358ccbf940360a7e85a1d835fddfc040fbe1d516bf564943efb08766c393a8edce3fa424b19c83b91df4606f8a1c0d6d65679dbe36f3abf659aa450fe0b0020600e1383b0f8349f0000,0x59450fe0c4000600e1383b0f834020002])))))) (.b 1600 (.b 1488 (.b 1424 (.b 1392 (.p [0xf5c6f3d7791d69a81ccc93c803e18309fb581f36609b35b473b3ee2978367e14b13fc6194b72dd7aa7e599150b0000440e1383b0f834680000,0x112a627f0ea9848442d29ee4c86aba7887ab97b0d60e704690f5bbd1a5e9142f04ac97d7392b096927a599150b000060121383b0e034690000,0x258441ffef410e6a079b8a4443f0610bd2d93866985acd22f93c0a59bf4f1080b7dd73e4171743e454283b7a599150b000060121383b0f839670000,0x84599150b000060121383b0f834010002,0x64599150c4000600e1383b0f834020004,0x6f598fe0c4000600e1383b0f834010006,0x8d598fe0d0000600e1382e0f83402000a,0x1c7088334550d39331ec5f26f160cb9fe5ca4d031dc23790dc60a5779af967e9d48edec8f35ec16fdf63df4420277869c9573e7ed58d5f2ea383defa38add442daab450fe0bc000600e0e82e1343f8c0000,0x5108d2e59a25138bbe586560129c14d5e1d0620bea469cf69e8667997468f917d47e14b3f48c8513bc11ba25a2ccb7d9eb2f0b781e380a2b216d951fbf037b599150a8000440e0e82e1343fa00000,0x4e3e28a005a828f597e2d97d0c2d97d4e911465c698abd9640dba9080694493b8790b76334130f91dc9ccc91fe255dc2a2e480341c6798f82fbe7bff2604d7e599150a800060120e82e1143f8f0000,0x1294dffd7b7851d8a8be57cba7cf698ea8c51ef7e599150a800060120e82e13446380000,0x84599150a800060120e82e1343f010002,0x64599150bc000600e0e82e1343f020004,0x6f598fe0d0000600e0e82e1343f020006,0x36215920e035004c8ba06d615e1a65a61536ce280aa450fe0d0000500e1383b1343f340000,0x4f70421485cb6fd5b6f9d52f52e7518635b5a04fc4f443722b8f20292708235d2d610dea7437c91b1ff03eddb7a8f058601d9bc760985b65781c7e8237d599150b4000400e1383b1343f9e0000]) (.b 1408 (.p [0x6862170b2db7bb4b3552a887509d82599150b400050111383b1343f290000,0x64599150d0000500e1383b1343f020002,0x970598fe0d0000600e1383b1343f020004,0x8d598fe0d0000600e1382e1343f010006,0x84598fe0ec000600e1382e1343402000e,0x6f598c515c000600e1382e1343402001a,0x12ba47a8f726c80a77cbafa93f4c515c0014c191382e10c34220000,0x1f552756a8450fe0cc00098190e82e10c340a0000,0x2744c1a93330753be686d3bad5fa6d9b6f3eab2e00699d1761a41e62427f599150b000098190cc2e0e8344d0000,0x11c9493029260660aff6ae7f686b59ff60e7a48c97ea85df71c027c60afff5f8fe967a0c7a599150b000098190e8340e834600000,0x8d599150b800098190e82e0e834020002,0x4b1994faba1f8388f484bf3f34e3441c03a9db6c6aa12b9c5f4d4bbde249a72428a907de3e35382599150b800098190e82e10c3b6c0000,0x84599150cc00098190e82e10c34020002,0x6f598fe0e000098190e82e10c34020006,0x1537772785522622491813e46aff1832620542619e9307d07cc3bcd9456b5e421b8f71f718d78bb73980598fe0e000098191383b10c34750000,0x8d598fe12c00098191382e10c34020002]) (.p [0x186fae2b8c79d83e7c450fe12c0014c270e82e0e8341b0000,0x232156e96026e6e0203d58f3f77b806856a9448e9c28fadd58d95a303a7cd04af629e317201ca2419906503965cb570a160973dfc3f0946f98266d77c599150f4000d4270e82e0e834a60000,0x4d0b59834f4dafc7c999b00caf54f3b5ee7791da6bd33ba50018c7a599150f40014c360e82e0e8344e0000,0x645991512c0014c270e82e0e834020002,0xb71598fe12c0014c271382e10c34030004,0x64598fe15c0014c191382e10c34020006,0xc75598c515c0014c191382e13434020010,0x64598c58080014c0e1382e13434020012,0xddf11fac620627aece5944902a93f4c5224000600e3244f10c34250000,0x10b53fb3ab5151414b570b1ee40581a41d4848f7bc448fbca45fe2bed21123c11d140d01a8450fe0f4000600e1e04f10c344f0000,0x3fee10546a106abb9bee9f9042e24e40e9b0086b963f5219a2a35c805186815ef9c53054bf0f856dada89584b059b1179e098c956e284dd3f4a8790ad467395526aee9f2e61c9d2ef3b82599150d8000440e1e04f0e834b30000,0x4603ee602e141be219fc0cce9a6083a4ed99378aa92a28231e4e58c2caedc76ac290d9bda7fb32980cfba196a894e5c311fba79599150d800060121e04f0e834800000,0x64599150dc000600e1e04f0e834020002,0xb1bb57b54889620fc5bfbb316990f28380b5184c4f72149410c755c40bb1c3d1b106ed279711b6feb4bac9c90be087f599150dc000600e1e04f10c3b7b0000,0x84599150f4000600e1e04f10c34020002,0x6f598fe180000600e1e04f10c34020006]))) (.b 1456 (.b 1440 (.p [0x17ab48104180010480e324790e834030000,0x39f4e3dc09f69421552781836a09f71c5321d1ef299f2c86b60eb5a4337d33f1ce829cf37d9d12842d6e3e15e6c234fc1430b54e21e4b7b01141a27c5992113c010480e260790e8349c0000,0x2e6d37dd94bd2822fc17498b8691e246aecb96cb742e68bd093b707fa228e040013497674aa9f177629ac39be565a35956285ae0d23ae9038f4f9e10117105a083dc8edd95992113c010480e324990e834b40000,0x8d59921180010480e324790e834020002,0x6c26f598fe180000600e3247910c34050004,0x8d598fe224000600e3244f10c34020006,0x6677598c58080014c0e3244f1343404000e,0xa90598c58080085c0e85c2e13434030010,0x84598c58380085c0e85c2e13426020046,0x6f598768380085c0e85c2e13426010154,0x64598768380085c0685c2e13426010156,0x8d5987685c0085c0685c16134260201b6,0x5a635be5726e4526647eff867f5d03ab6df0b5b08d2d572a5405be45d3965a3104a20eaec0f02b173d870e4928fa93613c004d8ade6e81577abf652d87b6710d48870c9a8163c2f9e06b45cf6651de33b679c68c25f8db825c8a2e83087e5ec00034060b41624c4ed00000,0x3cdf78ef8083048cf29c34345f9b58700b4add71956f0e0c97cf6a378d85ab14f7f78f90ae1db3087e5ec00034060b41685c94540000,0x3c89310765f000034060b41685c4e030002,0x594d7cb0bcab383c51ab67d3564936fbb6f8e90dbb0c4c8b08dfef8b889fedd9a5400ea1f9e72119d8a873976cb25165ad5adcd8b802edc2566e4e0917c32b41e759e27cfbda5a76ceacd5c51b11b1765a3faa598c50f000034060741624c4eb90000]) (.p [0x1459c3c84c043b9e5ba8ae1afbe31a75db07ca105e9123f1f72f87edbc5649c5da51dd714d3b945560b64ae477968dee80c05c4b23cca9c9aa1f0ee6600550d464a7f170564b2f1059cc7e2598c50f000020060b41e24c4eac0000,0x42a3dc670f0097b519be02808076a8e56cd1d147b12dc0218380f872ff39660d43ca51733194c5ca1b34f77f3f4c50ac00034090901e1a04e650000,0x1d7cbf9949c1fff4380c50ac00034090b4251a04e0c0000,0x100dcf004959e1478b62376a3d733947ab8041529d98c8d9084cb7495a387ab309d6523528e2471c7aeb15d5e804e39f854f3ee480316b4abf4a21ba34fd9b7beaa6a50a7f901dea7b7b5bb3f4e10ac00034090b4251a04eb70000,0x6f3f4c50ac00034090b4251a04e010002,0x8d3f4c50d800034090b41e1a04e020004,0x335b45c9ea1ca24cb1f870b5f7ceb5cba3cfa23143d606ede8ab1dfc75c4f3dbcadae86dda430cb44b22c3ed106976325f40e2b2af57d54cd990923d2f5c595bc937ea23be5bbcbed96c7b6967c4a3b6cd534d7983d033ac0f1803f4c50d800034090901e24c69da0000,0x18b01ecf89088e4cab39079cefcc98147f58fb9ad2dfe1d774dabf4286272140362cdc6532f9219b715a809d15cc65ed97cd46a83e88b43252739f13f4c50d800034090b42524c698a0000,0x8d3f4c50d800034090b41e24c69010002,0x843f4c50f000034090b41e24c4e020004,0x2325a449da12e8223307b847d9e4ecf6027cac7f852340083c04ae0f207386c72ce552e75d8503ad70af4e2153c4d581a23cab346e6e8a90e7d1671b18f66c7c397a73be97793ea76940984e4ac7a448fe0b0000340a0b4211a04ec30000,0x17c2eeb8091d32ad7b16eca88033f33ea838755f91632537ea0578878269d421b039f717b7b1e2ce7a515130b0000340a0b4211a04e6a0000,0x26477598fe0d400034090b41e1a04e050002,0x39db45fc4f0d88e1df1a36f167b047f450fe0b401028090901e24c692a0000,0x19a0145677200c4d78a903e280736dbc34a4b72cc22fb6b7b7ac43cd06ba9d35e1eb789bd26dfa5612d8bf1103178b7b450fe0b4010340b0901e1f469790000,0xb4676d0173a4de8415ded37bb89bdb619ea953b230622431af4590efae9091384677f74400067ed9ee170a7204402d91bf167b36904aed3f60aa10002b80f86ab5ba8450fe0b4010340b0901e24c7e9f0000])) (.b 1472 (.p [0x84450fe0b4010340b0901e24c69010002,0x1563450fe0cc00034090901e24c69030004,0x296afdafa6bcab24cf017ec123ae1682248782125d3b26a8870a7f2f84ec530d6d1195a49668c59776ba931919fe0728479ce779599150cc00034090901e24c697e0000,0x6f598fe0d400034090901e24c69020002,0x3811afa19291ceed320531604a122b188da626e6e12a0a931546b51e9a272ab0401a203cdb0986647a1c4d66d51ccd1f05b6620c4a9a0cb3121225fa5a767cf3c323a1edd11bb5f7d8e33e1450fe0c000028090b42524c69a30000,0x516dfe9b02ab42c97bae14cdc49031848155221de4a38bf25199ba44da668a7e0965e29f037ef3b9ad74c81450fe0c0000340b0b42524c696e0000,0x64450fe0d400034090b42524c69020002,0xbed1e470361e35459787bc7617e77381ba83fa3194dcc23a669e17d50d2bb9be0ebfc7cabdfb7a599150c000028090b42524c695d0000,0x642c8e40f8e6eaf248e36d518a2ccccf3f713565c809bcb39dfde0a9e22485f0d7e74d786f3e78488866ff42d169008e8a6b5c456b2fba5ecc3f14ae9282599150c0000340b0b4251f469a40000,0xba41ffdf02ed80a5f4c9037554d1f7357862ab5e212bb0333cc55e64527636b92d6dfd50a2c241c22f5295ff27146b89d47aa7407358f0efcbba9258f79531d2b4fe827a599150c0000340b0b42524c7eaa0000,0x84599150c0000340b0b42524c69010002,0x64599150d400034090b42524c69020004,0x6f598fe0d400034090b42524c69010006,0x8d598fe0d400034090b41e24c6901000a,0x84598fe0f000034090b41e24c4e020012,0x6f598c50f000034090b41e24c4e010016]) (.p [0x64598c50f000034060b41e24c4e010020,0x8d598c55e400034060b41624c4e020022,0x2adb72f8598c500400034060741685c94060000,0x3d62a657a41730b5eb837a38fbc3dd598c55dc02020060741685c94270000,0xd674d39052e15a94a3600a15889fcf32753db594c43b7c73af449be3ffdf74c4700b373bf951c82efb14a3bd09e2b9712b675a71085c8cfdb3f4c55dc02034090741685c94710000,0x17490b96aa57f0d0ef87dce451ff12e8c7e5f032616409f1580297271b600a8012e105ace6bf18105b3d71f555dbd7a7658182260e3fff3b780598fe5b402034090741638094880000,0xbd5872992ce3e982d2753ad96a48def34daac64f60287f695209ec4295f341ea3e057db61d17f2d452735598fe5b402034090741685ce1720000,0x84598fe5dc02034090741685c94020002,0x6f598c55dc02034090741685c94010004,0x64598c55dc02034060741685c94010006,0x59598c55e400034060741685c94020008,0x3a099f8598c500400020060b41e85c94060000,0x13f6db616f50cb380ab1fb93f723fa1cc866ff9caedc3f4c55e002020060b41e85c942b0000,0xa16a116a6ff0236cc922092b3ee1b55085ebe0df84a2898af121dc76574224c6396c11951986ced03f395dce1359512e78c36255f886d2641b5ce56e3a51c3a26ddfea1d913072fb822a261ff24a2f3dd598fe5e002020060b41e85c94d20000,0x6f598c55e002020060b41e85c94010002,0x59598c55e400020060b41e85c94020004])))) (.b 1536 (.b 1504 (.p [0x2216cf8f8314a9ac885a43d644138b69c6eb10d2440e8929668a5e4dc3f4c55e400034090b41e524943e0000,0x1072580a5344e5560616f2f016240630c4bc39ce62bae61e736dd937f1f58df25d1c6139ed37682da6a43a9c8934b61bbbe36a35266f5570d5302284b8a7f7a36407d5b5795e19d6c08336871577d398686427958ef5dc450fe13801034090901e37494ae0000,0x39f130795628d78b7c129536f8718a7bb3a245f4524f725cadcbffc62c7cd38b5693e74be654021fa8a37a5991511801028090901e374946f0000,0x2289cd6609796b7636974617aaa86ea16ee993ca9a07480af69e1cd5ceae05aabb5cd36ffde78bcc08f524bd3807d69cf12c45a62b97e599150d8010340b0801e2e0947c0000,0x1e109274541eab4f4f5a4d989c4b7e839938b9f5f2389018dc61fb83d5202cd1219fa2f61392e733bbbbedc28d832a466ef668b7bd2dc3dd9d9a6c2646942a07a599150d8010340b090212e0949a0000,0x8d59915118010340b0901e2e094020002,0x49fdb49d15118020340b08c1e374b9060000,0xdc4fd28100020340b08c1e374b9030000,0x78d6befbf0b80f3ddcd33ea5c6f2848dd8adbf6a2590483b11c4e299335af4d0b1ddba395fed74635638fbd5632b0236f3bd7bd7c4fdf853771c5f880f218325737441b7dd98db599400e8020340b0801e374b9b10000,0xaea04488e2ddbc5663638d13edea79ab682599400e8020340b08c21374b92e0000,0x8d59940100020340b08c1e374b9020002,0x6f59928118020340b08c1e374b9020004,0x1236e59915118010340b0901e374b9030006,0x8459915118010340b0901e37494010008,0x645991513801034090901e3749402000c,0x6f598fe14401034090901e3749402000e]) (.b 1520 (.p [0x1e8236ee2450fe14401030090b425374940d0000,0xd5eee1128664328d41f5936b7694fe78d42bac68969294da72956c72e96ff23f9d79f79614e3bcdfda33488e163166198fd8d748484866ff99e912a23c77222927b88217f08cedcba1cda1b364564eaee1805991512001028090b42537494d80000,0x50049caa6a61c805857c59915120010300b0b425374941f0000,0x645991514401030090b42537494020002,0x970598fe14401034090b42537494020004,0x8d598fe49801034090b41e37494020006,0x31c01f8eee85dbafc146964ab242952c7ff4be1ce3986eb06b96d4f262ae9142828ead0430cc8dbf4db598fe49801034090b41e524de6a0000,0x108a598fe5e400034090b41e52494030002,0xc75598c55e400034090b41e85c94020018,0x64598c55e400034060b41e85c9401001a,0x8d598c55e400034060b41685c94010020,0x84598c55f000034060b41685c4e02002a,0x6f5987681400034060b41685c4e02004e,0x63b0f895283a83ea69bc9ad310768140085c0e0b41685c4e190000,0xe53f4c5004000740e0741624c4e010000,0x7131b1844fa1f53df50a2da1bfa00192a8e31b053d9e3e4dd9aba381f90b64a93f4c50140204c0e074161a04e420000]) (.p [0x40504244e5c4bccbdffb9383c7061e3b82b0e04ffaaa3ed414c784241b1c8c3d4489d067957e3eab3f4c50140207414064161a04e570000,0x163bfc48317c85a26f0dd0216b58bb3b470ad854690bd0a086ae3dec18da936bc60236f0e6f9d4506cccbb9c1fb744d9760a83f4c501402074140741a1a04e5f0000,0x8d3f4c50140207414074161a04e010002,0x643f4c5014020740e074161a04e010004,0x985587bfd55be5c7bbd702a4351bc216c7483004e09b0220f70641cf265e63a41db479e4f5ceb13ad190cb0eab3f4c50140204c0e0741624c69590000,0x5b6b1a84aceed4ec76174d049071b48331ba7ffbf94c44f3481703872c1c84456b1bb4da1ac5c2c3da0f4fb91e1775037dd41976975467b8c37ab58b9ad01c790547b4a93f4c501402074140741624c698e0000,0x643f4c5014020740e0741624c69010002,0x843f4c5014020740e0741624c4e010004,0xa93f4c50e0060740e0741624c4e010000,0x593f4c50e0020740e0741624c4e010002,0x593f4c50fc000740e0741624c4e02000c,0x376cec18de1bbc4ddfd7399c6c682ee4f631f75803884e2b540dbdfa298f8ee7a2fa226eca8b4bfa432d0bdc1422fc0a00608c1a8159e911890858bcfb9f16c6debffa25dea494083ab450fe0b80007410074171a04ea40000,0x2493c447b99abb038d005e197d82e563746a5f416a6d3bbd501df7d0a57855536094855be5fd037d5ab599150b80007410074171a04e650000,0x10974598fe0e0000740e074161a04e040002,0x24cf4cca0c91da3ddbdf71727ce5464595b2f100dbe82581255b8b338e28fc08547cfd9ba6d17e52ae7e6052e1f013765dcc464d26ba740cb47d7848af35c53f4aac0ab2cd8bef7b598fe0e00004c0e0741624c69ab0000,0xe5450fe00400074140641624c69010000]))) (.b 1568 (.b 1552 (.p [0xe1504ff53fcd01c49c5f67eab93b8a50ec61cd1f4a2eb8d2eb8db2824d71c11e615a2227f7889e1f23b60af6f8a6de3aea8450fe0c40207414064161f4696b0000,0x238f0e23144abbfcea623a53f93da91dc6a62b82662217b96bb3046cd1abf0aa6f5658770c9cf573a56b96df7445184427ec81b8235e65be9caf4064944f640ce2549c517204a9450fe0c402074140641624c7e990000,0x84450fe0c402074140641624c69010002,0x59450fe0dc00074140641624c69020004,0x130fef632b4074cab9bbd8e4a904c765ca78a395483c70c38779dab7550b559abfa302eb899828fcb1f763625142e1a46c0a7bae3e1c0936072290df08fe28d83f9f2fa99bc71277375218e2f0330f363e1c6de7c599150dc00074140641624c69d20000,0x6f598fe0e000074140641624c69020002,0x1ceb8b72d0a749ad2b05a530519d45bf9413b92e7f200f6e7c0db6102fc076dc5a97c82646972bab450fe0e000074140741a24c695a0000,0xd5a226ac73eb42f0e4964ca5c0f5dcb5cf50afb162c6be98054f5bc713919029f77a599150b40005c140741a1f469540000,0xbf3f6a68d2d85cfb40a47f410157569a34f8194a0fbaf73262eaa49d150b400074180741a1f4693c0000,0x27d3008319a368e7b67ad852c2c5878b16f85d000d244cafcb057be696159dc810bed2f586c3ac311e342da7781599280b400074180741a1f469720000,0x6f599150b400074180741a1f469010002,0x64599150c800074140741a1f469020004,0x49de31cc329d828f5cc854c429e8aba591a81e53a3c49eac438b9e7122265a49ac4ac7ad616c8703beb1e7b3cc94e81cef8971bf984837f0ca57f599150c800074140741a24c7e8b0000,0x84599150e000074140741a24c69020002,0x6f598fe0e000074140741a24c69010008,0x8d598fe0e000074140741624c6901000a]) (.p [0x64598fe0e0000740e0741624c69010012,0x84598fe0fc000740e0741624c4e020014,0x6f598c5110000740e0741624c4e020018,0x10d8f7d6db815bcc2945d2a74adfb6a16a73b2547ea5f9e927d12f805a913f2f51fa294bd0fd09ddbfe9df6a1ac0f21de8291af12b730c7df0c8abcd39217eee525039bcc5142ab4c7faff92bd883acc6d73dbabaa3f4c5110000740e0b41e24c4eb20000,0x79a7b1e07b8ea39b55a640fdf5e4c2c7464fd13a3ebde51b861afb87b80aa6d154f76fa252f0b40396b05a9450fe0b00004c0e0901e1a04e5e0000,0x19eaef11c97a6b2f3804d845ed81c3761db620308fe030d8ad7c39846685fdbfa8d8ab45658c50ec5b49dc80599150b00004c0e0901e1a04e6c0000,0x6f598fe0b80004c0e0901e1a04e020002,0xebdbd66e9ba0e855f6c993ab21e5d7762798af24da9dfcbcca14a8ac5f010091982457c35c3cfab926be0f8db67d3c445f021adaa8450fe0b80004c0e0b4251a04e730000,0x2c287f061ffdc7018dc40ee6bca78a92e9a6e70e39ad91de05e4d0d9ed34106fc1d3e2f5e7d83561b440bad996745aea0148f0cc8e8f7781599150a40004c0e0b4251644e860000,0x3947bd81f4bb0d840d5e1769e6c879b908a14a50d2e571a2bc334e4415bd1b94828e57a78251b8521c180d17da731ab99fa73aee1db60807d87b599150a40004c0e0b4251a05a900000,0x84599150b80004c0e0b4251a04e020002,0x6f598fe0b80004c0e0b4251a04e010004,0x8d598fe0c80004c0e0b41e1a04e020006,0x23b59a8450fe0c0000741408c1e1a04e080000,0x588391a4a7346fd8a3e24533e72122a5e5a93927eb02ccbaa4a4645baa6d84bdb70dde58a3725594f962fb713014e7e2e82599150ac000741408c1e1644e730000,0x60d7ff34329abb372037b6824e62a1494ce4d9d9b89abb339d9bbbe58bad73574d72c9389ed81c5ed862252b04f9e4fa81aea439e80599150ac000741408c1e1a05a800000])) (.b 1584 (.p [0x84599150c0000741408c1e1a04e020002,0x6f598fe0c8000741408c1e1a04e020004,0x1f1a0484150e47e4a1b5297289d746c0c27f1600d6014d2aef3cd85e2ae01f7184f73acd47a0a3cf8488785481598fe0c800074140b0241a04e7d0000,0x88f598fe0c800074140b41e1a04e020002,0x64598fe0f0000740e0b41e1a04e020008,0x140c6c83b5edc7612320e0df99604b867cfe1b1988f658eef9b38894b02e6653ac2b01f9f91d5aa8450fe0d4000480e08c1e24c69500000,0x47e67b6aa1f02f0da9f8fde266e608bda551959f267fe7312de1f5f5ad26cce04c2060d71f5f448935c994d851b1fbd410175e7a28b687a8776f7caae15ea194e19da31e127f599150bc000480e08c1e1f469a20000,0x2d93bda03a29d988a26c24821677e252d47c390659b0fd889e09e083f548e34dbb0cd5bcb094660782558377bfe4862ec5110c153043fe186f2f746c1cb34cf43424e40814da5836079599150bc000480e08c1e24c7eb50000,0x84599150d4000480e08c1e24c69020002,0x6f598fe0d8000480e08c1e24c69020004,0x470a7b0882dc07fb5cee6db5b0b04d13884a0e3b18fd7c67973744e58f28c2419dc2a59d79598fe0d8000480e0a82424c69660000,0x8d598fe0f0000480e0a81e24c69020002,0x250df09650df0130552e778475c5f57b55c51db760c94e074f3f1c6c84a9885ca32766f3367a598fe0f000068130a81e24c69660000,0x46a598fe0f0000740e0b41e24c69030002,0x84598fe110000740e0b41e24c4e02000a,0x6f598c5110000740e0b41e24c4e01001c]) (.p [0x8d598c571c000740e0b41624c4e02001e,0x36df3f4c50040085c1e078162304e020000,0x82573a7db3047ada0b060a8c97869710ec48fc9d6fa222740f547ab48884b4fc5aca548aa6677bde36d8abd7e3206302a2633d5677347bb8dddbdb5d11ddad3f4c5014020d81e0701617c4e760000,0x1febfa3fd158e794dcfe8a1d68de35f528723ccc8603eaa34223fb2d63af646441996debdf3f4c5014020d81e070161ec60490000,0x843f4c5014020d81e070161ec4e010002,0xa93f4c50f4060d81e070161ec4e010000,0x593f4c570c020d81e070161ec4e020002,0x3c77213faf2e0b3e01454bb822023ca3f4c570c0231837070161ec4e210000,0x46a3f4c57100285c1e078162304e050002,0xa5b3f4c571c0085c1e08c1624c4e040008,0xdf450fe004000f41e06c161a04e010000,0x32168e966d2bf57ec1fb2ea470e8331041c0c5f292a9f145bb1f183c7bd8ab450fe0d4020f41e060161a04e400000,0x9c5707d2c370bc2a1ae3cbeaed29ae24726a9e67569bc37be7971f647f39fafd1da7d5c7f4261805860845f6f3c9ce36198b86843f1d3f794df040e6caedc722f1bd7e2b3ac2558aa450fe0d4020f41e06c191a04e8a0000,0x8d450fe0d4020f41e06c161a04e010002,0x59450fe0ec000f41e06c161a04e020004,0x6faa58d0a360b617c292645840f3a225fc89c815cfd10664d53f07aca2cca599150d4000f41e060161a04e480000]))))) (.b 1712 (.b 1648 (.b 1616 (.p [0xe26a6686e4683350e5d1f53bf190ec0383dd39e6b41a8d8f47280ed76e3b2a0204d4b9d8a42b1151d5d42372a81599150d4000f41e06c191644e640000,0x1fef796d9fb9c8ada958323eb2e64635327d2883d1777885c9f89e404f4bb72636f75dc4799d714c0c297d599150d4000a01e06c191a05a600000,0x2298f7099e01b69edf7df675d2c0e4156ffb41f78ab87c30c6cb0338deba7f8d1871a847c3f97d04e6e1a1a9cf716f2e53b9007caa48f998c580599150d4000f42906c191a05a920000,0x64599150d4000f41e06c191a05a010002,0x84599150d4000f41e06c191a04e010004,0x8d599150ec000f41e06c161a04e020006,0x6f598fe6d4000f41e06c161a04e020008,0x39c11aa1d842d117b0738c64e3f66884df0b74f6214dc28fe746b26747a181b95710477c20bcbf7b09e2f0ef3ce165348d03bcd45b9cb0f66b195dabf6d21e1a7735c27ac317658a2541c8450fe6d40085c3e06c161a04eae0000,0x6c7e1d1215bdb27ef3717fc9ca9641c63f54f73c7a2b000156dc8f428f61d3ec728a39401f65c8350e7c4db2460c604f5d1ec51533e1518e7b3a3bc5991568c0085c3e060161644e9f0000,0x4760208c84d65933b8b270e841d429d059578ea3fc66aa49fee8c5ea7f6a2dc849d15130001f43e060161a05a470000,0x1ebd980cb59928114001f43e058161a05a0b0000,0x370285e54446c5ce7366bf83419d2bcd28aca99cb6d965b05f753652a12f98742086bbedb6cae8059928114001f43e060171805a5c0000,0x4e37ab643a6e14ec94087b4487b1116fbccda6dda95130514a815991ae2cc3d8c402c1436977bc2e70b630b88f593d67f9010866b1b5087de8ad249a4e2139c66d9616debfded2713fbc87a59928114001f43e060171a061b40000,0x8459928114001f43e060171a05a010002,0x8d59928130001f43e060161a05a020004,0x6f5991568c001f43e060161a05a020006]) (.b 1632 (.p [0xa3d8c7bd49d1568c0285c7e060161a05a0c0000,0x259d121f5a42b961805439726bce196fd7b5b7a919a5e634819578c60f456349b606e05e3c21dfb29d6ebf9656fb353fdd837ecbc11710ea375c11c0beb637605f35f2aa0a005395a51ae160e70123cbb04392d4ae587bc5992868c0285c7e060161a05aec0000,0x11785991568c0085c7e060161a05a020002,0x645991568c0085c3e060161a05a010004,0x84599156900085c3e060161a04e02000c,0x31d6045fe6f56d5959c84acc83f0ac0981b8a344d5557ad149642f049f7de315b5e04bec926bfc02947e0957c2c4be84482a3de8c87e4f569dfefc974c62af78ca025d22c4760d460cbf69969c069878059915684001f43e06c1915c4ec60000,0x8c005ebc4cd1d6840385c7e06c1915c4e0d0000,0x24c112187a92108145e515c5641cac2e45dd831cc3a7059a49af568ab9506d3815390260d4d75f3c957567905a7afdb88975cab36a6b6acc93e469478e6008d91caac3dbfc10f081c2ceef4b07cb62727a59934648033247e06c1915c4ed90000,0x34f47fe743a5553d16b989b0ef597a765f73b8734ce81599346480385cca06c1915c4e430000,0x64599346840385c7e06c1915c4e020002,0x946e599156840085c7e06c1915c4e030004,0x64599156900085c3e06c1915c4e020006,0xeebd67942a1e12324a81b5988fb62f07eff787b99cb51a88ff504b4c7d63cec147a86ec3bc66b9de960802c8d39d7b75bda4ef9272293c5017ed580599156900085c3e06c19190589c0000,0xa8b599156900085c3e06c191a04e020002,0x8d599156d40085c3e06c161a04e02000a,0x6f598fe6d40085c3e06c161a04e010018]) (.p [0x64598fe6e00085c1e06c161a04e02001a,0xdf450fe004000d81e0681624c69010000,0x46b7777224b607cf2fe3d2fb147d6903a5b5e3f5aa0eee9527b1c0679e6ce28d0d22beb1dcd36d32f220e02ed6fff76e9e485aaa450fe0f0020d81e064161f0696e0000,0x11075d93bc0a4ff13507e0e388111dd3aa71539f8b50c4508fdc3ee483bcd7fc03e6908c7e450fe0f0020d81e064162487d580000,0xe87450fe0f0020d81e0681624c69030002,0xdb60450fe108000d81e06c1624c69030004,0x299044e8479fe0263b7d85a4ed1bc18b14e8c97502e161392d31b7d599150d4000981e060161f4693b0000,0x12801260eca3271c27de566babc3e1f1bb4e0afa52df979404bf4870b9c51325627b91e9ee65e270917295f094b6f0fa9edc000ed260eab667609ff0e24e9bed61f3f9e7c599150d4000d827060161f469a00000,0x64599150e8000d81e060161f469020002,0x117998083e450e51e05318de6bc9999fd37c725c63df2d12616019e8650499957e03e3d2a7163520ed5c172c6934171f721b466eb790d77f49d150d0000981e0601624c7e840000,0x11c8381302820e25ffd0b2a0a2d20d82182772c0d5ed9ce868d15afbf86b5423fbee9c5ac98a643f06a8d6d75ee3d525816410cf7c599280d0000981e0601624c7e8d0000,0x6f599150e8000981e0601624c7e020002,0x1f0366f280d01b6d1fe871b1dda1d6a2f28cfe826fcc0dbc6b5337234e26e31ac2c0626a52d0c15ad889958817f0f6b2c639ee2069fda211a113073479472b2f6de1d0bd55a093c7d1aa9cf8fb9d2382bb4d82599150e8000d8270601624c7ecd0000,0x64599150e8000d81e0601624c7e010002,0x84599150ec000d81e0601624c69020006,0xf043ffe47a415254fb06fa401d0ec3aa5c4f3f9ddea282523198ef2cea6d6281b02fa2c0a65722050d45bb1e471a5ead3a691afa7aa2c803b5d984d4fd5aca9e7b599150ec000d01e06c191d869a40000]))) (.b 1680 (.b 1664 (.p [0x4376c5b76e7c6a8e6a20a2439c0d02ea329c81599150ec000d01e06c1921c77350000,0x9883599150ec000d81e06c1924c69030002,0x8d59915108000d81e06c1624c69020004,0x6f598fe6e0000d81e06c1624c6902000e,0x13e27b324d901fb73f0d7619482e0450fe2300030c370601622069250000,0x2088ad50dfc5bb18bdc54b2829134da10314297f5623d8c2dc849d151040016437060161dc692f0000,0x12292cea58f65df115ba55b6f29594c4be526ff30a14a9021c55d2d2cceb5cf8a5cf7f1e6f51f028f733a0e56998a7432a5c6a05ad7d8374e7cf6f93c5ccd4a4229be9866de1dce0b5decf0509740379599281040016437060161dc69c10000,0x6f599151100016437060161dc69020002,0x9f1fd73a7d6b3166669bb83b405576072924eb709c9869d1dfe68c68288fbbb27083ea46f8c38fbdcd3d7a0fe5d8df17959915110001643706016220787f0000,0x84599151ec00164370601622069020002,0x131c92afcf072e568351ecdf287959c2f9ce377f5c3f0a881b5caf15f43cbc73d624554adcf538857c9215e61f4634b59b910d6aaac9061d77689df01540cccbb2843b6643c61fbf31e33e0f9cb8556c59c34599151ec0030c5a0601622069db0000,0x64599152300030c370601622069020002,0xb71598fe6e00030c3706c1624c69040008,0x46a598fe6e00085c1e06c1624c6902000a,0x84598fe6e40085c1e06c1624c4e02001e,0x94fe46c3c1ea35865e66a0f14d8bd43b223825a51451c5951ee7c8c08fc267fa601adabac212883ab450fe6e4001781e08c1c1b04e590000]) (.p [0x7b7eaacf524a791d800ea27371ccd5b01f45ee996dbd5e76685ab34cf70894568b56567373d9d44c33347b6740afd000ac49d150b8000b81e07c1c1684e6d0000,0xbc047b63d717528be3f6ef4d269e60ab19d7203de45d7c934cd5fe2ff804436fe3d71f1a80e3dada1903247864b9bc11dcbf047be1ed98184807b3817d40a642030b681599280b8000b81e07c1c1684ea60000,0x6f599150bc000b81e07c1c1684e020002,0xf5fac982be2609e4b368096fe0e6ec9751ce6b9166aa92b047e599150bc000b81e08c201684e450000,0x8d599150c8000b81e08c1c1684e020002,0x7b25ec68d5c9416bef869e7cf3adccab4834cb8901509ea5987e3a5a0541abc190e7386133a9db87d54ab98c80599150c8000b81e08c1c1b05b700000,0x8459915110000b81e08c1c1b04e020002,0x3bea05b34a60a2364c0a939ae0687cd131f45927629fe79a15f6be9e88cb9f8aa582ed7d10de2b4f2762606ba24f2e16043b4f87e2a4a5e8fb702be92509132462133f81dec01abed7c59915110001782f08c1c1b04ec00000,0x64599156e4001781e08c1c1b04e020002,0x6677598fe6e40085c1e08c1c24c4e03000a,0x8d598fe71c0085c1e08c1624c4e02000c,0xb71598c571c0085c1e0b41624c4e020052,0x64598c57c80085c0e0b41624c4e02005c,0x15b3c658fdc3f4c57c8000a40e0841685c940f0000,0x242ab6dc682a40f4562f6c20fcfea8450fe140010540e06816380941a0000,0xf7e7ce317dd5758c16d019896b3f43b9a768c83b6dd466c62405d415917bc8add59915120010400e0681638094590000])) (.b 1696 (.p [0x3a8cb79d8562758d0308a2beea30cee301be392b794aeba7fbb6b108e4d7893cf5d7c167a88b7e599151200105411068162e8945e0000,0x6551739aed3942a0e458d1281e56007e81c9a73ff9878290098511900fa49b35824539eb14dea82c852d59d1f5548f9107fcb555417ebc2768927f59915120010541106816380bba20000,0x845991512001054110681638094010002,0x6459915140010540e0681638094020004,0x1170598fe5b8000540e0681638094030006,0xdc450fe5b8040540e0681685ce1030000,0xdc49d155a0040540e0681685ce1030000,0xad0ae7ef424dafd56845ec4ffc4d0d3933024ee678a97a47361713aecb50c4a19306cc52881695fcc09db5969371d40137a8b35d7af9234e8b438ee66bfb9539370f62e4497ecdc599285a0040540e0681685ce1b20000,0x6f599155b8040540e0681685ce1020002,0x1170598fe5b8000540e0681685ce1020004,0x84598fe5c4000540e0681685c94020006,0x1a320d47f5636fdb3a0d453aa450fe5c4000a41606816388941f0000,0xa74f211592160b0fb95c57df9596a7e5e82a41a01f2afc3750af41a2d4afb4d641ba0cadc7b538a1c15fd82307e69e0a8d25ed92862759d85b4cd9f5d90ea5393528066950403acd459aebbc0f8faab3ae617fc8fc370c2bfab507e599150e4010701605c162e894cd0000,0x2ea953ccb00b6abd6165a4b26483a1021a79d31a4f6435767e5a5c8982599150e40107016068182e8944b0000,0x1691599150f80007016068162e894030002,0xab12a03b5c88a19dd3478cddd0c2971516f7450b365fcef1a81d45e5841393cec699f1788504594c2273434f122dc468fd094f4543981ffad884c1a376c8bd80452a557e599150f8000a41d068162e894a30000]) (.p [0x6459915140000a416068162e894020002,0x71d6675ced55a6a50cf2a390b39b09367076aad6ea9fe8eacab1059e1ec0bd18e6d265587d39effdea85c69d500462c329d2cf087986c979559915140000a41606816388bb9b0000,0x84599155c4000a4160681638894020002,0xc75598fe5c4000a4160681685c94020008,0x64598fe5c8000a40e0681685c9402000a,0x21aa450fe5c8000500e0841b36c94030000,0x34ea849d1511c010500e0841b36c94060000,0x1c7529784739ceee980d22be61425801430898acd8b92a12cb250354c1feaa70d39881b9c3999a6aac69446164c8fb6ae78c389bc69a2003c3f084c55e35e696b02bee7a59928104010500e0841b2dc94b40000,0x421049144f3f110a190ecc200d172819a193f48646909a271a9070c7e7bbfb1a32e9759928104010500e0841b36cb85f0000,0x845992811c010500e0841b36c94020002,0x1170599155c8000500e0841b36c94030004,0x6677598fe5c8000a40e0841b85c94030006,0x8d598fe7c8000a40e0841685c94020008,0x970598c57c80085c0e0b41685c94030020,0x84598c58140085c0e0b41685c4e020022,0x6f598768140085c0e0b41685c4e0100c2])))) (.b 1776 (.b 1744 (.b 1728 (.p [0x645987685c0085c060b41685c4e0200c4,0x3ba9f764c9ae92b8089b6d5effee83e33107685c000480685c2e85c4e240000,0xf23f4c500400024061742e24c4e010000,0x14230543a01e476e466b480b9e685eb31a6480ee89222de13f4c50dc0201c061742e1a04e2d0000,0x4d1e703cc89a766e25a8274e2f71e2ec51e51ef815a13373927000f5ca7b5222f0e378d77b7159ba77d6e98e15da3b513a50dab6aba4e5a18bf634c14814b20b12d0d8e13f4c50dc02024081742e1a04e8c0000,0x643f4c510802024061742e1a04e020002,0x16775579c66263e613b2194a819e667ae890f8f6771d4e0955dde7bf89ca43742ce28c14c2def2ad17f3f4c510802024061742e24c695f0000,0x843f4c510802024061742e24c4e010002,0x593f4c512000024061742e24c4e020006,0x476e3b60dac9fe78538bc4d782d8b3e442236c31747d0267a0bb81833e1598fe0dc00024070f42e1a04e410000,0x51a6977c83648a8f10eb18de6764db95a74fb0e8ac663c5fbb520cf8eff97bd80f2cce52a649cd7e2450fe0dc00024071743e1a04e4f0000,0x1244b9f68bb2f670f90cfe0cdf44dcd306b562bf310cf904f34ed9d9525dd6de50f0b62ef375c0a612d12849115898d936fddab2b0e11e2b27165af51b81f4576cdc1982599150dc00024071743e1a04e940000,0x6f598fe0dc00024071743e1a04e010002,0x10a90598fe10000024061742e1a04e030004,0xa48d39212c7637e403801cda5985fdda4a5702af6f25a699147aefa4b6b1c62536bc51e69b9f4c429a1b2728c071e17fc4532464f3ba6de94c4390f760d9c06d27b598fe1000001c061742e24c69a20000,0xf2450fe00400024080f42e24c69010000]) (.p [0x276605a96e15193199a7b8d70cd7d2430a62a5549abf40a1f6d3a343994e3949c0c07c9f6dd794f90a23aefdac867c88e1450fe0c802024080f42e1f4696b0000,0x1ba5b7f799273b574d9150dfe9939c1a3581ec649f3ea42fb3da7c646606e27d9716608271007b0ad3e583708d10acee6487d7e3450fe0c802024080f42e24c7e770000,0x84450fe0c802024080f42e24c69010002,0x59450fe0e000024080f42e24c69020004,0x4fd41dcc2a7580aa2d33f2716592be4cb0ed0d507ca18689a9bf246916a7b599150c800024080f42e1f469460000,0x2a8566c544adf380ef071d57fcc1e30d486c1d8850330e67fb48aa0874fa133fe22167aacbb4311a64a555219bf3f60847ace3eba54d8164a795d5a44f4c12e523e877c24dd266e5c0f2764399a7c599150c800024080f42e24c7ebd0000,0x84599150e000024080f42e24c69020002,0x6f598fe10000024080f42e24c69020004,0xa1d2fa73125dde3450fe10000024081743e24469150000,0x7c6517a55f3141c5ed904d792c4ff97ba329a83a2e13ea301dd9c05a9cacf4cc47c3cd9c30a346519c0e2ccc10af59d0e9a7914fb900582599150e400024081743e1f0698d0000,0x14761e57be49452cffbf43074f5d1b805f3c8ce32279599150e400024081743e2447d390000,0x845991510000024081743e24469020002,0xc75598fe10000024081743e24c69020004,0x8d598fe10000024081742e24c69010006,0x64598fe10000024061742e24c69010010,0x84598fe12000024061742e24c4e020012])) (.b 1760 (.p [0x6f598c563c00024061742e24c4e020018,0xccdd2e29ba9dfa2ed5926849af56e23f4c563c000240685c5e24c4e220000,0x1e40f2598fe0040001c0685c5e1a04e040000,0x212afc903e7c08d9224ed4a68e709dc608afe78bbfd94fab988c68d7a66aef54ce0eeef644ad80598fe6140201c062b05e1a04e670000,0x23ebada450fe6140201c0685cad1a04e080000,0x1878c869c212dbad29a0ecc69751ddc861da9a7e113130f5177204ae825fca7c24b4f8f628bcf9e78cf3743dcf2d3a82d8599155fc0201c0685cad1644e770000,0x24be15259a7b46a3e26299056efc6794a7256f9f49bcb27d57439ef240befcc2a33d0797cd7093408c0f0f3c11d94da958ef6d1eff358303639619a185a92edd8599155fc0201c063c0ad1a05a8b0000,0x3bb4df17100d27c93d7195877c9705a189427141bfda599155fc0201c0685cf11a05a310000,0x8d599155fc0201c0685cad1a05a010002,0x84599156140201c0685cad1a04e020004,0x6f598fe6140201c0685cad1a04e010006,0x8d598fe6140201c0685c5e1a04e010008,0x59598fe6180001c0685c5e1a04e02000a,0x5f415e5a4082bef42ec33160aac8f9d4e1450fe61800024083585e1a04e270000,0x30b00ad149ba22ba051166fe82013918eea04e84c1210fb4d81c73a38db0da028f519d958fa28b7c81e0792bf839602c36ac5db1217d8d7f332b1a8a6076088d1f0e41a811d141b46b231384805179599150f000024082305e1644eb10000,0x10d1ac46290d71fc329c3fa1ab19222c61361b9bd6fffe23c96cfbba8e0b8406ce94315c5643616740ba339421656fee7c599150f000024082305e1a05a7b0000]) (.p [0x845991517800024082305e1a04e020002,0x109d2aac494d72ac8068e5e3d5f5c837bd3925ce5650683b903f1c747c7739cda8f290fc27f4e7832122331c46c632907bf3e196ca183b595816b55cf57a7f5991517800024083588d1a04ea60000,0x8d5991561800024083585e1a04e020002,0xb71598fe618000240885c5e1a04e020006,0x64598fe61c000240685c5e1a04e020008,0x6538dde5191047b17bb86964488a7d6740706557352b1aa7615010174a85257d58dac8294402e6e1bc24815653e12c245fa79f16b26eb61d493dce76c20e67f3cb189857a598fe14c00018062705e24c69ae0000,0x10794c8269e4d092559e55500c33582ccdcea9fa4277fb3ed1799367c86c564c8d969b62d547e5ba9c8dc218cd2ce7f38ae90c62409176066494f3db8eb67d25d3c6358f86b45d545b84232c3eb0282598fe14c00020072705e24c69d20000,0x64598fe61c00020062705e24c69020002,0x104774d453e2f80e618e68ace49ffaaccb78b7f384af7bf6c74f9f3a9bcc524877d802b17eee8c7ce6e40a537a93c780a7329f6395fbe1598fe61c00020064209d24c69940000,0xa90598fe61c000240685c5e24c69030002,0x84598fe63c000240685c5e24c4e020006,0x6f598c563c000240685c5e24c4e01001a,0x8d598c572c000240685c2e24c4e02001c,0x170ba7968a8676c2a6cb2fe10d637c81ce23f4c572c00024062002e85c942d0000,0x480da3bb1cd83c8b0ef714cdaca1ce2450fe1540001c061102e38094200000,0x41f054adb2414d9873113769c7b3cd25525ce159a626e3599151300001c060d82e380943b0000]))) (.b 1808 (.b 1792 (.p [0x9f1180536a221beed906be3c00967c88a106a0bc1ad179be7d145bf77bfc2674a3a800d0bacd745abf318eb71328d891c1521ff61ec72e8f4bd244377fd9ae2edc24aa17ac14cb5fbdea66de47fa273bda999599151300001c061103738094d20000,0x8d599151540001c061102e38094020002,0x6f598fe1580001c061102e38094020004,0x53c02ac1abf2208925e1c9a4908155cce8e2cdfb9649b35962bdda4c4851bf9d0d6510d05629d6cd594a3f6776729ad2533a23b302549d45c758b0cfcd59e2184a120fc858203667baf25095dff4792487a598fe15800024081102e38094dc0000,0x64598fe5c000024061102e38094020002,0x5e4dc450fe5c00301c061102e85ce1070000,0xaf8dc49d155a40301c061102e85ce1050000,0x42b1ede9731dcd9fad4d6dcaa161bc92218fbb2e8d526f8c7bdddba1f6663135a06d0e9fb4a987d0afd0b8e66f6d16135dd817dc5992859c0301c060d82e85ce1720000,0x76ece66ae6d0d25b7df6ed58a14d4ed48a57582540adc8c7b06e7f54ae5ea6fdbb4976441dec41eee67548d49ebdd5992859c0301c061103785ce1650000,0x8d599285a40301c061102e85ce1020002,0x6f599155c00301c061102e85ce1020004,0xda74598fe5c000024061102e85ce1030006,0x84598fe5cc00024061102e85c94020008,0x1d7f928a7be3450fe5cc0001c062004538c94100000,0x2e0b214df95cb6805cb9d4ebeb00a9c1774e8df948785864575bea96f17a599151280001c06168452f0944d0000,0x10ff033f42ed2ea18e6541523710ef320d8f975b0f36dff9196143b2ef78fad68cd07abaf84dab83b23d09b948b8a498b4b0414567c599151280001c062005b2f0948d0000]) (.p [0x8d599151740001c06200452f094020002,0x357c503755507a707f33aba8da1de90dfa2699bdb26bd2cb50fb2355c140a622ad8c79f889febf9e68f20e90666eadc49af7180d69e77d44bac2c22883bfcb8487a599151740001c062004538cbd990000,0x84599155cc0001c062004538c94020002,0x6677598fe5cc00024062004585c94030006,0x8d598fe72c00024062002e85c94020008,0xb71598c572c000240685c2e85c94020018,0x84598c5730000240685c2e85c4e02001a,0x79cae7348e07baaa7cd652e8f4ff14b3503967abf359858b4a85b0bb02156f135e7e3f4c5730000480a1b02e2384e5e0000,0xf2450fe004000340a1002e1984e010000,0x30b4aa5e5882c0944f27c18f3abf72d1388d7d48ec83dc7b364c18339ef32d15d0e88e8cdca2e8d9d6efc45a2c538f0f616861f287adaed5499c0d5118f0abc5a2031f9f1cd450fe0ac020340a1002e1604ea50000,0x5a905a64ce7934a6558d56a81016fcc4f1eb8689b2abbf70c3c33d3605d4b404622c121a3a3be42711afd78bc7e450fe0ac020340a1002e198596d0000,0x84450fe0ac020340a1002e1984e010002,0x59450fe0c0000340a1002e1984e020004,0x41f1b502d95cc1c1d4b9137c13277c4f4902634c2f430da3f316277459f47d10a6b9938fc0b3df248c24f373475b689c0e62ebba0a53cbf769f82599150ac000340a1002e1604e910000,0x5a5aff0fd0721c3918f0cf071a201234032927db6951ffb445d7b64c1c2a4ad979599150ac000340a0d42e19859580000,0x10c2d619228878bac78d8acee99f9f12664b3f5d0f06509808d854ca40021979aa82d35ac6d0bd6a099f10682599150ac000340a1003619859750000])) (.b 1824 (.p [0x8d599150ac000340a1002e19859010002,0x84599150c0000340a1002e1984e020004,0x6f598fe0c8000340a1002e1984e020006,0x974ceb7d5d139e0adf4703a02ac03ef98dc21ef16db901bee594d3ef618c97a0311be25050d89e99d29163b26a3f35e039864a53879598fe0c8000480e1002e1984e950000,0x64598fe0f8000480a1002e1984e020002,0xa07ac0555a6b57aa322d42713a31727b450fe0f8000340a1b0411984e2a0000,0x54a3b38beeca91b22f68e1822df5136af79c8985ffa8a87b1dea41fca8179186e58377dfabd74b7fc27048fda4a426c88e8c873851655d927565a9d6240c727d599150d8000340a144411984eb40000,0x19240c70fd668fdcd57238d7b15e84bfb7bd2d7507a599150d8000340a1b0521984e390000,0x8d599150f8000340a1b0411984e020002,0x970598fe0f8000480a1b0411984e020004,0x8d598fe118000480a1b02e1984e020006,0x1b133f1f5355f571692c4556807a450fe118000340a1002e23867290000,0x27b54a2a7e7d5eb35a59c69aadc3911cc2bfc137b9ed42548d93173f15aaa6838866d93130bcf9e3e1f71cda1beb3c85f8e2f1beb2bccb640cb8c00e0240710e2236261c2ffb856558e88ad5c54da3e7d59915118000340a1002e23867db0000,0x970598fe118000480a1b02e23867030002,0x84598fe730000480a1b02e2384e020004,0xb71598c5730000480a85c2e85c4e030018]) (.p [0x64598c585c000480685c2e85c4e02001a,0x9705987685c0085c0685c2e85c4e020070,0x8d5987685c0085c0685c1685c4e010072,0x845987685c0085c0685c1685c26010188,0x6f5983a85c0085c0685c1685c260103ea,0x645983a85c0085c0285c1685c260103f6,0x8d5983a85c0085c0285c0a85c2601042e,0x845983a85c0085c0285c0a85c1201056a,0x6f5981c85c0085c0285c0a85c1201067e,0x645981c85c0085c0085c0a85c120106a6,0x8d5981c85c0085c0085c0485c120106ac,0x845981c85c0085c0085c0485c080106d4,0x6f5980d85c0085c0085c0485c08010700,0x8d5980d85c0085c0085c0185c0801071e,0xe875980d85c0085c0085c0085c01030726]))))))))
private def data : Store := ⟨vals,rows,model,10,true⟩
def ok := test rule 5 13 data
theorem finish (checked : OMA.Tape245212.Before ok 1839) : Deny 5 13 ![⟨2,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨14,999999999999999999⟩] := by
  have same : data.vertex 1838=![⟨2,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨14,999999999999999999⟩] := by decide +kernel
  rw [← same]
  exact close valid _ _ data 1838 checked
end OMA.Tape5_13_245212
namespace OMA.Tape5_17_245212
open OMA.Box245212 OMA.DirectTape245212 OMA.TapeShared245212
private def vals := OMA.PageTree245212.get (.b 48 (.b 16 (.p [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,17]) (.b 32 (.p [18,19,20,21,22,23,24,25,26,27,28,29,30,31,34,35]) (.p [36,37,38,39,40,41,43,44,45,46,47,49,50,53,54,57]))) (.b 64 (.p [58,59,61,62,63,67,74,75,78,79,80,81,82,83,90,91]) (.b 80 (.p [96,101,102,150,151,162,163,255,256,7533,56320,56337,60018,60041,64353,64363]) (.p [0x11f71,0x129c0]))))

private def rows := OMA.PageTree245212.get (.b 96 (.b 48 (.b 16 (.p [0x1e6ab8c9d96aa229e21e2351021f8df6d7410c10a206881a228487180000,0x1cf09dbb2bc27b29cecaf09df68c8d4471cbe22b7bde8c9737da32021f7db58c41f8df68ca91a20a882343468a300000,0x1edf6d5e58adde25e2075aaec888a6abf08deb8c979e88adf68c87b7db51f6d7413adf6ef6d62ecadfc26321edf6d237a2788df47a32632355aaec888a6abf080abaa12ab8c979edde25cdf6d631e323b2bc277da320710b5b7db5d045aa5aa888abb2042c28495b8df6d621e229aafc23513a2b8df5d2324a91a20a882a26c68aa00000,0x237db510c10a206881a22868a050002,0x7e37db5d2410a202880a20c686060004,0x3cdf6d1cf09dbb288ef7d9cdf68c88c77328fb2b6eca737da31c2237da31fb2bc276d04088e37db5d2310e90a2068810e0cf0f380000,0x1d6676479e327656688a777da31f4102238df6d0e91a206881080e89f1a0000,0x1d578db5d2688adf6d74139df5d20667809df677b2bc2631d59bb1e229d56688a6678c9777da31f7db4204577d22e49df510b667f079e325decadddddcdf6be31dd8c9df68c7777db423c277d748c4f37db48f9df6ef7f098c78c8d1dbe2749dfc25c76229d8c9df68c7d2323b2842f9e232631d59bb1f488a2d99c4f07e37d2324e91a2068810e1689fac0000,0x810e90a2068810e0e89f020002,0x1f8df6d2410a2028800e0e88e050004,0x1aafc23c234e8ad446b8df5d23109e37d748ce91a200080a220e0e180000,0x5aa5aa887df6d74116aa25aa888d2aec85b6d7488ae8913adb55aaec8db5d222842d6abb237db5887ec82fa27588e910202882a220e0e3d0000,0xf3c1f7d748ca91a0082822020e0e070000,0x1cecaf09df6d748c4ef7d7cdb473b2bc26323b2a31fcf078c910becaf37db4f37d9cdf68c721c7222b7da31dc72f88abfc277db48c8eca13c278df6d232378ca91a00a886202090e540000,0xf36d7bec888aef7d3c25cecaf098c8eca8c7f3c1f48c98c4f36d74efb1cadf6d042dc72f88adf5d2ff0972ff098c7ecaf09737db48c8df6d748c4f37db58fcdf673c276ecada32231f5d3b2bc2442e323bec8d6228a91a00a8862020e13710000,0x1ca91a00a8862020e0e010002]) (.b 32 (.p [0x24a91a00a8822020e0e010004,0x1cbfc277db5d2310e16a00a8822020e0e0a0000,0x2f88ce91a20a8822020e0e030002,0xeb7d746b4afc22326313adf6d7410bf3c26313cf0910b8c8e8a6abf08f388c8e8a8c78ca91a208282a244e0e2f0000,0x5aaec8ec888a910a0a886a24490e070000,0x3bdf5d22eb7db4eba288277db55b7d62e89dfcdf6d637a31f6d5e88aeca8c81f4df6d74ae3f08d5aafc22bf088c78c913adf6d7410bf36d748bb2b7735d3b2bc27b2a321edf6737db5d2ff098c87b67368c87a22b7d631fc0878c9722ecadfc25cdf68c7737da32021f68c8ecad631fcd748c98c4ef6d748bb2b7d74f3c1e32442e320a91a21a886a24490eae0000,0x28a91a20a886a24490e010002,0xeb6d74e8adf6d3cdb5d22efb1e22b7d3cdb5d3adb4e482bc1e32632358c4df6d748c42f5df6d74abbdf4e8913adf6d748842e223bec713beca8842e222228a91a20a886a244e13530000,0x1ca91a20a886a244e0e010002,0x24a91a20a882a244e0e010006,0x1e5aa5aa888a9e88858a88a79aae326bf1ee371dee37db51e32232560a126229eeca79cdf68c4238de321ee37db58c77b8df6d748c9de321aafc237d6327579aac4788e37d63256e36d622b5087df6d47df6d4e9ba20a883a24490e6e0000,0x1aafc6ba2b6ae31f4ae323cdb5d2320284adf58ce9ba208383a244e131a0000,0xef7d637f67c88c9da311fdf6d748cbdb5735bdcd7b08bec888a8c9f3c2232631dfec788a73b7cb7c888a7e325cecaf098c77fb1f5d222a321ff09f077f8df6d748c8d6325cecaf098c473b2b7d7c24b73c25ee36d622a31fbe37d7488af38df6d748c973c26313b2b8df6d23236d631fbdb5d222b78ce9ba20a8884444e139d0000,0x16abb22aec8e895aaec8db588788e9b0a0a888a28ce13120000,0x3bdf6d7cf088c78c408bdb5d22eb6d3bec788888adf54b7db5ae10abf08ae11f7f3c1fae872a322325edf6d63787d6311edf6d748cbdb5d16e8988a79e88a8c47b7db5d0bd1edb5eca8c408b71e29e26311edf6d742de88a8c78c879ee8a29e1e327b2a321aafc6ba2ab8c9ae322bf3c27cdb48c8e8a8c88c91ce9ba21a888a28ce13a20000,0x28e9ba20a888a28ce13010002]) (.p [0x20e9ba20a888a244e13010004,0x24e9ba20a883a244e13010006,0x1f610e96a20a882a244e0e030008,0x2ce91a20a882a244e0e01000a,0x20e91a20a882a220e0e010012,0x28e91a202882a220e0e01001a,0x24e91a202880a220e0e01001c,0x6d34e11f484a6676f8df5d231f48c8d13d7484a089d748c44f8df5d1b4e54c784a8c9e6310210bd1bdf5d23111df5d276f92a31c42e3263213e4884a6f8df5d2b6fa2a321adf5d2311be8adc2ae36c8d74adb2378c710b8c96f92bc26323a2a31cb667f07f071028042b88c84f8d7484a8ce91a200080a22289d970000,0x174e54c78495d59a22265e21f92622175aa8961f4a97888887d3a257db5d22297df6d74888d621d39531f5d212445d3277db4895e37db5d265f92621e22355d7db5d16a9723588a887e8911787a277d842d75f92498888874d396023a1e124b566577db5d26887db5d04566ec7ec788be4988888e910202882a22289d9a0000,0x11df6d748c4e77d748fc2768c41f8db5d159b90842f6e4888788ad7bdf5d23e77db5f3c2231e3276d2310210bdb4ef7db4763763276d3b2a323cdb4eca72ff09f09ecade32231fc26313cdb5d392b7db5d042e323bec888a8c7667e792278c7f3c2392a31e324a91a20a882202289d880000,0x6676678c79f98c7e4ad0280ad748ce9ba208282202289d130000,0x1c774be22af7748c9738df6d2323b29de37db5d23277db48ce9b9c0a886162599d200000,0x3b08bdf48fcf098c408bf078c9db4eca777db4763749d9d88a8c88c4777db5d0b732ecaeca737db48c88c4ef7db4f36d3b2a320b8c777c27c1e327b2a321cf09eca8c4ef7db5d0b72ff09df68c473c27b28b8c7f348c9eca72ff09f09ecad9ce37db48c8df6d232231fcf08f37db58c7d2327b28e9b9c0a886203199d9a0000,0x2358ce9ba20a886202199d030002,0x11df6d79e4a139df6d742c7df6d63e422f7db475df098c9dbb2a32231f46678d9da78c7db5d27e792231e32559bb1e2291df67792631022f657926688a8c777474966775d9e32631e32559b99a21e688a21d777db42dde498c9eca755e37d7488a778df6d748c9de32231d99f99e31e7e631f92b48c9566ec7db488a20e9ba20a88620228b4a60000,0x1ce9ba20a886202289d010002]))) (.b 64 (.p [0x910e96a20a882202289d020006,0x2ce91a20a882202289d010008,0xe77db58fadf6d22e77db9db5eca887888d74884db5d2210bdf5d3adf6d236f6d748f92b6f3c2631e32358c4e77db5d2310bd7a2a32631f6d0a91a20a882a24689d4b0000,0x6dbd744ca84adb5d1329bdb5d278d99e36678c7da78c8db59dbe4adf4e486f92b92232631f92a321be8adf56ab6eb8c8adb6fa28a8c88c90ab8fc235d2bf0869bd2b84aafc2232631fa29b6f928af08e4af37d6327cdf6d748c7df48c88c78ce9ba208282a24689d7f0000,0xed72bb23927b5fb1e22b927b23688788e9b0a0a886444599d150000,0x7f6d7489feca88adf6d637e311f8cbdb5d1feca88a71c7c98c9d747e22a311fdf6d742df8c97fb2a22a32231f4f3c236d74e76d7908bd7924729ff097f92b925fe4ae491ca8c87fc25fe8ae8929ff09e8a8c7f3c25ff09df6d631e32231e324e9b9e1a886444599d7f0000,0xa8ce9ba20a886444599d020002,0x3adf6d237dfe8a2b7d74eba2840b7db5d0bdf5f078c98c8db5d17df6d62ea21f5d3a26228e9ba20a886a28d99d300000,0x20e9ba20a886a24599d010002,0x477db583cdb5d39db5e79247284e77db5d0bdb5d39db45f7db4e48e4988888a887df6d4e9ba20a886a2464b42f0000,0x7d0e9ba20a886a24689d020002,0x910e96a20a882a24689d020008,0x2ce91a20a882a24689d01000a,0x20e91a20a882a22289d01000c,0x28e91a202882a22289d010016,0x24e91a202880a22289d010018]) (.b 80 (.p [0x710f10a202880a22288e02001a,0x1cbdc25fe35d2f88abdfe35d2325fe37d7488a11fe37db5d23109e37db5d231179fa20688448490112a0000,0x1e5bae37db48498845b8db58841f8d22296aa2116aa2107e35d2a88a796df6d748842b8df48c8d446abf08d6b11adf6d6b8c41f8df6d748c4278df6d56a1a206885a294c13500000,0x5aa8845b8df6d74884238db5896a10606885a295019110000,0x1aadaafc2046ab8c4278db4ae322bf38db5d232040a110ae358d6a1a210585a295019220000,0x79cbdf8c97e326321f88a79ee37db5d222b7db5d2311eefb1e229c7a229e8c97f7db5d222a32042e31dfdf6d748c47fc7f48c97ca7f7db5d23236d631c42f48c97d62b7db5d04efb1fadf5d0910bdb488a8d321a21288c78950196d0000,0x7b55b7db4aa11022f6d74a9f88888a10210b796a96aa222a5bae37d095b8df6d74888db4888116df5d22eba1e1276d6210b88a1daae311aae3108e2b7e321aadadf6d748c46bae8784aeb484af0910be232231e3256a9f58a58a5877f8df6d21276116df6d2aef7d3ae877eb849aa12622042d6e89e36aa21ea888aa229321a21288ca2f5019a70000,0x21321a21288ca295019010002,0x1e5aa7f8d2223488a6ab11fae3108e35d2b8c95aa88a79f8842b8df6d23236d74116a7a21288ca2950192c0000,0x2d6a1a21288ca295019010002,0x256a1a212885a295019010006,0x296a1a206885a295019010008,0x7db41179fa206884a29501104000a,0x8e37db5d239fa202881a22101006000c,0x777db5d2311ddb474a77b2bb2222842fcf08e36d2327b29cbdc25ddf5d2f88abc4777db5d23109e37da31dde37db48c8e37db5d231181fa2068842021d24470000,0x7559959a21f89a22999e325d76210ae368c7778df6d08d15e36d749a22b8df6d16a1a20688516268bb2b0000]) (.p [0x15995e37db5d26887e36d26896a1060688520328bb100000,0x199c4e78df6d749e3107e348d6a1a21058520328bb100000,0x1d0a68957792a02621f48842b8d199d99ddf09f098c78c4477db5d2710b9e31e78c97559957792a0e48e202621e22999d99c465d2999e327c2278c41f89e31e78c92159a229d77b2b413becad2210b88af19e37db48c8db48c4f3c27cf098c710b8c9eca75de78d22295e37db4888e3488ae78db5d23255e37db5d222a32231d321a21288c20328bbaa0000,0x1d5667552b89a21d5e36d268889a22996678042b8d678c956688a755df6d748842b8df6d631f6d74116a7a21288c20328bb360000,0x2d6a1a21288c20328bb010002,0x256a1a21288520328bb010004,0x296a1a20688520328bb010006,0x8db51181fa20688420228bb040008,0x1f8df6d239fa20288120228a105000a,0x1b4f8d2129b2132b6d748db4db84784a6c84ca10b6fa2b8db58c76d92278c46f8df6d748c41f8db48c84f8db5d212b7d748d921a200181a2468a1420000,0x5d35e58089578478494c95665f8d66887997e37d621c2809da2217db5d175aa5c8de21d3e37db4a21257df6d7488810bdb5887899210202884a2468a1450000,0xf37db5d2313cf0910bf38df6d23239e36d742bce37db5d231f8df6d748d8a198084844445b21270000,0x17ec85cae572f7db5d045f92442c95fb238df6887ec8d74893210a0a88a4445b21200000,0x1f72f7c98c87fb29fe37d2223588a72f7c9df58c77f7d748c98c47f7db57f672f7c97c98c88c77dfeca88a88a10b7f7db5d2311fe9fdc7e48e89db529fdf6d631c42f88c971fe35d2f88abdfe35d2325fe37d7488a11fe37db5d23109e368c88d321981a88a44455a1800000,0x1ddf6d5ce37db5be372f8c7d6f7e32631df88a71dbe22af76325f088d222a323bec8d6229cbdfdf58c9df58c77f7d748c98c47f7db475d7ca2b7d9cbfc27c2631e321feca88a10b7f7db5d2311fe79236d4a7f7db58c710b8c98d321981a88a2e45b2c780000,0x7f6d5f7fb2a22a229f7f6d1f29f29f26321feca88a8c78c47fb2b7db5d2310b7df7f928a2a325321981a88a4461b2c330000])))) (.b 144 (.b 112 (.p [0x21321981a88a4445b2c010002,0x1d321981a88a4445b21010004,0xa11421980a88a4445b21020006,0x7df88adf6d748dcd74bdf25f27bdf6d7488a10b7df737db48c8df68c87e22847f7db58c41f8df68c772f7ef8c911f8c4278df6d2321fe37db5d23277db5d23118a9980a88a4445b21550000,0x2d8a1980a88a4445b21010002,0x2788d921a20a8844445b2103000a,0x1ae37db5d2b6f6d2b6f92a3223112df6d7410b8c86ab6f9e212a322325beba24a8c86abf3c1e313cf0710bf38d2b8c9ae323cdf6d748c4f3c1fc2442f68c88c7e8a8d321a208484a28db21580000,0x5f5e975d32612612bae8a847117df6d61e87df410be57db42845f92442c88495aaed72aa888abb5f688a888887893210a0a88aa28db213d0000,0x7df5ca8842b8df5d237f57dfe8a84a84a8c9db57d67fa2a1276d442b8df5d236b8db5d2b7f4adf7dfe8ad2128a8c88c4e9fae11f7db410b8c88c9d9f7dfeca88a88a7f6d237f671f2af7c98c78c8d637cad5f25feca88a8c78c47fb2b7db5d042df7dfe8a28a8c98c81d321a21a88aa28db218d0000,0x29321a20a88aa28db21010002,0x9114a1a20a884a28db21020004,0x6ab6fa2846f8df4ae3109e368c8f3c25bdf68c78c46f7db5d23108e36d748c86ab11aafc236d74ae3108e36d631d3e37db5d212b7d748d92aa208484a28db21490000,0x1c7e229f8c97ca7c97e22bbe37db5d222847f8df6d748c4278df68d92aa20a88a708d5a1240000,0x5aa5d6e37db5887e348880a12768992a0a0a88aa2e55a1130000,0x79f296a9622229e7cade321fdf58c9796db5d222b7db51c47c458ae377eb8c979f29f25f5bae212622a22a321e5aa7c888a10210b6ab7eb8c88c95aa88a79f29f256df6d7411f58a7f7d748498842e22a32072daadf8c8db5d237da2756ab688adf8c88c710b7e12847f8df6d2110ae232592aa21a88aa2e55a1970000,0x2992aa20a88aa2e55a1010002]) (.b 128 (.p [0x2192aa20a88aa28d5a1010004,0x1f7df5ca88a88a7df7d728a7f71dfdf4204e89e3629fe37da31dfe37db48c8db5d2311f7dfe8ad7428a10be23257df6d745fae87df5d0910be3688a8d92aa20a88a708db2c500000,0x1f7f55f6d74a9788888a7f57c95b588a7f7db5d212621c47d6e37db5d2a7d72a22222b5d222e229a7f6d2b84aadfdb48c87f7db5d212a311be37db5d2b7df6c97ca8c97dfe8a84a84a8c87f5d1aae326b8c40842f6adf69f29f29f8c88c97fae2129fe37d212612a32231cb8c95d6a97888887eba2b8d212622992aa20a88aa2e5b2ca20000,0x2192aa20a88aa28db2c010002,0x1d92aa20a88aa28db21010004,0x2592aa20a884a28db2101000a,0x2d921a20a884a28db2101000c,0x21921a20a884a245b21010012,0x6676676f6f08f0210b6486499e32231e78c79fcf08f3c2231e3139df6d7cdb5e4a8c710b6f7d748c4e4b8c9e77db5d2313cf099fcdf6d631c42f68c88c7e4a8d321a20848444468b7550000,0x159a210be37db5d268959a2235997ef8d172a22345cae792395f6d742b51c4e792a010b809ec8887893210a0a88a44468b7360000,0x7f7db48dd77b28a8c8db55757f92b920988a7e37e327675f77b2e222229f7488c98c87fb2bb2222a31e313becadf6d7410b7f929ff08e4a8c87f7d6313cf097f7d631cb7f7d6325fdf58c77f7d748c98c78c47f6d747f92a02b7d5ff1f2632357f928a8c710b8c98d3219a1a88a2e461b78b0000,0x7e37dfecae35d1fe4a80928ad93219a1a88a44621b7110000,0x88d321a21a88a44461b7020002,0x577d74811e37db5d27e76d79287809da010be37d748d99e37d99dff088c79e32359e31f49e310210bd749e3276d5321a21a88a44468c43d0000,0x1d321a21a88a44468b7010002,0x29321a20a88a44468b7010006]) (.p [0x9114a1a20a88444468b7020008,0x6676d99e32199e32271199e3109e369e31e7e5be37d748c9e36d748c76676678c8e37db48c80a580ad748d92aa20848444468b7390000,0x1dbdfe37d748c97e3277db5d23776d1f88a77b2a321dd74bdf8c97e325ddf6d232231fbdf6d7488a8c42dfe37db5d23278df68d92a940a88a2e461b7440000,0x3b5cae368992a0a0a88a44621b7060000,0x7df575d222a229d7ca7cade321fdf58c97f7db58c78c47df7fb2a22a229fd9f29f55fe4a2622a22a321f7dfeca88a88a75cbdf26f7c9737db48c8da31e311ddf6d7410b7ca7c9df6d7411feca8842e22a32231cb7c4e792442f8d8a7f8df68c87f8df6d631f6d748c47df7f92b428a10be232592a941a88a44621b7990000,0x2992a940a88a44621b7010002,0x88d92aa20a88a44461b7020004,0x7557e68099a229d6678c99e325d54a7678c9da32159a229d7e22b7db58c78c4477db58dd7552a688a8c7d231042f8d747599e32759e327556688a75f8842b8d1f8c955fe4a80988a75d54a88a779748e202a3255e4988a8c88c72d99dfdf6d749e31197f580a7f6d6780a9c42f89e31e78c95665479a22992aa20a88a2e468c49f0000,0x7f6d748952b7d5fd749e325f7df5792622a22a229d7ca54a7f78c98c88c78c47e30a67d57f92a02622a21e22b6d742d99df7d9e4ae192388c97ca8c97e79a02a31e3255997579e268095ca9a22268879a22992aa20a88a44628c46d0000,0x2192aa20a88a44468c4010002,0x1d92aa20a88a44468b7010004,0x2592aa20a88444468b701000a,0x2d921a20a88444468b701000c,0x5f8df5d1fe4ae36d745d3e4824a277d748dbd744e06e7960236d7497ae8984784a4e54f92132611e12a3276114a1a20a884a28e8b73b0000,0x1be35d1b25329b6489db1d3df6d749602b68c46f69dbe539602a580a8c72e321396129b4f6d7484ada311bdb54ca6eb6fa2a32231db4f8d212a324b6f9db5d04e7927adb51c42f8d8a8c84f8db584a8c78d92aa208484a28e8b76c0000,0x17e77db5d04e53279df6d74139e4a10b2395ca4c9e78df62072c98992a0a0a88a708e1b7240000]))) (.b 160 (.p [0x7f6d747f928a10210bdf67df7f928a2bc7f78c87f78c78c47f92b7d7410b8c98c87df7f928a29f7d328addfde321fde31e311fe4adf410b8c97df7f928a2a32231d6aa8018a0a708e1b7570000,0x1f7dfe4a28a6df2b92a325f7df5ca29fdc97f7db421fdf6d47d7429f2768c87df7d728a7f725fdf621fdf6d47d0a7f7d2321f276d631e31192e8018a0a708e1b74a0000,0xb8d92a9618a0a708e1b7020002,0x1f7d72a22992a961a895708e1b7060000,0x2592a961a88a708e1b7010002,0xa8d92aa20a88a708e1b7020006,0x1f7df5ca84a84ad746d32b6d214cadf6d237df4ca2b7d1f7db2632532a32632356eb8dbdb5ae31f6adf7fa2a129f7db26327a2a32632231e32768c46df2b8db5d1fe8a84adf6d748cbd974d7e89e172932611e12622992aa20a88aa2e61b7720000,0x2192aa20a88aa28e1b7010002,0x4f8db5d211132b8df6d1f7df5ca80a80adf5d19db5d277f92b7d747db2747df4ca80a80a8c97dfe4a7f7db580880a7db9db1e325f9e02a32632231e32768c40a77f7db59dfdb5e767e79a020a1c78040842f7db5d232f65d7e49e1729396026580988a2192aa20a88aa28e8c4850000,0x1d92aa20a88aa28e8b7010002,0x2592aa20a884a28e8b701000c,0x2d921a20a884a28e8b701000e,0x21921a20a884a2468b7010010,0x1d921a20a884a2468a1010026,0x29921a202884a2468a1010044,0x91199fa202881a2468a1020046]) (.b 176 (.p [0x7d6a845f7db5d221165f42578498842f8db488423888a7daae326b7f8df6d748c87f8df6d631f8df58c97d7e37db5d222b8df68c879f29629fae325fe37db5d23238df6d47db5d045f8df6d748842b8df6d63b4a202884a249d246d0000,0x75f29529f25fe358c754a7e78c97f8df6d631f7d2311f75f2a32159a229f9e325f75f2a3215578d6027588a7f9e37db59a029fe37d232232631d7566888d2688a10b66711fe36d749e3107e278c97559a22999e325d7e22b8db58c7d04578db5d268842b8df6d2321fdf58df557e37d74277d7488a7dde37db48c8df48c810b7f8df6d748c911fe37db58c41f8df6d631f7db48e0b5a2028844e528bbc50000,0x1b4f6d748444f9e36d65808953e36d748474f8d7484984be35d21293e36d7484ad744cadf48e0b5a200484a2a28bb320000,0x5d3d748498a0b5020288aa2a28bb070000,0x7df5cae2229f7df4ca7c829f2442df21f1f8db5d23257e36d7488a8e0b5a20a88a7ca22bb250000,0x7d77d72b88497d7db588a8871177d72a12755b8d745ea849a9f5ca8888878842e229729aadfe36d2b8c8adfe37db5d23236d748c46ab8c47c8e1b25faeaa212ab7d37d32b884729f6c94ca8c98c86ab7c86c9adf7df13a2fa25fe37db5d211dfe37db423484a7f7d748c910bda32231c42d3e36d212a3260b5a20a88aa2fe2bb9f0000,0x220b5a20a88aa2a22bb010002,0x1f7d75668889971e22845668040a68042f8db5d267d72a21e210b88a5ca6677f8db59e31e77f8df6d748c7df48c46677db2678c79df7dfe4ae202a029b4f8df6d7480adf48df6c94df23580a10b8c97f7db48df7df80adb580a6e76f8df6d749e31f7d748c910b8c88c74f9238df6d6580a10b8c98e0b5a20a88a7ca28c69c0000,0x7d77d74e54c784984a11f5cad7484b84988ae1729b4df6c980884a4e584a6df6c984a4ca8c78c44f8df6d237f8df5d2311b278db44ca8c8db57f8d5b7db2612a32532a31c42d32a3260b5a20a88aa2fe8c6610000,0x220b5a20a88aa2a28c6010002,0x1e0b5a20a88aa2a28bb010004,0x2a0b5a20288aa2a28bb010008,0x260b5a202884a2a28bb01000a,0x235120b4a202884a24a8bb03000c,0x1f5d3e35d21109e36d7488a5f8db5d222b6d7411f5cae1729f4ca4ca8c97d74df107e212622972a31df5dfe36d7480988a5ca8c86d3db5d044d3e36d65808953e36d748478442f6d7484a4f8db5d212932b5d2325f7d72b8db5d222972b68c77d59845f8db5d22107e36d7488a5cadb48c8d042f5d17e36d7488adb5d23c2a202884a24a8bba60000,0x2e3b4a202884a24a8bb010002]) (.p [0x7db5d23b4a202881a2468a1040010,0x2e39fa202881a2468a1010012,0x2239fa202881a2228a101005a,0x1f6d239fa202880a22288e030066,0xbe2410a202880a22288e020074,0x22410a202880a20e88e0100ac,0x1f5d2410a202880a2028810300b2])))))
private def data : Store := ⟨vals,rows,model,7,false⟩
def ok := test rule 5 17 data
theorem finish (checked : OMA.Tape245212.Before ok 183) : Deny 5 17 ![⟨2,76224⟩,⟨1,76224⟩,⟨1,76224⟩,⟨1,76224⟩,⟨18,256⟩] := by
  have same : data.vertex 182=![⟨2,76224⟩,⟨1,76224⟩,⟨1,76224⟩,⟨1,76224⟩,⟨18,256⟩] := by decide +kernel
  rw [← same]
  exact close valid _ _ data 182 checked
end OMA.Tape5_17_245212
namespace OMA.Tape5_19_245212
open OMA.Box245212 OMA.DirectTape245212 OMA.TapeShared245212
private def vals := OMA.PageTree245212.get (.b 32 (.b 16 (.p [1,2,3,4,6,7,8,9,11,12,13,14,15,16,17,18]) (.p [19,20,22,23,26,27,28,29,30,31,36,37,38,40,41,42])) (.b 48 (.p [46,47,52,53,54,55,56,57,58,59,60,61,89,94,95,96]) (.p [114,115,118,119,10604,20709,22194,23584])))

private def rows := OMA.PageTree245212.get (.b 64 (.b 32 (.b 16 (.p [0x796abb22a88addaafc235ae325edf61dedf6d4711edf6d748c4238df6d74653dc2dc3dd034a280000,0x7a37a3276d3b29cdb5d32ecaeca8c8f09eca73c27b29cdf6d47737db48c8df68c811cc9e88a7a229cdf68c8087df6d63107e37da3653dc2dc375148e460000,0x79eae3256aa229ee37db5d23237db5d040abaa14b7db4abadf4e89208df67b7d74f09df58fc276eca8c8782a9e88888adf5d1aafc223256abb22a88a7bb2bc25edf6d47de32076abf08d63256abb236d7488a10b653dc2dc3dde48e700000,0x235653dc2dc3dd048e020002,0x1f8df6d74b13dc0dc0dc4488060004,0x755778df59a026688a6678c956688a755e37db5d222b7da31dde37db4237db5d04776d748959a2566887d749a22b7d59df6d27667f079e32359e327becaddd76327b2a323c2631d59bb1e22842dddf6d1d2199e32559a2284777da3107e37db42199c4f07e37d749e3244777d748dd8c9db4eca75cbdd277db58c77622b7db48c8f36d748c9eca11cbe2f09dfc25cdf621cdf68c7088df6d748c41f8df6d748c41f8df6d74b13dc0dc0244dd3dc0000,0x6d32b7db5d23113df485b4e02a0237d746d32b7d748c910b6759dbd748c71392b8da321aadb21b204e8ae36d631f5d13e36d7484adf5d23653dc0040dcadd34a0000,0x5d34f7db4847e48d045f7d53961265e8710b8494f7db5d044cb8495579a02559a22265f8df6d74887da2216a97e37d2223a2745f8df6d74888db5887d22653040dc2dcadd3520000,0x3ce37db5d23653d8210250a813070000,0xefb23927b1f5d224d3102dc550a8130a0000,0x1fdb5d227fb2a22b7d3cdb5e7920a7fc279e482a31e327cdf6d23ef7d3c263236d7bdf4f0973b2bc2632231fbec8ef7d621e22bcf08df48c98c8f37dbbdfc263235ef7f0973b2bc2632231fbec7ec8d222bcf087f6d742b7d748c972ff09f09737db58c7df6d748c88c74d3d85dc550a8138d0000,0x284513d82dc550a813020002,0x72f7df708e2321fe358c7d748c97f5d2229fd748c97f8df6d7488a7f8df6d748c9df6d748c4655d82dc550a813320000,0xb653d82dc550a813010002,0x263653dc2dc250a813020006,0x1aadb6ba2ab8c7ae322bf086ab6eb8c8df5d2325aadaae3237db58c70a12b7d748c40ab8dbdf6d2bf3c1e3223236f3c26321aafc23c2231fa2842e3653dc2102dd58134f0000]) (.p [0x2aea87adb5d3ae8784a237db48fcdb5d3adf5d3a24adf6d7cdb5d23efb1cadb5d22ef4efb1e22222b7f3c1f4f3c1e323ae87eb6d082a32631e3235d124b7db4abae87221237db45f7d7b1fa262216abb23b2221e2284513dc2dc5dd5813730000,0x72f7a325e8c9df6d6311e7de1e229c7a22b47a327b2a320b79cdf6d23108e37db58c77fc1f8db5d2327be37db5d2229cecaf0911cdf6d23108e37db48c8df6d23657dc3dc5a17613560000,0x16abbe37d748880a1276d22657183dc5de96130f0000,0x1aada22bf38da321aac46ab107e36d631dfe37db5d212a3657dc72c5de96131f0000,0x1edf678878711ed742daadeeb8d2b8c98c88c95aa5ba256aa2296e37daa1ea888aa229e7bc27c1c47b7db5d23108e36d748c9ef8df6d7488a8c8657dc7dccde95134d0000,0x1edf5d236ab6ab6b67caf078c4eb7db4acb8c8ae32232765aa5ba24408b5aa88aaa222a88a79e88a7bc2632567c97c8ec7d44efb1dfec78882dfe877f8df6d0884988a8c8657dc7dccde96155b0000,0x7657dc7dccde9613010002,0x9657dc7dc5de9613010004,0xa657dc3dc5de9613010006,0x8df5657dc2dc5dd5613030008,0x16a97ec75ca5ba277887e89da223b5caec8df6d74888d62657102dc5dd58191f0000,0x1fd9f7f671f29f26321f2a31e311fdf6d742df26321feca88a71f88ad5f8c97e229f8c97fb29fe37db5d2223588a8c77fc27ae89d8a7fc25fe36d742b7da321ff09df6d631e3263657dc5dc59158195f0000,0x1f7fa28adf6d5e7e22b7d748df8c9db57f8df6d74aa15aa84adb5d2a7fb2a2222287f022f6d74ae37f7db47e323c2632357fa2ba26129aae37daae3263235ae31022f5d1aae326b69f29f29f21ae8a8c98c8eba1f684a8c78c9657dc5dc5de5819770000,0x8657dc5dc5dd5819010002,0xa657dc2dc5dd5819010004,0x1c4655dc2dc5dd5813020006])) (.b 48 (.p [0xb653dc2dc5dd5813010010,0x9653dc2dc2dd5813010012,0x8653dc2dc2dca813010014,0x667659d4b9e31d99e3267e631d99d99e3237db48c80a02b7d748c46678d9e6780ad678c7d67f3c27c2231f92842e3653dc210250ade13e0000,0x477db5d27839e481f7db58f9e48df6d3bdb5d22ecadfc2632231f5d15df5d22e49d66e77d3927b2221e2284513dc2dc550ade13a0000,0x3bec8ef8df6d74887db5d22657102dc550ab610f0000,0x1d77b29d23588aef5d222bce37db5d2325cbdd7441f8d2327b29de37db48c9738df6d23237db58c7da3657d45dc538ab61370000,0x7fc25fe4ae492bc23cf087f8db5d0adf6d631e3657d452c550fb611a0000,0x7f7db4776d747ddeca88888a7fc22326321fecaec888a7f7db571f88adf5d1f8c97e22a311fdf6d742e31df8c971f88adf48df8c9d9c76229d8c98c87c2235d222a313bdf6d4b73c27b2b7db58c47f7db473b2b7d3c26323b28b8c77fce2323c1e326321fecaec888a8c7657d45dcc50fb618e0000,0x9657d45dc550fb61010002,0x8657d45dc550ab61010004,0x2a3657dc2dc550ab61020006,0x159b9e48d668879a2657102dc550adee0b0000,0x1ff3c2081022f6d748b9e37db5d267f928408bdbb2221e22b7d746677f7d748f9276e487f92b92792202a31e3255df48dd275d1d6678c9d678c9d559a229de5d2222a311ddf6d748cbd3cf088c4e77db5d0bf3c22313cf092e31e325d76229de78d23263263239e4888a8c7667679db580ae78df6d7480ade31e3248657dc5dc550adeea50000,0xa657dc2dc550adee010002,0x1c4655dc2dc550ade1020004]) (.p [0xb653dc2dc550ade101000c,0x9653dc2dc250ade101000e,0x6d32b60a76f92a31db648d676f92a31e32632134e580896129bd74e8a6db4cad212a325be4a8c8e8a8c78c46f92b7db5d214f7db5d25e8784adc42e3653dc2102dd5de1500000,0xe77db5d04513dc2dc5dd5de1060000,0x3c6c9db5d23eb6d5fe8a1022f7d74e8984784adf6d237dfe76d7bd74e4913adf6d742f6ec888788a88ad3cf071022f6d74e7924addff097f92b924a8c87dbf1b2342e325fe4ae4929ff097f92b924a8c88c78c98c8d57df6d74aa25c8d3a257db5d172978885c7e4988888a657dc2dc5dd5b618f0000,0x477db5891df6d7908bdb5e422f6e48287db54f7d744c9df65f6d745cae4988888a887df5657dc2dc5dd5dee300000,0x1c4655dc2dc5dd5de1020002,0xb653dc2dc5dd5de1010004,0x9653dc2dc2dd5de1010006,0x8653dc2dc2dcade1010008,0x7653dc2dc2dcadd3010018,0xa653dc0dc2dcadd3010034,0x244693dc0dc0dcadd3020036,0x796a9f88888a6ab11fae3108e2b8c95aa8845aa884238d6a88a796db5d2210ae37db51c479f8842b8df6d23108e37db5d0489bdc2dc4dd86d6420000,0x7f7db5d2311f7fb2b7d7488a7dc78adf6d631f78c77f7d232442dfe37db5d2325fe37db48c8e37da385bdc2dc4a9899c360000,0x1aadfeb8d2b8c96ab8c9db4ae322b7fc278db5d232351028442b8df5d2385bdc2244deb99c270000]))) (.b 96 (.b 80 (.p [0x165b8df4aa126a117e37db5d22108e2285b102dcadeb99c150000,0x1fe37db47c85aa59fe972aa84a84988888a6ab7c8ae325f7fb5f8da22b688a88a8c879aadf22b8c95aa88a79f29f2632047f7db5d042d6a9f5aa88aaa222229aadf22b8c979f2967f7d74884238df5d2229fde325fe37db5d2326320779bdc5dcadeb99c7b0000,0x1e7ca7c97c859fe37db5d2126229aadf22b8c979f29e1de21fe35d2229fe37d748c9df61dfdf6d2320485fdc5dcadeb99c370000,0xb85bdc5dcadeb99c010002,0xa85bdc2dcadeb99c010004,0x985bdc2dc4deb99c010006,0x20489bdc2dc4dd899c020008,0x7e37db5b1bdc0dc2dcb99605000a,0x76f777d748c47ddde323556229fdf58c77f7d631c42f8df58c972f11f8c4278df58c77f8df5d2325fe37db5d23278df6d748c489bdc2dc458bca9440000,0x1d7552a688a6678c956688a755df6d748842b8df68c711de37db4108e37db485bdc2dc43cbdf3290000,0x7559a22999e325d7e688a8c77559a229de37db58c72199df9e31f59e32559a229d7ca7c9778df6d23237db58c711dd5fe36d1d56688a9a22359a22999df6678c89e31e78c956688a75f88a7d5e7880988a88a75fef8db488888a579278df488a8c87dfe48e37db48c87f8df6d602a32631cb5429a0109e2688a667e78df6d749e31f8d278c985bdc2dc4590df3b20000,0x20489bdc2dc458bdf3020002,0x7e37db4b1bdc0dc258bde7050004,0x1b4ca6d92276e31c40a010ae368c86d3e37db5d2110ae36d631d3e36d7484ade385bdc0102dd7de72b0000,0x5d3df5d21275d2285b040dc5dd7de70a0000,0x7df5f6d748845d77f928927b217df6d741175f9275d0910bdb588788be222a229b7f8db5d0adf6d748c47db275d1f29fe4a29be4ade32442dff097f62bc2047f7db58c41f8df6d2321f6f7d748c4278df6d748c7e23257df6d748845f9df5257df6d748878842f8db5d222a385bdc2dc5a17c27900000]) (.p [0x175d35c41f88495f8217297e37847849eb8df6d2126285b102dc5de9c271d0000,0x1aadbadbe8adb4e4a112df6d7410bddb4eba212a326322321b7dbe8a24a7d329325fdf621fdf6d47113df6d5f7d32a128710b29b4fa1ca8c98c86ab7dbae325b26b8c8adf6fae0a8c9df6d7411fe8a7f7db58478442e129be8ae378c98c88c779bd052c5de9c277f0000,0x6ab6eb6df7db278d092844dfdf6847e6b8478442f8d2884a6f8df6d2326322321f6f8df5d23277da321a7eb84a689adfe37db5d23237db58c78c485fd052c5de9c274e0000,0x2e385bdc52c5de9c27020002,0x7d2e37db5d2a5df5f92612a12622177d7e892898885aa7d7aa22a221f5f8db5d222b68888871177d7e8984a849db57e15ea84ad9f5d7e892622a22221cb88a85bdc5dccde9c27540000,0x985bdc5dc5de9c27010002,0xa85bdc2dc5de9c27010006,0x885bdc2dc5dd7c27010008,0x17548997db5887117548d665e21e22f9e37db596026285b102dc5a17df11d0000,0x6677db2678c76c96678c89df6c9db58c77f8df6d7480a8c46e78c40842f6d199e32277db6f92a02a3279e497f7d877f7db5d2023511fe4a8042e029be7880a8c97f9279e2325fe37db580a8c88c72e385bdc52c5a17df16a0000,0x1f7e68972b5d2688adf47f6d5f1d599f54a9a21e688a2357e78c97df5dfe4a809579276d2223588a88a8c711fd7456680410be37db5d267d75f9260276e622222a21e228b85bdc5dcca17df15b0000,0x985bdc5dc5a17df1010002,0xa85bdc2dc5a17df1010004,0x5d74e55d32611e126125326285b102dc5de9df1100000,0x6f6d237f7d748db2748c40842f5d1b2632354e584a6f7db5d2b8df6c98c8d6310210bd746c94ca7db2534f7db5d04e5329fdf61e010b80829b4f8d742a32632231e3113df6d658040842f7db56d32b6d744ca8440842f7d9f6c9d746c98c46f7db5d2310bd934f67f9276808113db48042d32a020a8c88c72e385bdc52c5de9df1a20000,0x7d77d74d37d74c9e202a0220209289d748842b8d7485bdc5dccde9df11c0000])) (.b 112 (.p [0x985bdc5dc5de9df1010002,0xa85bdc2dc5de9df1010004,0x885bdc2dc5dd7df1010006,0x785bdc2dc5dd7de701000c,0xa85bdc0dc5dd7de7010016,0x24489bdc0dc2dd7de7020018,0x7d6aa229fe378c87c97f8df6d47db5d047df5ca88a7dbe34ae326b7c88c92df5aa88a7f8df6d23238db51df7e22b8db48c85f8db5d222b8df6d74b23dc1dc4dd7c274e0000,0x1f56688a7f8df6d631f7db5d2311f5667e21e229f2559971e688a2dddf6d748c475f2959a22842df25fe37db58c7e37db42199df9e31f8d749e32447df88ae37db58c41f8df6b23dc1dc4a17df15d0000,0x1f5d3961113e36d748441f884988a6d329329fe37da32047f8df6d63107e2325f5f8db5d222b8da321f5f8db5d222b8db51d7e36d7488addfe36d745ca7db4ca8c94ca8c97d729b6678c89df1d34f7db5804238df6d6580a8c921f5ca6ab7e321f8c84f8db484a8c97d729fe37d232632075d3d7484988a10b6d3961113e37db5d21107e36d7484a1132b8df48c9b23dc1dc4de9df1bd0000,0x8b23dc1dc4dd7df1010002,0x7df6b23dc0dc2dd7de7030004,0xbb1bdc0dc2dd7de7010006,0x8b1bdc0dc2dcbde7010020,0x1f6d74b1bdc0dc0dcadd3040026,0xbb13dc0dc0dcadd3010032,0x8b13dc0dc0dc4dd301006a]) (.p [0x1f5d04bd1dc0dc0dc0dc104006c]))))
private def data : Store := ⟨vals,rows,model,6,false⟩
def ok := test rule 5 19 data
theorem finish (checked : OMA.Tape245212.Before ok 113) : Deny 5 19 ![⟨2,23584⟩,⟨1,23584⟩,⟨1,23584⟩,⟨1,23584⟩,⟨20,96⟩] := by
  have same : data.vertex 112=![⟨2,23584⟩,⟨1,23584⟩,⟨1,23584⟩,⟨1,23584⟩,⟨20,96⟩] := by decide +kernel
  rw [← same]
  exact close valid _ _ data 112 checked
end OMA.Tape5_19_245212
namespace OMA.Tape5_23_245212
open OMA.Box245212 OMA.DirectTape245212 OMA.TapeShared245212
private def vals := OMA.PageTree245212.get (.b 16 (.p [1,2,3,4,5,6,10,11,15,16,24,25,29,31,32,33]) (.p [34,35,36,37,47,50,51,68,102,103,136,137,11472]))

private def rows := OMA.PageTree245212.get (.b 16 (.p [0x7de1df25f29e6ab7c8e35d2b8c95aa88a7b8df6d23237db51daadfe37db5d23237d748c95aa5b8df6d74888db5d2a88ad047f7db5d23108e37db5d28ce0781e22ab4f0000,0x6d3d748442b8df6d748e8ce0461e27960d0000,0x1fd9d5667e68879a22847f7db5d0b6678c92159a229d7e229529f8c97e32631d99dfe49e37db5d278c79e32550a6809d2688a7559a22999e325de37db58c7df6d0811f75f8842b8d2321f8c97e22b7db58c41f8df6d28ce078472796720000,0x5d74f5d21275d21257db5d22293df5d2127489ac18784e3f96190000,0x7f50ab7e321f8c88c97d6a9f22229f21aadfae322b7e32232475dfe8ae8a8495aa5d67e12572aa887aa222a5b7db5d045fb1cbd22217297e37db5d212621e229f7e32577f92b8dc95f8df68885f8df6d74887df6d7488a8c86dbdf6d7413ae8a6fa2b784784be89da129aadbe37db48c88c76fae36d742b6d748c84f8df6d7484ad6325ace1384e3f16af0000,0x1b6d32b5d1b2532a129329b6676d99e32278c76c99e32276f9df6d74139e4ae792602202f9e49e0780a677db5d2313c6f7d678c92dbe37db58c7de321be37d748c98c74f8df6d7480a8c88dace10c4e3f99640000,0x1fdb5d225dfd748574c984ad748532b44c984988addfd199df8c77e31e32575665d59a22268875ca9a22265dfe4ae4a8095d57d72b8d09d2221fe4ae36d748095f8db5d222b688888788a21ace1387e3f99640000,0x25ace1384e3f99010002,0x1dace1384e3f96010004,0xa122ce0784e3f96020006,0x7d7117238d6229f6f7d748c4278de325fe37da32047f8df6d441f8df6d693e0b85e4357270000,0x7d75c427888a7dbdf5d23109e378c97f8df621fe37db51f5d047df6c94ca8c95d326229f7e32574f8df6d6580988a21f6df2a32574f8df6d2126229f5f8df6d7488a8c81cb6d34f8df6d74808db5d212844cae232574f8df5d21278db5d2229fdf6d7411f5665f7db5d26887d2688a6677c79e32442dfe37d8811fe37db58c41f8df62293e0b85e439baf0000,0x7df6d741292e0784e3f96060002,0x2e8ce0784e3f96010004,0x228ce0784e279601000c,0x9d68ce0781e239602000e]) (.p [0x7df6d7412aae0380e0381060010]))
private def data : Store := ⟨vals,rows,model,5,false⟩
def ok := test rule 5 23 data
theorem finish (checked : OMA.Tape245212.Before ok 17) : Deny 5 23 ![⟨2,11472⟩,⟨1,11472⟩,⟨1,11472⟩,⟨1,11472⟩,⟨24,50⟩] := by
  have same : data.vertex 16=![⟨2,11472⟩,⟨1,11472⟩,⟨1,11472⟩,⟨1,11472⟩,⟨24,50⟩] := by decide +kernel
  rw [← same]
  exact close valid _ _ data 16 checked
end OMA.Tape5_23_245212
namespace OMA.Tape5_29_245212
open OMA.Box245212 OMA.DirectTape245212 OMA.TapeShared245212
private def vals := OMA.PageTree245212.get (.p [1,2,30,34,8400])

private def rows := OMA.PageTree245212.get (.p [0x7d74c988a7dbdf5d232778c97f7d887f7d877f7db42357f7db5d07df6d7411a820821290000])
private def data : Store := ⟨vals,rows,model,3,false⟩
def ok := test rule 5 29 data
theorem finish (checked : OMA.Tape245212.Before ok 1) : Deny 5 29 ![⟨2,8400⟩,⟨1,8400⟩,⟨1,8400⟩,⟨1,8400⟩,⟨30,34⟩] := by
  have same : data.vertex 0=![⟨2,8400⟩,⟨1,8400⟩,⟨1,8400⟩,⟨1,8400⟩,⟨30,34⟩] := by decide +kernel
  rw [← same]
  exact close valid _ _ data 0 checked
end OMA.Tape5_29_245212
namespace OMA.Tape5_31_245212
open OMA.Box245212 OMA.DirectTape245212 OMA.TapeShared245212
private def vals := OMA.PageTree245212.get (.p [1,2,32,7952])

private def rows := OMA.PageTree245212.get (.p [0x4acccd010000])
private def data : Store := ⟨vals,rows,model,2,false⟩
def ok := test rule 5 31 data
theorem finish (checked : OMA.Tape245212.Before ok 1) : Deny 5 31 ![⟨2,7952⟩,⟨1,7952⟩,⟨1,7952⟩,⟨1,7952⟩,⟨32,32⟩] := by
  have same : data.vertex 0=![⟨2,7952⟩,⟨1,7952⟩,⟨1,7952⟩,⟨1,7952⟩,⟨32,32⟩] := by decide +kernel
  rw [← same]
  exact close valid _ _ data 0 checked
end OMA.Tape5_31_245212
namespace OMA.Tape7_11_245212
open OMA.Box245212 OMA.DirectTape245212 OMA.TapeShared245212
private def vals := OMA.PageTree245212.get (.b 16 (.p [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16]) (.b 32 (.p [17,18,19,20,21,22,23,26,30,31,34,35,42,43,86,87]) (.p [5824])))

private def rows := OMA.PageTree245212.get (.b 16 (.p [0x1ef09db5eb6ec888a79e6897a12a325eda321678958aec8e89db588a1dae8af08e8a6b7d6325adf6d631e325cf09ecaf09eca737da321cdf6d631f7da3216e89abb236d7488ad447b7db5d041f8df6d7458c8008018023c76b0000,0x11df6815e49df5f091f7d9df09eca8c7667f07d232559bb1f6d2229d56688add99e325ddf68c7777da31f4088df6d0811c77488a7748c9ecad3c277db5d23107e37db458c800801142810590000,0x17df6d741174e5e87849d959bb1f68885f6d621c22b6d7410be36d7458c040801806810250000,0x13df6d20e48df56fc235e8a8c76d3d7484adf5d096676479fc1c280adb48c84e5e87db5d2129ad1a6f48c8d2321bd212ba2b4f08df6d631f430c8020c18068104b0000,0x3adb4ec85aaec8ec888a5ba27b216db5d222b7887e89ef7db5d22236d6230c142804806690270000,0xef7d748fcdf6d7c1e327673c276d74eca73c27b29cdf6d232231fcd2326323bec8d6229cdf6d74be2f09ddcf09eca737db58c78c7f0973b2bc25cdf6d631f6d2323bdf6d7488adf58c7f3c277d748c9da330c8068043466906c0000,0x3adf6d636b7db5d2bf088c7db4f3c1fc26323ae8984a6b7db5d2bf086bc23a2a31daafc2348c9f36d748c8eb7db5d212a31e330c80624480e690430000,0xeb7db487ae87237db489ff351f6d3bdf5d3a276ec788a888df5eb7db487adf5d3c263237db4ef7db5f36d7bec888a8c7f3c23cf078c78c98c8d7bdf6d56e89df6ec8887eba1e127bec7eb7d7426222228730c80680a80e6906c0000,0x930c80680480e690010002,0x830c806804806690010004,0xa30c802804806690010006,0x3adf6d21e77db5e77db5d39237d74f3c2392a32631e3237db4477db5d26839df5d39247df6d63ef7d748fcdf5f3c2231e3276d7bdf5d39df5e79287276ec888a8c7d199fcf088c7f3c2231e3248d51df6d605f7d74e491f7db5897e89df6efb2a22221f44f923a1e12559bb1fb1f926220a30c80280480681b970000,0x730c802804806810010002,0x2443cc80280180681002000a,0x16e89ec85b6d7488adb5116df6d62107e36d748844d024480880e7151b0000,0x7f57877a325f29f8c97b7db51f7db5d047f6d5edf5d236b7d748da276d1f8c87e12a327679c7e22b47e326321f88a7e32632075aa8961f4aa27e22347e125f88888a2da7f6d2129fdb5d2322311fdf6d748442b88c979a7b6d2b84aadedf6d748c88c95aa5b7db5d2223688a71e29e25e2b7da32047b7db5107e37db51dc7e229fd748c97e22847e3109e36d232044d080a80880e715be0000]) (.b 32 (.p [0x2b8df6d74590802803806714060002,0x1d667777db5d278c7d749e32559a229ddf6d631f7db411ddb5d2256688adf56678dd6678c99e31f59e325d555df9249ed52a21f922229df09e4a777db48c88c98c72d5de2777809dd99dd9e31e78c9777d88777db4204777db58c41f8db4215984577db5d22107e36d7488a667f070a02b4119df5d278c4278df5d2324477bdf5d2229df0974af07df6d2325c777d74be22af737db5d23277da31c4777db48c4238df6d748c41f8df659080280334681de10000,0x1b4f7db5d044f7d7495b4f584a8474f923484984bda12999c46792b7db5d23107e368c84e5844e87e36d749612846daadb2358c7e8a6f7d748c811bdf5d23109e37db58c41f8df45908021c380e81d5f0000,0x5d32765c85c7117db5d0b5ca4e54f9238df68478495665fb238df58875f8df6d74809da2217db5d045aa5c8a97db4888d8b5f8db488a5f8df6d74888db588749014280880e81d540000,0x1f75cdf6d631f7db5d2311fdf675f88addd7c97ca8c98c87f7da3777d9c7e22b7f098c78c8db57e37c9d9cecaf098c88c77e229f8c98c72e321f13becad8be35d222a229ff3c26325fd8a7f7da32047f7db5d23107e37d2326349080680860e79d770000,0x1a7eb84ad2b7e321f84a7e321bdf5d23275d2311fdf5d1b6fa2a12a325adb4adf6fc1fae89db484a8c98c87dbf076f7db5d23237d232632231cb7fa2ba26113ae89df6d748441f8d212a349080644881979d630000,0x1f5d67e22357e12621df8497e2217db588a59fdf5d2221fdf6d74849db5887117df5d1f5fa2612a1276d56aa17f6d3b5ca88a888d9f5fb1d7d7427688a88888788b88a49080681281979d590000,0x949080680881979d010002,0x849080680880e79d010004,0x199d97f680ada78c76678c89dfdf6d748c7d231199e36678c8db59dff36d7cf098c7e79279e491e02a32597cadb57c77cae498c88c72dfe4ae498047f7db5d20108e36d602a349080644860e81f5d0000,0x1fdf675599f55de4ade02622221e22999df65dda02b68c88c77f7db59e680a8c921f75f7c2237db4888d2229fdf6d748c9da32231c47f6d747cadf6d742d59957f92b77f7808df5809d621dfeca7f7da21dfdf6d22237d621dfdf6d74809111566807df6d7499fdb5d392b65777f92897f92a02622221cb88a49080681260e81fa10000,0x949080680860e81f010002,0x7d7df581fd53d97e498089602a0276d577d74f484984a849d9fd9f8875f688a888887117df6d742ca6dbdb5d132a12b7d999dfddbe77db59602a32631e321b7dbe8ad2126129f6f7d748c9da32231c46f92b7db5d0b4d37f7db5d211f7da11dfdf6d74808113df6d74953df6d1fe4a808df54f92212611e12e128949080680881981fa40000,0x849080680880e81f010002,0x749080680880e81d010006,0xa49080280880e81d01000c]) (.p [0x1f7dbdf5d23263257d8a7f7d887f7db51f7db5d0459380280880e81d1b0000,0xb59080280880e81d010002,0x959080280380e81d010010,0x859080280380681d010012,0x7db4590802801806810030014,0xb58c802801806810010018,0xa58c800801806810010024,0x858c800801802810010026,0x7db5d045cb800800800801050028])))
private def data : Store := ⟨vals,rows,model,6,false⟩
def ok := test rule 7 11 data
theorem finish (checked : OMA.Tape245212.Before ok 41) : Deny 7 11 ![⟨2,5824⟩,⟨1,5824⟩,⟨1,5824⟩,⟨1,5824⟩,⟨12,26⟩] := by
  have same : data.vertex 40=![⟨2,5824⟩,⟨1,5824⟩,⟨1,5824⟩,⟨1,5824⟩,⟨12,26⟩] := by decide +kernel
  rw [← same]
  exact close valid _ _ data 40 checked
end OMA.Tape7_11_245212
namespace OMA.Tape7_13_245212
open OMA.Box245212 OMA.DirectTape245212 OMA.TapeShared245212
private def vals := OMA.PageTree245212.get (.p [1,2,14,19,4704])

private def rows := OMA.PageTree245212.get (.p [0x7f7db5d047db4f6d7484adf5d095d3953df6d748478495ca5f7db5d221d7df6d74888db5d0a2dfe37db421fe37db5d07df6d7411a820821450000])
private def data : Store := ⟨vals,rows,model,3,false⟩
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
  simpa only [OMA.CheckedTapes245212.tests, if_pos (show 0+i<189 by omega), show 0+i-0=i by omega] using h
end OMA.Tape5_7_245212
namespace OMA.Tape5_11_245212
open OMA.Box245212
theorem deny5_11 : Deny 5 11 ![⟨2,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨12,999999999999999999⟩] := by
  apply finish
  intro i hi
  have h := OMA.CheckedTapes245212.passed (189+i) (by omega)
  simpa only [OMA.CheckedTapes245212.tests, if_neg (show ¬189+i<189 by omega), if_pos (show 189+i<768 by omega), show 189+i-189=i by omega] using h
end OMA.Tape5_11_245212
namespace OMA.Tape5_13_245212
open OMA.Box245212
theorem deny5_13 : Deny 5 13 ![⟨2,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨1,1920000000000000011376⟩,⟨14,999999999999999999⟩] := by
  apply finish
  intro i hi
  have h := OMA.CheckedTapes245212.passed (768+i) (by omega)
  simpa only [OMA.CheckedTapes245212.tests, if_neg (show ¬768+i<189 by omega), if_neg (show ¬768+i<768 by omega), if_pos (show 768+i<2607 by omega), show 768+i-768=i by omega] using h
end OMA.Tape5_13_245212
namespace OMA.Tape5_17_245212
open OMA.Box245212
theorem deny5_17 : Deny 5 17 ![⟨2,76224⟩,⟨1,76224⟩,⟨1,76224⟩,⟨1,76224⟩,⟨18,256⟩] := by
  apply finish
  intro i hi
  have h := OMA.CheckedTapes245212.passed (2607+i) (by omega)
  simpa only [OMA.CheckedTapes245212.tests, if_neg (show ¬2607+i<189 by omega), if_neg (show ¬2607+i<768 by omega), if_neg (show ¬2607+i<2607 by omega), if_pos (show 2607+i<2790 by omega), show 2607+i-2607=i by omega] using h
end OMA.Tape5_17_245212
namespace OMA.Tape5_19_245212
open OMA.Box245212
theorem deny5_19 : Deny 5 19 ![⟨2,23584⟩,⟨1,23584⟩,⟨1,23584⟩,⟨1,23584⟩,⟨20,96⟩] := by
  apply finish
  intro i hi
  have h := OMA.CheckedTapes245212.passed (2790+i) (by omega)
  simpa only [OMA.CheckedTapes245212.tests, if_neg (show ¬2790+i<189 by omega), if_neg (show ¬2790+i<768 by omega), if_neg (show ¬2790+i<2607 by omega), if_neg (show ¬2790+i<2790 by omega), if_pos (show 2790+i<2903 by omega), show 2790+i-2790=i by omega] using h
end OMA.Tape5_19_245212
namespace OMA.Tape5_23_245212
open OMA.Box245212
theorem deny5_23 : Deny 5 23 ![⟨2,11472⟩,⟨1,11472⟩,⟨1,11472⟩,⟨1,11472⟩,⟨24,50⟩] := by
  apply finish
  intro i hi
  have h := OMA.CheckedTapes245212.passed (2903+i) (by omega)
  simpa only [OMA.CheckedTapes245212.tests, if_neg (show ¬2903+i<189 by omega), if_neg (show ¬2903+i<768 by omega), if_neg (show ¬2903+i<2607 by omega), if_neg (show ¬2903+i<2790 by omega), if_neg (show ¬2903+i<2903 by omega), if_pos (show 2903+i<2920 by omega), show 2903+i-2903=i by omega] using h
end OMA.Tape5_23_245212
namespace OMA.Tape5_29_245212
open OMA.Box245212
theorem deny5_29 : Deny 5 29 ![⟨2,8400⟩,⟨1,8400⟩,⟨1,8400⟩,⟨1,8400⟩,⟨30,34⟩] := by
  apply finish
  intro i hi
  have h := OMA.CheckedTapes245212.passed (2920+i) (by omega)
  simpa only [OMA.CheckedTapes245212.tests, if_neg (show ¬2920+i<189 by omega), if_neg (show ¬2920+i<768 by omega), if_neg (show ¬2920+i<2607 by omega), if_neg (show ¬2920+i<2790 by omega), if_neg (show ¬2920+i<2903 by omega), if_neg (show ¬2920+i<2920 by omega), if_pos (show 2920+i<2921 by omega), show 2920+i-2920=i by omega] using h
end OMA.Tape5_29_245212
namespace OMA.Tape5_31_245212
open OMA.Box245212
theorem deny5_31 : Deny 5 31 ![⟨2,7952⟩,⟨1,7952⟩,⟨1,7952⟩,⟨1,7952⟩,⟨32,32⟩] := by
  apply finish
  intro i hi
  have h := OMA.CheckedTapes245212.passed (2921+i) (by omega)
  simpa only [OMA.CheckedTapes245212.tests, if_neg (show ¬2921+i<189 by omega), if_neg (show ¬2921+i<768 by omega), if_neg (show ¬2921+i<2607 by omega), if_neg (show ¬2921+i<2790 by omega), if_neg (show ¬2921+i<2903 by omega), if_neg (show ¬2921+i<2920 by omega), if_neg (show ¬2921+i<2921 by omega), if_pos (show 2921+i<2922 by omega), show 2921+i-2921=i by omega] using h
end OMA.Tape5_31_245212
namespace OMA.Tape7_11_245212
open OMA.Box245212
theorem deny7_11 : Deny 7 11 ![⟨2,5824⟩,⟨1,5824⟩,⟨1,5824⟩,⟨1,5824⟩,⟨12,26⟩] := by
  apply finish
  intro i hi
  have h := OMA.CheckedTapes245212.passed (2922+i) (by omega)
  simpa only [OMA.CheckedTapes245212.tests, if_neg (show ¬2922+i<189 by omega), if_neg (show ¬2922+i<768 by omega), if_neg (show ¬2922+i<2607 by omega), if_neg (show ¬2922+i<2790 by omega), if_neg (show ¬2922+i<2903 by omega), if_neg (show ¬2922+i<2920 by omega), if_neg (show ¬2922+i<2921 by omega), if_neg (show ¬2922+i<2922 by omega), if_pos (show 2922+i<2963 by omega), show 2922+i-2922=i by omega] using h
end OMA.Tape7_11_245212
namespace OMA.Tape7_13_245212
open OMA.Box245212
theorem deny7_13 : Deny 7 13 ![⟨2,4704⟩,⟨1,4704⟩,⟨1,4704⟩,⟨1,4704⟩,⟨14,19⟩] := by
  apply finish
  intro i hi
  have h := OMA.CheckedTapes245212.passed (2963+i) (by omega)
  simpa only [OMA.CheckedTapes245212.tests, if_neg (show ¬2963+i<189 by omega), if_neg (show ¬2963+i<768 by omega), if_neg (show ¬2963+i<2607 by omega), if_neg (show ¬2963+i<2790 by omega), if_neg (show ¬2963+i<2903 by omega), if_neg (show ¬2963+i<2920 by omega), if_neg (show ¬2963+i<2921 by omega), if_neg (show ¬2963+i<2922 by omega), if_neg (show ¬2963+i<2963 by omega), show 2963+i-2963=i by omega] using h
end OMA.Tape7_13_245212

theorem OMA.solution : OMA.R_OeisA245212_conjecture_R1_H1_R1_H2_R1_H2_R1.H2 :=
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
