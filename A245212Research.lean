import FormalConjectures.OEIS.«245212»

/-! Fixed-support finiteness, uniqueness of a varying exponent, and two mixed-family exclusions for OEIS A245212. The final section proves auxiliary inequalities for the odd-divisor-count bound described in the accompanying note. -/

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

/- Rational interval certificates generated by smooth_boxes_245212.py. -/
namespace OMA.Smooth245212
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def box23 : Box := ![⟨1,none⟩,⟨1,none⟩,⟨0,some 0⟩,⟨0,some 0⟩]
private def tree23 : Tree := (.split 0 3 (.split 0 1 (.split 1 3 (.split 1 1 .leaf (.split 1 2 .leaf .leaf)) (.split 1 9 (.split 1 5 .leaf .leaf) .leaf)) (.split 1 3 (.split 0 2 (.split 1 1 .leaf (.split 1 2 .leaf .leaf)) (.split 1 1 .leaf .leaf)) (.split 0 2 (.split 1 9 .leaf .leaf) .leaf))) (.split 1 3 (.split 0 9 (.split 1 1 .leaf .leaf) .leaf) .leaf))
theorem reject23 {e : I → ℕ} (h : ∀ i,(box23 i).Contains (e i)) : score e ≠ 2 :=
  tree23.sound (by decide +kernel) h

def box25 : Box := ![⟨1,none⟩,⟨0,some 0⟩,⟨1,none⟩,⟨0,some 0⟩]
private def tree25 : Tree := (.split 0 3 (.split 0 1 (.split 2 3 .leaf .leaf) (.split 0 2 (.split 2 3 (.split 2 1 .leaf .leaf) .leaf) (.split 2 3 (.split 2 1 .leaf .leaf) (.split 2 9 .leaf .leaf)))) (.split 0 9 (.split 0 5 (.split 0 4 (.split 2 3 (.split 2 1 .leaf (.split 2 2 .leaf .leaf)) (.split 2 9 (.split 2 5 (.split 2 4 .leaf .leaf) (.split 2 7 .leaf .leaf)) (.split 2 21 (.split 2 13 .leaf .leaf) (.split 2 45 .leaf .leaf)))) (.split 2 3 (.split 2 1 .leaf .leaf) (.split 2 9 .leaf .leaf))) (.split 2 3 (.split 2 1 .leaf .leaf) .leaf)) .leaf))
theorem reject25 {e : I → ℕ} (h : ∀ i,(box25 i).Contains (e i)) : score e ≠ 2 :=
  tree25.sound (by decide +kernel) h

def box27 : Box := ![⟨1,none⟩,⟨0,some 0⟩,⟨0,some 0⟩,⟨1,none⟩]
private def tree27 : Tree := (.split 0 3 (.split 0 1 .leaf (.split 3 3 (.split 3 1 .leaf .leaf) .leaf)) (.split 0 9 (.split 0 5 (.split 0 4 (.split 3 3 (.split 3 1 .leaf .leaf) .leaf) (.split 3 3 (.split 3 1 .leaf .leaf) (.split 3 9 .leaf .leaf))) (.split 0 7 (.split 0 6 (.split 3 3 (.split 3 1 .leaf (.split 3 2 .leaf .leaf)) (.split 3 9 (.split 3 5 (.split 3 4 .leaf .leaf) (.split 3 7 (.split 3 6 .leaf .leaf) (.split 3 8 .leaf .leaf))) (.split 3 21 (.split 3 13 (.split 3 11 (.split 3 10 .leaf .leaf) .leaf) (.split 3 16 (.split 3 14 .leaf .leaf) (.split 3 18 .leaf .leaf))) (.split 3 45 (.split 3 29 (.split 3 25 .leaf .leaf) (.split 3 36 .leaf .leaf)) (.split 3 93 (.split 3 61 .leaf .leaf) (.split 3 189 .leaf .leaf)))))) (.split 3 3 (.split 3 1 .leaf .leaf) (.split 3 9 .leaf .leaf))) (.split 3 3 (.split 3 1 .leaf .leaf) .leaf))) (.split 0 21 (.split 3 3 (.split 0 13 (.split 3 1 .leaf .leaf) .leaf) .leaf) .leaf)))
theorem reject27 {e : I → ℕ} (h : ∀ i,(box27 i).Contains (e i)) : score e ≠ 2 :=
  tree27.sound (by decide +kernel) h

def box235 : Box := ![⟨1,none⟩,⟨1,none⟩,⟨1,none⟩,⟨0,some 0⟩]
private def tree235 : Tree := (.split 0 3 (.split 1 3 (.split 0 1 (.split 1 1 (.split 2 3 (.split 2 1 .leaf .leaf) .leaf) (.split 1 2 (.split 2 3 (.split 2 1 .leaf .leaf) (.split 2 9 (.split 2 5 .leaf .leaf) (.split 2 21 .leaf .leaf))) (.split 2 3 (.split 2 1 .leaf (.split 2 2 .leaf .leaf)) (.split 2 9 (.split 2 5 .leaf .leaf) .leaf)))) (.split 1 1 (.split 0 2 (.split 2 3 (.split 2 1 .leaf .leaf) (.split 2 9 .leaf .leaf)) (.split 2 3 .leaf .leaf)) (.split 2 3 .leaf .leaf))) (.split 0 1 (.split 2 3 (.split 1 9 (.split 2 1 (.split 1 5 (.split 1 4 .leaf .leaf) (.split 1 7 (.split 1 6 .leaf .leaf) .leaf)) (.split 1 5 (.split 2 2 .leaf .leaf) .leaf)) (.split 2 1 (.split 1 21 (.split 1 13 .leaf .leaf) .leaf) .leaf)) .leaf) .leaf)) .leaf)
theorem reject235 {e : I → ℕ} (h : ∀ i,(box235 i).Contains (e i)) : score e ≠ 2 :=
  tree235.sound (by decide +kernel) h

def box237 : Box := ![⟨1,none⟩,⟨1,none⟩,⟨0,some 0⟩,⟨1,none⟩]
private def tree237 : Tree := (.split 0 3 (.split 1 3 (.split 0 1 (.split 1 1 .leaf (.split 1 2 (.split 3 3 .leaf .leaf) (.split 3 3 .leaf .leaf))) (.split 1 1 (.split 0 2 (.split 3 3 (.split 3 1 .leaf .leaf) (.split 3 9 .leaf .leaf)) (.split 3 3 .leaf .leaf)) (.split 0 2 (.split 1 2 (.split 3 3 (.split 3 1 .leaf .leaf) .leaf) (.split 3 3 .leaf .leaf)) .leaf))) (.split 0 1 (.split 1 9 (.split 1 5 (.split 3 3 (.split 3 1 .leaf (.split 1 4 .leaf .leaf)) (.split 1 4 (.split 3 9 .leaf .leaf) (.split 3 9 (.split 3 5 .leaf (.split 3 7 .leaf .leaf)) (.split 3 21 (.split 3 13 (.split 3 11 .leaf .leaf) (.split 3 16 (.split 3 14 .leaf .leaf) (.split 3 18 (.split 3 17 .leaf .leaf) (.split 3 19 .leaf (.split 3 20 .leaf .leaf))))) (.split 3 45 (.split 3 29 (.split 3 25 (.split 3 23 .leaf .leaf) .leaf) (.split 3 36 .leaf .leaf)) (.split 3 93 .leaf .leaf)))))) (.split 3 3 (.split 3 1 (.split 1 7 .leaf .leaf) (.split 1 7 (.split 3 2 .leaf (.split 1 6 .leaf .leaf)) (.split 3 2 (.split 1 8 .leaf .leaf) .leaf))) (.split 1 7 (.split 3 9 (.split 3 5 (.split 1 6 (.split 3 4 .leaf .leaf) .leaf) (.split 1 6 .leaf .leaf)) .leaf) (.split 3 9 .leaf .leaf)))) (.split 3 3 (.split 3 1 (.split 1 21 (.split 1 13 .leaf (.split 1 16 .leaf .leaf)) (.split 1 45 (.split 1 29 (.split 1 25 .leaf .leaf) (.split 1 36 (.split 1 32 .leaf (.split 1 34 .leaf .leaf)) (.split 1 40 (.split 1 38 (.split 1 37 .leaf .leaf) (.split 1 39 .leaf .leaf)) (.split 1 42 (.split 1 41 .leaf .leaf) .leaf)))) (.split 1 93 (.split 1 61 (.split 1 52 (.split 1 48 .leaf .leaf) .leaf) (.split 1 74 .leaf .leaf)) (.split 1 189 .leaf .leaf)))) (.split 1 21 (.split 1 13 (.split 3 2 .leaf .leaf) .leaf) .leaf)) .leaf)) .leaf)) .leaf)
theorem reject237 {e : I → ℕ} (h : ∀ i,(box237 i).Contains (e i)) : score e ≠ 2 :=
  tree237.sound (by decide +kernel) h

def box257 : Box := ![⟨1,none⟩,⟨0,some 0⟩,⟨1,none⟩,⟨1,none⟩]
private def tree257 : Tree := (.split 0 3 (.split 0 1 (.split 2 3 .leaf .leaf) (.split 2 3 (.split 0 2 (.split 2 1 (.split 3 3 .leaf .leaf) (.split 3 3 .leaf .leaf)) (.split 2 1 (.split 3 3 (.split 3 1 .leaf .leaf) (.split 3 9 .leaf .leaf)) (.split 3 3 (.split 3 1 (.split 2 2 .leaf .leaf) (.split 2 2 (.split 3 2 .leaf .leaf) .leaf)) (.split 2 2 (.split 3 9 .leaf .leaf) .leaf)))) (.split 3 3 (.split 0 2 (.split 3 1 .leaf (.split 2 9 .leaf (.split 3 2 .leaf .leaf))) (.split 3 1 (.split 2 9 (.split 2 5 .leaf .leaf) .leaf) .leaf)) (.split 0 2 (.split 2 9 (.split 2 5 (.split 3 9 .leaf .leaf) (.split 3 9 (.split 3 5 .leaf .leaf) (.split 3 21 (.split 2 7 .leaf (.split 3 13 .leaf (.split 3 16 (.split 2 8 .leaf (.split 3 14 .leaf .leaf)) (.split 2 8 .leaf (.split 3 18 .leaf .leaf))))) (.split 2 7 (.split 3 45 .leaf (.split 2 6 .leaf (.split 3 93 (.split 3 61 .leaf .leaf) (.split 3 189 (.split 3 125 .leaf (.split 3 151 (.split 3 137 .leaf .leaf) (.split 3 168 (.split 3 159 (.split 3 155 .leaf (.split 3 157 .leaf .leaf)) (.split 3 163 (.split 3 161 (.split 3 160 .leaf .leaf) .leaf) .leaf)) .leaf))) (.split 3 381 (.split 3 253 .leaf .leaf) .leaf))))) (.split 3 45 (.split 2 8 (.split 3 29 (.split 3 25 .leaf (.split 3 27 (.split 3 26 .leaf .leaf) .leaf)) (.split 3 36 .leaf .leaf)) .leaf) .leaf))))) (.split 3 9 (.split 2 21 (.split 3 5 (.split 2 13 .leaf .leaf) (.split 2 13 (.split 3 7 .leaf (.split 2 11 .leaf (.split 3 8 .leaf (.split 2 12 .leaf .leaf)))) (.split 3 7 (.split 2 16 (.split 3 6 .leaf (.split 2 14 .leaf .leaf)) (.split 3 6 (.split 2 18 .leaf .leaf) (.split 2 18 .leaf .leaf))) (.split 2 16 (.split 2 14 (.split 3 8 .leaf .leaf) .leaf) .leaf)))) (.split 3 5 (.split 2 45 (.split 3 4 .leaf (.split 2 29 .leaf (.split 2 36 .leaf (.split 2 40 (.split 2 38 .leaf .leaf) (.split 2 42 (.split 2 41 .leaf .leaf) .leaf))))) (.split 3 4 (.split 2 93 .leaf .leaf) (.split 2 93 (.split 2 61 .leaf .leaf) .leaf))) (.split 2 45 (.split 3 7 (.split 2 29 (.split 3 6 (.split 2 25 (.split 2 23 (.split 2 22 .leaf .leaf) .leaf) .leaf) .leaf) .leaf) .leaf) .leaf))) (.split 2 21 (.split 3 21 (.split 2 13 (.split 3 13 (.split 2 11 (.split 3 11 (.split 2 10 .leaf (.split 3 10 .leaf .leaf)) (.split 2 10 (.split 3 12 .leaf .leaf) .leaf)) (.split 3 11 .leaf .leaf)) (.split 2 11 (.split 3 16 .leaf .leaf) .leaf)) .leaf) .leaf) .leaf))) .leaf)))) (.split 0 9 (.split 2 3 (.split 0 5 (.split 2 1 (.split 0 4 (.split 3 3 (.split 3 1 .leaf .leaf) .leaf) (.split 3 3 .leaf .leaf)) (.split 3 3 .leaf .leaf)) .leaf) .leaf) .leaf))
theorem reject257 {e : I → ℕ} (h : ∀ i,(box257 i).Contains (e i)) : score e ≠ 2 :=
  tree257.sound (by decide +kernel) h

def box2357 : Box := ![⟨1,none⟩,⟨1,none⟩,⟨1,none⟩,⟨1,none⟩]
private def tree2357 : Tree := (.split 0 3 (.split 1 3 (.split 0 1 (.split 2 3 (.split 1 1 (.split 2 1 (.split 3 3 .leaf .leaf) (.split 3 3 (.split 3 1 .leaf .leaf) (.split 2 2 .leaf (.split 3 9 .leaf (.split 3 21 .leaf (.split 3 45 .leaf .leaf)))))) (.split 2 1 (.split 1 2 (.split 3 3 (.split 3 1 .leaf (.split 3 2 .leaf .leaf)) (.split 3 9 (.split 3 5 (.split 3 4 .leaf .leaf) (.split 3 7 .leaf .leaf)) (.split 3 21 .leaf .leaf))) (.split 3 3 (.split 3 1 .leaf .leaf) .leaf)) (.split 3 3 (.split 1 2 (.split 3 1 (.split 2 2 .leaf .leaf) .leaf) .leaf) .leaf))) (.split 1 1 (.split 3 3 (.split 3 1 (.split 2 9 .leaf .leaf) (.split 2 9 (.split 2 5 (.split 3 2 .leaf .leaf) (.split 3 2 .leaf (.split 2 7 (.split 2 6 .leaf .leaf) (.split 2 8 .leaf .leaf)))) (.split 2 21 (.split 3 2 (.split 2 13 .leaf (.split 2 16 .leaf .leaf)) .leaf) (.split 3 2 (.split 2 45 (.split 2 29 (.split 2 25 (.split 2 23 .leaf .leaf) (.split 2 27 .leaf (.split 2 28 .leaf .leaf))) (.split 2 36 (.split 2 32 .leaf .leaf) .leaf)) (.split 2 93 .leaf .leaf)) .leaf)))) (.split 2 9 (.split 3 9 (.split 2 5 (.split 3 5 (.split 2 4 .leaf (.split 3 4 .leaf .leaf)) (.split 2 4 (.split 3 7 .leaf (.split 3 8 .leaf .leaf)) .leaf)) (.split 3 5 (.split 2 7 (.split 3 4 .leaf .leaf) .leaf) .leaf)) (.split 2 5 (.split 3 21 (.split 2 4 (.split 3 13 .leaf .leaf) .leaf) .leaf) .leaf)) .leaf)) .leaf)) (.split 2 3 (.split 1 1 (.split 0 2 (.split 2 1 (.split 3 3 .leaf .leaf) .leaf) .leaf) .leaf) .leaf)) (.split 0 1 (.split 2 3 (.split 1 9 (.split 3 3 (.split 2 1 .leaf .leaf) .leaf) .leaf) .leaf) .leaf)) .leaf)
theorem reject2357 {e : I → ℕ} (h : ∀ i,(box2357 i).Contains (e i)) : score e ≠ 2 :=
  tree2357.sound (by decide +kernel) h

end OMA.Smooth245212

/- No even number with nontrivial odd part supported on 3,5,7 is an
extra equality in A245212. All four exponents are unrestricted above. -/
namespace OMA.Smooth245212
open scoped ArithmeticFunction.sigma

theorem mixed {a b c d : ℕ} (ha : 0<a) (oddpart : 0<b+c+d) :
    OeisA245212.a (2^a*3^b*5^c*7^d) ≠ (σ 1 (2^a*3^b*5^c*7^d) : ℤ) := by
  let e : I → ℕ := ![a,b,c,d]
  have value : number e = 2^a*3^b*5^c*7^d := by
    simp [number,Fin.prod_univ_four,prime,e]
  intro eq
  have h := score_of_eq e (value ▸ eq)
  rcases Nat.eq_zero_or_pos b with hb|hb <;> rcases Nat.eq_zero_or_pos c with hc|hc <;>
      rcases Nat.eq_zero_or_pos d with hd|hd
  · omega
  · apply reject27 (e:=e) _ h; intro i; fin_cases i <;> simp [box27,Band.Contains,e] <;> omega
  · apply reject25 (e:=e) _ h; intro i; fin_cases i <;> simp [box25,Band.Contains,e] <;> omega
  · apply reject257 (e:=e) _ h; intro i; fin_cases i <;> simp [box257,Band.Contains,e] <;> omega
  · apply reject23 (e:=e) _ h; intro i; fin_cases i <;> simp [box23,Band.Contains,e] <;> omega
  · apply reject237 (e:=e) _ h; intro i; fin_cases i <;> simp [box237,Band.Contains,e] <;> omega
  · apply reject235 (e:=e) _ h; intro i; fin_cases i <;> simp [box235,Band.Contains,e] <;> omega
  · apply reject2357 (e:=e) _ h; intro i; fin_cases i <;> simp [box2357,Band.Contains,e] <;> omega

end OMA.Smooth245212

/- Variable-base interval bounds for the normalized divisor factors. For
large exponents the geometric remainder is enclosed using only the 32nd power. -/
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

/- A certificate for a box of four integer coordinates: three exponents
and the last prime. A singleton interval containing a composite is empty. -/
namespace OMA.Moving245212
open Finset OMA.Smooth245212

def single (p : ℕ) : Band := ⟨p,some p⟩
def primes (e : I → ℕ) : Fin 3 → ℕ := ![2,3,e 3]
def base (b : Box) : Fin 3 → Band := ![single 2,single 3,b 3]
def value (e : I → ℕ) : ℚ :=
  (∏ i:Fin 3, X (primes e i) (some (e i.castSucc)))+
    ∏ i:Fin 3, Y (primes e i) (some (e i.castSucc))
def lower (b : Box) : ℚ := (∏ i:Fin 3, xl (base b i) (b i.castSucc))+
    ∏ i:Fin 3, yl (base b i) (b i.castSucc)
def upper (b : Box) : ℚ := (∏ i:Fin 3, xu (base b i) (b i.castSucc))+
    ∏ i:Fin 3, yu (base b i) (b i.castSucc)

theorem enclose {b : Box} {e : I → ℕ} (hq : 1<(b 3).lo)
    (h : ∀ i, (b i).Contains (e i)) : lower b ≤ value e ∧ value e ≤ upper b := by
  have low (i : Fin 3) : 1<(base b i).lo := by
    fin_cases i <;> simp [base,single,hq]
  have hits (i : Fin 3) : (base b i).Contains (primes e i) := by
    fin_cases i <;> simp [base,primes,single,Band.Contains]
    exact h 3
  have v (i : Fin 3) := factor_bounds (low i) (hits i) (h i.castSucc)
  constructor
  · exact add_le_add
      (prod_le_prod (fun i _ => (v i).1) (fun i _ => (v i).2.1))
      (prod_le_prod (fun i _ => (v i).2.2.2.1) (fun i _ => (v i).2.2.2.2.1))
  · exact add_le_add
      (prod_le_prod (fun i _ => (v i).1.trans (v i).2.1) (fun i _ => (v i).2.2.1))
      (prod_le_prod (fun i _ => (v i).2.2.2.1.trans (v i).2.2.2.2.1)
        (fun i _ => (v i).2.2.2.2.2))

def check : Tree → Box → Bool
| .leaf,b => decide (((b 3).hi = some (b 3).lo ∧ ¬Nat.Prime (b 3).lo) ∨
    1<(b 3).lo ∧ (2<lower b ∨ upper b<2))
| .split i cut l r,b => check l (left b i cut) && check r (right b i cut)

theorem reject (t : Tree) {b : Box} (cert : check t b=true)
    {e : I → ℕ} (h : ∀ i,(b i).Contains (e i)) (prime : Nat.Prime (e 3)) : value e≠2 := by
  induction t generalizing b with
  | leaf =>
    rcases of_decide_eq_true cert with ⟨same,comp⟩|⟨good,larger|smaller⟩
    · exact (comp ((Nat.le_antisymm (h 3).1 ((h 3).2 _ same)).symm ▸ prime)).elim
    · exact (larger.trans_le (enclose good h).1).ne'
    · exact ((enclose good h).2.trans_lt smaller).ne
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

def Excluded (b : Box) : Prop := ∀ e : I → ℕ, (∀ i,(b i).Contains (e i)) →
  Nat.Prime (e 3) → value e ≠ 2

theorem bisect (b : Box) (i : I) (cut : ℕ)
    (hl : Excluded (left b i cut)) (hr : Excluded (right b i cut)) : Excluded b := by
  intro e h
  by_cases ec : e i≤cut
  · apply hl
    intro j; by_cases ji : j=i
    · subst j; simpa [left,Band.Contains] using And.intro (h i).1 ec
    · simpa [left,ji] using h j
  · apply hr
    intro j; by_cases ji : j=i
    · subst j; simpa [right,Band.Contains] using And.intro (by omega : cut+1≤e i) (h i).2
    · simpa [right,ji] using h j

end OMA.Moving245212

/- Generated by mixed_three_245212.py 3 --lean. -/
namespace OMA.Moving245212
open OMA.Smooth245212
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def domain : Box := ![⟨1,none⟩,⟨1,none⟩,⟨1,none⟩,⟨4,none⟩]
private def bl : Box := left domain 0 3
private def bll : Box := left bl 1 3
private def blll : Box := left bll 3 9
private def bllll : Box := left blll 2 3
private def tllll : Tree := (.split 0 1 (.split 1 1 (.split 2 1 .leaf (.split 3 5 (.split 2 2 .leaf .leaf) .leaf)) (.split 2 1 (.split 3 5 (.split 1 2 (.split 3 4 .leaf .leaf) (.split 3 4 .leaf .leaf)) (.split 1 2 .leaf .leaf)) (.split 3 5 (.split 1 2 (.split 2 2 (.split 3 4 .leaf .leaf) (.split 3 4 .leaf .leaf)) (.split 3 4 .leaf (.split 2 2 .leaf .leaf))) (.split 1 2 .leaf .leaf)))) (.split 1 1 (.split 2 1 (.split 0 2 (.split 3 5 .leaf (.split 3 7 (.split 3 6 .leaf .leaf) .leaf)) .leaf) (.split 3 5 (.split 0 2 .leaf .leaf) (.split 0 2 (.split 3 7 (.split 2 2 (.split 3 6 .leaf .leaf) (.split 3 6 .leaf .leaf)) .leaf) .leaf))) (.split 3 5 .leaf (.split 0 2 (.split 2 1 (.split 1 2 .leaf .leaf) (.split 1 2 (.split 3 7 .leaf .leaf) .leaf)) .leaf))))
private theorem cllll : Excluded bllll := fun _ h => reject tllll (by decide +kernel) h
private def blllr : Box := right blll 2 3
private def tlllr : Tree := (.split 0 1 (.split 3 5 (.split 1 1 (.split 2 9 (.split 2 5 .leaf .leaf) (.split 3 4 .leaf .leaf)) (.split 2 9 (.split 2 5 (.split 1 2 (.split 3 4 .leaf .leaf) .leaf) (.split 3 4 .leaf (.split 1 2 .leaf .leaf))) (.split 3 4 .leaf (.split 1 2 (.split 2 21 .leaf .leaf) .leaf)))) (.split 1 1 .leaf (.split 2 9 (.split 3 7 (.split 1 2 .leaf (.split 2 5 .leaf .leaf)) .leaf) (.split 3 7 (.split 1 2 .leaf (.split 2 21 .leaf .leaf)) .leaf)))) (.split 3 5 (.split 1 1 (.split 2 9 (.split 0 2 .leaf .leaf) .leaf) .leaf) (.split 1 1 (.split 2 9 (.split 0 2 (.split 3 7 (.split 2 5 (.split 3 6 .leaf .leaf) (.split 3 6 .leaf .leaf)) .leaf) (.split 3 7 .leaf (.split 2 5 .leaf .leaf))) (.split 0 2 (.split 3 7 (.split 2 21 (.split 3 6 .leaf .leaf) (.split 3 6 .leaf .leaf)) .leaf) (.split 3 7 .leaf (.split 2 21 .leaf (.split 3 8 .leaf .leaf))))) (.split 0 2 (.split 2 9 (.split 3 7 .leaf (.split 1 2 (.split 2 5 .leaf .leaf) .leaf)) (.split 3 7 .leaf (.split 1 2 (.split 2 21 (.split 3 8 .leaf .leaf) (.split 3 8 .leaf .leaf)) .leaf))) .leaf))))
private theorem clllr : Excluded blllr := fun _ h => reject tlllr (by decide +kernel) h
private theorem clll : Excluded blll := bisect blll 2 3 cllll clllr
private def bllr : Box := right bll 3 9
private def bllrl : Box := left bllr 0 1
private def tllrl : Tree := (.split 2 3 (.split 1 1 .leaf .leaf) .leaf)
private theorem cllrl : Excluded bllrl := fun _ h => reject tllrl (by decide +kernel) h
private def bllrr : Box := right bllr 0 1
private def bllrrl : Box := left bllrr 1 1
private def tllrrl : Tree := (.split 2 3 (.split 0 2 (.split 2 1 .leaf .leaf) (.split 3 21 (.split 2 1 (.split 3 13 .leaf (.split 3 16 .leaf (.split 3 18 .leaf .leaf))) (.split 3 13 (.split 2 2 (.split 3 11 .leaf (.split 3 12 .leaf .leaf)) (.split 3 11 .leaf .leaf)) .leaf)) (.split 2 1 .leaf .leaf))) (.split 3 21 (.split 0 2 .leaf (.split 2 9 (.split 3 13 (.split 2 5 (.split 3 11 (.split 2 4 (.split 3 10 .leaf .leaf) (.split 3 10 .leaf .leaf)) .leaf) (.split 3 11 (.split 2 7 (.split 3 10 .leaf .leaf) (.split 3 10 .leaf .leaf)) .leaf)) .leaf) (.split 3 13 (.split 2 21 (.split 3 11 (.split 2 13 (.split 3 10 .leaf .leaf) .leaf) .leaf) (.split 3 11 (.split 2 45 .leaf .leaf) .leaf)) .leaf))) .leaf))
private theorem cllrrl : Excluded bllrrl := fun _ h => reject tllrrl (by decide +kernel) h
private def bllrrr : Box := right bllrr 1 1
private def bllrrrl : Box := left bllrrr 2 3
private def tllrrrl : Tree := (.split 0 2 (.split 3 21 (.split 2 1 (.split 1 2 (.split 3 13 .leaf .leaf) .leaf) (.split 1 2 (.split 3 13 (.split 2 2 (.split 3 11 (.split 3 10 .leaf .leaf) .leaf) (.split 3 11 (.split 3 10 .leaf .leaf) .leaf)) .leaf) (.split 3 13 .leaf (.split 3 16 (.split 2 2 .leaf .leaf) (.split 2 2 (.split 3 18 .leaf (.split 3 19 .leaf (.split 3 20 .leaf .leaf))) (.split 3 18 .leaf .leaf)))))) (.split 1 2 .leaf (.split 2 1 (.split 3 45 (.split 3 29 .leaf (.split 3 36 (.split 3 32 .leaf (.split 3 34 .leaf (.split 3 35 .leaf .leaf))) .leaf)) .leaf) (.split 3 45 (.split 3 29 (.split 2 2 .leaf .leaf) .leaf) .leaf)))) (.split 3 21 .leaf (.split 1 2 (.split 2 1 .leaf (.split 3 45 .leaf (.split 3 93 (.split 2 2 .leaf .leaf) (.split 2 2 .leaf (.split 3 189 (.split 3 125 (.split 3 107 (.split 3 100 (.split 3 96 .leaf (.split 3 98 .leaf .leaf)) .leaf) .leaf) .leaf) .leaf))))) .leaf)))
private theorem cllrrrl : Excluded bllrrrl := fun _ h => reject tllrrrl (by decide +kernel) h
private def bllrrrr : Box := right bllrrr 2 3
private def bllrrrrl : Box := left bllrrrr 3 21
private def tllrrrrl : Tree := (.split 0 2 (.split 3 13 (.split 2 9 (.split 1 2 (.split 2 5 (.split 3 11 (.split 2 4 (.split 3 10 .leaf .leaf) .leaf) .leaf) (.split 3 11 (.split 2 7 .leaf .leaf) .leaf)) .leaf) (.split 1 2 (.split 3 11 (.split 2 21 (.split 2 13 .leaf .leaf) .leaf) .leaf) .leaf)) (.split 1 2 .leaf (.split 2 9 (.split 3 16 (.split 2 5 (.split 3 14 .leaf (.split 2 4 .leaf .leaf)) (.split 3 14 .leaf (.split 2 7 (.split 3 15 .leaf .leaf) (.split 3 15 .leaf .leaf)))) (.split 2 5 (.split 3 18 (.split 2 4 (.split 3 17 .leaf .leaf) .leaf) .leaf) .leaf)) (.split 3 16 (.split 2 21 (.split 3 14 .leaf (.split 2 13 (.split 3 15 .leaf .leaf) (.split 3 15 .leaf .leaf))) (.split 3 14 .leaf (.split 2 45 (.split 3 15 .leaf .leaf) (.split 3 15 .leaf .leaf)))) .leaf)))) .leaf)
private theorem cllrrrrl : Excluded bllrrrrl := fun _ h => reject tllrrrrl (by decide +kernel) h
private def bllrrrrr : Box := right bllrrrr 3 21
private def bllrrrrrl : Box := left bllrrrrr 0 2
private def tllrrrrrl : Tree := (.split 1 2 .leaf .leaf)
private theorem cllrrrrrl : Excluded bllrrrrrl := fun _ h => reject tllrrrrrl (by decide +kernel) h
private def bllrrrrrr : Box := right bllrrrrr 0 2
private def bllrrrrrrl : Box := left bllrrrrrr 1 2
private def bllrrrrrrll : Box := left bllrrrrrrl 3 45
private def bllrrrrrrlll : Box := left bllrrrrrrll 2 9
private def tllrrrrrrlll : Tree := (.split 3 29 .leaf (.split 2 5 .leaf (.split 3 36 (.split 2 7 .leaf .leaf) (.split 2 7 (.split 3 40 (.split 2 6 .leaf .leaf) (.split 2 6 (.split 3 42 .leaf (.split 3 43 .leaf .leaf)) .leaf)) (.split 3 40 (.split 3 38 (.split 2 8 .leaf .leaf) .leaf) .leaf)))))
private theorem cllrrrrrrlll : Excluded bllrrrrrrlll := fun _ h => reject tllrrrrrrlll (by decide +kernel) h
private def bllrrrrrrllr : Box := right bllrrrrrrll 2 9
private def tllrrrrrrllr : Tree := (.split 3 29 (.split 2 21 .leaf (.split 3 25 .leaf (.split 2 45 (.split 3 27 .leaf (.split 2 29 .leaf (.split 2 36 .leaf .leaf))) (.split 3 27 .leaf (.split 2 93 (.split 2 61 (.split 3 28 .leaf (.split 2 52 (.split 2 48 .leaf .leaf) (.split 2 56 (.split 2 54 .leaf (.split 2 55 .leaf .leaf)) .leaf))) (.split 3 28 .leaf (.split 2 74 .leaf .leaf))) (.split 2 189 (.split 3 28 .leaf .leaf) (.split 3 28 .leaf .leaf))))))) (.split 2 21 (.split 3 36 (.split 2 13 (.split 3 32 .leaf (.split 2 11 (.split 3 34 .leaf (.split 2 10 (.split 3 35 .leaf .leaf) .leaf)) (.split 3 34 (.split 3 33 .leaf .leaf) .leaf))) (.split 3 32 (.split 2 16 (.split 3 30 .leaf (.split 2 14 .leaf .leaf)) (.split 3 30 .leaf (.split 2 18 (.split 3 31 .leaf .leaf) (.split 3 31 (.split 2 19 .leaf (.split 2 20 .leaf .leaf)) .leaf)))) (.split 2 16 (.split 3 34 (.split 2 14 .leaf .leaf) .leaf) .leaf))) (.split 2 13 .leaf .leaf)) (.split 3 36 (.split 2 45 (.split 3 32 (.split 2 29 (.split 3 30 .leaf (.split 2 25 (.split 3 31 (.split 2 23 .leaf .leaf) .leaf) .leaf)) (.split 3 30 .leaf .leaf)) .leaf) .leaf) .leaf)))
private theorem cllrrrrrrllr : Excluded bllrrrrrrllr := fun _ h => reject tllrrrrrrllr (by decide +kernel) h
private theorem cllrrrrrrll : Excluded bllrrrrrrll := bisect bllrrrrrrll 2 9 cllrrrrrrlll cllrrrrrrllr
private def bllrrrrrrlr : Box := right bllrrrrrrl 3 45
private def tllrrrrrrlr : Tree := (.split 2 9 (.split 3 93 (.split 2 5 (.split 3 61 (.split 2 4 (.split 3 52 .leaf (.split 3 56 .leaf (.split 3 58 .leaf (.split 3 59 .leaf (.split 3 60 .leaf .leaf))))) (.split 3 52 (.split 3 48 .leaf .leaf) .leaf)) (.split 3 74 (.split 2 4 .leaf .leaf) .leaf)) .leaf) .leaf) .leaf)
private theorem cllrrrrrrlr : Excluded bllrrrrrrlr := fun _ h => reject tllrrrrrrlr (by decide +kernel) h
private theorem cllrrrrrrl : Excluded bllrrrrrrl := bisect bllrrrrrrl 3 45 cllrrrrrrll cllrrrrrrlr
private def bllrrrrrrr : Box := right bllrrrrrr 1 2
private def tllrrrrrrr : Tree := .leaf
private theorem cllrrrrrrr : Excluded bllrrrrrrr := fun _ h => reject tllrrrrrrr (by decide +kernel) h
private theorem cllrrrrrr : Excluded bllrrrrrr := bisect bllrrrrrr 1 2 cllrrrrrrl cllrrrrrrr
private theorem cllrrrrr : Excluded bllrrrrr := bisect bllrrrrr 0 2 cllrrrrrl cllrrrrrr
private theorem cllrrrr : Excluded bllrrrr := bisect bllrrrr 3 21 cllrrrrl cllrrrrr
private theorem cllrrr : Excluded bllrrr := bisect bllrrr 2 3 cllrrrl cllrrrr
private theorem cllrr : Excluded bllrr := bisect bllrr 1 1 cllrrl cllrrr
private theorem cllr : Excluded bllr := bisect bllr 0 1 cllrl cllrr
private theorem cll : Excluded bll := bisect bll 3 9 clll cllr
private def blr : Box := right bl 1 3
private def blrl : Box := left blr 3 9
private def blrll : Box := left blrl 0 1
private def blrlll : Box := left blrll 2 3
private def blrllll : Box := left blrlll 1 9
private def tlrllll : Tree := (.split 3 5 (.split 2 1 (.split 1 5 (.split 1 4 (.split 3 4 .leaf .leaf) (.split 3 4 .leaf .leaf)) (.split 1 7 (.split 3 4 .leaf (.split 1 6 .leaf .leaf)) .leaf)) (.split 1 5 (.split 3 4 .leaf (.split 2 2 .leaf .leaf)) .leaf)) (.split 1 5 (.split 2 1 (.split 1 4 .leaf .leaf) (.split 3 7 (.split 2 2 (.split 1 4 .leaf (.split 3 6 .leaf .leaf)) (.split 1 4 .leaf (.split 3 6 .leaf .leaf))) .leaf)) (.split 2 1 (.split 1 7 (.split 3 7 (.split 1 6 .leaf .leaf) .leaf) (.split 3 7 (.split 3 6 .leaf .leaf) .leaf)) (.split 3 7 (.split 1 7 (.split 2 2 (.split 3 6 .leaf .leaf) (.split 3 6 .leaf (.split 1 6 .leaf .leaf))) (.split 2 2 (.split 3 6 .leaf (.split 1 8 .leaf .leaf)) .leaf)) (.split 1 7 .leaf (.split 2 2 .leaf .leaf))))))
private theorem clrllll : Excluded blrllll := fun _ h => reject tlrllll (by decide +kernel) h
private def blrlllr : Box := right blrlll 1 9
private def blrlllrl : Box := left blrlllr 3 5
private def tlrlllrl : Tree := (.split 2 1 (.split 1 21 (.split 1 13 .leaf .leaf) .leaf) .leaf)
private theorem clrlllrl : Excluded blrlllrl := fun _ h => reject tlrlllrl (by decide +kernel) h
private def blrlllrr : Box := right blrlllr 3 5
private def tlrlllrr : Tree := (.split 1 21 (.split 2 1 (.split 1 13 (.split 3 7 (.split 1 11 (.split 3 6 .leaf .leaf) (.split 3 6 .leaf .leaf)) .leaf) (.split 3 7 (.split 1 16 (.split 3 6 .leaf .leaf) (.split 3 6 .leaf .leaf)) .leaf)) (.split 3 7 (.split 1 13 (.split 2 2 .leaf .leaf) .leaf) (.split 1 13 (.split 2 2 (.split 1 11 .leaf (.split 3 8 .leaf .leaf)) (.split 1 11 (.split 3 8 .leaf .leaf) (.split 3 8 .leaf .leaf))) (.split 2 2 (.split 1 16 (.split 3 8 .leaf .leaf) (.split 3 8 .leaf .leaf)) (.split 1 16 (.split 3 8 .leaf .leaf) .leaf))))) (.split 2 1 (.split 1 45 (.split 3 7 (.split 1 29 (.split 3 6 .leaf (.split 1 25 .leaf .leaf)) (.split 3 6 .leaf (.split 1 36 (.split 1 32 .leaf (.split 1 34 .leaf .leaf)) (.split 1 40 (.split 1 38 (.split 1 37 .leaf .leaf) (.split 1 39 .leaf .leaf)) (.split 1 42 (.split 1 41 .leaf .leaf) .leaf))))) .leaf) (.split 3 7 (.split 1 93 (.split 3 6 .leaf (.split 1 61 (.split 1 52 (.split 1 48 .leaf .leaf) .leaf) (.split 1 74 .leaf .leaf))) (.split 3 6 .leaf (.split 1 189 .leaf .leaf))) (.split 1 93 .leaf (.split 1 189 .leaf .leaf)))) (.split 3 7 .leaf (.split 1 45 (.split 1 29 (.split 2 2 (.split 3 8 .leaf .leaf) .leaf) (.split 2 2 (.split 3 8 .leaf .leaf) .leaf)) (.split 1 93 .leaf .leaf)))))
private theorem clrlllrr : Excluded blrlllrr := fun _ h => reject tlrlllrr (by decide +kernel) h
private theorem clrlllr : Excluded blrlllr := bisect blrlllr 3 5 clrlllrl clrlllrr
private theorem clrlll : Excluded blrlll := bisect blrlll 1 9 clrllll clrlllr
private def blrllr : Box := right blrll 2 3
private def blrllrl : Box := left blrllr 3 5
private def tlrllrl : Tree := (.split 1 9 (.split 2 9 .leaf .leaf) .leaf)
private theorem clrllrl : Excluded blrllrl := fun _ h => reject tlrllrl (by decide +kernel) h
private def blrllrr : Box := right blrllr 3 5
private def blrllrrl : Box := left blrllrr 1 9
private def tlrllrrl : Tree := (.split 2 9 (.split 1 5 (.split 3 7 (.split 2 5 (.split 3 6 .leaf (.split 1 4 .leaf .leaf)) (.split 3 6 .leaf (.split 1 4 .leaf (.split 2 7 .leaf .leaf)))) .leaf) (.split 3 7 (.split 2 5 (.split 1 7 (.split 3 6 .leaf (.split 1 6 (.split 2 4 .leaf .leaf) .leaf)) .leaf) (.split 1 7 (.split 3 6 .leaf (.split 2 7 .leaf .leaf)) .leaf)) (.split 1 7 (.split 2 5 .leaf (.split 3 8 .leaf .leaf)) (.split 2 5 (.split 3 8 .leaf .leaf) (.split 3 8 .leaf .leaf))))) (.split 3 7 (.split 1 5 (.split 2 21 (.split 3 6 .leaf (.split 1 4 .leaf (.split 2 13 (.split 2 11 .leaf .leaf) (.split 2 16 (.split 2 14 .leaf .leaf) (.split 2 18 (.split 2 17 .leaf .leaf) (.split 2 19 .leaf (.split 2 20 .leaf .leaf))))))) (.split 3 6 .leaf (.split 1 4 .leaf (.split 2 45 (.split 2 29 (.split 2 25 (.split 2 23 .leaf .leaf) .leaf) (.split 2 36 .leaf .leaf)) (.split 2 93 .leaf .leaf))))) (.split 3 6 .leaf .leaf)) (.split 1 5 .leaf (.split 1 7 (.split 2 21 (.split 3 8 .leaf .leaf) (.split 3 8 .leaf .leaf)) (.split 2 21 (.split 3 8 .leaf .leaf) (.split 3 8 .leaf .leaf))))))
private theorem clrllrrl : Excluded blrllrrl := fun _ h => reject tlrllrrl (by decide +kernel) h
private def blrllrrr : Box := right blrllrr 1 9
private def tlrllrrr : Tree := (.split 3 7 .leaf (.split 1 21 (.split 2 9 (.split 1 13 (.split 2 5 (.split 3 8 .leaf .leaf) (.split 3 8 .leaf .leaf)) (.split 2 5 (.split 1 16 (.split 3 8 .leaf .leaf) .leaf) .leaf)) (.split 1 13 (.split 2 21 (.split 3 8 .leaf .leaf) .leaf) .leaf)) .leaf))
private theorem clrllrrr : Excluded blrllrrr := fun _ h => reject tlrllrrr (by decide +kernel) h
private theorem clrllrr : Excluded blrllrr := bisect blrllrr 1 9 clrllrrl clrllrrr
private theorem clrllr : Excluded blrllr := bisect blrllr 3 5 clrllrl clrllrr
private theorem clrll : Excluded blrll := bisect blrll 2 3 clrlll clrllr
private def blrlr : Box := right blrl 0 1
private def tlrlr : Tree := .leaf
private theorem clrlr : Excluded blrlr := fun _ h => reject tlrlr (by decide +kernel) h
private theorem clrl : Excluded blrl := bisect blrl 0 1 clrll clrlr
private def blrr : Box := right blr 3 9
private def blrrl : Box := left blrr 0 1
private def blrrll : Box := left blrrl 1 9
private def tlrrll : Tree := (.split 2 3 (.split 1 5 .leaf (.split 3 21 (.split 2 1 .leaf .leaf) .leaf)) (.split 3 21 (.split 1 5 .leaf (.split 3 13 (.split 2 9 .leaf .leaf) .leaf)) .leaf))
private theorem clrrll : Excluded blrrll := fun _ h => reject tlrrll (by decide +kernel) h
private def blrrlr : Box := right blrrl 1 9
private def blrrlrl : Box := left blrrlr 3 21
private def blrrlrll : Box := left blrrlrl 2 3
private def tlrrlrll : Tree := (.split 1 21 (.split 2 1 .leaf (.split 3 13 (.split 1 13 .leaf (.split 3 11 (.split 1 16 .leaf (.split 2 2 .leaf .leaf)) .leaf)) .leaf)) (.split 3 13 (.split 1 45 (.split 2 1 .leaf (.split 3 11 (.split 1 29 (.split 2 2 .leaf (.split 3 10 .leaf .leaf)) (.split 2 2 .leaf (.split 3 10 .leaf .leaf))) .leaf)) (.split 2 1 .leaf (.split 3 11 (.split 1 93 (.split 2 2 (.split 1 61 .leaf (.split 3 10 .leaf .leaf)) (.split 3 10 .leaf (.split 1 61 (.split 1 52 .leaf (.split 1 56 .leaf (.split 1 58 .leaf .leaf))) (.split 1 74 (.split 1 67 (.split 1 64 (.split 1 62 .leaf (.split 1 63 .leaf .leaf)) .leaf) .leaf) .leaf)))) (.split 2 2 (.split 1 189 (.split 3 10 .leaf .leaf) (.split 3 10 .leaf .leaf)) (.split 3 10 .leaf .leaf))) (.split 1 93 .leaf (.split 2 2 .leaf (.split 1 189 .leaf (.split 3 12 .leaf .leaf))))))) (.split 1 45 .leaf .leaf)))
private theorem clrrlrll : Excluded blrrlrll := fun _ h => reject tlrrlrll (by decide +kernel) h
private def blrrlrlr : Box := right blrrlrl 2 3
private def blrrlrlrl : Box := left blrrlrlr 1 21
private def blrrlrlrll : Box := left blrrlrlrl 3 13
private def blrrlrlrlll : Box := left blrrlrlrll 2 9
private def tlrrlrlrlll : Tree := (.split 1 13 (.split 3 11 (.split 2 5 .leaf (.split 1 11 .leaf (.split 3 10 .leaf .leaf))) .leaf) (.split 3 11 (.split 2 5 (.split 1 16 (.split 3 10 .leaf .leaf) (.split 3 10 .leaf .leaf)) (.split 1 16 (.split 3 10 .leaf .leaf) (.split 3 10 .leaf (.split 1 18 .leaf (.split 2 7 .leaf (.split 1 19 .leaf (.split 2 8 .leaf (.split 1 20 .leaf .leaf)))))))) .leaf))
private theorem clrrlrlrlll : Excluded blrrlrlrlll := fun _ h => reject tlrrlrlrlll (by decide +kernel) h
private def blrrlrlrllr : Box := right blrrlrlrll 2 9
private def tlrrlrlrllr : Tree := (.split 1 13 (.split 3 11 (.split 2 21 (.split 1 11 .leaf (.split 3 10 .leaf .leaf)) (.split 1 11 (.split 3 10 .leaf .leaf) (.split 3 10 .leaf .leaf))) .leaf) (.split 3 11 (.split 2 21 (.split 1 16 (.split 3 10 .leaf (.split 2 13 .leaf .leaf)) (.split 3 10 .leaf (.split 2 13 (.split 1 18 (.split 2 11 .leaf .leaf) (.split 1 19 (.split 2 11 .leaf (.split 2 12 .leaf .leaf)) (.split 2 11 (.split 1 20 .leaf .leaf) .leaf))) (.split 1 18 (.split 2 16 (.split 1 17 .leaf (.split 2 14 .leaf (.split 2 15 .leaf .leaf))) (.split 1 17 .leaf .leaf)) .leaf)))) (.split 1 16 (.split 3 10 .leaf (.split 2 45 (.split 1 14 .leaf (.split 2 29 .leaf .leaf)) (.split 1 14 .leaf (.split 2 93 (.split 1 15 .leaf (.split 2 61 (.split 2 52 .leaf .leaf) (.split 2 74 (.split 2 67 (.split 2 64 .leaf .leaf) (.split 2 70 (.split 2 68 .leaf .leaf) .leaf)) (.split 2 83 .leaf .leaf)))) (.split 1 15 .leaf (.split 2 189 .leaf .leaf)))))) (.split 3 10 .leaf (.split 2 45 (.split 1 18 (.split 2 29 (.split 1 17 (.split 2 25 (.split 2 23 .leaf (.split 2 24 .leaf .leaf)) .leaf) .leaf) .leaf) .leaf) .leaf)))) (.split 1 16 .leaf (.split 2 21 .leaf (.split 3 12 .leaf .leaf)))))
private theorem clrrlrlrllr : Excluded blrrlrlrllr := fun _ h => reject tlrrlrlrllr (by decide +kernel) h
private theorem clrrlrlrll : Excluded blrrlrlrll := bisect blrrlrlrll 2 9 clrrlrlrlll clrrlrlrllr
private def blrrlrlrlr : Box := right blrrlrlrl 3 13
private def tlrrlrlrlr : Tree := .leaf
private theorem clrrlrlrlr : Excluded blrrlrlrlr := fun _ h => reject tlrrlrlrlr (by decide +kernel) h
private theorem clrrlrlrl : Excluded blrrlrlrl := bisect blrrlrlrl 3 13 clrrlrlrll clrrlrlrlr
private def blrrlrlrr : Box := right blrrlrlr 1 21
private def blrrlrlrrl : Box := left blrrlrlrr 3 13
private def blrrlrlrrll : Box := left blrrlrlrrl 2 9
private def blrrlrlrrlll : Box := left blrrlrlrrll 1 45
private def tlrrlrlrrlll : Tree := (.split 3 11 (.split 2 5 (.split 1 29 (.split 3 10 .leaf (.split 1 25 .leaf (.split 2 4 .leaf (.split 1 27 .leaf .leaf)))) (.split 3 10 .leaf (.split 1 36 (.split 2 4 (.split 1 32 .leaf (.split 1 34 .leaf (.split 1 35 .leaf .leaf))) .leaf) (.split 2 4 .leaf .leaf)))) (.split 1 29 (.split 3 10 .leaf (.split 1 25 (.split 2 7 (.split 1 23 (.split 2 6 .leaf (.split 1 22 .leaf .leaf)) (.split 2 6 (.split 1 24 .leaf .leaf) .leaf)) .leaf) (.split 2 7 .leaf .leaf))) .leaf)) (.split 1 29 (.split 2 5 .leaf (.split 3 12 .leaf .leaf)) (.split 2 5 (.split 1 36 .leaf .leaf) (.split 1 36 (.split 3 12 .leaf .leaf) (.split 3 12 .leaf .leaf)))))
private theorem clrrlrlrrlll : Excluded blrrlrlrrlll := fun _ h => reject tlrrlrlrrlll (by decide +kernel) h
private def blrrlrlrrllr : Box := right blrrlrlrrll 1 45
private def tlrrlrlrrllr : Tree := (.split 3 11 (.split 1 93 .leaf .leaf) (.split 1 93 (.split 2 5 (.split 1 61 (.split 3 12 .leaf .leaf) (.split 3 12 .leaf .leaf)) (.split 1 61 (.split 3 12 .leaf (.split 2 7 .leaf (.split 1 52 .leaf (.split 1 56 .leaf (.split 2 8 .leaf (.split 1 58 .leaf (.split 1 59 .leaf (.split 1 60 .leaf .leaf)))))))) (.split 3 12 .leaf (.split 2 7 (.split 1 74 .leaf (.split 2 6 .leaf (.split 1 83 (.split 1 78 .leaf (.split 1 80 .leaf .leaf)) (.split 1 88 (.split 1 85 .leaf .leaf) .leaf)))) (.split 1 74 (.split 1 67 (.split 2 8 .leaf .leaf) (.split 2 8 (.split 1 70 (.split 1 68 .leaf (.split 1 69 .leaf .leaf)) .leaf) .leaf)) .leaf))))) (.split 2 5 (.split 1 189 (.split 3 12 .leaf (.split 1 125 .leaf .leaf)) (.split 3 12 .leaf (.split 1 381 (.split 2 4 .leaf (.split 1 253 (.split 1 217 .leaf (.split 1 234 .leaf .leaf)) (.split 1 304 (.split 1 276 (.split 1 264 (.split 1 258 .leaf (.split 1 261 .leaf (.split 1 262 .leaf .leaf))) .leaf) .leaf) .leaf))) (.split 2 4 .leaf .leaf)))) (.split 3 12 .leaf (.split 1 189 (.split 2 7 (.split 1 125 (.split 2 6 (.split 1 107 .leaf (.split 1 115 (.split 1 111 .leaf .leaf) (.split 1 120 (.split 1 117 (.split 1 116 .leaf .leaf) .leaf) .leaf))) .leaf) (.split 2 6 .leaf .leaf)) .leaf) .leaf)))))
private theorem clrrlrlrrllr : Excluded blrrlrlrrllr := fun _ h => reject tlrrlrlrrllr (by decide +kernel) h
private theorem clrrlrlrrll : Excluded blrrlrlrrll := bisect blrrlrlrrll 1 45 clrrlrlrrlll clrrlrlrrllr
private def blrrlrlrrlr : Box := right blrrlrlrrl 2 9
private def blrrlrlrrlrl : Box := left blrrlrlrrlr 3 11
private def tlrrlrlrrlrl : Tree := (.split 1 45 (.split 2 21 .leaf .leaf) .leaf)
private theorem clrrlrlrrlrl : Excluded blrrlrlrrlrl := fun _ h => reject tlrrlrlrrlrl (by decide +kernel) h
private def blrrlrlrrlrr : Box := right blrrlrlrrlr 3 11
private def blrrlrlrrlrrl : Box := left blrrlrlrrlrr 1 45
private def blrrlrlrrlrrll : Box := left blrrlrlrrlrrl 1 29
private def tlrrlrlrrlrrll : Tree := (.split 2 21 (.split 3 12 .leaf .leaf) (.split 3 12 .leaf .leaf))
private theorem clrrlrlrrlrrll : Excluded blrrlrlrrlrrll := fun _ h => reject tlrrlrlrrlrrll (by decide +kernel) h
private def blrrlrlrrlrrlr : Box := right blrrlrlrrlrrl 1 29
private def blrrlrlrrlrrlrl : Box := left blrrlrlrrlrrlr 2 21
private def tlrrlrlrrlrrlrl : Tree := (.split 3 12 .leaf (.split 1 36 .leaf (.split 2 13 (.split 1 40 .leaf .leaf) (.split 1 40 (.split 2 16 .leaf (.split 1 38 .leaf (.split 2 18 .leaf (.split 2 19 .leaf (.split 1 39 .leaf (.split 2 20 .leaf .leaf)))))) (.split 2 16 (.split 1 42 .leaf (.split 2 14 .leaf (.split 1 43 (.split 2 15 .leaf .leaf) (.split 2 15 (.split 1 44 .leaf .leaf) .leaf)))) (.split 1 42 (.split 2 18 (.split 1 41 .leaf (.split 2 17 .leaf .leaf)) (.split 2 19 .leaf .leaf)) .leaf))))))
private theorem clrrlrlrrlrrlrl : Excluded blrrlrlrrlrrlrl := fun _ h => reject tlrrlrlrrlrrlrl (by decide +kernel) h
private def blrrlrlrrlrrlrr : Box := right blrrlrlrrlrrlr 2 21
private def blrrlrlrrlrrlrrl : Box := left blrrlrlrrlrrlrr 3 12
private def tlrrlrlrrlrrlrrl : Tree := .leaf
private theorem clrrlrlrrlrrlrrl : Excluded blrrlrlrrlrrlrrl := fun _ h => reject tlrrlrlrrlrrlrrl (by decide +kernel) h
private def blrrlrlrrlrrlrrr : Box := right blrrlrlrrlrrlrr 3 12
private def blrrlrlrrlrrlrrrl : Box := left blrrlrlrrlrrlrrr 1 36
private def tlrrlrlrrlrrlrrrl : Tree := (.split 2 45 (.split 1 32 .leaf (.split 2 29 .leaf (.split 1 34 .leaf (.split 2 36 (.split 2 32 .leaf (.split 1 35 .leaf (.split 2 34 .leaf .leaf))) (.split 2 40 (.split 1 35 .leaf .leaf) (.split 1 35 (.split 2 42 .leaf (.split 2 43 .leaf .leaf)) .leaf)))))) (.split 1 32 (.split 2 93 .leaf (.split 2 189 (.split 1 30 .leaf .leaf) (.split 1 30 .leaf (.split 2 381 (.split 1 31 .leaf (.split 2 253 (.split 2 217 .leaf .leaf) (.split 2 304 (.split 2 276 (.split 2 264 .leaf (.split 2 270 .leaf (.split 2 273 (.split 2 271 .leaf (.split 2 272 .leaf .leaf)) .leaf))) (.split 2 289 .leaf .leaf)) .leaf))) (.split 1 31 .leaf .leaf))))) (.split 2 93 (.split 1 34 (.split 2 61 (.split 2 52 .leaf (.split 1 33 .leaf (.split 2 56 .leaf (.split 2 58 (.split 2 57 .leaf .leaf) .leaf)))) (.split 2 74 (.split 1 33 .leaf .leaf) (.split 1 33 (.split 2 83 .leaf (.split 2 88 .leaf (.split 2 90 .leaf .leaf))) .leaf))) (.split 2 61 .leaf .leaf)) (.split 1 34 (.split 2 189 (.split 2 125 (.split 1 33 (.split 2 107 (.split 2 100 (.split 2 96 (.split 2 94 .leaf .leaf) .leaf) .leaf) .leaf) .leaf) .leaf) .leaf) .leaf))))
private theorem clrrlrlrrlrrlrrrl : Excluded blrrlrlrrlrrlrrrl := fun _ h => reject tlrrlrlrrlrrlrrrl (by decide +kernel) h
private def blrrlrlrrlrrlrrrr : Box := right blrrlrlrrlrrlrrr 1 36
private def tlrrlrlrrlrrlrrrr : Tree := (.split 2 45 (.split 1 40 (.split 2 29 (.split 1 38 (.split 2 25 (.split 2 23 .leaf (.split 1 37 .leaf (.split 2 24 .leaf .leaf))) (.split 2 27 (.split 1 37 .leaf .leaf) (.split 1 37 (.split 2 28 .leaf .leaf) .leaf))) (.split 2 25 (.split 2 23 (.split 1 39 (.split 2 22 .leaf .leaf) .leaf) .leaf) .leaf)) (.split 2 36 (.split 1 38 (.split 2 32 .leaf .leaf) .leaf) .leaf)) .leaf) .leaf)
private theorem clrrlrlrrlrrlrrrr : Excluded blrrlrlrrlrrlrrrr := fun _ h => reject tlrrlrlrrlrrlrrrr (by decide +kernel) h
private theorem clrrlrlrrlrrlrrr : Excluded blrrlrlrrlrrlrrr := bisect blrrlrlrrlrrlrrr 1 36 clrrlrlrrlrrlrrrl clrrlrlrrlrrlrrrr
private theorem clrrlrlrrlrrlrr : Excluded blrrlrlrrlrrlrr := bisect blrrlrlrrlrrlrr 3 12 clrrlrlrrlrrlrrl clrrlrlrrlrrlrrr
private theorem clrrlrlrrlrrlr : Excluded blrrlrlrrlrrlr := bisect blrrlrlrrlrrlr 2 21 clrrlrlrrlrrlrl clrrlrlrrlrrlrr
private theorem clrrlrlrrlrrl : Excluded blrrlrlrrlrrl := bisect blrrlrlrrlrrl 1 29 clrrlrlrrlrrll clrrlrlrrlrrlr
private def blrrlrlrrlrrr : Box := right blrrlrlrrlrr 1 45
private def tlrrlrlrrlrrr : Tree := (.split 1 93 (.split 2 21 (.split 3 12 .leaf (.split 1 61 (.split 2 13 (.split 1 52 (.split 2 11 (.split 1 48 .leaf (.split 2 10 .leaf (.split 1 50 .leaf (.split 1 51 .leaf .leaf)))) (.split 1 48 (.split 2 12 .leaf (.split 1 46 .leaf (.split 1 47 .leaf .leaf))) (.split 1 50 (.split 2 12 (.split 1 49 .leaf .leaf) .leaf) .leaf))) (.split 2 11 (.split 1 56 (.split 2 10 (.split 1 54 .leaf (.split 1 55 .leaf .leaf)) .leaf) .leaf) .leaf)) (.split 1 52 (.split 2 16 (.split 1 48 (.split 2 14 .leaf .leaf) .leaf) .leaf) .leaf)) .leaf)) .leaf) .leaf)
private theorem clrrlrlrrlrrr : Excluded blrrlrlrrlrrr := fun _ h => reject tlrrlrlrrlrrr (by decide +kernel) h
private theorem clrrlrlrrlrr : Excluded blrrlrlrrlrr := bisect blrrlrlrrlrr 1 45 clrrlrlrrlrrl clrrlrlrrlrrr
private theorem clrrlrlrrlr : Excluded blrrlrlrrlr := bisect blrrlrlrrlr 3 11 clrrlrlrrlrl clrrlrlrrlrr
private theorem clrrlrlrrl : Excluded blrrlrlrrl := bisect blrrlrlrrl 2 9 clrrlrlrrll clrrlrlrrlr
private def blrrlrlrrr : Box := right blrrlrlrr 3 13
private def tlrrlrlrrr : Tree := (.split 1 45 (.split 3 16 (.split 2 9 .leaf (.split 1 29 .leaf (.split 3 14 .leaf .leaf))) .leaf) (.split 3 16 (.split 2 9 (.split 1 93 .leaf (.split 3 14 .leaf .leaf)) (.split 1 93 (.split 3 14 .leaf (.split 2 21 .leaf .leaf)) (.split 3 14 .leaf (.split 2 21 (.split 1 189 .leaf (.split 3 15 .leaf .leaf)) (.split 1 189 (.split 3 15 .leaf .leaf) (.split 3 15 .leaf .leaf)))))) .leaf))
private theorem clrrlrlrrr : Excluded blrrlrlrrr := fun _ h => reject tlrrlrlrrr (by decide +kernel) h
private theorem clrrlrlrr : Excluded blrrlrlrr := bisect blrrlrlrr 3 13 clrrlrlrrl clrrlrlrrr
private theorem clrrlrlr : Excluded blrrlrlr := bisect blrrlrlr 1 21 clrrlrlrl clrrlrlrr
private theorem clrrlrl : Excluded blrrlrl := bisect blrrlrl 2 3 clrrlrll clrrlrlr
private def blrrlrr : Box := right blrrlr 3 21
private def tlrrlrr : Tree := (.split 1 21 .leaf .leaf)
private theorem clrrlrr : Excluded blrrlrr := fun _ h => reject tlrrlrr (by decide +kernel) h
private theorem clrrlr : Excluded blrrlr := bisect blrrlr 3 21 clrrlrl clrrlrr
private theorem clrrl : Excluded blrrl := bisect blrrl 1 9 clrrll clrrlr
private def blrrr : Box := right blrr 0 1
private def blrrrl : Box := left blrrr 1 9
private def blrrrll : Box := left blrrrl 3 21
private def tlrrrll : Tree := (.split 2 3 (.split 0 2 (.split 1 5 (.split 2 1 .leaf .leaf) .leaf) .leaf) (.split 0 2 (.split 1 5 (.split 3 13 .leaf (.split 2 9 .leaf (.split 3 16 .leaf (.split 1 4 (.split 2 21 .leaf .leaf) .leaf)))) .leaf) .leaf))
private theorem clrrrll : Excluded blrrrll := fun _ h => reject tlrrrll (by decide +kernel) h
private def blrrrlr : Box := right blrrrl 3 21
private def blrrrlrl : Box := left blrrrlr 0 2
private def blrrrlrll : Box := left blrrrlrl 1 5
private def blrrrlrlll : Box := left blrrrlrll 2 3
private def tlrrrlrlll : Tree := (.split 3 45 (.split 2 1 .leaf (.split 1 4 (.split 3 29 .leaf (.split 2 2 .leaf (.split 3 36 (.split 3 32 .leaf (.split 3 34 .leaf (.split 3 35 .leaf .leaf))) .leaf))) .leaf)) (.split 2 1 (.split 1 4 .leaf .leaf) (.split 1 4 (.split 3 93 (.split 2 2 (.split 3 61 (.split 3 52 (.split 3 48 (.split 3 46 .leaf (.split 3 47 .leaf .leaf)) .leaf) .leaf) .leaf) .leaf) .leaf) (.split 3 93 (.split 3 61 .leaf (.split 2 2 .leaf .leaf)) (.split 3 189 (.split 2 2 .leaf (.split 3 125 (.split 3 107 (.split 3 100 (.split 3 96 .leaf (.split 3 98 (.split 3 97 .leaf .leaf) .leaf)) .leaf) .leaf) .leaf)) (.split 2 2 (.split 3 381 .leaf (.split 3 765 (.split 3 509 (.split 3 436 (.split 3 407 .leaf (.split 3 421 (.split 3 414 (.split 3 410 (.split 3 408 .leaf (.split 3 409 .leaf .leaf)) .leaf) .leaf) .leaf)) .leaf) .leaf) .leaf)) .leaf))))))
private theorem clrrrlrlll : Excluded blrrrlrlll := fun _ h => reject tlrrrlrlll (by decide +kernel) h
private def blrrrlrllr : Box := right blrrrlrll 2 3
private def blrrrlrllrl : Box := left blrrrlrllr 3 45
private def blrrrlrllrll : Box := left blrrrlrllrl 2 9
private def tlrrrlrllrll : Tree := (.split 3 29 (.split 1 4 (.split 2 5 (.split 3 25 .leaf (.split 2 4 .leaf (.split 3 27 .leaf (.split 3 28 .leaf .leaf)))) (.split 3 25 (.split 2 7 .leaf .leaf) (.split 2 7 (.split 3 27 (.split 2 6 .leaf .leaf) (.split 2 6 .leaf .leaf)) (.split 3 27 (.split 2 8 (.split 3 26 .leaf .leaf) (.split 3 26 .leaf .leaf)) .leaf)))) .leaf) (.split 1 4 (.split 2 5 (.split 3 36 (.split 3 32 (.split 2 4 (.split 3 30 .leaf (.split 3 31 .leaf .leaf)) .leaf) .leaf) .leaf) .leaf) (.split 2 5 .leaf .leaf)))
private theorem clrrrlrllrll : Excluded blrrrlrllrll := fun _ h => reject tlrrrlrllrll (by decide +kernel) h
private def blrrrlrllrlr : Box := right blrrrlrllrl 2 9
private def blrrrlrllrlrl : Box := left blrrrlrllrlr 3 29
private def tlrrrlrllrlrl : Tree := (.split 1 4 (.split 2 21 (.split 3 25 (.split 2 13 (.split 3 23 .leaf (.split 2 11 .leaf (.split 3 24 .leaf .leaf))) (.split 3 23 .leaf (.split 2 16 (.split 3 24 .leaf .leaf) (.split 3 24 .leaf .leaf)))) (.split 2 13 (.split 3 27 (.split 2 11 .leaf .leaf) .leaf) .leaf)) (.split 3 25 (.split 2 45 (.split 3 23 .leaf (.split 2 29 (.split 3 24 .leaf .leaf) (.split 3 24 .leaf .leaf))) (.split 3 23 (.split 2 93 .leaf (.split 3 22 .leaf (.split 2 189 .leaf (.split 2 381 .leaf .leaf)))) (.split 2 93 .leaf .leaf))) .leaf)) .leaf)
private theorem clrrrlrllrlrl : Excluded blrrrlrllrlrl := fun _ h => reject tlrrrlrllrlrl (by decide +kernel) h
private def blrrrlrllrlrr : Box := right blrrrlrllrlr 3 29
private def tlrrrlrllrlrr : Tree := (.split 1 4 .leaf (.split 3 36 (.split 2 21 .leaf .leaf) (.split 2 21 (.split 3 40 .leaf (.split 2 13 (.split 3 42 .leaf (.split 2 11 .leaf (.split 3 43 .leaf (.split 2 12 .leaf (.split 3 44 .leaf .leaf))))) (.split 3 42 (.split 2 16 .leaf (.split 2 18 .leaf .leaf)) (.split 2 16 (.split 3 43 .leaf (.split 2 14 (.split 3 44 .leaf .leaf) (.split 3 44 .leaf .leaf))) (.split 3 43 (.split 2 18 (.split 2 17 .leaf .leaf) .leaf) .leaf))))) (.split 3 40 (.split 2 45 (.split 2 29 .leaf (.split 3 38 .leaf (.split 2 36 .leaf .leaf))) (.split 2 93 (.split 3 38 .leaf (.split 2 61 (.split 3 39 .leaf .leaf) (.split 3 39 .leaf .leaf))) (.split 3 38 .leaf (.split 2 189 (.split 3 39 .leaf .leaf) (.split 3 39 .leaf .leaf))))) (.split 2 45 (.split 3 42 (.split 2 29 (.split 2 25 (.split 3 41 .leaf .leaf) (.split 3 41 (.split 2 27 .leaf .leaf) .leaf)) (.split 2 36 (.split 3 41 (.split 2 32 (.split 2 30 .leaf (.split 2 31 .leaf .leaf)) .leaf) .leaf) .leaf)) .leaf) (.split 3 42 (.split 2 93 .leaf .leaf) .leaf))))))
private theorem clrrrlrllrlrr : Excluded blrrrlrllrlrr := fun _ h => reject tlrrrlrllrlrr (by decide +kernel) h
private theorem clrrrlrllrlr : Excluded blrrrlrllrlr := bisect blrrrlrllrlr 3 29 clrrrlrllrlrl clrrrlrllrlrr
private theorem clrrrlrllrl : Excluded blrrrlrllrl := bisect blrrrlrllrl 2 9 clrrrlrllrll clrrrlrllrlr
private def blrrrlrllrr : Box := right blrrrlrllr 3 45
private def tlrrrlrllrr : Tree := (.split 2 9 (.split 1 4 .leaf (.split 3 93 (.split 3 61 (.split 2 5 (.split 3 52 .leaf (.split 2 4 .leaf (.split 3 56 .leaf (.split 3 58 .leaf (.split 3 59 .leaf (.split 3 60 .leaf .leaf)))))) (.split 3 52 (.split 2 7 (.split 3 48 .leaf (.split 2 6 .leaf .leaf)) (.split 3 48 (.split 2 8 .leaf .leaf) (.split 3 50 (.split 2 8 (.split 3 49 .leaf .leaf) .leaf) .leaf))) (.split 2 7 (.split 3 56 (.split 2 6 (.split 3 54 .leaf (.split 3 55 .leaf .leaf)) .leaf) .leaf) .leaf))) (.split 2 5 (.split 3 74 (.split 2 4 (.split 3 67 .leaf (.split 3 70 .leaf .leaf)) .leaf) .leaf) .leaf)) .leaf)) (.split 3 93 (.split 1 4 .leaf (.split 3 61 (.split 2 21 (.split 3 52 (.split 2 13 (.split 3 48 (.split 2 11 (.split 3 46 .leaf (.split 2 10 (.split 3 47 .leaf .leaf) .leaf)) .leaf) .leaf) .leaf) .leaf) .leaf) .leaf)) .leaf))
private theorem clrrrlrllrr : Excluded blrrrlrllrr := fun _ h => reject tlrrrlrllrr (by decide +kernel) h
private theorem clrrrlrllr : Excluded blrrrlrllr := bisect blrrrlrllr 3 45 clrrrlrllrl clrrrlrllrr
private theorem clrrrlrll : Excluded blrrrlrll := bisect blrrrlrll 2 3 clrrrlrlll clrrrlrllr
private def blrrrlrlr : Box := right blrrrlrl 1 5
private def blrrrlrlrl : Box := left blrrrlrlr 2 3
private def tlrrrlrlrl : Tree := (.split 3 45 .leaf (.split 1 7 .leaf .leaf))
private theorem clrrrlrlrl : Excluded blrrrlrlrl := fun _ h => reject tlrrrlrlrl (by decide +kernel) h
private def blrrrlrlrr : Box := right blrrrlrlr 2 3
private def blrrrlrlrrl : Box := left blrrrlrlrr 3 45
private def tlrrrlrlrrl : Tree := .leaf
private theorem clrrrlrlrrl : Excluded blrrrlrlrrl := fun _ h => reject tlrrrlrlrrl (by decide +kernel) h
private def blrrrlrlrrr : Box := right blrrrlrlrr 3 45
private def blrrrlrlrrrl : Box := left blrrrlrlrrr 1 7
private def blrrrlrlrrrll : Box := left blrrrlrlrrrl 3 93
private def blrrrlrlrrrlll : Box := left blrrrlrlrrrll 2 9
private def tlrrrlrlrrrlll : Tree := .leaf
private theorem clrrrlrlrrrlll : Excluded blrrrlrlrrrlll := fun _ h => reject tlrrrlrlrrrlll (by decide +kernel) h
private def blrrrlrlrrrllr : Box := right blrrrlrlrrrll 2 9
private def blrrrlrlrrrllrl : Box := left blrrrlrlrrrllr 3 61
private def tlrrrlrlrrrllrl : Tree := .leaf
private theorem clrrrlrlrrrllrl : Excluded blrrrlrlrrrllrl := fun _ h => reject tlrrrlrlrrrllrl (by decide +kernel) h
private def blrrrlrlrrrllrr : Box := right blrrrlrlrrrllr 3 61
private def blrrrlrlrrrllrrl : Box := left blrrrlrlrrrllrr 1 6
private def blrrrlrlrrrllrrll : Box := left blrrrlrlrrrllrrl 2 21
private def tlrrrlrlrrrllrrll : Tree := (.split 3 74 .leaf (.split 2 13 .leaf (.split 3 83 .leaf (.split 2 16 .leaf (.split 3 88 .leaf (.split 2 18 .leaf (.split 3 90 .leaf (.split 2 19 (.split 3 91 .leaf (.split 3 92 .leaf .leaf)) (.split 3 91 .leaf .leaf)))))))))
private theorem clrrrlrlrrrllrrll : Excluded blrrrlrlrrrllrrll := fun _ h => reject tlrrrlrlrrrllrrll (by decide +kernel) h
private def blrrrlrlrrrllrrlr : Box := right blrrrlrlrrrllrrl 2 21
private def blrrrlrlrrrllrrlrl : Box := left blrrrlrlrrrllrrlr 3 74
private def tlrrrlrlrrrllrrlrl : Tree := (.split 2 45 .leaf (.split 3 67 .leaf (.split 2 93 .leaf .leaf)))
private theorem clrrrlrlrrrllrrlrl : Excluded blrrrlrlrrrllrrlrl := fun _ h => reject tlrrrlrlrrrllrrlrl (by decide +kernel) h
private def blrrrlrlrrrllrrlrr : Box := right blrrrlrlrrrllrrlr 3 74
private def blrrrlrlrrrllrrlrrl : Box := left blrrrlrlrrrllrrlrr 2 45
private def tlrrrlrlrrrllrrlrrl : Tree := (.split 3 83 (.split 2 29 .leaf (.split 3 78 .leaf (.split 2 36 (.split 3 80 .leaf (.split 2 32 .leaf .leaf)) (.split 3 80 .leaf (.split 2 40 (.split 3 81 .leaf (.split 2 38 (.split 3 82 .leaf (.split 2 37 .leaf .leaf)) (.split 3 82 .leaf .leaf))) (.split 3 81 .leaf (.split 2 42 (.split 3 82 .leaf .leaf) .leaf))))))) (.split 2 29 (.split 3 88 (.split 2 25 (.split 3 85 .leaf (.split 2 23 .leaf (.split 3 86 .leaf (.split 3 87 .leaf .leaf)))) (.split 3 85 .leaf (.split 2 27 (.split 3 86 .leaf (.split 3 87 .leaf .leaf)) (.split 3 86 .leaf .leaf)))) (.split 2 25 (.split 3 90 (.split 2 23 (.split 2 22 (.split 3 89 .leaf .leaf) (.split 3 89 .leaf .leaf)) .leaf) .leaf) .leaf)) (.split 3 88 (.split 2 36 (.split 3 85 (.split 2 32 (.split 2 30 .leaf (.split 3 84 .leaf .leaf)) (.split 2 34 (.split 3 84 .leaf .leaf) .leaf)) .leaf) .leaf) .leaf)))
private theorem clrrrlrlrrrllrrlrrl : Excluded blrrrlrlrrrllrrlrrl := fun _ h => reject tlrrrlrlrrrllrrlrrl (by decide +kernel) h
private def blrrrlrlrrrllrrlrrr : Box := right blrrrlrlrrrllrrlrr 2 45
private def tlrrrlrlrrrllrrlrrr : Tree := (.split 3 83 (.split 2 93 (.split 3 78 (.split 2 61 .leaf (.split 3 76 .leaf (.split 2 74 .leaf (.split 2 83 .leaf (.split 3 77 .leaf .leaf))))) (.split 2 61 (.split 3 80 (.split 2 52 .leaf (.split 2 56 .leaf (.split 3 79 .leaf .leaf))) (.split 2 52 (.split 3 81 .leaf .leaf) .leaf)) (.split 3 80 (.split 2 74 (.split 2 67 (.split 3 79 .leaf .leaf) (.split 3 79 (.split 2 70 (.split 2 68 .leaf (.split 2 69 .leaf .leaf)) .leaf) .leaf)) .leaf) .leaf))) (.split 3 78 (.split 2 189 (.split 3 76 (.split 2 125 .leaf .leaf) (.split 2 125 (.split 2 107 (.split 3 77 .leaf .leaf) (.split 3 77 .leaf .leaf)) (.split 2 151 (.split 3 77 .leaf .leaf) .leaf))) (.split 3 76 (.split 2 381 (.split 2 253 (.split 3 75 .leaf .leaf) (.split 3 75 .leaf .leaf)) (.split 2 765 (.split 3 75 .leaf .leaf) (.split 3 75 .leaf .leaf))) .leaf)) .leaf)) .leaf)
private theorem clrrrlrlrrrllrrlrrr : Excluded blrrrlrlrrrllrrlrrr := fun _ h => reject tlrrrlrlrrrllrrlrrr (by decide +kernel) h
private theorem clrrrlrlrrrllrrlrr : Excluded blrrrlrlrrrllrrlrr := bisect blrrrlrlrrrllrrlrr 2 45 clrrrlrlrrrllrrlrrl clrrrlrlrrrllrrlrrr
private theorem clrrrlrlrrrllrrlr : Excluded blrrrlrlrrrllrrlr := bisect blrrrlrlrrrllrrlr 3 74 clrrrlrlrrrllrrlrl clrrrlrlrrrllrrlrr
private theorem clrrrlrlrrrllrrl : Excluded blrrrlrlrrrllrrl := bisect blrrrlrlrrrllrrl 2 21 clrrrlrlrrrllrrll clrrrlrlrrrllrrlr
private def blrrrlrlrrrllrrr : Box := right blrrrlrlrrrllrr 1 6
private def tlrrrlrlrrrllrrr : Tree := .leaf
private theorem clrrrlrlrrrllrrr : Excluded blrrrlrlrrrllrrr := fun _ h => reject tlrrrlrlrrrllrrr (by decide +kernel) h
private theorem clrrrlrlrrrllrr : Excluded blrrrlrlrrrllrr := bisect blrrrlrlrrrllrr 1 6 clrrrlrlrrrllrrl clrrrlrlrrrllrrr
private theorem clrrrlrlrrrllr : Excluded blrrrlrlrrrllr := bisect blrrrlrlrrrllr 3 61 clrrrlrlrrrllrl clrrrlrlrrrllrr
private theorem clrrrlrlrrrll : Excluded blrrrlrlrrrll := bisect blrrrlrlrrrll 2 9 clrrrlrlrrrlll clrrrlrlrrrllr
private def blrrrlrlrrrlr : Box := right blrrrlrlrrrl 3 93
private def blrrrlrlrrrlrl : Box := left blrrrlrlrrrlr 2 9
private def tlrrrlrlrrrlrl : Tree := (.split 1 6 (.split 3 189 (.split 2 5 .leaf (.split 3 125 (.split 2 7 .leaf .leaf) (.split 2 7 (.split 3 151 .leaf (.split 2 6 .leaf (.split 3 168 (.split 3 159 (.split 3 155 .leaf (.split 3 157 .leaf .leaf)) .leaf) .leaf))) (.split 3 151 (.split 3 137 (.split 2 8 .leaf (.split 3 131 (.split 3 128 (.split 3 126 .leaf .leaf) .leaf) .leaf)) (.split 2 8 (.split 3 144 (.split 3 140 (.split 3 138 .leaf .leaf) .leaf) .leaf) .leaf)) .leaf)))) (.split 2 5 (.split 3 381 (.split 2 4 .leaf (.split 3 253 .leaf (.split 3 304 (.split 3 276 .leaf (.split 3 289 (.split 3 282 .leaf (.split 3 285 (.split 3 283 .leaf .leaf) .leaf)) .leaf)) .leaf))) (.split 3 765 (.split 2 4 .leaf .leaf) (.split 2 4 (.split 3 1533 (.split 3 1021 (.split 3 875 .leaf (.split 3 942 (.split 3 907 .leaf (.split 3 924 .leaf (.split 3 933 (.split 3 928 .leaf .leaf) .leaf))) .leaf)) .leaf) .leaf) .leaf))) (.split 3 381 (.split 2 7 (.split 3 253 (.split 2 6 (.split 3 217 (.split 3 202 (.split 3 195 (.split 3 192 .leaf (.split 3 193 .leaf .leaf)) .leaf) .leaf) .leaf) .leaf) .leaf) .leaf) .leaf))) .leaf)
private theorem clrrrlrlrrrlrl : Excluded blrrrlrlrrrlrl := fun _ h => reject tlrrrlrlrrrlrl (by decide +kernel) h
private def blrrrlrlrrrlrr : Box := right blrrrlrlrrrlr 2 9
private def blrrrlrlrrrlrrl : Box := left blrrrlrlrrrlrr 3 189
private def tlrrrlrlrrrlrrl : Tree := (.split 1 6 (.split 2 21 (.split 3 125 (.split 2 13 (.split 3 107 (.split 2 11 .leaf (.split 3 100 .leaf (.split 3 103 .leaf (.split 2 12 .leaf (.split 3 105 (.split 3 104 .leaf .leaf) .leaf))))) (.split 2 11 (.split 3 115 (.split 2 10 .leaf (.split 3 111 .leaf (.split 3 113 (.split 3 112 .leaf .leaf) .leaf))) (.split 3 120 (.split 2 10 (.split 3 117 .leaf (.split 3 118 .leaf .leaf)) .leaf) .leaf)) (.split 3 115 (.split 3 111 (.split 2 12 .leaf .leaf) .leaf) .leaf))) (.split 3 107 (.split 2 16 (.split 3 100 (.split 3 96 .leaf (.split 2 14 .leaf (.split 3 98 (.split 2 15 .leaf (.split 3 97 .leaf .leaf)) (.split 2 15 (.split 3 99 .leaf .leaf) .leaf)))) (.split 2 14 (.split 3 103 (.split 3 101 .leaf .leaf) .leaf) .leaf)) (.split 3 100 (.split 2 18 (.split 3 96 (.split 2 17 (.split 3 94 .leaf (.split 3 95 .leaf .leaf)) (.split 3 94 .leaf .leaf)) .leaf) .leaf) .leaf)) .leaf)) .leaf) .leaf) .leaf)
private theorem clrrrlrlrrrlrrl : Excluded blrrrlrlrrrlrrl := fun _ h => reject tlrrrlrlrrrlrrl (by decide +kernel) h
private def blrrrlrlrrrlrrr : Box := right blrrrlrlrrrlrr 3 189
private def blrrrlrlrrrlrrrl : Box := left blrrrlrlrrrlrrr 1 6
private def tlrrrlrlrrrlrrrl : Tree := .leaf
private theorem clrrrlrlrrrlrrrl : Excluded blrrrlrlrrrlrrrl := fun _ h => reject tlrrrlrlrrrlrrrl (by decide +kernel) h
private def blrrrlrlrrrlrrrr : Box := right blrrrlrlrrrlrrr 1 6
private def blrrrlrlrrrlrrrrl : Box := left blrrrlrlrrrlrrrr 2 21
private def blrrrlrlrrrlrrrrll : Box := left blrrrlrlrrrlrrrrl 3 381
private def tlrrrlrlrrrlrrrrll : Tree := .leaf
private theorem clrrrlrlrrrlrrrrll : Excluded blrrrlrlrrrlrrrrll := fun _ h => reject tlrrrlrlrrrlrrrrll (by decide +kernel) h
private def blrrrlrlrrrlrrrrlr : Box := right blrrrlrlrrrlrrrrl 3 381
private def blrrrlrlrrrlrrrrlrl : Box := left blrrrlrlrrrlrrrrlr 2 13
private def tlrrrlrlrrrlrrrrlrl : Tree := .leaf
private theorem clrrrlrlrrrlrrrrlrl : Excluded blrrrlrlrrrlrrrrlrl := fun _ h => reject tlrrrlrlrrrlrrrrlrl (by decide +kernel) h
private def blrrrlrlrrrlrrrrlrr : Box := right blrrrlrlrrrlrrrrlr 2 13
private def blrrrlrlrrrlrrrrlrrl : Box := left blrrrlrlrrrlrrrrlrr 3 765
private def tlrrrlrlrrrlrrrrlrrl : Tree := (.split 3 509 .leaf (.split 2 16 .leaf (.split 3 612 .leaf (.split 2 18 .leaf (.split 3 680 (.split 2 19 .leaf (.split 3 644 .leaf (.split 2 20 .leaf (.split 3 662 .leaf (.split 3 671 .leaf (.split 3 675 .leaf (.split 3 677 (.split 3 676 .leaf .leaf) .leaf))))))) (.split 2 19 .leaf (.split 3 720 (.split 2 20 .leaf .leaf) (.split 2 20 (.split 3 742 (.split 3 731 .leaf (.split 3 736 .leaf (.split 3 739 (.split 3 737 .leaf .leaf) .leaf))) .leaf) .leaf))))))))
private theorem clrrrlrlrrrlrrrrlrrl : Excluded blrrrlrlrrrlrrrrlrrl := fun _ h => reject tlrrrlrlrrrlrrrrlrrl (by decide +kernel) h
private def blrrrlrlrrrlrrrrlrrr : Box := right blrrrlrlrrrlrrrrlrr 3 765
private def blrrrlrlrrrlrrrrlrrrl : Box := left blrrrlrlrrrlrrrrlrrr 3 1533
private def tlrrrlrlrrrlrrrrlrrrl : Tree := (.split 2 16 (.split 3 1021 .leaf (.split 2 14 .leaf (.split 3 1226 .leaf (.split 2 15 .leaf (.split 3 1363 .leaf (.split 3 1443 (.split 3 1402 (.split 3 1382 .leaf (.split 3 1392 (.split 3 1387 (.split 3 1384 .leaf .leaf) .leaf) .leaf)) .leaf) .leaf)))))) (.split 3 1021 (.split 2 18 (.split 3 875 .leaf (.split 2 17 .leaf (.split 3 942 (.split 3 907 .leaf (.split 3 924 .leaf (.split 3 933 (.split 3 928 .leaf (.split 3 930 .leaf .leaf)) .leaf))) .leaf))) (.split 3 875 (.split 2 19 (.split 3 816 .leaf (.split 3 845 (.split 3 830 (.split 3 823 (.split 3 819 (.split 3 817 .leaf .leaf) .leaf) .leaf) .leaf) .leaf)) .leaf) .leaf)) (.split 2 18 (.split 3 1226 (.split 2 17 (.split 3 1114 (.split 3 1066 .leaf (.split 3 1089 .leaf (.split 3 1101 (.split 3 1095 .leaf (.split 3 1098 .leaf (.split 3 1099 .leaf (.split 3 1100 .leaf .leaf)))) .leaf))) .leaf) .leaf) .leaf) .leaf)))
private theorem clrrrlrlrrrlrrrrlrrrl : Excluded blrrrlrlrrrlrrrrlrrrl := fun _ h => reject tlrrrlrlrrrlrrrrlrrrl (by decide +kernel) h
private def blrrrlrlrrrlrrrrlrrrr : Box := right blrrrlrlrrrlrrrrlrrr 3 1533
private def tlrrrlrlrrrlrrrrlrrrr : Tree := (.split 2 16 (.split 3 3069 (.split 2 14 .leaf (.split 3 2045 (.split 2 15 (.split 3 1753 .leaf (.split 3 1888 .leaf (.split 3 1963 (.split 3 1925 .leaf (.split 3 1944 .leaf (.split 3 1953 .leaf (.split 3 1958 .leaf .leaf)))) .leaf))) .leaf) .leaf)) (.split 2 14 (.split 3 6141 (.split 3 4093 (.split 3 3508 .leaf (.split 3 3778 (.split 3 3638 .leaf (.split 3 3707 .leaf (.split 3 3742 (.split 3 3724 (.split 3 3715 .leaf (.split 3 3719 .leaf (.split 3 3721 .leaf .leaf))) .leaf) .leaf))) .leaf)) .leaf) .leaf) .leaf)) .leaf)
private theorem clrrrlrlrrrlrrrrlrrrr : Excluded blrrrlrlrrrlrrrrlrrrr := fun _ h => reject tlrrrlrlrrrlrrrrlrrrr (by decide +kernel) h
private theorem clrrrlrlrrrlrrrrlrrr : Excluded blrrrlrlrrrlrrrrlrrr := bisect blrrrlrlrrrlrrrrlrrr 3 1533 clrrrlrlrrrlrrrrlrrrl clrrrlrlrrrlrrrrlrrrr
private theorem clrrrlrlrrrlrrrrlrr : Excluded blrrrlrlrrrlrrrrlrr := bisect blrrrlrlrrrlrrrrlrr 3 765 clrrrlrlrrrlrrrrlrrl clrrrlrlrrrlrrrrlrrr
private theorem clrrrlrlrrrlrrrrlr : Excluded blrrrlrlrrrlrrrrlr := bisect blrrrlrlrrrlrrrrlr 2 13 clrrrlrlrrrlrrrrlrl clrrrlrlrrrlrrrrlrr
private theorem clrrrlrlrrrlrrrrl : Excluded blrrrlrlrrrlrrrrl := bisect blrrrlrlrrrlrrrrl 3 381 clrrrlrlrrrlrrrrll clrrrlrlrrrlrrrrlr
private def blrrrlrlrrrlrrrrr : Box := right blrrrlrlrrrlrrrr 2 21
private def blrrrlrlrrrlrrrrrl : Box := left blrrrlrlrrrlrrrrr 3 381
private def blrrrlrlrrrlrrrrrll : Box := left blrrrlrlrrrlrrrrrl 3 253
private def tlrrrlrlrrrlrrrrrll : Tree := (.split 2 45 .leaf (.split 3 217 .leaf (.split 2 93 .leaf .leaf)))
private theorem clrrrlrlrrrlrrrrrll : Excluded blrrrlrlrrrlrrrrrll := fun _ h => reject tlrrrlrlrrrlrrrrrll (by decide +kernel) h
private def blrrrlrlrrrlrrrrrlr : Box := right blrrrlrlrrrlrrrrrl 3 253
private def blrrrlrlrrrlrrrrrlrl : Box := left blrrrlrlrrrlrrrrrlr 2 45
private def tlrrrlrlrrrlrrrrrlrl : Tree := (.split 3 304 .leaf (.split 2 29 .leaf (.split 3 338 .leaf (.split 2 36 .leaf (.split 3 358 .leaf (.split 2 40 (.split 3 369 .leaf (.split 2 38 .leaf (.split 3 375 .leaf (.split 2 39 .leaf (.split 3 378 .leaf (.split 3 379 .leaf (.split 3 380 .leaf .leaf))))))) (.split 3 369 (.split 2 42 .leaf (.split 3 363 (.split 2 43 .leaf (.split 3 360 .leaf (.split 2 44 .leaf (.split 3 361 .leaf .leaf)))) (.split 2 43 (.split 3 366 .leaf (.split 3 367 .leaf (.split 3 368 .leaf .leaf))) (.split 3 366 (.split 2 44 (.split 3 364 .leaf .leaf) .leaf) .leaf)))) (.split 2 42 (.split 3 375 (.split 3 372 (.split 2 41 .leaf .leaf) (.split 2 41 .leaf .leaf)) (.split 3 378 (.split 2 41 (.split 3 376 .leaf .leaf) .leaf) .leaf)) .leaf))))))))
private theorem clrrrlrlrrrlrrrrrlrl : Excluded blrrrlrlrrrlrrrrrlrl := fun _ h => reject tlrrrlrlrrrlrrrrrlrl (by decide +kernel) h
private def blrrrlrlrrrlrrrrrlrr : Box := right blrrrlrlrrrlrrrrrlr 2 45
private def blrrrlrlrrrlrrrrrlrrl : Box := left blrrrlrlrrrlrrrrrlrr 3 304
private def blrrrlrlrrrlrrrrrlrrll : Box := left blrrrlrlrrrlrrrrrlrrl 2 93
private def tlrrrlrlrrrlrrrrrlrrll : Tree := (.split 3 276 .leaf (.split 2 61 .leaf (.split 3 289 .leaf (.split 2 74 .leaf (.split 3 296 .leaf (.split 2 83 .leaf (.split 3 300 (.split 2 88 .leaf (.split 3 298 .leaf (.split 2 90 .leaf (.split 2 91 (.split 3 299 .leaf .leaf) (.split 3 299 .leaf .leaf))))) (.split 2 88 (.split 3 302 (.split 2 85 .leaf (.split 2 86 .leaf (.split 3 301 .leaf .leaf))) (.split 2 85 (.split 3 303 .leaf .leaf) .leaf)) .leaf))))))))
private theorem clrrrlrlrrrlrrrrrlrrll : Excluded blrrrlrlrrrlrrrrrlrrll := fun _ h => reject tlrrrlrlrrrlrrrrrlrrll (by decide +kernel) h
private def blrrrlrlrrrlrrrrrlrrlr : Box := right blrrrlrlrrrlrrrrrlrrl 2 93
private def blrrrlrlrrrlrrrrrlrrlrl : Box := left blrrrlrlrrrlrrrrrlrrlr 3 276
private def blrrrlrlrrrlrrrrrlrrlrll : Box := left blrrrlrlrrrlrrrrrlrrlrl 2 189
private def tlrrrlrlrrrlrrrrrlrrlrll : Tree := (.split 3 264 .leaf (.split 2 125 .leaf (.split 2 151 .leaf (.split 3 270 .leaf (.split 2 168 .leaf (.split 3 273 .leaf (.split 2 178 .leaf (.split 3 274 .leaf (.split 2 183 .leaf (.split 3 275 .leaf .leaf))))))))))
private theorem clrrrlrlrrrlrrrrrlrrlrll : Excluded blrrrlrlrrrlrrrrrlrrlrll := fun _ h => reject tlrrrlrlrrrlrrrrrlrrlrll (by decide +kernel) h
private def blrrrlrlrrrlrrrrrlrrlrlr : Box := right blrrrlrlrrrlrrrrrlrrlrl 2 189
private def blrrrlrlrrrlrrrrrlrrlrlrl : Box := left blrrrlrlrrrlrrrrrlrrlrlr 3 264
private def tlrrrlrlrrrlrrrrrlrrlrlrl : Tree := (.split 2 381 .leaf (.split 2 765 (.split 3 258 .leaf (.split 2 509 (.split 3 261 .leaf (.split 2 436 .leaf (.split 3 262 .leaf (.split 2 470 (.split 3 263 .leaf .leaf) (.split 3 263 .leaf .leaf))))) (.split 3 261 (.split 2 612 .leaf .leaf) (.split 2 612 (.split 3 262 .leaf (.split 2 556 (.split 3 263 (.split 2 532 .leaf (.split 2 544 (.split 2 538 .leaf (.split 2 541 (.split 2 539 .leaf .leaf) .leaf)) .leaf)) .leaf) .leaf)) (.split 3 262 .leaf .leaf))))) (.split 3 258 (.split 2 1533 .leaf (.split 3 255 .leaf (.split 2 3069 (.split 3 256 .leaf (.split 2 2045 .leaf (.split 3 257 .leaf .leaf))) (.split 3 256 .leaf (.split 2 6141 (.split 3 257 .leaf .leaf) (.split 3 257 (.split 2 12285 (.split 2 8189 .leaf (.split 2 9828 .leaf (.split 2 10920 (.split 2 10345 (.split 2 10080 (.split 2 9952 .leaf (.split 2 10016 (.split 2 9984 .leaf (.split 2 10000 (.split 2 9992 .leaf (.split 2 9996 .leaf .leaf)) (.split 2 10008 (.split 2 10004 .leaf .leaf) .leaf))) .leaf)) .leaf) .leaf) .leaf))) .leaf) .leaf)))))) (.split 2 1533 (.split 3 261 (.split 2 1021 (.split 3 259 .leaf (.split 2 875 (.split 3 260 .leaf .leaf) (.split 3 260 .leaf .leaf))) (.split 3 259 .leaf (.split 2 1226 (.split 3 260 .leaf .leaf) .leaf))) .leaf) (.split 3 261 (.split 2 3069 .leaf .leaf) .leaf)))))
private theorem clrrrlrlrrrlrrrrrlrrlrlrl : Excluded blrrrlrlrrrlrrrrrlrrlrlrl := fun _ h => reject tlrrrlrlrrrlrrrrrlrrlrlrl (by decide +kernel) h
private def blrrrlrlrrrlrrrrrlrrlrlrr : Box := right blrrrlrlrrrlrrrrrlrrlrlr 3 264
private def tlrrrlrlrrrlrrrrrlrrlrlrr : Tree := (.split 2 381 (.split 2 253 (.split 3 270 .leaf (.split 2 217 (.split 3 273 (.split 2 202 .leaf (.split 3 271 .leaf (.split 2 209 .leaf .leaf))) (.split 2 202 (.split 3 274 .leaf (.split 2 195 (.split 3 275 .leaf .leaf) .leaf)) (.split 3 274 .leaf .leaf))) (.split 3 273 (.split 2 234 (.split 3 271 .leaf (.split 2 225 (.split 3 272 .leaf .leaf) (.split 3 272 .leaf .leaf))) (.split 3 271 (.split 2 243 .leaf (.split 2 248 (.split 2 245 .leaf (.split 2 246 .leaf .leaf)) .leaf)) .leaf)) .leaf))) (.split 3 270 (.split 2 304 (.split 3 267 .leaf (.split 2 276 (.split 3 268 .leaf (.split 2 264 (.split 3 269 .leaf .leaf) (.split 3 269 .leaf .leaf))) (.split 3 268 .leaf (.split 2 289 (.split 3 269 (.split 2 282 .leaf (.split 2 285 (.split 2 283 .leaf (.split 2 284 .leaf .leaf)) .leaf)) .leaf) .leaf)))) (.split 3 267 (.split 2 338 (.split 3 265 .leaf (.split 2 320 .leaf (.split 3 266 .leaf .leaf))) (.split 3 265 .leaf (.split 2 358 (.split 3 266 .leaf .leaf) (.split 3 266 .leaf .leaf)))) (.split 2 338 (.split 3 268 .leaf .leaf) .leaf))) .leaf)) (.split 2 765 (.split 3 270 (.split 2 509 (.split 3 267 (.split 2 436 (.split 3 265 .leaf .leaf) .leaf) .leaf) .leaf) .leaf) .leaf))
private theorem clrrrlrlrrrlrrrrrlrrlrlrr : Excluded blrrrlrlrrrlrrrrrlrrlrlrr := fun _ h => reject tlrrrlrlrrrlrrrrrlrrlrlrr (by decide +kernel) h
private theorem clrrrlrlrrrlrrrrrlrrlrlr : Excluded blrrrlrlrrrlrrrrrlrrlrlr := bisect blrrrlrlrrrlrrrrrlrrlrlr 3 264 clrrrlrlrrrlrrrrrlrrlrlrl clrrrlrlrrrlrrrrrlrrlrlrr
private theorem clrrrlrlrrrlrrrrrlrrlrl : Excluded blrrrlrlrrrlrrrrrlrrlrl := bisect blrrrlrlrrrlrrrrrlrrlrl 2 189 clrrrlrlrrrlrrrrrlrrlrll clrrrlrlrrrlrrrrrlrrlrlr
private def blrrrlrlrrrlrrrrrlrrlrr : Box := right blrrrlrlrrrlrrrrrlrrlr 3 276
private def blrrrlrlrrrlrrrrrlrrlrrl : Box := left blrrrlrlrrrlrrrrrlrrlrr 2 189
private def blrrrlrlrrrlrrrrrlrrlrrll : Box := left blrrrlrlrrrlrrrrrlrrlrrl 3 289
private def tlrrrlrlrrrlrrrrrlrrlrrll : Tree := (.split 2 125 (.split 2 107 .leaf (.split 3 282 .leaf (.split 3 285 .leaf (.split 2 115 .leaf (.split 3 287 (.split 2 120 .leaf (.split 2 122 .leaf (.split 3 286 .leaf .leaf))) (.split 2 120 (.split 2 117 (.split 3 288 .leaf .leaf) (.split 3 288 .leaf .leaf)) .leaf)))))) (.split 2 151 (.split 3 282 (.split 2 137 .leaf (.split 3 279 .leaf (.split 2 144 .leaf (.split 3 280 .leaf (.split 2 147 (.split 3 281 .leaf .leaf) (.split 3 281 (.split 2 149 .leaf (.split 2 150 .leaf .leaf)) .leaf)))))) (.split 2 137 (.split 3 285 (.split 2 131 (.split 3 283 .leaf (.split 2 128 .leaf (.split 3 284 .leaf .leaf))) (.split 3 283 .leaf (.split 2 134 (.split 3 284 .leaf .leaf) (.split 3 284 .leaf .leaf)))) (.split 2 131 (.split 3 287 (.split 2 128 (.split 3 286 .leaf .leaf) .leaf) .leaf) .leaf)) (.split 3 285 (.split 2 144 (.split 3 283 (.split 2 140 (.split 2 138 .leaf .leaf) .leaf) .leaf) .leaf) .leaf))) (.split 3 282 (.split 2 168 (.split 3 279 (.split 2 159 .leaf (.split 3 277 .leaf (.split 2 163 (.split 3 278 .leaf .leaf) (.split 3 278 .leaf .leaf)))) (.split 2 159 (.split 3 280 .leaf .leaf) .leaf)) (.split 3 279 (.split 2 178 (.split 3 277 (.split 2 173 .leaf (.split 2 175 .leaf (.split 2 176 .leaf (.split 2 177 .leaf .leaf)))) (.split 2 173 (.split 3 278 .leaf .leaf) .leaf)) .leaf) .leaf)) .leaf)))
private theorem clrrrlrlrrrlrrrrrlrrlrrll : Excluded blrrrlrlrrrlrrrrrlrrlrrll := fun _ h => reject tlrrrlrlrrrlrrrrrlrrlrrll (by decide +kernel) h
private def blrrrlrlrrrlrrrrrlrrlrrlr : Box := right blrrrlrlrrrlrrrrrlrrlrrl 3 289
private def tlrrrlrlrrrlrrrrrlrrlrrlr : Tree := (.split 2 125 (.split 3 296 (.split 2 107 (.split 2 100 (.split 3 292 .leaf (.split 2 96 .leaf (.split 3 294 .leaf (.split 2 98 .leaf (.split 3 295 .leaf .leaf))))) (.split 3 292 .leaf (.split 3 294 (.split 2 103 (.split 3 293 .leaf .leaf) (.split 2 105 (.split 3 293 .leaf .leaf) .leaf)) .leaf))) (.split 2 115 (.split 3 292 (.split 2 111 (.split 3 290 .leaf (.split 2 109 (.split 3 291 .leaf .leaf) (.split 3 291 .leaf .leaf))) (.split 3 290 .leaf .leaf)) .leaf) .leaf)) (.split 2 107 (.split 3 300 (.split 2 100 (.split 2 96 (.split 3 298 (.split 2 94 (.split 3 297 .leaf .leaf) (.split 3 297 .leaf .leaf)) .leaf) .leaf) .leaf) .leaf) .leaf)) .leaf)
private theorem clrrrlrlrrrlrrrrrlrrlrrlr : Excluded blrrrlrlrrrlrrrrrlrrlrrlr := fun _ h => reject tlrrrlrlrrrlrrrrrlrrlrrlr (by decide +kernel) h
private theorem clrrrlrlrrrlrrrrrlrrlrrl : Excluded blrrrlrlrrrlrrrrrlrrlrrl := bisect blrrrlrlrrrlrrrrrlrrlrrl 3 289 clrrrlrlrrrlrrrrrlrrlrrll clrrrlrlrrrlrrrrrlrrlrrlr
private def blrrrlrlrrrlrrrrrlrrlrrr : Box := right blrrrlrlrrrlrrrrrlrrlrr 2 189
private def tlrrrlrlrrrlrrrrrlrrlrrr : Tree := (.split 3 289 (.split 2 381 .leaf .leaf) .leaf)
private theorem clrrrlrlrrrlrrrrrlrrlrrr : Excluded blrrrlrlrrrlrrrrrlrrlrrr := fun _ h => reject tlrrrlrlrrrlrrrrrlrrlrrr (by decide +kernel) h
private theorem clrrrlrlrrrlrrrrrlrrlrr : Excluded blrrrlrlrrrlrrrrrlrrlrr := bisect blrrrlrlrrrlrrrrrlrrlrr 2 189 clrrrlrlrrrlrrrrrlrrlrrl clrrrlrlrrrlrrrrrlrrlrrr
private theorem clrrrlrlrrrlrrrrrlrrlr : Excluded blrrrlrlrrrlrrrrrlrrlr := bisect blrrrlrlrrrlrrrrrlrrlr 3 276 clrrrlrlrrrlrrrrrlrrlrl clrrrlrlrrrlrrrrrlrrlrr
private theorem clrrrlrlrrrlrrrrrlrrl : Excluded blrrrlrlrrrlrrrrrlrrl := bisect blrrrlrlrrrlrrrrrlrrl 2 93 clrrrlrlrrrlrrrrrlrrll clrrrlrlrrrlrrrrrlrrlr
private def blrrrlrlrrrlrrrrrlrrr : Box := right blrrrlrlrrrlrrrrrlrr 3 304
private def blrrrlrlrrrlrrrrrlrrrl : Box := left blrrrlrlrrrlrrrrrlrrr 2 93
private def blrrrlrlrrrlrrrrrlrrrll : Box := left blrrrlrlrrrlrrrrrlrrrl 3 338
private def blrrrlrlrrrlrrrrrlrrrlll : Box := left blrrrlrlrrrlrrrrrlrrrll 2 61
private def tlrrrlrlrrrlrrrrrlrrrlll : Tree := (.split 3 320 .leaf (.split 2 52 .leaf (.split 3 329 (.split 2 56 .leaf (.split 3 324 .leaf (.split 2 58 .leaf (.split 3 326 .leaf (.split 2 59 .leaf (.split 3 327 .leaf .leaf)))))) (.split 2 56 (.split 3 333 .leaf (.split 2 54 .leaf (.split 3 335 (.split 2 55 .leaf (.split 3 334 .leaf .leaf)) (.split 2 55 (.split 3 336 .leaf .leaf) .leaf)))) (.split 3 333 (.split 2 58 (.split 3 331 (.split 2 57 .leaf .leaf) (.split 2 57 (.split 3 332 .leaf .leaf) .leaf)) .leaf) .leaf)))))
private theorem clrrrlrlrrrlrrrrrlrrrlll : Excluded blrrrlrlrrrlrrrrrlrrrlll := fun _ h => reject tlrrrlrlrrrlrrrrrlrrrlll (by decide +kernel) h
private def blrrrlrlrrrlrrrrrlrrrllr : Box := right blrrrlrlrrrlrrrrrlrrrll 2 61
private def tlrrrlrlrrrlrrrrrlrrrllr : Tree := (.split 3 320 (.split 2 74 (.split 3 312 (.split 2 67 .leaf (.split 3 308 .leaf (.split 2 70 .leaf (.split 2 72 .leaf (.split 3 310 .leaf (.split 2 73 .leaf (.split 3 311 .leaf .leaf))))))) (.split 2 67 (.split 3 316 .leaf (.split 2 64 .leaf (.split 3 318 .leaf (.split 2 65 .leaf (.split 2 66 (.split 3 319 .leaf .leaf) .leaf))))) (.split 3 316 (.split 2 70 (.split 3 314 .leaf (.split 2 68 .leaf (.split 2 69 .leaf (.split 3 315 .leaf .leaf)))) (.split 2 72 (.split 3 314 (.split 2 71 .leaf (.split 3 313 .leaf .leaf)) .leaf) .leaf)) (.split 2 70 (.split 3 318 (.split 2 68 (.split 3 317 .leaf .leaf) .leaf) .leaf) .leaf)))) (.split 3 312 (.split 2 83 (.split 3 308 (.split 2 78 .leaf (.split 2 80 (.split 3 306 .leaf (.split 3 307 (.split 2 79 .leaf .leaf) .leaf)) (.split 3 306 (.split 2 81 (.split 3 305 .leaf .leaf) (.split 3 305 .leaf .leaf)) .leaf))) (.split 2 78 (.split 3 310 (.split 2 76 (.split 3 309 .leaf .leaf) (.split 3 309 .leaf .leaf)) .leaf) .leaf)) .leaf) .leaf)) (.split 2 74 (.split 3 329 (.split 2 67 (.split 3 324 (.split 2 64 (.split 3 322 .leaf (.split 2 62 .leaf (.split 2 63 (.split 3 323 .leaf .leaf) .leaf))) (.split 3 322 (.split 2 65 (.split 3 321 .leaf .leaf) .leaf) .leaf)) (.split 2 64 (.split 3 326 (.split 2 62 .leaf .leaf) .leaf) .leaf)) .leaf) .leaf) .leaf))
private theorem clrrrlrlrrrlrrrrrlrrrllr : Excluded blrrrlrlrrrlrrrrrlrrrllr := fun _ h => reject tlrrrlrlrrrlrrrrrlrrrllr (by decide +kernel) h
private theorem clrrrlrlrrrlrrrrrlrrrll : Excluded blrrrlrlrrrlrrrrrlrrrll := bisect blrrrlrlrrrlrrrrrlrrrll 2 61 clrrrlrlrrrlrrrrrlrrrlll clrrrlrlrrrlrrrrrlrrrllr
private def blrrrlrlrrrlrrrrrlrrrlr : Box := right blrrrlrlrrrlrrrrrlrrrl 3 338
private def tlrrrlrlrrrlrrrrrlrrrlr : Tree := (.split 2 61 (.split 3 358 (.split 2 52 (.split 3 348 (.split 2 48 .leaf (.split 3 343 (.split 2 50 .leaf (.split 3 340 .leaf (.split 2 51 .leaf (.split 3 341 .leaf (.split 3 342 .leaf .leaf))))) (.split 2 50 (.split 3 345 .leaf (.split 2 49 .leaf (.split 3 346 .leaf (.split 3 347 .leaf .leaf)))) (.split 3 345 (.split 2 51 (.split 3 344 .leaf .leaf) .leaf) .leaf)))) (.split 2 48 (.split 3 353 (.split 2 46 .leaf (.split 3 350 .leaf (.split 2 47 .leaf (.split 3 351 .leaf (.split 3 352 .leaf .leaf))))) (.split 2 46 .leaf (.split 3 355 (.split 2 47 .leaf .leaf) .leaf))) (.split 3 353 (.split 2 50 (.split 3 350 (.split 2 49 (.split 3 349 .leaf .leaf) .leaf) .leaf) .leaf) .leaf))) (.split 3 348 (.split 2 56 (.split 3 343 (.split 2 54 (.split 3 340 (.split 2 53 .leaf .leaf) .leaf) .leaf) .leaf) .leaf) .leaf)) (.split 2 52 (.split 3 369 (.split 2 48 .leaf .leaf) .leaf) .leaf)) .leaf)
private theorem clrrrlrlrrrlrrrrrlrrrlr : Excluded blrrrlrlrrrlrrrrrlrrrlr := fun _ h => reject tlrrrlrlrrrlrrrrrlrrrlr (by decide +kernel) h
private theorem clrrrlrlrrrlrrrrrlrrrl : Excluded blrrrlrlrrrlrrrrrlrrrl := bisect blrrrlrlrrrlrrrrrlrrrl 3 338 clrrrlrlrrrlrrrrrlrrrll clrrrlrlrrrlrrrrrlrrrlr
private def blrrrlrlrrrlrrrrrlrrrr : Box := right blrrrlrlrrrlrrrrrlrrr 2 93
private def tlrrrlrlrrrlrrrrrlrrrr : Tree := .leaf
private theorem clrrrlrlrrrlrrrrrlrrrr : Excluded blrrrlrlrrrlrrrrrlrrrr := fun _ h => reject tlrrrlrlrrrlrrrrrlrrrr (by decide +kernel) h
private theorem clrrrlrlrrrlrrrrrlrrr : Excluded blrrrlrlrrrlrrrrrlrrr := bisect blrrrlrlrrrlrrrrrlrrr 2 93 clrrrlrlrrrlrrrrrlrrrl clrrrlrlrrrlrrrrrlrrrr
private theorem clrrrlrlrrrlrrrrrlrr : Excluded blrrrlrlrrrlrrrrrlrr := bisect blrrrlrlrrrlrrrrrlrr 3 304 clrrrlrlrrrlrrrrrlrrl clrrrlrlrrrlrrrrrlrrr
private theorem clrrrlrlrrrlrrrrrlr : Excluded blrrrlrlrrrlrrrrrlr := bisect blrrrlrlrrrlrrrrrlr 2 45 clrrrlrlrrrlrrrrrlrl clrrrlrlrrrlrrrrrlrr
private theorem clrrrlrlrrrlrrrrrl : Excluded blrrrlrlrrrlrrrrrl := bisect blrrrlrlrrrlrrrrrl 3 253 clrrrlrlrrrlrrrrrll clrrrlrlrrrlrrrrrlr
private def blrrrlrlrrrlrrrrrr : Box := right blrrrlrlrrrlrrrrr 3 381
private def blrrrlrlrrrlrrrrrrl : Box := left blrrrlrlrrrlrrrrrr 3 765
private def blrrrlrlrrrlrrrrrrll : Box := left blrrrlrlrrrlrrrrrrl 2 45
private def blrrrlrlrrrlrrrrrrlll : Box := left blrrrlrlrrrlrrrrrrll 3 509
private def blrrrlrlrrrlrrrrrrllll : Box := left blrrrlrlrrrlrrrrrrlll 2 29
private def tlrrrlrlrrrlrrrrrrllll : Tree := (.split 3 436 .leaf (.split 2 25 .leaf (.split 3 470 (.split 2 27 .leaf (.split 3 452 .leaf (.split 3 461 .leaf (.split 2 28 .leaf (.split 3 465 .leaf (.split 3 467 (.split 3 466 .leaf .leaf) .leaf)))))) (.split 2 27 (.split 3 489 .leaf (.split 2 26 .leaf (.split 3 499 (.split 3 494 .leaf (.split 3 496 .leaf .leaf)) .leaf))) (.split 3 489 (.split 3 479 (.split 2 28 .leaf .leaf) (.split 2 28 (.split 3 484 (.split 3 481 (.split 3 480 .leaf .leaf) .leaf) .leaf) .leaf)) .leaf)))))
private theorem clrrrlrlrrrlrrrrrrllll : Excluded blrrrlrlrrrlrrrrrrllll := fun _ h => reject tlrrrlrlrrrlrrrrrrllll (by decide +kernel) h
private def blrrrlrlrrrlrrrrrrlllr : Box := right blrrrlrlrrrlrrrrrrlll 2 29
private def tlrrrlrlrrrlrrrrrrlllr : Tree := (.split 3 436 (.split 2 36 (.split 3 407 (.split 2 32 .leaf (.split 3 394 .leaf (.split 2 34 .leaf (.split 3 400 .leaf (.split 2 35 .leaf (.split 3 403 (.split 3 401 .leaf (.split 3 402 .leaf .leaf)) .leaf)))))) (.split 2 32 (.split 3 421 .leaf (.split 2 30 .leaf (.split 3 428 .leaf (.split 2 31 .leaf (.split 3 432 .leaf (.split 3 434 (.split 3 433 .leaf .leaf) .leaf)))))) (.split 3 421 (.split 2 34 (.split 3 414 .leaf (.split 2 33 .leaf (.split 3 417 (.split 3 415 .leaf (.split 3 416 .leaf .leaf)) .leaf))) (.split 3 414 (.split 2 35 (.split 3 410 (.split 3 408 .leaf .leaf) .leaf) .leaf) .leaf)) (.split 2 34 (.split 3 428 (.split 2 33 (.split 3 424 .leaf .leaf) .leaf) .leaf) .leaf)))) (.split 3 407 (.split 2 40 (.split 3 394 (.split 2 38 (.split 3 387 .leaf (.split 2 37 .leaf (.split 3 390 .leaf .leaf))) (.split 3 387 (.split 2 39 (.split 3 384 .leaf (.split 3 385 .leaf .leaf)) .leaf) .leaf)) (.split 2 38 (.split 3 400 (.split 2 37 (.split 3 397 (.split 3 395 .leaf (.split 3 396 .leaf .leaf)) .leaf) .leaf) .leaf) .leaf)) .leaf) .leaf)) (.split 2 36 (.split 3 470 (.split 2 32 (.split 3 452 (.split 2 30 .leaf (.split 3 444 (.split 2 31 (.split 3 440 .leaf (.split 3 442 .leaf .leaf)) .leaf) .leaf)) (.split 2 30 (.split 3 461 (.split 3 456 (.split 3 454 (.split 3 453 .leaf .leaf) .leaf) .leaf) .leaf) .leaf)) .leaf) .leaf) .leaf))
private theorem clrrrlrlrrrlrrrrrrlllr : Excluded blrrrlrlrrrlrrrrrrlllr := fun _ h => reject tlrrrlrlrrrlrrrrrrlllr (by decide +kernel) h
private theorem clrrrlrlrrrlrrrrrrlll : Excluded blrrrlrlrrrlrrrrrrlll := bisect blrrrlrlrrrlrrrrrrlll 2 29 clrrrlrlrrrlrrrrrrllll clrrrlrlrrrlrrrrrrlllr
private def blrrrlrlrrrlrrrrrrllr : Box := right blrrrlrlrrrlrrrrrrll 3 509
private def tlrrrlrlrrrlrrrrrrllr : Tree := (.split 2 29 (.split 3 612 (.split 2 25 (.split 3 556 (.split 2 23 .leaf (.split 3 532 .leaf (.split 2 24 .leaf (.split 3 544 (.split 3 538 (.split 3 535 .leaf (.split 3 536 .leaf .leaf)) .leaf) .leaf)))) (.split 2 23 (.split 3 583 .leaf (.split 2 22 .leaf (.split 3 597 (.split 3 590 .leaf (.split 3 593 (.split 3 591 .leaf (.split 3 592 .leaf .leaf)) .leaf)) .leaf))) (.split 3 583 (.split 2 24 (.split 3 569 (.split 3 562 (.split 3 559 .leaf (.split 3 560 .leaf (.split 3 561 .leaf .leaf))) .leaf) .leaf) .leaf) .leaf))) (.split 3 556 (.split 2 27 (.split 3 532 (.split 3 520 (.split 2 26 (.split 3 514 .leaf .leaf) .leaf) .leaf) .leaf) .leaf) .leaf)) (.split 2 25 (.split 3 680 (.split 2 23 (.split 3 644 (.split 2 22 (.split 3 628 .leaf (.split 3 636 (.split 3 632 (.split 3 630 (.split 3 629 .leaf .leaf) .leaf) .leaf) .leaf)) .leaf) .leaf) .leaf) .leaf) .leaf)) .leaf)
private theorem clrrrlrlrrrlrrrrrrllr : Excluded blrrrlrlrrrlrrrrrrllr := fun _ h => reject tlrrrlrlrrrlrrrrrrllr (by decide +kernel) h
private theorem clrrrlrlrrrlrrrrrrll : Excluded blrrrlrlrrrlrrrrrrll := bisect blrrrlrlrrrlrrrrrrll 3 509 clrrrlrlrrrlrrrrrrlll clrrrlrlrrrlrrrrrrllr
private def blrrrlrlrrrlrrrrrrlr : Box := right blrrrlrlrrrlrrrrrrl 2 45
private def tlrrrlrlrrrlrrrrrrlr : Tree := .leaf
private theorem clrrrlrlrrrlrrrrrrlr : Excluded blrrrlrlrrrlrrrrrrlr := fun _ h => reject tlrrrlrlrrrlrrrrrrlr (by decide +kernel) h
private theorem clrrrlrlrrrlrrrrrrl : Excluded blrrrlrlrrrlrrrrrrl := bisect blrrrlrlrrrlrrrrrrl 2 45 clrrrlrlrrrlrrrrrrll clrrrlrlrrrlrrrrrrlr
private def blrrrlrlrrrlrrrrrrr : Box := right blrrrlrlrrrlrrrrrr 3 765
private def tlrrrlrlrrrlrrrrrrr : Tree := .leaf
private theorem clrrrlrlrrrlrrrrrrr : Excluded blrrrlrlrrrlrrrrrrr := fun _ h => reject tlrrrlrlrrrlrrrrrrr (by decide +kernel) h
private theorem clrrrlrlrrrlrrrrrr : Excluded blrrrlrlrrrlrrrrrr := bisect blrrrlrlrrrlrrrrrr 3 765 clrrrlrlrrrlrrrrrrl clrrrlrlrrrlrrrrrrr
private theorem clrrrlrlrrrlrrrrr : Excluded blrrrlrlrrrlrrrrr := bisect blrrrlrlrrrlrrrrr 3 381 clrrrlrlrrrlrrrrrl clrrrlrlrrrlrrrrrr
private theorem clrrrlrlrrrlrrrr : Excluded blrrrlrlrrrlrrrr := bisect blrrrlrlrrrlrrrr 2 21 clrrrlrlrrrlrrrrl clrrrlrlrrrlrrrrr
private theorem clrrrlrlrrrlrrr : Excluded blrrrlrlrrrlrrr := bisect blrrrlrlrrrlrrr 1 6 clrrrlrlrrrlrrrl clrrrlrlrrrlrrrr
private theorem clrrrlrlrrrlrr : Excluded blrrrlrlrrrlrr := bisect blrrrlrlrrrlrr 3 189 clrrrlrlrrrlrrl clrrrlrlrrrlrrr
private theorem clrrrlrlrrrlr : Excluded blrrrlrlrrrlr := bisect blrrrlrlrrrlr 2 9 clrrrlrlrrrlrl clrrrlrlrrrlrr
private theorem clrrrlrlrrrl : Excluded blrrrlrlrrrl := bisect blrrrlrlrrrl 3 93 clrrrlrlrrrll clrrrlrlrrrlr
private def blrrrlrlrrrr : Box := right blrrrlrlrrr 1 7
private def tlrrrlrlrrrr : Tree := .leaf
private theorem clrrrlrlrrrr : Excluded blrrrlrlrrrr := fun _ h => reject tlrrrlrlrrrr (by decide +kernel) h
private theorem clrrrlrlrrr : Excluded blrrrlrlrrr := bisect blrrrlrlrrr 1 7 clrrrlrlrrrl clrrrlrlrrrr
private theorem clrrrlrlrr : Excluded blrrrlrlrr := bisect blrrrlrlrr 3 45 clrrrlrlrrl clrrrlrlrrr
private theorem clrrrlrlr : Excluded blrrrlrlr := bisect blrrrlrlr 2 3 clrrrlrlrl clrrrlrlrr
private theorem clrrrlrl : Excluded blrrrlrl := bisect blrrrlrl 1 5 clrrrlrll clrrrlrlr
private def blrrrlrr : Box := right blrrrlr 0 2
private def tlrrrlrr : Tree := .leaf
private theorem clrrrlrr : Excluded blrrrlrr := fun _ h => reject tlrrrlrr (by decide +kernel) h
private theorem clrrrlr : Excluded blrrrlr := bisect blrrrlr 0 2 clrrrlrl clrrrlrr
private theorem clrrrl : Excluded blrrrl := bisect blrrrl 3 21 clrrrll clrrrlr
private def blrrrr : Box := right blrrr 1 9
private def tlrrrr : Tree := .leaf
private theorem clrrrr : Excluded blrrrr := fun _ h => reject tlrrrr (by decide +kernel) h
private theorem clrrr : Excluded blrrr := bisect blrrr 1 9 clrrrl clrrrr
private theorem clrr : Excluded blrr := bisect blrr 0 1 clrrl clrrr
private theorem clr : Excluded blr := bisect blr 3 9 clrl clrr
private theorem cl : Excluded bl := bisect bl 1 3 cll clr
private def br : Box := right domain 0 3
private def brl : Box := left br 3 9
private def trl : Tree := (.split 1 3 (.split 0 9 (.split 2 3 (.split 1 1 .leaf .leaf) .leaf) .leaf) .leaf)
private theorem crl : Excluded brl := fun _ h => reject trl (by decide +kernel) h
private def brr : Box := right br 3 9
private def brrl : Box := left brr 1 3
private def brrll : Box := left brrl 0 9
private def brrlll : Box := left brrll 1 1
private def brrllll : Box := left brrlll 0 5
private def brrlllll : Box := left brrllll 2 3
private def trrlllll : Tree := (.split 3 21 (.split 2 1 .leaf (.split 0 4 .leaf .leaf)) (.split 0 4 (.split 2 1 .leaf (.split 3 45 (.split 3 29 (.split 2 2 .leaf (.split 3 25 .leaf (.split 3 27 .leaf .leaf))) (.split 2 2 (.split 3 36 .leaf (.split 3 40 .leaf (.split 3 42 (.split 3 41 .leaf .leaf) .leaf))) .leaf)) (.split 3 93 (.split 2 2 .leaf .leaf) .leaf))) .leaf))
private theorem crrlllll : Excluded brrlllll := fun _ h => reject trrlllll (by decide +kernel) h
private def brrllllr : Box := right brrllll 2 3
private def brrllllrl : Box := left brrllllr 3 21
private def trrllllrl : Tree := (.split 3 13 .leaf (.split 2 9 (.split 0 4 (.split 3 16 .leaf (.split 2 5 .leaf (.split 3 18 .leaf (.split 2 7 (.split 3 19 .leaf (.split 2 6 (.split 3 20 .leaf .leaf) (.split 3 20 .leaf .leaf))) (.split 3 19 .leaf (.split 3 20 .leaf .leaf)))))) .leaf) (.split 0 4 (.split 3 16 (.split 2 21 .leaf .leaf) (.split 2 21 (.split 3 18 (.split 2 13 .leaf (.split 2 16 .leaf (.split 3 17 .leaf .leaf))) (.split 2 13 (.split 3 19 (.split 2 11 (.split 2 10 .leaf .leaf) .leaf) .leaf) .leaf)) (.split 3 18 (.split 2 45 (.split 2 29 (.split 3 17 .leaf .leaf) (.split 3 17 .leaf .leaf)) (.split 2 93 (.split 3 17 (.split 2 61 .leaf (.split 2 74 .leaf .leaf)) .leaf) (.split 3 17 (.split 2 189 (.split 2 125 (.split 2 107 .leaf (.split 2 115 .leaf (.split 2 120 .leaf (.split 2 122 .leaf (.split 2 123 .leaf .leaf))))) (.split 2 151 (.split 2 137 (.split 2 131 (.split 2 128 (.split 2 126 .leaf (.split 2 127 .leaf .leaf)) .leaf) .leaf) .leaf) .leaf)) (.split 2 381 .leaf .leaf)) .leaf))) .leaf))) .leaf)))
private theorem crrllllrl : Excluded brrllllrl := fun _ h => reject trrllllrl (by decide +kernel) h
private def brrllllrr : Box := right brrllllr 3 21
private def brrllllrrl : Box := left brrllllrr 3 45
private def trrllllrrl : Tree := (.split 0 4 (.split 2 9 (.split 3 29 (.split 2 5 (.split 3 25 (.split 2 4 (.split 3 23 .leaf .leaf) (.split 3 23 (.split 3 22 .leaf .leaf) .leaf)) .leaf) (.split 3 25 (.split 2 7 .leaf .leaf) .leaf)) .leaf) .leaf) (.split 2 9 .leaf (.split 3 29 .leaf (.split 2 21 .leaf (.split 3 36 .leaf (.split 2 45 (.split 3 40 .leaf (.split 2 29 .leaf (.split 3 42 .leaf (.split 2 36 (.split 3 43 .leaf (.split 2 32 .leaf (.split 3 44 .leaf .leaf))) (.split 3 43 .leaf (.split 2 40 (.split 3 44 .leaf .leaf) (.split 3 44 .leaf .leaf))))))) (.split 3 40 (.split 2 93 .leaf (.split 3 38 .leaf (.split 2 189 .leaf .leaf))) (.split 2 93 (.split 3 42 (.split 2 61 .leaf (.split 2 74 .leaf (.split 3 41 .leaf .leaf))) (.split 2 61 (.split 3 43 (.split 2 52 .leaf (.split 2 56 .leaf (.split 2 58 (.split 2 57 .leaf .leaf) .leaf))) .leaf) (.split 3 43 (.split 2 74 .leaf .leaf) .leaf))) (.split 3 42 (.split 2 189 (.split 2 125 (.split 3 41 .leaf .leaf) (.split 3 41 .leaf .leaf)) (.split 2 381 (.split 3 41 (.split 2 253 (.split 2 217 .leaf (.split 2 234 .leaf (.split 2 243 (.split 2 238 .leaf (.split 2 240 .leaf (.split 2 241 .leaf (.split 2 242 .leaf .leaf)))) (.split 2 248 .leaf .leaf)))) (.split 2 304 .leaf .leaf)) .leaf) .leaf)) .leaf)))))))))
private theorem crrllllrrl : Excluded brrllllrrl := fun _ h => reject trrllllrrl (by decide +kernel) h
private def brrllllrrr : Box := right brrllllrr 3 45
private def brrllllrrrl : Box := left brrllllrrr 0 4
private def trrllllrrrl : Tree := .leaf
private theorem crrllllrrrl : Excluded brrllllrrrl := fun _ h => reject trrllllrrrl (by decide +kernel) h
private def brrllllrrrr : Box := right brrllllrrr 0 4
private def brrllllrrrrl : Box := left brrllllrrrr 2 9
private def trrllllrrrrl : Tree := (.split 3 93 (.split 2 5 .leaf (.split 3 61 .leaf (.split 2 7 (.split 3 74 .leaf (.split 3 83 (.split 2 6 .leaf (.split 3 78 .leaf (.split 3 80 (.split 3 79 .leaf .leaf) .leaf))) (.split 2 6 .leaf .leaf))) (.split 3 74 (.split 3 67 (.split 2 8 .leaf (.split 3 64 .leaf (.split 3 65 .leaf .leaf))) (.split 2 8 (.split 3 70 .leaf .leaf) .leaf)) .leaf)))) (.split 2 5 (.split 3 189 (.split 3 125 (.split 2 4 .leaf .leaf) (.split 2 4 .leaf (.split 3 151 (.split 3 137 (.split 3 131 (.split 3 128 .leaf .leaf) .leaf) .leaf) .leaf))) (.split 3 381 (.split 2 4 (.split 3 253 .leaf (.split 3 304 (.split 3 276 .leaf (.split 3 289 (.split 3 282 (.split 3 279 .leaf (.split 3 280 .leaf .leaf)) .leaf) .leaf)) .leaf)) .leaf) .leaf)) (.split 3 189 (.split 2 7 (.split 3 125 (.split 3 107 (.split 2 6 (.split 3 100 (.split 3 96 (.split 3 94 .leaf .leaf) .leaf) .leaf) .leaf) .leaf) .leaf) .leaf) .leaf)))
private theorem crrllllrrrrl : Excluded brrllllrrrrl := fun _ h => reject trrllllrrrrl (by decide +kernel) h
private def brrllllrrrrr : Box := right brrllllrrrr 2 9
private def trrllllrrrrr : Tree := (.split 3 93 (.split 2 21 (.split 3 61 (.split 2 13 (.split 3 52 .leaf (.split 2 11 (.split 3 56 .leaf (.split 3 58 .leaf (.split 2 10 .leaf .leaf))) (.split 3 56 (.split 3 54 .leaf (.split 2 12 .leaf .leaf)) .leaf))) (.split 3 52 (.split 2 16 (.split 3 48 .leaf (.split 3 50 .leaf (.split 2 14 .leaf (.split 2 15 .leaf (.split 3 51 .leaf .leaf))))) (.split 3 48 (.split 2 18 .leaf .leaf) (.split 2 18 (.split 3 50 (.split 3 49 .leaf .leaf) .leaf) (.split 3 50 (.split 2 19 (.split 3 49 .leaf .leaf) .leaf) .leaf)))) (.split 2 16 (.split 3 56 (.split 2 14 (.split 3 54 (.split 3 53 .leaf .leaf) .leaf) .leaf) .leaf) .leaf))) (.split 2 13 (.split 3 74 (.split 2 11 (.split 3 67 (.split 3 64 (.split 2 10 .leaf .leaf) .leaf) .leaf) .leaf) .leaf) .leaf)) (.split 3 61 (.split 2 45 (.split 3 52 (.split 2 29 (.split 3 48 (.split 2 25 (.split 3 46 .leaf (.split 2 23 (.split 3 47 .leaf .leaf) (.split 3 47 (.split 2 24 .leaf .leaf) .leaf))) (.split 3 46 .leaf .leaf)) .leaf) (.split 3 48 (.split 2 36 .leaf .leaf) .leaf)) .leaf) .leaf) .leaf)) .leaf)
private theorem crrllllrrrrr : Excluded brrllllrrrrr := fun _ h => reject trrllllrrrrr (by decide +kernel) h
private theorem crrllllrrrr : Excluded brrllllrrrr := bisect brrllllrrrr 2 9 crrllllrrrrl crrllllrrrrr
private theorem crrllllrrr : Excluded brrllllrrr := bisect brrllllrrr 0 4 crrllllrrrl crrllllrrrr
private theorem crrllllrr : Excluded brrllllrr := bisect brrllllrr 3 45 crrllllrrl crrllllrrr
private theorem crrllllr : Excluded brrllllr := bisect brrllllr 3 21 crrllllrl crrllllrr
private theorem crrllll : Excluded brrllll := bisect brrllll 2 3 crrlllll crrllllr
private def brrlllr : Box := right brrlll 0 5
private def trrlllr : Tree := .leaf
private theorem crrlllr : Excluded brrlllr := fun _ h => reject trrlllr (by decide +kernel) h
private theorem crrlll : Excluded brrlll := bisect brrlll 0 5 crrllll crrlllr
private def brrllr : Box := right brrll 1 1
private def trrllr : Tree := .leaf
private theorem crrllr : Excluded brrllr := fun _ h => reject trrllr (by decide +kernel) h
private theorem crrll : Excluded brrll := bisect brrll 1 1 crrlll crrllr
private def brrlr : Box := right brrl 0 9
private def trrlr : Tree := .leaf
private theorem crrlr : Excluded brrlr := fun _ h => reject trrlr (by decide +kernel) h
private theorem crrl : Excluded brrl := bisect brrl 0 9 crrll crrlr
private def brrr : Box := right brr 1 3
private def trrr : Tree := .leaf
private theorem crrr : Excluded brrr := fun _ h => reject trrr (by decide +kernel) h
private theorem crr : Excluded brr := bisect brr 1 3 crrl crrr
private theorem cr : Excluded br := bisect br 3 9 crl crr
theorem domain_excluded : Excluded domain := bisect domain 0 3 cl cr
end OMA.Moving245212

/- Even integers supported on 2, 3, and one arbitrary larger prime. -/
namespace OMA.Moving245212
open OMA.Smooth245212 Finset
open scoped ArithmeticFunction.sigma

theorem mixed_three {a b c q : ℕ} (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (hq : Nat.Prime q) (large : 3<q) :
    OeisA245212.a (2^a*3^b*q^c) ≠ (σ 1 (2^a*3^b*q^c):ℤ) := by
  let e : I → ℕ := ![a,b,c,q]
  let u : Fin 3 → ℕ := fun i => e i.castSucc
  have hp (i : Fin 3) : Nat.Prime (primes e i) := by
    fin_cases i <;> simp [primes,e,hq,Nat.prime_two,Nat.prime_three]
  have hinj : Function.Injective (primes e) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [primes,e]
    omega
  have he : total (primes e) u = 2^a*3^b*q^c := by
    simp [total,Fin.prod_univ_three,primes,u,e,mul_assoc]
  intro eq
  apply domain_excluded e _ hq
  · exact normalized_of_eq _ hp hinj _ (he ▸ eq)
  · intro i
    fin_cases i <;> simp [domain,e,Band.Contains] <;> omega

end OMA.Moving245212

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

/- The divisor score strictly increases in one prime exponent as soon as
one other prime exponent is sufficiently large. -/
namespace OMA.CapOrder245212
open Finset OMA.Smooth245212 OMA.Abundance245212

private theorem geom (p : ℕ) (hp : 1<p) (e : ℕ) :
    (∑ i∈range (e+1),p^i)<2*p^e := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [sum_range_succ _ (e+1),pow_succ]
    have := Nat.mul_le_mul_left (p^e) (show 2≤p from hp)
    omega

theorem y_short {q : ℕ} (hq : Nat.Prime q) (e : ℕ) :
    Y q (some e)*((e:ℚ)+1)<2 := by
  have h := y_factor hq e
  have l : (ArithmeticFunction.sigma 1 (q^e):ℚ)<2*(q:ℚ)^e := by
    exact_mod_cast (show ArithmeticFunction.sigma 1 (q^e)<2*q^e by
      rw [ArithmeticFunction.sigma_one_apply_prime_pow hq]; exact geom q hq.one_lt e)
  apply lt_of_mul_lt_mul_right (a:= (q:ℚ)^e)
  · linarith only [h,l]
  · positivity

private theorem x_one {q : ℕ} (hq : 1<q) (e : ℕ) : 1≤X q (some e) := by
  have q1 : (1:ℚ)<q := by exact_mod_cast hq
  exact le_add_of_nonneg_right (div_nonneg (sub_nonneg.mpr (y_one hq _)) (by linarith))

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def otherFactors (f : ι → ℚ) (i : ι) : ℚ := ∏ j∈univ.erase i,f j
private theorem update_value (p e : ι → ℕ) (i : ι) (t : ℕ) :
    normalized p (Function.update e i t) =
      otherFactors (fun j => X (p j) (some (e j))) i*X (p i) (some t) +
      otherFactors (fun j => Y (p j) (some (e j))) i*Y (p i) (some t) := by
  have prod_update (F : ι → ℕ → ℚ) :
      (∏ j,F j (Function.update e i t j))=otherFactors (fun j => F j (e j)) i * F i t := by
    rw [←prod_erase_mul _ _ (mem_univ i),Function.update_self]
    congr 1
    exact prod_congr rfl fun j hj => by rw [Function.update_of_ne (mem_erase.mp hj).1]
  exact congrArg₂ (·+·) (prod_update (fun j v => X (p j) (some v)))
    (prod_update (fun j v => Y (p j) (some v)))

theorem upward (p : ι → ℕ) (hp : ∀ i,Nat.Prime (p i)) (e : ι → ℕ)
    {i j : ι} (ij : j≠i) (high : 2*p i≤e j) {t : ℕ} (lt : e i<t) :
    normalized p e<normalized p (Function.update e i t) := by
  let xx := otherFactors (fun j => X (p j) (some (e j))) i
  let yy := otherFactors (fun j => Y (p j) (some (e j))) i
  have hj : j∈(univ:Finset ι).erase i := mem_erase.mpr ⟨ij,mem_univ j⟩
  have yl : yy≤Y (p j) (some (e j)) := by
    dsimp [yy,otherFactors]
    rw [←prod_erase_mul _ _ hj]
    exact mul_le_of_le_one_left (y_nonneg (hp j).one_lt _)
      (prod_le_one (fun h _ => y_nonneg (hp h).one_lt _) (fun h _ => y_one (hp h).one_lt _))
  have xl : 1≤xx := one_le_prod (fun h _ => x_one (hp h).one_lt _)
  have yr := y_short (hp j) (e j)
  have yp := y_nonneg (hp j).one_lt (some (e j))
  have pp : (1:ℚ)<p i := by exact_mod_cast (hp i).one_lt
  have ht : (2:ℚ)*p i≤e j := by exact_mod_cast high
  have cap : yy*((p i:ℚ)-1)<xx := by
    have bound := mul_le_mul_of_nonneg_right yl (show 0≤(p i:ℚ)-1 by linarith)
    have dual := mul_nonneg yp (show 0≤(e j:ℚ)+1-2*((p i:ℚ)-1) by linarith only [ht])
    linarith only [yr,bound,dual,xl]
  have dec := y_strict (hp i).one_lt lt
  have old : normalized p e=xx*X (p i) (some (e i))+yy*Y (p i) (some (e i)) := by
    simpa [xx,yy] using update_value p e i (e i)
  rw [old,update_value]
  change xx*X _ _+yy*Y _ _ < xx*X _ _+yy*Y _ _
  unfold X
  have positive := mul_pos (sub_pos.mpr cap) (sub_pos.mpr dec)
  apply sub_pos.mp
  have difference (a b : ℚ) :
      (xx*(1+(1-b)/((p i:ℚ)-1))+yy*b) - (xx*(1+(1-a)/((p i:ℚ)-1))+yy*a) =
      ((xx-yy*((p i:ℚ)-1))*(a-b))/((p i:ℚ)-1) := by
    field_simp [sub_ne_zero.mpr pp.ne']; ring
  rw [difference]
  exact div_pos positive (by linarith)

theorem nondecrease (p : ι → ℕ) (hp : ∀ i,Nat.Prime (p i)) {e f : ι → ℕ}
    (ef : e≤f) (witness : ∀ i,e i<f i → ∃ j,j≠i ∧ 2*p i≤e j) :
    normalized p e≤normalized p f := by
  let mix (s : Finset ι) (i : ι) := if i∈s then f i else e i
  have h (s : Finset ι) : normalized p e≤normalized p (mix s) := by
    induction s using Finset.induction_on with
    | empty => simp [mix]
    | @insert i s his ih =>
      have update : mix (insert i s)=Function.update (mix s) i (f i) := by
        funext j
        by_cases ji : j=i <;> simp [mix,ji]
      rw [update]
      have old : mix s i=e i := by simp [mix,his]
      rcases (ef i).eq_or_lt with same|lt
      · simpa [←same,←old] using ih
      · obtain ⟨j,ij,high⟩ := witness i lt
        have hj : e j ≤ mix s j := by by_cases js : j∈s <;> simp [mix,js,ef _]
        exact ih.trans (upward p hp (mix s) ij (high.trans hj) (old ▸ lt)).le
  simpa [mix] using h univ

theorem strict_of_changes (p : ι → ℕ) (hp : ∀ i,Nat.Prime (p i)) {e f : ι → ℕ}
    (ef : e≤f) {i : ι} (lt : e i<f i) (witness : ∀ i,e i<f i → ∃ j,j≠i ∧ 2*p i≤e j) :
    normalized p e<normalized p f := by
  let g := Function.update e i (f i)
  have eg (j : ι) : e j≤g j := by by_cases ji : j=i <;> simp [g,ji,ef _]
  have gf : g≤f := by intro j; by_cases ji : j=i <;> simp [g,ji,ef _]
  obtain ⟨j,ij,high⟩ := witness i lt
  refine (upward p hp e ij high lt).trans_le (nondecrease p hp (e:=g) gf ?_)
  intro l hl
  obtain ⟨r,rl,hr⟩ := witness l ((eg l).trans_lt hl)
  exact ⟨r,rl,hr.trans (eg r)⟩

end OMA.CapOrder245212

/- Finitely many non-dyadic A245212 solutions on any fixed set of primes.
Truncate each exponent at twice the largest prime. The solutions of each
truncated pattern form an antichain, which is finite by Dickson's lemma. -/
namespace OMA.FixedPrimes245212
open Finset OMA.Smooth245212 OMA.Abundance245212 OMA.CapOrder245212
open scoped ArithmeticFunction.sigma

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def Exception (n : ℕ) : Prop :=
  OeisA245212.a n = (σ 1 n:ℤ) ∧ ¬∃ u : ℕ, n=2^u

private theorem axis (p : ι → ℕ) (hp : ∀ i,Nat.Prime (p i)) (hinj : Function.Injective p)
    {e f : ι → ℕ} (i : ι) (other : ∀ j,j≠i → e j=f j)
    (he : Exception (total p e)) (hf : Exception (total p f)) : e i=f i := by
  let m := ∏ j∈univ.erase i,(p j)^(e j)
  have em : total p e=m*(p i)^(e i) := (prod_erase_mul _ _ (mem_univ i)).symm
  have fm : total p f=m*(p i)^(f i) := by
    rw [total,←prod_erase_mul _ _ (mem_univ i)]
    congr 1
    exact prod_congr rfl fun j hj => by rw [other j (mem_erase.mp hj).1]
  have hm : m≠0 := prod_ne_zero_iff.mpr (fun j _ => pow_ne_zero _ (hp j).ne_zero)
  have cp : (p i).Coprime m := Nat.Coprime.prod_right (fun j hj =>
    ((Nat.coprime_primes (hp i) (hp j)).mpr (fun h => (mem_erase.mp hj).1 (hinj h).symm)).pow_right _)
  rcases unique_exponent hm (hp i) ((hp i).coprime_iff_not_dvd.mp cp)
      (em ▸ he.1) (fm ▸ hf.1) with yes|⟨p2,m1⟩
  · exact yes
  · exact (he.2 ⟨e i,by simpa [m1,p2] using em⟩).elim

theorem finite_vectors (p : ι → ℕ) (hp : ∀ i,Nat.Prime (p i)) (hinj : Function.Injective p) :
    {e : ι → ℕ | Exception (total p e)}.Finite := by
  classical
  let H := 2*(∑ i,p i)
  let cap (e : ι → ℕ) (i : ι) : Fin (H+1) := ⟨min H (e i),by omega⟩
  apply Set.Finite.of_finite_fibers cap (Set.toFinite _)
  intro pat _
  apply WellQuasiOrderedLE.finite_of_isAntichain
  intro e he f hf ne ef
  have hE : Exception (total p e) := he.1
  have hF : Exception (total p f) := hf.1
  have capped : cap e=cap f := he.2.trans hf.2.symm
  have bound (i : ι) : 2*p i≤H := Nat.mul_le_mul_left 2
    (single_le_sum (f:=p) (fun _ _ => Nat.zero_le _) (mem_univ i))
  have high (i : ι) (lt : e i<f i) : H≤e i := by
    have hh := congrArg Fin.val (congrFun capped i)
    change min H (e i)=min H (f i) at hh
    omega
  obtain ⟨i,lt⟩ : ∃ i,e i<f i := by
    by_contra! h; exact ne (funext fun j => Nat.le_antisymm (ef j) (h j))
  by_cases only : ∀ j,j≠i → e j=f j
  · exact lt.ne (axis p hp hinj i only hE hF)
  · push Not at only
    obtain ⟨j,ji,ej⟩ := only
    have lj := (ef j).lt_of_ne ej
    have rise := strict_of_changes p hp ef lt (fun l _ => by
      by_cases li : l=i
      · exact ⟨j,li ▸ ji,(bound l).trans (high j lj)⟩
      · exact ⟨i,Ne.symm li,(bound l).trans (high i lt)⟩)
    rw [normalized_of_eq p hp hinj _ hE.1,normalized_of_eq p hp hinj _ hF.1] at rise
    exact rise.false

theorem finite (P : Finset ℕ) :
    {n : ℕ | 0<n ∧ n.primeFactors⊆P ∧ Exception n}.Finite := by
  classical
  let S := P.filter Nat.Prime
  let p (i : S) := i.val
  have hp (i : S) : Nat.Prime (p i) := (mem_filter.mp i.property).2
  have h := (finite_vectors p hp Subtype.val_injective).image (total p)
  refine h.subset ?_
  intro n hn
  let e (i : S) := n.factorization i.val
  have prod : total p e=n := by
    unfold total
    change (∏ i:S,i.val^(n.factorization i.val))=n
    rw [Finset.prod_coe_sort S (fun q => q^n.factorization q)]
    apply Eq.symm
    refine (Nat.prod_primeFactors_pow_factorization hn.1.ne').trans (prod_subset ?_ ?_)
    · intro q hq; exact mem_filter.mpr ⟨hn.2.1 hq,Nat.prime_of_mem_primeFactors hq⟩
    · intro q hq hnq
      have h0 : n.factorization q=0 := Finsupp.notMem_support_iff.mp hnq
      simp [h0]
  exact ⟨e,show Exception (total p e) from prod.symm ▸ hn.2.2,prod⟩

end OMA.FixedPrimes245212

/- The denominator argument for truncating the Egyptian-fraction equation
for the odd part in A245212.  All sums here are over positive denominators. -/
namespace OMA.DivisorEnvelope245212
open Finset

private lemma div_cast {m d : ℕ} (hd : d ∈ m.divisors) :
    ((m/d : ℕ) : ℚ) = (m:ℚ)/d := by
  exact Nat.cast_div (Nat.mem_divisors.mp hd).1 (by
    exact_mod_cast (Nat.pos_of_mem_divisors hd).ne')

/-- Convert a weighted equation over divisor complements into a positive
Egyptian-fraction identity, omitting the known first denominator. -/
theorem egyptian {m : ℕ} (hm : 0 < m) (c : ℚ)
    (balance : ((m:ℚ)*m.divisors.card - ∑ d ∈ m.divisors, (d:ℚ)) =
      c*((∑ d ∈ m.divisors, (d:ℚ)*d.divisors.card)-(m:ℚ)*m.divisors.card)) :
    (m.divisors.card:ℚ)-1 =
      ∑ d ∈ m.divisors.erase 1, (c*((m/d).divisors.card:ℚ)+1)/d := by
  let w (d : ℕ) := (d:ℚ)*(c*d.divisors.card+1)
  have comp := Nat.sum_div_divisors m w
  have id' : ∑ d ∈ m.divisors, (c*((m/d).divisors.card:ℚ)+1)/d =
      (∑ d ∈ m.divisors, w d)/m := by
    rw [←comp, Finset.sum_div]
    refine sum_congr rfl fun d hd => ?_
    dsimp [w]
    rw [div_cast hd]
    field_simp
  have one := Nat.one_mem_divisors.mpr hm.ne'
  have erase := Finset.sum_erase_add _ (fun d : ℕ => (c*((m/d).divisors.card:ℚ)+1)/d) one
  simp only [Nat.div_one,Nat.cast_one,div_one] at erase
  dsimp [w] at id'
  simp_rw [mul_add,mul_one,mul_left_comm (_:ℚ) c] at id'
  rw [sum_add_distrib,←mul_sum] at id'
  have id'' := (eq_div_iff (by exact_mod_cast hm.ne' : (m:ℚ)≠0)).1 id'
  rw [←erase] at id''
  apply (mul_right_cancel₀ (by exact_mod_cast hm.ne' : (m:ℚ) ≠ 0))
  linear_combination balance - id''

/-- The common denominator itself, not its square, controls the strict gap
between an integer and a partial divisor-reciprocal sum. -/
theorem gap {b t : ℕ} (hb : 0<b) (s : Finset ℕ) (u : ℕ → ℕ)
    (den : ∀ d ∈ s, d∣b) (pos : ∀ d ∈ s, 0<d)
    (lt : (∑ d ∈ s, (u d : ℚ)/d) < t) :
    1/(b:ℚ) ≤ t-∑ d ∈ s, (u d : ℚ)/d := by
  let v := ∑ d ∈ s, u d*(b/d)
  have id' : ((∑ d ∈ s, (u d:ℚ)/d)*(b:ℚ)) = (v:ℚ) := by
    dsimp [v]
    push_cast
    rw [sum_mul]
    refine sum_congr rfl fun d hd => ?_
    rw [Nat.cast_div (den d hd) (by exact_mod_cast (pos d hd).ne')]
    ring
  have bl : (0:ℚ)<b := by exact_mod_cast hb
  have h := mul_lt_mul_of_pos_right lt bl
  rw [id'] at h
  have hn : v < t*b := by exact_mod_cast h
  have step : (v:ℚ)+1 ≤ (t:ℚ)*b := by exact_mod_cast hn
  apply (div_le_iff₀ bl).2
  rw [sub_mul,id']
  linarith

/-- An integer Egyptian-fraction target and a common positive perturbation
give an explicit lower bound on the tails left by a divisor cutoff. -/
theorem truncated {s : Finset ℕ} (nonempty : s.Nonempty) {u : ℕ → ℕ}
    {t a b P y : ℕ} (hb : 0<b) (hp : 0<P)
    (count : s.card≤t) (hpos : ∀ d∈s, 0<d)
    (wu : ∀ d∈s, 0<u d ∧ u d≤t) (tail : ∀ d∈s, ¬d∣b → P≤d)
    {δ : ℚ} (hδ : 0<δ)
    (target : (y:ℚ) = ∑ d∈s, (((a:ℚ)+δ)*u d+1)/d) :
    1/(b:ℚ) ≤ t*(δ*t+(((a:ℚ)+δ)*t+1)/P) := by
  classical
  let F := s.filter (· ∣ b)
  let v (d : ℕ) : ℚ := if d∣b then ((a*u d+1:ℕ):ℚ)/d else 0
  let w (d : ℕ) : ℚ := (((a:ℚ)+δ)*u d+1)/d
  have cut : ∑ d∈s, v d = ∑ d∈F, ((a*u d+1:ℕ):ℚ)/d := by
    simp [v,F,sum_filter]
  have diff (d : ℕ) (hd : d∈s) :
      0<w d-v d ∧ w d-v d≤δ*t+(((a:ℚ)+δ)*t+1)/P := by
    have dp : (0:ℚ)<d := by exact_mod_cast hpos d hd
    have one : (1:ℚ)≤d := by exact_mod_cast hpos d hd
    have up : (0:ℚ)<u d := by exact_mod_cast (wu d hd).1
    have ut : (u d:ℚ)≤t := by exact_mod_cast (wu d hd).2
    have pp : (0:ℚ)<P := by exact_mod_cast hp
    dsimp [w,v]
    by_cases dd : d∣b
    · rw [if_pos dd]
      push_cast
      rw [←sub_div,show ((a:ℚ)+δ)*u d+1-(a*u d+1)=δ*u d by ring]
      constructor
      · positivity
      · calc
          _ ≤ δ*u d := div_le_self (by positivity) one
          _ ≤ δ*t := by gcongr
          _ ≤ _ := le_add_of_nonneg_right (by positivity)
    · rw [if_neg dd,sub_zero]
      constructor
      · positivity
      · have pd : (P:ℚ)≤d := by exact_mod_cast tail d hd dd
        calc
          _ ≤ (((a:ℚ)+δ)*t+1)/P := by gcongr
          _ ≤ _ := le_add_of_nonneg_left (by positivity)
  have strict : (∑ d∈F, ((a*u d+1:ℕ):ℚ)/d) < y := by
    rw [←cut,target]
    exact sum_lt_sum_of_nonempty nonempty (fun d hd => sub_pos.mp (diff d hd).1)
  have lower := gap hb F (fun d => a*u d+1)
    (fun d hd => (mem_filter.mp hd).2)
    (fun d hd => hpos d (mem_filter.mp hd).1) strict
  rw [←cut,target,←sum_sub_distrib] at lower
  calc
    _ ≤ ∑ d∈s, (w d-v d) := lower
    _ ≤ ∑ _d∈s, (δ*t+(((a:ℚ)+δ)*t+1)/P) := sum_le_sum fun d hd => (diff d hd).2
    _ ≤ _ := by simp only [sum_const,nsmul_eq_mul]; gcongr

/-- Finite bootstrap: if at each stage either an integer is already
bounded or the next prime base is bounded, the cumulative height exponent
is the product of the local divisor counts. -/
theorem bootstrap {r B H : ℕ} {p e : ℕ → ℕ} (hH : 1≤H)
    (step : ∀ j<r,
      B ≤ H*(∏ i ∈ range j, (p i)^(e i)) ∨
      p j ≤ H*(∏ i ∈ range j, (p i)^(e i)))
    (last : B ≤ H*(∏ i ∈ range r, (p i)^(e i))) :
    B ≤ H^(∏ i ∈ range r, (e i+1)) := by
  let m (j : ℕ) := ∏ i ∈ range j, (p i)^(e i)
  let t (j : ℕ) := ∏ i ∈ range j, (e i+1)
  have grow (j : ℕ) : H^(t j) ≤ H^(t (j+1)) := by
    apply Nat.pow_le_pow_right hH
    simp only [t,prod_range_succ]; exact Nat.le_mul_of_pos_right _ (by omega)
  have aux (j : ℕ) (hj : j≤r) : B≤H^(t j) ∨ H*m j ≤ H^(t j) := by
    induction j with
    | zero => exact Or.inr (by simp [m,t])
    | succ j ih =>
      rcases ih (by omega) with done|bound
      · exact Or.inl (done.trans (grow j))
      rcases step j (by omega) with done|next
      · exact Or.inl ((done.trans bound).trans (grow j))
      right
      have hp : p j ≤ H*m j := next
      calc
        H*m (j+1) = H*m j*(p j)^(e j) := by simp [m,prod_range_succ,mul_assoc]
        _ ≤ (H*m j)^(e j+1) := by rw [pow_succ']; gcongr
        _ ≤ (H^(t j))^(e j+1) := Nat.pow_le_pow_left bound _
        _ = H^(t (j+1)) := by rw [←pow_mul]; simp [t,prod_range_succ]
  rcases aux r le_rfl with h|h
  · exact h
  · exact last.trans h

end OMA.DivisorEnvelope245212
