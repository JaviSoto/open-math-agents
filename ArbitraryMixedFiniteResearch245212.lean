import FormalConjectures.OEIS.«245212»

import Mathlib


/-! Uniform one-sided rational separation of normalized weighted divisor sums, at every fixed rank -/

section

/- A uniform one-sided integer gap for any number of factors of the form
g*z+1. The multiplier depends on the coefficients and the number of factors,
but not on the positive variables z or the numerator U. -/
namespace OMA.PositiveProductGap245212
open Finset
variable {ι : Type*} [DecidableEq ι]

def cost : ℕ → ℕ → ℕ
  | 0,_ => 1
  | n+1,A => 2*(A+1)*cost n (2*(A+1)^2)

private theorem cost_pos (n A : ℕ) : 0<cost n A := by
  induction n generalizing A with
  | zero => simp [cost]
  | succ n ih => exact Nat.mul_pos (by positivity) (ih _)

private theorem error {s : Finset ι} (g z : ι→ℕ) (m : ℕ)
    (lower : ∀i∈s, m≤z i) (positive : ∀i∈s, 0<z i) :
    let P:=∏i∈s,z i
    let Q:=∏i∈s,(g i*z i+1)
    let c:=∏i∈s,g i
    let A:=∏i∈s,(g i+1)
    c*P ≤ Q ∧ Q ≤ A*P ∧ m*Q ≤ m*(c*P)+A*P := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have lo:=lower i (mem_insert_self ..)
    have po:=positive i (mem_insert_self ..)
    obtain ⟨lb,ub,err⟩:=ih (fun j hj=>lower j (mem_insert_of_mem hj))
      (fun j hj=>positive j (mem_insert_of_mem hj))
    simp only [prod_insert hi]
    refine ⟨?_,?_,?_⟩
    · have h:=Nat.mul_le_mul (Nat.le_succ (g i*z i)) lb
      simpa only [mul_comm,mul_assoc,mul_left_comm] using h
    · have h:=Nat.mul_le_mul (show g i*z i+1≤(g i+1)*z i by nlinarith only [po]) ub
      simpa only [mul_comm,mul_assoc,mul_left_comm] using h
    · have h:=Nat.mul_le_mul_left (g i*z i) err
      have small:=Nat.mul_le_mul lo ub
      nlinarith only [h,small]

theorem gap (n A : ℕ) (s : Finset ι) (g z : ι→ℕ) {U V R : ℕ}
    (count : s.card=n) (pos : ∀i∈s,0<z i) (rp : 0<R)
    (budget : V*(∏i∈s,(g i+1))≤A)
    (eqn : U*(∏i∈s,z i)=R+V*(∏i∈s,(g i*z i+1))) :
    (∏i∈s,z i)≤cost n A*R := by
  induction n generalizing A s U V with
  | zero =>
    have empty:=Finset.card_eq_zero.mp count
    simpa [empty,cost] using (show 1≤R from rp)
  | succ n ih =>
    by_cases small : ∃i∈s,z i≤2*(A+1)
    · obtain ⟨i,mem,lim⟩:=small
      let t:=s.erase i
      have mult (x : ι→ℕ) : x i*(∏j∈t,x j)=∏j∈s,x j := by
        rw [mul_comm];exact prod_erase_mul _ _ mem
      have zp:=pos i mem
      have cb : (V*(g i*z i+1))*(∏j∈t,(g j+1))≤2*(A+1)^2 := calc
        _ ≤ z i*(V*(∏j∈s,(g j+1))) := by
          rw [←mult (fun j=>g j+1)]
          have h:=Nat.mul_le_mul_left (V*(∏j∈t,(g j+1)))
            (show g i*z i+1≤z i*(g i+1) by nlinarith only [zp])
          simpa only [mul_comm,mul_assoc,mul_left_comm] using h
        _ ≤ 2*(A+1)*(A+1) := Nat.mul_le_mul lim (budget.trans (Nat.le_succ _))
        _ = _ := by ring
      have eq : (U*z i)*(∏j∈t,z j)=R+(V*(g i*z i+1))*(∏j∈t,(g j*z j+1)) := by
        rw [Nat.mul_assoc,Nat.mul_assoc,mult z,mult (fun j=>g j*z j+1)]
        exact eqn
      have smaller:=ih (2*(A+1)^2) t (by dsimp [t];rw [card_erase_of_mem mem,count];omega)
        (fun j hj=>pos j (mem_of_mem_erase hj)) cb eq
      rw [←mult z]
      exact (Nat.mul_le_mul lim smaller).trans_eq (by simp only [cost,Nat.mul_assoc])
    · have lo i (mem:i∈s) : 2*(A+1)≤z i:=by
        have no : ¬z i≤2*(A+1):=fun h=>small ⟨i,mem,h⟩
        omega
      obtain ⟨lb,_,err⟩:=error g z (2*(A+1)) lo pos
      let P:=∏i∈s,z i
      let Q:=∏i∈s,(g i*z i+1)
      let c:=∏i∈s,g i
      let B:=∏i∈s,(g i+1)
      change c*P≤Q at lb
      change 2*(A+1)*Q≤2*(A+1)*(c*P)+B*P at err
      change U*P=R+V*Q at eqn
      have uc : V*c<U := by
        by_contra! rev
        have h:=Nat.mul_le_mul_right P rev
        have l:=Nat.mul_le_mul_left V lb
        nlinarith only [h,l,eqn,rp]
      have h:=Nat.mul_le_mul_right P (Nat.succ_le_of_lt uc)
      have extra:=Nat.mul_le_mul_left V err
      have cap:=Nat.mul_le_mul_right P budget
      change V*B*P≤A*P at cap
      have joined:=Nat.mul_le_mul_left (2*(A+1)) h
      have id:=congrArg (2*(A+1)*·) eqn
      have pr : P≤2*R := by
        by_contra! bad
        have worse:=Nat.mul_lt_mul_of_pos_left bad (Nat.succ_pos A)
        nlinarith only [extra,cap,joined,id,worse,Nat.zero_le P]
      change P≤cost (n+1) A*R
      have big : 2≤cost (n+1) A:=
        calc
          2 ≤ 2*(A+1) := by omega
          _ ≤ _ := Nat.le_mul_of_pos_right _ (cost_pos n _)
      exact pr.trans (Nat.mul_le_mul_right R big)

#print axioms gap
end OMA.PositiveProductGap245212

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

/- Simultaneous integer separation after rounding both odd prime powers.
The coefficient pair (f,g) denotes t=f/g, permitting t=k and t=γ. -/
namespace OMA.TwoOddGlobalGap245212

def defect (f g p q B C : ℤ) :=
  (f+g)*B*C*(p-1)^2*(q-1)^2 -
    p*q*(f*(B*(p-1)-1)*(C*(q-1)-1)+g*(p-1)*(q-1))

def alpha (f g p q C : ℤ) := q*(f*(C*(q-1)-1)-g*(p-1)*(q-1))
def beta (f g p q B : ℤ) := p*(f*(B*(p-1)-1)-g*(p-1)*(q-1))

/-- The simultaneous finite-tail formula is a polynomial identity. The
four moment identities input here are the ordinary geometric sums. -/
theorem expansion (f g p q B C P Q W V S T : ℤ)
    (pw : (p-1)^2*W=p*(B*(p-1)-1)*P+1)
    (qw : (q-1)^2*V=q*(C*(q-1)-1)*Q+1)
    (ps : (p-1)*S=p*P-1) (qs : (q-1)*T=q*Q-1) :
    (p-1)^2*(q-1)^2*(f*W*V+g*S*T-(f+g)*B*C*P*Q) =
      -defect f g p q B C*P*Q+alpha f g p q C*Q+beta f g p q B*P+f+g*(p-1)*(q-1) := by
  unfold defect alpha beta
  linear_combination f*((q-1)^2*V)*pw+f*(p*(B*(p-1)-1)*P+1)*qw+
    g*(p-1)*(q-1)*((q-1)*T)*ps+g*(p-1)*(q-1)*(p*P-1)*qs

private theorem divides {f g p q B C : ℕ} (hq : q.Prime) (hp : 3≤p) (pq : p<q)
    (zero : defect f g p q B C=0) : q ∣ (f+g)*B*C := by
  let : Fact q.Prime := ⟨hq⟩
  have modq := congrArg (fun z:ℤ => (z:ZMod q)) zero
  unfold defect at modq
  push_cast at modq
  simp only [ZMod.natCast_self] at modq
  have mz : (((f:ZMod q)+g)*B*C)*((p:ZMod q)-1)^2=0 := by linear_combination modq
  have pn : (p:ZMod q)-1≠0 := by
    rw [←Nat.cast_one,←Nat.cast_sub (by omega : 1≤p)]
    exact fun h => Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
      ((ZMod.natCast_eq_zero_iff (p-1) q).mp h)
  have dm := (mul_eq_zero.mp mz).resolve_right (pow_ne_zero _ pn)
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  push_cast; exact dm

/-- A nonpositive finite-balance residual forces a nonzero integer after
both local prime-power factors are replaced by their rational limits. -/
theorem nonzero_of_positive_alpha {p q B C k f g l : ℕ} (hq : q.Prime) (hp : 3≤p) (pq : p<q)
    (hb : 2≤B) (hc : 2≤C) (hk : 2≤k) (small : (p:ℤ)-1<(k:ℤ)*(C-1))
    (gpos : 0<g) (fg : k*g≤f) (frac : f+g=(k+1)*l) (unit : ¬q∣l)
    (actual : alpha f g p q C*(q:ℤ)^(C-1)+beta f g p q B*(p:ℤ)^(B-1)+f+
      g*(p-1)*(q-1)≤defect f g p q B C*(p:ℤ)^(B-1)*(q:ℤ)^(C-1)) :
    defect f g p q B C ≠ 0 := by
  intro zero
  have dv := divides hq hp pq zero
  rw [frac] at dv
  let u : ℤ := p-1
  let v : ℤ := q-1
  have pp' : (0:ℤ)<p := by omega
  have qp' : (0:ℤ)<q := by omega
  have uv : u<v := by dsimp [u,v]; omega
  have up : (2:ℤ)≤u := by dsimp [u]; omega
  have vp : (2:ℤ)≤v := by omega
  have fp : (k:ℤ)*g≤f := by exact_mod_cast fg
  have pp : (0:ℤ)<g := by exact_mod_cast gpos
  have posf : 0<(f:ℤ) := by nlinarith only [fp,mul_pos (by omega : (0:ℤ)<k) pp]
  have kb : (B:ℤ)≤k*(B-1) := by
    nlinarith only [mul_nonneg (by omega : (0:ℤ)≤k-2) (by omega : (0:ℤ)≤B-1), (show (2:ℤ)≤B by exact_mod_cast hb)]
  have kbase : (k:ℤ)≤k*(B-1) := by
    nlinarith only [mul_nonneg (by positivity : (0:ℤ)≤k) (by omega : (0:ℤ)≤B-2)]
  have kc : u<k*(C-1) := small
  have cden : 0<(C:ℤ)*v-1 := by nlinarith only [mul_nonneg (by omega : (0:ℤ)≤C-2) (by omega : 0≤v),vp]
  have bden : 0<(B:ℤ)*u-1 := by nlinarith only [mul_nonneg (by omega : (0:ℤ)≤B-2) (by omega : 0≤u),up]
  have compare (N h z : ℤ) (zd : 1≤z) (den : 0<N*z-1)
      (lim : h<(k:ℤ)*(N-1)) : (g:ℤ)*h*z < f*(N*z-1) := by
    have hm := mul_lt_mul_of_pos_right lim (mul_pos pp (by omega : 0<z))
    have kern := mul_le_mul_of_nonneg_right fp den.le
    nlinarith only [hm,kern,mul_nonneg (mul_nonneg (by positivity : (0:ℤ)≤k) pp.le)
      (by omega : 0≤z-1)]
  have first := compare C u v (by omega) cden kc
  have al : 0<alpha f g p q C := by
    unfold alpha
    exact mul_pos (by positivity) (sub_pos.mpr first)
  rw [zero,zero_mul,zero_mul] at actual
  have bp : beta f g p q B<0 := by
    by_contra! ge
    nlinarith only [actual,mul_pos al (by positivity : (0:ℤ)<q^(C-1)),
      mul_nonneg ge (by positivity : (0:ℤ)≤p^(B-1)),posf,
      mul_nonneg (mul_nonneg pp.le (by omega : 0≤u)) (by omega : 0≤v)]
  have bound : k*(B-1)<v := by
    have neg : (f:ℤ)*(B*u-1)<g*u*v :=
      sub_neg.mp (neg_of_mul_neg_right bp (by positivity : (0:ℤ)≤p))
    by_contra! bad
    have m := mul_le_mul_of_nonneg_right bad (mul_nonneg pp.le (by omega : 0≤u))
    have kern := mul_le_mul_of_nonneg_right fp bden.le
    nlinarith only [neg,m,kern,mul_nonneg (mul_nonneg (by positivity : (0:ℤ)≤k) pp.le) (by omega : 0≤u-1)]
  have qB : B<q := by dsimp [v] at bound; omega
  have qK : k+1<q := by dsimp [v] at bound; omega
  have divC : q∣C := by
    rcases hq.dvd_mul.mp dv with previous | done
    · rcases hq.dvd_mul.mp previous with pre | bBad
      · rcases hq.dvd_mul.mp pre with kBad | lBad
        · exact False.elim (Nat.not_dvd_of_pos_of_lt (by omega) qK kBad)
        · exact False.elim (unit lBad)
      · exact False.elim (Nat.not_dvd_of_pos_of_lt (by omega) qB bBad)
    · exact done
  have qC := Nat.le_of_dvd (by omega : 0<C) divC
  have kC : 2*u < (k:ℤ)*(C-1) := by
    dsimp [u,v] at uv ⊢
    nlinarith only [mul_nonneg (by omega : (0:ℤ)≤k-2) (by omega : (0:ℤ)≤C-1),
      (show (q:ℤ)≤C by exact_mod_cast qC),uv]
  have stronger := compare C (2*u) v (by omega) cden kC
  have asum : 0<alpha f g p q C + beta f g p q B := by
    change 0<(q:ℤ)*(f*(C*v-1)-g*u*v)+p*(f*(B*u-1)-g*u*v)
    nlinarith only [mul_pos (by positivity : (0:ℤ)<q) (sub_pos.mpr stronger),
      mul_nonneg (by omega : (0:ℤ)≤q-p) (mul_nonneg (mul_nonneg pp.le (by omega : 0≤u)) (by omega : 0≤v)),
      mul_pos (mul_pos (by positivity : (0:ℤ)<p) posf) bden]
  have sizes : (p:ℤ)^(B-1)≤(q:ℤ)^(C-1) := calc
    _ ≤ (q:ℤ)^(B-1) := pow_le_pow_left₀ (by positivity) (by exact_mod_cast pq.le) _
    _ ≤ _ := pow_le_pow_right₀ (by omega : (1:ℤ)≤q) (by omega)
  nlinarith only [actual,mul_pos asum (by positivity : (0:ℤ)<p^(B-1)),
    mul_nonneg al.le (sub_nonneg.mpr sizes),posf,
    mul_nonneg (mul_nonneg pp.le (by omega : 0≤u)) (by omega : 0≤v)]

/-- The coarser range used in the original two-prime finiteness theorem. -/
theorem nonzero {p q B C k f g l : ℕ} (hq : q.Prime) (hp : 3≤p) (pq : p<q)
    (hb : 2≤B) (hc : 16≤C) (hk : 2≤k) (small : p≤5*(k+1))
    (gpos : 0<g) (fg : k*g≤f) (frac : f+g=(k+1)*l) (unit : ¬q∣l)
    (actual : alpha f g p q C*(q:ℤ)^(C-1)+beta f g p q B*(p:ℤ)^(B-1)+f+
      g*(p-1)*(q-1)≤defect f g p q B C*(p:ℤ)^(B-1)*(q:ℤ)^(C-1)) :
    defect f g p q B C ≠ 0 := by
  apply nonzero_of_positive_alpha hq hp pq hb (by omega) hk _ gpos fg frac unit actual
  have hs : (p:ℤ)≤5*((k:ℤ)+1) := by exact_mod_cast small
  nlinarith only [hs,mul_nonneg (by positivity : (0:ℤ)≤k) (by omega : (0:ℤ)≤C-16),
    (show (2:ℤ)≤k by exact_mod_cast hk)]

end OMA.TwoOddGlobalGap245212

end

section

/- Local exact divisor identities, taken directly from the formal OEIS
equality; these are the arithmetic inputs of the complementary-exponent bound. -/
namespace OMA.ComplementaryLocal245212
open Finset ArithmeticFunction OMA.Smooth245212
open scoped ArithmeticFunction.sigma

/-- Ordinary and weighted finite geometric sums, in a form that keeps
the two small residuals exactly. -/
theorem moments {p : ℕ} (hp : p.Prime) (e : ℕ) :
    ((p:ℤ)-1)*(σ 1 (p^e):ℤ)=p*(p:ℤ)^e-1 ∧
    ((p:ℤ)-1)^2*(W (p^e):ℤ)=p*((e+1)*(p-1)-1)*(p:ℤ)^e+1 := by
  have g : ((p:ℤ)-1)*(σ 1 (p^e):ℤ)=p*(p:ℤ)^e-1 := by
    rw [sigma_one_apply_prime_pow hp]
    push_cast
    rw [mul_comm ((p:ℤ)-1),geom_sum_mul,pow_succ,mul_comm]
  refine ⟨g,?_⟩
  have w := OMA.PrimePowerDiv245212.weighted hp e
  zify [Nat.cast_sub hp.pos] at w
  linear_combination ((p:ℤ)-1)*w-g

theorem bounds {p : ℕ} (hp : p.Prime) (odd : 3≤p) (e : ℕ) :
    2*(σ 1 (p^e))≤3*p^e ∧ 2*W (p^e)≤3*(e+1)*p^e ∧
    (e+1)*p^e≤W (p^e) ∧ σ 1 (p^e)≤W (p^e) := by
  have g := (moments hp e).1
  have ps : ((p:ℤ)-1)*((3:ℤ)*p^e-2*(σ 1 (p^e):ℤ)) =
      ((p:ℤ)-3)*p^e+2 := by linear_combination -2*g
  have sb : 2*(σ 1 (p^e))≤3*p^e := by
    have pp : (0:ℤ)≤p-3 := by omega
    have : 0≤((p:ℤ)-1)*(3*(p:ℤ)^e-2*(σ 1 (p^e):ℤ)) :=
      ps ▸ (by positivity)
    have hh := nonneg_of_mul_nonneg_right this (by omega : (0:ℤ)<p-1)
    exact_mod_cast (sub_nonneg.mp hh)
  have simple : W (p^e) ≤ (e+1)*(σ 1 (p^e)) := by
    rw [w_pow hp,sigma_one_apply_prime_pow hp,mul_sum]
    refine sum_le_sum fun i hi => ?_
    rw [mul_comm (e+1)]
    exact Nat.mul_le_mul_left _ (by have := mem_range.mp hi; omega)
  refine ⟨sb,by nlinarith only [Nat.mul_le_mul_left 2 simple,Nat.mul_le_mul_left (e+1) sb],?_,?_⟩
  · rw [w_pow hp,sum_range_succ]
    nlinarith only [Nat.zero_le (∑ i∈range e,p^i*(i+1))]
  · rw [w_pow hp,sigma_one_apply_prime_pow hp]
    exact sum_le_sum fun i _ => by nlinarith only [Nat.zero_le (p^i*i)]

theorem last {p : ℕ} (hp : p.Prime) (odd : 3≤p) (e : ℕ) :
    W (p^(e+1))=(e+2)*p^(e+1)+W (p^e) ∧
    σ 1 (p^(e+1))=p^(e+1)+σ 1 (p^e) ∧ 2*W (p^e)≤3*(e+1)*p^e := by
  refine ⟨?_,?_,(bounds hp odd e).2.1⟩
  · rw [w_pow hp,w_pow hp,sum_range_succ]; ring
  · rw [sigma_one_apply_prime_pow hp,sigma_one_apply_prime_pow hp,sum_range_succ,add_comm]

private theorem binary (k : ℕ) :
    (σ 1 (2^k):ℤ)=(2:ℤ)^(k+1)-1 ∧ (W (2^k):ℤ)=1+k*(2:ℤ)^(k+1) := by
  have h := moments Nat.prime_two k
  norm_num at h
  rw [pow_succ]; constructor <;> nlinarith only [h.1,h.2]

/-- Starting at the actual OEIS hypothesis, both odd factors and the power
of two separate with no asymptotic or arithmetic assumptions. -/
theorem physical {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (op : p≠2)
    (oq : q≠2) (pq : p≠q) (a d k : ℕ)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    (1+k*(2:ℤ)^(k+1))*(W (p^a):ℤ)*(W (q^d):ℤ)+
      ((2:ℤ)^(k+1)-1)*(σ 1 (p^a):ℤ)*(σ 1 (q^d):ℤ) =
      (2:ℤ)^(k+1)*(k+1)*(a+1)*(d+1)*p^a*q^d := by
  have tp : (2^k).Coprime (p^a) :=
    (((Nat.coprime_primes Nat.prime_two hp).mpr op.symm).pow_left k).pow_right a
  have tq : (2^k*p^a).Coprime (q^d) :=
    ((((Nat.coprime_primes Nat.prime_two hq).mpr oq.symm).pow_left k).mul_left
      (((Nat.coprime_primes hp hq).mpr pq).pow_left a)).pow_right d
  have pos : 0<p := hp.pos
  have pos' : 0<q := hq.pos
  have b := OMA.Abundance245212.balance (show 2^k*p^a*q^d≠0 by positivity) eqn
  rw [w_mult.map_mul_of_coprime tq,w_mult.map_mul_of_coprime tp,
    isMultiplicative_sigma.map_mul_of_coprime tq,isMultiplicative_sigma.map_mul_of_coprime tp,
    isMultiplicative_sigma.map_mul_of_coprime tq,isMultiplicative_sigma.map_mul_of_coprime tp,
    sigma_zero_apply_prime_pow Nat.prime_two,sigma_zero_apply_prime_pow hp,sigma_zero_apply_prime_pow hq] at b
  zify at b
  rw [(binary k).1,(binary k).2] at b
  rw [pow_succ (2:ℤ) k] at b ⊢
  linear_combination b

/-- The ordinary OEIS equality directly implies both nonzero integer
defects used in the unrestricted rank-two finiteness proof. -/
theorem original_separations {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p)
    (pq : p<q) {a d k : ℕ} (ha : 1≤a) (hd : 15≤d) (hk : 2≤k) (small : p≤5*(k+1))
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    OMA.TwoOddGlobalGap245212.defect k 1 p q (a+1) (d+1)≠0 ∧
    OMA.TwoOddGlobalGap245212.defect (1+k*(2:ℤ)^(k+1)) ((2:ℤ)^(k+1)-1) p q (a+1) (d+1)≠0 := by
  have bal := physical hp hq (by omega) (by omega) pq.ne a d k eqn
  let P : ℤ := (p:ℤ)^a
  let Q : ℤ := (q:ℤ)^d
  let W : ℤ := OMA.Smooth245212.W (p^a)
  let V : ℤ := OMA.Smooth245212.W (q^d)
  let S : ℤ := σ 1 (p^a)
  let T : ℤ := σ 1 (q^d)
  let B : ℤ := (a:ℤ)+1
  let C : ℤ := (d:ℤ)+1
  let G : ℤ := (2:ℤ)^(k+1)-1
  let F : ℤ := 1+k*(2:ℤ)^(k+1)
  have hfg : F+G=(2:ℤ)^(k+1)*(k+1) := by dsimp [F,G];ring
  change F*W*V+G*S*T=(2:ℤ)^(k+1)*(k+1)*B*C*P*Q at bal
  rw [←hfg] at bal
  have w₁ : B*P ≤ W := by dsimp [B,P,W]; exact_mod_cast (bounds hp op a).2.2.1
  have w₂ : C*Q ≤ V := by dsimp [C,Q,V]; exact_mod_cast (bounds hq (by omega) d).2.2.1
  have ww : B*C*P*Q ≤ W*V := by
    have := mul_le_mul w₁ w₂ (by dsimp [C,Q];positivity) (by dsimp [W];positivity)
    nlinarith only [this]
  have gp : 0<G := by
    dsimp [G]; have := one_lt_pow₀ (a:=(2:ℤ)) (by norm_num) (show k+1≠0 by omega); omega
  have fg : F=(k:ℤ)*G+(k+1) := by dsimp [F,G];ring
  have low : (k:ℤ)*W*V+S*T≤((k:ℤ)+1)*B*C*P*Q := by
    have m : G*((k:ℤ)*W*V+S*T-((k:ℤ)+1)*B*C*P*Q)=
        -((k:ℤ)+1)*(W*V-B*C*P*Q) := by
      rw [fg] at bal
      linear_combination bal
    have hh : G*((k:ℤ)*W*V+S*T-((k:ℤ)+1)*B*C*P*Q) ≤ 0 :=
      m ▸ (mul_nonpos_of_nonpos_of_nonneg (by omega) (sub_nonneg.mpr ww))
    exact sub_nonpos.mp (nonpos_of_mul_nonpos_right hh gp)
  have apply_for (f g l : ℕ) (gpos : 0<g) (fg' : k*g≤f) (sum : f+g=(k+1)*l)
      (unit : ¬q∣l) (w : (f:ℤ)*W*V+g*S*T≤(f+g)*B*C*P*Q) :
      OMA.TwoOddGlobalGap245212.defect f g p q B C ≠ 0 := by
    have hi := OMA.TwoOddGlobalGap245212.expansion f g p q B C P Q W V S T
      (moments hp a).2 (moments hq d).2 (moments hp a).1 (moments hq d).1
    have v0 := mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (sq_nonneg ((p:ℤ)-1)) (sq_nonneg ((q:ℤ)-1))) (sub_nonpos.mpr w)
    rw [hi] at v0
    apply OMA.TwoOddGlobalGap245212.nonzero (B:=a+1) (C:=d+1) hq op pq (by omega) (by omega)
      hk small gpos fg' sum unit
    simp only [Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel] 
    dsimp only [B,C,P,Q] at v0
    linarith only [v0]
  refine ⟨apply_for k 1 1 (by decide) (by simp) (by simp)
    (by simpa using hq.not_dvd_one) (by simpa using low),?_⟩
  let z := 2^(k+1)
  have zp : 0<z := by dsimp [z];positivity
  have zcast : (z:ℤ)=(2:ℤ)^(k+1) := by push_cast [z];rfl
  have dvz : ¬q∣z := fun bad => Nat.not_dvd_of_pos_of_lt (by decide : 0<2) (by omega)
    (hq.dvd_of_dvd_pow bad)
  have app := apply_for (1+k*z) (z-1) z (by
    dsimp [z];have := Nat.one_lt_pow (by omega : k+1≠0) (by decide : 1<2);omega)
    (by nlinarith only [Nat.mul_le_mul_left k (Nat.sub_le z 1)])
    (by have h := Nat.sub_add_cancel (by omega : 1≤z); nlinarith only [h])
    dvz (by
      push_cast [Nat.cast_sub zp,zcast]
      exact bal.le)
  simpa [Nat.cast_sub zp,zcast,F,G] using app

end OMA.ComplementaryLocal245212

end

section

/- Quantitative separation below rational targets for products of normalized
weighted divisor sums. The bound does not contain any prime power. -/
namespace OMA.WeightedUpperGap245212
open Nat Finset ArithmeticFunction OMA.Smooth245212
open scoped ArithmeticFunction.sigma
variable {ι : Type*} [DecidableEq ι]

def mass (p e : ℕ) := (e+1)*p^e
def coeff (p e : ℕ) := p*((e+1)*(p-1)-1)
def boundedCost (r V T B : ℕ) :=
  (T^r*(B^2)^r)*OMA.PositiveProductGap245212.cost r (V*(B*(T*B)+1)^r)

theorem local_moment {p : ℕ} (pr : p.Prime) (e : ℕ) :
    (p-1)^2*W (p^e)=coeff p e*p^e+1 := by
  have base : 1≤(e+1)*(p-1):=Nat.mul_pos (Nat.succ_pos _) (Nat.sub_pos_of_lt pr.one_lt)
  unfold coeff
  zify [Nat.cast_sub pr.pos,Nat.cast_sub base]
  exact (OMA.ComplementaryLocal245212.moments pr e).2

theorem bounded {s : Finset ι} (p e : ι→ℕ) (V U R T B : ℕ)
    (pr : ∀i∈s,(p i).Prime) (base : ∀i∈s,p i≤B) (len : ∀i∈s,e i+1≤T) (rp : 0<R)
    (eqn : U*(∏i∈s,mass (p i) (e i))=R+V*(∏i∈s,W ((p i)^(e i)))) :
    (∏i∈s,mass (p i) (e i))≤boundedCost s.card V T B*R := by
  let z i:=p i^e i
  let g i:=coeff (p i) (e i)
  let L:=∏i∈s,(p i-1)^2
  let M:=∏i∈s,(e i+1)
  let P:=∏i∈s,z i
  let Wp:=∏i∈s,W (p i^e i)
  have mass_eq : (∏i∈s,mass (p i) (e i))=M*P:=by simp only [mass,prod_mul_distrib,M,P,z]
  have weights : L*Wp=∏i∈s,(g i*z i+1):=by
    dsimp only [L,Wp]
    rw [←prod_mul_distrib]; exact prod_congr rfl (fun i hi=>local_moment (pr i hi) _)
  have lpos : 0<L:=prod_pos fun i hi=>pow_pos (Nat.sub_pos_of_lt (pr i hi).one_lt) _
  have gb : V*(∏i∈s,(g i+1))≤V*(B*(T*B)+1)^s.card:=by
    apply Nat.mul_le_mul_left
    calc
      _ ≤ ∏_i∈s,(B*(T*B)+1) := by
        apply prod_le_prod'
        intro i hi
        exact Nat.succ_le_succ (Nat.mul_le_mul (base i hi) ((Nat.sub_le _ _).trans
          (Nat.mul_le_mul (len i hi) ((Nat.sub_le _ _).trans (base i hi)))))
      _ = _ := by simp
  have gap : (U*L*M)*P=L*R+V*(∏i∈s,(g i*z i+1)):=by
    rw [←weights]
    rw [mass_eq] at eqn
    change U*(M*P)=R+V*Wp at eqn
    nlinarith only [congrArg (L*·) eqn]
  have res:=OMA.PositiveProductGap245212.gap _ _ s g z rfl
    (fun i hi=>pow_pos (pr i hi).pos _) (Nat.mul_pos lpos rp) gb gap
  have lcap : L≤(B^2)^s.card:=calc
    L ≤ ∏_i∈s,B^2 := prod_le_prod' fun i hi=>Nat.pow_le_pow_left ((Nat.sub_le _ _).trans (base i hi)) _
    _ = _ := by simp
  have mcap : M≤T^s.card:=calc
    M ≤ ∏_i∈s,T := prod_le_prod' len
    _ = _ := by simp
  rw [mass_eq]
  have out:=Nat.mul_le_mul mcap res
  let C:=OMA.PositiveProductGap245212.cost s.card (V*(B*(T*B)+1)^s.card)
  change M*P≤T^s.card*(C*(L*R)) at out
  exact out.trans (by
    have h:=Nat.mul_le_mul_left (T^s.card*C*R) lcap
    simpa only [boundedCost,C,mul_assoc,mul_comm,mul_left_comm] using h)

theorem local_range {p : ℕ} (pr : p.Prime) (e : ℕ) :
    mass p e≤W (p^e) ∧ (p-1)*W (p^e)≤p*mass p e ∧ W (p^e)≤2*mass p e := by
  have identity:=OMA.PrimePowerDiv245212.weighted pr e
  have lower : mass p e≤W (p^e):=by
    rw [w_pow pr];unfold mass
    simpa only [mul_comm] using single_le_sum (f:=fun i=>p^i*(i+1)) (fun i _=>Nat.zero_le _)
      (mem_range.mpr (Nat.lt_succ_self e))
  have upper : (p-1)*W (p^e)≤p*mass p e:=by dsimp [mass];omega
  have nz : 0<p-1:=Nat.sub_pos_of_lt pr.one_lt
  have p2 : p≤(p-1)*2:=by omega
  have h:=upper.trans (Nat.mul_le_mul_right (mass p e) p2)
  exact ⟨lower,upper,Nat.le_of_mul_le_mul_left (by simpa only [mul_assoc] using h) nz⟩

-- The rank-r target gap survives adding one sufficiently large prime.
theorem large_step {U V A T x y p K E R : ℕ}
    (left : U*T=E+V*A) (coarse : A≤T*(2^p))
    (old : T≤K*E) {prime : ℕ} (strong : 2*K*V*2^p≤prime-1)
    (massbound : (prime-1)*y≤prime*x) (pr : 2≤prime)
    (full : U*(T*x)=R+V*(A*y)) : T*x≤(2*K)*R := by
  have den : 0<prime-1:=by omega
  have add:=Nat.sub_add_cancel (show 1≤prime by omega)
  have localDiff : (prime-1)*y≤(prime-1)*x+x:=by nlinarith only [massbound,congrArg (·*x) add]
  have rem:=Nat.mul_le_mul_left (V*A) localDiff
  have e:=congrArg (·*((prime-1)*x)) left
  have f:=congrArg ((prime-1)*·) full
  have gap : (prime-1)*E*x ≤ (prime-1)*R + V*A*x:=by nlinarith only [rem,e,f]
  have h:=Nat.mul_le_mul_left ((prime-1)*x) old
  have b:=Nat.mul_le_mul_left K gap
  have err:=Nat.mul_le_mul_left (2*K*V*x) coarse
  have top:=Nat.mul_le_mul_right (T*x) strong
  have goal : (prime-1)*(T*x)≤(prime-1)*((2*K)*R) := by
    nlinarith only [h,b,err,top]
  exact Nat.le_of_mul_le_mul_left goal den

#print axioms bounded
end OMA.WeightedUpperGap245212

end

section

/- A rational strictly above the normalized weighted moment is separated
from it independently of all the prime bases and prime powers. -/
namespace OMA.WeightedUniformGap245212
open Nat Finset ArithmeticFunction OMA.Smooth245212 OMA.WeightedUpperGap245212
open scoped ArithmeticFunction.sigma
variable {ι : Type*} [DecidableEq ι]

def cutoff (r x K : ℕ) := 2*K*x*2^r+2
def constant : ℕ→ℕ→ℕ
  | 0,_ => 1
  | r+1,x => let K:=constant r x; 2*K+boundedCost (r+1) x x (cutoff r x K)

theorem cost_mono (n : ℕ) : Monotone (OMA.PositiveProductGap245212.cost n) := by
  induction n with
  | zero => intro _ _ _;rfl
  | succ n ih =>
    intro a b le
    dsimp only [OMA.PositiveProductGap245212.cost]
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 (Nat.succ_le_succ le))
      (ih (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (Nat.succ_le_succ le) 2)))

theorem bound (n x : ℕ) (s : Finset ι) (p e : ι→ℕ) {U V R : ℕ}
    (count : s.card=n) (pr : ∀i∈s,(p i).Prime) (len : ∀i∈s,e i+1≤x)
    (vx : V≤x) (rp : 0<R)
    (eqn : U*(∏i∈s,mass (p i) (e i))=R+V*(∏i∈s,W ((p i)^(e i)))) :
    (∏i∈s,mass (p i) (e i))≤constant n x*R := by
  induction n generalizing s R with
  | zero =>
    have empty:=card_eq_zero.mp count
    simpa [empty,constant] using (show 1≤R from rp)
  | succ n ih =>
    let K:=constant n x
    let B:=cutoff n x K
    by_cases low : ∀i∈s,p i≤B
    · have h:=bounded p e V U R x B pr low len rp eqn
      rw [count] at h
      have c : boundedCost (n+1) V x B ≤ boundedCost (n+1) x x B := by
        unfold boundedCost
        exact Nat.mul_le_mul_left _ (cost_mono _ (Nat.mul_le_mul_right _ vx))
      exact h.trans (Nat.mul_le_mul_right R (c.trans (Nat.le_add_left _ _)))
    push Not at low
    obtain ⟨i,mem,high⟩:=low
    let t:=s.erase i
    have card : t.card=n:=by dsimp [t];rw [card_erase_of_mem mem,count];omega
    let M j:=mass (p j) (e j)
    let A j:=W ((p j)^(e j))
    let P:=∏j∈t,M j
    let Q:=∏j∈t,A j
    have combine (f : ι→ℕ) : (∏j∈t,f j)*f i=∏j∈s,f j := prod_erase_mul _ _ mem
    change U*(∏j∈s,M j)=R+V*(∏j∈s,A j) at eqn
    rw [←combine M,←combine A] at eqn
    change U*(P*M i)=R+V*(Q*A i) at eqn
    have loc:=local_range (pr i mem) (e i)
    change M i≤A i ∧ (p i-1)*A i≤p i*M i ∧ _ at loc
    have pv : V*Q<U*P:=by
      by_contra! bad
      have h:=Nat.mul_le_mul bad loc.1
      nlinarith only [h,eqn,rp]
    let E:=U*P-V*Q
    have ep : 0<E:=Nat.sub_pos_of_lt pv
    have prev : U*P=E+V*Q:=(Nat.sub_add_cancel pv.le).symm
    have old : P≤K*E:=ih t card (fun j mj=>pr j (mem_of_mem_erase mj))
      (fun j mj=>len j (mem_of_mem_erase mj)) ep prev
    have coarse : Q≤P*2^n:=calc
      Q ≤ ∏j∈t,(2*M j) := prod_le_prod' fun j hj=>(local_range (pr j (mem_of_mem_erase hj)) (e j)).2.2
      _ = _ := by simp [prod_mul_distrib,card,P,mul_comm]
    have strong : 2*K*V*2^n≤p i-1:=by
      change 2*K*x*2^n+2<p i at high
      have h:=Nat.mul_le_mul_right (2^n) (Nat.mul_le_mul_left (2*K) vx)
      omega
    have lift:=large_step prev coarse old strong loc.2.1 (pr i mem).two_le eqn
    change (∏j∈s,M j)≤_
    rw [←combine M]
    exact lift.trans (Nat.mul_le_mul_right R (Nat.le_add_right _ _))

#print axioms bound
end OMA.WeightedUniformGap245212

end

section

/- A single polynomial controls every cofactor of bounded rank, without
fixing its bases, exponents, or numerator of the rational target. -/
namespace OMA.WeightedGapPolynomial245212
noncomputable section
open Nat Finset ArithmeticFunction Polynomial OMA.WeightedUpperGap245212
open OMA.Smooth245212 (W w_mult)
open scoped ArithmeticFunction.sigma Function

def localCost : ℕ→Polynomial ℕ→Polynomial ℕ
  | 0,_ => 1
  | n+1,A => 2*(A+1)*localCost n (2*(A+1)^2)

def fixed : ℕ→Polynomial ℕ
  | 0 => 1
  | r+1 => let K:=fixed r; let B:=2*K*X*2^r+2
           2*K+(X^(r+1)*(B^2)^(r+1))*localCost (r+1) (X*(B*(X*B)+1)^(r+1))

def envelope (r : ℕ) : Polynomial ℕ := ∑j∈range (r+1),fixed j

theorem evaluate_local (n x : ℕ) (A : Polynomial ℕ) :
    (localCost n A).eval x=OMA.PositiveProductGap245212.cost n (A.eval x) := by
  induction n generalizing A with
  | zero => simp [localCost,OMA.PositiveProductGap245212.cost]
  | succ n ih => simp [localCost,OMA.PositiveProductGap245212.cost,ih]

theorem evaluate_fixed (r x : ℕ) : (fixed r).eval x=OMA.WeightedUniformGap245212.constant r x := by
  induction r with
  | zero => simp [fixed,OMA.WeightedUniformGap245212.constant]
  | succ r ih => simp [fixed,evaluate_local,ih,OMA.WeightedUniformGap245212.constant,
      OMA.WeightedUniformGap245212.cutoff,boundedCost]

theorem monotone_eval (P : Polynomial ℕ) : Monotone P.eval := by
  intro a b le
  simp only [eval_eq_sum,Polynomial.sum]
  exact sum_le_sum (fun i _=>Nat.mul_le_mul_left _ (Nat.pow_le_pow_left le i))

theorem eval_height (P : Polynomial ℕ) (x : ℕ) :
    P.eval x≤P.eval 1*(x+1)^P.natDegree := by
  rw [eval_eq_sum,eval_eq_sum]
  simp only [Polynomial.sum,one_pow,mul_one,sum_mul]
  refine sum_le_sum fun i hi=>Nat.mul_le_mul_left _ ?_
  exact (Nat.pow_le_pow_left (Nat.le_succ _) i).trans
    (Nat.pow_le_pow_right (Nat.succ_pos _) (P.le_natDegree_of_mem_supp i hi))

theorem original {h U V R r x : ℕ} (hp : 0<h) (rank : h.primeFactors.card≤r)
    (len : ∀p∈h.primeFactors,h.factorization p+1≤x) (vx : V≤x) (rp : 0<R)
    (eqn : U*(h*σ 0 h)=R+V*W h) : h*σ 0 h≤(envelope r).eval x*R := by
  let s:=h.primeFactors
  let z (p:ℕ):=p^h.factorization p
  have repr : h=∏p∈s,z p:=Nat.prod_primeFactors_pow_factorization hp.ne'
  have pr (p) (mp:p∈s) := prime_of_mem_primeFactors mp
  have pair : (s:Set ℕ).Pairwise (Coprime on z):=by
    intro p mp q mq ne
    exact (((coprime_primes (pr p mp) (pr q mq)).mpr ne).pow_left _).pow_right _
  have weight:=IsMultiplicative.map_prod z w_mult s pair
  have tau:=IsMultiplicative.map_prod z (isMultiplicative_sigma (k:=0)) s pair
  rw [←repr] at weight tau
  have lengths : (∏p∈s,(h.factorization p+1))=σ 0 h := by
    rw [tau]
    exact prod_congr rfl (fun p mp=>(sigma_zero_apply_prime_pow (pr p mp)).symm)
  have mass_eq : (∏p∈s,mass p (h.factorization p))=h*σ 0 h := by
    simp only [mass,prod_mul_distrib]
    change (∏p∈s,(h.factorization p+1))*(∏p∈s,z p)=_
    rw [lengths,←repr,mul_comm]
  have ineq:=OMA.WeightedUniformGap245212.bound s.card x s id (fun p=>h.factorization p)
    (U:=U) rfl pr len vx rp (by
      change U*(∏i∈s,mass i (h.factorization i))=R+V*(∏i∈s,W (z i))
      rwa [mass_eq,←weight])
  change (∏p∈s,mass p (h.factorization p))≤_ at ineq
  rw [mass_eq] at ineq
  have inc : (fixed s.card).eval x≤(envelope r).eval x:=by
    simp only [envelope,eval_finsetSum]
    exact single_le_sum (f:=fun j=>(fixed j).eval x) (fun _ _=>Nat.zero_le _)
      (mem_range.mpr (Nat.lt_succ_of_le rank))
  rw [evaluate_fixed] at inc
  exact ineq.trans (Nat.mul_le_mul_right R inc)

#print axioms original
end
end OMA.WeightedGapPolynomial245212

end

section

/- Congruences for complete dyadic blocks in the weighted geometric sum. -/
namespace OMA.DyadicBlocks245212
open Finset Nat

def geom (p n : ℕ) := ∑ i∈range n,p^i
def weight (p n : ℕ) := ∑ i∈range n,p^i*(i+1)

theorem split_g (p m n : ℕ) : geom p (m+n)=geom p m+p^m*geom p n := by
  simp only [geom,sum_range_add,mul_sum,pow_add]

theorem split_w (p m n : ℕ) :
    weight p (m+n)=weight p m+p^m*(weight p n+m*geom p n) := by
  simp only [weight,geom,sum_range_add]
  congr 1
  simp only [mul_sum,←sum_add_distrib,pow_add]
  apply sum_congr rfl
  intro i _
  ring

theorem pow_block (p h : ℕ) (ho : Odd p) :
    p^(2^h) ≡ 1 [MOD 2^(h+1)] := by
  have cop := (Nat.coprime_two_right.mpr ho).pow_right (h+1)
  simpa only [Nat.totient_prime_pow_succ Nat.prime_two,Nat.reduceSub,mul_one] using
    Nat.ModEq.pow_totient cop

theorem div_geom (p : ℕ) (ho : Odd p) (h : ℕ) : 2^h ∣ geom p (2^h) := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [pow_succ, Nat.mul_two,split_g,←one_add_mul]
    have even := (ho.pow (n:=2^h)).add_one
    simpa [Nat.two_mul,add_comm] using Nat.mul_dvd_mul (even_iff_two_dvd.mp even) ih

theorem weight_block (p : ℕ) (ho : Odd p) (h : ℕ) :
    weight p (2^(h+1)) ≡ 2^h [MOD 2^(h+1)] := by
  induction h with
  | zero => simp [weight,sum_range_succ,Nat.ModEq]
  | succ h ih =>
    let N := 2^(h+1)
    have even : 2∣geom p N := (dvd_pow_self 2 (by omega : h+1≠0)).trans (div_geom p ho _)
    have off : N*geom p N ≡ 0 [MOD 2*N] := by
      apply Nat.modEq_zero_iff_dvd.mpr
      simpa [mul_comm] using Nat.mul_dvd_mul_left N even
    have pp : p^N ≡ 1 [MOD 2*N] := by
      simpa only [N,pow_succ (2:ℕ) (h+1),mul_comm] using pow_block p (h+1) ho
    have twice : 2*weight p N ≡ N [MOD 2*N] := by
      simpa only [N,pow_succ' (2:ℕ) h] using ih.mul_left' 2
    have bridge := (Nat.ModEq.rfl (a:=weight p N)).add
      (pp.mul ((Nat.ModEq.rfl (a:=weight p N)).add off))
    change weight p (2^(h+1+1)) ≡ 2^(h+1) [MOD 2^(h+1+1)]
    rw [pow_succ' (2:ℕ) (h+1)]
    change weight p (2*N) ≡ N [MOD 2*N]
    rw [show 2*N=N+N by omega,split_w]
    simpa [Nat.two_mul] using bridge.trans (by simpa [Nat.two_mul] using twice)

theorem prime_block (p h a : ℕ) (hp : p.Prime) (ho : Odd p) :
    let N := 2^(h+1)
    let n := p^(a*N)
    n ≡ 1 [MOD N] ∧ ArithmeticFunction.sigma 0 n ≡ 1 [MOD N] ∧
      ArithmeticFunction.sigma 1 n ≡ 1 [MOD N] ∧
      OMA.Smooth245212.W n ≡ 1+a*2^h [MOD N] := by
  let N := 2^(h+1)
  have p1 : p^N ≡ 1 [MOD N] := (pow_block p (h+1) ho).of_dvd
    (pow_dvd_pow _ (by omega : h+1≤h+1+1))
  have zeroG := Nat.modEq_zero_iff_dvd.mpr (div_geom p ho (h+1))
  have we := weight_block p ho h
  have powr (b : ℕ) : p^(b*N) ≡ 1 [MOD N] := by
    rw [Nat.mul_comm b N,pow_mul]
    simpa only [one_pow] using p1.pow b
  have dz (b : ℕ) : b*N ≡ 0 [MOD N] := Nat.modEq_zero_iff_dvd.mpr (dvd_mul_left _ _)
  have blk (b : ℕ) : geom p (b*N) ≡ 0 [MOD N] ∧ weight p (b*N) ≡ b*2^h [MOD N] := by
    induction b with
    | zero => simp [geom,weight,Nat.ModEq]
    | succ b ih =>
      rw [Nat.succ_mul,split_g,split_w]
      constructor
      · simpa only [mul_zero,add_zero] using ih.1.add ((powr b).mul zeroG)
      · simpa only [zero_mul,add_zero,one_mul,Nat.succ_mul] using
          ih.2.add ((powr b).mul (we.add ((dz b).mul zeroG)))
  have times (b : ℕ) : b*N+1 ≡ 1 [MOD N] := (dz b).add_right 1
  refine ⟨powr a,?_,?_,?_⟩
  · rw [ArithmeticFunction.sigma_zero_apply_prime_pow hp]; exact times a
  · rw [ArithmeticFunction.sigma_one_apply_prime_pow hp,sum_range_succ]
    simpa only [geom,N,zero_add] using (blk a).1.add (powr a)
  · rw [OMA.Smooth245212.w_pow hp,sum_range_succ]
    simpa only [weight,N,one_mul,add_comm 1] using (blk a).2.add ((powr a).mul (times a))

end OMA.DyadicBlocks245212

end

section

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

end

section

/- Limits of the weighted divisor factors on odd fourth powers have odd
numerators. Finite products of them stay uniformly away from two. -/
namespace OMA.SquareCompact245212
open Finset Filter Topology OMA.Smooth245212

def OddNum (x : ℚ) := ∃ A B : ℕ, Odd A ∧ 0<B ∧ x=(A:ℚ)/B

theorem one : OddNum 1 := ⟨1,1,by decide,by decide,by norm_num⟩
theorem mul {x y : ℚ} (hx : OddNum x) (hy : OddNum y) : OddNum (x*y) := by
  obtain ⟨a,b,ha,hb,rfl⟩ := hx
  obtain ⟨c,d,hc,hd,rfl⟩ := hy
  exact ⟨a*c,b*d,ha.mul hc,Nat.mul_pos hb hd,by push_cast; ring⟩
theorem ne_two {x : ℚ} (h : OddNum x) : x≠2 := by
  obtain ⟨a,b,ha,hb,rfl⟩ := h
  intro eq
  have div := (div_eq_iff (by positivity : (b:ℚ)≠0)).mp eq
  have same : a=2*b := by exact_mod_cast div
  obtain ⟨t,ht⟩ := ha
  omega

theorem quotient {p e : ℕ} (hp : Nat.Prime p) (odd : Odd (W (p^e))) :
    OddNum (X p (some e)) := by
  refine ⟨W (p^e),(e+1)*p^e,odd,by have := hp.pos; positivity,?_⟩
  apply (eq_div_iff (by have := hp.pos; positivity)).2
  simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_pow] using x_factor hp e

private theorem finite_factor {p e : ℕ} (hp : Nat.Prime p) (po : Odd p) (e4 : 4∣e) :
    OddNum (X p (some e)) := by
  obtain ⟨a,rfl⟩ := e4
  have hh := (OMA.DyadicBlocks245212.prime_block p 0 (2*a) hp po).2.2.2
  apply quotient hp
  rw [Nat.odd_iff]
  simpa [Nat.ModEq,show 2*a*2=4*a by ring,Nat.add_mod] using hh

theorem infinite_factor {p : ℕ} (hp : Nat.Prime p) (po : Odd p) :
    OddNum (X p none) := by
  refine ⟨p,p-1,po,by have := hp.one_lt; omega,?_⟩
  have pp : (1:ℚ)<p := by exact_mod_cast hp.one_lt
  simp only [X,Y,sub_zero,Nat.cast_sub hp.one_le,Nat.cast_one]
  field_simp [show (p:ℚ)-1≠0 by linarith]; ring

private theorem dichotomy {v : ℕ → ℕ} (inc : Monotone v) :
    (∃ M, ∀ᶠ n in atTop,v n=M) ∨ Tendsto v atTop atTop := by
  by_cases h : BddAbove (Set.range v)
  · obtain ⟨n,hn⟩ := Nat.sSup_mem (Set.range_nonempty v) h
    refine Or.inl ⟨v n,eventually_atTop.mpr ⟨n,fun m hm => le_antisymm ?_ (inc hm)⟩⟩
    rw [hn]; exact le_csSup h ⟨m,rfl⟩
  · exact Or.inr (tendsto_atTop_atTop_of_monotone' inc h)

/-- A moving prime or exponent has an odd-numerator limit automatically.
Only pairs stabilizing in both coordinates need a local arithmetic check. -/
theorem factor_limit_restricted (s : ℚ → Prop) (p e : ℕ → ℕ) (pm : Monotone p) (em : Monotone e)
    (hp : ∀ n,Nat.Prime (p n)) (po : ∀ n,Odd (p n)) (atOne : s 1)
    (atCap : ∀ P : ℕ,Nat.Prime P → Odd P → (∀ᶠ n in atTop,p n=P) → s (X P none))
    (stable : ∀ P E, (∀ᶠ n in atTop,p n=P) → (∀ᶠ n in atTop,e n=E) →
      s (X P (some E))) :
    ∃ x : ℚ,s x ∧ Tendsto (fun n => X (p n) (some (e n))) atTop (𝓝 x) := by
  rcases dichotomy pm with ⟨P,hP⟩|hP
  · obtain ⟨n,hn⟩ := hP.exists
    have pr : Nat.Prime P := hn ▸ hp n
    have od : Odd P := hn ▸ po n
    rcases dichotomy em with ⟨E,hE⟩|hE
    · refine ⟨X P (some E),stable P E hP hE,?_⟩
      apply tendsto_const_nhds.congr'
      filter_upwards [hP,hE] with n a b; rw [a,b]
    · have upper : Tendsto (fun n : ℕ => (2:ℚ)/(e n+1)) atTop (𝓝 0) := by
        simpa only [Function.comp_apply,div_eq_mul_inv,one_mul,mul_zero] using
          ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℚ)).comp hE).const_mul 2
      have yl : Tendsto (fun n => Y P (some (e n))) atTop (𝓝 0) :=
        tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds upper
          (fun n => y_nonneg pr.one_lt _) (fun n => ((lt_div_iff₀ (by positivity)).mpr
            (OMA.CapOrder245212.y_short pr (e n))).le)
      have pp : (1:ℚ)<P := by exact_mod_cast pr.one_lt
      refine ⟨X P none,atCap P pr od hP,?_⟩
      have lim := (tendsto_const_nhds (x:=(1:ℚ))).add
        (((tendsto_const_nhds (x:=(1:ℚ))).sub yl).div_const ((P:ℚ)-1))
      apply lim.congr'
      filter_upwards [hP] with n pn; rw [pn]; rfl
  · have pt : Tendsto (fun n => (p n:ℚ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hP
    have den : Tendsto (fun n => (p n:ℚ)-1) atTop atTop := by
      apply tendsto_atTop.mpr
      intro x
      filter_upwards [tendsto_atTop.mp pt (x+1)] with n hn
      linarith
    have inv : Tendsto (fun n => ((p n:ℚ)-1)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp den
    refine ⟨1,atOne,tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (show Tendsto (fun n => 1+((p n:ℚ)-1)⁻¹) atTop (𝓝 1) by simpa using inv.const_add 1) ?_ ?_⟩
    · intro n
      have pp : (1:ℚ)<p n := by exact_mod_cast (hp n).one_lt
      exact le_add_of_nonneg_right (div_nonneg (sub_nonneg.mpr (y_one (hp n).one_lt _)) (by linarith))
    · intro n
      have pp : (1:ℚ)<p n := by exact_mod_cast (hp n).one_lt
      simp only [X,←one_div]
      exact add_le_add_right (div_le_div_of_nonneg_right (sub_le_self _ (y_nonneg (hp n).one_lt _))
        (by linarith)) _

theorem factor_limit_by (s : ℚ → Prop) (p e : ℕ → ℕ) (pm : Monotone p) (em : Monotone e)
    (hp : ∀ n,Nat.Prime (p n)) (po : ∀ n,Odd (p n)) (atOne : s 1)
    (atCap : ∀ P : ℕ,Nat.Prime P → Odd P → s (X P none))
    (stable : ∀ P E, (∀ᶠ n in atTop,p n=P) → (∀ᶠ n in atTop,e n=E) →
      s (X P (some E))) :
    ∃ x : ℚ,s x ∧ Tendsto (fun n => X (p n) (some (e n))) atTop (𝓝 x) :=
  factor_limit_restricted s p e pm em hp po atOne (fun P pr op _ => atCap P pr op) stable

theorem factor_limit_of_stable (p e : ℕ → ℕ) (pm : Monotone p) (em : Monotone e)
    (hp : ∀ n,Nat.Prime (p n)) (po : ∀ n,Odd (p n))
    (stable : ∀ P E, (∀ᶠ n in atTop,p n=P) → (∀ᶠ n in atTop,e n=E) →
      OddNum (X P (some E))) :
    ∃ x : ℚ,OddNum x ∧ Tendsto (fun n => X (p n) (some (e n))) atTop (𝓝 x) :=
  factor_limit_by OddNum p e pm em hp po one (fun _ => infinite_factor) stable

theorem factor_limit (p e : ℕ → ℕ) (pm : Monotone p) (em : Monotone e)
    (hp : ∀ n,Nat.Prime (p n)) (po : ∀ n,Odd (p n)) (ed : ∀ n,4∣e n) :
    ∃ x : ℚ,OddNum x ∧ Tendsto (fun n => X (p n) (some (e n))) atTop (𝓝 x) := by
  apply factor_limit_of_stable p e pm em hp po
  intro P E pP eE
  obtain ⟨n,pn,en⟩ := (pP.and eE).exists
  exact finite_factor (pn ▸ hp n) (pn ▸ po n) (en ▸ ed n)

theorem uniform_gap (K : ℕ) (c : ℚ) (hc : OddNum c) :
    ∃ δ : ℚ, 0<δ ∧ ∀ p e : Fin K → ℕ, (∀ i,Nat.Prime (p i)) → (∀ i,Odd (p i)) →
      (∀ i,4∣e i) → δ≤|c*(∏ i,X (p i) (some (e i)))-2| := by
  by_contra! bad
  have pick (n : ℕ) := bad (1/((n:ℚ)+1)) (by positivity)
  choose p e hp ho he close using pick
  let seq (n : ℕ) := (p n,e n)
  obtain ⟨g,sorted⟩ := wellQuasiOrdered_le.exists_monotone_subseq seq
  have points (i : Fin K) := factor_limit (fun n => p (g n) i) (fun n => e (g n) i)
    (fun _ _ le => (sorted _ _ le).1 i) (fun _ _ le => (sorted _ _ le).2 i)
    (fun n => hp (g n) i) (fun n => ho (g n) i) (fun n => he (g n) i)
  choose x ox conv using points
  have prod (s : Finset (Fin K)) : OddNum (∏ i∈s,x i) := by
    induction s using Finset.induction_on with
    | empty => simpa using one
    | @insert i s mem ih => simpa only [prod_insert mem] using mul (ox i) ih
  have unequal := ne_two (mul hc (prod univ))
  have limit := (tendsto_finsetProd univ (fun i _ => conv i)).const_mul c
  have t2 : Tendsto (fun n => c*∏ i,X (p n i) (some (e n i))) atTop (𝓝 2) := by
    have hz := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℚ)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (show Tendsto (fun n : ℕ => 2-1/((n:ℚ)+1)) atTop (𝓝 2) by simpa using tendsto_const_nhds.sub hz)
      (show Tendsto (fun n : ℕ => 2+1/((n:ℚ)+1)) atTop (𝓝 2) by simpa using hz.const_add 2)
    · intro n; linarith only [(abs_lt.mp (close n)).1]
    · intro n; linarith only [(abs_lt.mp (close n)).2]
  exact unequal (tendsto_nhds_unique limit (t2.comp g.strictMono.tendsto_atTop))

end OMA.SquareCompact245212

end

section

/- In an equality whose odd part is a power of 2 in its exponent,
the divisor count of the square root of the odd part is 1 modulo that power. -/
namespace OMA.DyadicPower245212
open Finset Nat ArithmeticFunction OMA.Smooth245212 OMA.Abundance245212 OMA.DyadicBlocks245212
open scoped ArithmeticFunction.sigma ArithmeticFunction.Omega

private theorem odd_block (u h : ℕ) (odd : Odd u) :
    let N := 2^(h+1)
    let v := u^N
    v ≡ 1 [MOD N] ∧ σ 0 v ≡ 1 [MOD N] ∧ σ 1 v ≡ 1 [MOD N] ∧
      W v ≡ σ 0 (u^(2^h)) [MOD N] := by
  let N := 2^(h+1)
  induction u using Nat.recOnPrimeCoprime with
  | zero => simp at odd
  | prime_pow p e hp =>
    by_cases zero : e=0
    · subst e; simp [W,Nat.ModEq]
    have op : Odd p := (Nat.prime_two.coprime_iff_not_dvd.mp
      (Nat.coprime_two_left.mpr odd)) |> fun h => Nat.odd_iff.mpr (by
        by_contra! hh
        have d : 2∣p := by omega
        exact h (d.trans (dvd_pow_self _ zero)))
    have hh := prime_block p h e hp op
    simpa only [←pow_mul,sigma_zero_apply_prime_pow hp,add_comm 1] using hh
  | coprime a b ha hb hab ia ib =>
    obtain ⟨oa,ob⟩ := Nat.odd_mul.mp odd
    obtain ⟨a0,a1,a2,a3⟩ := ia oa
    obtain ⟨b0,b1,b2,b3⟩ := ib ob
    have c := (hab.pow_left (2^(h+1))).pow_right (2^(h+1))
    have d := (hab.pow_left (2^h)).pow_right (2^h)
    dsimp only
    simp only [mul_pow,isMultiplicative_sigma.map_mul_of_coprime c,
      isMultiplicative_sigma.map_mul_of_coprime d,w_mult.map_mul_of_coprime c]
    exact ⟨by simpa using a0.mul b0,by simpa using a1.mul b1,by simpa using a2.mul b2,a3.mul b3⟩

private theorem dyadic_balance (k : ℕ) :
    W (2^k)+σ 1 (2^k)=2*2^k*(σ 0 (2^k)) := by
  rw [w_pow Nat.prime_two,sigma_zero_apply_prime_pow Nat.prime_two,
    sigma_one_apply_prime_pow Nat.prime_two]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ _ (k+1),sum_range_succ _ (k+1),pow_succ]
    linarith only [ih]

theorem dyadic_odd (k : ℕ) : Odd (W (2^k)) := by
  rw [w_pow Nat.prime_two,Nat.odd_iff,sum_range_succ']
  have h : 2∣∑ i∈range k, 2^(i+1)*(i+1+1) :=
    Finset.dvd_sum (fun i _ => dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) _)
  simp only [pow_zero,zero_add,one_mul]
  omega

theorem tau_root {k h u : ℕ} (ou : Odd u)
    (eq : OeisA245212.a (2^k*u^(2^(h+1)))=(σ 1 (2^k*u^(2^(h+1))):ℤ)) :
    σ 0 (u^(2^h)) ≡ 1 [MOD 2^(h+1)] := by
  let d := 2^k
  let N := 2^(h+1)
  let v := u^N
  have cop : d.Coprime v := ((Nat.coprime_two_left.mpr ou).pow_left k).pow_right N
  have nz : d*v ≠ 0 := mul_ne_zero (by dsimp [d]; positivity) (pow_ne_zero _ ou.pos.ne')
  have bal := balance nz eq
  rw [w_mult.map_mul_of_coprime cop,isMultiplicative_sigma.map_mul_of_coprime cop,
    isMultiplicative_sigma.map_mul_of_coprime cop] at bal
  obtain ⟨v0,t,s,w⟩ := odd_block u h ou
  have red : W d*(σ 0 (u^(2^h)))+σ 1 d ≡ 2*d*(σ 0 d) [MOD N] := by
    have left := (w.mul_left (W d)).add (s.mul_left (σ 1 d))
    have right := ((v0.mul_left d).mul_left 2).mul (t.mul_left (σ 0 d))
    apply (show W d*(σ 0 (u^(2^h)))+σ 1 d ≡ W d*W v+σ 1 d*(σ 1 v) [MOD N] by
      simpa only [mul_one] using left.symm).trans
    rw [bal]
    simpa only [mul_one] using right
  have known := dyadic_balance k
  change W d+σ 1 d=2*d*(σ 0 d) at known
  rw [←known] at red
  have coeff : N.Coprime (W d) := (Nat.coprime_two_left.mpr (dyadic_odd k)).pow_left _
  exact (red.add_right_cancel' _ |>.trans (show W d ≡ W d*1 [MOD N] by rw [mul_one])).cancel_left_of_coprime coeff

private theorem square_of_odd_tau {u : ℕ} (odd : Odd (σ 0 u)) : IsSquare u := by
  induction u using Nat.recOnPrimeCoprime with
  | zero => simp at odd
  | prime_pow p a hp =>
    rw [sigma_zero_apply_prime_pow hp,Nat.odd_iff] at odd
    have even : Even a := Nat.even_iff.mpr (by omega)
    obtain ⟨b,rfl⟩ := even
    exact ⟨p^b,pow_add _ _ _⟩
  | coprime a b _ _ cop ia ib =>
    rw [isMultiplicative_sigma.map_mul_of_coprime cop,Nat.odd_mul] at odd
    exact (ia odd.1).mul (ib odd.2)

/-- If the odd part of a solution is a square, it is a fourth power. -/
theorem square_root_is_square {k u : ℕ} (ou : Odd u)
    (eq : OeisA245212.a (2^k*u^2)=(σ 1 (2^k*u^2):ℤ)) : IsSquare u := by
  have v := tau_root (h:=0) ou eq
  apply square_of_odd_tau
  simpa [Nat.odd_iff,Nat.ModEq] using v

private theorem merge (a b H : ℕ) (even : Even H) :
    (1+a*H)*(1+b*H) ≡ 1+(a+b)*H [MOD 2*H] := by
  obtain ⟨c,hc⟩ := even
  rw [show (1+a*H)*(1+b*H)=(2*H)*(a*b*c)+(1+(a+b)*H) by rw [hc]; ring]
  exact Nat.ModEq.modulus_mul_add

private theorem tau_linear (u H : ℕ) (even : Even H) (nz : u≠0) :
    σ 0 (u^H) ≡ 1+Ω u*H [MOD 2*H] := by
  induction u using Nat.recOnPrimeCoprime with
  | zero => contradiction
  | prime_pow p a hp =>
    simp only [←pow_mul,sigma_zero_apply_prime_pow hp,cardFactors_apply_prime_pow hp,add_comm 1]
    rfl
  | coprime a b ha hb hab ia ib =>
    have a0 : a≠0 := by omega
    have b0 : b≠0 := by omega
    rw [mul_pow,isMultiplicative_sigma.map_mul_of_coprime ((hab.pow_left H).pow_right H),
      cardFactors_mul a0 b0]
    exact ((ia a0).mul (ib b0)).trans (merge _ _ H even)

/-- A perfect-power odd part must have a root with even total prime multiplicity. -/
theorem even_multiplicity {k h u : ℕ} (ou : Odd u)
    (eq : OeisA245212.a (2^k*u^(2^(h+1)))=(σ 1 (2^k*u^(2^(h+1))):ℤ)) :
    Even (Ω u) := by
  cases h with
  | zero =>
    obtain ⟨v,eqv⟩ := square_root_is_square ou eq
    rw [eqv,←sq,cardFactors_pow]; exact even_two_mul _
  | succ h =>
    let H : ℕ := 2^(h+1)
    have hh : Even H := even_iff_two_dvd.mpr (dvd_pow_self _ (by omega))
    have root := tau_root ou eq
    rw [pow_succ' (2:ℕ) (h+1)] at root
    have lin := tau_linear u H hh ou.pos.ne'
    have m : 1+Ω u*H ≡ 1+0 [MOD 2*H] := lin.symm.trans root
    have z : Ω u*H ≡ 0*H [MOD 2*H] := by simpa only [zero_mul] using m.add_left_cancel' 1
    exact even_iff_two_dvd.mpr (Nat.modEq_zero_iff_dvd.mp (z.mul_right_cancel' (by dsimp [H]; positivity)))

end OMA.DyadicPower245212

end

section

/- For a fixed positive exponent vector there are finitely many choices of
prime bases at which a fixed positive combination of the two divisor products
can equal a given number. The products decrease when bases increase. -/
namespace OMA.FixedExponents245212
open Finset OMA.Smooth245212

private theorem x_avg {p : ℕ} (hp : Nat.Prime p) (e : ℕ) :
    X p (some e)=(∑ j∈range (e+1),((e-j+1:ℕ):ℚ)*(p:ℚ)⁻¹^j)/((e:ℚ)+1) := by
  have xf := x_factor hp e
  rw [w_pow hp] at xf
  push_cast at xf
  have nz : (p:ℚ)≠0 := by exact_mod_cast hp.ne_zero
  apply (eq_div_iff (by positivity)).2
  apply mul_right_cancel₀ (pow_ne_zero e nz)
  rw [mul_assoc,xf,sum_mul]
  rw [←sum_range_reflect (fun j => (p:ℚ)^j*((j:ℚ)+1)) (e+1)]
  refine sum_congr rfl fun j hj => ?_
  have h : j≤e := by have := mem_range.mp hj; omega
  have h' : e+1-1-j=e-j := by omega
  rw [h',Nat.cast_add,Nat.cast_one]
  have add : j+(e-j)=e := by omega
  have cancel : (p:ℚ)⁻¹^j*(p:ℚ)^e=(p:ℚ)^(e-j) := by
    calc
      _ = (p:ℚ)⁻¹^j*((p:ℚ)^j*(p:ℚ)^(e-j)) := by rw [←pow_add,add]
      _ = _ := by rw [inv_pow,←mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ nz),one_mul]
  rw [mul_assoc,cancel,mul_comm]

private theorem y_strict_prime {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (pq : p<q) {e : ℕ} (ep : 0<e) : Y q (some e)<Y p (some e) := by
  rw [y_avg hq.one_lt,y_avg hp.one_lt]
  apply div_lt_div_of_pos_right _ (by positivity)
  apply sum_lt_sum
  · intro i _
    gcongr
    exact_mod_cast hp.pos
  · refine ⟨1,mem_range.mpr (by omega),?_⟩
    simp only [pow_one]
    apply inv_lt_inv₀ (by exact_mod_cast hq.pos) (by exact_mod_cast hp.pos) |>.mpr
    exact_mod_cast pq

private theorem x_le_prime {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (pq : p≤q) (e : ℕ) : X q (some e)≤X p (some e) := by
  rw [x_avg hp,x_avg hq]
  gcongr
  exact_mod_cast hp.pos

theorem y_pos {p : ℕ} (hp : Nat.Prime p) (e : ℕ) : 0<Y p (some e) := by
  rw [y_avg hp.one_lt]
  apply div_pos _ (by positivity)
  exact sum_pos' (fun _ _ => by positivity) ⟨0,by simp,by simp⟩

theorem finite_bases {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → ℕ)
    (ep : ∀ i,0<e i) (a b t : ℚ) (ha : 0≤a) (hb : 0<b) :
    {p : ι → ℕ | (∀ i,Nat.Prime (p i)) ∧
      a*(∏ i,X (p i) (some (e i)))+b*(∏ i,Y (p i) (some (e i)))=t}.Finite := by
  apply WellQuasiOrderedLE.finite_of_isAntichain
  intro p hp q hq diff pq
  obtain ⟨i,lt⟩ : ∃ i,p i<q i := by
    by_contra! h; exact diff (funext fun j => Nat.le_antisymm (pq j) (h j))
  have yp (j) := y_pos (hq.1 j) (e j)
  have xp := prod_le_prod (s:=univ) (fun j _ => x_nonneg (hq.1 j).one_lt (some (e j)))
    (fun j _ => x_le_prime (hp.1 j) (hq.1 j) (pq j) (e j))
  have ys (j) : Y (q j) (some (e j))≤Y (p j) (some (e j)) := by
    rcases (pq j).eq_or_lt with h|l
    · rw [h]
    · exact (y_strict_prime (hp.1 j) (hq.1 j) l (ep j)).le
  have strict := Finset.prod_lt_prod (s:=univ) (fun j _ => yp j) (fun j _ => ys j)
    ⟨i,mem_univ i,y_strict_prime (hp.1 i) (hq.1 i) lt (ep i)⟩
  linarith only [hp.2,hq.2,mul_le_mul_of_nonneg_left xp ha,mul_lt_mul_of_pos_left strict hb]

end OMA.FixedExponents245212

end

section

/- Finitely many solutions at fixed dyadic exponent and bounded number of odd
prime factors, whenever the odd part is a square. -/
namespace OMA.SquareFinite245212
open Finset OMA.Smooth245212 OMA.SquareCompact245212
open scoped ArithmeticFunction.sigma

def Config (K : ℕ) (c d : ℚ) (p e : Fin K → ℕ) :=
  (∀ i,Nat.Prime (p i)) ∧ (∀ i,Odd (p i)) ∧ (∀ i,4∣e i) ∧ (∀ i,0<e i) ∧
  c*(∏ i,X (p i) (some (e i)))+d*(∏ i,Y (p i) (some (e i)))=2

private theorem bounded {K : ℕ} {c d : ℚ} (hc : OddNum c) (d0 : 0<d) (d1 : d≤1) :
    ∃ L : ℕ, ∀ p e, Config K c d p e → ∀ i,e i<L := by
  obtain ⟨δ,hδ,sep⟩ := uniform_gap K c hc
  obtain ⟨L,hL⟩ := exists_nat_gt (2/δ)
  refine ⟨L,fun p e he i => ?_⟩
  obtain ⟨hp,ho,ed,_,eq⟩ := he
  have bound := sep p e hp ho ed
  have y0 (j) := y_nonneg (hp j).one_lt (some (e j))
  have z : 0≤d*(∏ j,Y (p j) (some (e j))) := mul_nonneg d0.le (prod_nonneg (fun j _ => y0 j))
  have act : |c*(∏ j,X (p j) (some (e j)))-2|=d*(∏ j,Y (p j) (some (e j))) := by
    rw [abs_of_nonpos (by linarith only [eq,z])]; linarith only [eq]
  rw [act] at bound
  have upper : δ≤Y (p i) (some (e i)) := by
    apply bound.trans
    rw [←prod_erase_mul _ _ (mem_univ i)]
    exact (mul_le_of_le_one_left (mul_nonneg (prod_nonneg (fun j _ => y0 j)) (y0 i)) d1).trans
      (mul_le_of_le_one_left (y0 i) (prod_le_one (fun j _ => y0 j)
        (fun j _ => y_one (hp j).one_lt _)))
  have hh := OMA.CapOrder245212.y_short (hp i) (e i)
  have m := mul_le_mul_of_nonneg_right upper (show 0≤(e i:ℚ)+1 by positivity)
  have qq : (e i:ℚ)<2/δ := (lt_div_iff₀ hδ).mpr (by linarith only [hh,m,hδ])
  exact_mod_cast qq.trans hL

theorem configs (K : ℕ) (c d : ℚ) (hc : OddNum c) (d0 : 0<d) (d1 : d≤1) :
    {v : (Fin K → ℕ) × (Fin K → ℕ) | Config K c d v.1 v.2}.Finite := by
  obtain ⟨L,size⟩ := bounded hc d0 d1
  have c0 : 0≤c := by obtain ⟨A,B,_,_,rfl⟩ := hc; positivity
  apply Set.Finite.of_finite_fibers Prod.snd
  · apply (Set.Finite.pi' (fun _ : Fin K => Set.finite_Iio L)).subset
    rintro e ⟨⟨p,v⟩,h,rfl⟩
    exact size _ _ h
  · rintro e ⟨⟨p,v⟩,conf,rfl⟩
    have finite := OMA.FixedExponents245212.finite_bases v conf.2.2.2.1 c d 2 c0 d0
    apply (finite.image (fun q => (q,v))).subset
    rintro ⟨q,f⟩ ⟨hf,hv⟩
    have same : f=v := hv
    subst f
    exact ⟨q,⟨hf.1,hf.2.2.2.2⟩,rfl⟩

private theorem square_rank (k K : ℕ) :
    {u : ℕ | Odd u ∧ IsSquare u ∧ u.primeFactors.card=K ∧
      OeisA245212.a (2^k*u)=(σ 1 (2^k*u):ℤ)}.Finite := by
  let c := X 2 (some k)
  let d := Y 2 (some k)
  have hc : OddNum c := quotient Nat.prime_two (OMA.DyadicPower245212.dyadic_odd k)
  have d0 : 0<d := by
    dsimp [d]; rw [y_avg (by decide : 1<2)]
    exact div_pos (sum_pos' (fun i _ => by positivity) ⟨0,by simp,by simp⟩) (by positivity)
  apply ((configs K c d hc d0 (y_one (by decide) _)).image (fun v => total v.1 v.2)).subset
  rintro u ⟨odd,sq,card,eq⟩
  let S := u.primeFactors
  let p := S.orderEmbOfFin card
  let e (i : Fin K) := u.factorization (p i)
  have mem (i) : p i∈u.primeFactors := orderEmbOfFin_mem S card i
  have hp (i) := Nat.prime_of_mem_primeFactors (mem i)
  have op (i) : Odd (p i) := Nat.coprime_two_left.mp ((Nat.coprime_two_left.mpr odd).of_dvd_right
    (Nat.dvd_of_mem_primeFactors (mem i)))
  have ep (i) : 0<e i := (hp i).factorization_pos_of_dvd odd.pos.ne' (Nat.dvd_of_mem_primeFactors (mem i))
  have fourth : ∃ t,u=t^4 := by
    obtain ⟨w,hw⟩ := sq
    have wo : Odd w := (Nat.odd_mul.mp (hw ▸ odd)).1
    have eq' : OeisA245212.a (2^k*w^2)=(σ 1 (2^k*w^2):ℤ) := by simpa only [sq,hw] using eq
    obtain ⟨t,ht⟩ := OMA.DyadicPower245212.square_root_is_square wo eq'
    exact ⟨t,by rw [hw,ht]; ring⟩
  have ed (i) : 4∣e i := by
    obtain ⟨t,ht⟩ := fourth
    change 4∣u.factorization (p i)
    have f (q : ℕ) : 4∣u.factorization q := by
      rw [ht,Nat.factorization_pow]; simp
    apply f
  have repr : total p e=u := by
    exact (Fintype.prod_equiv (S.orderIsoOfFin card).toEquiv _
      (fun j : S => j.val^(u.factorization j.val)) (fun _ => rfl)).trans
      (Nat.prod_primeFactors_coe_pow_factorization odd.pos.ne').symm
  let P : Fin (K+1) → ℕ := Fin.cons 2 (p : Fin K → ℕ)
  let E : Fin (K+1) → ℕ := Fin.cons k e
  have prime : ∀ i,Nat.Prime (P i) := Fin.cases Nat.prime_two hp
  have inj : P.Injective := Fin.cons_injective_of_injective (by
    rintro ⟨i,hi⟩; have h := op i; rw [hi] at h; norm_num [Nat.odd_iff] at h) p.injective
  have entire : total P E=2^k*u := by
    rw [total,Fin.prod_univ_succ]; simp only [P,E,Fin.cons_zero,Fin.cons_succ]
    exact congrArg (2^k*·) repr
  have norm := normalized_of_eq P prime inj E (by rw [entire]; exact eq)
  unfold normalized at norm
  rw [Fin.prod_univ_succ (fun i => X (P i) (some (E i))),
    Fin.prod_univ_succ (fun i => Y (P i) (some (E i)))] at norm
  exact ⟨(p,e),⟨hp,op,ed,ep,by simpa only [P,E,c,d,Fin.cons_zero,Fin.cons_succ] using norm⟩,repr⟩

theorem square_finite (k K : ℕ) :
    {u : ℕ | Odd u ∧ IsSquare u ∧ u.primeFactors.card≤K ∧
      OeisA245212.a (2^k*u)=(σ 1 (2^k*u):ℤ)}.Finite := by
  apply ((Set.finite_Iic K).biUnion (fun j _ => square_rank k j)).subset
  rintro u ⟨ho,hs,hc,he⟩
  exact Set.mem_iUnion.mpr ⟨u.primeFactors.card,Set.mem_iUnion.mpr ⟨hc,ho,hs,rfl,he⟩⟩

end OMA.SquareFinite245212

end

section

/- Exact power of two in a weighted sum of divisors of an odd prime power. -/
namespace OMA.WeightVal245212
open Finset OMA.Smooth245212 OMA.DyadicBlocks245212
open scoped ArithmeticFunction.sigma
open OMA.DyadicBlocks245212 (split_g)
open OMA.DyadicBlocks245212 (split_w)
open OMA.DyadicBlocks245212 (pow_block)

abbrev val (n : ℕ) := n.factorization 2
theorem val_odd {n : ℕ} (h : Odd n) : val n=0 :=
  Nat.factorization_eq_zero_of_not_dvd (by have := Nat.odd_iff.mp h; omega)

theorem identify {n h : ℕ} (nz : 0<n) (mod : n ≡ 2^h [MOD 2^(h+1)]) : val n=h := by
  have pp : 0<2^h := Nat.two_pow_pos _
  have bound : 2^h<2^(h+1) := by rw [pow_succ]; omega
  have low : 2^h∣n := Nat.modEq_zero_iff_dvd.mp
    ((mod.of_dvd (pow_dvd_pow _ (by omega))).trans (Nat.modEq_zero_iff_dvd.mpr (dvd_refl _)))
  have high : ¬2^(h+1)∣n := by
    intro d
    have bad := Nat.modEq_zero_iff_dvd.mp (mod.symm.trans (Nat.modEq_zero_iff_dvd.mpr d))
    exact bound.not_ge (Nat.le_of_dvd pp bad)
  have l := (Nat.prime_two.pow_dvd_iff_le_factorization nz.ne').mp low
  have hi := mt (Nat.prime_two.pow_dvd_iff_le_factorization nz.ne').mpr high
  change n.factorization 2=h
  omega

theorem blocks (p : ℕ) (op : Odd p) (h u : ℕ) :
    let N := 2^(h+1)
    geom p (u*N) ≡ 0 [MOD N] ∧ weight p (u*N) ≡ u*2^h [MOD N] := by
  let N := 2^(h+1)
  have p1 : p^N ≡ 1 [MOD N] := (OMA.DyadicBlocks245212.pow_block p (h+1) op).of_dvd
    (pow_dvd_pow _ (by omega : h+1≤h+1+1))
  have gp := Nat.modEq_zero_iff_dvd.mpr (div_geom p op (h+1))
  have wp := weight_block p op h
  have powr (b : ℕ) : p^(b*N) ≡ 1 [MOD N] := by
    rw [Nat.mul_comm b N,pow_mul]; simpa only [one_pow] using p1.pow b
  dsimp only
  change geom p (u*N) ≡ 0 [MOD N] ∧ weight p (u*N) ≡ u*2^h [MOD N]
  induction u with
  | zero => simp [geom,weight,Nat.ModEq]
  | succ u ih =>
    have dz : u*N ≡ 0 [MOD N] := Nat.modEq_zero_iff_dvd.mpr (dvd_mul_left _ _)
    rw [Nat.succ_mul,OMA.DyadicBlocks245212.split_g,OMA.DyadicBlocks245212.split_w]
    exact ⟨by simpa only [mul_zero,zero_add] using ih.1.add ((powr u).mul gp),
      by simpa only [zero_mul,add_zero,one_mul,Nat.succ_mul] using
        ih.2.add ((powr u).mul (wp.add (dz.mul gp)))⟩

private theorem even_weight {p t : ℕ} (odd : Odd p) (tp : 0<t) (even : Even t) :
    ∃ h, val t=h+1 ∧ weight p t ≡ 2^h [MOD 2^(h+1)] ∧ 2^(h+1)∣geom p t := by
  obtain ⟨k,u,ou,eq⟩ := Nat.exists_eq_two_pow_mul_odd tp.ne'
  cases k with
  | zero => simp only [pow_zero,one_mul] at eq; exact (Nat.not_even_iff_odd.mpr ou (eq ▸ even)).elim
  | succ h =>
    have prod : t=u*2^(h+1) := eq.trans (mul_comm _ _)
    have vv : val t=h+1 := by
      have vu := val_odd ou
      unfold val at vu ⊢
      rw [prod,Nat.factorization_mul ou.pos.ne' (by positivity),Finsupp.add_apply,
        Nat.factorization_pow_self Nat.prime_two,vu,zero_add]
    have b := blocks p odd h u
    dsimp only at b
    have o : u ≡ 1 [MOD 2] := by simpa [Nat.ModEq] using Nat.odd_iff.mp ou
    have reduced : u*2^h ≡ 2^h [MOD 2^(h+1)] := by
      simpa [pow_succ,mul_comm] using o.mul_right' (2^h)
    exact ⟨h,vv,prod ▸ b.2.trans reduced,prod ▸ Nat.modEq_zero_iff_dvd.mp b.1⟩

private theorem weight_pos {p t : ℕ} (ht : 0<t) : 0<weight p t :=
  sum_pos' (fun _ _=>Nat.zero_le _) ⟨0,mem_range.mpr ht,by simp⟩

/-- The valuation depends only on the exponent, even when the odd prime varies. -/
theorem weight_local {p : ℕ} (hp : p.Prime) (odd : Odd p) (e : ℕ) :
    val (W (p^e))+1=val (e+1)+val (e+2) := by
  rw [w_pow hp]
  change val (weight p (e+1))+1=_
  rcases Nat.even_or_odd (e+1) with ev|od
  · obtain ⟨h,vv,ww,_⟩ := even_weight odd (by omega) ev
    have vo := val_odd (show Odd (e+2) from ev.add_one)
    rw [identify (weight_pos (by omega)) ww,vv,vo,Nat.add_zero]
  · have ev : Even (e+2) := od.add_one
    obtain ⟨h,vv,ww,_⟩ := even_weight odd (by omega) ev
    have d : 2^(h+1)∣e+2 := (Nat.prime_two.pow_dvd_iff_le_factorization (by omega : e+2≠0)).mpr vv.ge
    have off : p^(e+1)*(e+2) ≡ 0 [MOD 2^(h+1)] :=
      Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_right d _)
    have next : weight p (e+2) ≡ weight p (e+1) [MOD 2^(h+1)] := by
      dsimp only [weight]
      rw [sum_range_succ _ (e+1)]
      simpa only [weight,add_zero] using (Nat.ModEq.refl (weight p (e+1))).add off
    rw [identify (weight_pos (by omega)) (next.symm.trans ww),val_odd od,vv,zero_add]

theorem sigma_local {p : ℕ} (hp : p.Prime) (odd : Odd p) (e : ℕ) :
    2^val (e+1)∣ArithmeticFunction.sigma 1 (p^e) := by
  rcases Nat.even_or_odd (e+1) with ev|od
  · obtain ⟨_,vv,_,sg⟩ := even_weight (p:=p) odd (by omega) ev
    rw [ArithmeticFunction.sigma_one_apply_prime_pow hp,vv]; exact sg
  · simp [val_odd od]

end OMA.WeightVal245212

end

section

/- A base-independent two-adic obstruction for every number of odd primes. -/
namespace OMA.ExponentParity245212
open Finset Nat ArithmeticFunction OMA.Smooth245212 OMA.Abundance245212
  OMA.WeightVal245212
open scoped ArithmeticFunction.sigma Function

/-- In an equality with r distinct odd prime factors, the product of their
exponents plus two is divisible by 2^r. The power of two in n is unrestricted. -/
theorem exponent_product {ι : Type*} [Fintype ι] (p e : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (odd : ∀ i, Odd (p i)) (inj : Function.Injective p)
    (a : ℕ) (eq : OeisA245212.a (2^a*total p e) = (σ 1 (2^a*total p e) : ℤ)) :
    2^Fintype.card ι ∣ ∏ i, (e i+2) := by
  classical
  let z (i : ι) := p i^e i
  have cop : (↑(univ : Finset ι) : Set ι).Pairwise (Coprime on z) := by
    intro i _ j _ ne
    exact (((Nat.coprime_primes (hp i) (hp j)).mpr (fun h => ne (inj h))).pow_left _).pow_right _
  have co : (2^a).Coprime (total p e) := (Coprime.prod_right (fun i _ =>
    (Nat.coprime_two_left.mpr (odd i)).pow_right (e i))).pow_left _
  have zn : total p e ≠ 0 := prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hp i).ne_zero)
  have b := balance (mul_ne_zero (by positivity) zn) eq
  rw [w_mult.map_mul_of_coprime co,isMultiplicative_sigma.map_mul_of_coprime co,
    isMultiplicative_sigma.map_mul_of_coprime co] at b
  let T := ∑ i, WeightVal245212.val (e i+1)
  have sd : 2^T ∣ σ 1 (total p e) := by
    rw [show σ 1 (total p e) = ∏ i, σ 1 (z i) from
      IsMultiplicative.map_prod z (isMultiplicative_sigma (k:=1)) univ cop]
    dsimp only [T]
    rw [←prod_pow_eq_pow_sum]
    exact prod_dvd_prod_of_dvd _ _ (fun i _ => sigma_local (hp i) (odd i) (e i))
  have td : 2^T ∣ σ 0 (total p e) := by
    rw [show σ 0 (total p e) = ∏ i, σ 0 (z i) from
      IsMultiplicative.map_prod z (isMultiplicative_sigma (k:=0)) univ cop]
    dsimp only [T,z]
    simp only [sigma_zero_apply_prime_pow (hp _)]
    rw [←prod_pow_eq_pow_sum]
    exact prod_dvd_prod_of_dvd _ _ fun i _ =>
      (Nat.prime_two.pow_dvd_iff_le_factorization (by omega : e i+1≠0)).mpr le_rfl
  have wb : 2^T ∣ W (2^a)*W (total p e) := by
    apply (Nat.dvd_add_iff_left (dvd_mul_of_dvd_right sd (σ 1 (2^a)))).mpr
    rw [b]
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right td _) _
  have wd := ((Nat.coprime_two_left.mpr (OMA.DyadicPower245212.dyadic_odd a)).pow_left T).dvd_of_dvd_mul_left wb
  have wm := IsMultiplicative.map_prod z w_mult univ cop
  change W (total p e) = _ at wm
  rw [wm] at wd
  have wpos (i : ι) : W (z i) ≠ 0 := by
    rw [show z i=p i^e i from rfl,w_pow (hp i)]
    exact (sum_pos' (fun _ _ => Nat.zero_le _) ⟨0,mem_range.mpr (by omega),by simp⟩).ne'
  have lower := (Nat.prime_two.pow_dvd_iff_le_factorization
    (prod_ne_zero_iff.mpr (fun i _ => wpos i))).mp wd
  rw [Nat.factorization_prod_apply (fun i _ => wpos i)] at lower
  have allv := Finset.sum_congr (s₁:=univ) rfl (fun i _ => weight_local (hp i) (odd i) (e i))
  simp only [sum_add_distrib,sum_const,smul_eq_mul,mul_one] at allv
  change (∑ i, WeightVal245212.val (W (p i^e i))) + Fintype.card ι =
    (∑ i, WeightVal245212.val (e i+1)) + ∑ i, WeightVal245212.val (e i+2) at allv
  apply (Nat.prime_two.pow_dvd_iff_le_factorization
    (prod_ne_zero_iff.mpr (fun i _ => by omega : ∀ i ∈ univ, e i+2≠0))).mpr
  rw [Nat.factorization_prod_apply (fun i _ => by omega : ∀ i ∈ univ, e i+2≠0)]
  change (∑ i, WeightVal245212.val (e i+1)) ≤ ∑ i, WeightVal245212.val (W (p i^e i)) at lower
  change Fintype.card ι ≤ ∑ i, WeightVal245212.val (e i+2)
  omega

/-- A solution whose odd part is not square has an exponent equal to 2 mod 4. -/
theorem two_mod_four {ι : Type*} [Fintype ι] (p e : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (odd : ∀ i, Odd (p i)) (inj : Function.Injective p)
    (a : ℕ) (eq : OeisA245212.a (2^a*total p e) = (σ 1 (2^a*total p e) : ℤ))
    (nonsquare : ∃ i, Odd (e i)) : ∃ i, e i % 4 = 2 := by
  classical
  by_contra! no
  have lower := (Nat.prime_two.pow_dvd_iff_le_factorization
    (prod_ne_zero_iff.mpr (fun i _ => by omega : ∀ i ∈ univ, e i+2≠0))).mp
      (exponent_product p e hp odd inj a eq)
  rw [Nat.factorization_prod_apply (fun i _ => by omega : ∀ i ∈ univ, e i+2≠0)] at lower
  have upper (i : ι) : (e i+2).factorization 2 ≤ 1 := by
    have d : ¬ 2^2 ∣ e i+2 := by have := no i; norm_num; omega
    have := mt (Nat.prime_two.pow_dvd_iff_le_factorization (by omega : e i+2≠0)).mpr d
    omega
  obtain ⟨j,hj⟩ := nonsquare
  have zero : WeightVal245212.val (e j+2)=0 := val_odd (by
    rw [Nat.odd_iff] at hj ⊢; omega)
  have lt := Finset.sum_lt_sum (s:=univ) (fun i _ => upper i)
    ⟨j,mem_univ j,show (e j+2).factorization 2 < 1 by rw [show (e j+2).factorization 2=0 from zero]; decide⟩
  simpa using (not_lt_of_ge lower (by simpa using lt))

end OMA.ExponentParity245212

end

section

/- A bounded exceptional odd prime power in nonsquare A245212 solutions.
The rank of the odd part and the dyadic exponent are fixed, not its primes. -/
namespace OMA.BoundedAtom245212
open Finset Filter Topology Nat OMA.Smooth245212 OMA.SquareCompact245212
open OMA.WeightVal245212 (weight_local)
local notation "v₂" => OMA.WeightVal245212.val
open scoped ArithmeticFunction.sigma

/-- Away from exponents 2 mod 4 the factors of two in the numerator
can all be cancelled against the local divisor count. -/
theorem good_factor {p e : ℕ} (pr : Nat.Prime p) (op : Odd p) (good : e%4≠2) :
    OddNum (X p (some e)) := by
  let N := W (p^e)
  have np : 0<N := by
    dsimp [N]; rw [w_pow pr]
    exact sum_pos' (fun i _ => Nat.zero_le _) ⟨0,mem_range.mpr (Nat.succ_pos _),by simp⟩
  have small : v₂ (e+2)<2 := by
    by_contra! hi
    have x := (Nat.prime_two.pow_dvd_iff_le_factorization (by omega : e+2≠0)).mpr hi
    change 4 ∣ e+2 at x
    omega
  have vals := weight_local pr op e
  change v₂ N+1=v₂ (e+1)+v₂ (e+2) at vals
  obtain ⟨B,hB⟩ := (Nat.prime_two.pow_dvd_iff_le_factorization (Nat.succ_ne_zero e)).mpr
    (show v₂ N≤v₂ (e+1) by omega)
  let A := ordCompl[2] N
  have rep : 2^(v₂ N)*A=N := Nat.ordProj_mul_ordCompl_eq_self N 2
  have oa : Odd A := Nat.not_even_iff_odd.mp (fun h => Nat.not_dvd_ordCompl Nat.prime_two np.ne'
    (even_iff_two_dvd.mp h))
  have bp : 0<B := by
    by_contra! z
    have z' : B=0 := by omega
    simp [z'] at hB
  have raw := x_factor pr e
  change X p (some e)*(((e:ℚ)+1)*p^e)=(N:ℚ) at raw
  have br := congrArg (Nat.cast : ℕ → ℚ) hB
  have nr := congrArg (Nat.cast : ℕ → ℚ) rep
  push_cast at br nr
  refine ⟨A,B*p^e,oa,Nat.mul_pos bp (Nat.pow_pos pr.pos),?_⟩
  apply (eq_div_iff (by exact_mod_cast (Nat.mul_pos bp (Nat.pow_pos pr.pos)).ne')).mpr
  push_cast
  apply (mul_left_cancel₀ (by positivity : (2:ℚ)^(v₂ N)≠0))
  linear_combination raw - nr - (X p (some e)*(p:ℚ)^e)*br

private theorem product_odd {K : ℕ} (x : Fin K → ℚ) (ox : ∀ i,OddNum (x i)) :
    OddNum (∏ i,x i) := by
  have aux (s : Finset (Fin K)) : OddNum (∏ i∈s,x i) := by
    induction s using Finset.induction_on with
    | empty => simpa using OMA.SquareCompact245212.one
    | @insert i s hi ih => simpa only [prod_insert hi] using OMA.SquareCompact245212.mul (ox i) ih
  exact aux univ

/-- If some exponent grows past every bound, a prime and an exponent
2 mod 4 must both stay bounded in at least one coordinate. -/
theorem bounded_or_atom (K : ℕ) (c d : ℚ) (hc : OddNum c) (d0 : 0≤d) (d1 : d≤1) :
    ∃ B : ℕ, ∀ p e : Fin K → ℕ, (∀ i,Nat.Prime (p i)) → (∀ i,Odd (p i)) →
      c*(∏ i,X (p i) (some (e i)))+d*(∏ i,Y (p i) (some (e i)))=2 →
      (∀ i,e i≤B) ∨ ∃ i,e i%4=2 ∧ p i≤B ∧ e i≤B := by
  by_contra! bad
  choose p e hp ho eq large avoid using bad
  let seq (n : ℕ) := (p n,e n)
  obtain ⟨g,sorted⟩ := wellQuasiOrdered_le.exists_monotone_subseq seq
  have points (i : Fin K) : ∃ x : ℚ,OddNum x ∧
      Tendsto (fun n => X (p (g n) i) (some (e (g n) i))) atTop (𝓝 x) := by
    apply factor_limit_of_stable _ _ (fun _ _ le => (sorted _ _ le).1 i)
      (fun _ _ le => (sorted _ _ le).2 i) (fun n => hp (g n) i) (fun n => ho (g n) i)
    intro P E pP eE
    have eventuallyLarge := g.strictMono.tendsto_atTop.eventually (eventually_ge_atTop (max P E))
    obtain ⟨n,pn,en,gn⟩ := (pP.and (eE.and eventuallyLarge)).exists
    change p (g n) i=P at pn
    change e (g n) i=E at en
    apply good_factor (pn ▸ hp (g n) i) (pn ▸ ho (g n) i)
    intro badE
    have stop := avoid (g n) i
    rw [pn,en] at stop
    exact (not_lt_of_ge ((le_max_right P E).trans gn)) (stop badE ((le_max_left P E).trans gn))
  choose x ox conv using points
  have limit := (tendsto_finsetProd univ (fun i _ => conv i)).const_mul c
  have notTwo := ne_two (OMA.SquareCompact245212.mul hc (product_odd x ox))
  apply notTwo
  apply tendsto_nhds_unique limit
  suffices total : Tendsto (fun n => c*∏ i,X (p n i) (some (e n i))) atTop (𝓝 2) from
    total.comp g.strictMono.tendsto_atTop
  have error (n : ℕ) : 0 ≤ d*∏ i,Y (p n i) (some (e n i)) ∧
      d*(∏ i,Y (p n i) (some (e n i))) ≤ 2/((n:ℚ)+1) := by
    have y0 (j) := y_nonneg (hp n j).one_lt (some (e n j))
    have pos := prod_nonneg (s:=univ) (fun j _ => y0 j)
    refine ⟨mul_nonneg d0 pos,?_⟩
    obtain ⟨i,gi⟩ := large n
    calc
      _ ≤ ∏ j,Y (p n j) (some (e n j)) := mul_le_of_le_one_left pos d1
      _ ≤ Y (p n i) (some (e n i)) := by
        rw [←prod_erase_mul _ _ (mem_univ i)]
        exact mul_le_of_le_one_left (y0 i) (prod_le_one (fun j _ => y0 j) (fun j _ => y_one (hp n j).one_lt _))
      _ ≤ 2/((e n i:ℚ)+1) := ((lt_div_iff₀ (by positivity)).mpr (OMA.CapOrder245212.y_short (hp n i) _)).le
      _ ≤ _ := by gcongr
  have zero : Tendsto (fun n : ℕ => 2/((n:ℚ)+1)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℚ)).const_mul 2
  have err := tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds zero
    (fun n => (error n).1) (fun n => (error n).2)
  apply (show Tendsto (fun n => 2-d*∏ i,Y (p n i) (some (e n i))) atTop (𝓝 2) by
    simpa using (tendsto_const_nhds (x:=(2:ℚ))).sub err).congr
  intro n; linarith only [eq n]

private theorem atom_in_box (K : ℕ) (c d : ℚ) (hc : OddNum c) (d0 : 0<d) (d1 : d≤1) :
    ∃ B : ℕ, ∀ p e : Fin K → ℕ, (∀ i,Nat.Prime (p i)) → (∀ i,Odd (p i)) →
      (∀ i,0<e i) → (∃ i,e i%4=2) →
      c*(∏ i,X (p i) (some (e i)))+d*(∏ i,Y (p i) (some (e i)))=2 →
      ∃ i,e i%4=2 ∧ p i≤B ∧ e i≤B := by
  classical
  obtain ⟨L,alt⟩ := bounded_or_atom K c d hc d0.le d1
  let F : Set (Fin K → ℕ) := {e | ∀ i,0<e i ∧ e i≤L}
  let bases (e : Fin K → ℕ) : Set (Fin K → ℕ) := {p | (∀ i,Nat.Prime (p i)) ∧
    c*(∏ i,X (p i) (some (e i)))+d*(∏ i,Y (p i) (some (e i)))=2}
  have cf : F.Finite := (Set.Finite.pi' (fun _ : Fin K => Set.finite_Iic L)).subset
    (fun _ h i => (h i).2)
  have c0 : 0≤c := by obtain ⟨A,B,_,_,rfl⟩ := hc; positivity
  have bf := cf.biUnion (fun e he => (show (bases e).Finite from
    OMA.FixedExponents245212.finite_bases e (fun i => (he i).1) c d 2 c0 d0))
  have vals := bf.biUnion (fun p _ => Set.finite_range p)
  obtain ⟨M,cap⟩ := vals.bddAbove
  refine ⟨max L M,?_⟩
  intro p e hp ho ep has eq
  rcases alt p e hp ho eq with low | ⟨i,good,pi,ei⟩
  · obtain ⟨i,good⟩ := has
    have ef : e∈F := fun j => ⟨ep j,low j⟩
    have member : p∈⋃ t∈F,bases t := Set.mem_iUnion₂.mpr ⟨e,ef,hp,eq⟩
    have pm := cap (Set.mem_iUnion₂.mpr ⟨p,member,i,rfl⟩)
    exact ⟨i,good,pm.trans (le_max_right _ _),(low i).trans (le_max_left _ _)⟩
  · exact ⟨i,good,pi.trans (le_max_left _ _),ei.trans (le_max_left _ _)⟩

/-- Include the dyadic prime in the normalized equality and then separate
it back out; p and e describe only the odd factors. -/
theorem normalized_dyadic {K : ℕ} (k : ℕ) (p e : Fin K → ℕ) (hp : ∀ i,Nat.Prime (p i))
    (op : ∀ i,Odd (p i)) (inj : p.Injective)
    (eq : OeisA245212.a (2^k*total p e)=(σ 1 (2^k*total p e):ℤ)) :
    X 2 (some k)*(∏ i,X (p i) (some (e i)))+
      Y 2 (some k)*(∏ i,Y (p i) (some (e i)))=2 := by
  let P : Fin (K+1) → ℕ := Fin.cons 2 p
  let E : Fin (K+1) → ℕ := Fin.cons k e
  have prime : ∀ i,Nat.Prime (P i) := Fin.cases Nat.prime_two hp
  have distinct : P.Injective := Fin.cons_injective_of_injective (by
    rintro ⟨i,hi⟩; have h := op i; rw [hi] at h; norm_num [Nat.odd_iff] at h) inj
  have all : total P E=2^k*total p e := by
    rw [total,Fin.prod_univ_succ]; rfl
  have norm := normalized_of_eq P prime distinct E (by rw [all]; exact eq)
  unfold normalized at norm
  rw [Fin.prod_univ_succ (fun i => X (P i) (some (E i))),
    Fin.prod_univ_succ (fun i => Y (P i) (some (E i)))] at norm
  exact norm

private theorem exact_rank (k K : ℕ) :
    ∃ L : ℕ, ∀ m : ℕ, Odd m → ¬IsSquare m → m.primeFactors.card=K →
    OeisA245212.a (2^k*m)=(σ 1 (2^k*m):ℤ) →
    ∃ q∈m.primeFactors,m.factorization q%4=2 ∧ q≤L ∧ m.factorization q≤L := by
  classical
  let c := X 2 (some k)
  let d := Y 2 (some k)
  have hc : OddNum c := quotient Nat.prime_two (OMA.DyadicPower245212.dyadic_odd k)
  have dp : 0<d := by
    dsimp [d]; rw [y_avg (by decide : 1<2)]
    exact div_pos (sum_pos' (fun i _ => by positivity) ⟨0,by simp,by simp⟩) (by positivity)
  obtain ⟨L,cap⟩ := atom_in_box K c d hc dp (y_one (by decide) _)
  refine ⟨L,?_⟩
  intro m odd nonsq card eq
  let S := m.primeFactors
  let p := S.orderEmbOfFin card
  let e (i : Fin K) := m.factorization (p i)
  have mem (i) : p i∈m.primeFactors := orderEmbOfFin_mem S card i
  have hp (i) := Nat.prime_of_mem_primeFactors (mem i)
  have op (i) := Nat.coprime_two_left.mp ((Nat.coprime_two_left.mpr odd).of_dvd_right
    (Nat.dvd_of_mem_primeFactors (mem i)))
  have ep (i) : 0<e i := (hp i).factorization_pos_of_dvd odd.pos.ne' (Nat.dvd_of_mem_primeFactors (mem i))
  have repr : total p e=m := by
    exact (Fintype.prod_equiv (S.orderIsoOfFin card).toEquiv _
      (fun j : S => j.val^(m.factorization j.val)) (fun _ => rfl)).trans
      (Nat.prod_primeFactors_coe_pow_factorization odd.pos.ne').symm
  have ex : ∃ i,Odd (e i) := by
    by_contra! no
    have even (i) := Nat.not_odd_iff_even.mp (no i)
    choose f hf using even
    apply nonsq
    refine ⟨∏ i,p i^f i,?_⟩
    rw [←repr,total,←prod_mul_distrib]
    exact prod_congr rfl fun i _ => by rw [hf i,pow_add]
  have has := OMA.ExponentParity245212.two_mod_four p e hp op p.injective k (by rw [repr];exact eq) ex
  have norm := normalized_dyadic k p e hp op p.injective (by rw [repr]; exact eq)
  obtain ⟨i,bad,pi,ei⟩ := cap p e hp op ep has norm
  exact ⟨p i,mem i,bad,pi,ei⟩

/-- Fixing the power of two and the number of distinct odd primes, every
nonsquare odd core at equality is divisible exactly by one of a finite list
of prime powers whose exponents are 2 mod 4. Other exponents are unrestricted. -/
theorem bounded_atom (k K : ℕ) :
    ∃ B : ℕ, ∀ m : ℕ, Odd m → ¬IsSquare m → m.primeFactors.card≤K →
    OeisA245212.a (2^k*m)=(σ 1 (2^k*m):ℤ) →
    ∃ q∈m.primeFactors,m.factorization q%4=2 ∧ q≤B ∧ m.factorization q≤B := by
  choose L hL using exact_rank k
  refine ⟨∑ j∈range (K+1),L j,?_⟩
  intro m om ns hc eq
  obtain ⟨q,hq,pq,ql,el⟩ := hL m.primeFactors.card m om ns rfl eq
  have bound := single_le_sum (f:=L) (fun j _ => Nat.zero_le (L j)) (mem_range.mpr (Nat.lt_succ_of_le hc))
  exact ⟨q,hq,pq,ql.trans bound,el.trans bound⟩

#print axioms bounded_atom
end OMA.BoundedAtom245212

end

section

/- Finiteness at bounded rank when the finite odd prime-power factors
cannot cancel the full dyadic denominator of the weighted factor at two. -/
namespace OMA.ParityBudget245212
open Nat Finset Filter Topology OMA.Smooth245212 OMA.SquareCompact245212
open scoped ArithmeticFunction.sigma
open OMA.SquareCompact245212 (infinite_factor)
local notation "v₂" => OMA.WeightVal245212.val

private theorem odd_fraction {N D : ℕ} (nz : 0<N) (dz : 0<D) (dv : 2^(v₂ N)∣D) :
    OddNum ((N:ℚ)/D) := by
  obtain ⟨B,db⟩ := dv
  let A := ordCompl[2] N
  have na : 2^(v₂ N)*A=N := Nat.ordProj_mul_ordCompl_eq_self N 2
  have oa : Odd A := Nat.not_even_iff_odd.mp (fun h =>
    Nat.not_dvd_ordCompl Nat.prime_two nz.ne' (even_iff_two_dvd.mp h))
  have bp : 0<B := by
    by_contra! neg
    have zero : B=0 := by omega
    rw [db,zero,mul_zero] at dz
    omega
  refine ⟨A,B,oa,bp,?_⟩
  rw [←na,db]
  push_cast; field_simp

private theorem scale_down {x : ℚ} (ox : OddNum x) (w : ℕ) : OddNum (x/(2:ℚ)^w) := by
  obtain ⟨A,B,odd,bp,rfl⟩ := ox
  exact ⟨A,B*2^w,odd,Nat.mul_pos bp (Nat.two_pow_pos _),by push_cast; ring⟩

/-- Each odd prime contributes at most this many factors of two to the
reduced numerator of the local weighted ratio. -/
def excess (e : ℕ) := v₂ (e+2)-1

private theorem scale_local {p e w : ℕ} (pr : p.Prime) (op : Odd p) (hw : excess e≤w) :
    OddNum (X p (some e)/(2:ℚ)^w) := by
  let N := W (p^e)
  let D := (e+1)*p^e*2^w
  have np : 0<N := by
    dsimp [N]; rw [w_pow pr]
    exact sum_pos' (fun i _ => Nat.zero_le _) ⟨0,mem_range.mpr (Nat.succ_pos _),by simp⟩
  have dp : 0<D := by dsimp [D]; have := pr.pos; positivity
  have ord := OMA.WeightVal245212.weight_local pr op e
  change v₂ N+1=v₂ (e+1)+v₂ (e+2) at ord
  have inc : v₂ N≤v₂ (e+1)+w := by unfold excess at hw; omega
  have divides : 2^(v₂ N)∣D := by
    apply (pow_dvd_pow 2 inc).trans
    rw [pow_add]
    have dv := Nat.ordProj_dvd (e+1) 2
    exact mul_dvd_mul (dvd_mul_of_dvd_left dv (p^e)) (dvd_refl _)
  have ofrac := odd_fraction np dp divides
  have fx := x_factor pr e
  have eqx : X p (some e)=(N:ℚ)/(((e:ℚ)+1)*p^e) := by
    apply (eq_div_iff (by
      have pos : (0:ℚ)<p := by exact_mod_cast pr.pos
      positivity)).mpr
    exact fx
  rw [eqx,div_div]
  simpa [D] using ofrac

private theorem scaled_coefficient {k b : ℕ} (low : b≤k+v₂ (k+1)) :
    OddNum (X 2 (some k)*(2:ℚ)^b) := by
  let D := (k+1)*2^k
  have dv : 2^b∣D := by
    apply (pow_dvd_pow 2 low).trans
    rw [pow_add,Nat.mul_comm]
    exact mul_dvd_mul (Nat.ordProj_dvd (k+1) 2) (dvd_refl _)
  obtain ⟨B,db⟩ := dv
  have dp : 0<D := by dsimp [D]; positivity
  have bp : 0<B := by
    by_contra! neg
    have z : B=0 := by omega
    rw [db,z,mul_zero] at dp
    omega
  have fx := x_factor Nat.prime_two k
  have bd := congrArg (Nat.cast : ℕ → ℚ) db
  dsimp only [D] at bd
  push_cast at bd
  refine ⟨W (2^k),B,OMA.DyadicPower245212.dyadic_odd k,bp,?_⟩
  apply (eq_div_iff (by exact_mod_cast bp.ne' : (B:ℚ)≠0)).mpr
  linear_combination fx - X 2 (some k)*bd

/-- Only count dyadic excess carried by an exactly bounded base and exponent. -/
def visible (B p e : ℕ) := if p≤B ∧ e≤B then excess e else 0

private theorem visible_gap (k K : ℕ) :
    ∃ B : ℕ, ∃ δ : ℚ, 0<δ ∧ ∀ p e : Fin K → ℕ, (∀ i,Nat.Prime (p i)) → (∀ i,Odd (p i)) →
      (∑ i,visible B (p i) (e i))≤k+v₂ (k+1) →
      δ≤|X 2 (some k)*(∏ i,X (p i) (some (e i)))-2| := by
  by_contra! bad
  have pick (n : ℕ) := bad n (1/((n:ℚ)+1)) (by positivity)
  choose p e hp ho he close using pick
  let seq (n : ℕ) := (p n,e n)
  obtain ⟨g,sorted⟩ := wellQuasiOrdered_le.exists_monotone_subseq seq
  let Capture (i : Fin K) (x : ℚ) := ∃ w : ℕ, OddNum (x/(2:ℚ)^w) ∧
    ∀ᶠ n in atTop,w≤visible (g n) (p (g n) i) (e (g n) i)
  have points (i : Fin K) : ∃ x : ℚ,Capture i x ∧
      Tendsto (fun n => X (p (g n) i) (some (e (g n) i))) atTop (𝓝 x) := by
    have trivialWeight (x : ℚ) (hx : OddNum x) : Capture i x :=
      ⟨0,by simpa using hx,Eventually.of_forall fun _ => Nat.zero_le _⟩
    apply factor_limit_by (Capture i) _ _
      (fun _ _ le => (sorted _ _ le).1 i) (fun _ _ le => (sorted _ _ le).2 i)
      (fun n => hp (g n) i) (fun n => ho (g n) i) (trivialWeight _ OMA.SquareCompact245212.one)
      (fun _ pr op => trivialWeight _ (OMA.SquareCompact245212.infinite_factor pr op))
    intro P E pP eE
    obtain ⟨n,pn,en⟩ := (pP.and eE).exists
    change p (g n) i=P at pn
    refine ⟨excess E,scale_local (pn ▸ hp (g n) i) (pn ▸ ho (g n) i) le_rfl,?_⟩
    have large := g.strictMono.tendsto_atTop.eventually (eventually_ge_atTop (max P E))
    filter_upwards [pP,eE,large] with j pj ej big
    change p (g j) i=P at pj
    change e (g j) i=E at ej
    simp [visible,pj,ej,(le_max_left P E).trans big,(le_max_right P E).trans big]
  choose x capture conv using points
  choose w ox see using capture
  obtain ⟨n,hn⟩ := (Filter.eventually_all.mpr see).exists
  have low := (sum_le_sum (s:=univ) (fun i _ => hn i)).trans (he (g n))
  have prod (s : Finset (Fin K)) : OddNum (∏ i∈s,x i/(2:ℚ)^(w i)) := by
    induction s using Finset.induction_on with
    | empty => simpa using OMA.SquareCompact245212.one
    | @insert i s hi ih => simpa only [prod_insert hi] using OMA.SquareCompact245212.mul (ox i) ih
  have od := OMA.SquareCompact245212.mul (scaled_coefficient low) (prod univ)
  rw [prod_div_distrib,prod_pow_eq_pow_sum] at od
  let c := X 2 (some k)
  have distinct := ne_two (show OddNum (c*∏ i,x i) by
    dsimp only [c]; convert od using 1; field_simp)
  have limit := (tendsto_finsetProd univ (fun i _ => conv i)).const_mul c
  have t2 : Tendsto (fun n => c*∏ i,X (p n i) (some (e n i))) atTop (𝓝 2) := by
    have hz := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℚ)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (show Tendsto (fun n : ℕ => 2-1/((n:ℚ)+1)) atTop (𝓝 2) by simpa using tendsto_const_nhds.sub hz)
      (show Tendsto (fun n : ℕ => 2+1/((n:ℚ)+1)) atTop (𝓝 2) by simpa using hz.const_add 2)
    · intro n; linarith only [(abs_lt.mp (close n)).1]
    · intro n; linarith only [(abs_lt.mp (close n)).2]
  exact distinct (tendsto_nhds_unique limit (t2.comp g.strictMono.tendsto_atTop))

private def Config {K : ℕ} (c d : ℚ) (B H : ℕ)
    (v : (Fin K → ℕ) × (Fin K → ℕ)) :=
  (∀ i,Nat.Prime (v.1 i)) ∧ (∀ i,Odd (v.1 i)) ∧ (∀ i,0<v.2 i) ∧
  (∑ i,visible B (v.1 i) (v.2 i))≤H ∧
  c*(∏ i,X (v.1 i) (some (v.2 i)))+d*(∏ i,Y (v.1 i) (some (v.2 i)))=2

private theorem configs (K k : ℕ) (d : ℚ) (d0 : 0<d) (d1 : d≤1) :
    ∃ B, {v | Config (K:=K) (X 2 (some k)) d B (k+v₂ (k+1)) v}.Finite := by
  let c := X 2 (some k)
  have c0 := x_nonneg (by decide : 1<2) (some k)
  obtain ⟨B,δ,hδ,sep⟩ := visible_gap k K
  refine ⟨B,?_⟩
  obtain ⟨L,hL⟩ := exists_nat_gt (2/δ)
  have size (p e : Fin K → ℕ) (cfg : Config c d B (k+v₂ (k+1)) (p,e)) (i : Fin K) : e i<L := by
    obtain ⟨hp,ho,_,he,eq⟩ := cfg
    have bound := sep p e hp ho he
    change δ≤|c*(∏ j,X (p j) (some (e j)))-2| at bound
    have y0 (j) := y_nonneg (hp j).one_lt (some (e j))
    have yp := prod_nonneg (s:=univ) (fun j _ => y0 j)
    have z := mul_nonneg d0.le yp
    change c*(∏ j,X (p j) (some (e j)))+d*(∏ j,Y (p j) (some (e j)))=2 at eq
    rw [abs_of_nonpos (by linarith only [eq,z])] at bound
    have upper : δ≤Y (p i) (some (e i)) := by
      apply (show δ≤d*∏ j,Y (p j) (some (e j)) by linarith only [eq,bound]).trans
      apply (mul_le_of_le_one_left yp d1).trans
      rw [←prod_erase_mul _ _ (mem_univ i)]
      exact mul_le_of_le_one_left (y0 i) (prod_le_one (fun j _ => y0 j)
        (fun j _ => y_one (hp j).one_lt _))
    have hh := OMA.CapOrder245212.y_short (hp i) (e i)
    have mult := mul_le_mul_of_nonneg_right upper (show 0≤(e i:ℚ)+1 by positivity)
    have le : (e i:ℚ)<2/δ := (lt_div_iff₀ hδ).mpr (by linarith only [hh,mult,hδ])
    exact_mod_cast le.trans hL
  apply Set.Finite.of_finite_fibers Prod.snd
  · apply (Set.Finite.pi' (fun _ : Fin K => Set.finite_Iio L)).subset
    rintro e ⟨⟨p,v⟩,h,rfl⟩
    exact size _ _ h
  · rintro e ⟨⟨p,v⟩,cfg,rfl⟩
    have finite := OMA.FixedExponents245212.finite_bases v cfg.2.2.1 c d 2 c0 d0
    apply (finite.image (fun q => (q,v))).subset
    rintro ⟨q,f⟩ ⟨hf,hv⟩
    have same : f=v := hv
    subst f
    exact ⟨q,⟨hf.1,hf.2.2.2.2⟩,rfl⟩

private theorem rank_finite (k K : ℕ) :
    ∃ B : ℕ,{m : ℕ | Odd m ∧ m.primeFactors.card=K ∧
      (∑ q∈m.primeFactors,visible B q (m.factorization q))≤k+v₂ (k+1) ∧
      OeisA245212.a (2^k*m)=(σ 1 (2^k*m):ℤ)}.Finite := by
  classical
  let c := X 2 (some k)
  let d := Y 2 (some k)
  have dp : 0<d := by
    dsimp [d]; rw [y_avg (by decide : 1<2)]
    exact div_pos (sum_pos' (fun i _ => by positivity) ⟨0,by simp,by simp⟩) (by positivity)
  obtain ⟨B,fin⟩ := configs K k d dp (y_one (by decide) _)
  refine ⟨B,?_⟩
  apply (fin.image (fun v => total v.1 v.2)).subset
  rintro m ⟨om,card,budget,eq⟩
  let S := m.primeFactors
  let p := S.orderEmbOfFin card
  let e (i : Fin K) := m.factorization (p i)
  have mem (i) : p i∈m.primeFactors := orderEmbOfFin_mem S card i
  have hp (i) := Nat.prime_of_mem_primeFactors (mem i)
  have op (i) := Nat.coprime_two_left.mp ((Nat.coprime_two_left.mpr om).of_dvd_right
    (Nat.dvd_of_mem_primeFactors (mem i)))
  have ep (i) := (hp i).factorization_pos_of_dvd om.pos.ne' (Nat.dvd_of_mem_primeFactors (mem i))
  have repr : total p e=m := by
    exact (Fintype.prod_equiv (S.orderIsoOfFin card).toEquiv _
      (fun j : S => j.val^(m.factorization j.val)) (fun _ => rfl)).trans
      (Nat.prod_primeFactors_coe_pow_factorization om.pos.ne').symm
  let w (i : Fin K) := visible B (p i) (e i)
  have wsum : ∑ i,w i = ∑ q∈m.primeFactors,visible B q (m.factorization q) := by
    exact (Fintype.sum_equiv (S.orderIsoOfFin card).toEquiv _
      (fun j : S => visible B j.val (m.factorization j.val)) (fun _ => rfl)).trans
      (Finset.sum_coe_sort S (fun q => visible B q (m.factorization q)))
  have norm := OMA.BoundedAtom245212.normalized_dyadic k p e hp op p.injective (by rw [repr];exact eq)
  exact ⟨(p,e),⟨hp,op,ep,wsum.le.trans budget,norm⟩,repr⟩

/-- Apart from finitely many solutions, bounded exceptional prime powers
must together supply enough powers of two for the fixed dyadic coefficient.
Large primes and large exponents do not count towards the required sum. -/
theorem finite_visible_budget (k K : ℕ) :
    ∃ B : ℕ,{m : ℕ | Odd m ∧ m.primeFactors.card≤K ∧
      (∑ q∈m.primeFactors,visible B q (m.factorization q))≤k+v₂ (k+1) ∧
      OeisA245212.a (2^k*m)=(σ 1 (2^k*m):ℤ)}.Finite := by
  choose L fin using rank_finite k
  let B := ∑ j∈range (K+1),L j
  refine ⟨B,((Set.finite_Iic K).biUnion (fun j _ => fin j)).subset ?_⟩
  rintro m ⟨om,card,v,eq⟩
  refine Set.mem_iUnion₂.mpr ⟨m.primeFactors.card,card,om,rfl,?_,eq⟩
  have less : L m.primeFactors.card≤B := single_le_sum (fun j _ => Nat.zero_le (L j))
    (mem_range.mpr (Nat.lt_succ_of_le card))
  apply (sum_le_sum (s:=m.primeFactors) (f:=fun q => visible (L m.primeFactors.card) q (m.factorization q))
    (g:=fun q => visible B q (m.factorization q)) ?_).trans v
  intro q hq
  unfold visible
  split_ifs <;> omega

/-- No upper bound on any prime or any individual exponent: only finitely
many positive odd parts with bounded rank and bounded total dyadic excess
can satisfy the original equality, for each fixed power of two. -/
theorem finite_budget (k K : ℕ) :
    {m : ℕ | Odd m ∧ m.primeFactors.card≤K ∧
      (∑ q∈m.primeFactors,excess (m.factorization q))≤k+v₂ (k+1) ∧
      OeisA245212.a (2^k*m)=(σ 1 (2^k*m):ℤ)}.Finite := by
  obtain ⟨B,fin⟩ := finite_visible_budget k K
  apply fin.subset
  rintro m ⟨om,card,v,eq⟩
  exact ⟨om,card,(sum_le_sum (fun q _ => show visible B q (m.factorization q)≤_ by
    unfold visible; split_ifs <;> omega)).trans v,eq⟩

#print axioms finite_budget
#print axioms finite_visible_budget
end OMA.ParityBudget245212

end

section

/- A single bounded odd factor supplying the dyadic excess prevents
resonance with any coprime product of Euler numerators. -/
namespace OMA.RankThreeAnchor245212
open Nat Finset ArithmeticFunction OMA.Smooth245212
open scoped ArithmeticFunction.sigma

private theorem dyadic_weight (k : ℕ) : W (2^k)=k*2^(k+1)+1 := by
  rw [w_pow Nat.prime_two]
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [sum_range_succ _ (k+1),ih,pow_succ (2:ℕ) (k+1)]
    ring

private theorem weight_unit {r : ℕ} (pr : r.Prime) (a : ℕ) : r.Coprime (W (r^a)) := by
  apply pr.coprime_iff_not_dvd.mpr
  intro dv
  let : Fact r.Prime := ⟨pr⟩
  have zero := (ZMod.natCast_eq_zero_iff (W (r^a)) r).mpr dv
  rw [w_pow pr,sum_range_succ'] at zero
  push_cast at zero
  simp [pow_succ] at zero

theorem high {k r a : ℕ} (hr : 2 ≤ r)
    (hex : k + OMA.WeightVal245212.val (k+1) < OMA.ParityBudget245212.excess a) :
    W (2^k) < r^a := by
  have hv : k+2 ≤ (a+2).factorization 2 := by
    unfold OMA.ParityBudget245212.excess OMA.WeightVal245212.val at hex; omega
  have dv : 2^(k+2) ∣ a+2 := (pow_dvd_pow _ hv).trans (Nat.ordProj_dvd (a+2) 2)
  have bound := Nat.le_of_dvd (by omega : 0 < a+2) dv
  have size (j : ℕ) : 2*j+4 ≤ 2^(j+2) := by
    induction j with
    | zero => decide
    | succ j ih => rw [pow_succ 2 (j+2)]; omega
  have exp : 2*(k+1) ≤ a := by have := size k; omega
  have power := (Nat.pow_le_pow_right (by decide : 0<2) exp).trans (Nat.pow_le_pow_left hr a)
  apply lt_of_lt_of_le _ power
  rw [dyadic_weight,show 2*(k+1)=(k+1)+(k+1) by omega,pow_add 2 (k+1) (k+1)]
  have inc : k+1 < 2^(k+1) := Nat.lt_two_pow_self
  have gap := Nat.mul_le_mul_right (2^(k+1)) inc
  have nz := Nat.two_pow_pos (k+1)
  nlinarith only [gap,nz,inc]

/-- The Euler numerator U may contain any number of other primes. -/
theorem no_resonance {k r a U V : ℕ} (pr : r.Prime) (odd : r≠2)
    (cop : r.Coprime U) (large : W (2^k) < r^a) :
    W (2^k*r^a)*U ≠ 2*(2^k*r^a)*(σ 0 (2^k*r^a))*V := by
  intro eq
  have base := ((Nat.coprime_primes Nat.prime_two pr).mpr odd.symm).pow_left k
  rw [w_mult.map_mul_of_coprime (base.pow_right a),mul_assoc] at eq
  have d : r^a ∣ 2*(2^k*r^a)*(σ 0 (2^k*r^a))*V := by
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_mul_left _ _) _) _) _
  have fac := ((weight_unit pr a).mul_right cop).pow_left a
  have divides : r^a ∣ W (2^k) := fac.dvd_of_dvd_mul_right (eq ▸ d)
  have pos : 0 < W (2^k) := by rw [dyadic_weight]; omega
  exact large.not_ge (Nat.le_of_dvd pos divides)

#print axioms high
#print axioms no_resonance
end OMA.RankThreeAnchor245212

end

section

/- A cofactor whose prime-power denominator survives in the weighted
moment forces another bounded prime and exponent in any fixed-rank extension. -/
namespace OMA.CohortAtom245212
open Nat Finset Filter Topology OMA.Smooth245212 OMA.SquareCompact245212
open scoped ArithmeticFunction.sigma

private def UnitNum (r : ℕ) (x : ℚ) := ∃ U V : ℕ, r.Coprime U ∧ 0<V ∧ x=(U:ℚ)/V

private theorem one (r : ℕ) : UnitNum r 1 := ⟨1,1,by simp,by decide,by norm_num⟩

private theorem mul {r : ℕ} {x y : ℚ} (ux : UnitNum r x) (uy : UnitNum r y) : UnitNum r (x*y) := by
  obtain ⟨A,B,ca,hb,rfl⟩ := ux
  obtain ⟨U,V,cu,hv,rfl⟩ := uy
  exact ⟨A*U,B*V,ca.mul_right cu,Nat.mul_pos hb hv,by push_cast; ring⟩

private theorem cap {r p : ℕ} (pr : p.Prime) (cop : r.Coprime p) : UnitNum r (X p none) := by
  refine ⟨p,p-1,cop,by have := pr.one_lt; omega,?_⟩
  have pp : (1:ℚ)<p := by exact_mod_cast pr.one_lt
  simp only [X,Y,sub_zero,Nat.cast_sub pr.one_le,Nat.cast_one]
  field_simp [show (p:ℚ)-1≠0 by linarith]; ring

private theorem product {K r : ℕ} (x : Fin K → ℚ) (unit : ∀ i,UnitNum r (x i)) :
    UnitNum r (∏ i,x i) := by
  have aux (s : Finset (Fin K)) : UnitNum r (∏ i∈s,x i) := by
    induction s using Finset.induction_on with
    | empty => simpa using one r
    | @insert i s hi ih => simpa only [prod_insert hi] using mul (unit i) ih
  exact aux univ

theorem at_two {K : ℕ} (c d : ℚ) (d0 : 0≤d) (d1 : d≤1)
    (p e : ℕ → Fin K → ℕ) (hp : ∀ n i,Nat.Prime (p n i)) (large : ∀ n,∃ i,n<e n i)
    (eqn : ∀ n,c*(∏ i,X (p n i) (some (e n i)))+d*(∏ i,Y (p n i) (some (e n i)))=2) :
    Tendsto (fun n => c*∏ i,X (p n i) (some (e n i))) atTop (𝓝 2) := by
  have error (n : ℕ) : 0 ≤ d*∏ i,Y (p n i) (some (e n i)) ∧
      d*(∏ i,Y (p n i) (some (e n i))) ≤ 2/((n:ℚ)+1) := by
    have y0 (j) := y_nonneg (hp n j).one_lt (some (e n j))
    have pos := prod_nonneg (s:=univ) (fun j _ => y0 j)
    obtain ⟨i,gi⟩ := large n
    refine ⟨mul_nonneg d0 pos,(mul_le_of_le_one_left pos d1).trans ?_⟩
    calc
      _ ≤ Y (p n i) (some (e n i)) := by
        rw [←prod_erase_mul _ _ (mem_univ i)]
        exact mul_le_of_le_one_left (y0 i) (prod_le_one (fun j _ => y0 j) (fun j _ => y_one (hp n j).one_lt _))
      _ ≤ 2/((e n i:ℚ)+1) := ((lt_div_iff₀ (by positivity)).mpr (OMA.CapOrder245212.y_short (hp n i) _)).le
      _ ≤ _ := by gcongr
  have zero : Tendsto (fun n : ℕ => 2/((n:ℚ)+1)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℚ)).const_mul 2
  have err := tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds zero
    (fun n => (error n).1) (fun n => (error n).2)
  apply (show Tendsto (fun n => 2-d*∏ i,Y (p n i) (some (e n i))) atTop (𝓝 2) by
    simpa using (tendsto_const_nhds (x:=(2:ℚ))).sub err).congr
  intro n; linarith only [eqn n]

/-- Either all exponents are bounded, or at least one entire prime-power
factor has its base and exponent simultaneously bounded. -/
theorem alternative (K r : ℕ) (c d : ℚ) (d0 : 0≤d) (d1 : d≤1)
    (miss : ∀ U V : ℕ,r.Coprime U → 0<V → c*((U:ℚ)/V)≠2) :
    ∃ B : ℕ, ∀ p e : Fin K → ℕ, (∀ i,Nat.Prime (p i)) → (∀ i,Odd (p i)) → (∀ i,r.Coprime (p i)) →
      c*(∏ i,X (p i) (some (e i)))+d*(∏ i,Y (p i) (some (e i)))=2 →
      (∀ i,e i≤B) ∨ ∃ i,p i≤B ∧ e i≤B := by
  by_contra! bad
  choose p e hp ho cop eqn large avoid using bad
  let seq (n : ℕ) := (p n,e n)
  obtain ⟨g,sorted⟩ := wellQuasiOrdered_le.exists_monotone_subseq seq
  have points (i : Fin K) : ∃ x : ℚ,UnitNum r x ∧
      Tendsto (fun n => X (p (g n) i) (some (e (g n) i))) atTop (𝓝 x) := by
    apply factor_limit_restricted _ _ _ (fun _ _ le => (sorted _ _ le).1 i)
      (fun _ _ le => (sorted _ _ le).2 i) (fun n => hp (g n) i) (fun n => ho (g n) i) (one r)
    · intro P pr _ hP
      obtain ⟨n,hn⟩ := hP.exists
      exact cap pr (hn ▸ cop (g n) i)
    · intro P E hP hE
      have big := g.strictMono.tendsto_atTop.eventually (eventually_ge_atTop (max P E))
      obtain ⟨n,pn,en,gn⟩ := (hP.and (hE.and big)).exists
      change p (g n) i=P at pn
      change e (g n) i=E at en
      have a := avoid (g n) i
      rw [pn,en] at a
      exact False.elim ((not_lt_of_ge ((le_max_right P E).trans gn)) (a ((le_max_left P E).trans gn)))
  choose x ox conv using points
  obtain ⟨U,V,unit,vpos,prod⟩ := product x ox
  have limit := (tendsto_finsetProd univ (fun i _ => conv i)).const_mul c
  have two := (at_two c d d0 d1 p e hp large eqn).comp g.strictMono.tendsto_atTop
  exact miss U V unit vpos (prod ▸ tendsto_nhds_unique limit two)

#print axioms alternative

/-- Positive exponents on a nonempty support turn the alternative into a
bounded pair: for bounded exponent vectors, only finitely many bases work. -/
theorem atom {K : ℕ} (pos : 0<K) (r : ℕ) (c d : ℚ) (c0 : 0≤c) (d0 : 0<d) (d1 : d≤1)
    (miss : ∀ U V : ℕ,r.Coprime U → 0<V → c*((U:ℚ)/V)≠2) :
    ∃ B : ℕ, ∀ p e : Fin K → ℕ, (∀ i,Nat.Prime (p i)) → (∀ i,Odd (p i)) → (∀ i,r.Coprime (p i)) →
      (∀ i,0<e i) → c*(∏ i,X (p i) (some (e i)))+d*(∏ i,Y (p i) (some (e i)))=2 →
      ∃ i,p i≤B ∧ e i≤B := by
  classical
  obtain ⟨L,alt⟩ := alternative K r c d d0.le d1 miss
  let F : Set (Fin K → ℕ) := {e | ∀ i,0<e i ∧ e i≤L}
  let bases (e : Fin K → ℕ) : Set (Fin K → ℕ) := {p | (∀ i,Nat.Prime (p i)) ∧
    c*(∏ i,X (p i) (some (e i)))+d*(∏ i,Y (p i) (some (e i)))=2}
  have cf : F.Finite := (Set.Finite.pi' (fun _ : Fin K => Set.finite_Iic L)).subset
    (fun _ h i => (h i).2)
  have bf := cf.biUnion (fun e he => (show (bases e).Finite from
    OMA.FixedExponents245212.finite_bases e (fun i => (he i).1) c d 2 c0 d0))
  obtain ⟨M,cap⟩ := (bf.biUnion (fun p _ => Set.finite_range p)).bddAbove
  refine ⟨max L M,?_⟩
  intro p e hp ho cop ep eq
  rcases alt p e hp ho cop eq with low | ⟨i,pi,ei⟩
  · let i : Fin K := ⟨0,pos⟩
    have ef : e∈F := fun j => ⟨ep j,low j⟩
    have member : p∈⋃ t∈F,bases t := Set.mem_iUnion₂.mpr ⟨e,ef,hp,eq⟩
    have pm := cap (Set.mem_iUnion₂.mpr ⟨p,member,i,rfl⟩)
    exact ⟨i,pm.trans (le_max_right _ _),(low i).trans (le_max_left _ _)⟩
  · exact ⟨i,pi.trans (le_max_left _ _),ei.trans (le_max_left _ _)⟩

theorem miss_core {k r a : ℕ} (pr : r.Prime) (odd : r≠2) (large : W (2^k)<r^a)
    (U V : ℕ) (unit : r.Coprime U) (vpos : 0<V) :
    (X 2 (some k)*X r (some a))*((U:ℚ)/V)≠2 := by
  intro eq
  let d2 := (k+1)*2^k
  let dr := (a+1)*r^a
  have fx : X 2 (some k)*(d2:ℚ)=W (2^k) := by simpa [d2] using x_factor Nat.prime_two k
  have fy : X r (some a)*(dr:ℚ)=W (r^a) := by simpa [dr] using x_factor pr a
  have diff := OMA.RankThreeAnchor245212.no_resonance pr odd unit large (V:=V)
  apply diff
  have cp := ((Nat.coprime_primes Nat.prime_two pr).mpr odd.symm).pow_left k
  rw [w_mult.map_mul_of_coprime (cp.pow_right a),ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
      (cp.pow_right a),ArithmeticFunction.sigma_zero_apply_prime_pow Nat.prime_two,
      ArithmeticFunction.sigma_zero_apply_prime_pow pr]
  have rhs : 2*(2^k*r^a)*((k+1)*(a+1))*V=2*d2*dr*V := by unfold d2 dr; ring
  rw [rhs]
  have eq' : (X 2 (some k)*X r (some a))*U=2*V := by
    rw [←mul_div_assoc] at eq
    exact (div_eq_iff (by exact_mod_cast vpos.ne')).mp eq
  exact_mod_cast (show (W (2^k):ℚ)*W (r^a)*U=2*d2*dr*V by
    rw [←fx,←fy]; linear_combination ((d2:ℚ)*dr)*eq')

#print axioms atom
#print axioms miss_core
end OMA.CohortAtom245212

end

section

/- The largest prime in a nonempty Euler resonance must divide the
target numerator. Thus a fixed cofactor forces a bounded prime power
unless a remaining prime divides the cofactor's divisor count. -/
namespace OMA.CofactorPrimeChain245212
open Finset Nat Filter Topology OMA.Smooth245212 OMA.SquareCompact245212
open OMA.CohortAtom245212 (at_two)
open scoped ArithmeticFunction.sigma

private def EulerTerm (H u v : ℕ) : Prop :=
  (u=1 ∧ v=1) ∨ (u.Prime ∧ ¬u∣H ∧ v=u-1)

private theorem no_product {K A H : ℕ} (below : A<H) (u v : Fin K→ℕ)
    (terms : ∀i,EulerTerm H (u i) (v i)) :
    A*(∏ i,u i)≠H*(∏ i,v i) := by
  classical
  by_cases one : ∀i,u i=1
  · have neutral (i) : v i=1 := by
      rcases terms i with z|z
      · exact z.2
      · have := z.1.one_lt; rw [one i] at this; omega
    simpa [one,neutral] using below.ne
  push Not at one
  obtain ⟨j,hj⟩:=one
  obtain ⟨m,_,maxim⟩:=univ.exists_max_image u ⟨j,mem_univ _⟩
  have far : 1<u j := by rcases terms j with z|z; exact False.elim (hj z.1); exact z.1.one_lt
  have big := far.trans_le (maxim j (mem_univ _))
  rcases terms m with z|⟨pr,avoid,_⟩
  · omega
  intro eqn
  have dvd : u m∣H*(∏ i,v i) := eqn ▸ dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem u (mem_univ m)) A
  obtain target|rest:=pr.dvd_mul.mp dvd
  · exact avoid target
  obtain ⟨i,_,iv⟩:= (pr.prime.dvd_finsetProd_iff v).mp rest
  have upper := maxim i (mem_univ _)
  rcases terms i with z|z
  · rw [z.2] at iv
    exact (not_le_of_gt big) (Nat.le_of_dvd (by decide) iv)
  · have pos := z.1.one_lt
    have gap : 0<v i ∧ v i<u m := by rw [z.2.2];omega
    exact gap.2.not_ge (Nat.le_of_dvd gap.1 iv)

private theorem no_limit {K A T : ℕ} (tpos : 0<T) (below : A<2*T) (x : Fin K→ℚ)
    (repr : ∀i,∃ u v : ℕ,EulerTerm (2*T) u v ∧ x i=(u:ℚ)/v) :
    ((A:ℚ)/T)*(∏ i,x i)≠2 := by
  classical
  choose u v uv frac using repr
  have pos (i) : 0<v i := by
    rcases uv i with z|z
    · rw [z.2];decide
    · rw [z.2.2];have := z.1.one_lt;omega
  have nonzero : (∏ i,(v i:ℚ))≠0 := (prod_pos (fun i _=>by exact_mod_cast pos i)).ne'
  have original := no_product below u v uv
  intro bad
  simp only [frac,prod_div_distrib] at bad
  field_simp [nonzero,show (T:ℚ)≠0 by exact_mod_cast tpos.ne'] at bad
  apply original
  exact_mod_cast (show (A:ℚ)*(∏ i,(u i:ℚ))=(2*T)*(∏ i,(v i:ℚ)) by linarith only [bad])

private theorem cap_repr {p H : ℕ} (pr : p.Prime) (avoid : ¬p∣H) :
    ∃ u v : ℕ,EulerTerm H u v ∧ X p none=(u:ℚ)/v := by
  refine ⟨p,p-1,Or.inr ⟨pr,avoid,rfl⟩,?_⟩
  have pp : (1:ℚ)<p := by exact_mod_cast pr.one_lt
  simp only [X,Y,sub_zero,Nat.cast_sub pr.one_le,Nat.cast_one]
  field_simp [show (p:ℚ)-1≠0 by linarith];ring

theorem alternative (K A T : ℕ) (tpos : 0<T) (below : A<2*T)
    (d : ℚ) (d0 : 0≤d) (d1 : d≤1) :
    ∃ B : ℕ, ∀ p e : Fin K→ℕ, (∀i,(p i).Prime) → (∀i,Odd (p i)) → (∀i,¬p i∣2*T) →
      ((A:ℚ)/T)*(∏ i,X (p i) (some (e i)))+d*(∏ i,Y (p i) (some (e i)))=2 →
      (∀i,e i≤B) ∨ ∃i,p i≤B ∧ e i≤B := by
  by_contra! bad
  choose p e hp ho avoid eqn large leave using bad
  let seq (n : ℕ) := (p n,e n)
  obtain ⟨g,sorted⟩ := wellQuasiOrdered_le.exists_monotone_subseq seq
  have points (i : Fin K) : ∃ x : ℚ,(∃ u v : ℕ,EulerTerm (2*T) u v ∧ x=(u:ℚ)/v) ∧
      Tendsto (fun n => X (p (g n) i) (some (e (g n) i))) atTop (𝓝 x) := by
    apply factor_limit_restricted _ _ _ (fun _ _ le => (sorted _ _ le).1 i)
      (fun _ _ le => (sorted _ _ le).2 i) (fun n=>hp (g n) i) (fun n=>ho (g n) i)
      ⟨1,1,Or.inl ⟨rfl,rfl⟩,by norm_num⟩
    · intro P pr _ fixed
      obtain ⟨n,same⟩:=fixed.exists
      exact cap_repr pr (same ▸ avoid (g n) i)
    · intro P E hP hE
      have big:=g.strictMono.tendsto_atTop.eventually (eventually_ge_atTop (max P E))
      obtain ⟨n,pn,en,gn⟩:=(hP.and (hE.and big)).exists
      change p (g n) i=P at pn
      change e (g n) i=E at en
      have both:=leave (g n) i
      rw [pn,en] at both
      exact False.elim ((not_lt_of_ge ((le_max_right P E).trans gn)) (both ((le_max_left P E).trans gn)))
  choose x ox conv using points
  have limit:=(tendsto_finsetProd univ (fun i _=>conv i)).const_mul ((A:ℚ)/T)
  have two:=(OMA.CohortAtom245212.at_two _ d d0 d1 p e hp large eqn).comp g.strictMono.tendsto_atTop
  exact no_limit tpos below x ox (tendsto_nhds_unique limit two)

#print axioms alternative
end OMA.CofactorPrimeChain245212

end

section

/- A fixed-rank family with no cross divisibility between its prime
bases and its exponent lengths is finite. The induction absorbs one
bounded prime power into the cofactor. -/
namespace OMA.CofactorCrossCount245212
open Finset Nat OMA.Smooth245212
open OMA.FixedExponents245212 (y_pos)
open scoped ArithmeticFunction.sigma

def balance {K : ℕ} (A T : ℕ) (d : ℚ) (p e : Fin K→ℕ) : Prop :=
  ((A:ℚ)/T)*(∏ i,X (p i) (some (e i)))+d*(∏ i,Y (p i) (some (e i)))=2

structure Admissible {K : ℕ} (T : ℕ) (p e : Fin K→ℕ) : Prop where
  prime (i) : (p i).Prime
  odd (i) : Odd (p i)
  positive (i) : 0<e i
  distinct : Function.Injective p
  avoid (i) : ¬p i∣2*T
  cross (i j) : i≠j → ¬p i∣e j+1

private theorem below {K A T : ℕ} {d : ℚ} {p e : Fin K→ℕ}
    (tp : 0<T) (dp : 0<d) (ok : Admissible T p e) (eqn : balance A T d p e) : A<2*T := by
  have one (i) : 1≤X (p i) (some (e i)) :=
    le_add_of_nonneg_right (div_nonneg (sub_nonneg.mpr (y_one (ok.prime i).one_lt _))
      (sub_nonneg.mpr (by exact_mod_cast (ok.prime i).one_le)))
  have all : 1≤∏i,X (p i) (some (e i)) := by
    calc
      1 = ∏ _i : Fin K,(1:ℚ) := by simp
      _ ≤ _ := prod_le_prod (fun _ _=>by norm_num) (fun i _=>one i)
  have yp := prod_pos (s:=univ) (fun i _=>OMA.FixedExponents245212.y_pos (ok.prime i) (e i))
  have c0 : 0≤(A:ℚ)/T := by positivity
  have small : (A:ℚ)/T<2 := by unfold balance at eqn;nlinarith only [eqn,mul_pos dp yp,mul_nonneg c0 (sub_nonneg.mpr all)]
  exact_mod_cast (div_lt_iff₀ (by exact_mod_cast tp : (0:ℚ)<T)).mp small

private theorem atom {K A T : ℕ} {d : ℚ} (kp : 0<K) (tp : 0<T) (cut : A<2*T)
    (dp : 0<d) (ds : d≤1) :
    ∃ B : ℕ, ∀ p e : Fin K→ℕ, Admissible T p e → balance A T d p e → ∃i,p i≤B ∧ e i≤B := by
  classical
  obtain ⟨L,alt⟩:=OMA.CofactorPrimeChain245212.alternative K A T tp cut d dp.le ds
  let F : Set (Fin K→ℕ) := {e | ∀i,0<e i ∧ e i≤L}
  let bases (e : Fin K→ℕ) : Set (Fin K→ℕ) := {p | (∀i,(p i).Prime) ∧ balance A T d p e}
  have cf : F.Finite := (Set.Finite.pi' (fun _ : Fin K=>Set.finite_Iic L)).subset
    (fun _ h i=>(h i).2)
  have bf := cf.biUnion (fun e he=>(show (bases e).Finite from
    OMA.FixedExponents245212.finite_bases e (fun i=>(he i).1) ((A:ℚ)/T) d 2 (by positivity) dp))
  obtain ⟨M,cap⟩:=(bf.biUnion (fun p _=>Set.finite_range p)).bddAbove
  refine ⟨max L M,?_⟩
  intro p e ok eqn
  rcases alt p e ok.prime ok.odd ok.avoid eqn with low|⟨i,pi,ei⟩
  · let i : Fin K:=⟨0,kp⟩
    have ef : e∈F:=fun j=>⟨ok.positive j,low j⟩
    have mem : p∈⋃ t∈F,bases t:=Set.mem_iUnion₂.mpr ⟨e,ef,ok.prime,eqn⟩
    have pm:=cap (Set.mem_iUnion₂.mpr ⟨p,mem,i,rfl⟩)
    exact ⟨i,pm.trans (le_max_right _ _),(low i).trans (le_max_left _ _)⟩
  · exact ⟨i,pi.trans (le_max_left _ _),ei.trans (le_max_left _ _)⟩

private def scale (p e : ℕ) := (e+1)*p^e

private theorem peel {K A T : ℕ} {d : ℚ} {p e : Fin (K+1)→ℕ} (j : Fin (K+1))
    (tp : 0<T) (ok : Admissible T p e) (eqn : balance A T d p e) :
    Admissible (T*scale (p j) (e j)) (p ∘ j.succAbove) (e ∘ j.succAbove) ∧
    balance (A*W (p j^e j)) (T*scale (p j) (e j)) (d*Y (p j) (some (e j)))
      (p ∘ j.succAbove) (e ∘ j.succAbove) := by
  constructor
  · refine ⟨fun i=>ok.prime _,fun i=>ok.odd _,fun i=>ok.positive _,ok.distinct.comp j.succAbove_right_injective,?_,?_⟩
    · intro i dv
      let l:=j.succAbove i
      change p l∣2*(T*scale (p j) (e j)) at dv
      rw [←mul_assoc] at dv
      rcases (ok.prime l).dvd_mul.mp dv with a|a
      · exact ok.avoid l a
      rcases (ok.prime l).dvd_mul.mp a with b|b
      · exact ok.cross l j (Fin.succAbove_ne _ _) b
      exact Fin.succAbove_ne j i (ok.distinct ((prime_dvd_prime_iff_eq (ok.prime l) (ok.prime j)).mp
        ((ok.prime l).dvd_of_dvd_pow b)))
    · intro i k neq
      exact ok.cross _ _ (fun same=>neq (j.succAbove_right_injective same))
  · have hscale : 0<scale (p j) (e j) := by unfold scale;have:= (ok.prime j).pos;positivity
    have fx:=x_factor (ok.prime j) (e j)
    have val : ((A*W (p j^e j):ℕ):ℚ)/(T*scale (p j) (e j):ℕ)=((A:ℚ)/T)*X (p j) (some (e j)) := by
      push_cast
      field_simp [show (scale (p j) (e j):ℚ)≠0 by exact_mod_cast hscale.ne',
        show (T:ℚ)≠0 by exact_mod_cast tp.ne']
      unfold scale
      push_cast
      linear_combination -(A:ℚ)*fx
    unfold balance at eqn ⊢
    rw [Fin.prod_univ_succAbove (fun i=>X (p i) (some (e i))) j,
      Fin.prod_univ_succAbove (fun i=>Y (p i) (some (e i))) j] at eqn
    simpa only [val,Function.comp_apply,mul_assoc] using eqn

theorem bounded (K : ℕ) : ∀ (A T : ℕ) (d : ℚ), 0<T → 0<d → d≤1 →
    ∃ B : ℕ,∀ p e : Fin K→ℕ, Admissible T p e → balance A T d p e → total p e≤B := by
  classical
  induction K with
  | zero =>
    intro A T d _ _ _
    exact ⟨1,fun p e _ _=>by simp [total]⟩
  | succ K ih =>
    intro A T d tp dp ds
    by_cases cut : A<2*T
    · obtain ⟨L,cap⟩:=atom (K:=K+1) (Nat.succ_pos _) tp cut dp ds
      let bound (r z : ℕ) : ℕ := if good : r.Prime then
        Classical.choose (ih (A*W (r^z)) (T*scale r z) (d*Y r (some z))
          (by unfold scale;have:=good.pos;positivity) (mul_pos dp (OMA.FixedExponents245212.y_pos good z))
          ((mul_le_of_le_one_right dp.le (y_one good.one_lt _)).trans ds)) else 0
      let maxRest:=((range (L+1)).product (range (L+1))).sup (fun k=>bound k.1 k.2)
      refine ⟨(L+1)^L*maxRest,?_⟩
      intro p e ok eqn
      obtain ⟨j,pj,ej⟩:=cap p e ok eqn
      have rest:=peel j tp ok eqn
      have rule : total (p ∘ j.succAbove) (e ∘ j.succAbove)≤bound (p j) (e j) := by
        unfold bound
        rw [dif_pos (ok.prime j)]
        exact Classical.choose_spec (ih (A*W (p j^e j)) (T*scale (p j) (e j)) (d*Y (p j) (some (e j)))
          (by unfold scale;have:=(ok.prime j).pos;positivity)
          (mul_pos dp (OMA.FixedExponents245212.y_pos (ok.prime j) _))
          ((mul_le_of_le_one_right dp.le (y_one (ok.prime j).one_lt _)).trans ds))
          _ _ rest.1 rest.2
      have member : (p j,e j)∈(range (L+1)).product (range (L+1)) :=
        mem_product.mpr ⟨mem_range.mpr (by omega),mem_range.mpr (by omega)⟩
      have hi : bound (p j) (e j) ≤ maxRest := le_sup (f:=fun k : ℕ×ℕ=>bound k.1 k.2) member
      have pw : p j^e j≤(L+1)^L := (Nat.pow_le_pow_left (pj.trans (Nat.le_succ L)) _).trans
        (Nat.pow_le_pow_right (Nat.succ_pos _) ej)
      rw [total,Fin.prod_univ_succAbove _ j]
      exact Nat.mul_le_mul pw (rule.trans hi)
    · exact ⟨0,fun p e ok eqn=>False.elim (cut (below tp dp ok eqn))⟩

#print axioms bounded
end OMA.CofactorCrossCount245212

end

section

/- Finite original A245212 solutions of bounded odd-prime rank
when no odd prime divides another exponent length or the divisor count
of the fixed cofactor. -/
namespace OMA.CofactorCrossOriginal245212
open Nat Finset ArithmeticFunction OMA.Smooth245212 OMA.CofactorCrossCount245212
open scoped ArithmeticFunction.sigma

theorem sigma_bound {h : ℕ} (pos : 0<h) : σ 1 h≤h*σ 0 h := by
  rw [sigma_one_apply,sigma_zero_apply,mul_comm]
  simpa using (sum_le_card_nsmul h.divisors (fun d : ℕ=>d) h (fun d hd=>
    Nat.le_of_dvd pos (Nat.mem_divisors.mp hd).1))

theorem normalized_extension {ι : Type*} [Fintype ι] {h : ℕ} {p e : ι→ℕ} (hh : 0<h) (pr : ∀i,(p i).Prime)
    (unique : Function.Injective p) (cop : ∀i,h.Coprime (p i))
    (eqn : OeisA245212.a (h*total p e)=(σ 1 (h*total p e):ℤ)) :
    ((W h:ℚ)/(h*σ 0 h:ℕ))*(∏i,X (p i) (some (e i)))+
      ((σ 1 h:ℚ)/(h*σ 0 h:ℕ))*(∏i,Y (p i) (some (e i)))=2 := by
  classical
  let z (i : ι):=p i^e i
  have pair : (↑(univ : Finset ι) : Set ι).Pairwise (fun i j=>(z i).Coprime (z j)) := by
    intro i _ j _ different
    exact (((coprime_primes (pr i) (pr j)).mpr (fun same=>different (unique same))).pow_left _).pow_right _
  have hc : h.Coprime (total p e) := coprime_prod_right_iff.mpr (fun i _=>(cop i).pow_right _)
  have nz : total p e≠0 := prod_ne_zero_iff.mpr (fun i _=>pow_ne_zero _ (pr i).ne_zero)
  have bal:=OMA.Abundance245212.balance (mul_ne_zero hh.ne' nz) eqn
  rw [w_mult.map_mul_of_coprime hc,isMultiplicative_sigma.map_mul_of_coprime hc,
    isMultiplicative_sigma.map_mul_of_coprime hc] at bal
  have wp:=IsMultiplicative.map_prod z w_mult univ pair
  have sp:=IsMultiplicative.map_prod z (isMultiplicative_sigma (k:=1)) univ pair
  have tp:=IsMultiplicative.map_prod z (isMultiplicative_sigma (k:=0)) univ pair
  change W (total p e)=_ at wp
  change σ 1 (total p e)=_ at sp
  change σ 0 (total p e)=_ at tp
  simp only [z,sigma_zero_apply_prime_pow (pr _)] at tp
  let mass : ℚ:=∏ i,(((e i:ℕ):ℚ)+1)*(p i:ℚ)^e i
  have tax : mass = (total p e:ℚ)*(σ 0 (total p e):ℚ) := by
    rw [tp,total];push_cast;dsimp [mass];rw [prod_mul_distrib];ring
  have positive : 0 < mass := by
    apply prod_pos
    intro i _
    have := (pr i).pos
    positivity
  have wprod : (∏ i,X (p i) (some (e i)))*mass=(W (total p e):ℚ) := by
    rw [wp,←prod_mul_distrib];push_cast
    exact prod_congr rfl (fun i _=>x_factor (pr i) (e i))
  have sprod : (∏ i,Y (p i) (some (e i)))*mass=(σ 1 (total p e):ℚ) := by
    rw [sp,←prod_mul_distrib];push_cast
    exact prod_congr rfl (fun i _=>y_factor (pr i) (e i))
  have D : 0<h*σ 0 h := Nat.mul_pos hh (sigma_pos 0 h hh.ne')
  have rat:=congrArg ((↑):ℕ→ℚ) bal
  push_cast at rat
  apply mul_right_cancel₀ (b:=mass) positive.ne'
  rw [add_mul,mul_assoc,mul_assoc,wprod,sprod,tax]
  field_simp [show ((h*σ 0 h:ℕ):ℚ)≠0 by exact_mod_cast D.ne']
  push_cast
  linear_combination rat

theorem original (h K : ℕ) (hh : 0<h) :
    ∃ B : ℕ,∀ p e : Fin K→ℕ, (∀i,(p i).Prime) → (∀i,Odd (p i)) → (∀i,h.Coprime (p i)) →
      Function.Injective p → (∀i,0<e i) → (∀i,¬p i∣σ 0 h) → (∀i j,i≠j → ¬p i∣e j+1) →
      OeisA245212.a (h*total p e)=(σ 1 (h*total p e):ℤ) → h*total p e≤B := by
  let T:=h*σ 0 h
  have tp : 0<T:=mul_pos hh (sigma_pos 0 h hh.ne')
  have dp : (0:ℚ)<(σ 1 h:ℚ)/T := div_pos (by exact_mod_cast sigma_pos 1 h hh.ne') (by exact_mod_cast tp)
  have ds : (σ 1 h:ℚ)/T≤1 := (div_le_one (by exact_mod_cast tp)).mpr (by exact_mod_cast sigma_bound hh)
  obtain ⟨L,cap⟩:=bounded K (W h) T _ tp dp ds
  refine ⟨h*L,?_⟩
  intro p e pr odd cop inj ep avoid cross eqn
  apply Nat.mul_le_mul_left h
  apply cap p e ⟨pr,odd,ep,inj,?_,cross⟩ (normalized_extension hh pr inj cop eqn)
  intro i dv
  rcases (pr i).dvd_mul.mp dv with two|rhs
  · have same:=(prime_dvd_prime_iff_eq (pr i) prime_two).mp two
    obtain ⟨k,hk⟩:=odd i
    omega
  rcases (pr i).dvd_mul.mp rhs with divides|divides
  · exact ((pr i).coprime_iff_not_dvd.mp (cop i).symm) divides
  · exact avoid i divides

#print axioms original
end OMA.CofactorCrossOriginal245212

end

section

/- Removal of all cofactor prime bases from the pole bound of a retained
prime. The remaining exponent is polynomially bounded in log of the cofactor. -/
namespace OMA.ArbitraryMixedGap245212
noncomputable section
open Nat Finset ArithmeticFunction Polynomial OMA.WeightedGapPolynomial245212
open OMA.Smooth245212 (W)
open scoped ArithmeticFunction.sigma
open OMA.CofactorCrossOriginal245212 (sigma_bound)

def poly (r : ℕ) : Polynomial ℕ :=
  let K:=2*envelope r
  2*K+2*K*(2*(envelope r).comp (X+2*K))

private theorem equations {H A S B C q u : ℕ} (qv : q=u+1) (up : 0<u)
    (bp : 0<B) (cp : 0<C) (ss : S≤H) (side : C*A<u*S)
    (hit : H*B*C*u^2=q*(A*C*(B*u-1)+S*u)) :
    ∃ E Δ : ℕ, 0<E ∧ 0<Δ ∧ E+q*A=u*H ∧ Δ+A=H ∧ B*E≤q*H ∧ q*Δ=E+H := by
  have qp : 0<q:=by omega
  have bu:=Nat.sub_add_cancel (show 1≤B*u from Nat.mul_pos bp up)
  have raw : B*u*C*(H*u)+q*(A*C)=B*u*C*(A*q)+q*(u*S):=by
    nlinarith only [hit,congrArg (fun z : ℕ=>q*(A*C)*z) bu]
  have strict : A*q<H*u:=by
    by_contra! no
    have low:=Nat.mul_le_mul_left (B*u*C) no
    have sign:=Nat.mul_lt_mul_of_pos_left side qp
    nlinarith only [raw,low,sign]
  have ah : A<H:=by
    by_contra! no
    have bad:=Nat.mul_le_mul_right u no
    rw [qv,Nat.mul_add,Nat.mul_one] at strict
    omega
  let E:=H*u-A*q
  let Δ:=H-A
  have ee : E+q*A=u*H:=by
    dsimp only [E];rw [Nat.mul_comm q A,Nat.mul_comm u H,Nat.sub_add_cancel strict.le]
  have de : Δ+A=H:=Nat.sub_add_cancel ah.le
  have prod : B*u*C*E+q*(A*C)=q*(u*S):=by
    nlinarith only [raw,congrArg (fun z : ℕ=>B*u*C*z) ee]
  have main : (B*E*C)*u≤(q*S)*u:=by nlinarith only [prod,Nat.zero_le (q*(A*C))]
  have bare:=Nat.le_of_mul_le_mul_right main up
  refine ⟨E,Δ,Nat.sub_pos_of_lt strict,Nat.sub_pos_of_lt ah,ee,de,
    (Nat.le_mul_of_pos_right _ cp).trans (bare.trans (Nat.mul_le_mul_left q ss)),?_⟩
  nlinarith only [ee,congrArg (q*·) de,congrArg (·*H) qv]

theorem mixed {h q B C r : ℕ} (pos : 0<h) (rank : h.primeFactors.card≤r)
    (qg : 2≤q) (bp : 0<B) (cp : 0<C)
    (side : C*W h<(q-1)*σ 1 h)
    (hit : (2*h*σ 0 h)*B*C*(q-1)^2=q*(W h*C*(B*(q-1)-1)+σ 1 h*(q-1))) :
    B≤(poly r).eval (Nat.log 2 h+2) := by
  let x:=Nat.log 2 h+2
  let H:=2*(h*σ 0 h)
  let K:=2*(envelope r).eval x
  have lengths (p) (mem:p∈h.primeFactors) : h.factorization p+1≤x:=by
    have pow : 2^h.factorization p≤h:=(Nat.pow_le_pow_left (prime_of_mem_primeFactors mem).two_le _).trans
      (Nat.le_of_dvd pos (Nat.ordProj_dvd h p))
    have log:=Nat.le_log_of_pow_le (by decide : 1<(2:ℕ)) pow
    dsimp [x];omega
  have ss : σ 1 h≤H:=(OMA.CofactorCrossOriginal245212.sigma_bound pos).trans (by dsimp [H];omega)
  obtain ⟨E,Δ,ep,dp,ee,de,sb,id⟩:=equations (H:=H) (u:=q-1) (q:=q) (by omega) (by omega)
    bp cp ss side (by simpa only [H,mul_assoc] using hit)
  have rel (v t y z : ℕ) (yp : 0<y) (vz : v≤z) (xz : x≤z) (eqn : y+v*W h=t*H) :
      H≤(2*(envelope r).eval z)*y:=by
    have e : (t*2)*(h*σ 0 h)=y+v*W h:=by
      simpa only [H,mul_assoc] using eqn.symm
    have g:=OMA.WeightedGapPolynomial245212.original pos rank (fun p m=>(lengths p m).trans xz) vz yp e
    simpa only [H,mul_assoc] using Nat.mul_le_mul_left 2 g
  have first : H≤K*Δ:=rel 1 1 Δ x dp (by dsimp [x];omega) le_rfl (by simpa using de)
  change B≤(poly r).eval x
  simp only [poly,eval_add,eval_mul,eval_ofNat,eval_comp,eval_X]
  change B≤2*K+2*K*(2*(envelope r).eval (x+2*K))
  by_cases large : 2*K≤q
  · have high:=Nat.mul_le_mul_right Δ large
    have bound : q*Δ≤2*E:=by nlinarith only [high,id,first]
    have hq:=Nat.mul_le_mul_left q first
    have b:=Nat.mul_le_mul_left K bound
    have fin : B*E≤(2*K)*E:=by nlinarith only [sb,hq,b]
    exact (Nat.le_of_mul_le_mul_right fin ep).trans (Nat.le_add_right _ _)
  · have qz : q≤x+2*K:=by omega
    have close:=rel q (q-1) E (x+2*K) ep qz (Nat.le_add_right _ _) ee
    have hq:=Nat.mul_le_mul_left q close
    have fin : B*E≤(q*(2*(envelope r).eval (x+2*K)))*E:=by
      simpa only [mul_assoc] using sb.trans hq
    exact (Nat.le_of_mul_le_mul_right fin ep).trans
      ((Nat.mul_le_mul_right _ (by omega : q≤2*K)).trans (Nat.le_add_left _ _))

#print axioms mixed
end
end OMA.ArbitraryMixedGap245212

end

section

/- Integer size comparisons for the general complementary-exponent bound. -/
namespace OMA.ComplementarySize245212

/-- An elementary integer substitute for d log b ≤ b/2 when
b≥16(d+1)². -/
theorem absorb {b d : ℕ} (big : 16*(d+1)^2≤b) : b^(2*d)≤2^b := by
  let s := b.sqrt
  have sl : (4*(d+1)) ≤ s := Nat.le_sqrt'.mpr (by nlinarith only [big])
  have slo : s^2≤b := Nat.sqrt_le' b
  have shi : b<(s+1)^2 := Nat.lt_succ_sqrt' b
  have bas : b≤2^(2*s) := calc
    _ ≤ 2*s^2+1 := by
      nlinarith only [shi, Nat.mul_le_mul_left s (show 2 ≤ s by omega)]
    _ ≤ _ := Nat.two_mul_sq_add_one_le_two_pow_two_mul s
  calc
    _ ≤ (2^(2*s))^(2*d) := Nat.pow_le_pow_left bas _
    _ = _ := (pow_mul _ _ _).symm
    _ ≤ 2^b := Nat.pow_le_pow_right (by decide)
      (by nlinarith only [slo,Nat.mul_le_mul_left s sl])

/-- Common last step, using the integer-only growth estimate above. -/
theorem exponents {a d K : ℕ} (hK : 1≤K)
    (power : 2^(a-1)≤2^(16*(d+1)^2)*(2^K)^(d+1)*(a+1)^d*K^(3*d+1)) :
    a+1≤64*(d+1)^2*K := by
  by_cases big : 16*(d+1)^2≤a+1
  · let X := 16*(d+1)^2 + K*(d+1) + K*(3*d+1)
    have scale : K≤(2:ℕ)^K := (Nat.lt_pow_self (by decide : 1<2)).le
    have idpow : 2^X = (2^(16*(d+1)^2)*(2^K)^(d+1))*(2^K)^(3*d+1) := by
      dsimp [X]
      rw [pow_add (2:ℕ) (16*(d+1)^2+K*(d+1)) (K*(3*d+1)),
        pow_add (2:ℕ) (16*(d+1)^2) (K*(d+1)),pow_mul (2:ℕ) K (d+1),
        pow_mul (2:ℕ) K (3*d+1)]
    have input : 2^(a-1)≤2^X*(a+1)^d := calc
      _ ≤ _ := power
      _ ≤ 2^(16*(d+1)^2)*(2^K)^(d+1)*(a+1)^d*(2^K)^(3*d+1) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left scale _)
      _ = _ := by
        rw [idpow]
        exact mul_right_comm _ _ _
    have hh := Nat.pow_le_pow_left input 2
    rw [←pow_mul,mul_pow,←pow_mul,←pow_mul] at hh
    have v := Nat.mul_le_mul_left (2^(X*2)) (absorb big)
    rw [Nat.mul_comm 2 d] at v
    rw [←pow_add] at v
    have hb := (pow_le_pow_iff_right₀ (a:=(2:ℕ)) (by decide)).mp (hh.trans v)
    dsimp [X] at hb
    have al : 1≤a := by nlinarith only [big, Nat.zero_le d, Nat.zero_le (d^2)]
    have cut := Nat.sub_add_cancel al
    nlinarith only [hb,cut,
      Nat.mul_le_mul_right ((d+1)^2) hK,
      Nat.zero_le (K*d),Nat.zero_le (K*d^2),hK]
  · nlinarith only [Nat.lt_of_not_ge big, Nat.mul_le_mul_right ((d+1)^2) hK]

end OMA.ComplementarySize245212

end

section

/- Absolute length bound for an exact physical rounding with one retained
prime, any number of exact primes, and any number of discarded primes. -/
namespace OMA.ArbitraryMixedFinite245212
noncomputable section
open Nat ArithmeticFunction OMA.ArbitraryMixedGap245212 OMA.WeightedGapPolynomial245212
open OMA.Smooth245212 (W)
open scoped ArithmeticFunction.sigma

def cutoff (r D : ℕ) :=
  let F:=poly r
  let a:=F.eval 1+1
  let d:=F.natDegree
  a*(16*(d*D+1)^2+2*(a*D)+6)^d

theorem bounded {h q B C r D : ℕ} (pos : 0<h) (rank : h.primeFactors.card≤r)
    (qg : 2≤q) (bp : 0<B) (cp : 0<C) (small : h≤(B+1)^D)
    (side : C*W h<(q-1)*σ 1 h)
    (hit : (2*h*σ 0 h)*B*C*(q-1)^2=q*(W h*C*(B*(q-1)-1)+σ 1 h*(q-1))) :
    B≤cutoff r D := by
  let l:=Nat.log 2 h
  let F:=poly r
  let d:=F.natDegree
  let a:=F.eval 1+1
  let y:=l+3
  have base : B≤F.eval 1*y^d:=(mixed pos rank qg bp cp side hit).trans (eval_height _ _)
  have plus : B+1≤a*y^d:=by
    have one:=Nat.one_le_pow d y (by dsimp [y];omega)
    dsimp only [a];nlinarith only [base,one]
  have pot : 2^l≤2^(a*D)*y^(d*D):=calc
    _ ≤ h := Nat.pow_log_le_self 2 pos.ne'
    _ ≤ (B+1)^D := small
    _ ≤ (a*y^d)^D := Nat.pow_le_pow_left plus _
    _ = a^D*y^(d*D) := by rw [mul_pow,pow_mul]
    _ ≤ _ := by
      rw [pow_mul (2:ℕ) a D]
      exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.lt_pow_self (by decide : 1<(2:ℕ))).le _)
  have bound : y≤16*(d*D+1)^2+2*(a*D)+6:=by
    by_cases big : 16*(d*D+1)^2≤y
    · have absorb:=OMA.ComplementarySize245212.absorb big
      have square:=Nat.pow_le_pow_left pot 2
      have hsq : (2^(a*D)*y^(d*D))^2=2^(2*(a*D))*y^(2*(d*D)):=by
        rw [mul_pow,←pow_mul,←pow_mul,Nat.mul_comm (a*D) 2,Nat.mul_comm (d*D) 2]
      have joined : 2^(2*l)≤2^(2*(a*D)+y):=by
        rw [pow_add]
        rw [hsq,←pow_mul,Nat.mul_comm l 2] at square
        exact square.trans (Nat.mul_le_mul_left _ absorb)
      have exp:=(pow_le_pow_iff_right₀ (a:=(2:ℕ)) (by decide)).mp joined
      dsimp only [y] at exp ⊢;omega
    · omega
  exact (Nat.le_succ B).trans (plus.trans (Nat.mul_le_mul_left a (Nat.pow_le_pow_left bound d)))

#print axioms bounded
end
end OMA.ArbitraryMixedFinite245212

end

#print axioms OMA.ArbitraryMixedFinite245212.bounded
