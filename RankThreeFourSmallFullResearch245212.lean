import FormalConjectures.OEIS.«245212»






/-! OEIS A245212: four times three distinct odd prime powers. -/

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

namespace OMA.OddFaces245212
open OMA.Smooth245212
def limitX (p : ℕ) : ℚ := X p none
end OMA.OddFaces245212

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

/- The product of the limiting prime factors must reach two on
any nontrivial solution. This keeps the small-prime classification independent
of particular statements of the high-totient result. -/
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

theorem envelope (s : Finset ι) (p e : ι → ℕ) (hp : ∀ i,1<p i) :
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

theorem cap_anti {a b : ℕ} (ha : 1<a) (hab : a≤b) : limitX b≤limitX a := by
  have a' : (1:ℚ)<a := by exact_mod_cast ha
  have ab : (a:ℚ)≤b := by exact_mod_cast hab
  simp only [limitX,X,Y,sub_zero]
  exact add_le_add_right (one_div_le_one_div_of_le (by linarith) (by linarith)) 1

end OMA.OddFaces245212

end

section

/- Keep the dyadic factor exact in the Euler bound for an odd support. -/
namespace OMA.DyadicEuler245212
open Finset Nat OMA.Smooth245212 OMA.OddFaces245212
open scoped ArithmeticFunction.sigma
open OMA.OddFaces245212 (envelope)

theorem cap_needed_at_two {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ)
    (p e : ι → ℕ) (hp : ∀ j,1<p j) (i : ι) (ei : 0<e i)
    (eq : X 2 (some k)*(∏ j,X (p j) (some (e j)))+
      Y 2 (some k)*(∏ j,Y (p j) (some (e j)))=2) :
    2≤X 2 (some k)*∏ j,limitX (p j) := by
  let c := X 2 (some k)
  let d := Y 2 (some k)
  have sum : c+d=2 := by dsimp [c,d,X]; norm_num; ring
  have c0 : 0≤c := x_nonneg (by decide) _
  have yl : Y (p i) (some (e i))<1 := by
    simpa [y_avg (hp i)] using OMA.Abundance245212.y_strict (hp i) ei
  have small : (∏ j,Y (p j) (some (e j)))<1 := by
    rw [←prod_erase_mul _ _ (mem_univ i)]
    exact (mul_le_of_le_one_left (y_nonneg (hp i) _) (prod_le_one
      (fun j _ => y_nonneg (hp j) _) (fun j _ => y_one (hp j) _))).trans_lt yl
  have weigh := mul_le_mul_of_nonneg_left (OMA.OddFaces245212.envelope univ p e hp) c0
  change c*(∏ j,X (p j) (some (e j)))+d*(∏ j,Y (p j) (some (e j)))=2 at eq
  change 2≤c*_
  by_contra! low
  let t := ∏ j,Y (p j) (some (e j))
  let C := ∏ j,limitX (p j)
  change c*C<2 at low
  change t<1 at small
  change c*_≤c*(t+(1-t)*C) at weigh
  change c*_+d*t=2 at eq
  nlinarith only [weigh,eq,mul_pos (sub_pos.mpr small) (sub_pos.mpr low),
    congrArg (·*t) sum]

theorem pair_norm (k p q e f : ℕ) (hp : p.Prime) (hq : q.Prime)
    (po : 2<p) (pq : p<q)
    (eq : OeisA245212.a (2^k*p^e*q^f)=(σ 1 (2^k*p^e*q^f):ℤ)) :
    X 2 (some k)*(X p (some e)*X q (some f))+Y 2 (some k)*(Y p (some e)*Y q (some f))=2 := by
  let P : Fin 3 → ℕ := ![2,p,q]
  let E : Fin 3 → ℕ := ![k,e,f]
  have prime (i : Fin 3) : (P i).Prime := by fin_cases i <;> simp [P,hp,hq,prime_two]
  have inj : P.Injective := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [P] <;> omega
  have he : total P E=2^k*p^e*q^f := by simp [total,Fin.prod_univ_three,P,E,mul_assoc]
  have norm := normalized_of_eq P prime inj E (he ▸ eq)
  simpa [normalized,Fin.prod_univ_three,P,E,mul_assoc] using norm

theorem pair_cap (k p q e f : ℕ) (hp : p.Prime) (hq : q.Prime)
    (po : 2<p) (pq : p<q) (ep : 0<e)
    (eq : OeisA245212.a (2^k*p^e*q^f)=(σ 1 (2^k*p^e*q^f):ℤ)) :
    2≤X 2 (some k)*(limitX p*limitX q) := by
  have norm := pair_norm k p q e f hp hq po pq eq
  have lim := cap_needed_at_two k (![p,q] : Fin 2 → ℕ) ![e,f]
    (by intro j; fin_cases j <;> first | exact hp.one_lt | exact hq.one_lt) 0 ep
  simpa [Fin.prod_univ_two,mul_assoc] using lim (by simpa [Fin.prod_univ_two,mul_assoc] using norm)

theorem pair_small {k p q e f u v : ℕ} (hp : p.Prime) (hq : q.Prime)
    (po : 2<p) (pq : p<q) (ep : 0<e) (hu : 1<u) (hv : 1<v) (up : u≤p) (vq : v≤q)
    (small : X 2 (some k)*(limitX u*limitX v)<2) :
    OeisA245212.a (2^k*p^e*q^f)≠(σ 1 (2^k*p^e*q^f):ℤ) := by
  intro eq
  have atMost := mul_le_mul_of_nonneg_left (mul_le_mul (cap_anti hu up) (cap_anti hv vq)
    (x_nonneg hq.one_lt none) (x_nonneg hu none)) (x_nonneg (by decide : 1<2) (some k))
  exact ((pair_cap k p q e f hp hq po pq ep eq).trans atMost).not_gt small


end OMA.DyadicEuler245212

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

/- Divisibility constraints on a single prime extension. -/
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

/- The divisor score strictly increases in one prime exponent as soon as
one other prime exponent is sufficiently large. -/
namespace OMA.CapOrder245212
open Finset OMA.Smooth245212 OMA.Abundance245212

theorem geom (p : ℕ) (hp : 1<p) (e : ℕ) :
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

/- A computable finite search at each dyadic exponent for two unrestricted
odd primes. No divisor-count or exponent pattern has to be fixed. -/
namespace OMA.PairHeight245212
open Nat Finset ArithmeticFunction OMA.Smooth245212 OMA.OddFaces245212
open scoped ArithmeticFunction.sigma
open OMA.FixedExponents245212 (y_pos)

theorem scaledX (p : ℕ) (hp : 1<p) (e : Option ℕ) :
    X p e*((p-1:ℕ):ℚ)=(p:ℚ)-Y p e := by
  have pp : (1:ℚ)<p := by exact_mod_cast hp
  rw [Nat.cast_sub (by omega : 1≤p),Nat.cast_one]
  unfold X; field_simp [show (p:ℚ)-1≠0 by linarith]; ring

def T (k : ℕ) := (k+1)*2^k
def Q (k : ℕ) := 2*T k*(6*T k+1)+1
def E (k : ℕ) := 8*T k*Q k

private theorem small_first {A T u v p q : ℕ} (a : A<2*T) (pv : p=u+1) (qv : q=v+1)
    (uv : u≤v) (vp : 0<v) (cap : 2*T*u*v < A*p*q) : p≤6*T+1 := by
  have diff : (A+1)*u*v≤2*T*u*v :=
    Nat.mul_le_mul_right v (Nat.mul_le_mul_right u a)
  have extra : A*(u+v+1)≤(2*T)*(3*v) := Nat.mul_le_mul a.le (by omega)
  have bound : u*v≤(6*T)*v := by
    rw [pv,qv] at cap
    nlinarith only [cap,diff,extra]
  exact pv ▸ (Nat.add_le_add_right (Nat.le_of_mul_le_mul_right bound vp) 1)

private theorem small_second {A T u v p q : ℕ} (a : A<2*T) (qv : q=v+1)
    (cap : 2*T*u*v<A*p*q) (under : A*p<2*T*u) : q≤2*T*p+1 := by
  have scaled : (A*p+1)*v≤2*T*u*v := Nat.mul_le_mul_right v under
  have above := Nat.mul_le_mul_right p a.le
  rw [qv] at cap ⊢
  nlinarith only [cap,scaled,above]

theorem small_exp {A T u v p q e f : ℕ} (up : 0<u) (vp : 0<v)
    (hp : p.Prime) (hq : q.Prime) (big : 2*T*u*v<A*p*q)
    (uv : X p (some e)*((u:ℕ):ℚ)=(p:ℚ)-Y p (some e))
    (vv : X q (some f)*((v:ℕ):ℚ)=(q:ℚ)-Y q (some f))
    (strict : (A:ℚ)*(X p (some e)*X q (some f))<2*(T:ℚ)) :
    min e f+1≤2*A*(p+q) := by
  let y:=Y p (some e)
  let z:=Y q (some f)
  have y0 : 0≤y := y_nonneg hp.one_lt _
  have z0 : 0≤z := y_nonneg hq.one_lt _
  have ad : (0:ℚ)≤A := Nat.cast_nonneg _
  have gap : (2:ℚ)*T*u*v+1≤A*p*q := by exact_mod_cast big
  have den : (0:ℚ)<u*v := mul_pos (by exact_mod_cast up) (by exact_mod_cast vp)
  have scaled := mul_lt_mul_of_pos_right strict den
  have prodid := congrArg₂ (·*·) uv vv
  change X p (some e)*u*(X q (some f)*v)=((p:ℚ)-y)*((q:ℚ)-z) at prodid
  have lo : (1:ℚ)≤A*(p*z+q*y) := by
    nlinarith only [gap,scaled,congrArg ((A:ℚ)*·) prodid,mul_nonneg ad (mul_nonneg y0 z0)]
  let m := min e f+1
  have mb (a : ℕ) (h : min e f≤a) : (m:ℚ)≤(a:ℚ)+1 := by exact_mod_cast Nat.succ_le_succ h
  have ym := (mul_le_mul_of_nonneg_left (mb e (min_le_left ..)) y0).trans_lt (OMA.CapOrder245212.y_short hp e)
  have zm := (mul_le_mul_of_nonneg_left (mb f (min_le_right ..)) z0).trans_lt (OMA.CapOrder245212.y_short hq f)
  have hi := mul_le_mul_of_nonneg_left (add_le_add
    (mul_le_mul_of_nonneg_left zm.le (Nat.cast_nonneg p : (0:ℚ)≤p))
    (mul_le_mul_of_nonneg_left ym.le (Nat.cast_nonneg q : (0:ℚ)≤q))) ad
  have low := mul_le_mul_of_nonneg_right lo (Nat.cast_nonneg m : (0:ℚ) ≤ m)
  exact_mod_cast (show (m:ℚ)≤2*A*((p:ℚ)+q) by nlinarith only [low,hi])

private theorem one_exp {A T p e u : ℕ} (hp : p.Prime) (up : 0<u)
    (big : 2*T*u<A*p) (strict : (A:ℚ)*X p (some e)<2*(T:ℚ))
    (xy : X p (some e)*(u:ℚ)=(p:ℚ)-Y p (some e)) : e+1≤2*A := by
  have gap : (2:ℚ)*T*u+1≤A*p := by exact_mod_cast big
  have bound := mul_lt_mul_of_pos_right strict (show (0:ℚ)<u by exact_mod_cast up)
  have cost : 1≤(A:ℚ)*Y p (some e) := by nlinarith only [gap,bound,congrArg ((A:ℚ)*·) xy]
  have low := mul_le_mul_of_nonneg_right cost (show (0:ℚ)≤e+1 by positivity)
  have high := mul_le_mul_of_nonneg_left (OMA.CapOrder245212.y_short hp e).le (Nat.cast_nonneg A : (0:ℚ)≤A)
  exact_mod_cast (show (e:ℚ)+1≤2*A by nlinarith only [low,high])

/-- On two odd primes one of the primes and its exponent are simultaneously
bounded by explicit functions of the dyadic exponent alone. -/
theorem atom {k p q e f : ℕ} (hp : p.Prime) (hq : q.Prime) (po : 2<p) (pq : p<q) (ep : 0<e)
    (eq : OeisA245212.a (2^k*p^e*q^f)=(σ 1 (2^k*p^e*q^f):ℤ)) :
    (p≤Q k ∧ e≤E k) ∨ (q≤Q k ∧ f≤E k) := by
  let A := W (2^k)
  let t := T k
  let u := p-1
  let v := q-1
  have tpos : 0<t := by dsimp [t,T]; positivity
  have pr : p=u+1 := by dsimp [u]; omega
  have qr : q=v+1 := by dsimp [v]; omega
  have up : 0<u := by omega
  have vp : 0<v := by omega
  have uv : u≤v := by omega
  have coeff : X 2 (some k)*(t:ℚ)=A := by
    simpa [t,T,A] using x_factor prime_two k
  have raw := OMA.DyadicEuler245212.pair_norm k p q e f hp hq po pq eq
  have ypos := mul_pos (OMA.FixedExponents245212.y_pos prime_two k)
    (mul_pos (OMA.FixedExponents245212.y_pos hp e) (OMA.FixedExponents245212.y_pos hq f))
  have score : X 2 (some k)*(X p (some e)*X q (some f))<2 := by linarith only [raw,ypos]
  have strict : (A:ℚ)*(X p (some e)*X q (some f))<2*(t:ℚ) := by
    calc
      _ = (X 2 (some k)*(X p (some e)*X q (some f)))*t := by rw [←coeff]; ring
      _ < _ := mul_lt_mul_of_pos_right score (by exact_mod_cast tpos)
  have cd : X 2 (some k)+Y 2 (some k)=2 := by simp only [X]; norm_num; ring
  have cost : X 2 (some k)<2 := by linarith only [cd,OMA.FixedExponents245212.y_pos prime_two k]
  have a : A<2*t := by
    exact_mod_cast (show (A:ℚ)<2*(t:ℚ) by rw [←coeff]; gcongr)
  have pu : limitX p*(u:ℚ)=p := by simpa [limitX,u,Y] using scaledX p hp.one_lt none
  have qv : limitX q*(v:ℚ)=q := by simpa [limitX,v,Y] using scaledX q hq.one_lt none
  have needed := OMA.DyadicEuler245212.pair_cap k p q e f hp hq po pq ep eq
  have cap : 2*t*u*v≤A*p*q := by
    have eqprod : X 2 (some k)*(limitX p*limitX q)*(t*u*v:ℚ)=A*p*q := by
      rw [←coeff,←pu,←qv]; ring
    have compare := mul_le_mul_of_nonneg_right needed (show 0≤(t:ℚ)*u*v by positivity)
    rw [eqprod] at compare
    exact_mod_cast (show (2:ℚ)*t*u*v≤A*p*q by linarith only [compare])
  have oddA : Odd A := OMA.DyadicPower245212.dyadic_odd k
  have oddP := hp.odd_of_ne_two (by omega)
  have oddQ := hq.odd_of_ne_two (by omega)
  have big : 2*t*u*v<A*p*q := cap.lt_of_ne (by
    intro h
    have ev : Even (2*t*u*v) := (((even_two.mul_right t).mul_right u).mul_right v)
    exact Nat.not_even_iff_odd.mpr ((oddA.mul oddP).mul oddQ) (h ▸ ev))
  have pBound := small_first a pr qr uv vp big
  have pqmax : p≤Q k := by unfold Q; change p≤2*t*(6*t+1)+1; nlinarith only [pBound,tpos]
  by_cases under : A*p<2*t*u
  · have qBound := (small_second a qr big under).trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ pBound) 1)
    change q≤Q k at qBound
    have degree := small_exp up vp hp hq big (scaledX p hp.one_lt _) (scaledX q hq.one_lt _) strict
    have total : 2*A*(p+q)≤E k := by
      have h := Nat.mul_le_mul (Nat.mul_le_mul_left 2 a.le) (Nat.add_le_add pqmax qBound)
      unfold E; change _≤8*t*Q k; nlinarith only [h]
    rcases le_total e f with h|h
    · rw [min_eq_left h] at degree; exact Or.inl ⟨pqmax,(Nat.le_succ e).trans (degree.trans total)⟩
    · rw [min_eq_right h] at degree; exact Or.inr ⟨qBound,(Nat.le_succ f).trans (degree.trans total)⟩
  · have above : 2*t*u<A*p := lt_of_le_of_ne (by omega) (by
      intro h; exact Nat.not_even_iff_odd.mpr (oddA.mul oddP) (h ▸ ((even_two.mul_right t).mul_right u)))
    have xq : 1≤X q (some f) := le_add_of_nonneg_right (div_nonneg (sub_nonneg.mpr (y_one hq.one_lt _))
      (sub_nonneg.mpr (by exact_mod_cast hq.one_le)))
    have single := (mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (x_nonneg hp.one_lt _) xq)
      (Nat.cast_nonneg A : (0:ℚ)≤A)).trans_lt strict
    have degree := one_exp hp up above single (scaledX p hp.one_lt _)
    have total : 2*A≤E k := by
      have one : 1≤Q k := by unfold Q; omega
      have h := Nat.mul_le_mul (Nat.mul_le_mul_left 2 a.le) one
      unfold E; change _≤8*t*Q k; nlinarith only [h]
    exact Or.inl ⟨pqmax,(Nat.le_succ e).trans (degree.trans total)⟩


theorem last_square {h q f : ℕ} (hh : 0<h) (hq : q.Prime) (qo : q≠2)
    (cop : h.Coprime q) (positive : 0<f)
    (eq : OeisA245212.a (h*q^f)=(σ 1 (h*q^f):ℤ)) : q^f≤(W h+σ 1 h)^2 := by
  let A := W h
  let S := σ 1 h
  have dv := OMA.OddCofactor245212.last_dvd hh hq cop positive eq
  have sp : 0<S := sigma_pos 1 h hh.ne'
  have small : q≤A+S := Nat.le_of_dvd (by omega) dv
  have pow := OMA.PrimePowerDiv245212.cofactor_bound hh hq qo cop f eq
  have bound : ((A:ℤ)-((q:ℤ)-1)*(S:ℤ)).natAbs≤q*(A+S) := by
    apply Int.ofNat_le.mp
    rw [Int.natCast_natAbs]; push_cast
    have q1 : (1:ℤ)≤q := by exact_mod_cast hq.one_le
    apply abs_le.mpr
    constructor <;> nlinarith only [Int.natCast_nonneg A,Int.natCast_nonneg S,
      mul_nonneg (sub_nonneg.mpr q1) (Int.natCast_nonneg A),
      mul_nonneg (sub_nonneg.mpr q1) (Int.natCast_nonneg S)]
  exact (pow.trans bound).trans (by simpa only [sq] using Nat.mul_le_mul_right (A+S) small)

def Box (k p q e f : ℕ) := p≤Q k ∧ e≤E k ∧
  q^f≤(W (2^k*p^e)+σ 1 (2^k*p^e))^2

theorem box {k p q e f : ℕ} (hp : p.Prime) (hq : q.Prime) (po : 2<p) (pq : p<q)
    (ep : 0<e) (fp : 0<f) (eq : OeisA245212.a (2^k*p^e*q^f)=(σ 1 (2^k*p^e*q^f):ℤ)) :
    Box k p q e f ∨ Box k q p f e := by
  have last {r s i j : ℕ} (rp : r.Prime) (sp : s.Prime) (so : 2<s) (ne : r≠s) (jp : 0<j)
      (bal : OeisA245212.a (2^k*r^i*s^j)=(σ 1 (2^k*r^i*s^j):ℤ)) :
      s^j≤(W (2^k*r^i)+σ 1 (2^k*r^i))^2 := by
    have cop : (2^k*r^i).Coprime s := (((Nat.coprime_primes prime_two sp).mpr (by omega)).pow_left k).mul_left
      (((Nat.coprime_primes rp sp).mpr ne).pow_left i)
    exact last_square (by have := rp.pos; positivity) sp (by omega) cop jp bal
  obtain ⟨pB,eB⟩|⟨qB,fB⟩ := atom hp hq po pq ep eq
  · exact Or.inl ⟨pB,eB,last hp hq (po.trans pq) pq.ne fp eq⟩
  · exact Or.inr ⟨qB,fB,last hq hp po pq.ne' ep (by simpa only [mul_right_comm (2^k)] using eq)⟩


private theorem count_le (h : ℕ) : h.divisors.card≤h := by
  have inc : h.divisors⊆Icc 1 h := by
    intro d hd
    exact mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,Nat.le_of_dvd (Nat.pos_of_ne_zero (mem_divisors.mp hd).2)
      (dvd_of_mem_divisors hd)⟩
  simpa using Finset.card_le_card inc

theorem moment_bound {h : ℕ} (hh : 0<h) : W h+σ 1 h≤2*h^3 := by
  have w : W h≤h^3 := by
    rw [w_apply]
    calc
      _ ≤ ∑ _d∈h.divisors,(h^2 : ℕ) := sum_le_sum fun d hd => by
        have db := Nat.le_of_dvd hh (dvd_of_mem_divisors hd)
        simpa [sq] using Nat.mul_le_mul db ((count_le d).trans db)
      _ ≤ h^3 := by
        simp only [sum_const,nsmul_eq_mul, Nat.cast_id]
        simpa only [show h^3=h*h^2 by ring] using Nat.mul_le_mul_right (h^2) (count_le h)
  have s : σ 1 h≤h^2 := by
    rw [sigma_one_apply]
    calc
      _ ≤ ∑ _d∈h.divisors,h := sum_le_sum fun _ hd => Nat.le_of_dvd hh (dvd_of_mem_divisors hd)
      _ ≤ h^2 := by simpa [sq] using Nat.mul_le_mul_right h (count_le h)
  have h23 : h^2≤h^3 := Nat.pow_le_pow_right hh (by decide)
  omega

def coreBound (k : ℕ) := 2^k*(Q k)^(E k)
def height (k : ℕ) := 4*(coreBound k)^7

private theorem combine {h v B : ℕ} (pos : 0<h) (small : h≤B) (large : v≤(W h+σ 1 h)^2) :
    h*v≤4*B^7 := by
  have vBound := large.trans (Nat.pow_le_pow_left (moment_bound pos) 2)
  calc
    _ ≤ h*((2*h^3)^2) := Nat.mul_le_mul_left _ vBound
    _ = 4*h^7 := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left small 7)

private theorem height_of_box {k p q e f : ℕ} (hp : p.Prime) (b : Box k p q e f) :
    2^k*p^e*q^f≤height k := by
  obtain ⟨pq,eb,qf⟩ := b
  have qpos : 0<Q k := by unfold Q; omega
  have small : p^e≤(Q k)^(E k) := (Nat.pow_le_pow_left pq e).trans (Nat.pow_le_pow_right qpos eb)
  exact combine (by have := hp.pos; positivity) (Nat.mul_le_mul_left (2^k) small) qf

/-- Every solution with at most two distinct odd primes lies below an
explicit height depending on the dyadic exponent alone. -/
theorem bounded {k m : ℕ} (om : Odd m) (hm : 1 < m) (rank : m.primeFactors.card≤2)
    (eq : OeisA245212.a (2^k*m)=(σ 1 (2^k*m):ℤ)) : 2^k*m≤height k := by
  classical
  have props {p : ℕ} (mem : p ∈ m.primeFactors) : p.Prime ∧ 2 < p ∧ 0 < m.factorization p := by
    have pr := Nat.prime_of_mem_primeFactors mem
    have dv := Nat.dvd_of_mem_primeFactors mem
    have od := Nat.coprime_two_left.mp ((Nat.coprime_two_left.mpr om).of_dvd_right dv)
    have ne : p≠2 := by rintro rfl; exact (by decide : ¬Odd 2) od
    exact ⟨pr,lt_of_le_of_ne pr.two_le ne.symm,pr.factorization_pos_of_dvd om.pos.ne' dv⟩
  have repr := Nat.prod_primeFactors_pow_factorization om.pos.ne'
  by_cases two : m.primeFactors.card=2
  · obtain ⟨p,q,diff,s⟩ := card_eq_two.mp two
    obtain ⟨hp,po,ep⟩ := props (p:=p) (by simp [s])
    obtain ⟨hq,qo,fp⟩ := props (p:=q) (by simp [s])
    rw [s,prod_insert (by simpa using diff),prod_singleton] at repr
    have target := congrArg (2^k*·) repr
    rw [←mul_assoc] at target
    rw [target] at eq ⊢
    rcases lt_or_gt_of_ne diff with pq|qp
    · rcases box hp hq po pq ep fp eq with b|b
      · exact height_of_box hp b
      · simpa only [mul_right_comm (2^k)] using height_of_box hq b
    · rw [mul_right_comm (2^k)] at eq ⊢
      rcases box hq hp qo qp fp ep eq with b|b
      · exact height_of_box hq b
      · simpa only [mul_right_comm (2^k)] using height_of_box hp b
  · have nonempty := Nat.nonempty_primeFactors.mpr hm
    have card := Finset.card_pos.mpr nonempty
    obtain ⟨p,s⟩ := card_eq_one.mp (show m.primeFactors.card=1 by omega)
    obtain ⟨hp,po,ep⟩ := props (p:=p) (by simp [s])
    rw [s,prod_singleton] at repr
    have target := congrArg (2^k*·) repr
    rw [target] at eq ⊢
    have cop := ((Nat.coprime_primes prime_two hp).mpr (by omega)).pow_left k
    have pB := last_square (by positivity) hp (by omega) cop ep eq
    have small : 2^k≤coreBound k := Nat.le_mul_of_pos_right _ (Nat.pow_pos (by unfold Q; omega))
    exact combine (by positivity) small pB

end OMA.PairHeight245212

end

section

/- Effective recovery of the only possible last prime from its cofactor
and exponent, by bounding the lower digits in the divisor identity. -/
namespace OMA.LastDigit245212
open Finset ArithmeticFunction OMA.Smooth245212 OMA.Abundance245212
open scoped ArithmeticFunction.sigma

def digitSum (p A S e : ℕ) := ∑ j∈range e,p^j*(A*(j+1)+S)
def denom (A S T d : ℕ) := 2*T*(d+1)-(A*(d+1)+S)

private theorem digit_pos {p A S d : ℕ} (hs : 0<S) (hd : 0<d) :
    0<digitSum p A S d := by
  apply sum_pos' (fun _ _ => Nat.zero_le _)
  exact ⟨0,mem_range.mpr hd,by simpa using (show 0<A+S by omega)⟩

theorem geom (p e : ℕ) (hp : 1≤p) :
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

end

section

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

/- Certify extensions of an arbitrary fixed cofactor without factoring its
divisor moments or iterating over prime bases. -/
namespace OMA.PairExtension245212
open Nat Finset ArithmeticFunction OMA.Smooth245212 OMA.LastDigit245212 OMA.Large245212
open scoped ArithmeticFunction.sigma
open OMA.Large245212 (force)
open OMA.Large245212 (moments)

/-- Even when the last prime is unknown, its exponent needs at most a
logarithmic scan in the sizes of the two known cofactor moments. -/
theorem last_log_base {a q f b : ℕ} (ha : 0<a) (hq : q.Prime) (oq : q≠2) (cop : a.Coprime q)
    (base : 1<b) (below : b≤q)
    (pos : 0<f) (eq : OeisA245212.a (a*q^f)=(σ 1 (a*q^f):ℤ)) :
    f≤Nat.log b (W a+σ 1 a)+1 := by
  obtain ⟨g,rfl⟩ := Nat.exists_eq_succ_of_ne_zero pos.ne'
  have raw := OMA.PrimePowerDiv245212.cofactor_bound ha hq oq cop (g+1) eq
  let A := W a
  let S := σ 1 a
  have q1 : (1:ℤ)≤q := by exact_mod_cast hq.one_le
  have absBound : ((A:ℤ)-((q:ℤ)-1)*(S:ℤ)).natAbs≤q*(A+S) := by
    apply Int.ofNat_le.mp
    rw [Int.natCast_natAbs]
    push_cast
    apply abs_le.mpr
    constructor <;> nlinarith only [Int.natCast_nonneg A,Int.natCast_nonneg S,
      mul_nonneg (sub_nonneg.mpr q1) (Int.natCast_nonneg A),
      mul_nonneg (sub_nonneg.mpr q1) (Int.natCast_nonneg S)]
  have power := raw.trans absBound
  change q^(g+1)≤q*(A+S) at power
  rw [pow_succ'] at power
  have small := (Nat.pow_le_pow_left below g).trans (Nat.le_of_mul_le_mul_left power hq.pos)
  have sz : 0<S := sigma_pos 1 a ha.ne'
  exact Nat.add_le_add_right ((Nat.le_log_iff_pow_le base (by omega)).mpr small) 1

theorem last_log {a q f : ℕ} (ha : 0<a) (hq : q.Prime) (oq : q≠2) (cop : a.Coprime q)
    (pos : 0<f) (eq : OeisA245212.a (a*q^f)=(σ 1 (a*q^f):ℤ)) :
    f≤(W a+σ 1 a).log2+1 := by
  rw [Nat.log2_eq_log_two]
  exact last_log_base ha hq oq cop (by decide) hq.two_le pos eq

/-- The leading digit forces a large last prime when the cofactor's
weighted moment is close to twice its weighted divisor count. -/
def lowerBase (R A T : ℕ) := max 2 (max R (A/(2*(2*T-A))))

theorem lowerBase_le {R A S T q f : ℕ} (q2 : 2≤q) (rq : R≤q) (fp : 0<f)
    (pos : 0<denom A S T f) (digit : A*f+S≤denom A S T f*q) : lowerBase R A T≤q := by
  have a : A<2*T := by
    by_contra! le
    have ge := Nat.mul_le_mul_right (f+1) le
    unfold denom at pos; omega
  have gd : 0<2*T-A := Nat.sub_pos_of_lt a
  have cap : denom A S T f≤(2*T-A)*(f+1) := by
    rw [Nat.sub_mul]; unfold denom; omega
  have two : (2*T-A)*(f+1)≤(2*T-A)*(2*f) := Nat.mul_le_mul_left _ (by omega)
  have lim := digit.trans (Nat.mul_le_mul_right q (cap.trans two))
  have val : A*f≤(2*(2*T-A)*q)*f := by nlinarith only [lim,Nat.zero_le S]
  have num := Nat.le_of_mul_le_mul_right val fp
  have le : A/(2*(2*T-A))≤q := by
    exact (Nat.div_le_div_right num).trans_eq (by rw [Nat.mul_comm (2*_) q,Nat.mul_div_cancel _ (by omega)])
  exact max_le q2 (max_le rq le)

def permitted (A S T q f : ℕ) : Bool :=
  decide (q∣A+S) && decide (A*wt q f+S*sig q f=2*T*OMA.Large245212.tax q f)

theorem fit {a q f : ℕ} (ha : 0<a) (hq : q.Prime) (cop : a.Coprime q)
    (hf : 0<f) (eq : OeisA245212.a (a*q^f)=(σ 1 (a*q^f):ℤ)) :
    permitted (W a) (σ 1 a) (a*(σ 0 a)) q f=true := by
  obtain ⟨ss,ww⟩ := OMA.Large245212.moments hq f
  have b := OMA.Abundance245212.balance (mul_ne_zero ha.ne' (pow_ne_zero _ hq.ne_zero)) eq
  have cf := cop.pow_right f
  rw [w_mult.map_mul_of_coprime cf,isMultiplicative_sigma.map_mul_of_coprime cf,
    isMultiplicative_sigma.map_mul_of_coprime cf,sigma_zero_apply_prime_pow hq] at b
  simp only [permitted,Bool.and_eq_true,decide_eq_true_eq,ss,ww,OMA.Large245212.tax]
  exact ⟨OMA.OddCofactor245212.last_dvd ha hq cop hf eq,by linear_combination b⟩

def free (R A S T : ℕ) : Bool := (List.range (Nat.log (lowerBase R A T) (A+S)+1)).all fun i =>
  let f := i+1
  let q := candidate A S T f
  decide (denom A S T f=0 ∨ q<R) || !permitted A S T q f

theorem free_sound {a q f R : ℕ} (ha : 0<a) (hq : q.Prime) (oq : q≠2) (cop : a.Coprime q)
    (hf : 0<f) (lo : R≤q) (check : free R (W a) (σ 1 a) (a*(σ 0 a))=true) :
    OeisA245212.a (a*q^f)≠(σ 1 (a*q^f):ℤ) := by
  intro eq
  obtain ⟨g,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hf.ne'
  obtain ⟨pos,low,high,_⟩ := balance_digits ha hq cop hf eq
  have base := lowerBase_le hq.two_le lo hf pos high
  have limit := last_log_base (b:=lowerBase R (W a) (a*(σ 0 a))) ha hq oq cop
    (lt_of_lt_of_le (by decide : 1<2) (le_max_left _ _)) base hf eq
  have val := OMA.Large245212.force (sigma_pos 1 a ha.ne') hq.one_lt pos low high
  have h := List.all_eq_true.mp check g (List.mem_range.mpr (by omega))
  simp [val,pos.ne',Nat.not_lt_of_ge lo,fit ha hq cop hf eq] at h

def known (A S T q : ℕ) : Bool :=
  let C := OMA.ReverseDigit245212.numerator q A S
  let D := OMA.ReverseDigit245212.denominator q A T
  if ¬q∣A+S ∨ D=0 then true else
    let f := (⌊C/D⌋-1).toNat
    Bool.not (permitted A S T q f)

theorem known_sound {a q f : ℕ} (ha : 0<a) (hq : q.Prime) (oq : q≠2) (cop : a.Coprime q)
    (hf : 0<f) (check : known (W a) (σ 1 a) (a*(σ 0 a)) q=true) :
    OeisA245212.a (a*q^f)≠(σ 1 (a*q^f):ℤ) := by
  intro eq
  obtain ⟨nz,_,recover⟩ := OMA.ReverseDigit245212.recover ha hq oq cop eq
  have dv := OMA.OddCofactor245212.last_dvd ha hq cop hf eq
  simp only [known,Nat.cast_mul] at check
  simp [dv,nz,recover,fit ha hq cop hf eq] at check

end OMA.PairExtension245212

end

section

/- Euler bounds and exact reconstruction for a fixed cofactor followed
by two odd prime powers. Neither odd exponent is prescribed. -/
namespace OMA.CofactorEulerPair245212
open Nat Finset ArithmeticFunction OMA.Smooth245212 OMA.OddFaces245212
open scoped ArithmeticFunction.sigma
open OMA.OddFaces245212 (envelope)
open OMA.FixedExponents245212 (y_pos)
open OMA.PairHeight245212 (scaledX)
open OMA.PairHeight245212 (small_exp)
open OMA.Large245212 (moments)

theorem normalized {h p q a d : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime)
    (cp : h.Coprime p) (cq : h.Coprime q) (pq : p≠q)
    (eqn : OeisA245212.a (h*p^a*q^d)=(σ 1 (h*p^a*q^d):ℤ)) :
    (W h:ℚ)*(X p (some a)*X q (some d))+(σ 1 h:ℚ)*(Y p (some a)*Y q (some d))=
      2*(h*σ 0 h:ℕ) := by
  have hc := (cq.mul_left (((Nat.coprime_primes hp hq).mpr pq).pow_left a)).pow_right d
  have hp0 := hp.pos
  have hq0 := hq.pos
  have b := OMA.Abundance245212.balance (show h*p^a*q^d≠0 by positivity) eqn
  rw [w_mult.map_mul_of_coprime hc,w_mult.map_mul_of_coprime (cp.pow_right a),
    isMultiplicative_sigma.map_mul_of_coprime hc,isMultiplicative_sigma.map_mul_of_coprime (cp.pow_right a),
    isMultiplicative_sigma.map_mul_of_coprime hc,isMultiplicative_sigma.map_mul_of_coprime (cp.pow_right a),
    sigma_zero_apply_prime_pow hp,sigma_zero_apply_prime_pow hq] at b
  have eqQ := congrArg ((↑):ℕ→ℚ) b
  push_cast at eqQ ⊢
  apply mul_right_cancel₀ (b:=(((a:ℚ)+1)*p^a)*(((d:ℚ)+1)*q^d)) (by positivity)
  rw [←x_factor hp a,←x_factor hq d,←y_factor hp a,←y_factor hq d] at eqQ
  linear_combination eqQ

theorem cap {p q a d : ℕ} {A S H : ℚ} (hp : 1<p) (hq : 1<q) (pos : 0<a)
    (wp : 0≤A) (sub : A+S≤H)
    (bal : A*(X p (some a)*X q (some d))+S*(Y p (some a)*Y q (some d))=H) :
    H≤A*(limitX p*limitX q) := by
  let t:=Y p (some a)*Y q (some d)
  let C:=limitX p*limitX q
  have y0 : 0≤t := mul_nonneg (y_nonneg hp _) (y_nonneg hq _)
  have y1 : t<1 := by
    have z := OMA.Abundance245212.y_strict hp pos
    exact (mul_le_of_le_one_right (y_nonneg hp _) (y_one hq _)).trans_lt (by simpa [y_avg hp] using z)
  have env := OMA.OddFaces245212.envelope univ (![p,q]:Fin 2→ℕ) ![a,d]
    (by intro i;fin_cases i <;> assumption)
  simp only [Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one] at env
  change _≤t+(1-t)*C at env
  change A*_+S*t=H at bal
  change H≤A*C
  by_contra! low
  nlinarith only [bal,mul_le_mul_of_nonneg_left env wp,
    mul_le_mul_of_nonneg_right sub y0,mul_pos (sub_pos.mpr y1) (sub_pos.mpr low)]

/-- Positive Euler excess bounds the smaller exponent. Only the sign is
needed here, so a single table covers every fixed pair of prime bases. -/
theorem short {h p q a d : ℕ} (hp : p.Prime) (hq : q.Prime) (hh : 0<h)
    (excess : 2*(h*σ 0 h)*(p-1)*(q-1)<W h*p*q)
    (bal : (W h:ℚ)*(X p (some a)*X q (some d))+(σ 1 h:ℚ)*(Y p (some a)*Y q (some d))=
      2*(h*σ 0 h:ℕ)) : min a d+1≤2*W h*(p+q) := by
  have s : (0:ℚ)<(σ 1 h:ℕ) := by exact_mod_cast sigma_pos 1 h hh.ne'
  have strict := mul_pos s (mul_pos (OMA.FixedExponents245212.y_pos hp a) (OMA.FixedExponents245212.y_pos hq d))
  exact OMA.PairHeight245212.small_exp (Nat.sub_pos_of_lt hp.one_lt) (Nat.sub_pos_of_lt hq.one_lt)
    hp hq excess (OMA.PairHeight245212.scaledX p hp.one_lt _) (OMA.PairHeight245212.scaledX q hq.one_lt _)
    (by linarith only [strict,bal])

def row (A S T p q e : ℕ) := OMA.PairExtension245212.known
  (A*OMA.Large245212.wt p e) (S*OMA.Large245212.sig p e) (T*OMA.Large245212.tax p e) q

theorem row_sound {h p q e f : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime) (oq : q≠2)
    (cp : h.Coprime p) (cq : h.Coprime q) (pq : p≠q) (fp : 0<f)
    (check : row (W h) (σ 1 h) (h*σ 0 h) p q e=true) :
    OeisA245212.a (h*p^e*q^f)≠(σ 1 (h*p^e*q^f):ℤ) := by
  have c := cp.pow_right e
  obtain ⟨sg,wt⟩:=OMA.Large245212.moments hp e
  have pp:=hp.pos
  apply OMA.PairExtension245212.known_sound (by positivity) hq oq
    (cq.mul_left (((Nat.coprime_primes hp hq).mpr pq).pow_left e)) fp
  rw [w_mult.map_mul_of_coprime c,isMultiplicative_sigma.map_mul_of_coprime c,
    isMultiplicative_sigma.map_mul_of_coprime c,sigma_zero_apply_prime_pow hp]
  simpa only [row,wt,sg,OMA.Large245212.tax,mul_assoc,mul_comm,mul_left_comm] using check

def table (A S T p q E : ℕ) := (List.range E).all fun i => row A S T p q (i+1)

theorem table_sound {h p q a d E : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime)
    (op : p≠2) (oq : q≠2) (cp : h.Coprime p) (cq : h.Coprime q) (pq : p≠q)
    (ap : 0<a) (dp : 0<d) (small : min a d≤E)
    (left : table (W h) (σ 1 h) (h*σ 0 h) p q E=true)
    (right : table (W h) (σ 1 h) (h*σ 0 h) q p E=true) :
    OeisA245212.a (h*p^a*q^d)≠(σ 1 (h*p^a*q^d):ℤ) := by
  by_cases order : a≤d
  · rw [min_eq_left order] at small
    obtain ⟨j,rfl⟩:=Nat.exists_eq_succ_of_ne_zero ap.ne'
    exact row_sound hh hp hq oq cp cq pq dp (List.all_eq_true.mp left j (List.mem_range.mpr (by omega)))
  · rw [min_eq_right (by omega)] at small
    obtain ⟨j,rfl⟩:=Nat.exists_eq_succ_of_ne_zero dp.ne'
    simpa only [mul_right_comm h] using
      row_sound hh hq hp op cq cp pq.symm ap (List.all_eq_true.mp right j (List.mem_range.mpr (by omega)))

end OMA.CofactorEulerPair245212

end

section

/- Effective prime and exponent cuts at the Euler limit. -/
namespace OMA.CofactorEulerPair245212
open Nat ArithmeticFunction OMA.Smooth245212 OMA.OddFaces245212
open scoped ArithmeticFunction.sigma
open OMA.PairHeight245212 (scaledX)
open OMA.FixedExponents245212 (y_pos)

theorem original_cap {h p q a d : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime)
    (cp : h.Coprime p) (cq : h.Coprime q) (pq : p≠q) (pos : 0<a)
    (sub : W h+σ 1 h≤2*(h*σ 0 h))
    (eqn : OeisA245212.a (h*p^a*q^d)=(σ 1 (h*p^a*q^d):ℤ)) :
    2*(h*σ 0 h)*(p-1)*(q-1) ≤ W h*p*q ∧
    (W h:ℚ)*(X p (some a)*X q (some d)) < 2*(h*σ 0 h:ℕ) := by
  have b := normalized hh hp hq cp cq pq eqn
  have c := cap hp.one_lt hq.one_lt pos (Nat.cast_nonneg _) (by exact_mod_cast sub) b
  have pref (r : ℕ) (pr : r.Prime) : limitX r*((r-1:ℕ):ℚ)=r := by
    simpa [limitX,Y] using OMA.PairHeight245212.scaledX r pr.one_lt none
  constructor
  · have v := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right c
      (Nat.cast_nonneg (p-1))) (Nat.cast_nonneg (q-1) : (0:ℚ)≤_)
    simp only [Nat.cast_mul] at v
    have rat : (2*(h*σ 0 h):ℕ)*(p-1:ℕ)*(q-1:ℕ) ≤ (W h*p*q:ℕ) := by
      apply (Nat.cast_le (α:=ℚ)).mp
      push_cast only [Nat.cast_mul,Nat.cast_ofNat]
      calc
        _ ≤ _ := v
        _ = (W h:ℚ)*(limitX p*((p-1:ℕ):ℚ))*(limitX q*((q-1:ℕ):ℚ)) := by ring
        _ = _ := by rw [pref p hp,pref q hq]
    exact rat
  · have s : (0:ℚ)<(σ 1 h:ℕ) := by exact_mod_cast sigma_pos 1 h hh.ne'
    linarith only [b,mul_pos s (mul_pos (OMA.FixedExponents245212.y_pos hp a) (OMA.FixedExponents245212.y_pos hq d))]

theorem first_bound {A H p q : ℕ} (hp : 1<p) (pq : p≤q) (small : A<H)
    (cap : H*(p-1)*(q-1)≤A*p*q) : p ≤ 1+3*A/(H-A) := by
  let u:=p-1
  let v:=q-1
  have pval : p=u+1 := by dsimp [u];omega
  have qval : q=v+1 := by dsimp [v];omega
  have dv := Nat.sub_add_cancel small.le
  have uv : u+v+1≤3*v := by omega
  have cost := Nat.mul_le_mul_left A uv
  change H*u*v≤A*p*q at cap
  have prod : (H-A)*u*v ≤ 3*A*v := by
    rw [pval,qval] at cap
    nlinarith only [cap,cost,congrArg (fun t:ℕ=>t*u*v) dv]
  have simple := Nat.le_of_mul_le_mul_right prod (show 0<v by omega)
  have div := (Nat.le_div_iff_mul_le (show 0<H-A by omega)).mpr (by rwa [mul_comm] : u*(H-A)≤3*A)
  omega

theorem second_bound {A H p q : ℕ} (hq : 1<q) (under : A*p<H*(p-1))
    (cap : H*(p-1)*(q-1)≤A*p*q) : q≤H*(p-1)/(H*(p-1)-A*p) := by
  apply (Nat.le_div_iff_mul_le (Nat.sub_pos_of_lt under)).mpr
  have d := Nat.sub_add_cancel under.le
  have v := Nat.sub_add_cancel (by omega : 1≤q)
  nlinarith only [cap,congrArg (q*·) d,congrArg (H*(p-1)*·) v]

theorem short_first {A H p q a d : ℕ} (hp : p.Prime) (hq : q.Prime)
    (excess : H*(p-1)<A*p) (small : (A:ℚ)*(X p (some a)*X q (some d)) < H) :
    a+1≤2*A/(A*p-H*(p-1)) := by
  let u:=p-1
  let E:=A*p-H*u
  have ext := Nat.sub_add_cancel excess.le
  have unit : 1≤X q (some d) := le_add_of_nonneg_right (div_nonneg (sub_nonneg.mpr (y_one hq.one_lt _))
    (sub_nonneg.mpr (by exact_mod_cast hq.one_le)))
  have mid := (mul_le_mul_of_nonneg_left
    (le_mul_of_one_le_right (x_nonneg hp.one_lt _) unit) (Nat.cast_nonneg A : (0:ℚ)≤A)).trans_lt small
  have sc := mul_lt_mul_of_pos_right mid (show (0:ℚ)<u by exact_mod_cast Nat.sub_pos_of_lt hp.one_lt)
  have id := OMA.PairHeight245212.scaledX p hp.one_lt (some a)
  have eq : (E:ℚ)+H*u=A*p := by exact_mod_cast ext
  have lower : (E:ℚ)≤A*Y p (some a) := by
    change X p (some a)*(u:ℚ)=_ at id
    nlinarith only [sc,eq,congrArg ((A:ℚ)*·) id]
  have top := mul_le_mul_of_nonneg_left (OMA.CapOrder245212.y_short hp a).le (Nat.cast_nonneg A : (0:ℚ)≤A)
  apply (Nat.le_div_iff_mul_le (Nat.sub_pos_of_lt excess)).mpr
  change (a+1)*E≤2*A
  exact_mod_cast (show ((a:ℚ)+1)*E≤2*A by
    nlinarith only [top,mul_le_mul_of_nonneg_left lower (show (0:ℚ)≤a+1 by positivity)])

theorem short_pair {A H p q a d : ℕ} (hp : p.Prime) (hq : q.Prime)
    (excess : H*(p-1)*(q-1)<A*p*q)
    (small : (A:ℚ)*(X p (some a)*X q (some d)) < H) :
    min a d+1≤2*A*(p+q)/(A*p*q-H*(p-1)*(q-1)) := by
  let u:=p-1
  let v:=q-1
  let E:=A*p*q-H*u*v
  let m:=min a d+1
  have eq : (E:ℚ)+H*u*v=A*p*q := by exact_mod_cast Nat.sub_add_cancel excess.le
  have id := congrArg₂ (·*·) (OMA.PairHeight245212.scaledX p hp.one_lt (some a))
    (OMA.PairHeight245212.scaledX q hq.one_lt (some d))
  let y:=Y p (some a)
  let z:=Y q (some d)
  change X p (some a)*u*(X q (some d)*v)=((p:ℚ)-y)*((q:ℚ)-z) at id
  have y0 := y_nonneg hp.one_lt (some a)
  have z0 := y_nonneg hq.one_lt (some d)
  have scale := mul_lt_mul_of_pos_right small
    (mul_pos (by exact_mod_cast Nat.sub_pos_of_lt hp.one_lt : (0:ℚ)<u)
      (by exact_mod_cast Nat.sub_pos_of_lt hq.one_lt : (0:ℚ)<v))
  have error : (E:ℚ)≤A*(p*z+q*y) := by
    nlinarith only [scale,eq,congrArg ((A:ℚ)*·) id,
      mul_nonneg (Nat.cast_nonneg A : (0:ℚ)≤A) (mul_nonneg y0 z0)]
  have yl : (m:ℚ)*y≤2 := (mul_le_mul_of_nonneg_right
    (by exact_mod_cast Nat.succ_le_succ (min_le_left a d) : (m:ℚ)≤a+1) y0).trans (by simpa [mul_comm] using (OMA.CapOrder245212.y_short hp a).le)
  have zl : (m:ℚ)*z≤2 := (mul_le_mul_of_nonneg_right
    (by exact_mod_cast Nat.succ_le_succ (min_le_right a d) : (m:ℚ)≤d+1) z0).trans (by simpa [mul_comm] using (OMA.CapOrder245212.y_short hq d).le)
  apply (Nat.le_div_iff_mul_le (Nat.sub_pos_of_lt excess)).mpr
  change m*E≤2*A*(p+q)
  exact_mod_cast (show (m:ℚ)*E≤2*A*(p+q) by
    nlinarith only [mul_le_mul_of_nonneg_left error (Nat.cast_nonneg m),
      mul_le_mul_of_nonneg_left yl (show (0:ℚ)≤A*q by positivity),
      mul_le_mul_of_nonneg_left zl (show (0:ℚ)≤A*p by positivity)])

end OMA.CofactorEulerPair245212

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

/- Exact identities for a fixed cofactor and two unrestricted odd primes.
At the exceptional Euler slope p*W(h)=2*h*τ(h)*(p-1), the first deficit
collapses to a multiple of the ordinary divisor sum. -/
namespace OMA.CofactorPairPole245212
open ArithmeticFunction OMA.Smooth245212
open scoped ArithmeticFunction.sigma

theorem balance {h p q a f : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime)
    (cp : h.Coprime p) (cq : h.Coprime q) (pq : p≠q)
    (eqn : OeisA245212.a (h*p^a*q^f)=(σ 1 (h*p^a*q^f):ℤ)) :
    (W h:ℤ)*W (p^a)*W (q^f)+(σ 1 h:ℤ)*σ 1 (p^a)*σ 1 (q^f)=
      2*((h:ℤ)*σ 0 h)*(a+1)*(f+1)*(p:ℤ)^a*(q:ℤ)^f := by
  have tq := (cq.mul_left (((Nat.coprime_primes hp hq).mpr pq).pow_left a)).pow_right f
  have tp := cp.pow_right a
  have pp := hp.pos
  have qp := hq.pos
  have b := OMA.Abundance245212.balance (show h*p^a*q^f≠0 by positivity) eqn
  rw [w_mult.map_mul_of_coprime tq,w_mult.map_mul_of_coprime tp,
    isMultiplicative_sigma.map_mul_of_coprime tq,isMultiplicative_sigma.map_mul_of_coprime tp,
    isMultiplicative_sigma.map_mul_of_coprime tq,isMultiplicative_sigma.map_mul_of_coprime tp,
    sigma_zero_apply_prime_pow hp,sigma_zero_apply_prime_pow hq] at b
  zify at b
  linear_combination b

/-- P=the smaller-prime power, U=its ordinary moment and W=its weighted
moment. No bound on the exponents or on the second prime enters. -/
theorem pole {A S T p B C P Q U W V Z : ℤ}
    (res : A*p=2*T*(p-1)) (wt : (p-1)*W+U=p*B*P)
    (eqn : A*W*V+S*U*Z=2*T*B*C*P*Q) :
    Q*(C*A-S*(p-1))*U =
      (p-1)*(A*W*(V-C*Q)+S*U*(Z-Q)) := by
  linear_combination -(p-1)*eqn+(A*C*Q)*wt+(B*C*P*Q)*res

theorem slope {p B P U W : ℤ} (sig : (p-1)*U=p*P-1)
    (wt : (p-1)*W+U=p*B*P) :
    (p-1)*W=(B*(p-1)-1)*U+B := by linear_combination wt-B*sig

/-- Integral versions of the bounds from the first omitted divisor. -/
theorem last_tail {q : ℕ} (hq : q.Prime) (odd : 3≤q) (d : ℕ) :
    let Q : ℤ := (q:ℤ)^(d+1)
    let C : ℤ := (d:ℤ)+2
    let V : ℤ := W (q^(d+1))
    let Z : ℤ := σ 1 (q^(d+1))
    (C-1)*Q≤q*(V-C*Q) ∧ q*(V-C*Q)≤2*C*Q ∧
      0≤Z-Q ∧ q*(Z-Q)≤2*Q := by
  dsimp only
  have ends := OMA.ComplementaryLocal245212.last hq odd d
  have b := OMA.ComplementaryLocal245212.bounds hq odd d
  have w : (W (q^(d+1)):ℤ)=((d:ℤ)+2)*(q:ℤ)^(d+1)+W (q^d) := by exact_mod_cast ends.1
  have s : (σ 1 (q^(d+1)):ℤ)=(q:ℤ)^(d+1)+σ 1 (q^d) := by exact_mod_cast ends.2.1
  have lb : ((d:ℤ)+1)*q^d≤W (q^d) := by exact_mod_cast b.2.2.1
  have ub : 2*(W (q^d):ℤ)≤3*((d:ℤ)+1)*q^d := by exact_mod_cast b.2.1
  have us : 2*(σ 1 (q^d):ℤ)≤3*(q:ℤ)^d := by exact_mod_cast b.1
  rw [w,s,pow_succ]
  constructor
  · nlinarith only [mul_le_mul_of_nonneg_left lb (Int.natCast_nonneg q)]
  constructor
  · nlinarith only [mul_le_mul_of_nonneg_left ub (Int.natCast_nonneg q),
      mul_nonneg (Int.natCast_nonneg q) (pow_nonneg (Int.natCast_nonneg q) d),
      mul_nonneg (Int.natCast_nonneg d) (mul_nonneg (Int.natCast_nonneg q)
        (pow_nonneg (Int.natCast_nonneg q) d))]
  constructor
  · linarith only [Int.natCast_nonneg (σ 1 (q^d))]
  · nlinarith only [mul_le_mul_of_nonneg_left us (Int.natCast_nonneg q),
      mul_nonneg (Int.natCast_nonneg q) (pow_nonneg (Int.natCast_nonneg q) d)]

/-- Under the exact Euler resonance the moving prime exceeds the
exponent length B once its own exponent is at least two. -/
theorem larger_than_length {A S u B C U W q : ℤ} (ap : 0<A) (sp : 0≤S)
    (up : 2≤u) (bp : 2≤B) (cp : 3≤C) (pos : 0<U) (qp : 0<q)
    (weight : u*W=(B*u-1)*U+B)
    (first : u*A*W*(C-1)≤q*(C*A-S*u)*U) : B<q := by
  have mid : B*C ≤ (B*u-1)*(C-1) := by
    nlinarith only [mul_nonneg (by omega : 0≤B-2) (by omega : 0≤C-2),
      mul_nonneg (by omega : 0≤C-3) (by omega : 0≤(1:ℤ)),
      mul_nonneg (mul_nonneg (by omega : 0≤B) (by omega : 0≤u-2)) (by omega : 0≤C-1)]
  by_contra! small
  have lhs := mul_le_mul_of_nonneg_right mid (mul_nonneg ap.le pos.le)
  have rhs := mul_le_mul_of_nonneg_right small (mul_nonneg (mul_nonneg (by omega : 0≤C) ap.le) pos.le)
  have spill := mul_nonneg (mul_nonneg qp.le (mul_nonneg sp (by omega : 0≤u))) pos.le
  have extra := mul_pos (mul_pos ap (by omega : 0<B)) (by omega : 0<C-1)
  nlinarith only [first,lhs,rhs,spill,extra,congrArg (fun z:ℤ => z*A*(C-1)) weight]

/-- A positive integral deficit gives a linear upper bound on the
moving prime, uniformly in both exponents. -/
theorem linear_upper {A S u B C q : ℤ} (ap : 1≤A) (sp : 0≤S) (up : 0<u)
    (bp : 1≤B) (cp : 1≤C) (gap : 0<C*A-S*u)
    (upper : q*(C*A-S*u)≤2*u*(A*B*C+S)) :
    q≤2*u*(A+S)*(S*u+1)*B := by
  let D := C*A-S*u
  have dp : 1≤D := by dsimp [D]; omega
  have len : C≤(S*u+1)*D := by
    have a := mul_nonneg (by omega : 0≤C) (by omega : 0≤A-1)
    have b := mul_nonneg (mul_nonneg sp up.le) (sub_nonneg.mpr dp)
    dsimp [D] at *; nlinarith only [a,b]
  have bc : 1≤B*C := by nlinarith only [mul_nonneg (by omega : 0≤B-1) (by omega : 0≤C),cp]
  have cost := mul_nonneg sp (sub_nonneg.mpr bc)
  have bound := mul_le_mul_of_nonneg_left len (show 0≤(A+S)*B by positivity)
  apply le_of_mul_le_mul_right (a:=D) _ (by omega : 0<D)
  calc
    q*D ≤ 2*u*(A*B*C+S) := upper
    _ ≤ 2*u*((A+S)*B*((S*u+1)*D)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith only [bound,cost]
    _ = _ := by ring

/-- Extract the two scalar inequalities from the exact identity before
cancelling the positive last prime power. -/
theorem sandwich {A S u B C U W V Z Q q : ℤ}
    (ap : 0<A) (sp : 0≤S) (up : 0<u) (wp : 0<W) (pos : 0<U) (qp : 0<q)
    (big : 0<Q) (len : 1<C) (wt : W≤B*U)
    (id : Q*(C*A-S*u)*U=u*(A*W*(V-C*Q)+S*U*(Z-Q)))
    (wl : (C-1)*Q≤q*(V-C*Q)) (wh : q*(V-C*Q)≤2*C*Q)
    (sl : 0≤Z-Q) (sh : q*(Z-Q)≤2*Q) :
    0<C*A-S*u ∧ u*A*W*(C-1)≤q*(C*A-S*u)*U ∧
      q*(C*A-S*u)≤2*u*(A*B*C+S) := by
  have a0 := mul_nonneg up.le (mul_nonneg ap.le wp.le)
  have s0 := mul_nonneg up.le (mul_nonneg sp pos.le)
  have first : u*A*W*(C-1)≤q*(C*A-S*u)*U := by
    apply le_of_mul_le_mul_right (a:=Q) _ big
    nlinarith only [congrArg (fun z:ℤ => q*z) id,mul_le_mul_of_nonneg_left wl a0,
      mul_nonneg (mul_nonneg s0 qp.le) sl]
  refine ⟨?_,first,?_⟩
  · by_contra! bad
    nlinarith only [first,mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos qp.le bad) pos.le,
      mul_pos (mul_pos (mul_pos up ap) wp) (by omega : 0<C-1)]
  · apply le_of_mul_le_mul_right (a:=U*Q) _ (mul_pos pos big)
    have weight := mul_le_mul_of_nonneg_right wt (show 0≤2*u*A*C*Q by positivity)
    nlinarith only [congrArg (fun z:ℤ => q*z) id,mul_le_mul_of_nonneg_left wh a0,
      mul_le_mul_of_nonneg_left sh s0,weight]

def defect (A S T p q B C : ℤ) :=
  2*T*B*C*(p-1)^2*(q-1)^2 -
    p*q*(A*(B*(p-1)-1)*(C*(q-1)-1)+S*(p-1)*(q-1))

/-- At resonance the last base is at most a fixed multiple of the first
exponent length. From last exponent two on, it is strictly above that length. -/
theorem original_slope {h p q a d : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime)
    (op : 3≤p) (oq : 3≤q) (cp : h.Coprime p) (cq : h.Coprime q) (pq : p≠q)
    (res : (W h:ℤ)*p=2*((h:ℤ)*σ 0 h)*(p-1))
    (eqn : OeisA245212.a (h*p^a*q^(d+1))=(σ 1 (h*p^a*q^(d+1)):ℤ)) :
    (q:ℤ) ≤ 2*((p:ℤ)-1)*(W h+((σ 1 h:ℕ):ℤ))*((σ 1 h:ℤ)*(p-1)+1)*(a+1) ∧
    (0<a → 0<d → a+1<q) := by
  let U : ℤ := σ 1 (p^a)
  let Wp : ℤ := W (p^a)
  let B : ℤ := a+1
  let C : ℤ := d+2
  have up : 0<U := by dsimp [U]; exact_mod_cast sigma_pos 1 (p^a) (pow_ne_zero _ hp.ne_zero)
  have wp : 0<Wp := by
    have r := (OMA.ComplementaryLocal245212.bounds hp op a).2.2.2
    change (0:ℤ)<W (p^a)
    exact_mod_cast lt_of_lt_of_le (sigma_pos 1 (p^a) (pow_ne_zero _ hp.ne_zero)) r
  have ap : (0:ℤ)<W h := by
    have base : h∈h.divisors := Nat.mem_divisors.mpr ⟨dvd_refl h,hh.ne'⟩
    rw [w_apply]
    exact_mod_cast Finset.sum_pos' (f:=fun i : ℕ => i*i.divisors.card) (fun i _=>Nat.zero_le _) ⟨h,base,
      Nat.mul_pos hh (Finset.card_pos.mpr ⟨h,base⟩)⟩
  have wt := OMA.PrimePowerDiv245212.weighted hp a
  zify [Nat.cast_sub hp.pos] at wt
  have w : ((p:ℤ)-1)*Wp+U=p*B*(p:ℤ)^a := by dsimp [Wp,U,B];linear_combination wt
  have xy : Wp≤B*U := by
    change (W (p^a):ℤ)≤((a:ℤ)+1)*σ 1 (p^a)
    exact_mod_cast (show W (p^a)≤(a+1)*σ 1 (p^a) by
      rw [w_pow hp,sigma_one_apply_prime_pow hp,Finset.mul_sum]
      exact Finset.sum_le_sum fun j hj => by
        rw [Nat.mul_comm (a+1)]
        exact Nat.mul_le_mul_left _ (by have := Finset.mem_range.mp hj; omega))
  have raw := balance hh hp hq cp cq pq eqn
  have id := pole (B:=B) (C:=C) (Q:=(q:ℤ)^(d+1)) res w
    (show (W h:ℤ)*Wp*W (q^(d+1))+(σ 1 h:ℤ)*U*σ 1 (q^(d+1))=
      2*((h:ℤ)*σ 0 h)*B*C*(p:ℤ)^a*(q:ℤ)^(d+1) by
      dsimp [B,C,Wp,U];push_cast at raw;linear_combination raw)
  obtain ⟨lo,hi,lo',hi'⟩ := last_tail hq oq d
  obtain ⟨gap,first,last⟩ := sandwich (B:=B) ap (Int.natCast_nonneg _)
    (by omega : (0:ℤ)<p-1) wp up (by omega : (0:ℤ)<q)
    (pow_pos (by omega : (0:ℤ)<q) _) (by dsimp [C]; omega) xy id lo hi lo' hi'
  refine ⟨linear_upper (B:=B) (C:=C) (by omega) (Int.natCast_nonneg _) (by omega)
    (by dsimp [B];omega) (by dsimp [C];omega) gap last,?_⟩
  intro ea ed
  have sl := slope (OMA.ComplementaryLocal245212.moments hp a).1 w
  have result := larger_than_length ap (Int.natCast_nonneg _) (by omega : (2:ℤ)≤p-1)
    (by dsimp [B];omega) (by dsimp [C];omega) up (by omega : (0:ℤ)<q) sl first
  dsimp [B] at result
  exact_mod_cast result

theorem tails (A S T p q B C P Q W V U Z : ℤ)
    (pw : (p-1)^2*W=p*(B*(p-1)-1)*P+1)
    (qw : (q-1)^2*V=q*(C*(q-1)-1)*Q+1)
    (ps : (p-1)*U=p*P-1) (qs : (q-1)*Z=q*Q-1)
    (eqn : A*W*V+S*U*Z=2*T*B*C*P*Q) :
    defect A S T p q B C*P*Q =
      q*(A*(C*(q-1)-1)-S*(p-1)*(q-1))*Q+
      p*(A*(B*(p-1)-1)-S*(p-1)*(q-1))*P+A+S*(p-1)*(q-1) := by
  unfold defect
  linear_combination A*((q-1)^2*V)*pw+A*(p*(B*(p-1)-1)*P+1)*qw+
    S*(p-1)*(q-1)*((q-1)*Z)*ps+S*(p-1)*(q-1)*(p*P-1)*qs-
    ((p-1)^2*(q-1)^2)*eqn

/-- The rounded integer cannot vanish when q is above the two lengths
and the fixed cofactor; no ordering between the two powers is needed. -/
theorem separated {A S T p q B C : ℕ} (hq : q.Prime) (op : 2≤p) (pq : p<q)
    (ht : 0<T) (hb : 0<B) (hc : 0<C) (qt : 2*T<q) (qb : B<q) (qc : C<q) :
    defect A S T p q B C≠0 := by
  intro zero
  let : Fact q.Prime := ⟨hq⟩
  have h := congrArg (fun n:ℤ => (n:ZMod q)) zero
  unfold defect at h
  push_cast at h
  simp only [ZMod.natCast_self] at h
  have eq : ((2*T:ℕ):ZMod q)*B*C*((p:ZMod q)-1)^2=0 := by
    push_cast
    linear_combination h
  have nz (n : ℕ) (lo : 0<n) (hi : n<q) : (n:ZMod q)≠0 :=
    fun zero => Nat.not_dvd_of_pos_of_lt lo hi ((ZMod.natCast_eq_zero_iff n q).mp zero)
  have pn : (p:ZMod q)-1≠0 := by
    rw [←Nat.cast_one,←Nat.cast_sub (by omega : 1≤p)]
    exact nz _ (by omega) (by omega)
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (nz _ (by omega) qt) (nz _ hb qb)) (nz _ hc qc))
    (pow_ne_zero _ pn)) eq

end OMA.CofactorPairPole245212

end

section

/- A fixed pair with a tiny Euler excess can give a very loose exponent
bound. Replace that bound by a logarithmic integer-rounding test before
enumerating any exponents. -/
namespace OMA.CofactorPairRounding245212
open Nat ArithmeticFunction OMA.Smooth245212
open scoped ArithmeticFunction.sigma
open OMA.PairHeight245212 (moment_bound)

def bits (n : ℕ) := Nat.log 2 n+1
def ceiling (h q E : ℕ) := 2+3*(bits h+E*bits q)
def cost (A S q M : ℕ) := 2*A*(M+1)*q^2+A+S*q^2
def threshold (h A S p q E : ℕ) :=
  max (S*q/A+1) (Nat.log p (cost A S q (ceiling h q E))+1)

private theorem bits_bound (n : ℕ) : n≤2^bits n := (lt_pow_succ_log_self (by decide) n).le

private theorem degree {h p q a d E z : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime)
    (oq : q≠2) (cq : h.Coprime q) (pq : p≠q) (pz : p≤z) (ae : a≤E) (dp : 0<d)
    (eqn : OeisA245212.a (h*p^a*q^d)=(σ 1 (h*p^a*q^d):ℤ)) : d≤ceiling h z E := by
  let b:=h*p^a
  have pp:=hp.pos
  have pos : 0<b := by dsimp [b];positivity
  have bound := OMA.PairExtension245212.last_log pos hq oq
    (cq.mul_left (((coprime_primes hp hq).mpr pq).pow_left _)) dp eqn
  let N:=bits h+E*bits z
  have tiny : b≤2^N := by
    dsimp [b,N]
    rw [pow_add,Nat.mul_comm E,pow_mul]
    apply Nat.mul_le_mul (bits_bound h)
    exact (Nat.pow_le_pow_left (pz.trans (bits_bound z)) a).trans
      (Nat.pow_le_pow_right (by positivity) ae)
  have weight : W b+σ 1 b≤2^(1+3*N) := by
    rw [pow_add,pow_one,Nat.mul_comm 3,pow_mul]
    exact (OMA.PairHeight245212.moment_bound pos).trans (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left tiny 3))
  rw [Nat.log2_eq_log_two] at bound
  have logs := Nat.log_mono_right (b:=2) weight
  rw [Nat.log_pow (by decide)] at logs
  change d≤2+3*N
  omega

private theorem squeeze {u v A S p q B C P Q M N : ℤ}
    (pq : p≤q) (u0 : u=p-1) (v0 : v=q-1)
    (A0 : 0<A) (S0 : 0≤S) (P0 : 1≤P) (Q0 : 1≤Q)
    (bp : 1≤B) (bm : B≤M+1) (cm : C≤M+1)
    (bu : S*q≤A*(B-1)) (cv : S*q≤A*(C-1)) (pr : 2≤p)
    (pbig : 2*A*(M+1)*q^2+A+S*q^2<P) (qbig : 2*A*(M+1)*q^2+A+S*q^2<Q)
    (identity : N*P*Q=q*(A*(C*v-1)-S*u*v)*Q+p*(A*(B*u-1)-S*u*v)*P+A+S*u*v) : False := by
  let x:=q*(A*(C*v-1)-S*u*v)
  let y:=p*(A*(B*u-1)-S*u*v)
  let w:=A+S*u*v
  let t:=A*(M+1)*q^2
  have up : 1≤u := by omega
  have vp : 1≤v := by omega
  have uv : u≤q := by omega
  have vq : v≤q := by omega
  have q0 : 0≤q := by omega
  have x0 : 0≤x := by
    apply mul_nonneg q0
    nlinarith only [mul_le_mul_of_nonneg_right cv (by omega : 0≤v),
      mul_nonneg (mul_nonneg S0 (by omega : 0≤v)) (sub_nonneg.mpr uv),
      mul_nonneg A0.le (by omega : 0≤v-1)]
  have y0 : 0≤y := by
    apply mul_nonneg (by omega)
    nlinarith only [mul_le_mul_of_nonneg_right bu (by omega : 0≤u),
      mul_nonneg (mul_nonneg S0 (by omega : 0≤u)) (sub_nonneg.mpr vq),
      mul_nonneg A0.le (by omega : 0≤u-1)]
  have w0 : 0<w := by dsimp [w];have := mul_nonneg (mul_nonneg S0 (by omega : 0≤u)) (by omega : 0≤v);omega
  have wmax : w≤A+S*q^2 := by
    dsimp [w]; nlinarith only [mul_le_mul_of_nonneg_left (mul_le_mul uv vq (by omega) q0) S0]
  have xx : x≤t := by
    dsimp [x,t]
    have cBound := mul_le_mul cm vq (by omega) (by omega : 0≤M+1)
    nlinarith only [mul_le_mul_of_nonneg_left cBound (mul_nonneg q0 A0.le),
      mul_nonneg (mul_nonneg (mul_nonneg q0 S0) (by omega : 0≤u)) (by omega : 0≤v),mul_nonneg q0 A0.le]
  have yy : y≤t := by
    dsimp [y,t]
    have bBound := mul_le_mul bm uv (by omega) (by omega : 0≤M+1)
    have allBound := mul_le_mul pq bBound (mul_nonneg (by omega) (by omega)) q0
    nlinarith only [mul_le_mul_of_nonneg_left allBound A0.le,
      mul_nonneg (mul_nonneg (mul_nonneg (by omega : 0≤p) S0) (by omega : 0≤u)) (by omega : 0≤v),
      mul_nonneg (by omega : 0≤p) A0.le]
  rw [add_assoc (q*_ *Q+p*_ *P) A] at identity
  change N*P*Q=x*Q+y*P+w at identity
  have high : 1≤N := by
    by_contra! off
    have v := mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by omega : N≤0) (by omega : 0≤P)) (by omega : 0≤Q)
    nlinarith only [identity,v,mul_nonneg x0 (by omega : 0≤Q),mul_nonneg y0 (by omega : 0≤P),w0]
  have lhs := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right high (by omega : 0≤P)) (by omega : 0≤Q)
  have pcap : 2*t+w<P := by dsimp [t];linarith only [pbig,wmax]
  have qcap : 2*t+w<Q := by dsimp [t];linarith only [qbig,wmax]
  rcases le_total P Q with l|l
  · nlinarith only [identity,lhs,mul_le_mul_of_nonneg_right xx (by omega : 0≤Q),
      mul_le_mul yy l (by omega : 0≤P) (x0.trans xx),mul_le_mul_of_nonneg_left Q0 w0.le,
      mul_lt_mul_of_pos_right pcap (by omega : 0<Q)]
  · nlinarith only [identity,lhs,mul_le_mul xx l (by omega : 0≤Q) (y0.trans yy),
      mul_le_mul_of_nonneg_right yy (by omega : 0≤P),mul_le_mul_of_nonneg_left P0 w0.le,
      mul_lt_mul_of_pos_right qcap (by omega : 0<P)]

theorem shortened {h p q a d E : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime)
    (op : 3≤p) (cp : h.Coprime p) (cq : h.Coprime q) (pq : p<q) (aa : 0<a) (dd : 0<d)
    (small : min a d≤E) (eqn : OeisA245212.a (h*p^a*q^d)=(σ 1 (h*p^a*q^d):ℤ)) :
    min a d < threshold h (W h) (σ 1 h) p q E := by
  let A:=W h
  let S:=σ 1 h
  let M:=ceiling h q E
  let L:=threshold h A S p q E
  have a0 : 0<A := by
    dsimp [A]; rw [w_apply]
    exact Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨1,Nat.one_mem_divisors.mpr hh.ne',by simp⟩
  have bound : a≤M ∧ d≤M := by
    have z : E≤M := by
      have qt := bits_bound q
      have qb : 1≤bits q := by dsimp [bits];omega
      dsimp [M,ceiling]
      nlinarith only [Nat.mul_le_mul_left E qb,Nat.zero_le (bits h)]
    rcases le_total a d with order|order
    · rw [min_eq_left order] at small
      exact ⟨small.trans z,degree hh hp hq (by omega) cq pq.ne pq.le small dd eqn⟩
    · rw [min_eq_right order] at small
      have flipped : OeisA245212.a (h*q^d*p^a)=(σ 1 (h*q^d*p^a):ℤ) := by rwa [mul_right_comm]
      exact ⟨degree hh hq hp (by omega) cp pq.ne.symm le_rfl small aa flipped,small.trans z⟩
  by_contra! bad
  change L ≤ min a d at bad
  have la := bad.trans (min_le_left a d)
  have ld := bad.trans (min_le_right a d)
  have mass : S*q≤A*L := by
    have floor := Nat.lt_mul_div_succ (S*q) a0
    have lim : S*q/A+1≤L := le_max_left _ _
    exact floor.le.trans (by simpa [mul_comm] using Nat.mul_le_mul_left A lim)
  have power : cost A S q M < p^L :=
    (Nat.lt_pow_succ_log_self hp.one_lt _).trans_le
      (Nat.pow_le_pow_right hp.pos (le_max_right _ _))
  have pa := power.trans_le (Nat.pow_le_pow_right hp.pos la)
  have qd := (power.trans_le (Nat.pow_le_pow_right hp.pos ld)).trans_le (Nat.pow_le_pow_left pq.le _)
  have locp:=OMA.ComplementaryLocal245212.moments hp a
  have locq:=OMA.ComplementaryLocal245212.moments hq d
  have ident:=OMA.CofactorPairPole245212.tails (W h) (σ 1 h) ((h:ℤ)*σ 0 h) p q
    (a+1) (d+1) ((p:ℤ)^a) ((q:ℤ)^d) (W (p^a)) (W (q^d)) (σ 1 (p^a)) (σ 1 (q^d))
    locp.2 locq.2 locp.1 locq.1 (OMA.CofactorPairPole245212.balance hh hp hq cp cq pq.ne eqn)
  apply squeeze (p:=(p:ℤ)) (q:=(q:ℤ)) (M:=(M:ℤ)) (by exact_mod_cast pq.le)
    rfl rfl (by exact_mod_cast a0) (by positivity) (by exact_mod_cast Nat.one_le_pow a p hp.pos)
    (by exact_mod_cast Nat.one_le_pow d q hq.pos) (by omega)
    (by exact_mod_cast Nat.succ_le_succ bound.1) (by exact_mod_cast Nat.succ_le_succ bound.2)
    _ _ (by omega) _ _ ident
  · simp only [add_sub_cancel_right];exact_mod_cast mass.trans (Nat.mul_le_mul_left A la)
  · simp only [add_sub_cancel_right];exact_mod_cast mass.trans (Nat.mul_le_mul_left A ld)
  · dsimp [cost] at pa;exact_mod_cast pa
  · dsimp [cost] at qd;exact_mod_cast qd

end OMA.CofactorPairRounding245212

end

section

/- A complete positive certificate runs finite integer tables for the
shape h·p^a·q^d. A zero Euler denominator is left unresolved. No bound
on the exponents or primes is an input to the resulting theorem. -/
namespace OMA.CofactorEulerPair245212
open Nat ArithmeticFunction OMA.Smooth245212
open scoped ArithmeticFunction.sigma
open OMA.Large245212 (moments)

def every (l r : ℕ) (f : ℕ→Bool) := (List.range' l (r+1-l)).all f

theorem checked {l r i : ℕ} {f : ℕ→Bool} (yes : every l r f=true)
    (lo : l ≤ i) (hi : i ≤ r) : f i=true :=
  List.all_eq_true.mp yes i (List.mem_range'_1.mpr ⟨lo,by omega⟩)

def movingRow (A S T p e : ℕ) := OMA.PairExtension245212.free (p+1)
  (A*OMA.Large245212.wt p e) (S*OMA.Large245212.sig p e) (T*OMA.Large245212.tax p e)

theorem moving_row_sound {h p q a d : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime)
    (oq : q≠2) (cp : h.Coprime p) (cq : h.Coprime q) (pq : p<q) (dp : 0<d)
    (yes : movingRow (W h) (σ 1 h) (h*σ 0 h) p a=true) :
    OeisA245212.a (h*p^a*q^d)≠(σ 1 (h*p^a*q^d):ℤ) := by
  obtain ⟨ys,xw⟩ := OMA.Large245212.moments hp a
  have pp:=hp.pos
  have cop:=cp.pow_right a
  apply OMA.PairExtension245212.free_sound (by positivity) hq oq
    (cq.mul_left (((coprime_primes hp hq).mpr pq.ne).pow_left a)) dp pq
  rw [w_mult.map_mul_of_coprime cop,isMultiplicative_sigma.map_mul_of_coprime cop,
    isMultiplicative_sigma.map_mul_of_coprime cop,sigma_zero_apply_prime_pow hp]
  simpa only [movingRow,ys,xw,OMA.Large245212.tax,mul_assoc,mul_left_comm,mul_comm] using yes

def finitePair (h A S T p q : ℕ) : Bool :=
  let floor:=2*T*(p-1)*(q-1)
  let top:=A*p*q
  if ¬q.Prime ∨ ¬h.Coprime q ∨ top<floor then true else
  if top=floor then false else
  let E:=2*A*(p+q)/(top-floor)
  let endAt:=min E (OMA.CofactorPairRounding245212.threshold h A S p q E)
  table A S T p q endAt && table A S T q p endAt

def nextPrime (h A S T p : ℕ) : Bool :=
  if ¬p.Prime ∨ ¬h.Coprime p then true else
  let c:=2*T*(p-1)
  let b:=A*p
  if c<b then every 1 (2*A/(b-c)) (movingRow A S T p) else
  if b<c then every (p+1) (c/(c-b)) (finitePair h A S T p) else false

def decidePair (h A S T : ℕ) :=
  every 3 (1+3*A/(2*T-A)) (nextPrime h A S T)

theorem original_at_prime {h p q a d : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime)
    (op : 3≤p) (cp : h.Coprime p) (cq : h.Coprime q) (pq : p<q)
    (ap : 0<a) (dp : 0<d) (sub : W h+σ 1 h≤2*(h*σ 0 h))
    (row : nextPrime h (W h) (σ 1 h) (h*σ 0 h) p=true) :
    OeisA245212.a (h*p^a*q^d)≠(σ 1 (h*p^a*q^d):ℤ) := by
  intro eqn
  let A:=W h
  let S:=σ 1 h
  let T:=h*σ 0 h
  change A+S≤2*T at sub
  obtain ⟨c,b⟩:=original_cap hh hp hq cp cq pq.ne ap sub eqn
  change 2*T*(p-1)*(q-1)≤A*p*q at c
  change (A:ℚ)*(X p (some a)*X q (some d))<2*(T:ℚ) at b
  have bcast : (A:ℚ)*(X p (some a)*X q (some d))<((2*T:ℕ):ℚ) := by simpa using b
  change nextPrime h A S T p=true at row
  have valid : ¬(¬p.Prime ∨ ¬h.Coprime p) := by tauto
  rw [nextPrime,if_neg valid] at row
  by_cases l : 2*T*(p-1)<A*p
  · rw [if_pos l] at row
    have e := short_first hp hq l bcast
    exact moving_row_sound hh hp hq (by omega) cp cq pq dp (checked row ap (by omega)) eqn
  · rw [if_neg l] at row
    by_cases r : A*p<2*T*(p-1)
    · rw [if_pos r] at row
      have capQ := second_bound hq.one_lt r c
      have point := checked row pq capQ
      have eligible : ¬(¬q.Prime ∨ ¬h.Coprime q ∨ A*p*q<2*T*(p-1)*(q-1)) := by
        have bound := not_lt_of_ge c
        tauto
      rw [finitePair,if_neg eligible] at point
      by_cases same : A*p*q=2*T*(p-1)*(q-1)
      · simp [same] at point
      · rw [if_neg same,Bool.and_eq_true] at point
        have fit := short_pair hp hq (lt_of_le_of_ne c (Ne.symm same)) bcast
        have bounded := Nat.le_trans (Nat.le_succ _) fit
        have smaller := OMA.CofactorPairRounding245212.shortened hh hp hq op cp cq pq ap dp bounded eqn
        exact table_sound hh hp hq (by omega) (by omega) cp cq pq.ne ap dp
          (le_min bounded smaller.le) point.1 point.2 eqn
    · simp [r] at row

theorem original_of_decision {h p q a d : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime)
    (op : 3≤p) (cp : h.Coprime p) (cq : h.Coprime q) (pq : p<q)
    (ap : 0<a) (dp : 0<d) (sub : W h+σ 1 h≤2*(h*σ 0 h))
    (yes : decidePair h (W h) (σ 1 h) (h*σ 0 h)=true) :
    OeisA245212.a (h*p^a*q^d)≠(σ 1 (h*p^a*q^d):ℤ) := by
  intro eqn
  have bound := (original_cap hh hp hq cp cq pq.ne ap sub eqn).1
  have sp := sigma_pos 1 h hh.ne'
  have small := first_bound hp.one_lt pq.le (by omega : W h<2*(h*σ 0 h)) bound
  exact original_at_prime hh hp hq op cp cq pq ap dp sub (checked yes op small) eqn

end OMA.CofactorEulerPair245212

end

section

/- A two-prime certificate for a supercritical divisor cofactor. -/
namespace OMA.RankThreeFourSmallBounds245212
open Nat OMA.Smooth245212
open OMA.PairHeight245212 (scaledX)
open OMA.FixedExponents245212 (y_pos)

def Bal (A S H p q a d : ℕ) :=
  (A:ℚ)*(X p (some a)*X q (some d))+(S:ℚ)*(Y p (some a)*Y q (some d))=H

theorem strict {A S H p q a d : ℕ} (hp : p.Prime) (hq : q.Prime) (sp : 0<S)
    (eq : Bal A S H p q a d) : (A:ℚ)*(X p (some a)*X q (some d))<H := by
  have pos := mul_pos (by exact_mod_cast sp : (0:ℚ)<S)
    (mul_pos (OMA.FixedExponents245212.y_pos hp a) (OMA.FixedExponents245212.y_pos hq d))
  unfold Bal at eq
  linarith

/-- On the low side of the fixed pair's Euler limit, the second exponent
is bounded even if the two integer Euler numerators agree. -/
theorem under_pair {A S H p q a d : ℕ} (hp : p.Prime) (hq : q.Prime) (ap : 0<A)
    (eq : Bal A S H p q a d) (under : A*p*q≤H*(p-1)*(q-1)) :
    d+1≤2*(A+S*(p-1)*(q-1))/(A*q) := by
  let u:=p-1
  let v:=q-1
  let y:=Y p (some a)
  let z:=Y q (some d)
  have y0 : 0<y := OMA.FixedExponents245212.y_pos hp _
  have z0 : 0<z := OMA.FixedExponents245212.y_pos hq _
  have id := congrArg₂ (·*·) (OMA.PairHeight245212.scaledX p hp.one_lt (some a))
    (OMA.PairHeight245212.scaledX q hq.one_lt (some d))
  change X p (some a)*u*(X q (some d)*v)=((p:ℚ)-y)*((q:ℚ)-z) at id
  unfold Bal at eq
  change (A:ℚ)*_+S*(y*z)=H at eq
  have bound : (A:ℚ)*p*q≤H*u*v := by exact_mod_cast under
  have first : (A:ℚ)*q*y≤(A+S*u*v)*z*y := by
    nlinarith only [bound,congrArg (fun t:ℚ=>t*u*v) eq,congrArg ((A:ℚ)*·) id,
      mul_nonneg (show (0:ℚ)≤A*p by positivity) z0.le]
  have one := le_of_mul_le_mul_right first y0
  have two : z*((d:ℚ)+1)≤2 := (OMA.CapOrder245212.y_short hq d).le
  apply (Nat.le_div_iff_mul_le (Nat.mul_pos ap hq.pos)).mpr
  change (d+1)*(A*q)≤2*(A+S*u*v)
  exact_mod_cast (show ((d:ℚ)+1)*(A*q)≤2*(A+S*u*v) by
    nlinarith only [mul_le_mul_of_nonneg_right one (show (0:ℚ)≤d+1 by positivity),
      mul_le_mul_of_nonneg_left two (show (0:ℚ)≤A+S*u*v by positivity)])

/-- On the low side of the one-prime limit, separate a short first
exponent from a bounded second prime. -/
theorem under_first {A S H p q a d : ℕ} (hp : p.Prime) (hq : q.Prime)
    (eq : Bal A S H p q a d) (under : A*p<H*(p-1)) :
    a+1≤4*S*(p-1)/(H*(p-1)-A*p) ∨ q≤1+2*A*p/(H*(p-1)-A*p) := by
  let u:=p-1
  let v:=q-1
  let G:=H*u-A*p
  let y:=Y p (some a)
  let z:=Y q (some d)
  have y0 : 0≤y := y_nonneg hp.one_lt _
  have z0 : 0≤z := y_nonneg hq.one_lt _
  have u0 : 0<u := Nat.sub_pos_of_lt hp.one_lt
  have v0 : 0<v := Nat.sub_pos_of_lt hq.one_lt
  have g0 : 0<G := Nat.sub_pos_of_lt under
  have gs : (G:ℚ)+A*p=H*u := by exact_mod_cast Nat.sub_add_cancel under.le
  have y2 : y*((a:ℚ)+1)≤2 := (OMA.CapOrder245212.y_short hp a).le
  have z1 : z≤1 := y_one hq.one_lt _
  have id := congrArg₂ (·*·) (OMA.PairHeight245212.scaledX p hp.one_lt (some a))
    (OMA.PairHeight245212.scaledX q hq.one_lt (some d))
  change X p (some a)*u*(X q (some d)*v)=((p:ℚ)-y)*((q:ℚ)-z) at id
  have xx : ((p:ℚ)-y)*(q-z)≤p*q := mul_le_mul (by linarith) (by linarith)
    (sub_nonneg.mpr (z1.trans (by exact_mod_cast hq.one_le : (1:ℚ)≤q)))
    (Nat.cast_nonneg _)
  have yz : y*z≤y := mul_le_of_le_one_right y0 z1
  have qv : (q:ℚ)=(v:ℚ)+1 := by exact_mod_cast (show q=v+1 by dsimp [v];omega)
  unfold Bal at eq
  change (A:ℚ)*_+S*(y*z)=H at eq
  have sum : (G:ℚ)*v≤A*p+S*y*u*v := by
    nlinarith only [congrArg (fun t:ℚ=>t*u*v) eq,congrArg ((A:ℚ)*·) id,
      mul_le_mul_of_nonneg_left xx (Nat.cast_nonneg A : (0:ℚ)≤A),
      mul_le_mul_of_nonneg_left yz (show (0:ℚ)≤S*u*v by positivity),
      congrArg (fun t:ℚ => t*v) gs,congrArg (fun t:ℚ => A*p*t) qv]
  by_cases b : (a+1)*G≤4*S*u
  · exact Or.inl ((Nat.le_div_iff_mul_le g0).mpr b)
  right
  have neg : 4*(S:ℚ)*u<((a:ℚ)+1)*G := by exact_mod_cast lt_of_not_ge b
  have sy : 2*(S:ℚ)*y*u≤G := by
    apply le_of_mul_le_mul_right (a:=(a:ℚ)+1) _ (by positivity)
    nlinarith only [neg,mul_le_mul_of_nonneg_left y2 (show (0:ℚ)≤2*S*u by positivity)]
  have cap : v*G≤2*A*p := by
    exact_mod_cast (show (v:ℚ)*G≤2*A*p by
      nlinarith only [sum,mul_le_mul_of_nonneg_right sy (Nat.cast_nonneg v)])
  have low := (Nat.le_div_iff_mul_le g0).mpr cap
  change q≤1+2*A*p/G
  dsimp [v] at low
  omega

end OMA.RankThreeFourSmallBounds245212

end

section

/- Check short intervals separately and join them without reducing the
boolean arithmetic again. All endpoints are checked in the kernel. -/
namespace OMA.RankThreeMiddle245212
open OMA.CofactorEulerPair245212

theorem joinEvery {f : ℕ→Bool} {a b c : ℕ}
    (left : every a b f=true) (right : every (b+1) c f=true) :
    every a c f=true := by
  apply List.all_eq_true.mpr
  intro i hi
  obtain ⟨lo,up⟩:=List.mem_range'_1.mp hi
  by_cases e : i≤b
  · exact List.all_eq_true.mp left i (List.mem_range'_1.mpr ⟨lo,by omega⟩)
  · exact List.all_eq_true.mp right i (List.mem_range'_1.mpr ⟨by omega,by omega⟩)

end OMA.RankThreeMiddle245212

end

section

/- Exact replacement for huge reverse-digit powers. A prime-power
congruence rejects an impossible exponent before evaluating the power. -/
namespace OMA.CofactorGuardFast245212
open Nat ArithmeticFunction OMA.Smooth245212 OMA.CofactorEulerPair245212 OMA.PairExtension245212
open OMA.Large245212 (moments)
open scoped ArithmeticFunction.sigma

def magnitude (A S q : ℕ) := ((A:ℤ)-((q:ℤ)-1)*(S:ℤ)).natAbs

private theorem divides {A S T p f : ℕ} (hp : p.Prime) (ok : permitted A S T p f=true) :
    p^f ∣ magnitude A S p := by
  obtain ⟨sval,wval⟩:=OMA.Large245212.moments hp f
  simp only [permitted,Bool.and_eq_true,decide_eq_true_eq] at ok
  have balance:=ok.2
  rw [sval,wval] at balance
  have van : (p:ZMod (p^f))^f=0 := by rw [←Nat.cast_pow];exact ZMod.natCast_self _
  have w:=congrArg (fun n:ℕ=>(n:ZMod (p^f))) (OMA.PrimePowerDiv245212.weighted hp f)
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_sub hp.pos,Nat.cast_one,Nat.cast_pow,van,mul_zero] at w
  have s : ((p:ZMod (p^f))-1)*(σ 1 (p^f):ℕ) = -1 := by
    rw [sigma_one_apply_prime_pow hp]
    simp only [Nat.cast_sum,Nat.cast_pow]
    rw [mul_comm,geom_sum_mul,pow_succ,van,zero_mul,zero_sub]
  have bb:=congrArg (fun n:ℕ=>(n:ZMod (p^f))) balance
  simp only [OMA.Large245212.tax,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_one,van,mul_zero] at bb
  have iv : ((p^f:ℕ):ℤ) ∣ (A:ℤ)-((p:ℤ)-1)*(S:ℤ) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p^f)).mp
    push_cast
    linear_combination ((p:ZMod (p^f))-1)^2*bb - (A:ZMod (p^f))*((p:ZMod (p^f))-1)*w +
      ((A:ZMod (p^f))-((p:ZMod (p^f))-1)*(S:ZMod (p^f)))*s
  simpa [magnitude] using Int.natAbs_dvd_natAbs.mpr iv

def fastKnown (A S T q : ℕ) : Bool :=
  let C:=OMA.ReverseDigit245212.numerator q A S
  let D:=OMA.ReverseDigit245212.denominator q A T
  if ¬q∣A+S ∨ D=0 then true else
    let f:=(⌊C/D⌋-1).toNat
    let N:=magnitude A S q
    decide (0<N ∧ N.log2<f) || !permitted A S T q f

theorem fastKnown_eq {A S T q : ℕ} (hq : q.Prime) : fastKnown A S T q=known A S T q := by
  simp only [fastKnown,known]
  split
  · rfl
  · let f:=(⌊OMA.ReverseDigit245212.numerator q A S / OMA.ReverseDigit245212.denominator q A T⌋-1).toNat
    let N:=magnitude A S q
    change (decide (0<N ∧ N.log2<f) || !permitted A S T q f)=(!permitted A S T q f)
    by_cases yes : permitted A S T q f=true
    · have impossible : ¬(0<N ∧ N.log2<f) := by
        rintro ⟨pos,small⟩
        have bound := Nat.le_of_dvd pos (divides hq yes)
        have two := (Nat.pow_le_pow_left hq.two_le f).trans bound
        have low := (Nat.le_log_iff_pow_le (by decide : 1<2) pos.ne').mpr two
        rw [Nat.log2_eq_log_two] at small
        omega
      simp [impossible]
    · simp [Bool.eq_false_iff.mpr yes]

def fastRow (A S T p q e : ℕ) := fastKnown (A*OMA.Large245212.wt p e)
  (S*OMA.Large245212.sig p e) (T*OMA.Large245212.tax p e) q

def fastTable (A S T p q E : ℕ) := (List.range E).all fun i=>fastRow A S T p q (i+1)

theorem tables {A S T p q E : ℕ} (hq : q.Prime) : fastTable A S T p q E=table A S T p q E := by
  simp only [fastTable,table,fastRow,row,fastKnown_eq hq]

def fastPair (h A S T p q : ℕ) : Bool :=
  let floor:=2*T*(p-1)*(q-1)
  let top:=A*p*q
  if ¬q.Prime ∨ ¬h.Coprime q ∨ top<floor then true else
  if top=floor then false else
  let E:=2*A*(p+q)/(top-floor)
  let endAt:=min E (OMA.CofactorPairRounding245212.threshold h A S p q E)
  fastTable A S T p q endAt && fastTable A S T q p endAt

theorem pairs {h A S T p : ℕ} (hp : p.Prime) : fastPair h A S T p=finitePair h A S T p := by
  funext q
  by_cases hq : q.Prime
  · simp only [fastPair,finitePair,tables hp,tables hq]
  · simp [fastPair,finitePair,hq]

theorem restore {l r h A S T p : ℕ} (hp : p.Prime)
    (yes : every l r (fastPair h A S T p)=true) : every l r (finitePair h A S T p)=true := by
  simpa only [pairs hp] using yes

end OMA.CofactorGuardFast245212

end

section

/- All integer checks for two new odd primes after a fixed weighted cofactor. -/
namespace OMA.RankThreeFourSmallDecision245212
open Nat ArithmeticFunction OMA.Smooth245212 OMA.CofactorEulerPair245212
open OMA.RankThreeFourSmallBounds245212 OMA.CofactorGuardFast245212
open scoped ArithmeticFunction.sigma
open OMA.Large245212 (force)
open OMA.Large245212 (moments)
open OMA.PairExtension245212 (fit)
open OMA.CofactorGuardFast245212 (tables)
open OMA.CofactorEulerPair245212 (checked)

def fixedPair (h A S T p q : ℕ) : Bool :=
  if ¬q.Prime ∨ ¬h.Coprime q then true else
  if 2*T*(p-1)*(q-1)<A*p*q then fastPair h A S T p q else
    fastTable A S T q p (2*(A+S*(p-1)*(q-1))/(A*q))

theorem pair_sound {h p q a d : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime) (op : 3≤p)
    (cp : h.Coprime p) (cq : h.Coprime q) (pq : p<q) (ap : 0<a) (dp : 0<d)
    (ck : fixedPair h (W h) (σ 1 h) (h*σ 0 h) p q=true) :
    OeisA245212.a (h*p^a*q^d)≠(σ 1 (h*p^a*q^d):ℤ) := by
  intro eqn
  let A:=W h
  let S:=σ 1 h
  let T:=h*σ 0 h
  have b : Bal A S (2*T) p q a d := by
    simpa [A,S,T,Bal] using normalized hh hp hq cp cq pq.ne eqn
  have az : 0<A := by
    dsimp [A];rw [w_apply]
    exact Finset.sum_pos' (fun _ _=>Nat.zero_le _) ⟨1,Nat.one_mem_divisors.mpr hh.ne',by simp⟩
  have sz : 0<S := sigma_pos 1 h hh.ne'
  change fixedPair h A S T p q=true at ck
  have eligible : ¬(¬q.Prime ∨ ¬h.Coprime q) := by tauto
  rw [fixedPair,if_neg eligible] at ck
  by_cases pos : 2*T*(p-1)*(q-1)<A*p*q
  · rw [if_pos pos,pairs hp] at ck
    have elig : ¬(¬q.Prime ∨ ¬h.Coprime q ∨ A*p*q<2*T*(p-1)*(q-1)) := by
      have n := not_lt.mpr pos.le;tauto
    rw [finitePair,if_neg elig,if_neg pos.ne.symm,Bool.and_eq_true] at ck
    have e:=short_pair hp hq pos (strict hp hq sz b)
    have raw := (Nat.le_succ _).trans e
    have l := OMA.CofactorPairRounding245212.shortened hh hp hq op cp cq pq ap dp raw eqn
    exact table_sound hh hp hq (by omega) (by omega) cp cq pq.ne ap dp (le_min raw l.le) ck.1 ck.2 eqn
  · rw [if_neg pos,OMA.CofactorGuardFast245212.tables hp] at ck
    have ed:=under_pair hp hq az b (by omega)
    obtain ⟨j,rfl⟩:=Nat.exists_eq_succ_of_ne_zero dp.ne'
    have one:=List.all_eq_true.mp ck j (List.mem_range.mpr (by omega))
    have kill:=row_sound hh hq hp (by omega) cq cp pq.ne.symm ap one
    exact kill (by rwa [mul_right_comm h])

def freeTo (R A S T D : ℕ) : Bool := every 1 D fun d=>
  let q:=OMA.Large245212.candidate A S T d
  decide (OMA.LastDigit245212.denom A S T d=0 ∨ q<R) || !OMA.PairExtension245212.permitted A S T q d

theorem freeTo_sound {m q d R D : ℕ} (mp : 0 < m) (hq : q.Prime) (cop : m.Coprime q)
    (dp : 0<d) (lo : R≤q) (hi : d≤D) (eqn : OeisA245212.a (m*q^d)=(σ 1 (m*q^d):ℤ)) :
    freeTo R (W m) (σ 1 m) (m*σ 0 m) D≠true := by
  intro ck
  obtain ⟨pos,low,high,_⟩:=OMA.LastDigit245212.balance_digits mp hq cop dp eqn
  have val := OMA.Large245212.force (sigma_pos 1 m mp.ne') hq.one_lt pos low high
  have done_ := OMA.CofactorEulerPair245212.checked ck dp hi
  simp [val,pos.ne',Nat.not_lt_of_ge lo,OMA.PairExtension245212.fit mp hq cop dp eqn] at done_

def moving (R D A S T p b : ℕ) := freeTo R (A*OMA.Large245212.wt p b)
  (S*OMA.Large245212.sig p b) (T*OMA.Large245212.tax p b) D

theorem moving_sound {h p q a d R D : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime)
    (cp : h.Coprime p) (cq : h.Coprime q) (pq : p<q)
    (dp : 0<d) (lo : R≤q) (hi : d≤D)
    (ck : moving R D (W h) (σ 1 h) (h*σ 0 h) p a=true) :
    OeisA245212.a (h*p^a*q^d)≠(σ 1 (h*p^a*q^d):ℤ) := by
  intro eqn
  obtain ⟨sg,wt⟩:=OMA.Large245212.moments hp a
  have cop:=cp.pow_right a
  have pp:=hp.pos
  apply freeTo_sound (by positivity : 0<h*p^a) hq
    (cq.mul_left (((coprime_primes hp hq).mpr pq.ne).pow_left a)) dp lo hi eqn
  rw [w_mult.map_mul_of_coprime cop,isMultiplicative_sigma.map_mul_of_coprime cop,
    isMultiplicative_sigma.map_mul_of_coprime cop,sigma_zero_apply_prime_pow hp]
  simpa only [moving,wt,sg,OMA.Large245212.tax,mul_assoc,mul_comm,mul_left_comm] using ck

def lenD (A S p : ℕ) := 2*(A+S*(p-1))/A
def lenB (A S T p : ℕ) := 4*S*(p-1)/(2*T*(p-1)-A*p)
def capQ (A T p : ℕ) := 1+2*A*p/(2*T*(p-1)-A*p)
def atPrime (h A S T p : ℕ) : Bool :=
  if ¬p.Prime ∨ ¬h.Coprime p then true else
  if 2*T*(p-1)<A*p then every 1 (2*A/(A*p-2*T*(p-1))) (movingRow A S T p) else
  if A*p<2*T*(p-1) then
    every (p+1) (capQ A T p) (fixedPair h A S T p) &&
    every 1 (lenB A S T p) (moving (max (p+1) (capQ A T p+1)) (lenD A S p) A S T p)
  else false

theorem prime_sound {h p q a d : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime) (op : 3≤p)
    (cp : h.Coprime p) (cq : h.Coprime q) (pq : p<q) (ap : 0<a) (dp : 0<d)
    (ck : atPrime h (W h) (σ 1 h) (h*σ 0 h) p=true) :
    OeisA245212.a (h*p^a*q^d)≠(σ 1 (h*p^a*q^d):ℤ) := by
  intro eqn
  let A:=W h
  let S:=σ 1 h
  let T:=h*σ 0 h
  have b : Bal A S (2*T) p q a d := by
    simpa [A,S,T,Bal] using normalized hh hp hq cp cq pq.ne eqn
  have az : 0<A := by
    dsimp [A];rw [w_apply]
    exact Finset.sum_pos' (fun _ _=>Nat.zero_le _) ⟨1,Nat.one_mem_divisors.mpr hh.ne',by simp⟩
  have sz : 0<S := sigma_pos 1 h hh.ne'
  change atPrime h A S T p=true at ck
  have elig : ¬(¬p.Prime ∨ ¬h.Coprime p) := by tauto
  rw [atPrime,if_neg elig] at ck
  by_cases high : 2*T*(p-1)<A*p
  · rw [if_pos high] at ck
    have sh:=short_first hp hq high (strict hp hq sz b)
    exact moving_row_sound hh hp hq (by omega) cp cq pq dp (OMA.CofactorEulerPair245212.checked ck ap (by omega)) eqn
  rw [if_neg high] at ck
  by_cases under : A*p<2*T*(p-1)
  · rw [if_pos under,Bool.and_eq_true] at ck
    by_cases qr : q≤capQ A T p
    · exact pair_sound hh hp hq op cp cq pq ap dp (OMA.CofactorEulerPair245212.checked ck.1 pq qr) eqn
    have sh := under_first hp hq b under
    have eb : a≤lenB A S T p := by change a≤4*S*(p-1)/_; change ¬q≤1+2*A*p/_ at qr; omega
    have low : A*p*q≤2*T*(p-1)*(q-1) := by
      let G:=2*T*(p-1)-A*p
      have val:=Nat.sub_add_cancel under.le
      have gs : 0<G := Nat.sub_pos_of_lt under
      have qq : 2*A*p/G+1≤q-1 := by change ¬q≤1+2*A*p/G at qr;omega
      have less := (Nat.div_lt_iff_lt_mul gs).mp (by omega : 2*A*p/G<q-1)
      have v:=Nat.sub_add_cancel (by omega : 1≤q)
      nlinarith only [less,congrArg (·*(q-1)) val,congrArg (A*p*·) v,Nat.zero_le (A*p)]
    have ed:=(Nat.le_div_iff_mul_le (Nat.mul_pos az hq.pos)).mp (under_pair hp hq az b low)
    have grow : (d+1)*(A*q)≤(2*(A+S*(p-1)))*q := by
      nlinarith only [ed,Nat.mul_le_mul_left (S*(p-1)) (Nat.sub_le q 1),
        Nat.le_mul_of_pos_right A hq.pos]
    have e0 : (d+1)*A≤2*(A+S*(p-1)) := Nat.le_of_mul_le_mul_right (by simpa only [mul_assoc] using grow) hq.pos
    have small : d≤lenD A S p := (Nat.le_succ _).trans ((Nat.le_div_iff_mul_le az).mpr e0)
    exact moving_sound hh hp hq cp cq pq dp (max_le pq (by omega)) small
      (OMA.CofactorEulerPair245212.checked ck.2 ap eb) eqn
  · simp [under] at ck

end OMA.RankThreeFourSmallDecision245212

end

section

/- A logarithmic upper bound for both complementary exponents, using
the smaller actual prime as logarithm base. -/
namespace OMA.RankThreeFourSmallDegree245212
open Nat Finset ArithmeticFunction OMA.Smooth245212
open scoped ArithmeticFunction.sigma
open OMA.CapOrder245212 (geom)

def degree (A S base z E : ℕ) :=
  (Nat.log base z+1)*E+Nat.log base (2*(A*(E+1)+S))+2

theorem one {h p q e f E base z : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime)
    (cp : h.Coprime p) (cq : h.Coprime q) (pq : p≠q) (oq : q≠2) (fp : 0<f)
    (bp : 1<base) (bq : base≤q) (pz : p≤z) (small : e≤E)
    (eqn : OeisA245212.a (h*p^e*q^f)=(σ 1 (h*p^e*q^f):ℤ)) :
    f≤degree (W h) (σ 1 h) base z E := by
  let A:=W h
  let S:=σ 1 h
  let J:=Nat.log base z+1
  let C:=2*(A*(E+1)+S)
  have pp:=hp.pos
  have pos : 0<h*p^e := by positivity
  have eb := OMA.PairExtension245212.last_log_base pos hq oq
    (cq.mul_left (((coprime_primes hp hq).mpr pq).pow_left _)) bp bq fp eqn
  have norm : σ 1 (p^e)<2*p^e := by
    rw [sigma_one_apply_prime_pow hp]
    exact OMA.CapOrder245212.geom p hp.one_lt e
  have w : W (p^e)≤(e+1)*(σ 1 (p^e)) := by
    rw [w_pow hp,sigma_one_apply_prime_pow hp,Finset.mul_sum]
    exact sum_le_sum fun j hj => by
      have le:=show j+1≤e+1 by have := mem_range.mp hj;omega
      simpa only [Nat.mul_comm] using Nat.mul_le_mul_left (p^j) le
  have c:=cp.pow_right e
  have mass : W (h*p^e)+σ 1 (h*p^e)≤C*p^e := by
    rw [w_mult.map_mul_of_coprime c,isMultiplicative_sigma.map_mul_of_coprime c]
    change A*W (p^e)+S*(σ 1 (p^e))≤2*(A*(E+1)+S)*p^e
    nlinarith only [Nat.mul_le_mul_left A w,Nat.mul_le_mul_left (A*(e+1)+S) norm.le,
      Nat.mul_le_mul_right (2*A*p^e) (Nat.succ_le_succ small)]
  have under := Nat.lt_pow_succ_log_self bp C
  have zlim : z≤base^J := (Nat.lt_pow_succ_log_self bp _).le
  have pmax : p^e≤base^(J*E) := by
    rw [pow_mul]
    exact (Nat.pow_le_pow_left (pz.trans zlim) e).trans (Nat.pow_le_pow_right (by positivity) small)
  have upper : W (h*p^e)+σ 1 (h*p^e)<base^(J*E+(Nat.log base C+1)) := by
    rw [pow_add,mul_comm (base^(J*E))]
    exact mass.trans_lt (Nat.mul_lt_mul_of_lt_of_le under pmax (pow_pos (by omega) _))
  have plus : 0<W (h*p^e)+σ 1 (h*p^e) := by have := sigma_pos 1 _ pos.ne';omega
  have cap:=(Nat.log_lt_iff_lt_pow bp plus.ne').mpr upper
  change f≤J*E+Nat.log base C+2
  omega

theorem both {h p q a d E : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime) (op : 3≤p)
    (cp : h.Coprime p) (cq : h.Coprime q) (pq : p<q) (ap : 0<a) (dp : 0<d)
    (small : min a d≤E) (eqn : OeisA245212.a (h*p^a*q^d)=(σ 1 (h*p^a*q^d):ℤ)) :
    a≤degree (W h) (σ 1 h) p q E ∧ d≤degree (W h) (σ 1 h) p q E := by
  have ee : E≤degree (W h) (σ 1 h) p q E := by
    unfold degree; rw [Nat.add_mul,one_mul];omega
  rcases le_total a d with ha|hd
  · rw [min_eq_left ha] at small
    exact ⟨small.trans ee,one hh hp hq cp cq pq.ne (by omega) dp hp.one_lt pq.le pq.le small eqn⟩
  · rw [min_eq_right hd] at small
    have flip : OeisA245212.a (h*q^d*p^a)=(σ 1 (h*q^d*p^a):ℤ) := by rwa [mul_right_comm]
    exact ⟨one hh hq hp cq cp pq.ne.symm (by omega) ap hp.one_lt le_rfl le_rfl small flip,small.trans ee⟩
end OMA.RankThreeFourSmallDegree245212

end

section

/- A nonzero rounded integer forces a logarithmic small exponent, even
when the two first-order coefficients have opposite signs. -/
namespace OMA.RankThreeFourSmallSeparation245212
open Nat ArithmeticFunction OMA.Smooth245212 OMA.CofactorPairPole245212
open scoped ArithmeticFunction.sigma

def cost (A S z M : ℕ) := 2*(A*(M+1)*z^2+z*(A+S*z^2))+A+S*z^2

theorem separated' {A S T p q B C : ℕ} (hq : q.Prime) (op : 2≤p) (pq : p<q)
    (hb : 0<B) (hc : 0<C) (qt : ¬q∣2*T) (qb : B<q) (qc : C<q) :
    defect A S T p q B C≠0 := by
  intro zero
  let : Fact q.Prime := ⟨hq⟩
  have congr := congrArg (fun n:ℤ=>(n:ZMod q)) zero
  unfold defect at congr
  push_cast at congr
  simp only [ZMod.natCast_self] at congr
  have eq : ((2*T:ℕ):ZMod q)*B*C*((p:ZMod q)-1)^2=0 := by push_cast;linear_combination congr
  have nz (n : ℕ) (lo : 0<n) (hi : n<q) : (n:ZMod q)≠0 :=
    fun h=>Nat.not_dvd_of_pos_of_lt lo hi ((ZMod.natCast_eq_zero_iff n q).mp h)
  have pn : (p:ZMod q)-1≠0 := by
    rw [←Nat.cast_one,←Nat.cast_sub (by omega : 1≤p)];exact nz _ (by omega) (by omega)
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero ((ZMod.natCast_eq_zero_iff _ _).not.mpr qt)
    (nz _ hb qb)) (nz _ hc qc)) (pow_ne_zero _ pn)) eq

private theorem squeeze {N x y w P Q X L : ℤ} (nz : N≠0) (p : 1≤P) (q : 1≤Q)
    (a : |x|≤X) (b : |y|≤X) (w0 : 0≤w) (wl : w≤L) (ident : N*P*Q=x*Q+y*P+w) :
    min P Q≤2*X+L := by
  have n : 1≤|N| := by have := abs_pos.mpr nz;omega
  have size : P*Q≤|x| * Q+|y| * P+w := calc
    _ ≤ |N*P*Q| := by
      rw [abs_mul,abs_mul,abs_of_nonneg (by omega : 0≤P),abs_of_nonneg (by omega : 0≤Q)]
      nlinarith only [mul_le_mul_of_nonneg_right n (mul_nonneg (by omega : 0≤P) (by omega : 0≤Q))]
    _ = |x*Q+y*P+w| := congrArg abs ident
    _ ≤ |x*Q+y*P| + |w| := abs_add_le _ _
    _ ≤ |x| * Q+|y| * P+w := by
      have u:=abs_add_le (x*Q) (y*P)
      rw [abs_mul,abs_mul,abs_of_nonneg (by omega : 0≤Q),abs_of_nonneg (by omega : 0≤P)] at u
      rw [abs_of_nonneg w0];omega
  have x0 : 0≤X := (abs_nonneg _).trans a
  have l0 : 0≤L := w0.trans wl
  have big : P*Q≤X*Q+X*P+L := by
    nlinarith only [size,mul_le_mul_of_nonneg_right a (by omega : 0≤Q),
      mul_le_mul_of_nonneg_right b (by omega : 0≤P),wl]
  rcases le_total P Q with pq|qp
  · rw [min_eq_left pq]
    apply le_of_mul_le_mul_right (a:=Q) _ (by omega)
    nlinarith only [big,mul_le_mul_of_nonneg_left pq x0,mul_le_mul_of_nonneg_left q l0]
  · rw [min_eq_right qp]
    apply le_of_mul_le_mul_right (a:=P) _ (by omega)
    nlinarith only [big,mul_le_mul_of_nonneg_left qp x0,mul_le_mul_of_nonneg_left p l0]

private theorem coeff {A S p q B M z : ℤ} (a : 0≤A) (s : 0≤S)
    (pp : 2≤p) (qp : 2≤q) (pz : p≤z) (qz : q≤z) (bp : 1≤B) (bm : B≤M+1) :
    |p*(A*(B*(p-1)-1)-S*(p-1)*(q-1))| ≤ A*(M+1)*z^2+z*(A+S*z^2) := by
  have prod : (p-1)*(q-1)≤z*z :=
    mul_le_mul (by omega) (by omega) (by omega) (by omega)
  have pe : B*(p-1)≤(M+1)*z :=
    mul_le_mul bm (by omega) (by omega) (by omega)
  have pv : 1≤B*(p-1) := by nlinarith only [mul_nonneg (by omega : 0≤B-1) (by omega : 0≤p-2),pp,bp]
  have h : |A*(B*(p-1)-1)-S*(p-1)*(q-1)|≤A*(M+1)*z+(A+S*z^2) := by
    apply abs_le.mpr
    constructor <;> nlinarith only [
      mul_nonneg a (by omega : 0≤B*(p-1)-1),
      mul_le_mul_of_nonneg_left prod s, mul_le_mul_of_nonneg_left pe a,
      mul_nonneg s (mul_nonneg (by omega : 0≤p-1) (by omega : 0≤q-1)),
      mul_nonneg s (sq_nonneg z),mul_nonneg (mul_nonneg a (by omega : 0≤M+1)) (by omega : 0≤z),a]
  rw [abs_mul,abs_of_nonneg (by omega : 0≤p)]
  have g:=mul_le_mul pz h (abs_nonneg _) (by omega : 0≤z)
  exact g.trans_eq (by ring)

theorem small {h p q a d M : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime)
    (cp : h.Coprime p) (cq : h.Coprime q) (pq : p<q)
    (am : a≤M) (dm : d≤M) (qm : M+1<q) (qt : ¬q∣2*(h*σ 0 h))
    (eqn : OeisA245212.a (h*p^a*q^d)=(σ 1 (h*p^a*q^d):ℤ)) :
    min a d≤Nat.log p (cost (W h) (σ 1 h) q M) := by
  let A:=W h
  let S:=σ 1 h
  let T:=h*σ 0 h
  have nt:=separated' (A:=A) (S:=S) (T:=T) hq hp.two_le pq (Nat.succ_pos a)
    (Nat.succ_pos d) qt (by omega) (by omega)
  have f:=OMA.ComplementaryLocal245212.moments hp a
  have g:=OMA.ComplementaryLocal245212.moments hq d
  have id:=tails A S T p q (a+1) (d+1) ((p:ℤ)^a) ((q:ℤ)^d)
    (W (p^a)) (W (q^d)) (σ 1 (p^a)) (σ 1 (q^d)) f.2 g.2 f.1 g.1
    (balance hh hp hq cp cq pq.ne eqn)
  have x:=coeff (p:=(q:ℤ)) (q:=(p:ℤ)) (z:=(q:ℤ)) (A:=(A:ℤ)) (S:=(S:ℤ)) (M:=(M:ℤ)) (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    (by exact_mod_cast hq.two_le) (by exact_mod_cast hp.two_le) (by rfl : (q:ℤ)≤q)
    (by exact_mod_cast pq.le) (by omega : 1≤(d:ℤ)+1) (by omega)
  have y:=coeff (p:=(p:ℤ)) (q:=(q:ℤ)) (z:=(q:ℤ)) (A:=(A:ℤ)) (S:=(S:ℤ)) (M:=(M:ℤ)) (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    (by exact_mod_cast hp.two_le) (by exact_mod_cast hq.two_le) (by exact_mod_cast pq.le)
    (by rfl : (q:ℤ)≤q) (by omega : 1≤(a:ℤ)+1) (by omega)
  have ip : (2:ℤ)≤p := by exact_mod_cast hp.two_le
  have iq : (2:ℤ)≤q := by exact_mod_cast hq.two_le
  have ord : (p:ℤ)≤q := by exact_mod_cast pq.le
  have u : ((p:ℤ)-1)*(q-1)≤(q:ℤ)*q :=
    mul_le_mul (by omega) (by omega) (by omega) (by omega)
  have wle : (A:ℤ)+(S:ℤ)*((p:ℤ)-1)*((q:ℤ)-1)≤A+S*(q:ℤ)^2 := by
    nlinarith only [mul_le_mul_of_nonneg_left u (Int.natCast_nonneg S)]
  have n : defect A S T p q ((a:ℤ)+1) ((d:ℤ)+1)≠0 := by exact_mod_cast nt
  rw [mul_right_comm (S:ℤ) ((q:ℤ)-1) ((p:ℤ)-1)] at x
  have w0 : (0:ℤ)≤(A:ℤ)+(S:ℤ)*((p:ℤ)-1)*((q:ℤ)-1) := add_nonneg (Int.natCast_nonneg A)
    (mul_nonneg (mul_nonneg (Int.natCast_nonneg S) (by omega)) (by omega))
  have k:=squeeze (P:=(p:ℤ)^a) (Q:=(q:ℤ)^d) n (by exact_mod_cast Nat.one_le_pow a p hp.pos)
    (by exact_mod_cast Nat.one_le_pow d q hq.pos) x y w0 wle (by simpa only [add_assoc] using id)
  have result : min (p^a) (q^d)≤cost A S q M := by unfold cost;rw [Nat.add_assoc];exact_mod_cast k
  have pmin : p^(min a d)≤ min (p^a) (q^d) := le_min
    (Nat.pow_le_pow_right hp.pos (min_le_left _ _))
    ((Nat.pow_le_pow_right hp.pos (min_le_right _ _)).trans (Nat.pow_le_pow_left pq.le d))
  exact Nat.le_log_of_pow_le hp.one_lt (pmin.trans result)

end OMA.RankThreeFourSmallSeparation245212

end

section

/- Finite prime pairs need only a short exponent interval. A previously
excluded initial range of exponents may be skipped in the forward table. -/
namespace OMA.RankThreeFourSmallCut245212
open Nat ArithmeticFunction OMA.Smooth245212 OMA.CofactorEulerPair245212
open OMA.CofactorGuardFast245212 OMA.RankThreeFourSmallBounds245212
open scoped ArithmeticFunction.sigma
open OMA.CofactorEulerPair245212 (checked)

def initial (h A S T p q : ℕ) :=
  let E:=2*A*(p+q)/(A*p*q-2*T*(p-1)*(q-1))
  min E (OMA.CofactorPairRounding245212.threshold h A S p q E)

def horizon (h A S T p q : ℕ) :=
  let E:=initial h A S T p q
  let M:=OMA.RankThreeFourSmallDegree245212.degree A S p q E
  if M+1<q ∧ ¬q∣2*T then min E (Nat.log p (OMA.RankThreeFourSmallSeparation245212.cost A S q M)) else E

theorem horizon_sound {h p q a d : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime) (op : 3≤p)
    (cp : h.Coprime p) (cq : h.Coprime q) (pq : p<q) (ap : 0<a) (dp : 0<d)
    (big : 2*(h*σ 0 h)*(p-1)*(q-1)<W h*p*q)
    (eqn : OeisA245212.a (h*p^a*q^d)=(σ 1 (h*p^a*q^d):ℤ)) :
    min a d≤horizon h (W h) (σ 1 h) (h*σ 0 h) p q := by
  let A:=W h
  let S:=σ 1 h
  let T:=h*σ 0 h
  have b : Bal A S (2*T) p q a d := by simpa [A,S,T,Bal] using normalized hh hp hq cp cq pq.ne eqn
  have e:=short_pair hp hq big (strict hp hq (sigma_pos 1 h hh.ne') b)
  have raw:=(Nat.le_succ _).trans e
  have bound:=OMA.CofactorPairRounding245212.shortened hh hp hq op cp cq pq ap dp raw eqn
  have lo : min a d≤ initial h A S T p q := le_min raw bound.le
  obtain ⟨ab,db⟩:=OMA.RankThreeFourSmallDegree245212.both hh hp hq op cp cq pq ap dp lo eqn
  change min a d≤horizon h A S T p q
  unfold horizon
  dsimp only
  split
  next yes => exact le_min lo (OMA.RankThreeFourSmallSeparation245212.small hh hp hq cp cq pq ab db yes.1 yes.2 eqn)
  next _ => exact lo

def fixed (F h A S T p q : ℕ) :=
  if ¬q.Prime ∨ ¬h.Coprime q then true else
  if 2*T*(p-1)*(q-1)<A*p*q then
    let E:=horizon h A S T p q
    every (F+1) E (fastRow A S T p q) && every 1 E (fastRow A S T q p)
  else every 1 (2*(A+S*(p-1)*(q-1))/(A*q)) (fastRow A S T q p)

theorem fixed_sound {F h p q a d : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime) (op : 3≤p)
    (cp : h.Coprime p) (cq : h.Coprime q) (pq : p<q) (ap : F<a) (dp : 0<d)
    (ck : fixed F h (W h) (σ 1 h) (h*σ 0 h) p q=true) :
    OeisA245212.a (h*p^a*q^d)≠(σ 1 (h*p^a*q^d):ℤ) := by
  intro eqn
  let A:=W h
  let S:=σ 1 h
  let T:=h*σ 0 h
  have eligible : ¬(¬q.Prime ∨ ¬h.Coprime q) := by tauto
  have flip : OeisA245212.a (h*q^d*p^a)=(σ 1 (h*q^d*p^a):ℤ) := by rwa [mul_right_comm]
  have eqtable {x y e : ℕ} (pr : y.Prime) : fastRow A S T x y e=row A S T x y e := fastKnown_eq pr
  change fixed F h A S T p q=true at ck
  rw [fixed,if_neg eligible] at ck
  by_cases b : 2*T*(p-1)*(q-1)<A*p*q
  · rw [if_pos b,Bool.and_eq_true] at ck
    have bound:=horizon_sound hh hp hq op cp cq pq (by omega) dp b eqn
    rcases le_total a d with ad|da
    · rw [min_eq_left ad] at bound
      have z:=OMA.CofactorEulerPair245212.checked ck.1 ap bound
      exact row_sound hh hp hq (by omega) cp cq pq.ne dp ((eqtable hq) ▸ z) eqn
    · rw [min_eq_right da] at bound
      have z:=OMA.CofactorEulerPair245212.checked ck.2 dp bound
      exact row_sound hh hq hp (by omega) cq cp pq.ne.symm (by omega) ((eqtable hp) ▸ z) flip
  · rw [if_neg b] at ck
    have bal : Bal A S (2*T) p q a d := by simpa [A,S,T,Bal] using normalized hh hp hq cp cq pq.ne eqn
    have wp : 0<A := by
      dsimp [A];rw [w_apply]
      exact Finset.sum_pos' (fun _ _=>Nat.zero_le _) ⟨1,Nat.one_mem_divisors.mpr hh.ne',by simp⟩
    have lim:=under_pair hp hq wp bal (le_of_not_gt b)
    have z:=OMA.CofactorEulerPair245212.checked ck dp (Nat.le_trans (Nat.le_succ _) lim)
    exact row_sound hh hq hp (by omega) cq cp pq.ne.symm (by omega) ((eqtable hp) ▸ z) flip

end OMA.RankThreeFourSmallCut245212

end

section

/- Last-prime digit inequalities after separating the common large power
P=p^b. The two leading coefficients are affine in b+1. -/
namespace OMA.RankThreeFourSmallAffine245212
open Nat ArithmeticFunction OMA.Smooth245212
open scoped ArithmeticFunction.sigma

def du (A H p d : ℤ) := (d+1)*(p-1)*(H*(p-1)-A*p)
def dc (A S p d : ℤ) := p*((d+1)*A-S*(p-1))
def dr (A S p d : ℤ) := S*(p-1)-(d+1)*A
def nu (A p d : ℤ) := p*d*A*(p-1)
def nc (A S p d : ℤ) := p*(S*(p-1)-d*A)
def nr (A S p d : ℤ) := d*A-S*(p-1)

def starts (A S p R d : ℕ) :=
  Nat.log p (max (dr A S p d).natAbs (nr A S p d-((R:ℤ)-1)*dr A S p d).natAbs)+1

theorem inequalities {h p q b d R : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime)
    (cp : h.Coprime p) (cq : h.Coprime q) (pq : p<q) (dp : 0<d) (rq : R≤q)
    (big : starts (W h) (σ 1 h) p R d≤b)
    (eqn : OeisA245212.a (h*p^b*q^d)=(σ 1 (h*p^b*q^d):ℤ)) :
    let A:ℤ:=W h
    let S:ℤ:=σ 1 h
    let H:ℤ:=2*(h*σ 0 h:ℕ)
    let D:=du A H p d*(b+1)+dc A S p d
    let N:=nu A p d*(b+1)+nc A S p d
    0≤D ∧ ((R:ℤ)-1)*D≤N := by
  let A:ℤ:=W h
  let S:ℤ:=σ 1 h
  let H:ℤ:=2*(h*σ 0 h:ℕ)
  let P:ℤ:=(p:ℤ)^b
  let v:ℤ:=(p:ℤ)-1
  let D:=du A H p d*(b+1)+dc A S p d
  let N:=nu A p d*(b+1)+nc A S p d
  let D1:=dr A S p d
  let N1:=nr A S p d
  let V:=W (h*p^b)
  let Y:=σ 1 (h*p^b)
  let T:=(h*p^b)*σ 0 (h*p^b)
  let delta:=OMA.LastDigit245212.denom V Y T d
  have pp:=hp.pos
  have pos : 0<h*p^b := by positivity
  have cop:=(cq.mul_left (((coprime_primes hp hq).mpr pq.ne).pow_left b))
  obtain ⟨dpos,dlo,_,_⟩:=OMA.LastDigit245212.balance_digits pos hq cop dp eqn
  change 0<delta at dpos
  change delta*(q-1)<V*d+Y at dlo
  have subtract : delta+(V*(d+1)+Y)=2*T*(d+1) := Nat.sub_add_cancel
    (Nat.sub_pos_iff_lt.mp dpos).le
  have w : (V:ℤ)=A*W (p^b) := by
    simp only [V,A,w_mult.map_mul_of_coprime (cp.pow_right b),Nat.cast_mul]
  have s : (Y:ℤ)=S*σ 1 (p^b) := by
    simp only [Y,S,isMultiplicative_sigma.map_mul_of_coprime (cp.pow_right b),Nat.cast_mul]
  have t : (2:ℤ)*T=H*(b+1)*P := by
    dsimp [T,H,P]
    rw [isMultiplicative_sigma.map_mul_of_coprime (cp.pow_right b),sigma_zero_apply_prime_pow hp]
    push_cast;ring
  have loc:=OMA.ComplementaryLocal245212.moments hp b
  have sub : (delta:ℤ)+((V:ℤ)*(d+1)+Y)=2*T*(d+1) := by exact_mod_cast subtract
  have de : v^2*(delta:ℤ)=D*P+D1 := by
    rw [w,s,t] at sub
    dsimp [D,P,D1,v,du,dc,dr] at *
    linear_combination ((p:ℤ)-1)^2*sub - A*((d:ℤ)+1)*loc.2 - S*((p:ℤ)-1)*loc.1
  have ne : v^2*((V:ℤ)*d+Y)=N*P+N1 := by
    rw [w,s]
    dsimp [N,P,N1,v,nu,nc,nr]
    linear_combination A*(d:ℤ)*loc.2 + S*((p:ℤ)-1)*loc.1
  have qpos:=hq.pos
  have lower : (delta:ℤ)*((q:ℤ)-1)<V*d+Y := by
    zify [Nat.sub_le_sub_left qpos 0] at dlo
    simpa only [Nat.cast_sub (by omega : 1≤q),Nat.cast_one] using dlo
  have vpos : 0<v := sub_pos.mpr (by exact_mod_cast hp.one_lt)
  have gap : ((R:ℤ)-1)*(D*P+D1)<N*P+N1 := by
    have low := mul_lt_mul_of_pos_left lower (pow_pos vpos 2)
    have le := mul_le_mul_of_nonneg_right (by exact_mod_cast rq : (R:ℤ)≤q)
      (show 0≤v^2*(delta:ℤ) from mul_nonneg (sq_nonneg _) (Int.natCast_nonneg _))
    nlinarith only [low,le,congrArg (((R:ℤ)-1)*·) de,ne]
  have lowD : 0<D*P+D1 := by rw [←de]; exact mul_pos (sq_pos_of_pos
    (by dsimp [v]; exact sub_pos.mpr (by exact_mod_cast hp.one_lt))) (by exact_mod_cast dpos)
  have ppow : max D1.natAbs (N1-((R:ℤ)-1)*D1).natAbs<p^b :=
    (Nat.lt_pow_succ_log_self hp.one_lt _).trans_le (Nat.pow_le_pow_right hp.pos big)
  have vd : |D1|<P := by simpa [P] using (show (D1.natAbs:ℤ)<(p:ℤ)^b by
    exact_mod_cast (le_max_left _ _).trans_lt ppow)
  have vn : |N1-((R:ℤ)-1)*D1|<P := by simpa [P] using
    (show (((N1-((R:ℤ)-1)*D1).natAbs):ℤ)<(p:ℤ)^b by exact_mod_cast (le_max_right _ _).trans_lt ppow)
  change 0≤D ∧ ((R:ℤ)-1)*D≤N
  have pp' : 0<P := by dsimp [P];positivity
  constructor
  · by_contra! neg
    have := mul_le_mul_of_nonneg_right (show D≤ -1 by omega) pp'.le
    linarith only [this,lowD,(le_abs_self D1).trans_lt vd]
  · by_contra! neg
    have := mul_le_mul_of_nonneg_right (show N+1≤((R:ℤ)-1)*D by omega) pp'.le
    linarith only [this,gap,(le_abs_self _).trans_lt vn]
end OMA.RankThreeFourSmallAffine245212

end

section

/- A uniform effective restriction on every coprime part of a putative
solution, without assuming that its prime bases or exponents are fixed. -/
namespace OMA.CofactorHarmonic245212
open Nat Finset ArithmeticFunction OMA.Smooth245212
open scoped ArithmeticFunction.sigma
open OMA.LastDigit245212 (geom)

theorem phi_sigma (m : ℕ) : m.totient * σ 1 m ≤ m^2 := by
  induction m using Nat.recOnPrimeCoprime with
  | zero => simp
  | prime_pow p e hp =>
    cases e with
    | zero => simp
    | succ e =>
      rw [totient_prime_pow_succ hp,sigma_one_apply_prime_pow hp]
      have g := OMA.LastDigit245212.geom p (e+2) hp.pos
      have z := Nat.mul_le_mul_left (p^e)
        (show (∑ j∈range (e+2),p^j)*(p-1)≤p^(e+2) by omega)
      calc
        _ = p^e*((∑ j∈range (e+2),p^j)*(p-1)) := by ring
        _ ≤ _ := z
        _ = _ := by simp only [pow_succ];ring
  | coprime a b _ _ cop ia ib =>
    rw [totient_mul cop,isMultiplicative_sigma.map_mul_of_coprime cop,mul_pow]
    simpa only [mul_assoc,mul_left_comm,mul_comm] using Nat.mul_le_mul ia ib

private theorem divisor_bounds {m : ℕ} (hm : 1 < m) :
    m*(σ 0 m)≤W m ∧ m<σ 1 m ∧ W m≤(σ 0 m)*(σ 1 m) := by
  have nz : m≠0 := by omega
  constructor
  · rw [w_apply,sigma_zero_apply]
    exact single_le_sum (f:=fun d : ℕ => d*d.divisors.card)
      (fun _ _ => Nat.zero_le _) (Nat.mem_divisors_self _ nz)
  constructor
  · rw [sigma_one_apply,←Nat.insert_self_properDivisors nz,sum_insert Nat.self_notMem_properDivisors]
    have h := single_le_sum (f:=fun d : ℕ => d) (fun _ _ => Nat.zero_le _)
      (Nat.one_mem_properDivisors_iff_one_lt.mpr hm)
    omega
  · rw [w_apply,sigma_zero_apply,sigma_one_apply,mul_sum]
    exact sum_le_sum fun d hd => by
      rw [mul_comm m.divisors.card d]
      exact Nat.mul_le_mul_left d (Finset.card_le_card
        (Nat.divisors_subset_of_dvd nz (Nat.mem_divisors.mp hd).1))

/-- If h·m is a solution, the gap at the largest divisor of m is a
positive integer. The totient bound limits how much its other divisors
can contribute. -/
theorem gap {h m : ℕ} (hh : 0<h) (hm : 1 < m) (cop : h.Coprime m)
    (eqn : OeisA245212.a (h*m)=(σ 1 (h*m):ℤ)) :
    W h*(σ 0 m)+σ 1 h < 2*(h*σ 0 h)*(σ 0 m) ∧
    2*(h*σ 0 h)*(σ 0 m)*m.totient ≤ (W h*σ 0 m+σ 1 h)*m := by
  have mp : 0 < m := by omega
  have s := sigma_pos 1 h hh.ne'
  have b := OMA.Abundance245212.balance (mul_ne_zero hh.ne' mp.ne') eqn
  rw [w_mult.map_mul_of_coprime cop,isMultiplicative_sigma.map_mul_of_coprime cop,
    isMultiplicative_sigma.map_mul_of_coprime cop] at b
  obtain ⟨l,r,u⟩ := divisor_bounds hm
  constructor
  · apply Nat.lt_of_mul_lt_mul_right (a:=m)
    nlinarith only [b,Nat.mul_le_mul_left (W h) l,Nat.mul_lt_mul_of_pos_left r s]
  · apply Nat.le_of_mul_le_mul_right _ mp
    have v := Nat.mul_le_mul_right m.totient (Nat.mul_le_mul_left (W h) u)
    have w := Nat.mul_le_mul_left (W h*σ 0 m+σ 1 h) (phi_sigma m)
    nlinarith only [congrArg (fun t : ℕ => t*m.totient) b,v,w]

/-- Uniform bound independent of the prime exponents inside m. -/
theorem totient_gap {h m : ℕ} (hh : 0<h) (hm : 1 < m) (cop : h.Coprime m)
    (eqn : OeisA245212.a (h*m)=(σ 1 (h*m):ℤ)) :
    (2*(h*σ 0 h)-W h)*m ≤ 2*(h*σ 0 h)*(σ 1 h+1)*(m-m.totient) := by
  obtain ⟨strict,cap⟩ := gap hh hm cop eqn
  let H := 2*(h*σ 0 h)
  let A := W h
  let S := σ 1 h
  let L := σ 0 m
  change A*L+S < H*L at strict
  change H*L*m.totient ≤ (A*L+S)*m at cap
  change (H-A)*m ≤ H*(S+1)*(m-m.totient)
  have al : A≤H := by
    by_contra! no
    exact (not_le_of_gt strict) ((Nat.mul_le_mul_right L no.le).trans (Nat.le_add_right _ _))
  have D := Nat.sub_add_cancel al
  have E : S+1≤(H-A)*L := by nlinarith only [strict,congrArg (·*L) D]
  have mu := Nat.sub_add_cancel m.totient_le
  have bound : ((H-A)*L-S)*m≤H*L*(m-m.totient) := by
    have diff := Nat.sub_add_cancel (show S≤(H-A)*L by omega)
    nlinarith only [cap,congrArg (·*m*L) D,congrArg (·*m) diff,congrArg (H*L*·) mu]
  have low : (H-A)*L ≤ (S+1)*((H-A)*L-S) := by
    have diff := Nat.sub_add_cancel (show S≤(H-A)*L by omega)
    have one : 1≤(H-A)*L-S := by omega
    nlinarith only [diff,Nat.mul_le_mul_left S one]
  apply Nat.le_of_mul_le_mul_right _ (sigma_pos 0 m (by omega : m≠0))
  nlinarith only [Nat.mul_le_mul_right m low,Nat.mul_le_mul_left (S+1) bound]

private theorem union_bound (s : Finset ℕ) (hp : ∀ p∈s,0 < p) :
    1-(∏ p∈s,(1-(p:ℚ)⁻¹)) ≤ ∑ p∈s,(p:ℚ)⁻¹ := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s out ih =>
    have pp : 0<p := hp p (mem_insert_self ..)
    have tail (q : ℕ) (hq : q∈s) := hp q (mem_insert_of_mem hq)
    have unit (q : ℕ) (hq : q∈s) : 0≤1-(q:ℚ)⁻¹ := by
      have pos : (1:ℚ)≤q := by exact_mod_cast tail q hq
      have v := (inv_le_one₀ (by linarith : (0:ℚ)<q)).mpr pos
      linarith
    have bound : (∏ q∈s,(1-(q:ℚ)⁻¹))≤1 :=
      prod_le_one (fun q hq => unit q hq) (fun _ _ => by simp)
    have p0 : (0:ℚ)≤(p:ℚ)⁻¹ := by positivity
    rw [prod_insert out,sum_insert out]
    nlinarith only [ih tail,mul_le_mul_of_nonneg_left bound p0]

private theorem to_mass {m D scale : ℕ} (hm : 0 < m) (gap : D*m ≤ scale*(m-m.totient)) :
    (D:ℚ) ≤ (scale:ℚ) * ∑ p∈m.primeFactors,(p:ℚ)⁻¹ := by
  have rat : (D:ℚ)*m≤(scale:ℚ)*((m:ℚ)-(m.totient:ℚ)) := by
    rw [←Nat.cast_sub m.totient_le]
    exact_mod_cast gap
  rw [Nat.totient_eq_mul_prod_factors m] at rat
  have mass := union_bound m.primeFactors (fun _ hp => Nat.pos_of_mem_primeFactors hp)
  change (D:ℚ)≤(scale:ℚ)*_
  apply le_of_mul_le_mul_left (a:=(m:ℚ)) _ (by exact_mod_cast (show 0 < m by omega))
  nlinarith only [rat,mul_le_mul_of_nonneg_left mass (by positivity : 0≤(m:ℚ)*scale)]

/-- The distinct new primes must contribute a positive, explicit total
reciprocal mass determined solely by the known factor h. -/
theorem reciprocals {h m : ℕ} (hh : 0<h) (hm : 1 < m) (cop : h.Coprime m)
    (eqn : OeisA245212.a (h*m)=(σ 1 (h*m):ℤ)) :
    ((2*(h*σ 0 h)-W h:ℕ):ℚ) ≤
      (2*(h*σ 0 h)*(σ 1 h+1):ℕ) * ∑ p∈m.primeFactors,(p:ℚ)⁻¹ :=
  to_mass (by omega) (totient_gap hh hm cop eqn)

/-- If the remaining exponents are prescribed, use their actual divisor
count to sharpen the lower bound. Its numerator is a positive integer. -/
theorem count_sensitive {h m : ℕ} (hh : 0<h) (hm : 1 < m) (cop : h.Coprime m)
    (eqn : OeisA245212.a (h*m)=(σ 1 (h*m):ℤ)) :
    let H := 2*(h*σ 0 h)*(σ 0 m)
    let A := W h*σ 0 m+σ 1 h
    0<H-A ∧ ((H-A:ℕ):ℚ) ≤ (H:ℚ)*∑ p∈m.primeFactors,(p:ℚ)⁻¹ := by
  obtain ⟨l,c⟩:=gap hh hm cop eqn
  dsimp only
  refine ⟨by omega,to_mass (by omega) ?_⟩
  have d := Nat.sub_add_cancel l.le
  have f := Nat.sub_add_cancel m.totient_le
  nlinarith only [c,congrArg (·*m) d,congrArg ((2*(h*σ 0 h)*(σ 0 m))*·) f]

theorem from_mass {r H D m : ℕ} (lower : ∀ p∈m.primeFactors,r≤p)
    (mass : (D:ℚ)≤(H:ℚ)*∑ p∈m.primeFactors,(p:ℚ)⁻¹) : r*D ≤ m.primeFactors.card*H := by
  have per (p : ℕ) (hp : p∈m.primeFactors) : (r:ℚ)*(p:ℚ)⁻¹≤1 := by
    rw [←div_eq_mul_inv,div_le_one (by exact_mod_cast Nat.pos_of_mem_primeFactors hp : (0:ℚ)<p)]
    exact_mod_cast lower p hp
  have cap := sum_le_sum per
  simp only [←mul_sum,sum_const,nsmul_eq_mul,mul_one] at cap
  exact_mod_cast (show (r:ℚ)*D≤(m.primeFactors.card:ℚ)*H by
    nlinarith only [mul_le_mul_of_nonneg_left mass (Nat.cast_nonneg r),
      mul_le_mul_of_nonneg_left cap (Nat.cast_nonneg H)])

/-- Taking r to be the least new prime gives an integer bound linear
in the number of remaining prime factors and independent of all exponents. -/
theorem least_prime {h m r : ℕ} (hh : 0<h) (hm : 1 < m) (cop : h.Coprime m)
    (lower : ∀ p∈m.primeFactors,r≤p) (eqn : OeisA245212.a (h*m)=(σ 1 (h*m):ℤ)) :
    r*(2*(h*σ 0 h)-W h) ≤ m.primeFactors.card*(2*(h*σ 0 h)*(σ 1 h+1)) :=
  from_mass lower (reciprocals hh hm cop eqn)

end OMA.CofactorHarmonic245212

end

section

/- A uniform first-prime bound with the remaining divisor count retained. -/
namespace OMA.RankThreeFourSmallHarmonic245212
open Nat Finset ArithmeticFunction OMA.Smooth245212
open scoped ArithmeticFunction.sigma
open OMA.CofactorHarmonic245212 (from_mass)

def lengthCut (A S H : ℕ) := max 4 (S/(H-A)+1)
def primeCut (A S H : ℕ) :=
  let L:=lengthCut A S H
  2*H*L/((H-A)*L-S)

theorem count_cap {h p q a d : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime)
    (cp : h.Coprime p) (cq : h.Coprime q) (pq : p<q) (ap : 0<a) (dp : 0<d)
    (eqn : OeisA245212.a (h*p^a*q^d)=(σ 1 (h*p^a*q^d):ℤ)) :
    let H:=2*(h*σ 0 h)
    let A:=W h
    let S:=σ 1 h
    let n:=(a+1)*(d+1)
    (H-A)*n>S ∧ p*((H-A)*n-S)≤2*H*n := by
  let A:=W h
  let S:=σ 1 h
  let H:=2*(h*σ 0 h)
  let m:=p^a*q^d
  let n:=(a+1)*(d+1)
  let D:=H-A
  have fact : m.primeFactors={p,q} := by
    simp [m,Nat.primeFactors_mul (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hq.ne_zero),
      Nat.primeFactors_pow _ ap.ne',Nat.primeFactors_pow _ dp.ne',hp.primeFactors,hq.primeFactors]
  have low : ∀ x∈m.primeFactors,p≤x := by rw [fact];simp [pq.le]
  have card : m.primeFactors.card=2 := by rw [fact];simp [pq.ne]
  have dcnt : (σ 0 m:ℕ)=n := by
    have cop := (((coprime_primes hp hq).mpr pq.ne).pow_left a).pow_right d
    simp [m,n,isMultiplicative_sigma.map_mul_of_coprime cop,sigma_zero_apply_prime_pow,hp,hq]
  have m1 : 1 < m := (Nat.one_lt_pow ap.ne' hp.one_lt).trans_le (Nat.le_mul_of_pos_right _ (pow_pos hq.pos _))
  have eq := OMA.CofactorHarmonic245212.count_sensitive hh m1
    ((cp.pow_right a).mul_right (cq.pow_right d)) (by simpa [m,mul_assoc] using eqn)
  dsimp only at eq
  rw [dcnt] at eq
  have cap:=OMA.CofactorHarmonic245212.from_mass low eq.2
  rw [card] at cap
  change p*(H*n-(A*n+S))≤2*(H*n) at cap
  have sign : A*n+S<H*n := by exact Nat.sub_pos_iff_lt.mp eq.1
  have dh : A<H := by
    by_contra! bad
    have := Nat.mul_le_mul_right n bad
    omega
  have dt : D+A=H := Nat.sub_add_cancel dh.le
  have key : (H*n-(A*n+S))+S=D*n := by
    have z := Nat.sub_add_cancel sign.le
    nlinarith only [z,congrArg (·*n) dt]
  have dn : S<D*n := by
    have z := Nat.sub_pos_iff_lt.mpr sign
    omega
  have dpos : 0<D := Nat.sub_pos_of_lt dh
  change D*n>S ∧ p*(D*n-S)≤2*H*n
  refine ⟨dn,?_⟩
  rw [←key,Nat.add_sub_cancel]
  simpa only [mul_assoc] using cap

theorem first_prime {h p q a d : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime)
    (cp : h.Coprime p) (cq : h.Coprime q) (pq : p<q) (ap : 0<a) (dp : 0<d)
    (eqn : OeisA245212.a (h*p^a*q^d)=(σ 1 (h*p^a*q^d):ℤ)) :
    p≤primeCut (W h) (σ 1 h) (2*(h*σ 0 h)) := by
  let A:=W h
  let S:=σ 1 h
  let H:=2*(h*σ 0 h)
  let m:=p^a*q^d
  let n:=(a+1)*(d+1)
  let D:=H-A
  let L:=lengthCut A S H
  have fact : m.primeFactors={p,q} := by
    simp [m,Nat.primeFactors_mul (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hq.ne_zero),
      Nat.primeFactors_pow _ ap.ne',Nat.primeFactors_pow _ dp.ne',hp.primeFactors,hq.primeFactors]
  have low : ∀ x∈m.primeFactors,p≤x := by rw [fact];simp [pq.le]
  have card : m.primeFactors.card=2 := by rw [fact];simp [pq.ne]
  have dcnt : (σ 0 m:ℕ)=n := by
    have cop := (((coprime_primes hp hq).mpr pq.ne).pow_left a).pow_right d
    simp [m,n,isMultiplicative_sigma.map_mul_of_coprime cop,sigma_zero_apply_prime_pow,hp,hq]
  have m1 : 1 < m := (Nat.one_lt_pow ap.ne' hp.one_lt).trans_le (Nat.le_mul_of_pos_right _ (pow_pos hq.pos _))
  have eq := OMA.CofactorHarmonic245212.count_sensitive hh m1
    ((cp.pow_right a).mul_right (cq.pow_right d)) (by simpa [m,mul_assoc] using eqn)
  dsimp only at eq
  rw [dcnt] at eq
  have cap:=OMA.CofactorHarmonic245212.from_mass low eq.2
  rw [card] at cap
  change p*(H*n-(A*n+S))≤2*(H*n) at cap
  have sign : A*n+S<H*n := by exact Nat.sub_pos_iff_lt.mp eq.1
  have dh : A<H := by
    by_contra! bad
    have := Nat.mul_le_mul_right n bad
    omega
  have dt : D+A=H := Nat.sub_add_cancel dh.le
  have key : (H*n-(A*n+S))+S=D*n := by
    have z := Nat.sub_add_cancel sign.le
    nlinarith only [z,congrArg (·*n) dt]
  have dn : S<D*n := by
    have z := Nat.sub_pos_iff_lt.mpr sign
    omega
  have dpos : 0<D := Nat.sub_pos_of_lt dh
  have n4 : 4≤n := Nat.mul_le_mul (by omega : 2≤a+1) (by omega : 2≤d+1)
  have ls : S/D+1≤n := by
    have := (Nat.div_lt_iff_lt_mul dpos).mpr (by simpa only [Nat.mul_comm] using dn)
    omega
  have ln : L≤n := max_le n4 ls
  have divpos := Nat.lt_mul_div_succ S dpos
  have ld : S<D*L := divpos.trans_le (Nat.mul_le_mul_left D (le_max_right _ _))
  have subtract := Nat.sub_add_cancel ld.le
  apply (Nat.le_div_iff_mul_le (Nat.sub_pos_of_lt ld)).mpr
  change p*(D*L-S)≤2*H*L
  have np : 0<n := by omega
  apply Nat.le_of_mul_le_mul_right (c:=n) _ np
  have scale := Nat.mul_le_mul_right L cap
  have shift := Nat.mul_le_mul_left (p*S) ln
  nlinarith only [scale,shift,congrArg (fun t:ℕ=>p*t*L) key,
    congrArg (fun t:ℕ=>p*t*n) subtract]
end OMA.RankThreeFourSmallHarmonic245212

end

section

/- Direct digit replay on the interval of exponents allowed by the
two affine leading coefficients. -/
namespace OMA.RankThreeFourSmallBand245212
open Nat ArithmeticFunction OMA.Smooth245212 OMA.CofactorEulerPair245212
open OMA.RankThreeFourSmallAffine245212
open scoped ArithmeticFunction.sigma
open OMA.CofactorEulerPair245212 (checked)
open OMA.Large245212 (force)
open OMA.Large245212 (moments)
open OMA.PairExtension245212 (fit)

def bit (A S T p R d b : ℕ) : Bool :=
  let V:=A*OMA.Large245212.wt p b
  let Y:=S*OMA.Large245212.sig p b
  let J:=T*OMA.Large245212.tax p b
  let den:=OMA.LastDigit245212.denom V Y J d
  let q:=OMA.Large245212.candidate V Y J d
  decide (den=0 ∨ q<R) || !OMA.PairExtension245212.permitted V Y J q d

theorem bit_sound {h p q b d R : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime)
    (cp : h.Coprime p) (cq : h.Coprime q) (pq : p<q) (dp : 0<d) (rq : R≤q)
    (eqn : OeisA245212.a (h*p^b*q^d)=(σ 1 (h*p^b*q^d):ℤ)) :
    bit (W h) (σ 1 h) (h*σ 0 h) p R d b≠true := by
  have pp:=hp.pos
  have mp : 0<h*p^b := by positivity
  have cop:=(cq.mul_left (((coprime_primes hp hq).mpr pq.ne).pow_left b))
  have z:=OMA.LastDigit245212.balance_digits mp hq cop dp eqn
  have val:=OMA.Large245212.force (sigma_pos 1 _ mp.ne') hq.one_lt z.1 z.2.1 z.2.2.1
  have fit:=OMA.PairExtension245212.fit mp hq cop dp eqn
  have cc:=cp.pow_right b
  obtain ⟨sg,ww⟩:=OMA.Large245212.moments hp b
  have sz:=(show 0<OMA.LastDigit245212.denom (W (h*p^b)) (σ 1 (h*p^b))
    ((h*p^b)*σ 0 (h*p^b)) d from z.1)
  rw [w_mult.map_mul_of_coprime cc,isMultiplicative_sigma.map_mul_of_coprime cc,
    isMultiplicative_sigma.map_mul_of_coprime cc,sigma_zero_apply_prime_pow hp,←sg,←ww] at sz val fit
  have t : (h*p^b)*(σ 0 h*(b+1))=h*σ 0 h*OMA.Large245212.tax p b := by unfold OMA.Large245212.tax;ring
  rw [t] at sz val fit
  simp [bit,sz.ne',val,not_lt.mpr rq,fit]

def slope (A _S H p R d : ℕ) := ((R:ℤ)-1)*du A H p d-nu A p d
def intercept (A S p R d : ℕ) := nc A S p d-((R:ℤ)-1)*dc A S p d
def lower (A S H p d : ℕ) := ((-dc A S p d)/du A H p d).toNat-1
def upper (A S H p R d : ℕ) := (intercept A S p R d/slope A S H p R d).toNat

def band (A S T p R BB d : ℕ) :=
  let J:=starts A S p R d
  let hi:=min BB (upper A S (2*T) p R d)
  (decide (0<du A (2*T) p d ∧ 0<slope A S (2*T) p R d)) &&
    every 1 (min BB (J-1)) (bit A S T p R d) &&
    every (max J (lower A S (2*T) p d)) hi (bit A S T p R d)

theorem band_sound {h p q b d R BB : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime)
    (cp : h.Coprime p) (cq : h.Coprime q) (pq : p<q) (bp : 0<b) (dp : 0<d)
    (rq : R≤q) (maxb : b≤BB) (ck : band (W h) (σ 1 h) (h*σ 0 h) p R BB d=true)
    (eqn : OeisA245212.a (h*p^b*q^d)=(σ 1 (h*p^b*q^d):ℤ)) : False := by
  let A:=W h
  let S:=σ 1 h
  let T:=h*σ 0 h
  let H:=2*T
  let J:=starts A S p R d
  change band A S T p R BB d=true at ck
  simp only [band,Bool.and_eq_true,decide_eq_true_eq] at ck
  apply bit_sound hh hp hq cp cq pq dp rq eqn
  by_cases short : b<J
  · exact OMA.CofactorEulerPair245212.checked ck.1.2 bp (le_min maxb (by omega))
  obtain ⟨lo,hi⟩:=inequalities hh hp hq cp cq pq dp rq (le_of_not_gt short) eqn
  change 0≤du A H p d*((b:ℤ)+1)+dc A S p d at lo
  change ((R:ℤ)-1)*(du A H p d*((b:ℤ)+1)+dc A S p d)≤nu A p d*((b:ℤ)+1)+nc A S p d at hi
  have u0 := ck.1.1.1
  have v0 := ck.1.1.2
  change 0<du A H p d at u0
  change 0<slope A S H p R d at v0
  have ll : -dc A S p d/du A H p d≤(b:ℤ)+1 := by
    apply Int.ediv_le_of_le_mul u0
    nlinarith only [lo]
  have uu : (b:ℤ)+1≤ intercept A S p R d/slope A S H p R d := by
    apply (Int.le_ediv_iff_mul_le v0).mpr
    dsimp [intercept,slope]
    linarith only [hi]
  have lb : lower A S H p d≤b := by unfold lower;omega
  have ub : b≤upper A S H p R d := by unfold upper;omega
  exact OMA.CofactorEulerPair245212.checked ck.2 (max_le (by omega) lb) (le_min maxb ub)

def budget (A S H p d BB : ℕ) :=
  if 2*H<p*(H-A) then min BB (p*S/(p*(H-A)-2*H)/(d+1)-1) else BB

theorem budget_ge {h p q b d BB : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime)
    (cp : h.Coprime p) (cq : h.Coprime q) (pq : p<q) (bp : 0<b) (dp : 0<d) (maxb : b≤BB)
    (eqn : OeisA245212.a (h*p^b*q^d)=(σ 1 (h*p^b*q^d):ℤ)) :
    b≤budget (W h) (σ 1 h) (2*(h*σ 0 h)) p d BB := by
  let A:=W h
  let S:=σ 1 h
  let H:=2*(h*σ 0 h)
  let L:=(b+1)*(d+1)
  obtain ⟨pos,cut⟩:=OMA.RankThreeFourSmallHarmonic245212.count_cap hh hp hq cp cq pq bp dp eqn
  change S<(H-A)*L at pos
  change p*((H-A)*L-S)≤2*H*L at cut
  change b≤budget A S H p d BB
  unfold budget
  split
  next high =>
    have diff := Nat.sub_add_cancel high.le
    have rest := Nat.sub_add_cancel pos.le
    have x : L*(p*(H-A)-2*H)≤p*S := by
      nlinarith only [cut,congrArg (fun x:ℕ=>L*x) diff,congrArg (fun x:ℕ=>p*x) rest]
    have l := (Nat.le_div_iff_mul_le (Nat.sub_pos_of_lt high)).mpr x
    have zb : b+1≤p*S/(p*(H-A)-2*H)/(d+1) := (Nat.le_div_iff_mul_le (by omega)).mpr l
    exact le_min maxb (by omega)
  next _ => exact maxb

end OMA.RankThreeFourSmallBand245212

end

section

/- Dyadic exponent two, with three odd bases. Keeping one actual
Euler factor also gives a lower bound for each exponent near the cap. -/
namespace OMA.RankThreeFourLargeCap245212
open Finset Nat OMA.Smooth245212 OMA.OddFaces245212
open scoped ArithmeticFunction.sigma
open OMA.OddFaces245212 (envelope)

theorem norm {p q r a b c : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (po : 2<p) (pq : p<q) (qr : q<r)
    (eq : OeisA245212.a (4*p^a*q^b*r^c)=(σ 1 (4*p^a*q^b*r^c):ℤ)) :
    17*(X p (some a)*X q (some b)*X r (some c))+
      7*(Y p (some a)*Y q (some b)*Y r (some c))=24 := by
  let P : Fin 4 → ℕ := ![2,p,q,r]
  let E : Fin 4 → ℕ := ![2,a,b,c]
  have pr (i : Fin 4) : (P i).Prime := by fin_cases i <;> simp [P,hp,hq,hr,prime_two]
  have inj : P.Injective := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all [P] <;> omega
  have repr : total P E=4*p^a*q^b*r^c := by simp [total,Fin.prod_univ_four,P,E,mul_assoc]
  have n := normalized_of_eq P pr inj E (repr ▸ eq)
  have x : X 2 (some 2)=17/12 := by decide +kernel
  have y : Y 2 (some 2)=7/12 := by decide +kernel
  simp [normalized,Fin.prod_univ_four,P,E,x,y] at n
  linarith

theorem caps {p q r a b c : ℕ} (hp : 1<p) (hq : 1<q) (hr : 1<r) (ap : 0<a)
    (eq : 17*(X p (some a)*X q (some b)*X r (some c))+
      7*(Y p (some a)*Y q (some b)*Y r (some c))=24) :
    24≤17*(limitX p*limitX q*limitX r) := by
  let P : Fin 3 → ℕ := ![p,q,r]
  let E : Fin 3 → ℕ := ![a,b,c]
  have pr (i : Fin 3) : 1<P i := by fin_cases i <;> simp [P,hp,hq,hr]
  have x : X 2 (some 2)=17/12 := by decide +kernel
  have y : Y 2 (some 2)=7/12 := by decide +kernel
  have val : X 2 (some 2)*(∏ i,X (P i) (some (E i)))+
      Y 2 (some 2)*(∏ i,Y (P i) (some (E i)))=2 := by
    rw [x,y]; simp [Fin.prod_univ_three,P,E]; linarith
  have t := OMA.DyadicEuler245212.cap_needed_at_two 2 P E pr 0 ap val
  simp [Fin.prod_univ_three,P,x] at t
  linarith

theorem one_cap {p q r a b c : ℕ} (hp : 5≤p) (hq : 1<q) (hr : 1<r) (bp : 0<b)
    (eq : 17*(X p (some a)*X q (some b)*X r (some c))+
      7*(Y p (some a)*Y q (some b)*Y r (some c))=24) :
    24≤17*X p (some a)*(limitX q*limitX r) := by
  have pg : 1<p := by omega
  have p' : (5:ℚ)≤p := by exact_mod_cast hp
  have sp : (0:ℚ)<p-1 := by linarith
  have yp := y_one pg (some a)
  have sum_bound : 17*X p (some a)+7*Y p (some a)≤24 := by
    unfold X; apply (le_of_mul_le_mul_right · sp)
    field_simp
    nlinarith only [mul_nonneg (sub_nonneg.mpr (show (24:ℚ)≤7*p by linarith)) (sub_nonneg.mpr yp)]
  let P : Fin 2 → ℕ := ![q,r]
  let E : Fin 2 → ℕ := ![b,c]
  have pr (i : Fin 2) : 1<P i := by fin_cases i <;> simp [P,hq,hr]
  have env := OMA.OddFaces245212.envelope univ P E pr
  simp [Fin.prod_univ_two,P,E] at env
  let T := Y q (some b)*Y r (some c)
  let U := limitX q*limitX r
  change X q (some b)*X r (some c)≤T+(1-T)*U at env
  have qb : Y q (some b)<1 := by simpa [y_avg hq] using OMA.Abundance245212.y_strict hq bp
  have ltT : T<1 := (mul_le_of_le_one_right (y_nonneg hq _) (y_one hr _)).trans_lt qb
  have T0 : 0≤T := mul_nonneg (y_nonneg hq _) (y_nonneg hr _)
  have W := mul_le_mul_of_nonneg_left env (mul_nonneg (by decide : (0:ℚ)≤17) (x_nonneg pg (some a)))
  change 24≤17*X p (some a)*U
  by_contra! bad
  have h : 17*(X p (some a)*(X q (some b)*X r (some c)))+7*(Y p (some a)*T)=24 := by
    simpa only [T,mul_assoc] using eq
  nlinarith only [W,h,mul_le_mul_of_nonneg_right sum_bound T0,mul_pos (sub_pos.mpr ltT) (sub_pos.mpr bad)]

end OMA.RankThreeFourLargeCap245212

end

section

/- Recover the bounded initial power of three and the cofactor moments. -/
namespace OMA.RankThreeFourSmallOriginal245212
open Nat Finset ArithmeticFunction OMA.Smooth245212 OMA.CofactorEulerPair245212
open OMA.RankThreeFourSmallHarmonic245212 OMA.RankThreeFourSmallDecision245212
open scoped ArithmeticFunction.sigma
open OMA.CofactorEulerPair245212 (checked)
open OMA.FixedExponents245212 (y_pos)
open OMA.Large245212 (moments)

def cert (a : ℕ) :=
  let A:=17*OMA.Large245212.wt 3 a
  let S:=7*OMA.Large245212.sig 3 a
  let T:=12*OMA.Large245212.tax 3 a
  every 5 (primeCut A S (2*T)) (atPrime (4*3^a) A S T)

theorem checked_row {p q a b c : ℕ} (hp : p.Prime) (hq : q.Prime) (lo : 5≤p) (pq : p<q)
    (bp : 0<b) (cp : 0<c) (ok : cert a=true) :
    OeisA245212.a (4*3^a*p^b*q^c)≠(σ 1 (4*3^a*p^b*q^c):ℤ) := by
  intro eqn
  have cop (r : ℕ) (hr : r.Prime) (low : 5≤r) : (4*3^a).Coprime r :=
    (((coprime_primes prime_two hr).mpr (by omega)).pow_left 2).mul_left
      (((coprime_primes (by decide : Nat.Prime 3) hr).mpr (by omega)).pow_left a)
  have c3 : (4:ℕ).Coprime (3^a) := (by decide : Nat.Coprime 4 3).pow_right a
  have base : W 4=17 ∧ σ 1 4=7 ∧ σ 0 4=3 := by decide +kernel
  obtain ⟨y,x⟩:=OMA.Large245212.moments (by decide : Nat.Prime 3) a
  have w : W (4*3^a)=17*OMA.Large245212.wt 3 a := by rw [w_mult.map_mul_of_coprime c3,base.1,x]
  have s : σ 1 (4*3^a)=7*OMA.Large245212.sig 3 a := by rw [isMultiplicative_sigma.map_mul_of_coprime c3,base.2.1,y]
  have t : (4*3^a)*σ 0 (4*3^a)=12*OMA.Large245212.tax 3 a := by
    rw [isMultiplicative_sigma.map_mul_of_coprime c3,base.2.2,sigma_zero_apply_prime_pow (by decide : Nat.Prime 3)]
    unfold OMA.Large245212.tax;ring
  have good:=cop p hp lo
  have other:=cop q hq (by omega)
  have pos : 0<4*3^a := by positivity
  have pm:=first_prime pos hp hq good other pq bp cp eqn
  apply prime_sound pos hp hq (by omega) good other pq bp cp _ eqn
  apply OMA.CofactorEulerPair245212.checked _ lo pm
  simpa only [cert,w,s,t] using ok

theorem exponent {p q a b c : ℕ} (hp : p.Prime) (hq : q.Prime) (lo : 5≤p) (pq : p<q)
    (eqn : OeisA245212.a (4*3^a*p^b*q^c)=(σ 1 (4*3^a*p^b*q^c):ℤ)) : a≤7 := by
  have e:=OMA.RankThreeFourLargeCap245212.norm (by decide : Nat.Prime 3) hp hq
    (by decide) (by omega) pq eqn
  have yz := mul_pos (OMA.FixedExponents245212.y_pos (by decide : Nat.Prime 3) a)
    (mul_pos (OMA.FixedExponents245212.y_pos hp b) (OMA.FixedExponents245212.y_pos hq c))
  have one (r d : ℕ) (pr : r.Prime) : 1≤X r (some d) :=
    le_add_of_nonneg_right (div_nonneg (sub_nonneg.mpr (y_one pr.one_lt _))
      (sub_nonneg.mpr (by exact_mod_cast pr.one_le)))
  have xz := mul_le_mul (one p b hp) (one q c hq) (by decide : (0:ℚ)≤1) (x_nonneg hp.one_lt _)
  by_contra! la
  have y:=y_anti (by decide : 1<3) (by omega : 8≤a)
  have xx : X 3 (some 8) ≤ X 3 (some a) := add_le_add_right
    (div_le_div_of_nonneg_right (sub_le_sub_left y 1) (by norm_num)) 1
  have start : 24≤17*X 3 (some 8) := by decide +kernel
  nlinarith only [e,yz,start,xx,mul_le_mul_of_nonneg_left xz (x_nonneg (by decide : 1<3) (some a))]

end OMA.RankThreeFourSmallOriginal245212

end

section

/- Fast arithmetic certificate with logarithmic finite-pair bounds and
an affine interval for each last exponent in the infinite-prime range. -/
namespace OMA.RankThreeFourSmallFast245212
open Nat ArithmeticFunction OMA.Smooth245212 OMA.CofactorEulerPair245212
open OMA.RankThreeFourSmallBounds245212 OMA.RankThreeFourSmallDecision245212
open OMA.RankThreeFourSmallCut245212 OMA.RankThreeFourSmallBand245212
open OMA.RankThreeFourSmallHarmonic245212 OMA.CofactorGuardFast245212
open scoped ArithmeticFunction.sigma
open OMA.CofactorEulerPair245212 (checked)

def raw (h A S T p q : ℕ) :=
  if 2*T*(p-1)*(q-1)<A*p*q then
    let E:=horizon h A S T p q
    every 1 E (fastRow A S T p q) && every 1 E (fastRow A S T q p)
  else every 1 (2*(A+S*(p-1)*(q-1))/(A*q)) (fastRow A S T q p)

def quick (h A S T p q : ℕ) :=
  if 37<q ∧ q.gcd (37!)≠1 then true else raw h A S T p q || !decide q.Prime

theorem quick_sound {h p q a d : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime) (op : 3≤p)
    (cp : h.Coprime p) (cq : h.Coprime q) (pq : p<q) (ap : 0<a) (dp : 0<d)
    (ck : quick h (W h) (σ 1 h) (h*σ 0 h) p q=true)
    (eqn : OeisA245212.a (h*p^a*q^d)=(σ 1 (h*p^a*q^d):ℤ)) : False := by
  have gc : ¬(37<q ∧ q.gcd (37!)≠1) := fun h=>h.2 (hq.coprime_factorial_of_lt h.1)
  rw [quick,if_neg gc] at ck
  simp only [hq,decide_true,Bool.not_true,Bool.or_false] at ck
  have possible : ¬(¬q.Prime ∨ ¬h.Coprime q) := by tauto
  apply fixed_sound (F:=0) hh hp hq op cp cq pq ap dp _ eqn
  simpa only [raw,fixed,if_neg possible] using ck

def far (_h A S T p R BB d : ℕ) :=
  let B:=budget A S (2*T) p d BB
  if B=0 then true else band A S T p R B d

def run (h A S T p : ℕ) :=
  if ¬p.Prime ∨ ¬h.Coprime p then true else
  if 2*T*(p-1)<A*p then every 1 (2*A/(A*p-2*T*(p-1))) (movingRow A S T p) else
  if A*p<2*T*(p-1) then
    every (p+1) (capQ A T p) (quick h A S T p) &&
    every 1 (lenD A S p) (far h A S T p (max (p+1) (capQ A T p+1)) (lenB A S T p))
  else false

theorem sound {h p q a d : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime) (op : 3≤p)
    (cp : h.Coprime p) (cq : h.Coprime q) (pq : p<q) (ap : 0<a) (dp : 0<d)
    (ck : run h (W h) (σ 1 h) (h*σ 0 h) p=true) :
    OeisA245212.a (h*p^a*q^d)≠(σ 1 (h*p^a*q^d):ℤ) := by
  intro eqn
  let A:=W h
  let S:=σ 1 h
  let T:=h*σ 0 h
  have b : Bal A S (2*T) p q a d := by simpa [A,S,T,Bal] using normalized hh hp hq cp cq pq.ne eqn
  have wp : 0<A := by
    dsimp [A];rw [w_apply]
    exact Finset.sum_pos' (fun _ _=>Nat.zero_le _) ⟨1,Nat.one_mem_divisors.mpr hh.ne',by simp⟩
  have eligible : ¬(¬p.Prime ∨ ¬h.Coprime p) := by tauto
  change run h A S T p=true at ck
  rw [run,if_neg eligible] at ck
  by_cases high : 2*T*(p-1)<A*p
  · rw [if_pos high] at ck
    have sh:=short_first hp hq high (strict hp hq (sigma_pos 1 h hh.ne') b)
    exact moving_row_sound hh hp hq (by omega) cp cq pq dp (OMA.CofactorEulerPair245212.checked ck ap (by omega)) eqn
  rw [if_neg high] at ck
  by_cases under : A*p<2*T*(p-1)
  · rw [if_pos under,Bool.and_eq_true] at ck
    by_cases qr : q≤capQ A T p
    · exact quick_sound hh hp hq op cp cq pq ap dp (OMA.CofactorEulerPair245212.checked ck.1 pq qr) eqn
    have sh := under_first hp hq b under
    have eb : a≤lenB A S T p := by change a≤4*S*(p-1)/_; change ¬q≤1+2*A*p/_ at qr; omega
    have low : A*p*q≤2*T*(p-1)*(q-1) := by
      let G:=2*T*(p-1)-A*p
      have val:=Nat.sub_add_cancel under.le
      have gs : 0<G := Nat.sub_pos_of_lt under
      have qq : 2*A*p/G+1≤q-1 := by change ¬q≤1+2*A*p/G at qr;omega
      have less := (Nat.div_lt_iff_lt_mul gs).mp (by omega : 2*A*p/G<q-1)
      have v:=Nat.sub_add_cancel (by omega : 1≤q)
      nlinarith only [less,congrArg (·*(q-1)) val,congrArg (A*p*·) v,Nat.zero_le (A*p)]
    have ed:=(Nat.le_div_iff_mul_le (Nat.mul_pos wp hq.pos)).mp (under_pair hp hq wp b low)
    have grow : (d+1)*(A*q)≤(2*(A+S*(p-1)))*q := by
      nlinarith only [ed,Nat.mul_le_mul_left (S*(p-1)) (Nat.sub_le q 1),Nat.le_mul_of_pos_right A hq.pos]
    have e0 : (d+1)*A≤2*(A+S*(p-1)) := Nat.le_of_mul_le_mul_right (by simpa only [mul_assoc] using grow) hq.pos
    have small : d≤lenD A S p := (Nat.le_succ _).trans ((Nat.le_div_iff_mul_le wp).mpr e0)
    have atD:=OMA.CofactorEulerPair245212.checked ck.2 dp small
    have bounded:=budget_ge hh hp hq cp cq pq ap dp eb eqn
    change a≤budget A S (2*T) p d (lenB A S T p) at bounded
    rw [far,if_neg (Nat.ne_of_gt (ap.trans_le bounded))] at atD
    exact band_sound hh hp hq cp cq pq ap dp (max_le pq (by omega)) bounded atD eqn
  · simp [under] at ck

def cert (a : ℕ) :=
  let A:=17*OMA.Large245212.wt 3 a
  let S:=7*OMA.Large245212.sig 3 a
  let T:=12*OMA.Large245212.tax 3 a
  every 5 (primeCut A S (2*T)) (run (4*3^a) A S T)

end OMA.RankThreeFourSmallFast245212

end

section

/- Bound a whole interval of second primes by a single first-exponent table. -/
namespace OMA.RankThreeFourSmallNear245212
open Nat ArithmeticFunction OMA.Smooth245212 OMA.CofactorEulerPair245212
open OMA.RankThreeFourSmallBounds245212 OMA.RankThreeFourSmallDegree245212
open OMA.RankThreeFourSmallDecision245212
open scoped ArithmeticFunction.sigma


private theorem incD (A S p E : ℕ) {q u : ℕ} (le : q≤u) :
    degree A S p q E≤degree A S p u E := by
  unfold degree;gcongr

private theorem incR (h A S p E : ℕ) {q u : ℕ} (le : q≤u) :
    OMA.CofactorPairRounding245212.threshold h A S p q E≤OMA.CofactorPairRounding245212.threshold h A S p u E := by
  unfold OMA.CofactorPairRounding245212.threshold OMA.CofactorPairRounding245212.cost OMA.CofactorPairRounding245212.ceiling OMA.CofactorPairRounding245212.bits;gcongr

private theorem incC (A S M : ℕ) {q u : ℕ} (le : q≤u) :
    OMA.RankThreeFourSmallSeparation245212.cost A S q M≤OMA.RankThreeFourSmallSeparation245212.cost A S u M := by
  unfold OMA.RankThreeFourSmallSeparation245212.cost;gcongr

def slab (h A S p l u : ℕ) :=
  let E:=2*A*(p+u)
  let T:=OMA.CofactorPairRounding245212.threshold h A S p u E
  let M:=degree A S p u T
  let Z:=if M+1<l then Nat.log p (OMA.RankThreeFourSmallSeparation245212.cost A S u M) else T
  degree A S p u (max Z (lenD A S p))

theorem slab_sound {h p q a d l u : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime)
    (op : 3≤p) (cp : h.Coprime p) (cq : h.Coprime q) (pq : p<q) (ap : 0<a) (dp : 0<d)
    (ql : l≤q) (qu : q≤u) (good : ¬q∣2*(h*σ 0 h))
    (eqn : OeisA245212.a (h*p^a*q^d)=(σ 1 (h*p^a*q^d):ℤ)) :
    a ≤ slab h (W h) (σ 1 h) p l u := by
  let A:=W h
  let S:=σ 1 h
  let H:=2*(h*σ 0 h)
  let E:=2*A*(p+u)
  let T:=OMA.CofactorPairRounding245212.threshold h A S p u E
  let M:=degree A S p u T
  let Z:=if M+1<l then Nat.log p (OMA.RankThreeFourSmallSeparation245212.cost A S u M) else T
  let L:=max Z (lenD A S p)
  have bal : Bal A S H p q a d := by simpa [A,S,H,Bal] using normalized hh hp hq cp cq pq.ne eqn
  have wp : 0<A := by
    dsimp [A];rw [w_apply]
    exact Finset.sum_pos' (fun _ _=>Nat.zero_le _) ⟨1,Nat.one_mem_divisors.mpr hh.ne',by simp⟩
  suffices sm : min a d≤L by
    exact ((both hh hp hq op cp cq pq ap dp sm eqn).1).trans (incD _ _ _ _ qu)
  by_cases high : H*(p-1)*(q-1)<A*p*q
  · have e:=short_pair hp hq high (strict hp hq (sigma_pos 1 h hh.ne') bal)
    have leE : min a d≤E := le_trans ((Nat.le_succ _).trans e) ((Nat.div_le_self _ _).trans (by dsimp [E]; gcongr))
    have rt:=OMA.CofactorPairRounding245212.shortened hh hp hq op cp cq pq ap dp leE eqn
    have t : min a d≤T := rt.le.trans (incR _ _ _ _ _ qu)
    apply le_trans _ (le_max_left Z _)
    dsimp only [Z]
    split
    next inside =>
      obtain ⟨x,y⟩:=both hh hp hq op cp cq pq ap dp t eqn
      have inc:=incD A S p T qu
      exact (OMA.RankThreeFourSmallSeparation245212.small hh hp hq cp cq pq (x.trans inc) (y.trans inc) (inside.trans_le ql) good eqn).trans
        (Nat.log_mono_right (incC _ _ _ qu))
    next _ =>exact t
  · have ed:=(Nat.le_div_iff_mul_le (Nat.mul_pos wp hq.pos)).mp (under_pair hp hq wp bal (le_of_not_gt high))
    have grow : (d+1)*(A*q)≤(2*(A+S*(p-1)))*q := by
      nlinarith only [ed,Nat.mul_le_mul_left (S*(p-1)) (Nat.sub_le q 1),Nat.le_mul_of_pos_right A hq.pos]
    have e0 : (d+1)*A≤2*(A+S*(p-1)) := Nat.le_of_mul_le_mul_right (by simpa only [mul_assoc] using grow) hq.pos
    exact (min_le_right a d).trans (((Nat.le_succ _).trans ((Nat.le_div_iff_mul_le wp).mpr e0)).trans (le_max_right _ _))


/-- A binary partition of the finite last-prime interval; only the largest
first exponent certified on one of its occupied components is needed. -/
def nearCap (h A S p Q : ℕ) :=
  (List.range (Nat.log 2 Q+1)).foldl (fun n i=>
    let l:=max (p+1) (2^i)
    let u:=min Q (2^(i+1))
    max n (if l≤u then slab h A S p l u else 0)) 0

private theorem all_le (l : List ℕ) (f : ℕ→ℕ) (z : ℕ) {i : ℕ} (mem : i∈l) :
    f i ≤ l.foldl (fun n j=>max n (f j)) z := by
  induction l generalizing z with
  | nil=>simp at mem
  | cons h t ih=>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp mem with rfl|rest
    · have keep (u : List ℕ) (x : ℕ) : x≤u.foldl (fun n j=>max n (f j)) x := by
        induction u generalizing x with
        | nil=>rfl
        | cons y u hyp=> exact (le_max_left _ _).trans (hyp _)
      exact (le_max_right _ _).trans (keep _ _)
    · exact ih _ rest

theorem near_bound {h p q a d Q : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime)
    (op : 3≤p) (cp : h.Coprime p) (cq : h.Coprime q) (pq : p<q) (ap : 0<a) (dp : 0<d)
    (qu : q≤Q) (good : ¬q∣2*(h*σ 0 h))
    (eqn : OeisA245212.a (h*p^a*q^d)=(σ 1 (h*p^a*q^d):ℤ)) :
    a≤nearCap h (W h) (σ 1 h) p Q := by
  let j:=Nat.log 2 q
  let l:=max (p+1) (2^j)
  let u:=min Q (2^(j+1))
  have low : l≤q:=max_le pq (Nat.pow_log_le_self _ hq.ne_zero)
  have high : q≤u:=le_min qu (Nat.lt_pow_succ_log_self (by decide) q).le
  let f (i : ℕ) := if max (p+1) (2^i) ≤ min Q (2^(i+1))
    then slab h (W h) (σ 1 h) p (max (p+1) (2^i)) (min Q (2^(i+1))) else 0
  have sm : a≤f j := by
    change a≤(if l≤u then slab _ _ _ _ l u else 0)
    rw [if_pos (low.trans high)]
    exact slab_sound hh hp hq op cp cq pq ap dp low high good eqn
  have mem : j∈List.range (Nat.log 2 Q+1) := List.mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right qu))
  have last:=sm.trans (all_le _ f 0 mem)
  exact last

end OMA.RankThreeFourSmallNear245212

end

section

/- A positive integral leading denominator bounds the candidate last prime
uniformly without computing the entire large prime power. -/
namespace OMA.RankThreeFourSmallFar245212
open Nat ArithmeticFunction OMA.Smooth245212 OMA.RankThreeFourSmallAffine245212
open OMA.RankThreeFourSmallDegree245212 OMA.CofactorEulerPair245212
open scoped ArithmeticFunction.sigma

def leading (A S H p d b : ℕ) := du A H p d*((b:ℤ)+1)+dc A S p d

def top (A S p d BB : ℕ) :=
  2*((nu A p d).natAbs*(BB+1)+(nc A S p d).natAbs+(nr A S p d).natAbs)+2

def little (A S p d : ℕ) := Nat.log p (2*(dr A S p d).natAbs)+1

theorem limited {h p q b d BB : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime)
    (cp : h.Coprime p) (cq : h.Coprime q) (pq : p<q) (dp : 0<d) (bb : b≤BB)
    (large : little (W h) (σ 1 h) p d ≤ b)
    (nonzero : leading (W h) (σ 1 h) (2*(h*σ 0 h)) p d b≠0)
    (eqn : OeisA245212.a (h*p^b*q^d)=(σ 1 (h*p^b*q^d):ℤ)) :
    q ≤ top (W h) (σ 1 h) p d BB := by
  let A:ℤ:=W h
  let S:ℤ:=σ 1 h
  let H:ℤ:=2*(h*σ 0 h:ℕ)
  let P:ℤ:=(p:ℤ)^b
  let v:ℤ:=(p:ℤ)-1
  let D:=du A H p d*(b+1)+dc A S p d
  let N:=nu A p d*(b+1)+nc A S p d
  let D1:=dr A S p d
  let N1:=nr A S p d
  let V:=W (h*p^b)
  let Y:=σ 1 (h*p^b)
  let T:=(h*p^b)*σ 0 (h*p^b)
  let delta:=OMA.LastDigit245212.denom V Y T d
  have pp:=hp.pos
  have pos : 0<h*p^b := by positivity
  have cop:=(cq.mul_left (((coprime_primes hp hq).mpr pq.ne).pow_left b))
  obtain ⟨dpos,dlo,_,_⟩:=OMA.LastDigit245212.balance_digits pos hq cop dp eqn
  change 0<delta at dpos
  change delta*(q-1)<V*d+Y at dlo
  have subtract : delta+(V*(d+1)+Y)=2*T*(d+1) := Nat.sub_add_cancel
    (Nat.sub_pos_iff_lt.mp dpos).le
  have w : (V:ℤ)=A*W (p^b) := by
    simp only [V,A,w_mult.map_mul_of_coprime (cp.pow_right b),Nat.cast_mul]
  have s : (Y:ℤ)=S*σ 1 (p^b) := by
    simp only [Y,S,isMultiplicative_sigma.map_mul_of_coprime (cp.pow_right b),Nat.cast_mul]
  have t : (2:ℤ)*T=H*(b+1)*P := by
    dsimp [T,H,P]
    rw [isMultiplicative_sigma.map_mul_of_coprime (cp.pow_right b),sigma_zero_apply_prime_pow hp]
    push_cast;ring
  have loc:=OMA.ComplementaryLocal245212.moments hp b
  have sub : (delta:ℤ)+((V:ℤ)*(d+1)+Y)=2*T*(d+1) := by exact_mod_cast subtract
  have de : v^2*(delta:ℤ)=D*P+D1 := by
    rw [w,s,t] at sub
    dsimp [D,P,D1,v,du,dc,dr] at *
    linear_combination ((p:ℤ)-1)^2*sub - A*((d:ℤ)+1)*loc.2 - S*((p:ℤ)-1)*loc.1
  have ne : v^2*((V:ℤ)*d+Y)=N*P+N1 := by
    rw [w,s]
    dsimp [N,P,N1,v,nu,nc,nr]
    linear_combination A*(d:ℤ)*loc.2 + S*((p:ℤ)-1)*loc.1
  have qpos:=hq.pos
  have lower : (delta:ℤ)*((q:ℤ)-1)<V*d+Y := by
    zify [Nat.sub_le_sub_left qpos 0] at dlo
    simpa only [Nat.cast_sub (by omega : 1≤q),Nat.cast_one] using dlo
  have vpos : 0<v := sub_pos.mpr (by exact_mod_cast hp.one_lt)
  have mag : 2*D1.natAbs < p^b :=
    (Nat.lt_pow_succ_log_self hp.one_lt _).trans_le (Nat.pow_le_pow_right hp.pos large)
  have magZ : 2*|D1| <P := by simpa [P] using (show 2*(D1.natAbs:ℤ)<(p:ℤ)^b by exact_mod_cast mag)
  have Ppos : 1≤P := by dsimp [P]; exact_mod_cast Nat.one_le_pow b p hp.pos
  have positive : 0<D*P+D1 := by rw [←de]; exact mul_pos (sq_pos_of_pos vpos) (by exact_mod_cast dpos)
  have dd : 1≤D := by
    change D≠0 at nonzero
    by_contra! bad
    have mul:=mul_le_mul_of_nonneg_right (show D≤ -1 by omega) (by omega : 0≤P)
    linarith only [positive, le_abs_self D1, magZ, mul, abs_nonneg D1]
  have lowD : P≤2*(D*P+D1) := by
    have mul:=mul_le_mul_of_nonneg_right dd (by omega : 0≤P)
    linarith only [mul,neg_abs_le D1,magZ]
  have capq := mul_lt_mul_of_pos_left lower (sq_pos_of_pos vpos)
  have lm : ((q:ℤ)-1)*P < 2*(N*P+N1) := by
    have mult := mul_le_mul_of_nonneg_left lowD (show 0≤(q:ℤ)-1 by omega)
    nlinarith only [capq,mult,ne,congrArg (((q:ℤ)-1)*·) de]
  let Z:=top (W h) (σ 1 h) p d BB
  have nn : N ≤ (nu A p d).natAbs*(BB+1:ℤ)+(nc A S p d).natAbs := by
    have cmp := mul_le_mul (le_abs_self (nu A p d)) (show (b:ℤ)+1≤(BB:ℤ)+1 by omega)
      (by positivity) (abs_nonneg _)
    dsimp [N];simpa using add_le_add cmp (le_abs_self (nc A S p d))
  have nn1 : N1≤(N1.natAbs:ℤ)*P := by
    simpa using (le_abs_self N1).trans (le_mul_of_one_le_right (abs_nonneg _) Ppos)
  have zx : (Z:ℤ)=2*((nu A p d).natAbs*((BB:ℤ)+1)+(nc A S p d).natAbs+N1.natAbs)+2 := by
    simp [Z,top,A,S,N1]
  have largeq : ((q:ℤ)-1)*P < ((Z:ℤ)-1)*P := by
    nlinarith only [lm,mul_le_mul_of_nonneg_right nn (show 0≤P by omega),nn1,congrArg (·*P) zx,Ppos]
  have order := lt_of_mul_lt_mul_right largeq (by omega : 0≤P)
  change q≤Z
  omega


open OMA.RankThreeFourSmallBand245212

def exceptional (A S H p d : ℕ) :=
  ((-dc A S p d)/du A H p d).toNat-1

def clipped (A S T p R BB d : ℕ) :=
  let E:=max (little A S p d) (degree A S p (top A S p d BB) d)
  let ex:=exceptional A S (2*T) p d
  band A S T p R (min BB E) d &&
    (if E<ex ∧ ex≤BB ∧ leading A S (2*T) p d ex=0 then bit A S T p R d ex else true)

theorem clipped_sound {h p q b d R BB : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime)
    (op : 3≤p) (cp : h.Coprime p) (cq : h.Coprime q) (pq : p<q) (bp : 0<b) (dp : 0<d)
    (rq : R≤q) (bb : b≤BB)
    (ck : clipped (W h) (σ 1 h) (h*σ 0 h) p R BB d=true)
    (eqn : OeisA245212.a (h*p^b*q^d)=(σ 1 (h*p^b*q^d):ℤ)) : False := by
  let A:=W h
  let S:=σ 1 h
  let T:=h*σ 0 h
  let H:=2*T
  let E:=max (little A S p d) (degree A S p (top A S p d BB) d)
  let ex:=exceptional A S H p d
  change (band A S T p R (min BB E) d && (if E<ex ∧ ex≤BB ∧ leading A S H p d ex=0 then _ else true))=true at ck
  rw [Bool.and_eq_true] at ck
  obtain ⟨bandOK,excOK⟩:=ck
  by_cases small : b≤E
  · exact band_sound hh hp hq cp cq pq bp dp rq (le_min bb small) bandOK eqn
  have init : little A S p d≤b := (le_max_left ..).trans (le_of_not_ge small)
  by_cases vanish : leading A S H p d b=0
  · have ds : 0<du A H p d := by
      simp only [band,Bool.and_eq_true,decide_eq_true_eq] at bandOK;exact bandOK.1.1.1
    have id : (-dc A S p d)/du A H p d=(b:ℤ)+1 := by
      have eq : -dc A S p d=((b:ℤ)+1)*du A H p d := by
        unfold leading at vanish; linarith only [vanish,mul_comm (du A H p d) ((b:ℤ)+1)]
      rw [eq,Int.mul_ediv_cancel _ ds.ne']
    have exb : ex=b := by change ((-dc A S p d)/du A H p d).toNat-1=b;rw [id];omega
    rw [exb,if_pos ⟨lt_of_not_ge small,bb,vanish⟩] at excOK
    change bit A S T p R d ex = true at excOK
    rw [exb] at excOK
    exact bit_sound hh hp hq cp cq pq dp rq eqn excOK
  · have largeq:=limited hh hp hq cp cq pq dp bb init vanish eqn
    have flipped : OeisA245212.a (h*q^d*p^b)=(σ 1 (h*q^d*p^b):ℤ) := by rwa [mul_right_comm]
    have t:=one hh hq hp cq cp pq.ne.symm (by omega) bp hp.one_lt le_rfl largeq (show d≤d from le_rfl) flipped
    exact small (t.trans (le_max_right _ _))

end OMA.RankThreeFourSmallFar245212

end

section

/- Dyadic last-prime ranges and the first-three-term divisor-count bound
keep the unrestricted cofactor test inexpensive near an Euler pole. -/
namespace OMA.RankThreeFourSmallCompact245212
open Nat ArithmeticFunction OMA.Smooth245212 OMA.CofactorEulerPair245212
open OMA.RankThreeFourSmallBounds245212 OMA.RankThreeFourSmallDecision245212
open OMA.RankThreeFourSmallBand245212 OMA.RankThreeFourSmallHarmonic245212
open OMA.RankThreeFourSmallNear245212 OMA.RankThreeFourSmallFar245212
open OMA.RankThreeFourSmallFast245212 (quick quick_sound)
open scoped ArithmeticFunction.sigma
open OMA.CofactorEulerPair245212 (checked)

def near (h A S T p Q : ℕ) :=
  if Q≤p+256 then every (p+1) Q (quick h A S T p) else
  ((2*T).primeFactorsList.all fun r=>decide (r≤p)) && every 1 (nearCap h A S p Q) (movingRow A S T p)

theorem near_sound {h p q a d Q : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime)
    (op : 3≤p) (cp : h.Coprime p) (cq : h.Coprime q) (pq : p<q) (ap : 0<a) (dp : 0<d)
    (qr : q≤Q) (ck : near h (W h) (σ 1 h) (h*σ 0 h) p Q=true)
    (eqn : OeisA245212.a (h*p^a*q^d)=(σ 1 (h*p^a*q^d):ℤ)) : False := by
  unfold near at ck
  split at ck
  · exact quick_sound hh hp hq op cp cq pq ap dp (OMA.CofactorEulerPair245212.checked ck pq qr) eqn
  · simp only [Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at ck
    have pos:=sigma_pos 0 h hh.ne'
    have good : ¬q∣2*(h*σ 0 h) := fun dv=>pq.not_ge (ck.1 q (Nat.mem_primeFactors_iff_mem_primeFactorsList.mp (hq.mem_primeFactors dv (by positivity))))
    have small:=near_bound hh hp hq op cp cq pq ap dp qr good eqn
    exact moving_row_sound hh hp hq (by omega) cp cq pq dp (OMA.CofactorEulerPair245212.checked ck.2 ap small) eqn

def capD (A S H p : ℕ) := budget A S H p 1 (lenD A S p)

theorem capD_sound {h p q b d : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime)
    (cp : h.Coprime p) (cq : h.Coprime q) (pq : p<q) (bp : 0<b) (dp : 0<d)
    (eqn : OeisA245212.a (h*p^b*q^d)=(σ 1 (h*p^b*q^d):ℤ))
    (prior : d≤lenD (W h) (σ 1 h) p) : d≤capD (W h) (σ 1 h) (2*(h*σ 0 h)) p := by
  let A:=W h
  let S:=σ 1 h
  let H:=2*(h*σ 0 h)
  let L:=(b+1)*(d+1)
  obtain ⟨pos,cut⟩:=count_cap hh hp hq cp cq pq bp dp eqn
  change S<(H-A)*L at pos
  change p*((H-A)*L-S)≤2*H*L at cut
  unfold capD budget
  split
  next high =>
    change 2*H<p*(H-A) at high
    have diff:=Nat.sub_add_cancel high.le
    have rest:=Nat.sub_add_cancel pos.le
    have x : L*(p*(H-A)-2*H)≤p*S := by
      nlinarith only [cut,congrArg (fun x:ℕ=>L*x) diff,congrArg (fun x:ℕ=>p*x) rest]
    have l := (Nat.le_div_iff_mul_le (Nat.sub_pos_of_lt high)).mpr x
    have two : (d+1)*2≤L := by dsimp [L]; nlinarith only [Nat.mul_le_mul_right (d+1) (show 2≤b+1 by omega)]
    have both:=(Nat.le_div_iff_mul_le (by decide : 0<2)).mpr (two.trans l)
    apply le_min prior
    change d≤p*S/(p*(H-A)-2*H)/2-1
    omega
  next _ => exact prior

def smallFar (A S T p R BB d : ℕ) :=
  let B:=budget A S (2*T) p d BB
  if B=0 then true else if B≤64 then band A S T p R B d else clipped A S T p R B d
def run (h A S T p : ℕ) :=
  if ¬p.Prime ∨ ¬h.Coprime p then true else
  if 2*T*(p-1)<A*p then every 1 (2*A/(A*p-2*T*(p-1))) (movingRow A S T p) else
  if A*p<2*T*(p-1) then
    near h A S T p (capQ A T p) &&
    every 1 (capD A S (2*T) p) (smallFar A S T p (max (p+1) (capQ A T p+1)) (lenB A S T p))
  else false

theorem sound {h p q a d : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime) (op : 3≤p)
    (cp : h.Coprime p) (cq : h.Coprime q) (pq : p<q) (ap : 0<a) (dp : 0<d)
    (ck : run h (W h) (σ 1 h) (h*σ 0 h) p=true) :
    OeisA245212.a (h*p^a*q^d)≠(σ 1 (h*p^a*q^d):ℤ) := by
  intro eqn
  let A:=W h
  let S:=σ 1 h
  let T:=h*σ 0 h
  have b : Bal A S (2*T) p q a d := by simpa [A,S,T,Bal] using normalized hh hp hq cp cq pq.ne eqn
  have wp : 0<A := by
    dsimp [A];rw [w_apply]
    exact Finset.sum_pos' (fun _ _=>Nat.zero_le _) ⟨1,Nat.one_mem_divisors.mpr hh.ne',by simp⟩
  have eligible : ¬(¬p.Prime ∨ ¬h.Coprime p) := by tauto
  change run h A S T p=true at ck
  rw [run,if_neg eligible] at ck
  by_cases high : 2*T*(p-1)<A*p
  · rw [if_pos high] at ck
    have sh:=short_first hp hq high (strict hp hq (sigma_pos 1 h hh.ne') b)
    exact moving_row_sound hh hp hq (by omega) cp cq pq dp (OMA.CofactorEulerPair245212.checked ck ap (by omega)) eqn
  rw [if_neg high] at ck
  by_cases under : A*p<2*T*(p-1)
  · rw [if_pos under,Bool.and_eq_true] at ck
    by_cases qr : q≤capQ A T p
    · exact near_sound hh hp hq op cp cq pq ap dp qr ck.1 eqn
    have sh := under_first hp hq b under
    have eb : a≤lenB A S T p := by change a≤4*S*(p-1)/_; change ¬q≤1+2*A*p/_ at qr; omega
    have low : A*p*q≤2*T*(p-1)*(q-1) := by
      let G:=2*T*(p-1)-A*p
      have val:=Nat.sub_add_cancel under.le
      have gs : 0<G := Nat.sub_pos_of_lt under
      have qq : 2*A*p/G+1≤q-1 := by change ¬q≤1+2*A*p/G at qr;omega
      have less := (Nat.div_lt_iff_lt_mul gs).mp (by omega : 2*A*p/G<q-1)
      have v:=Nat.sub_add_cancel (by omega : 1≤q)
      nlinarith only [less,congrArg (·*(q-1)) val,congrArg (A*p*·) v,Nat.zero_le (A*p)]
    have ed:=(Nat.le_div_iff_mul_le (Nat.mul_pos wp hq.pos)).mp (under_pair hp hq wp b low)
    have grow : (d+1)*(A*q)≤(2*(A+S*(p-1)))*q := by
      nlinarith only [ed,Nat.mul_le_mul_left (S*(p-1)) (Nat.sub_le q 1),Nat.le_mul_of_pos_right A hq.pos]
    have e0 : (d+1)*A≤2*(A+S*(p-1)) := Nat.le_of_mul_le_mul_right (by simpa only [mul_assoc] using grow) hq.pos
    have small : d≤lenD A S p := (Nat.le_succ _).trans ((Nat.le_div_iff_mul_le wp).mpr e0)
    have atD:=OMA.CofactorEulerPair245212.checked ck.2 dp (capD_sound hh hp hq cp cq pq ap dp eqn small)
    have bounded:=budget_ge hh hp hq cp cq pq ap dp eb eqn
    change a≤budget A S (2*T) p d (lenB A S T p) at bounded
    rw [smallFar,if_neg (Nat.ne_of_gt (ap.trans_le bounded))] at atD
    split at atD
    · exact band_sound hh hp hq cp cq pq ap dp (max_le pq (by omega)) bounded atD eqn
    · exact clipped_sound hh hp hq op cp cq pq ap dp (max_le pq (by omega)) bounded atD eqn
  · simp [under] at ck

def cert (a : ℕ) :=
  let A:=17*OMA.Large245212.wt 3 a
  let S:=7*OMA.Large245212.sig 3 a
  let T:=12*OMA.Large245212.tax 3 a
  every 5 (primeCut A S (2*T)) (run (4*3^a) A S T)

end OMA.RankThreeFourSmallCompact245212

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

/- The exact two-adic valuation of the ordinary divisor sum at each prime power. -/
namespace OMA.ExactSigma245212
open Finset ArithmeticFunction OMA.WeightVal245212
open scoped ArithmeticFunction.sigma

abbrev v₂ (n : ℕ) := n.factorization 2
lemma mul_val {x y : ℕ} (hx : x≠0) (hy : y≠0) : v₂ (x*y)=v₂ x+v₂ y := by
  simp only [v₂,Nat.factorization_mul hx hy,Finsupp.add_apply]

def surplus (p e : ℕ) : ℕ := if Odd e then v₂ (p+1)-1 else 0

theorem local_sigma {p : ℕ} (hp : p.Prime) (op : Odd p) (e : ℕ) :
    v₂ (σ 1 (p^e))=v₂ (e+1)+surplus p e := by
  have sp := sigma_pos 1 _ (pow_ne_zero e hp.ne_zero)
  rcases Nat.even_or_odd e with ev|od
  · have mod : σ 1 (p^e) ≡ e+1 [MOD 2] := by
      rw [sigma_one_apply_prime_pow hp]
      have b : p ≡ 1 [MOD 2] := Nat.odd_iff.mp op
      have h := Nat.ModEq.sum (s:=range (e+1)) (fun j _ =>
        show p^j ≡ 1 [MOD 2] by simpa using b.pow j)
      simpa using h
    have od1 : Odd (e+1) := ev.add_one
    have os : Odd (σ 1 (p^e)) := Nat.odd_iff.mpr (mod.trans (show e+1 ≡ 1 [MOD 2] from Nat.odd_iff.mp od1))
    have nev : ¬ Odd e := fun h => (Nat.not_even_iff_odd.mpr h) ev
    rw [surplus,if_neg nev,
      show v₂ (e+1)=0 from val_odd od1,show v₂ (σ 1 (p^e))=0 from val_odd os]
  · have nd : ¬2∣p := by have := Nat.odd_iff.mp op; omega
    have lte := padicValNat.pow_two_sub_one hp.one_lt nd (by omega : e+1≠0) od.add_one
    simp only [←Nat.factorization_def _ Nat.prime_two] at lte
    have fg : σ 1 (p^e)*(p-1)=p^(e+1)-1 := by
      rw [sigma_one_apply_prime_pow hp]; exact geom_sum_mul_of_one_le hp.one_lt.le _
    change v₂ (p^(e+1)-1)+1 = v₂ (p+1)+v₂ (p-1)+v₂ (e+1) at lte
    rw [←fg,mul_val sp.ne' (by have := hp.one_lt; omega)] at lte
    have pos : 1 ≤ v₂ (p+1) := (Nat.prime_two.pow_dvd_iff_le_factorization
      (by omega : p+1≠0)).mp (by simpa using even_iff_two_dvd.mp op.add_one)
    rw [surplus,if_pos od]
    omega

theorem sigma_two_odd (a : ℕ) : Odd (σ 1 (2^a)) := by
  rw [sigma_one_apply_prime_pow Nat.prime_two,sum_range_succ',Nat.odd_iff]
  have h : 2 ∣ ∑ i∈range a, 2^(i+1) :=
    dvd_sum (fun i _ => dvd_pow_self 2 (by omega))
  simp only [pow_zero]
  omega

/-- Positive x is 2^v times an odd number. -/
theorem exact_units (x : ℕ) (hx : x≠0) : ∃ u, Odd u ∧ x=2^v₂ x*u := by
  obtain ⟨k,u,ou,eq⟩ := Nat.exists_eq_two_pow_mul_odd hx
  refine ⟨u,ou,?_⟩
  have v : v₂ x=k := by
    calc
      _ = v₂ (2^k*u) := congrArg v₂ eq
      _ = k := by rw [mul_val (by positivity) ou.pos.ne',
                    show v₂ (2^k)=k from Nat.factorization_pow_self Nat.prime_two,
                    show v₂ u=0 from val_odd ou,add_zero]
  simpa only [v] using eq

theorem exact_residue {x : ℕ} (hx : x≠0) : x ≡ 2^v₂ x [MOD 2^(v₂ x+1)] := by
  obtain ⟨u,ou,eu⟩ := exact_units x hx
  have o : u ≡ 1 [MOD 2] := Nat.odd_iff.mp ou
  have h := o.mul_left' (2^v₂ x)
  simpa only [←eu,mul_one,←pow_succ] using h

theorem sum_of_lt {x y : ℕ} (hx : x≠0) (hy : y≠0) (h : v₂ x < v₂ y) :
    v₂ (x+y)=v₂ x := by
  have zd : 2^(v₂ x+1)∣y := (Nat.prime_two.pow_dvd_iff_le_factorization hy).mpr h
  apply identify (by omega)
  simpa only [add_zero] using (exact_residue hx).add (Nat.modEq_zero_iff_dvd.mpr zd)

theorem sum_of_equal {x y : ℕ} (hx : x≠0) (hy : y≠0) (h : v₂ x=v₂ y) :
    v₂ x < v₂ (x+y) := by
  have ry := exact_residue hy
  rw [←h] at ry
  have sum := (exact_residue hx).add ry
  rw [←Nat.mul_two,←pow_succ] at sum
  exact (Nat.prime_two.pow_dvd_iff_le_factorization (by omega : x+y≠0)).mp
    (Nat.modEq_zero_iff_dvd.mp (sum.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_refl _))))

end OMA.ExactSigma245212

end

section

/- All three two-adic orders in the divisor balance in terms of the exponents. -/
namespace OMA.BalanceOrders245212
open Finset Nat ArithmeticFunction OMA.Smooth245212 OMA.Abundance245212 OMA.ExactSigma245212
open scoped ArithmeticFunction.sigma Function

theorem orders {ι : Type*} [Fintype ι] (p e : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (op : ∀ i, Odd (p i)) (inj : Function.Injective p) (a : ℕ) :
    let n := 2^a*total p e
    let T := ∑ i, v₂ (e i+1)
    let E := ∑ i, v₂ (e i+2)
    let U := ∑ i, surplus (p i) (e i)
    v₂ (W n)+Fintype.card ι=T+E ∧ v₂ (σ 1 n)=T+U ∧
      v₂ (2*n*(σ 0 n))=T+(1+a+v₂ (a+1)) := by
  classical
  dsimp only
  let z (i : ι) := p i^e i
  have cop : (↑(univ : Finset ι) : Set ι).Pairwise (Coprime on z) := by
    intro i _ j _ ne
    exact (((Nat.coprime_primes (hp i) (hp j)).mpr (fun h => ne (inj h))).pow_left _).pow_right _
  have oc : (2:ℕ).Coprime (total p e) := Coprime.prod_right (fun i _ =>
    (Nat.coprime_two_left.mpr (op i)).pow_right (e i))
  have co := oc.pow_left a
  have zn : total p e ≠ 0 := prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hp i).ne_zero)
  have wpos (i : ι) : W (z i) ≠ 0 := by
    rw [show z i=p i^e i from rfl,w_pow (hp i)]
    exact (sum_pos' (fun _ _ => Nat.zero_le _) ⟨0,mem_range.mpr (by omega),by simp⟩).ne'
  have wm : W (total p e) = ∏ i, W (z i) := IsMultiplicative.map_prod z w_mult univ cop
  have tm : σ 0 (total p e) = ∏ i, (e i+1) := by
    simpa only [z,total,sigma_zero_apply_prime_pow (hp _)] using
      IsMultiplicative.map_prod z (isMultiplicative_sigma (k:=0)) univ cop
  have sm : σ 1 (total p e) = ∏ i, σ 1 (z i) :=
    IsMultiplicative.map_prod z (isMultiplicative_sigma (k:=1)) univ cop
  have vp (f : ι → ℕ) (hf : ∀ i, f i≠0) :
      v₂ (∏ i, f i) = ∑ i, v₂ (f i) := Nat.factorization_prod_apply fun i _ => hf i
  have wa := OMA.DyadicPower245212.dyadic_odd a
  have sa := sigma_two_odd a
  constructor
  · rw [w_mult.map_mul_of_coprime co,wm,mul_val wa.pos.ne' (prod_ne_zero_iff.mpr (fun i _ => wpos i)),
      show v₂ (W (2^a))=0 from OMA.WeightVal245212.val_odd wa,zero_add,vp _ wpos]
    have h := sum_congr (s₁:=univ) rfl (fun i _ => OMA.WeightVal245212.weight_local (hp i) (op i) (e i))
    simp only [sum_add_distrib,sum_const,smul_eq_mul,mul_one] at h
    exact h
  constructor
  · rw [isMultiplicative_sigma.map_mul_of_coprime co,mul_val sa.pos.ne' (sigma_pos _ _ zn).ne',
      show v₂ (σ 1 (2^a))=0 from OMA.WeightVal245212.val_odd sa,zero_add,sm,
      vp _ (fun i => (sigma_pos 1 _ (pow_ne_zero _ (hp i).ne_zero)).ne'),←sum_add_distrib]
    exact sum_congr rfl (fun i _ => local_sigma (hp i) (op i) (e i))
  · have z2 : 2^a≠0 := by positivity
    have nz := mul_ne_zero z2 zn
    rw [mul_val (mul_ne_zero (by decide) nz) (sigma_pos 0 _ nz).ne',
      mul_val (by decide) nz,mul_val z2 zn,isMultiplicative_sigma.map_mul_of_coprime co,
      sigma_zero_apply_prime_pow Nat.prime_two,tm,mul_val (by omega) (prod_ne_zero_iff.mpr (fun _ _ => by omega)),
      vp _ (fun _ => by omega),show v₂ (total p e)=0 from OMA.WeightVal245212.val_odd
        (Nat.coprime_two_left.mp oc),show v₂ (2^a)=a from Nat.factorization_pow_self Nat.prime_two]
    have : v₂ 2=1 := by decide +kernel
    omega

/-- Compare the ordinary-divisor surplus U and the dyadic threshold H.
The weighted surplus equals their minimum unless they coincide, when it is larger. -/
theorem trichotomy {ι : Type*} [Fintype ι] (p e : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (op : ∀ i, Odd (p i)) (inj : Function.Injective p)
    (a : ℕ) (eq : OeisA245212.a (2^a*total p e) = (σ 1 (2^a*total p e) : ℤ)) :
    let E := ∑ i, v₂ (e i+2)
    let U := ∑ i, surplus (p i) (e i)
    let H := 1+a+v₂ (a+1)
    (U<H → E=Fintype.card ι+U) ∧ (H<U → E=Fintype.card ι+H) ∧
      (U=H → Fintype.card ι+H<E) := by
  let n := 2^a*total p e
  have nz : n≠0 := mul_ne_zero (by positivity) (prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hp i).ne_zero))
  have h := balance nz eq
  have ws : W n≠0 := by
    rw [w_apply]
    exact (sum_pos' (fun _ _ => Nat.zero_le _) ⟨1,one_mem_divisors.mpr nz,by simp⟩).ne'
  have ss := (sigma_pos 1 n nz).ne'
  have x := orders p e hp op inj a
  change v₂ (W n)+Fintype.card ι=_ ∧ v₂ (σ 1 n)=_ ∧ v₂ (2*n*(σ 0 n))=_ at x
  rw [←h] at x
  obtain ⟨w,s,b⟩ := x
  dsimp only
  rcases lt_trichotomy (v₂ (W n)) (v₂ (σ 1 n)) with lo|same|hi
  · have ord := sum_of_lt ws ss lo
    omega
  · have ord := sum_of_equal ws ss same
    omega
  · have ord := sum_of_lt ss ws hi
    rw [add_comm] at ord
    omega

end OMA.BalanceOrders245212

end

section

/- For the 4·3^7 cofactor, the exact dyadic balance excludes every
complementary divisor count below 30; the first free prime is at most 964. -/
namespace OMA.RankThreeFourSmallOrder245212
open Nat Finset ArithmeticFunction OMA.Smooth245212 OMA.ExactSigma245212
open OMA.RankThreeFourSmallHarmonic245212
open scoped ArithmeticFunction.sigma

open OMA.CofactorEulerPair245212
open OMA.CofactorEulerPair245212 (checked)

private theorem check : every 1 29 (fun b=>every 1 29 (fun d=>decide (
    (b+1)*(d+1)<15 ∨ 30≤(b+1)*(d+1) ∨ OMA.WeightVal245212.val (b+2)+OMA.WeightVal245212.val (d+2)<4 ∨
    b%2=0 ∧ d%2=0 ∧ OMA.WeightVal245212.val (b+2)+OMA.WeightVal245212.val (d+2)≠4)))=true := by decide +kernel

theorem first {p q b d : ℕ} (hp : p.Prime) (hq : q.Prime) (lo : 5≤p) (pq : p<q)
    (bp : 0<b) (dp : 0<d)
    (eqn : OeisA245212.a (4*3^7*p^b*q^d)=(σ 1 (4*3^7*p^b*q^d):ℤ)) : p≤964 := by
  let ps : Fin 3→ℕ:=![3,p,q]
  let es : Fin 3→ℕ:=![7,b,d]
  have pr : ∀ i,(ps i).Prime := by intro i;fin_cases i <;> first | exact hp | exact hq | exact (by decide : Nat.Prime 3)
  have odd : ∀ i,Odd (ps i) := by intro i;fin_cases i <;> first | exact hp.odd_of_ne_two (by omega) | exact hq.odd_of_ne_two (by omega) | exact (by decide : Odd 3)
  have inj : Function.Injective ps := by
    intro i j h;fin_cases i <;> fin_cases j <;> simp [ps] at * <;> omega
  have te : total ps es=3^7*p^b*q^d := by simp [total,ps,es,Fin.prod_univ_succ,mul_assoc]
  have eq : OeisA245212.a (2^2*total ps es)=(σ 1 (2^2*total ps es):ℤ) := by
    simpa only [te,show 2^2=4 by decide,←mul_assoc] using eqn
  have tri:=OMA.BalanceOrders245212.trichotomy ps es pr odd inj 2 eq
  let E:=OMA.WeightVal245212.val (b+2)+OMA.WeightVal245212.val (d+2)
  let U:=1+surplus p b+surplus q d
  have tri' : (U<3 → E=3+U) ∧ (3<U → E=6) ∧ (U=3 → 6<E) := by
    simpa [ps,es,E,U,Fin.sum_univ_succ,add_assoc,show OMA.WeightVal245212.val (7+2)=0 by decide +kernel,
      show OMA.WeightVal245212.val (2+1)=0 by decide +kernel,show surplus 3 7=1 by decide +kernel] using tri
  have E4 : 4≤E := by
    have pos : 0<U := by dsimp [U];omega
    rcases lt_trichotomy U 3 with lt|e|gt
    · have := tri'.1 lt;omega
    · have := tri'.2.2 e;omega
    · have := tri'.2.1 gt;omega
  have both (be : Even b) (de : Even d) : E=4 := by
    have nb : ¬Odd b := by rintro ⟨i,hi⟩;obtain ⟨j,hj⟩:=be;omega
    have nd : ¬Odd d := by rintro ⟨i,hi⟩;obtain ⟨j,hj⟩:=de;omega
    have u1 : U=1 := by simp [U,surplus,nb,nd]
    exact (tri'.1 (by omega)).trans (by omega)
  have hh : 0<8748 := by decide
  have cop (r : ℕ) (hr : r.Prime) (r5 : 5≤r) : (8748:ℕ).Coprime r := by
    change (2^2*3^7).Coprime r
    exact (((coprime_primes prime_two hr).mpr (by omega)).pow_left 2).mul_left
      (((coprime_primes (by decide : Nat.Prime 3) hr).mpr (by omega)).pow_left 7)
  obtain ⟨slope,cap⟩ := count_cap hh hp hq (cop p hp lo) (cop q hq (by omega)) pq bp dp eqn
  let L:=(b+1)*(d+1)
  have constants : W 8748=418268 ∧ σ 1 8748=22960 ∧ 2*(8748*σ 0 8748)=419904 := by decide +kernel
  rw [constants.1,constants.2.1,constants.2.2] at slope cap
  change 22960<1636*L at slope
  change p*(1636*L-22960)≤2*419904*L at cap
  have lt : 30≤L := by
    by_contra! small
    have bL : b<L := by dsimp [L]; nlinarith
    have dL : d<L := by dsimp [L]; nlinarith
    have re:=of_decide_eq_true (OMA.CofactorEulerPair245212.checked (OMA.CofactorEulerPair245212.checked check bp (by omega)) dp (by omega))
    change L<15 ∨ 30≤L ∨ E<4 ∨ b%2=0 ∧ d%2=0 ∧ E≠4 at re
    rcases re with r|r|r|⟨eb,ed,off⟩ <;> try omega
    exact off (both (Nat.even_iff.mpr eb) (Nat.even_iff.mpr ed))
  by_contra! big
  have rest:=Nat.sub_add_cancel slope.le
  have mult:=Nat.mul_le_mul_right (1636*L-22960) (show 965≤p by omega)
  nlinarith only [cap,mult,rest,lt]


/-- The complementary divisor count is a product of two integers ≥2 and
cannot be five, improving the harmonic first-prime bound on this cofactor. -/
theorem first_six {p q b d : ℕ} (hp : p.Prime) (hq : q.Prime) (lo : 5≤p) (pq : p<q)
    (bp : 0<b) (dp : 0<d)
    (eqn : OeisA245212.a (4*3^6*p^b*q^d)=(σ 1 (4*3^6*p^b*q^d):ℤ)) : p≤678 := by
  have cop (r : ℕ) (hr : r.Prime) (r5 : 5≤r) : (2916:ℕ).Coprime r := by
    change (2^2*3^6).Coprime r
    exact (((coprime_primes prime_two hr).mpr (by omega)).pow_left 2).mul_left
      (((coprime_primes (by decide : Nat.Prime 3) hr).mpr (by omega)).pow_left 6)
  obtain ⟨slope,cap⟩ := count_cap (by decide : 0<2916) hp hq (cop p hp lo) (cop q hq (by omega)) pq bp dp eqn
  let L:=(b+1)*(d+1)
  have constants : W 2916=120836 ∧ σ 1 2916=7651 ∧ 2*(2916*σ 0 2916)=122472 := by decide +kernel
  rw [constants.1,constants.2.1,constants.2.2] at slope cap
  change 7651<1636*L at slope
  change p*(1636*L-7651)≤2*122472*L at cap
  have lt : 6≤L := by
    by_contra! small
    by_cases be : b=1
    · dsimp [L] at *;subst b;omega
    · have := Nat.mul_le_mul (show 3≤b+1 by omega) (show 2≤d+1 by omega)
      omega
  by_contra! big
  have rest:=Nat.sub_add_cancel slope.le
  have mult:=Nat.mul_le_mul_right (1636*L-7651) (show 679≤p by omega)
  nlinarith only [cap,mult,rest,lt]

end OMA.RankThreeFourSmallOrder245212

end

section

section
/- Certified prime and exponent intervals for one power of three. -/
namespace OMA.RankThreeFourSmallTables245212
open OMA.CofactorEulerPair245212 OMA.RankThreeFourSmallDecision245212
open OMA.RankThreeFourSmallOriginal245212
open OMA.RankThreeMiddle245212 (joinEvery)
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
private theorem c1_0 : every 1 11 (movingRow 119 28 72 5)=true := by decide +kernel
private theorem c1_1 : every 12 12 (movingRow 119 28 72 5)=true := by decide +kernel
private theorem p1_5 : every 5 5 (atPrime 12 119 28 72)=true := by
  have localTest : atPrime 12 119 28 72 5=true := (joinEvery c1_0 c1_1)
  apply List.all_eq_true.mpr; intro j hj; obtain ⟨lo,hi⟩:=List.mem_range'_1.mp hj
  simpa only [show j=5 by omega] using localTest
private theorem c1_2 : every 6 6 (atPrime 12 119 28 72)=true := by decide +kernel
private theorem c1_3 : every 8 30 (fixedPair 12 119 28 72 7)=true := by decide +kernel
private theorem c1_4 : every 31 54 (fixedPair 12 119 28 72 7)=true := by decide +kernel
private theorem c1_5 : every 1 21 (moving 55 4 119 28 72 7)=true := by decide +kernel
private theorem p1_7 : every 7 7 (atPrime 12 119 28 72)=true := by
  have localTest : atPrime 12 119 28 72 7=true := by change (every 8 54 (fixedPair 12 119 28 72 7) && every 1 21 (moving 55 4 119 28 72 7)) = true; rw [Bool.and_eq_true]; exact ⟨(joinEvery c1_3 c1_4),c1_5⟩
  apply List.all_eq_true.mpr; intro j hj; obtain ⟨lo,hi⟩:=List.mem_range'_1.mp hj
  simpa only [show j=7 by omega] using localTest
private theorem c1_6 : every 8 10 (atPrime 12 119 28 72)=true := by decide +kernel
private theorem c1_7 : every 12 20 (fixedPair 12 119 28 72 11)=true := by decide +kernel
private theorem c1_8 : every 1 8 (moving 21 6 119 28 72 11)=true := by decide +kernel
private theorem p1_11 : every 11 11 (atPrime 12 119 28 72)=true := by
  have localTest : atPrime 12 119 28 72 11=true := by change (every 12 20 (fixedPair 12 119 28 72 11) && every 1 8 (moving 21 6 119 28 72 11)) = true; rw [Bool.and_eq_true]; exact ⟨c1_7,c1_8⟩
  apply List.all_eq_true.mpr; intro j hj; obtain ⟨lo,hi⟩:=List.mem_range'_1.mp hj
  simpa only [show j=11 by omega] using localTest
private theorem c1_9 : every 12 12 (atPrime 12 119 28 72)=true := by decide +kernel
private theorem c1_10 : every 14 18 (fixedPair 12 119 28 72 13)=true := by decide +kernel
private theorem c1_11 : every 1 7 (moving 19 7 119 28 72 13)=true := by decide +kernel
private theorem p1_13 : every 13 13 (atPrime 12 119 28 72)=true := by
  have localTest : atPrime 12 119 28 72 13=true := by change (every 14 18 (fixedPair 12 119 28 72 13) && every 1 7 (moving 19 7 119 28 72 13)) = true; rw [Bool.and_eq_true]; exact ⟨c1_10,c1_11⟩
  apply List.all_eq_true.mpr; intro j hj; obtain ⟨lo,hi⟩:=List.mem_range'_1.mp hj
  simpa only [show j=13 by omega] using localTest
private theorem c1_12 : every 14 16 (atPrime 12 119 28 72)=true := by decide +kernel
theorem at1 : cert 1=true := (joinEvery (joinEvery (joinEvery p1_5 c1_2) (joinEvery p1_7 c1_6)) (joinEvery (joinEvery p1_11 c1_9) (joinEvery p1_13 c1_12)))
end OMA.RankThreeFourSmallTables245212

end

section
/- Certified prime and exponent intervals for one power of three. -/
namespace OMA.RankThreeFourSmallTables245212
open OMA.CofactorEulerPair245212 OMA.RankThreeFourSmallDecision245212
open OMA.RankThreeFourSmallOriginal245212
open OMA.RankThreeMiddle245212 (joinEvery)
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
private theorem c2_0 : every 1 3 (movingRow 578 91 324 5)=true := by decide +kernel
private theorem p2_5 : every 5 5 (atPrime 36 578 91 324)=true := by
  have localTest : atPrime 36 578 91 324 5=true := c2_0
  apply List.all_eq_true.mpr; intro j hj; obtain ⟨lo,hi⟩:=List.mem_range'_1.mp hj
  simpa only [show j=5 by omega] using localTest
private theorem c2_1 : every 6 6 (atPrime 36 578 91 324)=true := by decide +kernel
private theorem c2_2 : every 1 7 (movingRow 578 91 324 7)=true := by decide +kernel
private theorem p2_7 : every 7 7 (atPrime 36 578 91 324)=true := by
  have localTest : atPrime 36 578 91 324 7=true := c2_2
  apply List.all_eq_true.mpr; intro j hj; obtain ⟨lo,hi⟩:=List.mem_range'_1.mp hj
  simpa only [show j=7 by omega] using localTest
private theorem c2_3 : every 8 10 (atPrime 36 578 91 324)=true := by decide +kernel
private theorem c2_4 : every 12 36 (fixedPair 36 578 91 324 11)=true := by decide +kernel
private theorem c2_5 : every 37 60 (fixedPair 36 578 91 324 11)=true := by decide +kernel
private theorem c2_6 : every 61 88 (fixedPair 36 578 91 324 11)=true := by decide +kernel
private theorem c2_7 : every 89 105 (fixedPair 36 578 91 324 11)=true := by decide +kernel
private theorem c2_8 : every 1 29 (moving 106 5 578 91 324 11)=true := by decide +kernel
private theorem p2_11 : every 11 11 (atPrime 36 578 91 324)=true := by
  have localTest : atPrime 36 578 91 324 11=true := by change (every 12 105 (fixedPair 36 578 91 324 11) && every 1 29 (moving 106 5 578 91 324 11)) = true; rw [Bool.and_eq_true]; exact ⟨(joinEvery (joinEvery c2_4 c2_5) (joinEvery c2_6 c2_7)),c2_8⟩
  apply List.all_eq_true.mpr; intro j hj; obtain ⟨lo,hi⟩:=List.mem_range'_1.mp hj
  simpa only [show j=11 by omega] using localTest
private theorem c2_9 : every 12 12 (atPrime 36 578 91 324)=true := by decide +kernel
private theorem c2_10 : every 14 40 (fixedPair 36 578 91 324 13)=true := by decide +kernel
private theorem c2_11 : every 41 58 (fixedPair 36 578 91 324 13)=true := by decide +kernel
private theorem c2_12 : every 1 16 (moving 59 5 578 91 324 13)=true := by decide +kernel
private theorem p2_13 : every 13 13 (atPrime 36 578 91 324)=true := by
  have localTest : atPrime 36 578 91 324 13=true := by change (every 14 58 (fixedPair 36 578 91 324 13) && every 1 16 (moving 59 5 578 91 324 13)) = true; rw [Bool.and_eq_true]; exact ⟨(joinEvery c2_10 c2_11),c2_12⟩
  apply List.all_eq_true.mpr; intro j hj; obtain ⟨lo,hi⟩:=List.mem_range'_1.mp hj
  simpa only [show j=13 by omega] using localTest
private theorem c2_13 : every 14 16 (atPrime 36 578 91 324)=true := by decide +kernel
private theorem c2_14 : every 18 37 (fixedPair 36 578 91 324 17)=true := by decide +kernel
private theorem c2_15 : every 1 10 (moving 38 7 578 91 324 17)=true := by decide +kernel
private theorem p2_17 : every 17 17 (atPrime 36 578 91 324)=true := by
  have localTest : atPrime 36 578 91 324 17=true := by change (every 18 37 (fixedPair 36 578 91 324 17) && every 1 10 (moving 38 7 578 91 324 17)) = true; rw [Bool.and_eq_true]; exact ⟨c2_14,c2_15⟩
  apply List.all_eq_true.mpr; intro j hj; obtain ⟨lo,hi⟩:=List.mem_range'_1.mp hj
  simpa only [show j=17 by omega] using localTest
private theorem c2_16 : every 18 18 (atPrime 36 578 91 324)=true := by decide +kernel
private theorem c2_17 : every 20 33 (fixedPair 36 578 91 324 19)=true := by decide +kernel
private theorem c2_18 : every 1 9 (moving 34 7 578 91 324 19)=true := by decide +kernel
private theorem p2_19 : every 19 19 (atPrime 36 578 91 324)=true := by
  have localTest : atPrime 36 578 91 324 19=true := by change (every 20 33 (fixedPair 36 578 91 324 19) && every 1 9 (moving 34 7 578 91 324 19)) = true; rw [Bool.and_eq_true]; exact ⟨c2_17,c2_18⟩
  apply List.all_eq_true.mpr; intro j hj; obtain ⟨lo,hi⟩:=List.mem_range'_1.mp hj
  simpa only [show j=19 by omega] using localTest
private theorem c2_19 : every 20 22 (atPrime 36 578 91 324)=true := by decide +kernel
private theorem c2_20 : every 24 28 (fixedPair 36 578 91 324 23)=true := by decide +kernel
private theorem c2_21 : every 1 8 (moving 29 8 578 91 324 23)=true := by decide +kernel
private theorem p2_23 : every 23 23 (atPrime 36 578 91 324)=true := by
  have localTest : atPrime 36 578 91 324 23=true := by change (every 24 28 (fixedPair 36 578 91 324 23) && every 1 8 (moving 29 8 578 91 324 23)) = true; rw [Bool.and_eq_true]; exact ⟨c2_20,c2_21⟩
  apply List.all_eq_true.mpr; intro j hj; obtain ⟨lo,hi⟩:=List.mem_range'_1.mp hj
  simpa only [show j=23 by omega] using localTest
private theorem c2_22 : every 24 27 (atPrime 36 578 91 324)=true := by decide +kernel
theorem at2 : cert 2=true := (joinEvery (joinEvery (joinEvery p2_5 (joinEvery c2_1 p2_7)) (joinEvery (joinEvery c2_3 p2_11) (joinEvery c2_9 p2_13))) (joinEvery (joinEvery c2_13 (joinEvery p2_17 c2_16)) (joinEvery (joinEvery p2_19 c2_19) (joinEvery p2_23 c2_22))))
end OMA.RankThreeFourSmallTables245212

end

section
/- Certified prime and exponent intervals for one power of three. -/
namespace OMA.RankThreeFourSmallTables245212
open OMA.CofactorEulerPair245212 OMA.RankThreeFourSmallDecision245212
open OMA.RankThreeFourSmallOriginal245212
open OMA.RankThreeMiddle245212 (joinEvery)
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
private theorem c3_0 : every 1 2 (movingRow 2414 280 1296 5)=true := by decide +kernel
private theorem p3_5 : every 5 5 (atPrime 108 2414 280 1296)=true := by
  have localTest : atPrime 108 2414 280 1296 5=true := c3_0
  apply List.all_eq_true.mpr; intro j hj; obtain ⟨lo,hi⟩:=List.mem_range'_1.mp hj
  simpa only [show j=5 by omega] using localTest
private theorem c3_1 : every 6 6 (atPrime 108 2414 280 1296)=true := by decide +kernel
private theorem c3_2 : every 1 3 (movingRow 2414 280 1296 7)=true := by decide +kernel
private theorem p3_7 : every 7 7 (atPrime 108 2414 280 1296)=true := by
  have localTest : atPrime 108 2414 280 1296 7=true := c3_2
  apply List.all_eq_true.mpr; intro j hj; obtain ⟨lo,hi⟩:=List.mem_range'_1.mp hj
  simpa only [show j=7 by omega] using localTest
private theorem c3_3 : every 8 10 (atPrime 108 2414 280 1296)=true := by decide +kernel
private theorem c3_4 : every 1 7 (movingRow 2414 280 1296 11)=true := by decide +kernel
private theorem p3_11 : every 11 11 (atPrime 108 2414 280 1296)=true := by
  have localTest : atPrime 108 2414 280 1296 11=true := c3_4
  apply List.all_eq_true.mpr; intro j hj; obtain ⟨lo,hi⟩:=List.mem_range'_1.mp hj
  simpa only [show j=11 by omega] using localTest
private theorem c3_5 : every 12 12 (atPrime 108 2414 280 1296)=true := by decide +kernel
private theorem c3_6 : every 1 11 (movingRow 2414 280 1296 13)=true := by decide +kernel
private theorem c3_7 : every 12 16 (movingRow 2414 280 1296 13)=true := by decide +kernel
private theorem c3_8 : every 17 17 (movingRow 2414 280 1296 13)=true := by decide +kernel
private theorem p3_13 : every 13 13 (atPrime 108 2414 280 1296)=true := by
  have localTest : atPrime 108 2414 280 1296 13=true := (joinEvery c3_6 (joinEvery c3_7 c3_8))
  apply List.all_eq_true.mpr; intro j hj; obtain ⟨lo,hi⟩:=List.mem_range'_1.mp hj
  simpa only [show j=13 by omega] using localTest
private theorem c3_9 : every 14 16 (atPrime 108 2414 280 1296)=true := by decide +kernel
private theorem c3_10 : every 18 42 (fixedPair 108 2414 280 1296 17)=true := by decide +kernel
private theorem c3_11 : every 43 70 (fixedPair 108 2414 280 1296 17)=true := by decide +kernel
private theorem c3_12 : every 71 100 (fixedPair 108 2414 280 1296 17)=true := by decide +kernel
private theorem c3_13 : every 101 130 (fixedPair 108 2414 280 1296 17)=true := by decide +kernel
private theorem c3_14 : every 131 160 (fixedPair 108 2414 280 1296 17)=true := by decide +kernel
private theorem c3_15 : every 161 190 (fixedPair 108 2414 280 1296 17)=true := by decide +kernel
private theorem c3_16 : every 1 40 (moving 191 5 2414 280 1296 17)=true := by decide +kernel
private theorem c3_17 : every 41 41 (moving 191 5 2414 280 1296 17)=true := by decide +kernel
private theorem p3_17 : every 17 17 (atPrime 108 2414 280 1296)=true := by
  have localTest : atPrime 108 2414 280 1296 17=true := by change (every 18 190 (fixedPair 108 2414 280 1296 17) && every 1 41 (moving 191 5 2414 280 1296 17)) = true; rw [Bool.and_eq_true]; exact ⟨(joinEvery (joinEvery c3_10 (joinEvery c3_11 c3_12)) (joinEvery c3_13 (joinEvery c3_14 c3_15))),(joinEvery c3_16 c3_17)⟩
  apply List.all_eq_true.mpr; intro j hj; obtain ⟨lo,hi⟩:=List.mem_range'_1.mp hj
  simpa only [show j=17 by omega] using localTest
private theorem c3_18 : every 18 18 (atPrime 108 2414 280 1296)=true := by decide +kernel
private theorem c3_19 : every 20 46 (fixedPair 108 2414 280 1296 19)=true := by decide +kernel
private theorem c3_20 : every 47 72 (fixedPair 108 2414 280 1296 19)=true := by decide +kernel
private theorem c3_21 : every 73 102 (fixedPair 108 2414 280 1296 19)=true := by decide +kernel
private theorem c3_22 : every 103 117 (fixedPair 108 2414 280 1296 19)=true := by decide +kernel
private theorem c3_23 : every 1 25 (moving 118 6 2414 280 1296 19)=true := by decide +kernel
private theorem p3_19 : every 19 19 (atPrime 108 2414 280 1296)=true := by
  have localTest : atPrime 108 2414 280 1296 19=true := by change (every 20 117 (fixedPair 108 2414 280 1296 19) && every 1 25 (moving 118 6 2414 280 1296 19)) = true; rw [Bool.and_eq_true]; exact ⟨(joinEvery (joinEvery c3_19 c3_20) (joinEvery c3_21 c3_22)),c3_23⟩
  apply List.all_eq_true.mpr; intro j hj; obtain ⟨lo,hi⟩:=List.mem_range'_1.mp hj
  simpa only [show j=19 by omega] using localTest
private theorem c3_24 : every 20 22 (atPrime 108 2414 280 1296)=true := by decide +kernel
private theorem c3_25 : every 24 52 (fixedPair 108 2414 280 1296 23)=true := by decide +kernel
private theorem c3_26 : every 53 74 (fixedPair 108 2414 280 1296 23)=true := by decide +kernel
private theorem c3_27 : every 1 16 (moving 75 7 2414 280 1296 23)=true := by decide +kernel
private theorem p3_23 : every 23 23 (atPrime 108 2414 280 1296)=true := by
  have localTest : atPrime 108 2414 280 1296 23=true := by change (every 24 74 (fixedPair 108 2414 280 1296 23) && every 1 16 (moving 75 7 2414 280 1296 23)) = true; rw [Bool.and_eq_true]; exact ⟨(joinEvery c3_25 c3_26),c3_27⟩
  apply List.all_eq_true.mpr; intro j hj; obtain ⟨lo,hi⟩:=List.mem_range'_1.mp hj
  simpa only [show j=23 by omega] using localTest
private theorem c3_28 : every 24 28 (atPrime 108 2414 280 1296)=true := by decide +kernel
private theorem c3_29 : every 30 55 (fixedPair 108 2414 280 1296 29)=true := by decide +kernel
private theorem c3_30 : every 1 12 (moving 56 8 2414 280 1296 29)=true := by decide +kernel
private theorem p3_29 : every 29 29 (atPrime 108 2414 280 1296)=true := by
  have localTest : atPrime 108 2414 280 1296 29=true := by change (every 30 55 (fixedPair 108 2414 280 1296 29) && every 1 12 (moving 56 8 2414 280 1296 29)) = true; rw [Bool.and_eq_true]; exact ⟨c3_29,c3_30⟩
  apply List.all_eq_true.mpr; intro j hj; obtain ⟨lo,hi⟩:=List.mem_range'_1.mp hj
  simpa only [show j=29 by omega] using localTest
private theorem c3_31 : every 30 30 (atPrime 108 2414 280 1296)=true := by decide +kernel
private theorem c3_32 : every 32 52 (fixedPair 108 2414 280 1296 31)=true := by decide +kernel
private theorem c3_33 : every 1 11 (moving 53 8 2414 280 1296 31)=true := by decide +kernel
private theorem p3_31 : every 31 31 (atPrime 108 2414 280 1296)=true := by
  have localTest : atPrime 108 2414 280 1296 31=true := by change (every 32 52 (fixedPair 108 2414 280 1296 31) && every 1 11 (moving 53 8 2414 280 1296 31)) = true; rw [Bool.and_eq_true]; exact ⟨c3_32,c3_33⟩
  apply List.all_eq_true.mpr; intro j hj; obtain ⟨lo,hi⟩:=List.mem_range'_1.mp hj
  simpa only [show j=31 by omega] using localTest
private theorem c3_34 : every 32 36 (atPrime 108 2414 280 1296)=true := by decide +kernel
private theorem c3_35 : every 38 45 (fixedPair 108 2414 280 1296 37)=true := by decide +kernel
private theorem c3_36 : every 1 10 (moving 46 10 2414 280 1296 37)=true := by decide +kernel
private theorem p3_37 : every 37 37 (atPrime 108 2414 280 1296)=true := by
  have localTest : atPrime 108 2414 280 1296 37=true := by change (every 38 45 (fixedPair 108 2414 280 1296 37) && every 1 10 (moving 46 10 2414 280 1296 37)) = true; rw [Bool.and_eq_true]; exact ⟨c3_35,c3_36⟩
  apply List.all_eq_true.mpr; intro j hj; obtain ⟨lo,hi⟩:=List.mem_range'_1.mp hj
  simpa only [show j=37 by omega] using localTest
private theorem c3_37 : every 38 40 (atPrime 108 2414 280 1296)=true := by decide +kernel
private theorem c3_38 : every 42 43 (fixedPair 108 2414 280 1296 41)=true := by decide +kernel
private theorem c3_39 : every 1 9 (moving 44 11 2414 280 1296 41)=true := by decide +kernel
private theorem p3_41 : every 41 41 (atPrime 108 2414 280 1296)=true := by
  have localTest : atPrime 108 2414 280 1296 41=true := by change (every 42 43 (fixedPair 108 2414 280 1296 41) && every 1 9 (moving 44 11 2414 280 1296 41)) = true; rw [Bool.and_eq_true]; exact ⟨c3_38,c3_39⟩
  apply List.all_eq_true.mpr; intro j hj; obtain ⟨lo,hi⟩:=List.mem_range'_1.mp hj
  simpa only [show j=41 by omega] using localTest
private theorem c3_40 : every 42 42 (atPrime 108 2414 280 1296)=true := by decide +kernel
private theorem c3_41 : every 44 42 (fixedPair 108 2414 280 1296 43)=true := by decide +kernel
private theorem c3_42 : every 1 9 (moving 44 11 2414 280 1296 43)=true := by decide +kernel
private theorem p3_43 : every 43 43 (atPrime 108 2414 280 1296)=true := by
  have localTest : atPrime 108 2414 280 1296 43=true := by change (every 44 42 (fixedPair 108 2414 280 1296 43) && every 1 9 (moving 44 11 2414 280 1296 43)) = true; rw [Bool.and_eq_true]; exact ⟨c3_41,c3_42⟩
  apply List.all_eq_true.mpr; intro j hj; obtain ⟨lo,hi⟩:=List.mem_range'_1.mp hj
  simpa only [show j=43 by omega] using localTest
private theorem c3_43 : every 44 46 (atPrime 108 2414 280 1296)=true := by decide +kernel
private theorem c3_44 : every 48 40 (fixedPair 108 2414 280 1296 47)=true := by decide +kernel
private theorem c3_45 : every 1 8 (moving 48 12 2414 280 1296 47)=true := by decide +kernel
private theorem p3_47 : every 47 47 (atPrime 108 2414 280 1296)=true := by
  have localTest : atPrime 108 2414 280 1296 47=true := by change (every 48 40 (fixedPair 108 2414 280 1296 47) && every 1 8 (moving 48 12 2414 280 1296 47)) = true; rw [Bool.and_eq_true]; exact ⟨c3_44,c3_45⟩
  apply List.all_eq_true.mpr; intro j hj; obtain ⟨lo,hi⟩:=List.mem_range'_1.mp hj
  simpa only [show j=47 by omega] using localTest
private theorem c3_46 : every 48 48 (atPrime 108 2414 280 1296)=true := by decide +kernel
theorem at3 : cert 3=true := (joinEvery (joinEvery (joinEvery (joinEvery p3_5 (joinEvery c3_1 p3_7)) (joinEvery c3_3 (joinEvery p3_11 c3_5))) (joinEvery (joinEvery p3_13 (joinEvery c3_9 p3_17)) (joinEvery (joinEvery c3_18 p3_19) (joinEvery c3_24 p3_23)))) (joinEvery (joinEvery (joinEvery c3_28 (joinEvery p3_29 c3_31)) (joinEvery p3_31 (joinEvery c3_34 p3_37))) (joinEvery (joinEvery c3_37 (joinEvery p3_41 c3_40)) (joinEvery (joinEvery p3_43 c3_43) (joinEvery p3_47 c3_46)))))
end OMA.RankThreeFourSmallTables245212

end

section
/- Certified prime and exponent intervals for one power of three. -/
namespace OMA.RankThreeFourSmallTables245212
open OMA.CofactorEulerPair245212 OMA.RankThreeFourSmallDecision245212
open OMA.RankThreeFourSmallOriginal245212
open OMA.RankThreeMiddle245212 (joinEvery)
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
private theorem c4_0 : every 1 2 (movingRow 9299 847 4860 5)=true := by decide +kernel
private theorem p4_5 : every 5 5 (atPrime 324 9299 847 4860)=true := by
  have localTest : atPrime 324 9299 847 4860 5=true := c4_0
  apply List.all_eq_true.mpr; intro j hj; obtain ⟨lo,hi⟩:=List.mem_range'_1.mp hj
  simpa only [show j=5 by omega] using localTest
private theorem c4_1 : every 6 6 (atPrime 324 9299 847 4860)=true := by decide +kernel
private theorem c4_2 : every 1 2 (movingRow 9299 847 4860 7)=true := by decide +kernel
private theorem p4_7 : every 7 7 (atPrime 324 9299 847 4860)=true := by
  have localTest : atPrime 324 9299 847 4860 7=true := c4_2
  apply List.all_eq_true.mpr; intro j hj; obtain ⟨lo,hi⟩:=List.mem_range'_1.mp hj
  simpa only [show j=7 by omega] using localTest
private theorem c4_3 : every 8 10 (atPrime 324 9299 847 4860)=true := by decide +kernel
private theorem c4_4 : every 1 3 (movingRow 9299 847 4860 11)=true := by decide +kernel
private theorem p4_11 : every 11 11 (atPrime 324 9299 847 4860)=true := by
  have localTest : atPrime 324 9299 847 4860 11=true := c4_4
  apply List.all_eq_true.mpr; intro j hj; obtain ⟨lo,hi⟩:=List.mem_range'_1.mp hj
  simpa only [show j=11 by omega] using localTest
private theorem c4_5 : every 12 12 (atPrime 324 9299 847 4860)=true := by decide +kernel
private theorem c4_6 : every 1 4 (movingRow 9299 847 4860 13)=true := by decide +kernel
private theorem p4_13 : every 13 13 (atPrime 324 9299 847 4860)=true := by
  have localTest : atPrime 324 9299 847 4860 13=true := c4_6
  apply List.all_eq_true.mpr; intro j hj; obtain ⟨lo,hi⟩:=List.mem_range'_1.mp hj
  simpa only [show j=13 by omega] using localTest
private theorem c4_7 : every 14 16 (atPrime 324 9299 847 4860)=true := by decide +kernel
private theorem c4_8 : every 1 7 (movingRow 9299 847 4860 17)=true := by decide +kernel
private theorem p4_17 : every 17 17 (atPrime 324 9299 847 4860)=true := by
  have localTest : atPrime 324 9299 847 4860 17=true := c4_8
  apply List.all_eq_true.mpr; intro j hj; obtain ⟨lo,hi⟩:=List.mem_range'_1.mp hj
  simpa only [show j=17 by omega] using localTest
private theorem c4_9 : every 18 18 (atPrime 324 9299 847 4860)=true := by decide +kernel
private theorem c4_10 : every 1 10 (movingRow 9299 847 4860 19)=true := by decide +kernel
private theorem p4_19 : every 19 19 (atPrime 324 9299 847 4860)=true := by
  have localTest : atPrime 324 9299 847 4860 19=true := c4_10
  apply List.all_eq_true.mpr; intro j hj; obtain ⟨lo,hi⟩:=List.mem_range'_1.mp hj
  simpa only [show j=19 by omega] using localTest
private theorem c4_11 : every 20 22 (atPrime 324 9299 847 4860)=true := by decide +kernel
private theorem c4_12 : every 1 11 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_13 : every 12 16 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_14 : every 17 20 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_15 : every 21 23 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_16 : every 24 26 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_17 : every 27 28 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_18 : every 29 30 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_19 : every 31 32 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_20 : every 33 34 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_21 : every 35 36 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_22 : every 37 38 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_23 : every 39 39 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_24 : every 40 40 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_25 : every 41 41 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_26 : every 42 42 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_27 : every 43 43 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_28 : every 44 44 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_29 : every 45 45 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_30 : every 46 46 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_31 : every 47 47 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_32 : every 48 48 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_33 : every 49 49 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_34 : every 50 50 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_35 : every 51 51 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_36 : every 52 52 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_37 : every 53 53 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_38 : every 54 54 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_39 : every 55 55 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_40 : every 56 56 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_41 : every 57 57 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_42 : every 58 58 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_43 : every 59 59 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_44 : every 60 60 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_45 : every 61 61 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_46 : every 62 62 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_47 : every 63 63 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_48 : every 64 64 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_49 : every 65 65 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_50 : every 66 66 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_51 : every 67 67 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_52 : every 68 68 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_53 : every 69 69 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_54 : every 70 70 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_55 : every 71 71 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_56 : every 72 72 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_57 : every 73 73 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_58 : every 74 74 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_59 : every 75 75 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_60 : every 76 76 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_61 : every 77 77 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_62 : every 78 78 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_63 : every 79 79 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_64 : every 80 80 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_65 : every 81 81 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_66 : every 82 82 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_67 : every 83 83 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_68 : every 84 84 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_69 : every 85 85 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_70 : every 86 86 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_71 : every 87 87 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_72 : every 88 88 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_73 : every 89 89 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_74 : every 90 90 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_75 : every 91 91 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_76 : every 92 92 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_77 : every 93 93 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_78 : every 94 94 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_79 : every 95 95 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_80 : every 96 96 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_81 : every 97 97 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_82 : every 98 98 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_83 : every 99 99 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_84 : every 100 100 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_85 : every 101 101 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_86 : every 102 102 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_87 : every 103 103 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_88 : every 104 104 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_89 : every 105 105 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_90 : every 106 106 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_91 : every 107 107 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_92 : every 108 108 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_93 : every 109 109 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_94 : every 110 110 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_95 : every 111 111 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_96 : every 112 112 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_97 : every 113 113 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_98 : every 114 114 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_99 : every 115 115 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_100 : every 116 116 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_101 : every 117 117 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_102 : every 118 118 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_103 : every 119 119 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_104 : every 120 120 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_105 : every 121 121 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_106 : every 122 122 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_107 : every 123 123 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_108 : every 124 124 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_109 : every 125 125 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_110 : every 126 126 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_111 : every 127 127 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_112 : every 128 128 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_113 : every 129 129 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_114 : every 130 130 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_115 : every 131 131 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_116 : every 132 132 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_117 : every 133 133 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_118 : every 134 134 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_119 : every 135 135 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_120 : every 136 136 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_121 : every 137 137 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_122 : every 138 138 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_123 : every 139 139 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_124 : every 140 140 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_125 : every 141 141 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_126 : every 142 142 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_127 : every 143 143 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_128 : every 144 144 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_129 : every 145 145 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_130 : every 146 146 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_131 : every 147 147 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_132 : every 148 148 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_133 : every 149 149 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_134 : every 150 150 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_135 : every 151 151 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_136 : every 152 152 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_137 : every 153 153 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_138 : every 154 154 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_139 : every 155 155 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_140 : every 156 156 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_141 : every 157 157 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_142 : every 158 158 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_143 : every 159 159 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_144 : every 160 160 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_145 : every 161 161 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_146 : every 162 162 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_147 : every 163 163 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_148 : every 164 164 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_149 : every 165 165 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_150 : every 166 166 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_151 : every 167 167 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_152 : every 168 168 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_153 : every 169 169 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_154 : every 170 170 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_155 : every 171 171 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_156 : every 172 172 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_157 : every 173 173 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_158 : every 174 174 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_159 : every 175 175 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_160 : every 176 176 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_161 : every 177 177 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_162 : every 178 178 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_163 : every 179 179 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_164 : every 180 180 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_165 : every 181 181 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_166 : every 182 182 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_167 : every 183 183 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_168 : every 184 184 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_169 : every 185 185 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_170 : every 186 186 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_171 : every 187 187 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_172 : every 188 188 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_173 : every 189 189 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_174 : every 190 190 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_175 : every 191 191 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_176 : every 192 192 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_177 : every 193 193 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_178 : every 194 194 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_179 : every 195 195 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_180 : every 196 196 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_181 : every 197 197 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_182 : every 198 198 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_183 : every 199 199 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_184 : every 200 200 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_185 : every 201 201 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_186 : every 202 202 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_187 : every 203 203 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_188 : every 204 204 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_189 : every 205 205 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_190 : every 206 206 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_191 : every 207 207 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_192 : every 208 208 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_193 : every 209 209 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_194 : every 210 210 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_195 : every 211 211 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_196 : every 212 212 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_197 : every 213 213 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_198 : every 214 214 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_199 : every 215 215 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_200 : every 216 216 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_201 : every 217 217 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_202 : every 218 218 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_203 : every 219 219 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_204 : every 220 220 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_205 : every 221 221 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_206 : every 222 222 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_207 : every 223 223 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_208 : every 224 224 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_209 : every 225 225 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_210 : every 226 226 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_211 : every 227 227 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_212 : every 228 228 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_213 : every 229 229 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_214 : every 230 230 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_215 : every 231 231 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_216 : every 232 232 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_217 : every 233 233 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_218 : every 234 234 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_219 : every 235 235 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_220 : every 236 236 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_221 : every 237 237 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_222 : every 238 238 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_223 : every 239 239 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_224 : every 240 240 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_225 : every 241 241 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_226 : every 242 242 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_227 : every 243 243 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_228 : every 244 244 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_229 : every 245 245 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_230 : every 246 246 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_231 : every 247 247 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_232 : every 248 248 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_233 : every 249 249 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_234 : every 250 250 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_235 : every 251 251 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_236 : every 252 252 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_237 : every 253 253 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_238 : every 254 254 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_239 : every 255 255 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_240 : every 256 256 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_241 : every 257 257 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_242 : every 258 258 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_243 : every 259 259 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_244 : every 260 260 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_245 : every 261 261 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_246 : every 262 262 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_247 : every 263 263 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_248 : every 264 264 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_249 : every 265 265 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_250 : every 266 266 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_251 : every 267 267 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_252 : every 268 268 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_253 : every 269 269 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_254 : every 270 270 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_255 : every 271 271 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_256 : every 272 272 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_257 : every 273 273 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_258 : every 274 274 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_259 : every 275 275 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_260 : every 276 276 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_261 : every 277 277 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_262 : every 278 278 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_263 : every 279 279 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_264 : every 280 280 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_265 : every 281 281 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_266 : every 282 282 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_267 : every 283 283 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_268 : every 284 284 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_269 : every 285 285 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_270 : every 286 286 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_271 : every 287 287 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_272 : every 288 288 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_273 : every 289 289 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_274 : every 290 290 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_275 : every 291 291 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_276 : every 292 292 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_277 : every 293 293 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_278 : every 294 294 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_279 : every 295 295 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_280 : every 296 296 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_281 : every 297 297 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_282 : every 298 298 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_283 : every 299 299 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_284 : every 300 300 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_285 : every 301 301 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_286 : every 302 302 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_287 : every 303 303 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_288 : every 304 304 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_289 : every 305 305 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_290 : every 306 306 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_291 : every 307 307 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_292 : every 308 308 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_293 : every 309 309 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_294 : every 310 310 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_295 : every 311 311 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_296 : every 312 312 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_297 : every 313 313 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_298 : every 314 314 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_299 : every 315 315 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_300 : every 316 316 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_301 : every 317 317 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_302 : every 318 318 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_303 : every 319 319 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_304 : every 320 320 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_305 : every 321 321 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_306 : every 322 322 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_307 : every 323 323 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_308 : every 324 324 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_309 : every 325 325 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_310 : every 326 326 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_311 : every 327 327 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_312 : every 328 328 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_313 : every 329 329 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_314 : every 330 330 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_315 : every 331 331 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_316 : every 332 332 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_317 : every 333 333 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_318 : every 334 334 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_319 : every 335 335 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_320 : every 336 336 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_321 : every 337 337 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_322 : every 338 338 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_323 : every 339 339 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_324 : every 340 340 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_325 : every 341 341 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_326 : every 342 342 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_327 : every 343 343 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_328 : every 344 344 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_329 : every 345 345 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_330 : every 346 346 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_331 : every 347 347 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_332 : every 348 348 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_333 : every 349 349 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_334 : every 350 350 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_335 : every 351 351 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_336 : every 352 352 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_337 : every 353 353 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_338 : every 354 354 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_339 : every 355 355 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_340 : every 356 356 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_341 : every 357 357 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_342 : every 358 358 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_343 : every 359 359 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_344 : every 360 360 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_345 : every 361 361 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_346 : every 362 362 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_347 : every 363 363 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_348 : every 364 364 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_349 : every 365 365 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_350 : every 366 366 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_351 : every 367 367 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_352 : every 368 368 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_353 : every 369 369 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_354 : every 370 370 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_355 : every 371 371 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_356 : every 372 372 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_357 : every 373 373 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_358 : every 374 374 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_359 : every 375 375 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_360 : every 376 376 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_361 : every 377 377 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_362 : every 378 378 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_363 : every 379 379 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_364 : every 380 380 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_365 : every 381 381 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_366 : every 382 382 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_367 : every 383 383 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_368 : every 384 384 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_369 : every 385 385 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_370 : every 386 386 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_371 : every 387 387 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_372 : every 388 388 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_373 : every 389 389 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_374 : every 390 390 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_375 : every 391 391 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_376 : every 392 392 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_377 : every 393 393 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_378 : every 394 394 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_379 : every 395 395 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_380 : every 396 396 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_381 : every 397 397 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_382 : every 398 398 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_383 : every 399 399 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_384 : every 400 400 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_385 : every 401 401 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_386 : every 402 402 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_387 : every 403 403 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_388 : every 404 404 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_389 : every 405 405 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_390 : every 406 406 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_391 : every 407 407 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_392 : every 408 408 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_393 : every 409 409 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_394 : every 410 410 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_395 : every 411 411 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_396 : every 412 412 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_397 : every 413 413 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_398 : every 414 414 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_399 : every 415 415 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_400 : every 416 416 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_401 : every 417 417 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_402 : every 418 418 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_403 : every 419 419 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_404 : every 420 420 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_405 : every 421 421 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_406 : every 422 422 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_407 : every 423 423 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_408 : every 424 424 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_409 : every 425 425 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_410 : every 426 426 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_411 : every 427 427 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_412 : every 428 428 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_413 : every 429 429 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_414 : every 430 430 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_415 : every 431 431 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_416 : every 432 432 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_417 : every 433 433 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_418 : every 434 434 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_419 : every 435 435 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_420 : every 436 436 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_421 : every 437 437 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_422 : every 438 438 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_423 : every 439 439 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_424 : every 440 440 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_425 : every 441 441 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_426 : every 442 442 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_427 : every 443 443 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_428 : every 444 444 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_429 : every 445 445 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_430 : every 446 446 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_431 : every 447 447 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_432 : every 448 448 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_433 : every 449 449 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_434 : every 450 450 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_435 : every 451 451 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_436 : every 452 452 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_437 : every 453 453 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_438 : every 454 454 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_439 : every 455 455 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_440 : every 456 456 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_441 : every 457 457 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_442 : every 458 458 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_443 : every 459 459 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_444 : every 460 460 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_445 : every 461 461 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_446 : every 462 462 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_447 : every 463 463 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_448 : every 464 464 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_449 : every 465 465 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_450 : every 466 466 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_451 : every 467 467 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_452 : every 468 468 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_453 : every 469 469 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_454 : every 470 470 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_455 : every 471 471 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_456 : every 472 472 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_457 : every 473 473 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_458 : every 474 474 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_459 : every 475 475 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_460 : every 476 476 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_461 : every 477 477 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_462 : every 478 478 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_463 : every 479 479 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_464 : every 480 480 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_465 : every 481 481 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_466 : every 482 482 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_467 : every 483 483 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_468 : every 484 484 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_469 : every 485 485 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_470 : every 486 486 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_471 : every 487 487 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_472 : every 488 488 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_473 : every 489 489 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_474 : every 490 490 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_475 : every 491 491 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_476 : every 492 492 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_477 : every 493 493 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_478 : every 494 494 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_479 : every 495 495 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_480 : every 496 496 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_481 : every 497 497 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_482 : every 498 498 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_483 : every 499 499 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_484 : every 500 500 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_485 : every 501 501 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem c4_486 : every 502 502 (movingRow 9299 847 4860 23)=true := by decide +kernel
private theorem p4_23 : every 23 23 (atPrime 324 9299 847 4860)=true := by
  have localTest : atPrime 324 9299 847 4860 23=true := (joinEvery (joinEvery (joinEvery (joinEvery (joinEvery (joinEvery (joinEvery (joinEvery c4_12 (joinEvery c4_13 c4_14)) (joinEvery (joinEvery c4_15 c4_16) (joinEvery c4_17 c4_18))) (joinEvery (joinEvery c4_19 (joinEvery c4_20 c4_21)) (joinEvery (joinEvery c4_22 c4_23) (joinEvery c4_24 c4_25)))) (joinEvery (joinEvery (joinEvery c4_26 (joinEvery c4_27 c4_28)) (joinEvery (joinEvery c4_29 c4_30) (joinEvery c4_31 c4_32))) (joinEvery (joinEvery (joinEvery c4_33 c4_34) (joinEvery c4_35 c4_36)) (joinEvery (joinEvery c4_37 c4_38) (joinEvery c4_39 c4_40))))) (joinEvery (joinEvery (joinEvery (joinEvery c4_41 (joinEvery c4_42 c4_43)) (joinEvery (joinEvery c4_44 c4_45) (joinEvery c4_46 c4_47))) (joinEvery (joinEvery (joinEvery c4_48 c4_49) (joinEvery c4_50 c4_51)) (joinEvery (joinEvery c4_52 c4_53) (joinEvery c4_54 c4_55)))) (joinEvery (joinEvery (joinEvery c4_56 (joinEvery c4_57 c4_58)) (joinEvery (joinEvery c4_59 c4_60) (joinEvery c4_61 c4_62))) (joinEvery (joinEvery (joinEvery c4_63 c4_64) (joinEvery c4_65 c4_66)) (joinEvery (joinEvery c4_67 c4_68) (joinEvery c4_69 c4_70)))))) (joinEvery (joinEvery (joinEvery (joinEvery (joinEvery c4_71 (joinEvery c4_72 c4_73)) (joinEvery (joinEvery c4_74 c4_75) (joinEvery c4_76 c4_77))) (joinEvery (joinEvery c4_78 (joinEvery c4_79 c4_80)) (joinEvery (joinEvery c4_81 c4_82) (joinEvery c4_83 c4_84)))) (joinEvery (joinEvery (joinEvery c4_85 (joinEvery c4_86 c4_87)) (joinEvery (joinEvery c4_88 c4_89) (joinEvery c4_90 c4_91))) (joinEvery (joinEvery (joinEvery c4_92 c4_93) (joinEvery c4_94 c4_95)) (joinEvery (joinEvery c4_96 c4_97) (joinEvery c4_98 c4_99))))) (joinEvery (joinEvery (joinEvery (joinEvery c4_100 (joinEvery c4_101 c4_102)) (joinEvery (joinEvery c4_103 c4_104) (joinEvery c4_105 c4_106))) (joinEvery (joinEvery (joinEvery c4_107 c4_108) (joinEvery c4_109 c4_110)) (joinEvery (joinEvery c4_111 c4_112) (joinEvery c4_113 c4_114)))) (joinEvery (joinEvery (joinEvery c4_115 (joinEvery c4_116 c4_117)) (joinEvery (joinEvery c4_118 c4_119) (joinEvery c4_120 c4_121))) (joinEvery (joinEvery (joinEvery c4_122 c4_123) (joinEvery c4_124 c4_125)) (joinEvery (joinEvery c4_126 c4_127) (joinEvery c4_128 c4_129))))))) (joinEvery (joinEvery (joinEvery (joinEvery (joinEvery (joinEvery c4_130 (joinEvery c4_131 c4_132)) (joinEvery (joinEvery c4_133 c4_134) (joinEvery c4_135 c4_136))) (joinEvery (joinEvery c4_137 (joinEvery c4_138 c4_139)) (joinEvery (joinEvery c4_140 c4_141) (joinEvery c4_142 c4_143)))) (joinEvery (joinEvery (joinEvery c4_144 (joinEvery c4_145 c4_146)) (joinEvery (joinEvery c4_147 c4_148) (joinEvery c4_149 c4_150))) (joinEvery (joinEvery (joinEvery c4_151 c4_152) (joinEvery c4_153 c4_154)) (joinEvery (joinEvery c4_155 c4_156) (joinEvery c4_157 c4_158))))) (joinEvery (joinEvery (joinEvery (joinEvery c4_159 (joinEvery c4_160 c4_161)) (joinEvery (joinEvery c4_162 c4_163) (joinEvery c4_164 c4_165))) (joinEvery (joinEvery (joinEvery c4_166 c4_167) (joinEvery c4_168 c4_169)) (joinEvery (joinEvery c4_170 c4_171) (joinEvery c4_172 c4_173)))) (joinEvery (joinEvery (joinEvery c4_174 (joinEvery c4_175 c4_176)) (joinEvery (joinEvery c4_177 c4_178) (joinEvery c4_179 c4_180))) (joinEvery (joinEvery (joinEvery c4_181 c4_182) (joinEvery c4_183 c4_184)) (joinEvery (joinEvery c4_185 c4_186) (joinEvery c4_187 c4_188)))))) (joinEvery (joinEvery (joinEvery (joinEvery (joinEvery c4_189 (joinEvery c4_190 c4_191)) (joinEvery (joinEvery c4_192 c4_193) (joinEvery c4_194 c4_195))) (joinEvery (joinEvery (joinEvery c4_196 c4_197) (joinEvery c4_198 c4_199)) (joinEvery (joinEvery c4_200 c4_201) (joinEvery c4_202 c4_203)))) (joinEvery (joinEvery (joinEvery c4_204 (joinEvery c4_205 c4_206)) (joinEvery (joinEvery c4_207 c4_208) (joinEvery c4_209 c4_210))) (joinEvery (joinEvery (joinEvery c4_211 c4_212) (joinEvery c4_213 c4_214)) (joinEvery (joinEvery c4_215 c4_216) (joinEvery c4_217 c4_218))))) (joinEvery (joinEvery (joinEvery (joinEvery c4_219 (joinEvery c4_220 c4_221)) (joinEvery (joinEvery c4_222 c4_223) (joinEvery c4_224 c4_225))) (joinEvery (joinEvery (joinEvery c4_226 c4_227) (joinEvery c4_228 c4_229)) (joinEvery (joinEvery c4_230 c4_231) (joinEvery c4_232 c4_233)))) (joinEvery (joinEvery (joinEvery c4_234 (joinEvery c4_235 c4_236)) (joinEvery (joinEvery c4_237 c4_238) (joinEvery c4_239 c4_240))) (joinEvery (joinEvery (joinEvery c4_241 c4_242) (joinEvery c4_243 c4_244)) (joinEvery (joinEvery c4_245 c4_246) (joinEvery c4_247 c4_248)))))))) (joinEvery (joinEvery (joinEvery (joinEvery (joinEvery (joinEvery (joinEvery c4_249 (joinEvery c4_250 c4_251)) (joinEvery (joinEvery c4_252 c4_253) (joinEvery c4_254 c4_255))) (joinEvery (joinEvery c4_256 (joinEvery c4_257 c4_258)) (joinEvery (joinEvery c4_259 c4_260) (joinEvery c4_261 c4_262)))) (joinEvery (joinEvery (joinEvery c4_263 (joinEvery c4_264 c4_265)) (joinEvery (joinEvery c4_266 c4_267) (joinEvery c4_268 c4_269))) (joinEvery (joinEvery (joinEvery c4_270 c4_271) (joinEvery c4_272 c4_273)) (joinEvery (joinEvery c4_274 c4_275) (joinEvery c4_276 c4_277))))) (joinEvery (joinEvery (joinEvery (joinEvery c4_278 (joinEvery c4_279 c4_280)) (joinEvery (joinEvery c4_281 c4_282) (joinEvery c4_283 c4_284))) (joinEvery (joinEvery (joinEvery c4_285 c4_286) (joinEvery c4_287 c4_288)) (joinEvery (joinEvery c4_289 c4_290) (joinEvery c4_291 c4_292)))) (joinEvery (joinEvery (joinEvery c4_293 (joinEvery c4_294 c4_295)) (joinEvery (joinEvery c4_296 c4_297) (joinEvery c4_298 c4_299))) (joinEvery (joinEvery (joinEvery c4_300 c4_301) (joinEvery c4_302 c4_303)) (joinEvery (joinEvery c4_304 c4_305) (joinEvery c4_306 c4_307)))))) (joinEvery (joinEvery (joinEvery (joinEvery (joinEvery c4_308 (joinEvery c4_309 c4_310)) (joinEvery (joinEvery c4_311 c4_312) (joinEvery c4_313 c4_314))) (joinEvery (joinEvery (joinEvery c4_315 c4_316) (joinEvery c4_317 c4_318)) (joinEvery (joinEvery c4_319 c4_320) (joinEvery c4_321 c4_322)))) (joinEvery (joinEvery (joinEvery c4_323 (joinEvery c4_324 c4_325)) (joinEvery (joinEvery c4_326 c4_327) (joinEvery c4_328 c4_329))) (joinEvery (joinEvery (joinEvery c4_330 c4_331) (joinEvery c4_332 c4_333)) (joinEvery (joinEvery c4_334 c4_335) (joinEvery c4_336 c4_337))))) (joinEvery (joinEvery (joinEvery (joinEvery c4_338 (joinEvery c4_339 c4_340)) (joinEvery (joinEvery c4_341 c4_342) (joinEvery c4_343 c4_344))) (joinEvery (joinEvery (joinEvery c4_345 c4_346) (joinEvery c4_347 c4_348)) (joinEvery (joinEvery c4_349 c4_350) (joinEvery c4_351 c4_352)))) (joinEvery (joinEvery (joinEvery c4_353 (joinEvery c4_354 c4_355)) (joinEvery (joinEvery c4_356 c4_357) (joinEvery c4_358 c4_359))) (joinEvery (joinEvery (joinEvery c4_360 c4_361) (joinEvery c4_362 c4_363)) (joinEvery (joinEvery c4_364 c4_365) (joinEvery c4_366 c4_367))))))) (joinEvery (joinEvery (joinEvery (joinEvery (joinEvery (joinEvery c4_368 (joinEvery c4_369 c4_370)) (joinEvery (joinEvery c4_371 c4_372) (joinEvery c4_373 c4_374))) (joinEvery (joinEvery c4_375 (joinEvery c4_376 c4_377)) (joinEvery (joinEvery c4_378 c4_379) (joinEvery c4_380 c4_381)))) (joinEvery (joinEvery (joinEvery c4_382 (joinEvery c4_383 c4_384)) (joinEvery (joinEvery c4_385 c4_386) (joinEvery c4_387 c4_388))) (joinEvery (joinEvery (joinEvery c4_389 c4_390) (joinEvery c4_391 c4_392)) (joinEvery (joinEvery c4_393 c4_394) (joinEvery c4_395 c4_396))))) (joinEvery (joinEvery (joinEvery (joinEvery c4_397 (joinEvery c4_398 c4_399)) (joinEvery (joinEvery c4_400 c4_401) (joinEvery c4_402 c4_403))) (joinEvery (joinEvery (joinEvery c4_404 c4_405) (joinEvery c4_406 c4_407)) (joinEvery (joinEvery c4_408 c4_409) (joinEvery c4_410 c4_411)))) (joinEvery (joinEvery (joinEvery c4_412 (joinEvery c4_413 c4_414)) (joinEvery (joinEvery c4_415 c4_416) (joinEvery c4_417 c4_418))) (joinEvery (joinEvery (joinEvery c4_419 c4_420) (joinEvery c4_421 c4_422)) (joinEvery (joinEvery c4_423 c4_424) (joinEvery c4_425 c4_426)))))) (joinEvery (joinEvery (joinEvery (joinEvery (joinEvery c4_427 (joinEvery c4_428 c4_429)) (joinEvery (joinEvery c4_430 c4_431) (joinEvery c4_432 c4_433))) (joinEvery (joinEvery (joinEvery c4_434 c4_435) (joinEvery c4_436 c4_437)) (joinEvery (joinEvery c4_438 c4_439) (joinEvery c4_440 c4_441)))) (joinEvery (joinEvery (joinEvery c4_442 (joinEvery c4_443 c4_444)) (joinEvery (joinEvery c4_445 c4_446) (joinEvery c4_447 c4_448))) (joinEvery (joinEvery (joinEvery c4_449 c4_450) (joinEvery c4_451 c4_452)) (joinEvery (joinEvery c4_453 c4_454) (joinEvery c4_455 c4_456))))) (joinEvery (joinEvery (joinEvery (joinEvery c4_457 (joinEvery c4_458 c4_459)) (joinEvery (joinEvery c4_460 c4_461) (joinEvery c4_462 c4_463))) (joinEvery (joinEvery (joinEvery c4_464 c4_465) (joinEvery c4_466 c4_467)) (joinEvery (joinEvery c4_468 c4_469) (joinEvery c4_470 c4_471)))) (joinEvery (joinEvery (joinEvery c4_472 (joinEvery c4_473 c4_474)) (joinEvery (joinEvery c4_475 c4_476) (joinEvery c4_477 c4_478))) (joinEvery (joinEvery (joinEvery c4_479 c4_480) (joinEvery c4_481 c4_482)) (joinEvery (joinEvery c4_483 c4_484) (joinEvery c4_485 c4_486)))))))))
  apply List.all_eq_true.mpr; intro j hj; obtain ⟨lo,hi⟩:=List.mem_range'_1.mp hj
  simpa only [show j=23 by omega] using localTest
private theorem c4_487 : every 24 28 (atPrime 324 9299 847 4860)=true := by decide +kernel
private theorem c4_488 : every 30 58 (fixedPair 324 9299 847 4860 29)=true := by decide +kernel
private theorem c4_489 : every 59 82 (fixedPair 324 9299 847 4860 29)=true := by decide +kernel
private theorem c4_490 : every 83 108 (fixedPair 324 9299 847 4860 29)=true := by decide +kernel
private theorem c4_491 : every 109 138 (fixedPair 324 9299 847 4860 29)=true := by decide +kernel
private theorem c4_492 : every 139 168 (fixedPair 324 9299 847 4860 29)=true := by decide +kernel
private theorem c4_493 : every 169 198 (fixedPair 324 9299 847 4860 29)=true := by decide +kernel
private theorem c4_494 : every 199 217 (fixedPair 324 9299 847 4860 29)=true := by decide +kernel
private theorem c4_495 : every 1 28 (moving 218 7 9299 847 4860 29)=true := by decide +kernel
private theorem c4_496 : every 29 38 (moving 218 7 9299 847 4860 29)=true := by decide +kernel
private theorem p4_29 : every 29 29 (atPrime 324 9299 847 4860)=true := by
  have localTest : atPrime 324 9299 847 4860 29=true := by change (every 30 217 (fixedPair 324 9299 847 4860 29) && every 1 38 (moving 218 7 9299 847 4860 29)) = true; rw [Bool.and_eq_true]; exact ⟨(joinEvery (joinEvery c4_488 (joinEvery c4_489 c4_490)) (joinEvery (joinEvery c4_491 c4_492) (joinEvery c4_493 c4_494))),(joinEvery c4_495 c4_496)⟩
  apply List.all_eq_true.mpr; intro j hj; obtain ⟨lo,hi⟩:=List.mem_range'_1.mp hj
  simpa only [show j=29 by omega] using localTest
private theorem c4_497 : every 30 30 (atPrime 324 9299 847 4860)=true := by decide +kernel
private theorem c4_498 : every 32 60 (fixedPair 324 9299 847 4860 31)=true := by decide +kernel
private theorem c4_499 : every 61 88 (fixedPair 324 9299 847 4860 31)=true := by decide +kernel
private theorem c4_500 : every 89 112 (fixedPair 324 9299 847 4860 31)=true := by decide +kernel
private theorem c4_501 : every 113 148 (fixedPair 324 9299 847 4860 31)=true := by decide +kernel
private theorem c4_502 : every 149 174 (fixedPair 324 9299 847 4860 31)=true := by decide +kernel
private theorem c4_503 : every 1 28 (moving 175 7 9299 847 4860 31)=true := by decide +kernel
private theorem c4_504 : every 29 30 (moving 175 7 9299 847 4860 31)=true := by decide +kernel
private theorem p4_31 : every 31 31 (atPrime 324 9299 847 4860)=true := by
  have localTest : atPrime 324 9299 847 4860 31=true := by change (every 32 174 (fixedPair 324 9299 847 4860 31) && every 1 30 (moving 175 7 9299 847 4860 31)) = true; rw [Bool.and_eq_true]; exact ⟨(joinEvery (joinEvery c4_498 c4_499) (joinEvery c4_500 (joinEvery c4_501 c4_502))),(joinEvery c4_503 c4_504)⟩
  apply List.all_eq_true.mpr; intro j hj; obtain ⟨lo,hi⟩:=List.mem_range'_1.mp hj
  simpa only [show j=31 by omega] using localTest
private theorem c4_505 : every 32 36 (atPrime 324 9299 847 4860)=true := by decide +kernel
private theorem c4_506 : every 38 66 (fixedPair 324 9299 847 4860 37)=true := by decide +kernel
private theorem c4_507 : every 67 96 (fixedPair 324 9299 847 4860 37)=true := by decide +kernel
private theorem c4_508 : every 97 118 (fixedPair 324 9299 847 4860 37)=true := by decide +kernel
private theorem c4_509 : every 1 20 (moving 119 8 9299 847 4860 37)=true := by decide +kernel
private theorem p4_37 : every 37 37 (atPrime 324 9299 847 4860)=true := by
  have localTest : atPrime 324 9299 847 4860 37=true := by change (every 38 118 (fixedPair 324 9299 847 4860 37) && every 1 20 (moving 119 8 9299 847 4860 37)) = true; rw [Bool.and_eq_true]; exact ⟨(joinEvery c4_506 (joinEvery c4_507 c4_508)),c4_509⟩
  apply List.all_eq_true.mpr; intro j hj; obtain ⟨lo,hi⟩:=List.mem_range'_1.mp hj
  simpa only [show j=37 by omega] using localTest
private theorem c4_510 : every 38 40 (atPrime 324 9299 847 4860)=true := by decide +kernel
private theorem c4_511 : every 42 70 (fixedPair 324 9299 847 4860 41)=true := by decide +kernel
private theorem c4_512 : every 71 100 (fixedPair 324 9299 847 4860 41)=true := by decide +kernel
private theorem c4_513 : every 101 102 (fixedPair 324 9299 847 4860 41)=true := by decide +kernel
private theorem c4_514 : every 1 17 (moving 103 9 9299 847 4860 41)=true := by decide +kernel
private theorem p4_41 : every 41 41 (atPrime 324 9299 847 4860)=true := by
  have localTest : atPrime 324 9299 847 4860 41=true := by change (every 42 102 (fixedPair 324 9299 847 4860 41) && every 1 17 (moving 103 9 9299 847 4860 41)) = true; rw [Bool.and_eq_true]; exact ⟨(joinEvery c4_511 (joinEvery c4_512 c4_513)),c4_514⟩
  apply List.all_eq_true.mpr; intro j hj; obtain ⟨lo,hi⟩:=List.mem_range'_1.mp hj
  simpa only [show j=41 by omega] using localTest
private theorem c4_515 : every 42 42 (atPrime 324 9299 847 4860)=true := by decide +kernel
private theorem c4_516 : every 44 72 (fixedPair 324 9299 847 4860 43)=true := by decide +kernel
private theorem c4_517 : every 73 96 (fixedPair 324 9299 847 4860 43)=true := by decide +kernel
private theorem c4_518 : every 1 16 (moving 97 9 9299 847 4860 43)=true := by decide +kernel
private theorem p4_43 : every 43 43 (atPrime 324 9299 847 4860)=true := by
  have localTest : atPrime 324 9299 847 4860 43=true := by change (every 44 96 (fixedPair 324 9299 847 4860 43) && every 1 16 (moving 97 9 9299 847 4860 43)) = true; rw [Bool.and_eq_true]; exact ⟨(joinEvery c4_516 c4_517),c4_518⟩
  apply List.all_eq_true.mpr; intro j hj; obtain ⟨lo,hi⟩:=List.mem_range'_1.mp hj
  simpa only [show j=43 by omega] using localTest
private theorem c4_519 : every 44 46 (atPrime 324 9299 847 4860)=true := by decide +kernel
private theorem c4_520 : every 48 77 (fixedPair 324 9299 847 4860 47)=true := by decide +kernel
private theorem c4_521 : every 78 87 (fixedPair 324 9299 847 4860 47)=true := by decide +kernel
private theorem c4_522 : every 1 15 (moving 88 10 9299 847 4860 47)=true := by decide +kernel
private theorem p4_47 : every 47 47 (atPrime 324 9299 847 4860)=true := by
  have localTest : atPrime 324 9299 847 4860 47=true := by change (every 48 87 (fixedPair 324 9299 847 4860 47) && every 1 15 (moving 88 10 9299 847 4860 47)) = true; rw [Bool.and_eq_true]; exact ⟨(joinEvery c4_520 c4_521),c4_522⟩
  apply List.all_eq_true.mpr; intro j hj; obtain ⟨lo,hi⟩:=List.mem_range'_1.mp hj
  simpa only [show j=47 by omega] using localTest
private theorem c4_523 : every 48 52 (atPrime 324 9299 847 4860)=true := by decide +kernel
private theorem c4_524 : every 54 79 (fixedPair 324 9299 847 4860 53)=true := by decide +kernel
private theorem c4_525 : every 1 13 (moving 80 11 9299 847 4860 53)=true := by decide +kernel
private theorem p4_53 : every 53 53 (atPrime 324 9299 847 4860)=true := by
  have localTest : atPrime 324 9299 847 4860 53=true := by change (every 54 79 (fixedPair 324 9299 847 4860 53) && every 1 13 (moving 80 11 9299 847 4860 53)) = true; rw [Bool.and_eq_true]; exact ⟨c4_524,c4_525⟩
  apply List.all_eq_true.mpr; intro j hj; obtain ⟨lo,hi⟩:=List.mem_range'_1.mp hj
  simpa only [show j=53 by omega] using localTest
private theorem c4_526 : every 54 58 (atPrime 324 9299 847 4860)=true := by decide +kernel
private theorem c4_527 : every 60 73 (fixedPair 324 9299 847 4860 59)=true := by decide +kernel
private theorem c4_528 : every 1 12 (moving 74 12 9299 847 4860 59)=true := by decide +kernel
private theorem p4_59 : every 59 59 (atPrime 324 9299 847 4860)=true := by
  have localTest : atPrime 324 9299 847 4860 59=true := by change (every 60 73 (fixedPair 324 9299 847 4860 59) && every 1 12 (moving 74 12 9299 847 4860 59)) = true; rw [Bool.and_eq_true]; exact ⟨c4_527,c4_528⟩
  apply List.all_eq_true.mpr; intro j hj; obtain ⟨lo,hi⟩:=List.mem_range'_1.mp hj
  simpa only [show j=59 by omega] using localTest
private theorem c4_529 : every 60 60 (atPrime 324 9299 847 4860)=true := by decide +kernel
private theorem c4_530 : every 62 72 (fixedPair 324 9299 847 4860 61)=true := by decide +kernel
private theorem c4_531 : every 1 12 (moving 73 12 9299 847 4860 61)=true := by decide +kernel
private theorem p4_61 : every 61 61 (atPrime 324 9299 847 4860)=true := by
  have localTest : atPrime 324 9299 847 4860 61=true := by change (every 62 72 (fixedPair 324 9299 847 4860 61) && every 1 12 (moving 73 12 9299 847 4860 61)) = true; rw [Bool.and_eq_true]; exact ⟨c4_530,c4_531⟩
  apply List.all_eq_true.mpr; intro j hj; obtain ⟨lo,hi⟩:=List.mem_range'_1.mp hj
  simpa only [show j=61 by omega] using localTest
private theorem c4_532 : every 62 66 (atPrime 324 9299 847 4860)=true := by decide +kernel
private theorem c4_533 : every 68 68 (fixedPair 324 9299 847 4860 67)=true := by decide +kernel
private theorem c4_534 : every 1 12 (moving 69 14 9299 847 4860 67)=true := by decide +kernel
private theorem p4_67 : every 67 67 (atPrime 324 9299 847 4860)=true := by
  have localTest : atPrime 324 9299 847 4860 67=true := by change (every 68 68 (fixedPair 324 9299 847 4860 67) && every 1 12 (moving 69 14 9299 847 4860 67)) = true; rw [Bool.and_eq_true]; exact ⟨c4_533,c4_534⟩
  apply List.all_eq_true.mpr; intro j hj; obtain ⟨lo,hi⟩:=List.mem_range'_1.mp hj
  simpa only [show j=67 by omega] using localTest
private theorem c4_535 : every 68 70 (atPrime 324 9299 847 4860)=true := by decide +kernel
private theorem c4_536 : every 72 66 (fixedPair 324 9299 847 4860 71)=true := by decide +kernel
private theorem c4_537 : every 1 11 (moving 72 14 9299 847 4860 71)=true := by decide +kernel
private theorem p4_71 : every 71 71 (atPrime 324 9299 847 4860)=true := by
  have localTest : atPrime 324 9299 847 4860 71=true := by change (every 72 66 (fixedPair 324 9299 847 4860 71) && every 1 11 (moving 72 14 9299 847 4860 71)) = true; rw [Bool.and_eq_true]; exact ⟨c4_536,c4_537⟩
  apply List.all_eq_true.mpr; intro j hj; obtain ⟨lo,hi⟩:=List.mem_range'_1.mp hj
  simpa only [show j=71 by omega] using localTest
private theorem c4_538 : every 72 72 (atPrime 324 9299 847 4860)=true := by decide +kernel
private theorem c4_539 : every 74 65 (fixedPair 324 9299 847 4860 73)=true := by decide +kernel
private theorem c4_540 : every 1 11 (moving 74 15 9299 847 4860 73)=true := by decide +kernel
private theorem p4_73 : every 73 73 (atPrime 324 9299 847 4860)=true := by
  have localTest : atPrime 324 9299 847 4860 73=true := by change (every 74 65 (fixedPair 324 9299 847 4860 73) && every 1 11 (moving 74 15 9299 847 4860 73)) = true; rw [Bool.and_eq_true]; exact ⟨c4_539,c4_540⟩
  apply List.all_eq_true.mpr; intro j hj; obtain ⟨lo,hi⟩:=List.mem_range'_1.mp hj
  simpa only [show j=73 by omega] using localTest
private theorem c4_541 : every 74 78 (atPrime 324 9299 847 4860)=true := by decide +kernel
private theorem c4_542 : every 80 63 (fixedPair 324 9299 847 4860 79)=true := by decide +kernel
private theorem c4_543 : every 1 11 (moving 80 16 9299 847 4860 79)=true := by decide +kernel
private theorem p4_79 : every 79 79 (atPrime 324 9299 847 4860)=true := by
  have localTest : atPrime 324 9299 847 4860 79=true := by change (every 80 63 (fixedPair 324 9299 847 4860 79) && every 1 11 (moving 80 16 9299 847 4860 79)) = true; rw [Bool.and_eq_true]; exact ⟨c4_542,c4_543⟩
  apply List.all_eq_true.mpr; intro j hj; obtain ⟨lo,hi⟩:=List.mem_range'_1.mp hj
  simpa only [show j=79 by omega] using localTest
private theorem c4_544 : every 80 82 (atPrime 324 9299 847 4860)=true := by decide +kernel
private theorem c4_545 : every 84 62 (fixedPair 324 9299 847 4860 83)=true := by decide +kernel
private theorem c4_546 : every 1 11 (moving 84 16 9299 847 4860 83)=true := by decide +kernel
private theorem p4_83 : every 83 83 (atPrime 324 9299 847 4860)=true := by
  have localTest : atPrime 324 9299 847 4860 83=true := by change (every 84 62 (fixedPair 324 9299 847 4860 83) && every 1 11 (moving 84 16 9299 847 4860 83)) = true; rw [Bool.and_eq_true]; exact ⟨c4_545,c4_546⟩
  apply List.all_eq_true.mpr; intro j hj; obtain ⟨lo,hi⟩:=List.mem_range'_1.mp hj
  simpa only [show j=83 by omega] using localTest
private theorem c4_547 : every 84 88 (atPrime 324 9299 847 4860)=true := by decide +kernel
private theorem c4_548 : every 90 60 (fixedPair 324 9299 847 4860 89)=true := by decide +kernel
private theorem c4_549 : every 1 10 (moving 90 18 9299 847 4860 89)=true := by decide +kernel
private theorem p4_89 : every 89 89 (atPrime 324 9299 847 4860)=true := by
  have localTest : atPrime 324 9299 847 4860 89=true := by change (every 90 60 (fixedPair 324 9299 847 4860 89) && every 1 10 (moving 90 18 9299 847 4860 89)) = true; rw [Bool.and_eq_true]; exact ⟨c4_548,c4_549⟩
  apply List.all_eq_true.mpr; intro j hj; obtain ⟨lo,hi⟩:=List.mem_range'_1.mp hj
  simpa only [show j=89 by omega] using localTest
private theorem c4_550 : every 90 92 (atPrime 324 9299 847 4860)=true := by decide +kernel
theorem at4 : cert 4=true := (joinEvery (joinEvery (joinEvery (joinEvery (joinEvery p4_5 c4_1) (joinEvery p4_7 (joinEvery c4_3 p4_11))) (joinEvery (joinEvery c4_5 (joinEvery p4_13 c4_7)) (joinEvery p4_17 (joinEvery c4_9 p4_19)))) (joinEvery (joinEvery (joinEvery c4_11 p4_23) (joinEvery c4_487 (joinEvery p4_29 c4_497))) (joinEvery (joinEvery p4_31 (joinEvery c4_505 p4_37)) (joinEvery c4_510 (joinEvery p4_41 c4_515))))) (joinEvery (joinEvery (joinEvery (joinEvery p4_43 c4_519) (joinEvery p4_47 (joinEvery c4_523 p4_53))) (joinEvery (joinEvery c4_526 (joinEvery p4_59 c4_529)) (joinEvery p4_61 (joinEvery c4_532 p4_67)))) (joinEvery (joinEvery (joinEvery c4_535 p4_71) (joinEvery c4_538 (joinEvery p4_73 c4_541))) (joinEvery (joinEvery p4_79 (joinEvery c4_544 p4_83)) (joinEvery c4_547 (joinEvery p4_89 c4_550))))))
end OMA.RankThreeFourSmallTables245212

end

section
/- Independently checked consecutive interval for the compressed two-prime decision. -/
namespace OMA.RankThreeFourSmallCompactTables245212
open OMA.CofactorEulerPair245212 OMA.RankThreeFourSmallCompact245212
open OMA.RankThreeMiddle245212 (joinEvery)
set_option maxRecDepth 65536
set_option maxHeartbeats 2200000
private theorem r5_5_12 : every 5 12 (run 972 34085 2548 17496)=true := by decide +kernel
private theorem r5_13_20 : every 13 20 (run 972 34085 2548 17496)=true := by decide +kernel
private theorem r5_21_28 : every 21 28 (run 972 34085 2548 17496)=true := by decide +kernel
private theorem r5_29_36 : every 29 36 (run 972 34085 2548 17496)=true := by decide +kernel
private theorem r5_37_44 : every 37 44 (run 972 34085 2548 17496)=true := by decide +kernel
private theorem r5_45_52 : every 45 52 (run 972 34085 2548 17496)=true := by decide +kernel
private theorem r5_53_60 : every 53 60 (run 972 34085 2548 17496)=true := by decide +kernel
private theorem r5_61_68 : every 61 68 (run 972 34085 2548 17496)=true := by decide +kernel
private theorem r5_69_76 : every 69 76 (run 972 34085 2548 17496)=true := by decide +kernel
private theorem r5_77_84 : every 77 84 (run 972 34085 2548 17496)=true := by decide +kernel
private theorem r5_85_92 : every 85 92 (run 972 34085 2548 17496)=true := by decide +kernel
private theorem r5_93_100 : every 93 100 (run 972 34085 2548 17496)=true := by decide +kernel
private theorem r5_101_108 : every 101 108 (run 972 34085 2548 17496)=true := by decide +kernel
private theorem r5_109_116 : every 109 116 (run 972 34085 2548 17496)=true := by decide +kernel
private theorem r5_117_124 : every 117 124 (run 972 34085 2548 17496)=true := by decide +kernel
private theorem r5_125_132 : every 125 132 (run 972 34085 2548 17496)=true := by decide +kernel
private theorem r5_133_140 : every 133 140 (run 972 34085 2548 17496)=true := by decide +kernel
private theorem r5_141_148 : every 141 148 (run 972 34085 2548 17496)=true := by decide +kernel
private theorem r5_149_156 : every 149 156 (run 972 34085 2548 17496)=true := by decide +kernel
private theorem r5_157_164 : every 157 164 (run 972 34085 2548 17496)=true := by decide +kernel
private theorem r5_165_172 : every 165 172 (run 972 34085 2548 17496)=true := by decide +kernel
private theorem r5_173_180 : every 173 180 (run 972 34085 2548 17496)=true := by decide +kernel
private theorem r5_181_188 : every 181 188 (run 972 34085 2548 17496)=true := by decide +kernel
private theorem r5_189_196 : every 189 196 (run 972 34085 2548 17496)=true := by decide +kernel
private theorem r5_197_204 : every 197 204 (run 972 34085 2548 17496)=true := by decide +kernel
private theorem r5_205_212 : every 205 212 (run 972 34085 2548 17496)=true := by decide +kernel
private theorem r5_213_220 : every 213 220 (run 972 34085 2548 17496)=true := by decide +kernel
private theorem r5_221_228 : every 221 228 (run 972 34085 2548 17496)=true := by decide +kernel
private theorem r5_229_236 : every 229 236 (run 972 34085 2548 17496)=true := by decide +kernel
private theorem r5_237_244 : every 237 244 (run 972 34085 2548 17496)=true := by decide +kernel
private theorem r5_245_252 : every 245 252 (run 972 34085 2548 17496)=true := by decide +kernel
private theorem r5_253_259 : every 253 259 (run 972 34085 2548 17496)=true := by decide +kernel
theorem span5_5_259 : every 5 259 (run 972 34085 2548 17496)=true := (joinEvery (joinEvery (joinEvery (joinEvery (joinEvery r5_5_12 r5_13_20) (joinEvery r5_21_28 r5_29_36)) (joinEvery (joinEvery r5_37_44 r5_45_52) (joinEvery r5_53_60 r5_61_68))) (joinEvery (joinEvery (joinEvery r5_69_76 r5_77_84) (joinEvery r5_85_92 r5_93_100)) (joinEvery (joinEvery r5_101_108 r5_109_116) (joinEvery r5_117_124 r5_125_132)))) (joinEvery (joinEvery (joinEvery (joinEvery r5_133_140 r5_141_148) (joinEvery r5_149_156 r5_157_164)) (joinEvery (joinEvery r5_165_172 r5_173_180) (joinEvery r5_181_188 r5_189_196))) (joinEvery (joinEvery (joinEvery r5_197_204 r5_205_212) (joinEvery r5_213_220 r5_221_228)) (joinEvery (joinEvery r5_229_236 r5_237_244) (joinEvery r5_245_252 r5_253_259)))))
end OMA.RankThreeFourSmallCompactTables245212

end

section
/- Independently checked consecutive interval for the compressed two-prime decision. -/
namespace OMA.RankThreeFourSmallCompactTables245212
open OMA.CofactorEulerPair245212 OMA.RankThreeFourSmallCompact245212
open OMA.RankThreeMiddle245212 (joinEvery)
set_option maxRecDepth 65536
set_option maxHeartbeats 2200000
private theorem r6_5_12 : every 5 12 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_13_20 : every 13 20 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_21_28 : every 21 28 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_29_36 : every 29 36 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_37_44 : every 37 44 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_45_52 : every 45 52 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_53_60 : every 53 60 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_61_68 : every 61 68 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_69_76 : every 69 76 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_77_84 : every 77 84 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_85_92 : every 85 92 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_93_100 : every 93 100 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_101_108 : every 101 108 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_109_116 : every 109 116 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_117_124 : every 117 124 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_125_132 : every 125 132 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_133_140 : every 133 140 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_141_148 : every 141 148 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_149_156 : every 149 156 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_157_164 : every 157 164 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_165_172 : every 165 172 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_173_180 : every 173 180 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_181_188 : every 181 188 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_189_196 : every 189 196 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_197_204 : every 197 204 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_205_212 : every 205 212 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_213_220 : every 213 220 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_221_228 : every 221 228 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_229_236 : every 229 236 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_237_244 : every 237 244 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_245_252 : every 245 252 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_253_259 : every 253 259 (run 2916 120836 7651 61236)=true := by decide +kernel
theorem span6_5_259 : every 5 259 (run 2916 120836 7651 61236)=true := (joinEvery (joinEvery (joinEvery (joinEvery (joinEvery r6_5_12 r6_13_20) (joinEvery r6_21_28 r6_29_36)) (joinEvery (joinEvery r6_37_44 r6_45_52) (joinEvery r6_53_60 r6_61_68))) (joinEvery (joinEvery (joinEvery r6_69_76 r6_77_84) (joinEvery r6_85_92 r6_93_100)) (joinEvery (joinEvery r6_101_108 r6_109_116) (joinEvery r6_117_124 r6_125_132)))) (joinEvery (joinEvery (joinEvery (joinEvery r6_133_140 r6_141_148) (joinEvery r6_149_156 r6_157_164)) (joinEvery (joinEvery r6_165_172 r6_173_180) (joinEvery r6_181_188 r6_189_196))) (joinEvery (joinEvery (joinEvery r6_197_204 r6_205_212) (joinEvery r6_213_220 r6_221_228)) (joinEvery (joinEvery r6_229_236 r6_237_244) (joinEvery r6_245_252 r6_253_259)))))
end OMA.RankThreeFourSmallCompactTables245212

end

section
/- Independently checked consecutive interval for the compressed two-prime decision. -/
namespace OMA.RankThreeFourSmallCompactTables245212
open OMA.CofactorEulerPair245212 OMA.RankThreeFourSmallCompact245212
open OMA.RankThreeMiddle245212 (joinEvery)
set_option maxRecDepth 65536
set_option maxHeartbeats 2200000
private theorem r6_260_267 : every 260 267 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_268_275 : every 268 275 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_276_283 : every 276 283 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_284_291 : every 284 291 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_292_299 : every 292 299 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_300_307 : every 300 307 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_308_315 : every 308 315 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_316_323 : every 316 323 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_324_331 : every 324 331 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_332_339 : every 332 339 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_340_347 : every 340 347 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_348_355 : every 348 355 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_356_363 : every 356 363 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_364_371 : every 364 371 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_372_379 : every 372 379 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_380_387 : every 380 387 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_388_395 : every 388 395 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_396_403 : every 396 403 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_404_411 : every 404 411 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_412_419 : every 412 419 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_420_427 : every 420 427 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_428_435 : every 428 435 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_436_443 : every 436 443 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_444_451 : every 444 451 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_452_459 : every 452 459 (run 2916 120836 7651 61236)=true := by decide +kernel
theorem span6_260_459 : every 260 459 (run 2916 120836 7651 61236)=true := (joinEvery (joinEvery (joinEvery (joinEvery r6_260_267 (joinEvery r6_268_275 r6_276_283)) (joinEvery r6_284_291 (joinEvery r6_292_299 r6_300_307))) (joinEvery (joinEvery r6_308_315 (joinEvery r6_316_323 r6_324_331)) (joinEvery r6_332_339 (joinEvery r6_340_347 r6_348_355)))) (joinEvery (joinEvery (joinEvery r6_356_363 (joinEvery r6_364_371 r6_372_379)) (joinEvery r6_380_387 (joinEvery r6_388_395 r6_396_403))) (joinEvery (joinEvery r6_404_411 (joinEvery r6_412_419 r6_420_427)) (joinEvery (joinEvery r6_428_435 r6_436_443) (joinEvery r6_444_451 r6_452_459)))))
end OMA.RankThreeFourSmallCompactTables245212

end

section
/- Independently checked consecutive interval for the compressed two-prime decision. -/
namespace OMA.RankThreeFourSmallCompactTables245212
open OMA.CofactorEulerPair245212 OMA.RankThreeFourSmallCompact245212
open OMA.RankThreeMiddle245212 (joinEvery)
set_option maxRecDepth 65536
set_option maxHeartbeats 2200000
private theorem r6_460_467 : every 460 467 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_468_475 : every 468 475 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_476_483 : every 476 483 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_484_491 : every 484 491 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_492_499 : every 492 499 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_500_507 : every 500 507 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_508_515 : every 508 515 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_516_523 : every 516 523 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_524_531 : every 524 531 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_532_539 : every 532 539 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_540_547 : every 540 547 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_548_555 : every 548 555 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_556_563 : every 556 563 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_564_571 : every 564 571 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_572_579 : every 572 579 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_580_587 : every 580 587 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_588_595 : every 588 595 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_596_603 : every 596 603 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_604_611 : every 604 611 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_612_619 : every 612 619 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_620_627 : every 620 627 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_628_635 : every 628 635 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_636_643 : every 636 643 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_644_651 : every 644 651 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_652_659 : every 652 659 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_660_667 : every 660 667 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_668_675 : every 668 675 (run 2916 120836 7651 61236)=true := by decide +kernel
private theorem r6_676_678 : every 676 678 (run 2916 120836 7651 61236)=true := by decide +kernel
theorem span6_460_678 : every 460 678 (run 2916 120836 7651 61236)=true := (joinEvery (joinEvery (joinEvery (joinEvery r6_460_467 (joinEvery r6_468_475 r6_476_483)) (joinEvery (joinEvery r6_484_491 r6_492_499) (joinEvery r6_500_507 r6_508_515))) (joinEvery (joinEvery r6_516_523 (joinEvery r6_524_531 r6_532_539)) (joinEvery (joinEvery r6_540_547 r6_548_555) (joinEvery r6_556_563 r6_564_571)))) (joinEvery (joinEvery (joinEvery r6_572_579 (joinEvery r6_580_587 r6_588_595)) (joinEvery (joinEvery r6_596_603 r6_604_611) (joinEvery r6_612_619 r6_620_627))) (joinEvery (joinEvery r6_628_635 (joinEvery r6_636_643 r6_644_651)) (joinEvery (joinEvery r6_652_659 r6_660_667) (joinEvery r6_668_675 r6_676_678)))))
end OMA.RankThreeFourSmallCompactTables245212

end

section
/- Independently checked consecutive interval for the compressed two-prime decision. -/
namespace OMA.RankThreeFourSmallCompactTables245212
open OMA.CofactorEulerPair245212 OMA.RankThreeFourSmallCompact245212
open OMA.RankThreeMiddle245212 (joinEvery)
set_option maxRecDepth 65536
set_option maxHeartbeats 2200000
private theorem r7_5_9 : every 5 9 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_10_14 : every 10 14 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_15_19 : every 15 19 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_20_24 : every 20 24 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_25_29 : every 25 29 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_30_34 : every 30 34 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_35_39 : every 35 39 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_40_44 : every 40 44 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_45_49 : every 45 49 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_50_54 : every 50 54 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_55_59 : every 55 59 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_60_64 : every 60 64 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_65_69 : every 65 69 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_70_74 : every 70 74 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_75_79 : every 75 79 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_80_84 : every 80 84 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_85_89 : every 85 89 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_90_94 : every 90 94 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_95_99 : every 95 99 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_100_104 : every 100 104 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_105_109 : every 105 109 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_110_114 : every 110 114 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_115_119 : every 115 119 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_120_124 : every 120 124 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_125_129 : every 125 129 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_130_134 : every 130 134 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_135_139 : every 135 139 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_140_144 : every 140 144 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_145_149 : every 145 149 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_150_154 : every 150 154 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_155_159 : every 155 159 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_160_164 : every 160 164 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_165_169 : every 165 169 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_170_174 : every 170 174 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_175_179 : every 175 179 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_180_184 : every 180 184 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_185_189 : every 185 189 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_190_194 : every 190 194 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_195_199 : every 195 199 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_200_204 : every 200 204 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_205_209 : every 205 209 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_210_214 : every 210 214 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_215_219 : every 215 219 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_220_224 : every 220 224 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_225_229 : every 225 229 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_230_234 : every 230 234 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_235_239 : every 235 239 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_240_244 : every 240 244 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_245_249 : every 245 249 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_250_251 : every 250 251 (run 8748 418268 22960 209952)=true := by decide +kernel
theorem span7_5_251 : every 5 251 (run 8748 418268 22960 209952)=true := (joinEvery (joinEvery (joinEvery (joinEvery (joinEvery r7_5_9 (joinEvery r7_10_14 r7_15_19)) (joinEvery r7_20_24 (joinEvery r7_25_29 r7_30_34))) (joinEvery (joinEvery r7_35_39 (joinEvery r7_40_44 r7_45_49)) (joinEvery r7_50_54 (joinEvery r7_55_59 r7_60_64)))) (joinEvery (joinEvery (joinEvery r7_65_69 (joinEvery r7_70_74 r7_75_79)) (joinEvery r7_80_84 (joinEvery r7_85_89 r7_90_94))) (joinEvery (joinEvery r7_95_99 (joinEvery r7_100_104 r7_105_109)) (joinEvery (joinEvery r7_110_114 r7_115_119) (joinEvery r7_120_124 r7_125_129))))) (joinEvery (joinEvery (joinEvery (joinEvery r7_130_134 (joinEvery r7_135_139 r7_140_144)) (joinEvery r7_145_149 (joinEvery r7_150_154 r7_155_159))) (joinEvery (joinEvery r7_160_164 (joinEvery r7_165_169 r7_170_174)) (joinEvery r7_175_179 (joinEvery r7_180_184 r7_185_189)))) (joinEvery (joinEvery (joinEvery r7_190_194 (joinEvery r7_195_199 r7_200_204)) (joinEvery r7_205_209 (joinEvery r7_210_214 r7_215_219))) (joinEvery (joinEvery r7_220_224 (joinEvery r7_225_229 r7_230_234)) (joinEvery (joinEvery r7_235_239 r7_240_244) (joinEvery r7_245_249 r7_250_251))))))
end OMA.RankThreeFourSmallCompactTables245212

end

section
/- Independently checked consecutive interval for the compressed two-prime decision. -/
namespace OMA.RankThreeFourSmallCompactTables245212
open OMA.CofactorEulerPair245212 OMA.RankThreeFourSmallCompact245212
open OMA.RankThreeMiddle245212 (joinEvery)
set_option maxRecDepth 65536
set_option maxHeartbeats 2200000
private theorem r7_252_256 : every 252 256 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_257_261 : every 257 261 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_262_266 : every 262 266 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_267_271 : every 267 271 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_272_276 : every 272 276 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_277_281 : every 277 281 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_282_286 : every 282 286 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_287_291 : every 287 291 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_292_296 : every 292 296 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_297_301 : every 297 301 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_302_306 : every 302 306 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_307_311 : every 307 311 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_312_316 : every 312 316 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_317_321 : every 317 321 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_322_326 : every 322 326 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_327_331 : every 327 331 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_332_336 : every 332 336 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_337_341 : every 337 341 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_342_346 : every 342 346 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_347_351 : every 347 351 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_352_356 : every 352 356 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_357_361 : every 357 361 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_362_366 : every 362 366 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_367_371 : every 367 371 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_372_376 : every 372 376 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_377_381 : every 377 381 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_382_386 : every 382 386 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_387_391 : every 387 391 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_392_396 : every 392 396 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_397_399 : every 397 399 (run 8748 418268 22960 209952)=true := by decide +kernel
theorem span7_252_399 : every 252 399 (run 8748 418268 22960 209952)=true := (joinEvery (joinEvery (joinEvery (joinEvery r7_252_256 (joinEvery r7_257_261 r7_262_266)) (joinEvery (joinEvery r7_267_271 r7_272_276) (joinEvery r7_277_281 r7_282_286))) (joinEvery (joinEvery (joinEvery r7_287_291 r7_292_296) (joinEvery r7_297_301 r7_302_306)) (joinEvery (joinEvery r7_307_311 r7_312_316) (joinEvery r7_317_321 r7_322_326)))) (joinEvery (joinEvery (joinEvery r7_327_331 (joinEvery r7_332_336 r7_337_341)) (joinEvery (joinEvery r7_342_346 r7_347_351) (joinEvery r7_352_356 r7_357_361))) (joinEvery (joinEvery (joinEvery r7_362_366 r7_367_371) (joinEvery r7_372_376 r7_377_381)) (joinEvery (joinEvery r7_382_386 r7_387_391) (joinEvery r7_392_396 r7_397_399)))))
end OMA.RankThreeFourSmallCompactTables245212

end

section
/- Independently checked consecutive interval for the compressed two-prime decision. -/
namespace OMA.RankThreeFourSmallCompactTables245212
open OMA.CofactorEulerPair245212 OMA.RankThreeFourSmallCompact245212
open OMA.RankThreeMiddle245212 (joinEvery)
set_option maxRecDepth 65536
set_option maxHeartbeats 2200000
private theorem r7_400_404 : every 400 404 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_405_409 : every 405 409 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_410_414 : every 410 414 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_415_419 : every 415 419 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_420_424 : every 420 424 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_425_429 : every 425 429 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_430_434 : every 430 434 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_435_439 : every 435 439 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_440_444 : every 440 444 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_445_449 : every 445 449 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_450_454 : every 450 454 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_455_459 : every 455 459 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_460_464 : every 460 464 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_465_469 : every 465 469 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_470_474 : every 470 474 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_475_479 : every 475 479 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_480_484 : every 480 484 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_485_489 : every 485 489 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_490_494 : every 490 494 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_495_499 : every 495 499 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_500_504 : every 500 504 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_505_509 : every 505 509 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_510_514 : every 510 514 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_515_519 : every 515 519 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_520_524 : every 520 524 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_525_529 : every 525 529 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_530_534 : every 530 534 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_535_539 : every 535 539 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_540_544 : every 540 544 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_545_549 : every 545 549 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_550_554 : every 550 554 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_555_559 : every 555 559 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_560_564 : every 560 564 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_565_569 : every 565 569 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_570_574 : every 570 574 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_575_579 : every 575 579 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_580_584 : every 580 584 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_585_589 : every 585 589 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_590_594 : every 590 594 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_595_599 : every 595 599 (run 8748 418268 22960 209952)=true := by decide +kernel
theorem span7_400_599 : every 400 599 (run 8748 418268 22960 209952)=true := (joinEvery (joinEvery (joinEvery (joinEvery (joinEvery r7_400_404 r7_405_409) (joinEvery r7_410_414 (joinEvery r7_415_419 r7_420_424))) (joinEvery (joinEvery r7_425_429 r7_430_434) (joinEvery r7_435_439 (joinEvery r7_440_444 r7_445_449)))) (joinEvery (joinEvery (joinEvery r7_450_454 r7_455_459) (joinEvery r7_460_464 (joinEvery r7_465_469 r7_470_474))) (joinEvery (joinEvery r7_475_479 r7_480_484) (joinEvery r7_485_489 (joinEvery r7_490_494 r7_495_499))))) (joinEvery (joinEvery (joinEvery (joinEvery r7_500_504 r7_505_509) (joinEvery r7_510_514 (joinEvery r7_515_519 r7_520_524))) (joinEvery (joinEvery r7_525_529 r7_530_534) (joinEvery r7_535_539 (joinEvery r7_540_544 r7_545_549)))) (joinEvery (joinEvery (joinEvery r7_550_554 r7_555_559) (joinEvery r7_560_564 (joinEvery r7_565_569 r7_570_574))) (joinEvery (joinEvery r7_575_579 r7_580_584) (joinEvery r7_585_589 (joinEvery r7_590_594 r7_595_599))))))
end OMA.RankThreeFourSmallCompactTables245212

end

section
/- Independently checked consecutive interval for the compressed two-prime decision. -/
namespace OMA.RankThreeFourSmallCompactTables245212
open OMA.CofactorEulerPair245212 OMA.RankThreeFourSmallCompact245212
open OMA.RankThreeMiddle245212 (joinEvery)
set_option maxRecDepth 65536
set_option maxHeartbeats 2200000
private theorem r7_600_604 : every 600 604 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_605_609 : every 605 609 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_610_614 : every 610 614 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_615_619 : every 615 619 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_620_624 : every 620 624 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_625_629 : every 625 629 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_630_634 : every 630 634 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_635_639 : every 635 639 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_640_644 : every 640 644 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_645_649 : every 645 649 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_650_654 : every 650 654 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_655_659 : every 655 659 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_660_664 : every 660 664 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_665_669 : every 665 669 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_670_674 : every 670 674 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_675_679 : every 675 679 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_680_684 : every 680 684 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_685_689 : every 685 689 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_690_694 : every 690 694 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_695_699 : every 695 699 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_700_704 : every 700 704 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_705_709 : every 705 709 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_710_714 : every 710 714 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_715_719 : every 715 719 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_720_724 : every 720 724 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_725_729 : every 725 729 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_730_734 : every 730 734 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_735_739 : every 735 739 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_740_744 : every 740 744 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_745_749 : every 745 749 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_750_754 : every 750 754 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_755_759 : every 755 759 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_760_764 : every 760 764 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_765_769 : every 765 769 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_770_774 : every 770 774 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_775_779 : every 775 779 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_780_784 : every 780 784 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_785_789 : every 785 789 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_790_794 : every 790 794 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_795_799 : every 795 799 (run 8748 418268 22960 209952)=true := by decide +kernel
theorem span7_600_799 : every 600 799 (run 8748 418268 22960 209952)=true := (joinEvery (joinEvery (joinEvery (joinEvery (joinEvery r7_600_604 r7_605_609) (joinEvery r7_610_614 (joinEvery r7_615_619 r7_620_624))) (joinEvery (joinEvery r7_625_629 r7_630_634) (joinEvery r7_635_639 (joinEvery r7_640_644 r7_645_649)))) (joinEvery (joinEvery (joinEvery r7_650_654 r7_655_659) (joinEvery r7_660_664 (joinEvery r7_665_669 r7_670_674))) (joinEvery (joinEvery r7_675_679 r7_680_684) (joinEvery r7_685_689 (joinEvery r7_690_694 r7_695_699))))) (joinEvery (joinEvery (joinEvery (joinEvery r7_700_704 r7_705_709) (joinEvery r7_710_714 (joinEvery r7_715_719 r7_720_724))) (joinEvery (joinEvery r7_725_729 r7_730_734) (joinEvery r7_735_739 (joinEvery r7_740_744 r7_745_749)))) (joinEvery (joinEvery (joinEvery r7_750_754 r7_755_759) (joinEvery r7_760_764 (joinEvery r7_765_769 r7_770_774))) (joinEvery (joinEvery r7_775_779 r7_780_784) (joinEvery r7_785_789 (joinEvery r7_790_794 r7_795_799))))))
end OMA.RankThreeFourSmallCompactTables245212

end

section
/- Independently checked consecutive interval for the compressed two-prime decision. -/
namespace OMA.RankThreeFourSmallCompactTables245212
open OMA.CofactorEulerPair245212 OMA.RankThreeFourSmallCompact245212
open OMA.RankThreeMiddle245212 (joinEvery)
set_option maxRecDepth 65536
set_option maxHeartbeats 2200000
private theorem r7_800_804 : every 800 804 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_805_809 : every 805 809 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_810_814 : every 810 814 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_815_819 : every 815 819 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_820_824 : every 820 824 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_825_829 : every 825 829 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_830_834 : every 830 834 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_835_839 : every 835 839 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_840_844 : every 840 844 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_845_849 : every 845 849 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_850_854 : every 850 854 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_855_859 : every 855 859 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_860_864 : every 860 864 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_865_869 : every 865 869 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_870_874 : every 870 874 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_875_879 : every 875 879 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_880_884 : every 880 884 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_885_889 : every 885 889 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_890_894 : every 890 894 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_895_899 : every 895 899 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_900_904 : every 900 904 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_905_909 : every 905 909 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_910_914 : every 910 914 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_915_919 : every 915 919 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_920_924 : every 920 924 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_925_929 : every 925 929 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_930_934 : every 930 934 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_935_939 : every 935 939 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_940_944 : every 940 944 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_945_949 : every 945 949 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_950_954 : every 950 954 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_955_959 : every 955 959 (run 8748 418268 22960 209952)=true := by decide +kernel
private theorem r7_960_964 : every 960 964 (run 8748 418268 22960 209952)=true := by decide +kernel
theorem span7_800_964 : every 800 964 (run 8748 418268 22960 209952)=true := (joinEvery (joinEvery (joinEvery (joinEvery (joinEvery r7_800_804 r7_805_809) (joinEvery r7_810_814 r7_815_819)) (joinEvery (joinEvery r7_820_824 r7_825_829) (joinEvery r7_830_834 r7_835_839))) (joinEvery (joinEvery (joinEvery r7_840_844 r7_845_849) (joinEvery r7_850_854 r7_855_859)) (joinEvery (joinEvery r7_860_864 r7_865_869) (joinEvery r7_870_874 r7_875_879)))) (joinEvery (joinEvery (joinEvery (joinEvery r7_880_884 r7_885_889) (joinEvery r7_890_894 r7_895_899)) (joinEvery (joinEvery r7_900_904 r7_905_909) (joinEvery r7_910_914 r7_915_919))) (joinEvery (joinEvery (joinEvery r7_920_924 r7_925_929) (joinEvery r7_930_934 r7_935_939)) (joinEvery (joinEvery r7_940_944 r7_945_949) (joinEvery r7_950_954 (joinEvery r7_955_959 r7_960_964))))))
end OMA.RankThreeFourSmallCompactTables245212

end
/- Every 4·3^a·p^b·q^d with 5≤p<q and positive exponents fails the OEIS balance. -/
namespace OMA.RankThreeFourSmallSolution245212
open Nat ArithmeticFunction OMA.Smooth245212 OMA.CofactorEulerPair245212
open OMA.RankThreeFourSmallHarmonic245212
open scoped ArithmeticFunction.sigma
open OMA.CofactorEulerPair245212 (checked)
open OMA.Large245212 (moments)
open OMA.RankThreeFourSmallCompactTables245212
open OMA.RankThreeMiddle245212 (joinEvery)

private theorem checked_row {p q a b c L : ℕ} (hp : p.Prime) (hq : q.Prime) (lo : 5≤p) (pq : p<q)
    (bp : 0<b) (cp : 0<c) (cap : OeisA245212.a (4*3^a*p^b*q^c)=(σ 1 (4*3^a*p^b*q^c):ℤ) → p≤L ∨
      OMA.RankThreeFourSmallHarmonic245212.primeCut (17*OMA.Large245212.wt 3 a)
        (7*OMA.Large245212.sig 3 a) (2*(12*OMA.Large245212.tax 3 a))≤L)
    (ok : every 5 L (OMA.RankThreeFourSmallCompact245212.run (4*3^a)
      (17*OMA.Large245212.wt 3 a) (7*OMA.Large245212.sig 3 a) (12*OMA.Large245212.tax 3 a))=true) :
    OeisA245212.a (4*3^a*p^b*q^c)≠(σ 1 (4*3^a*p^b*q^c):ℤ) := by
  intro eqn
  have cop (r : ℕ) (hr : r.Prime) (low : 5≤r) : (4*3^a).Coprime r :=
    (((coprime_primes prime_two hr).mpr (by omega)).pow_left 2).mul_left
      (((coprime_primes (by decide : Nat.Prime 3) hr).mpr (by omega)).pow_left a)
  have c3 : (4:ℕ).Coprime (3^a) := (by decide : Nat.Coprime 4 3).pow_right a
  have base : W 4=17 ∧ σ 1 4=7 ∧ σ 0 4=3 := by decide +kernel
  obtain ⟨y,x⟩:=OMA.Large245212.moments (by decide : Nat.Prime 3) a
  have w : W (4*3^a)=17*OMA.Large245212.wt 3 a := by rw [w_mult.map_mul_of_coprime c3,base.1,x]
  have s : σ 1 (4*3^a)=7*OMA.Large245212.sig 3 a := by rw [isMultiplicative_sigma.map_mul_of_coprime c3,base.2.1,y]
  have t : (4*3^a)*σ 0 (4*3^a)=12*OMA.Large245212.tax 3 a := by
    rw [isMultiplicative_sigma.map_mul_of_coprime c3,base.2.2,sigma_zero_apply_prime_pow (by decide : Nat.Prime 3)]
    unfold OMA.Large245212.tax;ring
  have good:=cop p hp lo
  have other:=cop q hq (by omega)
  have pos : 0<4*3^a := by positivity
  have pm:=first_prime pos hp hq good other pq bp cp eqn
  have lim : p≤L := (cap eqn).elim id (fun bound=>pm.trans (by simpa [w,s,t,mul_assoc] using bound))
  apply OMA.RankThreeFourSmallCompact245212.sound pos hp hq (by omega) good other pq bp cp _ eqn
  apply OMA.CofactorEulerPair245212.checked _ lo lim
  simpa only [w,s,t] using ok


theorem no_least_three {p q a b c : ℕ} (hp : p.Prime) (hq : q.Prime) (lo : 5≤p) (pq : p<q)
    (ap : 0<a) (bp : 0<b) (cp : 0<c) :
    OeisA245212.a (4*3^a*p^b*q^c)≠(σ 1 (4*3^a*p^b*q^c):ℤ) := by
  intro eqn
  have small:=OMA.RankThreeFourSmallOriginal245212.exponent hp hq lo pq eqn
  interval_cases a
  · exact OMA.RankThreeFourSmallOriginal245212.checked_row hp hq lo pq bp cp OMA.RankThreeFourSmallTables245212.at1 eqn
  · exact OMA.RankThreeFourSmallOriginal245212.checked_row hp hq lo pq bp cp OMA.RankThreeFourSmallTables245212.at2 eqn
  · exact OMA.RankThreeFourSmallOriginal245212.checked_row hp hq lo pq bp cp OMA.RankThreeFourSmallTables245212.at3 eqn
  · exact OMA.RankThreeFourSmallOriginal245212.checked_row hp hq lo pq bp cp OMA.RankThreeFourSmallTables245212.at4 eqn
  · exact checked_row hp hq lo pq bp cp (fun _=>Or.inr (by decide +kernel)) span5_5_259 eqn
  · exact checked_row hp hq lo pq bp cp (fun e=>Or.inl (OMA.RankThreeFourSmallOrder245212.first_six hp hq lo pq bp cp e))
      (joinEvery span6_5_259 (joinEvery span6_260_459 span6_460_678)) eqn
  · exact checked_row hp hq lo pq bp cp (fun e=>Or.inl (OMA.RankThreeFourSmallOrder245212.first hp hq lo pq bp cp e))
      (joinEvery span7_5_251 (joinEvery span7_252_399 (joinEvery span7_400_599 (joinEvery span7_600_799 span7_800_964)))) eqn

end OMA.RankThreeFourSmallSolution245212

end

section

/- Three odd primes at dyadic exponent two. A pair of large exponents
already contributes too much weighted divisor mass; each remaining short
prime power gives a two-free-prime cofactor certificate. -/
namespace OMA.RankThreeFourLargePrefix245212
open Nat Finset ArithmeticFunction OMA.Smooth245212 OMA.CofactorEulerPair245212
open scoped ArithmeticFunction.sigma
open OMA.Large245212 (moments)
open OMA.FixedExponents245212 (y_pos)

def test (s b p : ℕ) : Bool :=
  let h:=4*s^b
  let A:=17*OMA.Large245212.wt s b
  let S:=7*OMA.Large245212.sig s b
  let T:=12*OMA.Large245212.tax s b
  decide (A+S≤2*T) && nextPrime h A S T p

def rangeCheck (s p limit : ℕ) := (List.range (limit-1)).all fun i=>test s (i+1) p

private theorem base (s b : ℕ) (hs : s.Prime) (os : 3 ≤ s) :
    W (4*s^b)=17*OMA.Large245212.wt s b ∧ σ 1 (4*s^b)=7*OMA.Large245212.sig s b ∧
    4*s^b*σ 0 (4*s^b)=12*OMA.Large245212.tax s b := by
  obtain ⟨y,x⟩:=OMA.Large245212.moments hs b
  have two : W 4=17 ∧ σ 1 4=7 ∧ σ 0 4=3 := by decide +kernel
  have cop := (((coprime_primes prime_two hs).mpr (by omega)).pow_left 2).pow_right b
  simp only [w_mult.map_mul_of_coprime cop,isMultiplicative_sigma.map_mul_of_coprime cop,
    sigma_zero_apply_prime_pow hs,two.1,two.2.1,two.2.2,x,y,OMA.Large245212.tax]
  constructor
  · trivial
  constructor
  · trivial
  ring

private theorem of_range {s p q a e f L : ℕ} (hs : s.Prime) (hp : p.Prime) (hq : q.Prime)
    (os : 3 ≤ s) (op : 3≤p) (sp : s≠p) (sq : s≠q) (pq : p<q)
    (aa : 0<a) (ee : 0<e) (ff : 0<f) (short : a<L) (cert : rangeCheck s p L=true) :
    OeisA245212.a (4*s^a*p^e*q^f)≠(σ 1 (4*s^a*p^e*q^f):ℤ) := by
  obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero aa.ne'
  have t:=List.all_eq_true.mp cert i (List.mem_range.mpr (by omega))
  simp only [test,Bool.and_eq_true,decide_eq_true_eq] at t
  obtain ⟨w,y,tau⟩:=base s (i+1) hs os
  have cs (r : ℕ) (hr : r.Prime) (lo : 3≤r) (different : s≠r) : (4*s^(i+1)).Coprime r :=
    (((coprime_primes prime_two hr).mpr (by omega)).pow_left 2).mul_left
      (((coprime_primes hs hr).mpr different).pow_left _)
  have s0:=hs.pos
  apply original_at_prime (by positivity) hp hq op (cs p hp op sp) (cs q hq (by omega) sq) pq ee ff
  · simpa only [w,y,tau] using t.1
  · simpa only [w,y,tau] using t.2

private theorem weighted {p q a e f : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 7≤p) (pq : p<q)
    (eqn : OeisA245212.a (4*5^a*p^e*q^f)=(σ 1 (4*5^a*p^e*q^f):ℤ)) :
    17*X 5 (some a)*X p (some e)<24 := by
  let P : Fin 4→ℕ := ![2,5,p,q]
  let E : Fin 4→ℕ := ![2,a,e,f]
  have pr (i : Fin 4) : (P i).Prime := by fin_cases i <;> simp [P,prime_two,show Nat.Prime 5 by decide,hp,hq]
  have inj : P.Injective := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all [P] <;> omega
  have id : total P E=4*5^a*p^e*q^f := by simp [total,P,E,Fin.prod_univ_four,mul_assoc]
  have eq := OMA.Smooth245212.normalized_of_eq P pr inj E (id ▸ eqn)
  have pos : (0:ℚ)<∏ i,Y (P i) (some (E i)) :=
    prod_pos (fun i _ => OMA.FixedExponents245212.y_pos (pr i) _)
  have xprod : (∏ i,X (P i) (some (E i)))<2 := by unfold OMA.Smooth245212.normalized at eq;linarith
  have half : X 2 (some 2)=17/12 := by decide +kernel
  rw [Fin.prod_univ_four] at xprod
  change X 2 (some 2)*X 5 (some a)*X p (some e)*X q (some f)<2 at xprod
  rw [half] at xprod
  have unit : 1≤X q (some f) := le_add_of_nonneg_right (div_nonneg (sub_nonneg.mpr (y_one hq.one_lt _))
    (sub_nonneg.mpr (by exact_mod_cast hq.one_le)))
  have no := mul_le_mul_of_nonneg_left unit (mul_nonneg (x_nonneg (by decide : 1<5) (some a)) (x_nonneg hp.one_lt (some e)))
  nlinarith only [xprod,no]

private theorem rises {p n a : ℕ} (hp : 1<p) (lo : n≤a) : X p (some n)≤X p (some a) := by
  exact add_le_add_right (div_le_div_of_nonneg_right (sub_le_sub_left (y_anti hp lo) 1)
    (sub_nonneg.mpr (by exact_mod_cast hp.le))) 1

theorem close_short_prefix {p q a e f L M : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 7≤p) (pq : p<q)
    (aa : 0<a) (ee : 0<e) (ff : 0<f)
    (above : 24≤17*X 5 (some L)*X p (some M))
    (left : rangeCheck 5 p L=true) (right : rangeCheck p 5 M=true) :
    OeisA245212.a (4*5^a*p^e*q^f)≠(σ 1 (4*5^a*p^e*q^f):ℤ) := by
  by_cases first : a<L
  · exact of_range (by decide : Nat.Prime 5) hp hq (by decide) (by omega) (by omega) (by omega) pq aa ee ff first left
  by_cases second : e<M
  · have kill := of_range hp (by decide : Nat.Prime 5) hq (by omega) (by decide) (by omega) pq.ne (by omega) ee aa ff second right
    rwa [mul_right_comm 4 (p^e) (5^a)] at kill
  intro eqn
  have stop := weighted hp hq op pq eqn
  have mono := mul_le_mul (rises (by decide : 1<5) (by omega : L≤a))
    (rises hp.one_lt (by omega : M≤e)) (x_nonneg hp.one_lt _) (x_nonneg (by decide : 1<5) _)
  nlinarith only [stop,above,mono]


end OMA.RankThreeFourLargePrefix245212

end

section

/- Check short intervals separately and join them without reducing the
boolean arithmetic again. All endpoints are checked in the kernel. -/
namespace OMA.RankThreeFourLargePrefix245212
open OMA.CofactorEulerPair245212

theorem joinEvery {f : ℕ→Bool} {a b c : ℕ}
    (left : every a b f=true) (right : every (b+1) c f=true) :
    every a c f=true := by
  apply List.all_eq_true.mpr
  intro i hi
  obtain ⟨lo,up⟩:=List.mem_range'_1.mp hi
  by_cases e : i≤b
  · exact List.all_eq_true.mp left i (List.mem_range'_1.mpr ⟨lo,by omega⟩)
  · exact List.all_eq_true.mp right i (List.mem_range'_1.mpr ⟨by omega,by omega⟩)

theorem range_from_every {s p L : ℕ}
    (ok : every 1 (L-1) (fun i=>test s i p)=true) : rangeCheck s p L=true := by
  apply List.all_eq_true.mpr
  intro i hi
  have h:=List.mem_range.mp hi
  exact List.all_eq_true.mp ok (i+1) (List.mem_range'_1.mpr ⟨by omega,by omega⟩)

theorem fixedTest {s i p h A S T : ℕ}
    (base : (h,A,S,T)=(4*s^i,17*OMA.Large245212.wt s i,
      7*OMA.Large245212.sig s i,12*OMA.Large245212.tax s i))
    (yes : A+S≤2*T) (pr : p.Prime) (cop : h.Coprime p)
    (gap : A*p<2*T*(p-1))
    (table : every (p+1) (2*T*(p-1)/(2*T*(p-1)-A*p)) (finitePair h A S T p)=true) :
    test s i p=true := by
  simp only [Prod.mk.injEq] at base
  obtain ⟨rfl,rfl,rfl,rfl⟩:=base
  simpa [test,nextPrime,yes,pr,cop,gap,Nat.not_lt_of_ge gap.le] using table

theorem movingTest {s i p h A S T : ℕ}
    (base : (h,A,S,T)=(4*s^i,17*OMA.Large245212.wt s i,
      7*OMA.Large245212.sig s i,12*OMA.Large245212.tax s i))
    (yes : A+S≤2*T) (pr : p.Prime) (cop : h.Coprime p)
    (gap : 2*T*(p-1)<A*p)
    (table : every 1 (2*A/(A*p-2*T*(p-1))) (movingRow A S T p)=true) :
    test s i p=true := by
  simp only [Prod.mk.injEq] at base
  obtain ⟨rfl,rfl,rfl,rfl⟩:=base
  simpa [test,nextPrime,yes,pr,cop,gap] using table

theorem singleTest {s i p : ℕ} (ok : test s i p=true) :
    every i i (fun j=>test s j p)=true := by
  apply List.all_eq_true.mpr
  intro j hj
  obtain ⟨lo,hi⟩:=List.mem_range'_1.mp hj
  simpa [show j=i by omega] using ok

end OMA.RankThreeFourLargePrefix245212

end

section

/- Dyadic exponent two, 5 and 7, with the last prime unbounded. -/
namespace OMA.RankThreeFourLargeSeven245212
open OMA.RankThreeFourLargePrefix245212 OMA.CofactorEulerPair245212 OMA.Smooth245212
open scoped ArithmeticFunction.sigma
set_option maxRecDepth 32000
set_option maxHeartbeats 2200000

private theorem box5_1_0 : every 8 10 (finitePair 20 187 42 120 7)=true := by decide +kernel
theorem test5_1 : test 5 1 7=true :=
  fixedTest (h:=20) (A:=187) (S:=42) (T:=120)
    (by decide +kernel) (by decide) (by decide) (by decide) (by decide) box5_1_0
private theorem box5_2_0 : every 8 19 (finitePair 100 1462 217 900 7)=true := by decide +kernel
theorem test5_2 : test 5 2 7=true :=
  fixedTest (h:=100) (A:=1462) (S:=217) (T:=900)
    (by decide +kernel) (by decide) (by decide) (by decide) (by decide) box5_2_0
private theorem box5_3_0 : every 8 31 (finitePair 500 9962 1092 6000 7)=true := by decide +kernel
theorem test5_3 : test 5 3 7=true :=
  fixedTest (h:=500) (A:=9962) (S:=1092) (T:=6000)
    (by decide +kernel) (by decide) (by decide) (by decide) (by decide) box5_3_0
private theorem box5_4_0 : every 8 53 (finitePair 2500 63087 5467 37500 7)=true := by decide +kernel
theorem test5_4 : test 5 4 7=true :=
  fixedTest (h:=2500) (A:=63087) (S:=5467) (T:=37500)
    (by decide +kernel) (by decide) (by decide) (by decide) (by decide) box5_4_0
private theorem box5_5_0 : every 8 58 (finitePair 12500 381837 27342 225000 7)=true := by decide +kernel
private theorem box5_5_1 : every 59 99 (finitePair 12500 381837 27342 225000 7)=true := by decide +kernel
theorem test5_5 : test 5 5 7=true :=
  fixedTest (h:=12500) (A:=381837) (S:=27342) (T:=225000)
    (by decide +kernel) (by decide) (by decide) (by decide) (by decide) (joinEvery box5_5_0 box5_5_1)
private theorem box5_6_0 : every 8 60 (finitePair 62500 2241212 136717 1312500 7)=true := by decide +kernel
private theorem box5_6_1 : every 61 102 (finitePair 62500 2241212 136717 1312500 7)=true := by decide +kernel
private theorem box5_6_2 : every 103 148 (finitePair 62500 2241212 136717 1312500 7)=true := by decide +kernel
private theorem box5_6_3 : every 149 190 (finitePair 62500 2241212 136717 1312500 7)=true := by decide +kernel
private theorem box5_6_4 : every 191 232 (finitePair 62500 2241212 136717 1312500 7)=true := by decide +kernel
private theorem box5_6_5 : every 233 256 (finitePair 62500 2241212 136717 1312500 7)=true := by decide +kernel
theorem test5_6 : test 5 6 7=true :=
  fixedTest (h:=62500) (A:=2241212) (S:=136717) (T:=1312500)
    (by decide +kernel) (by decide) (by decide) (by decide) (by decide) (joinEvery (joinEvery box5_6_0 (joinEvery box5_6_1 box5_6_2)) (joinEvery box5_6_3 (joinEvery box5_6_4 box5_6_5)))
private theorem box5_7_0 : every 1 27 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_1 : every 28 45 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_2 : every 46 59 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_3 : every 60 72 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_4 : every 73 83 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_5 : every 84 93 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_6 : every 94 103 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_7 : every 104 112 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_8 : every 113 121 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_9 : every 122 129 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_10 : every 130 137 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_11 : every 138 145 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_12 : every 146 152 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_13 : every 153 159 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_14 : every 160 166 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_15 : every 167 173 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_16 : every 174 180 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_17 : every 181 187 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_18 : every 188 194 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_19 : every 195 201 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_20 : every 202 208 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_21 : every 209 215 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_22 : every 216 222 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_23 : every 223 229 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_24 : every 230 235 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_25 : every 236 236 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_26 : every 237 237 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_27 : every 238 238 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_28 : every 239 239 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_29 : every 240 240 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_30 : every 241 241 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_31 : every 242 242 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_32 : every 243 243 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_33 : every 244 244 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_34 : every 245 245 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_35 : every 246 246 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_36 : every 247 247 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_37 : every 248 248 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_38 : every 249 249 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_39 : every 250 250 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_40 : every 251 251 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_41 : every 252 252 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_42 : every 253 253 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_43 : every 254 254 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_44 : every 255 255 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_45 : every 256 256 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_46 : every 257 257 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_47 : every 258 258 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_48 : every 259 259 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_49 : every 260 260 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_50 : every 261 261 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_51 : every 262 262 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_52 : every 263 263 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_53 : every 264 264 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_54 : every 265 265 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_55 : every 266 266 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_56 : every 267 267 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_57 : every 268 268 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_58 : every 269 269 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_59 : every 270 270 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_60 : every 271 271 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_61 : every 272 272 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_62 : every 273 273 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_63 : every 274 274 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_64 : every 275 275 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_65 : every 276 276 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_66 : every 277 277 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_67 : every 278 278 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_68 : every 279 279 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_69 : every 280 280 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_70 : every 281 281 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_71 : every 282 282 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_72 : every 283 283 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_73 : every 284 284 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_74 : every 285 285 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_75 : every 286 286 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_76 : every 287 287 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_77 : every 288 288 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_78 : every 289 289 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_79 : every 290 290 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_80 : every 291 291 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_81 : every 292 292 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_82 : every 293 293 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_83 : every 294 294 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_84 : every 295 295 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_85 : every 296 296 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_86 : every 297 297 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_87 : every 298 298 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_88 : every 299 299 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_89 : every 300 300 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_90 : every 301 301 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_91 : every 302 302 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_92 : every 303 303 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_93 : every 304 304 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_94 : every 305 305 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_95 : every 306 306 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_96 : every 307 307 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_97 : every 308 308 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_98 : every 309 309 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_99 : every 310 310 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_100 : every 311 311 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_101 : every 312 312 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_102 : every 313 313 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_103 : every 314 314 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_104 : every 315 315 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_105 : every 316 316 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_106 : every 317 317 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_107 : every 318 318 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_108 : every 319 319 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_109 : every 320 320 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_110 : every 321 321 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_111 : every 322 322 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_112 : every 323 323 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_113 : every 324 324 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_114 : every 325 325 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_115 : every 326 326 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_116 : every 327 327 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_117 : every 328 328 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_118 : every 329 329 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_119 : every 330 330 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_120 : every 331 331 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_121 : every 332 332 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_122 : every 333 333 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_123 : every 334 334 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_124 : every 335 335 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_125 : every 336 336 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_126 : every 337 337 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_127 : every 338 338 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_128 : every 339 339 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_129 : every 340 340 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_130 : every 341 341 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_131 : every 342 342 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_132 : every 343 343 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_133 : every 344 344 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_134 : every 345 345 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_135 : every 346 346 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_136 : every 347 347 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_137 : every 348 348 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_138 : every 349 349 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_139 : every 350 350 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_140 : every 351 351 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_141 : every 352 352 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_142 : every 353 353 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_143 : every 354 354 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_144 : every 355 355 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_145 : every 356 356 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_146 : every 357 357 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_147 : every 358 358 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_148 : every 359 359 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_149 : every 360 360 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_150 : every 361 361 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_151 : every 362 362 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_152 : every 363 363 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_153 : every 364 364 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_154 : every 365 365 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_155 : every 366 366 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_156 : every 367 367 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_157 : every 368 368 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_158 : every 369 369 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_159 : every 370 370 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_160 : every 371 371 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_161 : every 372 372 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_162 : every 373 373 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_163 : every 374 374 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_164 : every 375 375 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_165 : every 376 376 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_166 : every 377 377 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_167 : every 378 378 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_168 : every 379 379 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_169 : every 380 380 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_170 : every 381 381 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_171 : every 382 382 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_172 : every 383 383 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_173 : every 384 384 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_174 : every 385 385 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_175 : every 386 386 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_176 : every 387 387 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_177 : every 388 388 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_178 : every 389 389 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_179 : every 390 390 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_180 : every 391 391 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_181 : every 392 392 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_182 : every 393 393 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_183 : every 394 394 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_184 : every 395 395 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_185 : every 396 396 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_186 : every 397 397 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_187 : every 398 398 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_188 : every 399 399 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_189 : every 400 400 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_190 : every 401 401 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_191 : every 402 402 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_192 : every 403 403 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_193 : every 404 404 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
private theorem box5_7_194 : every 405 405 (movingRow 12866212 683592 7500000 7)=true := by decide +kernel
theorem test5_7 : test 5 7 7=true :=
  movingTest (h:=312500) (A:=12866212) (S:=683592) (T:=7500000)
    (by decide +kernel) (by decide) (by decide) (by decide) (by decide) (joinEvery (joinEvery (joinEvery (joinEvery (joinEvery (joinEvery (joinEvery box5_7_0 (joinEvery box5_7_1 box5_7_2)) (joinEvery box5_7_3 (joinEvery box5_7_4 box5_7_5))) (joinEvery (joinEvery box5_7_6 (joinEvery box5_7_7 box5_7_8)) (joinEvery box5_7_9 (joinEvery box5_7_10 box5_7_11)))) (joinEvery (joinEvery (joinEvery box5_7_12 (joinEvery box5_7_13 box5_7_14)) (joinEvery box5_7_15 (joinEvery box5_7_16 box5_7_17))) (joinEvery (joinEvery box5_7_18 (joinEvery box5_7_19 box5_7_20)) (joinEvery box5_7_21 (joinEvery box5_7_22 box5_7_23))))) (joinEvery (joinEvery (joinEvery (joinEvery box5_7_24 (joinEvery box5_7_25 box5_7_26)) (joinEvery box5_7_27 (joinEvery box5_7_28 box5_7_29))) (joinEvery (joinEvery box5_7_30 (joinEvery box5_7_31 box5_7_32)) (joinEvery box5_7_33 (joinEvery box5_7_34 box5_7_35)))) (joinEvery (joinEvery (joinEvery box5_7_36 (joinEvery box5_7_37 box5_7_38)) (joinEvery box5_7_39 (joinEvery box5_7_40 box5_7_41))) (joinEvery (joinEvery box5_7_42 (joinEvery box5_7_43 box5_7_44)) (joinEvery box5_7_45 (joinEvery box5_7_46 box5_7_47)))))) (joinEvery (joinEvery (joinEvery (joinEvery (joinEvery box5_7_48 (joinEvery box5_7_49 box5_7_50)) (joinEvery box5_7_51 (joinEvery box5_7_52 box5_7_53))) (joinEvery (joinEvery box5_7_54 (joinEvery box5_7_55 box5_7_56)) (joinEvery box5_7_57 (joinEvery box5_7_58 box5_7_59)))) (joinEvery (joinEvery (joinEvery box5_7_60 (joinEvery box5_7_61 box5_7_62)) (joinEvery box5_7_63 (joinEvery box5_7_64 box5_7_65))) (joinEvery (joinEvery box5_7_66 (joinEvery box5_7_67 box5_7_68)) (joinEvery box5_7_69 (joinEvery box5_7_70 box5_7_71))))) (joinEvery (joinEvery (joinEvery (joinEvery box5_7_72 (joinEvery box5_7_73 box5_7_74)) (joinEvery box5_7_75 (joinEvery box5_7_76 box5_7_77))) (joinEvery (joinEvery box5_7_78 (joinEvery box5_7_79 box5_7_80)) (joinEvery box5_7_81 (joinEvery box5_7_82 box5_7_83)))) (joinEvery (joinEvery (joinEvery box5_7_84 (joinEvery box5_7_85 box5_7_86)) (joinEvery box5_7_87 (joinEvery box5_7_88 box5_7_89))) (joinEvery (joinEvery box5_7_90 (joinEvery box5_7_91 box5_7_92)) (joinEvery (joinEvery box5_7_93 box5_7_94) (joinEvery box5_7_95 box5_7_96))))))) (joinEvery (joinEvery (joinEvery (joinEvery (joinEvery (joinEvery box5_7_97 (joinEvery box5_7_98 box5_7_99)) (joinEvery box5_7_100 (joinEvery box5_7_101 box5_7_102))) (joinEvery (joinEvery box5_7_103 (joinEvery box5_7_104 box5_7_105)) (joinEvery box5_7_106 (joinEvery box5_7_107 box5_7_108)))) (joinEvery (joinEvery (joinEvery box5_7_109 (joinEvery box5_7_110 box5_7_111)) (joinEvery box5_7_112 (joinEvery box5_7_113 box5_7_114))) (joinEvery (joinEvery box5_7_115 (joinEvery box5_7_116 box5_7_117)) (joinEvery box5_7_118 (joinEvery box5_7_119 box5_7_120))))) (joinEvery (joinEvery (joinEvery (joinEvery box5_7_121 (joinEvery box5_7_122 box5_7_123)) (joinEvery box5_7_124 (joinEvery box5_7_125 box5_7_126))) (joinEvery (joinEvery box5_7_127 (joinEvery box5_7_128 box5_7_129)) (joinEvery box5_7_130 (joinEvery box5_7_131 box5_7_132)))) (joinEvery (joinEvery (joinEvery box5_7_133 (joinEvery box5_7_134 box5_7_135)) (joinEvery box5_7_136 (joinEvery box5_7_137 box5_7_138))) (joinEvery (joinEvery box5_7_139 (joinEvery box5_7_140 box5_7_141)) (joinEvery (joinEvery box5_7_142 box5_7_143) (joinEvery box5_7_144 box5_7_145)))))) (joinEvery (joinEvery (joinEvery (joinEvery (joinEvery box5_7_146 (joinEvery box5_7_147 box5_7_148)) (joinEvery box5_7_149 (joinEvery box5_7_150 box5_7_151))) (joinEvery (joinEvery box5_7_152 (joinEvery box5_7_153 box5_7_154)) (joinEvery box5_7_155 (joinEvery box5_7_156 box5_7_157)))) (joinEvery (joinEvery (joinEvery box5_7_158 (joinEvery box5_7_159 box5_7_160)) (joinEvery box5_7_161 (joinEvery box5_7_162 box5_7_163))) (joinEvery (joinEvery box5_7_164 (joinEvery box5_7_165 box5_7_166)) (joinEvery box5_7_167 (joinEvery box5_7_168 box5_7_169))))) (joinEvery (joinEvery (joinEvery (joinEvery box5_7_170 (joinEvery box5_7_171 box5_7_172)) (joinEvery box5_7_173 (joinEvery box5_7_174 box5_7_175))) (joinEvery (joinEvery box5_7_176 (joinEvery box5_7_177 box5_7_178)) (joinEvery box5_7_179 (joinEvery box5_7_180 box5_7_181)))) (joinEvery (joinEvery (joinEvery box5_7_182 (joinEvery box5_7_183 box5_7_184)) (joinEvery box5_7_185 (joinEvery box5_7_186 box5_7_187))) (joinEvery (joinEvery box5_7_188 (joinEvery box5_7_189 box5_7_190)) (joinEvery (joinEvery box5_7_191 box5_7_192) (joinEvery box5_7_193 box5_7_194))))))))
private theorem box5_8_0 : every 1 29 (movingRow 72631837 3417967 42187500 7)=true := by decide +kernel
private theorem box5_8_1 : every 30 42 (movingRow 72631837 3417967 42187500 7)=true := by decide +kernel
private theorem box5_8_2 : every 43 48 (movingRow 72631837 3417967 42187500 7)=true := by decide +kernel
private theorem box5_8_3 : every 49 53 (movingRow 72631837 3417967 42187500 7)=true := by decide +kernel
private theorem box5_8_4 : every 54 58 (movingRow 72631837 3417967 42187500 7)=true := by decide +kernel
private theorem box5_8_5 : every 59 63 (movingRow 72631837 3417967 42187500 7)=true := by decide +kernel
private theorem box5_8_6 : every 64 66 (movingRow 72631837 3417967 42187500 7)=true := by decide +kernel
theorem test5_8 : test 5 8 7=true :=
  movingTest (h:=1562500) (A:=72631837) (S:=3417967) (T:=42187500)
    (by decide +kernel) (by decide) (by decide) (by decide) (by decide) (joinEvery (joinEvery box5_8_0 (joinEvery box5_8_1 box5_8_2)) (joinEvery (joinEvery box5_8_3 box5_8_4) (joinEvery box5_8_5 box5_8_6)))
private theorem box5_9_0 : every 1 25 (movingRow 404663087 17089842 234375000 7)=true := by decide +kernel
private theorem box5_9_1 : every 26 33 (movingRow 404663087 17089842 234375000 7)=true := by decide +kernel
private theorem box5_9_2 : every 34 40 (movingRow 404663087 17089842 234375000 7)=true := by decide +kernel
theorem test5_9 : test 5 9 7=true :=
  movingTest (h:=7812500) (A:=404663087) (S:=17089842) (T:=234375000)
    (by decide +kernel) (by decide) (by decide) (by decide) (by decide) (joinEvery box5_9_0 (joinEvery box5_9_1 box5_9_2))
private theorem box5_10_0 : every 1 22 (movingRow 2230834962 85449217 1289062500 7)=true := by decide +kernel
private theorem box5_10_1 : every 23 30 (movingRow 2230834962 85449217 1289062500 7)=true := by decide +kernel
theorem test5_10 : test 5 10 7=true :=
  movingTest (h:=39062500) (A:=2230834962) (S:=85449217) (T:=1289062500)
    (by decide +kernel) (by decide) (by decide) (by decide) (by decide) (joinEvery box5_10_0 box5_10_1)
private theorem box5_11_0 : every 1 20 (movingRow 12191772462 427246092 7031250000 7)=true := by decide +kernel
private theorem box5_11_1 : every 21 25 (movingRow 12191772462 427246092 7031250000 7)=true := by decide +kernel
theorem test5_11 : test 5 11 7=true :=
  movingTest (h:=195312500) (A:=12191772462) (S:=427246092) (T:=7031250000)
    (by decide +kernel) (by decide) (by decide) (by decide) (by decide) (joinEvery box5_11_0 box5_11_1)
theorem range5 : rangeCheck 5 7 12=true :=
  range_from_every (joinEvery (joinEvery (joinEvery (singleTest test5_1) (singleTest test5_2)) (joinEvery (singleTest test5_3) (joinEvery (singleTest test5_4) (singleTest test5_5)))) (joinEvery (joinEvery (singleTest test5_6) (joinEvery (singleTest test5_7) (singleTest test5_8))) (joinEvery (singleTest test5_9) (joinEvery (singleTest test5_10) (singleTest test5_11)))))
private theorem box7_1_0 : every 6 19 (finitePair 28 255 56 168 5)=true := by decide +kernel
theorem test7_1 : test 7 1 5=true :=
  fixedTest (h:=28) (A:=255) (S:=56) (T:=168)
    (by decide +kernel) (by decide) (by decide) (by decide) (by decide) box7_1_0
private theorem box7_2_0 : every 6 41 (finitePair 196 2754 399 1764 5)=true := by decide +kernel
theorem test7_2 : test 7 2 5=true :=
  fixedTest (h:=196) (A:=2754) (S:=399) (T:=1764)
    (by decide +kernel) (by decide) (by decide) (by decide) (by decide) box7_2_0
private theorem box7_3_0 : every 6 52 (finitePair 1372 26078 2800 16464 5)=true := by decide +kernel
private theorem box7_3_1 : every 53 92 (finitePair 1372 26078 2800 16464 5)=true := by decide +kernel
private theorem box7_3_2 : every 93 99 (finitePair 1372 26078 2800 16464 5)=true := by decide +kernel
theorem test7_3 : test 7 3 5=true :=
  fixedTest (h:=1372) (A:=26078) (S:=2800) (T:=16464)
    (by decide +kernel) (by decide) (by decide) (by decide) (by decide) (joinEvery box7_3_0 (joinEvery box7_3_1 box7_3_2))
private theorem box7_4_0 : every 6 52 (finitePair 9604 230163 19607 144060 5)=true := by decide +kernel
private theorem box7_4_1 : every 53 88 (finitePair 9604 230163 19607 144060 5)=true := by decide +kernel
private theorem box7_4_2 : every 89 130 (finitePair 9604 230163 19607 144060 5)=true := by decide +kernel
private theorem box7_4_3 : every 131 166 (finitePair 9604 230163 19607 144060 5)=true := by decide +kernel
private theorem box7_4_4 : every 167 198 (finitePair 9604 230163 19607 144060 5)=true := by decide +kernel
private theorem box7_4_5 : every 199 240 (finitePair 9604 230163 19607 144060 5)=true := by decide +kernel
private theorem box7_4_6 : every 241 276 (finitePair 9604 230163 19607 144060 5)=true := by decide +kernel
private theorem box7_4_7 : every 277 312 (finitePair 9604 230163 19607 144060 5)=true := by decide +kernel
private theorem box7_4_8 : every 313 348 (finitePair 9604 230163 19607 144060 5)=true := by decide +kernel
private theorem box7_4_9 : every 349 378 (finitePair 9604 230163 19607 144060 5)=true := by decide +kernel
private theorem box7_4_10 : every 379 400 (finitePair 9604 230163 19607 144060 5)=true := by decide +kernel
private theorem box7_4_11 : every 401 430 (finitePair 9604 230163 19607 144060 5)=true := by decide +kernel
private theorem box7_4_12 : every 431 448 (finitePair 9604 230163 19607 144060 5)=true := by decide +kernel
private theorem box7_4_13 : every 449 466 (finitePair 9604 230163 19607 144060 5)=true := by decide +kernel
private theorem box7_4_14 : every 467 490 (finitePair 9604 230163 19607 144060 5)=true := by decide +kernel
private theorem box7_4_15 : every 491 508 (finitePair 9604 230163 19607 144060 5)=true := by decide +kernel
private theorem box7_4_16 : every 509 540 (finitePair 9604 230163 19607 144060 5)=true := by decide +kernel
private theorem box7_4_17 : every 541 562 (finitePair 9604 230163 19607 144060 5)=true := by decide +kernel
private theorem box7_4_18 : every 563 576 (finitePair 9604 230163 19607 144060 5)=true := by decide +kernel
private theorem box7_4_19 : every 577 598 (finitePair 9604 230163 19607 144060 5)=true := by decide +kernel
private theorem box7_4_20 : every 599 612 (finitePair 9604 230163 19607 144060 5)=true := by decide +kernel
private theorem box7_4_21 : every 613 630 (finitePair 9604 230163 19607 144060 5)=true := by decide +kernel
private theorem box7_4_22 : every 631 646 (finitePair 9604 230163 19607 144060 5)=true := by decide +kernel
private theorem box7_4_23 : every 647 658 (finitePair 9604 230163 19607 144060 5)=true := by decide +kernel
private theorem box7_4_24 : every 659 672 (finitePair 9604 230163 19607 144060 5)=true := by decide +kernel
private theorem box7_4_25 : every 673 682 (finitePair 9604 230163 19607 144060 5)=true := by decide +kernel
private theorem box7_4_26 : every 683 692 (finitePair 9604 230163 19607 144060 5)=true := by decide +kernel
theorem test7_4 : test 7 4 5=true :=
  fixedTest (h:=9604) (A:=230163) (S:=19607) (T:=144060)
    (by decide +kernel) (by decide) (by decide) (by decide) (by decide) (joinEvery (joinEvery (joinEvery (joinEvery box7_4_0 (joinEvery box7_4_1 box7_4_2)) (joinEvery box7_4_3 (joinEvery box7_4_4 box7_4_5))) (joinEvery (joinEvery box7_4_6 (joinEvery box7_4_7 box7_4_8)) (joinEvery (joinEvery box7_4_9 box7_4_10) (joinEvery box7_4_11 box7_4_12)))) (joinEvery (joinEvery (joinEvery box7_4_13 (joinEvery box7_4_14 box7_4_15)) (joinEvery (joinEvery box7_4_16 box7_4_17) (joinEvery box7_4_18 box7_4_19))) (joinEvery (joinEvery box7_4_20 (joinEvery box7_4_21 box7_4_22)) (joinEvery (joinEvery box7_4_23 box7_4_24) (joinEvery box7_4_25 box7_4_26)))))
private theorem box7_5_0 : every 1 29 (movingRow 1944477 137256 1210104 5)=true := by decide +kernel
private theorem box7_5_1 : every 30 52 (movingRow 1944477 137256 1210104 5)=true := by decide +kernel
private theorem box7_5_2 : every 53 61 (movingRow 1944477 137256 1210104 5)=true := by decide +kernel
private theorem box7_5_3 : every 62 66 (movingRow 1944477 137256 1210104 5)=true := by decide +kernel
private theorem box7_5_4 : every 67 70 (movingRow 1944477 137256 1210104 5)=true := by decide +kernel
private theorem box7_5_5 : every 71 74 (movingRow 1944477 137256 1210104 5)=true := by decide +kernel
private theorem box7_5_6 : every 75 78 (movingRow 1944477 137256 1210104 5)=true := by decide +kernel
private theorem box7_5_7 : every 79 82 (movingRow 1944477 137256 1210104 5)=true := by decide +kernel
private theorem box7_5_8 : every 83 86 (movingRow 1944477 137256 1210104 5)=true := by decide +kernel
private theorem box7_5_9 : every 87 89 (movingRow 1944477 137256 1210104 5)=true := by decide +kernel
private theorem box7_5_10 : every 90 92 (movingRow 1944477 137256 1210104 5)=true := by decide +kernel
private theorem box7_5_11 : every 93 93 (movingRow 1944477 137256 1210104 5)=true := by decide +kernel
theorem test7_5 : test 7 5 5=true :=
  movingTest (h:=67228) (A:=1944477) (S:=137256) (T:=1210104)
    (by decide +kernel) (by decide) (by decide) (by decide) (by decide) (joinEvery (joinEvery (joinEvery box7_5_0 (joinEvery box7_5_1 box7_5_2)) (joinEvery box7_5_3 (joinEvery box7_5_4 box7_5_5))) (joinEvery (joinEvery box7_5_6 (joinEvery box7_5_7 box7_5_8)) (joinEvery box7_5_9 (joinEvery box7_5_10 box7_5_11))))
private theorem box7_6_0 : every 1 30 (movingRow 15944708 960799 9882516 5)=true := by decide +kernel
private theorem box7_6_1 : every 31 38 (movingRow 15944708 960799 9882516 5)=true := by decide +kernel
private theorem box7_6_2 : every 39 45 (movingRow 15944708 960799 9882516 5)=true := by decide +kernel
private theorem box7_6_3 : every 46 48 (movingRow 15944708 960799 9882516 5)=true := by decide +kernel
theorem test7_6 : test 7 6 5=true :=
  movingTest (h:=470596) (A:=15944708) (S:=960799) (T:=9882516)
    (by decide +kernel) (by decide) (by decide) (by decide) (by decide) (joinEvery (joinEvery box7_6_0 box7_6_1) (joinEvery box7_6_2 box7_6_3))
private theorem box7_7_0 : every 1 24 (movingRow 127946556 6725600 79060128 5)=true := by decide +kernel
private theorem box7_7_1 : every 25 32 (movingRow 127946556 6725600 79060128 5)=true := by decide +kernel
private theorem box7_7_2 : every 33 35 (movingRow 127946556 6725600 79060128 5)=true := by decide +kernel
theorem test7_7 : test 7 7 5=true :=
  movingTest (h:=3294172) (A:=127946556) (S:=6725600) (T:=79060128)
    (by decide +kernel) (by decide) (by decide) (by decide) (by decide) (joinEvery box7_7_0 (joinEvery box7_7_1 box7_7_2))
private theorem box7_8_0 : every 1 22 (movingRow 1009961109 47079207 622598508 5)=true := by decide +kernel
private theorem box7_8_1 : every 23 29 (movingRow 1009961109 47079207 622598508 5)=true := by decide +kernel
theorem test7_8 : test 7 8 5=true :=
  movingTest (h:=23059204) (A:=1009961109) (S:=47079207) (T:=622598508)
    (by decide +kernel) (by decide) (by decide) (by decide) (by decide) (joinEvery box7_8_0 box7_8_1)
private theorem box7_9_0 : every 1 20 (movingRow 7870074299 329554456 4842432840 5)=true := by decide +kernel
private theorem box7_9_1 : every 21 25 (movingRow 7870074299 329554456 4842432840 5)=true := by decide +kernel
theorem test7_9 : test 7 9 5=true :=
  movingTest (h:=161414428) (A:=7870074299) (S:=329554456) (T:=4842432840)
    (by decide +kernel) (by decide) (by decide) (by decide) (by decide) (joinEvery box7_9_0 box7_9_1)
private theorem box7_10_0 : every 1 19 (movingRow 60692945862 2306881199 37286732868 5)=true := by decide +kernel
private theorem box7_10_1 : every 20 23 (movingRow 60692945862 2306881199 37286732868 5)=true := by decide +kernel
theorem test7_10 : test 7 10 5=true :=
  movingTest (h:=1129900996) (A:=60692945862) (S:=2306881199) (T:=37286732868)
    (by decide +kernel) (by decide) (by decide) (by decide) (by decide) (joinEvery box7_10_0 box7_10_1)
private theorem box7_11_0 : every 1 18 (movingRow 464067601434 16148168400 284735050992 5)=true := by decide +kernel
private theorem box7_11_1 : every 19 21 (movingRow 464067601434 16148168400 284735050992 5)=true := by decide +kernel
theorem test7_11 : test 7 11 5=true :=
  movingTest (h:=7909306972) (A:=464067601434) (S:=16148168400) (T:=284735050992)
    (by decide +kernel) (by decide) (by decide) (by decide) (by decide) (joinEvery box7_11_0 box7_11_1)
theorem range7 : rangeCheck 7 5 12=true :=
  range_from_every (joinEvery (joinEvery (joinEvery (singleTest test7_1) (singleTest test7_2)) (joinEvery (singleTest test7_3) (joinEvery (singleTest test7_4) (singleTest test7_5)))) (joinEvery (joinEvery (singleTest test7_6) (joinEvery (singleTest test7_7) (singleTest test7_8))) (joinEvery (singleTest test7_9) (joinEvery (singleTest test7_10) (singleTest test7_11)))))
theorem all_last {r a b c : ℕ} (rp : r.Prime) (order : 7<r)
    (ap : 0<a) (bp : 0<b) (cp : 0<c) :
    OeisA245212.a (4*5^a*7^b*r^c)≠(σ 1 (4*5^a*7^b*r^c):ℤ) :=
  close_short_prefix (by decide) rp (by decide) order ap bp cp
    (by decide +kernel : 24≤17*X 5 (some 12)*X 7 (some 12)) range5 range7
end OMA.RankThreeFourLargeSeven245212

end

section

namespace OMA.PrefixLeaf245212
open OMA.Large245212 OMA.Smooth245212 ArithmeticFunction
open scoped ArithmeticFunction.sigma
open OMA.Large245212 (moments)
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

end

section

/- Check all exponents at a fixed terminal prime using the signed
reverse digit. Arithmetic on the cofactor uses closed prime-power sums. -/
namespace OMA.RankThreeLast245212
open OMA.Smooth245212 OMA.Large245212 OMA.ReverseDigit245212
open scoped ArithmeticFunction.sigma

def floorQuot (x y : ℤ) := if y<0 then (-x)/(-y) else x/y

private theorem floor_correct (x y : ℤ) : ⌊(x:ℚ)/(y:ℚ)⌋=floorQuot x y := by
  cases y with
  | ofNat n => simp [floorQuot,Rat.floor_intCast_div_natCast]
  | negSucc n =>
    have h : (Int.negSucc n:ℤ)=-((n+1:ℕ):ℤ) := by omega
    rw [h]
    have y : (0:ℤ)<(n+1:ℕ) := by omega
    simp only [floorQuot,neg_lt_zero.mpr y,if_true,neg_neg]
    rw [Int.cast_neg,Int.cast_natCast,div_neg,← neg_div,← Int.cast_neg,Rat.floor_intCast_div_natCast]

def len (r A S T : ℕ) : ℕ := (floorQuot
  ((r:ℤ)*(((r:ℤ)-1)*S-A)) (((r:ℤ)-1)*(2*(T:ℤ)*((r:ℤ)-1)-r*A))).toNat

theorem length_eq {r m e : ℕ} (hm : 0 < m) (rp : r.Prime) (ro : r≠2) (cop : m.Coprime r)
    (hit : OeisA245212.a (m*r^e)=(σ 1 (m*r^e):ℤ)) :
    len r (W m) (σ 1 m) (m*(σ 0 m))=e+1 := by
  have fl := (recover hm rp ro cop hit).2.2
  let C : ℤ := (r:ℤ)*(((r:ℤ)-1)*(σ 1 m:ℤ)-W m)
  let D : ℤ := ((r:ℤ)-1)*(2*(m*(σ 0 m):ℕ)*((r:ℤ)-1)-r*(W m:ℤ))
  have c : (C:ℚ)=numerator r (W m) (σ 1 m) := by simp [C,numerator]
  have d : (D:ℚ)=denominator r (W m) (m*(σ 0 m:ℚ)) := by simp [D,denominator]
  change ⌊numerator r (W m) (σ 1 m)/denominator r (W m) (m*(σ 0 m:ℚ))⌋=_ at fl
  rw [← c,← d,floor_correct] at fl
  change (floorQuot C D).toNat=_
  omega

def reject (r A S T cap : ℕ) : Bool :=
  if (A+S)%r≠0 then true else
    let k := len r A S T
    if k<2 ∨ cap+1<k then true else
      let e := k-1
      if Nat.log 2 (A+r*S)<e then true else
        A*wt r e+S*sig r e != 2*T*OMA.Large245212.tax r e

open OMA.Large245212 (moments)

theorem reject_sound {r m e cap : ℕ} (hm : 0 < m) (rp : r.Prime) (ro : r≠2)
    (cop : m.Coprime r) (ep : 0<e) (bound : e≤cap)
    (hit : OeisA245212.a (m*r^e)=(σ 1 (m*r^e):ℤ)) :
    reject r (W m) (σ 1 m) (m*(σ 0 m)) cap=false := by
  have dv := OMA.OddCofactor245212.last_dvd hm rp cop ep hit
  have recovered := length_eq hm rp ro cop hit
  have d := OMA.PrimePowerDiv245212.cofactor_bound hm rp ro cop e hit
  have le := Int.natAbs_sub_le (W m:ℤ) (((r:ℤ)-1)*(σ 1 m:ℤ))
  rw [Int.natAbs_mul] at le
  have rg := rp.one_lt
  have sub : (r:ℤ)-1=((r-1:ℕ):ℤ) := by omega
  rw [sub] at le d
  simp only [Int.natAbs_natCast] at le
  have ub : r^e≤W m+r*(σ 1 m) := (d.trans le).trans (by gcongr; omega)
  have logb := Nat.le_log_of_pow_le (by decide : 1<2) ((Nat.pow_le_pow_left rp.two_le e).trans ub)
  have b := OMA.Abundance245212.balance (mul_ne_zero hm.ne' (pow_ne_zero _ rp.ne_zero)) hit
  rw [w_mult.map_mul_of_coprime (cop.pow_right e),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (cop.pow_right e),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (cop.pow_right e),
    ArithmeticFunction.sigma_zero_apply_prime_pow rp] at b
  obtain ⟨ss,ww⟩ := OMA.Large245212.moments rp e
  have match_eq : W m*wt r e+(σ 1 m)*sig r e=2*(m*(σ 0 m))*OMA.Large245212.tax r e := by
    rw [ss,ww,OMA.Large245212.tax]; nlinarith only [b]
  simp [reject,Nat.mod_eq_zero_of_dvd dv,recovered,show ¬ e+1<2 by omega,
    show ¬cap+1<e+1 by omega,not_lt.mpr logb,match_eq]

theorem prefix_false {p q r a b c cap : ℕ} (pp : p.Prime) (qp : q.Prime) (rp : r.Prime)
    (po : p≠2) (qo : q≠2) (ro : r≠2) (pq : p≠q) (pr : p≠r) (qr : q≠r)
    (cp : 0<c) (cb : c≤cap)
    (hit : OeisA245212.a (2*p^a*q^b*r^c)=(σ 1 (2*p^a*q^b*r^c):ℤ)) :
    reject r (5*wt p a*wt q b) (3*sig p a*sig q b) (4*OMA.Large245212.tax p a*OMA.Large245212.tax q b) cap=false := by
  have cop : (2*p^a*q^b).Coprime r :=
    (((Nat.coprime_primes Nat.prime_two rp).mpr ro.symm).mul_left
      (((Nat.coprime_primes pp rp).mpr pr).pow_left a)).mul_left
      (((Nat.coprime_primes qp rp).mpr qr).pow_left b)
  have pos : 0<2*p^a*q^b := by have := pp.pos; have := qp.pos; positivity
  have z := reject_sound pos rp ro cop cp cb hit
  have ⟨w,s,t⟩ := OMA.PrefixLeaf245212.triple Nat.prime_two pp qp po.symm qo.symm pq 1 a b
  simp only [pow_one] at w s t
  rw [w,s,t] at z
  exact z
end OMA.RankThreeLast245212

end

section

/- Switch the four local moments one at a time.  After clearing the
denominators, the score of every partially rounded model is an integer. -/
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

end

section

/- Detect an impossible mixed score by integer separation; control its
denominator by the product of the unrounded prime powers. -/
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

end

section

/- Rounding one local factor cannot preserve the exact score at an odd
solution.  Its derivative is the nonzero cofactor divisor moment. -/
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

end

section

/- From an odd solution, extract its least prime-power scale repeatedly.
Four removals bound its total size without an a priori bound on exponents. -/
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

end

section

/- Integer-only final step in the A245212 exponent height bound. -/
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

end

section

/- Effective four-factor height allowing a dyadic prime power of bounded size.
The singleton rounding proof only needs its selected prime to be odd. A small
dyadic power meets the peeling bound directly. -/
namespace OMA.GuardedHeight245212
open OMA.Smooth245212 OMA.Height245212 Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma Function
noncomputable section
variable (p e : Fin 4 → ℕ)

private theorem singleton_at (hp : ∀ i,(p i).Prime) 
    (inj : Function.Injective p) (sol : OeisA245212.a (total p e)=(σ 1 (total p e):ℤ))
    (i : Fin 4) (odd : p i ≠ 2) : scoreM p e {i}≠normalized p e := by
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
  have nz := OMA.PrimePowerDiv245212.nonzero mpos (hp i) odd mpi (e i) (rep ▸ sol)
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


private theorem guarded_peel {B E : ℕ} (prime : ∀ i,(p i).Prime) (small_two : ∀ i, p i = 2 → p i^e i ≤ B^(2*B))
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
    have no : p i ≠ 2 := fun h => ((le_max_left _ _).trans_lt (fail i (mem_singleton_self i))).not_ge (small_two i h)
    exact singleton_at p e prime inj sol i no (same.trans norm.symm)


private theorem guarded_total {B E : ℕ} (prime : ∀ i,(p i).Prime) (small_two : ∀ i, p i = 2 → p i^e i ≤ B^(2*B))
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
      obtain ⟨i,hi,sm⟩ := guarded_peel p e prime small_two pos inj bp be sol s (card_pos.mp (by omega))
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



/-- The even prime is allowed when its power is at most the first peeling threshold. -/
theorem max_power {B : ℕ} (prime : ∀ i,(p i).Prime) (small_two : ∀ i, p i = 2 → p i^e i ≤ B^(2*B))
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
    _ ≤ _ := guarded_total p e prime small_two pos inj bp be sol


end
end OMA.GuardedHeight245212

end

section

/- Pick two bounded exponents in a three-prime dyadic solution. When
a group contains only large prime powers the integer rounding error is
below one denominator unit. The product of the other two Euler factors
controls the sign, allowing much shorter thresholds than a scalar bound. -/
namespace OMA.RankThreeFourLargeSmall245212
open Finset Nat OMA.Smooth245212 OMA.Height245212
open scoped ArithmeticFunction.sigma

def height (B : ℕ) := max 2 (OMA.HeightLog245212.ceiling 4 B)
def budget (B : ℕ) := 4*coefficientBound B (height B)
def first (B p : ℕ) := Nat.log p (budget B)
def next (B p e q r : ℕ) := max (Nat.log q (budget B*p^e)) (4*(r-1)/(e+1))
def seed (B p q r : ℕ) := 4*(p-1)<(first B q+2)*(first B r+2)

abbrev PP (p q r : ℕ) : Fin 4 → ℕ := ![2,p,q,r]
abbrev EE (a b c : ℕ) : Fin 4 → ℕ := ![2,a,b,c]
def Bal (p q r a b c : ℕ) :=
  17*(X p (some a)*X q (some b)*X r (some c))+7*(Y p (some a)*Y q (some b)*Y r (some c))=24

theorem normal {p q r a b c : ℕ} (h : Bal p q r a b c) : normalized (PP p q r) (EE a b c)=2 := by
  have x : X 2 (some 2)=17/12 := by decide +kernel
  have y : Y 2 (some 2)=7/12 := by decide +kernel
  simp [normalized,Fin.prod_univ_four,PP,EE,x,y]
  unfold Bal at h
  linarith

theorem exponent_height {p q r a b c : ℕ} (pp : p.Prime) (qp : q.Prime) (rp : r.Prime)
    (op : 2<p) (pq : p<q) (qr : q<r) (ap : 0<a) (bp : 0<b) (cp : 0<c)
    (sol : OeisA245212.a (4*p^a*q^b*r^c)=(σ 1 (4*p^a*q^b*r^c):ℤ)) :
    a≤height r ∧ b≤height r ∧ c≤height r := by
  let P := PP p q r
  let E := EE a b c
  have primes (i : Fin 4) : (P i).Prime := by fin_cases i <;> simp [P,PP,pp,qp,rp,prime_two]
  have inj : P.Injective := by intro i j hit; fin_cases i <;> fin_cases j <;> simp_all [P,PP] <;> omega
  have ps (i : Fin 4) : 0<E i := by fin_cases i <;> simp [E,EE,ap,bp,cp]
  have bnd (i : Fin 4) : P i≤r := by fin_cases i <;> simp [P,PP] <;> omega
  have dt (i : Fin 4) : P i=2 → P i^E i≤r^(2*r) := by
    fin_cases i <;> simp [P,E,PP,EE]
    · exact (by omega : 4≤r).trans (Nat.le_pow (by omega : 0<2*r))
    all_goals omega
  have repr : total P E=4*p^a*q^b*r^c := by simp [total,Fin.prod_univ_four,P,E,PP,EE,mul_assoc]
  have power := OMA.GuardedHeight245212.max_power P E primes dt ps inj bnd (repr ▸ sol)
  have top := OMA.HeightLog245212.four (lt_of_lt_of_le (ps 0) (le_sup (f:=E) (mem_univ 0))) power
  exact ⟨(le_sup (f:=E) (mem_univ 1)).trans (top.trans (le_max_right ..)),(le_sup (f:=E) (mem_univ 2)).trans (top.trans (le_max_right ..)),
    (le_sup (f:=E) (mem_univ 3)).trans (top.trans (le_max_right ..))⟩

private theorem control {p q r b c : ℕ} (pg : 1<p) (qg : 1<q) (rg : 1<r)
    (bp : 0<b) (cp : 0<c) (enough : 4*(p-1)<(b+1)*(c+1)) :
    ((p:ℚ)-1)*(yr q b*yr r c)<1 := by
  have h : (4:ℚ)*((p:ℚ)-1)<((b:ℚ)+1)*((c:ℚ)+1) := by
    simpa [Nat.cast_sub (show 1≤p by omega)] using
      (show (4:ℚ)*((p-1:ℕ):ℚ)<((b:ℚ)+1)*((c:ℚ)+1) by exact_mod_cast enough)
  obtain ⟨q0,_,q2⟩ := y_range qg bp
  obtain ⟨r0,_,r2⟩ := y_range rg cp
  have z := mul_le_mul q2 r2 (mul_nonneg r0 (by positivity)) (by norm_num : (0:ℚ)≤2)
  have pr : (1:ℚ)<p := by exact_mod_cast pg
  have m := mul_le_mul_of_nonneg_left z (sub_nonneg.mpr pr.le)
  apply (mul_lt_mul_iff_left₀ (show (0:ℚ)<((b:ℚ)+1)*((c:ℚ)+1) by positivity)).mp
  nlinarith only [m,h]

structure Context (B p q r a b c : ℕ) : Prop where
  prime : ∀ i, (PP p q r i).Prime
  pos : ∀ i, 0<EE a b c i
  bound : ∀ i, PP p q r i≤B
  exponents : ∀ i, EE a b c i≤height B
  bal : Bal p q r a b c

theorem context {B p q r a b c : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (pB : p≤B) (qB : q≤B) (rB : r≤B) (ap : 0<a) (bp : 0<b) (cp : 0<c)
    (ae : a≤height B) (be : b≤height B) (ce : c≤height B) (h : Bal p q r a b c) :
    Context B p q r a b c where
  prime i := by fin_cases i <;> simp [PP,hp,hq,hr,prime_two]
  pos i := by fin_cases i <;> simp [EE,ap,bp,cp]
  bound i := by have := hp.two_le; fin_cases i <;> simp [PP,pB,qB,rB]; omega
  exponents i := by fin_cases i <;> simp [EE,ae,be,ce]; exact le_max_left ..
  bal := h

private theorem no_round {B p q r a b c : ℕ} (h : Context B p q r a b c)
    (s : Finset (Fin 4)) (sn : s.Nonempty)
    (large : ∀ i∈s,coefficientBound B (height B)*outside (PP p q r) (EE a b c) s<
      (PP p q r i)^(EE a b c i))
    (strict : ∀ i∈s, ((PP p q r i:ℚ)-1)*
      (∏ j∈univ.erase i,yr (PP p q r j) (EE a b c j))<1) : False := by
  have n := normal h.bal
  have eq := gap_eq _ _ h.prime h.pos s n (enough _ _ h.prime h.bound h.exponents s large)
  have lt := strict_prod _ _ (fun i=>(h.prime i).one_lt) h.pos s sn strict
  linarith

private theorem pow_big {p u e : ℕ} (hp : 1<p) (big : Nat.log p u<e) : u<p^e :=
  (Nat.lt_pow_succ_log_self hp u).trans_le (Nat.pow_le_pow_right (by omega) big)

private theorem erase0 (i : Fin 4) (z : Fin 4 → ℚ) :
    (∏ j∈univ.erase i,z j)=∏ j,if j=i then 1 else z j := by
  rw [← Finset.prod_erase_mul univ (fun j => if j=i then 1 else z j) (mem_univ i)]
  simp only [ite_true,mul_one]
  apply Finset.prod_congr rfl
  intro j hj
  rw [if_neg (mem_erase.mp hj).1]

private theorem control_with_two {p q r b c : ℕ} (pg : 1<p) (qg : 1<q) (rg : 1<r)
    (bp : 0<b) (cp : 0<c) (enough : 4*(p-1)<(b+1)*(c+1)) :
    ((p:ℚ)-1)*(yr 2 2*yr q b*yr r c)<1 := by
  have pg' : (1:ℚ)<p := by exact_mod_cast pg
  have low := mul_nonneg (sub_nonneg.mpr pg'.le) (mul_nonneg (y_range qg bp).1 (y_range rg cp).1)
  calc
    _ = yr 2 2*(((p:ℚ)-1)*(yr q b*yr r c)) := by ring
    _ ≤ _ := mul_le_of_le_one_left low (by decide +kernel : yr 2 2≤1)
    _ < _ := control pg qg rg bp cp enough

private theorem three_ctl {p q r a b c : ℕ} (pg : 1<p) (qg : 1<q) (rg : 1<r)
    (ap : 0<a) (bp : 0<b) (cp : 0<c)
    (v : 4*(p-1)<(b+1)*(c+1)) (w : 4*(q-1)<(a+1)*(c+1)) (x : 4*(r-1)<(a+1)*(b+1))
    (i : Fin 4) (hi : i≠0) : ((PP p q r i:ℚ)-1)*
      (∏ j∈univ.erase i,yr (PP p q r j) (EE a b c j))<1 := by
  rw [erase0]
  fin_cases i <;> simp_all [Fin.prod_univ_four,PP,EE]
  · exact control_with_two pg qg rg bp cp v
  · exact control_with_two qg pg rg ap cp w
  · exact control_with_two rg pg qg ap bp x

theorem small_one {B p q r a b c : ℕ} (h : Context B p q r a b c)
    (sp : seed B p q r) (sq : seed B q p r) (sr : seed B r p q) :
    a≤first B p ∨ b≤first B q ∨ c≤first B r := by
  by_contra! far
  obtain ⟨aa,bb,cc⟩ := far
  let s : Finset (Fin 4) := {1,2,3}
  have out : outside (PP p q r) (EE a b c) s=4 := by simp [outside,Fin.prod_univ_four,PP,EE,s]
  have v := three_ctl (p:=p) (q:=q) (r:=r) (a:=a) (b:=b) (c:=c) (h.prime 1).one_lt (h.prime 2).one_lt (h.prime 3).one_lt (h.pos 1) (h.pos 2) (h.pos 3)
    (sp.trans_le (Nat.mul_le_mul (by omega) (by omega))) (sq.trans_le (Nat.mul_le_mul (by omega) (by omega)))
    (sr.trans_le (Nat.mul_le_mul (by omega) (by omega)))
  apply no_round h s (by decide) _ (fun i hi=> v i (by rintro rfl; simp [s] at hi))
  intro i hi
  rw [out,mul_comm]
  fin_cases i
  · simp [s] at hi
  · exact pow_big (h.prime 1).one_lt aa
  · exact pow_big (h.prime 2).one_lt bb
  · exact pow_big (h.prime 3).one_lt cc

theorem small_two {B p q r a b c : ℕ} (h : Context B p q r a b c) :
    b≤next B p a q r ∨ c≤next B p a r q := by
  by_contra! far
  obtain ⟨bb,cc⟩ := far
  have bigq := pow_big (h.prime 2).one_lt ((le_max_left ..).trans_lt bb)
  have bigr := pow_big (h.prime 3).one_lt ((le_max_left ..).trans_lt cc)
  have w := (Nat.div_lt_iff_lt_mul (Nat.succ_pos a)).mp ((le_max_right ..).trans_lt cc)
  have x := (Nat.div_lt_iff_lt_mul (Nat.succ_pos a)).mp ((le_max_right ..).trans_lt bb)
  let s : Finset (Fin 4) := {2,3}
  have out : outside (PP p q r) (EE a b c) s=4*p^a := by simp [outside,Fin.prod_univ_four,PP,EE,s]
  apply no_round h s (by decide)
  · intro i hi
    rw [out]
    have val : coefficientBound B (height B)*(4*p^a)=budget B*p^a := by unfold budget;ring
    rw [val]
    fin_cases i
    · simp [s] at hi
    · simp [s] at hi
    · exact bigq
    · exact bigr
  · intro i hi
    rw [erase0]
    fin_cases i <;> simp_all [Fin.prod_univ_four,PP,EE,s]
    · exact control_with_two (h.prime 2).one_lt (h.prime 1).one_lt (h.prime 3).one_lt
        (h.pos 1) (h.pos 3) (w.trans_le (by nlinarith only [Nat.zero_le a]))
    · exact control_with_two (h.prime 3).one_lt (h.prime 1).one_lt (h.prime 2).one_lt
        (h.pos 1) (h.pos 2) (x.trans_le (by nlinarith only [Nat.zero_le a]))
end OMA.RankThreeFourLargeSmall245212

end

section

/- Order the two short exponents; recover the last one with the signed floor. -/
namespace OMA.RankThreeFourLargeScan245212
open OMA.Smooth245212 OMA.Large245212 OMA.RankThreeLast245212 OMA.RankThreeFourLargeSmall245212
open scoped ArithmeticFunction.sigma

private theorem prefix_false {p q r a b c cap : ℕ} (pp : p.Prime) (qp : q.Prime) (rp : r.Prime)
    (po : p≠2) (qo : q≠2) (ro : r≠2) (pq : p≠q) (pr : p≠r) (qr : q≠r)
    (cp : 0<c) (cb : c≤cap)
    (hit : OeisA245212.a (4*p^a*q^b*r^c)=(σ 1 (4*p^a*q^b*r^c):ℤ)) :
    reject r (17*wt p a*wt q b) (7*sig p a*sig q b) (12*OMA.Large245212.tax p a*OMA.Large245212.tax q b) cap=false := by
  have cop : (4*p^a*q^b).Coprime r :=
    ((((Nat.coprime_primes Nat.prime_two rp).mpr ro.symm).pow_left 2).mul_left
      (((Nat.coprime_primes pp rp).mpr pr).pow_left a)).mul_left
      (((Nat.coprime_primes qp rp).mpr qr).pow_left b)
  have pos : 0<4*p^a*q^b := by have := pp.pos; have := qp.pos; positivity
  have z := reject_sound pos rp ro cop cp cb hit
  have ⟨w,s,t⟩ := OMA.PrefixLeaf245212.triple Nat.prime_two pp qp po.symm qo.symm pq 2 a b
  change W (4*p^a*q^b)=_ at w
  change σ 1 (4*p^a*q^b)=_ at s
  change (4*p^a*q^b)*(σ 0 (4*p^a*q^b))=_ at t
  rw [w,s,t] at z
  exact z

def row (B p q r a : ℕ) : Bool :=
  let w:=17*wt p a
  let s:=7*sig p a
  let t:=12*OMA.Large245212.tax p a
  (List.range (next B p a q r)).all fun i =>
    let b:=i+1
    reject r (w*wt q b) (s*sig q b) (t*OMA.Large245212.tax q b) (height B)

def check (B p q r : ℕ) : Bool :=
  (List.range (first B p)).all fun i=>row B p q r (i+1)

theorem check_false {B p q r a b c : ℕ} (pp : p.Prime) (qp : q.Prime) (rp : r.Prime)
    (po : 3≤p) (qo : 3≤q) (ro : 3≤r) (pq : p≠q) (pr : p≠r) (qr : q≠r)
    (ap : 0<a) (bp : 0<b) (cp : 0<c) (a1 : a≤first B p) (b2 : b≤next B p a q r)
    (cb : c≤height B) (hit : OeisA245212.a (4*p^a*q^b*r^c)=(σ 1 (4*p^a*q^b*r^c):ℤ)) :
    check B p q r=false := by
  obtain ⟨i,rfl⟩:=Nat.exists_eq_succ_of_ne_zero ap.ne'
  obtain ⟨j,rfl⟩:=Nat.exists_eq_succ_of_ne_zero bp.ne'
  have z:=prefix_false pp qp rp (by omega) (by omega) (by omega) pq pr qr cp cb hit
  apply Bool.eq_false_iff.mpr
  intro passed
  have a:=List.all_eq_true.mp passed i (List.mem_range.mpr (by omega))
  have b:=List.all_eq_true.mp a j (List.mem_range.mpr (Nat.lt_of_succ_le b2))
  simp [z] at b

end OMA.RankThreeFourLargeScan245212

end

section

/- Reindex the three odd powers, check each possible order of the two
small exponents, and extract one of the finitely many supports. -/
namespace OMA.RankThreeFourLargeFixed245212
open OMA.RankThreeFourLargeSmall245212 OMA.RankThreeFourLargeScan245212
open OMA.Smooth245212 OMA.OddFaces245212
open scoped ArithmeticFunction.sigma

structure State (B p q r a b c : ℕ) : Prop where
  pp : p.Prime
  qp : q.Prime
  rp : r.Prime
  po : 3≤p
  qo : 3≤q
  ro : 3≤r
  pq : p≠q
  pr : p≠r
  qr : q≠r
  pB : p≤B
  qB : q≤B
  rB : r≤B
  ap : 0<a
  bp : 0<b
  cp : 0<c
  ab : a≤height B
  bb : b≤height B
  cb : c≤height B
  h : Bal p q r a b c
  hit : OeisA245212.a (4*p^a*q^b*r^c)=(σ 1 (4*p^a*q^b*r^c):ℤ)

namespace State
variable {B p q r a b c : ℕ} (s : State B p q r a b c)
include s

theorem ctx : Context B p q r a b c :=
  context s.pp s.qp s.rp s.pB s.qB s.rB s.ap s.bp s.cp s.ab s.bb s.cb s.h

theorem swap : State B p r q a c b := by
  refine ⟨s.pp,s.rp,s.qp,s.po,s.ro,s.qo,s.pr,s.pq,s.qr.symm,s.pB,s.rB,s.qB,s.ap,s.cp,s.bp,
    s.ab,s.cb,s.bb,?_,?_⟩
  · have u:=s.h;unfold Bal at *;convert u using 1;ring
  · rw [mul_right_comm _ (r^c) (q^b)]; exact s.hit

theorem cycle : State B q r p b c a := by
  refine ⟨s.qp,s.rp,s.pp,s.qo,s.ro,s.po,s.qr,s.pq.symm,s.pr.symm,s.qB,s.rB,s.pB,s.bp,s.cp,s.ap,
    s.bb,s.cb,s.ab,?_,?_⟩
  · have u := s.h;unfold Bal at *;convert u using 1;ring
  · rw [show 4*q^b*r^c*p^a=4*p^a*q^b*r^c by ring]; exact s.hit

theorem after_first (a1 : a≤first B p) (ck : check B p q r=true) (ck' : check B p r q=true) : False := by
  rcases small_two s.ctx with h|h
  · simp [check_false s.pp s.qp s.rp s.po s.qo s.ro s.pq s.pr s.qr s.ap s.bp s.cp a1 h s.cb s.hit] at ck
  · let t := s.swap
    simp [check_false t.pp t.qp t.rp t.po t.qo t.ro t.pq t.pr t.qr t.ap t.bp t.cp a1 h t.cb t.hit] at ck'
end State

structure Facts (B p q r : ℕ) : Prop where
  v : seed B p q r
  w : seed B q p r
  x : seed B r p q
  pq : check B p q r=true
  pr : check B p r q=true
  qr : check B q r p=true
  qp : check B q p r=true
  rp : check B r p q=true
  rq : check B r q p=true

theorem exclude {B p q r a b c : ℕ} (s : State B p q r a b c) (ok : Facts B p q r) : False := by
  rcases small_one s.ctx ok.v ok.w ok.x with aa|bb|cc
  · exact s.after_first aa ok.pq ok.pr
  · exact s.cycle.after_first bb ok.qr ok.qp
  · exact s.cycle.cycle.after_first cc ok.rp ok.rq

end OMA.RankThreeFourLargeFixed245212

end

section

/- The dyadic Euler bound leaves one unbounded branch and ten finite supports. -/
namespace OMA.RankThreeFourLargeOrder245212
open OMA.Smooth245212 OMA.OddFaces245212

def supports : List (ℕ×ℕ) :=
  [(11,13),(11,17),(11,19),(11,23),(11,29),(11,31),(11,37),(13,17),(13,19),(13,23)]

theorem ordered {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (p5 : 5≤p) (pq : p<q) (qr : q<r) (cap : 24≤17*(limitX p*limitX q*limitX r)) :
    p=5 ∧ (q=7 ∨ (q,r)∈supports) := by
  have veto (u v w : ℕ) (hu : 1<u) (hv : 1<v) (hw : 1<w) (up : u≤p)
      (vq : v≤q) (wr : w≤r) (bad : 17*(limitX u*limitX v*limitX w)<24) : False := by
    have l := mul_le_mul (mul_le_mul (cap_anti hu up) (cap_anti hv vq)
      (x_nonneg hq.one_lt none) (x_nonneg hu none)) (cap_anti hw wr)
      (x_nonneg hr.one_lt none) (mul_nonneg (x_nonneg hu none) (x_nonneg hv none))
    linarith
  have p_is : p=5 := by
    by_contra pn
    have p7 : 7≤p := by by_contra! h;interval_cases p <;> norm_num at *
    have q11 : 11≤q := by by_contra! h;interval_cases q <;> norm_num at * <;> omega
    have r13 : 13≤r := by by_contra! h;interval_cases r <;> norm_num at * <;> omega
    exact veto 7 11 13 (by decide) (by decide) (by decide) p7 q11 r13 (by decide +kernel)
  refine ⟨p_is,?_⟩
  have q17 : q<17 := by
    by_contra! lo
    exact veto 5 17 17 (by decide) (by decide) (by decide) p5 lo (by omega) (by decide +kernel)
  have qs : q=7 ∨ q=11 ∨ q=13 := by interval_cases q <;> norm_num at * <;> omega
  rcases qs with h|h|h
  · exact Or.inl h
  · right
    subst q
    have r39 : r<39 := by
      by_contra! lo
      exact veto 5 11 39 (by decide) (by decide) (by decide) p5 le_rfl lo (by decide +kernel)
    interval_cases r <;> first | decide +kernel | norm_num at hr
  · right
    subst q
    have r25 : r<25 := by
      by_contra! lo
      exact veto 5 13 25 (by decide) (by decide) (by decide) p5 le_rfl lo (by decide +kernel)
    interval_cases r <;> first | decide +kernel | norm_num at hr

end OMA.RankThreeFourLargeOrder245212

end

section

/- Six permutations for each finite prime support. -/
namespace OMA.RankThreeFourLargeData245212
open OMA.RankThreeFourLargeFixed245212 OMA.RankThreeFourLargeOrder245212
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000

theorem row11_13 : Facts 13 5 11 13 := by
  constructor <;> first | (unfold OMA.RankThreeFourLargeSmall245212.seed; decide +kernel) | decide +kernel
theorem row11_17 : Facts 17 5 11 17 := by
  constructor <;> first | (unfold OMA.RankThreeFourLargeSmall245212.seed; decide +kernel) | decide +kernel
theorem row11_19 : Facts 19 5 11 19 := by
  constructor <;> first | (unfold OMA.RankThreeFourLargeSmall245212.seed; decide +kernel) | decide +kernel
theorem row11_23 : Facts 23 5 11 23 := by
  constructor <;> first | (unfold OMA.RankThreeFourLargeSmall245212.seed; decide +kernel) | decide +kernel
theorem row11_29 : Facts 29 5 11 29 := by
  constructor <;> first | (unfold OMA.RankThreeFourLargeSmall245212.seed; decide +kernel) | decide +kernel
theorem row11_31 : Facts 31 5 11 31 := by
  constructor <;> first | (unfold OMA.RankThreeFourLargeSmall245212.seed; decide +kernel) | decide +kernel
theorem row11_37 : Facts 37 5 11 37 := by
  constructor <;> first | (unfold OMA.RankThreeFourLargeSmall245212.seed; decide +kernel) | decide +kernel
theorem row13_17 : Facts 17 5 13 17 := by
  constructor <;> first | (unfold OMA.RankThreeFourLargeSmall245212.seed; decide +kernel) | decide +kernel
theorem row13_19 : Facts 19 5 13 19 := by
  constructor <;> first | (unfold OMA.RankThreeFourLargeSmall245212.seed; decide +kernel) | decide +kernel
theorem row13_23 : Facts 23 5 13 23 := by
  constructor <;> first | (unfold OMA.RankThreeFourLargeSmall245212.seed; decide +kernel) | decide +kernel
theorem data : ∀ z∈supports, Facts z.2 5 z.1 z.2 := by
  simp only [supports,List.forall_mem_cons,List.not_mem_nil]
  exact ⟨row11_13,row11_17,row11_19,row11_23,row11_29,row11_31,row11_37,row13_17,row13_19,row13_23,fun _ h => h.elim⟩
end OMA.RankThreeFourLargeData245212

end

section

/- A245212: dyadic exponent two, three odd primes, least odd prime at least five. -/
namespace OMA.RankThreeFourLargeSolution245212
open OMA.RankThreeFourLargeFixed245212 OMA.RankThreeFourLargeSmall245212
open scoped ArithmeticFunction.sigma

theorem no_least_ge_five {p q r a b c : ℕ} (pp : p.Prime) (qp : q.Prime) (rp : r.Prime)
    (p5 : 5≤p) (pq : p<q) (qr : q<r) (ap : 0<a) (bp : 0<b) (cp : 0<c) :
    OeisA245212.a (4*p^a*q^b*r^c)≠(σ 1 (4*p^a*q^b*r^c):ℤ) := by
  intro hit
  have n := OMA.RankThreeFourLargeCap245212.norm pp qp rp (by omega) pq qr hit
  have cap := OMA.RankThreeFourLargeCap245212.caps pp.one_lt qp.one_lt rp.one_lt ap n
  obtain ⟨rfl,seven|mem⟩ := OMA.RankThreeFourLargeOrder245212.ordered pp qp rp p5 pq qr cap
  · subst q
    exact OMA.RankThreeFourLargeSeven245212.all_last rp qr ap bp cp hit
  · obtain ⟨aa,bb,cc⟩ := exponent_height pp qp rp (by decide) pq qr ap bp cp hit
    apply exclude (B:=r) (a:=a) (b:=b) (c:=c) _ (OMA.RankThreeFourLargeData245212.data _ mem)
    exact ⟨pp,qp,rp,by decide,by omega,by omega,pq.ne,(pq.trans qr).ne,qr.ne,
      (pq.trans qr).le,qr.le,le_rfl,ap,bp,cp,aa,bb,cc,n,hit⟩

end OMA.RankThreeFourLargeSolution245212

end

section

/- Four times a product of three odd prime powers does not satisfy A245212. -/
namespace OMA.RankThreeFourSmallFull245212
open Nat ArithmeticFunction
open scoped ArithmeticFunction.sigma

theorem no_four_three {p q r a b c : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (odd : 3≤p) (pq : p<q) (qr : q<r) (ap : 0<a) (bp : 0<b) (cp : 0<c) :
    OeisA245212.a (4*p^a*q^b*r^c)≠(σ 1 (4*p^a*q^b*r^c):ℤ) := by
  by_cases low : p=3
  · subst p
    have notFour : q≠4 := fun eq=>by subst q;norm_num at hq
    exact OMA.RankThreeFourSmallSolution245212.no_least_three hq hr (by omega) qr ap bp cp
  · have notFour : p≠4 := fun eq=>by subst p;norm_num at hp
    exact OMA.RankThreeFourLargeSolution245212.no_least_ge_five hp hq hr (by omega) pq qr ap bp cp

end OMA.RankThreeFourSmallFull245212

end

#print axioms OMA.RankThreeFourSmallFull245212.no_four_three
