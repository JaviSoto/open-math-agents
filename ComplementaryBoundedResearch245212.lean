import FormalConjectures.OEIS.«245212»


/-! Effective finiteness for A245212 with either odd exponent prescribed. -/

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

/- The ordinary divisor equation bounds the free prime via a positive
integer at the dyadic pole. These calculations use integers throughout. -/
namespace OMA.ComplementaryPole245212
open ArithmeticFunction OMA.Smooth245212 OMA.ComplementaryLocal245212
open scoped ArithmeticFunction.sigma

def z (k : ℕ) : ℤ := 2^(k+1)
def G (k : ℕ) : ℤ := z k-1
def F (k : ℕ) : ℤ := 1+k*z k

theorem dyad (k : ℕ) : 0<G k ∧ 0<F k ∧ F k≤((k:ℤ)+1)*G k ∧
    F k+G k=z k*(k+1) := by
  have h : k+1<2^(k+1) := Nat.lt_pow_self (by decide)
  have h' : (k:ℤ)+1<(2:ℤ)^(k+1) := by exact_mod_cast h
  dsimp [G,F,z]
  refine ⟨by omega,by positivity,by nlinarith only [h'],by ring⟩

def den (k : ℕ) (b h P W S : ℤ) :=
  (F k+G k)*b*h*P - h*F k*W - G k*S

/-- The exact deficit at the fourth coordinate is positive and gives a
first upper bound for that prime. -/
theorem tail {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p) (oq : 3≤q)
    (pq : p≠q) (a d k : ℕ)
    (eqn : OeisA245212.a (2^k*p^a*q^(d+1))=(σ 1 (2^k*p^a*q^(d+1)):ℤ)) :
    let D:=den k (a+1) (d+2) ((p:ℤ)^a) (W (p^a)) (σ 1 (p^a))
    0<D ∧ q*D≤3*(d+2)*(k+1)*(a+1)*G k*(p:ℤ)^a := by
  let P : ℤ := (p:ℤ)^a
  let Q : ℤ := (q:ℤ)^(d+1)
  let U : ℤ := (q:ℤ)^d
  let w : ℤ := W (p^a)
  let s : ℤ := σ 1 (p^a)
  let V : ℤ := W (q^d)
  let T : ℤ := σ 1 (q^d)
  let b : ℤ := (a:ℤ)+1
  let h : ℤ := (d:ℤ)+2
  let D := den k b h P w s
  change 0<D ∧ (q:ℤ)*D≤3*h*(k+1)*b*G k*P
  have qp : Q=U*q := by dsimp [Q,U];rw [pow_succ]
  have posq : (0:ℤ)<q := by omega
  have posp : (0:ℤ)<p := by omega
  have pQ : 0<Q := by dsimp [Q];positivity
  have pU : 0<U := by dsimp [U];positivity
  have pP : 0<P := by dsimp [P];positivity
  have hb : 1≤b := by dsimp [b];omega
  have hh : 2≤h := by dsimp [h];omega
  have dy := dyad k
  have bP := bounds hp op a
  have bQ := bounds hq oq d
  have w₀ : b*P≤w := by dsimp [b,P,w]; exact_mod_cast bP.2.2.1
  have wMax : 2*w≤3*b*P := by dsimp [b,P,w]; exact_mod_cast bP.2.1
  have sMax : 2*s≤3*P := by dsimp [s,P]; exact_mod_cast bP.1
  have vMax : 2*V≤3*(h-1)*U := by
    dsimp [V,h,U]; convert! (show 2*(W (q^d):ℤ)≤3*((d:ℤ)+1)*(q:ℤ)^d by exact_mod_cast bQ.2.1) using 1; ring
  have vMin : ((d:ℤ)+1)*U≤V := by dsimp [V,U]; exact_mod_cast bQ.2.2.1
  have tMax : 2*T≤3*U := by dsimp [T,U]; exact_mod_cast bQ.1
  have wPos : 0<w := (mul_pos (by omega : 0<b) pP).trans_le w₀
  have vPos : 0<V := (mul_pos (by positivity) pU).trans_le vMin
  have s0 : 0 ≤ s := by dsimp [s];positivity
  have t0 : 0≤T := by dsimp [T];positivity
  have bal := physical hp hq (by omega) (by omega) pq a (d+1) k eqn
  have ends := last hq oq d
  rw [ends.1,ends.2.1] at bal
  push_cast at bal
  have iden : D*Q=F k*w*V+G k*s*T := by
    dsimp only [D,den,b,h,w,s,V,T,P,Q]
    rw [dy.2.2.2];dsimp [F,G,z]
    linear_combination -bal
  have dPos : 0<D := pos_of_mul_pos_left (iden ▸ add_pos_of_pos_of_nonneg
    (mul_pos (mul_pos dy.2.1 wPos) vPos) (mul_nonneg (mul_nonneg dy.1.le s0) t0)) pQ.le
  refine ⟨dPos,?_⟩
  have ma := mul_le_mul wMax vMax (mul_nonneg (by decide) vPos.le)
    (mul_nonneg (mul_nonneg (by decide) (by omega : 0≤b)) pP.le)
  have mb := mul_le_mul sMax tMax (mul_nonneg (by decide) t0) (mul_nonneg (by decide) pP.le)
  have wa := mul_le_mul_of_nonneg_left ma dy.2.1.le
  have wb := mul_le_mul_of_nonneg_left mb dy.1.le
  have wc := mul_le_mul_of_nonneg_right dy.2.2.1
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by decide : (0:ℤ)≤9) (by omega : 0≤b)) pP.le)
      (by omega : 0≤h-1)) pU.le)
  have one : G k*P*U ≤ (k+1)*b*G k*P*U := by
    have kb : (1:ℤ)≤(k+1)*b := by nlinarith only [hb,mul_nonneg (by positivity : (0:ℤ)≤k) (by omega : 0≤b)]
    nlinarith only [mul_le_mul_of_nonneg_right kb (mul_nonneg (mul_nonneg dy.1.le pP.le) pU.le)]
  have grand : (q*D)*U≤(3*h*(k+1)*b*G k*P)*U := by
    rw [qp] at iden
    nlinarith only [iden,wa,wb,wc,one,
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by omega : 0≤h)
        (by positivity : (0:ℤ)≤k+1)) (by omega : 0≤b)) dy.1.le) pP.le) pU.le]
  exact (mul_le_mul_iff_left₀ pU).mp grand

private theorem integral_pole (K G F p b h P W S : ℤ)
    (gpos : 0<G) (posp : 2≤p) (beyond : p<b*(p-1)) (hpos : 2≤h) (ppos : 0<P)
    (fg : F≤K*G) (w : (p-1)^2*W=p*(b*(p-1)-1)*P+1)
    (s : (p-1)*S=p*P-1) (D : ℤ)
    (den : D=(F+G)*b*h*P-h*F*W-G*S) (plus : 0<D) :
    P≤2*G*h*K ∨ P≤2*(p-1)^2*D := by
  let u:=p-1
  let L:=G*h*b*u^2+F*h*(p-b*u)-G*p*u
  have u0 : 0<u := by dsimp [u];omega
  have iden : u^2*D=P*L-(h*F-G*u) := by
    rw [den];dsimp [L,u]
    linear_combination -h*F*w - G*(p-1)*s
  have lp : 0<L := by
    by_cases yes : G*u≤h*F
    · have prod : 0<P*L := by nlinarith only [iden,yes,mul_pos (sq_pos_of_pos u0) plus]
      exact pos_of_mul_pos_right prod ppos.le
    · have al : L=(b*u)*((h-1)*G*u)+(b*u-p)*(G*u-h*F) := by dsimp [L,u]; ring
      rw [al]
      exact add_pos_of_pos_of_nonneg (mul_pos (by dsimp [u];omega)
        (mul_pos (mul_pos (by omega) gpos) u0)) (mul_nonneg (by dsimp [u];omega) (by omega))
  by_cases cap : P≤2*G*h*K
  · exact Or.inl cap
  right
  change P≤2*u^2*D
  nlinarith only [iden,cap,mul_nonneg ppos.le (by omega : 0≤L-1),
    mul_le_mul_of_nonneg_left fg (by omega : 0≤h),mul_pos gpos u0]

theorem alternative {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p) (oq : 3≤q)
    (pq : p≠q) (a d k : ℕ) (a2 : 2≤a)
    (eqn : OeisA245212.a (2^k*p^a*q^(d+1))=(σ 1 (2^k*p^a*q^(d+1)):ℤ)) :
    p^a≤2*2^(k+1)*(d+2)*(k+1) ∨ q≤6*(d+2)*(k+1)*(a+1)*2^(k+1)*p^2 := by
  have tt := tail hp hq op oq pq a d k eqn
  dsimp only at tt
  let D:=den k (a+1) (d+2) ((p:ℤ)^a) (W (p^a)) (σ 1 (p^a))
  have di := dyad k
  have pp : (0:ℤ)<p := by omega
  have ma := moments hp a
  have res := integral_pole ((k:ℤ)+1) (G k) (F k) p (a+1) (d+2) (p^a)
    (W (p^a)) (σ 1 (p^a)) di.1 (by omega) (by
      nlinarith only [mul_nonneg (by omega : (0:ℤ)≤a-2) (by omega : (0:ℤ)≤p-1),
        (show (3:ℤ)≤p by exact_mod_cast op)]) (by omega) (by positivity) di.2.2.1 ma.2 ma.1 D rfl tt.1
  have gz : G k≤z k := by dsimp [G];omega
  rcases res with cap | cap
  · left
    have z := mul_le_mul_of_nonneg_right gz (by positivity : (0:ℤ)≤2*(d+2)*(k+1))
    dsimp [OMA.ComplementaryPole245212.z] at z
    exact_mod_cast (show (p:ℤ)^a≤2*2^(k+1)*(d+2)*(k+1) by nlinarith only [cap,z])
  · right
    have factor := mul_le_mul_of_nonneg_left cap (by positivity : (0:ℤ)≤q)
    have prod := mul_le_mul_of_nonneg_right tt.2 (mul_nonneg (by decide : (0:ℤ)≤2) (sq_nonneg ((p:ℤ)-1)))
    change (q:ℤ)*D*(2*(p-1)^2) ≤ 3*(d+2)*(k+1)*(a+1)*G k*(p:ℤ)^a*(2*(p-1)^2) at prod
    have comp : (q:ℤ)*(p:ℤ)^a≤(6*(d+2)*(k+1)*(a+1)*G k*(p-1)^2)*(p:ℤ)^a := by
      nlinarith only [factor,prod]
    have v := (mul_le_mul_iff_left₀ (by positivity : 0<(p:ℤ)^a)).mp comp
    have pcap : ((p:ℤ)-1)^2≤(p:ℤ)^2 := by nlinarith only [pp]
    have gcap := mul_le_mul gz pcap (sq_nonneg _) (by dsimp [z];positivity)
    have upper := mul_le_mul_of_nonneg_left gcap (by positivity : (0:ℤ)≤6*(d+2)*(k+1)*(a+1))
    dsimp [z] at upper
    exact_mod_cast (show (q:ℤ)≤6*(d+2)*(k+1)*(a+1)*2^(k+1)*p^2 by nlinarith only [v,upper])

end OMA.ComplementaryPole245212

end

section

/- Integer bounds at both dyadic poles. No roots or logarithms are
needed, so the statements also cover small positive exponents. -/
namespace OMA.ComplementaryDyad245212
open ArithmeticFunction OMA.Smooth245212 OMA.ComplementaryPole245212 OMA.ComplementaryLocal245212
open scoped ArithmeticFunction.sigma

private theorem integer_round {k : ℕ} {b h P W S : ℤ} (hh : 0<h)
    (low : b*P≤W) (high : 2*W≤3*b*P)
    (plus : 0<den k b h P W S) (cut : ((k:ℤ)+1)*h*b*P≤G k) :
    G k≤2*den k b h P W S := by
  let u:=((k:ℤ)+1)*b*h*P-h*k*W-S
  have iden : G k*u=den k b h P W S+((k:ℤ)+1)*h*(W-b*P) := by
    dsimp [u,den,G,F]; ring
  have Kh : (0:ℤ)≤(k+1)*h := by positivity
  have gp := (dyad k).1
  have pos : 0<u := by
    apply pos_of_mul_pos_right (a:=G k) _ gp.le
    rw [iden]; exact add_pos_of_pos_of_nonneg plus (mul_nonneg Kh (sub_nonneg.mpr low))
  have gu : G k≤G k*u := by nlinarith only [mul_nonneg gp.le (by omega : 0≤u-1)]
  nlinarith only [iden,cut,gu,mul_le_mul_of_nonneg_left high Kh]

theorem near {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p) (oq : 3≤q)
    (pq : p≠q) (hd : 1≤d)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ))
    (cut : (k+1)*(d+1)*(a+1)*p^a<2^(k+1)) :
    q≤6*(d+1)*(k+1)*(a+1)*p^a := by
  obtain ⟨e,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d≠0)
  let D:=den k (a+1) (e+2) ((p:ℤ)^a) (W (p^a)) (σ 1 (p^a))
  obtain ⟨dp,qu⟩ := tail hp hq op oq pq a e k eqn
  change 0<D at dp
  have cut' : ((k:ℤ)+1)*(e+2)*(a+1)*(p:ℤ)^a≤G k := by
    have h : ((k:ℤ)+1)*(e+1+1)*(a+1)*(p:ℤ)^a<(2:ℤ)^(k+1) := by exact_mod_cast cut
    dsimp [G,z]; linarith only [h]
  have bd := bounds hp op a
  have dg := integer_round (by positivity : (0:ℤ)<e+2)
    (by exact_mod_cast bd.2.2.1) (by exact_mod_cast bd.2.1) dp cut'
  change (q:ℤ)*D≤3*(e+2)*(k+1)*(a+1)*G k*(p:ℤ)^a at qu
  have gg : (q:ℤ)*G k≤(6*(e+2)*(k+1)*(a+1)*(p:ℤ)^a)*G k := by
    nlinarith only [qu,mul_le_mul_of_nonneg_left dg (by positivity : (0:ℤ)≤q)]
  exact_mod_cast (mul_le_mul_iff_left₀ (dyad k).1).mp gg

/-- The dyadic power divides the positive difference of the two
cofactor products, independently of the sizes of the exponents. -/
theorem level {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p) (oq : 3≤q)
    (pq : p≠q) (hd : 1≤d)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    2^(k+1) ≤ 3*(d+1)*(a+1)*p^a*q^d := by
  obtain ⟨e,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d≠0)
  let Wp : ℤ:=W (p^a)
  let Sp : ℤ:=σ 1 (p^a)
  let Wq : ℤ:=W (q^(e+1))
  let Sq : ℤ:=σ 1 (q^(e+1))
  let J:ℤ:=((k:ℤ)+1)*(a+1)*(e+1+1)*p^a*q^(e+1)
  have phy := physical hp hq (by omega) (by omega) pq a (e+1) k eqn
  change (1+k*z k)*Wp*Wq+(z k-1)*Sp*Sq=z k*(k+1)*(a+1)*(e+1+1)*p^a*q^(e+1) at phy
  have dv : z k∣Wp*Wq-Sp*Sq := ⟨J-k*Wp*Wq-Sp*Sq,by dsimp [J];linear_combination phy⟩
  have bd := bounds hp op a
  have bq := bounds hq oq (e+1)
  have sub : Sq<Wq := by
    dsimp [Sq,Wq]
    have endq := last hq oq e
    rw [endq.1,endq.2.1]
    have rest := (bounds hq oq e).2.2.2
    have top : 0<q^(e+1) := pow_pos hq.pos _
    exact_mod_cast (show q^(e+1)+σ 1 (q^e)<(e+2)*q^(e+1)+W (q^e) by
      nlinarith only [top,rest,Nat.zero_le (e*q^(e+1))])
  have sp : 0<Sp := by
    dsimp [Sp]; exact_mod_cast (show 0<σ 1 (p^a) by
      rw [sigma_one_apply_prime_pow hp];exact Finset.sum_pos (fun i _ => pow_pos hp.pos i) (by simp))
  have sw : Sp≤Wp := by dsimp [Sp,Wp];exact_mod_cast bd.2.2.2
  have lt : 0<Wp*Wq-Sp*Sq := by
    have sq : 0≤Sq := by dsimp [Sq];positivity
    nlinarith only [mul_pos sp (sub_pos.mpr sub),
      mul_nonneg (sub_nonneg.mpr sw) (by omega : 0≤Wq)]
  have dz := Int.le_of_dvd lt dv
  have wp : 2*Wp≤3*((a:ℤ)+1)*p^a := by dsimp [Wp];exact_mod_cast bd.2.1
  have wq : 2*Wq≤3*((e:ℤ)+1+1)*q^(e+1) := by dsimp [Wq];exact_mod_cast bq.2.1
  have qs : 0≤Sq := by dsimp [Sq];positivity
  have zz : z k≤3*(e+1+1)*(a+1)*(p:ℤ)^a*q^(e+1) := by
    nlinarith only [dz,mul_le_mul wp wq (by dsimp [Wq];positivity) (by positivity),
      mul_nonneg sp.le qs, show (0:ℤ)≤(e+1+1)*(a+1)*(p:ℤ)^a*q^(e+1) by positivity]
  dsimp [z] at zz;exact_mod_cast zz

theorem power_floor {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p) (oq : 3≤q)
    (pq : p≠q) (hd : 1≤d)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    2^(k+1)≤(6*(d+1)*(k+1)*(a+1)*p^a)^(d+1) := by
  let B := 6*(d+1)*(k+1)*(a+1)*p^a
  have bpos : 0<B := by dsimp [B];have := hp.pos;positivity
  change _ ≤ B^(d+1)
  by_cases cut : (k+1)*(d+1)*(a+1)*p^a<2^(k+1)
  · have qB : q≤B := near hp hq op oq pq hd eqn cut
    have small : 3*(d+1)*(a+1)*p^a≤B := by
      dsimp [B];nlinarith only [Nat.zero_le ((d+1)*k*(a+1)*p^a), Nat.zero_le ((d+1)*(a+1)*p^a)]
    exact (level hp hq op oq pq hd eqn).trans (by rw [pow_succ'];exact Nat.mul_le_mul small (Nat.pow_le_pow_left qB _))
  · apply (show 2^(k+1)≤B by dsimp [B];nlinarith only [cut,Nat.zero_le ((d+1)*(k+1)*(a+1)*p^a)]).trans
    simpa using (Nat.pow_le_pow_right bpos (show 1≤d+1 by omega))

end OMA.ComplementaryDyad245212

end

section

/- The integer pole at k is positive once the original deficit is
positive; rounding it, rather than gamma, removes its dyadic denominator. -/
namespace OMA.ComplementaryFar245212
open ArithmeticFunction OMA.Smooth245212 OMA.ComplementaryPole245212 OMA.ComplementaryLocal245212
open scoped ArithmeticFunction.sigma

private theorem round {k : ℕ} {p b h P W S : ℤ} (hp : 3≤p) (hb : 3≤b) (hh : 2≤h) (hP : 0<P)
    (w : (p-1)^2*W=p*(b*(p-1)-1)*P+1) (s : (p-1)*S=p*P-1)
    (plus : 0<den k b h P W S) (gc : 4*((k:ℤ)+1)*h*b*p≤G k)
    (pc : 4*h*((k:ℤ)+1)≤P) : G k*P≤2*(p-1)^2*den k b h P W S := by
  let u:=p-1
  let L:=h*b*u^2+(k:ℤ)*h*(p-b*u)-p*u
  let D:=den k b h P W S
  change G k*P≤2*u^2*D
  have up : 0<u := by dsimp [u];omega
  have kp : (0:ℤ)<k+1 := by positivity
  have bp : 0<b*u-p := by
    dsimp [u];nlinarith only [hp,hb,mul_nonneg (show 0≤b-3 by omega) (show 0≤p-1 by omega)]
  have gp := (dyad k).1
  have fg : F k=(k:ℤ)*G k+(k+1) := by dsimp [F,G];ring
  have iden : u^2*D=P*G k*L-P*(k+1)*h*(b*u-p)-(h*F k-G k*u) := by
    dsimp [L,D,den,u];rw [fg]
    linear_combination -h*((k:ℤ)*G k+(k+1))*w-G k*(p-1)*s
  have lp : 0<L := by
    by_cases low : h*k≤u
    · have decomp : L=b*u*((h-1)*u)+(b*u-p)*(u-h*k) := by dsimp [L,u];ring
      rw [decomp]
      exact add_pos_of_pos_of_nonneg (mul_pos (mul_pos (by omega) up) (mul_pos (by omega) up))
        (mul_nonneg bp.le (by omega))
    · have ef : 0≤h*F k-G k*u := by
        rw [fg];nlinarith only [mul_nonneg gp.le (by omega : 0≤h*k-u),mul_nonneg (by omega : 0≤h) kp.le]
      have pl : 0<(P*G k)*L := by
        nlinarith only [iden,ef,mul_pos (sq_pos_of_pos up) plus,
          mul_nonneg (mul_nonneg (mul_nonneg hP.le kp.le) (by omega : 0≤h)) bp.le]
      exact pos_of_mul_pos_right pl (mul_nonneg hP.le gp.le)
  have PGL := mul_nonneg (mul_nonneg hP.le gp.le) (show 0≤L-1 by omega)
  have scaled := mul_le_mul_of_nonneg_left gc hP.le
  have other := mul_le_mul_of_nonneg_right pc gp.le
  have fcap := mul_le_mul_of_nonneg_left (dyad k).2.2.1 (by omega : 0≤h)
  have hu : b*u-p≤b*p := by dsimp [u];nlinarith only [hp,hb]
  have klein := mul_le_mul_of_nonneg_left hu
    (show (0:ℤ)≤P*(k+1)*h by positivity)
  nlinarith only [iden,PGL,scaled,other,fcap,klein,mul_nonneg gp.le up.le]

theorem far {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p) (oq : 3≤q) (pq : p≠q)
    (ha : 2≤a) (hd : 1≤d)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ))
    (gc : 4*(k+1)*(d+1)*(a+1)*p<2^(k+1)) (pc : 4*(d+1)*(k+1)≤p^a) :
    q≤6*(d+1)*(k+1)*(a+1)*p^2 := by
  obtain ⟨e,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d≠0)
  let D:=den k (a+1) (e+2) ((p:ℤ)^a) (W (p^a)) (σ 1 (p^a))
  obtain ⟨dp,qu⟩ := tail hp hq op oq pq a e k eqn
  change 0<D at dp
  have gc' : 4*((k:ℤ)+1)*(e+2)*(a+1)*p≤G k := by
    have h : 4*((k:ℤ)+1)*(e+1+1)*(a+1)*p<(2:ℤ)^(k+1) := by exact_mod_cast gc
    dsimp [G,z];linarith only [h]
  have pc' : 4*((e:ℤ)+2)*(k+1)≤(p:ℤ)^a := by
    have h : 4*((e:ℤ)+1+1)*(k+1)≤(p:ℤ)^a := by exact_mod_cast pc
    linarith only [h]
  have m := moments hp a
  have r := round (show (3:ℤ)≤p by omega) (show (3:ℤ)≤a+1 by omega)
    (show (2:ℤ)≤e+2 by omega) (pow_pos (show (0:ℤ)<p by omega) a) m.2 m.1 dp gc' pc'
  change (q:ℤ)*D≤3*(e+2)*(k+1)*(a+1)*G k*(p:ℤ)^a at qu
  have qk : (q:ℤ)*(G k*(p:ℤ)^a)≤(6*(e+2)*(k+1)*(a+1)*((p:ℤ)-1)^2)*(G k*(p:ℤ)^a) := by
    nlinarith only [mul_le_mul_of_nonneg_left r (show (0:ℤ)≤q by positivity),
      mul_le_mul_of_nonneg_left qu (mul_nonneg (show (0:ℤ)≤2 by decide) (sq_nonneg ((p:ℤ)-1)))]
  have cap := (mul_le_mul_iff_left₀ (mul_pos (dyad k).1 (pow_pos (show (0:ℤ)<p by omega) a))).mp qk
  have sq : ((p:ℤ)-1)^2≤(p:ℤ)^2 := by nlinarith only [show (3:ℤ)≤p by omega]
  exact_mod_cast cap.trans (mul_le_mul_of_nonneg_left sq (by positivity))

end OMA.ComplementaryFar245212

end

section

/- One prime is small, and the prime-power divisor of its complementary
cofactor gives a second independent estimate, from the original equality. -/
namespace OMA.ComplementaryBase245212
open ArithmeticFunction OMA.Smooth245212 OMA.ComplementaryLocal245212 OMA.ComplementaryPole245212
open scoped ArithmeticFunction.sigma

private theorem scaled {p k : ℕ} (hp : p.Prime) (op : 3≤p) (large : 5*(k+1)<p)
    (a : ℕ) : (5*((k:ℤ)+1))*(W (p^a):ℤ) ≤ (5*((k:ℤ)+1)+1)*((a:ℤ)+1)*p^a := by
  have w := OMA.PrimePowerDiv245212.weighted hp a
  zify [Nat.cast_sub hp.pos] at w
  have bottom : ((a:ℤ)+1)*p^a ≤ (W (p^a):ℤ) := by exact_mod_cast (bounds hp op a).2.2.1
  have big : 0≤((p:ℤ)-1)-5*(k+1) := by omega
  nlinarith only [w,mul_nonneg big (sub_nonneg.mpr bottom),
    (show (0:ℤ)≤σ 1 (p^a) by positivity)]

private theorem algebra {K Z F G A N : ℤ} (k1 : 1≤K) (z0 : 0<Z) (f0 : 0<F)
    (g0 : 0<G) (frac : F≤K*G) (eqn : F*A+G*N=(F+G)*Z)
    (weight : (5*K)^2*A≤(5*K+1)^2*Z) (ordinary : 2*N≤Z) : False := by
  have diff : G*Z≤2*F*(A-Z) := by
    nlinarith only [eqn,mul_le_mul_of_nonneg_left ordinary g0.le]
  have w' : (5*K)^2*(A-Z)≤(10*K+1)*Z := by nlinarith only [weight]
  have left := mul_le_mul_of_nonneg_left diff (sq_nonneg (5*K))
  have right := mul_le_mul_of_nonneg_left w' (show 0≤2*F by omega)
  have top := mul_le_mul_of_nonneg_right frac
    (mul_nonneg (show 0≤2*(10*K+1) by omega) z0.le)
  have good : 0<25*K^2-2*K*(10*K+1) := by
    nlinarith only [k1,mul_nonneg (by omega : 0≤K-1) (by omega : 0≤K)]
  nlinarith only [left,right,top,mul_pos good (mul_pos g0 z0)]

theorem small_prime {p q k a d : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p)
    (oq : 3≤q) (pq : p≠q) (many : 5≤(a+1)*(d+1))
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    p≤5*(k+1) ∨ q≤5*(k+1) := by
  by_contra! bad
  have l := scaled hp op bad.1 a
  have r := scaled hq oq bad.2 d
  have h := mul_le_mul l r (by positivity) (by positivity)
  have h₁ : 2*(σ 1 (p^a):ℤ)≤3*p^a := by exact_mod_cast (bounds hp op a).1
  have h₂ : 2*(σ 1 (q^d):ℤ)≤3*q^d := by exact_mod_cast (bounds hq oq d).1
  have ord := mul_le_mul h₁ h₂ (by positivity) (by positivity)
  have mb : (5:ℤ)≤((a:ℤ)+1)*(d+1) := by exact_mod_cast many
  have up := mul_le_mul_of_nonneg_right mb (by positivity : 0≤(p:ℤ)^a*q^d)
  have e := physical hp hq (by omega) (by omega) pq a d k eqn
  have y := dyad k
  change F k*(W (p^a):ℤ)*(W (q^d):ℤ)+G k*(σ 1 (p^a):ℤ)*(σ 1 (q^d):ℤ)=z k*(k+1)*(a+1)*(d+1)*p^a*q^d at e
  rw [←y.2.2.2] at e
  have pp : (0:ℤ)<p := by omega
  have qp : (0:ℤ)<q := by omega
  apply algebra (K:=(k:ℤ)+1) (Z:=((a:ℤ)+1)*(d+1)*p^a*q^d) (A:=(W (p^a):ℤ)*W (q^d))
    (N:=(σ 1 (p^a):ℤ)*σ 1 (q^d)) (by omega) (by positivity) y.2.1 y.1 y.2.2.1
  · linear_combination e
  · nlinarith only [h]
  · nlinarith only [ord,up, (show (0:ℤ)≤p^a*q^d by positivity)]

theorem cofactor {p q k a d : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p)
    (oq : 3≤q) (pq : p≠q)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    p^a ≤ 2*(d+1)*2^(k+1)*(k+1+p)*q^d := by
  have tq : (2^k).Coprime (q^d) := (((Nat.coprime_primes Nat.prime_two hq).mpr (by omega)).pow_left k).pow_right d
  have tp : (2^k*q^d).Coprime p :=
    (((Nat.coprime_primes Nat.prime_two hp).mpr (by omega)).pow_left k).mul_left
      (((Nat.coprime_primes hq hp).mpr pq.symm).pow_left d)
  have pp : 0<p := hp.pos
  have qp : 0<q := hq.pos
  have bound := OMA.PrimePowerDiv245212.cofactor_bound (show 0<2^k*q^d by positivity)
    hp (by omega) tp a (by simpa [mul_right_comm] using eqn)
  rw [w_mult.map_mul_of_coprime tq,isMultiplicative_sigma.map_mul_of_coprime tq] at bound
  have geom := moments Nat.prime_two k
  norm_num at geom
  have g : (σ 1 (2^k):ℤ)=G k := by dsimp [G,z];rw [pow_succ];nlinarith only [geom.1]
  have f : (W (2^k):ℤ)=F k := by dsimp [F,z];rw [pow_succ];nlinarith only [geom.2]
  have first : (W (q^d):ℤ)≤2*((d:ℤ)+1)*q^d := by
    have hh : 2*(W (q^d):ℤ)≤3*((d:ℤ)+1)*q^d := by exact_mod_cast (bounds hq oq d).2.1
    nlinarith only [hh, (show (0:ℤ)≤((d:ℤ)+1)*q^d by positivity)]
  have second : (σ 1 (q^d):ℤ)≤2*q^d := by
    have hh : 2*(σ 1 (q^d):ℤ)≤3*q^d := by exact_mod_cast (bounds hq oq d).1
    nlinarith only [hh, (show (0:ℤ)≤q^d by positivity)]
  have dy := dyad k
  have gz : G k≤z k := by unfold G; omega
  have zpos : 0≤z k := by unfold z;positivity
  have castBound : (p:ℤ)^a ≤ |F k*(W (q^d):ℤ)-((p:ℤ)-1)*G k*(σ 1 (q^d):ℤ)| := by
    zify at bound
    rw [f,g] at bound
    simpa [mul_assoc] using bound
  have pos1 : 0≤F k*(W (q^d):ℤ) := mul_nonneg dy.2.1.le (by positivity)
  have pos2 : 0≤((p:ℤ)-1)*G k*(σ 1 (q^d):ℤ) :=
    mul_nonneg (mul_nonneg (by omega) dy.1.le) (by positivity)
  have direct : |F k*(W (q^d):ℤ)-((p:ℤ)-1)*G k*(σ 1 (q^d):ℤ)| ≤
      F k*(W (q^d):ℤ)+((p:ℤ)-1)*G k*(σ 1 (q^d):ℤ) := by
    apply abs_le.mpr;omega
  have v₁ := mul_le_mul dy.2.2.1 first (by positivity) (mul_nonneg (by positivity) dy.1.le)
  have v₂ := mul_le_mul_of_nonneg_left second (mul_nonneg (by omega : (0:ℤ)≤p-1) dy.1.le)
  have cG := mul_le_mul_of_nonneg_right gz (by positivity : 0≤2*((d:ℤ)+1)*(k+1+p)*q^d)
  have gain : 0≤(2*(d:ℤ)*p+2)*G k*q^d := mul_nonneg (mul_nonneg (by positivity) dy.1.le) (by positivity)
  have result : (p:ℤ)^a ≤ 2*((d:ℤ)+1)*z k*(k+1+p)*q^d := by
    nlinarith only [castBound,direct,v₁,v₂,cG,gain]
  unfold z at result
  exact_mod_cast result

end OMA.ComplementaryBase245212

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

/- The original OEIS equation bounds the other exponent linearly in the
dyadic exponent and quadratically in the prescribed odd exponent. -/
namespace OMA.ComplementaryExp245212
open scoped ArithmeticFunction.sigma

private theorem constant (d : ℕ) :
    4*(d+1)*(150*(d+1))^d ≤ 2^(16*(d+1)^2) := by
  let h := d+1
  have hpos : 1≤h := by dsimp [h];omega
  have small : h≤(2:ℕ)^h := (Nat.lt_pow_self (by decide : 1<2)).le
  have first : 4*h≤2^(3*h) := calc
    _ ≤ 2^2*2^h := Nat.mul_le_mul_left _ small
    _ = _ := (pow_add _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  have second : 150*h≤2^(9*h) := calc
    _ ≤ 2^8*2^h := Nat.mul_le_mul (by decide : 150≤(2:ℕ)^8) small
    _ = _ := (pow_add _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  have prod := Nat.mul_le_mul first (Nat.pow_le_pow_left second d)
  rw [←pow_mul,←pow_add] at prod
  exact prod.trans (Nat.pow_le_pow_right (by decide) (by dsimp [h];nlinarith only [Nat.zero_le d,Nat.zero_le (d^2)]))

private theorem generic {p q a d K : ℕ} (hp : 2≤p) (ha : 2≤a) (hK : 1≤K)
    (small : p≤5*K ∨ q≤5*K)
    (power : p^a≤2*(d+1)*2^K*(K+p)*q^d)
    (alt : p^a≤2*2^K*(d+1)*K ∨ q≤6*(d+1)*K*(a+1)*2^K*p^2) :
    a+1≤64*(d+1)^2*K := by
  let h:=d+1
  let z:ℕ:=2^K
  let b:=a+1
  have hpos : 1≤h := by dsimp [h];omega
  have bpos : 1≤b := by dsimp [b];omega
  have zpos : 1≤z := Nat.one_le_pow _ _ (by decide : 0<2)
  have zmore : z≤z^h := by simpa using (Nat.pow_le_pow_right zpos hpos)
  have kmore : K≤K^(3*d+1) := by simpa using
    (Nat.pow_le_pow_right hK (show 1≤3*d+1 by omega))
  have Ccap : 4*h*(150*h)^d≤2^(16*h^2) := constant d
  have one : 1≤(150*h)^d := Nat.one_le_pow _ _ (by omega)
  have C₁ : 2*h≤2^(16*h^2) := (show 2*h≤4*h*(150*h)^d by
    nlinarith only [Nat.mul_le_mul_left (4*h) one]).trans Ccap
  have pa : 2^(a-1)≤p^a := (Nat.pow_le_pow_left hp _).trans
    (Nat.pow_le_pow_right (by omega) (Nat.sub_le a 1))
  apply OMA.ComplementarySize245212.exponents hK
  change 2^(a-1)≤2^(16*h^2)*z^h*b^d*K^(3*d+1)
  by_cases direct : p^a≤2*z*h*K
  · have scale := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul C₁ zmore)
      (Nat.one_le_pow d b bpos)) kmore
    exact (pa.trans direct).trans (by nlinarith only [scale])
  · have qlim : q≤150*h*z*b*K^3 := by
      rcases small with pSmall | qSmall
      · have cap := alt.resolve_left direct
        change q≤6*h*K*b*z*p^2 at cap
        have sq := Nat.pow_le_pow_left pSmall 2
        have w := Nat.mul_le_mul_left (6*h*K*b*z) sq
        nlinarith only [cap,w]
      · have z5 : 5≤150*h*z*b*K^2 := calc
          _ ≤ (150*h)*1*1*1 := by omega
          _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ zpos) bpos)
            (Nat.one_le_pow _ _ hK)
        nlinarith only [qSmall,Nat.mul_le_mul_left K z5]
    have kp : K+p≤2*K*p := by
      nlinarith only [Nat.mul_le_mul_right p hK,Nat.mul_le_mul_left K (show 1≤p by omega)]
    have hpow := Nat.mul_le_mul (Nat.mul_le_mul_left (2*h*z) kp) (Nat.pow_le_pow_left qlim d)
    have sub : p^(a-1)*p=p^a := by rw [←pow_succ]; congr 1;omega
    have canceled : p^(a-1)≤4*h*z*K*(150*h*z*b*K^3)^d := by
      apply Nat.le_of_mul_le_mul_right ?_ (by omega : 0<p)
      rw [sub]
      change p^a≤2*h*z*(K+p)*q^d at power
      nlinarith only [power,hpow]
    have exactfactor : 4*h*z*K*(150*h*z*b*K^3)^d =
       (4*h*(150*h)^d)*z^h*b^d*K^(3*d+1) := by
      dsimp [h];rw [pow_succ z d,pow_succ K (3*d), pow_mul K 3 d]
      simp only [mul_pow];ring
    rw [exactfactor] at canceled
    exact ((Nat.pow_le_pow_left hp (a-1)).trans canceled).trans
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ Ccap)))

/-- Uniform cofactor-exponent bound directly on the OEIS input. -/
theorem exponent {p q k a d : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p) (oq : 3≤q)
    (pq : p≠q) (hd : 1≤d)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    a+1≤64*(d+1)^2*(k+1) := by
  by_cases ha : 2≤a
  · obtain ⟨d,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d≠0)
    have many : 5≤(a+1)*(d+1+1) := by
      nlinarith only [ha,Nat.zero_le d,Nat.zero_le (a*d)]
    exact generic (by omega) ha (by omega) (OMA.ComplementaryBase245212.small_prime hp hq op oq pq many eqn)
      (OMA.ComplementaryBase245212.cofactor hp hq op oq pq eqn)
      (OMA.ComplementaryPole245212.alternative hp hq op oq pq a d k ha eqn)
  · nlinarith only [ha,Nat.zero_le d,Nat.zero_le (d^2),Nat.zero_le k,
      Nat.zero_le (k*d),Nat.zero_le (k*d^2)]

end OMA.ComplementaryExp245212

end

section

/- When the dyadic power is above the cutoff, both prime bases lie in
an explicit box of degree d+2 in the dyadic exponent. -/
namespace OMA.ComplementaryBox245212
open scoped ArithmeticFunction.sigma

theorem room (d : ℕ) :
    10000*(d+1)^4*5^d≤2^(16*(d+1)^2) := by
  by_cases hd : d=0
  · subst d;decide
  have h : d+1≤2^(d+1) := (Nat.lt_pow_self (by decide : 1<2)).le
  have f : 5^d≤(2^3)^d := Nat.pow_le_pow_left (by decide) d
  have full := Nat.mul_le_mul (Nat.mul_le_mul (show 10000≤(2:ℕ)^14 by decide)
    (Nat.pow_le_pow_left h 4)) f
  rw [←pow_mul,←pow_mul,←pow_add,←pow_add] at full
  exact full.trans (Nat.pow_le_pow_right (by decide) (by nlinarith only [show 1≤d by omega,Nat.zero_le (d^2)]))

theorem box {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p) (oq : 3≤q) (pq : p≠q)
    (ha : 2≤a) (hd : 2≤d)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ))
    (large : (2^(16*(d+1)^2)*(k+1)^(d+3))^(d+1)<2^(k+1)) :
    let B:=2^(16*(d+1)^2)*(k+1)^(d+2)
    p≤B ∧ q≤B ∧ a+1≤B ∧ k+1≤B := by
  let h:=d+1
  let K:=k+1
  let b:=a+1
  let E:ℕ:=2^(16*h^2)
  let B:=E*K^(d+2)
  let D:=E*K^(d+3)
  change p≤B ∧ q≤B ∧ b≤B ∧ K≤B
  change D^h<2^K at large
  have hK : 1≤K := by dsimp [K];omega
  have hh : 3≤h := by dsimp [h];omega
  have he : 1≤E := Nat.one_le_pow _ _ (by decide)
  have hD : 1≤D := Nat.mul_pos he (Nat.one_le_pow _ _ hK)
  have pr : D<2^K := (show D≤D^h by simpa using
    (Nat.pow_le_pow_right hD (show 1≤h by omega))).trans_lt large
  have BD : B≤D := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hK (by omega))
  have hb : b≤64*h^2*K := OMA.ComplementaryExp245212.exponent hp hq op oq pq (by omega) eqn
  have room' : 10000*h^4*5^d≤E := room d
  have h34 : h^3≤h^4 := Nat.pow_le_pow_right (by omega) (by decide)
  have h24 : h^2≤h^4 := Nat.pow_le_pow_right (by omega) (by decide)
  have h₄ : 10000*h^4≤E := (show 10000*h^4≤10000*h^4*5^d by
    simpa using (Nat.mul_le_mul_left (10000*h^4) (Nat.one_le_pow d 5 (by decide)))).trans room'
  have c₃ {x : ℕ} (hx : x≤10000) : x*h^3≤E := (Nat.mul_le_mul hx h34).trans h₄
  have cov {v w : ℕ} (u : v≤E) (g : w≤d+2) : v*K^w≤B :=
    Nat.mul_le_mul u (Nat.pow_le_pow_right hK g)
  have ek : 5*K≤B := by
    have five : 5≤E := (show 5≤10000*h^4 from (show 5≤10000*1 by decide).trans
      (Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ (by omega)))).trans h₄
    simpa using (cov five (show 1≤d+2 by omega))
  have bB : b≤B := hb.trans (by
    simpa using cov ((Nat.mul_le_mul (show 64≤10000 by decide) h24).trans h₄) (show 1≤d+2 by omega))
  have many : 5≤(a+1)*(d+1) := by nlinarith only [ha,hd,Nat.zero_le (a*d)]
  have bases := OMA.ComplementaryBase245212.small_prime hp hq op oq pq many eqn
  change p≤5*K ∨ q≤5*K at bases
  refine ⟨?_,?_,bB,(show K≤5*K by omega).trans ek⟩
  · rcases bases with h | hqK
    · exact h.trans ek
    have grow : 6*b*K*h*q^d≤B := calc
      _ ≤ 6*(64*h^2*K)*K*h*(5*K)^d := by gcongr
      _ = (384*h^3*5^d)*K^(d+2) := by rw [mul_pow,pow_add (m:=d) (n:=2)];ring
      _ ≤ _ := cov ((Nat.mul_le_mul_right _ (Nat.mul_le_mul (show 384≤10000 by decide) h34)).trans room') (by omega)
    have cut : K*(a+1)*(d+1)*q^d<2^K := by
      change K*b*h*q^d<2^K
      exact (show K*b*h*q^d≤6*b*K*h*q^d by nlinarith only [Nat.zero_le (b*K*h*q^d)]).trans_lt
        (grow.trans_lt (BD.trans_lt pr))
    have swap : OeisA245212.a (2^k*q^d*p^a)=(σ 1 (2^k*q^d*p^a):ℤ) := by
      rwa [mul_right_comm]
    exact (OMA.ComplementaryDyad245212.near hq hp oq op pq.symm (by omega) swap cut).trans grow
  · rcases bases with hpK | h
    · have gc : 4*K*h*b*p<2^K := calc
        _ ≤ 4*K*h*(64*h^2*K)*(5*K) := by gcongr
        _ = (1280*h^3)*K^3 := by ring
        _ ≤ B := cov (c₃ (by decide)) (by omega)
        _ < _ := BD.trans_lt pr
      have pc : 4*h*K≤p^a := by
        by_contra! smaller
        have low := OMA.ComplementaryDyad245212.power_floor hp hq op oq pq (by omega) eqn
        change 2^K≤(6*h*K*b*p^a)^h at low
        have scale : 6*h*K*b*p^a≤D := calc
          _ ≤ 6*h*K*(64*h^2*K)*(4*h*K) := by gcongr
          _ = (1536*h^4)*K^3 := by ring
          _ ≤ B := cov ((Nat.mul_le_mul_right _ (show 1536≤10000 by decide)).trans h₄) (by omega)
          _ ≤ D := BD
        exact (not_lt_of_ge (low.trans (Nat.pow_le_pow_left scale h))) large
      apply (OMA.ComplementaryFar245212.far hp hq op oq pq ha (by omega) eqn gc pc).trans
      change 6*h*K*b*p^2≤B
      calc
        _ ≤ 6*h*K*(64*h^2*K)*(5*K)^2 := by gcongr
        _ = (9600*h^3)*K^4 := by ring
        _ ≤ _ := cov (c₃ (by decide)) (by omega)
    · exact h.trans ek

end OMA.ComplementaryBox245212

end

section

/- Integer separations for a repeated prime and its complementary power.
The resonance identities apply to arbitrary positive complementary moments. -/
namespace OMA.QuadraticPowerGap245212

def A (p b J S : ℤ) := b*(p-1)^2*J-(p-1)*p*S
def H (p b J V : ℤ) := b*(p-1)*(p*V-(p-1)*J)-p*V
def C (p v V S : ℤ) := v*V-(p-1)*S

theorem clear (p b k z P W s J V S : ℤ)
    (weighted : (p-1)*W=b*p*P-s) (geometric : (p-1)*s=p*P-1)
    (balance : (1+k*z)*V*W+(z-1)*S*s=z*(k+1)*b*P*J) :
    P*((z-1)*(A p b J S-k*H p b J V)-(k+1)*H p b J V) =
    (z-1)*C p k V S+(k+1)*V := by
  unfold A H C
  linear_combination -(p-1)^2*balance+(1+k*z)*V*(p-1)*weighted+
    ((p-1)*(z-1)*S-(1+k*z)*V)*geometric

/-- All three consequences of an integer resonance, independently of any
particular exponent on the complementary prime. -/
theorem resonance {p b k a J V S : ℕ} (hp : p.Prime) (hp3 : 3≤p) (hb : 3≤b)
    (hS : 0<S) (hV : S≤V) (hJ : J≤V)
    (hit : A p b J S=(k:ℤ)*H p b J V)
    (eqn : (p:ℤ)^a*(((2:ℤ)^(k+1)-1)*(A p b J S-(k:ℤ)*H p b J V)-
          (k+1)*H p b J V)=((2:ℤ)^(k+1)-1)*C p k V S+(k+1)*V) :
    k+1<p ∧ p∣b*J ∧ (J:ℤ)*(V-(S:ℤ))<p*S*(V-(J:ℤ)) ∧
    (p:ℤ)^a < (2:ℤ)^(k+1)*(p-1)*S := by
  let : Fact p.Prime := ⟨hp⟩
  have hp' : (3:ℤ)≤p := by exact_mod_cast hp3
  have hb' : (3:ℤ)≤b := by exact_mod_cast hb
  have hs : (0:ℤ)<S := by exact_mod_cast hS
  have hv : (S:ℤ)≤V := by exact_mod_cast hV
  have hj : (J:ℤ)≤V := by exact_mod_cast hJ
  have bu : (p:ℤ)<b*(p-1) := by
    nlinarith only [hp',hb',mul_nonneg (by omega : (0:ℤ)≤b-3) (by omega : (0:ℤ)≤p-1)]
  have hh : 0<H p b J V := by
    unfold H
    nlinarith only [mul_pos (sub_pos.mpr bu) (by omega : (0:ℤ)<V),
      mul_nonneg (mul_nonneg (by positivity : (0:ℤ)≤b) (sq_nonneg ((p:ℤ)-1))) (sub_nonneg.mpr hj)]
  have zpos : 1<(2:ℤ)^(k+1) := one_lt_pow₀ (by norm_num) (by omega)
  have red : (p:ℤ)^a*(k+1)*H p b J V+(k+1)*V= -((2:ℤ)^(k+1)-1)*C p k V S := by
    rw [hit,sub_self,mul_zero,zero_sub] at eqn
    linear_combination -eqn
  have lhs : 0<(p:ℤ)^a*(k+1)*H p b J V+(k+1)*V := by positivity
  have hneg : C p k V S<0 := by
    by_contra! ge
    nlinarith only [red,lhs,mul_nonneg (by omega : (0:ℤ)≤2^(k+1)-1) ge]
  have hk : k+1<p := by
    by_contra! h
    have hp'' : (p:ℤ)≤k+1 := by exact_mod_cast h
    unfold C at hneg
    nlinarith only [hneg,mul_nonneg (by omega : (0:ℤ)≤k-(p-1)) (by omega : (0:ℤ)≤V),
      mul_nonneg (by omega : (0:ℤ)≤p-1) (sub_nonneg.mpr hv)]
  have modp := congrArg (fun z:ℤ => (z:ZMod p)) hit
  unfold A H at modp
  push_cast at modp
  simp only [ZMod.natCast_self] at modp
  have mod0 : ((b:ZMod p)*J)*(k+1)=0 := by linear_combination modp
  have knz : (↑(k+1:ℕ):ZMod p)≠0 := by
    exact fun he => Nat.not_dvd_of_pos_of_lt (by omega) hk
      ((ZMod.natCast_eq_zero_iff (k+1) p).mp he)
  have dv : p∣b*J := by
    apply (ZMod.natCast_eq_zero_iff (b*J) p).mp
    push_cast at knz ⊢
    exact (mul_eq_zero.mp mod0).resolve_right knz
  have iden : H p b J V*C p k V S=(b:ℤ)*(p-1)^2*
      (J*(V-(S:ℤ))-p*S*(V-(J:ℤ))) := by
    simp only [H,C,A] at hit ⊢
    linear_combination -(V:ℤ)*hit
  have neg := mul_neg_of_pos_of_neg hh hneg
  rw [iden] at neg
  refine ⟨hk,dv,sub_neg.mp (neg_of_mul_neg_right neg (by positivity)),?_⟩
  have hle : 1≤((k:ℤ)+1)*H p b J V := by
    nlinarith only [hh,mul_nonneg (by positivity : (0:ℤ)≤k) hh.le]
  have pbound := mul_le_mul_of_nonneg_left hle (by positivity : 0≤(p:ℤ)^a)
  have cmax : -C p k V S ≤ ((p:ℤ)-1)*S := by unfold C; nlinarith only [mul_nonneg (by positivity : (0:ℤ)≤k) (by positivity : (0:ℤ)≤V)]
  have gc := mul_le_mul_of_nonneg_left cmax (by omega : (0:ℤ)≤2^(k+1)-1)
  nlinarith only [red,pbound,gc,mul_pos (by omega : (0:ℤ)<p-1) hs,
    mul_nonneg (by positivity : (0:ℤ)≤k+1) (by positivity : (0:ℤ)≤V)]

/-- For arbitrary complementary exponent d, this integer cannot vanish if
the weighted cofactor b(p−1)−p already exceeds dp. -/
theorem pole {p b k d : ℤ} (hp : 1<p) (hd : 0<d)
    (large : d*p<b*(p-1)-p) :
    (d+1)*b*(p-1)*(p-1-k)+((d+1)*k-(p-1))*p ≠ 0 := by
  intro hit
  let u := p-1
  let v := b*u-p
  have hu : 0<u := by dsimp [u]; omega
  have hv : d*p<v := large
  have hdpos : 0<d*p := mul_pos hd (by omega)
  have eqn : ((d+1)*(k-u))*v=u*(d*p) := by
    dsimp [v,u]; linear_combination -hit
  have pos : 0<(d+1)*(k-u) := pos_of_mul_pos_left (eqn ▸ mul_pos hu hdpos) (by omega : 0≤v)
  have div : u ∣ (d+1)*(k-u) := by
    refine ⟨((d+1)*(k-u))*(b-1)-d*p,?_⟩
    dsimp [v,u] at eqn ⊢; linear_combination -eqn
  have hle := Int.le_of_dvd pos div
  nlinarith only [eqn,mul_pos hu (sub_pos.mpr hv),
    mul_nonneg (sub_nonneg.mpr hle) (by omega : 0≤v)]

def j (q : ℕ) := 3*q^2
def v (q : ℕ) := 3*q^2+2*q+1
def s (q : ℕ) := q^2+q+1

/-- For complementary exponent two, an exact balance precludes integer
resonance for every a≥6; the cofactor base need not itself be prime. -/
theorem quadratic {p q a k : ℕ} (hp : p.Prime) (hp3 : 3≤p) (hq : 3≤q) (ha : 6≤a)
    (eqn : (p:ℤ)^a*(((2:ℤ)^(k+1)-1)*
      (A p (a+1) (j q) (s q)-(k:ℤ)*H p (a+1) (j q) (v q))-
      (k+1)*H p (a+1) (j q) (v q))=((2:ℤ)^(k+1)-1)*C p k (v q) (s q)+(k+1)*v q) :
    A p (a+1) (j q) (s q)≠(k:ℤ)*H p (a+1) (j q) (v q) := by
  intro hit
  have facts := resonance (b:=a+1) hp hp3 (by omega) (show 0<s q by unfold s; positivity)
    (show s q≤v q by dsimp [s,v]; omega) (show j q≤v q by dsimp [j,v]; omega) (by exact_mod_cast hit)
    (by exact_mod_cast eqn)
  rcases facts with ⟨hk,dv,sep,ub⟩
  have q' : (3:ℤ)≤q := by exact_mod_cast hq
  have qp : q<p := by
    by_contra! pq
    have p' : (p:ℤ)≤q := by exact_mod_cast pq
    simp only [v,s,j] at sep
    push_cast at sep
    have good := mul_pos (mul_pos (by omega : (0:ℤ)<q) (by omega : (0:ℤ)<q-1))
      (sq_pos_of_pos (by omega : (0:ℤ)<2*q+1))
    have diff := mul_nonneg (mul_nonneg (sub_nonneg.mpr p')
      (by positivity : (0:ℤ)≤q^2+q+1)) (by positivity : (0:ℤ)≤2*q+1)
    nlinarith only [sep,good,diff]
  have hp4 : 4≤p := by omega
  have ndj : ¬p∣j q := by
    intro dd
    rcases hp.dvd_mul.mp dd with bad | bad
    · exact Nat.not_dvd_of_pos_of_lt (by decide : 0<3) (by omega) bad
    · exact Nat.not_dvd_of_pos_of_lt (by omega) qp (hp.dvd_of_dvd_pow bad)
  have pa := Nat.le_of_dvd (by omega : 0<a+1) ((hp.dvd_mul.mp dv).resolve_right ndj)
  have ep : 2^(k+1)≤p^(a-3) := calc
    2^(k+1) ≤ 2^(2*(a-3)) := Nat.pow_le_pow_right (by decide) (by omega)
    _ = 4^(a-3) := by rw [pow_mul]; norm_num
    _ ≤ p^(a-3) := Nat.pow_le_pow_left hp4 _
  have pbound : (2:ℤ)^(k+1)*p^3 ≤ (p:ℤ)^a := by
    have ep' : (2:ℤ)^(k+1)≤(p:ℤ)^(a-3) := by exact_mod_cast ep
    have mult := mul_le_mul_of_nonneg_right ep' (by positivity : (0:ℤ)≤p^3)
    rwa [←pow_add,show a-3+3=a by omega] at mult
  have ss : (s q:ℤ)≤(p:ℤ)^2 := by
    have pq' : (q:ℤ)+1≤p := by exact_mod_cast qp
    have sq := pow_le_pow_left₀ (by positivity : (0:ℤ)≤q+1) pq' 2
    unfold s; push_cast; nlinarith only [sq,q']
  have bb := mul_le_mul_of_nonneg_left ss (by omega : (0:ℤ)≤p-1)
  have ab : ((p:ℤ)-1)*s q ≤ (p:ℤ)^3 := by nlinarith only [bb,sq_nonneg (p:ℤ)]
  have tt := mul_le_mul_of_nonneg_left ab (by positivity : (0:ℤ)≤2^(k+1))
  nlinarith only [ub,pbound,tt]

end OMA.QuadraticPowerGap245212

end

section

/- The ordinary A245212 equality separates the integer dyadic parameter
from its complementary-cofactor pole for every exponent d≥2. -/
namespace OMA.ComplementaryNonres245212
open ArithmeticFunction OMA.Smooth245212 OMA.QuadraticPowerGap245212 OMA.ComplementaryLocal245212
open scoped ArithmeticFunction.sigma

theorem cleared {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p) (oq : 3≤q) (pq : p≠q)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    let J := ((d:ℤ)+1)*q^d
    let V : ℤ := W (q^d)
    let S : ℤ := σ 1 (q^d)
    (p:ℤ)^a*(((2:ℤ)^(k+1)-1)*(A p (a+1) J S-(k:ℤ)*H p (a+1) J V)-
      (k+1)*H p (a+1) J V)=((2:ℤ)^(k+1)-1)*C p k V S+(k+1)*V := by
  dsimp only
  have weight := OMA.PrimePowerDiv245212.weighted hp a
  zify [Nat.cast_sub hp.pos] at weight
  apply clear p (a+1) k (2^(k+1)) (p^a) (W (p^a)) (σ 1 (p^a))
    (((d:ℤ)+1)*q^d) (W (q^d)) (σ 1 (q^d))
    (by linear_combination weight) (moments hp a).1
  linear_combination physical hp hq (by omega) (by omega) pq a d k eqn

private theorem moments_sep {q d : ℕ} (hq : q.Prime) (oq : 3≤q) (hd : 1≤d) :
    (d:ℤ)*q^d ≤ (W (q^d):ℤ)-(σ 1 (q^d):ℤ) ∧
    2*q*((W (q^d):ℤ)-((d:ℤ)+1)*q^d) ≤ 3*d*(q:ℤ)^d := by
  obtain ⟨e,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d≠0)
  have ends := last hq oq e
  have rest := (bounds hq oq e).2.2.2
  rw [ends.1,ends.2.1]
  have b : 2*(W (q^e):ℤ)≤3*((e:ℤ)+1)*q^e := by exact_mod_cast ends.2.2
  have l : (σ 1 (q^e):ℤ)≤W (q^e) := by exact_mod_cast rest
  push_cast
  rw [pow_succ]
  constructor
  · linarith only [l]
  · nlinarith only [mul_le_mul_of_nonneg_right b (by positivity : (0:ℤ)≤q)]

private theorem ordered {p q d Q V S : ℤ} (hs : 0 ≤ S) (hQ : 0<Q) (hd : 2≤d)
    (lower : d*Q≤V-S) (error : 0≤V-(d+1)*Q) (up : 2*q*(V-(d+1)*Q)≤3*d*Q)
    (su : 2*S≤3*Q) (strict : (d+1)*Q*(V-S)<p*S*(V-(d+1)*Q)) : q<p := by
  by_contra! pq
  have h1 := mul_le_mul_of_nonneg_right pq (mul_nonneg hs error)
  have h2 := mul_le_mul_of_nonneg_left lower (mul_nonneg (by omega : 0≤d+1) hQ.le)
  have h3 := mul_le_mul_of_nonneg_left up (show 0≤2*S by positivity)
  have h4 := mul_le_mul_of_nonneg_right su (show 0≤3*d*Q by positivity)
  have pos := mul_pos (by omega : 0<4*d-5) (mul_pos (by omega : 0<d) (sq_pos_of_pos hQ))
  nlinarith only [strict,h1,h2,h3,h4,pos]

/-- With a sufficiently high cofactor exponent, an actual equality cannot
annul the limiting integer obtained by replacing gamma with k. -/
theorem original {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p) (oq : 3≤q)
    (pq : p≠q) (hd : 2≤d) (ha : 2*d+4≤a)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    A p (a+1) (((d:ℤ)+1)*q^d) (σ 1 (q^d)) ≠ (k:ℤ)*H p (a+1) (((d:ℤ)+1)*q^d) (W (q^d)) := by
  intro hit
  have clr := cleared hp hq op oq pq eqn
  have bd := bounds hq oq d
  have ps : 0<σ 1 (q^d) := by
    rw [sigma_one_apply_prime_pow hq]
    exact Finset.sum_pos (fun i _ => pow_pos hq.pos i) (by simp)
  obtain ⟨hk,dv,sep,ub⟩ := resonance (J:=(d+1)*q^d) (b:=a+1) hp op (by omega)
    ps bd.2.2.2 bd.2.2.1 (by exact_mod_cast hit) (by exact_mod_cast clr)
  push_cast at sep
  have loc := moments_sep hq oq (by omega : 1≤d)
  have vj : ((d:ℤ)+1)*q^d≤W (q^d) := by exact_mod_cast bd.2.2.1
  have su : 2*(σ 1 (q^d):ℤ)≤3*(q:ℤ)^d := by exact_mod_cast bd.1
  have qq : (0:ℤ)<q := by omega
  have ordering : q<p := by
    exact_mod_cast ordered (by positivity) (pow_pos qq d) (show (2:ℤ)≤d by omega)
      loc.1 (sub_nonneg.mpr vj) loc.2 su sep
  have pp : (4:ℕ)≤p := by omega
  have notq : ¬p∣q^d := fun eq => Nat.not_dvd_of_pos_of_lt hq.pos ordering (hp.dvd_of_dvd_pow eq)
  have exp : k+1≤2*(a-d-2) := by
    by_cases hsmall : p≤2*d+4
    · omega
    · have nj : ¬p∣(d+1)*q^d := by
        intro bad
        exact ((hp.dvd_mul.mp bad).elim (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) notq)
      have bp := Nat.le_of_dvd (by omega : 0<a+1) ((hp.dvd_mul.mp dv).resolve_right nj)
      omega
  have zz : 2^(k+1)≤p^(a-d-2) := calc
    _ ≤ 2^(2*(a-d-2)) := Nat.pow_le_pow_right (by decide) exp
    _ = 4^(a-d-2) := by rw [pow_mul];norm_num
    _ ≤ _ := Nat.pow_le_pow_left pp _
  have fact := Nat.mul_le_mul_right (p^(d+2)) zz
  rw [←pow_add,show a-d-2+(d+2)=a by omega] at fact
  have smax : (σ 1 (q^d):ℤ)≤(p:ℤ)^d*p := by
    have qp := pow_le_pow_left₀ qq.le (show (q:ℤ)≤p by omega) d
    nlinarith only [su,qp,mul_nonneg (show (0:ℤ)≤p-2 by omega) (show (0:ℤ)≤p^d by positivity)]
  have cap : ((p:ℤ)-1)*(σ 1 (q^d):ℤ)≤(p:ℤ)^(d+2) := by
    rw [pow_succ,pow_succ]
    nlinarith only [mul_le_mul_of_nonneg_left smax (by omega : (0:ℤ)≤p-1),
      mul_nonneg (by positivity : (0:ℤ)≤p^d) (by positivity : (0:ℤ)≤p)]
  have ff : (2:ℤ)^(k+1)*p^(d+2)≤(p:ℤ)^a := by exact_mod_cast fact
  nlinarith only [ff,ub,mul_le_mul_of_nonneg_left cap (by positivity : (0:ℤ)≤2^(k+1))]

end OMA.ComplementaryNonres245212

end

section

/- A separated integral cofactor pole bounds the dyadic power
polynomially once the prime bases and divisor exponents are bounded. -/
namespace OMA.ComplementaryHeight245212
open ArithmeticFunction OMA.Smooth245212 OMA.ComplementaryPole245212 OMA.ComplementaryLocal245212
open OMA.QuadraticPowerGap245212
open scoped ArithmeticFunction.sigma

private theorem gap {k : ℕ} {P L H p V S R : ℤ} (pp : 0<P) (pv : 0≤V) (ps : 0 ≤ S)
    (p1 : 1≤p) (ph : 0≤H) (sep : L≠0)
    (clear : P*(G k*L-(k+1)*H)=F k*V-G k*(p-1)*S) (level : G k≤P*R) :
    G k≤(k+1)*H+R*((k+1)*V+p*S) := by
  have gp := (dyad k).1
  have fp := (dyad k).2.1
  have fc := mul_le_mul_of_nonneg_right (dyad k).2.2.1 pv
  have ep : (0:ℤ)≤(k+1)*V+p*S := by positivity
  have rr := mul_le_mul_of_nonneg_right level ep
  have common : P*G k≤P*((k+1)*H+R*((k+1)*V+p*S)) := by
    rcases lt_or_gt_of_ne sep with lt | gt
    · nlinarith only [clear,rr,mul_nonneg (mul_nonneg pp.le gp.le) (show 0≤ -L-1 by omega),
        mul_nonneg fp.le pv,mul_nonneg (mul_nonneg pp.le (show (0:ℤ)≤k+1 by positivity)) ph,
        mul_nonneg gp.le ps,mul_nonneg (mul_nonneg gp.le (show (0:ℤ)≤k+1 by positivity)) pv]
    · nlinarith only [clear,rr,fc,mul_nonneg (mul_nonneg pp.le gp.le) (show 0≤L-1 by omega),
        mul_nonneg (mul_nonneg gp.le (show 0≤p-1 by omega)) ps,
        mul_nonneg (mul_nonneg gp.le (show 0≤p by omega)) ps]
  exact (mul_le_mul_iff_right₀ pp).mp common

theorem height {p q a d k B : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p) (oq : 3≤q) (pq : p≠q)
    (hd : 2≤d) (ha : 2*d+4≤a) (pb : p≤B) (qb : q≤B) (ab : a+1≤B) (kb : k+1≤B)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    2^(k+1)≤16*(d+1)^2*B^(2*d+3) := by
  let h : ℤ := (d:ℤ)+1
  let b : ℤ := (a:ℤ)+1
  let K : ℤ := (k:ℤ)+1
  let Q : ℤ := (q:ℤ)^d
  let P : ℤ := (p:ℤ)^a
  let U : ℤ := p-1
  let V : ℤ := W (q^d)
  let S : ℤ := σ 1 (q^d)
  let J : ℤ := h*Q
  let H0 := H p b J V
  let A0 := A p b J S
  have op' : (3:ℤ)≤p := by omega
  have oq' : (3:ℤ)≤q := by omega
  have pz : (0:ℤ)≤p := by omega
  have uz : 0≤U := by dsimp [U];omega
  have hh : 3≤h := by dsimp [h];omega
  have bh : 3≤b := by dsimp [b];omega
  have b0 : 0≤b := by omega
  have u : U≤(p:ℤ) := by dsimp [U];omega
  have ppos : 0<P := by dsimp [P];positivity
  have qp : 0<Q := by dsimp [Q];positivity
  have v0 : 0≤V := by dsimp [V];positivity
  have s0 : 0 ≤ S := by dsimp [S];positivity
  have j0 : 0≤J := by dsimp [J];positivity
  have bd := bounds hq oq d
  have jv : J≤V := by dsimp [J,V,h,Q];exact_mod_cast bd.2.2.1
  have vh : 2*V≤3*h*Q := by dsimp [V,h,Q];exact_mod_cast bd.2.1
  have sh : 2*S≤3*Q := by dsimp [S,Q];exact_mod_cast bd.1
  have bu : p≤b*U := by dsimp [U];nlinarith only [bh,op',mul_nonneg (show 0≤b-3 by omega) uz]
  have Hpos : 0≤H0 := by
    change 0≤b*U*(p*V-U*J)-p*V
    have id : b*U*(p*V-U*J)-p*V=(b*U-p)*V+b*U^2*(V-J) := by dsimp [U];ring
    rw [id];exact add_nonneg (mul_nonneg (sub_nonneg.mpr bu) v0)
      (mul_nonneg (mul_nonneg b0 (sq_nonneg _)) (sub_nonneg.mpr jv))
  have Hub : H0≤b*(p:ℤ)^2*V := by
    change b*U*(p*V-U*J)-p*V≤_
    nlinarith only [mul_nonneg (mul_nonneg b0 (sq_nonneg U)) j0,mul_nonneg pz v0,
      mul_le_mul_of_nonneg_right u (mul_nonneg (mul_nonneg b0 pz) v0)]
  have raw := OMA.ComplementaryNonres245212.cleared hp hq op oq pq eqn
  change P*(G k*(A0-k*H0)-K*H0)=G k*C p k V S+K*V at raw
  have clr : P*(G k*(A0-k*H0)-(k+1)*H0)=F k*V-G k*(p-1)*S := by
    dsimp only [K,C] at raw
    have fg : F k=(k:ℤ)*G k+(k+1) := by dsimp [F,G];ring
    rw [fg];linear_combination raw
  have nz : A0-k*H0≠0 := sub_ne_zero.mpr
    (OMA.ComplementaryNonres245212.original hp hq op oq pq hd ha eqn)
  have lev := OMA.ComplementaryDyad245212.level hp hq op oq pq (by omega) eqn
  have zz : z k≤3*h*b*P*Q := by dsimp [z,h,b,P,Q];exact_mod_cast lev
  have lev' : G k≤P*(3*h*b*Q) := by dsimp [G];linarith only [zz]
  have g := gap ppos v0 s0 (by omega) Hpos nz clr lev'
  change G k≤K*H0+(3*h*b*Q)*(K*V+p*S) at g
  have bp' : (p:ℤ)≤B := by omega
  have bb : b≤B := by dsimp [b];omega
  have kb' : K≤B := by dsimp [K];omega
  have bB : (1:ℤ)≤B := by omega
  have qB : Q≤(B:ℤ)^d := by dsimp [Q];exact pow_le_pow_left₀ (by omega) (by omega) _
  have VU : V≤2*h*B^d := by
    nlinarith only [vh,mul_le_mul_of_nonneg_left qB (show 0≤h by omega),
      mul_nonneg (show 0≤h by omega) qp.le]
  have SU : S≤2*(B:ℤ)^d := by nlinarith only [sh,qB,qp.le]
  have HH : K*H0≤2*h*(B:ℤ)^(d+4) := calc
    _ ≤ K*(b*p^2*V) := mul_le_mul_of_nonneg_left Hub (by dsimp [K];positivity)
    _ ≤ (B:ℤ)*(B*B^2*(2*h*B^d)) := by gcongr
    _ = _ := by rw [pow_add];ring
  have RR : 3*h*b*Q≤3*h*(B:ℤ)^(d+1) := calc
    _ ≤ 3*h*(B:ℤ)*B^d := by gcongr
    _ = _ := by rw [pow_succ];ring
  have VV : K*V+p*S≤4*h*(B:ℤ)^(d+1) := calc
    _ ≤ (B:ℤ)*(2*h*B^d)+B*(2*(B:ℤ)^d) := by gcongr
    _ ≤ _ := by
      rw [pow_succ]
      have pos := mul_nonneg (show 0≤h-1 by omega)
        (mul_nonneg (show 0≤(B:ℤ) by omega) (show 0≤(B:ℤ)^d by positivity))
      nlinarith only [pos]
  have R : (3*h*b*Q)*(K*V+p*S)≤(3*h*(B:ℤ)^(d+1))*(4*h*B^(d+1)) :=
    mul_le_mul RR VV (by dsimp [K];positivity) (by positivity)
  have rb : (3*h*(B:ℤ)^(d+1))*(4*h*B^(d+1))=12*h^2*(B:ℤ)^(2*d+2) := by
    rw [show 2*d+2=(d+1)+(d+1) by omega,pow_add];ring
  rw [rb] at R
  have pb₁ := pow_le_pow_right₀ bB (show d+4≤2*d+3 by omega)
  have pb₂ := pow_le_pow_right₀ bB (show 2*d+2≤2*d+3 by omega)
  have pb₀ : (1:ℤ)≤(B:ℤ)^(2*d+3) := one_le_pow₀ bB
  have cap : z k≤16*h^2*(B:ℤ)^(2*d+3) := by
    dsimp only [G] at g
    nlinarith only [g,HH,R,mul_le_mul_of_nonneg_left pb₁ (show 0≤2*h by omega),
      mul_le_mul_of_nonneg_left pb₂ (show 0≤12*h^2 by positivity),pb₀,
      mul_nonneg (show 0≤4*h^2-2*h-1 by nlinarith only [hh,sq_nonneg (h-1)])
        (show 0≤(B:ℤ)^(2*d+3) by positivity)]
  dsimp [z,h] at cap;exact_mod_cast cap

end OMA.ComplementaryHeight245212

end

section

/- Polynomial/exponential cutoff in the dyadic exponent. -/
namespace OMA.ComplementaryCut245212
open scoped ArithmeticFunction.sigma

private theorem scalar {h K : ℕ} (hh : 3≤h)
    (growth : 2^K≤2^(16*h^2*(2*h+2))*K^((h+1)*(2*h+1))) :
    K≤512*h^4 := by
  let T:=16*h^2*(2*h+2)
  let s:=(h+1)*(2*h+1)
  let t:=K.sqrt
  change 2^K≤2^T*K^s at growth
  by_contra! wide
  have hs : s≤4*h^2 := by
    dsimp [s];nlinarith only [hh,Nat.mul_le_mul_left h hh]
  have tbound : 2*T≤512*h^4 := by
    dsimp [T]
    have h34:=Nat.pow_le_pow_right (show 1≤h by omega) (show 3≤4 by decide)
    have h24:=Nat.pow_le_pow_right (show 1≤h by omega) (show 2≤4 by decide)
    nlinarith only [h34,h24,Nat.zero_le (h^4)]
  have ss : 4*s≤t := Nat.le_sqrt'.mpr (calc
    (4*s)^2 ≤ (4*(4*h^2))^2 := Nat.pow_le_pow_left (Nat.mul_le_mul_left _ hs) _
    _ ≤ 512*h^4 := by nlinarith only [Nat.zero_le (h^4)]
    _ ≤ K := wide.le)
  have tt : t^2≤K := Nat.sqrt_le' K
  have tt' : K<(t+1)^2 := Nat.lt_succ_sqrt' K
  have two : 2≤t := by dsimp [s] at ss;nlinarith only [ss,hh,Nat.zero_le (h^2)]
  have pk : K≤2^(2*t) := calc
    _ ≤ 2*t^2+1 := by nlinarith only [tt',Nat.mul_le_mul_left t two]
    _ ≤ _ := Nat.two_mul_sq_add_one_le_two_pow_two_mul t
  have powers := growth.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left pk s))
  rw [←pow_mul,←pow_add] at powers
  have rem := (pow_le_pow_iff_right₀ (a:=(2:ℕ)) (by decide)).mp powers
  nlinarith only [rem,tt,Nat.mul_le_mul_left t ss,wide,tbound]

theorem large {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p) (oq : 3≤q) (pq : p≠q)
    (hd : 2≤d) (ha : 2*d+4≤a)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    k+1≤512*(d+1)^4 := by
  let h:=d+1
  let K:=k+1
  let E:ℕ:=2^(16*h^2)
  let B:=E*K^(d+2)
  let D:=E*K^(d+3)
  let s:=(h+1)*(2*h+1)
  let T:=16*h^2*(2*h+2)
  have hK : 1≤K := by dsimp [K];omega
  have hh : 3≤h := by dsimp [h];omega
  have he : 1≤E := Nat.one_le_pow _ _ (by decide)
  apply scalar hh
  change 2^K≤2^T*K^s
  by_cases small : 2^K≤D^h
  · have comp : E^h≤2^T := by
      dsimp [E,T];rw [←pow_mul]
      apply Nat.pow_le_pow_right (by decide)
      exact Nat.mul_le_mul_left _ (by omega)
    have kcomp : K^((d+3)*h)≤K^s := Nat.pow_le_pow_right hK (by
      dsimp [s,h];nlinarith only [Nat.zero_le d,Nat.zero_le (d^2)])
    change 2^K≤(E*K^(d+3))^h at small
    rw [mul_pow,←pow_mul K (d+3) h] at small
    exact small.trans (Nat.mul_le_mul comp kcomp)
  · obtain ⟨pb,qb,ab,kb⟩:=OMA.ComplementaryBox245212.box hp hq op oq pq (by omega) hd eqn (lt_of_not_ge small)
    have bound := OMA.ComplementaryHeight245212.height hp hq op oq pq hd ha pb qb ab kb eqn
    change 2^K≤16*h^2*B^(2*d+3) at bound
    have initial : 16*h^2≤E := (Nat.lt_pow_self (by decide : 1<2)).le
    have eqE : E*E^(2*d+3)=2^T := by
      rw [←pow_succ'];dsimp [E,T,h];rw [←pow_mul];congr 2
    have eqK : (K^(d+2))^(2*d+3)=K^s := by dsimp [s,h];rw [←pow_mul];congr 1
    dsimp only [B] at bound
    rw [mul_pow,eqK,←mul_assoc] at bound
    exact bound.trans (Nat.mul_le_mul_right _ ((Nat.mul_le_mul_right _ initial).trans_eq eqE))

end OMA.ComplementaryCut245212

end

section
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
end

section
/- Effective height bounds from the original A245212 equality. -/
namespace OMA.DivisorHeight245212
open Finset Nat ArithmeticFunction OMA.Smooth245212 OMA.DivisorEnvelope245212
open scoped ArithmeticFunction.sigma

private theorem dyadic_moments (a : ℕ) :
    W (2^a) = a*2^(a+1)+1 ∧ σ 1 (2^a)+1 = 2^(a+1) := by
  rw [w_pow Nat.prime_two,sigma_one_apply_prime_pow Nat.prime_two]
  induction a with
  | zero => norm_num
  | succ a ih =>
    rw [sum_range_succ (fun j => 2^j*(j+1)) (a+1),
      sum_range_succ (fun j => 2^j) (a+1),ih.1,pow_succ (2:ℕ) (a+1)]
    constructor <;> nlinarith only [ih.2]

/-- At equality the odd part gives an integer target and a common rational
perturbation of the coefficients, including for an odd input (a=0). -/
theorem identity {a m : ℕ} (odd : Odd m)
    (eqn : OeisA245212.a (2^a*m)=(σ 1 (2^a*m):ℤ)) :
    (m.divisors.card:ℚ)-1 = ∑ d∈m.divisors.erase 1,
      (((a:ℚ)+((a:ℚ)+1)/(2^(a+1)-1))*(m/d).divisors.card+1)/d := by
  apply egyptian odd.pos
  have cp := (Nat.coprime_two_left.mpr odd).pow_left a
  have natBal := OMA.Abundance245212.balance (mul_ne_zero (pow_ne_zero _ (by decide)) odd.pos.ne') eqn
  rw [w_mult.map_mul_of_coprime cp,isMultiplicative_sigma.map_mul_of_coprime cp,
    isMultiplicative_sigma.map_mul_of_coprime cp,sigma_zero_apply_prime_pow Nat.prime_two,
    (dyadic_moments a).1] at natBal
  have bal := congrArg (Nat.cast : ℕ → ℚ) natBal
  have geom := congrArg (Nat.cast : ℕ → ℚ) (dyadic_moments a).2
  push_cast at bal geom
  rw [sigma_zero_apply,w_apply,sigma_one_apply (n:=m)] at bal
  push_cast at bal
  have dp : 1 < (2:ℚ)^(a+1) := one_lt_pow₀ (by norm_num) (by omega)
  field_simp [sub_ne_zero.mpr dp.ne']
  rw [pow_succ (2:ℚ) a] at bal geom ⊢
  linear_combination -bal + geom * (∑ d ∈ m.divisors, (d:ℚ))

private theorem tail_cut {m d : ℕ} (hd : d∈m.divisors) {s : Finset ℕ}
    (support : d.primeFactors ⊆ s) :
    d ∣ ∏ p∈s, p^m.factorization p := by
  have dz := (Nat.pos_of_mem_divisors hd).ne'
  obtain ⟨div,mz⟩ := Nat.mem_divisors.mp hd
  trans ∏ p∈d.primeFactors, p^m.factorization p
  · nth_rw 1 [Nat.prod_primeFactors_pow_factorization dz]
    exact Finset.prod_dvd_prod_of_dvd _ _ fun p _ =>
      pow_dvd_pow _ ((Nat.factorization_le_iff_dvd dz mz).mpr div p)
  · exact Finset.prod_dvd_prod_of_subset _ _ _ support

private def core (m : ℕ) (s : Finset ℕ) := ∏ p∈s,p^m.factorization p

private theorem prefix_pos {m : ℕ} {s : Finset ℕ} (ss : s ⊆ m.primeFactors) :
    0 < core m s :=
  Finset.prod_pos fun _ h => Nat.pow_pos (Nat.prime_of_mem_primeFactors (ss h)).pos

/-- Advance through the prime factors in order, with all exponents taken
at once. The height exponent spent on p^e is exactly e+1. -/
private theorem prime_bootstrap {m B H : ℕ} (mp : 0 < m)
    (step : ∀ s ⊆ m.primeFactors, ∀ P : ℕ, 0<P →
      (∀ p∈m.primeFactors \ s,P≤p) → B≤H*core m s ∨ P≤H*core m s) :
    B≤H^m.divisors.card := by
  classical
  let M := m.primeFactors
  let t (r : Finset ℕ) := ∏ p∈r,(m.factorization p+1)
  have aux (r : Finset ℕ) (sub : r⊆M) :
      B≤(H*core m (M\r))^(t r) := by
    induction r using Finset.strongInductionOn with | _ r ih =>
    let s := M\r
    have ss : s ⊆ M := sdiff_subset
    have rem : M\s=r := by ext x; simp [s]; grind
    have hr : 0<t r := prod_pos fun _ _ => Nat.succ_pos _
    by_cases done : B≤H*core m s
    · exact done.trans (Nat.le_self_pow hr.ne' _)
    by_cases ne : r.Nonempty
    · let p := r.min' ne
      have pr : p ∈ r := min'_mem _ _
      have ps : p ∉ s := fun h => (mem_sdiff.mp h).2 pr
      have subset := (erase_subset p r).trans sub
      have key := (step s ss p (Nat.prime_of_mem_primeFactors (sub pr)).pos
        (by rw [rem]; exact fun q hq => min'_le _ _ hq)).resolve_left done
      have insert_eq : M\(r.erase p)=insert p s := by
        ext x; simp [s]; grind
      have up : H*core m (M\(r.erase p)) ≤ (H*core m s)^(m.factorization p+1) := by
        rw [insert_eq,core,prod_insert ps,pow_succ']
        change H*(p^m.factorization p*core m s) ≤ _
        rw [show H*(p^m.factorization p*core m s)=(H*core m s)*p^m.factorization p by ring]
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left key _)
      have rest := ih (r.erase p) (erase_ssubset pr) subset
      apply rest.trans ((Nat.pow_le_pow_left up _).trans_eq ?_)
      rw [←pow_mul]
      congr 1
      exact mul_prod_erase r (fun q => m.factorization q+1) pr
    · have z := step s ss (H*core m s+1) (by omega) (by
        change ∀ p∈M\s,_
        simp [rem,not_nonempty_iff_eq_empty.mp ne])
      omega
  simpa [M,t,core,Nat.card_divisors mp.ne'] using aux M (Subset.rfl)

private theorem tail_prime {m P : ℕ} {s : Finset ℕ} (hP : ∀ p∈m.primeFactors\s,P≤p)
    {d : ℕ} (hd : d∈m.divisors) (nd : ¬d∣core m s) : P≤d := by
  by_contra! small
  apply nd (tail_cut hd ?_)
  intro p h
  by_contra out
  have hm := Nat.primeFactors_mono (Nat.mem_divisors.mp hd).1 (Nat.mem_divisors.mp hd).2 h
  exact small.not_ge ((hP p (mem_sdiff.mpr ⟨hm,out⟩)).trans (Nat.le_of_mem_primeFactors h))

private theorem counts {m d : ℕ} (hd : d ∈ m.divisors) :
    0 < (m/d).divisors.card ∧ (m/d).divisors.card ≤ m.divisors.card := by
  obtain ⟨dv,mz⟩ := Nat.mem_divisors.mp hd
  have prod := Nat.div_mul_cancel dv
  have nz : m/d≠0 := by intro h; simp [h] at prod; exact mz prod.symm
  exact ⟨card_pos.mpr ⟨1,Nat.one_mem_divisors.mpr nz⟩,
    card_le_card (Nat.divisors_subset_of_dvd mz (Nat.div_dvd_of_dvd dv))⟩

private theorem dyadic_step {a t b P : ℕ} (ht : 0<t) (hb : 0<b)
    {δ : ℚ} (δ1 : δ≤1) (δ2 : δ≤((a:ℚ)+1)/2^a)
    (lower : 1/(b:ℚ) ≤ t*(δ*t+(((a:ℚ)+δ)*t+1)/P)) :
    2^a≤4*(a+2)*t^2*b ∨ P≤4*(a+2)*t^2*b := by
  by_contra! both
  let L : ℚ := 4*(a+2:ℚ)*t^2*b
  have bp : (0:ℚ)<b := by exact_mod_cast hb
  have tp : (0:ℚ)<t := by exact_mod_cast ht
  have t1 : (1:ℚ)≤t := by exact_mod_cast ht
  have lp : 0<L := by dsimp [L]; positivity
  have ll : L≤(2:ℚ)^a := by dsimp [L]; exact_mod_cast both.1.le
  have pl : L≤(P:ℚ) := by dsimp [L]; exact_mod_cast both.2.le
  have δ3 : δ≤((a:ℚ)+1)/L := δ2.trans (by gcongr)
  have z : t*(δ*t+(((a:ℚ)+δ)*t+1)/P) ≤
      t*((((a:ℚ)+1)/L)*t+(((a:ℚ)+1)*t+1)/L) := by gcongr
  have strict : (t:ℚ)*((((a:ℚ)+1)/L)*t+(((a:ℚ)+1)*t+1)/L) < 1/b := by
    field_simp [lp.ne',bp.ne']
    dsimp [L]
    have posat : 0≤(a:ℚ)*t := by positivity
    nlinarith only [mul_pos tp bp, mul_nonneg (sub_nonneg.mpr t1) (mul_pos tp bp).le,
      mul_nonneg posat (mul_pos tp bp).le]
  exact (lower.trans z).not_gt strict

/-- At a solution the power of two has an upper bound whose exponent is
only the number of odd divisors, independent of the prime bases. -/
theorem dyadic_height {a m : ℕ} (odd : Odd m) (hm : 1 < m)
    (eqn : OeisA245212.a (2^a*m)=(σ 1 (2^a*m):ℤ)) :
    2^a≤(4*(a+2)*m.divisors.card^2)^m.divisors.card := by
  let t := m.divisors.card
  have tp : 0<t := card_pos.mpr ⟨m,Nat.mem_divisors_self _ odd.pos.ne'⟩
  apply prime_bootstrap odd.pos
  intro s ss P pp hP
  let δ : ℚ := ((a:ℚ)+1)/(2^(a+1)-1)
  have b := prefix_pos ss
  have power : (1:ℚ)≤2^a := one_le_pow₀ (by norm_num)
  have z : (0:ℚ)<2^(a+1)-1 := by rw [pow_succ]; linarith
  have δ1 : δ≤1 := by
    apply (div_le_iff₀ z).mpr
    have grow := (a+1).lt_two_pow_self
    have aux : a+1+1≤2^(a+1) := grow
    have q : (a:ℚ)+1+1≤2^(a+1) := by exact_mod_cast aux
    linarith
  have δ2 : δ≤((a:ℚ)+1)/2^a := by
    dsimp [δ]; gcongr
    rw [pow_succ]; linarith
  have en : (m.divisors.erase 1).Nonempty := ⟨m,mem_erase.mpr ⟨by omega,Nat.mem_divisors_self _ odd.pos.ne'⟩⟩
  have iden := identity odd eqn
  have target : ((t-1:ℕ):ℚ) = ∑ d∈m.divisors.erase 1,
      (((a:ℚ)+δ)*(m/d).divisors.card+1)/d := by
    rw [Nat.cast_sub (by omega : 1≤t)]
    exact iden
  exact dyadic_step tp b δ1 δ2 (truncated en b pp (card_le_card (erase_subset _ _))
    (fun _ h => Nat.pos_of_mem_divisors (mem_of_mem_erase h))
    (fun _ h => counts (mem_of_mem_erase h)) (fun _ h => tail_prime hP (mem_of_mem_erase h))
    (div_pos (by positivity) z) target)

/-- A plain integer bound on the dyadic exponent; no root finding or
exponential search is required to turn the implicit bound into a cutoff. -/
theorem exponent_cutoff {a t : ℕ} (ht : 0<t) (h : 2^a≤(4*(a+2)*t^2)^t) :
    a<t*(2*Nat.log 2 (8*t^3)+2) := by
  let x := a/t
  have lo : x*t≤a := Nat.div_mul_le_self _ _
  have hi : a<(x+1)*t := by
    have rem := Nat.mod_lt a ht
    have eqn := Nat.mod_add_div a t
    dsimp [x]; nlinarith only [rem,eqn]
  have top : a+2≤(x+2)*t := by nlinarith only [hi,ht]
  have base : 2^x≤4*(a+2)*t^2 := by
    apply (Nat.pow_le_pow_iff_left ht.ne').mp
    rw [←pow_mul]; exact (Nat.pow_le_pow_right (by decide) lo).trans h
  have scale : 2*2^x≤8*(x+2)*t^3 := by
    have b := Nat.mul_le_mul_right (4*t^2) top
    nlinarith only [base,b]
  have half : x+2 ≤ 2*2^(x-x/2) := by
    have f := (x-x/2).lt_two_pow_self
    omega
  have hhalf := Nat.mul_le_mul_left (2^(x/2)) half
  rw [show 2^(x/2)*(2*2^(x-x/2))=2*2^x by
    rw [←Nat.mul_assoc,Nat.mul_comm (2^(x/2)) 2,Nat.mul_assoc,←pow_add]
    rw [Nat.add_sub_of_le (Nat.div_le_self x 2)]] at hhalf
  have cap : 2^(x/2)≤8*t^3 := by
    apply (mul_le_mul_iff_left₀ (Nat.succ_pos (x+1))).mp
    nlinarith only [hhalf,scale]
  have logBound := Nat.le_log_of_pow_le (by decide : 1<2) cap
  apply hi.trans_le
  rw [Nat.mul_comm]
  exact Nat.mul_le_mul_left t (by omega)

/-- For unperturbed integer weights the strict gap is either absent, or
it forces the next omitted denominator to be small. -/
private theorem exact_cut {s : Finset ℕ} {w : ℕ → ℕ} {y b P t M : ℕ}
    (bp : 0<b) (pp : 0<P) (card : s.card≤t) (ds : ∀ d∈s,0<d)
    (ws : ∀ d∈s,0<w d ∧ w d≤M) (tail : ∀ d∈s,¬d∣b → P≤d)
    (idn : (y:ℚ)=∑ d∈s,(w d:ℚ)/d) :
    (∀ d∈s,d∣b) ∨ P≤b*t*M := by
  classical
  by_cases all : ∀ d∈s,d∣b
  · exact Or.inl all
  right
  push Not at all
  obtain ⟨d,hd,nd⟩ := all
  let f := s.filter (·∣b)
  let r := s\f
  have inside := filter_subset (fun d => d∣b) s
  have rest : ∀ i∈r,i∈s ∧ ¬i∣b := by
    intro i h
    obtain ⟨hs,hf⟩ := mem_sdiff.mp h
    exact ⟨hs,fun dv => hf (mem_filter.mpr ⟨hs,dv⟩)⟩
  have positive : 0<∑ i∈r,(w i:ℚ)/i := by
    apply sum_pos' (fun _ _ => by positivity)
    exact ⟨d,mem_sdiff.mpr ⟨hd,fun h => nd (mem_filter.mp h).2⟩,
      div_pos (by exact_mod_cast (ws d hd).1) (by exact_mod_cast ds d hd)⟩
  have split := sum_sdiff inside (f:=fun i => (w i:ℚ)/i)
  change (∑ i∈r,(w i:ℚ)/i)+(∑ i∈f,(w i:ℚ)/i)=_ at split
  rw [←idn] at split
  have lower := gap bp f w (fun i h => (mem_filter.mp h).2)
    (fun i h => ds i (mem_filter.mp h).1) (show (∑ i∈f,(w i:ℚ)/i)<y by linarith)
  have upper : (∑ i∈r,(w i:ℚ)/i) ≤ t*((M:ℚ)/P) := by
    calc
      _ ≤ ∑ _i∈r,(M:ℚ)/P := by
        apply sum_le_sum; intro i hi
        obtain ⟨si,ni⟩ := rest i hi
        have pe : (P:ℚ) ≤ i := by exact_mod_cast tail i si ni
        have wp : (w i:ℚ)≤M := by exact_mod_cast (ws i si).2
        gcongr
      _ ≤ _ := by
        simp only [sum_const,nsmul_eq_mul]
        gcongr
        exact (card_le_card (sdiff_subset : r⊆s)).trans card
  have le : 1/(b:ℚ) ≤ t*((M:ℚ)/P) := by linarith
  have bq : 0<(b:ℚ) := by exact_mod_cast bp
  have pq : 0<(P:ℚ) := by exact_mod_cast pp
  field_simp at le
  exact_mod_cast (show (P:ℚ) ≤ b*t*M by linarith only [le])

/-- Explicit upper bound on the odd part itself. -/
theorem odd_height {a m : ℕ} (odd : Odd m) (hm : 1 < m)
    (eqn : OeisA245212.a (2^a*m)=(σ 1 (2^a*m):ℤ)) :
    m≤((2^(a+1)-1)*(a+2)*m.divisors.card^2)^(m.divisors.card-1) := by
  let t := m.divisors.card
  let z : ℕ := 2^(a+1)-1
  let K := z*(a+2)*t^2
  let u (d : ℕ) := (m/d).divisors.card
  let w (d : ℕ) := (a*z+(a+1))*u d+z
  have tpos : 0<t := card_pos.mpr ⟨m,Nat.mem_divisors_self _ odd.pos.ne'⟩
  have grow := (a+1).lt_two_pow_self
  have az : a+1≤z := by dsimp [z]; omega
  have zp : 0<z := by omega
  have kp : 0<K := by dsimp only [K]; positivity
  have castz : (z:ℚ)=2^(a+1)-1 := by
    dsimp [z]; rw [Nat.cast_sub (by omega : 1≤(2:ℕ)^(a+1))]; push_cast; rfl
  have zq : (z:ℚ)≠0 := by exact_mod_cast zp.ne'
  have target : (((t-1)*z:ℕ):ℚ)=∑ d∈m.divisors.erase 1,(w d:ℚ)/d := by
    have idn := identity odd eqn
    rw [←castz] at idn
    push_cast [Nat.cast_sub (by omega : 1≤t)]
    rw [show (t:ℚ)-1=(m.divisors.card:ℚ)-1 from rfl,idn,sum_mul]
    apply sum_congr rfl
    intro d hd
    dsimp only [w,u]
    push_cast
    field_simp
  have cap : K*m≤K^t := by
    apply prime_bootstrap odd.pos
    intro s ss P pp hP
    have ww (d : ℕ) (h : d∈m.divisors.erase 1) : 0<w d ∧ w d≤z*(a+2)*t := by
      have c := (counts (mem_of_mem_erase h)).2
      change u d≤t at c
      constructor
      · dsimp [w]; positivity
      · calc
          w d ≤ (a*z+z)*t+z := by dsimp [w]; gcongr
          _ ≤ z*(a+2)*t := by
            have bz := Nat.mul_le_mul_left z (show 1≤t from tpos)
            nlinarith only [bz]
    rcases exact_cut (prefix_pos ss) pp (card_le_card (erase_subset _ _ ) : (m.divisors.erase 1).card≤t)
      (fun d h => Nat.pos_of_mem_divisors (mem_of_mem_erase h)) ww
      (fun d h => tail_prime hP (mem_of_mem_erase h)) target with all|bound
    · left; apply Nat.mul_le_mul_left
      exact Nat.le_of_dvd (prefix_pos ss) (all m (mem_erase.mpr ⟨by omega,Nat.mem_divisors_self _ odd.pos.ne'⟩))
    · right; apply bound.trans_eq; dsimp [K]; ring
  have eqt : t=(t-1)+1 := by omega
  rw [eqt] at cap
  rw [pow_succ'] at cap
  exact (mul_le_mul_iff_right₀ kp).mp cap

/-- Every fixed odd divisor count comes with a finite rectangular search
space given solely by that count. This does not bound t itself. -/
def exponentLimit (t : ℕ) := t*(2*Nat.log 2 (8*t^3)+2)
def coreLimit (t : ℕ) :=
  ((2^(exponentLimit t+1)-1)*(exponentLimit t+2)*t^2)^(t-1)

theorem effective_box {a m : ℕ} (odd : Odd m) (hm : 1 < m)
    (eqn : OeisA245212.a (2^a*m)=(σ 1 (2^a*m):ℤ)) :
    a<exponentLimit m.divisors.card ∧ m≤coreLimit m.divisors.card := by
  have ht : 0 < m.divisors.card := card_pos.mpr ⟨m,Nat.mem_divisors_self _ odd.pos.ne'⟩
  have ka := exponent_cutoff ht (dyadic_height odd hm eqn)
  refine ⟨ka,(odd_height odd hm eqn).trans ?_⟩
  dsimp only [coreLimit]
  gcongr <;> first | exact ka.le | decide

end OMA.DivisorHeight245212
end

section
/- The small-exponent case of the uniform dyadic bound follows from the
effective odd divisor envelope, with its constants made explicit. -/
namespace OMA.ComplementarySmall245212
open ArithmeticFunction
open scoped ArithmeticFunction.sigma

private theorem limit {t h : ℕ} (hh : 3≤h) (ht : t≤16*h^3) :
    OMA.DivisorHeight245212.exponentLimit t≤512*h^4 := by
  have he : h≤2^h := (Nat.lt_pow_self (by decide : 1<2)).le
  have base : 8*t^3≤2^(15+9*h) := calc
    _ ≤ 8*(16*(2^h)^3)^3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
      (ht.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left he 3))) 3)
    _ = _ := by rw [pow_add, Nat.mul_comm 9 h, pow_mul]; ring
  have log := Nat.log_mono_right (b:=2) base
  rw [Nat.log_pow (by decide)] at log
  unfold OMA.DivisorHeight245212.exponentLimit
  have full := Nat.mul_le_mul ht (show 2*Nat.log 2 (8*t^3)+2≤32+18*h by omega)
  nlinarith only [full,Nat.mul_le_mul_left (h^3) hh]

theorem small {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p)
    (oq : 3≤q) (pq : p≠q) (hd : 2≤d) (sm : a+1≤16*(d+1)^2)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    k+1≤512*(d+1)^4 := by
  have odd := ((hp.odd_of_ne_two (by omega)).pow (n:=a)).mul
    ((hq.odd_of_ne_two (by omega)).pow (n:=d))
  have big := Nat.one_lt_pow (by omega : d≠0) hq.one_lt
  have first := Nat.one_le_pow a p hp.pos
  have size : 1<p^a*q^d := by nlinarith only [big,Nat.mul_le_mul_right (q^d) first]
  rw [mul_assoc] at eqn
  have core := (OMA.DivisorHeight245212.effective_box odd size eqn).1
  have cp := (((Nat.coprime_primes hp hq).mpr pq).pow_left a).pow_right d
  have card : (p^a*q^d).divisors.card=(a+1)*(d+1) := by
    rw [←sigma_zero_apply,isMultiplicative_sigma.map_mul_of_coprime cp,
      sigma_zero_apply_prime_pow hp,sigma_zero_apply_prime_pow hq]
  rw [card] at core
  exact (show k+1≤_ from core).trans (limit (by omega)
    (by nlinarith only [Nat.mul_le_mul_right (d+1) sm]))

end OMA.ComplementarySmall245212
end

section
/- From the actual balance, one prescribed odd exponent bounds the power
of two, the other odd exponent, and the entire integer. -/
namespace OMA.ComplementaryFinish245212
open ArithmeticFunction OMA.DivisorHeight245212
open scoped ArithmeticFunction.sigma

theorem exponents {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p) (oq : 3≤q) (pq : p≠q)
    (hd : 2≤d) (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    k+1≤512*(d+1)^4 ∧ a+1≤32768*(d+1)^6 := by
  have cut : k+1≤512*(d+1)^4 := by
    by_cases lo : a+1≤16*(d+1)^2
    · exact OMA.ComplementarySmall245212.small hp hq op oq pq hd lo eqn
    · exact OMA.ComplementaryCut245212.large hp hq op oq pq hd
        (by nlinarith only [Nat.lt_of_not_ge lo,hd,Nat.zero_le (d^2)]) eqn
  have cap := OMA.ComplementaryExp245212.exponent hp hq op oq pq (by omega) eqn
  exact ⟨cut,cap.trans (by nlinarith only [Nat.mul_le_mul_left (64*(d+1)^2) cut])⟩

/-- Explicit cutoff for n with a prescribed complementary exponent d.
Taking the prefix maximum of the published divisor envelope avoids any
assumption about monotonicity of its logarithmic formula. -/
def height (d : ℕ) : ℕ :=
  2^(512*(d+1)^4) * (Finset.range (32768*(d+1)^6+1)).sup
    (fun b => coreLimit (b*(d+1)))

theorem bounded {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p) (oq : 3≤q) (pq : p≠q)
    (hd : 2≤d) (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    2^k*p^a*q^d≤height d := by
  have ex := exponents hp hq op oq pq hd eqn
  have odd := ((hp.odd_of_ne_two (by omega)).pow (n:=a)).mul
    ((hq.odd_of_ne_two (by omega)).pow (n:=d))
  have size₁ := Nat.one_lt_pow (by omega : d≠0) hq.one_lt
  have size : 1<p^a*q^d := by
    nlinarith only [size₁,Nat.mul_le_mul_right (q^d) (Nat.one_le_pow a p hp.pos)]
  rw [mul_assoc] at eqn ⊢
  have m := (effective_box odd size eqn).2
  have cp := (((Nat.coprime_primes hp hq).mpr pq).pow_left a).pow_right d
  have card : (p^a*q^d).divisors.card=(a+1)*(d+1) := by
    rw [←sigma_zero_apply,isMultiplicative_sigma.map_mul_of_coprime cp,
      sigma_zero_apply_prime_pow hp,sigma_zero_apply_prime_pow hq]
  rw [card] at m
  apply Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) (Nat.le_succ k |>.trans ex.1))
  exact m.trans (Finset.le_sup (f:=fun b=>coreLimit (b*(d+1)))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le ex.2)))

theorem finite (d : ℕ) (hd : 2≤d) :
    {n : ℕ | ∃ p q a k : ℕ, p.Prime ∧ q.Prime ∧ 3≤p ∧ 3≤q ∧ p≠q ∧
      n=2^k*p^a*q^d ∧ OeisA245212.a n=(σ 1 n:ℤ)}.Finite := by
  apply (Set.finite_Iic (height d)).subset
  rintro n ⟨p,q,a,k,hp,hq,op,oq,pq,rfl,eqn⟩
  exact bounded hp hq op oq pq hd eqn

end OMA.ComplementaryFinish245212
end

#print axioms OMA.ComplementaryFinish245212.exponents

#print axioms OMA.ComplementaryFinish245212.bounded

#print axioms OMA.ComplementaryFinish245212.finite
