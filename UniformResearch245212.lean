import FormalConjectures.OEIS.«245212»

/-! Uniform least-exponent bound and finiteness theorems for A245212. -/

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

/- Congruences for complete dyadic blocks in the weighted geometric sum. -/
namespace OMA.DyadicBlocks245212
open Finset Nat

def geom (p n : ℕ) := ∑ i∈range n,p^i
def weight (p n : ℕ) := ∑ i∈range n,p^i*(i+1)

private theorem split_g (p m n : ℕ) : geom p (m+n)=geom p m+p^m*geom p n := by
  simp only [geom,sum_range_add,mul_sum,pow_add]

private theorem split_w (p m n : ℕ) :
    weight p (m+n)=weight p m+p^m*(weight p n+m*geom p n) := by
  simp only [weight,geom,sum_range_add]
  congr 1
  simp only [mul_sum,←sum_add_distrib,pow_add]
  apply sum_congr rfl
  intro i _
  ring

private theorem pow_block (p h : ℕ) (ho : Odd p) :
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

private theorem y_pos {p : ℕ} (hp : Nat.Prime p) (e : ℕ) : 0<Y p (some e) := by
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

private theorem infinite_factor {p : ℕ} (hp : Nat.Prime p) (po : Odd p) :
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

theorem factor_limit (p e : ℕ → ℕ) (pm : Monotone p) (em : Monotone e)
    (hp : ∀ n,Nat.Prime (p n)) (po : ∀ n,Odd (p n)) (ed : ∀ n,4∣e n) :
    ∃ x : ℚ,OddNum x ∧ Tendsto (fun n => X (p n) (some (e n))) atTop (𝓝 x) := by
  rcases dichotomy pm with ⟨P,hP⟩|hP
  · obtain ⟨n,hn⟩ := hP.exists
    have pr : Nat.Prime P := hn ▸ hp n
    have od : Odd P := hn ▸ po n
    rcases dichotomy em with ⟨E,hE⟩|hE
    · obtain ⟨j,hj⟩ := hE.exists
      refine ⟨X P (some E),finite_factor pr od (hj ▸ ed j),?_⟩
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
      refine ⟨X P none,infinite_factor pr od,?_⟩
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
    refine ⟨1,one,tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (show Tendsto (fun n => 1+((p n:ℚ)-1)⁻¹) atTop (𝓝 1) by simpa using inv.const_add 1) ?_ ?_⟩
    · intro n
      have pp : (1:ℚ)<p n := by exact_mod_cast (hp n).one_lt
      exact le_add_of_nonneg_right (div_nonneg (sub_nonneg.mpr (y_one (hp n).one_lt _)) (by linarith))
    · intro n
      have pp : (1:ℚ)<p n := by exact_mod_cast (hp n).one_lt
      simp only [X,←one_div]
      exact add_le_add_right (div_le_div_of_nonneg_right (sub_le_self _ (y_nonneg (hp n).one_lt _))
        (by linarith)) _

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

/- Uniform separation of products of at most k odd-prime Euler factors from 2.
The bound is explicit and does not use a bound on the primes. -/
namespace OMA.Uniform245212
open Finset OMA.Smooth245212

def cap (p : ℕ) : ℚ := X p none
def caps (s : Finset ℕ) := ∏ p∈s,cap p
def cut (k c : ℕ) := 1+2^(k+1)*c
def gapDen : ℕ → ℕ
  | 0 => 1
  | k+1 => 2*gapDen k*(cut k (gapDen k))^(k+1)

private theorem gap_pos (k : ℕ) : 0 < gapDen k := by
  induction k with
  | zero => decide
  | succ k ih => simp only [gapDen,cut]; positivity

theorem cap_nonneg {p : ℕ} (hp : 3≤p) : 0≤cap p := x_nonneg (by omega) none
theorem cap_le_two {p : ℕ} (hp : 3≤p) : cap p≤2 := by
  have h : (3:ℚ)≤p := by exact_mod_cast hp
  simp only [cap,X,Y,sub_zero]
  have h' : 1/((p:ℚ)-1)≤1 := (div_le_iff₀ (by linarith)).mpr (by linarith)
  linarith

private theorem cap_den {p : ℕ} (hp : 3≤p) : cap p*((p-1:ℕ):ℚ)=p := by
  have h : (3:ℚ)≤p := by exact_mod_cast hp
  rw [Nat.cast_sub (by omega : 1≤p)]
  simp only [cap,X,Y,sub_zero,Nat.cast_one]
  field_simp [show (p:ℚ)-1≠0 by linarith only [h]]
  ring

private theorem small_gap (s : Finset ℕ) (hm : ∀ p∈s,3≤p) (ho : ∀ p∈s,Odd p) :
    1≤((∏ p∈s,(p-1 : ℕ)):ℚ)*|caps s-2| := by
  let A : ℕ := ∏ p∈s,p
  let D : ℕ := ∏ p∈s,(p-1 : ℕ)
  have odd : Odd A := by
    induction s using Finset.induction_on with
    | empty => simp [A]
    | @insert p s ps ih =>
      dsimp only [A]
      rw [prod_insert ps]
      exact (ho p (mem_insert_self _ _)).mul (ih (fun i hi => hm i (mem_insert_of_mem hi))
        (fun i hi => ho i (mem_insert_of_mem hi)))
  have distinct : A≠2*D := by obtain ⟨a,ha⟩ := odd; omega
  have integral : (1:ℚ)≤|(A:ℚ)-2*D| := by
    rcases lt_or_gt_of_ne distinct with l|g
    · have b : (A:ℚ)+1≤2*D := by exact_mod_cast l
      rw [abs_of_nonpos (by linarith)]; linarith
    · have b : (2:ℚ)*D+1≤A := by exact_mod_cast g
      rw [abs_of_nonneg (by linarith)]; linarith
  have prod : caps s*(D:ℚ)=A := by
    dsimp only [caps,A,D]
    push_cast only [Nat.cast_prod]
    rw [←prod_mul_distrib]
    exact prod_congr rfl fun p hp => cap_den (hm p hp)
  have hab : |caps s-2| * (D:ℚ)=|(A:ℚ)-2*D| := by
    calc
      _ = |caps s-2| * |(D:ℚ)| := by rw [abs_of_nonneg (a:=(D:ℚ)) (by positivity)]
      _ = _ := by rw [←abs_mul,sub_mul,prod]
  have out : (1:ℚ)≤(D:ℚ)*|caps s-2| := by rwa [mul_comm,hab]
  simpa only [D,Nat.cast_prod] using out

theorem gap (k : ℕ) (s : Finset ℕ) (hs : s.card≤k) (hm : ∀ p∈s,3≤p) (ho : ∀ p∈s,Odd p) :
    1≤(gapDen k:ℚ)*|caps s-2| := by
  induction k generalizing s with
  | zero => simp_all [gapDen,caps]; norm_num
  | succ k ih =>
    let c := gapDen k
    let L := cut k c
    have hc : 0 < c := gap_pos k
    have hL : 0<L := by dsimp [L,cut]; omega
    have form : gapDen (k+1)=2*c*L^(k+1) := rfl
    have new1 : 2*c≤gapDen (k+1) := form ▸ Nat.le_mul_of_pos_right _ (pow_pos hL _)
    have new2 : L^(k+1)≤gapDen (k+1) := form ▸ Nat.le_mul_of_pos_left _ (by positivity)
    by_cases small : ∀ p∈s,p≤L
    · have ds : ∏ p∈s,(p-1)≤L^(k+1) :=
        (Finset.prod_le_pow_card s (fun p => p-1) L (fun p hp => by have := small p hp; omega)).trans
          (Nat.pow_le_pow_right hL hs)
      exact (small_gap s hm ho).trans (mul_le_mul_of_nonneg_right
        (by exact_mod_cast ds.trans new2) (abs_nonneg _))
    push Not at small
    obtain ⟨p,ps,pL⟩ := small
    let v := s.erase p
    have sub : v⊆s := erase_subset p s
    have vk : v.card≤k := by dsimp [v]; rw [card_erase_of_mem ps]; omega
    have h := ih v vk (fun i hi => hm i (sub hi)) (fun i hi => ho i (sub hi))
    have prod : caps s=caps v*cap p := (Finset.prod_erase_mul _ _ ps).symm
    have v0 : 0≤caps v := Finset.prod_nonneg (fun i hi => cap_nonneg (hm i (sub hi)))
    have v2 : caps v≤(2:ℚ)^k := by
      unfold caps
      have small := prod_le_prod (s:=v) (fun i hi => cap_nonneg (hm i (sub hi)))
        (fun i hi => cap_le_two (hm i (sub hi)))
      simpa using small.trans (by simpa using (pow_le_pow_right₀ (a:=(2:ℚ)) (by norm_num) vk))
    have pz : (3:ℚ)≤p := by exact_mod_cast hm p ps
    have delta : caps s-caps v=caps v/((p:ℚ)-1) := by rw [prod]; simp [cap,X,Y]; ring
    have major : 2*(c:ℚ)*(2:ℚ)^k ≤ (p:ℚ)-1 := by
      have : (1+(2:ℚ)^(k+1)*c)<p := by exact_mod_cast pL
      rw [pow_succ] at this
      linarith
    have err : 2*(c:ℚ)*|caps s-caps v|≤1 := by
      rw [delta,abs_of_nonneg (div_nonneg v0 (by linarith)),←mul_div_assoc,div_le_iff₀ (by linarith only [pz])]
      have g := mul_le_mul_of_nonneg_left v2 (show 0≤2*(c:ℚ) by positivity)
      linarith only [g,major]
    have triangle := abs_sub_le (caps v) (caps s) 2
    rw [abs_sub_comm (caps v) (caps s)] at triangle
    have tm := mul_le_mul_of_nonneg_left triangle (show 0≤2*(c:ℚ) by positivity)
    have twice : (1:ℚ)≤(2*c)*|caps s-2| := by
      change (1:ℚ)≤(c:ℚ)*|caps v-2| at h
      linarith only [h,tm,err]
    exact twice.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast new1) (abs_nonneg _))

end OMA.Uniform245212

/- For fixed rank, the least exponent of any nontrivial odd solution
is uniformly bounded, regardless of its prime bases. -/
namespace OMA.Uniform245212
open Finset OMA.Smooth245212

private theorem prod_error {ι : Type*} (s : Finset ι) (a b : ι → ℚ) (d : ℚ)
    (d0 : 0≤d) (a0 : ∀ i∈s,0≤a i) (ab : ∀ i∈s,a i≤b i)
    (b2 : ∀ i∈s,b i≤2) (diff : ∀ i∈s,b i-a i≤d) :
    (∏ i∈s,b i)-(∏ i∈s,a i) ≤ s.card*2^s.card*d := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s h ih =>
    have old := ih (fun j hj => a0 j (mem_insert_of_mem hj))
      (fun j hj => ab j (mem_insert_of_mem hj)) (fun j hj => b2 j (mem_insert_of_mem hj))
      (fun j hj => diff j (mem_insert_of_mem hj))
    have hi := mem_insert_self i s
    have x0 := a0 i hi
    have step := diff i hi
    have bound := (ab i hi).trans (b2 i hi)
    have def0 := sub_nonneg.mpr (ab i hi)
    have small : (∏ j∈s,b j)≤(2:ℚ)^s.card := by
      have bs := prod_le_prod (s:=s)
        (fun j hj => (a0 j (mem_insert_of_mem hj)).trans (ab j (mem_insert_of_mem hj)))
        (fun j hj => b2 j (mem_insert_of_mem hj))
      simpa only [prod_const] using bs
    have t1 := mul_le_mul step small (prod_nonneg (fun j hj =>
        (a0 j (mem_insert_of_mem hj)).trans (ab j (mem_insert_of_mem hj)))) d0
    have t2 := mul_le_mul_of_nonneg_left old x0
    have t3 := mul_le_mul_of_nonneg_right bound (show 0≤(s.card:ℚ)*2^s.card*d by positivity)
    simp only [prod_insert h,card_insert_of_notMem h,Nat.cast_add,Nat.cast_one,pow_succ]
    nlinarith only [t1,t2,t3,mul_nonneg (show 0≤(2:ℚ)^s.card by positivity) d0]

def maxLeast (k : ℕ) := 2*gapDen k*(k*2^k+1)

theorem least (s : Finset ℕ) (ne : s.Nonempty) (K m : ℕ) (sk : s.card≤K)
    (e : ℕ → ℕ) (hp : ∀ p∈s,Nat.Prime p) (ho : ∀ p∈s,Odd p)
    (low : ∀ p∈s,m≤e p)
    (eq : (∏ p∈s,X p (some (e p)))+(∏ p∈s,Y p (some (e p)))=2) : m < maxLeast K := by
  let d : ℚ := 2/((m:ℚ)+1)
  have d0 : 0≤d := by dsimp [d]; positivity
  have pp (p) (ps : p∈s) : 3≤p := by
    have p2 := (hp p ps).two_le
    obtain ⟨t,ht⟩ := ho p ps
    omega
  have y0 (p) (ps : p∈s) := y_nonneg (hp p ps).one_lt (some (e p))
  have yl (p) (ps : p∈s) : Y p (some (e p))≤d := by
    dsimp [d]
    apply (le_div_iff₀ (by positivity)).2
    have h := OMA.CapOrder245212.y_short (hp p ps) (e p)
    have v : (m:ℚ)≤e p := by exact_mod_cast low p ps
    nlinarith only [h,mul_nonneg (y0 p ps) (sub_nonneg.mpr v)]
  have xy (p) (ps : p∈s) : 0≤cap p-X p (some (e p)) ∧ cap p-X p (some (e p))≤d := by
    have h : (3:ℚ)≤p := by exact_mod_cast pp p ps
    have diff : cap p-X p (some (e p))=Y p (some (e p))/((p:ℚ)-1) := by
      simp only [cap,X,Y]; ring
    rw [diff]
    exact ⟨div_nonneg (y0 p ps) (by linarith),(div_le_self (y0 p ps) (by linarith)).trans (yl p ps)⟩
  have err := prod_error s (fun p => X p (some (e p))) cap d d0
    (fun p ps => x_nonneg (hp p ps).one_lt _) (fun p ps => sub_nonneg.mp (xy p ps).1)
    (fun p ps => cap_le_two (pp p ps)) (fun p ps => (xy p ps).2)
  have dp := prod_le_prod (s:=s) (fun p ps => x_nonneg (hp p ps).one_lt (some (e p)))
    (fun p ps => sub_nonneg.mp (xy p ps).1)
  obtain ⟨p,pm⟩ := ne
  have yz : (∏ i∈s,Y i (some (e i)))≤d := by
    rw [←prod_erase_mul _ _ pm]
    exact (mul_le_of_le_one_left (y0 p pm)
      (prod_le_one (fun i hi => y0 i (mem_of_mem_erase hi))
        (fun i hi => y_one (hp i (mem_of_mem_erase hi)).one_lt _))).trans (yl p pm)
  have yall := prod_nonneg y0
  have est : |caps s-2| ≤ ((s.card:ℚ)*2^s.card+1)*d := by
    unfold caps
    rw [abs_le]
    constructor
    · nlinarith only [dp,eq,yz,mul_nonneg (show 0≤(s.card:ℚ)*2^s.card by positivity) d0]
    · nlinarith only [err,eq,yall,d0]
  have kd : (s.card:ℚ)*2^s.card≤(K:ℚ)*2^K :=
    mul_le_mul (by exact_mod_cast sk) (pow_le_pow_right₀ (by norm_num) sk) (by positivity) (by positivity)
  have final := (gap K s sk pp ho).trans
    (mul_le_mul_of_nonneg_left (est.trans (mul_le_mul_of_nonneg_right
      (add_le_add kd (le_refl (1:ℚ))) d0)) (by positivity))
  dsimp [d] at final
  rw [←mul_div_assoc,←mul_div_assoc,le_div_iff₀ (by positivity)] at final
  have cast : (m:ℚ)+1≤(maxLeast K:ℚ) := by
    simpa [maxLeast,mul_comm,mul_left_comm,mul_assoc] using final
  exact_mod_cast cast

open scoped ArithmeticFunction.sigma

theorem least_exponent {n K : ℕ} (hn : 1<n) (odd : Odd n) (hc : n.primeFactors.card≤K)
    (eq : OeisA245212.a n=(σ 1 n:ℤ)) :
    ∃ p∈n.primeFactors,n.factorization p < maxLeast K := by
  let s := n.primeFactors
  let p : s → ℕ := fun i => i.val
  let e : s → ℕ := fun i => n.factorization i.val
  have pprime (i : s) := Nat.prime_of_mem_primeFactors i.property
  have repr : total p e=n := (Nat.prod_primeFactors_coe_pow_factorization (by omega : n≠0)).symm
  have norm := normalized_of_eq p pprime Subtype.val_injective e (by rw [repr]; exact eq)
  change (∏ i : s,X i.val (some (n.factorization i.val)))+
    (∏ i : s,Y i.val (some (n.factorization i.val)))=2 at norm
  rw [Finset.prod_coe_sort s (fun i => X i (some (n.factorization i))),
    Finset.prod_coe_sort s (fun i => Y i (some (n.factorization i)))] at norm
  have op (i) (hi : i∈s) : Odd i := by
    have di := Nat.dvd_of_mem_primeFactors hi
    exact (Nat.Coprime.of_dvd_right di (Nat.coprime_two_left.mpr odd)).symm |> Nat.coprime_two_right.mp
  have has : s.Nonempty := ⟨n.minFac, Nat.mem_primeFactors.mpr
    ⟨Nat.minFac_prime (by omega),n.minFac_dvd,by omega⟩⟩
  by_contra! lower
  exact (least s has K (maxLeast K) hc n.factorization
    (fun _ hi => Nat.prime_of_mem_primeFactors hi) op lower norm).false

end OMA.Uniform245212

/- Odd solutions with a bounded number of primes and bounded ratio of maximum
to minimum exponent are finite. The common-exponent case includes arbitrary
powers of squarefree bases of bounded rank. -/
namespace OMA.Uniform245212
open Finset OMA.Smooth245212
open scoped ArithmeticFunction.sigma

private theorem by_pattern (K : ℕ) (e : Fin K → ℕ) (ep : ∀ i,0<e i) :
    {n : ℕ | ∃ p : Fin K → ℕ, (∀ i,Nat.Prime (p i)) ∧
      normalized p e=2 ∧ total p e=n}.Finite := by
  have finite := OMA.FixedExponents245212.finite_bases e ep 1 1 2 (by decide) (by decide)
  apply (finite.image (fun p => total p e)).subset
  rintro n ⟨p,hp,eq,rfl⟩
  exact ⟨p,⟨hp,by simpa only [one_mul,normalized] using eq⟩,rfl⟩

private theorem bounded_patterns (K L : ℕ) :
    {n : ℕ | 0<n ∧ n.primeFactors.card=K ∧ (∀ p∈n.primeFactors,n.factorization p≤L) ∧
      OeisA245212.a n=(σ 1 n:ℤ)}.Finite := by
  let E : Set (Fin K → ℕ) := {e | ∀ i,e i∈Set.Icc 1 L}
  have ef : E.Finite := Set.Finite.pi' (fun _ => Set.finite_Icc 1 L)
  apply (ef.biUnion (fun e mem => by_pattern K e (fun i => (mem i).1))).subset
  rintro n ⟨nz,card,size,eq⟩
  let S := n.primeFactors
  let p := S.orderEmbOfFin card
  let e (i : Fin K) := n.factorization (p i)
  have mem (i) : p i∈n.primeFactors := orderEmbOfFin_mem S card i
  have hp (i) := Nat.prime_of_mem_primeFactors (mem i)
  have ep (i) : 0<e i := (hp i).factorization_pos_of_dvd nz.ne' (Nat.dvd_of_mem_primeFactors (mem i))
  have repr : total p e=n := (Fintype.prod_equiv (S.orderIsoOfFin card).toEquiv _
    (fun j : S => j.val^(n.factorization j.val)) (fun _ => rfl)).trans
      (Nat.prod_primeFactors_coe_pow_factorization nz.ne').symm
  have norm := normalized_of_eq p hp p.injective e (by rw [repr]; exact eq)
  exact Set.mem_iUnion.mpr ⟨e,Set.mem_iUnion.mpr ⟨fun i => ⟨ep i,size _ (mem i)⟩,p,hp,norm,repr⟩⟩

theorem comparable_finite (K C : ℕ) :
    {n : ℕ | Odd n ∧ n.primeFactors.card≤K ∧
      (∀ p∈n.primeFactors,∀ q∈n.primeFactors,n.factorization p≤C*n.factorization q) ∧
      OeisA245212.a n=(σ 1 n:ℤ)}.Finite := by
  let L := C*maxLeast K
  apply ((Set.finite_Iic K).biUnion (fun j _ => bounded_patterns j L)).subset
  rintro n ⟨odd,card,ratio,eq⟩
  refine Set.mem_iUnion.mpr ⟨n.primeFactors.card,Set.mem_iUnion.mpr ⟨card,odd.pos,rfl,?_,eq⟩⟩
  intro p hp
  have h1 := (Nat.prime_of_mem_primeFactors hp).one_lt
  have h2 := Nat.le_of_dvd odd.pos (Nat.dvd_of_mem_primeFactors hp)
  obtain ⟨q,hq,low⟩ := least_exponent (h1.trans_le h2) odd card eq
  exact (ratio p hp q hq).trans (Nat.mul_le_mul_left C low.le)

end OMA.Uniform245212
