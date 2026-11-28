import FormalConjectures.OEIS.«245212»


/-! No A245212 equality with least odd prime eleven and exactly two odd prime factors -/

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

end

section

/- A two-sided window for the exponent at an arbitrarily large last
prime; each box uses only the three cofactor exponents. -/
namespace OMA.Large245212
open OMA.Smooth245212 OMA.Moving245212 Finset

abbrev B := Fin 3 → Band
def bases (q : ℕ) : Fin 3 → ℕ := ![3,5,q]
def singleton (p : ℕ) : Band := ⟨p,some p⟩
def lows (f : Band → Band → ℚ) (q : ℕ) (b : B) : ℚ :=
  ∏ i,f (singleton (bases q i)) (b i)
def lowerD (L G : ℚ) := max 2 ⌈G/(2-L)⌉₊
def upperD (scale U V : ℚ) := ⌊V*scale/(2-U*scale)⌋₊
def scale (R : ℕ) : ℚ := (R:ℚ)/((R:ℚ)-1)
def prefProd (f : ℕ → Option ℕ → ℚ) (q : ℕ) (e : Fin 3 → ℕ) :=
  ∏ i,f (bases q i) (some (e i))

private theorem y_both {r d : ℕ} (hr : 1<r) :
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

private theorem scale_anti {R r : ℕ} (hR : 1<R) (rr : R≤r) : scale r≤ scale R := by
  have a : (1:ℚ)<R := by exact_mod_cast hR
  have b : (R:ℚ)≤r := by exact_mod_cast rr
  apply (div_le_div_iff₀ (by linarith : 0<(r:ℚ)-1) (by linarith : 0<(R:ℚ)-1)).2
  linarith

private theorem finale {r d R : ℕ} (hR : 1<R) (hrr : R≤r) :
    1≤X r (some d) ∧ X r (some d)≤ scale R ∧
    1/((d:ℚ)+1)≤Y r (some d) ∧ Y r (some d)≤ scale R/((d:ℚ)+1) := by
  have hr := hR.trans_le hrr
  have rr : (1:ℚ)<r := by exact_mod_cast hr
  have y0 := y_nonneg hr (some d)
  have y1 := y_one hr (some d)
  have lim := y_both (d:=d) hr
  have scaleR := scale_anti hR hrr
  refine ⟨le_add_of_nonneg_right (div_nonneg (by linarith only [y1]) (by linarith)),?_,lim.1,
    lim.2.trans (div_le_div_of_nonneg_right scaleR (by positivity))⟩
  apply le_trans _ scaleR
  unfold X scale
  rw [show (r:ℚ)/(r-1)=1+1/(r-1) by field_simp [(by linarith : (r:ℚ)-1≠0)]; ring]
  exact add_le_add_right (div_le_div_of_nonneg_right (by linarith only [y0]) (by linarith)) _

structure Window (R q : ℕ) (b : B) (d : ℕ) : Prop where
  xl : lows xl q b<2
  coarse : 2≤(lows xu q b+lows yu q b/2)*scale R
  low : lowerD (lows OMA.Moving245212.xl q b) (lows yl q b)≤d+1
  high : 0<2-lows xu q b*scale R → d+1≤upperD (scale R) (lows xu q b) (lows yu q b)

theorem window {R q r d : ℕ} (hR : 1<R) (hrr : R≤r) (hq : 1<q) (hd : 0<d)
    (b : B) (e : Fin 3 → ℕ) (inb : ∀ i,(b i).Contains (e i))
    (eq : prefProd X q e*X r (some d)+prefProd Y q e*Y r (some d)=2) : Window R q b d := by
  have p1 (i : Fin 3) : 1<bases q i := by fin_cases i <;> simp [bases,hq]
  have f (i : Fin 3) := factor_bounds (p:=bases q i) (pb:=singleton (bases q i)) (e:=e i)
    (p1 i) (by simp [singleton,Band.Contains]) (inb i)
  have x0 : 0≤prefProd X q e := prod_nonneg (fun i _ => x_nonneg (p1 i) _)
  have y0 : 0<prefProd Y q e := prod_pos (fun i _ => lt_of_lt_of_le
    (by positivity : 0 < 1/((e i:ℚ)+1)) (y_both (p1 i)).1)
  have xlow : lows xl q b≤prefProd X q e := prod_le_prod (fun i _ => (f i).1) (fun i _ => (f i).2.1)
  have xup : prefProd X q e≤lows xu q b := prod_le_prod (fun i _ => (f i).1.trans (f i).2.1)
    (fun i _ => (f i).2.2.1)
  have ylow : lows yl q b≤prefProd Y q e := prod_le_prod (fun i _ => (f i).2.2.2.1)
    (fun i _ => (f i).2.2.2.2.1)
  have yup : prefProd Y q e≤lows yu q b := prod_le_prod (fun i _ => (f i).2.2.2.1.trans
    (f i).2.2.2.2.1) (fun i _ => (f i).2.2.2.2.2)
  obtain ⟨x1,xcap,y1,ycap⟩ := finale (d:=d) hR hrr
  have z : (0:ℚ)<(d:ℚ)+1 := by positivity
  have Rreal : (1:ℚ)<R := by exact_mod_cast hR
  have posR : 0<scale R := div_pos (by linarith) (by linarith)
  have low : prefProd X q e+prefProd Y q e/((d:ℚ)+1)≤2 := by
    rw [←eq,div_eq_mul_one_div]
    exact add_le_add (le_mul_of_one_le_right x0 x1) (mul_le_mul_of_nonneg_left y1 y0.le)
  have up : 2≤(lows xu q b+lows yu q b/((d:ℚ)+1))*scale R := by
    rw [←eq,add_mul,div_mul_eq_mul_div,mul_div_assoc]
    exact add_le_add (mul_le_mul xup xcap (x1.trans' zero_le_one) (x0.trans xup))
      (mul_le_mul yup ycap (y_nonneg (hR.trans_le hrr) _) (y0.le.trans yup))
  have L2 : lows xl q b<2 := by linarith only [xlow,low,div_pos y0 z]
  have two : (2:ℚ)≤(d:ℚ)+1 := by exact_mod_cast (by omega : 2≤d+1)
  have divbd := div_le_div_of_nonneg_left (y0.le.trans yup) (by norm_num : (0:ℚ)<2) two
  refine ⟨L2,up.trans (mul_le_mul_of_nonneg_right (add_le_add_right divbd _) posR.le),?_,?_⟩
  · apply max_le (by omega)
    rw [Nat.ceil_le,Nat.cast_add_one,div_le_iff₀ (by linarith)]
    have a := (div_le_iff₀ z).mp (show prefProd Y q e/((d:ℚ)+1)≤2-prefProd X q e by linarith)
    nlinarith only [a,ylow,mul_nonneg (sub_nonneg.mpr xlow) z.le]
  · intro h
    apply Nat.le_floor
    rw [Nat.cast_add_one,le_div_iff₀ h]
    have a : 2-lows xu q b*scale R≤lows yu q b*scale R/((d:ℚ)+1) := by
      rw [add_mul,div_mul_eq_mul_div] at up; linarith
    have := (le_div_iff₀ z).mp a
    linarith
end OMA.Large245212

end

section

/- Closed prime-power moments and the integer test at exact prefix leaves. -/
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

def candidate (A S T d : ℕ) := (A*d+S-1)/denom A S T d+1
def test (R A S T t : ℕ) : Bool :=
  let d:=t-1
  let D:=denom A S T d
  let p:=candidate A S T d
  decide (D=0 ∨ p<R ∨ ¬p∣A+S ∨ (1<d ∧ A*d+S=D*p) ∨ (d=1 ∧ A*d+S≠D*p))

theorem force {A S T d p : ℕ} (hs : 0<S) (hp : 1<p) (hD : 0<denom A S T d)
    (lo : denom A S T d*(p-1)<A*d+S) (hi : A*d+S≤denom A S T d*p) :
    candidate A S T d=p := by
  unfold candidate
  have low : p-1≤(A*d+S-1)/denom A S T d := (Nat.le_div_iff_mul_le hD).2 (by rw [mul_comm]; omega)
  have up : (A*d+S-1)/denom A S T d<p := (Nat.div_lt_iff_lt_mul hD).2
    (by rw [Nat.mul_comm p (denom A S T d)]; omega)
  omega

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

private theorem fit {a q f : ℕ} (ha : 0<a) (hq : q.Prime) (cop : a.Coprime q)
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

end

section

/- Certificate of a uniform gap from 2 on the infinite-exponent faces of
the three possible prime prefixes with an unbounded fourth odd prime. -/
namespace OMA.OddFaces245212
open Finset OMA.Smooth245212 OMA.Moving245212

def bases (q : ℕ) : Fin 3 → ℕ := ![3,5,q]
def limitX (p : ℕ) : ℚ := X p none
def face (q : ℕ) (k : Fin 3) (e : I → ℕ) : ℚ :=
  ∏ i : Fin 3, if i=k then limitX (bases q i) else X (bases q i) (some (e i.castSucc))
def lower (q : ℕ) (k : Fin 3) (b : Box) : ℚ :=
  ∏ i : Fin 3, if i=k then limitX (bases q i) else xl (single (bases q i)) (b i.castSucc)
def upper (q : ℕ) (k : Fin 3) (b : Box) : ℚ :=
  ∏ i : Fin 3, if i=k then limitX (bases q i) else xu (single (bases q i)) (b i.castSucc)
def gap : ℚ := 1/100000000
def Separated (x : ℚ) := x<2-gap ∨ 2+gap<x

private theorem enc {q : ℕ} (hq : 1<q) (k : Fin 3) {e : I → ℕ}
    {b : Box} (h : ∀ i,(b i).Contains (e i)) :
    lower q k b ≤ face q k e ∧ face q k e ≤ upper q k b := by
  have hp (i : Fin 3) : 1<bases q i := by fin_cases i <;> simp [bases,hq]
  have v (i : Fin 3) := factor_bounds (pb:=single (bases q i)) (eb:=b i.castSucc)
    (hp i) (p:=bases q i) (by simp [single,Band.Contains]) (h _)
  let L (i : Fin 3) := if i=k then limitX (bases q i) else xl (single (bases q i)) (b i.castSucc)
  let U (i : Fin 3) := if i=k then limitX (bases q i) else xu (single (bases q i)) (b i.castSucc)
  let F (i : Fin 3) := if i=k then limitX (bases q i) else X (bases q i) (some (e i.castSucc))
  have per (i : Fin 3) : 0≤L i ∧ L i≤F i ∧ F i≤U i := by
    by_cases hi : i=k
    · simp only [L,U,F,hi,if_true,le_refl,and_self,and_true]
      exact x_nonneg (hp k) none
    · simp only [L,U,F,hi,if_false]
      exact ⟨(v i).1,(v i).2.1,(v i).2.2.1⟩
  exact ⟨prod_le_prod (f:=L) (g:=F) (fun i _ => (per i).1) (fun i _ => (per i).2.1),
    prod_le_prod (f:=F) (g:=U) (fun i _ => (per i).1.trans (per i).2.1)
      (fun i _ => (per i).2.2)⟩

def check (q : ℕ) (k : Fin 3) : Tree → Box → Bool
| .leaf,b => decide (upper q k b<2-gap ∨ 2+gap<lower q k b)
| .split i cut l r,b => check q k l (left b i cut) && check q k r (right b i cut)

theorem sound {q : ℕ} (hq : 1<q) (k : Fin 3) (t : Tree)
    {b : Box} (cert : check q k t b=true) {e : I → ℕ} (h : ∀ i,(b i).Contains (e i)) :
    Separated (face q k e) := by
  induction t generalizing b with
  | leaf =>
    obtain up|low := of_decide_eq_true cert
    · exact Or.inl ((enc hq k h).2.trans_lt up)
    · exact Or.inr (low.trans_le (enc hq k h).1)
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

def Good (q : ℕ) (k : Fin 3) (b : Box) := ∀ e : I → ℕ,
  (∀ i,(b i).Contains (e i)) → Separated (face q k e)

theorem bisect {q : ℕ} {k : Fin 3} (b : Box) (i : I) (c : ℕ)
    (hl : Good q k (left b i c)) (hr : Good q k (right b i c)) : Good q k b := by
  intro e h
  by_cases ec : e i≤c
  · apply hl
    intro j
    by_cases ji : j=i
    · subst j; simpa [left,Band.Contains] using And.intro (h i).1 ec
    · simpa [left,ji] using h j
  · apply hr
    intro j
    by_cases ji : j=i
    · subst j; simpa [right,Band.Contains] using And.intro (by omega : c+1≤e i) (h i).2
    · simpa [right,ji] using h j

end OMA.OddFaces245212

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

end

section

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

end

section

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

end

section

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

/-- The first two positive dyadic exponents have no solutions on two distinct
odd primes. The primes and both odd exponents are unrestricted. -/
theorem no_two_small_k {k p q e f : ℕ} (lo : 0<k) (hi : k≤2) (hp : p.Prime)
    (hq : q.Prime) (po : 2<p) (pq : p<q) (ep : 0<e) (fp : 0<f) :
    OeisA245212.a (2^k*p^e*q^f)≠(σ 1 (2^k*p^e*q^f):ℤ) := by
  by_cases h3 : p=3
  · subst p; exact OMA.Moving245212.mixed_three lo ep fp hq pq
  have p5 : 5≤p := by by_contra! h; interval_cases p <;> norm_num at *
  have q7 : 7≤q := by by_contra! h; interval_cases q <;> norm_num at * <;> omega
  by_cases pair : p=5 ∧ q=7
  · obtain ⟨rfl,rfl⟩ := pair
    simpa using OMA.Smooth245212.mixed (a:=k) (b:=0) (c:=e) (d:=f) lo (by omega)
  by_cases p7 : 7≤p
  · interval_cases k <;> apply pair_small hp hq po pq ep (u:=7) (v:=7) (by decide) (by decide) p7 q7 <;> decide +kernel
  · have pval : p=5 := by interval_cases p <;> norm_num at *
    have q11 : 11≤q := by by_contra! h; interval_cases q <;> norm_num at * <;> omega
    interval_cases k <;> apply pair_small hp hq po pq ep (u:=5) (v:=11) (by decide) (by decide) p5 q11 <;> decide +kernel

#print axioms no_two_small_k
end OMA.DyadicEuler245212

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

theorem x_avg {p : ℕ} (hp : Nat.Prime p) (e : ℕ) :
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

/- Finiteness for a fixed dyadic exponent and at most two distinct odd primes. -/
namespace OMA.TwoOddFinite245212
open Nat Finset ArithmeticFunction OMA.Smooth245212
open scoped ArithmeticFunction.sigma

/-- A bound on every odd prime power that can extend this positive cofactor
at equality. The extra one also permits the empty extension. -/
def lastBound (a : ℕ) : ℕ := 1+∑ q∈(W a+σ 1 a).divisors,
  ((W a:ℤ)-((q:ℤ)-1)*(σ 1 a:ℤ)).natAbs

theorem last_power_le {a q f : ℕ} (ha : 0<a) (hq : q.Prime) (odd : q≠2)
    (cop : a.Coprime q) (hf : 0<f) (eq : OeisA245212.a (a*q^f)=(σ 1 (a*q^f):ℤ)) :
    q^f≤lastBound a := by
  have divides := OMA.OddCofactor245212.last_dvd ha hq cop hf eq
  have spos := sigma_pos 1 a ha.ne'
  have member := mem_divisors.mpr ⟨divides,by omega⟩
  have bound := OMA.PrimePowerDiv245212.cofactor_bound ha hq odd cop f eq
  have part := single_le_sum (f:=fun q : ℕ =>
    ((W a:ℤ)-((q:ℤ)-1)*(σ 1 a:ℤ)).natAbs) (fun i _ => Nat.zero_le _) member
  unfold lastBound
  omega

private theorem extend {k m r : ℕ} (om : Odd m) (hr : r∈m.primeFactors)
    (rank : m.primeFactors.card≤2) (eq : OeisA245212.a (2^k*m)=(σ 1 (2^k*m):ℤ)) :
    m≤r^(m.factorization r)*lastBound (2^k*r^(m.factorization r)) := by
  let F := m.primeFactors.erase r
  have card : F.card≤1 := by dsimp [F]; rw [card_erase_of_mem hr]; omega
  have repr : m=r^(m.factorization r)*∏ q∈F,q^(m.factorization q) := by
    calc
      m = ∏ q∈m.primeFactors,q^(m.factorization q) := Nat.prod_primeFactors_pow_factorization om.pos.ne'
      _ = _ := (prod_erase_mul _ _ hr).symm.trans (mul_comm _ _)
  have rpr := prime_of_mem_primeFactors hr
  rcases F.eq_empty_or_nonempty with empty|⟨q,hq⟩
  · rw [empty,prod_empty,mul_one] at repr
    exact repr.trans_le (Nat.le_mul_of_pos_right _ (by unfold lastBound; omega))
  · have singleton : F={q} := by
      ext x
      simpa only [mem_singleton] using
        (show x∈F ↔ x=q from ⟨fun hx => card_le_one.mp card x hx q hq,fun h => h ▸ hq⟩)
    rw [singleton,prod_singleton] at repr
    have qmem := (mem_erase.mp hq).2
    have qp := prime_of_mem_primeFactors qmem
    have qodd := Nat.coprime_two_left.mp
      ((Nat.coprime_two_left.mpr om).of_dvd_right (dvd_of_mem_primeFactors qmem))
    have nottwo : q≠2 := by intro z; rw [z] at qodd; exact (by decide : ¬Odd 2) qodd
    have cb : (2^k*r^(m.factorization r)).Coprime q :=
      ((Nat.coprime_two_left.mpr qodd).pow_left k).mul_left
        (((Nat.coprime_primes rpr qp).mpr (mem_erase.mp hq).1.symm).pow_left _)
    have ep := qp.factorization_pos_of_dvd om.pos.ne' (dvd_of_mem_primeFactors qmem)
    have pos : 0<2^k*r^(m.factorization r) := by have := rpr.pos; positivity
    have target : 2^k*m=2^k*r^(m.factorization r)*q^(m.factorization q) := by
      exact (congrArg (2^k*·) repr).trans (mul_assoc _ _ _).symm
    rw [target] at eq
    exact repr.trans_le (Nat.mul_le_mul_left _ (last_power_le pos qp nottwo cb ep eq))

/-- Both odd primes and their exponents are free; only the power of two is fixed. -/
theorem finite_two (k : ℕ) : {m : ℕ | Odd m ∧ m.primeFactors.card≤2 ∧
    OeisA245212.a (2^k*m)=(σ 1 (2^k*m):ℤ)}.Finite := by
  obtain ⟨B,atom⟩ := OMA.BoundedAtom245212.bounded_atom k 2
  let F := ⋃ r∈Set.Iic B, ⋃ e∈Set.Iic B, Set.Iic (r^e*lastBound (2^k*r^e))
  have fin : F.Finite := (Set.finite_Iic B).biUnion fun r _ =>
    (Set.finite_Iic B).biUnion fun e _ => Set.finite_Iic _
  apply ((OMA.SquareFinite245212.square_finite k 2).union fin).subset
  rintro m ⟨om,rank,eq⟩
  by_cases sq : IsSquare m
  · exact Or.inl ⟨om,sq,rank,eq⟩
  · obtain ⟨r,hr,_,rb,eb⟩ := atom m om sq rank eq
    exact Or.inr (Set.mem_iUnion₂.mpr ⟨r,rb,Set.mem_iUnion₂.mpr
      ⟨m.factorization r,eb,extend om hr rank eq⟩⟩)

#print axioms finite_two
end OMA.TwoOddFinite245212

end

section

/- An upper bound on the power of two in terms of each odd prime divisor. -/
namespace OMA.DyadicLeast245212
open Finset Nat ArithmeticFunction OMA.Smooth245212
open scoped ArithmeticFunction.sigma
open OMA.FixedExponents245212 (x_avg)
open OMA.FixedExponents245212 (y_pos)

def term (p e : ℕ) : ℚ := (e:ℚ)/(((e:ℚ)+1)*p)

private theorem x_two_terms {p e : ℕ} (hp : p.Prime) (he : 0<e) :
    1+term p e ≤ X p (some e) := by
  rw [OMA.FixedExponents245212.x_avg hp]
  apply (le_div_iff₀ (by positivity)).mpr
  let z (i : ℕ) := ((e-i+1:ℕ):ℚ)*(p:ℚ)⁻¹^i
  have sub : range 2⊆range (e+1) := range_subset_range.mpr (by omega)
  have b := sum_le_sum_of_subset_of_nonneg (f:=z) sub (fun _ _ _ => by dsimp [z]; positivity)
  refine le_trans ?_ b
  simp only [sum_range_succ,sum_range_zero,zero_add,pow_zero,pow_one,mul_one,z,Nat.sub_zero,
    Nat.cast_add,Nat.cast_one,Nat.cast_sub (show 1≤e by omega)]
  have pp : (p:ℚ)≠0 := by exact_mod_cast hp.ne_zero
  unfold term
  field_simp
  ring_nf
  exact le_rfl

private theorem sum_le_product {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (p e : ι → ℕ) (hp : ∀ i,(p i).Prime) (he : ∀ i,0<e i) :
    1+∑ i∈s,term (p i) (e i)≤∏ i∈s,X (p i) (some (e i)) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [sum_insert hi,prod_insert hi]
    have t0 (j) : 0≤term (p j) (e j) := by unfold term; positivity
    have s0 := sum_nonneg (s:=s) (fun j _ => t0 j)
    have b := mul_le_mul (x_two_terms (hp i) (he i)) ih (by linarith only [s0]) (x_nonneg (hp i).one_lt _)
    exact (show 1+(term (p i) (e i)+∑ j∈s,term (p j) (e j))≤_ by
      nlinarith only [mul_nonneg (t0 i) s0]).trans b

private theorem vector {K : ℕ} (k : ℕ) (p e : Fin K → ℕ) (hp : ∀ i,(p i).Prime)
    (he : ∀ i,0<e i) (eq : X 2 (some k)*(∏ i,X (p i) (some (e i)))+
      Y 2 (some k)*(∏ i,Y (p i) (some (e i)))=2) :
    (k:ℚ)*(∑ i,term (p i) (e i))<1 := by
  let c := X 2 (some k)
  let d := Y 2 (some k)
  let S := ∑ i,term (p i) (e i)
  have d0 : 0<d := OMA.FixedExponents245212.y_pos Nat.prime_two k
  have cd : c+d=2 := by dsimp [c,d,X]; norm_num; ring
  have kd : (k:ℚ)*d≤c := by
    have h := OMA.CapOrder245212.y_short prime_two k
    change d*((k:ℚ)+1)<2 at h
    linarith only [cd,h]
  have ys := prod_pos (s:=univ) (fun i _ => OMA.FixedExponents245212.y_pos (hp i) (e i))
  have s0 : 0≤S := sum_nonneg (fun i _ => by unfold term; positivity)
  have b := mul_le_mul_of_nonneg_left (sum_le_product univ p e hp he) (x_nonneg (by decide : 1<2) (some k))
  change c*(1+S)≤c*_ at b
  change c*_+d*_=2 at eq
  apply (mul_lt_mul_iff_right₀ d0).mp
  nlinarith only [eq,cd,b,mul_pos d0 ys,mul_le_mul_of_nonneg_right kd s0]

/-- The first two terms of each weighted prime factor already constrain
all odd prime reciprocals, independently of the divisor count. -/
theorem reciprocal_sum {k m : ℕ} (om : Odd m)
    (eq : OeisA245212.a (2^k*m)=(σ 1 (2^k*m):ℤ)) :
    (k:ℚ)*(∑ q∈m.primeFactors,term q (m.factorization q))<1 := by
  let F := m.primeFactors
  let p := F.orderEmbOfFin rfl
  let e (i : Fin F.card) := m.factorization (p i)
  have mem (i : Fin F.card) : p i∈m.primeFactors := orderEmbOfFin_mem F rfl i
  have hp (i) := prime_of_mem_primeFactors (mem i)
  have po (i) := Nat.coprime_two_left.mp ((Nat.coprime_two_left.mpr om).of_dvd_right
    (dvd_of_mem_primeFactors (mem i)))
  have ep (i) := (hp i).factorization_pos_of_dvd om.pos.ne' (dvd_of_mem_primeFactors (mem i))
  have repr : total p e=m :=
    (Fintype.prod_equiv (F.orderIsoOfFin rfl).toEquiv _
      (fun j : F => j.val^(m.factorization j.val)) (fun _ => rfl)).trans
      (Nat.prod_primeFactors_coe_pow_factorization om.pos.ne').symm
  have sm := (Fintype.sum_equiv (F.orderIsoOfFin rfl).toEquiv (fun i => term (p i) (e i))
    (fun j : F => term j.val (m.factorization j.val)) (fun _ => rfl)).trans
    (Finset.sum_coe_sort F (fun q => term q (m.factorization q)))
  rw [←sm]
  exact vector k p e hp ep (OMA.BoundedAtom245212.normalized_dyadic k p e hp po p.injective
    (by rw [repr]; exact eq))

theorem exponent_lt_twice_prime {k m q : ℕ} (om : Odd m) (hq : q∈m.primeFactors)
    (eq : OeisA245212.a (2^k*m)=(σ 1 (2^k*m):ℤ)) : k<2*q := by
  have h := reciprocal_sum om eq
  have pr := prime_of_mem_primeFactors hq
  have ep := pr.factorization_pos_of_dvd om.pos.ne' (dvd_of_mem_primeFactors hq)
  have one := single_le_sum (f:=fun q => term q (m.factorization q)) (fun i _ => by unfold term; positivity) hq
  have ratio := (mul_le_mul_of_nonneg_left one (Nat.cast_nonneg k : (0:ℚ)≤k)).trans_lt h
  let e := m.factorization q
  have he : (1:ℚ)≤e := by exact_mod_cast ep
  have qp : (0:ℚ)<q := by exact_mod_cast pr.pos
  change (k:ℚ)*((e:ℚ)/((e+1)*q))<1 at ratio
  rw [←mul_div_assoc,div_lt_iff₀ (by positivity),one_mul] at ratio
  by_contra! high
  have excess := mul_le_mul_of_nonneg_right (show (2:ℚ)*q≤k by exact_mod_cast high) (le_trans (by norm_num : (0:ℚ)≤1) he)
  nlinarith only [ratio,excess,mul_nonneg qp.le (sub_nonneg.mpr he)]

/-- Now the dyadic exponent can vary as well: only one of the odd primes is fixed. -/
theorem finite_with_prime (q : ℕ) : {n : ℕ | ∃ k m : ℕ, n=2^k*m ∧ Odd m ∧
    q∈m.primeFactors ∧ m.primeFactors.card≤2 ∧ OeisA245212.a n=(σ 1 n:ℤ)}.Finite := by
  apply ((Set.finite_Iio (2*q)).biUnion (fun k _ =>
    (OMA.TwoOddFinite245212.finite_two k).image (fun m => 2^k*m))).subset
  rintro n ⟨k,m,rfl,om,hq,rank,eq⟩
  exact Set.mem_iUnion₂.mpr ⟨k,exponent_lt_twice_prime om hq eq,⟨m,⟨om,rank,eq⟩,rfl⟩⟩

#print axioms reciprocal_sum
#print axioms finite_with_prime
end OMA.DyadicLeast245212

end

section

/- Finite kernel checks for fixed-dyadic two-prime exclusions, including
the unbounded-prime case. Only one exponent is enumerated at fixed bases. -/
namespace OMA.PairSweep245212
open Nat Finset ArithmeticFunction OMA.Smooth245212 OMA.Large245212 OMA.PairExtension245212
open scoped ArithmeticFunction.sigma
open OMA.Large245212 (moments)
open OMA.FixedExponents245212 (y_pos)

def run (test : ℕ → ℕ → ℕ → Bool) (k p e : ℕ) :=
  test (wt 2 k*wt p e) (sig 2 k*sig p e) (OMA.Large245212.tax 2 k*OMA.Large245212.tax p e)

private theorem run_true {k p e : ℕ} (hp : p.Prime) (po : 2<p) (test : ℕ → ℕ → ℕ → Bool)
    (ok : run test k p e=true) :
    test (W (2^k*p^e)) (σ 1 (2^k*p^e)) ((2^k*p^e)*(σ 0 (2^k*p^e)))=true := by
  have cp := (((Nat.coprime_primes prime_two hp).mpr (by omega)).pow_left k).pow_right e
  rw [w_mult.map_mul_of_coprime cp,isMultiplicative_sigma.map_mul_of_coprime cp,
    isMultiplicative_sigma.map_mul_of_coprime cp,sigma_zero_apply_prime_pow prime_two,
    sigma_zero_apply_prime_pow hp]
  have two := OMA.Large245212.moments prime_two k
  have odd := OMA.Large245212.moments hp e
  simpa [run,two.1,two.2,odd.1,odd.2,OMA.Large245212.tax,mul_comm,mul_assoc,mul_left_comm] using ok

private theorem cop {k p q e : ℕ} (hp : p.Prime) (hq : q.Prime) (oq : 2<q) (diff : p≠q) :
    (2^k*p^e).Coprime q := (((Nat.coprime_primes prime_two hq).mpr (by omega)).pow_left k).mul_left
      (((Nat.coprime_primes hp hq).mpr diff).pow_left e)

private theorem test_free {k p q e f : ℕ} (hp : p.Prime) (hq : q.Prime) (po : 2<p) (pq : p<q)
    (fp : 0<f) (ok : run (free (p+1)) k p e=true) :
    OeisA245212.a (2^k*p^e*q^f)≠(σ 1 (2^k*p^e*q^f):ℤ) :=
  free_sound (by have := hp.pos; positivity) hq (by omega) (cop hp hq (by omega) pq.ne) fp pq
    (run_true hp po _ ok)

private theorem test_known {k p q e f : ℕ} (hp : p.Prime) (hq : q.Prime) (po : 2<p)
    (qo : 2<q) (diff : p≠q) (fp : 0<f) (ok : run (fun a s t => known a s t q) k p e=true) :
    OeisA245212.a (2^k*p^e*q^f)≠(σ 1 (2^k*p^e*q^f):ℤ) :=
  known_sound (by have := hp.pos; positivity) hq (by omega) (cop hp hq qo diff) fp
    (run_true hp po _ ok)

private theorem x_mono {p : ℕ} (hp : 1<p) {e f : ℕ} (ef : e≤f) : X p (some e)≤X p (some f) := by
  have pp : (1:ℚ)<p := by exact_mod_cast hp
  unfold X; gcongr; exact y_anti hp ef

private theorem strict {k p q e f : ℕ} (hp : p.Prime) (hq : q.Prime) (po : 2<p) (pq : p<q)
    (eq : OeisA245212.a (2^k*p^e*q^f)=(σ 1 (2^k*p^e*q^f):ℤ)) :
    X 2 (some k)*(X p (some e)*X q (some f))<2 := by
  have := OMA.DyadicEuler245212.pair_norm k p q e f hp hq po pq eq
  exact lt_of_lt_of_eq (lt_add_of_pos_right _ (mul_pos (OMA.FixedExponents245212.y_pos prime_two k)
    (mul_pos (OMA.FixedExponents245212.y_pos hp e) (OMA.FixedExponents245212.y_pos hq f)))) this

def many (test : ℕ → ℕ → ℕ → Bool) (k p B : ℕ) :=
  (List.range B).all fun i => run test k p (i+1)

private theorem each {test : ℕ → ℕ → ℕ → Bool} {k p B e : ℕ}
    (all : many test k p B=true) (ep : 0<e) (eb : e≤B) : run test k p e=true := by
  obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero ep.ne'
  exact List.all_eq_true.mp all i (List.mem_range.mpr (by omega))

/-- Above B the smaller prime's weighted factor already crosses 2/c.
Below B recover the unknown last prime, once per possible last exponent. -/
theorem free_case {k p q e f B : ℕ} (hp : p.Prime) (hq : q.Prime) (po : 2<p) (pq : p<q)
    (ep : 0<e) (fp : 0<f) (high : 2≤X 2 (some k)*X p (some (B+1)))
    (check : many (free (p+1)) k p B=true) :
    OeisA245212.a (2^k*p^e*q^f)≠(σ 1 (2^k*p^e*q^f):ℤ) := by
  by_cases eb : e≤B
  · exact test_free hp hq po pq fp (each check ep eb)
  intro eq
  have q1 : 1≤X q (some f) := le_add_of_nonneg_right (div_nonneg (sub_nonneg.mpr (y_one hq.one_lt _))
    (sub_nonneg.mpr (by exact_mod_cast hq.one_le)))
  have step := mul_le_mul (x_mono hp.one_lt (by omega : B+1≤e)) q1 (by norm_num) (x_nonneg hp.one_lt _)
  rw [mul_one] at step
  exact ((high.trans (mul_le_mul_of_nonneg_left step (x_nonneg (by decide) _))).not_gt
    (strict hp hq po pq eq))

/-- Both bases are fixed. At least one exponent must be small; from it
the signed reverse-digit identity determines the other exponent. -/
theorem known_case {k p q e f B : ℕ} (hp : p.Prime) (hq : q.Prime) (po : 2<p) (pq : p<q)
    (ep : 0<e) (fp : 0<f)
    (high : 2≤X 2 (some k)*(X p (some (B+1))*X q (some (B+1))))
    (left : many (fun a s t => known a s t q) k p B=true)
    (right : many (fun a s t => known a s t p) k q B=true) :
    OeisA245212.a (2^k*p^e*q^f)≠(σ 1 (2^k*p^e*q^f):ℤ) := by
  by_cases eb : e≤B
  · exact test_known hp hq po (by omega) pq.ne fp (each left ep eb)
  by_cases fb : f≤B
  · simpa only [mul_right_comm (2^k)] using
      test_known hq hp (po.trans pq) po pq.ne' ep (each right fp fb)
  intro eq
  have steps := mul_le_mul (x_mono hp.one_lt (by omega : B+1≤e)) (x_mono hq.one_lt (by omega : B+1≤f))
    (x_nonneg hq.one_lt _) (x_nonneg hp.one_lt _)
  exact (high.trans (mul_le_mul_of_nonneg_left steps (x_nonneg (by decide) _))).not_gt (strict hp hq po pq eq)

end OMA.PairSweep245212

end

section

/- No A245212 equality with least odd prime 11 and exactly two odd primes. -/
namespace OMA.Least11Pair245212
open Nat Finset ArithmeticFunction OMA.PairSweep245212
open scoped ArithmeticFunction.sigma

set_option maxHeartbeats 50000000 in
private theorem at_0 {q e f : ℕ} (hq : q.Prime) (pq : 11<q) (ep : 0<e) (fp : 0<f) :
    OeisA245212.a (2^0*11^e*q^f)≠(σ 1 (2^0*11^e*q^f):ℤ) := by
  by_cases big : 12≤q
  · exact OMA.DyadicEuler245212.pair_small (by decide) hq (by decide) pq ep (u:=11) (v:=12)
      (by decide) (by decide) le_rfl big (by decide +kernel)
  interval_cases q <;> norm_num at *

set_option maxHeartbeats 50000000 in
private theorem at_1 {q e f : ℕ} (hq : q.Prime) (pq : 11<q) (ep : 0<e) (fp : 0<f) :
    OeisA245212.a (2^1*11^e*q^f)≠(σ 1 (2^1*11^e*q^f):ℤ) := by
  by_cases big : 12≤q
  · exact OMA.DyadicEuler245212.pair_small (by decide) hq (by decide) pq ep (u:=11) (v:=12)
      (by decide) (by decide) le_rfl big (by decide +kernel)
  interval_cases q <;> norm_num at *

set_option maxHeartbeats 50000000 in
private theorem at_2 {q e f : ℕ} (hq : q.Prime) (pq : 11<q) (ep : 0<e) (fp : 0<f) :
    OeisA245212.a (2^2*11^e*q^f)≠(σ 1 (2^2*11^e*q^f):ℤ) := by
  by_cases big : 12≤q
  · exact OMA.DyadicEuler245212.pair_small (by decide) hq (by decide) pq ep (u:=11) (v:=12)
      (by decide) (by decide) le_rfl big (by decide +kernel)
  interval_cases q <;> norm_num at *

set_option maxHeartbeats 50000000 in
private theorem at_3 {q e f : ℕ} (hq : q.Prime) (pq : 11<q) (ep : 0<e) (fp : 0<f) :
    OeisA245212.a (2^3*11^e*q^f)≠(σ 1 (2^3*11^e*q^f):ℤ) := by
  by_cases big : 12≤q
  · exact OMA.DyadicEuler245212.pair_small (by decide) hq (by decide) pq ep (u:=11) (v:=12)
      (by decide) (by decide) le_rfl big (by decide +kernel)
  interval_cases q <;> norm_num at *

set_option maxHeartbeats 50000000 in
private theorem at_4 {q e f : ℕ} (hq : q.Prime) (pq : 11<q) (ep : 0<e) (fp : 0<f) :
    OeisA245212.a (2^4*11^e*q^f)≠(σ 1 (2^4*11^e*q^f):ℤ) := by
  by_cases big : 12≤q
  · exact OMA.DyadicEuler245212.pair_small (by decide) hq (by decide) pq ep (u:=11) (v:=12)
      (by decide) (by decide) le_rfl big (by decide +kernel)
  interval_cases q <;> norm_num at *

set_option maxHeartbeats 50000000 in
private theorem at_5 {q e f : ℕ} (hq : q.Prime) (pq : 11<q) (ep : 0<e) (fp : 0<f) :
    OeisA245212.a (2^5*11^e*q^f)≠(σ 1 (2^5*11^e*q^f):ℤ) := by
  by_cases big : 13≤q
  · exact OMA.DyadicEuler245212.pair_small (by decide) hq (by decide) pq ep (u:=11) (v:=13)
      (by decide) (by decide) le_rfl big (by decide +kernel)
  interval_cases q <;> norm_num at *

set_option maxHeartbeats 50000000 in
private theorem at_6 {q e f : ℕ} (hq : q.Prime) (pq : 11<q) (ep : 0<e) (fp : 0<f) :
    OeisA245212.a (2^6*11^e*q^f)≠(σ 1 (2^6*11^e*q^f):ℤ) := by
  by_cases big : 18≤q
  · exact OMA.DyadicEuler245212.pair_small (by decide) hq (by decide) pq ep (u:=11) (v:=18)
      (by decide) (by decide) le_rfl big (by decide +kernel)
  have cases : q=13 ∨ q=17 := by
    interval_cases q <;> norm_num at *
  rcases cases with rfl|rfl
  · apply known_case (B:=7) (by decide) hq (by decide) pq ep fp <;> decide +kernel
  · apply known_case (B:=51) (by decide) hq (by decide) pq ep fp <;> decide +kernel

set_option maxHeartbeats 50000000 in
private theorem at_7 {q e f : ℕ} (hq : q.Prime) (pq : 11<q) (ep : 0<e) (fp : 0<f) :
    OeisA245212.a (2^7*11^e*q^f)≠(σ 1 (2^7*11^e*q^f):ℤ) := by
  by_cases big : 28≤q
  · exact OMA.DyadicEuler245212.pair_small (by decide) hq (by decide) pq ep (u:=11) (v:=28)
      (by decide) (by decide) le_rfl big (by decide +kernel)
  have cases : q=13 ∨ q=17 ∨ q=19 ∨ q=23 := by
    interval_cases q <;> norm_num at *
  rcases cases with rfl|rfl|rfl|rfl
  · apply known_case (B:=3) (by decide) hq (by decide) pq ep fp <;> decide +kernel
  · apply known_case (B:=6) (by decide) hq (by decide) pq ep fp <;> decide +kernel
  · apply known_case (B:=8) (by decide) hq (by decide) pq ep fp <;> decide +kernel
  · apply known_case (B:=20) (by decide) hq (by decide) pq ep fp <;> decide +kernel

set_option maxHeartbeats 50000000 in
private theorem at_8 {q e f : ℕ} (hq : q.Prime) (pq : 11<q) (ep : 0<e) (fp : 0<f) :
    OeisA245212.a (2^8*11^e*q^f)≠(σ 1 (2^8*11^e*q^f):ℤ) := by
  by_cases big : 46≤q
  · exact OMA.DyadicEuler245212.pair_small (by decide) hq (by decide) pq ep (u:=11) (v:=46)
      (by decide) (by decide) le_rfl big (by decide +kernel)
  have cases : q=13 ∨ q=17 ∨ q=19 ∨ q=23 ∨ q=29 ∨ q=31 ∨ q=37 ∨ q=41 ∨ q=43 := by
    interval_cases q <;> norm_num at *
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · apply known_case (B:=2) (by decide) hq (by decide) pq ep fp <;> decide +kernel
  · apply known_case (B:=3) (by decide) hq (by decide) pq ep fp <;> decide +kernel
  · apply known_case (B:=3) (by decide) hq (by decide) pq ep fp <;> decide +kernel
  · apply known_case (B:=5) (by decide) hq (by decide) pq ep fp <;> decide +kernel
  · apply known_case (B:=9) (by decide) hq (by decide) pq ep fp <;> decide +kernel
  · apply known_case (B:=11) (by decide) hq (by decide) pq ep fp <;> decide +kernel
  · apply known_case (B:=23) (by decide) hq (by decide) pq ep fp <;> decide +kernel
  · apply known_case (B:=49) (by decide) hq (by decide) pq ep fp <;> decide +kernel
  · apply known_case (B:=94) (by decide) hq (by decide) pq ep fp <;> decide +kernel

set_option maxHeartbeats 50000000 in
private theorem at_9 {q e f : ℕ} (hq : q.Prime) (pq : 11<q) (ep : 0<e) (fp : 0<f) :
    OeisA245212.a (2^9*11^e*q^f)≠(σ 1 (2^9*11^e*q^f):ℤ) := by
  by_cases big : 102≤q
  · exact OMA.DyadicEuler245212.pair_small (by decide) hq (by decide) pq ep (u:=11) (v:=102)
      (by decide) (by decide) le_rfl big (by decide +kernel)
  have cases : q=13 ∨ q=17 ∨ q=19 ∨ q=23 ∨ q=29 ∨ q=31 ∨ q=37 ∨ q=41 ∨ q=43 ∨ q=47 ∨ q=53 ∨ q=59 ∨ q=61 ∨ q=67 ∨ q=71 ∨ q=73 ∨ q=79 ∨ q=83 ∨ q=89 ∨ q=97 ∨ q=101 := by
    interval_cases q <;> norm_num at *
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · apply known_case (B:=1) (by decide) hq (by decide) pq ep fp <;> decide +kernel
  · apply known_case (B:=2) (by decide) hq (by decide) pq ep fp <;> decide +kernel
  · apply known_case (B:=2) (by decide) hq (by decide) pq ep fp <;> decide +kernel
  · apply known_case (B:=3) (by decide) hq (by decide) pq ep fp <;> decide +kernel
  · apply known_case (B:=4) (by decide) hq (by decide) pq ep fp <;> decide +kernel
  · apply known_case (B:=4) (by decide) hq (by decide) pq ep fp <;> decide +kernel
  · apply known_case (B:=6) (by decide) hq (by decide) pq ep fp <;> decide +kernel
  · apply known_case (B:=7) (by decide) hq (by decide) pq ep fp <;> decide +kernel
  · apply known_case (B:=8) (by decide) hq (by decide) pq ep fp <;> decide +kernel
  · apply known_case (B:=9) (by decide) hq (by decide) pq ep fp <;> decide +kernel
  · apply known_case (B:=12) (by decide) hq (by decide) pq ep fp <;> decide +kernel
  · apply known_case (B:=15) (by decide) hq (by decide) pq ep fp <;> decide +kernel
  · apply known_case (B:=16) (by decide) hq (by decide) pq ep fp <;> decide +kernel
  · apply known_case (B:=21) (by decide) hq (by decide) pq ep fp <;> decide +kernel
  · apply known_case (B:=25) (by decide) hq (by decide) pq ep fp <;> decide +kernel
  · apply known_case (B:=28) (by decide) hq (by decide) pq ep fp <;> decide +kernel
  · apply known_case (B:=39) (by decide) hq (by decide) pq ep fp <;> decide +kernel
  · apply known_case (B:=50) (by decide) hq (by decide) pq ep fp <;> decide +kernel
  · apply known_case (B:=81) (by decide) hq (by decide) pq ep fp <;> decide +kernel
  · apply known_case (B:=261) (by decide) hq (by decide) pq ep fp <;> decide +kernel
  · apply known_case (B:=12946) (by decide) hq (by decide) pq ep fp <;> decide +kernel

set_option maxHeartbeats 50000000 in
private theorem at_10 {q e f : ℕ} (hq : q.Prime) (pq : 11<q) (ep : 0<e) (fp : 0<f) :
    OeisA245212.a (2^10*11^e*q^f)≠(σ 1 (2^10*11^e*q^f):ℤ) := by
  apply free_case (B:=2047) (by decide) hq (by decide) pq ep fp <;> decide +kernel

set_option maxHeartbeats 50000000 in
private theorem at_11 {q e f : ℕ} (hq : q.Prime) (pq : 11<q) (ep : 0<e) (fp : 0<f) :
    OeisA245212.a (2^11*11^e*q^f)≠(σ 1 (2^11*11^e*q^f):ℤ) := by
  apply free_case (B:=11) (by decide) hq (by decide) pq ep fp <;> decide +kernel

set_option maxHeartbeats 50000000 in
private theorem at_12 {q e f : ℕ} (hq : q.Prime) (pq : 11<q) (ep : 0<e) (fp : 0<f) :
    OeisA245212.a (2^12*11^e*q^f)≠(σ 1 (2^12*11^e*q^f):ℤ) := by
  apply free_case (B:=5) (by decide) hq (by decide) pq ep fp <;> decide +kernel

set_option maxHeartbeats 50000000 in
private theorem at_13 {q e f : ℕ} (hq : q.Prime) (pq : 11<q) (ep : 0<e) (fp : 0<f) :
    OeisA245212.a (2^13*11^e*q^f)≠(σ 1 (2^13*11^e*q^f):ℤ) := by
  apply free_case (B:=3) (by decide) hq (by decide) pq ep fp <;> decide +kernel

set_option maxHeartbeats 50000000 in
private theorem at_14 {q e f : ℕ} (hq : q.Prime) (pq : 11<q) (ep : 0<e) (fp : 0<f) :
    OeisA245212.a (2^14*11^e*q^f)≠(σ 1 (2^14*11^e*q^f):ℤ) := by
  apply free_case (B:=2) (by decide) hq (by decide) pq ep fp <;> decide +kernel

set_option maxHeartbeats 50000000 in
private theorem at_15 {q e f : ℕ} (hq : q.Prime) (pq : 11<q) (ep : 0<e) (fp : 0<f) :
    OeisA245212.a (2^15*11^e*q^f)≠(σ 1 (2^15*11^e*q^f):ℤ) := by
  apply free_case (B:=2) (by decide) hq (by decide) pq ep fp <;> decide +kernel

set_option maxHeartbeats 50000000 in
private theorem at_16 {q e f : ℕ} (hq : q.Prime) (pq : 11<q) (ep : 0<e) (fp : 0<f) :
    OeisA245212.a (2^16*11^e*q^f)≠(σ 1 (2^16*11^e*q^f):ℤ) := by
  apply free_case (B:=1) (by decide) hq (by decide) pq ep fp <;> decide +kernel

set_option maxHeartbeats 50000000 in
private theorem at_17 {q e f : ℕ} (hq : q.Prime) (pq : 11<q) (ep : 0<e) (fp : 0<f) :
    OeisA245212.a (2^17*11^e*q^f)≠(σ 1 (2^17*11^e*q^f):ℤ) := by
  apply free_case (B:=1) (by decide) hq (by decide) pq ep fp <;> decide +kernel

set_option maxHeartbeats 50000000 in
private theorem at_18 {q e f : ℕ} (hq : q.Prime) (pq : 11<q) (ep : 0<e) (fp : 0<f) :
    OeisA245212.a (2^18*11^e*q^f)≠(σ 1 (2^18*11^e*q^f):ℤ) := by
  apply free_case (B:=1) (by decide) hq (by decide) pq ep fp <;> decide +kernel

set_option maxHeartbeats 50000000 in
private theorem at_19 {q e f : ℕ} (hq : q.Prime) (pq : 11<q) (ep : 0<e) (fp : 0<f) :
    OeisA245212.a (2^19*11^e*q^f)≠(σ 1 (2^19*11^e*q^f):ℤ) := by
  apply free_case (B:=1) (by decide) hq (by decide) pq ep fp <;> decide +kernel

set_option maxHeartbeats 50000000 in
private theorem at_20 {q e f : ℕ} (hq : q.Prime) (pq : 11<q) (ep : 0<e) (fp : 0<f) :
    OeisA245212.a (2^20*11^e*q^f)≠(σ 1 (2^20*11^e*q^f):ℤ) := by
  apply free_case (B:=1) (by decide) hq (by decide) pq ep fp <;> decide +kernel

set_option maxHeartbeats 50000000 in
private theorem at_21 {q e f : ℕ} (hq : q.Prime) (pq : 11<q) (ep : 0<e) (fp : 0<f) :
    OeisA245212.a (2^21*11^e*q^f)≠(σ 1 (2^21*11^e*q^f):ℤ) := by
  apply free_case (B:=1) (by decide) hq (by decide) pq ep fp <;> decide +kernel

theorem no_pair {k q e f : ℕ} (hq : q.Prime) (pq : 11<q) (ep : 0<e) (fp : 0<f) :
    OeisA245212.a (2^k*11^e*q^f)≠(σ 1 (2^k*11^e*q^f):ℤ) := by
  intro eq
  have oq := hq.odd_of_ne_two (by omega)
  have odd : Odd (11^e*q^f) := ((by decide : Odd 11).pow).mul oq.pow
  have mem : 11∈(11^e*q^f).primeFactors := Nat.mem_primeFactors.mpr
    ⟨by decide,dvd_mul_of_dvd_left (dvd_pow_self 11 ep.ne') _,by have := hq.pos; positivity⟩
  have hi : k<22 := OMA.DyadicLeast245212.exponent_lt_twice_prime odd mem (by simpa [mul_assoc] using eq)
  interval_cases k
  · exact at_0 hq pq ep fp eq
  · exact at_1 hq pq ep fp eq
  · exact at_2 hq pq ep fp eq
  · exact at_3 hq pq ep fp eq
  · exact at_4 hq pq ep fp eq
  · exact at_5 hq pq ep fp eq
  · exact at_6 hq pq ep fp eq
  · exact at_7 hq pq ep fp eq
  · exact at_8 hq pq ep fp eq
  · exact at_9 hq pq ep fp eq
  · exact at_10 hq pq ep fp eq
  · exact at_11 hq pq ep fp eq
  · exact at_12 hq pq ep fp eq
  · exact at_13 hq pq ep fp eq
  · exact at_14 hq pq ep fp eq
  · exact at_15 hq pq ep fp eq
  · exact at_16 hq pq ep fp eq
  · exact at_17 hq pq ep fp eq
  · exact at_18 hq pq ep fp eq
  · exact at_19 hq pq ep fp eq
  · exact at_20 hq pq ep fp eq
  · exact at_21 hq pq ep fp eq

#print axioms no_pair
end OMA.Least11Pair245212

end
