import FormalConjectures.OEIS.«245212»


/-! An absolute bound on the smaller odd-prime exponent meeting the original OEIS A245212 equality. -/

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

/- A shared-error version of the k-pole rounding bound, exactly matching
the finite scalar table. The bound R may be any positive lower bound on P. -/
namespace OMA.TwoOddJoint245212
open ArithmeticFunction OMA.Smooth245212 OMA.ComplementaryPole245212 OMA.ComplementaryLocal245212
open scoped ArithmeticFunction.sigma

private theorem round {k : ℕ} {p b h P W S : ℤ} (hp : 3≤p) (hb : 3≤b) (hh : 2≤h) (hP : 0<P)
    (w : (p-1)^2*W=p*(b*(p-1)-1)*P+1) (s : (p-1)*S=p*P-1)
    (plus : 0<den k b h P W S) (small : p-1≤h*(k:ℤ))
    (joint : 2*(((k:ℤ)+1)*h*b*p*P+G k*h*(k+1))≤G k*P) :
    G k*P≤2*(p-1)^2*den k b h P W S := by
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
  have ef : 0≤h*F k-G k*u := by
    rw [fg];nlinarith only [mul_nonneg gp.le (sub_nonneg.mpr small),mul_nonneg (by omega : 0≤h) kp.le]
  have pl : 0<(P*G k)*L := by
    nlinarith only [iden,ef,mul_pos (sq_pos_of_pos up) plus,
      mul_nonneg (mul_nonneg (mul_nonneg hP.le kp.le) (by omega : 0≤h)) bp.le]
  have lp := pos_of_mul_pos_right pl (mul_nonneg hP.le gp.le)
  have gain := mul_nonneg (mul_nonneg hP.le gp.le) (show 0≤L-1 by omega)
  have fcap := mul_le_mul_of_nonneg_left (dyad k).2.2.1 (by omega : 0≤h)
  have bu : b*u-p≤b*p := by dsimp [u];nlinarith only [hp,hb]
  have sf := mul_le_mul_of_nonneg_left bu (show (0:ℤ)≤P*(k+1)*h by positivity)
  nlinarith only [iden,gain,joint,fcap,sf,mul_nonneg gp.le up.le]

private theorem enlarge {A B G R P : ℕ} (r0 : 0<R) (rP : R≤P) (box : 2*(A*R+B)≤G*R) :
    2*(A*P+B)≤G*P := by
  have ca : 2*A≤G := (mul_le_mul_iff_left₀ r0).mp (by nlinarith only [box,Nat.zero_le B])
  obtain ⟨n,rfl⟩:=Nat.exists_eq_add_of_le rP
  nlinarith only [box,Nat.mul_le_mul_right n ca]

theorem near {p q a d k R : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p) (oq : 3≤q) (pq : p≠q)
    (ha : 2≤a) (hd : 1≤d)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ))
    (small : p-1≤(d+1)*k) (r0 : 0<R) (rP : R≤p^a)
    (box : 2*((k+1)*(d+1)*(a+1)*p*R+(2^(k+1)-1)*(d+1)*(k+1))≤(2^(k+1)-1)*R) :
    q≤6*(d+1)*(k+1)*(a+1)*p^2 := by
  obtain ⟨e,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : d≠0)
  let D:=den k (a+1) (e+2) ((p:ℤ)^a) (W (p^a)) (σ 1 (p^a))
  obtain ⟨plus,tail'⟩ := tail hp hq op oq pq a e k eqn
  change 0<D at plus
  have jc:=enlarge r0 rP box
  have gz : 1≤2^(k+1) := Nat.one_le_pow _ _ (by decide : 0<2)
  zify [Nat.cast_sub gz] at jc
  have joint : 2*(((k:ℤ)+1)*(e+2)*(a+1)*p*p^a+G k*(e+2)*(k+1))≤G k*(p:ℤ)^a := by
    dsimp [G,z];nlinarith only [jc]
  have sm : (p:ℤ)-1≤((e:ℤ)+2)*k := by
    zify [Nat.cast_sub hp.pos] at small;linarith only [small]
  have m:=moments hp a
  have rr:=round (show (3:ℤ)≤p by omega) (show (3:ℤ)≤a+1 by omega) (show (2:ℤ)≤e+2 by omega)
    (pow_pos (show (0:ℤ)<p by omega) a) m.2 m.1 plus sm joint
  change (q:ℤ)*D≤3*(e+2)*(k+1)*(a+1)*G k*(p:ℤ)^a at tail'
  have qk : (q:ℤ)*(G k*(p:ℤ)^a)≤(6*(e+2)*(k+1)*(a+1)*((p:ℤ)-1)^2)*(G k*(p:ℤ)^a) := by
    nlinarith only [mul_le_mul_of_nonneg_left rr (show (0:ℤ)≤q by positivity),
      mul_le_mul_of_nonneg_left tail' (mul_nonneg (show (0:ℤ)≤2 by decide) (sq_nonneg ((p:ℤ)-1)))]
  have cap := (mul_le_mul_iff_left₀ (mul_pos (dyad k).1 (pow_pos (show (0:ℤ)<p by omega) a))).mp qk
  have sq : ((p:ℤ)-1)^2≤(p:ℤ)^2 := by nlinarith only [show (3:ℤ)≤p by omega]
  exact_mod_cast cap.trans (mul_le_mul_of_nonneg_left sq (by positivity))

end OMA.TwoOddJoint245212

end

section

/- Exact scalar comparisons in the finite part of the uniform smaller
exponent bound. No divisor sums, prime tables, or external certificates. -/
namespace OMA.TwoOddEffectiveTable245212

def floorPrime (K m : ℕ) := max 3 (1+(K-1)*(m-1)/m)

def tail (K : ℕ) := decide (2^(37+3*K)*K^10*119^8 < (floorPrime K 119)^118)

def cell (K m : ℕ) : Bool :=
  let z := 2^K
  let g := z-1
  let R := (floorPrime K m)^(m-1)
  let h := 5*K
  let u := 64*m^2*K
  let t := m*u
  let exact := 3*g*h^2*(K*u+h)<R ∧ 3*g*(K+h^2)<R^2 ∧
    (3*g*(K*u+h))^(m-2)*(3*z*K*u)^2<R^(m-4)
  let y := 6*t*K*h^2
  let a := y^2*(K*u+h)+h^2*(K*u+y)
  let b := K+h*y
  decide (exact ∨ (2*(K*t*h*R+g*u*K)≤g*R ∧
    4*g*(a*R+b)+9*K*h^2*y^2*t*R^2<4*g*R^2))

def row (K : ℕ) := tail K && (List.range' 33 86).all (cell K)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked : (List.range' 3 253).all row = true := by decide +kernel

theorem ranges {K m : ℕ} (lo : 3 ≤ K) (hi : K ≤ 255) (ml : 33 ≤ m) (mh : m ≤ 118) :
    tail K=true ∧ cell K m=true := by
  have ok := List.all_eq_true.mp checked K (List.mem_range'_1.mpr ⟨lo,by omega⟩)
  simp only [row,Bool.and_eq_true] at ok
  exact ⟨ok.1,List.all_eq_true.mp ok.2 m (List.mem_range'_1.mpr ⟨ml,by omega⟩)⟩

#print axioms ranges
end OMA.TwoOddEffectiveTable245212

end

section

/- Elementary bounds on the prime bases and on powers appearing in the
simultaneous rounding estimates. -/
namespace OMA.TwoOddParameters245212
open OMA.Smooth245212 OMA.ComplementaryLocal245212 OMA.ComplementaryPole245212 ArithmeticFunction
open scoped ArithmeticFunction.sigma

theorem cofactor {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p) (oq : 3≤q) (pq : p≠q)
    (hd : 1≤d) (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    q^(d-1)≤3*2^(k+1)*(k+1)*(a+1)*p^a := by
  have eq' : OeisA245212.a (2^k*q^d*p^a)=(σ 1 (2^k*q^d*p^a):ℤ) := by rwa [mul_right_comm]
  have cap := OMA.ComplementaryBase245212.cofactor hq hp oq op pq.symm eq'
  have cq : 2*((k+1)+q)≤3*(k+1)*q := by
    nlinarith only [oq,Nat.mul_le_mul_left k oq]
  apply (mul_le_mul_iff_left₀ hq.pos).mp
  rw [←pow_succ,show d-1+1=d by omega]
  nlinarith only [cap,Nat.mul_le_mul_right ((a+1)*2^(k+1)*p^a) cq]

theorem reciprocal {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p) (oq : 3≤q) (pq : p≠q)
    (ha : 1≤a) (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    k*a<(a+1)*p := by
  obtain ⟨e,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : a≠0)
  let B : ℤ := e+2
  let C : ℤ := d+1
  let P : ℤ := (p:ℤ)^(e+1)
  let Q : ℤ := (q:ℤ)^d
  let x : ℤ := (p:ℤ)^e
  let W0 : ℤ := W (p^(e+1))
  let V : ℤ := W (q^d)
  let S : ℤ := σ 1 (p^(e+1))
  let T : ℤ := σ 1 (q^d)
  have pp : (0:ℤ)<p := by omega
  have qq : (0:ℤ)<q := by omega
  have xp : 0<x := pow_pos pp _
  have qp : 0<Q := pow_pos qq _
  have cp : 0<C := by dsimp [C];positivity
  have bp : 0<B := by dsimp [B];positivity
  have px : P=x*p := by dsimp [P,x];rw [pow_succ]
  have first : B*P+((e:ℤ)+1)*x≤W0 := by
    dsimp [B,P,x,W0];rw [(last hp op e).1];push_cast
    have low : ((e:ℤ)+1)*(p:ℤ)^e≤W (p^e) := by exact_mod_cast (bounds hp op e).2.2.1
    linarith only [low]
  have second : C*Q≤V := by dsimp [C,Q,V];exact_mod_cast (bounds hq oq d).2.2.1
  have w0 : 0≤W0 := by dsimp [W0];positivity
  have pos (r t : ℕ) (prime : r.Prime) : (0:ℤ)<σ 1 (r^t) := by
    exact_mod_cast (show 0<σ 1 (r^t) by
      rw [sigma_one_apply_prime_pow prime]
      exact Finset.sum_pos (fun i _=>pow_pos prime.pos i) (by simp))
  have phy := physical hp hq (by omega) (by omega) pq (e+1) d k eqn
  change F k*W0*V+G k*S*T=z k*(k+1)*(e+1+1)*C*P*Q at phy
  have ar : ((e:ℤ)+1+1)=B := by dsimp [B];ring
  rw [←(dyad k).2.2.2, ar] at phy
  have prod := mul_le_mul first second (mul_pos cp qp).le w0
  have f : (k:ℤ)*G k≤F k := by dsimp [F,G];nlinarith only [show (0:ℤ)≤k by positivity]
  have up := mul_le_mul_of_nonneg_right f (mul_nonneg (mul_nonneg (by positivity : (0:ℤ)≤e+1) xp.le) (mul_pos cp qp).le)
  have g0 := (dyad k).1
  have st : 0<G k*S*T := mul_pos (mul_pos g0 (pos p (e+1) hp)) (pos q d hq)
  have fact : ((k:ℤ)*(e+1))*(G k*x*C*Q)<(B*p)*(G k*x*C*Q) := by
    rw [px] at phy prod
    nlinarith only [phy,mul_le_mul_of_nonneg_left prod (dyad k).2.1.le,up,st]
  have res := (mul_lt_mul_iff_left₀ (mul_pos (mul_pos (mul_pos g0 xp) cp) qp)).mp fact
  dsimp [B] at res;exact_mod_cast res

theorem floor {p q a d k m : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p) (oq : 3≤q) (pq : p≠q)
    (ha : 1≤a) (hm : 1 ≤ m) (mb : m≤a+1)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    OMA.TwoOddEffectiveTable245212.floorPrime (k+1) m≤p := by
  have r := reciprocal hp hq op oq pq ha eqn
  unfold OMA.TwoOddEffectiveTable245212.floorPrime
  apply max_le op
  have lt : k*(m-1)<p*m := by
    by_contra! ge
    have sub := Nat.sub_add_cancel hm
    nlinarith only [Nat.mul_le_mul_left (a+1) ge,Nat.mul_lt_mul_of_pos_left r hm,
      Nat.mul_le_mul_left k mb,congrArg (fun x:ℕ=>k*(a+1)*x) sub]
  change 1+k*(m-1)/m≤p
  exact (Nat.div_lt_iff_lt_mul hm).mpr lt |> (by omega : _ → _)

end OMA.TwoOddParameters245212

end

section

/- Explicit integer lower bounds on both rounded defects of the
two-prime divisor balance; terms retain the separate powers P and Q. -/
namespace OMA.SimultaneousBound245212
open OMA.TwoOddGlobalGap245212 OMA.ComplementaryPole245212 OMA.ComplementaryLocal245212
open OMA.Smooth245212 ArithmeticFunction
open scoped ArithmeticFunction.sigma

def error (p q K B C P Q : ℕ) :=
  q^2*(K*C+p)*Q+p^2*(K*B+q)*P+K+p*q

private theorem alpha_bound {f g p q C K : ℤ} (hp : 2≤p) (hq : 2≤q) (hc : 1≤C)
    (fg : f≤K*g) (f0 : 0≤f) (g0 : 0≤g) (k0 : 0≤K) :
    |alpha f g p q C|≤g*q^2*(K*C+p) := by
  have vp : 0≤q-1 := by omega
  have up : 0≤p-1 := by omega
  have pos : 0≤C*(q-1)-1 := by
    nlinarith only [mul_nonneg (show 0≤C-1 by omega) vp,hq]
  have top : C*(q-1)-1≤C*q := by nlinarith only [hc]
  have down : (p-1)*(q-1)≤p*q := by nlinarith only [hp,hq]
  have fterm := mul_le_mul fg top pos (mul_nonneg k0 g0)
  have gterm := mul_le_mul_of_nonneg_left down g0
  dsimp [alpha]
  apply abs_le.mpr
  constructor
  · nlinarith only [mul_le_mul_of_nonneg_left gterm (show 0≤q by omega),
      mul_nonneg (mul_nonneg (show 0≤q by omega) f0) pos,
      mul_nonneg (mul_nonneg g0 (sq_nonneg q)) (mul_nonneg k0 (show 0≤C by omega))]
  · nlinarith only [mul_le_mul_of_nonneg_left fterm (show 0≤q by omega),
      mul_nonneg (mul_nonneg (mul_nonneg g0 up) vp) (show 0≤q by omega),
      mul_nonneg (mul_nonneg g0 (sq_nonneg q)) (show 0≤p by omega)]

private theorem abs_terms {f g p q B C P Q K : ℤ} (hp : 2≤p) (hq : 2≤q) (hb : 1≤B)
    (hc : 1≤C) (fg : f≤K*g) (f0 : 0≤f) (g0 : 0≤g) (k0 : 0≤K) (p0 : 0≤P) (q0 : 0≤Q) :
    |alpha f g p q C*Q+beta f g p q B*P+f+g*(p-1)*(q-1)| ≤
    g*(q^2*(K*C+p)*Q+p^2*(K*B+q)*P+K+p*q) := by
  have ab := alpha_bound hp hq hc fg f0 g0 k0
  have ba := alpha_bound hq hp hb fg f0 g0 k0
  have sym : alpha f g q p B=beta f g p q B := by dsimp [alpha,beta];ring
  rw [sym] at ba
  have uv : g*(p-1)*(q-1)≤g*(p*q) := by
    have h : (p-1)*(q-1)≤p*q := by nlinarith only [hp,hq]
    nlinarith only [mul_le_mul_of_nonneg_left h g0]
  have s : 0≤g*(p-1)*(q-1) := mul_nonneg (mul_nonneg g0 (by omega)) (by omega)
  calc
    _ ≤ (|alpha f g p q C*Q|+|beta f g p q B*P|)+|f|+|g*(p-1)*(q-1)| := by
      have t1 := abs_add_le (alpha f g p q C*Q) (beta f g p q B*P)
      have t2 := abs_add_le (alpha f g p q C*Q+beta f g p q B*P) f
      have t3 := abs_add_le (alpha f g p q C*Q+beta f g p q B*P+f) (g*(p-1)*(q-1))
      linarith only [t1,t2,t3]
    _ ≤ _ := by
      rw [abs_mul,abs_of_nonneg q0,abs_mul,abs_of_nonneg p0,abs_of_nonneg f0,abs_of_nonneg s]
      nlinarith only [mul_le_mul_of_nonneg_right ab q0,mul_le_mul_of_nonneg_right ba p0,fg,uv]

theorem of_separations {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p) (oq : 3≤q)
    (pq : p≠q) (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ))
    (s1 : defect k 1 p q (a+1) (d+1) ≠ 0)
    (s2 : defect (F k) (G k) p q (a+1) (d+1) ≠ 0) :
    let K:=k+1; let B:=a+1; let C:=d+1; let gn:=2^K-1; let P:=p^a; let Q:=q^d
    P*Q ≤ gn*error p q K B C P Q ∧
    4*gn*P*Q ≤ 4*gn*error p q K B C P Q + 9*K*p^2*q^2*B*C*P*Q := by
  let K:ℤ:=k+1
  let B:ℤ:=a+1
  let C:ℤ:=d+1
  let W : ℤ:=OMA.Smooth245212.W (p^a)
  let V : ℤ:=OMA.Smooth245212.W (q^d)
  let S : ℤ:=σ 1 (p^a)
  let T : ℤ:=σ 1 (q^d)
  let P : ℤ:=(p:ℤ)^a
  let Q : ℤ:=(q:ℤ)^d
  let err := (q:ℤ)^2*(K*C+p)*Q+(p:ℤ)^2*(K*B+q)*P+K+p*q
  let terms (f g : ℤ) := alpha f g p q C*Q+beta f g p q B*P+f+g*(p-1)*(q-1)
  have gp := (dyad k).1
  have fp := (dyad k).2.1
  have zz := (dyad k).2.2.2
  have op' : (3:ℤ)≤p := by omega
  have oq' : (3:ℤ)≤q := by omega
  have pp : 0<P := by dsimp [P];positivity
  have qq : 0<Q := by dsimp [Q];positivity
  have phys := physical hp hq (by omega) (by omega) pq a d k eqn
  change F k*W*V+G k*S*T=z k*(k+1)*B*C*P*Q at phys
  rw [←zz] at phys
  have bound (f g : ℤ) (fg : f≤K*g) (f0 : 0≤f) (g0 : 0≤g) : |terms f g|≤g*err :=
    abs_terms (by omega) (by omega) (by dsimp [B];omega) (by dsimp [C];omega)
      fg f0 g0 (by dsimp [K];omega) pp.le qq.le
  have iden (f g : ℤ) :
      (p-1:ℤ)^2*(q-1:ℤ)^2*(f*W*V+g*S*T-(f+g)*B*C*P*Q) =
      -defect f g p q B C*P*Q+terms f g := by
    simpa only [terms,add_assoc] using expansion f g p q B C P Q W V S T
      (moments hp a).2 (moments hq d).2 (moments hp a).1 (moments hq d).1
  have l := iden (F k) (G k)
  rw [phys,sub_self,mul_zero] at l
  have l' : defect (F k) (G k) p q B C*P*Q=terms (F k) (G k) := by linarith only [l]
  have mag (e : ℤ) (ne : e≠0) : P*Q≤|e*P*Q| := by
    rw [abs_mul,abs_mul,abs_of_pos pp,abs_of_pos qq]
    nlinarith only [mul_nonneg (show 0≤|e|-1 by have := abs_pos.mpr ne;omega) (mul_pos pp qq).le]
  have lhs := mag _ s2
  change P*Q≤|defect (F k) (G k) p q B C*P*Q| at lhs
  rw [l'] at lhs
  have lfinal := lhs.trans (bound _ _ (dyad k).2.2.1 fp.le gp.le)
  have km := iden k 1
  let U : ℤ := (p-1:ℤ)^2*(q-1:ℤ)^2
  have fg : F k=(k:ℤ)*G k+K := by dsimp [K,F,G,z]; ring
  have rel : G k*((k:ℤ)*W*V+S*T-(k+1)*B*C*P*Q) = -K*(W*V-B*C*P*Q) := by
    rw [fg] at phys; dsimp [K] at phys ⊢;linear_combination phys
  have k' : G k*(defect k 1 p q B C*P*Q)=G k*terms k 1+K*U*(W*V-B*C*P*Q) := by
    simp only [one_mul] at km
    dsimp only [U]
    linear_combination (G k)*km - ((p:ℤ)-1)^2*((q:ℤ)-1)^2*rel
  have bp := bounds hp op a
  have bq := bounds hq oq d
  have wmin : B*P≤W := by dsimp [B,P,W];exact_mod_cast bp.2.2.1
  have vmin : C*Q≤V := by dsimp [C,Q,V];exact_mod_cast bq.2.2.1
  have wmax : 2*W≤3*B*P := by dsimp [B,P,W];exact_mod_cast bp.2.1
  have vmax : 2*V≤3*C*Q := by dsimp [C,Q,V];exact_mod_cast bq.2.1
  have w0 : 0≤W := by dsimp [W];positivity
  have v0 : 0≤V := by dsimp [V];positivity
  have bpos : 0<B := by dsimp [B];positivity
  have cpos : 0<C := by dsimp [C];positivity
  have rmin : 0≤W*V-B*C*P*Q := by
    nlinarith only [mul_le_mul wmin vmin (mul_pos cpos qq).le w0]
  have rmax : 4*(W*V-B*C*P*Q)≤9*B*C*P*Q := by
    have lim := mul_le_mul wmax vmax (show 0≤2*V by positivity) (show 0≤3*B*P by positivity)
    nlinarith only [lim,mul_nonneg (mul_nonneg (mul_nonneg bpos.le cpos.le) pp.le) qq.le]
  have u0 : 0≤U := by dsimp [U];positivity
  have uc : U≤(p:ℤ)^2*q^2 := mul_le_mul
    (show ((p:ℤ)-1)^2≤(p:ℤ)^2 by nlinarith only [op'])
    (show ((q:ℤ)-1)^2≤(q:ℤ)^2 by nlinarith only [oq']) (sq_nonneg _) (sq_nonneg _)
  have kp : 0<K := by dsimp [K];positivity
  have product := mul_le_mul uc rmax (mul_nonneg (show (0:ℤ)≤4 by decide) rmin)
    (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have dmag := mul_le_mul_of_nonneg_left (mag _ s1) gp.le
  change G k*(P*Q)≤G k*|defect k 1 p q B C*P*Q| at dmag
  rw [←abs_of_pos gp,←abs_mul,k',abs_of_pos gp] at dmag
  have triangle := abs_add_le (G k*terms k 1) (K*U*(W*V-B*C*P*Q))
  have target := dmag.trans triangle
  rw [abs_mul,abs_of_pos gp,abs_of_nonneg (mul_nonneg (mul_nonneg kp.le u0) rmin)] at target
  have tb := bound k 1 (by dsimp [K];omega) (by positivity) (by decide)
  have final : 4*G k*P*Q≤4*G k*err+9*K*(p:ℤ)^2*q^2*B*C*P*Q := by
    nlinarith only [target,mul_le_mul_of_nonneg_left tb gp.le,mul_le_mul_of_nonneg_left product kp.le]
  have gcast : ((2^(k+1)-1:ℕ):ℤ)=G k := by
    dsimp [G,z];push_cast [Nat.cast_sub (Nat.one_le_pow _ _ (by decide : 0<2))];rfl
  dsimp only [error]
  constructor
  · zify;rw [gcast];exact lfinal
  · zify;rw [gcast];exact final

theorem original {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p)
    (pq : p<q) (ha : 1≤a) (hd : 15≤d) (hk : 2≤k) (small : p≤5*(k+1))
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    let K:=k+1; let B:=a+1; let C:=d+1; let gn:=2^K-1; let P:=p^a; let Q:=q^d
    P*Q ≤ gn*error p q K B C P Q ∧
    4*gn*P*Q ≤ 4*gn*error p q K B C P Q + 9*K*p^2*q^2*B*C*P*Q := by
  obtain ⟨a,b⟩ := original_separations hp hq op pq ha hd hk small eqn
  exact of_separations hp hq op (by omega) pq.ne eqn a b

end OMA.SimultaneousBound245212

end

section

/- Compare integer defect errors against the scalar cell tests, with
no approximations to the prime powers. -/
namespace OMA.TwoOddErrorCells245212
open OMA.SimultaneousBound245212

/-- Lower-cofactor and ordered prime-power comparisons reduce the exact
dyadic defect to three scalar alternatives. -/
theorem alternatives {p q K B C P Q G R h u : ℕ}
    (rpos : 0<R) (rP : R≤P) (rQ : R≤Q) (qR : q*R≤h*Q) (ph : p≤h) (bu : B≤u) (cu : C≤u)
    (necessary : P*Q≤G*error p q K B C P Q) :
    P≤3*G*(K*u+h)*q^2 ∨ R≤3*G*h^2*(K*u+h) ∨ R^2≤3*G*(K+h^2) := by
  by_contra! no
  have A : 3*G*q^2*(K*C+p)<P := calc
    _ ≤ 3*G*q^2*(K*u+h) := by gcongr
    _ = _ := by ring
    _ < _ := no.1
  have second : 3*G*p^2*(K*B+q)<Q := by
    apply (mul_lt_mul_iff_left₀ rpos).mp
    calc
      _ = 3*G*p^2*(K*B*R+q*R) := by ring
      _ ≤ 3*G*h^2*(K*u*Q+h*Q) := by gcongr
      _ = (3*G*h^2*(K*u+h))*Q := by ring
      _ < R*Q := Nat.mul_lt_mul_of_pos_right no.2.1 (lt_of_lt_of_le rpos rQ)
      _ = _ := by ring
  have third : 3*G*(K+p*q)<P*Q := by
    apply (mul_lt_mul_iff_left₀ rpos).mp
    calc
      _ = 3*G*(K*R+p*(q*R)) := by ring
      _ ≤ 3*G*(K*Q+h*(h*Q)) := by gcongr
      _ = 3*G*(K+h^2)*Q := by ring
      _ < R^2*Q := Nat.mul_lt_mul_of_pos_right no.2.2 (lt_of_lt_of_le rpos rQ)
      _ ≤ (P*Q)*R := by nlinarith only [Nat.mul_le_mul_right (R*Q) rP]
  unfold error at necessary
  nlinarith only [necessary,Nat.mul_lt_mul_of_pos_right A (rpos.trans_le rQ),
    Nat.mul_lt_mul_of_pos_right second (rpos.trans_le rP),third]

/-- A scalar power comparison eliminates the first of the alternatives. -/
theorem first_excluded {m G K u h q R P v : ℕ} (hm : 4 ≤ m) (rP : R≤P) (pp : 0<P)
    (qcap : q^(m-2)≤v*P)
    (test : (3*G*(K*u+h))^(m-2)*v^2<R^(m-4)) :
    3*G*(K*u+h)*q^2<P := by
  let a:=3*G*(K*u+h)
  change a^(m-2)*v^2<R^(m-4) at test
  change a*q^2<P
  apply lt_of_not_ge
  intro bad
  have hw := Nat.pow_le_pow_left bad (m-2)
  rw [mul_pow,←pow_mul,mul_comm 2 (m-2),pow_mul] at hw
  have qq := Nat.pow_le_pow_left qcap 2
  rw [mul_pow] at qq
  have big := hw.trans (Nat.mul_le_mul_left (a^(m-2)) qq)
  have tight := Nat.mul_lt_mul_of_pos_right (test.trans_le (Nat.pow_le_pow_left rP (m-4)))
    (pow_pos pp 2)
  rw [←pow_add,show m-4+2=m-2 by omega] at tight
  rw [←mul_assoc] at big
  exact (not_lt_of_ge big) tight

/-- The integer-dyadic obstruction after bounding q itself. -/
theorem second_excluded {p q K B C P Q G R h y u t : ℕ} (rpos : 0<R) (rP : R≤P) (rQ : R≤Q)
    (ph : p≤h) (qy : q≤y) (bu : B≤u) (cu : C≤u) (prod : B*C≤t)
    (necessary : 4*G*P*Q≤4*G*error p q K B C P Q+9*K*p^2*q^2*B*C*P*Q)
    (test : 4*G*((y^2*(K*u+h)+h^2*(K*u+y))*R+(K+h*y))+
      9*K*h^2*y^2*t*R^2 < 4*G*R^2) : False := by
  let a:=y^2*(K*u+h)
  let b:=h^2*(K*u+y)
  let c:=K+h*y
  have aa : q^2*(K*C+p)≤a := by dsimp [a];gcongr
  have bb : p^2*(K*B+q)≤b := by dsimp [b];gcongr
  have cc : K+p*q≤c := by dsimp [c];gcongr
  have re : R^2*error p q K B C P Q≤((a+b)*R+c)*(P*Q) := by
    have lo1 := Nat.mul_le_mul aa (Nat.mul_le_mul_right (R*Q) rP)
    have lo2 := Nat.mul_le_mul bb (Nat.mul_le_mul_right (R*P) rQ)
    have lo3 := Nat.mul_le_mul cc (Nat.mul_le_mul rP rQ)
    dsimp [error];nlinarith only [lo1,lo2,lo3]
  have tr : 9*K*p^2*q^2*B*C≤9*K*h^2*y^2*t := calc
    _ = 9*K*p^2*q^2*(B*C) := by ring
    _ ≤ _ := by gcongr
  change 4*G*((a+b)*R+c)+9*K*h^2*y^2*t*R^2<4*G*R^2 at test
  have cmp := Nat.mul_lt_mul_of_pos_right test (Nat.mul_pos (rpos.trans_le rP) (rpos.trans_le rQ))
  nlinarith only [cmp,Nat.mul_le_mul_left (R^2) necessary,Nat.mul_le_mul_left (4*G) re,
    Nat.mul_le_mul_right (P*Q*R^2) tr]

end OMA.TwoOddErrorCells245212

end

section

/- Coarse growth inequality obtained from the three positive-error
alternatives before splitting the dyadic exponent into ranges. -/
namespace OMA.TwoOddCoarse245212
open OMA.SimultaneousBound245212 OMA.TwoOddErrorCells245212

theorem coarse {p q K B C P Q G R m u : ℕ} (hK : 1≤K) (hu : 1≤u)
    (rpos : 0<R) (rP : R≤P) (rQ : R≤Q) (qR : q*R≤(5*K)*Q) (ph : p≤5*K)
    (bu : B≤u) (cu : C≤u) (uB : u≤64*m^2*K) (gz : G≤2^K)
    (necessary : P*Q≤G*error p q K B C P Q) (fourth : q^4≤3*2^K*K*u*P) :
    R≤2^(37+3*K)*K^10*m^8 := by
  let z:ℕ:=2^K
  change q^4≤3*z*K*u*P at fourth
  have zp : 1≤z := Nat.one_le_pow _ _ (by decide)
  have KK : K*u+5*K≤6*K*u := by nlinarith only [Nat.mul_le_mul_left K hu]
  have target : R≤6400*z^3*K^6*u^4 := by
    rcases alternatives rpos rP rQ qR ph bu cu necessary with x|x|x
    · have w : P≤3*z*(6*K*u)*q^2 := x.trans (by gcongr)
      have sq := Nat.pow_le_pow_left w 2
      simp only [mul_pow] at sq
      rw [←pow_mul q 2 2] at sq
      have sq' := sq.trans (Nat.mul_le_mul_left _ fourth)
      have shrink : P≤972*z^3*K^3*u^3 := by
        apply (mul_le_mul_iff_left₀ (rpos.trans_le rP)).mp
        nlinarith only [sq']
      have gain := Nat.mul_le_mul (Nat.pow_le_pow_right hK (show 3≤6 by decide))
        (Nat.pow_le_pow_right hu (show 3≤4 by decide))
      have gain' := Nat.mul_le_mul (Nat.mul_le_mul_right (z^3) (show 972≤6400 by decide)) gain
      exact rP.trans (shrink.trans (by nlinarith only [gain']))
    · have z3 : z≤z^3 := by simpa using (Nat.pow_le_pow_right zp (show 1≤3 by decide))
      have ub : u≤u^4 := by simpa using (Nat.pow_le_pow_right hu (show 1≤4 by decide))
      have w : R≤3*z*(5*K)^2*(6*K*u) := x.trans (by gcongr)
      have lo := Nat.mul_le_mul (Nat.mul_le_mul z3 (Nat.pow_le_pow_right hK (show 3≤6 by decide))) ub
      nlinarith only [w,Nat.mul_le_mul (show 450≤6400 by decide) lo]
    · have rr : R≤R^2 := by simpa using (Nat.pow_le_pow_right rpos (show 1≤2 by decide))
      have zz : z≤z^3 := by simpa using (Nat.pow_le_pow_right zp (show 1≤3 by decide))
      have k2 : K≤K^2 := by simpa using (Nat.pow_le_pow_right hK (show 1≤2 by decide))
      have w : R≤3*z*(26*K^2) := rr.trans (x.trans
        (Nat.mul_le_mul (Nat.mul_le_mul_left 3 gz) (by nlinarith only [k2])))
      have lower := Nat.mul_le_mul (Nat.mul_le_mul zz (Nat.pow_le_pow_right hK (show 2≤6 by decide)))
        (Nat.one_le_pow 4 u hu)
      nlinarith only [w,Nat.mul_le_mul (show 78≤6400 by decide) lower]
  have scale := target.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left uB 4))
  have eqn : 6400*z^3*K^6*(64*m^2*K)^4 = (6400*64^4)*(2^(3*K))*K^10*m^8 := by
    dsimp [z];rw [pow_mul 2 3 K,←pow_mul 2 K 3,mul_comm K 3,pow_mul];ring
  rw [eqn] at scale
  rw [pow_add]
  exact scale.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
    (Nat.mul_le_mul_right _ (show 6400*64^4≤(2:ℕ)^37 by decide))))

end OMA.TwoOddCoarse245212

end

section

/- Scalar domination by powers of two and propagation of the table tail. -/
namespace OMA.TwoOddGrowth245212

private theorem step {t c j n : ℕ} (ht : 0<t) (s : (t+1)^j≤c*t^j) (h : t≤n) :
    (n+1)^j≤c*n^j := by
  have spread : (n+1)*t≤(t+1)*n := by nlinarith only [h]
  have w := Nat.pow_le_pow_left spread j
  rw [mul_pow,mul_pow] at w
  exact (mul_le_mul_iff_left₀ (pow_pos ht j)).mp
    (by nlinarith only [w,Nat.mul_le_mul_right (n^j) s])

private theorem exponential {t c j : ℕ} (ht : 0<t) (s : (t+1)^j≤2*t^j)
    (base : c*t^j≤2^t) (n : ℕ) (hn : t≤n) : c*n^j≤2^n := by
  induction n,hn using Nat.le_induction with
  | base => exact base
  | succ n hn ih =>
    have hp := Nat.mul_le_mul_left c (step ht s hn)
    rw [pow_succ]
    nlinarith only [hp,ih]

theorem at256 {n : ℕ} (hn : 256≤n) :
    n^20≤2^n ∧ n^16≤2^n ∧ 2^65*n^21≤2^n := by
  refine ⟨?_,?_,exponential (by decide : 0<256) (by decide) (by decide) n hn⟩
  · simpa using exponential (c:=1) (j:=20) (by decide : 0<256) (by decide) (by decide) n hn
  · simpa using exponential (c:=1) (j:=16) (by decide : 0<256) (by decide) (by decide) n hn

theorem table_tail {K p m : ℕ} (klo : 3≤K) (khi : K≤255) (ml : 119 ≤ m)
    (least : OMA.TwoOddEffectiveTable245212.floorPrime K 119≤p) (p3 : 3≤p) :
    2^(37+3*K)*K^10*m^8<p^(m-1) := by
  have tail := (OMA.TwoOddEffectiveTable245212.ranges (m:=33) klo khi (by decide) (by decide)).1
  change decide (_ < _) = true at tail
  have t := of_decide_eq_true tail
  have ini := t.trans_le (Nat.pow_le_pow_left least 118)
  induction m,ml using Nat.le_induction with
  | base => exact ini
  | succ n hn ih =>
    have sf := step (j:=8) (c:=3) (by decide : 0<119) (by decide) hn
    calc
      _ ≤ 2^(37+3*K)*K^10*(3*n^8) := Nat.mul_le_mul_left _ sf
      _ = (2^(37+3*K)*K^10*n^8)*3 := by ring
      _ < p^(n-1)*p := Nat.mul_lt_mul_of_lt_of_le ih p3 (by omega)
      _ = p^((n+1)-1) := by rw [←pow_succ];congr 1;omega

theorem m_large {K m p : ℕ} (big : 256≤K) (pp : 3≤p)
    (input : p^(m-1)≤2^(37+3*K)*K^10*m^8) : m≤5*K := by
  by_cases sm : m<256
  · omega
  have mm := (at256 (by omega : 256 ≤ m)).2.1
  have kk := (at256 big).1
  have power := Nat.pow_le_pow_left input 2
  simp only [mul_pow,←pow_mul] at power
  have bound : (p^(m-1))^2≤2^(74+7*K+m) := calc
    _ ≤ (2^((37+3*K)*2))*K^20*m^16 := by rw [←pow_mul];exact power
    _ ≤ (2^((37+3*K)*2))*2^K*2^m := by gcongr
    _ = _ := by rw [←pow_add,←pow_add];congr 1;ring
  have nine : 8≤p^2 := (show 8≤(3:ℕ)^2 by decide).trans (Nat.pow_le_pow_left pp 2)
  have lo : 2^(3*(m-1)) ≤ (p^(m-1))^2 := by
    rw [pow_mul 2 3 (m-1),←pow_mul p (m-1) 2,mul_comm (m-1) 2,pow_mul p 2 (m-1)]
    exact Nat.pow_le_pow_left nine _
  have cut := (pow_le_pow_iff_right₀ (a:=(2:ℕ)) (by decide)).mp (lo.trans bound)
  omega

end OMA.TwoOddGrowth245212

end

section

/- Uniform large-dyadic-index exclusion from four explicit power
comparisons. The constants are chosen to keep the arithmetic integral. -/
namespace OMA.TwoOddLargeScale245212
open OMA.TwoOddGrowth245212

theorem estimates {K m p : ℕ} (big : 256≤K) (ml : 33 ≤ m) (ms : m≤5*K) (least : K≤3*p) :
    let h:=5*K; let u:=64*m^2*K; let t:=m*u; let R:=p^(m-1); let g:=2^K-1
    let y:=6*t*K*h^2
    4*K*t*h<2^K ∧ 4*u*K≤R ∧
      4*g*((y^2*(K*u+h)+h^2*(K*u+y))*R+(K+h*y))+
      9*K*h^2*y^2*t*R^2 < 4*g*R^2 := by
  let h:=5*K
  let u:=64*m^2*K
  let t:=m*u
  let R:=p^(m-1)
  let g:=2^K-1
  let y:=6*t*K*h^2
  change 4*K*t*h<2^K ∧ 4*u*K≤R ∧
    4*g*((y^2*(K*u+h)+h^2*(K*u+y))*R+(K+h*y))+9*K*h^2*y^2*t*R^2<4*g*R^2
  have kp : 1≤K := by omega
  have pp : 64≤p := by omega
  have r0 : 1≤R := Nat.one_le_pow _ _ (by omega)
  have zk := (at256 big).2.2
  have ub : u≤2^11*K^3 := calc
    _ ≤ 64*(5*K)^2*K := by dsimp [u];gcongr
    _ ≤ _ := by nlinarith only [Nat.zero_le (K^3)]
  have tb : t≤2^13*K^4 := calc
    _ ≤ (5*K)*(1600*K^3) := Nat.mul_le_mul ms
      (by dsimp [u];nlinarith only [Nat.mul_le_mul_right (64*K) (Nat.pow_le_pow_left ms 2)])
    _ ≤ _ := by nlinarith only [Nat.zero_le (K^4)]
  have yb : y≤2^21*K^7 := calc
    _ ≤ 6*(2^13*K^4)*K*(5*K)^2 := by dsimp only [y,h];gcongr
    _ ≤ _ := by nlinarith only [Nat.zero_le (K^7)]
  have high (c e : ℕ) (cc : c<2^65) (ee : e≤21) : c*K^e<2^K :=
    (Nat.mul_lt_mul_of_lt_of_le cc (Nat.pow_le_pow_right kp ee) (Nat.pow_pos kp)).trans_le zk
  have gc : 4*K*t*h<2^K := calc
    _ ≤ 4*K*(2^13*K^4)*(5*K) := by dsimp only [h];gcongr
    _ = 163840*K^6 := by ring
    _ < _ := high _ _ (by decide) (by decide)
  have p5 : K^4≤p^5 := by
    have lo := Nat.pow_le_pow_left least 5
    have w := Nat.mul_le_mul_right (K^4) (show 243≤K by omega)
    rw [mul_pow] at lo
    nlinarith only [lo,w]
  have p32 : K^24*p^2≤R := calc
    _ = (K^4)^6*p^2 := by ring
    _ ≤ (p^5)^6*p^2 := by gcongr
    _ = p^32 := by ring
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
  have room : 2^57*K^18≤R := calc
    _ ≤ (K^6*p^2)*K^18 := Nat.mul_le_mul_right _ ((show 2^57≤(256:ℕ)^6*64^2 by decide).trans
      (Nat.mul_le_mul (Nat.pow_le_pow_left big 6) (Nat.pow_le_pow_left pp 2)))
    _ = K^24*p^2 := by ring
    _ ≤ R := p32
  have pack {v c e : ℕ} (vb : v≤c*K^e) (cb : 2*c≤2^57) (eb : e≤18) : 2*v≤R := by
    have ext := Nat.mul_le_mul cb (Nat.pow_le_pow_right kp eb)
    nlinarith only [room,ext,vb]
  have pc : 4*u*K≤R := (show 4*u*K≤2*(4*u*K) by omega).trans
    (pack (c:=8192) (e:=4) (by nlinarith only [Nat.mul_le_mul_right (4*K) ub]) (by decide) (by decide))
  let aa:=y^2*(K*u+h)+h^2*(K*u+y)
  let bb:=K+h*y
  have sum : aa+bb≤2^56*K^18 := by
    have X (n : ℕ) (hn : n≤18) := Nat.pow_le_pow_right kp hn
    have M : aa+bb≤(2^21*K^7)^2*(K*(2^11*K^3)+5*K)+(5*K)^2*(K*(2^11*K^3)+2^21*K^7)+(K+(5*K)*(2^21*K^7)) := by
      dsimp only [aa,bb,h];gcongr
    nlinarith only [M,X 15 (by decide),X 6 (by decide),X 9 (by decide),X 8 (by decide),
      (show K≤K^18 by simpa using X 1 (by decide)),Nat.zero_le (K^18)]
  have ab := pack sum (by decide) (by decide)
  have drift : 9*K*h^2*y^2*t≤g := by
    have drift0 : 9*K*h^2*y^2*t≤9*K*(5*K)^2*(2^21*K^7)^2*(2^13*K^4) := by
      dsimp only [h];gcongr
    have iso : 9*K*(5*K)^2*(2^21*K^7)^2*(2^13*K^4)=8106479329266892800*K^21 := by ring
    rw [iso] at drift0
    have lt:=drift0.trans_lt (high _ _ (by decide) (by decide))
    dsimp [g];omega
  have gp : 0<g := by dsimp [g];have := Nat.one_lt_pow (by omega : K≠0) (by decide : 1<2);omega
  refine ⟨gc,pc,?_⟩
  change 4*g*(aa*R+bb)+(9*K*h^2*y^2*t)*R^2<4*g*R^2
  have margin := Nat.mul_le_mul_left (2*g*R) ab
  have br := Nat.mul_le_mul_left bb r0
  have plus := Nat.mul_le_mul_left (4*g) br
  nlinarith only [margin,plus,Nat.mul_le_mul_right (R^2) drift,Nat.mul_pos gp (pow_pos r0 2)]

end OMA.TwoOddLargeScale245212

end

section

/- The finite scalar table and the unbounded dyadic estimate apply to
the same original integer equality, with all substitutions proved here. -/
namespace OMA.TwoOddEffectiveOriginal245212
open ArithmeticFunction OMA.TwoOddEffectiveTable245212
open scoped ArithmeticFunction.sigma

theorem bound {p q k a d : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p) (pq : p<q)
    (hk : 2≤k) (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    min (a+1) (d+1)≤32 := by
  by_contra! outside
  let K:=k+1
  let B:=a+1
  let C:=d+1
  let m:=min B C
  let u:=64*m^2*K
  let t:=m*u
  let h:=5*K
  let y:=6*t*K*h^2
  let z:ℕ:=2^K
  let g:=z-1
  let P:=p^a
  let Q:=q^d
  let R:=p^(m-1)
  have ml : 33 ≤ m := outside
  have mb : m≤B := min_le_left _ _
  have mc : m≤C := min_le_right _ _
  have a32 : 32≤a := by dsimp [B] at mb;omega
  have d32 : 32≤d := by dsimp [C] at mc;omega
  have k3 : 3≤K := by dsimp [K];omega
  have many : 5≤(a+1)*(d+1) := by nlinarith only [a32,d32,Nat.zero_le (a*d)]
  have sm := OMA.ComplementaryBase245212.small_prime hp hq op (by omega) pq.ne many eqn
  have ph : p≤h := sm.elim id (fun z=>pq.le.trans z)
  have swap : OeisA245212.a (2^k*q^d*p^a)=(σ 1 (2^k*q^d*p^a):ℤ) := by rwa [mul_right_comm]
  have both : B≤u ∧ C≤u ∧ B*C≤t := by
    have easy : m≤u := by
      dsimp [u];nlinarith only [Nat.mul_le_mul_left (64*m^2) (show 1≤K by omega),Nat.mul_le_mul_left m ml]
    by_cases ord : B≤C
    · have me : m=B := min_eq_left ord
      have c : C≤u := by
        dsimp [u];rw [me]
        exact OMA.ComplementaryExp245212.exponent hq hp (by omega) op pq.ne' (by omega) swap
      exact ⟨me ▸ easy,c,by dsimp only [t];rw [me];exact Nat.mul_le_mul_left _ c⟩
    · have me : m=C := min_eq_right (by omega)
      have b : B≤u := by
        dsimp [u];rw [me]
        exact OMA.ComplementaryExp245212.exponent hp hq op (by omega) pq.ne (by omega) eqn
      exact ⟨b,me ▸ easy,by dsimp only [t];rw [me,mul_comm C u];exact Nat.mul_le_mul_right _ b⟩
  obtain ⟨bu,cu,bc⟩:=both
  have r0 : 0<R := pow_pos hp.pos _
  have rP : R≤P := Nat.pow_le_pow_right hp.pos (by dsimp [B] at mb;omega)
  have rQ : R≤Q := (Nat.pow_le_pow_left pq.le _).trans (Nat.pow_le_pow_right hq.pos (by dsimp [C] at mc;omega))
  have eqm : m-1=m-2+1 := by omega
  have qR : q*R≤h*Q := calc
    _ = p*(p^(m-2)*q) := by dsimp [R];rw [eqm,pow_succ];ring
    _ ≤ h*(q^(m-2)*q) := Nat.mul_le_mul ph (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left pq.le _))
    _ = h*q^(m-1) := by rw [eqm,pow_succ]
    _ ≤ h*Q := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hq.pos (by dsimp [C] at mc;omega))
  have co := OMA.TwoOddParameters245212.cofactor hp hq op (by omega) pq.ne (by omega) eqn
  have qcap : q^(m-2)≤3*z*K*u*P := calc
    _ ≤ q^(d-1) := Nat.pow_le_pow_right hq.pos (by dsimp [C] at mc;omega)
    _ ≤ 3*z*K*B*P := co
    _ ≤ _ := by gcongr
  have errs := OMA.SimultaneousBound245212.original hp hq op pq (by omega) (by omega) hk ph eqn
  change P*Q≤g*OMA.SimultaneousBound245212.error p q K B C P Q ∧
    4*g*P*Q≤4*g*OMA.SimultaneousBound245212.error p q K B C P Q+9*K*p^2*q^2*B*C*P*Q at errs
  have cg := OMA.TwoOddCoarse245212.coarse (m:=m) (by omega : 1≤K)
    (by dsimp [u];exact Nat.mul_pos (Nat.mul_pos (by decide) (pow_pos (by omega) _)) (by omega))
    r0 rP rQ qR ph bu cu (le_refl _) (Nat.sub_le z 1) errs.1
    ((Nat.pow_le_pow_right hq.pos (show 4 ≤ m-2 by omega)).trans qcap)
  have near {r : ℕ} (pr : 0<r) (lower : r≤R) (box : 2*(K*t*h*r+g*u*K)≤g*r) : q≤y := by
    have actu : K*C*B*p*r+g*C*K≤K*t*h*r+g*u*K := calc
      _ = K*(B*C)*p*r+g*C*K := by ring
      _ ≤ _ := by gcongr
    have sm' : p-1≤(d+1)*k := by
      dsimp [h,K] at ph;nlinarith only [ph,hk,Nat.mul_le_mul_left k d32,Nat.sub_le p 1]
    have hq':=OMA.TwoOddJoint245212.near hp hq op (by omega) pq.ne (by omega) (by omega) eqn
      sm' pr (lower.trans rP) ((Nat.mul_le_mul_left _ actu).trans box)
    change q≤6*C*K*B*p^2 at hq'
    exact hq'.trans (calc
      _ = 6*(B*C)*K*p^2 := by ring
      _ ≤ y := Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ bc)) (Nat.pow_le_pow_left ph _))
  by_cases big : 256≤K
  · have ms := OMA.TwoOddGrowth245212.m_large big op cg
    have lo := OMA.TwoOddParameters245212.reciprocal hp hq op (by omega) pq.ne (by omega) eqn
    have least : K≤3*p := by
      dsimp [K];by_contra! bad
      nlinarith only [lo,Nat.mul_le_mul_right a (show 2*p≤k by omega),Nat.mul_le_mul_left p a32]
    obtain ⟨gc,pc,fin⟩:=OMA.TwoOddLargeScale245212.estimates big ml ms least
    change 4*K*t*h<z at gc
    change 4*u*K≤R at pc
    have gc' : 4*K*C*B*p<z := (show 4*K*C*B*p≤4*K*t*h by
      nlinarith only [Nat.mul_le_mul_left (4*K) (Nat.mul_le_mul bc ph)]).trans_lt gc
    have qsmall := OMA.ComplementaryFar245212.far hp hq op (by omega) pq.ne (by omega) (by omega)
      eqn gc' (((Nat.mul_le_mul_right K (Nat.mul_le_mul_left 4 cu)).trans pc).trans rP)
    have qy : q≤y := qsmall.trans (calc
      _ = 6*(B*C)*K*p^2 := by dsimp [B,C,K];ring
      _ ≤ y := Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ bc)) (Nat.pow_le_pow_left ph 2))
    exact OMA.TwoOddErrorCells245212.second_excluded r0 rP rQ ph qy bu cu bc errs.2 fin
  · have klow : K≤255 := by omega
    have mmax : m≤118 := by
      by_contra! tail
      have pmin := OMA.TwoOddParameters245212.floor hp hq op (by omega) pq.ne (by omega) (by decide : 1≤119)
        (show 119≤a+1 by dsimp [B] at mb;omega) eqn
      exact (not_lt_of_ge cg) (OMA.TwoOddGrowth245212.table_tail k3 klow tail pmin op)
    let rr:=(floorPrime K m)^(m-1)
    have lp : floorPrime K m≤p := OMA.TwoOddParameters245212.floor hp hq op (by omega) pq.ne
      (by omega) (by omega) mb eqn
    have rr0 : 0<rr := pow_pos (lt_of_lt_of_le (by decide : 0<3) (le_max_left _ _)) _
    have rrR : rr≤R := Nat.pow_le_pow_left lp _
    have data := of_decide_eq_true (ranges k3 klow ml mmax).2
    change (3*g*h^2*(K*u+h)<rr ∧ 3*g*(K+h^2)<rr^2 ∧ (3*g*(K*u+h))^(m-2)*(3*z*K*u)^2<rr^(m-4)) ∨
      (2*(K*t*h*rr+g*u*K)≤g*rr ∧ 4*g*((y^2*(K*u+h)+h^2*(K*u+y))*rr+(K+h*y))+
        9*K*h^2*y^2*t*rr^2<4*g*rr^2) at data
    rcases data with ⟨l1,l2,l3⟩|⟨j,jt⟩
    · have first := OMA.TwoOddErrorCells245212.first_excluded (by omega : 4 ≤ m) (rrR.trans rP)
        (r0.trans_le rP) qcap l3
      rcases OMA.TwoOddErrorCells245212.alternatives r0 rP rQ qR ph bu cu errs.1 with bad|bad|bad
      · omega
      · omega
      · exact (not_lt_of_ge (bad.trans' (Nat.pow_le_pow_left rrR 2))) l2
    · exact OMA.TwoOddErrorCells245212.second_excluded rr0 (rrR.trans rP) (rrR.trans rQ)
        ph (near rr0 rrR j) bu cu bc errs.2 jt

end OMA.TwoOddEffectiveOriginal245212

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

/- The smaller odd-prime exponent of any original A245212 solution
with two distinct odd primes is at most 31. -/
namespace OMA.TwoOddEffectiveAll245212
open scoped ArithmeticFunction.sigma

private theorem ordered {p q k a d : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p) (pq : p<q)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    min (a+1) (d+1)≤32 := by
  by_cases hk : 2≤k
  · exact OMA.TwoOddEffectiveOriginal245212.bound hp hq op pq hk eqn
  by_contra! bad
  have ep : 0<a := by omega
  have fp : 0<d := by omega
  by_cases z : k=0
  · subst k
    have five : 5≤q := by obtain ⟨v,h⟩:=hq.odd_of_ne_two (by omega);omega
    exact OMA.DyadicEuler245212.pair_small hp hq op pq ep
      (by decide : 1<3) (by decide : 1<5) op five (by decide +kernel) eqn
  · exact OMA.DyadicEuler245212.no_two_small_k (by omega) (by omega) hp hq op pq ep fp eqn

theorem original {p q k a d : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p) (oq : 3≤q) (pq : p≠q)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    min (a+1) (d+1)≤32 := by
  obtain lt|gt:=lt_or_gt_of_ne pq
  · exact ordered hp hq op lt eqn
  · have sw : OeisA245212.a (2^k*q^d*p^a)=(σ 1 (2^k*q^d*p^a):ℤ) := by rwa [mul_right_comm]
    rw [min_comm];exact ordered hq hp oq gt sw

theorem smaller_exponent {p q k a d : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p) (oq : 3≤q) (pq : p≠q)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    min a d≤31 := by have := original hp hq op oq pq eqn;omega

end OMA.TwoOddEffectiveAll245212

end

#print axioms OMA.TwoOddEffectiveAll245212.smaller_exponent
