import FormalConjectures.OEIS.«245212»


/-! A total-prime-multiplicity congruence for all positive powers in OEIS A245212. -/

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

theorem dyadic_balance (k : ℕ) :
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

theorem tau_linear (u H : ℕ) (even : Even H) (nz : u≠0) :
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

/- Centered complete blocks, uniformly in the exponent's binary valuation. -/
namespace OMA.UniformDyad245212
open Finset ArithmeticFunction OMA.Smooth245212 OMA.DyadicBlocks245212
open scoped ArithmeticFunction.sigma ArithmeticFunction.Omega
open OMA.DyadicBlocks245212 (split_g)
open OMA.DyadicBlocks245212 (split_w)
open OMA.DyadicPower245212 (tau_linear)
open OMA.DyadicPower245212 (dyadic_balance)

private def center (p s : ℕ) : ℤ :=
  (weight p (4*s):ℤ)+2*s-(2*(s:ℤ)+1)*(geom p (4*s):ℤ)

private theorem center_double (p s : ℕ) :
    center p (2*s)=(1+(p:ℤ)^(4*s))*center p s+
      (2*(s:ℤ))*(1-(p:ℤ)^(4*s))*(1-(geom p (4*s):ℤ)) := by
  unfold center
  rw [show 4*(2*s)=4*s+4*s by omega,OMA.DyadicBlocks245212.split_w,OMA.DyadicBlocks245212.split_g]
  push_cast
  ring

theorem pow_lift (p j : ℕ) (odd : Odd p) :
    (16*(2:ℤ)^j) ∣ (p:ℤ)^(4*2^j)-1 := by
  induction j with
  | zero =>
    obtain ⟨t,ht⟩:=odd
    have h : ((((p:ℤ)^4-1:ℤ):ZMod 16))=0 := by
      rw [ht];push_cast
      exact (by decide : ∀ t : ZMod 16, (2*t+1)^4-1=0) t
    simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd _ 16).mp h
  | succ j ih =>
    obtain ⟨b,hb⟩:=ih
    obtain ⟨c,hc⟩:=(odd.pow (n:=4*2^j)).add_one.two_dvd
    have c' : (p:ℤ)^(4*2^j)+1=2*c := by exact_mod_cast hc
    refine ⟨b*c,?_⟩
    rw [show 4*2^(j+1)=(4*2^j)*2 by ring,pow_mul,pow_succ (2:ℤ) j]
    linear_combination ((p:ℤ)^(4*2^j)+1)*hb + (16*(2:ℤ)^j*b)*c'

private theorem center_lift (p j : ℕ) (odd : Odd p) :
    (16*(2:ℤ)^j) ∣ center p (2^j)-(2:ℤ)^j*((p:ℤ)^2-1) := by
  induction j with
  | zero =>
    obtain ⟨t,ht⟩:=odd
    have h : (((center p 1-((p:ℤ)^2-1):ℤ):ZMod 16))=0 := by
      rw [ht]
      simp only [center,weight,geom,show 4*1=3+1 by decide,sum_range_succ,sum_range_zero]
      push_cast
      exact (by decide : ∀ t : ZMod 16,
        (0+1*(0+1)+(2*t+1)^1*(1+1)+(2*t+1)^2*(2+1)+(2*t+1)^3*(3+1)
          +2*1-(2*1+1)*(0+1+(2*t+1)^1+(2*t+1)^2+(2*t+1)^3))-((2*t+1)^2-1)=0) t
    simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd _ 16).mp h
  | succ j ih =>
    let s:=2^j
    let P:ℤ:=(p:ℤ)^(4*s)
    obtain ⟨b,hb⟩:=ih
    have b' : center p s-(s:ℤ)*((p:ℤ)^2-1)=16*s*b := by exact_mod_cast hb
    obtain ⟨c,hc⟩:=pow_lift p j odd
    have c' : P-1=16*s*c := by exact_mod_cast hc
    obtain ⟨t,ht⟩:=(odd.pow (n:=4*s)).add_one.two_dvd
    have t' : P+1=2*t := by dsimp [P];exact_mod_cast ht
    obtain ⟨z,hz⟩:=odd
    have z' : (p:ℤ)=2*z+1 := by exact_mod_cast hz
    let l:ℤ:=2*z*((z:ℤ)+1)
    have z2 : (p:ℤ)^2-1=2*l := by rw [z'];dsimp [l];ring
    rw [pow_succ' (2:ℕ) j,center_double,pow_succ' (2:ℤ) j]
    change (16*(2*(s:ℤ))) ∣ (1+P)*center p s+
      2*(s:ℤ)*(1-P)*(1-(geom p (4*s):ℤ))-2*(s:ℤ)*((p:ℤ)^2-1)
    refine ⟨(t:ℤ)*b+s*c*l-(s:ℤ)*c*(1-(geom p (4*s):ℤ)),?_⟩
    linear_combination (1+P)*b'+(16*(s:ℤ)*b)*t'+
      ((s:ℤ)*(2*l)-2*(s:ℤ)*(1-(geom p (4*s):ℤ)))*c'+(P-1)*(s:ℤ)*z2

theorem eight_square (p : ℕ) (op : Odd p) : (8:ℤ) ∣ (p:ℤ)^2-1 := by
  obtain ⟨t,ht⟩:=op
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp
  rw [ht];push_cast
  exact (by decide : ∀ i : ZMod 8, (2*i+1)^2-1=0) t

theorem prime_moments {p e : ℕ} (hp : p.Prime) (op : Odd p) (oe : Odd e) (j : ℕ) :
    let s:=2^j
    let n:=4*s
    let m:=16*s
    W (p^(e*n)) ≡ (1+s*e*(p^2+1))*(σ 1 (p^(e*n))) [MOD m] := by
  let s:=2^j
  let n:=4*s
  let m:=16*s
  change W (p^(e*n)) ≡ (1+s*e*(p^2+1))*(σ 1 (p^(e*n))) [MOD m]
  have z16 : 16*(s:ZMod m)=0 := by
    exact_mod_cast (ZMod.natCast_self m)
  have center0 := (ZMod.intCast_zmod_eq_zero_iff_dvd
    (center p s-(s:ℤ)*((p:ℤ)^2-1)) m).mpr (by exact_mod_cast center_lift p j op)
  have cr : (weight p n:ZMod m)+2*(s:ZMod m)-(2*(s:ZMod m)+1)*(geom p n:ZMod m) =
      (s:ZMod m)*((p:ZMod m)^2-1) := by simpa [center,n,sub_eq_zero] using center0
  have p0 := (ZMod.intCast_zmod_eq_zero_iff_dvd ((p:ℤ)^n-1) m).mpr (by exact_mod_cast pow_lift p j op)
  have pn : (p:ZMod m)^n=1 := by simpa [sub_eq_zero] using p0
  have g4 : 4∣geom p n := (show 4∣n by exact dvd_mul_right _ _).trans
    (by simpa [n,s,pow_add,mul_comm] using (div_geom p op (j+2)) : n∣geom p n)
  have sg : 4*(s:ZMod m)*(geom p n:ZMod m)=0 := by
    obtain ⟨b,hb⟩:=g4
    rw [hb,Nat.cast_mul]
    linear_combination (b:ZMod m)*z16
  have pe (b : ℕ) : (p:ZMod m)^(b*n)=1 := by rw [mul_comm,pow_mul,pn,one_pow]
  have blocks (b : ℕ) : (geom p (b*n):ZMod m)=b*(geom p n:ZMod m) ∧
      (weight p (b*n):ZMod m)=b*(weight p n:ZMod m) := by
    induction b with
    | zero => simp [geom,weight]
    | succ b ih =>
      rw [Nat.succ_mul,OMA.DyadicBlocks245212.split_g,OMA.DyadicBlocks245212.split_w]
      push_cast
      rw [pe,one_mul,one_mul,ih.1,ih.2]
      constructor
      · ring
      · have nn : (n:ZMod m)=4*(s:ZMod m) := by dsimp [n];push_cast;rfl
        rw [nn]
        linear_combination (b:ZMod m)*sg
  obtain ⟨c,hc⟩:=eight_square p op
  have cz : (p:ZMod m)^2=1+8*(c:ZMod m) := by
    have t:=congrArg (fun z:ℤ => (z:ZMod m)) hc
    push_cast at t
    linear_combination t
  obtain ⟨b,eb⟩:=oe
  apply (ZMod.natCast_eq_natCast_iff _ _ m).mp
  rw [w_pow hp,sigma_one_apply_prime_pow hp,sum_range_succ,sum_range_succ]
  change ((weight p (e*n)+p^(e*n)*(e*n+1):ℕ):ZMod m)=
    (((1+s*e*(p^2+1))*(geom p (e*n)+p^(e*n)):ℕ):ZMod m)
  push_cast
  rw [(blocks e).1,(blocks e).2,pe,cz]
  rw [cz] at cr
  have nn : (n:ZMod m)=4*(s:ZMod m) := by dsimp [n];push_cast;rfl
  rw [nn,eb]
  push_cast
  linear_combination (2*(b:ZMod m)+1)*cr-
    ((2*(b:ZMod m)+1)*b+2*(2*(b:ZMod m)+1)^2*c)*sg

private theorem geom_lift (p j : ℕ) (op : Odd p) :
    (8*(2:ℤ)^j)∣(geom p (4*2^j):ℤ)-2*(2:ℤ)^j*(p+1) := by
  induction j with
  | zero =>
    obtain ⟨t,ht⟩:=op
    have hz : ((((geom p 4:ℤ)-2*((p:ℤ)+1):ℤ):ZMod 8))=0 := by
      rw [ht]
      simp only [geom,show 4=3+1 by decide,sum_range_succ,sum_range_zero];push_cast
      exact (by decide : ∀ t : ZMod 8, (0+1+(2*t+1)^1+(2*t+1)^2+(2*t+1)^3)-2*(2*t+1+1)=0) t
    simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp hz
  | succ j ih =>
    obtain ⟨b,hb⟩:=ih
    obtain ⟨c,hc⟩:=pow_lift p j op
    refine ⟨b+c*(geom p (4*2^j):ℤ),?_⟩
    rw [show 4*2^(j+1)=4*2^j+4*2^j by ring,OMA.DyadicBlocks245212.split_g,pow_succ (2:ℤ) j]
    push_cast
    linear_combination 2*hb+(geom p (4*2^j):ℤ)*hc

theorem sigma_prime {p : ℕ} (hp : p.Prime) (op : Odd p) (j e : ℕ) :
    let s:=2^j
    σ 1 (p^(e*(4*s))) ≡ 1+2*s*e*(p+1) [MOD 8*s] := by
  let s:=2^j
  let n:=4*s
  let m:=8*s
  have h1 : (m:ℤ)∣(p:ℤ)^n-1 := dvd_trans (show (m:ℤ)∣16*(2:ℤ)^j by
    dsimp [m,s];exact ⟨2,by ring⟩) (pow_lift p j op)
  have p0 := (ZMod.intCast_zmod_eq_zero_iff_dvd ((p:ℤ)^n-1) m).mpr h1
  have pn : (p:ZMod m)^n=1 := by simpa [sub_eq_zero] using p0
  have pe (a : ℕ) : (p:ZMod m)^(a*n)=1 := by rw [mul_comm,pow_mul,pn,one_pow]
  have gz := (ZMod.intCast_zmod_eq_zero_iff_dvd ((geom p n:ℤ)-2*s*((p:ℤ)+1)) m).mpr
    (by exact_mod_cast geom_lift p j op)
  have gn : (geom p n : ZMod m)=2*s*((p:ZMod m)+1) := by simpa [sub_eq_zero] using gz
  have ge : (geom p (e*n):ZMod m)=e*(2*s*((p:ZMod m)+1)) := by
    induction e with
    | zero => simp [geom]
    | succ e ih => rw [Nat.succ_mul,OMA.DyadicBlocks245212.split_g];push_cast;rw [pe,gn,ih];ring
  apply (ZMod.natCast_eq_natCast_iff _ _ m).mp
  rw [sigma_one_apply_prime_pow hp,sum_range_succ]
  change ((geom p (e*n)+p^(e*n):ℕ):ZMod m)=((1+2*s*e*(p+1):ℕ):ZMod m)
  push_cast;rw [ge,pe];ring

def weightCoeff (s e u r : ℕ) : ZMod (16*s) :=
  (1+2*(s:ZMod (16*s))*e)^r+s*e*((u:ZMod (16*s))^2-1)

theorem weight_mul (s e a b i j : ℕ) (oa : Odd a) (ob : Odd b) :
    weightCoeff s e (a*b) (i+j)=weightCoeff s e a i*weightCoeff s e b j := by
  let m:=16*s
  have zm : 16*(s:ZMod m)=0 := by exact_mod_cast ZMod.natCast_self m
  have oddA : Odd (1+2*s*e) := ⟨s*e,by ring⟩
  obtain ⟨x,hx⟩:=oddA.pow (n:=i)
  obtain ⟨y,hy⟩:=oddA.pow (n:=j)
  have x' : (1+2*(s:ZMod m)*e)^i=2*x+1 := by exact_mod_cast congrArg (fun n:ℕ => (n:ZMod m)) hx
  have y' : (1+2*(s:ZMod m)*e)^j=2*y+1 := by exact_mod_cast congrArg (fun n:ℕ => (n:ZMod m)) hy
  obtain ⟨v,hv⟩:=eight_square a oa
  obtain ⟨w,hw⟩:=eight_square b ob
  have v' : (a:ZMod m)^2=1+8*(v:ZMod m) := by
    have t:=congrArg (fun n:ℤ => (n:ZMod m)) hv;push_cast at t;linear_combination t
  have w' : (b:ZMod m)^2=1+8*(w:ZMod m) := by
    have t:=congrArg (fun n:ℤ => (n:ZMod m)) hw;push_cast at t;linear_combination t
  dsimp [weightCoeff]
  rw [Nat.cast_mul,mul_pow,pow_add,x',y',v',w']
  linear_combination ((4*(v:ZMod m)*w-x*w-y*v)*e-4*s*(e:ZMod m)^2*v*w)*zm

private theorem weight_core (u e j : ℕ) (ou : Odd u) (sq : Squarefree u) (oe : Odd e) :
    let s:=2^j
    (W (u^(e*(4*s))):ZMod (16*s))=weightCoeff s e u (Ω u)*(σ 1 (u^(e*(4*s))):ZMod (16*s)) := by
  let s:=2^j
  let M:=16*s
  let N:=e*(4*s)
  change (W (u^N):ZMod M)=weightCoeff s e u (Ω u)*(σ 1 (u^N):ZMod M)
  induction u using Nat.recOnPrimeCoprime with
  | zero => simp at ou
  | prime_pow p d hp =>
    by_cases dz : d=0
    · subst d;simp [weightCoeff,W]
    obtain rfl := ((Nat.squarefree_pow_iff hp.ne_one dz).mp sq).2
    simp only [pow_one] at ou ⊢
    rw [cardFactors_apply_prime hp]
    have ratio := (ZMod.natCast_eq_natCast_iff _ _ M).mpr (prime_moments hp ou oe j)
    change (W (p^N):ZMod M)=(((1+s*e*(p^2+1))*(σ 1 (p^N)):ℕ):ZMod M) at ratio
    dsimp [weightCoeff];push_cast at ratio; rw [ratio];ring
  | coprime a b ha hb cop ia ib =>
    obtain ⟨oa,ob⟩:=Nat.odd_mul.mp ou
    have h:=(cop.pow_left N).pow_right N
    rw [mul_pow,w_mult.map_mul_of_coprime h,isMultiplicative_sigma.map_mul_of_coprime h,
      cardFactors_mul (by omega : a≠0) (by omega : b≠0),weight_mul _ _ _ _ _ _ oa ob,
      Nat.cast_mul,Nat.cast_mul,ia oa sq.of_mul_left,ib ob sq.of_mul_right]
    ring

def ordinaryCoeff (s e u r : ℕ) : ZMod (8*s) :=
  1+4*(s:ZMod (8*s))*e*r+2*s*e*((u:ZMod (8*s))-1)

theorem ordinary_mul (s e a b i j : ℕ) (oa : Odd a) (ob : Odd b) :
    ordinaryCoeff s e (a*b) (i+j)=ordinaryCoeff s e a i*ordinaryCoeff s e b j := by
  let m:=8*s
  have zm : 8*(s:ZMod m)=0 := by exact_mod_cast ZMod.natCast_self m
  obtain ⟨x,hx⟩:=oa
  obtain ⟨y,hy⟩:=ob
  dsimp [ordinaryCoeff];rw [hx,hy];push_cast
  linear_combination ((e:ZMod m)*x*y-2*s*e^2*(i+x)*(j+y))*zm

private theorem ordinary_core (u e j : ℕ) (ou : Odd u) (sq : Squarefree u) :
    let s:=2^j
    (σ 1 (u^(e*(4*s))):ZMod (8*s))=ordinaryCoeff s e u (Ω u) := by
  let s:=2^j
  let M:=8*s
  let N:=e*(4*s)
  change (σ 1 (u^N):ZMod M)=ordinaryCoeff s e u (Ω u)
  induction u using Nat.recOnPrimeCoprime with
  | zero => simp at ou
  | prime_pow p d hp =>
    by_cases dz : d=0
    · subst d;simp [ordinaryCoeff]
    obtain rfl:=((Nat.squarefree_pow_iff hp.ne_one dz).mp sq).2
    simp only [pow_one] at ou ⊢
    have h:=(ZMod.natCast_eq_natCast_iff _ _ M).mpr (sigma_prime hp ou j e)
    change (σ 1 (p^N):ZMod M)=((1+2*s*e*(p+1):ℕ):ZMod M) at h
    rw [h,cardFactors_apply_prime hp]
    dsimp [ordinaryCoeff];push_cast;ring
  | coprime a b ha hb cop ia ib =>
    obtain ⟨oa,ob⟩:=Nat.odd_mul.mp ou
    rw [mul_pow,isMultiplicative_sigma.map_mul_of_coprime ((cop.pow_left N).pow_right N),
      cardFactors_mul (by omega : a≠0) (by omega : b≠0),ordinary_mul _ _ _ _ _ _ oa ob,
      Nat.cast_mul,ia oa sq.of_mul_left,ib ob sq.of_mul_right]

theorem scalar_coeff (s e u r : ℕ) (oe : Odd e) (u5 : u%8=5) (r8 : 8∣r) :
    weightCoeff s e u r=1+8*(s:ZMod (16*s)) ∧ ordinaryCoeff s e u r=1 := by
  let m:=16*s
  have z : 16*(s:ZMod m)=0 := by exact_mod_cast ZMod.natCast_self m
  have z' : 8*(s:ZMod (8*s))=0 := by exact_mod_cast ZMod.natCast_self (8*s)
  have power : (1+2*(s:ZMod m)*e)^8=1 := by
    linear_combination ((e:ZMod m)+7*s*e^2+28*s^2*e^3+70*s^3*e^4+
      112*s^4*e^5+112*s^5*e^6+64*s^6*e^7+16*s^7*e^8)*z
  obtain ⟨t,rt⟩:=r8
  obtain ⟨b,eb⟩:=oe
  let a:=u/8
  have ua : u=8*a+5 := by dsimp [a];omega
  constructor
  · dsimp [weightCoeff];rw [rt,pow_mul,power,one_pow,ua,eb];push_cast
    linear_combination ((2*(b:ZMod m)+1)*(4*a^2+5*a+1)+b)*z
  · dsimp [ordinaryCoeff];rw [rt,ua];push_cast
    linear_combination ((e:ZMod (8*s))*(4*t+2*a+1))*z'

private theorem four_not {k j e u : ℕ} (oe : Odd e) (ou : Odd u) (sq : Squarefree u)
    (u5 : u%8=5) (rank : 8∣Ω u) :
    let s:=2^j
    OeisA245212.a (2^k*u^(e*(4*s)))≠(σ 1 (2^k*u^(e*(4*s))):ℤ) := by
  let s:=2^j
  let N:=e*(4*s)
  let v:=u^N
  let d:=2^k
  let m:=16*s
  let l:=8*s
  change OeisA245212.a (d*v)≠(σ 1 (d*v):ℤ)
  intro eqn
  obtain ⟨hw,hs⟩:=scalar_coeff s e u (Ω u) oe u5 rank
  have sr:=ordinary_core u e j ou sq
  have wr:=weight_core u e j ou sq oe
  change (σ 1 v:ZMod l)=ordinaryCoeff s e u (Ω u) at sr
  change (W v:ZMod m)=weightCoeff s e u (Ω u)*(σ 1 v:ZMod m) at wr
  rw [hs] at sr
  rw [hw] at wr
  have sn : σ 1 v ≡ 1 [MOD l] := (ZMod.natCast_eq_natCast_iff _ 1 l).mp (by simpa using sr)
  have even : Even N := ⟨2*s*e,by dsimp [N];ring⟩
  have tl:=(OMA.DyadicPower245212.tau_linear u N even ou.pos.ne').of_dvd
    (show l∣2*N from ⟨e,by dsimp [l,N];ring⟩)
  have t : σ 0 v ≡ 1 [MOD l] := by
    apply tl.trans
    obtain ⟨q,hq⟩:=rank
    rw [hq,show 1+8*q*N=l*(4*q*e)+1 by dsimp [l,N];ring]
    exact Nat.ModEq.modulus_mul_add
  have p0 := (ZMod.intCast_zmod_eq_zero_iff_dvd ((u:ℤ)^(4*s)-1) m).mpr
    (by exact_mod_cast pow_lift u j ou)
  have pn : (u:ZMod m)^(4*s)=1 := by simpa [sub_eq_zero] using p0
  have zn : v ≡ 1 [MOD l] := by
    apply Nat.ModEq.of_dvd (show l∣m from ⟨2,by dsimp [l,m];ring⟩)
    apply (ZMod.natCast_eq_natCast_iff _ _ m).mp
    dsimp [v,N];push_cast;rw [mul_comm e,pow_mul,pn,one_pow]
  have ds : 2*(v*(σ 0 v)) ≡ 2*(σ 1 v) [MOD m] := by
    rw [show m=2*l by dsimp [m,l];ring]
    exact ((by simpa using zn.mul t : v*(σ 0 v) ≡ 1 [MOD l]).trans sn.symm).mul_left' 2
  have cop : d.Coprime v := ((Nat.coprime_two_left.mpr ou).pow_left k).pow_right N
  have bal:=OMA.Abundance245212.balance (show d*v≠0 by dsimp [d,v];have := ou.pos;positivity) eqn
  rw [w_mult.map_mul_of_coprime cop,isMultiplicative_sigma.map_mul_of_coprime cop,
    isMultiplicative_sigma.map_mul_of_coprime cop] at bal
  have dy : W d+σ 1 d=2*d*(σ 0 d) := OMA.DyadicPower245212.dyadic_balance k
  have red : W d*W v+(σ 1 d)*(σ 1 v) ≡ (W d+σ 1 d)*(σ 1 v) [MOD m] := calc
    _ = 2*(d*v)*(σ 0 d*σ 0 v) := bal
    _ = (d*σ 0 d)*(2*(v*σ 0 v)) := by ring
    _ ≡ (d*σ 0 d)*(2*σ 1 v) [MOD m] := ds.mul_left _
    _ = (W d+σ 1 d)*σ 1 v := by rw [dy];ring
  rw [add_mul] at red
  have modulus : m=2^(j+4) := by dsimp [m,s];rw [pow_add];ring
  have oddS : Odd (σ 1 v) := Nat.odd_iff.mpr (by
    have h:=sn.of_dvd (show 2∣l from ⟨4*s,by dsimp [l];ring⟩)
    simpa [Nat.ModEq] using h)
  have a : m.Coprime (W d) := modulus ▸ (Nat.coprime_two_left.mpr
    (OMA.DyadicPower245212.dyadic_odd k)).pow_left _
  have b : m.Coprime (σ 1 v) := modulus ▸ (Nat.coprime_two_left.mpr oddS).pow_left _
  have equal : W v ≡ σ 1 v [MOD m] := (red.add_right_cancel' _).cancel_left_of_coprime a
  have rel : W v ≡ (1+8*s)*(σ 1 v) [MOD m] := (ZMod.natCast_eq_natCast_iff _ _ m).mp
    (by push_cast;exact wr)
  have can : (1+8*s)*(σ 1 v) ≡ 1*(σ 1 v) [MOD m] := by simpa only [one_mul] using rel.symm.trans equal
  have z : 8*s ≡ 0 [MOD m] := Nat.ModEq.add_left_cancel' 1
    (by simpa only [add_zero] using can.cancel_right_of_coprime b)
  have le:=Nat.le_of_dvd (show 0<8*s by dsimp [s];positivity) (Nat.modEq_zero_iff_dvd.mp z)
  dsimp [m] at le
  have sp : 0<s := by dsimp [s];positivity
  omega

private theorem not_odd_exponent {u E k : ℕ} (hu : 1<u) (ou : Odd u) (sq : Squarefree u)
    (odd : Odd E) : OeisA245212.a (2^k*u^E)≠(σ 1 (2^k*u^E):ℤ) := by
  intro eqn
  let p : u.primeFactors → ℕ := Subtype.val
  have hp (i : u.primeFactors) : (p i).Prime := Nat.prime_of_mem_primeFactors i.property
  have op (i : u.primeFactors) : Odd (p i) := by
    apply Nat.odd_iff.mpr
    have d : p i∣u := Nat.dvd_of_mem_primeFactors i.property
    have no : ¬2∣p i := fun h => ou.not_two_dvd_nat (h.trans d)
    omega
  have total_eq : OMA.Smooth245212.total p (fun _ => E)=u^E := by
    change (∏ i : u.primeFactors,(i:ℕ)^E)=u^E
    rw [Finset.prod_pow,Finset.prod_coe_sort u.primeFactors (fun i:ℕ => i),
      Nat.prod_primeFactors_of_squarefree sq]
  rw [←total_eq] at eqn
  obtain ⟨i,hi⟩:=Nat.nonempty_primeFactors.mpr hu
  obtain ⟨_,bad⟩:=OMA.ExponentParity245212.two_mod_four p (fun _ => E) hp op
    Subtype.val_injective k eqn ⟨⟨i,hi⟩,odd⟩
  rw [Nat.odd_iff] at odd
  omega

/-- Entire two-parameter families are excluded: the common exponent E and the
power of two multiplying the odd part are both unrestricted. -/
theorem all_powers {u : ℕ} (sq : Squarefree u) (u5 : u%8=5) (rank : 8∣Ω u)
    (k E : ℕ) (pos : 0<E) : OeisA245212.a (2^k*u^E)≠(σ 1 (2^k*u^E):ℤ) := by
  have ou : Odd u := Nat.odd_iff.mpr (by omega)
  by_cases he : 2∣E
  · obtain ⟨b,rfl⟩:=he
    by_cases hb : 2∣b
    · obtain ⟨c,rfl⟩:=hb
      obtain ⟨j,e,oe,ce⟩:=Nat.exists_eq_two_pow_mul_odd (by omega : c≠0)
      rw [show 2*(2*c)=e*(4*2^j) by rw [ce];ring]
      exact four_not oe ou sq u5 rank
    · intro eqn
      have ob : Odd b := Nat.odd_iff.mpr (by omega)
      rw [mul_comm 2 b,pow_mul] at eqn
      obtain ⟨v,hv⟩:=OMA.DyadicPower245212.square_root_is_square (ou.pow (n:=b)) eqn
      obtain ⟨t,bt⟩:=ob
      have residue : (u:ZMod 8)=5 := (ZMod.natCast_eq_natCast_iff u 5 8).mpr (by simpa [Nat.ModEq] using u5)
      have h:=congrArg (fun z:ℕ => (z:ZMod 8)) hv
      push_cast at h
      rw [residue,bt,pow_succ,pow_mul,show (5:ZMod 8)^2=1 by decide,one_pow,one_mul] at h
      exact (by decide : ∀ x:ZMod 8, (5:ZMod 8)≠x*x) v h
  · exact not_odd_exponent (by omega) ou sq (Nat.odd_iff.mpr (by omega))

private theorem build_core (r : ℕ) : ∃ u : ℕ, Squarefree u ∧ u%8=5 ∧ Ω u=r+1 := by
  induction r with
  | zero =>
    have hp : Nat.Prime 5 := by decide
    exact ⟨5,hp.squarefree,by decide,cardFactors_apply_prime hp⟩
  | succ r ih =>
    obtain ⟨u,sq,u5,hr⟩:=ih
    obtain ⟨p,hp,up,pr⟩:=Nat.exists_prime_gt_modEq_one u (show 8≠0 by decide)
    have cop:=hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega : 0<u) up)
    refine ⟨p*u,(Nat.squarefree_mul cop).mpr ⟨hp.squarefree,sq⟩,?_,?_⟩
    · rw [Nat.mul_mod];change p%8=1%8 at pr;rw [pr,u5]
    · rw [cardFactors_mul hp.ne_zero (by omega : u≠0),cardFactors_apply_prime hp,hr];omega

/-- The excluded squarefree cores occur at every positive prime-factor count
divisible by eight, so this family has unbounded prime support. -/
theorem at_every_rank (r : ℕ) (hr : 0<r) (rank : 8∣r) :
    ∃ u : ℕ, Squarefree u ∧ u%8=5 ∧ Ω u=r ∧
      ∀ k E : ℕ, 0<E → OeisA245212.a (2^k*u^E)≠(σ 1 (2^k*u^E):ℤ) := by
  obtain ⟨u,sq,u5,hu⟩:=build_core (r-1)
  rw [Nat.sub_add_cancel hr] at hu
  exact ⟨u,sq,u5,hu,all_powers sq u5 (hu ▸ rank)⟩

#print axioms all_powers
#print axioms at_every_rank

end OMA.UniformDyad245212

end

section

/- Independent odd-prime exponents in a common class after removing a
shared power of two. -/
namespace OMA.MixedDyad245212
open Finset ArithmeticFunction OMA.Smooth245212 OMA.UniformDyad245212
open scoped ArithmeticFunction.sigma ArithmeticFunction.Omega
open OMA.UniformDyad245212 (weightCoeff)
open OMA.UniformDyad245212 (ordinaryCoeff)
open OMA.UniformDyad245212 (weight_mul)
open OMA.UniformDyad245212 (ordinary_mul)
open OMA.UniformDyad245212 (prime_moments)
open OMA.UniformDyad245212 (sigma_prime)
open OMA.UniformDyad245212 (pow_lift)
open OMA.UniformDyad245212 (scalar_coeff)
open OMA.UniformDyad245212 (eight_square)
open OMA.DyadicPower245212 (dyadic_balance)

private def bump (s e t : ℕ) : ZMod (16*s) := 1+4*(s:ZMod (16*s))*(1+2*s*e)*t

private theorem bump_add (s e a b : ℕ) : bump s e (a+b)=bump s e a*bump s e b := by
  have z : 16*(s:ZMod (16*s))=0 := by exact_mod_cast ZMod.natCast_self (16*s)
  dsimp [bump];push_cast
  linear_combination (-(s:ZMod (16*s))*(1+2*s*e)^2*a*b)*z

private theorem local_moments {p e : ℕ} (hp : p.Prime) (op : Odd p) (oe : Odd e)
    (t j : ℕ) :
    let s:=2^j
    let v:=p^((e+2*t)*(4*s))
    (W v:ZMod (16*s))=bump s e t*OMA.UniformDyad245212.weightCoeff s e p 1*(σ 1 v:ZMod (16*s)) ∧
    (σ 1 v:ZMod (8*s))=OMA.UniformDyad245212.ordinaryCoeff s e p 1 ∧
    (σ 0 v:ZMod (8*s))=1+4*s*e ∧ (v:ZMod (8*s))=1 := by
  let s:=2^j
  let m:=16*s
  let l:=8*s
  let v:=p^((e+2*t)*(4*s))
  have fodd : Odd (e+2*t) := by rw [Nat.odd_iff] at oe ⊢;omega
  have z : 16*(s:ZMod m)=0 := by exact_mod_cast ZMod.natCast_self m
  have zl : 8*(s:ZMod l)=0 := by exact_mod_cast ZMod.natCast_self l
  have wm:=(ZMod.natCast_eq_natCast_iff _ _ m).mpr (OMA.UniformDyad245212.prime_moments hp op fodd j)
  change (W v:ZMod m)=(((1+s*(e+2*t)*(p^2+1))*(σ 1 v):ℕ):ZMod m) at wm
  have sm:=(ZMod.natCast_eq_natCast_iff _ _ l).mpr (OMA.UniformDyad245212.sigma_prime hp op j (e+2*t))
  change (σ 1 v:ZMod l)=((1+2*s*(e+2*t)*(p+1):ℕ):ZMod l) at sm
  obtain ⟨c,hc⟩:=OMA.UniformDyad245212.eight_square p op
  have pp : (p:ZMod m)^2=1+8*(c:ZMod m) := by
    have y:=congrArg (fun z:ℤ => (z:ZMod m)) hc;push_cast at y;linear_combination y
  obtain ⟨a,pa⟩:=op
  have pw:=(ZMod.intCast_zmod_eq_zero_iff_dvd ((p:ℤ)^(4*s)-1) l).mpr
    (dvd_trans (show (l:ℤ)∣16*(2:ℤ)^j from ⟨2,by dsimp [l,s];ring⟩)
      (OMA.UniformDyad245212.pow_lift p j ⟨a,pa⟩))
  have pn : (p:ZMod l)^(4*s)=1 := by simpa [sub_eq_zero] using pw
  change (W v:ZMod m)=_ ∧ (σ 1 v:ZMod l)=OMA.UniformDyad245212.ordinaryCoeff s e p 1 ∧
    (σ 0 v:ZMod l)=1+4*(s:ZMod l)*e ∧ (v:ZMod l)=1
  refine ⟨?_,?_,?_,?_⟩
  · rw [wm];push_cast;dsimp [OMA.UniformDyad245212.weightCoeff,bump];rw [pp]
    linear_combination ((t:ZMod m)*(c-s*e-s^2*e^2-2*s*e*c-4*s^2*e^2*c)*(σ 1 v:ZMod m))*z
  · rw [sm];push_cast;dsimp [OMA.UniformDyad245212.ordinaryCoeff];rw [pa];push_cast
    linear_combination ((t:ZMod l)*(a+1))*zl
  · dsimp [v];rw [sigma_zero_apply_prime_pow hp];push_cast
    linear_combination (t:ZMod l)*zl
  · dsimp [v];push_cast;rw [mul_comm (e+2*t),pow_mul,pn,one_pow]

private theorem aggregate {ι : Type*} [DecidableEq ι] (S : Finset ι) (p t : ι→ℕ)
    (pr : ∀ i, (p i).Prime) (odd : ∀ i, Odd (p i)) (inj : Function.Injective p)
    {e : ℕ} (oe : Odd e) (j : ℕ) :
    let s:=2^j
    let v:=∏ i∈S,p i^((e+2*t i)*(4*s))
    let u:=∏ i∈S,p i
    (W v:ZMod (16*s))=bump s e (∑ i∈S,t i)*OMA.UniformDyad245212.weightCoeff s e u S.card*(σ 1 v:ZMod (16*s)) ∧
    (σ 1 v:ZMod (8*s))=OMA.UniformDyad245212.ordinaryCoeff s e u S.card ∧
    (σ 0 v:ZMod (8*s))=(1+4*(s:ZMod (8*s))*e)^S.card ∧ (v:ZMod (8*s))=1 := by
  let s:=2^j
  let m:=16*s
  let l:=8*s
  let h (i:ι):=(e+2*t i)*(4*s)
  let P (i:ι):=p i^h i
  change (W (∏ i∈S,P i):ZMod m)=bump s e (∑ i∈S,t i)*OMA.UniformDyad245212.weightCoeff s e (∏ i∈S,p i) S.card *
    (σ 1 (∏ i∈S,P i):ZMod m) ∧
    (σ 1 (∏ i∈S,P i):ZMod l)=OMA.UniformDyad245212.ordinaryCoeff s e (∏ i∈S,p i) S.card ∧
    (σ 0 (∏ i∈S,P i):ZMod l)=(1+4*(s:ZMod l)*e)^S.card ∧
    ((∏ i∈S,P i:ℕ):ZMod l)=1
  induction S using Finset.induction with
  | empty => simp [bump,OMA.UniformDyad245212.weightCoeff,OMA.UniformDyad245212.ordinaryCoeff,W]
  | insert i S outside ih =>
    have cop : (P i).Coprime (∏ a∈S,P a) := Nat.Coprime.prod_right fun q hq =>
      (((Nat.coprime_primes (pr i) (pr q)).mpr (fun same => outside (inj same ▸ hq))).pow_left _).pow_right _
    have prodOdd : Odd (∏ a∈S,p a) := Nat.coprime_two_left.mp
      (Nat.Coprime.prod_right (fun a _ => Nat.coprime_two_left.mpr (odd a)))
    obtain ⟨w,q,hτ,hp⟩:=local_moments (pr i) (odd i) oe (t i) j
    change (W (P i):ZMod m)=bump s e (t i)*OMA.UniformDyad245212.weightCoeff s e (p i) 1*(σ 1 (P i):ZMod m) at w
    change (σ 1 (P i):ZMod l)=OMA.UniformDyad245212.ordinaryCoeff s e (p i) 1 at q
    change (σ 0 (P i):ZMod l)=1+4*(s:ZMod l)*e at hτ
    change (P i:ZMod l)=1 at hp
    simp only [prod_insert outside,card_insert_of_notMem outside,sum_insert outside,bump_add]
    rw [w_mult.map_mul_of_coprime cop,isMultiplicative_sigma.map_mul_of_coprime cop,
      isMultiplicative_sigma.map_mul_of_coprime cop]
    simp only [Nat.cast_mul]
    rw [Nat.add_comm S.card 1,OMA.UniformDyad245212.weight_mul _ _ _ _ _ _ (odd i) prodOdd,
      OMA.UniformDyad245212.ordinary_mul _ _ _ _ _ _ (odd i) prodOdd,pow_add,pow_one,w,q,hτ,hp,ih.1,ih.2.1,ih.2.2.1,ih.2.2.2]
    exact ⟨by ring,rfl,rfl,one_mul 1⟩

private theorem charge {v R : ℕ} (ov : Odd v) (k j : ℕ) :
    let s:=2^j
    (¬ R ≡ 1 [MOD 16*s]) → (W v:ZMod (16*s))=(R:ZMod (16*s))*(σ 1 v:ZMod (16*s)) →
    (σ 1 v:ZMod (8*s))=1 → (σ 0 v:ZMod (8*s))=1 → (v:ZMod (8*s))=1 →
    OeisA245212.a (2^k*v)≠(σ 1 (2^k*v):ℤ) := by
  let s:=2^j
  let d:=2^k
  let m:=16*s
  let l:=8*s
  dsimp only
  intro fail wr sr tr vr eqn
  have sn : σ 1 v ≡ 1 [MOD l] := (ZMod.natCast_eq_natCast_iff _ 1 l).mp (by simpa using sr)
  have t : σ 0 v ≡ 1 [MOD l] := (ZMod.natCast_eq_natCast_iff _ 1 l).mp (by simpa using tr)
  have zn : v ≡ 1 [MOD l] := (ZMod.natCast_eq_natCast_iff _ 1 l).mp (by simpa using vr)
  have ds : 2*(v*(σ 0 v)) ≡ 2*(σ 1 v) [MOD m] := by
    rw [show m=2*l by dsimp [m,l];ring]
    exact ((by simpa using zn.mul t : v*(σ 0 v) ≡ 1 [MOD l]).trans sn.symm).mul_left' 2
  have cop : d.Coprime v := (Nat.coprime_two_left.mpr ov).pow_left k
  have bal:=OMA.Abundance245212.balance (show d*v≠0 by dsimp [d];have := ov.pos;positivity) eqn
  rw [w_mult.map_mul_of_coprime cop,isMultiplicative_sigma.map_mul_of_coprime cop,
    isMultiplicative_sigma.map_mul_of_coprime cop] at bal
  have dy : W d+σ 1 d=2*d*(σ 0 d) := OMA.DyadicPower245212.dyadic_balance k
  have red : W d*W v+(σ 1 d)*(σ 1 v) ≡ (W d+σ 1 d)*(σ 1 v) [MOD m] := calc
    _ = 2*(d*v)*(σ 0 d*σ 0 v) := bal
    _ = (d*σ 0 d)*(2*(v*σ 0 v)) := by ring
    _ ≡ (d*σ 0 d)*(2*σ 1 v) [MOD m] := ds.mul_left _
    _ = (W d+σ 1 d)*σ 1 v := by rw [dy];ring
  rw [add_mul] at red
  have modulus : m=2^(j+4) := by dsimp [m,s];rw [pow_add];ring
  have oddS : Odd (σ 1 v) := Nat.odd_iff.mpr (by
    have h:=sn.of_dvd (show 2∣l from ⟨4*s,by dsimp [l];ring⟩)
    simpa [Nat.ModEq] using h)
  have a : m.Coprime (W d) := modulus ▸ (Nat.coprime_two_left.mpr
    (OMA.DyadicPower245212.dyadic_odd k)).pow_left _
  have b : m.Coprime (σ 1 v) := modulus ▸ (Nat.coprime_two_left.mpr oddS).pow_left _
  have equal : W v ≡ σ 1 v [MOD m] := (red.add_right_cancel' _).cancel_left_of_coprime a
  have rel : W v ≡ R*(σ 1 v) [MOD m] := (ZMod.natCast_eq_natCast_iff _ _ m).mp
    (by push_cast;exact wr)
  have can : R*(σ 1 v) ≡ 1*(σ 1 v) [MOD m] := by simpa only [one_mul] using rel.symm.trans equal
  exact fail (can.cancel_right_of_coprime b)

private theorem impossible (s e a : ℕ) (sp : 0<s) (align : a%4≠2) :
    ¬(1+4*s*(1+2*s*e)*a)*(1+8*s) ≡ 1 [MOD 16*s] := by
  intro h
  let d:=(1+2*s*e)*a+2+8*s*(1+2*s*e)*a
  have eq : (1+4*s*(1+2*s*e)*a)*(1+8*s)=1+(4*s)*d := by dsimp [d];ring
  rw [eq] at h
  have hh : (4*s)*d ≡ (4*s)*0 [MOD (4*s)*4] := by
    rw [show 4*s*4=16*s by ring,mul_zero]
    exact Nat.ModEq.add_left_cancel' 1 (by simpa only [add_zero] using h)
  have hd : d ≡ 0 [MOD 4] := hh.mul_left_cancel' (by positivity)
  have hz:=(ZMod.natCast_eq_natCast_iff d 0 4).mpr hd
  dsimp [d] at hz
  push_cast at hz
  have two : (a:ZMod 4)=2 := (by decide : ∀ s e a:ZMod 4,
    (1+2*s*e)*a+2+8*s*(1+2*s*e)*a=0 → a=2) s e a hz
  exact align ((ZMod.natCast_eq_natCast_iff a 2 4).mp two)

private theorem many_four {ι : Type*} [Fintype ι] (p t : ι→ℕ)
    (pr : ∀ i, (p i).Prime) (odd : ∀ i, Odd (p i)) (inj : Function.Injective p)
    (rad : (∏ i,p i)%8=5) (rank : 8∣Fintype.card ι) (align : (∑ i,t i)%4≠2) {e : ℕ} (oe : Odd e) (k j : ℕ) :
    let v:=total p (fun i => (e+2*t i)*(4*2^j))
    OeisA245212.a (2^k*v)≠(σ 1 (2^k*v):ℤ) := by
  classical
  let s:=2^j
  let u:=∏ i,p i
  let v:=total p (fun i => (e+2*t i)*(4*s))
  have ov : Odd v := Nat.coprime_two_left.mp (Nat.Coprime.prod_right (fun i _ =>
    (Nat.coprime_two_left.mpr (odd i)).pow_right _))
  obtain ⟨w,q,tau,v1⟩:=aggregate univ p t pr odd inj oe j
  obtain ⟨wc,oc⟩:=OMA.UniformDyad245212.scalar_coeff s e u (Fintype.card ι) oe rad rank
  change (W v:ZMod (16*s))=bump s e (∑ i,t i)*OMA.UniformDyad245212.weightCoeff s e u (Fintype.card ι)*(σ 1 v:ZMod (16*s)) at w
  change (σ 1 v:ZMod (8*s))=OMA.UniformDyad245212.ordinaryCoeff s e u (Fintype.card ι) at q
  change (σ 0 v:ZMod (8*s))=(1+4*(s:ZMod (8*s))*e)^(Fintype.card ι) at tau
  rw [wc] at w;rw [oc] at q
  obtain ⟨r,hr⟩:=rank
  have z : 8*(s:ZMod (8*s))=0 := by exact_mod_cast ZMod.natCast_self (8*s)
  have two : (1+4*(s:ZMod (8*s))*e)^2=1 := by
    linear_combination ((e:ZMod (8*s))+2*s*e^2)*z
  rw [show Fintype.card ι=2*(4*r) by omega,pow_mul,two,one_pow] at tau
  apply charge ov k j (impossible s e (∑ i,t i) (by dsimp [s];positivity) align) _ q tau v1
  dsimp only [bump] at w;push_cast at w ⊢;exact w

/-- The odd parts of the odd-prime exponents can vary independently:
only their sum, through one residue modulo four, enters the obstruction. -/
theorem mixed {ι : Type*} [Fintype ι] (p t : ι→ℕ) (pr : ∀ i, (p i).Prime)
    (odd : ∀ i, Odd (p i)) (inj : Function.Injective p)
    (rad : (∏ i,p i)%8=5) (rank : 8∣Fintype.card ι) (align : (∑ i,t i)%4≠2) {e : ℕ} (oe : Odd e)
    (k h : ℕ) : let m:=total p (fun i => 2^h*(e+2*t i))
    OeisA245212.a (2^k*m)≠(σ 1 (2^k*m):ℤ) := by
  classical
  let a (i : ι):=e+2*t i
  have oa (i : ι) : Odd (a i) := by dsimp [a];rw [Nat.odd_iff] at oe ⊢;omega
  cases h with
  | zero =>
    simp only [pow_zero,one_mul]
    intro eqn
    have non : Nonempty ι := by
      by_contra empty
      have : IsEmpty ι := not_nonempty_iff.mp empty
      simp at rad
    obtain ⟨i⟩:=non
    obtain ⟨b,hb⟩:=OMA.ExponentParity245212.two_mod_four p a pr odd inj k eqn ⟨i,oa i⟩
    have q:=Nat.odd_iff.mp (oa b)
    omega
  | succ h =>
    cases h with
    | zero =>
      let v:=total p a
      have index : total p (fun i => 2^(0+1)*(e+2*t i))=v^2 := by
        dsimp only [total,v,a];rw [←Finset.prod_pow]
        exact Finset.prod_congr rfl fun i _ => by rw [←pow_mul];congr 1;ring
      change OeisA245212.a (2^k*total p (fun i => 2^(0+1)*(e+2*t i)))≠_
      rw [index]
      intro eqn
      have ov : Odd v := Nat.coprime_two_left.mp (Nat.Coprime.prod_right (fun i _ =>
        (Nat.coprime_two_left.mpr (odd i)).pow_right _))
      obtain ⟨y,hy⟩:=OMA.DyadicPower245212.square_root_is_square ov eqn
      have point (i:ι) : (p i:ZMod 8)^(a i)=(p i:ZMod 8) := by
        obtain ⟨b,hb⟩:=oa i
        obtain ⟨x,hx⟩:=odd i
        have sq : (p i:ZMod 8)^2=1 := by
          rw [hx];push_cast;exact (by decide : ∀ x : ZMod 8,(2*x+1)^2=1) x
        rw [hb,pow_succ,pow_mul,sq,one_pow,one_mul]
      have rv : (v:ZMod 8)=5 := calc
        _ = ∏ i,(p i:ZMod 8)^(a i) := by dsimp [v,total];push_cast;rfl
        _ = ∏ i,(p i:ZMod 8) := Finset.prod_congr rfl fun i _ => point i
        _ = ((∏ i,p i:ℕ):ZMod 8) := by push_cast;rfl
        _ = 5 := (ZMod.natCast_eq_natCast_iff _ 5 8).mpr (by simpa [Nat.ModEq] using rad)
      rw [hy,Nat.cast_mul] at rv
      exact (by decide : ∀ x:ZMod 8,x*x≠5) y rv
    | succ j =>
      have index : (fun i => 2^(j+1+1)*(e+2*t i))=(fun i => (e+2*t i)*(4*2^j)) := by
        funext i;ring
      dsimp only;rw [index]
      exact many_four p t pr odd inj rad rank align oe k j

private theorem odd_power_modEight (p a : ℕ) (op : Odd p) (oa : Odd a) :
    (p:ZMod 8)^a=(p:ZMod 8) := by
  obtain ⟨b,hb⟩:=oa
  obtain ⟨x,hx⟩:=op
  have sq : (p:ZMod 8)^2=1 := by
    rw [hx];push_cast;exact (by decide : ∀ x : ZMod 8,(2*x+1)^2=1) x
  rw [hb,pow_succ,pow_mul,sq,one_pow,one_mul]

/-- If an odd integer u is 5 modulo eight, has a multiple of eight distinct
prime factors, and every valuation in its support is odd, then equality at any
positive power of u requires its total number of prime factors to be 4 mod 8. -/
theorem all_powers {u : ℕ} (u5 : u%8=5) (rank : 8∣u.primeFactors.card)
    (odd_orders : ∀ p∈u.primeFactors,Odd (u.factorization p)) (mult : (Ω u)%8≠4)
    (k E : ℕ) (pos : 0<E) : OeisA245212.a (2^k*u^E)≠(σ 1 (2^k*u^E):ℤ) := by
  classical
  let p : u.primeFactors → ℕ := Subtype.val
  let f (i:u.primeFactors):=u.factorization i
  let a (i:u.primeFactors):=f i/2
  have pr (i : u.primeFactors) : (p i).Prime := Nat.prime_of_mem_primeFactors i.property
  have ou : Odd u := Nat.odd_iff.mpr (by omega)
  have odd (i : u.primeFactors) : Odd (p i) := by
    apply Nat.odd_iff.mpr
    have d : p i∣u := Nat.dvd_of_mem_primeFactors i.property
    have no : ¬2∣p i := fun h => ou.not_two_dvd_nat (h.trans d)
    omega
  have ofact (i : u.primeFactors) : Odd (f i) := odd_orders i i.property
  have rep (i : u.primeFactors) : f i=1+2*a i := by
    have h:=Nat.odd_iff.mp (ofact i);change f i=1+2*(f i/2);omega
  have support_eq : u=total p f := Nat.prod_primeFactors_coe_pow_factorization ou.pos.ne'
  have residue : (∏ i,p i)%8=5 := by
    have red : (u:ZMod 8)=((∏ i,p i:ℕ):ZMod 8) := calc
      _ = ((total p f:ℕ):ZMod 8) := congrArg (fun n:ℕ => (n:ZMod 8)) support_eq
      _ = ∏ i,(p i:ZMod 8)^(f i) := by dsimp [total];push_cast;rfl
      _ = ∏ i,(p i:ZMod 8) := Finset.prod_congr rfl fun i _ => odd_power_modEight _ _ (odd i) (ofact i)
      _ = _ := by push_cast;rfl
    have uval : (u:ZMod 8)=5 := (ZMod.natCast_eq_natCast_iff u 5 8).mpr u5
    exact (ZMod.natCast_eq_natCast_iff _ 5 8).mp (red.symm.trans uval)
  have sumval : Ω u = ∑ i,f i := by
    rw [cardFactors_eq_sum_factorization,Finset.sum_coe_sort u.primeFactors (fun i => u.factorization i)]
    rfl
  have total_rank : Ω u=u.primeFactors.card+2*∑ i,a i := by
    rw [sumval,Finset.sum_congr rfl (fun i _ => rep i),Finset.sum_add_distrib,←Finset.mul_sum]
    simp
  obtain ⟨h,e,oe,he⟩:=Nat.exists_eq_two_pow_mul_odd pos.ne'
  have sum_ok : (∑ i,e*a i)%4≠2 := by
    rw [←Finset.mul_sum]
    have half : (∑ i,a i)%4≠2 := by omega
    have he' := Nat.odd_iff.mp oe
    rw [Nat.mul_mod]
    have ha : (∑ i,a i)%4=0 ∨ (∑ i,a i)%4=1 ∨ (∑ i,a i)%4=3 := by omega
    have hb : e%4=1 ∨ e%4=3 := by omega
    rcases ha with ha|ha|ha <;> rcases hb with hb|hb <;> rw [ha,hb] <;> decide
  have index : u^E=total p (fun i => 2^h*(e+2*(e*a i))) := by
    calc
      _ = (total p f)^E := congrArg (fun n:ℕ => n^E) support_eq
      _ = _ := by
        dsimp [total];rw [←Finset.prod_pow];apply Finset.prod_congr rfl
        intro i _
        rw [←pow_mul,rep i,he];congr 1;ring
  rw [index]
  exact mixed p (fun i => e*a i) pr odd Subtype.val_injective residue (by simpa using rank) sum_ok oe k h

#print axioms mixed
#print axioms all_powers

end OMA.MixedDyad245212

end
