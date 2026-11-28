import FormalConjectures.OEIS.«245212»

/-! Exclusion of every nontrivial odd power of a squarefree base of rank at most four. -/

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

namespace OMA.OddFaces245212
open OMA.Smooth245212
def limitX (p : ℕ) : ℚ := X p none
end OMA.OddFaces245212

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

theorem cap_anti {a b : ℕ} (ha : 1<a) (hab : a≤b) : limitX b≤limitX a := by
  have a' : (1:ℚ)<a := by exact_mod_cast ha
  have ab : (a:ℚ)≤b := by exact_mod_cast hab
  simp only [limitX,X,Y,sub_zero]
  exact add_le_add_right (one_div_le_one_div_of_le (by linarith) (by linarith)) 1

end OMA.OddFaces245212

/- Modulo three, the weighted divisor sum of every cube is one and its
ordinary divisor sum is zero or one. This rules out cubes divisible by three. -/
namespace OMA.Cube245212
open Finset Nat ArithmeticFunction OMA.Smooth245212 OMA.Abundance245212 OMA.OddFaces245212
open scoped ArithmeticFunction.sigma

private def wg (x : ZMod 3) (e : ℕ) := ∑ j∈range (e+1),x^j*((j:ZMod 3)+1)
private def sg (x : ZMod 3) (e : ℕ) := ∑ j∈range (e+1),x^j

private theorem next_w (x : ZMod 3) (e : ℕ) : wg x (3*(e+1))=wg x (3*e) := by
  unfold wg
  rw [show 3*(e+1)+1=(3*e+1)+3 by omega,sum_range_add]
  have z : (3:ZMod 3)=0 := by decide
  have frob : ∀ y : ZMod 3, y^3=y := by decide
  simp only [sum_range_succ,sum_range_zero,zero_add,add_zero,pow_add,pow_succ,pow_zero,
    Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,Nat.cast_zero,z,zero_mul]
  linear_combination (norm := (ring_nf; simp only [z,mul_zero,add_zero])) x^(3*e)*(frob x)

private theorem next_s (x : ZMod 3) (e : ℕ) :
    sg x (3*(e+1))=(1+x+x^2)+x^3*sg x (3*e) := by
  unfold sg
  rw [show 3*(e+1)+1=3+(3*e+1) by omega,sum_range_add]
  simp_rw [pow_add]
  rw [←mul_sum]
  congr 1
  norm_num [sum_range_succ]

private theorem cube_local (x : ZMod 3) (e : ℕ) :
    wg x (3*e)=1 ∧ (sg x (3*e)=0 ∨ sg x (3*e)=1) := by
  induction e with
  | zero => simp [wg,sg]
  | succ e ih =>
    rw [next_w,next_s]
    have c : ∀ a b : ZMod 3, b=0 ∨ b=1 → 1+a+a^2+a^3*b=0 ∨ 1+a+a^2+a^3*b=1 := by decide
    exact ⟨ih.1,c _ _ ih.2⟩

private theorem reduce_prime {p : ℕ} (hp : Nat.Prime p) (e : ℕ) :
    (W (p^e):ZMod 3)=wg p e ∧ (σ 1 (p^e):ZMod 3)=sg p e := by
  rw [w_pow hp,sigma_one_apply_prime_pow hp]
  simp [wg,sg]

theorem cube_residues {u : ℕ} (hu : u≠0) :
    (W (u^3):ZMod 3)=1 ∧ ((σ 1 (u^3):ZMod 3)=0 ∨ (σ 1 (u^3):ZMod 3)=1) := by
  induction u using Nat.recOnPrimeCoprime with
  | zero => contradiction
  | prime_pow p e hp =>
    rw [←pow_mul,Nat.mul_comm e 3,(reduce_prime hp _).1,(reduce_prime hp _).2]
    exact cube_local _ _
  | coprime a b ha hb cop ia ib =>
    have cp := (cop.pow_left 3).pow_right 3
    rw [mul_pow,w_mult.map_mul_of_coprime cp,isMultiplicative_sigma.map_mul_of_coprime cp]
    obtain ⟨wa,sa⟩ := ia (by omega)
    obtain ⟨wb,sb⟩ := ib (by omega)
    rcases sa with sa|sa <;> rcases sb with sb|sb <;> simp [wa,wb,sa,sb]

private theorem contradiction3 {n : ℕ} (hn : n≠0) (div : 3∣n)
    (w : (W n:ZMod 3)=1) (s : (σ 1 n:ZMod 3)=0 ∨ (σ 1 n:ZMod 3)=1) :
    OeisA245212.a n≠(σ 1 n:ℤ) := by
  intro eq
  have h := congrArg (fun x : ℕ => (x:ZMod 3)) (balance hn eq)
  have zero := (ZMod.natCast_eq_zero_iff n 3).mpr div
  simp only [Nat.cast_add,Nat.cast_mul,zero,mul_zero,zero_mul,w] at h
  rcases s with z|o
  · rw [z] at h; exact (by decide : (1:ZMod 3)+0≠0) h
  · rw [o] at h; exact (by decide : (1:ZMod 3)+1≠0) h

theorem no_cube_of_three {u : ℕ} (hu : 0<u) (h3 : 3∣u) :
    OeisA245212.a (u^3)≠(σ 1 (u^3):ℤ) := by
  apply contradiction3 (pow_ne_zero _ hu.ne') (h3.trans (dvd_pow_self _ (by decide : 3≠0)))
  · exact (cube_residues hu.ne').1
  · exact (cube_residues hu.ne').2

theorem no_three_times_cube {a u : ℕ} (ha : 0<a) (hu : 0<u) (cop : (3:ℕ).Coprime u) :
    OeisA245212.a (3^a*u^3)≠(σ 1 (3^a*u^3):ℤ) := by
  have div : 3∣3^a*u^3 := dvd_mul_of_dvd_left (dvd_pow_self _ ha.ne') _
  have cp := (cop.pow_left a).pow_right 3
  have zero : (3:ZMod 3)=0 := by decide
  have w3 : (W (3^a):ZMod 3)=1 := by
    rw [(reduce_prime (by decide : Nat.Prime 3) a).1,wg,sum_range_succ']; simp [pow_succ,zero]
  have s3 : (σ 1 (3^a):ZMod 3)=1 := by
    rw [(reduce_prime (by decide : Nat.Prime 3) a).2,sg,sum_range_succ']; simp [pow_succ,zero]
  apply contradiction3 (by positivity) div
  · rw [w_mult.map_mul_of_coprime cp,Nat.cast_mul,w3,(cube_residues hu.ne').1,one_mul]
  · rw [isMultiplicative_sigma.map_mul_of_coprime cp,Nat.cast_mul,s3,one_mul]
    exact (cube_residues hu.ne').2

private def little : Finset ℕ := {5,7,11,13,17}

private theorem little_table :
    ∀ D ∈ little.powerset, (∏ p∈D,limitX p)*(19/18:ℚ)^(6-D.card)<2 := by decide +kernel

theorem three_dvd_odd_of_six {n : ℕ} (hn : 1<n) (odd : Odd n)
    (hc : n.primeFactors.card≤6) (eq : OeisA245212.a n=(σ 1 n:ℤ)) : 3∣n := by
  classical
  by_contra no3
  let s := n.primeFactors
  let D := s∩little
  let E := s\little
  let p : s → ℕ := fun i => i.val
  let e : s → ℕ := fun i => n.factorization i.val
  have hpr (i : s) := Nat.prime_of_mem_primeFactors i.property
  have repr : total p e=n := (Nat.prod_primeFactors_coe_pow_factorization (by omega : n≠0)).symm
  have norm := normalized_of_eq p hpr Subtype.val_injective e (by rw [repr]; exact eq)
  let i : s := ⟨n.minFac,Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime (by omega),n.minFac_dvd,by omega⟩⟩
  have pos : 0<e i := (hpr i).factorization_pos_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors i.property)
  have cap := cap_needed p e (fun t => (hpr t).one_lt) i pos norm
  change 2≤∏ i : s,limitX i.val at cap
  rw [Finset.prod_coe_sort s limitX] at cap
  have bd (t) (hs : t∈E) : limitX t≤(19/18:ℚ) := by
    obtain ⟨ts,nt⟩ := Finset.mem_sdiff.mp hs
    have hp := Nat.prime_of_mem_primeFactors ts
    have di := Nat.dvd_of_mem_primeFactors ts
    have nt3 : t≠3 := fun h => no3 (h ▸ di)
    have nt2 : t≠2 := fun h => (Nat.not_even_iff_odd.mpr odd) (even_iff_two_dvd.mpr (h ▸ di))
    have hi : 19≤t := by
      by_contra! h
      interval_cases t <;> norm_num [little] at *
    exact (cap_anti (by decide : 1<19) hi).trans (by decide +kernel)
  have non (t : ℕ) (ht : t∈s) := x_nonneg (Nat.prime_of_mem_primeFactors ht).one_lt none
  have ebd := Finset.prod_le_prod (s:=E) (fun t ht => non t (Finset.mem_sdiff.mp ht).1) bd
  have union : D∪E=s := by ext; simp [D,E]; tauto
  have dis : Disjoint D E := by
    apply Finset.disjoint_left.mpr; intro t tm em
    exact (Finset.mem_sdiff.mp em).2 (Finset.mem_inter.mp tm).2
  have card : D.card+E.card≤6 := by rw [←card_union_of_disjoint dis,union]; exact hc
  have prod : (∏t∈D,limitX t)*(∏t∈E,limitX t)=∏t∈s,limitX t := by
    rw [←prod_union dis,union]
  have z := little_table D (mem_powerset.mpr (by exact inter_subset_right))
  rw [←prod] at cap
  exact (not_lt_of_ge cap) (lt_of_le_of_lt (mul_le_mul_of_nonneg_left
    (ebd.trans (by rw [Finset.prod_const]; exact pow_le_pow_right₀ (by norm_num) (by omega)))
    (Finset.prod_nonneg (fun t ht => non t (Finset.mem_inter.mp ht).1))) z)

theorem no_odd_cube_six {u : ℕ} (hu : 1<u) (odd : Odd u) (hc : u.primeFactors.card≤6) :
    OeisA245212.a (u^3)≠(σ 1 (u^3):ℤ) := by
  intro h
  have div := three_dvd_odd_of_six (one_lt_pow₀ hu (by decide : 3≠0)) (odd.pow (n:=3))
    (by rw [Nat.primeFactors_pow _ (by decide : 3≠0)]; exact hc) h
  exact no_cube_of_three (by omega) (Nat.prime_three.dvd_of_dvd_pow div) h

end OMA.Cube245212

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

/- Interval inequalities for one common exponent and a variable list of
strictly increasing prime bases. Each leaf has a separate exact rejection. -/
namespace OMA.Equal245212
open Finset OMA.Smooth245212 OMA.Moving245212

abbrev Region (k : ℕ) := Fin (k+1) → Band
def cutL {k} (b : Region k) (i : Fin (k+1)) (n : ℕ) : Region k :=
  Function.update b i ⟨(b i).lo,some n⟩
def cutR {k} (b : Region k) (i : Fin (k+1)) (n : ℕ) : Region k :=
  Function.update b i ⟨n+1,(b i).hi⟩

def Value {k} (v : Fin (k+1) → ℕ) : ℚ :=
  (∏ i : Fin k,X (v i.succ) (some (v 0)))+∏ i : Fin k,Y (v i.succ) (some (v 0))
def Low {k} (b : Region k) : ℚ :=
  (∏ i : Fin k,xl (b i.succ) (b 0))+∏ i : Fin k,yl (b i.succ) (b 0)
def High {k} (b : Region k) : ℚ :=
  (∏ i : Fin k,xu (b i.succ) (b 0))+∏ i : Fin k,yu (b i.succ) (b 0)

private theorem envelope {k} (b : Region k) (v : Fin (k+1) → ℕ)
    (lo : ∀ i : Fin k,1<(b i.succ).lo) (hv : ∀ i,(b i).Contains (v i)) :
    Low b≤Value v ∧ Value v≤High b := by
  have f (i : Fin k) := factor_bounds (lo i) (hv i.succ) (hv 0)
  exact ⟨add_le_add
    (prod_le_prod (fun i _ => (f i).1) (fun i _ => (f i).2.1))
    (prod_le_prod (fun i _ => (f i).2.2.2.1) (fun i _ => (f i).2.2.2.2.1)),
    add_le_add
    (prod_le_prod (fun i _ => (f i).1.trans (f i).2.1) (fun i _ => (f i).2.2.1))
    (prod_le_prod (fun i _ => (f i).2.2.2.1.trans (f i).2.2.2.2.1)
      (fun i _ => (f i).2.2.2.2.2))⟩

def Reject {k} (b : Region k) := ∀ v : Fin (k+1) → ℕ, (∀ i,(b i).Contains (v i)) →
    (∀ i : Fin k,Nat.Prime (v i.succ)) → StrictMono (fun i : Fin k => v i.succ) → Value v≠2

theorem split {k} (b : Region k) (i : Fin (k+1)) (c : ℕ)
    (hl : Reject (cutL b i c)) (hr : Reject (cutR b i c)) : Reject b := by
  intro v hv
  by_cases h : v i≤c
  · apply hl
    intro j; by_cases ji : j=i
    · subst j; simpa [cutL,Band.Contains] using And.intro (hv i).1 h
    · simpa [cutL,ji] using hv j
  · apply hr
    intro j; by_cases ji : j=i
    · subst j; simpa [cutR,Band.Contains] using And.intro (by omega : c+1≤v i) (hv i).2
    · simpa [cutR,ji] using hv j

inductive Cert (k : ℕ)
| leaf
| split (i : Fin (k+1)) (cut : ℕ) (l r : Cert k)

def valid {k} : Cert k → Region k → Bool
| .leaf,b => decide ((∃ i : Fin k,(b i.succ).hi=some (b i.succ).lo ∧ ¬Nat.Prime (b i.succ).lo) ∨
    (∃ i j : Fin k, i<j ∧ ((b j.succ).hi.map (fun z => decide (z≤(b i.succ).lo))).getD false=true) ∨
    (∀ i : Fin k,1<(b i.succ).lo) ∧ (High b<2 ∨ 2<Low b))
| .split i c l r,b => valid l (cutL b i c) && valid r (cutR b i c)

theorem sound {k b} (t : Cert k) (ok : valid t b=true) : Reject b := by
  induction t generalizing b with
  | split i c l r il ir =>
    obtain ⟨cl,cr⟩ := Bool.and_eq_true_iff.mp ok
    exact split b i c (il cl) (ir cr)
  | leaf =>
    intro v h hp ord
    rcases of_decide_eq_true ok with ⟨i,hi,nop⟩|⟨i,j,ij,hb⟩|⟨lo,cap⟩
    · have eq := Nat.le_antisymm (h i.succ).1 ((h i.succ).2 _ hi)
      exact (nop (eq.symm ▸ hp i)).elim
    · cases hi : (b j.succ).hi with
      | none => simp [hi] at hb
      | some m =>
        have upper : m≤(b i.succ).lo := by simpa [hi] using hb
        exact (False.elim ((ord ij).not_ge (((h j.succ).2 m hi).trans (upper.trans (h i.succ).1))))
    · rcases cap with sm|lg
      · exact ((envelope b v lo h).2.trans_lt sm).ne
      · exact (lg.trans_le (envelope b v lo h).1).ne'

end OMA.Equal245212

/- Equal-exponent interval certificates. Generated by equal_power_245212.py --lean. -/
namespace OMA.Equal245212
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
def domain1 : Region 1 := ![⟨1,none⟩,⟨3,some 3⟩]
private def c1 : Cert 1 := (.split 0 3 .leaf .leaf)
theorem root1 : Reject domain1 := sound c1 (by decide +kernel)
def domain2 : Region 2 := ![⟨1,none⟩,⟨3,some 3⟩,⟨5,none⟩]
private def c2 : Cert 2 := (.split 0 3 .leaf .leaf)
theorem root2 : Reject domain2 := sound c2 (by decide +kernel)
def domain3 : Region 3 := ![⟨1,none⟩,⟨3,some 3⟩,⟨5,none⟩,⟨7,none⟩]
private def b3l : Region 3 := cutL domain3 0 3
private def c3l : Cert 3 := .leaf
theorem h3l : Reject b3l := sound c3l (by decide +kernel)
private def b3r : Region 3 := cutR domain3 0 3
private def b3rl : Region 3 := cutL b3r 0 9
private def c3rl : Cert 3 := (.split 2 11 (.split 3 15 (.split 2 7 (.split 0 5 .leaf (.split 3 9 (.split 2 5 .leaf .leaf) .leaf)) .leaf) .leaf) .leaf)
theorem h3rl : Reject b3rl := sound c3rl (by decide +kernel)
private def b3rr : Region 3 := cutR b3r 0 9
private def b3rrl : Region 3 := cutL b3rr 2 11
private def b3rrll : Region 3 := cutL b3rrl 3 15
private def b3rrlll : Region 3 := cutL b3rrll 2 7
private def b3rrllll : Region 3 := cutL b3rrlll 0 21
private def c3rrllll : Cert 3 := (.split 3 9 (.split 2 5 (.split 0 13 (.split 3 7 .leaf (.split 0 11 .leaf (.split 3 8 .leaf .leaf))) (.split 3 7 .leaf (.split 0 16 (.split 3 8 .leaf .leaf) .leaf))) (.split 0 13 .leaf (.split 3 7 (.split 2 6 .leaf .leaf) .leaf))) (.split 2 5 (.split 0 13 .leaf (.split 3 12 (.split 0 16 .leaf (.split 3 10 .leaf .leaf)) .leaf)) .leaf))
theorem h3rrllll : Reject b3rrllll := sound c3rrllll (by decide +kernel)
private def b3rrlllr : Region 3 := cutR b3rrlll 0 21
private def b3rrlllrl : Region 3 := cutL b3rrlllr 3 9
private def c3rrlllrl : Cert 3 := (.split 2 5 .leaf (.split 0 45 (.split 3 7 (.split 2 6 .leaf .leaf) (.split 2 6 .leaf .leaf)) (.split 3 7 .leaf (.split 2 6 .leaf (.split 0 93 .leaf (.split 3 8 .leaf .leaf))))))
theorem h3rrlllrl : Reject b3rrlllrl := sound c3rrlllrl (by decide +kernel)
private def b3rrlllrr : Region 3 := cutR b3rrlllr 3 9
private def c3rrlllrr : Cert 3 := (.split 2 5 (.split 0 45 (.split 3 12 (.split 0 29 (.split 3 10 .leaf (.split 0 25 .leaf (.split 3 11 (.split 0 27 (.split 0 26 .leaf .leaf) .leaf) .leaf))) (.split 3 10 .leaf (.split 0 36 (.split 3 11 .leaf .leaf) .leaf))) .leaf) (.split 3 12 .leaf (.split 0 93 (.split 3 13 (.split 0 61 (.split 0 52 .leaf .leaf) .leaf) (.split 0 61 .leaf (.split 3 14 .leaf .leaf))) (.split 3 13 .leaf (.split 0 189 (.split 3 14 .leaf .leaf) .leaf))))) (.split 3 12 (.split 0 45 .leaf (.split 2 6 .leaf .leaf)) .leaf))
theorem h3rrlllrr : Reject b3rrlllrr := sound c3rrlllrr (by decide +kernel)
theorem h3rrlllr : Reject b3rrlllr := split b3rrlllr 3 9 h3rrlllrl h3rrlllrr
theorem h3rrlll : Reject b3rrlll := split b3rrlll 0 21 h3rrllll h3rrlllr
private def b3rrllr : Region 3 := cutR b3rrll 2 7
private def c3rrllr : Cert 3 := (.split 3 9 (.split 0 21 .leaf (.split 2 9 (.split 3 7 .leaf .leaf) .leaf)) .leaf)
theorem h3rrllr : Reject b3rrllr := sound c3rrllr (by decide +kernel)
theorem h3rrll : Reject b3rrll := split b3rrll 2 7 h3rrlll h3rrllr
private def b3rrlr : Region 3 := cutR b3rrl 3 15
private def c3rrlr : Cert 3 := (.split 2 7 (.split 0 21 .leaf (.split 2 5 (.split 3 33 (.split 0 45 .leaf (.split 3 21 (.split 0 93 .leaf (.split 3 18 (.split 0 189 .leaf (.split 3 16 .leaf .leaf)) .leaf)) .leaf)) .leaf) .leaf)) .leaf)
theorem h3rrlr : Reject b3rrlr := sound c3rrlr (by decide +kernel)
theorem h3rrl : Reject b3rrl := split b3rrl 3 15 h3rrll h3rrlr
private def b3rrr : Region 3 := cutR b3rr 2 11
private def c3rrr : Cert 3 := .leaf
theorem h3rrr : Reject b3rrr := sound c3rrr (by decide +kernel)
theorem h3rr : Reject b3rr := split b3rr 2 11 h3rrl h3rrr
theorem h3r : Reject b3r := split b3r 0 9 h3rl h3rr
theorem root3 : Reject domain3 := split domain3 0 3 h3l h3r
def domain4 : Region 4 := ![⟨1,none⟩,⟨3,some 3⟩,⟨5,none⟩,⟨7,none⟩,⟨11,none⟩]
private def b4l : Region 4 := cutL domain4 0 3
private def c4l : Cert 4 := (.split 0 1 .leaf .leaf)
theorem h4l : Reject b4l := sound c4l (by decide +kernel)
private def b4r : Region 4 := cutR domain4 0 3
private def b4rl : Region 4 := cutL b4r 0 9
private def b4rll : Region 4 := cutL b4rl 2 11
private def b4rlll : Region 4 := cutL b4rll 3 15
private def b4rllll : Region 4 := cutL b4rlll 2 7
private def b4rlllll : Region 4 := cutL b4rllll 0 5
private def c4rlllll : Cert 4 := (.split 4 23 (.split 3 9 (.split 2 5 (.split 4 15 (.split 0 4 .leaf (.split 3 7 (.split 4 12 .leaf .leaf) .leaf)) .leaf) .leaf) .leaf) .leaf)
theorem h4rlllll : Reject b4rlllll := sound c4rlllll (by decide +kernel)
private def b4rllllr : Region 4 := cutR b4rllll 0 5
private def b4rllllrl : Region 4 := cutL b4rllllr 4 23
private def b4rllllrll : Region 4 := cutL b4rllllrl 3 9
private def b4rllllrlll : Region 4 := cutL b4rllllrll 2 5
private def c4rllllrlll : Cert 4 := (.split 4 15 (.split 0 7 (.split 3 7 .leaf (.split 4 12 (.split 0 6 (.split 3 8 .leaf .leaf) .leaf) (.split 0 6 (.split 3 8 .leaf .leaf) .leaf))) .leaf) (.split 0 7 (.split 3 7 (.split 4 18 .leaf (.split 0 6 (.split 4 20 (.split 4 19 .leaf .leaf) .leaf) .leaf)) (.split 4 18 (.split 0 6 .leaf (.split 3 8 .leaf .leaf)) (.split 0 6 .leaf (.split 3 8 .leaf .leaf)))) (.split 3 7 .leaf (.split 4 18 .leaf (.split 3 8 .leaf .leaf)))))
theorem h4rllllrlll : Reject b4rllllrlll := sound c4rllllrlll (by decide +kernel)
private def b4rllllrllr : Region 4 := cutR b4rllllrll 2 5
private def c4rllllrllr : Cert 4 := (.split 4 15 (.split 0 7 (.split 3 7 (.split 2 6 .leaf .leaf) (.split 2 6 .leaf .leaf)) (.split 3 7 (.split 2 6 .leaf .leaf) (.split 2 6 .leaf (.split 4 12 (.split 3 8 .leaf .leaf) .leaf)))) (.split 0 7 .leaf (.split 3 7 (.split 2 6 .leaf .leaf) (.split 2 6 .leaf .leaf))))
theorem h4rllllrllr : Reject b4rllllrllr := sound c4rllllrllr (by decide +kernel)
theorem h4rllllrll : Reject b4rllllrll := split b4rllllrll 2 5 h4rllllrlll h4rllllrllr
private def b4rllllrlr : Region 4 := cutR b4rllllrl 3 9
private def b4rllllrlrl : Region 4 := cutL b4rllllrlr 2 5
private def c4rllllrlrl : Cert 4 := (.split 4 15 (.split 0 7 (.split 3 12 (.split 4 12 (.split 3 10 .leaf (.split 0 6 .leaf (.split 4 11 .leaf .leaf))) (.split 3 10 .leaf .leaf)) .leaf) (.split 3 12 (.split 4 12 .leaf (.split 3 10 .leaf (.split 4 13 (.split 0 8 (.split 3 11 .leaf .leaf) .leaf) (.split 0 8 (.split 3 11 (.split 4 14 .leaf .leaf) .leaf) (.split 3 11 .leaf .leaf))))) (.split 4 12 .leaf (.split 4 13 .leaf .leaf)))) (.split 0 7 .leaf (.split 3 12 (.split 4 18 (.split 3 10 .leaf (.split 0 8 .leaf (.split 3 11 (.split 4 16 .leaf .leaf) .leaf))) (.split 3 10 .leaf .leaf)) .leaf)))
theorem h4rllllrlrl : Reject b4rllllrlrl := sound c4rllllrlrl (by decide +kernel)
private def b4rllllrlrr : Region 4 := cutR b4rllllrlr 2 5
private def c4rllllrlrr : Cert 4 := (.split 4 15 (.split 0 7 .leaf (.split 3 12 (.split 2 6 .leaf .leaf) .leaf)) .leaf)
theorem h4rllllrlrr : Reject b4rllllrlrr := sound c4rllllrlrr (by decide +kernel)
theorem h4rllllrlr : Reject b4rllllrlr := split b4rllllrlr 2 5 h4rllllrlrl h4rllllrlrr
theorem h4rllllrl : Reject b4rllllrl := split b4rllllrl 3 9 h4rllllrll h4rllllrlr
private def b4rllllrr : Region 4 := cutR b4rllllr 4 23
private def b4rllllrrl : Region 4 := cutL b4rllllrr 3 9
private def b4rllllrrll : Region 4 := cutL b4rllllrrl 2 5
private def c4rllllrrll : Cert 4 := (.split 0 7 (.split 4 49 (.split 3 7 (.split 4 32 (.split 0 6 .leaf .leaf) .leaf) .leaf) .leaf) (.split 4 49 (.split 3 7 .leaf (.split 4 32 (.split 3 8 .leaf .leaf) (.split 3 8 .leaf .leaf))) (.split 3 7 (.split 4 101 (.split 0 8 (.split 4 67 (.split 4 57 .leaf (.split 4 62 .leaf .leaf)) .leaf) .leaf) (.split 0 8 .leaf (.split 4 205 .leaf (.split 4 413 (.split 4 275 (.split 4 235 .leaf (.split 4 254 (.split 4 244 (.split 4 239 .leaf (.split 4 241 .leaf (.split 4 242 .leaf (.split 4 243 .leaf .leaf)))) .leaf) .leaf)) .leaf) .leaf)))) .leaf)))
theorem h4rllllrrll : Reject b4rllllrrll := sound c4rllllrrll (by decide +kernel)
private def b4rllllrrlr : Region 4 := cutR b4rllllrrl 2 5
private def c4rllllrrlr : Cert 4 := (.split 4 49 (.split 0 7 .leaf (.split 3 7 .leaf .leaf)) .leaf)
theorem h4rllllrrlr : Reject b4rllllrrlr := sound c4rllllrrlr (by decide +kernel)
theorem h4rllllrrl : Reject b4rllllrrl := split b4rllllrrl 2 5 h4rllllrrll h4rllllrrlr
private def b4rllllrrr : Region 4 := cutR b4rllllrr 3 9
private def c4rllllrrr : Cert 4 := .leaf
theorem h4rllllrrr : Reject b4rllllrrr := sound c4rllllrrr (by decide +kernel)
theorem h4rllllrr : Reject b4rllllrr := split b4rllllrr 3 9 h4rllllrrl h4rllllrrr
theorem h4rllllr : Reject b4rllllr := split b4rllllr 4 23 h4rllllrl h4rllllrr
theorem h4rllll : Reject b4rllll := split b4rllll 0 5 h4rlllll h4rllllr
private def b4rlllr : Region 4 := cutR b4rlll 2 7
private def c4rlllr : Cert 4 := (.split 0 5 .leaf (.split 4 23 (.split 3 9 (.split 4 15 (.split 0 7 .leaf (.split 2 9 (.split 3 7 .leaf .leaf) .leaf)) .leaf) .leaf) .leaf))
theorem h4rlllr : Reject b4rlllr := sound c4rlllr (by decide +kernel)
theorem h4rlll : Reject b4rlll := split b4rlll 2 7 h4rllll h4rlllr
private def b4rllr : Region 4 := cutR b4rll 3 15
private def c4rllr : Cert 4 := (.split 2 7 (.split 0 5 .leaf (.split 4 23 (.split 2 5 (.split 3 33 (.split 4 15 .leaf .leaf) .leaf) .leaf) .leaf)) .leaf)
theorem h4rllr : Reject b4rllr := sound c4rllr (by decide +kernel)
theorem h4rll : Reject b4rll := split b4rll 3 15 h4rlll h4rllr
private def b4rlr : Region 4 := cutR b4rl 2 11
private def c4rlr : Cert 4 := .leaf
theorem h4rlr : Reject b4rlr := sound c4rlr (by decide +kernel)
theorem h4rl : Reject b4rl := split b4rl 2 11 h4rll h4rlr
private def b4rr : Region 4 := cutR b4r 0 9
private def b4rrl : Region 4 := cutL b4rr 2 11
private def b4rrll : Region 4 := cutL b4rrl 3 15
private def b4rrlll : Region 4 := cutL b4rrll 2 7
private def b4rrllll : Region 4 := cutL b4rrlll 0 21
private def b4rrlllll : Region 4 := cutL b4rrllll 4 23
private def b4rrllllll : Region 4 := cutL b4rrlllll 3 9
private def b4rrlllllll : Region 4 := cutL b4rrllllll 2 5
private def c4rrlllllll : Cert 4 := .leaf
theorem h4rrlllllll : Reject b4rrlllllll := sound c4rrlllllll (by decide +kernel)
private def b4rrllllllr : Region 4 := cutR b4rrllllll 2 5
private def b4rrllllllrl : Region 4 := cutL b4rrllllllr 4 15
private def c4rrllllllrl : Cert 4 := (.split 0 13 (.split 3 7 .leaf (.split 2 6 .leaf (.split 4 12 (.split 0 11 (.split 3 8 .leaf .leaf) .leaf) (.split 0 11 (.split 3 8 .leaf .leaf) (.split 3 8 .leaf .leaf))))) (.split 3 7 .leaf (.split 2 6 .leaf (.split 4 12 .leaf (.split 0 16 (.split 3 8 .leaf .leaf) .leaf)))))
theorem h4rrllllllrl : Reject b4rrllllllrl := sound c4rrllllllrl (by decide +kernel)
private def b4rrllllllrr : Region 4 := cutR b4rrllllllr 4 15
private def c4rrllllllrr : Cert 4 := (.split 0 13 (.split 3 7 (.split 2 6 .leaf .leaf) (.split 2 6 .leaf (.split 4 18 (.split 0 11 .leaf (.split 3 8 .leaf .leaf)) .leaf))) (.split 3 7 .leaf (.split 2 6 .leaf (.split 4 18 (.split 0 16 (.split 3 8 .leaf .leaf) (.split 3 8 .leaf .leaf)) (.split 0 16 (.split 3 8 .leaf .leaf) (.split 3 8 .leaf .leaf))))))
theorem h4rrllllllrr : Reject b4rrllllllrr := sound c4rrllllllrr (by decide +kernel)
theorem h4rrllllllr : Reject b4rrllllllr := split b4rrllllllr 4 15 h4rrllllllrl h4rrllllllrr
theorem h4rrllllll : Reject b4rrllllll := split b4rrllllll 2 5 h4rrlllllll h4rrllllllr
private def b4rrlllllr : Region 4 := cutR b4rrlllll 3 9
private def b4rrlllllrl : Region 4 := cutL b4rrlllllr 2 5
private def b4rrlllllrll : Region 4 := cutL b4rrlllllrl 4 15
private def c4rrlllllrll : Cert 4 := (.split 0 13 (.split 3 12 .leaf (.split 4 12 .leaf (.split 0 11 (.split 4 13 .leaf (.split 3 13 .leaf (.split 0 10 (.split 4 14 .leaf .leaf) (.split 4 14 .leaf .leaf)))) .leaf))) .leaf)
theorem h4rrlllllrll : Reject b4rrlllllrll := sound c4rrlllllrll (by decide +kernel)
private def b4rrlllllrlr : Region 4 := cutR b4rrlllllrl 4 15
private def b4rrlllllrlrl : Region 4 := cutL b4rrlllllrlr 0 13
private def b4rrlllllrlrll : Region 4 := cutL b4rrlllllrlrl 3 12
private def c4rrlllllrlrll : Cert 4 := (.split 4 18 (.split 0 11 (.split 3 10 .leaf (.split 3 11 .leaf .leaf)) .leaf) (.split 0 11 (.split 3 10 .leaf (.split 4 20 (.split 3 11 (.split 0 10 (.split 4 19 .leaf .leaf) .leaf) .leaf) (.split 3 11 (.split 0 10 .leaf (.split 4 21 .leaf (.split 4 22 .leaf .leaf))) .leaf))) (.split 3 10 .leaf (.split 4 20 .leaf (.split 3 11 .leaf .leaf)))))
theorem h4rrlllllrlrll : Reject b4rrlllllrlrll := sound c4rrlllllrlrll (by decide +kernel)
private def b4rrlllllrlrlr : Region 4 := cutR b4rrlllllrlrl 3 12
private def c4rrlllllrlrlr : Cert 4 := (.split 4 18 (.split 0 11 (.split 3 13 (.split 4 16 .leaf (.split 0 10 .leaf (.split 4 17 .leaf .leaf))) .leaf) (.split 3 13 .leaf (.split 4 16 .leaf (.split 3 14 .leaf .leaf)))) (.split 0 11 .leaf (.split 3 13 (.split 4 20 (.split 0 12 (.split 4 19 .leaf .leaf) .leaf) (.split 0 12 .leaf (.split 4 21 .leaf .leaf))) .leaf)))
theorem h4rrlllllrlrlr : Reject b4rrlllllrlrlr := sound c4rrlllllrlrlr (by decide +kernel)
theorem h4rrlllllrlrl : Reject b4rrlllllrlrl := split b4rrlllllrlrl 3 12 h4rrlllllrlrll h4rrlllllrlrlr
private def b4rrlllllrlrr : Region 4 := cutR b4rrlllllrlr 0 13
private def c4rrlllllrlrr : Cert 4 := (.split 3 12 .leaf (.split 4 18 .leaf (.split 0 16 (.split 3 13 .leaf (.split 4 20 (.split 0 14 (.split 3 14 .leaf .leaf) .leaf) (.split 0 14 .leaf (.split 3 14 .leaf .leaf)))) .leaf)))
theorem h4rrlllllrlrr : Reject b4rrlllllrlrr := sound c4rrlllllrlrr (by decide +kernel)
theorem h4rrlllllrlr : Reject b4rrlllllrlr := split b4rrlllllrlr 0 13 h4rrlllllrlrl h4rrlllllrlrr
theorem h4rrlllllrl : Reject b4rrlllllrl := split b4rrlllllrl 4 15 h4rrlllllrll h4rrlllllrlr
private def b4rrlllllrr : Region 4 := cutR b4rrlllllr 2 5
private def b4rrlllllrrl : Region 4 := cutL b4rrlllllrr 4 15
private def c4rrlllllrrl : Cert 4 := (.split 0 13 (.split 3 12 (.split 2 6 .leaf (.split 4 12 (.split 3 10 .leaf .leaf) .leaf)) (.split 2 6 .leaf .leaf)) (.split 3 12 (.split 2 6 .leaf (.split 4 12 (.split 0 16 (.split 3 10 .leaf (.split 4 11 .leaf .leaf)) (.split 3 10 .leaf (.split 0 18 (.split 4 11 .leaf .leaf) (.split 4 11 .leaf .leaf)))) (.split 0 16 (.split 3 10 .leaf .leaf) (.split 3 10 .leaf (.split 4 13 (.split 0 18 .leaf (.split 3 11 (.split 0 19 .leaf .leaf) .leaf)) .leaf))))) (.split 2 6 .leaf (.split 4 12 .leaf .leaf))))
theorem h4rrlllllrrl : Reject b4rrlllllrrl := sound c4rrlllllrrl (by decide +kernel)
private def b4rrlllllrrr : Region 4 := cutR b4rrlllllrr 4 15
private def c4rrlllllrrr : Cert 4 := (.split 0 13 (.split 3 12 (.split 2 6 .leaf .leaf) .leaf) (.split 3 12 (.split 2 6 .leaf .leaf) (.split 2 6 .leaf .leaf)))
theorem h4rrlllllrrr : Reject b4rrlllllrrr := sound c4rrlllllrrr (by decide +kernel)
theorem h4rrlllllrr : Reject b4rrlllllrr := split b4rrlllllrr 4 15 h4rrlllllrrl h4rrlllllrrr
theorem h4rrlllllr : Reject b4rrlllllr := split b4rrlllllr 2 5 h4rrlllllrl h4rrlllllrr
theorem h4rrlllll : Reject b4rrlllll := split b4rrlllll 3 9 h4rrllllll h4rrlllllr
private def b4rrllllr : Region 4 := cutR b4rrllll 4 23
private def b4rrllllrl : Region 4 := cutL b4rrllllr 3 9
private def b4rrllllrll : Region 4 := cutL b4rrllllrl 2 5
private def c4rrllllrll : Cert 4 := (.split 0 13 (.split 4 49 (.split 3 7 .leaf (.split 4 32 .leaf (.split 0 11 (.split 3 8 .leaf .leaf) .leaf))) (.split 3 7 .leaf (.split 4 101 (.split 0 11 (.split 3 8 .leaf .leaf) (.split 3 8 .leaf .leaf)) (.split 0 11 (.split 3 8 .leaf .leaf) (.split 3 8 .leaf .leaf))))) (.split 4 49 .leaf (.split 3 7 .leaf (.split 4 101 .leaf (.split 0 16 (.split 3 8 .leaf .leaf) .leaf)))))
theorem h4rrllllrll : Reject b4rrllllrll := sound c4rrllllrll (by decide +kernel)
private def b4rrllllrlr : Region 4 := cutR b4rrllllrl 2 5
private def c4rrllllrlr : Cert 4 := (.split 0 13 (.split 4 49 (.split 3 7 (.split 2 6 .leaf .leaf) (.split 2 6 .leaf .leaf)) (.split 3 7 (.split 2 6 .leaf .leaf) .leaf)) (.split 4 49 (.split 3 7 (.split 2 6 .leaf .leaf) (.split 2 6 .leaf (.split 4 32 (.split 0 16 .leaf (.split 3 8 .leaf .leaf)) .leaf))) (.split 3 7 (.split 2 6 .leaf .leaf) (.split 2 6 .leaf .leaf))))
theorem h4rrllllrlr : Reject b4rrllllrlr := sound c4rrllllrlr (by decide +kernel)
theorem h4rrllllrl : Reject b4rrllllrl := split b4rrllllrl 2 5 h4rrllllrll h4rrllllrlr
private def b4rrllllrr : Region 4 := cutR b4rrllllr 3 9
private def b4rrllllrrl : Region 4 := cutL b4rrllllrr 2 5
private def b4rrllllrrll : Region 4 := cutL b4rrllllrrl 0 13
private def c4rrllllrrll : Cert 4 := (.split 4 49 (.split 3 12 (.split 4 32 (.split 3 10 .leaf (.split 0 11 .leaf (.split 4 27 (.split 3 11 (.split 0 12 (.split 4 25 .leaf (.split 4 26 .leaf .leaf)) .leaf) .leaf) (.split 3 11 (.split 0 12 .leaf (.split 4 29 .leaf (.split 4 30 .leaf .leaf))) .leaf)))) (.split 3 10 .leaf .leaf)) .leaf) .leaf)
theorem h4rrllllrrll : Reject b4rrllllrrll := sound c4rrllllrrll (by decide +kernel)
private def b4rrllllrrlr : Region 4 := cutR b4rrllllrrl 0 13
private def b4rrllllrrlrl : Region 4 := cutL b4rrllllrrlr 4 49
private def b4rrllllrrlrll : Region 4 := cutL b4rrllllrrlrl 3 12
private def c4rrllllrrlrll : Cert 4 := (.split 4 32 (.split 0 16 (.split 3 10 .leaf (.split 4 27 .leaf (.split 3 11 .leaf .leaf))) .leaf) (.split 0 16 (.split 3 10 .leaf (.split 4 39 (.split 3 11 (.split 0 14 (.split 4 35 .leaf .leaf) .leaf) .leaf) (.split 3 11 (.split 0 14 .leaf (.split 4 44 (.split 0 15 (.split 4 41 .leaf .leaf) .leaf) (.split 0 15 .leaf (.split 4 46 .leaf (.split 4 47 .leaf (.split 4 48 .leaf .leaf)))))) .leaf))) (.split 3 10 .leaf (.split 4 39 (.split 0 18 (.split 3 11 .leaf .leaf) .leaf) (.split 0 18 (.split 3 11 .leaf .leaf) (.split 3 11 .leaf .leaf))))))
theorem h4rrllllrrlrll : Reject b4rrllllrrlrll := sound c4rrllllrrlrll (by decide +kernel)
private def b4rrllllrrlrlr : Region 4 := cutR b4rrllllrrlrl 3 12
private def b4rrllllrrlrlrl : Region 4 := cutL b4rrllllrrlrlr 4 32
private def c4rrllllrrlrlrl : Cert 4 := (.split 0 16 (.split 3 13 (.split 4 27 (.split 0 14 .leaf (.split 4 25 .leaf (.split 0 15 .leaf .leaf))) (.split 0 14 .leaf (.split 4 29 (.split 0 15 .leaf (.split 4 28 .leaf .leaf)) .leaf))) (.split 4 27 (.split 0 14 .leaf (.split 3 14 .leaf .leaf)) .leaf)) (.split 3 13 (.split 4 27 .leaf (.split 0 18 (.split 4 29 .leaf (.split 0 17 (.split 4 30 .leaf .leaf) .leaf)) .leaf)) (.split 4 27 (.split 0 18 (.split 3 14 .leaf .leaf) (.split 3 14 .leaf .leaf)) (.split 0 18 (.split 3 14 .leaf .leaf) (.split 3 14 .leaf .leaf)))))
theorem h4rrllllrrlrlrl : Reject b4rrllllrrlrlrl := sound c4rrllllrrlrlrl (by decide +kernel)
private def b4rrllllrrlrlrr : Region 4 := cutR b4rrllllrrlrlr 4 32
private def c4rrllllrrlrlrr : Cert 4 := (.split 0 16 .leaf (.split 3 13 (.split 4 39 (.split 0 18 (.split 4 35 (.split 0 17 .leaf (.split 4 33 .leaf .leaf)) .leaf) (.split 4 35 .leaf (.split 0 19 (.split 4 37 (.split 4 36 .leaf .leaf) .leaf) .leaf))) (.split 0 18 .leaf (.split 4 44 (.split 0 19 .leaf (.split 4 41 (.split 0 20 .leaf .leaf) (.split 0 20 .leaf (.split 4 42 .leaf .leaf)))) .leaf))) (.split 4 39 (.split 0 18 .leaf (.split 3 14 .leaf .leaf)) .leaf)))
theorem h4rrllllrrlrlrr : Reject b4rrllllrrlrlrr := sound c4rrllllrrlrlrr (by decide +kernel)
theorem h4rrllllrrlrlr : Reject b4rrllllrrlrlr := split b4rrllllrrlrlr 4 32 h4rrllllrrlrlrl h4rrllllrrlrlrr
theorem h4rrllllrrlrl : Reject b4rrllllrrlrl := split b4rrllllrrlrl 3 12 h4rrllllrrlrll h4rrllllrrlrlr
private def b4rrllllrrlrr : Region 4 := cutR b4rrllllrrlr 4 49
private def b4rrllllrrlrrl : Region 4 := cutL b4rrllllrrlrr 3 12
private def b4rrllllrrlrrll : Region 4 := cutL b4rrllllrrlrrl 4 101
private def c4rrllllrrlrrll : Cert 4 := (.split 0 16 (.split 3 10 .leaf .leaf) (.split 3 10 .leaf (.split 4 67 (.split 0 18 (.split 3 11 (.split 4 57 (.split 0 17 (.split 4 53 .leaf (.split 4 55 .leaf (.split 4 56 .leaf .leaf))) .leaf) (.split 0 17 .leaf (.split 4 62 .leaf (.split 4 64 .leaf (.split 4 65 .leaf (.split 4 66 .leaf .leaf)))))) .leaf) (.split 3 11 .leaf .leaf)) (.split 0 18 .leaf (.split 3 11 (.split 4 81 (.split 0 19 (.split 4 73 .leaf (.split 4 77 .leaf (.split 4 79 (.split 4 78 .leaf .leaf) .leaf))) .leaf) (.split 0 19 .leaf (.split 4 90 .leaf (.split 0 20 (.split 4 95 .leaf .leaf) .leaf)))) .leaf)))))
theorem h4rrllllrrlrrll : Reject b4rrllllrrlrrll := sound c4rrllllrrlrrll (by decide +kernel)
private def b4rrllllrrlrrlr : Region 4 := cutR b4rrllllrrlrrl 4 101
private def c4rrllllrrlrrlr : Cert 4 := (.split 0 16 .leaf (.split 3 10 .leaf (.split 4 205 (.split 0 18 .leaf (.split 3 11 (.split 4 136 (.split 0 19 .leaf (.split 4 116 (.split 0 20 .leaf .leaf) .leaf)) .leaf) .leaf)) .leaf)))
theorem h4rrllllrrlrrlr : Reject b4rrllllrrlrrlr := sound c4rrllllrrlrrlr (by decide +kernel)
theorem h4rrllllrrlrrl : Reject b4rrllllrrlrrl := split b4rrllllrrlrrl 4 101 h4rrllllrrlrrll h4rrllllrrlrrlr
private def b4rrllllrrlrrr : Region 4 := cutR b4rrllllrrlrr 3 12
private def c4rrllllrrlrrr : Cert 4 := .leaf
theorem h4rrllllrrlrrr : Reject b4rrllllrrlrrr := sound c4rrllllrrlrrr (by decide +kernel)
theorem h4rrllllrrlrr : Reject b4rrllllrrlrr := split b4rrllllrrlrr 3 12 h4rrllllrrlrrl h4rrllllrrlrrr
theorem h4rrllllrrlr : Reject b4rrllllrrlr := split b4rrllllrrlr 4 49 h4rrllllrrlrl h4rrllllrrlrr
theorem h4rrllllrrl : Reject b4rrllllrrl := split b4rrllllrrl 0 13 h4rrllllrrll h4rrllllrrlr
private def b4rrllllrrr : Region 4 := cutR b4rrllllrr 2 5
private def c4rrllllrrr : Cert 4 := (.split 4 49 (.split 0 13 .leaf (.split 3 12 (.split 2 6 .leaf .leaf) .leaf)) .leaf)
theorem h4rrllllrrr : Reject b4rrllllrrr := sound c4rrllllrrr (by decide +kernel)
theorem h4rrllllrr : Reject b4rrllllrr := split b4rrllllrr 2 5 h4rrllllrrl h4rrllllrrr
theorem h4rrllllr : Reject b4rrllllr := split b4rrllllr 3 9 h4rrllllrl h4rrllllrr
theorem h4rrllll : Reject b4rrllll := split b4rrllll 4 23 h4rrlllll h4rrllllr
private def b4rrlllr : Region 4 := cutR b4rrlll 0 21
private def b4rrlllrl : Region 4 := cutL b4rrlllr 4 23
private def b4rrlllrll : Region 4 := cutL b4rrlllrl 3 9
private def c4rrlllrll : Cert 4 := (.split 2 5 .leaf (.split 4 15 .leaf (.split 0 45 (.split 3 7 .leaf (.split 2 6 .leaf (.split 4 18 .leaf (.split 0 29 (.split 3 8 .leaf .leaf) .leaf)))) .leaf)))
theorem h4rrlllrll : Reject b4rrlllrll := sound c4rrlllrll (by decide +kernel)
private def b4rrlllrlr : Region 4 := cutR b4rrlllrl 3 9
private def b4rrlllrlrl : Region 4 := cutL b4rrlllrlr 2 5
private def c4rrlllrlrl : Cert 4 := .leaf
theorem h4rrlllrlrl : Reject b4rrlllrlrl := sound c4rrlllrlrl (by decide +kernel)
private def b4rrlllrlrr : Region 4 := cutR b4rrlllrlr 2 5
private def b4rrlllrlrrl : Region 4 := cutL b4rrlllrlrr 4 15
private def b4rrlllrlrrll : Region 4 := cutL b4rrlllrlrrl 0 45
private def c4rrlllrlrrll : Cert 4 := (.split 3 12 (.split 2 6 .leaf (.split 4 12 .leaf (.split 0 29 (.split 3 10 .leaf (.split 4 13 (.split 0 25 (.split 3 11 .leaf .leaf) .leaf) (.split 0 25 (.split 3 11 (.split 4 14 .leaf .leaf) .leaf) (.split 3 11 (.split 4 14 .leaf .leaf) .leaf)))) (.split 3 10 .leaf (.split 4 13 .leaf (.split 0 36 (.split 3 11 .leaf .leaf) .leaf)))))) (.split 2 6 .leaf (.split 4 12 .leaf (.split 0 29 .leaf (.split 4 13 .leaf (.split 3 13 (.split 0 36 .leaf (.split 4 14 .leaf .leaf)) .leaf))))))
theorem h4rrlllrlrrll : Reject b4rrlllrlrrll := sound c4rrlllrlrrll (by decide +kernel)
private def b4rrlllrlrrlr : Region 4 := cutR b4rrlllrlrrl 0 45
private def c4rrlllrlrrlr : Cert 4 := (.split 3 12 .leaf (.split 2 6 .leaf (.split 4 12 .leaf (.split 0 93 (.split 4 13 .leaf (.split 3 13 (.split 0 61 (.split 4 14 .leaf .leaf) .leaf) (.split 0 61 (.split 4 14 .leaf .leaf) (.split 4 14 .leaf .leaf)))) (.split 4 13 .leaf (.split 3 13 .leaf (.split 0 189 (.split 4 14 .leaf .leaf) .leaf)))))))
theorem h4rrlllrlrrlr : Reject b4rrlllrlrrlr := sound c4rrlllrlrrlr (by decide +kernel)
theorem h4rrlllrlrrl : Reject b4rrlllrlrrl := split b4rrlllrlrrl 0 45 h4rrlllrlrrll h4rrlllrlrrlr
private def b4rrlllrlrrr : Region 4 := cutR b4rrlllrlrr 4 15
private def b4rrlllrlrrrl : Region 4 := cutL b4rrlllrlrrr 0 45
private def c4rrlllrlrrrl : Cert 4 := (.split 3 12 (.split 2 6 .leaf (.split 4 18 (.split 0 29 (.split 3 10 .leaf .leaf) (.split 3 10 .leaf (.split 0 36 (.split 3 11 (.split 4 16 .leaf .leaf) .leaf) (.split 3 11 (.split 4 16 .leaf (.split 0 40 (.split 4 17 .leaf .leaf) (.split 4 17 .leaf .leaf))) .leaf)))) (.split 0 29 .leaf (.split 3 10 .leaf .leaf)))) (.split 2 6 .leaf .leaf))
theorem h4rrlllrlrrrl : Reject b4rrlllrlrrrl := sound c4rrlllrlrrrl (by decide +kernel)
private def b4rrlllrlrrrr : Region 4 := cutR b4rrlllrlrrr 0 45
private def b4rrlllrlrrrrl : Region 4 := cutL b4rrlllrlrrrr 3 12
private def b4rrlllrlrrrrll : Region 4 := cutL b4rrlllrlrrrrl 2 6
private def c4rrlllrlrrrrll : Cert 4 := .leaf
theorem h4rrlllrlrrrrll : Reject b4rrlllrlrrrrll := sound c4rrlllrlrrrrll (by decide +kernel)
private def b4rrlllrlrrrrlr : Region 4 := cutR b4rrlllrlrrrrl 2 6
private def b4rrlllrlrrrrlrl : Region 4 := cutL b4rrlllrlrrrrlr 4 18
private def c4rrlllrlrrrrlrl : Cert 4 := (.split 3 10 .leaf (.split 0 93 (.split 0 61 (.split 3 11 .leaf .leaf) (.split 3 11 .leaf .leaf)) .leaf))
theorem h4rrlllrlrrrrlrl : Reject b4rrlllrlrrrrlrl := sound c4rrlllrlrrrrlrl (by decide +kernel)
private def b4rrlllrlrrrrlrr : Region 4 := cutR b4rrlllrlrrrrlr 4 18
private def b4rrlllrlrrrrlrrl : Region 4 := cutL b4rrlllrlrrrrlrr 3 10
private def c4rrlllrlrrrrlrrl : Cert 4 := .leaf
theorem h4rrlllrlrrrrlrrl : Reject b4rrlllrlrrrrlrrl := sound c4rrlllrlrrrrlrrl (by decide +kernel)
private def b4rrlllrlrrrrlrrr : Region 4 := cutR b4rrlllrlrrrrlrr 3 10
private def b4rrlllrlrrrrlrrrl : Region 4 := cutL b4rrlllrlrrrrlrrr 0 93
private def c4rrlllrlrrrrlrrrl : Cert 4 := (.split 4 20 (.split 0 61 (.split 3 11 (.split 0 52 (.split 4 19 (.split 0 48 .leaf (.split 0 50 .leaf (.split 0 51 .leaf .leaf))) .leaf) (.split 4 19 .leaf .leaf)) .leaf) (.split 3 11 .leaf .leaf)) (.split 0 61 .leaf (.split 3 11 (.split 4 21 .leaf .leaf) .leaf)))
theorem h4rrlllrlrrrrlrrrl : Reject b4rrlllrlrrrrlrrrl := sound c4rrlllrlrrrrlrrrl (by decide +kernel)
private def b4rrlllrlrrrrlrrrr : Region 4 := cutR b4rrlllrlrrrrlrrr 0 93
private def c4rrlllrlrrrrlrrrr : Cert 4 := (.split 4 20 (.split 0 189 (.split 3 11 .leaf .leaf) .leaf) (.split 0 189 (.split 3 11 (.split 4 21 .leaf (.split 0 125 (.split 0 107 (.split 4 22 .leaf .leaf) (.split 4 22 .leaf .leaf)) (.split 0 151 (.split 4 22 .leaf (.split 0 137 (.split 0 131 (.split 0 128 .leaf (.split 0 129 .leaf .leaf)) .leaf) .leaf)) .leaf))) .leaf) (.split 3 11 .leaf .leaf)))
theorem h4rrlllrlrrrrlrrrr : Reject b4rrlllrlrrrrlrrrr := sound c4rrlllrlrrrrlrrrr (by decide +kernel)
theorem h4rrlllrlrrrrlrrr : Reject b4rrlllrlrrrrlrrr := split b4rrlllrlrrrrlrrr 0 93 h4rrlllrlrrrrlrrrl h4rrlllrlrrrrlrrrr
theorem h4rrlllrlrrrrlrr : Reject b4rrlllrlrrrrlrr := split b4rrlllrlrrrrlrr 3 10 h4rrlllrlrrrrlrrl h4rrlllrlrrrrlrrr
theorem h4rrlllrlrrrrlr : Reject b4rrlllrlrrrrlr := split b4rrlllrlrrrrlr 4 18 h4rrlllrlrrrrlrl h4rrlllrlrrrrlrr
theorem h4rrlllrlrrrrl : Reject b4rrlllrlrrrrl := split b4rrlllrlrrrrl 2 6 h4rrlllrlrrrrll h4rrlllrlrrrrlr
private def b4rrlllrlrrrrr : Region 4 := cutR b4rrlllrlrrrr 3 12
private def b4rrlllrlrrrrrl : Region 4 := cutL b4rrlllrlrrrrr 2 6
private def c4rrlllrlrrrrrl : Cert 4 := .leaf
theorem h4rrlllrlrrrrrl : Reject b4rrlllrlrrrrrl := sound c4rrlllrlrrrrrl (by decide +kernel)
private def b4rrlllrlrrrrrr : Region 4 := cutR b4rrlllrlrrrrr 2 6
private def b4rrlllrlrrrrrrl : Region 4 := cutL b4rrlllrlrrrrrr 4 18
private def c4rrlllrlrrrrrrl : Cert 4 := (.split 0 93 (.split 3 13 (.split 0 61 .leaf (.split 4 16 .leaf .leaf)) .leaf) (.split 3 13 (.split 0 189 (.split 4 16 .leaf (.split 0 125 (.split 4 17 (.split 0 107 .leaf (.split 0 115 (.split 0 111 .leaf (.split 0 113 .leaf .leaf)) .leaf)) .leaf) (.split 4 17 .leaf .leaf))) (.split 4 16 .leaf (.split 0 381 (.split 4 17 .leaf .leaf) .leaf))) (.split 0 189 (.split 4 16 .leaf .leaf) (.split 4 16 .leaf (.split 3 14 .leaf .leaf)))))
theorem h4rrlllrlrrrrrrl : Reject b4rrlllrlrrrrrrl := sound c4rrlllrlrrrrrrl (by decide +kernel)
private def b4rrlllrlrrrrrrr : Region 4 := cutR b4rrlllrlrrrrrr 4 18
private def c4rrlllrlrrrrrrr : Cert 4 := (.split 0 93 .leaf (.split 3 13 (.split 4 20 (.split 0 189 .leaf (.split 0 381 .leaf (.split 4 19 (.split 0 765 .leaf (.split 0 1533 (.split 0 1021 .leaf (.split 0 1226 .leaf (.split 0 1363 .leaf (.split 0 1443 (.split 0 1402 (.split 0 1382 .leaf (.split 0 1392 (.split 0 1387 .leaf (.split 0 1389 .leaf (.split 0 1390 .leaf (.split 0 1391 .leaf .leaf)))) .leaf)) .leaf) .leaf)))) .leaf)) .leaf))) .leaf) .leaf))
theorem h4rrlllrlrrrrrrr : Reject b4rrlllrlrrrrrrr := sound c4rrlllrlrrrrrrr (by decide +kernel)
theorem h4rrlllrlrrrrrr : Reject b4rrlllrlrrrrrr := split b4rrlllrlrrrrrr 4 18 h4rrlllrlrrrrrrl h4rrlllrlrrrrrrr
theorem h4rrlllrlrrrrr : Reject b4rrlllrlrrrrr := split b4rrlllrlrrrrr 2 6 h4rrlllrlrrrrrl h4rrlllrlrrrrrr
theorem h4rrlllrlrrrr : Reject b4rrlllrlrrrr := split b4rrlllrlrrrr 3 12 h4rrlllrlrrrrl h4rrlllrlrrrrr
theorem h4rrlllrlrrr : Reject b4rrlllrlrrr := split b4rrlllrlrrr 0 45 h4rrlllrlrrrl h4rrlllrlrrrr
theorem h4rrlllrlrr : Reject b4rrlllrlrr := split b4rrlllrlrr 4 15 h4rrlllrlrrl h4rrlllrlrrr
theorem h4rrlllrlr : Reject b4rrlllrlr := split b4rrlllrlr 2 5 h4rrlllrlrl h4rrlllrlrr
theorem h4rrlllrl : Reject b4rrlllrl := split b4rrlllrl 3 9 h4rrlllrll h4rrlllrlr
private def b4rrlllrr : Region 4 := cutR b4rrlllr 4 23
private def b4rrlllrrl : Region 4 := cutL b4rrlllrr 3 9
private def b4rrlllrrll : Region 4 := cutL b4rrlllrrl 2 5
private def c4rrlllrrll : Cert 4 := .leaf
theorem h4rrlllrrll : Reject b4rrlllrrll := sound c4rrlllrrll (by decide +kernel)
private def b4rrlllrrlr : Region 4 := cutR b4rrlllrrl 2 5
private def b4rrlllrrlrl : Region 4 := cutL b4rrlllrrlr 4 49
private def c4rrlllrrlrl : Cert 4 := (.split 0 45 (.split 3 7 .leaf (.split 2 6 .leaf (.split 4 32 (.split 0 29 (.split 3 8 .leaf .leaf) (.split 3 8 .leaf .leaf)) (.split 0 29 (.split 3 8 .leaf .leaf) (.split 3 8 .leaf .leaf))))) (.split 3 7 .leaf (.split 2 6 .leaf (.split 4 32 (.split 0 93 (.split 3 8 .leaf .leaf) .leaf) (.split 0 93 (.split 3 8 .leaf .leaf) (.split 3 8 .leaf .leaf))))))
theorem h4rrlllrrlrl : Reject b4rrlllrrlrl := sound c4rrlllrrlrl (by decide +kernel)
private def b4rrlllrrlrr : Region 4 := cutR b4rrlllrrlr 4 49
private def c4rrlllrrlrr : Cert 4 := (.split 0 45 (.split 3 7 (.split 2 6 .leaf .leaf) (.split 2 6 .leaf (.split 4 101 (.split 0 29 .leaf (.split 3 8 .leaf .leaf)) .leaf))) (.split 3 7 .leaf (.split 2 6 .leaf (.split 4 101 (.split 0 93 (.split 3 8 .leaf .leaf) (.split 3 8 .leaf .leaf)) (.split 0 93 (.split 3 8 .leaf .leaf) (.split 3 8 .leaf .leaf))))))
theorem h4rrlllrrlrr : Reject b4rrlllrrlrr := sound c4rrlllrrlrr (by decide +kernel)
theorem h4rrlllrrlr : Reject b4rrlllrrlr := split b4rrlllrrlr 4 49 h4rrlllrrlrl h4rrlllrrlrr
theorem h4rrlllrrl : Reject b4rrlllrrl := split b4rrlllrrl 2 5 h4rrlllrrll h4rrlllrrlr
private def b4rrlllrrr : Region 4 := cutR b4rrlllrr 3 9
private def b4rrlllrrrl : Region 4 := cutL b4rrlllrrr 2 5
private def b4rrlllrrrll : Region 4 := cutL b4rrlllrrrl 4 49
private def c4rrlllrrrll : Cert 4 := (.split 0 45 (.split 3 12 .leaf (.split 4 32 (.split 0 29 (.split 3 13 .leaf (.split 4 27 .leaf (.split 0 25 (.split 3 14 .leaf .leaf) .leaf))) .leaf) (.split 0 29 (.split 3 13 (.split 4 39 .leaf (.split 0 25 (.split 4 44 .leaf (.split 0 23 (.split 4 46 (.split 0 22 (.split 4 45 .leaf .leaf) .leaf) (.split 0 22 .leaf .leaf)) .leaf)) .leaf)) (.split 4 39 (.split 0 25 (.split 3 14 .leaf .leaf) (.split 3 14 .leaf .leaf)) (.split 0 25 (.split 3 14 .leaf .leaf) (.split 3 14 .leaf .leaf)))) (.split 3 13 .leaf (.split 4 39 .leaf (.split 0 36 (.split 3 14 .leaf .leaf) .leaf)))))) .leaf)
theorem h4rrlllrrrll : Reject b4rrlllrrrll := sound c4rrlllrrrll (by decide +kernel)
private def b4rrlllrrrlr : Region 4 := cutR b4rrlllrrrl 4 49
private def b4rrlllrrrlrl : Region 4 := cutL b4rrlllrrrlr 0 45
private def b4rrlllrrrlrll : Region 4 := cutL b4rrlllrrrlrl 3 12
private def b4rrlllrrrlrlll : Region 4 := cutL b4rrlllrrrlrll 4 101
private def c4rrlllrrrlrlll : Cert 4 := (.split 0 29 (.split 3 10 .leaf (.split 4 67 (.split 0 25 (.split 3 11 .leaf .leaf) .leaf) (.split 0 25 (.split 3 11 .leaf .leaf) .leaf))) .leaf)
theorem h4rrlllrrrlrlll : Reject b4rrlllrrrlrlll := sound c4rrlllrrrlrlll (by decide +kernel)
private def b4rrlllrrrlrllr : Region 4 := cutR b4rrlllrrrlrll 4 101
private def b4rrlllrrrlrllrl : Region 4 := cutL b4rrlllrrrlrllr 0 29
private def b4rrlllrrrlrllrll : Region 4 := cutL b4rrlllrrrlrllrl 3 10
private def c4rrlllrrrlrllrll : Cert 4 := .leaf
theorem h4rrlllrrrlrllrll : Reject b4rrlllrrrlrllrll := sound c4rrlllrrrlrllrll (by decide +kernel)
private def b4rrlllrrrlrllrlr : Region 4 := cutR b4rrlllrrrlrllrl 3 10
private def b4rrlllrrrlrllrlrl : Region 4 := cutL b4rrlllrrrlrllrlr 4 205
private def c4rrlllrrrlrllrlrl : Cert 4 := (.split 0 25 (.split 3 11 (.split 4 136 .leaf (.split 0 23 (.split 4 164 (.split 0 22 (.split 4 149 (.split 4 142 .leaf (.split 4 145 .leaf (.split 4 147 .leaf .leaf))) .leaf) .leaf) (.split 0 22 .leaf (.split 4 182 .leaf (.split 4 193 .leaf (.split 4 199 (.split 4 196 (.split 4 194 .leaf (.split 4 195 .leaf .leaf)) .leaf) .leaf))))) .leaf)) .leaf) (.split 3 11 .leaf .leaf))
theorem h4rrlllrrrlrllrlrl : Reject b4rrlllrrrlrllrlrl := sound c4rrlllrrrlrllrlrl (by decide +kernel)
private def b4rrlllrrrlrllrlrr : Region 4 := cutR b4rrlllrrrlrllrlr 4 205
private def b4rrlllrrrlrllrlrrl : Region 4 := cutL b4rrlllrrrlrllrlrr 0 25
private def c4rrlllrrrlrllrlrrl : Cert 4 := (.split 3 11 (.split 4 413 (.split 0 23 .leaf (.split 4 275 .leaf (.split 0 24 .leaf .leaf))) (.split 0 23 .leaf (.split 4 829 (.split 0 24 .leaf (.split 4 552 (.split 4 473 (.split 4 441 .leaf (.split 4 456 (.split 4 448 (.split 4 444 .leaf (.split 4 446 (.split 4 445 .leaf .leaf) .leaf)) .leaf) .leaf)) .leaf) .leaf)) .leaf))) .leaf)
theorem h4rrlllrrrlrllrlrrl : Reject b4rrlllrrrlrllrlrrl := sound c4rrlllrrrlrllrlrrl (by decide +kernel)
private def b4rrlllrrrlrllrlrrr : Region 4 := cutR b4rrlllrrrlrllrlrr 0 25
private def c4rrlllrrrlrllrlrrr : Cert 4 := (.split 3 11 (.split 4 413 .leaf (.split 0 27 (.split 4 829 .leaf (.split 4 1661 (.split 0 26 (.split 4 1107 (.split 4 948 .leaf (.split 4 1021 .leaf (.split 4 1062 (.split 4 1041 (.split 4 1031 .leaf (.split 4 1036 (.split 4 1033 .leaf (.split 4 1034 .leaf .leaf)) .leaf)) .leaf) .leaf))) .leaf) .leaf) (.split 0 26 .leaf .leaf))) .leaf)) .leaf)
theorem h4rrlllrrrlrllrlrrr : Reject b4rrlllrrrlrllrlrrr := sound c4rrlllrrrlrllrlrrr (by decide +kernel)
theorem h4rrlllrrrlrllrlrr : Reject b4rrlllrrrlrllrlrr := split b4rrlllrrrlrllrlrr 0 25 h4rrlllrrrlrllrlrrl h4rrlllrrrlrllrlrrr
theorem h4rrlllrrrlrllrlr : Reject b4rrlllrrrlrllrlr := split b4rrlllrrrlrllrlr 4 205 h4rrlllrrrlrllrlrl h4rrlllrrrlrllrlrr
theorem h4rrlllrrrlrllrl : Reject b4rrlllrrrlrllrl := split b4rrlllrrrlrllrl 3 10 h4rrlllrrrlrllrll h4rrlllrrrlrllrlr
private def b4rrlllrrrlrllrr : Region 4 := cutR b4rrlllrrrlrllr 0 29
private def c4rrlllrrrlrllrr : Cert 4 := (.split 3 10 .leaf (.split 4 205 (.split 0 36 (.split 3 11 .leaf .leaf) .leaf) (.split 0 36 (.split 3 11 .leaf .leaf) .leaf)))
theorem h4rrlllrrrlrllrr : Reject b4rrlllrrrlrllrr := sound c4rrlllrrrlrllrr (by decide +kernel)
theorem h4rrlllrrrlrllr : Reject b4rrlllrrrlrllr := split b4rrlllrrrlrllr 0 29 h4rrlllrrrlrllrl h4rrlllrrrlrllrr
theorem h4rrlllrrrlrll : Reject b4rrlllrrrlrll := split b4rrlllrrrlrll 4 101 h4rrlllrrrlrlll h4rrlllrrrlrllr
private def b4rrlllrrrlrlr : Region 4 := cutR b4rrlllrrrlrl 3 12
private def b4rrlllrrrlrlrl : Region 4 := cutL b4rrlllrrrlrlr 4 101
private def b4rrlllrrrlrlrll : Region 4 := cutL b4rrlllrrrlrlrl 0 29
private def c4rrlllrrrlrlrll : Cert 4 := (.split 3 13 (.split 4 67 (.split 0 25 (.split 4 57 (.split 0 23 .leaf (.split 4 53 .leaf (.split 0 24 .leaf .leaf))) .leaf) (.split 4 57 .leaf (.split 0 27 (.split 4 62 .leaf (.split 0 26 .leaf .leaf)) .leaf))) (.split 0 25 .leaf (.split 4 81 (.split 0 27 .leaf (.split 4 73 (.split 4 70 .leaf (.split 0 28 (.split 4 71 .leaf (.split 4 72 .leaf .leaf)) .leaf)) (.split 4 77 (.split 0 28 .leaf .leaf) (.split 0 28 .leaf (.split 4 79 (.split 4 78 .leaf .leaf) .leaf))))) .leaf))) (.split 4 67 (.split 0 25 .leaf (.split 4 57 (.split 3 14 .leaf .leaf) .leaf)) .leaf))
theorem h4rrlllrrrlrlrll : Reject b4rrlllrrrlrlrll := sound c4rrlllrrrlrlrll (by decide +kernel)
private def b4rrlllrrrlrlrlr : Region 4 := cutR b4rrlllrrrlrlrl 0 29
private def c4rrlllrrrlrlrlr : Cert 4 := (.split 3 13 (.split 4 67 .leaf (.split 0 36 (.split 4 81 .leaf (.split 0 32 (.split 4 90 (.split 0 30 (.split 4 85 (.split 4 83 .leaf (.split 4 84 .leaf .leaf)) .leaf) .leaf) (.split 0 30 .leaf (.split 4 95 (.split 0 31 (.split 4 92 (.split 4 91 .leaf .leaf) .leaf) .leaf) (.split 0 31 .leaf (.split 4 98 .leaf .leaf))))) .leaf)) .leaf)) (.split 4 67 (.split 0 36 (.split 4 57 (.split 3 14 .leaf .leaf) (.split 3 14 .leaf .leaf)) (.split 4 57 (.split 3 14 .leaf .leaf) (.split 3 14 .leaf .leaf))) (.split 0 36 (.split 3 14 .leaf .leaf) (.split 3 14 .leaf .leaf))))
theorem h4rrlllrrrlrlrlr : Reject b4rrlllrrrlrlrlr := sound c4rrlllrrrlrlrlr (by decide +kernel)
theorem h4rrlllrrrlrlrl : Reject b4rrlllrrrlrlrl := split b4rrlllrrrlrlrl 0 29 h4rrlllrrrlrlrll h4rrlllrrrlrlrlr
private def b4rrlllrrrlrlrr : Region 4 := cutR b4rrlllrrrlrlr 4 101
private def b4rrlllrrrlrlrrl : Region 4 := cutL b4rrlllrrrlrlrr 0 29
private def c4rrlllrrrlrlrrl : Cert 4 := .leaf
theorem h4rrlllrrrlrlrrl : Reject b4rrlllrrrlrlrrl := sound c4rrlllrrrlrlrrl (by decide +kernel)
private def b4rrlllrrrlrlrrr : Region 4 := cutR b4rrlllrrrlrlrr 0 29
private def b4rrlllrrrlrlrrrl : Region 4 := cutL b4rrlllrrrlrlrrr 3 13
private def b4rrlllrrrlrlrrrll : Region 4 := cutL b4rrlllrrrlrlrrrl 4 205
private def b4rrlllrrrlrlrrrlll : Region 4 := cutL b4rrlllrrrlrlrrrll 0 36
private def c4rrlllrrrlrlrrrlll : Cert 4 := (.split 4 136 (.split 0 32 .leaf (.split 4 116 (.split 0 34 (.split 4 108 (.split 0 33 (.split 4 104 .leaf (.split 4 106 .leaf .leaf)) .leaf) (.split 0 33 .leaf (.split 4 112 .leaf (.split 4 114 .leaf (.split 4 115 .leaf .leaf))))) .leaf) (.split 0 34 .leaf (.split 4 125 .leaf (.split 0 35 .leaf .leaf))))) .leaf)
theorem h4rrlllrrrlrlrrrlll : Reject b4rrlllrrrlrlrrrlll := sound c4rrlllrrrlrlrrrlll (by decide +kernel)
private def b4rrlllrrrlrlrrrllr : Region 4 := cutR b4rrlllrrrlrlrrrll 0 36
private def c4rrlllrrrlrlrrrllr : Cert 4 := (.split 4 136 .leaf (.split 0 40 (.split 4 164 (.split 0 38 (.split 4 149 .leaf (.split 4 156 (.split 0 37 .leaf .leaf) (.split 0 37 .leaf (.split 4 160 .leaf (.split 4 162 .leaf (.split 4 163 .leaf .leaf)))))) .leaf) (.split 0 38 .leaf (.split 4 182 (.split 4 173 .leaf (.split 0 39 (.split 4 177 .leaf (.split 4 179 .leaf (.split 4 180 .leaf .leaf))) .leaf)) (.split 4 193 (.split 0 39 .leaf .leaf) (.split 0 39 .leaf (.split 4 199 (.split 4 196 .leaf (.split 4 197 .leaf (.split 4 198 .leaf .leaf))) .leaf)))))) .leaf))
theorem h4rrlllrrrlrlrrrllr : Reject b4rrlllrrrlrlrrrllr := sound c4rrlllrrrlrlrrrllr (by decide +kernel)
theorem h4rrlllrrrlrlrrrll : Reject b4rrlllrrrlrlrrrll := split b4rrlllrrrlrlrrrll 0 36 h4rrlllrrrlrlrrrlll h4rrlllrrrlrlrrrllr
private def b4rrlllrrrlrlrrrlr : Region 4 := cutR b4rrlllrrrlrlrrrl 4 205
private def b4rrlllrrrlrlrrrlrl : Region 4 := cutL b4rrlllrrrlrlrrrlr 0 36
private def c4rrlllrrrlrlrrrlrl : Cert 4 := .leaf
theorem h4rrlllrrrlrlrrrlrl : Reject b4rrlllrrrlrlrrrlrl := sound c4rrlllrrrlrlrrrlrl (by decide +kernel)
private def b4rrlllrrrlrlrrrlrr : Region 4 := cutR b4rrlllrrrlrlrrrlr 0 36
private def b4rrlllrrrlrlrrrlrrl : Region 4 := cutL b4rrlllrrrlrlrrrlrr 4 413
private def b4rrlllrrrlrlrrrlrrll : Region 4 := cutL b4rrlllrrrlrlrrrlrrl 0 40
private def c4rrlllrrrlrlrrrlrrll : Cert 4 := .leaf
theorem h4rrlllrrrlrlrrrlrrll : Reject b4rrlllrrrlrlrrrlrrll := sound c4rrlllrrrlrlrrrlrrll (by decide +kernel)
private def b4rrlllrrrlrlrrrlrrlr : Region 4 := cutR b4rrlllrrrlrlrrrlrrl 0 40
private def b4rrlllrrrlrlrrrlrrlrl : Region 4 := cutL b4rrlllrrrlrlrrrlrrlr 4 275
private def c4rrlllrrrlrlrrrlrrlrl : Cert 4 := (.split 0 42 (.split 4 235 (.split 4 219 .leaf (.split 0 41 (.split 4 227 (.split 4 223 (.split 4 221 (.split 4 220 .leaf .leaf) .leaf) .leaf) .leaf) .leaf)) (.split 4 254 (.split 0 41 .leaf (.split 4 244 .leaf (.split 4 249 (.split 4 246 .leaf .leaf) .leaf))) .leaf)) .leaf)
theorem h4rrlllrrrlrlrrrlrrlrl : Reject b4rrlllrrrlrlrrrlrrlrl := sound c4rrlllrrrlrlrrrlrrlrl (by decide +kernel)
private def b4rrlllrrrlrlrrrlrrlrr : Region 4 := cutR b4rrlllrrrlrlrrrlrrlr 4 275
private def c4rrlllrrrlrlrrrlrrlrr : Cert 4 := (.split 0 42 .leaf (.split 4 330 (.split 0 43 (.split 4 300 (.split 4 287 (.split 4 281 (.split 4 278 .leaf .leaf) .leaf) .leaf) .leaf) (.split 4 300 .leaf (.split 0 44 (.split 4 314 .leaf (.split 4 322 (.split 4 318 (.split 4 316 .leaf .leaf) .leaf) .leaf)) .leaf))) (.split 0 43 .leaf (.split 4 367 (.split 0 44 .leaf (.split 4 348 .leaf (.split 4 357 .leaf (.split 4 362 .leaf (.split 4 364 .leaf .leaf))))) .leaf))))
theorem h4rrlllrrrlrlrrrlrrlrr : Reject b4rrlllrrrlrlrrrlrrlrr := sound c4rrlllrrrlrlrrrlrrlrr (by decide +kernel)
theorem h4rrlllrrrlrlrrrlrrlr : Reject b4rrlllrrrlrlrrrlrrlr := split b4rrlllrrrlrlrrrlrrlr 4 275 h4rrlllrrrlrlrrrlrrlrl h4rrlllrrrlrlrrrlrrlrr
theorem h4rrlllrrrlrlrrrlrrl : Reject b4rrlllrrrlrlrrrlrrl := split b4rrlllrrrlrlrrrlrrl 0 40 h4rrlllrrrlrlrrrlrrll h4rrlllrrrlrlrrrlrrlr
private def b4rrlllrrrlrlrrrlrrr : Region 4 := cutR b4rrlllrrrlrlrrrlrr 4 413
private def c4rrlllrrrlrlrrrlrrr : Cert 4 := .leaf
theorem h4rrlllrrrlrlrrrlrrr : Reject b4rrlllrrrlrlrrrlrrr := sound c4rrlllrrrlrlrrrlrrr (by decide +kernel)
theorem h4rrlllrrrlrlrrrlrr : Reject b4rrlllrrrlrlrrrlrr := split b4rrlllrrrlrlrrrlrr 4 413 h4rrlllrrrlrlrrrlrrl h4rrlllrrrlrlrrrlrrr
theorem h4rrlllrrrlrlrrrlr : Reject b4rrlllrrrlrlrrrlr := split b4rrlllrrrlrlrrrlr 0 36 h4rrlllrrrlrlrrrlrl h4rrlllrrrlrlrrrlrr
theorem h4rrlllrrrlrlrrrl : Reject b4rrlllrrrlrlrrrl := split b4rrlllrrrlrlrrrl 4 205 h4rrlllrrrlrlrrrll h4rrlllrrrlrlrrrlr
private def b4rrlllrrrlrlrrrr : Region 4 := cutR b4rrlllrrrlrlrrr 3 13
private def c4rrlllrrrlrlrrrr : Cert 4 := (.split 4 205 (.split 0 36 .leaf (.split 3 14 .leaf .leaf)) .leaf)
theorem h4rrlllrrrlrlrrrr : Reject b4rrlllrrrlrlrrrr := sound c4rrlllrrrlrlrrrr (by decide +kernel)
theorem h4rrlllrrrlrlrrr : Reject b4rrlllrrrlrlrrr := split b4rrlllrrrlrlrrr 3 13 h4rrlllrrrlrlrrrl h4rrlllrrrlrlrrrr
theorem h4rrlllrrrlrlrr : Reject b4rrlllrrrlrlrr := split b4rrlllrrrlrlrr 0 29 h4rrlllrrrlrlrrl h4rrlllrrrlrlrrr
theorem h4rrlllrrrlrlr : Reject b4rrlllrrrlrlr := split b4rrlllrrrlrlr 4 101 h4rrlllrrrlrlrl h4rrlllrrrlrlrr
theorem h4rrlllrrrlrl : Reject b4rrlllrrrlrl := split b4rrlllrrrlrl 3 12 h4rrlllrrrlrll h4rrlllrrrlrlr
private def b4rrlllrrrlrr : Region 4 := cutR b4rrlllrrrlr 0 45
private def b4rrlllrrrlrrl : Region 4 := cutL b4rrlllrrrlrr 3 12
private def c4rrlllrrrlrrl : Cert 4 := .leaf
theorem h4rrlllrrrlrrl : Reject b4rrlllrrrlrrl := sound c4rrlllrrrlrrl (by decide +kernel)
private def b4rrlllrrrlrrr : Region 4 := cutR b4rrlllrrrlrr 3 12
private def b4rrlllrrrlrrrl : Region 4 := cutL b4rrlllrrrlrrr 4 101
private def c4rrlllrrrlrrrl : Cert 4 := (.split 0 93 (.split 3 13 .leaf (.split 4 67 .leaf (.split 0 61 (.split 3 14 .leaf .leaf) .leaf))) .leaf)
theorem h4rrlllrrrlrrrl : Reject b4rrlllrrrlrrrl := sound c4rrlllrrrlrrrl (by decide +kernel)
private def b4rrlllrrrlrrrr : Region 4 := cutR b4rrlllrrrlrrr 4 101
private def b4rrlllrrrlrrrrl : Region 4 := cutL b4rrlllrrrlrrrr 0 93
private def b4rrlllrrrlrrrrll : Region 4 := cutL b4rrlllrrrlrrrrl 3 13
private def b4rrlllrrrlrrrrlll : Region 4 := cutL b4rrlllrrrlrrrrll 4 205
private def c4rrlllrrrlrrrrlll : Cert 4 := .leaf
theorem h4rrlllrrrlrrrrlll : Reject b4rrlllrrrlrrrrlll := sound c4rrlllrrrlrrrrlll (by decide +kernel)
private def b4rrlllrrrlrrrrllr : Region 4 := cutR b4rrlllrrrlrrrrll 4 205
private def b4rrlllrrrlrrrrllrl : Region 4 := cutL b4rrlllrrrlrrrrllr 0 61
private def b4rrlllrrrlrrrrllrll : Region 4 := cutL b4rrlllrrrlrrrrllrl 4 413
private def c4rrlllrrrlrrrrllrll : Cert 4 := .leaf
theorem h4rrlllrrrlrrrrllrll : Reject b4rrlllrrrlrrrrllrll := sound c4rrlllrrrlrrrrllrll (by decide +kernel)
private def b4rrlllrrrlrrrrllrlr : Region 4 := cutR b4rrlllrrrlrrrrllrl 4 413
private def b4rrlllrrrlrrrrllrlrl : Region 4 := cutL b4rrlllrrrlrrrrllrlr 0 52
private def b4rrlllrrrlrrrrllrlrll : Region 4 := cutL b4rrlllrrrlrrrrllrlrl 4 829
private def b4rrlllrrrlrrrrllrlrlll : Region 4 := cutL b4rrlllrrrlrrrrllrlrll 0 48
private def c4rrlllrrrlrrrrllrlrlll : Cert 4 := (.split 4 552 (.split 0 46 (.split 4 473 (.split 4 441 (.split 4 427 (.split 4 420 .leaf (.split 4 423 .leaf (.split 4 425 .leaf (.split 4 426 .leaf .leaf)))) .leaf) .leaf) .leaf) (.split 4 473 .leaf (.split 0 47 (.split 4 510 (.split 4 491 .leaf (.split 4 500 .leaf (.split 4 505 .leaf (.split 4 507 .leaf (.split 4 508 .leaf .leaf))))) .leaf) .leaf))) (.split 0 46 .leaf (.split 4 663 (.split 0 47 .leaf (.split 4 603 .leaf (.split 4 632 (.split 4 617 .leaf (.split 4 624 .leaf .leaf)) .leaf))) .leaf)))
theorem h4rrlllrrrlrrrrllrlrlll : Reject b4rrlllrrrlrrrrllrlrlll := sound c4rrlllrrrlrrrrllrlrlll (by decide +kernel)
private def b4rrlllrrrlrrrrllrlrllr : Region 4 := cutR b4rrlllrrrlrrrrllrlrll 0 48
private def c4rrlllrrrlrrrrllrlrllr : Cert 4 := (.split 4 552 .leaf (.split 0 50 (.split 4 663 .leaf (.split 0 49 (.split 4 737 .leaf (.split 4 780 .leaf (.split 4 804 (.split 4 792 .leaf (.split 4 798 .leaf (.split 4 801 (.split 4 799 .leaf .leaf) .leaf))) .leaf))) .leaf)) .leaf))
theorem h4rrlllrrrlrrrrllrlrllr : Reject b4rrlllrrrlrrrrllrlrllr := sound c4rrlllrrrlrrrrllrlrllr (by decide +kernel)
theorem h4rrlllrrrlrrrrllrlrll : Reject b4rrlllrrrlrrrrllrlrll := split b4rrlllrrrlrrrrllrlrll 0 48 h4rrlllrrrlrrrrllrlrlll h4rrlllrrrlrrrrllrlrllr
private def b4rrlllrrrlrrrrllrlrlr : Region 4 := cutR b4rrlllrrrlrrrrllrlrl 4 829
private def b4rrlllrrrlrrrrllrlrlrl : Region 4 := cutL b4rrlllrrrlrrrrllrlrlr 0 48
private def c4rrlllrrrlrrrrllrlrlrl : Cert 4 := .leaf
theorem h4rrlllrrrlrrrrllrlrlrl : Reject b4rrlllrrrlrrrrllrlrlrl := sound c4rrlllrrrlrrrrllrlrlrl (by decide +kernel)
private def b4rrlllrrrlrrrrllrlrlrr : Region 4 := cutR b4rrlllrrrlrrrrllrlrlr 0 48
private def b4rrlllrrrlrrrrllrlrlrrl : Region 4 := cutL b4rrlllrrrlrrrrllrlrlrr 4 1661
private def c4rrlllrrrlrrrrllrlrlrrl : Cert 4 := (.split 0 50 (.split 4 1107 (.split 0 49 .leaf (.split 4 948 .leaf (.split 4 1021 .leaf (.split 4 1062 .leaf (.split 4 1084 .leaf (.split 4 1095 (.split 4 1089 .leaf (.split 4 1092 .leaf (.split 4 1093 .leaf .leaf))) .leaf)))))) .leaf) .leaf)
theorem h4rrlllrrrlrrrrllrlrlrrl : Reject b4rrlllrrrlrrrrllrlrlrrl := sound c4rrlllrrrlrrrrllrlrlrrl (by decide +kernel)
private def b4rrlllrrrlrrrrllrlrlrrr : Region 4 := cutR b4rrlllrrrlrrrrllrlrlrr 4 1661
private def c4rrlllrrrlrrrrllrlrlrrr : Cert 4 := (.split 0 50 .leaf (.split 4 3325 (.split 0 51 (.split 4 2216 (.split 4 1899 (.split 4 1772 (.split 4 1715 (.split 4 1688 .leaf (.split 4 1701 (.split 4 1694 (.split 4 1691 (.split 4 1689 .leaf .leaf) .leaf) .leaf) .leaf)) .leaf) .leaf) .leaf) .leaf) .leaf) (.split 0 51 .leaf (.split 4 6653 (.split 4 4435 (.split 4 3801 (.split 4 3547 .leaf (.split 4 3670 (.split 4 3607 (.split 4 3577 (.split 4 3562 (.split 4 3554 (.split 4 3550 .leaf (.split 4 3552 .leaf (.split 4 3553 .leaf .leaf))) .leaf) .leaf) .leaf) .leaf) .leaf)) .leaf) .leaf) .leaf))))
theorem h4rrlllrrrlrrrrllrlrlrrr : Reject b4rrlllrrrlrrrrllrlrlrrr := sound c4rrlllrrrlrrrrllrlrlrrr (by decide +kernel)
theorem h4rrlllrrrlrrrrllrlrlrr : Reject b4rrlllrrrlrrrrllrlrlrr := split b4rrlllrrrlrrrrllrlrlrr 4 1661 h4rrlllrrrlrrrrllrlrlrrl h4rrlllrrrlrrrrllrlrlrrr
theorem h4rrlllrrrlrrrrllrlrlr : Reject b4rrlllrrrlrrrrllrlrlr := split b4rrlllrrrlrrrrllrlrlr 0 48 h4rrlllrrrlrrrrllrlrlrl h4rrlllrrrlrrrrllrlrlrr
theorem h4rrlllrrrlrrrrllrlrl : Reject b4rrlllrrrlrrrrllrlrl := split b4rrlllrrrlrrrrllrlrl 4 829 h4rrlllrrrlrrrrllrlrll h4rrlllrrrlrrrrllrlrlr
private def b4rrlllrrrlrrrrllrlrr : Region 4 := cutR b4rrlllrrrlrrrrllrlr 0 52
private def c4rrlllrrrlrrrrllrlrr : Cert 4 := .leaf
theorem h4rrlllrrrlrrrrllrlrr : Reject b4rrlllrrrlrrrrllrlrr := sound c4rrlllrrrlrrrrllrlrr (by decide +kernel)
theorem h4rrlllrrrlrrrrllrlr : Reject b4rrlllrrrlrrrrllrlr := split b4rrlllrrrlrrrrllrlr 0 52 h4rrlllrrrlrrrrllrlrl h4rrlllrrrlrrrrllrlrr
theorem h4rrlllrrrlrrrrllrl : Reject b4rrlllrrrlrrrrllrl := split b4rrlllrrrlrrrrllrl 4 413 h4rrlllrrrlrrrrllrll h4rrlllrrrlrrrrllrlr
private def b4rrlllrrrlrrrrllrr : Region 4 := cutR b4rrlllrrrlrrrrllr 0 61
private def c4rrlllrrrlrrrrllrr : Cert 4 := .leaf
theorem h4rrlllrrrlrrrrllrr : Reject b4rrlllrrrlrrrrllrr := sound c4rrlllrrrlrrrrllrr (by decide +kernel)
theorem h4rrlllrrrlrrrrllr : Reject b4rrlllrrrlrrrrllr := split b4rrlllrrrlrrrrllr 0 61 h4rrlllrrrlrrrrllrl h4rrlllrrrlrrrrllrr
theorem h4rrlllrrrlrrrrll : Reject b4rrlllrrrlrrrrll := split b4rrlllrrrlrrrrll 4 205 h4rrlllrrrlrrrrlll h4rrlllrrrlrrrrllr
private def b4rrlllrrrlrrrrlr : Region 4 := cutR b4rrlllrrrlrrrrl 3 13
private def c4rrlllrrrlrrrrlr : Cert 4 := (.split 4 205 (.split 0 61 (.split 3 14 .leaf .leaf) (.split 3 14 .leaf .leaf)) (.split 0 61 (.split 3 14 .leaf .leaf) (.split 3 14 .leaf .leaf)))
theorem h4rrlllrrrlrrrrlr : Reject b4rrlllrrrlrrrrlr := sound c4rrlllrrrlrrrrlr (by decide +kernel)
theorem h4rrlllrrrlrrrrl : Reject b4rrlllrrrlrrrrl := split b4rrlllrrrlrrrrl 3 13 h4rrlllrrrlrrrrll h4rrlllrrrlrrrrlr
private def b4rrlllrrrlrrrrr : Region 4 := cutR b4rrlllrrrlrrrr 0 93
private def c4rrlllrrrlrrrrr : Cert 4 := (.split 3 13 .leaf (.split 4 205 .leaf (.split 0 189 (.split 3 14 .leaf .leaf) .leaf)))
theorem h4rrlllrrrlrrrrr : Reject b4rrlllrrrlrrrrr := sound c4rrlllrrrlrrrrr (by decide +kernel)
theorem h4rrlllrrrlrrrr : Reject b4rrlllrrrlrrrr := split b4rrlllrrrlrrrr 0 93 h4rrlllrrrlrrrrl h4rrlllrrrlrrrrr
theorem h4rrlllrrrlrrr : Reject b4rrlllrrrlrrr := split b4rrlllrrrlrrr 4 101 h4rrlllrrrlrrrl h4rrlllrrrlrrrr
theorem h4rrlllrrrlrr : Reject b4rrlllrrrlrr := split b4rrlllrrrlrr 3 12 h4rrlllrrrlrrl h4rrlllrrrlrrr
theorem h4rrlllrrrlr : Reject b4rrlllrrrlr := split b4rrlllrrrlr 0 45 h4rrlllrrrlrl h4rrlllrrrlrr
theorem h4rrlllrrrl : Reject b4rrlllrrrl := split b4rrlllrrrl 4 49 h4rrlllrrrll h4rrlllrrrlr
private def b4rrlllrrrr : Region 4 := cutR b4rrlllrrr 2 5
private def b4rrlllrrrrl : Region 4 := cutL b4rrlllrrrr 4 49
private def c4rrlllrrrrl : Cert 4 := (.split 0 45 (.split 3 12 (.split 2 6 .leaf .leaf) .leaf) (.split 3 12 (.split 2 6 .leaf (.split 4 32 (.split 3 10 .leaf (.split 0 93 .leaf (.split 4 27 (.split 0 189 (.split 3 11 (.split 4 25 (.split 0 125 .leaf (.split 0 151 .leaf (.split 4 24 .leaf .leaf))) .leaf) .leaf) (.split 3 11 (.split 4 25 (.split 0 381 (.split 0 253 (.split 4 24 .leaf .leaf) (.split 4 24 .leaf .leaf)) .leaf) (.split 0 381 .leaf (.split 0 765 .leaf (.split 4 26 .leaf .leaf)))) .leaf)) .leaf))) (.split 3 10 .leaf .leaf))) (.split 2 6 .leaf .leaf)))
theorem h4rrlllrrrrl : Reject b4rrlllrrrrl := sound c4rrlllrrrrl (by decide +kernel)
private def b4rrlllrrrrr : Region 4 := cutR b4rrlllrrrr 4 49
private def c4rrlllrrrrr : Cert 4 := (.split 0 45 (.split 3 12 (.split 2 6 .leaf .leaf) .leaf) (.split 3 12 (.split 2 6 .leaf .leaf) .leaf))
theorem h4rrlllrrrrr : Reject b4rrlllrrrrr := sound c4rrlllrrrrr (by decide +kernel)
theorem h4rrlllrrrr : Reject b4rrlllrrrr := split b4rrlllrrrr 4 49 h4rrlllrrrrl h4rrlllrrrrr
theorem h4rrlllrrr : Reject b4rrlllrrr := split b4rrlllrrr 2 5 h4rrlllrrrl h4rrlllrrrr
theorem h4rrlllrr : Reject b4rrlllrr := split b4rrlllrr 3 9 h4rrlllrrl h4rrlllrrr
theorem h4rrlllr : Reject b4rrlllr := split b4rrlllr 4 23 h4rrlllrl h4rrlllrr
theorem h4rrlll : Reject b4rrlll := split b4rrlll 0 21 h4rrllll h4rrlllr
private def b4rrllr : Region 4 := cutR b4rrll 2 7
private def b4rrllrl : Region 4 := cutL b4rrllr 4 23
private def b4rrllrll : Region 4 := cutL b4rrllrl 0 21
private def b4rrllrlll : Region 4 := cutL b4rrllrll 3 9
private def c4rrllrlll : Cert 4 := (.split 4 15 (.split 0 13 (.split 2 9 (.split 3 7 .leaf (.split 4 12 (.split 0 11 (.split 3 8 .leaf .leaf) (.split 3 8 .leaf .leaf)) .leaf)) .leaf) (.split 2 9 (.split 3 7 .leaf (.split 4 12 (.split 0 16 (.split 3 8 .leaf .leaf) (.split 3 8 .leaf .leaf)) (.split 0 16 (.split 3 8 .leaf .leaf) (.split 3 8 .leaf .leaf)))) .leaf)) (.split 0 13 (.split 2 9 (.split 3 7 .leaf .leaf) .leaf) (.split 2 9 (.split 3 7 .leaf (.split 4 18 (.split 0 16 .leaf (.split 3 8 .leaf .leaf)) .leaf)) .leaf)))
theorem h4rrllrlll : Reject b4rrllrlll := sound c4rrllrlll (by decide +kernel)
private def b4rrllrllr : Region 4 := cutR b4rrllrll 3 9
private def c4rrllrllr : Cert 4 := (.split 4 15 (.split 0 13 .leaf (.split 2 9 (.split 3 12 (.split 4 12 (.split 0 16 .leaf (.split 3 10 .leaf .leaf)) .leaf) .leaf) .leaf)) .leaf)
theorem h4rrllrllr : Reject b4rrllrllr := sound c4rrllrllr (by decide +kernel)
theorem h4rrllrll : Reject b4rrllrll := split b4rrllrll 3 9 h4rrllrlll h4rrllrllr
private def b4rrllrlr : Region 4 := cutR b4rrllrl 0 21
private def b4rrllrlrl : Region 4 := cutL b4rrllrlr 3 9
private def b4rrllrlrll : Region 4 := cutL b4rrllrlrl 4 15
private def c4rrllrlrll : Cert 4 := (.split 0 45 (.split 2 9 (.split 3 7 .leaf (.split 4 12 (.split 0 29 (.split 3 8 .leaf .leaf) .leaf) (.split 0 29 (.split 3 8 .leaf .leaf) (.split 3 8 .leaf .leaf)))) .leaf) (.split 2 9 (.split 3 7 .leaf (.split 4 12 .leaf (.split 0 93 (.split 3 8 .leaf .leaf) .leaf))) .leaf))
theorem h4rrllrlrll : Reject b4rrllrlrll := sound c4rrllrlrll (by decide +kernel)
private def b4rrllrlrlr : Region 4 := cutR b4rrllrlrl 4 15
private def c4rrllrlrlr : Cert 4 := (.split 0 45 (.split 2 9 (.split 3 7 .leaf (.split 4 18 (.split 0 29 (.split 3 8 .leaf .leaf) (.split 3 8 .leaf .leaf)) (.split 0 29 (.split 3 8 .leaf .leaf) (.split 3 8 .leaf .leaf)))) .leaf) (.split 2 9 (.split 3 7 .leaf (.split 4 18 (.split 0 93 (.split 3 8 .leaf .leaf) (.split 3 8 .leaf .leaf)) (.split 0 93 (.split 3 8 .leaf .leaf) (.split 3 8 .leaf .leaf)))) .leaf))
theorem h4rrllrlrlr : Reject b4rrllrlrlr := sound c4rrllrlrlr (by decide +kernel)
theorem h4rrllrlrl : Reject b4rrllrlrl := split b4rrllrlrl 4 15 h4rrllrlrll h4rrllrlrlr
private def b4rrllrlrr : Region 4 := cutR b4rrllrlr 3 9
private def b4rrllrlrrl : Region 4 := cutL b4rrllrlrr 4 15
private def b4rrllrlrrll : Region 4 := cutL b4rrllrlrrl 2 9
private def c4rrllrlrrll : Cert 4 := (.split 0 45 (.split 3 12 (.split 4 12 (.split 0 29 (.split 3 10 .leaf (.split 2 8 .leaf .leaf)) (.split 3 10 .leaf (.split 2 8 .leaf .leaf))) (.split 0 29 (.split 3 10 .leaf .leaf) (.split 3 10 .leaf (.split 2 8 .leaf .leaf)))) (.split 4 12 .leaf .leaf)) (.split 3 12 (.split 4 12 (.split 3 10 .leaf (.split 0 93 (.split 2 8 .leaf .leaf) (.split 2 8 .leaf .leaf))) (.split 3 10 .leaf (.split 0 93 (.split 2 8 .leaf .leaf) (.split 2 8 .leaf .leaf)))) (.split 4 12 .leaf (.split 0 93 .leaf (.split 2 8 .leaf .leaf)))))
theorem h4rrllrlrrll : Reject b4rrllrlrrll := sound c4rrllrlrrll (by decide +kernel)
private def b4rrllrlrrlr : Region 4 := cutR b4rrllrlrrl 2 9
private def c4rrllrlrrlr : Cert 4 := (.split 0 45 (.split 3 12 (.split 4 12 (.split 3 10 .leaf .leaf) .leaf) .leaf) (.split 3 12 (.split 4 12 (.split 3 10 .leaf (.split 0 93 .leaf (.split 2 10 .leaf .leaf))) (.split 3 10 .leaf .leaf)) .leaf))
theorem h4rrllrlrrlr : Reject b4rrllrlrrlr := sound c4rrllrlrrlr (by decide +kernel)
theorem h4rrllrlrrl : Reject b4rrllrlrrl := split b4rrllrlrrl 2 9 h4rrllrlrrll h4rrllrlrrlr
private def b4rrllrlrrr : Region 4 := cutR b4rrllrlrr 4 15
private def c4rrllrlrrr : Cert 4 := (.split 2 9 (.split 3 12 (.split 0 45 .leaf (.split 4 18 (.split 3 10 .leaf (.split 0 93 .leaf (.split 2 8 .leaf .leaf))) (.split 3 10 .leaf .leaf))) .leaf) .leaf)
theorem h4rrllrlrrr : Reject b4rrllrlrrr := sound c4rrllrlrrr (by decide +kernel)
theorem h4rrllrlrr : Reject b4rrllrlrr := split b4rrllrlrr 4 15 h4rrllrlrrl h4rrllrlrrr
theorem h4rrllrlr : Reject b4rrllrlr := split b4rrllrlr 3 9 h4rrllrlrl h4rrllrlrr
theorem h4rrllrl : Reject b4rrllrl := split b4rrllrl 0 21 h4rrllrll h4rrllrlr
private def b4rrllrr : Region 4 := cutR b4rrllr 4 23
private def c4rrllrr : Cert 4 := (.split 3 9 (.split 0 21 (.split 4 49 (.split 0 13 .leaf (.split 2 9 (.split 3 7 .leaf .leaf) .leaf)) .leaf) (.split 4 49 (.split 2 9 (.split 0 45 (.split 3 7 .leaf (.split 4 32 (.split 0 29 .leaf (.split 3 8 .leaf .leaf)) .leaf)) (.split 3 7 .leaf (.split 4 32 (.split 0 93 (.split 3 8 .leaf .leaf) (.split 3 8 .leaf .leaf)) (.split 0 93 (.split 3 8 .leaf .leaf) (.split 3 8 .leaf .leaf))))) .leaf) (.split 2 9 (.split 0 45 (.split 3 7 .leaf .leaf) (.split 3 7 .leaf .leaf)) .leaf))) .leaf)
theorem h4rrllrr : Reject b4rrllrr := sound c4rrllrr (by decide +kernel)
theorem h4rrllr : Reject b4rrllr := split b4rrllr 4 23 h4rrllrl h4rrllrr
theorem h4rrll : Reject b4rrll := split b4rrll 2 7 h4rrlll h4rrllr
private def b4rrlr : Region 4 := cutR b4rrl 3 15
private def b4rrlrl : Region 4 := cutL b4rrlr 2 7
private def b4rrlrll : Region 4 := cutL b4rrlrl 4 23
private def b4rrlrlll : Region 4 := cutL b4rrlrll 0 21
private def b4rrlrllll : Region 4 := cutL b4rrlrlll 2 5
private def b4rrlrlllll : Region 4 := cutL b4rrlrllll 3 33
private def b4rrlrllllll : Region 4 := cutL b4rrlrlllll 4 15
private def c4rrlrllllll : Cert 4 := .leaf
theorem h4rrlrllllll : Reject b4rrlrllllll := sound c4rrlrllllll (by decide +kernel)
private def b4rrlrlllllr : Region 4 := cutR b4rrlrlllll 4 15
private def b4rrlrlllllrl : Region 4 := cutL b4rrlrlllllr 0 13
private def c4rrlrlllllrl : Cert 4 := (.split 3 21 (.split 4 18 (.split 0 11 .leaf (.split 3 18 (.split 4 16 .leaf .leaf) .leaf)) .leaf) .leaf)
theorem h4rrlrlllllrl : Reject b4rrlrlllllrl := sound c4rrlrlllllrl (by decide +kernel)
private def b4rrlrlllllrr : Region 4 := cutR b4rrlrlllllr 0 13
private def b4rrlrlllllrrl : Region 4 := cutL b4rrlrlllllrr 3 21
private def b4rrlrlllllrrll : Region 4 := cutL b4rrlrlllllrrl 4 18
private def c4rrlrlllllrrll : Cert 4 := (.split 0 16 (.split 3 18 (.split 4 16 .leaf (.split 3 16 .leaf (.split 0 14 .leaf (.split 4 17 .leaf .leaf)))) .leaf) (.split 3 18 .leaf .leaf))
theorem h4rrlrlllllrrll : Reject b4rrlrlllllrrll := sound c4rrlrlllllrrll (by decide +kernel)
private def b4rrlrlllllrrlr : Region 4 := cutR b4rrlrlllllrrl 4 18
private def c4rrlrlllllrrlr : Cert 4 := (.split 0 16 (.split 3 18 (.split 4 20 (.split 3 16 .leaf .leaf) .leaf) .leaf) (.split 3 18 (.split 4 20 (.split 0 18 (.split 3 16 .leaf (.split 3 17 (.split 4 19 .leaf .leaf) .leaf)) .leaf) (.split 0 18 (.split 3 16 .leaf .leaf) (.split 3 16 .leaf (.split 4 21 .leaf (.split 0 19 .leaf (.split 3 17 (.split 4 22 .leaf (.split 0 20 .leaf .leaf)) .leaf)))))) (.split 4 20 (.split 0 18 .leaf (.split 3 19 (.split 0 19 (.split 4 19 .leaf .leaf) (.split 4 19 .leaf .leaf)) .leaf)) .leaf)))
theorem h4rrlrlllllrrlr : Reject b4rrlrlllllrrlr := sound c4rrlrlllllrrlr (by decide +kernel)
theorem h4rrlrlllllrrl : Reject b4rrlrlllllrrl := split b4rrlrlllllrrl 4 18 h4rrlrlllllrrll h4rrlrlllllrrlr
private def b4rrlrlllllrrr : Region 4 := cutR b4rrlrlllllrr 3 21
private def c4rrlrlllllrrr : Cert 4 := (.split 4 18 .leaf .leaf)
theorem h4rrlrlllllrrr : Reject b4rrlrlllllrrr := sound c4rrlrlllllrrr (by decide +kernel)
theorem h4rrlrlllllrr : Reject b4rrlrlllllrr := split b4rrlrlllllrr 3 21 h4rrlrlllllrrl h4rrlrlllllrrr
theorem h4rrlrlllllr : Reject b4rrlrlllllr := split b4rrlrlllllr 0 13 h4rrlrlllllrl h4rrlrlllllrr
theorem h4rrlrlllll : Reject b4rrlrlllll := split b4rrlrlllll 4 15 h4rrlrllllll h4rrlrlllllr
private def b4rrlrllllr : Region 4 := cutR b4rrlrllll 3 33
private def c4rrlrllllr : Cert 4 := .leaf
theorem h4rrlrllllr : Reject b4rrlrllllr := sound c4rrlrllllr (by decide +kernel)
theorem h4rrlrllll : Reject b4rrlrllll := split b4rrlrllll 3 33 h4rrlrlllll h4rrlrllllr
private def b4rrlrlllr : Region 4 := cutR b4rrlrlll 2 5
private def c4rrlrlllr : Cert 4 := (.split 3 33 (.split 4 15 .leaf .leaf) .leaf)
theorem h4rrlrlllr : Reject b4rrlrlllr := sound c4rrlrlllr (by decide +kernel)
theorem h4rrlrlll : Reject b4rrlrlll := split b4rrlrlll 2 5 h4rrlrllll h4rrlrlllr
private def b4rrlrllr : Region 4 := cutR b4rrlrll 0 21
private def b4rrlrllrl : Region 4 := cutL b4rrlrllr 2 5
private def b4rrlrllrll : Region 4 := cutL b4rrlrllrl 3 33
private def b4rrlrllrlll : Region 4 := cutL b4rrlrllrll 4 15
private def c4rrlrllrlll : Cert 4 := .leaf
theorem h4rrlrllrlll : Reject b4rrlrllrlll := sound c4rrlrllrlll (by decide +kernel)
private def b4rrlrllrllr : Region 4 := cutR b4rrlrllrll 4 15
private def b4rrlrllrllrl : Region 4 := cutL b4rrlrllrllr 0 45
private def b4rrlrllrllrll : Region 4 := cutL b4rrlrllrllrl 3 21
private def c4rrlrllrllrll : Cert 4 := (.split 4 18 .leaf (.split 0 29 (.split 3 18 (.split 4 20 .leaf (.split 0 25 (.split 3 16 .leaf (.split 0 23 (.split 4 21 .leaf (.split 3 17 .leaf .leaf)) .leaf)) .leaf)) (.split 4 20 (.split 0 25 (.split 3 19 .leaf .leaf) .leaf) (.split 0 25 (.split 3 19 (.split 0 23 (.split 4 21 .leaf (.split 4 22 .leaf .leaf)) (.split 4 21 .leaf (.split 4 22 .leaf (.split 0 24 .leaf .leaf)))) (.split 0 23 .leaf (.split 4 21 .leaf (.split 3 20 .leaf .leaf)))) (.split 3 19 .leaf (.split 4 21 .leaf (.split 0 27 (.split 3 20 .leaf .leaf) (.split 3 20 .leaf .leaf))))))) .leaf))
theorem h4rrlrllrllrll : Reject b4rrlrllrllrll := sound c4rrlrllrllrll (by decide +kernel)
private def b4rrlrllrllrlr : Region 4 := cutR b4rrlrllrllrl 3 21
private def c4rrlrllrllrlr : Cert 4 := (.split 4 18 .leaf (.split 0 29 (.split 3 26 (.split 4 20 .leaf (.split 0 25 .leaf (.split 3 23 (.split 4 21 .leaf (.split 0 27 .leaf (.split 4 22 .leaf .leaf))) .leaf))) .leaf) (.split 3 26 (.split 4 20 .leaf (.split 0 36 (.split 3 23 (.split 0 32 (.split 4 21 .leaf (.split 4 22 .leaf (.split 3 22 .leaf .leaf))) (.split 4 21 .leaf (.split 4 22 .leaf (.split 3 22 .leaf .leaf)))) .leaf) (.split 3 23 .leaf .leaf))) .leaf)))
theorem h4rrlrllrllrlr : Reject b4rrlrllrllrlr := sound c4rrlrllrllrlr (by decide +kernel)
theorem h4rrlrllrllrl : Reject b4rrlrllrllrl := split b4rrlrllrllrl 3 21 h4rrlrllrllrll h4rrlrllrllrlr
private def b4rrlrllrllrr : Region 4 := cutR b4rrlrllrllr 0 45
private def c4rrlrllrllrr : Cert 4 := (.split 3 21 .leaf (.split 4 18 .leaf (.split 0 93 (.split 3 26 .leaf .leaf) .leaf)))
theorem h4rrlrllrllrr : Reject b4rrlrllrllrr := sound c4rrlrllrllrr (by decide +kernel)
theorem h4rrlrllrllr : Reject b4rrlrllrllr := split b4rrlrllrllr 0 45 h4rrlrllrllrl h4rrlrllrllrr
theorem h4rrlrllrll : Reject b4rrlrllrll := split b4rrlrllrll 4 15 h4rrlrllrlll h4rrlrllrllr
private def b4rrlrllrlr : Region 4 := cutR b4rrlrllrl 3 33
private def c4rrlrllrlr : Cert 4 := .leaf
theorem h4rrlrllrlr : Reject b4rrlrllrlr := sound c4rrlrllrlr (by decide +kernel)
theorem h4rrlrllrl : Reject b4rrlrllrl := split b4rrlrllrl 3 33 h4rrlrllrll h4rrlrllrlr
private def b4rrlrllrr : Region 4 := cutR b4rrlrllr 2 5
private def c4rrlrllrr : Cert 4 := (.split 3 33 (.split 4 15 .leaf (.split 0 45 (.split 3 21 (.split 2 6 .leaf .leaf) .leaf) (.split 3 21 (.split 2 6 .leaf .leaf) (.split 2 6 .leaf .leaf)))) .leaf)
theorem h4rrlrllrr : Reject b4rrlrllrr := sound c4rrlrllrr (by decide +kernel)
theorem h4rrlrllr : Reject b4rrlrllr := split b4rrlrllr 2 5 h4rrlrllrl h4rrlrllrr
theorem h4rrlrll : Reject b4rrlrll := split b4rrlrll 0 21 h4rrlrlll h4rrlrllr
private def b4rrlrlr : Region 4 := cutR b4rrlrl 4 23
private def b4rrlrlrl : Region 4 := cutL b4rrlrlr 0 21
private def c4rrlrlrl : Cert 4 := (.split 2 5 (.split 3 33 (.split 4 49 (.split 0 13 .leaf (.split 3 21 (.split 4 32 (.split 0 16 .leaf (.split 3 18 (.split 4 27 (.split 0 18 .leaf (.split 3 16 .leaf .leaf)) .leaf) .leaf)) .leaf) .leaf)) .leaf) .leaf) .leaf)
theorem h4rrlrlrl : Reject b4rrlrlrl := sound c4rrlrlrl (by decide +kernel)
private def b4rrlrlrr : Region 4 := cutR b4rrlrlr 0 21
private def b4rrlrlrrl : Region 4 := cutL b4rrlrlrr 2 5
private def b4rrlrlrrll : Region 4 := cutL b4rrlrlrrl 3 33
private def b4rrlrlrrlll : Region 4 := cutL b4rrlrlrrll 4 49
private def b4rrlrlrrllll : Region 4 := cutL b4rrlrlrrlll 0 45
private def b4rrlrlrrlllll : Region 4 := cutL b4rrlrlrrllll 3 21
private def b4rrlrlrrllllll : Region 4 := cutL b4rrlrlrrlllll 4 32
private def b4rrlrlrrlllllll : Region 4 := cutL b4rrlrlrrllllll 0 29
private def b4rrlrlrrllllllll : Region 4 := cutL b4rrlrlrrlllllll 3 18
private def c4rrlrlrrllllllll : Cert 4 := (.split 4 27 (.split 0 25 (.split 3 16 .leaf (.split 4 25 (.split 0 23 (.split 3 17 (.split 4 24 .leaf .leaf) .leaf) (.split 3 17 .leaf .leaf)) (.split 0 23 .leaf (.split 3 17 (.split 4 26 .leaf .leaf) .leaf)))) (.split 3 16 .leaf (.split 4 25 .leaf (.split 3 17 .leaf .leaf)))) (.split 0 25 (.split 3 16 .leaf .leaf) (.split 3 16 .leaf (.split 4 29 (.split 3 17 (.split 0 27 (.split 4 28 .leaf (.split 0 26 .leaf .leaf)) .leaf) .leaf) (.split 3 17 (.split 0 27 .leaf (.split 4 30 .leaf (.split 4 31 (.split 0 28 .leaf .leaf) .leaf))) .leaf)))))
theorem h4rrlrlrrllllllll : Reject b4rrlrlrrllllllll := sound c4rrlrlrrllllllll (by decide +kernel)
private def b4rrlrlrrlllllllr : Region 4 := cutR b4rrlrlrrlllllll 3 18
private def c4rrlrlrrlllllllr : Cert 4 := (.split 4 27 (.split 0 25 .leaf (.split 3 19 (.split 4 25 (.split 0 27 (.split 4 24 .leaf .leaf) .leaf) (.split 0 27 .leaf (.split 4 26 .leaf .leaf))) (.split 4 25 (.split 0 27 .leaf (.split 3 20 .leaf .leaf)) .leaf))) .leaf)
theorem h4rrlrlrrlllllllr : Reject b4rrlrlrrlllllllr := sound c4rrlrlrrlllllllr (by decide +kernel)
theorem h4rrlrlrrlllllll : Reject b4rrlrlrrlllllll := split b4rrlrlrrlllllll 3 18 h4rrlrlrrllllllll h4rrlrlrrlllllllr
private def b4rrlrlrrllllllr : Region 4 := cutR b4rrlrlrrllllll 0 29
private def b4rrlrlrrllllllrl : Region 4 := cutL b4rrlrlrrllllllr 3 18
private def c4rrlrlrrllllllrl : Cert 4 := (.split 4 27 .leaf (.split 0 36 (.split 3 16 .leaf (.split 4 29 .leaf (.split 0 32 (.split 3 17 .leaf .leaf) (.split 3 17 .leaf .leaf)))) .leaf))
theorem h4rrlrlrrllllllrl : Reject b4rrlrlrrllllllrl := sound c4rrlrlrrllllllrl (by decide +kernel)
private def b4rrlrlrrllllllrr : Region 4 := cutR b4rrlrlrrllllllr 3 18
private def b4rrlrlrrllllllrrl : Region 4 := cutL b4rrlrlrrllllllrr 4 27
private def c4rrlrlrrllllllrrl : Cert 4 := (.split 0 36 (.split 3 19 (.split 4 25 .leaf (.split 0 32 (.split 0 30 (.split 4 26 .leaf .leaf) .leaf) .leaf)) (.split 4 25 (.split 0 32 (.split 3 20 .leaf .leaf) .leaf) (.split 0 32 (.split 3 20 .leaf .leaf) (.split 3 20 .leaf .leaf)))) (.split 3 19 .leaf (.split 4 25 .leaf (.split 0 40 (.split 3 20 .leaf .leaf) .leaf))))
theorem h4rrlrlrrllllllrrl : Reject b4rrlrlrrllllllrrl := sound c4rrlrlrrllllllrrl (by decide +kernel)
private def b4rrlrlrrllllllrrr : Region 4 := cutR b4rrlrlrrllllllrr 4 27
private def c4rrlrlrrllllllrrr : Cert 4 := (.split 0 36 (.split 3 19 (.split 4 29 (.split 0 32 (.split 0 30 .leaf (.split 4 28 .leaf .leaf)) (.split 0 34 (.split 4 28 .leaf (.split 0 33 .leaf .leaf)) .leaf)) (.split 0 32 .leaf (.split 4 30 .leaf .leaf))) (.split 4 29 (.split 0 32 .leaf (.split 3 20 .leaf .leaf)) .leaf)) (.split 3 19 (.split 4 29 .leaf (.split 0 40 (.split 4 30 .leaf (.split 0 38 (.split 4 31 .leaf .leaf) .leaf)) .leaf)) (.split 4 29 (.split 0 40 (.split 3 20 .leaf .leaf) (.split 3 20 .leaf .leaf)) (.split 0 40 (.split 3 20 .leaf .leaf) (.split 3 20 .leaf .leaf)))))
theorem h4rrlrlrrllllllrrr : Reject b4rrlrlrrllllllrrr := sound c4rrlrlrrllllllrrr (by decide +kernel)
theorem h4rrlrlrrllllllrr : Reject b4rrlrlrrllllllrr := split b4rrlrlrrllllllrr 4 27 h4rrlrlrrllllllrrl h4rrlrlrrllllllrrr
theorem h4rrlrlrrllllllr : Reject b4rrlrlrrllllllr := split b4rrlrlrrllllllr 3 18 h4rrlrlrrllllllrl h4rrlrlrrllllllrr
theorem h4rrlrlrrllllll : Reject b4rrlrlrrllllll := split b4rrlrlrrllllll 0 29 h4rrlrlrrlllllll h4rrlrlrrllllllr
private def b4rrlrlrrlllllr : Region 4 := cutR b4rrlrlrrlllll 4 32
private def b4rrlrlrrlllllrl : Region 4 := cutL b4rrlrlrrlllllr 0 29
private def c4rrlrlrrlllllrl : Cert 4 := (.split 3 18 (.split 4 39 (.split 0 25 .leaf (.split 3 16 .leaf .leaf)) .leaf) .leaf)
theorem h4rrlrlrrlllllrl : Reject b4rrlrlrrlllllrl := sound c4rrlrlrrlllllrl (by decide +kernel)
private def b4rrlrlrrlllllrr : Region 4 := cutR b4rrlrlrrlllllr 0 29
private def b4rrlrlrrlllllrrl : Region 4 := cutL b4rrlrlrrlllllrr 3 18
private def b4rrlrlrrlllllrrll : Region 4 := cutL b4rrlrlrrlllllrrl 4 39
private def c4rrlrlrrlllllrrll : Cert 4 := (.split 0 36 (.split 3 16 .leaf (.split 4 35 (.split 0 32 (.split 3 17 (.split 4 33 .leaf (.split 0 30 .leaf (.split 4 34 .leaf .leaf))) .leaf) (.split 3 17 .leaf .leaf)) (.split 0 32 .leaf (.split 3 17 (.split 4 37 (.split 0 34 (.split 4 36 .leaf .leaf) .leaf) .leaf) .leaf)))) (.split 3 16 .leaf (.split 4 35 (.split 0 40 (.split 3 17 .leaf .leaf) .leaf) (.split 0 40 (.split 3 17 (.split 4 37 .leaf (.split 0 38 (.split 4 38 .leaf .leaf) .leaf)) .leaf) (.split 3 17 .leaf .leaf)))))
theorem h4rrlrlrrlllllrrll : Reject b4rrlrlrrlllllrrll := sound c4rrlrlrrlllllrrll (by decide +kernel)
private def b4rrlrlrrlllllrrlr : Region 4 := cutR b4rrlrlrrlllllrrl 4 39
private def c4rrlrlrrlllllrrlr : Cert 4 := (.split 0 36 (.split 3 16 .leaf .leaf) (.split 3 16 .leaf (.split 4 44 (.split 0 40 (.split 3 17 (.split 4 41 (.split 0 38 .leaf (.split 4 40 .leaf (.split 0 39 .leaf .leaf))) .leaf) .leaf) (.split 3 17 (.split 4 41 .leaf (.split 0 42 (.split 4 42 .leaf (.split 4 43 (.split 0 41 .leaf .leaf) .leaf)) (.split 4 42 .leaf (.split 0 43 (.split 4 43 .leaf .leaf) .leaf)))) .leaf)) (.split 0 40 .leaf (.split 3 17 (.split 4 46 (.split 0 42 .leaf (.split 0 43 .leaf (.split 4 45 .leaf .leaf))) .leaf) .leaf)))))
theorem h4rrlrlrrlllllrrlr : Reject b4rrlrlrrlllllrrlr := sound c4rrlrlrrlllllrrlr (by decide +kernel)
theorem h4rrlrlrrlllllrrl : Reject b4rrlrlrrlllllrrl := split b4rrlrlrrlllllrrl 4 39 h4rrlrlrrlllllrrll h4rrlrlrrlllllrrlr
private def b4rrlrlrrlllllrrr : Region 4 := cutR b4rrlrlrrlllllrr 3 18
private def c4rrlrlrrlllllrrr : Cert 4 := (.split 4 39 (.split 0 36 .leaf (.split 3 19 (.split 4 35 (.split 0 40 .leaf (.split 4 33 .leaf (.split 0 42 .leaf (.split 4 34 .leaf .leaf)))) .leaf) .leaf)) .leaf)
theorem h4rrlrlrrlllllrrr : Reject b4rrlrlrrlllllrrr := sound c4rrlrlrrlllllrrr (by decide +kernel)
theorem h4rrlrlrrlllllrr : Reject b4rrlrlrrlllllrr := split b4rrlrlrrlllllrr 3 18 h4rrlrlrrlllllrrl h4rrlrlrrlllllrrr
theorem h4rrlrlrrlllllr : Reject b4rrlrlrrlllllr := split b4rrlrlrrlllllr 0 29 h4rrlrlrrlllllrl h4rrlrlrrlllllrr
theorem h4rrlrlrrlllll : Reject b4rrlrlrrlllll := split b4rrlrlrrlllll 4 32 h4rrlrlrrllllll h4rrlrlrrlllllr
private def b4rrlrlrrllllr : Region 4 := cutR b4rrlrlrrllll 3 21
private def c4rrlrlrrllllr : Cert 4 := (.split 4 32 (.split 0 29 .leaf (.split 3 26 (.split 4 27 (.split 0 36 (.split 3 23 (.split 4 25 (.split 0 32 .leaf (.split 3 22 .leaf .leaf)) .leaf) .leaf) (.split 3 23 (.split 4 25 (.split 0 40 (.split 3 22 .leaf (.split 4 24 .leaf .leaf)) .leaf) (.split 0 40 (.split 3 22 .leaf .leaf) (.split 3 22 .leaf (.split 0 42 .leaf (.split 4 26 .leaf .leaf))))) (.split 4 25 (.split 0 40 (.split 3 24 .leaf .leaf) (.split 3 24 .leaf .leaf)) .leaf))) (.split 0 36 .leaf (.split 3 23 (.split 4 29 (.split 0 40 .leaf (.split 3 22 .leaf .leaf)) .leaf) .leaf))) .leaf)) .leaf)
theorem h4rrlrlrrllllr : Reject b4rrlrlrrllllr := sound c4rrlrlrrllllr (by decide +kernel)
theorem h4rrlrlrrllll : Reject b4rrlrlrrllll := split b4rrlrlrrllll 3 21 h4rrlrlrrlllll h4rrlrlrrllllr
private def b4rrlrlrrlllr : Region 4 := cutR b4rrlrlrrlll 0 45
private def b4rrlrlrrlllrl : Region 4 := cutL b4rrlrlrrlllr 3 21
private def b4rrlrlrrlllrll : Region 4 := cutL b4rrlrlrrlllrl 4 32
private def c4rrlrlrrlllrll : Cert 4 := (.split 0 93 (.split 3 18 .leaf (.split 4 27 .leaf (.split 0 61 (.split 3 19 .leaf (.split 4 29 .leaf (.split 0 52 (.split 3 20 .leaf .leaf) .leaf))) .leaf))) .leaf)
theorem h4rrlrlrrlllrll : Reject b4rrlrlrrlllrll := sound c4rrlrlrrlllrll (by decide +kernel)
private def b4rrlrlrrlllrlr : Region 4 := cutR b4rrlrlrrlllrl 4 32
private def b4rrlrlrrlllrlrl : Region 4 := cutL b4rrlrlrrlllrlr 0 93
private def b4rrlrlrrlllrlrll : Region 4 := cutL b4rrlrlrrlllrlrl 3 18
private def c4rrlrlrrlllrlrll : Cert 4 := (.split 4 39 .leaf (.split 0 61 (.split 3 16 .leaf (.split 4 44 (.split 0 52 (.split 3 17 .leaf .leaf) .leaf) (.split 0 52 (.split 3 17 (.split 0 48 (.split 4 46 .leaf (.split 4 47 (.split 0 46 .leaf .leaf) (.split 0 46 .leaf (.split 4 48 .leaf .leaf)))) (.split 4 46 .leaf (.split 0 50 (.split 4 47 .leaf (.split 4 48 .leaf .leaf)) .leaf))) .leaf) (.split 3 17 .leaf .leaf)))) .leaf))
theorem h4rrlrlrrlllrlrll : Reject b4rrlrlrrlllrlrll := sound c4rrlrlrrlllrlrll (by decide +kernel)
private def b4rrlrlrrlllrlrlr : Region 4 := cutR b4rrlrlrrlllrlrl 3 18
private def b4rrlrlrrlllrlrlrl : Region 4 := cutL b4rrlrlrrlllrlrlr 4 39
private def c4rrlrlrrlllrlrlrl : Cert 4 := (.split 0 61 (.split 3 19 (.split 4 35 .leaf (.split 0 52 (.split 4 37 (.split 0 48 (.split 4 36 .leaf .leaf) .leaf) (.split 0 48 .leaf (.split 0 50 .leaf (.split 4 38 .leaf .leaf)))) .leaf)) (.split 4 35 (.split 0 52 (.split 3 20 .leaf .leaf) (.split 3 20 .leaf .leaf)) (.split 0 52 .leaf (.split 3 20 .leaf .leaf)))) (.split 3 19 .leaf (.split 4 35 .leaf (.split 0 74 (.split 3 20 .leaf .leaf) (.split 3 20 .leaf .leaf)))))
theorem h4rrlrlrrlllrlrlrl : Reject b4rrlrlrrlllrlrlrl := sound c4rrlrlrrlllrlrlrl (by decide +kernel)
private def b4rrlrlrrlllrlrlrr : Region 4 := cutR b4rrlrlrrlllrlrlr 4 39
private def b4rrlrlrrlllrlrlrrl : Region 4 := cutL b4rrlrlrrlllrlrlrr 0 61
private def c4rrlrlrrlllrlrlrrl : Cert 4 := (.split 3 19 (.split 4 44 (.split 0 52 .leaf (.split 4 41 (.split 0 56 (.split 0 54 .leaf (.split 4 40 .leaf .leaf)) (.split 0 58 (.split 4 40 .leaf (.split 0 57 .leaf .leaf)) .leaf)) (.split 0 56 .leaf (.split 4 42 .leaf .leaf)))) .leaf) .leaf)
theorem h4rrlrlrrlllrlrlrrl : Reject b4rrlrlrrlllrlrlrrl := sound c4rrlrlrrlllrlrlrrl (by decide +kernel)
private def b4rrlrlrrlllrlrlrrr : Region 4 := cutR b4rrlrlrrlllrlrlrr 0 61
private def c4rrlrlrrlllrlrlrrr : Cert 4 := (.split 3 19 (.split 4 44 (.split 0 74 (.split 4 41 .leaf (.split 0 67 (.split 4 42 .leaf (.split 0 64 (.split 4 43 (.split 0 62 .leaf .leaf) .leaf) (.split 4 43 .leaf .leaf))) .leaf)) .leaf) (.split 0 74 (.split 0 67 .leaf (.split 4 46 (.split 0 70 (.split 4 45 .leaf .leaf) (.split 4 45 .leaf .leaf)) .leaf)) (.split 0 83 (.split 4 46 .leaf (.split 0 78 (.split 4 47 .leaf (.split 4 48 .leaf .leaf)) (.split 4 47 .leaf (.split 0 80 (.split 4 48 .leaf .leaf) .leaf)))) .leaf))) (.split 4 44 (.split 0 74 (.split 3 20 .leaf .leaf) (.split 3 20 .leaf .leaf)) (.split 0 74 .leaf (.split 3 20 .leaf .leaf))))
theorem h4rrlrlrrlllrlrlrrr : Reject b4rrlrlrrlllrlrlrrr := sound c4rrlrlrrlllrlrlrrr (by decide +kernel)
theorem h4rrlrlrrlllrlrlrr : Reject b4rrlrlrrlllrlrlrr := split b4rrlrlrrlllrlrlrr 0 61 h4rrlrlrrlllrlrlrrl h4rrlrlrrlllrlrlrrr
theorem h4rrlrlrrlllrlrlr : Reject b4rrlrlrrlllrlrlr := split b4rrlrlrrlllrlrlr 4 39 h4rrlrlrrlllrlrlrl h4rrlrlrrlllrlrlrr
theorem h4rrlrlrrlllrlrl : Reject b4rrlrlrrlllrlrl := split b4rrlrlrrlllrlrl 3 18 h4rrlrlrrlllrlrll h4rrlrlrrlllrlrlr
private def b4rrlrlrrlllrlrr : Region 4 := cutR b4rrlrlrrlllrlr 0 93
private def c4rrlrlrrlllrlrr : Cert 4 := (.split 3 18 .leaf (.split 4 39 .leaf (.split 0 189 (.split 3 19 .leaf (.split 4 44 (.split 0 125 (.split 3 20 .leaf .leaf) .leaf) (.split 0 125 (.split 3 20 .leaf .leaf) (.split 3 20 .leaf .leaf)))) .leaf)))
theorem h4rrlrlrrlllrlrr : Reject b4rrlrlrrlllrlrr := sound c4rrlrlrrlllrlrr (by decide +kernel)
theorem h4rrlrlrrlllrlr : Reject b4rrlrlrrlllrlr := split b4rrlrlrrlllrlr 0 93 h4rrlrlrrlllrlrl h4rrlrlrrlllrlrr
theorem h4rrlrlrrlllrl : Reject b4rrlrlrrlllrl := split b4rrlrlrrlllrl 4 32 h4rrlrlrrlllrll h4rrlrlrrlllrlr
private def b4rrlrlrrlllrr : Region 4 := cutR b4rrlrlrrlllr 3 21
private def b4rrlrlrrlllrrl : Region 4 := cutL b4rrlrlrrlllrr 4 32
private def b4rrlrlrrlllrrll : Region 4 := cutL b4rrlrlrrlllrrl 0 93
private def b4rrlrlrrlllrrlll : Region 4 := cutL b4rrlrlrrlllrrll 3 26
private def b4rrlrlrrlllrrllll : Region 4 := cutL b4rrlrlrrlllrrlll 4 27
private def c4rrlrlrrlllrrllll : Cert 4 := (.split 0 61 (.split 3 23 (.split 4 25 .leaf (.split 0 52 (.split 3 22 .leaf (.split 0 48 (.split 4 26 .leaf .leaf) .leaf)) .leaf)) (.split 4 25 (.split 0 52 (.split 3 24 .leaf .leaf) .leaf) (.split 0 52 (.split 3 24 .leaf .leaf) (.split 3 24 .leaf (.split 0 56 (.split 3 25 .leaf .leaf) (.split 3 25 .leaf .leaf)))))) (.split 3 23 .leaf (.split 4 25 .leaf (.split 0 74 (.split 3 24 .leaf (.split 0 67 (.split 3 25 .leaf .leaf) .leaf)) .leaf))))
theorem h4rrlrlrrlllrrllll : Reject b4rrlrlrrlllrrllll := sound c4rrlrlrrlllrrllll (by decide +kernel)
private def b4rrlrlrrlllrrlllr : Region 4 := cutR b4rrlrlrrlllrrlll 4 27
private def b4rrlrlrrlllrrlllrl : Region 4 := cutL b4rrlrlrrlllrrlllr 0 61
private def c4rrlrlrrlllrrlllrl : Cert 4 := (.split 3 23 (.split 4 29 (.split 0 52 (.split 3 22 .leaf (.split 0 48 .leaf (.split 4 28 .leaf .leaf))) (.split 3 22 .leaf (.split 0 56 (.split 4 28 .leaf (.split 0 54 .leaf .leaf)) .leaf))) (.split 0 52 (.split 4 30 .leaf .leaf) (.split 4 30 .leaf (.split 3 22 .leaf .leaf)))) (.split 4 29 (.split 0 52 .leaf (.split 3 24 .leaf .leaf)) .leaf))
theorem h4rrlrlrrlllrrlllrl : Reject b4rrlrlrrlllrrlllrl := sound c4rrlrlrrlllrrlllrl (by decide +kernel)
private def b4rrlrlrrlllrrlllrr : Region 4 := cutR b4rrlrlrrlllrrlllr 0 61
private def c4rrlrlrrlllrrlllrr : Cert 4 := (.split 3 23 (.split 4 29 .leaf (.split 0 74 (.split 4 30 .leaf (.split 0 67 (.split 3 22 .leaf (.split 4 31 (.split 0 64 .leaf .leaf) .leaf)) (.split 3 22 .leaf (.split 4 31 .leaf .leaf)))) .leaf)) (.split 4 29 (.split 0 74 (.split 3 24 .leaf (.split 0 67 (.split 3 25 .leaf .leaf) (.split 3 25 .leaf .leaf))) (.split 3 24 .leaf (.split 0 83 (.split 3 25 .leaf .leaf) .leaf))) (.split 0 74 (.split 3 24 .leaf .leaf) (.split 3 24 .leaf (.split 4 30 .leaf (.split 0 83 .leaf (.split 3 25 .leaf .leaf)))))))
theorem h4rrlrlrrlllrrlllrr : Reject b4rrlrlrrlllrrlllrr := sound c4rrlrlrrlllrrlllrr (by decide +kernel)
theorem h4rrlrlrrlllrrlllr : Reject b4rrlrlrrlllrrlllr := split b4rrlrlrrlllrrlllr 0 61 h4rrlrlrrlllrrlllrl h4rrlrlrrlllrrlllrr
theorem h4rrlrlrrlllrrlll : Reject b4rrlrlrrlllrrlll := split b4rrlrlrrlllrrlll 4 27 h4rrlrlrrlllrrllll h4rrlrlrrlllrrlllr
private def b4rrlrlrrlllrrllr : Region 4 := cutR b4rrlrlrrlllrrll 3 26
private def c4rrlrlrrlllrrllr : Cert 4 := (.split 4 27 .leaf (.split 0 61 .leaf (.split 3 29 (.split 4 29 (.split 0 74 .leaf (.split 3 27 .leaf .leaf)) .leaf) .leaf)))
theorem h4rrlrlrrlllrrllr : Reject b4rrlrlrrlllrrllr := sound c4rrlrlrrlllrrllr (by decide +kernel)
theorem h4rrlrlrrlllrrll : Reject b4rrlrlrrlllrrll := split b4rrlrlrrlllrrll 3 26 h4rrlrlrrlllrrlll h4rrlrlrrlllrrllr
private def b4rrlrlrrlllrrlr : Region 4 := cutR b4rrlrlrrlllrrl 0 93
private def b4rrlrlrrlllrrlrl : Region 4 := cutL b4rrlrlrrlllrrlr 3 26
private def c4rrlrlrrlllrrlrl : Cert 4 := (.split 4 27 .leaf (.split 0 189 (.split 3 23 .leaf (.split 4 29 .leaf (.split 0 125 (.split 3 24 .leaf (.split 4 30 .leaf (.split 0 107 (.split 3 25 .leaf .leaf) (.split 3 25 .leaf .leaf)))) (.split 3 24 .leaf (.split 0 151 (.split 4 30 .leaf (.split 3 25 .leaf .leaf)) .leaf))))) .leaf))
theorem h4rrlrlrrlllrrlrl : Reject b4rrlrlrrlllrrlrl := sound c4rrlrlrrlllrrlrl (by decide +kernel)
private def b4rrlrlrrlllrrlrr : Region 4 := cutR b4rrlrlrrlllrrlr 3 26
private def b4rrlrlrrlllrrlrrl : Region 4 := cutL b4rrlrlrrlllrrlrr 4 27
private def c4rrlrlrrlllrrlrrl : Cert 4 := .leaf
theorem h4rrlrlrrlllrrlrrl : Reject b4rrlrlrrlllrrlrrl := sound c4rrlrlrrlllrrlrrl (by decide +kernel)
private def b4rrlrlrrlllrrlrrr : Region 4 := cutR b4rrlrlrrlllrrlrr 4 27
private def b4rrlrlrrlllrrlrrrl : Region 4 := cutL b4rrlrlrrlllrrlrrr 0 189
private def c4rrlrlrrlllrrlrrrl : Cert 4 := (.split 3 29 (.split 4 29 (.split 0 125 (.split 3 27 .leaf (.split 0 107 (.split 4 28 .leaf .leaf) (.split 4 28 .leaf (.split 3 28 .leaf .leaf)))) (.split 3 27 .leaf (.split 0 151 (.split 4 28 .leaf (.split 3 28 .leaf .leaf)) .leaf))) (.split 0 125 (.split 3 27 .leaf .leaf) (.split 3 27 .leaf (.split 4 30 .leaf (.split 0 151 .leaf (.split 3 28 .leaf .leaf)))))) (.split 4 29 .leaf .leaf))
theorem h4rrlrlrrlllrrlrrrl : Reject b4rrlrlrrlllrrlrrrl := sound c4rrlrlrrlllrrlrrrl (by decide +kernel)
private def b4rrlrlrrlllrrlrrrr : Region 4 := cutR b4rrlrlrrlllrrlrrr 0 189
private def b4rrlrlrrlllrrlrrrrl : Region 4 := cutL b4rrlrlrrlllrrlrrrr 3 29
private def c4rrlrlrrlllrrlrrrrl : Cert 4 := (.split 4 29 .leaf (.split 0 381 (.split 3 27 .leaf (.split 0 253 (.split 4 30 .leaf (.split 3 28 .leaf (.split 0 217 .leaf (.split 4 31 (.split 0 234 .leaf (.split 0 243 .leaf (.split 0 248 (.split 0 245 (.split 0 244 .leaf .leaf) .leaf) .leaf))) .leaf)))) (.split 4 30 .leaf (.split 3 28 .leaf (.split 0 304 (.split 4 31 .leaf .leaf) (.split 4 31 .leaf .leaf)))))) .leaf))
theorem h4rrlrlrrlllrrlrrrrl : Reject b4rrlrlrrlllrrlrrrrl := sound c4rrlrlrrlllrrlrrrrl (by decide +kernel)
private def b4rrlrlrrlllrrlrrrrr : Region 4 := cutR b4rrlrlrrlllrrlrrrr 3 29
private def c4rrlrlrrlllrrlrrrrr : Cert 4 := (.split 4 29 .leaf (.split 0 381 (.split 3 31 (.split 4 30 .leaf (.split 0 253 .leaf (.split 3 30 .leaf .leaf))) .leaf) (.split 3 31 (.split 4 30 .leaf (.split 0 765 (.split 3 30 .leaf .leaf) (.split 3 30 .leaf (.split 0 1533 (.split 4 31 .leaf .leaf) (.split 4 31 .leaf .leaf))))) .leaf)))
theorem h4rrlrlrrlllrrlrrrrr : Reject b4rrlrlrrlllrrlrrrrr := sound c4rrlrlrrlllrrlrrrrr (by decide +kernel)
theorem h4rrlrlrrlllrrlrrrr : Reject b4rrlrlrrlllrrlrrrr := split b4rrlrlrrlllrrlrrrr 3 29 h4rrlrlrrlllrrlrrrrl h4rrlrlrrlllrrlrrrrr
theorem h4rrlrlrrlllrrlrrr : Reject b4rrlrlrrlllrrlrrr := split b4rrlrlrrlllrrlrrr 0 189 h4rrlrlrrlllrrlrrrl h4rrlrlrrlllrrlrrrr
theorem h4rrlrlrrlllrrlrr : Reject b4rrlrlrrlllrrlrr := split b4rrlrlrrlllrrlrr 4 27 h4rrlrlrrlllrrlrrl h4rrlrlrrlllrrlrrr
theorem h4rrlrlrrlllrrlr : Reject b4rrlrlrrlllrrlr := split b4rrlrlrrlllrrlr 3 26 h4rrlrlrrlllrrlrl h4rrlrlrrlllrrlrr
theorem h4rrlrlrrlllrrl : Reject b4rrlrlrrlllrrl := split b4rrlrlrrlllrrl 0 93 h4rrlrlrrlllrrll h4rrlrlrrlllrrlr
private def b4rrlrlrrlllrrr : Region 4 := cutR b4rrlrlrrlllrr 4 32
private def b4rrlrlrrlllrrrl : Region 4 := cutL b4rrlrlrrlllrrr 0 93
private def c4rrlrlrrlllrrrl : Cert 4 := (.split 3 26 (.split 4 39 (.split 0 61 .leaf (.split 3 23 (.split 4 35 (.split 0 74 (.split 0 67 (.split 3 22 .leaf .leaf) (.split 3 22 .leaf .leaf)) (.split 0 83 (.split 3 22 .leaf (.split 4 33 .leaf .leaf)) (.split 3 22 .leaf (.split 4 33 .leaf (.split 0 88 (.split 4 34 .leaf .leaf) (.split 4 34 .leaf .leaf)))))) (.split 0 74 .leaf (.split 4 37 (.split 0 83 (.split 3 22 .leaf .leaf) (.split 3 22 .leaf .leaf)) .leaf))) (.split 4 35 (.split 0 74 .leaf (.split 3 24 .leaf .leaf)) .leaf))) .leaf) .leaf)
theorem h4rrlrlrrlllrrrl : Reject b4rrlrlrrlllrrrl := sound c4rrlrlrrlllrrrl (by decide +kernel)
private def b4rrlrlrrlllrrrr : Region 4 := cutR b4rrlrlrrlllrrr 0 93
private def b4rrlrlrrlllrrrrl : Region 4 := cutL b4rrlrlrrlllrrrr 3 26
private def b4rrlrlrrlllrrrrll : Region 4 := cutL b4rrlrlrrlllrrrrl 4 39
private def b4rrlrlrrlllrrrrlll : Region 4 := cutL b4rrlrlrrlllrrrrll 0 189
private def b4rrlrlrrlllrrrrllll : Region 4 := cutL b4rrlrlrrlllrrrrlll 3 23
private def c4rrlrlrrlllrrrrllll : Cert 4 := (.split 4 35 .leaf (.split 0 125 (.split 4 37 (.split 0 107 (.split 3 22 .leaf (.split 0 100 .leaf (.split 4 36 .leaf .leaf))) (.split 3 22 .leaf (.split 0 115 (.split 4 36 .leaf (.split 0 111 .leaf .leaf)) .leaf))) (.split 0 107 (.split 3 22 .leaf .leaf) (.split 3 22 .leaf (.split 0 115 .leaf (.split 4 38 .leaf .leaf))))) (.split 4 37 .leaf (.split 0 151 (.split 3 22 .leaf (.split 0 137 (.split 4 38 .leaf .leaf) (.split 4 38 .leaf .leaf))) .leaf))))
theorem h4rrlrlrrlllrrrrllll : Reject b4rrlrlrrlllrrrrllll := sound c4rrlrlrrlllrrrrllll (by decide +kernel)
private def b4rrlrlrrlllrrrrlllr : Region 4 := cutR b4rrlrlrrlllrrrrlll 3 23
private def c4rrlrlrrlllrrrrlllr : Cert 4 := (.split 4 35 (.split 0 125 (.split 3 24 .leaf (.split 0 107 .leaf (.split 4 33 .leaf .leaf))) (.split 3 24 .leaf (.split 0 151 (.split 4 33 .leaf (.split 3 25 .leaf .leaf)) (.split 4 33 .leaf (.split 3 25 .leaf .leaf))))) (.split 0 125 .leaf (.split 3 24 .leaf (.split 4 37 (.split 0 151 .leaf (.split 3 25 .leaf .leaf)) .leaf))))
theorem h4rrlrlrrlllrrrrlllr : Reject b4rrlrlrrlllrrrrlllr := sound c4rrlrlrrlllrrrrlllr (by decide +kernel)
theorem h4rrlrlrrlllrrrrlll : Reject b4rrlrlrrlllrrrrlll := split b4rrlrlrrlllrrrrlll 3 23 h4rrlrlrrlllrrrrllll h4rrlrlrrlllrrrrlllr
private def b4rrlrlrrlllrrrrllr : Region 4 := cutR b4rrlrlrrlllrrrrll 0 189
private def c4rrlrlrrlllrrrrllr : Cert 4 := (.split 3 23 .leaf (.split 4 35 (.split 0 381 (.split 3 24 .leaf (.split 0 253 (.split 4 33 .leaf (.split 3 25 .leaf .leaf)) .leaf)) .leaf) (.split 0 381 (.split 3 24 .leaf (.split 4 37 (.split 0 253 (.split 3 25 .leaf .leaf) (.split 3 25 .leaf .leaf)) (.split 0 253 .leaf (.split 3 25 .leaf .leaf)))) (.split 3 24 .leaf (.split 4 37 (.split 0 765 (.split 3 25 .leaf .leaf) .leaf) (.split 0 765 (.split 3 25 .leaf .leaf) (.split 3 25 .leaf .leaf)))))))
theorem h4rrlrlrrlllrrrrllr : Reject b4rrlrlrrlllrrrrllr := sound c4rrlrlrrlllrrrrllr (by decide +kernel)
theorem h4rrlrlrrlllrrrrll : Reject b4rrlrlrrlllrrrrll := split b4rrlrlrrlllrrrrll 0 189 h4rrlrlrrlllrrrrlll h4rrlrlrrlllrrrrllr
private def b4rrlrlrrlllrrrrlr : Region 4 := cutR b4rrlrlrrlllrrrrl 4 39
private def b4rrlrlrrlllrrrrlrl : Region 4 := cutL b4rrlrlrrlllrrrrlr 0 189
private def c4rrlrlrrlllrrrrlrl : Cert 4 := (.split 3 23 (.split 4 44 (.split 0 125 (.split 4 41 (.split 0 107 .leaf (.split 3 22 .leaf .leaf)) .leaf) (.split 4 41 (.split 0 151 (.split 3 22 .leaf .leaf) (.split 3 22 .leaf (.split 0 168 (.split 4 40 .leaf .leaf) (.split 4 40 .leaf (.split 0 178 (.split 0 173 .leaf (.split 0 175 .leaf (.split 0 176 .leaf (.split 0 177 .leaf .leaf)))) .leaf))))) (.split 0 151 (.split 3 22 .leaf .leaf) (.split 3 22 .leaf .leaf)))) (.split 0 125 .leaf (.split 0 151 .leaf (.split 3 22 .leaf .leaf)))) .leaf)
theorem h4rrlrlrrlllrrrrlrl : Reject b4rrlrlrrlllrrrrlrl := sound c4rrlrlrrlllrrrrlrl (by decide +kernel)
private def b4rrlrlrrlllrrrrlrr : Region 4 := cutR b4rrlrlrrlllrrrrlr 0 189
private def b4rrlrlrrlllrrrrlrrl : Region 4 := cutL b4rrlrlrrlllrrrrlrr 3 23
private def b4rrlrlrrlllrrrrlrrll : Region 4 := cutL b4rrlrlrrlllrrrrlrrl 4 44
private def c4rrlrlrrlllrrrrlrrll : Cert 4 := (.split 0 381 (.split 4 41 .leaf (.split 0 253 (.split 3 22 .leaf (.split 4 42 .leaf (.split 0 217 .leaf (.split 4 43 (.split 0 234 .leaf (.split 0 243 (.split 0 238 (.split 0 236 .leaf (.split 0 237 .leaf .leaf)) .leaf) .leaf)) .leaf)))) (.split 3 22 .leaf (.split 4 42 .leaf (.split 0 304 (.split 4 43 .leaf .leaf) .leaf))))) .leaf)
theorem h4rrlrlrrlllrrrrlrrll : Reject b4rrlrlrrlllrrrrlrrll := sound c4rrlrlrrlllrrrrlrrll (by decide +kernel)
private def b4rrlrlrrlllrrrrlrrlr : Region 4 := cutR b4rrlrlrrlllrrrrlrrl 4 44
private def c4rrlrlrrlllrrrrlrrlr : Cert 4 := (.split 0 381 (.split 0 253 (.split 3 22 .leaf .leaf) (.split 3 22 .leaf (.split 4 46 (.split 0 304 .leaf (.split 0 338 .leaf (.split 4 45 .leaf .leaf))) .leaf))) (.split 0 765 (.split 3 22 .leaf (.split 4 46 (.split 0 509 (.split 0 436 (.split 4 45 .leaf .leaf) .leaf) .leaf) (.split 0 509 .leaf (.split 4 47 (.split 0 612 (.split 0 556 .leaf (.split 0 583 (.split 0 569 .leaf (.split 0 576 (.split 0 572 .leaf (.split 0 574 .leaf .leaf)) .leaf)) .leaf)) .leaf) .leaf)))) (.split 3 22 .leaf (.split 4 46 .leaf (.split 0 1533 (.split 4 47 .leaf (.split 0 1021 (.split 4 48 .leaf .leaf) (.split 4 48 .leaf .leaf))) .leaf)))))
theorem h4rrlrlrrlllrrrrlrrlr : Reject b4rrlrlrrlllrrrrlrrlr := sound c4rrlrlrrlllrrrrlrrlr (by decide +kernel)
theorem h4rrlrlrrlllrrrrlrrl : Reject b4rrlrlrrlllrrrrlrrl := split b4rrlrlrrlllrrrrlrrl 4 44 h4rrlrlrrlllrrrrlrrll h4rrlrlrrlllrrrrlrrlr
private def b4rrlrlrrlllrrrrlrrr : Region 4 := cutR b4rrlrlrrlllrrrrlrr 3 23
private def c4rrlrlrrlllrrrrlrrr : Cert 4 := (.split 4 44 (.split 0 381 (.split 3 24 .leaf .leaf) (.split 3 24 .leaf (.split 4 41 (.split 0 765 (.split 3 25 .leaf .leaf) (.split 3 25 .leaf .leaf)) (.split 0 765 .leaf (.split 3 25 .leaf .leaf))))) (.split 0 381 .leaf (.split 3 24 .leaf .leaf)))
theorem h4rrlrlrrlllrrrrlrrr : Reject b4rrlrlrrlllrrrrlrrr := sound c4rrlrlrrlllrrrrlrrr (by decide +kernel)
theorem h4rrlrlrrlllrrrrlrr : Reject b4rrlrlrrlllrrrrlrr := split b4rrlrlrrlllrrrrlrr 3 23 h4rrlrlrrlllrrrrlrrl h4rrlrlrrlllrrrrlrrr
theorem h4rrlrlrrlllrrrrlr : Reject b4rrlrlrrlllrrrrlr := split b4rrlrlrrlllrrrrlr 0 189 h4rrlrlrrlllrrrrlrl h4rrlrlrrlllrrrrlrr
theorem h4rrlrlrrlllrrrrl : Reject b4rrlrlrrlllrrrrl := split b4rrlrlrrlllrrrrl 4 39 h4rrlrlrrlllrrrrll h4rrlrlrrlllrrrrlr
private def b4rrlrlrrlllrrrrr : Region 4 := cutR b4rrlrlrrlllrrrr 3 26
private def c4rrlrlrrlllrrrrr : Cert 4 := (.split 4 39 (.split 0 189 .leaf (.split 3 29 (.split 4 35 (.split 0 381 (.split 3 27 .leaf (.split 0 253 .leaf (.split 4 33 .leaf .leaf))) (.split 3 27 .leaf (.split 0 765 (.split 4 33 .leaf (.split 3 28 .leaf .leaf)) (.split 4 33 .leaf (.split 3 28 .leaf (.split 0 1533 .leaf (.split 4 34 .leaf .leaf))))))) (.split 0 381 .leaf (.split 3 27 .leaf (.split 4 37 (.split 0 765 .leaf (.split 3 28 .leaf .leaf)) .leaf)))) (.split 4 35 (.split 0 381 .leaf (.split 3 31 (.split 0 765 .leaf (.split 4 33 .leaf .leaf)) .leaf)) .leaf))) .leaf)
theorem h4rrlrlrrlllrrrrr : Reject b4rrlrlrrlllrrrrr := sound c4rrlrlrrlllrrrrr (by decide +kernel)
theorem h4rrlrlrrlllrrrr : Reject b4rrlrlrrlllrrrr := split b4rrlrlrrlllrrrr 3 26 h4rrlrlrrlllrrrrl h4rrlrlrrlllrrrrr
theorem h4rrlrlrrlllrrr : Reject b4rrlrlrrlllrrr := split b4rrlrlrrlllrrr 0 93 h4rrlrlrrlllrrrl h4rrlrlrrlllrrrr
theorem h4rrlrlrrlllrr : Reject b4rrlrlrrlllrr := split b4rrlrlrrlllrr 4 32 h4rrlrlrrlllrrl h4rrlrlrrlllrrr
theorem h4rrlrlrrlllr : Reject b4rrlrlrrlllr := split b4rrlrlrrlllr 3 21 h4rrlrlrrlllrl h4rrlrlrrlllrr
theorem h4rrlrlrrlll : Reject b4rrlrlrrlll := split b4rrlrlrrlll 0 45 h4rrlrlrrllll h4rrlrlrrlllr
private def b4rrlrlrrllr : Region 4 := cutR b4rrlrlrrll 4 49
private def b4rrlrlrrllrl : Region 4 := cutL b4rrlrlrrllr 0 45
private def c4rrlrlrrllrl : Cert 4 := (.split 3 21 (.split 4 101 (.split 0 29 .leaf (.split 3 18 (.split 4 67 (.split 0 36 .leaf (.split 3 16 .leaf .leaf)) .leaf) .leaf)) .leaf) .leaf)
theorem h4rrlrlrrllrl : Reject b4rrlrlrrllrl := sound c4rrlrlrrllrl (by decide +kernel)
private def b4rrlrlrrllrr : Region 4 := cutR b4rrlrlrrllr 0 45
private def b4rrlrlrrllrrl : Region 4 := cutL b4rrlrlrrllrr 3 21
private def b4rrlrlrrllrrll : Region 4 := cutL b4rrlrlrrllrrl 4 101
private def b4rrlrlrrllrrlll : Region 4 := cutL b4rrlrlrrllrrll 0 93
private def b4rrlrlrrllrrllll : Region 4 := cutL b4rrlrlrrllrrlll 3 18
private def b4rrlrlrrllrrlllll : Region 4 := cutL b4rrlrlrrllrrllll 4 67
private def b4rrlrlrrllrrllllll : Region 4 := cutL b4rrlrlrrllrrlllll 0 61
private def b4rrlrlrrllrrlllllll : Region 4 := cutL b4rrlrlrrllrrllllll 3 16
private def c4rrlrlrrllrrlllllll : Cert 4 := .leaf
theorem h4rrlrlrrllrrlllllll : Reject b4rrlrlrrllrrlllllll := sound c4rrlrlrrllrrlllllll (by decide +kernel)
private def b4rrlrlrrllrrllllllr : Region 4 := cutR b4rrlrlrrllrrllllll 3 16
private def c4rrlrlrrllrrllllllr : Cert 4 := (.split 4 57 (.split 0 52 (.split 3 17 (.split 4 53 (.split 0 48 .leaf (.split 4 51 (.split 0 50 .leaf (.split 4 50 .leaf .leaf)) .leaf)) .leaf) .leaf) (.split 3 17 (.split 4 53 (.split 0 56 (.split 4 51 .leaf (.split 0 54 (.split 4 52 .leaf .leaf) .leaf)) .leaf) (.split 0 56 (.split 4 55 (.split 0 54 .leaf (.split 4 54 .leaf .leaf)) .leaf) (.split 4 55 .leaf (.split 0 58 .leaf (.split 0 59 (.split 4 56 .leaf .leaf) .leaf))))) .leaf)) (.split 0 52 .leaf (.split 3 17 (.split 4 62 (.split 0 56 .leaf (.split 4 59 (.split 0 58 .leaf (.split 0 59 .leaf (.split 4 58 .leaf .leaf))) .leaf)) .leaf) .leaf)))
theorem h4rrlrlrrllrrllllllr : Reject b4rrlrlrrllrrllllllr := sound c4rrlrlrrllrrllllllr (by decide +kernel)
theorem h4rrlrlrrllrrllllll : Reject b4rrlrlrrllrrllllll := split b4rrlrlrrllrrllllll 3 16 h4rrlrlrrllrrlllllll h4rrlrlrrllrrllllllr
private def b4rrlrlrrllrrlllllr : Region 4 := cutR b4rrlrlrrllrrlllll 0 61
private def b4rrlrlrrllrrlllllrl : Region 4 := cutL b4rrlrlrrllrrlllllr 3 16
private def c4rrlrlrrllrrlllllrl : Cert 4 := .leaf
theorem h4rrlrlrrllrrlllllrl : Reject b4rrlrlrrllrrlllllrl := sound c4rrlrlrrllrrlllllrl (by decide +kernel)
private def b4rrlrlrrllrrlllllrr : Region 4 := cutR b4rrlrlrrllrrlllllr 3 16
private def c4rrlrlrrllrrlllllrr : Cert 4 := (.split 4 57 (.split 0 74 (.split 3 17 .leaf .leaf) (.split 3 17 .leaf .leaf)) (.split 0 74 (.split 3 17 (.split 4 62 (.split 0 67 (.split 4 59 (.split 0 64 (.split 0 62 (.split 4 58 .leaf .leaf) .leaf) .leaf) (.split 0 64 (.split 4 60 .leaf .leaf) (.split 4 60 .leaf (.split 0 65 (.split 4 61 .leaf .leaf) (.split 4 61 .leaf .leaf))))) .leaf) (.split 0 67 .leaf (.split 0 70 (.split 4 64 (.split 0 68 (.split 4 63 .leaf .leaf) (.split 4 63 .leaf .leaf)) .leaf) (.split 4 64 .leaf (.split 4 65 .leaf (.split 0 72 .leaf (.split 4 66 .leaf (.split 0 73 .leaf .leaf)))))))) .leaf) (.split 3 17 .leaf .leaf)))
theorem h4rrlrlrrllrrlllllrr : Reject b4rrlrlrrllrrlllllrr := sound c4rrlrlrrllrrlllllrr (by decide +kernel)
theorem h4rrlrlrrllrrlllllr : Reject b4rrlrlrrllrrlllllr := split b4rrlrlrrllrrlllllr 3 16 h4rrlrlrrllrrlllllrl h4rrlrlrrllrrlllllrr
theorem h4rrlrlrrllrrlllll : Reject b4rrlrlrrllrrlllll := split b4rrlrlrrllrrlllll 0 61 h4rrlrlrrllrrllllll h4rrlrlrrllrrlllllr
private def b4rrlrlrrllrrllllr : Region 4 := cutR b4rrlrlrrllrrllll 4 67
private def b4rrlrlrrllrrllllrl : Region 4 := cutL b4rrlrlrrllrrllllr 0 61
private def c4rrlrlrrllrrllllrl : Cert 4 := (.split 3 16 .leaf .leaf)
theorem h4rrlrlrrllrrllllrl : Reject b4rrlrlrrllrrllllrl := sound c4rrlrlrrllrrllllrl (by decide +kernel)
private def b4rrlrlrrllrrllllrr : Region 4 := cutR b4rrlrlrrllrrllllr 0 61
private def b4rrlrlrrllrrllllrrl : Region 4 := cutL b4rrlrlrrllrrllllrr 3 16
private def c4rrlrlrrllrrllllrrl : Cert 4 := .leaf
theorem h4rrlrlrrllrrllllrrl : Reject b4rrlrlrrllrrllllrrl := sound c4rrlrlrrllrrllllrrl (by decide +kernel)
private def b4rrlrlrrllrrllllrrr : Region 4 := cutR b4rrlrlrrllrrllllrr 3 16
private def b4rrlrlrrllrrllllrrrl : Region 4 := cutL b4rrlrlrrllrrllllrrr 4 81
private def b4rrlrlrrllrrllllrrrll : Region 4 := cutL b4rrlrlrrllrrllllrrrl 0 74
private def c4rrlrlrrllrrllllrrrll : Cert 4 := .leaf
theorem h4rrlrlrrllrrllllrrrll : Reject b4rrlrlrrllrrllllrrrll := sound c4rrlrlrrllrrllllrrrll (by decide +kernel)
private def b4rrlrlrrllrrllllrrrlr : Region 4 := cutR b4rrlrlrrllrrllllrrrl 0 74
private def b4rrlrlrrllrrllllrrrlrl : Region 4 := cutL b4rrlrlrrllrrllllrrrlr 3 17
private def b4rrlrlrrllrrllllrrrlrll : Region 4 := cutL b4rrlrlrrllrrllllrrrlrl 4 73
private def c4rrlrlrrllrrllllrrrlrll : Cert 4 := (.split 0 83 (.split 0 78 (.split 4 70 (.split 4 68 .leaf (.split 0 76 .leaf (.split 4 69 .leaf .leaf))) .leaf) (.split 4 70 .leaf (.split 0 80 (.split 4 71 (.split 0 79 .leaf .leaf) .leaf) (.split 4 71 .leaf (.split 0 81 .leaf (.split 4 72 .leaf (.split 0 82 .leaf .leaf))))))) .leaf)
theorem h4rrlrlrrllrrllllrrrlrll : Reject b4rrlrlrrllrrllllrrrlrll := sound c4rrlrlrrllrrllllrrrlrll (by decide +kernel)
private def b4rrlrlrrllrrllllrrrlrlr : Region 4 := cutR b4rrlrlrrllrrllllrrrlrl 4 73
private def c4rrlrlrrllrrllllrrrlrlr : Cert 4 := (.split 0 83 .leaf (.split 4 77 (.split 0 88 (.split 4 75 (.split 0 85 (.split 4 74 .leaf .leaf) (.split 0 86 (.split 4 74 .leaf .leaf) .leaf)) (.split 0 85 .leaf (.split 0 86 .leaf (.split 4 76 .leaf .leaf)))) (.split 4 75 .leaf (.split 0 90 (.split 4 76 .leaf .leaf) .leaf))) (.split 0 88 .leaf (.split 4 79 (.split 0 90 .leaf (.split 0 91 .leaf (.split 4 78 .leaf (.split 0 92 .leaf .leaf)))) .leaf))))
theorem h4rrlrlrrllrrllllrrrlrlr : Reject b4rrlrlrrllrrllllrrrlrlr := sound c4rrlrlrrllrrllllrrrlrlr (by decide +kernel)
theorem h4rrlrlrrllrrllllrrrlrl : Reject b4rrlrlrrllrrllllrrrlrl := split b4rrlrlrrllrrllllrrrlrl 4 73 h4rrlrlrrllrrllllrrrlrll h4rrlrlrrllrrllllrrrlrlr
private def b4rrlrlrrllrrllllrrrlrr : Region 4 := cutR b4rrlrlrrllrrllllrrrlr 3 17
private def c4rrlrlrrllrrllllrrrlrr : Cert 4 := .leaf
theorem h4rrlrlrrllrrllllrrrlrr : Reject b4rrlrlrrllrrllllrrrlrr := sound c4rrlrlrrllrrllllrrrlrr (by decide +kernel)
theorem h4rrlrlrrllrrllllrrrlr : Reject b4rrlrlrrllrrllllrrrlr := split b4rrlrlrrllrrllllrrrlr 3 17 h4rrlrlrrllrrllllrrrlrl h4rrlrlrrllrrllllrrrlrr
theorem h4rrlrlrrllrrllllrrrl : Reject b4rrlrlrrllrrllllrrrl := split b4rrlrlrrllrrllllrrrl 0 74 h4rrlrlrrllrrllllrrrll h4rrlrlrrllrrllllrrrlr
private def b4rrlrlrrllrrllllrrrr : Region 4 := cutR b4rrlrlrrllrrllllrrr 4 81
private def c4rrlrlrrllrrllllrrrr : Cert 4 := .leaf
theorem h4rrlrlrrllrrllllrrrr : Reject b4rrlrlrrllrrllllrrrr := sound c4rrlrlrrllrrllllrrrr (by decide +kernel)
theorem h4rrlrlrrllrrllllrrr : Reject b4rrlrlrrllrrllllrrr := split b4rrlrlrrllrrllllrrr 4 81 h4rrlrlrrllrrllllrrrl h4rrlrlrrllrrllllrrrr
theorem h4rrlrlrrllrrllllrr : Reject b4rrlrlrrllrrllllrr := split b4rrlrlrrllrrllllrr 3 16 h4rrlrlrrllrrllllrrl h4rrlrlrrllrrllllrrr
theorem h4rrlrlrrllrrllllr : Reject b4rrlrlrrllrrllllr := split b4rrlrlrrllrrllllr 0 61 h4rrlrlrrllrrllllrl h4rrlrlrrllrrllllrr
theorem h4rrlrlrrllrrllll : Reject b4rrlrlrrllrrllll := split b4rrlrlrrllrrllll 4 67 h4rrlrlrrllrrlllll h4rrlrlrrllrrllllr
private def b4rrlrlrrllrrlllr : Region 4 := cutR b4rrlrlrrllrrlll 3 18
private def c4rrlrlrrllrrlllr : Cert 4 := (.split 4 67 (.split 0 61 .leaf (.split 3 19 (.split 4 57 (.split 0 74 .leaf (.split 4 53 (.split 0 83 .leaf (.split 4 51 (.split 0 88 (.split 0 85 (.split 4 50 .leaf .leaf) (.split 4 50 .leaf .leaf)) .leaf) (.split 0 88 .leaf (.split 0 90 .leaf (.split 4 52 .leaf .leaf))))) .leaf)) .leaf) .leaf)) .leaf)
theorem h4rrlrlrrllrrlllr : Reject b4rrlrlrrllrrlllr := sound c4rrlrlrrllrrlllr (by decide +kernel)
theorem h4rrlrlrrllrrlll : Reject b4rrlrlrrllrrlll := split b4rrlrlrrllrrlll 3 18 h4rrlrlrrllrrllll h4rrlrlrrllrrlllr
private def b4rrlrlrrllrrllr : Region 4 := cutR b4rrlrlrrllrrll 0 93
private def b4rrlrlrrllrrllrl : Region 4 := cutL b4rrlrlrrllrrllr 3 18
private def b4rrlrlrrllrrllrll : Region 4 := cutL b4rrlrlrrllrrllrl 4 67
private def c4rrlrlrrllrrllrll : Cert 4 := (.split 0 189 (.split 3 16 .leaf (.split 4 57 .leaf (.split 0 125 (.split 3 17 .leaf .leaf) .leaf))) .leaf)
theorem h4rrlrlrrllrrllrll : Reject b4rrlrlrrllrrllrll := sound c4rrlrlrrllrrllrll (by decide +kernel)
private def b4rrlrlrrllrrllrlr : Region 4 := cutR b4rrlrlrrllrrllrl 4 67
private def b4rrlrlrrllrrllrlrl : Region 4 := cutL b4rrlrlrrllrrllrlr 0 189
private def b4rrlrlrrllrrllrlrll : Region 4 := cutL b4rrlrlrrllrrllrlrl 3 16
private def c4rrlrlrrllrrllrlrll : Cert 4 := .leaf
theorem h4rrlrlrrllrrllrlrll : Reject b4rrlrlrrllrrllrlrll := sound c4rrlrlrrllrrllrlrll (by decide +kernel)
private def b4rrlrlrrllrrllrlrlr : Region 4 := cutR b4rrlrlrrllrrllrlrl 3 16
private def b4rrlrlrrllrrllrlrlrl : Region 4 := cutL b4rrlrlrrllrrllrlrlr 4 81
private def c4rrlrlrrllrrllrlrlrl : Cert 4 := (.split 0 125 (.split 3 17 (.split 4 73 .leaf (.split 0 107 (.split 4 77 .leaf (.split 0 100 (.split 0 96 (.split 4 79 .leaf (.split 0 94 .leaf (.split 4 80 .leaf .leaf))) .leaf) .leaf)) .leaf)) .leaf) (.split 3 17 .leaf .leaf))
theorem h4rrlrlrrllrrllrlrlrl : Reject b4rrlrlrrllrrllrlrlrl := sound c4rrlrlrrllrrllrlrlrl (by decide +kernel)
private def b4rrlrlrrllrrllrlrlrr : Region 4 := cutR b4rrlrlrrllrrllrlrlr 4 81
private def b4rrlrlrrllrrllrlrlrrl : Region 4 := cutL b4rrlrlrrllrrllrlrlrr 0 125
private def b4rrlrlrrllrrllrlrlrrll : Region 4 := cutL b4rrlrlrrllrrllrlrlrrl 3 17
private def b4rrlrlrrllrrllrlrlrrlll : Region 4 := cutL b4rrlrlrrllrrllrlrlrrll 4 90
private def c4rrlrlrrllrrllrlrlrrlll : Cert 4 := (.split 0 107 (.split 4 85 (.split 0 100 (.split 0 96 .leaf (.split 4 83 (.split 0 98 (.split 4 82 .leaf .leaf) (.split 4 82 .leaf (.split 0 99 .leaf .leaf))) .leaf)) (.split 0 103 (.split 4 83 .leaf (.split 0 101 .leaf (.split 4 84 .leaf .leaf))) .leaf)) (.split 0 100 .leaf (.split 4 87 (.split 0 103 .leaf (.split 0 105 .leaf (.split 4 86 .leaf .leaf))) .leaf))) (.split 4 85 .leaf (.split 0 115 (.split 4 87 .leaf (.split 0 111 (.split 4 88 .leaf (.split 0 109 .leaf (.split 4 89 (.split 0 110 .leaf .leaf) .leaf))) (.split 4 88 .leaf (.split 0 113 (.split 4 89 .leaf .leaf) .leaf)))) .leaf)))
theorem h4rrlrlrrllrrllrlrlrrlll : Reject b4rrlrlrrllrrllrlrlrrlll := sound c4rrlrlrrllrrllrlrlrrlll (by decide +kernel)
private def b4rrlrlrrllrrllrlrlrrllr : Region 4 := cutR b4rrlrlrrllrrllrlrlrrll 4 90
private def c4rrlrlrrllrrllrlrlrrllr : Cert 4 := (.split 0 107 .leaf (.split 4 95 (.split 0 115 (.split 4 92 (.split 0 111 .leaf (.split 0 113 .leaf (.split 4 91 .leaf .leaf))) .leaf) (.split 0 120 (.split 4 92 (.split 0 117 (.split 4 91 .leaf .leaf) .leaf) (.split 0 117 .leaf (.split 4 93 .leaf .leaf))) (.split 4 92 .leaf (.split 4 93 .leaf (.split 0 122 (.split 4 94 .leaf .leaf) .leaf))))) (.split 0 115 .leaf (.split 4 98 (.split 0 120 .leaf (.split 0 122 .leaf (.split 4 96 .leaf .leaf))) .leaf))))
theorem h4rrlrlrrllrrllrlrlrrllr : Reject b4rrlrlrrllrrllrlrlrrllr := sound c4rrlrlrrllrrllrlrlrrllr (by decide +kernel)
theorem h4rrlrlrrllrrllrlrlrrll : Reject b4rrlrlrrllrrllrlrlrrll := split b4rrlrlrrllrrllrlrlrrll 4 90 h4rrlrlrrllrrllrlrlrrlll h4rrlrlrrllrrllrlrlrrllr
private def b4rrlrlrrllrrllrlrlrrlr : Region 4 := cutR b4rrlrlrrllrrllrlrlrrl 3 17
private def c4rrlrlrrllrrllrlrlrrlr : Cert 4 := .leaf
theorem h4rrlrlrrllrrllrlrlrrlr : Reject b4rrlrlrrllrrllrlrlrrlr := sound c4rrlrlrrllrrllrlrlrrlr (by decide +kernel)
theorem h4rrlrlrrllrrllrlrlrrl : Reject b4rrlrlrrllrrllrlrlrrl := split b4rrlrlrrllrrllrlrlrrl 3 17 h4rrlrlrrllrrllrlrlrrll h4rrlrlrrllrrllrlrlrrlr
private def b4rrlrlrrllrrllrlrlrrr : Region 4 := cutR b4rrlrlrrllrrllrlrlrr 0 125
private def c4rrlrlrrllrrllrlrlrrr : Cert 4 := (.split 3 17 (.split 4 90 .leaf (.split 0 151 (.split 4 95 .leaf (.split 0 137 (.split 4 98 (.split 0 131 (.split 0 128 (.split 4 96 .leaf (.split 4 97 (.split 0 126 .leaf .leaf) .leaf)) .leaf) .leaf) (.split 0 131 .leaf (.split 0 134 (.split 4 99 .leaf (.split 4 100 .leaf .leaf)) (.split 4 99 .leaf (.split 4 100 .leaf (.split 0 135 .leaf .leaf)))))) .leaf)) .leaf)) .leaf)
theorem h4rrlrlrrllrrllrlrlrrr : Reject b4rrlrlrrllrrllrlrlrrr := sound c4rrlrlrrllrrllrlrlrrr (by decide +kernel)
theorem h4rrlrlrrllrrllrlrlrr : Reject b4rrlrlrrllrrllrlrlrr := split b4rrlrlrrllrrllrlrlrr 0 125 h4rrlrlrrllrrllrlrlrrl h4rrlrlrrllrrllrlrlrrr
theorem h4rrlrlrrllrrllrlrlr : Reject b4rrlrlrrllrrllrlrlr := split b4rrlrlrrllrrllrlrlr 4 81 h4rrlrlrrllrrllrlrlrl h4rrlrlrrllrrllrlrlrr
theorem h4rrlrlrrllrrllrlrl : Reject b4rrlrlrrllrrllrlrl := split b4rrlrlrrllrrllrlrl 3 16 h4rrlrlrrllrrllrlrll h4rrlrlrrllrrllrlrlr
private def b4rrlrlrrllrrllrlrr : Region 4 := cutR b4rrlrlrrllrrllrlr 0 189
private def c4rrlrlrrllrrllrlrr : Cert 4 := (.split 3 16 .leaf (.split 4 81 .leaf (.split 0 381 (.split 3 17 .leaf .leaf) .leaf)))
theorem h4rrlrlrrllrrllrlrr : Reject b4rrlrlrrllrrllrlrr := sound c4rrlrlrrllrrllrlrr (by decide +kernel)
theorem h4rrlrlrrllrrllrlr : Reject b4rrlrlrrllrrllrlr := split b4rrlrlrrllrrllrlr 0 189 h4rrlrlrrllrrllrlrl h4rrlrlrrllrrllrlrr
theorem h4rrlrlrrllrrllrl : Reject b4rrlrlrrllrrllrl := split b4rrlrlrrllrrllrl 4 67 h4rrlrlrrllrrllrll h4rrlrlrrllrrllrlr
private def b4rrlrlrrllrrllrr : Region 4 := cutR b4rrlrlrrllrrllr 3 18
private def b4rrlrlrrllrrllrrl : Region 4 := cutL b4rrlrlrrllrrllrr 4 67
private def b4rrlrlrrllrrllrrll : Region 4 := cutL b4rrlrlrrllrrllrrl 0 189
private def b4rrlrlrrllrrllrrlll : Region 4 := cutL b4rrlrlrrllrrllrrll 3 19
private def b4rrlrlrrllrrllrrllll : Region 4 := cutL b4rrlrlrrllrrllrrlll 4 57
private def c4rrlrlrrllrrllrrllll : Cert 4 := (.split 0 125 (.split 4 53 (.split 0 107 (.split 4 51 .leaf (.split 0 100 (.split 0 96 (.split 4 52 .leaf (.split 0 94 .leaf (.split 0 95 .leaf .leaf))) .leaf) .leaf)) .leaf) (.split 0 107 (.split 0 100 (.split 4 55 (.split 0 96 .leaf (.split 4 54 .leaf .leaf)) .leaf) (.split 4 55 (.split 0 103 (.split 4 54 .leaf .leaf) .leaf) .leaf)) (.split 0 115 (.split 4 55 .leaf (.split 0 111 (.split 4 56 .leaf .leaf) (.split 4 56 .leaf .leaf))) .leaf))) .leaf)
theorem h4rrlrlrrllrrllrrllll : Reject b4rrlrlrrllrrllrrllll := sound c4rrlrlrrllrrllrrllll (by decide +kernel)
private def b4rrlrlrrllrrllrrlllr : Region 4 := cutR b4rrlrlrrllrrllrrlll 4 57
private def b4rrlrlrrllrrllrrlllrl : Region 4 := cutL b4rrlrlrrllrrllrrlllr 0 125
private def c4rrlrlrrllrrllrrlllrl : Cert 4 := (.split 4 62 (.split 0 107 .leaf (.split 4 59 (.split 0 115 .leaf (.split 0 120 (.split 4 58 .leaf .leaf) (.split 4 58 .leaf (.split 0 122 .leaf (.split 0 123 .leaf .leaf))))) .leaf)) .leaf)
theorem h4rrlrlrrllrrllrrlllrl : Reject b4rrlrlrrllrrllrrlllrl := sound c4rrlrlrrllrrllrrlllrl (by decide +kernel)
private def b4rrlrlrrllrrllrrlllrr : Region 4 := cutR b4rrlrlrrllrrllrrlllr 0 125
private def c4rrlrlrrllrrllrrlllrr : Cert 4 := (.split 4 62 (.split 0 151 (.split 4 59 .leaf (.split 0 137 (.split 4 60 .leaf (.split 0 131 .leaf (.split 4 61 (.split 0 134 .leaf .leaf) .leaf))) (.split 4 60 .leaf (.split 0 144 (.split 4 61 .leaf .leaf) .leaf)))) .leaf) (.split 0 151 (.split 0 137 .leaf (.split 4 64 (.split 0 144 .leaf (.split 4 63 .leaf .leaf)) .leaf)) (.split 0 168 (.split 4 64 (.split 0 159 (.split 4 63 .leaf .leaf) .leaf) (.split 0 159 .leaf (.split 4 65 .leaf .leaf))) (.split 4 64 .leaf (.split 0 178 (.split 4 65 .leaf (.split 0 173 (.split 4 66 .leaf .leaf) (.split 4 66 .leaf .leaf))) .leaf)))))
theorem h4rrlrlrrllrrllrrlllrr : Reject b4rrlrlrrllrrllrrlllrr := sound c4rrlrlrrllrrllrrlllrr (by decide +kernel)
theorem h4rrlrlrrllrrllrrlllr : Reject b4rrlrlrrllrrllrrlllr := split b4rrlrlrrllrrllrrlllr 0 125 h4rrlrlrrllrrllrrlllrl h4rrlrlrrllrrllrrlllrr
theorem h4rrlrlrrllrrllrrlll : Reject b4rrlrlrrllrrllrrlll := split b4rrlrlrrllrrllrrlll 4 57 h4rrlrlrrllrrllrrllll h4rrlrlrrllrrllrrlllr
private def b4rrlrlrrllrrllrrllr : Region 4 := cutR b4rrlrlrrllrrllrrll 3 19
private def c4rrlrlrrllrrllrrllr : Cert 4 := (.split 4 57 (.split 0 125 (.split 3 20 .leaf .leaf) (.split 3 20 .leaf .leaf)) .leaf)
theorem h4rrlrlrrllrrllrrllr : Reject b4rrlrlrrllrrllrrllr := sound c4rrlrlrrllrrllrrllr (by decide +kernel)
theorem h4rrlrlrrllrrllrrll : Reject b4rrlrlrrllrrllrrll := split b4rrlrlrrllrrllrrll 3 19 h4rrlrlrrllrrllrrlll h4rrlrlrrllrrllrrllr
private def b4rrlrlrrllrrllrrlr : Region 4 := cutR b4rrlrlrrllrrllrrl 0 189
private def c4rrlrlrrllrrllrrlr : Cert 4 := (.split 3 19 .leaf (.split 4 57 (.split 0 381 (.split 3 20 .leaf .leaf) (.split 3 20 .leaf .leaf)) (.split 0 381 (.split 3 20 .leaf .leaf) (.split 3 20 .leaf .leaf))))
theorem h4rrlrlrrllrrllrrlr : Reject b4rrlrlrrllrrllrrlr := sound c4rrlrlrrllrrllrrlr (by decide +kernel)
theorem h4rrlrlrrllrrllrrl : Reject b4rrlrlrrllrrllrrl := split b4rrlrlrrllrrllrrl 0 189 h4rrlrlrrllrrllrrll h4rrlrlrrllrrllrrlr
private def b4rrlrlrrllrrllrrr : Region 4 := cutR b4rrlrlrrllrrllrr 4 67
private def b4rrlrlrrllrrllrrrl : Region 4 := cutL b4rrlrlrrllrrllrrr 0 189
private def c4rrlrlrrllrrllrrrl : Cert 4 := (.split 3 19 (.split 4 81 (.split 0 125 .leaf (.split 4 73 (.split 0 151 .leaf (.split 0 168 .leaf (.split 4 70 (.split 0 178 .leaf (.split 4 68 .leaf .leaf)) .leaf))) .leaf)) .leaf) .leaf)
theorem h4rrlrlrrllrrllrrrl : Reject b4rrlrlrrllrrllrrrl := sound c4rrlrlrrllrrllrrrl (by decide +kernel)
private def b4rrlrlrrllrrllrrrr : Region 4 := cutR b4rrlrlrrllrrllrrr 0 189
private def b4rrlrlrrllrrllrrrrl : Region 4 := cutL b4rrlrlrrllrrllrrrr 3 19
private def b4rrlrlrrllrrllrrrrll : Region 4 := cutL b4rrlrlrrllrrllrrrrl 4 81
private def b4rrlrlrrllrrllrrrrlll : Region 4 := cutL b4rrlrlrrllrrllrrrrll 0 381
private def b4rrlrlrrllrrllrrrrllll : Region 4 := cutL b4rrlrlrrllrrllrrrrlll 4 73
private def c4rrlrlrrllrrllrrrrllll : Cert 4 := (.split 0 253 (.split 0 217 (.split 4 70 (.split 0 202 (.split 4 68 .leaf (.split 0 195 .leaf (.split 4 69 .leaf .leaf))) (.split 4 68 .leaf (.split 0 209 (.split 4 69 .leaf .leaf) .leaf))) .leaf) (.split 4 70 .leaf (.split 0 234 (.split 4 71 (.split 0 225 (.split 0 221 (.split 0 219 .leaf .leaf) .leaf) .leaf) (.split 0 225 .leaf (.split 4 72 .leaf .leaf))) (.split 4 71 .leaf (.split 0 243 (.split 4 72 .leaf .leaf) (.split 4 72 .leaf (.split 0 248 (.split 0 245 .leaf .leaf) .leaf))))))) .leaf)
theorem h4rrlrlrrllrrllrrrrllll : Reject b4rrlrlrrllrrllrrrrllll := sound c4rrlrlrrllrrllrrrrllll (by decide +kernel)
private def b4rrlrlrrllrrllrrrrlllr : Region 4 := cutR b4rrlrlrrllrrllrrrrlll 4 73
private def c4rrlrlrrllrrllrrrrlllr : Cert 4 := (.split 0 253 .leaf (.split 4 77 (.split 0 304 (.split 4 75 (.split 0 276 (.split 0 264 (.split 4 74 .leaf .leaf) (.split 4 74 .leaf .leaf)) .leaf) (.split 0 276 .leaf (.split 0 289 .leaf (.split 4 76 .leaf .leaf)))) (.split 4 75 .leaf (.split 0 338 (.split 0 320 (.split 4 76 .leaf .leaf) .leaf) .leaf))) (.split 0 304 .leaf (.split 0 338 (.split 4 79 (.split 0 320 .leaf (.split 4 78 .leaf .leaf)) .leaf) (.split 4 79 (.split 0 358 (.split 4 78 .leaf .leaf) (.split 4 78 .leaf (.split 0 369 (.split 0 363 (.split 0 360 .leaf .leaf) .leaf) .leaf))) .leaf)))))
theorem h4rrlrlrrllrrllrrrrlllr : Reject b4rrlrlrrllrrllrrrrlllr := sound c4rrlrlrrllrrllrrrrlllr (by decide +kernel)
theorem h4rrlrlrrllrrllrrrrlll : Reject b4rrlrlrrllrrllrrrrlll := split b4rrlrlrrllrrllrrrrlll 4 73 h4rrlrlrrllrrllrrrrllll h4rrlrlrrllrrllrrrrlllr
private def b4rrlrlrrllrrllrrrrllr : Region 4 := cutR b4rrlrlrrllrrllrrrrll 0 381
private def c4rrlrlrrllrrllrrrrllr : Cert 4 := (.split 4 73 .leaf (.split 0 765 (.split 4 77 .leaf (.split 0 509 (.split 0 436 (.split 4 79 .leaf (.split 0 407 (.split 4 80 .leaf .leaf) (.split 4 80 .leaf .leaf))) .leaf) .leaf)) .leaf))
theorem h4rrlrlrrllrrllrrrrllr : Reject b4rrlrlrrllrrllrrrrllr := sound c4rrlrlrrllrrllrrrrllr (by decide +kernel)
theorem h4rrlrlrrllrrllrrrrll : Reject b4rrlrlrrllrrllrrrrll := split b4rrlrlrrllrrllrrrrll 0 381 h4rrlrlrrllrrllrrrrlll h4rrlrlrrllrrllrrrrllr
private def b4rrlrlrrllrrllrrrrlr : Region 4 := cutR b4rrlrlrrllrrllrrrrl 4 81
private def b4rrlrlrrllrrllrrrrlrl : Region 4 := cutL b4rrlrlrrllrrllrrrrlr 0 381
private def c4rrlrlrrllrrllrrrrlrl : Cert 4 := .leaf
theorem h4rrlrlrrllrrllrrrrlrl : Reject b4rrlrlrrllrrllrrrrlrl := sound c4rrlrlrrllrrllrrrrlrl (by decide +kernel)
private def b4rrlrlrrllrrllrrrrlrr : Region 4 := cutR b4rrlrlrrllrrllrrrrlr 0 381
private def b4rrlrlrrllrrllrrrrlrrl : Region 4 := cutL b4rrlrlrrllrrllrrrrlrr 4 90
private def b4rrlrlrrllrrllrrrrlrrll : Region 4 := cutL b4rrlrlrrllrrllrrrrlrrl 0 765
private def c4rrlrlrrllrrllrrrrlrrll : Cert 4 := (.split 4 85 (.split 0 509 (.split 0 436 .leaf (.split 4 83 (.split 0 470 (.split 4 82 .leaf .leaf) (.split 4 82 .leaf (.split 0 489 .leaf (.split 0 499 (.split 0 494 .leaf .leaf) .leaf)))) .leaf)) (.split 0 612 (.split 4 83 .leaf (.split 0 556 (.split 4 84 .leaf .leaf) (.split 4 84 .leaf .leaf))) .leaf)) (.split 0 509 .leaf (.split 0 612 .leaf (.split 4 87 (.split 0 680 (.split 4 86 .leaf .leaf) (.split 4 86 .leaf .leaf)) .leaf))))
theorem h4rrlrlrrllrrllrrrrlrrll : Reject b4rrlrlrrllrrllrrrrlrrll := sound c4rrlrlrrllrrllrrrrlrrll (by decide +kernel)
private def b4rrlrlrrllrrllrrrrlrrlr : Region 4 := cutR b4rrlrlrrllrrllrrrrlrrl 0 765
private def c4rrlrlrrllrrllrrrrlrrlr : Cert 4 := (.split 4 85 .leaf (.split 0 1533 (.split 0 1021 (.split 4 87 .leaf (.split 0 875 (.split 4 88 .leaf .leaf) (.split 4 88 .leaf (.split 0 942 .leaf (.split 4 89 (.split 0 980 .leaf (.split 0 1000 (.split 0 990 (.split 0 985 .leaf .leaf) .leaf) .leaf)) .leaf))))) (.split 4 87 .leaf (.split 0 1226 (.split 4 88 .leaf (.split 0 1114 (.split 4 89 .leaf .leaf) (.split 4 89 .leaf .leaf))) .leaf))) .leaf))
theorem h4rrlrlrrllrrllrrrrlrrlr : Reject b4rrlrlrrllrrllrrrrlrrlr := sound c4rrlrlrrllrrllrrrrlrrlr (by decide +kernel)
theorem h4rrlrlrrllrrllrrrrlrrl : Reject b4rrlrlrrllrrllrrrrlrrl := split b4rrlrlrrllrrllrrrrlrrl 0 765 h4rrlrlrrllrrllrrrrlrrll h4rrlrlrrllrrllrrrrlrrlr
private def b4rrlrlrrllrrllrrrrlrrr : Region 4 := cutR b4rrlrlrrllrrllrrrrlrr 4 90
private def c4rrlrlrrllrrllrrrrlrrr : Cert 4 := (.split 0 765 .leaf (.split 4 95 (.split 0 1533 (.split 0 1021 .leaf (.split 4 92 (.split 0 1226 .leaf (.split 0 1363 .leaf (.split 4 91 .leaf .leaf))) .leaf)) (.split 0 3069 (.split 4 92 (.split 0 2045 (.split 0 1753 (.split 4 91 .leaf .leaf) (.split 4 91 .leaf .leaf)) .leaf) (.split 0 2045 .leaf (.split 4 93 .leaf .leaf))) (.split 4 92 .leaf (.split 0 6141 (.split 4 93 .leaf (.split 0 4093 (.split 4 94 .leaf .leaf) (.split 4 94 .leaf .leaf))) (.split 4 93 .leaf (.split 0 12285 (.split 4 94 .leaf .leaf) .leaf)))))) (.split 0 1533 .leaf (.split 0 3069 .leaf (.split 4 98 (.split 0 6141 .leaf (.split 4 96 .leaf .leaf)) .leaf)))))
theorem h4rrlrlrrllrrllrrrrlrrr : Reject b4rrlrlrrllrrllrrrrlrrr := sound c4rrlrlrrllrrllrrrrlrrr (by decide +kernel)
theorem h4rrlrlrrllrrllrrrrlrr : Reject b4rrlrlrrllrrllrrrrlrr := split b4rrlrlrrllrrllrrrrlrr 4 90 h4rrlrlrrllrrllrrrrlrrl h4rrlrlrrllrrllrrrrlrrr
theorem h4rrlrlrrllrrllrrrrlr : Reject b4rrlrlrrllrrllrrrrlr := split b4rrlrlrrllrrllrrrrlr 0 381 h4rrlrlrrllrrllrrrrlrl h4rrlrlrrllrrllrrrrlrr
theorem h4rrlrlrrllrrllrrrrl : Reject b4rrlrlrrllrrllrrrrl := split b4rrlrlrrllrrllrrrrl 4 81 h4rrlrlrrllrrllrrrrll h4rrlrlrrllrrllrrrrlr
private def b4rrlrlrrllrrllrrrrr : Region 4 := cutR b4rrlrlrrllrrllrrrr 3 19
private def c4rrlrlrrllrrllrrrrr : Cert 4 := (.split 4 81 (.split 0 381 .leaf (.split 3 20 .leaf .leaf)) .leaf)
theorem h4rrlrlrrllrrllrrrrr : Reject b4rrlrlrrllrrllrrrrr := sound c4rrlrlrrllrrllrrrrr (by decide +kernel)
theorem h4rrlrlrrllrrllrrrr : Reject b4rrlrlrrllrrllrrrr := split b4rrlrlrrllrrllrrrr 3 19 h4rrlrlrrllrrllrrrrl h4rrlrlrrllrrllrrrrr
theorem h4rrlrlrrllrrllrrr : Reject b4rrlrlrrllrrllrrr := split b4rrlrlrrllrrllrrr 0 189 h4rrlrlrrllrrllrrrl h4rrlrlrrllrrllrrrr
theorem h4rrlrlrrllrrllrr : Reject b4rrlrlrrllrrllrr := split b4rrlrlrrllrrllrr 4 67 h4rrlrlrrllrrllrrl h4rrlrlrrllrrllrrr
theorem h4rrlrlrrllrrllr : Reject b4rrlrlrrllrrllr := split b4rrlrlrrllrrllr 3 18 h4rrlrlrrllrrllrl h4rrlrlrrllrrllrr
theorem h4rrlrlrrllrrll : Reject b4rrlrlrrllrrll := split b4rrlrlrrllrrll 0 93 h4rrlrlrrllrrlll h4rrlrlrrllrrllr
private def b4rrlrlrrllrrlr : Region 4 := cutR b4rrlrlrrllrrl 4 101
private def b4rrlrlrrllrrlrl : Region 4 := cutL b4rrlrlrrllrrlr 0 93
private def c4rrlrlrrllrrlrl : Cert 4 := (.split 3 18 (.split 4 205 (.split 0 61 .leaf (.split 3 16 .leaf .leaf)) .leaf) .leaf)
theorem h4rrlrlrrllrrlrl : Reject b4rrlrlrrllrrlrl := sound c4rrlrlrrllrrlrl (by decide +kernel)
private def b4rrlrlrrllrrlrr : Region 4 := cutR b4rrlrlrrllrrlr 0 93
private def b4rrlrlrrllrrlrrl : Region 4 := cutL b4rrlrlrrllrrlrr 3 18
private def b4rrlrlrrllrrlrrll : Region 4 := cutL b4rrlrlrrllrrlrrl 4 205
private def b4rrlrlrrllrrlrrlll : Region 4 := cutL b4rrlrlrrllrrlrrll 0 189
private def b4rrlrlrrllrrlrrllll : Region 4 := cutL b4rrlrlrrllrrlrrlll 3 16
private def c4rrlrlrrllrrlrrllll : Cert 4 := .leaf
theorem h4rrlrlrrllrrlrrllll : Reject b4rrlrlrrllrrlrrllll := sound c4rrlrlrrllrrlrrllll (by decide +kernel)
private def b4rrlrlrrllrrlrrlllr : Region 4 := cutR b4rrlrlrrllrrlrrlll 3 16
private def b4rrlrlrrllrrlrrlllrl : Region 4 := cutL b4rrlrlrrllrrlrrlllr 4 136
private def b4rrlrlrrllrrlrrlllrll : Region 4 := cutL b4rrlrlrrllrrlrrlllrl 0 125
private def c4rrlrlrrllrrlrrlllrll : Cert 4 := .leaf
theorem h4rrlrlrrllrrlrrlllrll : Reject b4rrlrlrrllrrlrrlllrll := sound c4rrlrlrrllrrlrrlllrll (by decide +kernel)
private def b4rrlrlrrllrrlrrlllrlr : Region 4 := cutR b4rrlrlrrllrrlrrlllrl 0 125
private def b4rrlrlrrllrrlrrlllrlrl : Region 4 := cutL b4rrlrlrrllrrlrrlllrlr 3 17
private def b4rrlrlrrllrrlrrlllrlrll : Region 4 := cutL b4rrlrlrrllrrlrrlllrlrl 4 116
private def b4rrlrlrrllrrlrrlllrlrlll : Region 4 := cutL b4rrlrlrrllrrlrrlllrlrll 0 151
private def c4rrlrlrrllrrlrrlllrlrlll : Cert 4 := (.split 4 108 (.split 0 137 .leaf (.split 4 104 (.split 0 144 (.split 0 140 (.split 4 102 .leaf (.split 4 103 (.split 0 138 .leaf (.split 0 139 .leaf .leaf)) .leaf)) (.split 4 102 .leaf (.split 0 142 (.split 4 103 .leaf .leaf) .leaf))) .leaf) (.split 0 144 .leaf (.split 4 106 (.split 0 147 (.split 4 105 .leaf .leaf) .leaf) (.split 0 147 .leaf (.split 0 149 .leaf (.split 4 107 .leaf .leaf))))))) .leaf)
theorem h4rrlrlrrllrrlrrlllrlrlll : Reject b4rrlrlrrllrrlrrlllrlrlll := sound c4rrlrlrrllrrlrrlllrlrlll (by decide +kernel)
private def b4rrlrlrrllrrlrrlllrlrllr : Region 4 := cutR b4rrlrlrrllrrlrrlllrlrll 0 151
private def c4rrlrlrrllrrlrrlllrlrllr : Cert 4 := (.split 4 108 .leaf (.split 0 168 (.split 4 112 (.split 0 159 (.split 4 110 (.split 0 155 (.split 0 153 .leaf (.split 4 109 (.split 0 154 .leaf .leaf) .leaf)) (.split 0 157 (.split 4 109 .leaf .leaf) .leaf)) .leaf) (.split 4 110 .leaf (.split 0 163 (.split 0 161 (.split 4 111 .leaf .leaf) .leaf) .leaf))) (.split 0 159 .leaf (.split 0 163 .leaf (.split 4 114 (.split 0 165 (.split 4 113 (.split 0 164 .leaf .leaf) .leaf) (.split 4 113 .leaf .leaf)) .leaf)))) (.split 4 112 .leaf (.split 0 178 (.split 0 173 (.split 4 114 .leaf (.split 0 170 (.split 4 115 .leaf .leaf) (.split 4 115 .leaf .leaf))) .leaf) .leaf))))
theorem h4rrlrlrrllrrlrrlllrlrllr : Reject b4rrlrlrrllrrlrrlllrlrllr := sound c4rrlrlrrllrrlrrlllrlrllr (by decide +kernel)
theorem h4rrlrlrrllrrlrrlllrlrll : Reject b4rrlrlrrllrrlrrlllrlrll := split b4rrlrlrrllrrlrrlllrlrll 0 151 h4rrlrlrrllrrlrrlllrlrlll h4rrlrlrrllrrlrrlllrlrllr
private def b4rrlrlrrllrrlrrlllrlrlr : Region 4 := cutR b4rrlrlrrllrrlrrlllrlrl 4 116
private def c4rrlrlrrllrrlrrlllrlrlr : Cert 4 := (.split 0 151 .leaf (.split 4 125 (.split 0 168 .leaf (.split 4 120 (.split 0 178 (.split 0 173 .leaf (.split 4 118 (.split 0 175 .leaf (.split 4 117 .leaf .leaf)) .leaf)) (.split 0 183 (.split 4 118 .leaf (.split 0 180 .leaf (.split 4 119 .leaf .leaf))) .leaf)) (.split 0 178 .leaf (.split 4 122 (.split 0 183 .leaf (.split 0 186 .leaf (.split 4 121 .leaf .leaf))) .leaf)))) .leaf))
theorem h4rrlrlrrllrrlrrlllrlrlr : Reject b4rrlrlrrllrrlrrlllrlrlr := sound c4rrlrlrrllrrlrrlllrlrlr (by decide +kernel)
theorem h4rrlrlrrllrrlrrlllrlrl : Reject b4rrlrlrrllrrlrrlllrlrl := split b4rrlrlrrllrrlrrlllrlrl 4 116 h4rrlrlrrllrrlrrlllrlrll h4rrlrlrrllrrlrrlllrlrlr
private def b4rrlrlrrllrrlrrlllrlrr : Region 4 := cutR b4rrlrlrrllrrlrrlllrlr 3 17
private def c4rrlrlrrllrrlrrlllrlrr : Cert 4 := .leaf
theorem h4rrlrlrrllrrlrrlllrlrr : Reject b4rrlrlrrllrrlrrlllrlrr := sound c4rrlrlrrllrrlrrlllrlrr (by decide +kernel)
theorem h4rrlrlrrllrrlrrlllrlr : Reject b4rrlrlrrllrrlrrlllrlr := split b4rrlrlrrllrrlrrlllrlr 3 17 h4rrlrlrrllrrlrrlllrlrl h4rrlrlrrllrrlrrlllrlrr
theorem h4rrlrlrrllrrlrrlllrl : Reject b4rrlrlrrllrrlrrlllrl := split b4rrlrlrrllrrlrrlllrl 0 125 h4rrlrlrrllrrlrrlllrll h4rrlrlrrllrrlrrlllrlr
private def b4rrlrlrrllrrlrrlllrr : Region 4 := cutR b4rrlrlrrllrrlrrlllr 4 136
private def c4rrlrlrrllrrlrrlllrr : Cert 4 := .leaf
theorem h4rrlrlrrllrrlrrlllrr : Reject b4rrlrlrrllrrlrrlllrr := sound c4rrlrlrrllrrlrrlllrr (by decide +kernel)
theorem h4rrlrlrrllrrlrrlllr : Reject b4rrlrlrrllrrlrrlllr := split b4rrlrlrrllrrlrrlllr 4 136 h4rrlrlrrllrrlrrlllrl h4rrlrlrrllrrlrrlllrr
theorem h4rrlrlrrllrrlrrlll : Reject b4rrlrlrrllrrlrrlll := split b4rrlrlrrllrrlrrlll 3 16 h4rrlrlrrllrrlrrllll h4rrlrlrrllrrlrrlllr
private def b4rrlrlrrllrrlrrllr : Region 4 := cutR b4rrlrlrrllrrlrrll 0 189
private def b4rrlrlrrllrrlrrllrl : Region 4 := cutL b4rrlrlrrllrrlrrllr 3 16
private def c4rrlrlrrllrrlrrllrl : Cert 4 := .leaf
theorem h4rrlrlrrllrrlrrllrl : Reject b4rrlrlrrllrrlrrllrl := sound c4rrlrlrrllrrlrrllrl (by decide +kernel)
private def b4rrlrlrrllrrlrrllrr : Region 4 := cutR b4rrlrlrrllrrlrrllr 3 16
private def b4rrlrlrrllrrlrrllrrl : Region 4 := cutL b4rrlrlrrllrrlrrllrr 4 136
private def b4rrlrlrrllrrlrrllrrll : Region 4 := cutL b4rrlrlrrllrrlrrllrrl 0 381
private def b4rrlrlrrllrrlrrllrrlll : Region 4 := cutL b4rrlrlrrllrrlrrllrrll 3 17
private def b4rrlrlrrllrrlrrllrrllll : Region 4 := cutL b4rrlrlrrllrrlrrllrrlll 4 116
private def c4rrlrlrrllrrlrrllrrllll : Cert 4 := .leaf
theorem h4rrlrlrrllrrlrrllrrllll : Reject b4rrlrlrrllrrlrrllrrllll := sound c4rrlrlrrllrrlrrllrrllll (by decide +kernel)
private def b4rrlrlrrllrrlrrllrrlllr : Region 4 := cutR b4rrlrlrrllrrlrrllrrlll 4 116
private def b4rrlrlrrllrrlrrllrrlllrl : Region 4 := cutL b4rrlrlrrllrrlrrllrrlllr 0 253
private def b4rrlrlrrllrrlrrllrrlllrll : Region 4 := cutL b4rrlrlrrllrrlrrllrrlllrl 4 125
private def c4rrlrlrrllrrlrrllrrlllrll : Cert 4 := (.split 0 217 (.split 4 120 .leaf (.split 0 202 (.split 4 122 .leaf (.split 0 195 (.split 4 123 .leaf .leaf) (.split 4 123 .leaf (.split 0 198 (.split 4 124 .leaf .leaf) .leaf)))) .leaf)) .leaf)
theorem h4rrlrlrrllrrlrrllrrlllrll : Reject b4rrlrlrrllrrlrrllrrlllrll := sound c4rrlrlrrllrrlrrllrrlllrll (by decide +kernel)
private def b4rrlrlrrllrrlrrllrrlllrlr : Region 4 := cutR b4rrlrlrrllrrlrrllrrlllrl 4 125
private def b4rrlrlrrllrrlrrllrrlllrlrl : Region 4 := cutL b4rrlrlrrllrrlrrllrrlllrlr 0 217
private def c4rrlrlrrllrrlrrllrrlllrlrl : Cert 4 := (.split 4 130 (.split 0 202 (.split 0 195 .leaf (.split 4 127 (.split 0 198 .leaf (.split 4 126 .leaf .leaf)) .leaf)) (.split 0 209 (.split 4 127 (.split 0 205 (.split 4 126 .leaf (.split 0 203 .leaf (.split 0 204 .leaf .leaf))) .leaf) (.split 4 128 .leaf .leaf)) (.split 4 127 .leaf (.split 0 213 (.split 4 128 .leaf (.split 4 129 .leaf .leaf)) (.split 4 128 .leaf (.split 4 129 .leaf .leaf)))))) .leaf)
theorem h4rrlrlrrllrrlrrllrrlllrlrl : Reject b4rrlrlrrllrrlrrllrrlllrlrl := sound c4rrlrlrrllrrlrrllrrlllrlrl (by decide +kernel)
private def b4rrlrlrrllrrlrrllrrlllrlrr : Region 4 := cutR b4rrlrlrrllrrlrrllrrlllrlr 0 217
private def c4rrlrlrrllrrlrrllrrlllrlrr : Cert 4 := (.split 4 130 .leaf (.split 0 234 (.split 4 133 (.split 0 225 (.split 0 221 (.split 4 131 .leaf .leaf) (.split 4 131 .leaf (.split 4 132 .leaf .leaf))) .leaf) (.split 0 225 .leaf (.split 0 229 (.split 4 134 .leaf .leaf) (.split 4 134 .leaf (.split 0 231 .leaf (.split 4 135 .leaf .leaf)))))) (.split 4 133 .leaf (.split 0 243 (.split 0 238 (.split 4 134 .leaf (.split 4 135 .leaf .leaf)) .leaf) .leaf))))
theorem h4rrlrlrrllrrlrrllrrlllrlrr : Reject b4rrlrlrrllrrlrrllrrlllrlrr := sound c4rrlrlrrllrrlrrllrrlllrlrr (by decide +kernel)
theorem h4rrlrlrrllrrlrrllrrlllrlr : Reject b4rrlrlrrllrrlrrllrrlllrlr := split b4rrlrlrrllrrlrrllrrlllrlr 0 217 h4rrlrlrrllrrlrrllrrlllrlrl h4rrlrlrrllrrlrrllrrlllrlrr
theorem h4rrlrlrrllrrlrrllrrlllrl : Reject b4rrlrlrrllrrlrrllrrlllrl := split b4rrlrlrrllrrlrrllrrlllrl 4 125 h4rrlrlrrllrrlrrllrrlllrll h4rrlrlrrllrrlrrllrrlllrlr
private def b4rrlrlrrllrrlrrllrrlllrr : Region 4 := cutR b4rrlrlrrllrrlrrllrrlllr 0 253
private def c4rrlrlrrllrrlrrllrrlllrr : Cert 4 := .leaf
theorem h4rrlrlrrllrrlrrllrrlllrr : Reject b4rrlrlrrllrrlrrllrrlllrr := sound c4rrlrlrrllrrlrrllrrlllrr (by decide +kernel)
theorem h4rrlrlrrllrrlrrllrrlllr : Reject b4rrlrlrrllrrlrrllrrlllr := split b4rrlrlrrllrrlrrllrrlllr 0 253 h4rrlrlrrllrrlrrllrrlllrl h4rrlrlrrllrrlrrllrrlllrr
theorem h4rrlrlrrllrrlrrllrrlll : Reject b4rrlrlrrllrrlrrllrrlll := split b4rrlrlrrllrrlrrllrrlll 4 116 h4rrlrlrrllrrlrrllrrllll h4rrlrlrrllrrlrrllrrlllr
private def b4rrlrlrrllrrlrrllrrllr : Region 4 := cutR b4rrlrlrrllrrlrrllrrll 3 17
private def c4rrlrlrrllrrlrrllrrllr : Cert 4 := .leaf
theorem h4rrlrlrrllrrlrrllrrllr : Reject b4rrlrlrrllrrlrrllrrllr := sound c4rrlrlrrllrrlrrllrrllr (by decide +kernel)
theorem h4rrlrlrrllrrlrrllrrll : Reject b4rrlrlrrllrrlrrllrrll := split b4rrlrlrrllrrlrrllrrll 3 17 h4rrlrlrrllrrlrrllrrlll h4rrlrlrrllrrlrrllrrllr
private def b4rrlrlrrllrrlrrllrrlr : Region 4 := cutR b4rrlrlrrllrrlrrllrrl 0 381
private def c4rrlrlrrllrrlrrllrrlr : Cert 4 := (.split 3 17 .leaf .leaf)
theorem h4rrlrlrrllrrlrrllrrlr : Reject b4rrlrlrrllrrlrrllrrlr := sound c4rrlrlrrllrrlrrllrrlr (by decide +kernel)
theorem h4rrlrlrrllrrlrrllrrl : Reject b4rrlrlrrllrrlrrllrrl := split b4rrlrlrrllrrlrrllrrl 0 381 h4rrlrlrrllrrlrrllrrll h4rrlrlrrllrrlrrllrrlr
private def b4rrlrlrrllrrlrrllrrr : Region 4 := cutR b4rrlrlrrllrrlrrllrr 4 136
private def b4rrlrlrrllrrlrrllrrrl : Region 4 := cutL b4rrlrlrrllrrlrrllrrr 0 381
private def b4rrlrlrrllrrlrrllrrrll : Region 4 := cutL b4rrlrlrrllrrlrrllrrrl 3 17
private def b4rrlrlrrllrrlrrllrrrlll : Region 4 := cutL b4rrlrlrrllrrlrrllrrrll 4 164
private def b4rrlrlrrllrrlrrllrrrllll : Region 4 := cutL b4rrlrlrrllrrlrrllrrrlll 0 253
private def c4rrlrlrrllrrlrrllrrrllll : Cert 4 := (.split 4 149 (.split 0 217 .leaf (.split 4 142 (.split 0 234 .leaf (.split 4 139 (.split 0 243 (.split 0 238 .leaf (.split 4 137 (.split 0 240 (.split 0 239 .leaf .leaf) .leaf) .leaf)) (.split 0 248 (.split 4 137 .leaf (.split 0 245 (.split 4 138 .leaf .leaf) (.split 4 138 .leaf (.split 0 246 .leaf (.split 0 247 .leaf .leaf))))) .leaf)) (.split 0 243 .leaf (.split 0 248 .leaf (.split 4 140 .leaf .leaf))))) .leaf)) .leaf)
theorem h4rrlrlrrllrrlrrllrrrllll : Reject b4rrlrlrrllrrlrrllrrrllll := sound c4rrlrlrrllrrlrrllrrrllll (by decide +kernel)
private def b4rrlrlrrllrrlrrllrrrlllr : Region 4 := cutR b4rrlrlrrllrrlrrllrrrlll 0 253
private def b4rrlrlrrllrrlrrllrrrlllrl : Region 4 := cutL b4rrlrlrrllrrlrrllrrrlllr 4 149
private def b4rrlrlrrllrrlrrllrrrlllrll : Region 4 := cutL b4rrlrlrrllrrlrrllrrrlllrl 0 304
private def b4rrlrlrrllrrlrrllrrrlllrlll : Region 4 := cutL b4rrlrlrrllrrlrrllrrrlllrll 4 142
private def c4rrlrlrrllrrlrrllrrrlllrlll : Cert 4 := (.split 0 276 (.split 4 139 .leaf (.split 0 264 (.split 0 258 (.split 4 140 .leaf (.split 4 141 .leaf .leaf)) (.split 4 140 .leaf (.split 0 261 (.split 4 141 .leaf .leaf) .leaf))) .leaf)) .leaf)
theorem h4rrlrlrrllrrlrrllrrrlllrlll : Reject b4rrlrlrrllrrlrrllrrrlllrlll := sound c4rrlrlrrllrrlrrllrrrlllrlll (by decide +kernel)
private def b4rrlrlrrllrrlrrllrrrlllrllr : Region 4 := cutR b4rrlrlrrllrrlrrllrrrlllrll 4 142
private def c4rrlrlrrllrrlrrllrrrlllrllr : Cert 4 := (.split 0 276 (.split 4 145 (.split 0 264 (.split 0 258 .leaf (.split 4 143 .leaf .leaf)) (.split 0 270 (.split 4 143 .leaf (.split 0 267 .leaf (.split 4 144 .leaf .leaf))) (.split 4 143 .leaf (.split 0 273 (.split 4 144 .leaf .leaf) .leaf)))) .leaf) (.split 4 145 .leaf (.split 0 289 (.split 4 147 (.split 0 282 (.split 0 279 (.split 4 146 .leaf .leaf) (.split 4 146 .leaf .leaf)) .leaf) (.split 0 282 .leaf (.split 0 285 .leaf (.split 4 148 .leaf .leaf)))) .leaf)))
theorem h4rrlrlrrllrrlrrllrrrlllrllr : Reject b4rrlrlrrllrrlrrllrrrlllrllr := sound c4rrlrlrrllrrlrrllrrrlllrllr (by decide +kernel)
theorem h4rrlrlrrllrrlrrllrrrlllrll : Reject b4rrlrlrrllrrlrrllrrrlllrll := split b4rrlrlrrllrrlrrllrrrlllrll 4 142 h4rrlrlrrllrrlrrllrrrlllrlll h4rrlrlrrllrrlrrllrrrlllrllr
private def b4rrlrlrrllrrlrrllrrrlllrlr : Region 4 := cutR b4rrlrlrrllrrlrrllrrrlllrl 0 304
private def c4rrlrlrrllrrlrrllrrrlllrlr : Cert 4 := .leaf
theorem h4rrlrlrrllrrlrrllrrrlllrlr : Reject b4rrlrlrrllrrlrrllrrrlllrlr := sound c4rrlrlrrllrrlrrllrrrlllrlr (by decide +kernel)
theorem h4rrlrlrrllrrlrrllrrrlllrl : Reject b4rrlrlrrllrrlrrllrrrlllrl := split b4rrlrlrrllrrlrrllrrrlllrl 0 304 h4rrlrlrrllrrlrrllrrrlllrll h4rrlrlrrllrrlrrllrrrlllrlr
private def b4rrlrlrrllrrlrrllrrrlllrr : Region 4 := cutR b4rrlrlrrllrrlrrllrrrlllr 4 149
private def b4rrlrlrrllrrlrrllrrrlllrrl : Region 4 := cutL b4rrlrlrrllrrlrrllrrrlllrr 0 304
private def c4rrlrlrrllrrlrrllrrrlllrrl : Cert 4 := (.split 4 156 (.split 0 276 .leaf (.split 0 289 .leaf (.split 4 152 (.split 0 296 (.split 4 150 .leaf .leaf) (.split 4 150 .leaf (.split 0 300 (.split 4 151 (.split 0 298 .leaf (.split 0 299 .leaf .leaf)) .leaf) (.split 4 151 .leaf .leaf)))) .leaf))) .leaf)
theorem h4rrlrlrrllrrlrrllrrrlllrrl : Reject b4rrlrlrrllrrlrrllrrrlllrrl := sound c4rrlrlrrllrrlrrllrrrlllrrl (by decide +kernel)
private def b4rrlrlrrllrrlrrllrrrlllrrr : Region 4 := cutR b4rrlrlrrllrrlrrllrrrlllrr 0 304
private def b4rrlrlrrllrrlrrllrrrlllrrrl : Region 4 := cutL b4rrlrlrrllrrlrrllrrrlllrrr 4 156
private def c4rrlrlrrllrrlrrllrrrlllrrrl : Cert 4 := (.split 0 338 (.split 0 320 (.split 4 152 .leaf (.split 4 154 (.split 0 312 (.split 0 308 .leaf (.split 4 153 .leaf .leaf)) (.split 0 316 (.split 4 153 .leaf .leaf) .leaf)) (.split 0 312 .leaf (.split 0 316 .leaf (.split 4 155 .leaf .leaf))))) (.split 4 152 .leaf (.split 0 329 (.split 4 154 .leaf (.split 0 324 (.split 4 155 .leaf .leaf) .leaf)) .leaf))) .leaf)
theorem h4rrlrlrrllrrlrrllrrrlllrrrl : Reject b4rrlrlrrllrrlrrllrrrlllrrrl := sound c4rrlrlrrllrrlrrllrrrlllrrrl (by decide +kernel)
private def b4rrlrlrrllrrlrrllrrrlllrrrr : Region 4 := cutR b4rrlrlrrllrrlrrllrrrlllrrr 4 156
private def c4rrlrlrrllrrlrrllrrrlllrrrr : Cert 4 := (.split 0 338 (.split 4 160 (.split 0 320 .leaf (.split 0 329 .leaf (.split 4 158 (.split 0 333 (.split 4 157 .leaf .leaf) (.split 4 157 .leaf .leaf)) .leaf))) .leaf) (.split 4 160 (.split 0 358 (.split 0 348 (.split 4 158 .leaf (.split 0 343 (.split 4 159 .leaf .leaf) (.split 4 159 .leaf .leaf))) .leaf) .leaf) (.split 0 358 (.split 0 348 .leaf (.split 4 162 (.split 0 353 (.split 4 161 .leaf .leaf) (.split 4 161 .leaf .leaf)) .leaf)) (.split 0 369 (.split 4 162 .leaf (.split 0 363 .leaf (.split 4 163 (.split 0 366 (.split 0 364 .leaf .leaf) .leaf) .leaf))) (.split 4 162 .leaf (.split 0 375 (.split 4 163 .leaf .leaf) .leaf))))))
theorem h4rrlrlrrllrrlrrllrrrlllrrrr : Reject b4rrlrlrrllrrlrrllrrrlllrrrr := sound c4rrlrlrrllrrlrrllrrrlllrrrr (by decide +kernel)
theorem h4rrlrlrrllrrlrrllrrrlllrrr : Reject b4rrlrlrrllrrlrrllrrrlllrrr := split b4rrlrlrrllrrlrrllrrrlllrrr 4 156 h4rrlrlrrllrrlrrllrrrlllrrrl h4rrlrlrrllrrlrrllrrrlllrrrr
theorem h4rrlrlrrllrrlrrllrrrlllrr : Reject b4rrlrlrrllrrlrrllrrrlllrr := split b4rrlrlrrllrrlrrllrrrlllrr 0 304 h4rrlrlrrllrrlrrllrrrlllrrl h4rrlrlrrllrrlrrllrrrlllrrr
theorem h4rrlrlrrllrrlrrllrrrlllr : Reject b4rrlrlrrllrrlrrllrrrlllr := split b4rrlrlrrllrrlrrllrrrlllr 4 149 h4rrlrlrrllrrlrrllrrrlllrl h4rrlrlrrllrrlrrllrrrlllrr
theorem h4rrlrlrrllrrlrrllrrrlll : Reject b4rrlrlrrllrrlrrllrrrlll := split b4rrlrlrrllrrlrrllrrrlll 0 253 h4rrlrlrrllrrlrrllrrrllll h4rrlrlrrllrrlrrllrrrlllr
private def b4rrlrlrrllrrlrrllrrrllr : Region 4 := cutR b4rrlrlrrllrrlrrllrrrll 4 164
private def c4rrlrlrrllrrlrrllrrrllr : Cert 4 := (.split 0 253 .leaf (.split 4 182 (.split 0 304 .leaf (.split 4 173 (.split 0 338 .leaf (.split 4 168 (.split 0 358 .leaf (.split 0 369 .leaf (.split 4 166 (.split 0 375 .leaf (.split 4 165 .leaf .leaf)) .leaf))) .leaf)) .leaf)) .leaf))
theorem h4rrlrlrrllrrlrrllrrrllr : Reject b4rrlrlrrllrrlrrllrrrllr := sound c4rrlrlrrllrrlrrllrrrllr (by decide +kernel)
theorem h4rrlrlrrllrrlrrllrrrll : Reject b4rrlrlrrllrrlrrllrrrll := split b4rrlrlrrllrrlrrllrrrll 4 164 h4rrlrlrrllrrlrrllrrrlll h4rrlrlrrllrrlrrllrrrllr
private def b4rrlrlrrllrrlrrllrrrlr : Region 4 := cutR b4rrlrlrrllrrlrrllrrrl 3 17
private def c4rrlrlrrllrrlrrllrrrlr : Cert 4 := .leaf
theorem h4rrlrlrrllrrlrrllrrrlr : Reject b4rrlrlrrllrrlrrllrrrlr := sound c4rrlrlrrllrrlrrllrrrlr (by decide +kernel)
theorem h4rrlrlrrllrrlrrllrrrl : Reject b4rrlrlrrllrrlrrllrrrl := split b4rrlrlrrllrrlrrllrrrl 3 17 h4rrlrlrrllrrlrrllrrrll h4rrlrlrrllrrlrrllrrrlr
private def b4rrlrlrrllrrlrrllrrrr : Region 4 := cutR b4rrlrlrrllrrlrrllrrr 0 381
private def b4rrlrlrrllrrlrrllrrrrl : Region 4 := cutL b4rrlrlrrllrrlrrllrrrr 3 17
private def b4rrlrlrrllrrlrrllrrrrll : Region 4 := cutL b4rrlrlrrllrrlrrllrrrrl 4 164
private def c4rrlrlrrllrrlrrllrrrrll : Cert 4 := .leaf
theorem h4rrlrlrrllrrlrrllrrrrll : Reject b4rrlrlrrllrrlrrllrrrrll := sound c4rrlrlrrllrrlrrllrrrrll (by decide +kernel)
private def b4rrlrlrrllrrlrrllrrrrlr : Region 4 := cutR b4rrlrlrrllrrlrrllrrrrl 4 164
private def b4rrlrlrrllrrlrrllrrrrlrl : Region 4 := cutL b4rrlrlrrllrrlrrllrrrrlr 0 765
private def b4rrlrlrrllrrlrrllrrrrlrll : Region 4 := cutL b4rrlrlrrllrrlrrllrrrrlrl 4 182
private def b4rrlrlrrllrrlrrllrrrrlrlll : Region 4 := cutL b4rrlrlrrllrrlrrllrrrrlrll 0 509
private def b4rrlrlrrllrrlrrllrrrrlrllll : Region 4 := cutL b4rrlrlrrllrrlrrllrrrrlrlll 4 173
private def b4rrlrlrrllrrlrrllrrrrlrlllll : Region 4 := cutL b4rrlrlrrllrrlrrllrrrrlrllll 0 436
private def c4rrlrlrrllrrlrrllrrrrlrlllll : Cert 4 := (.split 4 168 (.split 0 407 (.split 0 394 (.split 4 166 (.split 0 387 (.split 4 165 .leaf .leaf) .leaf) (.split 0 387 .leaf (.split 4 167 (.split 0 390 .leaf .leaf) .leaf))) (.split 4 166 .leaf (.split 0 400 (.split 4 167 .leaf .leaf) .leaf))) .leaf) (.split 0 407 (.split 4 170 (.split 0 394 .leaf (.split 0 400 .leaf (.split 4 169 .leaf .leaf))) .leaf) (.split 4 170 (.split 0 421 (.split 0 414 (.split 4 169 .leaf .leaf) .leaf) .leaf) (.split 0 421 (.split 4 171 .leaf .leaf) (.split 4 171 .leaf (.split 0 428 (.split 4 172 .leaf .leaf) (.split 4 172 .leaf (.split 0 432 .leaf (.split 0 434 (.split 0 433 .leaf .leaf) .leaf)))))))))
theorem h4rrlrlrrllrrlrrllrrrrlrlllll : Reject b4rrlrlrrllrrlrrllrrrrlrlllll := sound c4rrlrlrrllrrlrrllrrrrlrlllll (by decide +kernel)
private def b4rrlrlrrllrrlrrllrrrrlrllllr : Region 4 := cutR b4rrlrlrrllrrlrrllrrrrlrllll 0 436
private def c4rrlrlrrllrrlrrllrrrrlrllllr : Cert 4 := .leaf
theorem h4rrlrlrrllrrlrrllrrrrlrllllr : Reject b4rrlrlrrllrrlrrllrrrrlrllllr := sound c4rrlrlrrllrrlrrllrrrrlrllllr (by decide +kernel)
theorem h4rrlrlrrllrrlrrllrrrrlrllll : Reject b4rrlrlrrllrrlrrllrrrrlrllll := split b4rrlrlrrllrrlrrllrrrrlrllll 0 436 h4rrlrlrrllrrlrrllrrrrlrlllll h4rrlrlrrllrrlrrllrrrrlrllllr
private def b4rrlrlrrllrrlrrllrrrrlrlllr : Region 4 := cutR b4rrlrlrrllrrlrrllrrrrlrlll 4 173
private def c4rrlrlrrllrrlrrllrrrrlrlllr : Cert 4 := (.split 0 436 .leaf (.split 0 470 (.split 4 177 (.split 0 452 (.split 4 175 (.split 0 444 (.split 4 174 .leaf .leaf) (.split 4 174 .leaf .leaf)) .leaf) (.split 4 175 .leaf (.split 0 461 (.split 4 176 .leaf .leaf) (.split 4 176 .leaf .leaf)))) .leaf) (.split 4 177 .leaf (.split 0 489 (.split 4 179 (.split 0 479 (.split 4 178 .leaf .leaf) (.split 4 178 .leaf (.split 0 484 (.split 0 481 .leaf (.split 0 482 .leaf (.split 0 483 .leaf .leaf))) .leaf))) .leaf) (.split 4 179 .leaf (.split 0 499 (.split 4 180 .leaf .leaf) (.split 4 180 .leaf (.split 4 181 (.split 0 504 (.split 0 501 .leaf (.split 0 502 .leaf .leaf)) .leaf) .leaf))))))))
theorem h4rrlrlrrllrrlrrllrrrrlrlllr : Reject b4rrlrlrrllrrlrrllrrrrlrlllr := sound c4rrlrlrrllrrlrrllrrrrlrlllr (by decide +kernel)
theorem h4rrlrlrrllrrlrrllrrrrlrlll : Reject b4rrlrlrrllrrlrrllrrrrlrlll := split b4rrlrlrrllrrlrrllrrrrlrlll 4 173 h4rrlrlrrllrrlrrllrrrrlrllll h4rrlrlrrllrrlrrllrrrrlrlllr
private def b4rrlrlrrllrrlrrllrrrrlrllr : Region 4 := cutR b4rrlrlrrllrrlrrllrrrrlrll 0 509
private def c4rrlrlrrllrrlrrllrrrrlrllr : Cert 4 := (.split 4 173 .leaf (.split 0 612 (.split 0 556 (.split 4 177 .leaf (.split 0 532 (.split 4 179 .leaf (.split 0 520 (.split 4 180 .leaf (.split 0 514 (.split 4 181 .leaf .leaf) .leaf)) .leaf)) .leaf)) .leaf) .leaf))
theorem h4rrlrlrrllrrlrrllrrrrlrllr : Reject b4rrlrlrrllrrlrrllrrrrlrllr := sound c4rrlrlrrllrrlrrllrrrrlrllr (by decide +kernel)
theorem h4rrlrlrrllrrlrrllrrrrlrll : Reject b4rrlrlrrllrrlrrllrrrrlrll := split b4rrlrlrrllrrlrrllrrrrlrll 0 509 h4rrlrlrrllrrlrrllrrrrlrlll h4rrlrlrrllrrlrrllrrrrlrllr
private def b4rrlrlrrllrrlrrllrrrrlrlr : Region 4 := cutR b4rrlrlrrllrrlrrllrrrrlrl 4 182
private def b4rrlrlrrllrrlrrllrrrrlrlrl : Region 4 := cutL b4rrlrlrrllrrlrrllrrrrlrlr 0 509
private def c4rrlrlrrllrrlrrllrrrrlrlrl : Cert 4 := .leaf
theorem h4rrlrlrrllrrlrrllrrrrlrlrl : Reject b4rrlrlrrllrrlrrllrrrrlrlrl := sound c4rrlrlrrllrrlrrllrrrrlrlrl (by decide +kernel)
private def b4rrlrlrrllrrlrrllrrrrlrlrr : Region 4 := cutR b4rrlrlrrllrrlrrllrrrrlrlr 0 509
private def b4rrlrlrrllrrlrrllrrrrlrlrrl : Region 4 := cutL b4rrlrlrrllrrlrrllrrrrlrlrr 4 193
private def b4rrlrlrrllrrlrrllrrrrlrlrrll : Region 4 := cutL b4rrlrlrrllrrlrrllrrrrlrlrrl 0 612
private def b4rrlrlrrllrrlrrllrrrrlrlrrlll : Region 4 := cutL b4rrlrlrrllrrlrrllrrrrlrlrrll 4 187
private def c4rrlrlrrllrrlrrllrrrrlrlrrlll : Cert 4 := (.split 0 556 (.split 0 532 (.split 4 184 (.split 0 520 .leaf (.split 0 526 (.split 4 183 .leaf .leaf) (.split 4 183 .leaf .leaf))) .leaf) (.split 4 184 .leaf (.split 0 544 (.split 4 185 .leaf .leaf) (.split 4 185 .leaf (.split 0 550 .leaf (.split 4 186 .leaf .leaf)))))) (.split 0 583 (.split 4 184 .leaf (.split 0 569 (.split 4 185 .leaf (.split 0 562 (.split 4 186 .leaf .leaf) (.split 4 186 .leaf .leaf))) .leaf)) .leaf))
theorem h4rrlrlrrllrrlrrllrrrrlrlrrlll : Reject b4rrlrlrrllrrlrrllrrrrlrlrrlll := sound c4rrlrlrrllrrlrrllrrrrlrlrrlll (by decide +kernel)
private def b4rrlrlrrllrrlrrllrrrrlrlrrllr : Region 4 := cutR b4rrlrlrrllrrlrrllrrrrlrlrrll 4 187
private def c4rrlrlrrllrrlrrllrrrrlrlrrllr : Cert 4 := (.split 0 556 .leaf (.split 4 190 (.split 0 583 (.split 0 569 .leaf (.split 4 188 .leaf .leaf)) (.split 0 597 (.split 4 188 .leaf (.split 0 590 (.split 4 189 .leaf .leaf) (.split 4 189 .leaf .leaf))) (.split 4 188 .leaf (.split 0 604 (.split 4 189 .leaf .leaf) .leaf)))) (.split 0 583 .leaf (.split 0 597 .leaf (.split 4 191 (.split 0 604 .leaf (.split 0 608 .leaf (.split 0 610 .leaf (.split 0 611 .leaf .leaf)))) .leaf)))))
theorem h4rrlrlrrllrrlrrllrrrrlrlrrllr : Reject b4rrlrlrrllrrlrrllrrrrlrlrrllr := sound c4rrlrlrrllrrlrrllrrrrlrlrrllr (by decide +kernel)
theorem h4rrlrlrrllrrlrrllrrrrlrlrrll : Reject b4rrlrlrrllrrlrrllrrrrlrlrrll := split b4rrlrlrrllrrlrrllrrrrlrlrrll 4 187 h4rrlrlrrllrrlrrllrrrrlrlrrlll h4rrlrlrrllrrlrrllrrrrlrlrrllr
private def b4rrlrlrrllrrlrrllrrrrlrlrrlr : Region 4 := cutR b4rrlrlrrllrrlrrllrrrrlrlrrl 0 612
private def c4rrlrlrrllrrlrrllrrrrlrlrrlr : Cert 4 := (.split 4 187 .leaf (.split 0 680 (.split 4 190 .leaf (.split 0 644 (.split 0 628 (.split 4 191 .leaf (.split 0 620 .leaf (.split 4 192 .leaf .leaf))) (.split 4 191 .leaf (.split 0 636 (.split 4 192 .leaf .leaf) (.split 4 192 .leaf (.split 0 640 (.split 0 638 (.split 0 637 .leaf .leaf) .leaf) .leaf))))) .leaf)) .leaf))
theorem h4rrlrlrrllrrlrrllrrrrlrlrrlr : Reject b4rrlrlrrllrrlrrllrrrrlrlrrlr := sound c4rrlrlrrllrrlrrllrrrrlrlrrlr (by decide +kernel)
theorem h4rrlrlrrllrrlrrllrrrrlrlrrl : Reject b4rrlrlrrllrrlrrllrrrrlrlrrl := split b4rrlrlrrllrrlrrllrrrrlrlrrl 0 612 h4rrlrlrrllrrlrrllrrrrlrlrrll h4rrlrlrrllrrlrrllrrrrlrlrrlr
private def b4rrlrlrrllrrlrrllrrrrlrlrrr : Region 4 := cutR b4rrlrlrrllrrlrrllrrrrlrlrr 4 193
private def b4rrlrlrrllrrlrrllrrrrlrlrrrl : Region 4 := cutL b4rrlrlrrllrrlrrllrrrrlrlrrr 0 612
private def c4rrlrlrrllrrlrrllrrrrlrlrrrl : Cert 4 := .leaf
theorem h4rrlrlrrllrrlrrllrrrrlrlrrrl : Reject b4rrlrlrrllrrlrrllrrrrlrlrrrl := sound c4rrlrlrrllrrlrrllrrrrlrlrrrl (by decide +kernel)
private def b4rrlrlrrllrrlrrllrrrrlrlrrrr : Region 4 := cutR b4rrlrlrrllrrlrrllrrrrlrlrrr 0 612
private def b4rrlrlrrllrrlrrllrrrrlrlrrrrl : Region 4 := cutL b4rrlrlrrllrrlrrllrrrrlrlrrrr 4 199
private def c4rrlrlrrllrrlrrllrrrrlrlrrrrl : Cert 4 := (.split 0 680 (.split 0 644 .leaf (.split 4 196 (.split 0 662 (.split 4 194 .leaf .leaf) (.split 4 194 .leaf (.split 0 671 (.split 4 195 .leaf .leaf) (.split 4 195 .leaf .leaf)))) .leaf)) (.split 0 720 (.split 4 196 .leaf (.split 0 699 (.split 4 197 (.split 0 689 .leaf (.split 0 694 .leaf .leaf)) .leaf) (.split 4 197 .leaf (.split 0 709 .leaf (.split 4 198 .leaf .leaf))))) (.split 4 196 .leaf (.split 0 742 (.split 4 197 .leaf (.split 0 731 (.split 4 198 .leaf (.split 0 725 .leaf (.split 0 728 (.split 0 726 .leaf .leaf) .leaf))) .leaf)) .leaf))))
theorem h4rrlrlrrllrrlrrllrrrrlrlrrrrl : Reject b4rrlrlrrllrrlrrllrrrrlrlrrrrl := sound c4rrlrlrrllrrlrrllrrrrlrlrrrrl (by decide +kernel)
private def b4rrlrlrrllrrlrrllrrrrlrlrrrrr : Region 4 := cutR b4rrlrlrrllrrlrrllrrrrlrlrrrr 4 199
private def c4rrlrlrrllrrlrrllrrrrlrlrrrrr : Cert 4 := (.split 0 680 .leaf (.split 0 720 .leaf (.split 4 202 (.split 0 742 .leaf (.split 4 200 .leaf (.split 0 753 .leaf (.split 4 201 .leaf .leaf)))) .leaf)))
theorem h4rrlrlrrllrrlrrllrrrrlrlrrrrr : Reject b4rrlrlrrllrrlrrllrrrrlrlrrrrr := sound c4rrlrlrrllrrlrrllrrrrlrlrrrrr (by decide +kernel)
theorem h4rrlrlrrllrrlrrllrrrrlrlrrrr : Reject b4rrlrlrrllrrlrrllrrrrlrlrrrr := split b4rrlrlrrllrrlrrllrrrrlrlrrrr 4 199 h4rrlrlrrllrrlrrllrrrrlrlrrrrl h4rrlrlrrllrrlrrllrrrrlrlrrrrr
theorem h4rrlrlrrllrrlrrllrrrrlrlrrr : Reject b4rrlrlrrllrrlrrllrrrrlrlrrr := split b4rrlrlrrllrrlrrllrrrrlrlrrr 0 612 h4rrlrlrrllrrlrrllrrrrlrlrrrl h4rrlrlrrllrrlrrllrrrrlrlrrrr
theorem h4rrlrlrrllrrlrrllrrrrlrlrr : Reject b4rrlrlrrllrrlrrllrrrrlrlrr := split b4rrlrlrrllrrlrrllrrrrlrlrr 4 193 h4rrlrlrrllrrlrrllrrrrlrlrrl h4rrlrlrrllrrlrrllrrrrlrlrrr
theorem h4rrlrlrrllrrlrrllrrrrlrlr : Reject b4rrlrlrrllrrlrrllrrrrlrlr := split b4rrlrlrrllrrlrrllrrrrlrlr 0 509 h4rrlrlrrllrrlrrllrrrrlrlrl h4rrlrlrrllrrlrrllrrrrlrlrr
theorem h4rrlrlrrllrrlrrllrrrrlrl : Reject b4rrlrlrrllrrlrrllrrrrlrl := split b4rrlrlrrllrrlrrllrrrrlrl 4 182 h4rrlrlrrllrrlrrllrrrrlrll h4rrlrlrrllrrlrrllrrrrlrlr
private def b4rrlrlrrllrrlrrllrrrrlrr : Region 4 := cutR b4rrlrlrrllrrlrrllrrrrlr 0 765
private def c4rrlrlrrllrrlrrllrrrrlrr : Cert 4 := (.split 4 182 .leaf (.split 0 1533 (.split 4 193 .leaf (.split 0 1021 (.split 4 199 .leaf (.split 0 875 (.split 0 816 (.split 4 202 (.split 0 790 (.split 4 200 .leaf (.split 0 777 (.split 4 201 .leaf .leaf) (.split 4 201 .leaf .leaf))) .leaf) (.split 0 790 .leaf (.split 4 203 .leaf .leaf))) (.split 4 202 .leaf (.split 0 845 (.split 4 203 .leaf (.split 0 830 (.split 4 204 .leaf .leaf) (.split 4 204 .leaf .leaf))) .leaf))) .leaf)) .leaf)) .leaf))
theorem h4rrlrlrrllrrlrrllrrrrlrr : Reject b4rrlrlrrllrrlrrllrrrrlrr := sound c4rrlrlrrllrrlrrllrrrrlrr (by decide +kernel)
theorem h4rrlrlrrllrrlrrllrrrrlr : Reject b4rrlrlrrllrrlrrllrrrrlr := split b4rrlrlrrllrrlrrllrrrrlr 0 765 h4rrlrlrrllrrlrrllrrrrlrl h4rrlrlrrllrrlrrllrrrrlrr
theorem h4rrlrlrrllrrlrrllrrrrl : Reject b4rrlrlrrllrrlrrllrrrrl := split b4rrlrlrrllrrlrrllrrrrl 4 164 h4rrlrlrrllrrlrrllrrrrll h4rrlrlrrllrrlrrllrrrrlr
private def b4rrlrlrrllrrlrrllrrrrr : Region 4 := cutR b4rrlrlrrllrrlrrllrrrr 3 17
private def c4rrlrlrrllrrlrrllrrrrr : Cert 4 := .leaf
theorem h4rrlrlrrllrrlrrllrrrrr : Reject b4rrlrlrrllrrlrrllrrrrr := sound c4rrlrlrrllrrlrrllrrrrr (by decide +kernel)
theorem h4rrlrlrrllrrlrrllrrrr : Reject b4rrlrlrrllrrlrrllrrrr := split b4rrlrlrrllrrlrrllrrrr 3 17 h4rrlrlrrllrrlrrllrrrrl h4rrlrlrrllrrlrrllrrrrr
theorem h4rrlrlrrllrrlrrllrrr : Reject b4rrlrlrrllrrlrrllrrr := split b4rrlrlrrllrrlrrllrrr 0 381 h4rrlrlrrllrrlrrllrrrl h4rrlrlrrllrrlrrllrrrr
theorem h4rrlrlrrllrrlrrllrr : Reject b4rrlrlrrllrrlrrllrr := split b4rrlrlrrllrrlrrllrr 4 136 h4rrlrlrrllrrlrrllrrl h4rrlrlrrllrrlrrllrrr
theorem h4rrlrlrrllrrlrrllr : Reject b4rrlrlrrllrrlrrllr := split b4rrlrlrrllrrlrrllr 3 16 h4rrlrlrrllrrlrrllrl h4rrlrlrrllrrlrrllrr
theorem h4rrlrlrrllrrlrrll : Reject b4rrlrlrrllrrlrrll := split b4rrlrlrrllrrlrrll 0 189 h4rrlrlrrllrrlrrlll h4rrlrlrrllrrlrrllr
private def b4rrlrlrrllrrlrrlr : Region 4 := cutR b4rrlrlrrllrrlrrl 4 205
private def b4rrlrlrrllrrlrrlrl : Region 4 := cutL b4rrlrlrrllrrlrrlr 0 189
private def c4rrlrlrrllrrlrrlrl : Cert 4 := (.split 3 16 .leaf .leaf)
theorem h4rrlrlrrllrrlrrlrl : Reject b4rrlrlrrllrrlrrlrl := sound c4rrlrlrrllrrlrrlrl (by decide +kernel)
private def b4rrlrlrrllrrlrrlrr : Region 4 := cutR b4rrlrlrrllrrlrrlr 0 189
private def b4rrlrlrrllrrlrrlrrl : Region 4 := cutL b4rrlrlrrllrrlrrlrr 3 16
private def c4rrlrlrrllrrlrrlrrl : Cert 4 := .leaf
theorem h4rrlrlrrllrrlrrlrrl : Reject b4rrlrlrrllrrlrrlrrl := sound c4rrlrlrrllrrlrrlrrl (by decide +kernel)
private def b4rrlrlrrllrrlrrlrrr : Region 4 := cutR b4rrlrlrrllrrlrrlrr 3 16
private def b4rrlrlrrllrrlrrlrrrl : Region 4 := cutL b4rrlrlrrllrrlrrlrrr 4 413
private def b4rrlrlrrllrrlrrlrrrll : Region 4 := cutL b4rrlrlrrllrrlrrlrrrl 0 381
private def c4rrlrlrrllrrlrrlrrrll : Cert 4 := .leaf
theorem h4rrlrlrrllrrlrrlrrrll : Reject b4rrlrlrrllrrlrrlrrrll := sound c4rrlrlrrllrrlrrlrrrll (by decide +kernel)
private def b4rrlrlrrllrrlrrlrrrlr : Region 4 := cutR b4rrlrlrrllrrlrrlrrrl 0 381
private def b4rrlrlrrllrrlrrlrrrlrl : Region 4 := cutL b4rrlrlrrllrrlrrlrrrlr 3 17
private def b4rrlrlrrllrrlrrlrrrlrll : Region 4 := cutL b4rrlrlrrllrrlrrlrrrlrl 4 275
private def b4rrlrlrrllrrlrrlrrrlrlll : Region 4 := cutL b4rrlrlrrllrrlrrlrrrlrll 0 765
private def c4rrlrlrrllrrlrrlrrrlrlll : Cert 4 := .leaf
theorem h4rrlrlrrllrrlrrlrrrlrlll : Reject b4rrlrlrrllrrlrrlrrrlrlll := sound c4rrlrlrrllrrlrrlrrrlrlll (by decide +kernel)
private def b4rrlrlrrllrrlrrlrrrlrllr : Region 4 := cutR b4rrlrlrrllrrlrrlrrrlrll 0 765
private def b4rrlrlrrllrrlrrlrrrlrllrl : Region 4 := cutL b4rrlrlrrllrrlrrlrrrlrllr 4 235
private def b4rrlrlrrllrrlrrlrrrlrllrll : Region 4 := cutL b4rrlrlrrllrrlrrlrrrlrllrl 0 1533
private def b4rrlrlrrllrrlrrlrrrlrllrlll : Region 4 := cutL b4rrlrlrrllrrlrrlrrrlrllrll 4 219
private def b4rrlrlrrllrrlrrlrrrlrllrllll : Region 4 := cutL b4rrlrlrrllrrlrrlrrrlrllrlll 0 1021
private def c4rrlrlrrllrrlrrlrrrlrllrllll : Cert 4 := (.split 4 212 (.split 0 875 (.split 4 208 (.split 0 816 .leaf (.split 0 845 .leaf (.split 4 206 .leaf .leaf))) .leaf) (.split 4 208 (.split 0 942 (.split 0 907 (.split 4 206 .leaf (.split 0 891 (.split 4 207 .leaf .leaf) (.split 4 207 .leaf .leaf))) .leaf) .leaf) (.split 0 942 (.split 4 210 (.split 0 907 .leaf (.split 0 924 .leaf (.split 4 209 .leaf .leaf))) .leaf) (.split 4 210 (.split 0 980 (.split 0 961 (.split 4 209 .leaf .leaf) .leaf) .leaf) (.split 0 980 (.split 0 961 .leaf (.split 4 211 (.split 0 970 .leaf (.split 0 975 .leaf .leaf)) .leaf)) (.split 0 1000 (.split 4 211 .leaf .leaf) (.split 4 211 .leaf .leaf))))))) .leaf)
theorem h4rrlrlrrllrrlrrlrrrlrllrllll : Reject b4rrlrlrrllrrlrrlrrrlrllrllll := sound c4rrlrlrrllrrlrrlrrrlrllrllll (by decide +kernel)
private def b4rrlrlrrllrrlrrlrrrlrllrlllr : Region 4 := cutR b4rrlrlrrllrrlrrlrrrlrllrlll 0 1021
private def c4rrlrlrrllrrlrrlrrrlrllrlllr : Cert 4 := (.split 4 212 .leaf (.split 0 1226 (.split 0 1114 (.split 4 215 (.split 0 1066 (.split 4 213 .leaf (.split 0 1043 .leaf (.split 4 214 .leaf .leaf))) (.split 4 213 .leaf (.split 0 1089 (.split 4 214 .leaf .leaf) (.split 4 214 .leaf .leaf)))) .leaf) (.split 4 215 .leaf (.split 0 1167 (.split 4 217 (.split 0 1140 (.split 4 216 .leaf .leaf) (.split 4 216 .leaf .leaf)) .leaf) (.split 4 217 .leaf (.split 0 1196 (.split 4 218 .leaf .leaf) (.split 4 218 .leaf .leaf)))))) (.split 0 1363 (.split 4 215 .leaf (.split 0 1291 (.split 4 217 .leaf (.split 0 1258 (.split 4 218 .leaf .leaf) .leaf)) .leaf)) .leaf)))
theorem h4rrlrlrrllrrlrrlrrrlrllrlllr : Reject b4rrlrlrrllrrlrrlrrrlrllrlllr := sound c4rrlrlrrllrrlrrlrrrlrllrlllr (by decide +kernel)
theorem h4rrlrlrrllrrlrrlrrrlrllrlll : Reject b4rrlrlrrllrrlrrlrrrlrllrlll := split b4rrlrlrrllrrlrrlrrrlrllrlll 0 1021 h4rrlrlrrllrrlrrlrrrlrllrllll h4rrlrlrrllrrlrrlrrrlrllrlllr
private def b4rrlrlrrllrrlrrlrrrlrllrllr : Region 4 := cutR b4rrlrlrrllrrlrrlrrrlrllrll 4 219
private def b4rrlrlrrllrrlrrlrrrlrllrllrl : Region 4 := cutL b4rrlrlrrllrrlrrlrrrlrllrllr 0 1021
private def c4rrlrlrrllrrlrrlrrrlrllrllrl : Cert 4 := .leaf
theorem h4rrlrlrrllrrlrrlrrrlrllrllrl : Reject b4rrlrlrrllrrlrrlrrrlrllrllrl := sound c4rrlrlrrllrrlrrlrrrlrllrllrl (by decide +kernel)
private def b4rrlrlrrllrrlrrlrrrlrllrllrr : Region 4 := cutR b4rrlrlrrllrrlrrlrrrlrllrllr 0 1021
private def c4rrlrlrrllrrlrrlrrrlrllrllrr : Cert 4 := (.split 4 227 (.split 0 1226 .leaf (.split 4 223 (.split 0 1363 (.split 0 1291 (.split 4 221 (.split 0 1258 .leaf (.split 4 220 .leaf .leaf)) .leaf) (.split 4 221 (.split 0 1326 (.split 4 220 .leaf .leaf) .leaf) (.split 0 1326 .leaf (.split 4 222 .leaf .leaf)))) (.split 0 1443 (.split 4 221 .leaf (.split 0 1402 (.split 4 222 .leaf .leaf) (.split 4 222 .leaf (.split 0 1422 (.split 0 1412 (.split 0 1407 (.split 0 1404 .leaf (.split 0 1405 .leaf (.split 0 1406 .leaf .leaf))) .leaf) .leaf) .leaf)))) .leaf)) (.split 0 1363 .leaf (.split 0 1443 .leaf (.split 4 225 (.split 0 1487 (.split 4 224 .leaf .leaf) (.split 4 224 .leaf .leaf)) .leaf))))) .leaf)
theorem h4rrlrlrrllrrlrrlrrrlrllrllrr : Reject b4rrlrlrrllrrlrrlrrrlrllrllrr := sound c4rrlrlrrllrrlrrlrrrlrllrllrr (by decide +kernel)
theorem h4rrlrlrrllrrlrrlrrrlrllrllr : Reject b4rrlrlrrllrrlrrlrrrlrllrllr := split b4rrlrlrrllrrlrrlrrrlrllrllr 0 1021 h4rrlrlrrllrrlrrlrrrlrllrllrl h4rrlrlrrllrrlrrlrrrlrllrllrr
theorem h4rrlrlrrllrrlrrlrrrlrllrll : Reject b4rrlrlrrllrrlrrlrrrlrllrll := split b4rrlrlrrllrrlrrlrrrlrllrll 4 219 h4rrlrlrrllrrlrrlrrrlrllrlll h4rrlrlrrllrrlrrlrrrlrllrllr
private def b4rrlrlrrllrrlrrlrrrlrllrlr : Region 4 := cutR b4rrlrlrrllrrlrrlrrrlrllrl 0 1533
private def b4rrlrlrrllrrlrrlrrrlrllrlrl : Region 4 := cutL b4rrlrlrrllrrlrrlrrrlrllrlr 4 219
private def c4rrlrlrrllrrlrrlrrrlrllrlrl : Cert 4 := .leaf
theorem h4rrlrlrrllrrlrrlrrrlrllrlrl : Reject b4rrlrlrrllrrlrrlrrrlrllrlrl := sound c4rrlrlrrllrrlrrlrrrlrllrlrl (by decide +kernel)
private def b4rrlrlrrllrrlrrlrrrlrllrlrr : Region 4 := cutR b4rrlrlrrllrrlrrlrrrlrllrlr 4 219
private def b4rrlrlrrllrrlrrlrrrlrllrlrrl : Region 4 := cutL b4rrlrlrrllrrlrrlrrrlrllrlrr 0 3069
private def b4rrlrlrrllrrlrrlrrrlrllrlrrll : Region 4 := cutL b4rrlrlrrllrrlrrlrrrlrllrlrrl 4 227
private def c4rrlrlrrllrrlrrlrrrlrllrlrrll : Cert 4 := (.split 0 2045 (.split 4 223 .leaf (.split 0 1753 (.split 0 1636 (.split 4 225 .leaf (.split 0 1583 (.split 4 226 .leaf .leaf) (.split 4 226 .leaf (.split 0 1609 .leaf (.split 0 1622 .leaf (.split 0 1629 .leaf .leaf)))))) .leaf) .leaf)) .leaf)
theorem h4rrlrlrrllrrlrrlrrrlrllrlrrll : Reject b4rrlrlrrllrrlrrlrrrlrllrlrrll := sound c4rrlrlrrllrrlrrlrrrlrllrlrrll (by decide +kernel)
private def b4rrlrlrrllrrlrrlrrrlrllrlrrlr : Region 4 := cutR b4rrlrlrrllrrlrrlrrrlrllrlrrl 4 227
private def b4rrlrlrrllrrlrrlrrrlrllrlrrlrl : Region 4 := cutL b4rrlrlrrllrrlrrlrrrlrllrlrrlr 0 2045
private def c4rrlrlrrllrrlrrlrrrlrllrlrrlrl : Cert 4 := (.split 0 1753 (.split 4 231 (.split 0 1636 .leaf (.split 4 229 (.split 0 1693 .leaf (.split 4 228 .leaf .leaf)) .leaf)) .leaf) (.split 4 231 (.split 0 1888 (.split 4 229 (.split 0 1818 (.split 4 228 .leaf (.split 0 1785 (.split 0 1769 (.split 0 1761 .leaf (.split 0 1765 .leaf .leaf)) .leaf) .leaf)) .leaf) (.split 0 1818 .leaf (.split 4 230 .leaf .leaf))) (.split 4 229 .leaf (.split 0 1963 (.split 4 230 .leaf .leaf) .leaf))) (.split 0 1888 .leaf (.split 4 233 (.split 0 1963 .leaf (.split 4 232 .leaf .leaf)) .leaf))))
theorem h4rrlrlrrllrrlrrlrrrlrllrlrrlrl : Reject b4rrlrlrrllrrlrrlrrrlrllrlrrlrl := sound c4rrlrlrrllrrlrrlrrrlrllrlrrlrl (by decide +kernel)
private def b4rrlrlrrllrrlrrlrrrlrllrlrrlrr : Region 4 := cutR b4rrlrlrrllrrlrrlrrrlrllrlrrlr 0 2045
private def c4rrlrlrrllrrlrrlrrrlrllrlrrlrr : Cert 4 := (.split 0 2455 (.split 4 231 .leaf (.split 0 2231 (.split 4 233 (.split 0 2134 (.split 4 232 .leaf (.split 0 2089 .leaf (.split 0 2111 (.split 0 2100 .leaf (.split 0 2105 .leaf (.split 0 2108 .leaf .leaf))) .leaf))) .leaf) (.split 0 2134 .leaf (.split 4 234 .leaf .leaf))) (.split 4 233 .leaf (.split 0 2338 (.split 4 234 .leaf .leaf) .leaf)))) .leaf)
theorem h4rrlrlrrllrrlrrlrrrlrllrlrrlrr : Reject b4rrlrlrrllrrlrrlrrrlrllrlrrlrr := sound c4rrlrlrrllrrlrrlrrrlrllrlrrlrr (by decide +kernel)
theorem h4rrlrlrrllrrlrrlrrrlrllrlrrlr : Reject b4rrlrlrrllrrlrrlrrrlrllrlrrlr := split b4rrlrlrrllrrlrrlrrrlrllrlrrlr 0 2045 h4rrlrlrrllrrlrrlrrrlrllrlrrlrl h4rrlrlrrllrrlrrlrrrlrllrlrrlrr
theorem h4rrlrlrrllrrlrrlrrrlrllrlrrl : Reject b4rrlrlrrllrrlrrlrrrlrllrlrrl := split b4rrlrlrrllrrlrrlrrrlrllrlrrl 4 227 h4rrlrlrrllrrlrrlrrrlrllrlrrll h4rrlrlrrllrrlrrlrrrlrllrlrrlr
private def b4rrlrlrrllrrlrrlrrrlrllrlrrr : Region 4 := cutR b4rrlrlrrllrrlrrlrrrlrllrlrr 0 3069
private def c4rrlrlrrllrrlrrlrrrlrllrlrrr : Cert 4 := .leaf
theorem h4rrlrlrrllrrlrrlrrrlrllrlrrr : Reject b4rrlrlrrllrrlrrlrrrlrllrlrrr := sound c4rrlrlrrllrrlrrlrrrlrllrlrrr (by decide +kernel)
theorem h4rrlrlrrllrrlrrlrrrlrllrlrr : Reject b4rrlrlrrllrrlrrlrrrlrllrlrr := split b4rrlrlrrllrrlrrlrrrlrllrlrr 0 3069 h4rrlrlrrllrrlrrlrrrlrllrlrrl h4rrlrlrrllrrlrrlrrrlrllrlrrr
theorem h4rrlrlrrllrrlrrlrrrlrllrlr : Reject b4rrlrlrrllrrlrrlrrrlrllrlr := split b4rrlrlrrllrrlrrlrrrlrllrlr 4 219 h4rrlrlrrllrrlrrlrrrlrllrlrl h4rrlrlrrllrrlrrlrrrlrllrlrr
theorem h4rrlrlrrllrrlrrlrrrlrllrl : Reject b4rrlrlrrllrrlrrlrrrlrllrl := split b4rrlrlrrllrrlrrlrrrlrllrl 0 1533 h4rrlrlrrllrrlrrlrrrlrllrll h4rrlrlrrllrrlrrlrrrlrllrlr
private def b4rrlrlrrllrrlrrlrrrlrllrr : Region 4 := cutR b4rrlrlrrllrrlrrlrrrlrllr 4 235
private def b4rrlrlrrllrrlrrlrrrlrllrrl : Region 4 := cutL b4rrlrlrrllrrlrrlrrrlrllrr 0 1533
private def c4rrlrlrrllrrlrrlrrrlrllrrl : Cert 4 := .leaf
theorem h4rrlrlrrllrrlrrlrrrlrllrrl : Reject b4rrlrlrrllrrlrrlrrrlrllrrl := sound c4rrlrlrrllrrlrrlrrrlrllrrl (by decide +kernel)
private def b4rrlrlrrllrrlrrlrrrlrllrrr : Region 4 := cutR b4rrlrlrrllrrlrrlrrrlrllrr 0 1533
private def b4rrlrlrrllrrlrrlrrrlrllrrrl : Region 4 := cutL b4rrlrlrrllrrlrrlrrrlrllrrr 4 254
private def b4rrlrlrrllrrlrrlrrrlrllrrrll : Region 4 := cutL b4rrlrlrrllrrlrrlrrrlrllrrrl 0 3069
private def c4rrlrlrrllrrlrrlrrrlrllrrrll : Cert 4 := (.split 4 244 (.split 0 2045 .leaf (.split 4 239 (.split 0 2455 .leaf (.split 0 2728 (.split 4 237 (.split 0 2584 (.split 4 236 .leaf .leaf) (.split 4 236 .leaf .leaf)) .leaf) (.split 4 237 .leaf (.split 0 2889 (.split 4 238 .leaf .leaf) (.split 4 238 .leaf (.split 0 2976 (.split 0 2932 (.split 0 2910 .leaf (.split 0 2921 .leaf (.split 0 2926 .leaf .leaf))) .leaf) .leaf)))))) .leaf)) .leaf)
theorem h4rrlrlrrllrrlrrlrrrlrllrrrll : Reject b4rrlrlrrllrrlrrlrrrlrllrrrll := sound c4rrlrlrrllrrlrrlrrrlrllrrrll (by decide +kernel)
private def b4rrlrlrrllrrlrrlrrrlrllrrrlr : Region 4 := cutR b4rrlrlrrllrrlrrlrrrlrllrrrl 0 3069
private def b4rrlrlrrllrrlrrlrrrlrllrrrlrl : Region 4 := cutL b4rrlrlrrllrrlrrlrrrlrllrrrlr 4 244
private def c4rrlrlrrllrrlrrlrrrlrllrrrlrl : Cert 4 := (.split 0 6141 (.split 4 239 .leaf (.split 0 4093 (.split 4 241 (.split 0 3508 (.split 0 3274 (.split 4 240 .leaf .leaf) (.split 4 240 .leaf (.split 0 3387 (.split 0 3330 .leaf (.split 0 3358 (.split 0 3344 .leaf .leaf) .leaf)) .leaf))) .leaf) (.split 0 3508 .leaf (.split 4 242 .leaf (.split 0 3778 .leaf (.split 4 243 .leaf .leaf))))) (.split 4 241 .leaf (.split 0 4912 (.split 4 242 .leaf (.split 0 4465 (.split 4 243 .leaf .leaf) .leaf)) .leaf)))) .leaf)
theorem h4rrlrlrrllrrlrrlrrrlrllrrrlrl : Reject b4rrlrlrrllrrlrrlrrrlrllrrrlrl := sound c4rrlrlrrllrrlrrlrrrlrllrrrlrl (by decide +kernel)
private def b4rrlrlrrllrrlrrlrrrlrllrrrlrr : Region 4 := cutR b4rrlrlrrllrrlrrlrrrlrllrrrlr 4 244
private def b4rrlrlrrllrrlrrlrrrlrllrrrlrrl : Region 4 := cutL b4rrlrlrrllrrlrrlrrrlrllrrrlrr 0 6141
private def c4rrlrlrrllrrlrrlrrrlrllrrrlrrl : Cert 4 := (.split 4 249 (.split 0 4093 .leaf (.split 0 4912 (.split 4 246 (.split 0 4465 .leaf (.split 4 245 .leaf .leaf)) .leaf) (.split 4 246 (.split 0 5458 (.split 4 245 .leaf .leaf) .leaf) (.split 0 5458 .leaf (.split 4 247 .leaf .leaf))))) .leaf)
theorem h4rrlrlrrllrrlrrlrrrlrllrrrlrrl : Reject b4rrlrlrrllrrlrrlrrrlrllrrrlrrl := sound c4rrlrlrrllrrlrrlrrrlrllrrrlrrl (by decide +kernel)
private def b4rrlrlrrllrrlrrlrrrlrllrrrlrrr : Region 4 := cutR b4rrlrlrrllrrlrrlrrrlrllrrrlrr 0 6141
private def b4rrlrlrrllrrlrrlrrrlrllrrrlrrrl : Region 4 := cutL b4rrlrlrrllrrlrrlrrrlrllrrrlrrr 4 249
private def c4rrlrlrrllrrlrrlrrrlrllrrrlrrrl : Cert 4 := (.split 0 12285 (.split 0 8189 (.split 4 246 .leaf (.split 0 7019 (.split 4 247 .leaf (.split 0 6551 (.split 4 248 .leaf .leaf) (.split 4 248 .leaf .leaf))) (.split 4 247 .leaf (.split 0 7559 (.split 4 248 .leaf .leaf) .leaf)))) .leaf) .leaf)
theorem h4rrlrlrrllrrlrrlrrrlrllrrrlrrrl : Reject b4rrlrlrrllrrlrrlrrrlrllrrrlrrrl := sound c4rrlrlrrllrrlrrlrrrlrllrrrlrrrl (by decide +kernel)
private def b4rrlrlrrllrrlrrlrrrlrllrrrlrrrr : Region 4 := cutR b4rrlrlrrllrrlrrlrrrlrllrrrlrrr 4 249
private def b4rrlrlrrllrrlrrlrrrlrllrrrlrrrrl : Region 4 := cutL b4rrlrlrrllrrlrrlrrrlrllrrrlrrrr 0 12285
private def c4rrlrlrrllrrlrrlrrrlrllrrrlrrrrl : Cert 4 := (.split 0 8189 .leaf (.split 4 251 (.split 0 9828 (.split 0 8934 (.split 4 250 .leaf .leaf) (.split 4 250 .leaf .leaf)) (.split 0 10920 (.split 4 250 .leaf (.split 0 10345 .leaf (.split 0 10625 (.split 0 10483 (.split 0 10414 .leaf (.split 0 10448 .leaf (.split 0 10465 (.split 0 10456 (.split 0 10452 (.split 0 10450 .leaf .leaf) .leaf) .leaf) .leaf))) .leaf) .leaf))) .leaf)) .leaf))
theorem h4rrlrlrrllrrlrrlrrrlrllrrrlrrrrl : Reject b4rrlrlrrllrrlrrlrrrlrllrrrlrrrrl := sound c4rrlrlrrllrrlrrlrrrlrllrrrlrrrrl (by decide +kernel)
private def b4rrlrlrrllrrlrrlrrrlrllrrrlrrrrr : Region 4 := cutR b4rrlrlrrllrrlrrlrrrlrllrrrlrrrr 0 12285
private def c4rrlrlrrllrrlrrlrrrlrllrrrlrrrrr : Cert 4 := (.split 0 24573 (.split 4 251 .leaf (.split 0 16381 (.split 4 252 .leaf .leaf) (.split 4 252 .leaf (.split 0 19658 (.split 4 253 .leaf .leaf) (.split 4 253 .leaf .leaf))))) (.split 4 251 .leaf (.split 0 49149 (.split 4 252 .leaf (.split 0 32765 (.split 4 253 .leaf .leaf) .leaf)) .leaf)))
theorem h4rrlrlrrllrrlrrlrrrlrllrrrlrrrrr : Reject b4rrlrlrrllrrlrrlrrrlrllrrrlrrrrr := sound c4rrlrlrrllrrlrrlrrrlrllrrrlrrrrr (by decide +kernel)
theorem h4rrlrlrrllrrlrrlrrrlrllrrrlrrrr : Reject b4rrlrlrrllrrlrrlrrrlrllrrrlrrrr := split b4rrlrlrrllrrlrrlrrrlrllrrrlrrrr 0 12285 h4rrlrlrrllrrlrrlrrrlrllrrrlrrrrl h4rrlrlrrllrrlrrlrrrlrllrrrlrrrrr
theorem h4rrlrlrrllrrlrrlrrrlrllrrrlrrr : Reject b4rrlrlrrllrrlrrlrrrlrllrrrlrrr := split b4rrlrlrrllrrlrrlrrrlrllrrrlrrr 4 249 h4rrlrlrrllrrlrrlrrrlrllrrrlrrrl h4rrlrlrrllrrlrrlrrrlrllrrrlrrrr
theorem h4rrlrlrrllrrlrrlrrrlrllrrrlrr : Reject b4rrlrlrrllrrlrrlrrrlrllrrrlrr := split b4rrlrlrrllrrlrrlrrrlrllrrrlrr 0 6141 h4rrlrlrrllrrlrrlrrrlrllrrrlrrl h4rrlrlrrllrrlrrlrrrlrllrrrlrrr
theorem h4rrlrlrrllrrlrrlrrrlrllrrrlr : Reject b4rrlrlrrllrrlrrlrrrlrllrrrlr := split b4rrlrlrrllrrlrrlrrrlrllrrrlr 4 244 h4rrlrlrrllrrlrrlrrrlrllrrrlrl h4rrlrlrrllrrlrrlrrrlrllrrrlrr
theorem h4rrlrlrrllrrlrrlrrrlrllrrrl : Reject b4rrlrlrrllrrlrrlrrrlrllrrrl := split b4rrlrlrrllrrlrrlrrrlrllrrrl 0 3069 h4rrlrlrrllrrlrrlrrrlrllrrrll h4rrlrlrrllrrlrrlrrrlrllrrrlr
private def b4rrlrlrrllrrlrrlrrrlrllrrrr : Region 4 := cutR b4rrlrlrrllrrlrrlrrrlrllrrr 4 254
private def c4rrlrlrrllrrlrrlrrrlrllrrrr : Cert 4 := (.split 0 3069 .leaf (.split 4 264 (.split 0 6141 .leaf (.split 4 259 (.split 0 12285 .leaf (.split 0 24573 .leaf (.split 4 256 (.split 0 49149 .leaf (.split 0 98301 (.split 4 255 .leaf .leaf) (.split 4 255 .leaf .leaf))) .leaf))) .leaf)) .leaf))
theorem h4rrlrlrrllrrlrrlrrrlrllrrrr : Reject b4rrlrlrrllrrlrrlrrrlrllrrrr := sound c4rrlrlrrllrrlrrlrrrlrllrrrr (by decide +kernel)
theorem h4rrlrlrrllrrlrrlrrrlrllrrr : Reject b4rrlrlrrllrrlrrlrrrlrllrrr := split b4rrlrlrrllrrlrrlrrrlrllrrr 4 254 h4rrlrlrrllrrlrrlrrrlrllrrrl h4rrlrlrrllrrlrrlrrrlrllrrrr
theorem h4rrlrlrrllrrlrrlrrrlrllrr : Reject b4rrlrlrrllrrlrrlrrrlrllrr := split b4rrlrlrrllrrlrrlrrrlrllrr 0 1533 h4rrlrlrrllrrlrrlrrrlrllrrl h4rrlrlrrllrrlrrlrrrlrllrrr
theorem h4rrlrlrrllrrlrrlrrrlrllr : Reject b4rrlrlrrllrrlrrlrrrlrllr := split b4rrlrlrrllrrlrrlrrrlrllr 4 235 h4rrlrlrrllrrlrrlrrrlrllrl h4rrlrlrrllrrlrrlrrrlrllrr
theorem h4rrlrlrrllrrlrrlrrrlrll : Reject b4rrlrlrrllrrlrrlrrrlrll := split b4rrlrlrrllrrlrrlrrrlrll 0 765 h4rrlrlrrllrrlrrlrrrlrlll h4rrlrlrrllrrlrrlrrrlrllr
private def b4rrlrlrrllrrlrrlrrrlrlr : Region 4 := cutR b4rrlrlrrllrrlrrlrrrlrl 4 275
private def c4rrlrlrrllrrlrrlrrrlrlr : Cert 4 := .leaf
theorem h4rrlrlrrllrrlrrlrrrlrlr : Reject b4rrlrlrrllrrlrrlrrrlrlr := sound c4rrlrlrrllrrlrrlrrrlrlr (by decide +kernel)
theorem h4rrlrlrrllrrlrrlrrrlrl : Reject b4rrlrlrrllrrlrrlrrrlrl := split b4rrlrlrrllrrlrrlrrrlrl 4 275 h4rrlrlrrllrrlrrlrrrlrll h4rrlrlrrllrrlrrlrrrlrlr
private def b4rrlrlrrllrrlrrlrrrlrr : Region 4 := cutR b4rrlrlrrllrrlrrlrrrlr 3 17
private def c4rrlrlrrllrrlrrlrrrlrr : Cert 4 := .leaf
theorem h4rrlrlrrllrrlrrlrrrlrr : Reject b4rrlrlrrllrrlrrlrrrlrr := sound c4rrlrlrrllrrlrrlrrrlrr (by decide +kernel)
theorem h4rrlrlrrllrrlrrlrrrlr : Reject b4rrlrlrrllrrlrrlrrrlr := split b4rrlrlrrllrrlrrlrrrlr 3 17 h4rrlrlrrllrrlrrlrrrlrl h4rrlrlrrllrrlrrlrrrlrr
theorem h4rrlrlrrllrrlrrlrrrl : Reject b4rrlrlrrllrrlrrlrrrl := split b4rrlrlrrllrrlrrlrrrl 0 381 h4rrlrlrrllrrlrrlrrrll h4rrlrlrrllrrlrrlrrrlr
private def b4rrlrlrrllrrlrrlrrrr : Region 4 := cutR b4rrlrlrrllrrlrrlrrr 4 413
private def c4rrlrlrrllrrlrrlrrrr : Cert 4 := .leaf
theorem h4rrlrlrrllrrlrrlrrrr : Reject b4rrlrlrrllrrlrrlrrrr := sound c4rrlrlrrllrrlrrlrrrr (by decide +kernel)
theorem h4rrlrlrrllrrlrrlrrr : Reject b4rrlrlrrllrrlrrlrrr := split b4rrlrlrrllrrlrrlrrr 4 413 h4rrlrlrrllrrlrrlrrrl h4rrlrlrrllrrlrrlrrrr
theorem h4rrlrlrrllrrlrrlrr : Reject b4rrlrlrrllrrlrrlrr := split b4rrlrlrrllrrlrrlrr 3 16 h4rrlrlrrllrrlrrlrrl h4rrlrlrrllrrlrrlrrr
theorem h4rrlrlrrllrrlrrlr : Reject b4rrlrlrrllrrlrrlr := split b4rrlrlrrllrrlrrlr 0 189 h4rrlrlrrllrrlrrlrl h4rrlrlrrllrrlrrlrr
theorem h4rrlrlrrllrrlrrl : Reject b4rrlrlrrllrrlrrl := split b4rrlrlrrllrrlrrl 4 205 h4rrlrlrrllrrlrrll h4rrlrlrrllrrlrrlr
private def b4rrlrlrrllrrlrrr : Region 4 := cutR b4rrlrlrrllrrlrr 3 18
private def c4rrlrlrrllrrlrrr : Cert 4 := .leaf
theorem h4rrlrlrrllrrlrrr : Reject b4rrlrlrrllrrlrrr := sound c4rrlrlrrllrrlrrr (by decide +kernel)
theorem h4rrlrlrrllrrlrr : Reject b4rrlrlrrllrrlrr := split b4rrlrlrrllrrlrr 3 18 h4rrlrlrrllrrlrrl h4rrlrlrrllrrlrrr
theorem h4rrlrlrrllrrlr : Reject b4rrlrlrrllrrlr := split b4rrlrlrrllrrlr 0 93 h4rrlrlrrllrrlrl h4rrlrlrrllrrlrr
theorem h4rrlrlrrllrrl : Reject b4rrlrlrrllrrl := split b4rrlrlrrllrrl 4 101 h4rrlrlrrllrrll h4rrlrlrrllrrlr
private def b4rrlrlrrllrrr : Region 4 := cutR b4rrlrlrrllrr 3 21
private def c4rrlrlrrllrrr : Cert 4 := (.split 4 101 (.split 0 93 .leaf (.split 3 26 (.split 4 67 (.split 0 189 .leaf (.split 3 23 (.split 4 57 (.split 0 381 (.split 4 53 (.split 0 253 .leaf (.split 3 22 .leaf .leaf)) .leaf) (.split 4 53 (.split 0 765 (.split 3 22 .leaf .leaf) (.split 3 22 .leaf (.split 4 51 (.split 0 1533 .leaf (.split 0 3069 .leaf (.split 4 50 .leaf .leaf))) .leaf))) (.split 0 765 .leaf (.split 3 22 .leaf .leaf)))) .leaf) .leaf)) .leaf) .leaf)) .leaf)
theorem h4rrlrlrrllrrr : Reject b4rrlrlrrllrrr := sound c4rrlrlrrllrrr (by decide +kernel)
theorem h4rrlrlrrllrr : Reject b4rrlrlrrllrr := split b4rrlrlrrllrr 3 21 h4rrlrlrrllrrl h4rrlrlrrllrrr
theorem h4rrlrlrrllr : Reject b4rrlrlrrllr := split b4rrlrlrrllr 0 45 h4rrlrlrrllrl h4rrlrlrrllrr
theorem h4rrlrlrrll : Reject b4rrlrlrrll := split b4rrlrlrrll 4 49 h4rrlrlrrlll h4rrlrlrrllr
private def b4rrlrlrrlr : Region 4 := cutR b4rrlrlrrl 3 33
private def c4rrlrlrrlr : Cert 4 := (.split 4 49 (.split 0 45 .leaf (.split 3 69 (.split 4 32 .leaf .leaf) .leaf)) .leaf)
theorem h4rrlrlrrlr : Reject b4rrlrlrrlr := sound c4rrlrlrrlr (by decide +kernel)
theorem h4rrlrlrrl : Reject b4rrlrlrrl := split b4rrlrlrrl 3 33 h4rrlrlrrll h4rrlrlrrlr
private def b4rrlrlrrr : Region 4 := cutR b4rrlrlrr 2 5
private def c4rrlrlrrr : Cert 4 := (.split 3 33 (.split 4 49 (.split 0 45 .leaf (.split 3 21 (.split 2 6 .leaf .leaf) .leaf)) .leaf) .leaf)
theorem h4rrlrlrrr : Reject b4rrlrlrrr := sound c4rrlrlrrr (by decide +kernel)
theorem h4rrlrlrr : Reject b4rrlrlrr := split b4rrlrlrr 2 5 h4rrlrlrrl h4rrlrlrrr
theorem h4rrlrlr : Reject b4rrlrlr := split b4rrlrlr 0 21 h4rrlrlrl h4rrlrlrr
theorem h4rrlrl : Reject b4rrlrl := split b4rrlrl 4 23 h4rrlrll h4rrlrlr
private def b4rrlrr : Region 4 := cutR b4rrlr 2 7
private def c4rrlrr : Cert 4 := (.split 4 23 (.split 0 21 .leaf (.split 3 33 (.split 4 15 .leaf .leaf) .leaf)) .leaf)
theorem h4rrlrr : Reject b4rrlrr := sound c4rrlrr (by decide +kernel)
theorem h4rrlr : Reject b4rrlr := split b4rrlr 2 7 h4rrlrl h4rrlrr
theorem h4rrl : Reject b4rrl := split b4rrl 3 15 h4rrll h4rrlr
private def b4rrr : Region 4 := cutR b4rr 2 11
private def c4rrr : Cert 4 := (.split 3 15 (.split 4 23 (.split 2 25 (.split 3 9 .leaf (.split 0 21 .leaf (.split 4 15 (.split 2 16 (.split 3 12 .leaf .leaf) .leaf) .leaf))) .leaf) .leaf) .leaf)
theorem h4rrr : Reject b4rrr := sound c4rrr (by decide +kernel)
theorem h4rr : Reject b4rr := split b4rr 2 11 h4rrl h4rrr
theorem h4r : Reject b4r := split b4r 0 9 h4rl h4rr
theorem root4 : Reject domain4 := split domain4 0 3 h4l h4r
end OMA.Equal245212

/- Recover the increasing list of prime bases of a squarefree power. -/
namespace OMA.Equal245212
open OMA.Smooth245212 OMA.Cube245212 Finset
open scoped ArithmeticFunction.sigma

def init {k : ℕ} (i : Fin (k+1)) : Band :=
  match i.val with
  | 0 => ⟨1,none⟩
  | 1 => ⟨3,some 3⟩
  | 2 => ⟨5,none⟩
  | 3 => ⟨7,none⟩
  | _ => ⟨11,none⟩

private theorem cut_order {k : ℕ} (p : Fin (k+1) → ℕ) (hp : ∀ i,Nat.Prime (p i))
    (odd : ∀ i,Odd (p i)) (mono : StrictMono p) (first : p 0=3) :
    ∀ i, (init (k:=k+1) i.succ).Contains (p i) := by
  have spaced (i : Fin (k+1)) : 2*i.val+3≤p i := by
    induction i using Fin.induction with
    | zero => simp [first]
    | succ j ih =>
      have lt := mono (Fin.castSucc_lt_succ (i:=j))
      obtain ⟨u,hu⟩ := odd j.castSucc
      obtain ⟨v,hv⟩ := odd j.succ
      simp only [Fin.val_castSucc] at ih
      simp only [Fin.val_succ]; omega
  intro i
  rcases i with ⟨n,hn⟩
  have b := spaced ⟨n,hn⟩
  have prime := hp ⟨n,hn⟩
  change 2*n+3≤_ at b
  rcases n with _|_|_|n
  · simpa [init,Band.Contains] using And.intro first.ge first.le
  · simp [init,Band.Contains]; omega
  · simp [init,Band.Contains]; omega
  · have nine : p ⟨n+1+1+1,hn⟩ ≠ 9 := fun h => (by decide : ¬Nat.Prime 9) (h ▸ prime)
    have ten : p ⟨n+1+1+1,hn⟩ ≠ 10 := fun h => (by decide : ¬Nat.Prime 10) (h ▸ prime)
    have step : 11≤p ⟨n+1+1+1,hn⟩ := by omega
    simpa [init,Band.Contains] using step

theorem from_interval (reject : ∀ k : ℕ,0<k → k≤4 → Reject (init (k:=k)))
    {u e : ℕ} (hu : 1<u) (odd : Odd u) (sf : Squarefree u)
    (few : u.primeFactors.card≤4) (he : 0<e) :
    OeisA245212.a (u^e)≠(σ 1 (u^e):ℤ) := by
  intro eq
  let S := u.primeFactors
  have h3 : 3∣u := Nat.prime_three.dvd_of_dvd_pow (three_dvd_odd_of_six
    (one_lt_pow₀ hu he.ne') (odd.pow (n:=e))
    (by rw [Nat.primeFactors_pow _ he.ne']; omega) eq)
  have in3 : 3∈S := Nat.mem_primeFactors.mpr ⟨Nat.prime_three,h3,by omega⟩
  have nonempty := Finset.card_pos.mpr (show S.Nonempty from ⟨3,in3⟩)
  let p := S.orderEmbOfFin rfl
  have pm (i) : p i∈S := orderEmbOfFin_mem S rfl i
  have hp (i) := Nat.prime_of_mem_primeFactors (pm i)
  have op (i) : Odd (p i) :=
    Nat.coprime_two_right.mp (Nat.Coprime.of_dvd_right (Nat.dvd_of_mem_primeFactors (pm i))
      (Nat.coprime_two_left.mpr odd)).symm
  have range3 : 3∈Set.range p := by rw [show Set.range p=(S:Set ℕ) from range_orderEmbOfFin S rfl]; exact in3
  obtain ⟨j,hj⟩ := range3
  have repr : total p (fun _ => e)=u^e := by
    rw [total,Finset.prod_pow]
    congr 1
    exact (Fintype.prod_equiv (S.orderIsoOfFin rfl).toEquiv _ (fun j : S => j.val)
      (fun _ => rfl)).trans ((Finset.prod_coe_sort _ id).trans (Nat.prod_primeFactors_of_squarefree sf))
  have norm := normalized_of_eq p hp p.injective (fun _ => e) (by rw [repr]; exact eq)
  have lift {k : ℕ} (k4 : k≤4) (pos : 0<k) (p : Fin k → ℕ) (j : Fin k) (hj : p j=3)
      (hp : ∀ i,Nat.Prime (p i)) (odd : ∀ i,Odd (p i)) (mono : StrictMono p)
      (norm : normalized p (fun _ => e)=2) : False := by
    cases k with
    | zero => omega
    | succ k =>
      have lower := (hp 0).two_le
      have top := mono.monotone (Fin.zero_le j)
      obtain ⟨a,ha⟩ := odd 0
      have first : p 0=3 := by omega
      let v : Fin ((k+1)+1) → ℕ := Fin.cons (α:=fun _ => ℕ) e p
      have h (i) : (init i).Contains (v i) := by
        refine Fin.cases ?_ (fun t => ?_) i
        · simpa [init,v,Band.Contains] using (show 1≤e by omega)
        · simpa [v] using cut_order p hp odd mono first t
      have neq := reject (k+1) pos k4 v h (by simpa [v] using hp) (by simpa [v] using mono)
      apply neq
      simpa [Value,v,normalized] using norm
  exact lift few nonempty p j hj hp op p.strictMono norm

end OMA.Equal245212

/- An odd squarefree integer on at most four distinct prime factors has no
nontrivial power satisfying the A245212 equality. -/
namespace OMA.Equal245212
open scoped ArithmeticFunction.sigma
theorem no_squarefree_power {u e : ℕ} (hu : 1<u) (odd : Odd u) (sf : Squarefree u)
    (few : u.primeFactors.card≤4) (he : 0<e) :
    OeisA245212.a (u^e)≠(σ 1 (u^e):ℤ) := by
  apply from_interval _ hu odd sf few he
  intro k hk lt
  interval_cases k
  · rw [show init (k:=1)=domain1 by funext i; fin_cases i <;> rfl]; exact root1
  · rw [show init (k:=2)=domain2 by funext i; fin_cases i <;> rfl]; exact root2
  · rw [show init (k:=3)=domain3 by funext i; fin_cases i <;> rfl]; exact root3
  · rw [show init (k:=4)=domain4 by funext i; fin_cases i <;> rfl]; exact root4
end OMA.Equal245212
