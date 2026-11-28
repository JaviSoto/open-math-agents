import FormalConjectures.OEIS.«245212»



/-! An end-to-end proof of the small-exponent sector of OEIS A245212. -/

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

theorem gap {k : ℕ} {P L H p V S R : ℤ} (pp : 0<P) (pv : 0≤V) (ps : 0 ≤ S)
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

/- Integer separation for a dyadic factor, an odd prime power and one
additional odd prime. All polynomial expressions below are over ℤ. -/
namespace OMA.LinearPowerGap245212

/-- The second pole is absent even without assuming its base prime. -/
theorem pole {p b k : ℤ} (hp : 3 ≤ p) (hb : 4 ≤ b) :
    2*b*(p-1)*(p-1-k)+(2*k-(p-1))*p ≠ 0 := by
  intro hit
  let u := p-1
  let d := b*u-p
  have hu : 0<u := by dsimp [u]; omega
  have hd : p<d := by
    dsimp [d,u]
    nlinarith only [hp,hb,mul_nonneg (by omega : 0≤b-4) (by omega : 0≤p-1)]
  have eqn : (2*(k-u))*d=u*p := by
    dsimp [d,u]; linear_combination -hit
  have hmul : 0<u*p := mul_pos hu (by omega)
  have pos : 0<2*(k-u) := (pos_of_mul_pos_left (eqn ▸ hmul) (by omega : 0≤d))
  have div : u ∣ 2*(k-u) := by
    refine ⟨(2*(k-u))*(b-1)-p, ?_⟩
    dsimp [d,u] at eqn ⊢
    linear_combination -eqn
  have hle := Int.le_of_dvd pos div
  nlinarith only [eqn, mul_pos hu (sub_pos.mpr hd),
    mul_nonneg (sub_nonneg.mpr hle) (by omega : 0≤d)]

def intercept (p x b : ℤ) := 2*b*x*(p-1)^2-(p-1)*(x+1)*p
def slope (p x b : ℤ) := b*(p-1)*(2*x+p)-(2*x+1)*p
def residual (p x k : ℤ) := k*(2*x+1)-(p-1)*(x+1)

private theorem divisor {p x b k : ℕ} (hp : p.Prime) (xp : x<p) (hx : 0<x)
    (kp : k+1<p) (hp2 : 2<p)
    (hit : intercept p x b=(k:ℤ)*slope p x b) : p ∣ b := by
  let : Fact p.Prime := ⟨hp⟩
  have h := congrArg (fun z : ℤ => (z : ZMod p)) hit
  simp only [intercept,slope] at h
  push_cast at h
  simp only [ZMod.natCast_self] at h
  have eqn : (b:ZMod p)*(2*(x:ZMod p)*(k+1))=0 := by
    linear_combination h
  have nonzero (n : ℕ) (h₁ : 0<n) (h₂ : n<p) : (n:ZMod p)≠0 := by
    simpa [ZMod.natCast_eq_zero_iff] using (Nat.not_dvd_of_pos_of_lt h₁ h₂)
  have hn : (2*(x:ZMod p)*(k+1))≠0 := by
    apply mul_ne_zero (mul_ne_zero (by exact_mod_cast nonzero 2 (by omega) hp2)
      (nonzero x hx xp))
    exact_mod_cast nonzero (k+1) (by omega) kp
  exact (ZMod.natCast_eq_zero_iff b p).mp ((mul_eq_zero.mp eqn).resolve_right hn)

/-- The exact cleared dyadic equation separates the limiting integer from
zero. In fact the second odd base need only be an integer at least three. -/
theorem gap {p x a k : ℕ} (hp : p.Prime) (hp3 : 3≤p) (hx : 3≤x) (ha : 3≤a)
    (eqn : (p:ℤ)^a * (((2:ℤ)^(k+1)-1)*
      (intercept p x (a+1) - (k:ℤ)*slope p x (a+1)) -
      (k+1)*slope p x (a+1)) =
      ((2:ℤ)^(k+1)-1)*residual p x k+(k+1)*(2*x+1)) :
    intercept p x (a+1) ≠ (k:ℤ)*slope p x (a+1) := by
  intro hit
  let G : ℤ := 2^(k+1)-1
  let B : ℤ := slope p x (a+1)
  let C : ℤ := residual p x k
  have ep : 1<(2:ℤ)^(k+1) := one_lt_pow₀ (by norm_num) (by omega)
  have gpos : 0<G := by dsimp [G]; omega
  have pp : 0<(p:ℤ)^a := by positivity
  have hx' : (3:ℤ)≤x := by exact_mod_cast hx
  have hp' : (3:ℤ)≤p := by exact_mod_cast hp3
  have ha' : (3:ℤ)≤a := by exact_mod_cast ha
  have bu : (p:ℤ)<(a+1)*(p-1) := by
    nlinarith only [ha',hp',mul_nonneg (by omega : (0:ℤ)≤a-3) (by omega : (0:ℤ)≤p-1)]
  have bpos : 0<B := by
    dsimp [B,slope]
    nlinarith only [mul_pos (sub_pos.mpr bu) (by omega : (0:ℤ)<2*x+p),
      mul_pos (by omega : (0:ℤ)<p) (by omega : (0:ℤ)<p-1)]
  have h : (p:ℤ)^a*((k:ℤ)+1)*B+((k:ℤ)+1)*(2*x+1) = -G*C := by
    dsimp [G,B,C]; rw [hit,sub_self,mul_zero,zero_sub] at eqn
    linear_combination -eqn
  have hpos : 0 < (p:ℤ)^a*((k:ℤ)+1)*B+((k:ℤ)+1)*(2*x+1) := by positivity
  have cneg : C<0 := by
    by_contra! hc
    nlinarith only [h,hpos,mul_nonneg gpos.le hc]
  have sep : B*C=((a:ℤ)+1)*(p-1)^2*(2*(x:ℤ)^2-p*(x+1)) := by
    dsimp [B,C,slope,intercept,residual] at hit ⊢
    linear_combination -(2*(x:ℤ)+1)*hit
  have qneg : 2*(x:ℤ)^2<p*(x+1) := by
    have h₁ := mul_neg_of_pos_of_neg bpos cneg
    rw [sep] at h₁
    exact sub_neg.mp (neg_of_mul_neg_right h₁ (by positivity))
  have xp : x<p := by
    by_contra! hxp
    have hp'' : (p:ℤ)≤x := by exact_mod_cast hxp
    nlinarith only [qneg,mul_nonneg (sub_nonneg.mpr hp'') (by positivity : (0:ℤ)≤x+1),
      mul_nonneg (by omega : (0:ℤ)≤x) (by omega : (0:ℤ)≤x-1)]
  have kp : k+1<p := by
    by_contra! hkp
    dsimp [C,residual] at cneg
    have hp'' : (p:ℤ)≤k+1 := by exact_mod_cast hkp
    nlinarith only [cneg,mul_nonneg (by omega : (0:ℤ)≤k-(p-1)) (by omega : (0:ℤ)≤2*x+1),
      mul_nonneg (by omega : (0:ℤ)≤p-1) (by omega : (0:ℤ)≤x)]
  have divis : p ∣ a+1 := divisor hp xp (by omega) kp (by omega) (by exact_mod_cast hit)
  have pa := Nat.le_of_dvd (by omega : 0<a+1) divis
  have hp5 : 5≤p := by
    by_contra! hlt
    have : p=4 := by omega
    subst p; norm_num at hp
  have expPow : 2^(k+1) ≤ p^(a-2) := calc
    2^(k+1) ≤ 2^(2*(p-3)) := Nat.pow_le_pow_right (by decide) (by omega)
    _ = 4^(p-3) := by rw [pow_mul]; norm_num
    _ ≤ p^(p-3) := Nat.pow_le_pow_left (by omega) _
    _ ≤ p^(a-2) := Nat.pow_le_pow_right (by omega) (by omega)
  have pw : (p:ℤ)^2 * (2:ℤ)^(k+1) ≤ (p:ℤ)^a := by
    have hh : (2:ℤ)^(k+1) ≤ (p:ℤ)^(a-2) := by exact_mod_cast expPow
    have mul := mul_le_mul_of_nonneg_left hh (sq_nonneg (p:ℤ))
    rwa [←pow_add,show 2+(a-2)=a by omega] at mul
  have hcx : -C ≤ (p:ℤ)^2 := by
    dsimp [C,residual]
    have xp' : (x:ℤ)<p := by exact_mod_cast xp
    nlinarith only [mul_nonneg (by omega : (0:ℤ)≤p) (by omega : (0:ℤ)≤p-x-1),
      mul_nonneg (by positivity : (0:ℤ)≤k) (by positivity : (0:ℤ)≤2*x+1),hx']
  have gg := mul_le_mul_of_nonneg_left hcx gpos.le
  have bk : (1:ℤ)≤((k:ℤ)+1)*B := by
    nlinarith only [mul_nonneg (by positivity : (0:ℤ)≤k) (by omega : 0≤B),bpos]
  have v := mul_le_mul_of_nonneg_left bk pp.le
  dsimp [G] at gg h
  nlinarith only [pw,h,gg,v,sq_nonneg (p:ℤ),
    mul_pos (by positivity : (0:ℤ)<k+1) (by positivity : (0:ℤ)<2*x+1)]

/-- The cleared equation used in `gap` follows by an integral polynomial
identity from the divisor-moment balance and both local geometric sums. -/
theorem clear (p x b k z P W S : ℤ)
    (weighted : (p-1)*W=b*p*P-S) (geometric : (p-1)*S=p*P-1)
    (balance : (1+k*z)*(2*x+1)*W+(z-1)*(x+1)*S = 2*z*(k+1)*b*P*x) :
    P*((z-1)*(intercept p x b-k*slope p x b)-(k+1)*slope p x b) =
    (z-1)*residual p x k+(k+1)*(2*x+1) := by
  unfold intercept slope residual
  linear_combination -(p-1)^2*balance + (1+k*z)*(2*x+1)*(p-1)*weighted +
    ((p-1)*(z-1)*(x+1)-(1+k*z)*(2*x+1))*geometric

end OMA.LinearPowerGap245212

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

/- Exact scalar comparisons in the finite part of the uniform smaller
exponent bound. No divisor sums, prime tables, or external certificates. -/
namespace OMA.TwoOddEffectiveTable245212

def floorPrime (K m : ℕ) := max 3 (1+(K-1)*(m-1)/m)

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

/- Preserve the two actual bases in the integer complementary-pole estimate. -/
namespace OMA.SmallLength245212
open ArithmeticFunction OMA.Smooth245212 OMA.ComplementaryPole245212 OMA.ComplementaryLocal245212
open OMA.QuadraticPowerGap245212
open scoped ArithmeticFunction.sigma
open OMA.ComplementaryHeight245212 (gap)

theorem separated {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p) (oq : 3≤q)
    (pq : p≠q) (hd : 1≤d) (ha : 2*d+4≤a)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    A p (a+1) (((d:ℤ)+1)*q^d) (σ 1 (q^d)) ≠ (k:ℤ)*H p (a+1) (((d:ℤ)+1)*q^d) (W (q^d)) := by
  by_cases large : 2 ≤ d
  · exact OMA.ComplementaryNonres245212.original hp hq op oq pq large ha eqn
  have one : d=1 := by omega
  subst d
  have sw : (σ 1 q : ℤ) = q+1 := by
    have h := (last hq oq 0).2.1
    norm_num at h
    exact_mod_cast h
  have ww : (W q : ℤ) = 2*q+1 := by
    have h := last hq oq 0
    norm_num at h
    exact_mod_cast h.1
  have ac := OMA.ComplementaryNonres245212.cleared hp hq op oq pq eqn
  simp only [pow_one,Nat.cast_one,sw,ww] at ac ⊢
  have Aeq : A p (a+1) ((1+1)*q) (q+1) = OMA.LinearPowerGap245212.intercept p q (a+1) := by
    unfold A OMA.LinearPowerGap245212.intercept;ring
  have Heq : H p (a+1) ((1+1)*q) (2*q+1) = OMA.LinearPowerGap245212.slope p q (a+1) := by
    unfold H OMA.LinearPowerGap245212.slope;ring
  rw [Aeq,Heq] at ac ⊢
  exact OMA.LinearPowerGap245212.gap hp op oq (by omega) ac

theorem complement {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p) (oq : 3≤q) (pq : p≠q)
    (hd : 1≤d) (ha : 2*d+4≤a)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    2^(k+1)≤1+2*(d+1)*(a+1)*(k+1)*p^2*q^d+
      6*(d+1)^2*(a+1)*(k+1+p)*(q^d)^2 := by
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
  have hh : 2≤h := by dsimp [h];omega
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
    (separated hp hq op oq pq hd ha eqn)
  have lev := OMA.ComplementaryDyad245212.level hp hq op oq pq (by omega) eqn
  have zz : z k≤3*h*b*P*Q := by dsimp [z,h,b,P,Q];exact_mod_cast lev
  have lev' : G k≤P*(3*h*b*Q) := by dsimp [G];linarith only [zz]
  have g := OMA.ComplementaryHeight245212.gap ppos v0 s0 (by omega) Hpos nz clr lev'
  change G k≤K*H0+(3*h*b*Q)*(K*V+p*S) at g
  have vr : V≤2*h*Q := by nlinarith only [vh,mul_nonneg (by omega : 0≤h) qp.le]
  have sr : S≤2*h*Q := by nlinarith only [sh,mul_nonneg (show 0≤h-1 by omega) qp.le,qp.le]
  have Hcap := Hub.trans (mul_le_mul_of_nonneg_left vr (mul_nonneg b0 (sq_nonneg _)))
  have Fcap := mul_le_mul_of_nonneg_left Hcap (by dsimp [K];positivity : 0≤K)
  have Ecap : K*V+p*S≤2*h*(K+p)*Q := by
    nlinarith only [mul_le_mul_of_nonneg_left vr (by dsimp [K];positivity : 0≤K),mul_le_mul_of_nonneg_left sr pz]
  have Rcap := mul_le_mul_of_nonneg_left Ecap (show 0≤3*h*b*Q by positivity)
  have result : z k≤1+2*h*b*K*p^2*Q+6*h^2*b*(K+p)*Q^2 := by
    dsimp only [G] at g
    nlinarith only [g,Rcap,Fcap]
  dsimp only [z,h,b,K,Q] at result
  exact_mod_cast result

end OMA.SmallLength245212

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

/- The fixed-exponent input with the same modular imports as the exterior proof. -/


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

end

section

/- Quantitative bounds for a single linear complementary prime. The base
carrying the large exponent need not be the smaller prime. -/
namespace OMA.SmallLinear245212
open ArithmeticFunction
open scoped ArithmeticFunction.sigma

theorem exponential {C s start : ℕ} (nz : 0<start)
    (first : C*start^s < 2^start) (ratio : (start+1)^s≤2*start^s) :
    ∀ K, start≤K → C*K^s<2^K := by
  intro K hk
  induction K,hk using Nat.le_induction with
  | base => exact first
  | succ n hn ih =>
    have comp : (n+1)*start ≤ (start+1)*n := by nlinarith only [hn]
    have step := Nat.pow_le_pow_left comp s
    simp only [mul_pow] at step
    have limit : (n+1)^s*start^s ≤ (2*n^s)*start^s := calc
      _ ≤ (start+1)^s*n^s := step
      _ ≤ (2*start^s)*n^s := Nat.mul_le_mul_right _ ratio
      _ = _ := by ring
    have r := Nat.le_of_mul_le_mul_right limit (pow_pos nz s)
    rw [pow_succ];nlinarith only [Nat.mul_le_mul_left C r,ih]

theorem parity {p q a k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p)
    (oq : 3≤q) (pq : p≠q)
    (eqn : OeisA245212.a (2^k*p^a*q)=(σ 1 (2^k*p^a*q):ℤ)) : a%4=2 := by
  let primes : Fin 2 → ℕ := ![p,q]
  let exp : Fin 2 → ℕ := ![a,1]
  have pr : ∀ i, (primes i).Prime := by intro i;fin_cases i <;> assumption
  have odd : ∀ i, Odd (primes i) := fun i => (pr i).odd_of_ne_two (by fin_cases i <;> dsimp [primes] <;> omega)
  have inj : Function.Injective primes := by
    intro i j h;fin_cases i <;> fin_cases j <;> simp_all [primes]
  have total : OMA.Smooth245212.total primes exp = p^a*q := by
    simp [OMA.Smooth245212.total,Fin.prod_univ_two,primes,exp]
  have eq := OMA.ExponentParity245212.exponent_product primes exp pr odd inj k (by
    rw [total,←mul_assoc];exact eqn)
  simp [Fin.prod_univ_two, exp] at eq
  omega

theorem dyadic {p q a k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p)
    (oq : 3≤q) (pq : p≠q) (ha : 6≤a)
    (eqn : OeisA245212.a (2^k*p^a*q)=(σ 1 (2^k*p^a*q):ℤ)) : k+1<160 := by
  let K:=k+1
  let b:=a+1
  have eq' : OeisA245212.a (2^k*p^a*q^1)=(σ 1 (2^k*p^a*q^1):ℤ) := by simpa
  have flip : OeisA245212.a (2^k*q^1*p^a)=(σ 1 (2^k*q^1*p^a):ℤ) := by rwa [mul_right_comm]
  have cap := OMA.ComplementaryExp245212.exponent hp hq op oq pq (by decide : 1≤1) eq'
  have bnd : b≤256*K := by simpa [b,K] using cap
  have small := OMA.ComplementaryBase245212.small_prime hp hq op oq pq (by omega : 5≤(a+1)*(1+1)) eq'
  change p≤5*K ∨ q≤5*K at small
  have fin := OMA.SmallLength245212.complement hp hq op oq pq (by decide : 1≤1) (by omega) eq'
  change 2^K≤1+2*(1+1)*b*K*p^2*q^1+6*(1+1)^2*b*(K+p)*(q^1)^2 at fin
  norm_num only [pow_one,show (1+1:ℕ)=2 by rfl,show (2*2:ℕ)=4 by rfl,show (6*2^2:ℕ)=24 by rfl] at fin
  by_contra! h
  change 160≤K at h
  have fast : 2^56*K^12 < 2^K := exponential (by decide : 0<160) (by decide) (by decide) K h
  have hk : 1 ≤ K := by omega
  have cmp {i c : ℕ} (hi : i≤12) (hc : c≤2^56) : c*K^i<2^K :=
    (Nat.mul_le_mul hc (Nat.pow_le_pow_right hk hi)).trans_lt fast
  rcases small with ps | qs
  · have gc : 4*K*2*b*p<2^K := calc
      _ ≤ 4*K*2*(256*K)*(5*K) := by gcongr
      _ = 10240*K^3 := by ring
      _ < _ := cmp (by decide) (by decide)
    have pc : 8*K≤p^a := by
      by_contra! below
      have low := OMA.ComplementaryDyad245212.power_floor hp hq op oq pq (by decide : 1≤1) eq'
      change 2^K≤(6*2*K*b*p^a)^2 at low
      have limit : (6*2*K*b*p^a)^2 ≤ (6*2*K*(256*K)*(8*K))^2 := by gcongr
      have th : (6*2*K*(256*K)*(8*K))^2=603979776*K^6 := by ring
      exact (not_lt_of_ge (low.trans (limit.trans_eq th))) (cmp (by decide) (by decide))
    have qlim := OMA.ComplementaryFar245212.far hp hq op oq pq (by omega) (by decide : 1≤1) eq' gc pc
    have qmax : q ≤ 76800*K^4 := calc
      _ ≤ 6*2*K*b*p^2 := qlim
      _ ≤ 6*2*K*(256*K)*(5*K)^2 := by gcongr
      _ = _ := by ring
    have upper : 1+4*b*K*p^2*q+24*b*(K+p)*q^2 ≤
        1+4*(256*K)*K*(5*K)^2*(76800*K^4)+24*(256*K)*(K+5*K)*(76800*K^4)^2 := by gcongr
    have growth : 1+4*(256*K)*K*(5*K)^2*(76800*K^4)+24*(256*K)*(K+5*K)*(76800*K^4)^2
        ≤ 2^56*K^12 := by
      nlinarith only [Nat.one_le_pow 12 K (by omega),Nat.pow_le_pow_right hk (show 8≤12 by decide),
        Nat.pow_le_pow_right hk (show 10≤12 by decide)]
    exact (not_lt_of_ge (fin.trans (upper.trans growth))) fast
  · have gate : K*(a+1)*(1+1)*q^1<2^K := calc
      _ ≤ K*(256*K)*2*(5*K) := by rw [pow_one];change K*b*2*q≤_;gcongr
      _ = 2560*K^3 := by ring
      _ < _ := cmp (by decide) (by decide)
    have pbound := OMA.ComplementaryDyad245212.near hq hp oq op pq.symm (by omega) flip gate
    have pmax : p≤15360*K^3 := calc
      _ ≤ 6*b*K*2*q^1 := pbound
      _ ≤ 6*(256*K)*K*2*(5*K) := by rw [pow_one];gcongr
      _ = _ := by ring
    have upper : 1+4*b*K*p^2*q+24*b*(K+p)*q^2 ≤
        1+4*(256*K)*K*(15360*K^3)^2*(5*K)+24*(256*K)*(K+15360*K^3)*(5*K)^2 := by gcongr
    have growth : 1+4*(256*K)*K*(15360*K^3)^2*(5*K)+24*(256*K)*(K+15360*K^3)*(5*K)^2
        ≤ 2^56*K^12 := by
      nlinarith only [Nat.one_le_pow 12 K (by omega),Nat.pow_le_pow_right hk (show 9≤12 by decide),
        Nat.pow_le_pow_right hk (show 4≤12 by decide),Nat.pow_le_pow_right hk (show 6≤12 by decide)]
    exact (not_lt_of_ge (fin.trans (upper.trans growth))) fast

def limit (K : ℕ) := 4194304*(2^K)^2*K^5

theorem box {p q a k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p)
    (oq : 3≤q) (pq : p≠q)
    (eqn : OeisA245212.a (2^k*p^a*q)=(σ 1 (2^k*p^a*q):ℤ)) :
    k+1<160 ∧ a%4=2 ∧ p^(a-1)≤limit (k+1) ∧ a≤240 ∧ min p q≤5*(k+1) := by
  let K:=k+1
  let z:ℕ:=2^K
  have res := parity hp hq op oq pq eqn
  have ha : 2≤a := by omega
  have eq' : OeisA245212.a (2^k*p^a*q^1)=(σ 1 (2^k*p^a*q^1):ℤ) := by simpa
  have dy : K<160 := by
    by_cases big : 6≤a
    · exact dyadic hp hq op oq pq big eqn
    have a2 : a=2 := by omega
    subst a
    have odd := ((hp.odd_of_ne_two (by omega)).pow (n:=2)).mul (hq.odd_of_ne_two (by omega))
    have size : 1<p^2*q := by nlinarith only [hp.pos,hq.pos,op,oq,Nat.mul_le_mul_left (p^2) oq]
    have t := (OMA.DivisorHeight245212.effective_box odd size (by simpa only [←mul_assoc] using eqn)).1
    have cp := ((Nat.coprime_primes hp hq).mpr pq).pow_left 2
    have card : (p^2*q).divisors.card=6 := by
      have one : (σ 0) (q^1) = 1+1 := sigma_zero_apply_prime_pow hq
      simp only [pow_one] at one
      rw [←sigma_zero_apply,isMultiplicative_sigma.map_mul_of_coprime cp,
        sigma_zero_apply_prime_pow hp,one]
      decide
    rw [card] at t
    exact lt_of_le_of_lt t (by decide)
  have hk : 1≤K := by dsimp [K];omega
  have hz : 1≤z := Nat.one_le_pow _ _ (by decide)
  have bnd := OMA.ComplementaryExp245212.exponent hp hq op oq pq (by decide : 1≤1) eq'
  change a+1≤256*K at bnd
  have small := OMA.ComplementaryBase245212.small_prime hp hq op oq pq (by omega : 5≤(a+1)*(1+1)) eq'
  change p≤5*K ∨ q≤5*K at small
  have orig := OMA.ComplementaryBase245212.cofactor hp hq op oq pq eq'
  simp only [pow_one] at orig
  change p^a≤4*z*(K+p)*q at orig
  have power : p^(a-1)≤limit K := by
    change p^(a-1)≤4194304*z^2*K^5
    rcases small with ps | qs
    · have alt := OMA.ComplementaryPole245212.alternative hp hq op oq pq a 0 k ha eq'
      change p^a≤2*z*2*K ∨ q≤12*K*(a+1)*z*p^2 at alt
      apply (Nat.pow_le_pow_right hp.pos (Nat.sub_le _ _)).trans
      rcases alt with smallP | upper
      · have cf : 4*z*K^1≤4194304*z^2*K^5 :=
          Nat.mul_le_mul (Nat.mul_le_mul (by decide) (by simpa using Nat.pow_le_pow_right hz (show 1≤2 by decide)))
            (Nat.pow_le_pow_right hk (by decide))
        rw [pow_one] at cf
        exact smallP.trans (by nlinarith only [cf])
      · have bound : 4*z*(K+p)*q≤4*z*(K+5*K)*(12*K*(256*K)*z*(5*K)^2) := by
          apply Nat.mul_le_mul (by gcongr) (upper.trans (by gcongr))
        exact orig.trans (bound.trans (by nlinarith only [Nat.zero_le (z^2*K^5)]))
    · have kp : K+p≤2*K*p := by nlinarith only [Nat.mul_le_mul_left K hp.pos,Nat.mul_le_mul_right p hk]
      have bound : 4*z*(K+p)*q≤4*z*(2*K*p)*(5*K) := by gcongr
      have cancel : p^(a-1)≤40*z*K^2 := by
        apply Nat.le_of_mul_le_mul_right _ hp.pos
        rw [←pow_succ,show a-1+1=a by omega]
        exact orig.trans (bound.trans_eq (by ring))
      exact cancel.trans (Nat.mul_le_mul (Nat.mul_le_mul (by decide)
        (by simpa using Nat.pow_le_pow_right hz (show 1≤2 by decide))) (Nat.pow_le_pow_right hk (by decide)))
  refine ⟨dy,res,power,?_,by omega⟩
  by_contra! big
  have bigger : 3^240≤p^(a-1) :=
    (Nat.pow_le_pow_left op 240).trans (Nat.pow_le_pow_right hp.pos (by omega))
  have cut : limit K≤limit 160 := by unfold limit;gcongr;omega
  exact (not_le_of_gt (by decide : limit 160<3^240)) (bigger.trans (power.trans cut))

end OMA.SmallLinear245212

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

namespace OMA.PairExtension245212
open Nat Finset ArithmeticFunction OMA.Smooth245212 OMA.LastDigit245212 OMA.Large245212
open scoped ArithmeticFunction.sigma


open OMA.Large245212 (moments)

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


end OMA.PairExtension245212

end

section

namespace OMA.PairSweep245212
open Nat Finset ArithmeticFunction OMA.Smooth245212 OMA.Large245212 OMA.PairExtension245212
open scoped ArithmeticFunction.sigma


open OMA.Large245212 (moments)

def run (test : ℕ → ℕ → ℕ → Bool) (k p e : ℕ) :=
  test (wt 2 k*wt p e) (sig 2 k*sig p e) (OMA.Large245212.tax 2 k*OMA.Large245212.tax p e)

theorem run_true {k p e : ℕ} (hp : p.Prime) (po : 2<p) (test : ℕ → ℕ → ℕ → Bool)
    (ok : run test k p e=true) :
    test (W (2^k*p^e)) (σ 1 (2^k*p^e)) ((2^k*p^e)*(σ 0 (2^k*p^e)))=true := by
  have cp := (((Nat.coprime_primes prime_two hp).mpr (by omega)).pow_left k).pow_right e
  rw [w_mult.map_mul_of_coprime cp,isMultiplicative_sigma.map_mul_of_coprime cp,
    isMultiplicative_sigma.map_mul_of_coprime cp,sigma_zero_apply_prime_pow prime_two,
    sigma_zero_apply_prime_pow hp]
  have two := OMA.Large245212.moments prime_two k
  have odd := OMA.Large245212.moments hp e
  simpa [run,two.1,two.2,odd.1,odd.2,OMA.Large245212.tax,mul_comm,mul_assoc,mul_left_comm] using ok


end OMA.PairSweep245212

end

section

/- Sound finite replay for both free odd primes. Each rectangular slice
checks the last base via a single leading-digit division; the actual
prime bases outside the cofactor are never truncated. -/
namespace OMA.RankTwoReplay245212
open Nat ArithmeticFunction OMA.Smooth245212 OMA.Large245212 OMA.LastDigit245212
open scoped ArithmeticFunction.sigma
open OMA.Large245212 (force)
open OMA.PairExtension245212 (fit)
open OMA.PairSweep245212 (run_true)

def excluded (p f A S T : ℕ) : Bool :=
  let D := denom A S T f
  if D=0 then true else
  let q := candidate A S T f
  decide (q≤p) || !OMA.PairExtension245212.permitted A S T q f

theorem leaf {k p e q f : ℕ} (hp : p.Prime) (po : 2<p) (hq : q.Prime) (pq : p<q)
    (fp : 0<f) (ok : OMA.PairSweep245212.run (excluded p f) k p e=true) :
    OeisA245212.a (2^k*p^e*q^f)≠(σ 1 (2^k*p^e*q^f):ℤ) := by
  intro eq
  let b := 2^k*p^e
  have bp : 0<b := by dsimp [b]; have := hp.pos; positivity
  have cop : b.Coprime q :=
    (((Nat.coprime_primes prime_two hq).mpr (by omega)).pow_left k).mul_left
      (((Nat.coprime_primes hp hq).mpr pq.ne).pow_left e)
  obtain ⟨pos,low,high,_⟩ := balance_digits bp hq cop fp eq
  have value := OMA.Large245212.force (sigma_pos 1 b bp.ne') hq.one_lt pos low high
  have r := OMA.PairSweep245212.run_true hp po _ ok
  change excluded p f (W b) (σ 1 b) (b*(σ 0 b))=true at r
  simp [excluded,pos.ne',value,not_le_of_gt pq,OMA.PairExtension245212.fit bp hq cop fp eq] at r

def allIn (lo hi : ℕ) (f : ℕ → Bool) : Bool :=
  (List.range' lo (hi+1-lo)).all f

private theorem member {lo hi n : ℕ} {f : ℕ → Bool} (h : allIn lo hi f=true)
    (l : lo≤n) (u : n≤hi) : f n=true :=
  List.all_eq_true.mp h n (List.mem_range'_1.mpr ⟨l,by omega⟩)

/-- k=powers of two's exponent; e, f are the odd exponents (not lengths). -/
def slice (kl kh pl ph el eh fl fh : ℕ) : Bool :=
  allIn pl ph fun p => !decide p.Prime || allIn kl kh fun k =>
    let w := wt 2 k
    let s := sig 2 k
    let t := OMA.Large245212.tax 2 k
    allIn el eh fun e =>
      let a := w*wt p e
      let o := s*sig p e
      let u := t*OMA.Large245212.tax p e
      allIn fl fh fun f => excluded p f a o u

theorem of_slice {kl kh pl ph el eh fl fh k p e q f : ℕ}
    (hp : p.Prime) (po : 2<p) (hq : q.Prime) (pq : p<q) (fp : 0<f)
    (p₀ : pl≤p) (p₁ : p≤ph) (k₀ : kl≤k) (k₁ : k≤kh)
    (e₀ : el≤e) (e₁ : e≤eh) (f₀ : fl≤f) (f₁ : f≤fh)
    (ok : slice kl kh pl ph el eh fl fh=true) :
    OeisA245212.a (2^k*p^e*q^f)≠(σ 1 (2^k*p^e*q^f):ℤ) := by
  have base := member ok p₀ p₁
  simp only [hp,decide_true,Bool.not_true,Bool.false_or] at base
  have row := member base k₀ k₁
  have exp := member row e₀ e₁
  have point := member exp f₀ f₁
  exact leaf hp po hq pq fp point

end OMA.RankTwoReplay245212

end

section

/- Check both choices of the smaller prime. No bound on the other base is
used: its value is recovered by leading-digit division. -/
namespace OMA.SmallLinearReplay245212
open OMA.Large245212 OMA.RankTwoReplay245212
open scoped ArithmeticFunction.sigma

def row (r k : ℕ) : Bool :=
  let K:=k+1
  let w:=wt 2 k
  let s:=sig 2 k
  let t:=OMA.Large245212.tax 2 k
  let oneA:=w*wt r 1
  let oneS:=s*sig r 1
  let oneT:=t*OMA.Large245212.tax r 1
  let top:=min 59 (Nat.log r (OMA.SmallLinear245212.limit K)/4)
  (List.range (top+1)).all fun j =>
    let a:=4*j+2
    excluded r a oneA oneS oneT &&
      excluded r 1 (w*wt r a) (s*sig r a) (t*OMA.Large245212.tax r a)

def stripe (lo hi : ℕ) := (List.range' lo (hi+1-lo)).all fun r =>
  !decide r.Prime || (List.range' ((r+4)/5-1) (min 159 (2*r)+1-(r+4)/5)).all (row r)

theorem use_stripe {p q a k lo hi : ℕ} (hp : p.Prime) (hq : q.Prime)
    (op : 3 ≤ p) (oq : 3 ≤ q) (pq : p≠q) (lower : lo ≤ min p q) (upper : min p q≤hi)
    (ok : stripe lo hi=true) :
    OeisA245212.a (2^k*p^a*q)≠(σ 1 (2^k*p^a*q):ℤ) := by
  intro eqn
  obtain ⟨K,res,power,endA,small⟩:=OMA.SmallLinear245212.box hp hq op oq pq eqn
  have ha : 1≤a := by omega
  have eq' : OeisA245212.a (2^k*p^a*q^1)=(σ 1 (2^k*p^a*q^1):ℤ) := by simpa
  have flip : OeisA245212.a (2^k*q^1*p^a)=(σ 1 (2^k*q^1*p^a):ℤ) := by rwa [mul_right_comm]
  let r:=min p q
  have r3 : 3≤r := le_min op oq
  have pr : r.Prime := by rcases le_total p q with l|l <;> simp_all [r]
  have Kbound : k<2*r := by
    have pBound := OMA.TwoOddParameters245212.reciprocal hp hq op oq pq ha eq'
    have qBound := OMA.TwoOddParameters245212.reciprocal hq hp oq op pq.symm (by decide : 1≤1) flip
    have pk : k<2*p := by
      by_contra! fail
      nlinarith only [pBound,Nat.mul_le_mul_right a fail,Nat.mul_le_mul_left p ha]
    dsimp [r];omega
  have rpass:=List.all_eq_true.mp ok r (List.mem_range'_1.mpr ⟨lower,by omega⟩)
  simp only [pr,decide_true,Bool.not_true,Bool.false_or] at rpass
  have step:=List.all_eq_true.mp rpass k (List.mem_range'_1.mpr ⟨by dsimp [r] at *;omega,by dsimp [r] at *;omega⟩)
  have rg : r^(a-1)≤OMA.SmallLinear245212.limit (k+1) :=
    (Nat.pow_le_pow_left (min_le_left p q) _).trans power
  have alog := Nat.le_log_of_pow_le (by omega : 1<r) rg
  let j:=a/4
  have ja : 4*j+2=a := by dsimp [j];omega
  have part:=List.all_eq_true.mp step j (List.mem_range.mpr (by dsimp [j];omega))
  simp only [ja,Bool.and_eq_true] at part
  rcases lt_or_gt_of_ne pq with less|more
  · have ln : r=p := min_eq_left less.le
    rw [ln] at part
    exact leaf hp (by omega) hq less (by decide : 0<1) part.2 eq'
  · have ln : r=q := min_eq_right more.le
    rw [ln] at part
    exact leaf hq (by omega) hp more ha part.1 flip

end OMA.SmallLinearReplay245212

end

section

/- No solution of the A245212 divisor equation with a complementary
first-power odd prime, with no restrictions on the other prime or exponents. -/
namespace OMA.SmallLinear245212
open OMA.SmallLinearReplay245212
open scoped ArithmeticFunction.sigma

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
private theorem tables {j : ℕ} (bound : j≤24) :
    stripe (3+32*j) (34+32*j)=true := by
  interval_cases j <;> decide +kernel

theorem closed {p q a k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (op : 3≤p) (oq : 3≤q) (pq : p≠q) :
    OeisA245212.a (2^k*p^a*q)≠(σ 1 (2^k*p^a*q):ℤ) := by
  intro eqn
  have info := box hp hq op oq pq eqn
  let j := (min p q-3)/32
  have r3 : 3 ≤ min p q := le_min op oq
  have rmax : min p q≤795 := by omega
  exact use_stripe hp hq op oq pq (by dsimp [j];omega : 3+32*j ≤ min p q)
    (by dsimp [j];omega : min p q≤34+32*j) (tables (by dsimp [j];omega)) eqn

end OMA.SmallLinear245212

end

section

/- Finite interval bounds uniform in the smaller odd exponent.
The two orientations keep the base of that exponent separate. -/
namespace OMA.SmallCaps245212
open scoped ArithmeticFunction.sigma

def smallCore (d a p q _K b : ℕ) := 3*(d+1)*b*p^a*q^d
def highCore (d p q K b : ℕ) := 1+2*(d+1)*b*K*p^2*q^d+
    6*(d+1)^2*b*(K+p)*(q^d)^2

/-- The three implications bound the unbounded prime with the same
polynomial at every point in the current interval. -/
def caps (d l t : ℕ) (few reversed : Bool) : Bool :=
  let h:=d+1
  let z:=2^(min l 4096)
  let b:=if few then 2*d+4 else 64*h^2*t
  let s:=5*t
  let (test,p,q):=if reversed then
    (decide (t*b*h*s^d<z),6*b*t*h*s^d,s)
    else (decide (4*t*h*b*s<z ∧ (6*h*t*b*(4*h*t))^h<z),s,6*h*t*b*s^2)
  test && decide ((if few then smallCore d (2*d+3) p q t b else highCore d p q t b)<z)

theorem retain {p q a d k l t : ℕ} (hp : p.Prime) (hq : q.Prime)
    (op : 3≤p) (oq : 3≤q) (pq : p≠q) (hd : 2≤d) (order : d≤a)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ))
    (lk : l≤k+1) (hk : k+1≤t) :
    caps d l t (decide (a<2*d+4)) (decide (q<p))=false := by
  let h:=d+1
  let K:=k+1
  let z:ℕ:=2^(min l 4096)
  let b:=if a<2*d+4 then 2*d+4 else 64*h^2*t
  let s:=5*t
  have kz : z≤2^K := Nat.pow_le_pow_right (by decide) ((min_le_left _ _).trans lk)
  have ba : a+1≤b := by
    dsimp only [b];split
    · omega
    · exact (OMA.ComplementaryExp245212.exponent hp hq op oq pq (by omega) eqn).trans
        (Nat.mul_le_mul_left _ hk)
  have many : 5≤(a+1)*(d+1) := by nlinarith only [hd,order,Nat.zero_le (a*d)]
  have small := OMA.ComplementaryBase245212.small_prime hp hq op oq pq many eqn
  have flip : OeisA245212.a (2^k*q^d*p^a)=(σ 1 (2^k*q^d*p^a):ℤ) := by rwa [mul_right_comm]
  have denial (P Q : ℕ) (pmax : p≤P) (qmax : q≤Q) :
      ¬ (if a<2*d+4 then smallCore d (2*d+3) P Q t b else highCore d P Q t b)<z := by
    apply not_lt_of_ge
    apply kz.trans
    split
    · rename_i low
      apply (OMA.ComplementaryDyad245212.level hp hq op oq pq (by omega) eqn).trans
      unfold smallCore
      gcongr <;> omega
    · rename_i high
      apply (OMA.SmallLength245212.complement hp hq op oq pq (by omega) (by omega) eqn).trans
      unfold highCore
      gcongr
  by_contra! yes
  have yes' : caps d l t (decide (a<2*d+4)) (decide (q<p))=true := by simpa using yes
  unfold caps at yes'
  by_cases rev : q<p
  · simp only [if_pos rev,Bool.and_eq_true,decide_eq_true_eq] at yes'
    change t*b*h*s^d<z ∧ _ at yes'
    have qs : q ≤ s := by dsimp [s];omega
    have lim : K*(a+1)*h*q^d<2^K := calc
      _ ≤ t*b*h*s^d := by gcongr
      _ < _ := yes'.1
      _ ≤ _ := kz
    have ps : p≤6*b*t*h*s^d := (OMA.ComplementaryDyad245212.near hq hp oq op pq.symm (by omega) flip lim).trans
      (by change 6*(a+1)*K*h*q^d≤_;gcongr)
    exact denial _ _ ps qs yes'.2
  · simp only [if_neg rev,Bool.and_eq_true,decide_eq_true_eq] at yes'
    change (4*t*h*b*s<z ∧ (6*h*t*b*(4*h*t))^h<z) ∧ _ at yes'
    have ps : p ≤ s := by dsimp [s];omega
    have gc : 4*K*h*(a+1)*p<2^K := calc
      _ ≤ 4*t*h*b*s := by gcongr
      _ < _ := yes'.1.1
      _ ≤ _ := kz
    have pc : 4*h*K≤p^a := by
      by_contra! low
      have pow := OMA.ComplementaryDyad245212.power_floor hp hq op oq pq (by omega) eqn
      change 2^K≤(6*h*K*(a+1)*p^a)^h at pow
      have cmp : (6*h*K*(a+1)*p^a)^h≤(6*h*t*b*(4*h*t))^h := by
        gcongr
        exact low.le.trans (Nat.mul_le_mul_left _ hk)
      exact (not_lt_of_ge (kz.trans (pow.trans cmp))) yes'.1.2
    have qs : q≤6*h*t*b*s^2 :=
      (OMA.ComplementaryFar245212.far hp hq op oq pq (by omega) (by omega) eqn gc pc).trans
        (by change 6*h*K*(a+1)*p^2≤_;gcongr)
    exact denial _ _ ps qs yes'.2

def search : ℕ → ℕ → ℕ → ℕ → Bool → Bool → Bool
  | 0,_,_,_,_,_ => false
  | n+1,d,l,t,f,r =>
    if caps d l t f r then true else
    let mid:=(l+t)/2
    search n d l mid f r && search n d (mid+1) t f r

theorem stays {K d : ℕ} {f r : Bool}
    (keep : ∀ l t, l≤K → K≤t → caps d l t f r=false)
    (n l t : ℕ) (lt : l≤K) (ut : K≤t) : search n d l t f r=false := by
  induction n generalizing l t with
  | zero => rfl
  | succ n ih =>
    rw [search,keep l t lt ut];simp only [Bool.false_eq_true,↓reduceIte]
    by_cases lower : K≤(l+t)/2
    · simp [ih l _ lt lower]
    · simp [ih ((l+t)/2+1) t (by omega) ut]

def ceiling (d : ℕ) (few reversed : Bool) :=
  match d,few,reversed with
  | 2,false,false => 230 | 2,false,true => 137 | 2,true,false => 138 | 2,true,true => 280
  | 3,false,false => 354 | 3,false,true => 174 | 3,true,false => 203 | 3,true,true => 497
  | _,false,false => 485 | _,false,true => 212 | _,true,false => 271 | _,true,true => 779

set_option maxRecDepth 4096 in
set_option maxHeartbeats 16000000 in
private theorem checked {d : ℕ} (lo : 2≤d) (hi : d≤4) (f r : Bool) :
    search 32 d (ceiling d f r+1) (512*(d+1)^4) f r=true := by
  interval_cases d <;> cases f <;> cases r <;> decide +kernel

theorem dyadic {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (op : 3≤p) (oq : 3≤q) (pq : p≠q) (hd : 2≤d) (small : d≤4) (order : d≤a)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    k+1≤ceiling d (decide (a<2*d+4)) (decide (q<p)) := by
  by_contra! big
  have upper := (OMA.ComplementaryFinish245212.exponents hp hq op oq pq hd eqn).1
  have ok := checked hd small (decide (a<2*d+4)) (decide (q<p))
  have no := stays (fun l t => retain hp hq op oq pq hd order eqn (l:=l) (t:=t))
    32 (ceiling d (decide (a<2*d+4)) (decide (q<p))+1) _ big upper
  grind

end OMA.SmallCaps245212

end

section

/- The dyadic box checker uses signed integers in units of a sixteenth
of a binary logarithm. The real interpretation is used only in its proof. -/
namespace OMA.OddBox245212

noncomputable def logSize (x : ℝ) := 16*Real.logb 2 x
def down (n : ℕ) : ℤ := Nat.log 2 (n^16)
def up (n : ℕ) : ℤ := Nat.clog 2 (n^16)
def roundedQuot (n : ℤ) (d : ℕ) := -((-n)/(d:ℤ))

theorem mono {x y : ℝ} (hx : 0<x) (xy : x≤y) : logSize x≤logSize y :=
  mul_le_mul_of_nonneg_left (Real.logb_le_logb_of_le (by norm_num) hx xy) (by norm_num)

theorem reflect {x y : ℝ} (hx : 0<x) (hy : 0<y) : logSize x≤logSize y ↔ x≤y := by
  unfold logSize; rw [mul_le_mul_iff_right₀ (by norm_num : (0:ℝ)<16)]
  exact Real.logb_le_logb (by norm_num) hx hy

theorem enclosed (n : ℕ) (pos : 0<n) : (down n:ℝ)≤logSize n ∧ logSize n≤up n := by
  have x : 0≤Real.logb 2 ((n:ℝ)^16) :=
    Real.logb_nonneg (by norm_num) (one_le_pow₀ (by exact_mod_cast pos : (1:ℝ)≤n))
  have fid := Nat.floor_le x
  have cid := Nat.le_ceil (Real.logb 2 ((n:ℝ)^16))
  have fn := Real.natFloor_logb_natCast 2 (n^16)
  have cn := Real.natCeil_logb_natCast 2 (n^16)
  norm_num only [Nat.cast_ofNat,Nat.cast_pow] at fn cn
  rw [fn] at fid
  rw [cn] at cid
  dsimp [down,up,logSize]
  push_cast at fid cid ⊢
  rw [Real.logb_pow] at fid cid
  norm_num at fid cid
  exact ⟨fid,cid⟩

theorem mul {x y : ℝ} (hx : 0<x) (hy : 0<y) : logSize (x*y)=logSize x+logSize y := by
  simp only [logSize,Real.logb_mul hx.ne' hy.ne',mul_add]
theorem pow (x : ℝ) (n : ℕ) : logSize (x^n)=n*logSize x := by
  simp only [logSize,Real.logb_pow];ring
theorem div {x y : ℝ} (hx : 0<x) (hy : 0<y) : logSize (x/y)=logSize x-logSize y := by
  simp only [logSize,Real.logb_div hx.ne' hy.ne',mul_sub]
@[simp] theorem two : logSize 2=16 := by norm_num [logSize,Real.logb_self_eq_one]
@[simp] theorem one : logSize 1=0 := by simp [logSize]
theorem nat_nonneg (n : ℕ) (hn : 0<n) : 0≤logSize n := by
  simpa using mono (by norm_num : (0:ℝ)<1) (show (1:ℝ)≤n by exact_mod_cast hn)
theorem over_bound {x : ℝ} {a : ℤ} {d : ℕ} (hd : 0<d) (h : (d:ℝ)*x≤a) : x≤roundedQuot a d := by
  have pos : (0:ℤ)<d := by exact_mod_cast hd
  have cut := Int.ediv_mul_le (-a) pos.ne'
  have z : a≤d*roundedQuot a d := by dsimp [roundedQuot];nlinarith only [cut]
  have lift : (a:ℝ)≤(d:ℝ)*(roundedQuot a d:ℝ) := by exact_mod_cast z
  exact (mul_le_mul_iff_right₀ (show (0:ℝ)<d by exact_mod_cast hd)).mp (h.trans lift)

theorem max_sum {x y : ℝ} (hx : 0<x) (hy : 0<y) :
    logSize (x+y)≤16+max (logSize x) (logSize y) := by
  rcases le_total x y with h|h
  · rw [max_eq_right (mono hx h),←two,←mul (by norm_num) hy]
    exact mono (by positivity) (by linarith)
  · rw [max_eq_left (mono hy h),←two,←mul (by norm_num) hx]
    exact mono (by positivity) (by linarith)

end OMA.OddBox245212

end

section

/- Integer exterior tests. Every logarithmic endpoint is measured in
sixteenths of a binary logarithm. The final two endpoints allow either the
entire least-prime interval or any user-supplied subinterval. -/
namespace OMA.OddBox245212

def lowPrime (kl bl pl : ℕ) :=
  let l := max 13 (max pl (1+(kl-1)*(bl-1)/bl))
  l+(1-l%2)

def highPrime (kh ph : ℕ) := min ph (1+9*kh/4)

def compVeto (kl kh bl bh ch : ℕ) (x y : ℤ) : Bool :=
  let fst := up (2*ch*bh*kh)+2*x+(ch-1:ℕ)*y
  let snd := up (6*ch^2*bh)+16+max (up kh) x+2*(ch-1:ℕ)*y
  decide (2*ch+3≤bl ∧ max 0 (max fst snd)+up 3<16*(kl:ℤ))

structure Frame where
  kl : ℕ
  kh : ℕ
  bl : ℕ
  bh : ℕ
  cl : ℕ
  ch : ℕ
  lo : ℕ
  hi : ℕ

namespace Frame

def qlo (f : Frame) := f.lo+2
def xp (f : Frame) := (f.bl-1:ℕ)*down f.lo
def yq (f : Frame) := (f.cl-1:ℕ)*down f.qlo
def dz (f : Frame) : ℤ := 16*f.kh
def dg (f : Frame) : ℤ := 16*(f.kl-1:ℕ)
def cap (f : Frame) := f.dz+up (3*f.kh*f.bh)
def capY (f : Frame) := f.cap+(f.bh-1:ℕ)*up f.hi
def residue (f : Frame) := up (6*f.ch*f.bh*f.kh*f.hi^2)

def y (f : Frame) : ℤ :=
  let upper := roundedQuot f.capY (f.cl-2)
  let near := if f.dz+up (2*f.ch*f.kh)≤f.xp then min upper (f.dz+f.residue) else upper
  if max (up (f.ch*f.kh*f.bh*f.hi)-f.dg) (up (f.ch*f.kh)-f.xp)≤ -32 then
    min near f.residue else near

def normalized (f : Frame) := min (roundedQuot (2*f.cap-(f.cl-4:ℕ)*f.xp) (f.cl-2)) (2*f.y-f.xp)

def e1 (f : Frame) := up (f.kh*f.ch+f.hi)+f.normalized
def e2 (f : Frame) := 2*up f.hi+up (f.kh*f.bh+f.qlo)-f.yq
def e3 (f : Frame) := up (f.kh+f.hi*f.qlo)-f.xp-f.yq
def largest (f : Frame) := max f.e1 (max f.e2 f.e3)
def drift (f : Frame) := up (3*f.kh*f.bh*f.ch)+2*up f.hi+2*f.y-f.dg

def reject (f : Frame) : Bool :=
  decide (f.hi<f.lo ∨ f.capY<(f.cl-2:ℕ)*down f.qlo ∨
    f.cap<((f.cl:ℤ)-f.bh-1)*down f.qlo ∨ f.y<down f.qlo ∨
    f.dz+up (3*f.kh*f.ch)+(f.ch-1:ℕ)*f.y<(f.bl-2:ℕ)*down f.lo ∨
    up (3*f.bh*f.ch)+(f.bh-1:ℕ)*up f.hi+(f.ch-1:ℕ)*f.y<16*(f.kl:ℤ) ∨
    f.largest+up 3+f.dz<0 ∨ max f.largest f.drift+32<0) ||
    compVeto f.kl f.kh f.bl f.bh f.ch (up f.hi) f.y ||
    compVeto f.kl f.kh f.cl f.ch f.bh f.y (up f.hi)

end Frame

def veto (kl kh bl bh cl ch pl ph : ℕ) : Bool :=
  if 6≤kl ∧ 6≤bl ∧ 6≤cl then
    Frame.reject ⟨kl,kh,bl,bh,cl,ch,lowPrime kl bl pl,highPrime kh ph⟩
  else false

end OMA.OddBox245212

end

section

/- Bounds on the least odd prime follow from the two-prime balance. -/

namespace OMA.OddBox245212
open ArithmeticFunction OMA.Smooth245212 OMA.ComplementaryLocal245212 OMA.ComplementaryPole245212
open scoped ArithmeticFunction.sigma

theorem ratio {K G F u D E S T W V : ℤ} (u12 : 12≤u) (gg : 0<G)
    (ff : 0<F) (kg : F≤K*G) (dd : 0<D) (ee : 0<E)
    (wl : D≤W) (vl : E≤V) (wu : u*W≤(u+1)*D) (vu : u*V≤(u+1)*E)
    (ss : 16*S*T≤D*E) (eqn : F*W*V+G*S*T=(F+G)*D*E) : 4*u<9*K := by
  have ww := mul_le_mul wu vu (mul_nonneg (by omega) (ee.le.trans vl))
    (mul_nonneg (by omega) dd.le)
  have sur := mul_le_mul wl vl ee.le (dd.le.trans wl)
  have wz : 0≤W*V-D*E := sub_nonneg.mpr sur
  have upper : u^2*(W*V-D*E)≤(2*u+1)*D*E := by nlinarith only [ww]
  have fst : 15*G*D*E≤16*F*(W*V-D*E) := by
    nlinarith only [eqn,mul_le_mul_of_nonneg_left ss gg.le]
  have limit : (15*u^2)*(G*D*E)≤(16*K*(2*u+1))*(G*D*E) := by
    nlinarith only [mul_le_mul_of_nonneg_left fst (sq_nonneg u),
      mul_le_mul_of_nonneg_left upper (show 0≤16*F by omega),
      mul_le_mul_of_nonneg_right kg (show 0≤16*(2*u+1)*D*E by positivity)]
  have cap := (mul_le_mul_iff_left₀ (mul_pos (mul_pos gg dd) ee)).mp limit
  have kp : 0<K := pos_of_mul_pos_left (ff.trans_le kg) gg.le
  have bound : (180*u)*u≤(400*K)*u := by
    nlinarith only [cap,mul_le_mul_of_nonneg_left (show 12*(2*u+1)≤25*u by omega) (show 0≤16*K by omega)]
  have := (mul_le_mul_iff_left₀ (show 0<u by omega)).mp bound
  omega

theorem prime_bound {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 13≤p)
    (pq : p<q) (ha : 5≤a) (hd : 5≤d)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    4*(p-1)<9*(k+1) := by
  let P : ℤ := (p:ℤ)^a
  let Q : ℤ := (q:ℤ)^d
  let D : ℤ := (a+1)*P
  let E : ℤ := (d+1)*Q
  let W : ℤ := OMA.Smooth245212.W (p^a)
  let V : ℤ := OMA.Smooth245212.W (q^d)
  let S : ℤ := σ 1 (p^a)
  let T : ℤ := σ 1 (q^d)
  let u : ℤ := (p:ℤ)-1
  let v : ℤ := (q:ℤ)-1
  have up : 12≤u := by dsimp [u];omega
  have uv : u≤v := by dsimp [u,v];omega
  have pw := OMA.PrimePowerDiv245212.weighted hp a
  have qw := OMA.PrimePowerDiv245212.weighted hq d
  zify [Nat.cast_sub hp.pos] at pw
  zify [Nat.cast_sub hq.pos] at qw
  change u*W+S=(p:ℤ)*D at pw
  change v*V+T=(q:ℤ)*E at qw
  have wl : D≤W := by dsimp [D,P,W];exact_mod_cast (bounds hp (by omega) a).2.2.1
  have vl : E≤V := by dsimp [E,Q,V];exact_mod_cast (bounds hq (by omega) d).2.2.1
  have ss : 2*S≤3*P := by dsimp [S,P];exact_mod_cast (bounds hp (by omega) a).1
  have tt : 2*T≤3*Q := by dsimp [T,Q];exact_mod_cast (bounds hq (by omega) d).1
  have s0 : 0 ≤ S := by dsimp [S];positivity
  have t0 : 0≤T := by dsimp [T];positivity
  have p0 : 0<P := by dsimp [P];positivity
  have q0 : 0<Q := pow_pos (by omega : (0:ℤ)<q) _
  have vu : u*V≤(u+1)*E := by
    have scale := mul_le_mul_of_nonneg_right uv (sub_nonneg.mpr vl)
    dsimp only [v] at qw scale
    nlinarith only [scale,qw,t0]
  have st := mul_le_mul ss tt (by positivity : 0≤2*T) (by positivity : 0≤3*P)
  have bc := mul_le_mul (show (6:ℤ)≤a+1 by omega) (show (6:ℤ)≤d+1 by omega) (by decide) (by positivity)
  have sm : 16*S*T≤D*E := by dsimp only [D,E];nlinarith only [st,mul_le_mul_of_nonneg_right bc (mul_nonneg p0.le q0.le)]
  have eq := physical hp hq (by omega) (by omega) pq.ne a d k eqn
  change F k*W*V+G k*S*T=z k*(k+1)*(a+1)*(d+1)*P*Q at eq
  rw [←(dyad k).2.2.2] at eq
  have r := ratio up (dyad k).1 (dyad k).2.1 (dyad k).2.2.1
    (by dsimp [D];positivity : 0<D) (by dsimp [E];positivity : 0<E) wl vl
    (by dsimp [u] at pw ⊢;nlinarith only [pw,s0]) vu sm (by dsimp [D,E];linear_combination eq)
  dsimp only [u] at r;zify [Nat.cast_sub hp.pos];exact r

theorem prime_window {p q a d k kl kh bl pl ph : ℕ} (hp : p.Prime) (hq : q.Prime)
    (op : 13≤p) (pq : p<q) (ha : 5≤a) (hd : 5≤d) (lk : kl≤k+1) (uk : k+1≤kh)
    (lb : 1≤bl) (ba : bl≤a+1) (plp : pl≤p) (php : p≤ph)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    lowPrime kl bl pl≤p ∧ p≤highPrime kh ph ∧ lowPrime kl bl pl+2≤q := by
  have lo := OMA.TwoOddParameters245212.floor hp hq (by omega) (by omega) pq.ne (by omega) lb ba eqn
  unfold OMA.TwoOddEffectiveTable245212.floorPrime at lo
  have le : (kl-1)*(bl-1)/bl≤k*(bl-1)/bl :=
    Nat.div_le_div_right (Nat.mul_le_mul_right _ (by omega))
  obtain ⟨i,po⟩ := hp.odd_of_ne_two (by omega)
  obtain ⟨j,qo⟩ := hq.odd_of_ne_two (by omega)
  have small : lowPrime kl bl pl≤p := by
    unfold lowPrime
    simp only [Nat.add_sub_cancel] at lo
    generalize h : max 13 (max pl (1+(kl-1)*(bl-1)/bl))=b
    have b0 : b≤p := by rw [←h];omega
    change b+(1-b%2)≤p
    omega
  have pb := prime_bound hp hq op pq ha hd eqn
  exact ⟨small,by unfold highPrime;omega,by omega⟩

end OMA.OddBox245212

end

section

/- Exact admissibility restrictions at the lower prime and the variable odd exponent. -/
namespace OMA.SmallFacts245212
open ArithmeticFunction OMA.Smooth245212 OMA.ComplementaryLocal245212 OMA.ComplementaryPole245212
open OMA.OddBox245212 (ratio)
open scoped ArithmeticFunction.sigma

private theorem ordered {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 13≤p)
    (pq : p<q) (bc : 36≤(a+1)*(d+1))
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    4*(p-1)<9*(k+1) := by
  let P : ℤ := (p:ℤ)^a
  let Q : ℤ := (q:ℤ)^d
  let D : ℤ := (a+1)*P
  let E : ℤ := (d+1)*Q
  let W : ℤ := OMA.Smooth245212.W (p^a)
  let V : ℤ := OMA.Smooth245212.W (q^d)
  let S : ℤ := σ 1 (p^a)
  let T : ℤ := σ 1 (q^d)
  let u : ℤ := (p:ℤ)-1
  let v : ℤ := (q:ℤ)-1
  have up : 12≤u := by dsimp [u];omega
  have uv : u≤v := by dsimp [u,v];omega
  have pw := OMA.PrimePowerDiv245212.weighted hp a
  have qw := OMA.PrimePowerDiv245212.weighted hq d
  zify [Nat.cast_sub hp.pos] at pw
  zify [Nat.cast_sub hq.pos] at qw
  change u*W+S=(p:ℤ)*D at pw
  change v*V+T=(q:ℤ)*E at qw
  have wl : D≤W := by dsimp [D,P,W];exact_mod_cast (bounds hp (by omega) a).2.2.1
  have vl : E≤V := by dsimp [E,Q,V];exact_mod_cast (bounds hq (by omega) d).2.2.1
  have ss : 2*S≤3*P := by dsimp [S,P];exact_mod_cast (bounds hp (by omega) a).1
  have tt : 2*T≤3*Q := by dsimp [T,Q];exact_mod_cast (bounds hq (by omega) d).1
  have s0 : 0 ≤ S := by dsimp [S];positivity
  have t0 : 0≤T := by dsimp [T];positivity
  have p0 : 0<P := by dsimp [P];positivity
  have q0 : 0<Q := pow_pos (by omega : (0:ℤ)<q) _
  have vu : u*V≤(u+1)*E := by
    have scale := mul_le_mul_of_nonneg_right uv (sub_nonneg.mpr vl)
    dsimp only [v] at qw scale
    nlinarith only [scale,qw,t0]
  have st := mul_le_mul ss tt (by positivity : 0≤2*T) (by positivity : 0≤3*P)
  have bc : (36:ℤ) ≤ ((a:ℤ)+1)*(d+1) := by exact_mod_cast bc
  have sm : 16*S*T≤D*E := by dsimp only [D,E];nlinarith only [st,mul_le_mul_of_nonneg_right bc (mul_nonneg p0.le q0.le)]
  have eq := physical hp hq (by omega) (by omega) pq.ne a d k eqn
  change F k*W*V+G k*S*T=z k*(k+1)*(a+1)*(d+1)*P*Q at eq
  rw [←(dyad k).2.2.2] at eq
  have r := OMA.OddBox245212.ratio up (dyad k).1 (dyad k).2.1 (dyad k).2.2.1
    (by dsimp [D];positivity : 0<D) (by dsimp [E];positivity : 0<E) wl vl
    (by dsimp [u] at pw ⊢;nlinarith only [pw,s0]) vu sm (by dsimp [D,E];linear_combination eq)
  dsimp only [u] at r;zify [Nat.cast_sub hp.pos];exact r


theorem either {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime) (pq : p≠q)
    (op : 13 ≤ min p q) (bc : 36≤(a+1)*(d+1))
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    4*(min p q-1)<9*(k+1) := by
  rcases lt_or_gt_of_ne pq with h|h
  · rw [min_eq_left h.le];exact ordered hp hq (op.trans (min_le_left ..)) h bc eqn
  · rw [min_eq_right h.le]
    exact ordered hq hp (op.trans (min_le_right ..)) h (by rwa [Nat.mul_comm])
      (by rwa [mul_right_comm])

private theorem square_factors {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (op : 3≤p) (oq : 3≤q) (pq : p≠q) (ea : Even a) (ed : Even d)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) : 4∣a := by
  obtain ⟨e,rfl⟩:=ea
  obtain ⟨s,rfl⟩:=ed
  let u:=p^e*q^s
  have ue : p^(e+e)*q^(s+s)=u^2 := by dsimp [u];rw [mul_pow,←pow_mul,←pow_mul];congr 2 <;> omega
  have ou := ((hp.odd_of_ne_two (by omega)).pow (n:=e)).mul ((hq.odd_of_ne_two (by omega)).pow (n:=s))
  rw [mul_assoc,ue] at eqn
  obtain ⟨v,hv⟩:=OMA.DyadicPower245212.square_root_is_square ou eqn
  have notq : ¬p∣q^s := fun div => pq ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow div))
  have exactp : u.factorization p=e := by
    unfold u
    rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hq.ne_zero),
      Finsupp.add_apply,Nat.factorization_pow_self hp,Nat.factorization_eq_zero_of_not_dvd notq,add_zero]
  change u = v*v at hv
  rw [hv,←pow_two,Nat.factorization_pow] at exactp
  simp only [Finsupp.smul_apply,smul_eq_mul] at exactp
  omega

theorem parity {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (op : 3≤p) (oq : 3≤q) (pq : p≠q)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    (d=2 → a%2=1) ∧ (d=3 → a%4=2) ∧ (d=4 → a%4=0) := by
  let primes : Fin 2 → ℕ := ![p,q]
  let exps : Fin 2 → ℕ := ![a,d]
  have pr : ∀ i, (primes i).Prime := by intro i;fin_cases i <;> assumption
  have odd : ∀ i, Odd (primes i) := fun i => (pr i).odd_of_ne_two (by fin_cases i <;> dsimp [primes] <;> omega)
  have inj : Function.Injective primes := by
    intro i j h;fin_cases i <;> fin_cases j <;> simp_all [primes]
  have total : OMA.Smooth245212.total primes exps=p^a*q^d := by
    simp [OMA.Smooth245212.total,Fin.prod_univ_two,primes,exps]
  have eq := OMA.ExponentParity245212.exponent_product primes exps pr odd inj k (by
    rw [total,←mul_assoc];exact eqn)
  simp [Fin.prod_univ_two,exps] at eq
  have flip : OeisA245212.a (2^k*q^d*p^a)=(σ 1 (2^k*q^d*p^a):ℤ) := by rwa [mul_right_comm]
  refine ⟨fun v => ?_,fun v => ?_,fun v => ?_⟩ <;> subst d
  · by_contra! bad
    have ea : Even a := Nat.even_iff.mpr (by omega)
    have := square_factors hq hp oq op pq.symm (by decide : Even 2) ea flip
    omega
  · change 4 ∣ (a+2)*(3+2) at eq
    omega
  · change 4 ∣ (a+2)*(4+2) at eq
    have even : Even a := Nat.even_iff.mpr (by omega)
    exact Nat.dvd_iff_mod_eq_zero.mp (square_factors hp hq op oq pq even (by decide) eqn)

end OMA.SmallFacts245212

end

section

/- A bound depending only on the smaller prime and the dyadic exponent
for the number of powers which the finite replay needs to examine. -/
namespace OMA.SmallExponent245212
open scoped ArithmeticFunction.sigma

def cap (d K r : ℕ) (rev : Bool) : ℕ :=
  let h:=d+1
  let z:=2^K
  let b:=64*h^2*K
  let factor:=3*z*K*h
  if rev then factor*r^d else
  let R:=6*h*K*b*r^2
  if 4*K*h*b*r<z then max (4*h*K) (factor*R^d)
  else max (2*z*h*K) (factor*(z*R)^d)

theorem power {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (op : 3≤p) (oq : 3≤q) (pq : p≠q) (hd : 2≤d) (order : d≤a)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    (min p q)^(a-1)≤cap d (k+1) (min p q) (decide (q<p)) := by
  let K:=k+1
  let h:=d+1
  let z:ℕ:=2^K
  let b:=64*h^2*K
  let R:=6*h*K*b*p^2
  have rle := Nat.pow_le_pow_left (min_le_left p q) (a-1)
  have flip : OeisA245212.a (2^k*q^d*p^a)=(σ 1 (2^k*q^d*p^a):ℤ) := by rwa [mul_right_comm]
  have cp := OMA.TwoOddParameters245212.cofactor hq hp oq op pq.symm (by omega) flip
  change p^(a-1)≤3*z*K*h*q^d at cp
  have ab : a+1≤b := OMA.ComplementaryExp245212.exponent hp hq op oq pq (by omega) eqn
  by_cases rev : q<p
  · simpa [cap,rev,min_eq_right rev.le,h,K,z] using rle.trans cp
  · have le : p≤q := by omega
    simp only [min_eq_left le,cap,decide_eq_true_eq,if_neg rev]
    change p^(a-1) ≤ if 4*K*h*b*p<z then max (4*h*K) (3*z*K*h*R^d) else
        max (2*z*h*K) (3*z*K*h*(z*R)^d)
    split
    · rename_i cut
      by_cases small : p^a<4*h*K
      · exact le_max_of_le_left ((Nat.pow_le_pow_right hp.pos (Nat.sub_le _ _)).trans small.le)
      · have gc : 4*K*h*(a+1)*p<z := lt_of_le_of_lt (by gcongr) cut
        have pc : 4*h*K≤p^a := le_of_not_gt small
        have ub := OMA.ComplementaryFar245212.far hp hq op oq pq (by omega) (by omega) eqn gc pc
        have qr : q≤R := ub.trans (by dsimp [R,K,h];gcongr)
        exact le_max_of_le_right (cp.trans (by gcongr))
    · obtain ⟨e,de⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d≠0)
      have alt := OMA.ComplementaryPole245212.alternative hp hq op oq pq a e k (by omega) (by simpa [de] using eqn)
      have eh : e+2=h := by dsimp [h];omega
      rw [eh] at alt
      rcases alt with direct|upper
      · exact le_max_of_le_left ((Nat.pow_le_pow_right hp.pos (Nat.sub_le _ _)).trans direct)
      · have qr : q≤z*R := by
          apply upper.trans
          calc
            _ ≤ 6*h*K*b*z*p^2 := by dsimp [K,z];gcongr
            _ = _ := by dsimp [R];ring
        exact le_max_of_le_right (cp.trans (by gcongr))

end OMA.SmallExponent245212

end

section

/- Exhaust the allowed residues of the variable exponent. For either
prime order only the smaller prime is enumerated. -/
namespace OMA.SmallReplay245212
open OMA.Large245212 OMA.RankTwoReplay245212 OMA.SmallCaps245212
open scoped ArithmeticFunction.sigma

def first (d : ℕ) (few : Bool) := if few then d else 2*d+4
def stride (d : ℕ) := if d=2 then 2 else 4
def offset (d : ℕ) := if d=2 then 1 else if d=3 then 2 else 0

theorem index_fits {d a b H : ℕ} (lo : 2≤d) (hi : d≤4) (ba : b≤a) (aH : a≤H)
    (par : (d=2 → a%2=1) ∧ (d=3 → a%4=2) ∧ (d=4 → a%4=0)) :
    (b+stride d-1-offset d)/stride d≤a/stride d ∧
    a/stride d≤(H-offset d)/stride d ∧ stride d*(a/stride d)+offset d=a := by
  rcases (show d=2 ∨ d=3 ∨ d=4 by omega) with rfl|rfl|rfl <;> simp [stride,offset] at * <;> omega

def row (d r k : ℕ) (few rev : Bool) : Bool :=
  let K:=k+1
  let low:=first d few
  let baseLen:=(if rev then d else low)+1
  if r<OMA.TwoOddEffectiveTable245212.floorPrime K baseLen ||
      decide (13≤r ∧ 36≤(low+1)*(d+1) ∧ 9*K≤4*(r-1)) then true else
  let high:=if few then 2*d+3 else 1+Nat.log r (OMA.SmallExponent245212.cap d K r rev)
  let start:=(low+stride d-1-offset d)/stride d
  let hi:=(high-offset d)/stride d
  let w:=wt 2 k
  let s:=sig 2 k
  let t:=OMA.Large245212.tax 2 k
  let fixedA:=w*wt r d
  let fixedS:=s*sig r d
  let fixedT:=t*OMA.Large245212.tax r d
  (List.range' start (hi+1-start)).all fun j =>
    let a:=stride d*j+offset d
    if rev then excluded r a fixedA fixedS fixedT else
      excluded r d (w*wt r a) (s*sig r a) (t*OMA.Large245212.tax r a)

def stripe (d : ℕ) (few rev : Bool) (lo hi : ℕ) :=
  (List.range' lo (hi+1-lo)).all fun r =>
  !decide r.Prime || (List.range' ((r+4)/5-1) (ceiling d few rev+1-(r+4)/5)).all
    (fun k => row d r k few rev)

theorem use_stripe {p q a d k lo hi : ℕ} (hp : p.Prime) (hq : q.Prime)
    (op : 3 ≤ p) (oq : 3 ≤ q) (pq : p≠q) (hd : 2≤d) (ed : d≤4) (order : d≤a)
    (lower : lo ≤ min p q) (upper : min p q≤hi)
    (ok : stripe d (decide (a<2*d+4)) (decide (q<p)) lo hi=true)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) : False := by
  let r:=min p q
  let f:=decide (a<2*d+4)
  let v:=decide (q<p)
  let b:=first d f
  let low:=(if v then d else b)+1
  have r3 : 3≤r := le_min op oq
  have pr : r.Prime := by rcases le_total p q with l|l <;> simp_all [r]
  have ba : b≤a := by by_cases c : a<2*d+4 <;> simp [b,first,f,c] <;> omega
  have small := OMA.ComplementaryBase245212.small_prime hp hq op oq pq (by nlinarith only [hd,order,Nat.zero_le (a*d)] : 5≤(a+1)*(d+1)) eqn
  have dy := OMA.SmallCaps245212.dyadic hp hq op oq pq hd ed order eqn
  have par := OMA.SmallFacts245212.parity hp hq op oq pq eqn
  have flip : OeisA245212.a (2^k*q^d*p^a)=(σ 1 (2^k*q^d*p^a):ℤ) := by rwa [mul_right_comm]
  have cut : OMA.TwoOddEffectiveTable245212.floorPrime (k+1) low≤r := by
    dsimp [low,v,r]
    split
    · rename_i rev
      have smaller : q<p := by simpa using rev
      rw [min_eq_right smaller.le]
      exact OMA.TwoOddParameters245212.floor hq hp oq op pq.symm (by omega) (by omega) le_rfl flip
    · rename_i rev
      have smaller : p≤q := by simpa using rev
      rw [min_eq_left smaller]
      exact OMA.TwoOddParameters245212.floor hp hq op oq pq (by omega) (by omega) (by omega) eqn
  have wide : ¬(13≤r ∧ 36≤(b+1)*(d+1) ∧ 9*(k+1)≤4*(r-1)) := by
    rintro ⟨room,size,bad⟩
    have h:=OMA.SmallFacts245212.either hp hq pq room (size.trans (Nat.mul_le_mul_right _ (by omega))) eqn
    omega
  have rpass := List.all_eq_true.mp ok r (List.mem_range'_1.mpr ⟨lower,by omega⟩)
  simp only [pr,decide_true,Bool.not_true,Bool.false_or] at rpass
  have rowpass := List.all_eq_true.mp rpass k (List.mem_range'_1.mpr ⟨by dsimp [r] at *;omega,by dsimp [r] at *;omega⟩)
  change row d r k f v=true at rowpass
  unfold row at rowpass
  have rn : ¬r<OMA.TwoOddEffectiveTable245212.floorPrime (k+1) low := not_lt_of_ge cut
  change (if (decide (r<OMA.TwoOddEffectiveTable245212.floorPrime (k+1) low) || decide (13≤r ∧ 36≤(b+1)*(d+1) ∧ 9*(k+1)≤4*(r-1))) then _ else _)=true at rowpass
  simp only [rn,wide,decide_false,Bool.false_or,Bool.false_eq_true,↓reduceIte] at rowpass
  let H:=if f then 2*d+3 else 1+Nat.log r (OMA.SmallExponent245212.cap d (k+1) r v)
  let j:=a/stride d
  have aH : a≤H := by
    by_cases few : a<2*d+4
    · simp [H,f,few];omega
    · simp only [H,f,few,decide_false,Bool.false_eq_true,↓reduceIte]
      have pw:=OMA.SmallExponent245212.power hp hq op oq pq hd order eqn
      have e:=Nat.le_log_of_pow_le (by omega : 1<r) pw
      change a-1≤Nat.log r (OMA.SmallExponent245212.cap d (k+1) r v) at e
      omega
  have idx : (b+stride d-1-offset d)/stride d≤j ∧ j≤(H-offset d)/stride d ∧ stride d*j+offset d=a := by
    exact index_fits hd ed ba aH par
  have point:=List.all_eq_true.mp rowpass j (List.mem_range'_1.mpr ⟨idx.1,by dsimp [H,b] at *;omega⟩)
  simp only [idx.2.2] at point
  by_cases rev : q<p
  · have qv : v=true := by simp [v,rev]
    have rq : r=q := min_eq_right rev.le
    simp only [qv,↓reduceIte,rq] at point
    exact leaf hq (by omega) hp rev (by omega) point flip
  · have qv : v=false := by simp [v,rev]
    have rp : r=p := min_eq_left (by omega)
    simp only [qv,Bool.false_eq_true,↓reduceIte,rp] at point
    exact leaf hp (by omega) hq (by omega) (by omega) point eqn

end OMA.SmallReplay245212

end

section

/- A least-prime bound retaining the deficit in each weighted
prime-power divisor sum. It applies without lower bounds on the primes
beyond oddness and does not require many odd divisors. -/
namespace OMA.SmallLeast245212
open ArithmeticFunction OMA.Smooth245212 OMA.ComplementaryLocal245212 OMA.ComplementaryPole245212
open scoped ArithmeticFunction.sigma

private theorem local_upper {p : ℕ} (hp : p.Prime) (op : 3≤p) (a : ℕ) {r : ℤ}
    (rp : r≤p) :
    (r-1)*(σ 1 (p^a):ℤ) ≤ r*p^a ∧
    (r-1)*(W (p^a):ℤ) ≤ (((a:ℤ)+1)*r-1)*p^a := by
  let P:ℤ:=(p:ℤ)^a
  let S:ℤ:=σ 1 (p^a)
  let V:ℤ:=W (p^a)
  let b:ℤ:=(a:ℤ)+1
  have geo : ((p:ℤ)-1)*S=p*P-1 := (moments hp a).1
  have w := OMA.PrimePowerDiv245212.weighted hp a
  zify [Nat.cast_sub hp.pos] at w
  change ((p:ℤ)-1)*V+S=p*(b*P) at w
  have positive : 0<P := pow_pos (by omega : (0:ℤ)<p) a
  have sl : P≤S := by
    apply (mul_le_mul_iff_right₀ (by omega : 0<(p:ℤ)-1)).mp
    nlinarith only [geo,positive]
  have wl : b*P≤V := by dsimp [b,P,V];exact_mod_cast (bounds hp op a).2.2.1
  change (r-1)*S≤r*P ∧ (r-1)*V≤(b*r-1)*P
  constructor
  · nlinarith only [geo,mul_nonneg (sub_nonneg.mpr rp) (sub_nonneg.mpr sl)]
  · nlinarith only [w,sl,mul_nonneg (sub_nonneg.mpr rp) (sub_nonneg.mpr wl)]

private theorem scalar {r b h m K F G : ℤ} (rr : 1≤r) (bb : 1≤b) (hh : 1≤h)
    (mm : 1 ≤ m) (mb : m≤b) (kk : 0≤K) (gg : 0<G) (fk : F≤K*G)
    (eqn : (F+G)*b*h*(r-1)^2 ≤ F*(b*r-1)*(h*r-1)+G*r^2) :
    (m*h-1)*r ≤ m*(2*h+K*(2*h-1)) := by
  have diff : 0 ≤ (b*r-1)*(h*r-1)-b*h*(r-1)^2 := by
    have u:=mul_le_mul (show b*(r-1)≤b*r-1 by nlinarith only [bb])
      (show h*(r-1)≤h*r-1 by nlinarith only [hh])
      (mul_nonneg (by omega) (by omega)) (by nlinarith only [mul_nonneg (by omega : 0≤b) (by omega : 0≤r-1),bb])
    nlinarith only [u]
  have limit : b*h*(r-1)^2-r^2 ≤ K*((b*r-1)*(h*r-1)-b*h*(r-1)^2) := by
    apply (mul_le_mul_iff_right₀ gg).mp
    nlinarith only [eqn,mul_le_mul_of_nonneg_right fk diff]
  have large : (b*h-1)*r ≤ b*(2*h+K*(2*h-1)) := by
    apply (mul_le_mul_iff_left₀ (by omega : 0<r)).mp
    have bh : 1≤b*h := by nlinarith only [mul_nonneg (show 0≤b-1 by omega) (show 0≤h-1 by omega),bb,hh]
    nlinarith only [limit, mul_nonneg kk (by omega : 0≤b*h-1),
      mul_nonneg (mul_nonneg kk (by omega : 0≤h)) (by omega : 0≤r),bh]
  apply (mul_le_mul_iff_right₀ (by omega : 0<b)).mp
  nlinarith only [mul_le_mul_of_nonneg_left large (by omega : 0 ≤ m),
    mul_nonneg (sub_nonneg.mpr mb) (by omega : 0≤r)]

theorem bound {p q a d k M : ℕ} (hp : p.Prime) (hq : q.Prime)
    (op : 3≤p) (oq : 3≤q) (pq : p≠q) (mh : 1≤M) (mb : M≤a+1)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    (M*(d+1)-1)*min p q ≤ M*(2*(d+1)+(k+1)*(2*(d+1)-1)) := by
  let r:ℤ:=min p q
  let b:ℤ:=(a:ℤ)+1
  let h:ℤ:=(d:ℤ)+1
  let P:ℤ:=(p:ℤ)^a
  let Q:ℤ:=(q:ℤ)^d
  have rr : 3≤r := by dsimp [r];exact_mod_cast le_min op oq
  have r₁ : r≤p := by dsimp [r];exact_mod_cast min_le_left p q
  have r₂ : r≤q := by dsimp [r];exact_mod_cast min_le_right p q
  have up:=local_upper hp op a r₁
  have uq:=local_upper hq oq d r₂
  have gp := (dyad k).1
  have fp := (dyad k).2.1
  have Ppos : 0<P := pow_pos (by omega : (0:ℤ)<p) _
  have Qpos : 0<Q := pow_pos (by omega : (0:ℤ)<q) _
  have b1 : 1≤b := by dsimp [b];omega
  have h1 : 1≤h := by dsimp [h];omega
  have wu := mul_le_mul up.2 uq.2 (mul_nonneg (by omega) (by positivity))
    (mul_nonneg (by nlinarith only [mul_nonneg (by omega : 0≤b) (by omega : 0≤r-1),b1] : 0≤b*r-1) Ppos.le)
  have su := mul_le_mul up.1 uq.1 (mul_nonneg (by omega) (by positivity)) (mul_nonneg (by omega : 0≤r) Ppos.le)
  have phy := physical hp hq (by omega) (by omega) pq a d k eqn
  change F k*_*_+G k*_*_=z k*(k+1)*b*h*P*Q at phy
  rw [←(dyad k).2.2.2] at phy
  have ratio : (F k+G k)*b*h*(r-1)^2 ≤ F k*(b*r-1)*(h*r-1)+G k*r^2 := by
    apply (mul_le_mul_iff_left₀ (mul_pos Ppos Qpos)).mp
    change (r-1)*_*((r-1)*_) ≤ ((b*r-1)*P)*((h*r-1)*Q) at wu
    change (r-1)*_*((r-1)*_) ≤ (r*P)*(r*Q) at su
    nlinarith only [congrArg (fun x:ℤ=>x*(r-1)^2) phy,
      mul_le_mul_of_nonneg_left wu fp.le,mul_le_mul_of_nonneg_left su gp.le]
  have ans := scalar (by omega : 1≤r) b1 h1 (by exact_mod_cast mh : (1:ℤ)≤M)
    (by dsimp [b];exact_mod_cast mb) (by positivity : (0:ℤ)≤k+1) gp (dyad k).2.2.1 ratio
  dsimp [b,h,r] at ans
  zify [show 1≤M*(d+1) by nlinarith only [mh,Nat.zero_le (M*d)],show 1≤2*(d+1) by omega]
  exact ans

end OMA.SmallLeast245212

end

section

/- Jump to the admissible dyadic interval before testing the variable exponent. -/
namespace OMA.SmallFastReplay245212
open OMA.Large245212 OMA.RankTwoReplay245212 OMA.SmallCaps245212 OMA.SmallReplay245212
open OMA.SmallReplay245212 (index_fits)
open scoped ArithmeticFunction.sigma

def beginAt (d b r : ℕ) := ((b*(d+1)-1)*r-2*b*(d+1)-1)/(b*(2*(d+1)-1))

private theorem enter {d b r k : ℕ} (_r3 : 3≤r) (bh : 1≤b) (_hd : 2≤d)
    (h : (b*(d+1)-1)*r≤b*(2*(d+1)+(k+1)*(2*(d+1)-1))) : beginAt d b r≤k := by
  have hp : 0<b*(2*(d+1)-1) := Nat.mul_pos (by omega) (by omega)
  have h' : (b*(d+1)-1)*r≤2*b*(d+1)+(k+1)*(b*(2*(d+1)-1)) := by nlinarith only [h]
  unfold beginAt
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul hp).mpr
  change (b*(d+1)-1)*r-2*b*(d+1)-1 < (k+1)*(b*(2*(d+1)-1))
  have pos : 0<(k+1)*(b*(2*(d+1)-1)) := Nat.mul_pos (Nat.succ_pos _) hp
  omega

private theorem leave {e K r : ℕ} (he : 0<e)
    (h : OMA.TwoOddEffectiveTable245212.floorPrime (K+1) (e+1)≤r) : K<r*(e+1)/e+1 := by
  unfold OMA.TwoOddEffectiveTable245212.floorPrime at h
  simp only [Nat.add_sub_cancel,max_le_iff] at h
  have ht := (Nat.div_lt_iff_lt_mul (Nat.succ_pos e)).mp (by omega : K*e/(e+1)<r)
  have cut := (Nat.le_div_iff_mul_le he).mpr ht.le
  exact Nat.lt_succ_of_le cut

def stripe (d : ℕ) (few rev : Bool) (lo hi : ℕ) :=
  (List.range' lo (hi+1-lo)).all fun r =>
    let b:=first d few
    let e:=if rev then d else b
    let start:=beginAt d (b+1) r
    let top:=min (ceiling d few rev) (r*(e+1)/e+1)
    !decide r.Prime || (List.range' start (top-start)).all (fun k => row d r k few rev)

theorem use_stripe {p q a d k lo hi : ℕ} (hp : p.Prime) (hq : q.Prime)
    (op : 3 ≤ p) (oq : 3 ≤ q) (pq : p≠q) (hd : 2≤d) (ed : d≤4) (order : d≤a)
    (lower : lo ≤ min p q) (upper : min p q≤hi)
    (ok : stripe d (decide (a<2*d+4)) (decide (q<p)) lo hi=true)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) : False := by
  let r:=min p q
  let f:=decide (a<2*d+4)
  let v:=decide (q<p)
  let b:=first d f
  let low:=(if v then d else b)+1
  have r3 : 3≤r := le_min op oq
  have pr : r.Prime := by rcases le_total p q with l|l <;> simp_all [r]
  have ba : b≤a := by by_cases c : a<2*d+4 <;> simp [b,first,f,c] <;> omega
  have small := OMA.ComplementaryBase245212.small_prime hp hq op oq pq (by nlinarith only [hd,order,Nat.zero_le (a*d)] : 5≤(a+1)*(d+1)) eqn
  have dy := OMA.SmallCaps245212.dyadic hp hq op oq pq hd ed order eqn
  have par := OMA.SmallFacts245212.parity hp hq op oq pq eqn
  have flip : OeisA245212.a (2^k*q^d*p^a)=(σ 1 (2^k*q^d*p^a):ℤ) := by rwa [mul_right_comm]
  have cut : OMA.TwoOddEffectiveTable245212.floorPrime (k+1) low≤r := by
    dsimp [low,v,r]
    split
    · rename_i rev
      have smaller : q<p := by simpa using rev
      rw [min_eq_right smaller.le]
      exact OMA.TwoOddParameters245212.floor hq hp oq op pq.symm (by omega) (by omega) le_rfl flip
    · rename_i rev
      have smaller : p≤q := by simpa using rev
      rw [min_eq_left smaller]
      exact OMA.TwoOddParameters245212.floor hp hq op oq pq (by omega) (by omega) (by omega) eqn
  have wide : ¬(13≤r ∧ 36≤(b+1)*(d+1) ∧ 9*(k+1)≤4*(r-1)) := by
    rintro ⟨room,size,bad⟩
    have h:=OMA.SmallFacts245212.either hp hq pq room (size.trans (Nat.mul_le_mul_right _ (by omega))) eqn
    omega
  have rpass := List.all_eq_true.mp ok r (List.mem_range'_1.mpr ⟨lower,by omega⟩)
  simp only [pr,decide_true,Bool.not_true,Bool.false_or] at rpass
  have bh : 1≤b := by dsimp [b,first];split <;> omega
  have nh := OMA.SmallLeast245212.bound hp hq op oq pq (Nat.succ_pos b) (Nat.add_le_add_right ba 1) eqn
  change ((b+1)*(d+1)-1)*r ≤ (b+1)*(2*(d+1)+(k+1)*(2*(d+1)-1)) at nh
  have lowerK := enter (d:=d) r3 (Nat.succ_pos b) (by omega) nh
  have ul := leave (K:=k) (e:=if v then d else b) (r:=r) (by split <;> omega) cut
  have ur : k < min (ceiling d f v) (r*((if v then d else b)+1)/(if v then d else b)+1) := lt_min (by exact dy) ul
  have rowpass := List.all_eq_true.mp rpass k (List.mem_range'_1.mpr ⟨lowerK,by change k<beginAt d (b+1) r+(min (ceiling d f v) (r*((if v then d else b)+1)/(if v then d else b)+1)-beginAt d (b+1) r);omega⟩)
  change row d r k f v=true at rowpass
  unfold row at rowpass
  have rn : ¬r<OMA.TwoOddEffectiveTable245212.floorPrime (k+1) low := not_lt_of_ge cut
  change (if (decide (r<OMA.TwoOddEffectiveTable245212.floorPrime (k+1) low) || decide (13≤r ∧ 36≤(b+1)*(d+1) ∧ 9*(k+1)≤4*(r-1))) then _ else _)=true at rowpass
  simp only [rn,wide,decide_false,Bool.false_or,Bool.false_eq_true,↓reduceIte] at rowpass
  let H:=if f then 2*d+3 else 1+Nat.log r (OMA.SmallExponent245212.cap d (k+1) r v)
  let j:=a/stride d
  have aH : a≤H := by
    by_cases few : a<2*d+4
    · simp [H,f,few];omega
    · simp only [H,f,few,decide_false,Bool.false_eq_true,↓reduceIte]
      have pw:=OMA.SmallExponent245212.power hp hq op oq pq hd order eqn
      have e:=Nat.le_log_of_pow_le (by omega : 1<r) pw
      change a-1≤Nat.log r (OMA.SmallExponent245212.cap d (k+1) r v) at e
      omega
  have idx : (b+stride d-1-offset d)/stride d≤j ∧ j≤(H-offset d)/stride d ∧ stride d*j+offset d=a := by
    exact OMA.SmallReplay245212.index_fits hd ed ba aH par
  have point:=List.all_eq_true.mp rowpass j (List.mem_range'_1.mpr ⟨idx.1,by dsimp [H,b] at *;omega⟩)
  simp only [idx.2.2] at point
  by_cases rev : q<p
  · have qv : v=true := by simp [v,rev]
    have rq : r=q := min_eq_right rev.le
    simp only [qv,↓reduceIte,rq] at point
    exact leaf hq (by omega) hp rev (by omega) point flip
  · have qv : v=false := by simp [v,rev]
    have rp : r=p := min_eq_left (by omega)
    simp only [qv,Bool.false_eq_true,↓reduceIte,rp] at point
    exact leaf hp (by omega) hq (by omega) (by omega) point eqn


end OMA.SmallFastReplay245212

end

section

/- Cover just the primes admitted by the least-prime bound. -/
namespace OMA.SmallFastDegree245212
open OMA.SmallCaps245212 OMA.SmallFastReplay245212
open scoped ArithmeticFunction.sigma

def lastPrime (d : ℕ) (f v : Bool) :=
  let m:=OMA.SmallReplay245212.first d f+1
  m*(2*(d+1)+ceiling d f v*(2*(d+1)-1))/(m*(d+1)-1)

def Checked (d : ℕ) (f v : Bool) : Prop :=
  ∀ j : ℕ, j≤(lastPrime d f v-3)/32 → stripe d f v (3+32*j) (34+32*j)=true

theorem of_tables {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p)
    (oq : 3≤q) (pq : p≠q) (hd : 2≤d) (ed : d≤4) (order : d≤a)
    (tables : ∀ f v, Checked d f v) :
    OeisA245212.a (2^k*p^a*q^d)≠(σ 1 (2^k*p^a*q^d):ℤ) := by
  intro eqn
  let f:=decide (a<2*d+4)
  let v:=decide (q<p)
  let b:=OMA.SmallReplay245212.first d f
  have ba : b≤a := by by_cases c : a<2*d+4 <;> simp [b,OMA.SmallReplay245212.first,f,c] <;> omega
  have dy : k+1≤ceiling d f v := OMA.SmallCaps245212.dyadic hp hq op oq pq hd ed order eqn
  have sep := OMA.SmallLeast245212.bound hp hq op oq pq (Nat.succ_pos b) (Nat.add_le_add_right ba 1) eqn
  have factor : 2≤(b+1)*(d+1) := by nlinarith only [hd,Nat.zero_le b,Nat.zero_le (b*d)]
  have pos : 0<(b+1)*(d+1)-1 := by omega
  have upper : min p q≤lastPrime d f v := by
    apply (Nat.le_div_iff_mul_le pos).mpr
    rw [Nat.mul_comm]
    exact sep.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.mul_le_mul_right _ dy) _))
  let j:=(min p q-3)/32
  have size : j≤(lastPrime d f v-3)/32 := by dsimp [j];omega
  have lb : 3+32*j ≤ min p q := by dsimp [j];omega
  have ub : min p q≤34+32*j := by dsimp [j];omega
  exact use_stripe hp hq op oq pq hd ed order lb ub (tables f v j size) eqn

end OMA.SmallFastDegree245212

end

section

/- Exclude the original divisor equation for complementary exponent 2. -/
namespace OMA.SmallSecondBlocks245212
open OMA.SmallFastReplay245212 OMA.SmallFastDegree245212
open scoped ArithmeticFunction.sigma

set_option maxRecDepth 8192
set_option maxHeartbeats 16000000

private theorem s00_0 : stripe 2 false false 3 34=true := by decide +kernel

private theorem s00_1 : stripe 2 false false 35 66=true := by decide +kernel

private theorem s00_2 : stripe 2 false false 67 98=true := by decide +kernel

private theorem s00_3 : stripe 2 false false 99 130=true := by decide +kernel

private theorem s00_4 : stripe 2 false false 131 162=true := by decide +kernel

private theorem s00_5 : stripe 2 false false 163 194=true := by decide +kernel

private theorem s00_6 : stripe 2 false false 195 226=true := by decide +kernel

private theorem s00_7 : stripe 2 false false 227 258=true := by decide +kernel

private theorem s00_8 : stripe 2 false false 259 290=true := by decide +kernel

private theorem s00_9 : stripe 2 false false 291 322=true := by decide +kernel

private theorem s00_10 : stripe 2 false false 323 354=true := by decide +kernel

private theorem s00_11 : stripe 2 false false 355 386=true := by decide +kernel

private theorem s00_12 : stripe 2 false false 387 418=true := by decide +kernel

private theorem part00 : Checked 2 false false := by
  intro j h
  change j≤12 at h
  interval_cases j
  · exact s00_0
  · exact s00_1
  · exact s00_2
  · exact s00_3
  · exact s00_4
  · exact s00_5
  · exact s00_6
  · exact s00_7
  · exact s00_8
  · exact s00_9
  · exact s00_10
  · exact s00_11
  · exact s00_12

private theorem s01_0 : stripe 2 false true 3 34=true := by decide +kernel

private theorem s01_1 : stripe 2 false true 35 66=true := by decide +kernel

private theorem s01_2 : stripe 2 false true 67 98=true := by decide +kernel

private theorem s01_3 : stripe 2 false true 99 130=true := by decide +kernel

private theorem s01_4 : stripe 2 false true 131 162=true := by decide +kernel

private theorem s01_5 : stripe 2 false true 163 194=true := by decide +kernel

private theorem s01_6 : stripe 2 false true 195 226=true := by decide +kernel

private theorem s01_7 : stripe 2 false true 227 258=true := by decide +kernel

private theorem part01 : Checked 2 false true := by
  intro j h
  change j≤7 at h
  interval_cases j
  · exact s01_0
  · exact s01_1
  · exact s01_2
  · exact s01_3
  · exact s01_4
  · exact s01_5
  · exact s01_6
  · exact s01_7

private theorem s10_0 : stripe 2 true false 3 34=true := by decide +kernel

private theorem s10_1 : stripe 2 true false 35 66=true := by decide +kernel

private theorem s10_2 : stripe 2 true false 67 98=true := by decide +kernel

private theorem s10_3 : stripe 2 true false 99 130=true := by decide +kernel

private theorem s10_4 : stripe 2 true false 131 162=true := by decide +kernel

private theorem s10_5 : stripe 2 true false 163 194=true := by decide +kernel

private theorem s10_6 : stripe 2 true false 195 226=true := by decide +kernel

private theorem s10_7 : stripe 2 true false 227 258=true := by decide +kernel

private theorem s10_8 : stripe 2 true false 259 290=true := by decide +kernel

private theorem part10 : Checked 2 true false := by
  intro j h
  change j≤8 at h
  interval_cases j
  · exact s10_0
  · exact s10_1
  · exact s10_2
  · exact s10_3
  · exact s10_4
  · exact s10_5
  · exact s10_6
  · exact s10_7
  · exact s10_8

private theorem s11_0 : stripe 2 true true 3 34=true := by decide +kernel

private theorem s11_1 : stripe 2 true true 35 66=true := by decide +kernel

private theorem s11_2 : stripe 2 true true 67 98=true := by decide +kernel

private theorem s11_3 : stripe 2 true true 99 130=true := by decide +kernel

private theorem s11_4 : stripe 2 true true 131 162=true := by decide +kernel

private theorem s11_5 : stripe 2 true true 163 194=true := by decide +kernel

private theorem s11_6 : stripe 2 true true 195 226=true := by decide +kernel

private theorem s11_7 : stripe 2 true true 227 258=true := by decide +kernel

private theorem s11_8 : stripe 2 true true 259 290=true := by decide +kernel

private theorem s11_9 : stripe 2 true true 291 322=true := by decide +kernel

private theorem s11_10 : stripe 2 true true 323 354=true := by decide +kernel

private theorem s11_11 : stripe 2 true true 355 386=true := by decide +kernel

private theorem s11_12 : stripe 2 true true 387 418=true := by decide +kernel

private theorem s11_13 : stripe 2 true true 419 450=true := by decide +kernel

private theorem s11_14 : stripe 2 true true 451 482=true := by decide +kernel

private theorem s11_15 : stripe 2 true true 483 514=true := by decide +kernel

private theorem s11_16 : stripe 2 true true 515 546=true := by decide +kernel

private theorem part11 : Checked 2 true true := by
  intro j h
  change j≤16 at h
  interval_cases j
  · exact s11_0
  · exact s11_1
  · exact s11_2
  · exact s11_3
  · exact s11_4
  · exact s11_5
  · exact s11_6
  · exact s11_7
  · exact s11_8
  · exact s11_9
  · exact s11_10
  · exact s11_11
  · exact s11_12
  · exact s11_13
  · exact s11_14
  · exact s11_15
  · exact s11_16

theorem closed {p q a k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p)
    (oq : 3≤q) (pq : p≠q) (ha : 2≤a) :
    OeisA245212.a (2^k*p^a*q^2)≠(σ 1 (2^k*p^a*q^2):ℤ) := by
  apply of_tables hp hq op oq pq (by decide) (by decide) ha
  intro f v
  cases f <;> cases v
  · exact part00
  · exact part01
  · exact part10
  · exact part11

end OMA.SmallSecondBlocks245212

end

section

/- Exclude the original divisor equation for complementary exponent 3. -/
namespace OMA.SmallThirdBlocks245212
open OMA.SmallFastReplay245212 OMA.SmallFastDegree245212
open scoped ArithmeticFunction.sigma

set_option maxRecDepth 8192
set_option maxHeartbeats 16000000

private theorem s00_0 : stripe 3 false false 3 34=true := by decide +kernel

private theorem s00_1 : stripe 3 false false 35 66=true := by decide +kernel

private theorem s00_2 : stripe 3 false false 67 98=true := by decide +kernel

private theorem s00_3 : stripe 3 false false 99 130=true := by decide +kernel

private theorem s00_4 : stripe 3 false false 131 162=true := by decide +kernel

private theorem s00_5 : stripe 3 false false 163 194=true := by decide +kernel

private theorem s00_6 : stripe 3 false false 195 226=true := by decide +kernel

private theorem s00_7 : stripe 3 false false 227 258=true := by decide +kernel

private theorem s00_8 : stripe 3 false false 259 290=true := by decide +kernel

private theorem s00_9 : stripe 3 false false 291 322=true := by decide +kernel

private theorem s00_10 : stripe 3 false false 323 354=true := by decide +kernel

private theorem s00_11 : stripe 3 false false 355 386=true := by decide +kernel

private theorem s00_12 : stripe 3 false false 387 418=true := by decide +kernel

private theorem s00_13 : stripe 3 false false 419 450=true := by decide +kernel

private theorem s00_14 : stripe 3 false false 451 482=true := by decide +kernel

private theorem s00_15 : stripe 3 false false 483 514=true := by decide +kernel

private theorem s00_16 : stripe 3 false false 515 546=true := by decide +kernel

private theorem s00_17 : stripe 3 false false 547 578=true := by decide +kernel

private theorem s00_18 : stripe 3 false false 579 610=true := by decide +kernel

private theorem s00_19 : stripe 3 false false 611 642=true := by decide +kernel

private theorem part00 : Checked 3 false false := by
  intro j h
  change j≤19 at h
  interval_cases j
  · exact s00_0
  · exact s00_1
  · exact s00_2
  · exact s00_3
  · exact s00_4
  · exact s00_5
  · exact s00_6
  · exact s00_7
  · exact s00_8
  · exact s00_9
  · exact s00_10
  · exact s00_11
  · exact s00_12
  · exact s00_13
  · exact s00_14
  · exact s00_15
  · exact s00_16
  · exact s00_17
  · exact s00_18
  · exact s00_19

private theorem s01_0 : stripe 3 false true 3 34=true := by decide +kernel

private theorem s01_1 : stripe 3 false true 35 66=true := by decide +kernel

private theorem s01_2 : stripe 3 false true 67 98=true := by decide +kernel

private theorem s01_3 : stripe 3 false true 99 130=true := by decide +kernel

private theorem s01_4 : stripe 3 false true 131 162=true := by decide +kernel

private theorem s01_5 : stripe 3 false true 163 194=true := by decide +kernel

private theorem s01_6 : stripe 3 false true 195 226=true := by decide +kernel

private theorem s01_7 : stripe 3 false true 227 258=true := by decide +kernel

private theorem s01_8 : stripe 3 false true 259 290=true := by decide +kernel

private theorem s01_9 : stripe 3 false true 291 322=true := by decide +kernel

private theorem part01 : Checked 3 false true := by
  intro j h
  change j≤9 at h
  interval_cases j
  · exact s01_0
  · exact s01_1
  · exact s01_2
  · exact s01_3
  · exact s01_4
  · exact s01_5
  · exact s01_6
  · exact s01_7
  · exact s01_8
  · exact s01_9

private theorem s10_0 : stripe 3 true false 3 34=true := by decide +kernel

private theorem s10_1 : stripe 3 true false 35 66=true := by decide +kernel

private theorem s10_2 : stripe 3 true false 67 98=true := by decide +kernel

private theorem s10_3 : stripe 3 true false 99 130=true := by decide +kernel

private theorem s10_4 : stripe 3 true false 131 162=true := by decide +kernel

private theorem s10_5 : stripe 3 true false 163 194=true := by decide +kernel

private theorem s10_6 : stripe 3 true false 195 226=true := by decide +kernel

private theorem s10_7 : stripe 3 true false 227 258=true := by decide +kernel

private theorem s10_8 : stripe 3 true false 259 290=true := by decide +kernel

private theorem s10_9 : stripe 3 true false 291 322=true := by decide +kernel

private theorem s10_10 : stripe 3 true false 323 354=true := by decide +kernel

private theorem s10_11 : stripe 3 true false 355 386=true := by decide +kernel

private theorem part10 : Checked 3 true false := by
  intro j h
  change j≤11 at h
  interval_cases j
  · exact s10_0
  · exact s10_1
  · exact s10_2
  · exact s10_3
  · exact s10_4
  · exact s10_5
  · exact s10_6
  · exact s10_7
  · exact s10_8
  · exact s10_9
  · exact s10_10
  · exact s10_11

private theorem s11_0 : stripe 3 true true 3 34=true := by decide +kernel

private theorem s11_1 : stripe 3 true true 35 66=true := by decide +kernel

private theorem s11_2 : stripe 3 true true 67 98=true := by decide +kernel

private theorem s11_3 : stripe 3 true true 99 130=true := by decide +kernel

private theorem s11_4 : stripe 3 true true 131 162=true := by decide +kernel

private theorem s11_5 : stripe 3 true true 163 194=true := by decide +kernel

private theorem s11_6 : stripe 3 true true 195 226=true := by decide +kernel

private theorem s11_7 : stripe 3 true true 227 258=true := by decide +kernel

private theorem s11_8 : stripe 3 true true 259 290=true := by decide +kernel

private theorem s11_9 : stripe 3 true true 291 322=true := by decide +kernel

private theorem s11_10 : stripe 3 true true 323 354=true := by decide +kernel

private theorem s11_11 : stripe 3 true true 355 386=true := by decide +kernel

private theorem s11_12 : stripe 3 true true 387 418=true := by decide +kernel

private theorem s11_13 : stripe 3 true true 419 450=true := by decide +kernel

private theorem s11_14 : stripe 3 true true 451 482=true := by decide +kernel

private theorem s11_15 : stripe 3 true true 483 514=true := by decide +kernel

private theorem s11_16 : stripe 3 true true 515 546=true := by decide +kernel

private theorem s11_17 : stripe 3 true true 547 578=true := by decide +kernel

private theorem s11_18 : stripe 3 true true 579 610=true := by decide +kernel

private theorem s11_19 : stripe 3 true true 611 642=true := by decide +kernel

private theorem s11_20 : stripe 3 true true 643 674=true := by decide +kernel

private theorem s11_21 : stripe 3 true true 675 706=true := by decide +kernel

private theorem s11_22 : stripe 3 true true 707 738=true := by decide +kernel

private theorem s11_23 : stripe 3 true true 739 770=true := by decide +kernel

private theorem s11_24 : stripe 3 true true 771 802=true := by decide +kernel

private theorem s11_25 : stripe 3 true true 803 834=true := by decide +kernel

private theorem s11_26 : stripe 3 true true 835 866=true := by decide +kernel

private theorem s11_27 : stripe 3 true true 867 898=true := by decide +kernel

private theorem s11_28 : stripe 3 true true 899 930=true := by decide +kernel

private theorem part11 : Checked 3 true true := by
  intro j h
  change j≤28 at h
  interval_cases j
  · exact s11_0
  · exact s11_1
  · exact s11_2
  · exact s11_3
  · exact s11_4
  · exact s11_5
  · exact s11_6
  · exact s11_7
  · exact s11_8
  · exact s11_9
  · exact s11_10
  · exact s11_11
  · exact s11_12
  · exact s11_13
  · exact s11_14
  · exact s11_15
  · exact s11_16
  · exact s11_17
  · exact s11_18
  · exact s11_19
  · exact s11_20
  · exact s11_21
  · exact s11_22
  · exact s11_23
  · exact s11_24
  · exact s11_25
  · exact s11_26
  · exact s11_27
  · exact s11_28

theorem closed {p q a k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p)
    (oq : 3≤q) (pq : p≠q) (ha : 3≤a) :
    OeisA245212.a (2^k*p^a*q^3)≠(σ 1 (2^k*p^a*q^3):ℤ) := by
  apply of_tables hp hq op oq pq (by decide) (by decide) ha
  intro f v
  cases f <;> cases v
  · exact part00
  · exact part01
  · exact part10
  · exact part11

end OMA.SmallThirdBlocks245212

end

section

/- Exclude the original divisor equation for complementary exponent 4. -/
namespace OMA.SmallFourthBlocks245212
open OMA.SmallFastReplay245212 OMA.SmallFastDegree245212
open scoped ArithmeticFunction.sigma

set_option maxRecDepth 8192
set_option maxHeartbeats 16000000

private theorem s00_0 : stripe 4 false false 3 34=true := by decide +kernel

private theorem s00_1 : stripe 4 false false 35 66=true := by decide +kernel

private theorem s00_2 : stripe 4 false false 67 98=true := by decide +kernel

private theorem s00_3 : stripe 4 false false 99 130=true := by decide +kernel

private theorem s00_4 : stripe 4 false false 131 162=true := by decide +kernel

private theorem s00_5 : stripe 4 false false 163 194=true := by decide +kernel

private theorem s00_6 : stripe 4 false false 195 226=true := by decide +kernel

private theorem s00_7 : stripe 4 false false 227 258=true := by decide +kernel

private theorem s00_8 : stripe 4 false false 259 290=true := by decide +kernel

private theorem s00_9 : stripe 4 false false 291 322=true := by decide +kernel

private theorem s00_10 : stripe 4 false false 323 354=true := by decide +kernel

private theorem s00_11 : stripe 4 false false 355 386=true := by decide +kernel

private theorem s00_12 : stripe 4 false false 387 418=true := by decide +kernel

private theorem s00_13 : stripe 4 false false 419 450=true := by decide +kernel

private theorem s00_14 : stripe 4 false false 451 482=true := by decide +kernel

private theorem s00_15 : stripe 4 false false 483 514=true := by decide +kernel

private theorem s00_16 : stripe 4 false false 515 546=true := by decide +kernel

private theorem s00_17 : stripe 4 false false 547 578=true := by decide +kernel

private theorem s00_18 : stripe 4 false false 579 610=true := by decide +kernel

private theorem s00_19 : stripe 4 false false 611 642=true := by decide +kernel

private theorem s00_20 : stripe 4 false false 643 674=true := by decide +kernel

private theorem s00_21 : stripe 4 false false 675 706=true := by decide +kernel

private theorem s00_22 : stripe 4 false false 707 738=true := by decide +kernel

private theorem s00_23 : stripe 4 false false 739 770=true := by decide +kernel

private theorem s00_24 : stripe 4 false false 771 802=true := by decide +kernel

private theorem s00_25 : stripe 4 false false 803 834=true := by decide +kernel

private theorem s00_26 : stripe 4 false false 835 866=true := by decide +kernel

private theorem s00_27 : stripe 4 false false 867 898=true := by decide +kernel

private theorem part00 : Checked 4 false false := by
  intro j h
  change j≤27 at h
  interval_cases j
  · exact s00_0
  · exact s00_1
  · exact s00_2
  · exact s00_3
  · exact s00_4
  · exact s00_5
  · exact s00_6
  · exact s00_7
  · exact s00_8
  · exact s00_9
  · exact s00_10
  · exact s00_11
  · exact s00_12
  · exact s00_13
  · exact s00_14
  · exact s00_15
  · exact s00_16
  · exact s00_17
  · exact s00_18
  · exact s00_19
  · exact s00_20
  · exact s00_21
  · exact s00_22
  · exact s00_23
  · exact s00_24
  · exact s00_25
  · exact s00_26
  · exact s00_27

private theorem s01_0 : stripe 4 false true 3 34=true := by decide +kernel

private theorem s01_1 : stripe 4 false true 35 66=true := by decide +kernel

private theorem s01_2 : stripe 4 false true 67 98=true := by decide +kernel

private theorem s01_3 : stripe 4 false true 99 130=true := by decide +kernel

private theorem s01_4 : stripe 4 false true 131 162=true := by decide +kernel

private theorem s01_5 : stripe 4 false true 163 194=true := by decide +kernel

private theorem s01_6 : stripe 4 false true 195 226=true := by decide +kernel

private theorem s01_7 : stripe 4 false true 227 258=true := by decide +kernel

private theorem s01_8 : stripe 4 false true 259 290=true := by decide +kernel

private theorem s01_9 : stripe 4 false true 291 322=true := by decide +kernel

private theorem s01_10 : stripe 4 false true 323 354=true := by decide +kernel

private theorem s01_11 : stripe 4 false true 355 386=true := by decide +kernel

private theorem s01_12 : stripe 4 false true 387 418=true := by decide +kernel

private theorem part01 : Checked 4 false true := by
  intro j h
  change j≤12 at h
  interval_cases j
  · exact s01_0
  · exact s01_1
  · exact s01_2
  · exact s01_3
  · exact s01_4
  · exact s01_5
  · exact s01_6
  · exact s01_7
  · exact s01_8
  · exact s01_9
  · exact s01_10
  · exact s01_11
  · exact s01_12

private theorem s10_0 : stripe 4 true false 3 34=true := by decide +kernel

private theorem s10_1 : stripe 4 true false 35 66=true := by decide +kernel

private theorem s10_2 : stripe 4 true false 67 98=true := by decide +kernel

private theorem s10_3 : stripe 4 true false 99 130=true := by decide +kernel

private theorem s10_4 : stripe 4 true false 131 162=true := by decide +kernel

private theorem s10_5 : stripe 4 true false 163 194=true := by decide +kernel

private theorem s10_6 : stripe 4 true false 195 226=true := by decide +kernel

private theorem s10_7 : stripe 4 true false 227 258=true := by decide +kernel

private theorem s10_8 : stripe 4 true false 259 290=true := by decide +kernel

private theorem s10_9 : stripe 4 true false 291 322=true := by decide +kernel

private theorem s10_10 : stripe 4 true false 323 354=true := by decide +kernel

private theorem s10_11 : stripe 4 true false 355 386=true := by decide +kernel

private theorem s10_12 : stripe 4 true false 387 418=true := by decide +kernel

private theorem s10_13 : stripe 4 true false 419 450=true := by decide +kernel

private theorem s10_14 : stripe 4 true false 451 482=true := by decide +kernel

private theorem s10_15 : stripe 4 true false 483 514=true := by decide +kernel

private theorem part10 : Checked 4 true false := by
  intro j h
  change j≤15 at h
  interval_cases j
  · exact s10_0
  · exact s10_1
  · exact s10_2
  · exact s10_3
  · exact s10_4
  · exact s10_5
  · exact s10_6
  · exact s10_7
  · exact s10_8
  · exact s10_9
  · exact s10_10
  · exact s10_11
  · exact s10_12
  · exact s10_13
  · exact s10_14
  · exact s10_15

private theorem s11_0 : stripe 4 true true 3 34=true := by decide +kernel

private theorem s11_1 : stripe 4 true true 35 66=true := by decide +kernel

private theorem s11_2 : stripe 4 true true 67 98=true := by decide +kernel

private theorem s11_3 : stripe 4 true true 99 130=true := by decide +kernel

private theorem s11_4 : stripe 4 true true 131 162=true := by decide +kernel

private theorem s11_5 : stripe 4 true true 163 194=true := by decide +kernel

private theorem s11_6 : stripe 4 true true 195 226=true := by decide +kernel

private theorem s11_7 : stripe 4 true true 227 258=true := by decide +kernel

private theorem s11_8 : stripe 4 true true 259 290=true := by decide +kernel

private theorem s11_9 : stripe 4 true true 291 322=true := by decide +kernel

private theorem s11_10 : stripe 4 true true 323 354=true := by decide +kernel

private theorem s11_11 : stripe 4 true true 355 386=true := by decide +kernel

private theorem s11_12 : stripe 4 true true 387 418=true := by decide +kernel

private theorem s11_13 : stripe 4 true true 419 450=true := by decide +kernel

private theorem s11_14 : stripe 4 true true 451 482=true := by decide +kernel

private theorem s11_15 : stripe 4 true true 483 514=true := by decide +kernel

private theorem s11_16 : stripe 4 true true 515 546=true := by decide +kernel

private theorem s11_17 : stripe 4 true true 547 578=true := by decide +kernel

private theorem s11_18 : stripe 4 true true 579 610=true := by decide +kernel

private theorem s11_19 : stripe 4 true true 611 642=true := by decide +kernel

private theorem s11_20 : stripe 4 true true 643 674=true := by decide +kernel

private theorem s11_21 : stripe 4 true true 675 706=true := by decide +kernel

private theorem s11_22 : stripe 4 true true 707 738=true := by decide +kernel

private theorem s11_23 : stripe 4 true true 739 770=true := by decide +kernel

private theorem s11_24 : stripe 4 true true 771 802=true := by decide +kernel

private theorem s11_25 : stripe 4 true true 803 834=true := by decide +kernel

private theorem s11_26 : stripe 4 true true 835 866=true := by decide +kernel

private theorem s11_27 : stripe 4 true true 867 898=true := by decide +kernel

private theorem s11_28 : stripe 4 true true 899 930=true := by decide +kernel

private theorem s11_29 : stripe 4 true true 931 962=true := by decide +kernel

private theorem s11_30 : stripe 4 true true 963 994=true := by decide +kernel

private theorem s11_31 : stripe 4 true true 995 1026=true := by decide +kernel

private theorem s11_32 : stripe 4 true true 1027 1058=true := by decide +kernel

private theorem s11_33 : stripe 4 true true 1059 1090=true := by decide +kernel

private theorem s11_34 : stripe 4 true true 1091 1122=true := by decide +kernel

private theorem s11_35 : stripe 4 true true 1123 1154=true := by decide +kernel

private theorem s11_36 : stripe 4 true true 1155 1186=true := by decide +kernel

private theorem s11_37 : stripe 4 true true 1187 1218=true := by decide +kernel

private theorem s11_38 : stripe 4 true true 1219 1250=true := by decide +kernel

private theorem s11_39 : stripe 4 true true 1251 1282=true := by decide +kernel

private theorem s11_40 : stripe 4 true true 1283 1314=true := by decide +kernel

private theorem s11_41 : stripe 4 true true 1315 1346=true := by decide +kernel

private theorem s11_42 : stripe 4 true true 1347 1378=true := by decide +kernel

private theorem s11_43 : stripe 4 true true 1379 1410=true := by decide +kernel

private theorem s11_44 : stripe 4 true true 1411 1442=true := by decide +kernel

private theorem s11_45 : stripe 4 true true 1443 1474=true := by decide +kernel

private theorem part11 : Checked 4 true true := by
  intro j h
  change j≤45 at h
  interval_cases j
  · exact s11_0
  · exact s11_1
  · exact s11_2
  · exact s11_3
  · exact s11_4
  · exact s11_5
  · exact s11_6
  · exact s11_7
  · exact s11_8
  · exact s11_9
  · exact s11_10
  · exact s11_11
  · exact s11_12
  · exact s11_13
  · exact s11_14
  · exact s11_15
  · exact s11_16
  · exact s11_17
  · exact s11_18
  · exact s11_19
  · exact s11_20
  · exact s11_21
  · exact s11_22
  · exact s11_23
  · exact s11_24
  · exact s11_25
  · exact s11_26
  · exact s11_27
  · exact s11_28
  · exact s11_29
  · exact s11_30
  · exact s11_31
  · exact s11_32
  · exact s11_33
  · exact s11_34
  · exact s11_35
  · exact s11_36
  · exact s11_37
  · exact s11_38
  · exact s11_39
  · exact s11_40
  · exact s11_41
  · exact s11_42
  · exact s11_43
  · exact s11_44
  · exact s11_45

theorem closed {p q a k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p)
    (oq : 3≤q) (pq : p≠q) (ha : 4≤a) :
    OeisA245212.a (2^k*p^a*q^4)≠(σ 1 (2^k*p^a*q^4):ℤ) := by
  apply of_tables hp hq op oq pq (by decide) (by decide) ha
  intro f v
  cases f <;> cases v
  · exact part00
  · exact part01
  · exact part10
  · exact part11

end OMA.SmallFourthBlocks245212

end

section

/- The complete small-exponent sector of the two-odd-prime divisor equation. -/
namespace OMA.SmallOriginal245212
open scoped ArithmeticFunction.sigma

private theorem ordered {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (op : 3≤p) (oq : 3≤q) (pq : p≠q) (hd : 1≤d) (small : d≤4) (order : d≤a) :
    OeisA245212.a (2^k*p^a*q^d)≠(σ 1 (2^k*p^a*q^d):ℤ) := by
  interval_cases d
  · simpa using OMA.SmallLinear245212.closed (a:=a) (k:=k) hp hq op oq pq
  · exact OMA.SmallSecondBlocks245212.closed hp hq op oq pq order
  · exact OMA.SmallThirdBlocks245212.closed hp hq op oq pq order
  · exact OMA.SmallFourthBlocks245212.closed hp hq op oq pq order

theorem closed {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (op : 3≤p) (oq : 3≤q) (pq : p≠q) (ha : 1≤a) (hd : 1≤d) (small : min a d≤4) :
    OeisA245212.a (2^k*p^a*q^d)≠(σ 1 (2^k*p^a*q^d):ℤ) := by
  rcases le_total d a with da|ad
  · exact ordered hp hq op oq pq hd (by omega) da
  · rw [mul_right_comm (2^k)]
    exact ordered hq hp oq op pq.symm ha (by omega) ad

end OMA.SmallOriginal245212

end

#print axioms OMA.SmallOriginal245212.closed
