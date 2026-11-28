import FormalConjectures.OEIS.«245212»



/-! OEIS A245212: an explicit height for any fixed cofactor extended by two free odd prime powers. -/

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

theorem squeeze {N x y w P Q X L : ℤ} (nz : N≠0) (p : 1≤P) (q : 1≤Q)
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

theorem coeff {A S p q B M z : ℤ} (a : 0≤A) (s : 0≤S)
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

end OMA.RankThreeFourSmallSeparation245212

end

section

namespace OMA.OddFaces245212
open OMA.Smooth245212
def limitX (p : ℕ) : ℚ := X p none
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


theorem count_le (h : ℕ) : h.divisors.card≤h := by
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

theorem combine {h v B : ℕ} (pos : 0<h) (small : h≤B) (large : v≤(W h+σ 1 h)^2) :
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

/- Prime-power estimates for making the exceptional two-prime Euler slope effective. -/
namespace OMA.TwoFreeEffectivePower245212
open Nat ArithmeticFunction OMA.Smooth245212 OMA.CofactorPairPole245212
open OMA.RankThreeFourSmallSeparation245212
open scoped ArithmeticFunction.sigma
open OMA.RankThreeFourSmallSeparation245212 (squeeze)
open OMA.RankThreeFourSmallSeparation245212 (coeff)
open OMA.CapOrder245212 (geom)

theorem min_power {h p q a d M : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime)
    (cp : h.Coprime p) (cq : h.Coprime q) (pq : p<q)
    (am : a≤M) (dm : d≤M) (qm : M+1<q) (qt : ¬q∣2*(h*σ 0 h))
    (eqn : OeisA245212.a (h*p^a*q^d)=(σ 1 (h*p^a*q^d):ℤ)) :
    min (p^a) (q^d)≤cost (W h) (σ 1 h) q M := by
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
  have x:=OMA.RankThreeFourSmallSeparation245212.coeff (p:=(q:ℤ)) (q:=(p:ℤ)) (z:=(q:ℤ)) (A:=(A:ℤ)) (S:=(S:ℤ)) (M:=(M:ℤ)) (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    (by exact_mod_cast hq.two_le) (by exact_mod_cast hp.two_le) (by rfl : (q:ℤ)≤q)
    (by exact_mod_cast pq.le) (by omega : 1≤(d:ℤ)+1) (by omega)
  have y:=OMA.RankThreeFourSmallSeparation245212.coeff (p:=(p:ℤ)) (q:=(q:ℤ)) (z:=(q:ℤ)) (A:=(A:ℤ)) (S:=(S:ℤ)) (M:=(M:ℤ)) (Int.natCast_nonneg _) (Int.natCast_nonneg _)
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
  have k:=OMA.RankThreeFourSmallSeparation245212.squeeze (P:=(p:ℤ)^a) (Q:=(q:ℤ)^d) n (by exact_mod_cast Nat.one_le_pow a p hp.pos)
    (by exact_mod_cast Nat.one_le_pow d q hq.pos) x y w0 wle (by simpa only [add_assoc] using id)
  unfold cost; rw [Nat.add_assoc];exact_mod_cast k

theorem moments {h p e : ℕ} (hp : p.Prime) (cp : h.Coprime p) :
    W (h*p^e)+σ 1 (h*p^e)≤2*(W h*(e+1)+σ 1 h)*p^e := by
  have sg : σ 1 (p^e)<2*p^e := by rw [sigma_one_apply_prime_pow hp];exact OMA.CapOrder245212.geom p hp.one_lt e
  have wt : W (p^e)≤(e+1)*(σ 1 (p^e)) := by
    rw [w_pow hp,sigma_one_apply_prime_pow hp,Finset.mul_sum]
    exact Finset.sum_le_sum fun j hj => by
      have le:=show j+1≤e+1 by have := Finset.mem_range.mp hj;omega
      simpa only [Nat.mul_comm] using Nat.mul_le_mul_left (p^j) le
  rw [w_mult.map_mul_of_coprime (cp.pow_right e),isMultiplicative_sigma.map_mul_of_coprime (cp.pow_right e)]
  nlinarith only [Nat.mul_le_mul_left (W h) wt,Nat.mul_le_mul_left (W h*(e+1)+σ 1 h) sg.le]

theorem next_power {h p q a d : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime) (oq : q≠2)
    (cp : h.Coprime p) (cq : h.Coprime q) (pq : p≠q) (dp : 0<d)
    (eqn : OeisA245212.a (h*p^a*q^d)=(σ 1 (h*p^a*q^d):ℤ)) :
    q^d≤(2*(W h*(a+1)+σ 1 h)*p^a)^2 := by
  have pos:=hp.pos
  have mp : 0<h*p^a := by positivity
  have c:=(cq.mul_left (((coprime_primes hp hq).mpr pq).pow_left a))
  exact (OMA.PairHeight245212.last_square mp hq oq c dp eqn).trans (Nat.pow_le_pow_left (moments hp cp) 2)

theorem lengths {A S p q a d : ℕ} (pa : p^4≤q) (large : 16*(A+S+1)≤q)
    (aq : a+1<q) (pow : q^d≤(2*(A*(a+1)+S)*p^a)^2) : d+1<q := by
  have q1 : 1<q := by omega
  have small : 2*(A*(a+1)+S)≤q^2 := by
    have ord : 2*(A+S)≤q := by omega
    nlinarith only [Nat.mul_le_mul_right q ord,Nat.mul_le_mul_left A aq.le,Nat.le_mul_of_pos_right S (by omega : 0<q)]
  have twice:=Nat.pow_le_pow_left (pow.trans (Nat.pow_le_pow_left (Nat.mul_le_mul_right _ small) 2)) 2
  have le : q^(2*d)≤q^(8+a) := calc
    _ = (q^d)^2 := by rw [←pow_mul];ring_nf
    _ ≤ ((q^2*p^a)^2)^2 := twice
    _ = q^8*(p^4)^a := by ring_nf
    _ ≤ q^8*q^a := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left pa a)
    _ = _ := (pow_add q 8 a).symm
  have := (pow_le_pow_iff_right₀ q1).mp le
  omega

theorem polynomial_cut {C a : ℕ} (z : 2^a≤C*(a+1)^6) : a ≤ max 784 (64*C) := by
  by_cases big : 784≤a
  · have abs:=OMA.ComplementarySize245212.absorb (d:=6) big
    have le1 : a+1≤2*a := by omega
    have le:=abs.trans (z.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left le1 6)))
    have v : a^6*a^6≤64*C*a^6 := calc
      _ = a^(2*6) := by ring
      _ ≤ C*(2*a)^6 := le
      _ = _ := by ring
    have a0 : 0<a^6 := by positivity
    have x:=Nat.le_of_mul_le_mul_right v a0
    have aa : a≤a^6 := by simpa using (Nat.pow_le_pow_right (show 0<a by omega) (by decide : 1≤6))
    exact (aa.trans x).trans (le_max_right _ _)
  · omega

end OMA.TwoFreeEffectivePower245212

end

section

/- Explicit first-exponent bound at the exact smaller-prime Euler slope. -/
namespace OMA.TwoFreeEffectivePole245212
open Nat ArithmeticFunction OMA.Smooth245212 OMA.TwoFreeEffectivePower245212
open OMA.RankThreeFourSmallSeparation245212
open scoped ArithmeticFunction.sigma

def scalar (A S : ℕ) := 16*(A+S+1)
def multiplier (A S P : ℕ) := 2*P*(A+S)*(S*P+1)
def scale (A S : ℕ) := max (scalar A S) ((2*(4*A+S))^2)
def poleExponent (A S P : ℕ) := max 784 (64*(scale A S*(multiplier A S P)^6))

theorem cost_le {A S q M : ℕ} (pos : 0<q) (small : M+1≤q) :
    cost A S q M ≤ scalar A S*q^3 := by
  have t : 1≤q^3 := Nat.one_le_pow _ _ pos
  have one : q≤q^3 := by simpa using Nat.pow_le_pow_right pos (by decide : 1≤3)
  have two : q^2≤q^3 := Nat.pow_le_pow_right pos (by decide : 2≤3)
  have cm:=Nat.mul_le_mul_right (A*q^2) small
  unfold cost scalar
  nlinarith only [cm,Nat.mul_le_mul_left A one,Nat.mul_le_mul_left A t,Nat.mul_le_mul_left S two,t]

private theorem small_second {h p q a d : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime) (op : 3≤p)
    (cp : h.Coprime p) (cq : h.Coprime q) (pq : p<q) (ap : 0<a) (low : d≤3)
    (eqn : OeisA245212.a (h*p^a*q^d)=(σ 1 (h*p^a*q^d):ℤ)) :
    p^a ≤ scale (W h) (σ 1 h)*q^6 := by
  have swapped : OeisA245212.a (h*q^d*p^a)=(σ 1 (h*q^d*p^a):ℤ) := by rwa [mul_right_comm]
  have pw:=next_power hh hq hp (by omega) cq cp pq.ne.symm ap swapped
  let A:=W h
  let S:=σ 1 h
  have le : 2*(A*(d+1)+S)*q^d≤2*(4*A+S)*q^3 := by
    rw [mul_comm 4 A]
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 (Nat.add_le_add_right (Nat.mul_le_mul_left A (by omega)) _))
      (Nat.pow_le_pow_right hq.pos low)
  calc
    _ ≤ (2*(4*A+S)*q^3)^2 := pw.trans (Nat.pow_le_pow_left le 2)
    _ = (2*(4*A+S))^2*q^6 := by ring
    _ ≤ scale A S*q^6 := Nat.mul_le_mul_right _ (le_max_right ..)

theorem original {h p q a d P : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime) (op : 3≤p)
    (cp : h.Coprime p) (cq : h.Coprime q) (pq : p<q) (ap : 0<a) (dp : 0<d) (maxp : p≤P)
    (pole : W h*p=2*(h*σ 0 h)*(p-1)) (pa : P^4≤q) (costly : scalar (W h) (σ 1 h)<q)
    (qt : 2*(h*σ 0 h)<q) (eqn : OeisA245212.a (h*p^a*q^d)=(σ 1 (h*p^a*q^d):ℤ)) :
    a ≤ poleExponent (W h) (σ 1 h) P := by
  let A:=W h
  let S:=σ 1 h
  let K:=multiplier A S P
  have iz : (W h:ℤ)*p=2*((h:ℤ)*σ 0 h)*(p-1) := by
    zify [Nat.cast_sub hp.pos] at pole
    simpa only [mul_assoc] using pole
  obtain ⟨d,rfl⟩:=Nat.exists_eq_succ_of_ne_zero dp.ne'
  obtain ⟨lin,lower⟩:=OMA.CofactorPairPole245212.original_slope hh hp hq op (by omega) cp cq pq.ne iz eqn
  have lin' : q≤2*(p-1)*(A+S)*(S*(p-1)+1)*(a+1) := by
    dsimp [A,S];exact_mod_cast (by simpa only [Nat.cast_sub hp.pos,Nat.cast_one,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat] using lin :
      (q:ℤ)≤(2*(p-1)*(W h+σ 1 h)*(σ 1 h*(p-1)+1)*(a+1):ℕ))
  have qb : q≤K*(a+1) := lin'.trans (by dsimp [K,multiplier];gcongr <;> omega)
  have pw : p^a ≤ scale A S*q^6 := by
    by_cases sd : d+1≤3
    · exact small_second hh hp hq op cp cq pq ap sd eqn
    have aq:=lower ap (by omega)
    have qo:=lengths ((Nat.pow_le_pow_left maxp 4).trans pa) costly.le aq (next_power hh hp hq (by omega) cp cq pq.ne (by omega) eqn)
    let M:=max a (d+1)
    have m : M+1<q := by dsimp [M];omega
    have hd:=min_power hh hp hq cp cq pq (le_max_left ..) (le_max_right ..) m
      (Nat.not_dvd_of_pos_of_lt (by have := sigma_pos 0 h hh.ne'; positivity) qt) eqn
    have cap := hd.trans (cost_le hq.pos m.le)
    rcases le_total (p^a) (q^(d+1)) with x|y
    · rw [min_eq_left x] at cap
      exact cap.trans (Nat.mul_le_mul (le_max_left ..) (Nat.pow_le_pow_right hq.pos (by decide : 3≤6)))
    · rw [min_eq_right y] at cap
      have small := cap.trans_lt (Nat.mul_lt_mul_of_pos_right costly (pow_pos hq.pos 3))
      have order := (Nat.pow_le_pow_right hq.pos (show 4≤d+1 by omega)).trans_lt small
      have zero : q*q^3=q^4 := by ring
      rw [zero] at order
      exact order.false.elim
  apply polynomial_cut (C:=scale A S*K^6)
  calc
    _ ≤ p^a := Nat.pow_le_pow_left hp.two_le _
    _ ≤ scale A S*(K*(a+1))^6 := pw.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left qb 6))
    _ = _ := by ring

end OMA.TwoFreeEffectivePole245212

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

/- A computable height for every extension of a fixed positive integer by
two arbitrary distinct odd prime powers, including exact Euler resonance. -/
namespace OMA.TwoFreeEffective245212
open Nat Finset ArithmeticFunction OMA.Smooth245212 OMA.CofactorEulerPair245212
open OMA.RankThreeFourSmallHarmonic245212 OMA.RankThreeFourSmallBounds245212
open OMA.TwoFreeEffectivePole245212 (scalar poleExponent)
open scoped ArithmeticFunction.sigma
open OMA.PairHeight245212 (combine)

def lastCut (A S H P : ℕ) := P^4+scalar A S+H+2*A*P+2
def finiteExponent (A S Z : ℕ) := 4*A*Z+2*(A+S*Z^2)
def looseExponent (A S P : ℕ) := 2*A+4*S*P+poleExponent A S P
def atomBound (A S H : ℕ) :=
  let P:=primeCut A S H
  let Z:=lastCut A S H P
  max (Z^finiteExponent A S Z) (P^looseExponent A S P)

/-- The factor 1 also covers absent prime powers. -/
def height (h : ℕ) := 4*(h*max 1 (atomBound (W h) (σ 1 h) (2*(h*σ 0 h))))^7

private theorem bounded_pair {A S H p q a d Z : ℕ} (hp : p.Prime) (hq : q.Prime)
    (ap : 0<A) (sp : 0<S) (pq : p<q) (qz : q≤Z) (b : Bal A S H p q a d) :
    min a d ≤ finiteExponent A S Z := by
  by_cases high : H*(p-1)*(q-1)<A*p*q
  · have raw:=(short_pair hp hq high (strict hp hq sp b)).trans (Nat.div_le_self _ _)
    have x : 2*A*(p+q)≤4*A*Z := by
      nlinarith only [Nat.mul_le_mul_left A pq.le,Nat.mul_le_mul_left A qz]
    unfold finiteExponent;omega
  · have raw:=(under_pair hp hq ap b (le_of_not_gt high)).trans (Nat.div_le_self _ _)
    have x : 2*(A+S*(p-1)*(q-1))≤2*(A+S*Z^2) := by
      rw [sq,←mul_assoc S Z Z];gcongr <;> omega
    unfold finiteExponent;omega

theorem atom {h p q a d : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime) (op : 3≤p)
    (cp : h.Coprime p) (cq : h.Coprime q) (pq : p<q) (ap : 0<a) (dp : 0<d)
    (eqn : OeisA245212.a (h*p^a*q^d)=(σ 1 (h*p^a*q^d):ℤ)) :
    min (p^a) (q^d) ≤ atomBound (W h) (σ 1 h) (2*(h*σ 0 h)) := by
  let A:=W h
  let S:=σ 1 h
  let H:=2*(h*σ 0 h)
  let P:=primeCut A S H
  let Z:=lastCut A S H P
  have wp : 0<A := by
    dsimp [A];rw [w_apply]
    exact sum_pos' (fun _ _=>Nat.zero_le _) ⟨1,Nat.one_mem_divisors.mpr hh.ne',by simp⟩
  have sp : 0<S := sigma_pos 1 h hh.ne'
  have pp : p≤P := first_prime hh hp hq cp cq pq ap dp eqn
  have b : Bal A S H p q a d := by simpa [A,S,H,Bal] using normalized hh hp hq cp cq pq.ne eqn
  by_cases finite : q≤Z
  · apply le_trans _ (le_max_left ..)
    have lim:=bounded_pair hp hq wp sp pq finite b
    have zp : 0<Z := hq.pos.trans_le finite
    rcases le_total a d with ad|da
    · rw [min_eq_left ad] at lim
      exact (min_le_left ..).trans ((Nat.pow_le_pow_left (pq.le.trans finite) a).trans (Nat.pow_le_pow_right zp lim))
    · rw [min_eq_right da] at lim
      exact (min_le_right ..).trans ((Nat.pow_le_pow_left finite d).trans (Nat.pow_le_pow_right zp lim))
  have short : a ≤ looseExponent A S P := by
    rcases lt_trichotomy (A*p) (H*(p-1)) with low|pole|high
    · rcases under_first hp hq b low with short|impossible
      · have cap:= short.trans (Nat.div_le_self _ _)
        have ext : 4*S*(p-1)≤4*S*P := Nat.mul_le_mul_left _ ((Nat.sub_le _ _).trans pp)
        unfold looseExponent;omega
      · have cap:=Nat.div_le_self (2*A*p) (H*(p-1)-A*p)
        have sec:=Nat.mul_le_mul_left (2*A) pp
        dsimp [Z,lastCut] at finite;omega
    · have cap:=OMA.TwoFreeEffectivePole245212.original hh hp hq op cp cq pq ap dp pp pole
          (show P^4≤q by dsimp [Z,lastCut] at finite;omega)
          (show scalar A S<q by dsimp [Z,lastCut] at finite;omega)
          (show H<q by dsimp [Z,lastCut] at finite;omega) eqn
      unfold looseExponent;exact (by omega : a≤2*A+4*S*P+poleExponent (W h) (σ 1 h) P)
    · have cap:=(short_first hp hq high (strict hp hq sp b)).trans (Nat.div_le_self _ _)
      unfold looseExponent;omega
  apply (min_le_left ..).trans (le_trans _ (le_max_right ..))
  exact (Nat.pow_le_pow_left pp a).trans (Nat.pow_le_pow_right (hp.pos.trans_le pp) short)

theorem ordered {h p q a d : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime) (op : 3≤p)
    (cp : h.Coprime p) (cq : h.Coprime q) (pq : p<q) (ap : 0<a) (dp : 0<d)
    (eqn : OeisA245212.a (h*p^a*q^d)=(σ 1 (h*p^a*q^d):ℤ)) : h*p^a*q^d ≤ height h := by
  let B:=max 1 (atomBound (W h) (σ 1 h) (2*(h*σ 0 h)))
  have small : min (p^a) (q^d)≤B := (atom hh hp hq op cp cq pq ap dp eqn).trans (le_max_right ..)
  have pp:=hp.pos
  have qp:=hq.pos
  rcases le_total (p^a) (q^d) with first|second
  · rw [min_eq_left first] at small
    exact OMA.PairHeight245212.combine (by positivity : 0<h*p^a) (Nat.mul_le_mul_left h small)
      (OMA.PairHeight245212.last_square (by positivity) hq (by omega)
        (cq.mul_left (((coprime_primes hp hq).mpr pq.ne).pow_left a)) dp eqn)
  · rw [min_eq_right second] at small
    rw [mul_right_comm] at eqn ⊢
    exact OMA.PairHeight245212.combine (by positivity : 0<h*q^d) (Nat.mul_le_mul_left h small)
      (OMA.PairHeight245212.last_square (by positivity) hp (by omega)
        (cp.mul_left (((coprime_primes hq hp).mpr pq.ne.symm).pow_left d)) ap eqn)


private theorem absent {h q d : ℕ} (hh : 0<h) (hq : q.Prime) (oq : 3≤q) (cq : h.Coprime q)
    (eqn : OeisA245212.a (h*q^d)=(σ 1 (h*q^d):ℤ)) : h*q^d ≤ height h := by
  let B:=max 1 (atomBound (W h) (σ 1 h) (2*(h*σ 0 h)))
  have hb : h≤h*B := Nat.le_mul_of_pos_right _ (lt_of_lt_of_le (by decide : 0<1) (le_max_left ..))
  by_cases zero : d=0
  · subst d
    change h*1≤4*(h*B)^7
    have hpos : 0<h*B := hh.trans_le hb
    have growth : h*B≤(h*B)^7 := by simpa using Nat.pow_le_pow_right hpos (by decide : 1≤7)
    omega
  · exact OMA.PairHeight245212.combine hh hb (OMA.PairHeight245212.last_square hh hq (by omega) cq (by omega) eqn)

/-- Arbitrary order and arbitrary nonnegative exponents, so this includes
extensions by zero, one or two distinct odd primes. -/
theorem original {h p q a d : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime) (op : 3≤p) (oq : 3≤q)
    (cp : h.Coprime p) (cq : h.Coprime q) (ne : p≠q)
    (eqn : OeisA245212.a (h*p^a*q^d)=(σ 1 (h*p^a*q^d):ℤ)) : h*p^a*q^d ≤ height h := by
  by_cases empty : a=0
  · subst a;simp only [pow_zero,mul_one] at eqn ⊢;exact absent hh hq oq cq eqn
  by_cases empty' : d=0
  · subst d;simp only [pow_zero,mul_one] at eqn ⊢;exact absent hh hp op cp eqn
  rcases lt_or_gt_of_ne ne with pq|qp
  · exact ordered hh hp hq op cp cq pq (by omega) (by omega) eqn
  · rw [mul_right_comm] at eqn ⊢
    exact ordered hh hq hp oq cq cp qp (by omega) (by omega) eqn


/-- Prime-support form, including the empty odd cofactor m=1. -/
theorem of_rank {h m : ℕ} (hh : 0<h) (om : Odd m) (cop : h.Coprime m)
    (rank : m.primeFactors.card≤2) (eqn : OeisA245212.a (h*m)=(σ 1 (h*m):ℤ)) :
    h*m ≤ height h := by
  classical
  have props {r : ℕ} (mem : r∈m.primeFactors) : r.Prime ∧ 3≤r ∧ h.Coprime r := by
    have pr := Nat.prime_of_mem_primeFactors mem
    have dv := Nat.dvd_of_mem_primeFactors mem
    have od := Nat.coprime_two_left.mp ((Nat.coprime_two_left.mpr om).of_dvd_right dv)
    have ne : r≠2 := by rintro rfl; exact (by decide : ¬Odd 2) od
    exact ⟨pr,lt_of_le_of_ne pr.two_le ne.symm,cop.of_dvd_right dv⟩
  have repr := Nat.prod_primeFactors_pow_factorization om.pos.ne'
  by_cases two : m.primeFactors.card=2
  · obtain ⟨p,q,diff,s⟩:=card_eq_two.mp two
    obtain ⟨hp,op,cp⟩:=props (r:=p) (by simp [s])
    obtain ⟨hq,oq,cq⟩:=props (r:=q) (by simp [s])
    rw [s,prod_insert (by simpa using diff),prod_singleton] at repr
    have target:=congrArg (h*·) repr
    rw [←mul_assoc] at target
    rw [target] at eqn ⊢
    exact original hh hp hq op oq cp cq diff eqn
  by_cases one : m.primeFactors.card=1
  · obtain ⟨p,s⟩:=card_eq_one.mp one
    obtain ⟨hp,op,cp⟩:=props (r:=p) (by simp [s])
    rw [s,prod_singleton] at repr
    have target:=congrArg (h*·) repr
    rw [target] at eqn ⊢
    exact absent hh hp op cp eqn
  have empty : m.primeFactors=∅ := card_eq_zero.mp (by omega)
  rw [empty,prod_empty] at repr
  rw [repr,mul_one]
  let U:=max 1 (atomBound (W h) (σ 1 h) (2*(h*σ 0 h)))
  have hu : h≤h*U := Nat.le_mul_of_pos_right _ (lt_of_lt_of_le (by decide : 0<1) (le_max_left ..))
  have power : h*U≤(h*U)^7 := by simpa using Nat.pow_le_pow_right (hh.trans_le hu) (by decide : 1≤7)
  change h≤4*(h*U)^7;omega

end OMA.TwoFreeEffective245212

end

section

/- A monotone arithmetic height for all positive cofactors up to B. -/
namespace OMA.TwoFreeEffectiveUniform245212
open Nat ArithmeticFunction OMA.Smooth245212 OMA.TwoFreeEffective245212
open OMA.RankThreeFourSmallHarmonic245212 OMA.TwoFreeEffectivePole245212
open scoped ArithmeticFunction.sigma
open OMA.PairHeight245212 (moment_bound)
open OMA.PairHeight245212 (count_le)

def envelope (B : ℕ) :=
  let C:=2*B^3+1
  let P:=2*C*(C+4)
  let Z:=lastCut C C C P
  let X:=max (Z^finiteExponent C C Z) (P^looseExponent C C P)
  4*(B*max 1 X)^7

private theorem last_mono {A S H P C P' : ℕ} (a : A≤C) (s : S≤C) (h : H≤C) (p : P≤P') :
    lastCut A S H P ≤ lastCut C C C P' := by unfold lastCut scalar;gcongr

private theorem finite_mono {A S Z C Z' : ℕ} (a : A≤C) (s : S≤C) (z : Z≤Z') :
    finiteExponent A S Z ≤ finiteExponent C C Z' := by unfold finiteExponent;gcongr

private theorem loose_mono {A S P C P' : ℕ} (a : A≤C) (s : S≤C) (p : P≤P') :
    looseExponent A S P ≤ looseExponent C C P' := by unfold looseExponent poleExponent scale scalar multiplier;gcongr

theorem dominates {h B : ℕ} (hh : 0<h) (hb : h≤B) : height h ≤ envelope B := by
  let A:=W h
  let S:=σ 1 h
  let H:=2*(h*σ 0 h)
  let C:=2*B^3+1
  let P:=primeCut A S H
  let P':=2*C*(C+4)
  let Z:=lastCut A S H P
  let Z':=lastCut C C C P'
  have bpos : 0<B := hh.trans_le hb
  have cm:= (OMA.PairHeight245212.moment_bound hh).trans (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hb 3))
  have a : A≤C := by dsimp [A,C];omega
  have s : S≤C := by dsimp [S,C];omega
  have t : H≤C := by
    have c : σ 0 h≤B := by rw [sigma_zero_apply];exact (OMA.PairHeight245212.count_le h).trans hb
    have b2 : B^2≤B^3 := Nat.pow_le_pow_right bpos (by decide : 2≤3)
    have lim:=Nat.mul_le_mul hb c
    dsimp [H,C];nlinarith only [lim,b2]
  have l : lengthCut A S H≤C+4 := max_le (by omega) (by have := Nat.div_le_self S (H-A);omega)
  have p : P≤P' := (Nat.div_le_self _ _).trans (Nat.mul_le_mul (Nat.mul_le_mul_left 2 t) l)
  have z:=last_mono a s t p
  change Z≤Z' at z
  have pp : 0<P' := by dsimp [P',C];positivity
  have zp : 0<Z' := by dsimp [Z',lastCut];omega
  have one:= (Nat.pow_le_pow_left z (finiteExponent A S Z)).trans (Nat.pow_le_pow_right zp (finite_mono a s z))
  have two:= (Nat.pow_le_pow_left p (looseExponent A S P)).trans (Nat.pow_le_pow_right pp (loose_mono a s p))
  exact Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left (Nat.mul_le_mul hb
    (max_le_max le_rfl (max_le_max one two))) 7)


theorem monotone : Monotone envelope := by
  intro B D bd
  let C:=2*B^3+1
  let K:=2*D^3+1
  let P:=2*C*(C+4)
  let Q:=2*K*(K+4)
  let Z:=lastCut C C C P
  let Y:=lastCut K K K Q
  have c : C≤K := by dsimp [C,K];gcongr
  have p : P≤Q := by dsimp only [P,Q];gcongr
  have z : Z≤Y := last_mono c c c p
  have qp : 0<Q := by dsimp [Q,K];positivity
  have yp : 0<Y := by dsimp [Y,lastCut];omega
  have one:= (Nat.pow_le_pow_left z (finiteExponent C C Z)).trans (Nat.pow_le_pow_right yp (finite_mono c c z))
  have two:= (Nat.pow_le_pow_left p (looseExponent C C P)).trans (Nat.pow_le_pow_right qp (loose_mono c c p))
  exact Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left (Nat.mul_le_mul bd
    (max_le_max le_rfl (max_le_max one two))) 7)

theorem original {B h p q a d : ℕ} (hh : 0<h) (hb : h≤B) (hp : p.Prime) (hq : q.Prime)
    (op : 3≤p) (oq : 3≤q) (cp : h.Coprime p) (cq : h.Coprime q) (ne : p≠q)
    (eqn : OeisA245212.a (h*p^a*q^d)=(σ 1 (h*p^a*q^d):ℤ)) : h*p^a*q^d ≤ envelope B :=
  (OMA.TwoFreeEffective245212.original hh hp hq op oq cp cq ne eqn).trans (dominates hh hb)


/-- A uniform height for every odd cofactor of rank at most two. -/
theorem of_rank {B h m : ℕ} (hh : 0<h) (hb : h≤B) (om : Odd m) (cp : h.Coprime m)
    (rank : m.primeFactors.card≤2) (eqn : OeisA245212.a (h*m)=(σ 1 (h*m):ℤ)) :
    h*m ≤ envelope B :=
  (OMA.TwoFreeEffective245212.of_rank hh om cp rank eqn).trans (dominates hh hb)

end OMA.TwoFreeEffectiveUniform245212

end

#print axioms OMA.TwoFreeEffective245212.original
#print axioms OMA.TwoFreeEffectiveUniform245212.original
#print axioms OMA.TwoFreeEffectiveUniform245212.of_rank
#print axioms OMA.TwoFreeEffectiveUniform245212.monotone
