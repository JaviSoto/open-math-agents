import FormalConjectures.OEIS.«245212»

/-! Explicit dyadic height at arbitrary odd support size for OEIS A245212. -/

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

namespace OMA.ComplementaryLocal245212
open Finset ArithmeticFunction OMA.Smooth245212
open scoped ArithmeticFunction.sigma
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

theorem binary (k : ℕ) :
    (σ 1 (2^k):ℤ)=(2:ℤ)^(k+1)-1 ∧ (W (2^k):ℤ)=1+k*(2:ℤ)^(k+1) := by
  have h := moments Nat.prime_two k
  norm_num at h
  rw [pow_succ]; constructor <;> nlinarith only [h.1,h.2]


end OMA.ComplementaryLocal245212

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

namespace OMA.ThreeMovingLocal245212
open Nat Finset ArithmeticFunction OMA.Smooth245212 OMA.Abundance245212
open scoped ArithmeticFunction.sigma

def den (p e : ℕ) (round : Bool) := if round then (e+1)*(p-1)^2 else e+1
def xn (p e : ℕ) (round : Bool) := if round then p*((e+1)*(p-1)-1) else e+1
def yn (p _e : ℕ) (round : Bool) := if round then p*(p-1) else 1
def xx (p e : ℕ) (b : Bool) : ℚ := (xn p e b:ℚ)/den p e b
def yy (p e : ℕ) (b : Bool) : ℚ := (yn p e b:ℚ)/den p e b

theorem den_pos {p : ℕ} (hp : 2≤p) (e) (b) : 0<den p e b := by
  have:0<p-1:=by omega
  cases b <;> simp [den]
  positivity

theorem quotients {p e : ℕ} (hp : p.Prime) :
    let u:ℚ:=(p:ℚ)-1
    let B:ℚ:=(e:ℚ)+1
    let P:ℚ:=(p:ℚ)^e
    let δ : ℚ:=1/(B*u^2*P)
    X p (some e) = xx p e true+δ ∧
    Y p (some e) = yy p e true-u*δ := by
  have p2:=hp.two_le
  have pp : (1:ℚ)<p:=by exact_mod_cast hp.one_lt
  have Bp : (0:ℚ)<(e:ℚ)+1:=by positivity
  have uu : (p-1)*(e+1)≥1:=Nat.mul_pos (by omega) (by omega)
  have uu' : 1≤(e+1)*(p-1):=by simpa [mul_comm] using uu
  have id:=OMA.ComplementaryLocal245212.moments hp e
  have w:((p:ℚ)-1)^2*W (p^e)=p*(((e:ℚ)+1)*(p-1)-1)*(p:ℚ)^e+1 := by exact_mod_cast id.2
  have s:((p:ℚ)-1)*σ 1 (p^e)=p*(p:ℚ)^e-1 := by exact_mod_cast id.1
  have x:=x_factor hp e
  have y:=y_factor hp e
  dsimp [xx,yy,xn,yn,den]
  push_cast [Nat.cast_sub hp.one_le,Nat.cast_sub uu']
  constructor
  · field_simp [sub_ne_zero.mpr pp.ne',Bp.ne',(show (0:ℚ)<p by positivity).ne']
    linear_combination ((p:ℚ)-1)^2*x+w
  · field_simp [sub_ne_zero.mpr pp.ne',Bp.ne',(show (0:ℚ)<p by positivity).ne']
    linear_combination ((p:ℚ)-1)*y+s

theorem bounds {p e m : ℕ} (hp : p.Prime) (pe : 0<e) (mp : 0 < m) (sl : m≤e+1) (b : Bool) :
    1≤X p (some e) ∧ X p (some e)≤2 ∧ 0≤Y p (some e) ∧ Y p (some e)≤2/(m:ℚ) ∧
    1≤xx p e b ∧ xx p e b≤2 ∧ 0≤yy p e b ∧ yy p e b≤2/(m:ℚ) := by
  have pp : (2:ℚ)≤p := by exact_mod_cast hp.two_le
  have ep : (1:ℚ)≤e := by exact_mod_cast pe
  have md : (0:ℚ) < m := by exact_mod_cast mp
  have hl : (m:ℚ)≤(e:ℚ)+1 := by exact_mod_cast sl
  have bpos : (0:ℚ)<(e:ℚ)+1:=by positivity
  have ypos := y_nonneg hp.one_lt (some e)
  have ysm := y_one hp.one_lt (some e)
  have ub : Y p (some e)≤2/(m:ℚ) := (le_div_iff₀ md).mpr <|
    (mul_le_mul_of_nonneg_left hl ypos).trans (OMA.CapOrder245212.y_short hp e).le
  have xb : 1≤X p (some e) := le_add_of_nonneg_right (div_nonneg (sub_nonneg.mpr ysm) (by linarith))
  have xb' : X p (some e)≤2 := by
    dsimp [X]
    suffices (1-Y p (some e))/((p:ℚ)-1)≤1 by linarith
    apply (div_le_one₀ (by linarith)).mpr;linarith
  refine ⟨xb,xb',ypos,ub,?_⟩
  cases b with
  | false =>
    have a0 : xx p e false=1 := by simp [xx,xn,den,bpos.ne']
    have b0 : yy p e false=1/((e:ℚ)+1) := by simp [yy,yn,den]
    rw [a0,b0]
    refine ⟨by norm_num,by norm_num,by positivity,(div_le_div_iff₀ bpos md).mpr ?_⟩
    linarith
  | true =>
    have u : (0:ℚ)<(p:ℚ)-1:=by linarith
    have yw : yy p e true=(p:ℚ)/(((e:ℚ)+1)*(p-1)) := by
      dsimp [yy,yn,den];push_cast [Nat.cast_sub hp.one_le];field_simp
    have yw2 : yy p e true≤2/(m:ℚ) := by
      rw [yw,div_le_div_iff₀ (mul_pos bpos u) md]
      nlinarith only [mul_le_mul_of_nonneg_left hl (show (0:ℚ)≤p by positivity),
        mul_nonneg bpos.le (sub_nonneg.mpr pp)]
    have d0 : 0≤1/(((e:ℚ)+1)*((p:ℚ)-1)^2*(p:ℚ)^e) := by positivity
    have one : 1≤xx p e true := by
      dsimp [xx,xn,den]
      push_cast [Nat.cast_sub hp.one_le,Nat.cast_sub (Nat.mul_pos (by omega : 0<e+1) (by have:=hp.two_le;omega : 0<p-1))]
      rw [le_div_iff₀ (mul_pos bpos (sq_pos_of_pos u)),one_mul]
      nlinarith only [mul_nonneg (sub_nonneg.mpr ep) u.le,pp]
    exact ⟨one,(by linarith only [(quotients hp (e:=e)).1,xb',d0]),by rw [yw];positivity,yw2⟩

theorem move {p e f g m k : ℕ} (hp : p.Prime) (pe : 0<e) (mp : 0 < m)
    (ku : 0<k) (gu : 0<g) (fk : k*g≤f) (b : Bool)
    (small : b=true → 4*(p-1)<k*m^2)
    (x x' y y' : ℚ) (x0 : 1≤x) (x1 : 1≤x') (y0 : 0≤y) (y1 : 0≤y')
    (yl : y≤2/(m:ℚ)) (yl' : y'≤2/(m:ℚ)) :
    (f:ℚ)*xx p e b*x*x'+g*yy p e b*y*y' < f*X p (some e)*x*x'+g*Y p (some e)*y*y' := by
  have pp : (1:ℚ)<p:=by exact_mod_cast hp.one_lt
  have fg : (k:ℚ)*g≤f:=by exact_mod_cast fk
  have g0 : (0:ℚ)<g:=by exact_mod_cast gu
  have kp : (0:ℚ)<k:=by exact_mod_cast ku
  have fm : (0:ℚ)<f := lt_of_lt_of_le (mul_pos kp g0) fg
  have xl : (1:ℚ)≤x*x' := one_le_mul_of_one_le_of_one_le x0 x1
  have ylo := mul_nonneg y0 y1
  cases b with
  | false =>
    have ysum : 1/((e:ℚ)+1)≤Y p (some e) := by
      have id:=y_factor hp e
      have big : (p:ℚ)^e ≤ σ 1 (p^e) := by
        exact_mod_cast (show p^e ≤ σ 1 (p^e) by rw [sigma_one_apply_prime_pow hp,Finset.sum_range_succ];omega)
      apply (div_le_iff₀ (by positivity : (0:ℚ)<(e:ℚ)+1)).mpr
      apply le_of_mul_le_mul_right (a:=(p:ℚ)^e) _ (by positivity)
      nlinarith only [id,big]
    have ylt := y_strict hp.one_lt (show 0<e from pe)
    have xstrict : 1<X p (some e) := by
      dsimp [X];apply lt_add_of_pos_right;apply _root_.div_pos _ (by linarith)
      exact sub_pos.mpr (ylt.trans_le (y_one hp.one_lt _))
    have minus : 0<(f:ℚ)*(X p (some e)-1)*(x*x') := by positivity
    have plus := mul_nonneg (mul_nonneg g0.le (sub_nonneg.mpr ysum)) ylo
    have xx0 : xx p e false=1 := by simp [xx,xn,den,show (e:ℚ)+1≠0 by positivity]
    have yy0 : yy p e false=1/((e:ℚ)+1) := by simp [yy,yn,den]
    rw [xx0,yy0]
    nlinarith only [minus,plus]
  | true =>
    let u:ℚ:=(p:ℚ)-1
    let d:ℚ:=1/(((e:ℚ)+1)*u^2*(p:ℚ)^e)
    have dp : 0<d := by dsimp [d,u];positivity
    have us : (0:ℚ)≤u:=by dsimp [u];linarith
    have cap0 := mul_le_mul yl yl' y1 (by positivity)
    have cap : (y*y')*(m:ℚ)^2≤4 := by
      apply (le_div_iff₀ (sq_pos_of_pos (show (0:ℚ) < m by exact_mod_cast mp))).mp
      convert cap0 using 1; ring
    have gate : 4*u < (k:ℚ)*m^2 := by
      have sc : (4:ℚ)*((p-1:ℕ):ℚ)<k*(m:ℚ)^2 := by exact_mod_cast small rfl
      simpa [u,Nat.cast_sub hp.one_le] using sc
    have unc : u*(y*y')<(k:ℚ) := by
      apply lt_of_mul_lt_mul_right (a:=(m:ℚ)^2) _ (by positivity)
      nlinarith only [gate,mul_le_mul_of_nonneg_left cap us]
    have diff : 0<(f:ℚ)*x*x'-g*u*y*y' := by
      nlinarith only [mul_lt_mul_of_pos_left unc g0,mul_le_mul_of_nonneg_left xl fm.le,fg]
    have q:=quotients hp (e:=e)
    change X p (some e)=xx p e true+d ∧ Y p (some e)=yy p e true-u*d at q
    rw [q.1,q.2]
    nlinarith only [mul_pos dp diff]

/-- A rounded factor costs at most 2/p^e; a base omitted to infinity
costs at most 2/p. Both local moments obey the same estimate. -/
theorem error {p e N : ℕ} (hp : p.Prime) (he : 0<e) (hN : 0<N) (b : Bool)
    (space : N ≤ (if b then p^e else p)) :
    |X p (some e)-xx p e b|≤2/(N:ℚ) ∧ |Y p (some e)-yy p e b|≤2/(N:ℚ) := by
  let u:ℚ:=(p:ℚ)-1
  let B:ℚ:=(e:ℚ)+1
  let P:ℚ:=(p:ℚ)^e
  have ulo : 1≤u := by dsimp [u];linarith only [show (2:ℚ)≤p by exact_mod_cast hp.two_le]
  have blo : 1≤B := by dsimp [B];linarith only [Nat.cast_nonneg (α:=ℚ) e]
  have up : 0<u := by linarith
  have bp : 0<B := by linarith
  have pp : 0<P := pow_pos (by exact_mod_cast hp.pos) _
  have np : (0:ℚ)<N := by exact_mod_cast hN
  let d:=1/(B*u^2*P)
  have dp : 0≤d := by dsimp [d];positivity
  have pairs:=quotients hp (e:=e)
  change X p (some e)=xx p e true+d ∧ Y p (some e)=yy p e true-u*d at pairs
  cases b with
  | true =>
    change N≤p^e at space
    have sg : (N:ℚ)≤P:=by dsimp [P];exact_mod_cast space
    have du : u*d=1/(B*u*P) := by dsimp [d];field_simp
    have ud : u*d≤2/(N:ℚ) := by
      rw [du,div_le_div_iff₀ (by positivity) np]
      have big : P≤B*u*P := le_mul_of_one_le_left pp.le (one_le_mul_of_one_le_of_one_le blo ulo)
      linarith
    rw [pairs.1,pairs.2,add_sub_cancel_left,sub_sub_cancel_left,abs_neg,abs_of_nonneg dp,abs_of_nonneg (mul_nonneg up.le dp)]
    exact ⟨(le_mul_of_one_le_left dp ulo).trans ud,ud⟩
  | false =>
    change N≤p at space
    have small : (N:ℚ)≤2*u := by
      have pp : (2:ℚ)≤p:=by exact_mod_cast hp.two_le
      dsimp [u];linarith only [pp,show (N:ℚ)≤p by exact_mod_cast space]
    have frac : 1/u ≤ 2/(N:ℚ):= (div_le_div_iff₀ up np).mpr (by linarith)
    have xr:= (bounds hp he (by decide : 0<1) (by omega) false).1
    have xe : X p (some e)-1≤1/u := by dsimp [X,u];rw [add_sub_cancel_left];gcongr;exact sub_le_self _ (y_nonneg hp.one_lt _)
    have yupper : yy p e true-1/B=1/(B*u) := by
      dsimp [yy,yn,den,u,B];push_cast [Nat.cast_sub hp.one_le];field_simp [show (p:ℚ)-1≠0 from up.ne'];ring
    have lower : 1/B≤Y p (some e) := by
      apply (div_le_iff₀ bp).mpr
      apply le_of_mul_le_mul_right (a:=P) _ pp
      have big : (p:ℚ)^e ≤ σ 1 (p^e) := by
        exact_mod_cast (show p^e ≤ σ 1 (p^e) by rw [sigma_one_apply_prime_pow hp,Finset.sum_range_succ];omega)
      dsimp [B,P];nlinarith only [y_factor hp e,big]
    have pre : Y p (some e)-1/B≤1/(B*u) := by
      nlinarith only [pairs.2,yupper,mul_nonneg up.le dp]
    have s : 1/(B*u) ≤ 1/u := one_div_le_one_div_of_le up (le_mul_of_one_le_left up.le blo)
    have xx0 : xx p e false=1 := by simp [xx,xn,den,show (e:ℚ)+1≠0 by positivity]
    have yy0 : yy p e false=1/B := by simp [yy,yn,den,B]
    rw [xx0,yy0,abs_of_nonneg (sub_nonneg.mpr xr),abs_of_nonneg (sub_nonneg.mpr lower)]
    exact ⟨xe.trans frac,pre.trans (s.trans frac)⟩

end OMA.ThreeMovingLocal245212

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

namespace OMA.CofactorCrossOriginal245212
open Nat Finset ArithmeticFunction OMA.Smooth245212
open scoped ArithmeticFunction.sigma

private theorem sigma_bound {h : ℕ} (pos : 0<h) : σ 1 h≤h*σ 0 h := by
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


end OMA.CofactorCrossOriginal245212

namespace OMA.CofactorEffectiveAtom245212
open Finset Nat
theorem product_error {ι : Type*} [DecidableEq ι] (s : Finset ι) (x z : ι→ℚ)
    {w : ℚ} (wp : 0≤w) (bounds : ∀i∈s,0≤x i ∧ x i≤2 ∧ 0≤z i ∧ z i≤2 ∧ |x i-z i|≤w) :
    |(∏i∈s,x i)-(∏i∈s,z i)| ≤ s.card*(2:ℚ)^s.card*w := by
  induction s using Finset.induction_on with
  | empty=>simp
  | @insert i s fresh ih=>
    let X:=∏j∈s,x j
    let Z:=∏j∈s,z j
    have b:=bounds i (mem_insert_self ..)
    have bs (j) (hj:j∈s):=bounds j (mem_insert_of_mem hj)
    have z0 : 0≤Z:=prod_nonneg (fun j hj=>(bs j hj).2.2.1)
    have z2 : Z≤(2:ℚ)^s.card := by
      simpa [Z] using prod_le_prod (fun j hj=>(bs j hj).2.2.1) (fun j hj=>(bs j hj).2.2.2.1)
    have old:=ih bs
    change |X-Z|≤_ at old
    rw [prod_insert fresh,prod_insert fresh,card_insert_of_notMem fresh,Nat.cast_add,Nat.cast_one,pow_succ]
    change |x i*X-z i*Z|≤_
    have tri:=abs_add_le (x i*(X-Z)) ((x i-z i)*Z)
    rw [show x i*(X-Z)+(x i-z i)*Z=x i*X-z i*Z by ring,abs_mul,abs_of_nonneg b.1,
      abs_mul,abs_of_nonneg z0] at tri
    have l:=mul_le_mul b.2.1 old (abs_nonneg _) (by decide : (0:ℚ)≤2)
    have r:=mul_le_mul b.2.2.2.2 z2 z0 wp
    nlinarith only [tri,l,r,mul_nonneg (pow_nonneg (by decide : (0:ℚ)≤2) s.card) wp]

private def factor (p : ℕ) : ℚ := (p:ℚ)/(p-1:ℕ)

end OMA.CofactorEffectiveAtom245212

namespace OMA.BoundedAtom245212
open Finset OMA.Smooth245212
open scoped ArithmeticFunction.sigma
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


end OMA.BoundedAtom245212

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

namespace OMA.DyadicLeast245212
open Finset Nat ArithmeticFunction OMA.Smooth245212
open scoped ArithmeticFunction.sigma
open OMA.FixedExponents245212 (x_avg)
open OMA.FixedExponents245212 (y_pos)

def term (p e : ℕ) : ℚ := (e:ℚ)/(((e:ℚ)+1)*p)

theorem x_two_terms {p e : ℕ} (hp : p.Prime) (he : 0<e) :
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


end OMA.DyadicLeast245212

namespace OMA.ThreeMovingOriginal245212
def F (k : ℕ) := 1+k*2^(k+1)
def G (k : ℕ) := 2^(k+1)-1

end OMA.ThreeMovingOriginal245212

namespace OMA.TwoTallLocal245212
open Nat Finset ArithmeticFunction OMA.Smooth245212 OMA.Abundance245212 OMA.ThreeMovingLocal245212
open scoped ArithmeticFunction.sigma
open OMA.ThreeMovingLocal245212 (quotients)

def Dn (p e : ℕ) : Option Bool → ℕ
  | none => (e+1)*p^e
  | some b => den p e b
def Nx (p e : ℕ) : Option Bool → ℕ
  | none => W (p^e)
  | some b => xn p e b
def Ny (p e : ℕ) : Option Bool → ℕ
  | none => σ 1 (p^e)
  | some b => yn p e b
def xx' (p e : ℕ) : Option Bool → ℚ
  | none => X p (some e)
  | some b => xx p e b
def yy' (p e : ℕ) : Option Bool → ℚ
  | none => Y p (some e)
  | some b => yy p e b
theorem Dpos {p : ℕ} (hp : p.Prime) (e : ℕ) (mode : Option Bool) : 0<Dn p e mode := by
  cases mode with
  | none =>exact Nat.mul_pos (Nat.succ_pos _) (pow_pos hp.pos _)
  | some b=>exact den_pos hp.two_le e b

theorem moments {p : ℕ} (hp : p.Prime) (e : ℕ) (mode : Option Bool) :
    xx' p e mode*(Dn p e mode:ℕ)=Nx p e mode ∧ yy' p e mode*(Dn p e mode:ℕ)=Ny p e mode := by
  cases mode with
  | none =>simpa [xx',yy',Dn,Nx,Ny,mul_assoc] using And.intro (x_factor hp e) (y_factor hp e)
  | some b=>
    have dp : (den p e b:ℚ)≠0:=by exact_mod_cast (den_pos hp.two_le e b).ne'
    simp [xx',yy',Dn,Nx,Ny,xx,yy,div_mul_cancel₀ _ dp]

theorem ranges {p e : ℕ} (hp : p.Prime) (pe : 0<e) (mode : Option Bool) :
    1≤xx' p e mode ∧ xx' p e mode≤2 ∧ 0≤yy' p e mode ∧ yy' p e mode≤2/((e:ℚ)+1) := by
  have a (b : Bool):=bounds hp pe (Nat.succ_pos e) (le_refl (e+1)) b
  cases mode with
  | none =>simpa [xx',yy'] using And.intro (a false).1 (And.intro (a false).2.1
      (And.intro (a false).2.2.1 (a false).2.2.2.1))
  | some b=>simpa [xx',yy'] using (a b).2.2.2.2

theorem move {p e f g m k : ℕ} (hp : p.Prime) (pe : 0<e) (mp : 0 < m)
    (ku : 0<k) (gu : 0<g) (fk : k*g≤f) (b : Bool)
    (small : b=true → 4*(p-1)<k*m)
    (x x' y y' : ℚ) (x0 : 1≤x) (x1 : 1≤x') (y0 : 0≤y) (y1 : 0≤y')
    (cap : (y*y')*(m:ℚ)≤4) :
    (f:ℚ)*xx p e b*x*x'+g*yy p e b*y*y' < f*X p (some e)*x*x'+g*Y p (some e)*y*y' := by
  have pp : (1:ℚ)<p:=by exact_mod_cast hp.one_lt
  have fg : (k:ℚ)*g≤f:=by exact_mod_cast fk
  have g0 : (0:ℚ)<g:=by exact_mod_cast gu
  have kp : (0:ℚ)<k:=by exact_mod_cast ku
  have fm : (0:ℚ)<f := lt_of_lt_of_le (mul_pos kp g0) fg
  have xl : (1:ℚ)≤x*x' := one_le_mul_of_one_le_of_one_le x0 x1
  have ylo := mul_nonneg y0 y1
  cases b with
  | false =>
    have ysum : 1/((e:ℚ)+1)≤Y p (some e) := by
      have id:=y_factor hp e
      have big : (p:ℚ)^e ≤ σ 1 (p^e) := by
        exact_mod_cast (show p^e ≤ σ 1 (p^e) by rw [sigma_one_apply_prime_pow hp,Finset.sum_range_succ];omega)
      apply (div_le_iff₀ (by positivity : (0:ℚ)<(e:ℚ)+1)).mpr
      apply le_of_mul_le_mul_right (a:=(p:ℚ)^e) _ (by positivity)
      nlinarith only [id,big]
    have ylt := y_strict hp.one_lt (show 0<e from pe)
    have xstrict : 1<X p (some e) := by
      dsimp [X];apply lt_add_of_pos_right;apply _root_.div_pos _ (by linarith)
      exact sub_pos.mpr (ylt.trans_le (y_one hp.one_lt _))
    have minus : 0<(f:ℚ)*(X p (some e)-1)*(x*x') := by positivity
    have plus := mul_nonneg (mul_nonneg g0.le (sub_nonneg.mpr ysum)) ylo
    have xx0 : xx p e false=1 := by simp [xx,xn,den,show (e:ℚ)+1≠0 by positivity]
    have yy0 : yy p e false=1/((e:ℚ)+1) := by simp [yy,yn,den]
    rw [xx0,yy0]
    nlinarith only [minus,plus]
  | true =>
    let u:ℚ:=(p:ℚ)-1
    let d:ℚ:=1/(((e:ℚ)+1)*u^2*(p:ℚ)^e)
    have dp : 0<d := by dsimp [d,u];positivity
    have us : (0:ℚ)≤u:=by dsimp [u];linarith
    have gate : 4*u < (k:ℚ)*m := by
      have sc : (4:ℚ)*((p-1:ℕ):ℚ)<k*(m:ℚ) := by exact_mod_cast small rfl
      simpa [u,Nat.cast_sub hp.one_le] using sc
    have unc : u*(y*y')<(k:ℚ) := by
      apply lt_of_mul_lt_mul_right (a:=(m:ℚ)) _ (by positivity)
      nlinarith only [gate,mul_le_mul_of_nonneg_left cap us]
    have diff : 0<(f:ℚ)*x*x'-g*u*y*y' := by
      nlinarith only [mul_lt_mul_of_pos_left unc g0,mul_le_mul_of_nonneg_left xl fm.le,fg]
    have q:=OMA.ThreeMovingLocal245212.quotients hp (e:=e)
    change X p (some e)=xx p e true+d ∧ Y p (some e)=yy p e true-u*d at q
    rw [q.1,q.2]
    nlinarith only [mul_pos dp diff]

end OMA.TwoTallLocal245212

namespace OMA.TwoTallScalar245212
def base (k L : ℕ) := 128*(k+2)*(L+1)
end OMA.TwoTallScalar245212

namespace OMA.SingleMovingLoss245212
open Nat Finset OMA.Smooth245212 OMA.TwoTallLocal245212
open OMA.ThreeMovingLocal245212 (xx yy)
open OMA.ThreeMovingLocal245212 (quotients)
open OMA.DyadicLeast245212 (x_two_terms)

theorem single_lb {p e : ℕ} (hp : p.Prime) (he : 0<e) :
    1≤(2*(p:ℚ))*(X p (some e)-1) := by
  have r:=OMA.DyadicLeast245212.x_two_terms hp he
  change 1+(e:ℚ)/((e+1)*p)≤_ at r
  have z : 0<((e:ℚ)+1)*p := by have:=hp.pos;positivity
  have z' := (div_le_iff₀ z).mp (by linarith only [r] : (e:ℚ)/((e+1)*p)≤X p (some e)-1)
  have q : (1:ℚ)≤e:=by exact_mod_cast he
  by_contra! bad
  have mul:=mul_lt_mul_of_pos_right bad (by positivity : 0<(e:ℚ)+1)
  nlinarith only [z',q,mul]

theorem scalar {k p e : ℕ} (hk : 8≤k) (kp : k+1<p) (len : p≤e+1) :
    8*p*(2^(k+1)-1)≤p^e := by
  have k4 : 4≤k:=by omega
  have c : 16≤2^k := (by decide : 16≤2^4).trans (Nat.pow_le_pow_right (by decide) k4)
  have ep : k+1≤e:=by omega
  calc
    _ ≤ 8*p*(2^(k+1)) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    _ = p*(2^k*16) := by rw [pow_succ];ring
    _ ≤ p*(2^k*2^k) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ c)
    _ = p*(2*2)^k := by rw [mul_pow]
    _ ≤ p*p^k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    _ = p^(k+1) := (pow_succ' ..).symm
    _ ≤ p^e := Nat.pow_le_pow_right (by omega) ep

/-- Returns a coordinate from any of the three proxy choices. The comparison
tests u*y*y' against k, keeping the product of the *other* ordinary factors. -/
theorem restore {p e k : ℕ} (hp : p.Prime) (ep : 0<e) (kp : 0<k) (mode : Option Bool)
    (x x' y y' allowance : ℚ) (xp : 1≤x) (xp' : 1≤x') (yp : 0≤y) (yp' : 0≤y')
    (yl : y*y'≤1) (dl : 0≤allowance)
    (bad : mode=some true → (k:ℚ)<((p:ℚ)-1)*(y*y') → 1/(p:ℚ)^e≤allowance) :
    (k:ℚ)*xx' p e mode*x*x'+yy' p e mode*y*y' ≤
    (k:ℚ)*X p (some e)*x*x'+Y p (some e)*y*y'+allowance := by
  cases mode with
  | none=> dsimp [xx',yy'];linarith
  | some t=>
    cases t with
    | false=>
      have v:=OMA.TwoTallLocal245212.move hp ep (by decide : 0 < (1:ℕ)) kp (by decide : 0<(1:ℕ))
        (le_refl (k*1)) false (by simp) x x' y y' xp xp' yp yp' (by norm_num;linarith)
      dsimp [xx',yy'];push_cast at v;linarith only [v,dl]
    | true=>
      let u:ℚ:=(p:ℚ)-1
      let H:ℚ:=(e:ℚ)+1
      let d:ℚ:=1/(H*u^2*(p:ℚ)^e)
      have u1 : 1≤u:=by dsimp [u];have z:=(by exact_mod_cast hp.two_le : (2:ℚ)≤p);linarith
      have h1 : 1≤H:=by dsimp [H];have z:=Nat.cast_nonneg (α:=ℚ) e;linarith
      have po : (0:ℚ)<(p:ℚ)^e:=pow_pos (by exact_mod_cast hp.pos) _
      have dpos : 0<d:=by dsimp [d];positivity
      have vk : 0≤(k:ℚ)*(x*x'):=mul_nonneg (by positivity) (mul_nonneg (by linarith) (by linarith))
      have xy : 1≤x*x':=one_le_mul_of_one_le_of_one_le xp xp'
      have m:=OMA.ThreeMovingLocal245212.quotients hp (e:=e)
      change X p (some e)=xx p e true+d ∧ Y p (some e)=yy p e true-u*d at m
      change _*xx p e true*x*x'+yy p e true*y*y'≤_
      rw [m.1,m.2]
      by_cases good : u*(y*y')≤k
      · have more:=(mul_le_mul_of_nonneg_left xy (Nat.cast_nonneg (α:=ℚ) k))
        have dif : 0≤(k:ℚ)*x*x'-u*(y*y'):=by linarith [good,more]
        nlinarith only [mul_nonneg dpos.le dif,dl]
      · have limit:=bad rfl (lt_of_not_ge good)
        have ud : u*d=1/((H*u)*(p:ℚ)^e) := by dsimp [d];field_simp
        have abd : u*d≤1/(p:ℚ)^e := by
          rw [ud]
          exact one_div_le_one_div_of_le po (le_mul_of_one_le_left po.le (one_le_mul_of_one_le_of_one_le h1 u1))
        have loss:=mul_le_mul_of_nonneg_left yl (mul_nonneg (by linarith : 0≤u) dpos.le)
        nlinarith only [loss,abd,limit,mul_nonneg dpos.le vk]

end OMA.SingleMovingLoss245212

namespace OMA.SingleMovingHeight245212
open OMA.ThreeMovingOriginal245212 (G)
open OMA.TwoTallScalar245212 (base)
def constant (D : ℕ) := 2^(16*(D+2)^2+8)+(16*128^D)^2

private theorem eliminate {k L D : ℕ}
    (h : 2^k ≤ 8*(k+1)*(base k L)^D) :
    2^k ≤ constant D*(L+1)^(2*D) := by
  have pos : 1≤(L+1)^(2*D):=Nat.one_le_pow _ _ (by omega)
  by_cases large : 16*(D+2)^2≤k+2
  · have grow:=OMA.ComplementarySize245212.absorb (b:=k+2) (d:=D+1) (by simpa [Nat.add_assoc] using large)
    let C : ℕ := 8*128^D
    have e : 2^k≤C*(k+2)^(D+1)*(L+1)^D := calc
      _ ≤ _ := h
      _ ≤ 8*(k+2)*(base k L)^D := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by simp only [base,mul_pow,C,pow_succ];ring
    have z:=Nat.pow_le_pow_left e 2
    have powers : ((k+2)^(D+1))^2 ≤ 2^k*4 := by
      rw [←pow_mul,mul_comm (D+1) 2,←show (2:ℕ)^(k+2)=2^k*4 by rw [pow_add];rfl]
      exact grow
    have w : 2^k*2^k ≤ 2^k*((16*128^D)^2*(L+1)^(2*D)) := calc
      _ = (2^k)^2 := (sq _).symm
      _ ≤ _ := z
      _ = C^2*((k+2)^(D+1))^2*((L+1)^D)^2 := by ring
      _ ≤ C^2*(2^k*4)*((L+1)^D)^2 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ powers)
      _ = _ := by rw [←pow_mul,mul_comm D 2];dsimp [C];ring
    exact (Nat.le_of_mul_le_mul_left w (Nat.two_pow_pos k)).trans
      (Nat.mul_le_mul_right _ (Nat.le_add_left _ _))
  · have top : k≤16*(D+2)^2+8:=by omega
    have bounded := Nat.pow_le_pow_right (by decide : 1≤2) top
    exact bounded.trans ((Nat.le_add_right _ _).trans (Nat.le_mul_of_pos_right _ pos))

theorem all_k {k L D : ℕ}
    (coarse : 8≤k → G k < 8*(k+1)*(base k L)^D) :
    2^k ≤constant D*(L+1)^(2*D) := by
  by_cases hk : 8≤k
  · have h := coarse hk
    have ge : 2^k≤G k:=by
      have := Nat.two_pow_pos k
      dsimp [G];rw [pow_succ];omega
    exact eliminate (ge.trans h.le)
  · have : 2^k≤(2:ℕ)^8:=Nat.pow_le_pow_right (by decide) (by omega)
    have high : (2:ℕ)^8≤2^(16*(D+2)^2+8):=Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _)
    exact this.trans (high.trans ((Nat.le_add_right _ _).trans (Nat.le_mul_of_pos_right _
      (pow_pos (by omega) _))))

end OMA.SingleMovingHeight245212


/- Cleared moments and the restriction on every retained prime. -/
namespace OMA.FixedRankGap245212
open Nat Finset OMA.Smooth245212 OMA.TwoTallLocal245212

structure Family (r : ℕ) where
  p : Fin r→ℕ
  e : Fin r→ℕ
  k : ℕ
  L : ℕ
  prime : ∀i,(p i).Prime
  positive : ∀i,0<e i
  kp : 8≤k
  longest : ∃i,e i+1=L
  cap : ∀i,e i+1≤L
  inj : p.Injective

variable {r : ℕ}

def exactX (c : Family r) (i : Fin r) := X (c.p i) (some (c.e i))
def exactY (c : Family r) (i : Fin r) := Y (c.p i) (some (c.e i))
def x' (c : Family r) (b : Fin r→Option Bool) (i : Fin r) := xx' (c.p i) (c.e i) (b i)
def y' (c : Family r) (b : Fin r→Option Bool) (i : Fin r) := yy' (c.p i) (c.e i) (b i)
def dust (c : Family r) (b : Fin r→Option Bool) := ∏i,Dn (c.p i) (c.e i) (b i)
def NX (c : Family r) (b : Fin r→Option Bool) := ∏i,Nx (c.p i) (c.e i) (b i)
def NY (c : Family r) (b : Fin r→Option Bool) := ∏i,Ny (c.p i) (c.e i) (b i)
def score (f g : ℕ) (x y : Fin r→ℚ) := (f:ℚ)*(∏i,x i)+(g:ℚ)*(∏i,y i)

theorem dust_pos (c : Family r) (b : Fin r→Option Bool) : 0<dust c b :=
  prod_pos (fun i _=>Dpos (c.prime i) _ _)

theorem clear (c : Family r) (b : Fin r→Option Bool) (f g : ℕ) :
    score f g (x' c b) (y' c b)*dust c b=(f*NX c b+g*NY c b:ℕ) := by
  have w : (∏i,x' c b i)*(dust c b:ℚ)=NX c b := by
    dsimp [dust,NX,x'];push_cast;rw [←prod_mul_distrib]
    exact prod_congr rfl (fun i _=>(moments (c.prime i) (c.e i) (b i)).1)
  have s : (∏i,y' c b i)*(dust c b:ℚ)=NY c b := by
    dsimp [dust,NY,y'];push_cast;rw [←prod_mul_distrib]
    exact prod_congr rfl (fun i _=>(moments (c.prime i) (c.e i) (b i)).2)
  dsimp [score];push_cast
  linear_combination (f:ℚ)*w+(g:ℚ)*s


private theorem largest {c : Family r} {b : Fin r→Option Bool} {f g l : ℕ} (frac : f+g=(c.k+1)*l)
    (unit : ∀i,¬c.p i∣l) (hit : (f+g)*dust c b=f*NX c b+g*NY c b) :
    ∀i,b i=some true → c.p i≤ max (c.k+1) c.L := by
  classical
  let s:=univ.filter (fun j=>b j=some true)
  intro i hi
  have im : i∈s:=mem_filter.mpr ⟨mem_univ _,hi⟩
  obtain ⟨j,jm,top⟩:=s.exists_max_image c.p ⟨i,im⟩
  have sh: b j=some true := (mem_filter.mp jm).2
  let q:=c.p j
  have pr:=c.prime j
  have dn : q∣NX c b := by
    apply dvd_trans (b:=Nx (c.p j) (c.e j) (b j)) _ (dvd_prod_of_mem (fun i=>Nx (c.p i) (c.e i) (b i)) (mem_univ j))
    simp [Nx,OMA.ThreeMovingLocal245212.xn,sh,q]
  have ds : q∣NY c b := by
    apply dvd_trans (b:=Ny (c.p j) (c.e j) (b j)) _ (dvd_prod_of_mem (fun i=>Ny (c.p i) (c.e i) (b i)) (mem_univ j))
    simp [Ny,OMA.ThreeMovingLocal245212.yn,sh,q]
  have total : q∣(f+g)*dust c b := hit ▸ dvd_add (dvd_mul_of_dvd_right dn f) (dvd_mul_of_dvd_right ds g)
  apply (top _ im).trans
  by_contra! no
  change max (c.k+1) c.L < q at no
  rw [frac] at total
  rcases pr.dvd_mul.mp total with h|h
  · rcases pr.dvd_mul.mp h with small|bad
    · exact (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) small
    · exact unit j bad
  · obtain ⟨i',_,v⟩:=(pr.prime.dvd_finsetProd_iff _).mp h
    have le0:=c.cap i'
    have absent := Nat.not_dvd_of_pos_of_lt (by omega : 0<c.e i'+1) (by omega : c.e i'+1<q)
    change q∣Dn (c.p i') (c.e i') (b i') at v
    cases which : b i' with
    | none =>
      rw [which] at v
      rcases pr.dvd_mul.mp v with hit|hit
      · exact absent hit
      have same:=c.inj ((prime_dvd_prime_iff_eq pr (c.prime i')).mp (pr.dvd_of_dvd_pow hit))
      exact (by rw [←same,sh] at which; contradiction)
    | some bit =>
      cases bit with
      | false => rw [which] at v;exact absent v
      | true =>
        have mt : i'∈s:=mem_filter.mpr ⟨mem_univ _,which⟩
        have sz:=top i' mt
        rw [which] at v
        rcases pr.dvd_mul.mp v with bad|bad
        · exact absent bad
        · exact Nat.not_dvd_of_pos_of_lt (by have:=(c.prime i').two_le;omega : 0<c.p i'-1)
            (by omega) (pr.dvd_of_dvd_pow bad)


theorem retained {c : Family r} {b : Fin r→Option Bool} {f g l : ℕ} (frac : f+g=(c.k+1)*l)
    (unit : ∀i,¬c.p i∣l) (hit : (f+g)*dust c b=f*NX c b+g*NY c b) :
    ∀i,b i=some true → c.p i≤ max (c.k+1) c.L := largest frac unit hit

end OMA.FixedRankGap245212


/- The actual dyadic deficit exceeds the total possible loss caused by
all risky rounded coordinates, without any comparability assumption. -/
namespace OMA.FixedRankProxy245212
open Nat Finset OMA.FixedRankGap245212 OMA.TwoTallLocal245212
open OMA.ThreeMovingOriginal245212 (G)
variable {r : ℕ}

def deficit (c : Family r) : ℚ := (c.k:ℚ)+1-score c.k 1 (exactX c) (exactY c)

theorem lower (c : Family r) (link : deficit c*(G c.k:ℕ)=((c.k:ℚ)+1)*((∏i,exactX c i)-1)) (i) :
    1≤(2*(c.p i:ℚ))*(G c.k)*(deficit c) := by
  have xb j : 1≤exactX c j:=(ranges (c.prime j) (c.positive j) none).1
  have xi : exactX c i≤∏j,exactX c j := by
    rw [←prod_erase_mul (univ : Finset (Fin r)) (exactX c) (mem_univ i)]
    exact le_mul_of_one_le_left (zero_le_one.trans (xb _)) (one_le_prod (fun j _=>xb j))
  have localBound:=OMA.SingleMovingLoss245212.single_lb (c.prime i) (c.positive i)
  change 1≤(2*(c.p i:ℚ))*(exactX c i-1) at localBound
  have xm : 0≤(∏j,exactX c j)-1:=by linarith only [xi,xb i]
  have more:=mul_nonneg (Nat.cast_nonneg (α:=ℚ) c.k) xm
  have cc : 0≤2*(c.p i:ℚ):=by positivity
  nlinarith only [localBound,mul_le_mul_of_nonneg_left xi cc,mul_nonneg cc more,
    congrArg (fun z:ℚ=>2*(c.p i:ℚ)*z) link]


set_option maxHeartbeats 1200000 in
/-- All coordinates apart from one longest coordinate have nonnegative
restoration, regardless of how many other coordinates there are. -/
theorem separated (c : Family r) (b : Fin r→Option Bool)
    (link : deficit c*(G c.k:ℕ)=((c.k:ℚ)+1)*((∏i,exactX c i)-1)) :
    (c.k+1)*dust c b ≠ c.k*NX c b+NY c b := by
  classical
  obtain ⟨v,vbig⟩:=c.longest
  have gd : 0<deficit c := by
    have h:=lower c link v
    by_contra! n
    have t:=mul_nonpos_of_nonneg_of_nonpos (show 0≤2*(c.p v:ℚ)*(G c.k:ℕ) by positivity) n
    linarith
  intro hit
  have scale:=retained (b:=b) (f:=c.k) (g:=1) (l:=1) (by simp)
    (fun i=>Nat.not_dvd_of_pos_of_lt (by decide) (c.prime i).one_lt) (by simpa using hit)
  let mix (s : Finset (Fin r)) (i : Fin r) := if i∈s then exactX c i else x' c b i
  let miy (s : Finset (Fin r)) (i : Fin r) := if i∈s then exactY c i else y' c b i
  let val (s : Finset (Fin r)):=score c.k 1 (mix s) (miy s)
  have adv (s : Finset (Fin r)) {i} (fresh : i∉s) :
      val s ≤ val (insert i s)+(if i=v then deficit c/4 else 0) := by
    have bound j : 1≤ mix s j ∧ 0≤ miy s j ∧ miy s j≤2/((c.e j:ℚ)+1) := by
      by_cases mem : j∈s
      · have w:=ranges (c.prime j) (c.positive j) none
        simpa only [mix,miy,if_pos mem,exactX,exactY,xx',yy'] using And.intro w.1 w.2.2
      · have w:=ranges (c.prime j) (c.positive j) (b j)
        simpa only [mix,miy,if_neg mem,x',y'] using And.intro w.1 w.2.2
    have size j : miy s j≤1 := (bound j).2.2.trans ((div_le_iff₀ (by positivity)).mpr (by
      have:= (by exact_mod_cast c.positive j : (1:ℚ)≤c.e j);linarith))
    let t:=(univ:Finset (Fin r)).erase i
    let xx:=∏j∈t,mix s j
    let yy:=∏j∈t,miy s j
    have x1 : 1≤xx:=one_le_prod (fun j _=>(bound j).1)
    have y0 : 0≤yy:=prod_nonneg (fun j _=>(bound j).2.1)
    have y1 : yy≤1:=prod_le_one (fun j _=>(bound j).2.1) (fun j _=>size j)
    have sameX : ∏j∈t,mix (insert i s) j=xx := Finset.prod_congr rfl (by
      intro j hj
      have ji:=ne_of_mem_erase hj
      simp [mix,Finset.mem_insert,ji])
    have sameY : ∏j∈t,miy (insert i s) j=yy := Finset.prod_congr rfl (by
      intro j hj
      have ji:=ne_of_mem_erase hj
      simp [miy,Finset.mem_insert,ji])
    have step:=OMA.SingleMovingLoss245212.restore (c.prime i) (c.positive i)
      (by have:=c.kp;omega : 0<c.k) (b i) xx 1 yy 1
      (if i=v then deficit c/4 else 0) x1 le_rfl y0 zero_le_one
      (by simpa only [mul_one] using y1) (by split <;> positivity)
    have bad (bit : b i=some true) (risk : (c.k:ℚ)<((c.p i:ℚ)-1)*(yy*1)) :
        1/(c.p i:ℚ)^(c.e i) ≤ if i=v then deficit c/4 else 0 := by
      simp only [mul_one] at risk
      have u0 : 0≤(c.p i:ℚ)-1:=by have z:=(by exact_mod_cast (c.prime i).one_le : (1:ℚ)≤c.p i);linarith
      have pk : c.k+1<c.p i := by
        have up:=mul_le_mul_of_nonneg_left y1 u0
        exact_mod_cast (show (c.k:ℚ)+1<c.p i by linarith only [up,risk])
      have pL : c.p i≤c.L:=by have:=scale i bit;omega
      have unique : i=v := by
        by_contra iv
        have vm : v∈t:=mem_erase.mpr ⟨Ne.symm iv,mem_univ _⟩
        have rest : ∏j∈t.erase v,miy s j≤1:=prod_le_one (fun j _=>(bound j).2.1) (fun j _=>size j)
        have yv : yy ≤ miy s v := by
          dsimp [yy];rw [←prod_erase_mul t (miy s) vm]
          simpa only [one_mul] using mul_le_mul_of_nonneg_right rest (bound v).2.1
        have base : c.p i≤c.e v+1:=by omega
        have base' : (c.p i:ℚ)-1≤(c.e v:ℚ)+1:=by
          have u:(c.p i:ℚ)≤c.e v+1:=by exact_mod_cast base
          linarith
        have M:=(le_div_iff₀ (by positivity)).mp (bound v).2.2
        have g:=mul_le_mul_of_nonneg_left yv u0
        have h:=mul_le_mul_of_nonneg_right base' (bound v).2.1
        have k8 : (8:ℚ)≤c.k:=by exact_mod_cast c.kp
        nlinarith only [risk,g,h,M,k8]
      rw [if_pos unique]
      have len : c.p i≤c.e i+1:=by simpa [unique,vbig] using pL
      have pw:=OMA.SingleMovingLoss245212.scalar c.kp pk len
      have more:=lower c link i
      have pwq : 8*(c.p i:ℚ)*(G c.k)≤(c.p i:ℚ)^(c.e i):=by exact_mod_cast pw
      apply (div_le_iff₀ (by have:=(c.prime i).pos;positivity : (0:ℚ)<(c.p i:ℚ)^(c.e i))).mpr
      nlinarith only [more,mul_le_mul_of_nonneg_right pwq gd.le]
    have h:=step bad
    dsimp only [val,score];simp only [Nat.cast_one,one_mul]
    rw [←prod_erase_mul univ (mix s) (mem_univ i),←prod_erase_mul univ (miy s) (mem_univ i),
        ←prod_erase_mul univ (mix (insert i s)) (mem_univ i),←prod_erase_mul univ (miy (insert i s)) (mem_univ i)]
    change (c.k:ℚ)*(xx*mix s i)+yy*miy s i≤ _*(_*mix (insert i s) i)+_*miy (insert i s) i+_
    change (c.k:ℚ)*(xx*mix s i)+yy*miy s i≤
      c.k*((∏j∈t,mix (insert i s) j)*mix (insert i s) i)+
      (∏j∈t,miy (insert i s) j)*miy (insert i s) i+_
    rw [sameX,sameY]
    simpa only [mix,miy,if_neg fresh,mem_insert_self,if_true,exactX,exactY,x',y',mul_one,one_mul,
      mul_comm,mul_left_comm,mul_assoc] using h
  have sum (s : Finset (Fin r)) : val ∅ ≤ val s+(if v∈s then deficit c/4 else 0) := by
    induction s using Finset.induction_on with
    | empty=>simp
    | @insert i s fresh ih=>
      have h:=adv s fresh
      by_cases iv : i=v
      · subst i
        simpa [fresh] using ih.trans (by simpa [fresh] using h : val s+(if v∈s then deficit c/4 else 0) ≤ val (insert v s)+deficit c/4)
      · have adv0 : val s≤val (insert i s):=by simpa only [if_neg iv,add_zero] using h
        simpa only [Finset.mem_insert,Ne.symm iv,false_or] using ih.trans
          (add_le_add_left adv0 (if v∈s then deficit c/4 else 0))
  have a:=sum univ
  simp only [val,mix,miy,notMem_empty,if_false,mem_univ,if_true] at a
  have eq:=clear c b c.k 1
  simp only [one_mul] at eq
  rw [←hit] at eq
  push_cast at eq
  have dp : (0:ℚ)<dust c b:=by exact_mod_cast dust_pos c b
  have eq' : score c.k 1 (x' c b) (y' c b)=(c.k:ℚ)+1:=mul_right_cancel₀ dp.ne' eq
  dsimp only [deficit] at a gd
  linarith only [a,eq',gd]

end OMA.FixedRankProxy245212


/- Uniform integer separation for a finite list of odd prime powers. -/
namespace OMA.FixedRankStep245212
open Nat Finset OMA.TwoTallLocal245212 OMA.ThreeMovingLocal245212 OMA.FixedRankGap245212
variable {r : ℕ}

def cut (r x j : ℕ) := x^((3*r+4)^j)
def degree (r : ℕ) := (3*r+4)^(2*r+1)

theorem cut_succ (r x j : ℕ) : cut r x (j+1)=(cut r x j)^(3*r+4) := by
  simp only [cut,pow_succ (3*r+4),←pow_mul]

theorem cut_mono (r : ℕ) {x : ℕ} (hx : 1≤x) : Monotone (cut r x) :=
  fun _ _ z=>Nat.pow_le_pow_right hx (Nat.pow_le_pow_right (by omega) z)

theorem empty_band (x : ℕ) (hx : 1≤x) (p : Fin r ⊕ Fin r →ℕ) :
    ∃j : Fin (2*r+1),∀i, p i ≤ cut r x j.val ∨ cut r x (j.val+1) < p i := by
  by_contra! no
  choose f above below using no
  have inj:Function.Injective f := by
    intro j k eqn
    rcases lt_trichotomy j k with lt|eq|gt
    · have h := cut_mono r hx (show j.val+1≤k.val from lt)
      have impossible:=(below j).trans h
      rw [eqn] at impossible
      exact False.elim ((above k).not_ge impossible)
    · exact eq
    · have h := cut_mono r hx (show k.val+1≤j.val from gt)
      have impossible:=(below k).trans h
      rw [←eqn] at impossible
      exact False.elim ((above j).not_ge impossible)
  have h:=Fintype.card_le_of_injective _ inj
  simp only [Fintype.card_fin,Fintype.card_sum] at h
  omega

private theorem integer_gap (c : Family r) (bits : Fin r→Option Bool) (f g : ℕ)
    (different : (f+g)*dust c bits ≠ f*NX c bits+g*NY c bits) :
    (1:ℚ)≤|score f g (x' c bits) (y' c bits)-(f+g:ℕ)| * dust c bits := by
  let B:=dust c bits
  let T:=f*NX c bits+g*NY c bits
  let L:ℤ:=(T:ℤ)-((f+g)*B:ℕ)
  have nz : L≠0 := fun h => different (by exact_mod_cast (sub_eq_zero.mp h).symm)
  have la : (1:ℤ)≤|L| := by have:=abs_pos.mpr nz;omega
  have raw : (1:ℚ)≤|(T:ℚ)-((f+g)*B:ℕ)| := by dsimp [L] at la;exact_mod_cast la
  have ab:=congrArg (fun w:ℚ=>|w|) (show (score f g (x' c bits) (y' c bits)-(f+g:ℕ))*B =
      (T:ℚ)-((f+g)*B:ℕ) by rw [sub_mul];push_cast;rw [show score f g (x' c bits) (y' c bits)*B=(T:ℚ) from clear ..])
  rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg B : (0:ℚ)≤B)] at ab
  exact ab.trans_ge raw

private theorem difference (c : Family r) (b : Fin r→Option Bool) (f g N : ℕ) (n0 : 0<N)
    (space : ∀ i t, b i=some t → N ≤ (if t then (c.p i)^(c.e i) else c.p i)) :
    |score f g (x' c b) (y' c b)-score f g (exactX c) (exactY c)|≤(2*r*2^r:ℕ)*((f:ℚ)+g)/N := by
  have bp i := ranges (c.prime i) (c.positive i) (b i)
  have ex i := ranges (c.prime i) (c.positive i) none
  have er (i) : |exactX c i-x' c b i|≤2/(N:ℚ) ∧ |exactY c i-y' c b i|≤2/(N:ℚ) := by
    cases h:b i with
    | none=>simp [exactX,x',exactY,y',h,xx',yy'];positivity
    | some t=>simpa [exactX,x',exactY,y',h,xx',yy'] using error (c.prime i) (c.positive i) n0 t (space i t h)
  have eps : (0:ℚ)≤2/N := by positivity
  have one i : 2/((c.e i:ℚ)+1)≤2 := div_le_self (by decide) (by have:=Nat.cast_nonneg (α:=ℚ) (c.e i);linarith)
  have x:=OMA.CofactorEffectiveAtom245212.product_error (univ:Finset (Fin r)) (exactX c) (x' c b) eps
    (fun i _=>⟨zero_le_one.trans (ex i).1,(ex i).2.1,zero_le_one.trans (bp i).1,(bp i).2.1,(er i).1⟩)
  have y:=OMA.CofactorEffectiveAtom245212.product_error (univ:Finset (Fin r)) (exactY c) (y' c b) eps
    (fun i _=>⟨(ex i).2.2.1,(ex i).2.2.2.trans (one i),(bp i).2.2.1,(bp i).2.2.2.trans (one i),(er i).2⟩)
  have cards : (univ:Finset (Fin r)).card=r:=Finset.card_fin _
  rw [cards] at x y
  change |(∏i,exactX c i)-(∏i,x' c b i)| ≤ (r:ℚ)*2^r*(2/N) at x
  change |(∏i,exactY c i)-(∏i,y' c b i)| ≤ (r:ℚ)*2^r*(2/N) at y
  dsimp [score]
  rw [abs_sub_comm]
  calc
    _ = |(f:ℚ)*((∏i,exactX c i)-∏i,x' c b i)+(g:ℚ)*((∏i,exactY c i)-∏i,y' c b i)| := by congr 1;ring
    _ ≤ _ := (abs_add_le ..).trans (by
      rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg f : (0:ℚ)≤f),abs_mul,
        abs_of_nonneg (Nat.cast_nonneg g : (0:ℚ)≤g)]
      push_cast
      simp only [div_eq_mul_inv] at x y ⊢
      nlinarith only [mul_le_mul_of_nonneg_left x (Nat.cast_nonneg f : (0:ℚ)≤f),
        mul_le_mul_of_nonneg_left y (Nat.cast_nonneg g : (0:ℚ)≤g)])

theorem contradiction (c : Family r) (f g x : ℕ) (big : 128≤x) (cf : f+g≤x) (cl : c.L≤x) (errorCap : 2*r*2^r≤x)
    (separated : ∀ b, (f+g)*dust c b ≠ f*NX c b+g*NY c b)
    (close : |score f g (exactX c) (exactY c)-(f+g:ℕ)| ≤ 1/((x^(degree r):ℕ):ℚ)) : False := by
  let point : Fin r ⊕ Fin r → ℕ := Sum.elim c.p (fun i=>c.p i^c.e i)
  obtain ⟨j,band⟩:=empty_band x (by omega) point
  have bp (i:Fin r) := band (Sum.inl i)
  have bd (i:Fin r) := band (Sum.inr i)
  let Q:=cut r x j.val
  let N:=cut r x (j.val+1)
  let b (i:Fin r) : Option Bool := if c.p i^c.e i≤Q then none else some (decide (c.p i≤Q))
  have next : N=Q^(3*r+4) := cut_succ ..
  have xQ : x≤Q := by
    have old:=cut_mono r (show 1≤x by omega) (Nat.zero_le j.val)
    simpa [cut,Q] using old
  have np : 0<N := by rw [next];exact pow_pos (by omega) _
  have nb : N≤x^(degree r):=cut_mono r (by omega) (show j.val+1≤2*r+1 by omega)
  have space (i) (t:Bool) (mode:b i=some t) : N ≤ (if t then c.p i^c.e i else c.p i) := by
    dsimp [b] at mode
    split at mode
    next=>contradiction
    next off=>
      obtain rfl:=Option.some.inj mode
      by_cases lo : c.p i≤Q
      · simp [lo]
        exact ((bd i).resolve_left off).le
      · simp [lo]
        exact ((bp i).resolve_left lo).le
  have ds : dust c b≤Q^(3*r) := by
    have per i : Dn (c.p i) (c.e i) (b i)≤Q^3 := by
      have el := (c.cap i).trans (cl.trans xQ)
      by_cases exactMode : c.p i^c.e i≤Q
      · rw [show b i=none from if_pos exactMode]
        change (c.e i+1)*(c.p i^c.e i)≤Q^3
        exact
          (Nat.mul_le_mul el exactMode).trans (show Q*Q≤Q^3 by rw [←sq];exact Nat.pow_le_pow_right (by omega) (by decide))
      · by_cases keep:c.p i≤Q
        · simpa [b,exactMode,keep,Dn,den] using
            (Nat.mul_le_mul el (Nat.pow_le_pow_left (show c.p i-1≤Q by omega) 2)).trans_eq (by ring : Q*Q^2=Q^3)
        · simpa [b,exactMode,keep,Dn,den] using el.trans (Nat.le_self_pow (by decide : 3≠0) Q)
    dsimp [dust]
    exact (prod_le_prod' (fun i _=>per i)).trans_eq (by simp [←pow_mul])
  have nz:=separated b
  have iga:=integer_gap c b f g nz
  let orig:=score f g (exactX c) (exactY c)
  let approx:=score f g (x' c b) (y' c b)
  let W:ℚ:=(f+g:ℕ)
  have lite : |orig-W|≤1/(N:ℚ) := close.trans (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast nb))
  have diff:=difference c b f g N np space
  change |approx-orig|≤_ at diff
  change (1:ℚ)≤|approx-W| * dust c b at iga
  have err : |approx-W| * (N:ℚ)≤(2*r*2^r:ℕ)*((f:ℚ)+g)+1 := by
    have t:=abs_sub_le approx orig W
    have wn : (0:ℚ)<N:=by exact_mod_cast np
    nlinarith only [mul_le_mul_of_nonneg_right t wn.le,(le_div_iff₀ wn).mp diff,(le_div_iff₀ wn).mp lite]
  have sep : N≤((2*r*2^r)*(f+g)+1)*dust c b := by
    have z : (N:ℚ)≤((2*r*2^r:ℕ)*((f:ℚ)+g)+1)*dust c b := by
      nlinarith only [mul_le_mul_of_nonneg_right iga (Nat.cast_nonneg N : (0:ℚ)≤N),
        mul_le_mul_of_nonneg_right err (Nat.cast_nonneg (dust c b) : (0:ℚ)≤_)]
    exact_mod_cast z
  have qr : 128≤Q:=big.trans xQ
  have cfq : f+g≤Q:=cf.trans xQ
  have rate : 2*r*2^r≤Q := errorCap.trans xQ
  have cf' : (2*r*2^r)*(f+g)+1<Q^3 := by
    have m:=Nat.mul_le_mul rate cfq
    have grow:=Nat.mul_le_mul_left (Q*Q) (show 2≤Q by omega)
    nlinarith only [m,grow,qr,Nat.mul_self_le_mul_self (show 2≤Q by omega)]
  have bad : N < Q^(3+3*r) := sep.trans_lt ((Nat.mul_lt_mul_of_lt_of_le cf' ds
    (pow_pos (by omega) _)).trans_eq (by rw [pow_add]))
  have natural : Q^(3+3*r)≤N:=next ▸ Nat.pow_le_pow_right (by omega) (by omega)
  omega

end OMA.FixedRankStep245212


/- The dyadic factor of every solution with three distinct odd primes
is polynomially bounded in the largest odd exponent length. -/
namespace OMA.FixedRankHeight245212
open Nat Finset ArithmeticFunction OMA.FixedRankGap245212 OMA.FixedRankStep245212
open OMA.ThreeMovingOriginal245212 (F G)
open OMA.TwoTallScalar245212 (base)
open OMA.Smooth245212 (total W)
open scoped ArithmeticFunction.sigma
variable {r : ℕ}

private theorem identities (k : ℕ) : 0<G k ∧ F k+G k=(k+1)*2^(k+1) ∧ F k=k*G k+(k+1) := by
  have g:=Nat.two_pow_pos k
  dsimp [F,G];rw [pow_succ]
  have sub:=Nat.sub_add_cancel (show 1≤2^k*2 by omega)
  exact ⟨by omega,by nlinarith only [sub],by nlinarith only [congrArg (k*·) sub]⟩


theorem physical (c : Family r) (k : ℕ) (op : ∀i,Odd (c.p i)) (inj : c.p.Injective)
    (eqn : OeisA245212.a (2^k*total c.p c.e)=(σ 1 (2^k*total c.p c.e):ℤ)) :
    score (F k) (G k) (exactX c) (exactY c)=(F k+G k:ℕ) := by
  let t:=2^k*σ 0 (2^k)
  have t0 : 0<t := Nat.mul_pos (Nat.two_pow_pos k) (sigma_pos 0 _ (Nat.two_pow_pos k).ne')
  have norm:=OMA.CofactorCrossOriginal245212.normalized_extension (p:=c.p) (e:=c.e) (Nat.two_pow_pos k)
    c.prime inj (fun i=>(Nat.coprime_two_left.mpr (op i)).pow_left k) eqn
  change ((W (2^k):ℚ)/t)*(∏i,exactX c i)+((σ 1 (2^k):ℚ)/t)*(∏i,exactY c i)=2 at norm
  field_simp [show (t:ℚ)≠0 by exact_mod_cast t0.ne'] at norm
  have z0:=Nat.two_pow_pos (k+1)
  have gold : σ 1 (2^k)=G k := by
    dsimp [G];zify [Nat.cast_sub (show 1≤2^(k+1) from z0)]
    exact (OMA.ComplementaryLocal245212.binary k).1
  have fold : W (2^k)=F k := by exact_mod_cast (OMA.ComplementaryLocal245212.binary k).2
  have ht : 2*t=F k+G k := by
    dsimp [t];rw [sigma_zero_apply_prime_pow Nat.prime_two,(identities k).2.1,pow_succ];ring
  rw [gold,fold] at norm
  dsimp [score];rw [←ht];push_cast;linarith only [norm]


theorem coarse (c : Family r) (op : ∀i,Odd (c.p i))
    (eqn : OeisA245212.a (2^c.k*total c.p c.e)=(σ 1 (2^c.k*total c.p c.e):ℤ)) :
    G c.k < 2^r*(c.k+1)*((base c.k c.L)^(r+2))^(degree r) := by
  have exact:=physical c c.k op c.inj eqn
  let x:=(base c.k c.L)^(r+2)
  have toX : base c.k c.L≤x:=Nat.le_self_pow (by omega) _
  have big : 128≤x := by apply le_trans _ toX; dsimp [base];nlinarith only [Nat.zero_le (c.k*c.L),Nat.zero_le c.k,Nat.zero_le c.L]
  have cf : c.k+1≤x := by apply le_trans _ toX; dsimp [base];nlinarith only [Nat.zero_le (c.k*c.L),Nat.zero_le c.k,Nat.zero_le c.L]
  have cl : c.L≤x := by apply le_trans _ toX; dsimp [base];nlinarith only [Nat.zero_le (c.k*c.L),Nat.zero_le c.k,Nat.zero_le c.L]
  have dx : 1≤x:=by omega
  have r0 := (identities c.k).1
  let PX:=∏i,exactX c i
  let PY:=∏i,exactY c i
  have xb i := OMA.TwoTallLocal245212.ranges (c.prime i) (c.positive i) none
  have low : (1:ℚ)≤PX:=one_le_prod (fun i _=>(xb i).1)
  have top : PX≤(2:ℚ)^r := calc
    _ ≤ ∏_i:Fin r,(2:ℚ) := prod_le_prod (fun i _=>zero_le_one.trans (xb i).1) (fun i _=>(xb i).2.1)
    _ = _ := by norm_num
  have id : (G c.k:ℚ)*((c.k:ℚ)+1-score c.k 1 (exactX c) (exactY c))=((c.k:ℚ)+1)*(PX-1) := by
    change (F c.k:ℚ)*PX+(G c.k:ℚ)*PY=(F c.k+G c.k:ℕ) at exact
    change _*((c.k:ℚ)+1-((c.k:ℚ)*PX+(1:ℕ)*PY))=_
    have f : (F c.k:ℚ)=(c.k:ℚ)*G c.k+(c.k+1:ℕ) := by exact_mod_cast (identities c.k).2.2
    push_cast at f exact ⊢
    linear_combination -exact+(PX-1)*f
  have gp : (0:ℚ)<G c.k := by exact_mod_cast r0
  by_contra! ample
  have below : score c.k 1 (exactX c) (exactY c)≤(c.k+1:ℕ):=by
    push_cast
    exact sub_nonneg.mp (nonneg_of_mul_nonneg_right (id ▸ mul_nonneg (by positivity) (sub_nonneg.mpr low)) gp)
  have close : |score c.k 1 (exactX c) (exactY c)-(c.k+1:ℕ)|≤1/((x^(degree r):ℕ):ℚ) := by
    rw [abs_of_nonpos (sub_nonpos.mpr below),neg_sub]
    have h : (((c.k+1:ℕ):ℚ)-score c.k 1 (exactX c) (exactY c))*(x^(degree r):ℕ)≤1 := by
      apply le_of_mul_le_mul_left (a:=(G c.k:ℚ)) _ gp
      have g0 : (2:ℚ)^r*(c.k+1)*(x^(degree r):ℕ)≤G c.k:=by exact_mod_cast ample
      push_cast at g0 ⊢
      nlinarith only [congrArg (·*(x:ℚ)^(degree r)) id,g0,
        mul_le_mul_of_nonneg_right (show PX-1≤(2:ℚ)^r by linarith) (show 0≤((c.k:ℚ)+1)*x^(degree r) by positivity)]
    exact (le_div_iff₀ (by exact_mod_cast pow_pos dx (degree r) : (0:ℚ)<(x^(degree r):ℕ))).mpr h

  apply OMA.FixedRankStep245212.contradiction c c.k 1 x big cf cl ?_ ?_ close
  · have B : 4≤base c.k c.L := by dsimp [base];nlinarith only [Nat.zero_le (c.k*c.L),Nat.zero_le c.k,Nat.zero_le c.L]
    calc
      2*r*2^r ≤ 2*(2^r)*2^r := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ ((Nat.lt_two_pow_self).le))
      _ = 2*4^r := by rw [show (4:ℕ)=2*2 by decide,mul_pow];ring
      _ ≤ 4^r*4^2 := by nlinarith only [Nat.zero_le (4^r)]
      _ = 4^(r+2) := (pow_add ..).symm
      _ ≤ x := Nat.pow_le_pow_left B _
  intro b
  have link : OMA.FixedRankProxy245212.deficit c*(G c.k:ℕ)=((c.k:ℚ)+1)*((∏i,exactX c i)-1) := by
    simpa only [OMA.FixedRankProxy245212.deficit,mul_comm] using id
  simpa only [one_mul] using OMA.FixedRankProxy245212.separated c b link


/-- The explicit polynomial degree depends only on the number of odd primes. -/
def exponent (r : ℕ) := (r+2)*degree r+r


/-- The full A245212 equality bounds its dyadic prime power polynomially in
the largest odd exponent length at every fixed positive support size. -/
theorem original {r : ℕ} (k L : ℕ) (p e : Fin r→ℕ) (prime : ∀i,(p i).Prime)
    (odd : ∀i,Odd (p i)) (distinct : p.Injective) (positive : ∀i,0<e i)
    (longest : ∃i,e i+1=L) (cap : ∀i,e i+1≤L)
    (eqn : OeisA245212.a (2^k*total p e)=(σ 1 (2^k*total p e):ℤ)) :
    2^k≤OMA.SingleMovingHeight245212.constant (exponent r)*(L+1)^(2*exponent r) := by
  apply OMA.SingleMovingHeight245212.all_k
  intro hk
  let c : Family r := ⟨p,e,k,L,prime,positive,hk,longest,cap,distinct⟩
  have z:=coarse c odd eqn
  change G k < 2^r*(k+1)*((base k L)^(r+2))^(degree r) at z
  apply z.trans_le
  let b:=base k L
  have hb : 2≤b := by dsimp [base,b];nlinarith only [Nat.zero_le (k*L),Nat.zero_le k,Nat.zero_le L]
  have h:=Nat.pow_le_pow_left hb r
  calc
    _ ≤ b^r*(k+1)*(b^(r+2))^(degree r) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h)
    _ = (k+1)*b^(exponent r) := by rw [exponent,pow_add b ((r+2)*degree r) r,pow_mul];ring
    _ ≤ 8*(k+1)*b^(exponent r) := Nat.mul_le_mul_right _ (by omega)

end OMA.FixedRankHeight245212


/- The fixed-support dyadic estimate directly on the original integer, without
an ordered factorization as input. The nonempty hypothesis removes pure powers of two. -/
namespace OMA.FixedRankInteger245212
open Nat Finset OMA.Smooth245212 OMA.FixedRankHeight245212
open scoped ArithmeticFunction.sigma

def support (n : ℕ) := n.primeFactors.erase 2
def longest (n : ℕ) := (support n).sup (fun p=>n.factorization p+1)
def polynomial (r L : ℕ) := OMA.SingleMovingHeight245212.constant (exponent r)*(L+1)^(2*exponent r)

/-- A single explicit function works simultaneously for every nonempty odd
support, even when the number of primes is itself allowed to vary. -/
theorem original {n : ℕ} (pos : 0<n) (nonempty : (support n).Nonempty)
    (eqn : OeisA245212.a n=(σ 1 n:ℤ)) :
    2^(n.factorization 2)≤polynomial (support n).card (longest n) := by
  let s:=support n
  let P : Fin s.card ↪o ℕ:=s.orderEmbOfFin rfl
  let e (i : Fin s.card):=n.factorization (P i)
  have mem (i : Fin s.card) : P i∈s:=s.orderEmbOfFin_mem rfl i
  have prime i := prime_of_mem_primeFactors (mem_erase.mp (mem i)).2
  have odd i := (prime i).odd_of_ne_two (mem_erase.mp (mem i)).1
  have ep (i) : 0<e i:=Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (mem_erase.mp (mem i)).2)
  have lift : univ.map P.toEmbedding=s:=s.map_orderEmbOfFin_univ rfl
  have fac : 2^(n.factorization 2)*(∏ p∈s,p^(n.factorization p))=n := by
    by_cases h : 2∈n.primeFactors
    · exact (mul_prod_erase n.primeFactors (fun p => p^(n.factorization p)) h).trans
        (Nat.prod_primeFactors_pow_factorization pos.ne').symm
    · have z : n.factorization 2=0:=Finsupp.notMem_support_iff.mp h
      simpa [z,s,support,erase_eq_of_notMem h] using (Nat.prod_primeFactors_pow_factorization pos.ne').symm
  rw [←lift,prod_map] at fac
  change 2^(n.factorization 2)*total P e=n at fac
  obtain ⟨z,zm,zt⟩:=Finset.exists_mem_eq_sup s nonempty (fun p=>n.factorization p+1)
  obtain ⟨i,_,zi⟩:=Finset.mem_map.mp (lift.symm ▸ zm)
  change P i=z at zi
  have zmax : ∃ i,e i+1=longest n:=⟨i,by change n.factorization (P i)+1=longest n;rw [zi];exact zt.symm⟩
  have cap i : e i+1≤longest n := Finset.le_sup (f:=fun p=>n.factorization p+1) (mem i)
  exact OMA.FixedRankHeight245212.original (n.factorization 2) (longest n) P e prime odd P.injective ep zmax cap (by rwa [fac])

/-- In rank four the exponent of (L+1) is exactly 824633720840. -/
theorem four {n : ℕ} (pos : 0<n) (rank : (support n).card=4)
    (eqn : OeisA245212.a n=(σ 1 n:ℤ)) :
    2^(n.factorization 2)≤OMA.SingleMovingHeight245212.constant 412316860420*(longest n+1)^824633720840 := by
  have ne:=Finset.card_pos.mp (show 0<(support n).card by omega)
  simpa only [rank,polynomial,show exponent 4=412316860420 by decide,show 2*412316860420=824633720840 by decide]
    using original pos ne eqn

end OMA.FixedRankInteger245212

#print axioms OMA.FixedRankProxy245212.separated

#print axioms OMA.FixedRankHeight245212.original

#print axioms OMA.FixedRankInteger245212.original

#print axioms OMA.FixedRankInteger245212.four
