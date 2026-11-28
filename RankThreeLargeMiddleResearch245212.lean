import FormalConjectures.OEIS.«245212»




/-! OEIS A245212: no solution twice a product of powers of three distinct primes at least five. -/

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

end OMA.DyadicEuler245212

end

section

/- Dyadic exponent one, with three odd bases. Keeping one actual
Euler factor also gives a lower bound for each exponent near the cap. -/
namespace OMA.RankThreeCap245212
open Finset Nat OMA.Smooth245212 OMA.OddFaces245212
open scoped ArithmeticFunction.sigma
open OMA.OddFaces245212 (envelope)

theorem norm {p q r a b c : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (po : 2<p) (pq : p<q) (qr : q<r)
    (eq : OeisA245212.a (2*p^a*q^b*r^c)=(σ 1 (2*p^a*q^b*r^c):ℤ)) :
    5*(X p (some a)*X q (some b)*X r (some c))+
      3*(Y p (some a)*Y q (some b)*Y r (some c))=8 := by
  let P : Fin 4 → ℕ := ![2,p,q,r]
  let E : Fin 4 → ℕ := ![1,a,b,c]
  have pr (i : Fin 4) : (P i).Prime := by fin_cases i <;> simp [P,hp,hq,hr,prime_two]
  have inj : P.Injective := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all [P] <;> omega
  have repr : total P E=2*p^a*q^b*r^c := by simp [total,Fin.prod_univ_four,P,E,mul_assoc]
  have n := normalized_of_eq P pr inj E (repr ▸ eq)
  have x : X 2 (some 1)=5/4 := by decide +kernel
  have y : Y 2 (some 1)=3/4 := by decide +kernel
  simp [normalized,Fin.prod_univ_four,P,E,x,y] at n
  linarith

theorem caps {p q r a b c : ℕ} (hp : 1<p) (hq : 1<q) (hr : 1<r) (ap : 0<a)
    (eq : 5*(X p (some a)*X q (some b)*X r (some c))+
      3*(Y p (some a)*Y q (some b)*Y r (some c))=8) :
    8≤5*(limitX p*limitX q*limitX r) := by
  let P : Fin 3 → ℕ := ![p,q,r]
  let E : Fin 3 → ℕ := ![a,b,c]
  have pr (i : Fin 3) : 1<P i := by fin_cases i <;> simp [P,hp,hq,hr]
  have x : X 2 (some 1)=5/4 := by decide +kernel
  have y : Y 2 (some 1)=3/4 := by decide +kernel
  have val : X 2 (some 1)*(∏ i,X (P i) (some (E i)))+
      Y 2 (some 1)*(∏ i,Y (P i) (some (E i)))=2 := by
    rw [x,y]; simp [Fin.prod_univ_three,P,E]; linarith
  have t := OMA.DyadicEuler245212.cap_needed_at_two 1 P E pr 0 ap val
  simp [Fin.prod_univ_three,P,x] at t
  linarith

theorem one_cap {p q r a b c : ℕ} (hp : 3≤p) (hq : 1<q) (hr : 1<r) (bp : 0<b)
    (eq : 5*(X p (some a)*X q (some b)*X r (some c))+
      3*(Y p (some a)*Y q (some b)*Y r (some c))=8) :
    8≤5*X p (some a)*(limitX q*limitX r) := by
  have pg : 1<p := by omega
  have p' : (3:ℚ)≤p := by exact_mod_cast hp
  have sp : (0:ℚ)<p-1 := by linarith
  have yp := y_one pg (some a)
  have sum_bound : 5*X p (some a)+3*Y p (some a)≤8 := by
    unfold X; apply (le_of_mul_le_mul_right · sp)
    field_simp
    nlinarith only [mul_nonneg (sub_nonneg.mpr (show (8:ℚ)≤3*p by linarith)) (sub_nonneg.mpr yp)]
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
  have W := mul_le_mul_of_nonneg_left env (mul_nonneg (by decide : (0:ℚ)≤5) (x_nonneg pg (some a)))
  change 8≤5*X p (some a)*U
  by_contra! bad
  have h : 5*(X p (some a)*(X q (some b)*X r (some c)))+3*(Y p (some a)*T)=8 := by
    simpa only [T,mul_assoc] using eq
  nlinarith only [W,h,mul_le_mul_of_nonneg_right sum_bound T0,mul_pos (sub_pos.mpr ltT) (sub_pos.mpr bad)]

theorem ordered {p q r : ℕ} (_hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (p5 : 5≤p) (pq : p<q) (qr : q<r) (cap : 8≤5*(limitX p*limitX q*limitX r)) :
    p=5 ∧ q=7 ∧ r=11 := by
  have veto (u v w : ℕ) (hu : 1<u) (hv : 1<v) (hw : 1<w) (up : u≤p) (vq : v≤q) (wr : w≤r)
      (bad : 5*(limitX u*limitX v*limitX w)<8) : False := by
    have l := mul_le_mul (mul_le_mul (cap_anti hu up) (cap_anti hv vq)
      (x_nonneg hq.one_lt none) (x_nonneg hu none)) (cap_anti hw wr)
      (x_nonneg hr.one_lt none) (mul_nonneg (x_nonneg hu none) (x_nonneg hv none))
    linarith
  have q7 : 7≤q := by by_contra! h; interval_cases q <;> norm_num at * <;> omega
  have r11 : 11≤r := by by_contra! h; interval_cases r <;> norm_num at * <;> omega
  have pp : p=5 := by
    by_contra h
    exact veto 6 7 11 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by omega) q7 r11 (by decide +kernel)
  have qq : q=7 := by
    by_contra h
    exact veto 5 8 11 (by decide +kernel) (by decide +kernel) (by decide +kernel) p5 (by omega) r11 (by decide +kernel)
  have rr : r=11 := by
    by_contra h
    exact veto 5 7 12 (by decide +kernel) (by decide +kernel) (by decide +kernel) p5 q7 (by omega) (by decide +kernel)
  exact ⟨pp,qq,rr⟩
end OMA.RankThreeCap245212

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

theorem outside_erase {s : Finset (Fin 4)} {i : Fin 4} (hi : i∈s) :
    outside p e (s.erase i)=outside p e s*(p i^e i) := by
  let a (j : Fin 4) := if j∈s then 1 else p j^e j
  let b (j : Fin 4) := if j∈s.erase i then 1 else p j^e j
  have eq : (∏ j∈univ.erase i,b j)=∏ j∈univ.erase i,a j :=
    prod_congr rfl fun j hj=>by simp [a,b,(mem_erase.mp hj).1]
  change (∏ j,b j)=(∏ j,a j)*(p i^e i)
  rw [←prod_erase_mul _ b (mem_univ i),←prod_erase_mul _ a (mem_univ i),eq]
  simp [a,b,hi]

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

/- At dyadic exponent one there is no solution with three distinct odd
primes all at least five. The Euler cap leaves 5,7,11. For that support
the height bound and the three one-factor caps make rounding simultaneous. -/
namespace OMA.RankThreeOne245212
open Finset Nat OMA.Smooth245212 OMA.OddFaces245212 OMA.Height245212
open OMA.RankThreeCap245212
open scoped ArithmeticFunction.sigma

private theorem cut {p q r a t : ℕ} (hp : 1<p) (hq : 1<q) (hr : 1<r)
    (h : 8≤5*X p (some a)*(limitX q*limitX r))
    (small : 5*X p (some t)*(limitX q*limitX r)<8) : t<a := by
  by_contra! le
  have rat : (1:ℚ)<p := by exact_mod_cast hp
  have x : X p (some a)≤X p (some t) := by
    unfold X
    gcongr
    exact y_anti hp le
  have m := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left x (by decide : (0:ℚ)≤5))
    (mul_nonneg (x_nonneg hq none) (x_nonneg hr none))
  exact small.not_ge (h.trans m)

theorem fixed {a b c : ℕ} (ap : 0<a) (bp : 0<b) (cp : 0<c) :
    OeisA245212.a (2*5^a*7^b*11^c)≠(σ 1 (2*5^a*7^b*11^c):ℤ) := by
  intro eq
  have n := OMA.RankThreeCap245212.norm (by decide : Nat.Prime 5) (by decide : Nat.Prime 7)
    (by decide : Nat.Prime 11) (by decide) (by decide) (by decide) eq
  have aa : 59<a := cut (by decide : 1<5) (by decide : 1<7) (by decide : 1<11)
    (one_cap (by decide) (by decide) (by decide) bp n) (by decide +kernel)
  have bb : 44<b := cut (by decide : 1<7) (by decide : 1<5) (by decide : 1<11)
    (one_cap (by decide) (by decide) (by decide) ap (by convert n using 1; ring)) (by decide +kernel)
  have cc : 29<c := cut (by decide : 1<11) (by decide : 1<5) (by decide : 1<7)
    (one_cap (by decide) (by decide) (by decide) ap (by convert n using 1; ring)) (by decide +kernel)
  let P : Fin 4 → ℕ := ![2,5,7,11]
  let E : Fin 4 → ℕ := ![1,a,b,c]
  have pr (i : Fin 4) : (P i).Prime := by fin_cases i <;> decide
  have distinct : P.Injective := by intro i j hit; fin_cases i <;> fin_cases j <;> simp_all [P]
  have pos (i : Fin 4) : 0<E i := by fin_cases i <;> simp [E,ap,bp,cp]
  have prime_bound (i : Fin 4) : P i≤11 := by fin_cases i <;> decide
  have two (i : Fin 4) : P i=2 → P i^E i ≤ 11^(2*11) := by fin_cases i <;> simp [P,E]
  have repr : total P E=2*5^a*7^b*11^c := by simp [total,Fin.prod_univ_four,P,E,mul_assoc]
  have bal := normalized_of_eq P pr distinct E (repr ▸ eq)
  have height := OMA.GuardedHeight245212.max_power P E pr two pos distinct prime_bound (repr ▸ eq)
  have top : univ.sup E≤3000 := (OMA.HeightLog245212.four
    (lt_of_lt_of_le (pos 0) (le_sup (f:=E) (mem_univ 0))) height).trans (by decide +kernel)
  have be (i : Fin 4) : E i≤3000 := (le_sup (f:=E) (mem_univ i)).trans top
  let S : Finset (Fin 4) := {1,2,3}
  have out : outside P E S=2 := by simp [outside,Fin.prod_univ_four,P,E,S]
  have large (i : Fin 4) (hi : i∈S) : coefficientBound 11 3000*outside P E S<P i^E i := by
    rw [out]; fin_cases i
    · simp [S] at hi
    · exact lt_of_lt_of_le (by decide +kernel : coefficientBound 11 3000*2<5^60) (Nat.pow_le_pow_right (by decide) aa)
    · exact lt_of_lt_of_le (by decide +kernel : coefficientBound 11 3000*2<7^45) (Nat.pow_le_pow_right (by decide) bb)
    · exact lt_of_lt_of_le (by decide +kernel : coefficientBound 11 3000*2<11^30) (Nat.pow_le_pow_right (by decide) cc)
  have same := gap_eq P E pr pos S bal (enough P E pr prime_bound be S large)
  have ctl {i j : Fin 4} (eb : 29<E j) : ((P i:ℚ)-1)*yr (P j) (E j)<1 := by
    have h := (y_range (pr j).one_lt (pos j)).2.2
    have r : (P i : ℚ) ≤11 := by exact_mod_cast prime_bound i
    have low : (29:ℚ)<E j := by exact_mod_cast eb
    have yy := (y_range (pr j).one_lt (pos j)).1
    nlinarith only [h, yy, mul_nonneg (sub_nonneg.mpr r) yy, mul_nonneg (sub_nonneg.mpr low.le) yy]
  have signs (i : Fin 4) (_ : i∈S) : ∃ j, j≠i ∧ ((P i:ℚ)-1)*yr (P j) (E j)<1 := by
    by_cases one : i=1
    · exact ⟨2,by simp [one],ctl (show 29<E 2 from by simpa [E] using (show 29<b by omega))⟩
    · exact ⟨1,Ne.symm one,ctl (show 29<E 1 from by simpa [E] using (show 29<a by omega))⟩
  have strict := strict_rounding P E (fun i=>(pr i).one_lt) pos S (by decide) signs
  linarith

theorem no_least_ge_five {p q r a b c : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (least : 5≤p) (pq : p<q) (qr : q<r) (ap : 0<a) (bp : 0<b) (cp : 0<c) :
    OeisA245212.a (2*p^a*q^b*r^c)≠(σ 1 (2*p^a*q^b*r^c):ℤ) := by
  intro hit
  have n := OMA.RankThreeCap245212.norm hp hq hr (by omega) pq qr hit
  obtain ⟨rfl,rfl,rfl⟩ := ordered hp hq hr least pq qr (caps hp.one_lt hq.one_lt hr.one_lt ap n)
  exact fixed ap bp cp hit
end OMA.RankThreeOne245212

end

section

namespace OMA.Moving245212
open Finset OMA.Smooth245212
theorem y_infty {p e : ℕ} (hp : 1<p) :
    1/((e:ℚ)+1) ≤ Y p (some e) := by
  rw [y_avg hp]
  gcongr
  calc
    (1:ℚ) = (p:ℚ)⁻¹^0 := by simp
    _ ≤ ∑ i∈range (e+1),(p:ℚ)⁻¹^i :=
      single_le_sum (f:= fun i => (p:ℚ)⁻¹^i) (fun _ _ => by positivity) (by simp)

end OMA.Moving245212

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
open OMA.Smooth245212 Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma
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

end OMA.Large245212

end

section

namespace OMA.PrefixLeaf245212
open OMA.Large245212 OMA.Smooth245212 ArithmeticFunction
open scoped ArithmeticFunction.sigma
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

/- Pick two bounded exponents in a three-prime dyadic solution. When
a group contains only large prime powers the integer rounding error is
below one denominator unit. The product of the other two Euler factors
controls the sign, allowing much shorter thresholds than a scalar bound. -/
namespace OMA.RankThreeSmall245212
open Finset Nat OMA.Smooth245212 OMA.Height245212
open scoped ArithmeticFunction.sigma

def height (B : ℕ) := OMA.HeightLog245212.ceiling 4 B
def budget (B : ℕ) := 2*coefficientBound B (height B)
def first (B p : ℕ) := Nat.log p (budget B)
def next (B p e q r : ℕ) := max (Nat.log q (budget B*p^e)) (4*(r-1)/(e+1))
def seed (B p q r : ℕ) := 4*(p-1)<(first B q+2)*(first B r+2)

abbrev PP (p q r : ℕ) : Fin 4 → ℕ := ![2,p,q,r]
abbrev EE (a b c : ℕ) : Fin 4 → ℕ := ![1,a,b,c]
def Bal (p q r a b c : ℕ) :=
  5*(X p (some a)*X q (some b)*X r (some c))+3*(Y p (some a)*Y q (some b)*Y r (some c))=8

theorem normal {p q r a b c : ℕ} (h : Bal p q r a b c) : normalized (PP p q r) (EE a b c)=2 := by
  have x : X 2 (some 1)=5/4 := by decide +kernel
  have y : Y 2 (some 1)=3/4 := by decide +kernel
  simp [normalized,Fin.prod_univ_four,PP,EE,x,y]
  unfold Bal at h
  linarith

theorem exponent_height {p q r a b c : ℕ} (pp : p.Prime) (qp : q.Prime) (rp : r.Prime)
    (op : 2<p) (pq : p<q) (qr : q<r) (ap : 0<a) (bp : 0<b) (cp : 0<c)
    (sol : OeisA245212.a (2*p^a*q^b*r^c)=(σ 1 (2*p^a*q^b*r^c):ℤ)) :
    a≤height r ∧ b≤height r ∧ c≤height r := by
  let P := PP p q r
  let E := EE a b c
  have primes (i : Fin 4) : (P i).Prime := by fin_cases i <;> simp [P,PP,pp,qp,rp,prime_two]
  have inj : P.Injective := by intro i j hit; fin_cases i <;> fin_cases j <;> simp_all [P,PP] <;> omega
  have ps (i : Fin 4) : 0<E i := by fin_cases i <;> simp [E,EE,ap,bp,cp]
  have bnd (i : Fin 4) : P i≤r := by fin_cases i <;> simp [P,PP] <;> omega
  have dt (i : Fin 4) : P i=2 → P i^E i≤r^(2*r) := by
    fin_cases i <;> simp [P,E,PP,EE]
    · exact (by omega : 2≤r).trans (Nat.le_pow (by omega : 0<2*r))
    all_goals omega
  have repr : total P E=2*p^a*q^b*r^c := by simp [total,Fin.prod_univ_four,P,E,PP,EE,mul_assoc]
  have power := OMA.GuardedHeight245212.max_power P E primes dt ps inj bnd (repr ▸ sol)
  have top := OMA.HeightLog245212.four (lt_of_lt_of_le (ps 0) (le_sup (f:=E) (mem_univ 0))) power
  exact ⟨(le_sup (f:=E) (mem_univ 1)).trans top,(le_sup (f:=E) (mem_univ 2)).trans top,
    (le_sup (f:=E) (mem_univ 3)).trans top⟩

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
  exponents i := by fin_cases i <;> simp [EE,ae,be,ce]; omega
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

private theorem three_ctl {p q r a b c : ℕ} (pg : 1<p) (qg : 1<q) (rg : 1<r)
    (ap : 0<a) (bp : 0<b) (cp : 0<c)
    (v : 4*(p-1)<(b+1)*(c+1)) (w : 4*(q-1)<(a+1)*(c+1)) (x : 4*(r-1)<(a+1)*(b+1))
    (i : Fin 4) (hi : i≠0) : ((PP p q r i:ℚ)-1)*
      (∏ j∈univ.erase i,yr (PP p q r j) (EE a b c j))<1 := by
  rw [erase0]
  have z : yr 2 1=1 := by decide +kernel
  fin_cases i <;> simp_all [Fin.prod_univ_four,PP,EE]
  · exact control pg qg rg bp cp v
  · exact control qg pg rg ap cp w
  · exact control rg pg qg ap bp x

theorem small_one {B p q r a b c : ℕ} (h : Context B p q r a b c)
    (sp : seed B p q r) (sq : seed B q p r) (sr : seed B r p q) :
    a≤first B p ∨ b≤first B q ∨ c≤first B r := by
  by_contra! far
  obtain ⟨aa,bb,cc⟩ := far
  let s : Finset (Fin 4) := {1,2,3}
  have out : outside (PP p q r) (EE a b c) s=2 := by simp [outside,Fin.prod_univ_four,PP,EE,s]
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
  have out : outside (PP p q r) (EE a b c) s=2*p^a := by simp [outside,Fin.prod_univ_four,PP,EE,s]
  apply no_round h s (by decide)
  · intro i hi
    rw [out]
    have val : coefficientBound B (height B)*(2*p^a)=budget B*p^a := by unfold budget;ring
    rw [val]
    fin_cases i
    · simp [s] at hi
    · simp [s] at hi
    · exact bigq
    · exact bigr
  · intro i hi
    rw [erase0]
    have z : yr 2 1=1 := by decide +kernel
    fin_cases i <;> simp_all [Fin.prod_univ_four,PP,EE,s]
    · exact control (h.prime 2).one_lt (h.prime 1).one_lt (h.prime 3).one_lt
        (h.pos 1) (h.pos 3) (w.trans_le (by nlinarith only [Nat.zero_le a]))
    · exact control (h.prime 3).one_lt (h.prime 1).one_lt (h.prime 2).one_lt
        (h.pos 1) (h.pos 2) (x.trans_le (by nlinarith only [Nat.zero_le a]))
end OMA.RankThreeSmall245212

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

/- Integer endpoint tests for a dyadic rank-three support. -/
namespace OMA.RankThreeRanges245212
open OMA.Smooth245212 OMA.OddFaces245212 OMA.Large245212

def den (p q r : ℕ) := 5*p*q*r-8*(p-1)*(q-1)*(r-1)
def leastExp (p q r : ℕ) := max 1 ((5*q*r-1)/den p q r)

private theorem lim {p : ℕ} (hp : 1<p) : limitX p=(p:ℚ)/((p:ℚ)-1) := by
  have pr : (1:ℚ)<p := by exact_mod_cast hp
  change 1+(1-0)/((p:ℚ)-1)=_
  field_simp [(sub_pos.mpr pr).ne'];ring

theorem capNat {p q r : ℕ} (hp : 1<p) (hq : 1<q) (hr : 1<r)
    (cap : 8≤5*(limitX p*limitX q*limitX r)) :
    8*(p-1)*(q-1)*(r-1)≤5*p*q*r := by
  have h (v : ℕ) (x : 1<v) : (0:ℚ)<(v:ℚ)-1 := sub_pos.mpr (by exact_mod_cast x)
  rw [lim hp,lim hq,lim hr] at cap
  have u := mul_le_mul_of_nonneg_right cap (mul_nonneg (mul_nonneg (h p hp).le (h q hq).le) (h r hr).le)
  have v : (8:ℚ)*((p:ℚ)-1)*((q:ℚ)-1)*((r:ℚ)-1)≤5*p*q*r := by
    calc
      _ = 8*(((p:ℚ)-1)*((q:ℚ)-1)*((r:ℚ)-1)) := by ring
      _ ≤ _ := u
      _ = _ := by field_simp [(h p hp).ne',(h q hq).ne',(h r hr).ne']
  have z : (8:ℚ)*((p-1:ℕ):ℚ)*((q-1:ℕ):ℚ)*((r-1:ℕ):ℚ)≤5*p*q*r := by
    simpa [Nat.cast_sub (show 1≤p by omega),Nat.cast_sub (show 1≤q by omega),Nat.cast_sub (show 1≤r by omega)] using v
  exact_mod_cast z

theorem first_tests {p q r a : ℕ} (hp : p.Prime) (hq : 1<q) (hr : 1<r) (ap : 0<a)
    (cap : 8≤5*X p (some a)*(limitX q*limitX r)) :
    leastExp p q r≤a ∧ 8*OMA.Large245212.tax p a*(q-1)*(r-1)≤5*wt p a*q*r := by
  have pg := hp.one_lt
  have h (v : ℕ) (x : 1<v) : (0:ℚ)<(v:ℚ)-1 := sub_pos.mpr (by exact_mod_cast x)
  let U := Y p (some a)
  have lx : X p (some a)*((p:ℚ)-1)=(p:ℚ)-U := by
    unfold X U;field_simp [(h p pg).ne'];ring
  rw [lim hq,lim hr] at cap
  have t := mul_le_mul_of_nonneg_right cap (mul_nonneg (h q hq).le (h r hr).le)
  have one : (8:ℚ)*((q:ℚ)-1)*((r:ℚ)-1)≤5*X p (some a)*q*r := by
    calc
      _ = 8*(((q:ℚ)-1)*((r:ℚ)-1)) := by ring
      _ ≤ _ := t
      _ = _ := by field_simp [(h q hq).ne',(h r hr).ne']
  have gap := mul_le_mul_of_nonneg_right one (h p pg).le
  have gap' : (5:ℚ)*q*r*U ≤ 5*p*q*r-8*((p:ℚ)-1)*((q:ℚ)-1)*((r:ℚ)-1) := by
    linear_combination (norm := linarith) gap + (5*(q:ℚ)*r)*lx
  have u0 := y_nonneg pg (some a)
  have pos : (0:ℚ)<(a:ℚ)+1 := by positivity
  have flat : (1:ℚ) ≤ U*((a:ℚ)+1) := (div_le_iff₀ pos).mp (OMA.Moving245212.y_infty (e:=a) pg)
  have e_bound : (5:ℚ)*q*r ≤ (5*p*q*r-8*((p:ℚ)-1)*((q:ℚ)-1)*((r:ℚ)-1))*((a:ℚ)+1) := by
    nlinarith only [mul_le_mul_of_nonneg_right gap' pos.le,
      mul_le_mul_of_nonneg_left flat (show (0:ℚ)≤5*q*r by positivity)]
  have base : 8*(p-1)*(q-1)*(r-1)≤5*p*q*r := by
    have le : (8:ℚ)*((p-1:ℕ):ℚ)*((q-1:ℕ):ℚ)*((r-1:ℕ):ℚ)≤5*p*q*r := by
      simp only [Nat.cast_sub (show 1≤p by omega),Nat.cast_sub (show 1≤q by omega),Nat.cast_sub (show 1≤r by omega),Nat.cast_one]
      nlinarith only [gap',mul_nonneg (by positivity : (0:ℚ)≤5*q*r) u0]
    exact_mod_cast le
  have len : 5*q*r≤den p q r*(a+1) := by
    have dc : (den p q r:ℚ)=5*p*q*r-8*((p:ℚ)-1)*((q:ℚ)-1)*((r:ℚ)-1) := by
      unfold den; push_cast [Nat.cast_sub base,Nat.cast_sub (show 1≤p by omega),
        Nat.cast_sub (show 1≤q by omega),Nat.cast_sub (show 1≤r by omega)];ring
    rw [← dc] at e_bound
    exact_mod_cast e_bound
  have dpos : 0<den p q r := by
    by_contra! h0
    have z : den p q r=0 := by omega
    rw [z,zero_mul] at len
    have w : 0<5*q*r := by positivity
    omega
  constructor
  · apply max_le ap
    apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul dpos).mpr
    have positive : 0<5*q*r := by positivity
    exact (by omega : 5*q*r-1 <5*q*r).trans_le (by simpa only [mul_comm (den p q r)] using len)
  · have ww := (OMA.Large245212.moments hp a).2
    have xf := x_factor hp a
    rw [← ww] at xf
    have t0 : (0:ℚ)≤((a:ℚ)+1)*(p:ℚ)^a := by positivity
    have cmp := mul_le_mul_of_nonneg_right one t0
    have ru : (8:ℚ)*(OMA.Large245212.tax p a:ℚ)*((q-1:ℕ):ℚ)*((r-1:ℕ):ℚ)≤5*wt p a*q*r := by
      simp only [OMA.Large245212.tax,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_pow,
        Nat.cast_sub (show 1≤q by omega),Nat.cast_sub (show 1≤r by omega)]
      nlinarith only [cmp,congrArg ((5*(q:ℚ)*r)*·) xf]
    exact_mod_cast ru
end OMA.RankThreeRanges245212

end

section

/- A bounded two-coordinate scan; the third coordinate is recovered rather
than iterated. All discarded prefixes fail a necessary Euler inequality. -/
namespace OMA.RankThreeScan245212
open OMA.RankThreeSmall245212 OMA.RankThreeRanges245212 OMA.RankThreeLast245212 OMA.Large245212
open scoped ArithmeticFunction.sigma

def interval (lo hi : ℕ) := List.range' lo (hi+1-lo)

theorem mem_interval {lo hi i : ℕ} (lower : lo ≤ i) (upper : i ≤ hi) : i∈interval lo hi := by
  exact List.mem_range'_1.mpr ⟨lower,by omega⟩

def row (B p q r a : ℕ) : Bool :=
  let w := wt p a
  let t := tax p a
  if 5*w*q*r < 8*t*(q-1)*(r-1) then true else
    let s := sig p a
    let H := height B
    (interval (leastExp q p r) (next B p a q r)).all fun b =>
      reject r (5*w*wt q b) (3*s*sig q b) (4*t*tax q b) H

def check (B p q r : ℕ) : Bool :=
  (interval (leastExp p q r) (first B p)).all (row B p q r)

theorem check_false {B p q r a b c : ℕ} (pp : p.Prime) (qp : q.Prime) (rp : r.Prime)
    (po : 3≤p) (qo : 3≤q) (ro : 3≤r) (pq : p≠q) (pr : p≠r) (qr : q≠r)
    (ap : 0<a) (bp : 0<b) (cp : 0<c) (a1 : a≤first B p) (b2 : b≤next B p a q r)
    (cb : c≤height B) (h : Bal p q r a b c)
    (hit : OeisA245212.a (2*p^a*q^b*r^c)=(σ 1 (2*p^a*q^b*r^c):ℤ)) : check B p q r=false := by
  have f := first_tests pp qp.one_lt rp.one_lt ap
    (OMA.RankThreeCap245212.one_cap po qp.one_lt rp.one_lt bp h)
  have g := first_tests qp pp.one_lt rp.one_lt bp
    (OMA.RankThreeCap245212.one_cap qo pp.one_lt rp.one_lt ap
      (by unfold Bal at h; convert h using 1; ring))
  have zz := prefix_false pp qp rp (by omega) (by omega) (by omega) pq pr qr cp cb hit
  apply Bool.eq_false_iff.mpr
  intro passed
  obtain rr := List.all_eq_true.mp passed a (mem_interval f.1 a1)
  simp only [row,not_lt.mpr f.2,if_false] at rr
  have y := List.all_eq_true.mp rr b (mem_interval g.1 b2)
  simp [zz] at y

end OMA.RankThreeScan245212

end

section

/- Reindex the three odd powers, check each possible order of the two
small exponents, and extract one of the finitely many supports. -/
namespace OMA.RankThreeMiddle245212
open OMA.RankThreeSmall245212 OMA.RankThreeScan245212 OMA.RankThreeRanges245212
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
  hit : OeisA245212.a (2*p^a*q^b*r^c)=(σ 1 (2*p^a*q^b*r^c):ℤ)

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
  · rw [show 2*q^b*r^c*p^a=2*p^a*q^b*r^c by ring]; exact s.hit

theorem after_first (a1 : a≤first B p) (ck : check B p q r=true) (ck' : check B p r q=true) : False := by
  rcases small_two s.ctx with h|h
  · simp [check_false s.pp s.qp s.rp s.po s.qo s.ro s.pq s.pr s.qr s.ap s.bp s.cp a1 h s.cb s.h s.hit] at ck
  · let t := s.swap
    simp [check_false t.pp t.qp t.rp t.po t.qo t.ro t.pq t.pr t.qr t.ap t.bp t.cp a1 h t.cb t.h t.hit] at ck'
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

def lastBase (q : ℕ) := 16*(q-1)/(q-16)

def supports : List (ℕ×ℕ) :=
  [17,19,23,29,31].flatMap fun q =>
    ((interval (q+1) (lastBase q)).filter (fun r => decide (Nat.Prime r))).map (q,·)

theorem close (ok : ∀ z∈supports,Facts z.2 3 z.1 z.2) {q r a b c : ℕ}
    (qp : q.Prime) (rp : r.Prime) (middle : 17≤q) (qr : q<r) (ap : 0<a) (bp : 0<b) (cp : 0<c) :
    OeisA245212.a (2*3^a*q^b*r^c)≠(σ 1 (2*3^a*q^b*r^c):ℤ) := by
  intro hit
  have n := OMA.RankThreeCap245212.norm (by decide : Nat.Prime 3) qp rp (by decide) (by omega) qr hit
  have cap := OMA.RankThreeCap245212.caps (by decide : 1<3) qp.one_lt rp.one_lt ap n
  have bound (u v : ℕ) (up : u≤q) (vr : v≤r) (ug : 1<u) (vg : 1<v)
      (bad : 5*(limitX 3*limitX u*limitX v)<8) : False := by
    have h := mul_le_mul (mul_le_mul_of_nonneg_left (cap_anti ug up)
      (x_nonneg (by decide : 1<3) none)) (cap_anti vg vr) (x_nonneg rp.one_lt none)
      (mul_nonneg (x_nonneg (by decide : 1<3) none) (x_nonneg ug none))
    change limitX 3*limitX q*limitX r≤limitX 3*limitX u*limitX v at h
    linarith
  have q32 : q<32 := by by_contra! hi; exact bound 32 32 hi (by omega) (by decide) (by decide) (by decide +kernel)
  have num := capNat (by decide : 1<3) qp.one_lt rp.one_lt cap
  have boundR : r≤lastBase q := by
    apply (Nat.le_div_iff_mul_le (by omega : 0<q-16)).mpr
    have qq : q-16+16=q := by omega
    have qs : q-1+1=q := by omega
    have rs : r-1+1=r := by omega
    have x := congrArg (·*(r-1)) qs
    have y := congrArg (·*q) rs
    have z := congrArg (·*r) qq
    norm_num at num
    nlinarith only [num,x,y,z,qs]
  have qmem : q∈([17,19,23,29,31]:List ℕ) := by interval_cases q <;> norm_num at *
  have mem : (q,r)∈supports := by
    apply List.mem_flatMap.mpr
    refine ⟨q,qmem,List.mem_map.mpr ⟨r,?_,rfl⟩⟩
    simpa [rp] using (mem_interval qr boundR)
  obtain ⟨aa,bb,cc⟩ := exponent_height (by decide : Nat.Prime 3) qp rp (by decide) (by omega)
    qr ap bp cp hit
  apply exclude (B:=r) (a:=a) (b:=b) (c:=c) _ (ok _ mem)
  exact ⟨by decide,qp,rp,by decide,by omega,by omega,by omega,by omega,qr.ne,by omega,qr.le,le_rfl,
    ap,bp,cp,aa,bb,cc,n,hit⟩
end OMA.RankThreeMiddle245212

end

section

/- Verified k=1 three-prime support table. -/
namespace OMA.RankThreeData245212
open OMA.RankThreeMiddle245212
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000

theorem row17_19 : Facts 19 3 17 19  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row17_23 : Facts 23 3 17 23  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row17_29 : Facts 29 3 17 29  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row17_31 : Facts 31 3 17 31  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row17_37 : Facts 37 3 17 37  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row17_41 : Facts 41 3 17 41  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row17_43 : Facts 43 3 17 43  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row17_47 : Facts 47 3 17 47  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row17_53 : Facts 53 3 17 53  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row17_59 : Facts 59 3 17 59  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row17_61 : Facts 61 3 17 61  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row17_67 : Facts 67 3 17 67  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row17_71 : Facts 71 3 17 71  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row17_73 : Facts 73 3 17 73  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row17_79 : Facts 79 3 17 79  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row17_83 : Facts 83 3 17 83  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row17_89 : Facts 89 3 17 89  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row17_97 : Facts 97 3 17 97  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row17_101 : Facts 101 3 17 101  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row17_103 : Facts 103 3 17 103  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row17_107 : Facts 107 3 17 107  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row17_109 : Facts 109 3 17 109  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row17_113 : Facts 113 3 17 113  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row17_127 : Facts 127 3 17 127  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row17_131 : Facts 131 3 17 131  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row17_137 : Facts 137 3 17 137  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row17_139 : Facts 139 3 17 139  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row17_149 : Facts 149 3 17 149  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row17_151 : Facts 151 3 17 151  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row17_157 : Facts 157 3 17 157  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row17_163 : Facts 163 3 17 163  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row17_167 : Facts 167 3 17 167  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row17_173 : Facts 173 3 17 173  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row17_179 : Facts 179 3 17 179  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row17_181 : Facts 181 3 17 181  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row17_191 : Facts 191 3 17 191  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row17_193 : Facts 193 3 17 193  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row17_197 : Facts 197 3 17 197  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row17_199 : Facts 199 3 17 199  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row17_211 : Facts 211 3 17 211  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row17_223 : Facts 223 3 17 223  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row17_227 : Facts 227 3 17 227  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row17_229 : Facts 229 3 17 229  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row17_233 : Facts 233 3 17 233  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row17_239 : Facts 239 3 17 239  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row17_241 : Facts 241 3 17 241  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row17_251 : Facts 251 3 17 251  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row19_23 : Facts 23 3 19 23  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row19_29 : Facts 29 3 19 29  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row19_31 : Facts 31 3 19 31  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row19_37 : Facts 37 3 19 37  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row19_41 : Facts 41 3 19 41  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row19_43 : Facts 43 3 19 43  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row19_47 : Facts 47 3 19 47  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row19_53 : Facts 53 3 19 53  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row19_59 : Facts 59 3 19 59  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row19_61 : Facts 61 3 19 61  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row19_67 : Facts 67 3 19 67  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row19_71 : Facts 71 3 19 71  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row19_73 : Facts 73 3 19 73  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row19_79 : Facts 79 3 19 79  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row19_83 : Facts 83 3 19 83  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row19_89 : Facts 89 3 19 89  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row23_29 : Facts 29 3 23 29  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row23_31 : Facts 31 3 23 31  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row23_37 : Facts 37 3 23 37  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row23_41 : Facts 41 3 23 41  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row23_43 : Facts 43 3 23 43  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row23_47 : Facts 47 3 23 47  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel
theorem row29_31 : Facts 31 3 29 31  := by constructor <;> first | (unfold OMA.RankThreeSmall245212.seed; decide +kernel) | decide +kernel

theorem data : ∀ z∈supports,Facts z.2 3 z.1 z.2 := by
  have same : supports=[(17,19),(17,23),(17,29),(17,31),(17,37),(17,41),(17,43),(17,47),(17,53),(17,59),(17,61),(17,67),(17,71),(17,73),(17,79),(17,83),(17,89),(17,97),(17,101),(17,103),(17,107),(17,109),(17,113),(17,127),(17,131),(17,137),(17,139),(17,149),(17,151),(17,157),(17,163),(17,167),(17,173),(17,179),(17,181),(17,191),(17,193),(17,197),(17,199),(17,211),(17,223),(17,227),(17,229),(17,233),(17,239),(17,241),(17,251),(19,23),(19,29),(19,31),(19,37),(19,41),(19,43),(19,47),(19,53),(19,59),(19,61),(19,67),(19,71),(19,73),(19,79),(19,83),(19,89),(23,29),(23,31),(23,37),(23,41),(23,43),(23,47),(29,31)] := by decide +kernel
  rw [same]
  simp only [List.forall_mem_cons,List.not_mem_nil]
  exact ⟨row17_19,row17_23,row17_29,row17_31,row17_37,row17_41,row17_43,row17_47,row17_53,row17_59,row17_61,row17_67,row17_71,row17_73,row17_79,row17_83,row17_89,row17_97,row17_101,row17_103,row17_107,row17_109,row17_113,row17_127,row17_131,row17_137,row17_139,row17_149,row17_151,row17_157,row17_163,row17_167,row17_173,row17_179,row17_181,row17_191,row17_193,row17_197,row17_199,row17_211,row17_223,row17_227,row17_229,row17_233,row17_239,row17_241,row17_251,row19_23,row19_29,row19_31,row19_37,row19_41,row19_43,row19_47,row19_53,row19_59,row19_61,row19_67,row19_71,row19_73,row19_79,row19_83,row19_89,row23_29,row23_31,row23_37,row23_41,row23_43,row23_47,row29_31,fun _ h => h.elim⟩

open scoped ArithmeticFunction.sigma
theorem no_middle_ge_seventeen {q r a b c : ℕ} (qp : q.Prime) (rp : r.Prime)
    (middle : 17≤q) (qr : q<r) (ap : 0<a) (bp : 0<b) (cp : 0<c) :
    OeisA245212.a (2*3^a*q^b*r^c)≠(σ 1 (2*3^a*q^b*r^c):ℤ) :=
  close data qp rp middle qr ap bp cp
end OMA.RankThreeData245212

end

#print axioms OMA.RankThreeOne245212.no_least_ge_five

#print axioms OMA.RankThreeData245212.no_middle_ge_seventeen
