import FormalConjectures.OEIS.«245212»






/-! OEIS A245212: exact dyadic order four, three odd prime bases, least base at least seven. -/

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

/- Rounding one local factor cannot preserve the exact score at an odd
solution.  Its derivative is the nonzero cofactor divisor moment. -/
namespace OMA.Height245212
open OMA.Smooth245212 Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma Function
noncomputable section
variable (p e : Fin 4 → ℕ)

theorem singleton_ne (hp : ∀ i,(p i).Prime) (odd : ∀ i,3≤p i)
    (inj : Function.Injective p) (sol : OeisA245212.a (total p e)=(σ 1 (total p e):ℤ))
    (i : Fin 4) : scoreM p e {i}≠normalized p e := by
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
  have nz := OMA.PrimePowerDiv245212.nonzero mpos (hp i) (by have:=odd i; omega) mpi (e i) (rep ▸ sol)
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

theorem peel {B E : ℕ} (prime : ∀ i,(p i).Prime) (odd : ∀ i,3≤p i)
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
    exact singleton_ne p e prime odd inj sol i (same.trans norm.symm)

theorem outside_erase {s : Finset (Fin 4)} {i : Fin 4} (hi : i∈s) :
    outside p e (s.erase i)=outside p e s*(p i^e i) := by
  let a (j : Fin 4) := if j∈s then 1 else p j^e j
  let b (j : Fin 4) := if j∈s.erase i then 1 else p j^e j
  have eq : (∏ j∈univ.erase i,b j)=∏ j∈univ.erase i,a j :=
    prod_congr rfl fun j hj=>by simp [a,b,(mem_erase.mp hj).1]
  change (∏ j,b j)=(∏ j,a j)*(p i^e i)
  rw [←prod_erase_mul _ b (mem_univ i),←prod_erase_mul _ a (mem_univ i),eq]
  simp [a,b,hi]

theorem total_bound {B E : ℕ} (prime : ∀ i,(p i).Prime) (odd : ∀ i,3≤p i)
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
      obtain ⟨i,hi,sm⟩ := peel p e prime odd pos inj bp be sol s (card_pos.mp (by omega))
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

/-- Numerical premise for the exponent-only calculation, with E the actual maximum. -/
theorem max_power {B : ℕ} (prime : ∀ i,(p i).Prime) (odd : ∀ i,3≤p i)
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
    _ ≤ _ := total_bound p e prime odd pos inj bp be sol

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

namespace OMA.RankThreeFourLargeSmall245212
open Finset Nat OMA.Smooth245212 OMA.Height245212
theorem control {p q r b c : ℕ} (pg : 1<p) (qg : 1<q) (rg : 1<r)
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

theorem erase0 (i : Fin 4) (z : Fin 4 → ℚ) :
    (∏ j∈univ.erase i,z j)=∏ j,if j=i then 1 else z j := by
  rw [← Finset.prod_erase_mul univ (fun j => if j=i then 1 else z j) (mem_univ i)]
  simp only [ite_true,mul_one]
  apply Finset.prod_congr rfl
  intro j hj
  rw [if_neg (mem_erase.mp hj).1]


end OMA.RankThreeFourLargeSmall245212

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


private theorem count_le (h : ℕ) : h.divisors.card≤h := by
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

private theorem combine {h v B : ℕ} (pos : 0<h) (small : h≤B) (large : v≤(W h+σ 1 h)^2) :
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

/- A fixed pair with a tiny Euler excess can give a very loose exponent
bound. Replace that bound by a logarithmic integer-rounding test before
enumerating any exponents. -/
namespace OMA.CofactorPairRounding245212
open Nat ArithmeticFunction OMA.Smooth245212
open scoped ArithmeticFunction.sigma
open OMA.PairHeight245212 (moment_bound)

def bits (n : ℕ) := Nat.log 2 n+1
def ceiling (h q E : ℕ) := 2+3*(bits h+E*bits q)
def cost (A S q M : ℕ) := 2*A*(M+1)*q^2+A+S*q^2
def threshold (h A S p q E : ℕ) :=
  max (S*q/A+1) (Nat.log p (cost A S q (ceiling h q E))+1)

private theorem bits_bound (n : ℕ) : n≤2^bits n := (lt_pow_succ_log_self (by decide) n).le

private theorem degree {h p q a d E z : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime)
    (oq : q≠2) (cq : h.Coprime q) (pq : p≠q) (pz : p≤z) (ae : a≤E) (dp : 0<d)
    (eqn : OeisA245212.a (h*p^a*q^d)=(σ 1 (h*p^a*q^d):ℤ)) : d≤ceiling h z E := by
  let b:=h*p^a
  have pp:=hp.pos
  have pos : 0<b := by dsimp [b];positivity
  have bound := OMA.PairExtension245212.last_log pos hq oq
    (cq.mul_left (((coprime_primes hp hq).mpr pq).pow_left _)) dp eqn
  let N:=bits h+E*bits z
  have tiny : b≤2^N := by
    dsimp [b,N]
    rw [pow_add,Nat.mul_comm E,pow_mul]
    apply Nat.mul_le_mul (bits_bound h)
    exact (Nat.pow_le_pow_left (pz.trans (bits_bound z)) a).trans
      (Nat.pow_le_pow_right (by positivity) ae)
  have weight : W b+σ 1 b≤2^(1+3*N) := by
    rw [pow_add,pow_one,Nat.mul_comm 3,pow_mul]
    exact (OMA.PairHeight245212.moment_bound pos).trans (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left tiny 3))
  rw [Nat.log2_eq_log_two] at bound
  have logs := Nat.log_mono_right (b:=2) weight
  rw [Nat.log_pow (by decide)] at logs
  change d≤2+3*N
  omega

private theorem squeeze {u v A S p q B C P Q M N : ℤ}
    (pq : p≤q) (u0 : u=p-1) (v0 : v=q-1)
    (A0 : 0<A) (S0 : 0≤S) (P0 : 1≤P) (Q0 : 1≤Q)
    (bp : 1≤B) (bm : B≤M+1) (cm : C≤M+1)
    (bu : S*q≤A*(B-1)) (cv : S*q≤A*(C-1)) (pr : 2≤p)
    (pbig : 2*A*(M+1)*q^2+A+S*q^2<P) (qbig : 2*A*(M+1)*q^2+A+S*q^2<Q)
    (identity : N*P*Q=q*(A*(C*v-1)-S*u*v)*Q+p*(A*(B*u-1)-S*u*v)*P+A+S*u*v) : False := by
  let x:=q*(A*(C*v-1)-S*u*v)
  let y:=p*(A*(B*u-1)-S*u*v)
  let w:=A+S*u*v
  let t:=A*(M+1)*q^2
  have up : 1≤u := by omega
  have vp : 1≤v := by omega
  have uv : u≤q := by omega
  have vq : v≤q := by omega
  have q0 : 0≤q := by omega
  have x0 : 0≤x := by
    apply mul_nonneg q0
    nlinarith only [mul_le_mul_of_nonneg_right cv (by omega : 0≤v),
      mul_nonneg (mul_nonneg S0 (by omega : 0≤v)) (sub_nonneg.mpr uv),
      mul_nonneg A0.le (by omega : 0≤v-1)]
  have y0 : 0≤y := by
    apply mul_nonneg (by omega)
    nlinarith only [mul_le_mul_of_nonneg_right bu (by omega : 0≤u),
      mul_nonneg (mul_nonneg S0 (by omega : 0≤u)) (sub_nonneg.mpr vq),
      mul_nonneg A0.le (by omega : 0≤u-1)]
  have w0 : 0<w := by dsimp [w];have := mul_nonneg (mul_nonneg S0 (by omega : 0≤u)) (by omega : 0≤v);omega
  have wmax : w≤A+S*q^2 := by
    dsimp [w]; nlinarith only [mul_le_mul_of_nonneg_left (mul_le_mul uv vq (by omega) q0) S0]
  have xx : x≤t := by
    dsimp [x,t]
    have cBound := mul_le_mul cm vq (by omega) (by omega : 0≤M+1)
    nlinarith only [mul_le_mul_of_nonneg_left cBound (mul_nonneg q0 A0.le),
      mul_nonneg (mul_nonneg (mul_nonneg q0 S0) (by omega : 0≤u)) (by omega : 0≤v),mul_nonneg q0 A0.le]
  have yy : y≤t := by
    dsimp [y,t]
    have bBound := mul_le_mul bm uv (by omega) (by omega : 0≤M+1)
    have allBound := mul_le_mul pq bBound (mul_nonneg (by omega) (by omega)) q0
    nlinarith only [mul_le_mul_of_nonneg_left allBound A0.le,
      mul_nonneg (mul_nonneg (mul_nonneg (by omega : 0≤p) S0) (by omega : 0≤u)) (by omega : 0≤v),
      mul_nonneg (by omega : 0≤p) A0.le]
  rw [add_assoc (q*_ *Q+p*_ *P) A] at identity
  change N*P*Q=x*Q+y*P+w at identity
  have high : 1≤N := by
    by_contra! off
    have v := mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by omega : N≤0) (by omega : 0≤P)) (by omega : 0≤Q)
    nlinarith only [identity,v,mul_nonneg x0 (by omega : 0≤Q),mul_nonneg y0 (by omega : 0≤P),w0]
  have lhs := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right high (by omega : 0≤P)) (by omega : 0≤Q)
  have pcap : 2*t+w<P := by dsimp [t];linarith only [pbig,wmax]
  have qcap : 2*t+w<Q := by dsimp [t];linarith only [qbig,wmax]
  rcases le_total P Q with l|l
  · nlinarith only [identity,lhs,mul_le_mul_of_nonneg_right xx (by omega : 0≤Q),
      mul_le_mul yy l (by omega : 0≤P) (x0.trans xx),mul_le_mul_of_nonneg_left Q0 w0.le,
      mul_lt_mul_of_pos_right pcap (by omega : 0<Q)]
  · nlinarith only [identity,lhs,mul_le_mul xx l (by omega : 0≤Q) (y0.trans yy),
      mul_le_mul_of_nonneg_right yy (by omega : 0≤P),mul_le_mul_of_nonneg_left P0 w0.le,
      mul_lt_mul_of_pos_right qcap (by omega : 0<P)]

theorem shortened {h p q a d E : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime)
    (op : 3≤p) (cp : h.Coprime p) (cq : h.Coprime q) (pq : p<q) (aa : 0<a) (dd : 0<d)
    (small : min a d≤E) (eqn : OeisA245212.a (h*p^a*q^d)=(σ 1 (h*p^a*q^d):ℤ)) :
    min a d < threshold h (W h) (σ 1 h) p q E := by
  let A:=W h
  let S:=σ 1 h
  let M:=ceiling h q E
  let L:=threshold h A S p q E
  have a0 : 0<A := by
    dsimp [A]; rw [w_apply]
    exact Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨1,Nat.one_mem_divisors.mpr hh.ne',by simp⟩
  have bound : a≤M ∧ d≤M := by
    have z : E≤M := by
      have qt := bits_bound q
      have qb : 1≤bits q := by dsimp [bits];omega
      dsimp [M,ceiling]
      nlinarith only [Nat.mul_le_mul_left E qb,Nat.zero_le (bits h)]
    rcases le_total a d with order|order
    · rw [min_eq_left order] at small
      exact ⟨small.trans z,degree hh hp hq (by omega) cq pq.ne pq.le small dd eqn⟩
    · rw [min_eq_right order] at small
      have flipped : OeisA245212.a (h*q^d*p^a)=(σ 1 (h*q^d*p^a):ℤ) := by rwa [mul_right_comm]
      exact ⟨degree hh hq hp (by omega) cp pq.ne.symm le_rfl small aa flipped,small.trans z⟩
  by_contra! bad
  change L ≤ min a d at bad
  have la := bad.trans (min_le_left a d)
  have ld := bad.trans (min_le_right a d)
  have mass : S*q≤A*L := by
    have floor := Nat.lt_mul_div_succ (S*q) a0
    have lim : S*q/A+1≤L := le_max_left _ _
    exact floor.le.trans (by simpa [mul_comm] using Nat.mul_le_mul_left A lim)
  have power : cost A S q M < p^L :=
    (Nat.lt_pow_succ_log_self hp.one_lt _).trans_le
      (Nat.pow_le_pow_right hp.pos (le_max_right _ _))
  have pa := power.trans_le (Nat.pow_le_pow_right hp.pos la)
  have qd := (power.trans_le (Nat.pow_le_pow_right hp.pos ld)).trans_le (Nat.pow_le_pow_left pq.le _)
  have locp:=OMA.ComplementaryLocal245212.moments hp a
  have locq:=OMA.ComplementaryLocal245212.moments hq d
  have ident:=OMA.CofactorPairPole245212.tails (W h) (σ 1 h) ((h:ℤ)*σ 0 h) p q
    (a+1) (d+1) ((p:ℤ)^a) ((q:ℤ)^d) (W (p^a)) (W (q^d)) (σ 1 (p^a)) (σ 1 (q^d))
    locp.2 locq.2 locp.1 locq.1 (OMA.CofactorPairPole245212.balance hh hp hq cp cq pq.ne eqn)
  apply squeeze (p:=(p:ℤ)) (q:=(q:ℤ)) (M:=(M:ℤ)) (by exact_mod_cast pq.le)
    rfl rfl (by exact_mod_cast a0) (by positivity) (by exact_mod_cast Nat.one_le_pow a p hp.pos)
    (by exact_mod_cast Nat.one_le_pow d q hq.pos) (by omega)
    (by exact_mod_cast Nat.succ_le_succ bound.1) (by exact_mod_cast Nat.succ_le_succ bound.2)
    _ _ (by omega) _ _ ident
  · simp only [add_sub_cancel_right];exact_mod_cast mass.trans (Nat.mul_le_mul_left A la)
  · simp only [add_sub_cancel_right];exact_mod_cast mass.trans (Nat.mul_le_mul_left A ld)
  · dsimp [cost] at pa;exact_mod_cast pa
  · dsimp [cost] at qd;exact_mod_cast qd

end OMA.CofactorPairRounding245212

end

section

/- A complete positive certificate runs finite integer tables for the
shape h·p^a·q^d. A zero Euler denominator is left unresolved. No bound
on the exponents or primes is an input to the resulting theorem. -/
namespace OMA.CofactorEulerPair245212
open Nat ArithmeticFunction OMA.Smooth245212
open scoped ArithmeticFunction.sigma
open OMA.Large245212 (moments)

def every (l r : ℕ) (f : ℕ→Bool) := (List.range' l (r+1-l)).all f

theorem checked {l r i : ℕ} {f : ℕ→Bool} (yes : every l r f=true)
    (lo : l ≤ i) (hi : i ≤ r) : f i=true :=
  List.all_eq_true.mp yes i (List.mem_range'_1.mpr ⟨lo,by omega⟩)

def movingRow (A S T p e : ℕ) := OMA.PairExtension245212.free (p+1)
  (A*OMA.Large245212.wt p e) (S*OMA.Large245212.sig p e) (T*OMA.Large245212.tax p e)

theorem moving_row_sound {h p q a d : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime)
    (oq : q≠2) (cp : h.Coprime p) (cq : h.Coprime q) (pq : p<q) (dp : 0<d)
    (yes : movingRow (W h) (σ 1 h) (h*σ 0 h) p a=true) :
    OeisA245212.a (h*p^a*q^d)≠(σ 1 (h*p^a*q^d):ℤ) := by
  obtain ⟨ys,xw⟩ := OMA.Large245212.moments hp a
  have pp:=hp.pos
  have cop:=cp.pow_right a
  apply OMA.PairExtension245212.free_sound (by positivity) hq oq
    (cq.mul_left (((coprime_primes hp hq).mpr pq.ne).pow_left a)) dp pq
  rw [w_mult.map_mul_of_coprime cop,isMultiplicative_sigma.map_mul_of_coprime cop,
    isMultiplicative_sigma.map_mul_of_coprime cop,sigma_zero_apply_prime_pow hp]
  simpa only [movingRow,ys,xw,OMA.Large245212.tax,mul_assoc,mul_left_comm,mul_comm] using yes

def finitePair (h A S T p q : ℕ) : Bool :=
  let floor:=2*T*(p-1)*(q-1)
  let top:=A*p*q
  if ¬q.Prime ∨ ¬h.Coprime q ∨ top<floor then true else
  if top=floor then false else
  let E:=2*A*(p+q)/(top-floor)
  let endAt:=min E (OMA.CofactorPairRounding245212.threshold h A S p q E)
  table A S T p q endAt && table A S T q p endAt

def nextPrime (h A S T p : ℕ) : Bool :=
  if ¬p.Prime ∨ ¬h.Coprime p then true else
  let c:=2*T*(p-1)
  let b:=A*p
  if c<b then every 1 (2*A/(b-c)) (movingRow A S T p) else
  if b<c then every (p+1) (c/(c-b)) (finitePair h A S T p) else false

def decidePair (h A S T : ℕ) :=
  every 3 (1+3*A/(2*T-A)) (nextPrime h A S T)

theorem original_at_prime {h p q a d : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime)
    (op : 3≤p) (cp : h.Coprime p) (cq : h.Coprime q) (pq : p<q)
    (ap : 0<a) (dp : 0<d) (sub : W h+σ 1 h≤2*(h*σ 0 h))
    (row : nextPrime h (W h) (σ 1 h) (h*σ 0 h) p=true) :
    OeisA245212.a (h*p^a*q^d)≠(σ 1 (h*p^a*q^d):ℤ) := by
  intro eqn
  let A:=W h
  let S:=σ 1 h
  let T:=h*σ 0 h
  change A+S≤2*T at sub
  obtain ⟨c,b⟩:=original_cap hh hp hq cp cq pq.ne ap sub eqn
  change 2*T*(p-1)*(q-1)≤A*p*q at c
  change (A:ℚ)*(X p (some a)*X q (some d))<2*(T:ℚ) at b
  have bcast : (A:ℚ)*(X p (some a)*X q (some d))<((2*T:ℕ):ℚ) := by simpa using b
  change nextPrime h A S T p=true at row
  have valid : ¬(¬p.Prime ∨ ¬h.Coprime p) := by tauto
  rw [nextPrime,if_neg valid] at row
  by_cases l : 2*T*(p-1)<A*p
  · rw [if_pos l] at row
    have e := short_first hp hq l bcast
    exact moving_row_sound hh hp hq (by omega) cp cq pq dp (checked row ap (by omega)) eqn
  · rw [if_neg l] at row
    by_cases r : A*p<2*T*(p-1)
    · rw [if_pos r] at row
      have capQ := second_bound hq.one_lt r c
      have point := checked row pq capQ
      have eligible : ¬(¬q.Prime ∨ ¬h.Coprime q ∨ A*p*q<2*T*(p-1)*(q-1)) := by
        have bound := not_lt_of_ge c
        tauto
      rw [finitePair,if_neg eligible] at point
      by_cases same : A*p*q=2*T*(p-1)*(q-1)
      · simp [same] at point
      · rw [if_neg same,Bool.and_eq_true] at point
        have fit := short_pair hp hq (lt_of_le_of_ne c (Ne.symm same)) bcast
        have bounded := Nat.le_trans (Nat.le_succ _) fit
        have smaller := OMA.CofactorPairRounding245212.shortened hh hp hq op cp cq pq ap dp bounded eqn
        exact table_sound hh hp hq (by omega) (by omega) cp cq pq.ne ap dp
          (le_min bounded smaller.le) point.1 point.2 eqn
    · simp [r] at row

theorem original_of_decision {h p q a d : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime)
    (op : 3≤p) (cp : h.Coprime p) (cq : h.Coprime q) (pq : p<q)
    (ap : 0<a) (dp : 0<d) (sub : W h+σ 1 h≤2*(h*σ 0 h))
    (yes : decidePair h (W h) (σ 1 h) (h*σ 0 h)=true) :
    OeisA245212.a (h*p^a*q^d)≠(σ 1 (h*p^a*q^d):ℤ) := by
  intro eqn
  have bound := (original_cap hh hp hq cp cq pq.ne ap sub eqn).1
  have sp := sigma_pos 1 h hh.ne'
  have small := first_bound hp.one_lt pq.le (by omega : W h<2*(h*σ 0 h)) bound
  exact original_at_prime hh hp hq op cp cq pq ap dp sub (checked yes op small) eqn

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

/- Check short intervals separately and join them without reducing the
boolean arithmetic again. All endpoints are checked in the kernel. -/
namespace OMA.RankThreeMiddle245212
open OMA.CofactorEulerPair245212

theorem joinEvery {f : ℕ→Bool} {a b c : ℕ}
    (left : every a b f=true) (right : every (b+1) c f=true) :
    every a c f=true := by
  apply List.all_eq_true.mpr
  intro i hi
  obtain ⟨lo,up⟩:=List.mem_range'_1.mp hi
  by_cases e : i≤b
  · exact List.all_eq_true.mp left i (List.mem_range'_1.mpr ⟨lo,by omega⟩)
  · exact List.all_eq_true.mp right i (List.mem_range'_1.mpr ⟨by omega,by omega⟩)

end OMA.RankThreeMiddle245212

end

section

/- Exact replacement for huge reverse-digit powers. A prime-power
congruence rejects an impossible exponent before evaluating the power. -/
namespace OMA.CofactorGuardFast245212
open Nat ArithmeticFunction OMA.Smooth245212 OMA.CofactorEulerPair245212 OMA.PairExtension245212
open OMA.Large245212 (moments)
open scoped ArithmeticFunction.sigma

def magnitude (A S q : ℕ) := ((A:ℤ)-((q:ℤ)-1)*(S:ℤ)).natAbs

private theorem divides {A S T p f : ℕ} (hp : p.Prime) (ok : permitted A S T p f=true) :
    p^f ∣ magnitude A S p := by
  obtain ⟨sval,wval⟩:=OMA.Large245212.moments hp f
  simp only [permitted,Bool.and_eq_true,decide_eq_true_eq] at ok
  have balance:=ok.2
  rw [sval,wval] at balance
  have van : (p:ZMod (p^f))^f=0 := by rw [←Nat.cast_pow];exact ZMod.natCast_self _
  have w:=congrArg (fun n:ℕ=>(n:ZMod (p^f))) (OMA.PrimePowerDiv245212.weighted hp f)
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_sub hp.pos,Nat.cast_one,Nat.cast_pow,van,mul_zero] at w
  have s : ((p:ZMod (p^f))-1)*(σ 1 (p^f):ℕ) = -1 := by
    rw [sigma_one_apply_prime_pow hp]
    simp only [Nat.cast_sum,Nat.cast_pow]
    rw [mul_comm,geom_sum_mul,pow_succ,van,zero_mul,zero_sub]
  have bb:=congrArg (fun n:ℕ=>(n:ZMod (p^f))) balance
  simp only [OMA.Large245212.tax,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_one,van,mul_zero] at bb
  have iv : ((p^f:ℕ):ℤ) ∣ (A:ℤ)-((p:ℤ)-1)*(S:ℤ) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p^f)).mp
    push_cast
    linear_combination ((p:ZMod (p^f))-1)^2*bb - (A:ZMod (p^f))*((p:ZMod (p^f))-1)*w +
      ((A:ZMod (p^f))-((p:ZMod (p^f))-1)*(S:ZMod (p^f)))*s
  simpa [magnitude] using Int.natAbs_dvd_natAbs.mpr iv

def fastKnown (A S T q : ℕ) : Bool :=
  let C:=OMA.ReverseDigit245212.numerator q A S
  let D:=OMA.ReverseDigit245212.denominator q A T
  if ¬q∣A+S ∨ D=0 then true else
    let f:=(⌊C/D⌋-1).toNat
    let N:=magnitude A S q
    decide (0<N ∧ N.log2<f) || !permitted A S T q f

theorem fastKnown_eq {A S T q : ℕ} (hq : q.Prime) : fastKnown A S T q=known A S T q := by
  simp only [fastKnown,known]
  split
  · rfl
  · let f:=(⌊OMA.ReverseDigit245212.numerator q A S / OMA.ReverseDigit245212.denominator q A T⌋-1).toNat
    let N:=magnitude A S q
    change (decide (0<N ∧ N.log2<f) || !permitted A S T q f)=(!permitted A S T q f)
    by_cases yes : permitted A S T q f=true
    · have impossible : ¬(0<N ∧ N.log2<f) := by
        rintro ⟨pos,small⟩
        have bound := Nat.le_of_dvd pos (divides hq yes)
        have two := (Nat.pow_le_pow_left hq.two_le f).trans bound
        have low := (Nat.le_log_iff_pow_le (by decide : 1<2) pos.ne').mpr two
        rw [Nat.log2_eq_log_two] at small
        omega
      simp [impossible]
    · simp [Bool.eq_false_iff.mpr yes]

def fastRow (A S T p q e : ℕ) := fastKnown (A*OMA.Large245212.wt p e)
  (S*OMA.Large245212.sig p e) (T*OMA.Large245212.tax p e) q

def fastTable (A S T p q E : ℕ) := (List.range E).all fun i=>fastRow A S T p q (i+1)

theorem tables {A S T p q E : ℕ} (hq : q.Prime) : fastTable A S T p q E=table A S T p q E := by
  simp only [fastTable,table,fastRow,row,fastKnown_eq hq]

def fastPair (h A S T p q : ℕ) : Bool :=
  let floor:=2*T*(p-1)*(q-1)
  let top:=A*p*q
  if ¬q.Prime ∨ ¬h.Coprime q ∨ top<floor then true else
  if top=floor then false else
  let E:=2*A*(p+q)/(top-floor)
  let endAt:=min E (OMA.CofactorPairRounding245212.threshold h A S p q E)
  fastTable A S T p q endAt && fastTable A S T q p endAt

theorem pairs {h A S T p : ℕ} (hp : p.Prime) : fastPair h A S T p=finitePair h A S T p := by
  funext q
  by_cases hq : q.Prime
  · simp only [fastPair,finitePair,tables hp,tables hq]
  · simp [fastPair,finitePair,hq]

theorem restore {l r h A S T p : ℕ} (hp : p.Prime)
    (yes : every l r (fastPair h A S T p)=true) : every l r (finitePair h A S T p)=true := by
  simpa only [pairs hp] using yes

end OMA.CofactorGuardFast245212

end

section

/- All integer checks for two new odd primes after a fixed weighted cofactor. -/
namespace OMA.RankThreeFourSmallDecision245212
open Nat ArithmeticFunction OMA.Smooth245212 OMA.CofactorEulerPair245212
open OMA.RankThreeFourSmallBounds245212 OMA.CofactorGuardFast245212
open scoped ArithmeticFunction.sigma
open OMA.Large245212 (force)
open OMA.Large245212 (moments)
open OMA.PairExtension245212 (fit)
open OMA.CofactorGuardFast245212 (tables)
open OMA.CofactorEulerPair245212 (checked)

def fixedPair (h A S T p q : ℕ) : Bool :=
  if ¬q.Prime ∨ ¬h.Coprime q then true else
  if 2*T*(p-1)*(q-1)<A*p*q then fastPair h A S T p q else
    fastTable A S T q p (2*(A+S*(p-1)*(q-1))/(A*q))

theorem pair_sound {h p q a d : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime) (op : 3≤p)
    (cp : h.Coprime p) (cq : h.Coprime q) (pq : p<q) (ap : 0<a) (dp : 0<d)
    (ck : fixedPair h (W h) (σ 1 h) (h*σ 0 h) p q=true) :
    OeisA245212.a (h*p^a*q^d)≠(σ 1 (h*p^a*q^d):ℤ) := by
  intro eqn
  let A:=W h
  let S:=σ 1 h
  let T:=h*σ 0 h
  have b : Bal A S (2*T) p q a d := by
    simpa [A,S,T,Bal] using normalized hh hp hq cp cq pq.ne eqn
  have az : 0<A := by
    dsimp [A];rw [w_apply]
    exact Finset.sum_pos' (fun _ _=>Nat.zero_le _) ⟨1,Nat.one_mem_divisors.mpr hh.ne',by simp⟩
  have sz : 0<S := sigma_pos 1 h hh.ne'
  change fixedPair h A S T p q=true at ck
  have eligible : ¬(¬q.Prime ∨ ¬h.Coprime q) := by tauto
  rw [fixedPair,if_neg eligible] at ck
  by_cases pos : 2*T*(p-1)*(q-1)<A*p*q
  · rw [if_pos pos,pairs hp] at ck
    have elig : ¬(¬q.Prime ∨ ¬h.Coprime q ∨ A*p*q<2*T*(p-1)*(q-1)) := by
      have n := not_lt.mpr pos.le;tauto
    rw [finitePair,if_neg elig,if_neg pos.ne.symm,Bool.and_eq_true] at ck
    have e:=short_pair hp hq pos (strict hp hq sz b)
    have raw := (Nat.le_succ _).trans e
    have l := OMA.CofactorPairRounding245212.shortened hh hp hq op cp cq pq ap dp raw eqn
    exact table_sound hh hp hq (by omega) (by omega) cp cq pq.ne ap dp (le_min raw l.le) ck.1 ck.2 eqn
  · rw [if_neg pos,OMA.CofactorGuardFast245212.tables hp] at ck
    have ed:=under_pair hp hq az b (by omega)
    obtain ⟨j,rfl⟩:=Nat.exists_eq_succ_of_ne_zero dp.ne'
    have one:=List.all_eq_true.mp ck j (List.mem_range.mpr (by omega))
    have kill:=row_sound hh hq hp (by omega) cq cp pq.ne.symm ap one
    exact kill (by rwa [mul_right_comm h])

def freeTo (R A S T D : ℕ) : Bool := every 1 D fun d=>
  let q:=OMA.Large245212.candidate A S T d
  decide (OMA.LastDigit245212.denom A S T d=0 ∨ q<R) || !OMA.PairExtension245212.permitted A S T q d

theorem freeTo_sound {m q d R D : ℕ} (mp : 0 < m) (hq : q.Prime) (cop : m.Coprime q)
    (dp : 0<d) (lo : R≤q) (hi : d≤D) (eqn : OeisA245212.a (m*q^d)=(σ 1 (m*q^d):ℤ)) :
    freeTo R (W m) (σ 1 m) (m*σ 0 m) D≠true := by
  intro ck
  obtain ⟨pos,low,high,_⟩:=OMA.LastDigit245212.balance_digits mp hq cop dp eqn
  have val := OMA.Large245212.force (sigma_pos 1 m mp.ne') hq.one_lt pos low high
  have done_ := OMA.CofactorEulerPair245212.checked ck dp hi
  simp [val,pos.ne',Nat.not_lt_of_ge lo,OMA.PairExtension245212.fit mp hq cop dp eqn] at done_

def moving (R D A S T p b : ℕ) := freeTo R (A*OMA.Large245212.wt p b)
  (S*OMA.Large245212.sig p b) (T*OMA.Large245212.tax p b) D

theorem moving_sound {h p q a d R D : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime)
    (cp : h.Coprime p) (cq : h.Coprime q) (pq : p<q)
    (dp : 0<d) (lo : R≤q) (hi : d≤D)
    (ck : moving R D (W h) (σ 1 h) (h*σ 0 h) p a=true) :
    OeisA245212.a (h*p^a*q^d)≠(σ 1 (h*p^a*q^d):ℤ) := by
  intro eqn
  obtain ⟨sg,wt⟩:=OMA.Large245212.moments hp a
  have cop:=cp.pow_right a
  have pp:=hp.pos
  apply freeTo_sound (by positivity : 0<h*p^a) hq
    (cq.mul_left (((coprime_primes hp hq).mpr pq.ne).pow_left a)) dp lo hi eqn
  rw [w_mult.map_mul_of_coprime cop,isMultiplicative_sigma.map_mul_of_coprime cop,
    isMultiplicative_sigma.map_mul_of_coprime cop,sigma_zero_apply_prime_pow hp]
  simpa only [moving,wt,sg,OMA.Large245212.tax,mul_assoc,mul_comm,mul_left_comm] using ck

def lenD (A S p : ℕ) := 2*(A+S*(p-1))/A
def lenB (A S T p : ℕ) := 4*S*(p-1)/(2*T*(p-1)-A*p)
def capQ (A T p : ℕ) := 1+2*A*p/(2*T*(p-1)-A*p)
def atPrime (h A S T p : ℕ) : Bool :=
  if ¬p.Prime ∨ ¬h.Coprime p then true else
  if 2*T*(p-1)<A*p then every 1 (2*A/(A*p-2*T*(p-1))) (movingRow A S T p) else
  if A*p<2*T*(p-1) then
    every (p+1) (capQ A T p) (fixedPair h A S T p) &&
    every 1 (lenB A S T p) (moving (max (p+1) (capQ A T p+1)) (lenD A S p) A S T p)
  else false

theorem prime_sound {h p q a d : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime) (op : 3≤p)
    (cp : h.Coprime p) (cq : h.Coprime q) (pq : p<q) (ap : 0<a) (dp : 0<d)
    (ck : atPrime h (W h) (σ 1 h) (h*σ 0 h) p=true) :
    OeisA245212.a (h*p^a*q^d)≠(σ 1 (h*p^a*q^d):ℤ) := by
  intro eqn
  let A:=W h
  let S:=σ 1 h
  let T:=h*σ 0 h
  have b : Bal A S (2*T) p q a d := by
    simpa [A,S,T,Bal] using normalized hh hp hq cp cq pq.ne eqn
  have az : 0<A := by
    dsimp [A];rw [w_apply]
    exact Finset.sum_pos' (fun _ _=>Nat.zero_le _) ⟨1,Nat.one_mem_divisors.mpr hh.ne',by simp⟩
  have sz : 0<S := sigma_pos 1 h hh.ne'
  change atPrime h A S T p=true at ck
  have elig : ¬(¬p.Prime ∨ ¬h.Coprime p) := by tauto
  rw [atPrime,if_neg elig] at ck
  by_cases high : 2*T*(p-1)<A*p
  · rw [if_pos high] at ck
    have sh:=short_first hp hq high (strict hp hq sz b)
    exact moving_row_sound hh hp hq (by omega) cp cq pq dp (OMA.CofactorEulerPair245212.checked ck ap (by omega)) eqn
  rw [if_neg high] at ck
  by_cases under : A*p<2*T*(p-1)
  · rw [if_pos under,Bool.and_eq_true] at ck
    by_cases qr : q≤capQ A T p
    · exact pair_sound hh hp hq op cp cq pq ap dp (OMA.CofactorEulerPair245212.checked ck.1 pq qr) eqn
    have sh := under_first hp hq b under
    have eb : a≤lenB A S T p := by change a≤4*S*(p-1)/_; change ¬q≤1+2*A*p/_ at qr; omega
    have low : A*p*q≤2*T*(p-1)*(q-1) := by
      let G:=2*T*(p-1)-A*p
      have val:=Nat.sub_add_cancel under.le
      have gs : 0<G := Nat.sub_pos_of_lt under
      have qq : 2*A*p/G+1≤q-1 := by change ¬q≤1+2*A*p/G at qr;omega
      have less := (Nat.div_lt_iff_lt_mul gs).mp (by omega : 2*A*p/G<q-1)
      have v:=Nat.sub_add_cancel (by omega : 1≤q)
      nlinarith only [less,congrArg (·*(q-1)) val,congrArg (A*p*·) v,Nat.zero_le (A*p)]
    have ed:=(Nat.le_div_iff_mul_le (Nat.mul_pos az hq.pos)).mp (under_pair hp hq az b low)
    have grow : (d+1)*(A*q)≤(2*(A+S*(p-1)))*q := by
      nlinarith only [ed,Nat.mul_le_mul_left (S*(p-1)) (Nat.sub_le q 1),
        Nat.le_mul_of_pos_right A hq.pos]
    have e0 : (d+1)*A≤2*(A+S*(p-1)) := Nat.le_of_mul_le_mul_right (by simpa only [mul_assoc] using grow) hq.pos
    have small : d≤lenD A S p := (Nat.le_succ _).trans ((Nat.le_div_iff_mul_le az).mpr e0)
    exact moving_sound hh hp hq cp cq pq dp (max_le pq (by omega)) small
      (OMA.CofactorEulerPair245212.checked ck.2 ap eb) eqn
  · simp [under] at ck

end OMA.RankThreeFourSmallDecision245212

end

section

/- A logarithmic upper bound for both complementary exponents, using
the smaller actual prime as logarithm base. -/
namespace OMA.RankThreeFourSmallDegree245212
open Nat Finset ArithmeticFunction OMA.Smooth245212
open scoped ArithmeticFunction.sigma
open OMA.CapOrder245212 (geom)

def degree (A S base z E : ℕ) :=
  (Nat.log base z+1)*E+Nat.log base (2*(A*(E+1)+S))+2

theorem one {h p q e f E base z : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime)
    (cp : h.Coprime p) (cq : h.Coprime q) (pq : p≠q) (oq : q≠2) (fp : 0<f)
    (bp : 1<base) (bq : base≤q) (pz : p≤z) (small : e≤E)
    (eqn : OeisA245212.a (h*p^e*q^f)=(σ 1 (h*p^e*q^f):ℤ)) :
    f≤degree (W h) (σ 1 h) base z E := by
  let A:=W h
  let S:=σ 1 h
  let J:=Nat.log base z+1
  let C:=2*(A*(E+1)+S)
  have pp:=hp.pos
  have pos : 0<h*p^e := by positivity
  have eb := OMA.PairExtension245212.last_log_base pos hq oq
    (cq.mul_left (((coprime_primes hp hq).mpr pq).pow_left _)) bp bq fp eqn
  have norm : σ 1 (p^e)<2*p^e := by
    rw [sigma_one_apply_prime_pow hp]
    exact OMA.CapOrder245212.geom p hp.one_lt e
  have w : W (p^e)≤(e+1)*(σ 1 (p^e)) := by
    rw [w_pow hp,sigma_one_apply_prime_pow hp,Finset.mul_sum]
    exact sum_le_sum fun j hj => by
      have le:=show j+1≤e+1 by have := mem_range.mp hj;omega
      simpa only [Nat.mul_comm] using Nat.mul_le_mul_left (p^j) le
  have c:=cp.pow_right e
  have mass : W (h*p^e)+σ 1 (h*p^e)≤C*p^e := by
    rw [w_mult.map_mul_of_coprime c,isMultiplicative_sigma.map_mul_of_coprime c]
    change A*W (p^e)+S*(σ 1 (p^e))≤2*(A*(E+1)+S)*p^e
    nlinarith only [Nat.mul_le_mul_left A w,Nat.mul_le_mul_left (A*(e+1)+S) norm.le,
      Nat.mul_le_mul_right (2*A*p^e) (Nat.succ_le_succ small)]
  have under := Nat.lt_pow_succ_log_self bp C
  have zlim : z≤base^J := (Nat.lt_pow_succ_log_self bp _).le
  have pmax : p^e≤base^(J*E) := by
    rw [pow_mul]
    exact (Nat.pow_le_pow_left (pz.trans zlim) e).trans (Nat.pow_le_pow_right (by positivity) small)
  have upper : W (h*p^e)+σ 1 (h*p^e)<base^(J*E+(Nat.log base C+1)) := by
    rw [pow_add,mul_comm (base^(J*E))]
    exact mass.trans_lt (Nat.mul_lt_mul_of_lt_of_le under pmax (pow_pos (by omega) _))
  have plus : 0<W (h*p^e)+σ 1 (h*p^e) := by have := sigma_pos 1 _ pos.ne';omega
  have cap:=(Nat.log_lt_iff_lt_pow bp plus.ne').mpr upper
  change f≤J*E+Nat.log base C+2
  omega

theorem both {h p q a d E : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime) (op : 3≤p)
    (cp : h.Coprime p) (cq : h.Coprime q) (pq : p<q) (ap : 0<a) (dp : 0<d)
    (small : min a d≤E) (eqn : OeisA245212.a (h*p^a*q^d)=(σ 1 (h*p^a*q^d):ℤ)) :
    a≤degree (W h) (σ 1 h) p q E ∧ d≤degree (W h) (σ 1 h) p q E := by
  have ee : E≤degree (W h) (σ 1 h) p q E := by
    unfold degree; rw [Nat.add_mul,one_mul];omega
  rcases le_total a d with ha|hd
  · rw [min_eq_left ha] at small
    exact ⟨small.trans ee,one hh hp hq cp cq pq.ne (by omega) dp hp.one_lt pq.le pq.le small eqn⟩
  · rw [min_eq_right hd] at small
    have flip : OeisA245212.a (h*q^d*p^a)=(σ 1 (h*q^d*p^a):ℤ) := by rwa [mul_right_comm]
    exact ⟨one hh hq hp cq cp pq.ne.symm (by omega) ap hp.one_lt le_rfl le_rfl small flip,small.trans ee⟩
end OMA.RankThreeFourSmallDegree245212

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

private theorem squeeze {N x y w P Q X L : ℤ} (nz : N≠0) (p : 1≤P) (q : 1≤Q)
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

private theorem coeff {A S p q B M z : ℤ} (a : 0≤A) (s : 0≤S)
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

theorem small {h p q a d M : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime)
    (cp : h.Coprime p) (cq : h.Coprime q) (pq : p<q)
    (am : a≤M) (dm : d≤M) (qm : M+1<q) (qt : ¬q∣2*(h*σ 0 h))
    (eqn : OeisA245212.a (h*p^a*q^d)=(σ 1 (h*p^a*q^d):ℤ)) :
    min a d≤Nat.log p (cost (W h) (σ 1 h) q M) := by
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
  have x:=coeff (p:=(q:ℤ)) (q:=(p:ℤ)) (z:=(q:ℤ)) (A:=(A:ℤ)) (S:=(S:ℤ)) (M:=(M:ℤ)) (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    (by exact_mod_cast hq.two_le) (by exact_mod_cast hp.two_le) (by rfl : (q:ℤ)≤q)
    (by exact_mod_cast pq.le) (by omega : 1≤(d:ℤ)+1) (by omega)
  have y:=coeff (p:=(p:ℤ)) (q:=(q:ℤ)) (z:=(q:ℤ)) (A:=(A:ℤ)) (S:=(S:ℤ)) (M:=(M:ℤ)) (Int.natCast_nonneg _) (Int.natCast_nonneg _)
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
  have k:=squeeze (P:=(p:ℤ)^a) (Q:=(q:ℤ)^d) n (by exact_mod_cast Nat.one_le_pow a p hp.pos)
    (by exact_mod_cast Nat.one_le_pow d q hq.pos) x y w0 wle (by simpa only [add_assoc] using id)
  have result : min (p^a) (q^d)≤cost A S q M := by unfold cost;rw [Nat.add_assoc];exact_mod_cast k
  have pmin : p^(min a d)≤ min (p^a) (q^d) := le_min
    (Nat.pow_le_pow_right hp.pos (min_le_left _ _))
    ((Nat.pow_le_pow_right hp.pos (min_le_right _ _)).trans (Nat.pow_le_pow_left pq.le d))
  exact Nat.le_log_of_pow_le hp.one_lt (pmin.trans result)

end OMA.RankThreeFourSmallSeparation245212

end

section

/- Finite prime pairs need only a short exponent interval. A previously
excluded initial range of exponents may be skipped in the forward table. -/
namespace OMA.RankThreeFourSmallCut245212
open Nat ArithmeticFunction OMA.Smooth245212 OMA.CofactorEulerPair245212
open OMA.CofactorGuardFast245212 OMA.RankThreeFourSmallBounds245212
open scoped ArithmeticFunction.sigma
open OMA.CofactorEulerPair245212 (checked)

def initial (h A S T p q : ℕ) :=
  let E:=2*A*(p+q)/(A*p*q-2*T*(p-1)*(q-1))
  min E (OMA.CofactorPairRounding245212.threshold h A S p q E)

def horizon (h A S T p q : ℕ) :=
  let E:=initial h A S T p q
  let M:=OMA.RankThreeFourSmallDegree245212.degree A S p q E
  if M+1<q ∧ ¬q∣2*T then min E (Nat.log p (OMA.RankThreeFourSmallSeparation245212.cost A S q M)) else E

theorem horizon_sound {h p q a d : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime) (op : 3≤p)
    (cp : h.Coprime p) (cq : h.Coprime q) (pq : p<q) (ap : 0<a) (dp : 0<d)
    (big : 2*(h*σ 0 h)*(p-1)*(q-1)<W h*p*q)
    (eqn : OeisA245212.a (h*p^a*q^d)=(σ 1 (h*p^a*q^d):ℤ)) :
    min a d≤horizon h (W h) (σ 1 h) (h*σ 0 h) p q := by
  let A:=W h
  let S:=σ 1 h
  let T:=h*σ 0 h
  have b : Bal A S (2*T) p q a d := by simpa [A,S,T,Bal] using normalized hh hp hq cp cq pq.ne eqn
  have e:=short_pair hp hq big (strict hp hq (sigma_pos 1 h hh.ne') b)
  have raw:=(Nat.le_succ _).trans e
  have bound:=OMA.CofactorPairRounding245212.shortened hh hp hq op cp cq pq ap dp raw eqn
  have lo : min a d≤ initial h A S T p q := le_min raw bound.le
  obtain ⟨ab,db⟩:=OMA.RankThreeFourSmallDegree245212.both hh hp hq op cp cq pq ap dp lo eqn
  change min a d≤horizon h A S T p q
  unfold horizon
  dsimp only
  split
  next yes => exact le_min lo (OMA.RankThreeFourSmallSeparation245212.small hh hp hq cp cq pq ab db yes.1 yes.2 eqn)
  next _ => exact lo

def fixed (F h A S T p q : ℕ) :=
  if ¬q.Prime ∨ ¬h.Coprime q then true else
  if 2*T*(p-1)*(q-1)<A*p*q then
    let E:=horizon h A S T p q
    every (F+1) E (fastRow A S T p q) && every 1 E (fastRow A S T q p)
  else every 1 (2*(A+S*(p-1)*(q-1))/(A*q)) (fastRow A S T q p)

theorem fixed_sound {F h p q a d : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime) (op : 3≤p)
    (cp : h.Coprime p) (cq : h.Coprime q) (pq : p<q) (ap : F<a) (dp : 0<d)
    (ck : fixed F h (W h) (σ 1 h) (h*σ 0 h) p q=true) :
    OeisA245212.a (h*p^a*q^d)≠(σ 1 (h*p^a*q^d):ℤ) := by
  intro eqn
  let A:=W h
  let S:=σ 1 h
  let T:=h*σ 0 h
  have eligible : ¬(¬q.Prime ∨ ¬h.Coprime q) := by tauto
  have flip : OeisA245212.a (h*q^d*p^a)=(σ 1 (h*q^d*p^a):ℤ) := by rwa [mul_right_comm]
  have eqtable {x y e : ℕ} (pr : y.Prime) : fastRow A S T x y e=row A S T x y e := fastKnown_eq pr
  change fixed F h A S T p q=true at ck
  rw [fixed,if_neg eligible] at ck
  by_cases b : 2*T*(p-1)*(q-1)<A*p*q
  · rw [if_pos b,Bool.and_eq_true] at ck
    have bound:=horizon_sound hh hp hq op cp cq pq (by omega) dp b eqn
    rcases le_total a d with ad|da
    · rw [min_eq_left ad] at bound
      have z:=OMA.CofactorEulerPair245212.checked ck.1 ap bound
      exact row_sound hh hp hq (by omega) cp cq pq.ne dp ((eqtable hq) ▸ z) eqn
    · rw [min_eq_right da] at bound
      have z:=OMA.CofactorEulerPair245212.checked ck.2 dp bound
      exact row_sound hh hq hp (by omega) cq cp pq.ne.symm (by omega) ((eqtable hp) ▸ z) flip
  · rw [if_neg b] at ck
    have bal : Bal A S (2*T) p q a d := by simpa [A,S,T,Bal] using normalized hh hp hq cp cq pq.ne eqn
    have wp : 0<A := by
      dsimp [A];rw [w_apply]
      exact Finset.sum_pos' (fun _ _=>Nat.zero_le _) ⟨1,Nat.one_mem_divisors.mpr hh.ne',by simp⟩
    have lim:=under_pair hp hq wp bal (le_of_not_gt b)
    have z:=OMA.CofactorEulerPair245212.checked ck dp (Nat.le_trans (Nat.le_succ _) lim)
    exact row_sound hh hq hp (by omega) cq cp pq.ne.symm (by omega) ((eqtable hp) ▸ z) flip

end OMA.RankThreeFourSmallCut245212

end

section

/- Last-prime digit inequalities after separating the common large power
P=p^b. The two leading coefficients are affine in b+1. -/
namespace OMA.RankThreeFourSmallAffine245212
open Nat ArithmeticFunction OMA.Smooth245212
open scoped ArithmeticFunction.sigma

def du (A H p d : ℤ) := (d+1)*(p-1)*(H*(p-1)-A*p)
def dc (A S p d : ℤ) := p*((d+1)*A-S*(p-1))
def dr (A S p d : ℤ) := S*(p-1)-(d+1)*A
def nu (A p d : ℤ) := p*d*A*(p-1)
def nc (A S p d : ℤ) := p*(S*(p-1)-d*A)
def nr (A S p d : ℤ) := d*A-S*(p-1)

def starts (A S p R d : ℕ) :=
  Nat.log p (max (dr A S p d).natAbs (nr A S p d-((R:ℤ)-1)*dr A S p d).natAbs)+1

theorem inequalities {h p q b d R : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime)
    (cp : h.Coprime p) (cq : h.Coprime q) (pq : p<q) (dp : 0<d) (rq : R≤q)
    (big : starts (W h) (σ 1 h) p R d≤b)
    (eqn : OeisA245212.a (h*p^b*q^d)=(σ 1 (h*p^b*q^d):ℤ)) :
    let A:ℤ:=W h
    let S:ℤ:=σ 1 h
    let H:ℤ:=2*(h*σ 0 h:ℕ)
    let D:=du A H p d*(b+1)+dc A S p d
    let N:=nu A p d*(b+1)+nc A S p d
    0≤D ∧ ((R:ℤ)-1)*D≤N := by
  let A:ℤ:=W h
  let S:ℤ:=σ 1 h
  let H:ℤ:=2*(h*σ 0 h:ℕ)
  let P:ℤ:=(p:ℤ)^b
  let v:ℤ:=(p:ℤ)-1
  let D:=du A H p d*(b+1)+dc A S p d
  let N:=nu A p d*(b+1)+nc A S p d
  let D1:=dr A S p d
  let N1:=nr A S p d
  let V:=W (h*p^b)
  let Y:=σ 1 (h*p^b)
  let T:=(h*p^b)*σ 0 (h*p^b)
  let delta:=OMA.LastDigit245212.denom V Y T d
  have pp:=hp.pos
  have pos : 0<h*p^b := by positivity
  have cop:=(cq.mul_left (((coprime_primes hp hq).mpr pq.ne).pow_left b))
  obtain ⟨dpos,dlo,_,_⟩:=OMA.LastDigit245212.balance_digits pos hq cop dp eqn
  change 0<delta at dpos
  change delta*(q-1)<V*d+Y at dlo
  have subtract : delta+(V*(d+1)+Y)=2*T*(d+1) := Nat.sub_add_cancel
    (Nat.sub_pos_iff_lt.mp dpos).le
  have w : (V:ℤ)=A*W (p^b) := by
    simp only [V,A,w_mult.map_mul_of_coprime (cp.pow_right b),Nat.cast_mul]
  have s : (Y:ℤ)=S*σ 1 (p^b) := by
    simp only [Y,S,isMultiplicative_sigma.map_mul_of_coprime (cp.pow_right b),Nat.cast_mul]
  have t : (2:ℤ)*T=H*(b+1)*P := by
    dsimp [T,H,P]
    rw [isMultiplicative_sigma.map_mul_of_coprime (cp.pow_right b),sigma_zero_apply_prime_pow hp]
    push_cast;ring
  have loc:=OMA.ComplementaryLocal245212.moments hp b
  have sub : (delta:ℤ)+((V:ℤ)*(d+1)+Y)=2*T*(d+1) := by exact_mod_cast subtract
  have de : v^2*(delta:ℤ)=D*P+D1 := by
    rw [w,s,t] at sub
    dsimp [D,P,D1,v,du,dc,dr] at *
    linear_combination ((p:ℤ)-1)^2*sub - A*((d:ℤ)+1)*loc.2 - S*((p:ℤ)-1)*loc.1
  have ne : v^2*((V:ℤ)*d+Y)=N*P+N1 := by
    rw [w,s]
    dsimp [N,P,N1,v,nu,nc,nr]
    linear_combination A*(d:ℤ)*loc.2 + S*((p:ℤ)-1)*loc.1
  have qpos:=hq.pos
  have lower : (delta:ℤ)*((q:ℤ)-1)<V*d+Y := by
    zify [Nat.sub_le_sub_left qpos 0] at dlo
    simpa only [Nat.cast_sub (by omega : 1≤q),Nat.cast_one] using dlo
  have vpos : 0<v := sub_pos.mpr (by exact_mod_cast hp.one_lt)
  have gap : ((R:ℤ)-1)*(D*P+D1)<N*P+N1 := by
    have low := mul_lt_mul_of_pos_left lower (pow_pos vpos 2)
    have le := mul_le_mul_of_nonneg_right (by exact_mod_cast rq : (R:ℤ)≤q)
      (show 0≤v^2*(delta:ℤ) from mul_nonneg (sq_nonneg _) (Int.natCast_nonneg _))
    nlinarith only [low,le,congrArg (((R:ℤ)-1)*·) de,ne]
  have lowD : 0<D*P+D1 := by rw [←de]; exact mul_pos (sq_pos_of_pos
    (by dsimp [v]; exact sub_pos.mpr (by exact_mod_cast hp.one_lt))) (by exact_mod_cast dpos)
  have ppow : max D1.natAbs (N1-((R:ℤ)-1)*D1).natAbs<p^b :=
    (Nat.lt_pow_succ_log_self hp.one_lt _).trans_le (Nat.pow_le_pow_right hp.pos big)
  have vd : |D1|<P := by simpa [P] using (show (D1.natAbs:ℤ)<(p:ℤ)^b by
    exact_mod_cast (le_max_left _ _).trans_lt ppow)
  have vn : |N1-((R:ℤ)-1)*D1|<P := by simpa [P] using
    (show (((N1-((R:ℤ)-1)*D1).natAbs):ℤ)<(p:ℤ)^b by exact_mod_cast (le_max_right _ _).trans_lt ppow)
  change 0≤D ∧ ((R:ℤ)-1)*D≤N
  have pp' : 0<P := by dsimp [P];positivity
  constructor
  · by_contra! neg
    have := mul_le_mul_of_nonneg_right (show D≤ -1 by omega) pp'.le
    linarith only [this,lowD,(le_abs_self D1).trans_lt vd]
  · by_contra! neg
    have := mul_le_mul_of_nonneg_right (show N+1≤((R:ℤ)-1)*D by omega) pp'.le
    linarith only [this,gap,(le_abs_self _).trans_lt vn]
end OMA.RankThreeFourSmallAffine245212

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

/- Direct digit replay on the interval of exponents allowed by the
two affine leading coefficients. -/
namespace OMA.RankThreeFourSmallBand245212
open Nat ArithmeticFunction OMA.Smooth245212 OMA.CofactorEulerPair245212
open OMA.RankThreeFourSmallAffine245212
open scoped ArithmeticFunction.sigma
open OMA.CofactorEulerPair245212 (checked)
open OMA.Large245212 (force)
open OMA.Large245212 (moments)
open OMA.PairExtension245212 (fit)

def bit (A S T p R d b : ℕ) : Bool :=
  let V:=A*OMA.Large245212.wt p b
  let Y:=S*OMA.Large245212.sig p b
  let J:=T*OMA.Large245212.tax p b
  let den:=OMA.LastDigit245212.denom V Y J d
  let q:=OMA.Large245212.candidate V Y J d
  decide (den=0 ∨ q<R) || !OMA.PairExtension245212.permitted V Y J q d

theorem bit_sound {h p q b d R : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime)
    (cp : h.Coprime p) (cq : h.Coprime q) (pq : p<q) (dp : 0<d) (rq : R≤q)
    (eqn : OeisA245212.a (h*p^b*q^d)=(σ 1 (h*p^b*q^d):ℤ)) :
    bit (W h) (σ 1 h) (h*σ 0 h) p R d b≠true := by
  have pp:=hp.pos
  have mp : 0<h*p^b := by positivity
  have cop:=(cq.mul_left (((coprime_primes hp hq).mpr pq.ne).pow_left b))
  have z:=OMA.LastDigit245212.balance_digits mp hq cop dp eqn
  have val:=OMA.Large245212.force (sigma_pos 1 _ mp.ne') hq.one_lt z.1 z.2.1 z.2.2.1
  have fit:=OMA.PairExtension245212.fit mp hq cop dp eqn
  have cc:=cp.pow_right b
  obtain ⟨sg,ww⟩:=OMA.Large245212.moments hp b
  have sz:=(show 0<OMA.LastDigit245212.denom (W (h*p^b)) (σ 1 (h*p^b))
    ((h*p^b)*σ 0 (h*p^b)) d from z.1)
  rw [w_mult.map_mul_of_coprime cc,isMultiplicative_sigma.map_mul_of_coprime cc,
    isMultiplicative_sigma.map_mul_of_coprime cc,sigma_zero_apply_prime_pow hp,←sg,←ww] at sz val fit
  have t : (h*p^b)*(σ 0 h*(b+1))=h*σ 0 h*OMA.Large245212.tax p b := by unfold OMA.Large245212.tax;ring
  rw [t] at sz val fit
  simp [bit,sz.ne',val,not_lt.mpr rq,fit]

def slope (A _S H p R d : ℕ) := ((R:ℤ)-1)*du A H p d-nu A p d
def intercept (A S p R d : ℕ) := nc A S p d-((R:ℤ)-1)*dc A S p d
def lower (A S H p d : ℕ) := ((-dc A S p d)/du A H p d).toNat-1
def upper (A S H p R d : ℕ) := (intercept A S p R d/slope A S H p R d).toNat

def band (A S T p R BB d : ℕ) :=
  let J:=starts A S p R d
  let hi:=min BB (upper A S (2*T) p R d)
  (decide (0<du A (2*T) p d ∧ 0<slope A S (2*T) p R d)) &&
    every 1 (min BB (J-1)) (bit A S T p R d) &&
    every (max J (lower A S (2*T) p d)) hi (bit A S T p R d)

theorem band_sound {h p q b d R BB : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime)
    (cp : h.Coprime p) (cq : h.Coprime q) (pq : p<q) (bp : 0<b) (dp : 0<d)
    (rq : R≤q) (maxb : b≤BB) (ck : band (W h) (σ 1 h) (h*σ 0 h) p R BB d=true)
    (eqn : OeisA245212.a (h*p^b*q^d)=(σ 1 (h*p^b*q^d):ℤ)) : False := by
  let A:=W h
  let S:=σ 1 h
  let T:=h*σ 0 h
  let H:=2*T
  let J:=starts A S p R d
  change band A S T p R BB d=true at ck
  simp only [band,Bool.and_eq_true,decide_eq_true_eq] at ck
  apply bit_sound hh hp hq cp cq pq dp rq eqn
  by_cases short : b<J
  · exact OMA.CofactorEulerPair245212.checked ck.1.2 bp (le_min maxb (by omega))
  obtain ⟨lo,hi⟩:=inequalities hh hp hq cp cq pq dp rq (le_of_not_gt short) eqn
  change 0≤du A H p d*((b:ℤ)+1)+dc A S p d at lo
  change ((R:ℤ)-1)*(du A H p d*((b:ℤ)+1)+dc A S p d)≤nu A p d*((b:ℤ)+1)+nc A S p d at hi
  have u0 := ck.1.1.1
  have v0 := ck.1.1.2
  change 0<du A H p d at u0
  change 0<slope A S H p R d at v0
  have ll : -dc A S p d/du A H p d≤(b:ℤ)+1 := by
    apply Int.ediv_le_of_le_mul u0
    nlinarith only [lo]
  have uu : (b:ℤ)+1≤ intercept A S p R d/slope A S H p R d := by
    apply (Int.le_ediv_iff_mul_le v0).mpr
    dsimp [intercept,slope]
    linarith only [hi]
  have lb : lower A S H p d≤b := by unfold lower;omega
  have ub : b≤upper A S H p R d := by unfold upper;omega
  exact OMA.CofactorEulerPair245212.checked ck.2 (max_le (by omega) lb) (le_min maxb ub)

def budget (A S H p d BB : ℕ) :=
  if 2*H<p*(H-A) then min BB (p*S/(p*(H-A)-2*H)/(d+1)-1) else BB

theorem budget_ge {h p q b d BB : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime)
    (cp : h.Coprime p) (cq : h.Coprime q) (pq : p<q) (bp : 0<b) (dp : 0<d) (maxb : b≤BB)
    (eqn : OeisA245212.a (h*p^b*q^d)=(σ 1 (h*p^b*q^d):ℤ)) :
    b≤budget (W h) (σ 1 h) (2*(h*σ 0 h)) p d BB := by
  let A:=W h
  let S:=σ 1 h
  let H:=2*(h*σ 0 h)
  let L:=(b+1)*(d+1)
  obtain ⟨pos,cut⟩:=OMA.RankThreeFourSmallHarmonic245212.count_cap hh hp hq cp cq pq bp dp eqn
  change S<(H-A)*L at pos
  change p*((H-A)*L-S)≤2*H*L at cut
  change b≤budget A S H p d BB
  unfold budget
  split
  next high =>
    have diff := Nat.sub_add_cancel high.le
    have rest := Nat.sub_add_cancel pos.le
    have x : L*(p*(H-A)-2*H)≤p*S := by
      nlinarith only [cut,congrArg (fun x:ℕ=>L*x) diff,congrArg (fun x:ℕ=>p*x) rest]
    have l := (Nat.le_div_iff_mul_le (Nat.sub_pos_of_lt high)).mpr x
    have zb : b+1≤p*S/(p*(H-A)-2*H)/(d+1) := (Nat.le_div_iff_mul_le (by omega)).mpr l
    exact le_min maxb (by omega)
  next _ => exact maxb

end OMA.RankThreeFourSmallBand245212

end

section

/- Dyadic exponent two, with three odd bases. Keeping one actual
Euler factor also gives a lower bound for each exponent near the cap. -/
namespace OMA.RankThreeFourLargeCap245212
open Finset Nat OMA.Smooth245212 OMA.OddFaces245212
open scoped ArithmeticFunction.sigma
open OMA.OddFaces245212 (envelope)

theorem norm {p q r a b c : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (po : 2<p) (pq : p<q) (qr : q<r)
    (eq : OeisA245212.a (4*p^a*q^b*r^c)=(σ 1 (4*p^a*q^b*r^c):ℤ)) :
    17*(X p (some a)*X q (some b)*X r (some c))+
      7*(Y p (some a)*Y q (some b)*Y r (some c))=24 := by
  let P : Fin 4 → ℕ := ![2,p,q,r]
  let E : Fin 4 → ℕ := ![2,a,b,c]
  have pr (i : Fin 4) : (P i).Prime := by fin_cases i <;> simp [P,hp,hq,hr,prime_two]
  have inj : P.Injective := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all [P] <;> omega
  have repr : total P E=4*p^a*q^b*r^c := by simp [total,Fin.prod_univ_four,P,E,mul_assoc]
  have n := normalized_of_eq P pr inj E (repr ▸ eq)
  have x : X 2 (some 2)=17/12 := by decide +kernel
  have y : Y 2 (some 2)=7/12 := by decide +kernel
  simp [normalized,Fin.prod_univ_four,P,E,x,y] at n
  linarith

theorem caps {p q r a b c : ℕ} (hp : 1<p) (hq : 1<q) (hr : 1<r) (ap : 0<a)
    (eq : 17*(X p (some a)*X q (some b)*X r (some c))+
      7*(Y p (some a)*Y q (some b)*Y r (some c))=24) :
    24≤17*(limitX p*limitX q*limitX r) := by
  let P : Fin 3 → ℕ := ![p,q,r]
  let E : Fin 3 → ℕ := ![a,b,c]
  have pr (i : Fin 3) : 1<P i := by fin_cases i <;> simp [P,hp,hq,hr]
  have x : X 2 (some 2)=17/12 := by decide +kernel
  have y : Y 2 (some 2)=7/12 := by decide +kernel
  have val : X 2 (some 2)*(∏ i,X (P i) (some (E i)))+
      Y 2 (some 2)*(∏ i,Y (P i) (some (E i)))=2 := by
    rw [x,y]; simp [Fin.prod_univ_three,P,E]; linarith
  have t := OMA.DyadicEuler245212.cap_needed_at_two 2 P E pr 0 ap val
  simp [Fin.prod_univ_three,P,x] at t
  linarith

theorem one_cap {p q r a b c : ℕ} (hp : 5≤p) (hq : 1<q) (hr : 1<r) (bp : 0<b)
    (eq : 17*(X p (some a)*X q (some b)*X r (some c))+
      7*(Y p (some a)*Y q (some b)*Y r (some c))=24) :
    24≤17*X p (some a)*(limitX q*limitX r) := by
  have pg : 1<p := by omega
  have p' : (5:ℚ)≤p := by exact_mod_cast hp
  have sp : (0:ℚ)<p-1 := by linarith
  have yp := y_one pg (some a)
  have sum_bound : 17*X p (some a)+7*Y p (some a)≤24 := by
    unfold X; apply (le_of_mul_le_mul_right · sp)
    field_simp
    nlinarith only [mul_nonneg (sub_nonneg.mpr (show (24:ℚ)≤7*p by linarith)) (sub_nonneg.mpr yp)]
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
  have W := mul_le_mul_of_nonneg_left env (mul_nonneg (by decide : (0:ℚ)≤17) (x_nonneg pg (some a)))
  change 24≤17*X p (some a)*U
  by_contra! bad
  have h : 17*(X p (some a)*(X q (some b)*X r (some c)))+7*(Y p (some a)*T)=24 := by
    simpa only [T,mul_assoc] using eq
  nlinarith only [W,h,mul_le_mul_of_nonneg_right sum_bound T0,mul_pos (sub_pos.mpr ltT) (sub_pos.mpr bad)]

end OMA.RankThreeFourLargeCap245212

end

section

/- Recover the bounded initial power of three and the cofactor moments. -/
namespace OMA.RankThreeFourSmallOriginal245212
open Nat Finset ArithmeticFunction OMA.Smooth245212 OMA.CofactorEulerPair245212
open OMA.RankThreeFourSmallHarmonic245212 OMA.RankThreeFourSmallDecision245212
open scoped ArithmeticFunction.sigma
open OMA.CofactorEulerPair245212 (checked)
open OMA.FixedExponents245212 (y_pos)
open OMA.Large245212 (moments)

def cert (a : ℕ) :=
  let A:=17*OMA.Large245212.wt 3 a
  let S:=7*OMA.Large245212.sig 3 a
  let T:=12*OMA.Large245212.tax 3 a
  every 5 (primeCut A S (2*T)) (atPrime (4*3^a) A S T)

theorem checked_row {p q a b c : ℕ} (hp : p.Prime) (hq : q.Prime) (lo : 5≤p) (pq : p<q)
    (bp : 0<b) (cp : 0<c) (ok : cert a=true) :
    OeisA245212.a (4*3^a*p^b*q^c)≠(σ 1 (4*3^a*p^b*q^c):ℤ) := by
  intro eqn
  have cop (r : ℕ) (hr : r.Prime) (low : 5≤r) : (4*3^a).Coprime r :=
    (((coprime_primes prime_two hr).mpr (by omega)).pow_left 2).mul_left
      (((coprime_primes (by decide : Nat.Prime 3) hr).mpr (by omega)).pow_left a)
  have c3 : (4:ℕ).Coprime (3^a) := (by decide : Nat.Coprime 4 3).pow_right a
  have base : W 4=17 ∧ σ 1 4=7 ∧ σ 0 4=3 := by decide +kernel
  obtain ⟨y,x⟩:=OMA.Large245212.moments (by decide : Nat.Prime 3) a
  have w : W (4*3^a)=17*OMA.Large245212.wt 3 a := by rw [w_mult.map_mul_of_coprime c3,base.1,x]
  have s : σ 1 (4*3^a)=7*OMA.Large245212.sig 3 a := by rw [isMultiplicative_sigma.map_mul_of_coprime c3,base.2.1,y]
  have t : (4*3^a)*σ 0 (4*3^a)=12*OMA.Large245212.tax 3 a := by
    rw [isMultiplicative_sigma.map_mul_of_coprime c3,base.2.2,sigma_zero_apply_prime_pow (by decide : Nat.Prime 3)]
    unfold OMA.Large245212.tax;ring
  have good:=cop p hp lo
  have other:=cop q hq (by omega)
  have pos : 0<4*3^a := by positivity
  have pm:=first_prime pos hp hq good other pq bp cp eqn
  apply prime_sound pos hp hq (by omega) good other pq bp cp _ eqn
  apply OMA.CofactorEulerPair245212.checked _ lo pm
  simpa only [cert,w,s,t] using ok

theorem exponent {p q a b c : ℕ} (hp : p.Prime) (hq : q.Prime) (lo : 5≤p) (pq : p<q)
    (eqn : OeisA245212.a (4*3^a*p^b*q^c)=(σ 1 (4*3^a*p^b*q^c):ℤ)) : a≤7 := by
  have e:=OMA.RankThreeFourLargeCap245212.norm (by decide : Nat.Prime 3) hp hq
    (by decide) (by omega) pq eqn
  have yz := mul_pos (OMA.FixedExponents245212.y_pos (by decide : Nat.Prime 3) a)
    (mul_pos (OMA.FixedExponents245212.y_pos hp b) (OMA.FixedExponents245212.y_pos hq c))
  have one (r d : ℕ) (pr : r.Prime) : 1≤X r (some d) :=
    le_add_of_nonneg_right (div_nonneg (sub_nonneg.mpr (y_one pr.one_lt _))
      (sub_nonneg.mpr (by exact_mod_cast pr.one_le)))
  have xz := mul_le_mul (one p b hp) (one q c hq) (by decide : (0:ℚ)≤1) (x_nonneg hp.one_lt _)
  by_contra! la
  have y:=y_anti (by decide : 1<3) (by omega : 8≤a)
  have xx : X 3 (some 8) ≤ X 3 (some a) := add_le_add_right
    (div_le_div_of_nonneg_right (sub_le_sub_left y 1) (by norm_num)) 1
  have start : 24≤17*X 3 (some 8) := by decide +kernel
  nlinarith only [e,yz,start,xx,mul_le_mul_of_nonneg_left xz (x_nonneg (by decide : 1<3) (some a))]

end OMA.RankThreeFourSmallOriginal245212

end

section

/- Fast arithmetic certificate with logarithmic finite-pair bounds and
an affine interval for each last exponent in the infinite-prime range. -/
namespace OMA.RankThreeFourSmallFast245212
open Nat ArithmeticFunction OMA.Smooth245212 OMA.CofactorEulerPair245212
open OMA.RankThreeFourSmallBounds245212 OMA.RankThreeFourSmallDecision245212
open OMA.RankThreeFourSmallCut245212 OMA.RankThreeFourSmallBand245212
open OMA.RankThreeFourSmallHarmonic245212 OMA.CofactorGuardFast245212
open scoped ArithmeticFunction.sigma
open OMA.CofactorEulerPair245212 (checked)

def raw (h A S T p q : ℕ) :=
  if 2*T*(p-1)*(q-1)<A*p*q then
    let E:=horizon h A S T p q
    every 1 E (fastRow A S T p q) && every 1 E (fastRow A S T q p)
  else every 1 (2*(A+S*(p-1)*(q-1))/(A*q)) (fastRow A S T q p)

def quick (h A S T p q : ℕ) :=
  if 37<q ∧ q.gcd (37!)≠1 then true else raw h A S T p q || !decide q.Prime

theorem quick_sound {h p q a d : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime) (op : 3≤p)
    (cp : h.Coprime p) (cq : h.Coprime q) (pq : p<q) (ap : 0<a) (dp : 0<d)
    (ck : quick h (W h) (σ 1 h) (h*σ 0 h) p q=true)
    (eqn : OeisA245212.a (h*p^a*q^d)=(σ 1 (h*p^a*q^d):ℤ)) : False := by
  have gc : ¬(37<q ∧ q.gcd (37!)≠1) := fun h=>h.2 (hq.coprime_factorial_of_lt h.1)
  rw [quick,if_neg gc] at ck
  simp only [hq,decide_true,Bool.not_true,Bool.or_false] at ck
  have possible : ¬(¬q.Prime ∨ ¬h.Coprime q) := by tauto
  apply fixed_sound (F:=0) hh hp hq op cp cq pq ap dp _ eqn
  simpa only [raw,fixed,if_neg possible] using ck

def far (_h A S T p R BB d : ℕ) :=
  let B:=budget A S (2*T) p d BB
  if B=0 then true else band A S T p R B d

def run (h A S T p : ℕ) :=
  if ¬p.Prime ∨ ¬h.Coprime p then true else
  if 2*T*(p-1)<A*p then every 1 (2*A/(A*p-2*T*(p-1))) (movingRow A S T p) else
  if A*p<2*T*(p-1) then
    every (p+1) (capQ A T p) (quick h A S T p) &&
    every 1 (lenD A S p) (far h A S T p (max (p+1) (capQ A T p+1)) (lenB A S T p))
  else false

theorem sound {h p q a d : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime) (op : 3≤p)
    (cp : h.Coprime p) (cq : h.Coprime q) (pq : p<q) (ap : 0<a) (dp : 0<d)
    (ck : run h (W h) (σ 1 h) (h*σ 0 h) p=true) :
    OeisA245212.a (h*p^a*q^d)≠(σ 1 (h*p^a*q^d):ℤ) := by
  intro eqn
  let A:=W h
  let S:=σ 1 h
  let T:=h*σ 0 h
  have b : Bal A S (2*T) p q a d := by simpa [A,S,T,Bal] using normalized hh hp hq cp cq pq.ne eqn
  have wp : 0<A := by
    dsimp [A];rw [w_apply]
    exact Finset.sum_pos' (fun _ _=>Nat.zero_le _) ⟨1,Nat.one_mem_divisors.mpr hh.ne',by simp⟩
  have eligible : ¬(¬p.Prime ∨ ¬h.Coprime p) := by tauto
  change run h A S T p=true at ck
  rw [run,if_neg eligible] at ck
  by_cases high : 2*T*(p-1)<A*p
  · rw [if_pos high] at ck
    have sh:=short_first hp hq high (strict hp hq (sigma_pos 1 h hh.ne') b)
    exact moving_row_sound hh hp hq (by omega) cp cq pq dp (OMA.CofactorEulerPair245212.checked ck ap (by omega)) eqn
  rw [if_neg high] at ck
  by_cases under : A*p<2*T*(p-1)
  · rw [if_pos under,Bool.and_eq_true] at ck
    by_cases qr : q≤capQ A T p
    · exact quick_sound hh hp hq op cp cq pq ap dp (OMA.CofactorEulerPair245212.checked ck.1 pq qr) eqn
    have sh := under_first hp hq b under
    have eb : a≤lenB A S T p := by change a≤4*S*(p-1)/_; change ¬q≤1+2*A*p/_ at qr; omega
    have low : A*p*q≤2*T*(p-1)*(q-1) := by
      let G:=2*T*(p-1)-A*p
      have val:=Nat.sub_add_cancel under.le
      have gs : 0<G := Nat.sub_pos_of_lt under
      have qq : 2*A*p/G+1≤q-1 := by change ¬q≤1+2*A*p/G at qr;omega
      have less := (Nat.div_lt_iff_lt_mul gs).mp (by omega : 2*A*p/G<q-1)
      have v:=Nat.sub_add_cancel (by omega : 1≤q)
      nlinarith only [less,congrArg (·*(q-1)) val,congrArg (A*p*·) v,Nat.zero_le (A*p)]
    have ed:=(Nat.le_div_iff_mul_le (Nat.mul_pos wp hq.pos)).mp (under_pair hp hq wp b low)
    have grow : (d+1)*(A*q)≤(2*(A+S*(p-1)))*q := by
      nlinarith only [ed,Nat.mul_le_mul_left (S*(p-1)) (Nat.sub_le q 1),Nat.le_mul_of_pos_right A hq.pos]
    have e0 : (d+1)*A≤2*(A+S*(p-1)) := Nat.le_of_mul_le_mul_right (by simpa only [mul_assoc] using grow) hq.pos
    have small : d≤lenD A S p := (Nat.le_succ _).trans ((Nat.le_div_iff_mul_le wp).mpr e0)
    have atD:=OMA.CofactorEulerPair245212.checked ck.2 dp small
    have bounded:=budget_ge hh hp hq cp cq pq ap dp eb eqn
    change a≤budget A S (2*T) p d (lenB A S T p) at bounded
    rw [far,if_neg (Nat.ne_of_gt (ap.trans_le bounded))] at atD
    exact band_sound hh hp hq cp cq pq ap dp (max_le pq (by omega)) bounded atD eqn
  · simp [under] at ck

def cert (a : ℕ) :=
  let A:=17*OMA.Large245212.wt 3 a
  let S:=7*OMA.Large245212.sig 3 a
  let T:=12*OMA.Large245212.tax 3 a
  every 5 (primeCut A S (2*T)) (run (4*3^a) A S T)

end OMA.RankThreeFourSmallFast245212

end

section

/- Bound a whole interval of second primes by a single first-exponent table. -/
namespace OMA.RankThreeFourSmallNear245212
open Nat ArithmeticFunction OMA.Smooth245212 OMA.CofactorEulerPair245212
open OMA.RankThreeFourSmallBounds245212 OMA.RankThreeFourSmallDegree245212
open OMA.RankThreeFourSmallDecision245212
open scoped ArithmeticFunction.sigma


private theorem incD (A S p E : ℕ) {q u : ℕ} (le : q≤u) :
    degree A S p q E≤degree A S p u E := by
  unfold degree;gcongr

private theorem incR (h A S p E : ℕ) {q u : ℕ} (le : q≤u) :
    OMA.CofactorPairRounding245212.threshold h A S p q E≤OMA.CofactorPairRounding245212.threshold h A S p u E := by
  unfold OMA.CofactorPairRounding245212.threshold OMA.CofactorPairRounding245212.cost OMA.CofactorPairRounding245212.ceiling OMA.CofactorPairRounding245212.bits;gcongr

private theorem incC (A S M : ℕ) {q u : ℕ} (le : q≤u) :
    OMA.RankThreeFourSmallSeparation245212.cost A S q M≤OMA.RankThreeFourSmallSeparation245212.cost A S u M := by
  unfold OMA.RankThreeFourSmallSeparation245212.cost;gcongr

def slab (h A S p l u : ℕ) :=
  let E:=2*A*(p+u)
  let T:=OMA.CofactorPairRounding245212.threshold h A S p u E
  let M:=degree A S p u T
  let Z:=if M+1<l then Nat.log p (OMA.RankThreeFourSmallSeparation245212.cost A S u M) else T
  degree A S p u (max Z (lenD A S p))

theorem slab_sound {h p q a d l u : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime)
    (op : 3≤p) (cp : h.Coprime p) (cq : h.Coprime q) (pq : p<q) (ap : 0<a) (dp : 0<d)
    (ql : l≤q) (qu : q≤u) (good : ¬q∣2*(h*σ 0 h))
    (eqn : OeisA245212.a (h*p^a*q^d)=(σ 1 (h*p^a*q^d):ℤ)) :
    a ≤ slab h (W h) (σ 1 h) p l u := by
  let A:=W h
  let S:=σ 1 h
  let H:=2*(h*σ 0 h)
  let E:=2*A*(p+u)
  let T:=OMA.CofactorPairRounding245212.threshold h A S p u E
  let M:=degree A S p u T
  let Z:=if M+1<l then Nat.log p (OMA.RankThreeFourSmallSeparation245212.cost A S u M) else T
  let L:=max Z (lenD A S p)
  have bal : Bal A S H p q a d := by simpa [A,S,H,Bal] using normalized hh hp hq cp cq pq.ne eqn
  have wp : 0<A := by
    dsimp [A];rw [w_apply]
    exact Finset.sum_pos' (fun _ _=>Nat.zero_le _) ⟨1,Nat.one_mem_divisors.mpr hh.ne',by simp⟩
  suffices sm : min a d≤L by
    exact ((both hh hp hq op cp cq pq ap dp sm eqn).1).trans (incD _ _ _ _ qu)
  by_cases high : H*(p-1)*(q-1)<A*p*q
  · have e:=short_pair hp hq high (strict hp hq (sigma_pos 1 h hh.ne') bal)
    have leE : min a d≤E := le_trans ((Nat.le_succ _).trans e) ((Nat.div_le_self _ _).trans (by dsimp [E]; gcongr))
    have rt:=OMA.CofactorPairRounding245212.shortened hh hp hq op cp cq pq ap dp leE eqn
    have t : min a d≤T := rt.le.trans (incR _ _ _ _ _ qu)
    apply le_trans _ (le_max_left Z _)
    dsimp only [Z]
    split
    next inside =>
      obtain ⟨x,y⟩:=both hh hp hq op cp cq pq ap dp t eqn
      have inc:=incD A S p T qu
      exact (OMA.RankThreeFourSmallSeparation245212.small hh hp hq cp cq pq (x.trans inc) (y.trans inc) (inside.trans_le ql) good eqn).trans
        (Nat.log_mono_right (incC _ _ _ qu))
    next _ =>exact t
  · have ed:=(Nat.le_div_iff_mul_le (Nat.mul_pos wp hq.pos)).mp (under_pair hp hq wp bal (le_of_not_gt high))
    have grow : (d+1)*(A*q)≤(2*(A+S*(p-1)))*q := by
      nlinarith only [ed,Nat.mul_le_mul_left (S*(p-1)) (Nat.sub_le q 1),Nat.le_mul_of_pos_right A hq.pos]
    have e0 : (d+1)*A≤2*(A+S*(p-1)) := Nat.le_of_mul_le_mul_right (by simpa only [mul_assoc] using grow) hq.pos
    exact (min_le_right a d).trans (((Nat.le_succ _).trans ((Nat.le_div_iff_mul_le wp).mpr e0)).trans (le_max_right _ _))


/-- A binary partition of the finite last-prime interval; only the largest
first exponent certified on one of its occupied components is needed. -/
def nearCap (h A S p Q : ℕ) :=
  (List.range (Nat.log 2 Q+1)).foldl (fun n i=>
    let l:=max (p+1) (2^i)
    let u:=min Q (2^(i+1))
    max n (if l≤u then slab h A S p l u else 0)) 0

private theorem all_le (l : List ℕ) (f : ℕ→ℕ) (z : ℕ) {i : ℕ} (mem : i∈l) :
    f i ≤ l.foldl (fun n j=>max n (f j)) z := by
  induction l generalizing z with
  | nil=>simp at mem
  | cons h t ih=>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp mem with rfl|rest
    · have keep (u : List ℕ) (x : ℕ) : x≤u.foldl (fun n j=>max n (f j)) x := by
        induction u generalizing x with
        | nil=>rfl
        | cons y u hyp=> exact (le_max_left _ _).trans (hyp _)
      exact (le_max_right _ _).trans (keep _ _)
    · exact ih _ rest

theorem near_bound {h p q a d Q : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime)
    (op : 3≤p) (cp : h.Coprime p) (cq : h.Coprime q) (pq : p<q) (ap : 0<a) (dp : 0<d)
    (qu : q≤Q) (good : ¬q∣2*(h*σ 0 h))
    (eqn : OeisA245212.a (h*p^a*q^d)=(σ 1 (h*p^a*q^d):ℤ)) :
    a≤nearCap h (W h) (σ 1 h) p Q := by
  let j:=Nat.log 2 q
  let l:=max (p+1) (2^j)
  let u:=min Q (2^(j+1))
  have low : l≤q:=max_le pq (Nat.pow_log_le_self _ hq.ne_zero)
  have high : q≤u:=le_min qu (Nat.lt_pow_succ_log_self (by decide) q).le
  let f (i : ℕ) := if max (p+1) (2^i) ≤ min Q (2^(i+1))
    then slab h (W h) (σ 1 h) p (max (p+1) (2^i)) (min Q (2^(i+1))) else 0
  have sm : a≤f j := by
    change a≤(if l≤u then slab _ _ _ _ l u else 0)
    rw [if_pos (low.trans high)]
    exact slab_sound hh hp hq op cp cq pq ap dp low high good eqn
  have mem : j∈List.range (Nat.log 2 Q+1) := List.mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right qu))
  have last:=sm.trans (all_le _ f 0 mem)
  exact last

end OMA.RankThreeFourSmallNear245212

end

section

/- A positive integral leading denominator bounds the candidate last prime
uniformly without computing the entire large prime power. -/
namespace OMA.RankThreeFourSmallFar245212
open Nat ArithmeticFunction OMA.Smooth245212 OMA.RankThreeFourSmallAffine245212
open OMA.RankThreeFourSmallDegree245212 OMA.CofactorEulerPair245212
open scoped ArithmeticFunction.sigma

def leading (A S H p d b : ℕ) := du A H p d*((b:ℤ)+1)+dc A S p d

def top (A S p d BB : ℕ) :=
  2*((nu A p d).natAbs*(BB+1)+(nc A S p d).natAbs+(nr A S p d).natAbs)+2

def little (A S p d : ℕ) := Nat.log p (2*(dr A S p d).natAbs)+1

theorem limited {h p q b d BB : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime)
    (cp : h.Coprime p) (cq : h.Coprime q) (pq : p<q) (dp : 0<d) (bb : b≤BB)
    (large : little (W h) (σ 1 h) p d ≤ b)
    (nonzero : leading (W h) (σ 1 h) (2*(h*σ 0 h)) p d b≠0)
    (eqn : OeisA245212.a (h*p^b*q^d)=(σ 1 (h*p^b*q^d):ℤ)) :
    q ≤ top (W h) (σ 1 h) p d BB := by
  let A:ℤ:=W h
  let S:ℤ:=σ 1 h
  let H:ℤ:=2*(h*σ 0 h:ℕ)
  let P:ℤ:=(p:ℤ)^b
  let v:ℤ:=(p:ℤ)-1
  let D:=du A H p d*(b+1)+dc A S p d
  let N:=nu A p d*(b+1)+nc A S p d
  let D1:=dr A S p d
  let N1:=nr A S p d
  let V:=W (h*p^b)
  let Y:=σ 1 (h*p^b)
  let T:=(h*p^b)*σ 0 (h*p^b)
  let delta:=OMA.LastDigit245212.denom V Y T d
  have pp:=hp.pos
  have pos : 0<h*p^b := by positivity
  have cop:=(cq.mul_left (((coprime_primes hp hq).mpr pq.ne).pow_left b))
  obtain ⟨dpos,dlo,_,_⟩:=OMA.LastDigit245212.balance_digits pos hq cop dp eqn
  change 0<delta at dpos
  change delta*(q-1)<V*d+Y at dlo
  have subtract : delta+(V*(d+1)+Y)=2*T*(d+1) := Nat.sub_add_cancel
    (Nat.sub_pos_iff_lt.mp dpos).le
  have w : (V:ℤ)=A*W (p^b) := by
    simp only [V,A,w_mult.map_mul_of_coprime (cp.pow_right b),Nat.cast_mul]
  have s : (Y:ℤ)=S*σ 1 (p^b) := by
    simp only [Y,S,isMultiplicative_sigma.map_mul_of_coprime (cp.pow_right b),Nat.cast_mul]
  have t : (2:ℤ)*T=H*(b+1)*P := by
    dsimp [T,H,P]
    rw [isMultiplicative_sigma.map_mul_of_coprime (cp.pow_right b),sigma_zero_apply_prime_pow hp]
    push_cast;ring
  have loc:=OMA.ComplementaryLocal245212.moments hp b
  have sub : (delta:ℤ)+((V:ℤ)*(d+1)+Y)=2*T*(d+1) := by exact_mod_cast subtract
  have de : v^2*(delta:ℤ)=D*P+D1 := by
    rw [w,s,t] at sub
    dsimp [D,P,D1,v,du,dc,dr] at *
    linear_combination ((p:ℤ)-1)^2*sub - A*((d:ℤ)+1)*loc.2 - S*((p:ℤ)-1)*loc.1
  have ne : v^2*((V:ℤ)*d+Y)=N*P+N1 := by
    rw [w,s]
    dsimp [N,P,N1,v,nu,nc,nr]
    linear_combination A*(d:ℤ)*loc.2 + S*((p:ℤ)-1)*loc.1
  have qpos:=hq.pos
  have lower : (delta:ℤ)*((q:ℤ)-1)<V*d+Y := by
    zify [Nat.sub_le_sub_left qpos 0] at dlo
    simpa only [Nat.cast_sub (by omega : 1≤q),Nat.cast_one] using dlo
  have vpos : 0<v := sub_pos.mpr (by exact_mod_cast hp.one_lt)
  have mag : 2*D1.natAbs < p^b :=
    (Nat.lt_pow_succ_log_self hp.one_lt _).trans_le (Nat.pow_le_pow_right hp.pos large)
  have magZ : 2*|D1| <P := by simpa [P] using (show 2*(D1.natAbs:ℤ)<(p:ℤ)^b by exact_mod_cast mag)
  have Ppos : 1≤P := by dsimp [P]; exact_mod_cast Nat.one_le_pow b p hp.pos
  have positive : 0<D*P+D1 := by rw [←de]; exact mul_pos (sq_pos_of_pos vpos) (by exact_mod_cast dpos)
  have dd : 1≤D := by
    change D≠0 at nonzero
    by_contra! bad
    have mul:=mul_le_mul_of_nonneg_right (show D≤ -1 by omega) (by omega : 0≤P)
    linarith only [positive, le_abs_self D1, magZ, mul, abs_nonneg D1]
  have lowD : P≤2*(D*P+D1) := by
    have mul:=mul_le_mul_of_nonneg_right dd (by omega : 0≤P)
    linarith only [mul,neg_abs_le D1,magZ]
  have capq := mul_lt_mul_of_pos_left lower (sq_pos_of_pos vpos)
  have lm : ((q:ℤ)-1)*P < 2*(N*P+N1) := by
    have mult := mul_le_mul_of_nonneg_left lowD (show 0≤(q:ℤ)-1 by omega)
    nlinarith only [capq,mult,ne,congrArg (((q:ℤ)-1)*·) de]
  let Z:=top (W h) (σ 1 h) p d BB
  have nn : N ≤ (nu A p d).natAbs*(BB+1:ℤ)+(nc A S p d).natAbs := by
    have cmp := mul_le_mul (le_abs_self (nu A p d)) (show (b:ℤ)+1≤(BB:ℤ)+1 by omega)
      (by positivity) (abs_nonneg _)
    dsimp [N];simpa using add_le_add cmp (le_abs_self (nc A S p d))
  have nn1 : N1≤(N1.natAbs:ℤ)*P := by
    simpa using (le_abs_self N1).trans (le_mul_of_one_le_right (abs_nonneg _) Ppos)
  have zx : (Z:ℤ)=2*((nu A p d).natAbs*((BB:ℤ)+1)+(nc A S p d).natAbs+N1.natAbs)+2 := by
    simp [Z,top,A,S,N1]
  have largeq : ((q:ℤ)-1)*P < ((Z:ℤ)-1)*P := by
    nlinarith only [lm,mul_le_mul_of_nonneg_right nn (show 0≤P by omega),nn1,congrArg (·*P) zx,Ppos]
  have order := lt_of_mul_lt_mul_right largeq (by omega : 0≤P)
  change q≤Z
  omega


open OMA.RankThreeFourSmallBand245212

def exceptional (A S H p d : ℕ) :=
  ((-dc A S p d)/du A H p d).toNat-1

def clipped (A S T p R BB d : ℕ) :=
  let E:=max (little A S p d) (degree A S p (top A S p d BB) d)
  let ex:=exceptional A S (2*T) p d
  band A S T p R (min BB E) d &&
    (if E<ex ∧ ex≤BB ∧ leading A S (2*T) p d ex=0 then bit A S T p R d ex else true)

theorem clipped_sound {h p q b d R BB : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime)
    (op : 3≤p) (cp : h.Coprime p) (cq : h.Coprime q) (pq : p<q) (bp : 0<b) (dp : 0<d)
    (rq : R≤q) (bb : b≤BB)
    (ck : clipped (W h) (σ 1 h) (h*σ 0 h) p R BB d=true)
    (eqn : OeisA245212.a (h*p^b*q^d)=(σ 1 (h*p^b*q^d):ℤ)) : False := by
  let A:=W h
  let S:=σ 1 h
  let T:=h*σ 0 h
  let H:=2*T
  let E:=max (little A S p d) (degree A S p (top A S p d BB) d)
  let ex:=exceptional A S H p d
  change (band A S T p R (min BB E) d && (if E<ex ∧ ex≤BB ∧ leading A S H p d ex=0 then _ else true))=true at ck
  rw [Bool.and_eq_true] at ck
  obtain ⟨bandOK,excOK⟩:=ck
  by_cases small : b≤E
  · exact band_sound hh hp hq cp cq pq bp dp rq (le_min bb small) bandOK eqn
  have init : little A S p d≤b := (le_max_left ..).trans (le_of_not_ge small)
  by_cases vanish : leading A S H p d b=0
  · have ds : 0<du A H p d := by
      simp only [band,Bool.and_eq_true,decide_eq_true_eq] at bandOK;exact bandOK.1.1.1
    have id : (-dc A S p d)/du A H p d=(b:ℤ)+1 := by
      have eq : -dc A S p d=((b:ℤ)+1)*du A H p d := by
        unfold leading at vanish; linarith only [vanish,mul_comm (du A H p d) ((b:ℤ)+1)]
      rw [eq,Int.mul_ediv_cancel _ ds.ne']
    have exb : ex=b := by change ((-dc A S p d)/du A H p d).toNat-1=b;rw [id];omega
    rw [exb,if_pos ⟨lt_of_not_ge small,bb,vanish⟩] at excOK
    change bit A S T p R d ex = true at excOK
    rw [exb] at excOK
    exact bit_sound hh hp hq cp cq pq dp rq eqn excOK
  · have largeq:=limited hh hp hq cp cq pq dp bb init vanish eqn
    have flipped : OeisA245212.a (h*q^d*p^b)=(σ 1 (h*q^d*p^b):ℤ) := by rwa [mul_right_comm]
    have t:=one hh hq hp cq cp pq.ne.symm (by omega) bp hp.one_lt le_rfl largeq (show d≤d from le_rfl) flipped
    exact small (t.trans (le_max_right _ _))

end OMA.RankThreeFourSmallFar245212

end

section

/- Dyadic last-prime ranges and the first-three-term divisor-count bound
keep the unrestricted cofactor test inexpensive near an Euler pole. -/
namespace OMA.RankThreeFourSmallCompact245212
open Nat ArithmeticFunction OMA.Smooth245212 OMA.CofactorEulerPair245212
open OMA.RankThreeFourSmallBounds245212 OMA.RankThreeFourSmallDecision245212
open OMA.RankThreeFourSmallBand245212 OMA.RankThreeFourSmallHarmonic245212
open OMA.RankThreeFourSmallNear245212 OMA.RankThreeFourSmallFar245212
open OMA.RankThreeFourSmallFast245212 (quick quick_sound)
open scoped ArithmeticFunction.sigma
open OMA.CofactorEulerPair245212 (checked)

def near (h A S T p Q : ℕ) :=
  if Q≤p+256 then every (p+1) Q (quick h A S T p) else
  ((2*T).primeFactorsList.all fun r=>decide (r≤p)) && every 1 (nearCap h A S p Q) (movingRow A S T p)

theorem near_sound {h p q a d Q : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime)
    (op : 3≤p) (cp : h.Coprime p) (cq : h.Coprime q) (pq : p<q) (ap : 0<a) (dp : 0<d)
    (qr : q≤Q) (ck : near h (W h) (σ 1 h) (h*σ 0 h) p Q=true)
    (eqn : OeisA245212.a (h*p^a*q^d)=(σ 1 (h*p^a*q^d):ℤ)) : False := by
  unfold near at ck
  split at ck
  · exact quick_sound hh hp hq op cp cq pq ap dp (OMA.CofactorEulerPair245212.checked ck pq qr) eqn
  · simp only [Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at ck
    have pos:=sigma_pos 0 h hh.ne'
    have good : ¬q∣2*(h*σ 0 h) := fun dv=>pq.not_ge (ck.1 q (Nat.mem_primeFactors_iff_mem_primeFactorsList.mp (hq.mem_primeFactors dv (by positivity))))
    have small:=near_bound hh hp hq op cp cq pq ap dp qr good eqn
    exact moving_row_sound hh hp hq (by omega) cp cq pq dp (OMA.CofactorEulerPair245212.checked ck.2 ap small) eqn

def capD (A S H p : ℕ) := budget A S H p 1 (lenD A S p)

theorem capD_sound {h p q b d : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime)
    (cp : h.Coprime p) (cq : h.Coprime q) (pq : p<q) (bp : 0<b) (dp : 0<d)
    (eqn : OeisA245212.a (h*p^b*q^d)=(σ 1 (h*p^b*q^d):ℤ))
    (prior : d≤lenD (W h) (σ 1 h) p) : d≤capD (W h) (σ 1 h) (2*(h*σ 0 h)) p := by
  let A:=W h
  let S:=σ 1 h
  let H:=2*(h*σ 0 h)
  let L:=(b+1)*(d+1)
  obtain ⟨pos,cut⟩:=count_cap hh hp hq cp cq pq bp dp eqn
  change S<(H-A)*L at pos
  change p*((H-A)*L-S)≤2*H*L at cut
  unfold capD budget
  split
  next high =>
    change 2*H<p*(H-A) at high
    have diff:=Nat.sub_add_cancel high.le
    have rest:=Nat.sub_add_cancel pos.le
    have x : L*(p*(H-A)-2*H)≤p*S := by
      nlinarith only [cut,congrArg (fun x:ℕ=>L*x) diff,congrArg (fun x:ℕ=>p*x) rest]
    have l := (Nat.le_div_iff_mul_le (Nat.sub_pos_of_lt high)).mpr x
    have two : (d+1)*2≤L := by dsimp [L]; nlinarith only [Nat.mul_le_mul_right (d+1) (show 2≤b+1 by omega)]
    have both:=(Nat.le_div_iff_mul_le (by decide : 0<2)).mpr (two.trans l)
    apply le_min prior
    change d≤p*S/(p*(H-A)-2*H)/2-1
    omega
  next _ => exact prior

def smallFar (A S T p R BB d : ℕ) :=
  let B:=budget A S (2*T) p d BB
  if B=0 then true else if B≤64 then band A S T p R B d else clipped A S T p R B d
def run (h A S T p : ℕ) :=
  if ¬p.Prime ∨ ¬h.Coprime p then true else
  if 2*T*(p-1)<A*p then every 1 (2*A/(A*p-2*T*(p-1))) (movingRow A S T p) else
  if A*p<2*T*(p-1) then
    near h A S T p (capQ A T p) &&
    every 1 (capD A S (2*T) p) (smallFar A S T p (max (p+1) (capQ A T p+1)) (lenB A S T p))
  else false

theorem sound {h p q a d : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime) (op : 3≤p)
    (cp : h.Coprime p) (cq : h.Coprime q) (pq : p<q) (ap : 0<a) (dp : 0<d)
    (ck : run h (W h) (σ 1 h) (h*σ 0 h) p=true) :
    OeisA245212.a (h*p^a*q^d)≠(σ 1 (h*p^a*q^d):ℤ) := by
  intro eqn
  let A:=W h
  let S:=σ 1 h
  let T:=h*σ 0 h
  have b : Bal A S (2*T) p q a d := by simpa [A,S,T,Bal] using normalized hh hp hq cp cq pq.ne eqn
  have wp : 0<A := by
    dsimp [A];rw [w_apply]
    exact Finset.sum_pos' (fun _ _=>Nat.zero_le _) ⟨1,Nat.one_mem_divisors.mpr hh.ne',by simp⟩
  have eligible : ¬(¬p.Prime ∨ ¬h.Coprime p) := by tauto
  change run h A S T p=true at ck
  rw [run,if_neg eligible] at ck
  by_cases high : 2*T*(p-1)<A*p
  · rw [if_pos high] at ck
    have sh:=short_first hp hq high (strict hp hq (sigma_pos 1 h hh.ne') b)
    exact moving_row_sound hh hp hq (by omega) cp cq pq dp (OMA.CofactorEulerPair245212.checked ck ap (by omega)) eqn
  rw [if_neg high] at ck
  by_cases under : A*p<2*T*(p-1)
  · rw [if_pos under,Bool.and_eq_true] at ck
    by_cases qr : q≤capQ A T p
    · exact near_sound hh hp hq op cp cq pq ap dp qr ck.1 eqn
    have sh := under_first hp hq b under
    have eb : a≤lenB A S T p := by change a≤4*S*(p-1)/_; change ¬q≤1+2*A*p/_ at qr; omega
    have low : A*p*q≤2*T*(p-1)*(q-1) := by
      let G:=2*T*(p-1)-A*p
      have val:=Nat.sub_add_cancel under.le
      have gs : 0<G := Nat.sub_pos_of_lt under
      have qq : 2*A*p/G+1≤q-1 := by change ¬q≤1+2*A*p/G at qr;omega
      have less := (Nat.div_lt_iff_lt_mul gs).mp (by omega : 2*A*p/G<q-1)
      have v:=Nat.sub_add_cancel (by omega : 1≤q)
      nlinarith only [less,congrArg (·*(q-1)) val,congrArg (A*p*·) v,Nat.zero_le (A*p)]
    have ed:=(Nat.le_div_iff_mul_le (Nat.mul_pos wp hq.pos)).mp (under_pair hp hq wp b low)
    have grow : (d+1)*(A*q)≤(2*(A+S*(p-1)))*q := by
      nlinarith only [ed,Nat.mul_le_mul_left (S*(p-1)) (Nat.sub_le q 1),Nat.le_mul_of_pos_right A hq.pos]
    have e0 : (d+1)*A≤2*(A+S*(p-1)) := Nat.le_of_mul_le_mul_right (by simpa only [mul_assoc] using grow) hq.pos
    have small : d≤lenD A S p := (Nat.le_succ _).trans ((Nat.le_div_iff_mul_le wp).mpr e0)
    have atD:=OMA.CofactorEulerPair245212.checked ck.2 dp (capD_sound hh hp hq cp cq pq ap dp eqn small)
    have bounded:=budget_ge hh hp hq cp cq pq ap dp eb eqn
    change a≤budget A S (2*T) p d (lenB A S T p) at bounded
    rw [smallFar,if_neg (Nat.ne_of_gt (ap.trans_le bounded))] at atD
    split at atD
    · exact band_sound hh hp hq cp cq pq ap dp (max_le pq (by omega)) bounded atD eqn
    · exact clipped_sound hh hp hq op cp cq pq ap dp (max_le pq (by omega)) bounded atD eqn
  · simp [under] at ck

def cert (a : ℕ) :=
  let A:=17*OMA.Large245212.wt 3 a
  let S:=7*OMA.Large245212.sig 3 a
  let T:=12*OMA.Large245212.tax 3 a
  every 5 (primeCut A S (2*T)) (run (4*3^a) A S T)

end OMA.RankThreeFourSmallCompact245212

end

section

/- In the finite-support part of the 16-times-three-primes problem every
base is at most 1706. Rounding all three odd powers at once forces one
short exponent. With that prime power fixed, the other two exponents
are unrestricted in the certified two-prime test. -/
namespace OMA.RankThreeSixteenFixed245212
open Nat Finset ArithmeticFunction OMA.Smooth245212 OMA.Height245212
open OMA.CofactorEulerPair245212 OMA.RankThreeFourSmallFast245212
open scoped ArithmeticFunction.sigma
open OMA.RankThreeFourLargeSmall245212 (control)
open OMA.RankThreeFourLargeSmall245212 (erase0)
open OMA.Large245212 (moments)
open OMA.CofactorEulerPair245212 (checked)

abbrev bases (p q r : ℕ) : Fin 4 → ℕ := ![2,p,q,r]
abbrev exps (a b c : ℕ) : Fin 4 → ℕ := ![4,a,b,c]
def budget := 16*coefficientBound 1706 (OMA.HeightLog245212.ceiling 4 1706)
def first (p : ℕ) := max 82 (Nat.log p budget)

theorem one_short {p q r a b c : ℕ} (pp : p.Prime) (qp : q.Prime) (rp : r.Prime)
    (op : 2<p) (pq : p<q) (qr : q<r) (rb : r≤1706) (ap : 0<a) (bp : 0<b) (cp : 0<c)
    (sol : OeisA245212.a (16*p^a*q^b*r^c)=(σ 1 (16*p^a*q^b*r^c):ℤ)) :
    a≤first p ∨ b≤first q ∨ c≤first r := by
  let P:=bases p q r
  let E:=exps a b c
  have pr (i : Fin 4) : (P i).Prime := by fin_cases i <;> simp [P,bases,pp,qp,rp,prime_two]
  have inj : P.Injective := by intro i j hit;fin_cases i <;> fin_cases j <;> simp_all [P,bases] <;> omega
  have pos (i : Fin 4) : 0<E i := by fin_cases i <;> simp [E,exps,ap,bp,cp]
  have bound (i : Fin 4) : P i≤1706 := by fin_cases i <;> simp [P,bases] <;> omega
  have powB (B : ℕ) (large : 16≤B) : 16≤B^(2*B) := large.trans (Nat.le_pow (by omega))
  have dt (i : Fin 4) : P i=2 → P i^E i≤1706^(2*1706) := by
    intro eq2
    fin_cases i
    · exact powB 1706 (by decide)
    · change p=2 at eq2;omega
    · change q=2 at eq2;omega
    · change r=2 at eq2;omega
  have id : total P E=16*p^a*q^b*r^c := by simp [total,Fin.prod_univ_four,P,E,bases,exps,mul_assoc]
  have high:=OMA.GuardedHeight245212.max_power P E pr dt pos inj bound (id ▸ sol)
  have cap:=OMA.HeightLog245212.four (lt_of_lt_of_le (pos 0) (le_sup (f:=E) (mem_univ 0))) high
  have eb (i : Fin 4) := (le_sup (f:=E) (mem_univ i)).trans cap
  have norm:=normalized_of_eq P pr inj E (id ▸ sol)
  by_contra! far
  obtain ⟨aa,bb,cc⟩:=far
  let s : Finset (Fin 4):={1,2,3}
  have big {p a : ℕ} (hp : p.Prime) (lt : first p<a) : budget<p^a :=
    (Nat.lt_pow_succ_log_self hp.one_lt _).trans_le
      (Nat.pow_le_pow_right hp.pos ((le_max_right ..).trans_lt lt))
  have out : outside P E s=16 := by simp [outside,Fin.prod_univ_four,P,E,bases,exps,s]
  have large (i) (hi : i∈s) : coefficientBound 1706 (OMA.HeightLog245212.ceiling 4 1706)*outside P E s<P i^E i := by
    rw [out,mul_comm]
    fin_cases i
    · simp [s] at hi
    · exact big pp aa
    · exact big qp bb
    · exact big rp cc
  have pair {u v w j l : ℕ} (ug : 1<u) (vg : 1<v) (wg : 1<w) (ub : u≤1706)
      (jl : first v<j) (ll : first w<l) : ((u:ℚ)-1)*(yr 2 4*yr v j*yr w l)<1 := by
    have j1 : 82<j := (le_max_left ..).trans_lt jl
    have l1 : 82<l := (le_max_left ..).trans_lt ll
    have su : 4*(u-1)<(j+1)*(l+1) := by
      have := Nat.mul_le_mul (show 84≤j+1 by omega) (show 84≤l+1 by omega);omega
    have non := mul_nonneg (sub_nonneg.mpr (show (1:ℚ)≤u by exact_mod_cast ug.le))
      (mul_nonneg (y_range vg (by omega : 0<j)).1 (y_range wg (by omega : 0<l)).1)
    calc
      _ = yr 2 4*(((u:ℚ)-1)*(yr v j*yr w l)) := by ring
      _ ≤ _ := mul_le_of_le_one_left non (by decide +kernel : yr 2 4≤1)
      _ < _ := OMA.RankThreeFourLargeSmall245212.control ug vg wg (by omega) (by omega) su
  have strict (i) (hi : i∈s) : ((P i:ℚ)-1)*(∏j∈univ.erase i, yr (P j) (E j))<1 := by
    rw [OMA.RankThreeFourLargeSmall245212.erase0]
    fin_cases i <;> simp [Fin.prod_univ_four,P,E,bases,exps,s] at hi ⊢
    · exact pair pp.one_lt qp.one_lt rp.one_lt (by omega) bb cc
    · exact pair qp.one_lt pp.one_lt rp.one_lt (by omega) aa cc
    · exact pair rp.one_lt pp.one_lt qp.one_lt rb aa bb
  have same:=gap_eq _ _ pr pos s norm (enough _ _ pr bound eb s large)
  have lt:=strict_prod _ _ (fun i=>(pr i).one_lt) pos s (by decide) strict
  linarith

def atExp (moving : Bool) (s p q e : ℕ) :=
  let h:=16*s^e
  let A:=129*OMA.Large245212.wt s e
  let S:=31*OMA.Large245212.sig s e
  let T:=80*OMA.Large245212.tax s e
  if moving then OMA.RankThreeFourSmallCompact245212.run h A S T p else quick h A S T p q

theorem atExp_sound {s p q a b c : ℕ} (sp : s.Prime) (pp : p.Prime) (qp : q.Prime)
    (os : 2<s) (op : 2<p) (ps : s≠p) (qs : s≠q) (pq : p<q)
    (bp : 0<b) (cp : 0<c) (moving : Bool) (ck : atExp moving s p q a=true) :
    OeisA245212.a (16*s^a*p^b*q^c)≠(σ 1 (16*s^a*p^b*q^c):ℤ) := by
  obtain ⟨sg,wt⟩:=OMA.Large245212.moments sp a
  have cs : (16:ℕ).Coprime (s^a) := (((coprime_primes prime_two sp).mpr (by omega)).pow_left 4).pow_right a
  have cop (t) (tp : t.Prime) (ot : 2<t) (st : s≠t) : (16*s^a).Coprime t :=
    (((coprime_primes prime_two tp).mpr (by omega)).pow_left 4).mul_left (((coprime_primes sp tp).mpr st).pow_left a)
  have vals : W 16=129 ∧ σ 1 16=31 ∧ σ 0 16=5 := by decide +kernel
  have w : W (16*s^a)=129*OMA.Large245212.wt s a := by rw [w_mult.map_mul_of_coprime cs,vals.1,wt]
  have y : σ 1 (16*s^a)=31*OMA.Large245212.sig s a := by rw [isMultiplicative_sigma.map_mul_of_coprime cs,vals.2.1,sg]
  have t : 16*s^a*σ 0 (16*s^a)=80*OMA.Large245212.tax s a := by
    rw [isMultiplicative_sigma.map_mul_of_coprime cs,vals.2.2,sigma_zero_apply_prime_pow sp,OMA.Large245212.tax];ring
  have hp:=sp.pos
  have cp1:=cop p pp op ps
  have cp2:=cop q qp (by omega) qs
  cases moving
  · apply quick_sound (by positivity) pp qp (by omega) cp1 cp2 pq bp cp
    simpa [atExp,w,y,t] using ck
  · apply OMA.RankThreeFourSmallCompact245212.sound (by positivity) pp qp (by omega) cp1 cp2 pq bp cp
    simpa [atExp,w,y,t] using ck

def test (s p q : ℕ) := every 1 (first s) (atExp false s p q)
def tests (p q r : ℕ) := test p q r && test q p r && test r p q

theorem fixed {p q r a b c : ℕ} (pp : p.Prime) (qp : q.Prime) (rp : r.Prime)
    (op : 2<p) (pq : p<q) (qr : q<r) (rb : r≤1706) (ap : 0<a) (bp : 0<b) (cp : 0<c)
    (ck : tests p q r=true) : OeisA245212.a (16*p^a*q^b*r^c)≠(σ 1 (16*p^a*q^b*r^c):ℤ) := by
  intro eqn
  obtain ⟨⟨x,y⟩,z⟩ := (show (test p q r=true ∧ test q p r=true) ∧ test r p q=true by
    simpa only [tests,Bool.and_eq_true] using ck)
  rcases one_short pp qp rp op pq qr rb ap bp cp eqn with sh|sh|sh
  · exact atExp_sound pp qp rp op (by omega) pq.ne (pq.trans qr).ne qr bp cp false
      (OMA.CofactorEulerPair245212.checked x ap sh) eqn
  · exact atExp_sound qp pp rp (by omega) op pq.ne.symm qr.ne (pq.trans qr) ap cp false
      (OMA.CofactorEulerPair245212.checked y bp sh) (by rwa [mul_right_comm 16 (q^b) (p^a)])
  · exact atExp_sound rp pp qp (by omega) op (pq.trans qr).ne.symm qr.ne.symm pq ap bp false
      (OMA.CofactorEulerPair245212.checked z cp sh) (by rwa [show 16*r^c*p^a*q^b=16*p^a*q^b*r^c by ring])

end OMA.RankThreeSixteenFixed245212

end

section

/- Exact base support at dyadic order four and smallest odd prime at least seven. -/
namespace OMA.RankThreeSixteenSupport245212
open Nat Finset OMA.Smooth245212 OMA.OddFaces245212
open scoped ArithmeticFunction.sigma

theorem necessary {p q r a b c : ℕ} (pp : p.Prime) (qp : q.Prime) (rp : r.Prime)
    (op : 2<p) (pq : p<q) (qr : q<r) (ap : 0<a)
    (eq : OeisA245212.a (16*p^a*q^b*r^c)=(σ 1 (16*p^a*q^b*r^c):ℤ)) :
    160≤129*(limitX p*limitX q*limitX r) ∧ 129*(X p (some a)*X q (some b))<160 := by
  let P := OMA.RankThreeSixteenFixed245212.bases p q r
  let E := OMA.RankThreeSixteenFixed245212.exps a b c
  have pr (i : Fin 4) : (P i).Prime := by fin_cases i <;> simp [P,OMA.RankThreeSixteenFixed245212.bases,pp,qp,rp,prime_two]
  have inj : P.Injective := by intro i j hit;fin_cases i <;> fin_cases j <;> simp_all [P,OMA.RankThreeSixteenFixed245212.bases] <;> omega
  have id : total P E=16*p^a*q^b*r^c := by simp [total,Fin.prod_univ_four,P,E,OMA.RankThreeSixteenFixed245212.bases,OMA.RankThreeSixteenFixed245212.exps,mul_assoc]
  have bal:=normalized_of_eq P pr inj E (id ▸ eq)
  let A : Fin 3 → ℕ := ![p,q,r]
  let F : Fin 3 → ℕ := ![a,b,c]
  have prime (i : Fin 3) : 1<A i := by fin_cases i <;> first | exact pp.one_lt | exact qp.one_lt | exact rp.one_lt
  have normalized : X 2 (some 4)*(∏i,X (A i) (some (F i)))+Y 2 (some 4)*(∏i,Y (A i) (some (F i)))=2 := by
    simpa [OMA.Smooth245212.normalized,Fin.prod_univ_four,Fin.prod_univ_three,P,E,A,F,OMA.RankThreeSixteenFixed245212.bases,OMA.RankThreeSixteenFixed245212.exps,mul_assoc] using bal
  have cap:=OMA.DyadicEuler245212.cap_needed_at_two 4 A F prime 0 ap normalized
  have x2 : X 2 (some 4)=129/80 := by decide +kernel
  have y2 : Y 2 (some 4)=31/80 := by decide +kernel
  simp [x2,y2,Fin.prod_univ_three,A,F] at cap normalized
  constructor
  · linarith only [cap]
  · have yp (s e : ℕ) (hs : s.Prime) : 0<Y s (some e) := by
      rw [y_avg hs.one_lt];exact div_pos (sum_pos' (fun _ _=>by positivity) ⟨0,mem_range.mpr (by omega),by simp⟩) (by positivity)
    have y:=mul_pos (mul_pos (yp p a pp) (yp q b qp)) (yp r c rp)
    have x : 1≤X r (some c) := le_add_of_nonneg_right
      (div_nonneg (sub_nonneg.mpr (y_one rp.one_lt _)) (sub_nonneg.mpr (by exact_mod_cast rp.one_le)))
    have growth:=mul_le_mul_of_nonneg_left x (mul_nonneg (x_nonneg pp.one_lt (some a)) (x_nonneg qp.one_lt (some b)))
    nlinarith only [normalized,y,growth]

theorem integer_cap {p q r : ℕ} (pp : p.Prime) (qp : q.Prime) (rp : r.Prime)
    (cap : 160≤129*(limitX p*limitX q*limitX r)) :
    160*(p-1)*(q-1)*(r-1)≤129*p*q*r := by
  have factor {s : ℕ} (hs : s.Prime) : limitX s=(s:ℚ)/((s-1:ℕ):ℚ) := by
    rw [limitX,X]; simp only [Y]
    have h : (1:ℚ)<s := by exact_mod_cast hs.one_lt
    push_cast [Nat.cast_sub hs.one_le];field_simp [sub_ne_zero.mpr h.ne'];ring
  rw [factor pp,factor qp,factor rp] at cap
  have positive {s : ℕ} (hs : s.Prime) : (0:ℚ)<(s-1:ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hs.one_lt
  field_simp [positive pp,positive qp,positive rp] at cap
  exact_mod_cast (by linarith only [cap] : (160:ℚ)*((p-1:ℕ):ℚ)*(q-1:ℕ)*(r-1:ℕ) ≤ 129*p*q*r)


theorem order {p q r : ℕ} (pp : p.Prime) (qp : q.Prime) (rp : r.Prime)
    (p7 : 7≤p) (pq : p<q) (qr : q<r) (cap : 160≤129*(limitX p*limitX q*limitX r)) :
    p≤11 ∧ q≤29 ∧ ((p=7 ∧ q≤13) ∨ r≤1706) := by
  have veto (u v w : ℕ) (hu : 1<u) (hv : 1<v) (hw : 1<w) (up : u≤p)
      (vq : v≤q) (wr : w≤r) (bad : 129*(limitX u*limitX v*limitX w)<160) : False := by
    have cmp:=mul_le_mul (mul_le_mul (cap_anti hu up) (cap_anti hv vq) (x_nonneg qp.one_lt none) (x_nonneg hu none))
      (cap_anti hw wr) (x_nonneg rp.one_lt none) (mul_nonneg (x_nonneg hu none) (x_nonneg hv none))
    linarith
  have p11 : p≤11 := by
    by_contra! h
    have x : 13≤p := by by_contra! g;interval_cases p; norm_num at *
    have y : 17≤q := by by_contra! g;interval_cases q <;> norm_num at * <;> omega
    exact veto 13 17 17 (by decide) (by decide) (by decide) x y (by omega) (by decide +kernel)
  have q29 : q≤29 := by
    by_contra! h
    have y : 31≤q := by by_contra! g;interval_cases q; norm_num at *
    have z : 37≤r := by by_contra! g;interval_cases r <;> norm_num at * <;> omega
    exact veto 7 31 37 (by decide) (by decide) (by decide) p7 y z (by decide +kernel)
  refine ⟨p11,q29,?_⟩
  by_cases top : 1706<r
  · left
    have pval : p=7 := by
      by_contra ne
      have x : 11≤p := by by_contra! z;interval_cases p <;> norm_num at *
      have y : 13≤q := by by_contra! z;interval_cases q <;> norm_num at * <;> omega
      exact veto 11 13 1707 (by decide) (by decide) (by decide) x y top (by decide +kernel)
    refine ⟨pval,?_⟩
    by_contra! g
    have y : 17≤q := by by_contra! z;interval_cases q <;> norm_num at *
    exact veto 7 17 1707 (by decide) (by decide) (by decide) p7 y top (by decide +kernel)
  · exact Or.inr (by omega)
end OMA.RankThreeSixteenSupport245212

end

section

/- The Euler bound leaves just seven ordered pairs for the two smallest
odd primes. Any checked collection of the seven families covers every
odd core of rank three with least prime at least seven. -/
namespace OMA.SixteenFamiliesJoin245212
open Nat Finset OMA.Smooth245212 OMA.OddFaces245212
open scoped ArithmeticFunction.sigma
open OMA.CofactorEulerPair245212 (checked)

def Family (p q : ℕ) := ∀ {r a b c : ℕ}, r.Prime → q<r → 0<a → 0<b → 0<c →
    OeisA245212.a (16*p^a*q^b*r^c)≠(σ 1 (16*p^a*q^b*r^c):ℤ)

theorem join (f7_11 : Family 7 11) (f7_13 : Family 7 13) (f7_17 : Family 7 17) (f7_19 : Family 7 19) (f7_23 : Family 7 23) (f7_29 : Family 7 29) (f11_13 : Family 11 13)
    {p q r a b c : ℕ} (pp : p.Prime) (qp : q.Prime) (rp : r.Prime)
    (p7 : 7≤p) (pq : p<q) (qr : q<r) (ap : 0<a) (bp : 0<b) (cp : 0<c) :
    OeisA245212.a (16*p^a*q^b*r^c)≠(σ 1 (16*p^a*q^b*r^c):ℤ) := by
  intro eqn
  have cap:=(OMA.RankThreeSixteenSupport245212.necessary pp qp rp (by omega) pq qr ap eqn).1
  obtain ⟨pu,qu,_⟩:=OMA.RankThreeSixteenSupport245212.order pp qp rp p7 pq qr cap
  have lo : 160≤129*(limitX p*limitX q*limitX (q+1)) := by
    have m:=cap_anti (show 1<q+1 by omega) qr
    have n:=mul_nonneg (x_nonneg pp.one_lt none) (x_nonneg qp.one_lt none)
    exact cap.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left m n) (by norm_num))
  have small : OMA.CofactorEulerPair245212.every 7 11 (fun p=>OMA.CofactorEulerPair245212.every (p+1) 29 (fun q=>
      decide (p.Prime → q.Prime → 160≤129*(limitX p*limitX q*limitX (q+1)) →
      p=7 ∧ q=11 ∨ p=7 ∧ q=13 ∨ p=7 ∧ q=17 ∨ p=7 ∧ q=19 ∨ p=7 ∧ q=23 ∨ p=7 ∧ q=29 ∨ p=11 ∧ q=13)))=true := by decide +kernel
  have pairs:=(of_decide_eq_true (OMA.CofactorEulerPair245212.checked (OMA.CofactorEulerPair245212.checked small p7 pu) pq qu)) pp qp lo
  rcases pairs with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact f7_11 rp qr ap bp cp eqn
  · exact f7_13 rp qr ap bp cp eqn
  · exact f7_17 rp qr ap bp cp eqn
  · exact f7_19 rp qr ap bp cp eqn
  · exact f7_23 rp qr ap bp cp eqn
  · exact f7_29 rp qr ap bp cp eqn
  · exact f11_13 rp qr ap bp cp eqn

end OMA.SixteenFamiliesJoin245212

end

section

namespace OMA.PrefixLeaf245212
open OMA.Large245212 OMA.Smooth245212 ArithmeticFunction
open scoped ArithmeticFunction.sigma
open OMA.Large245212 (moments)
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

open OMA.Large245212 (moments)

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

/- On an interval of exponents the candidate prime is a rounded linear
fraction. Its endpoint values bound all intermediate candidates. Scan the
shorter of the prime and exponent intervals. -/
namespace OMA.RankThreeEightSweep245212
open Nat ArithmeticFunction OMA.Smooth245212 OMA.CofactorEulerPair245212
open OMA.LastDigit245212 OMA.Large245212 OMA.PairExtension245212
open scoped ArithmeticFunction.sigma
open OMA.Large245212 (force)
open OMA.PairExtension245212 (fit)
open OMA.CofactorEulerPair245212 (checked)

private theorem ceil_bounds {x z : ℕ} (xp : 0<x) (zp : 0<z) :
    z*((x-1)/z)<x ∧ x≤z*((x-1)/z+1) := by
  have lo:=Nat.div_mul_le_self (x-1) z
  have hi:=(Nat.div_lt_iff_lt_mul zp).mp (Nat.lt_succ_self ((x-1)/z))
  change x-1<((x-1)/z+1)*z at hi
  simpa only [mul_comm z] using (show (x-1)/z*z<x ∧ x≤((x-1)/z+1)*z by omega)

private theorem between {A S D l u d q : ℕ} (sp : 0<S) (dl : S<D*(l+1)) (lo : l≤d) (hi : d≤u)
    (qpos : 0<q) (left : (D*(d+1)-S)*(q-1)<A*d+S) (right : A*d+S≤(D*(d+1)-S)*q) :
    let cand := fun j : ℕ=>(A*j+S-1)/(D*(j+1)-S)+1
    min (cand l) (cand u)≤q ∧ q ≤ max (cand l) (cand u) := by
  dsimp only
  have pe (j : ℕ) (lj : l≤j) : S<D*(j+1) :=
    dl.trans_le (Nat.mul_le_mul_left _ (by omega))
  have val (j : ℕ) (lj : l≤j) := Nat.sub_add_cancel (pe j lj).le
  have cl := ceil_bounds (x:=A*l+S) (by omega) (Nat.sub_pos_of_lt dl)
  have cu := ceil_bounds (x:=A*u+S) (by omega) (Nat.sub_pos_of_lt (pe u (lo.trans hi)))
  have rise (m j : ℕ) (lj : l≤j) (mj : m≤j) (lm : l ≤ m) :
      D*(j+1)-S=(D*(m+1)-S)+D*(j-m) := by
    nlinarith only [val m lm,val j lj,congrArg (D*·) (Nat.sub_add_cancel mj)]
  have idx {t : ℕ} (atL : (D*(l+1)-S)*t<A*l+S) (atU : (D*(u+1)-S)*t<A*u+S) :
      (D*(d+1)-S)*t<A*d+S := by
    by_cases k : D*t≤A
    · rw [rise l d lo lo le_rfl]
      nlinarith only [atL,Nat.mul_le_mul_right (d-l) k,congrArg (A*·) (Nat.sub_add_cancel lo)]
    · rw [rise d u (lo.trans hi) hi lo] at atU
      nlinarith only [atU,Nat.mul_le_mul_right (u-d) (Nat.le_of_not_ge k),congrArg (A*·) (Nat.sub_add_cancel hi)]
  have idx' {t : ℕ} (atL : A*l+S≤(D*(l+1)-S)*t) (atU : A*u+S≤(D*(u+1)-S)*t) :
      A*d+S≤(D*(d+1)-S)*t := by
    by_cases k : A≤D*t
    · rw [rise l d lo lo le_rfl]
      nlinarith only [atL,Nat.mul_le_mul_right (d-l) k,congrArg (A*·) (Nat.sub_add_cancel lo)]
    · rw [rise d u (lo.trans hi) hi lo] at atU
      nlinarith only [atU,Nat.mul_le_mul_right (u-d) (Nat.le_of_not_ge k),congrArg (A*·) (Nat.sub_add_cancel hi)]
  constructor
  · by_contra! bad
    rw [lt_min_iff] at bad
    have neg:=idx ((Nat.mul_le_mul_left (D*(l+1)-S) (show q≤_ by omega)).trans_lt cl.1)
      ((Nat.mul_le_mul_left (D*(u+1)-S) (show q≤_ by omega)).trans_lt cu.1)
    omega
  · by_contra! bad
    rw [max_lt_iff] at bad
    have yes:=idx' (cl.2.trans (Nat.mul_le_mul_left (D*(l+1)-S) (show _≤q-1 by omega)))
      (cu.2.trans (Nat.mul_le_mul_left (D*(u+1)-S) (show _≤q-1 by omega)))
    omega

def single (A S T R d : ℕ) :=
  let q:=candidate A S T d
  decide (q<R) || !permitted A S T q d

def block (A S T R l u : ℕ) : Bool :=
  if u<l then true else
  let x:=candidate A S T l
  let y:=candidate A S T u
  let lo:=max R (min x y)
  let hi:=max x y
  if hi-lo≤u-l then every lo hi (fun q=>OMA.RankThreeLast245212.reject q A S T u)
  else every l u (single A S T R)

private theorem block_sound {m q d R l u : ℕ} (hm : 0 < m) (pr : q.Prime) (oq : q≠2)
    (cop : m.Coprime q) (dp : 0<d) (rq : R≤q) (ld : l≤d) (du : d≤u)
    (first : 0<denom (W m) (σ 1 m) (m*σ 0 m) l)
    (ck : block (W m) (σ 1 m) (m*σ 0 m) R l u=true)
    (eqn : OeisA245212.a (m*q^d)=(σ 1 (m*q^d):ℤ)) : False := by
  let A:=W m
  let S:=σ 1 m
  let T:=m*σ 0 m
  let G:=2*T-A
  have sp : 0<S:=sigma_pos 1 m hm.ne'
  have digits:=balance_digits hm pr cop dp eqn
  have z:=OMA.Large245212.force sp pr.one_lt digits.1 digits.2.1 digits.2.2.1
  have id (j : ℕ) : denom A S T j=G*(j+1)-S := by simp only [denom,G,Nat.sub_mul];omega
  change 0<denom A S T l at first
  have pos:=Nat.sub_pos_iff_lt.mp ((id l) ▸ first)
  have lo:=digits.2.1
  have hi:=digits.2.2.1
  change denom A S T d*(q-1)<A*d+S at lo
  change A*d+S≤denom A S T d*q at hi
  rw [id] at lo hi
  have bounds := between sp pos ld du pr.pos lo hi
  change block A S T R l u=true at ck
  rw [block,if_neg (Nat.not_lt.mpr (ld.trans du))] at ck
  dsimp only at ck
  have spec (j : ℕ) : candidate A S T j=(A*j+S-1)/(G*(j+1)-S)+1 := by rw [candidate,id]
  split at ck
  · have br : min (candidate A S T l) (candidate A S T u)≤q ∧ q ≤ max (candidate A S T l) (candidate A S T u) := by
      simpa only [spec] using bounds
    have found:=OMA.CofactorEulerPair245212.checked ck (max_le rq br.1) br.2
    have no:=OMA.RankThreeLast245212.reject_sound hm pr oq cop dp du eqn
    rw [show OMA.RankThreeLast245212.reject q A S T u=false from no] at found
    contradiction
  · have found:=OMA.CofactorEulerPair245212.checked ck ld du
    change candidate A S T d=q at z
    simp [single,z,Nat.not_lt.mpr rq,show permitted A S T q d=true from OMA.PairExtension245212.fit hm pr cop dp eqn] at found

def sweep (R A S T : ℕ) : Bool :=
  let G:=2*T-A
  if G=0 then true else
  let lo:=max 1 (S/G)
  let hi:=Nat.log (lowerBase R A T) (A+S)+1
  every 0 (Nat.log 2 hi) fun j=>block A S T R (max lo (2^j)) (min hi (2^(j+1)-1))

theorem sweep_sound {m q d R : ℕ} (hm : 0 < m) (pr : q.Prime) (oq : q≠2) (cop : m.Coprime q)
    (dp : 0<d) (rq : R≤q) (ck : sweep R (W m) (σ 1 m) (m*σ 0 m)=true) :
    OeisA245212.a (m*q^d)≠(σ 1 (m*q^d):ℤ) := by
  intro eqn
  let A:=W m
  let S:=σ 1 m
  let T:=m*σ 0 m
  let G:=2*T-A
  let hi:=Nat.log (lowerBase R A T) (A+S)+1
  obtain ⟨positive,_,digit,_⟩:=balance_digits hm pr cop dp eqn
  have base:=lowerBase_le pr.two_le rq dp positive digit
  have top : d≤hi:=last_log_base hm pr oq cop ((by decide : 1<2).trans_le (le_max_left ..)) base dp eqn
  have den (j : ℕ) : denom A S T j=G*(j+1)-S := by simp only [denom,G,Nat.sub_mul];omega
  change 0<denom A S T d at positive
  have dl:=Nat.sub_pos_iff_lt.mp ((den d) ▸ positive)
  have gp : 0<G:=by
    by_contra! bad
    have z : G=0:=by omega
    simp [z] at dl
  have good:= (Nat.div_lt_iff_lt_mul gp).mpr (by simpa [mul_comm] using dl)
  let j:=Nat.log 2 d
  have below : max (max 1 (S/G)) (2^j)≤d := max_le (max_le dp (by omega)) (Nat.pow_log_le_self _ dp.ne')
  have above : d ≤ min hi (2^(j+1)-1) := by have:=Nat.lt_pow_succ_log_self (by decide : 1<2) d;dsimp [j];omega
  have low := (le_max_left (max 1 (S/G)) (2^j))
  have pl : 0<denom A S T (max (max 1 (S/G)) (2^j)) := by
    rw [den];apply Nat.sub_pos_of_lt
    rw [mul_comm G];apply (Nat.div_lt_iff_lt_mul gp).mp;omega
  change sweep R A S T=true at ck
  rw [sweep,if_neg (show 2*T-A≠0 from gp.ne')] at ck
  change every 0 (Nat.log 2 hi) (fun i=>block A S T R (max (max 1 (S/G)) (2^i)) (min hi (2^(i+1)-1)))=true at ck
  have selected:=OMA.CofactorEulerPair245212.checked ck (Nat.zero_le j) (Nat.log_mono_right top)
  exact block_sound hm pr oq cop dp rq below above pl selected eqn

end OMA.RankThreeEightSweep245212

end

section

/- A fixed odd prime and an unbounded last prime after an exact dyadic prefix.
Use the short-prime alternative below the two-prime Euler limit. Above it
the two-way terminal digit sweep bounds the candidate degrees and primes. -/
namespace OMA.RankThreeEightMoving245212
open Nat ArithmeticFunction OMA.Smooth245212 OMA.CofactorEulerPair245212
open OMA.RankThreeFourSmallFast245212 OMA.RankThreeFourSmallNear245212
open OMA.RankThreeEightSweep245212
open scoped ArithmeticFunction.sigma
open OMA.Large245212 (moments)
open OMA.CofactorEulerPair245212 (checked)

def line (A S T p R b : ℕ) := sweep R (A*OMA.Large245212.wt p b)
  (S*OMA.Large245212.sig p b) (T*OMA.Large245212.tax p b)

theorem line_sound {h p q b d R : ℕ} (hh : 0 < h) (pp : p.Prime) (qp : q.Prime)
    (op : 2<q) (pc : h.Coprime p) (qc : h.Coprime q) (ne : p≠q) (dp : 0<d) (rq : R≤q)
    (ck : line (W h) (σ 1 h) (h*σ 0 h) p R b=true) :
    OeisA245212.a (h*p^b*q^d)≠(σ 1 (h*p^b*q^d):ℤ) := by
  obtain ⟨y,w⟩:=OMA.Large245212.moments pp b
  have cop:=pc.pow_right b
  have hp:=pp.pos
  apply sweep_sound (by positivity) qp (by omega) (qc.mul_left (((coprime_primes pp qp).mpr ne).pow_left b)) dp rq
  rw [w_mult.map_mul_of_coprime cop,isMultiplicative_sigma.map_mul_of_coprime cop,
    isMultiplicative_sigma.map_mul_of_coprime cop,sigma_zero_apply_prime_pow pp]
  simpa only [line,OMA.Large245212.tax,mul_assoc,mul_left_comm,mul_comm,y,w] using ck

def low (h A S T p R Q : ℕ) : Bool :=
  if Q≤R+128 then every R Q (quick h A S T p) else
  ((2*T).primeFactorsList.all fun q=>decide (q<R ∨ ¬h.Coprime q) || quick h A S T p q) &&
  every 1 (nearCap h A S p Q) (line A S T p R)

theorem low_sound {h p q b d R Q : ℕ} (hh : 0 < h) (pp : p.Prime) (qp : q.Prime)
    (op : 2<p) (pc : h.Coprime p) (qc : h.Coprime q) (pq : p<q) (bp : 0<b) (dp : 0<d)
    (rq : R≤q) (cap : q≤Q) (ck : low h (W h) (σ 1 h) (h*σ 0 h) p R Q=true)
    (eqn : OeisA245212.a (h*p^b*q^d)=(σ 1 (h*p^b*q^d):ℤ)) : False := by
  unfold low at ck
  split at ck
  · exact quick_sound hh pp qp op pc qc pq bp dp (OMA.CofactorEulerPair245212.checked ck rq cap) eqn
  · rw [Bool.and_eq_true] at ck
    by_cases bad : q∣2*(h*σ 0 h)
    · have tau:=sigma_pos 0 h hh.ne'
      have mem:=Nat.mem_primeFactors_iff_mem_primeFactorsList.mp (qp.mem_primeFactors bad (by positivity))
      have z:=List.all_eq_true.mp ck.1 q mem
      have eligible : ¬(q<R ∨ ¬h.Coprime q) := by push Not;exact ⟨rq,qc⟩
      exact quick_sound hh pp qp op pc qc pq bp dp (by simpa [eligible] using z) eqn
    · have bb:=near_bound hh pp qp op pc qc pq bp dp cap bad eqn
      exact line_sound hh pp qp (by omega) pc qc pq.ne dp rq (OMA.CofactorEulerPair245212.checked ck.2 bp bb) eqn

def run (h A S T p R : ℕ) : Bool :=
  decide (A+S≤2*T) &&
  (if 2*T*(p-1)<A*p then every 1 (2*A/(A*p-2*T*(p-1))) (line A S T p R)
   else if A*p<2*T*(p-1) then low h A S T p R (2*T*(p-1)/(2*T*(p-1)-A*p)) else false)

theorem run_sound {h p q a d R : ℕ} (hh : 0 < h) (pp : p.Prime) (qp : q.Prime)
    (op : 2<p) (pc : h.Coprime p) (qc : h.Coprime q) (pq : p<q) (ap : 0<a) (dp : 0<d)
    (rq : R≤q) (ck : run h (W h) (σ 1 h) (h*σ 0 h) p R=true) :
    OeisA245212.a (h*p^a*q^d)≠(σ 1 (h*p^a*q^d):ℤ) := by
  intro eqn
  rw [run,Bool.and_eq_true,decide_eq_true_eq] at ck
  obtain ⟨sub,ok⟩:=ck
  obtain ⟨limit,actual⟩:=original_cap hh pp qp pc qc pq.ne ap sub eqn
  split at ok
  next high =>
    have upper:=short_first (a:=a) (d:=d) pp qp high (by simpa only [Nat.cast_mul,Nat.cast_ofNat] using actual)
    exact line_sound hh pp qp (by omega) pc qc pq.ne dp rq
      (OMA.CofactorEulerPair245212.checked ok ap (by omega)) eqn
  next =>
    split at ok
    next under => exact low_sound hh pp qp op pc qc pq ap dp rq (second_bound qp.one_lt under limit) ok eqn
    next => contradiction


end OMA.RankThreeEightMoving245212

end

section

/- Tests for a known 16 times an odd prime power, with two remaining odd
primes and their exponents free. -/
namespace OMA.RankThreeSixteenMoving245212
open Nat Finset ArithmeticFunction OMA.Smooth245212 OMA.CofactorEulerPair245212
open OMA.RankThreeEightMoving245212 (line low run run_sound)
open scoped ArithmeticFunction.sigma
open OMA.Large245212 (moments)
open OMA.CofactorEulerPair245212 (checked)

def atom (s p e : ℕ) := run (16*s^e) (129*OMA.Large245212.wt s e)
  (31*OMA.Large245212.sig s e) (80*OMA.Large245212.tax s e) p (max s p+1)

theorem single {f : ℕ→Bool} {e : ℕ} (h : f e=true) : every e e f=true := by
  apply List.all_eq_true.mpr
  intro j hj
  obtain ⟨lo,hi⟩:=List.mem_range'_1.mp hj
  simpa only [show j=e by omega] using h

theorem row_high {s p e h A S T R B : ℕ}
    (vals : (16*s^e,129*OMA.Large245212.wt s e,31*OMA.Large245212.sig s e,80*OMA.Large245212.tax s e,max s p+1)=(h,A,S,T,R))
    (sub : A+S≤2*T) (hi : 2*T*(p-1)<A*p) (cap : 2*A/(A*p-2*T*(p-1))=B)
    (rows : every 1 B (line A S T p R)=true) : atom s p e=true := by
  simp only [Prod.mk.injEq] at vals
  obtain ⟨rfl,rfl,rfl,rfl,rfl⟩:=vals
  simpa only [atom,run,decide_eq_true sub,Bool.true_and,if_pos hi,cap] using rows

theorem row_low {s p e h A S T R Q : ℕ}
    (vals : (16*s^e,129*OMA.Large245212.wt s e,31*OMA.Large245212.sig s e,80*OMA.Large245212.tax s e,max s p+1)=(h,A,S,T,R))
    (sub : A+S≤2*T) (lo : A*p<2*T*(p-1)) (cap : 2*T*(p-1)/(2*T*(p-1)-A*p)=Q)
    (rows : low h A S T p R Q=true) : atom s p e=true := by
  simp only [Prod.mk.injEq] at vals
  obtain ⟨rfl,rfl,rfl,rfl,rfl⟩:=vals
  simpa only [atom,run,decide_eq_true sub,Bool.true_and,if_neg lo.not_gt,if_pos lo,cap] using rows

theorem atom_sound {s p q a b d : ℕ} (sp : s.Prime) (pp : p.Prime) (qp : q.Prime)
    (os : 2<s) (op : 2<p) (ps : s≠p) (sq : s<q) (pq : p<q)
    (bp : 0<b) (dp : 0<d) (ck : atom s p a=true) :
    OeisA245212.a (16*s^a*p^b*q^d)≠(σ 1 (16*s^a*p^b*q^d):ℤ) := by
  obtain ⟨sg,wt⟩:=OMA.Large245212.moments sp a
  have cs : (16:ℕ).Coprime (s^a) := (((coprime_primes prime_two sp).mpr (by omega)).pow_left 4).pow_right a
  have cop (t) (tp : t.Prime) (ot : 2<t) (st : s≠t) : (16*s^a).Coprime t :=
    (((coprime_primes prime_two tp).mpr (by omega)).pow_left 4).mul_left (((coprime_primes sp tp).mpr st).pow_left a)
  have vals : W 16=129 ∧ σ 1 16=31 ∧ σ 0 16=5 := by decide +kernel
  have w : W (16*s^a)=129*OMA.Large245212.wt s a := by rw [w_mult.map_mul_of_coprime cs,vals.1,wt]
  have y : σ 1 (16*s^a)=31*OMA.Large245212.sig s a := by rw [isMultiplicative_sigma.map_mul_of_coprime cs,vals.2.1,sg]
  have t : 16*s^a*σ 0 (16*s^a)=80*OMA.Large245212.tax s a := by
    rw [isMultiplicative_sigma.map_mul_of_coprime cs,vals.2.2,sigma_zero_apply_prime_pow sp,OMA.Large245212.tax];ring
  have hs:=sp.pos
  apply run_sound (by positivity) pp qp op (cop p pp op ps) (cop q qp (by omega) sq.ne) pq bp dp (show max s p+1≤q by omega)
  simpa only [w,y,t,atom] using ck

theorem close {p q r a b d l u : ℕ} (pp : p.Prime) (qp : q.Prime) (rp : r.Prime)
    (op : 2<p) (pq : p<q) (qr : q<r) (ap : 0<a) (bp : 0<b) (dp : 0<d)
    (above : 160≤129*(X p (some l)*X q (some u)))
    (firsts : every 1 (l-1) (atom p q)=true) (seconds : every 1 (u-1) (atom q p)=true) :
    OeisA245212.a (16*p^a*q^b*r^d)≠(σ 1 (16*p^a*q^b*r^d):ℤ) := by
  intro eqn
  by_cases al : a<l
  · exact atom_sound pp qp rp op (by omega) pq.ne (pq.trans qr) qr bp dp (OMA.CofactorEulerPair245212.checked firsts ap (by omega)) eqn
  by_cases bu : b<u
  · exact atom_sound qp pp rp (by omega) op pq.ne.symm qr (pq.trans qr) ap dp
      (OMA.CofactorEulerPair245212.checked seconds bp (by omega)) (by rwa [mul_right_comm 16 (q^b) (p^a)])
  have rises {s n m : ℕ} (sp : s.Prime) (nm : n ≤ m) : X s (some n)≤X s (some m) :=
    add_le_add_right (div_le_div_of_nonneg_right (sub_le_sub_left (y_anti sp.one_lt nm) 1)
      (sub_nonneg.mpr (by exact_mod_cast sp.one_le))) 1
  have inc:=mul_le_mul (rises pp (Nat.le_of_not_gt al)) (rises qp (Nat.le_of_not_gt bu))
    (x_nonneg qp.one_lt _) (x_nonneg pp.one_lt _)
  have strict:=(OMA.RankThreeSixteenSupport245212.necessary pp qp rp op pq qr ap eqn).2
  linarith

end OMA.RankThreeSixteenMoving245212

end

section

/- Exclusion of one unrestricted terminal-prime family at dyadic order four. -/
/- One exact initial prime power, with the last prime unrestricted. -/
namespace OMA.SixteenAt7E1P11
open OMA.RankThreeEightMoving245212 (line low)
open OMA.RankThreeSixteenMoving245212 OMA.CofactorEulerPair245212
open OMA.RankThreeFourSmallFast245212 (quick)
open OMA.RankThreeMiddle245212 (joinEvery)
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
private theorem b12 : every 12 20 (quick 112 1935 248 1120 11)=true := by decide +kernel
theorem certificate : atom 7 11 1=true := by
  apply row_low (h:=112) (A:=1935) (S:=248) (T:=1120) (R:=12) (Q:=20) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  rw [low,if_pos (by decide : 20≤12+128)]
  exact b12
end OMA.SixteenAt7E1P11

/- One exact initial prime power, with the last prime unrestricted. -/
namespace OMA.SixteenAt7E2P11
open OMA.RankThreeEightMoving245212 (line low)
open OMA.RankThreeSixteenMoving245212 OMA.CofactorEulerPair245212
open OMA.RankThreeFourSmallFast245212 (quick)
open OMA.RankThreeMiddle245212 (joinEvery)
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
private theorem b12 : every 12 27 (quick 784 20898 1767 11760 11)=true := by decide +kernel
private theorem b28 : every 28 43 (quick 784 20898 1767 11760 11)=true := by decide +kernel
private theorem b44 : every 44 44 (quick 784 20898 1767 11760 11)=true := by decide +kernel
theorem certificate : atom 7 11 2=true := by
  apply row_low (h:=784) (A:=20898) (S:=1767) (T:=11760) (R:=12) (Q:=44) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  rw [low,if_pos (by decide : 44≤12+128)]
  exact (joinEvery b12 (joinEvery b28 b44))
end OMA.SixteenAt7E2P11

/- One exact initial prime power, with the last prime unrestricted. -/
namespace OMA.SixteenAt7E3P11
open OMA.RankThreeEightMoving245212 (line low)
open OMA.RankThreeSixteenMoving245212 OMA.CofactorEulerPair245212
open OMA.RankThreeFourSmallFast245212 (quick)
open OMA.RankThreeMiddle245212 (joinEvery)
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
private theorem b12 : every 12 27 (quick 5488 197886 12400 109760 11)=true := by decide +kernel
private theorem b28 : every 28 43 (quick 5488 197886 12400 109760 11)=true := by decide +kernel
private theorem b44 : every 44 59 (quick 5488 197886 12400 109760 11)=true := by decide +kernel
private theorem b60 : every 60 75 (quick 5488 197886 12400 109760 11)=true := by decide +kernel
private theorem b76 : every 76 91 (quick 5488 197886 12400 109760 11)=true := by decide +kernel
private theorem b92 : every 92 107 (quick 5488 197886 12400 109760 11)=true := by decide +kernel
private theorem b108 : every 108 118 (quick 5488 197886 12400 109760 11)=true := by decide +kernel
theorem certificate : atom 7 11 3=true := by
  apply row_low (h:=5488) (A:=197886) (S:=12400) (T:=109760) (R:=12) (Q:=118) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  rw [low,if_pos (by decide : 118≤12+128)]
  exact (joinEvery (joinEvery b12 (joinEvery b28 b44)) (joinEvery (joinEvery b60 b76) (joinEvery b92 b108)))
end OMA.SixteenAt7E3P11

/- One exact initial prime power, with the last prime unrestricted. -/
namespace OMA.SixteenAt7E4P11
open OMA.RankThreeEightMoving245212 (line low)
open OMA.RankThreeSixteenMoving245212 OMA.CofactorEulerPair245212
open OMA.RankThreeFourSmallFast245212 (quick)
open OMA.RankThreeMiddle245212 (joinEvery)
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
private theorem b1 : every 1 16 (line 1746531 86831 960400 11 12)=true := by decide +kernel
private theorem b17 : every 17 32 (line 1746531 86831 960400 11 12)=true := by decide +kernel
private theorem b33 : every 33 48 (line 1746531 86831 960400 11 12)=true := by decide +kernel
private theorem b49 : every 49 64 (line 1746531 86831 960400 11 12)=true := by decide +kernel
private theorem b65 : every 65 80 (line 1746531 86831 960400 11 12)=true := by decide +kernel
private theorem b81 : every 81 96 (line 1746531 86831 960400 11 12)=true := by decide +kernel
private theorem b97 : every 97 112 (line 1746531 86831 960400 11 12)=true := by decide +kernel
private theorem b113 : every 113 128 (line 1746531 86831 960400 11 12)=true := by decide +kernel
private theorem b129 : every 129 144 (line 1746531 86831 960400 11 12)=true := by decide +kernel
private theorem b145 : every 145 160 (line 1746531 86831 960400 11 12)=true := by decide +kernel
private theorem b161 : every 161 176 (line 1746531 86831 960400 11 12)=true := by decide +kernel
private theorem b177 : every 177 192 (line 1746531 86831 960400 11 12)=true := by decide +kernel
private theorem b193 : every 193 208 (line 1746531 86831 960400 11 12)=true := by decide +kernel
private theorem b209 : every 209 224 (line 1746531 86831 960400 11 12)=true := by decide +kernel
private theorem b225 : every 225 240 (line 1746531 86831 960400 11 12)=true := by decide +kernel
private theorem b241 : every 241 256 (line 1746531 86831 960400 11 12)=true := by decide +kernel
private theorem b257 : every 257 272 (line 1746531 86831 960400 11 12)=true := by decide +kernel
private theorem b273 : every 273 288 (line 1746531 86831 960400 11 12)=true := by decide +kernel
private theorem b289 : every 289 304 (line 1746531 86831 960400 11 12)=true := by decide +kernel
private theorem b305 : every 305 320 (line 1746531 86831 960400 11 12)=true := by decide +kernel
private theorem b321 : every 321 336 (line 1746531 86831 960400 11 12)=true := by decide +kernel
private theorem b337 : every 337 352 (line 1746531 86831 960400 11 12)=true := by decide +kernel
private theorem b353 : every 353 368 (line 1746531 86831 960400 11 12)=true := by decide +kernel
private theorem b369 : every 369 384 (line 1746531 86831 960400 11 12)=true := by decide +kernel
private theorem b385 : every 385 400 (line 1746531 86831 960400 11 12)=true := by decide +kernel
private theorem b401 : every 401 416 (line 1746531 86831 960400 11 12)=true := by decide +kernel
private theorem b417 : every 417 432 (line 1746531 86831 960400 11 12)=true := by decide +kernel
private theorem b433 : every 433 448 (line 1746531 86831 960400 11 12)=true := by decide +kernel
private theorem b449 : every 449 464 (line 1746531 86831 960400 11 12)=true := by decide +kernel
private theorem b465 : every 465 480 (line 1746531 86831 960400 11 12)=true := by decide +kernel
private theorem b481 : every 481 496 (line 1746531 86831 960400 11 12)=true := by decide +kernel
private theorem b497 : every 497 512 (line 1746531 86831 960400 11 12)=true := by decide +kernel
private theorem b513 : every 513 528 (line 1746531 86831 960400 11 12)=true := by decide +kernel
private theorem b529 : every 529 544 (line 1746531 86831 960400 11 12)=true := by decide +kernel
private theorem b545 : every 545 560 (line 1746531 86831 960400 11 12)=true := by decide +kernel
private theorem b561 : every 561 576 (line 1746531 86831 960400 11 12)=true := by decide +kernel
private theorem b577 : every 577 592 (line 1746531 86831 960400 11 12)=true := by decide +kernel
private theorem b593 : every 593 608 (line 1746531 86831 960400 11 12)=true := by decide +kernel
private theorem b609 : every 609 624 (line 1746531 86831 960400 11 12)=true := by decide +kernel
private theorem b625 : every 625 640 (line 1746531 86831 960400 11 12)=true := by decide +kernel
private theorem b641 : every 641 656 (line 1746531 86831 960400 11 12)=true := by decide +kernel
private theorem b657 : every 657 672 (line 1746531 86831 960400 11 12)=true := by decide +kernel
private theorem b673 : every 673 688 (line 1746531 86831 960400 11 12)=true := by decide +kernel
private theorem b689 : every 689 704 (line 1746531 86831 960400 11 12)=true := by decide +kernel
private theorem b705 : every 705 720 (line 1746531 86831 960400 11 12)=true := by decide +kernel
private theorem b721 : every 721 736 (line 1746531 86831 960400 11 12)=true := by decide +kernel
private theorem b737 : every 737 752 (line 1746531 86831 960400 11 12)=true := by decide +kernel
private theorem b753 : every 753 768 (line 1746531 86831 960400 11 12)=true := by decide +kernel
private theorem b769 : every 769 784 (line 1746531 86831 960400 11 12)=true := by decide +kernel
private theorem b785 : every 785 800 (line 1746531 86831 960400 11 12)=true := by decide +kernel
private theorem b801 : every 801 816 (line 1746531 86831 960400 11 12)=true := by decide +kernel
private theorem b817 : every 817 832 (line 1746531 86831 960400 11 12)=true := by decide +kernel
private theorem b833 : every 833 848 (line 1746531 86831 960400 11 12)=true := by decide +kernel
private theorem b849 : every 849 864 (line 1746531 86831 960400 11 12)=true := by decide +kernel
private theorem b865 : every 865 880 (line 1746531 86831 960400 11 12)=true := by decide +kernel
private theorem b881 : every 881 896 (line 1746531 86831 960400 11 12)=true := by decide +kernel
private theorem b897 : every 897 909 (line 1746531 86831 960400 11 12)=true := by decide +kernel
theorem certificate : atom 7 11 4=true := by
  apply row_high (h:=38416) (A:=1746531) (S:=86831) (T:=960400) (R:=12) (B:=909) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact (joinEvery (joinEvery (joinEvery (joinEvery (joinEvery b1 (joinEvery b17 b33)) (joinEvery (joinEvery b49 b65) (joinEvery b81 b97))) (joinEvery (joinEvery b113 (joinEvery b129 b145)) (joinEvery (joinEvery b161 b177) (joinEvery b193 b209)))) (joinEvery (joinEvery (joinEvery b225 (joinEvery b241 b257)) (joinEvery (joinEvery b273 b289) (joinEvery b305 b321))) (joinEvery (joinEvery b337 (joinEvery b353 b369)) (joinEvery (joinEvery b385 b401) (joinEvery b417 b433))))) (joinEvery (joinEvery (joinEvery (joinEvery b449 (joinEvery b465 b481)) (joinEvery (joinEvery b497 b513) (joinEvery b529 b545))) (joinEvery (joinEvery b561 (joinEvery b577 b593)) (joinEvery (joinEvery b609 b625) (joinEvery b641 b657)))) (joinEvery (joinEvery (joinEvery b673 (joinEvery b689 b705)) (joinEvery (joinEvery b721 b737) (joinEvery b753 b769))) (joinEvery (joinEvery (joinEvery b785 b801) (joinEvery b817 b833)) (joinEvery (joinEvery b849 b865) (joinEvery b881 b897))))))
end OMA.SixteenAt7E4P11

/- One exact initial prime power, with the last prime unrestricted. -/
namespace OMA.SixteenAt7E5P11
open OMA.RankThreeEightMoving245212 (line low)
open OMA.RankThreeSixteenMoving245212 OMA.CofactorEulerPair245212
open OMA.RankThreeFourSmallFast245212 (quick)
open OMA.RankThreeMiddle245212 (joinEvery)
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
private theorem b1 : every 1 16 (line 14755149 607848 8067360 11 12)=true := by decide +kernel
private theorem b17 : every 17 30 (line 14755149 607848 8067360 11 12)=true := by decide +kernel
theorem certificate : atom 7 11 5=true := by
  apply row_high (h:=268912) (A:=14755149) (S:=607848) (T:=8067360) (R:=12) (B:=30) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact (joinEvery b1 b17)
end OMA.SixteenAt7E5P11

/- One exact initial prime power, with the last prime unrestricted. -/
namespace OMA.SixteenAt7E6P11
open OMA.RankThreeEightMoving245212 (line low)
open OMA.RankThreeSixteenMoving245212 OMA.CofactorEulerPair245212
open OMA.RankThreeFourSmallFast245212 (quick)
open OMA.RankThreeMiddle245212 (joinEvery)
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
private theorem b1 : every 1 16 (line 120992196 4254967 65883440 11 12)=true := by decide +kernel
private theorem b17 : every 17 18 (line 120992196 4254967 65883440 11 12)=true := by decide +kernel
theorem certificate : atom 7 11 6=true := by
  apply row_high (h:=1882384) (A:=120992196) (S:=4254967) (T:=65883440) (R:=12) (B:=18) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact (joinEvery b1 b17)
end OMA.SixteenAt7E6P11

namespace OMA.SixteenShort7P11
open OMA.CofactorEulerPair245212 OMA.RankThreeSixteenMoving245212
open OMA.RankThreeMiddle245212 (joinEvery)
theorem rows : every 1 6 (atom 7 11)=true := (joinEvery (joinEvery (single (f:=atom 7 11) OMA.SixteenAt7E1P11.certificate) (joinEvery (single (f:=atom 7 11) OMA.SixteenAt7E2P11.certificate) (single (f:=atom 7 11) OMA.SixteenAt7E3P11.certificate))) (joinEvery (single (f:=atom 7 11) OMA.SixteenAt7E4P11.certificate) (joinEvery (single (f:=atom 7 11) OMA.SixteenAt7E5P11.certificate) (single (f:=atom 7 11) OMA.SixteenAt7E6P11.certificate))))
end OMA.SixteenShort7P11
/- One exact initial prime power, with the last prime unrestricted. -/
namespace OMA.SixteenAt11E1P7
open OMA.RankThreeEightMoving245212 (line low)
open OMA.RankThreeSixteenMoving245212 OMA.CofactorEulerPair245212
open OMA.RankThreeFourSmallFast245212 (quick)
open OMA.RankThreeMiddle245212 (joinEvery)
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
private theorem b12 : every 12 27 (quick 176 2967 372 1760 7)=true := by decide +kernel
private theorem b28 : every 28 43 (quick 176 2967 372 1760 7)=true := by decide +kernel
private theorem b44 : every 44 59 (quick 176 2967 372 1760 7)=true := by decide +kernel
private theorem b60 : every 60 60 (quick 176 2967 372 1760 7)=true := by decide +kernel
theorem certificate : atom 11 7 1=true := by
  apply row_low (h:=176) (A:=2967) (S:=372) (T:=1760) (R:=12) (Q:=60) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  rw [low,if_pos (by decide : 60≤12+128)]
  exact (joinEvery (joinEvery b12 b28) (joinEvery b44 b60))
end OMA.SixteenAt11E1P7

/- One exact initial prime power, with the last prime unrestricted. -/
namespace OMA.SixteenAt11E2P7
open OMA.RankThreeEightMoving245212 (line low)
open OMA.RankThreeSixteenMoving245212 OMA.CofactorEulerPair245212
open OMA.RankThreeFourSmallFast245212 (quick)
open OMA.RankThreeMiddle245212 (joinEvery)
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
private theorem b1 : every 1 16 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b17 : every 17 32 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b33 : every 33 48 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b49 : every 49 64 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b65 : every 65 80 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b81 : every 81 96 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b97 : every 97 112 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b113 : every 113 128 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b129 : every 129 144 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b145 : every 145 160 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b161 : every 161 176 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b177 : every 177 192 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b193 : every 193 208 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b209 : every 209 224 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b225 : every 225 240 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b241 : every 241 256 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b257 : every 257 272 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b273 : every 273 288 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b289 : every 289 304 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b305 : every 305 320 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b321 : every 321 336 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b337 : every 337 352 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b353 : every 353 368 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b369 : every 369 384 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b385 : every 385 400 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b401 : every 401 416 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b417 : every 417 432 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b433 : every 433 448 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b449 : every 449 464 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b465 : every 465 480 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b481 : every 481 496 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b497 : every 497 512 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b513 : every 513 528 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b529 : every 529 544 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b545 : every 545 560 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b561 : every 561 576 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b577 : every 577 592 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b593 : every 593 608 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b609 : every 609 624 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b625 : every 625 640 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b641 : every 641 656 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b657 : every 657 672 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b673 : every 673 688 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b689 : every 689 704 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b705 : every 705 720 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b721 : every 721 736 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b737 : every 737 752 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b753 : every 753 768 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b769 : every 769 784 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b785 : every 785 800 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b801 : every 801 816 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b817 : every 817 832 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b833 : every 833 848 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b849 : every 849 864 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b865 : every 865 880 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b881 : every 881 896 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b897 : every 897 912 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b913 : every 913 928 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b929 : every 929 944 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b945 : every 945 960 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b961 : every 961 976 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b977 : every 977 992 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b993 : every 993 1008 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b1009 : every 1009 1024 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b1025 : every 1025 1040 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b1041 : every 1041 1056 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b1057 : every 1057 1072 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b1073 : every 1073 1088 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b1089 : every 1089 1104 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b1105 : every 1105 1120 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b1121 : every 1121 1136 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b1137 : every 1137 1152 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b1153 : every 1153 1168 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b1169 : every 1169 1184 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b1185 : every 1185 1200 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b1201 : every 1201 1216 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b1217 : every 1217 1232 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b1233 : every 1233 1248 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b1249 : every 1249 1264 (line 49794 4123 29040 7 12)=true := by decide +kernel
private theorem b1265 : every 1265 1276 (line 49794 4123 29040 7 12)=true := by decide +kernel
theorem certificate : atom 11 7 2=true := by
  apply row_high (h:=1936) (A:=49794) (S:=4123) (T:=29040) (R:=12) (B:=1276) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact (joinEvery (joinEvery (joinEvery (joinEvery (joinEvery (joinEvery b1 b17) (joinEvery b33 (joinEvery b49 b65))) (joinEvery (joinEvery b81 b97) (joinEvery b113 (joinEvery b129 b145)))) (joinEvery (joinEvery (joinEvery b161 b177) (joinEvery b193 (joinEvery b209 b225))) (joinEvery (joinEvery b241 b257) (joinEvery b273 (joinEvery b289 b305))))) (joinEvery (joinEvery (joinEvery (joinEvery b321 b337) (joinEvery b353 (joinEvery b369 b385))) (joinEvery (joinEvery b401 b417) (joinEvery b433 (joinEvery b449 b465)))) (joinEvery (joinEvery (joinEvery b481 b497) (joinEvery b513 (joinEvery b529 b545))) (joinEvery (joinEvery b561 b577) (joinEvery b593 (joinEvery b609 b625)))))) (joinEvery (joinEvery (joinEvery (joinEvery (joinEvery b641 b657) (joinEvery b673 (joinEvery b689 b705))) (joinEvery (joinEvery b721 b737) (joinEvery b753 (joinEvery b769 b785)))) (joinEvery (joinEvery (joinEvery b801 b817) (joinEvery b833 (joinEvery b849 b865))) (joinEvery (joinEvery b881 b897) (joinEvery b913 (joinEvery b929 b945))))) (joinEvery (joinEvery (joinEvery (joinEvery b961 b977) (joinEvery b993 (joinEvery b1009 b1025))) (joinEvery (joinEvery b1041 b1057) (joinEvery b1073 (joinEvery b1089 b1105)))) (joinEvery (joinEvery (joinEvery b1121 b1137) (joinEvery b1153 (joinEvery b1169 b1185))) (joinEvery (joinEvery b1201 b1217) (joinEvery b1233 (joinEvery b1249 b1265)))))))
end OMA.SixteenAt11E2P7

/- One exact initial prime power, with the last prime unrestricted. -/
namespace OMA.SixteenAt11E3P7
open OMA.RankThreeEightMoving245212 (line low)
open OMA.RankThreeSixteenMoving245212 OMA.CofactorEulerPair245212
open OMA.RankThreeFourSmallFast245212 (quick)
open OMA.RankThreeMiddle245212 (joinEvery)
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
private theorem b1 : every 1 16 (line 736590 45384 425920 7 12)=true := by decide +kernel
private theorem b17 : every 17 32 (line 736590 45384 425920 7 12)=true := by decide +kernel
theorem certificate : atom 11 7 3=true := by
  apply row_high (h:=21296) (A:=736590) (S:=45384) (T:=425920) (R:=12) (B:=32) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact (joinEvery b1 b17)
end OMA.SixteenAt11E3P7

/- One exact initial prime power, with the last prime unrestricted. -/
namespace OMA.SixteenAt11E4P7
open OMA.RankThreeEightMoving245212 (line low)
open OMA.RankThreeSixteenMoving245212 OMA.CofactorEulerPair245212
open OMA.RankThreeFourSmallFast245212 (quick)
open OMA.RankThreeMiddle245212 (joinEvery)
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
private theorem b1 : every 1 16 (line 10180035 499255 5856400 7 12)=true := by decide +kernel
private theorem b17 : every 17 20 (line 10180035 499255 5856400 7 12)=true := by decide +kernel
theorem certificate : atom 11 7 4=true := by
  apply row_high (h:=234256) (A:=10180035) (S:=499255) (T:=5856400) (R:=12) (B:=20) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact (joinEvery b1 b17)
end OMA.SixteenAt11E4P7

/- One exact initial prime power, with the last prime unrestricted. -/
namespace OMA.SixteenAt11E5P7
open OMA.RankThreeEightMoving245212 (line low)
open OMA.RankThreeSixteenMoving245212 OMA.CofactorEulerPair245212
open OMA.RankThreeFourSmallFast245212 (quick)
open OMA.RankThreeMiddle245212 (joinEvery)
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
private theorem b1 : every 1 16 (line 134833509 5491836 77304480 7 12)=true := by decide +kernel
theorem certificate : atom 11 7 5=true := by
  apply row_high (h:=2576816) (A:=134833509) (S:=5491836) (T:=77304480) (R:=12) (B:=16) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact b1
end OMA.SixteenAt11E5P7

/- One exact initial prime power, with the last prime unrestricted. -/
namespace OMA.SixteenAt11E6P7
open OMA.RankThreeEightMoving245212 (line low)
open OMA.RankThreeSixteenMoving245212 OMA.CofactorEulerPair245212
open OMA.RankThreeFourSmallFast245212 (quick)
open OMA.RankThreeMiddle245212 (joinEvery)
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
private theorem b1 : every 1 14 (line 1734553092 60410227 992074160 7 12)=true := by decide +kernel
theorem certificate : atom 11 7 6=true := by
  apply row_high (h:=28344976) (A:=1734553092) (S:=60410227) (T:=992074160) (R:=12) (B:=14) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact b1
end OMA.SixteenAt11E6P7

namespace OMA.SixteenShort11P7
open OMA.CofactorEulerPair245212 OMA.RankThreeSixteenMoving245212
open OMA.RankThreeMiddle245212 (joinEvery)
theorem rows : every 1 6 (atom 11 7)=true := (joinEvery (joinEvery (single (f:=atom 11 7) OMA.SixteenAt11E1P7.certificate) (joinEvery (single (f:=atom 11 7) OMA.SixteenAt11E2P7.certificate) (single (f:=atom 11 7) OMA.SixteenAt11E3P7.certificate))) (joinEvery (single (f:=atom 11 7) OMA.SixteenAt11E4P7.certificate) (joinEvery (single (f:=atom 11 7) OMA.SixteenAt11E5P7.certificate) (single (f:=atom 11 7) OMA.SixteenAt11E6P7.certificate))))
end OMA.SixteenShort11P7
namespace OMA.SixteenMoving7P11
open OMA.RankThreeSixteenMoving245212
open scoped ArithmeticFunction.sigma
theorem exclude {r a b c : ℕ} (pr : r.Prime) (large : 11<r) (ap : 0<a) (bp : 0<b) (cp : 0<c) :
    OeisA245212.a (16*7^a*11^b*r^c)≠(σ 1 (16*7^a*11^b*r^c):ℤ) :=
  close (l:=7) (u:=7) (by decide) (by decide) pr (by decide) (by decide) large ap bp cp (by decide +kernel)
    OMA.SixteenShort7P11.rows OMA.SixteenShort11P7.rows
end OMA.SixteenMoving7P11

end

section

/- Exclusion of one unrestricted terminal-prime family at dyadic order four. -/
/- One exact initial prime power, with the last prime unrestricted. -/
namespace OMA.SixteenAt7E1P13
open OMA.RankThreeEightMoving245212 (line low)
open OMA.RankThreeSixteenMoving245212 OMA.CofactorEulerPair245212
open OMA.RankThreeFourSmallFast245212 (quick)
open OMA.RankThreeMiddle245212 (joinEvery)
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
private theorem b14 : every 14 15 (quick 112 1935 248 1120 13)=true := by decide +kernel
theorem certificate : atom 7 13 1=true := by
  apply row_low (h:=112) (A:=1935) (S:=248) (T:=1120) (R:=14) (Q:=15) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  rw [low,if_pos (by decide : 15≤14+128)]
  exact b14
end OMA.SixteenAt7E1P13

/- One exact initial prime power, with the last prime unrestricted. -/
namespace OMA.SixteenAt7E2P13
open OMA.RankThreeEightMoving245212 (line low)
open OMA.RankThreeSixteenMoving245212 OMA.CofactorEulerPair245212
open OMA.RankThreeFourSmallFast245212 (quick)
open OMA.RankThreeMiddle245212 (joinEvery)
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
private theorem b14 : every 14 26 (quick 784 20898 1767 11760 13)=true := by decide +kernel
theorem certificate : atom 7 13 2=true := by
  apply row_low (h:=784) (A:=20898) (S:=1767) (T:=11760) (R:=14) (Q:=26) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  rw [low,if_pos (by decide : 26≤14+128)]
  exact b14
end OMA.SixteenAt7E2P13

/- One exact initial prime power, with the last prime unrestricted. -/
namespace OMA.SixteenAt7E3P13
open OMA.RankThreeEightMoving245212 (line low)
open OMA.RankThreeSixteenMoving245212 OMA.CofactorEulerPair245212
open OMA.RankThreeFourSmallFast245212 (quick)
open OMA.RankThreeMiddle245212 (joinEvery)
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
private theorem b14 : every 14 29 (quick 5488 197886 12400 109760 13)=true := by decide +kernel
private theorem b30 : every 30 42 (quick 5488 197886 12400 109760 13)=true := by decide +kernel
theorem certificate : atom 7 13 3=true := by
  apply row_low (h:=5488) (A:=197886) (S:=12400) (T:=109760) (R:=14) (Q:=42) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  rw [low,if_pos (by decide : 42≤14+128)]
  exact (joinEvery b14 b30)
end OMA.SixteenAt7E3P13

/- One exact initial prime power, with the last prime unrestricted. -/
namespace OMA.SixteenAt7E4P13
open OMA.RankThreeEightMoving245212 (line low)
open OMA.RankThreeSixteenMoving245212 OMA.CofactorEulerPair245212
open OMA.RankThreeFourSmallFast245212 (quick)
open OMA.RankThreeMiddle245212 (joinEvery)
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
private theorem b14 : every 14 29 (quick 38416 1746531 86831 960400 13)=true := by decide +kernel
private theorem b30 : every 30 45 (quick 38416 1746531 86831 960400 13)=true := by decide +kernel
private theorem b46 : every 46 61 (quick 38416 1746531 86831 960400 13)=true := by decide +kernel
private theorem b62 : every 62 66 (quick 38416 1746531 86831 960400 13)=true := by decide +kernel
theorem certificate : atom 7 13 4=true := by
  apply row_low (h:=38416) (A:=1746531) (S:=86831) (T:=960400) (R:=14) (Q:=66) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  rw [low,if_pos (by decide : 66≤14+128)]
  exact (joinEvery (joinEvery b14 b30) (joinEvery b46 b62))
end OMA.SixteenAt7E4P13

/- One exact initial prime power, with the last prime unrestricted. -/
namespace OMA.SixteenAt7E5P13
open OMA.RankThreeEightMoving245212 (line low)
open OMA.RankThreeSixteenMoving245212 OMA.CofactorEulerPair245212
open OMA.RankThreeFourSmallFast245212 (quick)
open OMA.RankThreeMiddle245212 (joinEvery)
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
private theorem b14 : every 14 29 (quick 268912 14755149 607848 8067360 13)=true := by decide +kernel
private theorem b30 : every 30 45 (quick 268912 14755149 607848 8067360 13)=true := by decide +kernel
private theorem b46 : every 46 61 (quick 268912 14755149 607848 8067360 13)=true := by decide +kernel
private theorem b62 : every 62 77 (quick 268912 14755149 607848 8067360 13)=true := by decide +kernel
private theorem b78 : every 78 93 (quick 268912 14755149 607848 8067360 13)=true := by decide +kernel
private theorem b94 : every 94 107 (quick 268912 14755149 607848 8067360 13)=true := by decide +kernel
theorem certificate : atom 7 13 5=true := by
  apply row_low (h:=268912) (A:=14755149) (S:=607848) (T:=8067360) (R:=14) (Q:=107) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  rw [low,if_pos (by decide : 107≤14+128)]
  exact (joinEvery (joinEvery b14 (joinEvery b30 b46)) (joinEvery b62 (joinEvery b78 b94)))
end OMA.SixteenAt7E5P13

/- One exact initial prime power, with the last prime unrestricted. -/
namespace OMA.SixteenAt7E6P13
open OMA.RankThreeEightMoving245212 (line low)
open OMA.RankThreeSixteenMoving245212 OMA.CofactorEulerPair245212
open OMA.RankThreeFourSmallFast245212 (quick)
open OMA.RankThreeMiddle245212 (joinEvery)
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
private theorem b1 : every 1 16 (line 120992196 4254967 65883440 13 14)=true := by decide +kernel
private theorem b17 : every 17 32 (line 120992196 4254967 65883440 13 14)=true := by decide +kernel
private theorem b33 : every 33 48 (line 120992196 4254967 65883440 13 14)=true := by decide +kernel
private theorem b49 : every 49 54 (line 120992196 4254967 65883440 13 14)=true := by decide +kernel
theorem certificate : atom 7 13 6=true := by
  apply row_low (h:=1882384) (A:=120992196) (S:=4254967) (T:=65883440) (R:=14) (Q:=190) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  rw [low,if_neg (by decide : ¬190≤14+128),Bool.and_eq_true]
  rw [show OMA.RankThreeFourSmallNear245212.nearCap 1882384 120992196 4254967 13 190=54 by decide +kernel]
  exact ⟨by decide +kernel,(joinEvery (joinEvery b1 b17) (joinEvery b33 b49))⟩
end OMA.SixteenAt7E6P13

/- One exact initial prime power, with the last prime unrestricted. -/
namespace OMA.SixteenAt7E7P13
open OMA.RankThreeEightMoving245212 (line low)
open OMA.RankThreeSixteenMoving245212 OMA.CofactorEulerPair245212
open OMA.RankThreeFourSmallFast245212 (quick)
open OMA.RankThreeMiddle245212 (joinEvery)
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
private theorem b1 : every 1 16 (line 970888572 29784800 527067520 13 14)=true := by decide +kernel
private theorem b17 : every 17 32 (line 970888572 29784800 527067520 13 14)=true := by decide +kernel
private theorem b33 : every 33 48 (line 970888572 29784800 527067520 13 14)=true := by decide +kernel
private theorem b49 : every 49 57 (line 970888572 29784800 527067520 13 14)=true := by decide +kernel
theorem certificate : atom 7 13 7=true := by
  apply row_low (h:=13176688) (A:=970888572) (S:=29784800) (T:=527067520) (R:=14) (Q:=450) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  rw [low,if_neg (by decide : ¬450≤14+128),Bool.and_eq_true]
  rw [show OMA.RankThreeFourSmallNear245212.nearCap 13176688 970888572 29784800 13 450=57 by decide +kernel]
  exact ⟨by decide +kernel,(joinEvery (joinEvery b1 b17) (joinEvery b33 b49))⟩
end OMA.SixteenAt7E7P13

/- One exact initial prime power, with the last prime unrestricted. -/
namespace OMA.SixteenAt7E8P13
open OMA.RankThreeEightMoving245212 (line low)
open OMA.RankThreeSixteenMoving245212 OMA.CofactorEulerPair245212
open OMA.RankThreeFourSmallFast245212 (quick)
open OMA.RankThreeMiddle245212 (joinEvery)
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
private theorem b1 : every 1 16 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b17 : every 17 32 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b33 : every 33 48 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b49 : every 49 64 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b65 : every 65 80 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b81 : every 81 96 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b97 : every 97 112 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b113 : every 113 128 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b129 : every 129 144 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b145 : every 145 160 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b161 : every 161 176 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b177 : every 177 192 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b193 : every 193 208 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b209 : every 209 224 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b225 : every 225 240 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b241 : every 241 256 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b257 : every 257 272 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b273 : every 273 288 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b289 : every 289 304 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b305 : every 305 320 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b321 : every 321 336 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b337 : every 337 352 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b353 : every 353 368 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b369 : every 369 384 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b385 : every 385 400 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b401 : every 401 416 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b417 : every 417 432 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b433 : every 433 448 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b449 : every 449 464 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b465 : every 465 480 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b481 : every 481 496 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b497 : every 497 512 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b513 : every 513 528 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b529 : every 529 544 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b545 : every 545 560 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b561 : every 561 576 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b577 : every 577 592 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b593 : every 593 608 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b609 : every 609 624 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b625 : every 625 640 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b641 : every 641 656 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b657 : every 657 672 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b673 : every 673 688 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b689 : every 689 704 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b705 : every 705 720 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b721 : every 721 736 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b737 : every 737 752 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b753 : every 753 768 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b769 : every 769 784 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b785 : every 785 800 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b801 : every 801 816 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b817 : every 817 832 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b833 : every 833 848 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b849 : every 849 864 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b865 : every 865 880 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b881 : every 881 896 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b897 : every 897 912 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b913 : every 913 928 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b929 : every 929 944 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b945 : every 945 960 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b961 : every 961 976 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b977 : every 977 992 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b993 : every 993 1008 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b1009 : every 1009 1024 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b1025 : every 1025 1040 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b1041 : every 1041 1056 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b1057 : every 1057 1072 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b1073 : every 1073 1088 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
private theorem b1089 : every 1089 1100 (line 7663822533 208493631 4150656720 13 14)=true := by decide +kernel
theorem certificate : atom 7 13 8=true := by
  apply row_high (h:=92236816) (A:=7663822533) (S:=208493631) (T:=4150656720) (R:=14) (B:=1100) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact (joinEvery (joinEvery (joinEvery (joinEvery (joinEvery (joinEvery b1 b17) (joinEvery b33 b49)) (joinEvery (joinEvery b65 b81) (joinEvery b97 b113))) (joinEvery (joinEvery (joinEvery b129 b145) (joinEvery b161 b177)) (joinEvery (joinEvery b193 b209) (joinEvery b225 (joinEvery b241 b257))))) (joinEvery (joinEvery (joinEvery (joinEvery b273 b289) (joinEvery b305 b321)) (joinEvery (joinEvery b337 b353) (joinEvery b369 b385))) (joinEvery (joinEvery (joinEvery b401 b417) (joinEvery b433 b449)) (joinEvery (joinEvery b465 b481) (joinEvery b497 (joinEvery b513 b529)))))) (joinEvery (joinEvery (joinEvery (joinEvery (joinEvery b545 b561) (joinEvery b577 b593)) (joinEvery (joinEvery b609 b625) (joinEvery b641 b657))) (joinEvery (joinEvery (joinEvery b673 b689) (joinEvery b705 b721)) (joinEvery (joinEvery b737 b753) (joinEvery b769 (joinEvery b785 b801))))) (joinEvery (joinEvery (joinEvery (joinEvery b817 b833) (joinEvery b849 b865)) (joinEvery (joinEvery b881 b897) (joinEvery b913 (joinEvery b929 b945)))) (joinEvery (joinEvery (joinEvery b961 b977) (joinEvery b993 b1009)) (joinEvery (joinEvery b1025 b1041) (joinEvery b1057 (joinEvery b1073 b1089)))))))
end OMA.SixteenAt7E8P13

/- One exact initial prime power, with the last prime unrestricted. -/
namespace OMA.SixteenAt7E9P13
open OMA.RankThreeEightMoving245212 (line low)
open OMA.RankThreeSixteenMoving245212 OMA.CofactorEulerPair245212
open OMA.RankThreeFourSmallFast245212 (quick)
open OMA.RankThreeMiddle245212 (joinEvery)
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
private theorem b1 : every 1 16 (line 59719975563 1459455448 32282885600 13 14)=true := by decide +kernel
private theorem b17 : every 17 32 (line 59719975563 1459455448 32282885600 13 14)=true := by decide +kernel
private theorem b33 : every 33 48 (line 59719975563 1459455448 32282885600 13 14)=true := by decide +kernel
private theorem b49 : every 49 64 (line 59719975563 1459455448 32282885600 13 14)=true := by decide +kernel
private theorem b65 : every 65 76 (line 59719975563 1459455448 32282885600 13 14)=true := by decide +kernel
theorem certificate : atom 7 13 9=true := by
  apply row_high (h:=645657712) (A:=59719975563) (S:=1459455448) (T:=32282885600) (R:=14) (B:=76) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact (joinEvery (joinEvery b1 b17) (joinEvery b33 (joinEvery b49 b65)))
end OMA.SixteenAt7E9P13

/- One exact initial prime power, with the last prime unrestricted. -/
namespace OMA.SixteenAt7E10P13
open OMA.RankThreeEightMoving245212 (line low)
open OMA.RankThreeSixteenMoving245212 OMA.CofactorEulerPair245212
open OMA.RankThreeFourSmallFast245212 (quick)
open OMA.RankThreeMiddle245212 (joinEvery)
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
private theorem b1 : every 1 16 (line 460552353894 10216188167 248578219120 13 14)=true := by decide +kernel
private theorem b17 : every 17 32 (line 460552353894 10216188167 248578219120 13 14)=true := by decide +kernel
private theorem b33 : every 33 43 (line 460552353894 10216188167 248578219120 13 14)=true := by decide +kernel
theorem certificate : atom 7 13 10=true := by
  apply row_high (h:=4519603984) (A:=460552353894) (S:=10216188167) (T:=248578219120) (R:=14) (B:=43) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact (joinEvery b1 (joinEvery b17 b33))
end OMA.SixteenAt7E10P13

/- One exact initial prime power, with the last prime unrestricted. -/
namespace OMA.SixteenAt7E11P13
open OMA.RankThreeEightMoving245212 (line low)
open OMA.RankThreeSixteenMoving245212 OMA.CofactorEulerPair245212
open OMA.RankThreeFourSmallFast245212 (quick)
open OMA.RankThreeMiddle245212 (joinEvery)
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
private theorem b1 : every 1 16 (line 3521454152058 71513317200 1898233673280 13 14)=true := by decide +kernel
private theorem b17 : every 17 31 (line 3521454152058 71513317200 1898233673280 13 14)=true := by decide +kernel
theorem certificate : atom 7 13 11=true := by
  apply row_high (h:=31637227888) (A:=3521454152058) (S:=71513317200) (T:=1898233673280) (R:=14) (B:=31) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact (joinEvery b1 b17)
end OMA.SixteenAt7E11P13

/- One exact initial prime power, with the last prime unrestricted. -/
namespace OMA.SixteenAt7E12P13
open OMA.RankThreeEightMoving245212 (line low)
open OMA.RankThreeSixteenMoving245212 OMA.CofactorEulerPair245212
open OMA.RankThreeFourSmallFast245212 (quick)
open OMA.RankThreeMiddle245212 (joinEvery)
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
private theorem b1 : every 1 16 (line 26733292788135 500593220431 14394938689040 13 14)=true := by decide +kernel
private theorem b17 : every 17 26 (line 26733292788135 500593220431 14394938689040 13 14)=true := by decide +kernel
theorem certificate : atom 7 13 12=true := by
  apply row_high (h:=221460595216) (A:=26733292788135) (S:=500593220431) (T:=14394938689040) (R:=14) (B:=26) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact (joinEvery b1 b17)
end OMA.SixteenAt7E12P13

namespace OMA.SixteenShort7P13
open OMA.CofactorEulerPair245212 OMA.RankThreeSixteenMoving245212
open OMA.RankThreeMiddle245212 (joinEvery)
theorem rows : every 1 12 (atom 7 13)=true := (joinEvery (joinEvery (joinEvery (single (f:=atom 7 13) OMA.SixteenAt7E1P13.certificate) (joinEvery (single (f:=atom 7 13) OMA.SixteenAt7E2P13.certificate) (single (f:=atom 7 13) OMA.SixteenAt7E3P13.certificate))) (joinEvery (single (f:=atom 7 13) OMA.SixteenAt7E4P13.certificate) (joinEvery (single (f:=atom 7 13) OMA.SixteenAt7E5P13.certificate) (single (f:=atom 7 13) OMA.SixteenAt7E6P13.certificate)))) (joinEvery (joinEvery (single (f:=atom 7 13) OMA.SixteenAt7E7P13.certificate) (joinEvery (single (f:=atom 7 13) OMA.SixteenAt7E8P13.certificate) (single (f:=atom 7 13) OMA.SixteenAt7E9P13.certificate))) (joinEvery (single (f:=atom 7 13) OMA.SixteenAt7E10P13.certificate) (joinEvery (single (f:=atom 7 13) OMA.SixteenAt7E11P13.certificate) (single (f:=atom 7 13) OMA.SixteenAt7E12P13.certificate)))))
end OMA.SixteenShort7P13
/- One exact initial prime power, with the last prime unrestricted. -/
namespace OMA.SixteenAt13E1P7
open OMA.RankThreeEightMoving245212 (line low)
open OMA.RankThreeSixteenMoving245212 OMA.CofactorEulerPair245212
open OMA.RankThreeFourSmallFast245212 (quick)
open OMA.RankThreeMiddle245212 (joinEvery)
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
private theorem b14 : every 14 29 (quick 208 3483 434 2080 7)=true := by decide +kernel
private theorem b30 : every 30 43 (quick 208 3483 434 2080 7)=true := by decide +kernel
theorem certificate : atom 13 7 1=true := by
  apply row_low (h:=208) (A:=3483) (S:=434) (T:=2080) (R:=14) (Q:=43) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  rw [low,if_pos (by decide : 43≤14+128)]
  exact (joinEvery b14 b30)
end OMA.SixteenAt13E1P7

/- One exact initial prime power, with the last prime unrestricted. -/
namespace OMA.SixteenAt13E2P7
open OMA.RankThreeEightMoving245212 (line low)
open OMA.RankThreeSixteenMoving245212 OMA.CofactorEulerPair245212
open OMA.RankThreeFourSmallFast245212 (quick)
open OMA.RankThreeMiddle245212 (joinEvery)
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
private theorem b14 : every 14 29 (quick 2704 68886 5673 40560 7)=true := by decide +kernel
private theorem b30 : every 30 45 (quick 2704 68886 5673 40560 7)=true := by decide +kernel
private theorem b46 : every 46 61 (quick 2704 68886 5673 40560 7)=true := by decide +kernel
private theorem b62 : every 62 77 (quick 2704 68886 5673 40560 7)=true := by decide +kernel
private theorem b78 : every 78 93 (quick 2704 68886 5673 40560 7)=true := by decide +kernel
private theorem b94 : every 94 107 (quick 2704 68886 5673 40560 7)=true := by decide +kernel
theorem certificate : atom 13 7 2=true := by
  apply row_low (h:=2704) (A:=68886) (S:=5673) (T:=40560) (R:=14) (Q:=107) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  rw [low,if_pos (by decide : 107≤14+128)]
  exact (joinEvery (joinEvery b14 (joinEvery b30 b46)) (joinEvery b62 (joinEvery b78 b94)))
end OMA.SixteenAt13E2P7

/- One exact initial prime power, with the last prime unrestricted. -/
namespace OMA.SixteenAt13E3P7
open OMA.RankThreeEightMoving245212 (line low)
open OMA.RankThreeSixteenMoving245212 OMA.CofactorEulerPair245212
open OMA.RankThreeFourSmallFast245212 (quick)
open OMA.RankThreeMiddle245212 (joinEvery)
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
private theorem b1 : every 1 16 (line 1202538 73780 703040 7 14)=true := by decide +kernel
private theorem b17 : every 17 32 (line 1202538 73780 703040 7 14)=true := by decide +kernel
private theorem b33 : every 33 48 (line 1202538 73780 703040 7 14)=true := by decide +kernel
private theorem b49 : every 49 64 (line 1202538 73780 703040 7 14)=true := by decide +kernel
private theorem b65 : every 65 80 (line 1202538 73780 703040 7 14)=true := by decide +kernel
private theorem b81 : every 81 86 (line 1202538 73780 703040 7 14)=true := by decide +kernel
theorem certificate : atom 13 7 3=true := by
  apply row_low (h:=35152) (A:=1202538) (S:=73780) (T:=703040) (R:=14) (Q:=450) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  rw [low,if_neg (by decide : ¬450≤14+128),Bool.and_eq_true]
  rw [show OMA.RankThreeFourSmallNear245212.nearCap 35152 1202538 73780 7 450=86 by decide +kernel]
  exact ⟨by decide +kernel,(joinEvery (joinEvery b1 (joinEvery b17 b33)) (joinEvery b49 (joinEvery b65 b81)))⟩
end OMA.SixteenAt13E3P7

/- One exact initial prime power, with the last prime unrestricted. -/
namespace OMA.SixteenAt13E4P7
open OMA.RankThreeEightMoving245212 (line low)
open OMA.RankThreeSixteenMoving245212 OMA.CofactorEulerPair245212
open OMA.RankThreeFourSmallFast245212 (quick)
open OMA.RankThreeMiddle245212 (joinEvery)
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
private theorem b1 : every 1 16 (line 19624383 959171 11424400 7 14)=true := by decide +kernel
private theorem b17 : every 17 32 (line 19624383 959171 11424400 7 14)=true := by decide +kernel
private theorem b33 : every 33 48 (line 19624383 959171 11424400 7 14)=true := by decide +kernel
private theorem b49 : every 49 64 (line 19624383 959171 11424400 7 14)=true := by decide +kernel
private theorem b65 : every 65 80 (line 19624383 959171 11424400 7 14)=true := by decide +kernel
private theorem b81 : every 81 96 (line 19624383 959171 11424400 7 14)=true := by decide +kernel
private theorem b97 : every 97 112 (line 19624383 959171 11424400 7 14)=true := by decide +kernel
private theorem b113 : every 113 128 (line 19624383 959171 11424400 7 14)=true := by decide +kernel
private theorem b129 : every 129 141 (line 19624383 959171 11424400 7 14)=true := by decide +kernel
theorem certificate : atom 13 7 4=true := by
  apply row_high (h:=456976) (A:=19624383) (S:=959171) (T:=11424400) (R:=14) (B:=141) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact (joinEvery (joinEvery (joinEvery b1 b17) (joinEvery b33 b49)) (joinEvery (joinEvery b65 b81) (joinEvery b97 (joinEvery b113 b129))))
end OMA.SixteenAt13E4P7

/- One exact initial prime power, with the last prime unrestricted. -/
namespace OMA.SixteenAt13E5P7
open OMA.RankThreeEightMoving245212 (line low)
open OMA.RankThreeSixteenMoving245212 OMA.CofactorEulerPair245212
open OMA.RankThreeFourSmallFast245212 (quick)
open OMA.RankThreeMiddle245212 (joinEvery)
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
private theorem b1 : every 1 16 (line 307005165 12469254 178220640 7 14)=true := by decide +kernel
private theorem b17 : every 17 32 (line 307005165 12469254 178220640 7 14)=true := by decide +kernel
private theorem b33 : every 33 48 (line 307005165 12469254 178220640 7 14)=true := by decide +kernel
private theorem b49 : every 49 59 (line 307005165 12469254 178220640 7 14)=true := by decide +kernel
theorem certificate : atom 13 7 5=true := by
  apply row_high (h:=5940688) (A:=307005165) (S:=12469254) (T:=178220640) (R:=14) (B:=59) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact (joinEvery (joinEvery b1 b17) (joinEvery b33 b49))
end OMA.SixteenAt13E5P7

/- One exact initial prime power, with the last prime unrestricted. -/
namespace OMA.SixteenAt13E6P7
open OMA.RankThreeEightMoving245212 (line low)
open OMA.RankThreeSixteenMoving245212 OMA.CofactorEulerPair245212
open OMA.RankThreeFourSmallFast245212 (quick)
open OMA.RankThreeMiddle245212 (joinEvery)
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
private theorem b1 : every 1 16 (line 4665613692 162100333 2703013040 7 14)=true := by decide +kernel
private theorem b17 : every 17 32 (line 4665613692 162100333 2703013040 7 14)=true := by decide +kernel
private theorem b33 : every 33 41 (line 4665613692 162100333 2703013040 7 14)=true := by decide +kernel
theorem certificate : atom 13 7 6=true := by
  apply row_high (h:=77228944) (A:=4665613692) (S:=162100333) (T:=2703013040) (R:=14) (B:=41) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact (joinEvery b1 (joinEvery b17 b33))
end OMA.SixteenAt13E6P7

/- One exact initial prime power, with the last prime unrestricted. -/
namespace OMA.SixteenAt13E7P7
open OMA.RankThreeEightMoving245212 (line low)
open OMA.RankThreeSixteenMoving245212 OMA.CofactorEulerPair245212
open OMA.RankThreeFourSmallFast245212 (quick)
open OMA.RankThreeMiddle245212 (joinEvery)
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
private theorem b1 : every 1 16 (line 69422083236 2107304360 40159050880 7 14)=true := by decide +kernel
private theorem b17 : every 17 32 (line 69422083236 2107304360 40159050880 7 14)=true := by decide +kernel
private theorem b33 : every 33 34 (line 69422083236 2107304360 40159050880 7 14)=true := by decide +kernel
theorem certificate : atom 13 7 7=true := by
  apply row_high (h:=1003976272) (A:=69422083236) (S:=2107304360) (T:=40159050880) (R:=14) (B:=34) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact (joinEvery b1 (joinEvery b17 b33))
end OMA.SixteenAt13E7P7

/- One exact initial prime power, with the last prime unrestricted. -/
namespace OMA.SixteenAt13E8P7
open OMA.RankThreeEightMoving245212 (line low)
open OMA.RankThreeSixteenMoving245212 OMA.CofactorEulerPair245212
open OMA.RankThreeFourSmallFast245212 (quick)
open OMA.RankThreeMiddle245212 (joinEvery)
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
private theorem b1 : every 1 16 (line 1016485450317 27394956711 587326119120 7 14)=true := by decide +kernel
private theorem b17 : every 17 30 (line 1016485450317 27394956711 587326119120 7 14)=true := by decide +kernel
theorem certificate : atom 13 7 8=true := by
  apply row_high (h:=13051691536) (A:=1016485450317) (S:=27394956711) (T:=587326119120) (R:=14) (B:=30) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact (joinEvery b1 b17)
end OMA.SixteenAt13E8P7

/- One exact initial prime power, with the last prime unrestricted. -/
namespace OMA.SixteenAt13E9P7
open OMA.RankThreeEightMoving245212 (line low)
open OMA.RankThreeSixteenMoving245212 OMA.CofactorEulerPair245212
open OMA.RankThreeFourSmallFast245212 (quick)
open OMA.RankThreeMiddle245212 (joinEvery)
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
private theorem b1 : every 1 16 (line 14696289641487 356134437274 8483599498400 7 14)=true := by decide +kernel
private theorem b17 : every 17 27 (line 14696289641487 356134437274 8483599498400 7 14)=true := by decide +kernel
theorem certificate : atom 13 7 9=true := by
  apply row_high (h:=169671989968) (A:=14696289641487) (S:=356134437274) (T:=8483599498400) (R:=14) (B:=27) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact (joinEvery b1 b17)
end OMA.SixteenAt13E9P7

/- One exact initial prime power, with the last prime unrestricted. -/
namespace OMA.SixteenAt13E10P7
open OMA.RankThreeEightMoving245212 (line low)
open OMA.RankThreeSixteenMoving245212 OMA.CofactorEulerPair245212
open OMA.RankThreeFourSmallFast245212 (quick)
open OMA.RankThreeMiddle245212 (joinEvery)
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
private theorem b1 : every 1 16 (line 210317489575218 4629747684593 121315472827120 7 14)=true := by decide +kernel
private theorem b17 : every 17 25 (line 210317489575218 4629747684593 121315472827120 7 14)=true := by decide +kernel
theorem certificate : atom 13 7 10=true := by
  apply row_high (h:=2205735869584) (A:=210317489575218) (S:=4629747684593) (T:=121315472827120) (R:=14) (B:=25) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact (joinEvery b1 b17)
end OMA.SixteenAt13E10P7

/- One exact initial prime power, with the last prime unrestricted. -/
namespace OMA.SixteenAt13E11P7
open OMA.RankThreeEightMoving245212 (line low)
open OMA.RankThreeSixteenMoving245212 OMA.CofactorEulerPair245212
open OMA.RankThreeFourSmallFast245212 (quick)
open OMA.RankThreeMiddle245212 (joinEvery)
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
private theorem b1 : every 1 16 (line 2984581779544494 60186719899740 1720473978275520 7 14)=true := by decide +kernel
private theorem b17 : every 17 24 (line 2984581779544494 60186719899740 1720473978275520 7 14)=true := by decide +kernel
theorem certificate : atom 13 7 11=true := by
  apply row_high (h:=28674566304592) (A:=2984581779544494) (S:=60186719899740) (T:=1720473978275520) (R:=14) (B:=24) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact (joinEvery b1 b17)
end OMA.SixteenAt13E11P7

/- One exact initial prime power, with the last prime unrestricted. -/
namespace OMA.SixteenAt13E12P7
open OMA.RankThreeEightMoving245212 (line low)
open OMA.RankThreeSixteenMoving245212 OMA.CofactorEulerPair245212
open OMA.RankThreeFourSmallFast245212 (quick)
open OMA.RankThreeMiddle245212 (joinEvery)
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
private theorem b1 : every 1 16 (line 42055470529945131 782427358696651 24230008527380240 7 14)=true := by decide +kernel
private theorem b17 : every 17 23 (line 42055470529945131 782427358696651 24230008527380240 7 14)=true := by decide +kernel
theorem certificate : atom 13 7 12=true := by
  apply row_high (h:=372769361959696) (A:=42055470529945131) (S:=782427358696651) (T:=24230008527380240) (R:=14) (B:=23) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact (joinEvery b1 b17)
end OMA.SixteenAt13E12P7

namespace OMA.SixteenShort13P7
open OMA.CofactorEulerPair245212 OMA.RankThreeSixteenMoving245212
open OMA.RankThreeMiddle245212 (joinEvery)
theorem rows : every 1 12 (atom 13 7)=true := (joinEvery (joinEvery (joinEvery (single (f:=atom 13 7) OMA.SixteenAt13E1P7.certificate) (joinEvery (single (f:=atom 13 7) OMA.SixteenAt13E2P7.certificate) (single (f:=atom 13 7) OMA.SixteenAt13E3P7.certificate))) (joinEvery (single (f:=atom 13 7) OMA.SixteenAt13E4P7.certificate) (joinEvery (single (f:=atom 13 7) OMA.SixteenAt13E5P7.certificate) (single (f:=atom 13 7) OMA.SixteenAt13E6P7.certificate)))) (joinEvery (joinEvery (single (f:=atom 13 7) OMA.SixteenAt13E7P7.certificate) (joinEvery (single (f:=atom 13 7) OMA.SixteenAt13E8P7.certificate) (single (f:=atom 13 7) OMA.SixteenAt13E9P7.certificate))) (joinEvery (single (f:=atom 13 7) OMA.SixteenAt13E10P7.certificate) (joinEvery (single (f:=atom 13 7) OMA.SixteenAt13E11P7.certificate) (single (f:=atom 13 7) OMA.SixteenAt13E12P7.certificate)))))
end OMA.SixteenShort13P7
namespace OMA.SixteenMoving7P13
open OMA.RankThreeSixteenMoving245212
open scoped ArithmeticFunction.sigma
theorem exclude {r a b c : ℕ} (pr : r.Prime) (large : 13<r) (ap : 0<a) (bp : 0<b) (cp : 0<c) :
    OeisA245212.a (16*7^a*13^b*r^c)≠(σ 1 (16*7^a*13^b*r^c):ℤ) :=
  close (l:=13) (u:=13) (by decide) (by decide) pr (by decide) (by decide) large ap bp cp (by decide +kernel)
    OMA.SixteenShort7P13.rows OMA.SixteenShort13P7.rows
end OMA.SixteenMoving7P13

end

section

/- Trial division only through the square root for kernel certificates.
Mathlib's compiler accelerates decidablePrime, but kernel reduction uses
the original decidable instance. This Boolean has the same meaning in both. -/
namespace OMA.KernelPrimeWindow245212
open Nat

def trial (n : ℕ) := decide (2≤n) && (List.range' 2 (n.sqrt-1)).all (fun d=>decide (n%d≠0))

theorem correct (n : ℕ) : trial n=true ↔ n.Prime := by
  rw [Nat.prime_def_le_sqrt]
  simp only [trial,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true]
  refine and_congr_right fun _=>?_
  constructor
  · intro test d lo hi divides
    exact test d (List.mem_range'_1.mpr ⟨lo,by omega⟩) (Nat.mod_eq_zero_of_dvd divides)
  · intro test d mem zero
    obtain ⟨lo,hi⟩:=List.mem_range'_1.mp mem
    exact test d lo (by omega) (Nat.dvd_of_mod_eq_zero zero)

end OMA.KernelPrimeWindow245212

end

section

/- Unrestricted-exponent checker for the finite supports. Each oriented
table first screens the terminal divisibility in small residue classes. -/
namespace OMA.SixteenTable245212
open Nat Finset ArithmeticFunction OMA.Smooth245212 OMA.Large245212
open OMA.CofactorEulerPair245212 OMA.RankThreeSixteenFixed245212
open scoped ArithmeticFunction.sigma
open OMA.CofactorEulerPair245212 (checked)
open OMA.Large245212 (moments)

def last (p q A S T e : ℕ) :=
  let w:=A*wt p e
  let y:=S*sig p e
  let t:=T*OMA.Large245212.tax p e
  OMA.RankThreeLast245212.reject q w y t (OMA.RankThreeLast245212.len q w y t)

theorem last_sound {h p q e d : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime) (oq : q≠2)
    (pc : h.Coprime p) (qc : h.Coprime q) (ne : p≠q) (dp : 0<d)
    (sol : OeisA245212.a (h*p^e*q^d)=(σ 1 (h*p^e*q^d):ℤ)) :
    last p q (W h) (σ 1 h) (h*σ 0 h) e=false := by
  have pos := hp.pos
  have cop:=qc.mul_left (((Nat.coprime_primes hp hq).mpr ne).pow_left e)
  have size:=OMA.RankThreeLast245212.length_eq (by positivity) hq oq cop sol
  have test:=OMA.RankThreeLast245212.reject_sound (by positivity) hq oq cop dp
    (show d≤OMA.RankThreeLast245212.len q (W (h*p^e)) (σ 1 (h*p^e)) (h*p^e*σ 0 (h*p^e)) by omega) sol
  obtain ⟨y,w⟩:=OMA.Large245212.moments hp e
  rw [w_mult.map_mul_of_coprime (pc.pow_right e), isMultiplicative_sigma.map_mul_of_coprime (pc.pow_right e),
    isMultiplicative_sigma.map_mul_of_coprime (pc.pow_right e), sigma_zero_apply_prime_pow hp] at test
  simpa only [last,w,y,OMA.Large245212.tax,mul_assoc,mul_comm,mul_left_comm] using test

/-- Scale residues once per prefix; use exact closed moments only for hits. -/
def residues (p q A S T e : ℕ) :=
  let w:=wt p e
  let y:=sig p e
  if ((A%q)*(w%q)+(S%q)*(y%q))%q≠0 then true else last p q A S T e

theorem residues_sound {h p q e d : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime) (oq : q≠2)
    (pc : h.Coprime p) (qc : h.Coprime q) (ne : p≠q) (dp : 0<d)
    (sol : OeisA245212.a (h*p^e*q^d)=(σ 1 (h*p^e*q^d):ℤ)) :
    residues p q (W h) (σ 1 h) (h*σ 0 h) e=false := by
  have no:=last_sound hh hp hq oq pc qc ne dp sol
  unfold last OMA.RankThreeLast245212.reject at no
  dsimp only at no
  split at no
  · contradiction
  next hz =>
    have modEq : (W h*wt p e+σ 1 h*sig p e)%q=
        ((W h%q)*(wt p e%q)+(σ 1 h%q)*(sig p e%q))%q := by
      simp [Nat.add_mod,Nat.mul_mod]
    simp only [residues,←modEq,if_neg hz]
    exact last_sound hh hp hq oq pc qc ne dp sol

def panel (h A S T p q : ℕ) :=
  let lo:=2*T*(p-1)*(q-1)
  let hi:=A*p*q
  if A+S>2*T then false else if hi<lo then true else if hi=lo then false else
    let E:=OMA.RankThreeFourSmallCut245212.horizon h A S T p q
    every 1 E (residues p q A S T) && every 1 E (residues q p A S T)

theorem panel_sound {h p q a b : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime)
    (op : 3≤p) (pq : p<q) (pc : h.Coprime p) (qc : h.Coprime q) (ap : 0<a) (bp : 0<b)
    (cert : panel h (W h) (σ 1 h) (h*σ 0 h) p q=true)
    (sol : OeisA245212.a (h*p^a*q^b)=(σ 1 (h*p^a*q^b):ℤ)) : False := by
  simp only [panel] at cert
  split at cert
  · contradiction
  next sub =>
    have cap:=(original_cap hh hp hq pc qc pq.ne ap (by omega) sol).1
    split at cert
    · omega
    split at cert
    · contradiction
    next ne =>
      have lt : 2*(h*σ 0 h)*(p-1)*(q-1)<W h*p*q := by omega
      have close:=OMA.RankThreeFourSmallCut245212.horizon_sound hh hp hq op pc qc pq ap bp lt sol
      obtain ⟨f,g⟩:=Bool.and_eq_true_iff.mp cert
      rcases le_total a b with sm|sm
      · rw [min_eq_left sm] at close
        have yes:=OMA.CofactorEulerPair245212.checked f ap close
        rw [residues_sound hh hp hq (by omega) pc qc pq.ne bp sol] at yes
        contradiction
      · rw [min_eq_right sm] at close
        have swap : OeisA245212.a (h*q^b*p^a)=(σ 1 (h*q^b*p^a):ℤ) := by rwa [mul_right_comm h (q^b)]
        have yes:=OMA.CofactorEulerPair245212.checked g bp close
        rw [residues_sound hh hq hp (by omega) qc pc pq.ne.symm ap swap] at yes
        contradiction

def slot (s p q a : ℕ) := panel (16*s^a) (129*wt s a) (31*sig s a) (80*OMA.Large245212.tax s a) p q

theorem slot_sound {s p q a b c : ℕ} (sp : s.Prime) (pp : p.Prime) (qp : q.Prime)
    (os : 2<s) (op : 2<p) (ps : s≠p) (qs : s≠q) (pq : p<q)
    (bp : 0<b) (cp : 0<c) (ck : slot s p q a=true) :
    OeisA245212.a (16*s^a*p^b*q^c)≠(σ 1 (16*s^a*p^b*q^c):ℤ) := by
  obtain ⟨sg,wt⟩:=OMA.Large245212.moments sp a
  have cs : (16:ℕ).Coprime (s^a) := (((coprime_primes prime_two sp).mpr (by omega)).pow_left 4).pow_right a
  have cop (t) (tp : t.Prime) (ot : 2<t) (st : s≠t) : (16*s^a).Coprime t :=
    (((coprime_primes prime_two tp).mpr (by omega)).pow_left 4).mul_left (((coprime_primes sp tp).mpr st).pow_left a)
  have vals : W 16=129 ∧ σ 1 16=31 ∧ σ 0 16=5 := by decide +kernel
  have w : W (16*s^a)=129*OMA.Large245212.wt s a := by rw [w_mult.map_mul_of_coprime cs,vals.1,wt]
  have y : σ 1 (16*s^a)=31*OMA.Large245212.sig s a := by rw [isMultiplicative_sigma.map_mul_of_coprime cs,vals.2.1,sg]
  have t : 16*s^a*σ 0 (16*s^a)=80*OMA.Large245212.tax s a := by
    rw [isMultiplicative_sigma.map_mul_of_coprime cs,vals.2.2,sigma_zero_apply_prime_pow sp,OMA.Large245212.tax];ring
  have hp:=sp.pos
  have cp1:=cop p pp op ps
  have cp2:=cop q qp (by omega) qs
  apply panel_sound (by positivity) pp qp op pq cp1 cp2 bp cp
  simpa only [slot,w,y,t] using ck

def check (s p q : ℕ) := every 1 (first s) (slot s p q)
def tables (p q r : ℕ) := check p q r && check q p r && check r p q

theorem original {p q r a b c : ℕ} (pp : p.Prime) (qp : q.Prime) (rp : r.Prime)
    (op : 2<p) (pq : p<q) (qr : q<r) (rb : r≤1706) (ap : 0<a) (bp : 0<b) (cp : 0<c)
    (ck : tables p q r=true) : OeisA245212.a (16*p^a*q^b*r^c)≠(σ 1 (16*p^a*q^b*r^c):ℤ) := by
  intro eqn
  obtain ⟨⟨x,y⟩,z⟩ := (show (check p q r=true ∧ check q p r=true) ∧ check r p q=true by
    simpa only [tables,Bool.and_eq_true] using ck)
  rcases one_short pp qp rp op pq qr rb ap bp cp eqn with sh|sh|sh
  · exact slot_sound pp qp rp op (by omega) pq.ne (pq.trans qr).ne qr bp cp
      (OMA.CofactorEulerPair245212.checked x ap sh) eqn
  · exact slot_sound qp pp rp (by omega) op pq.ne.symm qr.ne (pq.trans qr) ap cp
      (OMA.CofactorEulerPair245212.checked y bp sh) (by rwa [mul_right_comm 16 (q^b) (p^a)])
  · exact slot_sound rp pp qp (by omega) op (pq.trans qr).ne.symm qr.ne.symm pq ap bp
      (OMA.CofactorEulerPair245212.checked z cp sh) (by rwa [show 16*r^c*p^a*q^b=16*p^a*q^b*r^c by ring])

end OMA.SixteenTable245212

end

section

/- First enumerate a shortest exponent. The other two cannot be below it;
their increasing moments also exclude entire upper quadrants. -/
namespace OMA.SixteenMin245212
open Nat Finset ArithmeticFunction OMA.Smooth245212 OMA.Large245212
open OMA.SixteenTable245212 (residues residues_sound)
open OMA.RankThreeSixteenFixed245212 OMA.CofactorEulerPair245212
open scoped ArithmeticFunction.sigma
open OMA.CofactorEulerPair245212 (checked)
open OMA.Large245212 (moments)

private theorem corner {p q A T z a b : ℕ} (hp : p.Prime) (hq : q.Prime) (za : z≤a) (zb : z≤b)
    (lt : (A:ℚ)*(X p (some a)*X q (some b))<2*(T:ℚ)) :
    A*wt p z*wt q z < 2*T*OMA.Large245212.tax p z*OMA.Large245212.tax q z := by
  have rises {s n m : ℕ} (sp : s.Prime) (nm : n ≤ m) : X s (some n)≤X s (some m) :=
    add_le_add_right (div_le_div_of_nonneg_right (sub_le_sub_left (y_anti sp.one_lt nm) 1)
      (sub_nonneg.mpr (by exact_mod_cast sp.one_le))) 1
  have inc:=mul_le_mul (rises hp za) (rises hq zb) (x_nonneg hq.one_lt _) (x_nonneg hp.one_lt _)
  have sm := (mul_le_mul_of_nonneg_left inc (Nat.cast_nonneg A : (0:ℚ)≤A)).trans_lt lt
  have factor (s) (pr : s.Prime) : X s (some z)*(OMA.Large245212.tax s z:ℚ)=(wt s z:ℚ) := by
    rw [(OMA.Large245212.moments pr z).2];simpa [OMA.Large245212.tax] using x_factor pr z
  have pos (s) (pr : s.Prime) : 0<(OMA.Large245212.tax s z:ℚ) := by have :=pr.pos;unfold OMA.Large245212.tax; positivity
  have res:=mul_lt_mul_of_pos_right sm (mul_pos (pos p hp) (pos q hq))
  have ordered : (A:ℚ)*(X p (some z)*X q (some z))*((OMA.Large245212.tax p z:ℚ)*OMA.Large245212.tax q z)= A*(wt p z:ℚ)*wt q z := by rw [←factor p hp,←factor q hq];ring
  rw [ordered] at res
  exact_mod_cast (by linarith only [res] : (A:ℚ)*wt p z*wt q z<2*T*OMA.Large245212.tax p z*OMA.Large245212.tax q z)

def panel (h A S T p q z : ℕ) :=
  let lo:=2*T*(p-1)*(q-1)
  let hi:=A*p*q
  if A+S>2*T then false else if hi<lo then true else if hi=lo then false else if 2*T*OMA.Large245212.tax p z*OMA.Large245212.tax q z≤A*wt p z*wt q z then true else
    let E:=OMA.RankThreeFourSmallCut245212.horizon h A S T p q
    every z E (residues p q A S T) && every z E (residues q p A S T)

theorem panel_sound {h p q a b z : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime)
    (op : 3≤p) (pq : p<q) (pc : h.Coprime p) (qc : h.Coprime q) (ap : 0<a) (bp : 0<b)
    (za : z≤a) (zb : z≤b) (cert : panel h (W h) (σ 1 h) (h*σ 0 h) p q z=true)
    (sol : OeisA245212.a (h*p^a*q^b)=(σ 1 (h*p^a*q^b):ℤ)) : False := by
  simp only [panel] at cert
  split at cert
  · contradiction
  next sub =>
    obtain ⟨cap,actual⟩:=original_cap hh hp hq pc qc pq.ne ap (by omega) sol
    split at cert
    · omega
    split at cert
    · contradiction
    next ne =>
      have lt : 2*(h*σ 0 h)*(p-1)*(q-1)<W h*p*q := by omega
      split at cert
      · exact (Nat.not_le.mpr (corner hp hq za zb actual)) (by assumption)
      next =>
       have close:=OMA.RankThreeFourSmallCut245212.horizon_sound hh hp hq op pc qc pq ap bp lt sol
       obtain ⟨f,g⟩:=Bool.and_eq_true_iff.mp cert
       rcases le_total a b with sm|sm
       · rw [min_eq_left sm] at close
         have yes:=OMA.CofactorEulerPair245212.checked f za close
         rw [residues_sound hh hp hq (by omega) pc qc pq.ne bp sol] at yes
         contradiction
       · rw [min_eq_right sm] at close
         have swap : OeisA245212.a (h*q^b*p^a)=(σ 1 (h*q^b*p^a):ℤ) := by rwa [mul_right_comm h (q^b)]
         have yes:=OMA.CofactorEulerPair245212.checked g zb close
         rw [residues_sound hh hq hp (by omega) qc pc pq.ne.symm ap swap] at yes
         contradiction

def slot (s p q a : ℕ) := panel (16*s^a) (129*wt s a) (31*sig s a) (80*OMA.Large245212.tax s a) p q a

theorem slot_sound {s p q a b c : ℕ} (sp : s.Prime) (pp : p.Prime) (qp : q.Prime)
    (os : 2<s) (op : 2<p) (ps : s≠p) (qs : s≠q) (pq : p<q)
    (ab : a≤b) (ac : a≤c) (bp : 0<b) (cp : 0<c) (ck : slot s p q a=true) :
    OeisA245212.a (16*s^a*p^b*q^c)≠(σ 1 (16*s^a*p^b*q^c):ℤ) := by
  obtain ⟨sg,wt⟩:=OMA.Large245212.moments sp a
  have cs : (16:ℕ).Coprime (s^a) := (((coprime_primes prime_two sp).mpr (by omega)).pow_left 4).pow_right a
  have cop (t) (tp : t.Prime) (ot : 2<t) (st : s≠t) : (16*s^a).Coprime t :=
    (((coprime_primes prime_two tp).mpr (by omega)).pow_left 4).mul_left (((coprime_primes sp tp).mpr st).pow_left a)
  have vals : W 16=129 ∧ σ 1 16=31 ∧ σ 0 16=5 := by decide +kernel
  have w : W (16*s^a)=129*OMA.Large245212.wt s a := by rw [w_mult.map_mul_of_coprime cs,vals.1,wt]
  have y : σ 1 (16*s^a)=31*OMA.Large245212.sig s a := by rw [isMultiplicative_sigma.map_mul_of_coprime cs,vals.2.1,sg]
  have t : 16*s^a*σ 0 (16*s^a)=80*OMA.Large245212.tax s a := by
    rw [isMultiplicative_sigma.map_mul_of_coprime cs,vals.2.2,sigma_zero_apply_prime_pow sp,OMA.Large245212.tax];ring
  have hp:=sp.pos
  have cp1:=cop p pp op ps
  have cp2:=cop q qp (by omega) qs
  apply panel_sound (by positivity) pp qp op pq cp1 cp2 bp cp ab ac
  simpa only [slot,w,y,t] using ck


def check (s p q : ℕ) := every 1 82 (slot s p q)
def tables (p q r : ℕ) := check p q r && check q p r && check r p q

theorem original {p q r a b c : ℕ} (pp : p.Prime) (qp : q.Prime) (rp : r.Prime)
    (p7 : 7≤p) (pq : p<q) (qr : q<r) (rb : r≤1706) (ap : 0<a) (bp : 0<b) (cp : 0<c)
    (ck : tables p q r=true) : OeisA245212.a (16*p^a*q^b*r^c)≠(σ 1 (16*p^a*q^b*r^c):ℤ) := by
  intro eqn
  obtain ⟨⟨x,y⟩,z⟩ := (show (check p q r=true ∧ check q p r=true) ∧ check r p q=true by
    simpa only [tables,Bool.and_eq_true] using ck)
  have tiny {v : ℕ} (hv : 7≤v) : first v ≤ 82 :=
    max_le le_rfl (Nat.le_of_lt_succ (Nat.log_lt_of_lt_pow' (by decide : 83≠0)
      ((by decide +kernel : budget<7^83).trans_le (Nat.pow_le_pow_left hv 83))))
  have sh:=one_short pp qp rp (by omega) pq qr rb ap bp cp eqn
  have low : a≤82 ∨ b≤82 ∨ c≤82 := sh.imp (fun h=>h.trans (tiny p7))
    (Or.imp (fun h=>h.trans (tiny (by omega))) (fun h=>h.trans (tiny (by omega))))
  by_cases sm : a≤b ∧ a≤c
  · exact slot_sound pp qp rp (by omega) (by omega) pq.ne (pq.trans qr).ne qr sm.1 sm.2 bp cp
      (OMA.CofactorEulerPair245212.checked x ap (by omega)) eqn
  by_cases md : b≤c
  · exact slot_sound qp pp rp (by omega) (by omega) pq.ne.symm qr.ne (pq.trans qr) (by omega) md ap cp
      (OMA.CofactorEulerPair245212.checked y bp (by omega)) (by rwa [mul_right_comm 16 (q^b)])
  · exact slot_sound rp pp qp (by omega) (by omega) (pq.trans qr).ne.symm qr.ne.symm pq (by omega) (by omega) ap bp
      (OMA.CofactorEulerPair245212.checked z cp (by omega)) (by rwa [show 16*r^c*p^a*q^b=16*p^a*q^b*r^c by ring])

end OMA.SixteenMin245212

end

section

/- Join seven disjoint short-exponent intervals, allowing numerical
proofs to be checked independently while keeping the source small. -/
namespace OMA.SixteenCert245212
open OMA.CofactorEulerPair245212 OMA.RankThreeMiddle245212

theorem eightyTwo (f : ℕ→Bool)
    (c0 : every 1 12 f=true)
    (c1 : every 13 24 f=true)
    (c2 : every 25 36 f=true)
    (c3 : every 37 48 f=true)
    (c4 : every 49 60 f=true)
    (c5 : every 61 72 f=true)
    (c6 : every 73 82 f=true) : every 1 82 f=true :=
    (joinEvery (joinEvery c0 (joinEvery c1 c2)) (joinEvery (joinEvery c3 c4) (joinEvery c5 c6)))

theorem short {p q r : ℕ}
    (i0 : every 1 12 (OMA.SixteenMin245212.slot p q r)=true)
    (i1 : every 13 24 (OMA.SixteenMin245212.slot p q r)=true)
    (i2 : every 25 36 (OMA.SixteenMin245212.slot p q r)=true)
    (i3 : every 37 48 (OMA.SixteenMin245212.slot p q r)=true)
    (i4 : every 49 60 (OMA.SixteenMin245212.slot p q r)=true)
    (i5 : every 61 72 (OMA.SixteenMin245212.slot p q r)=true)
    (i6 : every 73 82 (OMA.SixteenMin245212.slot p q r)=true)
    (j0 : every 1 12 (OMA.SixteenMin245212.slot q p r)=true)
    (j1 : every 13 24 (OMA.SixteenMin245212.slot q p r)=true)
    (j2 : every 25 36 (OMA.SixteenMin245212.slot q p r)=true)
    (j3 : every 37 48 (OMA.SixteenMin245212.slot q p r)=true)
    (j4 : every 49 60 (OMA.SixteenMin245212.slot q p r)=true)
    (j5 : every 61 72 (OMA.SixteenMin245212.slot q p r)=true)
    (j6 : every 73 82 (OMA.SixteenMin245212.slot q p r)=true)
    (k0 : every 1 12 (OMA.SixteenMin245212.slot r p q)=true)
    (k1 : every 13 24 (OMA.SixteenMin245212.slot r p q)=true)
    (k2 : every 25 36 (OMA.SixteenMin245212.slot r p q)=true)
    (k3 : every 37 48 (OMA.SixteenMin245212.slot r p q)=true)
    (k4 : every 49 60 (OMA.SixteenMin245212.slot r p q)=true)
    (k5 : every 61 72 (OMA.SixteenMin245212.slot r p q)=true)
    (k6 : every 73 82 (OMA.SixteenMin245212.slot r p q)=true)
    : OMA.SixteenMin245212.tables p q r=true := by
  simp only [OMA.SixteenMin245212.tables,OMA.SixteenMin245212.check,Bool.and_eq_true]
  exact ⟨⟨eightyTwo _ i0 i1 i2 i3 i4 i5 i6,eightyTwo _ j0 j1 j2 j3 j4 j5 j6⟩,eightyTwo _ k0 k1 k2 k3 k4 k5 k6⟩

theorem fixed {p q r : ℕ}
    (pc : OMA.RankThreeSixteenFixed245212.first p=82) (qc : OMA.RankThreeSixteenFixed245212.first q=82) (rc : OMA.RankThreeSixteenFixed245212.first r=82)
    (i0 : every 1 12 (OMA.SixteenTable245212.slot p q r)=true)
    (i1 : every 13 24 (OMA.SixteenTable245212.slot p q r)=true)
    (i2 : every 25 36 (OMA.SixteenTable245212.slot p q r)=true)
    (i3 : every 37 48 (OMA.SixteenTable245212.slot p q r)=true)
    (i4 : every 49 60 (OMA.SixteenTable245212.slot p q r)=true)
    (i5 : every 61 72 (OMA.SixteenTable245212.slot p q r)=true)
    (i6 : every 73 82 (OMA.SixteenTable245212.slot p q r)=true)
    (j0 : every 1 12 (OMA.SixteenTable245212.slot q p r)=true)
    (j1 : every 13 24 (OMA.SixteenTable245212.slot q p r)=true)
    (j2 : every 25 36 (OMA.SixteenTable245212.slot q p r)=true)
    (j3 : every 37 48 (OMA.SixteenTable245212.slot q p r)=true)
    (j4 : every 49 60 (OMA.SixteenTable245212.slot q p r)=true)
    (j5 : every 61 72 (OMA.SixteenTable245212.slot q p r)=true)
    (j6 : every 73 82 (OMA.SixteenTable245212.slot q p r)=true)
    (k0 : every 1 12 (OMA.SixteenTable245212.slot r p q)=true)
    (k1 : every 13 24 (OMA.SixteenTable245212.slot r p q)=true)
    (k2 : every 25 36 (OMA.SixteenTable245212.slot r p q)=true)
    (k3 : every 37 48 (OMA.SixteenTable245212.slot r p q)=true)
    (k4 : every 49 60 (OMA.SixteenTable245212.slot r p q)=true)
    (k5 : every 61 72 (OMA.SixteenTable245212.slot r p q)=true)
    (k6 : every 73 82 (OMA.SixteenTable245212.slot r p q)=true)
    : OMA.SixteenTable245212.tables p q r=true := by
  simp only [OMA.SixteenTable245212.tables,OMA.SixteenTable245212.check,pc,qc,rc,Bool.and_eq_true]
  exact ⟨⟨eightyTwo _ i0 i1 i2 i3 i4 i5 i6,eightyTwo _ j0 j1 j2 j3 j4 j5 j6⟩,eightyTwo _ k0 k1 k2 k3 k4 k5 k6⟩

end OMA.SixteenCert245212

end

section

namespace OMA.SixteenRows7x17From19
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row19 : OMA.SixteenMin245212.tables 7 17 19=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From19

end

section

namespace OMA.SixteenRows7x17From23
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row23 : OMA.SixteenMin245212.tables 7 17 23=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From23

end

section

namespace OMA.SixteenRows7x17From29
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row29 : OMA.SixteenMin245212.tables 7 17 29=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From29

end

section

namespace OMA.SixteenRows7x17From31
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row31 : OMA.SixteenMin245212.tables 7 17 31=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From31

end

section

namespace OMA.SixteenRows7x17From37
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row37 : OMA.SixteenMin245212.tables 7 17 37=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From37

end

section

namespace OMA.SixteenRows7x17From41
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row41 : OMA.SixteenMin245212.tables 7 17 41=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From41

end

section

namespace OMA.SixteenRows7x17From43
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row43 : OMA.SixteenMin245212.tables 7 17 43=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From43

end

section

namespace OMA.SixteenRows7x17From47
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row47 : OMA.SixteenMin245212.tables 7 17 47=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From47

end

section

namespace OMA.SixteenRows7x17From53
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row53 : OMA.SixteenMin245212.tables 7 17 53=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From53

end

section

namespace OMA.SixteenRows7x17From59
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row59 : OMA.SixteenMin245212.tables 7 17 59=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From59

end

section

namespace OMA.SixteenRows7x17From61
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row61 : OMA.SixteenMin245212.tables 7 17 61=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From61

end

section

namespace OMA.SixteenRows7x17From67
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row67 : OMA.SixteenMin245212.tables 7 17 67=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From67

end

section

namespace OMA.SixteenRows7x17From71
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row71 : OMA.SixteenMin245212.tables 7 17 71=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From71

end

section

namespace OMA.SixteenRows7x17From73
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row73 : OMA.SixteenMin245212.tables 7 17 73=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From73

end

section

namespace OMA.SixteenRows7x17From79
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row79 : OMA.SixteenMin245212.tables 7 17 79=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From79

end

section

namespace OMA.SixteenRows7x17From83
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row83 : OMA.SixteenMin245212.tables 7 17 83=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From83

end

section

namespace OMA.SixteenRows7x17From89
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row89 : OMA.SixteenMin245212.tables 7 17 89=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From89

end

section

namespace OMA.SixteenRows7x17From97
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row97 : OMA.SixteenMin245212.tables 7 17 97=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From97

end

section

namespace OMA.SixteenRows7x17From101
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row101 : OMA.SixteenMin245212.tables 7 17 101=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From101

end

section

namespace OMA.SixteenRows7x17From103
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row103 : OMA.SixteenMin245212.tables 7 17 103=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From103

end

section

namespace OMA.SixteenRows7x17From107
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row107 : OMA.SixteenMin245212.tables 7 17 107=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From107

end

section

namespace OMA.SixteenRows7x17From109
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row109 : OMA.SixteenMin245212.tables 7 17 109=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From109

end

section

namespace OMA.SixteenRows7x17From113
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row113 : OMA.SixteenMin245212.tables 7 17 113=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From113

end

section

namespace OMA.SixteenRows7x17From127
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row127 : OMA.SixteenMin245212.tables 7 17 127=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From127

end

section

namespace OMA.SixteenRows7x17From131
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row131 : OMA.SixteenMin245212.tables 7 17 131=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From131

end

section

namespace OMA.SixteenRows7x17From137
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row137 : OMA.SixteenMin245212.tables 7 17 137=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From137

end

section

namespace OMA.SixteenRows7x17From139
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row139 : OMA.SixteenMin245212.tables 7 17 139=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From139

end

section

namespace OMA.SixteenRows7x17From149
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row149 : OMA.SixteenMin245212.tables 7 17 149=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From149

end

section

namespace OMA.SixteenRows7x17From151
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row151 : OMA.SixteenMin245212.tables 7 17 151=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From151

end

section

namespace OMA.SixteenRows7x17From157
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row157 : OMA.SixteenMin245212.tables 7 17 157=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From157

end

section

namespace OMA.SixteenRows7x17From163
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row163 : OMA.SixteenMin245212.tables 7 17 163=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From163

end

section

namespace OMA.SixteenRows7x17From167
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row167 : OMA.SixteenMin245212.tables 7 17 167=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From167

end

section

namespace OMA.SixteenRows7x17From173
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row173 : OMA.SixteenMin245212.tables 7 17 173=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From173

end

section

namespace OMA.SixteenRows7x17From179
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row179 : OMA.SixteenMin245212.tables 7 17 179=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From179

end

section

namespace OMA.SixteenRows7x17From181
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row181 : OMA.SixteenMin245212.tables 7 17 181=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From181

end

section

namespace OMA.SixteenRows7x17From191
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row191 : OMA.SixteenMin245212.tables 7 17 191=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From191

end

section

namespace OMA.SixteenRows7x17From193
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row193 : OMA.SixteenMin245212.tables 7 17 193=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From193

end

section

namespace OMA.SixteenRows7x17From197
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row197 : OMA.SixteenMin245212.tables 7 17 197=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From197

end

section

namespace OMA.SixteenRows7x17From199
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row199 : OMA.SixteenMin245212.tables 7 17 199=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From199

end

section

namespace OMA.SixteenRows7x17From211
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row211 : OMA.SixteenMin245212.tables 7 17 211=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From211

end

section

namespace OMA.SixteenRows7x17From223
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row223 : OMA.SixteenMin245212.tables 7 17 223=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From223

end

section

namespace OMA.SixteenRows7x17From227
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row227 : OMA.SixteenMin245212.tables 7 17 227=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From227

end

section

namespace OMA.SixteenRows7x17From229
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row229 : OMA.SixteenMin245212.tables 7 17 229=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From229

end

section

namespace OMA.SixteenRows7x17From233
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row233 : OMA.SixteenMin245212.tables 7 17 233=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From233

end

section

namespace OMA.SixteenRows7x17From239
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row239 : OMA.SixteenMin245212.tables 7 17 239=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From239

end

section

namespace OMA.SixteenRows7x17From241
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row241 : OMA.SixteenMin245212.tables 7 17 241=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From241

end

section

namespace OMA.SixteenRows7x17From251
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row251 : OMA.SixteenMin245212.tables 7 17 251=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From251

end

section

namespace OMA.SixteenRows7x17From257
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row257 : OMA.SixteenMin245212.tables 7 17 257=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From257

end

section

namespace OMA.SixteenRows7x17From263
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row263 : OMA.SixteenMin245212.tables 7 17 263=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From263

end

section

namespace OMA.SixteenRows7x17From269
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row269 : OMA.SixteenMin245212.tables 7 17 269=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From269

end

section

namespace OMA.SixteenRows7x17From271
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row271 : OMA.SixteenMin245212.tables 7 17 271=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From271

end

section

namespace OMA.SixteenRows7x17From277
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row277 : OMA.SixteenMin245212.tables 7 17 277=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From277

end

section

namespace OMA.SixteenRows7x17From281
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row281 : OMA.SixteenMin245212.tables 7 17 281=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From281

end

section

namespace OMA.SixteenRows7x17From283
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row283 : OMA.SixteenMin245212.tables 7 17 283=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From283

end

section

namespace OMA.SixteenRows7x17From293
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row293 : OMA.SixteenMin245212.tables 7 17 293=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From293

end

section

namespace OMA.SixteenRows7x17From307
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row307 : OMA.SixteenMin245212.tables 7 17 307=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From307

end

section

namespace OMA.SixteenRows7x17From311
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row311 : OMA.SixteenMin245212.tables 7 17 311=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From311

end

section

namespace OMA.SixteenRows7x17From313
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row313 : OMA.SixteenMin245212.tables 7 17 313=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From313

end

section

namespace OMA.SixteenRows7x17From317
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row317 : OMA.SixteenMin245212.tables 7 17 317=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From317

end

section

namespace OMA.SixteenRows7x17From331
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row331 : OMA.SixteenMin245212.tables 7 17 331=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From331

end

section

namespace OMA.SixteenRows7x17From337
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row337 : OMA.SixteenMin245212.tables 7 17 337=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From337

end

section

namespace OMA.SixteenRows7x17From347
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row347 : OMA.SixteenMin245212.tables 7 17 347=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From347

end

section

namespace OMA.SixteenRows7x17From349
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row349 : OMA.SixteenMin245212.tables 7 17 349=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From349

end

section

namespace OMA.SixteenRows7x17From353
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row353 : OMA.SixteenMin245212.tables 7 17 353=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From353

end

section

namespace OMA.SixteenRows7x17From359
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row359 : OMA.SixteenMin245212.tables 7 17 359=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From359

end

section

namespace OMA.SixteenRows7x17From367
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row367 : OMA.SixteenMin245212.tables 7 17 367=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From367

end

section

namespace OMA.SixteenRows7x17From373
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row373 : OMA.SixteenMin245212.tables 7 17 373=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From373

end

section

namespace OMA.SixteenRows7x17From379
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row379 : OMA.SixteenMin245212.tables 7 17 379=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From379

end

section

namespace OMA.SixteenRows7x17From383
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row383 : OMA.SixteenMin245212.tables 7 17 383=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From383

end

section

namespace OMA.SixteenRows7x17From389
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row389 : OMA.SixteenMin245212.tables 7 17 389=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From389

end

section

namespace OMA.SixteenRows7x17From397
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row397 : OMA.SixteenMin245212.tables 7 17 397=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From397

end

section

namespace OMA.SixteenRows7x17From401
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row401 : OMA.SixteenMin245212.tables 7 17 401=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From401

end

section

namespace OMA.SixteenRows7x17From409
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row409 : OMA.SixteenMin245212.tables 7 17 409=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From409

end

section

namespace OMA.SixteenRows7x17From419
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row419 : OMA.SixteenMin245212.tables 7 17 419=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From419

end

section

namespace OMA.SixteenRows7x17From421
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row421 : OMA.SixteenMin245212.tables 7 17 421=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From421

end

section

namespace OMA.SixteenRows7x17From431
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row431 : OMA.SixteenMin245212.tables 7 17 431=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From431

end

section

namespace OMA.SixteenRows7x17From433
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row433 : OMA.SixteenMin245212.tables 7 17 433=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From433

end

section

namespace OMA.SixteenRows7x17From439
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row439 : OMA.SixteenMin245212.tables 7 17 439=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From439

end

section

namespace OMA.SixteenRows7x17From443
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row443 : OMA.SixteenMin245212.tables 7 17 443=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From443

end

section

namespace OMA.SixteenRows7x17From449
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row449 : OMA.SixteenMin245212.tables 7 17 449=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From449

end

section

namespace OMA.SixteenRows7x17From457
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row457 : OMA.SixteenMin245212.tables 7 17 457=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From457

end

section

namespace OMA.SixteenRows7x17From461
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row461 : OMA.SixteenMin245212.tables 7 17 461=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From461

end

section

namespace OMA.SixteenRows7x17From463
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row463 : OMA.SixteenMin245212.tables 7 17 463=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From463

end

section

namespace OMA.SixteenRows7x17From467
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row467 : OMA.SixteenMin245212.tables 7 17 467=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From467

end

section

namespace OMA.SixteenRows7x17From479
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row479 : OMA.SixteenMin245212.tables 7 17 479=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From479

end

section

namespace OMA.SixteenRows7x17From487
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row487 : OMA.SixteenMin245212.tables 7 17 487=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From487

end

section

namespace OMA.SixteenRows7x17From491
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row491 : OMA.SixteenMin245212.tables 7 17 491=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From491

end

section

namespace OMA.SixteenRows7x17From499
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row499 : OMA.SixteenMin245212.tables 7 17 499=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From499

end

section

namespace OMA.SixteenRows7x17From503
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row503 : OMA.SixteenMin245212.tables 7 17 503=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From503

end

section

namespace OMA.SixteenRows7x17From509
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row509 : OMA.SixteenMin245212.tables 7 17 509=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From509

end

section

namespace OMA.SixteenRows7x17From521
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row521 : OMA.SixteenMin245212.tables 7 17 521=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From521

end

section

namespace OMA.SixteenRows7x17From523
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row523 : OMA.SixteenMin245212.tables 7 17 523=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From523

end

section

namespace OMA.SixteenRows7x17From541
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row541 : OMA.SixteenMin245212.tables 7 17 541=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From541

end

section

namespace OMA.SixteenRows7x17From547
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row547 : OMA.SixteenMin245212.tables 7 17 547=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From547

end

section

namespace OMA.SixteenRows7x17From557
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row557 : OMA.SixteenMin245212.tables 7 17 557=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From557

end

section

namespace OMA.SixteenRows7x17From563
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row563 : OMA.SixteenMin245212.tables 7 17 563=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From563

end

section

namespace OMA.SixteenRows7x17From569
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row569 : OMA.SixteenMin245212.tables 7 17 569=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From569

end

section

namespace OMA.SixteenRows7x17From571
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row571 : OMA.SixteenMin245212.tables 7 17 571=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From571

end

section

namespace OMA.SixteenRows7x17From577
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row577 : OMA.SixteenMin245212.tables 7 17 577=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From577

end

section

namespace OMA.SixteenRows7x17From587
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row587 : OMA.SixteenMin245212.tables 7 17 587=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From587

end

section

namespace OMA.SixteenRows7x17From593
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row593 : OMA.SixteenMin245212.tables 7 17 593=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From593

end

section

namespace OMA.SixteenRows7x17From599
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row599 : OMA.SixteenMin245212.tables 7 17 599=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From599

end

section

namespace OMA.SixteenRows7x17From601
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row601 : OMA.SixteenMin245212.tables 7 17 601=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From601

end

section

namespace OMA.SixteenRows7x17From607
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row607 : OMA.SixteenMin245212.tables 7 17 607=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From607

end

section

namespace OMA.SixteenRows7x17From613
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row613 : OMA.SixteenMin245212.tables 7 17 613=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From613

end

section

namespace OMA.SixteenRows7x17From617
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row617 : OMA.SixteenMin245212.tables 7 17 617=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From617

end

section

namespace OMA.SixteenRows7x17From619
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row619 : OMA.SixteenMin245212.tables 7 17 619=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From619

end

section

namespace OMA.SixteenRows7x17From631
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row631 : OMA.SixteenMin245212.tables 7 17 631=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From631

end

section

namespace OMA.SixteenRows7x17From641
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row641 : OMA.SixteenMin245212.tables 7 17 641=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From641

end

section

namespace OMA.SixteenRows7x17From643
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row643 : OMA.SixteenMin245212.tables 7 17 643=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From643

end

section

namespace OMA.SixteenRows7x17From647
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row647 : OMA.SixteenMin245212.tables 7 17 647=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From647

end

section

namespace OMA.SixteenRows7x17From653
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row653 : OMA.SixteenMin245212.tables 7 17 653=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From653

end

section

namespace OMA.SixteenRows7x17From659
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row659 : OMA.SixteenMin245212.tables 7 17 659=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From659

end

section

namespace OMA.SixteenRows7x17From661
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row661 : OMA.SixteenMin245212.tables 7 17 661=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From661

end

section

namespace OMA.SixteenRows7x17From673
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row673 : OMA.SixteenMin245212.tables 7 17 673=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From673

end

section

namespace OMA.SixteenRows7x17From677
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row677 : OMA.SixteenMin245212.tables 7 17 677=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From677

end

section

namespace OMA.SixteenRows7x17From683
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row683 : OMA.SixteenMin245212.tables 7 17 683=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From683

end

section

namespace OMA.SixteenRows7x17From691
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row691 : OMA.SixteenMin245212.tables 7 17 691=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From691

end

section

namespace OMA.SixteenRows7x17From701
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row701 : OMA.SixteenMin245212.tables 7 17 701=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From701

end

section

namespace OMA.SixteenRows7x17From709
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row709 : OMA.SixteenMin245212.tables 7 17 709=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From709

end

section

namespace OMA.SixteenRows7x17From719
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row719 : OMA.SixteenMin245212.tables 7 17 719=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From719

end

section

namespace OMA.SixteenRows7x17From727
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row727 : OMA.SixteenMin245212.tables 7 17 727=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From727

end

section

namespace OMA.SixteenRows7x17From733
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row733 : OMA.SixteenMin245212.tables 7 17 733=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From733

end

section

namespace OMA.SixteenRows7x17From739
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row739 : OMA.SixteenMin245212.tables 7 17 739=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From739

end

section

namespace OMA.SixteenRows7x17From743
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row743 : OMA.SixteenMin245212.tables 7 17 743=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From743

end

section

namespace OMA.SixteenRows7x17From751
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row751 : OMA.SixteenMin245212.tables 7 17 751=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From751

end

section

namespace OMA.SixteenRows7x17From757
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row757 : OMA.SixteenMin245212.tables 7 17 757=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From757

end

section

namespace OMA.SixteenRows7x17From761
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row761 : OMA.SixteenMin245212.tables 7 17 761=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From761

end

section

namespace OMA.SixteenRows7x17From769
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row769 : OMA.SixteenMin245212.tables 7 17 769=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From769

end

section

namespace OMA.SixteenRows7x17From773
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row773 : OMA.SixteenMin245212.tables 7 17 773=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From773

end

section

namespace OMA.SixteenRows7x17From787
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row787 : OMA.SixteenMin245212.tables 7 17 787=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From787

end

section

namespace OMA.SixteenRows7x17From797
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row797 : OMA.SixteenMin245212.tables 7 17 797=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From797

end

section

namespace OMA.SixteenRows7x17From809
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row809 : OMA.SixteenMin245212.tables 7 17 809=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From809

end

section

namespace OMA.SixteenRows7x17From811
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row811 : OMA.SixteenMin245212.tables 7 17 811=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From811

end

section

namespace OMA.SixteenRows7x17From821
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row821 : OMA.SixteenMin245212.tables 7 17 821=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From821

end

section

namespace OMA.SixteenRows7x17From823
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row823 : OMA.SixteenMin245212.tables 7 17 823=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From823

end

section

namespace OMA.SixteenRows7x17From827
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row827 : OMA.SixteenMin245212.tables 7 17 827=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From827

end

section

namespace OMA.SixteenRows7x17From829
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row829 : OMA.SixteenMin245212.tables 7 17 829=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From829

end

section

namespace OMA.SixteenRows7x17From839
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row839 : OMA.SixteenMin245212.tables 7 17 839=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From839

end

section

namespace OMA.SixteenRows7x17From853
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row853 : OMA.SixteenMin245212.tables 7 17 853=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From853

end

section

namespace OMA.SixteenRows7x17From857
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row857 : OMA.SixteenMin245212.tables 7 17 857=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From857

end

section

namespace OMA.SixteenRows7x17From859
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row859 : OMA.SixteenMin245212.tables 7 17 859=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From859

end

section

namespace OMA.SixteenRows7x17From863
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row863 : OMA.SixteenMin245212.tables 7 17 863=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From863

end

section

namespace OMA.SixteenRows7x17From877
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row877 : OMA.SixteenMin245212.tables 7 17 877=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From877

end

section

namespace OMA.SixteenRows7x17From881
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row881 : OMA.SixteenMin245212.tables 7 17 881=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From881

end

section

namespace OMA.SixteenRows7x17From883
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row883 : OMA.SixteenMin245212.tables 7 17 883=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From883

end

section

namespace OMA.SixteenRows7x17From887
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row887 : OMA.SixteenMin245212.tables 7 17 887=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From887

end

section

namespace OMA.SixteenRows7x17From907
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row907 : OMA.SixteenMin245212.tables 7 17 907=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From907

end

section

namespace OMA.SixteenRows7x17From911
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row911 : OMA.SixteenMin245212.tables 7 17 911=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From911

end

section

namespace OMA.SixteenRows7x17From919
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row919 : OMA.SixteenMin245212.tables 7 17 919=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From919

end

section

namespace OMA.SixteenRows7x17From929
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row929 : OMA.SixteenMin245212.tables 7 17 929=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From929

end

section

namespace OMA.SixteenRows7x17From937
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row937 : OMA.SixteenMin245212.tables 7 17 937=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From937

end

section

namespace OMA.SixteenRows7x17From941
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row941 : OMA.SixteenMin245212.tables 7 17 941=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From941

end

section

namespace OMA.SixteenRows7x17From947
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row947 : OMA.SixteenMin245212.tables 7 17 947=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From947

end

section

namespace OMA.SixteenRows7x17From953
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row953 : OMA.SixteenMin245212.tables 7 17 953=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From953

end

section

namespace OMA.SixteenRows7x17From967
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row967 : OMA.SixteenMin245212.tables 7 17 967=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From967

end

section

namespace OMA.SixteenRows7x17From971
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row971 : OMA.SixteenMin245212.tables 7 17 971=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From971

end

section

namespace OMA.SixteenRows7x17From977
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row977 : OMA.SixteenMin245212.tables 7 17 977=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From977

end

section

namespace OMA.SixteenRows7x17From983
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row983 : OMA.SixteenMin245212.tables 7 17 983=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From983

end

section

namespace OMA.SixteenRows7x17From991
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row991 : OMA.SixteenMin245212.tables 7 17 991=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From991

end

section

namespace OMA.SixteenRows7x17From997
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row997 : OMA.SixteenMin245212.tables 7 17 997=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From997

end

section

namespace OMA.SixteenRows7x17From1009
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1009 : OMA.SixteenMin245212.tables 7 17 1009=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1009

end

section

namespace OMA.SixteenRows7x17From1013
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1013 : OMA.SixteenMin245212.tables 7 17 1013=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1013

end

section

namespace OMA.SixteenRows7x17From1019
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1019 : OMA.SixteenMin245212.tables 7 17 1019=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1019

end

section

namespace OMA.SixteenRows7x17From1021
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1021 : OMA.SixteenMin245212.tables 7 17 1021=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1021

end

section

namespace OMA.SixteenRows7x17From1031
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1031 : OMA.SixteenMin245212.tables 7 17 1031=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1031

end

section

namespace OMA.SixteenRows7x17From1033
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1033 : OMA.SixteenMin245212.tables 7 17 1033=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1033

end

section

namespace OMA.SixteenRows7x17From1039
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1039 : OMA.SixteenMin245212.tables 7 17 1039=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1039

end

section

namespace OMA.SixteenRows7x17From1049
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1049 : OMA.SixteenMin245212.tables 7 17 1049=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1049

end

section

namespace OMA.SixteenRows7x17From1051
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1051 : OMA.SixteenMin245212.tables 7 17 1051=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1051

end

section

namespace OMA.SixteenRows7x17From1061
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1061 : OMA.SixteenMin245212.tables 7 17 1061=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1061

end

section

namespace OMA.SixteenRows7x17From1063
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1063 : OMA.SixteenMin245212.tables 7 17 1063=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1063

end

section

namespace OMA.SixteenRows7x17From1069
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1069 : OMA.SixteenMin245212.tables 7 17 1069=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1069

end

section

namespace OMA.SixteenRows7x17From1087
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1087 : OMA.SixteenMin245212.tables 7 17 1087=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1087

end

section

namespace OMA.SixteenRows7x17From1091
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1091 : OMA.SixteenMin245212.tables 7 17 1091=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1091

end

section

namespace OMA.SixteenRows7x17From1093
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1093 : OMA.SixteenMin245212.tables 7 17 1093=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1093

end

section

namespace OMA.SixteenRows7x17From1097
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1097 : OMA.SixteenMin245212.tables 7 17 1097=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1097

end

section

namespace OMA.SixteenRows7x17From1103
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1103 : OMA.SixteenMin245212.tables 7 17 1103=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1103

end

section

namespace OMA.SixteenRows7x17From1109
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1109 : OMA.SixteenMin245212.tables 7 17 1109=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1109

end

section

namespace OMA.SixteenRows7x17From1117
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1117 : OMA.SixteenMin245212.tables 7 17 1117=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1117

end

section

namespace OMA.SixteenRows7x17From1123
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1123 : OMA.SixteenMin245212.tables 7 17 1123=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1123

end

section

namespace OMA.SixteenRows7x17From1129
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1129 : OMA.SixteenMin245212.tables 7 17 1129=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1129

end

section

namespace OMA.SixteenRows7x17From1151
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1151 : OMA.SixteenMin245212.tables 7 17 1151=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1151

end

section

namespace OMA.SixteenRows7x17From1153
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1153 : OMA.SixteenMin245212.tables 7 17 1153=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1153

end

section

namespace OMA.SixteenRows7x17From1163
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1163 : OMA.SixteenMin245212.tables 7 17 1163=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1163

end

section

namespace OMA.SixteenRows7x17From1171
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1171 : OMA.SixteenMin245212.tables 7 17 1171=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1171

end

section

namespace OMA.SixteenRows7x17From1181
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1181 : OMA.SixteenMin245212.tables 7 17 1181=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1181

end

section

namespace OMA.SixteenRows7x17From1187
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1187 : OMA.SixteenMin245212.tables 7 17 1187=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1187

end

section

namespace OMA.SixteenRows7x17From1193
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1193 : OMA.SixteenMin245212.tables 7 17 1193=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1193

end

section

namespace OMA.SixteenRows7x17From1201
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1201 : OMA.SixteenMin245212.tables 7 17 1201=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1201

end

section

namespace OMA.SixteenRows7x17From1213
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1213 : OMA.SixteenMin245212.tables 7 17 1213=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1213

end

section

namespace OMA.SixteenRows7x17From1217
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1217 : OMA.SixteenMin245212.tables 7 17 1217=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1217

end

section

namespace OMA.SixteenRows7x17From1223
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1223 : OMA.SixteenMin245212.tables 7 17 1223=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1223

end

section

namespace OMA.SixteenRows7x17From1229
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1229 : OMA.SixteenMin245212.tables 7 17 1229=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1229

end

section

namespace OMA.SixteenRows7x17From1231
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1231 : OMA.SixteenMin245212.tables 7 17 1231=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1231

end

section

namespace OMA.SixteenRows7x17From1237
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1237 : OMA.SixteenMin245212.tables 7 17 1237=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1237

end

section

namespace OMA.SixteenRows7x17From1249
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1249 : OMA.SixteenMin245212.tables 7 17 1249=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1249

end

section

namespace OMA.SixteenRows7x17From1259
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1259 : OMA.SixteenMin245212.tables 7 17 1259=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1259

end

section

namespace OMA.SixteenRows7x17From1277
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1277 : OMA.SixteenMin245212.tables 7 17 1277=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1277

end

section

namespace OMA.SixteenRows7x17From1279
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1279 : OMA.SixteenMin245212.tables 7 17 1279=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1279

end

section

namespace OMA.SixteenRows7x17From1283
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1283 : OMA.SixteenMin245212.tables 7 17 1283=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1283

end

section

namespace OMA.SixteenRows7x17From1289
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1289 : OMA.SixteenMin245212.tables 7 17 1289=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1289

end

section

namespace OMA.SixteenRows7x17From1291
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1291 : OMA.SixteenMin245212.tables 7 17 1291=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1291

end

section

namespace OMA.SixteenRows7x17From1297
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1297 : OMA.SixteenMin245212.tables 7 17 1297=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1297

end

section

namespace OMA.SixteenRows7x17From1301
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1301 : OMA.SixteenMin245212.tables 7 17 1301=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1301

end

section

namespace OMA.SixteenRows7x17From1303
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1303 : OMA.SixteenMin245212.tables 7 17 1303=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1303

end

section

namespace OMA.SixteenRows7x17From1307
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1307 : OMA.SixteenMin245212.tables 7 17 1307=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1307

end

section

namespace OMA.SixteenRows7x17From1319
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1319 : OMA.SixteenMin245212.tables 7 17 1319=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1319

end

section

namespace OMA.SixteenRows7x17From1321
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1321 : OMA.SixteenMin245212.tables 7 17 1321=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1321

end

section

namespace OMA.SixteenRows7x17From1327
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1327 : OMA.SixteenMin245212.tables 7 17 1327=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1327

end

section

namespace OMA.SixteenRows7x17From1361
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1361 : OMA.SixteenMin245212.tables 7 17 1361=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1361

end

section

namespace OMA.SixteenRows7x17From1367
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1367 : OMA.SixteenMin245212.tables 7 17 1367=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1367

end

section

namespace OMA.SixteenRows7x17From1373
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1373 : OMA.SixteenMin245212.tables 7 17 1373=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1373

end

section

namespace OMA.SixteenRows7x17From1381
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1381 : OMA.SixteenMin245212.tables 7 17 1381=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1381

end

section

namespace OMA.SixteenRows7x17From1399
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1399 : OMA.SixteenMin245212.tables 7 17 1399=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1399

end

section

namespace OMA.SixteenRows7x17From1409
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1409 : OMA.SixteenMin245212.tables 7 17 1409=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1409

end

section

namespace OMA.SixteenRows7x17From1423
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1423 : OMA.SixteenMin245212.tables 7 17 1423=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1423

end

section

namespace OMA.SixteenRows7x17From1427
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1427 : OMA.SixteenMin245212.tables 7 17 1427=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1427

end

section

namespace OMA.SixteenRows7x17From1429
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1429 : OMA.SixteenMin245212.tables 7 17 1429=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1429

end

section

namespace OMA.SixteenRows7x17From1433
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1433 : OMA.SixteenMin245212.tables 7 17 1433=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1433

end

section

namespace OMA.SixteenRows7x17From1439
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1439 : OMA.SixteenMin245212.tables 7 17 1439=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1439

end

section

namespace OMA.SixteenRows7x17From1447
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1447 : OMA.SixteenMin245212.tables 7 17 1447=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1447

end

section

namespace OMA.SixteenRows7x17From1451
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1451 : OMA.SixteenMin245212.tables 7 17 1451=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1451

end

section

namespace OMA.SixteenRows7x17From1453
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1453 : OMA.SixteenMin245212.tables 7 17 1453=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1453

end

section

namespace OMA.SixteenRows7x17From1459
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1459 : OMA.SixteenMin245212.tables 7 17 1459=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1459

end

section

namespace OMA.SixteenRows7x17From1471
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1471 : OMA.SixteenMin245212.tables 7 17 1471=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1471

end

section

namespace OMA.SixteenRows7x17From1481
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1481 : OMA.SixteenMin245212.tables 7 17 1481=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1481

end

section

namespace OMA.SixteenRows7x17From1483
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1483 : OMA.SixteenMin245212.tables 7 17 1483=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1483

end

section

namespace OMA.SixteenRows7x17From1487
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1487 : OMA.SixteenMin245212.tables 7 17 1487=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1487

end

section

namespace OMA.SixteenRows7x17From1489
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1489 : OMA.SixteenMin245212.tables 7 17 1489=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1489

end

section

namespace OMA.SixteenRows7x17From1493
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1493 : OMA.SixteenMin245212.tables 7 17 1493=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1493

end

section

namespace OMA.SixteenRows7x17From1499
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1499 : OMA.SixteenMin245212.tables 7 17 1499=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1499

end

section

namespace OMA.SixteenRows7x17From1511
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1511 : OMA.SixteenMin245212.tables 7 17 1511=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1511

end

section

namespace OMA.SixteenRows7x17From1523
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1523 : OMA.SixteenMin245212.tables 7 17 1523=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1523

end

section

namespace OMA.SixteenRows7x17From1531
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1531 : OMA.SixteenMin245212.tables 7 17 1531=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1531

end

section

namespace OMA.SixteenRows7x17From1543
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1543 : OMA.SixteenMin245212.tables 7 17 1543=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1543

end

section

namespace OMA.SixteenRows7x17From1549
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1549 : OMA.SixteenMin245212.tables 7 17 1549=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1549

end

section

namespace OMA.SixteenRows7x17From1553
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1553 : OMA.SixteenMin245212.tables 7 17 1553=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1553

end

section

namespace OMA.SixteenRows7x17From1559
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1559 : OMA.SixteenMin245212.tables 7 17 1559=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1559

end

section

namespace OMA.SixteenRows7x17From1567
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1567 : OMA.SixteenMin245212.tables 7 17 1567=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1567

end

section

namespace OMA.SixteenRows7x17From1571
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1571 : OMA.SixteenMin245212.tables 7 17 1571=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1571

end

section

namespace OMA.SixteenRows7x17From1579
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1579 : OMA.SixteenMin245212.tables 7 17 1579=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1579

end

section

namespace OMA.SixteenRows7x17From1583
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1583 : OMA.SixteenMin245212.tables 7 17 1583=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1583

end

section

namespace OMA.SixteenRows7x17From1597
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1597 : OMA.SixteenMin245212.tables 7 17 1597=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1597

end

section

namespace OMA.SixteenRows7x17From1601
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1601 : OMA.SixteenMin245212.tables 7 17 1601=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1601

end

section

namespace OMA.SixteenRows7x17From1607
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1607 : OMA.SixteenMin245212.tables 7 17 1607=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1607

end

section

namespace OMA.SixteenRows7x17From1609
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1609 : OMA.SixteenMin245212.tables 7 17 1609=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1609

end

section

namespace OMA.SixteenRows7x17From1613
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1613 : OMA.SixteenMin245212.tables 7 17 1613=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1613

end

section

namespace OMA.SixteenRows7x17From1619
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1619 : OMA.SixteenMin245212.tables 7 17 1619=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1619

end

section

namespace OMA.SixteenRows7x17From1621
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1621 : OMA.SixteenMin245212.tables 7 17 1621=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1621

end

section

namespace OMA.SixteenRows7x17From1627
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1627 : OMA.SixteenMin245212.tables 7 17 1627=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1627

end

section

namespace OMA.SixteenRows7x17From1637
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1637 : OMA.SixteenMin245212.tables 7 17 1637=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1637

end

section

namespace OMA.SixteenRows7x17From1657
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1657 : OMA.SixteenMin245212.tables 7 17 1657=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1657

end

section

namespace OMA.SixteenRows7x17From1663
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1663 : OMA.SixteenMin245212.tables 7 17 1663=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1663

end

section

namespace OMA.SixteenRows7x17From1667
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1667 : OMA.SixteenMin245212.tables 7 17 1667=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1667

end

section

namespace OMA.SixteenRows7x17From1669
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1669 : OMA.SixteenMin245212.tables 7 17 1669=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1669

end

section

namespace OMA.SixteenRows7x17From1693
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1693 : OMA.SixteenMin245212.tables 7 17 1693=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1693

end

section

namespace OMA.SixteenRows7x17From1697
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1697 : OMA.SixteenMin245212.tables 7 17 1697=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1697

end

section

namespace OMA.SixteenRows7x17From1699
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row1699 : OMA.SixteenMin245212.tables 7 17 1699=true := by
  apply OMA.SixteenCert245212.short <;> decide +kernel
end OMA.SixteenRows7x17From1699

end

section

/- All values of the terminal prime and of all three exponents. -/
namespace OMA.SixteenFamily7x17
open OMA.SixteenMin245212 OMA.CofactorEulerPair245212 OMA.RankThreeSixteenSupport245212
open scoped ArithmeticFunction.sigma
open OMA.CofactorEulerPair245212 (checked)
set_option maxRecDepth 65536
private def allowed : List ℕ := [19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,293,307,311,313,317,331,337,347,349,353,359,367,373,379,383,389,397,401,409,419,421,431,433,439,443,449,457,461,463,467,479,487,491,499,503,509,521,523,541,547,557,563,569,571,577,587,593,599,601,607,613,617,619,631,641,643,647,653,659,661,673,677,683,691,701,709,719,727,733,739,743,751,757,761,769,773,787,797,809,811,821,823,827,829,839,853,857,859,863,877,881,883,887,907,911,919,929,937,941,947,953,967,971,977,983,991,997,1009,1013,1019,1021,1031,1033,1039,1049,1051,1061,1063,1069,1087,1091,1093,1097,1103,1109,1117,1123,1129,1151,1153,1163,1171,1181,1187,1193,1201,1213,1217,1223,1229,1231,1237,1249,1259,1277,1279,1283,1289,1291,1297,1301,1303,1307,1319,1321,1327,1361,1367,1373,1381,1399,1409,1423,1427,1429,1433,1439,1447,1451,1453,1459,1471,1481,1483,1487,1489,1493,1499,1511,1523,1531,1543,1549,1553,1559,1567,1571,1579,1583,1597,1601,1607,1609,1613,1619,1621,1627,1637,1657,1663,1667,1669,1693,1697,1699]
private theorem choices : every 18 1706 (fun r=>decide (OMA.KernelPrimeWindow245212.trial r=true → r∈allowed))=true := by decide +kernel
private theorem passed : ∀ r∈allowed,tables 7 17 r=true := by
  simp only [allowed,List.forall_mem_cons,List.not_mem_nil]
  exact ⟨OMA.SixteenRows7x17From19.row19,OMA.SixteenRows7x17From23.row23,OMA.SixteenRows7x17From29.row29,OMA.SixteenRows7x17From31.row31,OMA.SixteenRows7x17From37.row37,OMA.SixteenRows7x17From41.row41,OMA.SixteenRows7x17From43.row43,OMA.SixteenRows7x17From47.row47,OMA.SixteenRows7x17From53.row53,OMA.SixteenRows7x17From59.row59,OMA.SixteenRows7x17From61.row61,OMA.SixteenRows7x17From67.row67,OMA.SixteenRows7x17From71.row71,OMA.SixteenRows7x17From73.row73,OMA.SixteenRows7x17From79.row79,OMA.SixteenRows7x17From83.row83,OMA.SixteenRows7x17From89.row89,OMA.SixteenRows7x17From97.row97,OMA.SixteenRows7x17From101.row101,OMA.SixteenRows7x17From103.row103,OMA.SixteenRows7x17From107.row107,OMA.SixteenRows7x17From109.row109,OMA.SixteenRows7x17From113.row113,OMA.SixteenRows7x17From127.row127,OMA.SixteenRows7x17From131.row131,OMA.SixteenRows7x17From137.row137,OMA.SixteenRows7x17From139.row139,OMA.SixteenRows7x17From149.row149,OMA.SixteenRows7x17From151.row151,OMA.SixteenRows7x17From157.row157,OMA.SixteenRows7x17From163.row163,OMA.SixteenRows7x17From167.row167,OMA.SixteenRows7x17From173.row173,OMA.SixteenRows7x17From179.row179,OMA.SixteenRows7x17From181.row181,OMA.SixteenRows7x17From191.row191,OMA.SixteenRows7x17From193.row193,OMA.SixteenRows7x17From197.row197,OMA.SixteenRows7x17From199.row199,OMA.SixteenRows7x17From211.row211,OMA.SixteenRows7x17From223.row223,OMA.SixteenRows7x17From227.row227,OMA.SixteenRows7x17From229.row229,OMA.SixteenRows7x17From233.row233,OMA.SixteenRows7x17From239.row239,OMA.SixteenRows7x17From241.row241,OMA.SixteenRows7x17From251.row251,OMA.SixteenRows7x17From257.row257,OMA.SixteenRows7x17From263.row263,OMA.SixteenRows7x17From269.row269,OMA.SixteenRows7x17From271.row271,OMA.SixteenRows7x17From277.row277,OMA.SixteenRows7x17From281.row281,OMA.SixteenRows7x17From283.row283,OMA.SixteenRows7x17From293.row293,OMA.SixteenRows7x17From307.row307,OMA.SixteenRows7x17From311.row311,OMA.SixteenRows7x17From313.row313,OMA.SixteenRows7x17From317.row317,OMA.SixteenRows7x17From331.row331,OMA.SixteenRows7x17From337.row337,OMA.SixteenRows7x17From347.row347,OMA.SixteenRows7x17From349.row349,OMA.SixteenRows7x17From353.row353,OMA.SixteenRows7x17From359.row359,OMA.SixteenRows7x17From367.row367,OMA.SixteenRows7x17From373.row373,OMA.SixteenRows7x17From379.row379,OMA.SixteenRows7x17From383.row383,OMA.SixteenRows7x17From389.row389,OMA.SixteenRows7x17From397.row397,OMA.SixteenRows7x17From401.row401,OMA.SixteenRows7x17From409.row409,OMA.SixteenRows7x17From419.row419,OMA.SixteenRows7x17From421.row421,OMA.SixteenRows7x17From431.row431,OMA.SixteenRows7x17From433.row433,OMA.SixteenRows7x17From439.row439,OMA.SixteenRows7x17From443.row443,OMA.SixteenRows7x17From449.row449,OMA.SixteenRows7x17From457.row457,OMA.SixteenRows7x17From461.row461,OMA.SixteenRows7x17From463.row463,OMA.SixteenRows7x17From467.row467,OMA.SixteenRows7x17From479.row479,OMA.SixteenRows7x17From487.row487,OMA.SixteenRows7x17From491.row491,OMA.SixteenRows7x17From499.row499,OMA.SixteenRows7x17From503.row503,OMA.SixteenRows7x17From509.row509,OMA.SixteenRows7x17From521.row521,OMA.SixteenRows7x17From523.row523,OMA.SixteenRows7x17From541.row541,OMA.SixteenRows7x17From547.row547,OMA.SixteenRows7x17From557.row557,OMA.SixteenRows7x17From563.row563,OMA.SixteenRows7x17From569.row569,OMA.SixteenRows7x17From571.row571,OMA.SixteenRows7x17From577.row577,OMA.SixteenRows7x17From587.row587,OMA.SixteenRows7x17From593.row593,OMA.SixteenRows7x17From599.row599,OMA.SixteenRows7x17From601.row601,OMA.SixteenRows7x17From607.row607,OMA.SixteenRows7x17From613.row613,OMA.SixteenRows7x17From617.row617,OMA.SixteenRows7x17From619.row619,OMA.SixteenRows7x17From631.row631,OMA.SixteenRows7x17From641.row641,OMA.SixteenRows7x17From643.row643,OMA.SixteenRows7x17From647.row647,OMA.SixteenRows7x17From653.row653,OMA.SixteenRows7x17From659.row659,OMA.SixteenRows7x17From661.row661,OMA.SixteenRows7x17From673.row673,OMA.SixteenRows7x17From677.row677,OMA.SixteenRows7x17From683.row683,OMA.SixteenRows7x17From691.row691,OMA.SixteenRows7x17From701.row701,OMA.SixteenRows7x17From709.row709,OMA.SixteenRows7x17From719.row719,OMA.SixteenRows7x17From727.row727,OMA.SixteenRows7x17From733.row733,OMA.SixteenRows7x17From739.row739,OMA.SixteenRows7x17From743.row743,OMA.SixteenRows7x17From751.row751,OMA.SixteenRows7x17From757.row757,OMA.SixteenRows7x17From761.row761,OMA.SixteenRows7x17From769.row769,OMA.SixteenRows7x17From773.row773,OMA.SixteenRows7x17From787.row787,OMA.SixteenRows7x17From797.row797,OMA.SixteenRows7x17From809.row809,OMA.SixteenRows7x17From811.row811,OMA.SixteenRows7x17From821.row821,OMA.SixteenRows7x17From823.row823,OMA.SixteenRows7x17From827.row827,OMA.SixteenRows7x17From829.row829,OMA.SixteenRows7x17From839.row839,OMA.SixteenRows7x17From853.row853,OMA.SixteenRows7x17From857.row857,OMA.SixteenRows7x17From859.row859,OMA.SixteenRows7x17From863.row863,OMA.SixteenRows7x17From877.row877,OMA.SixteenRows7x17From881.row881,OMA.SixteenRows7x17From883.row883,OMA.SixteenRows7x17From887.row887,OMA.SixteenRows7x17From907.row907,OMA.SixteenRows7x17From911.row911,OMA.SixteenRows7x17From919.row919,OMA.SixteenRows7x17From929.row929,OMA.SixteenRows7x17From937.row937,OMA.SixteenRows7x17From941.row941,OMA.SixteenRows7x17From947.row947,OMA.SixteenRows7x17From953.row953,OMA.SixteenRows7x17From967.row967,OMA.SixteenRows7x17From971.row971,OMA.SixteenRows7x17From977.row977,OMA.SixteenRows7x17From983.row983,OMA.SixteenRows7x17From991.row991,OMA.SixteenRows7x17From997.row997,OMA.SixteenRows7x17From1009.row1009,OMA.SixteenRows7x17From1013.row1013,OMA.SixteenRows7x17From1019.row1019,OMA.SixteenRows7x17From1021.row1021,OMA.SixteenRows7x17From1031.row1031,OMA.SixteenRows7x17From1033.row1033,OMA.SixteenRows7x17From1039.row1039,OMA.SixteenRows7x17From1049.row1049,OMA.SixteenRows7x17From1051.row1051,OMA.SixteenRows7x17From1061.row1061,OMA.SixteenRows7x17From1063.row1063,OMA.SixteenRows7x17From1069.row1069,OMA.SixteenRows7x17From1087.row1087,OMA.SixteenRows7x17From1091.row1091,OMA.SixteenRows7x17From1093.row1093,OMA.SixteenRows7x17From1097.row1097,OMA.SixteenRows7x17From1103.row1103,OMA.SixteenRows7x17From1109.row1109,OMA.SixteenRows7x17From1117.row1117,OMA.SixteenRows7x17From1123.row1123,OMA.SixteenRows7x17From1129.row1129,OMA.SixteenRows7x17From1151.row1151,OMA.SixteenRows7x17From1153.row1153,OMA.SixteenRows7x17From1163.row1163,OMA.SixteenRows7x17From1171.row1171,OMA.SixteenRows7x17From1181.row1181,OMA.SixteenRows7x17From1187.row1187,OMA.SixteenRows7x17From1193.row1193,OMA.SixteenRows7x17From1201.row1201,OMA.SixteenRows7x17From1213.row1213,OMA.SixteenRows7x17From1217.row1217,OMA.SixteenRows7x17From1223.row1223,OMA.SixteenRows7x17From1229.row1229,OMA.SixteenRows7x17From1231.row1231,OMA.SixteenRows7x17From1237.row1237,OMA.SixteenRows7x17From1249.row1249,OMA.SixteenRows7x17From1259.row1259,OMA.SixteenRows7x17From1277.row1277,OMA.SixteenRows7x17From1279.row1279,OMA.SixteenRows7x17From1283.row1283,OMA.SixteenRows7x17From1289.row1289,OMA.SixteenRows7x17From1291.row1291,OMA.SixteenRows7x17From1297.row1297,OMA.SixteenRows7x17From1301.row1301,OMA.SixteenRows7x17From1303.row1303,OMA.SixteenRows7x17From1307.row1307,OMA.SixteenRows7x17From1319.row1319,OMA.SixteenRows7x17From1321.row1321,OMA.SixteenRows7x17From1327.row1327,OMA.SixteenRows7x17From1361.row1361,OMA.SixteenRows7x17From1367.row1367,OMA.SixteenRows7x17From1373.row1373,OMA.SixteenRows7x17From1381.row1381,OMA.SixteenRows7x17From1399.row1399,OMA.SixteenRows7x17From1409.row1409,OMA.SixteenRows7x17From1423.row1423,OMA.SixteenRows7x17From1427.row1427,OMA.SixteenRows7x17From1429.row1429,OMA.SixteenRows7x17From1433.row1433,OMA.SixteenRows7x17From1439.row1439,OMA.SixteenRows7x17From1447.row1447,OMA.SixteenRows7x17From1451.row1451,OMA.SixteenRows7x17From1453.row1453,OMA.SixteenRows7x17From1459.row1459,OMA.SixteenRows7x17From1471.row1471,OMA.SixteenRows7x17From1481.row1481,OMA.SixteenRows7x17From1483.row1483,OMA.SixteenRows7x17From1487.row1487,OMA.SixteenRows7x17From1489.row1489,OMA.SixteenRows7x17From1493.row1493,OMA.SixteenRows7x17From1499.row1499,OMA.SixteenRows7x17From1511.row1511,OMA.SixteenRows7x17From1523.row1523,OMA.SixteenRows7x17From1531.row1531,OMA.SixteenRows7x17From1543.row1543,OMA.SixteenRows7x17From1549.row1549,OMA.SixteenRows7x17From1553.row1553,OMA.SixteenRows7x17From1559.row1559,OMA.SixteenRows7x17From1567.row1567,OMA.SixteenRows7x17From1571.row1571,OMA.SixteenRows7x17From1579.row1579,OMA.SixteenRows7x17From1583.row1583,OMA.SixteenRows7x17From1597.row1597,OMA.SixteenRows7x17From1601.row1601,OMA.SixteenRows7x17From1607.row1607,OMA.SixteenRows7x17From1609.row1609,OMA.SixteenRows7x17From1613.row1613,OMA.SixteenRows7x17From1619.row1619,OMA.SixteenRows7x17From1621.row1621,OMA.SixteenRows7x17From1627.row1627,OMA.SixteenRows7x17From1637.row1637,OMA.SixteenRows7x17From1657.row1657,OMA.SixteenRows7x17From1663.row1663,OMA.SixteenRows7x17From1667.row1667,OMA.SixteenRows7x17From1669.row1669,OMA.SixteenRows7x17From1693.row1693,OMA.SixteenRows7x17From1697.row1697,OMA.SixteenRows7x17From1699.row1699,fun _ h=>h.elim⟩
theorem original {r a b c : ℕ} (pr : r.Prime) (large : 17<r) (ap : 0<a) (bp : 0<b) (cp : 0<c) :
    OeisA245212.a (16*7^a*17^b*r^c)≠(σ 1 (16*7^a*17^b*r^c):ℤ) := by
  intro eqn
  have ec:=(necessary (p:=7) (q:=17) (by decide) (by decide) pr (by decide) (by decide) large ap eqn).1
  have num:=integer_cap (by decide : Nat.Prime 7) (by decide : Nat.Prime 17) pr ec
  have rb : r≤1706 := by omega
  have allr:=of_decide_eq_true (OMA.CofactorEulerPair245212.checked choices large rb)
  have yes:=passed r (allr ((OMA.KernelPrimeWindow245212.correct _).mpr pr))
  exact OMA.SixteenMin245212.original (p:=7) (q:=17) (by decide) (by decide) pr (by decide : 7≤7) (by decide) large (by omega) ap bp cp yes eqn
end OMA.SixteenFamily7x17

end

section

namespace OMA.SixteenRows7x19From23
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row23 : OMA.SixteenTable245212.tables 7 19 23=true := by
  apply OMA.SixteenCert245212.fixed <;> decide +kernel
end OMA.SixteenRows7x19From23

end

section

namespace OMA.SixteenRows7x19From29
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row29 : OMA.SixteenTable245212.tables 7 19 29=true := by
  apply OMA.SixteenCert245212.fixed <;> decide +kernel
end OMA.SixteenRows7x19From29

end

section

namespace OMA.SixteenRows7x19From31
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row31 : OMA.SixteenTable245212.tables 7 19 31=true := by
  apply OMA.SixteenCert245212.fixed <;> decide +kernel
end OMA.SixteenRows7x19From31

end

section

namespace OMA.SixteenRows7x19From37
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row37 : OMA.SixteenTable245212.tables 7 19 37=true := by
  apply OMA.SixteenCert245212.fixed <;> decide +kernel
end OMA.SixteenRows7x19From37

end

section

namespace OMA.SixteenRows7x19From41
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row41 : OMA.SixteenTable245212.tables 7 19 41=true := by
  apply OMA.SixteenCert245212.fixed <;> decide +kernel
end OMA.SixteenRows7x19From41

end

section

namespace OMA.SixteenRows7x19From43
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row43 : OMA.SixteenTable245212.tables 7 19 43=true := by
  apply OMA.SixteenCert245212.fixed <;> decide +kernel
end OMA.SixteenRows7x19From43

end

section

namespace OMA.SixteenRows7x19From47
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row47 : OMA.SixteenTable245212.tables 7 19 47=true := by
  apply OMA.SixteenCert245212.fixed <;> decide +kernel
end OMA.SixteenRows7x19From47

end

section

namespace OMA.SixteenRows7x19From53
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row53 : OMA.SixteenTable245212.tables 7 19 53=true := by
  apply OMA.SixteenCert245212.fixed <;> decide +kernel
end OMA.SixteenRows7x19From53

end

section

namespace OMA.SixteenRows7x19From59
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row59 : OMA.SixteenTable245212.tables 7 19 59=true := by
  apply OMA.SixteenCert245212.fixed <;> decide +kernel
end OMA.SixteenRows7x19From59

end

section

namespace OMA.SixteenRows7x19From61
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row61 : OMA.SixteenTable245212.tables 7 19 61=true := by
  apply OMA.SixteenCert245212.fixed <;> decide +kernel
end OMA.SixteenRows7x19From61

end

section

namespace OMA.SixteenRows7x19From67
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row67 : OMA.SixteenTable245212.tables 7 19 67=true := by
  apply OMA.SixteenCert245212.fixed <;> decide +kernel
end OMA.SixteenRows7x19From67

end

section

namespace OMA.SixteenRows7x19From71
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row71 : OMA.SixteenTable245212.tables 7 19 71=true := by
  apply OMA.SixteenCert245212.fixed <;> decide +kernel
end OMA.SixteenRows7x19From71

end

section

namespace OMA.SixteenRows7x19From73
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row73 : OMA.SixteenTable245212.tables 7 19 73=true := by
  apply OMA.SixteenCert245212.fixed <;> decide +kernel
end OMA.SixteenRows7x19From73

end

section

namespace OMA.SixteenRows7x19From79
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row79 : OMA.SixteenTable245212.tables 7 19 79=true := by
  apply OMA.SixteenCert245212.fixed <;> decide +kernel
end OMA.SixteenRows7x19From79

end

section

namespace OMA.SixteenRows7x19From83
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row83 : OMA.SixteenTable245212.tables 7 19 83=true := by
  apply OMA.SixteenCert245212.fixed <;> decide +kernel
end OMA.SixteenRows7x19From83

end

section

namespace OMA.SixteenRows7x19From89
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row89 : OMA.SixteenTable245212.tables 7 19 89=true := by
  apply OMA.SixteenCert245212.fixed <;> decide +kernel
end OMA.SixteenRows7x19From89

end

section

namespace OMA.SixteenRows7x19From97
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row97 : OMA.SixteenTable245212.tables 7 19 97=true := by
  apply OMA.SixteenCert245212.fixed <;> decide +kernel
end OMA.SixteenRows7x19From97

end

section

namespace OMA.SixteenRows7x19From101
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row101 : OMA.SixteenTable245212.tables 7 19 101=true := by
  apply OMA.SixteenCert245212.fixed <;> decide +kernel
end OMA.SixteenRows7x19From101

end

section

namespace OMA.SixteenRows7x19From103
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row103 : OMA.SixteenTable245212.tables 7 19 103=true := by
  apply OMA.SixteenCert245212.fixed <;> decide +kernel
end OMA.SixteenRows7x19From103

end

section

namespace OMA.SixteenRows7x19From107
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row107 : OMA.SixteenTable245212.tables 7 19 107=true := by
  apply OMA.SixteenCert245212.fixed <;> decide +kernel
end OMA.SixteenRows7x19From107

end

section

namespace OMA.SixteenRows7x19From109
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row109 : OMA.SixteenTable245212.tables 7 19 109=true := by
  apply OMA.SixteenCert245212.fixed <;> decide +kernel
end OMA.SixteenRows7x19From109

end

section

namespace OMA.SixteenRows7x19From113
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row113 : OMA.SixteenTable245212.tables 7 19 113=true := by
  apply OMA.SixteenCert245212.fixed <;> decide +kernel
end OMA.SixteenRows7x19From113

end

section

namespace OMA.SixteenRows7x19From127
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row127 : OMA.SixteenTable245212.tables 7 19 127=true := by
  apply OMA.SixteenCert245212.fixed <;> decide +kernel
end OMA.SixteenRows7x19From127

end

section

namespace OMA.SixteenRows7x19From131
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row131 : OMA.SixteenTable245212.tables 7 19 131=true := by
  apply OMA.SixteenCert245212.fixed <;> decide +kernel
end OMA.SixteenRows7x19From131

end

section

namespace OMA.SixteenRows7x19From137
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row137 : OMA.SixteenTable245212.tables 7 19 137=true := by
  apply OMA.SixteenCert245212.fixed <;> decide +kernel
end OMA.SixteenRows7x19From137

end

section

namespace OMA.SixteenRows7x19From139
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row139 : OMA.SixteenTable245212.tables 7 19 139=true := by
  apply OMA.SixteenCert245212.fixed <;> decide +kernel
end OMA.SixteenRows7x19From139

end

section

/- All values of the terminal prime and of all three exponents. -/
namespace OMA.SixteenFamily7x19
open OMA.SixteenTable245212 OMA.CofactorEulerPair245212 OMA.RankThreeSixteenSupport245212
open scoped ArithmeticFunction.sigma
open OMA.CofactorEulerPair245212 (checked)
set_option maxRecDepth 65536
private def allowed : List ℕ := [23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139]
private theorem choices : every 20 140 (fun r=>decide (OMA.KernelPrimeWindow245212.trial r=true → r∈allowed))=true := by decide +kernel
private theorem passed : ∀ r∈allowed,tables 7 19 r=true := by
  simp only [allowed,List.forall_mem_cons,List.not_mem_nil]
  exact ⟨OMA.SixteenRows7x19From23.row23,OMA.SixteenRows7x19From29.row29,OMA.SixteenRows7x19From31.row31,OMA.SixteenRows7x19From37.row37,OMA.SixteenRows7x19From41.row41,OMA.SixteenRows7x19From43.row43,OMA.SixteenRows7x19From47.row47,OMA.SixteenRows7x19From53.row53,OMA.SixteenRows7x19From59.row59,OMA.SixteenRows7x19From61.row61,OMA.SixteenRows7x19From67.row67,OMA.SixteenRows7x19From71.row71,OMA.SixteenRows7x19From73.row73,OMA.SixteenRows7x19From79.row79,OMA.SixteenRows7x19From83.row83,OMA.SixteenRows7x19From89.row89,OMA.SixteenRows7x19From97.row97,OMA.SixteenRows7x19From101.row101,OMA.SixteenRows7x19From103.row103,OMA.SixteenRows7x19From107.row107,OMA.SixteenRows7x19From109.row109,OMA.SixteenRows7x19From113.row113,OMA.SixteenRows7x19From127.row127,OMA.SixteenRows7x19From131.row131,OMA.SixteenRows7x19From137.row137,OMA.SixteenRows7x19From139.row139,fun _ h=>h.elim⟩
theorem original {r a b c : ℕ} (pr : r.Prime) (large : 19<r) (ap : 0<a) (bp : 0<b) (cp : 0<c) :
    OeisA245212.a (16*7^a*19^b*r^c)≠(σ 1 (16*7^a*19^b*r^c):ℤ) := by
  intro eqn
  have ec:=(necessary (p:=7) (q:=19) (by decide) (by decide) pr (by decide) (by decide) large ap eqn).1
  have num:=integer_cap (by decide : Nat.Prime 7) (by decide : Nat.Prime 19) pr ec
  have rb : r≤140 := by omega
  have allr:=of_decide_eq_true (OMA.CofactorEulerPair245212.checked choices large rb)
  have yes:=passed r (allr ((OMA.KernelPrimeWindow245212.correct _).mpr pr))
  exact OMA.SixteenTable245212.original (p:=7) (q:=19) (by decide) (by decide) pr (by decide) (by decide) large (by omega) ap bp cp yes eqn
end OMA.SixteenFamily7x19

end

section

namespace OMA.SixteenRows7x23From29
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row29 : OMA.SixteenTable245212.tables 7 23 29=true := by
  apply OMA.SixteenCert245212.fixed <;> decide +kernel
end OMA.SixteenRows7x23From29

end

section

namespace OMA.SixteenRows7x23From31
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row31 : OMA.SixteenTable245212.tables 7 23 31=true := by
  apply OMA.SixteenCert245212.fixed <;> decide +kernel
end OMA.SixteenRows7x23From31

end

section

namespace OMA.SixteenRows7x23From37
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row37 : OMA.SixteenTable245212.tables 7 23 37=true := by
  apply OMA.SixteenCert245212.fixed <;> decide +kernel
end OMA.SixteenRows7x23From37

end

section

namespace OMA.SixteenRows7x23From41
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row41 : OMA.SixteenTable245212.tables 7 23 41=true := by
  apply OMA.SixteenCert245212.fixed <;> decide +kernel
end OMA.SixteenRows7x23From41

end

section

namespace OMA.SixteenRows7x23From43
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row43 : OMA.SixteenTable245212.tables 7 23 43=true := by
  apply OMA.SixteenCert245212.fixed <;> decide +kernel
end OMA.SixteenRows7x23From43

end

section

namespace OMA.SixteenRows7x23From47
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row47 : OMA.SixteenTable245212.tables 7 23 47=true := by
  apply OMA.SixteenCert245212.fixed <;> decide +kernel
end OMA.SixteenRows7x23From47

end

section

namespace OMA.SixteenRows7x23From53
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row53 : OMA.SixteenTable245212.tables 7 23 53=true := by
  apply OMA.SixteenCert245212.fixed <;> decide +kernel
end OMA.SixteenRows7x23From53

end

section

namespace OMA.SixteenRows7x23From59
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row59 : OMA.SixteenTable245212.tables 7 23 59=true := by
  apply OMA.SixteenCert245212.fixed <;> decide +kernel
end OMA.SixteenRows7x23From59

end

section

/- All values of the terminal prime and of all three exponents. -/
namespace OMA.SixteenFamily7x23
open OMA.SixteenTable245212 OMA.CofactorEulerPair245212 OMA.RankThreeSixteenSupport245212
open scoped ArithmeticFunction.sigma
open OMA.CofactorEulerPair245212 (checked)
set_option maxRecDepth 65536
private def allowed : List ℕ := [29,31,37,41,43,47,53,59]
private theorem choices : every 24 60 (fun r=>decide (OMA.KernelPrimeWindow245212.trial r=true → r∈allowed))=true := by decide +kernel
private theorem passed : ∀ r∈allowed,tables 7 23 r=true := by
  simp only [allowed,List.forall_mem_cons,List.not_mem_nil]
  exact ⟨OMA.SixteenRows7x23From29.row29,OMA.SixteenRows7x23From31.row31,OMA.SixteenRows7x23From37.row37,OMA.SixteenRows7x23From41.row41,OMA.SixteenRows7x23From43.row43,OMA.SixteenRows7x23From47.row47,OMA.SixteenRows7x23From53.row53,OMA.SixteenRows7x23From59.row59,fun _ h=>h.elim⟩
theorem original {r a b c : ℕ} (pr : r.Prime) (large : 23<r) (ap : 0<a) (bp : 0<b) (cp : 0<c) :
    OeisA245212.a (16*7^a*23^b*r^c)≠(σ 1 (16*7^a*23^b*r^c):ℤ) := by
  intro eqn
  have ec:=(necessary (p:=7) (q:=23) (by decide) (by decide) pr (by decide) (by decide) large ap eqn).1
  have num:=integer_cap (by decide : Nat.Prime 7) (by decide : Nat.Prime 23) pr ec
  have rb : r≤60 := by omega
  have allr:=of_decide_eq_true (OMA.CofactorEulerPair245212.checked choices large rb)
  have yes:=passed r (allr ((OMA.KernelPrimeWindow245212.correct _).mpr pr))
  exact OMA.SixteenTable245212.original (p:=7) (q:=23) (by decide) (by decide) pr (by decide) (by decide) large (by omega) ap bp cp yes eqn
end OMA.SixteenFamily7x23

end

section

namespace OMA.SixteenRows7x29From31
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row31 : OMA.SixteenTable245212.tables 7 29 31=true := by
  apply OMA.SixteenCert245212.fixed <;> decide +kernel
end OMA.SixteenRows7x29From31

end

section

namespace OMA.SixteenRows7x29From37
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row37 : OMA.SixteenTable245212.tables 7 29 37=true := by
  apply OMA.SixteenCert245212.fixed <;> decide +kernel
end OMA.SixteenRows7x29From37

end

section

/- All values of the terminal prime and of all three exponents. -/
namespace OMA.SixteenFamily7x29
open OMA.SixteenTable245212 OMA.CofactorEulerPair245212 OMA.RankThreeSixteenSupport245212
open scoped ArithmeticFunction.sigma
open OMA.CofactorEulerPair245212 (checked)
set_option maxRecDepth 65536
private def allowed : List ℕ := [31,37]
private theorem choices : every 30 38 (fun r=>decide (OMA.KernelPrimeWindow245212.trial r=true → r∈allowed))=true := by decide +kernel
private theorem passed : ∀ r∈allowed,tables 7 29 r=true := by
  simp only [allowed,List.forall_mem_cons,List.not_mem_nil]
  exact ⟨OMA.SixteenRows7x29From31.row31,OMA.SixteenRows7x29From37.row37,fun _ h=>h.elim⟩
theorem original {r a b c : ℕ} (pr : r.Prime) (large : 29<r) (ap : 0<a) (bp : 0<b) (cp : 0<c) :
    OeisA245212.a (16*7^a*29^b*r^c)≠(σ 1 (16*7^a*29^b*r^c):ℤ) := by
  intro eqn
  have ec:=(necessary (p:=7) (q:=29) (by decide) (by decide) pr (by decide) (by decide) large ap eqn).1
  have num:=integer_cap (by decide : Nat.Prime 7) (by decide : Nat.Prime 29) pr ec
  have rb : r≤38 := by omega
  have allr:=of_decide_eq_true (OMA.CofactorEulerPair245212.checked choices large rb)
  have yes:=passed r (allr ((OMA.KernelPrimeWindow245212.correct _).mpr pr))
  exact OMA.SixteenTable245212.original (p:=7) (q:=29) (by decide) (by decide) pr (by decide) (by decide) large (by omega) ap bp cp yes eqn
end OMA.SixteenFamily7x29

end

section

namespace OMA.SixteenRows11x13From17
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row17 : OMA.SixteenTable245212.tables 11 13 17=true := by
  apply OMA.SixteenCert245212.fixed <;> decide +kernel
end OMA.SixteenRows11x13From17

end

section

namespace OMA.SixteenRows11x13From19
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row19 : OMA.SixteenTable245212.tables 11 13 19=true := by
  apply OMA.SixteenCert245212.fixed <;> decide +kernel
end OMA.SixteenRows11x13From19

end

section

namespace OMA.SixteenRows11x13From23
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
theorem row23 : OMA.SixteenTable245212.tables 11 13 23=true := by
  apply OMA.SixteenCert245212.fixed <;> decide +kernel
end OMA.SixteenRows11x13From23

end

section

/- All values of the terminal prime and of all three exponents. -/
namespace OMA.SixteenFamily11x13
open OMA.SixteenTable245212 OMA.CofactorEulerPair245212 OMA.RankThreeSixteenSupport245212
open scoped ArithmeticFunction.sigma
open OMA.CofactorEulerPair245212 (checked)
set_option maxRecDepth 65536
private def allowed : List ℕ := [17,19,23]
private theorem choices : every 14 25 (fun r=>decide (OMA.KernelPrimeWindow245212.trial r=true → r∈allowed))=true := by decide +kernel
private theorem passed : ∀ r∈allowed,tables 11 13 r=true := by
  simp only [allowed,List.forall_mem_cons,List.not_mem_nil]
  exact ⟨OMA.SixteenRows11x13From17.row17,OMA.SixteenRows11x13From19.row19,OMA.SixteenRows11x13From23.row23,fun _ h=>h.elim⟩
theorem original {r a b c : ℕ} (pr : r.Prime) (large : 13<r) (ap : 0<a) (bp : 0<b) (cp : 0<c) :
    OeisA245212.a (16*11^a*13^b*r^c)≠(σ 1 (16*11^a*13^b*r^c):ℤ) := by
  intro eqn
  have ec:=(necessary (p:=11) (q:=13) (by decide) (by decide) pr (by decide) (by decide) large ap eqn).1
  have num:=integer_cap (by decide : Nat.Prime 11) (by decide : Nat.Prime 13) pr ec
  have rb : r≤25 := by omega
  have allr:=of_decide_eq_true (OMA.CofactorEulerPair245212.checked choices large rb)
  have yes:=passed r (allr ((OMA.KernelPrimeWindow245212.correct _).mpr pr))
  exact OMA.SixteenTable245212.original (p:=11) (q:=13) (by decide) (by decide) pr (by decide) (by decide) large (by omega) ap bp cp yes eqn
end OMA.SixteenFamily11x13

end

section

/- There are no divisor-balance solutions with exact dyadic order four,
three odd prime factors, and least odd prime at least seven. -/
namespace OMA.RankThreeSixteenLarge245212
open Nat Finset
open scoped ArithmeticFunction.sigma

theorem vector {p q r a b c : ℕ} (pp : p.Prime) (qp : q.Prime) (rp : r.Prime)
    (p7 : 7≤p) (pq : p<q) (qr : q<r) (ap : 0<a) (bp : 0<b) (cp : 0<c) :
    OeisA245212.a (16*p^a*q^b*r^c)≠(σ 1 (16*p^a*q^b*r^c):ℤ) :=
  OMA.SixteenFamiliesJoin245212.join
    @OMA.SixteenMoving7P11.exclude @OMA.SixteenMoving7P13.exclude @OMA.SixteenFamily7x17.original @OMA.SixteenFamily7x19.original @OMA.SixteenFamily7x23.original @OMA.SixteenFamily7x29.original @OMA.SixteenFamily11x13.original
    pp qp rp p7 pq qr ap bp cp

theorem odd_part {m : ℕ} (odd : Odd m) (rank : m.primeFactors.card=3)
    (least7 : ∀ p∈m.primeFactors, 7≤p) :
    OeisA245212.a (16*m)≠(σ 1 (16*m):ℤ) := by
  let P : Fin 3 ↪o ℕ := m.primeFactors.orderEmbOfFin rank
  let e (i : Fin 3):=m.factorization (P i)
  have mem (i : Fin 3) : P i∈m.primeFactors := m.primeFactors.orderEmbOfFin_mem rank i
  have pr (i) := prime_of_mem_primeFactors (mem i)
  have ep (i) : 0<e i := (pr i).factorization_pos_of_dvd odd.pos.ne' (dvd_of_mem_primeFactors (mem i))
  have least : 7≤P 0 := least7 _ (mem 0)
  have prod:=Nat.prod_primeFactors_pow_factorization odd.pos.ne'
  have lift : Finset.univ.map P.toEmbedding=m.primeFactors := m.primeFactors.map_orderEmbOfFin_univ rank
  rw [←lift,prod_map,Fin.prod_univ_three] at prod
  change m=(P 0)^(e 0)*(P 1)^(e 1)*(P 2)^(e 2) at prod
  have repr : 16*m=16*(P 0)^(e 0)*(P 1)^(e 1)*(P 2)^(e 2) := by
    simpa only [mul_assoc] using congrArg (16*·) prod
  rw [repr]
  exact vector (pr 0) (pr 1) (pr 2) least (P.strictMono (by decide : (0:Fin 3)<1))
    (P.strictMono (by decide : (1:Fin 3)<2)) (ep 0) (ep 1) (ep 2)

theorem original {n : ℕ} (pos : 0<n) (v2 : n.factorization 2=4)
    (rank : (n.primeFactors.erase 2).card=3) (least7 : ∀p∈n.primeFactors.erase 2,7≤p) : OeisA245212.a n≠(σ 1 n:ℤ) := by
  let m:=ordCompl[2] n
  have cm : Odd m:=Nat.coprime_two_left.mp (Nat.coprime_ordCompl prime_two pos.ne')
  have ss : m.primeFactors=n.primeFactors.erase 2 := by
    dsimp [m];rw [←Nat.support_factorization,Nat.factorization_ordCompl,Finsupp.support_erase,Nat.support_factorization]
  have id : 16*m=n := by simpa only [v2,show 2^4=16 by decide,m] using Nat.ordProj_mul_ordCompl_eq_self n 2
  simpa only [id] using odd_part cm (ss ▸ rank) (by rwa [ss])

end OMA.RankThreeSixteenLarge245212

end

#print axioms OMA.RankThreeSixteenLarge245212.original
