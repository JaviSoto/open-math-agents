import FormalConjectures.OEIS.«245212»

/-! A uniform prime bound and effective fixed-support decision procedure for OEIS A245212. -/

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

end OMA.Smooth245212

namespace OMA.Abundance245212
open OMA.Smooth245212 Finset ArithmeticFunction Nat
open scoped ArithmeticFunction.sigma
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

namespace OMA.Large245212
abbrev cutoff : ℕ := 1000000000000000000
end OMA.Large245212

namespace OMA.Smooth245212
structure Band where
  lo : ℕ
  hi : Option ℕ
  deriving DecidableEq

def Band.Contains (b : Band) (e : ℕ) := b.lo≤e ∧ ∀ h, b.hi=some h → e≤h
end OMA.Smooth245212

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

namespace OMA.OddFaces245212
open Finset OMA.Smooth245212
private theorem compare4 {p u : Fin 4 → ℕ} (h : ∀ i,1<u i) (lower : ∀ i,u i≤p i) :
    (∏ i,limitX (p i))≤∏ i,limitX (u i) := by
  exact prod_le_prod (f:=fun i => limitX (p i)) (g:=fun i => limitX (u i))
    (fun i _ => x_nonneg ((h i).trans_le (lower i)) none)
    (fun i _ => cap_anti (h i) (lower i))

private theorem prime_at_least {p t : ℕ} (hp : Nat.Prime p) (lo : t≤p)
    (no : ¬Nat.Prime t) : t<p := lt_of_le_of_ne lo (fun eq => no (eq ▸ hp))

theorem small_bases {p : Fin 4 → ℕ} (hp : ∀ i,Nat.Prime (p i)) (ord : StrictMono p)
    (odd : 3≤p 0) (big : 257≤p 3) (cap : 2≤∏ i,limitX (p i)) :
    p 0=3 ∧ p 1=5 ∧ (p 2=7 ∨ p 2=11 ∨ p 2=13) := by
  have h01 := ord (by decide : (0:Fin 4)<1)
  have h12 := ord (by decide : (1:Fin 4)<2)
  have h23 := ord (by decide : (2:Fin 4)<3)
  have drop (u : Fin 4 → ℕ) (a : ∀ i,1<u i) (b : ∀ i,u i≤p i)
      (c : (∏ i,limitX (u i))<2) : False := (cap.trans (compare4 a b)).not_gt c
  have first : p 0=3 := by
    by_contra! ne
    have h0 := prime_at_least (hp 0) (by omega : 4≤p 0) (by decide)
    apply drop ![5,6,7,257] (by decide) _ (by decide +kernel)
    intro i; fin_cases i <;> simp <;> omega
  have h1 := prime_at_least (hp 1) (by omega : 4≤p 1) (by decide)
  have second : p 1=5 := by
    by_contra! ne
    have h1' := prime_at_least (hp 1) (by omega : 6≤p 1) (by decide)
    have h2 := prime_at_least (hp 2) (by omega : 8≤p 2) (by decide)
    apply drop ![3,7,9,257] (by decide) _ (by decide +kernel)
    intro i; fin_cases i <;> simp <;> omega
  have third : p 2<17 := by
    by_contra! zl
    apply drop ![3,5,17,257] (by decide) _ (by decide +kernel)
    intro i; fin_cases i <;> simp <;> omega
  refine ⟨first,second,?_⟩
  have h2 := hp 2
  have lb : 6≤p 2 := by omega
  generalize p 2=u at h2 lb third ⊢
  interval_cases u <;> norm_num at *
end OMA.OddFaces245212

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

/- Closed prime-power moments and the integer test at exact prefix leaves. -/
namespace OMA.Large245212
open OMA.Smooth245212 OMA.LastDigit245212 Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma Function

def tax (p e : ℕ) := (e+1)*p^e
def sig (p e : ℕ) := (p^(e+1)-1)/(p-1)
def wt (p e : ℕ) := (p*tax p e-sig p e)/(p-1)

private theorem moments {p : ℕ} (hp : Nat.Prime p) (e : ℕ) :
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

private theorem force {A S T d p : ℕ} (hs : 0<S) (hp : 1<p) (hD : 0<denom A S T d)
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

/- A prefix-code tree for excluding large fourth primes. The split
locations are recomputed from the box, so just two bits describe each node. -/
namespace OMA.Large245212
open OMA.Smooth245212 OMA.Moving245212 Finset
open scoped ArithmeticFunction.sigma

def Deny (R q : ℕ) (b : B) := ∀ (e : Fin 3 → ℕ), (∀ i,(b i).Contains (e i)) →
  ∀ r d : ℕ, Nat.Prime r → 0<d → R≤r → (prev q e).Coprime r →
  prefProd X q e*X r (some d)+prefProd Y q e*Y r (some d)=2 →
  OeisA245212.a (prev q e*r^d)≠(σ 1 (prev q e*r^d):ℤ)

def leaf (R q : ℕ) (b : B) :=
  let L:=lows xl q b; let U:=lows xu q b; let G:=lows yl q b; let V:=lows yu q b;
  let c:=scale R; let lo:=lowerD L G; let hi:=upperD c U V; let e:=fun i => (b i).lo
  decide (2≤L ∨ (U+V/2)*c<2 ∨ 0<2-U*c ∧ (hi<lo ∨
    (∀ i,(b i).hi=some (b i).lo) ∧ ∀ t∈Icc lo hi,test R (full wt q e) (full sig q e) (full tax q e) t=true))

theorem leaf_sound {R q : ℕ} (R1 : 1<R) (hq : q=7 ∨ q=11 ∨ q=13) {b : B}
    (cert : leaf R q b=true) : Deny R q b := by
  intro e inside r d hp hd big cop score eq
  have hq1 : 1<q := by rcases hq with rfl|rfl|rfl <;> decide
  have w := window R1 big hq1 hd b e inside score
  rcases of_decide_eq_true cert with gt|lt|⟨pos,range|⟨single,all⟩⟩
  · exact w.xl.not_ge gt
  · exact w.coarse.not_gt lt
  · exact (w.low.trans (w.high pos)).not_gt range
  · have same : (fun i => (b i).lo)=e := funext fun i =>
      le_antisymm (inside i).1 ((inside i).2 _ (single i))
    have checked := all (d+1) (mem_Icc.mpr ⟨w.low,w.high pos⟩)
    rw [same,valid_exact hq e hp hd R big cop eq] at checked
    contradiction

def cutAt (a : Band) := match a.hi with
  | none => 2*a.lo+1
  | some h => max a.lo (min (h-1) (2*(a.lo+1)*(h+1)/(a.lo+h+2)-1))
def leftB (b : B) (i : Fin 3) : B := Function.update b i ⟨(b i).lo,some (cutAt (b i))⟩
def rightB (b : B) (i : Fin 3) : B := Function.update b i ⟨cutAt (b i)+1,(b i).hi⟩

theorem split {R q : ℕ} (b : B) (i : Fin 3) (l : Deny R q (leftB b i)) (r : Deny R q (rightB b i)) :
    Deny R q b := by
  intro e inside
  by_cases low : e i≤cutAt (b i)
  · apply l
    intro j; by_cases ji : j=i
    · subst j; simpa [leftB,Band.Contains] using And.intro (inside i).1 low
    · simpa [leftB,ji] using inside j
  · apply r
    intro j; by_cases ji : j=i
    · subst j; simpa [rightB,Band.Contains] using And.intro (by omega : cutAt (b i)+1≤e i) (inside i).2
    · simpa [rightB,ji] using inside j

def axis (word : ℕ) : Fin 3 := Fin.ofNat 3 (word%4-1)
def run (R q : ℕ) : ℕ → ℕ → B → Option ℕ
| 0,_,_ => none
| f+1,w,b =>
  if w%4=0 then if leaf R q b then some (w/4) else none
  else (run R q f (w/4) (leftB b (axis w))).bind (fun rest => run R q f rest (rightB b (axis w)))

theorem sound {R q : ℕ} (hR : 1<R) (hq : q=7 ∨ q=11 ∨ q=13) (f w : ℕ) {tail : ℕ} {b : B}
    (cert : run R q f w b=some tail) : Deny R q b := by
  induction f generalizing w tail b with
  | zero => simp [run] at cert
  | succ f ih =>
    by_cases tip : w%4=0
    · by_cases yes : leaf R q b=true
      · exact leaf_sound hR hq yes
      · simp [run,tip,yes] at cert
    · cases l : run R q f (w/4) (leftB b (axis w)) with
      | none => simp [run,tip,l] at cert
      | some rest =>
        exact split b (axis w) (ih _ l) (ih rest (by simpa [run,tip,l] using cert))

def start : B := fun _ => ⟨1,none⟩
end OMA.Large245212

/- Exact large-prime arithmetic certificate from large_last_245212.py. -/
namespace OMA.Large245212
private def bp7x1 : B := ![⟨1,some 3⟩,⟨1,none⟩,⟨1,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x1 : Deny 1000000000000000000 7 bp7x1 :=
  sound (by decide) (by decide) 2 2 (tail:=0) (by decide +kernel)
private def bp7x4 : B := ![⟨4,none⟩,⟨1,none⟩,⟨1,none⟩]
private def bp7x5 : B := ![⟨4,none⟩,⟨1,some 3⟩,⟨1,none⟩]
private def bp7x6 : B := ![⟨4,some 9⟩,⟨1,some 3⟩,⟨1,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x6 : Deny 1000000000000000000 7 bp7x6 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp7x7 : B := ![⟨10,none⟩,⟨1,some 3⟩,⟨1,none⟩]
private def bp7x8 : B := ![⟨10,none⟩,⟨1,some 3⟩,⟨1,some 3⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x8 : Deny 1000000000000000000 7 bp7x8 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp7x9 : B := ![⟨10,none⟩,⟨1,some 3⟩,⟨4,none⟩]
private def bp7x10 : B := ![⟨10,none⟩,⟨1,some 1⟩,⟨4,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x10 : Deny 1000000000000000000 7 bp7x10 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp7x11 : B := ![⟨10,none⟩,⟨2,some 3⟩,⟨4,none⟩]
private def bp7x12 : B := ![⟨10,some 21⟩,⟨2,some 3⟩,⟨4,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x12 : Deny 1000000000000000000 7 bp7x12 :=
  sound (by decide) (by decide) 19 348125124684521755609490311241395566883347 (tail:=0) (by decide +kernel)
private def bp7x89 : B := ![⟨22,none⟩,⟨2,some 3⟩,⟨4,none⟩]
private def bp7x90 : B := ![⟨22,none⟩,⟨2,some 3⟩,⟨4,some 9⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x90 : Deny 1000000000000000000 7 bp7x90 :=
  sound (by decide) (by decide) 19 437590918020134875709605246735920263637171891770914098747069217 (tail:=0) (by decide +kernel)
private def bp7x203 : B := ![⟨22,none⟩,⟨2,some 3⟩,⟨10,none⟩]
private def bp7x204 : B := ![⟨22,some 45⟩,⟨2,some 3⟩,⟨10,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x204 : Deny 1000000000000000000 7 bp7x204 :=
  sound (by decide) (by decide) 14 1558097095929717096477193612472295186938665121649519602540087118321216833477839418488460146 (tail:=0) (by decide +kernel)
private def bp7x363 : B := ![⟨46,none⟩,⟨2,some 3⟩,⟨10,none⟩]
private def bp7x364 : B := ![⟨46,none⟩,⟨2,some 2⟩,⟨10,none⟩]
private def bp7x365 : B := ![⟨46,none⟩,⟨2,some 2⟩,⟨10,some 21⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x365 : Deny 1000000000000000000 7 bp7x365 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp7x366 : B := ![⟨46,none⟩,⟨2,some 2⟩,⟨22,none⟩]
private def bp7x367 : B := ![⟨46,some 93⟩,⟨2,some 2⟩,⟨22,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x367 : Deny 1000000000000000000 7 bp7x367 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp7x368 : B := ![⟨94,none⟩,⟨2,some 2⟩,⟨22,none⟩]
private def bp7x369 : B := ![⟨94,none⟩,⟨2,some 2⟩,⟨22,some 45⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x369 : Deny 1000000000000000000 7 bp7x369 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp7x370 : B := ![⟨94,none⟩,⟨2,some 2⟩,⟨46,none⟩]
private def bp7x371 : B := ![⟨94,some 189⟩,⟨2,some 2⟩,⟨46,none⟩]
private def bp7x372 : B := ![⟨94,some 189⟩,⟨2,some 2⟩,⟨46,some 93⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x372 : Deny 1000000000000000000 7 bp7x372 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp7x373 : B := ![⟨94,some 189⟩,⟨2,some 2⟩,⟨94,none⟩]
private def bp7x374 : B := ![⟨94,some 125⟩,⟨2,some 2⟩,⟨94,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x374 : Deny 1000000000000000000 7 bp7x374 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp7x375 : B := ![⟨126,some 189⟩,⟨2,some 2⟩,⟨94,none⟩]
private def bp7x376 : B := ![⟨126,some 189⟩,⟨2,some 2⟩,⟨94,some 189⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x376 : Deny 1000000000000000000 7 bp7x376 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp7x377 : B := ![⟨126,some 189⟩,⟨2,some 2⟩,⟨190,none⟩]
private def bp7x378 : B := ![⟨126,some 151⟩,⟨2,some 2⟩,⟨190,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x378 : Deny 1000000000000000000 7 bp7x378 :=
  sound (by decide) (by decide) 27 39789850035605221556824393974825920426244404065852349462829888974601227997387117868807771979631354163644279576806993366815507 (tail:=0) (by decide +kernel)
private def bp7x593 : B := ![⟨152,some 189⟩,⟨2,some 2⟩,⟨190,none⟩]
private def bp7x594 : B := ![⟨152,some 189⟩,⟨2,some 2⟩,⟨190,some 381⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x594 : Deny 1000000000000000000 7 bp7x594 :=
  sound (by decide) (by decide) 16 633534167611339095582889415573339302984703539382831630937056999223141517835163760406011400681051393197878913918351028828782990834618986662743153 (tail:=0) (by decide +kernel)
private def bp7x841 : B := ![⟨152,some 189⟩,⟨2,some 2⟩,⟨382,none⟩]
private def bp7x842 : B := ![⟨152,some 168⟩,⟨2,some 2⟩,⟨382,none⟩]
private def bp7x843 : B := ![⟨152,some 168⟩,⟨2,some 2⟩,⟨382,some 765⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x843 : Deny 1000000000000000000 7 bp7x843 :=
  sound (by decide) (by decide) 15 505508076513544477032919635501009870803032295748008346977735350734979743971440040619301790374380953715089421868845661703281 (tail:=0) (by decide +kernel)
private def bp7x1054 : B := ![⟨152,some 168⟩,⟨2,some 2⟩,⟨766,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x1054 : Deny 1000000000000000000 7 bp7x1054 :=
  sound (by decide) (by decide) 19 11820772455675699963571836257934539226499531463707084460051641500385589452469118699219430779822133309186401880197276851021387596803953256043807165902975331737017171231687901 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p7x842 : Deny 1000000000000000000 7 bp7x842 := by
  apply split bp7x842 2
  · rw [show leftB bp7x842 2=bp7x843 by funext i; fin_cases i <;> rfl]; exact p7x843
  · rw [show rightB bp7x842 2=bp7x1054 by funext i; fin_cases i <;> rfl]; exact p7x1054
private def bp7x1349 : B := ![⟨169,some 189⟩,⟨2,some 2⟩,⟨382,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x1349 : Deny 1000000000000000000 7 bp7x1349 :=
  sound (by decide) (by decide) 15 69073189823581560714318255443939899255 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p7x841 : Deny 1000000000000000000 7 bp7x841 := by
  apply split bp7x841 0
  · rw [show leftB bp7x841 0=bp7x842 by funext i; fin_cases i <;> rfl]; exact p7x842
  · rw [show rightB bp7x841 0=bp7x1349 by funext i; fin_cases i <;> rfl]; exact p7x1349
set_option maxRecDepth 100000 in
private theorem p7x593 : Deny 1000000000000000000 7 bp7x593 := by
  apply split bp7x593 2
  · rw [show leftB bp7x593 2=bp7x594 by funext i; fin_cases i <;> rfl]; exact p7x594
  · rw [show rightB bp7x593 2=bp7x841 by funext i; fin_cases i <;> rfl]; exact p7x841
set_option maxRecDepth 100000 in
private theorem p7x377 : Deny 1000000000000000000 7 bp7x377 := by
  apply split bp7x377 0
  · rw [show leftB bp7x377 0=bp7x378 by funext i; fin_cases i <;> rfl]; exact p7x378
  · rw [show rightB bp7x377 0=bp7x593 by funext i; fin_cases i <;> rfl]; exact p7x593
set_option maxRecDepth 100000 in
private theorem p7x375 : Deny 1000000000000000000 7 bp7x375 := by
  apply split bp7x375 2
  · rw [show leftB bp7x375 2=bp7x376 by funext i; fin_cases i <;> rfl]; exact p7x376
  · rw [show rightB bp7x375 2=bp7x377 by funext i; fin_cases i <;> rfl]; exact p7x377
set_option maxRecDepth 100000 in
private theorem p7x373 : Deny 1000000000000000000 7 bp7x373 := by
  apply split bp7x373 0
  · rw [show leftB bp7x373 0=bp7x374 by funext i; fin_cases i <;> rfl]; exact p7x374
  · rw [show rightB bp7x373 0=bp7x375 by funext i; fin_cases i <;> rfl]; exact p7x375
set_option maxRecDepth 100000 in
private theorem p7x371 : Deny 1000000000000000000 7 bp7x371 := by
  apply split bp7x371 2
  · rw [show leftB bp7x371 2=bp7x372 by funext i; fin_cases i <;> rfl]; exact p7x372
  · rw [show rightB bp7x371 2=bp7x373 by funext i; fin_cases i <;> rfl]; exact p7x373
private def bp7x1424 : B := ![⟨190,none⟩,⟨2,some 2⟩,⟨46,none⟩]
private def bp7x1425 : B := ![⟨190,none⟩,⟨2,some 2⟩,⟨46,some 93⟩]
private def bp7x1426 : B := ![⟨190,some 381⟩,⟨2,some 2⟩,⟨46,some 93⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x1426 : Deny 1000000000000000000 7 bp7x1426 :=
  sound (by decide) (by decide) 17 156225044640168005756796662308779955780351162190479691173268996508760596844206188074068541277763327693587 (tail:=0) (by decide +kernel)
private def bp7x1607 : B := ![⟨382,none⟩,⟨2,some 2⟩,⟨46,some 93⟩]
private def bp7x1608 : B := ![⟨382,none⟩,⟨2,some 2⟩,⟨46,some 61⟩]
private def bp7x1609 : B := ![⟨382,some 765⟩,⟨2,some 2⟩,⟨46,some 61⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x1609 : Deny 1000000000000000000 7 bp7x1609 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp7x1610 : B := ![⟨766,none⟩,⟨2,some 2⟩,⟨46,some 61⟩]
private def bp7x1611 : B := ![⟨766,none⟩,⟨2,some 2⟩,⟨46,some 52⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x1611 : Deny 1000000000000000000 7 bp7x1611 :=
  sound (by decide) (by decide) 21 14243261768259240021603039163103205509384866916889859714280580118404080519671898260120635778035834970874613735015751883401835183361329 (tail:=0) (by decide +kernel)
private def bp7x1842 : B := ![⟨766,none⟩,⟨2,some 2⟩,⟨53,some 61⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x1842 : Deny 1000000000000000000 7 bp7x1842 :=
  sound (by decide) (by decide) 17 1223943793804438948949340461478392621780509031411437173610610025367908609017840602340826181184205147911150752750779599811019479387148122854677608204555677199141515549 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p7x1610 : Deny 1000000000000000000 7 bp7x1610 := by
  apply split bp7x1610 2
  · rw [show leftB bp7x1610 2=bp7x1611 by funext i; fin_cases i <;> rfl]; exact p7x1611
  · rw [show rightB bp7x1610 2=bp7x1842 by funext i; fin_cases i <;> rfl]; exact p7x1842
set_option maxRecDepth 100000 in
private theorem p7x1608 : Deny 1000000000000000000 7 bp7x1608 := by
  apply split bp7x1608 0
  · rw [show leftB bp7x1608 0=bp7x1609 by funext i; fin_cases i <;> rfl]; exact p7x1609
  · rw [show rightB bp7x1608 0=bp7x1610 by funext i; fin_cases i <;> rfl]; exact p7x1610
private def bp7x2129 : B := ![⟨382,none⟩,⟨2,some 2⟩,⟨62,some 93⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x2129 : Deny 1000000000000000000 7 bp7x2129 :=
  sound (by decide) (by decide) 17 96305429621891620346637392318511359409037145677997980963308422555110613662530552414788403676442264082040132828604158075298822945019040243074557009997305728410616432553280362337072702394397880952646909203778281558623453 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p7x1607 : Deny 1000000000000000000 7 bp7x1607 := by
  apply split bp7x1607 2
  · rw [show leftB bp7x1607 2=bp7x1608 by funext i; fin_cases i <;> rfl]; exact p7x1608
  · rw [show rightB bp7x1607 2=bp7x2129 by funext i; fin_cases i <;> rfl]; exact p7x2129
set_option maxRecDepth 100000 in
private theorem p7x1425 : Deny 1000000000000000000 7 bp7x1425 := by
  apply split bp7x1425 0
  · rw [show leftB bp7x1425 0=bp7x1426 by funext i; fin_cases i <;> rfl]; exact p7x1426
  · rw [show rightB bp7x1425 0=bp7x1607 by funext i; fin_cases i <;> rfl]; exact p7x1607
private def bp7x2504 : B := ![⟨190,none⟩,⟨2,some 2⟩,⟨94,none⟩]
private def bp7x2505 : B := ![⟨190,some 381⟩,⟨2,some 2⟩,⟨94,none⟩]
private def bp7x2506 : B := ![⟨190,some 381⟩,⟨2,some 2⟩,⟨94,some 189⟩]
private def bp7x2507 : B := ![⟨190,some 253⟩,⟨2,some 2⟩,⟨94,some 189⟩]
private def bp7x2508 : B := ![⟨190,some 253⟩,⟨2,some 2⟩,⟨94,some 125⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x2508 : Deny 1000000000000000000 7 bp7x2508 :=
  sound (by decide) (by decide) 13 529436564365240410648881 (tail:=0) (by decide +kernel)
private def bp7x2551 : B := ![⟨190,some 253⟩,⟨2,some 2⟩,⟨126,some 189⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x2551 : Deny 1000000000000000000 7 bp7x2551 :=
  sound (by decide) (by decide) 14 278100806588828477424009755857615427973126688386799263539225677420771755833795741193277026427993573907574437551420861203431049328168121846144892210906298082395600456286190407920228565600235314688273954315341 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p7x2507 : Deny 1000000000000000000 7 bp7x2507 := by
  apply split bp7x2507 2
  · rw [show leftB bp7x2507 2=bp7x2508 by funext i; fin_cases i <;> rfl]; exact p7x2508
  · rw [show rightB bp7x2507 2=bp7x2551 by funext i; fin_cases i <;> rfl]; exact p7x2551
private def bp7x2904 : B := ![⟨254,some 381⟩,⟨2,some 2⟩,⟨94,some 189⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x2904 : Deny 1000000000000000000 7 bp7x2904 :=
  sound (by decide) (by decide) 15 88511233415714268498816490965730956423956271527343650858835596342622751518031725693997453938976507385799613985755728132890989663357299849281075116251123120368979199335543 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p7x2506 : Deny 1000000000000000000 7 bp7x2506 := by
  apply split bp7x2506 0
  · rw [show leftB bp7x2506 0=bp7x2507 by funext i; fin_cases i <;> rfl]; exact p7x2507
  · rw [show rightB bp7x2506 0=bp7x2904 by funext i; fin_cases i <;> rfl]; exact p7x2904
private def bp7x3199 : B := ![⟨190,some 381⟩,⟨2,some 2⟩,⟨190,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x3199 : Deny 1000000000000000000 7 bp7x3199 :=
  sound (by decide) (by decide) 16 122846148997683172288249715925874161339374742092173723157470145911094428188267994451074525 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p7x2505 : Deny 1000000000000000000 7 bp7x2505 := by
  apply split bp7x2505 2
  · rw [show leftB bp7x2505 2=bp7x2506 by funext i; fin_cases i <;> rfl]; exact p7x2506
  · rw [show rightB bp7x2505 2=bp7x3199 by funext i; fin_cases i <;> rfl]; exact p7x3199
private def bp7x3360 : B := ![⟨382,none⟩,⟨2,some 2⟩,⟨94,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x3360 : Deny 1000000000000000000 7 bp7x3360 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p7x2504 : Deny 1000000000000000000 7 bp7x2504 := by
  apply split bp7x2504 0
  · rw [show leftB bp7x2504 0=bp7x2505 by funext i; fin_cases i <;> rfl]; exact p7x2505
  · rw [show rightB bp7x2504 0=bp7x3360 by funext i; fin_cases i <;> rfl]; exact p7x3360
set_option maxRecDepth 100000 in
private theorem p7x1424 : Deny 1000000000000000000 7 bp7x1424 := by
  apply split bp7x1424 2
  · rw [show leftB bp7x1424 2=bp7x1425 by funext i; fin_cases i <;> rfl]; exact p7x1425
  · rw [show rightB bp7x1424 2=bp7x2504 by funext i; fin_cases i <;> rfl]; exact p7x2504
set_option maxRecDepth 100000 in
private theorem p7x370 : Deny 1000000000000000000 7 bp7x370 := by
  apply split bp7x370 0
  · rw [show leftB bp7x370 0=bp7x371 by funext i; fin_cases i <;> rfl]; exact p7x371
  · rw [show rightB bp7x370 0=bp7x1424 by funext i; fin_cases i <;> rfl]; exact p7x1424
set_option maxRecDepth 100000 in
private theorem p7x368 : Deny 1000000000000000000 7 bp7x368 := by
  apply split bp7x368 2
  · rw [show leftB bp7x368 2=bp7x369 by funext i; fin_cases i <;> rfl]; exact p7x369
  · rw [show rightB bp7x368 2=bp7x370 by funext i; fin_cases i <;> rfl]; exact p7x370
set_option maxRecDepth 100000 in
private theorem p7x366 : Deny 1000000000000000000 7 bp7x366 := by
  apply split bp7x366 0
  · rw [show leftB bp7x366 0=bp7x367 by funext i; fin_cases i <;> rfl]; exact p7x367
  · rw [show rightB bp7x366 0=bp7x368 by funext i; fin_cases i <;> rfl]; exact p7x368
set_option maxRecDepth 100000 in
private theorem p7x364 : Deny 1000000000000000000 7 bp7x364 := by
  apply split bp7x364 2
  · rw [show leftB bp7x364 2=bp7x365 by funext i; fin_cases i <;> rfl]; exact p7x365
  · rw [show rightB bp7x364 2=bp7x366 by funext i; fin_cases i <;> rfl]; exact p7x366
private def bp7x3361 : B := ![⟨46,none⟩,⟨3,some 3⟩,⟨10,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x3361 : Deny 1000000000000000000 7 bp7x3361 :=
  sound (by decide) (by decide) 11 1341303 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p7x363 : Deny 1000000000000000000 7 bp7x363 := by
  apply split bp7x363 1
  · rw [show leftB bp7x363 1=bp7x364 by funext i; fin_cases i <;> rfl]; exact p7x364
  · rw [show rightB bp7x363 1=bp7x3361 by funext i; fin_cases i <;> rfl]; exact p7x3361
set_option maxRecDepth 100000 in
private theorem p7x203 : Deny 1000000000000000000 7 bp7x203 := by
  apply split bp7x203 0
  · rw [show leftB bp7x203 0=bp7x204 by funext i; fin_cases i <;> rfl]; exact p7x204
  · rw [show rightB bp7x203 0=bp7x363 by funext i; fin_cases i <;> rfl]; exact p7x363
set_option maxRecDepth 100000 in
private theorem p7x89 : Deny 1000000000000000000 7 bp7x89 := by
  apply split bp7x89 2
  · rw [show leftB bp7x89 2=bp7x90 by funext i; fin_cases i <;> rfl]; exact p7x90
  · rw [show rightB bp7x89 2=bp7x203 by funext i; fin_cases i <;> rfl]; exact p7x203
set_option maxRecDepth 100000 in
private theorem p7x11 : Deny 1000000000000000000 7 bp7x11 := by
  apply split bp7x11 0
  · rw [show leftB bp7x11 0=bp7x12 by funext i; fin_cases i <;> rfl]; exact p7x12
  · rw [show rightB bp7x11 0=bp7x89 by funext i; fin_cases i <;> rfl]; exact p7x89
set_option maxRecDepth 100000 in
private theorem p7x9 : Deny 1000000000000000000 7 bp7x9 := by
  apply split bp7x9 1
  · rw [show leftB bp7x9 1=bp7x10 by funext i; fin_cases i <;> rfl]; exact p7x10
  · rw [show rightB bp7x9 1=bp7x11 by funext i; fin_cases i <;> rfl]; exact p7x11
set_option maxRecDepth 100000 in
private theorem p7x7 : Deny 1000000000000000000 7 bp7x7 := by
  apply split bp7x7 2
  · rw [show leftB bp7x7 2=bp7x8 by funext i; fin_cases i <;> rfl]; exact p7x8
  · rw [show rightB bp7x7 2=bp7x9 by funext i; fin_cases i <;> rfl]; exact p7x9
set_option maxRecDepth 100000 in
private theorem p7x5 : Deny 1000000000000000000 7 bp7x5 := by
  apply split bp7x5 0
  · rw [show leftB bp7x5 0=bp7x6 by funext i; fin_cases i <;> rfl]; exact p7x6
  · rw [show rightB bp7x5 0=bp7x7 by funext i; fin_cases i <;> rfl]; exact p7x7
private def bp7x3382 : B := ![⟨4,none⟩,⟨4,none⟩,⟨1,none⟩]
private def bp7x3383 : B := ![⟨4,some 9⟩,⟨4,none⟩,⟨1,none⟩]
private def bp7x3384 : B := ![⟨4,some 9⟩,⟨4,none⟩,⟨1,some 3⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x3384 : Deny 1000000000000000000 7 bp7x3384 :=
  sound (by decide) (by decide) 3 18 (tail:=0) (by decide +kernel)
private def bp7x3389 : B := ![⟨4,some 9⟩,⟨4,none⟩,⟨4,none⟩]
private def bp7x3390 : B := ![⟨4,some 5⟩,⟨4,none⟩,⟨4,none⟩]
private def bp7x3391 : B := ![⟨4,some 5⟩,⟨4,some 9⟩,⟨4,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x3391 : Deny 1000000000000000000 7 bp7x3391 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp7x3392 : B := ![⟨4,some 5⟩,⟨10,none⟩,⟨4,none⟩]
private def bp7x3393 : B := ![⟨4,some 5⟩,⟨10,none⟩,⟨4,some 9⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x3393 : Deny 1000000000000000000 7 bp7x3393 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp7x3394 : B := ![⟨4,some 5⟩,⟨10,none⟩,⟨10,none⟩]
private def bp7x3395 : B := ![⟨4,some 5⟩,⟨10,some 21⟩,⟨10,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x3395 : Deny 1000000000000000000 7 bp7x3395 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp7x3396 : B := ![⟨4,some 5⟩,⟨22,none⟩,⟨10,none⟩]
private def bp7x3397 : B := ![⟨4,some 4⟩,⟨22,none⟩,⟨10,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x3397 : Deny 1000000000000000000 7 bp7x3397 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp7x3398 : B := ![⟨5,some 5⟩,⟨22,none⟩,⟨10,none⟩]
private def bp7x3399 : B := ![⟨5,some 5⟩,⟨22,none⟩,⟨10,some 21⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x3399 : Deny 1000000000000000000 7 bp7x3399 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp7x3400 : B := ![⟨5,some 5⟩,⟨22,none⟩,⟨22,none⟩]
private def bp7x3401 : B := ![⟨5,some 5⟩,⟨22,some 45⟩,⟨22,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x3401 : Deny 1000000000000000000 7 bp7x3401 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp7x3402 : B := ![⟨5,some 5⟩,⟨46,none⟩,⟨22,none⟩]
private def bp7x3403 : B := ![⟨5,some 5⟩,⟨46,none⟩,⟨22,some 45⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x3403 : Deny 1000000000000000000 7 bp7x3403 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp7x3404 : B := ![⟨5,some 5⟩,⟨46,none⟩,⟨46,none⟩]
private def bp7x3405 : B := ![⟨5,some 5⟩,⟨46,some 93⟩,⟨46,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x3405 : Deny 1000000000000000000 7 bp7x3405 :=
  sound (by decide) (by decide) 32 822880066514288764474002072405358039311471642564003871571972425641522111834853917310490714636116421372018067220687791570332804515645850064461227982086935833210091299382354977571 (tail:=0) (by decide +kernel)
private def bp7x3710 : B := ![⟨5,some 5⟩,⟨94,none⟩,⟨46,none⟩]
private def bp7x3711 : B := ![⟨5,some 5⟩,⟨94,none⟩,⟨46,some 93⟩]
private def bp7x3712 : B := ![⟨5,some 5⟩,⟨94,some 189⟩,⟨46,some 93⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x3712 : Deny 1000000000000000000 7 bp7x3712 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp7x3713 : B := ![⟨5,some 5⟩,⟨190,none⟩,⟨46,some 93⟩]
private def bp7x3714 : B := ![⟨5,some 5⟩,⟨190,none⟩,⟨46,some 61⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x3714 : Deny 1000000000000000000 7 bp7x3714 :=
  sound (by decide) (by decide) 25 195552584974555941553844574099105771998715335117255218 (tail:=0) (by decide +kernel)
private def bp7x3813 : B := ![⟨5,some 5⟩,⟨190,none⟩,⟨62,some 93⟩]
private def bp7x3814 : B := ![⟨5,some 5⟩,⟨190,some 381⟩,⟨62,some 93⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x3814 : Deny 1000000000000000000 7 bp7x3814 :=
  sound (by decide) (by decide) 16 21863189718305632422144120726052037222228768212555176491207303947688088150975044159527971675454769421474154855425166115 (tail:=0) (by decide +kernel)
private def bp7x4019 : B := ![⟨5,some 5⟩,⟨382,none⟩,⟨62,some 93⟩]
private def bp7x4020 : B := ![⟨5,some 5⟩,⟨382,none⟩,⟨62,some 74⟩]
private def bp7x4021 : B := ![⟨5,some 5⟩,⟨382,some 765⟩,⟨62,some 74⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x4021 : Deny 1000000000000000000 7 bp7x4021 :=
  sound (by decide) (by decide) 15 964563891948521531051717026373582093693544827148101560178583368398641595364722915 (tail:=0) (by decide +kernel)
private def bp7x4162 : B := ![⟨5,some 5⟩,⟨766,none⟩,⟨62,some 74⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x4162 : Deny 1000000000000000000 7 bp7x4162 :=
  sound (by decide) (by decide) 18 8018607878468577627084358046815551550679695515541288587938212322770537024411291082609892058809817464180304373358687714642238504786766555096039344699 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p7x4020 : Deny 1000000000000000000 7 bp7x4020 := by
  apply split bp7x4020 1
  · rw [show leftB bp7x4020 1=bp7x4021 by funext i; fin_cases i <;> rfl]; exact p7x4021
  · rw [show rightB bp7x4020 1=bp7x4162 by funext i; fin_cases i <;> rfl]; exact p7x4162
private def bp7x4417 : B := ![⟨5,some 5⟩,⟨382,none⟩,⟨75,some 93⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x4417 : Deny 1000000000000000000 7 bp7x4417 :=
  sound (by decide) (by decide) 15 12622121431918694995717163195630209088480842256110 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p7x4019 : Deny 1000000000000000000 7 bp7x4019 := by
  apply split bp7x4019 2
  · rw [show leftB bp7x4019 2=bp7x4020 by funext i; fin_cases i <;> rfl]; exact p7x4020
  · rw [show rightB bp7x4019 2=bp7x4417 by funext i; fin_cases i <;> rfl]; exact p7x4417
set_option maxRecDepth 100000 in
private theorem p7x3813 : Deny 1000000000000000000 7 bp7x3813 := by
  apply split bp7x3813 1
  · rw [show leftB bp7x3813 1=bp7x3814 by funext i; fin_cases i <;> rfl]; exact p7x3814
  · rw [show rightB bp7x3813 1=bp7x4019 by funext i; fin_cases i <;> rfl]; exact p7x4019
set_option maxRecDepth 100000 in
private theorem p7x3713 : Deny 1000000000000000000 7 bp7x3713 := by
  apply split bp7x3713 2
  · rw [show leftB bp7x3713 2=bp7x3714 by funext i; fin_cases i <;> rfl]; exact p7x3714
  · rw [show rightB bp7x3713 2=bp7x3813 by funext i; fin_cases i <;> rfl]; exact p7x3813
set_option maxRecDepth 100000 in
private theorem p7x3711 : Deny 1000000000000000000 7 bp7x3711 := by
  apply split bp7x3711 1
  · rw [show leftB bp7x3711 1=bp7x3712 by funext i; fin_cases i <;> rfl]; exact p7x3712
  · rw [show rightB bp7x3711 1=bp7x3713 by funext i; fin_cases i <;> rfl]; exact p7x3713
private def bp7x4510 : B := ![⟨5,some 5⟩,⟨94,none⟩,⟨94,none⟩]
private def bp7x4511 : B := ![⟨5,some 5⟩,⟨94,some 189⟩,⟨94,none⟩]
private def bp7x4512 : B := ![⟨5,some 5⟩,⟨94,some 189⟩,⟨94,some 189⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x4512 : Deny 1000000000000000000 7 bp7x4512 :=
  sound (by decide) (by decide) 16 1034188506159426900177206764423528552964510003116898470062939623972167083901582555155335990080770204687963500501311422743673195191316725827486861168437137895613978079062946744744700348220553994033277323901481759193992370 (tail:=0) (by decide +kernel)
private def bp7x4885 : B := ![⟨5,some 5⟩,⟨94,some 189⟩,⟨190,none⟩]
private def bp7x4886 : B := ![⟨5,some 5⟩,⟨94,some 125⟩,⟨190,none⟩]
private def bp7x4887 : B := ![⟨5,some 5⟩,⟨94,some 125⟩,⟨190,some 381⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x4887 : Deny 1000000000000000000 7 bp7x4887 :=
  sound (by decide) (by decide) 15 831451800180665916128416396273104835979489455537027999319789547061344691381651600064621386442350927916261923298111512843919995205256786750539689603153235122 (tail:=0) (by decide +kernel)
private def bp7x5154 : B := ![⟨5,some 5⟩,⟨94,some 125⟩,⟨382,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x5154 : Deny 1000000000000000000 7 bp7x5154 :=
  sound (by decide) (by decide) 19 282655273634290572152448514093184567047008590361198606621622231861319849886064825116223984969082554044193117497503570255892174073962750143409181846850149476586142972335839246610817213856291431447589895967213570843265262 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p7x4886 : Deny 1000000000000000000 7 bp7x4886 := by
  apply split bp7x4886 2
  · rw [show leftB bp7x4886 2=bp7x4887 by funext i; fin_cases i <;> rfl]; exact p7x4887
  · rw [show rightB bp7x4886 2=bp7x5154 by funext i; fin_cases i <;> rfl]; exact p7x5154
private def bp7x5529 : B := ![⟨5,some 5⟩,⟨126,some 189⟩,⟨190,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x5529 : Deny 1000000000000000000 7 bp7x5529 :=
  sound (by decide) (by decide) 15 24417413171514222118719493080773725371577378151252933563 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p7x4885 : Deny 1000000000000000000 7 bp7x4885 := by
  apply split bp7x4885 1
  · rw [show leftB bp7x4885 1=bp7x4886 by funext i; fin_cases i <;> rfl]; exact p7x4886
  · rw [show rightB bp7x4885 1=bp7x5529 by funext i; fin_cases i <;> rfl]; exact p7x5529
set_option maxRecDepth 100000 in
private theorem p7x4511 : Deny 1000000000000000000 7 bp7x4511 := by
  apply split bp7x4511 2
  · rw [show leftB bp7x4511 2=bp7x4512 by funext i; fin_cases i <;> rfl]; exact p7x4512
  · rw [show rightB bp7x4511 2=bp7x4885 by funext i; fin_cases i <;> rfl]; exact p7x4885
private def bp7x5634 : B := ![⟨5,some 5⟩,⟨190,none⟩,⟨94,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x5634 : Deny 1000000000000000000 7 bp7x5634 :=
  sound (by decide) (by decide) 17 111630362524272665636485359993582636884990148637417961453205079708356048837578014151075663087902375307415410965363060870776519943621333978986658806715 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p7x4510 : Deny 1000000000000000000 7 bp7x4510 := by
  apply split bp7x4510 1
  · rw [show leftB bp7x4510 1=bp7x4511 by funext i; fin_cases i <;> rfl]; exact p7x4511
  · rw [show rightB bp7x4510 1=bp7x5634 by funext i; fin_cases i <;> rfl]; exact p7x5634
set_option maxRecDepth 100000 in
private theorem p7x3710 : Deny 1000000000000000000 7 bp7x3710 := by
  apply split bp7x3710 2
  · rw [show leftB bp7x3710 2=bp7x3711 by funext i; fin_cases i <;> rfl]; exact p7x3711
  · rw [show rightB bp7x3710 2=bp7x4510 by funext i; fin_cases i <;> rfl]; exact p7x4510
set_option maxRecDepth 100000 in
private theorem p7x3404 : Deny 1000000000000000000 7 bp7x3404 := by
  apply split bp7x3404 1
  · rw [show leftB bp7x3404 1=bp7x3405 by funext i; fin_cases i <;> rfl]; exact p7x3405
  · rw [show rightB bp7x3404 1=bp7x3710 by funext i; fin_cases i <;> rfl]; exact p7x3710
set_option maxRecDepth 100000 in
private theorem p7x3402 : Deny 1000000000000000000 7 bp7x3402 := by
  apply split bp7x3402 2
  · rw [show leftB bp7x3402 2=bp7x3403 by funext i; fin_cases i <;> rfl]; exact p7x3403
  · rw [show rightB bp7x3402 2=bp7x3404 by funext i; fin_cases i <;> rfl]; exact p7x3404
set_option maxRecDepth 100000 in
private theorem p7x3400 : Deny 1000000000000000000 7 bp7x3400 := by
  apply split bp7x3400 1
  · rw [show leftB bp7x3400 1=bp7x3401 by funext i; fin_cases i <;> rfl]; exact p7x3401
  · rw [show rightB bp7x3400 1=bp7x3402 by funext i; fin_cases i <;> rfl]; exact p7x3402
set_option maxRecDepth 100000 in
private theorem p7x3398 : Deny 1000000000000000000 7 bp7x3398 := by
  apply split bp7x3398 2
  · rw [show leftB bp7x3398 2=bp7x3399 by funext i; fin_cases i <;> rfl]; exact p7x3399
  · rw [show rightB bp7x3398 2=bp7x3400 by funext i; fin_cases i <;> rfl]; exact p7x3400
set_option maxRecDepth 100000 in
private theorem p7x3396 : Deny 1000000000000000000 7 bp7x3396 := by
  apply split bp7x3396 0
  · rw [show leftB bp7x3396 0=bp7x3397 by funext i; fin_cases i <;> rfl]; exact p7x3397
  · rw [show rightB bp7x3396 0=bp7x3398 by funext i; fin_cases i <;> rfl]; exact p7x3398
set_option maxRecDepth 100000 in
private theorem p7x3394 : Deny 1000000000000000000 7 bp7x3394 := by
  apply split bp7x3394 1
  · rw [show leftB bp7x3394 1=bp7x3395 by funext i; fin_cases i <;> rfl]; exact p7x3395
  · rw [show rightB bp7x3394 1=bp7x3396 by funext i; fin_cases i <;> rfl]; exact p7x3396
set_option maxRecDepth 100000 in
private theorem p7x3392 : Deny 1000000000000000000 7 bp7x3392 := by
  apply split bp7x3392 2
  · rw [show leftB bp7x3392 2=bp7x3393 by funext i; fin_cases i <;> rfl]; exact p7x3393
  · rw [show rightB bp7x3392 2=bp7x3394 by funext i; fin_cases i <;> rfl]; exact p7x3394
set_option maxRecDepth 100000 in
private theorem p7x3390 : Deny 1000000000000000000 7 bp7x3390 := by
  apply split bp7x3390 1
  · rw [show leftB bp7x3390 1=bp7x3391 by funext i; fin_cases i <;> rfl]; exact p7x3391
  · rw [show rightB bp7x3390 1=bp7x3392 by funext i; fin_cases i <;> rfl]; exact p7x3392
private def bp7x5895 : B := ![⟨6,some 9⟩,⟨4,none⟩,⟨4,none⟩]
private def bp7x5896 : B := ![⟨6,some 9⟩,⟨4,some 9⟩,⟨4,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x5896 : Deny 1000000000000000000 7 bp7x5896 :=
  sound (by decide) (by decide) 20 114378720596353245186608931995747078153723177922925752402225431294565373218083 (tail:=0) (by decide +kernel)
private def bp7x6031 : B := ![⟨6,some 9⟩,⟨10,none⟩,⟨4,none⟩]
private def bp7x6032 : B := ![⟨6,some 9⟩,⟨10,none⟩,⟨4,some 9⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x6032 : Deny 1000000000000000000 7 bp7x6032 :=
  sound (by decide) (by decide) 19 5648974216979365473514966766879159145205925970302494397613642485578988600990543631366930844219849180489365958264058448738502 (tail:=0) (by decide +kernel)
private def bp7x6245 : B := ![⟨6,some 9⟩,⟨10,none⟩,⟨10,none⟩]
private def bp7x6246 : B := ![⟨6,some 9⟩,⟨10,some 21⟩,⟨10,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x6246 : Deny 1000000000000000000 7 bp7x6246 :=
  sound (by decide) (by decide) 19 37849213102717346189210830491057853889456263031836251619592119715869801131548986538488222678643407957109207330460949717813837011064206381414639964589165 (tail:=0) (by decide +kernel)
private def bp7x6505 : B := ![⟨6,some 9⟩,⟨22,none⟩,⟨10,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x6505 : Deny 1000000000000000000 7 bp7x6505 :=
  sound (by decide) (by decide) 22 11865614248219443361379330834888718549687055706881693030990180007749819640730664957662815205843111901677094609511301696393524369392173283516891498659513890414942430061 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p7x6245 : Deny 1000000000000000000 7 bp7x6245 := by
  apply split bp7x6245 1
  · rw [show leftB bp7x6245 1=bp7x6246 by funext i; fin_cases i <;> rfl]; exact p7x6246
  · rw [show rightB bp7x6245 1=bp7x6505 by funext i; fin_cases i <;> rfl]; exact p7x6505
set_option maxRecDepth 100000 in
private theorem p7x6031 : Deny 1000000000000000000 7 bp7x6031 := by
  apply split bp7x6031 2
  · rw [show leftB bp7x6031 2=bp7x6032 by funext i; fin_cases i <;> rfl]; exact p7x6032
  · rw [show rightB bp7x6031 2=bp7x6245 by funext i; fin_cases i <;> rfl]; exact p7x6245
set_option maxRecDepth 100000 in
private theorem p7x5895 : Deny 1000000000000000000 7 bp7x5895 := by
  apply split bp7x5895 1
  · rw [show leftB bp7x5895 1=bp7x5896 by funext i; fin_cases i <;> rfl]; exact p7x5896
  · rw [show rightB bp7x5895 1=bp7x6031 by funext i; fin_cases i <;> rfl]; exact p7x6031
set_option maxRecDepth 100000 in
private theorem p7x3389 : Deny 1000000000000000000 7 bp7x3389 := by
  apply split bp7x3389 0
  · rw [show leftB bp7x3389 0=bp7x3390 by funext i; fin_cases i <;> rfl]; exact p7x3390
  · rw [show rightB bp7x3389 0=bp7x5895 by funext i; fin_cases i <;> rfl]; exact p7x5895
set_option maxRecDepth 100000 in
private theorem p7x3383 : Deny 1000000000000000000 7 bp7x3383 := by
  apply split bp7x3383 2
  · rw [show leftB bp7x3383 2=bp7x3384 by funext i; fin_cases i <;> rfl]; exact p7x3384
  · rw [show rightB bp7x3383 2=bp7x3389 by funext i; fin_cases i <;> rfl]; exact p7x3389
private def bp7x6792 : B := ![⟨10,none⟩,⟨4,none⟩,⟨1,none⟩]
private def bp7x6793 : B := ![⟨10,none⟩,⟨4,none⟩,⟨1,some 3⟩]
private def bp7x6794 : B := ![⟨10,none⟩,⟨4,some 9⟩,⟨1,some 3⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x6794 : Deny 1000000000000000000 7 bp7x6794 :=
  sound (by decide) (by decide) 21 2513739694968616508172654909201027615617087941067089187923497479487476297600132598607872496674202887828899984098445 (tail:=0) (by decide +kernel)
private def bp7x6993 : B := ![⟨10,none⟩,⟨10,none⟩,⟨1,some 3⟩]
private def bp7x6994 : B := ![⟨10,some 21⟩,⟨10,none⟩,⟨1,some 3⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x6994 : Deny 1000000000000000000 7 bp7x6994 :=
  sound (by decide) (by decide) 20 529364597235340412859983396747396551834516421926712783684376988895746234477467966542318124586877864754553452082287280016557595439909773389786851967742292683183733578012539020714851 (tail:=0) (by decide +kernel)
private def bp7x7301 : B := ![⟨22,none⟩,⟨10,none⟩,⟨1,some 3⟩]
private def bp7x7302 : B := ![⟨22,none⟩,⟨10,none⟩,⟨1,some 1⟩]
private def bp7x7303 : B := ![⟨22,none⟩,⟨10,some 21⟩,⟨1,some 1⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x7303 : Deny 1000000000000000000 7 bp7x7303 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp7x7304 : B := ![⟨22,none⟩,⟨22,none⟩,⟨1,some 1⟩]
private def bp7x7305 : B := ![⟨22,some 45⟩,⟨22,none⟩,⟨1,some 1⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x7305 : Deny 1000000000000000000 7 bp7x7305 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp7x7306 : B := ![⟨46,none⟩,⟨22,none⟩,⟨1,some 1⟩]
private def bp7x7307 : B := ![⟨46,none⟩,⟨22,some 45⟩,⟨1,some 1⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x7307 : Deny 1000000000000000000 7 bp7x7307 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp7x7308 : B := ![⟨46,none⟩,⟨46,none⟩,⟨1,some 1⟩]
private def bp7x7309 : B := ![⟨46,some 93⟩,⟨46,none⟩,⟨1,some 1⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x7309 : Deny 1000000000000000000 7 bp7x7309 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp7x7310 : B := ![⟨94,none⟩,⟨46,none⟩,⟨1,some 1⟩]
private def bp7x7311 : B := ![⟨94,none⟩,⟨46,some 93⟩,⟨1,some 1⟩]
private def bp7x7312 : B := ![⟨94,some 189⟩,⟨46,some 93⟩,⟨1,some 1⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x7312 : Deny 1000000000000000000 7 bp7x7312 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp7x7313 : B := ![⟨190,none⟩,⟨46,some 93⟩,⟨1,some 1⟩]
private def bp7x7314 : B := ![⟨190,none⟩,⟨46,some 61⟩,⟨1,some 1⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x7314 : Deny 1000000000000000000 7 bp7x7314 :=
  sound (by decide) (by decide) 24 1342424161440391153838416447306917538663090978108466031747013960836594761088414684983443293404225248218239715645504166933109692949951435730899276251810414484077549451861996643840184138440442449447477895361761809 (tail:=0) (by decide +kernel)
private def bp7x7675 : B := ![⟨190,none⟩,⟨62,some 93⟩,⟨1,some 1⟩]
private def bp7x7676 : B := ![⟨190,some 381⟩,⟨62,some 93⟩,⟨1,some 1⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x7676 : Deny 1000000000000000000 7 bp7x7676 :=
  sound (by decide) (by decide) 16 3948466785104265552681033560819675434354751706345458659531341820779592309587890129000910881240942079386212345246077282643809953925409 (tail:=0) (by decide +kernel)
private def bp7x7905 : B := ![⟨382,none⟩,⟨62,some 93⟩,⟨1,some 1⟩]
private def bp7x7906 : B := ![⟨382,some 765⟩,⟨62,some 93⟩,⟨1,some 1⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x7906 : Deny 1000000000000000000 7 bp7x7906 :=
  sound (by decide) (by decide) 16 21291275319168999365618484092456665499021802184190712426439015357529176012241162825381495433173950656598584857591550025070781875845043193479176862639495575692173074646309142077734 (tail:=0) (by decide +kernel)
private def bp7x8213 : B := ![⟨766,none⟩,⟨62,some 93⟩,⟨1,some 1⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x8213 : Deny 1000000000000000000 7 bp7x8213 :=
  sound (by decide) (by decide) 17 31808494170589684328668617574765019213088086112151142 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p7x7905 : Deny 1000000000000000000 7 bp7x7905 := by
  apply split bp7x7905 0
  · rw [show leftB bp7x7905 0=bp7x7906 by funext i; fin_cases i <;> rfl]; exact p7x7906
  · rw [show rightB bp7x7905 0=bp7x8213 by funext i; fin_cases i <;> rfl]; exact p7x8213
set_option maxRecDepth 100000 in
private theorem p7x7675 : Deny 1000000000000000000 7 bp7x7675 := by
  apply split bp7x7675 0
  · rw [show leftB bp7x7675 0=bp7x7676 by funext i; fin_cases i <;> rfl]; exact p7x7676
  · rw [show rightB bp7x7675 0=bp7x7905 by funext i; fin_cases i <;> rfl]; exact p7x7905
set_option maxRecDepth 100000 in
private theorem p7x7313 : Deny 1000000000000000000 7 bp7x7313 := by
  apply split bp7x7313 1
  · rw [show leftB bp7x7313 1=bp7x7314 by funext i; fin_cases i <;> rfl]; exact p7x7314
  · rw [show rightB bp7x7313 1=bp7x7675 by funext i; fin_cases i <;> rfl]; exact p7x7675
set_option maxRecDepth 100000 in
private theorem p7x7311 : Deny 1000000000000000000 7 bp7x7311 := by
  apply split bp7x7311 0
  · rw [show leftB bp7x7311 0=bp7x7312 by funext i; fin_cases i <;> rfl]; exact p7x7312
  · rw [show rightB bp7x7311 0=bp7x7313 by funext i; fin_cases i <;> rfl]; exact p7x7313
private def bp7x8314 : B := ![⟨94,none⟩,⟨94,none⟩,⟨1,some 1⟩]
private def bp7x8315 : B := ![⟨94,some 189⟩,⟨94,none⟩,⟨1,some 1⟩]
private def bp7x8316 : B := ![⟨94,some 189⟩,⟨94,some 189⟩,⟨1,some 1⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x8316 : Deny 1000000000000000000 7 bp7x8316 :=
  sound (by decide) (by decide) 17 38750382944166589301912260358568151411551652903573005243145118785021933351092270335198029370328245124290194275299161055610330229489050295096711288361489482882884007777144235647265 (tail:=0) (by decide +kernel)
private def bp7x8621 : B := ![⟨94,some 189⟩,⟨190,none⟩,⟨1,some 1⟩]
private def bp7x8622 : B := ![⟨94,some 125⟩,⟨190,none⟩,⟨1,some 1⟩]
private def bp7x8623 : B := ![⟨94,some 125⟩,⟨190,some 381⟩,⟨1,some 1⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x8623 : Deny 1000000000000000000 7 bp7x8623 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp7x8624 : B := ![⟨94,some 125⟩,⟨382,none⟩,⟨1,some 1⟩]
private def bp7x8625 : B := ![⟨94,some 107⟩,⟨382,none⟩,⟨1,some 1⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x8625 : Deny 1000000000000000000 7 bp7x8625 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp7x8626 : B := ![⟨108,some 125⟩,⟨382,none⟩,⟨1,some 1⟩]
private def bp7x8627 : B := ![⟨108,some 125⟩,⟨382,some 765⟩,⟨1,some 1⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x8627 : Deny 1000000000000000000 7 bp7x8627 :=
  sound (by decide) (by decide) 15 229967119298250164008804974629508828874832274490117577379355492071352328481 (tail:=0) (by decide +kernel)
private def bp7x8756 : B := ![⟨108,some 125⟩,⟨766,none⟩,⟨1,some 1⟩]
private def bp7x8757 : B := ![⟨108,some 115⟩,⟨766,none⟩,⟨1,some 1⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x8757 : Deny 1000000000000000000 7 bp7x8757 :=
  sound (by decide) (by decide) 22 135386685227564950244732332136204038735640367235244036519605770717760210090843837583713230201987150729560462956261884948770439985439520574788804598725967141393646722719964349808674322 (tail:=0) (by decide +kernel)
private def bp7x9070 : B := ![⟨116,some 125⟩,⟨766,none⟩,⟨1,some 1⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x9070 : Deny 1000000000000000000 7 bp7x9070 :=
  sound (by decide) (by decide) 16 4910017017327092986519719180635000356058854873477120016608087034999694761692720483054949931855017769138406168678 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p7x8756 : Deny 1000000000000000000 7 bp7x8756 := by
  apply split bp7x8756 0
  · rw [show leftB bp7x8756 0=bp7x8757 by funext i; fin_cases i <;> rfl]; exact p7x8757
  · rw [show rightB bp7x8756 0=bp7x9070 by funext i; fin_cases i <;> rfl]; exact p7x9070
set_option maxRecDepth 100000 in
private theorem p7x8626 : Deny 1000000000000000000 7 bp7x8626 := by
  apply split bp7x8626 1
  · rw [show leftB bp7x8626 1=bp7x8627 by funext i; fin_cases i <;> rfl]; exact p7x8627
  · rw [show rightB bp7x8626 1=bp7x8756 by funext i; fin_cases i <;> rfl]; exact p7x8756
set_option maxRecDepth 100000 in
private theorem p7x8624 : Deny 1000000000000000000 7 bp7x8624 := by
  apply split bp7x8624 0
  · rw [show leftB bp7x8624 0=bp7x8625 by funext i; fin_cases i <;> rfl]; exact p7x8625
  · rw [show rightB bp7x8624 0=bp7x8626 by funext i; fin_cases i <;> rfl]; exact p7x8626
set_option maxRecDepth 100000 in
private theorem p7x8622 : Deny 1000000000000000000 7 bp7x8622 := by
  apply split bp7x8622 1
  · rw [show leftB bp7x8622 1=bp7x8623 by funext i; fin_cases i <;> rfl]; exact p7x8623
  · rw [show rightB bp7x8622 1=bp7x8624 by funext i; fin_cases i <;> rfl]; exact p7x8624
private def bp7x9267 : B := ![⟨126,some 189⟩,⟨190,none⟩,⟨1,some 1⟩]
private def bp7x9268 : B := ![⟨126,some 189⟩,⟨190,some 381⟩,⟨1,some 1⟩]
private def bp7x9269 : B := ![⟨126,some 151⟩,⟨190,some 381⟩,⟨1,some 1⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x9269 : Deny 1000000000000000000 7 bp7x9269 :=
  sound (by decide) (by decide) 15 647356190353747911791792864843920047846390402054746662034581976627247180585606336077025498187745761763105324329956524911841821882913713975699753671748073749385154274771111468782477590623898786931078 (tail:=0) (by decide +kernel)
private def bp7x9606 : B := ![⟨152,some 189⟩,⟨190,some 381⟩,⟨1,some 1⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x9606 : Deny 1000000000000000000 7 bp7x9606 :=
  sound (by decide) (by decide) 13 56572140858956931920558070341103163352678 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p7x9268 : Deny 1000000000000000000 7 bp7x9268 := by
  apply split bp7x9268 0
  · rw [show leftB bp7x9268 0=bp7x9269 by funext i; fin_cases i <;> rfl]; exact p7x9269
  · rw [show rightB bp7x9268 0=bp7x9606 by funext i; fin_cases i <;> rfl]; exact p7x9606
private def bp7x9685 : B := ![⟨126,some 189⟩,⟨382,none⟩,⟨1,some 1⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x9685 : Deny 1000000000000000000 7 bp7x9685 :=
  sound (by decide) (by decide) 17 57356595490065035923408133471184615645147491453967122198425325836697 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p7x9267 : Deny 1000000000000000000 7 bp7x9267 := by
  apply split bp7x9267 1
  · rw [show leftB bp7x9267 1=bp7x9268 by funext i; fin_cases i <;> rfl]; exact p7x9268
  · rw [show rightB bp7x9267 1=bp7x9685 by funext i; fin_cases i <;> rfl]; exact p7x9685
set_option maxRecDepth 100000 in
private theorem p7x8621 : Deny 1000000000000000000 7 bp7x8621 := by
  apply split bp7x8621 0
  · rw [show leftB bp7x8621 0=bp7x8622 by funext i; fin_cases i <;> rfl]; exact p7x8622
  · rw [show rightB bp7x8621 0=bp7x9267 by funext i; fin_cases i <;> rfl]; exact p7x9267
set_option maxRecDepth 100000 in
private theorem p7x8315 : Deny 1000000000000000000 7 bp7x8315 := by
  apply split bp7x8315 1
  · rw [show leftB bp7x8315 1=bp7x8316 by funext i; fin_cases i <;> rfl]; exact p7x8316
  · rw [show rightB bp7x8315 1=bp7x8621 by funext i; fin_cases i <;> rfl]; exact p7x8621
private def bp7x9808 : B := ![⟨190,none⟩,⟨94,none⟩,⟨1,some 1⟩]
private def bp7x9809 : B := ![⟨190,none⟩,⟨94,some 189⟩,⟨1,some 1⟩]
private def bp7x9810 : B := ![⟨190,some 381⟩,⟨94,some 189⟩,⟨1,some 1⟩]
private def bp7x9811 : B := ![⟨190,some 381⟩,⟨94,some 125⟩,⟨1,some 1⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x9811 : Deny 1000000000000000000 7 bp7x9811 :=
  sound (by decide) (by decide) 14 544055878852479461150492264194231373736917312290836725679280358977286218644808022476822212705275807290072425231842252047209990685066029541774746150107880214452820840212333047825196070094752797565541780225493987510565 (tail:=0) (by decide +kernel)
private def bp7x10180 : B := ![⟨190,some 381⟩,⟨126,some 189⟩,⟨1,some 1⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x10180 : Deny 1000000000000000000 7 bp7x10180 :=
  sound (by decide) (by decide) 14 51578661820484700406413797370398084901935705 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p7x9810 : Deny 1000000000000000000 7 bp7x9810 := by
  apply split bp7x9810 1
  · rw [show leftB bp7x9810 1=bp7x9811 by funext i; fin_cases i <;> rfl]; exact p7x9811
  · rw [show rightB bp7x9810 1=bp7x10180 by funext i; fin_cases i <;> rfl]; exact p7x10180
private def bp7x10263 : B := ![⟨382,none⟩,⟨94,some 189⟩,⟨1,some 1⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x10263 : Deny 1000000000000000000 7 bp7x10263 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p7x9809 : Deny 1000000000000000000 7 bp7x9809 := by
  apply split bp7x9809 0
  · rw [show leftB bp7x9809 0=bp7x9810 by funext i; fin_cases i <;> rfl]; exact p7x9810
  · rw [show rightB bp7x9809 0=bp7x10263 by funext i; fin_cases i <;> rfl]; exact p7x10263
private def bp7x10264 : B := ![⟨190,none⟩,⟨190,none⟩,⟨1,some 1⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x10264 : Deny 1000000000000000000 7 bp7x10264 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p7x9808 : Deny 1000000000000000000 7 bp7x9808 := by
  apply split bp7x9808 1
  · rw [show leftB bp7x9808 1=bp7x9809 by funext i; fin_cases i <;> rfl]; exact p7x9809
  · rw [show rightB bp7x9808 1=bp7x10264 by funext i; fin_cases i <;> rfl]; exact p7x10264
set_option maxRecDepth 100000 in
private theorem p7x8314 : Deny 1000000000000000000 7 bp7x8314 := by
  apply split bp7x8314 0
  · rw [show leftB bp7x8314 0=bp7x8315 by funext i; fin_cases i <;> rfl]; exact p7x8315
  · rw [show rightB bp7x8314 0=bp7x9808 by funext i; fin_cases i <;> rfl]; exact p7x9808
set_option maxRecDepth 100000 in
private theorem p7x7310 : Deny 1000000000000000000 7 bp7x7310 := by
  apply split bp7x7310 1
  · rw [show leftB bp7x7310 1=bp7x7311 by funext i; fin_cases i <;> rfl]; exact p7x7311
  · rw [show rightB bp7x7310 1=bp7x8314 by funext i; fin_cases i <;> rfl]; exact p7x8314
set_option maxRecDepth 100000 in
private theorem p7x7308 : Deny 1000000000000000000 7 bp7x7308 := by
  apply split bp7x7308 0
  · rw [show leftB bp7x7308 0=bp7x7309 by funext i; fin_cases i <;> rfl]; exact p7x7309
  · rw [show rightB bp7x7308 0=bp7x7310 by funext i; fin_cases i <;> rfl]; exact p7x7310
set_option maxRecDepth 100000 in
private theorem p7x7306 : Deny 1000000000000000000 7 bp7x7306 := by
  apply split bp7x7306 1
  · rw [show leftB bp7x7306 1=bp7x7307 by funext i; fin_cases i <;> rfl]; exact p7x7307
  · rw [show rightB bp7x7306 1=bp7x7308 by funext i; fin_cases i <;> rfl]; exact p7x7308
set_option maxRecDepth 100000 in
private theorem p7x7304 : Deny 1000000000000000000 7 bp7x7304 := by
  apply split bp7x7304 0
  · rw [show leftB bp7x7304 0=bp7x7305 by funext i; fin_cases i <;> rfl]; exact p7x7305
  · rw [show rightB bp7x7304 0=bp7x7306 by funext i; fin_cases i <;> rfl]; exact p7x7306
set_option maxRecDepth 100000 in
private theorem p7x7302 : Deny 1000000000000000000 7 bp7x7302 := by
  apply split bp7x7302 1
  · rw [show leftB bp7x7302 1=bp7x7303 by funext i; fin_cases i <;> rfl]; exact p7x7303
  · rw [show rightB bp7x7302 1=bp7x7304 by funext i; fin_cases i <;> rfl]; exact p7x7304
private def bp7x10265 : B := ![⟨22,none⟩,⟨10,none⟩,⟨2,some 3⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x10265 : Deny 1000000000000000000 7 bp7x10265 :=
  sound (by decide) (by decide) 13 71142846206484608100402113762640538128003278424496718511809716471728737133826486 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p7x7301 : Deny 1000000000000000000 7 bp7x7301 := by
  apply split bp7x7301 2
  · rw [show leftB bp7x7301 2=bp7x7302 by funext i; fin_cases i <;> rfl]; exact p7x7302
  · rw [show rightB bp7x7301 2=bp7x10265 by funext i; fin_cases i <;> rfl]; exact p7x10265
set_option maxRecDepth 100000 in
private theorem p7x6993 : Deny 1000000000000000000 7 bp7x6993 := by
  apply split bp7x6993 0
  · rw [show leftB bp7x6993 0=bp7x6994 by funext i; fin_cases i <;> rfl]; exact p7x6994
  · rw [show rightB bp7x6993 0=bp7x7301 by funext i; fin_cases i <;> rfl]; exact p7x7301
set_option maxRecDepth 100000 in
private theorem p7x6793 : Deny 1000000000000000000 7 bp7x6793 := by
  apply split bp7x6793 1
  · rw [show leftB bp7x6793 1=bp7x6794 by funext i; fin_cases i <;> rfl]; exact p7x6794
  · rw [show rightB bp7x6793 1=bp7x6993 by funext i; fin_cases i <;> rfl]; exact p7x6993
private def bp7x10410 : B := ![⟨10,none⟩,⟨4,none⟩,⟨4,none⟩]
private def bp7x10411 : B := ![⟨10,none⟩,⟨4,some 9⟩,⟨4,none⟩]
private def bp7x10412 : B := ![⟨10,some 21⟩,⟨4,some 9⟩,⟨4,none⟩]
private def bp7x10413 : B := ![⟨10,some 21⟩,⟨4,some 9⟩,⟨4,some 9⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x10413 : Deny 1000000000000000000 7 bp7x10413 :=
  sound (by decide) (by decide) 11 27218285888196243955078380993219521248875215504519089115453605473641552947892461887998435468486 (tail:=0) (by decide +kernel)
private def bp7x10576 : B := ![⟨10,some 21⟩,⟨4,some 9⟩,⟨10,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x10576 : Deny 1000000000000000000 7 bp7x10576 :=
  sound (by decide) (by decide) 19 52257171680035204612992618109867765274322412625527920381792551857115905265567687003853014358577095614434794204283551174763143188209790232305715973507190 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p7x10412 : Deny 1000000000000000000 7 bp7x10412 := by
  apply split bp7x10412 2
  · rw [show leftB bp7x10412 2=bp7x10413 by funext i; fin_cases i <;> rfl]; exact p7x10413
  · rw [show rightB bp7x10412 2=bp7x10576 by funext i; fin_cases i <;> rfl]; exact p7x10576
private def bp7x10839 : B := ![⟨22,none⟩,⟨4,some 9⟩,⟨4,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x10839 : Deny 1000000000000000000 7 bp7x10839 :=
  sound (by decide) (by decide) 15 32642174422030809378030185015951749767125837566140275738191060026500666856098267 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p7x10411 : Deny 1000000000000000000 7 bp7x10411 := by
  apply split bp7x10411 0
  · rw [show leftB bp7x10411 0=bp7x10412 by funext i; fin_cases i <;> rfl]; exact p7x10412
  · rw [show rightB bp7x10411 0=bp7x10839 by funext i; fin_cases i <;> rfl]; exact p7x10839
private def bp7x10982 : B := ![⟨10,none⟩,⟨10,none⟩,⟨4,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p7x10982 : Deny 1000000000000000000 7 bp7x10982 :=
  sound (by decide) (by decide) 14 16368656584948380708704373562113641429485958051548740147256318548893 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p7x10410 : Deny 1000000000000000000 7 bp7x10410 := by
  apply split bp7x10410 1
  · rw [show leftB bp7x10410 1=bp7x10411 by funext i; fin_cases i <;> rfl]; exact p7x10411
  · rw [show rightB bp7x10410 1=bp7x10982 by funext i; fin_cases i <;> rfl]; exact p7x10982
set_option maxRecDepth 100000 in
private theorem p7x6792 : Deny 1000000000000000000 7 bp7x6792 := by
  apply split bp7x6792 2
  · rw [show leftB bp7x6792 2=bp7x6793 by funext i; fin_cases i <;> rfl]; exact p7x6793
  · rw [show rightB bp7x6792 2=bp7x10410 by funext i; fin_cases i <;> rfl]; exact p7x10410
set_option maxRecDepth 100000 in
private theorem p7x3382 : Deny 1000000000000000000 7 bp7x3382 := by
  apply split bp7x3382 0
  · rw [show leftB bp7x3382 0=bp7x3383 by funext i; fin_cases i <;> rfl]; exact p7x3383
  · rw [show rightB bp7x3382 0=bp7x6792 by funext i; fin_cases i <;> rfl]; exact p7x6792
set_option maxRecDepth 100000 in
private theorem p7x4 : Deny 1000000000000000000 7 bp7x4 := by
  apply split bp7x4 1
  · rw [show leftB bp7x4 1=bp7x5 by funext i; fin_cases i <;> rfl]; exact p7x5
  · rw [show rightB bp7x4 1=bp7x3382 by funext i; fin_cases i <;> rfl]; exact p7x3382
set_option maxRecDepth 100000 in
theorem p7x0 : Deny 1000000000000000000 7 start := by
  apply split start 0
  · rw [show leftB start 0=bp7x1 by funext i; fin_cases i <;> rfl]; exact p7x1
  · rw [show rightB start 0=bp7x4 by funext i; fin_cases i <;> rfl]; exact p7x4
end OMA.Large245212

/- Exact large-prime arithmetic certificate from large_last_245212.py. -/
namespace OMA.Large245212
private def bp11x1 : B := ![⟨1,some 3⟩,⟨1,none⟩,⟨1,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x1 : Deny 1000000000000000000 11 bp11x1 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp11x2 : B := ![⟨4,none⟩,⟨1,none⟩,⟨1,none⟩]
private def bp11x3 : B := ![⟨4,none⟩,⟨1,some 3⟩,⟨1,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x3 : Deny 1000000000000000000 11 bp11x3 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp11x4 : B := ![⟨4,none⟩,⟨4,none⟩,⟨1,none⟩]
private def bp11x5 : B := ![⟨4,some 9⟩,⟨4,none⟩,⟨1,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x5 : Deny 1000000000000000000 11 bp11x5 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp11x6 : B := ![⟨10,none⟩,⟨4,none⟩,⟨1,none⟩]
private def bp11x7 : B := ![⟨10,none⟩,⟨4,some 9⟩,⟨1,none⟩]
private def bp11x8 : B := ![⟨10,none⟩,⟨4,some 9⟩,⟨1,some 3⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x8 : Deny 1000000000000000000 11 bp11x8 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp11x9 : B := ![⟨10,none⟩,⟨4,some 9⟩,⟨4,none⟩]
private def bp11x10 : B := ![⟨10,some 21⟩,⟨4,some 9⟩,⟨4,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x10 : Deny 1000000000000000000 11 bp11x10 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp11x11 : B := ![⟨22,none⟩,⟨4,some 9⟩,⟨4,none⟩]
private def bp11x12 : B := ![⟨22,none⟩,⟨4,some 5⟩,⟨4,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x12 : Deny 1000000000000000000 11 bp11x12 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp11x13 : B := ![⟨22,none⟩,⟨6,some 9⟩,⟨4,none⟩]
private def bp11x14 : B := ![⟨22,some 45⟩,⟨6,some 9⟩,⟨4,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x14 : Deny 1000000000000000000 11 bp11x14 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp11x15 : B := ![⟨46,none⟩,⟨6,some 9⟩,⟨4,none⟩]
private def bp11x16 : B := ![⟨46,none⟩,⟨6,some 9⟩,⟨4,some 9⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x16 : Deny 1000000000000000000 11 bp11x16 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp11x17 : B := ![⟨46,none⟩,⟨6,some 9⟩,⟨10,none⟩]
private def bp11x18 : B := ![⟨46,none⟩,⟨6,some 7⟩,⟨10,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x18 : Deny 1000000000000000000 11 bp11x18 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp11x19 : B := ![⟨46,none⟩,⟨8,some 9⟩,⟨10,none⟩]
private def bp11x20 : B := ![⟨46,some 93⟩,⟨8,some 9⟩,⟨10,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x20 : Deny 1000000000000000000 11 bp11x20 :=
  sound (by decide) (by decide) 34 590514221053394850353400759456333015599313720248625451997288488002920460418938415620307482459927140789456622855495223204430154740867859 (tail:=0) (by decide +kernel)
private def bp11x255 : B := ![⟨94,none⟩,⟨8,some 9⟩,⟨10,none⟩]
private def bp11x256 : B := ![⟨94,none⟩,⟨8,some 9⟩,⟨10,some 21⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x256 : Deny 1000000000000000000 11 bp11x256 :=
  sound (by decide) (by decide) 23 528931477418707132046490975764781599674238237483586898466727897239197922296765892203057 (tail:=0) (by decide +kernel)
private def bp11x409 : B := ![⟨94,none⟩,⟨8,some 9⟩,⟨22,none⟩]
private def bp11x410 : B := ![⟨94,some 189⟩,⟨8,some 9⟩,⟨22,none⟩]
private def bp11x411 : B := ![⟨94,some 189⟩,⟨8,some 9⟩,⟨22,some 45⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x411 : Deny 1000000000000000000 11 bp11x411 :=
  sound (by decide) (by decide) 15 1869735232198802082938548875880875120717975964498198496504279667474 (tail:=0) (by decide +kernel)
private def bp11x528 : B := ![⟨94,some 189⟩,⟨8,some 9⟩,⟨46,none⟩]
private def bp11x529 : B := ![⟨94,some 189⟩,⟨8,some 8⟩,⟨46,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x529 : Deny 1000000000000000000 11 bp11x529 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp11x530 : B := ![⟨94,some 189⟩,⟨9,some 9⟩,⟨46,none⟩]
private def bp11x531 : B := ![⟨94,some 125⟩,⟨9,some 9⟩,⟨46,none⟩]
private def bp11x532 : B := ![⟨94,some 125⟩,⟨9,some 9⟩,⟨46,some 93⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x532 : Deny 1000000000000000000 11 bp11x532 :=
  sound (by decide) (by decide) 13 23511067158702956213686046938924212229018455435964798899929935007025 (tail:=0) (by decide +kernel)
private def bp11x651 : B := ![⟨94,some 125⟩,⟨9,some 9⟩,⟨94,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x651 : Deny 1000000000000000000 11 bp11x651 :=
  sound (by decide) (by decide) 17 3685152689781072098845099520552357932883723470265088707815977631502808232037723850370254059730828413620271988529142107912780379590279418005654863912669414282590412616288029 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x531 : Deny 1000000000000000000 11 bp11x531 := by
  apply split bp11x531 2
  · rw [show leftB bp11x531 2=bp11x532 by funext i; fin_cases i <;> rfl]; exact p11x532
  · rw [show rightB bp11x531 2=bp11x651 by funext i; fin_cases i <;> rfl]; exact p11x651
private def bp11x946 : B := ![⟨126,some 189⟩,⟨9,some 9⟩,⟨46,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x946 : Deny 1000000000000000000 11 bp11x946 :=
  sound (by decide) (by decide) 14 22452908805652831217244866366257612055576554871320921547747308654089079 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x530 : Deny 1000000000000000000 11 bp11x530 := by
  apply split bp11x530 0
  · rw [show leftB bp11x530 0=bp11x531 by funext i; fin_cases i <;> rfl]; exact p11x531
  · rw [show rightB bp11x530 0=bp11x946 by funext i; fin_cases i <;> rfl]; exact p11x946
set_option maxRecDepth 100000 in
private theorem p11x528 : Deny 1000000000000000000 11 bp11x528 := by
  apply split bp11x528 1
  · rw [show leftB bp11x528 1=bp11x529 by funext i; fin_cases i <;> rfl]; exact p11x529
  · rw [show rightB bp11x528 1=bp11x530 by funext i; fin_cases i <;> rfl]; exact p11x530
set_option maxRecDepth 100000 in
private theorem p11x410 : Deny 1000000000000000000 11 bp11x410 := by
  apply split bp11x410 2
  · rw [show leftB bp11x410 2=bp11x411 by funext i; fin_cases i <;> rfl]; exact p11x411
  · rw [show rightB bp11x410 2=bp11x528 by funext i; fin_cases i <;> rfl]; exact p11x528
private def bp11x1073 : B := ![⟨190,none⟩,⟨8,some 9⟩,⟨22,none⟩]
private def bp11x1074 : B := ![⟨190,none⟩,⟨8,some 9⟩,⟨22,some 45⟩]
private def bp11x1075 : B := ![⟨190,none⟩,⟨8,some 8⟩,⟨22,some 45⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x1075 : Deny 1000000000000000000 11 bp11x1075 :=
  sound (by decide) (by decide) 27 79082437472250233787418226623214063064192996933616261965275255008297020464483218307623396965484611714293125293260320962514653523398454953160220368909307415737487166705558227633285763323988357425 (tail:=0) (by decide +kernel)
private def bp11x1410 : B := ![⟨190,none⟩,⟨9,some 9⟩,⟨22,some 45⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x1410 : Deny 1000000000000000000 11 bp11x1410 :=
  sound (by decide) (by decide) 15 10055134763896517629100562209906345918236022107747251573708068025237720761458995437357616090785227623380135272826077 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x1074 : Deny 1000000000000000000 11 bp11x1074 := by
  apply split bp11x1074 1
  · rw [show leftB bp11x1074 1=bp11x1075 by funext i; fin_cases i <;> rfl]; exact p11x1075
  · rw [show rightB bp11x1074 1=bp11x1410 by funext i; fin_cases i <;> rfl]; exact p11x1410
private def bp11x1613 : B := ![⟨190,none⟩,⟨8,some 9⟩,⟨46,none⟩]
private def bp11x1614 : B := ![⟨190,none⟩,⟨8,some 8⟩,⟨46,none⟩]
private def bp11x1615 : B := ![⟨190,some 381⟩,⟨8,some 8⟩,⟨46,none⟩]
private def bp11x1616 : B := ![⟨190,some 381⟩,⟨8,some 8⟩,⟨46,some 93⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x1616 : Deny 1000000000000000000 11 bp11x1616 :=
  sound (by decide) (by decide) 17 3929909293895106452447572185179583917521616813569803070344788874105954856606685678994558351651121 (tail:=0) (by decide +kernel)
private def bp11x1785 : B := ![⟨190,some 381⟩,⟨8,some 8⟩,⟨94,none⟩]
private def bp11x1786 : B := ![⟨190,some 253⟩,⟨8,some 8⟩,⟨94,none⟩]
private def bp11x1787 : B := ![⟨190,some 253⟩,⟨8,some 8⟩,⟨94,some 189⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x1787 : Deny 1000000000000000000 11 bp11x1787 :=
  sound (by decide) (by decide) 16 11600831060718497212740711590277777209485937363878772610058498353 (tail:=0) (by decide +kernel)
private def bp11x1900 : B := ![⟨190,some 253⟩,⟨8,some 8⟩,⟨190,none⟩]
private def bp11x1901 : B := ![⟨190,some 217⟩,⟨8,some 8⟩,⟨190,none⟩]
private def bp11x1902 : B := ![⟨190,some 217⟩,⟨8,some 8⟩,⟨190,some 381⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x1902 : Deny 1000000000000000000 11 bp11x1902 :=
  sound (by decide) (by decide) 15 4731972828327746564227249990644229733971514962225 (tail:=0) (by decide +kernel)
private def bp11x1989 : B := ![⟨190,some 217⟩,⟨8,some 8⟩,⟨382,none⟩]
private def bp11x1990 : B := ![⟨190,some 202⟩,⟨8,some 8⟩,⟨382,none⟩]
private def bp11x1991 : B := ![⟨190,some 202⟩,⟨8,some 8⟩,⟨382,some 765⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x1991 : Deny 1000000000000000000 11 bp11x1991 :=
  sound (by decide) (by decide) 15 3602889472815409 (tail:=0) (by decide +kernel)
private def bp11x2020 : B := ![⟨190,some 202⟩,⟨8,some 8⟩,⟨766,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x2020 : Deny 1000000000000000000 11 bp11x2020 :=
  sound (by decide) (by decide) 24 347761888013613884580462452651289712797579949742288571638596661846114825799107636973207780126561967879771385559774131800193657334899714516750544686486066078333607716177369999329777842401557967799539408014026282332402509 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x1990 : Deny 1000000000000000000 11 bp11x1990 := by
  apply split bp11x1990 2
  · rw [show leftB bp11x1990 2=bp11x1991 by funext i; fin_cases i <;> rfl]; exact p11x1991
  · rw [show rightB bp11x1990 2=bp11x2020 by funext i; fin_cases i <;> rfl]; exact p11x2020
private def bp11x2393 : B := ![⟨203,some 217⟩,⟨8,some 8⟩,⟨382,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x2393 : Deny 1000000000000000000 11 bp11x2393 :=
  sound (by decide) (by decide) 15 585962026121281524167905463760502811689631179183060527604933278213549245681535315161492961051143526713937015 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x1989 : Deny 1000000000000000000 11 bp11x1989 := by
  apply split bp11x1989 0
  · rw [show leftB bp11x1989 0=bp11x1990 by funext i; fin_cases i <;> rfl]; exact p11x1990
  · rw [show rightB bp11x1989 0=bp11x2393 by funext i; fin_cases i <;> rfl]; exact p11x2393
set_option maxRecDepth 100000 in
private theorem p11x1901 : Deny 1000000000000000000 11 bp11x1901 := by
  apply split bp11x1901 2
  · rw [show leftB bp11x1901 2=bp11x1902 by funext i; fin_cases i <;> rfl]; exact p11x1902
  · rw [show rightB bp11x1901 2=bp11x1989 by funext i; fin_cases i <;> rfl]; exact p11x1989
private def bp11x2584 : B := ![⟨218,some 253⟩,⟨8,some 8⟩,⟨190,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x2584 : Deny 1000000000000000000 11 bp11x2584 :=
  sound (by decide) (by decide) 15 10169642753245737654092468060374388198945652507470111559818166183616781883470749928106603861562839827022151343264486041753745410282382670339185783 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x1900 : Deny 1000000000000000000 11 bp11x1900 := by
  apply split bp11x1900 0
  · rw [show leftB bp11x1900 0=bp11x1901 by funext i; fin_cases i <;> rfl]; exact p11x1901
  · rw [show rightB bp11x1900 0=bp11x2584 by funext i; fin_cases i <;> rfl]; exact p11x2584
set_option maxRecDepth 100000 in
private theorem p11x1786 : Deny 1000000000000000000 11 bp11x1786 := by
  apply split bp11x1786 2
  · rw [show leftB bp11x1786 2=bp11x1787 by funext i; fin_cases i <;> rfl]; exact p11x1787
  · rw [show rightB bp11x1786 2=bp11x1900 by funext i; fin_cases i <;> rfl]; exact p11x1900
private def bp11x2835 : B := ![⟨254,some 381⟩,⟨8,some 8⟩,⟨94,none⟩]
private def bp11x2836 : B := ![⟨254,some 381⟩,⟨8,some 8⟩,⟨94,some 189⟩]
private def bp11x2837 : B := ![⟨254,some 304⟩,⟨8,some 8⟩,⟨94,some 189⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x2837 : Deny 1000000000000000000 11 bp11x2837 :=
  sound (by decide) (by decide) 14 295421859946075000306791633411036608368977694768648884760643196893228572783947435161911489393832191880565404723438516111250949110367362149115476825967944344148080024491086902980672201238119124862841143 (tail:=0) (by decide +kernel)
private def bp11x3180 : B := ![⟨305,some 381⟩,⟨8,some 8⟩,⟨94,some 189⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x3180 : Deny 1000000000000000000 11 bp11x3180 :=
  sound (by decide) (by decide) 13 535842308098824996506529648819155525606254393207 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x2836 : Deny 1000000000000000000 11 bp11x2836 := by
  apply split bp11x2836 0
  · rw [show leftB bp11x2836 0=bp11x2837 by funext i; fin_cases i <;> rfl]; exact p11x2837
  · rw [show rightB bp11x2836 0=bp11x3180 by funext i; fin_cases i <;> rfl]; exact p11x3180
private def bp11x3271 : B := ![⟨254,some 381⟩,⟨8,some 8⟩,⟨190,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x3271 : Deny 1000000000000000000 11 bp11x3271 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x2835 : Deny 1000000000000000000 11 bp11x2835 := by
  apply split bp11x2835 2
  · rw [show leftB bp11x2835 2=bp11x2836 by funext i; fin_cases i <;> rfl]; exact p11x2836
  · rw [show rightB bp11x2835 2=bp11x3271 by funext i; fin_cases i <;> rfl]; exact p11x3271
set_option maxRecDepth 100000 in
private theorem p11x1785 : Deny 1000000000000000000 11 bp11x1785 := by
  apply split bp11x1785 0
  · rw [show leftB bp11x1785 0=bp11x1786 by funext i; fin_cases i <;> rfl]; exact p11x1786
  · rw [show rightB bp11x1785 0=bp11x2835 by funext i; fin_cases i <;> rfl]; exact p11x2835
set_option maxRecDepth 100000 in
private theorem p11x1615 : Deny 1000000000000000000 11 bp11x1615 := by
  apply split bp11x1615 2
  · rw [show leftB bp11x1615 2=bp11x1616 by funext i; fin_cases i <;> rfl]; exact p11x1616
  · rw [show rightB bp11x1615 2=bp11x1785 by funext i; fin_cases i <;> rfl]; exact p11x1785
private def bp11x3272 : B := ![⟨382,none⟩,⟨8,some 8⟩,⟨46,none⟩]
private def bp11x3273 : B := ![⟨382,none⟩,⟨8,some 8⟩,⟨46,some 93⟩]
private def bp11x3274 : B := ![⟨382,some 765⟩,⟨8,some 8⟩,⟨46,some 93⟩]
private def bp11x3275 : B := ![⟨382,some 765⟩,⟨8,some 8⟩,⟨46,some 61⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x3275 : Deny 1000000000000000000 11 bp11x3275 :=
  sound (by decide) (by decide) 15 52840632880340824744094908798652058461360402316007500723276440996873857263311831329099876688559332651853520638331981 (tail:=0) (by decide +kernel)
private def bp11x3478 : B := ![⟨382,some 765⟩,⟨8,some 8⟩,⟨62,some 93⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x3478 : Deny 1000000000000000000 11 bp11x3478 :=
  sound (by decide) (by decide) 15 73140776920034053385304583223436848646812547451386038260732019937225794537295969850958285757859448076021898281459987677 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x3274 : Deny 1000000000000000000 11 bp11x3274 := by
  apply split bp11x3274 2
  · rw [show leftB bp11x3274 2=bp11x3275 by funext i; fin_cases i <;> rfl]; exact p11x3275
  · rw [show rightB bp11x3274 2=bp11x3478 by funext i; fin_cases i <;> rfl]; exact p11x3478
private def bp11x3687 : B := ![⟨766,none⟩,⟨8,some 8⟩,⟨46,some 93⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x3687 : Deny 1000000000000000000 11 bp11x3687 :=
  sound (by decide) (by decide) 17 8061492166666165955537016458051511080823510742256501222852471 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x3273 : Deny 1000000000000000000 11 bp11x3273 := by
  apply split bp11x3273 0
  · rw [show leftB bp11x3273 0=bp11x3274 by funext i; fin_cases i <;> rfl]; exact p11x3274
  · rw [show rightB bp11x3273 0=bp11x3687 by funext i; fin_cases i <;> rfl]; exact p11x3687
private def bp11x3800 : B := ![⟨382,none⟩,⟨8,some 8⟩,⟨94,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x3800 : Deny 1000000000000000000 11 bp11x3800 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x3272 : Deny 1000000000000000000 11 bp11x3272 := by
  apply split bp11x3272 2
  · rw [show leftB bp11x3272 2=bp11x3273 by funext i; fin_cases i <;> rfl]; exact p11x3273
  · rw [show rightB bp11x3272 2=bp11x3800 by funext i; fin_cases i <;> rfl]; exact p11x3800
set_option maxRecDepth 100000 in
private theorem p11x1614 : Deny 1000000000000000000 11 bp11x1614 := by
  apply split bp11x1614 0
  · rw [show leftB bp11x1614 0=bp11x1615 by funext i; fin_cases i <;> rfl]; exact p11x1615
  · rw [show rightB bp11x1614 0=bp11x3272 by funext i; fin_cases i <;> rfl]; exact p11x3272
private def bp11x3801 : B := ![⟨190,none⟩,⟨9,some 9⟩,⟨46,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x3801 : Deny 1000000000000000000 11 bp11x3801 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x1613 : Deny 1000000000000000000 11 bp11x1613 := by
  apply split bp11x1613 1
  · rw [show leftB bp11x1613 1=bp11x1614 by funext i; fin_cases i <;> rfl]; exact p11x1614
  · rw [show rightB bp11x1613 1=bp11x3801 by funext i; fin_cases i <;> rfl]; exact p11x3801
set_option maxRecDepth 100000 in
private theorem p11x1073 : Deny 1000000000000000000 11 bp11x1073 := by
  apply split bp11x1073 2
  · rw [show leftB bp11x1073 2=bp11x1074 by funext i; fin_cases i <;> rfl]; exact p11x1074
  · rw [show rightB bp11x1073 2=bp11x1613 by funext i; fin_cases i <;> rfl]; exact p11x1613
set_option maxRecDepth 100000 in
private theorem p11x409 : Deny 1000000000000000000 11 bp11x409 := by
  apply split bp11x409 0
  · rw [show leftB bp11x409 0=bp11x410 by funext i; fin_cases i <;> rfl]; exact p11x410
  · rw [show rightB bp11x409 0=bp11x1073 by funext i; fin_cases i <;> rfl]; exact p11x1073
set_option maxRecDepth 100000 in
private theorem p11x255 : Deny 1000000000000000000 11 bp11x255 := by
  apply split bp11x255 2
  · rw [show leftB bp11x255 2=bp11x256 by funext i; fin_cases i <;> rfl]; exact p11x256
  · rw [show rightB bp11x255 2=bp11x409 by funext i; fin_cases i <;> rfl]; exact p11x409
set_option maxRecDepth 100000 in
private theorem p11x19 : Deny 1000000000000000000 11 bp11x19 := by
  apply split bp11x19 0
  · rw [show leftB bp11x19 0=bp11x20 by funext i; fin_cases i <;> rfl]; exact p11x20
  · rw [show rightB bp11x19 0=bp11x255 by funext i; fin_cases i <;> rfl]; exact p11x255
set_option maxRecDepth 100000 in
private theorem p11x17 : Deny 1000000000000000000 11 bp11x17 := by
  apply split bp11x17 1
  · rw [show leftB bp11x17 1=bp11x18 by funext i; fin_cases i <;> rfl]; exact p11x18
  · rw [show rightB bp11x17 1=bp11x19 by funext i; fin_cases i <;> rfl]; exact p11x19
set_option maxRecDepth 100000 in
private theorem p11x15 : Deny 1000000000000000000 11 bp11x15 := by
  apply split bp11x15 2
  · rw [show leftB bp11x15 2=bp11x16 by funext i; fin_cases i <;> rfl]; exact p11x16
  · rw [show rightB bp11x15 2=bp11x17 by funext i; fin_cases i <;> rfl]; exact p11x17
set_option maxRecDepth 100000 in
private theorem p11x13 : Deny 1000000000000000000 11 bp11x13 := by
  apply split bp11x13 0
  · rw [show leftB bp11x13 0=bp11x14 by funext i; fin_cases i <;> rfl]; exact p11x14
  · rw [show rightB bp11x13 0=bp11x15 by funext i; fin_cases i <;> rfl]; exact p11x15
set_option maxRecDepth 100000 in
private theorem p11x11 : Deny 1000000000000000000 11 bp11x11 := by
  apply split bp11x11 1
  · rw [show leftB bp11x11 1=bp11x12 by funext i; fin_cases i <;> rfl]; exact p11x12
  · rw [show rightB bp11x11 1=bp11x13 by funext i; fin_cases i <;> rfl]; exact p11x13
set_option maxRecDepth 100000 in
private theorem p11x9 : Deny 1000000000000000000 11 bp11x9 := by
  apply split bp11x9 0
  · rw [show leftB bp11x9 0=bp11x10 by funext i; fin_cases i <;> rfl]; exact p11x10
  · rw [show rightB bp11x9 0=bp11x11 by funext i; fin_cases i <;> rfl]; exact p11x11
set_option maxRecDepth 100000 in
private theorem p11x7 : Deny 1000000000000000000 11 bp11x7 := by
  apply split bp11x7 2
  · rw [show leftB bp11x7 2=bp11x8 by funext i; fin_cases i <;> rfl]; exact p11x8
  · rw [show rightB bp11x7 2=bp11x9 by funext i; fin_cases i <;> rfl]; exact p11x9
private def bp11x3802 : B := ![⟨10,none⟩,⟨10,none⟩,⟨1,none⟩]
private def bp11x3803 : B := ![⟨10,none⟩,⟨10,none⟩,⟨1,some 3⟩]
private def bp11x3804 : B := ![⟨10,some 21⟩,⟨10,none⟩,⟨1,some 3⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x3804 : Deny 1000000000000000000 11 bp11x3804 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp11x3805 : B := ![⟨22,none⟩,⟨10,none⟩,⟨1,some 3⟩]
private def bp11x3806 : B := ![⟨22,none⟩,⟨10,none⟩,⟨1,some 1⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x3806 : Deny 1000000000000000000 11 bp11x3806 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp11x3807 : B := ![⟨22,none⟩,⟨10,none⟩,⟨2,some 3⟩]
private def bp11x3808 : B := ![⟨22,none⟩,⟨10,some 21⟩,⟨2,some 3⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x3808 : Deny 1000000000000000000 11 bp11x3808 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp11x3809 : B := ![⟨22,none⟩,⟨22,none⟩,⟨2,some 3⟩]
private def bp11x3810 : B := ![⟨22,some 45⟩,⟨22,none⟩,⟨2,some 3⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x3810 : Deny 1000000000000000000 11 bp11x3810 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp11x3811 : B := ![⟨46,none⟩,⟨22,none⟩,⟨2,some 3⟩]
private def bp11x3812 : B := ![⟨46,none⟩,⟨22,some 45⟩,⟨2,some 3⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x3812 : Deny 1000000000000000000 11 bp11x3812 :=
  sound (by decide) (by decide) 36 4957083405007185429246059275134652084707335269072407032165729510046558551398887082428580104001810436965092141373880888978124617934891381898053699743008150505006889570865 (tail:=0) (by decide +kernel)
private def bp11x4105 : B := ![⟨46,none⟩,⟨46,none⟩,⟨2,some 3⟩]
private def bp11x4106 : B := ![⟨46,some 93⟩,⟨46,none⟩,⟨2,some 3⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x4106 : Deny 1000000000000000000 11 bp11x4106 :=
  sound (by decide) (by decide) 34 138635488012695123965827078683038636078221499044925088392418374327362742977305674394503415745729545888437371527409559379471815117457265717852134929357932130601790027914764057635320832291 (tail:=0) (by decide +kernel)
private def bp11x4423 : B := ![⟨94,none⟩,⟨46,none⟩,⟨2,some 3⟩]
private def bp11x4424 : B := ![⟨94,none⟩,⟨46,none⟩,⟨2,some 2⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x4424 : Deny 1000000000000000000 11 bp11x4424 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp11x4425 : B := ![⟨94,none⟩,⟨46,none⟩,⟨3,some 3⟩]
private def bp11x4426 : B := ![⟨94,none⟩,⟨46,some 93⟩,⟨3,some 3⟩]
private def bp11x4427 : B := ![⟨94,some 189⟩,⟨46,some 93⟩,⟨3,some 3⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x4427 : Deny 1000000000000000000 11 bp11x4427 :=
  sound (by decide) (by decide) 16 22683904597651311561311584560455516134904338 (tail:=0) (by decide +kernel)
private def bp11x4504 : B := ![⟨190,none⟩,⟨46,some 93⟩,⟨3,some 3⟩]
private def bp11x4505 : B := ![⟨190,none⟩,⟨46,some 61⟩,⟨3,some 3⟩]
private def bp11x4506 : B := ![⟨190,some 381⟩,⟨46,some 61⟩,⟨3,some 3⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x4506 : Deny 1000000000000000000 11 bp11x4506 :=
  sound (by decide) (by decide) 15 80604345567243707425057 (tail:=0) (by decide +kernel)
private def bp11x4549 : B := ![⟨382,none⟩,⟨46,some 61⟩,⟨3,some 3⟩]
private def bp11x4550 : B := ![⟨382,some 765⟩,⟨46,some 61⟩,⟨3,some 3⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x4550 : Deny 1000000000000000000 11 bp11x4550 :=
  sound (by decide) (by decide) 14 8508835293029732603242130922662991734367900804674103422343794206234516602425270661412311827590 (tail:=0) (by decide +kernel)
private def bp11x4713 : B := ![⟨766,none⟩,⟨46,some 61⟩,⟨3,some 3⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x4713 : Deny 1000000000000000000 11 bp11x4713 :=
  sound (by decide) (by decide) 19 46718822049882655579393731929318470249205808304171956433402577698086781478657449168828135442703749292038425311160541705167980646 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x4549 : Deny 1000000000000000000 11 bp11x4549 := by
  apply split bp11x4549 0
  · rw [show leftB bp11x4549 0=bp11x4550 by funext i; fin_cases i <;> rfl]; exact p11x4550
  · rw [show rightB bp11x4549 0=bp11x4713 by funext i; fin_cases i <;> rfl]; exact p11x4713
set_option maxRecDepth 100000 in
private theorem p11x4505 : Deny 1000000000000000000 11 bp11x4505 := by
  apply split bp11x4505 0
  · rw [show leftB bp11x4505 0=bp11x4506 by funext i; fin_cases i <;> rfl]; exact p11x4506
  · rw [show rightB bp11x4505 0=bp11x4549 by funext i; fin_cases i <;> rfl]; exact p11x4549
private def bp11x4934 : B := ![⟨190,none⟩,⟨62,some 93⟩,⟨3,some 3⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x4934 : Deny 1000000000000000000 11 bp11x4934 :=
  sound (by decide) (by decide) 15 16801932314388466246827372050882383450440642298986552726271343737070318532068379143159958172836239264335571762318195016795361330770557533334392551214838248295755475535284325 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x4504 : Deny 1000000000000000000 11 bp11x4504 := by
  apply split bp11x4504 1
  · rw [show leftB bp11x4504 1=bp11x4505 by funext i; fin_cases i <;> rfl]; exact p11x4505
  · rw [show rightB bp11x4504 1=bp11x4934 by funext i; fin_cases i <;> rfl]; exact p11x4934
set_option maxRecDepth 100000 in
private theorem p11x4426 : Deny 1000000000000000000 11 bp11x4426 := by
  apply split bp11x4426 0
  · rw [show leftB bp11x4426 0=bp11x4427 by funext i; fin_cases i <;> rfl]; exact p11x4427
  · rw [show rightB bp11x4426 0=bp11x4504 by funext i; fin_cases i <;> rfl]; exact p11x4504
private def bp11x5231 : B := ![⟨94,none⟩,⟨94,none⟩,⟨3,some 3⟩]
private def bp11x5232 : B := ![⟨94,some 189⟩,⟨94,none⟩,⟨3,some 3⟩]
private def bp11x5233 : B := ![⟨94,some 189⟩,⟨94,some 189⟩,⟨3,some 3⟩]
private def bp11x5234 : B := ![⟨94,some 125⟩,⟨94,some 189⟩,⟨3,some 3⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x5234 : Deny 1000000000000000000 11 bp11x5234 :=
  sound (by decide) (by decide) 15 54249486449421387640856335336536325637546578450 (tail:=0) (by decide +kernel)
private def bp11x5317 : B := ![⟨126,some 189⟩,⟨94,some 189⟩,⟨3,some 3⟩]
private def bp11x5318 : B := ![⟨126,some 189⟩,⟨94,some 125⟩,⟨3,some 3⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x5318 : Deny 1000000000000000000 11 bp11x5318 :=
  sound (by decide) (by decide) 13 52259369276950654200116385486784145797496728061634955330209636717038168288405140504230913589836643089740145789620943963061653861439621 (tail:=0) (by decide +kernel)
private def bp11x5549 : B := ![⟨126,some 189⟩,⟨126,some 189⟩,⟨3,some 3⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x5549 : Deny 1000000000000000000 11 bp11x5549 :=
  sound (by decide) (by decide) 13 21895206596732403426009998727090493815331359240465597205849670848761433033602121988583459085427097 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x5317 : Deny 1000000000000000000 11 bp11x5317 := by
  apply split bp11x5317 1
  · rw [show leftB bp11x5317 1=bp11x5318 by funext i; fin_cases i <;> rfl]; exact p11x5318
  · rw [show rightB bp11x5317 1=bp11x5549 by funext i; fin_cases i <;> rfl]; exact p11x5549
set_option maxRecDepth 100000 in
private theorem p11x5233 : Deny 1000000000000000000 11 bp11x5233 := by
  apply split bp11x5233 0
  · rw [show leftB bp11x5233 0=bp11x5234 by funext i; fin_cases i <;> rfl]; exact p11x5234
  · rw [show rightB bp11x5233 0=bp11x5317 by funext i; fin_cases i <;> rfl]; exact p11x5317
private def bp11x5720 : B := ![⟨94,some 189⟩,⟨190,none⟩,⟨3,some 3⟩]
private def bp11x5721 : B := ![⟨94,some 125⟩,⟨190,none⟩,⟨3,some 3⟩]
private def bp11x5722 : B := ![⟨94,some 125⟩,⟨190,some 381⟩,⟨3,some 3⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x5722 : Deny 1000000000000000000 11 bp11x5722 :=
  sound (by decide) (by decide) 15 1965655855532773724890842721144759019030479481166699748751261397515576711964587142475492293699850467860876927288234733285417577501243349065 (tail:=0) (by decide +kernel)
private def bp11x5961 : B := ![⟨94,some 125⟩,⟨382,none⟩,⟨3,some 3⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x5961 : Deny 1000000000000000000 11 bp11x5961 :=
  sound (by decide) (by decide) 18 1631603016662170503656403377085179728684306693802328173345401481270370876183210470122588468357888470549873306406919055623309262151628606752872800665 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x5721 : Deny 1000000000000000000 11 bp11x5721 := by
  apply split bp11x5721 1
  · rw [show leftB bp11x5721 1=bp11x5722 by funext i; fin_cases i <;> rfl]; exact p11x5722
  · rw [show rightB bp11x5721 1=bp11x5961 by funext i; fin_cases i <;> rfl]; exact p11x5961
private def bp11x6218 : B := ![⟨126,some 189⟩,⟨190,none⟩,⟨3,some 3⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x6218 : Deny 1000000000000000000 11 bp11x6218 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x5720 : Deny 1000000000000000000 11 bp11x5720 := by
  apply split bp11x5720 0
  · rw [show leftB bp11x5720 0=bp11x5721 by funext i; fin_cases i <;> rfl]; exact p11x5721
  · rw [show rightB bp11x5720 0=bp11x6218 by funext i; fin_cases i <;> rfl]; exact p11x6218
set_option maxRecDepth 100000 in
private theorem p11x5232 : Deny 1000000000000000000 11 bp11x5232 := by
  apply split bp11x5232 1
  · rw [show leftB bp11x5232 1=bp11x5233 by funext i; fin_cases i <;> rfl]; exact p11x5233
  · rw [show rightB bp11x5232 1=bp11x5720 by funext i; fin_cases i <;> rfl]; exact p11x5720
private def bp11x6219 : B := ![⟨190,none⟩,⟨94,none⟩,⟨3,some 3⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x6219 : Deny 1000000000000000000 11 bp11x6219 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x5231 : Deny 1000000000000000000 11 bp11x5231 := by
  apply split bp11x5231 0
  · rw [show leftB bp11x5231 0=bp11x5232 by funext i; fin_cases i <;> rfl]; exact p11x5232
  · rw [show rightB bp11x5231 0=bp11x6219 by funext i; fin_cases i <;> rfl]; exact p11x6219
set_option maxRecDepth 100000 in
private theorem p11x4425 : Deny 1000000000000000000 11 bp11x4425 := by
  apply split bp11x4425 1
  · rw [show leftB bp11x4425 1=bp11x4426 by funext i; fin_cases i <;> rfl]; exact p11x4426
  · rw [show rightB bp11x4425 1=bp11x5231 by funext i; fin_cases i <;> rfl]; exact p11x5231
set_option maxRecDepth 100000 in
private theorem p11x4423 : Deny 1000000000000000000 11 bp11x4423 := by
  apply split bp11x4423 2
  · rw [show leftB bp11x4423 2=bp11x4424 by funext i; fin_cases i <;> rfl]; exact p11x4424
  · rw [show rightB bp11x4423 2=bp11x4425 by funext i; fin_cases i <;> rfl]; exact p11x4425
set_option maxRecDepth 100000 in
private theorem p11x4105 : Deny 1000000000000000000 11 bp11x4105 := by
  apply split bp11x4105 0
  · rw [show leftB bp11x4105 0=bp11x4106 by funext i; fin_cases i <;> rfl]; exact p11x4106
  · rw [show rightB bp11x4105 0=bp11x4423 by funext i; fin_cases i <;> rfl]; exact p11x4423
set_option maxRecDepth 100000 in
private theorem p11x3811 : Deny 1000000000000000000 11 bp11x3811 := by
  apply split bp11x3811 1
  · rw [show leftB bp11x3811 1=bp11x3812 by funext i; fin_cases i <;> rfl]; exact p11x3812
  · rw [show rightB bp11x3811 1=bp11x4105 by funext i; fin_cases i <;> rfl]; exact p11x4105
set_option maxRecDepth 100000 in
private theorem p11x3809 : Deny 1000000000000000000 11 bp11x3809 := by
  apply split bp11x3809 0
  · rw [show leftB bp11x3809 0=bp11x3810 by funext i; fin_cases i <;> rfl]; exact p11x3810
  · rw [show rightB bp11x3809 0=bp11x3811 by funext i; fin_cases i <;> rfl]; exact p11x3811
set_option maxRecDepth 100000 in
private theorem p11x3807 : Deny 1000000000000000000 11 bp11x3807 := by
  apply split bp11x3807 1
  · rw [show leftB bp11x3807 1=bp11x3808 by funext i; fin_cases i <;> rfl]; exact p11x3808
  · rw [show rightB bp11x3807 1=bp11x3809 by funext i; fin_cases i <;> rfl]; exact p11x3809
set_option maxRecDepth 100000 in
private theorem p11x3805 : Deny 1000000000000000000 11 bp11x3805 := by
  apply split bp11x3805 2
  · rw [show leftB bp11x3805 2=bp11x3806 by funext i; fin_cases i <;> rfl]; exact p11x3806
  · rw [show rightB bp11x3805 2=bp11x3807 by funext i; fin_cases i <;> rfl]; exact p11x3807
set_option maxRecDepth 100000 in
private theorem p11x3803 : Deny 1000000000000000000 11 bp11x3803 := by
  apply split bp11x3803 0
  · rw [show leftB bp11x3803 0=bp11x3804 by funext i; fin_cases i <;> rfl]; exact p11x3804
  · rw [show rightB bp11x3803 0=bp11x3805 by funext i; fin_cases i <;> rfl]; exact p11x3805
private def bp11x6220 : B := ![⟨10,none⟩,⟨10,none⟩,⟨4,none⟩]
private def bp11x6221 : B := ![⟨10,some 21⟩,⟨10,none⟩,⟨4,none⟩]
private def bp11x6222 : B := ![⟨10,some 13⟩,⟨10,none⟩,⟨4,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x6222 : Deny 1000000000000000000 11 bp11x6222 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp11x6223 : B := ![⟨14,some 21⟩,⟨10,none⟩,⟨4,none⟩]
private def bp11x6224 : B := ![⟨14,some 21⟩,⟨10,some 21⟩,⟨4,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x6224 : Deny 1000000000000000000 11 bp11x6224 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp11x6225 : B := ![⟨14,some 21⟩,⟨22,none⟩,⟨4,none⟩]
private def bp11x6226 : B := ![⟨14,some 21⟩,⟨22,none⟩,⟨4,some 9⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x6226 : Deny 1000000000000000000 11 bp11x6226 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp11x6227 : B := ![⟨14,some 21⟩,⟨22,none⟩,⟨10,none⟩]
private def bp11x6228 : B := ![⟨14,some 21⟩,⟨22,some 45⟩,⟨10,none⟩]
private def bp11x6229 : B := ![⟨14,some 16⟩,⟨22,some 45⟩,⟨10,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x6229 : Deny 1000000000000000000 11 bp11x6229 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp11x6230 : B := ![⟨17,some 21⟩,⟨22,some 45⟩,⟨10,none⟩]
private def bp11x6231 : B := ![⟨17,some 21⟩,⟨22,some 45⟩,⟨10,some 21⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x6231 : Deny 1000000000000000000 11 bp11x6231 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp11x6232 : B := ![⟨17,some 21⟩,⟨22,some 45⟩,⟨22,none⟩]
private def bp11x6233 : B := ![⟨17,some 21⟩,⟨22,some 29⟩,⟨22,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x6233 : Deny 1000000000000000000 11 bp11x6233 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp11x6234 : B := ![⟨17,some 21⟩,⟨30,some 45⟩,⟨22,none⟩]
private def bp11x6235 : B := ![⟨17,some 18⟩,⟨30,some 45⟩,⟨22,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x6235 : Deny 1000000000000000000 11 bp11x6235 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp11x6236 : B := ![⟨19,some 21⟩,⟨30,some 45⟩,⟨22,none⟩]
private def bp11x6237 : B := ![⟨19,some 21⟩,⟨30,some 45⟩,⟨22,some 45⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x6237 : Deny 1000000000000000000 11 bp11x6237 :=
  sound (by decide) (by decide) 14 57997804688188178 (tail:=0) (by decide +kernel)
private def bp11x6268 : B := ![⟨19,some 21⟩,⟨30,some 45⟩,⟨46,none⟩]
private def bp11x6269 : B := ![⟨19,some 21⟩,⟨30,some 36⟩,⟨46,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x6269 : Deny 1000000000000000000 11 bp11x6269 :=
  sound (by decide) (by decide) 19 329341965465367740206442570876264259973972020557303322004735537 (tail:=0) (by decide +kernel)
private def bp11x6380 : B := ![⟨19,some 21⟩,⟨37,some 45⟩,⟨46,none⟩]
private def bp11x6381 : B := ![⟨19,some 19⟩,⟨37,some 45⟩,⟨46,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x6381 : Deny 1000000000000000000 11 bp11x6381 :=
  sound (by decide) (by decide) 29 2154778733949626481558389342893172558441465929975808445179758641823609499976428648739535351979324195 (tail:=0) (by decide +kernel)
private def bp11x6554 : B := ![⟨20,some 21⟩,⟨37,some 45⟩,⟨46,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x6554 : Deny 1000000000000000000 11 bp11x6554 :=
  sound (by decide) (by decide) 21 798079163313260433228081276080311121623945336110704679373816060316135724508558480819040910599069446742093744791910421804940977599156821822285873475784475 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x6380 : Deny 1000000000000000000 11 bp11x6380 := by
  apply split bp11x6380 0
  · rw [show leftB bp11x6380 0=bp11x6381 by funext i; fin_cases i <;> rfl]; exact p11x6381
  · rw [show rightB bp11x6380 0=bp11x6554 by funext i; fin_cases i <;> rfl]; exact p11x6554
set_option maxRecDepth 100000 in
private theorem p11x6268 : Deny 1000000000000000000 11 bp11x6268 := by
  apply split bp11x6268 1
  · rw [show leftB bp11x6268 1=bp11x6269 by funext i; fin_cases i <;> rfl]; exact p11x6269
  · rw [show rightB bp11x6268 1=bp11x6380 by funext i; fin_cases i <;> rfl]; exact p11x6380
set_option maxRecDepth 100000 in
private theorem p11x6236 : Deny 1000000000000000000 11 bp11x6236 := by
  apply split bp11x6236 2
  · rw [show leftB bp11x6236 2=bp11x6237 by funext i; fin_cases i <;> rfl]; exact p11x6237
  · rw [show rightB bp11x6236 2=bp11x6268 by funext i; fin_cases i <;> rfl]; exact p11x6268
set_option maxRecDepth 100000 in
private theorem p11x6234 : Deny 1000000000000000000 11 bp11x6234 := by
  apply split bp11x6234 0
  · rw [show leftB bp11x6234 0=bp11x6235 by funext i; fin_cases i <;> rfl]; exact p11x6235
  · rw [show rightB bp11x6234 0=bp11x6236 by funext i; fin_cases i <;> rfl]; exact p11x6236
set_option maxRecDepth 100000 in
private theorem p11x6232 : Deny 1000000000000000000 11 bp11x6232 := by
  apply split bp11x6232 1
  · rw [show leftB bp11x6232 1=bp11x6233 by funext i; fin_cases i <;> rfl]; exact p11x6233
  · rw [show rightB bp11x6232 1=bp11x6234 by funext i; fin_cases i <;> rfl]; exact p11x6234
set_option maxRecDepth 100000 in
private theorem p11x6230 : Deny 1000000000000000000 11 bp11x6230 := by
  apply split bp11x6230 2
  · rw [show leftB bp11x6230 2=bp11x6231 by funext i; fin_cases i <;> rfl]; exact p11x6231
  · rw [show rightB bp11x6230 2=bp11x6232 by funext i; fin_cases i <;> rfl]; exact p11x6232
set_option maxRecDepth 100000 in
private theorem p11x6228 : Deny 1000000000000000000 11 bp11x6228 := by
  apply split bp11x6228 0
  · rw [show leftB bp11x6228 0=bp11x6229 by funext i; fin_cases i <;> rfl]; exact p11x6229
  · rw [show rightB bp11x6228 0=bp11x6230 by funext i; fin_cases i <;> rfl]; exact p11x6230
private def bp11x6817 : B := ![⟨14,some 21⟩,⟨46,none⟩,⟨10,none⟩]
private def bp11x6818 : B := ![⟨14,some 16⟩,⟨46,none⟩,⟨10,none⟩]
private def bp11x6819 : B := ![⟨14,some 16⟩,⟨46,none⟩,⟨10,some 21⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x6819 : Deny 1000000000000000000 11 bp11x6819 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp11x6820 : B := ![⟨14,some 16⟩,⟨46,none⟩,⟨22,none⟩]
private def bp11x6821 : B := ![⟨14,some 16⟩,⟨46,some 93⟩,⟨22,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x6821 : Deny 1000000000000000000 11 bp11x6821 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp11x6822 : B := ![⟨14,some 16⟩,⟨94,none⟩,⟨22,none⟩]
private def bp11x6823 : B := ![⟨14,some 16⟩,⟨94,none⟩,⟨22,some 45⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x6823 : Deny 1000000000000000000 11 bp11x6823 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp11x6824 : B := ![⟨14,some 16⟩,⟨94,none⟩,⟨46,none⟩]
private def bp11x6825 : B := ![⟨14,some 14⟩,⟨94,none⟩,⟨46,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x6825 : Deny 1000000000000000000 11 bp11x6825 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp11x6826 : B := ![⟨15,some 16⟩,⟨94,none⟩,⟨46,none⟩]
private def bp11x6827 : B := ![⟨15,some 16⟩,⟨94,some 189⟩,⟨46,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x6827 : Deny 1000000000000000000 11 bp11x6827 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp11x6828 : B := ![⟨15,some 16⟩,⟨190,none⟩,⟨46,none⟩]
private def bp11x6829 : B := ![⟨15,some 16⟩,⟨190,none⟩,⟨46,some 93⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x6829 : Deny 1000000000000000000 11 bp11x6829 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp11x6830 : B := ![⟨15,some 16⟩,⟨190,none⟩,⟨94,none⟩]
private def bp11x6831 : B := ![⟨15,some 15⟩,⟨190,none⟩,⟨94,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x6831 : Deny 1000000000000000000 11 bp11x6831 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp11x6832 : B := ![⟨16,some 16⟩,⟨190,none⟩,⟨94,none⟩]
private def bp11x6833 : B := ![⟨16,some 16⟩,⟨190,some 381⟩,⟨94,none⟩]
private def bp11x6834 : B := ![⟨16,some 16⟩,⟨190,some 381⟩,⟨94,some 189⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x6834 : Deny 1000000000000000000 11 bp11x6834 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp11x6835 : B := ![⟨16,some 16⟩,⟨190,some 381⟩,⟨190,none⟩]
private def bp11x6836 : B := ![⟨16,some 16⟩,⟨190,some 253⟩,⟨190,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x6836 : Deny 1000000000000000000 11 bp11x6836 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp11x6837 : B := ![⟨16,some 16⟩,⟨254,some 381⟩,⟨190,none⟩]
private def bp11x6838 : B := ![⟨16,some 16⟩,⟨254,some 381⟩,⟨190,some 381⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x6838 : Deny 1000000000000000000 11 bp11x6838 :=
  sound (by decide) (by decide) 18 973412530210902291657266 (tail:=0) (by decide +kernel)
private def bp11x6881 : B := ![⟨16,some 16⟩,⟨254,some 381⟩,⟨382,none⟩]
private def bp11x6882 : B := ![⟨16,some 16⟩,⟨254,some 304⟩,⟨382,none⟩]
private def bp11x6883 : B := ![⟨16,some 16⟩,⟨254,some 304⟩,⟨382,some 765⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x6883 : Deny 1000000000000000000 11 bp11x6883 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp11x6884 : B := ![⟨16,some 16⟩,⟨254,some 304⟩,⟨766,none⟩]
private def bp11x6885 : B := ![⟨16,some 16⟩,⟨254,some 276⟩,⟨766,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x6885 : Deny 1000000000000000000 11 bp11x6885 :=
  sound (by decide) (by decide) 27 866672730314442967711402656483581029001210096983802534391936092130317432522730330321597996057317424303016028269914483515758495803961367778314155250526723551942353699 (tail:=0) (by decide +kernel)
private def bp11x7166 : B := ![⟨16,some 16⟩,⟨277,some 304⟩,⟨766,none⟩]
private def bp11x7167 : B := ![⟨16,some 16⟩,⟨277,some 304⟩,⟨766,some 1533⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x7167 : Deny 1000000000000000000 11 bp11x7167 :=
  sound (by decide) (by decide) 17 9085507690941673478415403525201403264109829091501832771349733226440014844672682560536442958132341066778720538758539378580729107352754 (tail:=0) (by decide +kernel)
private def bp11x7396 : B := ![⟨16,some 16⟩,⟨277,some 304⟩,⟨1534,none⟩]
private def bp11x7397 : B := ![⟨16,some 16⟩,⟨277,some 289⟩,⟨1534,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x7397 : Deny 1000000000000000000 11 bp11x7397 :=
  sound (by decide) (by decide) 19 5366387757516594975331099915419691385594323561303551051992257316995906527274348583914694933004071480021577050816156599896498659673562082622988132594835807118080227733801358499999977674294155679879314056212698571579 (tail:=0) (by decide +kernel)
private def bp11x7764 : B := ![⟨16,some 16⟩,⟨290,some 304⟩,⟨1534,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x7764 : Deny 1000000000000000000 11 bp11x7764 :=
  sound (by decide) (by decide) 16 1251808232105483043382730895291 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x7396 : Deny 1000000000000000000 11 bp11x7396 := by
  apply split bp11x7396 1
  · rw [show leftB bp11x7396 1=bp11x7397 by funext i; fin_cases i <;> rfl]; exact p11x7397
  · rw [show rightB bp11x7396 1=bp11x7764 by funext i; fin_cases i <;> rfl]; exact p11x7764
set_option maxRecDepth 100000 in
private theorem p11x7166 : Deny 1000000000000000000 11 bp11x7166 := by
  apply split bp11x7166 2
  · rw [show leftB bp11x7166 2=bp11x7167 by funext i; fin_cases i <;> rfl]; exact p11x7167
  · rw [show rightB bp11x7166 2=bp11x7396 by funext i; fin_cases i <;> rfl]; exact p11x7396
set_option maxRecDepth 100000 in
private theorem p11x6884 : Deny 1000000000000000000 11 bp11x6884 := by
  apply split bp11x6884 1
  · rw [show leftB bp11x6884 1=bp11x6885 by funext i; fin_cases i <;> rfl]; exact p11x6885
  · rw [show rightB bp11x6884 1=bp11x7166 by funext i; fin_cases i <;> rfl]; exact p11x7166
set_option maxRecDepth 100000 in
private theorem p11x6882 : Deny 1000000000000000000 11 bp11x6882 := by
  apply split bp11x6882 2
  · rw [show leftB bp11x6882 2=bp11x6883 by funext i; fin_cases i <;> rfl]; exact p11x6883
  · rw [show rightB bp11x6882 2=bp11x6884 by funext i; fin_cases i <;> rfl]; exact p11x6884
private def bp11x7825 : B := ![⟨16,some 16⟩,⟨305,some 381⟩,⟨382,none⟩]
private def bp11x7826 : B := ![⟨16,some 16⟩,⟨305,some 381⟩,⟨382,some 765⟩]
private def bp11x7827 : B := ![⟨16,some 16⟩,⟨305,some 338⟩,⟨382,some 765⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x7827 : Deny 1000000000000000000 11 bp11x7827 :=
  sound (by decide) (by decide) 16 12377535383294614188460091052015888204969258727993222916093439085111609048357599815190507182010233857386697144904322669137209211805063740562103217620685817658762766349551843 (tail:=0) (by decide +kernel)
private def bp11x8122 : B := ![⟨16,some 16⟩,⟨339,some 381⟩,⟨382,some 765⟩]
private def bp11x8123 : B := ![⟨16,some 16⟩,⟨339,some 381⟩,⟨382,some 509⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x8123 : Deny 1000000000000000000 11 bp11x8123 :=
  sound (by decide) (by decide) 15 335005220031050766094196717281152408832948828656799644652367108324880530678130458629777064168775795206222010477068695817496631471314004688150553331798266919455156488869207480153722392624644860029538132242683077518 (tail:=0) (by decide +kernel)
private def bp11x8486 : B := ![⟨16,some 16⟩,⟨339,some 381⟩,⟨510,some 765⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x8486 : Deny 1000000000000000000 11 bp11x8486 :=
  sound (by decide) (by decide) 13 300038801186739962119401198 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x8122 : Deny 1000000000000000000 11 bp11x8122 := by
  apply split bp11x8122 2
  · rw [show leftB bp11x8122 2=bp11x8123 by funext i; fin_cases i <;> rfl]; exact p11x8123
  · rw [show rightB bp11x8122 2=bp11x8486 by funext i; fin_cases i <;> rfl]; exact p11x8486
set_option maxRecDepth 100000 in
private theorem p11x7826 : Deny 1000000000000000000 11 bp11x7826 := by
  apply split bp11x7826 1
  · rw [show leftB bp11x7826 1=bp11x7827 by funext i; fin_cases i <;> rfl]; exact p11x7827
  · rw [show rightB bp11x7826 1=bp11x8122 by funext i; fin_cases i <;> rfl]; exact p11x8122
private def bp11x8541 : B := ![⟨16,some 16⟩,⟨305,some 381⟩,⟨766,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x8541 : Deny 1000000000000000000 11 bp11x8541 :=
  sound (by decide) (by decide) 18 38316490722119787009443202930780944929573965153732757653164275033244850802719863501849683012222775372420582944494 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x7825 : Deny 1000000000000000000 11 bp11x7825 := by
  apply split bp11x7825 2
  · rw [show leftB bp11x7825 2=bp11x7826 by funext i; fin_cases i <;> rfl]; exact p11x7826
  · rw [show rightB bp11x7825 2=bp11x8541 by funext i; fin_cases i <;> rfl]; exact p11x8541
set_option maxRecDepth 100000 in
private theorem p11x6881 : Deny 1000000000000000000 11 bp11x6881 := by
  apply split bp11x6881 1
  · rw [show leftB bp11x6881 1=bp11x6882 by funext i; fin_cases i <;> rfl]; exact p11x6882
  · rw [show rightB bp11x6881 1=bp11x7825 by funext i; fin_cases i <;> rfl]; exact p11x7825
set_option maxRecDepth 100000 in
private theorem p11x6837 : Deny 1000000000000000000 11 bp11x6837 := by
  apply split bp11x6837 2
  · rw [show leftB bp11x6837 2=bp11x6838 by funext i; fin_cases i <;> rfl]; exact p11x6838
  · rw [show rightB bp11x6837 2=bp11x6881 by funext i; fin_cases i <;> rfl]; exact p11x6881
set_option maxRecDepth 100000 in
private theorem p11x6835 : Deny 1000000000000000000 11 bp11x6835 := by
  apply split bp11x6835 1
  · rw [show leftB bp11x6835 1=bp11x6836 by funext i; fin_cases i <;> rfl]; exact p11x6836
  · rw [show rightB bp11x6835 1=bp11x6837 by funext i; fin_cases i <;> rfl]; exact p11x6837
set_option maxRecDepth 100000 in
private theorem p11x6833 : Deny 1000000000000000000 11 bp11x6833 := by
  apply split bp11x6833 2
  · rw [show leftB bp11x6833 2=bp11x6834 by funext i; fin_cases i <;> rfl]; exact p11x6834
  · rw [show rightB bp11x6833 2=bp11x6835 by funext i; fin_cases i <;> rfl]; exact p11x6835
private def bp11x8742 : B := ![⟨16,some 16⟩,⟨382,none⟩,⟨94,none⟩]
private def bp11x8743 : B := ![⟨16,some 16⟩,⟨382,none⟩,⟨94,some 189⟩]
private def bp11x8744 : B := ![⟨16,some 16⟩,⟨382,some 765⟩,⟨94,some 189⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x8744 : Deny 1000000000000000000 11 bp11x8744 :=
  sound (by decide) (by decide) 19 119284432124611570049472388257852426467455777597858062879536779910143687456730554656709496941465264156586131013812223366704701979034210944705814697615687361315 (tail:=0) (by decide +kernel)
private def bp11x9015 : B := ![⟨16,some 16⟩,⟨766,none⟩,⟨94,some 189⟩]
private def bp11x9016 : B := ![⟨16,some 16⟩,⟨766,none⟩,⟨94,some 125⟩]
private def bp11x9017 : B := ![⟨16,some 16⟩,⟨766,some 1533⟩,⟨94,some 125⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x9017 : Deny 1000000000000000000 11 bp11x9017 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp11x9018 : B := ![⟨16,some 16⟩,⟨1534,none⟩,⟨94,some 125⟩]
private def bp11x9019 : B := ![⟨16,some 16⟩,⟨1534,none⟩,⟨94,some 107⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x9019 : Deny 1000000000000000000 11 bp11x9019 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp11x9020 : B := ![⟨16,some 16⟩,⟨1534,none⟩,⟨108,some 125⟩]
private def bp11x9021 : B := ![⟨16,some 16⟩,⟨1534,some 3069⟩,⟨108,some 125⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x9021 : Deny 1000000000000000000 11 bp11x9021 :=
  sound (by decide) (by decide) 18 6325586496565792763716863476530486417772199994582103663795493715108823660791293197527574293781814973412913759870568675 (tail:=0) (by decide +kernel)
private def bp11x9226 : B := ![⟨16,some 16⟩,⟨3070,none⟩,⟨108,some 125⟩]
private def bp11x9227 : B := ![⟨16,some 16⟩,⟨3070,none⟩,⟨108,some 115⟩]
private def bp11x9228 : B := ![⟨16,some 16⟩,⟨3070,some 6141⟩,⟨108,some 115⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x9228 : Deny 1000000000000000000 11 bp11x9228 :=
  sound (by decide) (by decide) 17 819211834946136347419021163932439194738176180735199431920419 (tail:=0) (by decide +kernel)
private def bp11x9335 : B := ![⟨16,some 16⟩,⟨6142,none⟩,⟨108,some 115⟩]
private def bp11x9336 : B := ![⟨16,some 16⟩,⟨6142,none⟩,⟨108,some 111⟩]
private def bp11x9337 : B := ![⟨16,some 16⟩,⟨6142,some 12285⟩,⟨108,some 111⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x9337 : Deny 1000000000000000000 11 bp11x9337 :=
  sound (by decide) (by decide) 16 14903791721441999979092151843 (tail:=0) (by decide +kernel)
private def bp11x9386 : B := ![⟨16,some 16⟩,⟨12286,none⟩,⟨108,some 111⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x9386 : Deny 1000000000000000000 11 bp11x9386 :=
  sound (by decide) (by decide) 26 10229493281215268689248421744396338743336336342372315961447962615650445200482906296216159252022904773423328608325751022977018209820198840340984115241376816351021645592780577373520475265167759630467925713803 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x9336 : Deny 1000000000000000000 11 bp11x9336 := by
  apply split bp11x9336 1
  · rw [show leftB bp11x9336 1=bp11x9337 by funext i; fin_cases i <;> rfl]; exact p11x9337
  · rw [show rightB bp11x9336 1=bp11x9386 by funext i; fin_cases i <;> rfl]; exact p11x9386
private def bp11x9737 : B := ![⟨16,some 16⟩,⟨6142,none⟩,⟨112,some 115⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x9737 : Deny 1000000000000000000 11 bp11x9737 :=
  sound (by decide) (by decide) 17 2452782475584914350 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x9335 : Deny 1000000000000000000 11 bp11x9335 := by
  apply split bp11x9335 2
  · rw [show leftB bp11x9335 2=bp11x9336 by funext i; fin_cases i <;> rfl]; exact p11x9336
  · rw [show rightB bp11x9335 2=bp11x9737 by funext i; fin_cases i <;> rfl]; exact p11x9737
set_option maxRecDepth 100000 in
private theorem p11x9227 : Deny 1000000000000000000 11 bp11x9227 := by
  apply split bp11x9227 1
  · rw [show leftB bp11x9227 1=bp11x9228 by funext i; fin_cases i <;> rfl]; exact p11x9228
  · rw [show rightB bp11x9227 1=bp11x9335 by funext i; fin_cases i <;> rfl]; exact p11x9335
private def bp11x9778 : B := ![⟨16,some 16⟩,⟨3070,none⟩,⟨116,some 125⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x9778 : Deny 1000000000000000000 11 bp11x9778 :=
  sound (by decide) (by decide) 17 12035323043620841000798962996817080246395630 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x9226 : Deny 1000000000000000000 11 bp11x9226 := by
  apply split bp11x9226 2
  · rw [show leftB bp11x9226 2=bp11x9227 by funext i; fin_cases i <;> rfl]; exact p11x9227
  · rw [show rightB bp11x9226 2=bp11x9778 by funext i; fin_cases i <;> rfl]; exact p11x9778
set_option maxRecDepth 100000 in
private theorem p11x9020 : Deny 1000000000000000000 11 bp11x9020 := by
  apply split bp11x9020 1
  · rw [show leftB bp11x9020 1=bp11x9021 by funext i; fin_cases i <;> rfl]; exact p11x9021
  · rw [show rightB bp11x9020 1=bp11x9226 by funext i; fin_cases i <;> rfl]; exact p11x9226
set_option maxRecDepth 100000 in
private theorem p11x9018 : Deny 1000000000000000000 11 bp11x9018 := by
  apply split bp11x9018 2
  · rw [show leftB bp11x9018 2=bp11x9019 by funext i; fin_cases i <;> rfl]; exact p11x9019
  · rw [show rightB bp11x9018 2=bp11x9020 by funext i; fin_cases i <;> rfl]; exact p11x9020
set_option maxRecDepth 100000 in
private theorem p11x9016 : Deny 1000000000000000000 11 bp11x9016 := by
  apply split bp11x9016 1
  · rw [show leftB bp11x9016 1=bp11x9017 by funext i; fin_cases i <;> rfl]; exact p11x9017
  · rw [show rightB bp11x9016 1=bp11x9018 by funext i; fin_cases i <;> rfl]; exact p11x9018
private def bp11x9861 : B := ![⟨16,some 16⟩,⟨766,none⟩,⟨126,some 189⟩]
private def bp11x9862 : B := ![⟨16,some 16⟩,⟨766,some 1533⟩,⟨126,some 189⟩]
private def bp11x9863 : B := ![⟨16,some 16⟩,⟨766,some 1533⟩,⟨126,some 151⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x9863 : Deny 1000000000000000000 11 bp11x9863 :=
  sound (by decide) (by decide) 17 53303480766825140543961220386909716456196790862019703499778564344223681161782974256473553136862369114538004034079261724631240774965811592837419504881296809109403685202367953978047686276076668473661751965319466126 (tail:=0) (by decide +kernel)
private def bp11x10224 : B := ![⟨16,some 16⟩,⟨766,some 1533⟩,⟨152,some 189⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x10224 : Deny 1000000000000000000 11 bp11x10224 :=
  sound (by decide) (by decide) 15 24623857524738824152287670917884268923573678433578174645369784549926159512419798832772080023331573299607403335398219166838751172375278 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x9862 : Deny 1000000000000000000 11 bp11x9862 := by
  apply split bp11x9862 2
  · rw [show leftB bp11x9862 2=bp11x9863 by funext i; fin_cases i <;> rfl]; exact p11x9863
  · rw [show rightB bp11x9862 2=bp11x10224 by funext i; fin_cases i <;> rfl]; exact p11x10224
private def bp11x10457 : B := ![⟨16,some 16⟩,⟨1534,none⟩,⟨126,some 189⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x10457 : Deny 1000000000000000000 11 bp11x10457 :=
  sound (by decide) (by decide) 18 1201691584558797574617280580887212699439810674401498312549628375431398603707 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x9861 : Deny 1000000000000000000 11 bp11x9861 := by
  apply split bp11x9861 1
  · rw [show leftB bp11x9861 1=bp11x9862 by funext i; fin_cases i <;> rfl]; exact p11x9862
  · rw [show rightB bp11x9861 1=bp11x10457 by funext i; fin_cases i <;> rfl]; exact p11x10457
set_option maxRecDepth 100000 in
private theorem p11x9015 : Deny 1000000000000000000 11 bp11x9015 := by
  apply split bp11x9015 2
  · rw [show leftB bp11x9015 2=bp11x9016 by funext i; fin_cases i <;> rfl]; exact p11x9016
  · rw [show rightB bp11x9015 2=bp11x9861 by funext i; fin_cases i <;> rfl]; exact p11x9861
set_option maxRecDepth 100000 in
private theorem p11x8743 : Deny 1000000000000000000 11 bp11x8743 := by
  apply split bp11x8743 1
  · rw [show leftB bp11x8743 1=bp11x8744 by funext i; fin_cases i <;> rfl]; exact p11x8744
  · rw [show rightB bp11x8743 1=bp11x9015 by funext i; fin_cases i <;> rfl]; exact p11x9015
private def bp11x10596 : B := ![⟨16,some 16⟩,⟨382,none⟩,⟨190,none⟩]
private def bp11x10597 : B := ![⟨16,some 16⟩,⟨382,some 765⟩,⟨190,none⟩]
private def bp11x10598 : B := ![⟨16,some 16⟩,⟨382,some 765⟩,⟨190,some 381⟩]
private def bp11x10599 : B := ![⟨16,some 16⟩,⟨382,some 509⟩,⟨190,some 381⟩]
private def bp11x10600 : B := ![⟨16,some 16⟩,⟨382,some 509⟩,⟨190,some 253⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x10600 : Deny 1000000000000000000 11 bp11x10600 :=
  sound (by decide) (by decide) 16 1611531564270512078871772447534377250508454466190422474316353296397651333435210738247784863744094155314 (tail:=0) (by decide +kernel)
private def bp11x10777 : B := ![⟨16,some 16⟩,⟨382,some 509⟩,⟨254,some 381⟩]
private def bp11x10778 : B := ![⟨16,some 16⟩,⟨382,some 436⟩,⟨254,some 381⟩]
private def bp11x10779 : B := ![⟨16,some 16⟩,⟨382,some 436⟩,⟨254,some 304⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x10779 : Deny 1000000000000000000 11 bp11x10779 :=
  sound (by decide) (by decide) 13 22041501620371124959784946488736688046516440981298039534130 (tail:=0) (by decide +kernel)
private def bp11x10882 : B := ![⟨16,some 16⟩,⟨382,some 436⟩,⟨305,some 381⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x10882 : Deny 1000000000000000000 11 bp11x10882 :=
  sound (by decide) (by decide) 14 13489783355320901619164933326073197031553671389642525722306039456985799119480228555609536544203370566613056402307899799388651286584618046004505811921692084504906586713625154163193733934 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x10778 : Deny 1000000000000000000 11 bp11x10778 := by
  apply split bp11x10778 2
  · rw [show leftB bp11x10778 2=bp11x10779 by funext i; fin_cases i <;> rfl]; exact p11x10779
  · rw [show rightB bp11x10778 2=bp11x10882 by funext i; fin_cases i <;> rfl]; exact p11x10882
private def bp11x11197 : B := ![⟨16,some 16⟩,⟨437,some 509⟩,⟨254,some 381⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x11197 : Deny 1000000000000000000 11 bp11x11197 :=
  sound (by decide) (by decide) 15 498332370580761283435516242932999085624362071320650746804410655963613094988785208791452200198018778527102669228178520464601326523 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x10777 : Deny 1000000000000000000 11 bp11x10777 := by
  apply split bp11x10777 1
  · rw [show leftB bp11x10777 1=bp11x10778 by funext i; fin_cases i <;> rfl]; exact p11x10778
  · rw [show rightB bp11x10777 1=bp11x11197 by funext i; fin_cases i <;> rfl]; exact p11x11197
set_option maxRecDepth 100000 in
private theorem p11x10599 : Deny 1000000000000000000 11 bp11x10599 := by
  apply split bp11x10599 2
  · rw [show leftB bp11x10599 2=bp11x10600 by funext i; fin_cases i <;> rfl]; exact p11x10600
  · rw [show rightB bp11x10599 2=bp11x10777 by funext i; fin_cases i <;> rfl]; exact p11x10777
private def bp11x11422 : B := ![⟨16,some 16⟩,⟨510,some 765⟩,⟨190,some 381⟩]
private def bp11x11423 : B := ![⟨16,some 16⟩,⟨510,some 765⟩,⟨190,some 253⟩]
private def bp11x11424 : B := ![⟨16,some 16⟩,⟨510,some 612⟩,⟨190,some 253⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x11424 : Deny 1000000000000000000 11 bp11x11424 :=
  sound (by decide) (by decide) 14 44847295151671321936848298586414443305762884806114455897903979157576984258992825052179245730943200366633143796747037613229268203967754598839298965652597389472248798533080153525792140220788486411349420176978491 (tail:=0) (by decide +kernel)
private def bp11x11781 : B := ![⟨16,some 16⟩,⟨613,some 765⟩,⟨190,some 253⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x11781 : Deny 1000000000000000000 11 bp11x11781 :=
  sound (by decide) (by decide) 14 11006525548095846919400328051643 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x11423 : Deny 1000000000000000000 11 bp11x11423 := by
  apply split bp11x11423 1
  · rw [show leftB bp11x11423 1=bp11x11424 by funext i; fin_cases i <;> rfl]; exact p11x11424
  · rw [show rightB bp11x11423 1=bp11x11781 by funext i; fin_cases i <;> rfl]; exact p11x11781
private def bp11x11844 : B := ![⟨16,some 16⟩,⟨510,some 765⟩,⟨254,some 381⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x11844 : Deny 1000000000000000000 11 bp11x11844 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x11422 : Deny 1000000000000000000 11 bp11x11422 := by
  apply split bp11x11422 2
  · rw [show leftB bp11x11422 2=bp11x11423 by funext i; fin_cases i <;> rfl]; exact p11x11423
  · rw [show rightB bp11x11422 2=bp11x11844 by funext i; fin_cases i <;> rfl]; exact p11x11844
set_option maxRecDepth 100000 in
private theorem p11x10598 : Deny 1000000000000000000 11 bp11x10598 := by
  apply split bp11x10598 1
  · rw [show leftB bp11x10598 1=bp11x10599 by funext i; fin_cases i <;> rfl]; exact p11x10599
  · rw [show rightB bp11x10598 1=bp11x11422 by funext i; fin_cases i <;> rfl]; exact p11x11422
private def bp11x11845 : B := ![⟨16,some 16⟩,⟨382,some 765⟩,⟨382,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x11845 : Deny 1000000000000000000 11 bp11x11845 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x10597 : Deny 1000000000000000000 11 bp11x10597 := by
  apply split bp11x10597 2
  · rw [show leftB bp11x10597 2=bp11x10598 by funext i; fin_cases i <;> rfl]; exact p11x10598
  · rw [show rightB bp11x10597 2=bp11x11845 by funext i; fin_cases i <;> rfl]; exact p11x11845
private def bp11x11846 : B := ![⟨16,some 16⟩,⟨766,none⟩,⟨190,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x11846 : Deny 1000000000000000000 11 bp11x11846 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x10596 : Deny 1000000000000000000 11 bp11x10596 := by
  apply split bp11x10596 1
  · rw [show leftB bp11x10596 1=bp11x10597 by funext i; fin_cases i <;> rfl]; exact p11x10597
  · rw [show rightB bp11x10596 1=bp11x11846 by funext i; fin_cases i <;> rfl]; exact p11x11846
set_option maxRecDepth 100000 in
private theorem p11x8742 : Deny 1000000000000000000 11 bp11x8742 := by
  apply split bp11x8742 2
  · rw [show leftB bp11x8742 2=bp11x8743 by funext i; fin_cases i <;> rfl]; exact p11x8743
  · rw [show rightB bp11x8742 2=bp11x10596 by funext i; fin_cases i <;> rfl]; exact p11x10596
set_option maxRecDepth 100000 in
private theorem p11x6832 : Deny 1000000000000000000 11 bp11x6832 := by
  apply split bp11x6832 1
  · rw [show leftB bp11x6832 1=bp11x6833 by funext i; fin_cases i <;> rfl]; exact p11x6833
  · rw [show rightB bp11x6832 1=bp11x8742 by funext i; fin_cases i <;> rfl]; exact p11x8742
set_option maxRecDepth 100000 in
private theorem p11x6830 : Deny 1000000000000000000 11 bp11x6830 := by
  apply split bp11x6830 0
  · rw [show leftB bp11x6830 0=bp11x6831 by funext i; fin_cases i <;> rfl]; exact p11x6831
  · rw [show rightB bp11x6830 0=bp11x6832 by funext i; fin_cases i <;> rfl]; exact p11x6832
set_option maxRecDepth 100000 in
private theorem p11x6828 : Deny 1000000000000000000 11 bp11x6828 := by
  apply split bp11x6828 2
  · rw [show leftB bp11x6828 2=bp11x6829 by funext i; fin_cases i <;> rfl]; exact p11x6829
  · rw [show rightB bp11x6828 2=bp11x6830 by funext i; fin_cases i <;> rfl]; exact p11x6830
set_option maxRecDepth 100000 in
private theorem p11x6826 : Deny 1000000000000000000 11 bp11x6826 := by
  apply split bp11x6826 1
  · rw [show leftB bp11x6826 1=bp11x6827 by funext i; fin_cases i <;> rfl]; exact p11x6827
  · rw [show rightB bp11x6826 1=bp11x6828 by funext i; fin_cases i <;> rfl]; exact p11x6828
set_option maxRecDepth 100000 in
private theorem p11x6824 : Deny 1000000000000000000 11 bp11x6824 := by
  apply split bp11x6824 0
  · rw [show leftB bp11x6824 0=bp11x6825 by funext i; fin_cases i <;> rfl]; exact p11x6825
  · rw [show rightB bp11x6824 0=bp11x6826 by funext i; fin_cases i <;> rfl]; exact p11x6826
set_option maxRecDepth 100000 in
private theorem p11x6822 : Deny 1000000000000000000 11 bp11x6822 := by
  apply split bp11x6822 2
  · rw [show leftB bp11x6822 2=bp11x6823 by funext i; fin_cases i <;> rfl]; exact p11x6823
  · rw [show rightB bp11x6822 2=bp11x6824 by funext i; fin_cases i <;> rfl]; exact p11x6824
set_option maxRecDepth 100000 in
private theorem p11x6820 : Deny 1000000000000000000 11 bp11x6820 := by
  apply split bp11x6820 1
  · rw [show leftB bp11x6820 1=bp11x6821 by funext i; fin_cases i <;> rfl]; exact p11x6821
  · rw [show rightB bp11x6820 1=bp11x6822 by funext i; fin_cases i <;> rfl]; exact p11x6822
set_option maxRecDepth 100000 in
private theorem p11x6818 : Deny 1000000000000000000 11 bp11x6818 := by
  apply split bp11x6818 2
  · rw [show leftB bp11x6818 2=bp11x6819 by funext i; fin_cases i <;> rfl]; exact p11x6819
  · rw [show rightB bp11x6818 2=bp11x6820 by funext i; fin_cases i <;> rfl]; exact p11x6820
private def bp11x11847 : B := ![⟨17,some 21⟩,⟨46,none⟩,⟨10,none⟩]
private def bp11x11848 : B := ![⟨17,some 21⟩,⟨46,none⟩,⟨10,some 21⟩]
private def bp11x11849 : B := ![⟨17,some 21⟩,⟨46,some 93⟩,⟨10,some 21⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x11849 : Deny 1000000000000000000 11 bp11x11849 :=
  sound (by decide) (by decide) 16 192143748653948571161137 (tail:=0) (by decide +kernel)
private def bp11x11892 : B := ![⟨17,some 21⟩,⟨94,none⟩,⟨10,some 21⟩]
private def bp11x11893 : B := ![⟨17,some 18⟩,⟨94,none⟩,⟨10,some 21⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x11893 : Deny 1000000000000000000 11 bp11x11893 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp11x11894 : B := ![⟨19,some 21⟩,⟨94,none⟩,⟨10,some 21⟩]
private def bp11x11895 : B := ![⟨19,some 21⟩,⟨94,none⟩,⟨10,some 13⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x11895 : Deny 1000000000000000000 11 bp11x11895 :=
  sound (by decide) (by decide) 23 16285948501387527561054842554723984269626923653611463442 (tail:=0) (by decide +kernel)
private def bp11x11998 : B := ![⟨19,some 21⟩,⟨94,none⟩,⟨14,some 21⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x11998 : Deny 1000000000000000000 11 bp11x11998 :=
  sound (by decide) (by decide) 20 2435705140191209700792864991983802356279931648398962093435249602381847541329029434829282231845307381183727922658682012351150993890484638561768628958358007998578435737379174228331537449447789254 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x11894 : Deny 1000000000000000000 11 bp11x11894 := by
  apply split bp11x11894 2
  · rw [show leftB bp11x11894 2=bp11x11895 by funext i; fin_cases i <;> rfl]; exact p11x11895
  · rw [show rightB bp11x11894 2=bp11x11998 by funext i; fin_cases i <;> rfl]; exact p11x11998
set_option maxRecDepth 100000 in
private theorem p11x11892 : Deny 1000000000000000000 11 bp11x11892 := by
  apply split bp11x11892 0
  · rw [show leftB bp11x11892 0=bp11x11893 by funext i; fin_cases i <;> rfl]; exact p11x11893
  · rw [show rightB bp11x11892 0=bp11x11894 by funext i; fin_cases i <;> rfl]; exact p11x11894
set_option maxRecDepth 100000 in
private theorem p11x11848 : Deny 1000000000000000000 11 bp11x11848 := by
  apply split bp11x11848 1
  · rw [show leftB bp11x11848 1=bp11x11849 by funext i; fin_cases i <;> rfl]; exact p11x11849
  · rw [show rightB bp11x11848 1=bp11x11892 by funext i; fin_cases i <;> rfl]; exact p11x11892
private def bp11x12327 : B := ![⟨17,some 21⟩,⟨46,none⟩,⟨22,none⟩]
private def bp11x12328 : B := ![⟨17,some 21⟩,⟨46,some 93⟩,⟨22,none⟩]
private def bp11x12329 : B := ![⟨17,some 18⟩,⟨46,some 93⟩,⟨22,none⟩]
private def bp11x12330 : B := ![⟨17,some 18⟩,⟨46,some 93⟩,⟨22,some 45⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x12330 : Deny 1000000000000000000 11 bp11x12330 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp11x12331 : B := ![⟨17,some 18⟩,⟨46,some 93⟩,⟨46,none⟩]
private def bp11x12332 : B := ![⟨17,some 18⟩,⟨46,some 61⟩,⟨46,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x12332 : Deny 1000000000000000000 11 bp11x12332 :=
  sound (by decide) (by decide) 23 16092072031195706017207955987 (tail:=0) (by decide +kernel)
private def bp11x12389 : B := ![⟨17,some 18⟩,⟨62,some 93⟩,⟨46,none⟩]
private def bp11x12390 : B := ![⟨17,some 18⟩,⟨62,some 93⟩,⟨46,some 93⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x12390 : Deny 1000000000000000000 11 bp11x12390 :=
  sound (by decide) (by decide) 15 298183840007050205790646148058396648602904929323227680400161 (tail:=0) (by decide +kernel)
private def bp11x12495 : B := ![⟨17,some 18⟩,⟨62,some 93⟩,⟨94,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x12495 : Deny 1000000000000000000 11 bp11x12495 :=
  sound (by decide) (by decide) 19 65096459640457876508883949764555537376711283518998165805171988126685663226660943579636813990730808377939796098691702266002696417661041438941420040658187799845523683380074369581462241 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x12389 : Deny 1000000000000000000 11 bp11x12389 := by
  apply split bp11x12389 2
  · rw [show leftB bp11x12389 2=bp11x12390 by funext i; fin_cases i <;> rfl]; exact p11x12390
  · rw [show rightB bp11x12389 2=bp11x12495 by funext i; fin_cases i <;> rfl]; exact p11x12495
set_option maxRecDepth 100000 in
private theorem p11x12331 : Deny 1000000000000000000 11 bp11x12331 := by
  apply split bp11x12331 1
  · rw [show leftB bp11x12331 1=bp11x12332 by funext i; fin_cases i <;> rfl]; exact p11x12332
  · rw [show rightB bp11x12331 1=bp11x12389 by funext i; fin_cases i <;> rfl]; exact p11x12389
set_option maxRecDepth 100000 in
private theorem p11x12329 : Deny 1000000000000000000 11 bp11x12329 := by
  apply split bp11x12329 2
  · rw [show leftB bp11x12329 2=bp11x12330 by funext i; fin_cases i <;> rfl]; exact p11x12330
  · rw [show rightB bp11x12329 2=bp11x12331 by funext i; fin_cases i <;> rfl]; exact p11x12331
private def bp11x12806 : B := ![⟨19,some 21⟩,⟨46,some 93⟩,⟨22,none⟩]
private def bp11x12807 : B := ![⟨19,some 21⟩,⟨46,some 93⟩,⟨22,some 45⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x12807 : Deny 1000000000000000000 11 bp11x12807 :=
  sound (by decide) (by decide) 14 14827037306325040381738276848906815601017719412937812135646641085876882159080722928249282993122860126573162472724488796573161939226903754597334778202018648609857706361715284732628465320597244236391178298299645975270086 (tail:=0) (by decide +kernel)
private def bp11x13176 : B := ![⟨19,some 21⟩,⟨46,some 93⟩,⟨46,none⟩]
private def bp11x13177 : B := ![⟨19,some 21⟩,⟨46,some 61⟩,⟨46,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x13177 : Deny 1000000000000000000 11 bp11x13177 :=
  sound (by decide) (by decide) 19 4361783166189104404000531670091349851716560680667786403193745137020230241108753111571422990893578261803652273111296773366210598186112771955619646830411402564916339131630525229251460280186132561262338861 (tail:=0) (by decide +kernel)
private def bp11x13522 : B := ![⟨19,some 21⟩,⟨62,some 93⟩,⟨46,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x13522 : Deny 1000000000000000000 11 bp11x13522 :=
  sound (by decide) (by decide) 14 1237744616087718340933079201792438646258283698813964013 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x13176 : Deny 1000000000000000000 11 bp11x13176 := by
  apply split bp11x13176 1
  · rw [show leftB bp11x13176 1=bp11x13177 by funext i; fin_cases i <;> rfl]; exact p11x13177
  · rw [show rightB bp11x13176 1=bp11x13522 by funext i; fin_cases i <;> rfl]; exact p11x13522
set_option maxRecDepth 100000 in
private theorem p11x12806 : Deny 1000000000000000000 11 bp11x12806 := by
  apply split bp11x12806 2
  · rw [show leftB bp11x12806 2=bp11x12807 by funext i; fin_cases i <;> rfl]; exact p11x12807
  · rw [show rightB bp11x12806 2=bp11x13176 by funext i; fin_cases i <;> rfl]; exact p11x13176
set_option maxRecDepth 100000 in
private theorem p11x12328 : Deny 1000000000000000000 11 bp11x12328 := by
  apply split bp11x12328 0
  · rw [show leftB bp11x12328 0=bp11x12329 by funext i; fin_cases i <;> rfl]; exact p11x12329
  · rw [show rightB bp11x12328 0=bp11x12806 by funext i; fin_cases i <;> rfl]; exact p11x12806
private def bp11x13623 : B := ![⟨17,some 21⟩,⟨94,none⟩,⟨22,none⟩]
private def bp11x13624 : B := ![⟨17,some 18⟩,⟨94,none⟩,⟨22,none⟩]
private def bp11x13625 : B := ![⟨17,some 18⟩,⟨94,none⟩,⟨22,some 45⟩]
private def bp11x13626 : B := ![⟨17,some 18⟩,⟨94,some 189⟩,⟨22,some 45⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x13626 : Deny 1000000000000000000 11 bp11x13626 :=
  sound (by decide) (by decide) 15 77161538861659329449400483427263422633399862596944977174088815155562197523 (tail:=0) (by decide +kernel)
private def bp11x13757 : B := ![⟨17,some 18⟩,⟨190,none⟩,⟨22,some 45⟩]
private def bp11x13758 : B := ![⟨17,some 18⟩,⟨190,none⟩,⟨22,some 29⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x13758 : Deny 1000000000000000000 11 bp11x13758 :=
  sound (by decide) (by decide) 21 70619153600813326028865477672109662441152116108888017828300425861206707494568322696433158369 (tail:=0) (by decide +kernel)
private def bp11x13921 : B := ![⟨17,some 18⟩,⟨190,none⟩,⟨30,some 45⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x13921 : Deny 1000000000000000000 11 bp11x13921 :=
  sound (by decide) (by decide) 25 50077502111283184393961161760490265069525007774004938439446679123930197137465128111169772636990572472565070065831265985525477325799988449630789807033837873866062111317019375246778292697187698751689 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x13757 : Deny 1000000000000000000 11 bp11x13757 := by
  apply split bp11x13757 2
  · rw [show leftB bp11x13757 2=bp11x13758 by funext i; fin_cases i <;> rfl]; exact p11x13758
  · rw [show rightB bp11x13757 2=bp11x13921 by funext i; fin_cases i <;> rfl]; exact p11x13921
set_option maxRecDepth 100000 in
private theorem p11x13625 : Deny 1000000000000000000 11 bp11x13625 := by
  apply split bp11x13625 1
  · rw [show leftB bp11x13625 1=bp11x13626 by funext i; fin_cases i <;> rfl]; exact p11x13626
  · rw [show rightB bp11x13625 1=bp11x13757 by funext i; fin_cases i <;> rfl]; exact p11x13757
private def bp11x14258 : B := ![⟨17,some 18⟩,⟨94,none⟩,⟨46,none⟩]
private def bp11x14259 : B := ![⟨17,some 18⟩,⟨94,some 189⟩,⟨46,none⟩]
private def bp11x14260 : B := ![⟨17,some 18⟩,⟨94,some 189⟩,⟨46,some 93⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x14260 : Deny 1000000000000000000 11 bp11x14260 :=
  sound (by decide) (by decide) 16 214821653746906358197107031082550862842539459245341299174185621100032823331171945873960417368899856349301472292252575565900448645104995458324814775945768972291072096520393 (tail:=0) (by decide +kernel)
private def bp11x14553 : B := ![⟨17,some 18⟩,⟨94,some 189⟩,⟨94,none⟩]
private def bp11x14554 : B := ![⟨17,some 17⟩,⟨94,some 189⟩,⟨94,none⟩]
private def bp11x14555 : B := ![⟨17,some 17⟩,⟨94,some 125⟩,⟨94,none⟩]
private def bp11x14556 : B := ![⟨17,some 17⟩,⟨94,some 125⟩,⟨94,some 189⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x14556 : Deny 1000000000000000000 11 bp11x14556 :=
  sound (by decide) (by decide) 14 5338246729263791113796379605830036501042 (tail:=0) (by decide +kernel)
private def bp11x14627 : B := ![⟨17,some 17⟩,⟨94,some 125⟩,⟨190,none⟩]
private def bp11x14628 : B := ![⟨17,some 17⟩,⟨94,some 107⟩,⟨190,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x14628 : Deny 1000000000000000000 11 bp11x14628 :=
  sound (by decide) (by decide) 22 870861947858108473091136547700880584778303574004373252355083941121985620850534769687498711776069960348139000387031286123965272566344741277356525531697996180705696637258600363121040738507 (tail:=0) (by decide +kernel)
private def bp11x14945 : B := ![⟨17,some 17⟩,⟨108,some 125⟩,⟨190,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x14945 : Deny 1000000000000000000 11 bp11x14945 :=
  sound (by decide) (by decide) 14 26322796773057889059307554701741978233362368029028501457249443079843813198308887183769128123 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x14627 : Deny 1000000000000000000 11 bp11x14627 := by
  apply split bp11x14627 1
  · rw [show leftB bp11x14627 1=bp11x14628 by funext i; fin_cases i <;> rfl]; exact p11x14628
  · rw [show rightB bp11x14627 1=bp11x14945 by funext i; fin_cases i <;> rfl]; exact p11x14945
set_option maxRecDepth 100000 in
private theorem p11x14555 : Deny 1000000000000000000 11 bp11x14555 := by
  apply split bp11x14555 2
  · rw [show leftB bp11x14555 2=bp11x14556 by funext i; fin_cases i <;> rfl]; exact p11x14556
  · rw [show rightB bp11x14555 2=bp11x14627 by funext i; fin_cases i <;> rfl]; exact p11x14627
private def bp11x15106 : B := ![⟨17,some 17⟩,⟨126,some 189⟩,⟨94,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x15106 : Deny 1000000000000000000 11 bp11x15106 :=
  sound (by decide) (by decide) 15 675511955102016431259833188927714650048706197580766871349890646791638732987854028313488727529061451636423434550214838098614743438978276226856665687880442402264263867 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x14554 : Deny 1000000000000000000 11 bp11x14554 := by
  apply split bp11x14554 1
  · rw [show leftB bp11x14554 1=bp11x14555 by funext i; fin_cases i <;> rfl]; exact p11x14555
  · rw [show rightB bp11x14554 1=bp11x15106 by funext i; fin_cases i <;> rfl]; exact p11x15106
private def bp11x15391 : B := ![⟨18,some 18⟩,⟨94,some 189⟩,⟨94,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x15391 : Deny 1000000000000000000 11 bp11x15391 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x14553 : Deny 1000000000000000000 11 bp11x14553 := by
  apply split bp11x14553 0
  · rw [show leftB bp11x14553 0=bp11x14554 by funext i; fin_cases i <;> rfl]; exact p11x14554
  · rw [show rightB bp11x14553 0=bp11x15391 by funext i; fin_cases i <;> rfl]; exact p11x15391
set_option maxRecDepth 100000 in
private theorem p11x14259 : Deny 1000000000000000000 11 bp11x14259 := by
  apply split bp11x14259 2
  · rw [show leftB bp11x14259 2=bp11x14260 by funext i; fin_cases i <;> rfl]; exact p11x14260
  · rw [show rightB bp11x14259 2=bp11x14553 by funext i; fin_cases i <;> rfl]; exact p11x14553
private def bp11x15392 : B := ![⟨17,some 18⟩,⟨190,none⟩,⟨46,none⟩]
private def bp11x15393 : B := ![⟨17,some 18⟩,⟨190,none⟩,⟨46,some 93⟩]
private def bp11x15394 : B := ![⟨17,some 17⟩,⟨190,none⟩,⟨46,some 93⟩]
private def bp11x15395 : B := ![⟨17,some 17⟩,⟨190,some 381⟩,⟨46,some 93⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x15395 : Deny 1000000000000000000 11 bp11x15395 :=
  sound (by decide) (by decide) 15 3072471538253502169396026739152540815130882288781412152147584458520721593707090763891281973492423244237482020339405761536486544091786862104973212804506583882049084972871452890074250004804155 (tail:=0) (by decide +kernel)
private def bp11x15720 : B := ![⟨17,some 17⟩,⟨382,none⟩,⟨46,some 93⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x15720 : Deny 1000000000000000000 11 bp11x15720 :=
  sound (by decide) (by decide) 16 47556666569172017263223424593291561590270172122043 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x15394 : Deny 1000000000000000000 11 bp11x15394 := by
  apply split bp11x15394 1
  · rw [show leftB bp11x15394 1=bp11x15395 by funext i; fin_cases i <;> rfl]; exact p11x15395
  · rw [show rightB bp11x15394 1=bp11x15720 by funext i; fin_cases i <;> rfl]; exact p11x15720
private def bp11x15813 : B := ![⟨18,some 18⟩,⟨190,none⟩,⟨46,some 93⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x15813 : Deny 1000000000000000000 11 bp11x15813 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x15393 : Deny 1000000000000000000 11 bp11x15393 := by
  apply split bp11x15393 0
  · rw [show leftB bp11x15393 0=bp11x15394 by funext i; fin_cases i <;> rfl]; exact p11x15394
  · rw [show rightB bp11x15393 0=bp11x15813 by funext i; fin_cases i <;> rfl]; exact p11x15813
private def bp11x15814 : B := ![⟨17,some 18⟩,⟨190,none⟩,⟨94,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x15814 : Deny 1000000000000000000 11 bp11x15814 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x15392 : Deny 1000000000000000000 11 bp11x15392 := by
  apply split bp11x15392 2
  · rw [show leftB bp11x15392 2=bp11x15393 by funext i; fin_cases i <;> rfl]; exact p11x15393
  · rw [show rightB bp11x15392 2=bp11x15814 by funext i; fin_cases i <;> rfl]; exact p11x15814
set_option maxRecDepth 100000 in
private theorem p11x14258 : Deny 1000000000000000000 11 bp11x14258 := by
  apply split bp11x14258 1
  · rw [show leftB bp11x14258 1=bp11x14259 by funext i; fin_cases i <;> rfl]; exact p11x14259
  · rw [show rightB bp11x14258 1=bp11x15392 by funext i; fin_cases i <;> rfl]; exact p11x15392
set_option maxRecDepth 100000 in
private theorem p11x13624 : Deny 1000000000000000000 11 bp11x13624 := by
  apply split bp11x13624 2
  · rw [show leftB bp11x13624 2=bp11x13625 by funext i; fin_cases i <;> rfl]; exact p11x13625
  · rw [show rightB bp11x13624 2=bp11x14258 by funext i; fin_cases i <;> rfl]; exact p11x14258
private def bp11x15815 : B := ![⟨19,some 21⟩,⟨94,none⟩,⟨22,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x15815 : Deny 1000000000000000000 11 bp11x15815 :=
  sound (by decide) (by decide) 16 6646011547713812853920183757405458606947925886397925988755036056763841204881116111011677196638729949079025085930311387 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x13623 : Deny 1000000000000000000 11 bp11x13623 := by
  apply split bp11x13623 0
  · rw [show leftB bp11x13623 0=bp11x13624 by funext i; fin_cases i <;> rfl]; exact p11x13624
  · rw [show rightB bp11x13623 0=bp11x15815 by funext i; fin_cases i <;> rfl]; exact p11x15815
set_option maxRecDepth 100000 in
private theorem p11x12327 : Deny 1000000000000000000 11 bp11x12327 := by
  apply split bp11x12327 1
  · rw [show leftB bp11x12327 1=bp11x12328 by funext i; fin_cases i <;> rfl]; exact p11x12328
  · rw [show rightB bp11x12327 1=bp11x13623 by funext i; fin_cases i <;> rfl]; exact p11x13623
set_option maxRecDepth 100000 in
private theorem p11x11847 : Deny 1000000000000000000 11 bp11x11847 := by
  apply split bp11x11847 2
  · rw [show leftB bp11x11847 2=bp11x11848 by funext i; fin_cases i <;> rfl]; exact p11x11848
  · rw [show rightB bp11x11847 2=bp11x12327 by funext i; fin_cases i <;> rfl]; exact p11x12327
set_option maxRecDepth 100000 in
private theorem p11x6817 : Deny 1000000000000000000 11 bp11x6817 := by
  apply split bp11x6817 0
  · rw [show leftB bp11x6817 0=bp11x6818 by funext i; fin_cases i <;> rfl]; exact p11x6818
  · rw [show rightB bp11x6817 0=bp11x11847 by funext i; fin_cases i <;> rfl]; exact p11x11847
set_option maxRecDepth 100000 in
private theorem p11x6227 : Deny 1000000000000000000 11 bp11x6227 := by
  apply split bp11x6227 1
  · rw [show leftB bp11x6227 1=bp11x6228 by funext i; fin_cases i <;> rfl]; exact p11x6228
  · rw [show rightB bp11x6227 1=bp11x6817 by funext i; fin_cases i <;> rfl]; exact p11x6817
set_option maxRecDepth 100000 in
private theorem p11x6225 : Deny 1000000000000000000 11 bp11x6225 := by
  apply split bp11x6225 2
  · rw [show leftB bp11x6225 2=bp11x6226 by funext i; fin_cases i <;> rfl]; exact p11x6226
  · rw [show rightB bp11x6225 2=bp11x6227 by funext i; fin_cases i <;> rfl]; exact p11x6227
set_option maxRecDepth 100000 in
private theorem p11x6223 : Deny 1000000000000000000 11 bp11x6223 := by
  apply split bp11x6223 1
  · rw [show leftB bp11x6223 1=bp11x6224 by funext i; fin_cases i <;> rfl]; exact p11x6224
  · rw [show rightB bp11x6223 1=bp11x6225 by funext i; fin_cases i <;> rfl]; exact p11x6225
set_option maxRecDepth 100000 in
private theorem p11x6221 : Deny 1000000000000000000 11 bp11x6221 := by
  apply split bp11x6221 0
  · rw [show leftB bp11x6221 0=bp11x6222 by funext i; fin_cases i <;> rfl]; exact p11x6222
  · rw [show rightB bp11x6221 0=bp11x6223 by funext i; fin_cases i <;> rfl]; exact p11x6223
private def bp11x16024 : B := ![⟨22,none⟩,⟨10,none⟩,⟨4,none⟩]
private def bp11x16025 : B := ![⟨22,none⟩,⟨10,some 21⟩,⟨4,none⟩]
private def bp11x16026 : B := ![⟨22,some 45⟩,⟨10,some 21⟩,⟨4,none⟩]
private def bp11x16027 : B := ![⟨22,some 45⟩,⟨10,some 21⟩,⟨4,some 9⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x16027 : Deny 1000000000000000000 11 bp11x16027 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp11x16028 : B := ![⟨22,some 45⟩,⟨10,some 21⟩,⟨10,none⟩]
private def bp11x16029 : B := ![⟨22,some 45⟩,⟨10,some 13⟩,⟨10,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x16029 : Deny 1000000000000000000 11 bp11x16029 :=
  sound (by decide) (by decide) 24 131122560291469923865288428230097952315158931260633812736756484691539802948867400820748096995753778171928599610959012145 (tail:=0) (by decide +kernel)
private def bp11x16236 : B := ![⟨22,some 45⟩,⟨14,some 21⟩,⟨10,none⟩]
private def bp11x16237 : B := ![⟨22,some 29⟩,⟨14,some 21⟩,⟨10,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x16237 : Deny 1000000000000000000 11 bp11x16237 :=
  sound (by decide) (by decide) 25 13278492064452636417442442889573814156205742149204953804198109833187501414358043523427727481960759010890845267676838147467915271088954350977183945087438909527657384444763481345667363 (tail:=0) (by decide +kernel)
private def bp11x16544 : B := ![⟨30,some 45⟩,⟨14,some 21⟩,⟨10,none⟩]
private def bp11x16545 : B := ![⟨30,some 45⟩,⟨14,some 21⟩,⟨10,some 21⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x16545 : Deny 1000000000000000000 11 bp11x16545 :=
  sound (by decide) (by decide) 14 386888593604654860629829629134338828489993709926621212121967569542815109807728693719270522872690317828455850869035938076294636289167325314162839513196971206 (tail:=0) (by decide +kernel)
private def bp11x16810 : B := ![⟨30,some 45⟩,⟨14,some 21⟩,⟨22,none⟩]
private def bp11x16811 : B := ![⟨30,some 45⟩,⟨14,some 16⟩,⟨22,none⟩]
private def bp11x16812 : B := ![⟨30,some 36⟩,⟨14,some 16⟩,⟨22,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x16812 : Deny 1000000000000000000 11 bp11x16812 :=
  sound (by decide) (by decide) 20 9906346635507541543164703694659446220551774239683341625013297454850505040359728970338639087432595323613392269641456615904470559684702637934791 (tail:=0) (by decide +kernel)
private def bp11x17057 : B := ![⟨37,some 45⟩,⟨14,some 16⟩,⟨22,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x17057 : Deny 1000000000000000000 11 bp11x17057 :=
  sound (by decide) (by decide) 15 3589208231382838429562921098753555626629798322029591021552427369343435459873850402501558898696853965145802943901920664381822113095532918473638414204178945904474344410295 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x16811 : Deny 1000000000000000000 11 bp11x16811 := by
  apply split bp11x16811 0
  · rw [show leftB bp11x16811 0=bp11x16812 by funext i; fin_cases i <;> rfl]; exact p11x16812
  · rw [show rightB bp11x16811 0=bp11x17057 by funext i; fin_cases i <;> rfl]; exact p11x17057
private def bp11x17346 : B := ![⟨30,some 45⟩,⟨17,some 21⟩,⟨22,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x17346 : Deny 1000000000000000000 11 bp11x17346 :=
  sound (by decide) (by decide) 17 162939110084647090164725031692396209054545613609478700681071482773935592491932919826274656219381573669476706339658081174408872748451930051934477589381657479902316740267295132956009001506839377315190077833573784695709 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x16810 : Deny 1000000000000000000 11 bp11x16810 := by
  apply split bp11x16810 1
  · rw [show leftB bp11x16810 1=bp11x16811 by funext i; fin_cases i <;> rfl]; exact p11x16811
  · rw [show rightB bp11x16810 1=bp11x17346 by funext i; fin_cases i <;> rfl]; exact p11x17346
set_option maxRecDepth 100000 in
private theorem p11x16544 : Deny 1000000000000000000 11 bp11x16544 := by
  apply split bp11x16544 2
  · rw [show leftB bp11x16544 2=bp11x16545 by funext i; fin_cases i <;> rfl]; exact p11x16545
  · rw [show rightB bp11x16544 2=bp11x16810 by funext i; fin_cases i <;> rfl]; exact p11x16810
set_option maxRecDepth 100000 in
private theorem p11x16236 : Deny 1000000000000000000 11 bp11x16236 := by
  apply split bp11x16236 0
  · rw [show leftB bp11x16236 0=bp11x16237 by funext i; fin_cases i <;> rfl]; exact p11x16237
  · rw [show rightB bp11x16236 0=bp11x16544 by funext i; fin_cases i <;> rfl]; exact p11x16544
set_option maxRecDepth 100000 in
private theorem p11x16028 : Deny 1000000000000000000 11 bp11x16028 := by
  apply split bp11x16028 1
  · rw [show leftB bp11x16028 1=bp11x16029 by funext i; fin_cases i <;> rfl]; exact p11x16029
  · rw [show rightB bp11x16028 1=bp11x16236 by funext i; fin_cases i <;> rfl]; exact p11x16236
set_option maxRecDepth 100000 in
private theorem p11x16026 : Deny 1000000000000000000 11 bp11x16026 := by
  apply split bp11x16026 2
  · rw [show leftB bp11x16026 2=bp11x16027 by funext i; fin_cases i <;> rfl]; exact p11x16027
  · rw [show rightB bp11x16026 2=bp11x16028 by funext i; fin_cases i <;> rfl]; exact p11x16028
private def bp11x17713 : B := ![⟨46,none⟩,⟨10,some 21⟩,⟨4,none⟩]
private def bp11x17714 : B := ![⟨46,none⟩,⟨10,some 21⟩,⟨4,some 9⟩]
private def bp11x17715 : B := ![⟨46,none⟩,⟨10,some 13⟩,⟨4,some 9⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x17715 : Deny 1000000000000000000 11 bp11x17715 :=
  sound (by decide) (by decide) 24 56973047716241866319370478064494413930051312899580503892955567552296005733992470731321084765999410430132495522156452503294273617447217 (tail:=0) (by decide +kernel)
private def bp11x17948 : B := ![⟨46,none⟩,⟨14,some 21⟩,⟨4,some 9⟩]
private def bp11x17949 : B := ![⟨46,some 93⟩,⟨14,some 21⟩,⟨4,some 9⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x17949 : Deny 1000000000000000000 11 bp11x17949 :=
  sound (by decide) (by decide) 14 2392168921360678575840125386528447518804090867347626363984673623321492997722960647823349008871100796051 (tail:=0) (by decide +kernel)
private def bp11x18126 : B := ![⟨94,none⟩,⟨14,some 21⟩,⟨4,some 9⟩]
private def bp11x18127 : B := ![⟨94,none⟩,⟨14,some 21⟩,⟨4,some 5⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x18127 : Deny 1000000000000000000 11 bp11x18127 :=
  sound (by decide) (by decide) 18 3291436472887610140361456716572609686705434053593415942708433682 (tail:=0) (by decide +kernel)
private def bp11x18236 : B := ![⟨94,none⟩,⟨14,some 21⟩,⟨6,some 9⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x18236 : Deny 1000000000000000000 11 bp11x18236 :=
  sound (by decide) (by decide) 19 5932775045505795293385939302370103676194941926486507364449733547290061103478954488085868169564223807977856563856233507144417638336094372252721933364636979620132114760822987829925906344479985813622 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x18126 : Deny 1000000000000000000 11 bp11x18126 := by
  apply split bp11x18126 2
  · rw [show leftB bp11x18126 2=bp11x18127 by funext i; fin_cases i <;> rfl]; exact p11x18127
  · rw [show rightB bp11x18126 2=bp11x18236 by funext i; fin_cases i <;> rfl]; exact p11x18236
set_option maxRecDepth 100000 in
private theorem p11x17948 : Deny 1000000000000000000 11 bp11x17948 := by
  apply split bp11x17948 0
  · rw [show leftB bp11x17948 0=bp11x17949 by funext i; fin_cases i <;> rfl]; exact p11x17949
  · rw [show rightB bp11x17948 0=bp11x18126 by funext i; fin_cases i <;> rfl]; exact p11x18126
set_option maxRecDepth 100000 in
private theorem p11x17714 : Deny 1000000000000000000 11 bp11x17714 := by
  apply split bp11x17714 1
  · rw [show leftB bp11x17714 1=bp11x17715 by funext i; fin_cases i <;> rfl]; exact p11x17715
  · rw [show rightB bp11x17714 1=bp11x17948 by funext i; fin_cases i <;> rfl]; exact p11x17948
private def bp11x18573 : B := ![⟨46,none⟩,⟨10,some 21⟩,⟨10,none⟩]
private def bp11x18574 : B := ![⟨46,none⟩,⟨10,some 13⟩,⟨10,none⟩]
private def bp11x18575 : B := ![⟨46,some 93⟩,⟨10,some 13⟩,⟨10,none⟩]
private def bp11x18576 : B := ![⟨46,some 93⟩,⟨10,some 13⟩,⟨10,some 21⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x18576 : Deny 1000000000000000000 11 bp11x18576 :=
  sound (by decide) (by decide) 14 63545850756566713657727165465257945271873421011345596311848204807819276593651228261160748931663049 (tail:=0) (by decide +kernel)
private def bp11x18745 : B := ![⟨46,some 93⟩,⟨10,some 13⟩,⟨22,none⟩]
private def bp11x18746 : B := ![⟨46,some 61⟩,⟨10,some 13⟩,⟨22,none⟩]
private def bp11x18747 : B := ![⟨46,some 61⟩,⟨10,some 11⟩,⟨22,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x18747 : Deny 1000000000000000000 11 bp11x18747 :=
  sound (by decide) (by decide) 23 175031283186009236513357925390618046574120570493665618670488542717241459449391453145674184739044285187225814154448794661948124335474231507 (tail:=0) (by decide +kernel)
private def bp11x18984 : B := ![⟨46,some 61⟩,⟨12,some 13⟩,⟨22,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x18984 : Deny 1000000000000000000 11 bp11x18984 :=
  sound (by decide) (by decide) 15 758746085428798594336042429246388191053994858643821854126648881872566910144276033596887717619716927074399988282878222680114163210940050419773529070074719330386801644087 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x18746 : Deny 1000000000000000000 11 bp11x18746 := by
  apply split bp11x18746 1
  · rw [show leftB bp11x18746 1=bp11x18747 by funext i; fin_cases i <;> rfl]; exact p11x18747
  · rw [show rightB bp11x18746 1=bp11x18984 by funext i; fin_cases i <;> rfl]; exact p11x18984
private def bp11x19273 : B := ![⟨62,some 93⟩,⟨10,some 13⟩,⟨22,none⟩]
private def bp11x19274 : B := ![⟨62,some 93⟩,⟨10,some 11⟩,⟨22,none⟩]
private def bp11x19275 : B := ![⟨62,some 93⟩,⟨10,some 11⟩,⟨22,some 45⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x19275 : Deny 1000000000000000000 11 bp11x19275 :=
  sound (by decide) (by decide) 13 1084705614238886497476977312965380640135279736832062267611296065416305584120897100271586363748236864583948645517 (tail:=0) (by decide +kernel)
private def bp11x19468 : B := ![⟨62,some 93⟩,⟨10,some 11⟩,⟨46,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x19468 : Deny 1000000000000000000 11 bp11x19468 :=
  sound (by decide) (by decide) 23 1205554687701101885249018447790640858817352839696677285920812529799047867490251016996592747607573721004381074893879572584719928267723036630983492428406868376732798382888350260179923790097840750070035661232724527266539275832429 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x19274 : Deny 1000000000000000000 11 bp11x19274 := by
  apply split bp11x19274 2
  · rw [show leftB bp11x19274 2=bp11x19275 by funext i; fin_cases i <;> rfl]; exact p11x19275
  · rw [show rightB bp11x19274 2=bp11x19468 by funext i; fin_cases i <;> rfl]; exact p11x19468
private def bp11x19851 : B := ![⟨62,some 93⟩,⟨12,some 13⟩,⟨22,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x19851 : Deny 1000000000000000000 11 bp11x19851 :=
  sound (by decide) (by decide) 12 3678976185629016268215 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x19273 : Deny 1000000000000000000 11 bp11x19273 := by
  apply split bp11x19273 1
  · rw [show leftB bp11x19273 1=bp11x19274 by funext i; fin_cases i <;> rfl]; exact p11x19274
  · rw [show rightB bp11x19273 1=bp11x19851 by funext i; fin_cases i <;> rfl]; exact p11x19851
set_option maxRecDepth 100000 in
private theorem p11x18745 : Deny 1000000000000000000 11 bp11x18745 := by
  apply split bp11x18745 0
  · rw [show leftB bp11x18745 0=bp11x18746 by funext i; fin_cases i <;> rfl]; exact p11x18746
  · rw [show rightB bp11x18745 0=bp11x19273 by funext i; fin_cases i <;> rfl]; exact p11x19273
set_option maxRecDepth 100000 in
private theorem p11x18575 : Deny 1000000000000000000 11 bp11x18575 := by
  apply split bp11x18575 2
  · rw [show leftB bp11x18575 2=bp11x18576 by funext i; fin_cases i <;> rfl]; exact p11x18576
  · rw [show rightB bp11x18575 2=bp11x18745 by funext i; fin_cases i <;> rfl]; exact p11x18745
private def bp11x19896 : B := ![⟨94,none⟩,⟨10,some 13⟩,⟨10,none⟩]
private def bp11x19897 : B := ![⟨94,none⟩,⟨10,some 13⟩,⟨10,some 21⟩]
private def bp11x19898 : B := ![⟨94,some 189⟩,⟨10,some 13⟩,⟨10,some 21⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x19898 : Deny 1000000000000000000 11 bp11x19898 :=
  sound (by decide) (by decide) 15 65382734254579825974368338510339242724067631288568160498346109834820184418784693349299445707858691270196682429559201064662098641437998177148998591310 (tail:=0) (by decide +kernel)
private def bp11x20155 : B := ![⟨190,none⟩,⟨10,some 13⟩,⟨10,some 21⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x20155 : Deny 1000000000000000000 11 bp11x20155 :=
  sound (by decide) (by decide) 25 5116050507272934461436136461671738648195754580007138317293194122228728934746033791440609770255838787878477932341537278826740034238780448359783671320793843969521915148769759911098212033366542666713363845854 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x19897 : Deny 1000000000000000000 11 bp11x19897 := by
  apply split bp11x19897 0
  · rw [show leftB bp11x19897 0=bp11x19898 by funext i; fin_cases i <;> rfl]; exact p11x19898
  · rw [show rightB bp11x19897 0=bp11x20155 by funext i; fin_cases i <;> rfl]; exact p11x20155
private def bp11x20506 : B := ![⟨94,none⟩,⟨10,some 13⟩,⟨22,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x20506 : Deny 1000000000000000000 11 bp11x20506 :=
  sound (by decide) (by decide) 16 716571672002158526209936733200321670738779879459057095649456192056187171887982260198265 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x19896 : Deny 1000000000000000000 11 bp11x19896 := by
  apply split bp11x19896 2
  · rw [show leftB bp11x19896 2=bp11x19897 by funext i; fin_cases i <;> rfl]; exact p11x19897
  · rw [show rightB bp11x19896 2=bp11x20506 by funext i; fin_cases i <;> rfl]; exact p11x20506
set_option maxRecDepth 100000 in
private theorem p11x18574 : Deny 1000000000000000000 11 bp11x18574 := by
  apply split bp11x18574 0
  · rw [show leftB bp11x18574 0=bp11x18575 by funext i; fin_cases i <;> rfl]; exact p11x18575
  · rw [show rightB bp11x18574 0=bp11x19896 by funext i; fin_cases i <;> rfl]; exact p11x19896
private def bp11x20663 : B := ![⟨46,none⟩,⟨14,some 21⟩,⟨10,none⟩]
private def bp11x20664 : B := ![⟨46,some 93⟩,⟨14,some 21⟩,⟨10,none⟩]
private def bp11x20665 : B := ![⟨46,some 93⟩,⟨14,some 21⟩,⟨10,some 21⟩]
private def bp11x20666 : B := ![⟨46,some 93⟩,⟨14,some 16⟩,⟨10,some 21⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x20666 : Deny 1000000000000000000 11 bp11x20666 :=
  sound (by decide) (by decide) 13 15663497312932069745501703984201705775177842743754912490215664143692648254363497574201236573587510341755321016429725642422890868317388693689796445403131991896605 (tail:=0) (by decide +kernel)
private def bp11x20941 : B := ![⟨46,some 93⟩,⟨17,some 21⟩,⟨10,some 21⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x20941 : Deny 1000000000000000000 11 bp11x20941 :=
  sound (by decide) (by decide) 12 833999470639079827968093407799563146280960493971205081187317552011960380902607721373 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x20665 : Deny 1000000000000000000 11 bp11x20665 := by
  apply split bp11x20665 1
  · rw [show leftB bp11x20665 1=bp11x20666 by funext i; fin_cases i <;> rfl]; exact p11x20666
  · rw [show rightB bp11x20665 1=bp11x20941 by funext i; fin_cases i <;> rfl]; exact p11x20941
private def bp11x21090 : B := ![⟨46,some 93⟩,⟨14,some 21⟩,⟨22,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x21090 : Deny 1000000000000000000 11 bp11x21090 :=
  sound (by decide) (by decide) 13 4208810118881968142998390 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x20664 : Deny 1000000000000000000 11 bp11x20664 := by
  apply split bp11x20664 2
  · rw [show leftB bp11x20664 2=bp11x20665 by funext i; fin_cases i <;> rfl]; exact p11x20665
  · rw [show rightB bp11x20664 2=bp11x21090 by funext i; fin_cases i <;> rfl]; exact p11x21090
private def bp11x21143 : B := ![⟨94,none⟩,⟨14,some 21⟩,⟨10,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x21143 : Deny 1000000000000000000 11 bp11x21143 :=
  sound (by decide) (by decide) 14 289896923 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x20663 : Deny 1000000000000000000 11 bp11x20663 := by
  apply split bp11x20663 0
  · rw [show leftB bp11x20663 0=bp11x20664 by funext i; fin_cases i <;> rfl]; exact p11x20664
  · rw [show rightB bp11x20663 0=bp11x21143 by funext i; fin_cases i <;> rfl]; exact p11x21143
set_option maxRecDepth 100000 in
private theorem p11x18573 : Deny 1000000000000000000 11 bp11x18573 := by
  apply split bp11x18573 1
  · rw [show leftB bp11x18573 1=bp11x18574 by funext i; fin_cases i <;> rfl]; exact p11x18574
  · rw [show rightB bp11x18573 1=bp11x20663 by funext i; fin_cases i <;> rfl]; exact p11x20663
set_option maxRecDepth 100000 in
private theorem p11x17713 : Deny 1000000000000000000 11 bp11x17713 := by
  apply split bp11x17713 2
  · rw [show leftB bp11x17713 2=bp11x17714 by funext i; fin_cases i <;> rfl]; exact p11x17714
  · rw [show rightB bp11x17713 2=bp11x18573 by funext i; fin_cases i <;> rfl]; exact p11x18573
set_option maxRecDepth 100000 in
private theorem p11x16025 : Deny 1000000000000000000 11 bp11x16025 := by
  apply split bp11x16025 0
  · rw [show leftB bp11x16025 0=bp11x16026 by funext i; fin_cases i <;> rfl]; exact p11x16026
  · rw [show rightB bp11x16025 0=bp11x17713 by funext i; fin_cases i <;> rfl]; exact p11x17713
private def bp11x21170 : B := ![⟨22,none⟩,⟨22,none⟩,⟨4,none⟩]
private def bp11x21171 : B := ![⟨22,some 45⟩,⟨22,none⟩,⟨4,none⟩]
private def bp11x21172 : B := ![⟨22,some 45⟩,⟨22,none⟩,⟨4,some 9⟩]
private def bp11x21173 : B := ![⟨22,some 29⟩,⟨22,none⟩,⟨4,some 9⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x21173 : Deny 1000000000000000000 11 bp11x21173 :=
  sound (by decide) (by decide) 24 668604182621606665518908656772377172075483017794979236375248735605758808363059622638715323789683373890491837434833292194358745945498284721771645196318604788589226664818895162172768809560377738027721378704705074 (tail:=0) (by decide +kernel)
private def bp11x21530 : B := ![⟨30,some 45⟩,⟨22,none⟩,⟨4,some 9⟩]
private def bp11x21531 : B := ![⟨30,some 45⟩,⟨22,some 45⟩,⟨4,some 9⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x21531 : Deny 1000000000000000000 11 bp11x21531 :=
  sound (by decide) (by decide) 15 323296111495650701112137783644497298444652782551678650340423638569027445926493710620747659194237298620323598063826394487612687010660519994074434659 (tail:=0) (by decide +kernel)
private def bp11x21782 : B := ![⟨30,some 45⟩,⟨46,none⟩,⟨4,some 9⟩]
private def bp11x21783 : B := ![⟨30,some 45⟩,⟨46,none⟩,⟨4,some 5⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x21783 : Deny 1000000000000000000 11 bp11x21783 :=
  sound (by decide) (by decide) 20 329189315510935032033218535035330079689022203174530542026700038991611603805334113324546407430640449635483838470395807942 (tail:=0) (by decide +kernel)
private def bp11x21990 : B := ![⟨30,some 45⟩,⟨46,none⟩,⟨6,some 9⟩]
private def bp11x21991 : B := ![⟨30,some 45⟩,⟨46,some 93⟩,⟨6,some 9⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x21991 : Deny 1000000000000000000 11 bp11x21991 :=
  sound (by decide) (by decide) 13 489098009344503167595294568990332292422342043148480579351317817315766986081771532330404080024310837464109841548856823012748779894909257589907758812269 (tail:=0) (by decide +kernel)
private def bp11x22248 : B := ![⟨30,some 45⟩,⟨94,none⟩,⟨6,some 9⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x22248 : Deny 1000000000000000000 11 bp11x22248 :=
  sound (by decide) (by decide) 22 313860723054543580667056088896169867299989173690860631211554472874247961812149738524244031784446859763762110948205 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x21990 : Deny 1000000000000000000 11 bp11x21990 := by
  apply split bp11x21990 1
  · rw [show leftB bp11x21990 1=bp11x21991 by funext i; fin_cases i <;> rfl]; exact p11x21991
  · rw [show rightB bp11x21990 1=bp11x22248 by funext i; fin_cases i <;> rfl]; exact p11x22248
set_option maxRecDepth 100000 in
private theorem p11x21782 : Deny 1000000000000000000 11 bp11x21782 := by
  apply split bp11x21782 2
  · rw [show leftB bp11x21782 2=bp11x21783 by funext i; fin_cases i <;> rfl]; exact p11x21783
  · rw [show rightB bp11x21782 2=bp11x21990 by funext i; fin_cases i <;> rfl]; exact p11x21990
set_option maxRecDepth 100000 in
private theorem p11x21530 : Deny 1000000000000000000 11 bp11x21530 := by
  apply split bp11x21530 1
  · rw [show leftB bp11x21530 1=bp11x21531 by funext i; fin_cases i <;> rfl]; exact p11x21531
  · rw [show rightB bp11x21530 1=bp11x21782 by funext i; fin_cases i <;> rfl]; exact p11x21782
set_option maxRecDepth 100000 in
private theorem p11x21172 : Deny 1000000000000000000 11 bp11x21172 := by
  apply split bp11x21172 0
  · rw [show leftB bp11x21172 0=bp11x21173 by funext i; fin_cases i <;> rfl]; exact p11x21173
  · rw [show rightB bp11x21172 0=bp11x21530 by funext i; fin_cases i <;> rfl]; exact p11x21530
private def bp11x22449 : B := ![⟨22,some 45⟩,⟨22,none⟩,⟨10,none⟩]
private def bp11x22450 : B := ![⟨22,some 29⟩,⟨22,none⟩,⟨10,none⟩]
private def bp11x22451 : B := ![⟨22,some 29⟩,⟨22,some 45⟩,⟨10,none⟩]
private def bp11x22452 : B := ![⟨22,some 29⟩,⟨22,some 45⟩,⟨10,some 21⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x22452 : Deny 1000000000000000000 11 bp11x22452 :=
  sound (by decide) (by decide) 14 56916030870436477723228723701139162117843462384313911690971015030604553207337654906204832350010373889977237099254320433403340491184766910389343243176974229846863979096383285327428108853576383372613437638 (tail:=0) (by decide +kernel)
private def bp11x22797 : B := ![⟨22,some 29⟩,⟨22,some 45⟩,⟨22,none⟩]
private def bp11x22798 : B := ![⟨22,some 29⟩,⟨22,some 29⟩,⟨22,none⟩]
private def bp11x22799 : B := ![⟨22,some 25⟩,⟨22,some 29⟩,⟨22,none⟩]
private def bp11x22800 : B := ![⟨22,some 25⟩,⟨22,some 29⟩,⟨22,some 45⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x22800 : Deny 1000000000000000000 11 bp11x22800 :=
  sound (by decide) (by decide) 12 60441696175748792234770 (tail:=0) (by decide +kernel)
private def bp11x22841 : B := ![⟨22,some 25⟩,⟨22,some 29⟩,⟨46,none⟩]
private def bp11x22842 : B := ![⟨22,some 25⟩,⟨22,some 25⟩,⟨46,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x22842 : Deny 1000000000000000000 11 bp11x22842 :=
  sound (by decide) (by decide) 21 37795403027162908218827046198350788336128653137001687069875649903375763315202218650770558648718013226818023118671960428296697794291059853 (tail:=0) (by decide +kernel)
private def bp11x23079 : B := ![⟨22,some 25⟩,⟨26,some 29⟩,⟨46,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x23079 : Deny 1000000000000000000 11 bp11x23079 :=
  sound (by decide) (by decide) 19 122052452889703452102329988277519815560621570541728168088109981084936554384086076061181111167473919894005420605 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x22841 : Deny 1000000000000000000 11 bp11x22841 := by
  apply split bp11x22841 1
  · rw [show leftB bp11x22841 1=bp11x22842 by funext i; fin_cases i <;> rfl]; exact p11x22842
  · rw [show rightB bp11x22841 1=bp11x23079 by funext i; fin_cases i <;> rfl]; exact p11x23079
set_option maxRecDepth 100000 in
private theorem p11x22799 : Deny 1000000000000000000 11 bp11x22799 := by
  apply split bp11x22799 2
  · rw [show leftB bp11x22799 2=bp11x22800 by funext i; fin_cases i <;> rfl]; exact p11x22800
  · rw [show rightB bp11x22799 2=bp11x22841 by funext i; fin_cases i <;> rfl]; exact p11x22841
private def bp11x23270 : B := ![⟨26,some 29⟩,⟨22,some 29⟩,⟨22,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x23270 : Deny 1000000000000000000 11 bp11x23270 :=
  sound (by decide) (by decide) 14 154598599358377716153693983496271719578763150690527058871122287036523470632525624920641942148995229657771651278626631649237623164259981670523 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x22798 : Deny 1000000000000000000 11 bp11x22798 := by
  apply split bp11x22798 0
  · rw [show leftB bp11x22798 0=bp11x22799 by funext i; fin_cases i <;> rfl]; exact p11x22799
  · rw [show rightB bp11x22798 0=bp11x23270 by funext i; fin_cases i <;> rfl]; exact p11x23270
private def bp11x23513 : B := ![⟨22,some 29⟩,⟨30,some 45⟩,⟨22,none⟩]
private def bp11x23514 : B := ![⟨22,some 25⟩,⟨30,some 45⟩,⟨22,none⟩]
private def bp11x23515 : B := ![⟨22,some 25⟩,⟨30,some 45⟩,⟨22,some 45⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x23515 : Deny 1000000000000000000 11 bp11x23515 :=
  sound (by decide) (by decide) 13 199116604896568220329353217503881987739398659568086634941940968013058979118262669258033311705692414447453866762935540758602528431910948309542112851908190827062 (tail:=0) (by decide +kernel)
private def bp11x23786 : B := ![⟨22,some 25⟩,⟨30,some 45⟩,⟨46,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x23786 : Deny 1000000000000000000 11 bp11x23786 :=
  sound (by decide) (by decide) 15 1764458294104303291177415046702888709956269926122439469923463429696584477231030 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x23514 : Deny 1000000000000000000 11 bp11x23514 := by
  apply split bp11x23514 2
  · rw [show leftB bp11x23514 2=bp11x23515 by funext i; fin_cases i <;> rfl]; exact p11x23515
  · rw [show rightB bp11x23514 2=bp11x23786 by funext i; fin_cases i <;> rfl]; exact p11x23786
private def bp11x23927 : B := ![⟨26,some 29⟩,⟨30,some 45⟩,⟨22,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x23927 : Deny 1000000000000000000 11 bp11x23927 :=
  sound (by decide) (by decide) 12 15047253627 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x23513 : Deny 1000000000000000000 11 bp11x23513 := by
  apply split bp11x23513 0
  · rw [show leftB bp11x23513 0=bp11x23514 by funext i; fin_cases i <;> rfl]; exact p11x23514
  · rw [show rightB bp11x23513 0=bp11x23927 by funext i; fin_cases i <;> rfl]; exact p11x23927
set_option maxRecDepth 100000 in
private theorem p11x22797 : Deny 1000000000000000000 11 bp11x22797 := by
  apply split bp11x22797 1
  · rw [show leftB bp11x22797 1=bp11x22798 by funext i; fin_cases i <;> rfl]; exact p11x22798
  · rw [show rightB bp11x22797 1=bp11x23513 by funext i; fin_cases i <;> rfl]; exact p11x23513
set_option maxRecDepth 100000 in
private theorem p11x22451 : Deny 1000000000000000000 11 bp11x22451 := by
  apply split bp11x22451 2
  · rw [show leftB bp11x22451 2=bp11x22452 by funext i; fin_cases i <;> rfl]; exact p11x22452
  · rw [show rightB bp11x22451 2=bp11x22797 by funext i; fin_cases i <;> rfl]; exact p11x22797
private def bp11x23954 : B := ![⟨22,some 29⟩,⟨46,none⟩,⟨10,none⟩]
private def bp11x23955 : B := ![⟨22,some 29⟩,⟨46,none⟩,⟨10,some 21⟩]
private def bp11x23956 : B := ![⟨22,some 29⟩,⟨46,some 93⟩,⟨10,some 21⟩]
private def bp11x23957 : B := ![⟨22,some 25⟩,⟨46,some 93⟩,⟨10,some 21⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x23957 : Deny 1000000000000000000 11 bp11x23957 :=
  sound (by decide) (by decide) 13 487218716883850546201142391619595853187547426092066296266946020900455512618918258666448461627112815922520284099247300357207162847308987958312039344145629173588763 (tail:=0) (by decide +kernel)
private def bp11x24234 : B := ![⟨26,some 29⟩,⟨46,some 93⟩,⟨10,some 21⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x24234 : Deny 1000000000000000000 11 bp11x24234 :=
  sound (by decide) (by decide) 12 15668483537066957830771697811210113028886390633387348432335483 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x23956 : Deny 1000000000000000000 11 bp11x23956 := by
  apply split bp11x23956 0
  · rw [show leftB bp11x23956 0=bp11x23957 by funext i; fin_cases i <;> rfl]; exact p11x23957
  · rw [show rightB bp11x23956 0=bp11x24234 by funext i; fin_cases i <;> rfl]; exact p11x24234
private def bp11x24343 : B := ![⟨22,some 29⟩,⟨94,none⟩,⟨10,some 21⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x24343 : Deny 1000000000000000000 11 bp11x24343 :=
  sound (by decide) (by decide) 19 7569305669495630518105797051740833365066706839951810889630945961116723343280923675440240750973816899453471910353669909204425543472078670701 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x23955 : Deny 1000000000000000000 11 bp11x23955 := by
  apply split bp11x23955 1
  · rw [show leftB bp11x23955 1=bp11x23956 by funext i; fin_cases i <;> rfl]; exact p11x23956
  · rw [show rightB bp11x23955 1=bp11x24343 by funext i; fin_cases i <;> rfl]; exact p11x24343
private def bp11x24586 : B := ![⟨22,some 29⟩,⟨46,none⟩,⟨22,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x24586 : Deny 1000000000000000000 11 bp11x24586 :=
  sound (by decide) (by decide) 15 874273921026153384399830904246 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x23954 : Deny 1000000000000000000 11 bp11x23954 := by
  apply split bp11x23954 2
  · rw [show leftB bp11x23954 2=bp11x23955 by funext i; fin_cases i <;> rfl]; exact p11x23955
  · rw [show rightB bp11x23954 2=bp11x24586 by funext i; fin_cases i <;> rfl]; exact p11x24586
set_option maxRecDepth 100000 in
private theorem p11x22450 : Deny 1000000000000000000 11 bp11x22450 := by
  apply split bp11x22450 1
  · rw [show leftB bp11x22450 1=bp11x22451 by funext i; fin_cases i <;> rfl]; exact p11x22451
  · rw [show rightB bp11x22450 1=bp11x23954 by funext i; fin_cases i <;> rfl]; exact p11x23954
private def bp11x24649 : B := ![⟨30,some 45⟩,⟨22,none⟩,⟨10,none⟩]
private def bp11x24650 : B := ![⟨30,some 45⟩,⟨22,some 45⟩,⟨10,none⟩]
private def bp11x24651 : B := ![⟨30,some 45⟩,⟨22,some 45⟩,⟨10,some 21⟩]
private def bp11x24652 : B := ![⟨30,some 45⟩,⟨22,some 29⟩,⟨10,some 21⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x24652 : Deny 1000000000000000000 11 bp11x24652 :=
  sound (by decide) (by decide) 13 134365270304300027691296166469982774595050474474953694690220652930166541492984107692439570185013652468236548571559243117772681688469837176680565447828854358440818039982283614985448416179523539895312731293 (tail:=0) (by decide +kernel)
private def bp11x24999 : B := ![⟨30,some 45⟩,⟨30,some 45⟩,⟨10,some 21⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x24999 : Deny 1000000000000000000 11 bp11x24999 :=
  sound (by decide) (by decide) 12 4133111782329194895024830733304279723423727337148023600540161974313248290679573357 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x24651 : Deny 1000000000000000000 11 bp11x24651 := by
  apply split bp11x24651 1
  · rw [show leftB bp11x24651 1=bp11x24652 by funext i; fin_cases i <;> rfl]; exact p11x24652
  · rw [show rightB bp11x24651 1=bp11x24999 by funext i; fin_cases i <;> rfl]; exact p11x24999
private def bp11x25144 : B := ![⟨30,some 45⟩,⟨22,some 45⟩,⟨22,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x25144 : Deny 1000000000000000000 11 bp11x25144 :=
  sound (by decide) (by decide) 13 1095124059549302 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x24650 : Deny 1000000000000000000 11 bp11x24650 := by
  apply split bp11x24650 2
  · rw [show leftB bp11x24650 2=bp11x24651 by funext i; fin_cases i <;> rfl]; exact p11x24651
  · rw [show rightB bp11x24650 2=bp11x25144 by funext i; fin_cases i <;> rfl]; exact p11x25144
private def bp11x25181 : B := ![⟨30,some 45⟩,⟨46,none⟩,⟨10,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x25181 : Deny 1000000000000000000 11 bp11x25181 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x24649 : Deny 1000000000000000000 11 bp11x24649 := by
  apply split bp11x24649 1
  · rw [show leftB bp11x24649 1=bp11x24650 by funext i; fin_cases i <;> rfl]; exact p11x24650
  · rw [show rightB bp11x24649 1=bp11x25181 by funext i; fin_cases i <;> rfl]; exact p11x25181
set_option maxRecDepth 100000 in
private theorem p11x22449 : Deny 1000000000000000000 11 bp11x22449 := by
  apply split bp11x22449 0
  · rw [show leftB bp11x22449 0=bp11x22450 by funext i; fin_cases i <;> rfl]; exact p11x22450
  · rw [show rightB bp11x22449 0=bp11x24649 by funext i; fin_cases i <;> rfl]; exact p11x24649
set_option maxRecDepth 100000 in
private theorem p11x21171 : Deny 1000000000000000000 11 bp11x21171 := by
  apply split bp11x21171 2
  · rw [show leftB bp11x21171 2=bp11x21172 by funext i; fin_cases i <;> rfl]; exact p11x21172
  · rw [show rightB bp11x21171 2=bp11x22449 by funext i; fin_cases i <;> rfl]; exact p11x22449
private def bp11x25182 : B := ![⟨46,none⟩,⟨22,none⟩,⟨4,none⟩]
private def bp11x25183 : B := ![⟨46,none⟩,⟨22,none⟩,⟨4,some 9⟩]
private def bp11x25184 : B := ![⟨46,none⟩,⟨22,some 45⟩,⟨4,some 9⟩]
private def bp11x25185 : B := ![⟨46,some 93⟩,⟨22,some 45⟩,⟨4,some 9⟩]
private def bp11x25186 : B := ![⟨46,some 93⟩,⟨22,some 45⟩,⟨4,some 5⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x25186 : Deny 1000000000000000000 11 bp11x25186 :=
  sound (by decide) (by decide) 13 739894909286926253472095405627408178793381535990325287784396911805921894550714221766 (tail:=0) (by decide +kernel)
private def bp11x25333 : B := ![⟨46,some 93⟩,⟨22,some 45⟩,⟨6,some 9⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x25333 : Deny 1000000000000000000 11 bp11x25333 :=
  sound (by decide) (by decide) 13 40178841464968446871585897421961231406423902987426152099710848723282049452239310910195696090338987027211361588259298245636915159930532690675572522645907225222944545612544815900744925154378153489150582 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x25185 : Deny 1000000000000000000 11 bp11x25185 := by
  apply split bp11x25185 2
  · rw [show leftB bp11x25185 2=bp11x25186 by funext i; fin_cases i <;> rfl]; exact p11x25186
  · rw [show rightB bp11x25185 2=bp11x25333 by funext i; fin_cases i <;> rfl]; exact p11x25333
private def bp11x25674 : B := ![⟨94,none⟩,⟨22,some 45⟩,⟨4,some 9⟩]
private def bp11x25675 : B := ![⟨94,none⟩,⟨22,some 45⟩,⟨4,some 5⟩]
private def bp11x25676 : B := ![⟨94,none⟩,⟨22,some 29⟩,⟨4,some 5⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x25676 : Deny 1000000000000000000 11 bp11x25676 :=
  sound (by decide) (by decide) 24 4652757773653738521261178693038865124871439087104774454130763652776551690598996489858413024788271391739702442860688270586932485558217496098966568895530282401829484297095713437486223353599788621 (tail:=0) (by decide +kernel)
private def bp11x26007 : B := ![⟨94,none⟩,⟨30,some 45⟩,⟨4,some 5⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x26007 : Deny 1000000000000000000 11 bp11x26007 :=
  sound (by decide) (by decide) 15 164187434754347864566063356576643182620521368212390910132529946409738328240259510240886189993891295589146953327773 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x25675 : Deny 1000000000000000000 11 bp11x25675 := by
  apply split bp11x25675 1
  · rw [show leftB bp11x25675 1=bp11x25676 by funext i; fin_cases i <;> rfl]; exact p11x25676
  · rw [show rightB bp11x25675 1=bp11x26007 by funext i; fin_cases i <;> rfl]; exact p11x26007
private def bp11x26206 : B := ![⟨94,none⟩,⟨22,some 45⟩,⟨6,some 9⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x26206 : Deny 1000000000000000000 11 bp11x26206 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x25674 : Deny 1000000000000000000 11 bp11x25674 := by
  apply split bp11x25674 2
  · rw [show leftB bp11x25674 2=bp11x25675 by funext i; fin_cases i <;> rfl]; exact p11x25675
  · rw [show rightB bp11x25674 2=bp11x26206 by funext i; fin_cases i <;> rfl]; exact p11x26206
set_option maxRecDepth 100000 in
private theorem p11x25184 : Deny 1000000000000000000 11 bp11x25184 := by
  apply split bp11x25184 0
  · rw [show leftB bp11x25184 0=bp11x25185 by funext i; fin_cases i <;> rfl]; exact p11x25185
  · rw [show rightB bp11x25184 0=bp11x25674 by funext i; fin_cases i <;> rfl]; exact p11x25674
private def bp11x26207 : B := ![⟨46,none⟩,⟨46,none⟩,⟨4,some 9⟩]
private def bp11x26208 : B := ![⟨46,some 93⟩,⟨46,none⟩,⟨4,some 9⟩]
private def bp11x26209 : B := ![⟨46,some 93⟩,⟨46,none⟩,⟨4,some 5⟩]
private def bp11x26210 : B := ![⟨46,some 61⟩,⟨46,none⟩,⟨4,some 5⟩]
private def bp11x26211 : B := ![⟨46,some 61⟩,⟨46,some 93⟩,⟨4,some 5⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x26211 : Deny 1000000000000000000 11 bp11x26211 :=
  sound (by decide) (by decide) 12 1089905787328743792259431548887075721450191457351534401364038243 (tail:=0) (by decide +kernel)
private def bp11x26324 : B := ![⟨46,some 61⟩,⟨94,none⟩,⟨4,some 5⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x26324 : Deny 1000000000000000000 11 bp11x26324 :=
  sound (by decide) (by decide) 23 3000017315707987537834508110803351882240385911198828203518967693011465323686090121200356705104356791743115771100648795860655548472134544906367205335661733940470088133552008235345290634637585829430811 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x26210 : Deny 1000000000000000000 11 bp11x26210 := by
  apply split bp11x26210 1
  · rw [show leftB bp11x26210 1=bp11x26211 by funext i; fin_cases i <;> rfl]; exact p11x26211
  · rw [show rightB bp11x26210 1=bp11x26324 by funext i; fin_cases i <;> rfl]; exact p11x26324
private def bp11x26665 : B := ![⟨62,some 93⟩,⟨46,none⟩,⟨4,some 5⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x26665 : Deny 1000000000000000000 11 bp11x26665 :=
  sound (by decide) (by decide) 14 1648140014784522208781935306401296652802354768534569086484489465358205805011562542993610062961486868340819479638059420538543169919649065605230 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x26209 : Deny 1000000000000000000 11 bp11x26209 := by
  apply split bp11x26209 0
  · rw [show leftB bp11x26209 0=bp11x26210 by funext i; fin_cases i <;> rfl]; exact p11x26210
  · rw [show rightB bp11x26209 0=bp11x26665 by funext i; fin_cases i <;> rfl]; exact p11x26665
private def bp11x26912 : B := ![⟨46,some 93⟩,⟨46,none⟩,⟨6,some 9⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x26912 : Deny 1000000000000000000 11 bp11x26912 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x26208 : Deny 1000000000000000000 11 bp11x26208 := by
  apply split bp11x26208 2
  · rw [show leftB bp11x26208 2=bp11x26209 by funext i; fin_cases i <;> rfl]; exact p11x26209
  · rw [show rightB bp11x26208 2=bp11x26912 by funext i; fin_cases i <;> rfl]; exact p11x26912
private def bp11x26913 : B := ![⟨94,none⟩,⟨46,none⟩,⟨4,some 9⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x26913 : Deny 1000000000000000000 11 bp11x26913 :=
  sound (by decide) (by decide) 14 26842843 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x26207 : Deny 1000000000000000000 11 bp11x26207 := by
  apply split bp11x26207 0
  · rw [show leftB bp11x26207 0=bp11x26208 by funext i; fin_cases i <;> rfl]; exact p11x26208
  · rw [show rightB bp11x26207 0=bp11x26913 by funext i; fin_cases i <;> rfl]; exact p11x26913
set_option maxRecDepth 100000 in
private theorem p11x25183 : Deny 1000000000000000000 11 bp11x25183 := by
  apply split bp11x25183 1
  · rw [show leftB bp11x25183 1=bp11x25184 by funext i; fin_cases i <;> rfl]; exact p11x25184
  · rw [show rightB bp11x25183 1=bp11x26207 by funext i; fin_cases i <;> rfl]; exact p11x26207
private def bp11x26940 : B := ![⟨46,none⟩,⟨22,none⟩,⟨10,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p11x26940 : Deny 1000000000000000000 11 bp11x26940 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p11x25182 : Deny 1000000000000000000 11 bp11x25182 := by
  apply split bp11x25182 2
  · rw [show leftB bp11x25182 2=bp11x25183 by funext i; fin_cases i <;> rfl]; exact p11x25183
  · rw [show rightB bp11x25182 2=bp11x26940 by funext i; fin_cases i <;> rfl]; exact p11x26940
set_option maxRecDepth 100000 in
private theorem p11x21170 : Deny 1000000000000000000 11 bp11x21170 := by
  apply split bp11x21170 0
  · rw [show leftB bp11x21170 0=bp11x21171 by funext i; fin_cases i <;> rfl]; exact p11x21171
  · rw [show rightB bp11x21170 0=bp11x25182 by funext i; fin_cases i <;> rfl]; exact p11x25182
set_option maxRecDepth 100000 in
private theorem p11x16024 : Deny 1000000000000000000 11 bp11x16024 := by
  apply split bp11x16024 1
  · rw [show leftB bp11x16024 1=bp11x16025 by funext i; fin_cases i <;> rfl]; exact p11x16025
  · rw [show rightB bp11x16024 1=bp11x21170 by funext i; fin_cases i <;> rfl]; exact p11x21170
set_option maxRecDepth 100000 in
private theorem p11x6220 : Deny 1000000000000000000 11 bp11x6220 := by
  apply split bp11x6220 0
  · rw [show leftB bp11x6220 0=bp11x6221 by funext i; fin_cases i <;> rfl]; exact p11x6221
  · rw [show rightB bp11x6220 0=bp11x16024 by funext i; fin_cases i <;> rfl]; exact p11x16024
set_option maxRecDepth 100000 in
private theorem p11x3802 : Deny 1000000000000000000 11 bp11x3802 := by
  apply split bp11x3802 2
  · rw [show leftB bp11x3802 2=bp11x3803 by funext i; fin_cases i <;> rfl]; exact p11x3803
  · rw [show rightB bp11x3802 2=bp11x6220 by funext i; fin_cases i <;> rfl]; exact p11x6220
set_option maxRecDepth 100000 in
private theorem p11x6 : Deny 1000000000000000000 11 bp11x6 := by
  apply split bp11x6 1
  · rw [show leftB bp11x6 1=bp11x7 by funext i; fin_cases i <;> rfl]; exact p11x7
  · rw [show rightB bp11x6 1=bp11x3802 by funext i; fin_cases i <;> rfl]; exact p11x3802
set_option maxRecDepth 100000 in
private theorem p11x4 : Deny 1000000000000000000 11 bp11x4 := by
  apply split bp11x4 0
  · rw [show leftB bp11x4 0=bp11x5 by funext i; fin_cases i <;> rfl]; exact p11x5
  · rw [show rightB bp11x4 0=bp11x6 by funext i; fin_cases i <;> rfl]; exact p11x6
set_option maxRecDepth 100000 in
private theorem p11x2 : Deny 1000000000000000000 11 bp11x2 := by
  apply split bp11x2 1
  · rw [show leftB bp11x2 1=bp11x3 by funext i; fin_cases i <;> rfl]; exact p11x3
  · rw [show rightB bp11x2 1=bp11x4 by funext i; fin_cases i <;> rfl]; exact p11x4
set_option maxRecDepth 100000 in
theorem p11x0 : Deny 1000000000000000000 11 start := by
  apply split start 0
  · rw [show leftB start 0=bp11x1 by funext i; fin_cases i <;> rfl]; exact p11x1
  · rw [show rightB start 0=bp11x2 by funext i; fin_cases i <;> rfl]; exact p11x2
end OMA.Large245212

/- Exact large-prime arithmetic certificate from large_last_245212.py. -/
namespace OMA.Large245212
private def bp13x1 : B := ![⟨1,some 3⟩,⟨1,none⟩,⟨1,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x1 : Deny 1000000000000000000 13 bp13x1 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x2 : B := ![⟨4,none⟩,⟨1,none⟩,⟨1,none⟩]
private def bp13x3 : B := ![⟨4,none⟩,⟨1,some 3⟩,⟨1,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x3 : Deny 1000000000000000000 13 bp13x3 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x4 : B := ![⟨4,none⟩,⟨4,none⟩,⟨1,none⟩]
private def bp13x5 : B := ![⟨4,some 9⟩,⟨4,none⟩,⟨1,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x5 : Deny 1000000000000000000 13 bp13x5 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x6 : B := ![⟨10,none⟩,⟨4,none⟩,⟨1,none⟩]
private def bp13x7 : B := ![⟨10,none⟩,⟨4,some 9⟩,⟨1,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x7 : Deny 1000000000000000000 13 bp13x7 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x8 : B := ![⟨10,none⟩,⟨10,none⟩,⟨1,none⟩]
private def bp13x9 : B := ![⟨10,some 21⟩,⟨10,none⟩,⟨1,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x9 : Deny 1000000000000000000 13 bp13x9 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x10 : B := ![⟨22,none⟩,⟨10,none⟩,⟨1,none⟩]
private def bp13x11 : B := ![⟨22,none⟩,⟨10,none⟩,⟨1,some 3⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x11 : Deny 1000000000000000000 13 bp13x11 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x12 : B := ![⟨22,none⟩,⟨10,none⟩,⟨4,none⟩]
private def bp13x13 : B := ![⟨22,none⟩,⟨10,some 21⟩,⟨4,none⟩]
private def bp13x14 : B := ![⟨22,some 45⟩,⟨10,some 21⟩,⟨4,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x14 : Deny 1000000000000000000 13 bp13x14 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x15 : B := ![⟨46,none⟩,⟨10,some 21⟩,⟨4,none⟩]
private def bp13x16 : B := ![⟨46,none⟩,⟨10,some 21⟩,⟨4,some 9⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x16 : Deny 1000000000000000000 13 bp13x16 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x17 : B := ![⟨46,none⟩,⟨10,some 21⟩,⟨10,none⟩]
private def bp13x18 : B := ![⟨46,none⟩,⟨10,some 13⟩,⟨10,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x18 : Deny 1000000000000000000 13 bp13x18 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x19 : B := ![⟨46,none⟩,⟨14,some 21⟩,⟨10,none⟩]
private def bp13x20 : B := ![⟨46,some 93⟩,⟨14,some 21⟩,⟨10,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x20 : Deny 1000000000000000000 13 bp13x20 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x21 : B := ![⟨94,none⟩,⟨14,some 21⟩,⟨10,none⟩]
private def bp13x22 : B := ![⟨94,none⟩,⟨14,some 21⟩,⟨10,some 21⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x22 : Deny 1000000000000000000 13 bp13x22 :=
  sound (by decide) (by decide) 28 8051705300319251935681991981797238693923831930502124306 (tail:=0) (by decide +kernel)
private def bp13x123 : B := ![⟨94,none⟩,⟨14,some 21⟩,⟨22,none⟩]
private def bp13x124 : B := ![⟨94,none⟩,⟨14,some 16⟩,⟨22,none⟩]
private def bp13x125 : B := ![⟨94,some 189⟩,⟨14,some 16⟩,⟨22,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x125 : Deny 1000000000000000000 13 bp13x125 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x126 : B := ![⟨190,none⟩,⟨14,some 16⟩,⟨22,none⟩]
private def bp13x127 : B := ![⟨190,none⟩,⟨14,some 16⟩,⟨22,some 45⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x127 : Deny 1000000000000000000 13 bp13x127 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x128 : B := ![⟨190,none⟩,⟨14,some 16⟩,⟨46,none⟩]
private def bp13x129 : B := ![⟨190,some 381⟩,⟨14,some 16⟩,⟨46,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x129 : Deny 1000000000000000000 13 bp13x129 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x130 : B := ![⟨382,none⟩,⟨14,some 16⟩,⟨46,none⟩]
private def bp13x131 : B := ![⟨382,none⟩,⟨14,some 14⟩,⟨46,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x131 : Deny 1000000000000000000 13 bp13x131 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x132 : B := ![⟨382,none⟩,⟨15,some 16⟩,⟨46,none⟩]
private def bp13x133 : B := ![⟨382,none⟩,⟨15,some 16⟩,⟨46,some 93⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x133 : Deny 1000000000000000000 13 bp13x133 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x134 : B := ![⟨382,none⟩,⟨15,some 16⟩,⟨94,none⟩]
private def bp13x135 : B := ![⟨382,some 765⟩,⟨15,some 16⟩,⟨94,none⟩]
private def bp13x136 : B := ![⟨382,some 765⟩,⟨15,some 15⟩,⟨94,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x136 : Deny 1000000000000000000 13 bp13x136 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x137 : B := ![⟨382,some 765⟩,⟨16,some 16⟩,⟨94,none⟩]
private def bp13x138 : B := ![⟨382,some 765⟩,⟨16,some 16⟩,⟨94,some 189⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x138 : Deny 1000000000000000000 13 bp13x138 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x139 : B := ![⟨382,some 765⟩,⟨16,some 16⟩,⟨190,none⟩]
private def bp13x140 : B := ![⟨382,some 509⟩,⟨16,some 16⟩,⟨190,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x140 : Deny 1000000000000000000 13 bp13x140 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x141 : B := ![⟨510,some 765⟩,⟨16,some 16⟩,⟨190,none⟩]
private def bp13x142 : B := ![⟨510,some 765⟩,⟨16,some 16⟩,⟨190,some 381⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x142 : Deny 1000000000000000000 13 bp13x142 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x143 : B := ![⟨510,some 765⟩,⟨16,some 16⟩,⟨382,none⟩]
private def bp13x144 : B := ![⟨510,some 612⟩,⟨16,some 16⟩,⟨382,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x144 : Deny 1000000000000000000 13 bp13x144 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x145 : B := ![⟨613,some 765⟩,⟨16,some 16⟩,⟨382,none⟩]
private def bp13x146 : B := ![⟨613,some 765⟩,⟨16,some 16⟩,⟨382,some 765⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x146 : Deny 1000000000000000000 13 bp13x146 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x147 : B := ![⟨613,some 765⟩,⟨16,some 16⟩,⟨766,none⟩]
private def bp13x148 : B := ![⟨613,some 680⟩,⟨16,some 16⟩,⟨766,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x148 : Deny 1000000000000000000 13 bp13x148 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x149 : B := ![⟨681,some 765⟩,⟨16,some 16⟩,⟨766,none⟩]
private def bp13x150 : B := ![⟨681,some 765⟩,⟨16,some 16⟩,⟨766,some 1533⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x150 : Deny 1000000000000000000 13 bp13x150 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x151 : B := ![⟨681,some 765⟩,⟨16,some 16⟩,⟨1534,none⟩]
private def bp13x152 : B := ![⟨681,some 720⟩,⟨16,some 16⟩,⟨1534,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x152 : Deny 1000000000000000000 13 bp13x152 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x153 : B := ![⟨721,some 765⟩,⟨16,some 16⟩,⟨1534,none⟩]
private def bp13x154 : B := ![⟨721,some 765⟩,⟨16,some 16⟩,⟨1534,some 3069⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x154 : Deny 1000000000000000000 13 bp13x154 :=
  sound (by decide) (by decide) 19 2608144093695682830756125906865501495159565570011483926522896409527104308439152133330039454738462236049879916904400008893828985137 (tail:=0) (by decide +kernel)
private def bp13x377 : B := ![⟨721,some 765⟩,⟨16,some 16⟩,⟨3070,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x377 : Deny 1000000000000000000 13 bp13x377 :=
  sound (by decide) (by decide) 34 784467132932729207818720700144839153901645393901400428014802313850976333228766381358853105352528048785444960189271988564006742439319244099576124549309838441118037741755497333228040094442552835559156435314858242163478845519640892292146463639387703136981244571946822342436914667590011707779024798177329710143195265592796227121573926914345214643606222020247878093127417694753059171205446450867323132730614893035394317667097085498177750552397474324595457551772149495068753414840945186592662481361324236250231556312653283788367360396419869506964776397750432254147574719148361710860747860252939051178372252848028190618553725013241247973667840270632170509612234796500436733378215077697368190729462875615692788509 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x153 : Deny 1000000000000000000 13 bp13x153 := by
  apply split bp13x153 2
  · rw [show leftB bp13x153 2=bp13x154 by funext i; fin_cases i <;> rfl]; exact p13x154
  · rw [show rightB bp13x153 2=bp13x377 by funext i; fin_cases i <;> rfl]; exact p13x377
set_option maxRecDepth 100000 in
private theorem p13x151 : Deny 1000000000000000000 13 bp13x151 := by
  apply split bp13x151 0
  · rw [show leftB bp13x151 0=bp13x152 by funext i; fin_cases i <;> rfl]; exact p13x152
  · rw [show rightB bp13x151 0=bp13x153 by funext i; fin_cases i <;> rfl]; exact p13x153
set_option maxRecDepth 100000 in
private theorem p13x149 : Deny 1000000000000000000 13 bp13x149 := by
  apply split bp13x149 2
  · rw [show leftB bp13x149 2=bp13x150 by funext i; fin_cases i <;> rfl]; exact p13x150
  · rw [show rightB bp13x149 2=bp13x151 by funext i; fin_cases i <;> rfl]; exact p13x151
set_option maxRecDepth 100000 in
private theorem p13x147 : Deny 1000000000000000000 13 bp13x147 := by
  apply split bp13x147 0
  · rw [show leftB bp13x147 0=bp13x148 by funext i; fin_cases i <;> rfl]; exact p13x148
  · rw [show rightB bp13x147 0=bp13x149 by funext i; fin_cases i <;> rfl]; exact p13x149
set_option maxRecDepth 100000 in
private theorem p13x145 : Deny 1000000000000000000 13 bp13x145 := by
  apply split bp13x145 2
  · rw [show leftB bp13x145 2=bp13x146 by funext i; fin_cases i <;> rfl]; exact p13x146
  · rw [show rightB bp13x145 2=bp13x147 by funext i; fin_cases i <;> rfl]; exact p13x147
set_option maxRecDepth 100000 in
private theorem p13x143 : Deny 1000000000000000000 13 bp13x143 := by
  apply split bp13x143 0
  · rw [show leftB bp13x143 0=bp13x144 by funext i; fin_cases i <;> rfl]; exact p13x144
  · rw [show rightB bp13x143 0=bp13x145 by funext i; fin_cases i <;> rfl]; exact p13x145
set_option maxRecDepth 100000 in
private theorem p13x141 : Deny 1000000000000000000 13 bp13x141 := by
  apply split bp13x141 2
  · rw [show leftB bp13x141 2=bp13x142 by funext i; fin_cases i <;> rfl]; exact p13x142
  · rw [show rightB bp13x141 2=bp13x143 by funext i; fin_cases i <;> rfl]; exact p13x143
set_option maxRecDepth 100000 in
private theorem p13x139 : Deny 1000000000000000000 13 bp13x139 := by
  apply split bp13x139 0
  · rw [show leftB bp13x139 0=bp13x140 by funext i; fin_cases i <;> rfl]; exact p13x140
  · rw [show rightB bp13x139 0=bp13x141 by funext i; fin_cases i <;> rfl]; exact p13x141
set_option maxRecDepth 100000 in
private theorem p13x137 : Deny 1000000000000000000 13 bp13x137 := by
  apply split bp13x137 2
  · rw [show leftB bp13x137 2=bp13x138 by funext i; fin_cases i <;> rfl]; exact p13x138
  · rw [show rightB bp13x137 2=bp13x139 by funext i; fin_cases i <;> rfl]; exact p13x139
set_option maxRecDepth 100000 in
private theorem p13x135 : Deny 1000000000000000000 13 bp13x135 := by
  apply split bp13x135 1
  · rw [show leftB bp13x135 1=bp13x136 by funext i; fin_cases i <;> rfl]; exact p13x136
  · rw [show rightB bp13x135 1=bp13x137 by funext i; fin_cases i <;> rfl]; exact p13x137
private def bp13x1560 : B := ![⟨766,none⟩,⟨15,some 16⟩,⟨94,none⟩]
private def bp13x1561 : B := ![⟨766,none⟩,⟨15,some 15⟩,⟨94,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x1561 : Deny 1000000000000000000 13 bp13x1561 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x1562 : B := ![⟨766,none⟩,⟨16,some 16⟩,⟨94,none⟩]
private def bp13x1563 : B := ![⟨766,none⟩,⟨16,some 16⟩,⟨94,some 189⟩]
private def bp13x1564 : B := ![⟨766,some 1533⟩,⟨16,some 16⟩,⟨94,some 189⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x1564 : Deny 1000000000000000000 13 bp13x1564 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x1565 : B := ![⟨1534,none⟩,⟨16,some 16⟩,⟨94,some 189⟩]
private def bp13x1566 : B := ![⟨1534,none⟩,⟨16,some 16⟩,⟨94,some 125⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x1566 : Deny 1000000000000000000 13 bp13x1566 :=
  sound (by decide) (by decide) 40 2518816659730251010330222435622409296556139707442617570335710811608340610235321868070255018312122417214534321769456890777246785043131463148718822233815132886481392570073883357244473467345410374454592407950941825940492659682663659149689317656527563462720839888465059423208695332804245794384124447792008545617204883978621596971832436137846737103001368785520383394881788714835045321839849126929091458093622913629455739701411590928248894762444863008926523448775146549553 (tail:=0) (by decide +kernel)
private def bp13x2351 : B := ![⟨1534,none⟩,⟨16,some 16⟩,⟨126,some 189⟩]
private def bp13x2352 : B := ![⟨1534,some 3069⟩,⟨16,some 16⟩,⟨126,some 189⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x2352 : Deny 1000000000000000000 13 bp13x2352 :=
  sound (by decide) (by decide) 20 62959377270600412314843454839368068476635478559888223632406728279657611485282290661273271189530518854132480485184436563178925055273284822366405583545525035849170090283777087004646358713304274465140522955703528669247848989595853641491611325864948093691208731428273862636403698309868423124851363275209349231563760044916362268279163926847210707 (tail:=0) (by decide +kernel)
private def bp13x2929 : B := ![⟨3070,none⟩,⟨16,some 16⟩,⟨126,some 189⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x2929 : Deny 1000000000000000000 13 bp13x2929 :=
  sound (by decide) (by decide) 23 246433832607126842822535519860396578539152028547695811094329894463068133419018777794683556883200892515994132024909493916883755084581775473465433172479717495576625805217660339720193744782376461064227121273644365432747736748189105514463111241132774026270028417679342929575834656611093730220796096017750932830961404728369771924814833445298176079756218280199617600371145611660015783337886085969753753578317053389595418251807074255609275606689910430737106612896417822951895177554588224259847626361353421841193170870488183 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x2351 : Deny 1000000000000000000 13 bp13x2351 := by
  apply split bp13x2351 0
  · rw [show leftB bp13x2351 0=bp13x2352 by funext i; fin_cases i <;> rfl]; exact p13x2352
  · rw [show rightB bp13x2351 0=bp13x2929 by funext i; fin_cases i <;> rfl]; exact p13x2929
set_option maxRecDepth 100000 in
private theorem p13x1565 : Deny 1000000000000000000 13 bp13x1565 := by
  apply split bp13x1565 2
  · rw [show leftB bp13x1565 2=bp13x1566 by funext i; fin_cases i <;> rfl]; exact p13x1566
  · rw [show rightB bp13x1565 2=bp13x2351 by funext i; fin_cases i <;> rfl]; exact p13x2351
set_option maxRecDepth 100000 in
private theorem p13x1563 : Deny 1000000000000000000 13 bp13x1563 := by
  apply split bp13x1563 0
  · rw [show leftB bp13x1563 0=bp13x1564 by funext i; fin_cases i <;> rfl]; exact p13x1564
  · rw [show rightB bp13x1563 0=bp13x1565 by funext i; fin_cases i <;> rfl]; exact p13x1565
private def bp13x3798 : B := ![⟨766,none⟩,⟨16,some 16⟩,⟨190,none⟩]
private def bp13x3799 : B := ![⟨766,some 1533⟩,⟨16,some 16⟩,⟨190,none⟩]
private def bp13x3800 : B := ![⟨766,some 1533⟩,⟨16,some 16⟩,⟨190,some 381⟩]
private def bp13x3801 : B := ![⟨766,some 1021⟩,⟨16,some 16⟩,⟨190,some 381⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x3801 : Deny 1000000000000000000 13 bp13x3801 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x3802 : B := ![⟨1022,some 1533⟩,⟨16,some 16⟩,⟨190,some 381⟩]
private def bp13x3803 : B := ![⟨1022,some 1533⟩,⟨16,some 16⟩,⟨190,some 253⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x3803 : Deny 1000000000000000000 13 bp13x3803 :=
  sound (by decide) (by decide) 18 19760483323179238308478189610933044740124491923097457294721938823567227389367771232703797541112437175586462442431766896241438963364472971982365263923731584012467205485392177 (tail:=0) (by decide +kernel)
private def bp13x4098 : B := ![⟨1022,some 1533⟩,⟨16,some 16⟩,⟨254,some 381⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x4098 : Deny 1000000000000000000 13 bp13x4098 :=
  sound (by decide) (by decide) 18 1179327645857092165442332968878980384325152977888642497551330309932112254974496478393711074554496947410674792885999090132119310862890791563594797230928182939437419530978226514875981134145678700055547660291655415101176176925360367686631202109915124621865967942645328044108340803433661430570964625298241138478022244140330284640536230932799057375100019258390728244971547009542372388441418192875985890385874836192494062635085423740019280762753888316261299540504747176701435308683723901664867276242913323712813676486042784434313988729982690994338743040001800977716441644266372602446859685547442507971106490515650665412547428773284349627884189647609096335470814046482730442514699037 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x3802 : Deny 1000000000000000000 13 bp13x3802 := by
  apply split bp13x3802 2
  · rw [show leftB bp13x3802 2=bp13x3803 by funext i; fin_cases i <;> rfl]; exact p13x3803
  · rw [show rightB bp13x3802 2=bp13x4098 by funext i; fin_cases i <;> rfl]; exact p13x4098
set_option maxRecDepth 100000 in
private theorem p13x3800 : Deny 1000000000000000000 13 bp13x3800 := by
  apply split bp13x3800 0
  · rw [show leftB bp13x3800 0=bp13x3801 by funext i; fin_cases i <;> rfl]; exact p13x3801
  · rw [show rightB bp13x3800 0=bp13x3802 by funext i; fin_cases i <;> rfl]; exact p13x3802
private def bp13x5233 : B := ![⟨766,some 1533⟩,⟨16,some 16⟩,⟨382,none⟩]
private def bp13x5234 : B := ![⟨766,some 1021⟩,⟨16,some 16⟩,⟨382,none⟩]
private def bp13x5235 : B := ![⟨766,some 1021⟩,⟨16,some 16⟩,⟨382,some 765⟩]
private def bp13x5236 : B := ![⟨766,some 875⟩,⟨16,some 16⟩,⟨382,some 765⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x5236 : Deny 1000000000000000000 13 bp13x5236 :=
  sound (by decide) (by decide) 18 8251944747773470078520270422758500814462987292328242284333970776547552516874115558883628758012691 (tail:=0) (by decide +kernel)
private def bp13x5405 : B := ![⟨876,some 1021⟩,⟨16,some 16⟩,⟨382,some 765⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x5405 : Deny 1000000000000000000 13 bp13x5405 :=
  sound (by decide) (by decide) 18 173236139261886212365741132987014932947028271070993716941935009801948466033569845755162516690690561560793222320431810160084387418703661109937525546607567332220860855660857639999873248686452878838218590426094692697842416428839217804220623284543096114420316161812803007069756516822345883943846915196003180778363482788382167743056574751680771659769818603797454040711598976984039558304479121494081149873172620611410205016451191977074834519859787969505032682738973921277711640430510378673808201719712234050173658321494036865618447057847326858946300321356289987136293768515568309417330144629300922594265009105169018998664625879297802576252887619728331912347566020494725208510772546712007 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x5235 : Deny 1000000000000000000 13 bp13x5235 := by
  apply split bp13x5235 0
  · rw [show leftB bp13x5235 0=bp13x5236 by funext i; fin_cases i <;> rfl]; exact p13x5236
  · rw [show rightB bp13x5235 0=bp13x5405 by funext i; fin_cases i <;> rfl]; exact p13x5405
private def bp13x6548 : B := ![⟨766,some 1021⟩,⟨16,some 16⟩,⟨766,none⟩]
private def bp13x6549 : B := ![⟨766,some 875⟩,⟨16,some 16⟩,⟨766,none⟩]
private def bp13x6550 : B := ![⟨766,some 875⟩,⟨16,some 16⟩,⟨766,some 1533⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x6550 : Deny 1000000000000000000 13 bp13x6550 :=
  sound (by decide) (by decide) 19 126923612746091622628507827276539343818160985066154227311193470288532400538641658072254051717812310814226111031441911425642716567584494145319146855441289176203607644007676813016935951059596146304838866328265516578647374124811812323292273028874944391671662456700251853842436534257645823687813440228451475229147565368358591809287672479353657223273875305802524035898567402131900698339923732667050776256738423940137096987231131763174639022055579995759923701623112145471939396240732624171350228961380087394245773621256292430131330109661041805205478374296196436220113656353243263398638167245860009462550448744274577453648988228347535496013 (tail:=0) (by decide +kernel)
private def bp13x7611 : B := ![⟨766,some 875⟩,⟨16,some 16⟩,⟨1534,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x7611 : Deny 1000000000000000000 13 bp13x7611 :=
  sound (by decide) (by decide) 20 5366682521258649142592747057762095165334911574776416204403338968159210084176724573307472659069658327420947541873139133786172924482434012732916332030060265733120129148202336422061181844077792537664090674915944243863440861 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x6549 : Deny 1000000000000000000 13 bp13x6549 := by
  apply split bp13x6549 2
  · rw [show leftB bp13x6549 2=bp13x6550 by funext i; fin_cases i <;> rfl]; exact p13x6550
  · rw [show rightB bp13x6549 2=bp13x7611 by funext i; fin_cases i <;> rfl]; exact p13x7611
private def bp13x7990 : B := ![⟨876,some 1021⟩,⟨16,some 16⟩,⟨766,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x7990 : Deny 1000000000000000000 13 bp13x7990 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x6548 : Deny 1000000000000000000 13 bp13x6548 := by
  apply split bp13x6548 0
  · rw [show leftB bp13x6548 0=bp13x6549 by funext i; fin_cases i <;> rfl]; exact p13x6549
  · rw [show rightB bp13x6548 0=bp13x7990 by funext i; fin_cases i <;> rfl]; exact p13x7990
set_option maxRecDepth 100000 in
private theorem p13x5234 : Deny 1000000000000000000 13 bp13x5234 := by
  apply split bp13x5234 2
  · rw [show leftB bp13x5234 2=bp13x5235 by funext i; fin_cases i <;> rfl]; exact p13x5235
  · rw [show rightB bp13x5234 2=bp13x6548 by funext i; fin_cases i <;> rfl]; exact p13x6548
private def bp13x7991 : B := ![⟨1022,some 1533⟩,⟨16,some 16⟩,⟨382,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x7991 : Deny 1000000000000000000 13 bp13x7991 :=
  sound (by decide) (by decide) 19 307933576767734583934271263819368012335242827247852413982463518738400082034581172644675067331399188727661157179429599016823 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x5233 : Deny 1000000000000000000 13 bp13x5233 := by
  apply split bp13x5233 0
  · rw [show leftB bp13x5233 0=bp13x5234 by funext i; fin_cases i <;> rfl]; exact p13x5234
  · rw [show rightB bp13x5233 0=bp13x7991 by funext i; fin_cases i <;> rfl]; exact p13x7991
set_option maxRecDepth 100000 in
private theorem p13x3799 : Deny 1000000000000000000 13 bp13x3799 := by
  apply split bp13x3799 2
  · rw [show leftB bp13x3799 2=bp13x3800 by funext i; fin_cases i <;> rfl]; exact p13x3800
  · rw [show rightB bp13x3799 2=bp13x5233 by funext i; fin_cases i <;> rfl]; exact p13x5233
private def bp13x8210 : B := ![⟨1534,none⟩,⟨16,some 16⟩,⟨190,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x8210 : Deny 1000000000000000000 13 bp13x8210 :=
  sound (by decide) (by decide) 21 320653548520820906568258280086699046255364112255191911247502136175135736920512245453533698972315500811660442441744847198139870396986735084688549203445113742581839318803902686998773364957957438667025884315171116361281176512170074652370814350650681379193155559945820367166178009511758695646242108550355509695819611578597689236075387369335 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x3798 : Deny 1000000000000000000 13 bp13x3798 := by
  apply split bp13x3798 0
  · rw [show leftB bp13x3798 0=bp13x3799 by funext i; fin_cases i <;> rfl]; exact p13x3799
  · rw [show rightB bp13x3798 0=bp13x8210 by funext i; fin_cases i <;> rfl]; exact p13x8210
set_option maxRecDepth 100000 in
private theorem p13x1562 : Deny 1000000000000000000 13 bp13x1562 := by
  apply split bp13x1562 2
  · rw [show leftB bp13x1562 2=bp13x1563 by funext i; fin_cases i <;> rfl]; exact p13x1563
  · rw [show rightB bp13x1562 2=bp13x3798 by funext i; fin_cases i <;> rfl]; exact p13x3798
set_option maxRecDepth 100000 in
private theorem p13x1560 : Deny 1000000000000000000 13 bp13x1560 := by
  apply split bp13x1560 1
  · rw [show leftB bp13x1560 1=bp13x1561 by funext i; fin_cases i <;> rfl]; exact p13x1561
  · rw [show rightB bp13x1560 1=bp13x1562 by funext i; fin_cases i <;> rfl]; exact p13x1562
set_option maxRecDepth 100000 in
private theorem p13x134 : Deny 1000000000000000000 13 bp13x134 := by
  apply split bp13x134 0
  · rw [show leftB bp13x134 0=bp13x135 by funext i; fin_cases i <;> rfl]; exact p13x135
  · rw [show rightB bp13x134 0=bp13x1560 by funext i; fin_cases i <;> rfl]; exact p13x1560
set_option maxRecDepth 100000 in
private theorem p13x132 : Deny 1000000000000000000 13 bp13x132 := by
  apply split bp13x132 2
  · rw [show leftB bp13x132 2=bp13x133 by funext i; fin_cases i <;> rfl]; exact p13x133
  · rw [show rightB bp13x132 2=bp13x134 by funext i; fin_cases i <;> rfl]; exact p13x134
set_option maxRecDepth 100000 in
private theorem p13x130 : Deny 1000000000000000000 13 bp13x130 := by
  apply split bp13x130 1
  · rw [show leftB bp13x130 1=bp13x131 by funext i; fin_cases i <;> rfl]; exact p13x131
  · rw [show rightB bp13x130 1=bp13x132 by funext i; fin_cases i <;> rfl]; exact p13x132
set_option maxRecDepth 100000 in
private theorem p13x128 : Deny 1000000000000000000 13 bp13x128 := by
  apply split bp13x128 0
  · rw [show leftB bp13x128 0=bp13x129 by funext i; fin_cases i <;> rfl]; exact p13x129
  · rw [show rightB bp13x128 0=bp13x130 by funext i; fin_cases i <;> rfl]; exact p13x130
set_option maxRecDepth 100000 in
private theorem p13x126 : Deny 1000000000000000000 13 bp13x126 := by
  apply split bp13x126 2
  · rw [show leftB bp13x126 2=bp13x127 by funext i; fin_cases i <;> rfl]; exact p13x127
  · rw [show rightB bp13x126 2=bp13x128 by funext i; fin_cases i <;> rfl]; exact p13x128
set_option maxRecDepth 100000 in
private theorem p13x124 : Deny 1000000000000000000 13 bp13x124 := by
  apply split bp13x124 0
  · rw [show leftB bp13x124 0=bp13x125 by funext i; fin_cases i <;> rfl]; exact p13x125
  · rw [show rightB bp13x124 0=bp13x126 by funext i; fin_cases i <;> rfl]; exact p13x126
private def bp13x8783 : B := ![⟨94,none⟩,⟨17,some 21⟩,⟨22,none⟩]
private def bp13x8784 : B := ![⟨94,some 189⟩,⟨17,some 21⟩,⟨22,none⟩]
private def bp13x8785 : B := ![⟨94,some 189⟩,⟨17,some 21⟩,⟨22,some 45⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x8785 : Deny 1000000000000000000 13 bp13x8785 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x8786 : B := ![⟨94,some 189⟩,⟨17,some 21⟩,⟨46,none⟩]
private def bp13x8787 : B := ![⟨94,some 125⟩,⟨17,some 21⟩,⟨46,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x8787 : Deny 1000000000000000000 13 bp13x8787 :=
  sound (by decide) (by decide) 34 162978885008576999027001429310205071374690945333018068545347270196756282902086318291666827902431247523944685239232739784455823666 (tail:=0) (by decide +kernel)
private def bp13x9008 : B := ![⟨126,some 189⟩,⟨17,some 21⟩,⟨46,none⟩]
private def bp13x9009 : B := ![⟨126,some 189⟩,⟨17,some 18⟩,⟨46,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x9009 : Deny 1000000000000000000 13 bp13x9009 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x9010 : B := ![⟨126,some 189⟩,⟨19,some 21⟩,⟨46,none⟩]
private def bp13x9011 : B := ![⟨126,some 189⟩,⟨19,some 21⟩,⟨46,some 93⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x9011 : Deny 1000000000000000000 13 bp13x9011 :=
  sound (by decide) (by decide) 17 5632065904027387722555325973982405847293023779232322265095897188418723508922068599157784649965965954801095802157255675136364631695184901872322337 (tail:=0) (by decide +kernel)
private def bp13x9260 : B := ![⟨126,some 189⟩,⟨19,some 21⟩,⟨94,none⟩]
private def bp13x9261 : B := ![⟨126,some 151⟩,⟨19,some 21⟩,⟨94,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x9261 : Deny 1000000000000000000 13 bp13x9261 :=
  sound (by decide) (by decide) 36 3019033321484620985688330418399103676249440402045331962611171867425933559657551768684486351210985337163524856467917958120085043714601803811310252159584609315118794645406226164702430310182546008997077912040628246090153161239195422164615394451556148809619055472266198687271979988941039356127852470775218464392565403399438114753433636767682744236128518348794326888107602907196275082620269256907411243702405280224197767269178071011239091084816102865638436973218675334353239204559320569515200295538 (tail:=0) (by decide +kernel)
private def bp13x10090 : B := ![⟨152,some 189⟩,⟨19,some 21⟩,⟨94,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x10090 : Deny 1000000000000000000 13 bp13x10090 :=
  sound (by decide) (by decide) 26 10687630826844156937369352452914588765401136171878326817529530290307291865614726314340142221347693492014595765954787162080405674916717469302953382070326353390349040833374605139999515279987229015810267296274055205824960868738974198073241742896457425265791407452480741446500279761095347241092419254365852791192782835436774728017910352391175109645477497677053643360490852265127104329940800300906135498144044352848738319454075784992781772530503069481941621334167327864375519679153918955602670939157573082190 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x9260 : Deny 1000000000000000000 13 bp13x9260 := by
  apply split bp13x9260 0
  · rw [show leftB bp13x9260 0=bp13x9261 by funext i; fin_cases i <;> rfl]; exact p13x9261
  · rw [show rightB bp13x9260 0=bp13x10090 by funext i; fin_cases i <;> rfl]; exact p13x10090
set_option maxRecDepth 100000 in
private theorem p13x9010 : Deny 1000000000000000000 13 bp13x9010 := by
  apply split bp13x9010 2
  · rw [show leftB bp13x9010 2=bp13x9011 by funext i; fin_cases i <;> rfl]; exact p13x9011
  · rw [show rightB bp13x9010 2=bp13x9260 by funext i; fin_cases i <;> rfl]; exact p13x9260
set_option maxRecDepth 100000 in
private theorem p13x9008 : Deny 1000000000000000000 13 bp13x9008 := by
  apply split bp13x9008 1
  · rw [show leftB bp13x9008 1=bp13x9009 by funext i; fin_cases i <;> rfl]; exact p13x9009
  · rw [show rightB bp13x9008 1=bp13x9010 by funext i; fin_cases i <;> rfl]; exact p13x9010
set_option maxRecDepth 100000 in
private theorem p13x8786 : Deny 1000000000000000000 13 bp13x8786 := by
  apply split bp13x8786 0
  · rw [show leftB bp13x8786 0=bp13x8787 by funext i; fin_cases i <;> rfl]; exact p13x8787
  · rw [show rightB bp13x8786 0=bp13x9008 by funext i; fin_cases i <;> rfl]; exact p13x9008
set_option maxRecDepth 100000 in
private theorem p13x8784 : Deny 1000000000000000000 13 bp13x8784 := by
  apply split bp13x8784 2
  · rw [show leftB bp13x8784 2=bp13x8785 by funext i; fin_cases i <;> rfl]; exact p13x8785
  · rw [show rightB bp13x8784 2=bp13x8786 by funext i; fin_cases i <;> rfl]; exact p13x8786
private def bp13x10935 : B := ![⟨190,none⟩,⟨17,some 21⟩,⟨22,none⟩]
private def bp13x10936 : B := ![⟨190,none⟩,⟨17,some 21⟩,⟨22,some 45⟩]
private def bp13x10937 : B := ![⟨190,some 381⟩,⟨17,some 21⟩,⟨22,some 45⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x10937 : Deny 1000000000000000000 13 bp13x10937 :=
  sound (by decide) (by decide) 18 25658295021717306054062161536201549427406453528055997280731398998519183535646155514048319931858103155304386572385099715985395029467722005931347127818442744144415420440171326824064652349815356981037362 (tail:=0) (by decide +kernel)
private def bp13x11278 : B := ![⟨382,none⟩,⟨17,some 21⟩,⟨22,some 45⟩]
private def bp13x11279 : B := ![⟨382,none⟩,⟨17,some 18⟩,⟨22,some 45⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x11279 : Deny 1000000000000000000 13 bp13x11279 :=
  sound (by decide) (by decide) 33 631900495056422319108391857063249069835037017558385462745716211930030545277305981936595539590840301126501377024466200972647197101956116273411430671493900781649468066254426212357409154777359766106195841298445702008234433461280630007025053209886398804448348828617491 (tail:=0) (by decide +kernel)
private def bp13x11728 : B := ![⟨382,none⟩,⟨19,some 21⟩,⟨22,some 45⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x11728 : Deny 1000000000000000000 13 bp13x11728 :=
  sound (by decide) (by decide) 25 20267400619358189003428356933298100240283248146362045866896001870987835776386236467423046395983061563641597258411789331524102700897056326229581006680459687786532901578592592314491756649581377299196605676731220357646792444283266799408065779184229572012101708877499455699549611737758635315161421181551330974581761371185991615217739243922967627708702089841348289390706814164285879545327117953834782990458770846993722354732264457913509410623356976216937185998315508940005485278576038137907869596799352042173423012209113772546987705477709057072877569831 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x11278 : Deny 1000000000000000000 13 bp13x11278 := by
  apply split bp13x11278 1
  · rw [show leftB bp13x11278 1=bp13x11279 by funext i; fin_cases i <;> rfl]; exact p13x11279
  · rw [show rightB bp13x11278 1=bp13x11728 by funext i; fin_cases i <;> rfl]; exact p13x11728
set_option maxRecDepth 100000 in
private theorem p13x10936 : Deny 1000000000000000000 13 bp13x10936 := by
  apply split bp13x10936 0
  · rw [show leftB bp13x10936 0=bp13x10937 by funext i; fin_cases i <;> rfl]; exact p13x10937
  · rw [show rightB bp13x10936 0=bp13x11278 by funext i; fin_cases i <;> rfl]; exact p13x11278
private def bp13x12651 : B := ![⟨190,none⟩,⟨17,some 21⟩,⟨46,none⟩]
private def bp13x12652 : B := ![⟨190,some 381⟩,⟨17,some 21⟩,⟨46,none⟩]
private def bp13x12653 : B := ![⟨190,some 381⟩,⟨17,some 18⟩,⟨46,none⟩]
private def bp13x12654 : B := ![⟨190,some 381⟩,⟨17,some 18⟩,⟨46,some 93⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x12654 : Deny 1000000000000000000 13 bp13x12654 :=
  sound (by decide) (by decide) 18 6186436363771625797012490930590584847667761 (tail:=0) (by decide +kernel)
private def bp13x12731 : B := ![⟨190,some 381⟩,⟨17,some 18⟩,⟨94,none⟩]
private def bp13x12732 : B := ![⟨190,some 253⟩,⟨17,some 18⟩,⟨94,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x12732 : Deny 1000000000000000000 13 bp13x12732 :=
  sound (by decide) (by decide) 30 6237512528180059634300968379392511239892408923447634284273472883157315608904109883739138209244369435526579502671038154184356610806910101460991423400208739890137443141504337777852841525050142874370224258959192287082677677222657611870469716068135403316640014597193566333177231614724578606050024424045707087053608098064276555726041635726727067536222971223927631482920331589118375348518261042379327683220639534838051 (tail:=0) (by decide +kernel)
private def bp13x13427 : B := ![⟨254,some 381⟩,⟨17,some 18⟩,⟨94,none⟩]
private def bp13x13428 : B := ![⟨254,some 381⟩,⟨17,some 18⟩,⟨94,some 189⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x13428 : Deny 1000000000000000000 13 bp13x13428 :=
  sound (by decide) (by decide) 17 1404932454240217093678584616841162747526901294319056189171935595640704548924647453079365098472938415381722425325057162684912105763956360322171529925238366768868504766474612117683603655697985670030731625822904255830790868926266219321715544747773005408527458090282946176790194495301803854660468842828245455807322338514 (tail:=0) (by decide +kernel)
private def bp13x13963 : B := ![⟨254,some 381⟩,⟨17,some 18⟩,⟨190,none⟩]
private def bp13x13964 : B := ![⟨254,some 381⟩,⟨17,some 17⟩,⟨190,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x13964 : Deny 1000000000000000000 13 bp13x13964 :=
  sound (by decide) (by decide) 33 752908217972264504343698349546332824229252166723690833224083128844018802725615025684760160405023274694670858782434868044404298217916412481080895075949116743811194879347145517361375502954142391688414114791915581027072063534485928273061307002873319639652267044117756746617100713259303098272146022369792814238136927462494016316590954224899862091673905542363647796075215173037498800343507986629582473478245885167050313806697682423558563580220770386163530009624688237219764967219431864620980845232223749361294250150871753818651895093331658177049595200736352342672906847935805638462292296137954067374089596695645902606872723036734080744031494921279901780034322911867642514787633 (tail:=0) (by decide +kernel)
private def bp13x15093 : B := ![⟨254,some 381⟩,⟨18,some 18⟩,⟨190,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x15093 : Deny 1000000000000000000 13 bp13x15093 :=
  sound (by decide) (by decide) 17 2338979931918057436270935771505970464872334252949842707709177563691855072766410417528134037420864413393505297918065753532570503606980061 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x13963 : Deny 1000000000000000000 13 bp13x13963 := by
  apply split bp13x13963 1
  · rw [show leftB bp13x13963 1=bp13x13964 by funext i; fin_cases i <;> rfl]; exact p13x13964
  · rw [show rightB bp13x13963 1=bp13x15093 by funext i; fin_cases i <;> rfl]; exact p13x15093
set_option maxRecDepth 100000 in
private theorem p13x13427 : Deny 1000000000000000000 13 bp13x13427 := by
  apply split bp13x13427 2
  · rw [show leftB bp13x13427 2=bp13x13428 by funext i; fin_cases i <;> rfl]; exact p13x13428
  · rw [show rightB bp13x13427 2=bp13x13963 by funext i; fin_cases i <;> rfl]; exact p13x13963
set_option maxRecDepth 100000 in
private theorem p13x12731 : Deny 1000000000000000000 13 bp13x12731 := by
  apply split bp13x12731 0
  · rw [show leftB bp13x12731 0=bp13x12732 by funext i; fin_cases i <;> rfl]; exact p13x12732
  · rw [show rightB bp13x12731 0=bp13x13427 by funext i; fin_cases i <;> rfl]; exact p13x13427
set_option maxRecDepth 100000 in
private theorem p13x12653 : Deny 1000000000000000000 13 bp13x12653 := by
  apply split bp13x12653 2
  · rw [show leftB bp13x12653 2=bp13x12654 by funext i; fin_cases i <;> rfl]; exact p13x12654
  · rw [show rightB bp13x12653 2=bp13x12731 by funext i; fin_cases i <;> rfl]; exact p13x12731
private def bp13x15330 : B := ![⟨190,some 381⟩,⟨19,some 21⟩,⟨46,none⟩]
private def bp13x15331 : B := ![⟨190,some 381⟩,⟨19,some 21⟩,⟨46,some 93⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x15331 : Deny 1000000000000000000 13 bp13x15331 :=
  sound (by decide) (by decide) 17 290080284359999700262078956022651113853429166833548416922201849045744387362575611336290272533074578956909569377509946255665513942218987209579711312675832515172716787704622445850995244343086028168325018190135061358489254120842320612958178631654766426219252592534751487488511766651767764534552609338796129533769665368518896584543666222106876650374945104783317659015572263005167108460791120748415945765643788714992097115858864659034842704800925136512331279718753338860124878650736408947580001428805482755299363129280581688998328066453817 (tail:=0) (by decide +kernel)
private def bp13x16228 : B := ![⟨190,some 381⟩,⟨19,some 21⟩,⟨94,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x16228 : Deny 1000000000000000000 13 bp13x16228 :=
  sound (by decide) (by decide) 19 28697033394437784774487504276309949643501751916087617870268476051757072668156282404016320470822181365818570477105724268494997958849909124432502519774663168267741519624360602662272315314820066218858305615562298939472723486495985168428670360902441557141490491350114124886287111033 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x15330 : Deny 1000000000000000000 13 bp13x15330 := by
  apply split bp13x15330 2
  · rw [show leftB bp13x15330 2=bp13x15331 by funext i; fin_cases i <;> rfl]; exact p13x15331
  · rw [show rightB bp13x15330 2=bp13x16228 by funext i; fin_cases i <;> rfl]; exact p13x16228
set_option maxRecDepth 100000 in
private theorem p13x12652 : Deny 1000000000000000000 13 bp13x12652 := by
  apply split bp13x12652 1
  · rw [show leftB bp13x12652 1=bp13x12653 by funext i; fin_cases i <;> rfl]; exact p13x12653
  · rw [show rightB bp13x12652 1=bp13x15330 by funext i; fin_cases i <;> rfl]; exact p13x15330
private def bp13x16703 : B := ![⟨382,none⟩,⟨17,some 21⟩,⟨46,none⟩]
private def bp13x16704 : B := ![⟨382,none⟩,⟨17,some 18⟩,⟨46,none⟩]
private def bp13x16705 : B := ![⟨382,none⟩,⟨17,some 18⟩,⟨46,some 93⟩]
private def bp13x16706 : B := ![⟨382,some 765⟩,⟨17,some 18⟩,⟨46,some 93⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x16706 : Deny 1000000000000000000 13 bp13x16706 :=
  sound (by decide) (by decide) 17 3113081014985617117362332314165574720285817599270705111944422968275721956512449293904690056267764233723059890472881116598493382415957686181473732984074055752895700536439126294270643040231030607841987080992146110362387953323794596721370168394637249273134191741175623650300903434689611 (tail:=0) (by decide +kernel)
private def bp13x17187 : B := ![⟨766,none⟩,⟨17,some 18⟩,⟨46,some 93⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x17187 : Deny 1000000000000000000 13 bp13x17187 :=
  sound (by decide) (by decide) 34 15606175805765149955909898531864614475875809036892510777778168561474257575566562253964933832877468517165385592002670847300597494376888003367776936710985449629425384897992250441428401460512945049670152610039377179726328209105833707376117992118605651977238311689348222262061225507909311760670385592425182742591329454319291378349284463881079533852012230549855993530799341708104204867314732880506756973123700417577421657970482364630991427109964259502544485032850769933501653282977701451684449315409554401577932627689027263060207142942243269011800433708220790616491941923185801306704890194636933659084459385394330213614508990895557727067969248139894014759565222150950248509347888197959801530274587 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x16705 : Deny 1000000000000000000 13 bp13x16705 := by
  apply split bp13x16705 0
  · rw [show leftB bp13x16705 0=bp13x16706 by funext i; fin_cases i <;> rfl]; exact p13x16706
  · rw [show rightB bp13x16705 0=bp13x17187 by funext i; fin_cases i <;> rfl]; exact p13x17187
private def bp13x18348 : B := ![⟨382,none⟩,⟨17,some 18⟩,⟨94,none⟩]
private def bp13x18349 : B := ![⟨382,some 765⟩,⟨17,some 18⟩,⟨94,none⟩]
private def bp13x18350 : B := ![⟨382,some 765⟩,⟨17,some 18⟩,⟨94,some 189⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x18350 : Deny 1000000000000000000 13 bp13x18350 :=
  sound (by decide) (by decide) 19 5783331615802237636322873562830526646266891000464180636173740032563138260562696368478791378184248017456623682289575295727159164463126531800898769836682803550782512450716994711096878186409358179710186667102385479744860213595709747789096528199061243535219658305494681543755835219267880745780473526208707147387309064818460615104510669183983931456182400527730480250104308367673829056210886182664917638360703097672499569634175763023806547151270366303525702392148137607590691270369789270790981697220954108214 (tail:=0) (by decide +kernel)
private def bp13x19197 : B := ![⟨382,some 765⟩,⟨17,some 18⟩,⟨190,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x19197 : Deny 1000000000000000000 13 bp13x19197 :=
  sound (by decide) (by decide) 20 69866966819970291909622707341311405312291741151890353096086834147061947704909629358039482374150441289308224165990081574123171350422312036295681633854445441330919331241101257837270940256884995671285353361298121142652538550227037099270151113344612540511730745128173179393208931118709704487122411705488109523463283037207717064575294224234027234314943223514506517999758565838331931978439725467510 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x18349 : Deny 1000000000000000000 13 bp13x18349 := by
  apply split bp13x18349 2
  · rw [show leftB bp13x18349 2=bp13x18350 by funext i; fin_cases i <;> rfl]; exact p13x18350
  · rw [show rightB bp13x18349 2=bp13x19197 by funext i; fin_cases i <;> rfl]; exact p13x19197
private def bp13x19864 : B := ![⟨766,none⟩,⟨17,some 18⟩,⟨94,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x19864 : Deny 1000000000000000000 13 bp13x19864 :=
  sound (by decide) (by decide) 18 78179751341972955 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x18348 : Deny 1000000000000000000 13 bp13x18348 := by
  apply split bp13x18348 0
  · rw [show leftB bp13x18348 0=bp13x18349 by funext i; fin_cases i <;> rfl]; exact p13x18349
  · rw [show rightB bp13x18348 0=bp13x19864 by funext i; fin_cases i <;> rfl]; exact p13x19864
set_option maxRecDepth 100000 in
private theorem p13x16704 : Deny 1000000000000000000 13 bp13x16704 := by
  apply split bp13x16704 2
  · rw [show leftB bp13x16704 2=bp13x16705 by funext i; fin_cases i <;> rfl]; exact p13x16705
  · rw [show rightB bp13x16704 2=bp13x18348 by funext i; fin_cases i <;> rfl]; exact p13x18348
private def bp13x19909 : B := ![⟨382,none⟩,⟨19,some 21⟩,⟨46,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x19909 : Deny 1000000000000000000 13 bp13x19909 :=
  sound (by decide) (by decide) 17 90625630199532121994409285960981991 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x16703 : Deny 1000000000000000000 13 bp13x16703 := by
  apply split bp13x16703 1
  · rw [show leftB bp13x16703 1=bp13x16704 by funext i; fin_cases i <;> rfl]; exact p13x16704
  · rw [show rightB bp13x16703 1=bp13x19909 by funext i; fin_cases i <;> rfl]; exact p13x19909
set_option maxRecDepth 100000 in
private theorem p13x12651 : Deny 1000000000000000000 13 bp13x12651 := by
  apply split bp13x12651 0
  · rw [show leftB bp13x12651 0=bp13x12652 by funext i; fin_cases i <;> rfl]; exact p13x12652
  · rw [show rightB bp13x12651 0=bp13x16703 by funext i; fin_cases i <;> rfl]; exact p13x16703
set_option maxRecDepth 100000 in
private theorem p13x10935 : Deny 1000000000000000000 13 bp13x10935 := by
  apply split bp13x10935 2
  · rw [show leftB bp13x10935 2=bp13x10936 by funext i; fin_cases i <;> rfl]; exact p13x10936
  · rw [show rightB bp13x10935 2=bp13x12651 by funext i; fin_cases i <;> rfl]; exact p13x12651
set_option maxRecDepth 100000 in
private theorem p13x8783 : Deny 1000000000000000000 13 bp13x8783 := by
  apply split bp13x8783 0
  · rw [show leftB bp13x8783 0=bp13x8784 by funext i; fin_cases i <;> rfl]; exact p13x8784
  · rw [show rightB bp13x8783 0=bp13x10935 by funext i; fin_cases i <;> rfl]; exact p13x10935
set_option maxRecDepth 100000 in
private theorem p13x123 : Deny 1000000000000000000 13 bp13x123 := by
  apply split bp13x123 1
  · rw [show leftB bp13x123 1=bp13x124 by funext i; fin_cases i <;> rfl]; exact p13x124
  · rw [show rightB bp13x123 1=bp13x8783 by funext i; fin_cases i <;> rfl]; exact p13x8783
set_option maxRecDepth 100000 in
private theorem p13x21 : Deny 1000000000000000000 13 bp13x21 := by
  apply split bp13x21 2
  · rw [show leftB bp13x21 2=bp13x22 by funext i; fin_cases i <;> rfl]; exact p13x22
  · rw [show rightB bp13x21 2=bp13x123 by funext i; fin_cases i <;> rfl]; exact p13x123
set_option maxRecDepth 100000 in
private theorem p13x19 : Deny 1000000000000000000 13 bp13x19 := by
  apply split bp13x19 0
  · rw [show leftB bp13x19 0=bp13x20 by funext i; fin_cases i <;> rfl]; exact p13x20
  · rw [show rightB bp13x19 0=bp13x21 by funext i; fin_cases i <;> rfl]; exact p13x21
set_option maxRecDepth 100000 in
private theorem p13x17 : Deny 1000000000000000000 13 bp13x17 := by
  apply split bp13x17 1
  · rw [show leftB bp13x17 1=bp13x18 by funext i; fin_cases i <;> rfl]; exact p13x18
  · rw [show rightB bp13x17 1=bp13x19 by funext i; fin_cases i <;> rfl]; exact p13x19
set_option maxRecDepth 100000 in
private theorem p13x15 : Deny 1000000000000000000 13 bp13x15 := by
  apply split bp13x15 2
  · rw [show leftB bp13x15 2=bp13x16 by funext i; fin_cases i <;> rfl]; exact p13x16
  · rw [show rightB bp13x15 2=bp13x17 by funext i; fin_cases i <;> rfl]; exact p13x17
set_option maxRecDepth 100000 in
private theorem p13x13 : Deny 1000000000000000000 13 bp13x13 := by
  apply split bp13x13 0
  · rw [show leftB bp13x13 0=bp13x14 by funext i; fin_cases i <;> rfl]; exact p13x14
  · rw [show rightB bp13x13 0=bp13x15 by funext i; fin_cases i <;> rfl]; exact p13x15
private def bp13x19982 : B := ![⟨22,none⟩,⟨22,none⟩,⟨4,none⟩]
private def bp13x19983 : B := ![⟨22,some 45⟩,⟨22,none⟩,⟨4,none⟩]
private def bp13x19984 : B := ![⟨22,some 45⟩,⟨22,none⟩,⟨4,some 9⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x19984 : Deny 1000000000000000000 13 bp13x19984 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x19985 : B := ![⟨22,some 45⟩,⟨22,none⟩,⟨10,none⟩]
private def bp13x19986 : B := ![⟨22,some 29⟩,⟨22,none⟩,⟨10,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x19986 : Deny 1000000000000000000 13 bp13x19986 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x19987 : B := ![⟨30,some 45⟩,⟨22,none⟩,⟨10,none⟩]
private def bp13x19988 : B := ![⟨30,some 45⟩,⟨22,some 45⟩,⟨10,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x19988 : Deny 1000000000000000000 13 bp13x19988 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x19989 : B := ![⟨30,some 45⟩,⟨46,none⟩,⟨10,none⟩]
private def bp13x19990 : B := ![⟨30,some 45⟩,⟨46,none⟩,⟨10,some 21⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x19990 : Deny 1000000000000000000 13 bp13x19990 :=
  sound (by decide) (by decide) 33 201334967299331949912289575222941705701181306457041814319826827096411660903837622917808402132505951799491761263998530199107751461542548453251243711957224170488457811825033609718118217768595413975220031136530 (tail:=0) (by decide +kernel)
private def bp13x20343 : B := ![⟨30,some 45⟩,⟨46,none⟩,⟨22,none⟩]
private def bp13x20344 : B := ![⟨30,some 45⟩,⟨46,some 93⟩,⟨22,none⟩]
private def bp13x20345 : B := ![⟨30,some 36⟩,⟨46,some 93⟩,⟨22,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x20345 : Deny 1000000000000000000 13 bp13x20345 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x20346 : B := ![⟨37,some 45⟩,⟨46,some 93⟩,⟨22,none⟩]
private def bp13x20347 : B := ![⟨37,some 45⟩,⟨46,some 93⟩,⟨22,some 45⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x20347 : Deny 1000000000000000000 13 bp13x20347 :=
  sound (by decide) (by decide) 17 2564731924869832319762 (tail:=0) (by decide +kernel)
private def bp13x20386 : B := ![⟨37,some 45⟩,⟨46,some 93⟩,⟨46,none⟩]
private def bp13x20387 : B := ![⟨37,some 45⟩,⟨46,some 61⟩,⟨46,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x20387 : Deny 1000000000000000000 13 bp13x20387 :=
  sound (by decide) (by decide) 29 315283884380453029655266605500404409530819763848754574177942294989850713726454644398722253859123654437559026228201504818734976119112088157674914247944776223286561530859787414658597892945467572961296026291845388377842118476767629873 (tail:=0) (by decide +kernel)
private def bp13x20780 : B := ![⟨37,some 45⟩,⟨62,some 93⟩,⟨46,none⟩]
private def bp13x20781 : B := ![⟨37,some 40⟩,⟨62,some 93⟩,⟨46,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x20781 : Deny 1000000000000000000 13 bp13x20781 :=
  sound (by decide) (by decide) 28 11667738943074357778575028794067125901756141355717567533245515540918747094476603824406438352373295139171639215599550190697885407833816544389831210423372946743450821497839752336754734798256557838087322168233735337476671717712794154404967244071718738641030019420492670782598434216014732834762912656777704688385179597207079734027678032734236963 (tail:=0) (by decide +kernel)
private def bp13x21354 : B := ![⟨41,some 45⟩,⟨62,some 93⟩,⟨46,none⟩]
private def bp13x21355 : B := ![⟨41,some 45⟩,⟨62,some 93⟩,⟨46,some 93⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x21355 : Deny 1000000000000000000 13 bp13x21355 :=
  sound (by decide) (by decide) 16 3779071527127930408639433705712653771802637963947718891048930799326743616187244755067139531828588341093203506408010018917352010920460635463882470900223716930377621043039692208265010616262694719061865751466391863873417203017062064566431431478582277466092584370341003058981541449207672508338152219108654564674643256838310396099531191409433656337286089320517802182 (tail:=0) (by decide +kernel)
private def bp13x21962 : B := ![⟨41,some 45⟩,⟨62,some 93⟩,⟨94,none⟩]
private def bp13x21963 : B := ![⟨41,some 45⟩,⟨62,some 74⟩,⟨94,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x21963 : Deny 1000000000000000000 13 bp13x21963 :=
  sound (by decide) (by decide) 35 4931098477789358757808988229491434961390974478540403912763085879157032611442287893714838119250710540830714714680610032752871808293647109101448167401136549283981992868925961242466878649791788812633730628630962916697241852045432478530092630056485366312793354614575214845732901764236884767277664674331796574773975464821311872214609023448818241616104405152619797690651825031004622747557694129531750329249737504286773567614769618169404910425089613877578868185393543663092045804364327285068191956866329770642199141980448364611372895435923021187274504921194797223824811498405491154953005 (tail:=0) (by decide +kernel)
private def bp13x22936 : B := ![⟨41,some 45⟩,⟨75,some 93⟩,⟨94,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x22936 : Deny 1000000000000000000 13 bp13x22936 :=
  sound (by decide) (by decide) 17 353246195796148506951721064236370398930406975313307559948245886321187034829888424199625242737717173451405092330738409289685850823378126864835775775091750782713026064659792534064858759262057189642864799266568487708950479621267894146571124693734125 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x21962 : Deny 1000000000000000000 13 bp13x21962 := by
  apply split bp13x21962 1
  · rw [show leftB bp13x21962 1=bp13x21963 by funext i; fin_cases i <;> rfl]; exact p13x21963
  · rw [show rightB bp13x21962 1=bp13x22936 by funext i; fin_cases i <;> rfl]; exact p13x22936
set_option maxRecDepth 100000 in
private theorem p13x21354 : Deny 1000000000000000000 13 bp13x21354 := by
  apply split bp13x21354 2
  · rw [show leftB bp13x21354 2=bp13x21355 by funext i; fin_cases i <;> rfl]; exact p13x21355
  · rw [show rightB bp13x21354 2=bp13x21962 by funext i; fin_cases i <;> rfl]; exact p13x21962
set_option maxRecDepth 100000 in
private theorem p13x20780 : Deny 1000000000000000000 13 bp13x20780 := by
  apply split bp13x20780 0
  · rw [show leftB bp13x20780 0=bp13x20781 by funext i; fin_cases i <;> rfl]; exact p13x20781
  · rw [show rightB bp13x20780 0=bp13x21354 by funext i; fin_cases i <;> rfl]; exact p13x21354
set_option maxRecDepth 100000 in
private theorem p13x20386 : Deny 1000000000000000000 13 bp13x20386 := by
  apply split bp13x20386 1
  · rw [show leftB bp13x20386 1=bp13x20387 by funext i; fin_cases i <;> rfl]; exact p13x20387
  · rw [show rightB bp13x20386 1=bp13x20780 by funext i; fin_cases i <;> rfl]; exact p13x20780
set_option maxRecDepth 100000 in
private theorem p13x20346 : Deny 1000000000000000000 13 bp13x20346 := by
  apply split bp13x20346 2
  · rw [show leftB bp13x20346 2=bp13x20347 by funext i; fin_cases i <;> rfl]; exact p13x20347
  · rw [show rightB bp13x20346 2=bp13x20386 by funext i; fin_cases i <;> rfl]; exact p13x20386
set_option maxRecDepth 100000 in
private theorem p13x20344 : Deny 1000000000000000000 13 bp13x20344 := by
  apply split bp13x20344 0
  · rw [show leftB bp13x20344 0=bp13x20345 by funext i; fin_cases i <;> rfl]; exact p13x20345
  · rw [show rightB bp13x20344 0=bp13x20346 by funext i; fin_cases i <;> rfl]; exact p13x20346
private def bp13x23355 : B := ![⟨30,some 45⟩,⟨94,none⟩,⟨22,none⟩]
private def bp13x23356 : B := ![⟨30,some 36⟩,⟨94,none⟩,⟨22,none⟩]
private def bp13x23357 : B := ![⟨30,some 36⟩,⟨94,none⟩,⟨22,some 45⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x23357 : Deny 1000000000000000000 13 bp13x23357 :=
  sound (by decide) (by decide) 36 98970756750764530842468931162902957010886719087046267708408614063284037585583738387200718504401599091106199469566941745239453398939542305 (tail:=0) (by decide +kernel)
private def bp13x23594 : B := ![⟨30,some 36⟩,⟨94,none⟩,⟨46,none⟩]
private def bp13x23595 : B := ![⟨30,some 32⟩,⟨94,none⟩,⟨46,none⟩]
private def bp13x23596 : B := ![⟨30,some 32⟩,⟨94,some 189⟩,⟨46,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x23596 : Deny 1000000000000000000 13 bp13x23596 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x23597 : B := ![⟨30,some 32⟩,⟨190,none⟩,⟨46,none⟩]
private def bp13x23598 : B := ![⟨30,some 32⟩,⟨190,none⟩,⟨46,some 93⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x23598 : Deny 1000000000000000000 13 bp13x23598 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x23599 : B := ![⟨30,some 32⟩,⟨190,none⟩,⟨94,none⟩]
private def bp13x23600 : B := ![⟨30,some 32⟩,⟨190,some 381⟩,⟨94,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x23600 : Deny 1000000000000000000 13 bp13x23600 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x23601 : B := ![⟨30,some 32⟩,⟨382,none⟩,⟨94,none⟩]
private def bp13x23602 : B := ![⟨30,some 30⟩,⟨382,none⟩,⟨94,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x23602 : Deny 1000000000000000000 13 bp13x23602 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x23603 : B := ![⟨31,some 32⟩,⟨382,none⟩,⟨94,none⟩]
private def bp13x23604 : B := ![⟨31,some 32⟩,⟨382,none⟩,⟨94,some 189⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x23604 : Deny 1000000000000000000 13 bp13x23604 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x23605 : B := ![⟨31,some 32⟩,⟨382,none⟩,⟨190,none⟩]
private def bp13x23606 : B := ![⟨31,some 32⟩,⟨382,some 765⟩,⟨190,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x23606 : Deny 1000000000000000000 13 bp13x23606 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x23607 : B := ![⟨31,some 32⟩,⟨766,none⟩,⟨190,none⟩]
private def bp13x23608 : B := ![⟨31,some 31⟩,⟨766,none⟩,⟨190,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x23608 : Deny 1000000000000000000 13 bp13x23608 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x23609 : B := ![⟨32,some 32⟩,⟨766,none⟩,⟨190,none⟩]
private def bp13x23610 : B := ![⟨32,some 32⟩,⟨766,none⟩,⟨190,some 381⟩]
private def bp13x23611 : B := ![⟨32,some 32⟩,⟨766,some 1533⟩,⟨190,some 381⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x23611 : Deny 1000000000000000000 13 bp13x23611 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x23612 : B := ![⟨32,some 32⟩,⟨1534,none⟩,⟨190,some 381⟩]
private def bp13x23613 : B := ![⟨32,some 32⟩,⟨1534,none⟩,⟨190,some 253⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x23613 : Deny 1000000000000000000 13 bp13x23613 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x23614 : B := ![⟨32,some 32⟩,⟨1534,none⟩,⟨254,some 381⟩]
private def bp13x23615 : B := ![⟨32,some 32⟩,⟨1534,some 3069⟩,⟨254,some 381⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x23615 : Deny 1000000000000000000 13 bp13x23615 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x23616 : B := ![⟨32,some 32⟩,⟨3070,none⟩,⟨254,some 381⟩]
private def bp13x23617 : B := ![⟨32,some 32⟩,⟨3070,none⟩,⟨254,some 304⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x23617 : Deny 1000000000000000000 13 bp13x23617 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x23618 : B := ![⟨32,some 32⟩,⟨3070,none⟩,⟨305,some 381⟩]
private def bp13x23619 : B := ![⟨32,some 32⟩,⟨3070,some 6141⟩,⟨305,some 381⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x23619 : Deny 1000000000000000000 13 bp13x23619 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x23620 : B := ![⟨32,some 32⟩,⟨6142,none⟩,⟨305,some 381⟩]
private def bp13x23621 : B := ![⟨32,some 32⟩,⟨6142,none⟩,⟨305,some 338⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x23621 : Deny 1000000000000000000 13 bp13x23621 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x23622 : B := ![⟨32,some 32⟩,⟨6142,none⟩,⟨339,some 381⟩]
private def bp13x23623 : B := ![⟨32,some 32⟩,⟨6142,some 12285⟩,⟨339,some 381⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x23623 : Deny 1000000000000000000 13 bp13x23623 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x23624 : B := ![⟨32,some 32⟩,⟨12286,none⟩,⟨339,some 381⟩]
private def bp13x23625 : B := ![⟨32,some 32⟩,⟨12286,none⟩,⟨339,some 358⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x23625 : Deny 1000000000000000000 13 bp13x23625 :=
  sound (by decide) (by decide) 30 400026500291234407656189892934155679241837083356548350045010572529054299114132402774138101343653015895017169447720894797479508987181386856858188470333122601463214149514168615644782241889330509720806898570279660292322696759612121225680204697312563523714966981217843542711896292857115095602 (tail:=0) (by decide +kernel)
private def bp13x24116 : B := ![⟨32,some 32⟩,⟨12286,none⟩,⟨359,some 381⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x24116 : Deny 1000000000000000000 13 bp13x24116 :=
  sound (by decide) (by decide) 23 5153924443968953101300418115171613646906114215940041748097278689399342183019084353878422198336655051681550976050448303117673983922985542748407762101961551112086381308962860939903001909807810974895296490419607378268404797875381709525502952988110057771619307445557263551133969609853633301248824412032812509161788452114537388550475818518290433269593139871058599764220472031415829179518206168800537966474996194999635249015234580717062475326687489918228481910602613097964334 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x23624 : Deny 1000000000000000000 13 bp13x23624 := by
  apply split bp13x23624 2
  · rw [show leftB bp13x23624 2=bp13x23625 by funext i; fin_cases i <;> rfl]; exact p13x23625
  · rw [show rightB bp13x23624 2=bp13x24116 by funext i; fin_cases i <;> rfl]; exact p13x24116
set_option maxRecDepth 100000 in
private theorem p13x23622 : Deny 1000000000000000000 13 bp13x23622 := by
  apply split bp13x23622 1
  · rw [show leftB bp13x23622 1=bp13x23623 by funext i; fin_cases i <;> rfl]; exact p13x23623
  · rw [show rightB bp13x23622 1=bp13x23624 by funext i; fin_cases i <;> rfl]; exact p13x23624
set_option maxRecDepth 100000 in
private theorem p13x23620 : Deny 1000000000000000000 13 bp13x23620 := by
  apply split bp13x23620 2
  · rw [show leftB bp13x23620 2=bp13x23621 by funext i; fin_cases i <;> rfl]; exact p13x23621
  · rw [show rightB bp13x23620 2=bp13x23622 by funext i; fin_cases i <;> rfl]; exact p13x23622
set_option maxRecDepth 100000 in
private theorem p13x23618 : Deny 1000000000000000000 13 bp13x23618 := by
  apply split bp13x23618 1
  · rw [show leftB bp13x23618 1=bp13x23619 by funext i; fin_cases i <;> rfl]; exact p13x23619
  · rw [show rightB bp13x23618 1=bp13x23620 by funext i; fin_cases i <;> rfl]; exact p13x23620
set_option maxRecDepth 100000 in
private theorem p13x23616 : Deny 1000000000000000000 13 bp13x23616 := by
  apply split bp13x23616 2
  · rw [show leftB bp13x23616 2=bp13x23617 by funext i; fin_cases i <;> rfl]; exact p13x23617
  · rw [show rightB bp13x23616 2=bp13x23618 by funext i; fin_cases i <;> rfl]; exact p13x23618
set_option maxRecDepth 100000 in
private theorem p13x23614 : Deny 1000000000000000000 13 bp13x23614 := by
  apply split bp13x23614 1
  · rw [show leftB bp13x23614 1=bp13x23615 by funext i; fin_cases i <;> rfl]; exact p13x23615
  · rw [show rightB bp13x23614 1=bp13x23616 by funext i; fin_cases i <;> rfl]; exact p13x23616
set_option maxRecDepth 100000 in
private theorem p13x23612 : Deny 1000000000000000000 13 bp13x23612 := by
  apply split bp13x23612 2
  · rw [show leftB bp13x23612 2=bp13x23613 by funext i; fin_cases i <;> rfl]; exact p13x23613
  · rw [show rightB bp13x23612 2=bp13x23614 by funext i; fin_cases i <;> rfl]; exact p13x23614
set_option maxRecDepth 100000 in
private theorem p13x23610 : Deny 1000000000000000000 13 bp13x23610 := by
  apply split bp13x23610 1
  · rw [show leftB bp13x23610 1=bp13x23611 by funext i; fin_cases i <;> rfl]; exact p13x23611
  · rw [show rightB bp13x23610 1=bp13x23612 by funext i; fin_cases i <;> rfl]; exact p13x23612
private def bp13x24907 : B := ![⟨32,some 32⟩,⟨766,none⟩,⟨382,none⟩]
private def bp13x24908 : B := ![⟨32,some 32⟩,⟨766,some 1533⟩,⟨382,none⟩]
private def bp13x24909 : B := ![⟨32,some 32⟩,⟨766,some 1533⟩,⟨382,some 765⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x24909 : Deny 1000000000000000000 13 bp13x24909 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x24910 : B := ![⟨32,some 32⟩,⟨766,some 1533⟩,⟨766,none⟩]
private def bp13x24911 : B := ![⟨32,some 32⟩,⟨766,some 1021⟩,⟨766,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x24911 : Deny 1000000000000000000 13 bp13x24911 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x24912 : B := ![⟨32,some 32⟩,⟨1022,some 1533⟩,⟨766,none⟩]
private def bp13x24913 : B := ![⟨32,some 32⟩,⟨1022,some 1533⟩,⟨766,some 1533⟩]
private def bp13x24914 : B := ![⟨32,some 32⟩,⟨1022,some 1226⟩,⟨766,some 1533⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x24914 : Deny 1000000000000000000 13 bp13x24914 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x24915 : B := ![⟨32,some 32⟩,⟨1227,some 1533⟩,⟨766,some 1533⟩]
private def bp13x24916 : B := ![⟨32,some 32⟩,⟨1227,some 1533⟩,⟨766,some 1021⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x24916 : Deny 1000000000000000000 13 bp13x24916 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x24917 : B := ![⟨32,some 32⟩,⟨1227,some 1533⟩,⟨1022,some 1533⟩]
private def bp13x24918 : B := ![⟨32,some 32⟩,⟨1227,some 1363⟩,⟨1022,some 1533⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x24918 : Deny 1000000000000000000 13 bp13x24918 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x24919 : B := ![⟨32,some 32⟩,⟨1364,some 1533⟩,⟨1022,some 1533⟩]
private def bp13x24920 : B := ![⟨32,some 32⟩,⟨1364,some 1533⟩,⟨1022,some 1226⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x24920 : Deny 1000000000000000000 13 bp13x24920 :=
  sound (by decide) (by decide) 17 103377085886138168820299952625442725326549171385339491816242576767645793600573676746822085025271669619971878765823477568913430745859336930283851690025605470475832331093063413113455966348214287263377747022670887797184828580101940852973437226546 (tail:=0) (by decide +kernel)
private def bp13x25331 : B := ![⟨32,some 32⟩,⟨1364,some 1533⟩,⟨1227,some 1533⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x25331 : Deny 1000000000000000000 13 bp13x25331 :=
  sound (by decide) (by decide) 18 414730105162953833315296935076730884905054580670094492291669855080696216500028621195688783496922787235880254820732630254092012794971444015637100183761569333974681218625170524253051115599249660237322938612148409277525388941343178388262638469864165010247370155320155204464624889610124477301553593621607655486189551688871539212932784395230557766919285655203514579122695985608325128715138649997507521520331710336739655676416951465738807823093285049498468222101226859345822796248066138996811768051426918699149223721134411978854385957380430003791092531567829343844695479975616804808472057977235913342395182 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x24919 : Deny 1000000000000000000 13 bp13x24919 := by
  apply split bp13x24919 2
  · rw [show leftB bp13x24919 2=bp13x24920 by funext i; fin_cases i <;> rfl]; exact p13x24920
  · rw [show rightB bp13x24919 2=bp13x25331 by funext i; fin_cases i <;> rfl]; exact p13x25331
set_option maxRecDepth 100000 in
private theorem p13x24917 : Deny 1000000000000000000 13 bp13x24917 := by
  apply split bp13x24917 1
  · rw [show leftB bp13x24917 1=bp13x24918 by funext i; fin_cases i <;> rfl]; exact p13x24918
  · rw [show rightB bp13x24917 1=bp13x24919 by funext i; fin_cases i <;> rfl]; exact p13x24919
set_option maxRecDepth 100000 in
private theorem p13x24915 : Deny 1000000000000000000 13 bp13x24915 := by
  apply split bp13x24915 2
  · rw [show leftB bp13x24915 2=bp13x24916 by funext i; fin_cases i <;> rfl]; exact p13x24916
  · rw [show rightB bp13x24915 2=bp13x24917 by funext i; fin_cases i <;> rfl]; exact p13x24917
set_option maxRecDepth 100000 in
private theorem p13x24913 : Deny 1000000000000000000 13 bp13x24913 := by
  apply split bp13x24913 1
  · rw [show leftB bp13x24913 1=bp13x24914 by funext i; fin_cases i <;> rfl]; exact p13x24914
  · rw [show rightB bp13x24913 1=bp13x24915 by funext i; fin_cases i <;> rfl]; exact p13x24915
private def bp13x26340 : B := ![⟨32,some 32⟩,⟨1022,some 1533⟩,⟨1534,none⟩]
private def bp13x26341 : B := ![⟨32,some 32⟩,⟨1022,some 1226⟩,⟨1534,none⟩]
private def bp13x26342 : B := ![⟨32,some 32⟩,⟨1022,some 1226⟩,⟨1534,some 3069⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x26342 : Deny 1000000000000000000 13 bp13x26342 :=
  sound (by decide) (by decide) 21 2094037671411289279740366055704105770452993828583833547783102743892975059665979122432180686240994035209433340837512746624933583244051895746300943016558052187647386081350079372735446093255518609484519619293856521096705052800545363077627914028707921006765706462601957837239972153721897148019853111858 (tail:=0) (by decide +kernel)
private def bp13x26845 : B := ![⟨32,some 32⟩,⟨1022,some 1226⟩,⟨3070,none⟩]
private def bp13x26846 : B := ![⟨32,some 32⟩,⟨1022,some 1114⟩,⟨3070,none⟩]
private def bp13x26847 : B := ![⟨32,some 32⟩,⟨1022,some 1114⟩,⟨3070,some 6141⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x26847 : Deny 1000000000000000000 13 bp13x26847 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x26848 : B := ![⟨32,some 32⟩,⟨1022,some 1114⟩,⟨6142,none⟩]
private def bp13x26849 : B := ![⟨32,some 32⟩,⟨1022,some 1066⟩,⟨6142,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x26849 : Deny 1000000000000000000 13 bp13x26849 :=
  sound (by decide) (by decide) 33 77996588801682913750288199239956683242751059212200320787716728308849390501098159944307024519073230443786084745898994046412094743260856116122715291372873153664069739791817603279388891954659045364912059632290626538144408728140556637626155617388964666065321204956826815279225020610522812726543226615452718985610774509898557119788625346854864453203981296980920641395191000467274668650841620212012581445640995 (tail:=0) (by decide +kernel)
private def bp13x27534 : B := ![⟨32,some 32⟩,⟨1067,some 1114⟩,⟨6142,none⟩]
private def bp13x27535 : B := ![⟨32,some 32⟩,⟨1067,some 1114⟩,⟨6142,some 12285⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x27535 : Deny 1000000000000000000 13 bp13x27535 :=
  sound (by decide) (by decide) 21 1433519246444279762334204767211915162571184791496114340379559538069963320586549832035102830372390669317327326414092993577285660609887460899450941187728477666125265549492205628442389340581635398205665983185331645080813743928852589830204800766923259602865266227051342867785985916174145078402314442365153331668587294363589346248358905345410826463716864838227346172633071200281394795764840795219701570891410578679690396850490510 (tail:=0) (by decide +kernel)
private def bp13x28250 : B := ![⟨32,some 32⟩,⟨1067,some 1114⟩,⟨12286,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x28250 : Deny 1000000000000000000 13 bp13x28250 :=
  sound (by decide) (by decide) 23 1036593449693428521552245392234741081185659193427777866139215465696429222719575818141986793624980531966593509241543102080127748625258981960814694272798546783502808275154591945266538635426782209086709463269823537563932948877717131759614565765396508901074542219759065845195052061107883134833122761807456311011507087999455147041494653776210200938614401818435263805678 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x27534 : Deny 1000000000000000000 13 bp13x27534 := by
  apply split bp13x27534 2
  · rw [show leftB bp13x27534 2=bp13x27535 by funext i; fin_cases i <;> rfl]; exact p13x27535
  · rw [show rightB bp13x27534 2=bp13x28250 by funext i; fin_cases i <;> rfl]; exact p13x28250
set_option maxRecDepth 100000 in
private theorem p13x26848 : Deny 1000000000000000000 13 bp13x26848 := by
  apply split bp13x26848 1
  · rw [show leftB bp13x26848 1=bp13x26849 by funext i; fin_cases i <;> rfl]; exact p13x26849
  · rw [show rightB bp13x26848 1=bp13x27534 by funext i; fin_cases i <;> rfl]; exact p13x27534
set_option maxRecDepth 100000 in
private theorem p13x26846 : Deny 1000000000000000000 13 bp13x26846 := by
  apply split bp13x26846 2
  · rw [show leftB bp13x26846 2=bp13x26847 by funext i; fin_cases i <;> rfl]; exact p13x26847
  · rw [show rightB bp13x26846 2=bp13x26848 by funext i; fin_cases i <;> rfl]; exact p13x26848
private def bp13x28867 : B := ![⟨32,some 32⟩,⟨1115,some 1226⟩,⟨3070,none⟩]
private def bp13x28868 : B := ![⟨32,some 32⟩,⟨1115,some 1226⟩,⟨3070,some 6141⟩]
private def bp13x28869 : B := ![⟨32,some 32⟩,⟨1115,some 1167⟩,⟨3070,some 6141⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x28869 : Deny 1000000000000000000 13 bp13x28869 :=
  sound (by decide) (by decide) 20 1195118152092912550900724509099146120880513721012272629888560521895004247727538892360534463240905347195437596269828847837183207377286886644828893849933776472115049849249377012344963807165779456849845641087250801763817623108593395746935549809410922450920943275142451006141818032783070024557534294366307833060997911783355712950471966873487560490005082516537148956383272542034893059188147350930213555445976382536340098711216232356166469661348285756495167233525415710864000792194219862348613270571094145728302517328494590266696679818474133481502436149451 (tail:=0) (by decide +kernel)
private def bp13x29794 : B := ![⟨32,some 32⟩,⟨1168,some 1226⟩,⟨3070,some 6141⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x29794 : Deny 1000000000000000000 13 bp13x29794 :=
  sound (by decide) (by decide) 18 22573134313527909147696279018443058003887213579849653641286431216822517386571044518702411323069056899836172654300243609285482574982197734943562389673108359038904913036389149446130421324613720798790006413721573825760099364823995 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x28868 : Deny 1000000000000000000 13 bp13x28868 := by
  apply split bp13x28868 1
  · rw [show leftB bp13x28868 1=bp13x28869 by funext i; fin_cases i <;> rfl]; exact p13x28869
  · rw [show rightB bp13x28868 1=bp13x29794 by funext i; fin_cases i <;> rfl]; exact p13x29794
private def bp13x30183 : B := ![⟨32,some 32⟩,⟨1115,some 1226⟩,⟨6142,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x30183 : Deny 1000000000000000000 13 bp13x30183 :=
  sound (by decide) (by decide) 21 325158675104724382857000009310996447729621358478321968410350 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x28867 : Deny 1000000000000000000 13 bp13x28867 := by
  apply split bp13x28867 2
  · rw [show leftB bp13x28867 2=bp13x28868 by funext i; fin_cases i <;> rfl]; exact p13x28868
  · rw [show rightB bp13x28867 2=bp13x30183 by funext i; fin_cases i <;> rfl]; exact p13x30183
set_option maxRecDepth 100000 in
private theorem p13x26845 : Deny 1000000000000000000 13 bp13x26845 := by
  apply split bp13x26845 1
  · rw [show leftB bp13x26845 1=bp13x26846 by funext i; fin_cases i <;> rfl]; exact p13x26846
  · rw [show rightB bp13x26845 1=bp13x28867 by funext i; fin_cases i <;> rfl]; exact p13x28867
set_option maxRecDepth 100000 in
private theorem p13x26341 : Deny 1000000000000000000 13 bp13x26341 := by
  apply split bp13x26341 2
  · rw [show leftB bp13x26341 2=bp13x26342 by funext i; fin_cases i <;> rfl]; exact p13x26342
  · rw [show rightB bp13x26341 2=bp13x26845 by funext i; fin_cases i <;> rfl]; exact p13x26845
private def bp13x30298 : B := ![⟨32,some 32⟩,⟨1227,some 1533⟩,⟨1534,none⟩]
private def bp13x30299 : B := ![⟨32,some 32⟩,⟨1227,some 1533⟩,⟨1534,some 3069⟩]
private def bp13x30300 : B := ![⟨32,some 32⟩,⟨1227,some 1363⟩,⟨1534,some 3069⟩]
private def bp13x30301 : B := ![⟨32,some 32⟩,⟨1227,some 1363⟩,⟨1534,some 2045⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x30301 : Deny 1000000000000000000 13 bp13x30301 :=
  sound (by decide) (by decide) 18 360919113781445709538773193294961410518654198754461991753401118727436095153097443501762960365065763360355421297276713945444480242773924144529861956173294208356521877243714609185141660797948580206085311774513870822805471797124049228714273482850019838295658753361320797590357422386371738890368848143230658019390769852984098976730395074721291871869023255510923254375913394793111548998672605996001264416266953966205343597765215556015504692094817002490129045118919997852633984607618790925801545195950485360026921238186609962113803473914369016601986106082245638895899300190758509745510125981436132033596558 (tail:=0) (by decide +kernel)
private def bp13x31308 : B := ![⟨32,some 32⟩,⟨1227,some 1363⟩,⟨2046,some 3069⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x31308 : Deny 1000000000000000000 13 bp13x31308 :=
  sound (by decide) (by decide) 18 241860574909161974079655187646739660975001197754545230350987749135278636967667194347744552847941455945084920383113777445802677270006963122630948097484300032347289028602042137017838857052798618798779341646786892833636604091320106322871591342699532368783699782999142859500822758292930118536535969309941420234633122590162184412674107097824458108642076278120154018542 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x30300 : Deny 1000000000000000000 13 bp13x30300 := by
  apply split bp13x30300 2
  · rw [show leftB bp13x30300 2=bp13x30301 by funext i; fin_cases i <;> rfl]; exact p13x30301
  · rw [show rightB bp13x30300 2=bp13x31308 by funext i; fin_cases i <;> rfl]; exact p13x31308
private def bp13x31923 : B := ![⟨32,some 32⟩,⟨1364,some 1533⟩,⟨1534,some 3069⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x31923 : Deny 1000000000000000000 13 bp13x31923 :=
  sound (by decide) (by decide) 18 170306223823010948740835692177505211 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x30299 : Deny 1000000000000000000 13 bp13x30299 := by
  apply split bp13x30299 1
  · rw [show leftB bp13x30299 1=bp13x30300 by funext i; fin_cases i <;> rfl]; exact p13x30300
  · rw [show rightB bp13x30299 1=bp13x31923 by funext i; fin_cases i <;> rfl]; exact p13x31923
private def bp13x31996 : B := ![⟨32,some 32⟩,⟨1227,some 1533⟩,⟨3070,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x31996 : Deny 1000000000000000000 13 bp13x31996 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x30298 : Deny 1000000000000000000 13 bp13x30298 := by
  apply split bp13x30298 2
  · rw [show leftB bp13x30298 2=bp13x30299 by funext i; fin_cases i <;> rfl]; exact p13x30299
  · rw [show rightB bp13x30298 2=bp13x31996 by funext i; fin_cases i <;> rfl]; exact p13x31996
set_option maxRecDepth 100000 in
private theorem p13x26340 : Deny 1000000000000000000 13 bp13x26340 := by
  apply split bp13x26340 1
  · rw [show leftB bp13x26340 1=bp13x26341 by funext i; fin_cases i <;> rfl]; exact p13x26341
  · rw [show rightB bp13x26340 1=bp13x30298 by funext i; fin_cases i <;> rfl]; exact p13x30298
set_option maxRecDepth 100000 in
private theorem p13x24912 : Deny 1000000000000000000 13 bp13x24912 := by
  apply split bp13x24912 2
  · rw [show leftB bp13x24912 2=bp13x24913 by funext i; fin_cases i <;> rfl]; exact p13x24913
  · rw [show rightB bp13x24912 2=bp13x26340 by funext i; fin_cases i <;> rfl]; exact p13x26340
set_option maxRecDepth 100000 in
private theorem p13x24910 : Deny 1000000000000000000 13 bp13x24910 := by
  apply split bp13x24910 1
  · rw [show leftB bp13x24910 1=bp13x24911 by funext i; fin_cases i <;> rfl]; exact p13x24911
  · rw [show rightB bp13x24910 1=bp13x24912 by funext i; fin_cases i <;> rfl]; exact p13x24912
set_option maxRecDepth 100000 in
private theorem p13x24908 : Deny 1000000000000000000 13 bp13x24908 := by
  apply split bp13x24908 2
  · rw [show leftB bp13x24908 2=bp13x24909 by funext i; fin_cases i <;> rfl]; exact p13x24909
  · rw [show rightB bp13x24908 2=bp13x24910 by funext i; fin_cases i <;> rfl]; exact p13x24910
private def bp13x31997 : B := ![⟨32,some 32⟩,⟨1534,none⟩,⟨382,none⟩]
private def bp13x31998 : B := ![⟨32,some 32⟩,⟨1534,none⟩,⟨382,some 765⟩]
private def bp13x31999 : B := ![⟨32,some 32⟩,⟨1534,some 3069⟩,⟨382,some 765⟩]
private def bp13x32000 : B := ![⟨32,some 32⟩,⟨1534,some 3069⟩,⟨382,some 509⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x32000 : Deny 1000000000000000000 13 bp13x32000 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x32001 : B := ![⟨32,some 32⟩,⟨1534,some 3069⟩,⟨510,some 765⟩]
private def bp13x32002 : B := ![⟨32,some 32⟩,⟨1534,some 2045⟩,⟨510,some 765⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x32002 : Deny 1000000000000000000 13 bp13x32002 :=
  sound (by decide) (by decide) 20 836613751175412432731818475485918193833468246274426322346819727723653357065785568871237726636444743960298999870100461599451652820247132978140294070361485667256193431651760329637096534276995542134498083 (tail:=0) (by decide +kernel)
private def bp13x32345 : B := ![⟨32,some 32⟩,⟨2046,some 3069⟩,⟨510,some 765⟩]
private def bp13x32346 : B := ![⟨32,some 32⟩,⟨2046,some 3069⟩,⟨510,some 612⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x32346 : Deny 1000000000000000000 13 bp13x32346 :=
  sound (by decide) (by decide) 19 1083236412999401092348415538854707197668259555969631091639591960682756651765137850904064941657046846942214035141883254849367255466596814802699944750073632941364184150947035215721584826990338031774521450193431761645417007516816008146800498003633628347626484451946860975132861953826198360946462237834969147590726717488374545784627615873425484688282797089709694818678328639052009122556494359739982876186645877863867555189147319360543349691480630886381068342352975306644108971638450402339127131463906148564845963185057332774975895049635598783519447311062442763100658054639651097778 (tail:=0) (by decide +kernel)
private def bp13x33315 : B := ![⟨32,some 32⟩,⟨2046,some 3069⟩,⟨613,some 765⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x33315 : Deny 1000000000000000000 13 bp13x33315 :=
  sound (by decide) (by decide) 19 990099593701200204331754278937704547913076406600212783497991945640318762921567863921446082824763032031692568691836601848061316193488703183049833404638945660842997617305033340037492141655662889598277076096276509753341052171397743887576827952384260182065413525750269409863170558402672400687614765299811809524022718644046247987582999740382360315478741878055911484022716597772185120204627301775628777099519961134557356900327023986789106511540832925356500085630560086178747852072337385634973541380567629483389756584616475542022067942890610350021341187442074180236854904602261894833029696285647562433568062223833790455097538744036615931043631940415545366094092007012379884368881679455305248513906269097279861616593134 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x32345 : Deny 1000000000000000000 13 bp13x32345 := by
  apply split bp13x32345 2
  · rw [show leftB bp13x32345 2=bp13x32346 by funext i; fin_cases i <;> rfl]; exact p13x32346
  · rw [show rightB bp13x32345 2=bp13x33315 by funext i; fin_cases i <;> rfl]; exact p13x33315
set_option maxRecDepth 100000 in
private theorem p13x32001 : Deny 1000000000000000000 13 bp13x32001 := by
  apply split bp13x32001 1
  · rw [show leftB bp13x32001 1=bp13x32002 by funext i; fin_cases i <;> rfl]; exact p13x32002
  · rw [show rightB bp13x32001 1=bp13x32345 by funext i; fin_cases i <;> rfl]; exact p13x32345
set_option maxRecDepth 100000 in
private theorem p13x31999 : Deny 1000000000000000000 13 bp13x31999 := by
  apply split bp13x31999 2
  · rw [show leftB bp13x31999 2=bp13x32000 by funext i; fin_cases i <;> rfl]; exact p13x32000
  · rw [show rightB bp13x31999 2=bp13x32001 by funext i; fin_cases i <;> rfl]; exact p13x32001
private def bp13x34510 : B := ![⟨32,some 32⟩,⟨3070,none⟩,⟨382,some 765⟩]
private def bp13x34511 : B := ![⟨32,some 32⟩,⟨3070,none⟩,⟨382,some 509⟩]
private def bp13x34512 : B := ![⟨32,some 32⟩,⟨3070,some 6141⟩,⟨382,some 509⟩]
private def bp13x34513 : B := ![⟨32,some 32⟩,⟨3070,some 6141⟩,⟨382,some 436⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x34513 : Deny 1000000000000000000 13 bp13x34513 :=
  sound (by decide) (by decide) 20 26040048837618515115981491805196190649993853657736038854354486319465027427793686402273525207692448330449870711527300929483224847046656220082738 (tail:=0) (by decide +kernel)
private def bp13x34760 : B := ![⟨32,some 32⟩,⟨3070,some 6141⟩,⟨437,some 509⟩]
private def bp13x34761 : B := ![⟨32,some 32⟩,⟨3070,some 4093⟩,⟨437,some 509⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x34761 : Deny 1000000000000000000 13 bp13x34761 :=
  sound (by decide) (by decide) 19 526954293157838498569659122804611453051738164801172846136337670600742307994949087090636526714797414500220035220117543369026491868163063044154399167357240029249789421168702010498490010010019933963696961214931249109953879428859491657189458899440861766723721799235077503103757437032021679287830788720396341278810299635784105904355 (tail:=0) (by decide +kernel)
private def bp13x35314 : B := ![⟨32,some 32⟩,⟨4094,some 6141⟩,⟨437,some 509⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x35314 : Deny 1000000000000000000 13 bp13x35314 :=
  sound (by decide) (by decide) 19 11384651633890751481785283355884344504693468191543028530931921174802763375776249720212966926565201922077851070944061066305787304209786775227802502985691676621591577977846579634770847514670730973217982156109243879279568113128963272474260430874736798384435532952007845794825139826581084897142397944290303977928438080664725069401386078291166160945463894716991718341723808051612055435322625211 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x34760 : Deny 1000000000000000000 13 bp13x34760 := by
  apply split bp13x34760 1
  · rw [show leftB bp13x34760 1=bp13x34761 by funext i; fin_cases i <;> rfl]; exact p13x34761
  · rw [show rightB bp13x34760 1=bp13x35314 by funext i; fin_cases i <;> rfl]; exact p13x35314
set_option maxRecDepth 100000 in
private theorem p13x34512 : Deny 1000000000000000000 13 bp13x34512 := by
  apply split bp13x34512 2
  · rw [show leftB bp13x34512 2=bp13x34513 by funext i; fin_cases i <;> rfl]; exact p13x34513
  · rw [show rightB bp13x34512 2=bp13x34760 by funext i; fin_cases i <;> rfl]; exact p13x34760
private def bp13x35971 : B := ![⟨32,some 32⟩,⟨6142,none⟩,⟨382,some 509⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x35971 : Deny 1000000000000000000 13 bp13x35971 :=
  sound (by decide) (by decide) 23 65483772300498784171192848736455816241484896198057983469993776284547339810856176723695185738798526659662818888857709386164679126925766330910100433279830128309527816675955877890506044017943832763860554791215432942568513015336518455291982135260243427385340953138079981252681994792127466303233078491967489857705986634534364591488432137010136945791574646912809468996082051045283423146892843877834051125610709421400094849065491897530002910781663667321304810009205095704637582477081906608237277188308344776869849373314509506509934280716597888030173082853607228744423371532947522284752519863411643 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x34511 : Deny 1000000000000000000 13 bp13x34511 := by
  apply split bp13x34511 1
  · rw [show leftB bp13x34511 1=bp13x34512 by funext i; fin_cases i <;> rfl]; exact p13x34512
  · rw [show rightB bp13x34511 1=bp13x35971 by funext i; fin_cases i <;> rfl]; exact p13x35971
private def bp13x36968 : B := ![⟨32,some 32⟩,⟨3070,none⟩,⟨510,some 765⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x36968 : Deny 1000000000000000000 13 bp13x36968 :=
  sound (by decide) (by decide) 21 43881467024536562290642004705027518125306965828293542182020253927584555542425090968898294153893392082486678240077219574661832272379680403885805783469200512140541584566025283591467633118968569438055288280379118 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x34510 : Deny 1000000000000000000 13 bp13x34510 := by
  apply split bp13x34510 2
  · rw [show leftB bp13x34510 2=bp13x34511 by funext i; fin_cases i <;> rfl]; exact p13x34511
  · rw [show rightB bp13x34510 2=bp13x36968 by funext i; fin_cases i <;> rfl]; exact p13x36968
set_option maxRecDepth 100000 in
private theorem p13x31998 : Deny 1000000000000000000 13 bp13x31998 := by
  apply split bp13x31998 1
  · rw [show leftB bp13x31998 1=bp13x31999 by funext i; fin_cases i <;> rfl]; exact p13x31999
  · rw [show rightB bp13x31998 1=bp13x34510 by funext i; fin_cases i <;> rfl]; exact p13x34510
private def bp13x37331 : B := ![⟨32,some 32⟩,⟨1534,none⟩,⟨766,none⟩]
private def bp13x37332 : B := ![⟨32,some 32⟩,⟨1534,some 3069⟩,⟨766,none⟩]
private def bp13x37333 : B := ![⟨32,some 32⟩,⟨1534,some 3069⟩,⟨766,some 1533⟩]
private def bp13x37334 : B := ![⟨32,some 32⟩,⟨1534,some 2045⟩,⟨766,some 1533⟩]
private def bp13x37335 : B := ![⟨32,some 32⟩,⟨1534,some 2045⟩,⟨766,some 1021⟩]
private def bp13x37336 : B := ![⟨32,some 32⟩,⟨1534,some 1753⟩,⟨766,some 1021⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x37336 : Deny 1000000000000000000 13 bp13x37336 :=
  sound (by decide) (by decide) 18 41326573718890731123561566938771592750300306454934512668134058440378998944838789808628170471186561363440175446401780213932124032698517706808959037482967213622951134352768469323383994762501340415222257793364962473094396093959006619992011376340995293071085920340571199178823896342262682259373566154519275841081824204927630307994416068399663094742609478479137685225413760090381673839583224221571020705564707623651693980083098416078662992843729407416784827886058332332939226166683371490035939 (tail:=0) (by decide +kernel)
private def bp13x38157 : B := ![⟨32,some 32⟩,⟨1754,some 2045⟩,⟨766,some 1021⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x38157 : Deny 1000000000000000000 13 bp13x38157 :=
  sound (by decide) (by decide) 18 653538095401278339689097633254580165357285598479929691731346213450034156569965198016347876724580697504004518091871121169787929520809591003382363204917788623087318946398562898634041532605249606989986206615625378766650165439888071409305688318902968327856158881671944770227507324193391053354513484529628265154593762131078691726928436826152302628429363363592805584060897557182689041690028995467093550410805215221763183286447047721854815155942769195184180717989663640323171904227417433392739118577769694137249971530561751563866555078557499165929934011 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x37335 : Deny 1000000000000000000 13 bp13x37335 := by
  apply split bp13x37335 1
  · rw [show leftB bp13x37335 1=bp13x37336 by funext i; fin_cases i <;> rfl]; exact p13x37336
  · rw [show rightB bp13x37335 1=bp13x38157 by funext i; fin_cases i <;> rfl]; exact p13x38157
private def bp13x39078 : B := ![⟨32,some 32⟩,⟨1534,some 2045⟩,⟨1022,some 1533⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x39078 : Deny 1000000000000000000 13 bp13x39078 :=
  sound (by decide) (by decide) 19 39363060016328619439443501584141186454174910188259710325306321168099110296266858900675777245148604898499375858098529517206643220776395792427885619707034544654953230192642012964083790830917701956268422065957978146392812047715954040376244301656294333385160930580520174402825479301381926134019762702611856436974 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x37334 : Deny 1000000000000000000 13 bp13x37334 := by
  apply split bp13x37334 2
  · rw [show leftB bp13x37334 2=bp13x37335 by funext i; fin_cases i <;> rfl]; exact p13x37335
  · rw [show rightB bp13x37334 2=bp13x39078 by funext i; fin_cases i <;> rfl]; exact p13x39078
private def bp13x39603 : B := ![⟨32,some 32⟩,⟨2046,some 3069⟩,⟨766,some 1533⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x39603 : Deny 1000000000000000000 13 bp13x39603 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x37333 : Deny 1000000000000000000 13 bp13x37333 := by
  apply split bp13x37333 1
  · rw [show leftB bp13x37333 1=bp13x37334 by funext i; fin_cases i <;> rfl]; exact p13x37334
  · rw [show rightB bp13x37333 1=bp13x39603 by funext i; fin_cases i <;> rfl]; exact p13x39603
private def bp13x39604 : B := ![⟨32,some 32⟩,⟨1534,some 3069⟩,⟨1534,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x39604 : Deny 1000000000000000000 13 bp13x39604 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x37332 : Deny 1000000000000000000 13 bp13x37332 := by
  apply split bp13x37332 2
  · rw [show leftB bp13x37332 2=bp13x37333 by funext i; fin_cases i <;> rfl]; exact p13x37333
  · rw [show rightB bp13x37332 2=bp13x39604 by funext i; fin_cases i <;> rfl]; exact p13x39604
private def bp13x39605 : B := ![⟨32,some 32⟩,⟨3070,none⟩,⟨766,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x39605 : Deny 1000000000000000000 13 bp13x39605 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x37331 : Deny 1000000000000000000 13 bp13x37331 := by
  apply split bp13x37331 1
  · rw [show leftB bp13x37331 1=bp13x37332 by funext i; fin_cases i <;> rfl]; exact p13x37332
  · rw [show rightB bp13x37331 1=bp13x39605 by funext i; fin_cases i <;> rfl]; exact p13x39605
set_option maxRecDepth 100000 in
private theorem p13x31997 : Deny 1000000000000000000 13 bp13x31997 := by
  apply split bp13x31997 2
  · rw [show leftB bp13x31997 2=bp13x31998 by funext i; fin_cases i <;> rfl]; exact p13x31998
  · rw [show rightB bp13x31997 2=bp13x37331 by funext i; fin_cases i <;> rfl]; exact p13x37331
set_option maxRecDepth 100000 in
private theorem p13x24907 : Deny 1000000000000000000 13 bp13x24907 := by
  apply split bp13x24907 1
  · rw [show leftB bp13x24907 1=bp13x24908 by funext i; fin_cases i <;> rfl]; exact p13x24908
  · rw [show rightB bp13x24907 1=bp13x31997 by funext i; fin_cases i <;> rfl]; exact p13x31997
set_option maxRecDepth 100000 in
private theorem p13x23609 : Deny 1000000000000000000 13 bp13x23609 := by
  apply split bp13x23609 2
  · rw [show leftB bp13x23609 2=bp13x23610 by funext i; fin_cases i <;> rfl]; exact p13x23610
  · rw [show rightB bp13x23609 2=bp13x24907 by funext i; fin_cases i <;> rfl]; exact p13x24907
set_option maxRecDepth 100000 in
private theorem p13x23607 : Deny 1000000000000000000 13 bp13x23607 := by
  apply split bp13x23607 0
  · rw [show leftB bp13x23607 0=bp13x23608 by funext i; fin_cases i <;> rfl]; exact p13x23608
  · rw [show rightB bp13x23607 0=bp13x23609 by funext i; fin_cases i <;> rfl]; exact p13x23609
set_option maxRecDepth 100000 in
private theorem p13x23605 : Deny 1000000000000000000 13 bp13x23605 := by
  apply split bp13x23605 1
  · rw [show leftB bp13x23605 1=bp13x23606 by funext i; fin_cases i <;> rfl]; exact p13x23606
  · rw [show rightB bp13x23605 1=bp13x23607 by funext i; fin_cases i <;> rfl]; exact p13x23607
set_option maxRecDepth 100000 in
private theorem p13x23603 : Deny 1000000000000000000 13 bp13x23603 := by
  apply split bp13x23603 2
  · rw [show leftB bp13x23603 2=bp13x23604 by funext i; fin_cases i <;> rfl]; exact p13x23604
  · rw [show rightB bp13x23603 2=bp13x23605 by funext i; fin_cases i <;> rfl]; exact p13x23605
set_option maxRecDepth 100000 in
private theorem p13x23601 : Deny 1000000000000000000 13 bp13x23601 := by
  apply split bp13x23601 0
  · rw [show leftB bp13x23601 0=bp13x23602 by funext i; fin_cases i <;> rfl]; exact p13x23602
  · rw [show rightB bp13x23601 0=bp13x23603 by funext i; fin_cases i <;> rfl]; exact p13x23603
set_option maxRecDepth 100000 in
private theorem p13x23599 : Deny 1000000000000000000 13 bp13x23599 := by
  apply split bp13x23599 1
  · rw [show leftB bp13x23599 1=bp13x23600 by funext i; fin_cases i <;> rfl]; exact p13x23600
  · rw [show rightB bp13x23599 1=bp13x23601 by funext i; fin_cases i <;> rfl]; exact p13x23601
set_option maxRecDepth 100000 in
private theorem p13x23597 : Deny 1000000000000000000 13 bp13x23597 := by
  apply split bp13x23597 2
  · rw [show leftB bp13x23597 2=bp13x23598 by funext i; fin_cases i <;> rfl]; exact p13x23598
  · rw [show rightB bp13x23597 2=bp13x23599 by funext i; fin_cases i <;> rfl]; exact p13x23599
set_option maxRecDepth 100000 in
private theorem p13x23595 : Deny 1000000000000000000 13 bp13x23595 := by
  apply split bp13x23595 1
  · rw [show leftB bp13x23595 1=bp13x23596 by funext i; fin_cases i <;> rfl]; exact p13x23596
  · rw [show rightB bp13x23595 1=bp13x23597 by funext i; fin_cases i <;> rfl]; exact p13x23597
private def bp13x39606 : B := ![⟨33,some 36⟩,⟨94,none⟩,⟨46,none⟩]
private def bp13x39607 : B := ![⟨33,some 36⟩,⟨94,some 189⟩,⟨46,none⟩]
private def bp13x39608 : B := ![⟨33,some 36⟩,⟨94,some 189⟩,⟨46,some 93⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x39608 : Deny 1000000000000000000 13 bp13x39608 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x39609 : B := ![⟨33,some 36⟩,⟨94,some 189⟩,⟨94,none⟩]
private def bp13x39610 : B := ![⟨33,some 36⟩,⟨94,some 125⟩,⟨94,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x39610 : Deny 1000000000000000000 13 bp13x39610 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x39611 : B := ![⟨33,some 36⟩,⟨126,some 189⟩,⟨94,none⟩]
private def bp13x39612 : B := ![⟨33,some 34⟩,⟨126,some 189⟩,⟨94,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x39612 : Deny 1000000000000000000 13 bp13x39612 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x39613 : B := ![⟨35,some 36⟩,⟨126,some 189⟩,⟨94,none⟩]
private def bp13x39614 : B := ![⟨35,some 36⟩,⟨126,some 189⟩,⟨94,some 189⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x39614 : Deny 1000000000000000000 13 bp13x39614 :=
  sound (by decide) (by decide) 17 1705878724716982918816845550773792329901109768639586990380357096558216305715844948274 (tail:=0) (by decide +kernel)
private def bp13x39761 : B := ![⟨35,some 36⟩,⟨126,some 189⟩,⟨190,none⟩]
private def bp13x39762 : B := ![⟨35,some 36⟩,⟨126,some 151⟩,⟨190,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x39762 : Deny 1000000000000000000 13 bp13x39762 :=
  sound (by decide) (by decide) 30 45877511938878441993952297951039653302150718661530647036651714809443861681093017865319070370646951001304403760149816544544823041331643265736353587862916645487854840089820612867545386040373909555888397298239454904891114254536682644812413986253908473692516956512704175669592458574533094058095281175351333772627079 (tail:=0) (by decide +kernel)
private def bp13x40289 : B := ![⟨35,some 36⟩,⟨152,some 189⟩,⟨190,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x40289 : Deny 1000000000000000000 13 bp13x40289 :=
  sound (by decide) (by decide) 31 12468800461411429667242285671030972374674986119541239136679697701636873878765370433334634780055588867327387454818646785971208576967150614891788902946601770411878912581794760582046111833262704548916286890439624218344940173916447936580934061067936218032133132578888620132727889942438219133973794933017816303368253436184395651547568139619944052340709660900451295526174382743787582976549222878071663528754885283254526450281316043340582376705422306946680961857843583894612628237430240695300878308965516196743 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x39761 : Deny 1000000000000000000 13 bp13x39761 := by
  apply split bp13x39761 1
  · rw [show leftB bp13x39761 1=bp13x39762 by funext i; fin_cases i <;> rfl]; exact p13x39762
  · rw [show rightB bp13x39761 1=bp13x40289 by funext i; fin_cases i <;> rfl]; exact p13x40289
set_option maxRecDepth 100000 in
private theorem p13x39613 : Deny 1000000000000000000 13 bp13x39613 := by
  apply split bp13x39613 2
  · rw [show leftB bp13x39613 2=bp13x39614 by funext i; fin_cases i <;> rfl]; exact p13x39614
  · rw [show rightB bp13x39613 2=bp13x39761 by funext i; fin_cases i <;> rfl]; exact p13x39761
set_option maxRecDepth 100000 in
private theorem p13x39611 : Deny 1000000000000000000 13 bp13x39611 := by
  apply split bp13x39611 0
  · rw [show leftB bp13x39611 0=bp13x39612 by funext i; fin_cases i <;> rfl]; exact p13x39612
  · rw [show rightB bp13x39611 0=bp13x39613 by funext i; fin_cases i <;> rfl]; exact p13x39613
set_option maxRecDepth 100000 in
private theorem p13x39609 : Deny 1000000000000000000 13 bp13x39609 := by
  apply split bp13x39609 1
  · rw [show leftB bp13x39609 1=bp13x39610 by funext i; fin_cases i <;> rfl]; exact p13x39610
  · rw [show rightB bp13x39609 1=bp13x39611 by funext i; fin_cases i <;> rfl]; exact p13x39611
set_option maxRecDepth 100000 in
private theorem p13x39607 : Deny 1000000000000000000 13 bp13x39607 := by
  apply split bp13x39607 2
  · rw [show leftB bp13x39607 2=bp13x39608 by funext i; fin_cases i <;> rfl]; exact p13x39608
  · rw [show rightB bp13x39607 2=bp13x39609 by funext i; fin_cases i <;> rfl]; exact p13x39609
private def bp13x41136 : B := ![⟨33,some 36⟩,⟨190,none⟩,⟨46,none⟩]
private def bp13x41137 : B := ![⟨33,some 36⟩,⟨190,none⟩,⟨46,some 93⟩]
private def bp13x41138 : B := ![⟨33,some 36⟩,⟨190,some 381⟩,⟨46,some 93⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x41138 : Deny 1000000000000000000 13 bp13x41138 :=
  sound (by decide) (by decide) 18 2253219216954764190664914319789266292122198111350563810530173271837080778325367786596246503089550355762757682412390208970863818620021722280837092966386499404858458313764645525540401 (tail:=0) (by decide +kernel)
private def bp13x41447 : B := ![⟨33,some 36⟩,⟨382,none⟩,⟨46,some 93⟩]
private def bp13x41448 : B := ![⟨33,some 34⟩,⟨382,none⟩,⟨46,some 93⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x41448 : Deny 1000000000000000000 13 bp13x41448 :=
  sound (by decide) (by decide) 32 9948799415934268859538486836350322124009653383654661687374386507935790626565923177189126665576280079312385685673279791704375587185402397764766599967337458189677735099476541242685556654008954991775784237523725382488374401144820184670142337789012000396594544025275135592486174218598340403808804717997415071756510246153899628750441667672918757162649379 (tail:=0) (by decide +kernel)
private def bp13x42039 : B := ![⟨35,some 36⟩,⟨382,none⟩,⟨46,some 93⟩]
private def bp13x42040 : B := ![⟨35,some 36⟩,⟨382,none⟩,⟨46,some 61⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x42040 : Deny 1000000000000000000 13 bp13x42040 :=
  sound (by decide) (by decide) 32 261890517029453710796490896513599598994645858504070264991094536621755248283442762971381728759039788356428462886366349359167786000924400349490124821317431161122155469228093508552231344587317631299299733564073161760511237243304717071302613942954655146616198889550023164582700878139839077650191618279812207362842797028073475706443861914900394828900909435324176449801680453303442407806087589788831909460682356814 (tail:=0) (by decide +kernel)
private def bp13x42731 : B := ![⟨35,some 36⟩,⟨382,none⟩,⟨62,some 93⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x42731 : Deny 1000000000000000000 13 bp13x42731 :=
  sound (by decide) (by decide) 19 466486972912996150779554835296279339550632899593092831633476887243975219745116770782084790981073620856333423156934482762622583324029249825320424713636337891394173347887949972674112537852905242538406297109414328628807817618674807656526859643525795562639411845369876841508933149730871892976605419498448624890449054 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x42039 : Deny 1000000000000000000 13 bp13x42039 := by
  apply split bp13x42039 2
  · rw [show leftB bp13x42039 2=bp13x42040 by funext i; fin_cases i <;> rfl]; exact p13x42040
  · rw [show rightB bp13x42039 2=bp13x42731 by funext i; fin_cases i <;> rfl]; exact p13x42731
set_option maxRecDepth 100000 in
private theorem p13x41447 : Deny 1000000000000000000 13 bp13x41447 := by
  apply split bp13x41447 0
  · rw [show leftB bp13x41447 0=bp13x41448 by funext i; fin_cases i <;> rfl]; exact p13x41448
  · rw [show rightB bp13x41447 0=bp13x42039 by funext i; fin_cases i <;> rfl]; exact p13x42039
set_option maxRecDepth 100000 in
private theorem p13x41137 : Deny 1000000000000000000 13 bp13x41137 := by
  apply split bp13x41137 1
  · rw [show leftB bp13x41137 1=bp13x41138 by funext i; fin_cases i <;> rfl]; exact p13x41138
  · rw [show rightB bp13x41137 1=bp13x41447 by funext i; fin_cases i <;> rfl]; exact p13x41447
private def bp13x43260 : B := ![⟨33,some 36⟩,⟨190,none⟩,⟨94,none⟩]
private def bp13x43261 : B := ![⟨33,some 36⟩,⟨190,some 381⟩,⟨94,none⟩]
private def bp13x43262 : B := ![⟨33,some 34⟩,⟨190,some 381⟩,⟨94,none⟩]
private def bp13x43263 : B := ![⟨33,some 34⟩,⟨190,some 381⟩,⟨94,some 189⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x43263 : Deny 1000000000000000000 13 bp13x43263 :=
  sound (by decide) (by decide) 19 796424002675479993274650780963913124747938046258 (tail:=0) (by decide +kernel)
private def bp13x43348 : B := ![⟨33,some 34⟩,⟨190,some 381⟩,⟨190,none⟩]
private def bp13x43349 : B := ![⟨33,some 34⟩,⟨190,some 253⟩,⟨190,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x43349 : Deny 1000000000000000000 13 bp13x43349 :=
  sound (by decide) (by decide) 30 392948126479914099225385613934338543228375846258336270303641625895501204338862454346375932059122366484152083323123556546247518426034970731621031148726639892261537518007906995020296895919342759678289583766403940863560177643221022438213617912542244589054239684826095937080813475484685968103024784653228110455169422704201887293428630653148370573287742184919143398368341515137795719474048354439809439189856156279157267 (tail:=0) (by decide +kernel)
private def bp13x44048 : B := ![⟨33,some 34⟩,⟨254,some 381⟩,⟨190,none⟩]
private def bp13x44049 : B := ![⟨33,some 34⟩,⟨254,some 381⟩,⟨190,some 381⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x44049 : Deny 1000000000000000000 13 bp13x44049 :=
  sound (by decide) (by decide) 18 93808856957452387168659919085651529195452640127979210955184346081687322634817149658477880332294227066960987671163475036775148163198917176432066698468817687898707002720216362503889604982071922910354147513904184877438115194850629315877164542515662872488834366530093875809898460093877643392182286433100134550098928038680040734838682118939512354828038953165112120931293878969963870179905191723758660591415603937263756397856001542369 (tail:=0) (by decide +kernel)
private def bp13x44772 : B := ![⟨33,some 34⟩,⟨254,some 381⟩,⟨382,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x44772 : Deny 1000000000000000000 13 bp13x44772 :=
  sound (by decide) (by decide) 40 156417651849317539123149817332784699636270620670504459462163394912338261367729357294695800687761295775327021377643073698445224201027519077323844671482351991965906159038206871742451961940119772756007010113703010868217884581749638315967000542247685601949270920192136453720058427930334813299481955582847054261651366467965560521556984425227803234408370991011839253257468279064260032718833414305118057678947479642216648385826602040960089737393639009211419597467375087768496309359468138152230998048892428058913642762715376682986550406004306852932649120834156288982631804347461304387708404080306283574355457451928327696987290911993666159229896293210720502876019512725681522889 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x44048 : Deny 1000000000000000000 13 bp13x44048 := by
  apply split bp13x44048 2
  · rw [show leftB bp13x44048 2=bp13x44049 by funext i; fin_cases i <;> rfl]; exact p13x44049
  · rw [show rightB bp13x44048 2=bp13x44772 by funext i; fin_cases i <;> rfl]; exact p13x44772
set_option maxRecDepth 100000 in
private theorem p13x43348 : Deny 1000000000000000000 13 bp13x43348 := by
  apply split bp13x43348 1
  · rw [show leftB bp13x43348 1=bp13x43349 by funext i; fin_cases i <;> rfl]; exact p13x43349
  · rw [show rightB bp13x43348 1=bp13x44048 by funext i; fin_cases i <;> rfl]; exact p13x44048
set_option maxRecDepth 100000 in
private theorem p13x43262 : Deny 1000000000000000000 13 bp13x43262 := by
  apply split bp13x43262 2
  · rw [show leftB bp13x43262 2=bp13x43263 by funext i; fin_cases i <;> rfl]; exact p13x43263
  · rw [show rightB bp13x43262 2=bp13x43348 by funext i; fin_cases i <;> rfl]; exact p13x43348
private def bp13x45895 : B := ![⟨35,some 36⟩,⟨190,some 381⟩,⟨94,none⟩]
private def bp13x45896 : B := ![⟨35,some 36⟩,⟨190,some 381⟩,⟨94,some 189⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x45896 : Deny 1000000000000000000 13 bp13x45896 :=
  sound (by decide) (by decide) 18 19911601752377443965199187741482410031104413102578099188847935029803718054674345554172081734729992115626844883122896997417533979583576659384340476015004850959382681455812851761057475255999251124598080077221592104147989781217339730889093003938260908623066258166357421315487395235165228015710509210510183012652270907288079173136353414881623454955474064988266912236271063635958247830674624691279571187902033288386391804386426605189364024221491511275528630007236182432513033920032118447935032080226836944659625863635007483598023434471781451314800726980402740477307358750 (tail:=0) (by decide +kernel)
private def bp13x46847 : B := ![⟨35,some 36⟩,⟨190,some 381⟩,⟨190,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x46847 : Deny 1000000000000000000 13 bp13x46847 :=
  sound (by decide) (by decide) 19 1652375586624713521084448553263073087604921486964815993415447671307823982065820640902772806768886222234313855010134915501749177180276031326218446269969484553887962970768949328027117473081559517118554676775153999907398428950542337836669430567680659352762467021801180062 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x45895 : Deny 1000000000000000000 13 bp13x45895 := by
  apply split bp13x45895 2
  · rw [show leftB bp13x45895 2=bp13x45896 by funext i; fin_cases i <;> rfl]; exact p13x45896
  · rw [show rightB bp13x45895 2=bp13x46847 by funext i; fin_cases i <;> rfl]; exact p13x46847
set_option maxRecDepth 100000 in
private theorem p13x43261 : Deny 1000000000000000000 13 bp13x43261 := by
  apply split bp13x43261 0
  · rw [show leftB bp13x43261 0=bp13x43262 by funext i; fin_cases i <;> rfl]; exact p13x43262
  · rw [show rightB bp13x43261 0=bp13x45895 by funext i; fin_cases i <;> rfl]; exact p13x45895
private def bp13x47306 : B := ![⟨33,some 36⟩,⟨382,none⟩,⟨94,none⟩]
private def bp13x47307 : B := ![⟨33,some 34⟩,⟨382,none⟩,⟨94,none⟩]
private def bp13x47308 : B := ![⟨33,some 34⟩,⟨382,none⟩,⟨94,some 189⟩]
private def bp13x47309 : B := ![⟨33,some 34⟩,⟨382,some 765⟩,⟨94,some 189⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x47309 : Deny 1000000000000000000 13 bp13x47309 :=
  sound (by decide) (by decide) 18 29634162595518052568787192292175669336272083544354290344984745468296380120422853301997616820931035821876067886244910902602828701724527452077043800744136807479261194036808010991125608601219924725703307165510396036531674716607846194151558424009076026170107287842457676486839896540645320433867140897264408335282271486350840375196495069478028430367410548415154727648255223479916747762707739020706765028172737203957301228893387478991645845331994961176128334948765411268617649543916679 (tail:=0) (by decide +kernel)
private def bp13x48116 : B := ![⟨33,some 34⟩,⟨766,none⟩,⟨94,some 189⟩]
private def bp13x48117 : B := ![⟨33,some 34⟩,⟨766,none⟩,⟨94,some 125⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x48117 : Deny 1000000000000000000 13 bp13x48117 :=
  sound (by decide) (by decide) 40 325201758719180688654403935844900203633423254431947745885721531154116794681895885200595510053329641320790696974957168373633445904344289862251950634955126251499814310467211769156697696045195110257236079577705807083019567032569886600389965472229071942032708246853283843949349553011031659989968418172726454958754625126444191245869305336912139208620677759903904335405559232880099655879163449642213316055823275917470841004681616335725263969646526749347488460177983689 (tail:=0) (by decide +kernel)
private def bp13x48896 : B := ![⟨33,some 34⟩,⟨766,none⟩,⟨126,some 189⟩]
private def bp13x48897 : B := ![⟨33,some 33⟩,⟨766,none⟩,⟨126,some 189⟩]
private def bp13x48898 : B := ![⟨33,some 33⟩,⟨766,some 1533⟩,⟨126,some 189⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x48898 : Deny 1000000000000000000 13 bp13x48898 :=
  sound (by decide) (by decide) 18 1270373315135004431999358820526567919743356535876809846800347823398156708504319691611282543127607173172294046601182710056453869714607125457330916018821870058643652940512872959011379495142654602198576503991264518197710808244622151268985532279533016239475938950204713437723816429911328995 (tail:=0) (by decide +kernel)
private def bp13x49381 : B := ![⟨33,some 33⟩,⟨1534,none⟩,⟨126,some 189⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x49381 : Deny 1000000000000000000 13 bp13x49381 :=
  sound (by decide) (by decide) 22 968195825992360502108840725954583095330602455081619427061615960852046015456841182107597780597292535419885954566636128293846267247269327601385175730419183212496292747638397780345474978984091364299234920012803946063044054958057208686016146636561586085980906130493111569629812218154352197854809958605925995370436680893688633971244302292747809663928380688143702396881486836812454358073634792172131037791372469281198715067815464123 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x48897 : Deny 1000000000000000000 13 bp13x48897 := by
  apply split bp13x48897 1
  · rw [show leftB bp13x48897 1=bp13x48898 by funext i; fin_cases i <;> rfl]; exact p13x48898
  · rw [show rightB bp13x48897 1=bp13x49381 by funext i; fin_cases i <;> rfl]; exact p13x49381
private def bp13x50100 : B := ![⟨34,some 34⟩,⟨766,none⟩,⟨126,some 189⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x50100 : Deny 1000000000000000000 13 bp13x50100 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x48896 : Deny 1000000000000000000 13 bp13x48896 := by
  apply split bp13x48896 0
  · rw [show leftB bp13x48896 0=bp13x48897 by funext i; fin_cases i <;> rfl]; exact p13x48897
  · rw [show rightB bp13x48896 0=bp13x50100 by funext i; fin_cases i <;> rfl]; exact p13x50100
set_option maxRecDepth 100000 in
private theorem p13x48116 : Deny 1000000000000000000 13 bp13x48116 := by
  apply split bp13x48116 2
  · rw [show leftB bp13x48116 2=bp13x48117 by funext i; fin_cases i <;> rfl]; exact p13x48117
  · rw [show rightB bp13x48116 2=bp13x48896 by funext i; fin_cases i <;> rfl]; exact p13x48896
set_option maxRecDepth 100000 in
private theorem p13x47308 : Deny 1000000000000000000 13 bp13x47308 := by
  apply split bp13x47308 1
  · rw [show leftB bp13x47308 1=bp13x47309 by funext i; fin_cases i <;> rfl]; exact p13x47309
  · rw [show rightB bp13x47308 1=bp13x48116 by funext i; fin_cases i <;> rfl]; exact p13x48116
private def bp13x50101 : B := ![⟨33,some 34⟩,⟨382,none⟩,⟨190,none⟩]
private def bp13x50102 : B := ![⟨33,some 34⟩,⟨382,some 765⟩,⟨190,none⟩]
private def bp13x50103 : B := ![⟨33,some 34⟩,⟨382,some 765⟩,⟨190,some 381⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x50103 : Deny 1000000000000000000 13 bp13x50103 :=
  sound (by decide) (by decide) 20 127067932707302013556822900062069061274925100926329508606581107628551810042394844045142692149775376393604939008872964215393404538670280349163989830108708282614558576667690777805443555122584166960670273894552946836847296939798634066765986819001328474846281472042116604643114115727188918158641109563663606142708168635776728882576176028253615433337146306603203856715467604423524042278541273373677674329843810429874717030734985373420291096668426737068408742874009186446050358202685263903189141151406838646541557491107115086927933542472555348864955694289504536355766611823965585512827137172784772910894971122157950363089889468017946186664535731090085206715151049 (tail:=0) (by decide +kernel)
private def bp13x51206 : B := ![⟨33,some 34⟩,⟨382,some 765⟩,⟨382,none⟩]
private def bp13x51207 : B := ![⟨33,some 33⟩,⟨382,some 765⟩,⟨382,none⟩]
private def bp13x51208 : B := ![⟨33,some 33⟩,⟨382,some 509⟩,⟨382,none⟩]
private def bp13x51209 : B := ![⟨33,some 33⟩,⟨382,some 509⟩,⟨382,some 765⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x51209 : Deny 1000000000000000000 13 bp13x51209 :=
  sound (by decide) (by decide) 18 165774562800305599549647736631649581398094490406193784760319202766355633830197028603107042493951790926482617924322351446756668767200068996913295131152044957357383221090765538389138309435854288778221712184028918087346479817074852071982769858887608399666781023972256074071435394724179962031705388155083085385011448981946065325490816859298566011417873989767032804319760330387305776095341927440168891490856508305161702284556521911157250973366575041592098743327591303363789854803325482178965503696089943182 (tail:=0) (by decide +kernel)
private def bp13x52052 : B := ![⟨33,some 33⟩,⟨382,some 509⟩,⟨766,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x52052 : Deny 1000000000000000000 13 bp13x52052 :=
  sound (by decide) (by decide) 21 2640370199972414796675594642688609770958054534546613756386889433901513281202449366593650346484328798989796937598791024937904552614277294525586336716709286029635678330037053107059455705634661047750738395561954833211672486420976983720116957115323150508792645733656577003147466248458650033964585805463018216372867449463570894546692253412423791681890276805657373559295950009294931732327564679172774938105020434763206445046086755836883733078185329030937111964124901671276254111336642798 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x51208 : Deny 1000000000000000000 13 bp13x51208 := by
  apply split bp13x51208 2
  · rw [show leftB bp13x51208 2=bp13x51209 by funext i; fin_cases i <;> rfl]; exact p13x51209
  · rw [show rightB bp13x51208 2=bp13x52052 by funext i; fin_cases i <;> rfl]; exact p13x52052
private def bp13x52863 : B := ![⟨33,some 33⟩,⟨510,some 765⟩,⟨382,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x52863 : Deny 1000000000000000000 13 bp13x52863 :=
  sound (by decide) (by decide) 18 6821871256738809571827178382615510056389711809567032951449863734473182323473993939899 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x51207 : Deny 1000000000000000000 13 bp13x51207 := by
  apply split bp13x51207 1
  · rw [show leftB bp13x51207 1=bp13x51208 by funext i; fin_cases i <;> rfl]; exact p13x51208
  · rw [show rightB bp13x51207 1=bp13x52863 by funext i; fin_cases i <;> rfl]; exact p13x52863
private def bp13x53018 : B := ![⟨34,some 34⟩,⟨382,some 765⟩,⟨382,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x53018 : Deny 1000000000000000000 13 bp13x53018 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x51206 : Deny 1000000000000000000 13 bp13x51206 := by
  apply split bp13x51206 0
  · rw [show leftB bp13x51206 0=bp13x51207 by funext i; fin_cases i <;> rfl]; exact p13x51207
  · rw [show rightB bp13x51206 0=bp13x53018 by funext i; fin_cases i <;> rfl]; exact p13x53018
set_option maxRecDepth 100000 in
private theorem p13x50102 : Deny 1000000000000000000 13 bp13x50102 := by
  apply split bp13x50102 2
  · rw [show leftB bp13x50102 2=bp13x50103 by funext i; fin_cases i <;> rfl]; exact p13x50103
  · rw [show rightB bp13x50102 2=bp13x51206 by funext i; fin_cases i <;> rfl]; exact p13x51206
private def bp13x53019 : B := ![⟨33,some 34⟩,⟨766,none⟩,⟨190,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x53019 : Deny 1000000000000000000 13 bp13x53019 :=
  sound (by decide) (by decide) 21 1152554381034146660640649000137932508309393740878973937233223373013814241273942584518802887848474230964094350136350237278048144628399718925346571834162222000363062672069228056978788659635958044829549563647398979546302339800648482401093993525143095301605179230588388306663 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x50101 : Deny 1000000000000000000 13 bp13x50101 := by
  apply split bp13x50101 1
  · rw [show leftB bp13x50101 1=bp13x50102 by funext i; fin_cases i <;> rfl]; exact p13x50102
  · rw [show rightB bp13x50101 1=bp13x53019 by funext i; fin_cases i <;> rfl]; exact p13x53019
set_option maxRecDepth 100000 in
private theorem p13x47307 : Deny 1000000000000000000 13 bp13x47307 := by
  apply split bp13x47307 2
  · rw [show leftB bp13x47307 2=bp13x47308 by funext i; fin_cases i <;> rfl]; exact p13x47308
  · rw [show rightB bp13x47307 2=bp13x50101 by funext i; fin_cases i <;> rfl]; exact p13x50101
private def bp13x53484 : B := ![⟨35,some 36⟩,⟨382,none⟩,⟨94,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x53484 : Deny 1000000000000000000 13 bp13x53484 :=
  sound (by decide) (by decide) 18 39054802062077563 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x47306 : Deny 1000000000000000000 13 bp13x47306 := by
  apply split bp13x47306 0
  · rw [show leftB bp13x47306 0=bp13x47307 by funext i; fin_cases i <;> rfl]; exact p13x47307
  · rw [show rightB bp13x47306 0=bp13x53484 by funext i; fin_cases i <;> rfl]; exact p13x53484
set_option maxRecDepth 100000 in
private theorem p13x43260 : Deny 1000000000000000000 13 bp13x43260 := by
  apply split bp13x43260 1
  · rw [show leftB bp13x43260 1=bp13x43261 by funext i; fin_cases i <;> rfl]; exact p13x43261
  · rw [show rightB bp13x43260 1=bp13x47306 by funext i; fin_cases i <;> rfl]; exact p13x47306
set_option maxRecDepth 100000 in
private theorem p13x41136 : Deny 1000000000000000000 13 bp13x41136 := by
  apply split bp13x41136 2
  · rw [show leftB bp13x41136 2=bp13x41137 by funext i; fin_cases i <;> rfl]; exact p13x41137
  · rw [show rightB bp13x41136 2=bp13x43260 by funext i; fin_cases i <;> rfl]; exact p13x43260
set_option maxRecDepth 100000 in
private theorem p13x39606 : Deny 1000000000000000000 13 bp13x39606 := by
  apply split bp13x39606 1
  · rw [show leftB bp13x39606 1=bp13x39607 by funext i; fin_cases i <;> rfl]; exact p13x39607
  · rw [show rightB bp13x39606 1=bp13x41136 by funext i; fin_cases i <;> rfl]; exact p13x41136
set_option maxRecDepth 100000 in
private theorem p13x23594 : Deny 1000000000000000000 13 bp13x23594 := by
  apply split bp13x23594 0
  · rw [show leftB bp13x23594 0=bp13x23595 by funext i; fin_cases i <;> rfl]; exact p13x23595
  · rw [show rightB bp13x23594 0=bp13x39606 by funext i; fin_cases i <;> rfl]; exact p13x39606
set_option maxRecDepth 100000 in
private theorem p13x23356 : Deny 1000000000000000000 13 bp13x23356 := by
  apply split bp13x23356 2
  · rw [show leftB bp13x23356 2=bp13x23357 by funext i; fin_cases i <;> rfl]; exact p13x23357
  · rw [show rightB bp13x23356 2=bp13x23594 by funext i; fin_cases i <;> rfl]; exact p13x23594
private def bp13x53527 : B := ![⟨37,some 45⟩,⟨94,none⟩,⟨22,none⟩]
private def bp13x53528 : B := ![⟨37,some 45⟩,⟨94,none⟩,⟨22,some 45⟩]
private def bp13x53529 : B := ![⟨37,some 45⟩,⟨94,some 189⟩,⟨22,some 45⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x53529 : Deny 1000000000000000000 13 bp13x53529 :=
  sound (by decide) (by decide) 17 2534649988502826260072305852960467014875436766028059811500895811875818601595532278535229064660140262585927170101172523867585778009136945384632046176528980713965378662347951824061988898128209756412385576894813980464305023517737095644292001519176938389375011714390450360631215989129822710690773801119155273677678438964605793941706409415392111054464520074079106573005497694981208763359086475725736486167186553386907450702714032285453634324254380737030931883706001391541171164426159172249582069873375408311381836941 (tail:=0) (by decide +kernel)
private def bp13x54386 : B := ![⟨37,some 45⟩,⟨190,none⟩,⟨22,some 45⟩]
private def bp13x54387 : B := ![⟨37,some 40⟩,⟨190,none⟩,⟨22,some 45⟩]
private def bp13x54388 : B := ![⟨37,some 40⟩,⟨190,none⟩,⟨22,some 29⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x54388 : Deny 1000000000000000000 13 bp13x54388 :=
  sound (by decide) (by decide) 25 435248627476041739219665237621567528935124283604074319578408807139804629755324480937693814647107070811143266214718290169577046703038531159419393723154 (tail:=0) (by decide +kernel)
private def bp13x54645 : B := ![⟨37,some 40⟩,⟨190,none⟩,⟨30,some 45⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x54645 : Deny 1000000000000000000 13 bp13x54645 :=
  sound (by decide) (by decide) 32 123241033348022814500003964363552506749028613072917813928727326764459206561545808526879918170056064375229479536294443933801737903064524629577396410055179432813390753066202508861096467757305432522871771296786335407362028928051029132399812413480352924946307229093683491553562439280522577616763223520124991258325147120826127748160497618830169507223734896838191153385534315080094642003467475286618217312547673346226498028840638811785232220644505172823048049307295528350268297896090594447507642417485988236264812029344626916771360739946794464374533468197208378649479855153158105096840241159208774898830947929245674268993055394113341496756968655275403377146364525078276300487421541209221778977334 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x54387 : Deny 1000000000000000000 13 bp13x54387 := by
  apply split bp13x54387 2
  · rw [show leftB bp13x54387 2=bp13x54388 by funext i; fin_cases i <;> rfl]; exact p13x54388
  · rw [show rightB bp13x54387 2=bp13x54645 by funext i; fin_cases i <;> rfl]; exact p13x54645
private def bp13x55802 : B := ![⟨41,some 45⟩,⟨190,none⟩,⟨22,some 45⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x55802 : Deny 1000000000000000000 13 bp13x55802 :=
  sound (by decide) (by decide) 24 298641230110354750903004084424508693426642496754076834326848377773001676030387514543761329652246714555871093539554410006262943133628018387571563167245730060569161657583309343159948381937765311712343533646245365296178506518736708562189877083647165615710104080371146436128201995078848840174080221726564896529379578766893098838943934919858714697880961637244609452262162554992325560054117642063677753482406976582170888265681745240541284362720161565976795 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x54386 : Deny 1000000000000000000 13 bp13x54386 := by
  apply split bp13x54386 0
  · rw [show leftB bp13x54386 0=bp13x54387 by funext i; fin_cases i <;> rfl]; exact p13x54387
  · rw [show rightB bp13x54386 0=bp13x55802 by funext i; fin_cases i <;> rfl]; exact p13x55802
set_option maxRecDepth 100000 in
private theorem p13x53528 : Deny 1000000000000000000 13 bp13x53528 := by
  apply split bp13x53528 1
  · rw [show leftB bp13x53528 1=bp13x53529 by funext i; fin_cases i <;> rfl]; exact p13x53529
  · rw [show rightB bp13x53528 1=bp13x54386 by funext i; fin_cases i <;> rfl]; exact p13x54386
private def bp13x56559 : B := ![⟨37,some 45⟩,⟨94,none⟩,⟨46,none⟩]
private def bp13x56560 : B := ![⟨37,some 45⟩,⟨94,some 189⟩,⟨46,none⟩]
private def bp13x56561 : B := ![⟨37,some 40⟩,⟨94,some 189⟩,⟨46,none⟩]
private def bp13x56562 : B := ![⟨37,some 40⟩,⟨94,some 189⟩,⟨46,some 93⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x56562 : Deny 1000000000000000000 13 bp13x56562 :=
  sound (by decide) (by decide) 18 231226005895744394147942868320514286707804102233246539636894731908759121201145650606873368595313046855359041028343312274435064176329497435723510046909409051103868255172534772989088610755531429123838719053213594549323220143810046435840114745141558642709398314791047307194713178702847083201181760145267706599120250124671813702631857710375366598096523022177806803656660465405572588557502914690352195031595594297121000187608639597972936164800071974889791311729698947146621364771009711847561597884859132633444894258376332219981170358470 (tail:=0) (by decide +kernel)
private def bp13x57453 : B := ![⟨37,some 40⟩,⟨94,some 189⟩,⟨94,none⟩]
private def bp13x57454 : B := ![⟨37,some 40⟩,⟨94,some 125⟩,⟨94,none⟩]
private def bp13x57455 : B := ![⟨37,some 38⟩,⟨94,some 125⟩,⟨94,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x57455 : Deny 1000000000000000000 13 bp13x57455 :=
  sound (by decide) (by decide) 29 3838703351980962179899633698281470713164578776720665063322509791717731456200423999513391532409076346667441726582570581759725992997295042252393686906643497833398098372693497353189621062830278508385670273449260341258936075307340925280385204818256006093080478428331585985871688304601035358922321169723722708423191227509045191453518930421466544921932163055023410017894782580104232519427142741867700287709415858371636956594951362016458221543413995588311709488325670773298845832535285931673486345854599704474092213475596214340404019500666144902854031410379 (tail:=0) (by decide +kernel)
private def bp13x58378 : B := ![⟨39,some 40⟩,⟨94,some 125⟩,⟨94,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x58378 : Deny 1000000000000000000 13 bp13x58378 :=
  sound (by decide) (by decide) 17 7007133691490881614778662207367454597981146897609021383316209563780363643759713492343882759780221401343275050134500159664119626222977116809767729087173751119060281425424532298886927795721366910559181492853400611846413555985986619340346468218490627749894251936221849558593979 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x57454 : Deny 1000000000000000000 13 bp13x57454 := by
  apply split bp13x57454 0
  · rw [show leftB bp13x57454 0=bp13x57455 by funext i; fin_cases i <;> rfl]; exact p13x57455
  · rw [show rightB bp13x57454 0=bp13x58378 by funext i; fin_cases i <;> rfl]; exact p13x58378
private def bp13x58845 : B := ![⟨37,some 40⟩,⟨126,some 189⟩,⟨94,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x58845 : Deny 1000000000000000000 13 bp13x58845 :=
  sound (by decide) (by decide) 19 66665667694606772813684514130783569656280390059171011630265584396702575167908117903889173950000439095552931289602165445338447277471622747341948740069758049711410933453120484985701483459543462065396291081768866794004172307364333517534476353730717268379061489433013101527029648834601609284375084611717735738093613217584673208321906845033930779451386329136291981841711741792282720118956525 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x57453 : Deny 1000000000000000000 13 bp13x57453 := by
  apply split bp13x57453 1
  · rw [show leftB bp13x57453 1=bp13x57454 by funext i; fin_cases i <;> rfl]; exact p13x57454
  · rw [show rightB bp13x57453 1=bp13x58845 by funext i; fin_cases i <;> rfl]; exact p13x58845
set_option maxRecDepth 100000 in
private theorem p13x56561 : Deny 1000000000000000000 13 bp13x56561 := by
  apply split bp13x56561 2
  · rw [show leftB bp13x56561 2=bp13x56562 by funext i; fin_cases i <;> rfl]; exact p13x56562
  · rw [show rightB bp13x56561 2=bp13x57453 by funext i; fin_cases i <;> rfl]; exact p13x57453
private def bp13x59498 : B := ![⟨41,some 45⟩,⟨94,some 189⟩,⟨46,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x59498 : Deny 1000000000000000000 13 bp13x59498 :=
  sound (by decide) (by decide) 17 7732051927169858000240460612298007086640952891408293868958117757630203415812975919191753702917687433145462169278230401411135556320189943408740740432813626324157331223621362660474828669512881088160429307701619466562462496885394733432072073639282044909773760729719663228492541898338511229376956012782774030470875 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x56560 : Deny 1000000000000000000 13 bp13x56560 := by
  apply split bp13x56560 0
  · rw [show leftB bp13x56560 0=bp13x56561 by funext i; fin_cases i <;> rfl]; exact p13x56561
  · rw [show rightB bp13x56560 0=bp13x59498 by funext i; fin_cases i <;> rfl]; exact p13x59498
private def bp13x60025 : B := ![⟨37,some 45⟩,⟨190,none⟩,⟨46,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x60025 : Deny 1000000000000000000 13 bp13x60025 :=
  sound (by decide) (by decide) 21 5314153867114288721022122590120298675320431024481772263810399895134534462273308575549134880444818436348894851024071127940864420983059890683059630943700202774925059173219325619733325273542561201225123833531645477646823187470517389569459729427505128475818823537980661370101180160599296245450113902664215498465471417439743210197636426821349935485893963053812653066255887789207882410230971361002337067755573548392492131605656304786009287733126134637 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x56559 : Deny 1000000000000000000 13 bp13x56559 := by
  apply split bp13x56559 1
  · rw [show leftB bp13x56559 1=bp13x56560 by funext i; fin_cases i <;> rfl]; exact p13x56560
  · rw [show rightB bp13x56559 1=bp13x60025 by funext i; fin_cases i <;> rfl]; exact p13x60025
set_option maxRecDepth 100000 in
private theorem p13x53527 : Deny 1000000000000000000 13 bp13x53527 := by
  apply split bp13x53527 2
  · rw [show leftB bp13x53527 2=bp13x53528 by funext i; fin_cases i <;> rfl]; exact p13x53528
  · rw [show rightB bp13x53527 2=bp13x56559 by funext i; fin_cases i <;> rfl]; exact p13x56559
set_option maxRecDepth 100000 in
private theorem p13x23355 : Deny 1000000000000000000 13 bp13x23355 := by
  apply split bp13x23355 0
  · rw [show leftB bp13x23355 0=bp13x23356 by funext i; fin_cases i <;> rfl]; exact p13x23356
  · rw [show rightB bp13x23355 0=bp13x53527 by funext i; fin_cases i <;> rfl]; exact p13x53527
set_option maxRecDepth 100000 in
private theorem p13x20343 : Deny 1000000000000000000 13 bp13x20343 := by
  apply split bp13x20343 1
  · rw [show leftB bp13x20343 1=bp13x20344 by funext i; fin_cases i <;> rfl]; exact p13x20344
  · rw [show rightB bp13x20343 1=bp13x23355 by funext i; fin_cases i <;> rfl]; exact p13x23355
set_option maxRecDepth 100000 in
private theorem p13x19989 : Deny 1000000000000000000 13 bp13x19989 := by
  apply split bp13x19989 2
  · rw [show leftB bp13x19989 2=bp13x19990 by funext i; fin_cases i <;> rfl]; exact p13x19990
  · rw [show rightB bp13x19989 2=bp13x20343 by funext i; fin_cases i <;> rfl]; exact p13x20343
set_option maxRecDepth 100000 in
private theorem p13x19987 : Deny 1000000000000000000 13 bp13x19987 := by
  apply split bp13x19987 1
  · rw [show leftB bp13x19987 1=bp13x19988 by funext i; fin_cases i <;> rfl]; exact p13x19988
  · rw [show rightB bp13x19987 1=bp13x19989 by funext i; fin_cases i <;> rfl]; exact p13x19989
set_option maxRecDepth 100000 in
private theorem p13x19985 : Deny 1000000000000000000 13 bp13x19985 := by
  apply split bp13x19985 0
  · rw [show leftB bp13x19985 0=bp13x19986 by funext i; fin_cases i <;> rfl]; exact p13x19986
  · rw [show rightB bp13x19985 0=bp13x19987 by funext i; fin_cases i <;> rfl]; exact p13x19987
set_option maxRecDepth 100000 in
private theorem p13x19983 : Deny 1000000000000000000 13 bp13x19983 := by
  apply split bp13x19983 2
  · rw [show leftB bp13x19983 2=bp13x19984 by funext i; fin_cases i <;> rfl]; exact p13x19984
  · rw [show rightB bp13x19983 2=bp13x19985 by funext i; fin_cases i <;> rfl]; exact p13x19985
private def bp13x60780 : B := ![⟨46,none⟩,⟨22,none⟩,⟨4,none⟩]
private def bp13x60781 : B := ![⟨46,none⟩,⟨22,none⟩,⟨4,some 9⟩]
private def bp13x60782 : B := ![⟨46,none⟩,⟨22,some 45⟩,⟨4,some 9⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x60782 : Deny 1000000000000000000 13 bp13x60782 :=
  sound (by decide) (by decide) 29 2653812024591663638374654048073387903780077403303253380012930564515755982451236370375483284102787624271754643434362411385379937662967495028777763395311176548784339330882294574756374271278228367186899182046063391038279474470729211205246015103583268723409827388909237773716869400292615170232881 (tail:=0) (by decide +kernel)
private def bp13x61277 : B := ![⟨46,none⟩,⟨46,none⟩,⟨4,some 9⟩]
private def bp13x61278 : B := ![⟨46,some 93⟩,⟨46,none⟩,⟨4,some 9⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x61278 : Deny 1000000000000000000 13 bp13x61278 :=
  sound (by decide) (by decide) 34 116040525606492479720402083880011108600017949116800604681577940444835665371957351453529684700097199510956509161250533220055513017502947905251138879566731096162434558951883133974599124331463857525514065149572060515338711397361776800206467778421119127409107790275154693895274650923771787749970921560552230862754183726977207136699030443410451234186974235014942178749564721915990714321978731393963812191647042325474235372388600043480376354998348140110481348289335633772639829972413146586733220243643282888208915 (tail:=0) (by decide +kernel)
private def bp13x62131 : B := ![⟨94,none⟩,⟨46,none⟩,⟨4,some 9⟩]
private def bp13x62132 : B := ![⟨94,none⟩,⟨46,none⟩,⟨4,some 5⟩]
private def bp13x62133 : B := ![⟨94,none⟩,⟨46,some 93⟩,⟨4,some 5⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x62133 : Deny 1000000000000000000 13 bp13x62133 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x62134 : B := ![⟨94,none⟩,⟨94,none⟩,⟨4,some 5⟩]
private def bp13x62135 : B := ![⟨94,some 189⟩,⟨94,none⟩,⟨4,some 5⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x62135 : Deny 1000000000000000000 13 bp13x62135 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x62136 : B := ![⟨190,none⟩,⟨94,none⟩,⟨4,some 5⟩]
private def bp13x62137 : B := ![⟨190,none⟩,⟨94,none⟩,⟨4,some 4⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x62137 : Deny 1000000000000000000 13 bp13x62137 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x62138 : B := ![⟨190,none⟩,⟨94,none⟩,⟨5,some 5⟩]
private def bp13x62139 : B := ![⟨190,none⟩,⟨94,some 189⟩,⟨5,some 5⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x62139 : Deny 1000000000000000000 13 bp13x62139 :=
  sound (by decide) (by decide) 37 17073459452193733591332980714542669232346285415708857925922430560655262163929344617607001417374981304049819621889357882872631142755254170481194828853186341900421370904448366050446173846966286197080174121560575393356908360881240007777549330875121674293508165012893782742317332104981220519068154732225546866095900125896546816492402174005433519622785843600208646594123947891200020461317632231720310861157485122827521925692860722922706833066408113755761405302327131603755705312564139979455429214648980643188089612522943958849572822398203300859260409360395929965615262627528822643419536395339567929661365268128341945559384380045253465544994648059956199723322192656306280091397540853915937 (tail:=0) (by decide +kernel)
private def bp13x63284 : B := ![⟨190,none⟩,⟨190,none⟩,⟨5,some 5⟩]
private def bp13x63285 : B := ![⟨190,some 381⟩,⟨190,none⟩,⟨5,some 5⟩]
private def bp13x63286 : B := ![⟨190,some 253⟩,⟨190,none⟩,⟨5,some 5⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x63286 : Deny 1000000000000000000 13 bp13x63286 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x63287 : B := ![⟨254,some 381⟩,⟨190,none⟩,⟨5,some 5⟩]
private def bp13x63288 : B := ![⟨254,some 381⟩,⟨190,some 381⟩,⟨5,some 5⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x63288 : Deny 1000000000000000000 13 bp13x63288 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x63289 : B := ![⟨254,some 381⟩,⟨382,none⟩,⟨5,some 5⟩]
private def bp13x63290 : B := ![⟨254,some 381⟩,⟨382,some 765⟩,⟨5,some 5⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x63290 : Deny 1000000000000000000 13 bp13x63290 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x63291 : B := ![⟨254,some 381⟩,⟨766,none⟩,⟨5,some 5⟩]
private def bp13x63292 : B := ![⟨254,some 304⟩,⟨766,none⟩,⟨5,some 5⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x63292 : Deny 1000000000000000000 13 bp13x63292 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x63293 : B := ![⟨305,some 381⟩,⟨766,none⟩,⟨5,some 5⟩]
private def bp13x63294 : B := ![⟨305,some 381⟩,⟨766,some 1533⟩,⟨5,some 5⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x63294 : Deny 1000000000000000000 13 bp13x63294 :=
  sound (by decide) (by decide) 19 32462740188352465544210133721322458485996407583689538178223994892908442530204214564458115446518598476479640960023262646747770418037089970446625 (tail:=0) (by decide +kernel)
private def bp13x63541 : B := ![⟨305,some 381⟩,⟨1534,none⟩,⟨5,some 5⟩]
private def bp13x63542 : B := ![⟨305,some 338⟩,⟨1534,none⟩,⟨5,some 5⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x63542 : Deny 1000000000000000000 13 bp13x63542 :=
  sound (by decide) (by decide) 31 33485127230147713030987312958627635002480491919887041448703638472258405073265502367829135536206044227399751684854753265497834166295601346680369938559657709130602973965505416000396562988079372574734387133607547018065208095906149394126583029014669926452466810744900979257392449187156048030204043526346513012092207420440996830845299907296629848766228042384914 (tail:=0) (by decide +kernel)
private def bp13x64145 : B := ![⟨339,some 381⟩,⟨1534,none⟩,⟨5,some 5⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x64145 : Deny 1000000000000000000 13 bp13x64145 :=
  sound (by decide) (by decide) 21 76410447188594866503082678046747378929787328898524555398219298751338525739475758504889147821038525278307360286037969454989142739448044923999780525563535814516851693519252486476134412611494253349045534440901895877430098370806158439951601355996437295746133602545801780027760851881124242691677654043746126812751932357730440007565532628370185815311260806870341618871737293453962680665067346735847330062216850096207619107693109569972090196538455349230079330406 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x63541 : Deny 1000000000000000000 13 bp13x63541 := by
  apply split bp13x63541 0
  · rw [show leftB bp13x63541 0=bp13x63542 by funext i; fin_cases i <;> rfl]; exact p13x63542
  · rw [show rightB bp13x63541 0=bp13x64145 by funext i; fin_cases i <;> rfl]; exact p13x64145
set_option maxRecDepth 100000 in
private theorem p13x63293 : Deny 1000000000000000000 13 bp13x63293 := by
  apply split bp13x63293 1
  · rw [show leftB bp13x63293 1=bp13x63294 by funext i; fin_cases i <;> rfl]; exact p13x63294
  · rw [show rightB bp13x63293 1=bp13x63541 by funext i; fin_cases i <;> rfl]; exact p13x63541
set_option maxRecDepth 100000 in
private theorem p13x63291 : Deny 1000000000000000000 13 bp13x63291 := by
  apply split bp13x63291 0
  · rw [show leftB bp13x63291 0=bp13x63292 by funext i; fin_cases i <;> rfl]; exact p13x63292
  · rw [show rightB bp13x63291 0=bp13x63293 by funext i; fin_cases i <;> rfl]; exact p13x63293
set_option maxRecDepth 100000 in
private theorem p13x63289 : Deny 1000000000000000000 13 bp13x63289 := by
  apply split bp13x63289 1
  · rw [show leftB bp13x63289 1=bp13x63290 by funext i; fin_cases i <;> rfl]; exact p13x63290
  · rw [show rightB bp13x63289 1=bp13x63291 by funext i; fin_cases i <;> rfl]; exact p13x63291
set_option maxRecDepth 100000 in
private theorem p13x63287 : Deny 1000000000000000000 13 bp13x63287 := by
  apply split bp13x63287 1
  · rw [show leftB bp13x63287 1=bp13x63288 by funext i; fin_cases i <;> rfl]; exact p13x63288
  · rw [show rightB bp13x63287 1=bp13x63289 by funext i; fin_cases i <;> rfl]; exact p13x63289
set_option maxRecDepth 100000 in
private theorem p13x63285 : Deny 1000000000000000000 13 bp13x63285 := by
  apply split bp13x63285 0
  · rw [show leftB bp13x63285 0=bp13x63286 by funext i; fin_cases i <;> rfl]; exact p13x63286
  · rw [show rightB bp13x63285 0=bp13x63287 by funext i; fin_cases i <;> rfl]; exact p13x63287
private def bp13x64912 : B := ![⟨382,none⟩,⟨190,none⟩,⟨5,some 5⟩]
private def bp13x64913 : B := ![⟨382,none⟩,⟨190,some 381⟩,⟨5,some 5⟩]
private def bp13x64914 : B := ![⟨382,some 765⟩,⟨190,some 381⟩,⟨5,some 5⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x64914 : Deny 1000000000000000000 13 bp13x64914 :=
  sound (by decide) (by decide) 19 21482340637042812044295909864159066356804914443673901735539778275000326748606717090314717192457941391640015962654585757263111819445326667145667700184025751567893161446420379546380839987667099354148269017397920067286505119217869690710058628669892072489321393566674969437479391578233192848755192339671846395291186280670621386909768259773294762527691276645372319111304705653588268615897329725566612822040166748147405889778398949323055748858639323107806382203510989774505168117814063581052389885495187710952978 (tail:=0) (by decide +kernel)
private def bp13x65765 : B := ![⟨766,none⟩,⟨190,some 381⟩,⟨5,some 5⟩]
private def bp13x65766 : B := ![⟨766,none⟩,⟨190,some 253⟩,⟨5,some 5⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x65766 : Deny 1000000000000000000 13 bp13x65766 :=
  sound (by decide) (by decide) 20 3493648298822839476399117313542143651352370992785919312830977981377624587278402729590501346450076652472217365305917642099810513315155018015246367896181991400755410507713914106178679102736635757692059439253373661963240914205328008854425059765855051976303600742833425804355761372633890926059295518136640994710466063124681953725719143504194793164576365405471989033963128978213147764054986020699420015349134541049143321813405512177416300286432073414156878725864566888622245919977194397207327782263000827513057368925167413999534956442705924971759082593997326142822662973384483224817980611904501613403759935754792787935553434689046432534632008360796041670893861 (tail:=0) (by decide +kernel)
private def bp13x66867 : B := ![⟨766,none⟩,⟨254,some 381⟩,⟨5,some 5⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x66867 : Deny 1000000000000000000 13 bp13x66867 :=
  sound (by decide) (by decide) 18 2295945438110976939172206536990629814027424895448754249678591532712159314977821368920861747443890977327083701824906829399715662239591769647454879305426468315395834526405371425067337112696009754198026522097918974943065489047788465643076003417 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x65765 : Deny 1000000000000000000 13 bp13x65765 := by
  apply split bp13x65765 1
  · rw [show leftB bp13x65765 1=bp13x65766 by funext i; fin_cases i <;> rfl]; exact p13x65766
  · rw [show rightB bp13x65765 1=bp13x66867 by funext i; fin_cases i <;> rfl]; exact p13x66867
set_option maxRecDepth 100000 in
private theorem p13x64913 : Deny 1000000000000000000 13 bp13x64913 := by
  apply split bp13x64913 0
  · rw [show leftB bp13x64913 0=bp13x64914 by funext i; fin_cases i <;> rfl]; exact p13x64914
  · rw [show rightB bp13x64913 0=bp13x65765 by funext i; fin_cases i <;> rfl]; exact p13x65765
private def bp13x67280 : B := ![⟨382,none⟩,⟨382,none⟩,⟨5,some 5⟩]
private def bp13x67281 : B := ![⟨382,some 765⟩,⟨382,none⟩,⟨5,some 5⟩]
private def bp13x67282 : B := ![⟨382,some 509⟩,⟨382,none⟩,⟨5,some 5⟩]
private def bp13x67283 : B := ![⟨382,some 509⟩,⟨382,some 765⟩,⟨5,some 5⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x67283 : Deny 1000000000000000000 13 bp13x67283 :=
  sound (by decide) (by decide) 18 17791817578908263884132159897779858270520509157312037147871385388178688469033124381438824914478132428034128184002949957157668245724739197503106849744892824730282159126461203044834839813473360303539456816166856497585587209332787792327025992106911470235186611226003523009649490698510153515416931460641441696000839555236800013834946486222828164851993951011722336592182089573075858431752091092079257336438723191349347236970125504256986603882632422297152323867491396533108139346525457495509101840025578471287492427782731514608995537971523717864283085386864466998725545588671590613124355082451868025990 (tail:=0) (by decide +kernel)
private def bp13x68284 : B := ![⟨382,some 509⟩,⟨766,none⟩,⟨5,some 5⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x68284 : Deny 1000000000000000000 13 bp13x68284 :=
  sound (by decide) (by decide) 19 118696243452023967754451307464763786114488493100999981064625383397634822449906161949620205331854005212560142990823080240843241626740720722230019661044317401846448550711361052171228429092123439104988915900328873538914807696075503262332463606790664668977389166412756945064061947399852635144242985546245813774052934965193743222753628292710 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x67282 : Deny 1000000000000000000 13 bp13x67282 := by
  apply split bp13x67282 1
  · rw [show leftB bp13x67282 1=bp13x67283 by funext i; fin_cases i <;> rfl]; exact p13x67283
  · rw [show rightB bp13x67282 1=bp13x68284 by funext i; fin_cases i <;> rfl]; exact p13x68284
private def bp13x68853 : B := ![⟨510,some 765⟩,⟨382,none⟩,⟨5,some 5⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x68853 : Deny 1000000000000000000 13 bp13x68853 :=
  sound (by decide) (by decide) 18 980503103602310237615364365513373757267578165532246102090408155917294254285200194168766777594557529609959999980965443488542059581553211598626858275741336183390846399458849226001317018685057610776668563793523074274518848076603647713285549913537437936640469106047397230396409416635197018 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x67281 : Deny 1000000000000000000 13 bp13x67281 := by
  apply split bp13x67281 0
  · rw [show leftB bp13x67281 0=bp13x67282 by funext i; fin_cases i <;> rfl]; exact p13x67282
  · rw [show rightB bp13x67281 0=bp13x68853 by funext i; fin_cases i <;> rfl]; exact p13x68853
private def bp13x69340 : B := ![⟨766,none⟩,⟨382,none⟩,⟨5,some 5⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x69340 : Deny 1000000000000000000 13 bp13x69340 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x67280 : Deny 1000000000000000000 13 bp13x67280 := by
  apply split bp13x67280 0
  · rw [show leftB bp13x67280 0=bp13x67281 by funext i; fin_cases i <;> rfl]; exact p13x67281
  · rw [show rightB bp13x67280 0=bp13x69340 by funext i; fin_cases i <;> rfl]; exact p13x69340
set_option maxRecDepth 100000 in
private theorem p13x64912 : Deny 1000000000000000000 13 bp13x64912 := by
  apply split bp13x64912 1
  · rw [show leftB bp13x64912 1=bp13x64913 by funext i; fin_cases i <;> rfl]; exact p13x64913
  · rw [show rightB bp13x64912 1=bp13x67280 by funext i; fin_cases i <;> rfl]; exact p13x67280
set_option maxRecDepth 100000 in
private theorem p13x63284 : Deny 1000000000000000000 13 bp13x63284 := by
  apply split bp13x63284 0
  · rw [show leftB bp13x63284 0=bp13x63285 by funext i; fin_cases i <;> rfl]; exact p13x63285
  · rw [show rightB bp13x63284 0=bp13x64912 by funext i; fin_cases i <;> rfl]; exact p13x64912
set_option maxRecDepth 100000 in
private theorem p13x62138 : Deny 1000000000000000000 13 bp13x62138 := by
  apply split bp13x62138 1
  · rw [show leftB bp13x62138 1=bp13x62139 by funext i; fin_cases i <;> rfl]; exact p13x62139
  · rw [show rightB bp13x62138 1=bp13x63284 by funext i; fin_cases i <;> rfl]; exact p13x63284
set_option maxRecDepth 100000 in
private theorem p13x62136 : Deny 1000000000000000000 13 bp13x62136 := by
  apply split bp13x62136 2
  · rw [show leftB bp13x62136 2=bp13x62137 by funext i; fin_cases i <;> rfl]; exact p13x62137
  · rw [show rightB bp13x62136 2=bp13x62138 by funext i; fin_cases i <;> rfl]; exact p13x62138
set_option maxRecDepth 100000 in
private theorem p13x62134 : Deny 1000000000000000000 13 bp13x62134 := by
  apply split bp13x62134 0
  · rw [show leftB bp13x62134 0=bp13x62135 by funext i; fin_cases i <;> rfl]; exact p13x62135
  · rw [show rightB bp13x62134 0=bp13x62136 by funext i; fin_cases i <;> rfl]; exact p13x62136
set_option maxRecDepth 100000 in
private theorem p13x62132 : Deny 1000000000000000000 13 bp13x62132 := by
  apply split bp13x62132 1
  · rw [show leftB bp13x62132 1=bp13x62133 by funext i; fin_cases i <;> rfl]; exact p13x62133
  · rw [show rightB bp13x62132 1=bp13x62134 by funext i; fin_cases i <;> rfl]; exact p13x62134
private def bp13x69341 : B := ![⟨94,none⟩,⟨46,none⟩,⟨6,some 9⟩]
private def bp13x69342 : B := ![⟨94,none⟩,⟨46,some 93⟩,⟨6,some 9⟩]
private def bp13x69343 : B := ![⟨94,some 189⟩,⟨46,some 93⟩,⟨6,some 9⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x69343 : Deny 1000000000000000000 13 bp13x69343 :=
  sound (by decide) (by decide) 17 82006631185959996507991188156039114900236562275458857259791526409903766397889022812405373630735035957451742613371928177437193593842165526279330131740372090944634030995632656722379462067853976814927939935882293872588074965393399520089201583871522713199799632688031238909385617989162341747812564012548409159968534323576932865265140835 (tail:=0) (by decide +kernel)
private def bp13x69904 : B := ![⟨190,none⟩,⟨46,some 93⟩,⟨6,some 9⟩]
private def bp13x69905 : B := ![⟨190,none⟩,⟨46,some 93⟩,⟨6,some 7⟩]
private def bp13x69906 : B := ![⟨190,none⟩,⟨46,some 61⟩,⟨6,some 7⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x69906 : Deny 1000000000000000000 13 bp13x69906 :=
  sound (by decide) (by decide) 28 128448488122203624142400513221593148938117217400736883487357706194040384809676640123983973443365768943365203012083775758260319863255561059153435688491260132415162668426255956719495714097891918038005483701095648522948856539470899805538711674542971413422978123319601 (tail:=0) (by decide +kernel)
private def bp13x70353 : B := ![⟨190,none⟩,⟨62,some 93⟩,⟨6,some 7⟩]
private def bp13x70354 : B := ![⟨190,some 381⟩,⟨62,some 93⟩,⟨6,some 7⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x70354 : Deny 1000000000000000000 13 bp13x70354 :=
  sound (by decide) (by decide) 16 5160566602100732936637903514197350430777453410612860246004054472641947946113311128323767987790333220918081010932080239833275017388841163839153633161539919604818145957958073263203 (tail:=0) (by decide +kernel)
private def bp13x70659 : B := ![⟨382,none⟩,⟨62,some 93⟩,⟨6,some 7⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x70659 : Deny 1000000000000000000 13 bp13x70659 :=
  sound (by decide) (by decide) 38 343036728600873951702420864844132925461876901014179606653304006646090726746152679728419030091164233699548300632242899686746978748795844677417193729586219382581395617050948699049564061916344274562879497075875209719670411554305886453254944572080309206519546454358971998582760533721414323945713239263136959933434860071032953855082567088482687310760487112526313366929764548795001641736008555663008555694105343272456042320202299756897081161007910041466687380682651311455986067090476437577596272346585744801829179897034748549174392782374155652233199522590492681119533279139094117512492728612832930887209873514897491137575084618835337699196017139940232368491006115187675177068999962797553804524488434009896460571 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x70353 : Deny 1000000000000000000 13 bp13x70353 := by
  apply split bp13x70353 0
  · rw [show leftB bp13x70353 0=bp13x70354 by funext i; fin_cases i <;> rfl]; exact p13x70354
  · rw [show rightB bp13x70353 0=bp13x70659 by funext i; fin_cases i <;> rfl]; exact p13x70659
set_option maxRecDepth 100000 in
private theorem p13x69905 : Deny 1000000000000000000 13 bp13x69905 := by
  apply split bp13x69905 1
  · rw [show leftB bp13x69905 1=bp13x69906 by funext i; fin_cases i <;> rfl]; exact p13x69906
  · rw [show rightB bp13x69905 1=bp13x70353 by funext i; fin_cases i <;> rfl]; exact p13x70353
private def bp13x71842 : B := ![⟨190,none⟩,⟨46,some 93⟩,⟨8,some 9⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x71842 : Deny 1000000000000000000 13 bp13x71842 :=
  sound (by decide) (by decide) 18 9079860759345275284998901441647910525125255770926919954977885558308208301871733460025381721658072670061796792080506005641511871989908045176033225661597410634311779507224757619217353603053574672435880685660924725298991546717387359671449515692060816449504171115478815638 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x69904 : Deny 1000000000000000000 13 bp13x69904 := by
  apply split bp13x69904 2
  · rw [show leftB bp13x69904 2=bp13x69905 by funext i; fin_cases i <;> rfl]; exact p13x69905
  · rw [show rightB bp13x69904 2=bp13x71842 by funext i; fin_cases i <;> rfl]; exact p13x71842
set_option maxRecDepth 100000 in
private theorem p13x69342 : Deny 1000000000000000000 13 bp13x69342 := by
  apply split bp13x69342 0
  · rw [show leftB bp13x69342 0=bp13x69343 by funext i; fin_cases i <;> rfl]; exact p13x69343
  · rw [show rightB bp13x69342 0=bp13x69904 by funext i; fin_cases i <;> rfl]; exact p13x69904
private def bp13x72299 : B := ![⟨94,none⟩,⟨94,none⟩,⟨6,some 9⟩]
private def bp13x72300 : B := ![⟨94,some 189⟩,⟨94,none⟩,⟨6,some 9⟩]
private def bp13x72301 : B := ![⟨94,some 189⟩,⟨94,none⟩,⟨6,some 7⟩]
private def bp13x72302 : B := ![⟨94,some 125⟩,⟨94,none⟩,⟨6,some 7⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x72302 : Deny 1000000000000000000 13 bp13x72302 :=
  sound (by decide) (by decide) 28 44779077317187926129231317283389960323234678995002397143273741555608847496378008693641929719322875203112761138615035919014782813387293545256472001926248881999672779086399706679664331055628335837933140377620397343492403615505151787900340867284873411253368900001591757068108433702845080178361367969969272568640288121609756794249088348153162031863063594459997684205106 (tail:=0) (by decide +kernel)
private def bp13x72919 : B := ![⟨126,some 189⟩,⟨94,none⟩,⟨6,some 7⟩]
private def bp13x72920 : B := ![⟨126,some 189⟩,⟨94,some 189⟩,⟨6,some 7⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x72920 : Deny 1000000000000000000 13 bp13x72920 :=
  sound (by decide) (by decide) 16 18379373360616972991063075344365266969779761714694624141645500587617234008243100361917162101247117326147198518680677445374303235967970610754542095103204335329775202510823190508019294033706765654229470523620452364074230833691690297923093874644284578321541503075 (tail:=0) (by decide +kernel)
private def bp13x73361 : B := ![⟨126,some 189⟩,⟨190,none⟩,⟨6,some 7⟩]
private def bp13x73362 : B := ![⟨126,some 189⟩,⟨190,none⟩,⟨6,some 6⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x73362 : Deny 1000000000000000000 13 bp13x73362 :=
  sound (by decide) (by decide) 37 37698884543116884228855519806016078689499198717024631219163561184084966134520754730412018239355475625418403540310558738095987842331535149732331066299145264409397911543823834425391172183154846608920195336762931327565643169298780530613896577064043119613367822611284963197401661518184505370792255409214690043417692436426860409568199963423960204947689613703127141852526244711165575505314043632866045177305294295758308344325492712677960243238385126433985481199168298150922089465681563128188385243449045106946020868496288332800321566685851087458703566793924666394751353864970628078145470762589522519330959510477753928602152295113429664127480025907291258689568576472087893754628759028589554212676929624491335037259605968006 (tail:=0) (by decide +kernel)
private def bp13x74561 : B := ![⟨126,some 189⟩,⟨190,none⟩,⟨7,some 7⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x74561 : Deny 1000000000000000000 13 bp13x74561 :=
  sound (by decide) (by decide) 15 54238327763703640579511351240057967164569577624627464136294 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x73361 : Deny 1000000000000000000 13 bp13x73361 := by
  apply split bp13x73361 2
  · rw [show leftB bp13x73361 2=bp13x73362 by funext i; fin_cases i <;> rfl]; exact p13x73362
  · rw [show rightB bp13x73361 2=bp13x74561 by funext i; fin_cases i <;> rfl]; exact p13x74561
set_option maxRecDepth 100000 in
private theorem p13x72919 : Deny 1000000000000000000 13 bp13x72919 := by
  apply split bp13x72919 1
  · rw [show leftB bp13x72919 1=bp13x72920 by funext i; fin_cases i <;> rfl]; exact p13x72920
  · rw [show rightB bp13x72919 1=bp13x73361 by funext i; fin_cases i <;> rfl]; exact p13x73361
set_option maxRecDepth 100000 in
private theorem p13x72301 : Deny 1000000000000000000 13 bp13x72301 := by
  apply split bp13x72301 0
  · rw [show leftB bp13x72301 0=bp13x72302 by funext i; fin_cases i <;> rfl]; exact p13x72302
  · rw [show rightB bp13x72301 0=bp13x72919 by funext i; fin_cases i <;> rfl]; exact p13x72919
private def bp13x74670 : B := ![⟨94,some 189⟩,⟨94,none⟩,⟨8,some 9⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x74670 : Deny 1000000000000000000 13 bp13x74670 :=
  sound (by decide) (by decide) 17 2543816857440193528110982317763799108614372670839982026233654516630095900473941675360731836802162241003681282943222621525023887802810351670313325307505029936271936626272284994001643933423419182306297493589673453188367017535322461055850236313306768780822793647619007610871170204296868784693743412346587866508873272130311865486240416807552539043998289754102359318356841 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x72300 : Deny 1000000000000000000 13 bp13x72300 := by
  apply split bp13x72300 2
  · rw [show leftB bp13x72300 2=bp13x72301 by funext i; fin_cases i <;> rfl]; exact p13x72301
  · rw [show rightB bp13x72300 2=bp13x74670 by funext i; fin_cases i <;> rfl]; exact p13x74670
private def bp13x75291 : B := ![⟨190,none⟩,⟨94,none⟩,⟨6,some 9⟩]
private def bp13x75292 : B := ![⟨190,none⟩,⟨94,none⟩,⟨6,some 7⟩]
private def bp13x75293 : B := ![⟨190,none⟩,⟨94,some 189⟩,⟨6,some 7⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x75293 : Deny 1000000000000000000 13 bp13x75293 :=
  sound (by decide) (by decide) 19 19819660261771438585351581248789272750218084159117529433488094825331227861270768683230551721429271125451279958159849842964362721461086319653385051159214110958926865737115487895436761224163193603166183833844157326541104850149364692752539617718542592236533822377459176860175974161982636170981354003452923508120403977756433153866405118895318757850074659537647931930488548537940815243938436930670116222252879975748901561958074154262826861107421813150752435865223208471909761499439889238798009315317259732446759557328389133892622061778641160474231917 (tail:=0) (by decide +kernel)
private def bp13x76212 : B := ![⟨190,none⟩,⟨190,none⟩,⟨6,some 7⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x76212 : Deny 1000000000000000000 13 bp13x76212 :=
  sound (by decide) (by decide) 19 1926324456100525370392697836682502329700508962658394099230896352616928155183026921284281287694573317562269956856689811858641092317689868602907227828618700634220189 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x75292 : Deny 1000000000000000000 13 bp13x75292 := by
  apply split bp13x75292 1
  · rw [show leftB bp13x75292 1=bp13x75293 by funext i; fin_cases i <;> rfl]; exact p13x75293
  · rw [show rightB bp13x75292 1=bp13x76212 by funext i; fin_cases i <;> rfl]; exact p13x76212
private def bp13x76495 : B := ![⟨190,none⟩,⟨94,none⟩,⟨8,some 9⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x76495 : Deny 1000000000000000000 13 bp13x76495 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x75291 : Deny 1000000000000000000 13 bp13x75291 := by
  apply split bp13x75291 2
  · rw [show leftB bp13x75291 2=bp13x75292 by funext i; fin_cases i <;> rfl]; exact p13x75292
  · rw [show rightB bp13x75291 2=bp13x76495 by funext i; fin_cases i <;> rfl]; exact p13x76495
set_option maxRecDepth 100000 in
private theorem p13x72299 : Deny 1000000000000000000 13 bp13x72299 := by
  apply split bp13x72299 0
  · rw [show leftB bp13x72299 0=bp13x72300 by funext i; fin_cases i <;> rfl]; exact p13x72300
  · rw [show rightB bp13x72299 0=bp13x75291 by funext i; fin_cases i <;> rfl]; exact p13x75291
set_option maxRecDepth 100000 in
private theorem p13x69341 : Deny 1000000000000000000 13 bp13x69341 := by
  apply split bp13x69341 1
  · rw [show leftB bp13x69341 1=bp13x69342 by funext i; fin_cases i <;> rfl]; exact p13x69342
  · rw [show rightB bp13x69341 1=bp13x72299 by funext i; fin_cases i <;> rfl]; exact p13x72299
set_option maxRecDepth 100000 in
private theorem p13x62131 : Deny 1000000000000000000 13 bp13x62131 := by
  apply split bp13x62131 2
  · rw [show leftB bp13x62131 2=bp13x62132 by funext i; fin_cases i <;> rfl]; exact p13x62132
  · rw [show rightB bp13x62131 2=bp13x69341 by funext i; fin_cases i <;> rfl]; exact p13x69341
set_option maxRecDepth 100000 in
private theorem p13x61277 : Deny 1000000000000000000 13 bp13x61277 := by
  apply split bp13x61277 0
  · rw [show leftB bp13x61277 0=bp13x61278 by funext i; fin_cases i <;> rfl]; exact p13x61278
  · rw [show rightB bp13x61277 0=bp13x62131 by funext i; fin_cases i <;> rfl]; exact p13x62131
set_option maxRecDepth 100000 in
private theorem p13x60781 : Deny 1000000000000000000 13 bp13x60781 := by
  apply split bp13x60781 1
  · rw [show leftB bp13x60781 1=bp13x60782 by funext i; fin_cases i <;> rfl]; exact p13x60782
  · rw [show rightB bp13x60781 1=bp13x61277 by funext i; fin_cases i <;> rfl]; exact p13x61277
private def bp13x76496 : B := ![⟨46,none⟩,⟨22,none⟩,⟨10,none⟩]
private def bp13x76497 : B := ![⟨46,none⟩,⟨22,some 45⟩,⟨10,none⟩]
private def bp13x76498 : B := ![⟨46,some 93⟩,⟨22,some 45⟩,⟨10,none⟩]
private def bp13x76499 : B := ![⟨46,some 93⟩,⟨22,some 45⟩,⟨10,some 21⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x76499 : Deny 1000000000000000000 13 bp13x76499 :=
  sound (by decide) (by decide) 18 1024004769508547271906701627081902699833501820899776809199964421026917188983418678535004463575957140236422685458 (tail:=0) (by decide +kernel)
private def bp13x76690 : B := ![⟨46,some 93⟩,⟨22,some 45⟩,⟨22,none⟩]
private def bp13x76691 : B := ![⟨46,some 93⟩,⟨22,some 29⟩,⟨22,none⟩]
private def bp13x76692 : B := ![⟨46,some 61⟩,⟨22,some 29⟩,⟨22,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x76692 : Deny 1000000000000000000 13 bp13x76692 :=
  sound (by decide) (by decide) 1 0 (tail:=0) (by decide +kernel)
private def bp13x76693 : B := ![⟨62,some 93⟩,⟨22,some 29⟩,⟨22,none⟩]
private def bp13x76694 : B := ![⟨62,some 93⟩,⟨22,some 29⟩,⟨22,some 45⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x76694 : Deny 1000000000000000000 13 bp13x76694 :=
  sound (by decide) (by decide) 4 801 (tail:=0) (by decide +kernel)
private def bp13x76701 : B := ![⟨62,some 93⟩,⟨22,some 29⟩,⟨46,none⟩]
private def bp13x76702 : B := ![⟨62,some 74⟩,⟨22,some 29⟩,⟨46,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x76702 : Deny 1000000000000000000 13 bp13x76702 :=
  sound (by decide) (by decide) 23 1883613822728218897787176159557408533193043447687147561688824383497438152496035155343765900158557503553530543677746 (tail:=0) (by decide +kernel)
private def bp13x76899 : B := ![⟨75,some 93⟩,⟨22,some 29⟩,⟨46,none⟩]
private def bp13x76900 : B := ![⟨75,some 93⟩,⟨22,some 25⟩,⟨46,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x76900 : Deny 1000000000000000000 13 bp13x76900 :=
  sound (by decide) (by decide) 30 4323171526163661425982361092683818003822969940113458647598534047293314780534345112384207707701999286076431905654277102414158582811008725164444839765922032434407330826337936816739930525922576482592924800809491336931340819 (tail:=0) (by decide +kernel)
private def bp13x77273 : B := ![⟨75,some 93⟩,⟨26,some 29⟩,⟨46,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x77273 : Deny 1000000000000000000 13 bp13x77273 :=
  sound (by decide) (by decide) 28 26475423287788987534995190831600108406211081979389338052980951826693782811840836720429748116100548792549736968686105471995823391484582677475381634189359219480340413382814558287655610269861424153059033052107564644548404557528166910543003040747441097156637172397077875771995265675118083822203069106188556478761257237321293255508852875835088517736051695900603716731559504408876168122350297610019175203580285138506731942585269653898860711533924887529197469041803285402429632901493363458306897566755642616820778031817694528179942657540292989515185078160979562789671054796859753850492058324318340804172183812689328135245075239 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x76899 : Deny 1000000000000000000 13 bp13x76899 := by
  apply split bp13x76899 1
  · rw [show leftB bp13x76899 1=bp13x76900 by funext i; fin_cases i <;> rfl]; exact p13x76900
  · rw [show rightB bp13x76899 1=bp13x77273 by funext i; fin_cases i <;> rfl]; exact p13x77273
set_option maxRecDepth 100000 in
private theorem p13x76701 : Deny 1000000000000000000 13 bp13x76701 := by
  apply split bp13x76701 0
  · rw [show leftB bp13x76701 0=bp13x76702 by funext i; fin_cases i <;> rfl]; exact p13x76702
  · rw [show rightB bp13x76701 0=bp13x76899 by funext i; fin_cases i <;> rfl]; exact p13x76899
set_option maxRecDepth 100000 in
private theorem p13x76693 : Deny 1000000000000000000 13 bp13x76693 := by
  apply split bp13x76693 2
  · rw [show leftB bp13x76693 2=bp13x76694 by funext i; fin_cases i <;> rfl]; exact p13x76694
  · rw [show rightB bp13x76693 2=bp13x76701 by funext i; fin_cases i <;> rfl]; exact p13x76701
set_option maxRecDepth 100000 in
private theorem p13x76691 : Deny 1000000000000000000 13 bp13x76691 := by
  apply split bp13x76691 0
  · rw [show leftB bp13x76691 0=bp13x76692 by funext i; fin_cases i <;> rfl]; exact p13x76692
  · rw [show rightB bp13x76691 0=bp13x76693 by funext i; fin_cases i <;> rfl]; exact p13x76693
private def bp13x78312 : B := ![⟨46,some 93⟩,⟨30,some 45⟩,⟨22,none⟩]
private def bp13x78313 : B := ![⟨46,some 61⟩,⟨30,some 45⟩,⟨22,none⟩]
private def bp13x78314 : B := ![⟨46,some 61⟩,⟨30,some 45⟩,⟨22,some 45⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x78314 : Deny 1000000000000000000 13 bp13x78314 :=
  sound (by decide) (by decide) 17 15568693496043350663500562 (tail:=0) (by decide +kernel)
private def bp13x78359 : B := ![⟨46,some 61⟩,⟨30,some 45⟩,⟨46,none⟩]
private def bp13x78360 : B := ![⟨46,some 61⟩,⟨30,some 36⟩,⟨46,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x78360 : Deny 1000000000000000000 13 bp13x78360 :=
  sound (by decide) (by decide) 27 14988238791383622348652587624562159336393615083255116031893556544694807891836828384896070555027055420396086878455169945599460368594440540560570680897295947103577388529397397253876603067131348658275684913 (tail:=0) (by decide +kernel)
private def bp13x78703 : B := ![⟨46,some 61⟩,⟨37,some 45⟩,⟨46,none⟩]
private def bp13x78704 : B := ![⟨46,some 52⟩,⟨37,some 45⟩,⟨46,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x78704 : Deny 1000000000000000000 13 bp13x78704 :=
  sound (by decide) (by decide) 31 4971754359127033834530342334206308714439052347224048204420474887233657221499217563475318734490103978163043295319158397799078182707980675222646588142079316876986646378095856655352381495149218855321405668234037081497526630992874861075 (tail:=0) (by decide +kernel)
private def bp13x79097 : B := ![⟨53,some 61⟩,⟨37,some 45⟩,⟨46,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x79097 : Deny 1000000000000000000 13 bp13x79097 :=
  sound (by decide) (by decide) 21 621424199343632706763377205718388956955577382728023200040326663616611133365426417174336296459020405204204611615595506783276456641396965174188575430195562081011840256153502541743233294502523020301133573939730112431599982551793482347142932748754548617436256349538524513588502047340722517576149388110244003621478983071150610908754703776739175639430888546598652519820106332053796100432472728365046256737012391139002885194238363120341931077468491150667321963017378006885742929575334447494218882049458166754611574350197559192236082107224692571661303566939586447804343263684980652105906387120822791809291538617651577309307789894641707114679841399591 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x78703 : Deny 1000000000000000000 13 bp13x78703 := by
  apply split bp13x78703 0
  · rw [show leftB bp13x78703 0=bp13x78704 by funext i; fin_cases i <;> rfl]; exact p13x78704
  · rw [show rightB bp13x78703 0=bp13x79097 by funext i; fin_cases i <;> rfl]; exact p13x79097
set_option maxRecDepth 100000 in
private theorem p13x78359 : Deny 1000000000000000000 13 bp13x78359 := by
  apply split bp13x78359 1
  · rw [show leftB bp13x78359 1=bp13x78360 by funext i; fin_cases i <;> rfl]; exact p13x78360
  · rw [show rightB bp13x78359 1=bp13x78703 by funext i; fin_cases i <;> rfl]; exact p13x78703
set_option maxRecDepth 100000 in
private theorem p13x78313 : Deny 1000000000000000000 13 bp13x78313 := by
  apply split bp13x78313 2
  · rw [show leftB bp13x78313 2=bp13x78314 by funext i; fin_cases i <;> rfl]; exact p13x78314
  · rw [show rightB bp13x78313 2=bp13x78359 by funext i; fin_cases i <;> rfl]; exact p13x78359
private def bp13x80174 : B := ![⟨62,some 93⟩,⟨30,some 45⟩,⟨22,none⟩]
private def bp13x80175 : B := ![⟨62,some 93⟩,⟨30,some 45⟩,⟨22,some 45⟩]
private def bp13x80176 : B := ![⟨62,some 93⟩,⟨30,some 36⟩,⟨22,some 45⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x80176 : Deny 1000000000000000000 13 bp13x80176 :=
  sound (by decide) (by decide) 15 122086291750578984027254936700242915827008885062809406177851198072889087779487675434268453692069825444682073760956378282090813296633329846062082056220543457997436634847392132237103229642885265533099059233908400622667546751347091284423613738436076323443949048916597329681537564356855483741866392147395741406053432696590982679637154648492338597925801739405 (tail:=0) (by decide +kernel)
private def bp13x80771 : B := ![⟨62,some 93⟩,⟨37,some 45⟩,⟨22,some 45⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x80771 : Deny 1000000000000000000 13 bp13x80771 :=
  sound (by decide) (by decide) 15 2393573028298722749400554571228376580210331435399056939575549700457056159871273060269417356641808474928520211356365469939166516181704477408571585340187488262179552881706323190541273085298879278812977866962510994261894727270622624149874578795900977391326664714895162443024399425604183621313628510195687934943411552743819940140431720324602796635743862197183623209119593554676689297474122190360694222004723678057871545601362763010975501624659100305045290783908573193370683843236410575214346902131164306436572187086689280846727501059532709541660035665837453853 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x80175 : Deny 1000000000000000000 13 bp13x80175 := by
  apply split bp13x80175 1
  · rw [show leftB bp13x80175 1=bp13x80176 by funext i; fin_cases i <;> rfl]; exact p13x80176
  · rw [show rightB bp13x80175 1=bp13x80771 by funext i; fin_cases i <;> rfl]; exact p13x80771
private def bp13x81704 : B := ![⟨62,some 93⟩,⟨30,some 45⟩,⟨46,none⟩]
private def bp13x81705 : B := ![⟨62,some 93⟩,⟨30,some 36⟩,⟨46,none⟩]
private def bp13x81706 : B := ![⟨62,some 74⟩,⟨30,some 36⟩,⟨46,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x81706 : Deny 1000000000000000000 13 bp13x81706 :=
  sound (by decide) (by decide) 25 242260912595964091543680942043513834204760649451396180111804148986805994554618458766360105082801451890424448522005317668602725364822800121574619269241114182152480219807909293033178331737993434432864699413413309241621029774532842485045464359508890021681105853246658791067935631188102852722213835785857725528414322025882885922645032154557612400030692851981713184704617607519079490828511743604322943729222991973927363879946446527527985629950364599530458578333999752199600681460125676004151522041706733324470160407985832729169348823401000812769307081376776506465053542728480680985423806251487219579751523062485684539004258819287256449405596022495480336232765021910304931122971823779146921943610306803667739 (tail:=0) (by decide +kernel)
private def bp13x82881 : B := ![⟨75,some 93⟩,⟨30,some 36⟩,⟨46,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x82881 : Deny 1000000000000000000 13 bp13x82881 :=
  sound (by decide) (by decide) 15 259924790243777653992767690817484284295306167086172151463435179134564773425435200163644715386582623931055391442771815223769765475803031611599972207934401287039080017304075181502714273838666499357180374075867 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x81705 : Deny 1000000000000000000 13 bp13x81705 := by
  apply split bp13x81705 0
  · rw [show leftB bp13x81705 0=bp13x81706 by funext i; fin_cases i <;> rfl]; exact p13x81706
  · rw [show rightB bp13x81705 0=bp13x82881 by funext i; fin_cases i <;> rfl]; exact p13x82881
private def bp13x83236 : B := ![⟨62,some 93⟩,⟨37,some 45⟩,⟨46,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x83236 : Deny 1000000000000000000 13 bp13x83236 :=
  sound (by decide) (by decide) 16 176501119177115114974939475275462356559011255546012999771083730626272877033533532726481992117148738752649914539705741047267306506103601122020399648219991435165 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x81704 : Deny 1000000000000000000 13 bp13x81704 := by
  apply split bp13x81704 1
  · rw [show leftB bp13x81704 1=bp13x81705 by funext i; fin_cases i <;> rfl]; exact p13x81705
  · rw [show rightB bp13x81704 1=bp13x83236 by funext i; fin_cases i <;> rfl]; exact p13x83236
set_option maxRecDepth 100000 in
private theorem p13x80174 : Deny 1000000000000000000 13 bp13x80174 := by
  apply split bp13x80174 2
  · rw [show leftB bp13x80174 2=bp13x80175 by funext i; fin_cases i <;> rfl]; exact p13x80175
  · rw [show rightB bp13x80174 2=bp13x81704 by funext i; fin_cases i <;> rfl]; exact p13x81704
set_option maxRecDepth 100000 in
private theorem p13x78312 : Deny 1000000000000000000 13 bp13x78312 := by
  apply split bp13x78312 0
  · rw [show leftB bp13x78312 0=bp13x78313 by funext i; fin_cases i <;> rfl]; exact p13x78313
  · rw [show rightB bp13x78312 0=bp13x80174 by funext i; fin_cases i <;> rfl]; exact p13x80174
set_option maxRecDepth 100000 in
private theorem p13x76690 : Deny 1000000000000000000 13 bp13x76690 := by
  apply split bp13x76690 1
  · rw [show leftB bp13x76690 1=bp13x76691 by funext i; fin_cases i <;> rfl]; exact p13x76691
  · rw [show rightB bp13x76690 1=bp13x78312 by funext i; fin_cases i <;> rfl]; exact p13x78312
set_option maxRecDepth 100000 in
private theorem p13x76498 : Deny 1000000000000000000 13 bp13x76498 := by
  apply split bp13x76498 2
  · rw [show leftB bp13x76498 2=bp13x76499 by funext i; fin_cases i <;> rfl]; exact p13x76499
  · rw [show rightB bp13x76498 2=bp13x76690 by funext i; fin_cases i <;> rfl]; exact p13x76690
private def bp13x83511 : B := ![⟨94,none⟩,⟨22,some 45⟩,⟨10,none⟩]
private def bp13x83512 : B := ![⟨94,none⟩,⟨22,some 45⟩,⟨10,some 21⟩]
private def bp13x83513 : B := ![⟨94,none⟩,⟨22,some 29⟩,⟨10,some 21⟩]
private def bp13x83514 : B := ![⟨94,some 189⟩,⟨22,some 29⟩,⟨10,some 21⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x83514 : Deny 1000000000000000000 13 bp13x83514 :=
  sound (by decide) (by decide) 16 52196300715464333858453595516680608235795963169085028850773015438897683 (tail:=0) (by decide +kernel)
private def bp13x83637 : B := ![⟨190,none⟩,⟨22,some 29⟩,⟨10,some 21⟩]
private def bp13x83638 : B := ![⟨190,none⟩,⟨22,some 29⟩,⟨10,some 13⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x83638 : Deny 1000000000000000000 13 bp13x83638 :=
  sound (by decide) (by decide) 23 218783826534319489383077946172537232366981116239436019572412049898331444180488805727407843086127496769253787142571799120220715428516788236209622701102630689 (tail:=0) (by decide +kernel)
private def bp13x83905 : B := ![⟨190,none⟩,⟨22,some 29⟩,⟨14,some 21⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x83905 : Deny 1000000000000000000 13 bp13x83905 :=
  sound (by decide) (by decide) 24 2880945924229031822895721546719135991924032346082587053924629366700653798857012737699595237275603362855158808174931967660512802745642769264664766274111336247949257294793183607302591363345531123209915873022042483032148115009393015564656414699294983887458333138899548695190357788091433433477654556407074762696384306384405215347190580209384600970703845744616659573591389125366029472702718647835295293827035706464508647411058011241838132639189292061706087042241476445059662737673757527361430659472764492189306926686252012630053852367300813188755688415543875342618943845258072794803680677712829677216643816804891200708432875538745 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x83637 : Deny 1000000000000000000 13 bp13x83637 := by
  apply split bp13x83637 2
  · rw [show leftB bp13x83637 2=bp13x83638 by funext i; fin_cases i <;> rfl]; exact p13x83638
  · rw [show rightB bp13x83637 2=bp13x83905 by funext i; fin_cases i <;> rfl]; exact p13x83905
set_option maxRecDepth 100000 in
private theorem p13x83513 : Deny 1000000000000000000 13 bp13x83513 := by
  apply split bp13x83513 0
  · rw [show leftB bp13x83513 0=bp13x83514 by funext i; fin_cases i <;> rfl]; exact p13x83514
  · rw [show rightB bp13x83513 0=bp13x83637 by funext i; fin_cases i <;> rfl]; exact p13x83637
private def bp13x84956 : B := ![⟨94,none⟩,⟨30,some 45⟩,⟨10,some 21⟩]
private def bp13x84957 : B := ![⟨94,some 189⟩,⟨30,some 45⟩,⟨10,some 21⟩]
private def bp13x84958 : B := ![⟨94,some 189⟩,⟨30,some 45⟩,⟨10,some 13⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x84958 : Deny 1000000000000000000 13 bp13x84958 :=
  sound (by decide) (by decide) 16 84000412471444254943706746795335093315442100387023292763692098531719696043727062509882006802271139218285731961435100112553310368801703917166038018918792588806098310678726 (tail:=0) (by decide +kernel)
private def bp13x85249 : B := ![⟨94,some 189⟩,⟨30,some 45⟩,⟨14,some 21⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x85249 : Deny 1000000000000000000 13 bp13x85249 :=
  sound (by decide) (by decide) 16 507696565377953734847212718147829049461074827215991895838997471009878223767633354202460579726685041504666250951644801489048504483075261493641726514864862025701043636763079198845105595251413890783530240318888749184950323022681725442213787289719323363436432061641202257638725165724020404247297154389522481669849993581048218931615553882736683093234855481689400804168407286410129612557392782979852192576502551266544356860574139627550682691881833434623844522416379075884973850291511143228767944772100462772661916286293094834225679118751716991748496452708418615748951908125670758829943943194538659128283547190 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x84957 : Deny 1000000000000000000 13 bp13x84957 := by
  apply split bp13x84957 2
  · rw [show leftB bp13x84957 2=bp13x84958 by funext i; fin_cases i <;> rfl]; exact p13x84958
  · rw [show rightB bp13x84957 2=bp13x85249 by funext i; fin_cases i <;> rfl]; exact p13x85249
private def bp13x86260 : B := ![⟨190,none⟩,⟨30,some 45⟩,⟨10,some 21⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x86260 : Deny 1000000000000000000 13 bp13x86260 :=
  sound (by decide) (by decide) 27 1547642397934636208903399898818615013541675827101012162518987248555944887364898436957265570645600587320871367472986781671684215817587672829954916000054744268828087065771809107113651332866866911613380970694897323600916793478383969270395350494059872466728985648148950215546563846489150525998357367306784996128313597814589320601665312296459738498527127671769648603414229760335314561188018893580567452806913327504537218052074153100595581643313383150492124127914226899125500700778012047636167208628224660726769297539712332951240259146715198466923008143715749619099620753500082907 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x84956 : Deny 1000000000000000000 13 bp13x84956 := by
  apply split bp13x84956 0
  · rw [show leftB bp13x84956 0=bp13x84957 by funext i; fin_cases i <;> rfl]; exact p13x84957
  · rw [show rightB bp13x84956 0=bp13x86260 by funext i; fin_cases i <;> rfl]; exact p13x86260
set_option maxRecDepth 100000 in
private theorem p13x83512 : Deny 1000000000000000000 13 bp13x83512 := by
  apply split bp13x83512 1
  · rw [show leftB bp13x83512 1=bp13x83513 by funext i; fin_cases i <;> rfl]; exact p13x83513
  · rw [show rightB bp13x83512 1=bp13x84956 by funext i; fin_cases i <;> rfl]; exact p13x84956
private def bp13x87225 : B := ![⟨94,none⟩,⟨22,some 45⟩,⟨22,none⟩]
private def bp13x87226 : B := ![⟨94,none⟩,⟨22,some 29⟩,⟨22,none⟩]
private def bp13x87227 : B := ![⟨94,some 189⟩,⟨22,some 29⟩,⟨22,none⟩]
private def bp13x87228 : B := ![⟨94,some 189⟩,⟨22,some 29⟩,⟨22,some 45⟩]
private def bp13x87229 : B := ![⟨94,some 125⟩,⟨22,some 29⟩,⟨22,some 45⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x87229 : Deny 1000000000000000000 13 bp13x87229 :=
  sound (by decide) (by decide) 16 24430806745288866759633716695619929497068675403254240700527958873283977032472321735346959768256211085813274241593929604485598143003715518023903996237157477452949376553972014130893182535806672595712007829799078282386916580735547283514445983159824538126305358 (tail:=0) (by decide +kernel)
private def bp13x87662 : B := ![⟨126,some 189⟩,⟨22,some 29⟩,⟨22,some 45⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x87662 : Deny 1000000000000000000 13 bp13x87662 :=
  sound (by decide) (by decide) 17 24945114916384953622860853755378364024353689623354730194291913155433241090702867964217296745816065268334551802614512932307353165362751505210055438756672884792961624592246639152198764004585640695559038574280684210685999598196471816639608825994880225392976552650223692379541855229346830979731168227137645483392268874326153308896296524443195278529031537509953891023419456455982690227800717620087273378887660266525246593386361453360074636557526433696208540942783592478308141042293908179050518839098889755995959838 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x87228 : Deny 1000000000000000000 13 bp13x87228 := by
  apply split bp13x87228 0
  · rw [show leftB bp13x87228 0=bp13x87229 by funext i; fin_cases i <;> rfl]; exact p13x87229
  · rw [show rightB bp13x87228 0=bp13x87662 by funext i; fin_cases i <;> rfl]; exact p13x87662
private def bp13x88517 : B := ![⟨94,some 189⟩,⟨22,some 29⟩,⟨46,none⟩]
private def bp13x88518 : B := ![⟨94,some 125⟩,⟨22,some 29⟩,⟨46,none⟩]
private def bp13x88519 : B := ![⟨94,some 125⟩,⟨22,some 25⟩,⟨46,none⟩]
private def bp13x88520 : B := ![⟨94,some 125⟩,⟨22,some 25⟩,⟨46,some 93⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x88520 : Deny 1000000000000000000 13 bp13x88520 :=
  sound (by decide) (by decide) 16 281346807869329743320169706527366141778562159672031329882552097255833246363227085069341809993095643450577044763766065932719092646302445637942859228540809637534230133421185021656412925114339807808934365337844282181127685321 (tail:=0) (by decide +kernel)
private def bp13x88895 : B := ![⟨94,some 125⟩,⟨22,some 25⟩,⟨94,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x88895 : Deny 1000000000000000000 13 bp13x88895 :=
  sound (by decide) (by decide) 26 3527843969181591555798415775411455103767880934765941941473993963144949550727642035136717391920883391349202732768225390886132212806492711540259874149797874524542288773351153113634260480926510850754988532940903800862489636979724301067261831123231487982261258282283633316867298549068155959274246159772116155756813565091216895487807771150361799629985674831046732919548060340405772215220016136773500820979342642785239558367293832716156360752808532457185970273933135098627590134353563836130805212642893113704482437347694033746680496450403410626826659950608770161991827916669169681483278910282908416988203321 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x88519 : Deny 1000000000000000000 13 bp13x88519 := by
  apply split bp13x88519 2
  · rw [show leftB bp13x88519 2=bp13x88520 by funext i; fin_cases i <;> rfl]; exact p13x88520
  · rw [show rightB bp13x88519 2=bp13x88895 by funext i; fin_cases i <;> rfl]; exact p13x88895
private def bp13x89904 : B := ![⟨94,some 125⟩,⟨26,some 29⟩,⟨46,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x89904 : Deny 1000000000000000000 13 bp13x89904 :=
  sound (by decide) (by decide) 15 30862810580401025619218701629516730275342471894413035372501573481344845674927214505887526326235646298654419658290093955362577853181475813390471700340742461773022267846123804666441191 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x88518 : Deny 1000000000000000000 13 bp13x88518 := by
  apply split bp13x88518 1
  · rw [show leftB bp13x88518 1=bp13x88519 by funext i; fin_cases i <;> rfl]; exact p13x88519
  · rw [show rightB bp13x88518 1=bp13x89904 by funext i; fin_cases i <;> rfl]; exact p13x89904
private def bp13x90217 : B := ![⟨126,some 189⟩,⟨22,some 29⟩,⟨46,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x90217 : Deny 1000000000000000000 13 bp13x90217 :=
  sound (by decide) (by decide) 19 16275624224920700347867856463283385002185300858358209027625537300831486130884359346864892521824086620773320443545950836630891764974558289539995977420508699431928483498667239042914306693336877509050587926386978047847319937674718542459600509971376614367758122259473773362384230558174187191399522160094731912528388923556886892420078723790094513397836006691777627455356781501165524428702 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x88517 : Deny 1000000000000000000 13 bp13x88517 := by
  apply split bp13x88517 0
  · rw [show leftB bp13x88517 0=bp13x88518 by funext i; fin_cases i <;> rfl]; exact p13x88518
  · rw [show rightB bp13x88517 0=bp13x90217 by funext i; fin_cases i <;> rfl]; exact p13x90217
set_option maxRecDepth 100000 in
private theorem p13x87227 : Deny 1000000000000000000 13 bp13x87227 := by
  apply split bp13x87227 2
  · rw [show leftB bp13x87227 2=bp13x87228 by funext i; fin_cases i <;> rfl]; exact p13x87228
  · rw [show rightB bp13x87227 2=bp13x88517 by funext i; fin_cases i <;> rfl]; exact p13x88517
private def bp13x90866 : B := ![⟨190,none⟩,⟨22,some 29⟩,⟨22,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x90866 : Deny 1000000000000000000 13 bp13x90866 :=
  sound (by decide) (by decide) 20 70884792018644380684396138551523015234270908663430226594922254145175653592954458421639359818602793897199795432378679954708180229150802162329199422090792603937892086060150714058930026871880850740028989343724510811404223480757349422478566440148542866238637277957265884525963246828440326327519698963530206799338922381819421919013032336315091970962922902993383 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x87226 : Deny 1000000000000000000 13 bp13x87226 := by
  apply split bp13x87226 0
  · rw [show leftB bp13x87226 0=bp13x87227 by funext i; fin_cases i <;> rfl]; exact p13x87227
  · rw [show rightB bp13x87226 0=bp13x90866 by funext i; fin_cases i <;> rfl]; exact p13x90866
private def bp13x91473 : B := ![⟨94,none⟩,⟨30,some 45⟩,⟨22,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x91473 : Deny 1000000000000000000 13 bp13x91473 :=
  sound (by decide) (by decide) 18 4220623725128009938475236599294500271543649699628515306360506757599752381222069193758273790777146275244244110346656115274759326999822589414544341813370361681480120177901520634488606909828588370386026902397381990157152217409557427034703711604354361194900510951284418934795787117 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x87225 : Deny 1000000000000000000 13 bp13x87225 := by
  apply split bp13x87225 1
  · rw [show leftB bp13x87225 1=bp13x87226 by funext i; fin_cases i <;> rfl]; exact p13x87226
  · rw [show rightB bp13x87225 1=bp13x91473 by funext i; fin_cases i <;> rfl]; exact p13x91473
set_option maxRecDepth 100000 in
private theorem p13x83511 : Deny 1000000000000000000 13 bp13x83511 := by
  apply split bp13x83511 2
  · rw [show leftB bp13x83511 2=bp13x83512 by funext i; fin_cases i <;> rfl]; exact p13x83512
  · rw [show rightB bp13x83511 2=bp13x87225 by funext i; fin_cases i <;> rfl]; exact p13x87225
set_option maxRecDepth 100000 in
private theorem p13x76497 : Deny 1000000000000000000 13 bp13x76497 := by
  apply split bp13x76497 0
  · rw [show leftB bp13x76497 0=bp13x76498 by funext i; fin_cases i <;> rfl]; exact p13x76498
  · rw [show rightB bp13x76497 0=bp13x83511 by funext i; fin_cases i <;> rfl]; exact p13x83511
private def bp13x91948 : B := ![⟨46,none⟩,⟨46,none⟩,⟨10,none⟩]
private def bp13x91949 : B := ![⟨46,some 93⟩,⟨46,none⟩,⟨10,none⟩]
private def bp13x91950 : B := ![⟨46,some 93⟩,⟨46,none⟩,⟨10,some 21⟩]
private def bp13x91951 : B := ![⟨46,some 61⟩,⟨46,none⟩,⟨10,some 21⟩]
private def bp13x91952 : B := ![⟨46,some 61⟩,⟨46,some 93⟩,⟨10,some 21⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x91952 : Deny 1000000000000000000 13 bp13x91952 :=
  sound (by decide) (by decide) 17 22785859018935756068142504059892526669451643453250996300951813811498860828389535407933120456033141421847334905430390119739683 (tail:=0) (by decide +kernel)
private def bp13x92165 : B := ![⟨46,some 61⟩,⟨94,none⟩,⟨10,some 21⟩]
private def bp13x92166 : B := ![⟨46,some 61⟩,⟨94,none⟩,⟨10,some 13⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x92166 : Deny 1000000000000000000 13 bp13x92166 :=
  sound (by decide) (by decide) 27 157130808840298863854536155048810967514104763167982358446877611079304916878350673779661417898469022945138194047269909057733790593583508304115180016661145502899047219094625797582176098973214194654185747398878828098535545878825588990382569339923721859132440534519102428087299617743001125368260227482206290714209580187911298484730620638566652945300474054 (tail:=0) (by decide +kernel)
private def bp13x92757 : B := ![⟨46,some 61⟩,⟨94,none⟩,⟨14,some 21⟩]
private def bp13x92758 : B := ![⟨46,some 61⟩,⟨94,some 189⟩,⟨14,some 21⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x92758 : Deny 1000000000000000000 13 bp13x92758 :=
  sound (by decide) (by decide) 17 57694985279212341036922810461335129178688084200999392909153089638151900296918979382773900171130845886423968556447125017574629206572999980328538365072073976003008370498315282003675085016820406503235510343856421665106687451281593798267880226004725836438655124873562285561369312918329643998231887043990174155901681639036701350859254370119846496883724592490309227704101752898689770565467158843538718633979144134472076767629 (tail:=0) (by decide +kernel)
private def bp13x93463 : B := ![⟨46,some 61⟩,⟨190,none⟩,⟨14,some 21⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x93463 : Deny 1000000000000000000 13 bp13x93463 :=
  sound (by decide) (by decide) 27 3729498285135322710684887917811840338428441957056062523900134988367281448298207771456294886596014046159712359166007218155515960296969902052532052467351820894394402200450524921493150935620132469821234956845042950797358155603906267823173777269224147367010272896617957984476885608370477280861406834680301523087226609351277772834360025278080667378301502603394157375577686331044714152946590209083863921246798121417619013534228811418225952471278215412679334697324876008031980420405433247213420594170459330670508532184223729604784930777820994517637638696857682080538250520398957 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x92757 : Deny 1000000000000000000 13 bp13x92757 := by
  apply split bp13x92757 1
  · rw [show leftB bp13x92757 1=bp13x92758 by funext i; fin_cases i <;> rfl]; exact p13x92758
  · rw [show rightB bp13x92757 1=bp13x93463 by funext i; fin_cases i <;> rfl]; exact p13x93463
set_option maxRecDepth 100000 in
private theorem p13x92165 : Deny 1000000000000000000 13 bp13x92165 := by
  apply split bp13x92165 2
  · rw [show leftB bp13x92165 2=bp13x92166 by funext i; fin_cases i <;> rfl]; exact p13x92166
  · rw [show rightB bp13x92165 2=bp13x92757 by funext i; fin_cases i <;> rfl]; exact p13x92757
set_option maxRecDepth 100000 in
private theorem p13x91951 : Deny 1000000000000000000 13 bp13x91951 := by
  apply split bp13x91951 1
  · rw [show leftB bp13x91951 1=bp13x91952 by funext i; fin_cases i <;> rfl]; exact p13x91952
  · rw [show rightB bp13x91951 1=bp13x92165 by funext i; fin_cases i <;> rfl]; exact p13x92165
private def bp13x94424 : B := ![⟨62,some 93⟩,⟨46,none⟩,⟨10,some 21⟩]
private def bp13x94425 : B := ![⟨62,some 93⟩,⟨46,some 93⟩,⟨10,some 21⟩]
private def bp13x94426 : B := ![⟨62,some 93⟩,⟨46,some 93⟩,⟨10,some 13⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x94426 : Deny 1000000000000000000 13 bp13x94426 :=
  sound (by decide) (by decide) 16 51689245825015239796503968502820148529165255307628877343391956148572433892070245738990671511100738539490050265050911847178664329131835515040365222345694520822399290678332985534279984964561812154155457778252642063995128006 (tail:=0) (by decide +kernel)
private def bp13x94801 : B := ![⟨62,some 93⟩,⟨46,some 93⟩,⟨14,some 21⟩]
private def bp13x94802 : B := ![⟨62,some 93⟩,⟨46,some 61⟩,⟨14,some 21⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x94802 : Deny 1000000000000000000 13 bp13x94802 :=
  sound (by decide) (by decide) 15 38546513212930982721521624963143226307898326051388874466735531422847587147851281674145343691359820390056738715327175394582865075642099975801371265340003862557204269113055241553700772553594116564250875742860114849483232798528822771116823748205799466736895542416465637508197204996941364468022301741887479359637911797100853671096627299760304802137405032580670992159810309252699987664273025681994125 (tail:=0) (by decide +kernel)
private def bp13x95467 : B := ![⟨62,some 93⟩,⟨62,some 93⟩,⟨14,some 21⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x95467 : Deny 1000000000000000000 13 bp13x95467 :=
  sound (by decide) (by decide) 15 1850111299049396417172270098508293591169584067492640934287188894547675811007194763113024548847400911258300939671956724151038977162610538329388169110253881984717632131807066460171515537462205583222337671648868097577398480723709963019571800810407752958775862996808986649946260764642077181049469068079702165454842345595128089709 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x94801 : Deny 1000000000000000000 13 bp13x94801 := by
  apply split bp13x94801 1
  · rw [show leftB bp13x94801 1=bp13x94802 by funext i; fin_cases i <;> rfl]; exact p13x94802
  · rw [show rightB bp13x94801 1=bp13x95467 by funext i; fin_cases i <;> rfl]; exact p13x95467
set_option maxRecDepth 100000 in
private theorem p13x94425 : Deny 1000000000000000000 13 bp13x94425 := by
  apply split bp13x94425 2
  · rw [show leftB bp13x94425 2=bp13x94426 by funext i; fin_cases i <;> rfl]; exact p13x94426
  · rw [show rightB bp13x94425 2=bp13x94801 by funext i; fin_cases i <;> rfl]; exact p13x94801
private def bp13x96016 : B := ![⟨62,some 93⟩,⟨94,none⟩,⟨10,some 21⟩]
private def bp13x96017 : B := ![⟨62,some 93⟩,⟨94,none⟩,⟨10,some 13⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x96017 : Deny 1000000000000000000 13 bp13x96017 :=
  sound (by decide) (by decide) 26 112464055286173358232098989088792767965581343017620909799691111867541390620464150038063491633621820054322656262724200477585671485028678670653067941619847109741104646849250979119072119093501513078334647426122106401848799729698012584975011097097311582806502127651430001878382060365342414332440016145035074902257334505334044248500824458783237113605397647340165520325874960190815477392918148849428913778079803658531764259749200578095728303490817109949857036656253084154837307825697042104284720250678868611831011112694223975045764697908235325138930878271507733912286308819305604186395660696185909234841451263684073401396539311025996550381562336825479069241155216652874420029207315638 (tail:=0) (by decide +kernel)
private def bp13x97156 : B := ![⟨62,some 93⟩,⟨94,none⟩,⟨14,some 21⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x97156 : Deny 1000000000000000000 13 bp13x97156 :=
  sound (by decide) (by decide) 15 69772044681835034909000344779987023650306468441067108531011349942 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x96016 : Deny 1000000000000000000 13 bp13x96016 := by
  apply split bp13x96016 2
  · rw [show leftB bp13x96016 2=bp13x96017 by funext i; fin_cases i <;> rfl]; exact p13x96017
  · rw [show rightB bp13x96016 2=bp13x97156 by funext i; fin_cases i <;> rfl]; exact p13x97156
set_option maxRecDepth 100000 in
private theorem p13x94424 : Deny 1000000000000000000 13 bp13x94424 := by
  apply split bp13x94424 1
  · rw [show leftB bp13x94424 1=bp13x94425 by funext i; fin_cases i <;> rfl]; exact p13x94425
  · rw [show rightB bp13x94424 1=bp13x96016 by funext i; fin_cases i <;> rfl]; exact p13x96016
set_option maxRecDepth 100000 in
private theorem p13x91950 : Deny 1000000000000000000 13 bp13x91950 := by
  apply split bp13x91950 0
  · rw [show leftB bp13x91950 0=bp13x91951 by funext i; fin_cases i <;> rfl]; exact p13x91951
  · rw [show rightB bp13x91950 0=bp13x94424 by funext i; fin_cases i <;> rfl]; exact p13x94424
private def bp13x97277 : B := ![⟨46,some 93⟩,⟨46,none⟩,⟨22,none⟩]
private def bp13x97278 : B := ![⟨46,some 61⟩,⟨46,none⟩,⟨22,none⟩]
private def bp13x97279 : B := ![⟨46,some 61⟩,⟨46,some 93⟩,⟨22,none⟩]
private def bp13x97280 : B := ![⟨46,some 61⟩,⟨46,some 93⟩,⟨22,some 45⟩]
private def bp13x97281 : B := ![⟨46,some 61⟩,⟨46,some 61⟩,⟨22,some 45⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x97281 : Deny 1000000000000000000 13 bp13x97281 :=
  sound (by decide) (by decide) 15 3405766013582769808748448282786327280067345877550853086243098813410413129365196132405559298266556969076382886477346084194525566368196159832609222595972803537181487315489662335706255965903093400830046293848188863616793201997528061074894830403591570198406317439031993403045421874186947309931989248789071599521339010033916138092873408200640132359265696887117739401017725435318210850314381865567373 (tail:=0) (by decide +kernel)
private def bp13x97942 : B := ![⟨46,some 61⟩,⟨62,some 93⟩,⟨22,some 45⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x97942 : Deny 1000000000000000000 13 bp13x97942 :=
  sound (by decide) (by decide) 16 223094892976827668686957524613656703664549190702661981079036540817585442859254997394194245790441197278477569211905758601164017989782839789799245103399672918658600238682448885559888355654397272522379967838849331276656525253521673822811930124529842476031129795640365780898660716910330321180480192094262368255694481913933323009679076760635942336861024450859735972466080306743103597693964196078600704865608125420194352403501467573917602140347026016780711262793845695654216123100377640943845556389914625121279019574482698043262313412780873940991228551619246347521092986254377742339771444825578642370878574410090334539096939517904259545578629814957510616457902614238865266230271015771021806821635363726209325 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x97280 : Deny 1000000000000000000 13 bp13x97280 := by
  apply split bp13x97280 1
  · rw [show leftB bp13x97280 1=bp13x97281 by funext i; fin_cases i <;> rfl]; exact p13x97281
  · rw [show rightB bp13x97280 1=bp13x97942 by funext i; fin_cases i <;> rfl]; exact p13x97942
private def bp13x99117 : B := ![⟨46,some 61⟩,⟨46,some 93⟩,⟨46,none⟩]
private def bp13x99118 : B := ![⟨46,some 61⟩,⟨46,some 61⟩,⟨46,none⟩]
private def bp13x99119 : B := ![⟨46,some 52⟩,⟨46,some 61⟩,⟨46,none⟩]
private def bp13x99120 : B := ![⟨46,some 52⟩,⟨46,some 61⟩,⟨46,some 93⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x99120 : Deny 1000000000000000000 13 bp13x99120 :=
  sound (by decide) (by decide) 16 154701352265242679422416227936178114390105778336971971957972882134767183190518441362339272804765027491543755745476196853782981873453452032840122316809336548983381995883336627243918995281371877820436982874995400135981652117618158810956530805855852402311561333753534935186317433389075971016936802572507334 (tail:=0) (by decide +kernel)
private def bp13x99629 : B := ![⟨46,some 52⟩,⟨46,some 61⟩,⟨94,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x99629 : Deny 1000000000000000000 13 bp13x99629 :=
  sound (by decide) (by decide) 26 101231874916186006861135880119008322813270076059267957322785908591703933314126591443208026414498182138797563980115462115203185402427787309901722402372937978591643795428652935207097981092718479667194738561773604761569860221260945782833964570389235017061782629610368010423840308438857025119917752025977360595397373280607650731639096140006209414148263298130645240426094651652315263601636277254988208004486096581004736981743791046306481808369460836154590080262979890870486812716840443689728287416355758687061511729921403543428974468806521607359863467085038077864636611607827678976782876291910838 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x99119 : Deny 1000000000000000000 13 bp13x99119 := by
  apply split bp13x99119 2
  · rw [show leftB bp13x99119 2=bp13x99120 by funext i; fin_cases i <;> rfl]; exact p13x99120
  · rw [show rightB bp13x99119 2=bp13x99629 by funext i; fin_cases i <;> rfl]; exact p13x99629
private def bp13x100620 : B := ![⟨53,some 61⟩,⟨46,some 61⟩,⟨46,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x100620 : Deny 1000000000000000000 13 bp13x100620 :=
  sound (by decide) (by decide) 15 87536351720457044145256961328682238929231603107753341956293540422732426693858673623351284916583184577259484088270395711554092107408767280315182307213079813021048211861229560118113718963590005676952150314443351792994011 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x99118 : Deny 1000000000000000000 13 bp13x99118 := by
  apply split bp13x99118 0
  · rw [show leftB bp13x99118 0=bp13x99119 by funext i; fin_cases i <;> rfl]; exact p13x99119
  · rw [show rightB bp13x99118 0=bp13x100620 by funext i; fin_cases i <;> rfl]; exact p13x100620
private def bp13x100995 : B := ![⟨46,some 61⟩,⟨62,some 93⟩,⟨46,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x100995 : Deny 1000000000000000000 13 bp13x100995 :=
  sound (by decide) (by decide) 17 1652394731004839803806483661627771529828603774043253169686456597936854565586064625655989832444863372655029337201449767363317385171132152201020839646437871267800299938764521680057913833361328331177265649106209290763283803487375690373179542523612003656794064109174987629 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x99117 : Deny 1000000000000000000 13 bp13x99117 := by
  apply split bp13x99117 1
  · rw [show leftB bp13x99117 1=bp13x99118 by funext i; fin_cases i <;> rfl]; exact p13x99118
  · rw [show rightB bp13x99117 1=bp13x100995 by funext i; fin_cases i <;> rfl]; exact p13x100995
set_option maxRecDepth 100000 in
private theorem p13x97279 : Deny 1000000000000000000 13 bp13x97279 := by
  apply split bp13x97279 2
  · rw [show leftB bp13x97279 2=bp13x97280 by funext i; fin_cases i <;> rfl]; exact p13x97280
  · rw [show rightB bp13x97279 2=bp13x99117 by funext i; fin_cases i <;> rfl]; exact p13x99117
private def bp13x101452 : B := ![⟨46,some 61⟩,⟨94,none⟩,⟨22,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x101452 : Deny 1000000000000000000 13 bp13x101452 :=
  sound (by decide) (by decide) 19 3348780538686479628781734352206809339363386870831161106339374036657656535640286341680075925570739406759023584903075461413371249107376665644916819788973725411966212754144323329752696293944530545017204894097776061703395942499609504917150066192915410513977959336059984475623218937171690562331809859680835665892737177139025103521987506546065707798799073803192134647402638389596930750171 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x97278 : Deny 1000000000000000000 13 bp13x97278 := by
  apply split bp13x97278 1
  · rw [show leftB bp13x97278 1=bp13x97279 by funext i; fin_cases i <;> rfl]; exact p13x97279
  · rw [show rightB bp13x97278 1=bp13x101452 by funext i; fin_cases i <;> rfl]; exact p13x101452
private def bp13x102101 : B := ![⟨62,some 93⟩,⟨46,none⟩,⟨22,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x102101 : Deny 1000000000000000000 13 bp13x102101 :=
  sound (by decide) (by decide) 18 7055164223671644609032481994420969158138267522703499713465110338441928080747295206359745232019861405583266004541338498982419163258855974071929157530935476800934623717319988838633737025112679226511317117120636051871541067998322839280585502646485723970231145534842808506469202812538471203103566667850224364060266708882034973550 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x97277 : Deny 1000000000000000000 13 bp13x97277 := by
  apply split bp13x97277 0
  · rw [show leftB bp13x97277 0=bp13x97278 by funext i; fin_cases i <;> rfl]; exact p13x97278
  · rw [show rightB bp13x97277 0=bp13x102101 by funext i; fin_cases i <;> rfl]; exact p13x102101
set_option maxRecDepth 100000 in
private theorem p13x91949 : Deny 1000000000000000000 13 bp13x91949 := by
  apply split bp13x91949 2
  · rw [show leftB bp13x91949 2=bp13x91950 by funext i; fin_cases i <;> rfl]; exact p13x91950
  · rw [show rightB bp13x91949 2=bp13x97277 by funext i; fin_cases i <;> rfl]; exact p13x97277
private def bp13x102656 : B := ![⟨94,none⟩,⟨46,none⟩,⟨10,none⟩]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
private theorem p13x102656 : Deny 1000000000000000000 13 bp13x102656 :=
  sound (by decide) (by decide) 20 1466156594906620793526721000212080961788324176531000616113577677889617821386429255655561352903701963589685186225459293598519384424250070174819607107558293612849849423283448557577218497413392493152383487407369145826413121276896811300369918347764127212162873581362828455450053957341978061763351762323273058347946494729492505887428387799839828716918543826730702253697071246083781485538727122871008582231848189341287702773339124264532110970547622352744621868296858725500095128475125499885630799412479237154090651535142927659286509051824337344222358683033074704605885401472779773236340220072231869776513886831698202348371214095840934293070706395 (tail:=0) (by decide +kernel)
set_option maxRecDepth 100000 in
private theorem p13x91948 : Deny 1000000000000000000 13 bp13x91948 := by
  apply split bp13x91948 0
  · rw [show leftB bp13x91948 0=bp13x91949 by funext i; fin_cases i <;> rfl]; exact p13x91949
  · rw [show rightB bp13x91948 0=bp13x102656 by funext i; fin_cases i <;> rfl]; exact p13x102656
set_option maxRecDepth 100000 in
private theorem p13x76496 : Deny 1000000000000000000 13 bp13x76496 := by
  apply split bp13x76496 1
  · rw [show leftB bp13x76496 1=bp13x76497 by funext i; fin_cases i <;> rfl]; exact p13x76497
  · rw [show rightB bp13x76496 1=bp13x91948 by funext i; fin_cases i <;> rfl]; exact p13x91948
set_option maxRecDepth 100000 in
private theorem p13x60780 : Deny 1000000000000000000 13 bp13x60780 := by
  apply split bp13x60780 2
  · rw [show leftB bp13x60780 2=bp13x60781 by funext i; fin_cases i <;> rfl]; exact p13x60781
  · rw [show rightB bp13x60780 2=bp13x76496 by funext i; fin_cases i <;> rfl]; exact p13x76496
set_option maxRecDepth 100000 in
private theorem p13x19982 : Deny 1000000000000000000 13 bp13x19982 := by
  apply split bp13x19982 0
  · rw [show leftB bp13x19982 0=bp13x19983 by funext i; fin_cases i <;> rfl]; exact p13x19983
  · rw [show rightB bp13x19982 0=bp13x60780 by funext i; fin_cases i <;> rfl]; exact p13x60780
set_option maxRecDepth 100000 in
private theorem p13x12 : Deny 1000000000000000000 13 bp13x12 := by
  apply split bp13x12 1
  · rw [show leftB bp13x12 1=bp13x13 by funext i; fin_cases i <;> rfl]; exact p13x13
  · rw [show rightB bp13x12 1=bp13x19982 by funext i; fin_cases i <;> rfl]; exact p13x19982
set_option maxRecDepth 100000 in
private theorem p13x10 : Deny 1000000000000000000 13 bp13x10 := by
  apply split bp13x10 2
  · rw [show leftB bp13x10 2=bp13x11 by funext i; fin_cases i <;> rfl]; exact p13x11
  · rw [show rightB bp13x10 2=bp13x12 by funext i; fin_cases i <;> rfl]; exact p13x12
set_option maxRecDepth 100000 in
private theorem p13x8 : Deny 1000000000000000000 13 bp13x8 := by
  apply split bp13x8 0
  · rw [show leftB bp13x8 0=bp13x9 by funext i; fin_cases i <;> rfl]; exact p13x9
  · rw [show rightB bp13x8 0=bp13x10 by funext i; fin_cases i <;> rfl]; exact p13x10
set_option maxRecDepth 100000 in
private theorem p13x6 : Deny 1000000000000000000 13 bp13x6 := by
  apply split bp13x6 1
  · rw [show leftB bp13x6 1=bp13x7 by funext i; fin_cases i <;> rfl]; exact p13x7
  · rw [show rightB bp13x6 1=bp13x8 by funext i; fin_cases i <;> rfl]; exact p13x8
set_option maxRecDepth 100000 in
private theorem p13x4 : Deny 1000000000000000000 13 bp13x4 := by
  apply split bp13x4 0
  · rw [show leftB bp13x4 0=bp13x5 by funext i; fin_cases i <;> rfl]; exact p13x5
  · rw [show rightB bp13x4 0=bp13x6 by funext i; fin_cases i <;> rfl]; exact p13x6
set_option maxRecDepth 100000 in
private theorem p13x2 : Deny 1000000000000000000 13 bp13x2 := by
  apply split bp13x2 1
  · rw [show leftB bp13x2 1=bp13x3 by funext i; fin_cases i <;> rfl]; exact p13x3
  · rw [show rightB bp13x2 1=bp13x4 by funext i; fin_cases i <;> rfl]; exact p13x4
set_option maxRecDepth 100000 in
theorem p13x0 : Deny 1000000000000000000 13 start := by
  apply split start 0
  · rw [show leftB start 0=bp13x1 by funext i; fin_cases i <;> rfl]; exact p13x1
  · rw [show rightB start 0=bp13x2 by funext i; fin_cases i <;> rfl]; exact p13x2
end OMA.Large245212

/- The large-prime exclusions cover every possible support of an odd
A245212 solution on at most four different primes. -/
namespace OMA.Large245212
open OMA.Smooth245212 Finset
open scoped ArithmeticFunction.sigma
abbrev Certs := ∀ q : ℕ,q=7 ∨ q=11 ∨ q=13 → Deny cutoff q start

private theorem four {p e : Fin 4 → ℕ} (cert : Certs) (hp : ∀ i,Nat.Prime (p i))
    (ord : StrictMono p) (odd : 3≤p 0) (positive : ∀ i,0<e i)
    (eq : OeisA245212.a (total p e)=(σ 1 (total p e):ℤ)) : p 3<cutoff := by
  by_contra! large
  have norm := normalized_of_eq p hp ord.injective _ eq
  have cap := OMA.OddFaces245212.cap_needed p e (fun i => (hp i).one_lt) 0 (positive 0) norm
  obtain ⟨a,b,c⟩ := OMA.OddFaces245212.small_bases hp ord odd
    ((by decide : 257≤cutoff).trans large) cap
  let q := p 2
  let r := p 3
  let f (i : Fin 3) := e i.castSucc
  have qq : q=7 ∨ q=11 ∨ q=13 := c
  have pp (i : Fin 3) : p i.castSucc=bases q i := by fin_cases i <;> simp [bases,q,a,b]
  have score : prefProd X q f*X r (some (e 3))+prefProd Y q f*Y r (some (e 3))=2 := by
    unfold normalized at norm
    rw [Fin.prod_univ_castSucc (fun i => X (p i) (some (e i))),
      Fin.prod_univ_castSucc (fun i => Y (p i) (some (e i)))] at norm
    simpa only [pp,prefProd,f,r,show Fin.last 3=(3:Fin 4) by decide] using norm
  have fact : total p e=prev q f*r^(e 3) := by
    simp [total,prev,bases,Fin.prod_univ_four,Fin.prod_univ_three,f,r,q,a,b,mul_assoc]
  have cop (i : Fin 4) (hi : i<3) : (p i).Coprime r :=
    (Nat.coprime_primes (hp i) (hp 3)).mpr (ord hi).ne
  have cm : (prev q f).Coprime r := by
    simp only [prev,total,Fin.prod_univ_three,bases,f,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two]
    have r3 : (3:ℕ).Coprime r := a ▸ cop 0 (by decide)
    have r5 : (5:ℕ).Coprime r := b ▸ cop 1 (by decide)
    exact Nat.coprime_mul_iff_left.mpr ⟨Nat.coprime_mul_iff_left.mpr
      ⟨r3.pow_left _,r5.pow_left _⟩,(cop 2 (by decide)).pow_left _⟩
  exact cert q qq f (fun i => by simp [start,Band.Contains,f]; exact positive _)
    r (e 3) (hp 3) (positive 3) large cm score (fact ▸ eq)

private theorem ordered {k : ℕ} (cert : Certs) (few : k≤4) (p e : Fin k → ℕ)
    (hp : ∀ i,Nat.Prime (p i)) (ord : StrictMono p) (odd : ∀ i,3≤p i)
    (positive : ∀ i,0<e i) (eq : OeisA245212.a (total p e)=(σ 1 (total p e):ℤ)) (i : Fin k) :
    p i<cutoff := by
  have norm := normalized_of_eq p hp ord.injective _ eq
  have cap := OMA.OddFaces245212.cap_needed p e (fun j => (hp j).one_lt) i (positive i) norm
  have tiny (u : Fin k → ℕ) (hu : ∀ j,1<u j) (bounds : ∀ j,u j≤p j)
      (small : (∏ j,OMA.OddFaces245212.limitX (u j))<2) : False := by
    have b := prod_le_prod (s:=Finset.univ) (f:=fun j => OMA.OddFaces245212.limitX (p j))
      (fun j _ => x_nonneg ((hu j).trans_le (bounds j)) none)
      (fun j _ => OMA.OddFaces245212.cap_anti (hu j) (bounds j))
    exact (cap.trans b).not_gt small
  interval_cases k
  · exact Fin.elim0 i
  · exact (tiny ![3] (by decide) (by intro j; fin_cases j; exact odd _) (by decide +kernel)).elim
  · by_contra! big
    have last : cutoff≤p 1 := big.trans (ord.monotone (Fin.le_last i))
    exact tiny ![3,cutoff] (by decide) (by intro j; fin_cases j; exact odd _; exact last) (by decide +kernel)
  · by_contra! big
    have last : cutoff≤p 2 := big.trans (ord.monotone (Fin.le_last i))
    have five : 5≤p 1 := by
      have a := odd 0; have b := ord (by decide : (0:Fin 3)<1)
      have neq : p 1≠4 := fun h => (by decide : ¬Nat.Prime 4) (h ▸ hp 1)
      omega
    exact tiny ![3,5,cutoff] (by decide) (by intro j; fin_cases j; exact odd _; exact five; exact last)
      (by decide +kernel)
  · exact (ord.monotone (Fin.le_last i)).trans_lt (four cert hp ord (odd 0) positive eq)

theorem from_certs (cert : Certs) {n : ℕ} (odd : Odd n) (few : n.primeFactors.card≤4)
    (eq : OeisA245212.a n=(σ 1 n:ℤ)) : ∀ p∈n.primeFactors,p<cutoff := by
  let S := n.primeFactors
  let p := S.orderEmbOfFin rfl
  let e (i : Fin S.card) := n.factorization (p i)
  have mem (i) : p i∈n.primeFactors := orderEmbOfFin_mem S rfl i
  have hp (i) := Nat.prime_of_mem_primeFactors (mem i)
  have op (i) : 3≤p i := by
    have h := (hp i).two_le
    have di := Nat.dvd_of_mem_primeFactors (mem i)
    have non : ¬2∣n := fun d => (Nat.not_even_iff_odd.mpr odd) (even_iff_two_dvd.mpr d)
    by_contra! lt
    have same : p i=2 := by omega
    exact non (same ▸ di)
  have ep (i) : 0<e i := (hp i).factorization_pos_of_dvd odd.pos.ne' (Nat.dvd_of_mem_primeFactors (mem i))
  have repr : total p e=n := by
    unfold total e
    exact (Fintype.prod_equiv (S.orderIsoOfFin rfl).toEquiv _
      (fun j : S => j.val^(n.factorization j.val)) (fun _ => rfl)).trans
      (Nat.prod_primeFactors_coe_pow_factorization odd.pos.ne').symm
  intro q hq
  have image : q∈Set.range p := by rw [show Set.range p=(S:Set ℕ) from range_orderEmbOfFin S rfl]; exact hq
  obtain ⟨i,rfl⟩ := image
  exact ordered cert few p e hp p.strictMono op ep (by rw [repr]; exact eq) i
end OMA.Large245212

namespace OMA.Uniform245212
open Finset OMA.Smooth245212
def cap (p : ℕ) : ℚ := X p none
def caps (s : Finset ℕ) := ∏ p∈s,cap p
theorem cap_le_two {p : ℕ} (hp : 3≤p) : cap p≤2 := by
  have h : (3:ℚ)≤p := by exact_mod_cast hp
  simp only [cap,X,Y,sub_zero]
  have h' : 1/((p:ℚ)-1)≤1 := (div_le_iff₀ (by linarith)).mpr (by linarith)
  linarith
end OMA.Uniform245212

namespace OMA.CapOrder245212
open Finset OMA.Smooth245212
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
end OMA.CapOrder245212

/- Effective bounds on the least unassigned exponent, for arbitrary fixed
prime support and normalized cofactor moments. -/
namespace OMA.Effective245212
open Finset OMA.Smooth245212 OMA.Uniform245212

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

def nextCut (s : Finset ℕ) (a : ℚ) : ℕ :=
  max (2*s.sup id+2) (1+⌈2*(a*s.card*2^s.card+1)/|a*caps s-2|⌉₊)

private theorem gap {s : Finset ℕ} (sn : s.Nonempty) (e : ℕ → ℕ) (hp : ∀ p∈s,p.Prime)
    (above : ∀ p∈s,3≤p) {a b : ℚ} (a1 : 1≤a) (b0 : 0≤b) (b1 : b≤1) {m : ℕ}
    (ge : ∀ p∈s,m≤e p)
    (eq : a*(∏ p∈s,X p (some (e p)))+b*(∏ p∈s,Y p (some (e p)))=2) :
    |a*caps s-2|≤(a*s.card*2^s.card+1)*(2/((m:ℚ)+1)) := by
  let z : ℚ := 2/((m:ℚ)+1)
  have z0 : 0≤z := by dsimp [z]; positivity
  have y0 (p) (h : p∈s) := y_nonneg (hp p h).one_lt (some (e p))
  have yl (p) (h : p∈s) : Y p (some (e p))≤z := by
    apply (le_div_iff₀ (by positivity : 0<(m:ℚ)+1)).2
    have g : (m:ℚ)≤e p := by exact_mod_cast ge p h
    nlinarith only [OMA.CapOrder245212.y_short (hp p h) (e p),
      mul_nonneg (y0 p h) (sub_nonneg.mpr g)]
  have diff (p) (h : p∈s) : 0≤cap p-X p (some (e p)) ∧ cap p-X p (some (e p))≤z := by
    have pp : (3:ℚ)≤p := by exact_mod_cast above p h
    have vals : cap p-X p (some (e p))=Y p (some (e p))/((p:ℚ)-1) := by simp [cap,X,Y]; ring
    rw [vals]
    exact ⟨div_nonneg (y0 p h) (by linarith),(div_le_self (y0 p h) (by linarith)).trans (yl p h)⟩
  have err := prod_error s (fun p => X p (some (e p))) cap z z0
    (fun p h => x_nonneg (hp p h).one_lt _) (fun p h => sub_nonneg.mp (diff p h).1)
    (fun p h => cap_le_two (above p h)) (fun p h => (diff p h).2)
  have xp := prod_le_prod (s:=s) (fun p h => x_nonneg (hp p h).one_lt (some (e p)))
    (fun p h => sub_nonneg.mp (diff p h).1)
  obtain ⟨p,pm⟩ := sn
  have yp : (∏ i∈s,Y i (some (e i)))≤z := by
    rw [←prod_erase_mul _ _ pm]
    exact (mul_le_of_le_one_left (y0 p pm)
      (prod_le_one (fun i hi => y0 i (mem_of_mem_erase hi))
        (fun i hi => y_one (hp i (mem_of_mem_erase hi)).one_lt _))).trans (yl p pm)
  have yy := prod_nonneg y0
  have az := zero_le_one.trans a1
  rw [abs_le]; unfold caps
  constructor <;> nlinarith only [eq, mul_le_mul_of_nonneg_left xp az, mul_le_mul_of_nonneg_left err az,
    mul_nonneg (show 0≤a*s.card*2^s.card by positivity) z0,
    mul_nonneg b0 yy, yp,mul_le_of_le_one_left yy b1, z0]

theorem off_face {s : Finset ℕ} (sn : s.Nonempty) (e : ℕ → ℕ) (hp : ∀ p∈s,p.Prime)
    (above : ∀ p∈s,3≤p) {a b : ℚ} (a1 : 1≤a) (b0 : 0≤b) (b1 : b≤1)
    (off : a*caps s≠2)
    (eq : a*(∏ p∈s,X p (some (e p)))+b*(∏ p∈s,Y p (some (e p)))=2) :
    ∃ p∈s,e p<nextCut s a := by
  by_contra! ge
  have g := gap sn e hp above a1 b0 b1 ge eq
  have den := abs_pos.mpr (sub_ne_zero.mpr off)
  let m := nextCut s a
  have ceiling : 2*(a*s.card*2^s.card+1)/|a*caps s-2| < (m:ℚ)+1 := by
    apply lt_of_le_of_lt (Nat.le_ceil _)
    have h : ⌈2*(a*s.card*2^s.card+1)/|a*caps s-2|⌉₊ ≤ m := by
      dsimp only [m,nextCut]; omega
    exact_mod_cast (Nat.lt_succ_of_le h)
  rw [div_lt_iff₀ den] at ceiling
  change |a*caps s-2|≤_*(2/((m:ℚ)+1)) at g
  rw [←mul_div_assoc,le_div_iff₀ (by positivity)] at g
  linarith

theorem on_face {s : Finset ℕ} (two : 1<s.card) (e : ℕ → ℕ) (hp : ∀ p∈s,p.Prime)
    (above : ∀ p∈s,3≤p) {a b : ℚ} (a1 : 1≤a) (b1 : b≤1) (on : a*caps s=2)
    (eq : a*(∏ p∈s,X p (some (e p)))+b*(∏ p∈s,Y p (some (e p)))=2) :
    ∃ p∈s,e p<nextCut s a := by
  by_contra! ge
  obtain ⟨i,ins,j,jns,ij⟩ := Finset.one_lt_card.mp two
  let x (p : ℕ) := X p (some (e p))
  let y (p : ℕ) := Y p (some (e p))
  have pp (p) (h : p∈s) : (3:ℚ)≤p := by exact_mod_cast above p h
  have y0 (p) (h : p∈s) : 0<y p := by
    dsimp only [y]; rw [y_avg (hp p h).one_lt]
    apply div_pos _ (by positivity)
    exact sum_pos' (fun t _ => by positivity)
      ⟨0,mem_range.mpr (by omega),by simp⟩
  have y1 (p) (h : p∈s) := y_one (hp p h).one_lt (some (e p))
  have x1 (p) (h : p∈s) : 1≤x p := le_add_of_nonneg_right (div_nonneg
    (sub_nonneg.mpr (y1 p h)) (by linarith only [pp p h]))
  have diff (p) : cap p-x p=y p/((p:ℚ)-1) := by dsimp only [cap,x,y,X,Y]; ring
  have xc (p) (h : p∈s) : x p≤cap p := by
    apply sub_nonneg.mp; rw [diff]; exact div_nonneg (y0 p h).le (by linarith only [pp p h])
  let P := ∏ p∈s.erase i,x p
  let Q := ∏ p∈s.erase i,cap p
  have p1 : 1≤P := one_le_prod (fun p h => x1 p (mem_of_mem_erase h))
  have pq : P≤Q := prod_le_prod (fun p h => zero_le_one.trans (x1 p (mem_of_mem_erase h)))
    (fun p h => xc p (mem_of_mem_erase h))
  have def0 := sub_nonneg.mpr (xc i ins)
  have deficit : cap i-x i≤caps s-∏ p∈s,x p := by
    rw [caps,←prod_erase_mul _ cap ins,←prod_erase_mul _ x ins]
    change cap i-x i≤Q*cap i-P*x i
    nlinarith only [mul_nonneg (sub_nonneg.mpr p1) def0,
      mul_nonneg (sub_nonneg.mpr pq) (zero_le_one.trans ((x1 i ins).trans (xc i ins)))]
  have ji : j∈s.erase i := mem_erase.mpr ⟨ij.symm,jns⟩
  have yp : (∏ p∈s,y p)≤y i*y j := by
    rw [←prod_erase_mul _ y ins,←prod_erase_mul _ y ji,mul_comm (y i)]
    apply mul_le_mul_of_nonneg_right _ (y0 i ins).le
    exact mul_le_of_le_one_left (y0 j jns).le (prod_le_one
      (fun p h => (y0 p (mem_of_mem_erase (mem_of_mem_erase h))).le)
      (fun p h => y1 p (mem_of_mem_erase (mem_of_mem_erase h))))
  have high : 2*i≤e j := by
    have sup := Finset.le_sup (f:=id) ins
    have cut := ge j jns
    dsimp [nextCut] at cut; change i≤_ at sup; omega
  have scalej : 2*((i:ℚ)-1)≤(e j:ℚ)+1 := by
    have v : 2*(i:ℚ)≤e j := by exact_mod_cast high
    linarith
  have small : y j<1/((i:ℚ)-1) := by
    apply (lt_div_iff₀ (by linarith only [pp i ins])).2
    have yy := mul_le_mul_of_nonneg_left scalej (y0 j jns).le
    have short := OMA.CapOrder245212.y_short (hp j jns) (e j)
    change y j*((e j:ℚ)+1)<2 at short
    linarith
  have fail : (∏ p∈s,y p)<cap i-x i := by
    rw [diff,div_eq_mul_one_div]
    exact yp.trans_lt (mul_lt_mul_of_pos_left small (y0 i ins))
  have yall : 0≤∏ p∈s,y p := prod_nonneg (fun p h => (y0 p h).le)
  change a*(∏ p∈s,x p)+b*(∏ p∈s,y p)=2 at eq
  have dp := le_trans def0 deficit
  nlinarith only [eq,on,fail,deficit,mul_nonneg (sub_nonneg.mpr a1) dp,
    mul_le_of_le_one_left yall b1]

theorem step {s : Finset ℕ} (two : 1<s.card) (e : ℕ → ℕ) (hp : ∀ p∈s,p.Prime)
    (above : ∀ p∈s,3≤p) {a b : ℚ} (a1 : 1≤a) (b0 : 0≤b) (b1 : b≤1)
    (eq : a*(∏ p∈s,X p (some (e p)))+b*(∏ p∈s,Y p (some (e p)))=2) :
    ∃ p∈s,e p<nextCut s a := by
  by_cases equal : a*caps s=2
  · exact on_face two e hp above a1 b1 equal eq
  · exact off_face (Finset.card_pos.mp (by omega)) e hp above a1 b0 b1 equal eq

end OMA.Effective245212

/- An executable complete existence test for arbitrary prime exponents.
The only recursive calls remove one prime, and the exponential cutoff is
computed from the remaining support and the current rational coefficient. -/
namespace OMA.Effective245212
open Finset OMA.Smooth245212 OMA.Uniform245212

def Sol (s : Finset ℕ) (a b : ℚ) := ∃ e : ℕ → ℕ, (∀ p∈s,0<e p) ∧
  a*(∏ p∈s,X p (some (e p)))+b*(∏ p∈s,Y p (some (e p)))=2

def search : ℕ → Finset ℕ → ℚ → ℚ → Bool
| 0,s,a,b => decide (s=∅ ∧ a+b=2)
| f+1,s,a,b =>
  if s=∅ then decide (a+b=2)
  else decide (∃ p∈s, ∃ j∈range (nextCut s a), 0<j ∧
    search f (s.erase p) (a*X p (some j)) (b*Y p (some j))=true)

private theorem peel {s : Finset ℕ} {a b : ℚ} {e : ℕ → ℕ} {p : ℕ}
    (ep : ∀ q∈s,0<e q) (eq : a*(∏ q∈s,X q (some (e q)))+b*(∏ q∈s,Y q (some (e q)))=2)
    (pm : p∈s) : Sol (s.erase p) (a*X p (some (e p))) (b*Y p (some (e p))) := by
  refine ⟨e,fun q h => ep q (mem_of_mem_erase h),?_⟩
  rw [←prod_erase_mul _ (fun q => X q (some (e q))) pm,
    ←prod_erase_mul _ (fun q => Y q (some (e q))) pm] at eq
  simpa only [mul_assoc,mul_comm,mul_left_comm] using eq

private theorem restore {s : Finset ℕ} {a b : ℚ} {p j : ℕ} (pm : p∈s) (jpos : 0<j)
    (sol : Sol (s.erase p) (a*X p (some j)) (b*Y p (some j))) : Sol s a b := by
  obtain ⟨e,ep,eq⟩ := sol
  let t := Function.update e p j
  have same (q) (h : q∈s.erase p) : t q=e q := Function.update_of_ne (mem_erase.mp h).1 _ _
  refine ⟨t,?_,?_⟩
  · intro q h
    by_cases qp : q=p
    · subst q; simpa [t] using jpos
    · exact (same q (mem_erase.mpr ⟨qp,h⟩)) ▸ ep q (mem_erase.mpr ⟨qp,h⟩)
  · rw [←prod_erase_mul _ (fun q => X q (some (t q))) pm,
      ←prod_erase_mul _ (fun q => Y q (some (t q))) pm]
    rw [prod_congr rfl (fun q h => congrArg (fun v => X q (some v)) (same q h)),
      prod_congr rfl (fun q h => congrArg (fun v => Y q (some v)) (same q h))]
    simpa only [t,Function.update_self,mul_assoc,mul_left_comm,mul_comm] using eq

private theorem same_axis {p k : ℕ} (hp : 3≤p) {a b : ℚ}
    (face : a*cap p=2) (eq : a*X p (some k)+b*Y p (some k)=2) :
    a*X p (some 1)+b*Y p (some 1)=2 := by
  have pp : (3:ℚ)≤p := by exact_mod_cast hp
  have yp : 0<Y p (some k) := by
    rw [y_avg (by omega)]
    apply div_pos _ (by positivity)
    exact sum_pos' (fun i _ => by positivity) ⟨0,mem_range.mpr (by omega),by simp⟩
  have off (k : ℕ) : X p (some k)=cap p-Y p (some k)/((p:ℚ)-1) := by dsimp [cap,X,Y]; ring
  rw [off] at eq ⊢
  have coeff : (b-a/((p:ℚ)-1))*Y p (some k)=0 := by linear_combination eq-face
  have bz := (mul_eq_zero.mp coeff).resolve_right yp.ne'
  linear_combination face+bz*Y p (some 1)

private theorem descend {s : Finset ℕ} {a b : ℚ} (sn : s.Nonempty) (hp : ∀ p∈s,p.Prime)
    (above : ∀ p∈s,3≤p) (a1 : 1≤a) (b0 : 0≤b) (b1 : b≤1) (sol : Sol s a b) :
    ∃ p∈s,∃ j∈range (nextCut s a),0<j ∧ Sol (s.erase p) (a*X p (some j)) (b*Y p (some j)) := by
  obtain ⟨e,ep,eq⟩ := sol
  by_cases small : ∃ p∈s,e p<nextCut s a
  · obtain ⟨p,pm,l⟩ := small
    exact ⟨p,pm,e p,mem_range.mpr l,ep p pm,peel ep eq pm⟩
  have c2 : s.card≤1 := by
    by_contra! h
    exact small (step h e hp above a1 b0 b1 eq)
  have c1 := card_pos.mpr sn
  have on : a*caps s=2 := by
    by_contra h
    exact small (off_face sn e hp above a1 b0 b1 h eq)
  obtain ⟨p,rfl⟩ := card_eq_one.mp (by omega : s.card=1)
  simp only [caps,prod_singleton] at on eq
  have ax := same_axis (above p (mem_singleton_self _)) on eq
  refine ⟨p,mem_singleton_self _,1,mem_range.mpr ?_,by decide,fun _ => 1,?_,?_⟩
  · dsimp [nextCut]; omega
  · simp
  · simpa using ax

theorem search_correct {f : ℕ} {s : Finset ℕ} {a b : ℚ} (depth : s.card≤f)
    (hp : ∀ p∈s,p.Prime) (above : ∀ p∈s,3≤p) (a1 : 1≤a) (b0 : 0≤b) (b1 : b≤1) :
    search f s a b=true ↔ Sol s a b := by
  induction f generalizing s a b with
  | zero =>
    have empty := card_eq_zero.mp (by omega : s.card=0)
    subst s; simp [search,Sol]
  | succ f ih =>
    by_cases empty : s=∅
    · subst s; simp [search,Sol]
    have sn := Finset.nonempty_iff_ne_empty.mpr empty
    simp only [search,if_neg empty,decide_eq_true_eq]
    have recurse (p) (pm : p∈s) (j : ℕ) : search f (s.erase p) (a*X p (some j)) (b*Y p (some j))=true
        ↔ Sol (s.erase p) (a*X p (some j)) (b*Y p (some j)) := by
      have rp : (3:ℚ)≤p := by exact_mod_cast above p pm
      have x1 : 1≤X p (some j) := le_add_of_nonneg_right (div_nonneg
        (sub_nonneg.mpr (y_one (hp p pm).one_lt _)) (by linarith))
      apply ih (by rw [card_erase_of_mem pm]; omega)
        (fun q h => hp q (mem_of_mem_erase h)) (fun q h => above q (mem_of_mem_erase h))
        (one_le_mul_of_one_le_of_one_le a1 x1) (mul_nonneg b0 (y_nonneg (hp p pm).one_lt _))
        (mul_le_one₀ b1 (y_nonneg (hp p pm).one_lt _) (y_one (hp p pm).one_lt _))
    constructor
    · rintro ⟨p,pm,j,_,pos,rest⟩
      exact restore pm pos ((recurse p pm j).mp rest)
    · intro sol
      obtain ⟨p,pm,j,js,pos,rest⟩ := descend sn hp above a1 b0 b1 sol
      exact ⟨p,pm,j,js,pos,(recurse p pm j).mpr rest⟩
end OMA.Effective245212

/- A finite arithmetic decision for the four-odd-prime A245212 child.
The remaining condition has no quantifier over exponents. -/
namespace OMA.Decision245212
open Finset OMA.Smooth245212 OMA.Large245212 OMA.Effective245212
open scoped ArithmeticFunction.sigma
def support (p q r : ℕ) : Finset ℕ := {3,p,q,r}
def baseTest (p q r : ℕ) := search 4 (support p q r) 1 1

def PrimeBound : Prop := ∀ n : ℕ, Odd n → n.primeFactors.card≤4 →
    OeisA245212.a n=(σ 1 n:ℤ) → ∀ p∈n.primeFactors,p<cutoff
def FiniteCheck : Prop :=
  ∀ p∈({5,7}:Finset ℕ), ∀ q∈Icc (p+1) 31, ∀ r∈Icc (q+1) (cutoff-1),
    q.Prime → r.Prime → 2≤OMA.Uniform245212.caps (support p q r) → baseTest p q r=false

def verdict : Bool := @decide FiniteCheck (by unfold FiniteCheck; infer_instance)
theorem verdict_iff : verdict=true ↔ FiniteCheck := by simp [verdict]

theorem of_finite_check (primes : PrimeBound) (finite : FiniteCheck) :
    ∀ k p q r e f g : ℕ, 2≤k → p.Prime → q.Prime → r.Prime → 5≤p → p<q → q<r →
      0<e → 0<f → 0<g → let n:=3^k*p^e*q^f*r^g;
      2*n.totient<n → OeisA245212.a n≠(σ 1 n:ℤ) := by
  intro k p q r e f g hk hp hq hr hp5 pq qr he hf hg n ht eq
  have tree : n.primeFactors=support p q r := by
    have k0 : k≠0 := by omega
    dsimp only [n,support]
    simp [Nat.primeFactors_mul, Nat.primeFactors_prime_pow, k0, he.ne', hf.ne', hg.ne',
      hp,hq,hr,hp.ne_zero,hq.ne_zero,hr.ne_zero,Nat.prime_three]
  have cheap : (support p q r).card≤4 := by
    simp [support,show 3≠p by omega,show 3≠q by omega,show 3≠r by omega,
      show p≠r by omega,pq.ne,qr.ne]
  have mem_prime (j) (hj : j∈support p q r) : Nat.Prime j := by
    simp only [support,mem_insert,mem_singleton] at hj
    rcases hj with rfl|rfl|rfl|rfl <;> first | assumption | decide
  have three (j) (hj : j∈support p q r) : 3≤j := by
    simp only [support,mem_insert,mem_singleton] at hj; omega
  have oddn : Odd n := by
    have op := hp.odd_of_ne_two (by omega)
    have oq := hq.odd_of_ne_two (by omega)
    have orr := hr.odd_of_ne_two (by omega)
    exact ((((by decide : Odd 3).pow).mul op.pow).mul oq.pow).mul orr.pow
  have big : r<cutoff := primes n oddn (tree ▸ cheap) eq r (by rw [tree]; simp [support])
  let P : Fin 4 → ℕ := ![3,p,q,r]
  let E : Fin 4 → ℕ := ![k,e,f,g]
  have pp (i : Fin 4) : Nat.Prime (P i) := by fin_cases i <;> simp [P,hp,hq,hr,Nat.prime_three]
  have pm : StrictMono P := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i; fin_cases i <;> simp [P] <;> omega
  have repr : total P E=n := by simp [total,P,E,n,Fin.prod_univ_four]
  have norm := normalized_of_eq P pp pm.injective E (by rw [repr]; exact eq)
  have cap := OMA.OddFaces245212.cap_needed P E (fun i => (pp i).one_lt) 0 (by simpa [E] using (by omega : 0<k)) norm
  have drop (u : Fin 4 → ℕ) (hu : ∀ i,1<u i) (ge : ∀ i,u i≤P i)
      (cut : (∏ i,OMA.OddFaces245212.limitX (u i))<2) : False := by
    have b := prod_le_prod (s:=univ) (f:=fun i => OMA.OddFaces245212.limitX (P i))
      (fun i _ => x_nonneg ((hu i).trans_le (ge i)) none) (fun i _ => OMA.OddFaces245212.cap_anti (hu i) (ge i))
    exact (cap.trans b).not_gt cut
  have smallP : p≤7 := by
    by_contra! h
    have pm : 11≤p := by by_contra! z; interval_cases p <;> norm_num at *
    apply drop ![3,11,12,13] (by decide) _ (by decide +kernel)
    intro i; fin_cases i <;> simp [P] <;> omega
  have p57 : p∈({5,7}:Finset ℕ) := by interval_cases p <;> norm_num at *
  have smallQ : q≤31 := by
    by_contra! h
    apply drop ![3,5,32,33] (by decide) _ (by decide +kernel)
    intro i; fin_cases i <;> simp [P] <;> omega
  have Eneq : 3≠p := by omega
  have Eneq' : 3≠q := by omega
  have Eneq'' : 3≠r := by omega
  have pr : p≠r := by omega
  let ex (i : ℕ) := if i=3 then k else if i=p then e else if i=q then f else g
  have ext (i) (h : i∈support p q r) : 0<ex i := by
    dsimp [ex]; split_ifs <;> omega
  have caps : 2≤OMA.Uniform245212.caps (support p q r) := by
    simpa [OMA.Uniform245212.caps,OMA.Uniform245212.cap,OMA.OddFaces245212.limitX,P,
      support,Fin.prod_univ_four,Eneq,Eneq',Eneq'',pq.ne,qr.ne,pr,mul_assoc] using cap
  have yes := (search_correct (f:=4) (a:=1) (b:=1) cheap mem_prime three (by decide) (by decide) (by decide)).mpr
    (show Sol (support p q r) 1 1 from ⟨ex,ext,by
      simpa [support,Fin.prod_univ_four,normalized,P,E,ex,Eneq,Eneq',Eneq'',Eneq.symm,Eneq'.symm,Eneq''.symm,
        pq.ne,qr.ne,pr,pq.ne.symm,qr.ne.symm,pr.symm,mul_assoc] using norm⟩)
  have no := finite p p57 q (mem_Icc.mpr ⟨pq,smallQ⟩) r (mem_Icc.mpr ⟨qr,by omega⟩) hq hr caps
  rw [baseTest,yes] at no; contradiction
end OMA.Decision245212

/- All prime-bound certificates are supplied. The sole unverified premise
is now a fixed, finite Boolean calculation. -/
namespace OMA.Decision245212
open OMA.Large245212
theorem prime_bound : PrimeBound := by
  intro n ho hf eq
  apply from_certs _ ho hf eq
  intro q h
  rcases h with rfl|rfl|rfl
  · exact p7x0
  · exact p11x0
  · exact p13x0

open scoped ArithmeticFunction.sigma
theorem conditional (last : verdict=true) :
    ∀ k p q r e f g : ℕ, 2≤k → p.Prime → q.Prime → r.Prime → 5≤p → p<q → q<r →
      0<e → 0<f → 0<g → let n:=3^k*p^e*q^f*r^g;
      2*n.totient<n → OeisA245212.a n≠(σ 1 n:ℤ) :=
  of_finite_check prime_bound (verdict_iff.mp last)
end OMA.Decision245212
