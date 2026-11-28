import FormalConjectures.OEIS.«245212»



/-! Reduction of the high-exponent divisor equation to 54 certified interior roots. -/

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

/- Algebra of the scaled binary logarithm on positive naturals. -/
namespace OMA.OddBox245212

noncomputable abbrev L (n : ℕ) := logSize (n:ℝ)

theorem lmono {a b : ℕ} (ha : 0<a) (hab : a≤b) : L a≤L b :=
  mono (by exact_mod_cast ha) (by exact_mod_cast hab)
theorem lreflect {a b : ℕ} (ha : 0<a) (hb : 0<b) : L a≤L b ↔ a≤b := by
  simpa [L] using reflect (x:=(a:ℝ)) (y:=(b:ℝ)) (by exact_mod_cast ha) (by exact_mod_cast hb)
theorem lmul {a b : ℕ} (ha : 0<a) (hb : 0<b) : L (a*b)=L a+L b := by
  push_cast [L];exact mul (by exact_mod_cast ha) (by exact_mod_cast hb)
theorem lpow (a n : ℕ) : L (a^n)=n*L a := by simp only [L,Nat.cast_pow,pow]
@[simp] theorem ltwo : L 2=16 := by norm_num [L]
@[simp] theorem lone : L 1=0 := by norm_num [L]
@[simp] theorem lfour : L 4=32 := by rw [show (4:ℕ)=2*2 by decide,lmul (by decide) (by decide),ltwo];norm_num

theorem le_up {a b : ℕ} (ha : 0<a) (h : a≤b) : L a≤up b := (lmono ha h).trans (enclosed b (ha.trans_le h)).2
theorem down_le {a b : ℕ} (ha : 0<a) (h : a≤b) : (down a:ℝ)≤L b := (enclosed a ha).1.trans (lmono ha h)
theorem lmax {a b : ℕ} (ha : 0<a) (hb : 0<b) : L (max a b)=max (L a) (L b) := by
  rcases le_total a b with h|h
  · rw [max_eq_right h,max_eq_right (lmono ha h)]
  · rw [max_eq_left h,max_eq_left (lmono hb h)]

theorem sum_three {x a b c : ℕ} (hx : 0<x) (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (ub : x≤a+b+c) : L x≤L 3+max (L a) (max (L b) (L c)) := by
  have h : x≤3*(max a (max b c)) := by omega
  have z := lmono hx h
  rwa [lmul (by decide) (by omega),lmax ha (by omega),lmax hb hc] at z

theorem sum_four {x a b c d : ℕ} (hx : 0<x) (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d)
    (ub : x≤a+b+c+d) : L x≤32+max (max (L a) (max (L b) (L c))) (L d) := by
  have h : x≤4*(max (max a (max b c)) d) := by omega
  have z := lmono hx h
  rwa [lmul (by decide) (by omega),lmax (by omega) hd,lmax ha (by omega),lmax hb hc,lfour] at z

/-- The numerator may grow linearly with the prime. Dividing by a
positive power of the prime makes the resulting ratio decreasing. -/
theorem increasing_gap {e lo q a b : ℕ} (he : 1≤e) (hl : 0<lo) (lq : lo≤q)
    (positive : 0<a+b*lo) : L (a+b*q)-e*L q≤L (a+b*lo)-e*L lo := by
  have h : (a+b*q)*lo≤(a+b*lo)*q := by nlinarith only [Nat.mul_le_mul_left a lq]
  have posq : 0<a+b*q := positive.trans_le (by gcongr)
  have h' := lmono (Nat.mul_pos posq hl) h
  rw [lmul posq hl,lmul positive (by omega)] at h'
  have := mul_nonneg (sub_nonneg.mpr (show (1:ℝ)≤e by exact_mod_cast he))
    (sub_nonneg.mpr (lmono hl lq))
  nlinarith only [h',this]

end OMA.OddBox245212

end

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

/- Preserve the two actual bases in the integer complementary-pole estimate. -/
namespace OMA.OddBox245212
open ArithmeticFunction OMA.Smooth245212 OMA.ComplementaryPole245212 OMA.ComplementaryLocal245212
open OMA.QuadraticPowerGap245212
open scoped ArithmeticFunction.sigma
open OMA.ComplementaryHeight245212 (gap)

theorem complement {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p) (oq : 3≤q) (pq : p≠q)
    (hd : 2≤d) (ha : 2*d+4≤a)
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

end OMA.OddBox245212

end

section

/- Simultaneous separation assuming the precise positive-alpha condition. -/
namespace OMA.OddBox245212
open ArithmeticFunction OMA.Smooth245212 OMA.ComplementaryLocal245212
open scoped ArithmeticFunction.sigma

theorem separations {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p)
    (pq : p<q) {a d k : ℕ} (ha : 1≤a) (hd : 1≤d) (hk : 2≤k) (small : (p:ℤ)-1<(k:ℤ)*d)
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
    apply OMA.TwoOddGlobalGap245212.nonzero_of_positive_alpha (B:=a+1) (C:=d+1) hq op pq (by omega) (by omega)
      hk (by simpa using small) gpos fg' sum unit
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


end OMA.OddBox245212

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

private theorem ratio {K G F u D E S T W V : ℤ} (u12 : 12≤u) (gg : 0<G)
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

/- Necessary inequalities, before either exponent or prime is replaced
by a box endpoint. All quantities refer to the actual divisor equation. -/
namespace OMA.OddBox245212
open ArithmeticFunction
open scoped ArithmeticFunction.sigma

def rest (K B C p : ℕ) := 6*C*B*K*p^2
noncomputable def terms (K B C p q : ℕ) :=
  max (L (K*C+p)+2*L q-(B-1:ℕ)*L p)
    (max (2*L p+L (K*B+q)-(C-1:ℕ)*L q)
      (L (K+p*q)-(B-1:ℕ)*L p-(C-1:ℕ)*L q))

noncomputable def compLimit (K B C : ℕ) (x y : ℝ) :=
  L 3+max 0 (max (L (2*C*B*K)+2*x+(C-1:ℕ)*y)
    (L (6*C^2*B)+16+max (L K) x+2*(C-1:ℕ)*y))

structure Model (K B C p q : ℕ) : Prop where
  co : (C-2:ℕ)*L q≤16*K+L (3*K*B)+(B-1:ℕ)*L p
  rev : (B-2:ℕ)*L p≤16*K+L (3*K*C)+(C-1:ℕ)*L q
  level : 16*(K:ℝ)≤L (3*B*C)+(B-1:ℕ)*L p+(C-1:ℕ)*L q
  near : 16*K+L (2*C*K)≤(B-1:ℕ)*L p → L q≤16*K+L (rest K B C p)
  far : L (C*K*B*p)+32≤16*(K-1:ℕ) → L (C*K)+32≤(B-1:ℕ)*L p → L q≤L (rest K B C p)
  exactInt : 0≤L 3+16*K+terms K B C p q
  limiting : 0≤32+max (terms K B C p q) (L (3*K*B*C)+2*L p+2*L q-16*(K-1:ℕ))
  comp : 2*C+3≤B → 16*(K:ℝ)≤compLimit K B C (L p) (L q)
  revComp : 2*B+3≤C → 16*(K:ℝ)≤compLimit K C B (L q) (L p)

private theorem comp_log {K B C x y : ℕ} (k0 : 0<K) (b0 : 0<B) (c0 : 0<C) (x0 : 0<x) (y0 : 0<y)
    (ub : 2^K≤1+2*C*B*K*x^2*y^(C-1)+6*C^2*B*(K+x)*(y^(C-1))^2) :
    16*(K:ℝ)≤compLimit K B C (L x) (L y) := by
  let U:=2*C*B*K;let V:=6*C^2*B
  have u : 0<U := by dsimp [U];positivity
  have v : 0<V := by dsimp [V];positivity
  change 2^K≤1+U*x^2*y^(C-1)+V*(K+x)*(y^(C-1))^2 at ub
  have h := sum_three (by positivity) (by decide : 0<1) (by positivity) (by positivity) ub
  rw [lpow,ltwo,lone,lmul (a:=U*x^2) (by positivity) (by positivity),lmul u (by positivity),
    lmul (a:=V*(K+x)) (by positivity) (by positivity),lmul v (by positivity),lpow,lpow,lpow] at h
  have plus : L (K+x)≤16+max (L K) (L x) := by
    simpa only [L,Nat.cast_add] using max_sum (by exact_mod_cast k0 : 0<(K:ℝ)) (by exact_mod_cast x0 : 0<(x:ℝ))
  unfold compLimit
  simp only [lpow,Nat.cast_ofNat] at h
  rw [mul_comm (K:ℝ)] at h
  refine h.trans ?_
  simp only [U,V] at *
  exact add_le_add le_rfl (max_le_max le_rfl (max_le_max le_rfl (by nlinarith only [plus])))

private theorem cofactor_log {x y a d k : ℕ} (xp : 0<x) (yp : 0<y)
    (h : y^(d-1)≤3*2^(k+1)*(k+1)*(a+1)*x^a) :
    (d-1:ℕ)*L y≤16*(k+1:ℕ)+L (3*(k+1)*(a+1))+a*L x := by
  rw [show 3*2^(k+1)*(k+1)*(a+1)*x^a=2^(k+1)*(3*(k+1)*(a+1))*x^a by ring] at h
  have g:=lmono (by positivity) h
  rw [lmul (by positivity) (by positivity),lmul (by positivity) (by positivity),lpow,lpow,lpow,ltwo] at g
  linarith only [g]

private theorem exact_logs {p q K B C : ℕ} (p0 : 0<p) (q0 : 0<q) (k0 : 0<K) (b0 : 0<B) (c0 : 0<C)
    (first : p^(B-1)*q^(C-1)≤(2^K-1)*OMA.SimultaneousBound245212.error p q K B C (p^(B-1)) (q^(C-1)))
    (second : 4*(2^K-1)*(p^(B-1)*q^(C-1))≤4*(2^K-1)*OMA.SimultaneousBound245212.error p q K B C (p^(B-1)) (q^(C-1))+
      9*K*p^2*q^2*B*C*p^(B-1)*q^(C-1)) :
    0≤L 3+16*K+terms K B C p q ∧
    0≤32+max (terms K B C p q) (L (3*K*B*C)+2*L p+2*L q-16*(K-1:ℕ)) := by
  let P:=p^(B-1);let Q:=q^(C-1);let G:=2^K-1
  let A:=(K*C+p)*q^2*Q;let D:=p^2*(K*B+q)*P;let E:=K+p*q;let H:=3*K*B*C
  have pp : 0<P := pow_pos p0 _
  have qq : 0<Q := pow_pos q0 _
  have gp : 0<G := by dsimp [G]; have:=Nat.one_lt_pow (by omega : K≠0) (by decide : 1<(2:ℕ));omega
  have ap : 0<A := by dsimp [A];positivity
  have dp : 0<D := by dsimp [D];positivity
  have ep : 0<E := by dsimp [E];positivity
  have hp : 0<H := by dsimp [H];positivity
  have err : OMA.SimultaneousBound245212.error p q K B C P Q=A+D+E := by
    dsimp [OMA.SimultaneousBound245212.error,A,D,E];ring
  change P*Q≤G*OMA.SimultaneousBound245212.error p q K B C P Q at first
  change 4*G*(P*Q)≤4*G*OMA.SimultaneousBound245212.error p q K B C P Q+9*K*p^2*q^2*B*C*P*Q at second
  rw [err] at first second
  have second' : G*P*Q≤G*A+G*D+G*E+H*p^2*q^2*P*Q := by
    dsimp [H];nlinarith only [second,Nat.zero_le (K*p^2*q^2*B*C*P*Q)]
  have fst : L (P*Q)≤L 3+max (L (G*A)) (max (L (G*D)) (L (G*E))) := by
    apply sum_three <;> first | positivity | nlinarith only [first]
  have snd := sum_four (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) second'
  have gmax : L G≤K*16 := by simpa only [lpow,ltwo] using lmono gp (Nat.sub_le (2^K) 1)
  have gmin : (K-1:ℕ)*16≤L G := by
    have tw : 0<(2:ℕ)^(K-1) := by positivity
    have sm : 2^(K-1)≤G := by dsimp [G];have:=pow_succ (2:ℕ) (K-1);rw [Nat.sub_add_cancel k0] at this;omega
    simpa only [lpow,ltwo] using lmono tw sm
  dsimp only [A,D,E] at fst snd
  simp (disch:=positivity) only [lmul,lpow,Nat.cast_ofNat] at fst snd
  dsimp [P,Q] at fst snd
  simp only [lpow] at fst snd
  dsimp only [H] at snd
  let t:=terms K B C p q
  let lp:=(B-1:ℕ)*L p
  let lq:=(C-1:ℕ)*L q
  have t1 : L (K*C+p)+2*L q-lp≤t := le_max_left _ _
  have t2 : 2*L p+L (K*B+q)-lq≤t := (le_max_left _ _).trans (le_max_right _ _)
  have t3 : L (K+p*q)-lp-lq≤t := (le_max_right _ _).trans (le_max_right _ _)
  have cap : max (L G+(L (K*C+p)+2*L q+lq))
      (max (L G+(2*L p+L (K*B+q)+lp)) (L G+L (K+p*q))) ≤ L G+lp+lq+t := by
    exact max_le (by linarith only [t1]) (max_le (by linarith only [t2]) (by linarith only [t3]))
  change lp+lq ≤ L 3+_ at fst
  change L G+lp+lq ≤ 32+_ at snd
  constructor
  · change 0≤L 3+16*K+t
    linarith only [fst,cap,gmax]
  · let h:=L (3*K*B*C)+2*L p+2*L q-16*(K-1:ℕ)
    have th : t ≤ max t h := le_max_left _ _
    have hh : h ≤ max t h := le_max_right _ _
    change 0≤32+max t h
    have all := max_le (cap.trans (by linarith only [th] : L G+lp+lq+t≤L G+lp+lq+max t h))
      (show L (3*K*B*C)+2*L p+2*L q+lp+lq≤L G+lp+lq+max t h by dsimp only [h] at hh;linarith only [gmin,hh])
    linarith only [snd,all]

theorem model {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 13≤p) (pq : p<q)
    (ha : 5≤a) (hd : 5≤d) (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    Model (k+1) (a+1) (d+1) p q := by
  let K:=k+1;let B:=a+1;let C:=d+1
  have k0 : 0<K := Nat.succ_pos _
  have b0 : 0<B := Nat.succ_pos _
  have c0 : 0<C := Nat.succ_pos _
  have p0:=hp.pos;have q0:=hq.pos
  have flip : OeisA245212.a (2^k*q^d*p^a)=(σ 1 (2^k*q^d*p^a):ℤ) := by rwa [mul_right_comm]
  have a2 : B-2=a-1 := by dsimp [B];omega
  have d2 : C-2=d-1 := by dsimp [C];omega
  have a1 : B-1=a := Nat.add_sub_cancel _ _
  have d1 : C-1=d := Nat.add_sub_cancel _ _
  have k1 : K-1=k := Nat.add_sub_cancel _ _
  have lx := OMA.TwoOddParameters245212.cofactor hp hq (by omega) (by omega) pq.ne (by omega) eqn
  have ly := OMA.TwoOddParameters245212.cofactor hq hp (by omega) (by omega) pq.ne.symm (by omega) flip
  have zc := OMA.ComplementaryDyad245212.level hp hq (by omega) (by omega) pq.ne (by omega) eqn
  change 2^K≤3*C*B*p^a*q^d at zc
  rw [show 3*C*B=3*B*C by ring] at zc
  have zl := lmono (by positivity : 0<(2:ℕ)^K) zc
  rw [lmul (a:=3*B*C*p^a) (by positivity) (by positivity),lmul (a:=3*B*C) (by positivity) (by positivity),
    lpow,lpow,lpow,ltwo] at zl
  have pb := prime_bound hp hq op pq ha hd eqn
  have kd := Nat.mul_le_mul_left k hd
  have sm : p-1<k*d := by omega
  have sm' : (p:ℤ)-1<(k:ℤ)*d := by zify [Nat.cast_sub hp.pos] at sm;exact sm
  have sep := separations hp hq (by omega) pq (by omega) (by omega) (by omega) sm' eqn
  obtain ⟨fi,se⟩ := OMA.SimultaneousBound245212.of_separations hp hq (by omega) (by omega) pq.ne eqn sep.1 sep.2
  have er := exact_logs (K:=K) (B:=B) (C:=C) p0 q0 k0 b0 c0 (by rw [a1,d1];exact fi)
    (by rw [a1,d1];simpa only [Nat.mul_assoc] using se)
  change Model K B C p q
  refine ⟨?_,?_,?_,?_,?_,er.1,er.2,?_,?_⟩
  · rw [d2,a1];exact cofactor_log p0 q0 lx
  · rw [a2,d1];exact cofactor_log q0 p0 ly
  · rw [a1,d1];linarith only [zl]
  · rw [a1]
    intro pole
    obtain ⟨s,succ⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : d≠0)
    have raw := OMA.ComplementaryPole245212.alternative hp hq (by omega) (by omega) pq.ne a s k (by omega) (by simpa [succ] using eqn)
    change p^a≤2*2^K*(s+2)*K ∨ q≤6*(s+2)*K*B*2^K*p^2 at raw
    have Cs : C=s+2 := by dsimp [C];omega
    rw [←Cs] at raw
    have poles : 2^K*(2*C*K)≤p^a := (lreflect (by positivity) (by positivity)).mp (by
      rw [lmul (by positivity) (by positivity),lpow,lpow,ltwo];linarith only [pole])
    rcases raw with le|qt
    · have equal : p^a=2*(2^K*C*K) := by nlinarith only [le,poles]
      obtain ⟨i,hi⟩ := (hp.odd_of_ne_two (by omega)).pow (n:=a)
      omega
    · have qt' : q≤2^K*rest K B C p := by dsimp [rest];nlinarith only [qt]
      have tmp := lmono q0 qt'
      rw [lmul (by positivity) (by dsimp [rest];positivity),lpow,ltwo] at tmp
      linarith only [tmp]
  · rw [a1,k1];intro first second
    have g : 4*(C*K*B*p)≤2^k := (lreflect (by positivity) (by positivity)).mp (by
      rw [lmul (by decide) (by positivity),lfour,lpow,ltwo];linarith only [first])
    have s : 4*(C*K)≤p^a := (lreflect (by positivity) (by positivity)).mp (by
      rw [lmul (by decide) (by positivity),lfour,lpow];linarith only [second])
    have longer : 2^k<2^K := by dsimp [K];rw [pow_succ];have:=Nat.two_pow_pos k;omega
    have qcap := OMA.ComplementaryFar245212.far hp hq (by omega) (by omega) pq.ne (by omega) (by omega) eqn
      (by change 4*K*C*B*p<2^K;nlinarith only [g,longer]) (by change 4*C*K≤p^a;nlinarith only [s])
    apply lmono q0
    dsimp [rest,K,B,C];nlinarith only [qcap]
  · intro med
    apply comp_log k0 b0 c0 p0 q0
    rw [d1];apply complement hp hq (by omega) (by omega) pq.ne (by omega) (by dsimp [C,B] at med;omega) eqn
  · intro med
    apply comp_log k0 c0 b0 q0 p0
    rw [a1];apply complement hq hp (by omega) (by omega) pq.ne.symm (by omega) (by dsimp [C,B] at med;omega) flip

end OMA.OddBox245212

end

section

/- Bounds for the logarithm of the larger prime and for its square divided
by the smaller prime power, including the two conditional pole refinements. -/
namespace OMA.OddBox245212

structure Fits (f : Frame) (K B C p q : ℕ) : Prop where
  kl0 : 6≤f.kl
  bl0 : 6≤f.bl
  cl0 : 6≤f.cl
  lo0 : 1≤f.lo
  lk : f.kl≤K
  hk : K≤f.kh
  lb : f.bl≤B
  hb : B≤f.bh
  lc : f.cl≤C
  hc : C≤f.ch
  lp : f.lo≤p
  hp : p≤f.hi
  lq : f.qlo≤q
  pq : p≤q

namespace Fits
variable {f : Frame} {K B C p q : ℕ} (t : Fits f K B C p q)
include t
theorem pos : 0<K ∧ 0<B ∧ 0<C ∧ 0<p ∧ 0<q := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_⟩:=t;omega
theorem xp_lower : (f.xp:ℝ)≤(B-1:ℕ)*L p := by
  have lo:=down_le t.lo0 t.lp
  have l0 : 0≤(down f.lo:ℝ) := by unfold down;positivity
  have b : (f.bl-1:ℕ)≤B-1 := Nat.sub_le_sub_right t.lb 1
  simp only [Frame.xp,Int.cast_mul,Int.cast_natCast]
  exact mul_le_mul (by exact_mod_cast b) lo l0 (by positivity)

theorem xp_upper : (B-1:ℕ)*L p≤((f.bh-1:ℕ)*up f.hi:ℤ) := by
  have u:=le_up t.pos.2.2.2.1 t.hp
  have b := Nat.sub_le_sub_right t.hb 1
  push_cast
  exact mul_le_mul (by exact_mod_cast b) u (nat_nonneg _ t.pos.2.2.2.1) (by positivity)

theorem rhs : 16*(K:ℝ)+L (3*K*B)≤f.cap := by
  obtain ⟨k,b,c,p',q'⟩:=t.pos
  have ha := le_up (by positivity : 0<3*K*B) (show 3*K*B≤3*f.kh*f.bh by gcongr <;> first | exact t.hk | exact t.hb)
  have hK : (K:ℝ)≤f.kh := by exact_mod_cast t.hk
  simp only [Frame.cap,Frame.dz,Int.cast_add,Int.cast_mul,Int.cast_natCast,Int.cast_ofNat]
  linarith

theorem caps (model : Model K B C p q) :
    (f.cl-2:ℕ)*L q≤(f.capY:ℝ) ∧
    ((f.cl:ℝ)-f.bh-1)*L q≤f.cap ∧
    L q≤f.y ∧ 2*L q-(B-1:ℕ)*L p≤f.normalized := by
  obtain ⟨kp,bp,cp,pp,qp⟩:=t.pos
  have qn:=nat_nonneg q qp
  have pn:=nat_nonneg p pp
  have kU : (K:ℝ)≤f.kh := by exact_mod_cast t.hk
  have kL : (f.kl-1:ℕ)≤K-1 := Nat.sub_le_sub_right t.lk _
  have c0:=t.cl0
  have clc : (f.cl-2:ℕ)≤C-2 := Nat.sub_le_sub_right t.lc _
  have bt := t.xp_upper
  have bi := t.xp_lower
  have co := model.co
  have right := t.rhs
  have cc := mul_le_mul_of_nonneg_right (show ((f.cl-2:ℕ):ℝ)≤(C-2:ℕ) by exact_mod_cast clc) qn
  have reduced : (f.cl-2:ℕ)*L q≤(f.cap:ℝ)+(B-1:ℕ)*L p := by linarith only [cc,co,right]
  have cY : (f.cl-2:ℕ)*L q≤(f.capY:ℝ) := by
    simp only [Frame.capY,Int.cast_add,Int.cast_mul,Int.cast_natCast] at bt ⊢
    linarith only [reduced,bt]
  have ordered : ((f.cl:ℝ)-f.bh-1)*L q≤f.cap := by
    have cb := Nat.sub_le_sub_right t.hb 1
    have mul := mul_le_mul (show ((B-1:ℕ):ℝ)≤(f.bh-1:ℕ) by exact_mod_cast cb)
      (lmono pp t.pq) pn (by positivity : (0:ℝ)≤(f.bh-1:ℕ))
    have bhp : 1≤f.bh := bp.trans_le t.hb
    simp only [Nat.cast_sub (by omega : 2≤f.cl),Nat.cast_sub bhp,Nat.cast_ofNat,Nat.cast_one] at reduced mul
    nlinarith only [reduced,mul]
  have y₁ := over_bound (show 0<f.cl-2 by omega) cY
  have rest : L (rest K B C p)≤f.residue := by
    unfold Frame.residue
    apply le_up (by dsimp [rest];positivity)
    unfold OddBox245212.rest
    gcongr <;> first | exact t.hk | exact t.hc | exact t.hb | exact t.hp
  have kdz : 16*(K:ℝ)≤f.dz := by
    simp only [Frame.dz,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast]
    linarith only [kU]
  have dgl : (f.dg:ℝ)≤16*(K-1:ℕ) := by
    simp only [Frame.dg,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast kL) (by norm_num)
  have y₂ : f.dz+up (2*f.ch*f.kh)≤f.xp → L q≤(f.dz+f.residue:ℤ) := by
    intro pre
    have pre' : (f.dz:ℝ)+up (2*f.ch*f.kh)≤f.xp := by exact_mod_cast pre
    have cv:=le_up (by positivity : 0<2*C*K) (show 2*C*K≤2*f.ch*f.kh by gcongr <;> first | exact t.hc | exact t.hk)
    have nz := model.near (by linarith only [pre',cv,kdz,bi])
    push_cast;linarith only [nz,kdz,rest]
  have y₃ : max (up (f.ch*f.kh*f.bh*f.hi)-f.dg) (up (f.ch*f.kh)-f.xp)≤ -32 → L q≤f.residue := by
    intro pre
    obtain ⟨u,v⟩:=max_le_iff.mp pre
    have wt:=le_up (by positivity : 0<C*K*B*p) (show C*K*B*p≤f.ch*f.kh*f.bh*f.hi by gcongr <;> first | exact t.hc | exact t.hk | exact t.hb | exact t.hp)
    have kt:=le_up (by positivity : 0<C*K) (show C*K≤f.ch*f.kh by gcongr <;> first | exact t.hc | exact t.hk)
    have u' : (up (f.ch*f.kh*f.bh*f.hi):ℝ)-f.dg≤ -32 := by exact_mod_cast u
    have v' : (up (f.ch*f.kh):ℝ)-f.xp≤ -32 := by exact_mod_cast v
    exact (model.far (by linarith only [wt,u',dgl]) (by linarith only [kt,v',bi])).trans rest
  have bound : L q≤f.y := by
    simp only [Int.cast_add] at y₂
    unfold Frame.y
    split <;> split <;> push_cast <;> try simp only [le_min_iff]
    all_goals tauto
  have ratio : (f.cl-2:ℕ)*(2*L q-(B-1:ℕ)*L p)≤(2*f.cap-(f.cl-4:ℕ)*f.xp:ℤ) := by
    have factor := mul_le_mul_of_nonneg_left bi (show (0:ℝ)≤(f.cl-4:ℕ) by positivity)
    simp only [Int.cast_sub,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast,Nat.cast_sub (by omega : 4≤f.cl),
      Nat.cast_sub (by omega : 2≤f.cl),Nat.cast_ofNat] at factor reduced ⊢
    nlinarith only [reduced,factor]
  have y₄ := over_bound (show 0<f.cl-2 by omega) ratio
  refine ⟨cY,ordered,bound,?_⟩
  simp only [Frame.normalized,Int.cast_min,Int.cast_sub,Int.cast_mul,Int.cast_ofNat,le_min_iff]
  exact ⟨y₄,by linarith only [bound,bi]⟩

end Fits
end OMA.OddBox245212

end

section

/- Endpoint substitution and soundness for any closed parameter box and
any least-prime subinterval. -/
namespace OMA.OddBox245212
open scoped ArithmeticFunction.sigma
set_option maxHeartbeats 1400000

private theorem down_nonneg (n : ℕ) : 0≤(down n:ℝ) := by
  simp only [down,Int.cast_natCast,Nat.cast_nonneg]

private theorem comp_false {kl kh bl bh ch K B C : ℕ} {x y : ℝ} {X Y : ℤ}
    (kp : 0<K) (bp : 0<B) (cp : 0<C) (klK : kl≤K) (Kkh : K≤kh)
    (blB : bl≤B) (Bbh : B≤bh) (Cch : C≤ch) (y0 : 0≤y) (lx : x≤X) (ly : y≤Y)
    (hit : 2*C+3≤B → 16*(K:ℝ)≤compLimit K B C x y) : compVeto kl kh bl bh ch X Y=false := by
  unfold compVeto
  simp only [decide_eq_false_iff_not,not_and]
  intro big fail
  have bound:=hit (by omega)
  have low : 16*(kl:ℝ)≤16*K := by gcongr
  have cut := le_up (a:=2*C*B*K) (by positivity)
    (show 2*C*B*K≤2*ch*bh*kh by gcongr)
  have cut' := le_up (a:=6*C^2*B) (by positivity)
    (show 6*C^2*B≤6*ch^2*bh by gcongr)
  have Y0 : 0≤(Y:ℝ) := y0.trans ly
  have cy : (C-1:ℕ)*y≤(ch-1:ℕ)*(Y:ℝ) :=
    mul_le_mul (by exact_mod_cast Nat.sub_le_sub_right Cch 1) ly y0 (by positivity)
  have mk := max_le_max (le_up kp Kkh) lx
  have a := (enclosed 3 (by decide)).2
  have z : 16*(kl:ℤ) ≤ max 0 (max (up (2*ch*bh*kh)+2*X+(ch-1:ℕ)*Y)
      (up (6*ch^2*bh)+16+max (up kh) X+2*(ch-1:ℕ)*Y))+up 3 := by
    apply Int.cast_le (R:=ℝ) |>.mp
    push_cast
    unfold compLimit at bound
    have le := max_le_max (a:= (0:ℝ)) le_rfl (max_le_max
      (show L (2*C*B*K)+2*x+(C-1:ℕ)*y≤(up (2*ch*bh*kh):ℝ)+2*X+(ch-1:ℕ)*(Y:ℝ) by linarith only [cut,lx,cy])
      (show L (6*C^2*B)+16+max (L K) x+2*(C-1:ℕ)*y≤(up (6*ch^2*bh):ℝ)+16+max (up kh:ℝ) (X:ℝ)+2*(ch-1:ℕ)*(Y:ℝ)
        by nlinarith only [cut',mk,cy]))
    linarith only [low,bound,le,a]
  omega

attribute [local irreducible] Frame.y Frame.normalized Frame.capY Frame.xp Frame.dz Frame.dg
  Frame.largest Frame.drift Frame.yq down up logSize

theorem Fits.retain {f : Frame} {K B C p q : ℕ} (t : Fits f K B C p q) (m : Model K B C p q) :
    f.reject=false := by
  obtain ⟨kp,bp,cp,pp,qp⟩:=t.pos
  obtain ⟨co,ord,y,norm⟩:=t.caps m
  have lo:=t.lo0
  have lq0 : 0<f.qlo := by dsimp [Frame.qlo];omega
  have dl := down_le lo t.lp
  have dq := down_le lq0 t.lq
  have dqn := down_nonneg f.qlo
  have hp := le_up pp t.hp
  have pn := nat_nonneg p pp
  have qn := nat_nonneg q qp
  have ch : ((C-1:ℕ):ℝ)≤(f.ch-1:ℕ) := by exact_mod_cast Nat.sub_le_sub_right t.hc 1
  have yd : (C-1:ℕ)*L q≤(f.ch-1:ℕ)*(f.y:ℝ) :=
    mul_le_mul ch y qn (Nat.cast_nonneg (α:=ℝ) _)
  have xp := t.xp_lower
  have pU := t.xp_upper
  have kmin : 16*(f.kl:ℝ)≤16*K := mul_le_mul_of_nonneg_left (by exact_mod_cast t.lk) (by norm_num)
  have kmax : 16*(K:ℝ)≤f.dz := by
    simp only [Frame.dz,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast t.hk) (by norm_num)
  have dg : (f.dg:ℝ)≤16*(K-1:ℕ) := by
    simp only [Frame.dg,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.sub_le_sub_right t.lk 1) (by norm_num)
  have rev : (f.bl-2:ℕ)*down f.lo≤f.dz+up (3*f.kh*f.ch)+(f.ch-1:ℕ)*f.y := by
    apply Int.cast_le (R:=ℝ) |>.mp
    push_cast
    have scale:= mul_le_mul (show ((f.bl-2:ℕ):ℝ)≤(B-2:ℕ) by exact_mod_cast Nat.sub_le_sub_right t.lb 2)
      dl (down_nonneg f.lo) (Nat.cast_nonneg (α:=ℝ) _)
    have u:=le_up (by positivity : 0<3*K*C) (show 3*K*C≤3*f.kh*f.ch by gcongr <;> first | exact t.hk | exact t.hc)
    linarith only [scale,m.rev,yd,kmax,u]
  have z : 16*(f.kl:ℤ)≤up (3*f.bh*f.ch)+(f.bh-1:ℕ)*up f.hi+(f.ch-1:ℕ)*f.y := by
    apply Int.cast_le (R:=ℝ) |>.mp
    push_cast at pU ⊢
    have u:=le_up (by positivity : 0<3*B*C) (show 3*B*C≤3*f.bh*f.ch by gcongr <;> first | exact t.hb | exact t.hc)
    linarith only [kmin,m.level,yd,pU,u]
  have yl : (f.cl-1:ℕ)*(down f.qlo:ℝ)≤(C-1:ℕ)*L f.qlo :=
    mul_le_mul (by exact_mod_cast Nat.sub_le_sub_right t.lc 1) (enclosed _ lq0).1 dqn (by positivity)
  have termle : terms K B C p q≤f.largest := by
    have c2 : 1≤C-1 := by have := t.cl0;have := t.lc;omega
    have nr := increasing_gap (a:=K*B) (b:=1) c2 lq0 t.lq (by positivity)
    simp only [one_mul] at nr
    have ns := increasing_gap (a:=K) (b:=p) c2 lq0 t.lq (by positivity)
    have u1:=le_up (by positivity : 0<K*C+p) (show K*C+p≤f.kh*f.ch+f.hi by gcongr <;> first | exact t.hk | exact t.hc | exact t.hp)
    have u2:=le_up (by positivity : 0<K*B+f.qlo) (show K*B+f.qlo≤f.kh*f.bh+f.qlo by gcongr <;> first | exact t.hk | exact t.hb)
    have u3:=le_up (by positivity : 0<K+p*f.qlo) (show K+p*f.qlo≤f.kh+f.hi*f.qlo by gcongr <;> first | exact t.hk | exact t.hp)
    unfold terms Frame.largest Frame.e1 Frame.e2 Frame.e3 Frame.yq
    push_cast
    exact max_le_max (by linarith only [norm,u1]) (max_le_max (by linarith only [nr,hp,yl,u2]) (by linarith only [ns,xp,yl,u3]))
  have drift : L (3*K*B*C)+2*L p+2*L q-16*(K-1:ℕ)≤f.drift := by
    have u:=le_up (by positivity : 0<3*K*B*C) (show 3*K*B*C≤3*f.kh*f.bh*f.ch by gcongr <;> first | exact t.hk | exact t.hb | exact t.hc)
    unfold Frame.drift;push_cast;linarith only [dg,hp,y,u]
  have ex : 0≤f.largest+up 3+f.dz := by
    apply Int.cast_le (R:=ℝ) |>.mp
    push_cast
    linarith only [m.exactInt,kmax,termle,(enclosed 3 (by decide)).2]
  have lim : 0 ≤ max f.largest f.drift+32 := by
    apply Int.cast_le (R:=ℝ) |>.mp
    push_cast
    linarith only [m.limiting,max_le_max termle drift]
  have pl : f.lo≤f.hi := t.lp.trans t.hp
  have qco : (f.cl-2:ℕ)*down f.qlo≤f.capY := by
    apply Int.cast_le (R:=ℝ) |>.mp
    push_cast;exact (mul_le_mul_of_nonneg_left dq (by positivity)).trans co
  have order : ((f.cl:ℤ)-f.bh-1)*down f.qlo≤f.cap := by
    apply Int.cast_le (R:=ℝ) |>.mp
    push_cast
    by_cases h : 0≤(f.cl:ℝ)-f.bh-1
    · exact (mul_le_mul_of_nonneg_left dq h).trans ord
    · have plus := t.rhs
      have c0:=nat_nonneg _ (by positivity : 0<3*K*B)
      nlinarith only [mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge h) dqn,plus,c0,(Nat.cast_nonneg (α:=ℝ) K)]
  have qcut : down f.qlo≤f.y := by exact_mod_cast dq.trans y
  have cmp := comp_false kp bp cp t.lk t.hk t.lb t.hb t.hc qn hp y m.comp
  have swp := comp_false kp cp bp t.lk t.hk t.lc t.hc t.hb pn y hp m.revComp
  unfold Frame.reject
  rw [cmp,swp]
  simp only [Bool.or_false,decide_eq_false_iff_not]
  omega

theorem veto_false {p q a d k kl kh bl bh cl ch pl ph : ℕ}
    (hp : p.Prime) (hq : q.Prime) (op : 13≤p) (pq : p<q) (ha : 5≤a) (hd : 5≤d)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ))
    (lk : kl≤k+1) (uk : k+1≤kh) (lb : bl≤a+1) (ub : a+1≤bh)
    (lc : cl≤d+1) (uc : d+1≤ch) (plp : pl≤p) (php : p≤ph) :
    veto kl kh bl bh cl ch pl ph=false := by
  unfold veto;split
  · rename_i cond
    obtain ⟨L,U,Q⟩:=prime_window hp hq op pq ha hd lk uk (by omega) lb plp php eqn
    have pos : 0<lowPrime kl bl pl := by dsimp [lowPrime];omega
    apply Fits.retain _ (model hp hq op pq ha hd eqn)
    exact ⟨cond.1,cond.2.1,cond.2.2,pos,lk,uk,lb,ub,lc,uc,L,U,Q,pq.le⟩
  · rfl

end OMA.OddBox245212

end

section

/- The geometric subdivision and its finite certificate. The coverage
proof uses only integer comparisons, including for ceilings and empty boxes. -/
namespace OMA.OddBox245212

def scan : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool → Bool
  | 0,_,_,_,_,_,_ => false
  | f+1,m,kl,kh,ml,mh,swap =>
    let top := min mh (min (64*m^2*kh) (32768*m^6))
    if kh < kl ∨ top < ml then true else
    let out := if swap then veto kl kh m m ml top 13 (3*kh)
      else veto kl kh ml top m m 13 (3*kh)
    if out then true else
    if kh*ml ≥ top*kl ∧ kl < kh then
      let mid := Nat.sqrt (kl*kh)
      scan f m kl mid ml top swap && scan f m (mid+1) kh ml top swap
    else
      let mid := Nat.sqrt (ml*top)
      scan f m kl kh ml mid swap && scan f m kl kh (mid+1) top swap

theorem scan_misses {K m M : ℕ} (swap : Bool) (fit : M ≤ 64*m^2*K) (global : M ≤ 32768*m^6)
    (retain : ∀ kl kh ml mh, kl ≤ K → K ≤ kh → ml ≤ M → M ≤ mh →
      (if swap then veto kl kh m m ml mh 13 (3*kh) else veto kl kh ml mh m m 13 (3*kh))=false)
    (fuel kl kh ml mh : ℕ) (lk : kl ≤ K) (hk : K ≤ kh) (lm : ml ≤ M) (hm : M ≤ mh) :
    scan fuel m kl kh ml mh swap=false := by
  induction fuel generalizing kl kh ml mh with
  | zero => rfl
  | succ f ih =>
    let top := min mh (min (64*m^2*kh) (32768*m^6))
    have ht : M ≤ top := le_min hm (le_min (fit.trans (Nat.mul_le_mul_left _ hk)) global)
    change (if kh < kl ∨ top < ml then _ else _) = false
    rw [if_neg (by omega),retain kl kh ml top lk hk lm ht]
    simp only [Bool.false_eq_true,↓reduceIte]
    split
    · let mid := Nat.sqrt (kl*kh)
      change (scan f m kl mid ml top swap && scan f m (mid+1) kh ml top swap)=false
      by_cases h : K ≤ mid
      · simp [ih kl mid ml top lk h lm ht]
      · simp [ih (mid+1) kh ml top (by omega) hk lm ht]
    · let mid := Nat.sqrt (ml*top)
      change (scan f m kl kh ml mid swap && scan f m kl kh (mid+1) top swap)=false
      by_cases h : M ≤ mid
      · simp [ih kl kh ml mid lk hk lm h]
      · simp [ih kl kh (mid+1) top lk hk (by omega) ht]

def exterior (m : ℕ) : Bool :=
  [false,true].all fun swap =>
    let ml := if swap then m+1 else m
    scan 40 m 1251 (512*m^4) ml (32768*m^6) swap &&
      scan 40 m 6 1250 (max 226 ml) (32768*m^6) swap

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
theorem table {m : ℕ} (lo : 6 ≤ m) (hi : m ≤ 32) : exterior m=true := by
  interval_cases m <;> decide +kernel

theorem rectangle {m M K : ℕ} (swap : Bool) (hm : 6 ≤ m) (small : m ≤ 32)
    (order : (if swap then m+1 else m) ≤ M) (hk : 6 ≤ K) (kb : K ≤ 512*m^4)
    (mb : M ≤ 64*m^2*K) (mg : M ≤ 32768*m^6)
    (retain : ∀ kl kh ml mh, kl ≤ K → K ≤ kh → ml ≤ M → M ≤ mh →
      (if swap then veto kl kh m m ml mh 13 (3*kh) else veto kl kh ml mh m m 13 (3*kh))=false) :
    K ≤ 1250 ∧ M ≤ 225 := by
  have h := table hm small
  unfold exterior at h
  have member : swap∈[false,true] := by cases swap <;> simp
  have both := List.all_eq_true.mp h swap member
  simp only [Bool.and_eq_true] at both
  obtain ⟨one,two⟩ := both
  have bound : K ≤ 1250 := by
    by_contra! large
    have := scan_misses swap mb mg retain 40 _ _ _ _ (by omega : 1251 ≤ K) kb order mg
    grind
  refine ⟨bound,?_⟩
  by_contra! large
  have := scan_misses swap mb mg retain 40 _ _ _ _ hk bound (max_le (by omega : 226 ≤ M) order) mg
  grind

end OMA.OddBox245212

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

/- The original OEIS equality implies the two-dimensional enclosure in
the high-exponent sector, for both relative orders of the odd exponents. -/
namespace OMA.OddBox245212
open scoped ArithmeticFunction.sigma

theorem original {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 13≤p)
    (pq : p<q) (ha : 5≤a) (hd : 5≤d)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    6≤k+1 ∧ k+1≤1250 ∧ max (a+1) (d+1)≤225 := by
  have prime := prime_bound hp hq op pq ha hd eqn
  have leanK : 6≤k+1 := by omega
  have minBound := OMA.TwoOddEffectiveOriginal245212.bound hp hq (by omega) pq (by omega) eqn
  refine ⟨leanK,?_⟩
  have small := OMA.ComplementaryExp245212.exponent hp hq (by omega) (by omega) pq.ne (by omega) eqn
  have flip : OeisA245212.a (2^k*q^d*p^a)=(σ 1 (2^k*q^d*p^a):ℤ) := by rwa [mul_right_comm]
  by_cases h : d≤a
  · have ⟨kb,mg⟩ := OMA.ComplementaryFinish245212.exponents hp hq (by omega) (by omega) pq.ne (by omega) eqn
    rw [max_eq_left (by omega)]
    apply rectangle (m:=d+1) (M:=a+1) false (by omega) (by omega) (by simp;omega) leanK kb small mg
    intro kl kh ml mh lk uk lm hm
    exact veto_false hp hq op pq ha hd eqn lk uk lm hm le_rfl le_rfl op (by omega)
  · have ⟨kb,mg⟩ := OMA.ComplementaryFinish245212.exponents hq hp (by omega) (by omega) pq.ne.symm (by omega) flip
    have ms := OMA.ComplementaryExp245212.exponent hq hp (by omega) (by omega) pq.ne.symm (by omega) flip
    rw [max_eq_right (by omega)]
    apply rectangle (m:=a+1) (M:=d+1) true (by omega) (by omega) (by simp;omega) leanK kb ms mg
    intro kl kh ml mh lk uk lm hm
    exact veto_false hp hq op pq ha hd eqn lk uk le_rfl le_rfl lm hm op (by omega)

end OMA.OddBox245212

end

section

/- A pointwise lower bound on the last-prime deficit, retaining the
actual integral pole instead of replacing a positive integer by one. -/
namespace OMA.RankTwoPoleInterior245212
open ArithmeticFunction OMA.Smooth245212 OMA.ComplementaryPole245212 OMA.ComplementaryLocal245212
open scoped ArithmeticFunction.sigma

def L (k p b c : ℤ) := c*b*(p-1)*((p-1)-k)+(c*k-(p-1))*p

theorem point {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p) (oq : 3≤q)
    (pq : p≠q) (ha : 2≤a) (small : (p:ℤ)-1≤((d:ℤ)+2)*k)
    (eqn : OeisA245212.a (2^k*p^a*q^(d+1))=(σ 1 (2^k*p^a*q^(d+1)):ℤ)) :
    let b : ℤ := a+1; let c : ℤ := d+2; let u : ℤ := p-1; let K : ℤ := k+1
    0<L k p b c ∧ ∀ x y : ℤ, K*c*b*u≤x*G k → c*K≤y*(p:ℤ)^a →
      (q:ℤ)*(L k p b c-(x+y))≤3*c*K*b*u^2 := by
  dsimp only
  let b : ℤ := a+1
  let c : ℤ := d+2
  let u : ℤ := p-1
  let K : ℤ := k+1
  let P : ℤ := (p:ℤ)^a
  let D := den k b c P (W (p^a)) (σ 1 (p^a))
  have gp := (dyad k).1
  have pp : 0<P := pow_pos (by omega) _
  have up : 0<u := by dsimp [u];omega
  have cb : 0<c := by dsimp [c];positivity
  have bp : 0<b := by dsimp [b];positivity
  have kp : 0<K := by dsimp [K];positivity
  have ppos : (0:ℤ)<p := by omega
  have qpos : (0:ℤ)<q := by omega
  have bu : 0<b*u-p := by
    dsimp [b,u]
    nlinarith only [mul_nonneg (by omega : (0:ℤ)≤a-2) (by omega : (0:ℤ)≤p-1),op]
  have fg : F k=(k:ℤ)*G k+K := by dsimp [F,G,K];ring
  have cf : 0≤c*F k-G k*u := by
    change u≤c*k at small
    rw [fg]; nlinarith only [mul_nonneg gp.le (sub_nonneg.mpr small),mul_pos cb kp]
  have m := moments hp a
  have id : u^2*D=P*G k*(L k p b c)-P*K*c*(b*u-p)-(c*F k-G k*u) := by
    dsimp [D,den,L,u,b,c,P,K] at *
    rw [fg]
    linear_combination -((d:ℤ)+2)*((k:ℤ)*G k+(k+1))*m.2-G k*(p-1)*m.1
  obtain ⟨plus,tail⟩ := tail hp hq op oq pq a d k eqn
  change 0<D at plus
  change (q:ℤ)*D≤3*c*K*b*G k*P at tail
  have pl : 0<(P*G k)*(L k p b c) := by
    nlinarith only [id,cf,mul_pos (sq_pos_of_pos up) plus,
      mul_nonneg (mul_nonneg (mul_nonneg pp.le kp.le) cb.le) bu.le]
  refine ⟨pos_of_mul_pos_right pl (mul_nonneg pp.le gp.le),?_⟩
  intro x y hx hy
  have fcap := mul_le_mul_of_nonneg_left (dyad k).2.2.1 cb.le
  have room : (P*G k)*(L k p b c-(x+y))≤u^2*D := by
    nlinarith only [id,mul_le_mul_of_nonneg_left hx pp.le,mul_le_mul_of_nonneg_left hy gp.le,
      fcap,mul_nonneg gp.le up.le,mul_nonneg (mul_nonneg (mul_nonneg pp.le kp.le) cb.le) ppos.le]
  apply le_of_mul_le_mul_right (a:=P*G k) _ (mul_pos pp gp)
  nlinarith only [mul_le_mul_of_nonneg_left room qpos.le,
    mul_le_mul_of_nonneg_left tail (sq_nonneg u)]


def underSlope (l h s : ℤ) := if s<0 then h*s else l*s
def overSlope (l h s : ℤ) := if s<0 then l*s else h*s

private theorem bracket {l h x s t w : ℤ} (lo : l≤x) (hi : x≤h)
    (xp : 0≤x) (sl : s≤t) (sw : t≤w) :
    underSlope l h s≤x*t ∧ x*t≤overSlope l h w := by
  have low := mul_le_mul_of_nonneg_left sl xp
  have high := mul_le_mul_of_nonneg_left sw xp
  constructor
  · unfold underSlope; split
    · exact (mul_le_mul_of_nonpos_right hi (by omega)).trans low
    · exact (mul_le_mul_of_nonneg_right lo (by omega)).trans low
  · unfold overSlope; split
    · exact high.trans (mul_le_mul_of_nonpos_right lo (by omega))
    · exact high.trans (mul_le_mul_of_nonneg_right hi (by omega))

/-- k endpoints are the ordinary exponent (not K); p,r bound the
smaller prime, while the larger prime is not yet bounded. -/
def lowPole (kl kh bl bh cl ch p r : ℤ) :=
  underSlope (cl*bl*(p-1)) (ch*bh*(r-1)) (p-1-kh)+max 0 (cl*kl-(r-1))*p

def highPole (kl kh bl bh cl ch p r : ℤ) :=
  overSlope (cl*bl*(p-1)) (ch*bh*(r-1)) (r-1-kl)+(ch*kh-(p-1))*r

theorem pole_interval {kl kh bl bh cl ch pl ph k p b c : ℤ}
    (k0 : 0≤kl) (b0 : 0≤bl) (c0 : 0≤cl) (p0 : 1≤pl)
    (kl' : kl≤k) (kh' : k≤kh) (bl' : bl≤b) (bh' : b≤bh)
    (cl' : cl≤c) (ch' : c≤ch) (pl' : pl≤p) (ph' : p≤ph)
    (small : p-1≤c*k) :
    lowPole kl kh bl bh cl ch pl ph≤L k p b c ∧ L k p b c≤highPole kl kh bl bh cl ch pl ph := by
  have pp : 0≤p := by omega
  have up : 0≤p-1 := by omega
  have bp : 0≤b := by omega
  have cp : 0≤c := by omega
  have bh0 : 0≤bh := by omega
  have ch0 : 0≤ch := by omega
  have kk : 0≤k := by omega
  have blim : cl*bl*(pl-1)≤c*b*(p-1) := by gcongr
  have bhim : c*b*(p-1)≤ch*bh*(ph-1) := by gcongr
  have first := bracket blim bhim (by positivity : 0≤c*b*(p-1))
    (show pl-1-kh≤p-1-k by omega) (show p-1-k≤ph-1-kl by omega)
  have a : cl*kl≤c*k := by gcongr
  have z : c*k≤ch*kh := by gcongr
  have e : max 0 (cl*kl-(ph-1))≤c*k-(p-1) := max_le (by omega) (by omega)
  have f : c*k-(p-1)≤ch*kh-(pl-1) := by omega
  have lower := mul_le_mul e pl' (by omega : 0≤pl) (by omega : 0≤c*k-(p-1))
  have upper := mul_le_mul f ph' pp (by omega : 0≤ch*kh-(pl-1))
  exact ⟨add_le_add first.1 lower,add_le_add first.2 upper⟩

end OMA.RankTwoPoleInterior245212

end

section

/- Certified endpoint bounds for interior prime ranges. Each test uses
integer budgets for the three tails of the simultaneous defect. -/
namespace OMA.RankTwoInteriorBox245212
open OMA.RankTwoPoleInterior245212 OMA.ComplementaryPole245212
open ArithmeticFunction OMA.SimultaneousBound245212
open scoped ArithmeticFunction.sigma

theorem no_exact {A B C P Q G : ℕ} (pp : 0<P) (qp : 0<Q)
    (necessary : P*Q≤G*(A*Q+B*P+C)) (a : 3*G*A<P) (b : 3*G*B<Q)
    (c : 3*G*C<P*Q) : False := by
  nlinarith only [necessary,Nat.mul_lt_mul_of_pos_right a qp,Nat.mul_lt_mul_of_pos_right b pp,c]

theorem no_integer {A B C P Q G F : ℕ} (pp : 0<P) (qp : 0<Q) (gp : 0<G)
    (necessary : 4*G*P*Q≤4*G*(A*Q+B*P+C)+F*P*Q)
    (a : 4*A<P) (b : 4*B<Q) (c : 4*C<P*Q) (drift : F<G) : False := by
  have three : 4*(A*Q+B*P+C)<3*P*Q := by
    nlinarith only [Nat.mul_lt_mul_of_pos_right a qp,Nat.mul_lt_mul_of_pos_right b pp,c]
  nlinarith only [necessary,Nat.mul_lt_mul_of_pos_left three gp,
    Nat.mul_lt_mul_of_pos_right drift (Nat.mul_pos pp qp)]

structure Cell where
  kl : ℕ
  kh : ℕ
  bl : ℕ
  bh : ℕ
  cl : ℕ
  ch : ℕ
  pl : ℕ
  ph : ℕ
  deriving Repr

def Fits (t : Cell) (K B C p : ℕ) : Prop :=
  t.kl≤K ∧ K≤t.kh ∧ t.bl≤B ∧ B≤t.bh ∧ t.cl≤C ∧ C≤t.ch ∧ t.pl≤p ∧ p≤t.ph

def gLow (t : Cell) := 2^t.kl-1
def gHigh (t : Cell) := 2^t.kh-1
def pLow (t : Cell) := t.pl^(t.bl-1)
def qLow (t : Cell) := (t.pl+2)^(t.cl-1)
def low (t : Cell) := lowPole ((t.kl:ℤ)-1) ((t.kh:ℤ)-1) t.bl t.bh t.cl t.ch t.pl t.ph
def high (t : Cell) := highPole ((t.kl:ℤ)-1) ((t.kh:ℤ)-1) t.bl t.bh t.cl t.ch t.pl t.ph
def e₁ (t : Cell) := (t.kh*t.ch*t.bh*(t.ph-1)+gLow t-1)/gLow t
def e₂ (t : Cell) := (t.ch*t.kh+pLow t-1)/pLow t
def gap (t : Cell) : ℤ := low t-e₁ t-e₂ t
def numerator (t : Cell) := 3*t.ch*t.bh*t.kh*(t.ph-1)^2
def yCap (t : Cell) := numerator t/(gap t).toNat

/-- The checks on the rounded witnesses make their calculation independent
of the proof of soundness. -/
def witness (t : Cell) : Bool := decide (
  t.kh*t.ch*t.bh*(t.ph-1)≤e₁ t*gLow t ∧ t.ch*t.kh≤e₂ t*pLow t ∧
  0<gap t ∧ numerator t<(yCap t+1)*(gap t).toNat)

def budget (t : Cell) (y : ℕ) : Bool :=
  let x := y^2*(t.kh*t.ch+t.ph)
  let z := t.ph^2*(t.kh*t.bh+y)
  let w := t.kh+t.ph*y
  let P := pLow t
  let Q := qLow t
  let G := gHigh t
  decide (3*G*x<P ∧ 3*G*z<Q ∧ 3*G*w<P*Q) ||
    decide (4*x<P ∧ 4*z<Q ∧ 4*w<P*Q ∧ 9*t.kh*t.ph^2*y^2*t.bh*t.ch<gLow t)

def veto (t : Cell) : Bool :=
  decide (high t≤0) || (witness t && (decide (yCap t<t.pl+2) || budget t (yCap t)))

theorem budget_false {t : Cell} {p q K B C P Q G y : ℕ}
    (fit : Fits t K B C p) (qy : q≤y)
    (pp : 0<P) (qp : 0<Q) (gp : 0<G)
    (rp : pLow t≤P) (rq : qLow t≤Q) (gl : gLow t≤G) (gh : G≤gHigh t)
    (ex : P*Q≤G*error p q K B C P Q)
    (int : 4*G*P*Q≤4*G*error p q K B C P Q+9*K*p^2*q^2*B*C*P*Q) :
    budget t y=false := by
  obtain ⟨_,kh,_,bh,_,ch,_,ph⟩ := fit
  have ae : q^2*(K*C+p)≤y^2*(t.kh*t.ch+t.ph) := by gcongr
  have be : p^2*(K*B+q)≤t.ph^2*(t.kh*t.bh+y) := by gcongr
  have ce : K+p*q≤t.kh+t.ph*y := by gcongr
  have de : 9*K*p^2*q^2*B*C≤9*t.kh*t.ph^2*y^2*t.bh*t.ch := by gcongr
  have prod := Nat.mul_le_mul rp rq
  by_contra! bad
  have ok : budget t y=true := Bool.eq_true_of_not_eq_false bad
  simp only [budget,Bool.or_eq_true,decide_eq_true_eq] at ok
  rcases ok with ⟨a,b,c⟩ | ⟨a,b,c,d⟩
  · apply no_exact pp qp (by simpa [error,add_assoc] using ex)
    · exact (Nat.mul_le_mul (Nat.mul_le_mul_left _ gh) ae).trans_lt (a.trans_le rp)
    · exact (Nat.mul_le_mul (Nat.mul_le_mul_left _ gh) be).trans_lt (b.trans_le rq)
    · exact (Nat.mul_le_mul (Nat.mul_le_mul_left _ gh) ce).trans_lt (c.trans_le prod)
  · apply no_integer pp qp gp (by simpa [error,add_assoc] using int)
    · exact (Nat.mul_le_mul_left _ ae).trans_lt (a.trans_le rp)
    · exact (Nat.mul_le_mul_left _ be).trans_lt (b.trans_le rq)
    · exact (Nat.mul_le_mul_left _ ce).trans_lt (c.trans_le prod)
    · exact de.trans_lt (d.trans_le gl)


theorem veto_false {t : Cell} {p q a d k : ℕ}
    (hp : p.Prime) (hq : q.Prime) (op : 3≤p) (pq : p+2≤q) (ha : 2≤a)
    (kl : 1≤t.kl) (pl : 1≤t.pl) (fit : Fits t (k+1) (a+1) (d+2) p)
    (small : (p:ℤ)-1≤((d:ℤ)+2)*k)
    (eqn : OeisA245212.a (2^k*p^a*q^(d+1))=(σ 1 (2^k*p^a*q^(d+1)):ℤ))
    (ex : p^a*q^(d+1)≤(2^(k+1)-1)*error p q (k+1) (a+1) (d+2) (p^a) (q^(d+1)))
    (int : 4*(2^(k+1)-1)*p^a*q^(d+1)≤4*(2^(k+1)-1)*error p q (k+1) (a+1) (d+2) (p^a) (q^(d+1))+
      9*(k+1)*p^2*q^2*(a+1)*(d+2)*p^a*q^(d+1)) : veto t=false := by
  obtain ⟨k₀,k₁,b₀,b₁,c₀,c₁,p₀,p₁⟩ := fit
  have qpos := hq.pos
  have ppos := hp.pos
  have rp : pLow t≤p^a := by
    exact (Nat.pow_le_pow_left p₀ _).trans (Nat.pow_le_pow_right hp.pos (by omega))
  have rq : qLow t≤q^(d+1) := by
    exact (Nat.pow_le_pow_left (by omega : t.pl+2≤q) _).trans
      (Nat.pow_le_pow_right hq.pos (by omega))
  have gl : gLow t≤2^(k+1)-1 :=
    Nat.sub_le_sub_right (Nat.pow_le_pow_right (by decide) k₀) 1
  have gh : 2^(k+1)-1≤gHigh t :=
    Nat.sub_le_sub_right (Nat.pow_le_pow_right (by decide) k₁) 1
  have pow2 : 2≤2^(k+1) := by simpa only [pow_one] using
    (Nat.pow_le_pow_right (by decide : 0<2) (by omega : 1≤k+1))
  have pole := point hp hq op (by omega) (by omega) ha small eqn
  dsimp only at pole
  have lim := pole_interval (p:=p) (b:=(a:ℤ)+1) (c:=(d:ℤ)+2) (k:=k)
    (kl:=(t.kl:ℤ)-1) (kh:=(t.kh:ℤ)-1) (bl:=t.bl) (bh:=t.bh) (cl:=t.cl)
    (ch:=t.ch) (pl:=t.pl) (ph:=t.ph)
    (by omega) (Int.natCast_nonneg _) (Int.natCast_nonneg _) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) small
  change low t≤L k p (a+1) (d+2) ∧ L k p (a+1) (d+2)≤high t at lim
  have pos := pole.1.trans_le lim.2
  by_cases test : witness t=true
  · have pieces := test
    simp only [witness,decide_eq_true_eq] at pieces
    obtain ⟨ex₁,ex₂,gapp,cover⟩ := pieces
    have xu : (k+1)*(d+2)*(a+1)*(p-1)≤e₁ t*(2^(k+1)-1) := calc
      _ ≤ t.kh*t.ch*t.bh*(t.ph-1) := by gcongr
      _ ≤ _ := ex₁.trans (Nat.mul_le_mul_left _ gl)
    have yu : (d+2)*(k+1)≤e₂ t*p^a :=
      (Nat.mul_le_mul c₁ k₁).trans (ex₂.trans (Nat.mul_le_mul_left _ rp))
    zify [Nat.cast_sub hp.pos,Nat.cast_sub (by omega : 1≤2^(k+1))] at xu
    have bound := pole.2 (e₁ t) (e₂ t) (by simpa [G,z,mul_assoc] using xu)
      (by exact_mod_cast yu)
    have gp : gap t≤L k p (a+1) (d+2)-(e₁ t+e₂ t) := by
      dsimp [gap];linarith only [lim.1]
    have num : 3*(d+2)*(k+1)*(a+1)*(p-1)^2≤numerator t := by
      unfold numerator
      rw [show 3*t.ch*t.bh*t.kh=3*t.ch*t.kh*t.bh by ring]
      gcongr
    zify [Nat.cast_sub hp.pos] at num
    have l : (q:ℤ)*gap t≤numerator t :=
      (mul_le_mul_of_nonneg_left gp (Int.natCast_nonneg q)).trans (bound.trans num)
    have yi : q≤yCap t := by
      have val : (((gap t).toNat:ℕ):ℤ)=gap t := Int.toNat_of_nonneg gapp.le
      rw [←val] at l
      have qg : q*(gap t).toNat≤numerator t := by exact_mod_cast l
      by_contra! bad
      exact (not_lt_of_ge (Nat.mul_le_mul_right _ (by omega : yCap t+1≤q))) (qg.trans_lt cover)
    have order : ¬yCap t<t.pl+2 := by omega
    have b := budget_false ⟨k₀,k₁,b₀,b₁,c₀,c₁,p₀,p₁⟩ yi (pow_pos ppos _) (pow_pos qpos _)
      (by omega : 0<2^(k+1)-1) rp rq gl gh ex int
    simp [veto,not_le_of_gt pos,test,order,b]
  · simp [veto,not_le_of_gt pos,Bool.eq_false_of_not_eq_true test]

end OMA.RankTwoInteriorBox245212

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

/- Deterministic exhaustive bisection. The exact last-prime check is a
fallback even if the recursion fuel is exhausted. Bounds are inclusive. -/
namespace OMA.RankTwoInteriorWalk245212
open OMA.RankTwoInteriorBox245212

def trim (t : Cell) : Cell :=
  {t with pl:=max t.pl (1+(t.kl-1)*(t.bl-1)/t.bl), ph:=min t.ph (3*t.kh)}

def exact (t : Cell) : Bool := OMA.RankTwoReplay245212.slice (t.kl-1) (t.kh-1)
  t.pl t.ph (t.bl-1) (t.bh-1) (t.cl-1) (t.ch-1)

def spend (t : Cell) :=
  (t.kh+1-t.kl)*(t.bh+1-t.bl)*(t.ch+1-t.cl)*(t.ph+1-t.pl)

def cut (a b : ℕ) := if 2*a≤b then Nat.sqrt (a*b) else (a+b)/2

def halves (t : Cell) : Cell × Cell :=
  let wk := t.kh-t.kl
  let wb := t.bh-t.bl
  let wc := t.ch-t.cl
  let wp := (t.ph-t.pl)/7
  if 3*t.kl<t.kh || (wk≥max wp (max wb wc) && 0<wk) then
    let j := cut t.kl t.kh
    ({t with kh:=j},{t with kl:=j+1})
  else if 3*t.bl<t.bh || (wb≥max wp wc && 0<wb) then
    let j := cut t.bl t.bh
    ({t with bh:=j},{t with bl:=j+1})
  else if 3*t.cl<t.ch || (wc≥wp && 0<wc) then
    let j := cut t.cl t.ch
    ({t with ch:=j},{t with cl:=j+1})
  else
    let j := (t.pl+t.ph)/2
    ({t with ph:=j},{t with pl:=j+1})

def easy (t : Cell) : Bool :=
  decide (t.ph<t.pl) || OMA.OddBox245212.veto t.kl t.kh t.bl t.bh t.cl t.ch t.pl t.ph ||
    veto t

def check (fuel : ℕ) (raw : Cell) : Bool :=
  let t := trim raw
  if easy t then true else
  match fuel with
  | 0 => exact t
  | fuel+1 =>
    if spend t≤160 then exact t else
    let (l,r) := halves t
    check fuel l && check fuel r

def root (m kl kh : ℕ) (swap : Bool) : Cell :=
  if swap then ⟨kl,kh,m,m,m+1,225,13,3*kh⟩ else ⟨kl,kh,m,225,m,m,13,3*kh⟩

def test (m kl kh : ℕ) := check 40 (root m kl kh false) && check 40 (root m kl kh true)

def Good (t : Cell) := 0<t.kl ∧ 0<t.bl ∧ 0<t.pl

theorem split_covers {t : Cell} {K B C p : ℕ} (h : Fits t K B C p) (g : Good t) :
    (Fits (halves t).1 K B C p ∧ Good (halves t).1) ∨
    (Fits (halves t).2 K B C p ∧ Good (halves t).2) := by
  unfold halves
  dsimp only
  split
  · simp only [Fits,Good] at *;omega
  · split
    · simp only [Fits,Good] at *;omega
    · split <;> simp only [Fits,Good] at * <;> omega

theorem trim_fits {t : Cell} {k B C p : ℕ} (h : Fits t (k+1) B C p) (g : Good t)
    (floor : ∀ j, 0<j → j≤B → 1+k*(j-1)/j≤p) (upper : p≤3*(k+1)) :
    Fits (trim t) (k+1) B C p ∧ Good (trim t) := by
  obtain ⟨k₀,k₁,b₀,b₁,c₀,c₁,p₀,p₁⟩ := h
  have a := Nat.div_le_div_right (c:=t.bl) (Nat.mul_le_mul_right (t.bl-1) (show t.kl-1≤k by omega))
  have b := floor t.bl g.2.1 b₀
  have ceil : p≤3*t.kh := upper.trans (Nat.mul_le_mul_left 3 k₁)
  refine ⟨⟨k₀,k₁,b₀,b₁,c₀,c₁,max_le p₀ ?_,le_min p₁ ceil⟩,g.1,g.2.1,lt_of_lt_of_le g.2.2 (le_max_left ..)⟩
  exact (Nat.add_le_add_left a 1).trans b

/-- The recursion and the choice of split cannot omit a solution. If
fuel runs out, the exact slice still covers the whole remaining box. -/
theorem walk_false {k B C p : ℕ}
    (floor : ∀ j, 0<j → j≤B → 1+k*(j-1)/j≤p) (upper : p≤3*(k+1))
    (noEasy : ∀ t, Fits t (k+1) B C p → Good t → easy t=false)
    (noExact : ∀ t, Fits t (k+1) B C p → exact t=false) :
    ∀ fuel t, Fits t (k+1) B C p → Good t → check fuel t=false := by
  intro fuel
  induction fuel with
  | zero =>
    intro raw fit g
    obtain ⟨ft,gt⟩ := trim_fits fit g floor upper
    simp [check,noEasy _ ft gt,noExact _ ft]
  | succ fuel ih =>
    intro raw fit g
    obtain ⟨ft,gt⟩ := trim_fits fit g floor upper
    simp only [check,noEasy _ ft gt,Bool.false_eq_true,ite_false]
    split
    · exact noExact _ ft
    · obtain ⟨fl,gl⟩ | ⟨fr,gr⟩ := split_covers ft gt
      · simp [ih _ fl gl]
      · simp [ih _ fr gr]


open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- An actual solution survives the three arithmetic tests needed by the
closed-cell certificates, regardless of a cell's ancestry. -/
theorem solution_facts {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (op : 13≤p) (pq : p+2≤q) (dk : 5≤k) (ea : 5≤a) (ed : 4≤d) (upper : p≤3*(k+1))
    (generic : ∀ s, Fits s (k+1) (a+1) (d+2) p →
      OeisA245212.a (2^k*p^a*q^(d+1))=(σ 1 (2^k*p^a*q^(d+1)):ℤ) →
      OMA.OddBox245212.veto s.kl s.kh s.bl s.bh s.cl s.ch s.pl s.ph=false)
    (eqn : OeisA245212.a (2^k*p^a*q^(d+1))=(σ 1 (2^k*p^a*q^(d+1)):ℤ)) :
    (∀ j, 0<j → j≤a+1 → 1+k*(j-1)/j≤p) ∧
    (∀ s, Fits s (k+1) (a+1) (d+2) p → Good s → easy s=false) ∧
    (∀ s, Fits s (k+1) (a+1) (d+2) p → exact s=false) := by
  have po : 3≤p := by omega
  have qo : 3≤q := by omega
  have plq : p<q := by omega
  have pos : (p:ℤ)-1<(k:ℤ)*(d+1) := by
    have ub : (p:ℤ)≤3*(k+1) := by exact_mod_cast upper
    nlinarith only [ub,mul_nonneg (by positivity : (0:ℤ)≤k) (by omega : (0:ℤ)≤d-4),
      (show (5:ℤ)≤k by exact_mod_cast dk)]
  have small : (p:ℤ)-1≤((d:ℤ)+2)*k := by nlinarith only [pos,Int.natCast_nonneg k]
  have sep := OMA.OddBox245212.separations hp hq po plq (by omega : 1≤a)
    (by omega : 1≤d+1) (by omega : 2≤k) (by exact_mod_cast pos) eqn
  have bd := OMA.SimultaneousBound245212.of_separations hp hq po qo plq.ne eqn sep.1 sep.2
  have floor (j : ℕ) (j0 : 0<j) (jb : j≤a+1) : 1+k*(j-1)/j≤p := by
    have f := OMA.TwoOddParameters245212.floor hp hq po qo plq.ne (by omega : 1≤a) j0 jb eqn
    exact (le_max_right _ _).trans (by simpa [OMA.TwoOddEffectiveTable245212.floorPrime] using f)
  have noEasy (s : Cell) (fs : Fits s (k+1) (a+1) (d+2) p) (gs : Good s) : easy s=false := by
    have order : ¬s.ph<s.pl := by obtain ⟨_,_,_,_,_,_,l,r⟩:=fs;omega
    have v := veto_false hp hq po pq (by omega : 2≤a) gs.1 gs.2.2 fs small eqn bd.1 bd.2
    simp [easy,order,generic s fs eqn,v]
  have noExact (s : Cell) (fs : Fits s (k+1) (a+1) (d+2) p) : exact s=false := by
    obtain ⟨k₀,k₁,b₀,b₁,c₀,c₁,p₀,p₁⟩ := fs
    by_contra! bad
    have checked := Bool.eq_true_of_not_eq_false bad
    exact OMA.RankTwoReplay245212.of_slice hp (by omega) hq plq (by omega : 0<d+1) p₀ p₁
      (by omega : s.kl-1 ≤ k) (by omega : k ≤ s.kh-1) (by omega : s.bl-1 ≤ a)
      (by omega : a ≤ s.bh-1) (by omega : s.cl-1 ≤ d+1) (by omega : d+1 ≤ s.ch-1) checked eqn
  exact ⟨floor,noEasy,noExact⟩

/-- Point, range and recursion soundness composed at the original OEIS
statement. The shared generic exterior veto can be supplied independently
of the sharper interior pole calculation and the final digit checks. -/
theorem original_of_check {t : Cell} {p q a d k fuel : ℕ}
    (hp : p.Prime) (hq : q.Prime) (op : 13≤p) (pq : p+2≤q)
    (dk : 5≤k) (ea : 5≤a) (ed : 4≤d) (upper : p≤3*(k+1))
    (fit : Fits t (k+1) (a+1) (d+2) p) (good : Good t)
    (generic : ∀ s, Fits s (k+1) (a+1) (d+2) p →
      OeisA245212.a (2^k*p^a*q^(d+1))=(σ 1 (2^k*p^a*q^(d+1)):ℤ) →
      OMA.OddBox245212.veto s.kl s.kh s.bl s.bh s.cl s.ch s.pl s.ph=false)
    (ok : check fuel t=true) :
    OeisA245212.a (2^k*p^a*q^(d+1))≠(σ 1 (2^k*p^a*q^(d+1)):ℤ) := by
  intro eqn
  obtain ⟨floor,noEasy,noExact⟩ := solution_facts hp hq op pq dk ea ed upper generic eqn
  have nope := walk_false floor upper noEasy noExact fuel t fit good
  simp [ok] at nope


end OMA.RankTwoInteriorWalk245212

end

section

/- Arithmetic checkpoints carry literal interval endpoints. Adjacent
checkpoints compose by one checked bisection, so the kernel need not
reconstruct a large ancestry while reducing an expensive leaf. -/
namespace OMA.RankTwoInteriorCover245212
open OMA.RankTwoInteriorBox245212 OMA.RankTwoInteriorWalk245212
open OMA.RankTwoInteriorWalk245212 (split_covers)

deriving instance DecidableEq for OMA.RankTwoInteriorBox245212.Cell

structure World where
  k : ℕ
  B : ℕ
  C : ℕ
  p : ℕ
  floor : ∀ j, 0<j → j≤B → 1+k*(j-1)/j≤p
  upper : p≤3*(k+1)
  noEasy : ∀ t, Fits t (k+1) B C p → Good t → easy t=false
  noExact : ∀ t, Fits t (k+1) B C p → exact t=false

def Closed (t : Cell) := ∀ w : World, Fits t (w.k+1) w.B w.C w.p → Good t → False

theorem tile (t : Cell) (ok : check 40 t=true) : Closed t := by
  intro w ft gt
  have h := walk_false w.floor w.upper w.noEasy w.noExact 40 t ft gt
  simp [ok] at h

/-- A replay certificate records which inexpensive obstruction worked. The
kernel need not evaluate the unsuccessful tests earlier in the search. -/
inductive Reason where
  | empty | pole | exterior | arithmetic
  deriving Repr

def certificate (r : Reason) (t : Cell) : Bool :=
  match r with
  | .empty => decide (t.ph<t.pl)
  | .pole => OMA.RankTwoInteriorBox245212.veto t
  | .exterior => OMA.OddBox245212.veto t.kl t.kh t.bl t.bh t.cl t.ch t.pl t.ph
  | .arithmetic => exact t

theorem certify {r : Reason} (raw t : Cell) (same : trim raw=t)
    (ok : certificate r t=true) : Closed raw := by
  intro w ft gt
  obtain ⟨f,g⟩ := trim_fits ft gt w.floor w.upper
  rw [same] at f g
  have e := w.noEasy t f g
  have a := w.noExact t f
  cases r <;> simp_all [certificate,easy]
  exact (Nat.not_lt_of_ge e.1.1) ok

theorem join (t : Cell) {l r : Cell} (left : Closed l) (right : Closed r)
    (ident : halves (trim t)=(l,r)) : Closed t := by
  intro w ft gt
  obtain ⟨f,g⟩ := trim_fits ft gt w.floor w.upper
  have sub := OMA.RankTwoInteriorWalk245212.split_covers f g
  rw [ident] at sub
  exact sub.elim (fun h => left w h.1 h.2) (fun h => right w h.1 h.2)

/-- A small proof tree of the successful arithmetic tests only. -/
inductive Script where
  | leaf : Reason → Script
  | fork : Script → Script → Script

def verify : Script → Cell → Bool
  | .leaf r, t => certificate r (trim t)
  | .fork l r, t =>
    let (a,b) := halves (trim t)
    verify l a && verify r b

theorem of_script (s : Script) (t : Cell) (ok : verify s t=true) : Closed t := by
  induction s generalizing t with
  | leaf r => exact certify t _ rfl ok
  | fork l r il ir =>
    simp only [verify,Bool.and_eq_true] at ok
    exact join t (il _ ok.1) (ir _ ok.2) rfl

end OMA.RankTwoInteriorCover245212

end

section

/- The two sets of 27 root certificates suffice for the entire
large-exponent two-odd-prime sector of the original divisor equation. -/
namespace OMA.RankTwoOriginalCover245212
open OMA.RankTwoInteriorBox245212 OMA.RankTwoInteriorWalk245212 OMA.RankTwoInteriorCover245212
open scoped ArithmeticFunction.sigma

theorem of_roots
    (closed : ∀ m : ℕ, 6 ≤ m → m ≤ 32 → ∀ swap : Bool, Closed (root m 6 1250 swap))
    {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 13 ≤ p)
    (pq : p<q) (ha : 5≤a) (hd : 5≤d) :
    OeisA245212.a (2^k*p^a*q^d)≠(σ 1 (2^k*p^a*q^d):ℤ) := by
  intro eqn
  obtain ⟨e,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : d≠0)
  obtain ⟨K0,K1,exp⟩:=OMA.OddBox245212.original hp hq op pq ha hd eqn
  have minb := OMA.TwoOddEffectiveOriginal245212.bound hp hq (by omega) pq (by omega) eqn
  have pbound := OMA.OddBox245212.prime_bound hp hq op pq ha hd eqn
  have upper : p≤3*(k+1) := by omega
  obtain ⟨i,pi⟩ := hp.odd_of_ne_two (by omega)
  obtain ⟨j,qj⟩ := hq.odd_of_ne_two (by omega)
  have gap : p+2≤q := by omega
  have generic (s : Cell) (fit : Fits s (k+1) (a+1) (e+2) p)
      (balance : OeisA245212.a (2^k*p^a*q^(e+1))=(σ 1 (2^k*p^a*q^(e+1)):ℤ)) :
      OMA.OddBox245212.veto s.kl s.kh s.bl s.bh s.cl s.ch s.pl s.ph=false := by
    obtain ⟨lK,hK,lB,hB,lC,hC,lp,rp⟩:=fit
    exact OMA.OddBox245212.veto_false hp hq op pq ha hd balance lK hK lB hB lC hC lp rp
  obtain ⟨floor,easy,exactS⟩:=solution_facts hp hq op gap (by omega) ha (by omega) upper generic eqn
  let w : World := ⟨k,a+1,e+2,p,floor,upper,easy,exactS⟩
  have cover (m : ℕ) (dir : Bool) (lo : 6 ≤ m) (hi : m≤32) (fit : Fits (root m 6 1250 dir) (k+1) (a+1) (e+2) p) : False :=
    closed m lo hi dir w fit (by cases dir <;> simp [Good,root] <;> omega)
  by_cases h : e+2≤a+1
  · apply cover (e+2) false (by omega) (by omega)
    simp only [root,Bool.false_eq_true,↓reduceIte,Fits];omega
  · apply cover (a+1) true (by omega) (by omega)
    simp only [root,↓reduceIte,Fits];omega

end OMA.RankTwoOriginalCover245212

end

#print axioms OMA.RankTwoOriginalCover245212.of_roots
