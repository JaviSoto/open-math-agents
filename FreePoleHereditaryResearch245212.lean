import FormalConjectures.OEIS.«245212»



/-! OEIS A245212: hereditary separation and polynomial bounds after a singleton Euler pole. -/

section

/- An explicit uniform distance from a rational target to Euler products
of bounded length, provided none of their subproducts hits the target. -/
namespace OMA.CofactorEulerSeparation245212
open Finset Nat

def num (s : Finset ℕ) := ∏p∈s,p
def den (s : Finset ℕ) := ∏p∈s,(p-1)
def gap (A H : ℕ) (s : Finset ℕ) := ((A:ℤ)*num s-(H:ℤ)*den s).natAbs
def miss (A H : ℕ) (s : Finset ℕ) := ∀t⊆s,A*num t≠H*den t

def budget (A : ℕ) : ℕ→ℕ
  | 0=>1
  | r+1=>let b:=budget A r;max (2*b) ((2+2*A*2^r*b)^(r+1))

theorem budget_pos (A r : ℕ) : 0<budget A r := by
  induction r with
  | zero=>simp [budget]
  | succ r ih=>exact (Nat.mul_pos (by decide) ih).trans_le (le_max_left _ _)

private theorem gap_pos {A H : ℕ} {s : Finset ℕ} (m : A*num s≠H*den s) : 0<gap A H s := by
  apply Int.natAbs_pos.mpr
  intro z
  exact m (by exact_mod_cast sub_eq_zero.mp z)

theorem size {s : Finset ℕ} (positive : ∀p∈s,2≤p) : num s≤2^s.card*den s := by
  calc
    num s ≤ ∏p∈s,(2*(p-1)) := by
      apply prod_le_prod'
      intro p mem;have:=positive p mem;omega
    _ = _ := by simp [den,prod_mul_distrib]

private theorem spread {u x z : ℤ} (u0 : 0≤u) (x0 : 0≤x) (large : 2*x≤u*|z|) :
    u*|z|≤2*|u*z+x| := by
  have tri:=abs_add_le (u*z+x) (-x)
  rw [add_neg_cancel_right,abs_mul,abs_of_nonneg u0,abs_neg,abs_of_nonneg x0] at tri
  linarith

theorem separated (A H K : ℕ) (s : Finset ℕ) (card : s.card≤K)
    (positive : ∀p∈s,2≤p) (apart : miss A H s) : den s≤budget A K*gap A H s := by
  classical
  induction K generalizing s with
  | zero=>
    have empty : s=∅:=card_eq_zero.mp (by omega)
    subst s
    simpa [den,budget] using Nat.succ_le_of_lt (gap_pos (apart ∅ (by simp)))
  | succ K ih=>
    by_cases empty : s=∅
    · subst s
      simpa [den] using Nat.succ_le_of_lt (Nat.mul_pos (budget_pos A (K+1)) (gap_pos (apart ∅ (by simp))))
    have nonempty:=nonempty_iff_ne_empty.mpr empty
    let q:=s.max' nonempty
    have mem : q∈s:=s.max'_mem _
    have qp:=positive q mem
    let t:=s.erase q
    have sub : t⊆s:=erase_subset _ _
    have oldBound:=ih t (by dsimp [t];rw [card_erase_of_mem mem];omega)
      (fun p hp=>positive p (sub hp)) (fun z hz=>apart z (hz.trans sub))
    have scale:=size (s:=t) (fun p hp=>positive p (sub hp))
    have tc : t.card≤K := by dsimp [t];rw [card_erase_of_mem mem];omega
    let B:=budget A K
    have U : num s=q*num t := (mul_prod_erase s (fun p=>p) mem).symm
    have V : den s=(q-1)*den t := (mul_prod_erase s (fun p=>p-1) mem).symm
    by_cases large : 2*A*2^K*B≤q-1
    · have twice : 2*A*num t≤(q-1)*gap A H t := by
        calc
          _ ≤ 2*A*(2^K*(B*gap A H t)) := Nat.mul_le_mul_left _ (scale.trans
            (Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) tc) oldBound))
          _ = (2*A*2^K*B)*gap A H t := by ring
          _ ≤ _ := Nat.mul_le_mul_right _ large
      have twiceInt : 2*((A:ℤ)*num t)≤((q-1:ℕ):ℤ)*|(A:ℤ)*num t-(H:ℤ)*den t| := by
        have cast:=Int.ofNat_le.mpr twice
        simpa only [gap,Nat.cast_mul,Nat.cast_ofNat,Int.natCast_natAbs,mul_assoc] using cast
      have pre:=spread (u:=((q-1:ℕ):ℤ)) (x:=(A:ℤ)*num t) (z:=(A:ℤ)*num t-(H:ℤ)*den t)
        (by positivity) (by positivity) twiceInt
      have id : ((q-1:ℕ):ℤ)*((A:ℤ)*num t-(H:ℤ)*den t)+A*num t=(A:ℤ)*num s-(H:ℤ)*den s := by
        rw [U,V];push_cast [Nat.cast_sub (show 1≤q by omega)];ring
      rw [id] at pre
      have control : (q-1)*gap A H t≤2*gap A H s := by
        apply Int.ofNat_le.mp
        simpa [gap,Int.natCast_natAbs] using pre
      calc
        den s ≤ (q-1)*(B*gap A H t) := V ▸ Nat.mul_le_mul_left _ oldBound
        _ = B*((q-1)*gap A H t) := by ring
        _ ≤ B*(2*gap A H s) := Nat.mul_le_mul_left _ control
        _ = (2*B)*gap A H s := by ring
        _ ≤ _ := Nat.mul_le_mul_right _ (le_max_left _ _)
    · let J:=2+2*A*2^K*B
      have lo : 0<J := by dsimp [J];omega
      have modest : den s≤J^(K+1) := by
        refine (prod_le_pow_card s (fun p=>p-1) J ?_).trans (Nat.pow_le_pow_right lo card)
        intro p hp
        have below : p≤q:=s.le_max' p hp
        dsimp [J];omega
      have nonzero := gap_pos (apart s (Subset.rfl))
      exact modest.trans ((le_max_right _ _).trans (Nat.le_mul_of_pos_right _ nonzero))


theorem miss_odd {A H : ℕ} {s : Finset ℕ} (oa : Odd A) (eh : Even H)
    (pr : ∀p∈s,Odd p) : miss A H s := by
  intro t ht eqn
  have all (u : Finset ℕ) (ho : ∀p∈u,Odd p) : Odd (num u) := by
    induction u using Finset.induction_on with
    | empty=>simp [num]
    | @insert p u fresh ih=>
      rw [num,prod_insert fresh]
      exact (ho p (mem_insert_self ..)).mul (ih (fun q hq=>ho q (mem_insert_of_mem hq)))
  have left:=oa.mul (all t (fun p hp=>pr p (ht hp)))
  rw [eqn] at left
  exact (Nat.not_even_iff_odd.mpr left) (eh.mul_right _)

theorem miss_avoids {A H : ℕ} {s : Finset ℕ} (different : A≠H)
    (pr : ∀p∈s,p.Prime) (avoid : ∀p∈s,¬p∣H) : miss A H s := by
  intro t ht eqn
  by_cases empty : t=∅
  · exact different (by simpa [empty,num,den] using eqn)
  have nonempty:=nonempty_iff_ne_empty.mpr empty
  let q:=t.max' nonempty
  have mq : q∈t:=t.max'_mem _
  have pq:=pr q (ht mq)
  have dvd : q∣H*den t := eqn ▸ dvd_mul_of_dvd_right (dvd_prod_of_mem (fun p=>p) mq) A
  rcases pq.dvd_mul.mp dvd with bad|denom
  · exact avoid q (ht mq) bad
  obtain ⟨p,mp,dv⟩:=(pq.prime.dvd_finsetProd_iff (fun j=>j-1)).mp denom
  have upper : p≤q:=t.le_max' _ mp
  have lower:=(pr p (ht mp)).one_lt
  have:=Nat.le_of_dvd (show 0<p-1 by omega) dv
  omega

/-- A computable absolute gap, uniform over all allowed support sets. -/
theorem rational_gap {A H K : ℕ} {s : Finset ℕ} (card : s.card≤K)
    (positive : ∀p∈s,2≤p) (apart : miss A H s) :
    1 ≤ (budget A K:ℚ)*|(A:ℚ)*((num s:ℚ)/den s)-H| := by
  have n:=separated A H K s card positive apart
  have dp : 0<den s := prod_pos (fun p hp=>by have:=positive p hp;omega)
  have v : (0:ℚ)<den s := by exact_mod_cast dp
  let u : ℤ:=(A:ℤ)*num s-(H:ℤ)*den s
  have cast : (den s:ℚ)≤(budget A K:ℚ)*|(u:ℚ)| := by
    have intBound:=Int.ofNat_le.mpr n
    simp only [gap,Nat.cast_mul,Int.natCast_natAbs] at intBound
    dsimp [u]
    exact_mod_cast intBound
  have eqn : ((A:ℚ)*((num s:ℚ)/den s)-H)*(den s:ℚ)=(u:ℚ) := by
    dsimp [u];push_cast;field_simp
  apply (mul_le_mul_iff_of_pos_right v).mp
  have ab:=congrArg (fun z:ℚ=>|z|) eqn
  rw [abs_mul,abs_of_pos v] at ab
  simpa only [one_mul,mul_assoc,ab] using cast

end OMA.CofactorEulerSeparation245212

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


end OMA.CofactorPairPole245212

end

section

/- After a singleton Euler resonance, adjoining any power of that prime
breaks every further fresh-subset resonance, with a quantitative gap. -/
namespace OMA.FreePoleHereditary245212
open Nat Finset ArithmeticFunction OMA.Smooth245212 OMA.CofactorEulerSeparation245212
open scoped ArithmeticFunction.sigma

def lead (u B N D : ℤ) := N-u*B*(N-D)
def drift (g N D : ℕ) : ℤ := 2*((g:ℤ)*σ 0 g)*D-(W g:ℤ)*N

theorem positive {h : ℕ} (hh : 0<h) : 0<W h := by
  rw [w_apply];exact sum_pos' (fun _ _=>Nat.zero_le _) ⟨1,Nat.one_mem_divisors.mpr hh.ne',by simp⟩

theorem algebra {h p a : ℕ} (hp : p.Prime) (cp : h.Coprime p) (N D : ℕ)
    (pole : W h*p=2*(h*σ 0 h)*(p-1)) :
    ((p:ℤ)-1)^2*drift (h*p^a) N D =
      (W h:ℤ)*(p*(p:ℤ)^a*lead ((p:ℤ)-1) ((a:ℤ)+1) N D-N) := by
  have pp:=hp.pos
  have res : (W h:ℤ)*p=2*((h:ℤ)*σ 0 h)*(p-1) := by
    zify [Nat.cast_sub hp.pos] at pole;simpa only [mul_assoc] using pole
  have wx:=OMA.ComplementaryLocal245212.moments hp a
  unfold drift lead
  rw [w_mult.map_mul_of_coprime (cp.pow_right a),isMultiplicative_sigma.map_mul_of_coprime (cp.pow_right a),
    sigma_zero_apply_prime_pow hp]
  push_cast
  linear_combination ((p:ℤ)-1)*((a:ℤ)+1)*(p:ℤ)^a*(D:ℤ)*(-res) - (W h:ℤ)*(N:ℤ)*wx.2

theorem no_zero {h p a N D : ℕ} (hh : 0<h) (hp : p.Prime) (cp : h.Coprime p) (fresh : ¬p∣N)
    (pole : W h*p=2*(h*σ 0 h)*(p-1)) : drift (h*p^a) N D≠0 := by
  intro z
  have eq:=algebra (a:=a) hp cp N D pole
  rw [z,mul_zero] at eq
  have az : (W h:ℤ)≠0 := by exact_mod_cast (positive hh).ne'
  have prod:=Or.resolve_left (mul_eq_zero.mp eq.symm) az
  have div : (p:ℤ)∣N := ⟨(p:ℤ)^a*lead ((p:ℤ)-1) ((a:ℤ)+1) N D,by
    exact (sub_eq_zero.mp prod).symm.trans (mul_assoc ..)⟩
  exact fresh (by exact_mod_cast div)

theorem inherited {h p a : ℕ} (hh : 0<h) (hp : p.Prime) (cp : h.Coprime p) (s : Finset ℕ)
    (fresh : ∀r∈s,¬p∣r) (pole : W h*p=2*(h*σ 0 h)*(p-1)) :
    miss (W (h*p^a)) (2*((h*p^a)*σ 0 (h*p^a))) s := by
  intro t ts hit
  have good : ¬p∣num t := by
    intro dv
    obtain ⟨r,rt,div⟩:=(Prime.dvd_finsetProd_iff hp.prime (fun r:ℕ=>r)).mp dv
    exact fresh r (ts rt) div
  apply no_zero (a:=a) (D:=den t) hh hp cp good pole
  apply sub_eq_zero.mpr
  exact_mod_cast hit.symm

theorem gap_of_odd {h p a N D : ℕ} (hp : p.Prime) (op : Odd p) (cp : h.Coprime p)
    (odd : Odd N) (pole : W h*p=2*(h*σ 0 h)*(p-1)) (size : 2*N≤p*p^a) :
    (W h:ℤ)*p*(p:ℤ)^a≤2*((p:ℤ)-1)^2*|drift (h*p^a) N D| := by
  let L := lead ((p:ℤ)-1) ((a:ℤ)+1) N D
  have nz : L≠0 := by
    obtain ⟨i,ip⟩:=op; obtain ⟨j,jn⟩:=odd
    have even : Even (((p:ℤ)-1)*((a:ℤ)+1)*((N:ℤ)-D)) :=
      ⟨(i:ℤ)*((a:ℤ)+1)*((N:ℤ)-D),by rw [ip];push_cast;ring⟩
    obtain ⟨k,ek⟩:=even
    dsimp [L,lead];rw [ek,jn];push_cast;omega
  have l1 : 1≤|L| := by have pos:=abs_pos.mpr nz;omega
  let V:ℤ:=p*(p:ℤ)^a
  have vp : 0≤V := by dsimp [V];positivity
  have largen : 2*(N:ℤ)≤V := by dsimp [V];exact_mod_cast size
  have tri':=abs_add_le (V*L-(N:ℤ)) (N:ℤ)
  rw [sub_add_cancel,abs_mul,abs_of_nonneg vp,abs_of_nonneg (Int.natCast_nonneg N)] at tri'
  have vv : V≤2*|V*L-(N:ℤ)| := by nlinarith only [tri',largen,mul_le_mul_of_nonneg_left l1 vp]
  have identity:=congrArg abs (algebra (a:=a) hp cp N D pole)
  rw [abs_mul,abs_of_nonneg (sq_nonneg _),abs_mul,abs_of_nonneg (Int.natCast_nonneg (W h))] at identity
  change _= (W h:ℤ)*|V*L-(N:ℤ)| at identity
  nlinarith only [identity,mul_le_mul_of_nonneg_left vv (Int.natCast_nonneg (W h))]

end OMA.FreePoleHereditary245212

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

/- Quantitative separation at every odd Euler subproduct after absorbing
a prime power on the original singleton pole. -/
namespace OMA.FreePoleSpread245212
open Nat Finset ArithmeticFunction OMA.Smooth245212 OMA.CofactorEulerSeparation245212
open OMA.FreePoleHereditary245212
open scoped ArithmeticFunction.sigma
open OMA.CofactorEulerSeparation245212 (size)
open OMA.CofactorEulerSeparation245212 (budget_pos)

private theorem perturbed {V N D C L : ℤ} (v : 0≤V) (n : 0≤N) (c : 0≤C)
    (gap : D≤C*|L|) (noise : 2*C*N≤V*D) : V*D≤2*C*|V*L-N| := by
  have triangle :=abs_add_le (V*L-N) N
  rw [sub_add_cancel,abs_mul,abs_of_nonneg v,abs_of_nonneg n] at triangle
  nlinarith only [noise,mul_le_mul_of_nonneg_left triangle c,mul_le_mul_of_nonneg_left gap v]

theorem uniform {h p a r : ℕ} (hp : p.Prime) (op : Odd p) (cp : h.Coprime p)
    (pole : W h*p=2*(h*σ 0 h)*(p-1)) (s : Finset ℕ) (order : s.card≤r)
    (odd : ∀q∈s,Odd q) (base : ∀q∈s,2≤q)
    (size : 2^(r+1)*budget ((p-1)*(a+1)-1) r ≤ p*p^a) :
    let C:=budget ((p-1)*(a+1)-1) r
    2*(C:ℤ)*((p:ℤ)-1)^2*|drift (h*p^a) (num s) (den s)| ≥ (W h:ℤ)*p*(p:ℤ)^a*den s := by
  let t:=(p-1)*(a+1)
  let c:=budget (t-1) r
  let N:=num s
  let D:=den s
  let L:=lead ((p:ℤ)-1) ((a:ℤ)+1) N D
  let V:ℤ:=p*(p:ℤ)^a
  have ueven : Even (p-1) := by obtain ⟨j,hj⟩:=op;exact ⟨j,by omega⟩
  have te : Even t := ueven.mul_right _
  have tpos : 0<t := Nat.mul_pos (by have := hp.one_lt;omega) (by omega)
  have to' : Odd (t-1) := by obtain ⟨i,hi⟩:=te;exact ⟨i-1,by omega⟩
  have sep:=separated (t-1) t r s order base (miss_odd to' te odd)
  have aeq : L = -(((t-1:ℕ):ℤ)*N-(t:ℤ)*D) := by
    change lead ((p:ℤ)-1) ((a:ℤ)+1) N D = _
    dsimp [lead,t]
    rw [Nat.cast_sub (tpos : 1≤(p-1)*(a+1))]
    dsimp [t];push_cast [Nat.cast_sub hp.pos];ring
  have g : (D:ℤ) ≤ (c:ℤ)*|L| := by
    dsimp [gap] at sep
    simpa only [aeq,abs_neg,←Int.natCast_natAbs,←Nat.cast_mul] using (Int.ofNat_le.mpr sep)
  have sizes:=OMA.CofactorEulerSeparation245212.size (s:=s) base
  have ns : N ≤ 2^r*D := sizes.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide : 0<2) order))
  have noi : 2*c*N≤p*p^a*D := by
    change 2^(r+1)*c≤p*p^a at size
    rw [pow_succ] at size
    nlinarith only [Nat.mul_le_mul_left (2*c) ns,Nat.mul_le_mul_right D size]
  have per:=perturbed (V:=V) (N:=(N:ℤ)) (by dsimp [V];positivity) (by positivity)
    (show 0≤(c:ℤ) by positivity) g (by dsimp [V];exact_mod_cast noi)
  have id:=congrArg abs (algebra (a:=a) hp cp N D pole)
  rw [abs_mul,abs_of_nonneg (sq_nonneg _),abs_mul,abs_of_nonneg (Int.natCast_nonneg (W h))] at id
  change _= (W h:ℤ)*|V*L-(N:ℤ)| at id
  change _ ≤ 2*(c:ℤ)*((p:ℤ)-1)^2*|drift (h*p^a) N D|
  nlinarith only [congrArg ((2*(c:ℤ))*·) id,mul_le_mul_of_nonneg_left per (Int.natCast_nonneg (W h))]

end OMA.FreePoleSpread245212

end

section

/- An explicit exponent from which the hereditary separation is polynomially uniform. -/
namespace OMA.FreePoleOnset245212
open Nat Finset ArithmeticFunction OMA.Smooth245212 OMA.CofactorEulerSeparation245212
open OMA.FreePoleHereditary245212 OMA.FreePoleSpread245212
open scoped ArithmeticFunction.sigma
open OMA.CofactorEulerSeparation245212 (budget_pos)

def exponent : ℕ→ℕ
  | 0 => 1
  | r+1 => (1+r+exponent r)*(r+1)

private theorem exp_pos (r : ℕ) : 0<exponent r := by
  cases r <;> simp [exponent]

theorem polynomial (A r : ℕ) : budget A r ≤ (4*(A+1))^(exponent r) := by
  let x:=4*(A+1)
  change budget A r ≤ x^(exponent r)
  have xpos : 1<x := by dsimp [x];omega
  induction r with
  | zero => simp [budget,exponent];omega
  | succ r ih =>
    let b:=budget A r
    let z:=2^r*b
    have zp : 0<z := Nat.mul_pos (pow_pos (by decide) r) (OMA.CofactorEulerSeparation245212.budget_pos A r)
    have major : 2+2*A*2^r*b≤x*z := by
      change 2+2*A*2^r*b≤(4*(A+1))*(2^r*b)
      dsimp [z] at zp
      nlinarith only [zp,Nat.zero_le (A*(2^r*b))]
    have zbound : z≤x^r*x^(exponent r) := Nat.mul_le_mul (Nat.pow_le_pow_left xpos r) ih
    have sm : 2*b≤x*z := by
      have e : b≤z:=Nat.le_mul_of_pos_left _ (pow_pos (by decide) r)
      nlinarith only [Nat.mul_le_mul_left 2 e,Nat.mul_le_mul_right z xpos]
    have all : x*z≤x^(1+r+exponent r) := by
      rw [pow_add,pow_add,pow_one]
      simpa [mul_assoc] using Nat.mul_le_mul_left x zbound
    have once : 1+r+exponent r ≤ exponent (r+1) := Nat.le_mul_of_pos_right _ (by omega)
    exact max_le (sm.trans (all.trans (Nat.pow_le_pow_right (by omega) once)))
      ((Nat.pow_le_pow_left (major.trans all) (r+1)).trans_eq (pow_mul x _ _).symm)

def onset (p r : ℕ) := max (16*(exponent r+1)^2) (2^(r+1)*(8*p)^(exponent r))

theorem large {p r a : ℕ} (hp : 2≤p) (high : onset p r ≤ a) :
    2^(r+1)*budget ((p-1)*(a+1)-1) r ≤ p*p^a := by
  let e:=exponent r
  let t:=(p-1)*(a+1)
  have ep : 0<e := exp_pos r
  obtain ⟨cut,coef⟩:= max_le_iff.mp high
  have ap : 1≤a := by nlinarith only [cut,Nat.zero_le ((exponent r)^2),Nat.zero_le (exponent r)]
  have tp : 1≤t := Nat.mul_pos (by omega) (by omega)
  have elementary : 4*(t-1+1)≤(8*p)*a := by
    rw [Nat.sub_add_cancel tp]
    dsimp [t]
    have h := Nat.mul_le_mul (show p-1≤p by omega) (show a+1≤2*a by omega)
    nlinarith only [h]
  have D := (polynomial (t-1) r).trans (Nat.pow_le_pow_left elementary e)
  change 2^(r+1)*budget (t-1) r ≤ p*p^a
  calc
    _ ≤ 2^(r+1)*((8*p)*a)^e := Nat.mul_le_mul_left _ D
    _ = (2^(r+1)*(8*p)^e)*a^e := by rw [mul_pow];ring
    _ ≤ a^e*a^e := Nat.mul_le_mul_right _ (coef.trans (Nat.le_self_pow (by omega) _))
    _ = a^(2*e) := by rw [two_mul,pow_add]
    _ ≤ 2^a := OMA.ComplementarySize245212.absorb cut
    _ ≤ p^a := Nat.pow_le_pow_left hp _
    _ ≤ p*p^a := Nat.le_mul_of_pos_left _ (by omega)

theorem original {h p a r : ℕ} (hp : p.Prime) (op : Odd p) (cp : h.Coprime p)
    (pole : W h*p=2*(h*σ 0 h)*(p-1)) (high : onset p r≤a) (s : Finset ℕ)
    (order : s.card≤r) (odd : ∀q∈s,Odd q) (base : ∀q∈s,2≤q) :
    2*(budget ((p-1)*(a+1)-1) r:ℤ)*((p:ℤ)-1)^2*
      |drift (h*p^a) (num s) (den s)| ≥ (W h:ℤ)*p*(p:ℤ)^a*den s :=
  uniform hp op cp pole s order odd base (large hp.two_le high)

end OMA.FreePoleOnset245212

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

/- A fresh least prime lies in an interval linear in the length
of the absorbed prime power, for arbitrarily many other prime factors. -/
namespace OMA.FreePoleLeast245212
open Nat Finset ArithmeticFunction OMA.Smooth245212
open scoped ArithmeticFunction.sigma
open OMA.CofactorHarmonic245212 (from_mass)
open OMA.FreePoleHereditary245212 (positive)

theorem exact_mass {h p a m q : ℕ} (hh : 0<h) (hp : p.Prime) (cp : h.Coprime p)
    (pole : W h*p=2*(h*σ 0 h)*(p-1)) (hm : 1 < m) (cop : (h*p^a).Coprime m)
    (lower : ∀x∈m.primeFactors,q≤x)
    (eqn : OeisA245212.a (h*p^a*m)=(σ 1 (h*p^a*m):ℤ)) :
    (σ 1 h)*(p-1)<W h*σ 0 m ∧
    q*(W h*σ 0 m-(σ 1 h)*(p-1)) ≤ m.primeFactors.card*(W h)*p*(a+1)*(σ 0 m) := by
  let u:=p-1
  let P:=p^a
  let U:=σ 1 P
  let A:=W h
  let S:=σ 1 h
  let t:=σ 0 m
  let R:=m.primeFactors.card
  let g:=h*P
  let H:=2*(g*σ 0 g)
  let d:=H*t-(W g*t+σ 1 g)
  have pp:=hp.pos
  have gp : 0<g := by dsimp [g,P];positivity
  have up : 0<u := by dsimp [u];have:=hp.one_lt;omega
  have upos : 0<U := sigma_pos 1 P (pow_ne_zero _ hp.ne_zero)
  have m0:=OMA.CofactorHarmonic245212.count_sensitive gp hm cop eqn
  change 0<d ∧ (d:ℚ)≤((H*t:ℕ):ℚ)*_ at m0
  have bound : q*d≤R*(H*t):=OMA.CofactorHarmonic245212.from_mass lower m0.2
  have add : d+(W g*t+σ 1 g)=H*t := Nat.sub_add_cancel (by have:=m0.1;dsimp [d] at this;omega)
  have localW:=OMA.PrimePowerDiv245212.weighted hp a
  have wt : u*W P+U=p*(a+1)*P := by
    dsimp [u,P,U];linear_combination localW
  have den : u*H=A*p*(a+1)*P := by
    dsimp [g,H,A,P,u]
    rw [isMultiplicative_sigma.map_mul_of_coprime (cp.pow_right a),sigma_zero_apply_prime_pow hp, pole]
    ring
  have num : u*(W g)+A*U=u*H := by
    rw [den];dsimp [g]
    rw [w_mult.map_mul_of_coprime (cp.pow_right a)]
    dsimp [A] at *
    nlinarith only [congrArg (W h*·) wt]
  have sig : σ 1 g=S*U := isMultiplicative_sigma.map_mul_of_coprime (cp.pow_right a)
  rw [sig] at add
  have identity : u*d+(S*u)*U=(A*t)*U := by
    nlinarith only [congrArg (u*·) add,congrArg (·*t) num]
  have strict : S*u<A*t := by
    apply Nat.lt_of_mul_lt_mul_right (a:=U)
    nlinarith only [identity,Nat.mul_pos up m0.1]
  have diff : (A*t-S*u)*U=u*d := by
    nlinarith only [identity,congrArg (·*U) (Nat.sub_add_cancel strict.le)]
  have pu : P≤U := by
    dsimp [U,P]; rw [sigma_one_apply_prime_pow hp,Finset.sum_range_succ];omega
  refine ⟨strict,?_⟩
  change q*(A*t-S*u)≤R*A*p*(a+1)*t
  apply Nat.le_of_mul_le_mul_right _ upos
  nlinarith only [congrArg (q*·) diff,Nat.mul_le_mul_left u bound,
    congrArg (fun z=>R*z*t) den,Nat.mul_le_mul_left (R*A*p*(a+1)*t) pu]

theorem upper {h p a m q : ℕ} (hh : 0<h) (hp : p.Prime) (cp : h.Coprime p)
    (pole : W h*p=2*(h*σ 0 h)*(p-1)) (hm : 1 < m) (cop : (h*p^a).Coprime m)
    (lower : ∀x∈m.primeFactors,q≤x)
    (eqn : OeisA245212.a (h*p^a*m)=(σ 1 (h*p^a*m):ℤ)) :
    q ≤ m.primeFactors.card * W h*p*((σ 1 h)*(p-1)+1)*(a+1) := by
  obtain ⟨strict,cap⟩:=exact_mass hh hp cp pole hm cop lower eqn
  let K:=(σ 1 h)*(p-1)
  let T:=σ 0 m
  let D:=W h*T-K
  let Z:=m.primeFactors.card*W h*p*(a+1)
  change K<W h*T at strict
  change q*D≤Z*T at cap
  have dp : 0<D := by dsimp [D]; omega
  have one : T≤(K+1)*D := by
    have eq:D+K=W h*T:=Nat.sub_add_cancel strict.le
    nlinarith only [eq,Nat.mul_le_mul_left K dp,Nat.mul_le_mul_right T (OMA.FreePoleHereditary245212.positive hh)]
  apply Nat.le_of_mul_le_mul_right _ dp
  have endcap:=cap.trans (Nat.mul_le_mul_left Z one)
  dsimp [Z,K] at endcap
  simpa only [mul_comm,mul_left_comm,mul_assoc] using endcap

end OMA.FreePoleLeast245212

end

section

/- At a singleton Euler pole, every fresh prime grows at least linearly
with the exponent length on the pole, independently of the other fresh primes. -/
namespace OMA.FreePoleLower245212
open Nat Finset ArithmeticFunction OMA.Smooth245212
open scoped ArithmeticFunction.sigma

private theorem prefix_lt {x z : ℕ} (hx : 0<x) (hz : 0<z) (cop : x.Coprime z)
    (eqn : OeisA245212.a (x*z)=(σ 1 (x*z):ℤ)) : W x<2*(x*σ 0 x) := by
  have all:=OMA.Abundance245212.balance (Nat.mul_pos hx hz).ne' eqn
  rw [w_mult.map_mul_of_coprime cop,isMultiplicative_sigma.map_mul_of_coprime cop,
    isMultiplicative_sigma.map_mul_of_coprime cop] at all
  have minw : z*σ 0 z≤W z := by
    rw [w_apply,sigma_zero_apply]
    exact single_le_sum (f:=fun d : ℕ=>d*d.divisors.card) (fun _ _=>Nat.zero_le _) (Nat.mem_divisors_self _ hz.ne')
  apply Nat.lt_of_mul_lt_mul_right (a:=z*σ 0 z)
  nlinarith only [all,Nat.mul_le_mul_left (W x) minw,
    Nat.mul_pos (sigma_pos 1 x hx.ne') (sigma_pos 1 z hz.ne')]

private theorem lower_scalar {p u B P U W q b Q V : ℤ}
    (bpos : 0<b) (qpos : 0<q) (Ppos : 0<P) (Qpos : 0<Q) (ppos : 0<p) (upos : 0<u)
    (Wpos : 0<W)
    (eq1 : u*U=p*P-1) (eq2 : u*W+U=p*B*P)
    (pref : u*W*V<p*B*P*(b+1)*Q)
    (tail : b*Q≤q*(V-(b+1)*Q)) : u*B*b<q*(b+1)+b := by
  have uWpos:=mul_pos upos Wpos
  have main : u*W*b<q*(b+1)*U := by
    apply lt_of_mul_lt_mul_right (a:=Q) _ Qpos.le
    nlinarith only [mul_le_mul_of_nonneg_left tail uWpos.le,
      mul_lt_mul_of_pos_left pref qpos,congrArg (fun t:ℤ=>q*(b+1)*Q*t) eq2]
  have add : p*P*B*b < (q*(b+1)+b)*U := by
    nlinarith only [main,congrArg (·*b) eq2]
  have nz : 0<q*(b+1)+b := by positivity
  apply lt_of_mul_lt_mul_right (a:=p*P) _ (mul_pos ppos Ppos).le
  nlinarith only [mul_lt_mul_of_pos_left add upos,congrArg ((q*(b+1)+b)*·) eq1,nz]

theorem original {h p a q b z : ℕ} (hh : 0<h) (hp : p.Prime) (hq : q.Prime)
    (oq : 3≤q) (cp : h.Coprime p) (cq : (h*p^a).Coprime q) (hz : 0<z)
    (cop : (h*p^a*q^(b+1)).Coprime z) (pole : W h*p=2*(h*σ 0 h)*(p-1))
    (eqn : OeisA245212.a (h*p^a*q^(b+1)*z)=(σ 1 (h*p^a*q^(b+1)*z):ℤ)) :
    (p-1)*(a+1)*(b+1)<q*(b+2)+(b+1) := by
  have two:=hp.two_le
  have pp:=hp.pos
  have qp:=hq.pos
  have pre:=prefix_lt (x:=h*p^a*q^(b+1)) (by positivity) hz cop eqn
  rw [w_mult.map_mul_of_coprime (cq.pow_right _),w_mult.map_mul_of_coprime (cp.pow_right a),
    isMultiplicative_sigma.map_mul_of_coprime (cq.pow_right _),isMultiplicative_sigma.map_mul_of_coprime (cp.pow_right a),
    sigma_zero_apply_prime_pow hp,sigma_zero_apply_prime_pow hq] at pre
  have w:=OMA.PrimePowerDiv245212.weighted hp a
  zify [Nat.cast_sub hp.pos] at w pole
  zify at pre
  have wh : (0:ℤ)<W h := by
    rw [w_apply]
    exact_mod_cast sum_pos' (f:=fun i:ℕ=>i*i.divisors.card) (fun _ _=>Nat.zero_le _)
      ⟨1,Nat.one_mem_divisors.mpr hh.ne',by simp⟩
  have base : ((p:ℤ)-1)*W (p^a)*W (q^(b+1)) < p*((a:ℤ)+1)*p^a*((b:ℤ)+1+1)*q^(b+1) := by
    apply lt_of_mul_lt_mul_left (a:=(W h:ℤ)) _ wh.le
    nlinarith only [mul_lt_mul_of_pos_left pre (by omega : (0:ℤ)<p-1),
      congrArg (fun t:ℤ=> t*((a:ℤ)+1)*p^a*((b:ℤ)+1+1)*q^(b+1)) pole]
  have Wpos : (0:ℤ)<W (p^a) := by
    rw [w_pow hp]
    exact_mod_cast (sum_pos' (f:=fun i:ℕ=>p^i*(i+1)) (fun _ _=>Nat.zero_le _)
      ⟨0,Finset.mem_range.mpr (by omega : 0<a+1),by simp⟩)
  have result:=lower_scalar (b:=(b:ℤ)+1) (by omega) (by omega : 0<(q:ℤ))
    (pow_pos (by omega : 0<(p:ℤ)) a) (pow_pos (by omega : 0<(q:ℤ)) (b+1))
    (by omega : 0<(p:ℤ)) (by omega : 0<(p:ℤ)-1) Wpos
    (OMA.ComplementaryLocal245212.moments hp a).1 (show ((p:ℤ)-1)*W (p^a)+σ 1 (p^a)=p*((a:ℤ)+1)*p^a by linear_combination w)
    base (by linarith only [(OMA.CofactorPairPole245212.last_tail hq oq b).1])
  zify [Nat.cast_sub hp.pos];linarith only [result]

end OMA.FreePoleLower245212

end

section

/- A binary divisibility obstruction to vanishing of the simultaneous
leading coefficient, after a singleton Euler resonance. -/
namespace OMA.FreePoleLeading245212
open Nat Finset OMA.CofactorEulerSeparation245212

private theorem v_mul {a b : ℕ} (ha : 0<a) (hb : 0<b) :
    (a*b).factorization 2=a.factorization 2+b.factorization 2 := by
  rw [Nat.factorization_mul ha.ne' hb.ne',Finsupp.add_apply]

private theorem v_odd {a : ℕ} (ha : Odd a) : a.factorization 2=0 :=
  factorization_eq_zero_of_not_dvd (Nat.not_even_iff_odd.mpr ha ∘ even_iff_two_dvd.mpr)

private theorem odd_prod' {s : Finset ℕ} (f : ℕ→ℕ) (all : ∀i∈s,Odd (f i)) :
    Odd (∏i∈s,f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s out ih =>
    rw [prod_insert out]
    exact (all i (mem_insert_self ..)).mul (ih (fun j hj=>all j (mem_insert_of_mem hj)))

private theorem odd_minus {x y : ℕ} (hx : Even x) (hy : Odd y) (le : y≤x) : Odd (x-y) := by
  obtain ⟨u,h⟩:=hx;obtain ⟨v,k⟩:=hy
  exact ⟨u-v-1,by omega⟩

theorem criterion {H A S p B K : ℕ} (hH : 0<H) (hS : 0<S) (hp : p.Prime) (op : Odd p)
    (hB : 0<B) (pole : A*p=H*(p-1)) (s : Finset ℕ) (len : ℕ→ℕ)
    (sizes : ∀q∈s,2≤q ∧ Odd q ∧ 0<len q)
    (zero : H*K*((p-1)*den s)^2 =
      p*num s*(A*((B*(p-1)-1)*(∏q∈s,(len q*(q-1)-1)))+S*(p-1)*den s)) :
    H.factorization 2 = S.factorization 2+∑q∈s,(q-1).factorization 2 := by
  let u:=p-1
  let V:=den s
  let R:=num s
  let J:=(B*u-1)*(∏q∈s,(len q*(q-1)-1))
  have up : 0<u := by dsimp [u];have:=hp.one_lt;omega
  have ue : Even u := by obtain ⟨i,ih⟩:=op;exact ⟨i,by dsimp [u];omega⟩
  have vp : 0<V := prod_pos (fun q hq=>by have:=(sizes q hq).1;omega)
  have ro : Odd R := odd_prod' id (fun q hq=>(sizes q hq).2.1)
  have rp : 0<R := by obtain ⟨i,ih⟩:=ro;omega
  have jo : Odd J := by
    have left:=odd_minus (ue.mul_left B) (show Odd 1 by decide) (Nat.mul_pos hB up)
    apply left.mul (odd_prod' _ _)
    intro q hq
    obtain ⟨q2,⟨i,eq⟩,lp⟩:=sizes q hq
    exact odd_minus ((show Even (q-1) from ⟨i,by omega⟩).mul_left _) (by decide) (Nat.mul_pos lp (by omega))
  have notDiv : ¬p∣u := Nat.not_dvd_of_pos_of_lt up (by dsimp [u];omega)
  have div : p∣H*u := pole ▸ dvd_mul_left _ _
  obtain ⟨c,ec⟩:= (hp.dvd_mul.mp div).resolve_right notDiv
  have cp : 0<c := by
    by_contra! c0
    have z:c=0:=by omega
    rw [z,mul_zero] at ec
    omega
  have ac : A=c*u := by
    apply Nat.eq_of_mul_eq_mul_right hp.pos
    rw [pole,ec];dsimp [u];ring
  change H*K*(u*V)^2=p*R*(A*J+S*u*V) at zero
  have cancel : c*(K*u*V^2)=c*(R*J)+R*S*V := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hp.pos up)
    rw [ec,ac] at zero
    nlinarith only [zero]
  have pos : 0<R*S*V := Nat.mul_pos (Nat.mul_pos rp hS) vp
  have gt : R*J<K*u*V^2 := by
    apply Nat.lt_of_mul_lt_mul_left (a:=c);omega
  let Z:=K*u*V^2-R*J
  have zo : Odd Z := odd_minus ((ue.mul_left K).mul_right _) (ro.mul jo) gt.le
  have zp : 0<Z := Nat.sub_pos_of_lt gt
  have id : c*Z=R*S*V := by
    dsimp [Z]
    rw [Nat.mul_sub_left_distrib,cancel];omega
  have v:=congrArg (fun x:ℕ=>x.factorization 2) id
  rw [v_mul cp zp,v_mul (Nat.mul_pos rp hS) vp,v_mul rp hS,v_odd zo,v_odd ro] at v
  rw [ec,v_mul hp.pos cp,v_odd op,zero_add]
  have fin : V.factorization 2=∑q∈s,(q-1).factorization 2 := by
    change (∏q∈s,(q-1)).factorization 2=_
    rw [Nat.factorization_prod (fun q hq=>by have:=(sizes q hq).1;omega),Finset.sum_apply']
  omega

end OMA.FreePoleLeading245212

end

section

/- The divisor score strictly increases in one prime exponent as soon as
one other prime exponent is sufficiently large. -/
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

end

section

/- Finite original A245212 solutions of bounded odd-prime rank
when no odd prime divides another exponent length or the divisor count
of the fixed cofactor. -/
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

end

section

/- An explicit whole-prime-power bound in the nonresonant case.
Replace large bases by 1 and small bases with large exponents by their
Euler limits. The explicitly separated subproduct cannot approximate a
solution this closely. -/
namespace OMA.CofactorEffectiveAtom245212
open Finset Nat OMA.Smooth245212 OMA.CofactorEulerSeparation245212

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

def factor (p : ℕ) : ℚ := (p:ℚ)/(p-1:ℕ)

theorem local_factor {p e : ℕ} (hp : p.Prime) :
    1≤X p (some e) ∧ X p (some e)≤factor p ∧ factor p≤2 ∧
    factor p-X p (some e)=Y p (some e)/((p:ℚ)-1) := by
  have hi : (1:ℚ)<p := by exact_mod_cast hp.one_lt
  have den : (0:ℚ)<p-1 := by linarith
  have two : (2:ℚ)≤p := by exact_mod_cast hp.two_le
  have y0:=y_nonneg hp.one_lt (some e)
  have y1:=y_one hp.one_lt (some e)
  have diff : factor p-X p (some e)=Y p (some e)/((p:ℚ)-1) := by
    unfold factor X;push_cast [Nat.cast_sub hp.one_le];field_simp;ring
  refine ⟨le_add_of_nonneg_right (div_nonneg (sub_nonneg.mpr y1) den.le),?_,?_,diff⟩
  · linarith only [diff,div_nonneg y0 den.le]
  · unfold factor;push_cast [Nat.cast_sub hp.one_le];apply (div_le_iff₀ den).mpr;linarith

theorem near {p e M : ℕ} (hp : p.Prime) (avoid : p≤M+1 → M<e) :
    |X p (some e)-(if p≤M+1 then factor p else 1)|≤2/((M:ℚ)+1) := by
  obtain ⟨low,hi,_,diff⟩:=local_factor (e:=e) hp
  have h2 : (2:ℚ)≤p:=by exact_mod_cast hp.two_le
  have den : (0:ℚ)<p-1:=by linarith
  split
  next small=>
    rw [abs_of_nonpos (sub_nonpos.mpr hi),neg_sub,diff]
    have ye:=OMA.CapOrder245212.y_short hp e
    have big : (M:ℚ)+1≤e+1 := by exact_mod_cast (by have:=avoid small;omega : M+1≤e+1)
    have y0:=y_nonneg hp.one_lt (some e)
    calc
      Y p (some e)/((p:ℚ)-1) ≤ Y p (some e) := div_le_self y0 (by linarith)
      _ ≤ _ := (le_div_iff₀ (by positivity)).mpr ((mul_le_mul_of_nonneg_left big y0).trans ye.le)
  next large=>
    rw [abs_of_nonneg (sub_nonneg.mpr low)]
    unfold X
    have bound : (M:ℚ)+1≤p-1 := by
      have strong : (M:ℚ)+2≤p:=by exact_mod_cast (show M+2≤p by omega)
      linarith
    have y0:=y_nonneg hp.one_lt (some e)
    rw [add_sub_cancel_left]
    calc
      _ ≤ 1/((p:ℚ)-1) := div_le_div_of_nonneg_right (sub_le_self _ y0) den.le
      _ ≤ 1/((M:ℚ)+1) := one_div_le_one_div_of_le (by positivity) bound
      _ ≤ _ := by gcongr; norm_num


end OMA.CofactorEffectiveAtom245212

end

section

/- Polynomial bounds for the prime and exponent of a fresh atom after
adjoining a possibly very large power at a singleton Euler pole. -/
namespace OMA.FreePoleAtom245212
open Nat Finset ArithmeticFunction OMA.Smooth245212 OMA.CofactorEulerSeparation245212
open OMA.CofactorEffectiveAtom245212 OMA.FreePoleHereditary245212 OMA.FreePoleOnset245212
open scoped ArithmeticFunction.sigma
open OMA.CofactorEffectiveAtom245212 (product_error)
open OMA.CofactorEffectiveAtom245212 (near)
open OMA.CofactorEffectiveAtom245212 (factor)
open OMA.CofactorEffectiveAtom245212 (local_factor)
open OMA.FreePoleHereditary245212 (positive)

private theorem alternative_scaled (A S H D E M : ℕ) (s : Finset ℕ) (e : ℕ→ℕ)
    (pr : ∀p∈s,p.Prime) (lower : ∀t⊆s,(E:ℚ)≤(D:ℚ)*|(A:ℚ)*(num t/den t)-H|)
    (positive : 0<E) (limit : D*(2*A*s.card*2^s.card+2*S)≤M*E)
    (bal : (A:ℚ)*(∏p∈s,X p (some (e p)))+S*(∏p∈s,Y p (some (e p)))=H) :
    (∀p∈s,e p≤M) ∨ ∃p∈s,p≤M+1 ∧ e p≤M := by
  classical
  let K:=s.card
  by_cases allSmall : ∀p∈s,e p≤M
  · exact Or.inl allSmall
  right
  by_contra no
  push Not at allSmall
  obtain ⟨j,hj,large⟩:=allSmall
  have avoid (p) (hp:p∈s) (low:p≤M+1) : M<e p := by
    by_contra! short
    exact no ⟨p,hp,low,short⟩
  let z (p : ℕ) : ℚ:=if p≤M+1 then OMA.CofactorEffectiveAtom245212.factor p else 1
  let t:=s.filter (fun p=>p≤M+1)
  have sub : t⊆s:=filter_subset _ _
  have proxy : (∏p∈s,z p)=(num t:ℚ)/den t := by
    rw [show (∏p∈s,z p)=∏p∈t,OMA.CofactorEffectiveAtom245212.factor p by simp [z,t,prod_filter]]
    unfold OMA.CofactorEffectiveAtom245212.factor num den
    push_cast
    rw [prod_div_distrib]
  have sep:=lower t sub
  rw [←proxy] at sep
  have feat:=OMA.CofactorEffectiveAtom245212.product_error s (fun p=>X p (some (e p))) z (w:=2/((M:ℚ)+1)) (by positivity)
    (fun p hp=>by
      have loc:=OMA.CofactorEffectiveAtom245212.local_factor (e:=e p) (pr p hp)
      refine ⟨zero_le_one.trans loc.1,loc.2.1.trans loc.2.2.1,?_,?_,OMA.CofactorEffectiveAtom245212.near (pr p hp) (avoid p hp)⟩
      · dsimp [z];split <;> first | exact (zero_le_one.trans loc.1).trans loc.2.1 | norm_num
      · dsimp [z];split <;> first | exact loc.2.2.1 | norm_num)
  let PX:=∏p∈s,X p (some (e p))
  let PY:=∏p∈s,Y p (some (e p))
  let Z:=∏p∈s,z p
  have y0 : 0≤PY:=prod_nonneg (fun p hp=>y_nonneg (pr p hp).one_lt _)
  have ylow : PY≤Y j (some (e j)) := by
    dsimp [PY];rw [←prod_erase_mul _ _ hj]
    exact mul_le_of_le_one_left (y_nonneg (pr j hj).one_lt _) (prod_le_one
      (fun p hp=>y_nonneg (pr p (mem_of_mem_erase hp)).one_lt _)
      (fun p hp=>y_one (pr p (mem_of_mem_erase hp)).one_lt _))
  have ycut := OMA.CapOrder245212.y_short (pr j hj) (e j)
  let L:ℚ:=M+1
  have lp : 0<L:=by dsimp [L];positivity
  have yl : PY*L≤2 := (mul_le_mul ylow (show L≤(e j:ℚ)+1 by dsimp [L];exact_mod_cast Nat.succ_le_succ large.le)
    lp.le (y_nonneg (pr j hj).one_lt _)).trans ycut.le
  change |PX-Z|≤K*(2:ℚ)^K*(2/L) at feat
  have xl : |PX-Z| * L≤K*2^K*2 := by
    apply (le_div_iff₀ lp).mp
    simpa [div_eq_mul_inv,mul_assoc] using feat
  change (A:ℚ)*PX+S*PY=H at bal
  change (E:ℚ)≤(D:ℚ)*|(A:ℚ)*Z-H| at sep
  have tri:=abs_add_le ((A:ℚ)*(PX-Z)) ((S:ℚ)*PY)
  rw [show (A:ℚ)*(PX-Z)+S*PY=H-A*Z by linarith only [bal],abs_sub_comm (H:ℚ)] at tri
  simp only [abs_mul,abs_of_nonneg (Nat.cast_nonneg A : (0:ℚ)≤A),
    abs_of_nonneg (Nat.cast_nonneg S : (0:ℚ)≤S),abs_of_nonneg y0] at tri
  have distance : |(A:ℚ)*Z-H| * L≤2*A*K*2^K+2*S := by
    nlinarith only [mul_le_mul_of_nonneg_right tri lp.le,
      mul_le_mul_of_nonneg_left xl (Nat.cast_nonneg A : (0:ℚ)≤A),
      mul_le_mul_of_nonneg_left yl (Nat.cast_nonneg S : (0:ℚ)≤S)]
  have bad : (E:ℚ)*L≤(D:ℚ)*(2*A*K*2^K+2*S) := by
    nlinarith only [mul_le_mul_of_nonneg_right sep lp.le,
      mul_le_mul_of_nonneg_left distance (Nat.cast_nonneg D : (0:ℚ)≤_)]
  have cap : (D:ℚ)*(2*A*K*2^K+2*S)≤M*E := by exact_mod_cast limit
  have pos : (0:ℚ)<E := by exact_mod_cast positive
  dsimp [L] at bad
  nlinarith only [bad,cap,pos]

private theorem rational_separation {h p a r : ℕ} (hp : p.Prime) (op : Odd p) (cp : h.Coprime p)
    (pole : W h*p=2*(h*σ 0 h)*(p-1)) (high : onset p r≤a) (s : Finset ℕ)
    (order : s.card≤r) (odd : ∀q∈s,Odd q) (base : ∀q∈s,2≤q) :
    ((W h*p*p^a:ℕ):ℚ) ≤ (2*budget ((p-1)*(a+1)-1) r*(p-1)^2:ℕ)*
      |(W (h*p^a):ℚ)*(num s/den s)-(2*((h*p^a)*σ 0 (h*p^a)):ℕ)| := by
  let g:=h*p^a
  let E:=W h*p*p^a
  let D:=2*budget ((p-1)*(a+1)-1) r*(p-1)^2
  let H:=2*(g*σ 0 g)
  have raw:= OMA.FreePoleOnset245212.original hp op cp pole high s order odd base
  have ic : (E:ℤ)*den s ≤ (D:ℤ)*|drift g (num s) (den s)| := by
    dsimp [E,D,g]
    push_cast [Nat.cast_sub hp.pos]
    exact raw
  have dd : (0:ℚ)<den s := by
    exact_mod_cast (prod_pos (fun x hx=>by have:=base x hx;omega) : 0<den s)
  have cast : (E:ℚ)*den s≤(D:ℚ)*|(H:ℚ)*den s - (W g:ℚ)*num s| := by
    unfold drift at ic
    dsimp [H]
    push_cast
    exact_mod_cast ic
  change (E:ℚ)≤(D:ℚ)*|(W g:ℚ)*(num s/den s)-(H:ℚ)|
  apply le_of_mul_le_mul_right (a:=(den s:ℚ)) _ dd
  rw [mul_assoc,show ∀x:ℚ,|x| * (den s:ℚ)=|x*(den s:ℚ)| by intro x;rw [abs_mul,abs_of_pos dd]]
  rwa [show ((W g:ℚ)*((num s:ℚ)/den s)-H)*den s=(W g:ℚ)*num s-H*den s by
    field_simp,abs_sub_comm]

/-- Apart from a known finite initial range in a, both coordinates of
one fresh prime power have an explicit polynomial-size upper bound. -/
def poly (h p a r : ℕ) :=
  let C:=budget ((p-1)*(a+1)-1) r
  6*C*(p-1)^2*((a+1)*r*2^r+σ 1 h)

theorem original {h p a m : ℕ} (hh : 0<h) (hp : p.Prime) (op : Odd p) (cp : h.Coprime p)
    (pole : W h*p=2*(h*σ 0 h)*(p-1)) (hm : 1 < m) (om : Odd m) (cop : (h*p^a).Coprime m)
    (high : onset p m.primeFactors.card ≤ a)
    (eqn : OeisA245212.a (h*p^a*m)=(σ 1 (h*p^a*m):ℤ)) :
    let r:=m.primeFactors.card
    let M:=poly h p a r
    ∃q∈m.primeFactors, q ≤ max (M+1) (r*W h*p*((σ 1 h)*(p-1)+1)*(a+1)) ∧ m.factorization q≤M := by
  classical
  let g:=h*p^a
  let s:=m.primeFactors
  let r:=s.card
  let M:=poly h p a r
  let C:=budget ((p-1)*(a+1)-1) r
  let D:=2*C*(p-1)^2
  let E:=W h*p*p^a
  let H:=2*(g*σ 0 g)
  have positive:=OMA.FreePoleHereditary245212.positive hh
  have pp:=hp.pos
  have gp : 0<g := by dsimp [g];positivity
  have odd_primes (q) (hq:q∈s) : Odd q :=
    Nat.coprime_two_left.mp ((Nat.coprime_two_left.mpr om).of_dvd_right (dvd_of_mem_primeFactors hq))
  have pr (q) (hq:q∈s) : q.Prime := prime_of_mem_primeFactors hq
  have lo (t : Finset ℕ) (sub : t⊆s) : (E:ℚ)≤(D:ℚ)*|(W g:ℚ)*(num t/den t)-(H:ℚ)| :=
    rational_separation hp op cp pole high t (card_le_card sub)
      (fun q hq=>odd_primes q (sub hq)) (fun q hq=>(pr q (sub hq)).two_le)
  have cost : D*(2*W g*r*2^r+2*σ 1 g) ≤ M*E := by
    have p3 : 3≤p := by have:=hp.two_le; obtain ⟨i,eq⟩:=op;omega
    obtain ⟨su,wu,_⟩:=OMA.ComplementaryLocal245212.bounds hp p3 a
    dsimp [D,M,poly,E,g,C]
    rw [w_mult.map_mul_of_coprime (cp.pow_right a),isMultiplicative_sigma.map_mul_of_coprime (cp.pow_right a)]
    let z:=budget ((p-1)*(a+1)-1) r*(p-1)^2
    have lowP : 1≤W h*p := Nat.mul_pos positive pp
    have low2 : 1≤p := pp
    have weight:=Nat.mul_le_mul_left (2*z*W h*r*2^r) wu
    have sigma:=Nat.mul_le_mul_left (2*z*σ 1 h) su
    have a2:= Nat.mul_le_mul_left (6*z*(σ 1 h)*p^a) lowP
    have b2:= Nat.mul_le_mul_left (6*z*(a+1)*r*2^r*(W h)*p^a) low2
    dsimp [z] at weight sigma a2 b2
    nlinarith only [weight,sigma,a2,b2]
  have mn:=show m≠0 by omega
  let x:s→ℕ:=Subtype.val
  let e (i:s):=m.factorization (x i)
  have repr : total x e=m := (Nat.prod_primeFactors_coe_pow_factorization mn).symm
  have mass:=OMA.CofactorCrossOriginal245212.normalized_extension (p:=x) (e:=e) gp
    (fun i=>pr i i.property) Subtype.val_injective (fun i=>cop.of_dvd_right (dvd_of_mem_primeFactors i.property)) (repr ▸ eqn)
  have sx : (∏i,X (x i) (some (e i)))=∏j∈s,X j (some (m.factorization j)) :=
    s.prod_coe_sort (fun i=>X i (some (m.factorization i)))
  have sy : (∏i,Y (x i) (some (e i)))=∏j∈s,Y j (some (m.factorization j)) :=
    s.prod_coe_sort (fun i=>Y i (some (m.factorization i)))
  rw [sx,sy] at mass
  let t:=g*σ 0 g
  have t0 : 0<t:=Nat.mul_pos gp (sigma_pos 0 g gp.ne')
  change ((W g:ℚ)/t)*_+((σ 1 g:ℚ)/t)*_=2 at mass
  field_simp [show (t:ℚ)≠0 by exact_mod_cast t0.ne'] at mass
  have norm : (W g:ℚ)*(∏j∈s,X j (some (m.factorization j)))+(σ 1 g:ℚ)*(∏j∈s,Y j (some (m.factorization j)))=H :=
    by change _=((2*t:ℕ):ℚ);push_cast;linarith only [mass]
  rcases alternative_scaled (W g) (σ 1 g) H D E M s m.factorization pr lo (by dsimp [E];positivity) cost norm with all|some
  · have ne : s.Nonempty := ⟨m.minFac,(Nat.mem_primeFactors_of_ne_zero mn).mpr ⟨Nat.minFac_prime (by omega),Nat.minFac_dvd _⟩⟩
    let q:=s.min' ne
    have mem:=s.min'_mem ne
    exact ⟨q,mem,(OMA.FreePoleLeast245212.upper hh hp cp pole hm cop (fun x hx=>s.min'_le x hx) eqn).trans
      (le_max_right _ _),all q mem⟩
  · obtain ⟨q,mem,bound,small⟩:=some
    exact ⟨q,mem,bound.trans (le_max_left _ _),small⟩

end OMA.FreePoleAtom245212

end

#print axioms OMA.FreePoleHereditary245212.inherited

#print axioms OMA.FreePoleOnset245212.polynomial

#print axioms OMA.FreePoleOnset245212.original

#print axioms OMA.FreePoleLeast245212.upper

#print axioms OMA.FreePoleLower245212.original

#print axioms OMA.FreePoleLeading245212.criterion

#print axioms OMA.FreePoleAtom245212.original
