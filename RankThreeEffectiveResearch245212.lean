import FormalConjectures.OEIS.«245212»

import Mathlib.Data.Nat.Totient


/-! Effective rank-three bound and divisibility obstruction for dyadic single-prime cofactors -/

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

private theorem budget_pos (A r : ℕ) : 0<budget A r := by
  induction r with
  | zero=>simp [budget]
  | succ r ih=>exact (Nat.mul_pos (by decide) ih).trans_le (le_max_left _ _)

private theorem gap_pos {A H : ℕ} {s : Finset ℕ} (m : A*num s≠H*den s) : 0<gap A H s := by
  apply Int.natAbs_pos.mpr
  intro z
  exact m (by exact_mod_cast sub_eq_zero.mp z)

private theorem size {s : Finset ℕ} (positive : ∀p∈s,2≤p) : num s≤2^s.card*den s := by
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

#print axioms separated

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

#print axioms rational_gap
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

/- Limits of the weighted divisor factors on odd fourth powers have odd
numerators. Finite products of them stay uniformly away from two. -/
namespace OMA.SquareCompact245212
open Finset Filter Topology OMA.Smooth245212

def OddNum (x : ℚ) := ∃ A B : ℕ, Odd A ∧ 0<B ∧ x=(A:ℚ)/B

theorem one : OddNum 1 := ⟨1,1,by decide,by decide,by norm_num⟩
theorem mul {x y : ℚ} (hx : OddNum x) (hy : OddNum y) : OddNum (x*y) := by
  obtain ⟨a,b,ha,hb,rfl⟩ := hx
  obtain ⟨c,d,hc,hd,rfl⟩ := hy
  exact ⟨a*c,b*d,ha.mul hc,Nat.mul_pos hb hd,by push_cast; ring⟩
theorem ne_two {x : ℚ} (h : OddNum x) : x≠2 := by
  obtain ⟨a,b,ha,hb,rfl⟩ := h
  intro eq
  have div := (div_eq_iff (by positivity : (b:ℚ)≠0)).mp eq
  have same : a=2*b := by exact_mod_cast div
  obtain ⟨t,ht⟩ := ha
  omega

theorem quotient {p e : ℕ} (hp : Nat.Prime p) (odd : Odd (W (p^e))) :
    OddNum (X p (some e)) := by
  refine ⟨W (p^e),(e+1)*p^e,odd,by have := hp.pos; positivity,?_⟩
  apply (eq_div_iff (by have := hp.pos; positivity)).2
  simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_pow] using x_factor hp e

private theorem finite_factor {p e : ℕ} (hp : Nat.Prime p) (po : Odd p) (e4 : 4∣e) :
    OddNum (X p (some e)) := by
  obtain ⟨a,rfl⟩ := e4
  have hh := (OMA.DyadicBlocks245212.prime_block p 0 (2*a) hp po).2.2.2
  apply quotient hp
  rw [Nat.odd_iff]
  simpa [Nat.ModEq,show 2*a*2=4*a by ring,Nat.add_mod] using hh

theorem infinite_factor {p : ℕ} (hp : Nat.Prime p) (po : Odd p) :
    OddNum (X p none) := by
  refine ⟨p,p-1,po,by have := hp.one_lt; omega,?_⟩
  have pp : (1:ℚ)<p := by exact_mod_cast hp.one_lt
  simp only [X,Y,sub_zero,Nat.cast_sub hp.one_le,Nat.cast_one]
  field_simp [show (p:ℚ)-1≠0 by linarith]; ring

private theorem dichotomy {v : ℕ → ℕ} (inc : Monotone v) :
    (∃ M, ∀ᶠ n in atTop,v n=M) ∨ Tendsto v atTop atTop := by
  by_cases h : BddAbove (Set.range v)
  · obtain ⟨n,hn⟩ := Nat.sSup_mem (Set.range_nonempty v) h
    refine Or.inl ⟨v n,eventually_atTop.mpr ⟨n,fun m hm => le_antisymm ?_ (inc hm)⟩⟩
    rw [hn]; exact le_csSup h ⟨m,rfl⟩
  · exact Or.inr (tendsto_atTop_atTop_of_monotone' inc h)

/-- A moving prime or exponent has an odd-numerator limit automatically.
Only pairs stabilizing in both coordinates need a local arithmetic check. -/
theorem factor_limit_restricted (s : ℚ → Prop) (p e : ℕ → ℕ) (pm : Monotone p) (em : Monotone e)
    (hp : ∀ n,Nat.Prime (p n)) (po : ∀ n,Odd (p n)) (atOne : s 1)
    (atCap : ∀ P : ℕ,Nat.Prime P → Odd P → (∀ᶠ n in atTop,p n=P) → s (X P none))
    (stable : ∀ P E, (∀ᶠ n in atTop,p n=P) → (∀ᶠ n in atTop,e n=E) →
      s (X P (some E))) :
    ∃ x : ℚ,s x ∧ Tendsto (fun n => X (p n) (some (e n))) atTop (𝓝 x) := by
  rcases dichotomy pm with ⟨P,hP⟩|hP
  · obtain ⟨n,hn⟩ := hP.exists
    have pr : Nat.Prime P := hn ▸ hp n
    have od : Odd P := hn ▸ po n
    rcases dichotomy em with ⟨E,hE⟩|hE
    · refine ⟨X P (some E),stable P E hP hE,?_⟩
      apply tendsto_const_nhds.congr'
      filter_upwards [hP,hE] with n a b; rw [a,b]
    · have upper : Tendsto (fun n : ℕ => (2:ℚ)/(e n+1)) atTop (𝓝 0) := by
        simpa only [Function.comp_apply,div_eq_mul_inv,one_mul,mul_zero] using
          ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℚ)).comp hE).const_mul 2
      have yl : Tendsto (fun n => Y P (some (e n))) atTop (𝓝 0) :=
        tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds upper
          (fun n => y_nonneg pr.one_lt _) (fun n => ((lt_div_iff₀ (by positivity)).mpr
            (OMA.CapOrder245212.y_short pr (e n))).le)
      have pp : (1:ℚ)<P := by exact_mod_cast pr.one_lt
      refine ⟨X P none,atCap P pr od hP,?_⟩
      have lim := (tendsto_const_nhds (x:=(1:ℚ))).add
        (((tendsto_const_nhds (x:=(1:ℚ))).sub yl).div_const ((P:ℚ)-1))
      apply lim.congr'
      filter_upwards [hP] with n pn; rw [pn]; rfl
  · have pt : Tendsto (fun n => (p n:ℚ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hP
    have den : Tendsto (fun n => (p n:ℚ)-1) atTop atTop := by
      apply tendsto_atTop.mpr
      intro x
      filter_upwards [tendsto_atTop.mp pt (x+1)] with n hn
      linarith
    have inv : Tendsto (fun n => ((p n:ℚ)-1)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp den
    refine ⟨1,atOne,tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (show Tendsto (fun n => 1+((p n:ℚ)-1)⁻¹) atTop (𝓝 1) by simpa using inv.const_add 1) ?_ ?_⟩
    · intro n
      have pp : (1:ℚ)<p n := by exact_mod_cast (hp n).one_lt
      exact le_add_of_nonneg_right (div_nonneg (sub_nonneg.mpr (y_one (hp n).one_lt _)) (by linarith))
    · intro n
      have pp : (1:ℚ)<p n := by exact_mod_cast (hp n).one_lt
      simp only [X,←one_div]
      exact add_le_add_right (div_le_div_of_nonneg_right (sub_le_self _ (y_nonneg (hp n).one_lt _))
        (by linarith)) _

theorem factor_limit_by (s : ℚ → Prop) (p e : ℕ → ℕ) (pm : Monotone p) (em : Monotone e)
    (hp : ∀ n,Nat.Prime (p n)) (po : ∀ n,Odd (p n)) (atOne : s 1)
    (atCap : ∀ P : ℕ,Nat.Prime P → Odd P → s (X P none))
    (stable : ∀ P E, (∀ᶠ n in atTop,p n=P) → (∀ᶠ n in atTop,e n=E) →
      s (X P (some E))) :
    ∃ x : ℚ,s x ∧ Tendsto (fun n => X (p n) (some (e n))) atTop (𝓝 x) :=
  factor_limit_restricted s p e pm em hp po atOne (fun P pr op _ => atCap P pr op) stable

theorem factor_limit_of_stable (p e : ℕ → ℕ) (pm : Monotone p) (em : Monotone e)
    (hp : ∀ n,Nat.Prime (p n)) (po : ∀ n,Odd (p n))
    (stable : ∀ P E, (∀ᶠ n in atTop,p n=P) → (∀ᶠ n in atTop,e n=E) →
      OddNum (X P (some E))) :
    ∃ x : ℚ,OddNum x ∧ Tendsto (fun n => X (p n) (some (e n))) atTop (𝓝 x) :=
  factor_limit_by OddNum p e pm em hp po one (fun _ => infinite_factor) stable

theorem factor_limit (p e : ℕ → ℕ) (pm : Monotone p) (em : Monotone e)
    (hp : ∀ n,Nat.Prime (p n)) (po : ∀ n,Odd (p n)) (ed : ∀ n,4∣e n) :
    ∃ x : ℚ,OddNum x ∧ Tendsto (fun n => X (p n) (some (e n))) atTop (𝓝 x) := by
  apply factor_limit_of_stable p e pm em hp po
  intro P E pP eE
  obtain ⟨n,pn,en⟩ := (pP.and eE).exists
  exact finite_factor (pn ▸ hp n) (pn ▸ po n) (en ▸ ed n)

theorem uniform_gap (K : ℕ) (c : ℚ) (hc : OddNum c) :
    ∃ δ : ℚ, 0<δ ∧ ∀ p e : Fin K → ℕ, (∀ i,Nat.Prime (p i)) → (∀ i,Odd (p i)) →
      (∀ i,4∣e i) → δ≤|c*(∏ i,X (p i) (some (e i)))-2| := by
  by_contra! bad
  have pick (n : ℕ) := bad (1/((n:ℚ)+1)) (by positivity)
  choose p e hp ho he close using pick
  let seq (n : ℕ) := (p n,e n)
  obtain ⟨g,sorted⟩ := wellQuasiOrdered_le.exists_monotone_subseq seq
  have points (i : Fin K) := factor_limit (fun n => p (g n) i) (fun n => e (g n) i)
    (fun _ _ le => (sorted _ _ le).1 i) (fun _ _ le => (sorted _ _ le).2 i)
    (fun n => hp (g n) i) (fun n => ho (g n) i) (fun n => he (g n) i)
  choose x ox conv using points
  have prod (s : Finset (Fin K)) : OddNum (∏ i∈s,x i) := by
    induction s using Finset.induction_on with
    | empty => simpa using one
    | @insert i s mem ih => simpa only [prod_insert mem] using mul (ox i) ih
  have unequal := ne_two (mul hc (prod univ))
  have limit := (tendsto_finsetProd univ (fun i _ => conv i)).const_mul c
  have t2 : Tendsto (fun n => c*∏ i,X (p n i) (some (e n i))) atTop (𝓝 2) := by
    have hz := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℚ)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (show Tendsto (fun n : ℕ => 2-1/((n:ℚ)+1)) atTop (𝓝 2) by simpa using tendsto_const_nhds.sub hz)
      (show Tendsto (fun n : ℕ => 2+1/((n:ℚ)+1)) atTop (𝓝 2) by simpa using hz.const_add 2)
    · intro n; linarith only [(abs_lt.mp (close n)).1]
    · intro n; linarith only [(abs_lt.mp (close n)).2]
  exact unequal (tendsto_nhds_unique limit (t2.comp g.strictMono.tendsto_atTop))

end OMA.SquareCompact245212

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

/- Finitely many solutions at fixed dyadic exponent and bounded number of odd
prime factors, whenever the odd part is a square. -/
namespace OMA.SquareFinite245212
open Finset OMA.Smooth245212 OMA.SquareCompact245212
open scoped ArithmeticFunction.sigma

def Config (K : ℕ) (c d : ℚ) (p e : Fin K → ℕ) :=
  (∀ i,Nat.Prime (p i)) ∧ (∀ i,Odd (p i)) ∧ (∀ i,4∣e i) ∧ (∀ i,0<e i) ∧
  c*(∏ i,X (p i) (some (e i)))+d*(∏ i,Y (p i) (some (e i)))=2

private theorem bounded {K : ℕ} {c d : ℚ} (hc : OddNum c) (d0 : 0<d) (d1 : d≤1) :
    ∃ L : ℕ, ∀ p e, Config K c d p e → ∀ i,e i<L := by
  obtain ⟨δ,hδ,sep⟩ := uniform_gap K c hc
  obtain ⟨L,hL⟩ := exists_nat_gt (2/δ)
  refine ⟨L,fun p e he i => ?_⟩
  obtain ⟨hp,ho,ed,_,eq⟩ := he
  have bound := sep p e hp ho ed
  have y0 (j) := y_nonneg (hp j).one_lt (some (e j))
  have z : 0≤d*(∏ j,Y (p j) (some (e j))) := mul_nonneg d0.le (prod_nonneg (fun j _ => y0 j))
  have act : |c*(∏ j,X (p j) (some (e j)))-2|=d*(∏ j,Y (p j) (some (e j))) := by
    rw [abs_of_nonpos (by linarith only [eq,z])]; linarith only [eq]
  rw [act] at bound
  have upper : δ≤Y (p i) (some (e i)) := by
    apply bound.trans
    rw [←prod_erase_mul _ _ (mem_univ i)]
    exact (mul_le_of_le_one_left (mul_nonneg (prod_nonneg (fun j _ => y0 j)) (y0 i)) d1).trans
      (mul_le_of_le_one_left (y0 i) (prod_le_one (fun j _ => y0 j)
        (fun j _ => y_one (hp j).one_lt _)))
  have hh := OMA.CapOrder245212.y_short (hp i) (e i)
  have m := mul_le_mul_of_nonneg_right upper (show 0≤(e i:ℚ)+1 by positivity)
  have qq : (e i:ℚ)<2/δ := (lt_div_iff₀ hδ).mpr (by linarith only [hh,m,hδ])
  exact_mod_cast qq.trans hL

theorem configs (K : ℕ) (c d : ℚ) (hc : OddNum c) (d0 : 0<d) (d1 : d≤1) :
    {v : (Fin K → ℕ) × (Fin K → ℕ) | Config K c d v.1 v.2}.Finite := by
  obtain ⟨L,size⟩ := bounded hc d0 d1
  have c0 : 0≤c := by obtain ⟨A,B,_,_,rfl⟩ := hc; positivity
  apply Set.Finite.of_finite_fibers Prod.snd
  · apply (Set.Finite.pi' (fun _ : Fin K => Set.finite_Iio L)).subset
    rintro e ⟨⟨p,v⟩,h,rfl⟩
    exact size _ _ h
  · rintro e ⟨⟨p,v⟩,conf,rfl⟩
    have finite := OMA.FixedExponents245212.finite_bases v conf.2.2.2.1 c d 2 c0 d0
    apply (finite.image (fun q => (q,v))).subset
    rintro ⟨q,f⟩ ⟨hf,hv⟩
    have same : f=v := hv
    subst f
    exact ⟨q,⟨hf.1,hf.2.2.2.2⟩,rfl⟩

private theorem square_rank (k K : ℕ) :
    {u : ℕ | Odd u ∧ IsSquare u ∧ u.primeFactors.card=K ∧
      OeisA245212.a (2^k*u)=(σ 1 (2^k*u):ℤ)}.Finite := by
  let c := X 2 (some k)
  let d := Y 2 (some k)
  have hc : OddNum c := quotient Nat.prime_two (OMA.DyadicPower245212.dyadic_odd k)
  have d0 : 0<d := by
    dsimp [d]; rw [y_avg (by decide : 1<2)]
    exact div_pos (sum_pos' (fun i _ => by positivity) ⟨0,by simp,by simp⟩) (by positivity)
  apply ((configs K c d hc d0 (y_one (by decide) _)).image (fun v => total v.1 v.2)).subset
  rintro u ⟨odd,sq,card,eq⟩
  let S := u.primeFactors
  let p := S.orderEmbOfFin card
  let e (i : Fin K) := u.factorization (p i)
  have mem (i) : p i∈u.primeFactors := orderEmbOfFin_mem S card i
  have hp (i) := Nat.prime_of_mem_primeFactors (mem i)
  have op (i) : Odd (p i) := Nat.coprime_two_left.mp ((Nat.coprime_two_left.mpr odd).of_dvd_right
    (Nat.dvd_of_mem_primeFactors (mem i)))
  have ep (i) : 0<e i := (hp i).factorization_pos_of_dvd odd.pos.ne' (Nat.dvd_of_mem_primeFactors (mem i))
  have fourth : ∃ t,u=t^4 := by
    obtain ⟨w,hw⟩ := sq
    have wo : Odd w := (Nat.odd_mul.mp (hw ▸ odd)).1
    have eq' : OeisA245212.a (2^k*w^2)=(σ 1 (2^k*w^2):ℤ) := by simpa only [sq,hw] using eq
    obtain ⟨t,ht⟩ := OMA.DyadicPower245212.square_root_is_square wo eq'
    exact ⟨t,by rw [hw,ht]; ring⟩
  have ed (i) : 4∣e i := by
    obtain ⟨t,ht⟩ := fourth
    change 4∣u.factorization (p i)
    have f (q : ℕ) : 4∣u.factorization q := by
      rw [ht,Nat.factorization_pow]; simp
    apply f
  have repr : total p e=u := by
    exact (Fintype.prod_equiv (S.orderIsoOfFin card).toEquiv _
      (fun j : S => j.val^(u.factorization j.val)) (fun _ => rfl)).trans
      (Nat.prod_primeFactors_coe_pow_factorization odd.pos.ne').symm
  let P : Fin (K+1) → ℕ := Fin.cons 2 (p : Fin K → ℕ)
  let E : Fin (K+1) → ℕ := Fin.cons k e
  have prime : ∀ i,Nat.Prime (P i) := Fin.cases Nat.prime_two hp
  have inj : P.Injective := Fin.cons_injective_of_injective (by
    rintro ⟨i,hi⟩; have h := op i; rw [hi] at h; norm_num [Nat.odd_iff] at h) p.injective
  have entire : total P E=2^k*u := by
    rw [total,Fin.prod_univ_succ]; simp only [P,E,Fin.cons_zero,Fin.cons_succ]
    exact congrArg (2^k*·) repr
  have norm := normalized_of_eq P prime inj E (by rw [entire]; exact eq)
  unfold normalized at norm
  rw [Fin.prod_univ_succ (fun i => X (P i) (some (E i))),
    Fin.prod_univ_succ (fun i => Y (P i) (some (E i)))] at norm
  exact ⟨(p,e),⟨hp,op,ed,ep,by simpa only [P,E,c,d,Fin.cons_zero,Fin.cons_succ] using norm⟩,repr⟩

theorem square_finite (k K : ℕ) :
    {u : ℕ | Odd u ∧ IsSquare u ∧ u.primeFactors.card≤K ∧
      OeisA245212.a (2^k*u)=(σ 1 (2^k*u):ℤ)}.Finite := by
  apply ((Set.finite_Iic K).biUnion (fun j _ => square_rank k j)).subset
  rintro u ⟨ho,hs,hc,he⟩
  exact Set.mem_iUnion.mpr ⟨u.primeFactors.card,Set.mem_iUnion.mpr ⟨hc,ho,hs,rfl,he⟩⟩

end OMA.SquareFinite245212

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

/- A bounded exceptional odd prime power in nonsquare A245212 solutions.
The rank of the odd part and the dyadic exponent are fixed, not its primes. -/
namespace OMA.BoundedAtom245212
open Finset Filter Topology Nat OMA.Smooth245212 OMA.SquareCompact245212
open OMA.WeightVal245212 (weight_local)
local notation "v₂" => OMA.WeightVal245212.val
open scoped ArithmeticFunction.sigma

/-- Away from exponents 2 mod 4 the factors of two in the numerator
can all be cancelled against the local divisor count. -/
theorem good_factor {p e : ℕ} (pr : Nat.Prime p) (op : Odd p) (good : e%4≠2) :
    OddNum (X p (some e)) := by
  let N := W (p^e)
  have np : 0<N := by
    dsimp [N]; rw [w_pow pr]
    exact sum_pos' (fun i _ => Nat.zero_le _) ⟨0,mem_range.mpr (Nat.succ_pos _),by simp⟩
  have small : v₂ (e+2)<2 := by
    by_contra! hi
    have x := (Nat.prime_two.pow_dvd_iff_le_factorization (by omega : e+2≠0)).mpr hi
    change 4 ∣ e+2 at x
    omega
  have vals := weight_local pr op e
  change v₂ N+1=v₂ (e+1)+v₂ (e+2) at vals
  obtain ⟨B,hB⟩ := (Nat.prime_two.pow_dvd_iff_le_factorization (Nat.succ_ne_zero e)).mpr
    (show v₂ N≤v₂ (e+1) by omega)
  let A := ordCompl[2] N
  have rep : 2^(v₂ N)*A=N := Nat.ordProj_mul_ordCompl_eq_self N 2
  have oa : Odd A := Nat.not_even_iff_odd.mp (fun h => Nat.not_dvd_ordCompl Nat.prime_two np.ne'
    (even_iff_two_dvd.mp h))
  have bp : 0<B := by
    by_contra! z
    have z' : B=0 := by omega
    simp [z'] at hB
  have raw := x_factor pr e
  change X p (some e)*(((e:ℚ)+1)*p^e)=(N:ℚ) at raw
  have br := congrArg (Nat.cast : ℕ → ℚ) hB
  have nr := congrArg (Nat.cast : ℕ → ℚ) rep
  push_cast at br nr
  refine ⟨A,B*p^e,oa,Nat.mul_pos bp (Nat.pow_pos pr.pos),?_⟩
  apply (eq_div_iff (by exact_mod_cast (Nat.mul_pos bp (Nat.pow_pos pr.pos)).ne')).mpr
  push_cast
  apply (mul_left_cancel₀ (by positivity : (2:ℚ)^(v₂ N)≠0))
  linear_combination raw - nr - (X p (some e)*(p:ℚ)^e)*br

private theorem product_odd {K : ℕ} (x : Fin K → ℚ) (ox : ∀ i,OddNum (x i)) :
    OddNum (∏ i,x i) := by
  have aux (s : Finset (Fin K)) : OddNum (∏ i∈s,x i) := by
    induction s using Finset.induction_on with
    | empty => simpa using OMA.SquareCompact245212.one
    | @insert i s hi ih => simpa only [prod_insert hi] using OMA.SquareCompact245212.mul (ox i) ih
  exact aux univ

/-- If some exponent grows past every bound, a prime and an exponent
2 mod 4 must both stay bounded in at least one coordinate. -/
theorem bounded_or_atom (K : ℕ) (c d : ℚ) (hc : OddNum c) (d0 : 0≤d) (d1 : d≤1) :
    ∃ B : ℕ, ∀ p e : Fin K → ℕ, (∀ i,Nat.Prime (p i)) → (∀ i,Odd (p i)) →
      c*(∏ i,X (p i) (some (e i)))+d*(∏ i,Y (p i) (some (e i)))=2 →
      (∀ i,e i≤B) ∨ ∃ i,e i%4=2 ∧ p i≤B ∧ e i≤B := by
  by_contra! bad
  choose p e hp ho eq large avoid using bad
  let seq (n : ℕ) := (p n,e n)
  obtain ⟨g,sorted⟩ := wellQuasiOrdered_le.exists_monotone_subseq seq
  have points (i : Fin K) : ∃ x : ℚ,OddNum x ∧
      Tendsto (fun n => X (p (g n) i) (some (e (g n) i))) atTop (𝓝 x) := by
    apply factor_limit_of_stable _ _ (fun _ _ le => (sorted _ _ le).1 i)
      (fun _ _ le => (sorted _ _ le).2 i) (fun n => hp (g n) i) (fun n => ho (g n) i)
    intro P E pP eE
    have eventuallyLarge := g.strictMono.tendsto_atTop.eventually (eventually_ge_atTop (max P E))
    obtain ⟨n,pn,en,gn⟩ := (pP.and (eE.and eventuallyLarge)).exists
    change p (g n) i=P at pn
    change e (g n) i=E at en
    apply good_factor (pn ▸ hp (g n) i) (pn ▸ ho (g n) i)
    intro badE
    have stop := avoid (g n) i
    rw [pn,en] at stop
    exact (not_lt_of_ge ((le_max_right P E).trans gn)) (stop badE ((le_max_left P E).trans gn))
  choose x ox conv using points
  have limit := (tendsto_finsetProd univ (fun i _ => conv i)).const_mul c
  have notTwo := ne_two (OMA.SquareCompact245212.mul hc (product_odd x ox))
  apply notTwo
  apply tendsto_nhds_unique limit
  suffices total : Tendsto (fun n => c*∏ i,X (p n i) (some (e n i))) atTop (𝓝 2) from
    total.comp g.strictMono.tendsto_atTop
  have error (n : ℕ) : 0 ≤ d*∏ i,Y (p n i) (some (e n i)) ∧
      d*(∏ i,Y (p n i) (some (e n i))) ≤ 2/((n:ℚ)+1) := by
    have y0 (j) := y_nonneg (hp n j).one_lt (some (e n j))
    have pos := prod_nonneg (s:=univ) (fun j _ => y0 j)
    refine ⟨mul_nonneg d0 pos,?_⟩
    obtain ⟨i,gi⟩ := large n
    calc
      _ ≤ ∏ j,Y (p n j) (some (e n j)) := mul_le_of_le_one_left pos d1
      _ ≤ Y (p n i) (some (e n i)) := by
        rw [←prod_erase_mul _ _ (mem_univ i)]
        exact mul_le_of_le_one_left (y0 i) (prod_le_one (fun j _ => y0 j) (fun j _ => y_one (hp n j).one_lt _))
      _ ≤ 2/((e n i:ℚ)+1) := ((lt_div_iff₀ (by positivity)).mpr (OMA.CapOrder245212.y_short (hp n i) _)).le
      _ ≤ _ := by gcongr
  have zero : Tendsto (fun n : ℕ => 2/((n:ℚ)+1)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℚ)).const_mul 2
  have err := tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds zero
    (fun n => (error n).1) (fun n => (error n).2)
  apply (show Tendsto (fun n => 2-d*∏ i,Y (p n i) (some (e n i))) atTop (𝓝 2) by
    simpa using (tendsto_const_nhds (x:=(2:ℚ))).sub err).congr
  intro n; linarith only [eq n]

private theorem atom_in_box (K : ℕ) (c d : ℚ) (hc : OddNum c) (d0 : 0<d) (d1 : d≤1) :
    ∃ B : ℕ, ∀ p e : Fin K → ℕ, (∀ i,Nat.Prime (p i)) → (∀ i,Odd (p i)) →
      (∀ i,0<e i) → (∃ i,e i%4=2) →
      c*(∏ i,X (p i) (some (e i)))+d*(∏ i,Y (p i) (some (e i)))=2 →
      ∃ i,e i%4=2 ∧ p i≤B ∧ e i≤B := by
  classical
  obtain ⟨L,alt⟩ := bounded_or_atom K c d hc d0.le d1
  let F : Set (Fin K → ℕ) := {e | ∀ i,0<e i ∧ e i≤L}
  let bases (e : Fin K → ℕ) : Set (Fin K → ℕ) := {p | (∀ i,Nat.Prime (p i)) ∧
    c*(∏ i,X (p i) (some (e i)))+d*(∏ i,Y (p i) (some (e i)))=2}
  have cf : F.Finite := (Set.Finite.pi' (fun _ : Fin K => Set.finite_Iic L)).subset
    (fun _ h i => (h i).2)
  have c0 : 0≤c := by obtain ⟨A,B,_,_,rfl⟩ := hc; positivity
  have bf := cf.biUnion (fun e he => (show (bases e).Finite from
    OMA.FixedExponents245212.finite_bases e (fun i => (he i).1) c d 2 c0 d0))
  have vals := bf.biUnion (fun p _ => Set.finite_range p)
  obtain ⟨M,cap⟩ := vals.bddAbove
  refine ⟨max L M,?_⟩
  intro p e hp ho ep has eq
  rcases alt p e hp ho eq with low | ⟨i,good,pi,ei⟩
  · obtain ⟨i,good⟩ := has
    have ef : e∈F := fun j => ⟨ep j,low j⟩
    have member : p∈⋃ t∈F,bases t := Set.mem_iUnion₂.mpr ⟨e,ef,hp,eq⟩
    have pm := cap (Set.mem_iUnion₂.mpr ⟨p,member,i,rfl⟩)
    exact ⟨i,good,pm.trans (le_max_right _ _),(low i).trans (le_max_left _ _)⟩
  · exact ⟨i,good,pi.trans (le_max_left _ _),ei.trans (le_max_left _ _)⟩

/-- Include the dyadic prime in the normalized equality and then separate
it back out; p and e describe only the odd factors. -/
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

private theorem exact_rank (k K : ℕ) :
    ∃ L : ℕ, ∀ m : ℕ, Odd m → ¬IsSquare m → m.primeFactors.card=K →
    OeisA245212.a (2^k*m)=(σ 1 (2^k*m):ℤ) →
    ∃ q∈m.primeFactors,m.factorization q%4=2 ∧ q≤L ∧ m.factorization q≤L := by
  classical
  let c := X 2 (some k)
  let d := Y 2 (some k)
  have hc : OddNum c := quotient Nat.prime_two (OMA.DyadicPower245212.dyadic_odd k)
  have dp : 0<d := by
    dsimp [d]; rw [y_avg (by decide : 1<2)]
    exact div_pos (sum_pos' (fun i _ => by positivity) ⟨0,by simp,by simp⟩) (by positivity)
  obtain ⟨L,cap⟩ := atom_in_box K c d hc dp (y_one (by decide) _)
  refine ⟨L,?_⟩
  intro m odd nonsq card eq
  let S := m.primeFactors
  let p := S.orderEmbOfFin card
  let e (i : Fin K) := m.factorization (p i)
  have mem (i) : p i∈m.primeFactors := orderEmbOfFin_mem S card i
  have hp (i) := Nat.prime_of_mem_primeFactors (mem i)
  have op (i) := Nat.coprime_two_left.mp ((Nat.coprime_two_left.mpr odd).of_dvd_right
    (Nat.dvd_of_mem_primeFactors (mem i)))
  have ep (i) : 0<e i := (hp i).factorization_pos_of_dvd odd.pos.ne' (Nat.dvd_of_mem_primeFactors (mem i))
  have repr : total p e=m := by
    exact (Fintype.prod_equiv (S.orderIsoOfFin card).toEquiv _
      (fun j : S => j.val^(m.factorization j.val)) (fun _ => rfl)).trans
      (Nat.prod_primeFactors_coe_pow_factorization odd.pos.ne').symm
  have ex : ∃ i,Odd (e i) := by
    by_contra! no
    have even (i) := Nat.not_odd_iff_even.mp (no i)
    choose f hf using even
    apply nonsq
    refine ⟨∏ i,p i^f i,?_⟩
    rw [←repr,total,←prod_mul_distrib]
    exact prod_congr rfl fun i _ => by rw [hf i,pow_add]
  have has := OMA.ExponentParity245212.two_mod_four p e hp op p.injective k (by rw [repr];exact eq) ex
  have norm := normalized_dyadic k p e hp op p.injective (by rw [repr]; exact eq)
  obtain ⟨i,bad,pi,ei⟩ := cap p e hp op ep has norm
  exact ⟨p i,mem i,bad,pi,ei⟩

/-- Fixing the power of two and the number of distinct odd primes, every
nonsquare odd core at equality is divisible exactly by one of a finite list
of prime powers whose exponents are 2 mod 4. Other exponents are unrestricted. -/
theorem bounded_atom (k K : ℕ) :
    ∃ B : ℕ, ∀ m : ℕ, Odd m → ¬IsSquare m → m.primeFactors.card≤K →
    OeisA245212.a (2^k*m)=(σ 1 (2^k*m):ℤ) →
    ∃ q∈m.primeFactors,m.factorization q%4=2 ∧ q≤B ∧ m.factorization q≤B := by
  choose L hL using exact_rank k
  refine ⟨∑ j∈range (K+1),L j,?_⟩
  intro m om ns hc eq
  obtain ⟨q,hq,pq,ql,el⟩ := hL m.primeFactors.card m om ns rfl eq
  have bound := single_le_sum (f:=L) (fun j _ => Nat.zero_le (L j)) (mem_range.mpr (Nat.lt_succ_of_le hc))
  exact ⟨q,hq,pq,ql.trans bound,el.trans bound⟩

#print axioms bounded_atom
end OMA.BoundedAtom245212

end

section

/- Finiteness at bounded rank when the finite odd prime-power factors
cannot cancel the full dyadic denominator of the weighted factor at two. -/
namespace OMA.ParityBudget245212
open Nat Finset Filter Topology OMA.Smooth245212 OMA.SquareCompact245212
open scoped ArithmeticFunction.sigma
open OMA.SquareCompact245212 (infinite_factor)
local notation "v₂" => OMA.WeightVal245212.val

private theorem odd_fraction {N D : ℕ} (nz : 0<N) (dz : 0<D) (dv : 2^(v₂ N)∣D) :
    OddNum ((N:ℚ)/D) := by
  obtain ⟨B,db⟩ := dv
  let A := ordCompl[2] N
  have na : 2^(v₂ N)*A=N := Nat.ordProj_mul_ordCompl_eq_self N 2
  have oa : Odd A := Nat.not_even_iff_odd.mp (fun h =>
    Nat.not_dvd_ordCompl Nat.prime_two nz.ne' (even_iff_two_dvd.mp h))
  have bp : 0<B := by
    by_contra! neg
    have zero : B=0 := by omega
    rw [db,zero,mul_zero] at dz
    omega
  refine ⟨A,B,oa,bp,?_⟩
  rw [←na,db]
  push_cast; field_simp

private theorem scale_down {x : ℚ} (ox : OddNum x) (w : ℕ) : OddNum (x/(2:ℚ)^w) := by
  obtain ⟨A,B,odd,bp,rfl⟩ := ox
  exact ⟨A,B*2^w,odd,Nat.mul_pos bp (Nat.two_pow_pos _),by push_cast; ring⟩

/-- Each odd prime contributes at most this many factors of two to the
reduced numerator of the local weighted ratio. -/
def excess (e : ℕ) := v₂ (e+2)-1

private theorem scale_local {p e w : ℕ} (pr : p.Prime) (op : Odd p) (hw : excess e≤w) :
    OddNum (X p (some e)/(2:ℚ)^w) := by
  let N := W (p^e)
  let D := (e+1)*p^e*2^w
  have np : 0<N := by
    dsimp [N]; rw [w_pow pr]
    exact sum_pos' (fun i _ => Nat.zero_le _) ⟨0,mem_range.mpr (Nat.succ_pos _),by simp⟩
  have dp : 0<D := by dsimp [D]; have := pr.pos; positivity
  have ord := OMA.WeightVal245212.weight_local pr op e
  change v₂ N+1=v₂ (e+1)+v₂ (e+2) at ord
  have inc : v₂ N≤v₂ (e+1)+w := by unfold excess at hw; omega
  have divides : 2^(v₂ N)∣D := by
    apply (pow_dvd_pow 2 inc).trans
    rw [pow_add]
    have dv := Nat.ordProj_dvd (e+1) 2
    exact mul_dvd_mul (dvd_mul_of_dvd_left dv (p^e)) (dvd_refl _)
  have ofrac := odd_fraction np dp divides
  have fx := x_factor pr e
  have eqx : X p (some e)=(N:ℚ)/(((e:ℚ)+1)*p^e) := by
    apply (eq_div_iff (by
      have pos : (0:ℚ)<p := by exact_mod_cast pr.pos
      positivity)).mpr
    exact fx
  rw [eqx,div_div]
  simpa [D] using ofrac

private theorem scaled_coefficient {k b : ℕ} (low : b≤k+v₂ (k+1)) :
    OddNum (X 2 (some k)*(2:ℚ)^b) := by
  let D := (k+1)*2^k
  have dv : 2^b∣D := by
    apply (pow_dvd_pow 2 low).trans
    rw [pow_add,Nat.mul_comm]
    exact mul_dvd_mul (Nat.ordProj_dvd (k+1) 2) (dvd_refl _)
  obtain ⟨B,db⟩ := dv
  have dp : 0<D := by dsimp [D]; positivity
  have bp : 0<B := by
    by_contra! neg
    have z : B=0 := by omega
    rw [db,z,mul_zero] at dp
    omega
  have fx := x_factor Nat.prime_two k
  have bd := congrArg (Nat.cast : ℕ → ℚ) db
  dsimp only [D] at bd
  push_cast at bd
  refine ⟨W (2^k),B,OMA.DyadicPower245212.dyadic_odd k,bp,?_⟩
  apply (eq_div_iff (by exact_mod_cast bp.ne' : (B:ℚ)≠0)).mpr
  linear_combination fx - X 2 (some k)*bd

/-- Only count dyadic excess carried by an exactly bounded base and exponent. -/
def visible (B p e : ℕ) := if p≤B ∧ e≤B then excess e else 0

private theorem visible_gap (k K : ℕ) :
    ∃ B : ℕ, ∃ δ : ℚ, 0<δ ∧ ∀ p e : Fin K → ℕ, (∀ i,Nat.Prime (p i)) → (∀ i,Odd (p i)) →
      (∑ i,visible B (p i) (e i))≤k+v₂ (k+1) →
      δ≤|X 2 (some k)*(∏ i,X (p i) (some (e i)))-2| := by
  by_contra! bad
  have pick (n : ℕ) := bad n (1/((n:ℚ)+1)) (by positivity)
  choose p e hp ho he close using pick
  let seq (n : ℕ) := (p n,e n)
  obtain ⟨g,sorted⟩ := wellQuasiOrdered_le.exists_monotone_subseq seq
  let Capture (i : Fin K) (x : ℚ) := ∃ w : ℕ, OddNum (x/(2:ℚ)^w) ∧
    ∀ᶠ n in atTop,w≤visible (g n) (p (g n) i) (e (g n) i)
  have points (i : Fin K) : ∃ x : ℚ,Capture i x ∧
      Tendsto (fun n => X (p (g n) i) (some (e (g n) i))) atTop (𝓝 x) := by
    have trivialWeight (x : ℚ) (hx : OddNum x) : Capture i x :=
      ⟨0,by simpa using hx,Eventually.of_forall fun _ => Nat.zero_le _⟩
    apply factor_limit_by (Capture i) _ _
      (fun _ _ le => (sorted _ _ le).1 i) (fun _ _ le => (sorted _ _ le).2 i)
      (fun n => hp (g n) i) (fun n => ho (g n) i) (trivialWeight _ OMA.SquareCompact245212.one)
      (fun _ pr op => trivialWeight _ (OMA.SquareCompact245212.infinite_factor pr op))
    intro P E pP eE
    obtain ⟨n,pn,en⟩ := (pP.and eE).exists
    change p (g n) i=P at pn
    refine ⟨excess E,scale_local (pn ▸ hp (g n) i) (pn ▸ ho (g n) i) le_rfl,?_⟩
    have large := g.strictMono.tendsto_atTop.eventually (eventually_ge_atTop (max P E))
    filter_upwards [pP,eE,large] with j pj ej big
    change p (g j) i=P at pj
    change e (g j) i=E at ej
    simp [visible,pj,ej,(le_max_left P E).trans big,(le_max_right P E).trans big]
  choose x capture conv using points
  choose w ox see using capture
  obtain ⟨n,hn⟩ := (Filter.eventually_all.mpr see).exists
  have low := (sum_le_sum (s:=univ) (fun i _ => hn i)).trans (he (g n))
  have prod (s : Finset (Fin K)) : OddNum (∏ i∈s,x i/(2:ℚ)^(w i)) := by
    induction s using Finset.induction_on with
    | empty => simpa using OMA.SquareCompact245212.one
    | @insert i s hi ih => simpa only [prod_insert hi] using OMA.SquareCompact245212.mul (ox i) ih
  have od := OMA.SquareCompact245212.mul (scaled_coefficient low) (prod univ)
  rw [prod_div_distrib,prod_pow_eq_pow_sum] at od
  let c := X 2 (some k)
  have distinct := ne_two (show OddNum (c*∏ i,x i) by
    dsimp only [c]; convert od using 1; field_simp)
  have limit := (tendsto_finsetProd univ (fun i _ => conv i)).const_mul c
  have t2 : Tendsto (fun n => c*∏ i,X (p n i) (some (e n i))) atTop (𝓝 2) := by
    have hz := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℚ)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (show Tendsto (fun n : ℕ => 2-1/((n:ℚ)+1)) atTop (𝓝 2) by simpa using tendsto_const_nhds.sub hz)
      (show Tendsto (fun n : ℕ => 2+1/((n:ℚ)+1)) atTop (𝓝 2) by simpa using hz.const_add 2)
    · intro n; linarith only [(abs_lt.mp (close n)).1]
    · intro n; linarith only [(abs_lt.mp (close n)).2]
  exact distinct (tendsto_nhds_unique limit (t2.comp g.strictMono.tendsto_atTop))

private def Config {K : ℕ} (c d : ℚ) (B H : ℕ)
    (v : (Fin K → ℕ) × (Fin K → ℕ)) :=
  (∀ i,Nat.Prime (v.1 i)) ∧ (∀ i,Odd (v.1 i)) ∧ (∀ i,0<v.2 i) ∧
  (∑ i,visible B (v.1 i) (v.2 i))≤H ∧
  c*(∏ i,X (v.1 i) (some (v.2 i)))+d*(∏ i,Y (v.1 i) (some (v.2 i)))=2

private theorem configs (K k : ℕ) (d : ℚ) (d0 : 0<d) (d1 : d≤1) :
    ∃ B, {v | Config (K:=K) (X 2 (some k)) d B (k+v₂ (k+1)) v}.Finite := by
  let c := X 2 (some k)
  have c0 := x_nonneg (by decide : 1<2) (some k)
  obtain ⟨B,δ,hδ,sep⟩ := visible_gap k K
  refine ⟨B,?_⟩
  obtain ⟨L,hL⟩ := exists_nat_gt (2/δ)
  have size (p e : Fin K → ℕ) (cfg : Config c d B (k+v₂ (k+1)) (p,e)) (i : Fin K) : e i<L := by
    obtain ⟨hp,ho,_,he,eq⟩ := cfg
    have bound := sep p e hp ho he
    change δ≤|c*(∏ j,X (p j) (some (e j)))-2| at bound
    have y0 (j) := y_nonneg (hp j).one_lt (some (e j))
    have yp := prod_nonneg (s:=univ) (fun j _ => y0 j)
    have z := mul_nonneg d0.le yp
    change c*(∏ j,X (p j) (some (e j)))+d*(∏ j,Y (p j) (some (e j)))=2 at eq
    rw [abs_of_nonpos (by linarith only [eq,z])] at bound
    have upper : δ≤Y (p i) (some (e i)) := by
      apply (show δ≤d*∏ j,Y (p j) (some (e j)) by linarith only [eq,bound]).trans
      apply (mul_le_of_le_one_left yp d1).trans
      rw [←prod_erase_mul _ _ (mem_univ i)]
      exact mul_le_of_le_one_left (y0 i) (prod_le_one (fun j _ => y0 j)
        (fun j _ => y_one (hp j).one_lt _))
    have hh := OMA.CapOrder245212.y_short (hp i) (e i)
    have mult := mul_le_mul_of_nonneg_right upper (show 0≤(e i:ℚ)+1 by positivity)
    have le : (e i:ℚ)<2/δ := (lt_div_iff₀ hδ).mpr (by linarith only [hh,mult,hδ])
    exact_mod_cast le.trans hL
  apply Set.Finite.of_finite_fibers Prod.snd
  · apply (Set.Finite.pi' (fun _ : Fin K => Set.finite_Iio L)).subset
    rintro e ⟨⟨p,v⟩,h,rfl⟩
    exact size _ _ h
  · rintro e ⟨⟨p,v⟩,cfg,rfl⟩
    have finite := OMA.FixedExponents245212.finite_bases v cfg.2.2.1 c d 2 c0 d0
    apply (finite.image (fun q => (q,v))).subset
    rintro ⟨q,f⟩ ⟨hf,hv⟩
    have same : f=v := hv
    subst f
    exact ⟨q,⟨hf.1,hf.2.2.2.2⟩,rfl⟩

private theorem rank_finite (k K : ℕ) :
    ∃ B : ℕ,{m : ℕ | Odd m ∧ m.primeFactors.card=K ∧
      (∑ q∈m.primeFactors,visible B q (m.factorization q))≤k+v₂ (k+1) ∧
      OeisA245212.a (2^k*m)=(σ 1 (2^k*m):ℤ)}.Finite := by
  classical
  let c := X 2 (some k)
  let d := Y 2 (some k)
  have dp : 0<d := by
    dsimp [d]; rw [y_avg (by decide : 1<2)]
    exact div_pos (sum_pos' (fun i _ => by positivity) ⟨0,by simp,by simp⟩) (by positivity)
  obtain ⟨B,fin⟩ := configs K k d dp (y_one (by decide) _)
  refine ⟨B,?_⟩
  apply (fin.image (fun v => total v.1 v.2)).subset
  rintro m ⟨om,card,budget,eq⟩
  let S := m.primeFactors
  let p := S.orderEmbOfFin card
  let e (i : Fin K) := m.factorization (p i)
  have mem (i) : p i∈m.primeFactors := orderEmbOfFin_mem S card i
  have hp (i) := Nat.prime_of_mem_primeFactors (mem i)
  have op (i) := Nat.coprime_two_left.mp ((Nat.coprime_two_left.mpr om).of_dvd_right
    (Nat.dvd_of_mem_primeFactors (mem i)))
  have ep (i) := (hp i).factorization_pos_of_dvd om.pos.ne' (Nat.dvd_of_mem_primeFactors (mem i))
  have repr : total p e=m := by
    exact (Fintype.prod_equiv (S.orderIsoOfFin card).toEquiv _
      (fun j : S => j.val^(m.factorization j.val)) (fun _ => rfl)).trans
      (Nat.prod_primeFactors_coe_pow_factorization om.pos.ne').symm
  let w (i : Fin K) := visible B (p i) (e i)
  have wsum : ∑ i,w i = ∑ q∈m.primeFactors,visible B q (m.factorization q) := by
    exact (Fintype.sum_equiv (S.orderIsoOfFin card).toEquiv _
      (fun j : S => visible B j.val (m.factorization j.val)) (fun _ => rfl)).trans
      (Finset.sum_coe_sort S (fun q => visible B q (m.factorization q)))
  have norm := OMA.BoundedAtom245212.normalized_dyadic k p e hp op p.injective (by rw [repr];exact eq)
  exact ⟨(p,e),⟨hp,op,ep,wsum.le.trans budget,norm⟩,repr⟩

/-- Apart from finitely many solutions, bounded exceptional prime powers
must together supply enough powers of two for the fixed dyadic coefficient.
Large primes and large exponents do not count towards the required sum. -/
theorem finite_visible_budget (k K : ℕ) :
    ∃ B : ℕ,{m : ℕ | Odd m ∧ m.primeFactors.card≤K ∧
      (∑ q∈m.primeFactors,visible B q (m.factorization q))≤k+v₂ (k+1) ∧
      OeisA245212.a (2^k*m)=(σ 1 (2^k*m):ℤ)}.Finite := by
  choose L fin using rank_finite k
  let B := ∑ j∈range (K+1),L j
  refine ⟨B,((Set.finite_Iic K).biUnion (fun j _ => fin j)).subset ?_⟩
  rintro m ⟨om,card,v,eq⟩
  refine Set.mem_iUnion₂.mpr ⟨m.primeFactors.card,card,om,rfl,?_,eq⟩
  have less : L m.primeFactors.card≤B := single_le_sum (fun j _ => Nat.zero_le (L j))
    (mem_range.mpr (Nat.lt_succ_of_le card))
  apply (sum_le_sum (s:=m.primeFactors) (f:=fun q => visible (L m.primeFactors.card) q (m.factorization q))
    (g:=fun q => visible B q (m.factorization q)) ?_).trans v
  intro q hq
  unfold visible
  split_ifs <;> omega

/-- No upper bound on any prime or any individual exponent: only finitely
many positive odd parts with bounded rank and bounded total dyadic excess
can satisfy the original equality, for each fixed power of two. -/
theorem finite_budget (k K : ℕ) :
    {m : ℕ | Odd m ∧ m.primeFactors.card≤K ∧
      (∑ q∈m.primeFactors,excess (m.factorization q))≤k+v₂ (k+1) ∧
      OeisA245212.a (2^k*m)=(σ 1 (2^k*m):ℤ)}.Finite := by
  obtain ⟨B,fin⟩ := finite_visible_budget k K
  apply fin.subset
  rintro m ⟨om,card,v,eq⟩
  exact ⟨om,card,(sum_le_sum (fun q _ => show visible B q (m.factorization q)≤_ by
    unfold visible; split_ifs <;> omega)).trans v,eq⟩

#print axioms finite_budget
#print axioms finite_visible_budget
end OMA.ParityBudget245212

end

section

/- A single bounded odd factor supplying the dyadic excess prevents
resonance with any coprime product of Euler numerators. -/
namespace OMA.RankThreeAnchor245212
open Nat Finset ArithmeticFunction OMA.Smooth245212
open scoped ArithmeticFunction.sigma

theorem dyadic_weight (k : ℕ) : W (2^k)=k*2^(k+1)+1 := by
  rw [w_pow Nat.prime_two]
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [sum_range_succ _ (k+1),ih,pow_succ (2:ℕ) (k+1)]
    ring

theorem weight_unit {r : ℕ} (pr : r.Prime) (a : ℕ) : r.Coprime (W (r^a)) := by
  apply pr.coprime_iff_not_dvd.mpr
  intro dv
  let : Fact r.Prime := ⟨pr⟩
  have zero := (ZMod.natCast_eq_zero_iff (W (r^a)) r).mpr dv
  rw [w_pow pr,sum_range_succ'] at zero
  push_cast at zero
  simp [pow_succ] at zero

theorem high {k r a : ℕ} (hr : 2 ≤ r)
    (hex : k + OMA.WeightVal245212.val (k+1) < OMA.ParityBudget245212.excess a) :
    W (2^k) < r^a := by
  have hv : k+2 ≤ (a+2).factorization 2 := by
    unfold OMA.ParityBudget245212.excess OMA.WeightVal245212.val at hex; omega
  have dv : 2^(k+2) ∣ a+2 := (pow_dvd_pow _ hv).trans (Nat.ordProj_dvd (a+2) 2)
  have bound := Nat.le_of_dvd (by omega : 0 < a+2) dv
  have size (j : ℕ) : 2*j+4 ≤ 2^(j+2) := by
    induction j with
    | zero => decide
    | succ j ih => rw [pow_succ 2 (j+2)]; omega
  have exp : 2*(k+1) ≤ a := by have := size k; omega
  have power := (Nat.pow_le_pow_right (by decide : 0<2) exp).trans (Nat.pow_le_pow_left hr a)
  apply lt_of_lt_of_le _ power
  rw [dyadic_weight,show 2*(k+1)=(k+1)+(k+1) by omega,pow_add 2 (k+1) (k+1)]
  have inc : k+1 < 2^(k+1) := Nat.lt_two_pow_self
  have gap := Nat.mul_le_mul_right (2^(k+1)) inc
  have nz := Nat.two_pow_pos (k+1)
  nlinarith only [gap,nz,inc]

/-- The Euler numerator U may contain any number of other primes. -/
theorem no_resonance {k r a U V : ℕ} (pr : r.Prime) (odd : r≠2)
    (cop : r.Coprime U) (large : W (2^k) < r^a) :
    W (2^k*r^a)*U ≠ 2*(2^k*r^a)*(σ 0 (2^k*r^a))*V := by
  intro eq
  have base := ((Nat.coprime_primes Nat.prime_two pr).mpr odd.symm).pow_left k
  rw [w_mult.map_mul_of_coprime (base.pow_right a),mul_assoc] at eq
  have d : r^a ∣ 2*(2^k*r^a)*(σ 0 (2^k*r^a))*V := by
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_mul_left _ _) _) _) _
  have fac := ((weight_unit pr a).mul_right cop).pow_left a
  have divides : r^a ∣ W (2^k) := fac.dvd_of_dvd_mul_right (eq ▸ d)
  have pos : 0 < W (2^k) := by rw [dyadic_weight]; omega
  exact large.not_ge (Nat.le_of_dvd pos divides)

#print axioms high
#print axioms no_resonance
end OMA.RankThreeAnchor245212

end

section

/- A cofactor whose prime-power denominator survives in the weighted
moment forces another bounded prime and exponent in any fixed-rank extension. -/
namespace OMA.CohortAtom245212
open Nat Finset Filter Topology OMA.Smooth245212 OMA.SquareCompact245212
open scoped ArithmeticFunction.sigma

private def UnitNum (r : ℕ) (x : ℚ) := ∃ U V : ℕ, r.Coprime U ∧ 0<V ∧ x=(U:ℚ)/V

private theorem one (r : ℕ) : UnitNum r 1 := ⟨1,1,by simp,by decide,by norm_num⟩

private theorem mul {r : ℕ} {x y : ℚ} (ux : UnitNum r x) (uy : UnitNum r y) : UnitNum r (x*y) := by
  obtain ⟨A,B,ca,hb,rfl⟩ := ux
  obtain ⟨U,V,cu,hv,rfl⟩ := uy
  exact ⟨A*U,B*V,ca.mul_right cu,Nat.mul_pos hb hv,by push_cast; ring⟩

private theorem cap {r p : ℕ} (pr : p.Prime) (cop : r.Coprime p) : UnitNum r (X p none) := by
  refine ⟨p,p-1,cop,by have := pr.one_lt; omega,?_⟩
  have pp : (1:ℚ)<p := by exact_mod_cast pr.one_lt
  simp only [X,Y,sub_zero,Nat.cast_sub pr.one_le,Nat.cast_one]
  field_simp [show (p:ℚ)-1≠0 by linarith]; ring

private theorem product {K r : ℕ} (x : Fin K → ℚ) (unit : ∀ i,UnitNum r (x i)) :
    UnitNum r (∏ i,x i) := by
  have aux (s : Finset (Fin K)) : UnitNum r (∏ i∈s,x i) := by
    induction s using Finset.induction_on with
    | empty => simpa using one r
    | @insert i s hi ih => simpa only [prod_insert hi] using mul (unit i) ih
  exact aux univ

theorem at_two {K : ℕ} (c d : ℚ) (d0 : 0≤d) (d1 : d≤1)
    (p e : ℕ → Fin K → ℕ) (hp : ∀ n i,Nat.Prime (p n i)) (large : ∀ n,∃ i,n<e n i)
    (eqn : ∀ n,c*(∏ i,X (p n i) (some (e n i)))+d*(∏ i,Y (p n i) (some (e n i)))=2) :
    Tendsto (fun n => c*∏ i,X (p n i) (some (e n i))) atTop (𝓝 2) := by
  have error (n : ℕ) : 0 ≤ d*∏ i,Y (p n i) (some (e n i)) ∧
      d*(∏ i,Y (p n i) (some (e n i))) ≤ 2/((n:ℚ)+1) := by
    have y0 (j) := y_nonneg (hp n j).one_lt (some (e n j))
    have pos := prod_nonneg (s:=univ) (fun j _ => y0 j)
    obtain ⟨i,gi⟩ := large n
    refine ⟨mul_nonneg d0 pos,(mul_le_of_le_one_left pos d1).trans ?_⟩
    calc
      _ ≤ Y (p n i) (some (e n i)) := by
        rw [←prod_erase_mul _ _ (mem_univ i)]
        exact mul_le_of_le_one_left (y0 i) (prod_le_one (fun j _ => y0 j) (fun j _ => y_one (hp n j).one_lt _))
      _ ≤ 2/((e n i:ℚ)+1) := ((lt_div_iff₀ (by positivity)).mpr (OMA.CapOrder245212.y_short (hp n i) _)).le
      _ ≤ _ := by gcongr
  have zero : Tendsto (fun n : ℕ => 2/((n:ℚ)+1)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℚ)).const_mul 2
  have err := tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds zero
    (fun n => (error n).1) (fun n => (error n).2)
  apply (show Tendsto (fun n => 2-d*∏ i,Y (p n i) (some (e n i))) atTop (𝓝 2) by
    simpa using (tendsto_const_nhds (x:=(2:ℚ))).sub err).congr
  intro n; linarith only [eqn n]

/-- Either all exponents are bounded, or at least one entire prime-power
factor has its base and exponent simultaneously bounded. -/
theorem alternative (K r : ℕ) (c d : ℚ) (d0 : 0≤d) (d1 : d≤1)
    (miss : ∀ U V : ℕ,r.Coprime U → 0<V → c*((U:ℚ)/V)≠2) :
    ∃ B : ℕ, ∀ p e : Fin K → ℕ, (∀ i,Nat.Prime (p i)) → (∀ i,Odd (p i)) → (∀ i,r.Coprime (p i)) →
      c*(∏ i,X (p i) (some (e i)))+d*(∏ i,Y (p i) (some (e i)))=2 →
      (∀ i,e i≤B) ∨ ∃ i,p i≤B ∧ e i≤B := by
  by_contra! bad
  choose p e hp ho cop eqn large avoid using bad
  let seq (n : ℕ) := (p n,e n)
  obtain ⟨g,sorted⟩ := wellQuasiOrdered_le.exists_monotone_subseq seq
  have points (i : Fin K) : ∃ x : ℚ,UnitNum r x ∧
      Tendsto (fun n => X (p (g n) i) (some (e (g n) i))) atTop (𝓝 x) := by
    apply factor_limit_restricted _ _ _ (fun _ _ le => (sorted _ _ le).1 i)
      (fun _ _ le => (sorted _ _ le).2 i) (fun n => hp (g n) i) (fun n => ho (g n) i) (one r)
    · intro P pr _ hP
      obtain ⟨n,hn⟩ := hP.exists
      exact cap pr (hn ▸ cop (g n) i)
    · intro P E hP hE
      have big := g.strictMono.tendsto_atTop.eventually (eventually_ge_atTop (max P E))
      obtain ⟨n,pn,en,gn⟩ := (hP.and (hE.and big)).exists
      change p (g n) i=P at pn
      change e (g n) i=E at en
      have a := avoid (g n) i
      rw [pn,en] at a
      exact False.elim ((not_lt_of_ge ((le_max_right P E).trans gn)) (a ((le_max_left P E).trans gn)))
  choose x ox conv using points
  obtain ⟨U,V,unit,vpos,prod⟩ := product x ox
  have limit := (tendsto_finsetProd univ (fun i _ => conv i)).const_mul c
  have two := (at_two c d d0 d1 p e hp large eqn).comp g.strictMono.tendsto_atTop
  exact miss U V unit vpos (prod ▸ tendsto_nhds_unique limit two)

#print axioms alternative

/-- Positive exponents on a nonempty support turn the alternative into a
bounded pair: for bounded exponent vectors, only finitely many bases work. -/
theorem atom {K : ℕ} (pos : 0<K) (r : ℕ) (c d : ℚ) (c0 : 0≤c) (d0 : 0<d) (d1 : d≤1)
    (miss : ∀ U V : ℕ,r.Coprime U → 0<V → c*((U:ℚ)/V)≠2) :
    ∃ B : ℕ, ∀ p e : Fin K → ℕ, (∀ i,Nat.Prime (p i)) → (∀ i,Odd (p i)) → (∀ i,r.Coprime (p i)) →
      (∀ i,0<e i) → c*(∏ i,X (p i) (some (e i)))+d*(∏ i,Y (p i) (some (e i)))=2 →
      ∃ i,p i≤B ∧ e i≤B := by
  classical
  obtain ⟨L,alt⟩ := alternative K r c d d0.le d1 miss
  let F : Set (Fin K → ℕ) := {e | ∀ i,0<e i ∧ e i≤L}
  let bases (e : Fin K → ℕ) : Set (Fin K → ℕ) := {p | (∀ i,Nat.Prime (p i)) ∧
    c*(∏ i,X (p i) (some (e i)))+d*(∏ i,Y (p i) (some (e i)))=2}
  have cf : F.Finite := (Set.Finite.pi' (fun _ : Fin K => Set.finite_Iic L)).subset
    (fun _ h i => (h i).2)
  have bf := cf.biUnion (fun e he => (show (bases e).Finite from
    OMA.FixedExponents245212.finite_bases e (fun i => (he i).1) c d 2 c0 d0))
  obtain ⟨M,cap⟩ := (bf.biUnion (fun p _ => Set.finite_range p)).bddAbove
  refine ⟨max L M,?_⟩
  intro p e hp ho cop ep eq
  rcases alt p e hp ho cop eq with low | ⟨i,pi,ei⟩
  · let i : Fin K := ⟨0,pos⟩
    have ef : e∈F := fun j => ⟨ep j,low j⟩
    have member : p∈⋃ t∈F,bases t := Set.mem_iUnion₂.mpr ⟨e,ef,hp,eq⟩
    have pm := cap (Set.mem_iUnion₂.mpr ⟨p,member,i,rfl⟩)
    exact ⟨i,pm.trans (le_max_right _ _),(low i).trans (le_max_left _ _)⟩
  · exact ⟨i,pi.trans (le_max_left _ _),ei.trans (le_max_left _ _)⟩

theorem miss_core {k r a : ℕ} (pr : r.Prime) (odd : r≠2) (large : W (2^k)<r^a)
    (U V : ℕ) (unit : r.Coprime U) (vpos : 0<V) :
    (X 2 (some k)*X r (some a))*((U:ℚ)/V)≠2 := by
  intro eq
  let d2 := (k+1)*2^k
  let dr := (a+1)*r^a
  have fx : X 2 (some k)*(d2:ℚ)=W (2^k) := by simpa [d2] using x_factor Nat.prime_two k
  have fy : X r (some a)*(dr:ℚ)=W (r^a) := by simpa [dr] using x_factor pr a
  have diff := OMA.RankThreeAnchor245212.no_resonance pr odd unit large (V:=V)
  apply diff
  have cp := ((Nat.coprime_primes Nat.prime_two pr).mpr odd.symm).pow_left k
  rw [w_mult.map_mul_of_coprime (cp.pow_right a),ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
      (cp.pow_right a),ArithmeticFunction.sigma_zero_apply_prime_pow Nat.prime_two,
      ArithmeticFunction.sigma_zero_apply_prime_pow pr]
  have rhs : 2*(2^k*r^a)*((k+1)*(a+1))*V=2*d2*dr*V := by unfold d2 dr; ring
  rw [rhs]
  have eq' : (X 2 (some k)*X r (some a))*U=2*V := by
    rw [←mul_div_assoc] at eq
    exact (div_eq_iff (by exact_mod_cast vpos.ne')).mp eq
  exact_mod_cast (show (W (2^k):ℚ)*W (r^a)*U=2*d2*dr*V by
    rw [←fx,←fy]; linear_combination ((d2:ℚ)*dr)*eq')

#print axioms atom
#print axioms miss_core
end OMA.CohortAtom245212

end

section

/- The largest prime in a nonempty Euler resonance must divide the
target numerator. Thus a fixed cofactor forces a bounded prime power
unless a remaining prime divides the cofactor's divisor count. -/
namespace OMA.CofactorPrimeChain245212
open Finset Nat Filter Topology OMA.Smooth245212 OMA.SquareCompact245212
open OMA.CohortAtom245212 (at_two)
open scoped ArithmeticFunction.sigma

private def EulerTerm (H u v : ℕ) : Prop :=
  (u=1 ∧ v=1) ∨ (u.Prime ∧ ¬u∣H ∧ v=u-1)

private theorem no_product {K A H : ℕ} (below : A<H) (u v : Fin K→ℕ)
    (terms : ∀i,EulerTerm H (u i) (v i)) :
    A*(∏ i,u i)≠H*(∏ i,v i) := by
  classical
  by_cases one : ∀i,u i=1
  · have neutral (i) : v i=1 := by
      rcases terms i with z|z
      · exact z.2
      · have := z.1.one_lt; rw [one i] at this; omega
    simpa [one,neutral] using below.ne
  push Not at one
  obtain ⟨j,hj⟩:=one
  obtain ⟨m,_,maxim⟩:=univ.exists_max_image u ⟨j,mem_univ _⟩
  have far : 1<u j := by rcases terms j with z|z; exact False.elim (hj z.1); exact z.1.one_lt
  have big := far.trans_le (maxim j (mem_univ _))
  rcases terms m with z|⟨pr,avoid,_⟩
  · omega
  intro eqn
  have dvd : u m∣H*(∏ i,v i) := eqn ▸ dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem u (mem_univ m)) A
  obtain target|rest:=pr.dvd_mul.mp dvd
  · exact avoid target
  obtain ⟨i,_,iv⟩:= (pr.prime.dvd_finsetProd_iff v).mp rest
  have upper := maxim i (mem_univ _)
  rcases terms i with z|z
  · rw [z.2] at iv
    exact (not_le_of_gt big) (Nat.le_of_dvd (by decide) iv)
  · have pos := z.1.one_lt
    have gap : 0<v i ∧ v i<u m := by rw [z.2.2];omega
    exact gap.2.not_ge (Nat.le_of_dvd gap.1 iv)

private theorem no_limit {K A T : ℕ} (tpos : 0<T) (below : A<2*T) (x : Fin K→ℚ)
    (repr : ∀i,∃ u v : ℕ,EulerTerm (2*T) u v ∧ x i=(u:ℚ)/v) :
    ((A:ℚ)/T)*(∏ i,x i)≠2 := by
  classical
  choose u v uv frac using repr
  have pos (i) : 0<v i := by
    rcases uv i with z|z
    · rw [z.2];decide
    · rw [z.2.2];have := z.1.one_lt;omega
  have nonzero : (∏ i,(v i:ℚ))≠0 := (prod_pos (fun i _=>by exact_mod_cast pos i)).ne'
  have original := no_product below u v uv
  intro bad
  simp only [frac,prod_div_distrib] at bad
  field_simp [nonzero,show (T:ℚ)≠0 by exact_mod_cast tpos.ne'] at bad
  apply original
  exact_mod_cast (show (A:ℚ)*(∏ i,(u i:ℚ))=(2*T)*(∏ i,(v i:ℚ)) by linarith only [bad])

private theorem cap_repr {p H : ℕ} (pr : p.Prime) (avoid : ¬p∣H) :
    ∃ u v : ℕ,EulerTerm H u v ∧ X p none=(u:ℚ)/v := by
  refine ⟨p,p-1,Or.inr ⟨pr,avoid,rfl⟩,?_⟩
  have pp : (1:ℚ)<p := by exact_mod_cast pr.one_lt
  simp only [X,Y,sub_zero,Nat.cast_sub pr.one_le,Nat.cast_one]
  field_simp [show (p:ℚ)-1≠0 by linarith];ring

theorem alternative (K A T : ℕ) (tpos : 0<T) (below : A<2*T)
    (d : ℚ) (d0 : 0≤d) (d1 : d≤1) :
    ∃ B : ℕ, ∀ p e : Fin K→ℕ, (∀i,(p i).Prime) → (∀i,Odd (p i)) → (∀i,¬p i∣2*T) →
      ((A:ℚ)/T)*(∏ i,X (p i) (some (e i)))+d*(∏ i,Y (p i) (some (e i)))=2 →
      (∀i,e i≤B) ∨ ∃i,p i≤B ∧ e i≤B := by
  by_contra! bad
  choose p e hp ho avoid eqn large leave using bad
  let seq (n : ℕ) := (p n,e n)
  obtain ⟨g,sorted⟩ := wellQuasiOrdered_le.exists_monotone_subseq seq
  have points (i : Fin K) : ∃ x : ℚ,(∃ u v : ℕ,EulerTerm (2*T) u v ∧ x=(u:ℚ)/v) ∧
      Tendsto (fun n => X (p (g n) i) (some (e (g n) i))) atTop (𝓝 x) := by
    apply factor_limit_restricted _ _ _ (fun _ _ le => (sorted _ _ le).1 i)
      (fun _ _ le => (sorted _ _ le).2 i) (fun n=>hp (g n) i) (fun n=>ho (g n) i)
      ⟨1,1,Or.inl ⟨rfl,rfl⟩,by norm_num⟩
    · intro P pr _ fixed
      obtain ⟨n,same⟩:=fixed.exists
      exact cap_repr pr (same ▸ avoid (g n) i)
    · intro P E hP hE
      have big:=g.strictMono.tendsto_atTop.eventually (eventually_ge_atTop (max P E))
      obtain ⟨n,pn,en,gn⟩:=(hP.and (hE.and big)).exists
      change p (g n) i=P at pn
      change e (g n) i=E at en
      have both:=leave (g n) i
      rw [pn,en] at both
      exact False.elim ((not_lt_of_ge ((le_max_right P E).trans gn)) (both ((le_max_left P E).trans gn)))
  choose x ox conv using points
  have limit:=(tendsto_finsetProd univ (fun i _=>conv i)).const_mul ((A:ℚ)/T)
  have two:=(OMA.CohortAtom245212.at_two _ d d0 d1 p e hp large eqn).comp g.strictMono.tendsto_atTop
  exact no_limit tpos below x ox (tendsto_nhds_unique limit two)

#print axioms alternative
end OMA.CofactorPrimeChain245212

end

section

/- A fixed-rank family with no cross divisibility between its prime
bases and its exponent lengths is finite. The induction absorbs one
bounded prime power into the cofactor. -/
namespace OMA.CofactorCrossCount245212
open Finset Nat OMA.Smooth245212
open OMA.FixedExponents245212 (y_pos)
open scoped ArithmeticFunction.sigma

def balance {K : ℕ} (A T : ℕ) (d : ℚ) (p e : Fin K→ℕ) : Prop :=
  ((A:ℚ)/T)*(∏ i,X (p i) (some (e i)))+d*(∏ i,Y (p i) (some (e i)))=2

structure Admissible {K : ℕ} (T : ℕ) (p e : Fin K→ℕ) : Prop where
  prime (i) : (p i).Prime
  odd (i) : Odd (p i)
  positive (i) : 0<e i
  distinct : Function.Injective p
  avoid (i) : ¬p i∣2*T
  cross (i j) : i≠j → ¬p i∣e j+1

private theorem below {K A T : ℕ} {d : ℚ} {p e : Fin K→ℕ}
    (tp : 0<T) (dp : 0<d) (ok : Admissible T p e) (eqn : balance A T d p e) : A<2*T := by
  have one (i) : 1≤X (p i) (some (e i)) :=
    le_add_of_nonneg_right (div_nonneg (sub_nonneg.mpr (y_one (ok.prime i).one_lt _))
      (sub_nonneg.mpr (by exact_mod_cast (ok.prime i).one_le)))
  have all : 1≤∏i,X (p i) (some (e i)) := by
    calc
      1 = ∏ _i : Fin K,(1:ℚ) := by simp
      _ ≤ _ := prod_le_prod (fun _ _=>by norm_num) (fun i _=>one i)
  have yp := prod_pos (s:=univ) (fun i _=>OMA.FixedExponents245212.y_pos (ok.prime i) (e i))
  have c0 : 0≤(A:ℚ)/T := by positivity
  have small : (A:ℚ)/T<2 := by unfold balance at eqn;nlinarith only [eqn,mul_pos dp yp,mul_nonneg c0 (sub_nonneg.mpr all)]
  exact_mod_cast (div_lt_iff₀ (by exact_mod_cast tp : (0:ℚ)<T)).mp small

private theorem atom {K A T : ℕ} {d : ℚ} (kp : 0<K) (tp : 0<T) (cut : A<2*T)
    (dp : 0<d) (ds : d≤1) :
    ∃ B : ℕ, ∀ p e : Fin K→ℕ, Admissible T p e → balance A T d p e → ∃i,p i≤B ∧ e i≤B := by
  classical
  obtain ⟨L,alt⟩:=OMA.CofactorPrimeChain245212.alternative K A T tp cut d dp.le ds
  let F : Set (Fin K→ℕ) := {e | ∀i,0<e i ∧ e i≤L}
  let bases (e : Fin K→ℕ) : Set (Fin K→ℕ) := {p | (∀i,(p i).Prime) ∧ balance A T d p e}
  have cf : F.Finite := (Set.Finite.pi' (fun _ : Fin K=>Set.finite_Iic L)).subset
    (fun _ h i=>(h i).2)
  have bf := cf.biUnion (fun e he=>(show (bases e).Finite from
    OMA.FixedExponents245212.finite_bases e (fun i=>(he i).1) ((A:ℚ)/T) d 2 (by positivity) dp))
  obtain ⟨M,cap⟩:=(bf.biUnion (fun p _=>Set.finite_range p)).bddAbove
  refine ⟨max L M,?_⟩
  intro p e ok eqn
  rcases alt p e ok.prime ok.odd ok.avoid eqn with low|⟨i,pi,ei⟩
  · let i : Fin K:=⟨0,kp⟩
    have ef : e∈F:=fun j=>⟨ok.positive j,low j⟩
    have mem : p∈⋃ t∈F,bases t:=Set.mem_iUnion₂.mpr ⟨e,ef,ok.prime,eqn⟩
    have pm:=cap (Set.mem_iUnion₂.mpr ⟨p,mem,i,rfl⟩)
    exact ⟨i,pm.trans (le_max_right _ _),(low i).trans (le_max_left _ _)⟩
  · exact ⟨i,pi.trans (le_max_left _ _),ei.trans (le_max_left _ _)⟩

private def scale (p e : ℕ) := (e+1)*p^e

private theorem peel {K A T : ℕ} {d : ℚ} {p e : Fin (K+1)→ℕ} (j : Fin (K+1))
    (tp : 0<T) (ok : Admissible T p e) (eqn : balance A T d p e) :
    Admissible (T*scale (p j) (e j)) (p ∘ j.succAbove) (e ∘ j.succAbove) ∧
    balance (A*W (p j^e j)) (T*scale (p j) (e j)) (d*Y (p j) (some (e j)))
      (p ∘ j.succAbove) (e ∘ j.succAbove) := by
  constructor
  · refine ⟨fun i=>ok.prime _,fun i=>ok.odd _,fun i=>ok.positive _,ok.distinct.comp j.succAbove_right_injective,?_,?_⟩
    · intro i dv
      let l:=j.succAbove i
      change p l∣2*(T*scale (p j) (e j)) at dv
      rw [←mul_assoc] at dv
      rcases (ok.prime l).dvd_mul.mp dv with a|a
      · exact ok.avoid l a
      rcases (ok.prime l).dvd_mul.mp a with b|b
      · exact ok.cross l j (Fin.succAbove_ne _ _) b
      exact Fin.succAbove_ne j i (ok.distinct ((prime_dvd_prime_iff_eq (ok.prime l) (ok.prime j)).mp
        ((ok.prime l).dvd_of_dvd_pow b)))
    · intro i k neq
      exact ok.cross _ _ (fun same=>neq (j.succAbove_right_injective same))
  · have hscale : 0<scale (p j) (e j) := by unfold scale;have:= (ok.prime j).pos;positivity
    have fx:=x_factor (ok.prime j) (e j)
    have val : ((A*W (p j^e j):ℕ):ℚ)/(T*scale (p j) (e j):ℕ)=((A:ℚ)/T)*X (p j) (some (e j)) := by
      push_cast
      field_simp [show (scale (p j) (e j):ℚ)≠0 by exact_mod_cast hscale.ne',
        show (T:ℚ)≠0 by exact_mod_cast tp.ne']
      unfold scale
      push_cast
      linear_combination -(A:ℚ)*fx
    unfold balance at eqn ⊢
    rw [Fin.prod_univ_succAbove (fun i=>X (p i) (some (e i))) j,
      Fin.prod_univ_succAbove (fun i=>Y (p i) (some (e i))) j] at eqn
    simpa only [val,Function.comp_apply,mul_assoc] using eqn

theorem bounded (K : ℕ) : ∀ (A T : ℕ) (d : ℚ), 0<T → 0<d → d≤1 →
    ∃ B : ℕ,∀ p e : Fin K→ℕ, Admissible T p e → balance A T d p e → total p e≤B := by
  classical
  induction K with
  | zero =>
    intro A T d _ _ _
    exact ⟨1,fun p e _ _=>by simp [total]⟩
  | succ K ih =>
    intro A T d tp dp ds
    by_cases cut : A<2*T
    · obtain ⟨L,cap⟩:=atom (K:=K+1) (Nat.succ_pos _) tp cut dp ds
      let bound (r z : ℕ) : ℕ := if good : r.Prime then
        Classical.choose (ih (A*W (r^z)) (T*scale r z) (d*Y r (some z))
          (by unfold scale;have:=good.pos;positivity) (mul_pos dp (OMA.FixedExponents245212.y_pos good z))
          ((mul_le_of_le_one_right dp.le (y_one good.one_lt _)).trans ds)) else 0
      let maxRest:=((range (L+1)).product (range (L+1))).sup (fun k=>bound k.1 k.2)
      refine ⟨(L+1)^L*maxRest,?_⟩
      intro p e ok eqn
      obtain ⟨j,pj,ej⟩:=cap p e ok eqn
      have rest:=peel j tp ok eqn
      have rule : total (p ∘ j.succAbove) (e ∘ j.succAbove)≤bound (p j) (e j) := by
        unfold bound
        rw [dif_pos (ok.prime j)]
        exact Classical.choose_spec (ih (A*W (p j^e j)) (T*scale (p j) (e j)) (d*Y (p j) (some (e j)))
          (by unfold scale;have:=(ok.prime j).pos;positivity)
          (mul_pos dp (OMA.FixedExponents245212.y_pos (ok.prime j) _))
          ((mul_le_of_le_one_right dp.le (y_one (ok.prime j).one_lt _)).trans ds))
          _ _ rest.1 rest.2
      have member : (p j,e j)∈(range (L+1)).product (range (L+1)) :=
        mem_product.mpr ⟨mem_range.mpr (by omega),mem_range.mpr (by omega)⟩
      have hi : bound (p j) (e j) ≤ maxRest := le_sup (f:=fun k : ℕ×ℕ=>bound k.1 k.2) member
      have pw : p j^e j≤(L+1)^L := (Nat.pow_le_pow_left (pj.trans (Nat.le_succ L)) _).trans
        (Nat.pow_le_pow_right (Nat.succ_pos _) ej)
      rw [total,Fin.prod_univ_succAbove _ j]
      exact Nat.mul_le_mul pw (rule.trans hi)
    · exact ⟨0,fun p e ok eqn=>False.elim (cut (below tp dp ok eqn))⟩

#print axioms bounded
end OMA.CofactorCrossCount245212

end

section

/- Finite original A245212 solutions of bounded odd-prime rank
when no odd prime divides another exponent length or the divisor count
of the fixed cofactor. -/
namespace OMA.CofactorCrossOriginal245212
open Nat Finset ArithmeticFunction OMA.Smooth245212 OMA.CofactorCrossCount245212
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

theorem original (h K : ℕ) (hh : 0<h) :
    ∃ B : ℕ,∀ p e : Fin K→ℕ, (∀i,(p i).Prime) → (∀i,Odd (p i)) → (∀i,h.Coprime (p i)) →
      Function.Injective p → (∀i,0<e i) → (∀i,¬p i∣σ 0 h) → (∀i j,i≠j → ¬p i∣e j+1) →
      OeisA245212.a (h*total p e)=(σ 1 (h*total p e):ℤ) → h*total p e≤B := by
  let T:=h*σ 0 h
  have tp : 0<T:=mul_pos hh (sigma_pos 0 h hh.ne')
  have dp : (0:ℚ)<(σ 1 h:ℚ)/T := div_pos (by exact_mod_cast sigma_pos 1 h hh.ne') (by exact_mod_cast tp)
  have ds : (σ 1 h:ℚ)/T≤1 := (div_le_one (by exact_mod_cast tp)).mpr (by exact_mod_cast sigma_bound hh)
  obtain ⟨L,cap⟩:=bounded K (W h) T _ tp dp ds
  refine ⟨h*L,?_⟩
  intro p e pr odd cop inj ep avoid cross eqn
  apply Nat.mul_le_mul_left h
  apply cap p e ⟨pr,odd,ep,inj,?_,cross⟩ (normalized_extension hh pr inj cop eqn)
  intro i dv
  rcases (pr i).dvd_mul.mp dv with two|rhs
  · have same:=(prime_dvd_prime_iff_eq (pr i) prime_two).mp two
    obtain ⟨k,hk⟩:=odd i
    omega
  rcases (pr i).dvd_mul.mp rhs with divides|divides
  · exact ((pr i).coprime_iff_not_dvd.mp (cop i).symm) divides
  · exact avoid i divides

#print axioms original
end OMA.CofactorCrossOriginal245212

end

section

/- An explicit whole-prime-power bound in the nonresonant case.
Replace large bases by 1 and small bases with large exponents by their
Euler limits. The explicitly separated subproduct cannot approximate a
solution this closely. -/
namespace OMA.CofactorEffectiveAtom245212
open Finset Nat OMA.Smooth245212 OMA.CofactorEulerSeparation245212

private theorem product_error {ι : Type*} [DecidableEq ι] (s : Finset ι) (x z : ι→ℚ)
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

private theorem local_factor {p e : ℕ} (hp : p.Prime) :
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

private theorem near {p e M : ℕ} (hp : p.Prime) (avoid : p≤M+1 → M<e) :
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

def threshold (A S K : ℕ) := budget A K*(2*A*K*2^K+2*S)

theorem alternative (A S H : ℕ) (s : Finset ℕ) (e : ℕ→ℕ) (pr : ∀p∈s,p.Prime)
    (apart : miss A H s)
    (bal : (A:ℚ)*(∏p∈s,X p (some (e p)))+S*(∏p∈s,Y p (some (e p)))=H) :
    let M:=threshold A S s.card
    (∀p∈s,e p≤M) ∨ ∃p∈s,p≤M+1 ∧ e p≤M := by
  classical
  let K:=s.card
  let M:=threshold A S K
  change (∀p∈s,e p≤M) ∨ ∃p∈s,p≤M+1 ∧ e p≤M
  by_cases allSmall : ∀p∈s,e p≤M
  · exact Or.inl allSmall
  right
  by_contra no
  push Not at allSmall
  obtain ⟨j,hj,large⟩:=allSmall
  have avoid (p) (hp:p∈s) (low:p≤M+1) : M<e p := by
    by_contra! short
    exact no ⟨p,hp,low,short⟩
  let z (p : ℕ) : ℚ:=if p≤M+1 then factor p else 1
  let t:=s.filter (fun p=>p≤M+1)
  have sub : t⊆s:=filter_subset _ _
  have proxy : (∏p∈s,z p)=(num t:ℚ)/den t := by
    rw [show (∏p∈s,z p)=∏p∈t,factor p by simp [z,t,prod_filter]]
    unfold factor num den
    push_cast
    rw [prod_div_distrib]
  have sep:=rational_gap (A:=A) (H:=H) (K:=K) (s:=t) (card_le_card sub)
    (fun p hp=>(pr p (sub hp)).two_le) (fun u hu=>apart u (hu.trans sub))
  rw [←proxy] at sep
  have feat:=product_error s (fun p=>X p (some (e p))) z (w:=2/((M:ℚ)+1)) (by positivity)
    (fun p hp=>by
      have loc:=local_factor (e:=e p) (pr p hp)
      refine ⟨zero_le_one.trans loc.1,loc.2.1.trans loc.2.2.1,?_,?_,near (pr p hp) (avoid p hp)⟩
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
  change 1≤(budget A K:ℚ)*|(A:ℚ)*Z-H| at sep
  have tri:=abs_add_le ((A:ℚ)*(PX-Z)) ((S:ℚ)*PY)
  rw [show (A:ℚ)*(PX-Z)+S*PY=H-A*Z by linarith only [bal],abs_sub_comm (H:ℚ)] at tri
  simp only [abs_mul,abs_of_nonneg (Nat.cast_nonneg A : (0:ℚ)≤A),
    abs_of_nonneg (Nat.cast_nonneg S : (0:ℚ)≤S),abs_of_nonneg y0] at tri
  have distance : |(A:ℚ)*Z-H| * L≤2*A*K*2^K+2*S := by
    nlinarith only [mul_le_mul_of_nonneg_right tri lp.le,
      mul_le_mul_of_nonneg_left xl (Nat.cast_nonneg A : (0:ℚ)≤A),
      mul_le_mul_of_nonneg_left yl (Nat.cast_nonneg S : (0:ℚ)≤S)]
  have bad : L≤(budget A K:ℚ)*(2*A*K*2^K+2*S) := by
    nlinarith only [mul_le_mul_of_nonneg_right sep lp.le,
      mul_le_mul_of_nonneg_left distance (Nat.cast_nonneg (budget A K) : (0:ℚ)≤_)]
  change ((threshold A S K:ℕ):ℚ)+1≤_ at bad
  unfold threshold at bad
  push_cast at bad
  linarith

#print axioms alternative
end OMA.CofactorEffectiveAtom245212

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

private theorem from_mass {r H D m : ℕ} (lower : ∀ p∈m.primeFactors,r≤p)
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

#print axioms least_prime
#print axioms count_sensitive
end OMA.CofactorHarmonic245212

end

section

/- Explicit simultaneous base and exponent bounds for at least one
odd prime power of any solution with fixed dyadic exponent and rank. -/
namespace OMA.CofactorEffectiveOriginal245212
open Nat Finset ArithmeticFunction OMA.Smooth245212 OMA.CofactorEulerSeparation245212
open OMA.CofactorEffectiveAtom245212
open scoped ArithmeticFunction.sigma

def height (h r : ℕ) := threshold (W h) (σ 1 h) r
def primeHeight (h r : ℕ) :=
  let H:=2*(h*σ 0 h)
  max (height h r+1) (r*H*(σ 1 h+1)/(H-W h))

theorem original {h m : ℕ} (hh : 0<h) (hm : 1 < m) (cop : h.Coprime m)
    (apart : miss (W h) (2*(h*σ 0 h)) m.primeFactors)
    (eqn : OeisA245212.a (h*m)=(σ 1 (h*m):ℤ)) :
    ∃p∈m.primeFactors,p≤primeHeight h m.primeFactors.card ∧ m.factorization p≤height h m.primeFactors.card := by
  classical
  let t:=m.primeFactors
  let p : t→ℕ:=Subtype.val
  let e (i : t):=m.factorization (p i)
  have mn : m≠0:=by omega
  have pr (i:t) : (p i).Prime:=prime_of_mem_primeFactors i.property
  have localCop (i:t) : h.Coprime (p i):=cop.of_dvd_right (dvd_of_mem_primeFactors i.property)
  have repr : total p e=m := (Nat.prod_primeFactors_coe_pow_factorization mn).symm
  let D:=h*σ 0 h
  have d0 : 0<D:=mul_pos hh (sigma_pos 0 h hh.ne')
  have sc:=OMA.CofactorCrossOriginal245212.normalized_extension (p:=p) (e:=e) hh pr
    Subtype.val_injective localCop (repr ▸ eqn)
  have sx : (∏i,X (p i) (some (e i)))=∏x∈t,X x (some (m.factorization x)) :=
    t.prod_coe_sort (fun x=>X x (some (m.factorization x)))
  have sy : (∏i,Y (p i) (some (e i)))=∏x∈t,Y x (some (m.factorization x)) :=
    t.prod_coe_sort (fun x=>Y x (some (m.factorization x)))
  rw [sx,sy] at sc
  change ((W h:ℚ)/D)*_+((σ 1 h:ℚ)/D)*_=2 at sc
  field_simp [show (D:ℚ)≠0 by exact_mod_cast d0.ne'] at sc
  have mass : (W h:ℚ)*(∏x∈t,X x (some (m.factorization x)))+
      (σ 1 h:ℚ)*(∏x∈t,Y x (some (m.factorization x)))=((2*D:ℕ):ℚ) := by push_cast;linarith only [sc]
  rcases alternative (W h) (σ 1 h) (2*D) t m.factorization (fun _ hp=>prime_of_mem_primeFactors hp) apart mass with
    short|⟨q,hq,pq,eq⟩
  · have ne : t.Nonempty := by
      exact ⟨m.minFac,(Nat.mem_primeFactors_of_ne_zero mn).mpr ⟨Nat.minFac_prime (by omega),Nat.minFac_dvd _⟩⟩
    let q:=t.min' ne
    have mem : q∈t:=t.min'_mem ne
    have bound:=OMA.CofactorHarmonic245212.least_prime (r:=q) hh hm cop (fun r hr=>t.min'_le r hr) eqn
    have g:=(OMA.CofactorHarmonic245212.gap hh hm cop eqn).1
    have below : W h<2*D := by
      by_contra! no
      have bad:=Nat.mul_le_mul_right (σ 0 m) no
      change W h*σ 0 m+σ 1 h<2*D*σ 0 m at g
      omega
    have qp : q≤t.card*(2*D)*(σ 1 h+1)/(2*D-W h) := by
      apply (Nat.le_div_iff_mul_le (Nat.sub_pos_of_lt below)).mpr
      simpa only [D,mul_assoc] using bound
    exact ⟨q,mem,qp.trans (le_max_right _ _),short q mem⟩
  · exact ⟨q,hq,pq.trans (le_max_left _ _),eq⟩

theorem dyadic {k m : ℕ} (hm : 1 < m) (odd : Odd m)
    (eqn : OeisA245212.a (2^k*m)=(σ 1 (2^k*m):ℤ)) :
    ∃p∈m.primeFactors,p≤primeHeight (2^k) m.primeFactors.card ∧
      m.factorization p≤height (2^k) m.primeFactors.card := by
  apply original (by positivity) hm ((Nat.coprime_two_left.mpr odd).pow_left k) _ eqn
  apply miss_odd (OMA.DyadicPower245212.dyadic_odd k) (even_two_mul _)
  intro p mem
  exact Nat.coprime_two_left.mp ((Nat.coprime_two_left.mpr odd).of_dvd_right (dvd_of_mem_primeFactors mem))

#print axioms original
#print axioms dyadic
end OMA.CofactorEffectiveOriginal245212

end

section

/- A cofactor has at most one resonant Euler support, even without a rank
cutoff. The largest prime in the reduced numerator identifies the next factor. -/
namespace OMA.EulerSupportUnique245212
open Finset Nat ArithmeticFunction OMA.Smooth245212 OMA.CofactorEulerSeparation245212
open scoped ArithmeticFunction.sigma

private theorem forced {s t : Finset ℕ} {p : ℕ} (ps : ∀x∈s,x.Prime) (pt : ∀x∈t,x.Prime)
    (mem : p∈s) (hi : ∀x∈s,x≤p) (cross : num s*den t=num t*den s) : p∈t := by
  have pp:=ps p mem
  have dv : p∣num t*den s := cross ▸ dvd_mul_of_dvd_left (dvd_prod_of_mem (fun q=>q) mem) _
  rcases pp.dvd_mul.mp dv with a|b
  · obtain ⟨x,mx,px⟩:=(pp.prime.dvd_finsetProd_iff (fun q=>q)).mp a
    rwa [(prime_dvd_prime_iff_eq pp (pt x mx)).mp px]
  · obtain ⟨x,mx,px⟩:=(pp.prime.dvd_finsetProd_iff (fun q=>q-1)).mp b
    have :=(ps x mx).one_lt
    have :=Nat.le_of_dvd (by omega : 0<x-1) px
    have :=hi x mx
    omega

theorem unique_support (s t : Finset ℕ) (ps : ∀x∈s,x.Prime) (pt : ∀x∈t,x.Prime)
    (cross : num s*den t=num t*den s) : s=t := by
  induction s using Finset.strongInductionOn generalizing t with
  | _ s ih =>
    by_cases empty : s∪t=∅
    · have := Finset.union_eq_empty.mp empty
      exact this.1.trans this.2.symm
    have ne:=nonempty_iff_ne_empty.mpr empty
    let p:=(s∪t).max' ne
    have mp : p∈s∪t:=(s∪t).max'_mem ne
    have ls (x) (mx:x∈s) : x≤p := (s∪t).le_max' x (mem_union_left _ mx)
    have lt (x) (mx:x∈t) : x≤p := (s∪t).le_max' x (mem_union_right _ mx)
    have both : p∈s ∧ p∈t := by
      rcases mem_union.mp mp with a|b
      · exact ⟨a,forced ps pt a ls cross⟩
      · exact ⟨forced pt ps b lt cross.symm,b⟩
    have cut : num (s.erase p)*den (t.erase p)=num (t.erase p)*den (s.erase p) := by
      have ns : num s=p*num (s.erase p) := (mul_prod_erase s (fun q=>q) both.1).symm
      have nt : num t=p*num (t.erase p) := (mul_prod_erase t (fun q=>q) both.2).symm
      have ds : den s=(p-1)*den (s.erase p) := (mul_prod_erase s (fun q=>q-1) both.1).symm
      have dt : den t=(p-1)*den (t.erase p) := (mul_prod_erase t (fun q=>q-1) both.2).symm
      have pr:=(ps p both.1).one_lt
      apply Nat.eq_of_mul_eq_mul_left (show 0<p*(p-1) by exact mul_pos (by omega) (by omega))
      rw [ns,nt,ds,dt] at cross
      simpa only [mul_assoc,mul_left_comm,mul_comm] using cross
    have equal:=ih (s.erase p) (erase_ssubset both.1) (t.erase p)
      (fun _ mem=>ps _ (mem_of_mem_erase mem)) (fun _ mem=>pt _ (mem_of_mem_erase mem)) cut
    simpa only [insert_erase both.1,insert_erase both.2] using congrArg (insert p) equal

theorem only_one {A H : ℕ} (ap : 0<A) {s t : Finset ℕ} (ps : ∀x∈s,x.Prime) (pt : ∀x∈t,x.Prime)
    (hs : A*num s=H*den s) (ht : A*num t=H*den t) : s=t := by
  apply unique_support s t ps pt
  apply Nat.eq_of_mul_eq_mul_left ap
  rw [←mul_assoc,hs,←mul_assoc,ht]
  ring

theorem cofactor_divides {h : ℕ} {s : Finset ℕ} (cop : ∀p∈s,h.Coprime p)
    (hit : W h*num s=2*(h*σ 0 h)*den s) : h∣W h := by
  have cp : h.Coprime (num s) := coprime_prod_right_iff.mpr cop
  apply cp.dvd_of_dvd_mul_right
  rw [hit]
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) _

#print axioms unique_support
#print axioms cofactor_divides
end OMA.EulerSupportUnique245212

end

section

/- A number with exactly one distinct odd prime factor never divides its
own weighted divisor sum. Hence no such cofactor can have an Euler resonance. -/
namespace OMA.SinglePrefixEffective245212
open Nat ArithmeticFunction OMA.Smooth245212 OMA.WeightVal245212
open OMA.CofactorEffectiveOriginal245212 OMA.CofactorEulerSeparation245212
open scoped ArithmeticFunction.sigma
open OMA.RankThreeAnchor245212 (weight_unit)
open OMA.RankThreeAnchor245212 (dyadic_weight)

private theorem weight_pos {p a : ℕ} (pr : p.Prime) : 0<W (p^a) := by
  rw [w_pow pr]
  exact Finset.sum_pos' (fun _ _=>Nat.zero_le _) ⟨0,Finset.mem_range.mpr (by omega),by simp⟩

private theorem large_power {p k a : ℕ} (hp : 3≤p) (ap : 0<a) (size : 2^(k+1)≤a+2) :
    W (2^k)<p^a := by
  rw [OMA.RankThreeAnchor245212.dyadic_weight]
  cases k with
  | zero =>
    have one:=Nat.pow_le_pow_right (by omega : 0<p) (show 1≤a by omega)
    simp only [pow_one] at one
    omega
  | succ j =>
    cases j with
    | zero =>
      have a2 : 2≤a:=by norm_num at size;omega
      have pw:=(Nat.pow_le_pow_left hp 2).trans (Nat.pow_le_pow_right (by omega : 0<p) a2)
      norm_num at pw ⊢
      omega
    | succ t =>
      let k:=t+2
      have exp (s : ℕ) : 2*((s+2)+1)+2≤2^((s+2)+1) := by
        induction s with
        | zero=>decide
        | succ s ih=>
          calc
            2*(s+1+2+1)+2 ≤ 2*(2*(s+2+1)+2) := by omega
            _ ≤ 2*2^(s+2+1) := Nat.mul_le_mul_left _ ih
            _ = 2^(s+1+2+1) := by rw [show s+1+2+1=(s+2+1)+1 by omega,pow_succ 2 (s+2+1),mul_comm]
      have enough : 2*(k+1)≤a:=by have := exp t;change 2^(t+2+1)≤a+2 at size;dsimp [k];omega
      have power := (Nat.pow_le_pow_right (by decide : 0<2) enough).trans (Nat.pow_le_pow_left (by omega : 2≤p) a)
      apply lt_of_lt_of_le _ power
      change k*2^(k+1)+1<2^(2*(k+1))
      rw [show 2*(k+1)=(k+1)+(k+1) by omega,pow_add 2 (k+1) (k+1)]
      have inc : k+1<2^(k+1):=Nat.lt_two_pow_self
      have gap:=Nat.mul_le_mul_right (2^(k+1)) inc
      have nz:=Nat.two_pow_pos (k+1)
      nlinarith only [gap,nz,inc]

theorem not_divides {k p a : ℕ} (pr : p.Prime) (odd : Odd p) (ap : 0<a) :
    ¬2^k*p^a∣W (2^k*p^a) := by
  have pc:=(Nat.coprime_two_left.mpr odd).pow_left k
  intro hit
  rw [w_mult.map_mul_of_coprime (pc.pow_right a)] at hit
  have pd : p^a∣W (2^k) := ((OMA.RankThreeAnchor245212.weight_unit pr a).pow_left a).dvd_of_dvd_mul_right
    ((dvd_mul_left _ _).trans hit)
  have td : 2^k∣W (p^a) := ((Nat.coprime_two_left.mpr (OMA.DyadicPower245212.dyadic_odd k)).pow_left k).dvd_of_dvd_mul_left
    ((dvd_mul_right _ _).trans hit)
  have order : k≤val (W (p^a)) := (prime_two.pow_dvd_iff_le_factorization (weight_pos pr).ne').mp td
  have localOrder:=weight_local pr odd a
  have size (j : ℕ) (pos : 0<j) (v : k+1≤val j) : 2^(k+1)≤j :=
    Nat.le_of_dvd pos ((pow_dvd_pow 2 v).trans (Nat.ordProj_dvd j 2))
  have big : 2^(k+1)≤a+2 := by
    rcases Nat.even_or_odd (a+1) with ev|od
    · have v:=val_odd (show Odd (a+2) from ev.add_one)
      exact (size (a+1) (by omega) (by omega)).trans (by omega)
    · have v:=val_odd od
      exact size (a+2) (by omega) (by omega)
  have p3 : 3≤p:=by obtain ⟨u,hu⟩:=odd;have := pr.two_le;omega
  exact (large_power p3 ap big).not_ge (Nat.le_of_dvd (by rw [OMA.RankThreeAnchor245212.dyadic_weight];omega) pd)

/-- One whole remaining prime power is bounded even when the cofactor
already contains any prescribed power of a different odd prime. -/
theorem next_atom {k p a m : ℕ} (pr : p.Prime) (odd : Odd p) (ap : 0<a)
    (hm : 1 < m) (cop : (2^k*p^a).Coprime m)
    (eqn : OeisA245212.a (2^k*p^a*m)=(σ 1 (2^k*p^a*m):ℤ)) :
    ∃q∈m.primeFactors,q≤primeHeight (2^k*p^a) m.primeFactors.card ∧
      m.factorization q≤height (2^k*p^a) m.primeFactors.card := by
  apply original (Nat.mul_pos (Nat.two_pow_pos _) (pow_pos pr.pos _)) hm cop _ eqn
  intro t sub eq
  exact not_divides pr odd ap (OMA.EulerSupportUnique245212.cofactor_divides
    (fun q mq=>cop.of_dvd_right (dvd_of_mem_primeFactors (sub mq))) eq)

#print axioms not_divides
#print axioms next_atom
end OMA.SinglePrefixEffective245212

end

section

/- A computable bound on an entire cross-divisibility-free solution, by
absorbing a bounded whole prime power at each successive cofactor. -/
namespace OMA.CofactorEffectiveTree245212
open Nat Finset ArithmeticFunction OMA.Smooth245212
open OMA.CofactorEffectiveOriginal245212 OMA.CofactorEulerSeparation245212
open scoped ArithmeticFunction.sigma

/-- Every branch removes one distinct prime. The enlarged finite boxes
include nonprime bases; these are harmless upper bounds. -/
def ceiling : ℕ → ℕ → ℕ
  | 0,h => h
  | k+1,h => ((range (primeHeight h (k+1)+1)).product (range (height h (k+1)+1))).sup
      (fun t => ceiling k (h*t.1^t.2))

theorem support_rest (m p : ℕ) : (ordCompl[p] m).primeFactors=m.primeFactors.erase p := by
  rw [←Nat.support_factorization, Nat.factorization_ordCompl, Finsupp.support_erase,
    Nat.support_factorization]

/-- A single recursion works for any condition preserved when removing a
whole prime power, provided that condition rules out a resonant subproduct. -/
theorem bounded_by (Good : ℕ→ℕ→Prop)
    (apart : ∀ {h m : ℕ}, 0 < h → h.Coprime m → Odd m → W h<2*(h*σ 0 h) →
      Good h m → miss (W h) (2*(h*σ 0 h)) m.primeFactors)
    (peel : ∀ {h m p : ℕ}, 0 < h → 0 < m → h.Coprime m → Odd m → p∈m.primeFactors →
      Good h m → Good (h*ordProj[p] m) (ordCompl[p] m))
    (r : ℕ) {h m : ℕ} (hh : 0 < h) (hm : 0 < m) (cop : h.Coprime m)
    (odd : Odd m) (rank : m.primeFactors.card=r)
    (good : Good h m)
    (eqn : OeisA245212.a (h*m)=(σ 1 (h*m):ℤ)) : h*m≤ceiling r h := by
  induction r generalizing h m with
  | zero =>
    have emp:=Nat.primeFactors_eq_empty.mp (card_eq_zero.mp rank)
    have one : m=1:=by omega
    simp [one,ceiling]
  | succ k ih =>
    have bigger : 1 < m := by
      by_contra! small
      have one : m=1:=by omega
      simp [one] at rank
    have g:=(OMA.CofactorHarmonic245212.gap hh bigger cop eqn).1
    have below : W h<2*(h*σ 0 h) := by
      by_contra! no
      have b:=Nat.mul_le_mul_right (σ 0 m) no
      omega
    obtain ⟨p,mem,pbound,ebound⟩:=original hh bigger cop (apart hh cop odd below good) eqn
    rw [rank] at pbound ebound
    let e:=m.factorization p
    let t:=ordCompl[p] m
    have pp:=prime_of_mem_primeFactors mem
    have tp : 0<t := Nat.ordCompl_pos p hm.ne'
    have repr : p^e*t=m := Nat.ordProj_mul_ordCompl_eq_self m p
    have td : t∣m:=Nat.ordCompl_dvd m p
    have nextCop : (h*p^e).Coprime t :=
      (cop.of_dvd_right td).mul_left ((Nat.coprime_ordCompl pp hm.ne').pow_left e)
    have id : h*p^e*t=h*m := by rw [mul_assoc,repr]
    have result : h*p^e*t≤ceiling k (h*p^e) := by
      apply ih (Nat.mul_pos hh (pow_pos pp.pos e)) tp nextCop
        (Nat.coprime_two_left.mp ((Nat.coprime_two_left.mpr odd).of_dvd_right td))
      · rw [show t.primeFactors=m.primeFactors.erase p from support_rest m p,card_erase_of_mem mem,rank]; omega
      · exact peel hh hm cop odd mem good
      · rwa [id]
    have box : (p,e)∈(range (primeHeight h (k+1)+1)).product (range (height h (k+1)+1)) :=
      mem_product.mpr ⟨mem_range.mpr (by omega),mem_range.mpr (Nat.lt_succ_of_le ebound)⟩
    rw [←id]
    exact result.trans (le_sup (f:=fun t : ℕ×ℕ=>ceiling k (h*t.1^t.2)) box)

private def no_edges (h m : ℕ) : Prop :=
  (∀q∈m.primeFactors, ¬q∣σ 0 h) ∧
  (∀p∈m.primeFactors,∀q∈m.primeFactors,p≠q → ¬p∣m.factorization q+1)

theorem bounded {h m : ℕ} (hh : 0 < h) (hm : 0 < m) (cop : h.Coprime m) (odd : Odd m)
    (avoid : ∀q∈m.primeFactors, ¬q∣σ 0 h)
    (cross : ∀p∈m.primeFactors,∀q∈m.primeFactors,p≠q → ¬p∣m.factorization q+1)
    (eqn : OeisA245212.a (h*m)=(σ 1 (h*m):ℤ)) : h*m≤ceiling m.primeFactors.card h := by
  apply bounded_by no_edges _ _ _ hh hm cop odd rfl ⟨avoid,cross⟩ eqn
  · intro h m _ cop odd below good
    apply miss_avoids below.ne (fun _ mem=>prime_of_mem_primeFactors mem)
    intro q mem dvd
    have pr:=prime_of_mem_primeFactors mem
    have qd:=dvd_of_mem_primeFactors mem
    have oq:=Nat.coprime_two_left.mp ((Nat.coprime_two_left.mpr odd).of_dvd_right qd)
    rcases pr.dvd_mul.mp dvd with two|other
    · have same:=(prime_dvd_prime_iff_eq pr prime_two).mp two
      obtain ⟨j,hj⟩:=oq
      omega
    rcases pr.dvd_mul.mp other with dh|dt
    · exact (pr.coprime_iff_not_dvd.mp (cop.of_dvd_right qd).symm) dh
    · exact good.1 q mem dt
  · intro h m p _ _ cop _ mem good
    have pp:=prime_of_mem_primeFactors mem
    have hcop:=cop.of_dvd_right (dvd_of_mem_primeFactors mem)
    obtain ⟨av,cr⟩:=good
    unfold no_edges
    rw [support_rest,isMultiplicative_sigma.map_mul_of_coprime (hcop.pow_right _),sigma_zero_apply_prime_pow pp]
    constructor
    · intro q mq dv
      obtain ⟨neq,old⟩:=mem_erase.mp mq
      exact ((prime_of_mem_primeFactors old).dvd_mul.mp dv).elim (av q old) (cr q old p mem neq)
    · intro a ma b mb ne
      rw [Nat.factorization_ordCompl,Finsupp.erase_ne (ne_of_mem_erase mb)]
      exact cr a (mem_of_mem_erase ma) b (mem_of_mem_erase mb) ne

#print axioms bounded_by
#print axioms bounded
end OMA.CofactorEffectiveTree245212

end

section

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

end

section

/- A certificate for a box of four integer coordinates: three exponents
and the last prime. A singleton interval containing a composite is empty. -/
namespace OMA.Moving245212
open Finset OMA.Smooth245212

def single (p : ℕ) : Band := ⟨p,some p⟩
def primes (e : I → ℕ) : Fin 3 → ℕ := ![2,3,e 3]
def base (b : Box) : Fin 3 → Band := ![single 2,single 3,b 3]
def value (e : I → ℕ) : ℚ :=
  (∏ i:Fin 3, X (primes e i) (some (e i.castSucc)))+
    ∏ i:Fin 3, Y (primes e i) (some (e i.castSucc))
def lower (b : Box) : ℚ := (∏ i:Fin 3, xl (base b i) (b i.castSucc))+
    ∏ i:Fin 3, yl (base b i) (b i.castSucc)
def upper (b : Box) : ℚ := (∏ i:Fin 3, xu (base b i) (b i.castSucc))+
    ∏ i:Fin 3, yu (base b i) (b i.castSucc)

theorem enclose {b : Box} {e : I → ℕ} (hq : 1<(b 3).lo)
    (h : ∀ i, (b i).Contains (e i)) : lower b ≤ value e ∧ value e ≤ upper b := by
  have low (i : Fin 3) : 1<(base b i).lo := by
    fin_cases i <;> simp [base,single,hq]
  have hits (i : Fin 3) : (base b i).Contains (primes e i) := by
    fin_cases i <;> simp [base,primes,single,Band.Contains]
    exact h 3
  have v (i : Fin 3) := factor_bounds (low i) (hits i) (h i.castSucc)
  constructor
  · exact add_le_add
      (prod_le_prod (fun i _ => (v i).1) (fun i _ => (v i).2.1))
      (prod_le_prod (fun i _ => (v i).2.2.2.1) (fun i _ => (v i).2.2.2.2.1))
  · exact add_le_add
      (prod_le_prod (fun i _ => (v i).1.trans (v i).2.1) (fun i _ => (v i).2.2.1))
      (prod_le_prod (fun i _ => (v i).2.2.2.1.trans (v i).2.2.2.2.1)
        (fun i _ => (v i).2.2.2.2.2))

def check : Tree → Box → Bool
| .leaf,b => decide (((b 3).hi = some (b 3).lo ∧ ¬Nat.Prime (b 3).lo) ∨
    1<(b 3).lo ∧ (2<lower b ∨ upper b<2))
| .split i cut l r,b => check l (left b i cut) && check r (right b i cut)

theorem reject (t : Tree) {b : Box} (cert : check t b=true)
    {e : I → ℕ} (h : ∀ i,(b i).Contains (e i)) (prime : Nat.Prime (e 3)) : value e≠2 := by
  induction t generalizing b with
  | leaf =>
    rcases of_decide_eq_true cert with ⟨same,comp⟩|⟨good,larger|smaller⟩
    · exact (comp ((Nat.le_antisymm (h 3).1 ((h 3).2 _ same)).symm ▸ prime)).elim
    · exact (larger.trans_le (enclose good h).1).ne'
    · exact ((enclose good h).2.trans_lt smaller).ne
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

def Excluded (b : Box) : Prop := ∀ e : I → ℕ, (∀ i,(b i).Contains (e i)) →
  Nat.Prime (e 3) → value e ≠ 2

theorem bisect (b : Box) (i : I) (cut : ℕ)
    (hl : Excluded (left b i cut)) (hr : Excluded (right b i cut)) : Excluded b := by
  intro e h
  by_cases ec : e i≤cut
  · apply hl
    intro j; by_cases ji : j=i
    · subst j; simpa [left,Band.Contains] using And.intro (h i).1 ec
    · simpa [left,ji] using h j
  · apply hr
    intro j; by_cases ji : j=i
    · subst j; simpa [right,Band.Contains] using And.intro (by omega : cut+1≤e i) (h i).2
    · simpa [right,ji] using h j

end OMA.Moving245212

end

section

/- Certificate of a uniform gap from 2 on the infinite-exponent faces of
the three possible prime prefixes with an unbounded fourth odd prime. -/
namespace OMA.OddFaces245212
open Finset OMA.Smooth245212 OMA.Moving245212

def bases (q : ℕ) : Fin 3 → ℕ := ![3,5,q]
def limitX (p : ℕ) : ℚ := X p none
def face (q : ℕ) (k : Fin 3) (e : I → ℕ) : ℚ :=
  ∏ i : Fin 3, if i=k then limitX (bases q i) else X (bases q i) (some (e i.castSucc))
def lower (q : ℕ) (k : Fin 3) (b : Box) : ℚ :=
  ∏ i : Fin 3, if i=k then limitX (bases q i) else xl (single (bases q i)) (b i.castSucc)
def upper (q : ℕ) (k : Fin 3) (b : Box) : ℚ :=
  ∏ i : Fin 3, if i=k then limitX (bases q i) else xu (single (bases q i)) (b i.castSucc)
def gap : ℚ := 1/100000000
def Separated (x : ℚ) := x<2-gap ∨ 2+gap<x

private theorem enc {q : ℕ} (hq : 1<q) (k : Fin 3) {e : I → ℕ}
    {b : Box} (h : ∀ i,(b i).Contains (e i)) :
    lower q k b ≤ face q k e ∧ face q k e ≤ upper q k b := by
  have hp (i : Fin 3) : 1<bases q i := by fin_cases i <;> simp [bases,hq]
  have v (i : Fin 3) := factor_bounds (pb:=single (bases q i)) (eb:=b i.castSucc)
    (hp i) (p:=bases q i) (by simp [single,Band.Contains]) (h _)
  let L (i : Fin 3) := if i=k then limitX (bases q i) else xl (single (bases q i)) (b i.castSucc)
  let U (i : Fin 3) := if i=k then limitX (bases q i) else xu (single (bases q i)) (b i.castSucc)
  let F (i : Fin 3) := if i=k then limitX (bases q i) else X (bases q i) (some (e i.castSucc))
  have per (i : Fin 3) : 0≤L i ∧ L i≤F i ∧ F i≤U i := by
    by_cases hi : i=k
    · simp only [L,U,F,hi,if_true,le_refl,and_self,and_true]
      exact x_nonneg (hp k) none
    · simp only [L,U,F,hi,if_false]
      exact ⟨(v i).1,(v i).2.1,(v i).2.2.1⟩
  exact ⟨prod_le_prod (f:=L) (g:=F) (fun i _ => (per i).1) (fun i _ => (per i).2.1),
    prod_le_prod (f:=F) (g:=U) (fun i _ => (per i).1.trans (per i).2.1)
      (fun i _ => (per i).2.2)⟩

def check (q : ℕ) (k : Fin 3) : Tree → Box → Bool
| .leaf,b => decide (upper q k b<2-gap ∨ 2+gap<lower q k b)
| .split i cut l r,b => check q k l (left b i cut) && check q k r (right b i cut)

theorem sound {q : ℕ} (hq : 1<q) (k : Fin 3) (t : Tree)
    {b : Box} (cert : check q k t b=true) {e : I → ℕ} (h : ∀ i,(b i).Contains (e i)) :
    Separated (face q k e) := by
  induction t generalizing b with
  | leaf =>
    obtain up|low := of_decide_eq_true cert
    · exact Or.inl ((enc hq k h).2.trans_lt up)
    · exact Or.inr (low.trans_le (enc hq k h).1)
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

def Good (q : ℕ) (k : Fin 3) (b : Box) := ∀ e : I → ℕ,
  (∀ i,(b i).Contains (e i)) → Separated (face q k e)

theorem bisect {q : ℕ} {k : Fin 3} (b : Box) (i : I) (c : ℕ)
    (hl : Good q k (left b i c)) (hr : Good q k (right b i c)) : Good q k b := by
  intro e h
  by_cases ec : e i≤c
  · apply hl
    intro j
    by_cases ji : j=i
    · subst j; simpa [left,Band.Contains] using And.intro (h i).1 ec
    · simpa [left,ji] using h j
  · apply hr
    intro j
    by_cases ji : j=i
    · subst j; simpa [right,Band.Contains] using And.intro (by omega : c+1≤e i) (h i).2
    · simpa [right,ji] using h j

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

/- Generated by mixed_three_245212.py 3 --lean. -/
namespace OMA.Moving245212
open OMA.Smooth245212
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def domain : Box := ![⟨1,none⟩,⟨1,none⟩,⟨1,none⟩,⟨4,none⟩]
private def bl : Box := left domain 0 3
private def bll : Box := left bl 1 3
private def blll : Box := left bll 3 9
private def bllll : Box := left blll 2 3
private def tllll : Tree := (.split 0 1 (.split 1 1 (.split 2 1 .leaf (.split 3 5 (.split 2 2 .leaf .leaf) .leaf)) (.split 2 1 (.split 3 5 (.split 1 2 (.split 3 4 .leaf .leaf) (.split 3 4 .leaf .leaf)) (.split 1 2 .leaf .leaf)) (.split 3 5 (.split 1 2 (.split 2 2 (.split 3 4 .leaf .leaf) (.split 3 4 .leaf .leaf)) (.split 3 4 .leaf (.split 2 2 .leaf .leaf))) (.split 1 2 .leaf .leaf)))) (.split 1 1 (.split 2 1 (.split 0 2 (.split 3 5 .leaf (.split 3 7 (.split 3 6 .leaf .leaf) .leaf)) .leaf) (.split 3 5 (.split 0 2 .leaf .leaf) (.split 0 2 (.split 3 7 (.split 2 2 (.split 3 6 .leaf .leaf) (.split 3 6 .leaf .leaf)) .leaf) .leaf))) (.split 3 5 .leaf (.split 0 2 (.split 2 1 (.split 1 2 .leaf .leaf) (.split 1 2 (.split 3 7 .leaf .leaf) .leaf)) .leaf))))
private theorem cllll : Excluded bllll := fun _ h => reject tllll (by decide +kernel) h
private def blllr : Box := right blll 2 3
private def tlllr : Tree := (.split 0 1 (.split 3 5 (.split 1 1 (.split 2 9 (.split 2 5 .leaf .leaf) (.split 3 4 .leaf .leaf)) (.split 2 9 (.split 2 5 (.split 1 2 (.split 3 4 .leaf .leaf) .leaf) (.split 3 4 .leaf (.split 1 2 .leaf .leaf))) (.split 3 4 .leaf (.split 1 2 (.split 2 21 .leaf .leaf) .leaf)))) (.split 1 1 .leaf (.split 2 9 (.split 3 7 (.split 1 2 .leaf (.split 2 5 .leaf .leaf)) .leaf) (.split 3 7 (.split 1 2 .leaf (.split 2 21 .leaf .leaf)) .leaf)))) (.split 3 5 (.split 1 1 (.split 2 9 (.split 0 2 .leaf .leaf) .leaf) .leaf) (.split 1 1 (.split 2 9 (.split 0 2 (.split 3 7 (.split 2 5 (.split 3 6 .leaf .leaf) (.split 3 6 .leaf .leaf)) .leaf) (.split 3 7 .leaf (.split 2 5 .leaf .leaf))) (.split 0 2 (.split 3 7 (.split 2 21 (.split 3 6 .leaf .leaf) (.split 3 6 .leaf .leaf)) .leaf) (.split 3 7 .leaf (.split 2 21 .leaf (.split 3 8 .leaf .leaf))))) (.split 0 2 (.split 2 9 (.split 3 7 .leaf (.split 1 2 (.split 2 5 .leaf .leaf) .leaf)) (.split 3 7 .leaf (.split 1 2 (.split 2 21 (.split 3 8 .leaf .leaf) (.split 3 8 .leaf .leaf)) .leaf))) .leaf))))
private theorem clllr : Excluded blllr := fun _ h => reject tlllr (by decide +kernel) h
private theorem clll : Excluded blll := bisect blll 2 3 cllll clllr
private def bllr : Box := right bll 3 9
private def bllrl : Box := left bllr 0 1
private def tllrl : Tree := (.split 2 3 (.split 1 1 .leaf .leaf) .leaf)
private theorem cllrl : Excluded bllrl := fun _ h => reject tllrl (by decide +kernel) h
private def bllrr : Box := right bllr 0 1
private def bllrrl : Box := left bllrr 1 1
private def tllrrl : Tree := (.split 2 3 (.split 0 2 (.split 2 1 .leaf .leaf) (.split 3 21 (.split 2 1 (.split 3 13 .leaf (.split 3 16 .leaf (.split 3 18 .leaf .leaf))) (.split 3 13 (.split 2 2 (.split 3 11 .leaf (.split 3 12 .leaf .leaf)) (.split 3 11 .leaf .leaf)) .leaf)) (.split 2 1 .leaf .leaf))) (.split 3 21 (.split 0 2 .leaf (.split 2 9 (.split 3 13 (.split 2 5 (.split 3 11 (.split 2 4 (.split 3 10 .leaf .leaf) (.split 3 10 .leaf .leaf)) .leaf) (.split 3 11 (.split 2 7 (.split 3 10 .leaf .leaf) (.split 3 10 .leaf .leaf)) .leaf)) .leaf) (.split 3 13 (.split 2 21 (.split 3 11 (.split 2 13 (.split 3 10 .leaf .leaf) .leaf) .leaf) (.split 3 11 (.split 2 45 .leaf .leaf) .leaf)) .leaf))) .leaf))
private theorem cllrrl : Excluded bllrrl := fun _ h => reject tllrrl (by decide +kernel) h
private def bllrrr : Box := right bllrr 1 1
private def bllrrrl : Box := left bllrrr 2 3
private def tllrrrl : Tree := (.split 0 2 (.split 3 21 (.split 2 1 (.split 1 2 (.split 3 13 .leaf .leaf) .leaf) (.split 1 2 (.split 3 13 (.split 2 2 (.split 3 11 (.split 3 10 .leaf .leaf) .leaf) (.split 3 11 (.split 3 10 .leaf .leaf) .leaf)) .leaf) (.split 3 13 .leaf (.split 3 16 (.split 2 2 .leaf .leaf) (.split 2 2 (.split 3 18 .leaf (.split 3 19 .leaf (.split 3 20 .leaf .leaf))) (.split 3 18 .leaf .leaf)))))) (.split 1 2 .leaf (.split 2 1 (.split 3 45 (.split 3 29 .leaf (.split 3 36 (.split 3 32 .leaf (.split 3 34 .leaf (.split 3 35 .leaf .leaf))) .leaf)) .leaf) (.split 3 45 (.split 3 29 (.split 2 2 .leaf .leaf) .leaf) .leaf)))) (.split 3 21 .leaf (.split 1 2 (.split 2 1 .leaf (.split 3 45 .leaf (.split 3 93 (.split 2 2 .leaf .leaf) (.split 2 2 .leaf (.split 3 189 (.split 3 125 (.split 3 107 (.split 3 100 (.split 3 96 .leaf (.split 3 98 .leaf .leaf)) .leaf) .leaf) .leaf) .leaf))))) .leaf)))
private theorem cllrrrl : Excluded bllrrrl := fun _ h => reject tllrrrl (by decide +kernel) h
private def bllrrrr : Box := right bllrrr 2 3
private def bllrrrrl : Box := left bllrrrr 3 21
private def tllrrrrl : Tree := (.split 0 2 (.split 3 13 (.split 2 9 (.split 1 2 (.split 2 5 (.split 3 11 (.split 2 4 (.split 3 10 .leaf .leaf) .leaf) .leaf) (.split 3 11 (.split 2 7 .leaf .leaf) .leaf)) .leaf) (.split 1 2 (.split 3 11 (.split 2 21 (.split 2 13 .leaf .leaf) .leaf) .leaf) .leaf)) (.split 1 2 .leaf (.split 2 9 (.split 3 16 (.split 2 5 (.split 3 14 .leaf (.split 2 4 .leaf .leaf)) (.split 3 14 .leaf (.split 2 7 (.split 3 15 .leaf .leaf) (.split 3 15 .leaf .leaf)))) (.split 2 5 (.split 3 18 (.split 2 4 (.split 3 17 .leaf .leaf) .leaf) .leaf) .leaf)) (.split 3 16 (.split 2 21 (.split 3 14 .leaf (.split 2 13 (.split 3 15 .leaf .leaf) (.split 3 15 .leaf .leaf))) (.split 3 14 .leaf (.split 2 45 (.split 3 15 .leaf .leaf) (.split 3 15 .leaf .leaf)))) .leaf)))) .leaf)
private theorem cllrrrrl : Excluded bllrrrrl := fun _ h => reject tllrrrrl (by decide +kernel) h
private def bllrrrrr : Box := right bllrrrr 3 21
private def bllrrrrrl : Box := left bllrrrrr 0 2
private def tllrrrrrl : Tree := (.split 1 2 .leaf .leaf)
private theorem cllrrrrrl : Excluded bllrrrrrl := fun _ h => reject tllrrrrrl (by decide +kernel) h
private def bllrrrrrr : Box := right bllrrrrr 0 2
private def bllrrrrrrl : Box := left bllrrrrrr 1 2
private def bllrrrrrrll : Box := left bllrrrrrrl 3 45
private def bllrrrrrrlll : Box := left bllrrrrrrll 2 9
private def tllrrrrrrlll : Tree := (.split 3 29 .leaf (.split 2 5 .leaf (.split 3 36 (.split 2 7 .leaf .leaf) (.split 2 7 (.split 3 40 (.split 2 6 .leaf .leaf) (.split 2 6 (.split 3 42 .leaf (.split 3 43 .leaf .leaf)) .leaf)) (.split 3 40 (.split 3 38 (.split 2 8 .leaf .leaf) .leaf) .leaf)))))
private theorem cllrrrrrrlll : Excluded bllrrrrrrlll := fun _ h => reject tllrrrrrrlll (by decide +kernel) h
private def bllrrrrrrllr : Box := right bllrrrrrrll 2 9
private def tllrrrrrrllr : Tree := (.split 3 29 (.split 2 21 .leaf (.split 3 25 .leaf (.split 2 45 (.split 3 27 .leaf (.split 2 29 .leaf (.split 2 36 .leaf .leaf))) (.split 3 27 .leaf (.split 2 93 (.split 2 61 (.split 3 28 .leaf (.split 2 52 (.split 2 48 .leaf .leaf) (.split 2 56 (.split 2 54 .leaf (.split 2 55 .leaf .leaf)) .leaf))) (.split 3 28 .leaf (.split 2 74 .leaf .leaf))) (.split 2 189 (.split 3 28 .leaf .leaf) (.split 3 28 .leaf .leaf))))))) (.split 2 21 (.split 3 36 (.split 2 13 (.split 3 32 .leaf (.split 2 11 (.split 3 34 .leaf (.split 2 10 (.split 3 35 .leaf .leaf) .leaf)) (.split 3 34 (.split 3 33 .leaf .leaf) .leaf))) (.split 3 32 (.split 2 16 (.split 3 30 .leaf (.split 2 14 .leaf .leaf)) (.split 3 30 .leaf (.split 2 18 (.split 3 31 .leaf .leaf) (.split 3 31 (.split 2 19 .leaf (.split 2 20 .leaf .leaf)) .leaf)))) (.split 2 16 (.split 3 34 (.split 2 14 .leaf .leaf) .leaf) .leaf))) (.split 2 13 .leaf .leaf)) (.split 3 36 (.split 2 45 (.split 3 32 (.split 2 29 (.split 3 30 .leaf (.split 2 25 (.split 3 31 (.split 2 23 .leaf .leaf) .leaf) .leaf)) (.split 3 30 .leaf .leaf)) .leaf) .leaf) .leaf)))
private theorem cllrrrrrrllr : Excluded bllrrrrrrllr := fun _ h => reject tllrrrrrrllr (by decide +kernel) h
private theorem cllrrrrrrll : Excluded bllrrrrrrll := bisect bllrrrrrrll 2 9 cllrrrrrrlll cllrrrrrrllr
private def bllrrrrrrlr : Box := right bllrrrrrrl 3 45
private def tllrrrrrrlr : Tree := (.split 2 9 (.split 3 93 (.split 2 5 (.split 3 61 (.split 2 4 (.split 3 52 .leaf (.split 3 56 .leaf (.split 3 58 .leaf (.split 3 59 .leaf (.split 3 60 .leaf .leaf))))) (.split 3 52 (.split 3 48 .leaf .leaf) .leaf)) (.split 3 74 (.split 2 4 .leaf .leaf) .leaf)) .leaf) .leaf) .leaf)
private theorem cllrrrrrrlr : Excluded bllrrrrrrlr := fun _ h => reject tllrrrrrrlr (by decide +kernel) h
private theorem cllrrrrrrl : Excluded bllrrrrrrl := bisect bllrrrrrrl 3 45 cllrrrrrrll cllrrrrrrlr
private def bllrrrrrrr : Box := right bllrrrrrr 1 2
private def tllrrrrrrr : Tree := .leaf
private theorem cllrrrrrrr : Excluded bllrrrrrrr := fun _ h => reject tllrrrrrrr (by decide +kernel) h
private theorem cllrrrrrr : Excluded bllrrrrrr := bisect bllrrrrrr 1 2 cllrrrrrrl cllrrrrrrr
private theorem cllrrrrr : Excluded bllrrrrr := bisect bllrrrrr 0 2 cllrrrrrl cllrrrrrr
private theorem cllrrrr : Excluded bllrrrr := bisect bllrrrr 3 21 cllrrrrl cllrrrrr
private theorem cllrrr : Excluded bllrrr := bisect bllrrr 2 3 cllrrrl cllrrrr
private theorem cllrr : Excluded bllrr := bisect bllrr 1 1 cllrrl cllrrr
private theorem cllr : Excluded bllr := bisect bllr 0 1 cllrl cllrr
private theorem cll : Excluded bll := bisect bll 3 9 clll cllr
private def blr : Box := right bl 1 3
private def blrl : Box := left blr 3 9
private def blrll : Box := left blrl 0 1
private def blrlll : Box := left blrll 2 3
private def blrllll : Box := left blrlll 1 9
private def tlrllll : Tree := (.split 3 5 (.split 2 1 (.split 1 5 (.split 1 4 (.split 3 4 .leaf .leaf) (.split 3 4 .leaf .leaf)) (.split 1 7 (.split 3 4 .leaf (.split 1 6 .leaf .leaf)) .leaf)) (.split 1 5 (.split 3 4 .leaf (.split 2 2 .leaf .leaf)) .leaf)) (.split 1 5 (.split 2 1 (.split 1 4 .leaf .leaf) (.split 3 7 (.split 2 2 (.split 1 4 .leaf (.split 3 6 .leaf .leaf)) (.split 1 4 .leaf (.split 3 6 .leaf .leaf))) .leaf)) (.split 2 1 (.split 1 7 (.split 3 7 (.split 1 6 .leaf .leaf) .leaf) (.split 3 7 (.split 3 6 .leaf .leaf) .leaf)) (.split 3 7 (.split 1 7 (.split 2 2 (.split 3 6 .leaf .leaf) (.split 3 6 .leaf (.split 1 6 .leaf .leaf))) (.split 2 2 (.split 3 6 .leaf (.split 1 8 .leaf .leaf)) .leaf)) (.split 1 7 .leaf (.split 2 2 .leaf .leaf))))))
private theorem clrllll : Excluded blrllll := fun _ h => reject tlrllll (by decide +kernel) h
private def blrlllr : Box := right blrlll 1 9
private def blrlllrl : Box := left blrlllr 3 5
private def tlrlllrl : Tree := (.split 2 1 (.split 1 21 (.split 1 13 .leaf .leaf) .leaf) .leaf)
private theorem clrlllrl : Excluded blrlllrl := fun _ h => reject tlrlllrl (by decide +kernel) h
private def blrlllrr : Box := right blrlllr 3 5
private def tlrlllrr : Tree := (.split 1 21 (.split 2 1 (.split 1 13 (.split 3 7 (.split 1 11 (.split 3 6 .leaf .leaf) (.split 3 6 .leaf .leaf)) .leaf) (.split 3 7 (.split 1 16 (.split 3 6 .leaf .leaf) (.split 3 6 .leaf .leaf)) .leaf)) (.split 3 7 (.split 1 13 (.split 2 2 .leaf .leaf) .leaf) (.split 1 13 (.split 2 2 (.split 1 11 .leaf (.split 3 8 .leaf .leaf)) (.split 1 11 (.split 3 8 .leaf .leaf) (.split 3 8 .leaf .leaf))) (.split 2 2 (.split 1 16 (.split 3 8 .leaf .leaf) (.split 3 8 .leaf .leaf)) (.split 1 16 (.split 3 8 .leaf .leaf) .leaf))))) (.split 2 1 (.split 1 45 (.split 3 7 (.split 1 29 (.split 3 6 .leaf (.split 1 25 .leaf .leaf)) (.split 3 6 .leaf (.split 1 36 (.split 1 32 .leaf (.split 1 34 .leaf .leaf)) (.split 1 40 (.split 1 38 (.split 1 37 .leaf .leaf) (.split 1 39 .leaf .leaf)) (.split 1 42 (.split 1 41 .leaf .leaf) .leaf))))) .leaf) (.split 3 7 (.split 1 93 (.split 3 6 .leaf (.split 1 61 (.split 1 52 (.split 1 48 .leaf .leaf) .leaf) (.split 1 74 .leaf .leaf))) (.split 3 6 .leaf (.split 1 189 .leaf .leaf))) (.split 1 93 .leaf (.split 1 189 .leaf .leaf)))) (.split 3 7 .leaf (.split 1 45 (.split 1 29 (.split 2 2 (.split 3 8 .leaf .leaf) .leaf) (.split 2 2 (.split 3 8 .leaf .leaf) .leaf)) (.split 1 93 .leaf .leaf)))))
private theorem clrlllrr : Excluded blrlllrr := fun _ h => reject tlrlllrr (by decide +kernel) h
private theorem clrlllr : Excluded blrlllr := bisect blrlllr 3 5 clrlllrl clrlllrr
private theorem clrlll : Excluded blrlll := bisect blrlll 1 9 clrllll clrlllr
private def blrllr : Box := right blrll 2 3
private def blrllrl : Box := left blrllr 3 5
private def tlrllrl : Tree := (.split 1 9 (.split 2 9 .leaf .leaf) .leaf)
private theorem clrllrl : Excluded blrllrl := fun _ h => reject tlrllrl (by decide +kernel) h
private def blrllrr : Box := right blrllr 3 5
private def blrllrrl : Box := left blrllrr 1 9
private def tlrllrrl : Tree := (.split 2 9 (.split 1 5 (.split 3 7 (.split 2 5 (.split 3 6 .leaf (.split 1 4 .leaf .leaf)) (.split 3 6 .leaf (.split 1 4 .leaf (.split 2 7 .leaf .leaf)))) .leaf) (.split 3 7 (.split 2 5 (.split 1 7 (.split 3 6 .leaf (.split 1 6 (.split 2 4 .leaf .leaf) .leaf)) .leaf) (.split 1 7 (.split 3 6 .leaf (.split 2 7 .leaf .leaf)) .leaf)) (.split 1 7 (.split 2 5 .leaf (.split 3 8 .leaf .leaf)) (.split 2 5 (.split 3 8 .leaf .leaf) (.split 3 8 .leaf .leaf))))) (.split 3 7 (.split 1 5 (.split 2 21 (.split 3 6 .leaf (.split 1 4 .leaf (.split 2 13 (.split 2 11 .leaf .leaf) (.split 2 16 (.split 2 14 .leaf .leaf) (.split 2 18 (.split 2 17 .leaf .leaf) (.split 2 19 .leaf (.split 2 20 .leaf .leaf))))))) (.split 3 6 .leaf (.split 1 4 .leaf (.split 2 45 (.split 2 29 (.split 2 25 (.split 2 23 .leaf .leaf) .leaf) (.split 2 36 .leaf .leaf)) (.split 2 93 .leaf .leaf))))) (.split 3 6 .leaf .leaf)) (.split 1 5 .leaf (.split 1 7 (.split 2 21 (.split 3 8 .leaf .leaf) (.split 3 8 .leaf .leaf)) (.split 2 21 (.split 3 8 .leaf .leaf) (.split 3 8 .leaf .leaf))))))
private theorem clrllrrl : Excluded blrllrrl := fun _ h => reject tlrllrrl (by decide +kernel) h
private def blrllrrr : Box := right blrllrr 1 9
private def tlrllrrr : Tree := (.split 3 7 .leaf (.split 1 21 (.split 2 9 (.split 1 13 (.split 2 5 (.split 3 8 .leaf .leaf) (.split 3 8 .leaf .leaf)) (.split 2 5 (.split 1 16 (.split 3 8 .leaf .leaf) .leaf) .leaf)) (.split 1 13 (.split 2 21 (.split 3 8 .leaf .leaf) .leaf) .leaf)) .leaf))
private theorem clrllrrr : Excluded blrllrrr := fun _ h => reject tlrllrrr (by decide +kernel) h
private theorem clrllrr : Excluded blrllrr := bisect blrllrr 1 9 clrllrrl clrllrrr
private theorem clrllr : Excluded blrllr := bisect blrllr 3 5 clrllrl clrllrr
private theorem clrll : Excluded blrll := bisect blrll 2 3 clrlll clrllr
private def blrlr : Box := right blrl 0 1
private def tlrlr : Tree := .leaf
private theorem clrlr : Excluded blrlr := fun _ h => reject tlrlr (by decide +kernel) h
private theorem clrl : Excluded blrl := bisect blrl 0 1 clrll clrlr
private def blrr : Box := right blr 3 9
private def blrrl : Box := left blrr 0 1
private def blrrll : Box := left blrrl 1 9
private def tlrrll : Tree := (.split 2 3 (.split 1 5 .leaf (.split 3 21 (.split 2 1 .leaf .leaf) .leaf)) (.split 3 21 (.split 1 5 .leaf (.split 3 13 (.split 2 9 .leaf .leaf) .leaf)) .leaf))
private theorem clrrll : Excluded blrrll := fun _ h => reject tlrrll (by decide +kernel) h
private def blrrlr : Box := right blrrl 1 9
private def blrrlrl : Box := left blrrlr 3 21
private def blrrlrll : Box := left blrrlrl 2 3
private def tlrrlrll : Tree := (.split 1 21 (.split 2 1 .leaf (.split 3 13 (.split 1 13 .leaf (.split 3 11 (.split 1 16 .leaf (.split 2 2 .leaf .leaf)) .leaf)) .leaf)) (.split 3 13 (.split 1 45 (.split 2 1 .leaf (.split 3 11 (.split 1 29 (.split 2 2 .leaf (.split 3 10 .leaf .leaf)) (.split 2 2 .leaf (.split 3 10 .leaf .leaf))) .leaf)) (.split 2 1 .leaf (.split 3 11 (.split 1 93 (.split 2 2 (.split 1 61 .leaf (.split 3 10 .leaf .leaf)) (.split 3 10 .leaf (.split 1 61 (.split 1 52 .leaf (.split 1 56 .leaf (.split 1 58 .leaf .leaf))) (.split 1 74 (.split 1 67 (.split 1 64 (.split 1 62 .leaf (.split 1 63 .leaf .leaf)) .leaf) .leaf) .leaf)))) (.split 2 2 (.split 1 189 (.split 3 10 .leaf .leaf) (.split 3 10 .leaf .leaf)) (.split 3 10 .leaf .leaf))) (.split 1 93 .leaf (.split 2 2 .leaf (.split 1 189 .leaf (.split 3 12 .leaf .leaf))))))) (.split 1 45 .leaf .leaf)))
private theorem clrrlrll : Excluded blrrlrll := fun _ h => reject tlrrlrll (by decide +kernel) h
private def blrrlrlr : Box := right blrrlrl 2 3
private def blrrlrlrl : Box := left blrrlrlr 1 21
private def blrrlrlrll : Box := left blrrlrlrl 3 13
private def blrrlrlrlll : Box := left blrrlrlrll 2 9
private def tlrrlrlrlll : Tree := (.split 1 13 (.split 3 11 (.split 2 5 .leaf (.split 1 11 .leaf (.split 3 10 .leaf .leaf))) .leaf) (.split 3 11 (.split 2 5 (.split 1 16 (.split 3 10 .leaf .leaf) (.split 3 10 .leaf .leaf)) (.split 1 16 (.split 3 10 .leaf .leaf) (.split 3 10 .leaf (.split 1 18 .leaf (.split 2 7 .leaf (.split 1 19 .leaf (.split 2 8 .leaf (.split 1 20 .leaf .leaf)))))))) .leaf))
private theorem clrrlrlrlll : Excluded blrrlrlrlll := fun _ h => reject tlrrlrlrlll (by decide +kernel) h
private def blrrlrlrllr : Box := right blrrlrlrll 2 9
private def tlrrlrlrllr : Tree := (.split 1 13 (.split 3 11 (.split 2 21 (.split 1 11 .leaf (.split 3 10 .leaf .leaf)) (.split 1 11 (.split 3 10 .leaf .leaf) (.split 3 10 .leaf .leaf))) .leaf) (.split 3 11 (.split 2 21 (.split 1 16 (.split 3 10 .leaf (.split 2 13 .leaf .leaf)) (.split 3 10 .leaf (.split 2 13 (.split 1 18 (.split 2 11 .leaf .leaf) (.split 1 19 (.split 2 11 .leaf (.split 2 12 .leaf .leaf)) (.split 2 11 (.split 1 20 .leaf .leaf) .leaf))) (.split 1 18 (.split 2 16 (.split 1 17 .leaf (.split 2 14 .leaf (.split 2 15 .leaf .leaf))) (.split 1 17 .leaf .leaf)) .leaf)))) (.split 1 16 (.split 3 10 .leaf (.split 2 45 (.split 1 14 .leaf (.split 2 29 .leaf .leaf)) (.split 1 14 .leaf (.split 2 93 (.split 1 15 .leaf (.split 2 61 (.split 2 52 .leaf .leaf) (.split 2 74 (.split 2 67 (.split 2 64 .leaf .leaf) (.split 2 70 (.split 2 68 .leaf .leaf) .leaf)) (.split 2 83 .leaf .leaf)))) (.split 1 15 .leaf (.split 2 189 .leaf .leaf)))))) (.split 3 10 .leaf (.split 2 45 (.split 1 18 (.split 2 29 (.split 1 17 (.split 2 25 (.split 2 23 .leaf (.split 2 24 .leaf .leaf)) .leaf) .leaf) .leaf) .leaf) .leaf)))) (.split 1 16 .leaf (.split 2 21 .leaf (.split 3 12 .leaf .leaf)))))
private theorem clrrlrlrllr : Excluded blrrlrlrllr := fun _ h => reject tlrrlrlrllr (by decide +kernel) h
private theorem clrrlrlrll : Excluded blrrlrlrll := bisect blrrlrlrll 2 9 clrrlrlrlll clrrlrlrllr
private def blrrlrlrlr : Box := right blrrlrlrl 3 13
private def tlrrlrlrlr : Tree := .leaf
private theorem clrrlrlrlr : Excluded blrrlrlrlr := fun _ h => reject tlrrlrlrlr (by decide +kernel) h
private theorem clrrlrlrl : Excluded blrrlrlrl := bisect blrrlrlrl 3 13 clrrlrlrll clrrlrlrlr
private def blrrlrlrr : Box := right blrrlrlr 1 21
private def blrrlrlrrl : Box := left blrrlrlrr 3 13
private def blrrlrlrrll : Box := left blrrlrlrrl 2 9
private def blrrlrlrrlll : Box := left blrrlrlrrll 1 45
private def tlrrlrlrrlll : Tree := (.split 3 11 (.split 2 5 (.split 1 29 (.split 3 10 .leaf (.split 1 25 .leaf (.split 2 4 .leaf (.split 1 27 .leaf .leaf)))) (.split 3 10 .leaf (.split 1 36 (.split 2 4 (.split 1 32 .leaf (.split 1 34 .leaf (.split 1 35 .leaf .leaf))) .leaf) (.split 2 4 .leaf .leaf)))) (.split 1 29 (.split 3 10 .leaf (.split 1 25 (.split 2 7 (.split 1 23 (.split 2 6 .leaf (.split 1 22 .leaf .leaf)) (.split 2 6 (.split 1 24 .leaf .leaf) .leaf)) .leaf) (.split 2 7 .leaf .leaf))) .leaf)) (.split 1 29 (.split 2 5 .leaf (.split 3 12 .leaf .leaf)) (.split 2 5 (.split 1 36 .leaf .leaf) (.split 1 36 (.split 3 12 .leaf .leaf) (.split 3 12 .leaf .leaf)))))
private theorem clrrlrlrrlll : Excluded blrrlrlrrlll := fun _ h => reject tlrrlrlrrlll (by decide +kernel) h
private def blrrlrlrrllr : Box := right blrrlrlrrll 1 45
private def tlrrlrlrrllr : Tree := (.split 3 11 (.split 1 93 .leaf .leaf) (.split 1 93 (.split 2 5 (.split 1 61 (.split 3 12 .leaf .leaf) (.split 3 12 .leaf .leaf)) (.split 1 61 (.split 3 12 .leaf (.split 2 7 .leaf (.split 1 52 .leaf (.split 1 56 .leaf (.split 2 8 .leaf (.split 1 58 .leaf (.split 1 59 .leaf (.split 1 60 .leaf .leaf)))))))) (.split 3 12 .leaf (.split 2 7 (.split 1 74 .leaf (.split 2 6 .leaf (.split 1 83 (.split 1 78 .leaf (.split 1 80 .leaf .leaf)) (.split 1 88 (.split 1 85 .leaf .leaf) .leaf)))) (.split 1 74 (.split 1 67 (.split 2 8 .leaf .leaf) (.split 2 8 (.split 1 70 (.split 1 68 .leaf (.split 1 69 .leaf .leaf)) .leaf) .leaf)) .leaf))))) (.split 2 5 (.split 1 189 (.split 3 12 .leaf (.split 1 125 .leaf .leaf)) (.split 3 12 .leaf (.split 1 381 (.split 2 4 .leaf (.split 1 253 (.split 1 217 .leaf (.split 1 234 .leaf .leaf)) (.split 1 304 (.split 1 276 (.split 1 264 (.split 1 258 .leaf (.split 1 261 .leaf (.split 1 262 .leaf .leaf))) .leaf) .leaf) .leaf))) (.split 2 4 .leaf .leaf)))) (.split 3 12 .leaf (.split 1 189 (.split 2 7 (.split 1 125 (.split 2 6 (.split 1 107 .leaf (.split 1 115 (.split 1 111 .leaf .leaf) (.split 1 120 (.split 1 117 (.split 1 116 .leaf .leaf) .leaf) .leaf))) .leaf) (.split 2 6 .leaf .leaf)) .leaf) .leaf)))))
private theorem clrrlrlrrllr : Excluded blrrlrlrrllr := fun _ h => reject tlrrlrlrrllr (by decide +kernel) h
private theorem clrrlrlrrll : Excluded blrrlrlrrll := bisect blrrlrlrrll 1 45 clrrlrlrrlll clrrlrlrrllr
private def blrrlrlrrlr : Box := right blrrlrlrrl 2 9
private def blrrlrlrrlrl : Box := left blrrlrlrrlr 3 11
private def tlrrlrlrrlrl : Tree := (.split 1 45 (.split 2 21 .leaf .leaf) .leaf)
private theorem clrrlrlrrlrl : Excluded blrrlrlrrlrl := fun _ h => reject tlrrlrlrrlrl (by decide +kernel) h
private def blrrlrlrrlrr : Box := right blrrlrlrrlr 3 11
private def blrrlrlrrlrrl : Box := left blrrlrlrrlrr 1 45
private def blrrlrlrrlrrll : Box := left blrrlrlrrlrrl 1 29
private def tlrrlrlrrlrrll : Tree := (.split 2 21 (.split 3 12 .leaf .leaf) (.split 3 12 .leaf .leaf))
private theorem clrrlrlrrlrrll : Excluded blrrlrlrrlrrll := fun _ h => reject tlrrlrlrrlrrll (by decide +kernel) h
private def blrrlrlrrlrrlr : Box := right blrrlrlrrlrrl 1 29
private def blrrlrlrrlrrlrl : Box := left blrrlrlrrlrrlr 2 21
private def tlrrlrlrrlrrlrl : Tree := (.split 3 12 .leaf (.split 1 36 .leaf (.split 2 13 (.split 1 40 .leaf .leaf) (.split 1 40 (.split 2 16 .leaf (.split 1 38 .leaf (.split 2 18 .leaf (.split 2 19 .leaf (.split 1 39 .leaf (.split 2 20 .leaf .leaf)))))) (.split 2 16 (.split 1 42 .leaf (.split 2 14 .leaf (.split 1 43 (.split 2 15 .leaf .leaf) (.split 2 15 (.split 1 44 .leaf .leaf) .leaf)))) (.split 1 42 (.split 2 18 (.split 1 41 .leaf (.split 2 17 .leaf .leaf)) (.split 2 19 .leaf .leaf)) .leaf))))))
private theorem clrrlrlrrlrrlrl : Excluded blrrlrlrrlrrlrl := fun _ h => reject tlrrlrlrrlrrlrl (by decide +kernel) h
private def blrrlrlrrlrrlrr : Box := right blrrlrlrrlrrlr 2 21
private def blrrlrlrrlrrlrrl : Box := left blrrlrlrrlrrlrr 3 12
private def tlrrlrlrrlrrlrrl : Tree := .leaf
private theorem clrrlrlrrlrrlrrl : Excluded blrrlrlrrlrrlrrl := fun _ h => reject tlrrlrlrrlrrlrrl (by decide +kernel) h
private def blrrlrlrrlrrlrrr : Box := right blrrlrlrrlrrlrr 3 12
private def blrrlrlrrlrrlrrrl : Box := left blrrlrlrrlrrlrrr 1 36
private def tlrrlrlrrlrrlrrrl : Tree := (.split 2 45 (.split 1 32 .leaf (.split 2 29 .leaf (.split 1 34 .leaf (.split 2 36 (.split 2 32 .leaf (.split 1 35 .leaf (.split 2 34 .leaf .leaf))) (.split 2 40 (.split 1 35 .leaf .leaf) (.split 1 35 (.split 2 42 .leaf (.split 2 43 .leaf .leaf)) .leaf)))))) (.split 1 32 (.split 2 93 .leaf (.split 2 189 (.split 1 30 .leaf .leaf) (.split 1 30 .leaf (.split 2 381 (.split 1 31 .leaf (.split 2 253 (.split 2 217 .leaf .leaf) (.split 2 304 (.split 2 276 (.split 2 264 .leaf (.split 2 270 .leaf (.split 2 273 (.split 2 271 .leaf (.split 2 272 .leaf .leaf)) .leaf))) (.split 2 289 .leaf .leaf)) .leaf))) (.split 1 31 .leaf .leaf))))) (.split 2 93 (.split 1 34 (.split 2 61 (.split 2 52 .leaf (.split 1 33 .leaf (.split 2 56 .leaf (.split 2 58 (.split 2 57 .leaf .leaf) .leaf)))) (.split 2 74 (.split 1 33 .leaf .leaf) (.split 1 33 (.split 2 83 .leaf (.split 2 88 .leaf (.split 2 90 .leaf .leaf))) .leaf))) (.split 2 61 .leaf .leaf)) (.split 1 34 (.split 2 189 (.split 2 125 (.split 1 33 (.split 2 107 (.split 2 100 (.split 2 96 (.split 2 94 .leaf .leaf) .leaf) .leaf) .leaf) .leaf) .leaf) .leaf) .leaf))))
private theorem clrrlrlrrlrrlrrrl : Excluded blrrlrlrrlrrlrrrl := fun _ h => reject tlrrlrlrrlrrlrrrl (by decide +kernel) h
private def blrrlrlrrlrrlrrrr : Box := right blrrlrlrrlrrlrrr 1 36
private def tlrrlrlrrlrrlrrrr : Tree := (.split 2 45 (.split 1 40 (.split 2 29 (.split 1 38 (.split 2 25 (.split 2 23 .leaf (.split 1 37 .leaf (.split 2 24 .leaf .leaf))) (.split 2 27 (.split 1 37 .leaf .leaf) (.split 1 37 (.split 2 28 .leaf .leaf) .leaf))) (.split 2 25 (.split 2 23 (.split 1 39 (.split 2 22 .leaf .leaf) .leaf) .leaf) .leaf)) (.split 2 36 (.split 1 38 (.split 2 32 .leaf .leaf) .leaf) .leaf)) .leaf) .leaf)
private theorem clrrlrlrrlrrlrrrr : Excluded blrrlrlrrlrrlrrrr := fun _ h => reject tlrrlrlrrlrrlrrrr (by decide +kernel) h
private theorem clrrlrlrrlrrlrrr : Excluded blrrlrlrrlrrlrrr := bisect blrrlrlrrlrrlrrr 1 36 clrrlrlrrlrrlrrrl clrrlrlrrlrrlrrrr
private theorem clrrlrlrrlrrlrr : Excluded blrrlrlrrlrrlrr := bisect blrrlrlrrlrrlrr 3 12 clrrlrlrrlrrlrrl clrrlrlrrlrrlrrr
private theorem clrrlrlrrlrrlr : Excluded blrrlrlrrlrrlr := bisect blrrlrlrrlrrlr 2 21 clrrlrlrrlrrlrl clrrlrlrrlrrlrr
private theorem clrrlrlrrlrrl : Excluded blrrlrlrrlrrl := bisect blrrlrlrrlrrl 1 29 clrrlrlrrlrrll clrrlrlrrlrrlr
private def blrrlrlrrlrrr : Box := right blrrlrlrrlrr 1 45
private def tlrrlrlrrlrrr : Tree := (.split 1 93 (.split 2 21 (.split 3 12 .leaf (.split 1 61 (.split 2 13 (.split 1 52 (.split 2 11 (.split 1 48 .leaf (.split 2 10 .leaf (.split 1 50 .leaf (.split 1 51 .leaf .leaf)))) (.split 1 48 (.split 2 12 .leaf (.split 1 46 .leaf (.split 1 47 .leaf .leaf))) (.split 1 50 (.split 2 12 (.split 1 49 .leaf .leaf) .leaf) .leaf))) (.split 2 11 (.split 1 56 (.split 2 10 (.split 1 54 .leaf (.split 1 55 .leaf .leaf)) .leaf) .leaf) .leaf)) (.split 1 52 (.split 2 16 (.split 1 48 (.split 2 14 .leaf .leaf) .leaf) .leaf) .leaf)) .leaf)) .leaf) .leaf)
private theorem clrrlrlrrlrrr : Excluded blrrlrlrrlrrr := fun _ h => reject tlrrlrlrrlrrr (by decide +kernel) h
private theorem clrrlrlrrlrr : Excluded blrrlrlrrlrr := bisect blrrlrlrrlrr 1 45 clrrlrlrrlrrl clrrlrlrrlrrr
private theorem clrrlrlrrlr : Excluded blrrlrlrrlr := bisect blrrlrlrrlr 3 11 clrrlrlrrlrl clrrlrlrrlrr
private theorem clrrlrlrrl : Excluded blrrlrlrrl := bisect blrrlrlrrl 2 9 clrrlrlrrll clrrlrlrrlr
private def blrrlrlrrr : Box := right blrrlrlrr 3 13
private def tlrrlrlrrr : Tree := (.split 1 45 (.split 3 16 (.split 2 9 .leaf (.split 1 29 .leaf (.split 3 14 .leaf .leaf))) .leaf) (.split 3 16 (.split 2 9 (.split 1 93 .leaf (.split 3 14 .leaf .leaf)) (.split 1 93 (.split 3 14 .leaf (.split 2 21 .leaf .leaf)) (.split 3 14 .leaf (.split 2 21 (.split 1 189 .leaf (.split 3 15 .leaf .leaf)) (.split 1 189 (.split 3 15 .leaf .leaf) (.split 3 15 .leaf .leaf)))))) .leaf))
private theorem clrrlrlrrr : Excluded blrrlrlrrr := fun _ h => reject tlrrlrlrrr (by decide +kernel) h
private theorem clrrlrlrr : Excluded blrrlrlrr := bisect blrrlrlrr 3 13 clrrlrlrrl clrrlrlrrr
private theorem clrrlrlr : Excluded blrrlrlr := bisect blrrlrlr 1 21 clrrlrlrl clrrlrlrr
private theorem clrrlrl : Excluded blrrlrl := bisect blrrlrl 2 3 clrrlrll clrrlrlr
private def blrrlrr : Box := right blrrlr 3 21
private def tlrrlrr : Tree := (.split 1 21 .leaf .leaf)
private theorem clrrlrr : Excluded blrrlrr := fun _ h => reject tlrrlrr (by decide +kernel) h
private theorem clrrlr : Excluded blrrlr := bisect blrrlr 3 21 clrrlrl clrrlrr
private theorem clrrl : Excluded blrrl := bisect blrrl 1 9 clrrll clrrlr
private def blrrr : Box := right blrr 0 1
private def blrrrl : Box := left blrrr 1 9
private def blrrrll : Box := left blrrrl 3 21
private def tlrrrll : Tree := (.split 2 3 (.split 0 2 (.split 1 5 (.split 2 1 .leaf .leaf) .leaf) .leaf) (.split 0 2 (.split 1 5 (.split 3 13 .leaf (.split 2 9 .leaf (.split 3 16 .leaf (.split 1 4 (.split 2 21 .leaf .leaf) .leaf)))) .leaf) .leaf))
private theorem clrrrll : Excluded blrrrll := fun _ h => reject tlrrrll (by decide +kernel) h
private def blrrrlr : Box := right blrrrl 3 21
private def blrrrlrl : Box := left blrrrlr 0 2
private def blrrrlrll : Box := left blrrrlrl 1 5
private def blrrrlrlll : Box := left blrrrlrll 2 3
private def tlrrrlrlll : Tree := (.split 3 45 (.split 2 1 .leaf (.split 1 4 (.split 3 29 .leaf (.split 2 2 .leaf (.split 3 36 (.split 3 32 .leaf (.split 3 34 .leaf (.split 3 35 .leaf .leaf))) .leaf))) .leaf)) (.split 2 1 (.split 1 4 .leaf .leaf) (.split 1 4 (.split 3 93 (.split 2 2 (.split 3 61 (.split 3 52 (.split 3 48 (.split 3 46 .leaf (.split 3 47 .leaf .leaf)) .leaf) .leaf) .leaf) .leaf) .leaf) (.split 3 93 (.split 3 61 .leaf (.split 2 2 .leaf .leaf)) (.split 3 189 (.split 2 2 .leaf (.split 3 125 (.split 3 107 (.split 3 100 (.split 3 96 .leaf (.split 3 98 (.split 3 97 .leaf .leaf) .leaf)) .leaf) .leaf) .leaf)) (.split 2 2 (.split 3 381 .leaf (.split 3 765 (.split 3 509 (.split 3 436 (.split 3 407 .leaf (.split 3 421 (.split 3 414 (.split 3 410 (.split 3 408 .leaf (.split 3 409 .leaf .leaf)) .leaf) .leaf) .leaf)) .leaf) .leaf) .leaf)) .leaf))))))
private theorem clrrrlrlll : Excluded blrrrlrlll := fun _ h => reject tlrrrlrlll (by decide +kernel) h
private def blrrrlrllr : Box := right blrrrlrll 2 3
private def blrrrlrllrl : Box := left blrrrlrllr 3 45
private def blrrrlrllrll : Box := left blrrrlrllrl 2 9
private def tlrrrlrllrll : Tree := (.split 3 29 (.split 1 4 (.split 2 5 (.split 3 25 .leaf (.split 2 4 .leaf (.split 3 27 .leaf (.split 3 28 .leaf .leaf)))) (.split 3 25 (.split 2 7 .leaf .leaf) (.split 2 7 (.split 3 27 (.split 2 6 .leaf .leaf) (.split 2 6 .leaf .leaf)) (.split 3 27 (.split 2 8 (.split 3 26 .leaf .leaf) (.split 3 26 .leaf .leaf)) .leaf)))) .leaf) (.split 1 4 (.split 2 5 (.split 3 36 (.split 3 32 (.split 2 4 (.split 3 30 .leaf (.split 3 31 .leaf .leaf)) .leaf) .leaf) .leaf) .leaf) (.split 2 5 .leaf .leaf)))
private theorem clrrrlrllrll : Excluded blrrrlrllrll := fun _ h => reject tlrrrlrllrll (by decide +kernel) h
private def blrrrlrllrlr : Box := right blrrrlrllrl 2 9
private def blrrrlrllrlrl : Box := left blrrrlrllrlr 3 29
private def tlrrrlrllrlrl : Tree := (.split 1 4 (.split 2 21 (.split 3 25 (.split 2 13 (.split 3 23 .leaf (.split 2 11 .leaf (.split 3 24 .leaf .leaf))) (.split 3 23 .leaf (.split 2 16 (.split 3 24 .leaf .leaf) (.split 3 24 .leaf .leaf)))) (.split 2 13 (.split 3 27 (.split 2 11 .leaf .leaf) .leaf) .leaf)) (.split 3 25 (.split 2 45 (.split 3 23 .leaf (.split 2 29 (.split 3 24 .leaf .leaf) (.split 3 24 .leaf .leaf))) (.split 3 23 (.split 2 93 .leaf (.split 3 22 .leaf (.split 2 189 .leaf (.split 2 381 .leaf .leaf)))) (.split 2 93 .leaf .leaf))) .leaf)) .leaf)
private theorem clrrrlrllrlrl : Excluded blrrrlrllrlrl := fun _ h => reject tlrrrlrllrlrl (by decide +kernel) h
private def blrrrlrllrlrr : Box := right blrrrlrllrlr 3 29
private def tlrrrlrllrlrr : Tree := (.split 1 4 .leaf (.split 3 36 (.split 2 21 .leaf .leaf) (.split 2 21 (.split 3 40 .leaf (.split 2 13 (.split 3 42 .leaf (.split 2 11 .leaf (.split 3 43 .leaf (.split 2 12 .leaf (.split 3 44 .leaf .leaf))))) (.split 3 42 (.split 2 16 .leaf (.split 2 18 .leaf .leaf)) (.split 2 16 (.split 3 43 .leaf (.split 2 14 (.split 3 44 .leaf .leaf) (.split 3 44 .leaf .leaf))) (.split 3 43 (.split 2 18 (.split 2 17 .leaf .leaf) .leaf) .leaf))))) (.split 3 40 (.split 2 45 (.split 2 29 .leaf (.split 3 38 .leaf (.split 2 36 .leaf .leaf))) (.split 2 93 (.split 3 38 .leaf (.split 2 61 (.split 3 39 .leaf .leaf) (.split 3 39 .leaf .leaf))) (.split 3 38 .leaf (.split 2 189 (.split 3 39 .leaf .leaf) (.split 3 39 .leaf .leaf))))) (.split 2 45 (.split 3 42 (.split 2 29 (.split 2 25 (.split 3 41 .leaf .leaf) (.split 3 41 (.split 2 27 .leaf .leaf) .leaf)) (.split 2 36 (.split 3 41 (.split 2 32 (.split 2 30 .leaf (.split 2 31 .leaf .leaf)) .leaf) .leaf) .leaf)) .leaf) (.split 3 42 (.split 2 93 .leaf .leaf) .leaf))))))
private theorem clrrrlrllrlrr : Excluded blrrrlrllrlrr := fun _ h => reject tlrrrlrllrlrr (by decide +kernel) h
private theorem clrrrlrllrlr : Excluded blrrrlrllrlr := bisect blrrrlrllrlr 3 29 clrrrlrllrlrl clrrrlrllrlrr
private theorem clrrrlrllrl : Excluded blrrrlrllrl := bisect blrrrlrllrl 2 9 clrrrlrllrll clrrrlrllrlr
private def blrrrlrllrr : Box := right blrrrlrllr 3 45
private def tlrrrlrllrr : Tree := (.split 2 9 (.split 1 4 .leaf (.split 3 93 (.split 3 61 (.split 2 5 (.split 3 52 .leaf (.split 2 4 .leaf (.split 3 56 .leaf (.split 3 58 .leaf (.split 3 59 .leaf (.split 3 60 .leaf .leaf)))))) (.split 3 52 (.split 2 7 (.split 3 48 .leaf (.split 2 6 .leaf .leaf)) (.split 3 48 (.split 2 8 .leaf .leaf) (.split 3 50 (.split 2 8 (.split 3 49 .leaf .leaf) .leaf) .leaf))) (.split 2 7 (.split 3 56 (.split 2 6 (.split 3 54 .leaf (.split 3 55 .leaf .leaf)) .leaf) .leaf) .leaf))) (.split 2 5 (.split 3 74 (.split 2 4 (.split 3 67 .leaf (.split 3 70 .leaf .leaf)) .leaf) .leaf) .leaf)) .leaf)) (.split 3 93 (.split 1 4 .leaf (.split 3 61 (.split 2 21 (.split 3 52 (.split 2 13 (.split 3 48 (.split 2 11 (.split 3 46 .leaf (.split 2 10 (.split 3 47 .leaf .leaf) .leaf)) .leaf) .leaf) .leaf) .leaf) .leaf) .leaf)) .leaf))
private theorem clrrrlrllrr : Excluded blrrrlrllrr := fun _ h => reject tlrrrlrllrr (by decide +kernel) h
private theorem clrrrlrllr : Excluded blrrrlrllr := bisect blrrrlrllr 3 45 clrrrlrllrl clrrrlrllrr
private theorem clrrrlrll : Excluded blrrrlrll := bisect blrrrlrll 2 3 clrrrlrlll clrrrlrllr
private def blrrrlrlr : Box := right blrrrlrl 1 5
private def blrrrlrlrl : Box := left blrrrlrlr 2 3
private def tlrrrlrlrl : Tree := (.split 3 45 .leaf (.split 1 7 .leaf .leaf))
private theorem clrrrlrlrl : Excluded blrrrlrlrl := fun _ h => reject tlrrrlrlrl (by decide +kernel) h
private def blrrrlrlrr : Box := right blrrrlrlr 2 3
private def blrrrlrlrrl : Box := left blrrrlrlrr 3 45
private def tlrrrlrlrrl : Tree := .leaf
private theorem clrrrlrlrrl : Excluded blrrrlrlrrl := fun _ h => reject tlrrrlrlrrl (by decide +kernel) h
private def blrrrlrlrrr : Box := right blrrrlrlrr 3 45
private def blrrrlrlrrrl : Box := left blrrrlrlrrr 1 7
private def blrrrlrlrrrll : Box := left blrrrlrlrrrl 3 93
private def blrrrlrlrrrlll : Box := left blrrrlrlrrrll 2 9
private def tlrrrlrlrrrlll : Tree := .leaf
private theorem clrrrlrlrrrlll : Excluded blrrrlrlrrrlll := fun _ h => reject tlrrrlrlrrrlll (by decide +kernel) h
private def blrrrlrlrrrllr : Box := right blrrrlrlrrrll 2 9
private def blrrrlrlrrrllrl : Box := left blrrrlrlrrrllr 3 61
private def tlrrrlrlrrrllrl : Tree := .leaf
private theorem clrrrlrlrrrllrl : Excluded blrrrlrlrrrllrl := fun _ h => reject tlrrrlrlrrrllrl (by decide +kernel) h
private def blrrrlrlrrrllrr : Box := right blrrrlrlrrrllr 3 61
private def blrrrlrlrrrllrrl : Box := left blrrrlrlrrrllrr 1 6
private def blrrrlrlrrrllrrll : Box := left blrrrlrlrrrllrrl 2 21
private def tlrrrlrlrrrllrrll : Tree := (.split 3 74 .leaf (.split 2 13 .leaf (.split 3 83 .leaf (.split 2 16 .leaf (.split 3 88 .leaf (.split 2 18 .leaf (.split 3 90 .leaf (.split 2 19 (.split 3 91 .leaf (.split 3 92 .leaf .leaf)) (.split 3 91 .leaf .leaf)))))))))
private theorem clrrrlrlrrrllrrll : Excluded blrrrlrlrrrllrrll := fun _ h => reject tlrrrlrlrrrllrrll (by decide +kernel) h
private def blrrrlrlrrrllrrlr : Box := right blrrrlrlrrrllrrl 2 21
private def blrrrlrlrrrllrrlrl : Box := left blrrrlrlrrrllrrlr 3 74
private def tlrrrlrlrrrllrrlrl : Tree := (.split 2 45 .leaf (.split 3 67 .leaf (.split 2 93 .leaf .leaf)))
private theorem clrrrlrlrrrllrrlrl : Excluded blrrrlrlrrrllrrlrl := fun _ h => reject tlrrrlrlrrrllrrlrl (by decide +kernel) h
private def blrrrlrlrrrllrrlrr : Box := right blrrrlrlrrrllrrlr 3 74
private def blrrrlrlrrrllrrlrrl : Box := left blrrrlrlrrrllrrlrr 2 45
private def tlrrrlrlrrrllrrlrrl : Tree := (.split 3 83 (.split 2 29 .leaf (.split 3 78 .leaf (.split 2 36 (.split 3 80 .leaf (.split 2 32 .leaf .leaf)) (.split 3 80 .leaf (.split 2 40 (.split 3 81 .leaf (.split 2 38 (.split 3 82 .leaf (.split 2 37 .leaf .leaf)) (.split 3 82 .leaf .leaf))) (.split 3 81 .leaf (.split 2 42 (.split 3 82 .leaf .leaf) .leaf))))))) (.split 2 29 (.split 3 88 (.split 2 25 (.split 3 85 .leaf (.split 2 23 .leaf (.split 3 86 .leaf (.split 3 87 .leaf .leaf)))) (.split 3 85 .leaf (.split 2 27 (.split 3 86 .leaf (.split 3 87 .leaf .leaf)) (.split 3 86 .leaf .leaf)))) (.split 2 25 (.split 3 90 (.split 2 23 (.split 2 22 (.split 3 89 .leaf .leaf) (.split 3 89 .leaf .leaf)) .leaf) .leaf) .leaf)) (.split 3 88 (.split 2 36 (.split 3 85 (.split 2 32 (.split 2 30 .leaf (.split 3 84 .leaf .leaf)) (.split 2 34 (.split 3 84 .leaf .leaf) .leaf)) .leaf) .leaf) .leaf)))
private theorem clrrrlrlrrrllrrlrrl : Excluded blrrrlrlrrrllrrlrrl := fun _ h => reject tlrrrlrlrrrllrrlrrl (by decide +kernel) h
private def blrrrlrlrrrllrrlrrr : Box := right blrrrlrlrrrllrrlrr 2 45
private def tlrrrlrlrrrllrrlrrr : Tree := (.split 3 83 (.split 2 93 (.split 3 78 (.split 2 61 .leaf (.split 3 76 .leaf (.split 2 74 .leaf (.split 2 83 .leaf (.split 3 77 .leaf .leaf))))) (.split 2 61 (.split 3 80 (.split 2 52 .leaf (.split 2 56 .leaf (.split 3 79 .leaf .leaf))) (.split 2 52 (.split 3 81 .leaf .leaf) .leaf)) (.split 3 80 (.split 2 74 (.split 2 67 (.split 3 79 .leaf .leaf) (.split 3 79 (.split 2 70 (.split 2 68 .leaf (.split 2 69 .leaf .leaf)) .leaf) .leaf)) .leaf) .leaf))) (.split 3 78 (.split 2 189 (.split 3 76 (.split 2 125 .leaf .leaf) (.split 2 125 (.split 2 107 (.split 3 77 .leaf .leaf) (.split 3 77 .leaf .leaf)) (.split 2 151 (.split 3 77 .leaf .leaf) .leaf))) (.split 3 76 (.split 2 381 (.split 2 253 (.split 3 75 .leaf .leaf) (.split 3 75 .leaf .leaf)) (.split 2 765 (.split 3 75 .leaf .leaf) (.split 3 75 .leaf .leaf))) .leaf)) .leaf)) .leaf)
private theorem clrrrlrlrrrllrrlrrr : Excluded blrrrlrlrrrllrrlrrr := fun _ h => reject tlrrrlrlrrrllrrlrrr (by decide +kernel) h
private theorem clrrrlrlrrrllrrlrr : Excluded blrrrlrlrrrllrrlrr := bisect blrrrlrlrrrllrrlrr 2 45 clrrrlrlrrrllrrlrrl clrrrlrlrrrllrrlrrr
private theorem clrrrlrlrrrllrrlr : Excluded blrrrlrlrrrllrrlr := bisect blrrrlrlrrrllrrlr 3 74 clrrrlrlrrrllrrlrl clrrrlrlrrrllrrlrr
private theorem clrrrlrlrrrllrrl : Excluded blrrrlrlrrrllrrl := bisect blrrrlrlrrrllrrl 2 21 clrrrlrlrrrllrrll clrrrlrlrrrllrrlr
private def blrrrlrlrrrllrrr : Box := right blrrrlrlrrrllrr 1 6
private def tlrrrlrlrrrllrrr : Tree := .leaf
private theorem clrrrlrlrrrllrrr : Excluded blrrrlrlrrrllrrr := fun _ h => reject tlrrrlrlrrrllrrr (by decide +kernel) h
private theorem clrrrlrlrrrllrr : Excluded blrrrlrlrrrllrr := bisect blrrrlrlrrrllrr 1 6 clrrrlrlrrrllrrl clrrrlrlrrrllrrr
private theorem clrrrlrlrrrllr : Excluded blrrrlrlrrrllr := bisect blrrrlrlrrrllr 3 61 clrrrlrlrrrllrl clrrrlrlrrrllrr
private theorem clrrrlrlrrrll : Excluded blrrrlrlrrrll := bisect blrrrlrlrrrll 2 9 clrrrlrlrrrlll clrrrlrlrrrllr
private def blrrrlrlrrrlr : Box := right blrrrlrlrrrl 3 93
private def blrrrlrlrrrlrl : Box := left blrrrlrlrrrlr 2 9
private def tlrrrlrlrrrlrl : Tree := (.split 1 6 (.split 3 189 (.split 2 5 .leaf (.split 3 125 (.split 2 7 .leaf .leaf) (.split 2 7 (.split 3 151 .leaf (.split 2 6 .leaf (.split 3 168 (.split 3 159 (.split 3 155 .leaf (.split 3 157 .leaf .leaf)) .leaf) .leaf))) (.split 3 151 (.split 3 137 (.split 2 8 .leaf (.split 3 131 (.split 3 128 (.split 3 126 .leaf .leaf) .leaf) .leaf)) (.split 2 8 (.split 3 144 (.split 3 140 (.split 3 138 .leaf .leaf) .leaf) .leaf) .leaf)) .leaf)))) (.split 2 5 (.split 3 381 (.split 2 4 .leaf (.split 3 253 .leaf (.split 3 304 (.split 3 276 .leaf (.split 3 289 (.split 3 282 .leaf (.split 3 285 (.split 3 283 .leaf .leaf) .leaf)) .leaf)) .leaf))) (.split 3 765 (.split 2 4 .leaf .leaf) (.split 2 4 (.split 3 1533 (.split 3 1021 (.split 3 875 .leaf (.split 3 942 (.split 3 907 .leaf (.split 3 924 .leaf (.split 3 933 (.split 3 928 .leaf .leaf) .leaf))) .leaf)) .leaf) .leaf) .leaf))) (.split 3 381 (.split 2 7 (.split 3 253 (.split 2 6 (.split 3 217 (.split 3 202 (.split 3 195 (.split 3 192 .leaf (.split 3 193 .leaf .leaf)) .leaf) .leaf) .leaf) .leaf) .leaf) .leaf) .leaf))) .leaf)
private theorem clrrrlrlrrrlrl : Excluded blrrrlrlrrrlrl := fun _ h => reject tlrrrlrlrrrlrl (by decide +kernel) h
private def blrrrlrlrrrlrr : Box := right blrrrlrlrrrlr 2 9
private def blrrrlrlrrrlrrl : Box := left blrrrlrlrrrlrr 3 189
private def tlrrrlrlrrrlrrl : Tree := (.split 1 6 (.split 2 21 (.split 3 125 (.split 2 13 (.split 3 107 (.split 2 11 .leaf (.split 3 100 .leaf (.split 3 103 .leaf (.split 2 12 .leaf (.split 3 105 (.split 3 104 .leaf .leaf) .leaf))))) (.split 2 11 (.split 3 115 (.split 2 10 .leaf (.split 3 111 .leaf (.split 3 113 (.split 3 112 .leaf .leaf) .leaf))) (.split 3 120 (.split 2 10 (.split 3 117 .leaf (.split 3 118 .leaf .leaf)) .leaf) .leaf)) (.split 3 115 (.split 3 111 (.split 2 12 .leaf .leaf) .leaf) .leaf))) (.split 3 107 (.split 2 16 (.split 3 100 (.split 3 96 .leaf (.split 2 14 .leaf (.split 3 98 (.split 2 15 .leaf (.split 3 97 .leaf .leaf)) (.split 2 15 (.split 3 99 .leaf .leaf) .leaf)))) (.split 2 14 (.split 3 103 (.split 3 101 .leaf .leaf) .leaf) .leaf)) (.split 3 100 (.split 2 18 (.split 3 96 (.split 2 17 (.split 3 94 .leaf (.split 3 95 .leaf .leaf)) (.split 3 94 .leaf .leaf)) .leaf) .leaf) .leaf)) .leaf)) .leaf) .leaf) .leaf)
private theorem clrrrlrlrrrlrrl : Excluded blrrrlrlrrrlrrl := fun _ h => reject tlrrrlrlrrrlrrl (by decide +kernel) h
private def blrrrlrlrrrlrrr : Box := right blrrrlrlrrrlrr 3 189
private def blrrrlrlrrrlrrrl : Box := left blrrrlrlrrrlrrr 1 6
private def tlrrrlrlrrrlrrrl : Tree := .leaf
private theorem clrrrlrlrrrlrrrl : Excluded blrrrlrlrrrlrrrl := fun _ h => reject tlrrrlrlrrrlrrrl (by decide +kernel) h
private def blrrrlrlrrrlrrrr : Box := right blrrrlrlrrrlrrr 1 6
private def blrrrlrlrrrlrrrrl : Box := left blrrrlrlrrrlrrrr 2 21
private def blrrrlrlrrrlrrrrll : Box := left blrrrlrlrrrlrrrrl 3 381
private def tlrrrlrlrrrlrrrrll : Tree := .leaf
private theorem clrrrlrlrrrlrrrrll : Excluded blrrrlrlrrrlrrrrll := fun _ h => reject tlrrrlrlrrrlrrrrll (by decide +kernel) h
private def blrrrlrlrrrlrrrrlr : Box := right blrrrlrlrrrlrrrrl 3 381
private def blrrrlrlrrrlrrrrlrl : Box := left blrrrlrlrrrlrrrrlr 2 13
private def tlrrrlrlrrrlrrrrlrl : Tree := .leaf
private theorem clrrrlrlrrrlrrrrlrl : Excluded blrrrlrlrrrlrrrrlrl := fun _ h => reject tlrrrlrlrrrlrrrrlrl (by decide +kernel) h
private def blrrrlrlrrrlrrrrlrr : Box := right blrrrlrlrrrlrrrrlr 2 13
private def blrrrlrlrrrlrrrrlrrl : Box := left blrrrlrlrrrlrrrrlrr 3 765
private def tlrrrlrlrrrlrrrrlrrl : Tree := (.split 3 509 .leaf (.split 2 16 .leaf (.split 3 612 .leaf (.split 2 18 .leaf (.split 3 680 (.split 2 19 .leaf (.split 3 644 .leaf (.split 2 20 .leaf (.split 3 662 .leaf (.split 3 671 .leaf (.split 3 675 .leaf (.split 3 677 (.split 3 676 .leaf .leaf) .leaf))))))) (.split 2 19 .leaf (.split 3 720 (.split 2 20 .leaf .leaf) (.split 2 20 (.split 3 742 (.split 3 731 .leaf (.split 3 736 .leaf (.split 3 739 (.split 3 737 .leaf .leaf) .leaf))) .leaf) .leaf))))))))
private theorem clrrrlrlrrrlrrrrlrrl : Excluded blrrrlrlrrrlrrrrlrrl := fun _ h => reject tlrrrlrlrrrlrrrrlrrl (by decide +kernel) h
private def blrrrlrlrrrlrrrrlrrr : Box := right blrrrlrlrrrlrrrrlrr 3 765
private def blrrrlrlrrrlrrrrlrrrl : Box := left blrrrlrlrrrlrrrrlrrr 3 1533
private def tlrrrlrlrrrlrrrrlrrrl : Tree := (.split 2 16 (.split 3 1021 .leaf (.split 2 14 .leaf (.split 3 1226 .leaf (.split 2 15 .leaf (.split 3 1363 .leaf (.split 3 1443 (.split 3 1402 (.split 3 1382 .leaf (.split 3 1392 (.split 3 1387 (.split 3 1384 .leaf .leaf) .leaf) .leaf)) .leaf) .leaf)))))) (.split 3 1021 (.split 2 18 (.split 3 875 .leaf (.split 2 17 .leaf (.split 3 942 (.split 3 907 .leaf (.split 3 924 .leaf (.split 3 933 (.split 3 928 .leaf (.split 3 930 .leaf .leaf)) .leaf))) .leaf))) (.split 3 875 (.split 2 19 (.split 3 816 .leaf (.split 3 845 (.split 3 830 (.split 3 823 (.split 3 819 (.split 3 817 .leaf .leaf) .leaf) .leaf) .leaf) .leaf)) .leaf) .leaf)) (.split 2 18 (.split 3 1226 (.split 2 17 (.split 3 1114 (.split 3 1066 .leaf (.split 3 1089 .leaf (.split 3 1101 (.split 3 1095 .leaf (.split 3 1098 .leaf (.split 3 1099 .leaf (.split 3 1100 .leaf .leaf)))) .leaf))) .leaf) .leaf) .leaf) .leaf)))
private theorem clrrrlrlrrrlrrrrlrrrl : Excluded blrrrlrlrrrlrrrrlrrrl := fun _ h => reject tlrrrlrlrrrlrrrrlrrrl (by decide +kernel) h
private def blrrrlrlrrrlrrrrlrrrr : Box := right blrrrlrlrrrlrrrrlrrr 3 1533
private def tlrrrlrlrrrlrrrrlrrrr : Tree := (.split 2 16 (.split 3 3069 (.split 2 14 .leaf (.split 3 2045 (.split 2 15 (.split 3 1753 .leaf (.split 3 1888 .leaf (.split 3 1963 (.split 3 1925 .leaf (.split 3 1944 .leaf (.split 3 1953 .leaf (.split 3 1958 .leaf .leaf)))) .leaf))) .leaf) .leaf)) (.split 2 14 (.split 3 6141 (.split 3 4093 (.split 3 3508 .leaf (.split 3 3778 (.split 3 3638 .leaf (.split 3 3707 .leaf (.split 3 3742 (.split 3 3724 (.split 3 3715 .leaf (.split 3 3719 .leaf (.split 3 3721 .leaf .leaf))) .leaf) .leaf))) .leaf)) .leaf) .leaf) .leaf)) .leaf)
private theorem clrrrlrlrrrlrrrrlrrrr : Excluded blrrrlrlrrrlrrrrlrrrr := fun _ h => reject tlrrrlrlrrrlrrrrlrrrr (by decide +kernel) h
private theorem clrrrlrlrrrlrrrrlrrr : Excluded blrrrlrlrrrlrrrrlrrr := bisect blrrrlrlrrrlrrrrlrrr 3 1533 clrrrlrlrrrlrrrrlrrrl clrrrlrlrrrlrrrrlrrrr
private theorem clrrrlrlrrrlrrrrlrr : Excluded blrrrlrlrrrlrrrrlrr := bisect blrrrlrlrrrlrrrrlrr 3 765 clrrrlrlrrrlrrrrlrrl clrrrlrlrrrlrrrrlrrr
private theorem clrrrlrlrrrlrrrrlr : Excluded blrrrlrlrrrlrrrrlr := bisect blrrrlrlrrrlrrrrlr 2 13 clrrrlrlrrrlrrrrlrl clrrrlrlrrrlrrrrlrr
private theorem clrrrlrlrrrlrrrrl : Excluded blrrrlrlrrrlrrrrl := bisect blrrrlrlrrrlrrrrl 3 381 clrrrlrlrrrlrrrrll clrrrlrlrrrlrrrrlr
private def blrrrlrlrrrlrrrrr : Box := right blrrrlrlrrrlrrrr 2 21
private def blrrrlrlrrrlrrrrrl : Box := left blrrrlrlrrrlrrrrr 3 381
private def blrrrlrlrrrlrrrrrll : Box := left blrrrlrlrrrlrrrrrl 3 253
private def tlrrrlrlrrrlrrrrrll : Tree := (.split 2 45 .leaf (.split 3 217 .leaf (.split 2 93 .leaf .leaf)))
private theorem clrrrlrlrrrlrrrrrll : Excluded blrrrlrlrrrlrrrrrll := fun _ h => reject tlrrrlrlrrrlrrrrrll (by decide +kernel) h
private def blrrrlrlrrrlrrrrrlr : Box := right blrrrlrlrrrlrrrrrl 3 253
private def blrrrlrlrrrlrrrrrlrl : Box := left blrrrlrlrrrlrrrrrlr 2 45
private def tlrrrlrlrrrlrrrrrlrl : Tree := (.split 3 304 .leaf (.split 2 29 .leaf (.split 3 338 .leaf (.split 2 36 .leaf (.split 3 358 .leaf (.split 2 40 (.split 3 369 .leaf (.split 2 38 .leaf (.split 3 375 .leaf (.split 2 39 .leaf (.split 3 378 .leaf (.split 3 379 .leaf (.split 3 380 .leaf .leaf))))))) (.split 3 369 (.split 2 42 .leaf (.split 3 363 (.split 2 43 .leaf (.split 3 360 .leaf (.split 2 44 .leaf (.split 3 361 .leaf .leaf)))) (.split 2 43 (.split 3 366 .leaf (.split 3 367 .leaf (.split 3 368 .leaf .leaf))) (.split 3 366 (.split 2 44 (.split 3 364 .leaf .leaf) .leaf) .leaf)))) (.split 2 42 (.split 3 375 (.split 3 372 (.split 2 41 .leaf .leaf) (.split 2 41 .leaf .leaf)) (.split 3 378 (.split 2 41 (.split 3 376 .leaf .leaf) .leaf) .leaf)) .leaf))))))))
private theorem clrrrlrlrrrlrrrrrlrl : Excluded blrrrlrlrrrlrrrrrlrl := fun _ h => reject tlrrrlrlrrrlrrrrrlrl (by decide +kernel) h
private def blrrrlrlrrrlrrrrrlrr : Box := right blrrrlrlrrrlrrrrrlr 2 45
private def blrrrlrlrrrlrrrrrlrrl : Box := left blrrrlrlrrrlrrrrrlrr 3 304
private def blrrrlrlrrrlrrrrrlrrll : Box := left blrrrlrlrrrlrrrrrlrrl 2 93
private def tlrrrlrlrrrlrrrrrlrrll : Tree := (.split 3 276 .leaf (.split 2 61 .leaf (.split 3 289 .leaf (.split 2 74 .leaf (.split 3 296 .leaf (.split 2 83 .leaf (.split 3 300 (.split 2 88 .leaf (.split 3 298 .leaf (.split 2 90 .leaf (.split 2 91 (.split 3 299 .leaf .leaf) (.split 3 299 .leaf .leaf))))) (.split 2 88 (.split 3 302 (.split 2 85 .leaf (.split 2 86 .leaf (.split 3 301 .leaf .leaf))) (.split 2 85 (.split 3 303 .leaf .leaf) .leaf)) .leaf))))))))
private theorem clrrrlrlrrrlrrrrrlrrll : Excluded blrrrlrlrrrlrrrrrlrrll := fun _ h => reject tlrrrlrlrrrlrrrrrlrrll (by decide +kernel) h
private def blrrrlrlrrrlrrrrrlrrlr : Box := right blrrrlrlrrrlrrrrrlrrl 2 93
private def blrrrlrlrrrlrrrrrlrrlrl : Box := left blrrrlrlrrrlrrrrrlrrlr 3 276
private def blrrrlrlrrrlrrrrrlrrlrll : Box := left blrrrlrlrrrlrrrrrlrrlrl 2 189
private def tlrrrlrlrrrlrrrrrlrrlrll : Tree := (.split 3 264 .leaf (.split 2 125 .leaf (.split 2 151 .leaf (.split 3 270 .leaf (.split 2 168 .leaf (.split 3 273 .leaf (.split 2 178 .leaf (.split 3 274 .leaf (.split 2 183 .leaf (.split 3 275 .leaf .leaf))))))))))
private theorem clrrrlrlrrrlrrrrrlrrlrll : Excluded blrrrlrlrrrlrrrrrlrrlrll := fun _ h => reject tlrrrlrlrrrlrrrrrlrrlrll (by decide +kernel) h
private def blrrrlrlrrrlrrrrrlrrlrlr : Box := right blrrrlrlrrrlrrrrrlrrlrl 2 189
private def blrrrlrlrrrlrrrrrlrrlrlrl : Box := left blrrrlrlrrrlrrrrrlrrlrlr 3 264
private def tlrrrlrlrrrlrrrrrlrrlrlrl : Tree := (.split 2 381 .leaf (.split 2 765 (.split 3 258 .leaf (.split 2 509 (.split 3 261 .leaf (.split 2 436 .leaf (.split 3 262 .leaf (.split 2 470 (.split 3 263 .leaf .leaf) (.split 3 263 .leaf .leaf))))) (.split 3 261 (.split 2 612 .leaf .leaf) (.split 2 612 (.split 3 262 .leaf (.split 2 556 (.split 3 263 (.split 2 532 .leaf (.split 2 544 (.split 2 538 .leaf (.split 2 541 (.split 2 539 .leaf .leaf) .leaf)) .leaf)) .leaf) .leaf)) (.split 3 262 .leaf .leaf))))) (.split 3 258 (.split 2 1533 .leaf (.split 3 255 .leaf (.split 2 3069 (.split 3 256 .leaf (.split 2 2045 .leaf (.split 3 257 .leaf .leaf))) (.split 3 256 .leaf (.split 2 6141 (.split 3 257 .leaf .leaf) (.split 3 257 (.split 2 12285 (.split 2 8189 .leaf (.split 2 9828 .leaf (.split 2 10920 (.split 2 10345 (.split 2 10080 (.split 2 9952 .leaf (.split 2 10016 (.split 2 9984 .leaf (.split 2 10000 (.split 2 9992 .leaf (.split 2 9996 .leaf .leaf)) (.split 2 10008 (.split 2 10004 .leaf .leaf) .leaf))) .leaf)) .leaf) .leaf) .leaf))) .leaf) .leaf)))))) (.split 2 1533 (.split 3 261 (.split 2 1021 (.split 3 259 .leaf (.split 2 875 (.split 3 260 .leaf .leaf) (.split 3 260 .leaf .leaf))) (.split 3 259 .leaf (.split 2 1226 (.split 3 260 .leaf .leaf) .leaf))) .leaf) (.split 3 261 (.split 2 3069 .leaf .leaf) .leaf)))))
private theorem clrrrlrlrrrlrrrrrlrrlrlrl : Excluded blrrrlrlrrrlrrrrrlrrlrlrl := fun _ h => reject tlrrrlrlrrrlrrrrrlrrlrlrl (by decide +kernel) h
private def blrrrlrlrrrlrrrrrlrrlrlrr : Box := right blrrrlrlrrrlrrrrrlrrlrlr 3 264
private def tlrrrlrlrrrlrrrrrlrrlrlrr : Tree := (.split 2 381 (.split 2 253 (.split 3 270 .leaf (.split 2 217 (.split 3 273 (.split 2 202 .leaf (.split 3 271 .leaf (.split 2 209 .leaf .leaf))) (.split 2 202 (.split 3 274 .leaf (.split 2 195 (.split 3 275 .leaf .leaf) .leaf)) (.split 3 274 .leaf .leaf))) (.split 3 273 (.split 2 234 (.split 3 271 .leaf (.split 2 225 (.split 3 272 .leaf .leaf) (.split 3 272 .leaf .leaf))) (.split 3 271 (.split 2 243 .leaf (.split 2 248 (.split 2 245 .leaf (.split 2 246 .leaf .leaf)) .leaf)) .leaf)) .leaf))) (.split 3 270 (.split 2 304 (.split 3 267 .leaf (.split 2 276 (.split 3 268 .leaf (.split 2 264 (.split 3 269 .leaf .leaf) (.split 3 269 .leaf .leaf))) (.split 3 268 .leaf (.split 2 289 (.split 3 269 (.split 2 282 .leaf (.split 2 285 (.split 2 283 .leaf (.split 2 284 .leaf .leaf)) .leaf)) .leaf) .leaf)))) (.split 3 267 (.split 2 338 (.split 3 265 .leaf (.split 2 320 .leaf (.split 3 266 .leaf .leaf))) (.split 3 265 .leaf (.split 2 358 (.split 3 266 .leaf .leaf) (.split 3 266 .leaf .leaf)))) (.split 2 338 (.split 3 268 .leaf .leaf) .leaf))) .leaf)) (.split 2 765 (.split 3 270 (.split 2 509 (.split 3 267 (.split 2 436 (.split 3 265 .leaf .leaf) .leaf) .leaf) .leaf) .leaf) .leaf))
private theorem clrrrlrlrrrlrrrrrlrrlrlrr : Excluded blrrrlrlrrrlrrrrrlrrlrlrr := fun _ h => reject tlrrrlrlrrrlrrrrrlrrlrlrr (by decide +kernel) h
private theorem clrrrlrlrrrlrrrrrlrrlrlr : Excluded blrrrlrlrrrlrrrrrlrrlrlr := bisect blrrrlrlrrrlrrrrrlrrlrlr 3 264 clrrrlrlrrrlrrrrrlrrlrlrl clrrrlrlrrrlrrrrrlrrlrlrr
private theorem clrrrlrlrrrlrrrrrlrrlrl : Excluded blrrrlrlrrrlrrrrrlrrlrl := bisect blrrrlrlrrrlrrrrrlrrlrl 2 189 clrrrlrlrrrlrrrrrlrrlrll clrrrlrlrrrlrrrrrlrrlrlr
private def blrrrlrlrrrlrrrrrlrrlrr : Box := right blrrrlrlrrrlrrrrrlrrlr 3 276
private def blrrrlrlrrrlrrrrrlrrlrrl : Box := left blrrrlrlrrrlrrrrrlrrlrr 2 189
private def blrrrlrlrrrlrrrrrlrrlrrll : Box := left blrrrlrlrrrlrrrrrlrrlrrl 3 289
private def tlrrrlrlrrrlrrrrrlrrlrrll : Tree := (.split 2 125 (.split 2 107 .leaf (.split 3 282 .leaf (.split 3 285 .leaf (.split 2 115 .leaf (.split 3 287 (.split 2 120 .leaf (.split 2 122 .leaf (.split 3 286 .leaf .leaf))) (.split 2 120 (.split 2 117 (.split 3 288 .leaf .leaf) (.split 3 288 .leaf .leaf)) .leaf)))))) (.split 2 151 (.split 3 282 (.split 2 137 .leaf (.split 3 279 .leaf (.split 2 144 .leaf (.split 3 280 .leaf (.split 2 147 (.split 3 281 .leaf .leaf) (.split 3 281 (.split 2 149 .leaf (.split 2 150 .leaf .leaf)) .leaf)))))) (.split 2 137 (.split 3 285 (.split 2 131 (.split 3 283 .leaf (.split 2 128 .leaf (.split 3 284 .leaf .leaf))) (.split 3 283 .leaf (.split 2 134 (.split 3 284 .leaf .leaf) (.split 3 284 .leaf .leaf)))) (.split 2 131 (.split 3 287 (.split 2 128 (.split 3 286 .leaf .leaf) .leaf) .leaf) .leaf)) (.split 3 285 (.split 2 144 (.split 3 283 (.split 2 140 (.split 2 138 .leaf .leaf) .leaf) .leaf) .leaf) .leaf))) (.split 3 282 (.split 2 168 (.split 3 279 (.split 2 159 .leaf (.split 3 277 .leaf (.split 2 163 (.split 3 278 .leaf .leaf) (.split 3 278 .leaf .leaf)))) (.split 2 159 (.split 3 280 .leaf .leaf) .leaf)) (.split 3 279 (.split 2 178 (.split 3 277 (.split 2 173 .leaf (.split 2 175 .leaf (.split 2 176 .leaf (.split 2 177 .leaf .leaf)))) (.split 2 173 (.split 3 278 .leaf .leaf) .leaf)) .leaf) .leaf)) .leaf)))
private theorem clrrrlrlrrrlrrrrrlrrlrrll : Excluded blrrrlrlrrrlrrrrrlrrlrrll := fun _ h => reject tlrrrlrlrrrlrrrrrlrrlrrll (by decide +kernel) h
private def blrrrlrlrrrlrrrrrlrrlrrlr : Box := right blrrrlrlrrrlrrrrrlrrlrrl 3 289
private def tlrrrlrlrrrlrrrrrlrrlrrlr : Tree := (.split 2 125 (.split 3 296 (.split 2 107 (.split 2 100 (.split 3 292 .leaf (.split 2 96 .leaf (.split 3 294 .leaf (.split 2 98 .leaf (.split 3 295 .leaf .leaf))))) (.split 3 292 .leaf (.split 3 294 (.split 2 103 (.split 3 293 .leaf .leaf) (.split 2 105 (.split 3 293 .leaf .leaf) .leaf)) .leaf))) (.split 2 115 (.split 3 292 (.split 2 111 (.split 3 290 .leaf (.split 2 109 (.split 3 291 .leaf .leaf) (.split 3 291 .leaf .leaf))) (.split 3 290 .leaf .leaf)) .leaf) .leaf)) (.split 2 107 (.split 3 300 (.split 2 100 (.split 2 96 (.split 3 298 (.split 2 94 (.split 3 297 .leaf .leaf) (.split 3 297 .leaf .leaf)) .leaf) .leaf) .leaf) .leaf) .leaf)) .leaf)
private theorem clrrrlrlrrrlrrrrrlrrlrrlr : Excluded blrrrlrlrrrlrrrrrlrrlrrlr := fun _ h => reject tlrrrlrlrrrlrrrrrlrrlrrlr (by decide +kernel) h
private theorem clrrrlrlrrrlrrrrrlrrlrrl : Excluded blrrrlrlrrrlrrrrrlrrlrrl := bisect blrrrlrlrrrlrrrrrlrrlrrl 3 289 clrrrlrlrrrlrrrrrlrrlrrll clrrrlrlrrrlrrrrrlrrlrrlr
private def blrrrlrlrrrlrrrrrlrrlrrr : Box := right blrrrlrlrrrlrrrrrlrrlrr 2 189
private def tlrrrlrlrrrlrrrrrlrrlrrr : Tree := (.split 3 289 (.split 2 381 .leaf .leaf) .leaf)
private theorem clrrrlrlrrrlrrrrrlrrlrrr : Excluded blrrrlrlrrrlrrrrrlrrlrrr := fun _ h => reject tlrrrlrlrrrlrrrrrlrrlrrr (by decide +kernel) h
private theorem clrrrlrlrrrlrrrrrlrrlrr : Excluded blrrrlrlrrrlrrrrrlrrlrr := bisect blrrrlrlrrrlrrrrrlrrlrr 2 189 clrrrlrlrrrlrrrrrlrrlrrl clrrrlrlrrrlrrrrrlrrlrrr
private theorem clrrrlrlrrrlrrrrrlrrlr : Excluded blrrrlrlrrrlrrrrrlrrlr := bisect blrrrlrlrrrlrrrrrlrrlr 3 276 clrrrlrlrrrlrrrrrlrrlrl clrrrlrlrrrlrrrrrlrrlrr
private theorem clrrrlrlrrrlrrrrrlrrl : Excluded blrrrlrlrrrlrrrrrlrrl := bisect blrrrlrlrrrlrrrrrlrrl 2 93 clrrrlrlrrrlrrrrrlrrll clrrrlrlrrrlrrrrrlrrlr
private def blrrrlrlrrrlrrrrrlrrr : Box := right blrrrlrlrrrlrrrrrlrr 3 304
private def blrrrlrlrrrlrrrrrlrrrl : Box := left blrrrlrlrrrlrrrrrlrrr 2 93
private def blrrrlrlrrrlrrrrrlrrrll : Box := left blrrrlrlrrrlrrrrrlrrrl 3 338
private def blrrrlrlrrrlrrrrrlrrrlll : Box := left blrrrlrlrrrlrrrrrlrrrll 2 61
private def tlrrrlrlrrrlrrrrrlrrrlll : Tree := (.split 3 320 .leaf (.split 2 52 .leaf (.split 3 329 (.split 2 56 .leaf (.split 3 324 .leaf (.split 2 58 .leaf (.split 3 326 .leaf (.split 2 59 .leaf (.split 3 327 .leaf .leaf)))))) (.split 2 56 (.split 3 333 .leaf (.split 2 54 .leaf (.split 3 335 (.split 2 55 .leaf (.split 3 334 .leaf .leaf)) (.split 2 55 (.split 3 336 .leaf .leaf) .leaf)))) (.split 3 333 (.split 2 58 (.split 3 331 (.split 2 57 .leaf .leaf) (.split 2 57 (.split 3 332 .leaf .leaf) .leaf)) .leaf) .leaf)))))
private theorem clrrrlrlrrrlrrrrrlrrrlll : Excluded blrrrlrlrrrlrrrrrlrrrlll := fun _ h => reject tlrrrlrlrrrlrrrrrlrrrlll (by decide +kernel) h
private def blrrrlrlrrrlrrrrrlrrrllr : Box := right blrrrlrlrrrlrrrrrlrrrll 2 61
private def tlrrrlrlrrrlrrrrrlrrrllr : Tree := (.split 3 320 (.split 2 74 (.split 3 312 (.split 2 67 .leaf (.split 3 308 .leaf (.split 2 70 .leaf (.split 2 72 .leaf (.split 3 310 .leaf (.split 2 73 .leaf (.split 3 311 .leaf .leaf))))))) (.split 2 67 (.split 3 316 .leaf (.split 2 64 .leaf (.split 3 318 .leaf (.split 2 65 .leaf (.split 2 66 (.split 3 319 .leaf .leaf) .leaf))))) (.split 3 316 (.split 2 70 (.split 3 314 .leaf (.split 2 68 .leaf (.split 2 69 .leaf (.split 3 315 .leaf .leaf)))) (.split 2 72 (.split 3 314 (.split 2 71 .leaf (.split 3 313 .leaf .leaf)) .leaf) .leaf)) (.split 2 70 (.split 3 318 (.split 2 68 (.split 3 317 .leaf .leaf) .leaf) .leaf) .leaf)))) (.split 3 312 (.split 2 83 (.split 3 308 (.split 2 78 .leaf (.split 2 80 (.split 3 306 .leaf (.split 3 307 (.split 2 79 .leaf .leaf) .leaf)) (.split 3 306 (.split 2 81 (.split 3 305 .leaf .leaf) (.split 3 305 .leaf .leaf)) .leaf))) (.split 2 78 (.split 3 310 (.split 2 76 (.split 3 309 .leaf .leaf) (.split 3 309 .leaf .leaf)) .leaf) .leaf)) .leaf) .leaf)) (.split 2 74 (.split 3 329 (.split 2 67 (.split 3 324 (.split 2 64 (.split 3 322 .leaf (.split 2 62 .leaf (.split 2 63 (.split 3 323 .leaf .leaf) .leaf))) (.split 3 322 (.split 2 65 (.split 3 321 .leaf .leaf) .leaf) .leaf)) (.split 2 64 (.split 3 326 (.split 2 62 .leaf .leaf) .leaf) .leaf)) .leaf) .leaf) .leaf))
private theorem clrrrlrlrrrlrrrrrlrrrllr : Excluded blrrrlrlrrrlrrrrrlrrrllr := fun _ h => reject tlrrrlrlrrrlrrrrrlrrrllr (by decide +kernel) h
private theorem clrrrlrlrrrlrrrrrlrrrll : Excluded blrrrlrlrrrlrrrrrlrrrll := bisect blrrrlrlrrrlrrrrrlrrrll 2 61 clrrrlrlrrrlrrrrrlrrrlll clrrrlrlrrrlrrrrrlrrrllr
private def blrrrlrlrrrlrrrrrlrrrlr : Box := right blrrrlrlrrrlrrrrrlrrrl 3 338
private def tlrrrlrlrrrlrrrrrlrrrlr : Tree := (.split 2 61 (.split 3 358 (.split 2 52 (.split 3 348 (.split 2 48 .leaf (.split 3 343 (.split 2 50 .leaf (.split 3 340 .leaf (.split 2 51 .leaf (.split 3 341 .leaf (.split 3 342 .leaf .leaf))))) (.split 2 50 (.split 3 345 .leaf (.split 2 49 .leaf (.split 3 346 .leaf (.split 3 347 .leaf .leaf)))) (.split 3 345 (.split 2 51 (.split 3 344 .leaf .leaf) .leaf) .leaf)))) (.split 2 48 (.split 3 353 (.split 2 46 .leaf (.split 3 350 .leaf (.split 2 47 .leaf (.split 3 351 .leaf (.split 3 352 .leaf .leaf))))) (.split 2 46 .leaf (.split 3 355 (.split 2 47 .leaf .leaf) .leaf))) (.split 3 353 (.split 2 50 (.split 3 350 (.split 2 49 (.split 3 349 .leaf .leaf) .leaf) .leaf) .leaf) .leaf))) (.split 3 348 (.split 2 56 (.split 3 343 (.split 2 54 (.split 3 340 (.split 2 53 .leaf .leaf) .leaf) .leaf) .leaf) .leaf) .leaf)) (.split 2 52 (.split 3 369 (.split 2 48 .leaf .leaf) .leaf) .leaf)) .leaf)
private theorem clrrrlrlrrrlrrrrrlrrrlr : Excluded blrrrlrlrrrlrrrrrlrrrlr := fun _ h => reject tlrrrlrlrrrlrrrrrlrrrlr (by decide +kernel) h
private theorem clrrrlrlrrrlrrrrrlrrrl : Excluded blrrrlrlrrrlrrrrrlrrrl := bisect blrrrlrlrrrlrrrrrlrrrl 3 338 clrrrlrlrrrlrrrrrlrrrll clrrrlrlrrrlrrrrrlrrrlr
private def blrrrlrlrrrlrrrrrlrrrr : Box := right blrrrlrlrrrlrrrrrlrrr 2 93
private def tlrrrlrlrrrlrrrrrlrrrr : Tree := .leaf
private theorem clrrrlrlrrrlrrrrrlrrrr : Excluded blrrrlrlrrrlrrrrrlrrrr := fun _ h => reject tlrrrlrlrrrlrrrrrlrrrr (by decide +kernel) h
private theorem clrrrlrlrrrlrrrrrlrrr : Excluded blrrrlrlrrrlrrrrrlrrr := bisect blrrrlrlrrrlrrrrrlrrr 2 93 clrrrlrlrrrlrrrrrlrrrl clrrrlrlrrrlrrrrrlrrrr
private theorem clrrrlrlrrrlrrrrrlrr : Excluded blrrrlrlrrrlrrrrrlrr := bisect blrrrlrlrrrlrrrrrlrr 3 304 clrrrlrlrrrlrrrrrlrrl clrrrlrlrrrlrrrrrlrrr
private theorem clrrrlrlrrrlrrrrrlr : Excluded blrrrlrlrrrlrrrrrlr := bisect blrrrlrlrrrlrrrrrlr 2 45 clrrrlrlrrrlrrrrrlrl clrrrlrlrrrlrrrrrlrr
private theorem clrrrlrlrrrlrrrrrl : Excluded blrrrlrlrrrlrrrrrl := bisect blrrrlrlrrrlrrrrrl 3 253 clrrrlrlrrrlrrrrrll clrrrlrlrrrlrrrrrlr
private def blrrrlrlrrrlrrrrrr : Box := right blrrrlrlrrrlrrrrr 3 381
private def blrrrlrlrrrlrrrrrrl : Box := left blrrrlrlrrrlrrrrrr 3 765
private def blrrrlrlrrrlrrrrrrll : Box := left blrrrlrlrrrlrrrrrrl 2 45
private def blrrrlrlrrrlrrrrrrlll : Box := left blrrrlrlrrrlrrrrrrll 3 509
private def blrrrlrlrrrlrrrrrrllll : Box := left blrrrlrlrrrlrrrrrrlll 2 29
private def tlrrrlrlrrrlrrrrrrllll : Tree := (.split 3 436 .leaf (.split 2 25 .leaf (.split 3 470 (.split 2 27 .leaf (.split 3 452 .leaf (.split 3 461 .leaf (.split 2 28 .leaf (.split 3 465 .leaf (.split 3 467 (.split 3 466 .leaf .leaf) .leaf)))))) (.split 2 27 (.split 3 489 .leaf (.split 2 26 .leaf (.split 3 499 (.split 3 494 .leaf (.split 3 496 .leaf .leaf)) .leaf))) (.split 3 489 (.split 3 479 (.split 2 28 .leaf .leaf) (.split 2 28 (.split 3 484 (.split 3 481 (.split 3 480 .leaf .leaf) .leaf) .leaf) .leaf)) .leaf)))))
private theorem clrrrlrlrrrlrrrrrrllll : Excluded blrrrlrlrrrlrrrrrrllll := fun _ h => reject tlrrrlrlrrrlrrrrrrllll (by decide +kernel) h
private def blrrrlrlrrrlrrrrrrlllr : Box := right blrrrlrlrrrlrrrrrrlll 2 29
private def tlrrrlrlrrrlrrrrrrlllr : Tree := (.split 3 436 (.split 2 36 (.split 3 407 (.split 2 32 .leaf (.split 3 394 .leaf (.split 2 34 .leaf (.split 3 400 .leaf (.split 2 35 .leaf (.split 3 403 (.split 3 401 .leaf (.split 3 402 .leaf .leaf)) .leaf)))))) (.split 2 32 (.split 3 421 .leaf (.split 2 30 .leaf (.split 3 428 .leaf (.split 2 31 .leaf (.split 3 432 .leaf (.split 3 434 (.split 3 433 .leaf .leaf) .leaf)))))) (.split 3 421 (.split 2 34 (.split 3 414 .leaf (.split 2 33 .leaf (.split 3 417 (.split 3 415 .leaf (.split 3 416 .leaf .leaf)) .leaf))) (.split 3 414 (.split 2 35 (.split 3 410 (.split 3 408 .leaf .leaf) .leaf) .leaf) .leaf)) (.split 2 34 (.split 3 428 (.split 2 33 (.split 3 424 .leaf .leaf) .leaf) .leaf) .leaf)))) (.split 3 407 (.split 2 40 (.split 3 394 (.split 2 38 (.split 3 387 .leaf (.split 2 37 .leaf (.split 3 390 .leaf .leaf))) (.split 3 387 (.split 2 39 (.split 3 384 .leaf (.split 3 385 .leaf .leaf)) .leaf) .leaf)) (.split 2 38 (.split 3 400 (.split 2 37 (.split 3 397 (.split 3 395 .leaf (.split 3 396 .leaf .leaf)) .leaf) .leaf) .leaf) .leaf)) .leaf) .leaf)) (.split 2 36 (.split 3 470 (.split 2 32 (.split 3 452 (.split 2 30 .leaf (.split 3 444 (.split 2 31 (.split 3 440 .leaf (.split 3 442 .leaf .leaf)) .leaf) .leaf)) (.split 2 30 (.split 3 461 (.split 3 456 (.split 3 454 (.split 3 453 .leaf .leaf) .leaf) .leaf) .leaf) .leaf)) .leaf) .leaf) .leaf))
private theorem clrrrlrlrrrlrrrrrrlllr : Excluded blrrrlrlrrrlrrrrrrlllr := fun _ h => reject tlrrrlrlrrrlrrrrrrlllr (by decide +kernel) h
private theorem clrrrlrlrrrlrrrrrrlll : Excluded blrrrlrlrrrlrrrrrrlll := bisect blrrrlrlrrrlrrrrrrlll 2 29 clrrrlrlrrrlrrrrrrllll clrrrlrlrrrlrrrrrrlllr
private def blrrrlrlrrrlrrrrrrllr : Box := right blrrrlrlrrrlrrrrrrll 3 509
private def tlrrrlrlrrrlrrrrrrllr : Tree := (.split 2 29 (.split 3 612 (.split 2 25 (.split 3 556 (.split 2 23 .leaf (.split 3 532 .leaf (.split 2 24 .leaf (.split 3 544 (.split 3 538 (.split 3 535 .leaf (.split 3 536 .leaf .leaf)) .leaf) .leaf)))) (.split 2 23 (.split 3 583 .leaf (.split 2 22 .leaf (.split 3 597 (.split 3 590 .leaf (.split 3 593 (.split 3 591 .leaf (.split 3 592 .leaf .leaf)) .leaf)) .leaf))) (.split 3 583 (.split 2 24 (.split 3 569 (.split 3 562 (.split 3 559 .leaf (.split 3 560 .leaf (.split 3 561 .leaf .leaf))) .leaf) .leaf) .leaf) .leaf))) (.split 3 556 (.split 2 27 (.split 3 532 (.split 3 520 (.split 2 26 (.split 3 514 .leaf .leaf) .leaf) .leaf) .leaf) .leaf) .leaf)) (.split 2 25 (.split 3 680 (.split 2 23 (.split 3 644 (.split 2 22 (.split 3 628 .leaf (.split 3 636 (.split 3 632 (.split 3 630 (.split 3 629 .leaf .leaf) .leaf) .leaf) .leaf)) .leaf) .leaf) .leaf) .leaf) .leaf)) .leaf)
private theorem clrrrlrlrrrlrrrrrrllr : Excluded blrrrlrlrrrlrrrrrrllr := fun _ h => reject tlrrrlrlrrrlrrrrrrllr (by decide +kernel) h
private theorem clrrrlrlrrrlrrrrrrll : Excluded blrrrlrlrrrlrrrrrrll := bisect blrrrlrlrrrlrrrrrrll 3 509 clrrrlrlrrrlrrrrrrlll clrrrlrlrrrlrrrrrrllr
private def blrrrlrlrrrlrrrrrrlr : Box := right blrrrlrlrrrlrrrrrrl 2 45
private def tlrrrlrlrrrlrrrrrrlr : Tree := .leaf
private theorem clrrrlrlrrrlrrrrrrlr : Excluded blrrrlrlrrrlrrrrrrlr := fun _ h => reject tlrrrlrlrrrlrrrrrrlr (by decide +kernel) h
private theorem clrrrlrlrrrlrrrrrrl : Excluded blrrrlrlrrrlrrrrrrl := bisect blrrrlrlrrrlrrrrrrl 2 45 clrrrlrlrrrlrrrrrrll clrrrlrlrrrlrrrrrrlr
private def blrrrlrlrrrlrrrrrrr : Box := right blrrrlrlrrrlrrrrrr 3 765
private def tlrrrlrlrrrlrrrrrrr : Tree := .leaf
private theorem clrrrlrlrrrlrrrrrrr : Excluded blrrrlrlrrrlrrrrrrr := fun _ h => reject tlrrrlrlrrrlrrrrrrr (by decide +kernel) h
private theorem clrrrlrlrrrlrrrrrr : Excluded blrrrlrlrrrlrrrrrr := bisect blrrrlrlrrrlrrrrrr 3 765 clrrrlrlrrrlrrrrrrl clrrrlrlrrrlrrrrrrr
private theorem clrrrlrlrrrlrrrrr : Excluded blrrrlrlrrrlrrrrr := bisect blrrrlrlrrrlrrrrr 3 381 clrrrlrlrrrlrrrrrl clrrrlrlrrrlrrrrrr
private theorem clrrrlrlrrrlrrrr : Excluded blrrrlrlrrrlrrrr := bisect blrrrlrlrrrlrrrr 2 21 clrrrlrlrrrlrrrrl clrrrlrlrrrlrrrrr
private theorem clrrrlrlrrrlrrr : Excluded blrrrlrlrrrlrrr := bisect blrrrlrlrrrlrrr 1 6 clrrrlrlrrrlrrrl clrrrlrlrrrlrrrr
private theorem clrrrlrlrrrlrr : Excluded blrrrlrlrrrlrr := bisect blrrrlrlrrrlrr 3 189 clrrrlrlrrrlrrl clrrrlrlrrrlrrr
private theorem clrrrlrlrrrlr : Excluded blrrrlrlrrrlr := bisect blrrrlrlrrrlr 2 9 clrrrlrlrrrlrl clrrrlrlrrrlrr
private theorem clrrrlrlrrrl : Excluded blrrrlrlrrrl := bisect blrrrlrlrrrl 3 93 clrrrlrlrrrll clrrrlrlrrrlr
private def blrrrlrlrrrr : Box := right blrrrlrlrrr 1 7
private def tlrrrlrlrrrr : Tree := .leaf
private theorem clrrrlrlrrrr : Excluded blrrrlrlrrrr := fun _ h => reject tlrrrlrlrrrr (by decide +kernel) h
private theorem clrrrlrlrrr : Excluded blrrrlrlrrr := bisect blrrrlrlrrr 1 7 clrrrlrlrrrl clrrrlrlrrrr
private theorem clrrrlrlrr : Excluded blrrrlrlrr := bisect blrrrlrlrr 3 45 clrrrlrlrrl clrrrlrlrrr
private theorem clrrrlrlr : Excluded blrrrlrlr := bisect blrrrlrlr 2 3 clrrrlrlrl clrrrlrlrr
private theorem clrrrlrl : Excluded blrrrlrl := bisect blrrrlrl 1 5 clrrrlrll clrrrlrlr
private def blrrrlrr : Box := right blrrrlr 0 2
private def tlrrrlrr : Tree := .leaf
private theorem clrrrlrr : Excluded blrrrlrr := fun _ h => reject tlrrrlrr (by decide +kernel) h
private theorem clrrrlr : Excluded blrrrlr := bisect blrrrlr 0 2 clrrrlrl clrrrlrr
private theorem clrrrl : Excluded blrrrl := bisect blrrrl 3 21 clrrrll clrrrlr
private def blrrrr : Box := right blrrr 1 9
private def tlrrrr : Tree := .leaf
private theorem clrrrr : Excluded blrrrr := fun _ h => reject tlrrrr (by decide +kernel) h
private theorem clrrr : Excluded blrrr := bisect blrrr 1 9 clrrrl clrrrr
private theorem clrr : Excluded blrr := bisect blrr 0 1 clrrl clrrr
private theorem clr : Excluded blr := bisect blr 3 9 clrl clrr
private theorem cl : Excluded bl := bisect bl 1 3 cll clr
private def br : Box := right domain 0 3
private def brl : Box := left br 3 9
private def trl : Tree := (.split 1 3 (.split 0 9 (.split 2 3 (.split 1 1 .leaf .leaf) .leaf) .leaf) .leaf)
private theorem crl : Excluded brl := fun _ h => reject trl (by decide +kernel) h
private def brr : Box := right br 3 9
private def brrl : Box := left brr 1 3
private def brrll : Box := left brrl 0 9
private def brrlll : Box := left brrll 1 1
private def brrllll : Box := left brrlll 0 5
private def brrlllll : Box := left brrllll 2 3
private def trrlllll : Tree := (.split 3 21 (.split 2 1 .leaf (.split 0 4 .leaf .leaf)) (.split 0 4 (.split 2 1 .leaf (.split 3 45 (.split 3 29 (.split 2 2 .leaf (.split 3 25 .leaf (.split 3 27 .leaf .leaf))) (.split 2 2 (.split 3 36 .leaf (.split 3 40 .leaf (.split 3 42 (.split 3 41 .leaf .leaf) .leaf))) .leaf)) (.split 3 93 (.split 2 2 .leaf .leaf) .leaf))) .leaf))
private theorem crrlllll : Excluded brrlllll := fun _ h => reject trrlllll (by decide +kernel) h
private def brrllllr : Box := right brrllll 2 3
private def brrllllrl : Box := left brrllllr 3 21
private def trrllllrl : Tree := (.split 3 13 .leaf (.split 2 9 (.split 0 4 (.split 3 16 .leaf (.split 2 5 .leaf (.split 3 18 .leaf (.split 2 7 (.split 3 19 .leaf (.split 2 6 (.split 3 20 .leaf .leaf) (.split 3 20 .leaf .leaf))) (.split 3 19 .leaf (.split 3 20 .leaf .leaf)))))) .leaf) (.split 0 4 (.split 3 16 (.split 2 21 .leaf .leaf) (.split 2 21 (.split 3 18 (.split 2 13 .leaf (.split 2 16 .leaf (.split 3 17 .leaf .leaf))) (.split 2 13 (.split 3 19 (.split 2 11 (.split 2 10 .leaf .leaf) .leaf) .leaf) .leaf)) (.split 3 18 (.split 2 45 (.split 2 29 (.split 3 17 .leaf .leaf) (.split 3 17 .leaf .leaf)) (.split 2 93 (.split 3 17 (.split 2 61 .leaf (.split 2 74 .leaf .leaf)) .leaf) (.split 3 17 (.split 2 189 (.split 2 125 (.split 2 107 .leaf (.split 2 115 .leaf (.split 2 120 .leaf (.split 2 122 .leaf (.split 2 123 .leaf .leaf))))) (.split 2 151 (.split 2 137 (.split 2 131 (.split 2 128 (.split 2 126 .leaf (.split 2 127 .leaf .leaf)) .leaf) .leaf) .leaf) .leaf)) (.split 2 381 .leaf .leaf)) .leaf))) .leaf))) .leaf)))
private theorem crrllllrl : Excluded brrllllrl := fun _ h => reject trrllllrl (by decide +kernel) h
private def brrllllrr : Box := right brrllllr 3 21
private def brrllllrrl : Box := left brrllllrr 3 45
private def trrllllrrl : Tree := (.split 0 4 (.split 2 9 (.split 3 29 (.split 2 5 (.split 3 25 (.split 2 4 (.split 3 23 .leaf .leaf) (.split 3 23 (.split 3 22 .leaf .leaf) .leaf)) .leaf) (.split 3 25 (.split 2 7 .leaf .leaf) .leaf)) .leaf) .leaf) (.split 2 9 .leaf (.split 3 29 .leaf (.split 2 21 .leaf (.split 3 36 .leaf (.split 2 45 (.split 3 40 .leaf (.split 2 29 .leaf (.split 3 42 .leaf (.split 2 36 (.split 3 43 .leaf (.split 2 32 .leaf (.split 3 44 .leaf .leaf))) (.split 3 43 .leaf (.split 2 40 (.split 3 44 .leaf .leaf) (.split 3 44 .leaf .leaf))))))) (.split 3 40 (.split 2 93 .leaf (.split 3 38 .leaf (.split 2 189 .leaf .leaf))) (.split 2 93 (.split 3 42 (.split 2 61 .leaf (.split 2 74 .leaf (.split 3 41 .leaf .leaf))) (.split 2 61 (.split 3 43 (.split 2 52 .leaf (.split 2 56 .leaf (.split 2 58 (.split 2 57 .leaf .leaf) .leaf))) .leaf) (.split 3 43 (.split 2 74 .leaf .leaf) .leaf))) (.split 3 42 (.split 2 189 (.split 2 125 (.split 3 41 .leaf .leaf) (.split 3 41 .leaf .leaf)) (.split 2 381 (.split 3 41 (.split 2 253 (.split 2 217 .leaf (.split 2 234 .leaf (.split 2 243 (.split 2 238 .leaf (.split 2 240 .leaf (.split 2 241 .leaf (.split 2 242 .leaf .leaf)))) (.split 2 248 .leaf .leaf)))) (.split 2 304 .leaf .leaf)) .leaf) .leaf)) .leaf)))))))))
private theorem crrllllrrl : Excluded brrllllrrl := fun _ h => reject trrllllrrl (by decide +kernel) h
private def brrllllrrr : Box := right brrllllrr 3 45
private def brrllllrrrl : Box := left brrllllrrr 0 4
private def trrllllrrrl : Tree := .leaf
private theorem crrllllrrrl : Excluded brrllllrrrl := fun _ h => reject trrllllrrrl (by decide +kernel) h
private def brrllllrrrr : Box := right brrllllrrr 0 4
private def brrllllrrrrl : Box := left brrllllrrrr 2 9
private def trrllllrrrrl : Tree := (.split 3 93 (.split 2 5 .leaf (.split 3 61 .leaf (.split 2 7 (.split 3 74 .leaf (.split 3 83 (.split 2 6 .leaf (.split 3 78 .leaf (.split 3 80 (.split 3 79 .leaf .leaf) .leaf))) (.split 2 6 .leaf .leaf))) (.split 3 74 (.split 3 67 (.split 2 8 .leaf (.split 3 64 .leaf (.split 3 65 .leaf .leaf))) (.split 2 8 (.split 3 70 .leaf .leaf) .leaf)) .leaf)))) (.split 2 5 (.split 3 189 (.split 3 125 (.split 2 4 .leaf .leaf) (.split 2 4 .leaf (.split 3 151 (.split 3 137 (.split 3 131 (.split 3 128 .leaf .leaf) .leaf) .leaf) .leaf))) (.split 3 381 (.split 2 4 (.split 3 253 .leaf (.split 3 304 (.split 3 276 .leaf (.split 3 289 (.split 3 282 (.split 3 279 .leaf (.split 3 280 .leaf .leaf)) .leaf) .leaf)) .leaf)) .leaf) .leaf)) (.split 3 189 (.split 2 7 (.split 3 125 (.split 3 107 (.split 2 6 (.split 3 100 (.split 3 96 (.split 3 94 .leaf .leaf) .leaf) .leaf) .leaf) .leaf) .leaf) .leaf) .leaf)))
private theorem crrllllrrrrl : Excluded brrllllrrrrl := fun _ h => reject trrllllrrrrl (by decide +kernel) h
private def brrllllrrrrr : Box := right brrllllrrrr 2 9
private def trrllllrrrrr : Tree := (.split 3 93 (.split 2 21 (.split 3 61 (.split 2 13 (.split 3 52 .leaf (.split 2 11 (.split 3 56 .leaf (.split 3 58 .leaf (.split 2 10 .leaf .leaf))) (.split 3 56 (.split 3 54 .leaf (.split 2 12 .leaf .leaf)) .leaf))) (.split 3 52 (.split 2 16 (.split 3 48 .leaf (.split 3 50 .leaf (.split 2 14 .leaf (.split 2 15 .leaf (.split 3 51 .leaf .leaf))))) (.split 3 48 (.split 2 18 .leaf .leaf) (.split 2 18 (.split 3 50 (.split 3 49 .leaf .leaf) .leaf) (.split 3 50 (.split 2 19 (.split 3 49 .leaf .leaf) .leaf) .leaf)))) (.split 2 16 (.split 3 56 (.split 2 14 (.split 3 54 (.split 3 53 .leaf .leaf) .leaf) .leaf) .leaf) .leaf))) (.split 2 13 (.split 3 74 (.split 2 11 (.split 3 67 (.split 3 64 (.split 2 10 .leaf .leaf) .leaf) .leaf) .leaf) .leaf) .leaf)) (.split 3 61 (.split 2 45 (.split 3 52 (.split 2 29 (.split 3 48 (.split 2 25 (.split 3 46 .leaf (.split 2 23 (.split 3 47 .leaf .leaf) (.split 3 47 (.split 2 24 .leaf .leaf) .leaf))) (.split 3 46 .leaf .leaf)) .leaf) (.split 3 48 (.split 2 36 .leaf .leaf) .leaf)) .leaf) .leaf) .leaf)) .leaf)
private theorem crrllllrrrrr : Excluded brrllllrrrrr := fun _ h => reject trrllllrrrrr (by decide +kernel) h
private theorem crrllllrrrr : Excluded brrllllrrrr := bisect brrllllrrrr 2 9 crrllllrrrrl crrllllrrrrr
private theorem crrllllrrr : Excluded brrllllrrr := bisect brrllllrrr 0 4 crrllllrrrl crrllllrrrr
private theorem crrllllrr : Excluded brrllllrr := bisect brrllllrr 3 45 crrllllrrl crrllllrrr
private theorem crrllllr : Excluded brrllllr := bisect brrllllr 3 21 crrllllrl crrllllrr
private theorem crrllll : Excluded brrllll := bisect brrllll 2 3 crrlllll crrllllr
private def brrlllr : Box := right brrlll 0 5
private def trrlllr : Tree := .leaf
private theorem crrlllr : Excluded brrlllr := fun _ h => reject trrlllr (by decide +kernel) h
private theorem crrlll : Excluded brrlll := bisect brrlll 0 5 crrllll crrlllr
private def brrllr : Box := right brrll 1 1
private def trrllr : Tree := .leaf
private theorem crrllr : Excluded brrllr := fun _ h => reject trrllr (by decide +kernel) h
private theorem crrll : Excluded brrll := bisect brrll 1 1 crrlll crrllr
private def brrlr : Box := right brrl 0 9
private def trrlr : Tree := .leaf
private theorem crrlr : Excluded brrlr := fun _ h => reject trrlr (by decide +kernel) h
private theorem crrl : Excluded brrl := bisect brrl 0 9 crrll crrlr
private def brrr : Box := right brr 1 3
private def trrr : Tree := .leaf
private theorem crrr : Excluded brrr := fun _ h => reject trrr (by decide +kernel) h
private theorem crr : Excluded brr := bisect brr 1 3 crrl crrr
private theorem cr : Excluded br := bisect br 3 9 crl crr
theorem domain_excluded : Excluded domain := bisect domain 0 3 cl cr
end OMA.Moving245212

end

section

/- Even integers supported on 2, 3, and one arbitrary larger prime. -/
namespace OMA.Moving245212
open OMA.Smooth245212 Finset
open scoped ArithmeticFunction.sigma

theorem mixed_three {a b c q : ℕ} (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (hq : Nat.Prime q) (large : 3<q) :
    OeisA245212.a (2^a*3^b*q^c) ≠ (σ 1 (2^a*3^b*q^c):ℤ) := by
  let e : I → ℕ := ![a,b,c,q]
  let u : Fin 3 → ℕ := fun i => e i.castSucc
  have hp (i : Fin 3) : Nat.Prime (primes e i) := by
    fin_cases i <;> simp [primes,e,hq,Nat.prime_two,Nat.prime_three]
  have hinj : Function.Injective (primes e) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [primes,e]
    omega
  have he : total (primes e) u = 2^a*3^b*q^c := by
    simp [total,Fin.prod_univ_three,primes,u,e,mul_assoc]
  intro eq
  apply domain_excluded e _ hq
  · exact normalized_of_eq _ hp hinj _ (he ▸ eq)
  · intro i
    fin_cases i <;> simp [domain,e,Band.Contains] <;> omega

end OMA.Moving245212

end

section

/- Rational interval certificates generated by smooth_boxes_245212.py. -/
namespace OMA.Smooth245212
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def box23 : Box := ![⟨1,none⟩,⟨1,none⟩,⟨0,some 0⟩,⟨0,some 0⟩]
private def tree23 : Tree := (.split 0 3 (.split 0 1 (.split 1 3 (.split 1 1 .leaf (.split 1 2 .leaf .leaf)) (.split 1 9 (.split 1 5 .leaf .leaf) .leaf)) (.split 1 3 (.split 0 2 (.split 1 1 .leaf (.split 1 2 .leaf .leaf)) (.split 1 1 .leaf .leaf)) (.split 0 2 (.split 1 9 .leaf .leaf) .leaf))) (.split 1 3 (.split 0 9 (.split 1 1 .leaf .leaf) .leaf) .leaf))
theorem reject23 {e : I → ℕ} (h : ∀ i,(box23 i).Contains (e i)) : score e ≠ 2 :=
  tree23.sound (by decide +kernel) h

def box25 : Box := ![⟨1,none⟩,⟨0,some 0⟩,⟨1,none⟩,⟨0,some 0⟩]
private def tree25 : Tree := (.split 0 3 (.split 0 1 (.split 2 3 .leaf .leaf) (.split 0 2 (.split 2 3 (.split 2 1 .leaf .leaf) .leaf) (.split 2 3 (.split 2 1 .leaf .leaf) (.split 2 9 .leaf .leaf)))) (.split 0 9 (.split 0 5 (.split 0 4 (.split 2 3 (.split 2 1 .leaf (.split 2 2 .leaf .leaf)) (.split 2 9 (.split 2 5 (.split 2 4 .leaf .leaf) (.split 2 7 .leaf .leaf)) (.split 2 21 (.split 2 13 .leaf .leaf) (.split 2 45 .leaf .leaf)))) (.split 2 3 (.split 2 1 .leaf .leaf) (.split 2 9 .leaf .leaf))) (.split 2 3 (.split 2 1 .leaf .leaf) .leaf)) .leaf))
theorem reject25 {e : I → ℕ} (h : ∀ i,(box25 i).Contains (e i)) : score e ≠ 2 :=
  tree25.sound (by decide +kernel) h

def box27 : Box := ![⟨1,none⟩,⟨0,some 0⟩,⟨0,some 0⟩,⟨1,none⟩]
private def tree27 : Tree := (.split 0 3 (.split 0 1 .leaf (.split 3 3 (.split 3 1 .leaf .leaf) .leaf)) (.split 0 9 (.split 0 5 (.split 0 4 (.split 3 3 (.split 3 1 .leaf .leaf) .leaf) (.split 3 3 (.split 3 1 .leaf .leaf) (.split 3 9 .leaf .leaf))) (.split 0 7 (.split 0 6 (.split 3 3 (.split 3 1 .leaf (.split 3 2 .leaf .leaf)) (.split 3 9 (.split 3 5 (.split 3 4 .leaf .leaf) (.split 3 7 (.split 3 6 .leaf .leaf) (.split 3 8 .leaf .leaf))) (.split 3 21 (.split 3 13 (.split 3 11 (.split 3 10 .leaf .leaf) .leaf) (.split 3 16 (.split 3 14 .leaf .leaf) (.split 3 18 .leaf .leaf))) (.split 3 45 (.split 3 29 (.split 3 25 .leaf .leaf) (.split 3 36 .leaf .leaf)) (.split 3 93 (.split 3 61 .leaf .leaf) (.split 3 189 .leaf .leaf)))))) (.split 3 3 (.split 3 1 .leaf .leaf) (.split 3 9 .leaf .leaf))) (.split 3 3 (.split 3 1 .leaf .leaf) .leaf))) (.split 0 21 (.split 3 3 (.split 0 13 (.split 3 1 .leaf .leaf) .leaf) .leaf) .leaf)))
theorem reject27 {e : I → ℕ} (h : ∀ i,(box27 i).Contains (e i)) : score e ≠ 2 :=
  tree27.sound (by decide +kernel) h

def box235 : Box := ![⟨1,none⟩,⟨1,none⟩,⟨1,none⟩,⟨0,some 0⟩]
private def tree235 : Tree := (.split 0 3 (.split 1 3 (.split 0 1 (.split 1 1 (.split 2 3 (.split 2 1 .leaf .leaf) .leaf) (.split 1 2 (.split 2 3 (.split 2 1 .leaf .leaf) (.split 2 9 (.split 2 5 .leaf .leaf) (.split 2 21 .leaf .leaf))) (.split 2 3 (.split 2 1 .leaf (.split 2 2 .leaf .leaf)) (.split 2 9 (.split 2 5 .leaf .leaf) .leaf)))) (.split 1 1 (.split 0 2 (.split 2 3 (.split 2 1 .leaf .leaf) (.split 2 9 .leaf .leaf)) (.split 2 3 .leaf .leaf)) (.split 2 3 .leaf .leaf))) (.split 0 1 (.split 2 3 (.split 1 9 (.split 2 1 (.split 1 5 (.split 1 4 .leaf .leaf) (.split 1 7 (.split 1 6 .leaf .leaf) .leaf)) (.split 1 5 (.split 2 2 .leaf .leaf) .leaf)) (.split 2 1 (.split 1 21 (.split 1 13 .leaf .leaf) .leaf) .leaf)) .leaf) .leaf)) .leaf)
theorem reject235 {e : I → ℕ} (h : ∀ i,(box235 i).Contains (e i)) : score e ≠ 2 :=
  tree235.sound (by decide +kernel) h

def box237 : Box := ![⟨1,none⟩,⟨1,none⟩,⟨0,some 0⟩,⟨1,none⟩]
private def tree237 : Tree := (.split 0 3 (.split 1 3 (.split 0 1 (.split 1 1 .leaf (.split 1 2 (.split 3 3 .leaf .leaf) (.split 3 3 .leaf .leaf))) (.split 1 1 (.split 0 2 (.split 3 3 (.split 3 1 .leaf .leaf) (.split 3 9 .leaf .leaf)) (.split 3 3 .leaf .leaf)) (.split 0 2 (.split 1 2 (.split 3 3 (.split 3 1 .leaf .leaf) .leaf) (.split 3 3 .leaf .leaf)) .leaf))) (.split 0 1 (.split 1 9 (.split 1 5 (.split 3 3 (.split 3 1 .leaf (.split 1 4 .leaf .leaf)) (.split 1 4 (.split 3 9 .leaf .leaf) (.split 3 9 (.split 3 5 .leaf (.split 3 7 .leaf .leaf)) (.split 3 21 (.split 3 13 (.split 3 11 .leaf .leaf) (.split 3 16 (.split 3 14 .leaf .leaf) (.split 3 18 (.split 3 17 .leaf .leaf) (.split 3 19 .leaf (.split 3 20 .leaf .leaf))))) (.split 3 45 (.split 3 29 (.split 3 25 (.split 3 23 .leaf .leaf) .leaf) (.split 3 36 .leaf .leaf)) (.split 3 93 .leaf .leaf)))))) (.split 3 3 (.split 3 1 (.split 1 7 .leaf .leaf) (.split 1 7 (.split 3 2 .leaf (.split 1 6 .leaf .leaf)) (.split 3 2 (.split 1 8 .leaf .leaf) .leaf))) (.split 1 7 (.split 3 9 (.split 3 5 (.split 1 6 (.split 3 4 .leaf .leaf) .leaf) (.split 1 6 .leaf .leaf)) .leaf) (.split 3 9 .leaf .leaf)))) (.split 3 3 (.split 3 1 (.split 1 21 (.split 1 13 .leaf (.split 1 16 .leaf .leaf)) (.split 1 45 (.split 1 29 (.split 1 25 .leaf .leaf) (.split 1 36 (.split 1 32 .leaf (.split 1 34 .leaf .leaf)) (.split 1 40 (.split 1 38 (.split 1 37 .leaf .leaf) (.split 1 39 .leaf .leaf)) (.split 1 42 (.split 1 41 .leaf .leaf) .leaf)))) (.split 1 93 (.split 1 61 (.split 1 52 (.split 1 48 .leaf .leaf) .leaf) (.split 1 74 .leaf .leaf)) (.split 1 189 .leaf .leaf)))) (.split 1 21 (.split 1 13 (.split 3 2 .leaf .leaf) .leaf) .leaf)) .leaf)) .leaf)) .leaf)
theorem reject237 {e : I → ℕ} (h : ∀ i,(box237 i).Contains (e i)) : score e ≠ 2 :=
  tree237.sound (by decide +kernel) h

def box257 : Box := ![⟨1,none⟩,⟨0,some 0⟩,⟨1,none⟩,⟨1,none⟩]
private def tree257 : Tree := (.split 0 3 (.split 0 1 (.split 2 3 .leaf .leaf) (.split 2 3 (.split 0 2 (.split 2 1 (.split 3 3 .leaf .leaf) (.split 3 3 .leaf .leaf)) (.split 2 1 (.split 3 3 (.split 3 1 .leaf .leaf) (.split 3 9 .leaf .leaf)) (.split 3 3 (.split 3 1 (.split 2 2 .leaf .leaf) (.split 2 2 (.split 3 2 .leaf .leaf) .leaf)) (.split 2 2 (.split 3 9 .leaf .leaf) .leaf)))) (.split 3 3 (.split 0 2 (.split 3 1 .leaf (.split 2 9 .leaf (.split 3 2 .leaf .leaf))) (.split 3 1 (.split 2 9 (.split 2 5 .leaf .leaf) .leaf) .leaf)) (.split 0 2 (.split 2 9 (.split 2 5 (.split 3 9 .leaf .leaf) (.split 3 9 (.split 3 5 .leaf .leaf) (.split 3 21 (.split 2 7 .leaf (.split 3 13 .leaf (.split 3 16 (.split 2 8 .leaf (.split 3 14 .leaf .leaf)) (.split 2 8 .leaf (.split 3 18 .leaf .leaf))))) (.split 2 7 (.split 3 45 .leaf (.split 2 6 .leaf (.split 3 93 (.split 3 61 .leaf .leaf) (.split 3 189 (.split 3 125 .leaf (.split 3 151 (.split 3 137 .leaf .leaf) (.split 3 168 (.split 3 159 (.split 3 155 .leaf (.split 3 157 .leaf .leaf)) (.split 3 163 (.split 3 161 (.split 3 160 .leaf .leaf) .leaf) .leaf)) .leaf))) (.split 3 381 (.split 3 253 .leaf .leaf) .leaf))))) (.split 3 45 (.split 2 8 (.split 3 29 (.split 3 25 .leaf (.split 3 27 (.split 3 26 .leaf .leaf) .leaf)) (.split 3 36 .leaf .leaf)) .leaf) .leaf))))) (.split 3 9 (.split 2 21 (.split 3 5 (.split 2 13 .leaf .leaf) (.split 2 13 (.split 3 7 .leaf (.split 2 11 .leaf (.split 3 8 .leaf (.split 2 12 .leaf .leaf)))) (.split 3 7 (.split 2 16 (.split 3 6 .leaf (.split 2 14 .leaf .leaf)) (.split 3 6 (.split 2 18 .leaf .leaf) (.split 2 18 .leaf .leaf))) (.split 2 16 (.split 2 14 (.split 3 8 .leaf .leaf) .leaf) .leaf)))) (.split 3 5 (.split 2 45 (.split 3 4 .leaf (.split 2 29 .leaf (.split 2 36 .leaf (.split 2 40 (.split 2 38 .leaf .leaf) (.split 2 42 (.split 2 41 .leaf .leaf) .leaf))))) (.split 3 4 (.split 2 93 .leaf .leaf) (.split 2 93 (.split 2 61 .leaf .leaf) .leaf))) (.split 2 45 (.split 3 7 (.split 2 29 (.split 3 6 (.split 2 25 (.split 2 23 (.split 2 22 .leaf .leaf) .leaf) .leaf) .leaf) .leaf) .leaf) .leaf))) (.split 2 21 (.split 3 21 (.split 2 13 (.split 3 13 (.split 2 11 (.split 3 11 (.split 2 10 .leaf (.split 3 10 .leaf .leaf)) (.split 2 10 (.split 3 12 .leaf .leaf) .leaf)) (.split 3 11 .leaf .leaf)) (.split 2 11 (.split 3 16 .leaf .leaf) .leaf)) .leaf) .leaf) .leaf))) .leaf)))) (.split 0 9 (.split 2 3 (.split 0 5 (.split 2 1 (.split 0 4 (.split 3 3 (.split 3 1 .leaf .leaf) .leaf) (.split 3 3 .leaf .leaf)) (.split 3 3 .leaf .leaf)) .leaf) .leaf) .leaf))
theorem reject257 {e : I → ℕ} (h : ∀ i,(box257 i).Contains (e i)) : score e ≠ 2 :=
  tree257.sound (by decide +kernel) h

def box2357 : Box := ![⟨1,none⟩,⟨1,none⟩,⟨1,none⟩,⟨1,none⟩]
private def tree2357 : Tree := (.split 0 3 (.split 1 3 (.split 0 1 (.split 2 3 (.split 1 1 (.split 2 1 (.split 3 3 .leaf .leaf) (.split 3 3 (.split 3 1 .leaf .leaf) (.split 2 2 .leaf (.split 3 9 .leaf (.split 3 21 .leaf (.split 3 45 .leaf .leaf)))))) (.split 2 1 (.split 1 2 (.split 3 3 (.split 3 1 .leaf (.split 3 2 .leaf .leaf)) (.split 3 9 (.split 3 5 (.split 3 4 .leaf .leaf) (.split 3 7 .leaf .leaf)) (.split 3 21 .leaf .leaf))) (.split 3 3 (.split 3 1 .leaf .leaf) .leaf)) (.split 3 3 (.split 1 2 (.split 3 1 (.split 2 2 .leaf .leaf) .leaf) .leaf) .leaf))) (.split 1 1 (.split 3 3 (.split 3 1 (.split 2 9 .leaf .leaf) (.split 2 9 (.split 2 5 (.split 3 2 .leaf .leaf) (.split 3 2 .leaf (.split 2 7 (.split 2 6 .leaf .leaf) (.split 2 8 .leaf .leaf)))) (.split 2 21 (.split 3 2 (.split 2 13 .leaf (.split 2 16 .leaf .leaf)) .leaf) (.split 3 2 (.split 2 45 (.split 2 29 (.split 2 25 (.split 2 23 .leaf .leaf) (.split 2 27 .leaf (.split 2 28 .leaf .leaf))) (.split 2 36 (.split 2 32 .leaf .leaf) .leaf)) (.split 2 93 .leaf .leaf)) .leaf)))) (.split 2 9 (.split 3 9 (.split 2 5 (.split 3 5 (.split 2 4 .leaf (.split 3 4 .leaf .leaf)) (.split 2 4 (.split 3 7 .leaf (.split 3 8 .leaf .leaf)) .leaf)) (.split 3 5 (.split 2 7 (.split 3 4 .leaf .leaf) .leaf) .leaf)) (.split 2 5 (.split 3 21 (.split 2 4 (.split 3 13 .leaf .leaf) .leaf) .leaf) .leaf)) .leaf)) .leaf)) (.split 2 3 (.split 1 1 (.split 0 2 (.split 2 1 (.split 3 3 .leaf .leaf) .leaf) .leaf) .leaf) .leaf)) (.split 0 1 (.split 2 3 (.split 1 9 (.split 3 3 (.split 2 1 .leaf .leaf) .leaf) .leaf) .leaf) .leaf)) .leaf)
theorem reject2357 {e : I → ℕ} (h : ∀ i,(box2357 i).Contains (e i)) : score e ≠ 2 :=
  tree2357.sound (by decide +kernel) h

end OMA.Smooth245212

end

section

/- No even number with nontrivial odd part supported on 3,5,7 is an
extra equality in A245212. All four exponents are unrestricted above. -/
namespace OMA.Smooth245212
open scoped ArithmeticFunction.sigma

theorem mixed {a b c d : ℕ} (ha : 0<a) (oddpart : 0<b+c+d) :
    OeisA245212.a (2^a*3^b*5^c*7^d) ≠ (σ 1 (2^a*3^b*5^c*7^d) : ℤ) := by
  let e : I → ℕ := ![a,b,c,d]
  have value : number e = 2^a*3^b*5^c*7^d := by
    simp [number,Fin.prod_univ_four,prime,e]
  intro eq
  have h := score_of_eq e (value ▸ eq)
  rcases Nat.eq_zero_or_pos b with hb|hb <;> rcases Nat.eq_zero_or_pos c with hc|hc <;>
      rcases Nat.eq_zero_or_pos d with hd|hd
  · omega
  · apply reject27 (e:=e) _ h; intro i; fin_cases i <;> simp [box27,Band.Contains,e] <;> omega
  · apply reject25 (e:=e) _ h; intro i; fin_cases i <;> simp [box25,Band.Contains,e] <;> omega
  · apply reject257 (e:=e) _ h; intro i; fin_cases i <;> simp [box257,Band.Contains,e] <;> omega
  · apply reject23 (e:=e) _ h; intro i; fin_cases i <;> simp [box23,Band.Contains,e] <;> omega
  · apply reject237 (e:=e) _ h; intro i; fin_cases i <;> simp [box237,Band.Contains,e] <;> omega
  · apply reject235 (e:=e) _ h; intro i; fin_cases i <;> simp [box235,Band.Contains,e] <;> omega
  · apply reject2357 (e:=e) _ h; intro i; fin_cases i <;> simp [box2357,Band.Contains,e] <;> omega

end OMA.Smooth245212

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

/-- The first two positive dyadic exponents have no solutions on two distinct
odd primes. The primes and both odd exponents are unrestricted. -/
theorem no_two_small_k {k p q e f : ℕ} (lo : 0<k) (hi : k≤2) (hp : p.Prime)
    (hq : q.Prime) (po : 2<p) (pq : p<q) (ep : 0<e) (fp : 0<f) :
    OeisA245212.a (2^k*p^e*q^f)≠(σ 1 (2^k*p^e*q^f):ℤ) := by
  by_cases h3 : p=3
  · subst p; exact OMA.Moving245212.mixed_three lo ep fp hq pq
  have p5 : 5≤p := by by_contra! h; interval_cases p <;> norm_num at *
  have q7 : 7≤q := by by_contra! h; interval_cases q <;> norm_num at * <;> omega
  by_cases pair : p=5 ∧ q=7
  · obtain ⟨rfl,rfl⟩ := pair
    simpa using OMA.Smooth245212.mixed (a:=k) (b:=0) (c:=e) (d:=f) lo (by omega)
  by_cases p7 : 7≤p
  · interval_cases k <;> apply pair_small hp hq po pq ep (u:=7) (v:=7) (by decide) (by decide) p7 q7 <;> decide +kernel
  · have pval : p=5 := by interval_cases p <;> norm_num at *
    have q11 : 11≤q := by by_contra! h; interval_cases q <;> norm_num at * <;> omega
    interval_cases k <;> apply pair_small hp hq po pq ep (u:=5) (v:=11) (by decide) (by decide) p5 q11 <;> decide +kernel

#print axioms no_two_small_k
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

/- A computable finite search at each dyadic exponent for two unrestricted
odd primes. No divisor-count or exponent pattern has to be fixed. -/
namespace OMA.PairHeight245212
open Nat Finset ArithmeticFunction OMA.Smooth245212 OMA.OddFaces245212
open scoped ArithmeticFunction.sigma
open OMA.FixedExponents245212 (y_pos)

private theorem scaledX (p : ℕ) (hp : 1<p) (e : Option ℕ) :
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

private theorem small_exp {A T u v p q e f : ℕ} (up : 0<u) (vp : 0<v)
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

#print axioms atom

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

#print axioms box

private theorem count_le (h : ℕ) : h.divisors.card≤h := by
  have inc : h.divisors⊆Icc 1 h := by
    intro d hd
    exact mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,Nat.le_of_dvd (Nat.pos_of_ne_zero (mem_divisors.mp hd).2)
      (dvd_of_mem_divisors hd)⟩
  simpa using Finset.card_le_card inc

private theorem moment_bound {h : ℕ} (hh : 0<h) : W h+σ 1 h≤2*h^3 := by
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

#print axioms bounded
end OMA.PairHeight245212

end

section

/- An explicit, unconditional numerical bound on any solution with three
distinct odd prime factors, at each fixed dyadic exponent. -/
namespace OMA.RankThreeEffective245212
open Finset Nat ArithmeticFunction OMA.Smooth245212 OMA.CofactorEffectiveOriginal245212
open scoped ArithmeticFunction.sigma
open OMA.PairHeight245212 (combine)

def stepBound (h r : ℕ) := h*(primeHeight h r+1)^(height h r)
def bound (k : ℕ) :=
  let afterOne:=stepBound (2^k) 3
  let afterTwo:=(range (afterOne+1)).sup (fun h=>stepBound h 2)
  4*afterTwo^7

private theorem step_le {h r p e : ℕ} (pb : p≤primeHeight h r) (eb : e≤height h r) :
    h*p^e ≤ stepBound h r :=
  Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (pb.trans (Nat.le_succ _)) _).trans
    (Nat.pow_le_pow_right (Nat.succ_pos _) eb))

theorem original {k m : ℕ} (odd : Odd m) (rank : m.primeFactors.card=3)
    (eqn : OeisA245212.a (2^k*m)=(σ 1 (2^k*m):ℤ)) : 2^k*m≤bound k := by
  have larger {u : ℕ} (up : 0 < u) (many : 0<u.primeFactors.card) : 1 < u := by
    by_contra! low
    have one : u=1:=by omega
    simp [one] at many
  obtain ⟨p,mp,pb,pa⟩:=dyadic (larger odd.pos (by omega)) odd eqn
  rw [rank] at pb pa
  let a:=m.factorization p
  let h:=2^k*p^a
  let u:=ordCompl[p] m
  have hp:=prime_of_mem_primeFactors mp
  have ap:=hp.factorization_pos_of_dvd odd.pos.ne' (dvd_of_mem_primeFactors mp)
  have op:=Nat.coprime_two_left.mp ((Nat.coprime_two_left.mpr odd).of_dvd_right (dvd_of_mem_primeFactors mp))
  have ou:=Nat.coprime_two_left.mp ((Nat.coprime_two_left.mpr odd).of_dvd_right (Nat.ordCompl_dvd m p))
  have hc : h.Coprime u :=
    ((Nat.coprime_two_left.mpr ou).pow_left k).mul_left ((Nat.coprime_ordCompl hp odd.pos.ne').pow_left a)
  have ur : u.primeFactors.card=2 := by
    rw [show u.primeFactors=m.primeFactors.erase p from OMA.CofactorEffectiveTree245212.support_rest m p,
      card_erase_of_mem mp,rank]
  have id : h*u=2^k*m := by change 2^k*p^a*u=_; rw [mul_assoc,Nat.ordProj_mul_ordCompl_eq_self]
  have eq1 : OeisA245212.a (h*u)=(σ 1 (h*u):ℤ) := by rwa [id]
  obtain ⟨q,mq,qb,qe⟩:=OMA.SinglePrefixEffective245212.next_atom hp op ap
    (larger ou.pos (by omega : 0<u.primeFactors.card)) hc eq1
  rw [ur] at qb qe
  let b:=u.factorization q
  let v:=ordCompl[q] u
  let g:=h*q^b
  have qq:=prime_of_mem_primeFactors mq
  have ov:=Nat.coprime_two_left.mp ((Nat.coprime_two_left.mpr ou).of_dvd_right (Nat.ordCompl_dvd u q))
  have gc : g.Coprime v :=
    (hc.of_dvd_right (Nat.ordCompl_dvd u q)).mul_left ((Nat.coprime_ordCompl qq ou.pos.ne').pow_left b)
  have gr : v.primeFactors.card=1 := by
    rw [show v.primeFactors=u.primeFactors.erase q from OMA.CofactorEffectiveTree245212.support_rest u q,
      card_erase_of_mem mq,ur]
  have old : g*v=h*u := by change h*q^b*v=_;rw [mul_assoc,Nat.ordProj_mul_ordCompl_eq_self]
  obtain ⟨z,zs⟩:=card_eq_one.mp gr
  have mz : z∈v.primeFactors := by simp [zs]
  have zp:=prime_of_mem_primeFactors mz
  have ez:=zp.factorization_pos_of_dvd ov.pos.ne' (dvd_of_mem_primeFactors mz)
  have nz : z≠2 := by
    intro same
    have dv:=dvd_of_mem_primeFactors mz
    have od:=Nat.odd_iff.mp ov
    rw [same] at dv
    omega
  have rep:=Nat.prod_primeFactors_pow_factorization ov.pos.ne'
  rw [zs,prod_singleton] at rep
  change v=z^(v.factorization z) at rep
  have eq2 : OeisA245212.a (g*z^(v.factorization z))=(σ 1 (g*z^(v.factorization z)):ℤ) := by
    rw [←rep,old];exact eq1
  have gp : 0<g:=Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos k) (pow_pos hp.pos a)) (pow_pos qq.pos b)
  have hb : h ≤ stepBound (2^k) 3 := step_le pb pa
  let L:=stepBound (2^k) 3
  let M:=(range (L+1)).sup (fun j=>stepBound j 2)
  have gb : g≤M := (step_le qb qe).trans (le_sup (f:=fun j=>stepBound j 2) (mem_range.mpr (Nat.lt_succ_of_le hb)))
  have last:=OMA.PairHeight245212.last_square gp zp nz (gc.of_dvd_right (dvd_of_mem_primeFactors mz)) ez eq2
  have fin:=OMA.PairHeight245212.combine gp gb last
  rwa [←rep,old,id] at fin

#print axioms original
end OMA.RankThreeEffective245212

end
