import FormalConjectures.OEIS.«245212»


/-! Odd solutions of OEIS A245212 with bounded prime support. -/

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

/- Generated face certificates. Regenerate with odd_boundary_245212.py --lean. -/
namespace OMA.OddFaces245212
open OMA.Smooth245212
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def initial : Box := fun _ => ⟨1,none⟩
private def b70l : Box := left initial 1 3
private def t70l : Tree := (.split 2 3 .leaf (.split 1 1 .leaf (.split 2 9 (.split 1 2 .leaf (.split 2 5 .leaf .leaf)) (.split 1 2 (.split 2 21 .leaf (.split 2 45 .leaf (.split 2 93 (.split 2 61 (.split 2 52 (.split 2 48 .leaf (.split 2 50 (.split 2 49 .leaf .leaf) .leaf)) .leaf) .leaf) .leaf))) .leaf))))
private theorem h70l : Good 7 0 b70l := fun _ h => sound (by decide) 0 t70l (by decide +kernel) h
private def b70r : Box := right initial 1 3
private def t70r : Tree := (.split 2 3 (.split 1 9 (.split 2 1 .leaf (.split 1 5 (.split 2 2 .leaf (.split 1 4 .leaf .leaf)) (.split 2 2 (.split 1 7 (.split 1 6 .leaf .leaf) .leaf) .leaf))) (.split 2 1 (.split 1 21 .leaf (.split 1 45 .leaf (.split 1 93 (.split 1 61 (.split 1 52 .leaf (.split 1 56 (.split 1 54 .leaf (.split 1 55 .leaf .leaf)) .leaf)) .leaf) .leaf))) .leaf)) .leaf)
private theorem h70r : Good 7 0 b70r := fun _ h => sound (by decide) 0 t70r (by decide +kernel) h
private theorem h70 : Good 7 0 initial := bisect initial 1 3 h70l h70r
private def b71l : Box := left initial 0 3
private def t71l : Tree := .leaf
private theorem h71l : Good 7 1 b71l := fun _ h => sound (by decide) 1 t71l (by decide +kernel) h
private def b71r : Box := right initial 0 3
private def b71rl : Box := left b71r 0 9
private def t71rl : Tree := (.split 2 3 .leaf (.split 0 5 (.split 2 9 .leaf (.split 0 4 .leaf (.split 2 21 .leaf (.split 2 45 .leaf (.split 2 93 (.split 2 61 (.split 2 52 .leaf (.split 2 56 .leaf (.split 2 58 .leaf (.split 2 59 .leaf (.split 2 60 .leaf .leaf))))) .leaf) .leaf))))) (.split 2 9 (.split 0 7 (.split 2 5 .leaf (.split 0 6 .leaf .leaf)) (.split 2 5 (.split 0 8 (.split 2 4 .leaf .leaf) .leaf) .leaf)) .leaf)))
private theorem h71rl : Good 7 1 b71rl := fun _ h => sound (by decide) 1 t71rl (by decide +kernel) h
private def b71rr : Box := right b71r 0 9
private def t71rr : Tree := (.split 2 3 (.split 0 21 (.split 2 1 .leaf (.split 0 13 (.split 2 2 .leaf .leaf) (.split 2 2 (.split 0 16 (.split 0 14 .leaf .leaf) .leaf) .leaf))) (.split 2 1 (.split 0 45 .leaf (.split 0 93 .leaf (.split 0 189 (.split 0 125 (.split 0 107 .leaf (.split 0 115 (.split 0 111 .leaf .leaf) .leaf)) .leaf) .leaf))) .leaf)) .leaf)
private theorem h71rr : Good 7 1 b71rr := fun _ h => sound (by decide) 1 t71rr (by decide +kernel) h
private theorem h71r : Good 7 1 b71r := bisect b71r 0 9 h71rl h71rr
private theorem h71 : Good 7 1 initial := bisect initial 0 3 h71l h71r
private def b72l : Box := left initial 0 3
private def t72l : Tree := .leaf
private theorem h72l : Good 7 2 b72l := fun _ h => sound (by decide) 2 t72l (by decide +kernel) h
private def b72r : Box := right initial 0 3
private def b72rl : Box := left b72r 1 3
private def t72rl : Tree := (.split 0 9 .leaf (.split 1 1 .leaf (.split 0 21 (.split 0 13 .leaf (.split 1 2 .leaf (.split 0 16 .leaf (.split 0 18 .leaf (.split 0 19 .leaf .leaf))))) (.split 0 45 (.split 1 2 .leaf .leaf) (.split 1 2 (.split 0 93 .leaf (.split 0 189 (.split 0 125 .leaf (.split 0 151 (.split 0 137 .leaf (.split 0 144 .leaf (.split 0 147 .leaf (.split 0 149 .leaf .leaf)))) .leaf)) .leaf)) .leaf)))))
private theorem h72rl : Good 7 2 b72rl := fun _ h => sound (by decide) 2 t72rl (by decide +kernel) h
private def b72rr : Box := right b72r 1 3
private def b72rrl : Box := left b72rr 0 9
private def b72rrll : Box := left b72rrl 0 5
private def t72rrll : Tree := (.split 1 9 .leaf (.split 1 21 .leaf (.split 0 4 .leaf (.split 1 45 .leaf (.split 1 93 (.split 1 61 .leaf (.split 1 74 .leaf (.split 1 83 .leaf (.split 1 88 .leaf (.split 1 90 .leaf .leaf))))) .leaf)))))
private theorem h72rrll : Good 7 2 b72rrll := fun _ h => sound (by decide) 2 t72rrll (by decide +kernel) h
private def b72rrlr : Box := right b72rrl 0 5
private def t72rrlr : Tree := (.split 1 9 (.split 0 7 .leaf (.split 1 5 .leaf (.split 1 7 (.split 0 8 (.split 1 6 .leaf .leaf) .leaf) .leaf))) (.split 0 7 (.split 1 21 (.split 1 13 (.split 0 6 .leaf .leaf) (.split 0 6 (.split 1 16 (.split 1 14 .leaf (.split 1 15 .leaf .leaf)) .leaf) .leaf)) .leaf) .leaf))
private theorem h72rrlr : Good 7 2 b72rrlr := fun _ h => sound (by decide) 2 t72rrlr (by decide +kernel) h
private theorem h72rrl : Good 7 2 b72rrl := bisect b72rrl 0 5 h72rrll h72rrlr
private def b72rrr : Box := right b72rr 0 9
private def t72rrr : Tree := (.split 0 21 (.split 1 9 (.split 0 13 (.split 1 5 (.split 0 11 (.split 1 4 .leaf .leaf) (.split 1 4 (.split 0 12 .leaf .leaf) .leaf)) .leaf) .leaf) .leaf) .leaf)
private theorem h72rrr : Good 7 2 b72rrr := fun _ h => sound (by decide) 2 t72rrr (by decide +kernel) h
private theorem h72rr : Good 7 2 b72rr := bisect b72rr 0 9 h72rrl h72rrr
private theorem h72r : Good 7 2 b72r := bisect b72r 1 3 h72rl h72rr
private theorem h72 : Good 7 2 initial := bisect initial 0 3 h72l h72r
private def b110l : Box := left initial 1 3
private def t110l : Tree := .leaf
private theorem h110l : Good 11 0 b110l := fun _ h => sound (by decide) 0 t110l (by decide +kernel) h
private def b110r : Box := right initial 1 3
private def b110rl : Box := left b110r 1 9
private def t110rl : Tree := (.split 2 3 .leaf (.split 1 5 .leaf (.split 2 9 .leaf (.split 1 7 .leaf (.split 2 21 (.split 2 13 .leaf (.split 1 8 .leaf (.split 2 16 .leaf (.split 2 18 (.split 2 17 .leaf .leaf) .leaf)))) (.split 2 45 (.split 1 8 (.split 2 29 .leaf (.split 2 36 .leaf (.split 2 40 (.split 2 38 (.split 2 37 .leaf .leaf) .leaf) .leaf))) .leaf) .leaf))))))
private theorem h110rl : Good 11 0 b110rl := fun _ h => sound (by decide) 0 t110rl (by decide +kernel) h
private def b110rr : Box := right b110r 1 9
private def b110rrl : Box := left b110rr 2 3
private def t110rrl : Tree := (.split 1 21 .leaf (.split 2 1 .leaf (.split 1 45 (.split 2 2 .leaf (.split 1 29 .leaf (.split 1 36 .leaf (.split 1 40 .leaf (.split 1 42 .leaf (.split 1 43 .leaf (.split 1 44 .leaf .leaf))))))) (.split 2 2 .leaf .leaf))))
private theorem h110rrl : Good 11 0 b110rrl := fun _ h => sound (by decide) 0 t110rrl (by decide +kernel) h
private def b110rrr : Box := right b110rr 2 3
private def b110rrrl : Box := left b110rrr 1 21
private def t110rrrl : Tree := (.split 2 9 (.split 1 13 (.split 2 5 .leaf (.split 1 11 .leaf (.split 2 7 (.split 2 6 .leaf (.split 1 12 .leaf .leaf)) .leaf))) (.split 2 5 (.split 1 16 .leaf (.split 2 4 .leaf (.split 1 18 (.split 1 17 .leaf .leaf) .leaf))) (.split 1 16 (.split 2 7 (.split 1 14 (.split 2 6 .leaf .leaf) .leaf) .leaf) .leaf))) (.split 1 13 (.split 2 21 (.split 1 11 (.split 2 13 (.split 1 10 (.split 2 11 .leaf .leaf) .leaf) .leaf) .leaf) .leaf) .leaf))
private theorem h110rrrl : Good 11 0 b110rrrl := fun _ h => sound (by decide) 0 t110rrrl (by decide +kernel) h
private def b110rrrr : Box := right b110rrr 1 21
private def t110rrrr : Tree := (.split 2 9 (.split 1 45 (.split 2 5 (.split 1 29 (.split 2 4 (.split 1 25 (.split 1 23 (.split 1 22 .leaf .leaf) .leaf) .leaf) .leaf) .leaf) .leaf) .leaf) .leaf)
private theorem h110rrrr : Good 11 0 b110rrrr := fun _ h => sound (by decide) 0 t110rrrr (by decide +kernel) h
private theorem h110rrr : Good 11 0 b110rrr := bisect b110rrr 1 21 h110rrrl h110rrrr
private theorem h110rr : Good 11 0 b110rr := bisect b110rr 2 3 h110rrl h110rrr
private theorem h110r : Good 11 0 b110r := bisect b110r 1 9 h110rl h110rr
private theorem h110 : Good 11 0 initial := bisect initial 1 3 h110l h110r
private def b111l : Box := left initial 0 3
private def t111l : Tree := .leaf
private theorem h111l : Good 11 1 b111l := fun _ h => sound (by decide) 1 t111l (by decide +kernel) h
private def b111r : Box := right initial 0 3
private def b111rl : Box := left b111r 0 9
private def t111rl : Tree := .leaf
private theorem h111rl : Good 11 1 b111rl := fun _ h => sound (by decide) 1 t111rl (by decide +kernel) h
private def b111rr : Box := right b111r 0 9
private def b111rrl : Box := left b111rr 0 21
private def b111rrll : Box := left b111rrl 2 3
private def t111rrll : Tree := .leaf
private theorem h111rrll : Good 11 1 b111rrll := fun _ h => sound (by decide) 1 t111rrll (by decide +kernel) h
private def b111rrlr : Box := right b111rrl 2 3
private def b111rrlrl : Box := left b111rrlr 0 13
private def t111rrlrl : Tree := .leaf
private theorem h111rrlrl : Good 11 1 b111rrlrl := fun _ h => sound (by decide) 1 t111rrlrl (by decide +kernel) h
private def b111rrlrr : Box := right b111rrlr 0 13
private def b111rrlrrl : Box := left b111rrlrr 2 9
private def t111rrlrrl : Tree := .leaf
private theorem h111rrlrrl : Good 11 1 b111rrlrrl := fun _ h => sound (by decide) 1 t111rrlrrl (by decide +kernel) h
private def b111rrlrrr : Box := right b111rrlrr 2 9
private def b111rrlrrrl : Box := left b111rrlrrr 0 16
private def t111rrlrrrl : Tree := (.split 2 21 .leaf (.split 0 14 .leaf (.split 2 45 .leaf (.split 0 15 .leaf (.split 2 93 .leaf (.split 2 189 (.split 2 125 (.split 2 107 .leaf .leaf) .leaf) .leaf))))))
private theorem h111rrlrrrl : Good 11 1 b111rrlrrrl := fun _ h => sound (by decide) 1 t111rrlrrrl (by decide +kernel) h
private def b111rrlrrrr : Box := right b111rrlrrr 0 16
private def t111rrlrrrr : Tree := (.split 2 21 (.split 0 18 .leaf (.split 2 13 (.split 0 19 .leaf (.split 2 11 .leaf (.split 0 20 .leaf .leaf))) (.split 0 19 (.split 2 16 .leaf (.split 2 18 (.split 2 17 .leaf .leaf) .leaf)) (.split 2 16 (.split 0 20 (.split 2 14 .leaf .leaf) .leaf) .leaf)))) (.split 0 18 (.split 2 45 (.split 2 29 (.split 0 17 .leaf (.split 2 25 (.split 2 23 .leaf .leaf) .leaf)) (.split 0 17 (.split 2 36 .leaf (.split 2 40 (.split 2 38 (.split 2 37 .leaf .leaf) .leaf) .leaf)) .leaf)) .leaf) .leaf))
private theorem h111rrlrrrr : Good 11 1 b111rrlrrrr := fun _ h => sound (by decide) 1 t111rrlrrrr (by decide +kernel) h
private theorem h111rrlrrr : Good 11 1 b111rrlrrr := bisect b111rrlrrr 0 16 h111rrlrrrl h111rrlrrrr
private theorem h111rrlrr : Good 11 1 b111rrlrr := bisect b111rrlrr 2 9 h111rrlrrl h111rrlrrr
private theorem h111rrlr : Good 11 1 b111rrlr := bisect b111rrlr 0 13 h111rrlrl h111rrlrr
private theorem h111rrl : Good 11 1 b111rrl := bisect b111rrl 2 3 h111rrll h111rrlr
private def b111rrr : Box := right b111rr 0 21
private def b111rrrl : Box := left b111rrr 2 3
private def t111rrrl : Tree := (.split 0 45 .leaf (.split 2 1 .leaf (.split 0 93 (.split 2 2 .leaf (.split 0 61 .leaf (.split 0 74 .leaf (.split 0 83 .leaf (.split 0 88 .leaf (.split 0 90 .leaf .leaf)))))) (.split 2 2 .leaf .leaf))))
private theorem h111rrrl : Good 11 1 b111rrrl := fun _ h => sound (by decide) 1 t111rrrl (by decide +kernel) h
private def b111rrrr : Box := right b111rrr 2 3
private def b111rrrrl : Box := left b111rrrr 0 45
private def b111rrrrll : Box := left b111rrrrl 2 9
private def t111rrrrll : Tree := (.split 0 29 (.split 2 5 .leaf (.split 0 25 (.split 2 7 .leaf (.split 0 23 .leaf (.split 2 8 (.split 0 24 .leaf .leaf) .leaf))) (.split 2 7 (.split 0 27 (.split 2 6 .leaf (.split 0 26 .leaf .leaf)) (.split 2 6 .leaf .leaf)) .leaf))) (.split 2 5 (.split 0 36 (.split 0 32 .leaf (.split 2 4 .leaf (.split 0 34 .leaf (.split 0 35 .leaf .leaf)))) (.split 2 4 .leaf .leaf)) .leaf))
private theorem h111rrrrll : Good 11 1 b111rrrrll := fun _ h => sound (by decide) 1 t111rrrrll (by decide +kernel) h
private def b111rrrrlr : Box := right b111rrrrl 2 9
private def t111rrrrlr : Tree := (.split 0 29 (.split 2 21 (.split 0 25 (.split 2 13 (.split 0 23 (.split 2 11 (.split 0 22 (.split 2 10 .leaf .leaf) .leaf) .leaf) .leaf) .leaf) .leaf) .leaf) .leaf)
private theorem h111rrrrlr : Good 11 1 b111rrrrlr := fun _ h => sound (by decide) 1 t111rrrrlr (by decide +kernel) h
private theorem h111rrrrl : Good 11 1 b111rrrrl := bisect b111rrrrl 2 9 h111rrrrll h111rrrrlr
private def b111rrrrr : Box := right b111rrrr 0 45
private def t111rrrrr : Tree := (.split 2 9 (.split 0 93 (.split 2 5 (.split 0 61 (.split 0 52 (.split 2 4 (.split 0 48 (.split 0 46 .leaf .leaf) .leaf) .leaf) .leaf) .leaf) .leaf) .leaf) .leaf)
private theorem h111rrrrr : Good 11 1 b111rrrrr := fun _ h => sound (by decide) 1 t111rrrrr (by decide +kernel) h
private theorem h111rrrr : Good 11 1 b111rrrr := bisect b111rrrr 0 45 h111rrrrl h111rrrrr
private theorem h111rrr : Good 11 1 b111rrr := bisect b111rrr 2 3 h111rrrl h111rrrr
private theorem h111rr : Good 11 1 b111rr := bisect b111rr 0 21 h111rrl h111rrr
private theorem h111r : Good 11 1 b111r := bisect b111r 0 9 h111rl h111rr
private theorem h111 : Good 11 1 initial := bisect initial 0 3 h111l h111r
private def b112l : Box := left initial 0 3
private def t112l : Tree := .leaf
private theorem h112l : Good 11 2 b112l := fun _ h => sound (by decide) 2 t112l (by decide +kernel) h
private def b112r : Box := right initial 0 3
private def b112rl : Box := left b112r 1 3
private def t112rl : Tree := .leaf
private theorem h112rl : Good 11 2 b112rl := fun _ h => sound (by decide) 2 t112rl (by decide +kernel) h
private def b112rr : Box := right b112r 1 3
private def b112rrl : Box := left b112rr 0 9
private def t112rrl : Tree := .leaf
private theorem h112rrl : Good 11 2 b112rrl := fun _ h => sound (by decide) 2 t112rrl (by decide +kernel) h
private def b112rrr : Box := right b112rr 0 9
private def b112rrrl : Box := left b112rrr 0 21
private def b112rrrll : Box := left b112rrrl 1 9
private def t112rrrll : Tree := .leaf
private theorem h112rrrll : Good 11 2 b112rrrll := fun _ h => sound (by decide) 2 t112rrrll (by decide +kernel) h
private def b112rrrlr : Box := right b112rrrl 1 9
private def b112rrrlrl : Box := left b112rrrlr 0 13
private def t112rrrlrl : Tree := .leaf
private theorem h112rrrlrl : Good 11 2 b112rrrlrl := fun _ h => sound (by decide) 2 t112rrrlrl (by decide +kernel) h
private def b112rrrlrr : Box := right b112rrrlr 0 13
private def b112rrrlrrl : Box := left b112rrrlrr 1 21
private def t112rrrlrrl : Tree := .leaf
private theorem h112rrrlrrl : Good 11 2 b112rrrlrrl := fun _ h => sound (by decide) 2 t112rrrlrrl (by decide +kernel) h
private def b112rrrlrrr : Box := right b112rrrlrr 1 21
private def b112rrrlrrrl : Box := left b112rrrlrrr 0 16
private def t112rrrlrrrl : Tree := (.split 1 45 .leaf (.split 1 93 .leaf (.split 0 14 .leaf (.split 1 189 .leaf (.split 0 15 .leaf (.split 1 381 (.split 1 253 .leaf (.split 1 304 (.split 1 276 (.split 1 264 .leaf (.split 1 270 .leaf (.split 1 273 (.split 1 271 .leaf .leaf) .leaf))) .leaf) .leaf)) .leaf))))))
private theorem h112rrrlrrrl : Good 11 2 b112rrrlrrrl := fun _ h => sound (by decide) 2 t112rrrlrrrl (by decide +kernel) h
private def b112rrrlrrrr : Box := right b112rrrlrrr 0 16
private def b112rrrlrrrrl : Box := left b112rrrlrrrr 1 45
private def t112rrrlrrrrl : Tree := (.split 0 18 .leaf (.split 1 29 .leaf (.split 0 19 (.split 1 36 .leaf (.split 1 40 .leaf (.split 1 42 .leaf (.split 1 43 .leaf (.split 1 44 .leaf .leaf))))) (.split 1 36 (.split 1 32 (.split 0 20 .leaf (.split 1 30 .leaf (.split 1 31 .leaf .leaf))) (.split 0 20 .leaf .leaf)) .leaf))))
private theorem h112rrrlrrrrl : Good 11 2 b112rrrlrrrrl := fun _ h => sound (by decide) 2 t112rrrlrrrrl (by decide +kernel) h
private def b112rrrlrrrrr : Box := right b112rrrlrrrr 1 45
private def t112rrrlrrrrr : Tree := (.split 0 18 (.split 1 93 (.split 1 61 (.split 0 17 .leaf (.split 1 52 .leaf (.split 1 56 .leaf (.split 1 58 .leaf (.split 1 59 .leaf (.split 1 60 .leaf .leaf)))))) (.split 0 17 .leaf .leaf)) (.split 1 189 (.split 0 17 (.split 1 125 (.split 1 107 (.split 1 100 (.split 1 96 (.split 1 94 .leaf (.split 1 95 .leaf .leaf)) .leaf) .leaf) .leaf) .leaf) .leaf) .leaf)) .leaf)
private theorem h112rrrlrrrrr : Good 11 2 b112rrrlrrrrr := fun _ h => sound (by decide) 2 t112rrrlrrrrr (by decide +kernel) h
private theorem h112rrrlrrrr : Good 11 2 b112rrrlrrrr := bisect b112rrrlrrrr 1 45 h112rrrlrrrrl h112rrrlrrrrr
private theorem h112rrrlrrr : Good 11 2 b112rrrlrrr := bisect b112rrrlrrr 0 16 h112rrrlrrrl h112rrrlrrrr
private theorem h112rrrlrr : Good 11 2 b112rrrlrr := bisect b112rrrlrr 1 21 h112rrrlrrl h112rrrlrrr
private theorem h112rrrlr : Good 11 2 b112rrrlr := bisect b112rrrlr 0 13 h112rrrlrl h112rrrlrr
private theorem h112rrrl : Good 11 2 b112rrrl := bisect b112rrrl 1 9 h112rrrll h112rrrlr
private def b112rrrr : Box := right b112rrr 0 21
private def b112rrrrl : Box := left b112rrrr 1 9
private def t112rrrrl : Tree := (.split 0 45 .leaf (.split 1 5 .leaf (.split 0 93 (.split 1 7 .leaf (.split 0 61 .leaf (.split 0 74 .leaf (.split 1 8 .leaf (.split 0 83 .leaf (.split 0 88 .leaf (.split 0 90 .leaf .leaf))))))) (.split 1 7 .leaf (.split 0 189 (.split 0 125 (.split 1 8 .leaf .leaf) (.split 1 8 .leaf .leaf)) (.split 0 381 (.split 1 8 (.split 0 253 (.split 0 217 (.split 0 202 (.split 0 195 (.split 0 192 (.split 0 190 .leaf (.split 0 191 .leaf .leaf)) .leaf) .leaf) .leaf) .leaf) .leaf) .leaf) .leaf))))))
private theorem h112rrrrl : Good 11 2 b112rrrrl := fun _ h => sound (by decide) 2 t112rrrrl (by decide +kernel) h
private def b112rrrrr : Box := right b112rrrr 1 9
private def b112rrrrrl : Box := left b112rrrrr 0 45
private def b112rrrrrll : Box := left b112rrrrrl 1 21
private def b112rrrrrlll : Box := left b112rrrrrll 0 29
private def t112rrrrrlll : Tree := (.split 1 13 .leaf (.split 0 25 .leaf (.split 1 16 .leaf (.split 1 18 (.split 0 27 .leaf (.split 1 17 .leaf .leaf)) (.split 0 27 (.split 1 19 (.split 0 26 .leaf .leaf) .leaf) .leaf)))))
private theorem h112rrrrrlll : Good 11 2 b112rrrrrlll := fun _ h => sound (by decide) 2 t112rrrrrlll (by decide +kernel) h
private def b112rrrrrllr : Box := right b112rrrrrll 0 29
private def t112rrrrrllr : Tree := (.split 1 13 (.split 0 36 .leaf (.split 1 11 .leaf (.split 0 40 (.split 1 12 .leaf (.split 0 38 .leaf .leaf)) (.split 1 12 (.split 0 42 .leaf (.split 0 43 .leaf .leaf)) .leaf)))) (.split 0 36 (.split 1 16 (.split 0 32 (.split 1 14 .leaf (.split 0 30 .leaf (.split 1 15 .leaf .leaf))) (.split 1 14 (.split 0 34 .leaf (.split 0 35 .leaf .leaf)) .leaf)) .leaf) .leaf))
private theorem h112rrrrrllr : Good 11 2 b112rrrrrllr := fun _ h => sound (by decide) 2 t112rrrrrllr (by decide +kernel) h
private theorem h112rrrrrll : Good 11 2 b112rrrrrll := bisect b112rrrrrll 0 29 h112rrrrrlll h112rrrrrllr
private def b112rrrrrlr : Box := right b112rrrrrl 1 21
private def t112rrrrrlr : Tree := (.split 0 29 (.split 1 45 (.split 0 25 (.split 1 29 (.split 0 23 (.split 1 25 (.split 1 23 .leaf (.split 0 22 .leaf (.split 1 24 .leaf .leaf))) (.split 0 22 (.split 1 27 .leaf .leaf) .leaf)) (.split 1 25 (.split 1 23 (.split 0 24 (.split 1 22 .leaf .leaf) .leaf) .leaf) .leaf)) .leaf) .leaf) .leaf) .leaf)
private theorem h112rrrrrlr : Good 11 2 b112rrrrrlr := fun _ h => sound (by decide) 2 t112rrrrrlr (by decide +kernel) h
private theorem h112rrrrrl : Good 11 2 b112rrrrrl := bisect b112rrrrrl 1 21 h112rrrrrll h112rrrrrlr
private def b112rrrrrr : Box := right b112rrrrr 0 45
private def t112rrrrrr : Tree := (.split 1 21 (.split 0 93 (.split 1 13 (.split 0 61 (.split 1 11 (.split 0 52 (.split 1 10 .leaf (.split 0 48 .leaf (.split 0 50 .leaf .leaf))) (.split 1 10 .leaf .leaf)) .leaf) (.split 1 11 (.split 0 74 (.split 1 10 (.split 0 67 (.split 0 64 (.split 0 62 .leaf (.split 0 63 .leaf .leaf)) .leaf) .leaf) .leaf) .leaf) .leaf)) .leaf) .leaf) .leaf)
private theorem h112rrrrrr : Good 11 2 b112rrrrrr := fun _ h => sound (by decide) 2 t112rrrrrr (by decide +kernel) h
private theorem h112rrrrr : Good 11 2 b112rrrrr := bisect b112rrrrr 0 45 h112rrrrrl h112rrrrrr
private theorem h112rrrr : Good 11 2 b112rrrr := bisect b112rrrr 1 9 h112rrrrl h112rrrrr
private theorem h112rrr : Good 11 2 b112rrr := bisect b112rrr 0 21 h112rrrl h112rrrr
private theorem h112rr : Good 11 2 b112rr := bisect b112rr 0 9 h112rrl h112rrr
private theorem h112r : Good 11 2 b112r := bisect b112r 1 3 h112rl h112rr
private theorem h112 : Good 11 2 initial := bisect initial 0 3 h112l h112r
private def b130l : Box := left initial 1 3
private def t130l : Tree := .leaf
private theorem h130l : Good 13 0 b130l := fun _ h => sound (by decide) 0 t130l (by decide +kernel) h
private def b130r : Box := right initial 1 3
private def b130rl : Box := left b130r 1 9
private def t130rl : Tree := .leaf
private theorem h130rl : Good 13 0 b130rl := fun _ h => sound (by decide) 0 t130rl (by decide +kernel) h
private def b130rr : Box := right b130r 1 9
private def b130rrl : Box := left b130rr 2 3
private def t130rrl : Tree := .leaf
private theorem h130rrl : Good 13 0 b130rrl := fun _ h => sound (by decide) 0 t130rrl (by decide +kernel) h
private def b130rrr : Box := right b130rr 2 3
private def b130rrrl : Box := left b130rrr 1 21
private def b130rrrll : Box := left b130rrrl 2 9
private def t130rrrll : Tree := .leaf
private theorem h130rrrll : Good 13 0 b130rrrll := fun _ h => sound (by decide) 0 t130rrrll (by decide +kernel) h
private def b130rrrlr : Box := right b130rrrl 2 9
private def b130rrrlrl : Box := left b130rrrlr 1 13
private def t130rrrlrl : Tree := .leaf
private theorem h130rrrlrl : Good 13 0 b130rrrlrl := fun _ h => sound (by decide) 0 t130rrrlrl (by decide +kernel) h
private def b130rrrlrr : Box := right b130rrrlr 1 13
private def b130rrrlrrl : Box := left b130rrrlrr 2 21
private def t130rrrlrrl : Tree := (.split 1 16 .leaf (.split 2 13 .leaf (.split 1 18 .leaf (.split 2 16 .leaf (.split 1 19 .leaf (.split 2 18 .leaf (.split 1 20 .leaf (.split 2 19 .leaf .leaf))))))))
private theorem h130rrrlrrl : Good 13 0 b130rrrlrrl := fun _ h => sound (by decide) 0 t130rrrlrrl (by decide +kernel) h
private def b130rrrlrrr : Box := right b130rrrlrr 2 21
private def b130rrrlrrrl : Box := left b130rrrlrrr 1 16
private def t130rrrlrrrl : Tree := (.split 2 45 .leaf (.split 1 14 .leaf (.split 2 93 .leaf (.split 1 15 .leaf (.split 2 189 (.split 2 125 (.split 2 107 .leaf (.split 2 115 .leaf (.split 2 120 (.split 2 117 .leaf (.split 2 118 .leaf (.split 2 119 .leaf .leaf))) .leaf))) .leaf) .leaf)))))
private theorem h130rrrlrrrl : Good 13 0 b130rrrlrrrl := fun _ h => sound (by decide) 0 t130rrrlrrrl (by decide +kernel) h
private def b130rrrlrrrr : Box := right b130rrrlrrr 1 16
private def b130rrrlrrrrl : Box := left b130rrrlrrrr 2 45
private def t130rrrlrrrrl : Tree := (.split 1 18 (.split 2 29 .leaf (.split 2 36 (.split 1 17 .leaf (.split 2 32 .leaf (.split 2 34 .leaf (.split 2 35 .leaf .leaf)))) (.split 1 17 .leaf .leaf))) (.split 2 29 (.split 1 19 (.split 2 25 .leaf (.split 2 27 .leaf .leaf)) (.split 2 25 (.split 1 20 (.split 2 23 (.split 2 22 .leaf .leaf) .leaf) .leaf) .leaf)) .leaf))
private theorem h130rrrlrrrrl : Good 13 0 b130rrrlrrrrl := fun _ h => sound (by decide) 0 t130rrrlrrrrl (by decide +kernel) h
private def b130rrrlrrrrr : Box := right b130rrrlrrrr 2 45
private def t130rrrlrrrrr : Tree := (.split 1 18 (.split 2 93 (.split 2 61 (.split 1 17 (.split 2 52 .leaf (.split 2 56 (.split 2 54 (.split 2 53 .leaf .leaf) .leaf) .leaf)) .leaf) .leaf) .leaf) .leaf)
private theorem h130rrrlrrrrr : Good 13 0 b130rrrlrrrrr := fun _ h => sound (by decide) 0 t130rrrlrrrrr (by decide +kernel) h
private theorem h130rrrlrrrr : Good 13 0 b130rrrlrrrr := bisect b130rrrlrrrr 2 45 h130rrrlrrrrl h130rrrlrrrrr
private theorem h130rrrlrrr : Good 13 0 b130rrrlrrr := bisect b130rrrlrrr 1 16 h130rrrlrrrl h130rrrlrrrr
private theorem h130rrrlrr : Good 13 0 b130rrrlrr := bisect b130rrrlrr 2 21 h130rrrlrrl h130rrrlrrr
private theorem h130rrrlr : Good 13 0 b130rrrlr := bisect b130rrrlr 1 13 h130rrrlrl h130rrrlrr
private theorem h130rrrl : Good 13 0 b130rrrl := bisect b130rrrl 2 9 h130rrrll h130rrrlr
private def b130rrrr : Box := right b130rrr 1 21
private def b130rrrrl : Box := left b130rrrr 2 9
private def b130rrrrll : Box := left b130rrrrl 1 45
private def t130rrrrll : Tree := (.split 2 5 .leaf (.split 1 29 .leaf (.split 2 7 .leaf (.split 1 36 (.split 1 32 .leaf (.split 2 8 .leaf (.split 1 34 .leaf .leaf))) (.split 1 40 (.split 2 8 (.split 1 38 .leaf (.split 1 39 .leaf .leaf)) .leaf) .leaf)))))
private theorem h130rrrrll : Good 13 0 b130rrrrll := fun _ h => sound (by decide) 0 t130rrrrll (by decide +kernel) h
private def b130rrrrlr : Box := right b130rrrrl 1 45
private def t130rrrrlr : Tree := (.split 2 5 (.split 1 93 .leaf (.split 1 189 (.split 2 4 .leaf (.split 1 125 .leaf (.split 1 151 .leaf (.split 1 168 (.split 1 159 .leaf (.split 1 163 .leaf .leaf)) .leaf)))) (.split 2 4 .leaf .leaf))) (.split 1 93 (.split 2 7 (.split 1 61 (.split 2 6 .leaf (.split 1 52 (.split 1 48 .leaf .leaf) .leaf)) (.split 1 74 (.split 2 6 (.split 1 67 .leaf (.split 1 70 (.split 1 68 .leaf (.split 1 69 .leaf .leaf)) .leaf)) .leaf) .leaf)) .leaf) .leaf))
private theorem h130rrrrlr : Good 13 0 b130rrrrlr := fun _ h => sound (by decide) 0 t130rrrrlr (by decide +kernel) h
private theorem h130rrrrl : Good 13 0 b130rrrrl := bisect b130rrrrl 1 45 h130rrrrll h130rrrrlr
private def b130rrrrr : Box := right b130rrrr 2 9
private def b130rrrrrl : Box := left b130rrrrr 1 45
private def b130rrrrrll : Box := left b130rrrrrl 2 21
private def b130rrrrrlll : Box := left b130rrrrrll 1 29
private def t130rrrrrlll : Tree := (.split 2 13 (.split 1 25 .leaf (.split 2 11 (.split 1 27 .leaf (.split 2 10 .leaf (.split 1 28 .leaf .leaf))) (.split 1 27 (.split 2 12 (.split 1 26 .leaf .leaf) .leaf) .leaf))) (.split 1 25 (.split 2 16 (.split 1 23 (.split 2 14 .leaf (.split 1 22 .leaf (.split 2 15 .leaf .leaf))) (.split 2 14 (.split 1 24 .leaf .leaf) .leaf)) (.split 1 23 (.split 2 18 (.split 1 22 (.split 2 17 .leaf .leaf) .leaf) .leaf) .leaf)) .leaf))
private theorem h130rrrrrlll : Good 13 0 b130rrrrrlll := fun _ h => sound (by decide) 0 t130rrrrrlll (by decide +kernel) h
private def b130rrrrrllr : Box := right b130rrrrrll 1 29
private def t130rrrrrllr : Tree := (.split 2 13 (.split 1 36 (.split 2 11 (.split 1 32 (.split 2 10 (.split 1 30 .leaf .leaf) .leaf) .leaf) .leaf) .leaf) .leaf)
private theorem h130rrrrrllr : Good 13 0 b130rrrrrllr := fun _ h => sound (by decide) 0 t130rrrrrllr (by decide +kernel) h
private theorem h130rrrrrll : Good 13 0 b130rrrrrll := bisect b130rrrrrll 1 29 h130rrrrrlll h130rrrrrllr
private def b130rrrrrlr : Box := right b130rrrrrl 2 21
private def t130rrrrrlr : Tree := .leaf
private theorem h130rrrrrlr : Good 13 0 b130rrrrrlr := fun _ h => sound (by decide) 0 t130rrrrrlr (by decide +kernel) h
private theorem h130rrrrrl : Good 13 0 b130rrrrrl := bisect b130rrrrrl 2 21 h130rrrrrll h130rrrrrlr
private def b130rrrrrr : Box := right b130rrrrr 1 45
private def t130rrrrrr : Tree := .leaf
private theorem h130rrrrrr : Good 13 0 b130rrrrrr := fun _ h => sound (by decide) 0 t130rrrrrr (by decide +kernel) h
private theorem h130rrrrr : Good 13 0 b130rrrrr := bisect b130rrrrr 1 45 h130rrrrrl h130rrrrrr
private theorem h130rrrr : Good 13 0 b130rrrr := bisect b130rrrr 2 9 h130rrrrl h130rrrrr
private theorem h130rrr : Good 13 0 b130rrr := bisect b130rrr 1 21 h130rrrl h130rrrr
private theorem h130rr : Good 13 0 b130rr := bisect b130rr 2 3 h130rrl h130rrr
private theorem h130r : Good 13 0 b130r := bisect b130r 1 9 h130rl h130rr
private theorem h130 : Good 13 0 initial := bisect initial 1 3 h130l h130r
private def b131l : Box := left initial 0 3
private def t131l : Tree := .leaf
private theorem h131l : Good 13 1 b131l := fun _ h => sound (by decide) 1 t131l (by decide +kernel) h
private def b131r : Box := right initial 0 3
private def b131rl : Box := left b131r 0 9
private def t131rl : Tree := .leaf
private theorem h131rl : Good 13 1 b131rl := fun _ h => sound (by decide) 1 t131rl (by decide +kernel) h
private def b131rr : Box := right b131r 0 9
private def b131rrl : Box := left b131rr 0 21
private def t131rrl : Tree := .leaf
private theorem h131rrl : Good 13 1 b131rrl := fun _ h => sound (by decide) 1 t131rrl (by decide +kernel) h
private def b131rrr : Box := right b131rr 0 21
private def b131rrrl : Box := left b131rrr 2 3
private def t131rrrl : Tree := .leaf
private theorem h131rrrl : Good 13 1 b131rrrl := fun _ h => sound (by decide) 1 t131rrrl (by decide +kernel) h
private def b131rrrr : Box := right b131rrr 2 3
private def b131rrrrl : Box := left b131rrrr 0 45
private def b131rrrrll : Box := left b131rrrrl 2 9
private def t131rrrrll : Tree := .leaf
private theorem h131rrrrll : Good 13 1 b131rrrrll := fun _ h => sound (by decide) 1 t131rrrrll (by decide +kernel) h
private def b131rrrrlr : Box := right b131rrrrl 2 9
private def b131rrrrlrl : Box := left b131rrrrlr 0 29
private def t131rrrrlrl : Tree := .leaf
private theorem h131rrrrlrl : Good 13 1 b131rrrrlrl := fun _ h => sound (by decide) 1 t131rrrrlrl (by decide +kernel) h
private def b131rrrrlrr : Box := right b131rrrrlr 0 29
private def b131rrrrlrrl : Box := left b131rrrrlrr 2 21
private def t131rrrrlrrl : Tree := (.split 0 36 .leaf (.split 2 13 .leaf (.split 0 40 .leaf (.split 2 16 .leaf (.split 0 42 (.split 2 18 .leaf (.split 0 41 .leaf (.split 2 19 .leaf (.split 2 20 .leaf .leaf)))) (.split 2 18 (.split 0 43 .leaf (.split 0 44 .leaf (.split 2 17 .leaf .leaf))) (.split 0 43 (.split 2 19 .leaf .leaf) .leaf)))))))
private theorem h131rrrrlrrl : Good 13 1 b131rrrrlrrl := fun _ h => sound (by decide) 1 t131rrrrlrrl (by decide +kernel) h
private def b131rrrrlrrr : Box := right b131rrrrlrr 2 21
private def b131rrrrlrrrl : Box := left b131rrrrlrrr 0 36
private def b131rrrrlrrrll : Box := left b131rrrrlrrrl 2 45
private def t131rrrrlrrrll : Tree := (.split 0 32 .leaf (.split 2 29 .leaf (.split 0 34 .leaf (.split 2 36 .leaf (.split 0 35 .leaf (.split 2 40 .leaf (.split 2 42 .leaf .leaf)))))))
private theorem h131rrrrlrrrll : Good 13 1 b131rrrrlrrrll := fun _ h => sound (by decide) 1 t131rrrrlrrrll (by decide +kernel) h
private def b131rrrrlrrrlr : Box := right b131rrrrlrrrl 2 45
private def b131rrrrlrrrlrl : Box := left b131rrrrlrrrlr 0 32
private def t131rrrrlrrrlrl : Tree := (.split 2 93 .leaf (.split 0 30 .leaf (.split 2 189 .leaf (.split 0 31 .leaf (.split 2 381 (.split 2 253 .leaf (.split 2 304 .leaf (.split 2 338 .leaf (.split 2 358 (.split 2 348 .leaf (.split 2 353 (.split 2 350 .leaf (.split 2 351 .leaf .leaf)) .leaf)) .leaf)))) .leaf)))))
private theorem h131rrrrlrrrlrl : Good 13 1 b131rrrrlrrrlrl := fun _ h => sound (by decide) 1 t131rrrrlrrrlrl (by decide +kernel) h
private def b131rrrrlrrrlrr : Box := right b131rrrrlrrrlr 0 32
private def b131rrrrlrrrlrrl : Box := left b131rrrrlrrrlrr 2 93
private def t131rrrrlrrrlrrl : Tree := (.split 0 34 (.split 2 61 .leaf (.split 0 33 .leaf (.split 2 74 (.split 2 67 .leaf (.split 2 70 .leaf (.split 2 72 .leaf (.split 2 73 .leaf .leaf)))) .leaf))) (.split 2 61 (.split 0 35 (.split 2 52 .leaf (.split 2 56 (.split 2 54 (.split 2 53 .leaf .leaf) .leaf) .leaf)) .leaf) .leaf))
private theorem h131rrrrlrrrlrrl : Good 13 1 b131rrrrlrrrlrrl := fun _ h => sound (by decide) 1 t131rrrrlrrrlrrl (by decide +kernel) h
private def b131rrrrlrrrlrrr : Box := right b131rrrrlrrrlrr 2 93
private def t131rrrrlrrrlrrr : Tree := (.split 0 34 (.split 2 189 (.split 0 33 (.split 2 125 (.split 2 107 .leaf (.split 2 115 .leaf (.split 2 120 (.split 2 117 .leaf (.split 2 118 .leaf (.split 2 119 .leaf .leaf))) .leaf))) .leaf) .leaf) .leaf) .leaf)
private theorem h131rrrrlrrrlrrr : Good 13 1 b131rrrrlrrrlrrr := fun _ h => sound (by decide) 1 t131rrrrlrrrlrrr (by decide +kernel) h
private theorem h131rrrrlrrrlrr : Good 13 1 b131rrrrlrrrlrr := bisect b131rrrrlrrrlrr 2 93 h131rrrrlrrrlrrl h131rrrrlrrrlrrr
private theorem h131rrrrlrrrlr : Good 13 1 b131rrrrlrrrlr := bisect b131rrrrlrrrlr 0 32 h131rrrrlrrrlrl h131rrrrlrrrlrr
private theorem h131rrrrlrrrl : Good 13 1 b131rrrrlrrrl := bisect b131rrrrlrrrl 2 45 h131rrrrlrrrll h131rrrrlrrrlr
private def b131rrrrlrrrr : Box := right b131rrrrlrrr 0 36
private def b131rrrrlrrrrl : Box := left b131rrrrlrrrr 2 45
private def t131rrrrlrrrrl : Tree := (.split 0 40 (.split 2 29 (.split 0 38 .leaf (.split 2 25 (.split 0 39 .leaf (.split 2 23 .leaf (.split 2 24 .leaf .leaf))) (.split 0 39 (.split 2 27 .leaf .leaf) .leaf))) (.split 0 38 (.split 2 36 (.split 0 37 (.split 2 32 .leaf (.split 2 34 .leaf (.split 2 35 .leaf .leaf))) (.split 2 32 (.split 2 30 .leaf (.split 2 31 .leaf .leaf)) .leaf)) .leaf) .leaf)) (.split 2 29 (.split 0 42 (.split 2 25 (.split 2 23 (.split 0 41 (.split 2 22 .leaf .leaf) .leaf) .leaf) .leaf) .leaf) .leaf))
private theorem h131rrrrlrrrrl : Good 13 1 b131rrrrlrrrrl := fun _ h => sound (by decide) 1 t131rrrrlrrrrl (by decide +kernel) h
private def b131rrrrlrrrrr : Box := right b131rrrrlrrrr 2 45
private def t131rrrrlrrrrr : Tree := .leaf
private theorem h131rrrrlrrrrr : Good 13 1 b131rrrrlrrrrr := fun _ h => sound (by decide) 1 t131rrrrlrrrrr (by decide +kernel) h
private theorem h131rrrrlrrrr : Good 13 1 b131rrrrlrrrr := bisect b131rrrrlrrrr 2 45 h131rrrrlrrrrl h131rrrrlrrrrr
private theorem h131rrrrlrrr : Good 13 1 b131rrrrlrrr := bisect b131rrrrlrrr 0 36 h131rrrrlrrrl h131rrrrlrrrr
private theorem h131rrrrlrr : Good 13 1 b131rrrrlrr := bisect b131rrrrlrr 2 21 h131rrrrlrrl h131rrrrlrrr
private theorem h131rrrrlr : Good 13 1 b131rrrrlr := bisect b131rrrrlr 0 29 h131rrrrlrl h131rrrrlrr
private theorem h131rrrrl : Good 13 1 b131rrrrl := bisect b131rrrrl 2 9 h131rrrrll h131rrrrlr
private def b131rrrrr : Box := right b131rrrr 0 45
private def b131rrrrrl : Box := left b131rrrrr 2 9
private def b131rrrrrll : Box := left b131rrrrrl 0 93
private def t131rrrrrll : Tree := (.split 2 5 .leaf (.split 0 61 .leaf (.split 0 74 (.split 2 7 .leaf (.split 0 67 .leaf (.split 2 8 .leaf (.split 0 70 (.split 0 68 .leaf (.split 0 69 .leaf .leaf)) .leaf)))) (.split 2 7 .leaf (.split 0 83 (.split 2 8 (.split 0 78 .leaf (.split 0 80 (.split 0 79 .leaf .leaf) .leaf)) .leaf) .leaf)))))
private theorem h131rrrrrll : Good 13 1 b131rrrrrll := fun _ h => sound (by decide) 1 t131rrrrrll (by decide +kernel) h
private def b131rrrrrlr : Box := right b131rrrrrl 0 93
private def b131rrrrrlrl : Box := left b131rrrrrlr 2 5
private def t131rrrrrlrl : Tree := (.split 0 189 .leaf (.split 0 381 (.split 2 4 .leaf (.split 0 253 .leaf (.split 0 304 .leaf (.split 0 338 (.split 0 320 .leaf (.split 0 329 (.split 0 324 .leaf (.split 0 326 .leaf (.split 0 327 .leaf (.split 0 328 .leaf .leaf)))) .leaf)) .leaf)))) (.split 2 4 .leaf .leaf)))
private theorem h131rrrrrlrl : Good 13 1 b131rrrrrlrl := fun _ h => sound (by decide) 1 t131rrrrrlrl (by decide +kernel) h
private def b131rrrrrlrr : Box := right b131rrrrrlr 2 5
private def t131rrrrrlrr : Tree := (.split 0 189 (.split 0 125 (.split 2 7 (.split 0 107 (.split 2 6 .leaf (.split 0 100 (.split 0 96 .leaf (.split 0 98 .leaf .leaf)) .leaf)) (.split 2 6 .leaf .leaf)) .leaf) (.split 2 7 (.split 0 151 (.split 2 6 (.split 0 137 .leaf (.split 0 144 (.split 0 140 .leaf .leaf) .leaf)) .leaf) .leaf) .leaf)) .leaf)
private theorem h131rrrrrlrr : Good 13 1 b131rrrrrlrr := fun _ h => sound (by decide) 1 t131rrrrrlrr (by decide +kernel) h
private theorem h131rrrrrlr : Good 13 1 b131rrrrrlr := bisect b131rrrrrlr 2 5 h131rrrrrlrl h131rrrrrlrr
private theorem h131rrrrrl : Good 13 1 b131rrrrrl := bisect b131rrrrrl 0 93 h131rrrrrll h131rrrrrlr
private def b131rrrrrr : Box := right b131rrrrr 2 9
private def b131rrrrrrl : Box := left b131rrrrrr 0 93
private def b131rrrrrrll : Box := left b131rrrrrrl 2 21
private def b131rrrrrrlll : Box := left b131rrrrrrll 0 61
private def b131rrrrrrllll : Box := left b131rrrrrrlll 2 13
private def t131rrrrrrllll : Tree := (.split 0 52 (.split 0 48 .leaf (.split 2 11 .leaf (.split 0 50 .leaf (.split 2 12 .leaf (.split 0 51 .leaf .leaf))))) (.split 0 56 (.split 2 11 .leaf (.split 0 54 (.split 2 12 .leaf .leaf) .leaf)) (.split 2 11 (.split 0 58 (.split 2 10 .leaf (.split 0 57 .leaf .leaf)) (.split 2 10 .leaf .leaf)) .leaf)))
private theorem h131rrrrrrllll : Good 13 1 b131rrrrrrllll := fun _ h => sound (by decide) 1 t131rrrrrrllll (by decide +kernel) h
private def b131rrrrrrlllr : Box := right b131rrrrrrlll 2 13
private def t131rrrrrrlllr : Tree := (.split 0 52 (.split 2 16 (.split 0 48 (.split 2 14 .leaf (.split 0 46 .leaf (.split 2 15 (.split 0 47 .leaf .leaf) .leaf))) (.split 0 50 (.split 2 14 (.split 0 49 .leaf .leaf) .leaf) .leaf)) .leaf) .leaf)
private theorem h131rrrrrrlllr : Good 13 1 b131rrrrrrlllr := fun _ h => sound (by decide) 1 t131rrrrrrlllr (by decide +kernel) h
private theorem h131rrrrrrlll : Good 13 1 b131rrrrrrlll := bisect b131rrrrrrlll 2 13 h131rrrrrrllll h131rrrrrrlllr
private def b131rrrrrrllr : Box := right b131rrrrrrll 0 61
private def t131rrrrrrllr : Tree := (.split 2 13 (.split 0 74 (.split 0 67 (.split 2 11 (.split 0 64 (.split 2 10 (.split 0 62 .leaf .leaf) .leaf) .leaf) .leaf) .leaf) .leaf) .leaf)
private theorem h131rrrrrrllr : Good 13 1 b131rrrrrrllr := fun _ h => sound (by decide) 1 t131rrrrrrllr (by decide +kernel) h
private theorem h131rrrrrrll : Good 13 1 b131rrrrrrll := bisect b131rrrrrrll 0 61 h131rrrrrrlll h131rrrrrrllr
private def b131rrrrrrlr : Box := right b131rrrrrrl 2 21
private def t131rrrrrrlr : Tree := .leaf
private theorem h131rrrrrrlr : Good 13 1 b131rrrrrrlr := fun _ h => sound (by decide) 1 t131rrrrrrlr (by decide +kernel) h
private theorem h131rrrrrrl : Good 13 1 b131rrrrrrl := bisect b131rrrrrrl 2 21 h131rrrrrrll h131rrrrrrlr
private def b131rrrrrrr : Box := right b131rrrrrr 0 93
private def t131rrrrrrr : Tree := .leaf
private theorem h131rrrrrrr : Good 13 1 b131rrrrrrr := fun _ h => sound (by decide) 1 t131rrrrrrr (by decide +kernel) h
private theorem h131rrrrrr : Good 13 1 b131rrrrrr := bisect b131rrrrrr 0 93 h131rrrrrrl h131rrrrrrr
private theorem h131rrrrr : Good 13 1 b131rrrrr := bisect b131rrrrr 2 9 h131rrrrrl h131rrrrrr
private theorem h131rrrr : Good 13 1 b131rrrr := bisect b131rrrr 0 45 h131rrrrl h131rrrrr
private theorem h131rrr : Good 13 1 b131rrr := bisect b131rrr 2 3 h131rrrl h131rrrr
private theorem h131rr : Good 13 1 b131rr := bisect b131rr 0 21 h131rrl h131rrr
private theorem h131r : Good 13 1 b131r := bisect b131r 0 9 h131rl h131rr
private theorem h131 : Good 13 1 initial := bisect initial 0 3 h131l h131r
private def b132l : Box := left initial 0 3
private def t132l : Tree := .leaf
private theorem h132l : Good 13 2 b132l := fun _ h => sound (by decide) 2 t132l (by decide +kernel) h
private def b132r : Box := right initial 0 3
private def b132rl : Box := left b132r 1 3
private def t132rl : Tree := .leaf
private theorem h132rl : Good 13 2 b132rl := fun _ h => sound (by decide) 2 t132rl (by decide +kernel) h
private def b132rr : Box := right b132r 1 3
private def b132rrl : Box := left b132rr 0 9
private def t132rrl : Tree := .leaf
private theorem h132rrl : Good 13 2 b132rrl := fun _ h => sound (by decide) 2 t132rrl (by decide +kernel) h
private def b132rrr : Box := right b132rr 0 9
private def b132rrrl : Box := left b132rrr 0 21
private def t132rrrl : Tree := .leaf
private theorem h132rrrl : Good 13 2 b132rrrl := fun _ h => sound (by decide) 2 t132rrrl (by decide +kernel) h
private def b132rrrr : Box := right b132rrr 0 21
private def b132rrrrl : Box := left b132rrrr 1 9
private def t132rrrrl : Tree := .leaf
private theorem h132rrrrl : Good 13 2 b132rrrrl := fun _ h => sound (by decide) 2 t132rrrrl (by decide +kernel) h
private def b132rrrrr : Box := right b132rrrr 1 9
private def b132rrrrrl : Box := left b132rrrrr 0 45
private def b132rrrrrll : Box := left b132rrrrrl 1 21
private def t132rrrrrll : Tree := .leaf
private theorem h132rrrrrll : Good 13 2 b132rrrrrll := fun _ h => sound (by decide) 2 t132rrrrrll (by decide +kernel) h
private def b132rrrrrlr : Box := right b132rrrrrl 1 21
private def b132rrrrrlrl : Box := left b132rrrrrlr 0 29
private def t132rrrrrlrl : Tree := .leaf
private theorem h132rrrrrlrl : Good 13 2 b132rrrrrlrl := fun _ h => sound (by decide) 2 t132rrrrrlrl (by decide +kernel) h
private def b132rrrrrlrr : Box := right b132rrrrrlr 0 29
private def b132rrrrrlrrl : Box := left b132rrrrrlrr 1 45
private def t132rrrrrlrrl : Tree := .leaf
private theorem h132rrrrrlrrl : Good 13 2 b132rrrrrlrrl := fun _ h => sound (by decide) 2 t132rrrrrlrrl (by decide +kernel) h
private def b132rrrrrlrrr : Box := right b132rrrrrlrr 1 45
private def b132rrrrrlrrrl : Box := left b132rrrrrlrrr 0 36
private def b132rrrrrlrrrll : Box := left b132rrrrrlrrrl 1 93
private def t132rrrrrlrrrll : Tree := .leaf
private theorem h132rrrrrlrrrll : Good 13 2 b132rrrrrlrrrll := fun _ h => sound (by decide) 2 t132rrrrrlrrrll (by decide +kernel) h
private def b132rrrrrlrrrlr : Box := right b132rrrrrlrrrl 1 93
private def b132rrrrrlrrrlrl : Box := left b132rrrrrlrrrlr 0 32
private def t132rrrrrlrrrlrl : Tree := (.split 1 189 .leaf (.split 1 381 .leaf (.split 0 30 .leaf (.split 1 765 .leaf (.split 0 31 .leaf (.split 1 1533 (.split 1 1021 .leaf (.split 1 1226 (.split 1 1114 (.split 1 1066 (.split 1 1043 .leaf (.split 1 1054 .leaf (.split 1 1060 (.split 1 1057 (.split 1 1055 .leaf .leaf) .leaf) .leaf))) .leaf) .leaf) .leaf)) .leaf))))))
private theorem h132rrrrrlrrrlrl : Good 13 2 b132rrrrrlrrrlrl := fun _ h => sound (by decide) 2 t132rrrrrlrrrlrl (by decide +kernel) h
private def b132rrrrrlrrrlrr : Box := right b132rrrrrlrrrlr 0 32
private def b132rrrrrlrrrlrrl : Box := left b132rrrrrlrrrlrr 1 189
private def t132rrrrrlrrrlrrl : Tree := (.split 0 34 .leaf (.split 1 125 .leaf (.split 1 151 (.split 0 35 .leaf (.split 1 137 (.split 1 131 (.split 1 128 .leaf (.split 1 129 .leaf (.split 1 130 .leaf .leaf))) .leaf) .leaf)) (.split 0 35 (.split 1 168 (.split 1 159 .leaf (.split 1 163 .leaf .leaf)) .leaf) .leaf))))
private theorem h132rrrrrlrrrlrrl : Good 13 2 b132rrrrrlrrrlrrl := fun _ h => sound (by decide) 2 t132rrrrrlrrrlrrl (by decide +kernel) h
private def b132rrrrrlrrrlrrr : Box := right b132rrrrrlrrrlrr 1 189
private def t132rrrrrlrrrlrrr : Tree := (.split 0 34 (.split 1 381 (.split 1 253 (.split 0 33 .leaf (.split 1 217 .leaf (.split 1 234 (.split 1 225 (.split 1 221 .leaf (.split 1 223 .leaf .leaf)) .leaf) .leaf))) (.split 0 33 (.split 1 304 .leaf (.split 1 338 .leaf (.split 1 358 .leaf (.split 1 369 (.split 1 363 (.split 1 360 .leaf (.split 1 361 .leaf .leaf)) .leaf) .leaf)))) .leaf)) .leaf) .leaf)
private theorem h132rrrrrlrrrlrrr : Good 13 2 b132rrrrrlrrrlrrr := fun _ h => sound (by decide) 2 t132rrrrrlrrrlrrr (by decide +kernel) h
private theorem h132rrrrrlrrrlrr : Good 13 2 b132rrrrrlrrrlrr := bisect b132rrrrrlrrrlrr 1 189 h132rrrrrlrrrlrrl h132rrrrrlrrrlrrr
private theorem h132rrrrrlrrrlr : Good 13 2 b132rrrrrlrrrlr := bisect b132rrrrrlrrrlr 0 32 h132rrrrrlrrrlrl h132rrrrrlrrrlrr
private theorem h132rrrrrlrrrl : Good 13 2 b132rrrrrlrrrl := bisect b132rrrrrlrrrl 1 93 h132rrrrrlrrrll h132rrrrrlrrrlr
private def b132rrrrrlrrrr : Box := right b132rrrrrlrrr 0 36
private def b132rrrrrlrrrrl : Box := left b132rrrrrlrrrr 1 93
private def b132rrrrrlrrrrll : Box := left b132rrrrrlrrrrl 0 40
private def t132rrrrrlrrrrll : Tree := (.split 1 61 .leaf (.split 1 74 .leaf (.split 0 38 .leaf (.split 1 83 (.split 0 39 .leaf (.split 1 78 (.split 1 76 .leaf .leaf) .leaf)) (.split 0 39 (.split 1 88 (.split 1 85 (.split 1 84 .leaf .leaf) .leaf) .leaf) .leaf)))))
private theorem h132rrrrrlrrrrll : Good 13 2 b132rrrrrlrrrrll := fun _ h => sound (by decide) 2 t132rrrrrlrrrrll (by decide +kernel) h
private def b132rrrrrlrrrrlr : Box := right b132rrrrrlrrrrl 0 40
private def t132rrrrrlrrrrlr : Tree := (.split 1 61 (.split 1 52 .leaf (.split 0 42 .leaf (.split 1 56 (.split 0 43 .leaf (.split 0 44 .leaf (.split 1 54 (.split 1 53 .leaf .leaf) .leaf))) (.split 0 43 (.split 1 58 .leaf (.split 1 59 .leaf (.split 1 60 .leaf .leaf))) .leaf)))) (.split 1 74 (.split 0 42 (.split 1 67 (.split 0 41 .leaf (.split 1 64 .leaf .leaf)) (.split 0 41 (.split 1 70 (.split 1 68 .leaf (.split 1 69 .leaf .leaf)) .leaf) .leaf)) .leaf) .leaf))
private theorem h132rrrrrlrrrrlr : Good 13 2 b132rrrrrlrrrrlr := fun _ h => sound (by decide) 2 t132rrrrrlrrrrlr (by decide +kernel) h
private theorem h132rrrrrlrrrrl : Good 13 2 b132rrrrrlrrrrl := bisect b132rrrrrlrrrrl 0 40 h132rrrrrlrrrrll h132rrrrrlrrrrlr
private def b132rrrrrlrrrrr : Box := right b132rrrrrlrrrr 1 93
private def t132rrrrrlrrrrr : Tree := (.split 0 40 (.split 1 189 (.split 1 125 (.split 0 38 (.split 1 107 (.split 0 37 .leaf (.split 1 100 (.split 1 96 (.split 1 94 .leaf (.split 1 95 .leaf .leaf)) .leaf) .leaf)) (.split 0 37 (.split 1 115 (.split 1 111 (.split 1 109 .leaf .leaf) .leaf) .leaf) .leaf)) .leaf) .leaf) .leaf) .leaf)
private theorem h132rrrrrlrrrrr : Good 13 2 b132rrrrrlrrrrr := fun _ h => sound (by decide) 2 t132rrrrrlrrrrr (by decide +kernel) h
private theorem h132rrrrrlrrrr : Good 13 2 b132rrrrrlrrrr := bisect b132rrrrrlrrrr 1 93 h132rrrrrlrrrrl h132rrrrrlrrrrr
private theorem h132rrrrrlrrr : Good 13 2 b132rrrrrlrrr := bisect b132rrrrrlrrr 0 36 h132rrrrrlrrrl h132rrrrrlrrrr
private theorem h132rrrrrlrr : Good 13 2 b132rrrrrlrr := bisect b132rrrrrlrr 1 45 h132rrrrrlrrl h132rrrrrlrrr
private theorem h132rrrrrlr : Good 13 2 b132rrrrrlr := bisect b132rrrrrlr 0 29 h132rrrrrlrl h132rrrrrlrr
private theorem h132rrrrrl : Good 13 2 b132rrrrrl := bisect b132rrrrrl 1 21 h132rrrrrll h132rrrrrlr
private def b132rrrrrr : Box := right b132rrrrr 0 45
private def b132rrrrrrl : Box := left b132rrrrrr 1 21
private def b132rrrrrrll : Box := left b132rrrrrrl 0 93
private def t132rrrrrrll : Tree := .leaf
private theorem h132rrrrrrll : Good 13 2 b132rrrrrrll := fun _ h => sound (by decide) 2 t132rrrrrrll (by decide +kernel) h
private def b132rrrrrrlr : Box := right b132rrrrrrl 0 93
private def b132rrrrrrlrl : Box := left b132rrrrrrlr 1 13
private def t132rrrrrrlrl : Tree := .leaf
private theorem h132rrrrrrlrl : Good 13 2 b132rrrrrrlrl := fun _ h => sound (by decide) 2 t132rrrrrrlrl (by decide +kernel) h
private def b132rrrrrrlrr : Box := right b132rrrrrrlr 1 13
private def b132rrrrrrlrrl : Box := left b132rrrrrrlrr 0 189
private def t132rrrrrrlrrl : Tree := (.split 1 16 .leaf (.split 0 125 (.split 1 18 .leaf (.split 0 107 .leaf (.split 1 19 .leaf (.split 0 115 .leaf (.split 1 20 .leaf (.split 0 120 .leaf (.split 0 122 (.split 0 121 .leaf .leaf) .leaf))))))) (.split 1 18 .leaf (.split 0 151 (.split 1 19 .leaf (.split 0 137 (.split 1 20 .leaf .leaf) (.split 1 20 (.split 0 144 (.split 0 140 .leaf .leaf) .leaf) .leaf))) (.split 1 19 (.split 0 168 .leaf (.split 0 178 (.split 0 173 (.split 0 170 .leaf .leaf) .leaf) .leaf)) .leaf)))))
private theorem h132rrrrrrlrrl : Good 13 2 b132rrrrrrlrrl := fun _ h => sound (by decide) 2 t132rrrrrrlrrl (by decide +kernel) h
private def b132rrrrrrlrrr : Box := right b132rrrrrrlrr 0 189
private def b132rrrrrrlrrrl : Box := left b132rrrrrrlrrr 1 16
private def t132rrrrrrlrrrl : Tree := (.split 0 381 .leaf (.split 1 14 .leaf (.split 0 765 (.split 1 15 .leaf (.split 0 509 .leaf (.split 0 612 .leaf (.split 0 680 .leaf (.split 0 720 .leaf (.split 0 742 (.split 0 731 (.split 0 725 (.split 0 722 .leaf (.split 0 723 .leaf (.split 0 724 .leaf .leaf))) .leaf) .leaf) .leaf)))))) (.split 1 15 .leaf .leaf))))
private theorem h132rrrrrrlrrrl : Good 13 2 b132rrrrrrlrrrl := fun _ h => sound (by decide) 2 t132rrrrrrlrrrl (by decide +kernel) h
private def b132rrrrrrlrrrr : Box := right b132rrrrrrlrrr 1 16
private def t132rrrrrrlrrrr : Tree := (.split 0 381 (.split 1 18 (.split 0 253 (.split 0 217 .leaf (.split 1 17 .leaf (.split 0 234 (.split 0 225 (.split 0 221 (.split 0 219 .leaf (.split 0 220 .leaf .leaf)) .leaf) .leaf) .leaf))) (.split 0 304 (.split 1 17 .leaf .leaf) (.split 1 17 (.split 0 338 (.split 0 320 .leaf (.split 0 329 (.split 0 324 .leaf (.split 0 326 .leaf (.split 0 327 .leaf (.split 0 328 .leaf .leaf)))) .leaf)) .leaf) .leaf))) .leaf) .leaf)
private theorem h132rrrrrrlrrrr : Good 13 2 b132rrrrrrlrrrr := fun _ h => sound (by decide) 2 t132rrrrrrlrrrr (by decide +kernel) h
private theorem h132rrrrrrlrrr : Good 13 2 b132rrrrrrlrrr := bisect b132rrrrrrlrrr 1 16 h132rrrrrrlrrrl h132rrrrrrlrrrr
private theorem h132rrrrrrlrr : Good 13 2 b132rrrrrrlrr := bisect b132rrrrrrlrr 0 189 h132rrrrrrlrrl h132rrrrrrlrrr
private theorem h132rrrrrrlr : Good 13 2 b132rrrrrrlr := bisect b132rrrrrrlr 1 13 h132rrrrrrlrl h132rrrrrrlrr
private theorem h132rrrrrrl : Good 13 2 b132rrrrrrl := bisect b132rrrrrrl 0 93 h132rrrrrrll h132rrrrrrlr
private def b132rrrrrrr : Box := right b132rrrrrr 1 21
private def b132rrrrrrrl : Box := left b132rrrrrrr 0 93
private def b132rrrrrrrll : Box := left b132rrrrrrrl 1 45
private def b132rrrrrrrlll : Box := left b132rrrrrrrll 0 61
private def b132rrrrrrrllll : Box := left b132rrrrrrrlll 1 29
private def t132rrrrrrrllll : Tree := .leaf
private theorem h132rrrrrrrllll : Good 13 2 b132rrrrrrrllll := fun _ h => sound (by decide) 2 t132rrrrrrrllll (by decide +kernel) h
private def b132rrrrrrrlllr : Box := right b132rrrrrrrlll 1 29
private def b132rrrrrrrlllrl : Box := left b132rrrrrrrlllr 0 52
private def t132rrrrrrrlllrl : Tree := (.split 1 36 .leaf (.split 0 48 .leaf (.split 1 40 .leaf (.split 0 50 (.split 1 42 .leaf (.split 1 43 .leaf (.split 0 49 (.split 1 44 .leaf .leaf) .leaf))) (.split 1 42 (.split 0 51 (.split 1 41 .leaf .leaf) .leaf) .leaf)))))
private theorem h132rrrrrrrlllrl : Good 13 2 b132rrrrrrrlllrl := fun _ h => sound (by decide) 2 t132rrrrrrrlllrl (by decide +kernel) h
private def b132rrrrrrrlllrr : Box := right b132rrrrrrrlllr 0 52
private def t132rrrrrrrlllrr : Tree := (.split 1 36 (.split 0 56 .leaf (.split 1 32 .leaf (.split 0 58 (.split 1 34 .leaf (.split 1 35 (.split 0 57 .leaf .leaf) .leaf)) (.split 1 34 (.split 0 59 .leaf (.split 1 33 (.split 0 60 .leaf .leaf) .leaf)) .leaf)))) (.split 0 56 (.split 1 40 (.split 0 54 (.split 1 38 .leaf (.split 0 53 (.split 1 39 .leaf .leaf) .leaf)) (.split 1 38 (.split 0 55 (.split 1 37 .leaf .leaf) .leaf) .leaf)) .leaf) .leaf))
private theorem h132rrrrrrrlllrr : Good 13 2 b132rrrrrrrlllrr := fun _ h => sound (by decide) 2 t132rrrrrrrlllrr (by decide +kernel) h
private theorem h132rrrrrrrlllr : Good 13 2 b132rrrrrrrlllr := bisect b132rrrrrrrlllr 0 52 h132rrrrrrrlllrl h132rrrrrrrlllrr
private theorem h132rrrrrrrlll : Good 13 2 b132rrrrrrrlll := bisect b132rrrrrrrlll 1 29 h132rrrrrrrllll h132rrrrrrrlllr
private def b132rrrrrrrllr : Box := right b132rrrrrrrll 0 61
private def b132rrrrrrrllrl : Box := left b132rrrrrrrllr 1 29
private def b132rrrrrrrllrll : Box := left b132rrrrrrrllrl 0 74
private def t132rrrrrrrllrll : Tree := (.split 1 25 .leaf (.split 0 67 .leaf (.split 1 27 .leaf (.split 0 70 (.split 1 28 .leaf (.split 0 68 .leaf (.split 0 69 .leaf .leaf))) (.split 0 72 (.split 1 28 .leaf .leaf) .leaf)))))
private theorem h132rrrrrrrllrll : Good 13 2 b132rrrrrrrllrll := fun _ h => sound (by decide) 2 t132rrrrrrrllrll (by decide +kernel) h
private def b132rrrrrrrllrlr : Box := right b132rrrrrrrllrl 0 74
private def t132rrrrrrrllrlr : Tree := (.split 1 25 (.split 0 83 .leaf (.split 1 23 .leaf (.split 0 88 (.split 1 24 .leaf (.split 0 85 (.split 0 84 .leaf .leaf) .leaf)) (.split 1 24 (.split 0 90 .leaf .leaf) .leaf)))) (.split 0 83 (.split 1 27 (.split 0 78 (.split 1 26 .leaf (.split 0 76 (.split 0 75 .leaf .leaf) .leaf)) (.split 0 80 (.split 1 26 (.split 0 79 .leaf .leaf) .leaf) .leaf)) .leaf) .leaf))
private theorem h132rrrrrrrllrlr : Good 13 2 b132rrrrrrrllrlr := fun _ h => sound (by decide) 2 t132rrrrrrrllrlr (by decide +kernel) h
private theorem h132rrrrrrrllrl : Good 13 2 b132rrrrrrrllrl := bisect b132rrrrrrrllrl 0 74 h132rrrrrrrllrll h132rrrrrrrllrlr
private def b132rrrrrrrllrr : Box := right b132rrrrrrrllr 1 29
private def t132rrrrrrrllrr : Tree := (.split 0 74 (.split 1 36 (.split 0 67 (.split 1 32 (.split 0 64 (.split 1 30 .leaf (.split 0 62 .leaf (.split 1 31 .leaf .leaf))) (.split 1 30 (.split 0 65 .leaf (.split 0 66 .leaf .leaf)) .leaf)) .leaf) .leaf) .leaf) .leaf)
private theorem h132rrrrrrrllrr : Good 13 2 b132rrrrrrrllrr := fun _ h => sound (by decide) 2 t132rrrrrrrllrr (by decide +kernel) h
private theorem h132rrrrrrrllr : Good 13 2 b132rrrrrrrllr := bisect b132rrrrrrrllr 1 29 h132rrrrrrrllrl h132rrrrrrrllrr
private theorem h132rrrrrrrll : Good 13 2 b132rrrrrrrll := bisect b132rrrrrrrll 0 61 h132rrrrrrrlll h132rrrrrrrllr
private def b132rrrrrrrlr : Box := right b132rrrrrrrl 1 45
private def t132rrrrrrrlr : Tree := (.split 0 61 (.split 1 93 (.split 0 52 (.split 1 61 (.split 0 48 (.split 1 52 (.split 1 48 (.split 0 46 .leaf (.split 0 47 .leaf (.split 1 46 .leaf .leaf))) (.split 0 46 (.split 1 50 .leaf (.split 1 51 .leaf .leaf)) .leaf)) .leaf) .leaf) .leaf) .leaf) .leaf) .leaf)
private theorem h132rrrrrrrlr : Good 13 2 b132rrrrrrrlr := fun _ h => sound (by decide) 2 t132rrrrrrrlr (by decide +kernel) h
private theorem h132rrrrrrrl : Good 13 2 b132rrrrrrrl := bisect b132rrrrrrrl 1 45 h132rrrrrrrll h132rrrrrrrlr
private def b132rrrrrrrr : Box := right b132rrrrrrr 0 93
private def t132rrrrrrrr : Tree := (.split 1 45 (.split 0 189 (.split 1 29 (.split 0 125 (.split 1 25 (.split 0 107 (.split 1 23 (.split 0 100 (.split 1 22 .leaf (.split 0 96 .leaf (.split 0 98 .leaf .leaf))) (.split 1 22 .leaf .leaf)) .leaf) (.split 1 23 (.split 0 115 (.split 1 22 (.split 0 111 (.split 0 109 (.split 0 108 .leaf .leaf) .leaf) .leaf) .leaf) .leaf) .leaf)) .leaf) .leaf) .leaf) .leaf) .leaf)
private theorem h132rrrrrrrr : Good 13 2 b132rrrrrrrr := fun _ h => sound (by decide) 2 t132rrrrrrrr (by decide +kernel) h
private theorem h132rrrrrrr : Good 13 2 b132rrrrrrr := bisect b132rrrrrrr 0 93 h132rrrrrrrl h132rrrrrrrr
private theorem h132rrrrrr : Good 13 2 b132rrrrrr := bisect b132rrrrrr 1 21 h132rrrrrrl h132rrrrrrr
private theorem h132rrrrr : Good 13 2 b132rrrrr := bisect b132rrrrr 0 45 h132rrrrrl h132rrrrrr
private theorem h132rrrr : Good 13 2 b132rrrr := bisect b132rrrr 1 9 h132rrrrl h132rrrrr
private theorem h132rrr : Good 13 2 b132rrr := bisect b132rrr 0 21 h132rrrl h132rrrr
private theorem h132rr : Good 13 2 b132rr := bisect b132rr 0 9 h132rrl h132rrr
private theorem h132r : Good 13 2 b132r := bisect b132r 1 3 h132rl h132rr
private theorem h132 : Good 13 2 initial := bisect initial 0 3 h132l h132r
theorem separation {q : ℕ} (hq : q=7 ∨ q=11 ∨ q=13) (k : Fin 3) (e : I → ℕ)
    (he : ∀ i,0<e i) : Separated (face q k e) := by
  have mem : ∀ i,(initial i).Contains (e i) := fun i => ⟨he i,by simp [initial]⟩
  rcases hq with rfl|rfl|rfl <;> fin_cases k
  · exact h70 e mem
  · exact h71 e mem
  · exact h72 e mem
  · exact h110 e mem
  · exact h111 e mem
  · exact h112 e mem
  · exact h130 e mem
  · exact h131 e mem
  · exact h132 e mem
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

/- Finitely many non-dyadic A245212 solutions on any fixed set of primes.
Truncate each exponent at twice the largest prime. The solutions of each
truncated pattern form an antichain, which is finite by Dickson's lemma. -/
namespace OMA.FixedPrimes245212
open Finset OMA.Smooth245212 OMA.Abundance245212 OMA.CapOrder245212
open scoped ArithmeticFunction.sigma

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def Exception (n : ℕ) : Prop :=
  OeisA245212.a n = (σ 1 n:ℤ) ∧ ¬∃ u : ℕ, n=2^u

private theorem axis (p : ι → ℕ) (hp : ∀ i,Nat.Prime (p i)) (hinj : Function.Injective p)
    {e f : ι → ℕ} (i : ι) (other : ∀ j,j≠i → e j=f j)
    (he : Exception (total p e)) (hf : Exception (total p f)) : e i=f i := by
  let m := ∏ j∈univ.erase i,(p j)^(e j)
  have em : total p e=m*(p i)^(e i) := (prod_erase_mul _ _ (mem_univ i)).symm
  have fm : total p f=m*(p i)^(f i) := by
    rw [total,←prod_erase_mul _ _ (mem_univ i)]
    congr 1
    exact prod_congr rfl fun j hj => by rw [other j (mem_erase.mp hj).1]
  have hm : m≠0 := prod_ne_zero_iff.mpr (fun j _ => pow_ne_zero _ (hp j).ne_zero)
  have cp : (p i).Coprime m := Nat.Coprime.prod_right (fun j hj =>
    ((Nat.coprime_primes (hp i) (hp j)).mpr (fun h => (mem_erase.mp hj).1 (hinj h).symm)).pow_right _)
  rcases unique_exponent hm (hp i) ((hp i).coprime_iff_not_dvd.mp cp)
      (em ▸ he.1) (fm ▸ hf.1) with yes|⟨p2,m1⟩
  · exact yes
  · exact (he.2 ⟨e i,by simpa [m1,p2] using em⟩).elim

theorem finite_vectors (p : ι → ℕ) (hp : ∀ i,Nat.Prime (p i)) (hinj : Function.Injective p) :
    {e : ι → ℕ | Exception (total p e)}.Finite := by
  classical
  let H := 2*(∑ i,p i)
  let cap (e : ι → ℕ) (i : ι) : Fin (H+1) := ⟨min H (e i),by omega⟩
  apply Set.Finite.of_finite_fibers cap (Set.toFinite _)
  intro pat _
  apply WellQuasiOrderedLE.finite_of_isAntichain
  intro e he f hf ne ef
  have hE : Exception (total p e) := he.1
  have hF : Exception (total p f) := hf.1
  have capped : cap e=cap f := he.2.trans hf.2.symm
  have bound (i : ι) : 2*p i≤H := Nat.mul_le_mul_left 2
    (single_le_sum (f:=p) (fun _ _ => Nat.zero_le _) (mem_univ i))
  have high (i : ι) (lt : e i<f i) : H≤e i := by
    have hh := congrArg Fin.val (congrFun capped i)
    change min H (e i)=min H (f i) at hh
    omega
  obtain ⟨i,lt⟩ : ∃ i,e i<f i := by
    by_contra! h; exact ne (funext fun j => Nat.le_antisymm (ef j) (h j))
  by_cases only : ∀ j,j≠i → e j=f j
  · exact lt.ne (axis p hp hinj i only hE hF)
  · push Not at only
    obtain ⟨j,ji,ej⟩ := only
    have lj := (ef j).lt_of_ne ej
    have rise := strict_of_changes p hp ef lt (fun l _ => by
      by_cases li : l=i
      · exact ⟨j,li ▸ ji,(bound l).trans (high j lj)⟩
      · exact ⟨i,Ne.symm li,(bound l).trans (high i lt)⟩)
    rw [normalized_of_eq p hp hinj _ hE.1,normalized_of_eq p hp hinj _ hF.1] at rise
    exact rise.false

theorem finite (P : Finset ℕ) :
    {n : ℕ | 0<n ∧ n.primeFactors⊆P ∧ Exception n}.Finite := by
  classical
  let S := P.filter Nat.Prime
  let p (i : S) := i.val
  have hp (i : S) : Nat.Prime (p i) := (mem_filter.mp i.property).2
  have h := (finite_vectors p hp Subtype.val_injective).image (total p)
  refine h.subset ?_
  intro n hn
  let e (i : S) := n.factorization i.val
  have prod : total p e=n := by
    unfold total
    change (∏ i:S,i.val^(n.factorization i.val))=n
    rw [Finset.prod_coe_sort S (fun q => q^n.factorization q)]
    apply Eq.symm
    refine (Nat.prod_primeFactors_pow_factorization hn.1.ne').trans (prod_subset ?_ ?_)
    · intro q hq; exact mem_filter.mpr ⟨hn.2.1 hq,Nat.prime_of_mem_primeFactors hq⟩
    · intro q hq hnq
      have h0 : n.factorization q=0 := Finsupp.notMem_support_iff.mp hnq
      simp [h0]
  exact ⟨e,show Exception (total p e) from prod.symm ▸ hn.2.2,prod⟩

end OMA.FixedPrimes245212

end

section

/- A large fourth prime and a large exponent in the first three positions
force the normalized divisor score to approach one of the certified faces. -/
namespace OMA.OddFaces245212
open Finset OMA.Smooth245212

def threshold : ℕ := 10000000000

private theorem xbounds {p : ℕ} (hp : 3≤p) (e : Option ℕ) : 1≤X p e ∧ X p e≤3/2 := by
  have h : 1<p := by omega
  have h' : (3:ℚ)≤p := by exact_mod_cast hp
  have yl := y_nonneg h e
  have yu := y_one h e
  constructor
  · exact le_add_of_nonneg_right (div_nonneg (by linarith only [yu]) (by linarith only [h']))
  · unfold X
    have rhs : (1-Y p e)/((p:ℚ)-1) ≤ 1/2 :=
      (div_le_iff₀ (by linarith only [h'])).2 (by linarith only [yl,h'])
    linarith only [rhs]

private theorem diff {p : ℕ} (hp : 3≤p) (e : ℕ) :
    0≤limitX p-X p (some e) ∧ limitX p-X p (some e)≤Y p (some e) := by
  have h : (3:ℚ)≤p := by exact_mod_cast hp
  have yl := y_nonneg (show 1<p by omega) (some e)
  have hv : limitX p-X p (some e) = Y p (some e)/((p:ℚ)-1) := by
    simp only [limitX,X,Y]; ring
  rw [hv]
  exact ⟨div_nonneg yl (by linarith),div_le_self yl (by linarith)⟩

private theorem xlarge {p : ℕ} (hp : threshold<p) (e : ℕ) :
    1≤X p (some e) ∧ X p (some e)≤1+1/10000000000 := by
  have hp' : (10000000001:ℚ)≤p := by
    exact_mod_cast (show 10000000001≤p from hp)
  have zl := y_nonneg (by dsimp [threshold] at hp; omega : 1<p) (some e)
  refine ⟨(xbounds (by dsimp [threshold] at hp; omega) _).1,?_⟩
  unfold X
  exact add_le_add_right ((div_le_iff₀ (by linarith only [hp'])).2
    (by linarith only [zl,hp'])) 1

private theorem ysmall {p e : ℕ} (hp : Nat.Prime p) (he : threshold≤e) :
    Y p (some e)<2/10000000000 := by
  have h := OMA.CapOrder245212.y_short hp e
  have h' : (10000000000:ℚ)≤e := by exact_mod_cast he
  have z := y_nonneg hp.one_lt (some e)
  nlinarith only [h,mul_nonneg z (show 0≤(e:ℚ)+1-10000000000 by linarith only [h'])]

def preScore (q r d : ℕ) (e : I → ℕ) : ℚ :=
  (∏ i : Fin 3, X (bases q i) (some (e i.castSucc))) * X r (some d) +
  (∏ i : Fin 3, Y (bases q i) (some (e i.castSucc))) * Y r (some d)

theorem near_face {q r : ℕ} (hq : Nat.Prime q) (hq' : 3≤q) (hr : threshold<r)
    (e : I → ℕ) (d : ℕ) (k : Fin 3) (large : threshold≤e k.castSucc)
    (eq : preScore q r d e=2) : ¬Separated (face q k e) := by
  let p := bases q
  let x (i : Fin 3) := X (p i) (some (e i.castSucc))
  let y (i : Fin 3) := Y (p i) (some (e i.castSucc))
  let U := ∏ i∈univ.erase k, x i
  let V := ∏ i∈univ.erase k, y i
  have pp (i : Fin 3) : Nat.Prime (p i) := by fin_cases i <;> simp [p,bases,hq] <;> decide
  have h3 (i : Fin 3) : 3≤p i := by fin_cases i <;> simp [p,bases,hq']
  have x0 (i : Fin 3) : 0≤x i := x_nonneg (pp i).one_lt _
  have x1 (i : Fin 3) : x i≤3/2 := (xbounds (h3 i) _).2
  have y0 (i : Fin 3) : 0≤y i := y_nonneg (pp i).one_lt _
  have y1 (i : Fin 3) : y i≤1 := y_one (pp i).one_lt _
  have u0 : 0≤U := prod_nonneg (fun i _ => x0 i)
  have u3 : U≤3 := by
    have h := prod_le_prod (s:=univ.erase k) (fun i _ => x0 i) (fun i _ => x1 i)
    have hc : (univ.erase k).card=2 := by simp
    simp only [prod_const,hc] at h
    norm_num at h ⊢
    linarith
  have v0 : 0≤V := prod_nonneg (fun i _ => y0 i)
  have v1 : V≤1 := prod_le_one (fun i _ => y0 i) (fun i _ => y1 i)
  have r1 : 1<r := by dsimp [threshold] at hr; omega
  have zr := y_nonneg r1 (some d)
  have ur := y_one r1 (some d)
  have xk0 := x0 k
  have xk1 := x1 k
  have yk0 := y0 k
  have yk1 : y k<2/10000000000 := ysmall (pp k) large
  have a := xlarge hr d
  have b := diff (h3 k) (e k.castSucc)
  change 0≤limitX (p k)-x k ∧ limitX (p k)-x k≤y k at b
  have f : face q k e=U*limitX (p k) := by
    rw [face,←prod_erase_mul _ _ (mem_univ k)]
    simp only [if_pos]
    congr 1
    exact prod_congr rfl fun i hi => if_neg (mem_erase.mp hi).1
  have xx : U*x k≤5 := (mul_le_mul u3 xk1 xk0 (by norm_num)).trans (by norm_num)
  have delta1 : U*x k*(X r (some d)-1) ≤ 5*(1/10000000000) :=
    mul_le_mul xx (by linarith only [a.2]) (by linarith only [a.1]) (by norm_num)
  have delta2 : V*y k*Y r (some d) ≤ y k :=
    (mul_le_of_le_one_right (mul_nonneg v0 yk0) ur).trans
      (mul_le_of_le_one_left yk0 v1)
  have delta3 : U*(limitX (p k)-x k)≤3*y k :=
    mul_le_mul u3 b.2 b.1 (by norm_num)
  have total : U*x k*X r (some d)+V*y k*Y r (some d)=2 := by
    change (∏ i,x i)*X r (some d)+(∏ i,y i)*Y r (some d)=2 at eq
    dsimp only [U,V]
    rw [prod_erase_mul _ _ (mem_univ k),prod_erase_mul _ _ (mem_univ k)]
    exact eq
  rw [f]
  unfold Separated gap
  push Not
  constructor
  · nlinarith only [total,delta1,delta2,yk1,mul_nonneg u0 b.1]
  · nlinarith only [total,delta3,yk1,mul_nonneg (mul_nonneg u0 xk0)
      (show 0≤X r (some d)-1 by linarith only [a.1]),mul_nonneg (mul_nonneg v0 yk0) zr]

end OMA.OddFaces245212

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

/- Bound the largest prime in an arbitrary ordered four-prime odd exception. -/
namespace OMA.OddFaces245212
open Finset OMA.Smooth245212
open scoped ArithmeticFunction.sigma

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

/-- Explicit uniform prime-support bound. No primality checks on
the cofactor are needed when taking this finite envelope. -/
def envelopeBound (t : ℕ) := t + ∑ m∈range (195^t+1), (W m+ArithmeticFunction.sigma 1 m)
abbrev primeBound := envelopeBound threshold

private theorem basic (t : ℕ) : t≤envelopeBound t := Nat.le_add_right t _
private theorem bounded (t m : ℕ) (h : m≤195^t) : W m+ArithmeticFunction.sigma 1 m≤envelopeBound t := by
  apply le_trans (single_le_sum (f:=fun m => W m+ArithmeticFunction.sigma 1 m)
    (fun _ _ => Nat.zero_le _) (mem_range.mpr (Nat.lt_succ_of_le h)))
  exact Nat.le_add_left _ t

theorem primeBound_ge : threshold≤primeBound := basic threshold

private theorem cofactor_size (a b c q t : ℕ) (ha : a≤t) (hb : b≤t) (hc : c≤t)
    (hq : q≤13) : 3^a*5^b*q^c≤195^t := by
  have h := Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_right (by decide : 0<3) ha)
    (Nat.pow_le_pow_right (by decide : 0<5) hb))
    ((Nat.pow_le_pow_left hq c).trans (Nat.pow_le_pow_right (by decide : 0<13) hc))
  simpa only [←mul_pow,show 3*5*13=(195:ℕ) by decide] using h

theorem last_prime_le {p e : Fin 4 → ℕ} (hp : ∀ i,Nat.Prime (p i)) (ord : StrictMono p)
    (odd : 3≤p 0) (positive : ∀ i,0<e i)
    (eq : OeisA245212.a (total p e)=(σ 1 (total p e):ℤ)) : p 3≤primeBound := by
  by_cases sm : p 3≤threshold
  · exact sm.trans primeBound_ge
  have high : threshold<p 3 := by omega
  have norm := normalized_of_eq p hp ord.injective _ eq
  have cap := cap_needed p e (fun i => (hp i).one_lt) 0 (positive 0) norm
  obtain ⟨a,b,c⟩ := small_bases hp ord odd (by unfold threshold at high; omega) cap
  let q := p 2
  let r := p 3
  have qq : q=7 ∨ q=11 ∨ q=13 := c
  have q13 : q≤13 := by rcases qq with h|h|h <;> omega
  have q3 : 3≤q := by rcases qq with h|h|h <;> omega
  have qp : Nat.Prime q := hp 2
  have pp (i : Fin 3) : p i.castSucc=bases q i := by
    fin_cases i <;> simp [bases,q,a,b]
  have ps : preScore q r (e 3) e=2 := by
    unfold normalized at norm
    rw [Fin.prod_univ_castSucc (fun i => X (p i) (some (e i))),
      Fin.prod_univ_castSucc (fun i => Y (p i) (some (e i)))] at norm
    simpa only [pp,preScore,r,show Fin.last 3=(3:Fin 4) by decide] using norm
  have low (i : Fin 3) : e i.castSucc<threshold := by
    by_contra! large
    exact near_face qp q3 high e (e 3) i large ps (separation qq i e positive)
  let m := 3^(e 0)*5^(e 1)*q^(e 2)
  have fact : total p e=m*r^(e 3) := by
    simp [total,Fin.prod_univ_four,m,r,q,a,b,mul_assoc]
  have hm : 0 < m := by dsimp [m]; have := qp.pos; positivity
  have cop (i : Fin 4) (hi : i<3) : (p i).Coprime r :=
    (Nat.coprime_primes (hp i) (hp 3)).mpr (ord hi).ne
  have cm : m.Coprime r := by
    dsimp only [m]
    have r3 : (3:ℕ).Coprime r := a ▸ cop 0 (by decide)
    have r5 : (5:ℕ).Coprime r := b ▸ cop 1 (by decide)
    exact Nat.coprime_mul_iff_left.mpr ⟨Nat.coprime_mul_iff_left.mpr
      ⟨r3.pow_left _,r5.pow_left _⟩,(cop 2 (by decide)).pow_left _⟩
  have h0 := low 0
  have h1 := low 1
  have h2 := low 2
  have mb : m≤195^threshold := cofactor_size _ _ _ _ _ h0.le h1.le h2.le q13
  have divbound := OMA.OddCofactor245212.last_le hm (hp 3) cm (positive 3) (fact ▸ eq)
  exact divbound.trans (bounded threshold m mb)

end OMA.OddFaces245212

end

section

/- Odd solutions with at most four distinct prime factors form a finite set,
with no prescribed set of primes or exponents. -/
namespace OMA.OddFaces245212
open Finset OMA.Smooth245212 OMA.FixedPrimes245212
open scoped ArithmeticFunction.sigma

private theorem tiny {k : ℕ} (p u : Fin k → ℕ) (hu : ∀ i,1<u i) (pu : ∀ i,u i≤p i)
    (cap : 2≤∏ i,limitX (p i)) (small : (∏ i,limitX (u i))<2) : False := by
  have b := prod_le_prod (f:=fun i => limitX (p i)) (g:=fun i => limitX (u i))
    (s:=univ) (fun i _ => x_nonneg ((hu i).trans_le (pu i)) none)
    (fun i _ => cap_anti (hu i) (pu i))
  exact (cap.trans b).not_gt small

private theorem support_bound {k : ℕ} (hk : k≤4) (p e : Fin k → ℕ)
    (hp : ∀ i,Nat.Prime (p i)) (ord : StrictMono p) (odd : ∀ i,3≤p i)
    (positive : ∀ i,0<e i) (eq : OeisA245212.a (total p e)=(σ 1 (total p e):ℤ))
    (i : Fin k) : p i≤primeBound := by
  have norm := normalized_of_eq p hp ord.injective _ eq
  have cap := cap_needed p e (fun j => (hp j).one_lt) i (positive i) norm
  interval_cases k
  · exact Fin.elim0 i
  · exfalso
    exact tiny p ![3] (by decide) (by intro j; fin_cases j; exact odd 0) cap (by decide +kernel)
  · have last : p 1≤threshold := by
      by_contra! h
      have lastBig : 257≤p 1 := by unfold threshold at h; omega
      exact tiny p ![3,257] (by decide) (by intro j; fin_cases j; exact odd 0; exact lastBig)
        cap (by decide +kernel)
    exact (ord.monotone (Fin.le_last i)).trans (last.trans primeBound_ge)
  · have next : 5≤p 1 := by
      have a := odd 0
      have b := ord (by decide : (0:Fin 3)<1)
      have c : p 1≠4 := by intro e; have := hp 1; rw [e] at this; norm_num at this
      omega
    have last : p 2≤threshold := by
      by_contra! h
      have lastBig : 257≤p 2 := by unfold threshold at h; omega
      exact tiny p ![3,5,257] (by decide) (by intro j; fin_cases j; exact odd 0; exact next; exact lastBig)
        cap (by decide +kernel)
    exact (ord.monotone (Fin.le_last i)).trans (last.trans primeBound_ge)
  · exact (ord.monotone (Fin.le_last i)).trans (last_prime_le hp ord (odd 0) positive eq)

theorem odd_support {n : ℕ} (odd : Odd n) (few : n.primeFactors.card≤4)
    (eq : OeisA245212.a n=(σ 1 n:ℤ)) : ∀ p∈n.primeFactors, p≤primeBound := by
  let S := n.primeFactors
  let p := S.orderEmbOfFin rfl
  let e (i : Fin S.card) := n.factorization (p i)
  have mem (i) : p i∈n.primeFactors := orderEmbOfFin_mem S rfl i
  have hp (i) := Nat.prime_of_mem_primeFactors (mem i)
  have op (i) : 3≤p i := by
    have h := (hp i).two_le
    have a := Nat.dvd_of_mem_primeFactors (mem i)
    have non : ¬2∣n := fun d => (Nat.not_even_iff_odd.mpr odd) (even_iff_two_dvd.mpr d)
    by_contra! lt
    have same : p i=2 := by omega
    exact non (same ▸ a)
  have ep (i) : 0<e i := (hp i).factorization_pos_of_dvd odd.pos.ne' (Nat.dvd_of_mem_primeFactors (mem i))
  have repr : total p e=n := by
    unfold total e
    exact (Fintype.prod_equiv (S.orderIsoOfFin rfl).toEquiv _
      (fun j : S => j.val^(n.factorization j.val)) (fun _ => rfl)).trans
      (Nat.prod_primeFactors_coe_pow_factorization odd.pos.ne').symm
  intro q hq
  have image : q∈Set.range p := by rw [show Set.range p=(S:Set ℕ) from range_orderEmbOfFin S rfl]; exact hq
  obtain ⟨i,rfl⟩ := image
  exact support_bound few p e hp p.strictMono op ep (by rw [repr]; exact eq) i

private theorem finite_by_bound (B : ℕ)
    (bound : ∀ n : ℕ, Odd n → n.primeFactors.card≤4 → OeisA245212.a n=(σ 1 n:ℤ) →
      ∀ p∈n.primeFactors,p≤B) : {n : ℕ | Odd n ∧ n.primeFactors.card≤4 ∧
    OeisA245212.a n=(σ 1 n:ℤ)}.Finite := by
  apply (Set.finite_singleton 1 |>.union (OMA.FixedPrimes245212.finite (range (B+1)))).subset
  intro n hn
  obtain ⟨ho,hf,he⟩ := hn
  by_cases one : n=1
  · exact Or.inl one
  · refine Or.inr ⟨ho.pos,fun p hp => mem_range.mpr (Nat.lt_succ_of_le (bound n ho hf he p hp)),he,?_⟩
    rintro ⟨i,rfl⟩
    cases i with
    | zero => simp at one
    | succ j => exact (Nat.not_even_iff_odd.mpr ho) (by simp [pow_succ])

theorem odd_finite : {n : ℕ | Odd n ∧ n.primeFactors.card≤4 ∧
    OeisA245212.a n=(σ 1 n:ℤ)}.Finite :=
  finite_by_bound primeBound (fun _ => odd_support)

end OMA.OddFaces245212

end

section

/- A bounded-box certificate engine for the four-prime divisor balance.
The five coordinates are the four exponents followed by the last prime. -/
namespace OMA.Box245212
open Finset OMA.Smooth245212 OMA.Moving245212
open scoped ArithmeticFunction.sigma

structure Range where
  lo : ℕ
  hi : ℕ
  deriving DecidableEq
def Range.has (a : Range) (n : ℕ) := a.lo ≤ n ∧ n ≤ a.hi
def Range.band (a : Range) : Band := ⟨a.lo,some a.hi⟩
theorem Range.band_has {a : Range} {n : ℕ} (h : a.has n) : a.band.Contains n :=
  ⟨h.1,by intro j hj; cases Option.some.inj hj; exact h.2⟩

abbrev Box := Fin 5 → Range
abbrev Values := Fin 5 → ℕ
def Fits (b : Box) (v : Values) := ∀ i,(b i).has (v i)
def bases (p q : ℕ) (v : Values) : Fin 4 → ℕ := ![3,p,q,v 4]
def exponents (v : Values) (i : Fin 4) := v i.castSucc
def baseBox (p q : ℕ) (b : Box) : Fin 4 → Range :=
  ![⟨3,3⟩,⟨p,p⟩,⟨q,q⟩,b 4]

structure Candidate (p q : ℕ) (v : Values) : Prop where
  prime : ∀ i,(bases p q v i).Prime
  ordered : StrictMono (bases p q v)
  pos : ∀ i,0 < exponents v i
  first : 2 ≤ v 0
  eqn : let n := total (bases p q v) (exponents v)
        OeisA245212.a n=(σ 1 n:ℤ)

theorem Candidate.score {p q : ℕ} {v : Values} (h : Candidate p q v) :
    normalized (bases p q v) (exponents v)=2 :=
  normalized_of_eq _ h.prime h.ordered.injective _ h.eqn

def Deny (p q : ℕ) (b : Box) := ∀ v,Fits b v → ¬ Candidate p q v
def clip (b : Box) (i : Fin 5) (c : Range) : Box := Function.update b i c
theorem clip_fits {b : Box} {v : Values} (h : Fits b v) {i : Fin 5} {c : Range}
    (hc : c.has (v i)) : Fits (clip b i c) v := by
  intro j
  by_cases e : j=i
  · subst j; simpa [clip] using hc
  · simpa [clip,e] using h j

theorem split (p q : ℕ) (b : Box) (i : Fin 5) (m : ℕ)
    (lower : Deny p q (clip b i ⟨(b i).lo,m⟩))
    (upper : Deny p q (clip b i ⟨m+1,(b i).hi⟩)) : Deny p q b := by
  intro v inside
  by_cases small : v i ≤ m
  · exact lower v (clip_fits inside ⟨(inside i).1,small⟩)
  · exact upper v (clip_fits inside ⟨show m+1≤v i by omega,(inside i).2⟩)

def factor (f : Band → Band → ℚ) (p q : ℕ) (b : Box) (i : Fin 4) :=
  f (baseBox p q b i).band (b i.castSucc).band

theorem inside_primes {p q : ℕ} {b : Box} {v : Values} (inside : Fits b v) (i : Fin 4) :
    (baseBox p q b i).has (bases p q v i) := by
  fin_cases i <;> simp [baseBox,bases,Range.has]
  exact inside 4

theorem moments {p q : ℕ} {b : Box} {v : Values} (inside : Fits b v)
    (start : ∀ i,1<(baseBox p q b i).lo) (i : Fin 4) :
    let P := bases p q v i; let E := some (exponents v i)
    0≤factor xl p q b i ∧ factor xl p q b i≤X P E ∧ X P E≤factor xu p q b i ∧
    0≤factor yl p q b i ∧ factor yl p q b i≤Y P E ∧ Y P E≤factor yu p q b i :=
  factor_bounds (start i) (Range.band_has (inside_primes inside i)) (Range.band_has (inside i.castSucc))

def prod4 (f : Fin 4 → ℚ) := ∏ i,f i
def interval (p q : ℕ) (b : Box) : Bool :=
  decide ((∀ i,1<(baseBox p q b i).lo) ∧
    (2 < prod4 (factor xl p q b)+prod4 (factor yl p q b) ∨
      prod4 (factor xu p q b)+prod4 (factor yu p q b)<2))

theorem interval_sound {p q : ℕ} {b : Box} (check : interval p q b=true) : Deny p q b := by
  obtain ⟨start,why⟩ := of_decide_eq_true check
  intro v inside candidate
  have m := moments inside start
  have s := candidate.score
  unfold normalized at s
  have lowerX := prod_le_prod (s:=univ) (fun i _ => (m i).1) (fun i _ => (m i).2.1)
  have lowerY := prod_le_prod (s:=univ) (fun i _ => (m i).2.2.2.1) (fun i _ => (m i).2.2.2.2.1)
  have upperX := prod_le_prod (s:=univ) (fun i _ => (m i).1.trans (m i).2.1) (fun i _ => (m i).2.2.1)
  have upperY := prod_le_prod (s:=univ) (fun i _ => (m i).2.2.2.1.trans (m i).2.2.2.2.1)
    (fun i _ => (m i).2.2.2.2.2)
  rcases why with h|h <;> unfold prod4 at h <;> linarith

end OMA.Box245212

end

section

/- Integer fixed-point bounds for prime-power moments. All evaluated box
operations below are on Nat, with normalization reserved for the proof. -/
namespace OMA.FastFactor245212
open OMA.Box245212 OMA.Smooth245212 OMA.Moving245212 Finset

def scale : ℕ := 2^256
def smallQuot (p e : ℕ) :=
  let h := p^min (e+1) 32
  (scale*p*(h-1))/((p-1)*(e+1)*h)
def lowY (pb eb : Range) := smallQuot pb.hi eb.hi
def highY (pb eb : Range) :=
  let p := pb.lo
  let e := eb.lo
  min scale ((if e<32 then smallQuot p e else scale*p/((p-1)*(e+1)))+1)
def lowX (pb eb : Range) := scale+(scale-highY pb eb)/(pb.hi-1)
def highX (pb eb : Range) := scale+(scale-lowY pb eb)/(pb.lo-1)+1

theorem scale_pos : 0<scale := pow_pos (by decide) _
private theorem frac_lo (n d : ℕ) (pos : 0<d) : ((n/d:ℕ):ℚ)≤(n:ℚ)/d := by
  apply (le_div_iff₀ (by exact_mod_cast pos)).mpr
  exact_mod_cast Nat.div_mul_le_self n d
private theorem frac_hi (n d : ℕ) (pos : 0<d) : (n:ℚ)/d≤((n/d+1:ℕ):ℚ) := by
  apply (div_le_iff₀ (by exact_mod_cast pos)).mpr
  exact_mod_cast (Nat.lt_mul_div_succ n pos).le.trans_eq (Nat.mul_comm _ _)

private theorem true_form {p : ℕ} (hp : 1<p) (e : ℕ) :
    Y p (some e)=(p:ℚ)/(((p:ℚ)-1)*(e+1))*(1-(p:ℚ)⁻¹^(e+1)) := by
  have pp : (1:ℚ)<p := by exact_mod_cast hp
  simp only [Y]
  rw [show (p:ℚ)⁻¹-1=(1-p)/p by field_simp]
  generalize (p:ℚ)⁻¹^(e+1) = z
  field_simp [show 1-(p:ℚ)≠0 by linarith, show (p:ℚ)-1≠0 by linarith]; ring

private theorem raw_form {p : ℕ} (hp : 1<p) (e : ℕ) :
    let h := p^min (e+1) 32
    ((scale*p*(h-1):ℕ):ℚ)/((p-1)*(e+1)*h:ℕ) =
       (scale:ℚ)*approx false (some p) (some e) := by
  dsimp only
  have pp : (1:ℚ)<p := by exact_mod_cast hp
  have h1 : 1≤p^min (e+1) 32 := Nat.one_le_pow _ _ hp.le
  push_cast [Nat.cast_sub hp.le,Nat.cast_sub h1]
  unfold approx
  by_cases small : e<32
  · simp only [small,if_true, min_eq_left (show e+1≤32 by omega),true_form hp,inv_pow]
    field_simp
  · simp only [small,if_false, min_eq_right (show 32≤e+1 by omega),Bool.false_eq_true,inv_pow]
    field_simp

private theorem local_bounds {p : ℕ} (hp : 1<p) (e : ℕ) :
    (smallQuot p e:ℚ) ≤ scale*approx false (some p) (some e) ∧
    scale*approx true (some p) (some e)≤
      ((if e<32 then smallQuot p e else scale*p/((p-1)*(e+1)))+1:ℕ) := by
  let h := p^min (e+1) 32
  have p0 : 0<p-1 := by omega
  have dp : 0<(p-1)*(e+1)*h := Nat.mul_pos (Nat.mul_pos p0 (by omega)) (pow_pos hp.le _)
  have raw := raw_form hp e
  refine ⟨(frac_lo _ _ dp).trans_eq raw,?_⟩
  by_cases small : e<32
  · have same : approx true (some p) (some e)=approx false (some p) (some e) := by
      simp [approx,small]
    rw [same,←raw,if_pos small]
    exact frac_hi _ _ dp
  · simp only [approx,small,↓reduceIte]
    have t := frac_hi (scale*p) ((p-1)*(e+1)) (Nat.mul_pos p0 (by omega))
    push_cast [Nat.cast_sub hp.le] at t ⊢
    simpa only [mul_div_assoc'] using t

theorem bounds {pb eb : Range} {p e : ℕ} (valid : 1<pb.lo) (pi : pb.has p) (ei : eb.has e) :
    (lowX pb eb:ℚ) ≤ scale*X p (some e) ∧ scale*X p (some e)≤highX pb eb ∧
    (lowY pb eb:ℚ) ≤ scale*Y p (some e) ∧ scale*Y p (some e)≤highY pb eb := by
  have hP := valid.trans_le pi.1
  have hQ := hP.trans_le pi.2
  have S : (0:ℚ)<scale := by exact_mod_cast scale_pos
  have m := factor_bounds valid (Range.band_has pi) (Range.band_has ei)
  have l : approx false (some pb.hi) (some eb.hi)≤Y p (some e) :=
    (le_max_right _ _).trans m.2.2.2.2.1
  have u : Y p (some e)≤approx true (some pb.lo) (some eb.lo) := m.2.2.2.2.2
  have lo : (lowY pb eb:ℚ) ≤ scale*Y p (some e) :=
    (local_bounds hQ eb.hi).1.trans (mul_le_mul_of_nonneg_left l S.le)
  have hi : (scale:ℚ)*Y p (some e)≤highY pb eb := by
    unfold highY
    rw [Nat.cast_min]
    exact le_min (mul_le_of_le_one_right S.le (y_one hP _))
      ((mul_le_mul_of_nonneg_left u S.le).trans (local_bounds valid eb.lo).2)
  have yu : highY pb eb ≤ scale := min_le_left _ _
  have yl : lowY pb eb ≤ scale := by
    exact_mod_cast lo.trans (mul_le_of_le_one_right S.le (y_one hP _))
  have P1 : (1:ℚ)<p := by exact_mod_cast hP
  have L1 : (1:ℚ)<pb.lo := by exact_mod_cast valid
  have LL : (pb.lo:ℚ)≤p := by exact_mod_cast pi.1
  have HH : (p:ℚ)≤pb.hi := by exact_mod_cast pi.2
  have id : (scale:ℚ)*X p (some e)=scale+(scale-scale*Y p (some e))/((p:ℚ)-1) := by
    unfold X; ring
  rw [id]
  refine ⟨?_,?_,lo,hi⟩
  · have f := frac_lo (scale-highY pb eb) (pb.hi-1) (by omega)
    unfold lowX
    push_cast [Nat.cast_sub yu,Nat.cast_sub hQ.le] at f ⊢
    apply add_le_add_right
    exact f.trans (div_le_div₀ (sub_nonneg.mpr (mul_le_of_le_one_right S.le (y_one hP _)))
      (by linarith only [hi]) (by linarith) (by linarith))
  · have f := frac_hi (scale-lowY pb eb) (pb.lo-1) (by omega)
    unfold highX
    push_cast [Nat.cast_sub yl,Nat.cast_sub valid.le] at f ⊢
    have D := div_le_div₀ (show 0≤(scale:ℚ)-lowY pb eb by exact sub_nonneg.mpr (by exact_mod_cast yl))
      (show (scale:ℚ)-scale*Y p (some e) ≤ scale-lowY pb eb by linarith only [lo])
      (show 0<(pb.lo:ℚ)-1 by linarith) (show (pb.lo:ℚ)-1≤(p:ℚ)-1 by linarith)
    linarith only [D.trans f]

end OMA.FastFactor245212

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

end

section

/- Closed prime-power moments and the integer test at exact prefix leaves. -/
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

theorem force {A S T d p : ℕ} (hs : 0<S) (hp : 1<p) (hD : 0<denom A S T d)
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

/- Score and modular exclusions for the three possible odd three-prime supports. -/
namespace OMA.TriSupport245212
open Finset Nat ArithmeticFunction OMA.Smooth245212 OMA.FastFactor245212
open scoped ArithmeticFunction.sigma
open OMA.Large245212 (moments)

abbrev I3 := Fin 3
abbrev R := OMA.Box245212.Range
abbrev Box := I3 → R
abbrev P := OMA.OddFaces245212.bases
def Fits (b : Box) (e : I3 → ℕ) := ∀ i, (b i).has (e i)
def Deny (q : ℕ) (b : Box) :=
  ∀ e : I3 → ℕ, Fits b e →
    OeisA245212.a (total (P q) e) ≠ (σ 1 (total (P q) e) : ℤ)
def initial : Box := fun _ => ⟨1,10000000000⟩
def supported (q : ℕ) := q=7 ∨ q=11 ∨ q=13

theorem primes {q : ℕ} (ok : supported q) :
    (∀ i, (P q i).Prime) ∧ Function.Injective (P q) := by
  rcases ok with rfl|rfl|rfl <;> decide +kernel

theorem initial_fits {q : ℕ} (ok : supported q) (e : I3 → ℕ) (pos : ∀ i, 0<e i)
    (eq : OeisA245212.a (total (P q) e) = (σ 1 (total (P q) e) : ℤ)) : Fits initial e := by
  let v : Fin 4 → ℕ := Fin.snoc e 1
  have vpos (i : Fin 4) : 0 < v i := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · dsimp only [v]
      rw [Fin.snoc_last]; decide
    · simpa [v] using pos j
  have hp := primes ok
  have norm := normalized_of_eq (P q) hp.1 hp.2 e eq
  let r := OMA.OddFaces245212.threshold+1
  have rx : X r (some 0)=1 := by norm_num [X,Y,r,OMA.OddFaces245212.threshold]
  have ry : Y r (some 0)=1 := by norm_num [Y,r,OMA.OddFaces245212.threshold]
  have ps : OMA.OddFaces245212.preScore q r 0 v=2 := by
    simpa only [OMA.OddFaces245212.preScore,rx,ry,mul_one,v,Fin.snoc_castSucc,normalized]
      using norm
  intro i
  refine ⟨pos i,?_⟩
  change e i ≤ 10000000000
  by_contra! fail
  have qq : q.Prime ∧ 3≤q := by rcases ok with rfl|rfl|rfl <;> decide
  have hlarge : OMA.OddFaces245212.threshold ≤ v i.castSucc := by
    simpa only [v,Fin.snoc_castSucc,OMA.OddFaces245212.threshold] using fail.le
  exact OMA.OddFaces245212.near_face qq.1 qq.2 (by dsimp only [r];omega) v 0 i hlarge ps
    (OMA.OddFaces245212.separation ok i v vpos)

def scaledProd (f : R → R → ℕ) (q : ℕ) (b : Box) :=
  ∏ i, f ⟨P q i,P q i⟩ (b i)
def scoreTest (q : ℕ) (b : Box) : Bool :=
  decide (2*scale^3 < scaledProd lowX q b+scaledProd lowY q b ∨
    scaledProd highX q b+scaledProd highY q b < 2*scale^3)

theorem score_sound {q : ℕ} (ok : supported q) {b : Box} (test : scoreTest q b=true) : Deny q b := by
  intro e fit eq
  obtain ⟨prime,inj⟩ := primes ok
  have norm := normalized_of_eq (P q) prime inj e eq
  have h (i : I3) := OMA.FastFactor245212.bounds (pb:=⟨P q i,P q i⟩)
    (eb:=b i) (p:=P q i) (e:=e i) (prime i).one_lt ⟨le_rfl,le_rfl⟩ (fit i)
  have enclose (f F : R → R → ℕ) (u : I3 → ℚ) (hu : ∀ i, 0≤u i)
      (v : ∀ i, (f ⟨P q i,P q i⟩ (b i) : ℚ)≤ scale*u i ∧
        scale*u i ≤ (F ⟨P q i,P q i⟩ (b i) : ℚ)) :
      (scaledProd f q b:ℚ)≤(scale:ℚ)^3*∏ i,u i ∧
      (scale:ℚ)^3*(∏ i,u i) ≤ scaledProd F q b := by
    have lo := prod_le_prod (s:=(univ:Finset I3)) (fun i _ =>
      show (0:ℚ)≤f ⟨P q i,P q i⟩ (b i) by positivity) (fun i _ => (v i).1)
    have hi := prod_le_prod (s:=(univ:Finset I3)) (fun i _ => mul_nonneg
      (Nat.cast_nonneg scale) (hu i)) (fun i _ => (v i).2)
    have size : (univ : Finset I3).card=3 := by decide
    simpa only [scaledProd,Nat.cast_prod,prod_mul_distrib,prod_const,size] using And.intro lo hi
  have x := enclose lowX highX _ (fun i => x_nonneg (prime i).one_lt (some (e i)))
    (fun i => ⟨(h i).1,(h i).2.1⟩)
  have y := enclose lowY highY _ (fun i => y_nonneg (prime i).one_lt (some (e i)))
    (fun i => (h i).2.2)
  rw [scoreTest,decide_eq_true_eq] at test
  unfold normalized at norm
  have sn := congrArg (fun z : ℚ => (scale:ℚ)^3*z) norm
  rw [mul_add] at sn
  rcases test with t|t
  · have bad : 2*(scale:ℚ)^3 < (scaledProd lowX q b:ℚ)+scaledProd lowY q b := by exact_mod_cast t
    linarith only [bad,sn,x.1,y.1]
  · have bad : (scaledProd highX q b:ℚ)+scaledProd highY q b < 2*(scale:ℚ)^3 := by exact_mod_cast t
    linarith only [bad,sn,x.2,y.2]

end OMA.TriSupport245212

end

section

/- Reduction of arbitrary odd support of cardinality at most four to
three ternary supports and the classified four-prime branch. -/
namespace OMA.OddSupportClass245212
open Finset Nat ArithmeticFunction OMA.Smooth245212 OMA.OddFaces245212
open scoped ArithmeticFunction.sigma
open OMA.OddFaces245212 (envelope)

private theorem skip {p l u : ℕ} (hp : p.Prime) (low : l≤p)
    (empty : ∀ j∈Ico l u, ¬ Nat.Prime j) : u≤p := by
  by_contra! bad
  exact empty p (mem_Ico.mpr ⟨low,bad⟩) hp

private theorem tiny {k : ℕ} (p z : Fin k → ℕ) (gz : ∀ i,1<z i)
    (lz : ∀ i,z i≤p i) (cap : 2≤∏ i,limitX (p i)) (small : (∏ i,limitX (z i))<2) : False := by
  have le := prod_le_prod (s:=univ) (fun i _ => x_nonneg ((gz i).trans_le (lz i)) none)
    (fun i _ => cap_anti (gz i) (lz i))
  exact (cap.trans le).not_gt small

private theorem first_one (p e : Fin 4 → ℕ) (hp : ∀ i, (p i).Prime)
    (p0 : p 0=3) (e0 : e 0=1) (p1 : 5≤p 1) (p2 : 7≤p 2) (p3 : 11≤p 3)
    (norm : normalized p e=2) : False := by
  let z : Fin 3 → ℕ := ![5,7,11]
  let T := ∏ i : Fin 3, Y (p i.succ) (some (e i.succ))
  let C := ∏ i : Fin 3, limitX (p i.succ)
  let B := ∏ i : Fin 3, X (p i.succ) (some (e i.succ))
  have env : B≤T+(1-T)*C := OMA.OddFaces245212.envelope univ
    (fun i : Fin 3 => p i.succ) (fun i => e i.succ) (fun i => (hp _).one_lt)
  have tz : 0≤T := prod_nonneg (fun i _ => y_nonneg (hp _).one_lt _)
  have tone : T≤1 := prod_le_one (fun i _ => y_nonneg (hp _).one_lt _) (fun i _ => y_one (hp _).one_lt _)
  have lo (i : Fin 3) : z i ≤ p i.succ := by fin_cases i <;> first | exact p1 | exact p2 | exact p3
  have gc : ∀ i, 1<z i := by decide
  have c : C≤(∏ i,limitX (z i)) := prod_le_prod (s:=univ)
    (fun i _ => x_nonneg (hp _).one_lt _) (fun i _ => cap_anti (gc i) (lo i))
  have vc : (∏ i,limitX (z i))=77/48 := by decide +kernel
  rw [vc] at c
  have ca := mul_le_mul_of_nonneg_left c (sub_nonneg.mpr tone)
  unfold normalized at norm
  rw [Fin.prod_univ_succ (fun i => X (p i) (some (e i))),
    Fin.prod_univ_succ (fun i => Y (p i) (some (e i))),p0,e0] at norm
  change X 3 (some 1)*B+Y 3 (some 1)*T=2 at norm
  have x : X 3 (some 1)=7/6 := by decide +kernel
  have y : Y 3 (some 1)=2/3 := by decide +kernel
  rw [x,y] at norm
  linarith only [tz,tone,ca,env,norm]

def ThreeExcluded := ∀ q, OMA.TriSupport245212.supported q → ∀ e : Fin 3 → ℕ,
  (∀ i,0<e i) → OeisA245212.a (total (bases q) e) ≠ (σ 1 (total (bases q) e) : ℤ)
def FourExcluded := ∀ k p q r e f g : ℕ, 2≤k → p.Prime → q.Prime → r.Prime →
  5≤p → p<q → q<r → 0<e → 0<f → 0<g →
  OeisA245212.a (3^k*p^e*q^f*r^g) ≠ (σ 1 (3^k*p^e*q^f*r^g) : ℤ)

private theorem sorted (three : ThreeExcluded) {k : ℕ} (four : k=4 → FourExcluded) (few : k≤4)
    (p e : Fin k → ℕ) (hp : ∀ i, (p i).Prime) (ord : StrictMono p) (odd : ∀ i,3≤p i)
    (pos : ∀ i,0 < e i) (eq : OeisA245212.a (total p e)=(σ 1 (total p e):ℤ)) : total p e=1 := by
  have norm := normalized_of_eq p hp ord.injective e eq
  have cap (i : Fin k) := cap_needed p e (fun j => (hp j).one_lt) i (pos i) norm
  interval_cases k
  · simp [total]
  · exfalso
    exact tiny p ![3] (by decide) (fun j => by fin_cases j; exact odd 0) (cap 0) (by decide +kernel)
  · exfalso
    have h5 : 5≤p 1 := skip (hp 1) (show 4≤p 1 by have := ord (by decide : (0:Fin 2)<1); have := odd 0; omega) (by decide)
    exact tiny p ![3,5] (by decide) (fun j => by fin_cases j; exact odd 0; exact h5) (cap 0) (by decide +kernel)
  · exfalso
    have a := ord (by decide : (0:Fin 3)<1)
    have b := ord (by decide : (1:Fin 3)<2)
    have p0 := odd 0
    have p5 : 5≤p 1 := skip (hp 1) (show 4≤p 1 by omega) (by decide)
    have p7 : 7≤p 2 := skip (hp 2) (show 6≤p 2 by omega) (by decide)
    have first : p 0=3 := by
      by_contra! bad
      have a5 : 5≤p 0 := skip (hp 0) (show 4≤p 0 by omega) (by decide)
      have a7 : 7≤p 1 := skip (hp 1) (show 6≤p 1 by omega) (by decide)
      have a11 : 11≤p 2 := skip (hp 2) (show 8≤p 2 by omega) (by decide)
      exact tiny p ![5,7,11] (by decide) (fun i => by fin_cases i <;> first | exact a5 | exact a7 | exact a11) (cap 0) (by decide +kernel)
    have second : p 1=5 := by
      by_contra! bad
      have a7 : 7≤p 1 := skip (hp 1) (show 6≤p 1 by omega) (by decide)
      have a11 : 11≤p 2 := skip (hp 2) (show 8≤p 2 by omega) (by decide)
      exact tiny p ![3,7,11] (by decide) (fun i => by fin_cases i <;> first | exact p0 | exact a7 | exact a11) (cap 0) (by decide +kernel)
    have mx : p 2<17 := by
      by_contra! bad
      exact tiny p ![3,5,17] (by decide) (fun i => by fin_cases i <;> first | exact p0 | exact p5 | exact bad) (cap 0) (by decide +kernel)
    have last : OMA.TriSupport245212.supported (p 2) := by
      have pr := hp 2
      generalize p 2=z at p7 mx pr ⊢
      interval_cases z <;> norm_num [OMA.TriSupport245212.supported] at *
    have same : bases (p 2)=p := by
      funext i
      fin_cases i <;> simp [bases,first,second]
    exact three (p 2) last e pos (same ▸ eq)
  · exfalso
    have a := ord (by decide : (0:Fin 4)<1)
    have b := ord (by decide : (1:Fin 4)<2)
    have c := ord (by decide : (2:Fin 4)<3)
    have p0 := odd 0
    have p5 : 5≤p 1 := skip (hp 1) (show 4≤p 1 by omega) (by decide)
    have p7 : 7≤p 2 := skip (hp 2) (show 6≤p 2 by omega) (by decide)
    have p11 : 11≤p 3 := skip (hp 3) (show 8≤p 3 by omega) (by decide)
    have first : p 0=3 := by
      by_contra! bad
      have a5 : 5≤p 0 := skip (hp 0) (show 4≤p 0 by omega) (by decide)
      have a7 : 7≤p 1 := skip (hp 1) (show 6≤p 1 by omega) (by decide)
      have a11 : 11≤p 2 := skip (hp 2) (show 8≤p 2 by omega) (by decide)
      have a13 : 13≤p 3 := skip (hp 3) (show 12≤p 3 by omega) (by decide)
      exact tiny p ![5,7,11,13] (by decide)
        (fun i => by fin_cases i <;> first | exact a5 | exact a7 | exact a11 | exact a13) (cap 0) (by decide +kernel)
    by_cases one : e 0=1
    · exact first_one p e hp first one p5 p7 p11 norm
    · have ge : 2≤e 0 := by have := pos 0; omega
      apply four rfl (e 0) (p 1) (p 2) (p 3) (e 1) (e 2) (e 3) ge (hp 1) (hp 2) (hp 3)
        p5 b c (pos 1) (pos 2) (pos 3)
      simpa only [total,Fin.prod_univ_four,first,mul_assoc] using eq

theorem classify (three : ThreeExcluded) (n : ℕ) (odd : Odd n) (few : n.primeFactors.card≤4)
    (four : n.primeFactors.card=4 → FourExcluded) (eq : OeisA245212.a n=(σ 1 n:ℤ)) : n=1 := by
  let S := n.primeFactors
  let p := S.orderEmbOfFin rfl
  let e (i : Fin S.card) := n.factorization (p i)
  have mem (i) : p i∈n.primeFactors := orderEmbOfFin_mem S rfl i
  have hp (i) := Nat.prime_of_mem_primeFactors (mem i)
  have op (i) : 3≤p i := by
    have h := (hp i).two_le
    have a := Nat.dvd_of_mem_primeFactors (mem i)
    have non : ¬2∣n := fun d => (Nat.not_even_iff_odd.mpr odd) (even_iff_two_dvd.mpr d)
    by_contra! lt
    have same : p i=2 := by omega
    exact non (same ▸ a)
  have ep (i) : 0<e i := (hp i).factorization_pos_of_dvd odd.pos.ne' (Nat.dvd_of_mem_primeFactors (mem i))
  have repr : total p e=n := by
    unfold total e
    exact (Fintype.prod_equiv (S.orderIsoOfFin rfl).toEquiv _
      (fun j : S => j.val^(n.factorization j.val)) (fun _ => rfl)).trans
      (Nat.prod_primeFactors_coe_pow_factorization odd.pos.ne').symm
  simpa only [repr] using sorted three four few p e hp p.strictMono op ep (by rw [repr]; exact eq)

end OMA.OddSupportClass245212

end

section

/- Exact-prefix leaves for the final prime and exponent. The two top
digit inequalities first cut the exponent interval by signed linear
inequalities. Power divisibility supplies an independent finite cap. -/

namespace OMA.PrefixLeaf245212
open OMA.LastDigit245212 OMA.Large245212 OMA.Smooth245212 ArithmeticFunction
open scoped ArithmeticFunction.sigma
open OMA.Large245212 (force)
open OMA.Large245212 (moments)

/-- Intersect the natural interval with the single half-space v*d ≤ w. -/
def trim (B : ℕ×ℕ) (v w : ℤ) : ℕ×ℕ :=
  if 0<v then
    if w<0 then (1,0) else (B.1,min B.2 (w/v).toNat)
  else if v<0 then (max B.1 (-(w/(-v))).toNat,B.2)
  else if w<0 then (1,0) else B

private theorem trim_sound {B : ℕ×ℕ} {v w : ℤ} {d : ℕ} (blo : B.1≤d) (bhi : d≤B.2)
    (eq : v*(d:ℤ)≤w) : (trim B v w).1≤d ∧ d≤(trim B v w).2 := by
  unfold trim
  split_ifs with pos neg vn wn
  · have := mul_nonneg pos.le (Int.natCast_nonneg d); omega
  · have v1 : (d:ℤ)≤w/v := (Int.le_ediv_iff_mul_le pos).2 (by simpa [mul_comm] using eq)
    exact ⟨blo,le_min bhi (by omega)⟩
  · have v1 : -(d:ℤ)≤w/(-v) := (Int.le_ediv_iff_mul_le (by omega)).2 (by nlinarith only [eq])
    exact ⟨max_le blo (by omega),bhi⟩
  · have : v=0 := by omega
    simp [this] at eq
    omega
  · exact ⟨blo,bhi⟩

private def slope (A T u : ℕ) : ℤ := ((u:ℤ)+1)*A-2*u*T
private def offset (A S u : ℕ) : ℤ := (A:ℤ)-((u:ℤ)+1)*S

def bounds (A S T rl rh gl gh : ℕ) : ℕ×ℕ :=
  let cap := Nat.log rl (A+rh*S)
  let v := slope A T rh
  let w := offset A S rh
  let B := trim (gl,min gh cap) v (w-v)
  let u := rl-1
  let v' := slope A T u
  let w' := offset A S u
  trim B (-v') (v'-w'-1)

private theorem bounds_sound {A S T rl rh gl gh r d : ℕ} (base : 1<rl)
    (lo : rl≤r) (hi : r≤rh) (dlo : gl≤d) (dhi : d≤gh)
    (positive : 0<denom A S T d)
    (lower : denom A S T d*(r-1)<A*d+S) (upper : A*d+S≤denom A S T d*r)
    (power : r^d≤A+rh*S) :
    (bounds A S T rl rh gl gh).1≤d ∧ d≤(bounds A S T rl rh gl gh).2 := by
  have cap : d≤Nat.log rl (A+rh*S) :=
    Nat.le_log_of_pow_le base ((Nat.pow_le_pow_left lo d).trans power)
  have eq : denom A S T d+(A*(d+1)+S)=2*T*(d+1) := by
    apply Nat.sub_add_cancel
    exact (Nat.sub_pos_iff_lt.mp positive).le
  have lm : denom A S T d*(rl-1)<A*d+S :=
    lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right lo 1)) lower
  have um : A*d+S≤denom A S T d*rh := upper.trans (Nat.mul_le_mul_left _ hi)
  have eq' : (denom A S T d:ℤ)+(A*(d+1)+S)=2*T*(d+1) := by exact_mod_cast eq
  have um' : (A:ℤ)*d+S≤denom A S T d*rh := by exact_mod_cast um
  have lm' : (denom A S T d:ℤ)*((rl-1:ℕ):ℤ)<(A:ℤ)*d+S := by exact_mod_cast lm
  have cm := congrArg (fun z:ℤ=>z*(rh:ℤ)) eq'
  have f := trim_sound (B:=(gl,min gh (Nat.log rl (A+rh*S)))) dlo (le_min dhi cap)
    (v:=slope A T rh) (w:=offset A S rh-slope A T rh) (by
      unfold slope offset; nlinarith only [um',cm])
  apply trim_sound f.1 f.2
  unfold slope offset
  have c := congrArg (fun z:ℤ=>z*((rl-1:ℕ):ℤ)) eq'
  have lm'' : (denom A S T d:ℤ)*((rl-1:ℕ):ℤ)+1≤(A:ℤ)*d+S := by omega
  nlinarith only [lm'',c]

/-- Exclude one exponent using the only possible last prime. Full
    divisor moments are needed only after the inexpensive tests pass. -/
def rejects (A S T rl rh d : ℕ) : Bool :=
  let D := denom A S T d
  let r := candidate A S T d
  D==0 || r<rl || rh<r || (A+S)%r != 0 ||
    (1<d && A*d+S==D*r) ||
    A*wt r d+S*sig r d != 2*T*OMA.Large245212.tax r d

/-- True certifies that the given prime and exponent window contains no
    solution with the specified cofactor moments. -/
def exact (A S T rl rh gl gh : ℕ) : Bool :=
  let B := bounds A S T rl rh gl gh
  (List.range' B.1 (B.2+1-B.1)).all (rejects A S T rl rh)

theorem sound {A S T rl rh gl gh r d : ℕ} (base : 1<rl)
    (lo : rl≤r) (hi : r≤rh) (dlo : gl≤d) (dhi : d≤gh) (hs : 0<S)
    (positive : 0<denom A S T d)
    (lower : denom A S T d*(r-1)<A*d+S) (upper : A*d+S≤denom A S T d*r)
    (strict : 1<d → A*d+S<denom A S T d*r)
    (powBound : r^d≤A+rh*S) (dvd : r∣A+S)
    (eq : A*wt r d+S*sig r d=2*T*OMA.Large245212.tax r d) : exact A S T rl rh gl gh=false := by
  have fit := bounds_sound base lo hi dlo dhi positive lower upper powBound
  have cand := OMA.Large245212.force hs (lt_of_lt_of_le base lo) positive lower upper
  have no : rejects A S T rl rh d=false := by
    simp [rejects,cand,Nat.mod_eq_zero_of_dvd dvd,eq,positive.ne',not_lt.mpr lo,not_lt.mpr hi]
    exact fun gt=>(strict gt).ne
  cases h : exact A S T rl rh gl gh with
  | false => rfl
  | true =>
    have hit : d∈List.range' (bounds A S T rl rh gl gh).1
          ((bounds A S T rl rh gl gh).2+1-(bounds A S T rl rh gl gh).1) := by
      exact List.mem_range'.mpr ⟨d-(bounds A S T rl rh gl gh).1,by omega,by simp; omega⟩
    have bad := List.all_eq_true.mp h d hit
    simp [no] at bad

/-- A genuine odd prime-power extension satisfying the divisor equality
    must survive the exact-prefix test. No primality of the other factors
    of the cofactor is needed. -/
theorem extension {m rl rh gl gh r d : ℕ} (hm : 0 < m) (hp : r.Prime) (hp2 : r ≠ 2)
    (cop : m.Coprime r) (base : 1<rl) (lo : rl≤r) (hi : r≤rh)
    (dlo : gl≤d) (dhi : d≤gh) (dp : 0<d)
    (eq : OeisA245212.a (m*r^d)=(σ 1 (m*r^d):ℤ)) :
    exact (W m) (σ 1 m) (m*(σ 0 m)) rl rh gl gh=false := by
  obtain ⟨pos,lower,upper,strict⟩ := balance_digits hm hp cop dp eq
  have sp : 0<σ 1 m := by
    rw [sigma_one_apply]
    exact Finset.sum_pos' (fun _ _=>Nat.zero_le _)
      ⟨1,Nat.one_mem_divisors.mpr hm.ne',by decide⟩
  apply sound base lo hi dlo dhi sp pos lower upper strict
  · have h := OMA.PrimePowerDiv245212.cofactor_bound hm hp hp2 cop d eq
    have le := Int.natAbs_sub_le (W m:ℤ) (((r:ℤ)-1)*(σ 1 m:ℤ))
    rw [Int.natAbs_mul] at le
    have sub : (r:ℤ)-1=((r-1:ℕ):ℤ) := by omega
    rw [sub] at le h
    simp only [Int.natAbs_natCast] at le
    exact (h.trans le).trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega : r-1≤rh)) _)
  · exact OMA.OddCofactor245212.last_dvd hm hp cop dp eq
  · have b := OMA.Abundance245212.balance (mul_ne_zero hm.ne' (pow_ne_zero _ hp.ne_zero)) eq
    rw [w_mult.map_mul_of_coprime (cop.pow_right d),
      isMultiplicative_sigma.map_mul_of_coprime (cop.pow_right d),
      isMultiplicative_sigma.map_mul_of_coprime (cop.pow_right d),sigma_zero_apply_prime_pow hp] at b
    obtain ⟨ss,ww⟩ := OMA.Large245212.moments hp d
    rw [ss,ww,OMA.Large245212.tax]
    nlinarith only [b]

/-- Closed products for a cofactor consisting of three distinct prime
    powers; these are the arguments passed to the arithmetic leaf. -/
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

/- Exact-prefix exclusions for rectangular ranges of all three cofactor exponents. -/
namespace OMA.Box245212
open OMA.Smooth245212 Finset OMA.Large245212
open scoped ArithmeticFunction.sigma

def Range.entries (r : Range) := List.range' r.lo (r.hi+1-r.lo)
theorem Range.mem_entries {r : Range} {v : ℕ} (h : r.has v) : v∈r.entries := by
  rcases h with ⟨l,u⟩
  exact List.mem_range'_1.mpr ⟨l,by omega⟩

def exactBlock (p q : ℕ) (b : Box) : Bool :=
  decide (1<(b 4).lo) &&
  (b 0).entries.all (fun k => (b 1).entries.all (fun e => (b 2).entries.all (fun f =>
    PrefixLeaf245212.exact (wt 3 k*wt p e*wt q f) (sig 3 k*sig p e*sig q f)
      (tax 3 k*tax p e*tax q f) (b 4).lo (b 4).hi (b 3).lo (b 3).hi)))

theorem prefix_sound {p q : ℕ} {b : Box} (yes : exactBlock p q b=true) : Deny p q b := by
  intro v inside c
  have h := Bool.and_eq_true_iff.mp yes
  have check0 := List.all_eq_true.mp h.2 (v 0) (Range.mem_entries (inside 0))
  have check1 := List.all_eq_true.mp check0 (v 1) (Range.mem_entries (inside 1))
  have check2 := List.all_eq_true.mp check1 (v 2) (Range.mem_entries (inside 2))
  let m := 3^(v 0)*p^(v 1)*q^(v 2)
  have hp : p.Prime := c.prime 1
  have hq : q.Prime := c.prime 2
  have hr : (v 4).Prime := c.prime 3
  have small : 3<p := c.ordered (show (0:Fin 4)<1 by decide)
  have pq : p<q := c.ordered (show (1:Fin 4)<2 by decide)
  have qr : q<v 4 := c.ordered (show (2:Fin 4)<3 by decide)
  have same : total (bases p q v) (exponents v)=m*(v 4)^(v 3) := by
    simp [total,bases,exponents,m,Fin.prod_univ_four]
  have s := c.eqn; dsimp only at s; rw [same] at s
  have cop : m.Coprime (v 4) :=
    (((Nat.coprime_primes Nat.prime_three hr).mpr (by omega)).pow_left _).mul_left
      (((Nat.coprime_primes hp hr).mpr (by omega)).pow_left _) |>.mul_left
        (((Nat.coprime_primes hq hr).mpr qr.ne).pow_left _)
  have mp : 0 < m := mul_pos (mul_pos (pow_pos (by decide) _) (pow_pos hp.pos _)) (pow_pos hq.pos _)
  have no := PrefixLeaf245212.extension mp
    hr (by omega) cop (of_decide_eq_true h.1) (inside 4).1 (inside 4).2 (inside 3).1 (inside 3).2
    (c.pos 3) s
  have triple := PrefixLeaf245212.triple Nat.prime_three hp hq small.ne (by omega) pq.ne (v 0) (v 1) (v 2)
  dsimp only at triple
  dsimp only [m] at no
  rw [triple.1,triple.2.1,triple.2.2] at no
  exact Bool.noConfusion (check2.symm.trans no)

end OMA.Box245212

end

section

/- At each odd prime, screen the two other exponents by a necessary congruence. -/
namespace OMA.TriSupport245212
open Nat Finset ArithmeticFunction OMA.Smooth245212
open scoped ArithmeticFunction.sigma
open OMA.Large245212 (moments)

def next (i : I3) : I3 := i+1
def last (i : I3) : I3 := i+2
def residue (p u v a b mod : ℕ) : Bool :=
  decide ((OMA.Large245212.wt u a * OMA.Large245212.wt v b) % mod =
    ((p-1)*OMA.Large245212.sig u a*OMA.Large245212.sig v b) % mod)
def modTest (q : ℕ) (box : Box) (i : I3) : Bool :=
  let j := next i
  let k := last i
  let p := P q i
  let mod := p^(min 8 (box i).lo)
  (box j).entries.all fun a => (box k).entries.all fun b => !residue p (P q j) (P q k) a b mod

theorem mod_sound {q : ℕ} (ok : supported q) {box : Box} {i : I3}
    (yes : modTest q box i=true) : Deny q box := by
  intro e fit eq
  let j := next i
  let k := last i
  let p := P q i
  let u := P q j
  let v := P q k
  let m := u^(e j)*v^(e k)
  let h := min 8 (box i).lo
  have hp := primes ok
  have neq : j≠i ∧ k≠i ∧ j≠k := by fin_cases i <;> decide
  have cju : u.Coprime p := (Nat.coprime_primes (hp.1 j) (hp.1 i)).mpr (fun z => neq.1 (hp.2 z))
  have cku : v.Coprime p := (Nat.coprime_primes (hp.1 k) (hp.1 i)).mpr (fun z => neq.2.1 (hp.2 z))
  have cjk : u.Coprime v := (Nat.coprime_primes (hp.1 j) (hp.1 k)).mpr (fun z => neq.2.2 (hp.2 z))
  have cop : m.Coprime p := Nat.coprime_mul_iff_left.mpr ⟨cju.pow_left _,cku.pow_left _⟩
  have cp := (cjk.pow_left (e j)).pow_right (e k)
  have posm : 0 < m := Nat.mul_pos (pow_pos (hp.1 j).pos _) (pow_pos (hp.1 k).pos _)
  have ident : total (P q) e=m*p^(e i) := by
    fin_cases i <;> simp [total,Fin.prod_univ_three,m,p,u,v,j,k,next,last] <;> ring
  rw [ident] at eq
  have div := OMA.PrimePowerDiv245212.power_divides posm (hp.1 i) cop (e i) eq
  have hh : h ≤ e i := (min_le_right _ _).trans (fit i).1
  have full := (pow_dvd_pow (p:ℤ) hh).trans div
  have hu := OMA.Large245212.moments (hp.1 j) (e j)
  have hv := OMA.Large245212.moments (hp.1 k) (e k)
  change _ ∣ (W (u^(e j)*v^(e k)) : ℤ)-((p:ℤ)-1)*(σ 1 (u^(e j)*v^(e k)):ℤ) at full
  rw [w_mult.map_mul_of_coprime cp,isMultiplicative_sigma.map_mul_of_coprime cp,
    ←hu.2,←hv.2,←hu.1,←hv.1] at full
  have cong : (p-1)*OMA.Large245212.sig u (e j)*OMA.Large245212.sig v (e k) ≡
    OMA.Large245212.wt u (e j)*OMA.Large245212.wt v (e k) [MOD p^h] := by
    apply Nat.modEq_iff_dvd.mpr
    have z : ((p-1:ℕ):ℤ)=(p:ℤ)-1 := by rw [Nat.cast_sub (show 1≤p from (hp.1 i).pos),Nat.cast_one]
    simp only [Nat.cast_pow,Nat.cast_mul,z,mul_assoc]
    exact full
  have actual : residue p u v (e j) (e k) (p^h)=true := decide_eq_true cong.symm
  have no := List.all_eq_true.mp (List.all_eq_true.mp yes _ ((box j).mem_entries (fit j)))
    _ ((box k).mem_entries (fit k))
  change (!residue p u v (e j) (e k) (p^h))=true at no
  simp [actual] at no

inductive Trace
  | score
  | sieve (i : I3)
  | branch (i : I3) (cut : ℕ) (left right : Trace)
def leftB (b : Box) (i : I3) (c : ℕ) := Function.update b i ⟨(b i).lo,c⟩
def rightB (b : Box) (i : I3) (c : ℕ) := Function.update b i ⟨c+1,(b i).hi⟩
def Trace.check (q : ℕ) : Trace → Box → Bool
  | .score,b => scoreTest q b
  | .sieve i,b => modTest q b i
  | .branch i c l r,b => l.check q (leftB b i c) && r.check q (rightB b i c)
theorem Trace.sound {q : ℕ} (ok : supported q) (t : Trace) (b : Box)
    (cert : t.check q b=true) : Deny q b := by
  induction t generalizing b with
  | score => exact score_sound ok cert
  | sieve i => exact mod_sound ok cert
  | branch i c l r il ir =>
    obtain ⟨cl,cr⟩ := Bool.and_eq_true_iff.mp cert
    intro e he eq
    by_cases small : e i≤c
    · apply il _ cl e _ eq
      intro j; by_cases ij : j=i
      · subst j; simpa [leftB,OMA.Box245212.Range.has] using And.intro (he i).1 small
      · simpa [leftB,ij] using he j
    · apply ir _ cr e _ eq
      intro j; by_cases ij : j=i
      · subst j; simpa [rightB,OMA.Box245212.Range.has] using And.intro (by omega : c+1≤e i) (he i).2
      · simpa [rightB,ij] using he j

end OMA.TriSupport245212

end

section

/- Fixed three-prime support (3,5,7) with unrestricted positive exponents. -/
namespace OMA.TriSupport245212
open OMA.Smooth245212
open scoped ArithmeticFunction.sigma
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private def witness7 : Trace := (.branch 0 2 (.branch 1 2 .score .score) (.branch 0 6 (.branch 1 2 .score (.branch 2 2 .score (.branch 1 6 .score (.branch 0 4 .score (.branch 2 6 .score (.branch 1 14 (.sieve 2) (.branch 2 14 (.sieve 1) (.branch 1 30 (.sieve 2) (.branch 0 5 (.branch 2 30 .score (.branch 1 62 .score (.branch 2 62 (.sieve 1) (.branch 1 126 (.sieve 2) (.branch 2 126 (.sieve 1) (.branch 1 254 (.branch 2 254 (.branch 1 169 (.sieve 2) (.sieve 2)) .score) .score)))))) (.branch 2 30 (.sieve 1) .score)))))))))) (.branch 1 2 (.branch 2 2 .score (.branch 0 14 .score (.branch 2 6 .score (.branch 1 1 .score (.branch 0 30 .score (.branch 2 14 .score (.branch 0 62 .score (.branch 2 30 .score (.branch 0 126 .score (.branch 2 62 (.sieve 0) (.branch 0 254 (.branch 2 126 (.sieve 0) (.branch 0 169 (.sieve 2) (.sieve 2))) (.branch 2 126 (.sieve 0) .score)))))))))))) (.branch 2 2 (.branch 0 14 (.branch 1 6 .score (.sieve 1)) (.branch 1 6 (.sieve 0) (.branch 0 30 (.sieve 1) (.branch 1 14 (.sieve 0) (.branch 2 1 (.branch 1 30 .score (.branch 0 62 .score (.branch 1 62 (.sieve 0) (.branch 0 126 (.sieve 1) (.branch 1 126 (.sieve 0) (.branch 0 254 (.branch 1 254 (.branch 0 169 (.sieve 1) (.sieve 1)) (.branch 0 169 (.sieve 1) .score)) .score)))))) .score))))) (.branch 0 14 (.branch 1 6 (.sieve 2) (.branch 2 6 (.sieve 1) (.branch 1 14 (.sieve 2) (.branch 0 9 (.branch 2 14 (.sieve 1) (.branch 1 30 (.sieve 2) .score)) .score)))) (.branch 1 6 (.branch 2 6 (.sieve 0) (.branch 0 30 (.sieve 2) (.branch 1 4 (.branch 2 14 (.sieve 0) (.branch 0 62 (.sieve 2) .score)) .score))) (.branch 2 6 (.branch 0 30 (.sieve 1) (.branch 1 14 (.sieve 0) .score)) .score)))))))
theorem exclude7 (e : I3 → ℕ) (pos : ∀ i, 0<e i) :
    OeisA245212.a (total (P 7) e) ≠ (σ 1 (total (P 7) e) : ℤ) := by
  intro eq
  have ok : supported 7 := by unfold supported; decide +kernel
  exact Trace.sound ok witness7 initial (by decide +kernel) e (initial_fits ok e pos eq) eq
end OMA.TriSupport245212

end

section

/- Fixed three-prime support (3,5,11) with unrestricted positive exponents. -/
namespace OMA.TriSupport245212
open OMA.Smooth245212
open scoped ArithmeticFunction.sigma
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private def witness11 : Trace := (.branch 0 2 .score (.branch 0 6 (.branch 1 2 .score .score) (.branch 1 2 .score (.branch 0 14 (.branch 1 6 .score (.branch 2 2 .score (.branch 1 14 .score .score))) (.branch 1 6 (.branch 2 2 .score .score) (.branch 2 2 (.branch 0 30 .score .score) (.branch 0 30 (.branch 1 14 .score (.branch 2 6 (.sieve 1) (.branch 1 30 (.branch 0 20 .score (.branch 2 14 (.sieve 1) (.branch 1 20 (.sieve 2) (.branch 0 24 (.sieve 2) (.sieve 2))))) (.branch 0 20 (.branch 2 14 (.sieve 1) (.branch 1 62 (.branch 0 17 .score (.sieve 2)) (.branch 0 17 (.branch 2 30 .score (.branch 1 126 (.branch 0 15 .score (.branch 2 62 .score (.branch 1 84 .score (.sieve 2)))) (.branch 0 15 .score (.branch 2 62 (.sieve 1) (.branch 1 254 (.branch 0 16 .score (.branch 2 126 (.sieve 1) (.branch 1 169 (.sieve 2) .score))) (.branch 0 16 (.branch 2 126 (.sieve 1) (.branch 1 510 (.branch 2 254 (.branch 1 340 .score (.branch 2 169 .score (.sieve 1))) (.branch 1 340 (.sieve 2) (.branch 2 510 (.branch 1 408 (.sieve 2) (.branch 2 340 (.sieve 1) .score)) (.branch 1 408 (.sieve 2) .score)))) (.branch 2 254 (.branch 1 1022 (.branch 2 169 (.sieve 1) (.sieve 1)) (.branch 2 169 (.sieve 1) .score)) .score))) .score)))))) (.branch 2 30 (.sieve 1) (.branch 1 126 (.branch 2 62 (.sieve 1) (.branch 0 18 (.sieve 2) (.branch 1 84 (.sieve 2) .score))) (.branch 2 62 (.sieve 1) .score)))))) (.branch 2 14 (.sieve 1) (.branch 1 62 (.branch 0 24 (.branch 2 30 (.sieve 1) (.branch 1 41 (.sieve 2) (.sieve 2))) (.branch 2 30 (.sieve 1) .score)) (.branch 0 24 (.branch 2 30 (.sieve 1) .score) .score))))))) (.branch 1 14 (.branch 2 6 (.sieve 0) (.branch 0 62 (.branch 1 9 .score (.branch 2 14 .score (.branch 0 41 (.sieve 2) (.branch 2 30 (.sieve 0) (.branch 1 11 (.sieve 2) (.sieve 2)))))) (.branch 1 9 (.branch 2 14 .score (.branch 0 126 (.branch 1 7 .score (.branch 2 30 .score (.branch 0 84 .score (.sieve 2)))) (.branch 1 7 .score (.branch 2 30 (.sieve 0) (.branch 0 254 (.branch 2 62 (.sieve 0) (.branch 1 8 (.branch 0 169 .score (.sieve 2)) (.branch 0 169 (.sieve 2) .score))) (.branch 2 62 (.sieve 0) (.branch 1 8 (.branch 0 510 (.branch 2 126 (.sieve 0) (.branch 0 340 (.sieve 2) .score)) .score) .score))))))) (.branch 2 14 (.sieve 0) (.branch 0 126 (.branch 2 30 (.sieve 0) (.branch 1 11 (.branch 0 84 (.sieve 2) (.sieve 2)) .score)) (.branch 2 30 (.sieve 0) .score)))))) (.branch 2 6 (.branch 1 30 (.sieve 0) (.branch 0 62 (.branch 2 4 (.sieve 1) (.sieve 1)) (.branch 2 4 (.branch 1 62 (.sieve 0) (.branch 0 126 (.branch 2 3 (.sieve 1) (.sieve 1)) (.branch 2 3 (.branch 1 126 (.sieve 0) (.branch 0 254 (.branch 1 254 (.branch 0 169 (.sieve 1) .score) .score) .score)) .score))) (.branch 1 62 (.sieve 0) .score)))) (.branch 1 30 (.branch 0 62 (.branch 2 14 (.branch 0 41 (.sieve 1) (.branch 1 20 (.sieve 0) (.sieve 0))) (.branch 0 41 (.branch 1 20 (.sieve 2) (.branch 2 30 (.branch 0 35 (.sieve 1) (.sieve 1)) .score)) (.branch 1 20 (.branch 2 30 (.branch 1 17 (.sieve 0) (.sieve 2)) .score) .score))) (.branch 2 14 (.branch 0 126 (.branch 1 20 (.sieve 0) (.sieve 0)) (.branch 1 20 (.sieve 0) .score)) .score)) (.branch 0 62 (.branch 2 14 (.branch 1 62 (.branch 0 41 (.sieve 1) (.branch 2 9 (.sieve 0) .score)) (.branch 0 41 (.sieve 1) .score)) .score) .score)))))))))))
theorem exclude11 (e : I3 → ℕ) (pos : ∀ i, 0<e i) :
    OeisA245212.a (total (P 11) e) ≠ (σ 1 (total (P 11) e) : ℤ) := by
  intro eq
  have ok : supported 11 := by unfold supported; decide +kernel
  exact Trace.sound ok witness11 initial (by decide +kernel) e (initial_fits ok e pos eq) eq
end OMA.TriSupport245212

end

section

/- Fixed three-prime support (3,5,13) with unrestricted positive exponents. -/
namespace OMA.TriSupport245212
open OMA.Smooth245212
open scoped ArithmeticFunction.sigma
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private def witness13 : Trace := (.branch 0 2 .score (.branch 0 6 (.branch 1 2 .score .score) (.branch 1 2 .score (.branch 0 14 .score (.branch 1 6 .score (.branch 2 2 .score (.branch 0 30 (.branch 1 14 .score (.branch 2 6 .score .score)) (.branch 1 14 .score (.branch 2 6 (.branch 1 30 .score (.branch 0 62 .score (.branch 2 4 .score (.branch 1 62 .score (.branch 0 126 .score (.branch 1 126 (.branch 0 254 .score (.branch 2 5 .score (.sieve 0))) (.branch 0 254 (.branch 2 5 .score (.branch 1 254 (.branch 0 169 .score (.sieve 1)) (.branch 0 169 (.sieve 1) (.sieve 1)))) (.branch 2 5 (.branch 1 254 (.branch 0 510 .score (.branch 0 1022 (.branch 1 169 .score (.sieve 0)) (.branch 1 169 (.sieve 0) (.sieve 0)))) (.branch 0 510 (.branch 1 510 (.branch 0 340 .score (.branch 1 340 .score (.branch 0 408 .score (.branch 1 408 .score (.branch 0 453 .score (.sieve 1)))))) (.branch 0 340 (.sieve 1) (.branch 1 1022 (.branch 0 408 (.sieve 1) (.branch 1 681 (.branch 0 453 (.sieve 1) (.sieve 1)) (.branch 0 453 (.sieve 1) .score))) (.branch 0 408 (.sieve 1) .score)))) (.branch 1 510 (.branch 0 1022 (.branch 0 681 (.branch 1 340 (.sieve 0) (.branch 0 583 (.sieve 1) (.branch 1 408 (.sieve 0) .score))) (.branch 1 340 (.sieve 0) .score)) .score) .score))) (.branch 1 254 (.branch 0 510 (.branch 0 340 (.sieve 1) .score) .score) .score))))))))) (.branch 1 30 (.branch 0 62 .score (.branch 2 14 (.branch 0 126 .score (.branch 1 20 .score (.sieve 0))) (.branch 0 126 (.branch 1 20 .score (.branch 2 30 (.branch 0 84 .score (.branch 1 24 .score (.sieve 0))) (.branch 0 84 (.branch 1 24 .score (.branch 2 62 (.branch 0 72 .score (.sieve 2)) (.branch 0 72 (.sieve 2) (.sieve 2)))) (.branch 1 24 (.branch 2 62 (.branch 0 101 .score (.branch 1 22 .score (.sieve 0))) (.branch 0 101 (.sieve 2) (.branch 1 22 (.sieve 2) (.sieve 2)))) (.branch 2 62 (.branch 0 101 (.branch 1 27 (.sieve 0) (.sieve 0)) (.branch 1 27 (.sieve 0) (.sieve 0))) (.branch 0 101 (.branch 1 27 (.sieve 2) (.sieve 2)) (.branch 1 27 (.sieve 2) .score))))))) (.branch 1 20 (.branch 2 30 (.sieve 0) (.branch 0 254 (.branch 1 17 .score (.branch 2 62 (.sieve 0) (.branch 0 169 (.branch 2 126 .score (.branch 1 18 .score (.sieve 2))) (.branch 2 126 (.branch 1 18 .score (.branch 0 203 (.sieve 2) (.branch 2 84 (.sieve 0) (.sieve 0)))) (.branch 1 18 (.sieve 2) (.branch 0 203 (.sieve 2) (.branch 2 254 (.branch 1 19 (.sieve 2) .score) .score))))))) (.branch 1 17 (.branch 2 62 (.sieve 0) (.branch 0 510 (.branch 1 15 .score (.branch 2 126 .score (.branch 0 340 (.branch 1 16 .score (.sieve 2)) (.branch 1 16 .score (.branch 2 254 (.branch 0 408 .score (.branch 2 169 (.sieve 0) (.sieve 0))) (.branch 0 408 (.sieve 2) (.branch 2 510 (.branch 0 453 (.sieve 2) .score) .score))))))) (.branch 1 15 .score (.branch 2 126 (.branch 0 1022 (.branch 1 16 .score (.sieve 0)) (.branch 1 16 (.sieve 0) (.sieve 0))) (.branch 0 1022 (.branch 1 16 (.branch 2 254 .score (.branch 0 681 .score (.branch 2 510 (.branch 0 818 .score (.branch 2 340 .score (.branch 0 909 .score (.branch 2 408 .score (.branch 0 962 (.sieve 2) (.sieve 2)))))) (.branch 0 818 (.branch 2 1022 .score (.branch 0 743 (.sieve 2) (.sieve 2))) (.branch 2 1022 (.branch 0 909 (.sieve 2) (.branch 2 681 (.branch 0 962 (.sieve 2) .score) .score)) (.branch 0 909 (.sieve 2) .score)))))) (.branch 2 254 (.branch 0 681 (.branch 2 169 (.sieve 0) .score) .score) .score)) (.branch 1 16 (.branch 2 254 (.branch 0 2046 (.branch 2 169 .score (.sieve 0)) (.branch 2 169 (.sieve 0) (.sieve 0))) (.branch 0 2046 (.branch 2 510 (.branch 0 1364 (.branch 2 340 (.sieve 0) (.branch 0 1169 (.branch 2 408 (.sieve 0) (.branch 0 1091 (.sieve 2) .score)) .score)) (.branch 2 340 (.sieve 0) .score)) .score) .score)) .score)))))) (.branch 2 62 (.sieve 0) (.branch 0 510 (.branch 2 126 (.branch 1 18 (.sieve 0) (.branch 0 340 (.branch 2 84 (.sieve 0) .score) .score)) (.branch 1 18 (.branch 0 340 (.sieve 2) .score) .score)) (.branch 2 126 (.branch 1 18 (.sieve 0) .score) .score)))))) (.branch 2 30 (.branch 0 254 (.branch 1 24 (.sieve 0) (.sieve 0)) (.branch 1 24 (.sieve 0) (.sieve 0))) (.branch 0 254 (.branch 1 24 (.branch 2 62 (.branch 0 169 (.branch 1 22 (.sieve 0) (.sieve 0)) (.branch 1 22 (.sieve 0) (.sieve 0))) (.branch 0 169 (.branch 1 22 (.sieve 2) (.sieve 2)) (.branch 1 22 (.branch 2 126 (.branch 0 203 (.sieve 2) .score) .score) .score))) (.branch 2 62 (.branch 0 169 (.branch 1 27 (.sieve 0) .score) .score) .score)) (.branch 1 24 (.branch 2 62 (.branch 0 510 (.branch 1 22 (.sieve 0) .score) .score) .score) .score))))))) (.branch 0 62 (.branch 2 14 (.branch 1 62 .score (.branch 0 41 .score (.branch 2 9 .score (.branch 1 126 (.branch 0 50 .score (.sieve 1)) (.branch 0 50 (.sieve 1) (.sieve 1)))))) (.branch 1 62 (.branch 0 41 .score (.branch 2 30 (.branch 1 41 .score (.branch 0 50 .score (.branch 2 20 .score (.branch 1 50 .score (.branch 0 55 .score (.sieve 1)))))) (.branch 1 41 (.branch 0 50 .score (.branch 2 62 (.branch 1 35 .score (.sieve 2)) (.branch 1 35 (.sieve 2) (.sieve 2)))) (.branch 0 50 (.branch 2 62 (.branch 1 50 .score (.branch 0 45 .score (.sieve 2))) (.branch 1 50 (.sieve 2) (.branch 0 45 (.sieve 2) (.sieve 2)))) (.branch 2 62 (.branch 1 50 (.branch 0 55 (.sieve 2) (.sieve 2)) (.branch 0 55 (.sieve 2) (.sieve 2))) (.branch 1 50 (.branch 0 55 (.sieve 2) (.sieve 2)) (.branch 0 55 (.sieve 2) .score))))))) (.branch 0 41 (.branch 2 30 (.branch 1 126 .score (.branch 0 35 .score (.sieve 1))) (.branch 1 126 (.branch 0 35 .score (.branch 2 62 (.branch 1 84 .score (.branch 0 38 .score (.sieve 1))) (.branch 1 84 (.branch 0 38 .score (.sieve 2)) (.branch 0 38 (.branch 2 126 .score (.branch 1 101 (.sieve 2) (.sieve 2))) (.branch 2 126 (.branch 1 101 (.sieve 2) (.sieve 2)) (.branch 1 101 (.sieve 2) (.sieve 2))))))) (.branch 0 35 (.branch 2 62 (.branch 1 254 .score (.branch 0 32 .score (.sieve 1))) (.branch 1 254 (.branch 0 32 .score (.branch 2 126 .score (.branch 1 169 (.branch 0 33 .score (.sieve 2)) (.branch 0 33 .score (.branch 2 254 (.branch 1 203 .score (.branch 0 34 .score (.sieve 2))) (.branch 1 203 (.sieve 2) (.branch 0 34 (.sieve 2) (.sieve 2)))))))) (.branch 0 32 (.branch 2 126 .score (.branch 1 510 .score (.branch 2 254 .score (.branch 1 1022 .score (.branch 0 31 .score (.branch 2 510 (.branch 1 2046 .score (.branch 2 340 .score (.branch 1 4094 (.branch 2 408 .score (.branch 1 2729 .score (.branch 2 453 .score (.sieve 1)))) (.branch 2 408 (.sieve 1) (.branch 1 8190 (.branch 2 453 (.sieve 1) (.sieve 1)) .score))))) (.branch 1 2046 (.branch 2 1022 (.branch 1 1364 .score (.branch 2 681 .score (.branch 1 1637 (.branch 2 818 .score (.branch 1 1488 .score (.branch 2 909 .score (.branch 1 1559 .score (.sieve 2))))) (.branch 2 818 (.branch 1 1819 .score (.branch 2 743 (.sieve 1) (.sieve 1))) (.branch 1 1819 (.branch 2 909 (.sieve 1) (.branch 1 1723 (.sieve 2) .score)) (.branch 2 909 (.sieve 1) .score)))))) (.branch 1 1364 (.branch 2 2046 (.branch 1 1169 .score (.branch 2 1364 .score (.branch 1 1259 .score (.branch 2 1637 (.branch 1 1309 .score (.sieve 2)) (.branch 1 1309 (.sieve 2) (.sieve 2)))))) (.branch 1 1169 (.branch 2 4094 (.branch 1 1091 .score (.sieve 2)) (.branch 1 1091 (.sieve 2) (.sieve 2))) (.branch 2 4094 (.branch 1 1259 (.sieve 2) (.branch 2 2729 (.branch 1 1309 (.sieve 2) .score) .score)) .score))) (.branch 2 2046 (.branch 1 1637 (.branch 2 1364 (.branch 1 1488 (.branch 2 1169 .score (.branch 1 1423 (.sieve 2) (.sieve 2))) (.branch 2 1169 (.branch 1 1559 (.sieve 2) (.sieve 2)) (.branch 1 1559 (.sieve 2) .score))) (.branch 1 1488 (.branch 2 1637 (.branch 1 1423 (.sieve 2) .score) .score) .score)) .score) .score))) (.branch 2 1022 (.branch 1 4094 (.branch 2 681 (.branch 1 2729 (.branch 2 583 (.sieve 1) (.branch 1 2339 (.branch 2 628 .score (.sieve 1)) (.branch 2 628 (.sieve 1) (.sieve 1)))) (.branch 2 583 (.sieve 1) .score)) (.branch 1 2729 (.branch 2 818 (.branch 1 2339 (.branch 2 743 (.sieve 1) .score) .score) .score) .score)) .score) .score)))))))) (.branch 2 126 (.branch 1 510 (.branch 0 33 .score (.branch 2 84 (.sieve 1) (.sieve 1))) (.branch 0 33 (.sieve 1) (.branch 2 84 (.sieve 1) (.sieve 1)))) (.branch 1 510 (.branch 0 33 (.branch 2 254 .score (.branch 1 340 .score (.branch 2 510 (.branch 1 408 .score (.branch 2 340 .score (.branch 1 453 .score (.sieve 2)))) (.branch 1 408 (.sieve 2) (.branch 2 1022 (.branch 1 453 (.sieve 2) (.sieve 2)) (.branch 1 453 (.sieve 2) .score)))))) (.branch 2 254 (.branch 1 340 (.branch 0 34 (.sieve 2) (.sieve 2)) (.branch 0 34 (.branch 2 169 (.sieve 1) (.sieve 1)) .score)) (.branch 1 340 (.branch 0 34 (.sieve 2) .score) .score))) (.branch 0 33 (.branch 2 254 (.branch 1 1022 (.branch 2 169 .score (.sieve 1)) (.branch 2 169 (.sieve 1) (.sieve 1))) (.branch 1 1022 (.branch 2 510 (.branch 1 681 (.branch 2 340 (.sieve 1) (.branch 1 583 (.sieve 2) .score)) (.branch 2 340 (.sieve 1) .score)) .score) .score)) (.branch 2 254 (.branch 1 1022 (.branch 0 34 (.branch 2 169 (.sieve 1) .score) .score) .score) .score))))))) (.branch 2 62 (.branch 1 254 (.branch 0 38 (.sieve 1) (.sieve 1)) (.branch 0 38 (.sieve 1) (.sieve 1))) (.branch 1 254 (.branch 0 38 (.branch 2 126 (.branch 1 169 (.branch 0 36 .score (.sieve 2)) (.branch 0 36 (.sieve 1) (.branch 2 84 (.sieve 1) (.sieve 1)))) (.branch 1 169 (.branch 0 36 (.sieve 2) (.sieve 2)) (.branch 0 36 (.sieve 2) .score))) (.branch 2 126 (.branch 1 169 (.branch 2 84 (.sieve 1) .score) .score) .score)) (.branch 0 38 (.branch 2 126 (.branch 1 510 (.branch 0 36 (.sieve 1) (.branch 2 84 (.sieve 1) .score)) .score) .score) .score)))))) (.branch 2 30 (.branch 1 126 (.branch 0 50 (.branch 2 20 .score (.sieve 1)) (.branch 2 20 (.sieve 1) (.branch 1 84 (.branch 0 55 (.sieve 1) (.sieve 1)) (.branch 0 55 (.sieve 1) (.sieve 1))))) (.branch 0 50 (.branch 2 20 (.sieve 1) (.sieve 1)) (.branch 2 20 (.sieve 1) .score))) (.branch 1 126 (.branch 0 50 (.branch 2 62 (.branch 1 84 (.branch 0 45 (.sieve 2) (.branch 2 41 (.sieve 1) (.branch 1 72 (.sieve 2) (.sieve 2)))) (.branch 0 45 (.branch 2 41 (.sieve 1) (.sieve 1)) (.branch 2 41 (.sieve 1) (.branch 1 101 (.sieve 2) .score)))) (.branch 1 84 (.branch 0 45 (.sieve 2) (.branch 2 126 (.branch 1 72 (.sieve 2) .score) .score)) (.branch 0 45 (.branch 2 126 (.branch 1 101 (.sieve 2) .score) .score) .score))) (.branch 2 62 (.branch 1 84 (.branch 0 55 (.branch 2 41 (.sieve 1) (.branch 1 72 (.sieve 2) .score)) .score) .score) .score)) (.branch 0 50 (.branch 2 62 (.branch 1 254 (.branch 0 45 (.branch 2 41 (.sieve 1) (.sieve 1)) .score) .score) .score) .score)))))) (.branch 2 14 (.branch 1 62 (.branch 0 126 (.branch 2 9 .score (.branch 0 84 (.branch 1 41 .score (.branch 2 11 .score (.sieve 0))) (.branch 1 41 (.sieve 0) (.branch 2 11 (.sieve 0) (.sieve 0))))) (.branch 2 9 (.sieve 0) (.branch 0 254 (.branch 1 41 (.sieve 0) (.branch 2 11 (.sieve 0) (.sieve 0))) (.branch 1 41 (.sieve 0) .score)))) (.branch 0 126 (.branch 2 9 (.branch 1 126 (.branch 0 84 .score (.branch 2 7 .score (.sieve 1))) (.branch 0 84 (.sieve 1) (.branch 2 7 (.sieve 1) (.sieve 1)))) (.branch 1 126 (.branch 0 84 (.branch 2 11 (.sieve 1) (.sieve 1)) (.branch 2 11 (.sieve 1) (.branch 1 84 (.sieve 0) .score))) (.branch 0 84 (.branch 2 11 (.sieve 1) (.sieve 1)) .score))) (.branch 2 9 (.branch 1 126 (.branch 0 254 (.branch 2 7 (.sieve 0) (.branch 0 169 (.sieve 1) (.branch 1 84 (.sieve 0) .score))) (.branch 2 7 (.sieve 0) .score)) (.branch 0 254 (.branch 2 7 (.branch 1 254 (.branch 0 169 (.sieve 1) .score) .score) .score) .score)) .score))) (.branch 1 62 (.branch 0 126 (.branch 2 30 (.branch 0 84 (.branch 1 41 (.branch 2 20 .score (.branch 0 72 .score (.branch 1 35 .score (.sieve 0)))) (.branch 2 20 (.branch 0 72 (.sieve 1) (.sieve 1)) (.branch 0 72 (.branch 1 50 (.sieve 0) (.branch 2 24 (.sieve 0) (.sieve 0))) (.branch 1 50 (.sieve 0) .score)))) (.branch 1 41 (.branch 2 20 (.sieve 0) (.branch 0 101 (.branch 1 35 (.sieve 0) (.sieve 0)) (.branch 1 35 (.sieve 0) .score))) (.branch 2 20 (.branch 0 101 (.branch 1 50 (.sieve 0) (.sieve 0)) (.branch 1 50 (.sieve 0) .score)) .score))) (.branch 0 84 (.branch 1 41 (.branch 2 62 (.branch 0 72 (.branch 1 35 (.sieve 2) (.sieve 2)) (.branch 1 35 (.sieve 2) (.sieve 2))) (.branch 0 72 (.branch 1 35 (.sieve 2) (.sieve 2)) (.branch 1 35 (.sieve 2) .score))) (.branch 2 62 (.branch 0 72 (.branch 1 50 (.sieve 2) .score) .score) .score)) (.branch 1 41 (.branch 2 62 (.branch 0 101 (.branch 1 35 (.sieve 2) .score) .score) .score) .score))) (.branch 2 30 (.branch 0 254 (.branch 1 41 (.branch 2 20 (.sieve 0) (.branch 0 169 (.branch 1 35 (.sieve 0) .score) .score)) .score) .score) .score)) (.branch 0 126 (.branch 2 30 (.branch 1 126 (.branch 0 84 (.branch 2 20 (.branch 1 84 (.branch 0 72 (.sieve 1) (.sieve 1)) (.branch 0 72 (.sieve 1) .score)) (.branch 1 84 (.branch 0 72 (.branch 2 24 (.sieve 0) .score) .score) .score)) .score) .score) .score) .score))))))))))))))
theorem exclude13 (e : I3 → ℕ) (pos : ∀ i, 0<e i) :
    OeisA245212.a (total (P 13) e) ≠ (σ 1 (total (P 13) e) : ℤ) := by
  intro eq
  have ok : supported 13 := by unfold supported; decide +kernel
  exact Trace.sound ok witness13 initial (by decide +kernel) e (initial_fits ok e pos eq) eq
end OMA.TriSupport245212

end

section

/- Classify all odd solutions supported on at most three different primes. -/
namespace OMA.OddSupportClass245212
open scoped ArithmeticFunction.sigma

theorem three_excluded : ThreeExcluded := by
  intro q h
  rcases h with rfl|rfl|rfl
  · exact OMA.TriSupport245212.exclude7
  · exact OMA.TriSupport245212.exclude11
  · exact OMA.TriSupport245212.exclude13

/-- The only odd solution with at most three distinct prime divisors is one. -/
theorem odd_three {n : ℕ} (odd : Odd n) (few : n.primeFactors.card≤3)
    (eq : OeisA245212.a n=(σ 1 n:ℤ)) : n=1 :=
  classify three_excluded n odd (by omega) (fun h => False.elim (by omega)) eq

#print axioms odd_three
end OMA.OddSupportClass245212

end
