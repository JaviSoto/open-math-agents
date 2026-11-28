import OddThreeResearch245212

/-! A rational interval proof for the three limiting products of the five-prime branch. -/
namespace OMA.FiveFace245212
open OMA.Smooth245212 OMA.Moving245212

def gap : ℚ := 1/100000000
def away (z : ℚ) := z<2-gap ∨ 2+gap<z
def cutL (b : Band) (c : ℕ) : Band := ⟨b.lo,some c⟩
def cutR (b : Band) (c : ℕ) : Band := ⟨c+1,b.hi⟩
inductive Cert where
  | leaf
  | fst (cut : ℕ) (l r : Cert)
  | snd (cut : ℕ) (l r : Cert)
def check (A : ℚ) (p q : ℕ) : Cert → Band → Band → Bool
  | .leaf,a,b => decide (A*xu (single p) a*xu (single q) b<2-gap ∨
                        2+gap<A*xl (single p) a*xl (single q) b)
  | .fst c l r,a,b => check A p q l (cutL a c) b && check A p q r (cutR a c) b
  | .snd c l r,a,b => check A p q l a (cutL b c) && check A p q r a (cutR b c)
def Good (A : ℚ) (p q : ℕ) (a b : Band) :=
  ∀ f g, a.Contains f → b.Contains g → away (A*X p (some f)*X q (some g))
theorem first {A : ℚ} {p q c : ℕ} {a b : Band}
    (l : Good A p q (cutL a c) b) (r : Good A p q (cutR a c) b) : Good A p q a b := by
  intro f g hf hg
  by_cases h : f≤c
  · exact l f g ⟨hf.1,by simpa [cutL] using h⟩ hg
  · exact r f g ⟨by exact Nat.lt_of_not_ge h,hf.2⟩ hg
theorem second {A : ℚ} {p q c : ℕ} {a b : Band}
    (l : Good A p q a (cutL b c)) (r : Good A p q a (cutR b c)) : Good A p q a b := by
  intro f g hf hg
  by_cases h : g≤c
  · exact l f g hf ⟨hg.1,by simpa [cutL] using h⟩
  · exact r f g hf ⟨by exact Nat.lt_of_not_ge h,hg.2⟩
theorem sound {A : ℚ} {p q : ℕ} (hA : 0≤A) (hp : 1<p) (hq : 1<q)
    (t : Cert) {a b : Band} (checked : check A p q t a b=true) : Good A p q a b := by
  induction t generalizing a b with
  | leaf =>
    intro f g hf hg
    have x := factor_bounds (pb:=single p) (eb:=a) (p:=p) hp (by simp [single,Band.Contains]) hf
    have y := factor_bounds (pb:=single q) (eb:=b) (p:=q) hq (by simp [single,Band.Contains]) hg
    obtain u|l := of_decide_eq_true checked
    · left
      exact lt_of_le_of_lt (mul_le_mul (mul_le_mul_of_nonneg_left x.2.2.1 hA) y.2.2.1
        (x_nonneg hq _) (mul_nonneg hA (x.1.trans (x.2.1.trans x.2.2.1)))) u
    · right
      exact lt_of_lt_of_le l (mul_le_mul (mul_le_mul_of_nonneg_left x.2.1 hA) y.2.1 y.1
        (mul_nonneg hA (x_nonneg hp _)))
  | fst c l r il ir =>
    obtain ⟨l,r⟩ := Bool.and_eq_true_iff.mp checked
    exact first (il l) (ir r)
  | snd c l r il ir =>
    obtain ⟨l,r⟩ := Bool.and_eq_true_iff.mp checked
    exact second (il l) (ir r)
end OMA.FiveFace245212
