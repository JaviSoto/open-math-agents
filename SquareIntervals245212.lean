import SquareCoreBound245212

/-! Certify gaps between successive integer quotients on quadratic intervals. -/
namespace OMA.SquareIntervals245212
open OMA.SquareCoreBound245212

structure Quad where
  a : ℤ
  b : ℤ
  c : ℤ

def Quad.eval (f : Quad) (x : ℤ) := f.a*x^2+f.b*x+f.c
def submul (f : Quad) (m : ℤ) (g : Quad) : Quad := ⟨f.a-m*g.a,f.b-m*g.b,f.c-m*g.c⟩
theorem submul_eval (f : Quad) (m : ℤ) (g : Quad) (x : ℤ) :
    (submul f m g).eval x=f.eval x-m*g.eval x := by simp only [submul,Quad.eval]; ring
def numerator (k z : ℤ) : Quad := ⟨z*(3*k+1)+2,z*(2*k+1)+1,z*(k+1)⟩
def denominator (k z : ℤ) : Quad := ⟨5*z-5,-z*(4*k+1)-3,-z*(2*k+1)-1⟩
theorem nv (k q z : ℤ) : (numerator k z).eval q=num k q z := by
  simp only [Quad.eval,numerator,num]; ring
theorem dv (k q z : ℤ) : (denominator k z).eval q=den k q z := by
  simp only [Quad.eval,denominator,den]; ring

def above (f : Quad) (l h : ℤ) : Bool :=
  decide (0<f.eval l ∧ 0≤2*f.eval l+(2*f.a*l+f.b)*(h-l) ∧ 0<f.eval h)

theorem positive {f : Quad} {l h x : ℤ} (yes : above f l h=true) (low : l≤x) (high : x≤h) :
    0<f.eval x := by
  obtain ⟨a,b,c⟩ := of_decide_eq_true yes
  by_cases atEnd : x=h
  · simpa only [atEnd] using c
  have hx : 0<h-x := by omega
  have xl : 0≤x-l := by omega
  have identity : f.eval x*(h-l)^2 = f.eval l*(h-x)^2 +
      (2*f.eval l+(2*f.a*l+f.b)*(h-l))*(h-x)*(x-l)+f.eval h*(x-l)^2 := by
    simp only [Quad.eval]; ring
  have pp : 0<f.eval l*(h-x)^2 := mul_pos a (sq_pos_of_pos hx)
  have nn := mul_nonneg (mul_nonneg b hx.le) xl
  have nh := mul_nonneg c.le (sq_nonneg (x-l))
  by_contra! bad
  have non := mul_nonpos_of_nonpos_of_nonneg bad (sq_nonneg (h-l))
  omega

def gaps (n d : Quad) (l h : ℕ) : Bool :=
  let m := n.eval l / d.eval l
  above (submul n m d) l h &&
    above (submul (submul ⟨0,0,0⟩ (-(m+1)) d) 1 n) l h

def check (n d : Quad) (l h : ℕ) : ℕ → Bool
  | 0 => false
  | fuel+1 =>
    if above (submul ⟨0,0,1⟩ 1 d) l h then true
    else if gaps n d l h then true
    else if l=h then decide (Even l)
    else let mid := (l+h)/2
         check n d l mid fuel && check n d (mid+1) h fuel

theorem sound (n d : Quad) {q : ℕ} {p : ℤ} (odd : Odd q) (hd : 0<d.eval q)
    (eqn : n.eval q=p*d.eval q) (fuel l h : ℕ) (yes : check n d l h fuel=true)
    (low : l≤q) (high : q≤h) : False := by
  induction fuel generalizing l h with
  | zero => simp [check] at yes
  | succ fuel ih =>
    have a : (l:ℤ)≤q := by exact_mod_cast low
    have b : (q:ℤ)≤h := by exact_mod_cast high
    rw [check] at yes
    split at yes
    next cert =>
      have v := positive cert a b
      rw [submul_eval] at v
      rw [show (⟨0,0,1⟩:Quad).eval (q:ℤ)=1 by simp [Quad.eval],one_mul] at v
      omega
    next =>
      split at yes
      next cert =>
        obtain ⟨c1,c2⟩ := Bool.and_eq_true_iff.mp cert
        have v1 := positive c1 a b
        have v2 := positive c2 a b
        rw [submul_eval,eqn] at v1
        rw [submul_eval,submul_eval,eqn] at v2
        rw [show (⟨0,0,0⟩:Quad).eval (q:ℤ)=0 by simp [Quad.eval],one_mul] at v2
        let m := n.eval l/d.eval l
        have left : m*d.eval q<p*d.eval q := by change 0<p*d.eval q-m*d.eval q at v1; omega
        have right : p*d.eval q<(m+1)*d.eval q := by
          change 0<0-(-(m+1))*d.eval q-p*d.eval q at v2
          linarith only [v2]
        have := (mul_lt_mul_iff_left₀ hd).mp left
        have := (mul_lt_mul_iff_left₀ hd).mp right
        omega
      next =>
        split at yes
        next same =>
          have v : Even l := of_decide_eq_true yes
          have eql : l=q := by omega
          exact (Nat.not_even_iff_odd.mpr odd) (eql ▸ v)
        next =>
          obtain ⟨left,right⟩ := Bool.and_eq_true_iff.mp yes
          by_cases mid : q≤(l+h)/2
          · exact ih _ _ left low mid
          · exact ih _ _ right (by omega) high

def row (k : ℕ) : Bool :=
  let z : ℤ := 2^(k+1)
  check (numerator k z) (denominator k z) 3 (2^20-1) 23

end OMA.SquareIntervals245212
