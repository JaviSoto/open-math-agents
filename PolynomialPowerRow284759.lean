import Mathlib

/-! Short exact certificates of complete power sums. A list of integer
coefficients is evaluated by Horner's rule. Its shift by one certifies a
discrete antiderivative, so the row length need not be enumerated. -/
namespace OMA.PolynomialPowerRow284759
open Finset

def value : List ℤ → ℤ → ℤ
  | [], _ => 0
  | a::t, x => a + x * value t x

def plus : List ℤ → List ℤ → List ℤ
  | [], t => t
  | a::t, [] => a::t
  | a::t, b::u => (a+b)::plus t u

theorem value_plus (l r : List ℤ) (x : ℤ) :
    value (plus l r) x = value l x + value r x := by
  induction l generalizing r with
  | nil => simp [value,plus]
  | cons a l ih => cases r with
    | nil => simp [plus,value]
    | cons b r => simp only [plus,value,ih];ring

def shift : List ℤ → List ℤ
  | [] => []
  | a::t => let u := shift t; plus (a::u) u

theorem value_shift (l : List ℤ) (x : ℤ) : value (shift l) x = value l (x+1) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [shift,value_plus,value,ih];ring

def monomial (e : ℕ) (d : ℤ) := List.replicate e (0:ℤ) ++ [d]

theorem value_monomial (e : ℕ) (d x : ℤ) : value (monomial e d) x=d*x^e := by
  induction e with
  | zero => simp [monomial,value]
  | succ e ih =>
    rw [monomial, List.replicate_succ, List.cons_append, value, zero_add]
    change x*value (monomial e d) x=_
    rw [ih,pow_succ];ring

theorem integral (e : ℕ) (d : ℕ) (l : List ℤ)
    (h : shift l = plus l (monomial e d)) (n : ℕ) :
    (d:ℤ)*(∑ i∈range n, (i:ℤ)^e) = value l n - value l 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have step := congrArg (fun t => value t n) h
    simp only [value_shift,value_plus,value_monomial] at step
    rw [sum_range_succ,mul_add,ih,Nat.cast_succ,step];ring

theorem row {e d n m : ℕ} (l : List ℤ)
    (cert : shift l = plus l (monomial e d)) (unit : d.Coprime m)
    (endpoints : (m:ℤ) ∣ value l n - value l 0) :
    (∑ i∈range n,(i:ZMod m)^e)=0 := by
  have zz := integral e d l cert n
  have div : (m:ℤ) ∣ (d:ℤ)*(∑ i∈range n,(i:ℤ)^e) := zz.symm ▸ endpoints
  have z := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr div
  push_cast at z
  exact ((ZMod.isUnit_iff_coprime d m).mpr unit).mul_right_inj.mp (by simpa using z)

#print axioms row
end OMA.PolynomialPowerRow284759
