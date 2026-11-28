import MollActual

/-! Two factorial-scaled binomial coefficients give the two evaluations of
the actual Gaussian product in any finite ring in which -1 splits. -/
namespace OMA.MollSegment
open Finset

theorem choose_prime_digit (p : ℕ) [hp : Fact p.Prime] (m n : ℕ) :
    n.choose (p^m) ≡ n / p^m [MOD p] := by
  induction m generalizing n with
  | zero => simp [Nat.ModEq]
  | succ m ih =>
    have eq := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n:=n) (k:=p^(m+1)) (p:=p)
    rw [pow_succ, Nat.mul_mod_left, Nat.mul_div_cancel _ hp.out.pos,
      Nat.choose_zero_right, one_mul] at eq
    simpa [Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm] using eq.trans (ih (n/p))

theorem two_binomials (q r n : ℕ) (hn : n ≤ r)
    (root : (r:ZMod q)*(r:ZMod q)=-1) :
    2*(r:ZMod q)^(n+1)*(r:ZMod q)*(OeisA105751.a n:ZMod q) =
      ((n+1).factorial:ZMod q) * ((r.choose (n+1):ZMod q)-((r+n).choose (n+1):ZMod q)) := by
  let u : ZMod q := r
  let pos : GaussianInt →+* ZMod q := Zsqrtd.lift ⟨u,by simpa using root⟩
  let neg : GaussianInt →+* ZMod q := Zsqrtd.lift ⟨-u,by simpa [u] using root⟩
  have const : u^(n+1) = ∏ _k ∈ range (n+1), u := by simp
  have lhs : u^(n+1)*pos (full n) = (r.descFactorial (n+1):ZMod q) := by
    rw [full, map_prod, Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    rw [const, ← prod_mul_distrib]
    apply prod_congr rfl
    intro k hk
    simp only [pos, Zsqrtd.lift_apply_apply, Int.cast_one, Int.cast_natCast]
    rw [Nat.cast_sub (by have := mem_range.mp hk; omega)]
    dsimp [u]; linear_combination (k:ZMod q)*root
  have rhs : u^(n+1)*neg (full n) = (r.ascFactorial (n+1):ZMod q) := by
    rw [full, map_prod, Nat.ascFactorial_eq_prod_range, Nat.cast_prod]
    rw [const, ← prod_mul_distrib]
    apply prod_congr rfl
    intro k _
    simp only [neg, Zsqrtd.lift_apply_apply, Int.cast_one, Int.cast_natCast]
    push_cast; dsimp [u]; linear_combination -(k:ZMod q)*root
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul] at lhs
  rw [Nat.ascFactorial_eq_factorial_mul_choose', Nat.cast_mul,
    show r+(n+1)-1=r+n by omega] at rhs
  rw [sequence_eq_im]
  change u^(n+1)*((full n).re+(full n).im*u) = _ at lhs
  change u^(n+1)*((full n).re+(full n).im*(-u)) = _ at rhs
  change 2*u^(n+1)*u*_ = _
  linear_combination lhs - rhs

end OMA.MollSegment
