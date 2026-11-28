import OddFourSolution245212
import FourPrimeLanes245212
import Q511All
import Q513WheelAll

/-! Complete classification of odd A245212 solutions on at most four prime divisors. -/
namespace OMA.OddSupportClass245212
open OMA.Box245212 OMA.FourPrimeLanes245212
open private OMA.FourPrimeLanes245212.cover from FourPrimeLanes245212
open scoped ArithmeticFunction.sigma

/-- For arbitrary positive exponents and arbitrary odd primes, one is the unique solution. -/
theorem odd_four {n : ℕ} (odd : Odd n) (few : n.primeFactors.card≤4)
    (eq : OeisA245212.a n=(σ 1 n:ℤ)) : n=1 :=
  odd_four_of_roots (roots_of_two
      (OMA.FourPrimeLanes245212.cover OMA.Blocks5_11_245212.deny5_11 (by decide +kernel))
      (OMA.FourPrimeLanes245212.cover OMA.Blocks5_13_245212.deny5_13 (by decide +kernel))) odd few eq

#print axioms odd_four
end OMA.OddSupportClass245212
