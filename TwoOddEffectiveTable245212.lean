import FormalConjectures.OEIS.«245212»

/-! Exact scalar comparisons in the finite part of the uniform smaller
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

#print axioms ranges
end OMA.TwoOddEffectiveTable245212
