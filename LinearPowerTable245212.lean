import FormalConjectures.OEIS.«245212»

/-! Evidence for the residual finite table of the linear complementary
prime family. Composite values of the power base are also checked. -/
namespace OMA.LinearPowerTable245212

def cap (K : ℕ) := 480000*(2^(2*K))*K^4

def test (p K a : ℕ) : Bool :=
  let P := p^a
  let S := (p*P-1)/(p-1)
  let W := ((a+1)*p*P-S)/(p-1)
  let z := 2^K
  let A := (1+(K-1)*z)*W
  let U := (z-1)*S
  let D := 2*z*K*(a+1)*P-2*A-U
  D == 0 || (A+U)%D != 0

def row (p K : ℕ) : Bool :=
  let bound := cap K
  if p^35>bound then true else
  (List.range' 35 (min 199 (Nat.log p bound)+1-35)).all (test p K)

def base (p : ℕ) : Bool :=
  let K := min 127 (2*p)
  if p^35>cap K then true else
  (List.range' 1 K).all (row p)

def block (p length : ℕ) : Bool := (List.range' p length).all base

private theorem cap_mono : Monotone cap := by
  intro i j le
  unfold cap
  gcongr
  decide

theorem inside {p K a : ℕ} (hp : 3≤p) (top : p≤640)
    (pos : 1≤K) (limit : K≤127) (two : K≤2*p)
    (lo : 35≤a) (hi : a≤199) (power : p^a≤cap K)
    (checked : block 3 638=true) : test p K a=true := by
  have baseOk := List.all_eq_true.mp checked p (List.mem_range'_1.mpr ⟨hp,by omega⟩)
  have kp : K ≤ min 127 (2*p) := le_min limit two
  have first : p^35≤cap K := (Nat.pow_le_pow_right (by omega) lo).trans power
  have total := first.trans (cap_mono kp)
  unfold base at baseOk
  rw [if_neg (not_lt.mpr total)] at baseOk
  have rowOk := List.all_eq_true.mp baseOk K (List.mem_range'_1.mpr ⟨pos,by omega⟩)
  unfold row at rowOk
  rw [if_neg (not_lt.mpr first)] at rowOk
  have amax : a ≤ min 199 (Nat.log p (cap K)) :=
    le_min hi (Nat.le_log_of_pow_le (by omega) power)
  exact List.all_eq_true.mp rowOk a (List.mem_range'_1.mpr ⟨lo,by omega⟩)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked : block 3 638 = true := by decide +kernel

end OMA.LinearPowerTable245212
