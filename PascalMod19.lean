import PascalPowerSum19

namespace OMA.PascalMod19
open Nat Finset OMA.PascalPowerSum19

private theorem truncated {R:Type*} [CommRing R] (x:R) (four:x^4=0)
    (twice:2*x^3=0) (k:ℕ) :
    (1-x)^(2*k+1)=1-(2*(k:R)+1)*x+k*(2*(k:R)+1)*x^2-k*x^3 := by
  induction k with
  | zero=>simp
  | succ k ih=>
    rw [show 2*(k+1)+1=2*k+1+2 by omega,pow_add,ih]
    push_cast
    linear_combination (-2*(k:R)*(k+1))*twice + ((k:R)*(2*k+3)-k*x)*four

private theorem endpoint_zero {R:Type*} [CommRing R] (x:R) (four:x^4=0)
    (twice:2*x^3=0) (k:ℕ) (hk:0<k) :
    x^(2*k+2)-(x-1)^(2*k+2)+1+
    x*(k+1:R)*(x^(2*k+1)+(x-1)^(2*k+1)-1)=0 := by
  have exp:x^(2*k+2)=0:=by
    rw [show 2*k+2=4+(2*k-2) by omega,pow_add,four,zero_mul]
  have odd:(x-1)^(2*k+1) = -((1-x)^(2*k+1)):=by
    rw [show x-1= -(1-x) by ring,pow_succ,pow_succ,pow_mul,pow_mul];ring
  have main: (1+(k:R)*x)*(1-x)^(2*k+1)=1-(k+1:R)*x:=by
    rw [truncated x four twice]
    obtain ⟨a,ha⟩:=Int.even_mul_pred_self (k:ℤ)
    have parity:=congrArg (Int.cast (R:=R)) ha
    push_cast at parity
    linear_combination ((k:R)^3+(a:R))*twice - (k:R)^2*four + x^3*parity
  have rep:x*x^(2*k+1)=0:=calc
    _ = x^(2*k+1)*x := mul_comm _ _
    _ = x^(2*k+2) := (pow_succ x (2*k+1)).symm
    _ = 0 := exp
  rw [show 2*k+2=2*k+1+1 by omega,pow_succ (x-1),odd,exp]
  linear_combination -main + (k+1:R)*rep

def total (n k:ℕ) : ℕ :=
  ∑i∈range (k+1), (1+n*(k+1-i))*((2*k+2).choose (2*i))*(∑a∈Ico 1 n, a^(2*i))

private theorem total_succ (t k:ℕ) :
    (total (t+1) k:ℤ)=∑j∈range t, term (t+1) k ((j:ℤ)+1) := by
  unfold total term
  simp only [Finset.sum_Ico_eq_sum_range,Nat.succ_sub_succ_eq_sub,Nat.sub_zero]
  push_cast
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply sum_congr rfl;intro j _
  apply sum_congr rfl;intro i _
  ring

private theorem doubled {t k M:ℕ} (hk:0<k)
    (four:((t+1:ℕ):ZMod M)^4=0) (twice:2*((t+1:ℕ):ZMod M)^3=0) :
    M∣2*(total (t+1) k+1) := by
  let x:ZMod M:=(t+1:ℕ)
  have val:=endpoint t k
  rw [←total_succ] at val
  have casted:=congrArg (Int.cast (R:=ZMod M)) val
  push_cast at casted
  have tx:(t:ZMod M)=x-1:=by dsimp [x];push_cast;ring
  have nx:(t:ZMod M)+1=x:=by dsimp [x];push_cast;rfl
  rw [nx,tx,endpoint_zero x four twice k hk] at casted
  exact (ZMod.natCast_eq_zero_iff _ _).mp (by push_cast;exact casted)

/-- Meštrović's Conjecture 19, with the inner and outer sums exactly
as in the statement. Divisibility of total+1 is congruence to −1. -/
theorem conjecture {n k:ℕ} (pos:0<n) (en:Even n) (hk:0<k) : n^3∣total n k+1 := by
  obtain ⟨t,rfl⟩:=Nat.exists_eq_succ_of_ne_zero pos.ne'
  let n:=t+1
  let M:=2*n^3
  have four:(n:ZMod M)^4=0 := by
    rw [←Nat.cast_pow,ZMod.natCast_eq_zero_iff,pow_succ]
    dsimp [M];simpa only [mul_comm 2] using Nat.mul_dvd_mul_left (n^3) en.two_dvd
  have twice:2*(n:ZMod M)^3=0 := by
    rw [←Nat.cast_pow,←Nat.cast_ofNat,←Nat.cast_mul];exact ZMod.natCast_self M
  have dbl:=doubled hk four twice
  exact Nat.dvd_of_mul_dvd_mul_left (by decide : 0<2) dbl

theorem all_positive {n k:ℕ} (pos:0<n) (hk:0<k) : n^3∣total n k+1 := by
  rcases Nat.even_or_odd n with en|on
  · exact conjecture pos en hk
  obtain ⟨t,rfl⟩:=Nat.exists_eq_succ_of_ne_zero pos.ne'
  let n:=t+1
  have cube:(n:ZMod (n^3))^3=0:=by rw [←Nat.cast_pow];exact ZMod.natCast_self _
  have four:(n:ZMod (n^3))^4=0:=by rw [pow_succ (n:ZMod (n^3)) 3,cube,zero_mul]
  exact ((Nat.coprime_two_right.mpr on).pow_left 3).dvd_of_dvd_mul_left
    (doubled hk four (by rw [cube,mul_zero]))

#print axioms conjecture
#print axioms all_positive
end OMA.PascalMod19
