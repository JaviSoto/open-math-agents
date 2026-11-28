import PowerSumIndexTransfer284759
import LeastWitnessRows284759
import PowerSumRegular284760

/-! The smaller counterexample 246407261 = 157 * 1569473, from two
polynomial identities of degrees 111 and 155. -/
namespace OMA.LeastCubicWitness284759
open Nat Finset
open OMA.PowerSumIndexTransfer284759 OMA.LeastWitnessRows284759
open private OMA.PowerSumRegular284760.first_block OMA.PowerSumRegular284760.reflect3
  OMA.PowerSumRegular284760.ico_range from PowerSumRegular284760

theorem row157 : (∑i∈range 157,(i:ZMod (157^2))^246407258)=0 := by
  have hp : Nat.Prime 157 := by norm_num
  exact transfer (p:=157) (g:=2) (v:=79) (k:=110) (j:=1579533) hp (by decide)
    (by decide) ((ZMod.isUnit_iff_coprime ..).mpr (by decide))
    (separated hp (by decide) (by decide +kernel)) low157

theorem row1569473 : (∑i∈range 1569473,(i:ZMod (1569473^2))^246407258)=0 := by
  have hp : Nat.Prime 1569473 := by norm_num
  exact transfer (p:=1569473) (g:=2) (v:=784737) (k:=154) (j:=157) hp (by decide)
    (by decide) ((ZMod.isUnit_iff_coprime ..).mpr (by decide))
    (separated hp (by decide) (by decide +kernel)) low1569473

private theorem lift_row {p n e : ℕ} (pn:p∣n) (op:Odd p) (prev:Odd (e-1))
    (row:(∑i∈range p,(i:ZMod (p^2))^e)=0) : p^2∣∑i∈range n,i^e := by
  obtain ⟨m,rfl⟩:=pn
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  rw [Nat.cast_sum]
  simp only [Nat.cast_pow]
  rw [OMA.PowerSumRegular284760.first_block op prev,row,mul_zero]

/-- Convert any even auxiliary row on an odd modulus into the original
odd cubic congruence, retaining the inclusive endpoints of OEIS A284759. -/
theorem reflect_up {n e : ℕ} (on:Odd n) (oe:Odd e) (big:3≤e)
    (sq:n^2∣∑i∈range n,i^(e-1)) : n^3∣∑i∈Icc 1 (n-1),i^e := by
  have nn:0<n:=on.pos
  rw [←OMA.PowerSumRegular284760.ico_range (f:=fun i:ℕ=>i^(e-1)) nn
    (zero_pow (by omega : e-1≠0))] at sq
  have cube:n^3∣n*(∑i∈Ico 1 n,i^(e-1)) := by rw [pow_succ'];exact Nat.mul_dvd_mul_left _ sq
  have zero : (n:ZMod (n^3))*(∑i∈Ico 1 n,(i:ZMod (n^3))^(e-1))=0 := by
    simpa only [Nat.cast_mul,Nat.cast_sum,Nat.cast_pow] using (ZMod.natCast_eq_zero_iff _ _).mpr cube
  have ref:=OMA.PowerSumRegular284760.reflect3 (e:=e) on oe big
  rw [mul_right_comm,zero,zero_mul] at ref
  have two:n^3∣2*(∑i∈Ico 1 n,i^e) :=
    (ZMod.natCast_eq_zero_iff _ _).mp (by push_cast;exact ref)
  rw [show Icc 1 (n-1)=Ico 1 n by ext x;simp;omega]
  exact ((Nat.coprime_two_right.mpr on).pow_left 3).dvd_of_dvd_mul_left two

theorem witness :
    ¬ Nat.Prime 246407261 ∧
    246407261^3∣∑i∈Icc 1 (246407261-1),i^(246407261-2) := by
  constructor
  · rw [show 246407261=157*1569473 by decide]
    exact Nat.not_prime_mul (by decide) (by decide)
  · apply reflect_up (by decide) (by decide) (by decide)
    have a:=lift_row (n:=246407261) (by decide : 157∣246407261) (by decide) (by decide) row157
    have b:=lift_row (n:=246407261) (by decide : 1569473∣246407261) (by decide) (by decide) row1569473
    rw [show 246407261^2=157^2*1569473^2 by decide]
    exact (show (157^2).Coprime (1569473^2) by decide).mul_dvd_of_dvd_of_dvd a b

#print axioms witness
end OMA.LeastCubicWitness284759
