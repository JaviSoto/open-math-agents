import MersenneDenominator245212

/-! When the reduced Mersenne denominator is a prime power, its index is prime. -/
namespace OMA.MersenneDenominator245212
open Finset Nat

private theorem square_lt {k : ℕ} (h : 5≤k) : k*k+1<2^k := by
  induction k, h using Nat.le_induction with
  | base => decide
  | succ k h ih =>
    rw [pow_succ]
    nlinarith only [ih,h,Nat.mul_self_le_mul_self h]

private theorem smallest_avoids (t k : ℕ) (ht : 2≤t) (kt : k∣t) :
    ¬ t.minFac∣2^k-1 := by
  let p := t.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have : Fact p.Prime := ⟨hp⟩
  intro bad
  have bh : (2 : ZMod p)^k=1 := by
    have m := (Nat.modEq_iff_dvd' (show 1≤(2:ℕ)^k from Nat.one_le_pow _ _ (by decide)) (n:=p)).mpr bad
    rw [←ZMod.natCast_eq_natCast_iff] at m
    simpa using m.symm
  have nk : k≠0 := by rintro rfl; simp at kt; omega
  have nz : (2 : ZMod p)≠0 := by intro z; simp [z,zero_pow nk] at bh
  have o := orderOf_dvd_of_pow_eq_one bh
  have o2 := ZMod.orderOf_dvd_card_sub_one nz
  have cp : t.Coprime (p-1) := Nat.coprime_of_lt_minFac (by have:=hp.two_le; omega)
    (by change t.minFac-1<t.minFac; have:=hp.two_le; change 2≤t.minFac at this; omega)
  have d := Nat.dvd_gcd (o.trans kt) o2
  rw [cp.gcd_eq_one] at d
  have one : orderOf (2 : ZMod p)=1 := Nat.dvd_one.mp d
  have z := orderOf_eq_one_iff.mp one
  have two : (2:ZMod p)=1+1 := by norm_num
  rw [two] at z
  have bad1 : (1:ZMod p)=0 := by linear_combination z
  exact one_ne_zero bad1

private theorem geom_coprime (t k : ℕ) (ht : 2≤t) (kt : k∣t) :
    (2^k-1).Coprime (∑ i ∈ range t.minFac, (2^k)^i) := by
  rw [← not_not (a:=Nat.Coprime _ _),Nat.Prime.not_coprime_iff_dvd]
  rintro ⟨s,hs,h1,h2⟩
  have dp := Nat.minFac_prime (by omega : t≠1)
  have x : ((2^k:ℕ):ZMod s)=1 := by
    have h := (Nat.modEq_iff_dvd' (n:=s) (show 1≤(2:ℕ)^k from Nat.one_le_pow _ _ (by decide))).mpr h1
    rw [←ZMod.natCast_eq_natCast_iff] at h
    simpa using h.symm
  have hz := (ZMod.natCast_eq_zero_iff _ _).mpr h2
  push_cast at hz x
  simp [x] at hz
  have hd : s∣t.minFac := (ZMod.natCast_eq_zero_iff _ _).mp hz
  have same := (Nat.dvd_prime dp).mp hd
  rcases same with bad|rfl
  · exact hs.ne_one bad
  · exact smallest_avoids t k ht kt h1

theorem index_prime {t : ℕ} (ht : 2≤t) (hq : IsPrimePow (Q t)) : t.Prime := by
  by_contra composite
  let p := t.minFac
  let k := t/p
  let x := 2^k
  let v := ∑ i∈range p, x^i
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have pk : p≤k := Nat.minFac_le_div (by omega) composite
  have kt : k*p=t := Nat.div_mul_cancel (Nat.minFac_dvd t)
  by_cases small : k<5
  · have t16 : t≤16 := by nlinarith only [kt,Nat.mul_le_mul (show k≤4 by omega) (show p≤4 by omega)]
    have tab : ∀ u∈Icc 2 16, IsPrimePow (Q u) → Nat.Prime u := by decide +kernel
    exact composite (tab t (mem_Icc.mpr ⟨ht,t16⟩) hq)
  have gcap : (2^t-1).gcd t≤t := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right _ _)
  have uf : t<x-1 := by
    have sq := square_lt (by omega : 5≤k)
    have le := Nat.mul_le_mul_left k pk
    dsimp [x]; omega
  have vbig : x≤v := by
    have m : 1∈range p := mem_range.mpr hp.one_lt
    simpa [v] using (single_le_sum (f:=fun i=>x^i) (fun _ _=>Nat.zero_le _) m)
  have prod : (x-1)*v=2^t-1 := by
    rw [←kt,pow_mul]
    exact (mul_comm _ _).trans (geom_sum_mul_of_one_le (show 1≤x from Nat.one_le_pow _ _ (by decide)) p)
  have adjust : Q t*((2^t-1).gcd t)=(x-1)*v :=
    (Nat.div_mul_cancel (Nat.gcd_dvd_left (2^t-1) t)).trans prod.symm
  have cp : (x-1).Coprime v := geom_coprime t k ht ⟨p,kt.symm⟩
  rcases (cp.isPrimePow_dvd_mul hq).mp ⟨_,adjust.symm⟩ with d|d
  · have le := Nat.le_of_dvd (by omega : 0<x-1) d
    have small := Nat.mul_le_mul le gcap
    rw [adjust] at small
    exact (Nat.mul_lt_mul_of_pos_left (by omega : t<v) (by omega : 0<x-1)).not_ge small
  · have le := Nat.le_of_dvd (by omega : 0<v) d
    have small := Nat.mul_le_mul le gcap
    rw [adjust,mul_comm (x-1)] at small
    exact (Nat.mul_lt_mul_of_pos_left uf (by omega : 0<v)).not_ge small

private theorem mersenne_pow {t r e : ℕ} (ht : 2≤t) (hr : r.Prime) (he : 0<e)
    (eq : r^e=2^t-1) : e=1 := by
  have sum : r^e+1=2^t := by have := Nat.two_pow_pos t; omega
  have four : 4∣2^t := pow_dvd_pow 2 ht
  have no4 : ∀ z : ZMod 4, z^2+1≠0 := by decide +kernel
  rcases Nat.even_or_odd e with ev|od
  · obtain ⟨j,hj⟩ := ev
    have z := (ZMod.natCast_eq_zero_iff _ _).mpr (sum ▸ four : 4∣r^e+1)
    rw [hj,pow_add] at z
    push_cast at z
    exact False.elim (no4 ((r:ZMod 4)^j) (by simpa [pow_two] using z))
  have ro : Odd r := by
    rcases hr.eq_two_or_odd with h|h
    · subst r
      have dv : 2∣2^e := dvd_pow_self 2 (by omega)
      have dt : 2∣2^t := dvd_pow_self 2 (by omega)
      omega
    · exact Nat.odd_iff.mpr h
  have div : r+1∣2^t := by
    rw [←sum]
    simpa using (od.nat_add_dvd_pow_add_pow (x:=r) (y:=1))
  obtain ⟨s,st,rs⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp div
  have same : s=t := by
    by_contra! diff
    have div2 : 2*(r+1)∣2^t := by
      rw [rs,mul_comm,←pow_succ]
      exact pow_dvd_pow _ (by omega)
    have base : 1 ≡ r^2 [MOD 2*(r+1)] := by
      apply (Nat.modEq_iff_exists_eq_add (show 1≤r^2 from Nat.one_le_pow _ _ hr.pos)).mpr
      obtain ⟨h,rfl⟩ := ro
      exact ⟨h,by ring⟩
    obtain ⟨j,ej⟩ := od
    have m := ((base.pow j).mul_right r).add_right 1
    simp only [one_pow,one_mul,←pow_mul,←pow_succ,←ej,sum] at m
    have divides : 2*(r+1)∣r+1 := (m.dvd_iff (dvd_refl _)).mpr div2
    have impossible := Nat.le_of_dvd (by omega : 0<r+1) divides
    omega
  rw [same,←sum] at rs
  have poweq : r^e=r^1 := by simp; omega
  exact (Nat.pow_right_injective hr.one_lt) poweq

theorem prime_index_value {t : ℕ} (hp : t.Prime) : Q t=2^t-1 := by
  have h := smallest_avoids t t hp.two_le (dvd_refl t)
  rw [hp.minFac_eq] at h
  have c := (hp.coprime_iff_not_dvd.mpr h).symm
  simp [Q,c.gcd_eq_one]

/-- A reduced Mersenne denominator can never be a proper prime power.
When it has just one distinct prime divisor, it is a Mersenne prime. -/
theorem prime_power_classification {t : ℕ} (ht : 2≤t) (h : IsPrimePow (Q t)) :
    t.Prime ∧ Q t=2^t-1 ∧ (Q t).Prime := by
  have hp := index_prime ht h
  have val := prime_index_value hp
  obtain ⟨r,e,hr,he,eq⟩ := (isPrimePow_nat_iff _).mp h
  have one := mersenne_pow ht hr he (eq.trans val)
  exact ⟨hp,val,by simpa [←eq,one] using hr⟩

#print axioms prime_power_classification
end OMA.MersenneDenominator245212
