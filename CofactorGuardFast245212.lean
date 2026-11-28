import RankThreeMiddleBlocks245212

/-! Exact replacement for huge reverse-digit powers. A prime-power
congruence rejects an impossible exponent before evaluating the power. -/
namespace OMA.CofactorGuardFast245212
open Nat ArithmeticFunction OMA.Smooth245212 OMA.CofactorEulerPair245212 OMA.PairExtension245212
open private OMA.Large245212.moments from LargeExact245212
open scoped ArithmeticFunction.sigma

def magnitude (A S q : ℕ) := ((A:ℤ)-((q:ℤ)-1)*(S:ℤ)).natAbs

private theorem divides {A S T p f : ℕ} (hp : p.Prime) (ok : permitted A S T p f=true) :
    p^f ∣ magnitude A S p := by
  obtain ⟨sval,wval⟩:=OMA.Large245212.moments hp f
  simp only [permitted,Bool.and_eq_true,decide_eq_true_eq] at ok
  have balance:=ok.2
  rw [sval,wval] at balance
  have van : (p:ZMod (p^f))^f=0 := by rw [←Nat.cast_pow];exact ZMod.natCast_self _
  have w:=congrArg (fun n:ℕ=>(n:ZMod (p^f))) (OMA.PrimePowerDiv245212.weighted hp f)
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_sub hp.pos,Nat.cast_one,Nat.cast_pow,van,mul_zero] at w
  have s : ((p:ZMod (p^f))-1)*(σ 1 (p^f):ℕ) = -1 := by
    rw [sigma_one_apply_prime_pow hp]
    simp only [Nat.cast_sum,Nat.cast_pow]
    rw [mul_comm,geom_sum_mul,pow_succ,van,zero_mul,zero_sub]
  have bb:=congrArg (fun n:ℕ=>(n:ZMod (p^f))) balance
  simp only [OMA.Large245212.tax,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_one,van,mul_zero] at bb
  have iv : ((p^f:ℕ):ℤ) ∣ (A:ℤ)-((p:ℤ)-1)*(S:ℤ) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p^f)).mp
    push_cast
    linear_combination ((p:ZMod (p^f))-1)^2*bb - (A:ZMod (p^f))*((p:ZMod (p^f))-1)*w +
      ((A:ZMod (p^f))-((p:ZMod (p^f))-1)*(S:ZMod (p^f)))*s
  simpa [magnitude] using Int.natAbs_dvd_natAbs.mpr iv

def fastKnown (A S T q : ℕ) : Bool :=
  let C:=OMA.ReverseDigit245212.numerator q A S
  let D:=OMA.ReverseDigit245212.denominator q A T
  if ¬q∣A+S ∨ D=0 then true else
    let f:=(⌊C/D⌋-1).toNat
    let N:=magnitude A S q
    decide (0<N ∧ N.log2<f) || !permitted A S T q f

theorem fastKnown_eq {A S T q : ℕ} (hq : q.Prime) : fastKnown A S T q=known A S T q := by
  simp only [fastKnown,known]
  split
  · rfl
  · let f:=(⌊OMA.ReverseDigit245212.numerator q A S / OMA.ReverseDigit245212.denominator q A T⌋-1).toNat
    let N:=magnitude A S q
    change (decide (0<N ∧ N.log2<f) || !permitted A S T q f)=(!permitted A S T q f)
    by_cases yes : permitted A S T q f=true
    · have impossible : ¬(0<N ∧ N.log2<f) := by
        rintro ⟨pos,small⟩
        have bound := Nat.le_of_dvd pos (divides hq yes)
        have two := (Nat.pow_le_pow_left hq.two_le f).trans bound
        have low := (Nat.le_log_iff_pow_le (by decide : 1<2) pos.ne').mpr two
        rw [Nat.log2_eq_log_two] at small
        omega
      simp [impossible]
    · simp [Bool.eq_false_iff.mpr yes]

def fastRow (A S T p q e : ℕ) := fastKnown (A*OMA.Large245212.wt p e)
  (S*OMA.Large245212.sig p e) (T*OMA.Large245212.tax p e) q

def fastTable (A S T p q E : ℕ) := (List.range E).all fun i=>fastRow A S T p q (i+1)

private theorem tables {A S T p q E : ℕ} (hq : q.Prime) : fastTable A S T p q E=table A S T p q E := by
  simp only [fastTable,table,fastRow,row,fastKnown_eq hq]

def fastPair (h A S T p q : ℕ) : Bool :=
  let floor:=2*T*(p-1)*(q-1)
  let top:=A*p*q
  if ¬q.Prime ∨ ¬h.Coprime q ∨ top<floor then true else
  if top=floor then false else
  let E:=2*A*(p+q)/(top-floor)
  let endAt:=min E (OMA.CofactorPairRounding245212.threshold h A S p q E)
  fastTable A S T p q endAt && fastTable A S T q p endAt

theorem pairs {h A S T p : ℕ} (hp : p.Prime) : fastPair h A S T p=finitePair h A S T p := by
  funext q
  by_cases hq : q.Prime
  · simp only [fastPair,finitePair,tables hp,tables hq]
  · simp [fastPair,finitePair,hq]

theorem restore {l r h A S T p : ℕ} (hp : p.Prime)
    (yes : every l r (fastPair h A S T p)=true) : every l r (finitePair h A S T p)=true := by
  simpa only [pairs hp] using yes

#print axioms pairs
end OMA.CofactorGuardFast245212
