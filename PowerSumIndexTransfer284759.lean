import PowerSum284760

/-! Change the exponent of a complete power sum modulo p². Multiplication
by g permutes residues; its first-order carry determines every exponent
in one class modulo p−1 from one small-index row. -/
namespace OMA.PowerSumIndexTransfer284759
open Finset Nat
open private OMA.PowerSum284760.taylor from PowerSum284760

private theorem permute {p g v : ℕ} (pos : 0<p) (inverse : g*v ≡ 1 [MOD p])
    {R : Type*} [AddCommMonoid R] (f : ℕ → R) :
    (∑i∈range p, f ((g*i)%p))=∑i∈range p, f i := by
  have cancel {a b i : ℕ} (one : a*b ≡ 1 [MOD p]) (ip : i<p) :
      a*((b*i)%p)%p=i := by
    rw [Nat.mul_mod_mod,←Nat.mul_assoc]
    simpa only [Nat.ModEq,one_mul,Nat.mod_eq_of_lt ip] using one.mul_right i
  apply sum_bij' (fun i _ => g*i%p) (fun i _ => v*i%p)
  · intro i _;exact mem_range.mpr (mod_lt _ pos)
  · intro i _;exact mem_range.mpr (mod_lt _ pos)
  · intro i hi;exact cancel (by simpa [mul_comm] using inverse) (mem_range.mp hi)
  · intro i hi;exact cancel inverse (mem_range.mp hi)
  · intro _ _;rfl

private def cs (p g e : ℕ) : ZMod (p^2) :=
  ∑i∈range p, (((g*i)%p:ℕ):ZMod (p^2))^(e-1) * (p:ZMod (p^2)) * ((g*i)/p:ℕ)

private theorem voronoi {p g v e : ℕ} (pos : 0<p) (inverse : g*v ≡ 1 [MOD p]) :
    ((g:ZMod (p^2))^e-1)*(∑i∈range p,(i:ZMod (p^2))^e)=(e:ZMod (p^2))*cs p g e := by
  let R:=ZMod (p^2)
  have nil : (p:R)^2=0 := by
    rw [←Nat.cast_pow];exact ZMod.natCast_self _
  have line (i:ℕ) : ((g:R)*i)^e=(((g*i)%p:ℕ):R)^e +
      (e:R)*((((g*i)%p:ℕ):R)^(e-1)*(p:R)*((g*i)/p:ℕ)) := by
    have h : (g:R)*i=(((g*i)%p:ℕ):R)+(p:R)*((g*i)/p:ℕ) := by
      rw [←Nat.cast_mul g i,←Nat.cast_mul p ((g*i)/p),←Nat.cast_add,Nat.mod_add_div]
    rw [h,OMA.PowerSum284760.taylor _ _ (by rw [mul_pow,nil,zero_mul])];ring
  have all := Finset.sum_congr (s₁:=range p) rfl (fun i _=>line i)
  simp only [mul_pow,←mul_sum,sum_add_distrib] at all
  rw [permute pos inverse (fun i=>(i:R)^e)] at all
  change ((g:R)^e-1)*_=_*(∑i∈range p,_)
  linear_combination all

private theorem same_times_p {a b p : ℕ} (eqn : (a:ZMod p)=b) :
    (a:ZMod (p^2))*p=(b:ZMod (p^2))*p := by
  rw [←Nat.cast_mul,←Nat.cast_mul,ZMod.natCast_eq_natCast_iff,pow_two]
  exact ((ZMod.natCast_eq_natCast_iff ..).mp eqn).mul_right' p

theorem transfer {p g v k j : ℕ} (hp:p.Prime) (inverse : g*v ≡ 1 [MOD p])
    (hk:1<k) (kunit:IsUnit (k:ZMod (p^2)))
    (separator:IsUnit ((g:ZMod (p^2))^(k+(p-1)*j)-1))
    (small:(∑ i∈range p,(i:ZMod (p^2))^k)=0) :
    (∑ i∈range p,(i:ZMod (p^2))^(k+(p-1)*j))=0 := by
  let : Fact p.Prime := ⟨hp⟩
  have equal : cs p g (k+(p-1)*j)=cs p g k := by
    unfold cs
    apply sum_congr rfl;intro i _
    apply congrArg (·*(((g*i)/p:ℕ):ZMod (p^2)))
    let x:ℕ := (g*i)%p
    change (x:ZMod (p^2))^_*p=(x:ZMod (p^2))^_*p
    rw [←Nat.cast_pow,←Nat.cast_pow]
    apply same_times_p
    simp only [Nat.cast_pow]
    rw [show k+(p-1)*j-1=k-1+(p-1)*j by omega,pow_add,pow_mul]
    by_cases z : (x:ZMod p)=0
    · simp [z,zero_pow (show k-1≠0 by omega)]
    · simp [ZMod.pow_card_sub_one_eq_one z]
  have first := voronoi (e:=k) hp.pos inverse
  have cz : cs p g k=0 := kunit.mul_right_inj.mp (by simpa [small] using first.symm)
  have second := voronoi (e:=k+(p-1)*j) hp.pos inverse
  exact separator.mul_right_inj.mp (by simpa [equal,cz] using second)

#print axioms transfer

theorem separated {p g k j : ℕ} (hp:p.Prime) (base:(g:ZMod p)≠0)
    (small:(g:ZMod p)^k≠1) : IsUnit ((g:ZMod (p^2))^(k+(p-1)*j)-1) := by
  let : Fact p.Prime := ⟨hp⟩
  let m:=p^2
  let y:ZMod m := (g:ZMod m)^(k+(p-1)*j)-1
  let down:=ZMod.castHom (show p∣p^2 by simp) (ZMod p)
  have nonzero : down y≠0 := by
    dsimp only [y,down,m]
    rw [map_sub,map_pow,map_natCast,map_one,pow_add,pow_mul,ZMod.pow_card_sub_one_eq_one base,one_pow,mul_one]
    exact sub_ne_zero.mpr small
  have non : ¬p∣y.val := by
    intro bad
    apply nonzero
    rw [←ZMod.natCast_zmod_val y,map_natCast,ZMod.natCast_eq_zero_iff]
    exact bad
  change IsUnit y
  rw [←ZMod.natCast_zmod_val y]
  exact (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by decide : 0<2)).mpr non

end OMA.PowerSumIndexTransfer284759
