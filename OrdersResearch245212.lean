import FormalConjectures.OEIS.«245212»
import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.SumTwoSquares

/-! Exact valuations of all three divisor terms and a necessary prime-factor test for A245212. -/

namespace OMA.Smooth245212
open Finset ArithmeticFunction Nat
open scoped ArithmeticFunction.sigma Function

def W : ArithmeticFunction ℕ := (ArithmeticFunction.id.pmul (σ 0)) * ArithmeticFunction.zeta
lemma w_mult : W.IsMultiplicative :=
  (isMultiplicative_id.pmul isMultiplicative_sigma).mul isMultiplicative_zeta
lemma w_apply (n : ℕ) : W n = ∑ d∈n.divisors, d*d.divisors.card := by
  rw [W,mul_zeta_apply]
  simp only [pmul_apply,id_apply,sigma_zero_apply]
lemma w_pow {p : ℕ} (hp : Nat.Prime p) (e : ℕ) :
    W (p^e) = ∑ j ∈ range (e+1), p^j*(j+1) := by
  rw [w_apply,Nat.sum_divisors_prime_pow hp]
  simp [Nat.divisors_prime_pow hp]

variable {ι : Type*} [Fintype ι] (p : ι → ℕ)
def total (e : ι → ℕ) : ℕ := ∏ i, p i^(e i)
end OMA.Smooth245212

namespace OMA.Abundance245212
open OMA.Smooth245212 Finset ArithmeticFunction Nat
open scoped ArithmeticFunction.sigma
theorem balance {n : ℕ} (hn : n≠0)
    (eq : OeisA245212.a n=(σ 1 n:ℤ)) : W n+σ 1 n=2*n*(σ 0 n) := by
  have total : W n = n*n.divisors.card+∑ d∈n.properDivisors,d*d.divisors.card := by
    calc
      _ = ∑ d∈insert n n.properDivisors,d*d.divisors.card := by
        rw [Nat.insert_self_properDivisors hn,w_apply]
      _ = _ := sum_insert Nat.self_notMem_properDivisors
  unfold OeisA245212.a at eq
  zify at total ⊢
  simp only [sigma_zero_apply]
  linarith
end OMA.Abundance245212

namespace OMA.DyadicBlocks245212
open Finset Nat

def geom (p n : ℕ) := ∑ i∈range n,p^i
def weight (p n : ℕ) := ∑ i∈range n,p^i*(i+1)

private theorem split_g (p m n : ℕ) : geom p (m+n)=geom p m+p^m*geom p n := by
  simp only [geom,sum_range_add,mul_sum,pow_add]

private theorem split_w (p m n : ℕ) :
    weight p (m+n)=weight p m+p^m*(weight p n+m*geom p n) := by
  simp only [weight,geom,sum_range_add]
  congr 1
  simp only [mul_sum,←sum_add_distrib,pow_add]
  apply sum_congr rfl
  intro i _
  ring

private theorem pow_block (p h : ℕ) (ho : Odd p) :
    p^(2^h) ≡ 1 [MOD 2^(h+1)] := by
  have cop := (Nat.coprime_two_right.mpr ho).pow_right (h+1)
  simpa only [Nat.totient_prime_pow_succ Nat.prime_two,Nat.reduceSub,mul_one] using
    Nat.ModEq.pow_totient cop

theorem div_geom (p : ℕ) (ho : Odd p) (h : ℕ) : 2^h ∣ geom p (2^h) := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [pow_succ, Nat.mul_two,split_g,←one_add_mul]
    have even := (ho.pow (n:=2^h)).add_one
    simpa [Nat.two_mul,add_comm] using Nat.mul_dvd_mul (even_iff_two_dvd.mp even) ih

theorem weight_block (p : ℕ) (ho : Odd p) (h : ℕ) :
    weight p (2^(h+1)) ≡ 2^h [MOD 2^(h+1)] := by
  induction h with
  | zero => simp [weight,sum_range_succ,Nat.ModEq]
  | succ h ih =>
    let N := 2^(h+1)
    have even : 2∣geom p N := (dvd_pow_self 2 (by omega : h+1≠0)).trans (div_geom p ho _)
    have off : N*geom p N ≡ 0 [MOD 2*N] := by
      apply Nat.modEq_zero_iff_dvd.mpr
      simpa [mul_comm] using Nat.mul_dvd_mul_left N even
    have pp : p^N ≡ 1 [MOD 2*N] := by
      simpa only [N,pow_succ (2:ℕ) (h+1),mul_comm] using pow_block p (h+1) ho
    have twice : 2*weight p N ≡ N [MOD 2*N] := by
      simpa only [N,pow_succ' (2:ℕ) h] using ih.mul_left' 2
    have bridge := (Nat.ModEq.rfl (a:=weight p N)).add
      (pp.mul ((Nat.ModEq.rfl (a:=weight p N)).add off))
    change weight p (2^(h+1+1)) ≡ 2^(h+1) [MOD 2^(h+1+1)]
    rw [pow_succ' (2:ℕ) (h+1)]
    change weight p (2*N) ≡ N [MOD 2*N]
    rw [show 2*N=N+N by omega,split_w]
    simpa [Nat.two_mul] using bridge.trans (by simpa [Nat.two_mul] using twice)
end OMA.DyadicBlocks245212

namespace OMA.DyadicPower245212
open Finset Nat ArithmeticFunction OMA.Smooth245212 OMA.Abundance245212 OMA.DyadicBlocks245212
open scoped ArithmeticFunction.sigma ArithmeticFunction.Omega
theorem dyadic_odd (k : ℕ) : Odd (W (2^k)) := by
  rw [w_pow Nat.prime_two,Nat.odd_iff,sum_range_succ']
  have h : 2∣∑ i∈range k, 2^(i+1)*(i+1+1) :=
    Finset.dvd_sum (fun i _ => dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) _)
  simp only [pow_zero,zero_add,one_mul]
  omega
end OMA.DyadicPower245212

namespace OMA.WeightVal245212
open Finset OMA.Smooth245212 OMA.DyadicBlocks245212
open scoped ArithmeticFunction.sigma

abbrev val (n : ℕ) := n.factorization 2
theorem val_odd {n : ℕ} (h : Odd n) : val n=0 :=
  Nat.factorization_eq_zero_of_not_dvd (by have := Nat.odd_iff.mp h; omega)

theorem identify {n h : ℕ} (nz : 0<n) (mod : n ≡ 2^h [MOD 2^(h+1)]) : val n=h := by
  have pp : 0<2^h := Nat.two_pow_pos _
  have bound : 2^h<2^(h+1) := by rw [pow_succ]; omega
  have low : 2^h∣n := Nat.modEq_zero_iff_dvd.mp
    ((mod.of_dvd (pow_dvd_pow _ (by omega))).trans (Nat.modEq_zero_iff_dvd.mpr (dvd_refl _)))
  have high : ¬2^(h+1)∣n := by
    intro d
    have bad := Nat.modEq_zero_iff_dvd.mp (mod.symm.trans (Nat.modEq_zero_iff_dvd.mpr d))
    exact bound.not_ge (Nat.le_of_dvd pp bad)
  have l := (Nat.prime_two.pow_dvd_iff_le_factorization nz.ne').mp low
  have hi := mt (Nat.prime_two.pow_dvd_iff_le_factorization nz.ne').mpr high
  change n.factorization 2=h
  omega

theorem blocks (p : ℕ) (op : Odd p) (h u : ℕ) :
    let N := 2^(h+1)
    geom p (u*N) ≡ 0 [MOD N] ∧ weight p (u*N) ≡ u*2^h [MOD N] := by
  let N := 2^(h+1)
  have p1 : p^N ≡ 1 [MOD N] := (OMA.DyadicBlocks245212.pow_block p (h+1) op).of_dvd
    (pow_dvd_pow _ (by omega : h+1≤h+1+1))
  have gp := Nat.modEq_zero_iff_dvd.mpr (div_geom p op (h+1))
  have wp := weight_block p op h
  have powr (b : ℕ) : p^(b*N) ≡ 1 [MOD N] := by
    rw [Nat.mul_comm b N,pow_mul]; simpa only [one_pow] using p1.pow b
  dsimp only
  change geom p (u*N) ≡ 0 [MOD N] ∧ weight p (u*N) ≡ u*2^h [MOD N]
  induction u with
  | zero => simp [geom,weight,Nat.ModEq]
  | succ u ih =>
    have dz : u*N ≡ 0 [MOD N] := Nat.modEq_zero_iff_dvd.mpr (dvd_mul_left _ _)
    rw [Nat.succ_mul,OMA.DyadicBlocks245212.split_g,OMA.DyadicBlocks245212.split_w]
    exact ⟨by simpa only [mul_zero,zero_add] using ih.1.add ((powr u).mul gp),
      by simpa only [zero_mul,add_zero,one_mul,Nat.succ_mul] using
        ih.2.add ((powr u).mul (wp.add (dz.mul gp)))⟩

private theorem even_weight {p t : ℕ} (odd : Odd p) (tp : 0<t) (even : Even t) :
    ∃ h, val t=h+1 ∧ weight p t ≡ 2^h [MOD 2^(h+1)] ∧ 2^(h+1)∣geom p t := by
  obtain ⟨k,u,ou,eq⟩ := Nat.exists_eq_two_pow_mul_odd tp.ne'
  cases k with
  | zero => simp only [pow_zero,one_mul] at eq; exact (Nat.not_even_iff_odd.mpr ou (eq ▸ even)).elim
  | succ h =>
    have prod : t=u*2^(h+1) := eq.trans (mul_comm _ _)
    have vv : val t=h+1 := by
      have vu := val_odd ou
      unfold val at vu ⊢
      rw [prod,Nat.factorization_mul ou.pos.ne' (by positivity),Finsupp.add_apply,
        Nat.factorization_pow_self Nat.prime_two,vu,zero_add]
    have b := blocks p odd h u
    dsimp only at b
    have o : u ≡ 1 [MOD 2] := by simpa [Nat.ModEq] using Nat.odd_iff.mp ou
    have reduced : u*2^h ≡ 2^h [MOD 2^(h+1)] := by
      simpa [pow_succ,mul_comm] using o.mul_right' (2^h)
    exact ⟨h,vv,prod ▸ b.2.trans reduced,prod ▸ Nat.modEq_zero_iff_dvd.mp b.1⟩

private theorem weight_pos {p t : ℕ} (ht : 0<t) : 0<weight p t :=
  sum_pos' (fun _ _=>Nat.zero_le _) ⟨0,mem_range.mpr ht,by simp⟩

/-- The valuation depends only on the exponent, even when the odd prime varies. -/
theorem weight_local {p : ℕ} (hp : p.Prime) (odd : Odd p) (e : ℕ) :
    val (W (p^e))+1=val (e+1)+val (e+2) := by
  rw [w_pow hp]
  change val (weight p (e+1))+1=_
  rcases Nat.even_or_odd (e+1) with ev|od
  · obtain ⟨h,vv,ww,_⟩ := even_weight odd (by omega) ev
    have vo := val_odd (show Odd (e+2) from ev.add_one)
    rw [identify (weight_pos (by omega)) ww,vv,vo,Nat.add_zero]
  · have ev : Even (e+2) := od.add_one
    obtain ⟨h,vv,ww,_⟩ := even_weight odd (by omega) ev
    have d : 2^(h+1)∣e+2 := (Nat.prime_two.pow_dvd_iff_le_factorization (by omega : e+2≠0)).mpr vv.ge
    have off : p^(e+1)*(e+2) ≡ 0 [MOD 2^(h+1)] :=
      Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_right d _)
    have next : weight p (e+2) ≡ weight p (e+1) [MOD 2^(h+1)] := by
      dsimp only [weight]
      rw [sum_range_succ _ (e+1)]
      simpa only [weight,add_zero] using (Nat.ModEq.refl (weight p (e+1))).add off
    rw [identify (weight_pos (by omega)) (next.symm.trans ww),val_odd od,vv,zero_add]
end OMA.WeightVal245212

namespace OMA.ExactSigma245212
open Finset ArithmeticFunction OMA.WeightVal245212
open scoped ArithmeticFunction.sigma

abbrev v₂ (n : ℕ) := n.factorization 2
lemma mul_val {x y : ℕ} (hx : x≠0) (hy : y≠0) : v₂ (x*y)=v₂ x+v₂ y := by
  simp only [v₂,Nat.factorization_mul hx hy,Finsupp.add_apply]

def surplus (p e : ℕ) : ℕ := if Odd e then v₂ (p+1)-1 else 0

theorem local_sigma {p : ℕ} (hp : p.Prime) (op : Odd p) (e : ℕ) :
    v₂ (σ 1 (p^e))=v₂ (e+1)+surplus p e := by
  have sp := sigma_pos 1 _ (pow_ne_zero e hp.ne_zero)
  rcases Nat.even_or_odd e with ev|od
  · have mod : σ 1 (p^e) ≡ e+1 [MOD 2] := by
      rw [sigma_one_apply_prime_pow hp]
      have b : p ≡ 1 [MOD 2] := Nat.odd_iff.mp op
      have h := Nat.ModEq.sum (s:=range (e+1)) (fun j _ =>
        show p^j ≡ 1 [MOD 2] by simpa using b.pow j)
      simpa using h
    have od1 : Odd (e+1) := ev.add_one
    have os : Odd (σ 1 (p^e)) := Nat.odd_iff.mpr (mod.trans (show e+1 ≡ 1 [MOD 2] from Nat.odd_iff.mp od1))
    have nev : ¬ Odd e := fun h => (Nat.not_even_iff_odd.mpr h) ev
    rw [surplus,if_neg nev,
      show v₂ (e+1)=0 from val_odd od1,show v₂ (σ 1 (p^e))=0 from val_odd os]
  · have nd : ¬2∣p := by have := Nat.odd_iff.mp op; omega
    have lte := padicValNat.pow_two_sub_one hp.one_lt nd (by omega : e+1≠0) od.add_one
    simp only [←Nat.factorization_def _ Nat.prime_two] at lte
    have fg : σ 1 (p^e)*(p-1)=p^(e+1)-1 := by
      rw [sigma_one_apply_prime_pow hp]; exact geom_sum_mul_of_one_le hp.one_lt.le _
    change v₂ (p^(e+1)-1)+1 = v₂ (p+1)+v₂ (p-1)+v₂ (e+1) at lte
    rw [←fg,mul_val sp.ne' (by have := hp.one_lt; omega)] at lte
    have pos : 1 ≤ v₂ (p+1) := (Nat.prime_two.pow_dvd_iff_le_factorization
      (by omega : p+1≠0)).mp (by simpa using even_iff_two_dvd.mp op.add_one)
    rw [surplus,if_pos od]
    omega

theorem sigma_two_odd (a : ℕ) : Odd (σ 1 (2^a)) := by
  rw [sigma_one_apply_prime_pow Nat.prime_two,sum_range_succ',Nat.odd_iff]
  have h : 2 ∣ ∑ i∈range a, 2^(i+1) :=
    dvd_sum (fun i _ => dvd_pow_self 2 (by omega))
  simp only [pow_zero]
  omega

/-- Positive x is 2^v times an odd number. -/
theorem exact_units (x : ℕ) (hx : x≠0) : ∃ u, Odd u ∧ x=2^v₂ x*u := by
  obtain ⟨k,u,ou,eq⟩ := Nat.exists_eq_two_pow_mul_odd hx
  refine ⟨u,ou,?_⟩
  have v : v₂ x=k := by
    calc
      _ = v₂ (2^k*u) := congrArg v₂ eq
      _ = k := by rw [mul_val (by positivity) ou.pos.ne',
                    show v₂ (2^k)=k from Nat.factorization_pow_self Nat.prime_two,
                    show v₂ u=0 from val_odd ou,add_zero]
  simpa only [v] using eq

theorem exact_residue {x : ℕ} (hx : x≠0) : x ≡ 2^v₂ x [MOD 2^(v₂ x+1)] := by
  obtain ⟨u,ou,eu⟩ := exact_units x hx
  have o : u ≡ 1 [MOD 2] := Nat.odd_iff.mp ou
  have h := o.mul_left' (2^v₂ x)
  simpa only [←eu,mul_one,←pow_succ] using h

theorem sum_of_lt {x y : ℕ} (hx : x≠0) (hy : y≠0) (h : v₂ x < v₂ y) :
    v₂ (x+y)=v₂ x := by
  have zd : 2^(v₂ x+1)∣y := (Nat.prime_two.pow_dvd_iff_le_factorization hy).mpr h
  apply identify (by omega)
  simpa only [add_zero] using (exact_residue hx).add (Nat.modEq_zero_iff_dvd.mpr zd)

theorem sum_of_equal {x y : ℕ} (hx : x≠0) (hy : y≠0) (h : v₂ x=v₂ y) :
    v₂ x < v₂ (x+y) := by
  have ry := exact_residue hy
  rw [←h] at ry
  have sum := (exact_residue hx).add ry
  rw [←Nat.mul_two,←pow_succ] at sum
  exact (Nat.prime_two.pow_dvd_iff_le_factorization (by omega : x+y≠0)).mp
    (Nat.modEq_zero_iff_dvd.mp (sum.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_refl _))))

end OMA.ExactSigma245212

namespace OMA.BalanceOrders245212
open Finset Nat ArithmeticFunction OMA.Smooth245212 OMA.Abundance245212 OMA.ExactSigma245212
open scoped ArithmeticFunction.sigma Function

theorem orders {ι : Type*} [Fintype ι] (p e : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (op : ∀ i, Odd (p i)) (inj : Function.Injective p) (a : ℕ) :
    let n := 2^a*total p e
    let T := ∑ i, v₂ (e i+1)
    let E := ∑ i, v₂ (e i+2)
    let U := ∑ i, surplus (p i) (e i)
    v₂ (W n)+Fintype.card ι=T+E ∧ v₂ (σ 1 n)=T+U ∧
      v₂ (2*n*(σ 0 n))=T+(1+a+v₂ (a+1)) := by
  classical
  dsimp only
  let z (i : ι) := p i^e i
  have cop : (↑(univ : Finset ι) : Set ι).Pairwise (Coprime on z) := by
    intro i _ j _ ne
    exact (((Nat.coprime_primes (hp i) (hp j)).mpr (fun h => ne (inj h))).pow_left _).pow_right _
  have oc : (2:ℕ).Coprime (total p e) := Coprime.prod_right (fun i _ =>
    (Nat.coprime_two_left.mpr (op i)).pow_right (e i))
  have co := oc.pow_left a
  have zn : total p e ≠ 0 := prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hp i).ne_zero)
  have wpos (i : ι) : W (z i) ≠ 0 := by
    rw [show z i=p i^e i from rfl,w_pow (hp i)]
    exact (sum_pos' (fun _ _ => Nat.zero_le _) ⟨0,mem_range.mpr (by omega),by simp⟩).ne'
  have wm : W (total p e) = ∏ i, W (z i) := IsMultiplicative.map_prod z w_mult univ cop
  have tm : σ 0 (total p e) = ∏ i, (e i+1) := by
    simpa only [z,total,sigma_zero_apply_prime_pow (hp _)] using
      IsMultiplicative.map_prod z (isMultiplicative_sigma (k:=0)) univ cop
  have sm : σ 1 (total p e) = ∏ i, σ 1 (z i) :=
    IsMultiplicative.map_prod z (isMultiplicative_sigma (k:=1)) univ cop
  have vp (f : ι → ℕ) (hf : ∀ i, f i≠0) :
      v₂ (∏ i, f i) = ∑ i, v₂ (f i) := Nat.factorization_prod_apply fun i _ => hf i
  have wa := OMA.DyadicPower245212.dyadic_odd a
  have sa := sigma_two_odd a
  constructor
  · rw [w_mult.map_mul_of_coprime co,wm,mul_val wa.pos.ne' (prod_ne_zero_iff.mpr (fun i _ => wpos i)),
      show v₂ (W (2^a))=0 from OMA.WeightVal245212.val_odd wa,zero_add,vp _ wpos]
    have h := sum_congr (s₁:=univ) rfl (fun i _ => OMA.WeightVal245212.weight_local (hp i) (op i) (e i))
    simp only [sum_add_distrib,sum_const,smul_eq_mul,mul_one] at h
    exact h
  constructor
  · rw [isMultiplicative_sigma.map_mul_of_coprime co,mul_val sa.pos.ne' (sigma_pos _ _ zn).ne',
      show v₂ (σ 1 (2^a))=0 from OMA.WeightVal245212.val_odd sa,zero_add,sm,
      vp _ (fun i => (sigma_pos 1 _ (pow_ne_zero _ (hp i).ne_zero)).ne'),←sum_add_distrib]
    exact sum_congr rfl (fun i _ => local_sigma (hp i) (op i) (e i))
  · have z2 : 2^a≠0 := by positivity
    have nz := mul_ne_zero z2 zn
    rw [mul_val (mul_ne_zero (by decide) nz) (sigma_pos 0 _ nz).ne',
      mul_val (by decide) nz,mul_val z2 zn,isMultiplicative_sigma.map_mul_of_coprime co,
      sigma_zero_apply_prime_pow Nat.prime_two,tm,mul_val (by omega) (prod_ne_zero_iff.mpr (fun _ _ => by omega)),
      vp _ (fun _ => by omega),show v₂ (total p e)=0 from OMA.WeightVal245212.val_odd
        (Nat.coprime_two_left.mp oc),show v₂ (2^a)=a from Nat.factorization_pow_self Nat.prime_two]
    have : v₂ 2=1 := by decide +kernel
    omega

/-- Compare the ordinary-divisor surplus U and the dyadic threshold H.
The weighted surplus equals their minimum unless they coincide, when it is larger. -/
theorem trichotomy {ι : Type*} [Fintype ι] (p e : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (op : ∀ i, Odd (p i)) (inj : Function.Injective p)
    (a : ℕ) (eq : OeisA245212.a (2^a*total p e) = (σ 1 (2^a*total p e) : ℤ)) :
    let E := ∑ i, v₂ (e i+2)
    let U := ∑ i, surplus (p i) (e i)
    let H := 1+a+v₂ (a+1)
    (U<H → E=Fintype.card ι+U) ∧ (H<U → E=Fintype.card ι+H) ∧
      (U=H → Fintype.card ι+H<E) := by
  let n := 2^a*total p e
  have nz : n≠0 := mul_ne_zero (by positivity) (prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hp i).ne_zero))
  have h := balance nz eq
  have ws : W n≠0 := by
    rw [w_apply]
    exact (sum_pos' (fun _ _ => Nat.zero_le _) ⟨1,one_mem_divisors.mpr nz,by simp⟩).ne'
  have ss := (sigma_pos 1 n nz).ne'
  have x := orders p e hp op inj a
  change v₂ (W n)+Fintype.card ι=_ ∧ v₂ (σ 1 n)=_ ∧ v₂ (2*n*(σ 0 n))=_ at x
  rw [←h] at x
  obtain ⟨w,s,b⟩ := x
  dsimp only
  rcases lt_trichotomy (v₂ (W n)) (v₂ (σ 1 n)) with lo|same|hi
  · have ord := sum_of_lt ws ss lo
    omega
  · have ord := sum_of_equal ws ss same
    omega
  · have ord := sum_of_lt ss ws hi
    rw [add_comm] at ord
    omega

end OMA.BalanceOrders245212

namespace OMA.ActualOrders245212
open Nat Finset ArithmeticFunction OMA.Smooth245212 OMA.ExactSigma245212 OMA.BalanceOrders245212
open scoped ArithmeticFunction.sigma

def compatible (k m : ℕ) : Prop :=
  let E := ∑ p : m.primeFactors, (m.factorization p+2).factorization 2
  let U := ∑ p : m.primeFactors, if Odd (m.factorization p) then ((p:ℕ)+1).factorization 2-1 else 0
  let H := 1+k+(k+1).factorization 2
  if U < H then E=m.primeFactors.card+U
  else if H < U then E=m.primeFactors.card+H else m.primeFactors.card+H<E

theorem necessary (k m : ℕ) (odd : Odd m)
    (eq : OeisA245212.a (2^k*m) = (σ 1 (2^k*m) : ℤ)) : compatible k m := by
  let p : m.primeFactors → ℕ := Subtype.val
  let e (i : m.primeFactors) := m.factorization i
  have hp (i : m.primeFactors) : (p i).Prime := prime_of_mem_primeFactors i.property
  have op (i : m.primeFactors) : Odd (p i) := by
    apply Nat.odd_iff.mpr
    have d := dvd_of_mem_primeFactors i.property
    change p i ∣ m at d
    have no : ¬2∣p i := fun h => odd.not_two_dvd_nat (h.trans d)
    omega
  have hn : total p e=m := (Nat.prod_primeFactors_coe_pow_factorization odd.pos.ne').symm
  rw [←hn] at eq
  obtain ⟨l,r,s⟩ := trichotomy p e hp op Subtype.val_injective k eq
  unfold compatible
  dsimp only
  simp only [Fintype.card_coe] at l r s
  split_ifs with h j
  · exact l h
  · exact r j
  · apply s
    exact le_antisymm (le_of_not_gt j) (le_of_not_gt h)

end OMA.ActualOrders245212

namespace OMA.TwoSquares245212
open Finset Nat ArithmeticFunction OMA.ExactSigma245212 OMA.ActualOrders245212
open scoped ArithmeticFunction.sigma

theorem surplus_zero {p e : ℕ} : surplus p e=0 ↔ (p%4=3 → Even e) := by
  by_cases ev : Even e
  · have h : ¬Odd e := fun o => Nat.not_even_iff_odd.mpr o ev
    simp [surplus,h,ev]
  have od := Nat.not_even_iff_odd.mp ev
  have v : 2 ≤ v₂ (p+1) ↔ p%4=3 := by
    rw [←Nat.prime_two.pow_dvd_iff_le_factorization (by omega : p+1≠0)]
    norm_num
    omega
  simp only [surplus,if_pos od,ev,imp_false]
  constructor
  · intro small h
    have := v.mpr h
    omega
  · intro h
    have := mt v.mp h
    omega

theorem no_surplus_iff_two_squares (m : ℕ) :
    (∑ p : m.primeFactors, surplus p (m.factorization p))=0 ↔
    ∃ a b : ℕ, m=a^2+b^2 := by
  rw [Nat.eq_sq_add_sq_iff,Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)]
  constructor
  · intro h p hp h3
    rw [←Nat.factorization_def m (Nat.prime_of_mem_primeFactors hp)]
    exact surplus_zero.mp (h ⟨p,hp⟩ (mem_univ _)) h3
  · intro h p _
    apply surplus_zero.mpr
    intro h3
    rw [Nat.factorization_def m (Nat.prime_of_mem_primeFactors p.property)]
    exact h p p.property h3

/-- Among solutions, the odd part is a sum of two squares exactly when the
old lower bound on the total exponent order is attained. -/
theorem saturation_iff (k m : ℕ) (odd : Odd m)
    (eq : OeisA245212.a (2^k*m) = (σ 1 (2^k*m) : ℤ)) :
    (∑ p : m.primeFactors, (m.factorization p+2).factorization 2)=m.primeFactors.card
      ↔ ∃ a b : ℕ, m=a^2+b^2 := by
  rw [←no_surplus_iff_two_squares]
  have cert := necessary k m odd eq
  let E := ∑ p : m.primeFactors, (m.factorization p+2).factorization 2
  let U := ∑ p : m.primeFactors, surplus p (m.factorization p)
  let H := 1+k+(k+1).factorization 2
  have hp : 0 < H := by dsimp only [H]; omega
  change E=m.primeFactors.card ↔ U=0
  change (if U<H then E=m.primeFactors.card+U else
    if H<U then E=m.primeFactors.card+H else m.primeFactors.card+H<E) at cert
  split_ifs at cert <;> omega

end OMA.TwoSquares245212

#print axioms OMA.TwoSquares245212.saturation_iff
#print axioms OMA.BalanceOrders245212.orders
#print axioms OMA.ActualOrders245212.necessary
