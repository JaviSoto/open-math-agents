import OddThreeResearch245212

/-! Necessary exponent bounds on the unique five-prime support with a single factor of three. -/
namespace OMA.FiveExponentBounds245212
open Finset OMA.Smooth245212 OMA.OddFaces245212
open scoped ArithmeticFunction.sigma

def primes : Fin 4→ℕ := ![5,7,11,13]
def floors : Fin 4→ℕ := ![18,12,7,6]

theorem limits (e : Fin 4→ℕ)
    (bal : (7/6:ℚ)*(∏ i,X (primes i) (some (e i)))+
      (2/3:ℚ)*(∏ i,Y (primes i) (some (e i)))=2) (i : Fin 4) : floors i≤e i := by
  let s := (univ : Finset (Fin 4)).erase i
  let p := primes i
  let x := X p (some (e i))
  let y := Y p (some (e i))
  let T := ∏ j∈s,Y (primes j) (some (e j))
  let B := ∏ j∈s,X (primes j) (some (e j))
  let C := ∏ j∈s,limitX (primes j)
  have hp : ∀ j, 1<primes j := by decide
  have hx := x_nonneg (hp i) (some (e i))
  have hT : 0≤T := prod_nonneg (fun j _ => y_nonneg (hp j) _)
  have ht : T≤1 := prod_le_one (fun j _ => y_nonneg (hp j) _) (fun j _ => y_one (hp j) _)
  have hc : 0≤C := prod_nonneg (fun j _ => x_nonneg (hp j) none)
  have bound : B≤T+(1-T)*C := OMA.OddFaces245212.envelope s primes e hp
  have h : (7/6:ℚ)*x*B+(2/3:ℚ)*y*T=2 := by
    rw [←mul_prod_erase _ _ (mem_univ i),←mul_prod_erase _ _ (mem_univ i)] at bal
    simpa only [mul_assoc,x,y,T,B,s,p] using bal
  have end1 : (7/6:ℚ)*x+(2/3:ℚ)*y≤11/6 := by
    have yy : y≤1 := y_one (hp _) _
    change (7/6:ℚ)*(1+(1-y)/((p:ℚ)-1))+(2/3:ℚ)*y≤11/6
    have lo : ∀ j,5≤primes j := by decide
    have castlo : (5:ℚ)≤(p:ℚ) := by exact_mod_cast lo i
    have p4 : (4:ℚ)≤(p:ℚ)-1 := by linarith
    have scale : (1-y)/((p:ℚ)-1)≤(1-y)/4 := div_le_div_of_nonneg_left (by linarith) (by norm_num) p4
    linarith
  by_contra! low
  have mono : x≤X p (some (floors i-1)) := by
    have yy := y_anti (hp i) (show e i≤floors i-1 by omega)
    have castlo : (1:ℚ)<(p:ℚ) := by exact_mod_cast hp i
    have den : 0<(p:ℚ)-1 := sub_pos.mpr castlo
    change 1+(1-Y p (some (e i)))/((p:ℚ)-1) ≤ 1+(1-Y p (some (floors i-1)))/((p:ℚ)-1)
    exact add_le_add_right (div_le_div_of_nonneg_right (sub_le_sub_left yy _) den.le) _
  have endpoint : (7/6:ℚ)*X p (some (floors i-1))*C<2 := by
    dsimp [p,C,s]; fin_cases i <;> decide +kernel
  have end0 : (7/6:ℚ)*x*C<2 :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left mono (by norm_num)) hc).trans_lt endpoint
  have score := mul_le_mul_of_nonneg_left bound (mul_nonneg (by norm_num : (0:ℚ)≤7/6) (show 0≤x from hx))
  by_cases t0 : T=0
  · rw [t0] at score h
    linarith only [score,h,end0]
  · have a := mul_le_mul_of_nonneg_right end0.le (sub_nonneg.mpr ht)
    have b := mul_lt_mul_of_pos_right (end1.trans_lt (by norm_num : (11:ℚ)/6<2)) (lt_of_le_of_ne hT (Ne.symm t0))
    nlinarith only [a,b,score,h]

theorem candidate (e : Fin 4 → ℕ)
    (eqn : OeisA245212.a (3*total primes e)=(σ 1 (3*total primes e):ℤ)) :
    ∀ i, floors i≤e i := by
  let P : Fin 5 → ℕ := Fin.cons 3 primes
  let E : Fin 5 → ℕ := Fin.cons 1 e
  have prime : ∀ i,(P i).Prime := by decide
  have inj : Function.Injective P := by decide +kernel
  have value : total P E=3*total primes e := by
    unfold total
    rw [Fin.prod_univ_succ]
    simp [P,E]
  have norm := normalized_of_eq P prime inj E (value ▸ eqn)
  unfold normalized at norm
  rw [Fin.prod_univ_succ (fun i => X (P i) (some (E i))),
    Fin.prod_univ_succ (fun i => Y (P i) (some (E i)))] at norm
  change X 3 (some 1)*(∏ i,X (primes i) (some (e i)))+
    Y 3 (some 1)*(∏ i,Y (primes i) (some (e i)))=2 at norm
  rw [show X 3 (some 1)=7/6 by decide +kernel,
    show Y 3 (some 1)=2/3 by decide +kernel] at norm
  exact limits e norm

#print axioms candidate
end OMA.FiveExponentBounds245212
