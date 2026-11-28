import OddThreeResearch245212

/-! A first restriction beyond rank four: at ranks five and six the prime three is necessary. -/
namespace OMA.OddSupportClass245212
open Finset Nat OMA.Smooth245212
open scoped ArithmeticFunction.sigma
open private OMA.OddSupportClass245212.skip OMA.OddSupportClass245212.tiny from OddThreeResearch245212

private theorem sorted_six {k : ℕ} (few : k≤6) (p e : Fin k → ℕ) (hp : ∀ i,(p i).Prime)
    (ord : StrictMono p) (floor : ∀ i,5≤p i) (pos : ∀ i,0<e i)
    (eq : OeisA245212.a (total p e)=(σ 1 (total p e):ℤ)) : total p e=1 := by
  have norm := normalized_of_eq p hp ord.injective e eq
  interval_cases k
  · simp [total]
  · exfalso
    have cap := OMA.OddFaces245212.cap_needed p e (fun i => (hp i).one_lt) 0 (pos 0) norm
    have b0 : 5≤p 0 := floor 0
    exact OMA.OddSupportClass245212.tiny p ![5] (by decide)
      (fun j => by fin_cases j; exact b0) cap (by decide +kernel)
  · exfalso
    have cap := OMA.OddFaces245212.cap_needed p e (fun i => (hp i).one_lt) 0 (pos 0) norm
    have b0 : 5≤p 0 := floor 0
    have b1 : 7≤p 1 := OMA.OddSupportClass245212.skip (hp 1)
      (show 6≤p 1 by have := ord (by decide : (0:Fin 2)<1); omega) (by decide)
    exact OMA.OddSupportClass245212.tiny p ![5,7] (by decide)
      (fun j => by fin_cases j <;> first | exact b0 | exact b1) cap (by decide +kernel)
  · exfalso
    have cap := OMA.OddFaces245212.cap_needed p e (fun i => (hp i).one_lt) 0 (pos 0) norm
    have b0 : 5≤p 0 := floor 0
    have b1 : 7≤p 1 := OMA.OddSupportClass245212.skip (hp 1)
      (show 6≤p 1 by have := ord (by decide : (0:Fin 3)<1); omega) (by decide)
    have b2 : 11≤p 2 := OMA.OddSupportClass245212.skip (hp 2)
      (show 8≤p 2 by have := ord (by decide : (1:Fin 3)<2); omega) (by decide)
    exact OMA.OddSupportClass245212.tiny p ![5,7,11] (by decide)
      (fun j => by fin_cases j <;> first | exact b0 | exact b1 | exact b2) cap (by decide +kernel)
  · exfalso
    have cap := OMA.OddFaces245212.cap_needed p e (fun i => (hp i).one_lt) 0 (pos 0) norm
    have b0 : 5≤p 0 := floor 0
    have b1 : 7≤p 1 := OMA.OddSupportClass245212.skip (hp 1)
      (show 6≤p 1 by have := ord (by decide : (0:Fin 4)<1); omega) (by decide)
    have b2 : 11≤p 2 := OMA.OddSupportClass245212.skip (hp 2)
      (show 8≤p 2 by have := ord (by decide : (1:Fin 4)<2); omega) (by decide)
    have b3 : 13≤p 3 := OMA.OddSupportClass245212.skip (hp 3)
      (show 12≤p 3 by have := ord (by decide : (2:Fin 4)<3); omega) (by decide)
    exact OMA.OddSupportClass245212.tiny p ![5,7,11,13] (by decide)
      (fun j => by fin_cases j <;> first | exact b0 | exact b1 | exact b2 | exact b3) cap (by decide +kernel)
  · exfalso
    have cap := OMA.OddFaces245212.cap_needed p e (fun i => (hp i).one_lt) 0 (pos 0) norm
    have b0 : 5≤p 0 := floor 0
    have b1 : 7≤p 1 := OMA.OddSupportClass245212.skip (hp 1)
      (show 6≤p 1 by have := ord (by decide : (0:Fin 5)<1); omega) (by decide)
    have b2 : 11≤p 2 := OMA.OddSupportClass245212.skip (hp 2)
      (show 8≤p 2 by have := ord (by decide : (1:Fin 5)<2); omega) (by decide)
    have b3 : 13≤p 3 := OMA.OddSupportClass245212.skip (hp 3)
      (show 12≤p 3 by have := ord (by decide : (2:Fin 5)<3); omega) (by decide)
    have b4 : 17≤p 4 := OMA.OddSupportClass245212.skip (hp 4)
      (show 14≤p 4 by have := ord (by decide : (3:Fin 5)<4); omega) (by decide)
    exact OMA.OddSupportClass245212.tiny p ![5,7,11,13,17] (by decide)
      (fun j => by fin_cases j <;> first | exact b0 | exact b1 | exact b2 | exact b3 | exact b4) cap (by decide +kernel)
  · exfalso
    have cap := OMA.OddFaces245212.cap_needed p e (fun i => (hp i).one_lt) 0 (pos 0) norm
    have b0 : 5≤p 0 := floor 0
    have b1 : 7≤p 1 := OMA.OddSupportClass245212.skip (hp 1)
      (show 6≤p 1 by have := ord (by decide : (0:Fin 6)<1); omega) (by decide)
    have b2 : 11≤p 2 := OMA.OddSupportClass245212.skip (hp 2)
      (show 8≤p 2 by have := ord (by decide : (1:Fin 6)<2); omega) (by decide)
    have b3 : 13≤p 3 := OMA.OddSupportClass245212.skip (hp 3)
      (show 12≤p 3 by have := ord (by decide : (2:Fin 6)<3); omega) (by decide)
    have b4 : 17≤p 4 := OMA.OddSupportClass245212.skip (hp 4)
      (show 14≤p 4 by have := ord (by decide : (3:Fin 6)<4); omega) (by decide)
    have b5 : 19≤p 5 := OMA.OddSupportClass245212.skip (hp 5)
      (show 18≤p 5 by have := ord (by decide : (4:Fin 6)<5); omega) (by decide)
    exact OMA.OddSupportClass245212.tiny p ![5,7,11,13,17,19] (by decide)
      (fun j => by fin_cases j <;> first | exact b0 | exact b1 | exact b2 | exact b3 | exact b4 | exact b5) cap (by decide +kernel)

theorem three_needed {n : ℕ} (odd : Odd n) (few : n.primeFactors.card≤6)
    (eq : OeisA245212.a n=(σ 1 n:ℤ)) : n=1 ∨ 3∣n := by
  by_cases div : 3∣n
  · exact Or.inr div
  left
  let S := n.primeFactors
  let p := S.orderEmbOfFin rfl
  let e (i : Fin S.card) := n.factorization (p i)
  have mem (i) : p i∈n.primeFactors := orderEmbOfFin_mem S rfl i
  have hp (i) := Nat.prime_of_mem_primeFactors (mem i)
  have floor (i) : 5≤p i := by
    have h := (hp i).two_le
    have di := Nat.dvd_of_mem_primeFactors (mem i)
    have two : ¬2∣n := fun d => (Nat.not_even_iff_odd.mpr odd) (even_iff_two_dvd.mpr d)
    have not2 : p i≠2 := fun a => two (a ▸ di)
    have not3 : p i≠3 := fun a => div (a ▸ di)
    have not4 : p i≠4 := fun a => (by decide : ¬ Nat.Prime 4) (a ▸ hp i)
    omega
  have pos (i) : 0<e i := (hp i).factorization_pos_of_dvd odd.pos.ne' (Nat.dvd_of_mem_primeFactors (mem i))
  have repr : total p e=n := by
    unfold total e
    exact (Fintype.prod_equiv (S.orderIsoOfFin rfl).toEquiv _
      (fun j : S => j.val^(n.factorization j.val)) (fun _ => rfl)).trans
      (Nat.prod_primeFactors_coe_pow_factorization odd.pos.ne').symm
  simpa only [repr] using sorted_six few p e hp p.strictMono floor pos (by rw [repr]; exact eq)
#print axioms three_needed

/-- With exactly five odd primes and a single factor of three, only one support remains. -/
theorem five_single_three (p e : Fin 5 → ℕ) (pr : ∀ i,(p i).Prime) (ord : StrictMono p)
    (p0 : p 0=3) (e0 : e 0=1)
    (eq : OeisA245212.a (total p e)=(σ 1 (total p e):ℤ)) : p=![3,5,7,11,13] := by
  have a := ord (by decide : (0:Fin 5)<1)
  have b := ord (by decide : (1:Fin 5)<2)
  have c := ord (by decide : (2:Fin 5)<3)
  have d := ord (by decide : (3:Fin 5)<4)
  have b1 : 5≤p 1 := OMA.OddSupportClass245212.skip (pr 1) (show 4≤p 1 by omega) (by decide)
  have b2 : 7≤p 2 := OMA.OddSupportClass245212.skip (pr 2) (show 6≤p 2 by omega) (by decide)
  have b3 : 11≤p 3 := OMA.OddSupportClass245212.skip (pr 3) (show 8≤p 3 by omega) (by decide)
  have b4 : 13≤p 4 := OMA.OddSupportClass245212.skip (pr 4) (show 12≤p 4 by omega) (by decide)
  have top : p 4<17 := by
    by_contra! big
    let z : Fin 4→ℕ := ![5,7,11,17]
    let T := ∏ i : Fin 4, Y (p i.succ) (some (e i.succ))
    let C := ∏ i : Fin 4, OMA.OddFaces245212.limitX (p i.succ)
    let B := ∏ i : Fin 4, X (p i.succ) (some (e i.succ))
    have env : B≤T+(1-T)*C := OMA.OddFaces245212.envelope univ
      (fun i : Fin 4 => p i.succ) (fun i => e i.succ) (fun i => (pr _).one_lt)
    have tz : 0≤T := prod_nonneg (fun i _ => y_nonneg (pr _).one_lt _)
    have tone : T≤1 := prod_le_one (fun i _ => y_nonneg (pr _).one_lt _) (fun i _ => y_one (pr _).one_lt _)
    have lo (i : Fin 4) : z i ≤ p i.succ := by fin_cases i <;> first | exact b1 | exact b2 | exact b3 | exact big
    have gc : ∀ i,1<z i := by decide
    have cm : C≤∏ i,OMA.OddFaces245212.limitX (z i) := prod_le_prod (s:=univ)
      (fun i _ => x_nonneg (pr _).one_lt _) (fun i _ => OMA.OddFaces245212.cap_anti (gc i) (lo i))
    have vc : (∏ i,OMA.OddFaces245212.limitX (z i))=1309/768 := by decide +kernel
    rw [vc] at cm
    have ca := mul_le_mul_of_nonneg_left cm (sub_nonneg.mpr tone)
    have norm := normalized_of_eq p pr ord.injective e eq
    unfold normalized at norm
    rw [Fin.prod_univ_succ (fun i => X (p i) (some (e i))),
      Fin.prod_univ_succ (fun i => Y (p i) (some (e i))),p0,e0] at norm
    change X 3 (some 1)*B+Y 3 (some 1)*T=2 at norm
    rw [show X 3 (some 1)=7/6 by decide +kernel,show Y 3 (some 1)=2/3 by decide +kernel] at norm
    linarith only [tz,tone,ca,env,norm]
  have end4 : p 4=13 := by
    have gaps : ∀ j∈Ico 14 17,¬Nat.Prime j := by decide
    by_contra! ne
    exact gaps _ (mem_Ico.mpr ⟨by omega,top⟩) (pr 4)
  have end3 : p 3=11 := by
    have gaps : ∀ j∈Ico 12 13,¬Nat.Prime j := by decide
    by_contra! ne
    exact gaps _ (mem_Ico.mpr ⟨by omega,by omega⟩) (pr 3)
  have end2 : p 2=7 := by
    have gaps : ∀ j∈Ico 8 11,¬Nat.Prime j := by decide
    by_contra! ne
    exact gaps _ (mem_Ico.mpr ⟨by omega,by omega⟩) (pr 2)
  have end1 : p 1=5 := by
    have gaps : ∀ j∈Ico 6 7,¬Nat.Prime j := by decide
    by_contra! ne
    exact gaps _ (mem_Ico.mpr ⟨by omega,by omega⟩) (pr 1)
  funext i; fin_cases i <;> simp [p0,end1,end2,end3,end4]
#print axioms five_single_three
end OMA.OddSupportClass245212
