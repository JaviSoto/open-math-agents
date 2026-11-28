import OddThreeResearch245212

/-! Prime supports of a five-prime A245212 solution with exactly two factors of three. -/
namespace OMA.FiveSquareThree245212
open Finset OMA.Smooth245212 OMA.OddFaces245212
open scoped ArithmeticFunction.sigma
open private OMA.OddSupportClass245212.skip from OddThreeResearch245212

theorem support (p e : Fin 5 → ℕ) (pr : ∀ i,(p i).Prime) (ord : StrictMono p)
    (p0 : p 0=3) (e0 : e 0=2)
    (eqn : OeisA245212.a (total p e)=(σ 1 (total p e):ℤ)) :
    p 1=5 ∧ p 2=7 ∧ (p 3=11 ∨ p 3=13 ∨ p 3=17 ∨ p 3=19) ∧
    (13≤p 3 → p 4<190) ∧ (17≤p 3 → p 4<41) ∧ (19≤p 3 → p 4<33) := by
  let T := ∏ i : Fin 4, Y (p i.succ) (some (e i.succ))
  let C := ∏ i : Fin 4, limitX (p i.succ)
  let B := ∏ i : Fin 4, X (p i.succ) (some (e i.succ))
  have env : B≤T+(1-T)*C := envelope univ (fun i : Fin 4 => p i.succ)
    (fun i => e i.succ) (fun i => (pr _).one_lt)
  have tz : 0≤T := prod_nonneg (fun i _ => y_nonneg (pr _).one_lt _)
  have tone : T≤1 := prod_le_one (fun i _ => y_nonneg (pr _).one_lt _) (fun i _ => y_one (pr _).one_lt _)
  have norm := normalized_of_eq p pr ord.injective e eqn
  unfold normalized at norm
  rw [Fin.prod_univ_succ (fun i => X (p i) (some (e i))),
    Fin.prod_univ_succ (fun i => Y (p i) (some (e i))),p0,e0] at norm
  change X 3 (some 2)*B+Y 3 (some 2)*T=2 at norm
  rw [show X 3 (some 2)=34/27 by decide +kernel,show Y 3 (some 2)=13/27 by decide +kernel] at norm
  have impossible (z : Fin 4 → ℕ) (good : ∀ i,1<z i) (lo : ∀ i,z i≤p i.succ)
      (cut : (34/27:ℚ)*(∏ i,limitX (z i))<2) : False := by
    have cm : C≤∏ i,limitX (z i) := prod_le_prod (s:=univ)
      (fun i _ => x_nonneg (pr _).one_lt _) (fun i _ => cap_anti (good i) (lo i))
    have ca := mul_le_mul_of_nonneg_left cm (sub_nonneg.mpr tone)
    by_cases top : T=1
    · rw [top] at env norm; linarith only [env,norm]
    · have u := mul_lt_mul_of_pos_left cut (sub_pos.mpr (lt_of_le_of_ne tone top))
      nlinarith only [env,ca,u,tz,norm]
  have h01 := ord (by decide : (0:Fin 5)<1)
  have h12 := ord (by decide : (1:Fin 5)<2)
  have h23 := ord (by decide : (2:Fin 5)<3)
  have h34 := ord (by decide : (3:Fin 5)<4)
  have l1 : 5≤p 1 := OMA.OddSupportClass245212.skip (pr 1) (show 4≤p 1 by omega) (by decide)
  have l2 : 7≤p 2 := OMA.OddSupportClass245212.skip (pr 2) (show 6≤p 2 by omega) (by decide)
  have l3 : 11≤p 3 := OMA.OddSupportClass245212.skip (pr 3) (show 8≤p 3 by omega) (by decide)
  have t2 : p 2<11 := by
    by_contra! big
    have d : 13≤p 3 := OMA.OddSupportClass245212.skip (pr 3) (show 12≤p 3 by omega) (by decide)
    have f : 17≤p 4 := OMA.OddSupportClass245212.skip (pr 4) (show 14≤p 4 by omega) (by decide)
    exact impossible ![5,11,13,17] (by decide)
      (fun i => by fin_cases i <;> first | exact l1 | exact big | exact d | exact f) (by decide +kernel)
  have e2 : p 2=7 := by
    by_contra! ne
    have := OMA.OddSupportClass245212.skip (pr 2) (show 8≤p 2 by omega) (by decide : ∀ j∈Ico 8 11,¬Nat.Prime j)
    omega
  have e1 : p 1=5 := by
    by_contra! ne
    have := OMA.OddSupportClass245212.skip (pr 1) (show 6≤p 1 by omega) (by decide : ∀ j∈Ico 6 7,¬Nat.Prime j)
    omega
  have t3 : p 3<23 := by
    by_contra! big
    have f : 29≤p 4 := OMA.OddSupportClass245212.skip (pr 4) (show 24≤p 4 by omega) (by decide)
    exact impossible ![5,7,23,29] (by decide)
      (fun i => by fin_cases i <;> first | exact l1 | exact l2 | exact big | exact f) (by decide +kernel)
  have choices : p 3=11 ∨ p 3=13 ∨ p 3=17 ∨ p 3=19 := by
    have cases : ∀ j∈Ico 11 23,Nat.Prime j → j=11 ∨ j=13 ∨ j=17 ∨ j=19 := by decide
    exact cases _ (mem_Ico.mpr ⟨l3,t3⟩) (pr 3)
  refine ⟨e1,e2,choices,?_,?_,?_⟩
  all_goals intro big; by_contra! f
  · exact impossible ![5,7,13,190] (by decide)
      (fun i => by fin_cases i <;> first | exact l1 | exact l2 | exact big | exact f) (by decide +kernel)
  · exact impossible ![5,7,17,41] (by decide)
      (fun i => by fin_cases i <;> first | exact l1 | exact l2 | exact big | exact f) (by decide +kernel)
  · exact impossible ![5,7,19,33] (by decide)
      (fun i => by fin_cases i <;> first | exact l1 | exact l2 | exact big | exact f) (by decide +kernel)

#print axioms support
end OMA.FiveSquareThree245212
