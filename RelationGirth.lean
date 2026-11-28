import CyclicPairs
import PathReturn

/-! Local inverse bounds for a dense valid cyclic sum system. -/

namespace OMA.RelationGirth
open Finset

private lemma pascal (n k : ℕ) (large : 63 ≤ n) : 10*n.choose k ≤ 2^n := by
  induction n,large using Nat.le_induction generalizing k with
  | base =>
    have m := Nat.choose_le_middle (n:=63) k
    exact (Nat.mul_le_mul_left 10 m).trans (by decide)
  | succ n hn ih =>
    cases k with
    | zero =>
      have h := ih 0
      simp only [Nat.choose_zero_right,mul_one,Nat.pow_succ] at h ⊢
      omega
    | succ k =>
      have h := ih k; have h' := ih k.succ
      rw [Nat.choose_succ_succ,Nat.pow_succ]
      omega

/-- A cross-intersecting union of faces occupying more than a tenth of
    a Boolean cube includes a face fixing at most 62 coordinates. -/
theorem small_face {α : Type*} [DecidableEq α] (S : Finset α)
    (K : Finset (Finset α × Finset α)) (boxes : Finset (Finset α))
    (inside : ∀ p∈K, p.1⊆S ∧ p.2⊆S) (dis : ∀ p∈K,Disjoint p.1 p.2)
    (cross : ∀ p∈K,∀ q∈K,p≠q → (p.1∩q.2).Nonempty)
    (cover : ∀ X∈boxes,∃ p∈K,p.1⊆X ∧ X⊆S\p.2)
    (big : 2^S.card<10*boxes.card) : ∃ p∈K,p.1.card+p.2.card≤62 := by
  classical
  by_contra! no
  let face (p : Finset α×Finset α) := Icc p.1 (S\p.2)
  have cov : boxes⊆K.biUnion face := fun X h=>by
    obtain ⟨p,hp,a,b⟩ := cover X h
    exact mem_biUnion.mpr ⟨p,hp,mem_Icc.mpr ⟨a,b⟩⟩
  have cb := (card_le_card cov).trans card_biUnion_le
  have abb := OMA.CyclicPairs.bollobas S K Prod.fst Prod.snd inside dis cross
  have bound (p : Finset α×Finset α) (hp : p∈K) :
      10*((face p).card:ℝ) ≤ 2^S.card*OMA.CyclicPairs.weight p.1.card p.2.card := by
    obtain ⟨a,b⟩ := inside p hp
    have sub : p.1⊆S\p.2 := fun j h=>mem_sdiff.mpr ⟨a h,disjoint_left.mp (dis p hp) h⟩
    have dim := card_le_card (union_subset a b)
    rw [card_union_of_disjoint (dis p hp)] at dim
    have sz : (face p).card=2^(S.card-(p.1.card+p.2.card)) := by
      dsimp only [face]
      rw [card_Icc_finset sub,card_sdiff_of_subset b]
      congr 1
      omega
    have use := pascal (p.1.card+p.2.card) p.1.card (by have := no p hp;omega)
    have pos : (0:ℝ)<((p.1.card+p.2.card).choose p.1.card : ℕ) :=
      by exact_mod_cast Nat.choose_pos (by omega : p.1.card≤p.1.card+p.2.card)
    rw [sz,OMA.CyclicPairs.weight,mul_one_div]
    apply (le_div_iff₀ pos).2
    push_cast
    exact_mod_cast (show 10*2^(S.card-(p.1.card+p.2.card))*(p.1.card+p.2.card).choose p.1.card ≤
        (2:ℕ)^S.card from by
      calc _ = 2^(S.card-(p.1.card+p.2.card))*(10*(p.1.card+p.2.card).choose p.1.card) := by ring
           _ ≤ 2^(S.card-(p.1.card+p.2.card))*2^(p.1.card+p.2.card) := Nat.mul_le_mul_left _ use
           _ = _ := by rw [←pow_add,Nat.sub_add_cancel dim])
  have w := sum_le_sum bound
  rw [←mul_sum,←mul_sum] at w
  have up := w.trans (mul_le_mul_of_nonneg_left abb (by positivity))
  rw [mul_one] at up
  have lower : 2^S.card<10*∑ p∈K,(face p).card := big.trans_le (by omega)
  exact (not_lt_of_ge up) (by exact_mod_cast lower)

private theorem heavy_bin {α : Type*} [DecidableEq α] (Q : Finset α) (u v : α→ℕ)
    (small : (∑ s∈Q,(u s+v s)) < 2*Q.card) :
    ∃ i j : ℕ,i+j≤3 ∧ Q.card<10*(Q.filter fun s=>u s=i ∧ v s=j).card := by
  classical
  let I := range 4
  let w (i j : ℕ) := 4-(i+j)
  let part (i j : ℕ) := Q.filter (fun s=>u s=i ∧ v s=j)
  have row (s : α) : (∑ i∈I,∑ j∈I, if u s=i ∧ v s=j then w i j else 0)=w (u s) (v s) := by
    by_cases su : u s∈I
    · by_cases sv : v s∈I
      · simp [ite_and,su,sv]
      · have e : w (u s) (v s)=0 := by
          have l : 4≤v s := by simpa [I] using sv
          exact Nat.sub_eq_zero_of_le (by omega)
        simp [ite_and,sv,e]
    · have e : w (u s) (v s)=0 := by
        have l : 4≤u s := by simpa [I] using su
        exact Nat.sub_eq_zero_of_le (by omega)
      simp [ite_and,su,e]
  have lower : 2*Q.card<∑ s∈Q,w (u s) (v s) := by
    have s := Finset.sum_le_sum (s:=Q) (g:=fun s=>u s+v s+w (u s) (v s))
      (f:=fun _=>4) (fun s _=>by dsimp [w];omega)
    rw [sum_add_distrib] at s
    simp only [sum_const,smul_eq_mul] at s
    omega
  have eq : (∑ s∈Q,w (u s) (v s))=∑ i∈I,∑ j∈I,w i j*(part i j).card := by
    simp_rw [←row]
    rw [sum_comm]
    apply sum_congr rfl
    intro i hi
    rw [sum_comm]
    apply sum_congr rfl
    intro j hj
    simp [part,sum_ite, mul_comm]
  by_contra! no
  have ub (i j : ℕ) : 10*(w i j*(part i j).card)≤w i j*Q.card := by
    by_cases le : i+j≤3
    · have upper := Nat.mul_le_mul_left (w i j) (no i j le)
      dsimp only [part]
      nlinarith
    · have z : w i j=0 := Nat.sub_eq_zero_of_le (by omega)
      simp [z]
  have up := sum_le_sum (s:=I) (fun i _=>sum_le_sum (s:=I) (fun j _=>ub i j))
  simp_rw [←mul_sum,←sum_mul] at up
  have tot : (∑ i∈I,∑ j∈I,w i j)=20 := by dsimp only [I,w]; decide
  rw [tot,←eq] at up
  omega

end OMA.RelationGirth
