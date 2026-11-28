import BinaryPrefix

/-! Binary words at a modulus whose doubling orbit has a tail and a cycle. -/

open private OMA.BinaryPrefix.weight OMA.BinaryPrefix.bounded OMA.BinaryPrefix.digits
  OMA.BinaryPrefix.fill OMA.BinaryPrefix.sum_bits from BinaryPrefix

namespace OMA.DyadicDigits
open Finset

def value (s : Multiset ℕ) : ℕ := (s.map (fun j : ℕ=>2^j)).sum

def Valid (n M : ℕ) : Prop :=
  ∀ s : Multiset ℕ, (∀ j∈s,j<n) → s.card=n → value s ≡ 2^n-1 [MOD M] → s=(range n).val

@[simp] theorem value_cons (j : ℕ) (s : Multiset ℕ) : value (j ::ₘ s)=2^j+value s := by
  simp [value]

@[simp] theorem value_range (n : ℕ) : value (range n).val=2^n-1 :=
  OMA.BinaryPrefix.sum_bits n

theorem lower {n M : ℕ} (hm : 0<M) (valid : Valid n M) : 2^n-n≤M := by
  by_contra! low
  let w := 2^n-1-M
  have p : 0<2^n := by positivity
  have small : w<2^n := by dsimp [w]; omega
  have nw : n≤w := by dsimp [w]; omega
  obtain ⟨L,bL,ew,le,_⟩ := OMA.BinaryPrefix.digits n w small
  obtain ⟨S,bS,eS,cS⟩ := OMA.BinaryPrefix.fill n n L bL le (ew ▸ nw)
  have val : value (S : Multiset ℕ)=w := eS.trans ew
  have same : (S : Multiset ℕ)=(range n).val := valid S bS cS (by
    rw [val,show 2^n-1=w+M by dsimp [w]; omega]
    simp [Nat.ModEq])
  have constraint := congrArg value same
  rw [val,value_range] at constraint
  dsimp [w] at constraint; omega

private lemma value_ge_card (s : Multiset ℕ) : s.card≤value s := by
  induction s using Multiset.induction_on with
  | empty => rfl
  | cons a s ih =>
    rw [Multiset.card_cons,value_cons]
    have h : 0<2^a := by positivity
    omega

/-- Merge repeated binary coins, wrapping the highest coin into position t.
    Starting at or above 2^t ensures even a wrap cannot drop below 2^t. -/
private lemma normalized {n t : ℕ} (ht : t<n) (s : Multiset ℕ) (bd : ∀ j∈s,j<n)
    (hi : 2^t≤value s) (hit : value s ≡ 2^n-1 [MOD 2^n-2^t]) :
    s=(range n).val ∨ (range n).card < s.card := by
  classical
  by_cases nd : s.Nodup
  · have sub : s≤(range n).val := (Multiset.le_iff_subset nd).mpr (fun j hj=>mem_range.mpr (bd j hj))
    have mono : ∀ u v : Multiset ℕ, u≤v → value u≤value v := by
      intro u v le
      obtain ⟨w,rfl⟩ := exists_add_of_le le
      simp [value]
    have upper := mono s (range n).val sub
    rw [value_range] at upper
    have ht' : 2^t<2^n := Nat.pow_lt_pow_right (by decide) ht
    have e : value s=2^n-1 := by
      obtain ⟨k,eq⟩ := (Nat.modEq_iff_dvd' upper).mp hit
      by_contra ne
      have pos : 0<2^n-1-value s := by omega
      have b := Nat.le_of_dvd pos (show 2^n-2^t ∣ 2^n-1-value s from ⟨k,eq⟩)
      omega
    have eq : s=(range n).val := by
      obtain ⟨w,ew⟩ := exists_add_of_le sub
      have eqv := congrArg value ew
      rw [value_range,show value (s+w)=value s+value w by simp [value],e] at eqv
      have c := value_ge_card w
      have nilw : w=0 := Multiset.card_eq_zero.mp (by omega)
      simpa [nilw] using ew.symm
    exact .inl eq
  · obtain ⟨j,u,eq⟩ : ∃ j,∃ u : Multiset ℕ,s=j ::ₘ j ::ₘ u := by
      rw [Multiset.nodup_iff_count_le_one] at nd
      push Not at nd
      obtain ⟨j,hj⟩ := nd
      have mem : j∈s := Multiset.count_pos.mp (by omega)
      obtain ⟨v,ev⟩ := Multiset.exists_cons_of_mem mem
      rw [ev,Multiset.count_cons_self] at hj
      obtain ⟨u,eu⟩ := Multiset.exists_cons_of_mem (Multiset.count_pos.mp (show 0<v.count j by omega))
      exact ⟨j,u,by rw [ev,eu]⟩
    have jn := bd j (by rw [eq]; simp)
    let a := if j+1=n then t else j+1
    let u' := a ::ₘ u
    have bound : ∀ l∈u', l<n := by
      intro l hl
      rcases Multiset.mem_cons.mp hl with rfl|hu
      · dsimp [a]; split <;> omega
      · exact bd l (by rw [eq]; simp [hu])
    have val := congrArg value eq
    simp only [value_cons] at val
    have two : 2^j+2^j=2^(j+1) := by rw [Nat.pow_succ]; omega
    have step : value u' ≡ value s [MOD 2^n-2^t] ∧ 2^t≤value u' := by
      by_cases top : j+1=n
      · have pe := Nat.pow_lt_pow_right (by decide : 1<2) ht
        have shape : value s=value u'+(2^n-2^t) := by
          dsimp only [u',a]; rw [if_pos top,value_cons,val,←add_assoc,two,top]; omega
        constructor
        · rw [shape]; simp [Nat.ModEq]
        · dsimp only [u',a]; rw [if_pos top,value_cons]; omega
      · have same : value u'=value s := by
          dsimp only [u',a]; rw [if_neg top,value_cons,val,←add_assoc,two]
        exact ⟨same ▸ Nat.ModEq.refl _,same ▸ hi⟩
    have less : u'.card < s.card := by simp [eq,u']
    apply Or.inr
    rcases normalized ht u' bound step.2 (step.1.trans hit) with eq|lt
    · rwa [eq] at less
    · exact lt.trans less
termination_by s.card

theorem valid_of_threshold {n t : ℕ} (ht : t<n) (hn : 2^t≤n) : Valid n (2^n-2^t) := by
  intro s bd sz hit
  have hi := (hn.trans sz.ge).trans (value_ge_card s)
  exact (normalized ht s bd hi hit).resolve_right (by simp [sz])

end OMA.DyadicDigits
