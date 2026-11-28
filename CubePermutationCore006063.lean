import FormalConjectures.OEIS.«228624»

/-! # Cube-sum permutations (OEIS A006063)

Robert Israel conjectured in 2018 that a cube-sum permutation exists for
every order at least 173 and reported checking orders through 1000.
The proof extends smaller permutations by reflecting a terminal interval.
James Tanton, "Square Permutations" (September 2016), gives this reflection
for the related square problem and asks about cubes; see also Benjamin
Schwartz, Mathematics Magazine 51 (1978), 64–66, for the square antecedent.
The finite witnesses used below are constructed independently.
-/

namespace OMA.CubePermutation

def Admits (n : ℕ) : Prop :=
  ∃ e : Equiv.Perm (Fin n), ∀ i, ∃ k : ℕ, i.val + (e i).val + 2 = k^3

theorem reflect {m n k : ℕ} (hm : m<n) (eq : m+n+1=k^3) (h : Admits m) : Admits n := by
  obtain ⟨p,hp⟩ := h
  let f (i : Fin n) : Fin n :=
    if hi : i.val < m then ⟨(p ⟨i.val,hi⟩).val, by have := (p ⟨i.val,hi⟩).isLt; omega⟩
    else ⟨(n-1-i.val)+m, by have := i.isLt; omega⟩
  have inj : Function.Injective f := by
    intro i j hij
    have hv := Fin.ext_iff.mp hij
    dsimp [f] at hv
    split at hv <;> rename_i hi <;> split at hv <;> rename_i hj <;> dsimp at hv
    · have e : (⟨i.val,hi⟩ : Fin m)=⟨j.val,hj⟩ := p.injective (Fin.ext hv)
      exact Fin.ext (congrArg (fun x : Fin m => x.val) e)
    · have := (p ⟨i.val,hi⟩).isLt; omega
    · have := (p ⟨j.val,hj⟩).isLt; omega
    · apply Fin.ext; have := i.isLt; have := j.isLt; omega
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp inj),?_⟩
  intro i
  change ∃ k, i.val + (f i).val + 2 = k^3
  dsimp [f]
  split <;> rename_i hi <;> dsimp
  · exact hp ⟨i.val,hi⟩
  · exact ⟨k,by have := i.isLt; omega⟩

theorem cube_between (n : ℕ) (hn : 365≤n) :
    ∃ k : ℕ, n+174≤k^3 ∧ k^3≤2*n := by
  have ex : ∃ k : ℕ, n+174≤k^3 := ⟨n+174,Nat.le_self_pow (by decide) _⟩
  let k := Nat.find ex
  refine ⟨k,Nat.find_spec ex,?_⟩
  by_cases small : k≤9
  · have hk := Nat.pow_le_pow_left small 3; norm_num at hk; omega
  · let s := k-1
    have hk : s+1=k := by dsimp [s]; omega
    have under : s^3 < n+174 := by
      have := Nat.find_min ex (show s<k by omega)
      omega
    obtain ⟨a,ha⟩ := Nat.exists_eq_add_of_le (show 9 ≤ s by omega)
    have gap : (s+1)^3+346 ≤ 2*s^3 := by
      rw [ha]
      nlinarith only [Nat.zero_le (a^3),Nat.zero_le (a^2),Nat.zero_le a]
    rw [hk] at gap
    omega

theorem of_bases (base : ∀ n, 173≤n → n<365 → Admits n) (n : ℕ) (hn : 173≤n) : Admits n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases small : n<365
    · exact base n hn small
    obtain ⟨k,lo,hi⟩ := cube_between n (by omega)
    let m := k^3-n-1
    have hm : 173 ≤ m := by dsimp [m]; omega
    have less : m<n := by dsimp [m]; omega
    exact reflect less (show m+n+1=k^3 by dsimp [m]; omega) (ih m less hm)

/-- The two hexadecimal integers give the cube root in digit `i` of each
row and column, starting at the least significant digit.
An edge chosen by two rows would receive the same root on its column,
which determines its row uniquely. -/
def digit (word i : ℕ) : ℕ := (word >>> (4*i)) % 16

def rowCheck (n rows cols i : ℕ) : Bool :=
  let k := digit rows i
  let j := k^3-i-2
  decide (i+2≤k^3 ∧ j<n ∧ digit cols j=k)

def check (n rows cols : ℕ) : Bool :=
  (List.range n).all (rowCheck n rows cols)

theorem of_check {n rows cols : ℕ} (h : check n rows cols = true) : Admits n := by
  let r (i : Fin n) := digit rows i.val
  let j (i : Fin n) := (r i)^3-i.val-2
  have each (i : Fin n) : i.val+2≤(r i)^3 ∧ j i<n ∧ digit cols (j i)=r i := by
    have hi := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
    simpa [rowCheck,r,j] using hi
  let f (i : Fin n) : Fin n := ⟨j i,(each i).2.1⟩
  have inj : Function.Injective f := by
    intro x y hxy
    have e : j x=j y := Fin.ext_iff.mp hxy
    have eq : r x=r y := (each x).2.2.symm.trans (e ▸ (each y).2.2)
    have hx := (each x).1
    have hy := (each y).1
    dsimp [j] at e
    rw [eq] at e hx
    apply Fin.ext; omega
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp inj),?_⟩
  intro i
  refine ⟨r i,?_⟩
  change i.val+j i+2=(r i)^3
  have := (each i).1
  dsimp [j]; omega

/-- A certificate for a failed matching: every allowed neighbor of a listed
row is among a strictly smaller collection of columns. -/
def hallCheck (n : ℕ) (xs ys : List ℕ) : Bool :=
  decide (ys.toFinset.card < xs.toFinset.card) &&
  xs.all (fun i => decide (i<n) && (List.range 10).all (fun k =>
    decide (k^3 < i+2 ∨ n ≤ k^3-i-2 ∨ k^3-i-2 ∈ ys)))

theorem of_hall {n : ℕ} (hn : 2*n<1000) {xs ys : List ℕ}
    (checked : hallCheck n xs ys = true) : ¬ Admits n := by
  obtain ⟨card, rows⟩ := Bool.and_eq_true_iff.mp checked
  have small : ys.toFinset.card < xs.toFinset.card := of_decide_eq_true card
  intro ⟨p,hp⟩
  let f (i : ℕ) := if hi : i<n then (p ⟨i,hi⟩).val else 0
  have inside (i : ℕ) (hi : i ∈ xs) : i<n :=
    of_decide_eq_true (Bool.and_eq_true_iff.mp (List.all_eq_true.mp rows i hi)).1
  have inj : Set.InjOn f (xs.toFinset : Set ℕ) := by
    intro i hi j hj eq
    have h1 := inside i (List.mem_toFinset.mp hi)
    have h2 := inside j (List.mem_toFinset.mp hj)
    dsimp [f] at eq
    rw [dif_pos h1,dif_pos h2] at eq
    exact congrArg (fun x : Fin n => x.val) (p.injective (Fin.ext eq))
  have sub : xs.toFinset.image f ⊆ ys.toFinset := by
    intro j mem
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp mem
    have hi' := List.mem_toFinset.mp hi
    have inn := inside i hi'
    let ii : Fin n := ⟨i,inn⟩
    obtain ⟨k,hk⟩ := hp ii
    have hv := (p ii).isLt
    change i+(p ii).val+2=k^3 at hk
    have smallk : k<10 := by
      by_contra! h
      have pow := Nat.pow_le_pow_left h 3
      norm_num at pow
      omega
    have every := (Bool.and_eq_true_iff.mp (List.all_eq_true.mp rows i hi')).2
    have allowed : k^3 < i+2 ∨ n ≤ k^3-i-2 ∨ k^3-i-2 ∈ ys :=
      of_decide_eq_true (List.all_eq_true.mp every k (List.mem_range.mpr smallk))
    have value : k^3-i-2=(p ii).val := by omega
    apply List.mem_toFinset.mpr
    change (if hi : i<n then (p ⟨i,hi⟩).val else 0) ∈ ys
    rw [dif_pos inn]
    change (p ii).val ∈ ys
    rw [value] at allowed
    rcases allowed with bad|bad|ok <;> omega
  have le := Finset.card_le_card sub
  rw [Finset.card_image_of_injOn inj] at le
  omega

end OMA.CubePermutation
