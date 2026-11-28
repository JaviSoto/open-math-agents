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

namespace OMA.CubePermutation
private theorem pos0 : Admits 0 := ⟨Equiv.refl _, fun i => Fin.elim0 i⟩
private theorem neg1 : ¬ Admits 1 :=
  of_hall (by decide) (xs := [0]) (ys := []) (by decide +kernel)
private theorem neg2 : ¬ Admits 2 :=
  of_hall (by decide) (xs := [1]) (ys := []) (by decide +kernel)
private theorem neg3 : ¬ Admits 3 :=
  of_hall (by decide) (xs := [2]) (ys := []) (by decide +kernel)
private theorem neg4 : ¬ Admits 4 :=
  of_hall (by decide) (xs := [2]) (ys := []) (by decide +kernel)
private theorem neg5 : ¬ Admits 5 :=
  of_hall (by decide) (xs := [1]) (ys := []) (by decide +kernel)
private theorem neg6 : ¬ Admits 6 :=
  of_hall (by decide) (xs := [0]) (ys := []) (by decide +kernel)
private theorem pos7 : Admits 7 := reflect (k := 2) (by decide) (by decide) pos0
private theorem neg8 : ¬ Admits 8 :=
  of_hall (by decide) (xs := [7]) (ys := []) (by decide +kernel)
private theorem neg9 : ¬ Admits 9 :=
  of_hall (by decide) (xs := [8]) (ys := []) (by decide +kernel)
private theorem neg10 : ¬ Admits 10 :=
  of_hall (by decide) (xs := [9]) (ys := []) (by decide +kernel)
private theorem neg11 : ¬ Admits 11 :=
  of_hall (by decide) (xs := [10]) (ys := []) (by decide +kernel)
private theorem neg12 : ¬ Admits 12 :=
  of_hall (by decide) (xs := [11]) (ys := []) (by decide +kernel)
private theorem neg13 : ¬ Admits 13 :=
  of_hall (by decide) (xs := [12]) (ys := []) (by decide +kernel)
private theorem neg14 : ¬ Admits 14 :=
  of_hall (by decide) (xs := [11]) (ys := []) (by decide +kernel)
private theorem neg15 : ¬ Admits 15 :=
  of_hall (by decide) (xs := [10]) (ys := []) (by decide +kernel)
private theorem neg16 : ¬ Admits 16 :=
  of_hall (by decide) (xs := [9]) (ys := []) (by decide +kernel)
private theorem neg17 : ¬ Admits 17 :=
  of_hall (by decide) (xs := [8]) (ys := []) (by decide +kernel)
private theorem neg18 : ¬ Admits 18 :=
  of_hall (by decide) (xs := [7]) (ys := []) (by decide +kernel)
private theorem pos19 : Admits 19 := reflect (k := 3) (by decide) (by decide) pos7
private theorem neg20 : ¬ Admits 20 :=
  of_hall (by decide) (xs := [0, 19]) (ys := [6]) (by decide +kernel)
private theorem neg21 : ¬ Admits 21 :=
  of_hall (by decide) (xs := [1, 20]) (ys := [5]) (by decide +kernel)
private theorem neg22 : ¬ Admits 22 :=
  of_hall (by decide) (xs := [2, 21]) (ys := [4]) (by decide +kernel)
private theorem neg23 : ¬ Admits 23 :=
  of_hall (by decide) (xs := [2, 21]) (ys := [4]) (by decide +kernel)
private theorem neg24 : ¬ Admits 24 :=
  of_hall (by decide) (xs := [1, 20]) (ys := [5]) (by decide +kernel)
private theorem neg25 : ¬ Admits 25 :=
  of_hall (by decide) (xs := [0, 19]) (ys := [6]) (by decide +kernel)
private theorem pos26 : Admits 26 := reflect (k := 3) (by decide) (by decide) pos0
private theorem neg27 : ¬ Admits 27 :=
  of_hall (by decide) (xs := [26]) (ys := []) (by decide +kernel)
private theorem neg28 : ¬ Admits 28 :=
  of_hall (by decide) (xs := [27]) (ys := []) (by decide +kernel)
private theorem neg29 : ¬ Admits 29 :=
  of_hall (by decide) (xs := [28]) (ys := []) (by decide +kernel)
private theorem neg30 : ¬ Admits 30 :=
  of_hall (by decide) (xs := [29]) (ys := []) (by decide +kernel)
private theorem neg31 : ¬ Admits 31 :=
  of_hall (by decide) (xs := [30]) (ys := []) (by decide +kernel)
private theorem neg32 : ¬ Admits 32 :=
  of_hall (by decide) (xs := [30]) (ys := []) (by decide +kernel)
private theorem neg33 : ¬ Admits 33 :=
  of_hall (by decide) (xs := [29]) (ys := []) (by decide +kernel)
private theorem neg34 : ¬ Admits 34 :=
  of_hall (by decide) (xs := [28]) (ys := []) (by decide +kernel)
private theorem neg35 : ¬ Admits 35 :=
  of_hall (by decide) (xs := [27]) (ys := []) (by decide +kernel)
private theorem neg36 : ¬ Admits 36 :=
  of_hall (by decide) (xs := [26]) (ys := []) (by decide +kernel)
private theorem pos37 : Admits 37 := reflect (k := 4) (by decide) (by decide) pos26
private theorem neg38 : ¬ Admits 38 :=
  of_hall (by decide) (xs := [0, 19, 37]) (ys := [6, 25]) (by decide +kernel)
private theorem neg39 : ¬ Admits 39 :=
  of_hall (by decide) (xs := [1, 20, 38]) (ys := [5, 24]) (by decide +kernel)
private theorem neg40 : ¬ Admits 40 :=
  of_hall (by decide) (xs := [2, 21, 39]) (ys := [4, 23]) (by decide +kernel)
private theorem neg41 : ¬ Admits 41 :=
  of_hall (by decide) (xs := [2, 21, 39]) (ys := [4, 23]) (by decide +kernel)
private theorem neg42 : ¬ Admits 42 :=
  of_hall (by decide) (xs := [1, 20, 38]) (ys := [5, 24]) (by decide +kernel)
private theorem neg43 : ¬ Admits 43 :=
  of_hall (by decide) (xs := [0, 19, 37]) (ys := [6, 25]) (by decide +kernel)
private theorem pos44 : Admits 44 := reflect (k := 4) (by decide) (by decide) pos19
private theorem neg45 : ¬ Admits 45 :=
  of_hall (by decide) (xs := [7, 44]) (ys := [18]) (by decide +kernel)
private theorem neg46 : ¬ Admits 46 :=
  of_hall (by decide) (xs := [8, 45]) (ys := [17]) (by decide +kernel)
private theorem neg47 : ¬ Admits 47 :=
  of_hall (by decide) (xs := [9, 46]) (ys := [16]) (by decide +kernel)
private theorem neg48 : ¬ Admits 48 :=
  of_hall (by decide) (xs := [10, 47]) (ys := [15]) (by decide +kernel)
private theorem neg49 : ¬ Admits 49 :=
  of_hall (by decide) (xs := [11, 48]) (ys := [14]) (by decide +kernel)
private theorem neg50 : ¬ Admits 50 :=
  of_hall (by decide) (xs := [12, 49]) (ys := [13]) (by decide +kernel)
private theorem neg51 : ¬ Admits 51 :=
  of_hall (by decide) (xs := [11, 48]) (ys := [14]) (by decide +kernel)
private theorem neg52 : ¬ Admits 52 :=
  of_hall (by decide) (xs := [10, 47]) (ys := [15]) (by decide +kernel)
private theorem neg53 : ¬ Admits 53 :=
  of_hall (by decide) (xs := [9, 46]) (ys := [16]) (by decide +kernel)
private theorem neg54 : ¬ Admits 54 :=
  of_hall (by decide) (xs := [8, 45]) (ys := [17]) (by decide +kernel)
private theorem neg55 : ¬ Admits 55 :=
  of_hall (by decide) (xs := [7, 44]) (ys := [18]) (by decide +kernel)
private theorem pos56 : Admits 56 := reflect (k := 4) (by decide) (by decide) pos7
private theorem neg57 : ¬ Admits 57 :=
  of_hall (by decide) (xs := [0, 37, 56]) (ys := [6, 25]) (by decide +kernel)
private theorem neg58 : ¬ Admits 58 :=
  of_hall (by decide) (xs := [1, 38, 57]) (ys := [5, 24]) (by decide +kernel)
private theorem neg59 : ¬ Admits 59 :=
  of_hall (by decide) (xs := [2, 39, 58]) (ys := [4, 23]) (by decide +kernel)
private theorem neg60 : ¬ Admits 60 :=
  of_hall (by decide) (xs := [2, 39, 58]) (ys := [4, 23]) (by decide +kernel)
private theorem neg61 : ¬ Admits 61 :=
  of_hall (by decide) (xs := [1, 38, 57]) (ys := [5, 24]) (by decide +kernel)
private theorem neg62 : ¬ Admits 62 :=
  of_hall (by decide) (xs := [0, 37, 56]) (ys := [6, 25]) (by decide +kernel)
private theorem pos63 : Admits 63 := reflect (k := 4) (by decide) (by decide) pos0
private theorem neg64 : ¬ Admits 64 :=
  of_hall (by decide) (xs := [2, 39, 58, 63]) (ys := [4, 23, 60]) (by decide +kernel)
private theorem neg65 : ¬ Admits 65 :=
  of_hall (by decide) (xs := [2, 39, 58, 63]) (ys := [4, 23, 60]) (by decide +kernel)
private theorem pos66 : Admits 66 :=
  of_check (rows := 0x555445554444444444444444444444444444444444444444444444444444422244)
           (cols := 0x555445554444444444444444444444444444444444444444444444444444422244) (by decide +kernel)
private theorem neg67 : ¬ Admits 67 :=
  of_hall (by decide) (xs := [0, 5, 37, 42, 56, 61, 66]) (ys := [1, 6, 20, 25, 57, 62]) (by decide +kernel)
private theorem pos68 : Admits 68 := reflect (k := 5) (by decide) (by decide) pos56
private theorem neg69 : ¬ Admits 69 :=
  of_hall (by decide) (xs := [7, 44, 68]) (ys := [18, 55]) (by decide +kernel)
private theorem neg70 : ¬ Admits 70 :=
  of_hall (by decide) (xs := [8, 45, 69]) (ys := [17, 54]) (by decide +kernel)
private theorem neg71 : ¬ Admits 71 :=
  of_hall (by decide) (xs := [9, 46, 70]) (ys := [16, 53]) (by decide +kernel)
private theorem neg72 : ¬ Admits 72 :=
  of_hall (by decide) (xs := [10, 47, 71]) (ys := [15, 52]) (by decide +kernel)
private theorem neg73 : ¬ Admits 73 :=
  of_hall (by decide) (xs := [11, 48, 72]) (ys := [14, 51]) (by decide +kernel)
private theorem neg74 : ¬ Admits 74 :=
  of_hall (by decide) (xs := [12, 49, 73]) (ys := [13, 50]) (by decide +kernel)
private theorem neg75 : ¬ Admits 75 :=
  of_hall (by decide) (xs := [11, 48, 72]) (ys := [14, 51]) (by decide +kernel)
private theorem neg76 : ¬ Admits 76 :=
  of_hall (by decide) (xs := [10, 47, 71]) (ys := [15, 52]) (by decide +kernel)
private theorem neg77 : ¬ Admits 77 :=
  of_hall (by decide) (xs := [9, 46, 70]) (ys := [16, 53]) (by decide +kernel)
private theorem neg78 : ¬ Admits 78 :=
  of_hall (by decide) (xs := [8, 45, 69]) (ys := [17, 54]) (by decide +kernel)
private theorem neg79 : ¬ Admits 79 :=
  of_hall (by decide) (xs := [7, 44, 68]) (ys := [18, 55]) (by decide +kernel)
private theorem pos80 : Admits 80 := reflect (k := 5) (by decide) (by decide) pos44
private theorem neg81 : ¬ Admits 81 :=
  of_hall (by decide) (xs := [0, 5, 19, 37, 42, 61, 66, 80]) (ys := [1, 6, 20, 25, 43, 57, 62]) (by decide +kernel)
private theorem pos82 : Admits 82 :=
  of_check (rows := 0x5555555555555555555445555555555555555555444444444444444444444333333333333333322244)
           (cols := 0x5555555555555555555445555555555555555555444444444444444444444333333333333333322244) (by decide +kernel)
private theorem neg83 : ¬ Admits 83 :=
  of_hall (by decide) (xs := [2, 21, 39, 63, 82]) (ys := [4, 23, 41, 60]) (by decide +kernel)
private theorem neg84 : ¬ Admits 84 :=
  of_hall (by decide) (xs := [2, 21, 39, 63, 82]) (ys := [4, 23, 41, 60]) (by decide +kernel)
private theorem pos85 : Admits 85 :=
  of_check (rows := 0x5555555555555555555555445555555555555555555555444444444444444333333333333333333333344)
           (cols := 0x5555555555555555555555445555555555555555555555444444444444444333333333333333333333344) (by decide +kernel)
private theorem neg86 : ¬ Admits 86 :=
  of_hall (by decide) (xs := [0, 19, 24, 37, 61, 80, 85]) (ys := [1, 6, 25, 38, 43, 62]) (by decide +kernel)
private theorem pos87 : Admits 87 := reflect (k := 5) (by decide) (by decide) pos37
private theorem neg88 : ¬ Admits 88 :=
  of_hall (by decide) (xs := [26, 87]) (ys := [36]) (by decide +kernel)
private theorem neg89 : ¬ Admits 89 :=
  of_hall (by decide) (xs := [27, 88]) (ys := [35]) (by decide +kernel)
private theorem neg90 : ¬ Admits 90 :=
  of_hall (by decide) (xs := [28, 89]) (ys := [34]) (by decide +kernel)
private theorem neg91 : ¬ Admits 91 :=
  of_hall (by decide) (xs := [29, 90]) (ys := [33]) (by decide +kernel)
private theorem neg92 : ¬ Admits 92 :=
  of_hall (by decide) (xs := [30, 91]) (ys := [32]) (by decide +kernel)
private theorem neg93 : ¬ Admits 93 :=
  of_hall (by decide) (xs := [30, 91]) (ys := [32]) (by decide +kernel)
private theorem neg94 : ¬ Admits 94 :=
  of_hall (by decide) (xs := [29, 90]) (ys := [33]) (by decide +kernel)
private theorem neg95 : ¬ Admits 95 :=
  of_hall (by decide) (xs := [28, 89]) (ys := [34]) (by decide +kernel)
private theorem neg96 : ¬ Admits 96 :=
  of_hall (by decide) (xs := [27, 88]) (ys := [35]) (by decide +kernel)
private theorem neg97 : ¬ Admits 97 :=
  of_hall (by decide) (xs := [26, 87]) (ys := [36]) (by decide +kernel)
private theorem pos98 : Admits 98 := reflect (k := 5) (by decide) (by decide) pos26
private theorem neg99 : ¬ Admits 99 :=
  of_hall (by decide) (xs := [0, 19, 24, 61, 80, 85, 98]) (ys := [1, 6, 25, 38, 43, 62]) (by decide +kernel)
private theorem pos100 : Admits 100 :=
  of_check (rows := 0x5555555555555555555555555555555555555445555555555555555555555555555555555555333333333333333333333344)
           (cols := 0x5555555555555555555555555555555555555445555555555555555555555555555555555555333333333333333333333344) (by decide +kernel)
private theorem neg101 : ¬ Admits 101 :=
  of_hall (by decide) (xs := [2, 21, 63, 82, 100]) (ys := [4, 23, 41, 60]) (by decide +kernel)
private theorem neg102 : ¬ Admits 102 :=
  of_hall (by decide) (xs := [2, 21, 63, 82, 100]) (ys := [4, 23, 41, 60]) (by decide +kernel)
private theorem pos103 : Admits 103 :=
  of_check (rows := 0x5555555555555555555555555555555555555555445555555555555555555555555555555555555555333333333333333322244)
           (cols := 0x5555555555555555555555555555555555555555445555555555555555555555555555555555555555333333333333333322244) (by decide +kernel)
private theorem neg104 : ¬ Admits 104 :=
  of_hall (by decide) (xs := [0, 5, 19, 61, 66, 80, 98, 103]) (ys := [1, 6, 20, 25, 43, 57, 62]) (by decide +kernel)
private theorem pos105 : Admits 105 := reflect (k := 5) (by decide) (by decide) pos19
private theorem neg106 : ¬ Admits 106 :=
  of_hall (by decide) (xs := [7, 68, 105]) (ys := [18, 55]) (by decide +kernel)
private theorem neg107 : ¬ Admits 107 :=
  of_hall (by decide) (xs := [8, 69, 106]) (ys := [17, 54]) (by decide +kernel)
private theorem neg108 : ¬ Admits 108 :=
  of_hall (by decide) (xs := [8, 69, 106]) (ys := [17, 54]) (by decide +kernel)
private theorem neg109 : ¬ Admits 109 :=
  of_hall (by decide) (xs := [7, 68, 105]) (ys := [18, 55]) (by decide +kernel)
private theorem pos110 : Admits 110 := reflect (k := 6) (by decide) (by decide) pos105
private theorem neg111 : ¬ Admits 111 :=
  of_hall (by decide) (xs := [0, 5, 12, 19, 61, 66, 73, 80, 98, 103, 110]) (ys := [1, 6, 13, 20, 25, 43, 50, 57, 62, 104]) (by decide +kernel)
private theorem pos112 : Admits 112 := reflect (k := 6) (by decide) (by decide) pos103
private theorem neg113 : ¬ Admits 113 :=
  of_hall (by decide) (xs := [2, 7, 14, 21, 63, 68, 75, 82, 100, 105, 112]) (ys := [4, 11, 18, 23, 41, 48, 55, 60, 102, 109]) (by decide +kernel)
private theorem neg114 : ¬ Admits 114 :=
  of_hall (by decide) (xs := [2, 7, 14, 21, 63, 68, 75, 82, 100, 105, 112]) (ys := [4, 11, 18, 23, 41, 48, 55, 60, 102, 109]) (by decide +kernel)
private theorem pos115 : Admits 115 := reflect (k := 6) (by decide) (by decide) pos100
private theorem pos116 : Admits 116 :=
  of_check (rows := 0x56565565656556565555555555555555555555555555555555555555555555555555555555555555555555555555353553535355353532232322)
           (cols := 0x56565565656556565555555555555555555555555555555555555555555555555555555555555555555555555555353553535355353532232322) (by decide +kernel)
private theorem pos117 : Admits 117 := reflect (k := 5) (by decide) (by decide) pos7
private theorem pos118 : Admits 118 :=
  of_check (rows := 0x5656565565656556565655555555555555555555555555555555555555555555555555555555555555555555555535353553535355353535232323)
           (cols := 0x5656565565656556565655555555555555555555555555555555555555555555555555555555555555555555555535353553535355353535232323) (by decide +kernel)
private theorem pos119 : Admits 119 :=
  of_check (rows := 0x55666665566666556666655555555555555555555555555555555555555555555555555555555555555555555555533333553333355333335533333)
           (cols := 0x55666665566666556666655555555555555555555555555555555555555555555555555555555555555555555555533333553333355333335533333) (by decide +kernel)
private theorem pos120 : Admits 120 :=
  of_check (rows := 0x555556555555655555565555555555555555555555555555555555555445555555555555555555555555555555555555355555535555553555552344)
           (cols := 0x555556555555655555565555555555555555555555555555555555555445555555555555555555555555555555555555355555535555553555552344) (by decide +kernel)
private theorem pos121 : Admits 121 :=
  of_check (rows := 0x5555556555555655555565555555555555555555555555555555555555445555555555555555555555555555555555555355555535555553555555344)
           (cols := 0x5555556555555655555565555555555555555555555555555555555555445555555555555555555555555555555555555355555535555553555555344) (by decide +kernel)
private theorem pos122 : Admits 122 :=
  of_check (rows := 0x55555555555555555555555555555555555555555555555555555555555445555555555555555555555555555555555555555555555555555555555544)
           (cols := 0x55555555555555555555555555555555555555555555555555555555555445555555555555555555555555555555555555555555555555555555555544) (by decide +kernel)
private theorem pos123 : Admits 123 :=
  of_check (rows := 0x655555555555555555555555555555655555555555555555555555555555445555555555555555555555555555545555555555555555555555555555544)
           (cols := 0x655555555555555555555555555555655555555555555555555555555555445555555555555555555555555555545555555555555555555555555555544) (by decide +kernel)
private theorem pos124 : Admits 124 := reflect (k := 5) (by decide) (by decide) pos0
private theorem pos125 : Admits 125 :=
  of_check (rows := 0x66666555556555555655555565555566666555555555555555555555555555445555555555555555555555555554444455555355555535555553555552344)
           (cols := 0x66666555556555555655555565555566666555555555555555555555555555445555555555555555555555555554444455555355555535555553555552344) (by decide +kernel)
private theorem pos126 : Admits 126 :=
  of_check (rows := 0x666666655555555555555555555555666666655555555555555555555555555445555555555555555555555555544444445555555555555555555555522244)
           (cols := 0x666666655555555555555555555555666666655555555555555555555555555445555555555555555555555555544444445555555555555555555555522244) (by decide +kernel)
private theorem pos127 : Admits 127 :=
  of_check (rows := 0x6666666665656565565656556565656666666665555555555555555555555555555555555555555555555555555444444444535353553535355353535232323)
           (cols := 0x6666666665656565565656556565656666666665555555555555555555555555555555555555555555555555555444444444535353553535355353535232323) (by decide +kernel)
private theorem pos128 : Admits 128 := reflect (k := 6) (by decide) (by decide) pos87
private theorem pos129 : Admits 129 :=
  of_check (rows := 0x666666666666656565565656556565666666666666655555555555555555555555555555555555555555555555544444444444445353553535355353532232322)
           (cols := 0x666666666666656565565656556565666666666666655555555555555555555555555555555555555555555555544444444444445353553535355353532232322) (by decide +kernel)
private theorem pos130 : Admits 130 := reflect (k := 6) (by decide) (by decide) pos85
private theorem pos131 : Admits 131 :=
  of_check (rows := 0x66666665556666666666666666666666666665556666666555555555555555555555555555555555555555555554444444555444444433333333333333333333555)
           (cols := 0x66666665556666666666666666666666666665556666666555555555555555555555555555555555555555555554444444555444444433333333333333333333555) (by decide +kernel)
private theorem pos132 : Admits 132 :=
  of_check (rows := 0x666666665556666666666666666666666666665556666666655555555555555555555555555555555555555555544444444555444444443333333333333333332555)
           (cols := 0x666666665556666666666666666666666666665556666666655555555555555555555555555555555555555555544444444555444444443333333333333333332555) (by decide +kernel)
private theorem pos133 : Admits 133 := reflect (k := 6) (by decide) (by decide) pos82
private theorem neg134 : ¬ Admits 134 :=
  of_hall (by decide) (xs := [0, 4, 5, 12, 19, 30, 34, 35, 37, 41, 42, 61, 65, 66, 73, 80, 91, 95, 96, 103, 110, 121, 125, 126, 128, 132, 133]) (ys := [1, 2, 6, 13, 20, 21, 25, 27, 28, 32, 43, 50, 57, 58, 62, 81, 82, 86, 88, 89, 93, 104, 111, 118, 119, 123]) (by decide +kernel)
private theorem pos135 : Admits 135 := reflect (k := 6) (by decide) (by decide) pos80
private theorem neg136 : ¬ Admits 136 :=
  of_hall (by decide) (xs := [7, 37, 44, 68, 98, 128, 135]) (ys := [18, 25, 55, 79, 86, 116]) (by decide +kernel)
private theorem neg137 : ¬ Admits 137 :=
  of_hall (by decide) (xs := [8, 37, 38, 45, 69, 99, 128, 129, 136]) (ys := [17, 24, 25, 54, 78, 85, 86, 115]) (by decide +kernel)
private theorem neg138 : ¬ Admits 138 :=
  of_hall (by decide) (xs := [9, 37, 38, 39, 46, 70, 100, 128, 129, 130, 137]) (ys := [16, 23, 24, 25, 53, 77, 84, 85, 86, 114]) (by decide +kernel)
private theorem neg139 : ¬ Admits 139 :=
  of_hall (by decide) (xs := [10, 37, 38, 39, 40, 47, 71, 101, 128, 129, 130, 131, 138]) (ys := [15, 22, 23, 24, 25, 52, 76, 83, 84, 85, 86, 113]) (by decide +kernel)
private theorem neg140 : ¬ Admits 140 :=
  of_hall (by decide) (xs := [11, 37, 38, 39, 40, 41, 48, 72, 102, 128, 129, 130, 131, 132, 139]) (ys := [14, 21, 22, 23, 24, 25, 51, 75, 82, 83, 84, 85, 86, 112]) (by decide +kernel)
private theorem neg141 : ¬ Admits 141 :=
  of_hall (by decide) (xs := [12, 37, 38, 39, 40, 41, 42, 49, 73, 103, 128, 129, 130, 131, 132, 133, 140]) (ys := [13, 20, 21, 22, 23, 24, 25, 50, 74, 81, 82, 83, 84, 85, 86, 111]) (by decide +kernel)
private theorem neg142 : ¬ Admits 142 :=
  of_hall (by decide) (xs := [11, 37, 38, 39, 40, 41, 48, 72, 102, 128, 129, 130, 131, 132, 139]) (ys := [14, 21, 22, 23, 24, 25, 51, 75, 82, 83, 84, 85, 86, 112]) (by decide +kernel)
private theorem neg143 : ¬ Admits 143 :=
  of_hall (by decide) (xs := [10, 37, 38, 39, 40, 47, 71, 101, 128, 129, 130, 131, 138]) (ys := [15, 22, 23, 24, 25, 52, 76, 83, 84, 85, 86, 113]) (by decide +kernel)
private theorem neg144 : ¬ Admits 144 :=
  of_hall (by decide) (xs := [9, 37, 38, 39, 46, 70, 100, 128, 129, 130, 137]) (ys := [16, 23, 24, 25, 53, 77, 84, 85, 86, 114]) (by decide +kernel)
private theorem neg145 : ¬ Admits 145 :=
  of_hall (by decide) (xs := [8, 37, 38, 45, 69, 99, 128, 129, 136]) (ys := [17, 24, 25, 54, 78, 85, 86, 115]) (by decide +kernel)
private theorem neg146 : ¬ Admits 146 :=
  of_hall (by decide) (xs := [7, 37, 44, 68, 98, 128, 135]) (ys := [18, 25, 55, 79, 86, 116]) (by decide +kernel)
private theorem pos147 : Admits 147 := reflect (k := 6) (by decide) (by decide) pos68
private theorem neg148 : ¬ Admits 148 :=
  of_hall (by decide) (xs := [0, 4, 5, 30, 34, 35, 37, 41, 42, 56, 61, 65, 66, 91, 95, 96, 121, 125, 126, 128, 132, 133, 147]) (ys := [1, 2, 6, 20, 21, 25, 27, 28, 32, 57, 58, 62, 67, 81, 82, 86, 88, 89, 93, 118, 119, 123]) (by decide +kernel)
private theorem pos149 : Admits 149 := reflect (k := 6) (by decide) (by decide) pos66
private theorem pos150 : Admits 150 :=
  of_check (rows := 0x666666666666666666666666665556666666666666666666666666665556666666666666666666666666655555544444444444444444444444444555444444444444444444444444442555)
           (cols := 0x666666666666666666666666665556666666666666666666666666665556666666666666666666666666655555544444444444444444444444444555444444444444444444444444442555) (by decide +kernel)
private theorem pos151 : Admits 151 :=
  of_check (rows := 0x6666666666666666666666666665556666666666666666666666666665556666666666666666666666666665555444444444444444444444444444555444444444444444444444444444555)
           (cols := 0x6666666666666666666666666665556666666666666666666666666665556666666666666666666666666665555444444444444444444444444444555444444444444444444444444444555) (by decide +kernel)
private theorem pos152 : Admits 152 := reflect (k := 6) (by decide) (by decide) pos63
private theorem neg153 : ¬ Admits 153 :=
  of_hall (by decide) (xs := [0, 30, 37, 56, 60, 91, 121, 128, 147, 151, 152]) (ys := [2, 6, 25, 32, 62, 63, 67, 86, 93, 123]) (by decide +kernel)
private theorem neg154 : ¬ Admits 154 :=
  of_hall (by decide) (xs := [0, 30, 37, 56, 60, 91, 121, 128, 147, 151, 152]) (ys := [2, 6, 25, 32, 62, 63, 67, 86, 93, 123]) (by decide +kernel)
private theorem pos155 : Admits 155 :=
  of_check (rows := 0x66666666666666666666666666666665556666666666666666666666666665556666666666666666666666666666666444444444444444444444444444555444444444444444444444444444555)
           (cols := 0x66666666666666666666666666666665556666666666666666666666666665556666666666666666666666666666666444444444444444444444444444555444444444444444444444444444555) (by decide +kernel)
private theorem pos156 : Admits 156 :=
  of_check (rows := 0x666666666666666666666666666666665556666666666666666666666666665556666666666666666666666666666666644444444444444444444444444555444444444444444444444444442555)
           (cols := 0x666666666666666666666666666666665556666666666666666666666666665556666666666666666666666666666666644444444444444444444444444555444444444444444444444444442555) (by decide +kernel)
private theorem neg157 : ¬ Admits 157 :=
  of_hall (by decide) (xs := [0, 4, 30, 34, 37, 41, 56, 91, 95, 121, 125, 128, 132, 147, 152, 156]) (ys := [2, 6, 21, 25, 28, 32, 58, 62, 67, 82, 86, 89, 93, 119, 123]) (by decide +kernel)
private theorem neg158 : ¬ Admits 158 :=
  of_hall (by decide) (xs := [0, 4, 30, 34, 37, 41, 56, 91, 95, 121, 125, 128, 132, 147, 152, 156]) (ys := [2, 6, 21, 25, 28, 32, 58, 62, 67, 82, 86, 89, 93, 119, 123]) (by decide +kernel)
private theorem pos159 : Admits 159 := reflect (k := 6) (by decide) (by decide) pos56
private theorem neg160 : ¬ Admits 160 :=
  of_hall (by decide) (xs := [7, 37, 44, 98, 128, 135, 159]) (ys := [18, 25, 55, 79, 86, 116]) (by decide +kernel)
private theorem neg161 : ¬ Admits 161 :=
  of_hall (by decide) (xs := [8, 37, 38, 45, 99, 128, 129, 136, 160]) (ys := [17, 24, 25, 54, 78, 85, 86, 115]) (by decide +kernel)
private theorem neg162 : ¬ Admits 162 :=
  of_hall (by decide) (xs := [9, 37, 38, 39, 46, 100, 128, 129, 130, 137, 161]) (ys := [16, 23, 24, 25, 53, 77, 84, 85, 86, 114]) (by decide +kernel)
private theorem neg163 : ¬ Admits 163 :=
  of_hall (by decide) (xs := [10, 37, 38, 39, 40, 47, 101, 128, 129, 130, 131, 138, 162]) (ys := [15, 22, 23, 24, 25, 52, 76, 83, 84, 85, 86, 113]) (by decide +kernel)
private theorem neg164 : ¬ Admits 164 :=
  of_hall (by decide) (xs := [11, 37, 38, 39, 40, 41, 48, 102, 128, 129, 130, 131, 132, 139, 163]) (ys := [14, 21, 22, 23, 24, 25, 51, 75, 82, 83, 84, 85, 86, 112]) (by decide +kernel)
private theorem neg165 : ¬ Admits 165 :=
  of_hall (by decide) (xs := [12, 37, 38, 39, 40, 41, 42, 49, 103, 128, 129, 130, 131, 132, 133, 140, 164]) (ys := [13, 20, 21, 22, 23, 24, 25, 50, 74, 81, 82, 83, 84, 85, 86, 111]) (by decide +kernel)
private theorem neg166 : ¬ Admits 166 :=
  of_hall (by decide) (xs := [11, 37, 38, 39, 40, 41, 48, 102, 128, 129, 130, 131, 132, 139, 163]) (ys := [14, 21, 22, 23, 24, 25, 51, 75, 82, 83, 84, 85, 86, 112]) (by decide +kernel)
private theorem neg167 : ¬ Admits 167 :=
  of_hall (by decide) (xs := [10, 37, 38, 39, 40, 47, 101, 128, 129, 130, 131, 138, 162]) (ys := [15, 22, 23, 24, 25, 52, 76, 83, 84, 85, 86, 113]) (by decide +kernel)
private theorem neg168 : ¬ Admits 168 :=
  of_hall (by decide) (xs := [9, 37, 38, 39, 46, 100, 128, 129, 130, 137, 161]) (ys := [16, 23, 24, 25, 53, 77, 84, 85, 86, 114]) (by decide +kernel)
private theorem neg169 : ¬ Admits 169 :=
  of_hall (by decide) (xs := [8, 37, 38, 45, 99, 128, 129, 136, 160]) (ys := [17, 24, 25, 54, 78, 85, 86, 115]) (by decide +kernel)
private theorem neg170 : ¬ Admits 170 :=
  of_hall (by decide) (xs := [7, 37, 44, 98, 128, 135, 159]) (ys := [18, 25, 55, 79, 86, 116]) (by decide +kernel)
private theorem pos171 : Admits 171 := reflect (k := 6) (by decide) (by decide) pos44
private theorem neg172 : ¬ Admits 172 :=
  of_hall (by decide) (xs := [0, 4, 7, 12, 19, 30, 34, 37, 41, 42, 44, 91, 95, 98, 103, 110, 121, 125, 128, 132, 133, 135, 152, 156, 159, 164, 171]) (ys := [2, 6, 13, 18, 20, 21, 25, 28, 32, 43, 50, 55, 58, 62, 79, 81, 82, 86, 89, 93, 104, 111, 116, 119, 123, 170]) (by decide +kernel)
private theorem pos173 : Admits 173 :=
  of_check (rows := 0x66666666666666666666666666666666666666666666666666666666666665566666556666666666666666666666666666666666666666666666666666666666666444444444444444444444553333355333332222222)
           (cols := 0x66666666666666666666666666666666666666666666666666666666666665566666556666666666666666666666666666666666666666666666666666666666666444444444444444444444553333355333332222222) (by decide +kernel)
private theorem pos174 : Admits 174 :=
  of_check (rows := 0x666666666666666666666666666666666666666666666666665556666666666666666666666666665556666666666666666666666666666666666666666666666666644444444555444444443333333333333333332555)
           (cols := 0x666666666666666666666666666666666666666666666666665556666666666666666666666666665556666666666666666666666666666666666666666666666666644444444555444444443333333333333333332555) (by decide +kernel)
private theorem pos175 : Admits 175 :=
  of_check (rows := 0x6666666666666666666666666666666666666666666666666665556666666666666666666666666665556666666666666666666666666666666666666666666666666664444444555444444433333333333333333333555)
           (cols := 0x6666666666666666666666666666666666666666666666666665556666666666666666666666666665556666666666666666666666666666666666666666666666666664444444555444444433333333333333333333555) (by decide +kernel)
private theorem pos176 : Admits 176 :=
  of_check (rows := 0x66666666666666666666666666666666666666666666666666666666666666665566666556666666666666666666666666666666666666666666666666666666666666666444444444444444333553333355333332233322)
           (cols := 0x66666666666666666666666666666666666666666666666666666666666666665566666556666666666666666666666666666666666666666666666666666666666666666444444444444444333553333355333332233322) (by decide +kernel)
private theorem pos177 : Admits 177 :=
  of_check (rows := 0x666666666666666666666666666666666666666666666666666665656666665666666566666656666665656666666666666666666666666666666666666666666666666666644444545444443533333353333335333333535)
           (cols := 0x666666666666666666666666666666666666666666666666666665656666665666666566666656666665656666666666666666666666666666666666666666666666666666644444545444443533333353333335333333535) (by decide +kernel)
private theorem pos178 : Admits 178 := reflect (k := 6) (by decide) (by decide) pos37
private theorem pos179 : Admits 179 :=
  of_check (rows := 0x66676667666666676666666666666666666666666666666666666666656665666666666666666666566666656666666666666666666666666666666666666666664666466666664444445444533433343333333433353333335)
           (cols := 0x76666666766676666666666666666666666666666666666666666665666666566666666666666666656665666666666666666666666666666666666666666664666666646664666444544444453333334333433333335333533) (by decide +kernel)
private theorem pos180 : Admits 180 :=
  of_check (rows := 0x666776677666666676666666666666666666666666666666666666666556655666666666666656665565666556666666666666666666666666666666666666666644664466666664644455445534433443333335433553533355)
           (cols := 0x676666666776677666666666666666666666666666666666666666665566656556665666666666666655665566666666666666666666666666666666666666664666666644664466644554445455333534433443333335533553) (by decide +kernel)
private theorem pos181 : Admits 181 :=
  of_check (rows := 0x6766677777666766677766666666666666666666666666666666666666656565666666666666666665566666656666666666666666666666666666666666666646664444466646664444445454533444443334333444553332325)
           (cols := 0x7776667666777776667666666666666666666666666666666666666665666666556666666666666666656565666666666666666666666666666666666666666444666466644444666464544444455343334444433343335252533) (by decide +kernel)
private theorem pos182 : Admits 182 :=
  of_check (rows := 0x66666677777666666677776666666666666666666666666666666666666655555666666666666666666566666656666666666666666666666666666666666666666664444466666664444445555533444443333333444453333335)
           (cols := 0x77776666666777776666666666666666666666666666666666666666665666666566666666666666666655555666666666666666666666666666666666666664444666666644444666666544444453333334444433333335555533) (by decide +kernel)
private theorem pos183 : Admits 183 := reflect (k := 7) (by decide) (by decide) pos159
private theorem pos184 : Admits 184 :=
  of_check (rows := 0x6767676777777767676777777766666666666666666666666666666666666565656666666666666666666666666666666666666666666666666666666666666646464644444446464644444454545434444444343434444444323232)
           (cols := 0x7777777676767777777676767666666666666666666666666666666666666666666666666666666666666665656566666666666666666666666666666666666444444464646444444464646464444443434344444443434342525253) (by decide +kernel)
private theorem pos185 : Admits 185 :=
  of_check (rows := 0x66676767677777676767677777676666666666666666666666666666666665656565666666666666666666666666666666666666666666666666666666666666664646464444464646464444565454543444443434343444443432323)
           (cols := 0x76777776767676777776767676666666666666666666666666666666666666666666666666666666666666656565656666666666666666666666666666666664644444646464644444646464666444434343434444434343435252535) (by decide +kernel)
private theorem pos186 : Admits 186 := reflect (k := 7) (by decide) (by decide) pos156
private theorem pos187 : Admits 187 := reflect (k := 7) (by decide) (by decide) pos155
private theorem pos188 : Admits 188 :=
  of_check (rows := 0x66677677776676667677776676667777776666666666666666666666666666666656666666665666666566666666666666666666666666666666666666666666664464444664666464444664666445444433433543444453433344444433)
           (cols := 0x77777766676677776766676677776776666666666666666666666666666666666666666666666566666656666666665666666666666666666666666666666664444446664664444646664664444644666433444454333435444434433533) (by decide +kernel)
private theorem pos189 : Admits 189 := reflect (k := 6) (by decide) (by decide) pos26
private theorem pos190 : Admits 190 := reflect (k := 7) (by decide) (by decide) pos152
private theorem pos191 : Admits 191 := reflect (k := 7) (by decide) (by decide) pos151
private theorem pos192 : Admits 192 := reflect (k := 7) (by decide) (by decide) pos150
private theorem pos193 : Admits 193 := reflect (k := 7) (by decide) (by decide) pos149
private theorem pos194 : Admits 194 :=
  of_check (rows := 0x67777777776776767677777776767677777677777777776666666666666666666666666666565666666666666666666666666666666666666666666666666666555555555644646464444444646464444464454543444444434343444442422323)
           (cols := 0x77777777776777776767677777776767677677777777766666666666666666666666666666666666666666666666666656566666666666666666666666666665555555554644444646464444444646464464444434346444444434343445252232) (by decide +kernel)
private theorem pos195 : Admits 195 := reflect (k := 7) (by decide) (by decide) pos147
private theorem pos196 : Admits 196 := reflect (k := 6) (by decide) (by decide) pos19
private theorem pos197 : Admits 197 :=
  of_check (rows := 0x66777777777777777777677776667777677777777777777777776666666666666666666666666666666666666666666666666666666666666666666666666666655555555555555444464444666444464444444444443444433344443444442322223)
           (cols := 0x77777777777777777776777766677776777777777777777777666666666666666666666666666666666666666666666666666666666666666666666666666665555555555555544444644446664444644444444444434444366444434444333222232) (by decide +kernel)
private theorem pos198 : Admits 198 :=
  of_check (rows := 0x667777777777777777776677766667776677777777777777777776666666666666666666666666666656666566666656666566666666666666666666666666666555555555555555444664446666444664444444444435444353644435444453222232)
           (cols := 0x677777777777777777776677766667776677777777777777777766666666666666666666666666666566665666666566665666666666666666666666666666665555555555555554444664446666444664444444444453444536644453444532322223) (by decide +kernel)
private theorem pos199 : Admits 199 :=
  of_check (rows := 0x6677777777777777777766666666666666677777777777777777777766666666666666666666666665556665555666556665666666666666666666666666666665555555555555555556666666666666664444444444555333555533355444532233323)
           (cols := 0x7777777777777777777776666666666666667777777777777777776666666666666666666666666666656665566655556665556666666666666666666666666555555555555555555444666666666666666444444444435333553665555333555233322) (by decide +kernel)
private theorem pos200 : Admits 200 :=
  of_check (rows := 0x67777777777777777777776666666766677667777777777777767777766666666666666666666666666566565666666666566656666666666666666666666666555555555455554555554666666646664466444444444453356534336443353335332243)
           (cols := 0x67777767777777777777766776667666666677777777777777777777766666666666666666666666665666566666666656566566666666666666666666666666555556555545555555556644666466666664444444444534453343336335453353422334) (by decide +kernel)
private theorem pos201 : Admits 201 :=
  of_check (rows := 0x666666777777777777777777666666666666677777777777777777777777666666666666666666666666666666666666666666666666666666666666666666666666655555555555555555566666666666664444444444443333333333333444442333333)
           (cols := 0x777777777777777777777776666666666666777777777777777777666666666666666666666666666666666666666666666666666666666666666666666666655555555555555555544444666666666666644444444444433333366666633333333333332) (by decide +kernel)
private theorem pos202 : Admits 202 :=
  of_check (rows := 0x6677776777767777777777777666667666776777777777777777677777677666666666666666666666666665655666666665666666666666666666666666666665555655556555545555545566666466644644444444444443565543364464533342322422)
           (cols := 0x6776777776777777777777777677666766666777777777777767777677776666666666666666666666666666656666666655656666666666666666666666666655655555655554555545555464466646666644444444444446445364333665545332242232) (by decide +kernel)
private theorem pos203 : Admits 203 :=
  of_check (rows := 0x66677766777777777777777777776676666667677777777777777777777777776666666666666666666666666666666666655666666666666666666666666666665556655555555555555555555664666666464444444444444433433333345533442223323)
           (cols := 0x77777777777777777777777776766666676677777777777777777777667776666666666666666666666666666655666666666666666666666666666666666665555555555555555555544555646666664664444444444444434335566433666333333233222) (by decide +kernel)
private theorem pos204 : Admits 204 :=
  of_check (rows := 0x666667667777777777777777777767766676676677777777777777777667777767666666666666666666666666666666666566566566666666666666666666666666566555555555555544555556546664664664444444444444344366433456454452232232)
           (cols := 0x767777766777777777777777776676676667767777777777777777777766766666666666666666666666666566566566666666666666666666666666666666656555556655555555555554454664664666446444444444444453453456646666633442322322) (by decide +kernel)
private theorem pos205 : Admits 205 :=
  of_check (rows := 0x6666677766777777777777777777777776666777677777777777777777777777777766666666666666666666666666666666655666666666666666666666666666665556655555555555555555555554666644464444444444444444433334445533442222223)
           (cols := 0x7777777777777777777777777776777666677777777777777777777777667776666666666666666666666666666655666666666666666666666666666666666555555555555555555555544555644466664444444444444444434445566433666663333222222) (by decide +kernel)
private theorem pos206 : Admits 206 :=
  of_check (rows := 0x66777777766777777777777777777777776667777777777777777777777777777777776666666666666666666666666666656666666666666666666666666666655555556655555545555555555555555666444444444444444444444433345333333442322224)
           (cols := 0x77777777777777777777777777777777766677777777777777777777777667777777666666666666666666666666666665666666666666666666666666666665555555555555555455555544555555546664444444444444444444444366533333366333222242) (by decide +kernel)
private theorem pos207 : Admits 207 := reflect (k := 7) (by decide) (by decide) pos135
private theorem pos208 : Admits 208 := reflect (k := 6) (by decide) (by decide) pos7
private theorem pos209 : Admits 209 := reflect (k := 7) (by decide) (by decide) pos133
private theorem pos210 : Admits 210 := reflect (k := 7) (by decide) (by decide) pos132
private theorem pos211 : Admits 211 := reflect (k := 7) (by decide) (by decide) pos131
private theorem pos212 : Admits 212 := reflect (k := 7) (by decide) (by decide) pos130
private theorem pos213 : Admits 213 := reflect (k := 7) (by decide) (by decide) pos129
private theorem pos214 : Admits 214 := reflect (k := 7) (by decide) (by decide) pos128
private theorem pos215 : Admits 215 := reflect (k := 6) (by decide) (by decide) pos0
private theorem pos216 : Admits 216 := reflect (k := 7) (by decide) (by decide) pos126
private theorem pos217 : Admits 217 := reflect (k := 7) (by decide) (by decide) pos125
private theorem pos218 : Admits 218 := reflect (k := 7) (by decide) (by decide) pos124
private theorem pos219 : Admits 219 := reflect (k := 7) (by decide) (by decide) pos123
private theorem pos220 : Admits 220 := reflect (k := 7) (by decide) (by decide) pos122
private theorem pos221 : Admits 221 := reflect (k := 7) (by decide) (by decide) pos121
private theorem pos222 : Admits 222 := reflect (k := 7) (by decide) (by decide) pos120
private theorem pos223 : Admits 223 := reflect (k := 7) (by decide) (by decide) pos119
private theorem pos224 : Admits 224 := reflect (k := 7) (by decide) (by decide) pos118
private theorem pos225 : Admits 225 := reflect (k := 7) (by decide) (by decide) pos117
private theorem pos226 : Admits 226 := reflect (k := 7) (by decide) (by decide) pos116
private theorem pos227 : Admits 227 := reflect (k := 7) (by decide) (by decide) pos115
private theorem pos228 : Admits 228 :=
  of_check (rows := 0x777777777777777777677777776677777777777777777777777777777777777777777777777777777777777777777777777777777777777777665666666665655555555555555555565555555665555555555445555555555555555555555555555555555555534533333344533333323244)
           (cols := 0x777777777777777777777777777777777777777777777777777777777777777777777777777777777777776677777776777777777777777777656666666656655555555555555555555555555555555555555445555555555445555555455555555555555555535333333665333333623244) (by decide +kernel)
private theorem pos229 : Admits 229 :=
  of_check (rows := 0x7777777777777777777666666667666666667777777777777777777777777777777777777777777777777777677777777777777777777777777766666666666555555555555555555566666666566666666555445555555555545555555555555555555555555554444444464444444422244)
           (cols := 0x7777777777777777777777777776777777777777777777777777777777777777777777777777777766666666766666666777777777777777777766666666666555555555555555555555555555655555555555445554444444454444444455555555555555555556666666646666666622244) (by decide +kernel)
private theorem pos230 : Admits 230 := reflect (k := 7) (by decide) (by decide) pos112
private theorem pos231 : Admits 231 :=
  of_check (rows := 0x777777777777777777777776666667666666777777777777777777777777777777777777777777777777777777677777777777777777777777777777666666655555555555555555555555666666566666655555555555555555545555555555555555555555555555544444464444442222222)
           (cols := 0x777777777777777777777777777776777777777777777777777777777777777777777777777777777777666666766666677777777777777777777777666666655555555555555555555555555555655555555555555555544444454444445555555555555555555555566666646666662222222) (by decide +kernel)
private theorem pos232 : Admits 232 := reflect (k := 7) (by decide) (by decide) pos110
private theorem pos233 : Admits 233 :=
  of_check (rows := 0x77777777777777777777777776666666666677777777777777777777777776677777777777777777777777777777777776677777777777777777777777776665555555555555555555555555666666666665555555555555555555555555665555555555555555555555555444444444662222222)
           (cols := 0x77777777777777777777777776677777777777777777777777777777777776677777777777777777777777776666666666677777777777777777777777776665555555555555555555555555665555555555555555555555555444444444665555555555555555555555555666666666662222222) (by decide +kernel)
private theorem pos234 : Admits 234 :=
  of_check (rows := 0x777777777777777777777777776677777777777777777777777777777777776677777777777777777777777777777777776677777777777777777777777777655555555555555555555555555665555555555555555555555555555555555665555555555555555555555555533333333662222222)
           (cols := 0x777777777777777777777777776677777777777777777777777777777777776677777777777777777777777777777777776677777777777777777777777777655555555555555555555555555665555555555555555555555555555555555665555555555555555555555555533333333662222222) (by decide +kernel)
private theorem pos235 : Admits 235 :=
  of_check (rows := 0x7777777777777777777777777776677777777777777777777777777777777776677777777777777777777777777777777776677777777777777777777777777755555555555555555555555555665555555555555555555555555555555555665555555555555555555555555533333333662222222)
           (cols := 0x7777777777777777777777777776677777777777777777777777777777777776677777777777777777777777777777777776677777777777777777777777777755555555555555555555555555665555555555555555555555555555555555665555555555555555555555555533333333662222222) (by decide +kernel)
private theorem pos236 : Admits 236 :=
  of_check (rows := 0x77777777777777777777777777776666666666677777777777777777777777776677777777777777777777777777777777776677777777777777777777777777775555555555555555555555555666666666665555555555555555555555555665555555555555555555555555444444444662222222)
           (cols := 0x77777777777777777777777777776677777777777777777777777777777777776677777777777777777777777776666666666677777777777777777777777777775555555555555555555555555665555555555555555555555555444444444665555555555555555555555555666666666662222222) (by decide +kernel)
private theorem pos237 : Admits 237 := reflect (k := 7) (by decide) (by decide) pos105
private theorem pos238 : Admits 238 :=
  of_check (rows := 0x7777777777777777777777777777777776776667776777777777777777777777777776777777777777777777777777766777666776777777777777777777777777777755555555555555555555555555655666555655555545555555554455544455655555555555555555555533336644466642622224)
           (cols := 0x7777777777777777777777777777677666777667777777777777777777777777677777777777777777777777777677766677677777777777777777777777777777777755555555555555555555565566655566555555555455555545554445565555555555555555555555555564446664463333222242) (by decide +kernel)
private theorem pos239 : Admits 239 := reflect (k := 7) (by decide) (by decide) pos103
private theorem pos240 : Admits 240 :=
  of_check (rows := 0x777777777777777777777777777677766666666666777777777777777777777677767777776777777777777777777777777677767777776777777777777777777777777777555555555555555565556666666666655555555445555555555565556555555655555555555555553344444464446333332644)
           (cols := 0x777777777777777777777777777677777767776777777777777777777777777677777767776777777777777777777777666666666667776777777777777777777777777777555555555555555565555556555655555555555445555555544464444446555655555555555555553333366666666666332644) (by decide +kernel)
private theorem pos241 : Admits 241 :=
  of_check (rows := 0x7777777777777777777777777777677766666666766766777777777777777777677777777776777777777777777777777777667767777776777777777777777777777777777755555555555555565556666666656656655555545555555555564554555555655555555555555533444444466446442333624)
           (cols := 0x7777777777777777777777777777677777767766777777777777777777777777677777777776777777777777777777667667666666667776777777777777777777777777777755555555555555565555556556655555555555455555544544564444444555655555555555555533366466466666666233642) (by decide +kernel)
private theorem pos242 : Admits 242 := reflect (k := 7) (by decide) (by decide) pos100
private theorem pos243 : Admits 243 :=
  of_check (rows := 0x777777777777777777777777777777777776666666666666777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777555555555555555555666666666666655555555555555555555555555555555555555555553333344444444444442333332)
           (cols := 0x777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777666666666666677777777777777777777777777777777777555555555555555555555555555555555555555555544444444444445555555555555555553333366666666666662333332) (by decide +kernel)
private theorem pos244 : Admits 244 := reflect (k := 7) (by decide) (by decide) pos98
private theorem pos245 : Admits 245 :=
  of_check (rows := 0x77777777777777777777777777777766666666666666666666666666677777777777777777777777777777777777777777777777777777777777777777777777777777777777777777775555555556666666666666666666666666665555555555555555555555555555555555444444444444444444444444444)
           (cols := 0x77777777777777777777777777777777777777777777777777777777777777777777777777777777777777777776666666666666666666666666667777777777777777777777777777775555555555555555555555555555555555444444444444444444444444444555555555666666666666666666666666666) (by decide +kernel)
private theorem pos246 : Admits 246 :=
  of_check (rows := 0x777777777777777777777777777777766777666666666666666666666667777777777777777777777777777777767767777777777777777777777777777777777777777777777777777777555555556655566666666666666666666666555555555555555555555555555555556446334444444444444444444244)
           (cols := 0x777777777777777777777777777777777777777777777777777777767767777777777777777777777777777777766666666666666666666666777667777777777777777777777777777777555555555555555555555555555555556446444444444444444444455544555555556666666666666666666666623366) (by decide +kernel)
private theorem pos247 : Admits 247 :=
  of_check (rows := 0x7777777777777777777777777777777766676666666666666666666666666777777777677777777776777777777667766777777777677777777776777777777777777777777777777777777755555556665666666666666666666666666655555555565555555555655555555566446644444444464444444442644)
           (cols := 0x7777777777777777777777777777777777677777777776777777777667766777777777677777777776777777777666666666666666666666666676667777777777777777777777777777777755555555565555555555655555555566446644444444464444444445644555555566666666666666666666666662666) (by decide +kernel)
private theorem pos248 : Admits 248 :=
  of_check (rows := 0x77777777777777777777777777777777766777666666667666666666666666677777777777777777777777777776667766677777777677777777777777777777777777777777777777777777775555556655566666666566666666666666665555555545555555555555555555666446664444444464444444422244)
           (cols := 0x77777777777777777777777777777777777777777777776777777776667766677777777777777777777777777776666666666666666766666666777667777777777777777777777777777777775555555555555555555655555555666446664444444454444444455544555555666666666666666646666666622266) (by decide +kernel)
private theorem pos249 : Admits 249 :=
  of_check (rows := 0x777777777777777777777777777777777777777766666666666666666666666667777777777777777777777777766666766667777777777777777777777777777777777777777777777777777777555555555556666666666666666666666666555555555555555555555555556666636666444444444444444222224)
           (cols := 0x777777777777777777777777777777777777777777777777777777766667666667777777777777777777777777766666666666666666666666667777777777777777777777777777777777777777555555555555555555555555556666466666444444444444444555555555556666666666666666666666666222223) (by decide +kernel)
private theorem pos250 : Admits 250 :=
  of_check (rows := 0x7777777777777777777777777777777777777777776666666666666666666666667777777777777777777777777766666766666777777777777777777777777777777777777777777777777777777755555555555666666666666666666666666455555555555555555555555546666636666644444444444444222224)
           (cols := 0x7777777777777777777777777777777777777777777777777777777666667666667777777777777777777777777766666666666666666666666677777777777777777777777777777777777777777755555555555555555555555566666466666444444444444445555555555546666666666666666666666664222223) (by decide +kernel)
private theorem pos251 : Admits 251 :=
  of_check (rows := 0x77777777777777777777777777777777777776666767666666677777776667666677777776666777777766677777776666666667677776666777777766677777777777777777777777777777777777775555666656566666665555555666466664545555666655555556665555444666666666464444666633333336663)
           (cols := 0x77777777777777777777777777777777777776667777777666677776766666666677777776667777777666677777776666766677777776666666767666677777777777777777777777777777777777775555666555555566665555656666666665555555666444454566665555444666636663333333666666646466664) (by decide +kernel)
private theorem pos252 : Admits 252 :=
  of_check (rows := 0x777777777777777777777777777777777777777767777777776676666667666666776677777767777777776677777667666666666677777766777777776677777777777777777777777777777777777777555556555555555665666666566666644665555556455555555665554466466666666663333336644442223662)
           (cols := 0x777777777777777777777777777777777777776677777777667777776666666666766777776677777777767777776677666666766666676677777777767777777777777777777777777777777777777777555665555555566555555666666666656644445665555555556555554664466666636666664663333332446222) (by decide +kernel)
private theorem pos253 : Admits 253 :=
  of_check (rows := 0x7777777777777777777777777777777777777777777777777777676666667766667776677777777777777777677777667766666666677777776777777777677777777777777777777777777777777777777755555555555555565666666556666444665555555455555555565544466446666666663333333644442223362)
           (cols := 0x7777777777777777777777777777777777777776777777777677777776666666667766777776777777777777777776677766667766666676777777777777777777777777777777777777777777777777777755655555555565555555666666666556644445655555555555555544664446666336666664633333332444222) (by decide +kernel)
private theorem pos254 : Admits 254 :=
  of_check (rows := 0x77777777777777777777777777777777777777776766666666666666666777776677777777777777777777777777777777776767777777777777777777777777777777777777777777777777777777777777775656666666666666666655555664555555555555555555555555444444444646444444444444444442333334)
           (cols := 0x77777777777777777777777777777777777777777777777777777777777777767677777777777777777777777777777777776677777666666666666666667677777777777777777777777777777777777777775555555555555555555555556465555544444444444444444545444444444663333366666666666666666462) (by decide +kernel)
private theorem pos255 : Admits 255 := reflect (k := 7) (by decide) (by decide) pos87
private theorem pos256 : Admits 256 := reflect (k := 8) (by decide) (by decide) pos255
private theorem pos257 : Admits 257 := reflect (k := 7) (by decide) (by decide) pos85
private theorem pos258 : Admits 258 := reflect (k := 8) (by decide) (by decide) pos253
private theorem pos259 : Admits 259 := reflect (k := 8) (by decide) (by decide) pos252
private theorem pos260 : Admits 260 := reflect (k := 7) (by decide) (by decide) pos82
private theorem pos261 : Admits 261 := reflect (k := 8) (by decide) (by decide) pos250
private theorem pos262 : Admits 262 := reflect (k := 7) (by decide) (by decide) pos80
private theorem pos263 : Admits 263 := reflect (k := 8) (by decide) (by decide) pos248
private theorem pos264 : Admits 264 := reflect (k := 8) (by decide) (by decide) pos247
private theorem pos265 : Admits 265 := reflect (k := 8) (by decide) (by decide) pos246
private theorem pos266 : Admits 266 := reflect (k := 8) (by decide) (by decide) pos245
private theorem pos267 : Admits 267 := reflect (k := 8) (by decide) (by decide) pos244
private theorem pos268 : Admits 268 := reflect (k := 8) (by decide) (by decide) pos243
private theorem pos269 : Admits 269 := reflect (k := 8) (by decide) (by decide) pos242
private theorem pos270 : Admits 270 := reflect (k := 8) (by decide) (by decide) pos241
private theorem pos271 : Admits 271 := reflect (k := 8) (by decide) (by decide) pos240
private theorem pos272 : Admits 272 := reflect (k := 8) (by decide) (by decide) pos239
private theorem pos273 : Admits 273 := reflect (k := 8) (by decide) (by decide) pos238
private theorem pos274 : Admits 274 := reflect (k := 7) (by decide) (by decide) pos68
private theorem pos275 : Admits 275 := reflect (k := 8) (by decide) (by decide) pos236
private theorem pos276 : Admits 276 := reflect (k := 7) (by decide) (by decide) pos66
private theorem pos277 : Admits 277 := reflect (k := 8) (by decide) (by decide) pos234
private theorem pos278 : Admits 278 := reflect (k := 8) (by decide) (by decide) pos233
private theorem pos279 : Admits 279 := reflect (k := 7) (by decide) (by decide) pos63
private theorem pos280 : Admits 280 := reflect (k := 8) (by decide) (by decide) pos231
private theorem pos281 : Admits 281 := reflect (k := 8) (by decide) (by decide) pos230
private theorem pos282 : Admits 282 := reflect (k := 8) (by decide) (by decide) pos229
private theorem pos283 : Admits 283 := reflect (k := 8) (by decide) (by decide) pos228
private theorem pos284 : Admits 284 := reflect (k := 8) (by decide) (by decide) pos227
private theorem pos285 : Admits 285 := reflect (k := 8) (by decide) (by decide) pos226
private theorem pos286 : Admits 286 := reflect (k := 7) (by decide) (by decide) pos56
private theorem pos287 : Admits 287 := reflect (k := 8) (by decide) (by decide) pos224
private theorem pos288 : Admits 288 := reflect (k := 8) (by decide) (by decide) pos223
private theorem pos289 : Admits 289 := reflect (k := 8) (by decide) (by decide) pos222
private theorem pos290 : Admits 290 := reflect (k := 8) (by decide) (by decide) pos221
private theorem pos291 : Admits 291 := reflect (k := 8) (by decide) (by decide) pos220
private theorem pos292 : Admits 292 := reflect (k := 8) (by decide) (by decide) pos219
private theorem pos293 : Admits 293 := reflect (k := 8) (by decide) (by decide) pos218
private theorem pos294 : Admits 294 := reflect (k := 8) (by decide) (by decide) pos217
private theorem pos295 : Admits 295 := reflect (k := 8) (by decide) (by decide) pos216
private theorem pos296 : Admits 296 := reflect (k := 8) (by decide) (by decide) pos215
private theorem pos297 : Admits 297 := reflect (k := 8) (by decide) (by decide) pos214
private theorem pos298 : Admits 298 := reflect (k := 7) (by decide) (by decide) pos44
private theorem pos299 : Admits 299 := reflect (k := 8) (by decide) (by decide) pos212
private theorem pos300 : Admits 300 := reflect (k := 8) (by decide) (by decide) pos211
private theorem pos301 : Admits 301 := reflect (k := 8) (by decide) (by decide) pos210
private theorem pos302 : Admits 302 := reflect (k := 8) (by decide) (by decide) pos209
private theorem pos303 : Admits 303 := reflect (k := 8) (by decide) (by decide) pos208
private theorem pos304 : Admits 304 := reflect (k := 8) (by decide) (by decide) pos207
private theorem pos305 : Admits 305 := reflect (k := 7) (by decide) (by decide) pos37
private theorem pos306 : Admits 306 := reflect (k := 8) (by decide) (by decide) pos205
private theorem pos307 : Admits 307 := reflect (k := 8) (by decide) (by decide) pos204
private theorem pos308 : Admits 308 := reflect (k := 8) (by decide) (by decide) pos203
private theorem pos309 : Admits 309 := reflect (k := 8) (by decide) (by decide) pos202
private theorem pos310 : Admits 310 := reflect (k := 8) (by decide) (by decide) pos201
private theorem pos311 : Admits 311 := reflect (k := 8) (by decide) (by decide) pos200
private theorem pos312 : Admits 312 := reflect (k := 8) (by decide) (by decide) pos199
private theorem pos313 : Admits 313 := reflect (k := 8) (by decide) (by decide) pos198
private theorem pos314 : Admits 314 := reflect (k := 8) (by decide) (by decide) pos197
private theorem pos315 : Admits 315 := reflect (k := 8) (by decide) (by decide) pos196
private theorem pos316 : Admits 316 := reflect (k := 7) (by decide) (by decide) pos26
private theorem pos317 : Admits 317 := reflect (k := 8) (by decide) (by decide) pos194
private theorem pos318 : Admits 318 := reflect (k := 8) (by decide) (by decide) pos193
private theorem pos319 : Admits 319 := reflect (k := 8) (by decide) (by decide) pos192
private theorem pos320 : Admits 320 := reflect (k := 8) (by decide) (by decide) pos191
private theorem pos321 : Admits 321 := reflect (k := 8) (by decide) (by decide) pos190
private theorem pos322 : Admits 322 := reflect (k := 8) (by decide) (by decide) pos189
private theorem pos323 : Admits 323 := reflect (k := 7) (by decide) (by decide) pos19
private theorem pos324 : Admits 324 := reflect (k := 8) (by decide) (by decide) pos187
private theorem pos325 : Admits 325 := reflect (k := 8) (by decide) (by decide) pos186
private theorem pos326 : Admits 326 := reflect (k := 8) (by decide) (by decide) pos185
private theorem pos327 : Admits 327 := reflect (k := 8) (by decide) (by decide) pos184
private theorem pos328 : Admits 328 := reflect (k := 8) (by decide) (by decide) pos183
private theorem pos329 : Admits 329 := reflect (k := 8) (by decide) (by decide) pos182
private theorem pos330 : Admits 330 := reflect (k := 8) (by decide) (by decide) pos181
private theorem pos331 : Admits 331 := reflect (k := 8) (by decide) (by decide) pos180
private theorem pos332 : Admits 332 := reflect (k := 8) (by decide) (by decide) pos179
private theorem pos333 : Admits 333 := reflect (k := 8) (by decide) (by decide) pos178
private theorem pos334 : Admits 334 := reflect (k := 8) (by decide) (by decide) pos177
private theorem pos335 : Admits 335 := reflect (k := 7) (by decide) (by decide) pos7
private theorem pos336 : Admits 336 := reflect (k := 8) (by decide) (by decide) pos175
private theorem pos337 : Admits 337 := reflect (k := 8) (by decide) (by decide) pos174
private theorem pos338 : Admits 338 := reflect (k := 8) (by decide) (by decide) pos173
private theorem pos339 : Admits 339 :=
  of_check (rows := 0x788888887878887888888888888887888888888877888888888888888888888888888887888888888888888888888888888888888888888887888888888888888888888888888888888888888887878888888787776666666767666766666666666666766666666667766666656666666666666666666665766666666666666666666666666666666666666666764666666646444444554444445444444444433433737334542274223)
           (cols := 0x878888888787888888888888888888888888888888888888888887888888888888888888888888888888888888888887888888888888888888888888888887788888888887888888888888887888787888888877767666666676766666666666666666666666666666666666666666756666666666666666666665666666556666666666766666666666666466646466666664774444444444744444435444444743373733433227522) (by decide +kernel)
private theorem pos340 : Admits 340 := reflect (k := 8) (by decide) (by decide) pos171
private theorem pos341 : Admits 341 :=
  of_check (rows := 0x78888878888778888888788888888888887787778888888888888778888888888888888888888888888888888888888888887888888888888888888888888888888888888888887888888888888868868888888778866667666677666666666666666666666776777666666665666677666566666666666666666666666666666666666666666766666666666666666666666655655544444444544745546334444337347333333377222)
           (cols := 0x88778888888788788888888888887888888888888888888888888888888888888888887888888888888888888888888888888888888888888888778888888888888777877888888888888868888888778888788888677666666666666666666666666766666666666666666666666666666666666666666766655666656666666655565566666666666666666666677666646666444477747746446444444447333333377353372223375) (by decide +kernel)
private theorem pos342 : Admits 342 := reflect (k := 7) (by decide) (by decide) pos0
private theorem pos343 : Admits 343 :=
  of_check (rows := 0x8888887878887788787877888888888888888777788888788888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888887888878788788888888767666776676767766666666666666677776666676666666665665666666665666666656666666666666666666666666666666666666466664646646645555444445444444444533544444744547374475424244)
           (cols := 0x8888888878878788887888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888878888877778888888888888887787878877888787888888667667676666766666666666666666666666666666666666665666666656666666656656666666665666665555666666666666666446464664466646447444447777444444444544444775747347745475724233) (by decide +kernel)
private theorem pos344 : Admits 344 :=
  of_check (rows := 0x88888888878887788887887888888888888888778788888788888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888887888878788788888888867666776666766766666666666666677676666676666666665665666666665666666656666666666666666666666666666666666666466664646646445545444445444444444534544444744547374475224224)
           (cols := 0x88888888878878788887888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888878888878778888888888888887887888877888788888888867667676666766666666666666666666666666666666666665666666656666666656656666666665666665655666666666666666466466664466646447444447477444444444544444745744347745475224223) (by decide +kernel)
private theorem pos345 : Admits 345 :=
  of_check (rows := 0x888888888878787888888788888888878888878878888777787888888888888788888888878888888888888878888888888888888888888888878888888888888878888788888888888888888888878888868888888888888886676766666676666666667666667667666677776766665566666676566666667666556666666667666656666666666666666666667666666666664547544475655454444554434445357343437434355223332)
           (cols := 0x888888888888888788888788888888888888888888878888788888888888888788888888888888888888888888788888888888888788888888878888888888887877778888788788888788888888878888887878688888888886666666666676666666666666666666667666676666666665566676666666565666666556666565575666656656666676666666667666666464664747777544474476444474553334447343453737372355223) (by decide +kernel)
private theorem pos346 : Admits 346 :=
  of_check (rows := 0x8888888888887788888888888887878787877887888787777877787888888888888888878888878888888888888888888888888888888888888888888888888888888886888888886888888886888886788878788688888868888776666666666666767676767766766676777767776756656666655666667666667666665666666666666666666666666666666666656665656654454445755554555755445443745533773547473572332537)
           (cols := 0x8888788888878878788877888887888888887888888887888888888888888888888888888888888888888888888888888888888788888788888888888888887877787777878887887787878787888888888888877888888888888667676667666666666666666666666666666666666656666656666656666655666665665565556555565666566576565676566666666666664747776777747644744775767473763344434465537733562532) (by decide +kernel)
private theorem pos347 : Admits 347 :=
  of_check (rows := 0x88888887888888788888888887877887888888887777877777778788888888888887888887888888888888888888878888888888888888888887888888888888888888878888888888888888888867887788888788888888788888876666666666767766766666666777767777777676666655656666766666766666666656666666667666666666666666666666766556666646444455557555555445444445535437753774344473333235273)
           (cols := 0x88888878888888878888877887788888888888888888888788888888888888888887888888888888888888888788888888888888888887888887888888888888878777777787777888888887887787888888888878888887888888867666667766766666666666666666666676666666665666666666766666566665655666665675555556555566666666766556766666666664447477777774777744444544736773733334444347535523723) (by decide +kernel)
private theorem pos348 : Admits 348 :=
  of_check (rows := 0x888888888888888878787888888878888888878778877887777778888878888888888888888888888888888888788888888888888888888888888888888888888888788888888888888888888888866867888888888888888888888887676666666667666666667677667766777767665667566556666666666666666666665666676666666666666666666666666666566666664545574554454554544564554455447737734444433433222526)
           (cols := 0x888888888888888888888887787788888888888888888888888878888888888888888888888888888888888888888878888888888888888888888888888888788888767777887788778788888888788888886878788888888888888886666666766666666666666666666666666667666656666666666666666666665566556656656557566556655656666666656666666664674444477777744774477475446466474433433747473553252225) (by decide +kernel)
private theorem pos349 : Admits 349 :=
  of_check (rows := 0x8888888888888888888787878888888887888777788887777787888888888788888888888887888778888887888887888888888888888888888887878888888887887787888886878886887888888867878888888888888888888888888676667666666666766677776666777776766666656576665666666666765677666666766556766666665666666566666666767666666644755774745555747444765755443537747344444435532343322)
           (cols := 0x8888888888888888888888888787788888887887888787888887877887888888888787888888888888888888888887888887888888778887888888888888878888888887877777888877778887888888888786878888888888888888888666666676766666666766666676666666767766766666655676766666666656665565666666765555766665577666766666666646667654444445747777744557777444746335343473767445362253532) (by decide +kernel)
private theorem pos350 : Admits 350 :=
  of_check (rows := 0x88888888788888888888887888878878888887788788887877787788788888888888888888888888888888887888887788888888888888888888888888888888887887887788886888887887888888868877888888888888888888888888866766667667666666776676666767776776676666566656566666666666666666666766566776666666666566566666666664566666455745746774555744445744754445457347744334434334232342)
           (cols := 0x88888888888888888888888887788788888887887888887888877887887888888888888888888888888888888888877888887888888888888888888888888888888878877877787888878877888888788788887888888888888868888888866666776666666666766766666666667766766766666666666666666666565666566665667765556766665665566666656646666466454457447747774744457447744446373473343743354562352427) (by decide +kernel)
private theorem pos351 : Admits 351 :=
  of_check (rows := 0x888888888888888788888878787888887888787777887778778887877888887878888888888888888888888878888888888888888888888888888888888888888888877886888788888877688888888788886788888888888888868888888887666766666766666777766777677666667766665757566666666666666666666667665566666656666665566666666656666656664455557755745576444557776555554373446773334443432333567)
           (cols := 0x888888888788888888888888877888878888888877788888878887887788888888888888888888888888888888888888888888788888888888888888888888787888887786888778777887777868887888887868788888868888888888888886667666667666666666776666667666666776656666666666666666666666555556666556666655675566555566666566666566674744455776744577477755777767444733343737673334457535362) (by decide +kernel)
private theorem pos352 : Admits 352 := reflect (k := 8) (by decide) (by decide) pos159
private theorem pos353 : Admits 353 :=
  of_check (rows := 0x88888888888888888888888888788877888888877787777887787778877788787888888878888888888888888888888888888888888888888878888888888888888888888888886888888888888878878888888886888888888888888888888888876667766666667776777766776777667775575766666657566666666666665666666666666666666666666667665666666666444555455554455755544555555557447345354433744343444533334)
           (cols := 0x88888888888888888888888887888888888788788888888888887888888888888888888888888888788888888888888888888888888888888888888888788888887878877788777877887777877788888887788878888888888888888888888888866666666676676666666666666666666666666656666666666666575666666555555556655565566555565556666666476665444747447774477747744777767775443333774437354533444365355) (by decide +kernel)
private theorem pos354 : Admits 354 :=
  of_check (rows := 0x888888888888888888888888888888888888877777877877887878877787888788888788888888888888878878887878888888878887888888888888888888878888887878888878878887866788788888888788868888888888888888888888888886666666667777767767766767667776765676556675566666666656667667666767666665667666766656656666666646667555554757454447447555757775475445554473347445343444522332)
           (cols := 0x888888888888888888888888888788878888888878877787888788788888787888888788888888888888888887888788888888787888788788888888888888878888878887877788787887787787777788888888888888888888888888888888888886667666666667667666766676676666676766656676665666666666555665765676565556676766576576555556666666667444547544747774475744774776777773344544434366455332552245) (by decide +kernel)
private theorem pos355 : Admits 355 := reflect (k := 8) (by decide) (by decide) pos156
private theorem pos356 : Admits 356 := reflect (k := 8) (by decide) (by decide) pos155
private theorem pos357 : Admits 357 :=
  of_check (rows := 0x888888888888888888888888888888888888877787787777787787777877778788888778778888888888888887888888888888888888888888888888888888888887888888888888888878888887878888888887888888888888888888888888888888888886667776776777776776677767777676565677677566666566666666766666666666666665666666565666666666464555755455545455445557555545757545545553733354334344364334423)
           (cols := 0x888888888888888888888888888888888887888888888787888888788888888888888887888888888888888888888888888888888888888887888888888888888778778888878777787776877877777877877788888888888888888888888888888888888886766666666676766666676666666666666666766666666566666555655656565655556555665565755565565556664477477445457477775777747747777747737773344354343354333235454) (by decide +kernel)
private theorem pos358 : Admits 358 :=
  of_check (rows := 0x8888888888888888888888888888888888887778888878787888888777888887788888888888788888888888888888888888888888888888888888888888888888888888788888888888878888886888888888887888888888888888888888888888888888888777666667676766666677766666776656666665676666666666666666656666666666665666666666666666666445544444575454444445557444455745444444535744443344444444444344)
           (cols := 0x8888888888888888888888888888888888887888888888887888888788888888888878888888888888888888888888888888888888888888888888888888888878888888888877888887778888887878788888777888888888888888888888888888888888888766666666666666666676666666666667666666666666666665656666665665566666555666666565656666655447444444444447744445777444444747574444377744444464335444443544) (by decide +kernel)
private theorem pos359 : Admits 359 := reflect (k := 8) (by decide) (by decide) pos152
private theorem pos360 : Admits 360 := reflect (k := 8) (by decide) (by decide) pos151
private theorem pos361 : Admits 361 := reflect (k := 8) (by decide) (by decide) pos150
private theorem pos362 : Admits 362 := reflect (k := 8) (by decide) (by decide) pos149
private theorem pos363 : Admits 363 :=
  of_check (rows := 0x888888888888888888888888888887788888888888888887878877877878777778887888887888888888888888888887878888888888888888888888888888888788888887878788888878888888888868888868886888888888888888888888888888888888888888888886667667767767677777666766556765666666666656666666767656666665666666666666666666665575555555747574544457545555566457455457534733364443444443444334333)
           (cols := 0x888888888888888888888888888888888888888888887888788888788888888888788888878787888888878888888888888888888888888888888787888888888888888888887888887888777778787787788786888888888888888866888888888888888888888888888886666666666666666666676666667676766666667666666666656565566566655555656576756656665555555455444744444744477777475774774574733363346534446437745333553) (by decide +kernel)
private theorem pos364 : Admits 364 := reflect (k := 8) (by decide) (by decide) pos147

/-- Robert Israel's 2018 conjecture on OEIS A006063. -/
theorem israel (n : ℕ) (hn : 173 ≤ n) : Admits n := by
  apply of_bases _ n hn
  intro m low high
  by_cases h269 : m < 269
  ·
    by_cases h221 : m < 221
    ·
      by_cases h197 : m < 197
      ·
        by_cases h185 : m < 185
        ·
          by_cases h179 : m < 179
          ·
            by_cases h176 : m < 176
            ·
              by_cases h174 : m < 174
              ·
                obtain rfl : m = 173 := by omega
                exact pos173
              ·
                by_cases h175 : m < 175
                ·
                  obtain rfl : m = 174 := by omega
                  exact pos174
                ·
                  obtain rfl : m = 175 := by omega
                  exact pos175
            ·
              by_cases h177 : m < 177
              ·
                obtain rfl : m = 176 := by omega
                exact pos176
              ·
                by_cases h178 : m < 178
                ·
                  obtain rfl : m = 177 := by omega
                  exact pos177
                ·
                  obtain rfl : m = 178 := by omega
                  exact pos178
          ·
            by_cases h182 : m < 182
            ·
              by_cases h180 : m < 180
              ·
                obtain rfl : m = 179 := by omega
                exact pos179
              ·
                by_cases h181 : m < 181
                ·
                  obtain rfl : m = 180 := by omega
                  exact pos180
                ·
                  obtain rfl : m = 181 := by omega
                  exact pos181
            ·
              by_cases h183 : m < 183
              ·
                obtain rfl : m = 182 := by omega
                exact pos182
              ·
                by_cases h184 : m < 184
                ·
                  obtain rfl : m = 183 := by omega
                  exact pos183
                ·
                  obtain rfl : m = 184 := by omega
                  exact pos184
        ·
          by_cases h191 : m < 191
          ·
            by_cases h188 : m < 188
            ·
              by_cases h186 : m < 186
              ·
                obtain rfl : m = 185 := by omega
                exact pos185
              ·
                by_cases h187 : m < 187
                ·
                  obtain rfl : m = 186 := by omega
                  exact pos186
                ·
                  obtain rfl : m = 187 := by omega
                  exact pos187
            ·
              by_cases h189 : m < 189
              ·
                obtain rfl : m = 188 := by omega
                exact pos188
              ·
                by_cases h190 : m < 190
                ·
                  obtain rfl : m = 189 := by omega
                  exact pos189
                ·
                  obtain rfl : m = 190 := by omega
                  exact pos190
          ·
            by_cases h194 : m < 194
            ·
              by_cases h192 : m < 192
              ·
                obtain rfl : m = 191 := by omega
                exact pos191
              ·
                by_cases h193 : m < 193
                ·
                  obtain rfl : m = 192 := by omega
                  exact pos192
                ·
                  obtain rfl : m = 193 := by omega
                  exact pos193
            ·
              by_cases h195 : m < 195
              ·
                obtain rfl : m = 194 := by omega
                exact pos194
              ·
                by_cases h196 : m < 196
                ·
                  obtain rfl : m = 195 := by omega
                  exact pos195
                ·
                  obtain rfl : m = 196 := by omega
                  exact pos196
      ·
        by_cases h209 : m < 209
        ·
          by_cases h203 : m < 203
          ·
            by_cases h200 : m < 200
            ·
              by_cases h198 : m < 198
              ·
                obtain rfl : m = 197 := by omega
                exact pos197
              ·
                by_cases h199 : m < 199
                ·
                  obtain rfl : m = 198 := by omega
                  exact pos198
                ·
                  obtain rfl : m = 199 := by omega
                  exact pos199
            ·
              by_cases h201 : m < 201
              ·
                obtain rfl : m = 200 := by omega
                exact pos200
              ·
                by_cases h202 : m < 202
                ·
                  obtain rfl : m = 201 := by omega
                  exact pos201
                ·
                  obtain rfl : m = 202 := by omega
                  exact pos202
          ·
            by_cases h206 : m < 206
            ·
              by_cases h204 : m < 204
              ·
                obtain rfl : m = 203 := by omega
                exact pos203
              ·
                by_cases h205 : m < 205
                ·
                  obtain rfl : m = 204 := by omega
                  exact pos204
                ·
                  obtain rfl : m = 205 := by omega
                  exact pos205
            ·
              by_cases h207 : m < 207
              ·
                obtain rfl : m = 206 := by omega
                exact pos206
              ·
                by_cases h208 : m < 208
                ·
                  obtain rfl : m = 207 := by omega
                  exact pos207
                ·
                  obtain rfl : m = 208 := by omega
                  exact pos208
        ·
          by_cases h215 : m < 215
          ·
            by_cases h212 : m < 212
            ·
              by_cases h210 : m < 210
              ·
                obtain rfl : m = 209 := by omega
                exact pos209
              ·
                by_cases h211 : m < 211
                ·
                  obtain rfl : m = 210 := by omega
                  exact pos210
                ·
                  obtain rfl : m = 211 := by omega
                  exact pos211
            ·
              by_cases h213 : m < 213
              ·
                obtain rfl : m = 212 := by omega
                exact pos212
              ·
                by_cases h214 : m < 214
                ·
                  obtain rfl : m = 213 := by omega
                  exact pos213
                ·
                  obtain rfl : m = 214 := by omega
                  exact pos214
          ·
            by_cases h218 : m < 218
            ·
              by_cases h216 : m < 216
              ·
                obtain rfl : m = 215 := by omega
                exact pos215
              ·
                by_cases h217 : m < 217
                ·
                  obtain rfl : m = 216 := by omega
                  exact pos216
                ·
                  obtain rfl : m = 217 := by omega
                  exact pos217
            ·
              by_cases h219 : m < 219
              ·
                obtain rfl : m = 218 := by omega
                exact pos218
              ·
                by_cases h220 : m < 220
                ·
                  obtain rfl : m = 219 := by omega
                  exact pos219
                ·
                  obtain rfl : m = 220 := by omega
                  exact pos220
    ·
      by_cases h245 : m < 245
      ·
        by_cases h233 : m < 233
        ·
          by_cases h227 : m < 227
          ·
            by_cases h224 : m < 224
            ·
              by_cases h222 : m < 222
              ·
                obtain rfl : m = 221 := by omega
                exact pos221
              ·
                by_cases h223 : m < 223
                ·
                  obtain rfl : m = 222 := by omega
                  exact pos222
                ·
                  obtain rfl : m = 223 := by omega
                  exact pos223
            ·
              by_cases h225 : m < 225
              ·
                obtain rfl : m = 224 := by omega
                exact pos224
              ·
                by_cases h226 : m < 226
                ·
                  obtain rfl : m = 225 := by omega
                  exact pos225
                ·
                  obtain rfl : m = 226 := by omega
                  exact pos226
          ·
            by_cases h230 : m < 230
            ·
              by_cases h228 : m < 228
              ·
                obtain rfl : m = 227 := by omega
                exact pos227
              ·
                by_cases h229 : m < 229
                ·
                  obtain rfl : m = 228 := by omega
                  exact pos228
                ·
                  obtain rfl : m = 229 := by omega
                  exact pos229
            ·
              by_cases h231 : m < 231
              ·
                obtain rfl : m = 230 := by omega
                exact pos230
              ·
                by_cases h232 : m < 232
                ·
                  obtain rfl : m = 231 := by omega
                  exact pos231
                ·
                  obtain rfl : m = 232 := by omega
                  exact pos232
        ·
          by_cases h239 : m < 239
          ·
            by_cases h236 : m < 236
            ·
              by_cases h234 : m < 234
              ·
                obtain rfl : m = 233 := by omega
                exact pos233
              ·
                by_cases h235 : m < 235
                ·
                  obtain rfl : m = 234 := by omega
                  exact pos234
                ·
                  obtain rfl : m = 235 := by omega
                  exact pos235
            ·
              by_cases h237 : m < 237
              ·
                obtain rfl : m = 236 := by omega
                exact pos236
              ·
                by_cases h238 : m < 238
                ·
                  obtain rfl : m = 237 := by omega
                  exact pos237
                ·
                  obtain rfl : m = 238 := by omega
                  exact pos238
          ·
            by_cases h242 : m < 242
            ·
              by_cases h240 : m < 240
              ·
                obtain rfl : m = 239 := by omega
                exact pos239
              ·
                by_cases h241 : m < 241
                ·
                  obtain rfl : m = 240 := by omega
                  exact pos240
                ·
                  obtain rfl : m = 241 := by omega
                  exact pos241
            ·
              by_cases h243 : m < 243
              ·
                obtain rfl : m = 242 := by omega
                exact pos242
              ·
                by_cases h244 : m < 244
                ·
                  obtain rfl : m = 243 := by omega
                  exact pos243
                ·
                  obtain rfl : m = 244 := by omega
                  exact pos244
      ·
        by_cases h257 : m < 257
        ·
          by_cases h251 : m < 251
          ·
            by_cases h248 : m < 248
            ·
              by_cases h246 : m < 246
              ·
                obtain rfl : m = 245 := by omega
                exact pos245
              ·
                by_cases h247 : m < 247
                ·
                  obtain rfl : m = 246 := by omega
                  exact pos246
                ·
                  obtain rfl : m = 247 := by omega
                  exact pos247
            ·
              by_cases h249 : m < 249
              ·
                obtain rfl : m = 248 := by omega
                exact pos248
              ·
                by_cases h250 : m < 250
                ·
                  obtain rfl : m = 249 := by omega
                  exact pos249
                ·
                  obtain rfl : m = 250 := by omega
                  exact pos250
          ·
            by_cases h254 : m < 254
            ·
              by_cases h252 : m < 252
              ·
                obtain rfl : m = 251 := by omega
                exact pos251
              ·
                by_cases h253 : m < 253
                ·
                  obtain rfl : m = 252 := by omega
                  exact pos252
                ·
                  obtain rfl : m = 253 := by omega
                  exact pos253
            ·
              by_cases h255 : m < 255
              ·
                obtain rfl : m = 254 := by omega
                exact pos254
              ·
                by_cases h256 : m < 256
                ·
                  obtain rfl : m = 255 := by omega
                  exact pos255
                ·
                  obtain rfl : m = 256 := by omega
                  exact pos256
        ·
          by_cases h263 : m < 263
          ·
            by_cases h260 : m < 260
            ·
              by_cases h258 : m < 258
              ·
                obtain rfl : m = 257 := by omega
                exact pos257
              ·
                by_cases h259 : m < 259
                ·
                  obtain rfl : m = 258 := by omega
                  exact pos258
                ·
                  obtain rfl : m = 259 := by omega
                  exact pos259
            ·
              by_cases h261 : m < 261
              ·
                obtain rfl : m = 260 := by omega
                exact pos260
              ·
                by_cases h262 : m < 262
                ·
                  obtain rfl : m = 261 := by omega
                  exact pos261
                ·
                  obtain rfl : m = 262 := by omega
                  exact pos262
          ·
            by_cases h266 : m < 266
            ·
              by_cases h264 : m < 264
              ·
                obtain rfl : m = 263 := by omega
                exact pos263
              ·
                by_cases h265 : m < 265
                ·
                  obtain rfl : m = 264 := by omega
                  exact pos264
                ·
                  obtain rfl : m = 265 := by omega
                  exact pos265
            ·
              by_cases h267 : m < 267
              ·
                obtain rfl : m = 266 := by omega
                exact pos266
              ·
                by_cases h268 : m < 268
                ·
                  obtain rfl : m = 267 := by omega
                  exact pos267
                ·
                  obtain rfl : m = 268 := by omega
                  exact pos268
  ·
    by_cases h317 : m < 317
    ·
      by_cases h293 : m < 293
      ·
        by_cases h281 : m < 281
        ·
          by_cases h275 : m < 275
          ·
            by_cases h272 : m < 272
            ·
              by_cases h270 : m < 270
              ·
                obtain rfl : m = 269 := by omega
                exact pos269
              ·
                by_cases h271 : m < 271
                ·
                  obtain rfl : m = 270 := by omega
                  exact pos270
                ·
                  obtain rfl : m = 271 := by omega
                  exact pos271
            ·
              by_cases h273 : m < 273
              ·
                obtain rfl : m = 272 := by omega
                exact pos272
              ·
                by_cases h274 : m < 274
                ·
                  obtain rfl : m = 273 := by omega
                  exact pos273
                ·
                  obtain rfl : m = 274 := by omega
                  exact pos274
          ·
            by_cases h278 : m < 278
            ·
              by_cases h276 : m < 276
              ·
                obtain rfl : m = 275 := by omega
                exact pos275
              ·
                by_cases h277 : m < 277
                ·
                  obtain rfl : m = 276 := by omega
                  exact pos276
                ·
                  obtain rfl : m = 277 := by omega
                  exact pos277
            ·
              by_cases h279 : m < 279
              ·
                obtain rfl : m = 278 := by omega
                exact pos278
              ·
                by_cases h280 : m < 280
                ·
                  obtain rfl : m = 279 := by omega
                  exact pos279
                ·
                  obtain rfl : m = 280 := by omega
                  exact pos280
        ·
          by_cases h287 : m < 287
          ·
            by_cases h284 : m < 284
            ·
              by_cases h282 : m < 282
              ·
                obtain rfl : m = 281 := by omega
                exact pos281
              ·
                by_cases h283 : m < 283
                ·
                  obtain rfl : m = 282 := by omega
                  exact pos282
                ·
                  obtain rfl : m = 283 := by omega
                  exact pos283
            ·
              by_cases h285 : m < 285
              ·
                obtain rfl : m = 284 := by omega
                exact pos284
              ·
                by_cases h286 : m < 286
                ·
                  obtain rfl : m = 285 := by omega
                  exact pos285
                ·
                  obtain rfl : m = 286 := by omega
                  exact pos286
          ·
            by_cases h290 : m < 290
            ·
              by_cases h288 : m < 288
              ·
                obtain rfl : m = 287 := by omega
                exact pos287
              ·
                by_cases h289 : m < 289
                ·
                  obtain rfl : m = 288 := by omega
                  exact pos288
                ·
                  obtain rfl : m = 289 := by omega
                  exact pos289
            ·
              by_cases h291 : m < 291
              ·
                obtain rfl : m = 290 := by omega
                exact pos290
              ·
                by_cases h292 : m < 292
                ·
                  obtain rfl : m = 291 := by omega
                  exact pos291
                ·
                  obtain rfl : m = 292 := by omega
                  exact pos292
      ·
        by_cases h305 : m < 305
        ·
          by_cases h299 : m < 299
          ·
            by_cases h296 : m < 296
            ·
              by_cases h294 : m < 294
              ·
                obtain rfl : m = 293 := by omega
                exact pos293
              ·
                by_cases h295 : m < 295
                ·
                  obtain rfl : m = 294 := by omega
                  exact pos294
                ·
                  obtain rfl : m = 295 := by omega
                  exact pos295
            ·
              by_cases h297 : m < 297
              ·
                obtain rfl : m = 296 := by omega
                exact pos296
              ·
                by_cases h298 : m < 298
                ·
                  obtain rfl : m = 297 := by omega
                  exact pos297
                ·
                  obtain rfl : m = 298 := by omega
                  exact pos298
          ·
            by_cases h302 : m < 302
            ·
              by_cases h300 : m < 300
              ·
                obtain rfl : m = 299 := by omega
                exact pos299
              ·
                by_cases h301 : m < 301
                ·
                  obtain rfl : m = 300 := by omega
                  exact pos300
                ·
                  obtain rfl : m = 301 := by omega
                  exact pos301
            ·
              by_cases h303 : m < 303
              ·
                obtain rfl : m = 302 := by omega
                exact pos302
              ·
                by_cases h304 : m < 304
                ·
                  obtain rfl : m = 303 := by omega
                  exact pos303
                ·
                  obtain rfl : m = 304 := by omega
                  exact pos304
        ·
          by_cases h311 : m < 311
          ·
            by_cases h308 : m < 308
            ·
              by_cases h306 : m < 306
              ·
                obtain rfl : m = 305 := by omega
                exact pos305
              ·
                by_cases h307 : m < 307
                ·
                  obtain rfl : m = 306 := by omega
                  exact pos306
                ·
                  obtain rfl : m = 307 := by omega
                  exact pos307
            ·
              by_cases h309 : m < 309
              ·
                obtain rfl : m = 308 := by omega
                exact pos308
              ·
                by_cases h310 : m < 310
                ·
                  obtain rfl : m = 309 := by omega
                  exact pos309
                ·
                  obtain rfl : m = 310 := by omega
                  exact pos310
          ·
            by_cases h314 : m < 314
            ·
              by_cases h312 : m < 312
              ·
                obtain rfl : m = 311 := by omega
                exact pos311
              ·
                by_cases h313 : m < 313
                ·
                  obtain rfl : m = 312 := by omega
                  exact pos312
                ·
                  obtain rfl : m = 313 := by omega
                  exact pos313
            ·
              by_cases h315 : m < 315
              ·
                obtain rfl : m = 314 := by omega
                exact pos314
              ·
                by_cases h316 : m < 316
                ·
                  obtain rfl : m = 315 := by omega
                  exact pos315
                ·
                  obtain rfl : m = 316 := by omega
                  exact pos316
    ·
      by_cases h341 : m < 341
      ·
        by_cases h329 : m < 329
        ·
          by_cases h323 : m < 323
          ·
            by_cases h320 : m < 320
            ·
              by_cases h318 : m < 318
              ·
                obtain rfl : m = 317 := by omega
                exact pos317
              ·
                by_cases h319 : m < 319
                ·
                  obtain rfl : m = 318 := by omega
                  exact pos318
                ·
                  obtain rfl : m = 319 := by omega
                  exact pos319
            ·
              by_cases h321 : m < 321
              ·
                obtain rfl : m = 320 := by omega
                exact pos320
              ·
                by_cases h322 : m < 322
                ·
                  obtain rfl : m = 321 := by omega
                  exact pos321
                ·
                  obtain rfl : m = 322 := by omega
                  exact pos322
          ·
            by_cases h326 : m < 326
            ·
              by_cases h324 : m < 324
              ·
                obtain rfl : m = 323 := by omega
                exact pos323
              ·
                by_cases h325 : m < 325
                ·
                  obtain rfl : m = 324 := by omega
                  exact pos324
                ·
                  obtain rfl : m = 325 := by omega
                  exact pos325
            ·
              by_cases h327 : m < 327
              ·
                obtain rfl : m = 326 := by omega
                exact pos326
              ·
                by_cases h328 : m < 328
                ·
                  obtain rfl : m = 327 := by omega
                  exact pos327
                ·
                  obtain rfl : m = 328 := by omega
                  exact pos328
        ·
          by_cases h335 : m < 335
          ·
            by_cases h332 : m < 332
            ·
              by_cases h330 : m < 330
              ·
                obtain rfl : m = 329 := by omega
                exact pos329
              ·
                by_cases h331 : m < 331
                ·
                  obtain rfl : m = 330 := by omega
                  exact pos330
                ·
                  obtain rfl : m = 331 := by omega
                  exact pos331
            ·
              by_cases h333 : m < 333
              ·
                obtain rfl : m = 332 := by omega
                exact pos332
              ·
                by_cases h334 : m < 334
                ·
                  obtain rfl : m = 333 := by omega
                  exact pos333
                ·
                  obtain rfl : m = 334 := by omega
                  exact pos334
          ·
            by_cases h338 : m < 338
            ·
              by_cases h336 : m < 336
              ·
                obtain rfl : m = 335 := by omega
                exact pos335
              ·
                by_cases h337 : m < 337
                ·
                  obtain rfl : m = 336 := by omega
                  exact pos336
                ·
                  obtain rfl : m = 337 := by omega
                  exact pos337
            ·
              by_cases h339 : m < 339
              ·
                obtain rfl : m = 338 := by omega
                exact pos338
              ·
                by_cases h340 : m < 340
                ·
                  obtain rfl : m = 339 := by omega
                  exact pos339
                ·
                  obtain rfl : m = 340 := by omega
                  exact pos340
      ·
        by_cases h353 : m < 353
        ·
          by_cases h347 : m < 347
          ·
            by_cases h344 : m < 344
            ·
              by_cases h342 : m < 342
              ·
                obtain rfl : m = 341 := by omega
                exact pos341
              ·
                by_cases h343 : m < 343
                ·
                  obtain rfl : m = 342 := by omega
                  exact pos342
                ·
                  obtain rfl : m = 343 := by omega
                  exact pos343
            ·
              by_cases h345 : m < 345
              ·
                obtain rfl : m = 344 := by omega
                exact pos344
              ·
                by_cases h346 : m < 346
                ·
                  obtain rfl : m = 345 := by omega
                  exact pos345
                ·
                  obtain rfl : m = 346 := by omega
                  exact pos346
          ·
            by_cases h350 : m < 350
            ·
              by_cases h348 : m < 348
              ·
                obtain rfl : m = 347 := by omega
                exact pos347
              ·
                by_cases h349 : m < 349
                ·
                  obtain rfl : m = 348 := by omega
                  exact pos348
                ·
                  obtain rfl : m = 349 := by omega
                  exact pos349
            ·
              by_cases h351 : m < 351
              ·
                obtain rfl : m = 350 := by omega
                exact pos350
              ·
                by_cases h352 : m < 352
                ·
                  obtain rfl : m = 351 := by omega
                  exact pos351
                ·
                  obtain rfl : m = 352 := by omega
                  exact pos352
        ·
          by_cases h359 : m < 359
          ·
            by_cases h356 : m < 356
            ·
              by_cases h354 : m < 354
              ·
                obtain rfl : m = 353 := by omega
                exact pos353
              ·
                by_cases h355 : m < 355
                ·
                  obtain rfl : m = 354 := by omega
                  exact pos354
                ·
                  obtain rfl : m = 355 := by omega
                  exact pos355
            ·
              by_cases h357 : m < 357
              ·
                obtain rfl : m = 356 := by omega
                exact pos356
              ·
                by_cases h358 : m < 358
                ·
                  obtain rfl : m = 357 := by omega
                  exact pos357
                ·
                  obtain rfl : m = 358 := by omega
                  exact pos358
          ·
            by_cases h362 : m < 362
            ·
              by_cases h360 : m < 360
              ·
                obtain rfl : m = 359 := by omega
                exact pos359
              ·
                by_cases h361 : m < 361
                ·
                  obtain rfl : m = 360 := by omega
                  exact pos360
                ·
                  obtain rfl : m = 361 := by omega
                  exact pos361
            ·
              by_cases h363 : m < 363
              ·
                obtain rfl : m = 362 := by omega
                exact pos362
              ·
                by_cases h364 : m < 364
                ·
                  obtain rfl : m = 363 := by omega
                  exact pos363
                ·
                  obtain rfl : m = 364 := by omega
                  exact pos364

/-- All positive admitted orders smaller than 173. -/
def earlyOrders : Finset ℕ := ([7, 19, 26, 37, 44, 56, 63, 66, 68, 80, 82, 85, 87, 98, 100, 103, 105, 110, 112, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 135, 147, 149, 150, 151, 152, 155, 156, 159, 171] : List ℕ).toFinset

theorem prefix_card : earlyOrders.card = 48 := by decide +kernel
theorem sharp : ¬ Admits 172 := neg172

theorem classify_small (m : ℕ) (h : m < 173) :
    Admits m ↔ m = 0 ∨ m ∈ earlyOrders := by
  by_cases h86 : m < 86
  ·
    by_cases h43 : m < 43
    ·
      by_cases h21 : m < 21
      ·
        by_cases h10 : m < 10
        ·
          by_cases h5 : m < 5
          ·
            by_cases h2 : m < 2
            ·
              by_cases h1 : m < 1
              ·
                obtain rfl : m = 0 := by omega
                exact iff_of_true pos0 (by decide +kernel)
              ·
                obtain rfl : m = 1 := by omega
                exact iff_of_false neg1 (by decide +kernel)
            ·
              by_cases h3 : m < 3
              ·
                obtain rfl : m = 2 := by omega
                exact iff_of_false neg2 (by decide +kernel)
              ·
                by_cases h4 : m < 4
                ·
                  obtain rfl : m = 3 := by omega
                  exact iff_of_false neg3 (by decide +kernel)
                ·
                  obtain rfl : m = 4 := by omega
                  exact iff_of_false neg4 (by decide +kernel)
          ·
            by_cases h7 : m < 7
            ·
              by_cases h6 : m < 6
              ·
                obtain rfl : m = 5 := by omega
                exact iff_of_false neg5 (by decide +kernel)
              ·
                obtain rfl : m = 6 := by omega
                exact iff_of_false neg6 (by decide +kernel)
            ·
              by_cases h8 : m < 8
              ·
                obtain rfl : m = 7 := by omega
                exact iff_of_true pos7 (by decide +kernel)
              ·
                by_cases h9 : m < 9
                ·
                  obtain rfl : m = 8 := by omega
                  exact iff_of_false neg8 (by decide +kernel)
                ·
                  obtain rfl : m = 9 := by omega
                  exact iff_of_false neg9 (by decide +kernel)
        ·
          by_cases h15 : m < 15
          ·
            by_cases h12 : m < 12
            ·
              by_cases h11 : m < 11
              ·
                obtain rfl : m = 10 := by omega
                exact iff_of_false neg10 (by decide +kernel)
              ·
                obtain rfl : m = 11 := by omega
                exact iff_of_false neg11 (by decide +kernel)
            ·
              by_cases h13 : m < 13
              ·
                obtain rfl : m = 12 := by omega
                exact iff_of_false neg12 (by decide +kernel)
              ·
                by_cases h14 : m < 14
                ·
                  obtain rfl : m = 13 := by omega
                  exact iff_of_false neg13 (by decide +kernel)
                ·
                  obtain rfl : m = 14 := by omega
                  exact iff_of_false neg14 (by decide +kernel)
          ·
            by_cases h18 : m < 18
            ·
              by_cases h16 : m < 16
              ·
                obtain rfl : m = 15 := by omega
                exact iff_of_false neg15 (by decide +kernel)
              ·
                by_cases h17 : m < 17
                ·
                  obtain rfl : m = 16 := by omega
                  exact iff_of_false neg16 (by decide +kernel)
                ·
                  obtain rfl : m = 17 := by omega
                  exact iff_of_false neg17 (by decide +kernel)
            ·
              by_cases h19 : m < 19
              ·
                obtain rfl : m = 18 := by omega
                exact iff_of_false neg18 (by decide +kernel)
              ·
                by_cases h20 : m < 20
                ·
                  obtain rfl : m = 19 := by omega
                  exact iff_of_true pos19 (by decide +kernel)
                ·
                  obtain rfl : m = 20 := by omega
                  exact iff_of_false neg20 (by decide +kernel)
      ·
        by_cases h32 : m < 32
        ·
          by_cases h26 : m < 26
          ·
            by_cases h23 : m < 23
            ·
              by_cases h22 : m < 22
              ·
                obtain rfl : m = 21 := by omega
                exact iff_of_false neg21 (by decide +kernel)
              ·
                obtain rfl : m = 22 := by omega
                exact iff_of_false neg22 (by decide +kernel)
            ·
              by_cases h24 : m < 24
              ·
                obtain rfl : m = 23 := by omega
                exact iff_of_false neg23 (by decide +kernel)
              ·
                by_cases h25 : m < 25
                ·
                  obtain rfl : m = 24 := by omega
                  exact iff_of_false neg24 (by decide +kernel)
                ·
                  obtain rfl : m = 25 := by omega
                  exact iff_of_false neg25 (by decide +kernel)
          ·
            by_cases h29 : m < 29
            ·
              by_cases h27 : m < 27
              ·
                obtain rfl : m = 26 := by omega
                exact iff_of_true pos26 (by decide +kernel)
              ·
                by_cases h28 : m < 28
                ·
                  obtain rfl : m = 27 := by omega
                  exact iff_of_false neg27 (by decide +kernel)
                ·
                  obtain rfl : m = 28 := by omega
                  exact iff_of_false neg28 (by decide +kernel)
            ·
              by_cases h30 : m < 30
              ·
                obtain rfl : m = 29 := by omega
                exact iff_of_false neg29 (by decide +kernel)
              ·
                by_cases h31 : m < 31
                ·
                  obtain rfl : m = 30 := by omega
                  exact iff_of_false neg30 (by decide +kernel)
                ·
                  obtain rfl : m = 31 := by omega
                  exact iff_of_false neg31 (by decide +kernel)
        ·
          by_cases h37 : m < 37
          ·
            by_cases h34 : m < 34
            ·
              by_cases h33 : m < 33
              ·
                obtain rfl : m = 32 := by omega
                exact iff_of_false neg32 (by decide +kernel)
              ·
                obtain rfl : m = 33 := by omega
                exact iff_of_false neg33 (by decide +kernel)
            ·
              by_cases h35 : m < 35
              ·
                obtain rfl : m = 34 := by omega
                exact iff_of_false neg34 (by decide +kernel)
              ·
                by_cases h36 : m < 36
                ·
                  obtain rfl : m = 35 := by omega
                  exact iff_of_false neg35 (by decide +kernel)
                ·
                  obtain rfl : m = 36 := by omega
                  exact iff_of_false neg36 (by decide +kernel)
          ·
            by_cases h40 : m < 40
            ·
              by_cases h38 : m < 38
              ·
                obtain rfl : m = 37 := by omega
                exact iff_of_true pos37 (by decide +kernel)
              ·
                by_cases h39 : m < 39
                ·
                  obtain rfl : m = 38 := by omega
                  exact iff_of_false neg38 (by decide +kernel)
                ·
                  obtain rfl : m = 39 := by omega
                  exact iff_of_false neg39 (by decide +kernel)
            ·
              by_cases h41 : m < 41
              ·
                obtain rfl : m = 40 := by omega
                exact iff_of_false neg40 (by decide +kernel)
              ·
                by_cases h42 : m < 42
                ·
                  obtain rfl : m = 41 := by omega
                  exact iff_of_false neg41 (by decide +kernel)
                ·
                  obtain rfl : m = 42 := by omega
                  exact iff_of_false neg42 (by decide +kernel)
    ·
      by_cases h64 : m < 64
      ·
        by_cases h53 : m < 53
        ·
          by_cases h48 : m < 48
          ·
            by_cases h45 : m < 45
            ·
              by_cases h44 : m < 44
              ·
                obtain rfl : m = 43 := by omega
                exact iff_of_false neg43 (by decide +kernel)
              ·
                obtain rfl : m = 44 := by omega
                exact iff_of_true pos44 (by decide +kernel)
            ·
              by_cases h46 : m < 46
              ·
                obtain rfl : m = 45 := by omega
                exact iff_of_false neg45 (by decide +kernel)
              ·
                by_cases h47 : m < 47
                ·
                  obtain rfl : m = 46 := by omega
                  exact iff_of_false neg46 (by decide +kernel)
                ·
                  obtain rfl : m = 47 := by omega
                  exact iff_of_false neg47 (by decide +kernel)
          ·
            by_cases h50 : m < 50
            ·
              by_cases h49 : m < 49
              ·
                obtain rfl : m = 48 := by omega
                exact iff_of_false neg48 (by decide +kernel)
              ·
                obtain rfl : m = 49 := by omega
                exact iff_of_false neg49 (by decide +kernel)
            ·
              by_cases h51 : m < 51
              ·
                obtain rfl : m = 50 := by omega
                exact iff_of_false neg50 (by decide +kernel)
              ·
                by_cases h52 : m < 52
                ·
                  obtain rfl : m = 51 := by omega
                  exact iff_of_false neg51 (by decide +kernel)
                ·
                  obtain rfl : m = 52 := by omega
                  exact iff_of_false neg52 (by decide +kernel)
        ·
          by_cases h58 : m < 58
          ·
            by_cases h55 : m < 55
            ·
              by_cases h54 : m < 54
              ·
                obtain rfl : m = 53 := by omega
                exact iff_of_false neg53 (by decide +kernel)
              ·
                obtain rfl : m = 54 := by omega
                exact iff_of_false neg54 (by decide +kernel)
            ·
              by_cases h56 : m < 56
              ·
                obtain rfl : m = 55 := by omega
                exact iff_of_false neg55 (by decide +kernel)
              ·
                by_cases h57 : m < 57
                ·
                  obtain rfl : m = 56 := by omega
                  exact iff_of_true pos56 (by decide +kernel)
                ·
                  obtain rfl : m = 57 := by omega
                  exact iff_of_false neg57 (by decide +kernel)
          ·
            by_cases h61 : m < 61
            ·
              by_cases h59 : m < 59
              ·
                obtain rfl : m = 58 := by omega
                exact iff_of_false neg58 (by decide +kernel)
              ·
                by_cases h60 : m < 60
                ·
                  obtain rfl : m = 59 := by omega
                  exact iff_of_false neg59 (by decide +kernel)
                ·
                  obtain rfl : m = 60 := by omega
                  exact iff_of_false neg60 (by decide +kernel)
            ·
              by_cases h62 : m < 62
              ·
                obtain rfl : m = 61 := by omega
                exact iff_of_false neg61 (by decide +kernel)
              ·
                by_cases h63 : m < 63
                ·
                  obtain rfl : m = 62 := by omega
                  exact iff_of_false neg62 (by decide +kernel)
                ·
                  obtain rfl : m = 63 := by omega
                  exact iff_of_true pos63 (by decide +kernel)
      ·
        by_cases h75 : m < 75
        ·
          by_cases h69 : m < 69
          ·
            by_cases h66 : m < 66
            ·
              by_cases h65 : m < 65
              ·
                obtain rfl : m = 64 := by omega
                exact iff_of_false neg64 (by decide +kernel)
              ·
                obtain rfl : m = 65 := by omega
                exact iff_of_false neg65 (by decide +kernel)
            ·
              by_cases h67 : m < 67
              ·
                obtain rfl : m = 66 := by omega
                exact iff_of_true pos66 (by decide +kernel)
              ·
                by_cases h68 : m < 68
                ·
                  obtain rfl : m = 67 := by omega
                  exact iff_of_false neg67 (by decide +kernel)
                ·
                  obtain rfl : m = 68 := by omega
                  exact iff_of_true pos68 (by decide +kernel)
          ·
            by_cases h72 : m < 72
            ·
              by_cases h70 : m < 70
              ·
                obtain rfl : m = 69 := by omega
                exact iff_of_false neg69 (by decide +kernel)
              ·
                by_cases h71 : m < 71
                ·
                  obtain rfl : m = 70 := by omega
                  exact iff_of_false neg70 (by decide +kernel)
                ·
                  obtain rfl : m = 71 := by omega
                  exact iff_of_false neg71 (by decide +kernel)
            ·
              by_cases h73 : m < 73
              ·
                obtain rfl : m = 72 := by omega
                exact iff_of_false neg72 (by decide +kernel)
              ·
                by_cases h74 : m < 74
                ·
                  obtain rfl : m = 73 := by omega
                  exact iff_of_false neg73 (by decide +kernel)
                ·
                  obtain rfl : m = 74 := by omega
                  exact iff_of_false neg74 (by decide +kernel)
        ·
          by_cases h80 : m < 80
          ·
            by_cases h77 : m < 77
            ·
              by_cases h76 : m < 76
              ·
                obtain rfl : m = 75 := by omega
                exact iff_of_false neg75 (by decide +kernel)
              ·
                obtain rfl : m = 76 := by omega
                exact iff_of_false neg76 (by decide +kernel)
            ·
              by_cases h78 : m < 78
              ·
                obtain rfl : m = 77 := by omega
                exact iff_of_false neg77 (by decide +kernel)
              ·
                by_cases h79 : m < 79
                ·
                  obtain rfl : m = 78 := by omega
                  exact iff_of_false neg78 (by decide +kernel)
                ·
                  obtain rfl : m = 79 := by omega
                  exact iff_of_false neg79 (by decide +kernel)
          ·
            by_cases h83 : m < 83
            ·
              by_cases h81 : m < 81
              ·
                obtain rfl : m = 80 := by omega
                exact iff_of_true pos80 (by decide +kernel)
              ·
                by_cases h82 : m < 82
                ·
                  obtain rfl : m = 81 := by omega
                  exact iff_of_false neg81 (by decide +kernel)
                ·
                  obtain rfl : m = 82 := by omega
                  exact iff_of_true pos82 (by decide +kernel)
            ·
              by_cases h84 : m < 84
              ·
                obtain rfl : m = 83 := by omega
                exact iff_of_false neg83 (by decide +kernel)
              ·
                by_cases h85 : m < 85
                ·
                  obtain rfl : m = 84 := by omega
                  exact iff_of_false neg84 (by decide +kernel)
                ·
                  obtain rfl : m = 85 := by omega
                  exact iff_of_true pos85 (by decide +kernel)
  ·
    by_cases h129 : m < 129
    ·
      by_cases h107 : m < 107
      ·
        by_cases h96 : m < 96
        ·
          by_cases h91 : m < 91
          ·
            by_cases h88 : m < 88
            ·
              by_cases h87 : m < 87
              ·
                obtain rfl : m = 86 := by omega
                exact iff_of_false neg86 (by decide +kernel)
              ·
                obtain rfl : m = 87 := by omega
                exact iff_of_true pos87 (by decide +kernel)
            ·
              by_cases h89 : m < 89
              ·
                obtain rfl : m = 88 := by omega
                exact iff_of_false neg88 (by decide +kernel)
              ·
                by_cases h90 : m < 90
                ·
                  obtain rfl : m = 89 := by omega
                  exact iff_of_false neg89 (by decide +kernel)
                ·
                  obtain rfl : m = 90 := by omega
                  exact iff_of_false neg90 (by decide +kernel)
          ·
            by_cases h93 : m < 93
            ·
              by_cases h92 : m < 92
              ·
                obtain rfl : m = 91 := by omega
                exact iff_of_false neg91 (by decide +kernel)
              ·
                obtain rfl : m = 92 := by omega
                exact iff_of_false neg92 (by decide +kernel)
            ·
              by_cases h94 : m < 94
              ·
                obtain rfl : m = 93 := by omega
                exact iff_of_false neg93 (by decide +kernel)
              ·
                by_cases h95 : m < 95
                ·
                  obtain rfl : m = 94 := by omega
                  exact iff_of_false neg94 (by decide +kernel)
                ·
                  obtain rfl : m = 95 := by omega
                  exact iff_of_false neg95 (by decide +kernel)
        ·
          by_cases h101 : m < 101
          ·
            by_cases h98 : m < 98
            ·
              by_cases h97 : m < 97
              ·
                obtain rfl : m = 96 := by omega
                exact iff_of_false neg96 (by decide +kernel)
              ·
                obtain rfl : m = 97 := by omega
                exact iff_of_false neg97 (by decide +kernel)
            ·
              by_cases h99 : m < 99
              ·
                obtain rfl : m = 98 := by omega
                exact iff_of_true pos98 (by decide +kernel)
              ·
                by_cases h100 : m < 100
                ·
                  obtain rfl : m = 99 := by omega
                  exact iff_of_false neg99 (by decide +kernel)
                ·
                  obtain rfl : m = 100 := by omega
                  exact iff_of_true pos100 (by decide +kernel)
          ·
            by_cases h104 : m < 104
            ·
              by_cases h102 : m < 102
              ·
                obtain rfl : m = 101 := by omega
                exact iff_of_false neg101 (by decide +kernel)
              ·
                by_cases h103 : m < 103
                ·
                  obtain rfl : m = 102 := by omega
                  exact iff_of_false neg102 (by decide +kernel)
                ·
                  obtain rfl : m = 103 := by omega
                  exact iff_of_true pos103 (by decide +kernel)
            ·
              by_cases h105 : m < 105
              ·
                obtain rfl : m = 104 := by omega
                exact iff_of_false neg104 (by decide +kernel)
              ·
                by_cases h106 : m < 106
                ·
                  obtain rfl : m = 105 := by omega
                  exact iff_of_true pos105 (by decide +kernel)
                ·
                  obtain rfl : m = 106 := by omega
                  exact iff_of_false neg106 (by decide +kernel)
      ·
        by_cases h118 : m < 118
        ·
          by_cases h112 : m < 112
          ·
            by_cases h109 : m < 109
            ·
              by_cases h108 : m < 108
              ·
                obtain rfl : m = 107 := by omega
                exact iff_of_false neg107 (by decide +kernel)
              ·
                obtain rfl : m = 108 := by omega
                exact iff_of_false neg108 (by decide +kernel)
            ·
              by_cases h110 : m < 110
              ·
                obtain rfl : m = 109 := by omega
                exact iff_of_false neg109 (by decide +kernel)
              ·
                by_cases h111 : m < 111
                ·
                  obtain rfl : m = 110 := by omega
                  exact iff_of_true pos110 (by decide +kernel)
                ·
                  obtain rfl : m = 111 := by omega
                  exact iff_of_false neg111 (by decide +kernel)
          ·
            by_cases h115 : m < 115
            ·
              by_cases h113 : m < 113
              ·
                obtain rfl : m = 112 := by omega
                exact iff_of_true pos112 (by decide +kernel)
              ·
                by_cases h114 : m < 114
                ·
                  obtain rfl : m = 113 := by omega
                  exact iff_of_false neg113 (by decide +kernel)
                ·
                  obtain rfl : m = 114 := by omega
                  exact iff_of_false neg114 (by decide +kernel)
            ·
              by_cases h116 : m < 116
              ·
                obtain rfl : m = 115 := by omega
                exact iff_of_true pos115 (by decide +kernel)
              ·
                by_cases h117 : m < 117
                ·
                  obtain rfl : m = 116 := by omega
                  exact iff_of_true pos116 (by decide +kernel)
                ·
                  obtain rfl : m = 117 := by omega
                  exact iff_of_true pos117 (by decide +kernel)
        ·
          by_cases h123 : m < 123
          ·
            by_cases h120 : m < 120
            ·
              by_cases h119 : m < 119
              ·
                obtain rfl : m = 118 := by omega
                exact iff_of_true pos118 (by decide +kernel)
              ·
                obtain rfl : m = 119 := by omega
                exact iff_of_true pos119 (by decide +kernel)
            ·
              by_cases h121 : m < 121
              ·
                obtain rfl : m = 120 := by omega
                exact iff_of_true pos120 (by decide +kernel)
              ·
                by_cases h122 : m < 122
                ·
                  obtain rfl : m = 121 := by omega
                  exact iff_of_true pos121 (by decide +kernel)
                ·
                  obtain rfl : m = 122 := by omega
                  exact iff_of_true pos122 (by decide +kernel)
          ·
            by_cases h126 : m < 126
            ·
              by_cases h124 : m < 124
              ·
                obtain rfl : m = 123 := by omega
                exact iff_of_true pos123 (by decide +kernel)
              ·
                by_cases h125 : m < 125
                ·
                  obtain rfl : m = 124 := by omega
                  exact iff_of_true pos124 (by decide +kernel)
                ·
                  obtain rfl : m = 125 := by omega
                  exact iff_of_true pos125 (by decide +kernel)
            ·
              by_cases h127 : m < 127
              ·
                obtain rfl : m = 126 := by omega
                exact iff_of_true pos126 (by decide +kernel)
              ·
                by_cases h128 : m < 128
                ·
                  obtain rfl : m = 127 := by omega
                  exact iff_of_true pos127 (by decide +kernel)
                ·
                  obtain rfl : m = 128 := by omega
                  exact iff_of_true pos128 (by decide +kernel)
    ·
      by_cases h151 : m < 151
      ·
        by_cases h140 : m < 140
        ·
          by_cases h134 : m < 134
          ·
            by_cases h131 : m < 131
            ·
              by_cases h130 : m < 130
              ·
                obtain rfl : m = 129 := by omega
                exact iff_of_true pos129 (by decide +kernel)
              ·
                obtain rfl : m = 130 := by omega
                exact iff_of_true pos130 (by decide +kernel)
            ·
              by_cases h132 : m < 132
              ·
                obtain rfl : m = 131 := by omega
                exact iff_of_true pos131 (by decide +kernel)
              ·
                by_cases h133 : m < 133
                ·
                  obtain rfl : m = 132 := by omega
                  exact iff_of_true pos132 (by decide +kernel)
                ·
                  obtain rfl : m = 133 := by omega
                  exact iff_of_true pos133 (by decide +kernel)
          ·
            by_cases h137 : m < 137
            ·
              by_cases h135 : m < 135
              ·
                obtain rfl : m = 134 := by omega
                exact iff_of_false neg134 (by decide +kernel)
              ·
                by_cases h136 : m < 136
                ·
                  obtain rfl : m = 135 := by omega
                  exact iff_of_true pos135 (by decide +kernel)
                ·
                  obtain rfl : m = 136 := by omega
                  exact iff_of_false neg136 (by decide +kernel)
            ·
              by_cases h138 : m < 138
              ·
                obtain rfl : m = 137 := by omega
                exact iff_of_false neg137 (by decide +kernel)
              ·
                by_cases h139 : m < 139
                ·
                  obtain rfl : m = 138 := by omega
                  exact iff_of_false neg138 (by decide +kernel)
                ·
                  obtain rfl : m = 139 := by omega
                  exact iff_of_false neg139 (by decide +kernel)
        ·
          by_cases h145 : m < 145
          ·
            by_cases h142 : m < 142
            ·
              by_cases h141 : m < 141
              ·
                obtain rfl : m = 140 := by omega
                exact iff_of_false neg140 (by decide +kernel)
              ·
                obtain rfl : m = 141 := by omega
                exact iff_of_false neg141 (by decide +kernel)
            ·
              by_cases h143 : m < 143
              ·
                obtain rfl : m = 142 := by omega
                exact iff_of_false neg142 (by decide +kernel)
              ·
                by_cases h144 : m < 144
                ·
                  obtain rfl : m = 143 := by omega
                  exact iff_of_false neg143 (by decide +kernel)
                ·
                  obtain rfl : m = 144 := by omega
                  exact iff_of_false neg144 (by decide +kernel)
          ·
            by_cases h148 : m < 148
            ·
              by_cases h146 : m < 146
              ·
                obtain rfl : m = 145 := by omega
                exact iff_of_false neg145 (by decide +kernel)
              ·
                by_cases h147 : m < 147
                ·
                  obtain rfl : m = 146 := by omega
                  exact iff_of_false neg146 (by decide +kernel)
                ·
                  obtain rfl : m = 147 := by omega
                  exact iff_of_true pos147 (by decide +kernel)
            ·
              by_cases h149 : m < 149
              ·
                obtain rfl : m = 148 := by omega
                exact iff_of_false neg148 (by decide +kernel)
              ·
                by_cases h150 : m < 150
                ·
                  obtain rfl : m = 149 := by omega
                  exact iff_of_true pos149 (by decide +kernel)
                ·
                  obtain rfl : m = 150 := by omega
                  exact iff_of_true pos150 (by decide +kernel)
      ·
        by_cases h162 : m < 162
        ·
          by_cases h156 : m < 156
          ·
            by_cases h153 : m < 153
            ·
              by_cases h152 : m < 152
              ·
                obtain rfl : m = 151 := by omega
                exact iff_of_true pos151 (by decide +kernel)
              ·
                obtain rfl : m = 152 := by omega
                exact iff_of_true pos152 (by decide +kernel)
            ·
              by_cases h154 : m < 154
              ·
                obtain rfl : m = 153 := by omega
                exact iff_of_false neg153 (by decide +kernel)
              ·
                by_cases h155 : m < 155
                ·
                  obtain rfl : m = 154 := by omega
                  exact iff_of_false neg154 (by decide +kernel)
                ·
                  obtain rfl : m = 155 := by omega
                  exact iff_of_true pos155 (by decide +kernel)
          ·
            by_cases h159 : m < 159
            ·
              by_cases h157 : m < 157
              ·
                obtain rfl : m = 156 := by omega
                exact iff_of_true pos156 (by decide +kernel)
              ·
                by_cases h158 : m < 158
                ·
                  obtain rfl : m = 157 := by omega
                  exact iff_of_false neg157 (by decide +kernel)
                ·
                  obtain rfl : m = 158 := by omega
                  exact iff_of_false neg158 (by decide +kernel)
            ·
              by_cases h160 : m < 160
              ·
                obtain rfl : m = 159 := by omega
                exact iff_of_true pos159 (by decide +kernel)
              ·
                by_cases h161 : m < 161
                ·
                  obtain rfl : m = 160 := by omega
                  exact iff_of_false neg160 (by decide +kernel)
                ·
                  obtain rfl : m = 161 := by omega
                  exact iff_of_false neg161 (by decide +kernel)
        ·
          by_cases h167 : m < 167
          ·
            by_cases h164 : m < 164
            ·
              by_cases h163 : m < 163
              ·
                obtain rfl : m = 162 := by omega
                exact iff_of_false neg162 (by decide +kernel)
              ·
                obtain rfl : m = 163 := by omega
                exact iff_of_false neg163 (by decide +kernel)
            ·
              by_cases h165 : m < 165
              ·
                obtain rfl : m = 164 := by omega
                exact iff_of_false neg164 (by decide +kernel)
              ·
                by_cases h166 : m < 166
                ·
                  obtain rfl : m = 165 := by omega
                  exact iff_of_false neg165 (by decide +kernel)
                ·
                  obtain rfl : m = 166 := by omega
                  exact iff_of_false neg166 (by decide +kernel)
          ·
            by_cases h170 : m < 170
            ·
              by_cases h168 : m < 168
              ·
                obtain rfl : m = 167 := by omega
                exact iff_of_false neg167 (by decide +kernel)
              ·
                by_cases h169 : m < 169
                ·
                  obtain rfl : m = 168 := by omega
                  exact iff_of_false neg168 (by decide +kernel)
                ·
                  obtain rfl : m = 169 := by omega
                  exact iff_of_false neg169 (by decide +kernel)
            ·
              by_cases h171 : m < 171
              ·
                obtain rfl : m = 170 := by omega
                exact iff_of_false neg170 (by decide +kernel)
              ·
                by_cases h172 : m < 172
                ·
                  obtain rfl : m = 171 := by omega
                  exact iff_of_true pos171 (by decide +kernel)
                ·
                  obtain rfl : m = 172 := by omega
                  exact iff_of_false neg172 (by decide +kernel)

/-- Exact classification, including the empty permutation. -/
theorem classification (n : ℕ) : Admits n ↔ n=0 ∨ n∈earlyOrders ∨ 173≤n := by
  by_cases large : 173≤n
  · exact iff_of_true (israel _ large) (Or.inr (Or.inr large))
  · simpa [large] using classify_small n (by omega)

end OMA.CubePermutation
