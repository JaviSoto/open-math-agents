import FormalConjectures.Arxiv.«2607.08366».MinModulus

/-! Rigidity of a one-label extension of the binary prefix for the
unique multiset-sum problem of J. A. R. Fonollosa. -/

namespace OMA.BinaryPrefix

private def weight (L : List ℕ) : ℕ := (L.map (fun i => 2^i)).sum

@[simp] private theorem wt_nil : weight [] = 0 := rfl
@[simp] private theorem wt_cons (i : ℕ) (L : List ℕ) :
    weight (i::L) = 2^i+weight L := rfl
@[simp] private theorem wt_append (L M : List ℕ) :
    weight (L++M) = weight L + weight M := by simp [weight]
@[simp] private theorem wt_rep (n i : ℕ) : weight (List.replicate n i) = n*2^i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih, Nat.succ_mul, Nat.add_comm]

private def bounded (r : ℕ) (L : List ℕ) := ∀ i ∈ L, i < r

@[simp] private theorem bounded_cons {r i : ℕ} {L : List ℕ} :
    bounded r (i::L) ↔ i < r ∧ bounded r L := by simp [bounded]

/-- All binary words fit in r coins. Except for the all-ones word, r−1 suffice. -/
private theorem digits (r x : ℕ) (h : x < 2^r) :
    ∃ L : List ℕ, bounded r L ∧ weight L = x ∧ L.length ≤ r ∧
      (x+1 < 2^r → L.length < r) := by
  induction r generalizing x with
  | zero =>
    have e : x = 0 := by simpa using h
    subst x
    exact ⟨[], by simp [bounded], rfl, by simp, by simp⟩
  | succ r ih =>
    have grow {L : List ℕ} (v : bounded r L) : bounded (r+1) L :=
      fun i hi => Nat.lt_succ_of_lt (v i hi)
    by_cases lt : x < 2^r
    · obtain ⟨L,hL,e,len,_⟩ := ih x lt
      exact ⟨L,grow hL,e,by omega,by omega⟩
    · rw [pow_succ] at h ⊢
      obtain ⟨L,hL,e,len,top⟩ := ih (x-2^r) (by omega)
      exact ⟨r::L,bounded_cons.mpr ⟨by omega,grow hL⟩,by simp [e]; omega,
        by simpa,by intro gap; simp only [List.length_cons]; have := top (by omega); omega⟩

/-- A coin larger than one can be split; a list whose length is less than
its value contains such a coin. -/
private theorem split_one (r : ℕ) (L : List ℕ) (b : bounded r L)
    (h : L.length < weight L) :
    ∃ M : List ℕ, bounded r M ∧ weight M = weight L ∧ M.length = L.length+1 := by
  induction L with
  | nil => simp at h
  | cons i L ih =>
    obtain ⟨hi,bl⟩ := bounded_cons.mp b
    cases i with
    | zero =>
      obtain ⟨M,bM,e,len⟩ := ih bl (by simp only [List.length_cons,wt_cons,pow_zero] at h; omega)
      exact ⟨0::M,bounded_cons.mpr ⟨hi,bM⟩,by simp [e],by simp [len]⟩
    | succ i =>
      exact ⟨i::i::L,bounded_cons.mpr ⟨by omega,bounded_cons.mpr ⟨by omega,bl⟩⟩,
        by simp [pow_succ]; omega,by simp⟩

private theorem fill (r t : ℕ) (L : List ℕ) (b : bounded r L)
    (h : L.length ≤ t) (v : t ≤ weight L) :
    ∃ M : List ℕ, bounded r M ∧ weight M = weight L ∧ M.length = t := by
  by_cases eq : L.length = t
  · exact ⟨L,b,rfl,eq⟩
  · obtain ⟨M,bM,e,len⟩ := split_one r L b (by omega)
    obtain ⟨U,bU,eU,lU⟩ := fill r t M bM (by omega) (by omega)
    exact ⟨U,bU,eU.trans e,lU⟩
termination_by t-L.length
decreasing_by omega

private theorem low (r x : ℕ) (hr : 1 ≤ r) (lo : r+1 ≤ x)
    (hi : x+1 < 2^(r+1)) :
    ∃ L : List ℕ, bounded r L ∧ weight L = x ∧ L.length = r+1 := by
  have small : ∃ L : List ℕ, bounded r L ∧ weight L = x ∧ L.length ≤ r+1 := by
    by_cases lt : x < 2^r
    · obtain ⟨L,b,e,len,_⟩ := digits r x lt
      exact ⟨L,b,e,by omega⟩
    · rw [pow_succ] at hi
      obtain ⟨L,b,e,_,lt'⟩ := digits r (x-2^r) (by omega)
      have len := lt' (by omega)
      have two : 2^r = 2^(r-1)*2 := by
        conv_lhs => rw [show r=(r-1)+1 by omega, pow_succ]
      exact ⟨(r-1)::(r-1)::L,bounded_cons.mpr ⟨by omega,bounded_cons.mpr ⟨by omega,b⟩⟩,
        by simp only [wt_cons]; omega,by simp; omega⟩
  obtain ⟨L,b,e,len⟩ := small
  obtain ⟨M,bM,e',len'⟩ := fill r (r+1) L b len (by omega)
  exact ⟨M,bM,e'.trans e,len'⟩

private theorem high (r x : ℕ) (hr : 4 ≤ r)
    (lo : 2^(r+1) ≤ x) (hi : x < 2^(r+1)+r) (except : r=4 → x≠35) :
    ∃ L : List ℕ, bounded r L ∧ weight L = x ∧ L.length = r+1 := by
  let s := x-2^(r+1)
  let L := List.replicate 4 (r-1) ++ List.replicate (s/2) 1 ++ List.replicate (s%2) 0
  have br : bounded r L := by
    intro i mem
    simp only [L,List.mem_append,List.mem_replicate] at mem
    rcases mem with ((h|h)|h) <;> obtain ⟨_,rfl⟩ := h <;> omega
  have factor : 2^(r+1) = 4*2^(r-1) := by
    rw [show r+1 = (r-1)+2 by omega, pow_add]; ring
  have val : weight L=x := by
    simp only [L,wt_append,wt_rep,pow_one,pow_zero,mul_one]
    dsimp [s]; omega
  have len : L.length ≤ r+1 := by
    simp [L,s]
    by_cases four : r=4
    · subst r; norm_num at lo hi ⊢; have := except rfl; omega
    · omega
  have grow : r+1 ≤ 2^(r+1) := Nat.le_of_lt (Nat.lt_two_pow_self)
  obtain ⟨M,bM,eM,lenM⟩ := fill r (r+1) L br len (by omega)
  exact ⟨M,bM,eM.trans val,lenM⟩

/-- With normalized binary labels, the residue of the full sum without the
new label must have no representation of length r+1 using the old labels. -/
private theorem force (r N y : ℕ) (hr : 4 ≤ r) (hn : N < 2^(r+1)) (hy : y < N)
    (except : ¬ (r=4 ∧ N=31 ∧ y=20))
    (no_rival : ∀ L : List ℕ, bounded r L → L.length = r+1 →
      (weight L : ZMod N) ≠ ((2^r-1+y : ℕ) : ZMod N)) : y = 2^r := by
  have pos : 0 < 2^r := by positivity
  have grow : r+2 ≤ 2^r := by
    have strong (i : ℕ) : (i+2)+2 ≤ 2^(i+2) := by
      induction i with
      | zero => decide
      | succ i ih => rw [show i+1+2=(i+2)+1 by omega,pow_succ]; omega
    convert strong (r-2) using 1 <;> congr 1 <;> omega
  have span : 2^(r+1) = 2^r*2 := pow_succ ..
  by_cases small : y < 2^r
  · obtain ⟨L,b,e,len⟩ := low r (2^r-1+y) (by omega) (by omega) (by omega)
    exact False.elim (no_rival L b len (by rw [e]))
  by_contra neq
  let v := 2^r-1+y-N
  have ev : v+N = 2^r-1+y := by dsimp [v]; omega
  have less : v < 2^r := by dsimp [v]; omega
  have short : v < r+1 := by
    by_contra long
    obtain ⟨L,b,e,len⟩ := low r v (by omega) (by omega) (by omega)
    apply no_rival L b len
    rw [e,←ev]
    simp
  obtain ⟨L,b,e,len⟩ := high r (2^r-1+y) hr (by omega) (by omega) (by
    rintro rfl ex
    norm_num at ex hn ev short
    exact except ⟨rfl,by omega,by omega⟩)
  exact no_rival L b len (by rw [e])

open Finset

private theorem sum_bits (r : ℕ) : ∑ i ∈ range r, 2^i = 2^r-1 := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [sum_range_succ,ih,pow_succ]
    have : 0 < 2^r := by positivity
    omega

private theorem counts {G : Type*} [DecidableEq G] [AddCommMonoid G]
    (A : Finset G) (L : List G) (inside : ∀ z ∈ L, z ∈ A) :
    (∑ z ∈ A, L.count z) = L.length ∧ (∑ z ∈ A, L.count z • z) = L.sum := by
  induction L with
  | nil => simp
  | cons x L ih =>
    have hx := inside x (by simp)
    obtain ⟨size,tot⟩ := ih fun z hz => inside z (by simp [hz])
    constructor
    · simp only [List.count_cons,beq_iff_eq,Finset.sum_add_distrib,List.length_cons]
      simp [size,hx]
    · simp only [List.count_cons,beq_iff_eq,add_nsmul,Finset.sum_add_distrib,List.sum_cons]
      simp [tot,ite_smul,hx,add_comm]

/-- In any modulus below 2^(r+1), a valid set of r+1 elements that already
contains the normalized powers 1,...,2^(r-1) must complete them with 2^r.
The cardinality premise also excludes coincidences within the prefix. -/
theorem extension (r N y : ℕ) (hr : 4 ≤ r) (hn : N < 2^(r+1)) (hy : y < N)
    (card : (insert (y : ZMod N) ((range r).image (fun i => (2:ZMod N)^i))).card = r+1)
    (valid : Arxiv.«2607.08366».IsValidMod
      (insert (y : ZMod N) ((range r).image (fun i => (2:ZMod N)^i)))) :
    y = 2^r := by
  classical
  let A := (range r).image (fun i => (2:ZMod N)^i)
  change (insert (y : ZMod N) A).card = r+1 at card
  have upper : A.card ≤ r := by simpa [A] using (card_image_le (f:=fun i => (2:ZMod N)^i) (s:=range r))
  have fresh : (y : ZMod N) ∉ A := by
    intro mem
    rw [insert_eq_of_mem mem] at card
    omega
  have exact_card : A.card = r := by rw [card_insert_of_notMem fresh] at card; omega
  have inj : Set.InjOn (fun i => (2:ZMod N)^i) (range r : Set ℕ) := by
    apply card_image_iff.mp
    simpa [A] using exact_card
  have total : (∑ z ∈ A, z) = ((2^r-1 : ℕ) : ZMod N) := by
    rw [←sum_bits]
    push_cast
    exact sum_image (fun i hi j hj eq => inj hi hj eq)
  have except : ¬ (r=4 ∧ N=31 ∧ y=20) := by
    rintro ⟨rfl,rfl,rfl⟩
    let m (z : ZMod 31) := if z=20 then 3 else if z=2 ∨ z=4 then 1 else 0
    have absurd := valid m (by decide) (by decide) 20 (by decide)
    change 3 = 1 at absurd
    omega
  apply force r N y hr hn hy except
  intro L b len eq
  let V := L.map (fun i => (2:ZMod N)^i)
  have sub : ∀ z ∈ V, z ∈ A := by
    intro z hz
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hz
    exact mem_image.mpr ⟨i,mem_range.mpr (b i hi),rfl⟩
  have cts := counts (insert (y:ZMod N) A) V (fun z hz => mem_insert_of_mem (sub z hz))
  have sumV : V.sum = (weight L : ZMod N) := by
    simp [V,weight,Function.comp_def]
  have one := valid (fun z => V.count z) (cts.1.trans ((by simp [V,len] : V.length=r+1).trans card.symm))
    (by
      change (∑ z ∈ insert (y : ZMod N) A, (V.count z : ZMod N)*z) = _
      simp only [←nsmul_eq_mul]
      rw [cts.2,sumV,eq,sum_insert fresh,total,Nat.cast_add,add_comm])
    (y:ZMod N) (by simp)
  have zero : V.count (y:ZMod N) = 0 := List.count_eq_zero.mpr (fun hy => fresh (sub _ hy))
  omega

/-- The threshold four is sharp: modulo 15 the three powers 1,2,4 also
admit 11 as a valid fourth label. -/
theorem sharp : Arxiv.«2607.08366».IsValidMod ({1,2,4,11} : Finset (ZMod 15)) := by
  intro m len eq z hz
  have a : (1:ZMod 15) ∉ ({2,4,11} : Finset _) := by decide
  have b : (2:ZMod 15) ∉ ({4,11} : Finset _) := by decide
  have c : (4:ZMod 15) ∉ ({11} : Finset _) := by decide
  have num : ({1,2,4,11} : Finset (ZMod 15)).card = 4 := by decide
  simp only [sum_insert a,sum_insert b,sum_insert c,sum_singleton,num,mul_one] at len eq
  rw [show (1+(2+(4+11)) : ZMod 15) = 3 by decide] at eq
  have h₁ : m 1 < 5 := by omega
  have h₂ : m 2 < 5 := by omega
  have h₄ : m 4 < 5 := by omega
  have h₁₁ : m 11 < 5 := by omega
  have cert : ∀ a b c d : Fin 5, a.val+b.val+c.val+d.val=4 →
      (a.val : ZMod 15)+b.val*2+c.val*4+d.val*11=3 →
      a.val=1 ∧ b.val=1 ∧ c.val=1 ∧ d.val=1 := by decide
  obtain ⟨one,two,four,eleven⟩ :=
    cert ⟨_,h₁⟩ ⟨_,h₂⟩ ⟨_,h₄⟩ ⟨_,h₁₁⟩ (by dsimp; omega) (by dsimp; convert eq using 1; ring)
  simp only [mem_insert,mem_singleton] at hz
  rcases hz with rfl|rfl|rfl|rfl <;> assumption

#print axioms OMA.BinaryPrefix.extension
#print axioms OMA.BinaryPrefix.sharp

end OMA.BinaryPrefix
