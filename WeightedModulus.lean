import Mathlib

/-! Exact bounds for prescribed multiplicities in the unique multiset-sum
problem. Normalize a label of least weight m to zero. The other weights are
w, and the multiplicity of the zero label is the unused part of the budget.
This file is independent of the formal-conjectures definitions. -/

namespace OMA.WeightedModulus
open Finset

variable {ι G : Type*} [Fintype ι] [AddCommGroup G]

def Valid (m : ℕ) (w : ι → ℕ) (g : ι → G) : Prop :=
  ∀ x : ι → ℕ, (∑ i, x i) ≤ m + ∑ i, w i →
    (∑ i, x i • g i) = ∑ i, w i • g i → x = w

/-- The homogeneous condition, with the pivot label and its count explicit. -/
def TupleValid (m : ℕ) (w : ι → ℕ) (g₀ : G) (g : ι → G) : Prop :=
  ∀ a x, a+(∑ i,x i)=m+∑ i,w i →
    a • g₀+(∑ i,x i • g i)=m • g₀+∑ i,w i • g i → a=m ∧ x=w

theorem normalize (m : ℕ) (w : ι → ℕ) (g₀ : G) (g : ι → G) :
    TupleValid m w g₀ g ↔ Valid m w (fun i => g i-g₀) := by
  have translate (a : ℕ) (x : ι → ℕ) :
      (∑ i,x i • (g i-g₀)) + (a+∑ i,x i) • g₀ = a • g₀+∑ i,x i • g i := by
    simp only [nsmul_sub,sum_sub_distrib,add_nsmul,Finset.sum_smul]
    abel
  constructor
  · intro h x budget mass
    let a := m+(∑ i,w i)-(∑ i,x i)
    have count : a+(∑ i,x i)=m+∑ i,w i := Nat.sub_add_cancel budget
    exact (h a x count (by rw [←translate a x,←translate m w,count,mass])).2
  · intro h a x count mass
    rw [←translate a x,←translate m w,count] at mass
    have eq := h x (by omega) (add_right_cancel mass)
    exact ⟨by rw [eq] at count; omega,eq⟩

def encode (w : ι → ℕ) (g : ι → G) (b : ∀ i, Fin (w i+1)) : G :=
  ∑ i, (b i).val • g i

private lemma change_counts (w a b : ι → ℕ) (g : ι → G) (hb : ∀ i, b i≤w i)
    (same : (∑ i,a i • g i)=∑ i,b i • g i) :
    let z := fun i => w i-b i+a i
    (∑ i,z i)+(∑ i,b i)=(∑ i,w i)+(∑ i,a i) ∧
    (∑ i,z i • g i)=∑ i,w i • g i := by
  dsimp only
  have eq (i : ι) : w i-b i+a i+b i = w i+a i := by have := hb i; omega
  constructor
  · simp only [←sum_add_distrib,eq]
  · apply add_right_cancel (b:=∑ i, b i • g i)
    conv_rhs => rw [←same]
    simp only [←sum_add_distrib,←add_nsmul,eq]

theorem box_injective {m : ℕ} {w : ι → ℕ} {g : ι → G} (h : Valid m w g) :
    Function.Injective (encode w g) := by
  intro a b same
  suffices aux : ∀ (a b : ∀ i, Fin (w i+1)), encode w g a=encode w g b →
      (∑ i,(a i).val)≤∑ i,(b i).val → a=b by
    rcases le_total (∑ i,(a i).val) (∑ i,(b i).val) with l|l
    · exact aux a b same l
    · exact (aux b a same.symm l).symm
  intro a b same less
  obtain ⟨count,mass⟩ := change_counts w (fun i=>(a i).val) (fun i=>(b i).val) g
    (fun i=>Nat.le_of_lt_succ (b i).isLt) same
  change (∑ i,(w i-(b i).val+(a i).val)) + _ = _ at count
  have hv := h _ (by omega) mass
  funext i
  have at_i := congrFun hv i
  have := (b i).isLt
  exact Fin.ext (by omega)

theorem order_lower [Fintype G] {m : ℕ} {w : ι → ℕ} {g : ι → G} (h : Valid m w g) :
    (∏ i, (w i+1)) ≤ Fintype.card G := by
  classical
  simpa using Fintype.card_le_of_injective _ (box_injective h)

theorem least_digit_annihilated [Fintype G] {m : ℕ} {w : ι → ℕ} {g : ι → G}
    (h : Valid m w g) (order : Fintype.card G=∏ i,(w i+1)) {i : ι} (wi : w i=m) :
    (m+1) • g i=0 := by
  classical
  have sur := ((Fintype.bijective_iff_injective_and_card (encode w g)).2
    ⟨box_injective h,by simpa using order.symm⟩).2
  obtain ⟨b,rep⟩ := sur ((m+1) • g i)
  let a (j : ι) : ℕ := if i=j then m+1 else 0
  have ar : (∑ j,a j • g j)=(m+1) • g i := by simp [a,ite_smul]
  have ac : (∑ j,a j)=m+1 := by simp [a]
  have same : (∑ j,a j • g j)= ∑ j,(b j).val • g j := ar.trans rep.symm
  obtain ⟨count,mass⟩ := change_counts w a (fun j=>(b j).val) g
    (fun j=>Nat.le_of_lt_succ (b j).isLt) same
  change (∑ j,(w j-(b j).val+a j)) + _ = _ at count
  by_cases pos : 0<∑ j,(b j).val
  · have hv := h _ (by omega) mass
    have t := congrFun hv i
    simp only [a,if_pos rfl,wi] at t
    omega
  · have bz (j : ι) : (b j).val=0 := by
      have le := single_le_sum (f:=fun l => (b l).val) (by simp) (mem_univ j)
      omega
    simpa [encode,bz] using rep.symm

/-- The standard coordinate labels in a product of cyclic groups attain
    the box bound for arbitrary positive weights. -/
theorem abelian_attains (m : ℕ) (w : ι → ℕ) (hm : ∀ i, m≤w i) :
    ∃ g : ι → (∀ j, ZMod (w j+1)), Valid m w g := by
  classical
  let g (i j : ι) : ZMod (w j+1) := if i=j then 1 else 0
  refine ⟨g,?_⟩
  intro x budget mass
  have value (i : ι) : (x i : ZMod (w i+1)) = (w i : ZMod (w i+1)) := by
    have z := congrFun mass i
    simpa [g,Finset.sum_apply,nsmul_eq_mul,mul_ite] using z
  have bounds (i : ι) : w i≤x i ∧ (w i≠x i → w i+(w i+1)≤x i) := by
    have z := (ZMod.natCast_eq_natCast_iff (x i) (w i) (w i+1)).mp (value i)
    change x i%(w i+1) = w i%(w i+1) at z
    rw [Nat.mod_eq_of_lt (Nat.lt_succ_self _)] at z
    have z' := Nat.mod_add_div (x i) (w i+1)
    rw [z] at z'
    constructor
    · omega
    · intro ne
      have d : 1≤x i/(w i+1) := by
        apply Nat.one_le_iff_ne_zero.mpr
        intro no
        rw [no,mul_zero,add_zero] at z'
        exact ne z'
      have := Nat.mul_le_mul_left (w i+1) d
      omega
  funext i
  by_contra ne
  have t := (bounds i).2 (Ne.symm ne)
  have total := sum_le_sum (s:=univ.erase i) (fun j _ => (bounds j).1)
  have lhs := sum_erase_add univ w (mem_univ i)
  have rhs := sum_erase_add univ x (mem_univ i)
  have := hm i
  omega

private lemma encode_axis [DecidableEq ι] (w : ι → ℕ) (g : ι → G) (i : ι) (a : Fin (w i+1)) :
    encode w g (Pi.single i a)=a.val • g i := by
  rw [encode,Finset.sum_eq_single i]
  · simp
  · intro j _ ji
    simp [Pi.single_eq_of_ne ji]
  · simp

/-- In a cyclic extremizer at most one *nonpivot* digit may have the
    pivot's weight. The full tuple can therefore have at most two minima. -/
theorem cyclic_minimum_unique {m N : ℕ} [NeZero N] {w : ι → ℕ} {g : ι → ZMod N}
    (hm : 0 < m) (h : Valid m w g) (order : N=∏ i,(w i+1)) {i j : ι}
    (wi : w i=m) (wj : w j=m) : i=j := by
  classical
  by_contra ne
  let q := m+1
  have card : Fintype.card (ZMod N)=∏ i,(w i+1) := (ZMod.card N).trans order
  have div : q ∣ N := by
    rw [order]
    simpa only [wi,q] using (dvd_prod_of_mem (fun l => w l+1) (mem_univ i))
  obtain ⟨s,hs⟩ := div
  have rep {l : ι} (wl : w l=m) : ∃ a : ℕ, a<q ∧ (g l).val=s*a := by
    have zero := least_digit_annihilated h card wl
    have dz : (q*s) ∣ q*(g l).val := by
      rw [←hs]
      apply (ZMod.natCast_eq_zero_iff _ _).mp
      simpa [q,Nat.cast_mul,nsmul_eq_mul] using zero
    obtain ⟨a,ha⟩ := Nat.dvd_of_mul_dvd_mul_left (Nat.succ_pos m) dz
    refine ⟨a,?_,ha⟩
    have ltb := (g l).val_lt
    rw [ha,hs,mul_comm q s] at ltb
    exact Nat.lt_of_mul_lt_mul_left ltb
  obtain ⟨a,ha,ea⟩ := rep wi
  obtain ⟨b,hb,eb⟩ := rep wj
  have notzero (l : ι) (wl : w l=m) : g l≠0 := by
    intro zg
    let o : Fin (w l+1) := ⟨1,by omega⟩
    have eq : encode w g (Pi.single l o)=encode w g (Pi.single l 0) := by
      rw [encode_axis,encode_axis,zg]
      simp
    have orig := congrFun (box_injective h eq) l
    simpa [o] using congrArg Fin.val orig
  have eq : b • g i = a • g j := by
    rw [←ZMod.natCast_zmod_val (g i),←ZMod.natCast_zmod_val (g j),ea,eb]
    push_cast
    simp only [nsmul_eq_mul]
    ring
  let u : Fin (w i+1) := ⟨b,wi ▸ hb⟩
  let v : Fin (w j+1) := ⟨a,wj ▸ ha⟩
  have hit : encode w g (Pi.single i u)=encode w g (Pi.single j v) := by simpa [encode_axis,u,v] using eq
  have at_i := congrFun (box_injective h hit) i
  have bz : b=0 := by simpa [u,Pi.single_eq_of_ne ne] using congrArg Fin.val at_i
  apply notzero j wj
  rw [←ZMod.natCast_zmod_val (g j),eb,bz]
  simp

private def ModValid (m N : ℕ) (S : Finset ι) (w b : ι → ℕ) : Prop :=
  ∀ x : ι → ℕ, (∑ i∈S,x i) ≤ m+∑ i∈S,w i →
    (∑ i∈S,x i*b i) ≡ (∑ i∈S,w i*b i) [MOD N] → ∀ i∈S,x i=w i

omit [Fintype ι] in
private lemma construct_digits [DecidableEq ι] (m : ℕ) (w : ι → ℕ) (j : ι) (wj : m≤w j)
    (S : Finset ι) (notj : j∉S) (large : ∀ i∈S,m<w i) :
    let A := insert j S
    ∃ b : ι → ℕ, (∃ z∈A, b z=1) ∧ ModValid m (∏ l∈A,(w l+1)) A w b := by
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨fun _=>1,⟨j,by simp,rfl⟩,?_⟩
    intro x budget mass i hi
    simp only [insert_empty_eq,mem_singleton] at hi
    subst i
    simp only [insert_empty_eq,sum_singleton,prod_singleton,mul_one] at budget mass
    change x j%(w j+1)=w j%(w j+1) at mass
    rw [Nat.mod_eq_of_lt (Nat.lt_succ_self _)] at mass
    have z := Nat.mod_add_div (x j) (w j+1)
    rw [mass] at z
    by_cases zero : x j/(w j+1)=0
    · simpa [zero] using z.symm
    have d := Nat.mul_le_mul_left (w j+1) (Nat.one_le_iff_ne_zero.mpr zero)
    omega
  | insert i S ni ih =>
    have ij : i≠j := by intro bad; subst i; exact notj (mem_insert_self ..)
    let A := insert j S
    have ia : i∉A := by simp [A,ij,ni]
    have wi : m<w i := large _ (mem_insert_self ..)
    obtain ⟨b,⟨l,hl,one⟩,old⟩ := ih (fun hj => notj (mem_insert_of_mem hj))
      (fun v hv => large _ (mem_insert_of_mem hv))
    change l∈A at hl
    let B := w i+1
    let N := ∏ l∈A,(w l+1)
    let f (v : ι) := if v=i then 1 else B*b v
    rw [insert_comm]
    refine ⟨f,⟨i,mem_insert_self ..,by simp [f]⟩,?_⟩
    intro x budget mass v hmem
    have fold (a : ι→ℕ) : (∑ j∈insert i A,a j*f j)=a i+B*(∑ j∈A,a j*b j) := by
      rw [sum_insert ia,mul_sum]
      simp only [f,if_pos rfl,mul_one,add_right_inj]
      apply sum_congr rfl
      intro r hr
      rw [if_neg (by intro e; exact ia (e ▸ hr))]
      ring
    change (∑ j∈insert i A,x j*f j) ≡ (∑ j∈insert i A,w j*f j) [MOD (∏ j∈insert i A,(w j+1))] at mass
    rw [fold,fold,prod_insert ia] at mass
    change x i+B*_ ≡ w i+B*_ [MOD B*N] at mass
    have cut := mass.of_dvd (dvd_mul_right B N)
    change (x i+B*_)%B=(w i+B*_)%B at cut
    simp only [Nat.add_mul_mod_self_left] at cut
    rw [Nat.mod_eq_of_lt (Nat.lt_succ_self (w i))] at cut
    let t := x i / B
    have xi : x i=w i+B*t := by simpa only [t,cut] using (Nat.mod_add_div (x i) B).symm
    have reduced : t+(∑ j∈A,x j*b j) ≡ (∑ j∈A,w j*b j) [MOD N] := by
      apply Nat.ModEq.mul_left_cancel' (by dsimp [B]; omega : B≠0)
      apply Nat.ModEq.add_left_cancel' (w i)
      convert mass using 1
      rw [xi]; ring
    let y (j : ι) := x j + if j=l then t else 0
    have ysum : (∑ j∈A,y j)=(∑ j∈A,x j)+t := by simp [y,sum_add_distrib,hl]
    have yval : (∑ j∈A,y j*b j)=(∑ j∈A,x j*b j)+t := by
      simp [y,add_mul,sum_add_distrib,ite_mul,hl,one]
    change (∑ j∈insert i A,x j) ≤ m+(∑ j∈insert i A,w j) at budget
    rw [sum_insert ia,sum_insert ia] at budget
    change ModValid m N A w b at old
    have yt := old y (by rw [ysum]; dsimp [B] at xi; nlinarith)
      (by rw [yval,add_comm]; exact reduced)
    have sy : (∑ j∈A,y j)=(∑ j∈A,w j) := sum_congr rfl yt
    rw [ysum] at sy
    have tz : t=0 := by
      by_contra! bad
      have cost := Nat.mul_le_mul_left (w i) (Nat.one_le_iff_ne_zero.mpr bad)
      dsimp [B] at xi
      nlinarith
    rcases mem_insert.mp hmem with rfl|hv
    · simpa [tz] using xi
    · simpa [y,tz] using yt v hv

/-- The product lower bound is attained in a cyclic group exactly when at most
one weight besides the pivot equals the minimum. -/
theorem cyclic_attains_iff (m : ℕ) (hm : 0 < m) (w : ι → ℕ) (hw : ∀ i, m≤w i) :
    (∃ g : ι → ZMod (∏ i,(w i+1)), Valid m w g) ↔
      ∀ i j, w i=m → w j=m → i=j := by
  classical
  let D := ∏ i,(w i+1)
  have : NeZero D := ⟨(Finset.prod_pos (s:=univ) (fun i _ => Nat.succ_pos (w i))).ne'⟩
  constructor
  · rintro ⟨g,h⟩ i j wi wj
    exact cyclic_minimum_unique (N:=D) hm h rfl wi wj
  intro unique
  rcases isEmpty_or_nonempty ι with empty|nonempty
  · exact ⟨fun _=>0, fun _ _ _ => Subsingleton.elim ..⟩
  obtain ⟨j,hj⟩ : ∃ j, ∀ i, i≠j → m<w i := by
    by_cases least : ∃ i,w i=m
    · obtain ⟨j,wj⟩ := least
      exact ⟨j,fun i ne => lt_of_le_of_ne (hw i) (fun wi => ne (unique i j wi.symm wj))⟩
    · exact ⟨nonempty.some,fun i _ => lt_of_le_of_ne (hw i) (fun wi => least ⟨i,wi.symm⟩)⟩
  have e := construct_digits m w j (hw j) (univ.erase j) (by simp)
    (fun i hi => hj i (mem_erase.mp hi).1)
  simp only [insert_erase (mem_univ j)] at e
  obtain ⟨b,_,valid⟩ := e
  refine ⟨fun i => (b i : ZMod D),?_⟩
  intro x budget mass
  have eq : ((∑ i,x i*b i : ℕ):ZMod D)=((∑ i,w i*b i : ℕ):ZMod D) := by
    simpa only [Nat.cast_sum,Nat.cast_mul,nsmul_eq_mul] using mass
  exact funext (fun i => valid x budget ((ZMod.natCast_eq_natCast_iff _ _ _).mp eq) i (mem_univ i))

/-- The cyclic equality criterion with the pivot and all rival multiplicities
    present in the statement. -/
theorem homogeneous_cyclic_iff (m : ℕ) (hm : 0 < m) (w : ι → ℕ) (hw : ∀ i, m≤w i) :
    (∃ (a : ZMod (∏ i,(w i+1))) (g : ι → ZMod (∏ i,(w i+1))), TupleValid m w a g) ↔
      ∀ i j, w i=m → w j=m → i=j := by
  constructor
  · rintro ⟨a,g,h⟩
    exact (cyclic_attains_iff m hm w hw).mp ⟨_,(normalize m w a g).mp h⟩
  · intro unique
    obtain ⟨g,h⟩ := (cyclic_attains_iff m hm w hw).mpr unique
    exact ⟨0,g,(normalize m w 0 g).mpr (by simpa using h)⟩

theorem homogeneous_abelian_minimum (m : ℕ) (w : ι → ℕ) (hw : ∀ i, m≤w i) :
    (∀ (G : Type) [Fintype G] [AddCommGroup G] (a : G) (g : ι → G),
      TupleValid m w a g → (∏ i,(w i+1))≤Fintype.card G) ∧
    (Nat.card (∀ j, ZMod (w j+1))=(∏ i,(w i+1)) ∧
      ∃ g : ι → (∀ j, ZMod (w j+1)), TupleValid m w 0 g) := by
  classical
  constructor
  · intro G _ _ a g valid
    exact order_lower ((normalize m w a g).mp valid)
  obtain ⟨g,h⟩ := abelian_attains m w hw
  exact ⟨by simp [Nat.card_eq_fintype_card,Fintype.card_pi],g,
    (normalize m w 0 g).mpr (by simpa using h)⟩

/-- Three labels with the same prescribed positive multiplicity. The third
    (pivot) label is translated to zero. -/
def ThreeValid (m : ℕ) (a b : G) : Prop :=
  ∀ x y : ℕ, x+y ≤ 3*m → x • a+y • b=m • a+m • b → x=m ∧ y=m

private lemma ThreeValid.swap {m : ℕ} {a b : G} (h : ThreeValid m a b) : ThreeValid m b a := by
  intro x y total mass
  exact (h y x (by omega) (by simpa only [add_comm] using mass)).symm

private lemma ThreeValid.move {m x y u v : ℕ} {a b : G} (h : ThreeValid m a b)
    (xu : u ≤ m+x) (yv : v ≤ m+y) (cost : x+y ≤ m+(u+v))
    (mass : x • a+y • b=u • a+v • b) : x=u ∧ y=v := by
  let z := m+x-u
  let t := m+y-v
  have zu : z+u=m+x := Nat.sub_add_cancel xu
  have tv : t+v=m+y := Nat.sub_add_cancel yv
  have same : z • a+t • b=m • a+m • b := by
    apply add_right_cancel (b:=u • a+v • b)
    conv_rhs => rw [←mass]
    calc
      _ = (z+u) • a+(t+v) • b := by simp only [add_nsmul]; abel
      _ = _ := by rw [zu,tv]; simp only [add_nsmul]; abel
  obtain ⟨hz,ht⟩ := h z t (by omega) same
  omega

private lemma ThreeValid.box {m : ℕ} {a b : G} (h : ThreeValid m a b)
    {x y u v : ℕ} (hx : x ≤ m) (hy : y ≤ m) (hu : u ≤ m) (hv : v ≤ m)
    (mass : x • a+y • b=u • a+v • b) : x=u ∧ y=v := by
  by_cases ord : x+y≤u+v
  · exact h.move (by omega) (by omega) (by omega) mass
  · obtain ⟨e,f⟩ := h.move (by omega) (by omega) (by omega) mass.symm
    exact ⟨e.symm,f.symm⟩

private lemma ThreeValid.fringe [Fintype G] {m : ℕ} {a b : G} (h : ThreeValid m a b)
    (small : Fintype.card G < (m+1)*(m+2)) :
    ∃ j ≤ m,(m+1) • a+j • b=0 := by
  by_contra no
  let f (s : Fin (m+2) × Fin (m+1)) := s.1.val • a+s.2.val • b
  have ordered (s t : Fin (m+2) × Fin (m+1)) (ord : s.1.val≤t.1.val)
      (same : f s=f t) : s=t := by
    change s.1.val • a+s.2.val • b=t.1.val • a+t.2.val • b at same
    have sx := s.1.isLt
    have sy := s.2.isLt
    have tx := t.1.isLt
    have ty := t.2.isLt
    by_cases inner : t.1.val ≤ m
    · obtain ⟨e,e'⟩ := h.box (by omega) (by omega) inner (by omega) same
      exact Prod.ext (Fin.ext e) (Fin.ext e')
    have top : t.1.val=m+1 := by omega
    rw [top] at same
    by_cases edge : s.1.val=m+1
    · rw [edge] at same
      have ev := add_left_cancel same
      have mass : (0:ℕ) • a+s.2.val • b=0 • a+t.2.val • b := by simpa using ev
      have eq := h.box (by omega) (by omega) (by omega) (by omega) mass
      exact Prod.ext (Fin.ext (by omega)) (Fin.ext eq.2)
    have left : s.1.val=0 := by
      by_contra nz
      have eq := h.move (by omega) (by omega) (by omega) same
      omega
    have order : s.2.val≤t.2.val := by
      by_contra lt
      have eq := h.move (by omega) (by omega) (by omega) same.symm
      omega
    apply False.elim <| no ⟨t.2.val-s.2.val,by omega,?_⟩
    apply add_right_cancel (b:=s.2.val • b)
    rw [zero_add,add_assoc,←add_nsmul,Nat.sub_add_cancel order]
    simpa [left] using same.symm
  have inj : Function.Injective f := by
    intro s t same
    rcases le_total s.1.val t.1.val with lt|gt
    · exact ordered s t lt same
    · exact (ordered t s gt same.symm).symm
  have lower := Fintype.card_le_of_injective f inj
  simp only [Fintype.card_prod,Fintype.card_fin] at lower
  rw [Nat.mul_comm] at lower
  omega

private lemma ThreeValid.no_small_cyclic {m : ℕ} {G : Type*} [Fintype G] [AddCommGroup G]
    [IsAddCyclic G] (hm : 0 < m) {a b : G} (h : ThreeValid m a b) :
    (m+1)*(m+2)≤Fintype.card G := by
  classical
  by_contra! small
  obtain ⟨j,hj,jrel⟩ := h.fringe small
  obtain ⟨k,hk,krel⟩ := h.swap.fringe small
  have j0k0 : j=0 ∧ k=0 := by
    by_cases jz : j=0
    · subst j
      simp only [zero_smul,add_zero] at jrel
      by_contra! bad
      have eq : (m+1-k) • a=(m+1) • b := by
        apply add_right_cancel (b:=k • a)
        rw [←add_nsmul,Nat.sub_add_cancel (by omega),jrel,krel]
      have mass : (m+1-k) • a+0 • b=0 • a+(m+1) • b := by simpa using eq
      have ff := h.move (by omega) (by omega) (by omega) mass.symm
      omega
    by_cases kz : k=0
    · subst k
      simp only [zero_smul,add_zero] at krel
      have eq : (m+1-j) • b=(m+1) • a := by
        apply add_right_cancel (b:=j • b)
        rw [←add_nsmul,Nat.sub_add_cancel (by omega),krel,jrel]
      have mass : (m+1) • a+0 • b=0 • a+(m+1-j) • b := by simpa using eq.symm
      have ff := h.move (by omega) (by omega) (by omega) mass
      omega
    have eq : (m+1-k) • a=(m+1-j) • b := by
      apply add_right_cancel (b:=k • a+j • b)
      calc
        _ = (m+1) • a+j • b := by rw [←add_assoc,←add_nsmul,Nat.sub_add_cancel (by omega)]
        _ = (m+1) • b+k • a := jrel.trans krel.symm
        _ = _ := by
          rw [add_comm (k • a) (j • b),←add_assoc,←add_nsmul,Nat.sub_add_cancel (by omega)]
    have mass : (m+1-k) • a+0 • b=0 • a+(m+1-j) • b := by simpa using eq
    have ff := h.box (by omega) (by omega) (by omega) (by omega) mass
    omega
  obtain ⟨rfl,rfl⟩ := j0k0
  simp only [zero_smul,add_zero] at jrel krel
  let T := univ.filter (fun z : G => (m+1) • z=0)
  let f (s : Fin (m+1) × Fin (m+1)) : T :=
    ⟨s.1.val • a+s.2.val • b,by
      apply mem_filter.mpr ⟨mem_univ _,?_⟩
      rw [nsmul_add,smul_comm (m+1) s.1.val,smul_comm (m+1) s.2.val,jrel,krel]
      simp⟩
  have inj : Function.Injective f := by
    intro s t same
    have eq := h.box (Nat.le_of_lt_succ s.1.isLt) (Nat.le_of_lt_succ s.2.isLt)
      (Nat.le_of_lt_succ t.1.isLt) (Nat.le_of_lt_succ t.2.isLt) (congrArg Subtype.val same)
    exact Prod.ext (Fin.ext eq.1) (Fin.ext eq.2)
  have lower := Fintype.card_le_of_injective f inj
  simp only [Fintype.card_coe,Fintype.card_prod,Fintype.card_fin] at lower
  have upper : T.card ≤ m+1 := IsAddCyclic.card_nsmul_eq_zero_le (Nat.succ_pos m)
  nlinarith

private lemma three_construct (m : ℕ) :
    ThreeValid m (1 : ZMod ((m+1)*(m+2))) (m+2 : ℕ) := by
  let B := m+2
  let q := m+1
  intro x y budget mass
  have eq : ((x+B*y : ℕ):ZMod (q*B))=((m+B*m : ℕ):ZMod (q*B)) := by
    simpa only [B,q,Nat.cast_add,Nat.cast_mul,nsmul_eq_mul,mul_one,mul_comm] using mass
  have congr := (ZMod.natCast_eq_natCast_iff _ _ _).mp eq
  rw [Nat.mul_comm q B] at congr
  have cut := congr.of_dvd (dvd_mul_right B q)
  change (x+B*y)%B=(m+B*m)%B at cut
  simp only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (show m<B by dsimp [B]; omega)] at cut
  let t := x/B
  have xi : x=m+B*t := by simpa only [t,cut] using (Nat.mod_add_div x B).symm
  have reduced : t+y ≡ m [MOD q] := by
    apply Nat.ModEq.mul_left_cancel' (by dsimp [B]; omega : B≠0)
    apply Nat.ModEq.add_left_cancel' m
    convert congr using 1
    rw [xi]; ring
  change (t+y)%q=m%q at reduced
  rw [Nat.mod_eq_of_lt (Nat.lt_succ_self m)] at reduced
  let s := (t+y)/q
  have yi : t+y=m+q*s := by simpa only [s,reduced] using (Nat.mod_add_div (t+y) q).symm
  have vanish : t+s=0 := by
    by_contra nz
    have low := Nat.mul_le_mul_left (m+1) (Nat.one_le_iff_ne_zero.mpr nz)
    dsimp [B] at xi
    dsimp [q] at yi
    nlinarith
  obtain ⟨tz,sz⟩ := Nat.add_eq_zero_iff.mp vanish
  rw [tz,mul_zero,add_zero] at xi
  rw [tz,zero_add,sz,mul_zero,add_zero] at yi
  exact ⟨xi,yi⟩

/-- Exact least cyclic modulus for three labels prescribed equally often. -/
theorem three_equal_minimum (m : ℕ) (hm : 0 < m) :
    IsLeast {N : ℕ | 0<N ∧ ∃ a b : ZMod N, ThreeValid m a b} ((m+1)*(m+2)) := by
  constructor
  · exact ⟨by positivity,_,_,three_construct m⟩
  rintro N ⟨pos,a,b,h⟩
  have : NeZero N := ⟨pos.ne'⟩
  simpa using h.no_small_cyclic hm

private lemma three_translate (m : ℕ) (g : Fin 2 → G) :
    Valid m ![m,m] g ↔ ThreeValid m (g 0) (g 1) := by
  constructor
  · intro valid x y budget mass
    have eq := valid ![x,y] (by simp [Fin.sum_univ_two]; omega)
      (by simpa [Fin.sum_univ_two] using mass)
    exact ⟨by simpa using congrFun eq 0,by simpa using congrFun eq 1⟩
  · intro valid x budget mass
    simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one] at budget mass
    obtain ⟨h0,h1⟩ := valid (x 0) (x 1) (by omega) mass
    funext i
    fin_cases i
    · exact h0
    · exact h1

/-- Complete cyclic minimum for three arbitrary positive prescribed counts:
    the product except in the all-equal case, where the next multiple is needed. -/
theorem three_weights_minimum (m u v : ℕ) (hm : 0 < m) (hu : m≤u) (hv : m≤v) :
    IsLeast {N : ℕ | 0<N ∧ ∃ (a : ZMod N) (g : Fin 2 → ZMod N),
      TupleValid m ![u,v] a g} (if u=m ∧ v=m then (m+1)*(m+2) else (u+1)*(v+1)) := by
  classical
  split_ifs with eq
  · obtain ⟨um,vm⟩ := eq
    subst u
    subst v
    obtain ⟨⟨pos,a,b,ok⟩,lower⟩ := three_equal_minimum m hm
    constructor
    · refine ⟨pos,0,![a,b],(normalize m _ 0 _).mpr ?_⟩
      simpa using (three_translate m ![a,b]).mpr ok
    rintro N ⟨npos,p,g,valid⟩
    have z := (normalize m _ p g).mp valid
    exact lower ⟨npos,_,_,(three_translate _ _).mp z⟩
  · let w : Fin 2 → ℕ := ![u,v]
    have least (i : Fin 2) : m≤w i := by fin_cases i <;> assumption
    have unique (i j : Fin 2) (wi : w i=m) (wj : w j=m) : i=j := by
      fin_cases i <;> fin_cases j <;> simp_all [w]
    have prod : (∏ i,(w i+1))=(u+1)*(v+1) := by simp [w,Fin.prod_univ_two]
    have ok := (homogeneous_cyclic_iff m hm w least).mpr unique
    rw [prod] at ok
    refine ⟨⟨by positivity,ok⟩,?_⟩
    rintro N ⟨pos,p,g,valid⟩
    have : NeZero N := ⟨pos.ne'⟩
    rw [←prod,←ZMod.card N]
    exact order_lower ((normalize m _ p g).mp valid)

end OMA.WeightedModulus
