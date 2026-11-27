import FormalConjectures.Arxiv.«1601.03081».UniqueCrystalComponents

/-! Abrate, Barbero, Cerruti and Murru (arXiv:1601.03081, §3) classify component
pairs by a recurrence. We give a Vieta descent and count its noncubic rows.
This gives a quantitative relative-density-one uniqueness result. -/

namespace OMA.CrystalDensity
open Arxiv.«1601.03081»

/-- The two coordinates are the smaller half-component and the difference of
the half-components, for the parameter w=d+4 of the crystal recurrence. -/
def row (d : ℕ) : ℕ → ℕ × ℕ
  | 0 => (1, d+3)
  | j+1 =>
    let (x,h) := row d j
    (x+h, h+d*(x+h)+2)

def value (d j : ℕ) : ℕ :=
  let (x,h) := row d j
  (2*x-1)*(2*(x+h)-1)

private theorem descent (d : ℕ) : ∀ x y : ℕ, 0<x → x≤y →
    (x+y)^2+1=(d+4)*x*y+2*(x+y) →
    ∃ j, (row d j).1=x ∧ (row d j).1+(row d j).2=y := by
  intro x
  induction x using Nat.strong_induction_on with
  | h x ih =>
    intro y hx hxy eq
    by_cases one : x=1
    · subst x
      have e : y*y = (d+4)*y := by nlinarith only [eq]
      have ey : y=d+4 := Nat.eq_of_mul_eq_mul_right (by omega) e
      exact ⟨0,rfl,by simp [row]; omega⟩
    · let z : ℤ := ((d:ℤ)+2)*x+2-y
      have e : ((x:ℤ)+y)^2+1 = ((d:ℤ)+4)*x*y+2*(x+y) := by exact_mod_cast eq
      have yz : (y:ℤ)*z=((x:ℤ)-1)^2 := by dsimp [z]; nlinarith only [e]
      have pos : 0<z := by
        have : 0 < (y:ℤ)*z := by rw [yz]; exact sq_pos_of_pos (by omega)
        exact pos_of_mul_pos_right this (by positivity)
      have lt : z<x := by
        by_contra! le
        have h := mul_le_mul (show (x:ℤ)≤y by exact_mod_cast hxy) le (by positivity)
          (show (0:ℤ)≤y by positivity)
        nlinarith only [h,yz,show (1:ℤ)<x by omega]
      have back : (z.toNat:ℤ)=z := Int.toNat_of_nonneg pos.le
      have ze : (z.toNat+x)^2+1=(d+4)*z.toNat*x+2*(z.toNat+x) := by
        rw [← Nat.cast_inj (R := ℤ)]
        push_cast
        rw [back]
        dsimp [z]
        nlinarith only [e]
      obtain ⟨j, hj, hnext⟩ := ih z.toNat (by omega) x (by omega) (by omega) ze
      refine ⟨j+1, by simpa [row] using hnext, ?_⟩
      simp only [row, hnext]
      have zsum : z.toNat+y=(d+2)*x+2 := by
        rw [← Nat.cast_inj (R := ℤ)]
        push_cast
        rw [back]
        dsimp [z]
        ring
      nlinarith only [hj,hnext,zsum]

private theorem encode {n a b : ℕ} (h : IsCrystalWithComponents n a b) (ord : a≤b) :
    (n=35 ∧ a=5 ∧ b=7) ∨ ∃ d j, 1≤j ∧ n=value d j ∧
      a=2*(row d j).1-1 ∧ b=2*((row d j).1+(row d j).2)-1 ∧
      (a+b)^2=(d+4)*((a+1)*(b+1)) := by
  obtain ⟨hn, ha, hb, prod, q, hq⟩ :=
    (isCrystalWithComponents_iff_sum_sq_dvd n a b).mp h
  obtain ⟨u, hu⟩ := Nat.Odd.of_mul_left (prod ▸ hn)
  obtain ⟨v, hv⟩ := Nat.Odd.of_mul_right (prod ▸ hn)
  let x := u+1
  let y := v+1
  have hx : 1<x := by dsimp [x]; omega
  have hxy : x≤y := by dsimp [x,y]; omega
  have e : (x+y)^2+1=q*x*y+2*(x+y) := by dsimp [x,y]; rw [hu,hv] at hq; nlinarith only [hq]
  by_cases sm : q<4
  · have eqZ : ((x:ℤ)+y)^2+1=(q:ℤ)*x*y+2*(x+y) := by exact_mod_cast e
    have ub : (q:ℤ)*x*y≤3*x*y := by gcongr; omega
    have hy : y≤4 := by
      by_contra! hlarge
      have hpos : 0<(y:ℤ)*(y-4) := mul_pos (by omega) (by omega)
      nlinarith only [sq_nonneg (2*(x:ℤ)-y-2),hpos,eqZ,ub]
    have only : x=3 ∧ y=4 := by
      have xb : x≤4 := hxy.trans hy
      have finite : ∀ x y q : Fin 5, 2≤x.val → x.val≤y.val → q.val<4 →
          (x.val+y.val)^2+1=q.val*x.val*y.val+2*(x.val+y.val) →
          x.val=3 ∧ y.val=4 := by decide
      exact finite ⟨x,by omega⟩ ⟨y,by omega⟩ ⟨q,by omega⟩ hx hxy sm e
    have : a=5 := by dsimp [x] at only; omega
    have : b=7 := by dsimp [y] at only; omega
    exact Or.inl (by simp_all)
  · obtain ⟨j,hj,hnext⟩ := descent (q-4) x y (by omega) hxy (by simpa [show q-4+4=q by omega] using e)
    have aa : a=2*(row (q-4) j).1-1 := by rw [hj]; dsimp [x]; omega
    have bb : b=2*((row (q-4) j).1+(row (q-4) j).2)-1 := by rw [hnext]; dsimp [y]; omega
    refine Or.inr ⟨q-4,j,?_,by simpa [value,aa,bb] using prod,aa,bb,by
      rw [show q-4+4=q by omega, mul_comm q]; exact hq⟩
    by_contra! hzero
    have : j=0 := by omega
    simp [this,row] at hj
    omega

private theorem row_pos (d j : ℕ) : 0<(row d j).1 := by
  induction j with
  | zero => simp [row]
  | succ j ih => simp only [row]; omega

private theorem val_lb (d j : ℕ) : (row d j).1*((row d j).1+(row d j).2) ≤ value d j := by
  unfold value
  apply Nat.mul_le_mul <;> have := row_pos d j <;> omega

private theorem row_mono (d : ℕ) : Monotone (value d) := by
  apply monotone_nat_of_le_succ
  intro j
  simp only [value,row]
  apply Nat.mul_le_mul <;> omega

private theorem row_zero (j : ℕ) :
    row 0 j=((j+1)^2,2*j+3) := by
  induction j with
  | zero => rfl
  | succ j ih => simpa [row,ih,Prod.mk.injEq] using
      (show (j+1)^2+(2*j+3)=(j+1+1)^2 ∧ 2*j+3+2=2*(j+1)+3 from ⟨by ring,by ring⟩)

private theorem parabolic_lb (j : ℕ) : j^4≤value 0 j := by
  apply le_trans _ (val_lb 0 j)
  rw [row_zero]
  dsimp
  ring_nf
  omega

private theorem five_lb (d j : ℕ) (hj : 2≤j) : d^5≤value d j := by
  apply le_trans _ (row_mono d hj)
  apply le_trans _ (val_lb d 2)
  simp only [row]
  ring_nf
  omega

private theorem growth (d : ℕ) (hd : 0<d) (j : ℕ) :
    2^j≤(row d j).1 ∧ (row d j).1≤(row d j).2 := by
  induction j with
  | zero => simp [row]
  | succ j ih =>
    simp only [row, pow_succ]
    have h := Nat.le_mul_of_pos_left ((row d j).1+(row d j).2) hd
    omega

private theorem index_lb (d j : ℕ) (hd : 0<d) : 2^j≤value d j := by
  apply (growth d hd j).1.trans
  apply le_trans _ (val_lb d j)
  apply Nat.le_mul_of_pos_right
  have := row_pos d j
  omega

/-- The classification needed in the uniqueness reduction. -/
theorem classify {n a b : ℕ} (h : IsCrystalWithComponents n a b) (ord : a≤b) :
    (a=5 ∧ b=7) ∨ (∃ d : ℕ, a=2*d+7 ∧ b=2*d^2+12*d+17) ∨
    (∃ j : ℕ, a=2*j^2+4*j+1 ∧ b=2*j^2+8*j+7) ∨
    ∃ q : ℕ, 5≤q ∧ 2*q<a ∧ (a+b)^2=q*((a+1)*(b+1)) := by
  rcases encode h ord with h | ⟨d,j,hj,_,aa,bb,qq⟩
  · exact Or.inl h.2
  right
  by_cases j1 : j=1
  · subst j
    refine Or.inl ⟨d,?_,?_⟩
    · simp [row] at aa; omega
    · simp [row] at bb; ring_nf at bb ⊢; omega
  right
  by_cases d0 : d=0
  · subst d
    rw [row_zero] at aa bb
    simp only at aa bb
    refine Or.inl ⟨j,?_,?_⟩ <;> ring_nf at aa bb ⊢ <;> omega
  right
  refine ⟨d+4,by omega,?_,qq⟩
  have first_mono : Monotone (fun i => (row d i).1) := by
    apply monotone_nat_of_le_succ
    intro i; simp [row]
  have lo := first_mono (show 2≤j by omega)
  change (row d 2).1 ≤ (row d j).1 at lo
  simp [row] at lo
  ring_nf at lo
  omega

private theorem cubic (d : ℕ) :
    value d 1=(2*d+7)*(2*d^2+12*d+17) := by
  simp [value,row]
  grind only [Nat.sub_add_cancel]

private theorem cubic_strict : StrictMono (fun d => value d 1) := by
  apply strictMono_nat_of_lt_succ
  intro d
  rw [cubic,cubic]
  nlinarith

/-- Two genuinely different unordered component pairs. -/
def Bad (n : ℕ) : Prop := ∃ a b c e, IsCrystalWithComponents n a b ∧ a≤b ∧
  IsCrystalWithComponents n c e ∧ c≤e ∧ a≠c

/-- The first (cubic) row cannot collide with itself. -/
private theorem bad_rows {n : ℕ} (hn : Bad n) : n=35 ∨ ∃ d j, 2≤j ∧ n=value d j := by
  obtain ⟨a,b,c,e,hab,ord,hce,ord',ne⟩ := hn
  rcases encode hab ord with h | ⟨d,j,hj,eq,aa,_⟩
  · exact Or.inl h.1
  rcases encode hce ord' with h | ⟨D,J,hJ,EQ,cc,_⟩
  · exact Or.inl h.1
  right
  by_cases hj' : 2≤j
  · exact ⟨d,j,hj',eq⟩
  by_cases hJ' : 2≤J
  · exact ⟨D,J,hJ',EQ⟩
  have : j=1 := by omega
  have : J=1 := by omega
  subst j J
  have same := cubic_strict.injective (eq.symm.trans EQ)
  subst D
  exact False.elim (ne (aa.trans cc.symm))

open Finset

noncomputable def exceptions (N : ℕ) : Finset ℕ := by
  classical exact (range (N+1)).filter Bad

noncomputable def crystals (N : ℕ) : Finset ℕ := by
  classical exact (range (N+1)).filter (fun n => ∃ a b, IsCrystalWithComponents n a b)

theorem exceptional_bound {N t : ℕ} (ht : 1≤t) (hN : N≤t^60) :
    (exceptions N).card≤125*t^15 := by
  classical
  let P := (range (t^15+1)).image (value 0)
  let Q := ((range (t^12+1)) ×ˢ (range (60*t+1))).image (fun p => value p.1 p.2)
  have incl : exceptions N ⊆ insert 35 (P∪Q) := by
    intro n hn
    obtain ⟨hr,hbad⟩ := mem_filter.mp hn
    have hnx : n ≤ t^60 := (Nat.le_of_lt_succ (mem_range.mp hr)).trans hN
    rcases bad_rows hbad with h | ⟨d,j,hj,rfl⟩
    · simp [h]
    apply mem_insert_of_mem
    by_cases hd : d=0
    · subst d
      apply mem_union_left
      apply mem_image.mpr ⟨j,mem_range.mpr (Nat.lt_succ_of_le ?_),rfl⟩
      apply (Nat.pow_le_pow_iff_left (by decide : 4≠0)).mp
      simpa only [← pow_mul] using (parabolic_lb j).trans hnx
    · apply mem_union_right
      apply mem_image.mpr ⟨(d,j),mem_product.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le ?_),
        mem_range.mpr (Nat.lt_succ_of_le ?_)⟩,rfl⟩
      · apply (Nat.pow_le_pow_iff_left (by decide : 5≠0)).mp
        simpa only [← pow_mul] using (five_lb d j hj).trans hnx
      · apply (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp
        calc
          2^j ≤ t^60 := (index_lb d j (by omega)).trans hnx
          _ ≤ (2^t)^60 := Nat.pow_le_pow_left (Nat.le_of_lt (Nat.lt_two_pow_self (n:=t))) _
          _ = 2^(60*t) := by rw [← pow_mul,Nat.mul_comm]
  have psize : P.card≤t^15+1 := (card_image_le).trans_eq (card_range _)
  have qsize : Q.card≤(t^12+1)*(60*t+1) :=
    card_image_le.trans_eq (by simp)
  have bc := (Finset.card_le_card incl).trans (Finset.card_insert_le ..)
  have bu := Finset.card_union_le P Q
  have h13 : t^13≤t^15 := Nat.pow_le_pow_right ht (by decide)
  have h12 : t^12≤t^15 := Nat.pow_le_pow_right ht (by decide)
  have h1 : t≤t^15 := by simpa using (Nat.pow_le_pow_right ht (by decide : 1≤15))
  have hp : 0<t^15 := by positivity
  ring_nf at qsize
  omega

private theorem cubic_valid (d : ℕ) :
    ∃ a b, IsCrystalWithComponents (value d 1) a b := by
  rw [cubic]
  use 2*d+7,2*d^2+12*d+17
  apply (isCrystalWithComponents_iff_sum_sq_dvd ..).mpr
  refine ⟨?_,by omega,by omega,rfl,d+4,by ring⟩
  apply Odd.mul
  · exact ⟨d+3,by omega⟩
  · exact ⟨d^2+6*d+8,by omega⟩

theorem plentiful {N t : ℕ} (hN : t^60≤N) :
    t^20/10≤(crystals N).card := by
  classical
  let A := (range (t^20/10)).image (fun d => value d 1)
  have incl : A ⊆ crystals N := by
    intro n hn
    obtain ⟨d,hd,rfl⟩ := mem_image.mp hn
    apply mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le ?_),cubic_valid d⟩
    apply le_trans _ hN
    have b : 10*(d+1)≤t^20 := by have := mem_range.mp hd; omega
    have e := Nat.pow_le_pow_left b 3
    rw [← pow_mul] at e
    apply le_trans _ e
    rw [cubic]
    ring_nf
    omega
  have size : A.card=t^20/10 := by
    dsimp [A]
    rw [card_image_of_injective _ cubic_strict.injective,card_range]
  exact size ▸ card_le_card incl

open Filter

set_option maxHeartbeats 700000 in
/-- Almost every crystal, relative to the set of crystals, has unique components. -/
theorem density_one : Tendsto (fun n : ℕ =>
    ((exceptions n).card:ℝ)/(crystals n).card) atTop (nhds 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let C : ℕ := 125*2^15*20
  obtain ⟨M,hM⟩ := exists_nat_gt ((C:ℝ)/ε)
  use (M+20)^60
  intro n hn
  obtain ⟨t,tl,tu⟩ : ∃ t : ℕ, t^60≤n ∧ n<(t+1)^60 :=
    ⟨Nat.nthRoot 60 n,Nat.pow_nthRoot_le (.inl (by decide)),Nat.lt_pow_nthRoot_add_one (by decide) n⟩
  have mt : M+20≤t := by
    by_contra! lt
    have := Nat.pow_le_pow_left (show t+1≤M+20 by omega) 60
    omega
  have ht : 1≤t := by omega
  have e := exceptional_bound (t:=t+1) (by omega) tu.le
  have e' : (exceptions n).card≤(125*2^15)*t^15 := by
    have bnd := Nat.pow_le_pow_left (show t+1≤2*t by omega) 15
    rw [mul_pow] at bnd
    exact e.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 125 bnd)
  have t20 : t^20/10≤(crystals n).card := plentiful tl
  have t20big : 20≤t^20 := by
    have : t^1≤t^20 := Nat.pow_le_pow_right ht (by decide)
    simp only [pow_one] at this
    omega
  have cl : t^20≤20*(crystals n).card := by omega
  have pos : 0<(crystals n).card := by omega
  have eb : (exceptions n).card*t≤C*(crystals n).card := by
    calc
      _ ≤ (125*2^15)*(t^15*t) := by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right t e'
      _ ≤ (125*2^15)*t^20 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right ht (by decide : 16≤20))
      _ ≤ (125*2^15)*(20*(crystals n).card) := Nat.mul_le_mul_left _ cl
      _ = _ := by unfold C; ring
  have ep : (0:ℝ)<(crystals n).card := by exact_mod_cast pos
  have tp : (0:ℝ)<t := by exact_mod_cast (show 0<t by omega)
  have ebr : ((exceptions n).card:ℝ)/(crystals n).card ≤ (C:ℝ)/t :=
    (div_le_div_iff₀ ep tp).mpr (by exact_mod_cast eb)
  have cu : (C:ℝ)/t<ε := by
    apply (div_lt_iff₀ tp).mpr
    have h := (div_lt_iff₀ hε).mp hM
    have tm : (M:ℝ)≤t := by exact_mod_cast (show M≤t by omega)
    calc
      (C:ℝ) < (M:ℝ)*ε := h
      _ ≤ ε*t := by simpa [mul_comm] using mul_le_mul_of_nonneg_right tm hε.le
  simpa only [Real.dist_eq,sub_zero,abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) ep.le)]
    using ebr.trans_lt cu

private theorem seventh (d j : ℕ) (hj : 3≤j) : d^7≤value d j := by
  apply le_trans _ (row_mono d hj)
  apply le_trans _ (val_lb d 3)
  simp only [row]
  ring_nf
  omega

/-- All rows contributing to the remaining open case. -/
noncomputable def sparse (N : ℕ) : Finset ℕ := by
  classical exact (range (N+1)).filter (fun n => ∃ d j, 0<d ∧ 2≤j ∧ n=value d j)

/-- The number of sparse candidates below X is O(X^(1/5)). Index 2 gives
the fifth-root term; all indices from 3 onward give O(X^(1/7) log X). -/
theorem sparse_bound {N t : ℕ} (ht : 1≤t) (hN : N≤t^35) :
    (sparse N).card≤75*t^7 := by
  classical
  let P := (range (t^7+1)).image (fun d => value d 2)
  let Q := ((range (t^5+1)) ×ˢ (range (35*t+1))).image (fun p => value p.1 p.2)
  have incl : sparse N ⊆ P∪Q := by
    intro n hn
    obtain ⟨hr,d,j,hd,hj,rfl⟩ := mem_filter.mp hn
    have hnx : value d j≤t^35 := (Nat.le_of_lt_succ (mem_range.mp hr)).trans hN
    by_cases jj : j=2
    · subst j
      apply mem_union_left
      apply mem_image.mpr ⟨d,mem_range.mpr (Nat.lt_succ_of_le ?_),rfl⟩
      apply (Nat.pow_le_pow_iff_left (by decide : 5≠0)).mp
      simpa only [← pow_mul] using (five_lb d 2 hj).trans hnx
    · apply mem_union_right
      apply mem_image.mpr ⟨(d,j),mem_product.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le ?_),
        mem_range.mpr (Nat.lt_succ_of_le ?_)⟩,rfl⟩
      · apply (Nat.pow_le_pow_iff_left (by decide : 7≠0)).mp
        simpa only [← pow_mul] using (seventh d j (by omega)).trans hnx
      · apply (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp
        calc
          2^j ≤ t^35 := (index_lb d j hd).trans hnx
          _ ≤ (2^t)^35 := Nat.pow_le_pow_left (Nat.le_of_lt (Nat.lt_two_pow_self (n:=t))) _
          _ = 2^(35*t) := by rw [← pow_mul,Nat.mul_comm]
  have psize : P.card≤t^7+1 := card_image_le.trans_eq (card_range _)
  have qsize : Q.card≤(t^5+1)*(35*t+1) := card_image_le.trans_eq (by simp)
  have bu := (Finset.card_le_card incl).trans (Finset.card_union_le P Q)
  have h6 : t^6≤t^7 := Nat.pow_le_pow_right ht (by decide)
  have h5 : t^5≤t^7 := Nat.pow_le_pow_right ht (by decide)
  have h1 : t≤t^7 := by simpa using (Nat.pow_le_pow_right ht (by decide : 1≤7))
  have hp : 0<t^7 := by positivity
  ring_nf at qsize
  omega

theorem parabolic (j : ℕ) :
    value 0 j=(2*j^2+4*j+1)*(2*j^2+8*j+7) := by
  unfold value
  rw [row_zero]
  dsimp
  congr 1 <;> ring_nf <;> omega

private theorem para_strict : StrictMono (value 0) := by
  apply strictMono_nat_of_lt_succ
  intro j
  rw [parabolic,parabolic]
  ring_nf
  omega

private theorem min35 {a b : ℕ} (h : IsCrystalWithComponents 35 a b) (ord : a≤b) : a=5 := by
  obtain ⟨_,ha,_,prod,_⟩ := h
  have sq : a*a≤35 := by rw [prod]; exact Nat.mul_le_mul_left _ ord
  have bound : a≤5 := by nlinarith
  interval_cases a <;> omega

theorem fifth_bound
    (cross : ∀ d j : ℕ, (2*d+7)*(2*d^2+12*d+17)=(2*j^2+4*j+1)*(2*j^2+8*j+7) →
      d=0 ∧ j=1)
    {N t : ℕ} (ht : 1≤t) (hN : N≤t^35) :
    (exceptions N).card≤75*t^7 := by
  classical
  apply le_trans _ (sparse_bound ht hN)
  apply card_le_card
  intro n hn
  obtain ⟨hr,a,b,c,e,hab,ab,hce,ce,ne⟩ := mem_filter.mp hn
  apply mem_filter.mpr ⟨hr,?_⟩
  by_contra! no
  by_cases h35 : n=35
  · subst n
    exact ne ((min35 hab ab).trans (min35 hce ce).symm)
  rcases encode hab ab with h | ⟨d,j,hj,eq,aa,_⟩
  · exact h35 h.1
  rcases encode hce ce with h | ⟨D,J,hJ,EQ,cc,_⟩
  · exact h35 h.1
  have side : ∀ w k, 1≤k → n=value w k → k=1 ∨ w=0 := by
    intro w k hk heq
    by_contra! h
    exact no w k (by omega) (by omega) heq
  obtain h|h := side d j hj eq <;> obtain H|H := side D J hJ EQ
  · subst j J
    have := cubic_strict.injective (eq.symm.trans EQ)
    grind
  · subst j D
    have same := eq.symm.trans EQ
    rw [cubic,parabolic] at same
    obtain ⟨rfl,rfl⟩ := cross d J same
    exact ne (aa.trans cc.symm)
  · subst d J
    have same := EQ.symm.trans eq
    rw [cubic,parabolic] at same
    obtain ⟨rfl,rfl⟩ := cross D j same
    exact ne (aa.trans cc.symm)
  · subst d D
    have := para_strict.injective (eq.symm.trans EQ)
    grind

private noncomputable def family (F : ℕ→ℕ) (N : ℕ) : Finset ℕ := by
  classical exact (range (N+1)).filter (fun n => ∃ j, F j=n)

private theorem family_count {F : ℕ→ℕ} {k s N : ℕ} (hk : k≠0) (inj : Function.Injective F)
    (growth : ∀ i, 4*i^k≤F i ∧ F i≤4*(i+s)^k) :
    Nat.nthRoot k (N/4)+1 ≤ (family F N).card+s ∧ (family F N).card≤Nat.nthRoot k (N/4)+1 := by
  classical
  let r := Nat.nthRoot k (N/4)
  have lo : (range (r+1-s)).image F ⊆ family F N := by
    rintro n hn
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hn
    have cutoff : (j+s)^k≤N/4 := (Nat.le_nthRoot_iff hk).mp (by have := mem_range.mp hj; omega)
    have e := (growth j).2
    exact mem_filter.mpr ⟨mem_range.mpr (by omega),⟨j,rfl⟩⟩
  have hi : family F N ⊆ (range (r+1)).image F := by
    rintro n hn
    obtain ⟨hr,j,rfl⟩ := mem_filter.mp hn
    have h := mem_range.mp hr
    have e := (growth j).1
    have cut : j≤r := (Nat.le_nthRoot_iff hk).mpr (by omega)
    exact mem_image.mpr ⟨j,mem_range.mpr (by omega),rfl⟩
  have lower := card_le_card lo
  have upper := card_le_card hi
  rw [card_image_of_injective _ inj,card_range] at lower upper
  change r+1≤_ ∧ _≤r+1
  omega

private theorem valid_parabolic (j : ℕ) :
    ∃ a b, IsCrystalWithComponents (value 0 (j+1)) a b := by
  rw [parabolic]
  use 2*(j+1)^2+4*(j+1)+1,2*(j+1)^2+8*(j+1)+7
  apply (isCrystalWithComponents_iff_sum_sq_dvd ..).mpr
  refine ⟨?_,by nlinarith,by omega,rfl,4,by ring⟩
  apply Odd.mul
  · exact ⟨(j+1)^2+2*(j+1),by omega⟩
  · exact ⟨(j+1)^2+4*(j+1)+3,by omega⟩

/-- Two-term counting law: the main terms are floor((N/4)^(1/3)) and
floor((N/4)^(1/4)). The error is O(N^(1/5)), subject only to the known
integral-point calculation on 2432.a1 (which implies the stated cross lemma). -/
theorem two_term
    (cross : ∀ d j : ℕ, (2*d+7)*(2*d^2+12*d+17)=(2*j^2+4*j+1)*(2*j^2+8*j+7) →
      d=0 ∧ j=1)
    {N t : ℕ} (ht : 1≤t) (hN : N≤t^35) :
    let main := Nat.nthRoot 3 (N/4)+Nat.nthRoot 4 (N/4)
    main ≤ (crystals N).card+7 ∧ (crystals N).card ≤ main+75*t^7+3 := by
  classical
  let C := family (fun d => value d 1) N
  let P := family (fun i => value 0 (i+1)) N
  have ccount := family_count (s:=4) (N:=N) (by decide : 3≠0) cubic_strict.injective (by
    intro i; rw [cubic]; constructor <;> ring_nf <;> omega)
  have pinc : StrictMono (fun i => value 0 (i+1)) := fun _ _ h => para_strict (by omega)
  have pcount := family_count (s:=4) (N:=N) (by decide : 4≠0) pinc.injective (by
    intro i; rw [parabolic]; constructor <;> ring_nf <;> omega)
  change Nat.nthRoot 3 (N/4)+1≤C.card+4 ∧ C.card≤_ at ccount
  change Nat.nthRoot 4 (N/4)+1≤P.card+4 ∧ P.card≤_ at pcount
  have low : C∪P ⊆ crystals N := by
    intro n hn
    rcases mem_union.mp hn with ch|ph
    · obtain ⟨nr,d,rfl⟩ := mem_filter.mp ch
      exact mem_filter.mpr ⟨nr,cubic_valid d⟩
    · obtain ⟨nr,j,rfl⟩ := mem_filter.mp ph
      exact mem_filter.mpr ⟨nr,valid_parabolic j⟩
  have inter : C∩P ⊆ {119} := by
    intro n hn
    obtain ⟨_,d,cd⟩ := mem_filter.mp (mem_inter.mp hn).1
    obtain ⟨_,j,pj⟩ := mem_filter.mp (mem_inter.mp hn).2
    have eq : value d 1 = value 0 (j+1) := cd.trans pj.symm
    rw [cubic,parabolic] at eq
    obtain ⟨rfl,_⟩ := cross d (j+1) eq
    exact mem_singleton.mpr cd.symm
  have upper : crystals N ⊆ insert 35 ((C∪P)∪sparse N) := by
    intro n hn
    obtain ⟨nr,a,b,h⟩ := mem_filter.mp hn
    have hencode : ∀ a b, IsCrystalWithComponents n a b → a≤b → n∈insert 35 ((C∪P)∪sparse N) := by
      intro u v h uv
      rcases encode h uv with small|⟨d,j,jpos,eq,_,_⟩
      · simp [small.1]
      apply mem_insert_of_mem
      by_cases j1 : j=1
      · subst j; exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨nr,⟨d,eq.symm⟩⟩))
      by_cases d0 : d=0
      · subst d
        exact mem_union_left _ (mem_union_right _ (mem_filter.mpr
          ⟨nr,⟨j-1,by simpa [show j-1+1=j by omega] using eq.symm⟩⟩))
      exact mem_union_right _ (mem_filter.mpr ⟨nr,d,j,by omega,by omega,eq⟩)
    rcases le_total a b with ord|ord
    · exact hencode a b h ord
    · apply hencode b a _ ord
      obtain ⟨odd,ha,hb,p,dvd⟩ := (isCrystalWithComponents_iff_sum_sq_dvd ..).mp h
      exact (isCrystalWithComponents_iff_sum_sq_dvd ..).mpr
        ⟨odd,hb,ha,by simpa only [mul_comm] using p,by simpa only [add_comm,mul_comm] using dvd⟩
  have low' := card_le_card low
  have i' : (C∩P).card≤1 := (card_le_card inter).trans_eq (card_singleton _)
  have sum := card_union_add_card_inter C P
  have upp := (card_le_card upper).trans (card_insert_le ..)
  have summ := card_union_le (C∪P) (sparse N)
  have sp := sparse_bound ht hN
  dsimp
  omega

end OMA.CrystalDensity
