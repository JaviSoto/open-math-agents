import FormalConjectures.Arxiv.«1601.03081».UniqueCrystalComponents

/-! An independent exclusion on the full crystal-uniqueness question:
two distinct decompositions cannot have parameters in the same square class. -/

namespace OMA.CrystalSquareClass
open Arxiv.«1601.03081»

/- Given the sorted half-components x,y, Vieta gives a positive integer
z with yz=(x-1)^2. Hence y≤(x-1)^2 and the parameter is at most x. -/
private theorem half_bound {x y q : ℤ} (hx : 1<x) (hy : x≤y)
    (e : (x+y-1)^2=q*x*y) : q≤x := by
  let z := (q-2)*x+2-y
  have f : y*z=(x-1)^2 := by dsimp [z]; nlinarith only [e]
  have hz : 0<z := by
    have p : 0<y*z := by rw [f]; exact sq_pos_of_pos (by omega)
    exact pos_of_mul_pos_right p (by omega)
  have cap : y≤(x-1)^2 := by
    rw [← f]
    exact le_mul_of_one_le_right (by omega) (by omega)
  have diff := mul_nonneg (show 0≤y-1 by omega) (sub_nonneg.mpr cap)
  have v : q*(x*y)≤x*(x*y) := by nlinarith only [e,diff]
  exact le_of_mul_le_mul_right v (mul_pos (by omega) (by omega))

theorem size {n a b q : ℕ} (h : IsCrystalWithComponents n a b) (ord : a≤b)
    (eq : (a+b)^2=q*((a+1)*(b+1))) : q^2 ≤ a+b := by
  obtain ⟨odd,ha,hb,prod,_⟩ := h
  obtain ⟨u, hu⟩ := Nat.Odd.of_mul_left (prod ▸ odd)
  obtain ⟨v, hv⟩ := Nat.Odd.of_mul_right (prod ▸ odd)
  have ez : ((a:ℤ)+b)^2=(q:ℤ)*((a+1)*(b+1)) := by exact_mod_cast eq
  have hu' : (a:ℤ)=2*u+1 := by exact_mod_cast hu
  have hv' : (b:ℤ)=2*v+1 := by exact_mod_cast hv
  have e : ((u:ℤ)+1+(v+1)-1)^2=(q:ℤ)*(u+1)*(v+1) := by
    rw [hu',hv'] at ez
    nlinarith only [ez]
  have hq := half_bound (x:=(u:ℤ)+1) (y:=(v:ℤ)+1) (by omega) (by omega) e
  have qa : 2*q≤a+1 := by omega
  have qb : a+b≤2*(b+1) := by omega
  have mult := Nat.mul_le_mul qa qb
  have ord' : q*(a+b)≤(a+1)*(b+1) := by nlinarith only [mult]
  have v' := Nat.mul_le_mul_left q ord'
  have v'' : q^2*(a+b)≤(a+b)*(a+b) := by nlinarith only [v',eq]
  exact Nat.le_of_mul_le_mul_right v'' (by omega)

private theorem almost_square {n a b s A : ℕ} (h : IsCrystalWithComponents n a b) (ord : a≤b)
    (hs : 0<s) (hA : 0<A) (eq : (a+b)^2=(s*A^2)*((a+1)*(b+1))) :
    ∃ U : ℕ, U^2=4*s*(n+1)+(s*A)^2 ∧ (s*A)^2≤U := by
  have big := size h ord eq
  let S := a+b
  have dvd' : A^2 ∣ S^2 := by
    use s*((a+1)*(b+1))
    dsimp [S]; rw [eq]; ring
  obtain ⟨t,ht⟩ := (Nat.pow_dvd_pow_iff (by decide : 2≠0)).mp dvd'
  have eq' : A^2*t^2=A^2*(s*((a+1)*(b+1))) := by
    calc
      A^2*t^2 = S^2 := by rw [ht]; ring
      _ = _ := by dsimp [S]; rw [eq]; ring
  have ts := Nat.eq_of_mul_eq_mul_left (pow_pos hA 2) eq'
  have lo : (s*A)^2 ≤ t := by
    have bnd : A*((s*A)^2*A)≤A*t := by rw [←ht]; dsimp [S]; nlinarith only [big]
    have l := Nat.le_of_mul_le_mul_left bnd hA
    exact (Nat.le_mul_of_pos_right _ hA).trans l
  have sa : 0<s*A := Nat.mul_pos hs hA
  have sa' : s*A≤t := by
    apply le_trans _ lo
    simpa [pow_two] using Nat.le_mul_of_pos_right (s*A) sa
  let U := 2*t-s*A
  have ud : U+s*A=2*t := by dsimp [U]; omega
  refine ⟨U,?_,by omega⟩
  have p := h.2.2.2.1
  have ds : (a+1)*(b+1)=n+1+A*t := by rw [←ht]; dsimp [S]; nlinarith only [p]
  rw [ds] at ts
  have sq := congrArg (fun z : ℕ => z^2) ud
  have mul' := congrArg (fun z : ℕ => z*(2*s*A)) ud
  nlinarith only [sq,mul',ts]

private theorem square_gap {u v : ℕ} (h : u<v) : u^2+u+v≤v^2 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le h.le
  cases k with
  | zero => omega
  | succ k => ring_nf; omega

private theorem floor_unique {u v a b N : ℕ}
    (hu : u^2=N+a) (hv : v^2=N+b) (ha : a≤u) (hb : b≤v) :
    0<N → u=v := by
  intro positive
  have up : 0<u := by by_contra! z; simp [Nat.eq_zero_of_le_zero z] at hu; omega
  have vp : 0<v := by by_contra! z; simp [Nat.eq_zero_of_le_zero z] at hv; omega
  rcases lt_trichotomy u v with h|h|h
  · have := square_gap h
    omega
  · exact h
  · have := square_gap h
    omega

theorem same_class {n a b c e s A B : ℕ}
    (h : IsCrystalWithComponents n a b) (ab : a≤b)
    (H : IsCrystalWithComponents n c e) (ce : c≤e)
    (hs : 0<s) (hA : 0<A) (hB : 0<B)
    (eq : (a+b)^2=(s*A^2)*((a+1)*(b+1)))
    (EQ : (c+e)^2=(s*B^2)*((c+1)*(e+1))) : a=c ∧ b=e := by
  obtain ⟨U,hu,lu⟩ := almost_square h ab hs hA eq
  obtain ⟨V,hv,lv⟩ := almost_square H ce hs hB EQ
  have uv := floor_unique hu hv lu lv (by positivity)
  subst V
  have sy : (s*A)^2=(s*B)^2 := by omega
  have : A=B := Nat.eq_of_mul_eq_mul_left hs (Nat.pow_left_injective (by decide : 2≠0) sy)
  subst B
  have p := h.2.2.2.1
  have P := H.2.2.2.1
  let q := s*A^2
  let S := a+b
  let T := c+e
  have es : S^2=q*(n+1+S) := by dsimp [q,S]; rw [eq]; congr 1; nlinarith only [p]
  have et : T^2=q*(n+1+T) := by dsimp [q,T]; rw [EQ]; congr 1; nlinarith only [P]
  have l := size h ab eq
  have L := size H ce EQ
  have qpos : 0<q := by dsimp [q]; positivity
  have qle : q≤S := (by simpa [pow_two] using (Nat.le_mul_of_pos_right q qpos) : q≤q^2).trans l
  have tpos : 0<T := by dsimp [T]; have := H.2.1; omega
  have de : ((S:ℤ)-T)*(S+T-q)=0 := by
    have es' : (S:ℤ)^2=q*(n+1+S) := by exact_mod_cast es
    have et' : (T:ℤ)^2=q*(n+1+T) := by exact_mod_cast et
    nlinarith only [es',et']
  rcases mul_eq_zero.mp de with zero|zero
  · have sum : a+b=c+e := by change S=T; omega
    have f : ((a:ℤ)-c)*(a-e)=0 := by
      have sZ : (a:ℤ)+b=c+e := by exact_mod_cast sum
      have pZ : (a:ℤ)*b=c*e := by exact_mod_cast p.symm.trans P
      nlinarith only [pZ,congrArg (fun z : ℤ => (a:ℤ)*z) sZ]
    rcases mul_eq_zero.mp f with hh|hh <;> omega
  · omega

end OMA.CrystalSquareClass

/- Algebra and the quantitative approximation for complementary
parameter squareclasses in a prospective crystal collision. -/
namespace OMA.CrystalComplement

/-- If dQ is a square and Q is a second parameter, then d times the
square root appearing in its comparison with the first parameter is integral. -/
theorem integer_companion {n S Q d A : ℕ} (hQ : 0<Q) (hle : Q≤2*S)
    (e : S^2=Q*(n+1+S)) (sq : d*Q=A^2) :
    ∃ v : ℕ, v^2=d^3*(4*(n+1)+Q) := by
  let m := 2*S-Q
  have mdef : m+Q=2*S := by dsimp [m]; omega
  have msq : m^2=Q*(4*(n+1)+Q) := by
    have a := congrArg (fun t : ℕ => t^2) mdef
    have b := congrArg (fun t : ℕ => t*(2*Q)) mdef
    nlinarith only [e,a,b]
  have eq : (A*m)^2=Q^2*(d*(4*(n+1)+Q)) := by
    rw [mul_pow, ←sq, msq]; ring
  have dvdSq : Q^2 ∣ (A*m)^2 := ⟨_,eq⟩
  obtain ⟨t,ht⟩ := (Nat.pow_dvd_pow_iff (by decide : 2≠0)).mp dvdSq
  rw [ht,mul_pow] at eq
  have tsq := Nat.eq_of_mul_eq_mul_left (pow_pos hQ 2) eq
  exact ⟨d*t,by rw [mul_pow,tsq]; ring⟩

/-- The exact rationalized identity, valid for any positive real data
satisfying the crystal component and difference equations. -/
theorem pell {q d n S D : ℝ} (hq : 0<q) (hd : 0<d) (hn : 0≤n)
    (de : d=q-4) (es : S^2=q*(n+1+S)) (ed : D^2=S^2-4*n)
    (hs : q≤2*S) :
    (d*Real.sqrt (d*(4*(n+1)+q))+q*Real.sqrt (q*d))^2
      = (2*d*D)^2+64*d := by
  let U := d*Real.sqrt (d*(4*(n+1)+q))
  let R := Real.sqrt (q*d)
  have rs : R^2=q*d := Real.sq_sqrt (by positivity)
  have us : U^2=d^3*(4*(n+1)+q) := by
    dsimp [U]; rw [mul_pow,Real.sq_sqrt (by positivity)]; ring
  have e : (2*S-q)^2=q*(4*(n+1)+q) := by nlinarith only [es]
  have ueq : q*U=d*R*(2*S-q) := by
    have sq : (q*U)^2=(d*R*(2*S-q))^2 := by
      rw [mul_pow q U,mul_pow (d*R) (2*S-q),mul_pow d R,rs,us,e]; ring
    apply (sq_eq_sq₀ (by dsimp [U]; positivity) (mul_nonneg
      (by dsimp [R]; positivity) (by linarith))).mp sq
  have norm : (d*S+2*q)^2-q*d*D^2=16*q := by
    rw [de]
    linear_combination -q*(q-4)*ed -4*(q-4)*es
  have sum : q*(U+q*R)=2*R*(d*S+2*q) := by
    calc
      _=d*R*(2*S-q)+q*q*R := by linear_combination ueq
      _=_ := by rw [de]; ring
  have squared := congrArg (fun x : ℝ => x^2) sum
  change (U+q*R)^2=(2*d*D)^2+64*d
  apply (mul_left_cancel₀ (pow_ne_zero 2 hq.ne') :
    q^2 * _ = q^2 * _ → _)
  calc
    q^2*(U+q*R)^2 = (2*R*(d*S+2*q))^2 := by simpa [mul_pow] using squared
    _ = 4*(q*d)*(q*d*D^2+16*q) := by
      rw [mul_pow,mul_pow,rs,show (d*S+2*q)^2=q*d*D^2+16*q by linarith]
      ring
    _ = _ := by ring

end OMA.CrystalComplement

/- Integer rounding for complementary parameter squareclasses at large q.
The square-root hypothesis is the integral companion of the second pair.
This argument uses the gap between adjacent integer squares only. -/
namespace OMA.CrystalLattice

theorem locked {a b q Q t : ℤ} (hq : 32≤q) (ha : q≤a)
    (bl : (q-3)*a≤b) (bu : b≤q*a) (hp : 0<Q) (hu : Q≤2*a)
    (pos : 0≤t) (ec : (a+b)^2=q*((a+1)*(b+1)))
    (sq : t^2=(q-4)*(4*(a*b+1)+Q)) :
    t=2*(b-a)-q-2 ∧ (q-4)*Q=8*(q+1)*a-8*b+(q+2)^2+16 := by
  let R := 2*(b-a)-q-2
  let U := 8*(q+1)*a-8*b+(q+2)^2+16
  have qa : 32*a≤q*a := mul_le_mul_of_nonneg_right hq (by omega)
  have rpos : 1≤R := by dsimp [R]; nlinarith only [hq,ha,bl,qa]
  have uq : 0≤U := by dsimp [U]; nlinarith only [bu,ha,hq,sq_nonneg (q+2)]
  have dQ : 0≤(q-4)*Q := mul_nonneg (by omega) (by omega)
  have uBound : U<2*R-1 := by
    have qa' : q*q≤q*a := mul_le_mul_of_nonneg_left ha (by omega)
    dsimp [U,R]
    nlinarith only [ha,hq,bl,qa,qa']
  have dBound : (q-4)*Q<2*R-1 := by
    have le := mul_le_mul_of_nonneg_left hu (show 0≤q-4 by omega)
    dsimp [R]
    nlinarith only [ha,hq,bl,qa,le]
  have eq : R^2-t^2=U-(q-4)*Q := by
    dsimp [R,U]; linear_combination 4*ec-sq
  have match' : t=R := by
    rcases lt_trichotomy t R with lo|same|hi
    · have gap : t^2≤(R-1)^2 :=
        (sq_le_sq₀ pos (by omega)).2 (by omega)
      nlinarith only [gap,eq,uBound,dQ]
    · exact same
    · have gap : (R+1)^2≤t^2 :=
        (sq_le_sq₀ (by omega) pos).2 (by omega)
      nlinarith only [gap,eq,dBound,uq]
  exact ⟨match',by rw [match'] at eq; dsimp [U] at eq; linarith⟩

theorem height {a b q Q : ℤ} (ha : 0<a) (hq : 4<q)
    (hb : b≤q*a) (hp : 0<Q) (cube : Q^3≤4*a*b)
    (eq : (q-4)*Q=8*(q+1)*a-8*b+(q+2)^2+16) :
    128*a≤q^4 := by
  have lo : 8*a≤q*Q := by nlinarith only [eq,hb,hp,sq_nonneg (q+2)]
  have cub : (8*a)^3≤(q*Q)^3 := by
    exact pow_le_pow_left₀ (by positivity) lo 3
  have u : Q^3≤4*q*a^2 := by
    have h := mul_le_mul_of_nonneg_left hb (show 0≤4*a by positivity)
    nlinarith only [cube,h]
  have h := mul_le_mul_of_nonneg_left u (show 0≤q^3 by positivity)
  have fin : (128*a)*(a^2)≤q^4*(a^2) := by nlinarith only [cub,h]
  exact le_of_mul_le_mul_right fin (sq_pos_of_pos ha)

end OMA.CrystalLattice

/- A deliberately generous finite cutoff for small first parameter.
Only the convergence of two integer-square tests matters, not the size of
the constant. The large-parameter result uses elementary integer gaps. -/
namespace OMA.CrystalSmallBound

private theorem diff {x y K z : ℝ} (hx : 0≤x) (hy : 0≤y) (_hz : 0<z)
    (hxy : z≤x+y) (hK : 0<K)
    (up : K*(x^2-y^2)<z) (lo : K*(y^2-x^2)<z) : |x-y|<1/K := by
  rw [abs_lt]
  constructor
  · rw [←neg_div,div_lt_iff₀ hK]
    by_contra! bad
    have h : 1≤K*(y-x) := by nlinarith only [bad]
    have m := mul_le_mul_of_nonneg_right h (show 0≤x+y by positivity)
    nlinarith only [m,hxy,lo]
  · rw [lt_div_iff₀ hK]
    by_contra! bad
    have h : 1≤K*(x-y) := by nlinarith only [bad]
    have m := mul_le_mul_of_nonneg_right h (show 0≤x+y by positivity)
    nlinarith only [m,hxy,up]

/-- For a large n, two independently computed square differences put
q sqrt(qd) within 1/10000 of the integer 2dD-dt. -/
theorem close {q d Q n S D t : ℝ}
    (hq : 4<q) (bound : q≤31) (hd : 1≤d) (de : d=q-4)
    (hn : (10:ℝ)^72≤n) (hp : 0<Q) (cube : Q^3≤4*n)
    (ed : D^2=S^2-4*n) (es : S^2=q*(n+1+S)) (hs : q≤2*S)
    (hD : 0≤D) (ht : 0≤t) (ts : t^2=d*(4*(n+1)+Q)) :
    |(2*d*D-d*t)-q*Real.sqrt (q*d)| < 1/10000 := by
  let z := Real.sqrt n
  have pos : 0<n := lt_of_lt_of_le (by norm_num) hn
  have zp : 0<z := Real.sqrt_pos.2 pos
  have zz : z^2=n := Real.sq_sqrt pos.le
  have zb : (10:ℝ)^36≤z := by
    apply (sq_le_sq₀ (by positivity) zp.le).mp
    rw [zz]; exact_mod_cast hn
  have Qb : (10:ℝ)^9*Q<z := by
    by_contra! bad
    have c := pow_le_pow_left₀ zp.le bad 3
    have z3 : z^3=z*n := by rw [←zz]; ring
    rw [z3,mul_pow] at c
    norm_num at c zb
    have le : z*n≤(4*10^27)*n := by nlinarith only [cube,c]
    have := le_of_mul_le_mul_right le pos
    norm_num at this
    linarith
  let U := d*Real.sqrt (d*(4*(n+1)+q))
  let V := d*t
  let R := q*Real.sqrt (q*d)
  have qp : 0<q := by linarith
  have dp : 0<d := by linarith
  have Upos : 0≤U := by dsimp [U]; positivity
  have Vpos : 0≤V := by dsimp [V]; positivity
  have Rp : 0≤R := by dsimp [R]; positivity
  have us : U^2=d^3*(4*(n+1)+q) := by
    dsimp [U]; rw [mul_pow,Real.sq_sqrt (by positivity)]; ring
  have vs : V^2=d^3*(4*(n+1)+Q) := by dsimp [V]; rw [mul_pow,ts]; ring
  have d3 : 1≤d^3 := one_le_pow₀ hd
  have cap : d^3≤30000 := by
    have e := pow_le_pow_left₀ dp.le (show d≤31 by linarith) 3
    norm_num at e; linarith
  have uz : z≤U := by
    apply (sq_le_sq₀ zp.le Upos).mp
    rw [zz,us]
    apply le_trans (show n≤4*(n+1)+q by linarith)
    exact le_mul_of_one_le_left (by positivity) d3
  have A := OMA.CrystalComplement.pell qp dp pos.le de es ed hs
  change (U+R)^2=(2*d*D)^2+64*d at A
  have Dpos : 0≤2*d*D := by positivity
  have E : |(U+R)-(2*d*D)|<1/20000 := by
    apply diff (add_nonneg Upos Rp) (by positivity) zp (by linarith) (by norm_num)
    · rw [A]; norm_num at zb; linarith
    · rw [A]; linarith
  have zQ : 20000*(d^3*Q)<z := by
    have h := mul_le_mul_of_nonneg_right cap hp.le
    norm_num at Qb; linarith
  have zq : 20000*(d^3*q)<z := by
    have h := mul_le_mul cap bound qp.le (by norm_num)
    norm_num at zb h; linarith
  have B : |U-V|<1/20000 := by
    apply diff Upos Vpos zp (by linarith) (by norm_num)
    · rw [us,vs]; nlinarith only [zq,mul_nonneg (pow_nonneg dp.le 3) hp.le]
    · rw [us,vs]; nlinarith only [zQ,mul_nonneg (pow_nonneg dp.le 3) qp.le]
  change |(2*d*D-V)-R|<1/10000
  rw [abs_lt] at E B ⊢
  constructor <;> linarith

private theorem small_irrational :
    (List.range 32).all (fun q =>
      q<5 || (q^3*(q-4)).sqrt^2 != q^3*(q-4))=true := by decide +kernel

theorem not_close {q d : ℕ} (hq : 5≤q) (bound : q≤31) (de : d+4=q) (z : ℤ) :
    ¬ |(z:ℝ)-(q:ℝ)*Real.sqrt ((q:ℝ)*d)| < 1/10000 := by
  intro near
  let R := (q:ℝ)*Real.sqrt ((q:ℝ)*d)
  have qp : (0:ℝ)≤q := by positivity
  have dp : (0:ℝ)≤d := by positivity
  have qc : (q:ℝ)≤31 := by exact_mod_cast bound
  have dc : (d:ℝ)≤31 := by exact_mod_cast (by omega : d≤31)
  have s : Real.sqrt ((q:ℝ)*d)≤31 := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num)).mp
    rw [Real.sq_sqrt (by positivity)]
    exact_mod_cast mul_le_mul qc dc dp (by norm_num)
  have rp : 0≤R := by dsimp [R]; positivity
  have cap : R≤961 := by
    dsimp [R]; exact_mod_cast mul_le_mul qc s (Real.sqrt_nonneg _) (by norm_num)
  change |(z:ℝ)-R|<1/10000 at near
  have N := abs_lt.mp near
  have sum : |(z:ℝ)+R|<2000 := by rw [abs_lt]; constructor <;> linarith
  have gap : |(z:ℝ)^2-R^2|<1 := by
    rw [show (z:ℝ)^2-R^2=((z:ℝ)-R)*((z:ℝ)+R) by ring,abs_mul]
    have m := mul_le_mul near.le sum.le (abs_nonneg _) (by norm_num : (0:ℝ)≤1/10000)
    nlinarith only [m]
  have rs : R^2=(q:ℝ)^3*d := by dsimp [R]; rw [mul_pow,Real.sq_sqrt (by positivity)]; ring
  rw [rs,abs_lt] at gap
  have a : (-1:ℤ)<z^2-(q:ℤ)^3*d := by exact_mod_cast gap.1
  have b : z^2-(q:ℤ)^3*d<1 := by exact_mod_cast gap.2
  have eq : z^2=(q:ℤ)^3*d := by omega
  have eqn : z.natAbs^2=q^3*d := by
    simpa [Int.natAbs_mul,Int.natAbs_pow] using congrArg Int.natAbs eq
  have entry := List.all_eq_true.mp small_irrational q (List.mem_range.mpr (by omega))
  have mod' : q-4=d := by omega
  simp [show ¬q<5 by omega,mod',←eqn,Nat.sqrt_eq'] at entry

end OMA.CrystalSmallBound

/- Integer proof for the large-parameter portion of the complementary
squareclass exclusion. The initial Vieta descent is from our density proof,
using the recurrence of Abrate, Barbero, Cerruti and Murru, arXiv:1601.03081. -/

namespace OMA.CrystalLarge
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

theorem encode {n a b : ℕ} (h : IsCrystalWithComponents n a b) (ord : a≤b) :
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


theorem parameter_cube {n a b q : ℕ} (h : IsCrystalWithComponents n a b) (ab : a≤b)
    (e : (a+b)^2=q*((a+1)*(b+1))) : q^3≤4*n := by
  have s := OMA.CrystalSquareClass.size h ab e
  obtain ⟨_,ha,hb,hn,_⟩ := h
  have p : 0<q := by
    by_contra! hq
    simp [Nat.eq_zero_of_le_zero hq] at e
    omega
  have left := Nat.pow_le_pow_left s 2
  have prod : (a+1)*(b+1)≤4*n := by
    have gt := Nat.mul_le_mul (show a+1≤2*a by omega) (show b+1≤2*b by omega)
    nlinarith only [hn,gt]
  have cap := Nat.mul_le_mul_left q prod
  have res : q*q^3≤q*(4*n) := by nlinarith only [left,e,cap]
  exact Nat.le_of_mul_le_mul_left res p

private theorem first_mono (d : ℕ) : Monotone (fun j => (row d j).1) := by
  apply monotone_nat_of_le_succ; intro j; simp [row]

private theorem row_shape (d j : ℕ) (hj : 1≤j) :
    d+4≤(row d j).1 ∧ d*(row d j).1≤(row d j).2 ∧
    (row d j).2≤(d+1)*(row d j).1+2 := by
  have lb := first_mono d hj
  have fst : d+4≤(row d j).1 := by simpa [row, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using lb
  refine ⟨fst,?_⟩
  obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show j≠0 by omega)
  simp only [row]
  constructor <;> nlinarith

private theorem comp_root {n c e Q d A : ℕ}
    (h : IsCrystalWithComponents n c e) (ce : c≤e)
    (eq : (c+e)^2=Q*((c+1)*(e+1))) (hp : 0<Q) (hd : 0<d) (sq : d*Q=A^2) :
    ∃ t : ℕ, t^2=d*(4*(n+1)+Q) := by
  have size := OMA.CrystalSquareClass.size h ce eq
  have le : Q≤Q^2 := by simpa [pow_two] using Nat.le_mul_of_pos_right Q hp
  have en : (c+e)^2=Q*(n+1+(c+e)) := by
    rw [eq]; congr 1
    have := h.2.2.2.1
    nlinarith only [this]
  obtain ⟨v,hv⟩ := OMA.CrystalComplement.integer_companion hp (by omega) en sq
  have dv : d^2 ∣ v^2 := ⟨d*(4*(n+1)+Q),by rw [hv]; ring⟩
  obtain ⟨t,ht⟩ := (Nat.pow_dvd_pow_iff (by decide : 2≠0)).mp dv
  refine ⟨t,Nat.eq_of_mul_eq_mul_left (pow_pos hd 2) ?_⟩
  rw [←mul_pow,←ht,hv]; ring

theorem window {n a b c e q Q A : ℕ}
    (h : IsCrystalWithComponents n a b) (ab : a≤b)
    (H : IsCrystalWithComponents n c e) (ce : c≤e)
    (eq : (a+b)^2=q*((a+1)*(b+1))) (EQ : (c+e)^2=Q*((c+1)*(e+1)))
    (hq : 32≤q) (sq : (q-4)*Q=A^2) :
    ∃ d j : ℕ, q=d+4 ∧ 1≤j ∧
      a+1=2*(row d j).1 ∧ b+1=2*((row d j).1+(row d j).2) ∧
      128*a≤q^4 ∧ d*Q+8*b=8*(q+1)*a+(q+2)^2+16 := by
  rcases encode h ab with sp|⟨d,j,hj,_,aa,bb,qq⟩
  · obtain ⟨_,rfl,rfl⟩ := sp; norm_num at eq; omega
  have ident : q=d+4 := Nat.eq_of_mul_eq_mul_right (by positivity) (eq.symm.trans qq)
  subst q
  have prod := h.2.2.2.1
  have Hp := H.2.1
  have hQ : 0<Q := by
    by_contra! le
    simp [Nat.eq_zero_of_le_zero le] at EQ
    omega
  obtain ⟨xlow,hlo,hup⟩ := row_shape d j hj
  have ad : a+1=2*(row d j).1 := by omega
  have bd : b+1=2*((row d j).1+(row d j).2) := by omega
  let x := (row d j).1
  let y := (row d j).2
  change a+1=2*x at ad
  change b+1=2*(x+y) at bd
  change d+4≤x at xlow
  change d*x≤y at hlo
  change y≤(d+1)*x+2 at hup
  have lower : (d+1)*a≤b := by
    have hmul := congrArg (fun t : ℕ => d*t) ad
    nlinarith only [ad,bd,hlo,hmul]
  have upper : b≤(d+4)*a := by
    have hmul := congrArg (fun t : ℕ => d*t) ad
    nlinarith only [ad,bd,hup,xlow,hmul]
  have qla : d+4≤a := by omega
  have cu := parameter_cube H ce EQ
  have Qle : Q≤2*a := by
    by_contra! gt
    have hi := Nat.pow_lt_pow_left gt (by decide : 3≠0)
    have u1 := Nat.mul_le_mul_left a upper
    have u2 := Nat.mul_le_mul_right (a*a) qla
    nlinarith only [cu,hi,u1,u2,prod,Nat.zero_le (a^3)]
  obtain ⟨t,ht⟩ := comp_root H ce EQ hQ (show 0<d by omega) (by simpa using sq)
  rw [prod] at ht cu
  have p := OMA.CrystalLattice.locked (a:=(a:ℤ)) (b:=(b:ℤ)) (q:=((d:ℤ)+4))
    (Q:=(Q:ℤ)) (t:=(t:ℤ)) (by omega) (by omega)
    (by convert (show (((d:ℤ)+1)*a)≤b by exact_mod_cast lower) using 1; ring)
    (by exact_mod_cast upper) (by omega) (by omega) (by positivity)
    (by exact_mod_cast eq) (by simpa using (show (t:ℤ)^2=d*(4*((a:ℤ)*b+1)+Q) by exact_mod_cast ht))
  have size := OMA.CrystalLattice.height (by exact_mod_cast (by omega : 0<a))
    (show (4:ℤ)<d+4 by omega) (by exact_mod_cast upper) (by exact_mod_cast hQ)
    (by exact_mod_cast (by simpa [Nat.mul_assoc] using cu :
      Q^3≤4*a*b)) p.2
  refine ⟨d,j,rfl,hj,ad,bd,by exact_mod_cast size,?_⟩
  have e' : (d:ℤ)*Q+8*b=8*(d+4+1)*a+(d+4+2)^2+16 := by linarith [p.2]
  exact_mod_cast e'

private theorem row_mod (d j : ℕ) :
    ((row d j).1 : ZMod d) = (j+1)^2 ∧ ((row d j).2 : ZMod d) = 2*j+3 := by
  induction j with
  | zero => simp [row]
  | succ j ih =>
    simp [row,ih.1,ih.2]
    constructor <;> ring

private theorem row_dvd {d j a b Q : ℕ}
    (aa : a+1=2*(row d j).1) (bb : b+1=2*((row d j).1+(row d j).2))
    (eq : d*Q+8*b=8*(d+4+1)*a+(d+4+2)^2+16) :
    d ∣ 4*(4*j+3)^2 := by
  have a' := congrArg (Nat.cast : ℕ → ZMod d) aa
  have b' := congrArg (Nat.cast : ℕ → ZMod d) bb
  have e' := congrArg (Nat.cast : ℕ → ZMod d) eq
  simp [(row_mod d j).1,(row_mod d j).2] at a' b' e'
  apply (ZMod.natCast_eq_zero_iff _ d).mp
  push_cast
  linear_combination -e' -40*a' +8*b'

private theorem row_limit {d j a : ℕ} (aa : a+1=2*(row d j).1)
    (h : 128*a≤(d+4)^4) : j≤3 := by
  by_contra! hi
  have m := first_mono d (show 4≤j by omega)
  have v : 2*(row d 4).1≤a+1 := aa ▸ Nat.mul_le_mul_left 2 m
  simp [row] at v
  ring_nf at v h
  omega

private def compatible (n Q z : ℕ) : Bool :=
  let u := (Q*(4*(n+1)+Q)).sqrt
  let T := (u+Q)/2
  let g := T^2-4*n
  z.sqrt^2==z && decide (Q^3≤4*n) && u^2==Q*(4*(n+1)+Q) && g.sqrt^2==g

private theorem compatible_of {n c e Q A : ℕ} (h : IsCrystalWithComponents n c e)
    (ce : c≤e) (eq : (c+e)^2=Q*((c+1)*(e+1))) : compatible n Q (A^2)=true := by
  have cu := parameter_cube h ce eq
  have le := OMA.CrystalSquareClass.size h ce eq
  have hp := h.2.1
  have prod := h.2.2.2.1
  have qp : 0<Q := by
    by_contra! z; simp [Nat.eq_zero_of_le_zero z] at eq; omega
  have qq : Q≤Q^2 := by simpa [pow_two] using Nat.le_mul_of_pos_right Q qp
  let u := 2*(c+e)-Q
  have eu : u+Q=2*(c+e) := by dsimp [u]; omega
  have us : u^2=Q*(4*(n+1)+Q) := by
    have e' : (c+e)^2=Q*(n+1+(c+e)) := by
      rw [eq,prod]; ring
    have f := congrArg (fun x : ℕ => x^2) eu
    have g := congrArg (fun x : ℕ => x*(2*Q)) eu
    nlinarith only [e',f,g]
  have ds : (c+e)^2-4*n=(e-c)^2 := by
    have dc := Nat.sub_add_cancel ce
    have dc2 := congrArg (fun v : ℕ => v^2) dc
    have dc3 := congrArg (fun v : ℕ => v*c) dc
    have sum : (c+e)^2=(e-c)^2+4*n := by nlinarith only [prod,dc2,dc3]
    omega
  simp [compatible,←us,Nat.sqrt_eq',eu,ds,cu]

private def possible (d j : ℕ) : Bool :=
  let xh := row d j
  let a := 2*xh.1-1
  let b := 2*(xh.1+xh.2)-1
  let z := 8*(d+4+1)*a+(d+4+2)^2+16-8*b
  compatible (a*b) (z/d) z

private theorem table : (List.range 901).all (fun d =>
    (List.range 4).all (fun j => d<28 || j<1 || (4*(4*j+3)^2 % d != 0) || !(possible d j)))=true := by
  decide +kernel

/-- Unconditional complementary-squareclass exclusion for the whole
large-parameter range in the original crystal predicate. -/
theorem no_large {n a b c e q Q A : ℕ}
    (h : IsCrystalWithComponents n a b) (ab : a≤b)
    (H : IsCrystalWithComponents n c e) (ce : c≤e)
    (eq : (a+b)^2=q*((a+1)*(b+1))) (EQ : (c+e)^2=Q*((c+1)*(e+1)))
    (hq : 32≤q) (sq : (q-4)*Q=A^2) : False := by
  obtain ⟨d,j,rfl,hj,aa,bb,lim,lin⟩ := window h ab H ce eq EQ hq sq
  have jlim := row_limit aa lim
  have divides := row_dvd aa bb lin
  have hd := Nat.le_of_dvd (show 0<4*(4*j+3)^2 by positivity) divides
  have top : 4*(4*j+3)^2≤900 := by interval_cases j <;> decide
  have entry := List.all_eq_true.mp (List.all_eq_true.mp table d
    (List.mem_range.mpr (by omega))) j (List.mem_range.mpr (by omega))
  have check : possible d j=true := by
    have aa' : 2*(row d j).1-1=a := by omega
    have bb' : 2*((row d j).1+(row d j).2)-1=b := by omega
    have zz : 8*(d+4+1)*a+(d+4+2)^2+16-8*b=d*Q := by omega
    have sq' : d*Q=A^2 := by simpa using sq
    have prod := h.2.2.2.1
    simp only [possible,aa',bb',zz,←prod]
    rw [Nat.mul_div_cancel_left _ (show 0<d by omega),sq']
    exact compatible_of H ce EQ
  have z := Nat.mod_eq_zero_of_dvd divides
  simp [show ¬d<28 by omega,show ¬j<1 by omega,z,check] at entry

private theorem small_bound {n a b c e d Q t : ℕ}
    (h : IsCrystalWithComponents n a b) (ab : a≤b)
    (H : IsCrystalWithComponents n c e) (ce : c≤e)
    (eq : (a+b)^2=(d+4)*((a+1)*(b+1))) (EQ : (c+e)^2=Q*((c+1)*(e+1)))
    (hd : 1≤d) (hmax : d≤27) (hp : 0<Q) (ts : t^2=d*(4*(n+1)+Q)) :
    n<10^72 := by
  by_contra! huge
  have prod := h.2.2.2.1
  have eR : ((a:ℝ)+b)^2=((d:ℝ)+4)*(n+1+((a:ℝ)+b)) := by
    have a' : (a+b)^2=(d+4)*(n+1+(a+b)) := by rw [eq,prod]; ring
    exact_mod_cast a'
  have ed : ((b:ℝ)-a)^2=((a:ℝ)+b)^2-4*n := by rw [prod]; push_cast; ring
  have sz := OMA.CrystalSquareClass.size h ab eq
  have small : d+4≤(d+4)^2 := by nlinarith only [Nat.zero_le (d*d)]
  have near := OMA.CrystalSmallBound.close (q:=((d:ℝ)+4)) (d:=(d:ℝ)) (Q:=(Q:ℝ))
    (n:=(n:ℝ)) (S:=((a:ℝ)+b)) (D:=((b:ℝ)-a)) (t:=(t:ℝ))
    (by exact_mod_cast (by omega : 4<d+4)) (by exact_mod_cast (by omega : d+4≤31))
    (by exact_mod_cast hd) (by ring) (by exact_mod_cast huge) (by exact_mod_cast hp)
    (by exact_mod_cast parameter_cube H ce EQ) ed eR
    (by exact_mod_cast (show d+4≤2*(a+b) by omega))
    (by exact_mod_cast sub_nonneg.mpr (show (a:ℝ)≤b by exact_mod_cast ab)) (by positivity)
    (by exact_mod_cast ts)
  apply OMA.CrystalSmallBound.not_close (q:=d+4) (by omega) (by omega) rfl
    (2*(d:ℤ)*((b:ℤ)-a)-(d:ℤ)*t)
  push_cast
  exact near

private theorem root_index {n d Q t : ℕ} (hd : 0<d) (hp : 0<Q)
    (cu : (d+4)^3≤4*n) (CU : Q^3≤4*n) (ts : t^2=d*(4*(n+1)+Q)) :
    t=(4*d*(n+1)).sqrt+1 := by
  let B := 4*d*(n+1)
  have eq : t^2=B+d*Q := by dsimp [B]; rw [ts]; ring
  have bound : d*Q^2≤4*n := by
    rcases le_total d Q with h|h
    · have m := Nat.mul_le_mul_right (Q^2) h; nlinarith only [m,CU]
    · have m := Nat.mul_le_mul_left d (Nat.pow_le_pow_left h 2)
      have e := Nat.pow_le_pow_left (show d≤d+4 by omega) 3
      nlinarith only [m,e,cu]
  have lo : d*Q≤B.sqrt := by
    apply Nat.le_sqrt'.2
    have m := Nat.mul_le_mul_left d bound
    dsimp [B]; nlinarith only [m,Nat.zero_le d]
  have pos := Nat.mul_pos hd hp
  have a : B.sqrt<t := Nat.sqrt_lt'.2 (by omega)
  have b := Nat.lt_succ_sqrt' B
  change t=B.sqrt+1
  by_contra! ne
  have z := Nat.pow_le_pow_left (show B.sqrt+2≤t by omega) 2
  nlinarith only [z,b,eq,lo]

private def candidate (d j : ℕ) : Bool :=
  let n := value d j
  let base := 4*d*(n+1)
  let z := (base.sqrt+1)^2-base
  (z%d == 0) && compatible n (z/d) z

private theorem end_small : (List.range 28).all (fun d =>
    d==0 || decide (10^72≤value d 100))=true := by decide +kernel

private theorem small_table : (List.range 28).all (fun d =>
    (List.range 100).all (fun j => d==0 || j==0 || !(candidate d j)))=true := by
  decide +kernel

theorem no_complement {n a b c e q Q A : ℕ}
    (h : IsCrystalWithComponents n a b) (ab : a≤b)
    (H : IsCrystalWithComponents n c e) (ce : c≤e)
    (eq : (a+b)^2=q*((a+1)*(b+1))) (EQ : (c+e)^2=Q*((c+1)*(e+1)))
    (hq : 4<q) (sq : (q-4)*Q=A^2) : False := by
  by_cases big : 32≤q
  · exact no_large h ab H ce eq EQ big sq
  rcases encode h ab with sp|⟨d,j,hj,nv,_,_,qq⟩
  · obtain ⟨_,rfl,rfl⟩ := sp; norm_num at eq; omega
  have id : q=d+4 := Nat.eq_of_mul_eq_mul_right (by positivity) (eq.symm.trans qq)
  subst q
  have hd : 0<d := by omega
  have hp : 0<Q := by
    by_contra! le
    have cp := H.2.1
    simp [Nat.eq_zero_of_le_zero le] at EQ
    omega
  have sq' : d*Q=A^2 := by simpa using sq
  obtain ⟨t,ts⟩ := comp_root H ce EQ hp hd sq'
  have sz := small_bound h ab H ce eq EQ hd (by omega) hp ts
  have entry := List.all_eq_true.mp end_small d (List.mem_range.mpr (by omega))
  simp [show d≠0 by omega] at entry
  have mono : Monotone (value d) := by
    apply monotone_nat_of_le_succ; intro i
    simp only [value,row]
    apply Nat.mul_le_mul <;> omega
  have jl : j<100 := by
    by_contra! ge
    have grow := mono ge
    omega
  have fail := List.all_eq_true.mp (List.all_eq_true.mp small_table d
    (List.mem_range.mpr (by omega))) j (List.mem_range.mpr jl)
  have ix := root_index hd hp (parameter_cube h ab eq) (parameter_cube H ce EQ) ts
  have recov : ((4*d*(n+1)).sqrt+1)^2-4*d*(n+1)=d*Q := by
    rw [←ix,ts]
    have e' : d*(4*(n+1)+Q)=4*d*(n+1)+d*Q := by ring
    omega
  have ok : candidate d j=true := by
    simp only [candidate,←nv,recov,Nat.mul_mod_right,Nat.mul_div_cancel_left _ hd]
    rw [sq']
    simpa using compatible_of H ce EQ (A:=A)
  simp [show d≠0 by omega,show j≠0 by omega,ok] at fail

end OMA.CrystalLarge

#print axioms OMA.CrystalLarge.no_complement

