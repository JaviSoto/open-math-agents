import MollBinomial

/-! Exact split-prime valuation on the prime-power boundary. -/
namespace OMA.MollSegment

private theorem root_ge (p k n : ℕ) [hp : Fact p.Prime] (h4 : p%4=1) :
    ∃ r : ℕ, n≤r ∧ (r:ZMod (p^k))*(r:ZMod (p^k))=-1 := by
  let Q := p^k
  have Qpos : 0<Q := pow_pos hp.out.pos _
  obtain ⟨u,hu⟩ := (ZMod.exists_sq_eq_neg_one_iff (p:=p)).mpr (by omega)
  have dv : p ∣ u.val^2+1 := by
    rw [← ZMod.natCast_eq_zero_iff]; push_cast; rw [ZMod.natCast_zmod_val, sq, ← hu]; ring
  obtain ⟨b,hb⟩ := dv
  let x : ℕ := 1+p*((Q-1)*b)
  have hx1 : (x^Q : ZMod Q)=1 := by
    exact_mod_cast (ZMod.natCast_eq_natCast_iff _ _ _).mpr (pow_pow_modEq_one p k ((Q-1)*b))
  have hv : ((Q-1:ℕ):ZMod Q)=-1 := by
    rw [Nat.cast_sub (by omega : 1≤Q), ZMod.natCast_self]; simp
  have hx2 : (x:ZMod Q)= -(u.val:ZMod Q)^2 := by
    have hb' : (u.val:ZMod Q)^2+1=(p:ZMod Q)*b := by
      simpa using congrArg (fun a : ℕ => (a:ZMod Q)) hb
    dsimp [x]; push_cast; rw [hv]; linear_combination hb'
  have odd : Odd Q := (hp.out.odd_of_ne_two (by omega)).pow
  have unit : ((u.val:ZMod Q)^Q)^2 = -1 := by
    rw [hx2, odd.neg_pow, ← pow_mul, Nat.mul_comm, pow_mul] at hx1
    linear_combination -hx1
  refine ⟨u.val^Q+Q*n,by have := Nat.le_mul_of_pos_left n Qpos; omega,?_⟩
  change ((u.val^Q+Q*n:ℕ):ZMod Q)*_ = _
  push_cast; simp only [ZMod.natCast_self, zero_mul, add_zero]
  simpa [sq] using unit

private theorem boundary_digit (p m r : ℕ) [hp : Fact p.Prime]
    (hm : 0 < m) (hr : ¬ p ∣ r) :
    ((r+p^m-1).choose (p^m) : ZMod p) - (r.choose (p^m):ZMod p) = 1 := by
  let N := p^m
  have hN : 0<N := pow_pos hp.out.pos _
  have nd : ¬ N ∣ r := fun h=>hr ((dvd_pow_self p hm.ne').trans h)
  have rem : 0 < r%N := Nat.pos_of_ne_zero (fun e=>nd (Nat.dvd_of_mod_eq_zero e))
  have remLess := Nat.mod_lt r hN
  have parts := Nat.mod_add_div r N
  have decomp : r+N-1=(r%N-1)+(r/N+1)*N := by
    rw [Nat.add_mul, one_mul, Nat.mul_comm (r/N) N]; omega
  have div : (r+N-1)/N=r/N+1 := by
    rw [decomp, Nat.add_mul_div_right _ _ hN, Nat.div_eq_of_lt (by omega : r%N-1<N), zero_add]
  have left := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (choose_prime_digit p m (r+N-1))
  have right := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (choose_prime_digit p m r)
  change (((r+N-1).choose N:ℕ):ZMod p) - (r.choose N:ZMod p)=1
  rw [left, right, div]; push_cast; ring

private theorem boundary_next_digit (p m r : ℕ) [hp : Fact p.Prime]
    (hm : 0 < m) (hr : p^m ≤ r) :
    ((r+p^m).choose (p^m+1):ZMod p) - (r.choose (p^m+1):ZMod p) = (r:ZMod p) := by
  let N := p^m
  have nz : (N:ZMod p)=0 := (ZMod.natCast_eq_zero_iff N p).mpr (dvd_pow_self p hm.ne')
  have reduce (x : ℕ) (hx : N≤x) :
      (x.choose (N+1):ZMod p)=(x.choose N:ZMod p)*(x:ZMod p) := by
    have e := congrArg (fun a:ℕ => (a:ZMod p)) (Nat.choose_succ_right_eq x N)
    simpa [Nat.cast_sub hx, nz] using e
  have hpN := pow_pos hp.out.pos m
  have e1 := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (choose_prime_digit p m (r+N))
  have e2 := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (choose_prime_digit p m r)
  change ((r+N).choose (N+1):ZMod p)-(r.choose (N+1):ZMod p)=_
  rw [reduce _ (by omega), reduce _ hr, e1, e2, Nat.add_div_right _ hpN]
  push_cast; rw [nz]; ring

private theorem unit_of_image {p k : ℕ} [hp : Fact p.Prime] (hk : 0<k) (a : ZMod (p^k))
    (ha : ZMod.castHom (dvd_pow_self p hk.ne') (ZMod p) a ≠ 0) : IsUnit a := by
  have : NeZero (p^k) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  rw [← ZMod.natCast_zmod_val a, ZMod.isUnit_natCast_iff_not_dvd_pow hp.out hk]
  intro d
  apply ha
  rw [← ZMod.natCast_zmod_val a, map_natCast, ZMod.natCast_eq_zero_iff]; exact d

private theorem same_divisors (p n k : ℕ) [hp : Fact p.Prime] (h4 : p%4=1)
    (unit_digit : ∀ r : ℕ, n≤r → ¬ p ∣ r →
      ((r+n).choose (n+1):ZMod p)-(r.choose (n+1):ZMod p) ≠ 0) :
    ((p^k:ℕ):ℤ) ∣ OeisA105751.a n ↔ p^k ∣ (n+1).factorial := by
  rcases k with _|k
  · simp
  have hk : 0<k+1 := by omega
  let Q := p^(k+1)
  let f : ZMod Q →+* ZMod p := ZMod.castHom (dvd_pow_self p hk.ne') _
  obtain ⟨r,hr,hs⟩ := root_ge p (k+1) n h4
  have hs' := congrArg f hs
  have rr : (r:ZMod p)*(r:ZMod p)=-1 := by simpa using hs'
  have nr : (r:ZMod p)≠0 := by intro z; rw [z,zero_mul] at rr; simp at rr
  have nd : ¬ p ∣ r := by rwa [← ZMod.natCast_eq_zero_iff]
  have ur : IsUnit (r:ZMod Q) := (ZMod.isUnit_natCast_iff_not_dvd_pow hp.out hk).mpr nd
  have u2 : IsUnit (2:ZMod Q) := by
    apply (ZMod.isUnit_natCast_iff_not_dvd_pow (a:=2) hp.out hk).mpr
    intro h; have := Nat.le_of_dvd (by decide : 0<2) h; have := hp.out.two_le; omega
  have delta := unit_of_image hk ((r.choose (n+1):ZMod Q)-((r+n).choose (n+1):ZMod Q)) (by
    simp only [map_sub,map_natCast]
    exact sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp (unit_digit r hr nd))))
  have eq := two_binomials Q r n hr hs
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← ZMod.natCast_eq_zero_iff]
  change (OeisA105751.a n:ZMod Q)=0 ↔ ((n+1).factorial:ZMod Q)=0
  rw [← (u2.mul ((ur.pow _))).mul ur |>.mul_right_eq_zero, eq, delta.mul_left_eq_zero]

private theorem valuation_of_digit (p n : ℕ) [hp : Fact p.Prime] (h4 : p%4=1)
    (unit_digit : ∀ r : ℕ, n≤r → ¬ p ∣ r →
      ((r+n).choose (n+1):ZMod p)-(r.choose (n+1):ZMod p) ≠ 0) :
    padicValInt p (OeisA105751.a n) = padicValNat p (n+1).factorial := by
  have eq (k : ℕ) := same_divisors p n k h4 unit_digit
  have per (k : ℕ) :
      (OeisA105751.a n=0 ∨ k≤padicValInt p (OeisA105751.a n)) ↔
         k≤padicValNat p (n+1).factorial := by
    simpa [padicValInt_dvd_iff, padicValNat_dvd_iff, Nat.factorial_ne_zero] using eq k
  have nz : OeisA105751.a n ≠ 0 := by
    intro z
    have h := (per (padicValNat p (n+1).factorial+1)).mp (Or.inl z)
    omega
  exact le_antisymm ((per _).mp (.inr le_rfl)) (((per _).mpr le_rfl).resolve_left nz)

private theorem val_factorial_power (p m : ℕ) [hp : Fact p.Prime] :
    (p-1)*padicValNat p (p^m).factorial = p^m-1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hp1 : 1≤p := hp.out.pos
    have hq : 1≤p^m := pow_pos hp.out.pos _
    rw [pow_succ', padicValNat_factorial_mul, Nat.mul_add, ih, Nat.sub_mul, one_mul]
    have hprod : p^m≤p*p^m := Nat.le_mul_of_pos_left _ hp.out.pos
    have hpos := pow_pos hp.out.pos m
    omega

/-- The precise exponent at both ends of each prime-power block, with no
assumption about a tie of the two split valuations. -/
theorem prime_power_endpoints (p m : ℕ) (hp : p.Prime) (h4 : p%4=1) (hm : 0 < m) :
    padicValInt p (OeisA105751.a (p^m-1)) = (p^m-1)/(p-1) ∧
    padicValInt p (OeisA105751.a (p^m)) = (p^m-1)/(p-1) := by
  let : Fact p.Prime := ⟨hp⟩
  let N := p^m
  have hN : 0<N := pow_pos hp.pos _
  have one : N-1+1=N := by omega
  have rhs : padicValNat p N.factorial = (N-1)/(p-1) := by
    rw [← val_factorial_power p m, Nat.mul_div_cancel_left _ (by have := hp.two_le; omega)]
  constructor
  · rw [valuation_of_digit p (N-1) h4 (by
      intro r _ nd
      rw [one, show r+(N-1)=r+N-1 by omega]
      rw [boundary_digit p m r hm nd]; exact one_ne_zero), one, rhs]
  · rw [valuation_of_digit p N h4 (by
      intro r hr nd
      rw [boundary_next_digit p m r hm hr]
      simpa [ZMod.natCast_eq_zero_iff] using nd), Nat.factorial_succ,
      padicValNat.mul (by omega) (Nat.factorial_ne_zero _)]
    have h : ¬ p ∣ N+1 := by
      intro h
      have d := (Nat.dvd_add_right (dvd_pow_self p hm.ne')).mp h
      exact hp.not_dvd_one d
    rw [padicValNat.eq_zero_of_not_dvd h, zero_add, rhs]

end OMA.MollSegment
