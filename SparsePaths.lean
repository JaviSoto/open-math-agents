import PathEndpoint
import PathCycle

/-! The conjectured lower bound and its inverse for sparse covers by
    paths of one affine doubling map. -/

open private OMA.LongCycle.translate from LongCycle
namespace OMA.SparsePaths
open Finset OMA.PathBox OMA.PathHoles OMA.PathSplice Arxiv.«2607.08366»

/-- The n labels, after one common translation, are the disjoint union
    of h binary progressions; zero-length rows are allowed. -/
def Covered {N : ℕ} (A : Finset (ZMod N)) (h : ℕ) : Prop :=
  ∃ (t : ZMod N) (L : Fin h→ℕ) (x : Fin h→ZMod N),
    Function.Injective (label L x) ∧ univ.image (label L x)=A.image (fun z=>z+t)

def Sparse (n h : ℕ) : Prop :=
  (n+h-1).choose h<2^(n-4*h) ∧ 4*n≤2^((n+h-1)/h) ∧ 2*h*Nat.log 2 n≤n

theorem big_cycle {N n h : ℕ} [NeZero N] {A : Finset (ZMod N)}
    (hn : 2≤n) (hh : 0<h) (ac : A.card=n) (valid : IsValidMod A) (cover : Covered A h)
    (sparse : Sparse n h) (sm : N<2^n) :
    ∃ (t : ZMod N) (r : ℕ) (y : ZMod N) (C : Finset (ZMod N)), 0<r ∧ n≤2*r ∧ 2^r • y=y ∧
      C.card=r ∧ C=(range r).image (fun j=>2^j • y) ∧ C⊆A.image (fun z=>z+t) := by
  classical
  obtain ⟨t,L,x,inj,im⟩ := cover
  have : Nonempty (Fin h) := ⟨⟨0,hh⟩⟩
  obtain ⟨M,J,mi,mim,ms,maximal,stop⟩ := OMA.PathSplice.maximal L x inj
  have im' := mim.trans im
  have total : (∑ i,M i)=n := by
    rw [←size M x mi,im',card_image_of_injective _ (fun _ _ e=>add_right_cancel e)]; exact ac
  have ok : IsValidMod (univ.image (label M x)) := im' ▸ OMA.LongCycle.translate A valid t
  obtain ⟨hsmall,hlarge,hhalf⟩ := sparse
  have sumMax := sum_le_sum (s:=univ) (fun i _=>maximal i)
  simp only [total,sum_const,card_univ,Fintype.card_fin,smul_eq_mul] at sumMax
  have max' := (ceilDiv_le_iff_le_mul hh).mpr sumMax
  rw [Nat.ceilDiv_eq_add_pred_div] at max'
  have big := hlarge.trans (Nat.pow_le_pow_right (by decide : 0<2) max')
  have kp : 2≤M J := by
    by_contra! low
    have p := Nat.pow_le_pow_right (by decide : 0<2) (show M J≤1 by omega)
    norm_num at p; omega
  have deficit := sum_le_sum (s:=univ) (fun i _=>(show M i≤(M i-4)+4 by omega))
  simp only [sum_add_distrib,sum_const,card_univ,Fintype.card_fin,smul_eq_mul,total] at deficit
  have exponent : n-4*h≤∑ i,(M i-4) := by rw [mul_comm h] at deficit; omega
  have enough : (n+h-1).choose h<Fintype.card (Tiny M) := by
    rw [Fintype.card_pi]
    change _<∏ i,Fintype.card (Fin (2^(M i-4)))
    simp only [Fintype.card_fin,prod_pow_eq_pow_sum]
    exact hsmall.trans_le (Nat.pow_le_pow_right (by decide : 0<2) exponent)
  have next := OMA.PathEndpoint.successor M x mi ok J kp (by rwa [total]) (by rwa [total])
    (by simpa [total] using enough)
  obtain ⟨⟨K,a⟩,_,e⟩ := mem_image.mp next
  have landed := stop K a.val a.isLt e.symm
  subst K
  obtain ⟨r,y,C,rp,half,wrap,cs,shape,sub⟩ := OMA.PathCycle.cycle M x mi ok J a.isLt e.symm total
    (by simpa only [Fintype.card_fin] using hhalf)
  exact ⟨t,r,y,C,rp,half,wrap,cs,shape,im' ▸ sub⟩

theorem lower {N n h : ℕ} [NeZero N] {A : Finset (ZMod N)}
    (hn : 2≤n) (hh : 0<h) (ac : A.card=n) (valid : IsValidMod A) (cover : Covered A h)
    (sparse : Sparse n h) : minModulus n≤N := by
  by_cases sm : N<2^n
  · obtain ⟨t,r,y,C,rp,half,wrap,cs,shape,sub⟩ := big_cycle hn hh ac valid cover sparse sm
    exact OMA.LongCycle.ordinary hn rp half _ ((card_image_of_injective _ (fun _ _ e=>add_right_cancel e)).trans ac)
      (OMA.LongCycle.translate A valid t) y wrap C cs shape sub
  · exact (Nat.sub_le (2^n) _).trans (by omega)

theorem extremal {n h : ℕ} {A : Finset (ZMod (minModulus n))}
    (hn : 4≤n) (hh : 0<h) (ac : A.card=n) (valid : IsValidMod A) (cover : Covered A h)
    (sparse : Sparse n h) :
    ∃ (t : ZMod (minModulus n)) (u : (ZMod (minModulus n))ˣ),
      A=(range n).image (fun j=>2^j • (u : ZMod (minModulus n))-t) := by
  classical
  have power := Nat.pow_log_le_self 2 (by omega : n≠0)
  have lg : 2≤Nat.log 2 n := (Nat.le_log_iff_pow_le (by decide : 1<2) (by omega : n≠0)).mpr hn
  have big : 4≤2^Nat.log 2 n := Nat.pow_le_pow_right (by decide : 0<2) lg
  have total := Nat.lt_two_pow_self (n:=n)
  have pos : 0 < minModulus n := minModulus_pos (by omega)
  have : NeZero (minModulus n) := ⟨pos.ne'⟩
  have bounds : minModulus n<2^n-2 := by change 2^n-2^(Nat.log 2 n)<_; omega
  obtain ⟨t,r,y,C,rp,half,wrap,cs,shape,sub⟩ := big_cycle (by omega) hh ac valid cover sparse (by omega)
  have im := card_image_of_injective A (fun (a b : ZMod (minModulus n)) (eq : a+t=b+t)=>add_right_cancel eq)
  have two := OMA.LongCycleShape.classify rp half _ (im.trans ac) (OMA.LongCycle.translate A valid t)
    y wrap C cs shape sub (by omega)
  have closed : ∀ a∈A,2 • a+t∈A := by
    rcases two with yes|bad
    · intro a ha
      obtain ⟨b,hb,e⟩ := mem_image.mp (yes (a+t) (mem_image_of_mem _ ha))
      have q : b=2 • a+t := by
        apply add_right_cancel (b:=t)
        rw [e,two_nsmul,two_nsmul]; abel
      exact q ▸ hb
    · omega
  obtain ⟨u,im⟩ := OMA.AffineDoublingClass.extremal_shape (by omega) A ac valid t closed
  exact ⟨t,u,im⟩

end OMA.SparsePaths
