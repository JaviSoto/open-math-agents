import PathPeriod
import PathSuccessor
import CycleTerminal

/-! The first missing successor cannot be a hole or a proper subset sum. -/

namespace OMA.PathEndpoint
open Finset OMA.PathBox OMA.PathShift OMA.PathHoles Arxiv.«2607.08366»

theorem subset_rep {I G : Type*} [Fintype I] [DecidableEq I] [AddCommMonoid G] [DecidableEq G]
    (L : I→ℕ) (x : I→G) (inj : Function.Injective (label L x)) (a : Box L) :
    ∃ T⊆univ.image (label L x), (∑ z∈T,z)=lin x (fun i=>(a i).val) := by
  classical
  choose J sub val using fun i=>OMA.CycleTerminal.mask (L i) (a i).val (a i).isLt
  let S := (univ : Finset (Σ i,Fin (L i))).filter (fun z=>z.2.val∈J z.1)
  refine ⟨S.image (label L x),image_subset_image (subset_univ _),?_⟩
  rw [sum_image inj.injOn]
  change (∑ z∈univ.filter (fun z : Σ i,Fin (L i)=>z.2.val∈J z.1),label L x z)=_
  rw [sum_filter,Fintype.sum_sigma]
  apply sum_congr rfl
  intro i _
  change (∑ j : Fin (L i),if j.val∈J i then 2^j.val • x i else 0)=(a i).val • x i
  rw [Fin.sum_univ_eq_sum_range (fun j=>if j∈J i then 2^j • x i else 0),←sum_filter]
  have e : (range (L i)).filter (fun j=>j∈J i)=J i := by
    ext j; simp only [mem_filter]; exact ⟨And.right,fun h=>⟨sub i h,h⟩⟩
  rw [e,←sum_smul,val]

/-- When the total deficit is small enough, a long row must continue
    at an actual label of the same cover. -/
theorem successor {I : Type*} [Fintype I] [DecidableEq I] {N : ℕ} [NeZero N]
    (L : I→ℕ) (x : I→ZMod N) (inj : Function.Injective (label L x))
    (ok : IsValidMod (univ.image (label L x))) (J : I) (kp : 2≤L J)
    (large : 4*(∑ i,L i)≤2^L J) (small : N<2^(∑ i,L i))
    (enough : ((∑ i,L i)+Fintype.card I-1).choose (Fintype.card I)<Fintype.card (Tiny L)) :
    2^L J • x J∈univ.image (label L x) := by
  classical
  obtain ⟨a,eq⟩ := represented L x inj ok J (by omega) (by omega) small enough
  obtain ⟨T,sub,shape⟩ := subset_rep L x inj a
  have size : (univ.image (label L x)).card=∑ i,L i := by
    rw [card_image_of_injective _ inj,card_univ,Fintype.card_sigma]
    simp
  have few := OMA.PathSuccessor.subset_succ ok (x J) (by omega : 0<L J)
    (by rw [size]; omega) (fun j hj=>by exact mem_image.mpr ⟨⟨J,⟨j,hj⟩⟩,mem_univ _,rfl⟩) T sub
    (shape.trans eq)
  have nz : 2^L J • x J ≠ 0 := fun kill=>small.not_ge (OMA.PathPeriod.full_modulus L x inj ok J kp large kill)
  have non : T.Nonempty := by
    by_contra h; have e := shape.trans eq
    rw [not_nonempty_iff_eq_empty.mp h,sum_empty] at e
    exact nz e.symm
  obtain ⟨z,hz⟩ := card_eq_one.mp (by have := card_pos.mpr non; omega : T.card=1)
  have e := shape.trans eq
  rw [hz,sum_singleton] at e
  rw [←e]; apply sub; simp [hz]

end OMA.PathEndpoint
