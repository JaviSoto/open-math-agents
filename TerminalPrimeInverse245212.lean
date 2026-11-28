import DyadicLeast245212

/-! The last prime in an exact weighted-cofactor search is the ceiling
of a rational function of the target. It need not be searched or factored out. -/
namespace OMA.TerminalPrimeInverse245212
open Finset Nat OMA.Smooth245212
open private OMA.DyadicLeast245212.x_two_terms from DyadicLeast245212

theorem recover {p e : ℕ} (hp : p.Prime) (ep : 0<e) :
    let x:=X p (some e)
    let u:=(e:ℚ)/(((e:ℚ)+1)*(x-1))
    (p:ℚ)-1<u ∧ u≤p := by
  let x:=X p (some e)
  have pn : (0:ℚ)<p:=by exact_mod_cast hp.pos
  have pg : (1:ℚ)<p:=by exact_mod_cast hp.one_lt
  have en : (0:ℚ)<e:=by exact_mod_cast ep
  have lo:=OMA.DyadicLeast245212.x_two_terms hp ep
  change 1+(e:ℚ)/(((e:ℚ)+1)*p)≤x at lo
  have surplus : 0<x-1:=by
    have positive : 0<(e:ℚ)/(((e:ℚ)+1)*p):=by positivity
    linarith only [positive,lo]
  have upper : 1<(e+1:ℚ)*Y p (some e):=by
    rw [y_avg hp.one_lt]
    have cancel : ∀a:ℚ,(e+1)* (a/(e+1))=a:=by intro a;field_simp
    rw [cancel]
    have inc : range 2⊆range (e+1):=range_subset_range.mpr (by omega)
    have base:=sum_le_sum_of_subset_of_nonneg (f:=fun j:ℕ=>(p:ℚ)⁻¹^j) inc (fun _ _ _=>by positivity)
    apply lt_of_lt_of_le _ base
    simp only [sum_range_succ,sum_range_zero,zero_add,pow_zero,pow_one]
    linarith only [inv_pos.mpr pn]
  have eqn : ((p:ℚ)-1)*(x-1)=1-Y p (some e):=by
    dsimp only [x,X];field_simp [ne_of_gt (sub_pos.mpr pg)];ring
  have scale : 0<((e:ℚ)+1)*(x-1):=by positivity
  change (p:ℚ)-1<(e:ℚ)/_ ∧ (e:ℚ)/_≤p
  constructor
  · apply (lt_div_iff₀ scale).mpr
    nlinarith only [upper,congrArg (fun z:ℚ=>((e:ℚ)+1)*z) eqn]
  · apply (div_le_iff₀ scale).mpr
    have b:=(div_le_iff₀ (show 0<((e:ℚ)+1)*p by positivity)).mp (show (e:ℚ)/(((e:ℚ)+1)*p)≤x-1 by linarith only [lo])
    linarith only [b]

#print axioms recover
end OMA.TerminalPrimeInverse245212
