import Mathlib

/-! Exact endpoint identity behind Meštrović, Conjecture 19. -/
namespace OMA.PascalPowerSum19
open Nat Finset

private theorem pairs (f:ℕ→ℤ) (x:ℤ) (k:ℕ) :
    (∑j∈range (2*k), f j*x^j)+(∑j∈range (2*k), f j*(-x)^j)=
    2*∑i∈range k, f (2*i)*x^(2*i) := by
  induction k with
  | zero=>simp
  | succ k ih=>
    rw [show 2*(k+1)=2*k+1+1 by omega]
    simp only [sum_range_succ]
    have even:(-x)^(2*k)=x^(2*k):=by rw [pow_mul,pow_mul];ring
    have odd:(-x)^(2*k+1) = -(x^(2*k+1)):=by rw [pow_succ,pow_succ,even];ring
    rw [odd,even];linear_combination ih

private def halfRow (N len:ℕ) (x:ℤ) :=
  ∑i∈range len, (N.choose (2*i):ℤ)*x^(2*i)

private theorem bin (x:ℤ) (N:ℕ) :
    (x+1)^N=∑i∈range (N+1), (N.choose i:ℤ)*x^i := by
  rw [add_pow];apply sum_congr rfl;intro i _;simp [mul_comm]

theorem even_row (x:ℤ) (k:ℕ) :
    (x+1)^(2*k+2)+(1-x)^(2*k+2)-2*x^(2*k+2)=2*halfRow (2*k+2) (k+1) x := by
  set N:=2*k+2
  rw [show 1-x=(-x)+1 by ring,bin,bin,
    sum_range_succ (fun j=>(N.choose j:ℤ)*x^j) N,
    sum_range_succ (fun j=>(N.choose j:ℤ)*(-x)^j) N]
  have h:=pairs (fun j=>(N.choose j:ℤ)) x (k+1)
  rw [show 2*(k+1)=N by dsimp [N];omega] at h
  have even:(-x)^N=x^N:=by dsimp [N];rw [show 2*k+2=2*(k+1) by omega,pow_mul,pow_mul];ring
  rw [even,Nat.choose_self,Nat.cast_one,one_mul]
  dsimp [halfRow];linear_combination h

theorem odd_row (x:ℤ) (k:ℕ) :
    (x+1)^(2*k+1)+(1-x)^(2*k+1)=2*halfRow (2*k+1) (k+1) x := by
  rw [show 1-x=(-x)+1 by ring,bin,bin]
  exact (show 2*(k+1)=2*k+1+1 by omega) ▸ pairs (fun j=>((2*k+1).choose j:ℤ)) x (k+1)

def term (n k:ℕ) (x:ℤ) :=
  ∑i∈range (k+1), (1+(n:ℤ)*(k+1-i:ℕ))*((2*k+2).choose (2*i):ℤ)*x^(2*i)

private theorem weighted (k i:ℕ) (hi:i<k+1) :
    ((k+1-i:ℕ):ℤ)*((2*k+2).choose (2*i):ℤ)=
    (k+1:ℤ)*((2*k+1).choose (2*i):ℤ) := by
  have rel:=Nat.choose_mul_succ_eq (2*k+1) (2*i)
  rw [show 2*k+1+1-2*i=2*(k+1-i) by omega] at rel
  have casted:=congrArg (Nat.cast (R:=ℤ)) rel
  push_cast at casted
  change ((2*k+1).choose (2*i):ℤ)*(2*(k:ℤ)+1+1)=
    ((2*k+2).choose (2*i):ℤ)*(2*(k+1-i:ℕ)) at casted
  nlinarith only [casted]

/-- The summand over a single base, expressed as two finite differences. -/
theorem difference (n k:ℕ) (x:ℤ) :
    2*term n k x =
    ((x+1)^(2*k+2)-x^(2*k+2))-(x^(2*k+2)-(x-1)^(2*k+2))+
    n*(k+1:ℤ)*((x+1)^(2*k+1)-(x-1)^(2*k+1)) := by
  have split:term n k x=halfRow (2*k+2) (k+1) x+
      n*(k+1:ℤ)*halfRow (2*k+1) (k+1) x:=by
    unfold term halfRow
    rw [mul_sum,←sum_add_distrib];apply sum_congr rfl;intro i hi
    linear_combination (n:ℤ)*x^(2*i)*weighted k i (mem_range.mp hi)
  have even:(1-x)^(2*k+2)=(x-1)^(2*k+2):=by
    rw [show 1-x= -(x-1) by ring,show 2*k+2=2*(k+1) by omega,pow_mul,pow_mul];ring
  have odd:(1-x)^(2*k+1)= -((x-1)^(2*k+1)):=by
    rw [show 1-x= -(x-1) by ring,pow_succ,pow_succ,pow_mul,pow_mul];ring
  have a:=even_row x k;rw [even] at a
  have b:=odd_row x k;rw [odd] at b
  rw [split];linear_combination -a-(n:ℤ)*(k+1)*b

private theorem telescope (f:ℕ→ℤ) (t:ℕ) :
    (∑j∈range t, (f (j+2)-f (j+1)))=f (t+1)-f 1 :=
  Finset.sum_range_sub (fun j=>f (j+1)) t

/-- Exact identity before any modular arithmetic. The base runs from 1
to t=n−1, including the zeroth power at those positive bases. -/
theorem endpoint (t k:ℕ) :
    2*((∑j∈range t, term (t+1) k ((j:ℤ)+1))+1)=
    (t+1:ℤ)^(2*k+2)-(t:ℤ)^(2*k+2)+1+
    (t+1:ℤ)*(k+1:ℤ)*((t+1:ℤ)^(2*k+1)+(t:ℤ)^(2*k+1)-1) := by
  let f (j:ℕ):ℤ:=(j:ℤ)^(2*k+2)
  let g (j:ℕ):ℤ:=(j:ℤ)^(2*k+1)
  let T:ℤ:=(t+1:ℤ)*(k+1:ℤ)
  have step (j:ℕ) : 2*term (t+1) k ((j:ℤ)+1) =
      ((f (j+2)-f (j+1))-(f (j+1)-f j))+
      T*((g (j+2)-g (j+1))+(g (j+1)-g j)):=by
    dsimp only [f,g,T];push_cast
    convert difference (t+1) k ((j:ℤ)+1) using 1; push_cast; ring
  have all:=sum_congr (s₁:=range t) rfl (fun j _=>step j)
  rw [←mul_sum,sum_add_distrib,sum_sub_distrib,←mul_sum,sum_add_distrib,
    telescope,Finset.sum_range_sub,telescope,Finset.sum_range_sub] at all
  dsimp [f,g,T] at all
  simp only [one_pow,zero_pow (by omega : 2*k+2≠0),
    zero_pow (by omega : 2*k+1≠0)] at all
  linear_combination all

end OMA.PascalPowerSum19
