import FormalConjectures.OEIS.«280864»

/-! The greedy multiplier in A280864: every smaller compatible choice was
used, and the next mandatory radical divides the present multiplier. -/
namespace OMA.CoffeeGrowth
open Finset OeisA280864

def mandatory (u v : ℕ) := ∏ p ∈ requiredFactors u v, p
def excluded (u v : ℕ) := ∏ p ∈ forbiddenFactors u v, p

theorem mandatory_pos (u v : ℕ) : 0 < mandatory u v :=
  prod_pos fun _ h => (Nat.prime_of_mem_primeFactors (mem_sdiff.mp h).1).pos

private theorem prime_dvd_product {p : ℕ} (hp : p.Prime) {s : Finset ℕ}
    (hs : ∀ q ∈ s, q.Prime) (d : p ∣ ∏ q ∈ s,q) : p ∈ s := by
  obtain ⟨q,hq,hdiv⟩ := (Nat.prime_iff.mp hp).exists_mem_finset_dvd d
  exact (Nat.dvd_prime (hs q hq)).mp hdiv |>.resolve_left hp.ne_one ▸ hq

theorem eligible_multiplier (u v j : ℕ) (hj : 0<j) (hc : (excluded u v).Coprime j) :
    Eligible u v (mandatory u v*j) := by
  refine ⟨Nat.mul_pos (mandatory_pos ..) hj,fun p h=>dvd_mul_of_dvd_left (dvd_prod_of_mem _ h) _,?_⟩
  intro p h d
  have hp := Nat.prime_of_mem_primeFactors (mem_inter.mp h).1
  rcases hp.dvd_mul.mp d with left|right
  · have mem := prime_dvd_product hp (s:=requiredFactors u v)
      (fun _ h=>Nat.prime_of_mem_primeFactors (mem_sdiff.mp h).1) left
    exact (mem_sdiff.mp mem).2 (mem_inter.mp h).2
  · exact hp.not_dvd_one (hc ▸ Nat.dvd_gcd (dvd_prod_of_mem _ h) right : p∣1)

private theorem subset_product {s : Finset ℕ} {v : ℕ} (h : s⊆v.primeFactors) :
    (∏ p ∈ s,p) ∣ v :=
  (prod_dvd_prod_of_subset _ _ _ h).trans (Nat.prod_primeFactors_dvd _)

theorem bounds {u v z : ℕ} (ok : Eligible u v z) :
    ∃ L : ℕ, z=mandatory u v*L ∧ mandatory v z ∣ L := by
  obtain ⟨pos,req,_⟩ := ok
  have d := subset_product (s:=requiredFactors u v) (v:=z)
    (by intro p h; exact Nat.mem_primeFactors.mpr
          ⟨Nat.prime_of_mem_primeFactors (mem_sdiff.mp h).1,req p h,pos.ne'⟩)
  obtain ⟨L,eq⟩ := d
  refine ⟨L,eq,subset_product ?_⟩
  intro p h
  obtain ⟨pz,notv⟩ := mem_sdiff.mp h
  have hp := Nat.prime_of_mem_primeFactors pz
  have div := Nat.dvd_of_mem_primeFactors pz
  rw [eq] at div
  rcases hp.dvd_mul.mp div with left|right
  · have mem := prime_dvd_product hp (s:=requiredFactors u v)
      (fun _ h=>Nat.prime_of_mem_primeFactors (mem_sdiff.mp h).1) left
    exact (notv (mem_sdiff.mp mem).1).elim
  · exact Nat.mem_primeFactors.mpr ⟨hp,right,by intro h; rw [h,mul_zero] at eq; omega⟩

theorem next_excluded {u v z : ℕ} (hz : Eligible u v z) :
    forbiddenFactors v z = requiredFactors u v := by
  ext p
  constructor
  · intro h
    obtain ⟨zz,vv⟩ := mem_inter.mp h
    apply mem_sdiff.mpr
    exact ⟨vv,fun uu => hz.2.2 p (mem_inter.mpr ⟨vv,uu⟩) (Nat.dvd_of_mem_primeFactors zz)⟩
  · intro h
    have pv := (mem_sdiff.mp h).1
    exact mem_inter.mpr ⟨Nat.mem_primeFactors.mpr
      ⟨Nat.prime_of_mem_primeFactors pv,hz.2.1 p h,hz.1.ne'⟩,pv⟩

theorem fresh_multiplier_bound {a : ℕ → ℕ} {n P : ℕ} (g : GreedyAt a n)
    (hn : 2≤n) (hp : P.Prime) (fresh : ∀ i<n, ¬ P ∣ a i) :
    a n ≤ mandatory (a (n-2)) (a (n-1))*P := by
  let u := a (n-2)
  let v := a (n-1)
  have nf := fresh (n-1) (by omega)
  have cop : (excluded u v).Coprime P := by
    apply Nat.Coprime.symm
    apply hp.coprime_iff_not_dvd.mpr
    intro divides
    have mem := prime_dvd_product hp (s:=forbiddenFactors u v)
      (fun _ h => Nat.prime_of_mem_primeFactors (mem_inter.mp h).1) divides
    exact nf (Nat.dvd_of_mem_primeFactors (mem_inter.mp mem).1)
  apply g.2.2 _ (eligible_multiplier u v P hp.pos cop)
  intro i hi e
  apply fresh i hi; rw [e]; exact dvd_mul_left ..

/-- There cannot be more than n smaller compatible multipliers: all of
their distinct products already occur in the n previous positions. -/
theorem sieve {a : ℕ → ℕ} {n : ℕ} (g : GreedyAt a n) (L : ℕ)
    (eq : a n = mandatory (a (n-2)) (a (n-1))*L) :
    ((Ico 1 L).filter (fun j => (excluded (a (n-2)) (a (n-1))).Coprime j)).card ≤ n := by
  let R := mandatory (a (n-2)) (a (n-1))
  let S := (Ico 1 L).filter (fun j => (excluded (a (n-2)) (a (n-1))).Coprime j)
  have rp : 0<R := mandatory_pos ..
  have used (j : ℕ) (hj : j∈S) : R*j ∈ (range n).image a := by
    obtain ⟨bounds,cop⟩ := mem_filter.mp hj
    obtain ⟨lo,hi⟩ := mem_Ico.mp bounds
    by_contra h
    have unused : UnusedBefore a n (R*j) := by
      intro i lt eq'; exact h (mem_image.mpr ⟨i,mem_range.mpr lt,eq'⟩)
    have le := g.2.2 (R*j) (eligible_multiplier _ _ _ lo cop) unused
    rw [eq] at le
    exact (Nat.mul_lt_mul_of_pos_left hi rp).not_ge le
  exact (card_le_card_of_injOn (fun j=>R*j) used
    (fun _ _ _ _ h=>Nat.eq_of_mul_eq_mul_left rp h)).trans
    ((card_image_le).trans (card_range n).le)

end OMA.CoffeeGrowth
