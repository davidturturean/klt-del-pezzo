import KltDP.RingTheory.AssociatedGradedRees
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# The associated graded ring is a domain when orders add sharply

BRIEF39. `gr_I R` is a domain exactly when the order filtration is multiplicative in the sharp sense:
if `x` has order exactly `a` and `y` order exactly `b`, then `x * y` has order exactly `a + b`. That
hypothesis is `SharpProduct`, and this module turns it into `IsDomain (AssociatedGraded I)`.

## Why this is short

`IsDomain (R ⧸ P) ↔ P.IsPrime` (`Ideal.Quotient.isDomain_iff_prime`), so the content is primality of
`shiftIdeal = I·R[It]`. Naively that means comparing coefficients of a product of two arbitrary Rees
elements: taking the least `a` with `f_a ∉ I^(a+1)`, splitting one term off the antidiagonal sum, and a
case analysis on either side of it.

**None of that is needed**, because the Rees algebra is graded — `KltDP.ReesGrading` supplies
`GradedAlgebra (component I)`, which *is* `GradedRing (component I)`, the pinned `GradedAlgebra` being
an `abbrev` for it — and `shiftIdeal` is spanned by the degree-zero elements `algebraMap a`, hence
homogeneous. For a homogeneous ideal, `Ideal.IsHomogeneous.isPrime_of_homogeneous_mem_or_mem` reduces
primality to **homogeneous** `x` and `y`. On those the computation is one line:
`single a r * single b s = single (a+b) (r*s)`, and `single_mem_shiftIdeal_iff` converts each
membership into membership of a power of `I`. `SharpProduct` is then literally the contrapositive.

The index type is `ℕ`, which satisfies the `AddCommMonoid`/`LinearOrder`/`IsOrderedCancelAddMonoid`
stack that the primality lemma requires.

## What is proved

* `SharpProduct` — the named hypothesis: orders add sharply.
* `algebraMap_mem_component_zero`, `shiftIdeal_isHomogeneous` — `I·R[It]` is a homogeneous ideal.
* `shiftIdeal_ne_top` — properness, from `I ≠ ⊤` via the degree-zero coefficient of `1`.
* **`shiftIdeal_isPrime`** and **`isDomain_of_sharpProduct`**.
-/

noncomputable section

open Polynomial

universe u

namespace KltDP.RingTheory.AssociatedGradedPrime

open KltDP.RingTheory.AssociatedGradedRees

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- **Orders add sharply**: an element of order exactly `a` times one of order exactly `b` has order
exactly `a + b`. This is the one hypothesis that `IsDomain (AssociatedGraded I)` needs. -/
def SharpProduct : Prop :=
  ∀ (a b : ℕ) (x y : R), x ∈ I ^ a → x ∉ I ^ (a + 1) → y ∈ I ^ b → y ∉ I ^ (b + 1) →
    x * y ∉ I ^ (a + b + 1)

/-! ## `I·R[It]` is homogeneous -/

/-- The image of `R` sits in degree zero. -/
theorem algebraMap_mem_component_zero (a : R) :
    algebraMap R (reesAlgebra I) a ∈ KltDP.ReesGrading.component I 0 := by
  refine ⟨⟨a, by rw [pow_zero, Ideal.one_eq_top]; trivial⟩, ?_⟩
  apply Subtype.ext
  show (Polynomial.monomial 0 a : Polynomial R)
      = ((algebraMap R (reesAlgebra I) a : reesAlgebra I) : Polynomial R)
  rw [Polynomial.monomial_zero_left, Subalgebra.coe_algebraMap, Polynomial.algebraMap_eq]

/-- `I·R[It]` is spanned by degree-zero elements, hence homogeneous. -/
theorem shiftIdeal_isHomogeneous :
    (shiftIdeal I).IsHomogeneous (KltDP.ReesGrading.component I) := by
  have hspan : shiftIdeal I
      = Ideal.span (⇑(algebraMap R (reesAlgebra I)) '' (I : Set R)) := rfl
  rw [hspan]
  refine Ideal.homogeneous_span (KltDP.ReesGrading.component I) _ ?_
  rintro x ⟨a, _, rfl⟩
  exact ⟨0, algebraMap_mem_component_zero I a⟩

/-- Properness, from properness of `I`. -/
theorem shiftIdeal_ne_top (hI : I ≠ ⊤) : shiftIdeal I ≠ ⊤ := by
  intro htop
  have h1 : (1 : reesAlgebra I) ∈ shiftIdeal I := by
    rw [htop]; trivial
  have hc := shiftIdeal_le_coeffShift I h1 0
  rw [show ((1 : reesAlgebra I) : Polynomial R) = 1 from rfl, Polynomial.coeff_one,
    if_pos rfl, pow_one] at hc
  exact hI ((Ideal.eq_top_iff_one I).mpr hc)

/-! ## Primality, and the domain property -/

/-- **`I·R[It]` is prime when orders add sharply.** Reduced to homogeneous elements, where the product
is a single monomial and `SharpProduct` applies directly. -/
theorem shiftIdeal_isPrime (hI : I ≠ ⊤) (hs : SharpProduct I) : (shiftIdeal I).IsPrime := by
  refine (shiftIdeal_isHomogeneous I).isPrime_of_homogeneous_mem_or_mem
    (shiftIdeal_ne_top I hI) ?_
  rintro x y ⟨a, hxa⟩ ⟨b, hyb⟩ hxy
  obtain ⟨r, rfl⟩ := hxa
  obtain ⟨s, rfl⟩ := hyb
  by_contra hcon
  push_neg at hcon
  obtain ⟨hx, hy⟩ := hcon
  have hr : (r : R) ∉ I ^ (a + 1) := fun h => hx ((single_mem_shiftIdeal_iff I a r).mpr h)
  have hs' : (s : R) ∉ I ^ (b + 1) := fun h => hy ((single_mem_shiftIdeal_iff I b s).mpr h)
  have hmul : (r : R) * (s : R) ∈ I ^ (a + b) := by
    rw [pow_add]; exact Ideal.mul_mem_mul r.property s.property
  have hprod : KltDP.ReesGrading.single I a r * KltDP.ReesGrading.single I b s
      = KltDP.ReesGrading.single I (a + b) ⟨(r : R) * (s : R), hmul⟩ := by
    apply Subtype.ext
    rw [Subalgebra.coe_mul, KltDP.ReesGrading.single_val, KltDP.ReesGrading.single_val,
      KltDP.ReesGrading.single_val, Polynomial.monomial_mul_monomial]
  rw [hprod] at hxy
  exact hs a b (r : R) (s : R) r.property hr s.property hs'
    ((single_mem_shiftIdeal_iff I (a + b) _).mp hxy)

/-- **The associated graded ring is a domain when orders add sharply.** -/
theorem isDomain_of_sharpProduct (hI : I ≠ ⊤) (hs : SharpProduct I) :
    IsDomain (AssociatedGraded I) := by
  have hp : (shiftIdeal I).IsPrime := shiftIdeal_isPrime I hI hs
  show IsDomain ((reesAlgebra I) ⧸ shiftIdeal I)
  exact (Ideal.Quotient.isDomain_iff_prime (shiftIdeal I)).mpr hp

end KltDP.RingTheory.AssociatedGradedPrime
