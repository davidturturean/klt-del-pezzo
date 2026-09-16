import KltDP.Examples.FrobeniusMultiCentreGraphCartierFactorization
import KltDP.Examples.FrobeniusTowerPicardRelation

/-!
# The original global strict-graph class on the multi-centre surface

Apply the actual Cartier-to-Picard homomorphism to the global Cartier
factorization. The original exceptional component classes are differences
of consecutive total-transform classes. The accepted additive-group
telescoping theorem therefore turns each weighted cluster contribution
into the sum of its original total exceptional classes.

This gives the class of the actual global strict graph and its original
kernel line, with prime `p = q + 1` in characteristic `p`, algebraic
closure and distinct selected affine parameters. No global class row,
projectivity, or numerical intersection formula is supplied as input.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreGraphPicardClass

open KltDP.Geometry
open FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
  FrobeniusMultiCentreExceptionalCartier FrobeniusMultiCentreGraphCartierTotal
  FrobeniusMultiCentreGraphCartierStrict FrobeniusMultiCentreGraphCartierFactorization
  FrobeniusTowerPicardRelation

variable {k : Type u} [Field k] [IsAlgClosed k]
  (q n : ℕ) (a : Fin n → k) (ha : Function.Injective a)

include ha

/-- Each actual weighted exceptional divisor represents the sum of the
original total exceptional classes in its cluster. -/
theorem weightedExceptional_picard_eq_sum (i : Fin n) :
    letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
    cartierPicardHom _ (multiWeightedExceptionalDivisor q n a ha i) =
      ∑ j : Fin (q + 1), exceptionalClass (q + 1) n a i j := by
  letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
  simp only [multiWeightedExceptionalDivisor, map_add, map_sum, map_nsmul,
    multiExceptionalDivisor_picard_inl, multiExceptionalDivisor_picard_inr]
  exact telescope_castSucc q (exceptionalClass (q + 1) n a i)

variable [Fact (q + 1).Prime] [CharP k (q + 1)]

/-- The actual global total class is the strict class plus the original total exceptional classes. -/
theorem totalClass_eq_strict_add_exceptional :
    letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
    (q + 1) • multiFirstFiberClass (q + 1) n a + multiSecondFiberClass (q + 1) n a =
      cartierPicardHom _ (multiGraphStrictDivisor q n a ha) +
        ∑ i : Fin n, ∑ j : Fin (q + 1), exceptionalClass (q + 1) n a i j := by
  letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
  have h := congrArg (cartierPicardHom (multiSurface (q + 1) n a))
    (multiGraphTotalDivisor_eq_weighted q n a ha)
  simpa only [multiGraphTotalDivisor_picard, map_add, map_sum,
    weightedExceptional_picard_eq_sum] using h

/-- The class of the actual global strict graph is `p a + b - ∑ᵢⱼ Eᵢⱼ`. -/
theorem strictGraphDivisor_picard_row :
    letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
    cartierPicardHom _ (multiGraphStrictDivisor q n a ha) =
      (q + 1) • multiFirstFiberClass (q + 1) n a + multiSecondFiberClass (q + 1) n a -
        ∑ i : Fin n, ∑ j : Fin (q + 1), exceptionalClass (q + 1) n a i j := by
  letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
  exact eq_sub_iff_add_eq.mpr (totalClass_eq_strict_add_exceptional q n a ha).symm

/-- The same global row for the negative class of the original strict-graph kernel line. -/
theorem strictGraphKernelLine_picard_row :
    -Additive.ofMul (multiGraphStrictKernelLine q n a ha).toPic =
      (q + 1) • multiFirstFiberClass (q + 1) n a + multiSecondFiberClass (q + 1) n a -
        ∑ i : Fin n, ∑ j : Fin (q + 1), exceptionalClass (q + 1) n a i j := by
  letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
  rw [← multiGraphStrictDivisor_picard q n a ha]
  exact strictGraphDivisor_picard_row q n a ha

end KltDP.Examples.FrobeniusMultiCentreGraphPicardClass
