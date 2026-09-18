import KltDP.Geometry.FrobeniusNormalFactorComplement
import KltDP.Geometry.SurfaceRegularityOnIsomorphismOpen

/-!
The original Frobenius source is regular by its proved smoothness. The
actual restricted isomorphism therefore makes every point away from the
null-locus image regular on the original target. This is only containment
of the actual singular points, not equality or a singularity classification.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction

open KltDP.Examples FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
open FrobeniusProjectivityProved FrobeniusMultiCentreGraphExceptionalPairing

variable {k : Type u} [Field k] [IsAlgClosed k]
  (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
  (a : Fin n → k) (ha : Function.Injective a)

/-- Actual singular target points are contained in the image of the
original null locus, for the same map and its actual isomorphism open. -/
theorem singularPoints_subset_nullImage (Y : NormalProjectiveSurface k)
    (π : multiSurface (q + 1) n a ⟶ Y.toScheme) (U : Y.toScheme.Opens)
    [IsIso (π ∣_ U)]
    (hU : (U : Set Y.toScheme) =
      (π.base '' Positivity.nullLocus (multiStructure (q + 1) n a) (originalLine q n a ha))ᶜ) :
    (Y.singularPoints : Set Y.Point) ⊆
      π.base '' Positivity.nullLocus (multiStructure (q + 1) n a) (originalLine q n a ha) := by
  have h := RegularPointsOnIsomorphismOpen.singularPoints_subset_compl Y π U
    (multiSurfaceSurface_regularPoints (q + 1) n a ha
      (originalMultiStructureProjective k (q + 1) n a))
  simpa only [hU, compl_compl] using h

end KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction
