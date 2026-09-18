import KltDP.Geometry.ProjectiveProductCanonicalDifferentialIso
import KltDP.Geometry.ProjectiveProductCanonicalExteriorIso
import KltDP.Geometry.ProjectiveProductCanonicalFactors
import KltDP.Geometry.SmoothCanonicalExteriorComparison
import KltDP.Geometry.SchemeExteriorPowerMap
import KltDP.Examples.FrobeniusGlobalBlowupSmooth

/-!
# The original canonical sheaf of the projective product

The original global differential decomposition, the ordered exterior-square
comparison for the two actual pulled cotangent lines, and the original
smooth canonical/exterior comparison identify the canonical sheaf with the
tensor of the two pulled projective-line canonical sheaves. The resulting
Picard equality concerns the original smooth canonical construction.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Geometry.ProjectiveProductCanonicalFormula

open KltDP.Examples.FrobeniusProjectivePoints KltDP.Examples.FrobeniusGraphClosed
open KltDP.Examples.FrobeniusGlobalBlowupSmooth SmoothSurfaceKaehlerAtlas

variable (k : Type u) [Field k]

local instance productMonoidal : MonoidalCategory (projectiveProduct k).Modules :=
  Scheme.Modules.monoidalCategory (projectiveProduct k)

/-- The actual canonical line on the first projective-line factor, pulled by the original projection. -/
abbrev firstCanonical : InvertibleSheaf (projectiveProduct k) :=
  pullbackInvertibleSheaf (firstProjection (k := k)) (ProjectiveLineCanonical.canonicalSheaf k)

/-- The actual canonical line on the second factor, pulled by the original projection. -/
abbrev secondCanonical : InvertibleSheaf (projectiveProduct k) :=
  pullbackInvertibleSheaf (secondProjection (k := k)) (ProjectiveLineCanonical.canonicalSheaf k)

/-- The independently constructed smooth canonical line is the tensor of the two original
pulled cotangent lines. The comparison is proved through the actual global exterior sheaf. -/
def canonicalSheafIsoTensor :
    (canonicalSheafOfSmoothSurface (projectiveProductToSpec (k := k))).obj ≅
      (firstCanonical k).obj ⊗ (secondCanonical k).obj :=
  SmoothCanonicalExteriorComparison.canonicalSheafOfSmoothSurfaceIsoExterior
      (projectiveProductToSpec (k := k)) ≪≫
    (SchemeExteriorPower.mapIso (ProjectiveProductCanonicalDifferentialIso.iso k) 2).symm ≪≫
    (ProjectiveProductCanonicalExteriorIso.iso (firstCanonical k) (secondCanonical k)).symm

/-- The original smooth canonical class equals the product of the two original pulled classes. -/
theorem canonical_toPic :
    (canonicalSheafOfSmoothSurface (projectiveProductToSpec (k := k))).toPic =
      (firstCanonical k).toPic * (secondCanonical k).toPic := by
  apply Units.ext
  change ((canonicalSheafOfSmoothSurface (projectiveProductToSpec (k := k))).toPic :
      Skeleton (projectiveProduct k).Modules) =
    ((firstCanonical k).toPic : Skeleton (projectiveProduct k).Modules) *
      ((secondCanonical k).toPic : Skeleton (projectiveProduct k).Modules)
  rw [InvertibleSheaf.toPic_val, InvertibleSheaf.toPic_val, InvertibleSheaf.toPic_val,
    ← Skeleton.toSkeleton_tensorObj]
  exact Quotient.sound ⟨canonicalSheafIsoTensor k⟩

end KltDP.Geometry.ProjectiveProductCanonicalFormula
