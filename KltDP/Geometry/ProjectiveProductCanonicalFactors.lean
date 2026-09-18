import KltDP.Geometry.ProjectiveLineCanonicalFrameUnit
import KltDP.Geometry.ProjectiveLinePicardExponent
import KltDP.Geometry.SchemeInvertibleSheafPullback
import KltDP.Examples.FrobeniusProjectiveCoordinatePicard

/-!
# Actual canonical factors for a product of projective lines

The original cotangent line of the projective line is isomorphic to the
tensor square of its original coordinate-point kernel ideal. This follows
from their proved transition exponents and the injective exponent on the
existing Picard group. Both the class equality and the actual sheaf
isomorphism are transported by the original scheme-module pullback.

These results identify the individual factors. They do not define or
identify the canonical sheaf of a product. The comparison with the second
exterior power of the product's original differential sheaf is separate.

Reuse boundary: the pinned Mathlib revision is
`c44e0c8ee63ca166450922a373c7409c5d26b00b`. Its
`RingTheory/Kaehler/TensorProduct.lean`, and the current primary documentation
at https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Kaehler/TensorProduct.html,
provide relative base-change comparisons, not the product differential
splitting needed for the remaining comparison. No external proof is ported
here; all proof inputs are existing project declarations.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Geometry.ProjectiveProductCanonicalFactors

open KltDP.Examples.FrobeniusProjectiveCoordinatePicard

variable (k : Type u) [Field k]

local instance factorMonoidal : MonoidalCategory (projectiveSpace k 1).Modules :=
  Scheme.Modules.monoidalCategory (projectiveSpace k 1)

/-- The actual canonical class is the square of the actual coordinate-point ideal class. -/
theorem canonical_toPic_eq_coordinate_square :
    (ProjectiveLineCanonical.canonicalSheaf k).toPic =
      (coordinateIdealLine (k := k)).toPic ^ 2 := by
  apply ProjectiveLinePicardExponent.hom_injective k
  change Multiplicative.ofAdd (ProjectiveLinePicardExponent.value k _) =
    Multiplicative.ofAdd (ProjectiveLinePicardExponent.value k _)
  apply congrArg Multiplicative.ofAdd
  rw [ProjectiveLinePicardExponent.value_toPic,
    ProjectiveLineCanonicalFrameUnit.exponent_canonicalSheaf_eq_neg_two,
    pow_two, ProjectiveLinePicardExponent.value_mul,
    coordinatePicardValue_eq_neg_one]
  norm_num

/-- An isomorphism between the original cotangent line and the actual ideal's tensor square. -/
def canonicalIsoCoordinateTensor :
    (ProjectiveLineCanonical.canonicalSheaf k).obj ≅
      (coordinateIdealLine (k := k)).obj ⊗ (coordinateIdealLine (k := k)).obj := by
  have hclass : toSkeleton (ProjectiveLineCanonical.canonicalSheaf k).obj =
      toSkeleton ((coordinateIdealLine (k := k)).obj ⊗
        (coordinateIdealLine (k := k)).obj) := by
    rw [Skeleton.toSkeleton_tensorObj]
    have h := congrArg (fun p : (projectiveSpace k 1).Pic =>
      (p : Skeleton (projectiveSpace k 1).Modules))
      (canonical_toPic_eq_coordinate_square k)
    simpa only [pow_two, Units.val_mul, InvertibleSheaf.toPic_val] using h
  exact Classical.choice (show Nonempty
    ((ProjectiveLineCanonical.canonicalSheaf k).obj ≅
      (coordinateIdealLine (k := k)).obj ⊗ (coordinateIdealLine (k := k)).obj) from
        Quotient.exact hclass)

variable {Y : Scheme.{u}} (f : Y ⟶ projectiveSpace k 1)

/-- The equality holds for the actual pulled-back lines along any original scheme morphism. -/
theorem pullback_canonical_toPic_eq_coordinate_square :
    (pullbackInvertibleSheaf f (ProjectiveLineCanonical.canonicalSheaf k)).toPic =
      (pullbackInvertibleSheaf f (coordinateIdealLine (k := k))).toPic ^ 2 := by
  rw [← schemePicardPullbackHom_toPic,
    canonical_toPic_eq_coordinate_square, map_pow, schemePicardPullbackHom_toPic]

/-- The actual pullback functor and its tensor comparison transport the sheaf isomorphism. -/
def pullbackCanonicalIsoCoordinateTensor :
    letI := Scheme.Modules.monoidalCategory Y
    (pullbackInvertibleSheaf f (ProjectiveLineCanonical.canonicalSheaf k)).obj ≅
      (pullbackInvertibleSheaf f (coordinateIdealLine (k := k))).obj ⊗
        (pullbackInvertibleSheaf f (coordinateIdealLine (k := k))).obj := by
  letI := Scheme.Modules.monoidalCategory Y
  exact (schemeModulePullback f).mapIso (canonicalIsoCoordinateTensor k) ≪≫
    schemeModulePullbackTensorIso f _ _

end KltDP.Geometry.ProjectiveProductCanonicalFactors
