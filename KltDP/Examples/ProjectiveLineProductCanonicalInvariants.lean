import KltDP.Examples.ProjectiveLineProductLattice
import KltDP.Examples.ProjectiveLineProductNumericalRank
import KltDP.Examples.FrobeniusInitialCanonicalFormula
import KltDP.Geometry.SmoothCanonicalCartierPicard

/-!
# The original product has canonical square eight and Noether sum ten

The canonical divisor is the existing representative of the original
smooth top-differential line. Its class and the ruling pairing have already
been proved geometrically. Only their original numerical calculation is joined here.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Examples.ProjectiveLineProductCanonicalInvariants

open KltDP.Geometry KltDP.Geometry.SmoothSurfaceKaehlerAtlas
open KltDP.Geometry.SmoothCanonicalCartierRepresentative SmoothCanonicalCartierPicard
open FrobeniusProjectivePoints FrobeniusStageZeroProjective
open FrobeniusGraphPicardClassFiberClasses FrobeniusRulingClassPairing
open ProjectiveLineProductPicardGeneration ProjectiveLineProductLattice
open ProjectiveLineProductNumericalRank FrobeniusInitialCanonicalFormula

variable {k : Type u} [Field k] [IsAlgClosed k]

local instance canonicalInvariantsProductIntegral : IsIntegral (projectiveProduct k) :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

theorem canonicalPicard_square :
    basePairing
      (Additive.ofMul (canonicalSheafOfSmoothSurface (projectiveProductToSpec (k := k))).toPic)
      (Additive.ofMul (canonicalSheafOfSmoothSurface (projectiveProductToSpec (k := k))).toPic) =
        8 := by
  rw [canonicalPicard_eq_fiberClasses, ← rulingPicardEquiv_apply (-2) (-2),
    pairing_coordinates]
  norm_num

/-- The square of the actual original smooth canonical Cartier representative. -/
theorem canonicalCartier_square :
    (projectiveProductSurface (k := k)).intersectionPairing baseRegular
      (cartierRepresentative (projectiveProductToSpec (k := k)))
      (cartierRepresentative (projectiveProductToSpec (k := k))) = 8 := by
  rw [← (projectiveProductSurface (k := k)).picardPairing_class baseRegular]
  change basePairing
    (cartierPicardHom (projectiveProduct k) (cartierRepresentative projectiveProductToSpec))
    (cartierPicardHom (projectiveProduct k) (cartierRepresentative projectiveProductToSpec)) = 8
  rw [cartierPicardHom_representative]
  exact canonicalPicard_square

/-- The original Noether relation, for the original canonical representative. -/
theorem noetherRelation :
    (projectiveProductSurface (k := k)).NoetherRelationFor baseRegular
      (cartierRepresentative (projectiveProductToSpec (k := k))) := by
  change (projectiveProductSurface (k := k)).intersectionPairing baseRegular _ _ +
    ((projectiveProductSurface (k := k)).picardRank : ℤ) = 10
  rw [canonicalCartier_square, picardRank_eq_two]
  norm_num

end KltDP.Examples.ProjectiveLineProductCanonicalInvariants

#check @KltDP.Examples.ProjectiveLineProductCanonicalInvariants.canonicalCartier_square
#check @KltDP.Examples.ProjectiveLineProductCanonicalInvariants.noetherRelation
#print axioms KltDP.Examples.ProjectiveLineProductCanonicalInvariants.noetherRelation
