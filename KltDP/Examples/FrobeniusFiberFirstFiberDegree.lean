import KltDP.Examples.FrobeniusRulingPairingValues
import KltDP.Examples.FrobeniusStrictTransformFiberRowsValues
import KltDP.Geometry.PrimeCurveDegreeTransport

/-!
# The strict horizontal fibre has first ruling degree one

The actual base horizontal fibre is isomorphic to the projective line over `k`. Degree transport
identifies its restriction degree with the same projective-line Euler degree that computes the
strict fibre's pairing upstairs. Its base Cartier class is `b`, and the proved ruling matrix has
`a · b = 1`, so the strict fibre has `F̃ · a = 1`.

The final bundle contains the four numerical ruling rows on one actual contact tower. Algebraic
closure and projectivity of the indicated stage remain explicit. Simultaneous multi-centre
transport and the full Frobenius-family proposition remain separate.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusFiberFirstFiberDegree

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open KltDP.Geometry.NormalProjectiveSurface.PrimeCurve
open KltDP.Geometry.PrimeCurveInclusionLift KltDP.Geometry.PrimeCurveDegreeTransport
open KltDP.Geometry.ProjectiveLineIdealLineDegree
open FrobeniusProjectivePoints FrobeniusGraphPicardClassZeroFiber FrobeniusGraphClosed
open FrobeniusStageZeroProjective FrobeniusRulingClassPairing FrobeniusRulingPairingValues
open FrobeniusGlobalBlowupStages FrobeniusStrictTransformPairing FrobeniusStrictTransformFiberRows
open FrobeniusGraphPicardClassFiberClasses FrobeniusGraphPicardClassTotalTransform
open FrobeniusGraphFirstFiberDegree FrobeniusStrictTransformFiberRowsValues

variable {k : Type u} [Field k] [IsAlgClosed k]

local instance horizontalDegreeLineIntegral : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

/-- The base horizontal prime curve's inverse identification with its original projective line. -/
abbrev horizontalCurveToLine (c : k) : (horizontalPrimeCurve c).toScheme ⟶ projectiveSpace k 1 :=
  inv (lift (horizontalPrimeCurve c) (horizontalFiberMorphism c) rfl)

theorem horizontalPrimeCurve_inclusion (c : k) :
    (horizontalPrimeCurve c).inclusion = horizontalCurveToLine c ≫ horizontalFiberMorphism c :=
  inclusion_eq_inv_lift (horizontalPrimeCurve c) (horizontalFiberMorphism c) rfl

theorem horizontalFiberMorphism_base (c : k) :
    horizontalFiberMorphism c ≫ projectiveProductToSpec = projectiveSpaceToSpec k 1 := by
  change horizontalFiberMorphism c ≫ (firstProjection ≫ projectiveSpaceToSpec k 1) = _
  rw [← Category.assoc, horizontalFiberMorphism_fst, Category.id_comp]

theorem horizontalCurveToLine_base (c : k) :
    horizontalCurveToLine c ≫ projectiveSpaceToSpec k 1 = (horizontalPrimeCurve c).toSpec := by
  change horizontalCurveToLine c ≫ projectiveSpaceToSpec k 1 =
    (horizontalPrimeCurve c).inclusion ≫ projectiveProductToSpec
  rw [horizontalPrimeCurve_inclusion, Category.assoc, horizontalFiberMorphism_base]

/-- The base horizontal curve's actual Picard degree is the Euler degree along its original section. -/
theorem horizontalPrimeCurve_picardRestrictionDegree (c : k) (q : (projectiveProduct k).Pic) :
    (horizontalPrimeCurve c).picardRestrictionDegree q =
      eulerDegree (projectiveSpaceToSpec k 1)
        (schemePicardPullbackHom (horizontalFiberMorphism c) q) := by
  change (horizontalPrimeCurve c).picardDegree
    (schemePicardPullbackHom (horizontalPrimeCurve c).inclusion q) = _
  rw [horizontalPrimeCurve_inclusion, schemePicardPullbackHom_comp]
  exact picardDegree_pullback_iso (horizontalPrimeCurve c) (horizontalCurveToLine c)
    (projectiveSpaceToSpec k 1) (horizontalCurveToLine_base c)
    (schemePicardPullbackHom (horizontalFiberMorphism c) q)

/-- The actual strict horizontal fibre has degree one against the total first fibre class. -/
theorem fiberStrictPairing_firstFiberTotalClass_eq_one (n : ℕ)
    (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap) :
    fiberStrictPairing n hproj (firstFiberTotalClass (n + 1)) = 1 := by
  rw [fiberStrictPairing_firstFiber, fiberSectionBase_eq]
  have h : (projectiveProductSurface (k := k)).picardRestrictionDegreeHom
      (horizontalPrimeCurve (0 : k)) firstFiberClass = 1 :=
    (basePairing_horizontal_right firstFiberClass (0 : k)).symm.trans basePairing_first_second_one
  rw [firstFiberClass, map_neg, picardRestrictionDegreeHom_apply,
    horizontalPrimeCurve_picardRestrictionDegree] at h
  exact h

/-- The four ruling rows for the actual strict graph and horizontal fibre on a single contact tower. -/
theorem contactTower_ruling_rows (n : ℕ)
    (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)
    (m : ℕ) :
    graphStrictPairing n hproj m (firstFiberTotalClass (n + 1)) = 1 ∧
    graphStrictPairing n hproj m (secondFiberTotalClass (n + 1)) = (m + (n + 1) : ℤ) ∧
    fiberStrictPairing n hproj (firstFiberTotalClass (n + 1)) = 1 ∧
    fiberStrictPairing n hproj (secondFiberTotalClass (n + 1)) = 0 :=
  ⟨graphStrictPairing_firstFiberTotalClass_eq_one n hproj m,
    graphStrictPairing_secondFiberTotalClass_eq n hproj m,
    fiberStrictPairing_firstFiberTotalClass_eq_one n hproj,
    fiberStrictPairing_secondFiber_zero n hproj⟩

end KltDP.Examples.FrobeniusFiberFirstFiberDegree
