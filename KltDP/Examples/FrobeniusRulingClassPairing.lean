import KltDP.Geometry.PrimeCurveClassPairing
import KltDP.Examples.ProjectiveProductFiberClassInvariance
import KltDP.Examples.FrobeniusStageZeroProjective
import KltDP.Geometry.PrimeCurveOfClosedImmersion

/-!
# Actual ruling curves and their zero self-intersections on the product

The horizontal and vertical fibres are closed immersions of the projective line, hence prime
curves of the accepted surface `P¹ × P¹`. The accepted kernel-line class comparison identifies
their Cartier classes with `b` and `a`. Two fibres of the same projection at distinct rational
points are disjoint. Their actual ideal pullback is consequently trivial, proving `a² = b² = 0`
for the accepted symmetric Picard pairing.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusRulingClassPairing

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open KltDP.Geometry.NormalProjectiveSurface.PrimeCurve
open KltDP.Geometry.PrimeCurveClassPairing KltDP.Geometry.PrimeCurveTransversalPoint
open KltDP.Geometry.PrimeCurveOfClosedImmersion
open FrobeniusProjectivePoints FrobeniusUnaffectedFibers FrobeniusGraphClosed
open FrobeniusGraphPicardClassZeroFiber FrobeniusGraphPicardClassFiberClasses
open FrobeniusStageSurface FrobeniusStageZeroProjective
open ProjectiveProductFiberClassInvariance

variable {k : Type u} [Field k] [IsAlgClosed k]

local instance rulingPairingLineIntegral : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

/-- The base product is regular, by its accepted smooth surface structure. -/
abbrev baseRegular : ∀ x : (projectiveProductSurface (k := k)).Point,
    RegularPoint (projectiveProductSurface (k := k)).toScheme x :=
  stageSurface_regularPoints 0 stage_zero_projective

/-- The accepted Picard pairing of the product, in additive notation. -/
abbrev basePairing (p q : Additive (projectiveProduct k).Pic) : ℤ :=
  pairing projectiveProductSurface baseRegular p q

/-- The actual horizontal fibre `y = c`, as a prime curve of the product. -/
def horizontalPrimeCurve (c : k) : (projectiveProductSurface (k := k)).PrimeCurve :=
  primeCurveOfIsoProjectiveLine projectiveProductSurface (horizontalFiberMorphism c) (Iso.refl _)

/-- The actual vertical fibre `x = c`, as a prime curve of the product. -/
def verticalPrimeCurve (c : k) : (projectiveProductSurface (k := k)).PrimeCurve :=
  primeCurveOfIsoProjectiveLine projectiveProductSurface (verticalFiberMorphismAt c) (Iso.refl _)

theorem horizontalPrimeCurve_class (c : k) :
    cartierPicardHom (projectiveProductSurface (k := k)).toScheme
      ((projectiveProductSurface (k := k)).primeCurveCartier baseRegular (horizontalPrimeCurve c)) =
        secondFiberClass :=
  (cartierPicardHom_primeCurveCartier_of_kernel baseRegular (horizontalPrimeCurve c)
    (horizontalFiberMorphism c) rfl (FrobeniusMultiCentreIsoOpenClasses.horizontalFiberLine c)
    rfl).trans (horizontalFiberClass_eq_secondFiberClass c)

theorem verticalPrimeCurve_class (c : k) :
    cartierPicardHom (projectiveProductSurface (k := k)).toScheme
      ((projectiveProductSurface (k := k)).primeCurveCartier baseRegular (verticalPrimeCurve c)) =
        firstFiberClass :=
  (cartierPicardHom_primeCurveCartier_of_kernel baseRegular (verticalPrimeCurve c)
    (verticalFiberMorphismAt c) rfl (verticalFiberLine c) rfl).trans
      (verticalFiberClass_eq_firstFiberClass c)

theorem basePairing_horizontal_right (p : Additive (projectiveProduct k).Pic) (c : k) :
    basePairing p secondFiberClass =
      (projectiveProductSurface (k := k)).picardRestrictionDegreeHom (horizontalPrimeCurve c) p := by
  rw [← horizontalPrimeCurve_class c]
  exact pairing_primeCurve_right _ _ _ _

theorem basePairing_vertical_right (p : Additive (projectiveProduct k).Pic) (c : k) :
    basePairing p firstFiberClass =
      (projectiveProductSurface (k := k)).picardRestrictionDegreeHom (verticalPrimeCurve c) p := by
  rw [← verticalPrimeCurve_class c]
  exact pairing_primeCurve_right _ _ _ _

/-- Distinct horizontal fibres are disjoint, by their second coordinate. -/
theorem horizontalFibres_disjoint (c d : k) (hcd : c ≠ d) :
    Disjoint (Set.range (horizontalFiberMorphism c).base)
      (Set.range (horizontalFiberMorphism d).base) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨s, rfl⟩ ⟨t, ht⟩
  have h := congrArg (secondProjection (k := k)).base ht
  rw [← Scheme.comp_base_apply, ← Scheme.comp_base_apply, horizontalFiberMorphism_snd,
    horizontalFiberMorphism_snd, Scheme.comp_base_apply, Scheme.comp_base_apply,
    Subsingleton.elim ((projectiveSpaceToSpec k 1).base t) (IsLocalRing.closedPoint k),
    Subsingleton.elim ((projectiveSpaceToSpec k 1).base s) (IsLocalRing.closedPoint k)] at h
  exact hcd (point_injective (k := k) h).symm

/-- Distinct vertical fibres are disjoint, by their first coordinate. -/
theorem verticalFibres_disjoint (c d : k) (hcd : c ≠ d) :
    Disjoint (Set.range (verticalFiberMorphismAt c).base)
      (Set.range (verticalFiberMorphismAt d).base) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨s, rfl⟩ ⟨t, ht⟩
  have h := congrArg (firstProjection (k := k)).base ht
  rw [← Scheme.comp_base_apply, ← Scheme.comp_base_apply, verticalFiberMorphismAt_fst,
    verticalFiberMorphismAt_fst, Scheme.comp_base_apply, Scheme.comp_base_apply,
    Subsingleton.elim ((projectiveSpaceToSpec k 1).base t) (IsLocalRing.closedPoint k),
    Subsingleton.elim ((projectiveSpaceToSpec k 1).base s) (IsLocalRing.closedPoint k)] at h
  exact hcd (point_injective (k := k) h).symm

/-- `a² = 0`, by computing against the disjoint vertical fibres at zero and one. -/
theorem basePairing_first_self_zero :
    basePairing (firstFiberClass (k := k)) firstFiberClass = 0 := by
  rw [basePairing_vertical_right firstFiberClass (0 : k),
    ← verticalFiberClass_eq_firstFiberClass (1 : k)]
  apply restrictionDegreeHom_neg_kernel_zero projectiveProductSurface (verticalPrimeCurve (0 : k))
    (verticalFiberMorphismAt (1 : k)) (verticalFiberLine (1 : k)) rfl
  rw [range_inclusion]
  exact verticalFibres_disjoint (0 : k) 1 zero_ne_one

/-- `b² = 0`, by computing against the disjoint horizontal fibres at zero and one. -/
theorem basePairing_second_self_zero :
    basePairing (secondFiberClass (k := k)) secondFiberClass = 0 := by
  rw [basePairing_horizontal_right secondFiberClass (0 : k),
    ← horizontalFiberClass_eq_secondFiberClass (1 : k)]
  apply restrictionDegreeHom_neg_kernel_zero projectiveProductSurface
    (horizontalPrimeCurve (0 : k)) (horizontalFiberMorphism (1 : k))
    (FrobeniusMultiCentreIsoOpenClasses.horizontalFiberLine (1 : k)) rfl
  rw [range_inclusion]
  exact horizontalFibres_disjoint (0 : k) 1 zero_ne_one

end KltDP.Examples.FrobeniusRulingClassPairing
