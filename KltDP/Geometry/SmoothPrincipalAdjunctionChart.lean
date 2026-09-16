import KltDP.RingTheory.SmoothPrincipalConormalDeterminant
import KltDP.Geometry.TopExteriorBaseChange
import KltDP.Geometry.AffineModuleTildePullback
import KltDP.Geometry.AffineKaehlerTildeLocalization

/-!
# Actual smooth principal adjunction on an affine equation chart

The original Kähler sheaf on `Spec(A/J)` is identified with the actual
pullback of tilde of `∧²Ω[A/R]`. The chosen regular equation trivializes
the normal line on this chart. The equivalence is built from the produced
conormal determinant map, canonical exterior base change, and the accepted
original affine Kähler and tilde/pullback comparisons.

This is an affine chart theorem, not the global adjunction isomorphism.
Gluing the actual equation transitions and matching the accepted smooth
surface Kähler-frame canonical sheaf remain separate obligations.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

universe u

namespace KltDP.Geometry.SmoothPrincipalAdjunctionChart

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] (J : Ideal A)
  [Algebra.IsStandardSmoothOfRelativeDimension 2 R A]
  [Algebra.IsStandardSmoothOfRelativeDimension 1 R (A ⧸ J)]

local instance ambientStandardSmooth : Algebra.IsStandardSmooth R A :=
  Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth (R := R) (S := A) 2

variable (d : J) (hJ : Ideal.span {(d : A)} = J)
  (hregular : (d : A) ∈ nonZeroDivisors A)

/-- The local adjunction map with the exterior square retained over the ambient ring. -/
def moduleEquiv :
    KaehlerDifferential R (A ⧸ J) ≃ₗ[A ⧸ J]
      (A ⧸ J) ⊗[A] (⋀[A]^2 (KaehlerDifferential R A)) :=
  (KltDP.RingTheory.SmoothPrincipalConormalDeterminant.determinantEquiv R A J d hJ hregular).trans
    (TopExteriorBaseChange.equiv (A ⧸ J)
      (AffineTopDifferentialFrame.standardSmoothDifferentialBasis R A)).symm

/-- Canonical exterior base change identifies this map with the original defining-equation wedge. -/
theorem moduleEquiv_mapBaseChange (m : (A ⧸ J) ⊗[A] KaehlerDifferential R A) :
    TopExteriorBaseChange.equiv (A ⧸ J)
        (AffineTopDifferentialFrame.standardSmoothDifferentialBasis R A)
        (moduleEquiv R A J d hJ hregular (KaehlerDifferential.mapBaseChange R A (A ⧸ J) m)) =
      exteriorPower.ιMulti (A ⧸ J) 2 ![1 ⊗ₜ[A] KaehlerDifferential.D R A (d : A), m] := by
  change TopExteriorBaseChange.equiv (A ⧸ J)
      (AffineTopDifferentialFrame.standardSmoothDifferentialBasis R A)
      ((TopExteriorBaseChange.equiv (A ⧸ J)
        (AffineTopDifferentialFrame.standardSmoothDifferentialBasis R A)).symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  exact KltDP.RingTheory.SmoothPrincipalConormalDeterminant.determinantEquiv_mapBaseChange
    R A J d hJ hregular m

/-- The local isomorphism is on the original quotient scheme and the actual scheme pullback. -/
def iso :
    SchemeKaehlerSheaf.baseRingSheaf
        (Spec.map (CommRingCat.ofHom (algebraMap R (A ⧸ J)))) ≅
      (schemeModulePullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).obj
        (ModuleCat.of A (⋀[A]^2 (KaehlerDifferential R A))).tilde :=
  AffineKaehlerTildeLocalization.iso R (A ⧸ J) ≪≫
    AffineModuleTilde.linearEquivIso
      (M := ModuleCat.of (A ⧸ J) (KaehlerDifferential R (A ⧸ J)))
      (N := (ModuleCat.extendScalars (Ideal.Quotient.mk J)).obj
        (ModuleCat.of A (⋀[A]^2 (KaehlerDifferential R A))))
      (moduleEquiv R A J d hJ hregular) ≪≫
    (AffineModuleTilde.pullbackIso (Ideal.Quotient.mk J)
      (ModuleCat.of A (⋀[A]^2 (KaehlerDifferential R A)))).symm

end KltDP.Geometry.SmoothPrincipalAdjunctionChart
