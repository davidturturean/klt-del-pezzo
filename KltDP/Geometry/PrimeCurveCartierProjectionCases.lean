import KltDP.Geometry.CartierPullbackComparison
import KltDP.Geometry.PrimeCurveIntersectionNumber
import KltDP.Geometry.PrimeCurveTransportPullback
import KltDP.Geometry.PrimeCurveInclusionLift

/-!
# Two effective-Cartier projection cases for actual prime curves

For an effective Cartier divisor with regular equations and a morphism preserving
the generic point, the accepted Cartier/Picard comparison identifies the class of
the actual pulled-back divisor. Applying the accepted restriction-degree
transport gives intersection-number projection when the induced curve map is an
isomorphism over the original base field. The actual factorization of a curve's
inclusion through `Spec R`, for a PID `R`, gives intersection number zero; the
field-valued point case is exported separately.

The commuting morphisms and the curve isomorphism's compatibility with the base
field are explicit. No general proper cycle pushforward or finite-map degree
formula is asserted.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.PrimeCurveCartierProjectionCases

open KltDP.Geometry.CartierDivisorPullbackIdeal
  KltDP.Geometry.CartierPullbackComparison

variable {k : Type u} [Field k] {X : NormalProjectiveSurface k}

section Isomorphism

variable {Y : NormalProjectiveSurface k}
  (C' : X.PrimeCurve) (C : Y.PrimeCurve) (π : X.toScheme ⟶ Y.toScheme)
  [GenericPointPreserving π] (φ : C'.toScheme ⟶ C.toScheme) [IsIso φ]
  (hfac : C'.inclusion ≫ π = φ ≫ C.inclusion)
  (hφ : φ ≫ C.toSpec = C'.toSpec)

include hfac hφ in
/-- Effective-Cartier projection when the actual restriction of the surface
morphism is an isomorphism of prime curves over the base field. -/
theorem intersectionNumber_pullbackDivisor_eq_of_isoFactor
    (D : CartierDivisor Y.toScheme) (hD : HasRegularCartierEquations Y.toScheme D) :
    C'.intersectionNumber (pullbackDivisor π D hD) = C.intersectionNumber D := by
  rw [← C'.picardRestrictionDegreeHom_cartierPicardHom,
    cartierPicardHom_pullbackDivisor_eq,
    ← C.picardRestrictionDegreeHom_cartierPicardHom]
  change C'.picardRestrictionDegree
      (schemePicardPullbackHom π (cartierPicardClass Y.toScheme D)) =
    C.picardRestrictionDegree (cartierPicardClass Y.toScheme D)
  exact PrimeCurveTransportPullback.picardRestrictionDegree_eq_of_isoFactor
    C' C π φ hfac hφ (cartierPicardClass Y.toScheme D)

end Isomorphism

section Contracted

variable {Y : Scheme.{u}} [IsIntegral Y] (C : X.PrimeCurve)
  (π : X.toScheme ⟶ Y) [GenericPointPreserving π]

/-- Effective-Cartier pullbacks have degree zero when the actual prime-curve
inclusion followed by the morphism factors through the spectrum of a PID. -/
theorem intersectionNumber_pullbackDivisor_eq_zero_of_pidFactor
    {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (t : C.toScheme ⟶ Spec (CommRingCat.of R)) (c : Spec (CommRingCat.of R) ⟶ Y)
    (hfac : C.inclusion ≫ π = t ≫ c)
    (D : CartierDivisor Y) (hD : HasRegularCartierEquations Y D) :
    C.intersectionNumber (pullbackDivisor π D hD) = 0 := by
  rw [← C.picardRestrictionDegreeHom_cartierPicardHom,
    cartierPicardHom_pullbackDivisor_eq]
  exact PrimeCurveInclusionLift.picardRestrictionDegreeHom_pullback_eq_zero
    C C.inclusion C.range_inclusion.symm π t c hfac (cartierPicardHom Y D)

/-- The point-contraction case, with the point's field and both actual morphisms
displayed explicitly. -/
theorem intersectionNumber_pullbackDivisor_eq_zero_of_pointFactor
    {F : Type u} [Field F]
    (t : C.toScheme ⟶ Spec (CommRingCat.of F)) (c : Spec (CommRingCat.of F) ⟶ Y)
    (hfac : C.inclusion ≫ π = t ≫ c)
    (D : CartierDivisor Y) (hD : HasRegularCartierEquations Y D) :
    C.intersectionNumber (pullbackDivisor π D hD) = 0 :=
  intersectionNumber_pullbackDivisor_eq_zero_of_pidFactor C π t c hfac D hD

end Contracted

end KltDP.Geometry.PrimeCurveCartierProjectionCases
