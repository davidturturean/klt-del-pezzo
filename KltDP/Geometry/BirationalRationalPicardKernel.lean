import KltDP.Geometry.BirationalRationalClassKernel
import KltDP.Geometry.NumericalEquivalence
import KltDP.Geometry.RationalPicardIntersection
import KltDP.Geometry.ExceptionalNegativeDefinite

/-!
# Exact exceptional kernel on the original rational Picard group

The regular-source Picard/Weil equivalence transports the actual rational
Weil pushforward. Its kernel is the span of the original exceptional
Cartier classes. The codomain remains the actual target rational Weil
class group: replacing it by the target Cartier numerical quotient would
require a separate descent theorem.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.BirationalRationalPicard

open BirationalWeilPushforward BirationalPrimeCorrespondence

variable {k : Type u} [Field k] {S X : NormalProjectiveSurface k}
  (π : S.toScheme ⟶ X.toScheme) [IsProper π] (hbir : IsBirationalScheme π)

/-- The original rational Weil pushforward descends through the original
principal submodules. -/
def classPushforward : S.RationalWeilClassGroup →ₗ[ℚ] X.RationalWeilClassGroup :=
  S.rationalPrincipalSubmodule.liftQ
    (X.rationalWeilClassMap.comp (rationalPushforward π hbir)) (by
      rw [rationalClassPushforward_ker π hbir]
      exact le_sup_left)

@[simp]
theorem classPushforward_class (D : S.RationalWeilDivisor) :
    classPushforward π hbir (S.rationalWeilClassMap D) =
      X.rationalWeilClassMap (rationalPushforward π hbir D) := rfl

/-- The original prime correspondence supplies every target rational class. -/
theorem classPushforward_surjective : Function.Surjective (classPushforward π hbir) := by
  intro c
  obtain ⟨D, rfl⟩ := X.rationalPrincipalSubmodule.mkQ_surjective c
  let E : S.RationalWeilDivisor := Finsupp.embDomain
    ⟨abovePrimeCurve π hbir, abovePrimeCurve_injective π hbir⟩ D
  refine ⟨S.rationalWeilClassMap E, ?_⟩
  rw [classPushforward_class]
  apply congrArg X.rationalWeilClassMap
  apply Finsupp.ext
  intro C
  exact Finsupp.embDomain_apply _ D C

/-- The exact kernel before the regular-source Picard identification. -/
theorem classPushforward_ker :
    LinearMap.ker (classPushforward π hbir) =
      (Finsupp.supported ℚ ℚ {C : S.PrimeCurve | IsExceptionalCurve π C}).map
        S.rationalWeilClassMap := by
  rw [classPushforward, Submodule.ker_liftQ, rationalClassPushforward_ker π hbir,
    Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq]
  rfl

variable [IsAlgClosed k] (hregular : ∀ x : S.Point, RegularPoint S.toScheme x)

/-- Pushforward on the original rationalized sheaf Picard group of the
regular source, retaining the original target Weil-class codomain. -/
def picardPushforward : S.RationalPicard →ₗ[ℚ] X.RationalWeilClassGroup :=
  (classPushforward π hbir).comp (S.regularPicardTensorRationalEquiv hregular).toLinearMap

/-- This map has the literal original divisor formula. -/
theorem picardPushforward_divisor (D : S.RationalWeilDivisor) :
    picardPushforward π hbir hregular (S.rationalWeilToRationalPicard hregular D) =
      X.rationalWeilClassMap (rationalPushforward π hbir D) := by
  change classPushforward π hbir ((S.regularPicardTensorRationalEquiv hregular)
    ((S.regularPicardTensorRationalEquiv hregular).symm (S.rationalWeilClassMap D))) = _
  rw [LinearEquiv.apply_symm_apply, classPushforward_class]

theorem picardPushforward_surjective :
    Function.Surjective (picardPushforward π hbir hregular) :=
  (classPushforward_surjective π hbir).comp
    (S.regularPicardTensorRationalEquiv hregular).surjective

omit π hbir in
/-- A prime singleton gives the original Cartier prime-curve Picard class. -/
theorem rationalWeilToRationalPicard_single (C : S.PrimeCurve) :
    S.rationalWeilToRationalPicard hregular (Finsupp.single C 1) =
      S.primeCurveRationalPicardClass hregular C := by
  have h := S.rationalWeilToRationalPicard_rationalize hregular
    (S.cartierToWeilHom (S.primeCurveCartier hregular C))
  have heq : S.regularWeilPicardClass hregular
      (S.cartierToWeilHom (S.primeCurveCartier hregular C)) =
        cartierPicardClass S.toScheme (S.primeCurveCartier hregular C) :=
    S.regularWeilClassPicardEquiv_of_cartier hregular _
  rw [heq, S.cartierToWeilHom_primeCurveCartier,
    NormalProjectiveSurface.rationalizeWeilDivisor_single, Int.cast_one] at h
  exact h

omit hbir in
/-- The supported-divisor submodule maps to exactly the actual exceptional
Picard span, with the original prime Cartier representatives. -/
theorem map_supported_eq_exceptional_span :
    (Finsupp.supported ℚ ℚ {C : S.PrimeCurve | IsExceptionalCurve π C}).map
        (S.rationalWeilToRationalPicard hregular) =
      Submodule.span ℚ (NormalProjectiveSurface.exceptionalClasses π hregular) := by
  rw [Finsupp.supported_eq_span_single, Submodule.map_span, Set.image_image]
  congr 1
  ext c
  constructor
  · rintro ⟨C, hC, rfl⟩
    exact ⟨C, hC, rationalWeilToRationalPicard_single hregular C⟩
  · rintro ⟨C, hC, rfl⟩
    exact ⟨C, hC, rationalWeilToRationalPicard_single hregular C⟩

/-- The exact kernel is the span of the original contracted prime classes;
there is no supplied support, independence, or descent hypothesis. -/
theorem picardPushforward_ker :
    LinearMap.ker (picardPushforward π hbir hregular) =
      Submodule.span ℚ (NormalProjectiveSurface.exceptionalClasses π hregular) := by
  rw [picardPushforward, LinearMap.ker_comp, classPushforward_ker π hbir,
    Submodule.comap_equiv_eq_map_symm, ← Submodule.map_comp]
  change (Finsupp.supported ℚ ℚ {C : S.PrimeCurve | IsExceptionalCurve π C}).map
      (S.rationalWeilToRationalPicard hregular) = _
  exact map_supported_eq_exceptional_span π hregular

end KltDP.Geometry.BirationalRationalPicard

#check @KltDP.Geometry.BirationalRationalPicard.picardPushforward_divisor
#check @KltDP.Geometry.BirationalRationalPicard.picardPushforward_surjective
#check @KltDP.Geometry.BirationalRationalPicard.picardPushforward_ker
#print axioms KltDP.Geometry.BirationalRationalPicard.picardPushforward_ker
