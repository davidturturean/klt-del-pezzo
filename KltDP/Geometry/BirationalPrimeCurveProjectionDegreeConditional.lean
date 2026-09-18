import KltDP.Geometry.BirationalPrimeCurveRestriction
import KltDP.Geometry.ProperBirationalCurvePullbackDegreeConditional
import KltDP.Geometry.PrimeCurveTransportPullback
import KltDP.Geometry.NumericalEquivalence

/-!
# Conditional projection degree for the original corresponding prime curves

The full every-rank Stacks 0AYZ hypothesis is retained verbatim. Its proved
birational consumer applies to the actual constructed curve restriction.
The original inclusion square then identifies the restriction degree of
an original pulled-back surface line with its target restriction degree.
No smoothness of either curve or isomorphism of whole curves is assumed.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open KltDP.Geometry.ModuleCohomology
universe u

namespace KltDP.Geometry.BirationalPrimeCurveProjectionDegree

open BirationalPrimeCorrespondence BirationalPrimeCurveMap

variable
    (hsource : ∀ {k : Type u} [instField : Field k]
      {C D : Scheme.{u}} [instIntegralC : IsIntegral C] [instIntegralD : IsIntegral D]
      (σC : C ⟶ Spec (CommRingCat.of k)) [instProperC : IsProper σC]
      (σD : D ⟶ Spec (CommRingCat.of k)) [instProperD : IsProper σD]
      (hdimC : topologicalKrullDim C = 1) (hdimD : topologicalKrullDim D = 1)
      (f : C ⟶ D) (hf : f ≫ σD = σC)
      (hnonconstant : ¬ ∃ y : D, ∀ x : C, f.base x = y)
      (E : D.Modules) (n : ℕ) (hE : IsLocallyFreeOfRankOn D E n),
      letI : IsNoetherian D := isNoetherian_of_finiteType_toSpec σD
      letI : GenericPointPreserving f :=
        ProperNonconstantCurve.genericPointPreserving_of_nonconstant_base
          f hdimD.le hnonconstant
      letI : Algebra D.functionField C.functionField :=
        (functionFieldMap f).hom.toAlgebra
      eulerCharacteristic σC ((schemeModulePullback f).obj E) -
          (n : ℤ) * eulerCharacteristic σC (_root_.SheafOfModules.unit C.ringCatSheaf) =
        (Module.finrank D.functionField C.functionField : ℤ) *
          (eulerCharacteristic σD E -
            (n : ℤ) * eulerCharacteristic σD (_root_.SheafOfModules.unit D.ringCatSheaf)))

variable {k : Type u} [Field k] {S X : NormalProjectiveSurface k}
  (π : S.toScheme ⟶ X.toScheme) [IsProper π]
  (hπ : π ≫ X.structureMorphism = S.structureMorphism) (hbir : IsBirationalScheme π)

include hsource hπ

/-- Birational degree invariance on the actual original curve restriction. -/
theorem lineDegree_restriction_pullback (C : X.PrimeCurve) (L : InvertibleSheaf C.toScheme) :
    (abovePrimeCurve π hbir C).lineDegree
        (pullbackInvertibleSheaf (restriction π hbir C) L) = C.lineDegree L := by
  letI : IsProper (abovePrimeCurve π hbir C).toSpec :=
    (abovePrimeCurve π hbir C).toSpec_isProper
  letI : IsProper C.toSpec := C.toSpec_isProper
  have h := ProperBirationalCurveDegree.eulerDifference_pullback_of_birational hsource
    (abovePrimeCurve π hbir C).toSpec C.toSpec
    (abovePrimeCurve π hbir C).dimension_one_toScheme C.dimension_one_toScheme
    (restriction π hbir C) (restriction_toSpec π hbir C hπ)
    (restriction_isBirationalScheme π hbir C) L.obj 1 (by infer_instance)
  simpa only [Nat.cast_one, one_mul] using h

/-- The original line bundle has the same degree on the actual corresponding prime. -/
theorem restrictionDegree_pullback (C : X.PrimeCurve) (L : InvertibleSheaf X.toScheme) :
    (abovePrimeCurve π hbir C).restrictionDegree (pullbackInvertibleSheaf π L) =
      C.restrictionDegree L := by
  rw [(abovePrimeCurve π hbir C).restrictionDegree_pullback,
    ← restriction_inclusion π hbir C,
    ← (abovePrimeCurve π hbir C).lineDegree_pullback_comp]
  exact lineDegree_restriction_pullback hsource π hπ hbir C
    (pullbackInvertibleSheaf C.inclusion L)

/-- The same original projection-degree equality on actual sheaf Picard classes. -/
theorem picardRestrictionDegree_pullback (C : X.PrimeCurve) (p : X.toScheme.Pic) :
    (abovePrimeCurve π hbir C).picardRestrictionDegree (schemePicardPullbackHom π p) =
      C.picardRestrictionDegree p := by
  obtain ⟨L, rfl⟩ := RationalTreePicard.toPic_surjective p
  rw [schemePicardPullbackHom_toPic,
    NormalProjectiveSurface.PrimeCurve.picardRestrictionDegree_toPic,
    NormalProjectiveSurface.PrimeCurve.picardRestrictionDegree_toPic]
  exact restrictionDegree_pullback hsource π hπ hbir C L

include hbir in
/-- Numerical triviality of the original pulled-back class detects
numerical triviality of the original target class. This uses all actual
primes above target primes, without any descent or rank equality input. -/
theorem numericallyTrivial_of_pullback (p : X.toScheme.Pic)
    (h : S.NumericallyTrivial (schemePicardPullbackHom π p)) : X.NumericallyTrivial p := by
  intro C
  rw [← picardRestrictionDegree_pullback hsource π hπ hbir C p]
  exact h (abovePrimeCurve π hbir C)

end KltDP.Geometry.BirationalPrimeCurveProjectionDegree

#check @KltDP.Geometry.BirationalPrimeCurveProjectionDegree.restrictionDegree_pullback
#check @KltDP.Geometry.BirationalPrimeCurveProjectionDegree.numericallyTrivial_of_pullback
#print axioms KltDP.Geometry.BirationalPrimeCurveProjectionDegree.restrictionDegree_pullback
#print axioms KltDP.Geometry.BirationalPrimeCurveProjectionDegree.numericallyTrivial_of_pullback
