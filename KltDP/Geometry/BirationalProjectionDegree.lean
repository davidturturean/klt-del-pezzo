import KltDP.Geometry.BirationalPrimeCurveProjectionDegreeConditional
import KltDP.Literature.ProperCurvePullbackDegreeLiteral

/-!
# Original birational projection degree using the reviewed whole source

These ordinary consumers discharge the full explicit source hypothesis
with the separately reviewed Stacks 0AYZ literal. All surface and curve
maps, line sheaves, Picard classes and degree expressions are unchanged.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.BirationalProjectionDegree

open BirationalPrimeCorrespondence

variable {k : Type u} [Field k] {S X : NormalProjectiveSurface k}
  (π : S.toScheme ⟶ X.toScheme) [IsProper π]
  (hπ : π ≫ X.structureMorphism = S.structureMorphism) (hbir : IsBirationalScheme π)

include hπ

theorem restrictionDegree_pullback (C : X.PrimeCurve) (L : InvertibleSheaf X.toScheme) :
    (abovePrimeCurve π hbir C).restrictionDegree (pullbackInvertibleSheaf π L) =
      C.restrictionDegree L :=
  BirationalPrimeCurveProjectionDegree.restrictionDegree_pullback
    KltDP.Literature.Stacks.proper_curve_pullback_degree_literal π hπ hbir C L

theorem picardRestrictionDegree_pullback (C : X.PrimeCurve) (p : X.toScheme.Pic) :
    (abovePrimeCurve π hbir C).picardRestrictionDegree (schemePicardPullbackHom π p) =
      C.picardRestrictionDegree p :=
  BirationalPrimeCurveProjectionDegree.picardRestrictionDegree_pullback
    KltDP.Literature.Stacks.proper_curve_pullback_degree_literal π hπ hbir C p

end KltDP.Geometry.BirationalProjectionDegree

#check @KltDP.Geometry.BirationalProjectionDegree.restrictionDegree_pullback
#print axioms KltDP.Geometry.BirationalProjectionDegree.restrictionDegree_pullback
