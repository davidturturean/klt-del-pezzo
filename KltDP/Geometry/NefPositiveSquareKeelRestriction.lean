import KltDP.Geometry.KeelSurfaceExceptionalComparison
import KltDP.Geometry.NefCompleteSystemBirational
import KltDP.Geometry.TrivialInvertibleSheafSemiample
import KltDP.Literature.KeelCompleteSystem

/-!
# Keel's actual restriction for a nef positive-square line on a smooth surface

The independently proved comparison identifies the two actual reduced loci.
A unit frame on the original null-locus restriction transfers through that
comparison and discharges exactly Keel's published restriction condition.
This is a reusable intermediate adapter; the exceptional-forest application
must construct its own frame separately.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.NefPositiveSquareKeelRestriction

variable {k : Type u} [Field k] [IsAlgClosed k]
  (S : NormalProjectiveSurface k)
  [IsSmoothOfRelativeDimension 2 S.structureMorphism]

local instance source_isSmooth : IsSmooth S.structureMorphism :=
  IsSmoothOfRelativeDimension.isSmooth 2 S.structureMorphism

local instance original_proper : IsProper S.structureMorphism := S.projective.isProper

/-- Positive square and nefness already produce the literal eventual
complete-system birationality on the original source. -/
theorem eventuallyBirational (L : InvertibleSheaf S.toScheme)
    (hnef : Positivity.IsNef S.structureMorphism L)
    (hpositive : 0 < S.selfIntersection S.regularPoints_of_isSmooth L) :
    KeelCompleteSystem.EventuallyBirational S.structureMorphism L :=
  NefCompleteSystemBirational.eventually_toImage_isBirationalScheme S L hnef hpositive

/-- Transfer a frame on the original null restriction to the actual reduced
exceptional restriction used in Keel's full theorem. -/
def exceptionalRestrictionUnitIso (L : InvertibleSheaf S.toScheme)
    (hnef : Positivity.IsNef S.structureMorphism L)
    (hpositive : 0 < S.selfIntersection S.regularPoints_of_isSmooth L)
    (e : (Positivity.nullLocusRestrict S.structureMorphism L).obj ≅
      _root_.SheafOfModules.unit
        (Positivity.nullLocusScheme S.structureMorphism L).ringCatSheaf) :
    (KeelCompleteSystem.exceptionalRestrict S.structureMorphism L).obj ≅
      _root_.SheafOfModules.unit
        (KeelCompleteSystem.exceptionalScheme S.structureMorphism L).ringCatSheaf := by
  let h := KeelSurfaceExceptionalComparison.exceptionalSupport_eq_nullLocus
    S S.regularPoints_of_isSmooth (SmoothCanonicalCartierRepresentative.weilRepresentative S)
    (SurfaceRiemannRochSource.constructedCanonical_isCanonical S) L hnef hpositive
  let j := (KeelCompleteSystem.exceptionalSchemeIso S.structureMorphism L h).hom
  exact (KeelCompleteSystem.exceptionalRestrictIso S.structureMorphism L h).symm ≪≫
    (schemeModulePullback j).mapIso e ≪≫ schemeModulePullbackUnitIso j

/-- The same original line is semiample after its original null restriction
has an actual unit frame. Positive characteristic is retained literally. -/
theorem isSemiample_of_nullRestriction_unitIso (p : ℕ) [CharP k p] (hp : 0 < p)
    (L : InvertibleSheaf S.toScheme) (hnef : Positivity.IsNef S.structureMorphism L)
    (hpositive : 0 < S.selfIntersection S.regularPoints_of_isSmooth L)
    (e : (Positivity.nullLocusRestrict S.structureMorphism L).obj ≅
      _root_.SheafOfModules.unit
        (Positivity.nullLocusScheme S.structureMorphism L).ringCatSheaf) :
    Positivity.IsSemiample L := by
  apply (KltDP.Literature.Keel.semiampleness_completeSystem_literal
    p hp S.toScheme S.structureMorphism S.projective L hnef).mpr
  exact Positivity.isSemiample_of_unitIso _
    (exceptionalRestrictionUnitIso S L hnef hpositive e)

end KltDP.Geometry.NefPositiveSquareKeelRestriction

#print axioms KltDP.Geometry.NefPositiveSquareKeelRestriction.eventuallyBirational
#print axioms KltDP.Geometry.NefPositiveSquareKeelRestriction.isSemiample_of_nullRestriction_unitIso
