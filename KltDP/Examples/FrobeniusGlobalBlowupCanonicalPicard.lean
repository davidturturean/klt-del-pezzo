import KltDP.Examples.FrobeniusGlobalBlowupCanonicalGlobalFactor
import KltDP.Geometry.SchemeInvertibleSheafPullback

/-!
# The original canonical Picard formula on the whole next blowup stage

The actual global differential factor identifies the original atlas
canonical sheaves. Passing through the original sheaf-isomorphism quotient
therefore gives the canonical Picard formula with the actual entire
exceptional ideal, without an assumed class relation.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Examples.FrobeniusGlobalBlowupCanonicalPicard

open KltDP.Geometry KltDP.Geometry.SmoothSurfaceKaehlerAtlas
open FrobeniusGlobalBlowupStages FrobeniusGlobalBlowupDifferentialAffine
open FrobeniusGlobalBlowupCanonicalTarget FrobeniusGlobalBlowupCanonicalGlobalFactor

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance wholePicardModules (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

private theorem picard_pullback_tensor_of_iso {X Y : Scheme.{u}} (f : Y ⟶ X)
    (L : InvertibleSheaf X) (I K : InvertibleSheaf Y)
    (e : (schemeModulePullback f).obj L.obj ≅ I.obj ⊗ K.obj) :
    schemePicardPullbackHom f L.toPic = I.toPic * K.toPic := by
  rw [schemePicardPullbackHom_toPic]
  apply Units.ext
  change ((pullbackInvertibleSheaf f L).toPic : Skeleton Y.Modules) =
    (I.toPic : Skeleton Y.Modules) * (K.toPic : Skeleton Y.Modules)
  rw [InvertibleSheaf.toPic_val, InvertibleSheaf.toPic_val,
    InvertibleSheaf.toPic_val, ← Skeleton.toSkeleton_tensorObj]
  exact Quotient.sound ⟨e⟩

variable {k : Type u} [Field k] (A : PlaneChartedScheme k)
    [IsSmoothOfRelativeDimension 2 A.structureMap]

/-- The actual original atlas canonical sheaves, through the proved original differential factor. -/
def canonicalSheafBlowupIso :
    (schemeModulePullback A.nextProjection).obj (canonicalSheafOfSmoothSurface A.structureMap).obj ≅
      wholeExceptionalIdeal A ⊗ (canonicalSheafOfSmoothSurface A.nextStructure).obj :=
  (schemeModulePullback A.nextProjection).mapIso
      (SmoothCanonicalExteriorComparison.canonicalSheafOfSmoothSurfaceIsoExterior A.structureMap) ≪≫
    wholeCanonicalBlowupIso A ≪≫ tensorIso (Iso.refl (wholeExceptionalIdeal A))
      (SmoothCanonicalExteriorComparison.canonicalSheafOfSmoothSurfaceIsoExterior A.nextStructure).symm

/-- The actual whole-stage canonical classes satisfy the original multiplicative Picard identity. -/
theorem canonicalSheafPicard_equation :
    schemePicardPullbackHom A.nextProjection (canonicalSheafOfSmoothSurface A.structureMap).toPic =
      (wholeExceptionalIdealLine A).toPic * (canonicalSheafOfSmoothSurface A.nextStructure).toPic :=
  picard_pullback_tensor_of_iso A.nextProjection (canonicalSheafOfSmoothSurface A.structureMap)
    (wholeExceptionalIdealLine A) (canonicalSheafOfSmoothSurface A.nextStructure)
    (canonicalSheafBlowupIso A)

/-- The canonical formula in the original whole-stage Picard group, with the actual ideal sign. -/
theorem canonicalSheafPicard_formula :
    Additive.ofMul (canonicalSheafOfSmoothSurface A.nextStructure).toPic =
      Additive.ofMul (schemePicardPullbackHom A.nextProjection
        (canonicalSheafOfSmoothSurface A.structureMap).toPic) -
        Additive.ofMul (wholeExceptionalIdealLine A).toPic := by
  have h := congrArg Additive.ofMul (canonicalSheafPicard_equation A)
  change Additive.ofMul (schemePicardPullbackHom A.nextProjection
      (canonicalSheafOfSmoothSurface A.structureMap).toPic) =
    Additive.ofMul (wholeExceptionalIdealLine A).toPic +
      Additive.ofMul (canonicalSheafOfSmoothSurface A.nextStructure).toPic at h
  apply (eq_sub_iff_add_eq).mpr
  simpa only [add_comm] using h.symm

end KltDP.Examples.FrobeniusGlobalBlowupCanonicalPicard
