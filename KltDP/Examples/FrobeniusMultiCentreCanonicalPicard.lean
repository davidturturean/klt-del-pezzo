import KltDP.Examples.FrobeniusMultiCentreCanonicalGlobalFactor
import KltDP.Examples.FrobeniusMultiCentreCanonicalIdealClass

/-!
# The original finite-centre canonical Picard formula

The normalized global differential factor identifies the actual atlas
canonical sheaves. Its ideal tensor has the accepted original total
exceptional double-sum class. Passing through the actual Picard quotient
gives the whole-surface formula, without assuming injectivity of local
Picard restriction or supplying a canonical class relation.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreCanonicalPicard

open KltDP.Geometry KltDP.Geometry.SmoothSurfaceKaehlerAtlas
open FrobeniusGlobalBlowupStages FrobeniusMultiCentreSurface
open FrobeniusMultiCentreCanonicalOpenComparison FrobeniusContactTowerCanonicalIteration
open FrobeniusMultiCentreCanonicalIdealFamily FrobeniusMultiCentreCanonicalIdealClass
open FrobeniusMultiCentreCanonicalGlobalFactor

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance multiCanonicalPicardModules (X : Scheme.{u}) : MonoidalCategory X.Modules :=
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

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The original global factor identifies the actual atlas canonical line sheaves. -/
def multiCanonicalSheafIso (q n : ℕ) (a : Fin n → k) (ha : Function.Injective a) :
    (schemeModulePullback (multiProjection (q + 1) n a)).obj
        (canonicalSheafOfSmoothSurface (projectiveProductInitial (k := k)).structureMap).obj ≅
      (multiIdealLine (q + 1) n a).obj ⊗ (multiCanonicalLine (q + 1) n a ha).obj := by
  letI := multiStructure_smoothTwo (q + 1) n a ha
  exact (schemeModulePullback (multiProjection (q + 1) n a)).mapIso
      (SmoothCanonicalExteriorComparison.canonicalSheafOfSmoothSurfaceIsoExterior
        (projectiveProductInitial (k := k)).structureMap) ≪≫
    multiCanonicalFactorIso q n a ha ≪≫
    tensorIso (Iso.refl (multiIdealLine (q + 1) n a).obj)
      (SmoothCanonicalExteriorComparison.canonicalSheafOfSmoothSurfaceIsoExterior
        (multiStructure (q + 1) n a)).symm

/-- The actual canonical sheaves satisfy the original multiplicative Picard equation. -/
theorem multiCanonicalPicard_equation (q n : ℕ) (a : Fin n → k) (ha : Function.Injective a) :
    schemePicardPullbackHom (multiProjection (q + 1) n a)
        (canonicalSheafOfSmoothSurface (projectiveProductInitial (k := k)).structureMap).toPic =
      (multiIdealLine (q + 1) n a).toPic * (multiCanonicalLine (q + 1) n a ha).toPic :=
  picard_pullback_tensor_of_iso (multiProjection (q + 1) n a)
    (canonicalSheafOfSmoothSurface (projectiveProductInitial (k := k)).structureMap)
    (multiIdealLine (q + 1) n a) (multiCanonicalLine (q + 1) n a ha)
    (multiCanonicalSheafIso q n a ha)

/-- The actual global finite-centre canonical class is the pulled original base class
plus the full accepted original total-exceptional sum. -/
theorem multiCanonicalClass_formula (q n : ℕ) (a : Fin n → k) (ha : Function.Injective a) :
    multiCanonicalClass (q + 1) n a ha =
      (schemePicardPullbackHom (multiProjection (q + 1) n a)).toAdditive
        (originalCanonicalClass (k := k) 0) +
        ∑ i : Fin n, ∑ j : Fin (q + 1), exceptionalClass (q + 1) n a i j := by
  have h := congrArg Additive.ofMul (multiCanonicalPicard_equation q n a ha)
  change (schemePicardPullbackHom (multiProjection (q + 1) n a)).toAdditive
      (originalCanonicalClass (k := k) 0) =
    Additive.ofMul (multiIdealLine (q + 1) n a).toPic + multiCanonicalClass (q + 1) n a ha at h
  have hs : multiCanonicalClass (q + 1) n a ha =
      (schemePicardPullbackHom (multiProjection (q + 1) n a)).toAdditive
        (originalCanonicalClass (k := k) 0) - Additive.ofMul (multiIdealLine (q + 1) n a).toPic := by
    apply (eq_sub_iff_add_eq).mpr
    simpa only [add_comm] using h.symm
  rw [sub_eq_add_neg, multiIdealClass] at hs
  exact hs

end KltDP.Examples.FrobeniusMultiCentreCanonicalPicard
