import KltDP.Examples.FrobeniusBlowupCanonicalGlobalFactor
import KltDP.Geometry.SchemeInvertibleSheafPullback

/-!
# The actual canonical Picard formula for the original contact-plane blowup

The global differential factor identifies the pullback of the original
canonical line with the original exceptional ideal tensor the new canonical
line. Passing through the original sheaf-isomorphism quotient gives its
Picard formula. No canonical-class relation is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Examples.FrobeniusBlowupCanonicalPicard

open KltDP.Geometry KltDP.Geometry.AffineBlowup
open KltDP.Geometry.SmoothSurfaceKaehlerAtlas
open FrobeniusBlowupContact FrobeniusBlowupSmooth
open FrobeniusBlowupGlobalDifferentialCharts FrobeniusBlowupGlobalCanonicalTarget
open FrobeniusBlowupCanonicalGlobalFactor

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance moduleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
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

variable {k : Type u} [Field k]

/-- The original atlas canonical sheaves retain the isomorphism constructed from the differential. -/
def canonicalSheafBlowupIso :
    (schemeModulePullback (toSpec centerIdeal)).obj
        (canonicalSheafOfSmoothSurface (planeStructure (k := k))).obj ≅
      exceptionalIdealModule (centerIdeal (k := k)) ⊗
        (canonicalSheafOfSmoothSurface (blowupStructure (k := k))).obj :=
  (schemeModulePullback (toSpec centerIdeal)).mapIso
      (SmoothCanonicalExteriorComparison.canonicalSheafOfSmoothSurfaceIsoExterior
        (planeStructure (k := k))) ≪≫
    canonicalBlowupIso (k := k) ≪≫
      tensorIso (Iso.refl (exceptionalIdealModule centerIdeal))
        (canonicalIsoBlowupTop (k := k)).symm

/-- The original canonical classes satisfy the actual multiplicative Picard identity. -/
theorem canonicalSheafPicard_equation :
    schemePicardPullbackHom (toSpec centerIdeal)
        (canonicalSheafOfSmoothSurface (planeStructure (k := k))).toPic =
      (exceptionalIdealLine (centerIdeal (k := k))).toPic *
        (canonicalSheafOfSmoothSurface (blowupStructure (k := k))).toPic :=
  picard_pullback_tensor_of_iso (toSpec centerIdeal)
    (canonicalSheafOfSmoothSurface (planeStructure (k := k)))
    (exceptionalIdealLine centerIdeal)
    (canonicalSheafOfSmoothSurface (blowupStructure (k := k)))
    (canonicalSheafBlowupIso (k := k))

/-- The additive canonical formula, with the original exceptional ideal sign explicit. -/
theorem canonicalSheafPicard_formula :
    Additive.ofMul (canonicalSheafOfSmoothSurface (blowupStructure (k := k))).toPic =
      Additive.ofMul (schemePicardPullbackHom (toSpec centerIdeal)
        (canonicalSheafOfSmoothSurface (planeStructure (k := k))).toPic) -
        Additive.ofMul (exceptionalIdealLine (centerIdeal (k := k))).toPic := by
  have h := congrArg Additive.ofMul (canonicalSheafPicard_equation (k := k))
  change Additive.ofMul (schemePicardPullbackHom (toSpec centerIdeal)
      (canonicalSheafOfSmoothSurface (planeStructure (k := k))).toPic) =
    Additive.ofMul (exceptionalIdealLine (centerIdeal (k := k))).toPic +
      Additive.ofMul (canonicalSheafOfSmoothSurface (blowupStructure (k := k))).toPic at h
  apply (eq_sub_iff_add_eq).mpr
  simpa only [add_comm] using h.symm

end KltDP.Examples.FrobeniusBlowupCanonicalPicard
