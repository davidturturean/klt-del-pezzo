import KltDP.Examples.FrobeniusBlowupGlobalDifferentialCharts
import KltDP.Geometry.SmoothCanonicalExteriorComparison
import KltDP.Geometry.AffineBlowupExceptionalInvertible
import KltDP.Geometry.SchemeModuleStructureUnit
import KltDP.Geometry.InvertibleTensorExact

/-!
# The actual global target for the canonical point-blowup factorization

The original global exceptional kernel is tensored with the intrinsic
top-differential sheaf of the actual smooth blowup. Its map into that top
sheaf uses the original ideal inclusion and the original tensor unit.
Smoothness proves that this map is monic, as required by the accepted
open-cover factorization theorem. The local factors remain separate.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace KltDP.Examples.FrobeniusBlowupGlobalCanonicalTarget

open KltDP.Geometry KltDP.Geometry.AffineBlowup
open FrobeniusBlowupContact FrobeniusBlowupSmooth FrobeniusBlowupGlobalDifferentialCharts

local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

private theorem tensorUnitInclusion_mono {X : Scheme.{u}} {I : X.Modules}
    (i : I ⟶ _root_.SheafOfModules.unit X.ringCatSheaf) [Mono i]
    (L : InvertibleSheaf X) :
    Mono (((i ≫ (SchemeModuleStructureUnit.iso X).hom) ▷ L.obj) ≫ (λ_ L.obj).hom) := by
  letI := L.tensorRight_preservesFiniteLimits
  haveI : Mono (i ≫ (SchemeModuleStructureUnit.iso X).hom) := inferInstance
  change Mono ((tensorRight L.obj).map (i ≫ (SchemeModuleStructureUnit.iso X).hom) ≫
    (λ_ L.obj).hom)
  infer_instance

variable {k : Type u} [Field k]

/-- Smoothness of the original blowup proves invertibility of its intrinsic top sheaf. -/
def blowupTopLine : InvertibleSheaf (scheme (centerIdeal (k := k))) :=
  ⟨blowupTop (k := k),
    SmoothCanonicalExteriorComparison.relativeDifferentialExterior_isInvertible
      (blowupStructure (k := k))⟩

/-- The existing canonical line is identified with this same intrinsic global top sheaf. -/
def canonicalIsoBlowupTop :
    (SmoothSurfaceKaehlerAtlas.canonicalSheafOfSmoothSurface
      (blowupStructure (k := k))).obj ≅ blowupTop (k := k) :=
  SmoothCanonicalExteriorComparison.canonicalSheafOfSmoothSurfaceIsoExterior
    (blowupStructure (k := k))

/-- The original global ideal inclusion, with the same original unit comparison as on the charts. -/
def exceptionalInclusionToUnit :
    exceptionalIdealModule (centerIdeal (k := k)) ⟶
      𝟙_ (scheme (centerIdeal (k := k))).Modules :=
  schemeKernelIdealι (exceptionalι (centerIdeal (k := k))) ≫
    (SchemeModuleStructureUnit.iso (scheme (centerIdeal (k := k)))).hom

/-- The original global ideal tensor, the required target of the canonical factor. -/
abbrev exceptionalCanonicalTensor : (scheme (centerIdeal (k := k))).Modules :=
  exceptionalIdealModule (centerIdeal (k := k)) ⊗ blowupTop (k := k)

/-- Tensor the actual kernel inclusion with the actual intrinsic top sheaf. -/
def exceptionalCanonicalInclusion :
    exceptionalCanonicalTensor (k := k) ⟶ blowupTop (k := k) :=
  (exceptionalInclusionToUnit (k := k) ▷ blowupTop (k := k)) ≫
    (λ_ (blowupTop (k := k))).hom

/-- The actual global target map is monic; no local factorization premise is used. -/
theorem exceptionalCanonicalInclusion_mono : Mono (exceptionalCanonicalInclusion (k := k)) := by
  letI : Mono (schemeKernelIdealι (exceptionalι (centerIdeal (k := k)))) := by
    unfold schemeKernelIdealι
    infer_instance
  exact tensorUnitInclusion_mono (schemeKernelIdealι (exceptionalι (centerIdeal (k := k))))
    (blowupTopLine (k := k))

end KltDP.Examples.FrobeniusBlowupGlobalCanonicalTarget
