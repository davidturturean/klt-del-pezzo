import KltDP.Geometry.QuadraticCanonicalFrameCover
import KltDP.Geometry.QuadraticOriginalUnitCanonicalChart
import KltDP.Geometry.SchemeModuleMonicFactorOnCharts
import KltDP.Geometry.SmoothCanonicalExteriorComparison
import KltDP.Geometry.InvertibleTensorExact

/-!
# The actual global normalized quadratic Hurwitz factor

The original geometric hypotheses produce a covering family of original
branch or unit coefficient charts. The local normalized factors glue by
monicity of the original ramification ideal tensored with the actual top
differential line. The resulting global isomorphism preserves the whole
original differential map; neither local frames nor a factorization are
hypotheses of the global theorem.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory
universe u

namespace KltDP.Geometry.QuadraticCoverAtlas.Data

open TransitionUnitGluing SchemeTopDifferentialFactorSquare

local instance originalCanonicalModules (Y : Scheme.{u}) : MonoidalCategory Y.Modules :=
  Scheme.Modules.monoidalCategory Y

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] {ι : Type u}
  (D : QuadraticCoverAtlas.Data X ι) (f : X ⟶ Spec (CommRingCat.of k))
  (h2 : IsUnit (2 : Γ(X, ⊤)))

/-- Every produced actual frame carries its actual normalized global-sheaf factor. -/
def canonicalFrameFactor (c : D.CanonicalFrameChart f) :
    {e : (schemeModulePullback (D.frameGlobalι c.le)).obj
        ((schemeModulePullback D.morphism).obj (top f 2)) ≅
      (schemeModulePullback (D.frameGlobalι c.le)).obj
        (schemeKernelIdeal D.rootZeroGlobalι ⊗ top (D.morphism ≫ f) 2) //
      e.hom ≫ (schemeModulePullback (D.frameGlobalι c.le)).map
        (schemeStructureTensorInclusion (schemeKernelIdealι D.rootZeroGlobalι)
          (top (D.morphism ≫ f) 2)) =
      (schemeModulePullback (D.frameGlobalι c.le)).map
        (SchemeKaehlerExteriorPullbackTransport.map f D.morphism (D.morphism ≫ f) rfl 2)} := by
  classical
  letI : Nonempty c.U.1 := ⟨⟨c.nonempty.choose, c.nonempty.choose_spec⟩⟩
  letI : IsDomain Γ(X, c.U.1) := IsIntegral.component_integral c.U.1
  letI : Algebra k Γ(X, c.U.1) := GluedChartKaehlerPullback.chartAlgebra f c.U
  letI : Algebra.IsStandardSmoothOfRelativeDimension 2 k Γ(X, c.U.1) := c.smooth
  have h2U : IsUnit (2 : Γ(X, c.U.1)) := by
    simpa only [map_ofNat] using h2.map (res X (le_top : c.U.1 ≤ ⊤))
  by_cases hu : IsUnit (res X c.le (D.sections c.index))
  · exact ⟨D.originalUnitCanonicalChartFactor f c.U c.le h2U hu c.basis,
      D.originalUnitCanonicalChartFactor_comp f c.U c.le h2U hu c.basis⟩
  · have hb := c.unit_or_branch.resolve_left hu
    exact ⟨D.originalBranchCanonicalChartFactor f c.U c.le c.regular h2U c.basis hb,
      D.originalBranchCanonicalChartFactor_comp f c.U c.le c.regular h2U c.basis hb⟩

variable [IsSmoothOfRelativeDimension 2 (D.morphism ≫ f)]

/-- Tensoring the original ideal inclusion with the actual top-differential line is monic. -/
theorem originalCanonicalTensorInclusion_mono :
    Mono (schemeStructureTensorInclusion (schemeKernelIdealι D.rootZeroGlobalι)
      (top (D.morphism ≫ f) 2)) := by
  let L : InvertibleSheaf D.scheme := ⟨top (D.morphism ≫ f) 2,
    SmoothCanonicalExteriorComparison.relativeDifferentialExterior_isInvertible (D.morphism ≫ f)⟩
  letI := L.tensorRight_preservesFiniteLimits
  haveI : Mono (schemeKernelIdealι D.rootZeroGlobalι) := by
    unfold schemeKernelIdealι
    infer_instance
  haveI : Mono (schemeKernelIdealι D.rootZeroGlobalι ≫
      (SchemeModuleStructureUnit.iso D.scheme).hom) := inferInstance
  change Mono ((tensorRight L.obj).map (schemeKernelIdealι D.rootZeroGlobalι ≫
    (SchemeModuleStructureUnit.iso D.scheme).hom) ≫ (λ_ L.obj).hom)
  infer_instance

variable (I : X.IdealSheafData) (hI : IdealLocallyPrincipalRegular I)
  [IsSmoothOfRelativeDimension 2 f] [IsSmoothOfRelativeDimension 1 (I.gluedTo ≫ f)]
  (hmatch : ∀ i, I.ideal ⟨D.opens i, D.affine i⟩ = Ideal.span {D.sections i})
  (hregular : ∀ i, (D.opens i : Set X).Nonempty →
    D.sections i ∈ nonZeroDivisors Γ(X, D.opens i))

/-- The actual pulled base canonical sheaf is the actual ramification ideal
tensored with the actual cover canonical sheaf. All local factors are produced internally. -/
def originalCanonicalFactor :
    (schemeModulePullback D.morphism).obj (top f 2) ≅
      schemeKernelIdeal D.rootZeroGlobalι ⊗ top (D.morphism ≫ f) 2 := by
  letI (c : D.CanonicalFrameChart f) : IsOpenImmersion (D.frameGlobalι c.le) :=
    D.frameGlobalι_isOpenImmersion c.le c.U.2
  letI := D.originalCanonicalTensorInclusion_mono f
  exact schemeModuleMonicFactorIsoOnOpenCharts
    (fun c : D.CanonicalFrameChart f => D.frameChart c.le)
    (fun c => D.frameGlobalι c.le) (D.canonicalFrameCharts_cover f I hI hmatch hregular)
    (schemeStructureTensorInclusion (schemeKernelIdealι D.rootZeroGlobalι) (top (D.morphism ≫ f) 2))
    (SchemeKaehlerExteriorPullbackTransport.map f D.morphism (D.morphism ≫ f) rfl 2)
    (fun c => (D.canonicalFrameFactor f h2 c).val)
    (fun c => (D.canonicalFrameFactor f h2 c).property)

/-- The global isomorphism factors the same original whole differential map. -/
theorem originalCanonicalFactor_comp :
    (D.originalCanonicalFactor f h2 I hI hmatch hregular).hom ≫
      schemeStructureTensorInclusion (schemeKernelIdealι D.rootZeroGlobalι) (top (D.morphism ≫ f) 2) =
      SchemeKaehlerExteriorPullbackTransport.map f D.morphism (D.morphism ≫ f) rfl 2 := by
  letI (c : D.CanonicalFrameChart f) : IsOpenImmersion (D.frameGlobalι c.le) :=
    D.frameGlobalι_isOpenImmersion c.le c.U.2
  letI := D.originalCanonicalTensorInclusion_mono f
  exact schemeModuleMonicFactorIsoOnOpenCharts_comp
    (fun c : D.CanonicalFrameChart f => D.frameChart c.le)
    (fun c => D.frameGlobalι c.le) (D.canonicalFrameCharts_cover f I hI hmatch hregular)
    (schemeStructureTensorInclusion (schemeKernelIdealι D.rootZeroGlobalι) (top (D.morphism ≫ f) 2))
    (SchemeKaehlerExteriorPullbackTransport.map f D.morphism (D.morphism ≫ f) rfl 2)
    (fun c => (D.canonicalFrameFactor f h2 c).val)
    (fun c => (D.canonicalFrameFactor f h2 c).property)

end KltDP.Geometry.QuadraticCoverAtlas.Data

#print axioms KltDP.Geometry.QuadraticCoverAtlas.Data.originalCanonicalFactor_comp
