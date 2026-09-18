import KltDP.Geometry.PointBlowupAffineDifferentialFactor
import KltDP.Geometry.PointBlowupComplementDifferentialFactor
import KltDP.Geometry.PointBlowupGluingRelativeDimension
import KltDP.Geometry.SchemeModuleMonicFactorOnCharts
import KltDP.Geometry.SmoothCanonicalExteriorComparison
import KltDP.Geometry.InvertibleTensorExact

/-!
# The normalized original canonical factor on the whole centered point blowup

The actual affine blowup and actual exceptional complement cover the
original glued scheme. Their proved factors retain the same original
inclusion and differential, so the accepted monic-factor construction
glues them. The source and the derived affine model supply smooth relative
dimension two; the original global inclusion is therefore monic.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Geometry.PointBlowupTopDifferential

open PointBlowupGluing

local instance centeredPointModules (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

private theorem pointTensorInclusion_mono {Y : Scheme.{u}} {I : Y.Modules}
    (i : I ⟶ _root_.SheafOfModules.unit Y.ringCatSheaf) [Mono i]
    (L : InvertibleSheaf Y) : Mono (schemeStructureTensorInclusion i L.obj) := by
  letI := L.tensorRight_preservesFiniteLimits
  haveI : Mono (i ≫ (SchemeModuleStructureUnit.iso Y).hom) := inferInstance
  change Mono ((tensorRight L.obj).map (i ≫ (SchemeModuleStructureUnit.iso Y).hom) ≫
    (λ_ L.obj).hom)
  infer_instance

variable {k R : Type u} [Field k] [CommRing R] [Algebra k R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsSmoothOfRelativeDimension 2 f]
    (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
    (hclosed : IsClosed ({j.base q} : Set X))
    (hj : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k R)))
    (φ : KltDP.Examples.FrobeniusBlowupContact.planeRing k →ₐ[k] R)
    (hφ : φ.toRingHom.IsStandardSmoothOfRelativeDimension 0)
    (hcenter : SmoothPointBlowupAffineCanonicalFactor.extendedCenter k φ = q.asIdeal)

include hj hφ hcenter in
/-- Smooth relative dimension two is derived on the same original whole blowup. -/
theorem centeredStructureSmoothTwo :
    IsSmoothOfRelativeDimension 2 (projection j q hclosed ≫ f) := by
  have hA := SmoothPointBlowupAffineCanonicalFactor.structureMap_isSmoothTwo k φ hφ
  rw [hcenter] at hA
  apply isSmoothOfRelativeDimension_projection_comp_of_affine j q hclosed f 2
  rw [hj]
  exact hA

/-- The same original top-differential sheaf is an actual invertible sheaf. -/
def centeredTopLine : InvertibleSheaf (scheme j q hclosed) := by
  letI := centeredStructureSmoothTwo f j q hclosed hj φ hφ hcenter
  exact ⟨topSheaf f j q hclosed 2,
    SmoothCanonicalExteriorComparison.relativeDifferentialExterior_isInvertible
      (projection j q hclosed ≫ f)⟩

include hj hφ hcenter in
theorem centeredExceptionalInclusion_mono : Mono (exceptionalInclusion f j q hclosed 2) := by
  letI : Mono (schemeKernelIdealι (globalCenterFiberι j q hclosed)) := by
    unfold schemeKernelIdealι
    infer_instance
  exact pointTensorInclusion_mono (schemeKernelIdealι (globalCenterFiberι j q hclosed))
    (centeredTopLine f j q hclosed hj φ hφ hcenter)

/-- The two actual open pieces used in the normalized factor gluing. -/
def factorPiece : Bool → Scheme.{u}
  | false => AffineBlowup.scheme q.asIdeal
  | true => (exceptionalComplementOpen j q hclosed).toScheme

def factorPieceMap : (i : Bool) → factorPiece j q hclosed i ⟶ scheme j q hclosed
  | false => affineBlowupι j q hclosed
  | true => (exceptionalComplementOpen j q hclosed).ι

instance factorPieceMap_isOpenImmersion (i : Bool) :
    IsOpenImmersion (factorPieceMap j q hclosed i) := by
  cases i
  · change IsOpenImmersion (affineBlowupι j q hclosed)
    infer_instance
  · change IsOpenImmersion (exceptionalComplementOpen j q hclosed).ι
    infer_instance

theorem factorPiece_cover (x : scheme j q hclosed) :
    ∃ i, ∃ y : factorPiece j q hclosed i, (factorPieceMap j q hclosed i).base y = x := by
  obtain ⟨a, ha⟩ | ⟨b, hb⟩ := pieces_cover j q hclosed x
  · exact ⟨false, a, ha⟩
  · refine ⟨true, ⟨x, ?_⟩, rfl⟩
    change x ∈ (projection j q hclosed ⁻¹ᵁ puncture j q hclosed : Set (scheme j q hclosed))
    rw [← range_complementι j q hclosed]
    exact ⟨b, hb⟩

/-- Both original local factors have exactly the two original global objects as carriers. -/
def centeredPieceFactor (i : Bool) :
    (schemeModulePullback (factorPieceMap j q hclosed i)).obj
        ((schemeModulePullback (projection j q hclosed)).obj (sourceSheaf f 2)) ≅
      (schemeModulePullback (factorPieceMap j q hclosed i)).obj
        (exceptionalTensor f j q hclosed 2) := by
  cases i
  · exact affineFactorIso f j q hclosed hj φ hφ hcenter
  · exact complementFactorIso f j q hclosed 2

theorem centeredPieceFactor_comp (i : Bool) :
    (centeredPieceFactor f j q hclosed hj φ hφ hcenter i).hom ≫
        (schemeModulePullback (factorPieceMap j q hclosed i)).map
          (exceptionalInclusion f j q hclosed 2) =
      (schemeModulePullback (factorPieceMap j q hclosed i)).map
        (blowdownMap f j q hclosed 2) := by
  cases i
  · exact affineFactorIso_comp f j q hclosed hj φ hφ hcenter
  · exact complementFactorIso_comp f j q hclosed 2

/-- The original whole blowdown differential factors through the actual exceptional ideal tensor. -/
def centeredCanonicalFactorIso :
    (schemeModulePullback (projection j q hclosed)).obj (sourceSheaf f 2) ≅
      exceptionalTensor f j q hclosed 2 := by
  letI := centeredExceptionalInclusion_mono f j q hclosed hj φ hφ hcenter
  exact schemeModuleMonicFactorIsoOnOpenCharts
    (factorPiece j q hclosed) (factorPieceMap j q hclosed) (factorPiece_cover j q hclosed)
    (exceptionalInclusion f j q hclosed 2) (blowdownMap f j q hclosed 2)
    (centeredPieceFactor f j q hclosed hj φ hφ hcenter)
    (centeredPieceFactor_comp f j q hclosed hj φ hφ hcenter)

/-- This same isomorphism preserves the whole original intrinsic differential. -/
theorem centeredCanonicalFactorIso_comp :
    (centeredCanonicalFactorIso f j q hclosed hj φ hφ hcenter).hom ≫
        exceptionalInclusion f j q hclosed 2 = blowdownMap f j q hclosed 2 := by
  letI := centeredExceptionalInclusion_mono f j q hclosed hj φ hφ hcenter
  exact schemeModuleMonicFactorIsoOnOpenCharts_comp
    (factorPiece j q hclosed) (factorPieceMap j q hclosed) (factorPiece_cover j q hclosed)
    (exceptionalInclusion f j q hclosed 2) (blowdownMap f j q hclosed 2)
    (centeredPieceFactor f j q hclosed hj φ hφ hcenter)
    (centeredPieceFactor_comp f j q hclosed hj φ hφ hcenter)

end KltDP.Geometry.PointBlowupTopDifferential
