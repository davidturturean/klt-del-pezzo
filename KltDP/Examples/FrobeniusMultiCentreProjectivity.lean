import KltDP.Geometry.ProjectiveOverSeparatedPullback
import KltDP.Examples.FrobeniusTowerTransport
import KltDP.Examples.FrobeniusMultiCentreIntegral
import KltDP.Examples.FrobeniusStageOneProjective

/-!
# Multi-centre projectivity from the actual origin contact tower

The actual translation isomorphisms transfer a projective embedding of the
origin stage to every selected tower at the same depth. The finite-centre surface
is the accepted iterated fibre product of these towers over `P¹ × P¹`. Since that
base is separated over the field, the projective fibre-product adapter proves
projectivity of the multi-centre surface from the same origin-stage hypothesis.

The hypothesis is discharged at depth one by the accepted explicit embedding of
the first origin blowup in `P⁷`. Thus finitely many distinct selected points, each
blown up once, give actual normal projective surfaces without a projectivity
premise. General-depth origin projectivity remains an explicit prerequisite;
no multi-centre intersection or canonical-divisor formula is asserted here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Examples.FrobeniusMultiCentreProjectivity

open KltDP.Geometry KltDP.Geometry.ProjectiveOverSeparatedPullback
  FrobeniusBlowupChartIteration FrobeniusGlobalBlowupStages
  FrobeniusTranslatedCharts FrobeniusContactTowerSelectedPoint
  FrobeniusTowerTransport FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
  FrobeniusProjectivePoints FrobeniusStageOneProjective

variable {k : Type u} [Field k]

/-- Every selected stage inherits an actual projective embedding from the origin
stage at the same depth, via the accepted translation isomorphism over `k`. -/
theorem selectedStage_projective_of_origin (p N : ℕ) (c : k)
    (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage N).structureMap) :
    IsProjectiveOverField ((translatedInitial p c).stage N).structureMap :=
  projective_of_iso (stageTranslationIso p c N)
    ((projectiveProductInitial (k := k)).stage N).structureMap
    ((translatedInitial p c).stage N).structureMap
    (stageTranslationIso_hom_structure p c N) hproj

/-- A projective origin stage of depth `p` supplies an actual projective embedding
of the finite-centre scheme with every tower at depth `p`. -/
theorem multiStructure_projective_of_origin (p : ℕ)
    (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage p).structureMap) :
    ∀ (n : ℕ) (a : Fin n → k), IsProjectiveOverField (multiStructure p n a)
  | 0, _ => by
      change IsProjectiveOverField (𝟙 (projectiveProduct k) ≫ projectiveProductToSpec)
      rw [Category.id_comp]
      exact ProjectiveSegreGeneral.projectiveProduct_isProjectiveOverField_general k
  | n + 1, a => by
      have hleft : IsProjectiveOverField
          (multiProjection p n (fun i => a i.castSucc) ≫ projectiveProductToSpec) :=
        multiStructure_projective_of_origin p hproj n (fun i => a i.castSucc)
      have hright : IsProjectiveOverField
          (selectedProjection p (a (Fin.last n)) p ≫ projectiveProductToSpec) := by
        rw [selectedProjection_structure]
        exact selectedStage_projective_of_origin p p (a (Fin.last n)) hproj
      rw [multiStructure_succ]
      simpa only [Category.assoc] using
        projective_pullback (multiProjection p n (fun i => a i.castSucc))
          (selectedProjection p (a (Fin.last n)) p) projectiveProductToSpec hleft hright

/-- The accepted multi-centre scheme as a normal projective surface, using only
the existing origin-stage projectivity premise. -/
def multiSurfaceFromOrigin [IsAlgClosed k] (p n : ℕ) (a : Fin n → k)
    (ha : Function.Injective a)
    (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage p).structureMap) :
    NormalProjectiveSurface k :=
  multiSurfaceSurface p n a ha (multiStructure_projective_of_origin p hproj n a)

@[simp] theorem multiSurfaceFromOrigin_toScheme [IsAlgClosed k] (p n : ℕ) (a : Fin n → k)
    (ha : Function.Injective a)
    (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage p).structureMap) :
    (multiSurfaceFromOrigin p n a ha hproj).toScheme = multiSurface p n a := rfl

/-- The depth-one finite-centre fibre-product scheme is projective, from the
accepted explicit stage-one embedding. Distinctness is unnecessary for this assertion. -/
theorem multiStructure_one_projective (n : ℕ) (a : Fin n → k) :
    IsProjectiveOverField (multiStructure 1 n a) :=
  multiStructure_projective_of_origin 1 (stage_one_projective (k := k)) n a

/-- The actual finite-centre surface with one blowup at each distinct selected
centre, without a projectivity premise. -/
def oneBlowupMultiSurface [IsAlgClosed k] (n : ℕ) (a : Fin n → k)
    (ha : Function.Injective a) : NormalProjectiveSurface k :=
  multiSurfaceSurface 1 n a ha (multiStructure_one_projective n a)

@[simp] theorem oneBlowupMultiSurface_toScheme [IsAlgClosed k] (n : ℕ) (a : Fin n → k)
    (ha : Function.Injective a) :
    (oneBlowupMultiSurface n a ha).toScheme = multiSurface 1 n a := rfl

end KltDP.Examples.FrobeniusMultiCentreProjectivity
