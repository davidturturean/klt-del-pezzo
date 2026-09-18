import KltDP.Geometry.LinearSystemRationalMapSubopen
import KltDP.Geometry.SubsystemMapOnIsoOpen
import KltDP.Geometry.CompleteLinearSystemImage
import KltDP.Geometry.CompleteLinearSystemExpansion
import KltDP.Geometry.LinearSystemMatrixSections

/-!
# The actual subsystem matrix domain on the original isomorphism open

The rows are the coefficients of the actual image sections in the entire
original H0 basis. Pullback preserves each row expansion. On an open where
the original line-bundle map is invertible, the image sections cover, so
the original complete map lands in the actual projective matrix domain.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.CompleteLinearSystemSubsystem

open CompleteLinearSystemSections InvertibleSectionNonvanishingOpen
  LinearSystemNaturality

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [IsIntegral X]
  (H L : InvertibleSheaf X) {m : ℕ} (s : Fin (m + 1) → H.obj.sections)
  (σ : H.obj ⟶ L.obj) (hpos : 0 < dimension f L)

/-- The actual coefficient rows of the mapped subsystem in the full original section basis. -/
abbrev matrix : Fin (m + 1) → Fin ((dimension f L - 1) + 1) → k :=
  CompleteLinearSystemExpansion.mappedCoefficients f L hpos H.obj σ s

/-- Pulling the original complete-basis expansion to an open gives the actual pulled image section. -/
theorem pulled_combination (U : X.Opens) (j : Fin (m + 1)) :
    SectionLinearCombinations.combination (U.ι ≫ f) (pullbackInvertibleSheaf U.ι L).obj
      (pullbackSections U.ι L (positiveBasisSections f L hpos))
      (matrix f H L s σ hpos j) =
        InvertibleSheafSectionPowersPullback.pullbackSection U.ι L.obj
          (_root_.SheafOfModules.sectionsMap σ (s j)) := by
  exact (SectionLinearCombinations.pullbackSection_combination f U.ι L.obj
    (positiveBasisSections f L hpos) (matrix f H L s σ hpos j)).symm.trans
      (congrArg (InvertibleSheafSectionPowersPullback.pullbackSection U.ι L.obj)
        (CompleteLinearSystemExpansion.combination_mappedCoefficients
          f L hpos H.obj σ s j))

variable (hcover : (⨆ j, nonvanishingOpen X H (s j)) = ⊤)
  (U : X.Opens) [IsIso ((schemeModulePullback U.ι).map σ)]

include σ hcover in
/-- The original isomorphism open lies in the actual complete-system domain. -/
theorem isoOpen_le_nonBase : U ≤ CompleteLinearSystemMap.nonBaseOpen f L hpos :=
  SubsystemNonbaseOpen.iso_open_le_complete_nonbase H L s σ hcover f hpos U

/-- The actual open inclusion into the complete system's original domain. -/
abbrev sourceMap : U.toScheme ⟶ (CompleteLinearSystemMap.nonBaseOpen f L hpos).toScheme :=
  X.homOfLE (isoOpen_le_nonBase f H L s σ hpos hcover U)

/-- The actual complete-basis linear-system morphism on the original isomorphism open. -/
abbrev restrictedCompleteMorphism : U.toScheme ⟶ projectiveSpace k (dimension f L - 1) :=
  LinearSystemMorphism.morphism (pullbackInvertibleSheaf U.ι L)
    (pullbackSections U.ι L (positiveBasisSections f L hpos)) (U.ι ≫ f)
    (LinearSystemRationalMap.subopenSections_cover L (positiveBasisSections f L hpos) U
      (isoOpen_le_nonBase f H L s σ hpos hcover U))

/-- This is the restriction of the original complete-system morphism, with the original maps. -/
theorem sourceMap_comp_complete :
    sourceMap f H L s σ hpos hcover U ≫ CompleteLinearSystemMap.morphism f L hpos =
      restrictedCompleteMorphism f H L s σ hpos hcover U :=
  LinearSystemRationalMap.morphism_subopen L (positiveBasisSections f L hpos) U
    (isoOpen_le_nonBase f H L s σ hpos hcover U) f

/-- The pulled original image sections force the actual matrix-domain preimage to be the whole open. -/
theorem matrixDomain_preimage :
    restrictedCompleteMorphism f H L s σ hpos hcover U ⁻¹ᵁ
      ProjectiveLinearForms.domain k (dimension f L - 1) (matrix f H L s σ hpos) = ⊤ := by
  calc
    _ = ⨆ j, nonvanishingOpen U.toScheme (pullbackInvertibleSheaf U.ι L)
        (SectionLinearCombinations.combination (U.ι ≫ f) (pullbackInvertibleSheaf U.ι L).obj
          (pullbackSections U.ι L (positiveBasisSections f L hpos))
          (matrix f H L s σ hpos j)) :=
      LinearSystemMatrixSections.preimage_matrixDomain (pullbackInvertibleSheaf U.ι L)
        (pullbackSections U.ι L (positiveBasisSections f L hpos)) (U.ι ≫ f)
        (LinearSystemRationalMap.subopenSections_cover L (positiveBasisSections f L hpos) U
          (isoOpen_le_nonBase f H L s σ hpos hcover U)) (matrix f H L s σ hpos)
    _ = ⨆ j, nonvanishingOpen U.toScheme (pullbackInvertibleSheaf U.ι L)
        (InvertibleSheafSectionPowersPullback.pullbackSection U.ι L.obj
          (_root_.SheafOfModules.sectionsMap σ (s j))) :=
      iSup_congr (fun j => congrArg (nonvanishingOpen U.toScheme (pullbackInvertibleSheaf U.ι L))
        (pulled_combination f H L s σ hpos U j))
    _ = ⊤ := SubsystemNonbaseOpen.pulled_image_sections_cover H L s σ hcover U

private theorem range_le_matrixDomain :
    Set.range (restrictedCompleteMorphism f H L s σ hpos hcover U).base ⊆
      Set.range (ProjectiveLinearForms.domain k (dimension f L - 1)
        (matrix f H L s σ hpos)).ι.base := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨x, rfl⟩
  have hx : x ∈ restrictedCompleteMorphism f H L s σ hpos hcover U ⁻¹ᵁ
      ProjectiveLinearForms.domain k (dimension f L - 1) (matrix f H L s σ hpos) := by
    rw [matrixDomain_preimage]
    trivial
  exact hx

/-- The lift is the original open-immersion universal factor of the original complete map. -/
def matrixMap : U.toScheme ⟶
    (ProjectiveLinearForms.domain k (dimension f L - 1) (matrix f H L s σ hpos)).toScheme :=
  IsOpenImmersion.lift
    (ProjectiveLinearForms.domain k (dimension f L - 1) (matrix f H L s σ hpos)).ι
    (restrictedCompleteMorphism f H L s σ hpos hcover U)
    (range_le_matrixDomain f H L s σ hpos hcover U)

/-- The actual matrix-domain factor has exactly the original complete map as its composite. -/
theorem matrixMap_inclusion :
    matrixMap f H L s σ hpos hcover U ≫
      (ProjectiveLinearForms.domain k (dimension f L - 1) (matrix f H L s σ hpos)).ι =
        restrictedCompleteMorphism f H L s σ hpos hcover U :=
  IsOpenImmersion.lift_fac _ _ _

/-- The same factor square written against the original complete-system morphism. -/
theorem matrixMap_complete :
    matrixMap f H L s σ hpos hcover U ≫
      (ProjectiveLinearForms.domain k (dimension f L - 1) (matrix f H L s σ hpos)).ι =
        sourceMap f H L s σ hpos hcover U ≫ CompleteLinearSystemMap.morphism f L hpos :=
  (matrixMap_inclusion f H L s σ hpos hcover U).trans
    (sourceMap_comp_complete f H L s σ hpos hcover U).symm

end KltDP.Geometry.CompleteLinearSystemSubsystem
