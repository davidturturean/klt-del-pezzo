import KltDP.Geometry.CompleteLinearSystemSubsystemTriangle
import KltDP.Geometry.SchematicImageMatrixTriangle
import KltDP.Geometry.InvertibleNonzeroIsoOpen

/-!
# The original complete linear system containing an embedded subsystem is birational

A nonzero original line-bundle map is invertible on an actual nonempty
open. The original complete-basis coefficient matrix recovers the given
closed-immersion subsystem there. Its actual image-open triangle proves
birationality of the original factor to the original schematic image.
The positivity input concerns the dimension of all original H0 sections.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.CompleteLinearSystemMap

open CompleteLinearSystemSections InvertibleSectionNonvanishingOpen

local instance subsystem_nonBaseOpen_integral
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [IsIntegral X]
    (L : InvertibleSheaf X) (hpos : 0 < dimension f L) :
    IsIntegral (nonBaseOpen f L hpos).toScheme := by
  letI : Nonempty (nonBaseOpen f L hpos) := (nonBaseOpen_nonempty f L hpos).to_subtype
  infer_instance

local instance subsystem_image_integral
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [IsIntegral X]
    (L : InvertibleSheaf X) (hpos : 0 < dimension f L) :
    IsIntegral (SchematicImageGlued.image (morphism f L hpos)) :=
  image_isIntegral f L hpos

/-- A nonzero map from an actually embedded generating subsystem makes the
original complete-system factor to its actual schematic image birational. -/
theorem toImage_isBirationalScheme_of_subsystem
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [IsIntegral X]
    (H L : InvertibleSheaf X) {m : ℕ} (s : Fin (m + 1) → H.obj.sections)
    (hcover : (⨆ j, nonvanishingOpen X H (s j)) = ⊤)
    (σ : H.obj ⟶ L.obj) (hσ : σ ≠ 0)
    (hclosed : IsClosedImmersion (LinearSystemMorphism.morphism H s f hcover))
    (hpos : 0 < dimension f L) :
    IsBirationalScheme (SchematicImageGlued.toImage (morphism f L hpos)) := by
  obtain ⟨U, hU, hσU⟩ := InvertibleNonzeroIsoOpen.exists_isIso_open X H L σ hσ
  letI : Nonempty U := hU
  letI : IsIntegral U.toScheme := inferInstance
  letI : IsIso ((schemeModulePullback U.ι).map σ) := hσU
  letI : Nonempty (nonBaseOpen f L hpos) := (nonBaseOpen_nonempty f L hpos).to_subtype
  letI : IsIntegral (nonBaseOpen f L hpos).toScheme := inferInstance
  letI : IsClosedImmersion (LinearSystemMorphism.morphism H s f hcover) := hclosed
  exact SchematicImageMatrixTriangle.toImage_isBirationalScheme
    (morphism f L hpos)
    (CompleteLinearSystemSubsystem.sourceMap f H L s σ hpos hcover U)
    U.ι (LinearSystemMorphism.morphism H s f hcover)
    (ProjectiveLinearForms.domain k (dimension f L - 1)
      (CompleteLinearSystemSubsystem.matrix f H L s σ hpos))
    (CompleteLinearSystemSubsystem.matrixMap f H L s σ hpos hcover U)
    (ProjectiveLinearForms.morphism k (dimension f L - 1)
      (CompleteLinearSystemSubsystem.matrix f H L s σ hpos))
    (CompleteLinearSystemSubsystem.matrixMap_complete f H L s σ hpos hcover U)
    (CompleteLinearSystemSubsystem.matrix_triangle f H L s σ hpos hcover U)

end KltDP.Geometry.CompleteLinearSystemMap
