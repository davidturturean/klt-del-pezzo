import KltDP.Geometry.PullbackSectionMap
import KltDP.Geometry.LinearSystemIsoCoordinates
import KltDP.Geometry.InvertibleSectionNonvanishingPullback
import KltDP.Geometry.CompleteLinearSystemBaseLocus

/-!
# A generating subsystem defines the complete map wherever its sheaf map is invertible

On any original open where an actual map H to L is invertible, the images
of a generating tuple for H still generate the restricted L. Every such
image section is detected by the original full H0 basis, so the same
open lies in the actual non-base open of the complete system.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.SubsystemNonbaseOpen

open InvertibleSectionNonvanishingOpen InvertibleSheafSectionPowersPullback
  CompleteLinearSystemSections CompleteLinearSystemExpansion LinearSystemNaturality

variable {X : Scheme.{u}} (H L : InvertibleSheaf X)
  {n : ℕ} (s : Fin (n + 1) → H.obj.sections) (g : H.obj ⟶ L.obj)
  (hcover : (⨆ i, nonvanishingOpen X H (s i)) = ⊤)

include hcover in
/-- The actual image sections cover every original open where the sheaf map is an isomorphism. -/
theorem pulled_image_sections_cover (U : X.Opens)
    [IsIso ((schemeModulePullback U.ι).map g)] :
    (⨆ i, nonvanishingOpen U.toScheme (pullbackInvertibleSheaf U.ι L)
      (InvertibleSheafSectionPowersPullback.pullbackSection U.ι L.obj (_root_.SheafOfModules.sectionsMap g (s i)))) = ⊤ := by
  let t := fun i => InvertibleSheafSectionPowersPullback.pullbackSection U.ι H.obj (s i)
  have ht : (⨆ i, nonvanishingOpen U.toScheme (pullbackInvertibleSheaf U.ι H) (t i)) = ⊤ := by
    calc
      _ = ⨆ i, U.ι ⁻¹ᵁ nonvanishingOpen X H (s i) :=
        iSup_congr (fun i => InvertibleSectionNonvanishingPullback.nonvanishingOpen_pullback
          U.ι H (s i))
      _ = U.ι ⁻¹ᵁ (⨆ i, nonvanishingOpen X H (s i)) :=
        (U.ι.preimage_iSup _).symm
      _ = ⊤ := by rw [hcover]; rfl
  let e : (pullbackInvertibleSheaf U.ι H).obj ≅ (pullbackInvertibleSheaf U.ι L).obj :=
    asIso ((schemeModulePullback U.ι).map g)
  have he := isoSections_cover (pullbackInvertibleSheaf U.ι H)
    (pullbackInvertibleSheaf U.ι L) e t ht
  have hsections : isoSections (pullbackInvertibleSheaf U.ι H)
      (pullbackInvertibleSheaf U.ι L) e t =
      fun i => InvertibleSheafSectionPowersPullback.pullbackSection U.ι L.obj (_root_.SheafOfModules.sectionsMap g (s i)) := by
    funext i
    exact pullbackSection_sectionsMap U.ι g (s i)
  rw [hsections] at he
  exact he

variable {k : Type u} [Field k] (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]

include hcover in
/-- Every point of the original isomorphism open belongs to the full original system's domain. -/
theorem iso_open_le_complete_nonbase (hpos : 0 < dimension f L) (U : X.Opens)
    [IsIso ((schemeModulePullback U.ι).map g)] :
    U ≤ ⨆ i, nonvanishingOpen X L (positiveBasisSections f L hpos i) := by
  intro x hx
  let y : U.toScheme := ⟨x, hx⟩
  have hy : y ∈ ⨆ i, nonvanishingOpen U.toScheme (pullbackInvertibleSheaf U.ι L)
      (InvertibleSheafSectionPowersPullback.pullbackSection U.ι L.obj (_root_.SheafOfModules.sectionsMap g (s i))) := by
    rw [pulled_image_sections_cover H L s g hcover U]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hy
  rw [InvertibleSectionNonvanishingPullback.nonvanishingOpen_pullback] at hi
  exact nonvanishingOpen_le_basis f L hpos (_root_.SheafOfModules.sectionsMap g (s i)) hi

end KltDP.Geometry.SubsystemNonbaseOpen
