import KltDP.Geometry.LinearSystemSectionIsoMorphism
import KltDP.Geometry.LinearSystemPullbackCoordinates
import KltDP.Geometry.PullbackSectionMap

/-!
# Original pulled linear systems under an ambient sheaf isomorphism

The literal pullback of the transported original sections is the
transport of their literal pullbacks. The existing intrinsic-open and
actual-morphism invariance theorems therefore preserve a cover and map
on the original source of the pullback. No ambient cover is required.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.LinearSystemNaturality

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open InvertibleSectionNonvanishingOpen LinearSystemMorphism

variable {X Y : Scheme.{u}} (h : Y ⟶ X) (L M : InvertibleSheaf X)
  (e : L.obj ≅ M.obj) {n : ℕ} (s : Fin (n + 1) → L.obj.sections)

/-- Transport retains the actual pulled section cover on the original source. -/
theorem pullback_isoSections_cover
    (hcover : (⨆ j, nonvanishingOpen Y (pullbackInvertibleSheaf h L)
      (pullbackSections h L s j)) = ⊤) :
    (⨆ j, nonvanishingOpen Y (pullbackInvertibleSheaf h M)
      (pullbackSections h M (isoSections L M e s) j)) = ⊤ := by
  calc
    _ = ⨆ j, nonvanishingOpen Y (pullbackInvertibleSheaf h M)
        (_root_.SheafOfModules.sectionsMap ((schemeModulePullback h).mapIso e).hom
          (pullbackSections h L s j)) := by
      apply iSup_congr
      intro j
      exact congrArg (nonvanishingOpen Y (pullbackInvertibleSheaf h M))
        (pullbackSection_sectionsMap h e.hom (s j)).symm
    _ = ⨆ j, nonvanishingOpen Y (pullbackInvertibleSheaf h L)
        (pullbackSections h L s j) :=
      iSup_congr (fun j => nonvanishingOpen_sectionsMap_iso
        (pullbackInvertibleSheaf h L) (pullbackInvertibleSheaf h M)
        ((schemeModulePullback h).mapIso e) (pullbackSections h L s j))
    _ = ⊤ := hcover

/-- The original projective map on the original source is unchanged by
transporting the ambient original sections through an actual isomorphism. -/
theorem morphism_pullback_isoSections
    {k : Type u} [Field k] (b : Y ⟶ Spec (CommRingCat.of k))
    (hcover : (⨆ j, nonvanishingOpen Y (pullbackInvertibleSheaf h L)
      (pullbackSections h L s j)) = ⊤) :
    morphism (pullbackInvertibleSheaf h M)
      (pullbackSections h M (isoSections L M e s)) b
      (pullback_isoSections_cover h L M e s hcover) =
        morphism (pullbackInvertibleSheaf h L) (pullbackSections h L s) b hcover :=
  (morphism_eq_of_iso_sections
    (pullbackInvertibleSheaf h L) (pullbackInvertibleSheaf h M)
    ((schemeModulePullback h).mapIso e)
    (pullbackSections h L s) (pullbackSections h M (isoSections L M e s)) b b
    hcover (pullback_isoSections_cover h L M e s hcover)
    (fun j => pullbackSection_sectionsMap h e.hom (s j)) rfl).symm

end KltDP.Geometry.LinearSystemNaturality
