import KltDP.Geometry.SubsystemNonbaseOpen
import KltDP.Geometry.LinearSystemMapIso
import KltDP.Geometry.LinearSystemMapPullback

/-!
# The mapped subsystem recovers the original map on its isomorphism open

The original pulled section map is an isomorphism on the indicated open.
Original section-map naturality identifies the mapped sections with its
transported tuple. The compiled map invariance and pullback naturality
then identify its actual projective morphism with the original one.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.SubsystemNonbaseOpen

open InvertibleSectionNonvanishingOpen LinearSystemNaturality

private theorem morphism_congr_sections {k : Type u} [Field k] {X : Scheme.{u}}
    (L : InvertibleSheaf X) {n : ℕ} (s t : Fin (n + 1) → L.obj.sections)
    (f : X ⟶ Spec (CommRingCat.of k)) (h : s = t)
    (hs : (⨆ i, nonvanishingOpen X L (s i)) = ⊤)
    (ht : (⨆ i, nonvanishingOpen X L (t i)) = ⊤) :
    LinearSystemMorphism.morphism L s f hs = LinearSystemMorphism.morphism L t f ht := by
  cases h
  rfl

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (H L : InvertibleSheaf X) {n : ℕ} (s : Fin (n + 1) → H.obj.sections)
  (g : H.obj ⟶ L.obj) (f : X ⟶ Spec (CommRingCat.of k))
  (hcover : (⨆ i, nonvanishingOpen X H (s i)) = ⊤)

/-- On the actual isomorphism open, the images of the original generating
sections define precisely the restriction of their original projective morphism. -/
theorem mapped_morphism_eq (U : X.Opens)
    [IsIso ((schemeModulePullback U.ι).map g)] :
    LinearSystemMorphism.morphism (pullbackInvertibleSheaf U.ι L)
      (pullbackSections U.ι L (fun i => _root_.SheafOfModules.sectionsMap g (s i)))
      (U.ι ≫ f) (pulled_image_sections_cover H L s g hcover U) =
        U.ι ≫ LinearSystemMorphism.morphism H s f hcover := by
  let HP := pullbackInvertibleSheaf U.ι H
  let LP := pullbackInvertibleSheaf U.ι L
  let t := pullbackSections U.ι H s
  let e : HP.obj ≅ LP.obj := asIso ((schemeModulePullback U.ι).map g)
  have ht := pullbackSections_cover U.ι H s hcover
  have hsections : isoSections HP LP e t =
      pullbackSections U.ι L (fun i => _root_.SheafOfModules.sectionsMap g (s i)) := by
    funext i
    exact pullbackSection_sectionsMap U.ι g (s i)
  have he := morphism_sectionsMap_iso HP LP t (U.ι ≫ f) e ht
  exact (morphism_congr_sections LP
    (pullbackSections U.ι L (fun i => _root_.SheafOfModules.sectionsMap g (s i)))
    (isoSections HP LP e t) (U.ι ≫ f) hsections.symm
    (pulled_image_sections_cover H L s g hcover U) (isoSections_cover HP LP e t ht)).trans
      (he.trans (morphism_pullback U.ι H s f hcover))

end KltDP.Geometry.SubsystemNonbaseOpen
