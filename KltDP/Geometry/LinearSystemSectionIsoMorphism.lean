import KltDP.Geometry.LinearSystemMapIso

/-!
# Comparing actual linear-system morphisms through a section-preserving isomorphism

This is the existing isomorphism-invariance theorem with the transported
sections and the original base map identified by explicit equalities.
It retains the actual maps and accepts either proof of the same open cover.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.LinearSystemNaturality

open InvertibleSectionNonvanishingOpen LinearSystemMorphism

/-- Actual section and base equalities specialize the proved isomorphism invariance. -/
theorem morphism_eq_of_iso_sections {k : Type u} [Field k] {X : Scheme.{u}}
    (L M : InvertibleSheaf X) (e : L.obj ≅ M.obj) {n : ℕ}
    (s : Fin (n + 1) → L.obj.sections) (t : Fin (n + 1) → M.obj.sections)
    (f g : X ⟶ Spec (CommRingCat.of k))
    (hs : (⨆ j, nonvanishingOpen X L (s j)) = ⊤)
    (ht : (⨆ j, nonvanishingOpen X M (t j)) = ⊤)
    (he : ∀ j, _root_.SheafOfModules.sectionsMap e.hom (s j) = t j)
    (hfg : f = g) :
    morphism L s f hs = morphism M t g ht := by
  have hst : isoSections L M e s = t := funext he
  subst t
  subst g
  exact (morphism_sectionsMap_iso L M s f e hs).symm

end KltDP.Geometry.LinearSystemNaturality
