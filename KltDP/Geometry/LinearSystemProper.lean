import KltDP.Geometry.LinearSystemMorphism
import KltDP.Geometry.ProjectiveProper

/-!
# Properness of the original linear-system morphism

The constructed map composed with the original projective-space structure
morphism is the original proper map to Spec k. The target is separated over
k, so the pinned proper-composite lemma proves properness of the constructed
map itself. Its underlying map is closed and its actual range is closed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.LinearSystemMorphism

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open InvertibleSectionNonvanishingOpen

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (L : InvertibleSheaf X) {n : ℕ} (s : Fin (n + 1) → L.obj.sections)
  (f : X ⟶ Spec (CommRingCat.of k))
  (hcover : (⨆ j, nonvanishingOpen X L (s j)) = ⊤) [IsProper f]

/-- The original covering linear system defines a proper map when the original source is proper. -/
instance morphism_isProper : IsProper (morphism L s f hcover) := by
  haveI : IsProper (morphism L s f hcover ≫ projectiveSpaceToSpec k n) := by
    rw [morphism_structure L s f hcover]
    infer_instance
  exact IsProper.of_comp_of_isSeparated (morphism L s f hcover) (projectiveSpaceToSpec k n)

/-- The actual underlying linear-system map sends closed subsets to closed subsets. -/
theorem morphism_isClosedMap : IsClosedMap (morphism L s f hcover).base :=
  (morphism L s f hcover).isClosedMap

/-- The original linear-system morphism has closed range in the original projective space. -/
theorem range_morphism_isClosed : IsClosed (Set.range (morphism L s f hcover).base) :=
  (morphism_isClosedMap L s f hcover).isClosed_range

end KltDP.Geometry.LinearSystemMorphism
