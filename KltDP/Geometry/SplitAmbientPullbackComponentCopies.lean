import KltDP.Geometry.SplitAmbientPullbackCopies
import KltDP.Geometry.RationalTreePicardComponentPartition
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Retaining both copies of every original irreducible component

The actual reduced component inclusion is composed with each of the two
actual ambient tree maps. Closed immersions and image formulas are proved
for these original maps. Their image family is indexed injectively by
Bool times the original irreducible components, so its cardinality is
twice the original component cardinality. No independence or rank claim
is needed for this geometric count.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u

namespace KltDP.Geometry.SplitAmbientPullbackComponentCopies

open RationalTreePicard SplitAmbientPullbackCopies

variable {X Z C : Scheme.{u}} [NoetherianSpace C]
    (p : Z ⟶ X) (f : C ⟶ X) (q : pullback p f ≅ C ⨿ C)

/-- The original reduced component inclusion followed by an actual labeled ambient copy. -/
def componentCopy (ε : Bool) (D : ↥(irreducibleComponents C)) :
    componentUnionScheme C {D} ⟶ Z :=
  componentUnionInclusion C {D} ≫ ambientCopy p f q ε

instance componentCopy_isClosedImmersion [IsClosedImmersion f]
    (ε : Bool) (D : ↥(irreducibleComponents C)) :
    IsClosedImmersion (componentCopy p f q ε D) := by
  dsimp only [componentCopy]
  infer_instance

/-- The literal image of the actual component map, indexed by both labels. -/
def componentImage (i : Bool × ↥(irreducibleComponents C)) : Set Z :=
  Set.range (componentCopy p f q i.1 i.2).base

/-- Its original image is the image of the original component set under its labeled copy. -/
theorem componentImage_eq (ε : Bool) (D : ↥(irreducibleComponents C)) :
    componentImage p f q (ε, D) = (ambientCopy p f q ε).base '' (D : Set C) := by
  change Set.range ((ambientCopy p f q ε).base ∘ (componentUnionInclusion C {D}).base) = _
  rw [Set.range_comp, range_componentUnionInclusion, coe_componentClosedUnion_singleton]

/-- The actual images retain every original component under each of the two labels. -/
theorem componentImage_injective [IsClosedImmersion f] :
    Function.Injective (componentImage p f q) := by
  rintro ⟨ε, D⟩ ⟨η, E⟩ h
  by_cases hε : ε = η
  · subst η
    apply congrArg (Prod.mk ε)
    apply Subtype.ext
    apply (ambientCopy p f q ε).isClosedEmbedding.injective.image_injective
    simpa only [componentImage_eq] using h
  · have hd : Disjoint (Set.range (ambientCopy p f q ε).base)
        (Set.range (ambientCopy p f q η).base) := by
      cases ε <;> cases η
      · exact False.elim (hε rfl)
      · exact ambientCopy_disjoint p f q
      · exact (ambientCopy_disjoint p f q).symm
      · exact False.elim (hε rfl)
    have hD : IsIrreducible (D : Set C) := D.property.1
    obtain ⟨x, hx⟩ := hD.1
    have hm : (ambientCopy p f q ε).base x ∈ componentImage p f q (ε, D) := by
      rw [componentImage_eq]
      exact ⟨x, hx, rfl⟩
    have hn : (ambientCopy p f q ε).base x ∈ componentImage p f q (η, E) := h ▸ hm
    rw [componentImage_eq] at hn
    obtain ⟨y, hy, hxy⟩ := hn
    exact False.elim ((Set.disjoint_left.mp hd) ⟨x, rfl⟩ ⟨y, hxy⟩)

/-- The actual ambient component-image family has exactly twice as many members. -/
theorem componentImage_card [IsClosedImmersion f] :
    Nat.card (Set.range (componentImage p f q)) = 2 * Nat.card ↥(irreducibleComponents C) := by
  rw [Nat.card_range_of_injective (componentImage_injective p f q), Nat.card_prod]
  have hBool : Nat.card Bool = 2 := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_bool]
  rw [hBool]

variable (hq : q.hom ≫ coprod.desc (𝟙 C) (𝟙 C) = pullback.snd p f)

include hq in
/-- Each original component map lies over precisely its original component inclusion. -/
@[reassoc]
theorem componentCopy_projection (ε : Bool) (D : ↥(irreducibleComponents C)) :
    componentCopy p f q ε D ≫ p = componentUnionInclusion C {D} ≫ f := by
  rw [componentCopy, Category.assoc, ambientCopy_projection p f q hq]

end KltDP.Geometry.SplitAmbientPullbackComponentCopies

#print axioms KltDP.Geometry.SplitAmbientPullbackComponentCopies.componentImage_card
#print axioms KltDP.Geometry.SplitAmbientPullbackComponentCopies.componentCopy_projection
