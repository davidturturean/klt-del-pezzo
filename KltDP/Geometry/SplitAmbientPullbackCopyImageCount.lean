import KltDP.Geometry.SplitAmbientPullbackCopies
import Mathlib.Data.Set.Card

/-!
# Exactly two distinct actual ambient copy images

For a nonempty curve included by a preimmersion, the actual inverse
splitting gives two nonempty disjoint ambient image sets. The two labels
therefore inject into the family of actual image sets, whose cardinality
is exactly two. This counts the two whole-copy images.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

namespace KltDP.Geometry.SplitAmbientPullbackCopyImageCount

open SplitAmbientPullbackCopies

variable {X Z C : Scheme.{u}} [Nonempty C] (p : Z ⟶ X) (f : C ⟶ X)
    [IsPreimmersion f] (q : pullback p f ≅ C ⨿ C)

/-- Disjointness and nonemptiness distinguish the actual image sets themselves. -/
theorem copy_images_ne :
    Set.range (ambientCopy p f q false).base ≠ Set.range (ambientCopy p f q true).base := by
  intro h
  obtain ⟨c⟩ := ‹Nonempty C›
  have hx : (ambientCopy p f q false).base c ∈ Set.range (ambientCopy p f q false).base :=
    ⟨c, rfl⟩
  have hy : (ambientCopy p f q false).base c ∈ Set.range (ambientCopy p f q true).base :=
    h ▸ hx
  exact (Set.disjoint_left.mp (ambientCopy_disjoint p f q)) hx hy

/-- Both labels retain different actual ambient image sets. -/
theorem copy_images_injective :
    Function.Injective (fun ε : Bool => Set.range (ambientCopy p f q ε).base) := by
  intro ε ε' h
  cases ε <;> cases ε'
  · rfl
  · exact False.elim (copy_images_ne p f q h)
  · exact False.elim (copy_images_ne p f q h.symm)
  · rfl

/-- There are exactly two distinct whole-copy images in the original ambient cover. -/
theorem copy_images_ncard :
    (Set.range (fun ε : Bool => Set.range (ambientCopy p f q ε).base)).ncard = 2 := by
  rw [← Set.image_univ, Set.ncard_image_of_injective _ (copy_images_injective p f q)]
  simp only [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_bool]

end KltDP.Geometry.SplitAmbientPullbackCopyImageCount

#print axioms KltDP.Geometry.SplitAmbientPullbackCopyImageCount.copy_images_ncard
