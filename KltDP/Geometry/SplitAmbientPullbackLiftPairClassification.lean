import KltDP.Geometry.SplitAmbientPullbackLiftClassification

/-!
# Two disjoint original lifts are the two complementary actual split copies

The existing generic-point classification identifies each original lift
with one actual split copy. Their actual disjointness and the nonempty
integral source force distinct labels. This recovers the opposite label
for coherent whole-tree lifts without supplying any map comparison.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

namespace KltDP.Geometry.SplitAmbientPullbackLiftClassification

open SplitAmbientPullbackCopies

variable {X Z C : Scheme.{u}} [IsIntegral C]
    (p : Z ⟶ X) (f : C ⟶ X) (q : pullback p f ≅ C ⨿ C)
    (hq : q.hom ≫ coprod.desc (𝟙 C) (𝟙 C) = pullback.snd p f)

include hq in
/-- Actual disjoint lifts of the same integral curve are exactly the two complementary copies. -/
theorem eq_complementary_ambientCopies_of_projection
    (g₀ g₁ : C ⟶ Z) (hg₀ : g₀ ≫ p = f) (hg₁ : g₁ ≫ p = f)
    (hdisj : Disjoint (Set.range g₀.base) (Set.range g₁.base)) :
    ∃ ε : Bool, g₀ = ambientCopy p f q ε ∧ g₁ = ambientCopy p f q (!ε) := by
  obtain ⟨ε, rfl⟩ := eq_ambientCopy_of_projection p f q hq g₀ hg₀
  obtain ⟨δ, rfl⟩ := eq_ambientCopy_of_projection p f q hq g₁ hg₁
  have hne : ε ≠ δ := by
    intro h
    subst δ
    have hx : (ambientCopy p f q ε).base (genericPoint C) ∈
        Set.range (ambientCopy p f q ε).base := ⟨genericPoint C, rfl⟩
    exact Set.disjoint_left.mp hdisj hx hx
  have hδ : δ = !ε := by
    cases ε <;> cases δ <;> first | rfl | exact False.elim (hne rfl)
  exact ⟨ε, rfl, by rw [hδ]⟩

end KltDP.Geometry.SplitAmbientPullbackLiftClassification

#print axioms KltDP.Geometry.SplitAmbientPullbackLiftClassification.eq_complementary_ambientCopies_of_projection
