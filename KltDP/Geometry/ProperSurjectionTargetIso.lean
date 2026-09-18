import KltDP.Geometry.SchemeMorphismDescent

/-!
# Target identification through actual proper quotient morphisms

The original point fibers and original pushforward structure-sheaf maps
determine the target. The inverse scheme maps are produced by the proved
descent theorem, with both original triangles retained.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.ProperSurjectionTargetIso

/-- A proper surjection whose original pushforward-O map is an isomorphism
cancels on the left against arbitrary original scheme morphisms. -/
theorem cancel_left {S X Z : Scheme.{u}} (π : S ⟶ X)
    [IsProper π] [Surjective π] [IsIso π.c]
    (g h : X ⟶ Z) (heq : π ≫ g = π ≫ h) : g = h := by
  have hfactors : Function.FactorsThrough (π ≫ g).base π.base := by
    intro x y hxy
    change g.base (π.base x) = g.base (π.base y)
    exact congrArg g.base hxy
  obtain ⟨q, _, hq⟩ :=
    SchemeMorphismDescent.existsUnique_lift_of_proper π (π ≫ g) hfactors
  exact (hq g rfl).trans (hq h heq.symm).symm

/-- The original targets are isomorphic when their actual quotient maps
have the same point fibers. No inverse morphism is an input. -/
theorem exists_iso_of_mutual_factors
    {S X Y : Scheme.{u}} (π : S ⟶ X) (f : S ⟶ Y)
    [IsProper π] [Surjective π] [IsIso π.c]
    [IsProper f] [Surjective f] [IsIso f.c]
    (hfπ : Function.FactorsThrough f.base π.base)
    (hπf : Function.FactorsThrough π.base f.base) :
    ∃ e : X ≅ Y, π ≫ e.hom = f ∧ f ≫ e.inv = π := by
  obtain ⟨g, hg, _⟩ := SchemeMorphismDescent.existsUnique_lift_of_proper π f hfπ
  obtain ⟨h, hh, _⟩ := SchemeMorphismDescent.existsUnique_lift_of_proper f π hπf
  have hgh : g ≫ h = 𝟙 X := by
    apply cancel_left π
    simpa only [← Category.assoc, hg, hh, Category.comp_id]
  have hhg : h ≫ g = 𝟙 Y := by
    apply cancel_left f
    simpa only [← Category.assoc, hh, hg, Category.comp_id]
  exact ⟨⟨g, h, hgh, hhg⟩, hg, hh⟩

/-- If the original morphisms are over the same base, the constructed
target isomorphism is over that base too. -/
theorem exists_iso_over_of_mutual_factors
    {S X Y B : Scheme.{u}} (π : S ⟶ X) (f : S ⟶ Y)
    [IsProper π] [Surjective π] [IsIso π.c]
    [IsProper f] [Surjective f] [IsIso f.c]
    (σS : S ⟶ B) (σX : X ⟶ B) (σY : Y ⟶ B)
    (hπ : π ≫ σX = σS) (hf : f ≫ σY = σS)
    (hfπ : Function.FactorsThrough f.base π.base)
    (hπf : Function.FactorsThrough π.base f.base) :
    ∃ e : X ≅ Y, π ≫ e.hom = f ∧ f ≫ e.inv = π ∧ e.hom ≫ σY = σX := by
  obtain ⟨e, he, hi⟩ := exists_iso_of_mutual_factors π f hfπ hπf
  refine ⟨e, he, hi, ?_⟩
  apply cancel_left π
  calc
    π ≫ (e.hom ≫ σY) = (π ≫ e.hom) ≫ σY := (Category.assoc _ _ _).symm
    _ = f ≫ σY := by rw [he]
    _ = σS := hf
    _ = π ≫ σX := hπ.symm

end KltDP.Geometry.ProperSurjectionTargetIso
#print axioms KltDP.Geometry.ProperSurjectionTargetIso.cancel_left
#print axioms KltDP.Geometry.ProperSurjectionTargetIso.exists_iso_of_mutual_factors
#print axioms KltDP.Geometry.ProperSurjectionTargetIso.exists_iso_over_of_mutual_factors
