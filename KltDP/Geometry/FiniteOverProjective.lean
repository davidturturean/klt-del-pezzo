import KltDP.Geometry.FiniteProjectiveTupleClosedImmersion

/-! Projectivity through an original finite map, retaining the original field map. -/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry

/-- A finite scheme over an actual projective scheme is projective over the
same field. The closed embedding is constructed from the original finite map. -/
theorem IsProjectiveOverField.comp_isFinite
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (π : X ⟶ Y) [IsFinite π] (σ : Y ⟶ Spec (CommRingCat.of k))
    (hσ : IsProjectiveOverField σ) : IsProjectiveOverField (π ≫ σ) := by
  obtain ⟨n, i, hi, hfield⟩ := hσ
  letI : IsClosedImmersion i := hi
  rw [← hfield]
  exact FiniteProjectiveTupleClosedImmersion.isProjectiveOverField π i

end KltDP.Geometry
