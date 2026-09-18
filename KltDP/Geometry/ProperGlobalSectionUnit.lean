import KltDP.Geometry.ProperGlobalSectionsConstants

/-! # Nonzero global coefficients on an original proper integral scheme are units -/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.ProperGlobalSectionUnit

/-- The original scalar map, rather than a replacement field structure,
proves invertibility of each nonzero global coefficient. -/
theorem isUnit_of_ne_zero {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} [IsIntegral C] (sC : C ⟶ Spec (CommRingCat.of k))
    [UniversallyClosed sC] [LocallyOfFiniteType sC]
    (a : Γ(C, ⊤)) (ha : a ≠ 0) : IsUnit a := by
  obtain ⟨b, rfl⟩ := (baseFieldToGlobalSections_bijective sC).surjective a
  have hb : b ≠ 0 := by
    intro hb
    apply ha
    rw [hb, map_zero]
  exact (isUnit_iff_ne_zero.mpr hb).map (baseFieldToGlobalSections sC)

end KltDP.Geometry.ProperGlobalSectionUnit
