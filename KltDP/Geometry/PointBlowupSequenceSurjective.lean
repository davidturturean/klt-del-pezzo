import KltDP.Geometry.SurfacePointBlowupSequenceBirational
import KltDP.Geometry.ProperGenericPointSurjective

/-! The actual point-blowup composite is surjective on original points. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry

/-- Properness and the unchanged generic point prove surjectivity of the
original composite, without a supplied point-lifting hypothesis. -/
theorem IsPointBlowupSequence.surjective_base
    {k : Type u} [Field k] {S T : NormalProjectiveSurface k}
    {b : S.toScheme ⟶ T.toScheme} (hb : IsPointBlowupSequence S T b) :
    Function.Surjective b.base := by
  letI : IsIntegral S.toScheme := S.integral
  letI : IsIntegral T.toScheme := T.integral
  letI : IsProper b := hb.isProper
  letI : GenericPointPreserving b := ⟨hb.isBirationalScheme.map_genericPoint⟩
  obtain ⟨h⟩ := surjective_of_proper_genericPointPreserving b
  exact h

end KltDP.Geometry

#print axioms KltDP.Geometry.IsPointBlowupSequence.surjective_base
