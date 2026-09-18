import KltDP.Geometry.IsolatedNodeCodeVanishing

/-! The original surface has an actual minimal resolution on which the
binary Picard code of all isolated exceptional nodes is the zero kernel. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry

/-- The minimal resolution and the literal vanishing code are both obtained
from the original rank-one klt del Pezzo surface. -/
theorem exists_minimalResolution_with_zero_isolatedNodePicardCode
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : NormalProjectiveSurface k) (hDP : IsKltDelPezzo X)
    (hrank : X.picardRank = 1) (p : ℕ) [CharP k p] (hp : 2 < p) :
    ∃ (S : NormalProjectiveSurface k) (π : S.toScheme ⟶ X.toScheme)
      (hmin : IsMinimalResolution S X π),
      selectedNodePicardCode π hmin (isolatedNodePrimes π hmin) = ⊥ := by
  obtain ⟨S, π, hmin⟩ := GeneralResolution.exists_minimalResolution X
  exact ⟨S, π, hmin, isolatedNodePicardCode_eq_bot π hmin hDP hrank p hp⟩

end KltDP.Geometry

#check @KltDP.Geometry.exists_minimalResolution_with_zero_isolatedNodePicardCode
#print axioms KltDP.Geometry.exists_minimalResolution_with_zero_isolatedNodePicardCode
