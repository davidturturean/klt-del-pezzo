import KltDP.Geometry.KltResolutionPicardRank
import KltDP.Geometry.ActualExceptionalNumericalComplement

/-! The original exceptional orthogonal complement has the original
target Picard rank. No constancy or rationality input is used. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S X : NormalProjectiveSurface k} {π : S.toScheme ⟶ X.toScheme}

/-- The exact original exceptional complement has the target Picard rank. -/
theorem IsMinimalResolution.finrank_exceptionalOrthogonal_eq_of_klt
    (hmin : IsMinimalResolution S X π) (hklt : IsKlt X)
    (p : ℕ) [CharP k p] (hp : 0 < p) :
    Module.finrank ℚ (ActualExceptionalNumerical.exceptionalOrthogonal π) = X.picardRank := by
  letI : IsProper π := hmin.toIsResolution.isProper
  have hbir : IsBirationalScheme π :=
    (isBirational_iff_isBirationalScheme π).mp hmin.birational
  have hsum := ActualExceptionalNumerical.exceptional_card_add_finrank_orthogonal
    π hmin.over_base hbir hmin.regular
  have hrank := hmin.picardRank_eq_of_klt hklt p hp
  omega

/-- Rank one of the original target gives a one-dimensional complement. -/
theorem IsMinimalResolution.finrank_exceptionalOrthogonal_eq_one_of_klt
    (hmin : IsMinimalResolution S X π) (hklt : IsKlt X)
    (p : ℕ) [CharP k p] (hp : 0 < p) (hrank : X.picardRank = 1) :
    Module.finrank ℚ (ActualExceptionalNumerical.exceptionalOrthogonal π) = 1 := by
  rw [hmin.finrank_exceptionalOrthogonal_eq_of_klt hklt p hp, hrank]

end KltDP.Geometry

#check @KltDP.Geometry.IsMinimalResolution.finrank_exceptionalOrthogonal_eq_one_of_klt
#print axioms KltDP.Geometry.IsMinimalResolution.finrank_exceptionalOrthogonal_eq_one_of_klt
