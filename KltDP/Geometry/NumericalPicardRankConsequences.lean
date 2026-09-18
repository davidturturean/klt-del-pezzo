import KltDP.Geometry.RationalHodgeIndexProved
import KltDP.Geometry.SurfaceNumericalFinitenessProved
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Consequences for the original Picard rank

A nonzero value of the existing `picardRank` forces finite dimensionality of
its original rational numerical quotient, over any field and without assuming
regularity. In particular the manuscript's rank-one hypothesis already carries
that finiteness consequence.

For a regular surface over an algebraically closed field, the separately proved
numerical finiteness and the actual positive Hodge direction give positive
Picard rank. The regular-surface source is used only in this second result.
-/

noncomputable section

open AlgebraicGeometry

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-- Nonzero original Picard rank implies finite dimensionality of the original
numerical quotient, for every normal projective surface over any field. -/
theorem numericalSpaceFiniteDimensional_of_picardRank_ne_zero
    (hρ : X.picardRank ≠ 0) : X.NumericalSpaceFiniteDimensional :=
  FiniteDimensional.of_finrank_pos (Nat.pos_of_ne_zero hρ)

/-- The original rank-one hypothesis itself supplies numerical finite dimension. -/
theorem numericalSpaceFiniteDimensional_of_picardRank_eq_one
    (hρ : X.picardRank = 1) : X.NumericalSpaceFiniteDimensional := by
  apply X.numericalSpaceFiniteDimensional_of_picardRank_ne_zero
  rw [hρ]
  exact one_ne_zero

/-- Every regular normal projective surface over an algebraically closed field
has positive original Picard rank. -/
theorem picardRank_pos_of_regular [IsAlgClosed k]
    (hregular : ∀ x : X.Point, RegularPoint X.toScheme x) : 0 < X.picardRank := by
  letI : FiniteDimensional ℚ X.NumericalClassGroup :=
    SurfaceNumericalFinitenessProved.numericalClassGroup_finite X hregular
  obtain ⟨h, hpos, _⟩ := RationalHodgeIndexProved.signature X hregular
  change 0 < Module.finrank ℚ X.NumericalClassGroup
  apply (Module.finrank_pos_iff_exists_ne_zero (R := ℚ) (M := X.NumericalClassGroup)).mpr
  refine ⟨h, ?_⟩
  intro hzero
  have hpair : X.numericalIntersectionBilinForm hregular h h = 0 := by
    rw [hzero]
    exact map_zero _
  exact (ne_of_gt hpos) hpair

end KltDP.Geometry.NormalProjectiveSurface
