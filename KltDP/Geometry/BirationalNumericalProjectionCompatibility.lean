import KltDP.Geometry.ActualExceptionalNumericalProjection
import KltDP.Geometry.BirationalNumericalPullback

/-!
# The actual pullback image inside the exceptional orthogonal subspace

The actual target pullback injects into the proved numerical complement and
is fixed by the original projection. Its disjointness from the exceptional
span gives the lower Picard-rank inequality with the full target rank.
Surjectivity onto the complement remains the geometric descent obligation.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.ActualExceptionalNumerical

variable {k : Type u} [Field k] [IsAlgClosed k] {S X : NormalProjectiveSurface k}
  (π : S.toScheme ⟶ X.toScheme) [IsProper π]
  (hπ : π ≫ X.structureMorphism = S.structureMorphism) (hbir : IsBirationalScheme π)

include hπ hbir

theorem pullback_range_le_exceptionalOrthogonal :
    LinearMap.range (BirationalNumericalPullback.pullback π hπ hbir) ≤
      exceptionalOrthogonal π := by
  rintro c ⟨d, rfl⟩
  apply (mem_exceptionalOrthogonal_iff π _).mpr
  intro C
  exact BirationalNumericalPullback.degree_pullback_exceptional π hπ hbir C.val C.property d

variable (hregular : ∀ x : S.Point, RegularPoint S.toScheme x)
include hregular

theorem projection_pullback (c : X.NumericalClassGroup) :
    projection π hπ hbir hregular (BirationalNumericalPullback.pullback π hπ hbir c) =
      BirationalNumericalPullback.pullback π hπ hbir c :=
  projection_eq_self π hπ hbir hregular _
    (pullback_range_le_exceptionalOrthogonal π hπ hbir ⟨c, rfl⟩)

theorem disjoint_exceptionalSpan_pullback_range :
    Disjoint (exceptionalSpan π hregular)
      (LinearMap.range (BirationalNumericalPullback.pullback π hπ hbir)) :=
  (disjoint_exceptionalSpan_orthogonal π hπ hbir hregular).mono_right
    (pullback_range_le_exceptionalOrthogonal π hπ hbir)

/-- Original exceptional curves and the whole target numerical space contribute
independent numerical directions on the actual regular source. -/
theorem exceptional_card_add_picardRank_le :
    Nat.card (ActualExceptionalIncidence.Vertices π) + X.picardRank ≤ S.picardRank := by
  letI : FiniteDimensional ℚ S.NumericalClassGroup :=
    SurfaceNumericalFinitenessProved.numericalSpaceFiniteDimensional S hregular
  have hle : X.picardRank ≤ Module.finrank ℚ (exceptionalOrthogonal π) := by
    change Module.finrank ℚ X.NumericalClassGroup ≤ _
    rw [← LinearMap.finrank_range_of_inj (BirationalNumericalPullback.pullback_injective π hπ hbir)]
    exact Submodule.finrank_mono (pullback_range_le_exceptionalOrthogonal π hπ hbir)
  calc
    Nat.card (ActualExceptionalIncidence.Vertices π) + X.picardRank ≤
        Nat.card (ActualExceptionalIncidence.Vertices π) +
          Module.finrank ℚ (exceptionalOrthogonal π) := Nat.add_le_add_left hle _
    _ = S.picardRank := exceptional_card_add_finrank_orthogonal π hπ hbir hregular

end KltDP.Geometry.ActualExceptionalNumerical

#check @KltDP.Geometry.ActualExceptionalNumerical.pullback_range_le_exceptionalOrthogonal
#check @KltDP.Geometry.ActualExceptionalNumerical.exceptional_card_add_picardRank_le
#print axioms KltDP.Geometry.ActualExceptionalNumerical.projection_pullback
#print axioms KltDP.Geometry.ActualExceptionalNumerical.exceptional_card_add_picardRank_le
