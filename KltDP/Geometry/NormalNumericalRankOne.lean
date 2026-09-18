import KltDP.Geometry.NormalRationalPicardWeil
import KltDP.Geometry.NumericalSpaceRank

/-!
A rational Weil-class spanning proof and one nonzero original curve
degree imply rank one for the original numerical Picard quotient.
Both finite dimensionality and the numerical rank are concluded.
-/

noncomputable section

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)

/-- Descend the proved spanning statement through the original numerical
quotient, without assuming a regular target. -/
theorem numericalClass_span_of_weilClass_span
    (p : Additive X.toScheme.Pic)
    (hspan : ∀ w : X.RationalWeilClassGroup, ∃ q : ℚ,
      w = q • X.weilClassRationalization (X.picardToWeilClassHom p))
    (c : X.NumericalClassGroup) :
    ∃ q : ℚ, c = q • X.picardNumericalMap p := by
  obtain ⟨v, rfl⟩ := X.rationalPicardNumericalMap_surjective c
  obtain ⟨q, rfl⟩ := X.rationalPicard_span_of_weilClass_span p hspan v
  exact ⟨q, X.rationalPicardNumericalMap.map_smul q (X.picardTensorInclusion p)⟩

/-- This criterion concludes the actual numerical Picard rank and its
finite-dimensionality from a proved span and an original nonzero degree. -/
theorem numericalRankOne_of_weilClass_span
    (p : Additive X.toScheme.Pic)
    (hspan : ∀ w : X.RationalWeilClassGroup, ∃ q : ℚ,
      w = q • X.weilClassRationalization (X.picardToWeilClassHom p))
    (C : X.PrimeCurve) (hdegree : C.picardRestrictionDegree p.toMul ≠ 0) :
    X.NumericalSpaceFiniteDimensional ∧ X.picardRank = 1 := by
  have hp : X.picardNumericalMap p ≠ 0 := by
    intro hzero
    have hd := congrArg (X.numericalRestrictionDegree C) hzero
    rw [X.numericalRestrictionDegree_picardNumericalMap, map_zero] at hd
    exact hdegree (Int.cast_injective hd)
  have hrank : Module.finrank ℚ X.NumericalClassGroup = 1 := by
    apply (finrank_eq_one_iff_of_nonzero' (X.picardNumericalMap p) hp).mpr
    intro c
    obtain ⟨q, hq⟩ := X.numericalClass_span_of_weilClass_span p hspan c
    exact ⟨q, hq.symm⟩
  exact ⟨FiniteDimensional.of_finrank_eq_succ hrank, hrank⟩

end KltDP.Geometry.NormalProjectiveSurface
