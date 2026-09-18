import KltDP.Geometry.ActualExceptionalNegativeDefinite
import KltDP.Geometry.ActualExceptionalIncidence
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The actual exceptional numerical span and its complement

The original exceptional prime classes span a negative definite subspace.
Their original degree tests define its orthogonal complement. The existing
Hodge argument and finite-dimensional bilinear-form API give a direct sum,
with the exceptional summand's dimension equal to the actual prime count.
No numerical descent or target Picard-rank equality is an input.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.ActualExceptionalNumerical

open DisjointNegativeCurvesRank

variable {k : Type u} [Field k] [IsAlgClosed k] {S X : NormalProjectiveSurface k}
  (π : S.toScheme ⟶ X.toScheme)

/-- The span of the original exceptional prime Cartier numerical classes. -/
def exceptionalSpan (hregular : ∀ x : S.Point, RegularPoint S.toScheme x) :
    Submodule ℚ S.NumericalClassGroup :=
  Submodule.span ℚ (Set.range (fun C : ActualExceptionalIncidence.Vertices π =>
    curveClass S hregular C.val))

/-- The simultaneous kernel of all original exceptional curve degree tests. -/
def exceptionalOrthogonal : Submodule ℚ S.NumericalClassGroup :=
  ⨅ C : ActualExceptionalIncidence.Vertices π, LinearMap.ker (S.numericalRestrictionDegree C.val)

theorem mem_exceptionalOrthogonal_iff (v : S.NumericalClassGroup) :
    v ∈ exceptionalOrthogonal π ↔
      ∀ C : ActualExceptionalIncidence.Vertices π, S.numericalRestrictionDegree C.val v = 0 := by
  simp only [exceptionalOrthogonal, Submodule.mem_iInf, LinearMap.mem_ker]

theorem orthogonal_exceptionalSpan
    (hregular : ∀ x : S.Point, RegularPoint S.toScheme x) :
    (S.numericalIntersectionBilinForm hregular).orthogonal (exceptionalSpan π hregular) =
      exceptionalOrthogonal π := by
  ext v
  rw [LinearMap.BilinForm.mem_orthogonal_iff, mem_exceptionalOrthogonal_iff]
  constructor
  · intro h C
    have hz := h (curveClass S hregular C.val) (Submodule.subset_span ⟨C, rfl⟩)
    change S.numericalIntersectionBilinForm hregular (curveClass S hregular C.val) v = 0 at hz
    rw [LinearMap.BilinForm.IsSymm.eq (S.numericalIntersectionBilinForm_isSymm hregular),
      pairing_curveClass] at hz
    exact hz
  · intro h w hw
    have hk : exceptionalSpan π hregular ≤
        LinearMap.ker (S.numericalIntersectionBilinForm hregular v) := by
      apply Submodule.span_le.mpr
      rintro c ⟨C, rfl⟩
      change S.numericalIntersectionBilinForm hregular v (curveClass S hregular C.val) = 0
      rw [pairing_curveClass]
      exact h C
    change S.numericalIntersectionBilinForm hregular w v = 0
    rw [LinearMap.BilinForm.IsSymm.eq (S.numericalIntersectionBilinForm_isSymm hregular)]
    exact hk hw

variable [IsProper π] (hπ : π ≫ X.structureMorphism = S.structureMorphism)
  (hbir : IsBirationalScheme π)
  (hregular : ∀ x : S.Point, RegularPoint S.toScheme x)

include hπ hbir hregular

theorem exceptionalSpan_square_neg (v : S.NumericalClassGroup)
    (hv : v ∈ exceptionalSpan π hregular) (hne : v ≠ 0) :
    S.numericalIntersectionBilinForm hregular v v < 0 := by
  obtain ⟨H, hH, hnull⟩ :=
    ActualExceptionalNegativeDefinite.exists_positive_square_orthogonal_divisor π hπ hbir hregular
  exact NullCurveNumericalSpan.square_neg_on_span S hregular H hH
    (fun C : ActualExceptionalIncidence.Vertices π => C.val)
    (fun C => hnull C.val C.property) v hv hne

theorem disjoint_exceptionalSpan_orthogonal :
    Disjoint (exceptionalSpan π hregular) (exceptionalOrthogonal π) := by
  apply disjoint_iff.mpr
  apply le_antisymm
  · intro v hv
    change v = 0
    by_contra hne
    have hneg := exceptionalSpan_square_neg π hπ hbir hregular v hv.1 hne
    have horth : v ∈ (S.numericalIntersectionBilinForm hregular).orthogonal
        (exceptionalSpan π hregular) := by
      rw [orthogonal_exceptionalSpan]
      exact hv.2
    exact (ne_of_lt hneg) (horth v hv.1)
  · exact bot_le

theorem isCompl_exceptionalSpan_orthogonal :
    IsCompl (exceptionalSpan π hregular) (exceptionalOrthogonal π) := by
  letI : FiniteDimensional ℚ S.NumericalClassGroup :=
    SurfaceNumericalFinitenessProved.numericalSpaceFiniteDimensional S hregular
  rw [← orthogonal_exceptionalSpan π hregular]
  apply (LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint
    (S.numericalIntersectionBilinForm_isSymm hregular).isRefl).mpr
  rw [orthogonal_exceptionalSpan]
  exact disjoint_exceptionalSpan_orthogonal π hπ hbir hregular

theorem finrank_exceptionalSpan :
    Module.finrank ℚ (exceptionalSpan π hregular) =
      Nat.card (ActualExceptionalIncidence.Vertices π) := by
  letI : Fintype (ActualExceptionalIncidence.Vertices π) :=
    (exceptionalCurves_finite_of_proper_birational π hbir).fintype
  simpa only [Nat.card_eq_fintype_card] using
    finrank_span_eq_card (ActualExceptionalNegativeDefinite.linearIndependent π hπ hbir hregular)

theorem exceptional_card_add_finrank_orthogonal :
    Nat.card (ActualExceptionalIncidence.Vertices π) +
      Module.finrank ℚ (exceptionalOrthogonal π) = S.picardRank := by
  letI : FiniteDimensional ℚ S.NumericalClassGroup :=
    SurfaceNumericalFinitenessProved.numericalSpaceFiniteDimensional S hregular
  have h := LinearMap.BilinForm.finrank_add_finrank_orthogonal
    (S.numericalIntersectionBilinForm_isSymm hregular).isRefl (exceptionalSpan π hregular)
  rw [orthogonal_exceptionalSpan,
    LinearMap.BilinForm.orthogonal_top_eq_bot
      (S.numericalIntersectionBilinForm_nondegenerate hregular)
      (S.numericalIntersectionBilinForm_isSymm hregular).isRefl,
    inf_bot_eq, _root_.finrank_bot, add_zero,
    finrank_exceptionalSpan π hπ hbir hregular] at h
  exact h

end KltDP.Geometry.ActualExceptionalNumerical

#check @KltDP.Geometry.ActualExceptionalNumerical.isCompl_exceptionalSpan_orthogonal
#check @KltDP.Geometry.ActualExceptionalNumerical.exceptional_card_add_finrank_orthogonal
#print axioms KltDP.Geometry.ActualExceptionalNumerical.isCompl_exceptionalSpan_orthogonal
#print axioms KltDP.Geometry.ActualExceptionalNumerical.exceptional_card_add_finrank_orthogonal
