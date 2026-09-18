import KltDP.Geometry.ProjectedLinePowerNumericalDescent
import KltDP.Geometry.BirationalNumericalProjectionCompatibility
import KltDP.Geometry.AmpleCartierNumericalSpan

/-!
# The linear rank conclusion from actual line-bundle descent data

This is an ordinary consumer of the explicit geometric output: each ample
source line has an actual correction line and an actual descended positive
power. It derives numerical surjectivity onto the exceptional orthogonal
space and the Picard-rank equality. The original geometric constructor must
supply the line data; no numerical descent or rank identity is an input.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.ActualExceptionalNumerical

open NefNullCurveNegativeSquare CanonicalAmpleSpan

variable {k : Type u} [Field k] [IsAlgClosed k] {S X : NormalProjectiveSurface k}
  [IsSmoothOfRelativeDimension 2 S.structureMorphism]
  (π : S.toScheme ⟶ X.toScheme) [IsProper π]
  (hπ : π ≫ X.structureMorphism = S.structureMorphism) (hbir : IsBirationalScheme π)

local instance actualLineDescentSourceSmooth : IsSmooth S.structureMorphism :=
  IsSmoothOfRelativeDimension.isSmooth 2 S.structureMorphism

variable (hdescent : ∀ H : InvertibleSheaf S.toScheme, AmpleSerre.IsAmple H →
  ∃ n m : ℕ, 0 < n ∧ 0 < m ∧
    ∃ L : InvertibleSheaf S.toScheme, ∃ A : InvertibleSheaf X.toScheme,
      ExceptionalAmpleProjection.lineClass S L =
        (n : ℚ) • ExceptionalAmpleProjection.originalProjectedClass π hbir
          (ExceptionalAmpleProjection.lineClass S H) ∧
      (pullbackInvertibleSheaf π A).toPic = L.toPic ^ m)

include hdescent hπ

/-- The actual descended powers on ample inputs supply the entire original
orthogonal subspace, by the proved ample spanning theorem. -/
theorem pullback_range_eq_orthogonal_of_actual_line_descent :
    LinearMap.range (BirationalNumericalPullback.pullback π hπ hbir) =
      exceptionalOrthogonal π := by
  apply le_antisymm (pullback_range_le_exceptionalOrthogonal π hπ hbir)
  have hspan : Submodule.span ℚ (ampleClasses S) ≤
      (LinearMap.range (BirationalNumericalPullback.pullback π hπ hbir)).comap
        (projection π hπ hbir S.regularPoints_of_isSmooth) := by
    apply Submodule.span_le.mpr
    rintro c ⟨D, hD, rfl⟩
    obtain ⟨n, m, hn, hm, L, A, hL, hpower⟩ :=
      hdescent (cartierDivisorInvertibleSheaf S.toScheme D) hD
    exact projection_mem_pullback_range_of_line_power π hπ hbir
      (cartierDivisorInvertibleSheaf S.toScheme D) L A n m hn hm hL hpower
  rw [span_ampleClasses_eq_top S S.regularPoints_of_isSmooth] at hspan
  intro c hc
  have h := hspan (show c ∈ (⊤ : Submodule ℚ S.NumericalClassGroup) from Submodule.mem_top)
  change projection π hπ hbir S.regularPoints_of_isSmooth c ∈
    LinearMap.range (BirationalNumericalPullback.pullback π hπ hbir) at h
  rwa [projection_eq_self π hπ hbir S.regularPoints_of_isSmooth c hc] at h

/-- The rank formula is a conclusion of the actual line data and original
exceptional classes, with their independence and finite count already derived. -/
theorem picardRank_eq_of_actual_line_descent :
    S.picardRank = X.picardRank + Nat.card (ActualExceptionalIncidence.Vertices π) := by
  have hdim : Module.finrank ℚ (exceptionalOrthogonal π) = X.picardRank := by
    rw [← pullback_range_eq_orthogonal_of_actual_line_descent π hπ hbir hdescent]
    exact LinearMap.finrank_range_of_inj (BirationalNumericalPullback.pullback_injective π hπ hbir)
  have h := exceptional_card_add_finrank_orthogonal π hπ hbir S.regularPoints_of_isSmooth
  rw [hdim] at h
  exact h.symm.trans (Nat.add_comm _ _)

end KltDP.Geometry.ActualExceptionalNumerical

#check @KltDP.Geometry.ActualExceptionalNumerical.pullback_range_eq_orthogonal_of_actual_line_descent
#check @KltDP.Geometry.ActualExceptionalNumerical.picardRank_eq_of_actual_line_descent
#print axioms KltDP.Geometry.ActualExceptionalNumerical.picardRank_eq_of_actual_line_descent
