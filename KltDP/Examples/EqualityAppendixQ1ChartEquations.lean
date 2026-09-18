import KltDP.Examples.FrobeniusGraphPicardClassDiagonal
import KltDP.Examples.FrobeniusTranslatedCharts

/-!
# Original coordinate equations for the appendix curve Q₁

The equation is exactly `x²-y`, including its sign. The original graph
ideal has this generator in both diagonal charts. The actual translated
and Rees-chart ring maps give the residual equations and their values at
the next graph centre. Identification with the global strict-transform
ideal on the combined surface remains a separate geometric step.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.EqualityAppendixQ1ChartEquations

open FrobeniusBlowupContact FrobeniusBlowupChartIteration FrobeniusBlowupSmooth
  FrobeniusTranslatedCharts FrobeniusStrictTransformClosure
  FrobeniusGraphPicardClassCharts FrobeniusGraphPicardClassAffine
  FrobeniusGraphPicardClassDiagonal

variable {k : Type u} [Field k]

/-- The frozen manuscript's `Q₁` equation. -/
def equation : planeRing k := uCoord ^ 2 - vCoord

/-- The original graph ideal transported through an original diagonal chart. -/
def chartIdeal (i : Fin 2) : Ideal (planeRing k) :=
  (((graphIdeal (k := k) 2).ideal
    ⟨productChart i i ''ᵁ ⊤, (isAffineOpen_top (plane k)).image_of_isOpenImmersion _⟩).comap
      ((productChart i i).appIso ⊤).inv.hom).comap
        (Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv.hom

theorem chartIdeal_eq_span (i : Fin 2) :
    chartIdeal (k := k) i = Ideal.span {equation} := by
  unfold chartIdeal
  rw [← graphIdeal_diagonalChart 2 i ⟨⊤, isAffineOpen_top (plane k)⟩,
    Scheme.Hom.ker_apply]
  change RingHom.ker
    (((Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv ≫
      (curveInPlane 2).appTop).hom) = _
  rw [curveInPlane_coordinateKernel]
  change Ideal.span ({vCoord - uCoord ^ 2} : Set (planeRing k)) =
    Ideal.span ({uCoord ^ 2 - vCoord} : Set (planeRing k))
  rw [show (vCoord - uCoord ^ 2 : planeRing k) = -(uCoord ^ 2 - vCoord) from
    (neg_sub (uCoord ^ 2) vCoord).symm, Ideal.span_singleton_neg]

/-- First actual blowup at zero or infinity: one exceptional factor. -/
theorem first_substitution :
    chartSubstitution (equation (k := k)) = uCoord * (uCoord - vCoord) := by
  simp only [equation, map_sub, map_pow, chartSubstitution_u, chartSubstitution_v]
  ring

/-- Second actual selected blowup: one further exceptional factor. -/
theorem second_substitution :
    chartSubstitution (uCoord (k := k) - vCoord) = uCoord * (1 - vCoord) := by
  simp only [map_sub, chartSubstitution_u, chartSubstitution_v]
  ring

theorem second_residual_at_origin :
    originEvaluation (1 - vCoord : planeRing k) = 1 := by
  simp [originEvaluation, vCoord]

variable [CharP k 3]

/-- The original translated chart at `(1,1)` has this literal equation. -/
theorem translated_at_one :
    coordinateTranslation (1 : k) 1 equation = uCoord ^ 2 - uCoord - vCoord := by
  rw [equation, map_sub, map_pow, coordinateTranslation_u, coordinateTranslation_v]
  simp only [map_one]
  have h3 : (3 : planeRing k) = 0 := CharP.cast_eq_zero (planeRing k) 3
  calc
    _ = (uCoord ^ 2 - uCoord - vCoord) + 3 * uCoord := by ring
    _ = _ := by rw [h3, zero_mul, add_zero]

/-- At one, the first selected blowup supplies the only exceptional factor. -/
theorem translated_first_substitution :
    chartSubstitution (coordinateTranslation (1 : k) 1 equation) =
      uCoord * (uCoord - 1 - vCoord) := by
  rw [translated_at_one]
  simp only [map_sub, map_pow, chartSubstitution_u, chartSubstitution_v]
  ring

theorem translated_residual_at_origin :
    originEvaluation (uCoord - 1 - vCoord : planeRing k) = -1 := by
  simp [originEvaluation, uCoord, vCoord]

end KltDP.Examples.EqualityAppendixQ1ChartEquations
