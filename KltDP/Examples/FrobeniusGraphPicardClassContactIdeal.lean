import KltDP.Examples.FrobeniusGlobalStrictTransform
import KltDP.Examples.FrobeniusExceptionalCharts

/-!
# The original strict-transform ideal in the selected contact chart

Restrict the actual whole-projective-graph strict-transform ideal through
the original stage chart and its canonical section-ring isomorphisms.
Its equation is the existing residual polynomial. The original composite
blowdown therefore pulls the initial graph ideal to the product of this
actual strict-transform ideal and the required exceptional chart factors.

This is an equality of the actual ideals on the selected affine chart.
It does not assert a global ideal-sheaf tensor factorization or a class
formula for the strict transform outside that chart.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusGraphPicardClassContactIdeal

open KltDP.Geometry.AffineBlowup
open FrobeniusBlowupContact FrobeniusBlowupChartIteration
open FrobeniusGlobalBlowupStages FrobeniusStrictTransformClosure
open FrobeniusGlobalStrictTransform FrobeniusExceptionalCharts

variable {k : Type u} [Field k]

/-- The original global strict-transform ideal in the original stage coordinates. -/
def strictChartIdeal (n m : ℕ) : Ideal (planeRing k) :=
  (((strictTransformIdeal (k := k) n (m + n)).ideal
    ⟨((projectiveProductInitial (k := k)).stage n).chart ''ᵁ ⊤,
      (isAffineOpen_top (plane k)).image_of_isOpenImmersion _⟩).comap
        ((((projectiveProductInitial (k := k)).stage n).chart.appIso ⊤).inv.hom)).comap
          (Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv.hom

/-- The residual equation generates the restriction of the actual global ideal. -/
theorem strictChartIdeal_eq_span (n m : ℕ) :
    strictChartIdeal (k := k) n m = Ideal.span {vCoord - uCoord ^ m} := by
  unfold strictChartIdeal
  rw [strictTransformIdeal_eq_local,
    ← liftedGraphClosureIdeal_chart projectiveProductInitial n m
      ⟨⊤, isAffineOpen_top (plane k)⟩,
    Scheme.Hom.ker_apply]
  change RingHom.ker
    (((Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv ≫
      (curveInPlane m).appTop).hom) = _
  exact curveInPlane_coordinateKernel m

/-- The original extended-center ideal transported by the actual Rees chart equivalence. -/
def exceptionalChartIdeal : Ideal (planeRing k) :=
  Ideal.map (FrobeniusBlowupContact.chartPolynomialEquiv (k := k)).toRingHom
    (chartCenterIdeal centerIdeal centerU)

theorem exceptionalChartIdeal_eq_span :
    exceptionalChartIdeal (k := k) = Ideal.span {uCoord} :=
  polynomialModel_center centerU FrobeniusBlowupContact.chartPolynomialEquiv
    uChart_selected_equation

/-- Subsequent actual selected-chart blowdowns retain this exceptional ideal. -/
theorem exceptionalChartIdeal_map_stage (n : ℕ) :
    Ideal.map (stageSubstitution (k := k) n) exceptionalChartIdeal =
      exceptionalChartIdeal := by
  rw [exceptionalChartIdeal_eq_span, Ideal.map_span, Set.image_singleton,
    stageSubstitution_u]

/-- The actual initial graph ideal pulls back to the actual residual ideal
times the exceptional factors, on the original selected stage chart. -/
theorem strictChart_totalIdeal_factorization (n m : ℕ) :
    Ideal.map (stageSubstitution (k := k) n) (strictChartIdeal 0 (m + n)) =
      exceptionalChartIdeal ^ n * strictChartIdeal n m := by
  rw [strictChartIdeal_eq_span, strictChartIdeal_eq_span, exceptionalChartIdeal_eq_span,
    Ideal.map_span, Set.image_singleton, Ideal.span_singleton_pow,
    Ideal.span_singleton_mul_span_singleton, stageTotalEquation_factorization]

end KltDP.Examples.FrobeniusGraphPicardClassContactIdeal
