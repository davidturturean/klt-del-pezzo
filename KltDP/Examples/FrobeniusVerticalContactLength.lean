import KltDP.Examples.FrobeniusVerticalFibreCrossing
import KltDP.Examples.FrobeniusGraphStalkContact
import KltDP.Examples.FrobeniusStrictTransformIsoProjectiveLine
import KltDP.Examples.FrobeniusFiberClosure
import KltDP.Geometry.SurfaceRegularCharts

/-!
# The crossing point of `B` with a vertical ruling fibre, and the `P¹` stalk there (BRIEF24, item 1)

BRIEF22 proved that `B_n ∩ (x = c)` is a subsingleton but never produced the point; a length statement
needs an actual point. This module supplies it, together with the stalk identification that the
length computation consumes.

* **`polynomialLineChart_point`**: the accepted polynomial chart of `P¹` sends the parameter point
  `t = c` to the rational point `[1:c]`. Proof exactly as the accepted
  `polynomialGraphChart_evaluation_inclusion`: `polynomialLineChart_eq`,
  `parameterEvaluation_via_polynomial`, `parameterMorphism_evaluation` at `p = 1` (`pow_one`), and
  `polynomialEvaluation_point`.
* **`lineStalkLocalEquiv`**: the stalk of `P¹` at that point is the accepted `parameterLocalRing c`
  (the accepted `openImmersionStalkLocalizationEquiv` on `polynomialLineChart`). This is the `P¹`
  analogue of the accepted `graphStalkLocalEquiv`, which did not exist.
* **`verticalCrossingPoint`**: the point of `B_n` over the parameter point `t = c`, via the accepted
  `graphStrictIsoProjectiveLine`, indexed by the chart point so that it is *definitionally* the
  `crossingPoint` used by the germ side — one index, no transport;
  **`verticalCrossingPoint_toInitial`** computes its image downstairs
  as `projectiveGraphMorphism (m + n)` applied to `[1:c]` (accepted
  `graphStrictIsoProjectiveLine_hom_comp`);
* **`verticalCrossingPoint_mem_stagePuncture`**: for `c ≠ 0` that point lies in the stage puncture,
  because its first coordinate is `[1:c]` while the centre's is `[1:0]` (BRIEF22's
  `originCenter_fst`). So lane A2's `towerStalkEquiv` applies at the crossing point.

**Not proved here**: the germ identification and the length itself; see the record.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusVerticalContactLength

open KltDP.Geometry
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism FrobeniusGraphClosed
open FrobeniusGraphContact FrobeniusGraphStalkContact
open FrobeniusGlobalBlowupStages FrobeniusGlobalStrictTransform
open FrobeniusStrictTransformIsoProjectiveLine
open FrobeniusStageComplement FrobeniusStageComplement.PlaneChartedScheme
open FrobeniusFiberClosure FrobeniusVerticalFibreCrossing

variable {k : Type u} [Field k]

/-- **The polynomial chart of `P¹` sends the parameter point `t = c` to `[1:c]`.** -/
theorem polynomialLineChart_point (c : k) :
    (polynomialLineChart (k := k)).base (parameterSchemePoint c) = point c := by
  have h : parameterPolynomialEquiv.toRingEquiv.toCommRingCatIso.hom ≫
      CommRingCat.ofHom (Polynomial.evalRingHom c) =
        CommRingCat.ofHom (parameterEvaluation c) :=
    CommRingCat.hom_ext (parameterEvaluation_via_polynomial c)
  rw [← polynomialEvaluation_point c, ← fieldMorphismPoint_comp, polynomialLineChart_eq,
    ← Category.assoc, ← Spec.map_comp, h, parameterMorphism_evaluation, pow_one]
  rfl

/-- **The stalk of `P¹` at the parameter point is the accepted local ring `k[t]_(t-c)`** — the `P¹`
analogue of the accepted `graphStalkLocalEquiv`. -/
def lineStalkLocalEquiv (c : k) :
    (projectiveSpace k 1).presheaf.stalk
        ((polynomialLineChart (k := k)).base (parameterSchemePoint c)) ≃+*
      parameterLocalRing c :=
  openImmersionStalkLocalizationEquiv polynomialLineChart (parameterSchemePoint c)

section Crossing

variable (n m : ℕ)

/-- **The crossing point of `B_n` with the vertical ruling fibre `x = c`**: the point of the strict
transform over the parameter point `t = c`.

Indexed by the **chart** point `polynomialLineChart.base (parameterSchemePoint c)` rather than by
`point c`, so that it is *definitionally* the `crossingPoint` of `FrobeniusVerticalContactStalk`
(whose index `lineParamPoint c` is an `abbrev` for the same term). The two sides of the development
therefore share one index, and no stalk is ever transported along the propositional point equality
`polynomialLineChart_point`. That equality is still used below, but only to rewrite **points inside a
`Prop`**, which moves no type. -/
def verticalCrossingPoint (c : k) : strictTransform (k := k) n (m + n) :=
  (graphStrictIsoProjectiveLine (k := k) n m).inv.base
    ((polynomialLineChart (k := k)).base (parameterSchemePoint c))

/-- Its image under the blowdown is the graph point over the parameter point. -/
theorem verticalCrossingPoint_toInitial (c : k) :
    ((projectiveProductInitial (k := k)).toInitial n).base
        ((strictTransformι (k := k) n (m + n)).base (verticalCrossingPoint n m c)) =
      (projectiveGraphMorphism (k := k) (m + n)).base
        ((polynomialLineChart (k := k)).base (parameterSchemePoint c)) := by
  change (strictTransformι (k := k) n (m + n) ≫ projectiveContactProjection n).base
    (verticalCrossingPoint n m c) = _
  -- `hpt` must be stated about the folded `verticalCrossingPoint n m c`: it is a `def`, and `rw`
  -- never sees its unfolding.
  have hpt : (graphStrictIsoProjectiveLine (k := k) n m).hom.base
      (verticalCrossingPoint n m c) =
        (polynomialLineChart (k := k)).base (parameterSchemePoint c) := by
    change (graphStrictIsoProjectiveLine (k := k) n m).hom.base
      ((graphStrictIsoProjectiveLine (k := k) n m).inv.base
        ((polynomialLineChart (k := k)).base (parameterSchemePoint c))) = _
    rw [← Scheme.comp_base_apply, Iso.inv_hom_id]
    rfl
  rw [← graphStrictIsoProjectiveLine_hom_comp n m, Scheme.comp_base_apply, hpt]

variable [IsAlgClosed k]

/-- **The crossing point lies in the stage puncture** when `c ≠ 0`: its first coordinate is `[1:c]`,
the centre's is `[1:0]`. Hence lane A2's `towerStalkEquiv` applies there. -/
theorem verticalCrossingPoint_mem_stagePuncture (c : k) (hc : c ≠ 0) :
    (strictTransformι (k := k) n (m + n)).base (verticalCrossingPoint n m c) ∈
      stagePuncture (projectiveProductInitial (k := k)) n := by
  change ((projectiveProductInitial (k := k)).toInitial n).base _ ≠
    (projectiveProductInitial (k := k)).chart.base (FrobeniusBlowupChartIteration.originPoint)
  rw [verticalCrossingPoint_toInitial, polynomialLineChart_point]
  intro h
  apply hc
  apply point_injective
  have h1 : (firstProjection (k := k)).base
      ((projectiveGraphMorphism (k := k) (m + n)).base (point c)) = point c := by
    change (projectiveGraphMorphism (k := k) (m + n) ≫ firstProjection).base (point c) = point c
    rw [projectiveGraphMorphism_fst]
    rfl
  rw [h, originCenter_fst] at h1
  exact h1.symm

end Crossing

end KltDP.Examples.FrobeniusVerticalContactLength

namespace KltDP.Examples

open KltDP.Geometry FrobeniusProjectivePoints FrobeniusProjectiveMorphism
  FrobeniusGraphStalkContact
  FrobeniusGlobalBlowupStages FrobeniusGlobalStrictTransform FrobeniusStageComplement
  FrobeniusStageComplement.PlaneChartedScheme FrobeniusVerticalContactLength

/-- **F29: the crossing point of `B` with a vertical ruling fibre**, with its image downstairs and
its membership in the stage puncture, so that the stalk transport applies there. -/
theorem f29_vertical_crossing_point (k : Type u) [Field k] [IsAlgClosed k] (n m : ℕ) (c : k)
    (hc : c ≠ 0) :
    ((projectiveProductInitial (k := k)).toInitial n).base
        ((strictTransformι (k := k) n (m + n)).base (verticalCrossingPoint n m c)) =
      (projectiveGraphMorphism (k := k) (m + n)).base
        ((polynomialLineChart (k := k)).base (parameterSchemePoint c)) ∧
    (strictTransformι (k := k) n (m + n)).base (verticalCrossingPoint n m c) ∈
      stagePuncture (projectiveProductInitial (k := k)) n :=
  ⟨verticalCrossingPoint_toInitial n m c, verticalCrossingPoint_mem_stagePuncture n m c hc⟩

/-- The bundle has exactly one universe parameter. -/
theorem f29_vertical_crossing_point_universe_check (k : Type u) [Field k] [IsAlgClosed k]
    (n m : ℕ) (c : k) (hc : c ≠ 0) : True := by
  have _ := f29_vertical_crossing_point.{u} k n m c hc
  trivial

end KltDP.Examples
