import KltDP.Geometry.ProjectiveLineCanonicalFrame
import KltDP.Geometry.ProjectiveLineChartCoordinate

/-!
# The overlap transition unit of the frames of `Ω_{P¹}`, and `deg K_{P¹} = −2`

`KltDP.Geometry.ProjectiveLineCanonicalFrame` builds the frame atlas `frameAtlas` of `Ω_{P¹}` on the
two standard opens and proves that its chart trivialisations send `d t` and `d s`, restricted to the
overlap, to `1` (`atlasFrame_left`, `atlasFrame_right`, through the cast-free transport
`baseRingCompare`).  Here that atlas is evaluated.

The evaluation goes through the chart coordinates of the atlas
(`TransitionUnitExtraction.chartEquiv` at `frameAtlas k`) and then through the generic
`transitionUnits_eq_of_chart`, which takes the atlas as a *parameter*.  It deliberately does **not**
go through `transitionUnits_eq_of_ofOpenCharts`, whose statement re-expands the atlas as
`localTrivializationsOfOpenCharts …`; instantiating that at `P¹` exhausts 4000000 heartbeats
(`F03_RESTRICTION_ADAPTERS.md`, Tasks 23–24).

The two chart-coordinate values are supplied by `ProjectiveLineChartCoordinate`
(`atlasChartEquiv_right_viaCoord`, `atlasChartEquiv_left_viaCoord`).  Every earlier attempt here
stated the same two facts with the over-site `.val.app` term inside the *type*, and every such
statement exhausted 4000000 heartbeats (Tasks 23–28).  The route that works never states an
over-site-typed condition about the concrete data at all: each concrete fact is an equation in
`Γ(X, W)` about `openChartCoordinate`, and all over-site content stays inside the generic accepted
lemmas `openChartCoordinate_app` and `chartEquiv_ofOpenCharts`.

With `t · s = 1` on the overlap (`leftFrame_mul_rightFrame`) and the inverse rule
`d s = −(s·s) • d t` (accepted `ProjectiveLineCanonicalTransition.baseRingDerivation_inv`), the
overlap transition unit is `−s²` (**`atlasUnits_overlap_eq`**), i.e. `−T⁻²` in the Laurent ring of the
overlap (`overlapLaurentUnit_atlasUnits`).  Hence

* **`exponent_canonicalSheaf_eq_neg_two : exponent Ω_{P¹} = −2`** and
* **`canonicalDegree_projectiveLine : deg K_{P¹} = −2`** (accepted
  `ProjectiveLineCanonicalInvertible.canonicalDegree_eq_exponent`, i.e. `deg = exponent` for every
  line bundle on `P¹`, the accepted 0AYX-based `ProjectiveLineDegreeExponent`).

Nothing is admitted here; there is no hypothesis beyond `k : Type u`, `[Field k]`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open KltDP.Geometry.ModuleCohomology KltDP.Geometry.SchemeKaehlerSheaf
open KltDP.Geometry.SchemeKaehlerOpenRestriction KltDP.Geometry.SchemeModuleRestriction
open KltDP.Geometry.ProjectiveLineChartTriviality KltDP.Geometry.ProjectiveLineComparison
open KltDP.Geometry.ProjectiveLineSections KltDP.Geometry.ProjectiveLineSheafExponent
open KltDP.Geometry.ProjectiveLineTransitionExtension KltDP.Geometry.ProjectiveLineTransitionExponent
open KltDP.Geometry.AffineModuleTilde KltDP.Geometry.AffineKaehlerTildeDerivation
open KltDP.Geometry.ProjectiveLineCanonical KltDP.Geometry.ProjectiveLineCanonicalFrame

universe u

namespace KltDP.Geometry.ProjectiveLineCanonicalFrameUnit

attribute [local instance] Types.instFunLike Types.instConcreteCategory
attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k]

set_option maxHeartbeats 4000000 in
/-- **The overlap transition unit of the frame atlas is `−s²`** (`ds = −s² dt`). -/
theorem atlasUnits_overlap_eq :
    (overlapRestriction k (atlasUnits k ⟨0⟩ ⟨1⟩) : Γ(projectiveSpace k 1, overlapOpen k)) =
      -(rightFrame k * rightFrame k) := by
  rw [overlapRestriction_val]
  exact transitionUnits_eq_of_chart (cotangent k) (frameAtlas k) ⟨0⟩ ⟨1⟩
    (overlapOpen_le_left k) (overlapOpen_le_right k)
    ((baseRingDerivation (projectiveSpaceToSpec k 1)).d (rightFrame k))
    ((baseRingDerivation (projectiveSpaceToSpec k 1)).d (leftFrame k))
    (rightFrame k * rightFrame k)
    (ProjectiveLineChartCoordinate.atlasChartEquiv_right_viaCoord k)
    (ProjectiveLineChartCoordinate.atlasChartEquiv_left_viaCoord k)
    (baseRingDerivation_inv (projectiveSpaceToSpec k 1) (overlapOpen k) (leftFrame k)
      (rightFrame k) (leftFrame_mul_rightFrame k))

/-- **The overlap unit in Laurent coordinates is `−T⁻²`.** -/
theorem overlapLaurentUnit_atlasUnits :
    ((overlapLaurentUnit k (overlapRestriction k (atlasUnits k ⟨0⟩ ⟨1⟩)) :
        (LaurentPolynomial k)ˣ) : LaurentPolynomial k) =
      LaurentPolynomial.C ((-1 : kˣ) : k) * LaurentPolynomial.T (-2) := by
  change overlapSectionsEquiv k
    (overlapRestriction k (atlasUnits k ⟨0⟩ ⟨1⟩) : Γ(projectiveSpace k 1, overlapOpen k)) = _
  rw [atlasUnits_overlap_eq, map_neg, map_mul, overlapSectionsEquiv_rightFrame,
    ← LaurentPolynomial.T_add, Units.val_neg, Units.val_one, map_neg, map_one, neg_mul, one_mul]
  norm_num

/-- **`exponent Ω_{P¹} = −2`.** -/
theorem exponent_canonicalSheaf_eq_neg_two : exponent k (canonicalSheaf k) = -2 := by
  rw [exponent_eq_atlasOverlapExponent]
  exact unitExponent_eq_of_monomial k _ (-1) (-2) (overlapLaurentUnit_atlasUnits k)

/-- **`deg K_{P¹} = −2`**, with no hypothesis. -/
theorem canonicalDegree_projectiveLine :
    CurveCanonical.canonicalDegree (projectiveSpaceToSpec k 1) = -2 :=
  (canonicalDegree_eq_exponent k).trans (exponent_canonicalSheaf_eq_neg_two k)

end KltDP.Geometry.ProjectiveLineCanonicalFrameUnit
