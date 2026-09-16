import KltDP.Examples.FrobeniusStrictTransformPrimeCurves
import KltDP.Examples.FrobeniusStrictTransformIsoProjectiveLine
import KltDP.Geometry.PrimeCurveOfClosedImmersion

/-!
# The generic point of `B` and its image downstairs (BRIEF42)

`(graphStrictPrimeCurve …).NotInSupport` is a statement about `C.genericPoint`, and
`not_mem_support_pullbackDivisor` turns it into one about `π.base C.genericPoint` for the blowdown
`π = projectiveContactProjection (n+1)`. This module computes that image.

Two points must not be confused, and neither is definitionally the other:

* `PrimeCurve.genericPoint` is `C.isIrreducible.genericPoint` — a point of the **surface**, extracted
  from irreducibility of the range;
* `genericPoint (strictTransform …)` is a point of the **curve scheme**.

`genericLift` is `Classical.choice` with only its image pinned, so it is no help either. The bridge is
topological: both `C.genericPoint` and `strictTransformι.base (genericPoint (strictTransform …))` are
generic points of the *same* set `Set.range (strictTransformι …).base` — the first by
`closure_genericPoint` with `coe_graphStrictPrimeCurve`, the second by the accepted
`range_eq_closure_genericPoint` — and a set in a `T0Space` has at most one generic point
(`IsGenericPoint.eq`). Schemes are `T0Space` and `QuasiSober` instances, and `IrreducibleSpace` comes
from the accepted `strictTransform_isIntegral` through Mathlib's `irreducibleSpace_of_isIntegral`, so no
instance has to be supplied by hand.

With the two identified, the image downstairs is read off the accepted composition lemma
`graphStrictIsoProjectiveLine_hom_comp` together with `genericPoint_eq_of_isOpenImmersion` along the
isomorphism `graphStrictIsoProjectiveLine` (an isomorphism is an open immersion).

* **`genericPoint_graphStrictPrimeCurve`** — `C.genericPoint = strictTransformι.base (genericPoint …)`;
* **`toInitial_genericPoint_graphStrictPrimeCurve`** — its image under the blowdown is
  `projectiveGraphMorphism (m + (n+1)) .base (genericPoint (projectiveSpace k 1))`, the graph's
  generic point.

**Not proved here**: that this point lies off `Supp(verticalFiberDivisorAt c)`. That is the remaining
step for `NotInSupport`, and it is *not* implied by the product's generic point lying off the fibre —
the graph's generic point is a different point, since the graph is a curve in the surface.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusGraphStrictGenericPoint

open KltDP.Geometry
open KltDP.Geometry.NormalProjectiveSurface.PrimeCurve
open KltDP.Geometry.PrimeCurveOfClosedImmersion
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism
open FrobeniusGlobalBlowupStages FrobeniusGlobalStrictTransform
open FrobeniusStrictTransformIsoProjectiveLine FrobeniusStrictTransformPrimeCurves
open FrobeniusStageSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (n : ℕ)
  (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)

-- `genericPoint` carries `[QuasiSober α] [IrreducibleSpace α]`, so the instance is needed to
-- elaborate the *statement*; a `haveI` inside the proof term runs too late. Integrality suffices,
-- since `irreducibleSpace_of_isIntegral` is an instance.
local instance graphStrictLineIntegral : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

/-- **The prime curve's generic point is the image of the curve scheme's generic point.**
Both are generic points of `Set.range (strictTransformι …).base`, and a set in a `T0Space` has at most
one. This is the bridge the `Classical.choice` definition of `genericLift` cannot provide. -/
theorem genericPoint_graphStrictPrimeCurve (m : ℕ) :
    (graphStrictPrimeCurve n hproj m).genericPoint =
      (strictTransformι (k := k) (n + 1) (m + (n + 1))).base
        (_root_.genericPoint (strictTransform (k := k) (n + 1) (m + (n + 1)))) := by
  have h₁ : IsGenericPoint ((graphStrictPrimeCurve n hproj m).genericPoint)
      (Set.range (strictTransformι (k := k) (n + 1) (m + (n + 1))).base) := by
    have h := (graphStrictPrimeCurve n hproj m).closure_genericPoint
    rw [coe_graphStrictPrimeCurve] at h
    exact h
  have h₂ : IsGenericPoint
      ((strictTransformι (k := k) (n + 1) (m + (n + 1))).base
        (_root_.genericPoint (strictTransform (k := k) (n + 1) (m + (n + 1)))))
      (Set.range (strictTransformι (k := k) (n + 1) (m + (n + 1))).base) :=
    (range_eq_closure_genericPoint (stageSurface (n + 1) hproj)
      (strictTransformι (n + 1) (m + (n + 1)))).symm
  exact h₁.eq h₂

/-- **The image of `B`'s generic point under the blowdown is the graph's generic point.**
The isomorphism `B ≅ P¹` carries generic point to generic point, and the accepted composition lemma
turns that into the statement downstairs. -/
theorem toInitial_genericPoint_graphStrictPrimeCurve (m : ℕ) :
    (projectiveContactProjection (k := k) (n + 1)).base
        ((graphStrictPrimeCurve n hproj m).genericPoint) =
      (projectiveGraphMorphism (k := k) (m + (n + 1))).base
        (_root_.genericPoint (projectiveSpace k 1)) := by
  rw [genericPoint_graphStrictPrimeCurve n hproj m]
  have hiso : (graphStrictIsoProjectiveLine (k := k) (n + 1) m).hom.base
      (_root_.genericPoint (strictTransform (k := k) (n + 1) (m + (n + 1)))) =
        _root_.genericPoint (projectiveSpace k 1) :=
    genericPoint_eq_of_isOpenImmersion (graphStrictIsoProjectiveLine (k := k) (n + 1) m).hom
  have hcomp := congrArg (fun f : strictTransform (k := k) (n + 1) (m + (n + 1)) ⟶
      projectiveProduct k => f.base
        (_root_.genericPoint (strictTransform (k := k) (n + 1) (m + (n + 1)))))
    (graphStrictIsoProjectiveLine_hom_comp (k := k) (n + 1) m)
  simp only [Scheme.comp_base_apply] at hcomp
  rw [hiso] at hcomp
  exact hcomp.symm

end KltDP.Examples.FrobeniusGraphStrictGenericPoint

namespace KltDP.Examples

open KltDP.Geometry FrobeniusProjectivePoints FrobeniusProjectiveMorphism
open FrobeniusGlobalBlowupStages FrobeniusGlobalStrictTransform
open FrobeniusStrictTransformPrimeCurves FrobeniusStageSurface
open FrobeniusGraphStrictGenericPoint

local instance graphStrictLineIntegral' {k : Type u} [Field k] : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

/-- **F29: the blowdown carries the generic point of `B` to the generic point of the graph.** -/
theorem f29_graph_strict_generic_point (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ)
    (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)
    (m : ℕ) :
    (projectiveContactProjection (k := k) (n + 1)).base
        ((graphStrictPrimeCurve n hproj m).genericPoint) =
      (projectiveGraphMorphism (k := k) (m + (n + 1))).base
        (_root_.genericPoint (projectiveSpace k 1)) :=
  toInitial_genericPoint_graphStrictPrimeCurve n hproj m

/-- The statement has exactly one universe parameter. -/
theorem f29_graph_strict_generic_point_universe_check (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ)
    (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)
    (m : ℕ) : True := by
  have _ := f29_graph_strict_generic_point.{u} k n hproj m
  trivial

end KltDP.Examples
