import KltDP.Examples.FrobeniusVerticalTranslationEquation
import KltDP.Examples.ProjectiveLinePointAtInfinity
import KltDP.Examples.FrobeniusGraphRationalPoints
import KltDP.Examples.FrobeniusFiberZeroClass
import KltDP.Examples.FrobeniusGraphPicardClassIntegral
import KltDP.Geometry.ProjectiveLineTranslation

/-!
# Chart-open bookkeeping for the vertical fibre (BRIEF49, Leg 3, first half)

Leg 3 is the tower transport plus the chart-open bookkeeping. This module is the **bookkeeping**: the two
facts about *opens and points* that the transport needs, both established without any cast.

**First**, the lemma dropped from Leg 2. `productOpen 0 0 = planeChart ''ᵁ ⊤` is true because
`productChart 0 0 = planeChart` is accepted, but it cannot be proved by `congrArg (fun f => f ''ᵁ ⊤)`:
`f ''ᵁ U` takes an `[IsOpenImmersion f]` instance argument, so the bound `f` has none and the body never
elaborates. The route that works is to leave `''ᵁ` **before** rewriting the morphism — push both sides to
`opensRange` with the pinned `Scheme.Hom.image_top_eq_opensRange`, drop to sets with `Opens.ext`, and
rewrite at `Set.range _.base`, which carries no instance at all.

This is the third member of the transport classification, and the one that corrected the discriminator
given in Leg 1: dependent through the **type** (`f.app U : Γ(Y,U) ⟶ Γ(X, f ⁻¹ᵁ U)`), safe
(`f.base x : Y`), dependent through a **typeclass argument** (`f ''ᵁ U`). Check instance arguments before
concluding a transport is non-dependent.

**Second**, the point computation. The stage chart of `stageVerticalDivisor` has open
`π ⁻¹ᵁ ((verticalTranslation c).inv ⁻¹ᵁ productOpen 0 0)`, so the transport needs the crossing point's
image to lie in `productOpen 0 0` *after* the translation. Geometrically the graph point `(c, c^p)` is
carried by `τ_{-c} × τ_0` to `(0, c^p)`, and both coordinates are finite, so it does. Every step here is
**point-level** — `f.base x : Y` regardless of `f` — so no cast arises anywhere.

* **`productOpen_zero_zero_eq`** — the divisor's chart open at `j = 0` is the plane chart's image;
* `graphMorphism_base_point` — the graph morphism sends `[1:a]` to the product point `(a, a^p)`;
* `translatedCrossingPoint`, `translatedCrossingPoint_fst`, `translatedCrossingPoint_snd` — the translated
  point and its two coordinates, `[1:0]` and `[1:c^p]`;
* **`translatedCrossingPoint_mem_productOpen`** — hence it lies in `productOpen 0 0`.

Characteristic-free, every `p` and every `c`; **`c ≠ 0` is not needed for the bookkeeping** — it enters
Leg 3's other half, the tower transport, through stage-puncture membership
(`verticalCrossingPoint_mem_stagePuncture`).

**Not proved here**: the germ transport itself, and therefore none of the rows.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusVerticalChartBookkeeping

open KltDP.Geometry
open KltDP.Geometry.ProjectiveLineComparison KltDP.Geometry.ProjectiveLineTranslation
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism FrobeniusGraphClosed
open FrobeniusProductPlaneChart FrobeniusGraphPicardClassCharts
open FrobeniusGraphPicardClassMixedCoordinates FrobeniusGraphPicardClassIntegral
open FrobeniusFiberZeroClass FrobeniusFiberClosure
open ProjectiveProductTranslation FrobeniusGraphRationalPoints
open ProjectiveLinePointAtInfinity FrobeniusVerticalFiberTranslated

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k]

/-- **The divisor's chart open at `j = 0` is the image of the plane chart.**
Proved by pushing both sides to `opensRange` *before* touching the morphism, then descending to
`Set.range _.base`, where no `[IsOpenImmersion _]` argument appears. A `congrArg` under `''ᵁ` does not
elaborate, because the image open carries that instance. -/
theorem productOpen_zero_zero_eq :
    productOpen (k := k) 0 0 = planeChart (k := k) ''ᵁ ⊤ := by
  show productChart (k := k) 0 0 ''ᵁ ⊤ = planeChart (k := k) ''ᵁ ⊤
  rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.image_top_eq_opensRange]
  apply TopologicalSpace.Opens.ext
  show Set.range (productChart (k := k) 0 0).base = Set.range (planeChart (k := k)).base
  rw [productChart_zero_zero]

/-- The graph morphism carries the rational point `[1:a]` of `P¹` to the product point `(a, a^p)`. -/
theorem graphMorphism_base_point (p : ℕ) (a : k) :
    (projectiveGraphMorphism (k := k) p).base (point a) = graphPoint p a := by
  change fieldMorphismPoint (pointMorphism a ≫ projectiveGraphMorphism (k := k) p) = graphPoint p a
  rw [pointMorphism_projectiveGraphMorphism]
  rfl

/-- The graph point `(c, c^p)` moved by the inverse vertical translation `τ_{-c} × τ_0`. -/
def translatedCrossingPoint (p : ℕ) (c : k) : projectiveProduct k :=
  (verticalTranslation (k := k) c).inv.base (graphPoint p c)

/-- **Its first coordinate is `[1:0]`**: the translation moves `c` to `c + (-c) = 0`. -/
theorem translatedCrossingPoint_fst (p : ℕ) (c : k) :
    firstProjection.base (translatedCrossingPoint (k := k) p c) = point (0 : k) := by
  have hmor := congrArg
    (fun f : projectiveProduct k ⟶ projectiveSpace k 1 => f.base (graphPoint p c))
    (productTranslation_fst (-c) (-(0 : k)))
  simp only [Scheme.comp_base_apply] at hmor
  change firstProjection.base
    ((productTranslation (-c) (-(0 : k))).base (graphPoint p c)) = point (0 : k)
  rw [hmor, graphPoint_fst]
  change fieldMorphismPoint (pointMorphism c ≫ projectiveTranslation (-c)) = point (0 : k)
  rw [pointMorphism_projectiveTranslation, add_neg_cancel]
  rfl

/-- **Its second coordinate is `[1:c^p]`**: the second translation is by `-0`. -/
theorem translatedCrossingPoint_snd (p : ℕ) (c : k) :
    secondProjection.base (translatedCrossingPoint (k := k) p c) = point (c ^ p) := by
  have hmor := congrArg
    (fun f : projectiveProduct k ⟶ projectiveSpace k 1 => f.base (graphPoint p c))
    (productTranslation_snd (-c) (-(0 : k)))
  simp only [Scheme.comp_base_apply] at hmor
  change secondProjection.base
    ((productTranslation (-c) (-(0 : k))).base (graphPoint p c)) = point (c ^ p)
  rw [hmor, graphPoint_snd]
  change fieldMorphismPoint
    (pointMorphism (c ^ p) ≫ projectiveTranslation (-(0 : k))) = point (c ^ p)
  rw [pointMorphism_projectiveTranslation, neg_zero, add_zero]
  rfl

/-- **The translated crossing point lies in the divisor's chart open.** Both coordinates are finite:
the first is `[1:0]`, the second `[1:c^p]`, and `point_mem_chart` puts every `[1:a]` in `chartOpen k 0`. -/
theorem translatedCrossingPoint_mem_productOpen (p : ℕ) (c : k) :
    translatedCrossingPoint (k := k) p c ∈ productOpen (k := k) 0 0 := by
  apply mem_productOpen_of_mem_range
  rw [productChart_range]
  refine ⟨?_, ?_⟩
  · show firstProjection.base (translatedCrossingPoint (k := k) p c) ∈
      (chartOpen k 0 : Set (projectiveSpace k 1))
    rw [translatedCrossingPoint_fst]
    exact point_mem_chart (0 : k)
  · show secondProjection.base (translatedCrossingPoint (k := k) p c) ∈
      (chartOpen k 0 : Set (projectiveSpace k 1))
    rw [translatedCrossingPoint_snd]
    exact point_mem_chart (c ^ p)

end KltDP.Examples.FrobeniusVerticalChartBookkeeping

namespace KltDP.Examples

open KltDP.Geometry
open FrobeniusProjectivePoints FrobeniusProductPlaneChart
open FrobeniusGraphPicardClassMixedCoordinates FrobeniusVerticalFiberTranslated
open FrobeniusVerticalChartBookkeeping

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **F29: the chart-open bookkeeping for the vertical fibre.** The divisor's chart open at `j = 0` is the
plane chart's image, and the graph's crossing point with `x = c`, moved by the inverse translation, lies in
it. Characteristic-free, every `p` and every `c`; `c ≠ 0` is not needed here. -/
theorem f29_vertical_chart_bookkeeping (k : Type u) [Field k] (p : ℕ) (c : k) :
    productOpen (k := k) 0 0 = planeChart (k := k) ''ᵁ ⊤ ∧
      translatedCrossingPoint (k := k) p c ∈ productOpen (k := k) 0 0 :=
  ⟨productOpen_zero_zero_eq, translatedCrossingPoint_mem_productOpen p c⟩

/-- The statement has exactly one universe parameter. -/
theorem f29_vertical_chart_bookkeeping_universe_check (k : Type u) [Field k] (p : ℕ) (c : k) :
    True := by
  have _ := f29_vertical_chart_bookkeeping.{u} k p c
  trivial

end KltDP.Examples
