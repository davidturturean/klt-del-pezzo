import KltDP.Examples.FrobeniusVerticalCrossingGerm
import KltDP.Geometry.PrimeCurveCartierRestriction

/-!
# The crossing point lies IN the support of the vertical fibre (BRIEF54, blocker 1, nonempty half)

BRIEF54's first module proved the containment `Supp(x = c) ⊆ (x = c)` on the first coordinate. The
count needs the intersection `B ∩ Supp D` to be a **singleton**, i.e. both subsingleton and
**nonempty**. This module supplies the nonemptiness input at the product level.

## The route is BRIEF52, not geometry

Nothing here computes a germ or a support from scratch. BRIEF52 already identified the germ of the
divisor's own chart coefficient at the crossing point: pulled back to the parameter line along the
graph it is `localParameter c`. That is all that is needed, because

* `localParameter c` is **irreducible** (accepted `localParameter_uniformizer`), hence not a unit;
* a ring homomorphism carries units to units (`IsUnit.map`), and both maps in BRIEF52's chain are ring
  homomorphisms — the stalk map of `projectiveGraphMorphism p`, and the ring equivalence
  `lineStalkLocalEquiv c`;
* so the germ upstairs cannot be a unit either — and non-invertibility of the germ of a chart
  coefficient **is** support membership, by the accepted `mem_support_iff_not_isUnit_germ`.

Note the direction: only `IsUnit.map` is used, never `isUnit_map_iff`, so no `IsLocalHom` instance is
required — the forward implication holds for any ring homomorphism.

* **`not_isUnit_translatedVerticalGerm`** — the germ of the chart coefficient at the crossing point is
  not a unit;
* **`crossingPoint_mem_support_verticalFiberAt`** — hence the crossing point lies in `Supp(x = c)`.

Characteristic-free, primality-free, and `c` arbitrary — `c ≠ 0` is not needed, because this statement
lives on the product, below the tower where `c ≠ 0` first enters.

## What this does NOT give

**No row, and the count is still not closed.** With BRIEF54's first module this gives both directions
at the *product* level: a support point has first coordinate `x = c`, and the crossing point is a
support point. What remains for `B ∩ Supp D` on the **stage**:

* transporting nonemptiness up the tower to a point of `B ∩ Supp(stageVerticalDivisor)` — the blowdown
  direction of `mem_support_pullbackDivisor_iff` gives membership upstairs from membership downstairs
  only once a stage point over the crossing point is exhibited, and `stageCrossingPoint` is exactly
  such a point (BRIEF52), so this looks short but is not done here;
* the subsingleton half, which still needs the **range of `verticalLift`** characterised — unchanged
  from BRIEF54's first module.

`B · a = 1` additionally waits on lane F's `cartierPicardHom_pullbackDivisor_eq` (candidate1197).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusVerticalSupportCrossing

open KltDP.Geometry
open KltDP.Geometry.NormalProjectiveSurface.PrimeCurve
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism
open FrobeniusGraphContact
open FrobeniusGraphPicardClassMixedCoordinates
open FrobeniusVerticalFiberClass FrobeniusVerticalFiberTranslated
open FrobeniusVerticalContactLength FrobeniusVerticalContactStalk
open FrobeniusVerticalCrossingGerm

variable {k : Type u} [Field k]

/-- `mem_support_iff_not_isUnit_germ` and `verticalZeroChartZero` both carry `[IsIntegral _]` in their
types, so the instance is needed to elaborate the statements, not merely the proofs. -/
local instance supportCrossingProductIntegral : IsIntegral (projectiveProduct k) :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

/-- **The germ of the divisor's chart coefficient at the crossing point is not a unit.** If it were,
both ring maps of BRIEF52's chain would carry it to a unit, and BRIEF52 identifies that image as
`localParameter c`, which is irreducible. -/
theorem not_isUnit_translatedVerticalGerm (p : ℕ) (c : k) :
    ¬ IsUnit ((projectiveProduct k).presheaf.germ
      ((verticalTranslation (k := k) c).inv ⁻¹ᵁ productOpen (k := k) 0 0)
      ((projectiveGraphMorphism (k := k) p).base (lineParamPoint c))
      (graphParamPoint_mem_translatedOpen p c)
      ((verticalTranslation (k := k) c).inv.app (productOpen (k := k) 0 0)
        (verticalZeroChartEquation 0))) := by
  intro hu
  -- the stalk map of the graph parameterisation is a ring homomorphism
  have h1 : IsUnit ((projectiveGraphMorphism (k := k) p).stalkMap (lineParamPoint c)
      ((projectiveProduct k).presheaf.germ
        ((verticalTranslation (k := k) c).inv ⁻¹ᵁ productOpen (k := k) 0 0)
        ((projectiveGraphMorphism (k := k) p).base (lineParamPoint c))
        (graphParamPoint_mem_translatedOpen p c)
        ((verticalTranslation (k := k) c).inv.app (productOpen (k := k) 0 0)
          (verticalZeroChartEquation 0)))) :=
    hu.map ((projectiveGraphMorphism (k := k) p).stalkMap (lineParamPoint c)).hom
  -- and so is the stalk/localization comparison on `P¹`
  have h2 : IsUnit (lineStalkLocalEquiv c
      ((projectiveGraphMorphism (k := k) p).stalkMap (lineParamPoint c)
        ((projectiveProduct k).presheaf.germ
          ((verticalTranslation (k := k) c).inv ⁻¹ᵁ productOpen (k := k) 0 0)
          ((projectiveGraphMorphism (k := k) p).base (lineParamPoint c))
          (graphParamPoint_mem_translatedOpen p c)
          ((verticalTranslation (k := k) c).inv.app (productOpen (k := k) 0 0)
            (verticalZeroChartEquation 0))))) :=
    h1.map (lineStalkLocalEquiv c).toRingHom
  rw [lineStalkLocalEquiv_translatedVerticalGerm p c] at h2
  exact (localParameter_uniformizer c).not_isUnit h2

/-- **The crossing point of the graph with `x = c` lies in the support of `x = c`.** The nonemptiness
input the intersection count needs, at the product level. -/
theorem crossingPoint_mem_support_verticalFiberAt (p : ℕ) (c : k) :
    (projectiveGraphMorphism (k := k) p).base (lineParamPoint c) ∈
      (effectiveCartierIdealDataOfRegularEquations (projectiveProduct k)
        (verticalFiberDivisorAt (k := k) c)
        (verticalFiberDivisorAt_hasRegularEquations c)).support := by
  rw [mem_support_iff_not_isUnit_germ (verticalFiberDivisorAt (k := k) c)
    (verticalFiberDivisorAt_hasRegularEquations c)
    (verticalFiberDivisorAt_chart c (verticalZeroChartZero 0))
    ((projectiveGraphMorphism (k := k) p).base (lineParamPoint c))
    (graphParamPoint_mem_translatedOpen p c)]
  exact not_isUnit_translatedVerticalGerm p c

end KltDP.Examples.FrobeniusVerticalSupportCrossing

namespace KltDP.Examples

open KltDP.Geometry
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism
open FrobeniusVerticalFiberClass FrobeniusVerticalFiberTranslated
open FrobeniusVerticalContactStalk
open FrobeniusVerticalSupportCrossing

local instance supportCrossingProductIntegralTop {k : Type u} [Field k] :
    IsIntegral (projectiveProduct k) :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

/-- **F29: the crossing point lies in the support of the vertical fibre `x = c`.** Together with
`f29_vertical_support_first_coordinate` this pins the support from both sides at the product level:
every support point has first coordinate `x = c`, and the graph's crossing point is one. Derived from
BRIEF52's germ identification, not from a new computation. -/
theorem f29_vertical_support_crossing (k : Type u) [Field k] (p : ℕ) (c : k) :
    (projectiveGraphMorphism (k := k) p).base (lineParamPoint c) ∈
      (effectiveCartierIdealDataOfRegularEquations (projectiveProduct k)
        (verticalFiberDivisorAt (k := k) c)
        (verticalFiberDivisorAt_hasRegularEquations c)).support :=
  crossingPoint_mem_support_verticalFiberAt p c

/-- The statement has exactly one universe parameter. -/
theorem f29_vertical_support_crossing_universe_check (k : Type u) [Field k] (p : ℕ) (c : k) :
    True := by
  have _ := f29_vertical_support_crossing.{u} k p c
  trivial

end KltDP.Examples
