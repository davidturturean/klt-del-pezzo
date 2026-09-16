import KltDP.Examples.FrobeniusVerticalCrossingGerm
import KltDP.Examples.FrobeniusVerticalGermTransport
import KltDP.Examples.FrobeniusContactLengthPow
import KltDP.Examples.FrobeniusStrictTransformIsoProjectiveLine

/-!
# Leg 4: the vertical divisor's germ on `B`, and its contact length (BRIEF52, continuation)

Leg 3c(iii) (`FrobeniusVerticalCrossingGerm`) identified the **product** germ of the divisor's chart
coefficient with `localParameter c`, after pulling it back to the parameter line along the graph
parameterisation. Two things still separated that from the contact length along `B`, and this module
supplies both:

* **the restriction to the curve** — the rows consume a germ on the strict transform `B_n`, obtained
  from the stage germ by `strictTransformι.stalkMap`, and `crossingStalkEquiv` compares stalks through
  `graphStrictIsoProjectiveLine.inv.stalkMap`. Composing the three stalk maps gives the stalk map of
  `graphStrictIsoProjectiveLine.inv ≫ strictTransformι ≫ projectiveContactProjection`;
* **the point index** — that composite *is* `projectiveGraphMorphism (m+(n+1))` (accepted
  `graphStrictIsoProjectiveLine_hom_comp`), but only propositionally, and the germ's point index sits
  in its type. Under the standing rule this is re-indexed, never transported: `stalkMap_germ_congr`
  takes the two morphisms as **variables** and a `subst` eliminates the identification before any
  index has to move, exactly the device that carried Leg 3c(iii).

Nothing here computes `.app`, transports a stalk along a point equality, or inserts a cast.

## What is proved

* `stalkMap_germ_congr`, `stalkMap_stalkMap` — generic: germ transport along equal morphisms, and the
  composition of two stalk maps on an element;
* `towerStalkEquiv_apply`, `crossingStalkEquiv_apply` — **bookkeeping, true by construction** and
  recorded as such: `towerStalkEquiv` is *defined* as the `asIso` packaging of
  `projectiveContactProjection.stalkMap`, and `crossingStalkEquiv` as the `trans` of
  `graphStrictIsoProjectiveLine.inv.stalkMap` with `lineStalkLocalEquiv`. Both are `rfl`. They carry no
  geometric claim: the content is entirely in Leg 3c(iii) and in the accepted morphism identity;
* `graphStrictIso_inv_comp_projection` — the composite down to `P¹ × P¹` is the graph parameterisation;
* **`crossingStalkEquiv_stageVerticalGerm`** — the germ of the coefficient that
  `stageVerticalChartZero` actually carries, restricted to `B_{n+1}` at the crossing point, is
  `localParameter c`;
* **`crossing_vertical_contact_length`** — hence that germ has quotient length `1`.

`c ≠ 0` is required, entering through `verticalCrossingPoint_mem_stagePuncture` as it has since
Leg 3b: the centre of the tower lies over `x = 0`. Characteristic-free and primality-free otherwise.

**Not proved here, and no row is claimed.** This is the *local* contact length of `B` against the
actual divisor `stageVerticalDivisor c` at the crossing point. The row `B · a = 1` is an intersection
**number**, which additionally needs the prime-curve machinery — `restrictedCoefficient` on
`C.toScheme` transported by Leg 1's `graphStrictLift`, the `NotInSupport` side condition (which this
lane derived), and the sum over intersection points. The rows `B · b = p` and `F̃ · a = 1` are not
touched at all: the first is the **horizontal** fibre, a different divisor whose pulled-back equation
is a `p`-th power, and the second needs the `F̃` counterpart of this whole chain, whose crossing point
is `(c, 0)` rather than `(c, c^p)` and whose parameterisation is a different ring map.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusVerticalCrossingContact

open KltDP.Geometry
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism
open FrobeniusGlobalBlowupStages FrobeniusGlobalStrictTransform
open FrobeniusStageComplement.PlaneChartedScheme
open FrobeniusGraphPicardClassMixedCoordinates
open FrobeniusStrictTransformIsoProjectiveLine
open FrobeniusGraphContact FrobeniusGraphStalkContact
open FrobeniusVerticalFiberClass FrobeniusVerticalFiberTranslated
open FrobeniusStageVerticalDivisor StagePunctureStalkTransport
open FrobeniusVerticalChartBookkeeping FrobeniusVerticalGermTransport
open FrobeniusVerticalContactLength FrobeniusVerticalContactStalk
open FrobeniusVerticalCrossingGerm

section Generic

/-- **Germ transport along equal morphisms.** Both morphisms are variables and the identification is
eliminated by `subst`, so the point index — which sits in the germ's *type* — never moves. The two
membership proofs are proofs of the same proposition once `F` and `G` coincide. -/
theorem stalkMap_germ_congr {X Y : Scheme.{u}} (F G : X ⟶ Y) (hFG : F = G) (x : X)
    (U : Y.Opens) (hF : F.base x ∈ U) (hG : G.base x ∈ U) (s : Γ(Y, U)) :
    F.stalkMap x (Y.presheaf.germ U (F.base x) hF s) =
      G.stalkMap x (Y.presheaf.germ U (G.base x) hG s) := by
  subst hFG
  rfl

/-- **Two stalk maps applied in turn are the stalk map of the composite.** Stated with the indices in
their canonical form so that use sites supply them by unification rather than by syntactic match. -/
theorem stalkMap_stalkMap {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
    (z : Z.presheaf.stalk (g.base (f.base x))) :
    f.stalkMap x (g.stalkMap (f.base x) z) = (f ≫ g).stalkMap x z := by
  rw [Scheme.stalkMap_comp, CommRingCat.comp_apply]
  rfl

end Generic

variable {k : Type u} [Field k]

-- The integrality instances `RegularCartierEquationChart X D` needs to elaborate the *type* of
-- `stageVerticalChartZero`; `FrobeniusStageVerticalDivisor` supplies them only as `local instance`s,
-- which reach neither an importing module nor a later namespace block. The `.carrier` form is a
-- separate instance: search does not reduce `projectiveProductInitial.carrier` to `projectiveProduct k`.
local instance crossingContactProductIntegral : IsIntegral (projectiveProduct k) :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

local instance crossingContactInitialIntegral :
    IsIntegral (projectiveProductInitial (k := k)).carrier :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

local instance crossingContactStageIntegral (N : ℕ) :
    IsIntegral (projectiveContactStage (k := k) N) :=
  FrobeniusTowerFunctionField.PlaneChartedScheme.instStageIsIntegral
    (projectiveProductInitial (k := k)) N

variable (n m : ℕ)

/-- **The blowdown of `B_n`, read through its identification with `P¹`, is the graph parameterisation.**
Immediate from the accepted `graphStrictIsoProjectiveLine_hom_comp` by cancelling the isomorphism. -/
theorem graphStrictIso_inv_comp_projection :
    (graphStrictIsoProjectiveLine (k := k) n m).inv ≫
        (strictTransformι (k := k) n (m + n) ≫ projectiveContactProjection n) =
      projectiveGraphMorphism (m + n) := by
  rw [← graphStrictIsoProjectiveLine_hom_comp n m, ← Category.assoc, Iso.inv_hom_id,
    Category.id_comp]

/-- **Bookkeeping, true by construction**: `towerStalkEquiv` is defined as the `asIso` packaging of the
blowdown's stalk map, so applying it *is* applying that stalk map. Nothing geometric is claimed; the
content sits in Leg 3c(iii) and in `graphStrictIso_inv_comp_projection`. -/
theorem towerStalkEquiv_apply (N : ℕ) (x : projectiveContactStage (k := k) N)
    (hx : x ∈ stagePuncture (projectiveProductInitial (k := k)) N)
    (z : (projectiveProduct k).presheaf.stalk
      ((projectiveContactProjection (k := k) N).base x)) :
    towerStalkEquiv N x hx z = (projectiveContactProjection (k := k) N).stalkMap x z := rfl

/-- **Bookkeeping, true by construction**: `crossingStalkEquiv` is the `trans` of the isomorphism's
stalk map with `lineStalkLocalEquiv`. -/
theorem crossingStalkEquiv_apply (c : k)
    (f : (strictTransform (k := k) n (m + n)).presheaf.stalk (crossingPoint n m c)) :
    crossingStalkEquiv n m c f =
      lineStalkLocalEquiv c
        ((graphStrictIsoProjectiveLine (k := k) n m).inv.stalkMap (lineParamPoint c) f) := rfl

variable [IsAlgClosed k]

/-- **Leg 4: the germ on `B` of the coefficient the vertical divisor actually carries is the local
parameter.** The germ is the stage chart coefficient of `stageVerticalChartZero (n+1) c 0` — the
translate of the plane coordinate, pulled back along the blowdown — restricted to the strict transform
at the crossing point. `c ≠ 0` enters through stage-puncture membership. -/
theorem crossingStalkEquiv_stageVerticalGerm (c : k) (hc : c ≠ 0) :
    crossingStalkEquiv (n + 1) m c
        ((strictTransformι (k := k) (n + 1) (m + (n + 1))).stalkMap
          (crossingPoint (n + 1) m c)
          ((projectiveContactStage (k := k) (n + 1)).presheaf.germ
            ((stageVerticalChartZero (k := k) (n + 1) c 0).chart.openSet)
            (stageCrossingPoint n m c) (stageCrossingPoint_mem_translatedOpen n m c)
            ((stageVerticalChartZero (k := k) (n + 1) c 0).coefficient))) =
      localParameter c := by
  -- the stage germ is the blowdown's stalk map applied to the product germ (Leg 3b, then bookkeeping)
  have hstage : (projectiveContactStage (k := k) (n + 1)).presheaf.germ
        ((stageVerticalChartZero (k := k) (n + 1) c 0).chart.openSet)
        (stageCrossingPoint n m c) (stageCrossingPoint_mem_translatedOpen n m c)
        ((stageVerticalChartZero (k := k) (n + 1) c 0).coefficient) =
      (projectiveContactProjection (k := k) (n + 1)).stalkMap (stageCrossingPoint n m c)
        ((projectiveProduct k).presheaf.germ
          ((verticalTranslation (k := k) c).inv ⁻¹ᵁ productOpen (k := k) 0 0)
          ((projectiveContactProjection (k := k) (n + 1)).base (stageCrossingPoint n m c))
          (stageCrossingPoint_mem_translatedOpen n m c)
          ((verticalTranslation (k := k) c).inv.app (productOpen (k := k) 0 0)
            (verticalZeroChartEquation 0))) :=
    (towerStalkEquiv_stageVerticalChartZero n m c hc).symm
  rw [hstage]
  -- the curve inclusion and the blowdown compose
  have hcomp : (strictTransformι (k := k) (n + 1) (m + (n + 1))).stalkMap
        (crossingPoint (n + 1) m c)
        ((projectiveContactProjection (k := k) (n + 1)).stalkMap (stageCrossingPoint n m c)
          ((projectiveProduct k).presheaf.germ
            ((verticalTranslation (k := k) c).inv ⁻¹ᵁ productOpen (k := k) 0 0)
            ((projectiveContactProjection (k := k) (n + 1)).base (stageCrossingPoint n m c))
            (stageCrossingPoint_mem_translatedOpen n m c)
            ((verticalTranslation (k := k) c).inv.app (productOpen (k := k) 0 0)
              (verticalZeroChartEquation 0)))) =
      (strictTransformι (k := k) (n + 1) (m + (n + 1)) ≫
          projectiveContactProjection (k := k) (n + 1)).stalkMap (crossingPoint (n + 1) m c)
        ((projectiveProduct k).presheaf.germ
          ((verticalTranslation (k := k) c).inv ⁻¹ᵁ productOpen (k := k) 0 0)
          ((projectiveContactProjection (k := k) (n + 1)).base (stageCrossingPoint n m c))
          (stageCrossingPoint_mem_translatedOpen n m c)
          ((verticalTranslation (k := k) c).inv.app (productOpen (k := k) 0 0)
            (verticalZeroChartEquation 0))) :=
    stalkMap_stalkMap _ _ _ _
  rw [hcomp, crossingStalkEquiv_apply]
  -- the third stalk map joins, giving the blowdown of `B` read through `P¹`
  have hjoin : (graphStrictIsoProjectiveLine (k := k) (n + 1) m).inv.stalkMap (lineParamPoint c)
        ((strictTransformι (k := k) (n + 1) (m + (n + 1)) ≫
            projectiveContactProjection (k := k) (n + 1)).stalkMap (crossingPoint (n + 1) m c)
          ((projectiveProduct k).presheaf.germ
            ((verticalTranslation (k := k) c).inv ⁻¹ᵁ productOpen (k := k) 0 0)
            ((projectiveContactProjection (k := k) (n + 1)).base (stageCrossingPoint n m c))
            (stageCrossingPoint_mem_translatedOpen n m c)
            ((verticalTranslation (k := k) c).inv.app (productOpen (k := k) 0 0)
              (verticalZeroChartEquation 0)))) =
      ((graphStrictIsoProjectiveLine (k := k) (n + 1) m).inv ≫
          (strictTransformι (k := k) (n + 1) (m + (n + 1)) ≫
            projectiveContactProjection (k := k) (n + 1))).stalkMap (lineParamPoint c)
        ((projectiveProduct k).presheaf.germ
          ((verticalTranslation (k := k) c).inv ⁻¹ᵁ productOpen (k := k) 0 0)
          ((projectiveContactProjection (k := k) (n + 1)).base (stageCrossingPoint n m c))
          (stageCrossingPoint_mem_translatedOpen n m c)
          ((verticalTranslation (k := k) c).inv.app (productOpen (k := k) 0 0)
            (verticalZeroChartEquation 0))) :=
    stalkMap_stalkMap _ _ _ _
  rw [hjoin]
  -- re-index onto the graph parameterisation, by `subst` on morphism variables, not by transport
  have hswap := stalkMap_germ_congr
    ((graphStrictIsoProjectiveLine (k := k) (n + 1) m).inv ≫
      (strictTransformι (k := k) (n + 1) (m + (n + 1)) ≫
        projectiveContactProjection (k := k) (n + 1)))
    (projectiveGraphMorphism (k := k) (m + (n + 1)))
    (graphStrictIso_inv_comp_projection (n + 1) m)
    (lineParamPoint c)
    ((verticalTranslation (k := k) c).inv ⁻¹ᵁ productOpen (k := k) 0 0)
    (stageCrossingPoint_mem_translatedOpen n m c)
    (graphParamPoint_mem_translatedOpen (m + (n + 1)) c)
    ((verticalTranslation (k := k) c).inv.app (productOpen (k := k) 0 0)
      (verticalZeroChartEquation 0))
  refine Eq.trans ?_ (lineStalkLocalEquiv_translatedVerticalGerm (m + (n + 1)) c)
  exact congrArg (fun z => lineStalkLocalEquiv c z) hswap

/-- **The vertical fibre `x = c` meets `B` in contact length one**, computed against the germ of the
coefficient the divisor `stageVerticalDivisor (n+1) c` actually carries. Characteristic-free and
primality-free; `c ≠ 0` only. -/
theorem crossing_vertical_contact_length (c : k) (hc : c ≠ 0) :
    Module.length
        ((strictTransform (k := k) (n + 1) (m + (n + 1))).presheaf.stalk
          (crossingPoint (n + 1) m c))
        ((strictTransform (k := k) (n + 1) (m + (n + 1))).presheaf.stalk
            (crossingPoint (n + 1) m c) ⧸
          Ideal.span
            {(strictTransformι (k := k) (n + 1) (m + (n + 1))).stalkMap
              (crossingPoint (n + 1) m c)
              ((projectiveContactStage (k := k) (n + 1)).presheaf.germ
                ((stageVerticalChartZero (k := k) (n + 1) c 0).chart.openSet)
                (stageCrossingPoint n m c) (stageCrossingPoint_mem_translatedOpen n m c)
                ((stageVerticalChartZero (k := k) (n + 1) c 0).coefficient))}) = 1 :=
  crossing_contact_length (n + 1) m c _ (crossingStalkEquiv_stageVerticalGerm n m c hc)

end KltDP.Examples.FrobeniusVerticalCrossingContact

namespace KltDP.Examples

open KltDP.Geometry
open FrobeniusProjectivePoints FrobeniusGlobalBlowupStages FrobeniusGlobalStrictTransform
open FrobeniusGraphPicardClassMixedCoordinates
open FrobeniusGraphContact
open FrobeniusVerticalFiberClass FrobeniusVerticalFiberTranslated
open FrobeniusStageVerticalDivisor
open FrobeniusVerticalGermTransport FrobeniusVerticalContactStalk
open FrobeniusVerticalCrossingContact

local instance crossingContactProductIntegralTop {k : Type u} [Field k] :
    IsIntegral (projectiveProduct k) :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

local instance crossingContactInitialIntegralTop {k : Type u} [Field k] :
    IsIntegral (projectiveProductInitial (k := k)).carrier :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

local instance crossingContactStageIntegralTop {k : Type u} [Field k] (N : ℕ) :
    IsIntegral (projectiveContactStage (k := k) N) :=
  FrobeniusTowerFunctionField.PlaneChartedScheme.instStageIsIntegral
    (projectiveProductInitial (k := k)) N

/-- **F29: the vertical fibre cuts `B` in contact length one, against the actual divisor.** The germ
is that of the coefficient `stageVerticalChartZero` carries, restricted to the strict transform at the
crossing point; its quotient has length `1`. -/
theorem f29_vertical_crossing_contact (k : Type u) [Field k] [IsAlgClosed k] (n m : ℕ) (c : k)
    (hc : c ≠ 0) :
    Module.length
        ((strictTransform (k := k) (n + 1) (m + (n + 1))).presheaf.stalk
          (crossingPoint (n + 1) m c))
        ((strictTransform (k := k) (n + 1) (m + (n + 1))).presheaf.stalk
            (crossingPoint (n + 1) m c) ⧸
          Ideal.span
            {(strictTransformι (k := k) (n + 1) (m + (n + 1))).stalkMap
              (crossingPoint (n + 1) m c)
              ((projectiveContactStage (k := k) (n + 1)).presheaf.germ
                ((stageVerticalChartZero (k := k) (n + 1) c 0).chart.openSet)
                (stageCrossingPoint n m c) (stageCrossingPoint_mem_translatedOpen n m c)
                ((stageVerticalChartZero (k := k) (n + 1) c 0).coefficient))}) = 1 :=
  crossing_vertical_contact_length n m c hc

/-- The statement has exactly one universe parameter. -/
theorem f29_vertical_crossing_contact_universe_check (k : Type u) [Field k] [IsAlgClosed k]
    (n m : ℕ) (c : k) (hc : c ≠ 0) : True := by
  have _ := f29_vertical_crossing_contact.{u} k n m c hc
  trivial

end KltDP.Examples
