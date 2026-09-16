import KltDP.Examples.FrobeniusVerticalFiberTranslated
import KltDP.Geometry.CartierDivisorPullbackSupport
import KltDP.Geometry.PrimeCurveCartierRestriction
import KltDP.Examples.FrobeniusGraphClosed
import KltDP.Examples.FrobeniusGraphPicardClassRulingDivisors
import KltDP.Examples.FrobeniusGraphPicardClassRulingCoordinates
import KltDP.Examples.FrobeniusGraphPicardClassIntegral
import KltDP.Examples.ProjectiveProductTranslation
import KltDP.Geometry.ProjectiveLineTranslation
import KltDP.Geometry.ProjectiveSpaceIntegral
import KltDP.Geometry.RationalFunctionSheaf

/-!
# The graph's generic point lies off every vertical fibre `x = c` (BRIEF44)

`(graphStrictPrimeCurve …).NotInSupport` is, after `f29_graph_strict_generic_point` and
`not_mem_support_pullbackDivisor`, a statement about the point

    `(projectiveGraphMorphism p).base (genericPoint (projectiveSpace k 1))`

— the generic point of the *graph curve* inside `P¹ × P¹`. That is **not** the generic point of the
product, so the queued `genericPoint_not_mem_support_verticalFiberAt` does not apply: the graph is a
curve in the surface, and `projectiveGraphMorphism` is a closed immersion with no dominance, so
Mathlib's `genericPoint_eq_of_isOpenImmersion` cannot transport between the two points either.

The proof here needs no computation of `(projectiveGraphMorphism p).app`, because the fibre divisor
already carries a chart on which its equation is `1`:

* `verticalZeroDivisor` is glued from `verticalZeroEquation 0 = x` on `rulingOpen 0 0` and
  `verticalZeroEquation 1 = 1` on `rulingOpen 0 1`. `verticalZeroDivisor_restrict_ruling 1` is
  literally the `represents` field of a chart with open `rulingOpen 0 1`, equation `1` and
  regular coefficient `1` — so **every** point of `rulingOpen 0 1` is off the support, by
  `mem_support_iff_not_isUnit_germ` (the germ of `1` is a unit);
* `rulingOpen 0 1 = rulingProjection 0 ⁻¹ᵁ chartOpen k 1`, so membership only constrains the *first*
  coordinate. The graph morphism satisfies `projectiveGraphMorphism p ≫ firstProjection = 𝟙`
  (accepted `projectiveGraphMorphism_fst`), hence the first coordinate of the graph's generic point
  is the generic point of `P¹` itself, which lies in every nonempty open;
* the fibre `x = c` is `pullbackDivisor (verticalTranslation c).inv verticalZeroDivisor`, and
  `productTranslation_fst` moves the first coordinate by the isomorphism
  `projectiveTranslation (-c)`, which fixes the generic point.

* **`graphGenericPoint_fst`** — the first coordinate of the graph's generic point is `P¹`'s;
* **`verticalZeroRulingChart`** — the trivial-equation chart of `x = 0` on `rulingOpen 0 1`;
* **`graphGenericPoint_not_mem_support_verticalFiberAt`** — the statement `NotInSupport` needs.

`c ≠ 0` is **not** needed here (the graph meets `x = c` in one point for every `c`); it is needed
downstream only to keep the crossing off the centre of the tower. Nothing about the second
coordinate, and hence nothing about `p`, enters the argument.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusGraphGenericPointOffFiber

open KltDP.Geometry
open KltDP.Geometry.NormalProjectiveSurface.PrimeCurve
open KltDP.Geometry.ProjectiveLineComparison
open KltDP.Geometry.ProjectiveLineTranslation
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism FrobeniusGraphClosed
open FrobeniusGraphPicardClassIntegral FrobeniusGraphPicardClassRulingCoordinates
open FrobeniusGraphPicardClassRulingDivisors ProjectiveProductTranslation
open FrobeniusVerticalFiberClass FrobeniusVerticalFiberTranslated

variable {k : Type u} [Field k]

-- A `local instance` does not survive the `end` of its namespace block and is never exported by the
-- accepted modules, so both blocks of this file declare integrality themselves.
local instance offFiberProductIntegral : IsIntegral (projectiveProduct k) :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

-- `genericPoint` carries `[QuasiSober] [IrreducibleSpace]`, both needed to elaborate the *statements*
-- below, so integrality of the line is a section-level instance too
-- (`irreducibleSpace_of_isIntegral` is an instance).
local instance offFiberLineIntegral : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

/-- **The first coordinate of the graph's generic point is the generic point of `P¹`.**
This is the accepted `projectiveGraphMorphism_fst` read at a point. -/
theorem graphGenericPoint_fst (p : ℕ) :
    (rulingProjection (k := k) 0).base
        ((projectiveGraphMorphism (k := k) p).base
          (_root_.genericPoint (projectiveSpace k 1))) =
      _root_.genericPoint (projectiveSpace k 1) := by
  -- `(𝟙 X).base` cannot be written with dot notation: the type of `𝟙 X` elaborates with head
  -- `Quiver.Hom`, not `Scheme.Hom`. Letting `rw` produce the identity avoids the field notation.
  have h : ((projectiveGraphMorphism (k := k) p) ≫ firstProjection).base
      (_root_.genericPoint (projectiveSpace k 1)) =
      _root_.genericPoint (projectiveSpace k 1) := by
    rw [projectiveGraphMorphism_fst]
    all_goals simp
  rw [Scheme.comp_base_apply] at h
  exact h

/-- **The same after the translation `τ_{-c} × τ_0`.** `productTranslation_fst` moves the first
coordinate by `projectiveTranslation (-c)`, an isomorphism, which fixes the generic point. -/
theorem translatedGraphGenericPoint_fst (p : ℕ) (c : k) :
    (rulingProjection (k := k) 0).base
        ((verticalTranslation (k := k) c).inv.base
          ((projectiveGraphMorphism (k := k) p).base
            (_root_.genericPoint (projectiveSpace k 1)))) =
      _root_.genericPoint (projectiveSpace k 1) := by
  have hmor : (verticalTranslation (k := k) c).inv ≫ rulingProjection 0 =
      rulingProjection 0 ≫ projectiveTranslation (-c) := by
    rw [verticalTranslation_inv]
    exact productTranslation_fst (-c) (-(0 : k))
  have hpt := congrArg (fun m : projectiveProduct k ⟶ projectiveSpace k 1 =>
      m.base ((projectiveGraphMorphism (k := k) p).base
        (_root_.genericPoint (projectiveSpace k 1)))) hmor
  simp only [Scheme.comp_base_apply] at hpt
  rw [hpt, graphGenericPoint_fst p]
  exact genericPoint_eq_of_isOpenImmersion (projectiveTranslation (-c))

/-- **The chart of the fibre `x = 0` on which its equation is `1`.** The divisor is glued from
`x` on `rulingOpen 0 0` and `1` on `rulingOpen 0 1`; this is the second of those, whose
`represents` obligation is exactly `verticalZeroDivisor_restrict_ruling 1`. -/
def verticalZeroRulingChart :
    RegularCartierEquationChart (projectiveProduct k) (verticalZeroDivisor (k := k)) where
  chart :=
    { openSet := rulingOpen (k := k) 0 1
      nonempty := rulingOpen_nonempty 0 1
      equation := 1
      represents := verticalZeroDivisor_restrict_ruling 1 }
  coefficient := 1
  germ_eq := by simp

/-- A point whose first coordinate is the generic point of `P¹` lies in `rulingOpen 0 1`:
that open is `rulingProjection 0 ⁻¹ᵁ chartOpen k 1`, and the generic point lies in every
nonempty open. -/
theorem mem_rulingOpen_one_of_fst_generic (w : projectiveProduct k)
    (hw : (rulingProjection (k := k) 0).base w = _root_.genericPoint (projectiveSpace k 1)) :
    w ∈ rulingOpen (k := k) 0 1 := by
  show (rulingProjection (k := k) 0).base w ∈ chartOpen k 1
  rw [hw]
  letI : Nonempty (chartOpen k 1) :=
    ⟨⟨(rulingProjection (k := k) 0).base (_root_.genericPoint (projectiveProduct k)),
      rulingGeneric_mem 0 1⟩⟩
  exact genericPoint_mem_nonempty_open (projectiveSpace k 1) (chartOpen k 1)

/-- **Any such point is off the support of the fibre `x = 0`**: on `rulingOpen 0 1` the regular
coefficient is `1`, whose germ is a unit. -/
theorem not_mem_support_verticalZero_of_fst_generic (w : projectiveProduct k)
    (hw : (rulingProjection (k := k) 0).base w = _root_.genericPoint (projectiveSpace k 1)) :
    w ∉ (effectiveCartierIdealDataOfRegularEquations (projectiveProduct k)
      (verticalZeroDivisor (k := k)) verticalZeroDivisor_hasRegularEquations).support := by
  intro h
  rw [mem_support_iff_not_isUnit_germ (verticalZeroDivisor (k := k))
    verticalZeroDivisor_hasRegularEquations (verticalZeroRulingChart (k := k)) w
    (mem_rulingOpen_one_of_fst_generic w hw)] at h
  apply h
  show IsUnit ((projectiveProduct k).presheaf.germ (rulingOpen (k := k) 0 1) w
    (mem_rulingOpen_one_of_fst_generic w hw)
    (1 : Γ(projectiveProduct k, rulingOpen (k := k) 0 1)))
  have h1 : (projectiveProduct k).presheaf.germ (rulingOpen (k := k) 0 1) w
      (mem_rulingOpen_one_of_fst_generic w hw)
      (1 : Γ(projectiveProduct k, rulingOpen (k := k) 0 1)) = 1 := by simp
  rw [h1]
  exact isUnit_one

/-- **The generic point of the graph lies off the support of the vertical fibre `x = c`**, for
every `c` — the fact `(graphStrictPrimeCurve …).NotInSupport` reduces to. -/
theorem graphGenericPoint_not_mem_support_verticalFiberAt (p : ℕ) (c : k) :
    (projectiveGraphMorphism (k := k) p).base (_root_.genericPoint (projectiveSpace k 1)) ∉
      (effectiveCartierIdealDataOfRegularEquations (projectiveProduct k)
        (verticalFiberDivisorAt (k := k) c)
        (verticalFiberDivisorAt_hasRegularEquations c)).support := by
  intro h
  -- `verticalFiberDivisorAt c` *is* `pullbackDivisor (verticalTranslation c).inv …` by definition,
  -- so the criterion applies to `h` up to defeq; `.mp` sees through the folded `def` where `rw`
  -- would need equation lemmas it does not supply.
  have h' := (mem_support_pullbackDivisor_iff (verticalTranslation (k := k) c).inv
    (verticalZeroDivisor (k := k)) verticalZeroDivisor_hasRegularEquations
    ((projectiveGraphMorphism (k := k) p).base
      (_root_.genericPoint (projectiveSpace k 1)))).mp h
  exact not_mem_support_verticalZero_of_fst_generic _ (translatedGraphGenericPoint_fst p c) h'

end KltDP.Examples.FrobeniusGraphGenericPointOffFiber

namespace KltDP.Examples

open KltDP.Geometry
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism
open FrobeniusVerticalFiberClass FrobeniusVerticalFiberTranslated
open FrobeniusGraphGenericPointOffFiber

-- Both instances again: a `local instance` is scoped to its namespace block.
local instance offFiberProductIntegral' {k : Type u} [Field k] : IsIntegral (projectiveProduct k) :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

local instance offFiberLineIntegral' {k : Type u} [Field k] : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

/-- **F29: the generic point of the graph `y = x^p` lies off every vertical fibre `x = c`.**
Together with `f29_graph_strict_generic_point` and `not_mem_support_pullbackDivisor` this is the
`NotInSupport` hypothesis for the strict transform `B` against the stage vertical divisor. -/
theorem f29_graph_generic_point_off_vertical_fiber (k : Type u) [Field k] (p : ℕ) (c : k) :
    (projectiveGraphMorphism (k := k) p).base (_root_.genericPoint (projectiveSpace k 1)) ∉
      (effectiveCartierIdealDataOfRegularEquations (projectiveProduct k)
        (verticalFiberDivisorAt (k := k) c)
        (verticalFiberDivisorAt_hasRegularEquations c)).support :=
  graphGenericPoint_not_mem_support_verticalFiberAt p c

/-- The statement has exactly one universe parameter. -/
theorem f29_graph_generic_point_off_vertical_fiber_universe_check (k : Type u) [Field k] (p : ℕ)
    (c : k) : True := by
  have _ := f29_graph_generic_point_off_vertical_fiber.{u} k p c
  trivial

end KltDP.Examples
