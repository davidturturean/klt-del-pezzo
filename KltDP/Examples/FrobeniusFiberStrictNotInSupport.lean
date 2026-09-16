import KltDP.Examples.FrobeniusGraphStrictNotInSupport
import KltDP.Examples.FrobeniusStrictTransformIsoProjectiveLine
import KltDP.Examples.FrobeniusGraphPicardClassZeroFiber
import KltDP.Examples.FrobeniusFiberClosure
import KltDP.Geometry.PrimeCurveOfClosedImmersion
import KltDP.Geometry.PrimeDivisor

/-!
# `F̃ ⊄ Supp(x = c)`: the second `NotInSupport` derived from geometry (BRIEF45)

The companion of `FrobeniusGraphStrictNotInSupport` for the strict transform `F̃` of the fibre. It costs
almost nothing, for a reason recorded when the graph case landed: the off-support lemma
`not_mem_support_verticalZero_of_fst_generic` was stated for an **arbitrary** point of `P¹ × P¹` whose
first coordinate is the generic point of `P¹`, not for the graph. So no second off-support argument is
needed — only the identification of `F̃`'s generic point, which is the accepted
`fiberStrictIsoProjectiveLine` replayed exactly as `FrobeniusGraphStrictGenericPoint` replays
`graphStrictIsoProjectiveLine`.

The decisive fact is that `fiberStrictIsoProjectiveLine_hom_comp` lands on
**`horizontalFiberMorphism (0 : k)`** — the fibre `v = 0`, whose parameterisation is `u = t, v = 0`.
Its first coordinate is therefore the parameter, recorded accepted as
`horizontalFiberMorphism_fst : horizontalFiberMorphism a ≫ firstProjection = 𝟙 (projectiveSpace k 1)`
— the very same shape as `projectiveGraphMorphism_fst`. `F̃` is a *horizontal* fibre, so it crosses every
vertical fibre transversally, exactly as the graph does.

* `fiberGenericPoint_fst`, `translatedFiberGenericPoint_fst` — the first coordinate, before and after
  the translation `τ_{-c} × τ_0`;
* `fiberGenericPoint_not_mem_support_verticalFiberAt` — the horizontal fibre's generic point is off
  `Supp(x = c)`;
* `genericPoint_fiberStrictPrimeCurve`, `toInitial_genericPoint_fiberStrictPrimeCurve` — `F̃`'s generic
  point and its blowdown image;
* **`fiberStrict_notInSupport`** — the `NotInSupport` itself.

As for the graph, this holds for **every** `c` (including `c = 0`); `c ≠ 0` is a downstream condition.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusFiberStrictNotInSupport

-- `KltDP.Geometry.NormalProjectiveSurface.PrimeCurve` is deliberately NOT opened: `NotInSupport`,
-- `genericPoint` and `closure_genericPoint` are all reached by dot notation on the prime curve, and
-- opening it would shadow the topological `_root_.genericPoint` used throughout.
open KltDP.Geometry
open KltDP.Geometry.PrimeCurveOfClosedImmersion
open KltDP.Geometry.ProjectiveLineTranslation
open FrobeniusProjectivePoints FrobeniusGraphClosed
open FrobeniusGlobalBlowupStages FrobeniusStageSurface
open FrobeniusStrictTransformPrimeCurves FrobeniusStrictTransformIsoProjectiveLine
open FrobeniusFiberClosure FrobeniusGraphPicardClassZeroFiber
open FrobeniusGraphPicardClassRulingCoordinates
open FrobeniusVerticalFiberClass FrobeniusVerticalFiberTranslated
open FrobeniusStageVerticalDivisor FrobeniusGraphGenericPointOffFiber
open ProjectiveProductTranslation
open FrobeniusTowerFunctionField FrobeniusTowerFunctionField.PlaneChartedScheme

variable {k : Type u} [Field k]

local instance fiberNotInSupportProductIntegral : IsIntegral (projectiveProduct k) :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

local instance fiberNotInSupportInitialIntegral :
    IsIntegral (projectiveProductInitial (k := k)).carrier :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

local instance fiberNotInSupportStageIntegral (m : ℕ) :
    IsIntegral (projectiveContactStage (k := k) m) :=
  instStageIsIntegral (projectiveProductInitial (k := k)) m

local instance fiberNotInSupportLineIntegral : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

/-- **The first coordinate of the horizontal fibre's generic point is `P¹`'s generic point.**
The accepted `horizontalFiberMorphism_fst` read at a point; `(𝟙 X).base` is never written, because
`𝟙 X` elaborates with head `Quiver.Hom` and dot notation cannot resolve on it. -/
theorem fiberGenericPoint_fst :
    (rulingProjection (k := k) 0).base
        ((horizontalFiberMorphism (0 : k)).base (_root_.genericPoint (projectiveSpace k 1))) =
      _root_.genericPoint (projectiveSpace k 1) := by
  have h : ((horizontalFiberMorphism (0 : k)) ≫ firstProjection).base
      (_root_.genericPoint (projectiveSpace k 1)) =
      _root_.genericPoint (projectiveSpace k 1) := by
    rw [horizontalFiberMorphism_fst]
    all_goals simp
  rw [Scheme.comp_base_apply] at h
  exact h

/-- **The same after the translation `τ_{-c} × τ_0`.** -/
theorem translatedFiberGenericPoint_fst (c : k) :
    (rulingProjection (k := k) 0).base
        ((verticalTranslation (k := k) c).inv.base
          ((horizontalFiberMorphism (0 : k)).base
            (_root_.genericPoint (projectiveSpace k 1)))) =
      _root_.genericPoint (projectiveSpace k 1) := by
  have hmor : (verticalTranslation (k := k) c).inv ≫ rulingProjection 0 =
      rulingProjection 0 ≫ projectiveTranslation (-c) := by
    rw [verticalTranslation_inv]
    exact productTranslation_fst (-c) (-(0 : k))
  have hpt := congrArg (fun m : projectiveProduct k ⟶ projectiveSpace k 1 =>
      m.base ((horizontalFiberMorphism (0 : k)).base
        (_root_.genericPoint (projectiveSpace k 1)))) hmor
  simp only [Scheme.comp_base_apply] at hpt
  rw [hpt, fiberGenericPoint_fst]
  exact genericPoint_eq_of_isOpenImmersion (projectiveTranslation (-c))

/-- **The horizontal fibre's generic point lies off the vertical fibre `x = c`.** The off-support
lemma is reused unchanged: it asks only that the first coordinate be generic. -/
theorem fiberGenericPoint_not_mem_support_verticalFiberAt (c : k) :
    (horizontalFiberMorphism (0 : k)).base (_root_.genericPoint (projectiveSpace k 1)) ∉
      (effectiveCartierIdealDataOfRegularEquations (projectiveProduct k)
        (verticalFiberDivisorAt (k := k) c)
        (verticalFiberDivisorAt_hasRegularEquations c)).support := by
  intro h
  have h' := (mem_support_pullbackDivisor_iff (verticalTranslation (k := k) c).inv
    (verticalZeroDivisor (k := k)) verticalZeroDivisor_hasRegularEquations
    ((horizontalFiberMorphism (0 : k)).base
      (_root_.genericPoint (projectiveSpace k 1)))).mp h
  exact not_mem_support_verticalZero_of_fst_generic _ (translatedFiberGenericPoint_fst c) h'

variable [IsAlgClosed k] (n : ℕ)
  (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)

/-- **`F̃`'s prime-curve generic point is the image of the curve scheme's generic point.**
Both are generic points of `Set.range (fiberClosureInclusion …).base`, and a set in a `T0Space` has at
most one — the same bridge `FrobeniusGraphStrictGenericPoint` uses for `B`. -/
theorem genericPoint_fiberStrictPrimeCurve :
    (fiberStrictPrimeCurve n hproj).genericPoint =
      (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1)).base
        (_root_.genericPoint
          (liftedFiberClosure (projectiveProductInitial (k := k)) (n + 1))) := by
  have h₁ : IsGenericPoint ((fiberStrictPrimeCurve n hproj).genericPoint)
      (Set.range (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1)).base) := by
    have h := (fiberStrictPrimeCurve n hproj).closure_genericPoint
    rw [coe_fiberStrictPrimeCurve] at h
    exact h
  have h₂ : IsGenericPoint
      ((fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1)).base
        (_root_.genericPoint
          (liftedFiberClosure (projectiveProductInitial (k := k)) (n + 1))))
      (Set.range (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1)).base) :=
    (range_eq_closure_genericPoint (stageSurface (n + 1) hproj)
      (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1))).symm
  exact h₁.eq h₂

/-- **The blowdown carries `F̃`'s generic point to the horizontal fibre's generic point.** -/
theorem toInitial_genericPoint_fiberStrictPrimeCurve :
    (projectiveContactProjection (k := k) (n + 1)).base
        ((fiberStrictPrimeCurve n hproj).genericPoint) =
      (horizontalFiberMorphism (0 : k)).base (_root_.genericPoint (projectiveSpace k 1)) := by
  rw [genericPoint_fiberStrictPrimeCurve n hproj]
  have hiso : (fiberStrictIsoProjectiveLine (k := k) (n + 1)).hom.base
      (_root_.genericPoint
        (liftedFiberClosure (projectiveProductInitial (k := k)) (n + 1))) =
        _root_.genericPoint (projectiveSpace k 1) :=
    genericPoint_eq_of_isOpenImmersion (fiberStrictIsoProjectiveLine (k := k) (n + 1)).hom
  have hcomp := congrArg
    (fun f : liftedFiberClosure (projectiveProductInitial (k := k)) (n + 1) ⟶
        projectiveProduct k =>
      f.base (_root_.genericPoint
        (liftedFiberClosure (projectiveProductInitial (k := k)) (n + 1))))
    (fiberStrictIsoProjectiveLine_hom_comp (k := k) (n + 1))
  simp only [Scheme.comp_base_apply] at hcomp
  rw [hiso] at hcomp
  exact hcomp.symm

/-- The blowdown image of `F̃`'s generic point is off the vertical fibre `x = c`. -/
theorem toInitial_fiberStrictGenericPoint_not_mem_support (c : k) :
    (projectiveContactProjection (k := k) (n + 1)).base
        ((fiberStrictPrimeCurve n hproj).genericPoint) ∉
      (effectiveCartierIdealDataOfRegularEquations (projectiveProduct k)
        (verticalFiberDivisorAt (k := k) c)
        (verticalFiberDivisorAt_hasRegularEquations c)).support := by
  rw [toInitial_genericPoint_fiberStrictPrimeCurve n hproj]
  exact fiberGenericPoint_not_mem_support_verticalFiberAt c

/-- **`F̃` is not contained in the support of the stage vertical fibre `x = c`.** -/
theorem fiberStrict_notInSupport (c : k) :
    (fiberStrictPrimeCurve n hproj).NotInSupport
      (stageVerticalDivisor (k := k) (n + 1) c)
      (stageVerticalDivisor_hasRegularEquations (n + 1) c) :=
  not_mem_support_pullbackDivisor (projectiveContactProjection (k := k) (n + 1))
    (verticalFiberDivisorAt (k := k) c) (verticalFiberDivisorAt_hasRegularEquations c)
    ((fiberStrictPrimeCurve n hproj).genericPoint)
    (toInitial_fiberStrictGenericPoint_not_mem_support n hproj c)

end KltDP.Examples.FrobeniusFiberStrictNotInSupport

namespace KltDP.Examples

open KltDP.Geometry
open FrobeniusProjectivePoints FrobeniusGlobalBlowupStages FrobeniusStageSurface
open FrobeniusStrictTransformPrimeCurves
open FrobeniusVerticalFiberClass FrobeniusVerticalFiberTranslated
open FrobeniusStageVerticalDivisor FrobeniusFiberStrictNotInSupport
open FrobeniusTowerFunctionField FrobeniusTowerFunctionField.PlaneChartedScheme

local instance fiberNotInSupportProductIntegral' {k : Type u} [Field k] :
    IsIntegral (projectiveProduct k) :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

local instance fiberNotInSupportInitialIntegral' {k : Type u} [Field k] :
    IsIntegral (projectiveProductInitial (k := k)).carrier :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

local instance fiberNotInSupportStageIntegral' {k : Type u} [Field k] (m : ℕ) :
    IsIntegral (projectiveContactStage (k := k) m) :=
  instStageIsIntegral (projectiveProductInitial (k := k)) m

local instance fiberNotInSupportLineIntegral' {k : Type u} [Field k] :
    IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

/-- **F29: the strict transform `F̃` of the fibre is not contained in the support of the vertical
fibre `x = c`** — the second `NotInSupport` produced from geometry rather than assumed, for every `c`. -/
theorem f29_fiber_strict_not_in_support (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ)
    (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)
    (c : k) :
    (fiberStrictPrimeCurve n hproj).NotInSupport
      (stageVerticalDivisor (k := k) (n + 1) c)
      (stageVerticalDivisor_hasRegularEquations (n + 1) c) :=
  fiberStrict_notInSupport n hproj c

/-- The statement has exactly one universe parameter. -/
theorem f29_fiber_strict_not_in_support_universe_check (k : Type u) [Field k] [IsAlgClosed k]
    (n : ℕ)
    (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)
    (c : k) : True := by
  have _ := f29_fiber_strict_not_in_support.{u} k n hproj c
  trivial

end KltDP.Examples
