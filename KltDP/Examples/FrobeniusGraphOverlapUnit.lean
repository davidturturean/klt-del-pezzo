import KltDP.Geometry.TransitionUnitSections
import KltDP.Geometry.RationalFunctionSheaf
import KltDP.Examples.FrobeniusBlowupContact
import KltDP.Examples.FrobeniusProjectivePoints
import KltDP.Examples.FrobeniusProjectiveMorphism
import KltDP.Examples.FrobeniusGraphPicardClassIntegral
import KltDP.Examples.FrobeniusGraphPicardClassFrames
import KltDP.Examples.FrobeniusGraphPicardClassRational
import KltDP.Examples.FrobeniusGraphPicardClassEquationTransition
import KltDP.Examples.FrobeniusStrictTransformFiberRowsExponents
import KltDP.Examples.FrobeniusGraphGeneratorEquation

/-!
# Step (b): the atlas transition unit on the overlap is `−x^{−q}·y^{−1}`

`FrobeniusGraphGeneratorEquation` proved step (a) concretely: the transition unit of the accepted
graph atlas is the ratio of the two actual graph equations, `g_{ij} · e_i = e_j`. This module
evaluates that ratio on the overlap of the two diagonal charts.

The evaluation needs **no new geometry**: the accepted tree already computes the ratio, in the
function field, as `FrobeniusGraphPicardClassEquationTransition.reverse_graph_equation`:

    chartFunctionFieldMap 1 (v − u^q) = −((rationalX)⁻¹ ^ q * (rationalY)⁻¹) * graphFunction q

and `graphFunction q` is by definition `chartFunctionFieldMap 0 (v − u^q)`, i.e. the germ of
`diagonalSection q 0` (`graphFunction_eq_original_section`, `rfl`); the same unfolding identifies
the germ of `diagonalSection q 1` with `chartFunctionFieldMap 1 (v − u^q)`. So applying the generic
point germ to step (a) and cancelling the nonzero `graphFunction q` gives

* **`graphAtlasUnits_germ_mul`** : `germ(g₀₁) * graphFunction q = chartFunctionFieldMap 1 (v − u^q)`;
* **`graphAtlasUnits_germ_eq`** : `germ(g₀₁) = −((rationalX)⁻¹ ^ q * (rationalY)⁻¹)`.

**A correction this module records.** An earlier lane note predicted `g₀₁ = −v`. That is wrong: the
second diagonal chart inverts *both* ruling coordinates, so the ratio carries `x^{−q}` as well and is
an inverse, `−x^{−q} y^{−1}`. At `q = 0` it is `−(rationalY)⁻¹`, not `−v`. The sign of the exponent
is what the `b`-row depends on, and only the corrected form is consistent with the accepted target
`c · T^{−p}` of `ProjectiveLineIdealLineDegree`.

**Deliberately not proved here.** Nothing is pulled back along a section: step (c) — reading this
unit on `P¹` through `projectiveGraphMorphism p` (giving `−t^{−p}`) or through the swapped section
(giving `−t^{−1}`) — is untouched, and no Laurent form or exponent value is claimed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Examples.FrobeniusGraphOverlapUnit

open KltDP.Geometry KltDP.Geometry.TransitionUnitGluing
open FrobeniusBlowupContact FrobeniusProjectivePoints FrobeniusProjectiveMorphism
open FrobeniusGraphPicardClassIntegral FrobeniusGraphPicardClassFrames
open FrobeniusGraphPicardClassRational FrobeniusGraphPicardClassEquationTransition
open FrobeniusStrictTransformFiberRowsExponents FrobeniusGraphGeneratorEquation

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k]

local instance overlapUnitProductIntegral : IsIntegral (projectiveProduct k) :=
  projectiveProduct_isIntegral

local instance diagonalOverlap_nonempty :
    Nonempty ((diagonalOpen (k := k) 0 ⊓ diagonalOpen (k := k) 1 : (projectiveProduct k).Opens)) :=
  ⟨⟨genericPoint (projectiveProduct k),
    genericPoint_mem_nonempty_open (projectiveProduct k) (diagonalOpen 0),
    genericPoint_mem_nonempty_open (projectiveProduct k) (diagonalOpen 1)⟩⟩

/-- The generic-point germ of a restriction is the germ of the section itself. The accepted proof of
this lives in `QuadraticCoverFunctionFieldBranch` but is `private`; the recipe is the one the
accepted `CartierEquationUnits.germToFunctionField_map_unit_restriction` uses for units. -/
theorem germToFunctionField_res {U V : (projectiveProduct k).Opens} [Nonempty U] [Nonempty V]
    (h : V ≤ U) (a : Γ(projectiveProduct k, U)) :
    (projectiveProduct k).germToFunctionField V (res (projectiveProduct k) h a) =
      (projectiveProduct k).germToFunctionField U a := by
  change (projectiveProduct k).germToFunctionField V
      (((projectiveProduct k).presheaf.map (homOfLE h).op) a) = _
  exact (projectiveProduct k).presheaf.germ_res_apply (homOfLE h)
    (genericPoint (projectiveProduct k))
    (genericPoint_mem_nonempty_open (projectiveProduct k) V) a

/-- Step (a), read at the generic point: the transition unit times the first graph equation is the
second graph equation, as rational functions. The hypotheses are named binders of explicit type, as
in the landed step (a), so that `res` has its source open pinned before its argument is elaborated. -/
theorem graphAtlasUnits_germ_mul (q : ℕ) {W : (projectiveProduct k).Opens} [Nonempty W]
    (hW0 : W ≤ graphAtlasCover q ⟨some 0⟩) (hW1 : W ≤ graphAtlasCover q ⟨some 1⟩) :
    (projectiveProduct k).germToFunctionField W
          (res (projectiveProduct k) (le_inf hW0 hW1)
            (graphAtlasUnits (k := k) q ⟨some 0⟩ ⟨some 1⟩)) *
        graphFunction (k := k) q =
      chartFunctionFieldMap (k := k) 1 (vCoord - uCoord ^ q) := by
  have h := graphAtlasUnits_mul_diagonalSection (k := k) q 0 1 hW0 hW1
  have hg := congrArg (fun s : Γ(projectiveProduct k, W) =>
      (projectiveProduct k).germToFunctionField W s) h
  simp only [map_mul] at hg
  haveI : Nonempty (graphAtlasCover (k := k) q ⟨some 0⟩) := diagonalOpen_nonempty 0
  haveI : Nonempty (graphAtlasCover (k := k) q ⟨some 1⟩) := diagonalOpen_nonempty 1
  rw [germToFunctionField_res hW0 (diagonalSection (k := k) q 0),
    germToFunctionField_res hW1 (diagonalSection (k := k) q 1)] at hg
  exact hg

/-- **Step (b): the transition unit of the graph atlas is `−x^{−q}·y^{−1}` at the generic point.** -/
theorem graphAtlasUnits_germ_eq (q : ℕ) {W : (projectiveProduct k).Opens} [Nonempty W]
    (hW0 : W ≤ graphAtlasCover q ⟨some 0⟩) (hW1 : W ≤ graphAtlasCover q ⟨some 1⟩) :
    (projectiveProduct k).germToFunctionField W
        (res (projectiveProduct k) (le_inf hW0 hW1)
          (graphAtlasUnits (k := k) q ⟨some 0⟩ ⟨some 1⟩)) =
      -((rationalX (k := k))⁻¹ ^ q * (rationalY (k := k))⁻¹) := by
  have h := graphAtlasUnits_germ_mul (k := k) q hW0 hW1
  rw [reverse_graph_equation] at h
  exact mul_right_cancel₀ (graphFunction_ne_zero q) h

/-- **Step (b) of the F29 ruling computation.** The transition unit of the accepted graph atlas
between the two diagonal charts is the rational function `−x^{−q}·y^{−1}`. Stated in this namespace
because it needs the integrality instance in scope. -/
theorem f29_graph_overlap_unit (q : ℕ) {W : (projectiveProduct k).Opens} [Nonempty W]
    (hW0 : W ≤ graphAtlasCover q ⟨some 0⟩) (hW1 : W ≤ graphAtlasCover q ⟨some 1⟩) :
    (projectiveProduct k).germToFunctionField W
        (res (projectiveProduct k) (le_inf hW0 hW1)
          (graphAtlasUnits (k := k) q ⟨some 0⟩ ⟨some 1⟩)) =
      -((rationalX (k := k))⁻¹ ^ q * (rationalY (k := k))⁻¹) :=
  graphAtlasUnits_germ_eq q hW0 hW1

/-- The bundle has exactly one universe parameter. -/
theorem f29_graph_overlap_unit_universe_check (q : ℕ) {W : (projectiveProduct k).Opens}
    [Nonempty W] (hW0 : W ≤ graphAtlasCover q ⟨some 0⟩)
    (hW1 : W ≤ graphAtlasCover q ⟨some 1⟩) : True := by
  have _ := f29_graph_overlap_unit.{u} q hW0 hW1
  trivial

end KltDP.Examples.FrobeniusGraphOverlapUnit
