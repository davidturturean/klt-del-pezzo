import KltDP.Geometry.TransitionUnitGenerator
import KltDP.Geometry.SchemeConormal
import KltDP.Geometry.TransitionUnitSections
import KltDP.Examples.FrobeniusProjectivePoints
import KltDP.Examples.FrobeniusProjectiveMorphism
import KltDP.Examples.FrobeniusGraphPicardClassFrames
import KltDP.Examples.FrobeniusStrictTransformFiberRowsExponents

/-!
# Step (a): the graph atlas transition unit is the ratio of the two diagonal generators

The F29 ruling rows both reduce to the Laurent form of a pulled-back transition unit of the accepted
atlas `originalGraphAtlas q` of the graph ideal line. This module supplies **step (a)** of that
computation: the atlas transition unit is the ratio of the two chart generators.

It is the instantiation of the generic `KltDP.Geometry.TransitionUnitGenerator` at the accepted
atlas, with `ι` the accepted ideal inclusion `schemeKernelIdealι (projectiveGraphMorphism q)`:

* `graphIdealGenerator q i hWi`, the generator of the graph ideal on atlas chart `i`;
* **`graphAtlasUnits_mul_graphIdealGenerator`**: `graphAtlasUnits q i j · d_i = d_j` on any common
  open — in particular, on the overlap of the two diagonal charts, `g₀₁ · e₀ = e₁`.

**Deliberately not proved here.** The generators are not identified with the concrete equations
`diagonalEquation q i` (the accepted `diagonalGlobalFrameIso_inclusion` is the input for that), and
no Laurent form is computed. Steps (b) and (c) — evaluating the ratio as `−v` on the overlap and
pulling it back along the two sections — are untouched.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Examples.FrobeniusGraphAtlasGenerator

open KltDP.Geometry KltDP.Geometry.TransitionUnitGluing
open KltDP.Geometry.TransitionUnitGenerator
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism
open FrobeniusGraphPicardClassFrames FrobeniusStrictTransformFiberRowsExponents

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k]

/-- The generator of the graph ideal on chart `i` of the accepted atlas. -/
def graphIdealGenerator (q : ℕ) (i : ULift.{u} (Option (Fin 2)))
    {W : (projectiveProduct k).Opens} (hWi : W ≤ graphAtlasCover q i) :
    Γ(projectiveProduct k, W) :=
  chartGenerator (projectiveProduct k) (schemeKernelIdeal (projectiveGraphMorphism (k := k) q))
    (originalGraphAtlas q) (schemeKernelIdealι (projectiveGraphMorphism (k := k) q)) i hWi

/-- **Step (a): `g_{ij} · d_i = d_j`** for the accepted graph atlas. Specialised to the two diagonal
charts on their overlap this is `g₀₁ · e₀ = e₁`. -/
theorem graphAtlasUnits_mul_graphIdealGenerator (q : ℕ) (i j : ULift.{u} (Option (Fin 2)))
    {W : (projectiveProduct k).Opens} (hWi : W ≤ graphAtlasCover q i)
    (hWj : W ≤ graphAtlasCover q j) :
    res (projectiveProduct k) (le_inf hWi hWj) (graphAtlasUnits (k := k) q i j) *
        graphIdealGenerator q i hWi = graphIdealGenerator q j hWj :=
  transitionUnits_mul_chartGenerator (projectiveProduct k)
    (schemeKernelIdeal (projectiveGraphMorphism (k := k) q)) (originalGraphAtlas q)
    (schemeKernelIdealι (projectiveGraphMorphism (k := k) q)) i j hWi hWj

end KltDP.Examples.FrobeniusGraphAtlasGenerator

namespace KltDP.Examples

open KltDP.Geometry KltDP.Geometry.TransitionUnitGluing
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism
open FrobeniusStrictTransformFiberRowsExponents FrobeniusGraphAtlasGenerator

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- **Step (a) of the F29 ruling computation.** The transition unit of the accepted graph atlas
between any two charts is the ratio of the corresponding ideal generators. -/
theorem f29_graph_atlas_unit_ratio (k : Type u) [Field k] (q : ℕ)
    (i j : ULift.{u} (Option (Fin 2))) {W : (projectiveProduct k).Opens}
    (hWi : W ≤ graphAtlasCover q i) (hWj : W ≤ graphAtlasCover q j) :
    res (projectiveProduct k) (le_inf hWi hWj) (graphAtlasUnits (k := k) q i j) *
        graphIdealGenerator q i hWi = graphIdealGenerator q j hWj :=
  graphAtlasUnits_mul_graphIdealGenerator q i j hWi hWj

end KltDP.Examples
