import KltDP.Examples.FrobeniusGraphPicardClassDiagonal

/-!
# Original graph points in the mixed product charts

The graph's first projection is the original parameter. If a graph point
lies in product chart (i,j), that parameter is in chart i. The already
proved power-map compatibility therefore places the same graph point in
diagonal chart (i,i). This is the actual range statement needed to compare
the mixed-chart Cartier equations; it does not assert their class identity.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusGraphPicardClassMixedCover

open KltDP.Geometry ProjectiveLineComparison
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism FrobeniusGraphClosed
open FrobeniusBlowupContact FrobeniusBlowupChartIteration FrobeniusProductPlaneChart
open FrobeniusGraphPicardClassCharts FrobeniusGraphPicardClassPowerCharts

variable {k : Type u} [Field k]

/-- A point of the original graph in chart (i,j) is in diagonal chart (i,i).
The proof uses the original first projection and original diagonal graph map. -/
theorem graph_range_productChart_same_first (p : ℕ) (i j : Fin 2)
    (x : projectiveProduct k)
    (hgraph : x ∈ Set.range (projectiveGraphMorphism (k := k) p).base)
    (hchart : x ∈ Set.range (productChart (k := k) i j).base) :
    x ∈ Set.range (productChart (k := k) i i).base := by
  obtain ⟨q, rfl⟩ := hgraph
  obtain ⟨z, hz⟩ := hchart
  let a : Spec (CommRingCat.of (Polynomial k)) :=
    (Spec.map (CommRingCat.ofHom firstCoordinateMap)).base z
  have hq : (polynomialChartMap k i).base a = q := by
    calc
      _ = firstProjection.base ((productChart i j).base z) := by
        exact (congrArg (fun f : Spec (CommRingCat.of (planeRing k)) ⟶
          projectiveSpace k 1 => f.base z) (productChart_fst (k := k) i j)).symm
      _ = firstProjection.base ((projectiveGraphMorphism p).base q) :=
        congrArg firstProjection.base hz
      _ = q := by
        change (projectiveGraphMorphism p ≫ firstProjection).base q = q
        rw [projectiveGraphMorphism_fst]
        rfl
  refine ⟨(curveInPlane p).base a, ?_⟩
  calc
    _ = (projectiveGraphMorphism p).base ((polynomialChartMap k i).base a) :=
      congrArg (fun f : Spec (CommRingCat.of (Polynomial k)) ⟶ projectiveProduct k =>
        f.base a) (curveInPlane_diagonalChart p i)
    _ = _ := congrArg (projectiveGraphMorphism p).base hq

/-- The portion of an original product chart outside its matching diagonal
contains no point of the original closed graph. -/
theorem productChart_outside_diagonal_disjoint_graph (p : ℕ) (i j : Fin 2) :
    Disjoint (Set.range (productChart (k := k) i j).base \
      Set.range (productChart (k := k) i i).base)
      (Set.range (projectiveGraphMorphism (k := k) p).base) := by
  apply Set.disjoint_left.mpr
  intro x hx hgraph
  exact hx.2 (graph_range_productChart_same_first p i j x hgraph hx.1)

end KltDP.Examples.FrobeniusGraphPicardClassMixedCover
