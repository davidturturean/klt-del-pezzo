import KltDP.Geometry.SurfaceFiniteness
import KltDP.Support.EqualityNumbers

/-!
# Support obligation U-SINGULAR-COUNT: a bound on points, not on exceptional vertices

Manuscript `source/manuscript.tex` lines 90–104: "We consider the number
`n(X) := #Sing(X)` of distinct singular points, rather than the number of
exceptional curves or the length of a singular subscheme."

Two clauses are recorded here.

* The public count used by this formalization is the accepted
  `NormalProjectiveSurface.singularPointCount`: the cardinality of the actual
  finite set of nonregular points of the surface (finiteness is the accepted
  F01 theorem `normalSurface_singularLocus_finite`, conditional only on the
  admitted Stacks 07PJ(1) literal). `singularPointCount_eq_card_singularPoints`
  and `mem_singularPoints_iff_not_regular` restate that it counts distinct
  nonregular points and nothing else.
* The manuscript's test case (plan strategy: "ten curves, three edges, seven
  singular points" on `S_{3,3}`) is the numerical statement, proved in
  `KltDP.Support.EqualityNumbers`, that the explicit exceptional matrix has ten
  vertices and its dual graph three edges and seven connected components, so
  the vertex count and the block count differ.

The bijection between connected exceptional blocks of a minimal resolution and
the distinct singular points of the surface (F16) is not proved here; without
it, `10 ≠ 7` is a statement about the explicit graph only.
-/

namespace KltDP.Support

open KltDP.Geometry

universe u

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-- The public count is the cardinality of the actual finite set of singular points. -/
theorem singularPointCount_eq_card_singularPoints :
    X.singularPointCount = X.singularPoints.card := rfl

/-- Membership in the counted set is exactly nonregularity of the stalk. -/
theorem mem_singularPoints_iff_not_regular (x : X.Point) :
    x ∈ X.singularPoints ↔ ¬ RegularLocal (X.stalk x) :=
  X.mem_singularPoints x

/-- **Test case.** On the explicit equality matrix, ten exceptional vertices, three
edges, seven blocks: the vertex count and the block count are different numbers. -/
theorem equality_vertices_ne_blocks :
    Fintype.card EqualityNumbers.Index = 10 ∧
    EqualityNumbers.dualGraph.edgeFinset.card = 3 ∧
    Nat.card EqualityNumbers.dualGraph.ConnectedComponent = 7 ∧
    Fintype.card EqualityNumbers.Index ≠ Nat.card EqualityNumbers.dualGraph.ConnectedComponent := by
  refine ⟨EqualityNumbers.card_index, EqualityNumbers.dualGraph_card_edgeFinset,
    EqualityNumbers.card_connectedComponent, ?_⟩
  rw [EqualityNumbers.card_index, EqualityNumbers.card_connectedComponent]
  norm_num

/-- **U-SINGULAR-COUNT**, definitional and numerical clauses. -/
theorem u_singular_count :
    (∀ (X : NormalProjectiveSurface k), X.singularPointCount = X.singularPoints.card ∧
      ∀ x : X.Point, x ∈ X.singularPoints ↔ ¬ RegularLocal (X.stalk x)) ∧
    Fintype.card EqualityNumbers.Index ≠ Nat.card EqualityNumbers.dualGraph.ConnectedComponent :=
  ⟨fun X => ⟨rfl, X.mem_singularPoints⟩, equality_vertices_ne_blocks.2.2.2⟩

end KltDP.Support
