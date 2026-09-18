import KltDP.Examples.FrobeniusMultiCentreGraphProjectiveLine

/-!
# The original strict graph carries the coordinate-square ruling

Identify the entire original second-ruling morphism on the strict graph
through its proved projective-line isomorphism. This equation preserves
both the original graph inclusion and the original power morphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusActualGraphRuling

open KltDP.Geometry FrobeniusGraphClosed FrobeniusProjectiveMorphism
  FrobeniusMultiCentreSurface FrobeniusMultiCentreGraphFiber
  FrobeniusMultiCentreGraphProjectiveLine

variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]

local instance primeTwo : Fact (2 : ℕ).Prime := ⟨Nat.prime_two⟩

/-- On the original strict graph, the original ruling is precisely the
coordinate-square map under the original graph isomorphism. -/
theorem strict_graph_second_ruling (n : ℕ) (a : Fin n → k) :
    graphStrictι 2 n a ≫ (multiProjection 2 n a ≫ secondProjection) =
      (globalGraphIsoProjectiveLine 2 n a).hom ≫ projectivePowerMorphism 2 := by
  rw [← globalGraphIsoProjectiveLine_hom_inclusion, Category.assoc,
    ← Category.assoc (globalGraphParametrization 2 n a),
    globalGraphParametrization_projection, projectiveGraphMorphism_snd]

end KltDP.Examples.FrobeniusActualGraphRuling
