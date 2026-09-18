import KltDP.Examples.FrobeniusActualGraphRuling
import KltDP.Examples.FrobeniusProjectiveSquareInseparable

/-!
# The original strict-graph ruling under its projective-line parametrization

The source of the morphism below is `P¹`. It is the original second ruling
restricted to the original strict graph, precomposed with the inverse of
the proved original graph isomorphism. Its function-field algebra uses
the literal generic stalk map of this parametrized morphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusActualParametrizedGraphInseparable

open KltDP.Geometry FrobeniusGraphClosed FrobeniusProjectiveMorphism
  FrobeniusMultiCentreSurface FrobeniusMultiCentreGraphFiber
  FrobeniusMultiCentreGraphProjectiveLine FrobeniusActualGraphRuling

variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]

local instance primeTwo : Fact (2 : ℕ).Prime := ⟨Nat.prime_two⟩

local instance rulingLineIntegral : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

/-- The original restricted ruling, with source parametrized by `P¹`. -/
def parametrizedRuling (n : ℕ) (a : Fin n → k) :
    projectiveSpace k 1 ⟶ projectiveSpace k 1 :=
  (globalGraphIsoProjectiveLine 2 n a).inv ≫
    (graphStrictι 2 n a ≫ (multiProjection 2 n a ≫ secondProjection))

theorem parametrizedRuling_eq_square (n : ℕ) (a : Fin n → k) :
    parametrizedRuling n a = projectivePowerMorphism 2 := by
  rw [parametrizedRuling, strict_graph_second_ruling, Iso.inv_hom_id_assoc]

instance parametrizedRuling_generic (n : ℕ) (a : Fin n → k) :
    GenericPointPreserving (parametrizedRuling n a) := by
  rw [parametrizedRuling_eq_square]
  infer_instance

/-- Degree two for the actual parametrized ruling's generic stalk map. -/
theorem parametrizedRuling_finrank (n : ℕ) (a : Fin n → k) :
    letI : Algebra (projectiveSpace k 1).functionField (projectiveSpace k 1).functionField :=
      (functionFieldMap (parametrizedRuling n a)).hom.toAlgebra
    letI : Module (projectiveSpace k 1).functionField (projectiveSpace k 1).functionField :=
      Algebra.toModule
    Module.finrank (projectiveSpace k 1).functionField
      (projectiveSpace k 1).functionField = 2 := by
  simpa only [parametrizedRuling_eq_square] using
    FrobeniusSquareGenericMap.projectiveSquare_finrank k

/-- Pure inseparability for the same original parametrized generic map. -/
theorem parametrizedRuling_isPurelyInseparable (n : ℕ) (a : Fin n → k) :
    letI : Algebra (projectiveSpace k 1).functionField (projectiveSpace k 1).functionField :=
      (functionFieldMap (parametrizedRuling n a)).hom.toAlgebra
    IsPurelyInseparable (projectiveSpace k 1).functionField
      (projectiveSpace k 1).functionField := by
  simpa only [parametrizedRuling_eq_square] using
    FrobeniusSquareGenericMap.projectiveSquare_isPurelyInseparable k

end KltDP.Examples.FrobeniusActualParametrizedGraphInseparable
