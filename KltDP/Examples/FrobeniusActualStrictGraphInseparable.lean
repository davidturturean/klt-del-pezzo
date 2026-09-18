import KltDP.Examples.FrobeniusActualParametrizedGraphInseparable

/-!
# Degree and inseparability on the actual original strict graph

The generic extension is induced by the literal original graph inclusion
followed by the original second ruling. The proved graph isomorphism
identifies this extension with the parametrized extension over `P¹`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusActualStrictGraphInseparable

open KltDP.Geometry FrobeniusGraphClosed FrobeniusProjectiveMorphism
  FrobeniusMultiCentreSurface FrobeniusMultiCentreGraphFiber
  FrobeniusMultiCentreGraphProjectiveLine FrobeniusActualGraphRuling
  FrobeniusActualParametrizedGraphInseparable

variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]

local instance primeTwo : Fact (2 : ℕ).Prime := ⟨Nat.prime_two⟩

local instance strictLineIntegral : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

instance strictGraphIntegral (n : ℕ) (a : Fin n → k) :
    IsIntegral (graphStrict 2 n a) :=
  PrimeCurveOfClosedImmersion.isIntegral_of_iso_projectiveLine
    (globalGraphIsoProjectiveLine 2 n a)

/-- The restriction has the original strict graph itself as its source. -/
def strictGraphRuling (n : ℕ) (a : Fin n → k) :
    graphStrict 2 n a ⟶ projectiveSpace k 1 :=
  graphStrictι 2 n a ≫ (multiProjection 2 n a ≫ secondProjection)

theorem strictGraphRuling_eq_parametrized (n : ℕ) (a : Fin n → k) :
    strictGraphRuling n a =
      (globalGraphIsoProjectiveLine 2 n a).hom ≫ parametrizedRuling n a := by
  rw [parametrizedRuling_eq_square]
  exact strict_graph_second_ruling n a

instance graphIso_generic (n : ℕ) (a : Fin n → k) :
    GenericPointPreserving (globalGraphIsoProjectiveLine 2 n a).hom :=
  ⟨genericPoint_eq_of_isOpenImmersion _⟩

instance strictGraphRuling_generic (n : ℕ) (a : Fin n → k) :
    GenericPointPreserving (strictGraphRuling n a) := by
  rw [strictGraphRuling_eq_parametrized]
  infer_instance

/-- This equivalence is the original graph isomorphism's generic stalk map. -/
def graphFieldEquiv (n : ℕ) (a : Fin n → k) :
    (projectiveSpace k 1).functionField ≃+* (graphStrict 2 n a).functionField :=
  (OpenImmersionRational.functionFieldIso
    (globalGraphIsoProjectiveLine 2 n a).hom).commRingCatIsoToRingEquiv

private theorem fieldMap_congr {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f g : X ⟶ Y) [GenericPointPreserving f] [GenericPointPreserving g]
    (h : f = g) : functionFieldMap f = functionFieldMap g := by
  subst g
  rfl

theorem graphFieldEquiv_map (n : ℕ) (a : Fin n → k)
    (z : (projectiveSpace k 1).functionField) :
    graphFieldEquiv n a (functionFieldMap (parametrizedRuling n a) z) =
      functionFieldMap (strictGraphRuling n a) z := by
  change functionFieldMap (globalGraphIsoProjectiveLine 2 n a).hom
      (functionFieldMap (parametrizedRuling n a) z) = _
  have hMap : functionFieldMap (strictGraphRuling n a) =
      functionFieldMap (parametrizedRuling n a) ≫
        functionFieldMap (globalGraphIsoProjectiveLine 2 n a).hom :=
    (fieldMap_congr _ _ (strictGraphRuling_eq_parametrized n a)).trans
      (CartierDivisorPullbackComp.functionFieldMap_comp
        (globalGraphIsoProjectiveLine 2 n a).hom (parametrizedRuling n a))
  exact (ConcreteCategory.congr_hom hMap z).symm

/-- An algebra equivalence for the two original ruling-induced actions. -/
def rulingFieldAlgEquiv (n : ℕ) (a : Fin n → k) :
    letI : Algebra (projectiveSpace k 1).functionField (projectiveSpace k 1).functionField :=
      (functionFieldMap (parametrizedRuling n a)).hom.toAlgebra
    letI : Algebra (projectiveSpace k 1).functionField (graphStrict 2 n a).functionField :=
      (functionFieldMap (strictGraphRuling n a)).hom.toAlgebra
    (projectiveSpace k 1).functionField ≃ₐ[(projectiveSpace k 1).functionField]
      (graphStrict 2 n a).functionField := by
  letI : Algebra (projectiveSpace k 1).functionField (projectiveSpace k 1).functionField :=
    (functionFieldMap (parametrizedRuling n a)).hom.toAlgebra
  letI : Algebra (projectiveSpace k 1).functionField (graphStrict 2 n a).functionField :=
    (functionFieldMap (strictGraphRuling n a)).hom.toAlgebra
  exact AlgEquiv.ofRingEquiv (f := graphFieldEquiv n a) (graphFieldEquiv_map n a)

/-- The original strict-graph second ruling has generic degree two. -/
theorem strictGraphRuling_finrank (n : ℕ) (a : Fin n → k) :
    letI : Algebra (projectiveSpace k 1).functionField (graphStrict 2 n a).functionField :=
      (functionFieldMap (strictGraphRuling n a)).hom.toAlgebra
    letI : Module (projectiveSpace k 1).functionField (graphStrict 2 n a).functionField :=
      Algebra.toModule
    Module.finrank (projectiveSpace k 1).functionField
      (graphStrict 2 n a).functionField = 2 := by
  letI : Algebra (projectiveSpace k 1).functionField (projectiveSpace k 1).functionField :=
    (functionFieldMap (parametrizedRuling n a)).hom.toAlgebra
  letI : Module (projectiveSpace k 1).functionField (projectiveSpace k 1).functionField :=
    Algebra.toModule
  letI : Algebra (projectiveSpace k 1).functionField (graphStrict 2 n a).functionField :=
    (functionFieldMap (strictGraphRuling n a)).hom.toAlgebra
  letI : Module (projectiveSpace k 1).functionField (graphStrict 2 n a).functionField :=
    Algebra.toModule
  exact (rulingFieldAlgEquiv n a).toLinearEquiv.finrank_eq.symm.trans
    (parametrizedRuling_finrank n a)

/-- The extension induced by that same original ruling is purely inseparable. -/
theorem strictGraphRuling_isPurelyInseparable (n : ℕ) (a : Fin n → k) :
    letI : Algebra (projectiveSpace k 1).functionField (graphStrict 2 n a).functionField :=
      (functionFieldMap (strictGraphRuling n a)).hom.toAlgebra
    IsPurelyInseparable (projectiveSpace k 1).functionField
      (graphStrict 2 n a).functionField := by
  letI : Algebra (projectiveSpace k 1).functionField (projectiveSpace k 1).functionField :=
    (functionFieldMap (parametrizedRuling n a)).hom.toAlgebra
  letI : Algebra (projectiveSpace k 1).functionField (graphStrict 2 n a).functionField :=
    (functionFieldMap (strictGraphRuling n a)).hom.toAlgebra
  letI : IsPurelyInseparable (projectiveSpace k 1).functionField
      (projectiveSpace k 1).functionField := parametrizedRuling_isPurelyInseparable n a
  exact (rulingFieldAlgEquiv n a).isPurelyInseparable

end KltDP.Examples.FrobeniusActualStrictGraphInseparable
