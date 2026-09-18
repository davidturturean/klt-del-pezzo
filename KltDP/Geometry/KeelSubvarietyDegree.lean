import KltDP.Geometry.ZeroDimensionalSubvarietyBigness
import KltDP.Geometry.ProperCurveEuler
import KltDP.AdmissionProbe.ProperCohomologyConsumers

/-!
# The original finite Euler degree on each proper integral subvariety curve

The reduced subvariety, its inclusion, and the restricted coefficient line
are the original Positivity constructions. Properness, dimension one,
cohomology finiteness, and higher vanishing are derived on these objects.
No projectivity, algebraic-closedness, smoothness, or numerical input is added.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.KeelSubvarietyDegree

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open ModuleCohomology Positivity
open KltDP.AdmissionProbe.ProperCohomologyConsumers

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) [hproper : IsProper f]
  (L : InvertibleSheaf X) (Z : IrreducibleCloseds X)

include hproper

/-- The original reduced curve is integral and proper, with its original dimension. -/
theorem subvariety_geometry (hdim : topologicalKrullDim (Z : Set X) = 1) :
    IsIntegral (toScheme Z) ∧ IsProper (inclusion Z ≫ f) ∧
      topologicalKrullDim (toScheme Z) = 1 :=
  ⟨ZeroDimensionalSubvarietyBigness.toScheme_isIntegral Z, inferInstance,
    (ZeroDimensionalSubvarietyBigness.toScheme_dimension Z).trans hdim⟩

/-- Every original cohomology group of the actual restricted line is finite over k. -/
theorem restriction_finiteDimensional (i : ℕ) :
    FiniteDimensional k ((baseFunctor (inclusion Z ≫ f) i).obj
      (pullbackInvertibleSheaf (inclusion Z) L).obj) :=
  proper_invertible_field_finiteDimensional (inclusion Z ≫ f)
    (pullbackInvertibleSheaf (inclusion Z) L) i

/-- The actual structure coefficient has finite original-field cohomology as well. -/
theorem structure_finiteDimensional (i : ℕ) :
    FiniteDimensional k ((baseFunctor (inclusion Z ≫ f) i).obj
      (_root_.SheafOfModules.unit (toScheme Z).ringCatSheaf)) :=
  proper_invertible_field_finiteDimensional (inclusion Z ≫ f)
    (InvertibleSheaf.trivial (toScheme Z)) i

/-- Both original coefficients have no cohomology above one on this curve. -/
theorem cohomology_subsingleton
    (hdim : topologicalKrullDim (Z : Set X) = 1) (i : ℕ) (hi : 1 < i) :
    Subsingleton (H (pullbackInvertibleSheaf (inclusion Z) L).obj i) ∧
      Subsingleton (H (_root_.SheafOfModules.unit (toScheme Z).ringCatSheaf) i) := by
  have hZ : topologicalKrullDim (toScheme Z) ≤ 1 :=
    le_of_eq ((ZeroDimensionalSubvarietyBigness.toScheme_dimension Z).trans hdim)
  exact ⟨proper_H_subsingleton_of_dimension_le_one (inclusion Z ≫ f) hZ _ i hi,
    proper_H_subsingleton_of_dimension_le_one (inclusion Z ≫ f) hZ _ i hi⟩

/-- The degree in the original nef predicate is the four original finite
H0/H1 dimensions, with scalars through the same original curve structure map. -/
theorem subvarietyDegree_eq_h0_sub_h1
    (hdim : topologicalKrullDim (Z : Set X) = 1) :
    subvarietyDegree f L Z =
      ((cohomologyDimension (inclusion Z ≫ f)
          (pullbackInvertibleSheaf (inclusion Z) L).obj 0 : ℤ) -
        (cohomologyDimension (inclusion Z ≫ f)
          (pullbackInvertibleSheaf (inclusion Z) L).obj 1 : ℤ)) -
      ((cohomologyDimension (inclusion Z ≫ f)
          (_root_.SheafOfModules.unit (toScheme Z).ringCatSheaf) 0 : ℤ) -
        (cohomologyDimension (inclusion Z ≫ f)
          (_root_.SheafOfModules.unit (toScheme Z).ringCatSheaf) 1 : ℤ)) := by
  have hZ : topologicalKrullDim (toScheme Z) ≤ 1 :=
    le_of_eq ((ZeroDimensionalSubvarietyBigness.toScheme_dimension Z).trans hdim)
  exact congrArg₂ (fun x y : ℤ => x - y)
    (proper_eulerCharacteristic_eq_h0_sub_h1 (inclusion Z ≫ f) hZ
      (pullbackInvertibleSheaf (inclusion Z) L).obj)
    (proper_eulerCharacteristic_eq_h0_sub_h1 (inclusion Z ≫ f) hZ
      (_root_.SheafOfModules.unit (toScheme Z).ringCatSheaf))

end KltDP.Geometry.KeelSubvarietyDegree
