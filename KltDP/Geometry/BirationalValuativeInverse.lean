import KltDP.Geometry.BirationalFunctionField
import KltDP.Geometry.DivisorOrder
import KltDP.Geometry.DominantOpenSection
import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-!
# Extending the original birational inverse to a valuation stalk

The fraction field is the target's original function field, with the pinned
stalk-specialization algebra structure. Properness lifts the original
inverse-function-field square. Its top triangle proves that the resulting
map from the original target stalk remains dominant.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u

namespace KltDP.Geometry.ProperBirationalCodimensionOne

attribute [local instance] integralSchemeStalk_isDomain

variable {S X : Scheme.{u}} [IsIntegral S] [IsIntegral X]

/-- The original function-field map commutes with the original generic
stalk maps to the schemes. -/
theorem functionFieldMap_fromSpecStalk (π : S ⟶ X) [GenericPointPreserving π] :
    Spec.map (functionFieldMap π) ≫ X.fromSpecStalk (genericPoint X) =
      S.fromSpecStalk (genericPoint S) ≫ π := by
  rw [functionFieldMap, Spec.map_comp, Category.assoc,
    Scheme.Spec_map_stalkSpecializes_fromSpecStalk,
    Scheme.Spec_map_stalkMap_fromSpecStalk]

/-- The original stalk algebra map to the function field gives the actual
specialization triangle of the canonical maps to the target. -/
theorem stalkFunctionField_fromSpecStalk (x : X) :
    Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField)) ≫
      X.fromSpecStalk x = X.fromSpecStalk (genericPoint X) := by
  change Spec.map (X.presheaf.stalkSpecializes
      ((genericPoint_spec X).specializes trivial)) ≫ X.fromSpecStalk x = _
  exact Scheme.Spec_map_stalkSpecializes_fromSpecStalk _

/-- At an original valuation stalk, properness extends the original
birational inverse to a dominant lift with its original base triangle. -/
theorem exists_dominant_stalk_lift
    (π : S ⟶ X) [IsProper π] (hbir : IsBirationalScheme π)
    (x : X) [ValuationRing (X.presheaf.stalk x)] :
    ∃ φ : Spec (X.presheaf.stalk x) ⟶ S,
      φ ≫ π = X.fromSpecStalk x ∧ IsDominant φ := by
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  letI : IsIso (functionFieldMap π) :=
    (BirationalFunctionField.isBirationalScheme_iff_functionFieldMap_isIso π).mp hbir
  let t : Spec X.functionField ⟶ S :=
    inv (Spec.map (functionFieldMap π)) ≫ S.fromSpecStalk (genericPoint S)
  have htπ : t ≫ π = X.fromSpecStalk (genericPoint X) := by
    dsimp only [t]
    rw [Category.assoc, ← functionFieldMap_fromSpecStalk π, IsIso.inv_hom_id_assoc]
  let V : ValuativeCommSq π :=
    { R := X.presheaf.stalk x
      K := X.functionField
      i₁ := t
      i₂ := X.fromSpecStalk x
      commSq := ⟨htπ.trans (stalkFunctionField_fromSpecStalk x).symm⟩ }
  have hval : ValuativeCriterion π := by
    have hp : IsProper π := inferInstance
    rw [IsProper.eq_valuativeCriterion] at hp
    exact hp.1.1.1
  letI : V.commSq.HasLift := hval.existence V
  let φ : Spec (X.presheaf.stalk x) ⟶ S := V.commSq.lift
  have hφπ : φ ≫ π = X.fromSpecStalk x := V.commSq.fac_right
  have htφ :
      Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField)) ≫ φ = t :=
    V.commSq.fac_left
  letI : IsDominant (S.fromSpecStalk (genericPoint S)) :=
    DominantOpenSection.fromSpecStalk_genericPoint_isDominant S
  letI : IsDominant t := by dsimp only [t]; infer_instance
  letI : IsDominant
      (Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField)) ≫ φ) := by
    rw [htφ]
    infer_instance
  exact ⟨φ, hφπ, IsDominant.of_comp
    (Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField))) φ⟩

end KltDP.Geometry.ProperBirationalCodimensionOne
