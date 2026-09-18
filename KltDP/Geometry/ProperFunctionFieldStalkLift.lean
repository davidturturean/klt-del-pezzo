import KltDP.Geometry.BirationalValuativeInverse

/-! Properness extends an original function-field-spectrum map to each
original valuation stalk. This does not presuppose a morphism from the
whole source, or birationality of such a morphism. Both triangles retain
the original maps and the pinned stalk-to-function-field algebra. -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u

namespace KltDP.Geometry.ProperFunctionFieldStalkLift

attribute [local instance] integralSchemeStalk_isDomain

theorem exists_lift {X Y B : Scheme.{u}} [IsIntegral X]
    (sX : X ⟶ B) (sY : Y ⟶ B) [IsProper sY]
    (t : Spec X.functionField ⟶ Y)
    (ht : t ≫ sY = X.fromSpecStalk (genericPoint X) ≫ sX)
    (x : X) [ValuationRing (X.presheaf.stalk x)] :
    ∃ φ : Spec (X.presheaf.stalk x) ⟶ Y,
      φ ≫ sY = X.fromSpecStalk x ≫ sX ∧
      Spec.map (CommRingCat.ofHom
        (algebraMap (X.presheaf.stalk x) X.functionField)) ≫ φ = t := by
  let V : ValuativeCommSq sY :=
    { R := X.presheaf.stalk x
      K := X.functionField
      i₁ := t
      i₂ := X.fromSpecStalk x ≫ sX
      commSq := ⟨by
        rw [ht, ← Category.assoc,
          ProperBirationalCodimensionOne.stalkFunctionField_fromSpecStalk]⟩ }
  have hval : ValuativeCriterion sY := by
    have hp : IsProper sY := inferInstance
    rw [IsProper.eq_valuativeCriterion] at hp
    exact hp.1.1.1
  letI : V.commSq.HasLift := hval.existence V
  exact ⟨V.commSq.lift, V.commSq.fac_right, V.commSq.fac_left⟩

end KltDP.Geometry.ProperFunctionFieldStalkLift
