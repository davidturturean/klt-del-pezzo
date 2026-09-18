import KltDP.Geometry.RegularCurveFunctionFieldExtension

/-! An isomorphism of the original generic-point spectra over the base
extends to an isomorphism of the original integral regular proper curves.
Both inverse laws follow from the proved uniqueness of extension. -/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.RegularProperCurveGenericIso

theorem exists_iso {X Y B : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [B.IsSeparated]
    (hX : ∀ x : X, RegularPoint X x) (hY : ∀ y : Y, RegularPoint Y y)
    (dX : topologicalKrullDim X ≤ 1) (dY : topologicalKrullDim Y ≤ 1)
    (sX : X ⟶ B) (sY : Y ⟶ B) [IsProper sX] [IsProper sY]
    (e : Spec X.functionField ≅ Spec Y.functionField)
    (he : e.hom ≫ Y.fromSpecStalk (genericPoint Y) ≫ sY =
      X.fromSpecStalk (genericPoint X) ≫ sX) :
    ∃ i : X ≅ Y, i.hom ≫ sY = sX ∧
      X.fromSpecStalk (genericPoint X) ≫ i.hom =
        e.hom ≫ Y.fromSpecStalk (genericPoint Y) := by
  obtain ⟨g, hgs, hg⟩ := RegularCurveFunctionFieldExtension.exists_extension
    hX dX sX sY (e.hom ≫ Y.fromSpecStalk (genericPoint Y))
      (by simpa only [Category.assoc] using he)
  have hei : (e.inv ≫ X.fromSpecStalk (genericPoint X)) ≫ sX =
      Y.fromSpecStalk (genericPoint Y) ≫ sY := by
    rw [Category.assoc, ← he, e.inv_hom_id_assoc]
  obtain ⟨h, hhs, hh⟩ := RegularCurveFunctionFieldExtension.exists_extension
    hY dY sY sX (e.inv ≫ X.fromSpecStalk (genericPoint X)) hei
  have hgh : g ≫ h = 𝟙 X := by
    apply RegularCurveFunctionFieldExtension.unique sX sX
      (by rw [Category.assoc, hhs, hgs]) (Category.id_comp sX)
    calc
      X.fromSpecStalk (genericPoint X) ≫ (g ≫ h) =
          e.hom ≫ (Y.fromSpecStalk (genericPoint Y) ≫ h) := by
        rw [← Category.assoc, hg, Category.assoc]
      _ = X.fromSpecStalk (genericPoint X) := by
        rw [hh, e.hom_inv_id_assoc]
      _ = X.fromSpecStalk (genericPoint X) ≫ 𝟙 X := (Category.comp_id _).symm
  have hhg : h ≫ g = 𝟙 Y := by
    apply RegularCurveFunctionFieldExtension.unique sY sY
      (by rw [Category.assoc, hgs, hhs]) (Category.id_comp sY)
    calc
      Y.fromSpecStalk (genericPoint Y) ≫ (h ≫ g) =
          e.inv ≫ (X.fromSpecStalk (genericPoint X) ≫ g) := by
        rw [← Category.assoc, hh, Category.assoc]
      _ = Y.fromSpecStalk (genericPoint Y) := by
        rw [hg, e.inv_hom_id_assoc]
      _ = Y.fromSpecStalk (genericPoint Y) ≫ 𝟙 Y := (Category.comp_id _).symm
  exact ⟨⟨g, h, hgh, hhg⟩, hgs, hg⟩

end KltDP.Geometry.RegularProperCurveGenericIso
