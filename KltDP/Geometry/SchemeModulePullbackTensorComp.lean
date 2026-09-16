import KltDP.Geometry.SchemeModulePullbackTensorSections
import KltDP.Geometry.SchemeModulePullbackCompSections

/-!
# Composition of the original scheme-module pullback tensor comparisons

The original adjunctions reduce equality to actual local pure tensors.
The proved formulas for the original tensor and composition comparisons
then identify the two routes through the original successive pullbacks.
No tensor-composition compatibility is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite

universe u

namespace KltDP.Geometry

open SchemeModuleTensorSections SchemeModulePullbackTensorSections
open SchemeModulePullbackTensorSectionUnits SchemeModulePullbackCompSections

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance compositionModuleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

/-- The actual tensor comparison commutes with the actual pullback composition map. -/
theorem schemeModulePullbackTensorIso_comp_hom {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (M N : Z.Modules) :
    (schemeModulePullback f).map (schemeModulePullbackTensorIso g M N).hom ≫
      (schemeModulePullbackTensorIso f
        ((schemeModulePullback g).obj M) ((schemeModulePullback g).obj N)).hom ≫
      ((schemeModulePullbackCompIso f g).hom.app M ⊗
        (schemeModulePullbackCompIso f g).hom.app N) =
    (schemeModulePullbackCompIso f g).hom.app (M ⊗ N) ≫
      (schemeModulePullbackTensorIso (f ≫ g) M N).hom := by
  apply ((schemeModulePullbackPushforwardAdjunction f).homEquiv _ _).injective
  apply ((schemeModulePullbackPushforwardAdjunction g).homEquiv _ _).injective
  apply SchemeModuleTensorSections.hom_ext
  intro U m n
  change (((schemeModulePullbackCompIso f g).hom.app M ⊗
        (schemeModulePullbackCompIso f g).hom.app N).val.app (op ((f ≫ g) ⁻¹ᵁ U)))
      ((schemeModulePullbackTensorIso f
        ((schemeModulePullback g).obj M) ((schemeModulePullback g).obj N)).hom.val.app
        (op ((f ≫ g) ⁻¹ᵁ U))
        (((schemeModulePullback f).map (schemeModulePullbackTensorIso g M N).hom).val.app
          (op ((f ≫ g) ⁻¹ᵁ U))
          (((schemeModulePullbackPushforwardAdjunction f).unit.app
            ((schemeModulePullback g).obj (M ⊗ N))).val.app (op (g ⁻¹ᵁ U))
            (((schemeModulePullbackPushforwardAdjunction g).unit.app (M ⊗ N)).val.app
              (op U) (tensorSection M N U m n))))) =
    (schemeModulePullbackTensorIso (f ≫ g) M N).hom.val.app (op ((f ≫ g) ⁻¹ᵁ U))
      (((schemeModulePullbackCompIso f g).hom.app (M ⊗ N)).val.app
        (op ((f ≫ g) ⁻¹ᵁ U))
        (((schemeModulePullbackPushforwardAdjunction f).unit.app
          ((schemeModulePullback g).obj (M ⊗ N))).val.app (op (g ⁻¹ᵁ U))
          (((schemeModulePullbackPushforwardAdjunction g).unit.app (M ⊗ N)).val.app
            (op U) (tensorSection M N U m n))))
  simp only [Scheme.preimage_comp]
  have hM := comp_unit_section f g M U m
  have hN := comp_unit_section f g N U n
  have hMN := comp_unit_section f g (M ⊗ N) U (tensorSection M N U m n)
  simp only [Scheme.preimage_comp] at hM hN hMN
  rw [pullback_map_unit f (schemeModulePullbackTensorIso g M N).hom (g ⁻¹ᵁ U)
    (((schemeModulePullbackPushforwardAdjunction g).unit.app (M ⊗ N)).val.app
      (op U) (tensorSection M N U m n))]
  rw [tensor_unit_section g M N U m n]
  rw [tensor_unit_section f ((schemeModulePullback g).obj M)
    ((schemeModulePullback g).obj N) (g ⁻¹ᵁ U)
    (((schemeModulePullbackPushforwardAdjunction g).unit.app M).val.app (op U) m)
    (((schemeModulePullbackPushforwardAdjunction g).unit.app N).val.app (op U) n)]
  have hTensor := tensorSection_natural ((schemeModulePullbackCompIso f g).hom.app M)
    ((schemeModulePullbackCompIso f g).hom.app N) (f ⁻¹ᵁ (g ⁻¹ᵁ U))
    (((schemeModulePullbackPushforwardAdjunction f).unit.app
      ((schemeModulePullback g).obj M)).val.app (op (g ⁻¹ᵁ U))
      (((schemeModulePullbackPushforwardAdjunction g).unit.app M).val.app (op U) m))
    (((schemeModulePullbackPushforwardAdjunction f).unit.app
      ((schemeModulePullback g).obj N)).val.app (op (g ⁻¹ᵁ U))
      (((schemeModulePullbackPushforwardAdjunction g).unit.app N).val.app (op U) n))
  simp only [Functor.comp_obj] at hTensor
  refine hTensor.trans ?_
  have hPair := congrArg₂
    (tensorSection ((schemeModulePullback (f ≫ g)).obj M)
      ((schemeModulePullback (f ≫ g)).obj N) (f ⁻¹ᵁ (g ⁻¹ᵁ U))) hM hN
  have hEnd := congrArg
    ((schemeModulePullbackTensorIso (f ≫ g) M N).hom.val.app (op (f ⁻¹ᵁ (g ⁻¹ᵁ U)))) hMN
  exact hPair.trans ((tensor_unit_section (f ≫ g) M N U m n).symm.trans hEnd.symm)

/-- The same composition law for the original isomorphisms themselves. -/
theorem schemeModulePullbackTensorIso_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (M N : Z.Modules) :
    (schemeModulePullback f).mapIso (schemeModulePullbackTensorIso g M N) ≪≫
      schemeModulePullbackTensorIso f
        ((schemeModulePullback g).obj M) ((schemeModulePullback g).obj N) ≪≫
      tensorIso ((schemeModulePullbackCompIso f g).app M)
        ((schemeModulePullbackCompIso f g).app N) =
    (schemeModulePullbackCompIso f g).app (M ⊗ N) ≪≫
      schemeModulePullbackTensorIso (f ≫ g) M N := by
  apply Iso.ext
  exact schemeModulePullbackTensorIso_comp_hom f g M N

end KltDP.Geometry
