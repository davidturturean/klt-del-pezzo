import KltDP.Geometry.InvertibleSheafPowerFrameTransition
import KltDP.Geometry.SchemeModuleTensorScalar

/-!
# Actual power twists in original frames

An original section of an invertible sheaf induces an actual morphism
`M → M ⊗ L^n`. In the constructed power frame, this morphism is literal
multiplication by the power of the original coefficient, on every local
section of an arbitrary original module. Changes of power-twist frame have
the corresponding literal transition power. No coherence or global
generation of the coefficient module is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite

universe u

namespace KltDP.Geometry.InvertibleSheafTwistFrame

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance twistFrameMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

local instance originalSectionModule {X : Scheme.{u}} (M : X.Modules) (V : X.Opens) :
    Module Γ(X, V) (M.val.obj (op V)) := (M.val.obj (op V)).isModule

open InvertibleSheafSectionPowers InvertibleSheafPowerFrameTransition
open SchemeModuleTensorScalar ModuleCohomology

variable {X : Scheme.{u}} (M : X.Modules) (L : InvertibleSheaf X)

/-- Tensor multiplication by the original power section, using the actual
structure-module unitor. -/
def rightTwistMap (s : L.obj.sections) (n : ℕ) : M ⟶ M ⊗ (power L n).obj :=
  (schemeStructureTensorRightIso M).inv ≫ (𝟙 M ⊗ powerSectionHom L s n)

/-- The actual power frame cancels the invertible factor of the original twist. -/
def rightTwistFrame (e : L.obj ≅ _root_.SheafOfModules.unit X.ringCatSheaf) (n : ℕ) :
    M ⊗ (power L n).obj ≅ M :=
  tensorIso (Iso.refl M) (powerFrame L e n) ≪≫ schemeStructureTensorRightIso M

/-- Multiplication by the power section has its literal original scalar
coefficient under the original twist frame. -/
theorem rightTwistMap_comp_frame
    (e : L.obj ≅ _root_.SheafOfModules.unit X.ringCatSheaf)
    (s : L.obj.sections) (n : ℕ) :
    rightTwistMap M L s n ≫ (rightTwistFrame M L e n).hom =
      globalSmulHom M (frameCoefficient L e s ^ n) := by
  simp only [rightTwistMap, rightTwistFrame, Iso.trans_hom, tensorIso_hom,
    Iso.refl_hom, Category.assoc]
  calc
    _ = (schemeStructureTensorRightIso M).inv ≫
        (𝟙 M ⊗ (powerSectionHom L s n ≫ (powerFrame L e n).hom)) ≫
        (schemeStructureTensorRightIso M).hom := by
      simpa only [Category.assoc, Category.id_comp] using
        congrArg (fun g => (schemeStructureTensorRightIso M).inv ≫
          g ≫ (schemeStructureTensorRightIso M).hom)
          (tensor_comp (𝟙 M) (powerSectionHom L s n)
            (𝟙 M) (powerFrame L e n).hom).symm
    _ = _ := by
      rw [powerSectionHom_frame]
      exact structureTensorRight_scalar_conjugate M (frameCoefficient L e s ^ n)

/-- The same equality acts literally on every original local section. -/
theorem rightTwistMap_frame_apply
    (e : L.obj ≅ _root_.SheafOfModules.unit X.ringCatSheaf)
    (s : L.obj.sections) (n : ℕ) (V : X.Opens) (t : M.val.obj (op V)) :
    (rightTwistFrame M L e n).hom.val.app (op V)
        ((rightTwistMap M L s n).val.app (op V) t) =
      X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
        (frameCoefficient L e s ^ n) • t := by
  have h := congrArg (fun g : M ⟶ M => g.val.app (op V) t)
    (rightTwistMap_comp_frame M L e s n)
  change (rightTwistFrame M L e n).hom.val.app (op V)
      ((rightTwistMap M L s n).val.app (op V) t) =
    (globalSmulHom M (frameCoefficient L e s ^ n)).val.app (op V) t at h
  exact h.trans (globalSmulHom_app M (frameCoefficient L e s ^ n) V t)

/-- The actual transition between power-twist frames is multiplication
by the literal power of the original line-frame coefficient. -/
theorem rightTwistFrame_transition
    (e d : L.obj ≅ _root_.SheafOfModules.unit X.ringCatSheaf) (n : ℕ) :
    (rightTwistFrame M L e n).inv ≫ (rightTwistFrame M L d n).hom =
      globalSmulHom M (frameCoefficient L d (frameGenerator L e) ^ n) := by
  simp only [rightTwistFrame, Iso.trans_inv, Iso.trans_hom, tensorIso_inv, tensorIso_hom,
    Iso.refl_inv, Iso.refl_hom, Category.assoc]
  calc
    _ = (schemeStructureTensorRightIso M).inv ≫
        (𝟙 M ⊗ ((powerFrame L e n).inv ≫ (powerFrame L d n).hom)) ≫
        (schemeStructureTensorRightIso M).hom := by
      simpa only [Category.assoc, Category.id_comp] using
        congrArg (fun g => (schemeStructureTensorRightIso M).inv ≫
          g ≫ (schemeStructureTensorRightIso M).hom)
          (tensor_comp (𝟙 M) (powerFrame L e n).inv
            (𝟙 M) (powerFrame L d n).hom).symm
    _ = _ := by
      rw [powerFrame_transition]
      exact structureTensorRight_scalar_conjugate M
        (frameCoefficient L d (frameGenerator L e) ^ n)

/-- The coefficient of any actual local twisted section changes by the
literal transition power, without a supplied compatibility condition. -/
theorem rightTwistFrame_change_apply
    (e d : L.obj ≅ _root_.SheafOfModules.unit X.ringCatSheaf) (n : ℕ)
    (V : X.Opens) (t : (M ⊗ (power L n).obj).val.obj (op V)) :
    (rightTwistFrame M L d n).hom.val.app (op V) t =
      X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
          (frameCoefficient L d (frameGenerator L e) ^ n) •
        (rightTwistFrame M L e n).hom.val.app (op V) t := by
  have hh : (rightTwistFrame M L d n).hom =
      (rightTwistFrame M L e n).hom ≫
        globalSmulHom M (frameCoefficient L d (frameGenerator L e) ^ n) := by
    simpa only [Iso.hom_inv_id_assoc] using
      congrArg (fun g : M ⟶ M => (rightTwistFrame M L e n).hom ≫ g)
        (rightTwistFrame_transition M L e d n)
  have h := congrArg (fun g : M ⊗ (power L n).obj ⟶ M => g.val.app (op V) t) hh
  change (rightTwistFrame M L d n).hom.val.app (op V) t =
    (globalSmulHom M (frameCoefficient L d (frameGenerator L e) ^ n)).val.app (op V)
      ((rightTwistFrame M L e n).hom.val.app (op V) t) at h
  exact h.trans (globalSmulHom_app M (frameCoefficient L d (frameGenerator L e) ^ n)
    V ((rightTwistFrame M L e n).hom.val.app (op V) t))

end KltDP.Geometry.InvertibleSheafTwistFrame
