import KltDP.Geometry.QuadraticTensorSectionCoordinates

/-!
# A tensor pairing in the original local line frames

An original sheaf-tensor pairing normalized on the two original frame
sections has the product of their original coordinates on all sections.
The proof uses the actual sheafification-unit pure tensor and its original
scalar actions. This is used to compare pulled ambient quadratic frames.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite
open scoped TensorProduct
universe u

namespace KltDP.Geometry.QuadraticTensorPairingFrame

attribute [local instance] Types.instFunLike Types.instConcreteCategory
local instance moduleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X
local instance presheafTensor (X : Scheme.{u}) : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModules.monoidalCategory (R := X.sheaf.val)
local instance sectionCommRing (X : Scheme.{u}) (W : X.Opensᵒᵖ) :
    CommRing (X.ringCatSheaf.val.obj W) :=
  inferInstanceAs (CommRing (X.presheaf.obj W))

open SchemeModuleTensorSections

/-- Both literal scalar actions are preserved by the original sheaf tensor section. -/
theorem tensorSection_smul_smul {X : Scheme.{u}} (M N : X.Modules) (W : X.Opens)
    (a b : Γ(X, W)) (m : M.val.obj (op W)) (n : N.val.obj (op W)) :
    tensorSection M N W (a • m) (b • n) =
      (a * b) • tensorSection M N W m n := by
  simp only [tensorSection, TensorProduct.smul_tmul_smul, map_smul]

/-- Normalization on actual unit frame sections determines every actual coefficient. -/
theorem coordinate {X : Scheme.{u}} (M N P : X.Modules) (q : M ⊗ N ⟶ P)
    (W : X.Opens)
    (eM : M.val.obj (op W) ≃ₗ[Γ(X, W)] Γ(X, W))
    (eN : N.val.obj (op W) ≃ₗ[Γ(X, W)] Γ(X, W))
    (eP : P.val.obj (op W) ≃ₗ[Γ(X, W)] Γ(X, W))
    (h : eP (q.val.app (op W) (tensorSection M N W (eM.symm 1) (eN.symm 1))) = 1)
    (m : M.val.obj (op W)) (n : N.val.obj (op W)) :
    eP (q.val.app (op W) (tensorSection M N W m n)) = eM m * eN n := by
  have hm : eM m • eM.symm 1 = m := by
    apply eM.injective
    simp only [map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
  have hn : eN n • eN.symm 1 = n := by
    apply eN.injective
    simp only [map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
  calc
    _ = eP (q.val.app (op W)
        (tensorSection M N W (eM m • eM.symm 1) (eN n • eN.symm 1))) :=
      congrArg (fun z => eP (q.val.app (op W) z))
        (congrArg₂ (tensorSection M N W) hm.symm hn.symm)
    _ = _ := by rw [tensorSection_smul_smul, map_smul, map_smul, h, smul_eq_mul, mul_one]

end KltDP.Geometry.QuadraticTensorPairingFrame

#print axioms KltDP.Geometry.QuadraticTensorPairingFrame.coordinate
