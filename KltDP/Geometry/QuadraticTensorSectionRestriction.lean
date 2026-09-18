import KltDP.Geometry.SchemeModuleTensorSections

/-!
# Restricting the original tensor-section pairing

Naturality of the original tensor/sheafification comparison and the
original sheafification unit gives the restriction formula. This is
used to evaluate a global quadratic root on the actual ambient subopens.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite
open scoped TensorProduct
universe u

namespace KltDP.Geometry.QuadraticTensorSectionRestriction

attribute [local instance] Types.instFunLike Types.instConcreteCategory
local instance moduleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X
local instance presheafTensor (X : Scheme.{u}) : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModules.monoidalCategory (R := X.sheaf.val)
local instance sectionCommRing (X : Scheme.{u}) (U : X.Opensᵒᵖ) :
    CommRing (X.ringCatSheaf.val.obj U) :=
  inferInstanceAs (CommRing (X.presheaf.obj U))

open SchemeModuleTensorSections

/-- Actual pure tensors commute with the original sheaf restriction maps. -/
theorem tensorSection_restrict {X : Scheme.{u}} (M N : X.Modules)
    {V W : X.Opens} (h : V ≤ W) (m : M.val.obj (op W)) (n : N.val.obj (op W)) :
    (M ⊗ N).val.map (homOfLE h).op (tensorSection M N W m n) =
      tensorSection M N V (M.val.map (homOfLE h).op m) (N.val.map (homOfLE h).op n) := by
  let T := PresheafOfModules.sheafTensorIsoSheafification
    X.sheaf.val X.ringCatSheaf.cond M N
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.val)).unit.app
    (M.val ⊗ N.val)
  let z := m ⊗ₜ[X.ringCatSheaf.val.obj (op W)] n
  have hT := _root_.PresheafOfModules.naturality_apply T.inv.val (homOfLE h).op
    (η.app (op W) z)
  have hη := _root_.PresheafOfModules.naturality_apply η (homOfLE h).op z
  have hm : (M.val ⊗ N.val).map (homOfLE h).op z =
      M.val.map (homOfLE h).op m ⊗ₜ[X.ringCatSheaf.val.obj (op V)]
        N.val.map (homOfLE h).op n := rfl
  exact hT.symm.trans (congrArg (T.inv.val.app (op V))
    (hη.symm.trans (congrArg (η.app (op V)) hm)))

/-- Every original tensor pairing has the same actual restriction formula. -/
theorem pairing_restrict {X : Scheme.{u}} (M N P : X.Modules) (q : M ⊗ N ⟶ P)
    {V W : X.Opens} (h : V ≤ W) (m : M.val.obj (op W)) (n : N.val.obj (op W)) :
    P.val.map (homOfLE h).op (q.val.app (op W) (tensorSection M N W m n)) =
      q.val.app (op V)
        (tensorSection M N V (M.val.map (homOfLE h).op m) (N.val.map (homOfLE h).op n)) :=
  (_root_.PresheafOfModules.naturality_apply q.val (homOfLE h).op
    (tensorSection M N W m n)).symm.trans
      (congrArg (q.val.app (op V)) (tensorSection_restrict M N h m n))

end KltDP.Geometry.QuadraticTensorSectionRestriction

#print axioms KltDP.Geometry.QuadraticTensorSectionRestriction.pairing_restrict
