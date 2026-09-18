import KltDP.Geometry.InvertibleQuadraticAtlas
import KltDP.Geometry.SchemeModulePullbackTensorSectionUnits
import KltDP.Geometry.SchemeModuleTensorSections
import KltDP.Geometry.SchemeStructureTensor

/-!
# Original quadratic tensor coordinates on local pure tensors

The actual sheafification unit and counit compute the already constructed
tensor multiplication on pairs of original sections. Consequently the
original quadratic recovery coordinates send a square of a section to
the square of its original matching coordinates.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite
open scoped TensorProduct
universe u

namespace KltDP.Geometry.QuadraticTensorSectionCoordinates

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance moduleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

local instance presheafTensor (X : Scheme.{u}) : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModules.monoidalCategory (R := X.sheaf.val)

local instance sectionCommRing (X : Scheme.{u}) (U : X.Opensᵒᵖ) :
    CommRing (X.ringCatSheaf.val.obj U) :=
  inferInstanceAs (CommRing (X.presheaf.obj U))

open SchemeModuleTensorSections SchemeModulePullbackTensorSectionUnits

/-- Evaluate the original sheafified presheaf pairing on its original pure tensor. -/
theorem sheafified_pair_apply {X : Scheme.{u}} (M N P : X.Modules)
    (a : M.val ⊗ N.val ⟶ P.val) (W : X.Opens)
    (m : M.val.obj (op W)) (n : N.val.obj (op W)) :
    ((PresheafOfModules.sheafTensorIsoSheafification
        X.sheaf.val X.ringCatSheaf.cond M N).hom ≫
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).map a ≫
      (PresheafOfModules.sheafificationForgetIso X.ringCatSheaf P).hom).val.app (op W)
        (tensorSection M N W m n) = a.app (op W) (m ⊗ₜ n) := by
  let T := PresheafOfModules.sheafTensorIsoSheafification
    X.sheaf.val X.ringCatSheaf.cond M N
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.val)).unit
  let ε := PresheafOfModules.sheafificationForgetIso X.ringCatSheaf P
  have hT : T.hom.val.app (op W) (tensorSection M N W m n) =
      (η.app (M.val ⊗ N.val)).app (op W) (m ⊗ₜ n) := by
    change (T.inv ≫ T.hom).val.app (op W) _ = _
    rw [Iso.inv_hom_id]
    rfl
  have hε : ε.hom.val.app (op W)
      ((η.app P.val).app (op W) (a.app (op W) (m ⊗ₜ n))) =
      a.app (op W) (m ⊗ₜ n) :=
    congrArg (fun z => z.app (op W) (a.app (op W) (m ⊗ₜ n)))
      (schemeSheafificationForgetIso_homEquiv P)
  change ε.hom.val.app (op W)
    (((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).map a).val.app
      (op W) (T.hom.val.app (op W) (tensorSection M N W m n))) = _
  rw [hT, sheafification_map_unit]
  exact hε

open TransitionUnitGluing TransitionUnitExtraction InvertibleQuadraticAtlas

/-- The existing transition tensor product has literal component multiplication. -/
theorem tensorMultiplication_tensorSection (X : Scheme.{u}) {ι : Type u}
    (U : ι → X.Opens) (g h : ∀ i j, Γ(X, U i ⊓ U j)ˣ)
    (W : X.Opens) (m : sections X U g W) (n : sections X U h W) :
    (tensorMultiplication X U g h).val.app (op W)
      (tensorSection (moduleSheaf X U g) (moduleSheaf X U h) W m n) =
      sectionMul X U g h W m n :=
  sheafified_pair_apply _ _ _ (multiplication X U g h) W m n

/-- Keep the tensor naturality elimination at abstract coefficient modules. -/
theorem tensor_map_pair_apply {X : Scheme.{u}} {M N M' N' P : X.Modules}
    (f : M ⟶ M') (g : N ⟶ N') (a : M' ⊗ N' ⟶ P)
    (q : ∀ W : X.Opens, M'.val.obj (op W) → N'.val.obj (op W) → P.val.obj (op W))
    (hq : ∀ W m n, a.val.app (op W) (tensorSection M' N' W m n) = q W m n)
    (W : X.Opens) (m : M.val.obj (op W)) (n : N.val.obj (op W)) :
    a.val.app (op W) ((f ⊗ g).val.app (op W) (tensorSection M N W m n)) =
      q W (f.val.app (op W) m) (g.val.app (op W) n) :=
  (congrArg (a.val.app (op W)) (tensorSection_natural f g W m n)).trans (hq W _ _)

/-- The original global quadratic coordinates retain the original square section. -/
theorem squareCoordinates_tensorSection (X : Scheme.{u}) (L : InvertibleSheaf X)
    (r : L.obj.val.obj (op (⊤ : X.Opens))) :
    squareCoordinates X L (tensorSection L.obj L.obj ⊤ r r) =
      sectionMul X L.localTrivializations.X (invertibleSheafUnits X L)
        (invertibleSheafUnits X L) ⊤
        ((invertibleSheafRecoveryIso X L).hom.val.app (op ⊤) r)
        ((invertibleSheafRecoveryIso X L).hom.val.app (op ⊤) r) := by
  change (tensorMultiplication X L.localTrivializations.X
    (invertibleSheafUnits X L) (invertibleSheafUnits X L)).val.app (op ⊤)
      (((invertibleSheafRecoveryIso X L).hom ⊗
        (invertibleSheafRecoveryIso X L).hom).val.app (op ⊤)
          (tensorSection L.obj L.obj ⊤ r r)) = _
  exact tensor_map_pair_apply
    (invertibleSheafRecoveryIso X L).hom (invertibleSheafRecoveryIso X L).hom
    (tensorMultiplication X L.localTrivializations.X
      (invertibleSheafUnits X L) (invertibleSheafUnits X L))
    (fun W m n => sectionMul X L.localTrivializations.X
      (invertibleSheafUnits X L) (invertibleSheafUnits X L) W m n)
    (tensorMultiplication_tensorSection X L.localTrivializations.X
      (invertibleSheafUnits X L) (invertibleSheafUnits X L)) ⊤ r r

/-- The original structure-module tensor multiplication is actual multiplication. -/
theorem structure_tensorSection (X : Scheme.{u}) (W : X.Opens)
    (a b : Γ(X, W)) :
    (schemeStructureTensorRightIso (_root_.SheafOfModules.unit X.ringCatSheaf)).hom.val.app
      (op W) (tensorSection (_root_.SheafOfModules.unit X.ringCatSheaf)
        (_root_.SheafOfModules.unit X.ringCatSheaf) W a b) = a * b := by
  rw [← schemeSheafTensorIso_structure_mul X]
  let O : X.Modules := _root_.SheafOfModules.unit X.ringCatSheaf
  have h := sheafified_pair_apply O O O (ρ_ O.val).hom W a b
  change _ = b * a at h
  exact h.trans (mul_comm b a)

end KltDP.Geometry.QuadraticTensorSectionCoordinates

#print axioms KltDP.Geometry.QuadraticTensorSectionCoordinates.squareCoordinates_tensorSection
