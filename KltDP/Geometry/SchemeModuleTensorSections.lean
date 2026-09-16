import KltDP.Geometry.SchemeModulePullbackTensorNaturality

/-!
# Local pure tensors in the original module-sheaf tensor

The actual sheafification unit and original tensor/sheafification comparison
send pairs of original local sections into the actual sheaf tensor. Such
sections detect maps out of that tensor by the existing adjunction and the
ordinary tensor universal property. This is the local-section interface for
normalizing the original pullback tensor comparisons.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite
open scoped TensorProduct

universe u

namespace KltDP.Geometry.SchemeModuleTensorSections

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance moduleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

local instance presheafTensor (X : Scheme.{u}) : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModules.monoidalCategory (R := X.sheaf.val)

local instance sectionCommRing (X : Scheme.{u}) (U : X.Opensᵒᵖ) :
    CommRing (X.ringCatSheaf.val.obj U) :=
  inferInstanceAs (CommRing (X.presheaf.obj U))

variable {X : Scheme.{u}}

/-- The actual local pure tensor, through the original sheafification unit. -/
def tensorSection (M N : X.Modules) (U : X.Opens)
    (m : M.val.obj (op U)) (n : N.val.obj (op U)) : (M ⊗ N).val.obj (op U) :=
  (PresheafOfModules.sheafTensorIsoSheafification
    X.sheaf.val X.ringCatSheaf.cond M N).inv.val.app (op U)
      (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.val)).unit.app
        (M.val ⊗ N.val)).app (op U) (m ⊗ₜ[X.ringCatSheaf.val.obj (op U)] n))

/-- Equality on actual local pure tensors determines the original sheaf-tensor map. -/
theorem hom_ext {M N P : X.Modules} (f g : M ⊗ N ⟶ P)
    (h : ∀ (U : X.Opens) (m : M.val.obj (op U)) (n : N.val.obj (op U)),
      f.val.app (op U) (tensorSection M N U m n) =
        g.val.app (op U) (tensorSection M N U m n)) : f = g := by
  apply (cancel_epi (PresheafOfModules.sheafTensorIsoSheafification
    X.sheaf.val X.ringCatSheaf.cond M N).inv).mp
  apply ((PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.val)).homEquiv _ _).injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  exact h U.unop m n

/-- The original tensor morphism acts on the original pair of local sections. -/
theorem tensorSection_natural {M M' N N' : X.Modules}
    (f : M ⟶ M') (g : N ⟶ N') (U : X.Opens)
    (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    (f ⊗ g).val.app (op U) (tensorSection M N U m n) =
      tensorSection M' N' U (f.val.app (op U) m) (g.val.app (op U) n) := by
  let S := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)
  let T : M ⊗ N ≅ S.obj (M.val ⊗ N.val) := PresheafOfModules.sheafTensorIsoSheafification
    X.sheaf.val X.ringCatSheaf.cond M N
  let T' : M' ⊗ N' ≅ S.obj (M'.val ⊗ N'.val) := PresheafOfModules.sheafTensorIsoSheafification
    X.sheaf.val X.ringCatSheaf.cond M' N'
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.val)
  have ht : T.inv ≫ (f ⊗ g) = S.map (f.val ⊗ g.val) ≫ T'.inv := by
    have h := congrArg (fun z => T.inv ≫ z ≫ T'.inv)
      (schemeSheafTensorIsoSheafification_natural f g)
    change T.inv ≫ ((f ⊗ g) ≫ T'.hom) ≫ T'.inv =
      T.inv ≫ (T.hom ≫ S.map (f.val ⊗ g.val)) ≫ T'.inv at h
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id,
      Category.comp_id] using h
  have htU := congrArg (fun z : S.obj (M.val ⊗ N.val) ⟶ M' ⊗ N' => z.val.app (op U)
      ((adj.unit.app (M.val ⊗ N.val)).app (op U)
        (m ⊗ₜ[X.ringCatSheaf.val.obj (op U)] n))) ht
  refine htU.trans ?_
  have hη := congrArg (fun z => z.app (op U)
      (m ⊗ₜ[X.ringCatSheaf.val.obj (op U)] n))
    (adj.unit.naturality (f.val ⊗ g.val))
  change (adj.unit.app (M'.val ⊗ N'.val)).app (op U)
      ((f.val ⊗ g.val).app (op U) (m ⊗ₜ[X.ringCatSheaf.val.obj (op U)] n)) =
    (S.map (f.val ⊗ g.val)).val.app (op U)
      ((adj.unit.app (M.val ⊗ N.val)).app (op U)
        (m ⊗ₜ[X.ringCatSheaf.val.obj (op U)] n)) at hη
  erw [PresheafOfModules.Monoidal.tensorHom_app,
    ModuleCat.MonoidalCategory.tensorHom_tmul] at hη
  exact congrArg (T'.inv.val.app (op U)) hη.symm

end KltDP.Geometry.SchemeModuleTensorSections
