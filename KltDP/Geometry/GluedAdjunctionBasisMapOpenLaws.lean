import KltDP.Geometry.GluedAdjunctionBasisMapLaws

/-!
# The original basis component laws with explicit original opens

Specialize the induced/op functor while the module sheaves and basis are
abstract, so the inputs retain the literal original open in every module.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
universe u v
namespace KltDP.Geometry.GluedAdjunctionBasisMapOpenLaws

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- Naturality with all original section modules indexed by their explicit open. -/
theorem naturality {X : Scheme.{u}} (M N : X.Modules)
    {ι : Type v} (B : ι → X.Opens)
    {c e : (InducedCategory X.Opens B)ᵒᵖ} (i : c ⟶ e)
    (h : B e.unop ≤ B c.unop) (hi : (homOfLE h).op = i)
    (gC : M.val.obj (op (B c.unop)) →+ N.val.obj (op (B c.unop)))
    (gD gE : M.val.obj (op (B e.unop)) →+ N.val.obj (op (B e.unop)))
    (hAgree : gE = gD)
    (hRes : ∀ m, gD (M.val.map (homOfLE h).op m) =
      N.val.map (homOfLE h).op (gC m)) :
    ((inducedFunctor B).op ⋙ M.val.presheaf).map i ≫ AddCommGrp.ofHom gE =
      AddCommGrp.ofHom gC ≫ ((inducedFunctor B).op ⋙ N.val.presheaf).map i :=
  GluedAdjunctionBasisMapLaws.naturality M N (inducedFunctor B).op i
    (homOfLE h).op hi gC gD gE hAgree hRes

/-- The named basis component is linear for the explicit original section ring. -/
theorem app_smul {X : Scheme.{u}} (M N : X.Modules)
    {ι : Type v} (B : ι → X.Opens)
    (φ : (inducedFunctor B).op ⋙ M.val.presheaf ⟶
      (inducedFunctor B).op ⋙ N.val.presheaf) (c : ι)
    (g : M.val.obj (op (B c)) →+ N.val.obj (op (B c)))
    (happ : φ.app (op c) = AddCommGrp.ofHom g)
    (hSmul : ∀ (r : Γ(X, B c)) (m : M.val.obj (op (B c))),
      g (r • m) = r • g m)
    (r : Γ(X, B c)) (m : M.val.obj (op (B c))) :
    φ.app (op c) (r • m) = r • (show N.val.obj (op (B c)) from φ.app (op c) m) :=
  GluedAdjunctionBasisMapLaws.app_smul M N (op (B c)) (φ.app (op c)) g happ hSmul r m

end KltDP.Geometry.GluedAdjunctionBasisMapOpenLaws
