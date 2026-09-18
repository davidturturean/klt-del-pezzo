import KltDP.Geometry.GluedAdjunctionBasisExtension

/-!
# Original additive components as a natural basis morphism

The conversion from the original section equations to additive-category
naturality is proved at abstract module sheaves. Scalar linearity likewise
retains the given component using its original defining equality.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
universe u v w
namespace KltDP.Geometry.GluedAdjunctionBasisMapLaws

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- Agreement and restriction of the actual section maps give additive naturality. -/
theorem naturality {X : Scheme.{u}} (M N : X.Modules)
    {C : Type v} [Category.{w} C] (F : C ⥤ X.Opensᵒᵖ)
    {c e : C} (i : c ⟶ e) (p : F.obj c ⟶ F.obj e) (hp : p = F.map i)
    (gC : M.val.obj (F.obj c) →+ N.val.obj (F.obj c))
    (gD gE : M.val.obj (F.obj e) →+ N.val.obj (F.obj e))
    (hAgree : gE = gD)
    (hRes : ∀ m, gD (M.val.map p m) = N.val.map p (gC m)) :
    (F ⋙ M.val.presheaf).map i ≫ AddCommGrp.ofHom gE =
      AddCommGrp.ofHom gC ≫ (F ⋙ N.val.presheaf).map i := by
  subst gE
  subst p
  ext m
  exact hRes m

/-- Scalar linearity passes through the original named component's defining equality. -/
theorem app_smul {X : Scheme.{u}} (M N : X.Modules) (U : X.Opensᵒᵖ)
    (a : M.val.presheaf.obj U ⟶ N.val.presheaf.obj U)
    (g : M.val.obj U →+ N.val.obj U) (ha : a = AddCommGrp.ofHom g)
    (hSmul : ∀ (r : X.ringCatSheaf.val.obj U) (m : M.val.obj U),
      g (r • m) = r • g m)
    (r : X.ringCatSheaf.val.obj U) (m : M.val.obj U) :
    a (r • m) = r • (show N.val.obj U from a m) := by
  subst a
  exact hSmul r m

end KltDP.Geometry.GluedAdjunctionBasisMapLaws
