import KltDP.Geometry.RationalOpenPullbackField
import KltDP.Geometry.OpenImmersionFunctionFieldFunctorial
import KltDP.Geometry.SchemeModulePullbackCoherence

/-!
# The adjoint of the original rational-module pullback

The original image-open restriction adjunction computes the adjoint on
every original section. On a nonempty open it is exactly the original
generic-stalk field map. The comparison to scheme pullback uses the pinned
left-adjoint uniqueness theorem, as in the existing module coherence
adapter; no new pullback or compatibility datum is introduced.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.OpenImmersionRational

open SchemeModuleRestriction

attribute [local instance] Types.instFunLike Types.instConcreteCategory

private theorem homEquiv_leftAdjointUniq_comp
    {C D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) (b : F' ⊣ G)
    (M : C) (N : D) (h : F'.obj M ⟶ N) :
    a.homEquiv M N ((Adjunction.leftAdjointUniq a b).hom.app M ≫ h) =
      b.homEquiv M N h := by
  rw [Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_leftAdjointUniq_hom_app, Adjunction.homEquiv_unit]

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) [IsOpenImmersion f]

/-- The actual rational restriction map under its original adjunction. -/
def rationalOpenAdjoint : rationalFunctionModule X ⟶
    (schemeModulePushforward f).obj (rationalFunctionModule Y) :=
  (restrictionAdjunction f).homEquiv _ _ (rationalRestrictionIso f).hom

/-- The original pullback and restriction maps have the same adjoint. -/
theorem rationalModulePullbackIso_adjoint :
    (schemeModulePullbackPushforwardAdjunction f).homEquiv _ _
        (rationalModulePullbackIso f).hom = rationalOpenAdjoint f := by
  have h := congrArg
    ((restrictionAdjunction f).homEquiv (rationalFunctionModule X)
      (rationalFunctionModule Y))
    (restrictionIsoPullback_comp_rationalModulePullbackIso f)
  change (restrictionAdjunction f).homEquiv _ _
      ((Adjunction.leftAdjointUniq (restrictionAdjunction f)
        (schemeModulePullbackPushforwardAdjunction f)).hom.app
          (rationalFunctionModule X) ≫ (rationalModulePullbackIso f).hom) =
    rationalOpenAdjoint f at h
  rw [homEquiv_leftAdjointUniq_comp] at h
  exact h

/-- On every nonempty original target open, the adjoint acts by the
original generic-stalk field map. -/
theorem rationalOpenAdjoint_field (U : X.Opens) [Nonempty U]
    (s : (rationalFunctionModule X).val.obj (op U)) :
    letI := preimage_nonempty f U
    rationalFunctionModuleSectionsEquiv Y (f ⁻¹ᵁ U)
        ((rationalOpenAdjoint f).val.app (op U) s) =
      (functionFieldIso f).hom (rationalFunctionModuleSectionsEquiv X U s) := by
  letI := preimage_nonempty f U
  letI := nonempty_image f (f ⁻¹ᵁ U)
  let i : f ''ᵁ (f ⁻¹ᵁ U) ⟶ U :=
    homOfLE (Set.image_preimage_subset f.base (U : Set X))
  rw [rationalOpenAdjoint, Adjunction.homEquiv_unit]
  change rationalFunctionModuleSectionsEquiv Y (f ⁻¹ᵁ U)
      (rationalRestrictionSectionEquiv f (f ⁻¹ᵁ U)
        ((rationalFunctionModule X).val.map i.op s)) = _
  rw [rationalRestrictionSectionEquiv_field,
    rationalFunctionModuleSectionsEquiv_naturality]

end KltDP.Geometry.OpenImmersionRational

#check @KltDP.Geometry.OpenImmersionRational.rationalModulePullbackIso_adjoint
#print axioms KltDP.Geometry.OpenImmersionRational.rationalOpenAdjoint_field
