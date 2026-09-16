import KltDP.Geometry.SchemeKaehlerPullbackRestrictionComp

/-!
# Original differential pullback on original unit sections

The original restriction/pullback comparison preserves the original
adjunction. Consequently the existing Kähler pullback isomorphism sends
the pullback-unit image of each original differential to the differential
of the original scheme section map. This fixes its affine normalization.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.SchemeKaehlerOpenRestriction

open SchemeKaehlerSheaf SchemeModuleRestriction

attribute [local instance] Types.instFunLike Types.instConcreteCategory

private theorem homEquiv_leftAdjointUniq_comp
    {C D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) (b : F' ⊣ G)
    (M : C) (N : D) (h : F'.obj M ⟶ N) :
    a.homEquiv M N ((Adjunction.leftAdjointUniq a b).hom.app M ≫ h) =
      b.homEquiv M N h := by
  rw [Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_leftAdjointUniq_hom_app, Adjunction.homEquiv_unit]

variable {k : Type u} [CommRing k] {X Y : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) (j : Y ⟶ X) [IsOpenImmersion j]

/-- The original pullback comparison has the original derivative map as its adjunct. -/
theorem pullbackIso_homEquiv :
    (schemeModulePullbackPushforwardAdjunction j).homEquiv _ _
      (pullbackIso f j).hom = adjointComparison f j := by
  change (schemeModulePullbackPushforwardAdjunction j).homEquiv _ _
    ((Adjunction.leftAdjointUniq
      (schemeModulePullbackPushforwardAdjunction j) (restrictionAdjunction j)).hom.app
      (baseRingSheaf f) ≫ (restrictionIso f j).hom) = _
  exact homEquiv_leftAdjointUniq_comp _ _ _ _ _

/-- The original unit section of a differential is carried to the original
differential of its image under the original scheme section map. -/
theorem pullbackIso_unit_d (U : X.Opens) (s : Γ(X, U)) :
    (pullbackIso f j).hom.val.app (op (j ⁻¹ᵁ U))
      (((schemeModulePullbackPushforwardAdjunction j).unit.app
        (baseRingSheaf f)).val.app (op U) ((baseRingDerivation f).d s)) =
      (baseRingDerivation (j ≫ f)).d (j.app U s) := by
  have h := congrArg (fun a => a.val.app (op U) ((baseRingDerivation f).d s))
    (pullbackIso_homEquiv f j)
  exact h.trans (adjointComparison_d f j U s)

end KltDP.Geometry.SchemeKaehlerOpenRestriction
